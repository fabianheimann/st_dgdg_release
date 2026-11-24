"""Run conv_study.py with the slab systems solved by SuperLU_dist or MUMPS (PETSc) on all MPI ranks.

  [FACTOR=mumps] mpirun -n P python3 superlu_mpi.py <conv_study.py arguments, with -sol pardiso_metis>

For more than 2^31 nonzeros in the factors (3D, k = 3, level 3) PETSc has to be built with 64-bit indices
(~/.local/petsc-3.25.2-int64, also with MUMPS; the pip PETSc has 32-bit indices). Level 2 (3D, k = 3), 12 ranks,
loaded machine: MUMPS 81 s, SuperLU_dist 134 s, PARDISO (12 threads) 156 s per slab.

Rank 0 runs conv_study.py / solve.py unchanged (NGSolve, ngsxfem, sequential); only the class PardisoMetis used by
solve.py for -sol pardiso_metis is replaced by SuperLUDist below, which distributes the matrix of the free dofs by rows
to all ranks and factorizes / solves it with SuperLU_dist or MUMPS. The other ranks only take part in these solves
(so the Ghost penalty couplings need no MPI support in NGSolve). Iterative solvers (hypre BoomerAMG, GAMG,
ILU/ASM + GMRES) were not competitive for these systems. Used for the 3D example, level 3 (run_3d_i3.sh).
"""
import os, sys, runpy
import numpy as np
from mpi4py import MPI
import petsc4py
petsc4py.init([])
from petsc4py import PETSc

comm = MPI.COMM_WORLD
FACTOR = os.environ.get("FACTOR", "superlu_dist")      # "superlu_dist" or "mumps" (MUMPS needs the PETSc build in
                                                        # ~/.local/petsc-3.25.2-int64 on PYTHONPATH)
rank, size = comm.Get_rank(), comm.Get_size()


def _rows(n):
    """Row partition: rank r owns rows [b[r], b[r+1])."""
    return np.linspace(0, n, size + 1).round().astype(np.int64)


class _Dist:
    """Collective part (all ranks): distributed matrix, LU factorization, solves."""

    def __init__(self, n, indptr, indices, data):
        b = _rows(n)
        A = PETSc.Mat().create(comm=PETSc.COMM_WORLD)
        A.setSizes(((b[rank + 1] - b[rank], n), (b[rank + 1] - b[rank], n)))
        A.setType("aij")
        A.setPreallocationCSR((indptr, indices))
        A.setValuesCSR(indptr, indices, data)
        A.assemble()
        self.A, self.b = A, b
        ksp = PETSc.KSP().create(comm=PETSc.COMM_WORLD)
        ksp.setOperators(A)
        ksp.setType("preonly")
        pc = ksp.getPC(); pc.setType("lu"); pc.setFactorSolverType(FACTOR)
        if FACTOR == "mumps":
            pc.setFactorSetUpSolverType()
            F = pc.getFactorMatrix()
            F.setMumpsIcntl(7, 5)                 # sequential METIS ordering (fastest in the tests)
            F.setMumpsIcntl(14, 50)               # 50% workspace margin
        ksp.setUp()
        self.ksp = ksp
        self.x, self.rhs = A.createVecs()

    def solve(self, rhs_loc):
        self.rhs.setArray(rhs_loc)
        self.ksp.solve(self.rhs, self.x)
        return self.x.getArray().copy()

    def destroy(self):
        for o in (self.ksp, self.A, self.x, self.rhs):
            o.destroy()


def _scatter_csr(A):
    """Rank 0: send the row blocks of the scipy CSR matrix A; returns the own block."""
    n = A.shape[0]
    b = _rows(n)
    comm.bcast(("factor", n), root=0)
    for r in range(1, size):
        blk = A[b[r]:b[r + 1]]
        meta = (len(blk.indptr), len(blk.indices))
        comm.send(meta, dest=r, tag=1)
        comm.Send(np.ascontiguousarray(blk.indptr, dtype=PETSc.IntType), dest=r, tag=2)
        comm.Send(np.ascontiguousarray(blk.indices, dtype=PETSc.IntType), dest=r, tag=3)
        comm.Send(np.ascontiguousarray(blk.data, dtype=PETSc.ScalarType), dest=r, tag=4)
    blk = A[b[0]:b[1]]
    return n, blk.indptr.astype(PETSc.IntType), blk.indices.astype(PETSc.IntType), blk.data.astype(PETSc.ScalarType)


def _recv_csr():
    lp, li = comm.recv(source=0, tag=1)
    indptr = np.empty(lp, dtype=PETSc.IntType); comm.Recv(indptr, source=0, tag=2)
    indices = np.empty(li, dtype=PETSc.IntType); comm.Recv(indices, source=0, tag=3)
    data = np.empty(li, dtype=PETSc.ScalarType); comm.Recv(data, source=0, tag=4)
    return indptr, indices, data


def _solve_root(dist, rhs_full):
    b = dist.b
    comm.bcast(("solve", None), root=0)
    for r in range(1, size):
        comm.Send(np.ascontiguousarray(rhs_full[b[r]:b[r + 1]]), dest=r, tag=5)
    x0 = dist.solve(rhs_full[b[0]:b[1]])
    x = np.empty(b[-1]); x[b[0]:b[1]] = x0
    for r in range(1, size):
        comm.Recv(x[b[r]:b[r + 1]], source=r, tag=6)
    return x


def worker():
    dist = None
    while True:
        cmd, arg = comm.bcast(None, root=0)
        if cmd == "factor":
            if dist is not None:
                dist.destroy()
            b = _rows(arg)
            dist = _Dist(arg, *_recv_csr())
        elif cmd == "solve":
            rhs = np.empty(dist.b[rank + 1] - dist.b[rank]); comm.Recv(rhs, source=0, tag=5)
            comm.Send(dist.solve(rhs), dest=0, tag=6)
        elif cmd == "free":
            if dist is not None:
                dist.destroy(); dist = None
        elif cmd == "exit":
            if dist is not None:
                dist.destroy()
            return


class SuperLUDist:
    """Drop-in replacement for mkl_pardiso.PardisoMetis on rank 0."""

    def __init__(self, mat, freedofs, n_threads):
        import scipy.sparse as sp
        val, col, ind = mat.CSR()
        A = sp.csr_matrix((np.asarray(val), np.asarray(col), np.asarray(ind)), shape=(mat.height, mat.width))
        self.free = np.flatnonzero(np.array(freedofs, dtype=bool))
        A = A[self.free][:, self.free].tocsr()
        A.sort_indices()
        self.dist = _Dist(*_scatter_csr(A))
        self.nnz_lu, self.mflop = 0, 0

    def Solve(self, rhs, sol):
        x = _solve_root(self.dist, rhs.FV().NumPy()[self.free].copy())
        s = sol.FV().NumPy()
        s[:] = 0.0
        s[self.free] = x

    def __del__(self):
        try:
            comm.bcast(("free", None), root=0)
            self.dist.destroy()
        except Exception:
            pass


if __name__ == "__main__":
    if rank == 0:
        here = os.path.dirname(os.path.abspath(__file__))
        sys.path.insert(0, here)
        import solve
        solve.PardisoMetis = SuperLUDist
        sys.argv = [os.path.join(here, "conv_study.py")] + sys.argv[1:]
        try:
            runpy.run_path(sys.argv[0], run_name="__main__")
        finally:
            comm.bcast(("exit", None), root=0)
    else:
        worker()
    # petsc4py's garbage cleanup at exit fails with this Open MPI: finalize MPI ourselves and leave
    comm.Barrier()
    sys.stdout.flush(); sys.stderr.flush()
    MPI.Finalize()
    os._exit(0)
