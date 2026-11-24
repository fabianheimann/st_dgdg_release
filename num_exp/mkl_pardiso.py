"""Direct call of MKL PARDISO with METIS (nested dissection) ordering.

NGSolve's PardisoInverse uses the minimum degree ordering (iparm[1] = 0). For the DG matrices, the analysis phase with
this ordering is much more expensive than the factorisation itself (e.g. 43 s vs. 5 s for one time slab of the kite
example, k = 3, level 5), which distorts any timing comparison with CG. This wrapper uses the same settings as NGSolve,
except for iparm[1] = 2 (METIS), and additionally reports the fill-in of the factors.
"""
import ctypes
import os
import numpy as np
import scipy.sparse as sp
from ngsolve import TaskManager

_mkl = ctypes.CDLL(os.environ.get("MKL_RT", "/opt/intel/oneapi/mkl/2026.0/lib/libmkl_rt.so"))


def _ptr(arr):
    return arr.ctypes.data_as(ctypes.c_void_p)


class PardisoMetis:
    def __init__(self, mat, freedofs, n_threads):
        _mkl.MKL_Set_Num_Threads(n_threads)
        val, col, ind = mat.CSR()
        A = sp.csr_matrix((np.asarray(val), np.asarray(col), np.asarray(ind)), shape=(mat.height, mat.width))
        self.free = np.flatnonzero(np.array(freedofs, dtype=bool))
        A = A[self.free][:, self.free].tocsr()
        A.sort_indices()
        self.n = A.shape[0]
        self.a = A.data.astype(np.float64)
        self.ia = (A.indptr + 1).astype(np.int32)
        self.ja = (A.indices + 1).astype(np.int32)
        self.pt = np.zeros(64, dtype=np.int64)
        self.iparm = np.zeros(64, dtype=np.int32)
        ip = self.iparm
        # as in NGSolve's PardisoInverse (general non-symmetric, scaling + matching), but METIS ordering
        ip[0] = 1; ip[1] = 2; ip[7] = 16; ip[9] = 13; ip[10] = 1; ip[12] = 1; ip[17] = -1; ip[18] = -1; ip[20] = 1
        self.perm = np.zeros(self.n, dtype=np.int32)
        self._call(12, np.zeros(self.n), np.zeros(self.n))  # analysis + numerical factorisation
        self.nnz_lu = int(ip[17])
        self.mflop = int(ip[18])

    def _call(self, phase, b, x):
        one, mtype, ph, n, err, msg = (ctypes.c_int32(v) for v in (1, 11, phase, self.n, 0, 0))
        _mkl.pardiso(_ptr(self.pt), ctypes.byref(one), ctypes.byref(one), ctypes.byref(mtype), ctypes.byref(ph),
                     ctypes.byref(n), _ptr(self.a), _ptr(self.ia), _ptr(self.ja), _ptr(self.perm), ctypes.byref(one),
                     _ptr(self.iparm), ctypes.byref(msg), _ptr(b), _ptr(x), ctypes.byref(err))
        if err.value != 0:
            raise RuntimeError("PARDISO phase {} failed with error {}".format(phase, err.value))

    def Solve(self, rhs, sol):
        """sol = A^{-1} rhs on the free dofs, 0 on the others (as for NGSolve's inverse)"""
        b = np.ascontiguousarray(rhs.FV().NumPy()[self.free])
        x = np.zeros(self.n)
        self._call(33, b, x)
        s = sol.FV().NumPy()
        s[:] = 0.
        s[self.free] = x

    def __del__(self):
        try:
            self._call(-1, np.zeros(1), np.zeros(1))
        except Exception:
            pass
