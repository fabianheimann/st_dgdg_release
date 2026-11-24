# Numerical experiments

Scripts and data behind the figures and the table of the section on numerical examples.
Only the experiments shown in the paper are contained here.

## Software

The computations use [NGSolve](https://ngsolve.org) with the add-on
[ngsxfem](https://github.com/ngsxfem/ngsxfem) (`solve.py`), Intel MKL PARDISO
(`mkl_pardiso.py`) and, for the finest level in three space dimensions, PETSc with MUMPS
through `petsc4py` / `mpi4py` (`superlu_mpi.py`, `run_3d_i3.sh`). The space-time sketches of
the geometry are rendered with Blender (`vis_spacetime/`).

## Files

| File | Purpose |
|---|---|
| `solve.py` | the discretisation (DG and CG variants) and the test problems |
| `conv_study.py` | convergence study for one configuration; writes `out/conv_*.dat` (and `out/line_*.dat` with `-line 1`) |
| `jobs_*.txt`, `run_queue.py` | the runs behind the data in `out/`, one command per line, and a simple job queue to execute them |
| `run_3d_i3.sh`, `superlu_mpi.py` | finest level of the example in three space dimensions (MPI, MUMPS) |
| `postprocess.py` | aggregates `out/conv_*.dat` and `out/line_*.dat` into the files read by the plots |
| `vis_spacetime/` | export, rendering and cropping of the space-time sketches of the moving domain |

## Data in `out/`

| Shown in the paper | Files |
|---|---|
| convergence of the DG method for `k = 1, …, 6`, `α = 1` and `α = 0` | `conv_kite_DG_ks<k>_kt<k>_a{1,0}_g0.05_c1.dat` |
| dependence on the diffusion coefficient (`k = 2, 3, 4`, level 4) | `peclet_k<k>_i4.dat`, aggregated from `conv_kite_{DG,CGall,CG}_ks<k>_kt<k>_a<α>_g0.05_c1.dat` |
| three space dimensions (moving sphere), table | `conv_moving_sphere_DG_ks{2,3}_kt{2,3}_a{1,0}_g0.05_c1.dat` and, for level 3, `…_c1_i3.dat` |
| profile of the steep layer | `ring_profile_{DG,CGall,CGall_g0.005}.dat`, computed from the three `line_kite_ring0.03_*.dat` files |

The columns of the `conv_*.dat` files are listed in `conv_study.py` (`i`: refinement level,
`l2final`: `L²` error at final time, `h1`, `mat`: errors in the gradient and in the material
derivative, …). `postprocess.py` also refers to data of further experiments that are not
shown in the paper; it skips files which are not present.
