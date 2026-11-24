#!/bin/bash
# 3D moving sphere, DG, level 3, order k (default 3): slab systems solved by MUMPS on P MPI ranks (superlu_mpi.py, FACTOR=mumps,
# PETSc build with 64-bit indices in ~/.local/petsc-3.25.2-int64; the factors exceed 2^31 nonzeros);
# writes out/conv_moving_sphere_DG_ks<k>_kt<k>_a<alpha>_g0.05_c1_i3.dat and logs/3d[_k<k>]_i3_a<alpha>.{log,mem}
#   ./run_3d_i3.sh <alpha> [P=16] [k=3]
alpha=$1; P=${2:-16}; k=${3:-3}
log=logs/3d_i3_a$alpha; [ "$k" = 3 ] || log=logs/3d_k${k}_i3_a$alpha
export PYTHONPATH=$HOME/.local/petsc-3.25.2-int64/lib FACTOR=mumps OMP_NUM_THREADS=1 \
       MKL_RT=/opt/intel/oneapi/mkl/latest/lib/libmkl_rt.so MKL_THREADING_LAYER=INTEL \
       LD_PRELOAD=/opt/intel/oneapi/compiler/latest/lib/libiomp5.so
mpirun -n $P -x PYTHONPATH -x FACTOR -x OMP_NUM_THREADS -x MKL_RT -x MKL_THREADING_LAYER -x LD_PRELOAD \
  python3 -u superlu_mpi.py -nthr 8 -g moving_sphere -a $alpha -s DG -ks $k -i0 3 -nr 1 -sol pardiso_metis -tag _i3 \
  > $log.log 2>&1 &
pid=$!
while kill -0 $pid 2>/dev/null; do
  echo "$(date +%m-%d_%H:%M) $(ps -eo rss,args | grep "superlu_mpi.py -nthr 8 -g moving_sphere -a $alpha -s DG -ks $k " | grep -v -E "grep|mpirun" | awk "{s+=\$1} END {printf \"%.1f\", s/1048576}") GB" >> $log.mem
  sleep 60
done
wait $pid; echo "EXIT code=$? $(date)" >> $log.log
