import argparse
import os
from math import log, log2
from solve import Solve

parser = argparse.ArgumentParser(description='Convergence study for the unfitted space-time DG/CG methods.')
parser.add_argument('-g', '--geom', default="kite")
parser.add_argument('-s', '--space', default="DG", help="DG, CG, CGall")
parser.add_argument('-ks', '--ks', type=int, default=3)
parser.add_argument('-kt', '--kt', type=int, default=-1, help="default: = ks")
parser.add_argument('-a', '--alpha', type=float, default=1.)
parser.add_argument('-gamma', '--gamma', type=float, default=0.05)
parser.add_argument('-lam', '--lam', type=float, default=10.)
parser.add_argument('-i0', '--i0', type=int, default=0, help="first refinement level")
parser.add_argument('-nr', '--n_ref', type=int, default=4, help="number of refinement levels")
parser.add_argument('-c', '--curved', type=int, default=1)
parser.add_argument('-nthr', '--nthr', type=int, default=6)
parser.add_argument('-sol', '--sol', default="pardiso")
parser.add_argument('-ms', '--max_slabs', type=int, default=0, help="only solve the first time slabs (for matrix/fill statistics)")
parser.add_argument('-tag', '--tag', default="")
parser.add_argument('-nsteps', '--nsteps', type=int, default=0, help="single run with this number of time steps instead of the levels i0, ...: i = log2(nsteps / 4), in general non-integer (for comparisons at equal numbers of dofs)")
parser.add_argument('-line', '--line', type=int, default=0, help="write final time solution along y=0 for each level")
args = parser.parse_args()
kt = args.ks if args.kt < 0 else args.kt

cols = ["i", "h", "delta_t", "l2final", "l2l2", "h1", "dt", "mat", "l1final", "over", "under", "l2far", "ndofs_max", "ndofs_sum",
        "nze_max", "nze_sum", "t_method", "t_cpu", "t_asm", "t_sol", "nnzlu_max", "mflop_sum"]
levels = [log2(args.nsteps / 4)] if args.nsteps > 0 else range(args.i0, args.i0 + args.n_ref)
tag = args.tag + ("_n{}".format(args.nsteps) if args.nsteps > 0 else "")
name = "out/conv_{}_{}_ks{}_kt{}_a{:g}_g{:g}_c{}{}.dat".format(args.geom, args.space, args.ks, kt, args.alpha,
                                                              args.gamma, args.curved, tag)
os.makedirs("out", exist_ok=True)
with open(name, "w") as fh:
    fh.write("\t".join(cols) + "\n")

prev = None
for i in levels:
    r = Solve(i_t=i, i_s=i, k_t=kt, k_s=args.ks, space=args.space, geom=args.geom, alpha=args.alpha,
              gamma=args.gamma, lam=args.lam, n_threads=args.nthr, solver=args.sol, curved=bool(args.curved),
              verbose=False, max_slabs=args.max_slabs if args.max_slabs > 0 else None, linefile=name.replace("out/conv_", "out/line_").replace(".dat", "_i{:g}.dat".format(i)) if args.line else None)
    r["i"] = i
    with open(name, "a") as fh:
        fh.write("\t".join("{:.6e}".format(r[c]) if isinstance(r[c], float) else str(r[c]) for c in cols) + "\n")
    eoc = "" if prev is None else "  eoc(l2final) = {:.2f}  eoc(l2l2) = {:.2f}  eoc(h1) = {:.2f}".format(
        log(prev["l2final"] / r["l2final"]) / log(2), log(prev["l2l2"] / r["l2l2"]) / log(2),
        log(prev["h1"] / r["h1"]) / log(2))
    print("i = {}: l2final = {:.4e}, l2l2 = {:.4e}, h1 = {:.4e}, over/under = {:.1e}/{:.1e}, ndofs = {}, t = {:.1f}s{}".format(
        i, r["l2final"], r["l2l2"], r["h1"], r["over"], r["under"], r["ndofs_max"], r["t_method"], eoc), flush=True)
    prev = r
