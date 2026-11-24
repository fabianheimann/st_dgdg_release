"""Data for the space-time sketch of the kite example (fig:spacetime_kite): the background mesh of the coarsest level
i = 1 of the convergence study (h = 0.45, 8 time slabs of length 0.0625) and, per slab, the active and cut elements
as computed by ngsxfem (same mesh generation, level set and CutInfo as in ../solve.py).

  python3 st_vis_kite.py [i] [k]      (run from num_exp/vis_spacetime/)  ->  vis/mesh.npz, vis/active_<n>.npz

Pipeline: st_vis_kite.py -> export_kite_st.py -> blender_kite_st.py (Blender 4.2, Cycles) -> crop_kite_st.py
Adapted from the proposal figure pipeline (dfg-unfitted/numexa: spacetime_vis.py, export_blender.py, ...).
"""
import os, sys
import numpy as np
from ngsolve import *
from xfem import *
from xfem.lset_spacetime import *

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
from solve import GetProblem

i = int(sys.argv[1]) if len(sys.argv) > 1 else 1
k = int(sys.argv[2]) if len(sys.argv) > 2 else 2
ngsglobals.msg_level = 0
os.makedirs("vis", exist_ok=True)

told = Parameter(0.0)
dtpar = Parameter(1.0)
t = told + dtpar * tref
prob = GetProblem("kite", t, 1.0, i)
n_steps = 4 * 2**i
delta_t = prob["tend"] / n_steps
dtpar.Set(delta_t)
mesh = Mesh(prob["geometry"].GenerateMesh(maxh=prob["maxh"] * 0.5**i, quad_dominated=False))
lsetadap = LevelSetMeshAdaptation_Spacetime(mesh, order_space=k, order_time=k, threshold=0.5, discontinuous_qn=True)
ci = CutInfo(mesh, time_order=0)

pts = np.array([v.point for v in mesh.vertices])
tris = np.array([[v.nr for v in el.vertices] for el in mesh.Elements(VOL)])
np.savez("vis/mesh.npz", points=pts, triangles=tris, h=prob["maxh"] * 0.5**i)
NS = 9
EDGES = sorted({tuple(sorted((int(p), int(q)))) for a, b_, c in tris for p, q in ((a, b_), (b_, c), (c, a))})
EDGES = np.array(EDGES)
lam = np.linspace(0, 1, NS)
EPTS = [(1 - lj) * pts[e0] + lj * pts[e1] for e0, e1 in EDGES for lj in lam]
for n in range(n_steps):
    told.Set(n * delta_t)
    lsetadap.CalcDeformation(prob["levelset"])
    ci.Update(lsetadap.levelsetp1[INTERVAL], time_order=0)
    hasneg = np.array(list(ci.GetElementsOfType(HASNEG)), dtype=bool)
    cut = np.array(list(ci.GetElementsOfType(IF)), dtype=bool)
    # isoparametric mesh deformation Theta_h - id on the mesh edges: samples s_l (time, reference) x lambda_j (along
    # the edge), so that horizontal edges (s = 0, 1), vertical edges (lambda = 0, 1) and lateral faces can be drawn
    defo = np.zeros((NS, len(EDGES), NS, 2))
    for l, s in enumerate(np.linspace(0, 1, NS)):
        cf = fix_tref(CoefficientFunction(lsetadap.deformation[INTERVAL]), s)
        vals = np.array([cf(mesh(*xy)) for xy in EPTS])
        defo[l] = vals.reshape(len(EDGES), NS, 2)
    # Ghost penalty facets as in ../solve.py: DG and CG_Gamma (facets between active elements, one of them cut),
    # CG (all facets between active elements)
    els = ci.GetElementsOfType(HASNEG)
    fac_v = lambda ba: np.array([sorted(v.nr for v in mesh.facets[f].vertices) for f in range(mesh.nfacet) if ba[f]])
    gp_cut = fac_v(GetFacetsWithNeighborTypes(mesh, a=els, b=ci.GetElementsOfType(IF)))
    gp_all = fac_v(GetFacetsWithNeighborTypes(mesh, a=els, b=els))
    np.savez(f"vis/active_{n}.npz", hasneg=hasneg, cut=cut, t_start=n * delta_t, t_end=(n + 1) * delta_t,
             defo=defo, edges=EDGES, gp_cut=gp_cut, gp_all=gp_all)
    print(f"   GP facets: DG/CG_Gamma {len(gp_cut)}, CG {len(gp_all)}")
    print(f"   max |Theta_h - id| = {np.abs(defo).max():.3e} (h = {prob['maxh'] * 0.5**i})")
    print(f"slab {n}: t in [{n * delta_t:.4f}, {(n + 1) * delta_t:.4f}], active {hasneg.sum()}, cut {cut.sum()}"
          f" of {mesh.ne} elements", flush=True)
