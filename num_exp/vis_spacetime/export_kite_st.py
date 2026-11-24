"""Export the space-time scene of the kite example for Blender (rendering: blender_kite_st.py).

  python3 st_vis_kite.py 1        # ngsxfem: mesh of level i = 1, active/cut element sets per slab
  python3 export_kite_st.py       # -> vis/scene.npz

Geometry (exact): phi = |(x - rho, y)| - 1, rho = (1 - y^2) t, w = (1 - y^2, 0). As w transports phi, a boundary
point starting at (cos th, sin th) moves to (cos th + cos^2 th * t, sin th).
Panel (a): Q over the fixed background mesh, time levels t_n as rings, one slab highlighted.
Panel (b): that slab with its active prisms Q_T^n: cut prisms (Q_T^n not contained in Q^n, orange) and the
remaining active prisms (grey wireframe). Time is the vertical axis, scaled by TS.
"""
import os
import numpy as np

VIS = "vis"
TS_A, TS_B = 3.0, 3.0
SLAB = int(os.environ.get("SLAB", "5"))


def bpt(th, t):
    return np.array([np.cos(th) + np.cos(th)**2 * t, np.sin(th)])


def phi(x, y, t):
    return np.sqrt((x - (1 - y**2) * t)**2 + y**2) - 1


mesh = np.load(f"{VIS}/mesh.npz")
P2, T = mesh["points"][:, :2], mesh["triangles"]
nslabs = len([k for k in range(100) if os.path.exists(f"{VIS}/active_{k}.npz")])
acts = [np.load(f"{VIS}/active_{k}.npz") for k in range(nslabs)]
t_lev = [float(a["t_start"]) for a in acts] + [float(acts[-1]["t_end"])]
out = {}


def tube_surface(t0, t1, TS, nth=200, nt=40):
    th = np.linspace(0, 2 * np.pi, nth, endpoint=False)
    ts = np.linspace(t0, t1, nt)
    V = np.vstack([np.column_stack([*bpt(th, t), np.full(nth, TS * t)]) for t in ts])
    F = []
    for j in range(nt - 1):
        for i in range(nth):
            a, b = j * nth + i, j * nth + (i + 1) % nth
            F += [[a, b, b + nth], [a, b + nth, a + nth]]
    return V, np.array(F)


def disc(t, TS, nth=200, nr=30):
    """Cap Omega(t): image of the unit disc under the flow map."""
    V = [[t, 0.0, TS * t]]
    th = np.linspace(0, 2 * np.pi, nth, endpoint=False)
    for k in range(1, nr + 1):
        s = k / nr
        X, Y = s * np.cos(th), s * np.sin(th)
        V += [[x + (1 - y**2) * t, y, TS * t] for x, y in zip(X, Y)]
    F = [[0, 1 + i, 1 + (i + 1) % nth] for i in range(nth)]
    for k in range(1, nr):
        o0, o1 = 1 + (k - 1) * nth, 1 + k * nth
        for i in range(nth):
            a, b, c, d = o0 + i, o0 + (i + 1) % nth, o1 + i, o1 + (i + 1) % nth
            F += [[a, d, b], [a, c, d]]
    return np.array(V), np.array(F)


def ring(t, TS, nth=240):
    a = np.linspace(0, 2 * np.pi, nth, endpoint=False)
    return np.column_stack([*bpt(a, t), np.full(nth, TS * t)])


def mesh_edges(mask=None):
    E = set()
    for e in (range(len(T)) if mask is None else np.where(mask)[0]):
        a, b, c = (int(v) for v in T[e])
        for p, q in ((a, b), (b, c), (c, a)):
            E.add(tuple(sorted((p, q))))
    return np.array(sorted(E))


def prism_edges(mask, n):
    E = set()
    for e in np.where(mask)[0]:
        a, b, c = (int(v) for v in T[e])
        for p, q in ((a, b), (b, c), (c, a)):
            E.add(tuple(sorted((p, q)))); E.add(tuple(sorted((p + n, q + n))))
        for p in (a, b, c):
            E.add((p, p + n))
    return np.array(sorted(E)).reshape(-1, 2)


def prism_faces(mask, n):
    F = []
    for e in np.where(mask)[0]:
        a, b, c = (int(v) for v in T[e])
        F += [[a, b, b + n, a + n], [b, c, c + n, b + n], [c, a, a + n, c + n]]
    return np.array(F).reshape(-1, 4)


# ----------------------------------------------------------------------------- isoparametric deformation
EXD = float(os.environ.get("EXD", "1"))        # exaggeration of Theta_h - id (1: true deformation)
EDGES_ALL = acts[0]["edges"]
EIDX = {tuple(e): k for k, e in enumerate(map(tuple, EDGES_ALL))}
NS = acts[0]["defo"].shape[0]
LAM = np.linspace(0, 1, NS)


def edge_curve(act, p, q, s_idx, TS):
    """Deformed spatial edge p -> q at reference time sample s_idx of the slab."""
    k = EIDX[tuple(sorted((p, q)))]
    d = act["defo"][s_idx, k]
    lam = LAM if p < q else LAM[::-1]
    dd = d if p < q else d[::-1]
    X = (1 - lam)[:, None] * P2[p] + lam[:, None] * P2[q] + EXD * dd
    t = float(act["t_start"]) + LAM[s_idx] * (float(act["t_end"]) - float(act["t_start"]))
    return np.column_stack([X, np.full(NS, TS * t)])


def vertical_curve(act, v, TS):
    for (p, q), k in EIDX.items():
        if v in (p, q):
            j = 0 if v == p else NS - 1
            X = P2[v] + EXD * act["defo"][:, k, j]
            t = float(act["t_start"]) + LAM * (float(act["t_end"]) - float(act["t_start"]))
            return np.column_stack([X, TS * t])


def prism_curves(act, mask, TS):
    C, seen = [], set()
    for e in np.where(mask)[0]:
        a, b_, c = (int(v) for v in T[e])
        for p, q in ((a, b_), (b_, c), (c, a)):
            key = tuple(sorted((p, q)))
            if key in seen:
                continue
            seen.add(key)
            C += [edge_curve(act, p, q, 0, TS), edge_curve(act, p, q, NS - 1, TS)]
        for v in (a, b_, c):
            if ("v", v) not in seen:
                seen.add(("v", v)); C.append(vertical_curve(act, v, TS))
    return np.array(C)


def prism_faces_curved(act, mask, TS):
    V, F = [], []
    for e in np.where(mask)[0]:
        a, b_, c = (int(v) for v in T[e])
        for p, q in ((a, b_), (b_, c), (c, a)):
            G = np.stack([edge_curve(act, p, q, l, TS) for l in range(NS)])      # (s, lambda, 3)
            o = len(V) and sum(len(x) for x in V)
            V.append(G.reshape(-1, 3))
            for l in range(NS - 1):
                for j in range(NS - 1):
                    i0 = o + l * NS + j
                    F += [[i0, i0 + 1, i0 + NS + 1, i0 + NS]]
    return np.vstack(V), np.array(F)


def facet_surfaces(act, F, TS):
    """Space-time facets F x I_n (deformed) of the facets F given by vertex pairs."""
    V, Fc = [], []
    for p, q in F:
        G = np.stack([edge_curve(act, int(p), int(q), l, TS) for l in range(NS)])
        o = sum(len(x) for x in V)
        V.append(G.reshape(-1, 3))
        for l in range(NS - 1):
            for j in range(NS - 1):
                i0 = o + l * NS + j
                Fc += [[i0, i0 + 1, i0 + NS + 1, i0 + NS]]
    return np.vstack(V), np.array(Fc)


def facet_frames(act, F, TS):
    C = []
    for p, q in F:
        C += [edge_curve(act, int(p), int(q), 0, TS), edge_curve(act, int(p), int(q), NS - 1, TS)]
    return np.array(C)


def mesh_curves(act, s_idx, TS, mask=None):
    E = mesh_edges(mask)
    return np.array([edge_curve(act, int(p), int(q), s_idx, TS) for p, q in E])


# ----------------------------------------------------------------------------- panel (a)
V, F = tube_surface(t_lev[0], t_lev[SLAB], TS_A, nt=10 * SLAB + 2)
if SLAB + 1 < nslabs:
    V2, F2 = tube_surface(t_lev[SLAB + 1], t_lev[-1], TS_A, nt=10 * (nslabs - SLAB - 1) + 2)
    V, F = np.vstack([V, V2]), np.vstack([F, F2 + len(V)])
out["a_lat_v"], out["a_lat_f"] = V, F
out["a_slab_v"], out["a_slab_f"] = tube_surface(t_lev[SLAB], t_lev[SLAB + 1], TS_A, nt=12)
out["a_top_v"], out["a_top_f"] = disc(t_lev[-1], TS_A)
out["a_rings"] = np.stack([ring(t, TS_A) for t in t_lev])
out["a_mark"] = np.array([SLAB, SLAB + 1])
out["bg_curves"] = mesh_curves(acts[0], 0, TS_A)
ts_ = 0.5 * (t_lev[SLAB] + t_lev[SLAB + 1])
out["a_anchor_Q"] = np.array([*bpt(-0.7 * np.pi, 0.15), TS_A * 0.15])
out["a_anchor_In"] = np.array([*bpt(-0.12 * np.pi, ts_), TS_A * ts_])
out["a_anchor_T"] = np.array([*bpt(0.8 * np.pi, t_lev[-1]), TS_A * t_lev[-1]])
out["a_axis_o"] = np.array([P2[:, 0].min(), P2[:, 1].min(), 0.0])
out["a_axis_len"] = np.array(0.45)

# ----------------------------------------------------------------------------- panel (b)
act = acts[SLAB]
t0, t1 = float(act["t_start"]), float(act["t_end"])
hasneg, cut = act["hasneg"].astype(bool), act["cut"].astype(bool)
inner = hasneg & ~cut
print(f"slab {SLAB} [{t0}, {t1}]: active {hasneg.sum()}, cut {cut.sum()}, inner {inner.sum()}")
n = len(P2)
out["b_prism_points"] = np.vstack([np.hstack([P2, np.full((n, 1), TS_B * t0)]), np.hstack([P2, np.full((n, 1), TS_B * t1)])])
out["b_cut_curves"] = prism_curves(act, cut, TS_B)
out["b_cut_fv"], out["b_cut_ff"] = prism_faces_curved(act, cut, TS_B)
out["b_in_curves"] = prism_curves(act, inner, TS_B)
out["b_bg_curves"] = mesh_curves(act, 0, TS_B)
out["b_act_curves"] = prism_curves(act, hasneg, TS_B)
for key in ("gp_cut", "gp_all"):
    out[f"b_{key}_fv"], out[f"b_{key}_ff"] = facet_surfaces(act, act[key], TS_B)
    out[f"b_{key}_frame"] = facet_frames(act, act[key], TS_B)
print("GP facets in the slab: DG/CG_Gamma", len(act["gp_cut"]), " CG", len(act["gp_all"]))
out["b_lat_v"], out["b_lat_f"] = tube_surface(t0, t1, TS_B, nt=20)
out["b_top_v"], out["b_top_f"] = disc(t1, TS_B)
out["b_bot_v"], out["b_bot_f"] = disc(t0, TS_B)
out["b_rings"] = np.stack([ring(t0, TS_B), ring(t1, TS_B)])
out["b_bg_points"] = np.hstack([P2, np.full((n, 1), TS_B * t0)])
act_nodes = np.unique(T[hasneg].ravel())
out["b_cand_lo"] = np.hstack([P2[act_nodes], np.full((len(act_nodes), 1), TS_B * t0)])
out["b_cand_hi"] = np.hstack([P2[act_nodes], np.full((len(act_nodes), 1), TS_B * t1)])
out["b_anchor_Om"] = np.array([0.2, 0.0, TS_B * t1])
cut_nodes = np.unique(T[cut].ravel())
far = cut_nodes[np.argmax(P2[cut_nodes, 0] - 0.5 * np.abs(P2[cut_nodes, 1] + 0.3))]
out["b_anchor_cut"] = np.array([P2[far, 0], P2[far, 1], TS_B * ts_])
out["b_center"] = np.array([0.25, 0.0, TS_B * ts_])
out["meta"] = np.array([TS_A, TS_B, t0, t1, SLAB, float(mesh["h"]), EXD])
print("max |Theta_h - id| in the slab:", np.abs(act["defo"]).max(), " exaggeration", EXD)
np.savez(f"{VIS}/scene.npz", **out)
print("exported", len(out), "arrays")
