"""Aggregate out/conv_*.dat into the LaTeX table used in sec_numex.tex and print the numbers quoted in the text.
Robust to missing runs / levels (so it can be run while the campaign is still going). Usage: python postprocess.py
"""
import os
from math import log

OUT = "out"


def read(name):
    path = os.path.join(OUT, name)
    if not os.path.exists(path):
        return []
    lines = open(path).read().split("\n")
    cols = lines[0].split("\t")
    rows = []
    for l in lines[1:]:
        if l.strip():
            rows.append({c: float(v) for c, v in zip(cols, l.split("\t"))})
    return rows


def conv(geom, space, k, alpha, gamma=0.05, tag=""):
    return read("conv_{}_{}_ks{}_kt{}_a{:g}_g{:g}_c1{}.dat".format(geom, space, k, k, alpha, gamma, tag))


def eoc(rows, key, j):
    if j < 1 or j >= len(rows):
        return None
    return log(rows[j - 1][key] / rows[j][key]) / log(rows[j - 1]["h"] / rows[j]["h"])


def sci(v):
    if v is None:
        return "--"
    m, e = "{:.2e}".format(v).split("e")
    return "${}\\cdot 10^{{{}}}$".format(m, int(e))


def rate(v):
    return "--" if v is None else "{:.2f}".format(v)


def write(name, text):
    with open(os.path.join(OUT, name), "w") as fh:
        fh.write(text)
    print("wrote", name)


LABEL = {"DG": "DG", "CGall": "CG"}

# --- cost of DG vs CG (GP on all facets) at alpha = 1: finest common level for each k
tab = ["\\begin{tabular}{cc rrc c cc}", "\\toprule",
       "& & \\multicolumn{3}{c}{active dofs} & nze & \\multicolumn{2}{c}{$\\Vert u - u_h \\Vert_{\\Omega(T)}$} \\\\",
       "\\cmidrule(lr){3-5} \\cmidrule(lr){6-6} \\cmidrule(lr){7-8}",
       "$k$ & $i$ & DG & CG & ratio & ratio & DG & CG \\\\", "\\midrule"]
for k in range(1, 7):
    dg, cg = conv("kite", "DG", k, 1), conv("kite", "CGall", k, 1)
    n = min(len(dg), len(cg))
    if n == 0:
        continue
    d, c = dg[n - 1], cg[n - 1]
    tab.append("{} & {:d} & {:d} & {:d} & {:.2f} & {:.2f} & {} & {} \\\\".format(
        k, int(d["i"]), int(d["ndofs_max"]), int(c["ndofs_max"]), d["ndofs_max"] / c["ndofs_max"],
        d["nze_max"] / c["nze_max"], sci(d["l2final"]), sci(c["l2final"])))
tab += ["\\bottomrule", "\\end{tabular}"]
write("table_cost.tex", "\n".join(tab) + "\n")

# --- numbers quoted in the text (printed only)
for k in [2, 3]:
    for s in ["DG", "CGall"]:
        out = []
        for a in [1, 1e-2, 1e-4, 1e-6, 0]:
            rows = conv("kite", s, k, a)
            if rows:
                out.append("a={:g}: i={:d} l2final={:.2e} eoc={}".format(a, int(rows[-1]["i"]), rows[-1]["l2final"],
                                                                     rate(eoc(rows, "l2final", len(rows) - 1))))
        print("robustness", s, "k =", k, " | ".join(out))
for s in ["DG", "CGall"]:
    for a in [1, 0]:
        rows = conv("kite", s, 3, a, tag="_timing_metis")
        if rows:
            print("timing", s, "a =", a, " ".join("i={:d}: {:.1f}s (asm {:.1f}, sol {:.1f})".format(
                int(r["i"]), r["t_method"], r["t_asm"], r["t_sol"]) for r in rows))
for d in ["0.02", "0.03", "0.04", "0.08", "0.005"]:
    for k in [2, 3, 4]:
        for s in ["DG", "CGall"]:
            for r in conv("kite_ring" + d, s, k, 0):
                print("ring delta={} k={} {} i={:d} ndofs={:d} l2={:.1e} over/under={:.1e} far={:.1e}".format(
                    d, k, s, int(r["i"]), int(r["ndofs_max"]), r["l2final"], r["over"] + r["under"], r["l2far"]))

# --- profile of the steep layer for the figure (delta = 0.03, k = 4) with the pointwise error precomputed
# (pgfplots' arithmetic is not accurate enough for u_h - u close to the plateau u = 1). DG on level 4; CG on the
# mesh with (almost) the same number of dofs (87 time steps, jobs_ring_eqdofs.txt), also for a 10x smaller / larger
# Ghost penalty parameter
for g in ["0.005", "0.05", "0.5"]:
    for r in conv("kite_ring0.03", "CGall", 4, 0, gamma=float(g), tag="_n87"):
        print("ring delta=0.03 k=4 CGall equal dofs gamma={} ndofs={:d} l2={:.1e} over/under={:.1e} far={:.1e}".format(
            g, int(r["ndofs_max"]), r["l2final"], r["over"] + r["under"], r["l2far"]))
profiles = [("DG", "line_kite_ring0.03_DG_ks4_kt4_a0_g0.05_c1_i4.dat"),
            ("CGall", "line_kite_ring0.03_CGall_ks4_kt4_a0_g0.05_c1_n87_i4.44294.dat"),
            ("CGall_g0.005", "line_kite_ring0.03_CGall_ks4_kt4_a0_g0.005_c1_n87_i4.44294.dat"),
            ("CGall_g0.5", "line_kite_ring0.03_CGall_ks4_kt4_a0_g0.5_c1_n87_i4.44294.dat")]
for s, linefile in profiles:
    path = os.path.join(OUT, linefile)
    if os.path.exists(path):
        lines = open(path).read().split("\n")[1:]
        out = ["x\tuh\tu\terr"]
        for l in lines:
            if l.strip():
                x, uh, u = (float(v) for v in l.split("\t"))
                out.append("{:.6e}\t{:.15e}\t{:.15e}\t{:.6e}".format(x, uh, u, max(abs(uh - u), 1e-16)))
        write("ring_profile_{}.dat".format(s), "\n".join(out) + "\n")

# --- Peclet sweep at fixed mesh (level 4): L2 error at final time over alpha for DG, CG (GP on all facets) and
# CG with GP on the cut facets only; alpha = 0 is plotted at x = 1e-8
ALPHAS = ["1", "0.1", "0.01", "0.001", "0.0001", "1e-05", "1e-06", "0"]
for k in [2, 3, 4]:
    out = ["alpha\tDG\tCGall\tCG"]
    for a in ALPHAS:
        vals = []
        for s in ["DG", "CGall", "CG"]:
            r = [row for row in conv("kite", s, k, float(a)) if int(row["i"]) == 4]
            vals.append("{:.6e}".format(r[0]["l2final"]) if r else "nan")
        out.append("{:g}\t".format(float(a) if a != "0" else 1e-8) + "\t".join(vals))
    write("peclet_k{}_i4.dat".format(k), "\n".join(out) + "\n")
    print("peclet k={}".format(k), " | ".join(l.replace("\t", " ") for l in out[1:]))
