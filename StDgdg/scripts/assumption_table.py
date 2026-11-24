#!/usr/bin/env python3
"""Generate ASSUMPTIONS.md: the translation between the Lean formalisation and the paper.

The LaTeX labels are the stable keys (they are also quoted in `StDgdg/Setting.lean`); the
numbers are read from the `.aux` file of the compiled paper, so that the table can be
regenerated whenever the numbering changes:

    python3 scripts/assumption_table.py [path/to/st_article.aux]

The script fails if a label does not exist in the paper, if a Lean declaration named here
does not exist, or if a field of `Setting.lean` is missing from the tables.
"""
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
AUX = Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT.parent / "st_article.aux"
SRC = ROOT / "StDgdg"

KIND = {"equation": "({})", "subequation": "({})", "lemma": "Lemma {}", "theorem": "Theorem {}",
        "proposition": "Proposition {}", "corollary": "Corollary {}", "assumption": "Assumption {}",
        "remark": "Remark {}", "section": "Section {}", "subsection": "Section {}",
        "definition": "Definition {}"}


def read_labels():
    aux = AUX.read_text()
    num = dict(re.findall(r"\\newlabel\{([^}@]+)\}\{\{([^}]*)\}", aux))
    kind = dict(re.findall(r"\\newlabel\{([^}@]+)@cref\}\{\{\[([a-z]+)\]", aux))
    return num, kind


NUM, KINDS = read_labels()
MISSING = []


def ref(label):
    if label not in NUM:
        MISSING.append(label)
        return f"`{label}` (?)"
    return KIND.get(KINDS.get(label, ""), "{}").format(NUM[label])


def refs(labels):
    return ", ".join(ref(l) for l in labels) if labels else "–"


# ----------------------------------------------------------------------------------------
# The assumptions: (fields, labels, relation to the paper)
# ----------------------------------------------------------------------------------------

SETTING = [
    ("Parameters and regimes", [
        (["h_pos", "τ_pos", "α_nonneg", "wInf_nonneg"], [], "signs of `h`, `Δt`, `α`, `‖w‖_∞`"),
        (["τ_le_one", "h_le"], ["ssec:prelim"], "the standing assumptions `Δt ≤ 1` and `h ≲ 1`"),
        (["caseD"], ["eq:ass_caseD"], "Case D"),
        (["caseC"], ["eq:ass_caseC"], "Case C"),
    ]),
    ("Spaces and operators", [
        (["Wh_le_Ws"], [], "`W_h` consists of functions which are piecewise polynomial in space"),
        (["dx_mem"], [], "`∇u ∈ [W_h]^d` for `u ∈ W_h` (used where `lemma_gp_E_IpGP` and "
                         "superapproximation are applied to `∇u`)"),
        (["Lh_mem"], ["eq:def_Lapp"], "`𝓛_h u ∈ W_h` for `u ∈ W_h`"),
        (["mat_Lc"], ["eq:def_Lapp"], "`𝓛 = ∂_t + w·∇` in Case C"),
        (["mat_dt", "Lc_dt"], [], "`‖w·∇v‖ ≤ ‖w‖_∞ ‖∇v‖` on `Q^n`, for the material derivative and "
                                  "for `𝓛` (`𝓛 = ∂_t` in Case D)"),
    ]),
    ("Monotonicity of the forms", [
        (["Q_le_QT"], [], "follows from `Q^n ⊆ 𝒬_T^n`"),
        (["FQ_le"], ["eq:def_int_facets"], "follows from the splitting of the active facets into "
                                            "stabilised and interior ones"),
        (["Fint_le_FQ"], ["eq:def_int_facets"], "follows from `F × I_n ⊆ closure Q^n` for interior facets"),
        (["FQw_le"], [], "`|w·n| ≤ ‖w‖_∞` (a bound of the weight, not an inclusion)"),
    ]),
    ("Standard discrete inequalities", [
        (["trace_up", "trace_dn"], ["eq:std_trace"],
         "first inequality, for both one-sided traces: pointwise `|u_∓|² ≤ |u|_{T₁}|² + |u|_{T₂}|²` "
         "on a facet (the upwind side may change within a facet), then the inequality on both "
         "neighbours and summation over the active facets. Stated for functions which are only "
         "piecewise polynomial in space (`Ws`), as it is applied to the remainder `Π_t(φu) − φu`"),
        (["trace_nfl"], ["eq:std_trace", "lemma_IP_coercivity"],
         "the same applied to `∇v` and averaged over the two sides; no displayed counterpart, "
         "used in the proof of the lemma"),
        (["trace_time"], ["eq:std_trace", "lemma_bound_tn_ag_temporal_vol"],
         "second inequality, summed: `Ω(t_n)` and `Ω(t_{n+1})` are covered by the active elements "
         "of slab `n`. For `W_h` only (polynomial in time)"),
        (["trace_time_cont"], ["eq:cont_trace"],
         "second inequality, summed in the same way; applied to the remainder and to the "
         "interpolation error"),
        (["trace_up_cont"], ["eq:cont_trace"],
         "first inequality, multiplied by `h`, upwind trace, summed over the active facets; "
         "applied to the interpolation error only"),
        (["inv_dx"], ["eq:std_inverse"], "first inequality, summed; for `Ws`"),
        (["Lc_inv"], ["eq:std_inverse", "lemma_test_fun_bnd"],
         "inverse inequality for `𝓛` (in Case C with `‖w‖_∞ Δt ≲ h`), as used in the proof of the lemma"),
    ]),
    ("Ghost penalty", [
        (["gp"], ["lemma_gp_E_IpGP", "ass:gp"], "the lemma, slab-wise; it rests on the assumption"),
        (["gp_inv_dx"], ["gp_inv_ineq"],
         "spatial part. An inverse inequality within the Ghost penalty form; it does not follow "
         "from `gp` and `inv_dx` (the polynomial extension commutes with `∇`)"),
        (["gp_facet"], ["lemma_gp_facet_jumps"],
         "the core step of the proof, slab-wise and unscaled: `‖[v]‖²` on the stabilised facets "
         "`≤ C h⁻¹ j_h^n(v,v)`. The lemma follows by multiplying with `α h⁻¹ + ‖w‖_∞` and summing"),
    ]),
    ("The discrete derivative `𝓛_h`", [
        (["Lc_Lh"], ["eq_Lapp_diff"], "as stated (trivial in Case D)"),
        (["Lh_inv_grad"], ["eq_Lapp_inverse"], "second inequality"),
        (["Lh_gp"], ["eq_Lapp_gp"],
         "as stated; contains the temporal part of `gp_inv_ineq`. The volume term stems from the "
         "jump of `w_h` across a facet patch and is absent in Case D"),
        (["Lh_int_jump"], ["lemma_y_jumps"],
         "interior facet step of the proof, no displayed counterpart: `[𝓛_h u] = ∂_t[u] + w_h·[∇u]`; "
         "temporal inverse inequality on `F × I_n`, trace inequality for `∇u` and `‖w‖_∞ Δt ≲ h`"),
    ]),
    ("Integration by parts", [
        (["ibp"], ["lemma_B_Bmc"],
         "first display of the proof: space-time integration by parts on the cut prisms of one "
         "slab, summed over the elements (uses `div w = 0` and `w^*·n^* = 0` on the lateral boundary)"),
    ]),
]

WEIGHT = [
    ("The weight `φ = φ(t)`", [
        (["σ_nonneg", "c0_pos", "Cφ_nonneg", "c0_le_lo", "c0_le_phi", "phi_le_one", "hi_le"],
         ["lemma_weighted_symm_testing"],
         "`c0 ≤ φ ≤ 1` and `M_n ≤ C_φ m_n` (proof of the lemma). For `e^{-σt}`: `c0 = e^{-σT}`, "
         "`C_φ = e` if `σ Δt ≤ 1`"),
        (["dx_M", "up_M", "dn_M", "nfl_M", "bot_M", "top_M"], [],
         "`φ` depends on `t` only: it commutes with spatial derivatives and traces and is a "
         "number on each time level"),
        (["mat_M", "Lc_M"], [], "product rule with `φ' = −σφ`"),
        (["Q_symm", "j_symm", "FQ_symm", "FQw_symm"], [], "multiplication by `φ` is symmetric"),
        (["Q_lo", "j_lo", "FQ_lo", "FQw_lo", "FQ_hi"], [], "`m_n ≤ φ ≤ M_n` on slab `n`"),
        (["Q_contr", "j_contr", "FQ_contr", "FQw_contr"], [], "`φ² ≤ 1`"),
    ]),
]

EXPWEIGHT = [
    ("The temporal projection `Π_t` and superapproximation", [
        (["Pw_mem", "r_mem", "r_dx"], ["lemma_superapprox"],
         "text before the lemma: `Π_t(φu) ∈ W_h`, the remainder `r = Π_t(φu) − φu` is polynomial "
         "in space, and `Π_t` commutes with `∇`. That `Π_t` is an orthogonal projection is not used"),
        (["superapprox"], ["eq_superapprox"], "as stated, squared"),
        (["superapprox_dt"], ["eq_superapprox_dt"], "the right-most bound, squared"),
        (["superapprox_gp", "superapprox_int"], ["eq_superapprox_F"],
         "squared, on the stabilised and on the interior facets"),
        (["superapprox_j"], ["eq_superapprox_patch"], "squared and summed over the facet patches"),
    ]),
]

ERRORDATA = [
    ("Exact solution, interpolant and discrete solution", [
        (["uh_mem", "Ih_mem"], [], "`u_h, I_h u^e ∈ W_h`"),
        (["disc"], ["eq_discrete_problem"], "the discrete problem"),
        (["cons"], ["lemma_consistency"], "the lemma is an assumption here (proven in Lean only "
                                           "for the ODE example)"),
        (["jmp_ue"], ["lemma_consistency"], "the exact solution has no jumps across spatial facets"),
        (["hCi", "hU", "hD2"], [], "signs"),
        (["i_L2"], ["eq_interpol_L2"], "squared"),
        (["i_dt"], ["eq_interpol_dt"], "squared"),
        (["i_grad"], ["eq_interpol_grad"], "squared; `D2` stands for `h² ‖D²e‖²`"),
        (["i_jump"], ["eq_interpol_jumps"], "squared: facet jumps on the full facets and Ghost "
                                            "penalty jumps of the interpolant"),
        (["nfl_e"], ["eq:cont_trace"], "first inequality applied to `∇e`"),
    ]),
]

# fields which are data (objects), not assumptions
DATA = set("""C γJ lam hC hγJ hlam regime N h τ α wInf Wh Ws dt dx mat Lc Lh up dn nfl bot top
Q QT j FQ FQw Fgp Fint Om M Mf lo hi phi σ c0 Cφ Cs hσ hCφ hCs Pw ue uh Ih f ks kt U D2""".split())

# ----------------------------------------------------------------------------------------
# The results: (label, [(declaration, file)], remark)
# ----------------------------------------------------------------------------------------

RESULTS = [
    ("thm_stability", [("ExpWeight.inf_sup", "Stability.lean"),
                       ("ExpWeight.inf_sup_product", "Solvability.lean"),
                       ("ExpWeight.unique_solvability", "Solvability.lean")],
     "`inf_sup` is `eq_inf_sup_two` with squared norms: `‖ṽ‖²_j ≤ M² ‖u‖²_j` and "
     "`(B_h+J)(u,ṽ) ≥ ⅛ ‖u‖²_j`. `inf_sup_product` is the product form with `C_stab = 1/(8M)` "
     "and `ṽ ≠ 0` for `‖u‖_j ≠ 0`. Unique solvability needs `W_h` finite dimensional and "
     "`‖·‖_{𝒬_T}` definite on `W_h`"),
    ("lemma_B_Bmc", [("Setting.CU_mc", "Continuity.lean")], "an identity"),
    ("lemma_continuity", [("Setting.continuity", "Continuity.lean")],
     "Young form `2 B_h(x,v) ≤ s K₁ ‖x‖²_* + s⁻¹ K₂ ‖v‖²_j` for all `s > 0`"),
    ("prop_strang", [("ExpWeight.strang", "Continuity.lean")], "squared"),
    ("lemma_approx", [("ErrorData.approx_D", "Apriori.lean"), ("ErrorData.approx_C", "Apriori.lean")],
     "squared; Case C without using `‖w‖_∞ ≃ 1` and `h ≲ 1`"),
    ("thm_apriori", [("ErrorData.apriori_D", "Apriori.lean"), ("ErrorData.apriori_C", "Apriori.lean"),
                     ("ErrorData.apriori_C_paper", "Apriori.lean")],
     "squared; `apriori_C_paper` is the form of the paper and has `‖w‖_∞ ≃ 1` as hypotheses"),
]

INTERMEDIATE = [
    ("lemma_IP_coercivity", [("Weight.IP_coercivity", "Coercivity.lean")]),
    ("prop_symm_testing", [("Setting.symm_testing", "Coercivity.lean")]),
    ("lemma_weighted_symm_testing", [("ExpWeight.weighted_symm_testing", "WeightedTesting.lean")]),
    ("lemma_y_jumps", [("Setting.y_jumps", "Lapp.lean")]),
    ("lemma_derivative_testing", [("Setting.derivative_testing", "Derivative.lean")]),
    ("lemma_test_fun_bnd", [("Setting.tnj2_y_le", "Stability.lean"),
                            ("ExpWeight.tnj2_Pw_le", "Stability.lean")]),
]

NOT_FORMALISED = ["cor_final_bound"]


def check_decl(decl, file):
    short = decl.split(".")[-1]
    text = (SRC / file).read_text()
    if not re.search(r"^theorem (?:[\w.]*\.)?" + re.escape(short) + r"\b", text, re.M):
        sys.exit(f"declaration {decl} not found in {file}")


def cell(text):
    """resolve quoted labels and escape the column separator"""
    text = re.sub(r"`([\w:]+)`", lambda m: ref(m.group(1)) if m.group(1) in NUM else m.group(0), text)
    return text.replace("|", "\\|")


def table(groups):
    out = []
    for title, rows in groups:
        out.append(f"\n**{title}**\n")
        out.append("| Lean field | Paper | Relation |")
        out.append("|---|---|---|")
        for fields, labels, text in rows:
            out.append(f"| {', '.join('`'+f+'`' for f in fields)} | {refs(labels)} | {cell(text)} |")
    return "\n".join(out)


def git(*args):
    try:
        return subprocess.run(["git", *args], cwd=ROOT.parent, capture_output=True, text=True).stdout.strip()
    except OSError:
        return ""


def main():
    setting = (SRC / "Setting.lean").read_text()
    fields = set(re.findall(r"^  ([^\W\d]\w*'?) :", setting, re.M))
    listed = {f for groups in (SETTING, WEIGHT, EXPWEIGHT, ERRORDATA) for _, rows in groups
              for fs, _, _ in rows for f in fs}
    if listed - fields:
        sys.exit(f"not a field of Setting.lean: {sorted(listed - fields)}")
    if fields - listed - DATA:
        sys.exit(f"fields of Setting.lean missing from the table: {sorted(fields - listed - DATA)}")
    for _, decls, *_ in RESULTS + INTERMEDIATE:
        for d, f in decls:
            check_decl(d, f)

    commit = git("log", "-1", "--format=%h", "--", "st_article.tex")
    dirty = " (with uncommitted changes)" if git("status", "--porcelain", "--", "st_article.tex") else ""
    toolchain = (ROOT / "lean-toolchain").read_text().strip()

    md = [f"""# Lean formalisation and paper: translation table

<!-- generated by scripts/assumption_table.py; do not edit by hand -->

Numbers refer to the paper as compiled from `st_article.tex`, commit `{commit}`{dirty}.
Lean toolchain: `{toolchain}`.

## What is formalised

The analysis of the paper is derived in Lean from an explicit list of assumptions, all of
which are fields of four structures in `StDgdg/Setting.lean`:

* `Setting`: the spaces, operators and forms of the method and the discrete inequalities,
* `Weight`: a temporal weight `φ(t)` (instances: `φ ≡ 1` and `φ = e^{{-σt}}`),
* `ExpWeight`: the exponential weight with the temporal projection `Π_t`,
* `ErrorData`: exact solution, interpolant and discrete solution.

The derivations are checked by the Lean kernel. The assumptions themselves are not proven in
general; they are proven for three model problems (see below).

## Reading the Lean statements

* Spaces are abstract real vector spaces, operators are linear maps, and every `L²`-type
  inner product (and the Ghost penalty form) is a symmetric positive semidefinite bilinear
  form. Norms appear squared, as `b u u`.
* The paper states the discrete inequalities for one element or facet; in Lean they are
  summed over the active elements or facets of one time slab.
* Every hidden constant of `≲` is an explicit function of `C`, `γ_J`, `λ` (`Consts`) and
  `σ`, `c0`, `C_φ`, `C_s` (`WConsts`) only.
* Time slabs are numbered `0, …, N−1` (paper: `1, …, N`).
* An assumption without a membership condition (for all `v : X`) is a requirement on the
  choice of the space `X`, see the header of `Setting.lean`.

## The assumptions

### `Setting`
{table(SETTING)}

### `Weight`
{table(WEIGHT)}

### `ExpWeight`
{table(EXPWEIGHT)}

### `ErrorData`
{table(ERRORDATA)}

## The results

| Paper | Lean | Form of the statement |
|---|---|---|"""]
    for label, decls, text in RESULTS:
        md.append(f"| {ref(label)} | {', '.join(f'`{d}` ({f})' for d, f in decls)} | {cell(text)} |")
    md.append("\nIntermediate results (steps of the proof of the stability theorem):\n")
    md.append("| Paper | Lean |")
    md.append("|---|---|")
    for label, decls in INTERMEDIATE:
        md.append(f"| {ref(label)} | {', '.join(f'`{d}` ({f})' for d, f in decls)} |")
    md.append("\nNot formalised: " + ", ".join(ref(l) for l in NOT_FORMALISED) + ".")
    md.append("""
## Validation examples

In each of the following models every assumption of `Setting`, `Weight` and `ExpWeight` is
proven in Lean (from Mathlib, without further assumptions):

| Folder | Model problem | Exercises in particular |
|---|---|---|
| `Ode/` | DG(1) in time for an ODE (no space) | integration by parts, trace and inverse inequalities in time, the weight `e^{-σt}`, superapproximation; also `ErrorData`, so that the a priori estimate holds without assumptions |
| `Cut1d/` | heat equation on a fixed interval, cut at arbitrary positions (Case D, `w = 0`) | Ghost penalty estimates uniformly in the cut position, spatial trace and inverse inequalities, facet splitting, Nitsche terms |
| `Move1d/` | convection-diffusion on a moving interval, constant `w > 0`, both regimes | integration by parts on moving cut elements, upwind facet terms, Ghost penalty with swept elements, `𝓛 = ∂_t + w ∂_x` |

Not covered by the examples: more than one space dimension, polynomial degrees above one,
a variable velocity (`w_h ≠ w`, a changing upwind side), and `ErrorData` in one space dimension.
""")
    if MISSING:
        sys.exit(f"labels not found in {AUX}: {sorted(set(MISSING))}")
    (ROOT / "ASSUMPTIONS.md").write_text("\n".join(md))
    print(f"wrote ASSUMPTIONS.md ({len(listed)} assumption fields, paper commit {commit}{dirty})")


if __name__ == "__main__":
    main()
