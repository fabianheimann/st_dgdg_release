# Lean formalisation: unfitted space-time DG methods

Lean 4 / Mathlib formalisation of the analysis of

> F. Heimann, C. Lehrenfeld: *Higher Order Unfitted Discontinuous Galerkin Methods in Space
> and Time.*

Repository: <https://github.com/fabianheimann/st_dgdg_release>

## What is established

The stability, well-posedness and a priori error results of the paper (Sections 4 and 5) are
derived from an explicit list of discrete inequalities and identities. The derivations are
checked by the Lean kernel.

* **Assumed:** the list itself. It consists of the fields of four structures in
  [`StDgdg/Setting.lean`](StDgdg/Setting.lean): trace and inverse inequalities, the Ghost
  penalty estimates, properties of the discrete derivative `𝓛_h`, space-time integration by
  parts, superapproximation of the temporal projection, interpolation estimates and
  consistency. These correspond to the standard results recalled in the paper.
* **Proven from it:** inf-sup stability and unique solvability (Theorem `thm_stability`),
  continuity, the Strang-type lemma, the approximation lemma and the a priori error
  estimates in both parameter regimes.
* **Validated:** in three model problems every assumption on the method is proven in Lean,
  without further assumptions (folders `Ode`, `Cut1d`, `Move1d` below).

[`ASSUMPTIONS.md`](ASSUMPTIONS.md) translates every assumption and every result into the
numbering of the paper and explains how each assumption follows from the paper's statements.

## What is not established

* The assumptions are **not** proven in the general setting of the paper (several space
  dimensions, higher polynomial degrees, general velocity fields and geometries). The model
  problems are an ODE and two problems in one space dimension with piecewise linear functions.
* Spaces, operators and inner products are abstract (real vector spaces, linear maps,
  symmetric positive semidefinite forms). That the Lean statements express the statements of
  the paper has been checked by the authors by reading `Setting.lean` and the statements of
  the main theorems; it is not something Lean can check.
* Norms appear squared, continuity is stated in Young form, and all hidden constants are
  explicit (not sharp) functions of the basic constants.
* The final corollary of the paper (`cor_final_bound`) is not formalised, and consistency
  (`lemma_consistency`) is an assumption, proven only in the ODE example.

## Verify

Requires [elan](https://github.com/leanprover/elan). The Lean version
(`leanprover/lean4:v4.37.0-rc1`) and Mathlib are pinned in `lean-toolchain` and
`lake-manifest.json`.

```sh
lake exe cache get     # download the compiled Mathlib (once)
./scripts/verify.sh    # build, reject `sorry` and extra axioms, print the axioms used
```

The script builds all modules and checks that the main results and the validation examples
depend only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Contents

| File | Content |
|---|---|
| `StDgdg/Setting.lean` | **all assumptions**; definitions of the norms and bilinear forms |
| `StDgdg/Basic.lean` | symmetric positive semidefinite forms, Young inequalities |
| `StDgdg/GP.lean`, `Lapp.lean` | consequences of the Ghost penalty estimates; the discrete derivative |
| `StDgdg/Coercivity.lean`, `Remainder.lean`, `WeightedTesting.lean` | (weighted) symmetric testing |
| `StDgdg/Derivative.lean` | testing with the discrete derivative |
| `StDgdg/Stability.lean`, `Solvability.lean` | inf-sup stability, unique solvability |
| `StDgdg/Continuity.lean` | mass conserving form, continuity, Strang-type lemma |
| `StDgdg/Apriori.lean` | approximation lemma and a priori error estimates |
| `StDgdg/Model.lean` | a trivial model (consistency of the assumptions) |
| `StDgdg/Ode/` | example: DG(1) in time for an ODE, including the error analysis |
| `StDgdg/Cut1d/` | example: heat equation on a fixed interval, cut at arbitrary positions |
| `StDgdg/Move1d/` | example: convection-diffusion on a moving interval, both regimes |
| `scripts/assumption_table.py` | regenerates `ASSUMPTIONS.md` from the compiled paper |
| `scripts/verify.sh` | the verification described above |

## Use of AI

The Lean code was written by Anthropic's Claude (Claude Fable) under the supervision of the
authors. The proofs are checked by Lean and need no trust in their origin. The authors have
read and checked the assumptions, the definitions and the statements of the main theorems.

## License and citation

The contents of this folder are licensed under
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/), see [`LICENSE`](LICENSE): you may
use and adapt them provided that you give credit. Please cite the paper named above.
