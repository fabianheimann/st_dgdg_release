import StDgdg.Basic

/-!
# The abstract setting (ALL ASSUMPTIONS LIVE IN THIS FILE)

This file contains every assumption that the formalisation of Sections 4 and 5 of
`st_article.tex` relies on. Nothing here is proven; everything in the other files is.
Each assumption is tagged with the LaTeX label of its counterpart in the paper; the file
`ASSUMPTIONS.md` translates the labels into the numbers of the compiled paper and explains
how each assumption follows from the statements of the paper.

## Modelling

* `X`  : scalar functions on the active mesh that are piecewise smooth
         (contains `W_h`, `φ·W_h`, `Π_t(φ W_h)` and the interpolation error),
* `Fs` : (traces of) functions on the spatial facets `F × I_n`,
* `Ts` : (traces of) functions at fixed time levels,
* `ι`  : index set of the spatial coordinates (`∇ = (∂_i)_{i ∈ ι}`).

All of these are *parameters*: abstract real vector spaces, with abstract linear maps and
symmetric positive semidefinite bilinear forms (`SemiIP`, see `Basic.lean`) between them.
Nothing says that the elements of `X` are functions or that the forms are integrals; the
operators and forms are related only by the assumptions below.

## How to read an assumption without a membership condition

Some assumptions are stated for all `v : X` (`trace_time_cont`, `trace_up_cont`, `mat_dt`,
`Lc_dt`, `ibp` and the laws of the weight). They are not claims about arbitrary functions
but requirements on the choice of `X`: whoever instantiates the setting has to choose `X` such
that they hold on all of it. The intended choice is a space of functions which are in `H¹`
of every active prism (piecewise smooth, as `dt` and `dx` map `X` to `X`; an exact solution
of finite regularity is reached by density). In the proofs they are applied only to

* `trace_time_cont`: the remainder `r = Π_t(φu) - φu`, `u ∈ W_h`, and the interpolation
  error `e = u^e - I_h u^e`,
* `trace_up_cont`: the interpolation error `e`,
* `mat_dt`, `Lc_dt`, `ibp`, weight laws: discrete functions, `φu`, `r` and `e`.

## Conventions

* Time slabs are indexed by `n = 0, …, N-1` (the paper uses `1, …, N`): slab `n` is
  `(t_n, t_{n+1}]`. All slab-wise objects are indexed by `ℕ`, but every slab-wise assumption
  is only required for `n < N` (and for the time levels `t_0, …, t_N`).
* Norms appear squared, as values `b u u` of the forms.
* The jump is `[u] = u_+ - u_-` (downwind minus upwind), on spatial facets and time levels
  alike, as in the paper. The upwind side may change within a facet; all assumptions on
  jumps are quadratic and hence insensitive to the orientation.
* The diffusion coefficient `α` is a constant.
-/

namespace StDgdg

open Finset

/-- The two parameter regimes of the paper. -/
inductive Regime
  | D  -- diffusion dominated,  `eq:ass_caseD`
  | C  -- convection dominated, `eq:ass_caseC`
  deriving DecidableEq

/-- The constants on which all derived constants are allowed to depend
("`≲`" hides exactly functions of these). -/
structure Consts where
  /-- one generic constant for all primitive inequalities (shape regularity, polynomial
  degrees, `ass:gp`, regime constants, norm of `w` in `W^{1,∞}` relative to `‖w‖_∞`) -/
  C : ℝ
  /-- Ghost penalty parameter `γ_J` -/
  γJ : ℝ
  /-- interior penalty parameter `λ` -/
  lam : ℝ
  hC : 1 ≤ C
  hγJ : 0 < γJ
  hlam : 0 < lam

variable (P : Consts) (ι X Fs Ts : Type*) [Fintype ι]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Fs] [Module ℝ Fs] [AddCommGroup Ts] [Module ℝ Ts]

/-- The abstract space-time DG setting. -/
structure Setting where
  /- ### discretisation and problem parameters -/
  regime : Regime
  N : ℕ
  h : ℝ
  τ : ℝ      -- Δt
  α : ℝ
  wInf : ℝ   -- ‖w‖_∞
  h_pos : 0 < h
  τ_pos : 0 < τ
  τ_le_one : τ ≤ 1
  /-- `h ≲ 1` (standing assumption of `ssec:prelim`) -/
  h_le : h ≤ P.C
  α_nonneg : 0 ≤ α
  wInf_nonneg : 0 ≤ wInf
  /-- Case D, `eq:ass_caseD`: `h² ≲ α Δt` and `‖w‖_∞² Δt ≲ α`. -/
  caseD : regime = .D → h ^ 2 ≤ P.C * α * τ ∧ wInf ^ 2 * τ ≤ P.C * α
  /-- Case C, `eq:ass_caseC`: `h ≃ ‖w‖_∞ Δt`. -/
  caseC : regime = .C → wInf * τ ≤ P.C * h ∧ h ≤ P.C * wInf * τ
  /- ### spaces and operators -/
  /-- the discrete space `W_h` -/
  Wh : Submodule ℝ X
  /-- functions which are piecewise polynomial in space (no condition in time), cf.
  `lemma_w_jumps`. The spatial trace and inverse inequalities are assumed on this larger
  space, as they are applied to the remainder `Π_t(φu) - φu`, which is not in `W_h`. -/
  Ws : Submodule ℝ X
  Wh_le_Ws : Wh ≤ Ws
  /-- `∂_t` -/
  dt : X →ₗ[ℝ] X
  /-- `∂_i` (broken spatial partial derivatives) -/
  dx : ι → X →ₗ[ℝ] X
  /-- the material derivative `w^* · ∇^* = ∂_t + w · ∇` -/
  mat : X →ₗ[ℝ] X
  /-- `𝓛` (`∂_t` in Case D, `w^* · ∇^*` in Case C) -/
  Lc : X →ₗ[ℝ] X
  /-- `𝓛_h`, `eq:def_Lapp` -/
  Lh : X →ₗ[ℝ] X
  /-- upwind trace `u_-` on spatial facets -/
  up : X →ₗ[ℝ] Fs
  /-- downwind trace `u_+` on spatial facets -/
  dn : X →ₗ[ℝ] Fs
  /-- `{∇u · n}` on spatial facets -/
  nfl : X →ₗ[ℝ] Fs
  /-- `bot n u = u_+(t_n)`: trace at the bottom of slab `n` -/
  bot : ℕ → X →ₗ[ℝ] Ts
  /-- `top n u = u_-(t_{n+1})`: trace at the top of slab `n` -/
  top : ℕ → X →ₗ[ℝ] Ts
  dx_mem : ∀ i u, u ∈ Wh → dx i u ∈ Wh
  Lh_mem : ∀ u, u ∈ Wh → Lh u ∈ Wh
  /- ### inner products -/
  /-- `(·,·)_{Q^n}` (physical part of slab `n`) -/
  Q : ℕ → SemiIP X
  /-- `(·,·)_{𝒬_T^n}` (full active prisms of slab `n`) -/
  QT : ℕ → SemiIP X
  /-- `j_h^n(·,·)`, `eq:def_jhn` -/
  j : ℕ → SemiIP X
  /-- `(·,·)_{𝒬_F^n ∩ Q}` -/
  FQ : ℕ → SemiIP Fs
  /-- `(|w·n| ·,·)_{𝒬_F^n ∩ Q}` -/
  FQw : ℕ → SemiIP Fs
  /-- `(·,·)` over the full stabilised facets `F × I_n`, `F ∈ 𝓕_h^n ∩ 𝓕^n_gp` -/
  Fgp : ℕ → SemiIP Fs
  /-- `(·,·)` over the interior facets `F × I_n ⊆ closure Q^n`, `F ∈ 𝓕^n_int` -/
  Fint : ℕ → SemiIP Fs
  /-- `(·,·)_{Ω^k}`, `Ω^k = Ω(t_k)` -/
  Om : ℕ → SemiIP Ts
  /- ### monotonicity of the forms (consequences of the domain inclusions)

  These are inequalities between squared norms. They follow from the inclusions of the
  domains of integration (not conversely); no property of sets is assumed. -/
  /-- follows from `Q^n ⊆ 𝒬_T^n` -/
  Q_le_QT : ∀ n, n < N → ∀ u, Q n u u ≤ QT n u u
  /-- follows from `𝒬_F^n ∩ Q ⊆ 𝒬_F^gp ∪ 𝒬_F^int`, `eq:def_int_facets` -/
  FQ_le : ∀ n, n < N → ∀ a, FQ n a a ≤ Fgp n a a + Fint n a a
  /-- follows from the interior facets being contained in `closure Q`, `eq:def_int_facets` -/
  Fint_le_FQ : ∀ n, n < N → ∀ a, Fint n a a ≤ FQ n a a
  /-- bound of the weight: `|w·n| ≤ ‖w‖_∞` (not an inclusion) -/
  FQw_le : ∀ n, n < N → ∀ a, FQw n a a ≤ wInf * FQ n a a
  /- ### standard discrete inequalities on full prisms, `eq:std_discrete_ineqs`

  The paper states them for one element and one facet. Here they are summed over the active
  facets resp. elements of slab `n`; the right hand sides are norms over the full prisms. -/
  /-- `eq:std_trace`, first inequality, for the upwind trace: pointwise on a facet
  `|u_-|² ≤ |u|_{T₁}|² + |u|_{T₂}|²`, then `eq:std_trace` on both neighbours and summation
  over the active facets `𝓕_h^n = (𝓕_h^n ∩ 𝓕^n_gp) ∪ 𝓕^n_int`. -/
  trace_up : ∀ n, n < N → ∀ v, v ∈ Ws → Fgp n (up v) (up v) + Fint n (up v) (up v) ≤ P.C * h⁻¹ * QT n v v
  /-- the same for the downwind trace -/
  trace_dn : ∀ n, n < N → ∀ v, v ∈ Ws → Fgp n (dn v) (dn v) + Fint n (dn v) (dn v) ≤ P.C * h⁻¹ * QT n v v
  /-- `eq:std_trace`, first inequality, applied to `∇v` and averaged over the two sides of
  a facet; no displayed counterpart, used in the proof of `lemma_IP_coercivity` -/
  trace_nfl : ∀ n, n < N → ∀ v, v ∈ Ws →
    Fgp n (nfl v) (nfl v) + Fint n (nfl v) (nfl v) ≤ P.C * h⁻¹ * ∑ i, QT n (dx i v) (dx i v)
  /-- `eq:std_trace`, second inequality, summed (first inequality of
  `lemma_bound_tn_ag_temporal_vol`): `Ω(t_n)` and `Ω(t_{n+1})` are covered by the active
  elements of slab `n` -/
  trace_time : ∀ n, n < N → ∀ v, v ∈ Wh →
    Om n (bot n v) (bot n v) + Om (n + 1) (top n v) (top n v) ≤ P.C * τ⁻¹ * QT n v v
  /-- `eq:cont_trace`, second inequality, summed in the same way -/
  trace_time_cont : ∀ n, n < N → ∀ v,
    Om n (bot n v) (bot n v) + Om (n + 1) (top n v) (top n v)
      ≤ P.C * (τ⁻¹ * QT n v v + τ * QT n (dt v) (dt v))
  /-- `eq:cont_trace`, first inequality, multiplied by `h`, for the upwind trace, summed
  over the active facets of slab `n` -/
  trace_up_cont : ∀ n, n < N → ∀ v, h * (Fgp n (up v) (up v) + Fint n (up v) (up v))
    ≤ P.C * (QT n v v + h ^ 2 * ∑ i, QT n (dx i v) (dx i v))
  /-- `eq:std_inverse`, first inequality, summed -/
  inv_dx : ∀ n, n < N → ∀ v, v ∈ Ws → ∑ i, QT n (dx i v) (dx i v) ≤ P.C * h⁻¹ ^ 2 * QT n v v
  /- ### Ghost penalty -/
  /-- `lemma_gp_E_IpGP` -/
  gp : ∀ n, n < N → ∀ v, v ∈ Wh → QT n v v ≤ P.C * (j n v v + Q n v v)
  /-- `gp_inv_ineq`, spatial part: an inverse inequality within the Ghost penalty form.
  It does not follow from `gp` and `inv_dx`; the paper uses that the polynomial extension
  commutes with `∇`. (The temporal part of `gp_inv_ineq` is contained in `Lh_gp`.) -/
  gp_inv_dx : ∀ n, n < N → ∀ v, v ∈ Wh → ∑ i, j n (dx i v) (dx i v) ≤ P.C * h⁻¹ ^ 2 * j n v v
  /-- the core step of the proof of `lemma_gp_facet_jumps`, slab-wise and without the
  scaling: on the stabilised facets the jump is controlled by the Ghost penalty.
  `lemma_gp_facet_jumps` follows by multiplying with `α h⁻¹ + ‖w‖_∞` and summing. -/
  gp_facet : ∀ n, n < N → ∀ v, v ∈ Wh → Fgp n (dn v - up v) (dn v - up v) ≤ P.C * h⁻¹ * j n v v
  /- ### the derivatives `𝓛`, `𝓛_h` and `w^*·∇^*` -/
  /-- `eq_Lapp_diff` (`𝓛 = 𝓛_h` in Case D; in Case C from `‖w - w_h‖_∞ ≲ h`) -/
  Lc_Lh : ∀ n, n < N → ∀ u, u ∈ Wh →
    Q n (Lc u - Lh u) (Lc u - Lh u) ≤ P.C * h ^ 2 * ∑ i, Q n (dx i u) (dx i u)
  /-- `eq_Lapp_inverse`, second part -/
  Lh_inv_grad : ∀ n, n < N → ∀ u, u ∈ Wh →
    ∑ i, QT n (dx i (Lh u)) (dx i (Lh u)) ≤ P.C * τ⁻¹ ^ 2 * ∑ i, QT n (dx i u) (dx i u)
  /-- `eq_Lapp_gp`. The volume term stems from the jump of `w_h` across the patch (times
  the gradient of `u`) and cannot be replaced by `j_h^n(u,u)`; it is absent in Case D. -/
  Lh_gp : ∀ n, n < N → ∀ u, u ∈ Wh →
    j n (Lh u) (Lh u) ≤ P.C * (τ⁻¹ ^ 2 * j n u u + h ^ 2 * ∑ i, QT n (dx i u) (dx i u))
  /-- interior facet part of the proof of `lemma_y_jumps` (no displayed counterpart):
  `[𝓛_h u] = ∂_t [u] + w_h · [∇u]`; temporal inverse inequality on `F × I_n` for the first
  part, and (Case C) the trace inequality `eq:std_trace` for `∇u` plus `‖w‖_∞ Δt ≲ h` for
  the second, which leaves the factor `h` -/
  Lh_int_jump : ∀ n, n < N → ∀ u, u ∈ Wh →
    Fint n (dn (Lh u) - up (Lh u)) (dn (Lh u) - up (Lh u))
      ≤ P.C * τ⁻¹ ^ 2 * (Fint n (dn u - up u) (dn u - up u) + h * ∑ i, QT n (dx i u) (dx i u))
  /-- inverse inequality for `𝓛` (`eq:std_inverse`, in Case C with `‖w‖_∞ Δt ≲ h`),
  used in the proof of `lemma_test_fun_bnd` -/
  Lc_inv : ∀ n, n < N → ∀ v, v ∈ Wh → Q n (Lc v) (Lc v) ≤ P.C * τ⁻¹ ^ 2 * QT n v v
  /-- `|w · ∇v| ≤ ‖w‖_∞ |∇v|` for `w^*·∇^* = ∂_t + w·∇` -/
  mat_dt : ∀ n, n < N → ∀ v, Q n (mat v - dt v) (mat v - dt v) ≤ wInf ^ 2 * ∑ i, Q n (dx i v) (dx i v)
  /-- same for `𝓛` (`𝓛 = ∂_t` in Case D, `𝓛 = ∂_t + w·∇` in Case C) -/
  Lc_dt : ∀ n, n < N → ∀ v, Q n (Lc v - dt v) (Lc v - dt v) ≤ wInf ^ 2 * ∑ i, Q n (dx i v) (dx i v)
  /-- in Case C, `𝓛 = w^*·∇^*` -/
  mat_Lc : regime = .C → mat = Lc
  /- ### integration by parts -/
  /-- Space-time integration by parts on the cut prisms of slab `n`, summed over the
  elements; first display in the proof of `lemma_B_Bmc` (uses `div w = 0` and
  `w^*·n^* = 0` on the lateral boundary of `Q`). -/
  ibp : ∀ n, n < N → ∀ u v,
    Q n (mat u) v = -Q n u (mat v) + Om (n + 1) (top n u) (top n v) - Om n (bot n u) (bot n v)
      + FQw n (up u) (up v) - FQw n (dn u) (dn v)

namespace Setting

variable {P ι X Fs Ts} (S : Setting P ι X Fs Ts)

/-! ### Derived notation

Most symbols of this block are auxiliary: squared norms, per slab or summed over the slabs,
which serve as building blocks and have no named counterpart in the paper. The norms of the
paper are `upw2`, `c2`, `cj2`, `J2`, `tnj2` (and `tn2`, `tnstar2` below). -/

/-- upwind jump `[u] = u_+ - u_-` on spatial facets -/
def jmp : X →ₗ[ℝ] Fs := S.dn - S.up

/-- the trace from the previous slab at `t_n` (`0` for `n = 0`, i.e. `u_- := 0` on `Ω^0`) -/
def prev : ℕ → X →ₗ[ℝ] Ts
  | 0 => 0
  | n + 1 => S.top n

/-- temporal upwind jump at `t_n` -/
def tjump (n : ℕ) : X →ₗ[ℝ] Ts := S.bot n - S.prev n

/-- `c_J = γ_J (α / h² + ‖w‖_∞ / h)`, `eq:def_J` -/
noncomputable def cJ : ℝ := P.γJ * (S.α * S.h⁻¹ ^ 2 + S.wInf * S.h⁻¹)

/-- `‖∇u‖²_{Q^n}` -/
def gQs (n : ℕ) (u : X) : ℝ := ∑ i, S.Q n (S.dx i u) (S.dx i u)
/-- `‖∇u‖²_{𝒬_T^n}` -/
def gQTs (n : ℕ) (u : X) : ℝ := ∑ i, S.QT n (S.dx i u) (S.dx i u)
/-- `‖a‖²` over all full facets of slab `n` -/
def Ffull (n : ℕ) (a : Fs) : ℝ := S.Fgp n a a + S.Fint n a a

/-- `‖u‖²_Q` -/
def nQ (u : X) : ℝ := ∑ n ∈ range S.N, S.Q n u u
/-- `‖u‖²_{𝒬_T}` -/
def nQT (u : X) : ℝ := ∑ n ∈ range S.N, S.QT n u u
/-- `‖∇u‖²_Q` -/
def gQ (u : X) : ℝ := ∑ n ∈ range S.N, S.gQs n u
/-- `‖∇u‖²_{𝒬_T}` -/
def gQT (u : X) : ℝ := ∑ n ∈ range S.N, S.gQTs n u
/-- `‖[u]‖²_{𝒬_F ∩ Q}` -/
def jQ (u : X) : ℝ := ∑ n ∈ range S.N, S.FQ n (S.jmp u) (S.jmp u)
/-- `∑_n j_h^n(u,u)` -/
def jh (u : X) : ℝ := ∑ n ∈ range S.N, S.j n u u
/-- `|u|_J² = J(u,u)` -/
noncomputable def J2 (u : X) : ℝ := S.cJ * S.jh u

/-- `|||u|||²_{upw}` (the space-time upwind seminorm `eq:upwnorm`) -/
def upw2 (u : X) : ℝ :=
  ∑ n ∈ range S.N, (S.Om n (S.tjump n u) (S.tjump n u) + S.FQw n (S.jmp u) (S.jmp u))
    + S.Om S.N (S.prev S.N u) (S.prev S.N u)

/-- `‖u‖_c²`, `eq_def_coerc_norm` -/
noncomputable def c2 (u : X) : ℝ := S.nQ u + S.α * (S.gQ u + S.h⁻¹ * S.jQ u) + S.upw2 u
/-- `‖u‖_{c,j}²` -/
noncomputable def cj2 (u : X) : ℝ := S.c2 u + S.J2 u
/-- `Δt ‖𝓛u‖_Q²` -/
def L2 (u : X) : ℝ := S.τ * S.nQ (S.Lc u)
/-- `|||u|||_j²`, `eq_def_tripplenorm` -/
noncomputable def tnj2 (u : X) : ℝ := S.L2 u + S.cj2 u

/-! ### The bilinear forms of the method -/

/-- `C(u,v) = (∂_t u + w·∇u, v)_Q` -/
def Cb (u v : X) : ℝ := ∑ n ∈ range S.N, S.Q n (S.mat u) v
/-- `A(u,v) = α (∇u, ∇v)_Q` -/
def Ab (u v : X) : ℝ := S.α * ∑ n ∈ range S.N, ∑ i, S.Q n (S.dx i u) (S.dx i v)
/-- `U_h(u,v) = (|w·n| [u], v_+)_{𝒬_F ∩ Q} + ∑_n ([u], v_+)_{Ω^n}` -/
def Ub (u v : X) : ℝ :=
  ∑ n ∈ range S.N, (S.FQw n (S.jmp u) (S.dn v) + S.Om n (S.tjump n u) (S.bot n v))
/-- `N_h(u,v)`, symmetric interior penalty terms. With `[u] = u_+ - u_-` and `n` pointing
from the upwind to the downwind side the consistency terms carry a positive sign (cf. the
remark after the definition of `N_h` in the paper); `α` is constant and stands in front. -/
noncomputable def Nb (u v : X) : ℝ :=
  ∑ n ∈ range S.N, (S.α * S.FQ n (S.nfl u) (S.jmp v) + S.α * S.FQ n (S.nfl v) (S.jmp u)
    + S.α * P.lam * S.h⁻¹ * S.FQ n (S.jmp u) (S.jmp v))
/-- `J(u,v)`, `eq:def_J` -/
noncomputable def Jb (u v : X) : ℝ := S.cJ * ∑ n ∈ range S.N, S.j n u v
/-- `B_h + J` -/
noncomputable def BJ (u v : X) : ℝ := S.Cb u v + S.Ub u v + S.Ab u v + S.Nb u v + S.Jb u v
/-- `B_h = C + U_h + A + N_h` -/
noncomputable def Bh (u v : X) : ℝ := S.Cb u v + S.Ub u v + S.Ab u v + S.Nb u v

/-! ### The norms `|||·|||` and `|||·|||_*` -/

/-- `|||u|||² = Δt ‖𝓛u‖_Q² + ‖u‖_c²`, `eq_def_tripplenorm` -/
noncomputable def tn2 (u : X) : ℝ := S.L2 u + S.c2 u
/-- `∑_{n=1}^N ‖u_-‖²_{Ω^n}` (auxiliary: third summand of `|||·|||_*²`) -/
def TT (u : X) : ℝ := ∑ n ∈ range S.N, S.Om (n + 1) (S.top n u) (S.top n u)
/-- `‖u_-‖²_{𝒬_F ∩ Q}` (auxiliary: in the fourth summand of `|||·|||_*²`) -/
def FU (u : X) : ℝ := ∑ n ∈ range S.N, S.FQ n (S.up u) (S.up u)
/-- `‖{∇u·n}‖²_{𝒬_F ∩ Q}` (auxiliary: in the fifth summand of `|||·|||_*²`) -/
def FN (u : X) : ℝ := ∑ n ∈ range S.N, S.FQ n (S.nfl u) (S.nfl u)
/-- `|||u|||_*²`, `eq_def_tripplenorm_ast` -/
noncomputable def tnstar2 (u : X) : ℝ :=
  S.tn2 u + S.τ⁻¹ * S.nQ u + S.TT u + S.h * S.τ⁻¹ * S.FU u + S.α * (S.h * S.FN u)

end Setting

/-! ### Temporal weights -/

/-- A temporal weight `φ = φ(t) > 0` (multiplication operator), with
`m_n = inf_{I_n} φ = lo n`, `M_n = sup_{I_n} φ = hi n`, `φ(t_k) = phi k`,
`φ' = -σ φ`, `c0 ≤ φ ≤ 1` and `M_n ≤ Cφ m_n`. Instances: `φ ≡ 1` (`σ = 0`) and
`φ = e^{-σ t}`. Every field is a property of multiplication by a function of `t` only
(the commutation fields would fail for `φ = φ(x,t)`). The product rule encodes `φ' = -σ φ`;
for `e^{-σ t}` one has `c0 = e^{-σ T}`, and `M_n ≤ Cφ m_n` requires `σ Δt ≲ 1`. -/
structure Weight {P : Consts} {ι X Fs Ts : Type*} [Fintype ι]
    [AddCommGroup X] [Module ℝ X] [AddCommGroup Fs] [Module ℝ Fs] [AddCommGroup Ts] [Module ℝ Ts]
    (S : Setting P ι X Fs Ts) (σ c0 Cφ : ℝ) where
  /-- `u ↦ φ u` -/
  M : X →ₗ[ℝ] X
  /-- `a ↦ φ a` on facets -/
  Mf : Fs →ₗ[ℝ] Fs
  lo : ℕ → ℝ
  hi : ℕ → ℝ
  phi : ℕ → ℝ
  σ_nonneg : 0 ≤ σ
  c0_pos : 0 < c0
  Cφ_nonneg : 0 ≤ Cφ
  c0_le_lo : ∀ n, n < S.N → c0 ≤ lo n
  hi_le : ∀ n, n < S.N → hi n ≤ Cφ * lo n
  c0_le_phi : ∀ n, n ≤ S.N → c0 ≤ phi n
  phi_le_one : ∀ n, n ≤ S.N → phi n ≤ 1
  /- `φ` commutes with spatial operations and traces -/
  dx_M : ∀ i u, S.dx i (M u) = M (S.dx i u)
  up_M : ∀ u, S.up (M u) = Mf (S.up u)
  dn_M : ∀ u, S.dn (M u) = Mf (S.dn u)
  nfl_M : ∀ u, S.nfl (M u) = Mf (S.nfl u)
  bot_M : ∀ n, n < S.N → ∀ u, S.bot n (M u) = phi n • S.bot n u
  top_M : ∀ n, n < S.N → ∀ u, S.top n (M u) = phi (n + 1) • S.top n u
  /- product rule, `φ' = -σ φ` -/
  mat_M : ∀ u, S.mat (M u) = M (S.mat u) - σ • M u
  Lc_M : ∀ u, S.Lc (M u) = M (S.Lc u) - σ • M u
  /- `φ` is a symmetric multiplier -/
  Q_symm : ∀ n, n < S.N → ∀ u v, S.Q n (M u) v = S.Q n u (M v)
  j_symm : ∀ n, n < S.N → ∀ u v, S.j n (M u) v = S.j n u (M v)
  FQ_symm : ∀ n, n < S.N → ∀ a b, S.FQ n (Mf a) b = S.FQ n a (Mf b)
  FQw_symm : ∀ n, n < S.N → ∀ a b, S.FQw n (Mf a) b = S.FQw n a (Mf b)
  /- `m_n ≤ φ ≤ M_n` on slab `n` -/
  Q_lo : ∀ n, n < S.N → ∀ u, lo n * S.Q n u u ≤ S.Q n u (M u)
  j_lo : ∀ n, n < S.N → ∀ u, lo n * S.j n u u ≤ S.j n u (M u)
  FQ_lo : ∀ n, n < S.N → ∀ a, lo n * S.FQ n a a ≤ S.FQ n a (Mf a)
  FQw_lo : ∀ n, n < S.N → ∀ a, lo n * S.FQw n a a ≤ S.FQw n a (Mf a)
  FQ_hi : ∀ n, n < S.N → ∀ a, S.FQ n a (Mf a) ≤ hi n * S.FQ n a a
  /- `φ² ≤ 1` -/
  Q_contr : ∀ n, n < S.N → ∀ u, S.Q n (M u) (M u) ≤ S.Q n u u
  j_contr : ∀ n, n < S.N → ∀ u, S.j n (M u) (M u) ≤ S.j n u u
  FQ_contr : ∀ n, n < S.N → ∀ a, S.FQ n (Mf a) (Mf a) ≤ S.FQ n a a
  FQw_contr : ∀ n, n < S.N → ∀ a, S.FQw n (Mf a) (Mf a) ≤ S.FQw n a a

/-- Constants of the exponential weight. -/
structure WConsts where
  /-- the weighting parameter `σ` -/
  σ : ℝ
  /-- lower bound `e^{-σ T}` of the weight -/
  c0 : ℝ
  /-- slab-wise comparison constant `C_φ` (`= e` for `σ Δt ≤ 1`) -/
  Cφ : ℝ
  /-- the superapproximation constant `C(φ)` of `lemma_superapprox` -/
  Cs : ℝ
  hσ : 0 < σ
  hCφ : 1 ≤ Cφ
  hCs : 1 ≤ Cs

/-- The exponential weight `φ = e^{-σ t}` together with the temporal `L²` projection
`Π_t`, i.e. the test function `u_w = Π_t(e^{-σ t} u)` and the remainder
`r = (Π_t - Id)(φ u)` of `lemma_weighted_symm_testing`. -/
structure ExpWeight {P : Consts} {ι X Fs Ts : Type*} [Fintype ι]
    [AddCommGroup X] [Module ℝ X] [AddCommGroup Fs] [Module ℝ Fs] [AddCommGroup Ts] [Module ℝ Ts]
    (S : Setting P ι X Fs Ts) (Wc : WConsts) extends Weight S Wc.σ Wc.c0 Wc.Cφ where
  /-- `u ↦ Π_t(φ u)`. Only the properties below are assumed; that `Π_t` is an orthogonal
  projection is not used. -/
  Pw : X →ₗ[ℝ] X
  Pw_mem : ∀ u, u ∈ S.Wh → Pw u ∈ S.Wh
  /-- `r = (Π_t - Id)(φ u)` is a piecewise polynomial in space -/
  r_mem : ∀ u, u ∈ S.Wh → Pw u - M u ∈ S.Ws
  /-- `Π_t` and `φ` commute with `∇` -/
  r_dx : ∀ i u, S.dx i (Pw u - M u) = Pw (S.dx i u) - M (S.dx i u)
  /-- `lemma_superapprox`, `eq_superapprox` -/
  superapprox : ∀ n, n < S.N → ∀ u, u ∈ S.Wh →
    S.QT n (Pw u - M u) (Pw u - M u) ≤ Wc.Cs * S.τ ^ 2 * S.QT n u u
  /-- `lemma_superapprox`, `eq_superapprox_dt` (right-most bound) -/
  superapprox_dt : ∀ n, n < S.N → ∀ u, u ∈ S.Wh →
    S.QT n (S.dt (Pw u - M u)) (S.dt (Pw u - M u)) ≤ Wc.Cs * S.QT n u u
  /-- `lemma_superapprox` on the facets `S = F`, applied to the fixed-orientation jump
  (`eq_superapprox_F`; `eq_r_props_b`, first estimate, facet by facet) -/
  superapprox_gp : ∀ n, n < S.N → ∀ u, u ∈ S.Wh →
    S.Fgp n (S.jmp (Pw u - M u)) (S.jmp (Pw u - M u)) ≤ Wc.Cs * S.τ ^ 2 * S.Fgp n (S.jmp u) (S.jmp u)
  superapprox_int : ∀ n, n < S.N → ∀ u, u ∈ S.Wh →
    S.Fint n (S.jmp (Pw u - M u)) (S.jmp (Pw u - M u))
      ≤ Wc.Cs * S.τ ^ 2 * S.Fint n (S.jmp u) (S.jmp u)
  /-- `lemma_superapprox` on the facet patches, applied to the Ghost penalty jump
  (`eq_superapprox_patch`; `eq_r_props_b`, second estimate) -/
  superapprox_j : ∀ n, n < S.N → ∀ u, u ∈ S.Wh →
    S.j n (Pw u - M u) (Pw u - M u) ≤ Wc.Cs * S.τ ^ 2 * S.j n u u

/-! ### Exact solution, discrete solution and interpolant -/

/-- The data of the error analysis (Section 5). `ue` is (the extension `u^e` of) the exact
solution, `uh` the discrete solution, `Ih = I_h u^e` the interpolant, `e = u^e - I_h u^e`.
`Ci` is the interpolation constant, `U = ‖u‖²_{H^{k_max+2}(Q)}`. -/
structure ErrorData {P : Consts} {ι X Fs Ts : Type*} [Fintype ι]
    [AddCommGroup X] [Module ℝ X] [AddCommGroup Fs] [Module ℝ Fs] [AddCommGroup Ts] [Module ℝ Ts]
    (S : Setting P ι X Fs Ts) (Ci : ℝ) where
  ue : X
  uh : X
  Ih : X
  /-- the right hand side `f_h` -/
  f : X → ℝ
  uh_mem : uh ∈ S.Wh
  Ih_mem : Ih ∈ S.Wh
  /-- `lemma_consistency`: `B_h(u, v) = f_h(v)` -/
  cons : ∀ v, v ∈ S.Wh → S.Bh ue v = f v
  /-- the discrete problem `eq_discrete_problem` -/
  disc : ∀ v, v ∈ S.Wh → S.BJ uh v = f v
  /-- `u` has no jumps across spatial facets -/
  jmp_ue : S.jmp ue = 0
  /-- polynomial degrees -/
  ks : ℕ
  kt : ℕ
  /-- `‖u‖²_{H^{k_max+2}}` -/
  U : ℝ
  /-- `h² ‖D²e‖²_{𝒬_T}` -/
  D2 : ℝ
  hCi : 0 ≤ Ci
  hU : 0 ≤ U
  hD2 : 0 ≤ D2
  /-- `eq:cont_trace` in space applied to `∇e` -/
  nfl_e : S.h * S.FN (ue - Ih) ≤ P.C * (S.gQT (ue - Ih) + D2)
  /-- `eq_interpol_L2` (squared) -/
  i_L2 : S.nQT (ue - Ih) ≤ Ci * (S.τ ^ 2 * S.τ ^ (2 * kt) + S.h ^ 2 * S.h ^ (2 * ks)) * U
  /-- `eq_interpol_dt` (squared) -/
  i_dt : S.nQT (S.dt (ue - Ih)) ≤ Ci * (S.τ ^ (2 * kt) + S.h ^ 2 * S.h ^ (2 * ks)) * U
  /-- `eq_interpol_grad` (squared) -/
  i_grad : S.gQT (ue - Ih) + D2 ≤ Ci * (S.τ ^ 2 * S.τ ^ (2 * kt) + S.h ^ (2 * ks)) * U
  /-- `eq_interpol_jumps` (facet jumps on the full facets and Ghost penalty jumps) -/
  i_jump : S.h⁻¹ * ∑ n ∈ range S.N, (S.Fgp n (S.jmp Ih) (S.jmp Ih) + S.Fint n (S.jmp Ih) (S.jmp Ih))
      + S.h⁻¹ ^ 2 * S.jh Ih ≤ Ci * S.h ^ (2 * ks) * U

end StDgdg
