import StDgdg.Solvability
import StDgdg.Ode.Model
import StDgdg.Cut1d.Simpson

/-!
# Validation examples `d = 1`: element-level facts

Common part of the one-dimensional examples (uniform background mesh `K_i = [ih, (i+1)h]`,
`P¹` in space and time).

A function on the space-time mesh is given, per time slab `n` and element `i`, by two smooth
functions of time `(g₀, g₁)`, meaning `u(x,t) = g₀(t) + g₁(t) ξ`, `ξ = (x - ih)/h`.
Integrals in space are evaluated exactly (Simpson's rule, see `Simpson.lean`).
Nodes are numbered by their left element: node `i` lies between `K_i` and `K_{i+1}`.

This file contains everything that does not depend on the position of the domain: the
operators, the forms on full elements, on nodes and on node patches (Ghost penalty), and the
element-wise inequalities, in particular the Ghost penalty mechanism `patchL`, `patchR`.
-/

namespace StDgdg.Cut1d

open Finset Ode SemiIP

/-- Mesh size, time step and weighting parameter. -/
structure Base where
  h : ℝ
  τ : ℝ
  σ : ℝ
  h_pos : 0 < h
  τ_pos : 0 < τ
  τ_le_one : τ ≤ 1
  σ_pos : 0 < σ
  στ : σ * τ ≤ 1

variable (p : Base)

/-- element-local functions `g₀(t) + g₁(t) ξ` -/
abbrev V := Sm × Sm
/-- functions on the active space-time mesh: slab ↦ element ↦ local function -/
abbrev X := ℕ → ℕ → V
/-- functions on the space-time facets: slab ↦ node ↦ function of time -/
abbrev Fs := ℕ → ℕ → Sm
/-- functions at a time level: element ↦ `(a₀, a₁)`, meaning `a₀ + a₁ ξ` -/
abbrev Ts := ℕ → ℝ × ℝ

/-- `t_k = k Δt`. -/
def tk (k : ℕ) : ℝ := k * p.τ

theorem tk_succ (k : ℕ) : tk p (k + 1) = tk p k + p.τ := by
  unfold tk; push_cast; ring

theorem tk_nonneg (k : ℕ) : 0 ≤ tk p k := mul_nonneg (Nat.cast_nonneg k) p.τ_pos.le

theorem tk_le {k m : ℕ} (h : k ≤ m) : tk p k ≤ tk p m :=
  mul_le_mul_of_nonneg_right (Nat.cast_le.2 h) p.τ_pos.le

theorem τi_pos : 0 < p.τ⁻¹ := inv_pos.2 p.τ_pos
theorem hi_pos : 0 < p.h⁻¹ := inv_pos.2 p.h_pos

/-- `L²(t_n, t_{n+1})` -/
noncomputable abbrev It (n : ℕ) : SemiIP Sm := Iv p.τ_pos (tk p n)

/-- the coefficient `g₀` on slab `n`, element `i` -/
def c0 (n i : ℕ) : X →ₗ[ℝ] Sm where
  toFun u := (u n i).1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-- the coefficient `g₁` on slab `n`, element `i` -/
def c1 (n i : ℕ) : X →ₗ[ℝ] Sm where
  toFun u := (u n i).2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem c0_apply (n i : ℕ) (u : X) : c0 n i u = (u n i).1 := rfl
theorem c1_apply (n i : ℕ) (u : X) : c1 n i u = (u n i).2 := rfl

/-- the function of time `u(ξ, ·)` on slab `n`, element `i` -/
abbrev pt (n i : ℕ) (ξ : ℝ) : X →ₗ[ℝ] Sm := ptL (c0 n i) (c1 n i) ξ

/-- the jump of `u` at node `i`: `u|_{K_i}(ξ=1) - u|_{K_{i+1}}(ξ=0)` -/
def jA (n i : ℕ) : X →ₗ[ℝ] Sm := pt n i 1 - c0 n (i + 1)
/-- the jump of the slope at node `i` -/
def jB (n i : ℕ) : X →ₗ[ℝ] Sm := c1 n i - c1 n (i + 1)

/-! ### Operators -/

/-- `∂_t` -/
noncomputable def dtX : X →ₗ[ℝ] X :=
  LinearMap.pi fun n => LinearMap.pi fun i => (D.comp (c0 n i)).prod (D.comp (c1 n i))

/-- `∂_x`: `(g₀, g₁) ↦ (g₁ / h, 0)` -/
noncomputable def dxX : X →ₗ[ℝ] X :=
  LinearMap.pi fun n => LinearMap.pi fun i => (p.h⁻¹ • c1 n i).prod 0

/-- multiplication by `e^{-σt}` -/
noncomputable def MX : X →ₗ[ℝ] X :=
  LinearMap.pi fun n => LinearMap.pi fun i =>
    ((Mexp p.σ).comp (c0 n i)).prod ((Mexp p.σ).comp (c1 n i))

/-- `u ↦ Π_t(e^{-σt} u)` -/
noncomputable def PwX : X →ₗ[ℝ] X :=
  LinearMap.pi fun n => LinearMap.pi fun i =>
    ((Ode.Pi p.τ_pos (tk p n)).comp ((Mexp p.σ).comp (c0 n i))).prod
      ((Ode.Pi p.τ_pos (tk p n)).comp ((Mexp p.σ).comp (c1 n i)))

/-- `W_h`: `P¹` in time (and, as all of `X`, `P¹` in space). -/
def WhX : Submodule ℝ X where
  carrier := {u | ∀ n i, (u n i).1 ∈ P1 ∧ (u n i).2 ∈ P1}
  add_mem' := fun hu hv n i => ⟨P1.add_mem (hu n i).1 (hv n i).1, P1.add_mem (hu n i).2 (hv n i).2⟩
  zero_mem' := fun _ _ => ⟨P1.zero_mem, P1.zero_mem⟩
  smul_mem' := fun c _ hu n i => ⟨P1.smul_mem c (hu n i).1, P1.smul_mem c (hu n i).2⟩

/-! ### Functionals in time

All forms below are non-negative combinations of `(L u, L v)_{L²(I_n)}` for functionals
`L : X → (functions of time)` which commute with the operators acting in time. -/

/-- `L` commutes with `∂_t`, `e^{-σt}`, `Π_t(e^{-σt} ·)`, and maps `W_h` to `P¹`. -/
structure Compat (n : ℕ) (L : X →ₗ[ℝ] Sm) : Prop where
  dt : ∀ u, L (dtX u) = D (L u)
  M : ∀ u, L (MX p u) = Mexp p.σ (L u)
  Pw : ∀ u, L (PwX p u) = Ode.Pi p.τ_pos (tk p n) (Mexp p.σ (L u))
  mem : ∀ u, u ∈ WhX → L u ∈ P1

theorem compat_c0 (n i : ℕ) : Compat p n (c0 n i) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun u hu => (hu n i).1⟩

theorem compat_c1 (n i : ℕ) : Compat p n (c1 n i) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun u hu => (hu n i).2⟩

variable {p}

theorem Compat.add {n : ℕ} {L L' : X →ₗ[ℝ] Sm} (h : Compat p n L) (h' : Compat p n L') :
    Compat p n (L + L') :=
  ⟨fun u => by simp [h.dt, h'.dt], fun u => by simp [h.M, h'.M],
    fun u => by simp [h.Pw, h'.Pw], fun u hu => P1.add_mem (h.mem u hu) (h'.mem u hu)⟩

theorem Compat.smul {n : ℕ} {L : X →ₗ[ℝ] Sm} (c : ℝ) (h : Compat p n L) :
    Compat p n (c • L) :=
  ⟨fun u => by simp [h.dt], fun u => by simp [h.M],
    fun u => by simp [h.Pw], fun u hu => P1.smul_mem c (h.mem u hu)⟩

theorem Compat.sub {n : ℕ} {L L' : X →ₗ[ℝ] Sm} (h : Compat p n L) (h' : Compat p n L') :
    Compat p n (L - L') :=
  ⟨fun u => by simp [h.dt, h'.dt], fun u => by simp [h.M, h'.M],
    fun u => by simp [h.Pw, h'.Pw], fun u hu => P1.sub_mem (h.mem u hu) (h'.mem u hu)⟩

variable (p)

theorem compat_pt (n i : ℕ) (ξ : ℝ) : Compat p n (pt n i ξ) :=
  (compat_c0 p n i).add ((compat_c1 p n i).smul ξ)

theorem compat_jA (n i : ℕ) : Compat p n (jA n i) := (compat_pt p n i 1).sub (compat_c0 p n (i + 1))
theorem compat_jB (n i : ℕ) : Compat p n (jB n i) := (compat_c1 p n i).sub (compat_c1 p n (i + 1))

section T

variable {p} {n : ℕ} {L : X →ₗ[ℝ] Sm} (hL : Compat p n L)

include hL

/-- inverse inequality in time -/
theorem T_inv {u : X} (hu : u ∈ WhX) :
    It p n (L (dtX u)) (L (dtX u)) ≤ 12 * p.τ⁻¹ ^ 2 * It p n (L u) (L u) := by
  rw [hL.dt]; exact inv_P1 p.τ_pos (tk p n) (hL.mem u hu)

/-- integration by parts in time -/
theorem T_ibp (u v : X) :
    It p n (L (dtX u)) (L v) = -It p n (L u) (L (dtX v))
      + L u (tk p n + p.τ) * L v (tk p n + p.τ) - L u (tk p n) * L v (tk p n) := by
  rw [hL.dt, hL.dt]; exact ip_D _ _ _

/-- discrete trace inequality in time -/
theorem T_trace {u : X} (hu : u ∈ WhX) :
    L u (tk p n) * L u (tk p n) + L u (tk p n + p.τ) * L u (tk p n + p.τ)
      ≤ 6 * p.τ⁻¹ * It p n (L u) (L u) := by
  have := trace_P1 p.τ_pos (tk p n) (hL.mem u hu)
  linarith

/-- continuous trace inequality in time -/
theorem T_trace_cont (u : X) :
    L u (tk p n) * L u (tk p n) + L u (tk p n + p.τ) * L u (tk p n + p.τ)
      ≤ 4 * (p.τ⁻¹ * It p n (L u) (L u)) + 2 * (p.τ * It p n (L (dtX u)) (L (dtX u))) := by
  have hab : tk p n ≤ tk p n + p.τ := le_of_lt (lt_add_of_pos_right _ p.τ_pos)
  have h1 := trace_left hab (L u)
  have h2 := trace_right hab (L u)
  rw [add_sub_cancel_left] at h1 h2
  have h1' := mul_le_mul_of_nonneg_left h1 (τi_pos p).le
  have h2' := mul_le_mul_of_nonneg_left h2 (τi_pos p).le
  have hτ := p.τ_pos
  have e1 : ∀ x : ℝ, p.τ⁻¹ * (p.τ * x) = x := fun x => by field_simp
  have e2 : ∀ x y : ℝ, p.τ⁻¹ * (2 * x + p.τ ^ 2 * y) = 2 * (p.τ⁻¹ * x) + p.τ * y :=
    fun x y => by field_simp
  rw [e1, e2] at h1' h2'
  rw [hL.dt]
  linarith

theorem T_symm (u v : X) : It p n (L (MX p u)) (L v) = It p n (L u) (L (MX p v)) := by
  rw [hL.M, hL.M]; exact ip_Mexp_symm _ _ _ _

theorem T_lo (u : X) :
    Real.exp (-p.σ * tk p (n + 1)) * It p n (L u) (L u) ≤ It p n (L u) (L (MX p u)) := by
  rw [hL.M]
  exact ip_Mexp_lo _ p.σ_pos.le (by rw [tk_succ]) _

theorem T_contr (u : X) : It p n (L (MX p u)) (L (MX p u)) ≤ It p n (L u) (L u) := by
  rw [hL.M]; exact ip_Mexp_contr _ p.σ_pos.le (tk_nonneg p n) _

/-- superapproximation -/
theorem T_sa {u : X} (hu : u ∈ WhX) :
    It p n (L (PwX p u - MX p u)) (L (PwX p u - MX p u))
      ≤ p.σ ^ 2 * p.τ ^ 2 * It p n (L u) (L u) := by
  rw [map_sub, hL.Pw, hL.M]
  exact superapprox_iv p.τ_pos (tk p n) p.σ_pos.le (tk_nonneg p n) (hL.mem u hu)

/-- superapproximation for the time derivative -/
theorem T_sa_dt {u : X} (hu : u ∈ WhX) :
    It p n (L (dtX (PwX p u - MX p u))) (L (dtX (PwX p u - MX p u)))
      ≤ 76 * p.σ ^ 2 * It p n (L u) (L u) := by
  rw [hL.dt, map_sub, hL.Pw, hL.M]
  exact superapprox_dt_iv p.τ_pos (tk p n) p.σ_pos.le (tk_nonneg p n) (hL.mem u hu)

end T

/-- `∫_{I_n} ∫_{K_i ∩ {a ≤ ξ ≤ b}} u v dx dt` -/
noncomputable def elem (n i : ℕ) (a b : ℝ) (hab : a ≤ b) : SemiIP X :=
  simpson (It p n) (c0 n i) (c1 n i) p.h p.h_pos.le a b hab

/-- `(·,·)_{K_i × I_n}` -/
noncomputable abbrev full (n i : ℕ) : SemiIP X := elem p n i 0 1 zero_le_one

theorem It_nonneg (n : ℕ) (f : Sm) : 0 ≤ It p n f f := (It p n).nonneg f

def d0 (i : ℕ) : Ts →ₗ[ℝ] ℝ where
  toFun a := (a i).1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def d1 (i : ℕ) : Ts →ₗ[ℝ] ℝ where
  toFun a := (a i).2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `∫_{K_i ∩ {a ≤ ξ ≤ b}} u v dx` at a fixed time -/
noncomputable def elemR (i : ℕ) (a b : ℝ) (hab : a ≤ b) : SemiIP Ts :=
  simpson OmR (d0 i) (d1 i) p.h p.h_pos.le a b hab

/-- trace at the bottom of slab `n` -/
def botX (n : ℕ) : X →ₗ[ℝ] Ts where
  toFun u := fun i => ((u n i).1 (tk p n), (u n i).2 (tk p n))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-- trace at the top of slab `n` -/
def topX (n : ℕ) : X →ₗ[ℝ] Ts where
  toFun u := fun i => ((u n i).1 (tk p n + p.τ), (u n i).2 (tk p n + p.τ))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem pt_bot (n i : ℕ) (ξ : ℝ) (u : X) :
    ptL (d0 i) (d1 i) ξ (botX p n u) = pt n i ξ u (tk p n) := rfl
theorem pt_top (n i : ℕ) (ξ : ℝ) (u : X) :
    ptL (d0 i) (d1 i) ξ (topX p n u) = pt n i ξ u (tk p n + p.τ) := rfl

def fN (n i : ℕ) : Fs →ₗ[ℝ] Sm where
  toFun a := a n i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- trace from the left element -/
def upX : X →ₗ[ℝ] Fs := LinearMap.pi fun n => LinearMap.pi fun i => pt n i 1
/-- trace from the right element -/
def dnX : X →ₗ[ℝ] Fs := LinearMap.pi fun n => LinearMap.pi fun i => c0 n (i + 1)
/-- `{∂_x u · n}` with `n = -1` (pointing from the right to the left element) -/
noncomputable def nflX : X →ₗ[ℝ] Fs :=
  LinearMap.pi fun n => LinearMap.pi fun i => (-(2 * p.h)⁻¹) • (c1 n i + c1 n (i + 1))

/-- the direct Ghost penalty form on the patch of node `i`:
`∫_{I_n} ∫_{ω_F} ⟦u⟧ ⟦v⟧ = h ∫_{I_n} ∫_{-1}^{1} (A_u + B_u s)(A_v + B_v s) ds dt` -/
noncomputable def jF (n i : ℕ) : SemiIP X where
  B := (2 * p.h) • ((It p n).comap (jA n i)).B + (2 / 3 * p.h) • ((It p n).comap (jB n i)).B
  symm u v := by
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [((It p n).comap (jA n i)).symm u v, ((It p n).comap (jB n i)).symm u v]
  nonneg u := by
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    have := ((It p n).comap (jA n i)).nonneg u
    have := ((It p n).comap (jB n i)).nonneg u
    have := p.h_pos
    positivity

theorem jF_apply (n i : ℕ) (u v : X) :
    jF p n i u v = 2 * p.h * It p n (jA n i u) (jA n i v)
      + 2 / 3 * p.h * It p n (jB n i u) (jB n i v) := rfl

theorem full_nonneg (n i : ℕ) (u : X) : 0 ≤ full p n i u u := (full p n i).nonneg u

theorem div_h {x y K : ℝ} (h : p.h * x ≤ K * y) : x ≤ K * p.h⁻¹ * y := by
  have := mul_le_mul_of_nonneg_left h (hi_pos p).le
  have hh := p.h_pos
  have e1 : p.h⁻¹ * (p.h * x) = x := by field_simp
  rw [e1] at this
  linarith

theorem pt1_le (n i : ℕ) (u : X) :
    It p n (pt n i 1 u) (pt n i 1 u) ≤ 6 * p.h⁻¹ * full p n i u u :=
  div_h p (pt1_le_full _ _ _ _ u)

theorem c0_le (n i : ℕ) (u : X) :
    It p n (c0 n i u) (c0 n i u) ≤ 6 * p.h⁻¹ * full p n i u u :=
  div_h p (pt0_le_full _ _ _ _ u)

theorem c1_le (n i : ℕ) (u : X) :
    It p n (c1 n i u) (c1 n i u) ≤ 24 * p.h⁻¹ * full p n i u u :=
  div_h p (c1_le_full _ _ _ _ u)

/-- `‖∂_x u‖²_{K_i × I_n} = h⁻¹ ‖g₁‖²_{L²(I_n)}` -/
theorem full_dx (n i : ℕ) (u : X) :
    full p n i (dxX p u) (dxX p u) = p.h⁻¹ * It p n (c1 n i u) (c1 n i u) := by
  have e0 : c0 n i (dxX p u) = p.h⁻¹ • c1 n i u := rfl
  have e1 : c1 n i (dxX p u) = 0 := rfl
  unfold full elem
  rw [simpson_const _ _ _ _ _ e1, e0, SemiIP.smul_sq]
  have := p.h_pos
  field_simp
  ring

/-- Simpson weights: an estimate at the three quadrature points gives one for the integral. -/
theorem lift3 {w K x0 xh x1 y0 yh y1 : ℝ} (hw : 0 ≤ w) (h0 : x0 ≤ K * y0) (hh : xh ≤ K * yh)
    (h1 : x1 ≤ K * y1) : w * (x0 + 4 * xh + x1) ≤ K * (w * (y0 + 4 * yh + y1)) := by
  have : x0 + 4 * xh + x1 ≤ K * (y0 + 4 * yh + y1) := by linarith
  have := mul_le_mul_of_nonneg_left this hw
  linarith

theorem patch_arith {h P0 Ph P1 a b q0 qh q1 : ℝ} (hh : 0 ≤ h) (hqh : 0 ≤ qh)
    (k : P0 + 4 * Ph + P1 ≤ 24 * a + 8 * b + 56 * q0 + 56 * q1) :
    h * (1 - 0) / 6 * (P0 + 4 * Ph + P1)
      ≤ 2 * (2 * h * a + 2 / 3 * h * b) + 56 * (h * (1 - 0) / 6 * (q0 + 4 * qh + q1)) := by
  have := mul_le_mul_of_nonneg_left k (by positivity : (0 : ℝ) ≤ h / 6)
  have := mul_nonneg hh hqh
  nlinarith

/-- `I(x + c y) ≤ 2 I(x) + 2 c² I(y)` -/
theorem add_smul_le (I : SemiIP Sm) (x y : Sm) (c : ℝ) :
    I (x + c • y) (x + c • y) ≤ 2 * I x x + 2 * c ^ 2 * I y y := by
  have := I.add_sq_le x (c • y)
  rw [I.smul_sq] at this
  linarith

/-- **Ghost penalty mechanism, cut element on the left**: the norm on `K_i` is controlled by
the Ghost penalty on the patch of node `i` and the norm on the neighbour `K_{i+1}`. -/
theorem patchL (n i : ℕ) (u : X) :
    full p n i u u ≤ 2 * jF p n i u u + 56 * full p n (i + 1) u u := by
  have key : ∀ ξ : ℝ, It p n (pt n i ξ u) (pt n i ξ u)
      ≤ 2 * (2 * It p n (jA n i u) (jA n i u) + 2 * (ξ - 1) ^ 2 * It p n (jB n i u) (jB n i u))
        + 2 * (2 * (1 - (ξ - 1)) ^ 2 * It p n (c0 n (i + 1) u) (c0 n (i + 1) u)
          + 2 * (ξ - 1) ^ 2 * It p n (pt n (i + 1) 1 u) (pt n (i + 1) 1 u)) := by
    intro ξ
    have e : pt n i ξ u = (jA n i u + (ξ - 1) • jB n i u) + pt n (i + 1) (ξ - 1) u := by
      simp only [jA, jB, ptL_apply, LinearMap.sub_apply]; module
    rw [e]
    have h1 := (It p n).add_sq_le (jA n i u + (ξ - 1) • jB n i u) (pt n (i + 1) (ξ - 1) u)
    have h2 := add_smul_le (It p n) (jA n i u) (jB n i u) (ξ - 1)
    have h3 := pt_le (It p n) (c0 n (i + 1)) (c1 n (i + 1)) (ξ - 1) u
    linarith
  have k0 := key 0
  have kh := key (1 / 2)
  have k1 := key 1
  have e0 : pt n (i + 1) 0 u = c0 n (i + 1) u := by simp [ptL_apply]
  have hmid : ((0 : ℝ) + 1) / 2 = 1 / 2 := by norm_num
  rw [jF_apply]
  unfold full elem
  rw [simpson_apply, simpson_apply, e0, hmid]
  norm_num at k0 kh k1
  exact patch_arith p.h_pos.le (It_nonneg p n _)
    (by linarith [It_nonneg p n (jB n i u), It_nonneg p n (jA n i u),
      It_nonneg p n (c0 n (i + 1) u), It_nonneg p n (pt n (i + 1) 1 u)])

/-- **Ghost penalty mechanism, cut element on the right.** -/
theorem patchR (n i : ℕ) (u : X) :
    full p n (i + 1) u u ≤ 2 * jF p n i u u + 56 * full p n i u u := by
  have key : ∀ ξ : ℝ, It p n (pt n (i + 1) ξ u) (pt n (i + 1) ξ u)
      ≤ 2 * (2 * It p n (jA n i u) (jA n i u) + 2 * ξ ^ 2 * It p n (jB n i u) (jB n i u))
        + 2 * (2 * (1 - (1 + ξ)) ^ 2 * It p n (c0 n i u) (c0 n i u)
          + 2 * (1 + ξ) ^ 2 * It p n (pt n i 1 u) (pt n i 1 u)) := by
    intro ξ
    have e : pt n (i + 1) ξ u = -(jA n i u + ξ • jB n i u) + pt n i (1 + ξ) u := by
      simp only [jA, jB, ptL_apply, LinearMap.sub_apply]; module
    rw [e]
    have h1 := (It p n).add_sq_le (-(jA n i u + ξ • jB n i u)) (pt n i (1 + ξ) u)
    rw [SemiIP.neg_sq] at h1
    have h2 := add_smul_le (It p n) (jA n i u) (jB n i u) ξ
    have h3 := pt_le (It p n) (c0 n i) (c1 n i) (1 + ξ) u
    linarith
  have k0 := key 0
  have kh := key (1 / 2)
  have k1 := key 1
  have e0 : pt n i 0 u = c0 n i u := by simp [ptL_apply]
  have hmid : ((0 : ℝ) + 1) / 2 = 1 / 2 := by norm_num
  rw [jF_apply]
  unfold full elem
  rw [simpson_apply, simpson_apply, e0, hmid]
  norm_num at k0 kh k1
  exact patch_arith p.h_pos.le (It_nonneg p n _)
    (by linarith [It_nonneg p n (jB n i u), It_nonneg p n (jA n i u),
      It_nonneg p n (c0 n i u), It_nonneg p n (pt n i 1 u)])

/-- discrete trace inequality in time on one element -/
theorem elem_time (n i : ℕ) {v : X} (hv : v ∈ WhX) :
    elemR p i 0 1 zero_le_one (botX p n v) (botX p n v)
      + elemR p i 0 1 zero_le_one (topX p n v) (topX p n v)
      ≤ 6 * p.τ⁻¹ * full p n i v v := by
  unfold elemR full elem
  rw [simpson_apply, simpson_apply, simpson_apply]
  simp only [OmR_apply, pt_bot, pt_top]
  have t0 := T_trace (compat_pt p n i 0) hv
  have th := T_trace (compat_pt p n i ((0 + 1) / 2)) hv
  have t1 := T_trace (compat_pt p n i 1) hv
  have hw : (0 : ℝ) ≤ p.h * (1 - 0) / 6 := by have := p.h_pos; positivity
  have := lift3 hw t0 th t1
  linarith

/-- continuous trace inequality in time on one element -/
theorem elem_time_cont (n i : ℕ) (v : X) :
    elemR p i 0 1 zero_le_one (botX p n v) (botX p n v)
      + elemR p i 0 1 zero_le_one (topX p n v) (topX p n v)
      ≤ 4 * (p.τ⁻¹ * full p n i v v) + 2 * (p.τ * full p n i (dtX v) (dtX v)) := by
  unfold elemR full elem
  rw [simpson_apply, simpson_apply, simpson_apply, simpson_apply]
  simp only [OmR_apply, pt_bot, pt_top]
  have t0 := T_trace_cont (compat_pt p n i 0) v
  have th := T_trace_cont (compat_pt p n i ((0 + 1) / 2)) v
  have t1 := T_trace_cont (compat_pt p n i 1) v
  have hw : (0 : ℝ) ≤ p.h * (1 - 0) / 6 := by have := p.h_pos; positivity
  have h0 := mul_le_mul_of_nonneg_left t0 hw
  have hh := mul_le_mul_of_nonneg_left th hw
  have h1 := mul_le_mul_of_nonneg_left t1 hw
  linarith

theorem jA_dx (n i : ℕ) (v : X) : jA n i (dxX p v) = p.h⁻¹ • jB n i v := by
  show (p.h⁻¹ • c1 n i v + (1 : ℝ) • (0 : Sm)) - p.h⁻¹ • c1 n (i + 1) v
    = p.h⁻¹ • (c1 n i v - c1 n (i + 1) v)
  module

theorem jB_dx (n i : ℕ) (v : X) : jB n i (dxX p v) = 0 := by
  show (0 : Sm) - 0 = 0
  simp

theorem jF_dx (n i : ℕ) (v : X) :
    jF p n i (dxX p v) (dxX p v) ≤ 3 * p.h⁻¹ ^ 2 * jF p n i v v := by
  rw [jF_apply, jF_apply, jA_dx, jB_dx, SemiIP.smul_sq]
  have hh := p.h_pos; have hhi := hi_pos p
  have a := It_nonneg p n (jA n i v)
  have b := It_nonneg p n (jB n i v)
  simp only [map_zero, mul_zero, add_zero]
  have e : 3 * p.h⁻¹ ^ 2 * (2 * p.h * It p n (jA n i v) (jA n i v)
      + 2 / 3 * p.h * It p n (jB n i v) (jB n i v))
      = 6 * p.h⁻¹ * It p n (jA n i v) (jA n i v) + 2 * p.h⁻¹ * It p n (jB n i v) (jB n i v) := by
    field_simp
    ring
  rw [e]
  have e2 : 2 * p.h * (p.h⁻¹ ^ 2 * It p n (jB n i v) (jB n i v))
      = 2 * p.h⁻¹ * It p n (jB n i v) (jB n i v) := by field_simp
  rw [e2]
  have := mul_nonneg hhi.le a
  linarith

theorem jump_node (n i : ℕ) (v : X) : (dnX v - upX v) n i = -jA n i v := by
  show c0 n (i + 1) v - pt n i 1 v = -(pt n i 1 v - c0 n (i + 1) v)
  abel

theorem jF_dt (n i : ℕ) {u : X} (hu : u ∈ WhX) :
    jF p n i (dtX u) (dtX u) ≤ 12 * p.τ⁻¹ ^ 2 * jF p n i u u := by
  rw [jF_apply, jF_apply]
  have h1 := T_inv (compat_jA p n i) hu
  have h2 := T_inv (compat_jB p n i) hu
  have hh := p.h_pos
  have g1 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * p.h)
  have g2 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 / 3 * p.h)
  linarith

theorem full_dt (n i : ℕ) {v : X} (hv : v ∈ WhX) :
    full p n i (dtX v) (dtX v) ≤ 12 * p.τ⁻¹ ^ 2 * full p n i v v := by
  unfold full elem
  rw [simpson_apply, simpson_apply]
  have hw : (0 : ℝ) ≤ p.h * (1 - 0) / 6 := by have := p.h_pos; positivity
  exact lift3 hw (T_inv (compat_pt p n i 0) hv) (T_inv (compat_pt p n i ((0 + 1) / 2)) hv)
    (T_inv (compat_pt p n i 1) hv)

/-- integration by parts in time on (the physical part of) one element -/
theorem elem_ibp (n i : ℕ) {a b : ℝ} (hab : a ≤ b) (u v : X) :
    elem p n i a b hab (dtX u) v = -elem p n i a b hab u (dtX v)
      + elemR p i a b hab (topX p n u) (topX p n v)
      - elemR p i a b hab (botX p n u) (botX p n v) := by
  unfold elem elemR
  rw [simpson_apply, simpson_apply, simpson_apply, simpson_apply]
  simp only [OmR_apply, pt_bot, pt_top]
  have t0 := T_ibp (compat_pt p n i a) u v
  have th := T_ibp (compat_pt p n i ((a + b) / 2)) u v
  have t1 := T_ibp (compat_pt p n i b) u v
  linear_combination (p.h * (b - a) / 6) * (t0 + 4 * th + t1)

theorem dx_mem' (u : X) (hu : u ∈ WhX) : dxX p u ∈ WhX := fun n i =>
  ⟨P1.smul_mem _ (hu n i).2, P1.zero_mem⟩

theorem dt_mem' (u : X) (hu : u ∈ WhX) : dtX u ∈ WhX := fun n i =>
  ⟨D_mem_P1 (hu n i).1, D_mem_P1 (hu n i).2⟩

/-- multiplication by `e^{-σt}` on the facets -/
noncomputable def MfX : Fs →ₗ[ℝ] Fs :=
  LinearMap.pi fun n => LinearMap.pi fun i => (Mexp p.σ).comp (fN n i)

/-- `φ(t_k) = e^{-σ t_k}` -/
noncomputable def phiX (k : ℕ) : ℝ := Real.exp (-p.σ * tk p k)

theorem phi_le_one' (k : ℕ) : phiX p k ≤ 1 := by
  have := mul_nonneg p.σ_pos.le (tk_nonneg p k)
  exact Real.exp_le_one_iff.2 (by linarith)

theorem hi_le' (n : ℕ) : phiX p n ≤ Real.exp 1 * phiX p (n + 1) := by
  unfold phiX
  rw [← Real.exp_add, tk_succ]
  apply Real.exp_le_exp.2
  have := p.στ
  linarith

theorem lift3_ge {w K x0 xh x1 y0 yh y1 : ℝ} (hw : 0 ≤ w) (h0 : K * y0 ≤ x0) (hh : K * yh ≤ xh)
    (h1 : K * y1 ≤ x1) : K * (w * (y0 + 4 * yh + y1)) ≤ w * (x0 + 4 * xh + x1) := by
  have : K * (y0 + 4 * yh + y1) ≤ x0 + 4 * xh + x1 := by linarith
  have := mul_le_mul_of_nonneg_left this hw
  linarith

theorem dx_M' (u : X) : dxX p (MX p u) = MX p (dxX p u) := by
  funext n i
  show ((p.h⁻¹ • Mexp p.σ (c1 n i u), (0 : Sm)) : V)
    = (Mexp p.σ (p.h⁻¹ • c1 n i u), Mexp p.σ 0)
  rw [map_smul, map_zero]

theorem up_M' (u : X) : upX (MX p u) = MfX p (upX u) := by
  funext n i; exact (compat_pt p n i 1).M u

theorem nfl_M' (u : X) : nflX p (MX p u) = MfX p (nflX p u) := by
  funext n i
  show (-(2 * p.h)⁻¹) • (Mexp p.σ (c1 n i u) + Mexp p.σ (c1 n (i + 1) u))
    = Mexp p.σ ((-(2 * p.h)⁻¹) • (c1 n i u + c1 n (i + 1) u))
  rw [map_smul, map_add]

theorem bot_M' (n : ℕ) (u : X) : botX p n (MX p u) = phiX p n • botX p n u := rfl

theorem top_M' (n : ℕ) (u : X) : topX p n (MX p u) = phiX p (n + 1) • topX p n u := by
  funext i
  show ((Real.exp (-p.σ * (tk p n + p.τ)) * (u n i).1 (tk p n + p.τ),
      Real.exp (-p.σ * (tk p n + p.τ)) * (u n i).2 (tk p n + p.τ)) : ℝ × ℝ)
    = phiX p (n + 1) • ((u n i).1 (tk p n + p.τ), (u n i).2 (tk p n + p.τ))
  unfold phiX
  rw [tk_succ]
  rfl

theorem dt_M' (u : X) : dtX (MX p u) = MX p (dtX u) - p.σ • MX p u := by
  funext n i
  exact Prod.ext (D_Mexp p.σ (u n i).1) (D_Mexp p.σ (u n i).2)

theorem jF_symm (n i : ℕ) (u v : X) : jF p n i (MX p u) v = jF p n i u (MX p v) := by
  rw [jF_apply, jF_apply, T_symm (compat_jA p n i), T_symm (compat_jB p n i)]

theorem jF_lo (n i : ℕ) (u : X) : phiX p (n + 1) * jF p n i u u ≤ jF p n i u (MX p u) := by
  rw [jF_apply, jF_apply]
  have h1 := T_lo (compat_jA p n i) u
  have h2 := T_lo (compat_jB p n i) u
  have hh := p.h_pos
  have g1 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * p.h)
  have g2 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 / 3 * p.h)
  unfold phiX
  linarith

theorem jF_contr (n i : ℕ) (u : X) : jF p n i (MX p u) (MX p u) ≤ jF p n i u u := by
  rw [jF_apply, jF_apply]
  have h1 := T_contr (compat_jA p n i) u
  have h2 := T_contr (compat_jB p n i) u
  have hh := p.h_pos
  have g1 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * p.h)
  have g2 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 / 3 * p.h)
  linarith

theorem jF_sa (n i : ℕ) {u : X} (hu : u ∈ WhX) :
    jF p n i (PwX p u - MX p u) (PwX p u - MX p u) ≤ p.σ ^ 2 * p.τ ^ 2 * jF p n i u u := by
  rw [jF_apply, jF_apply]
  have h1 := T_sa (compat_jA p n i) hu
  have h2 := T_sa (compat_jB p n i) hu
  have hh := p.h_pos
  have g1 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * p.h)
  have g2 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 / 3 * p.h)
  linarith

theorem Cs_ge : p.σ ^ 2 ≤ 1 + 76 * p.σ ^ 2 := by nlinarith [sq_nonneg p.σ]

theorem Pw_mem' (u : X) : PwX p u ∈ WhX := fun _ _ => ⟨Pi_mem _ _ _, Pi_mem _ _ _⟩

theorem r_dx' (u : X) : dxX p (PwX p u - MX p u) = PwX p (dxX p u) - MX p (dxX p u) := by
  funext n i
  show ((p.h⁻¹ • (Ode.Pi p.τ_pos (tk p n) (Mexp p.σ (c1 n i u)) - Mexp p.σ (c1 n i u)),
      (0 : Sm)) : V)
    = (Ode.Pi p.τ_pos (tk p n) (Mexp p.σ (p.h⁻¹ • c1 n i u)) - Mexp p.σ (p.h⁻¹ • c1 n i u),
      Ode.Pi p.τ_pos (tk p n) (Mexp p.σ 0) - Mexp p.σ 0)
  simp only [map_smul, map_zero, sub_zero, smul_sub]

theorem full_sa (n i : ℕ) {u : X} (hu : u ∈ WhX) :
    full p n i (PwX p u - MX p u) (PwX p u - MX p u) ≤ p.σ ^ 2 * p.τ ^ 2 * full p n i u u := by
  unfold full elem
  rw [simpson_apply, simpson_apply]
  have hw : (0 : ℝ) ≤ p.h * (1 - 0) / 6 := by have := p.h_pos; positivity
  exact lift3 hw (T_sa (compat_pt p n i 0) hu) (T_sa (compat_pt p n i ((0 + 1) / 2)) hu)
    (T_sa (compat_pt p n i 1) hu)

theorem full_sa_dt (n i : ℕ) {u : X} (hu : u ∈ WhX) :
    full p n i (dtX (PwX p u - MX p u)) (dtX (PwX p u - MX p u))
      ≤ 76 * p.σ ^ 2 * full p n i u u := by
  unfold full elem
  rw [simpson_apply, simpson_apply]
  have hw : (0 : ℝ) ≤ p.h * (1 - 0) / 6 := by have := p.h_pos; positivity
  exact lift3 hw (T_sa_dt (compat_pt p n i 0) hu) (T_sa_dt (compat_pt p n i ((0 + 1) / 2)) hu)
    (T_sa_dt (compat_pt p n i 1) hu)

/-- superapproximation for the jump at the nodes of a set `s` -/
theorem jump_sa (n : ℕ) (s : Finset ℕ) {u : X} (hu : u ∈ WhX) :
    ∑ i ∈ s, It p n ((dnX (PwX p u - MX p u) - upX (PwX p u - MX p u)) n i)
        ((dnX (PwX p u - MX p u) - upX (PwX p u - MX p u)) n i)
      ≤ (1 + 76 * p.σ ^ 2) * p.τ ^ 2
        * ∑ i ∈ s, It p n ((dnX u - upX u) n i) ((dnX u - upX u) n i) := by
  have h1 : ∑ i ∈ s, It p n ((dnX (PwX p u - MX p u) - upX (PwX p u - MX p u)) n i)
        ((dnX (PwX p u - MX p u) - upX (PwX p u - MX p u)) n i)
      ≤ p.σ ^ 2 * p.τ ^ 2 * ∑ i ∈ s, It p n ((dnX u - upX u) n i) ((dnX u - upX u) n i) :=
    sum_le_mul_sum fun i _ => by
      rw [jump_node, jump_node, SemiIP.neg_sq, SemiIP.neg_sq]
      exact T_sa (compat_jA p n i) hu
  have hS : 0 ≤ ∑ i ∈ s, It p n ((dnX u - upX u) n i) ((dnX u - upX u) n i) :=
    sum_nonneg fun i _ => It_nonneg p n _
  have := mul_le_mul_of_nonneg_right (Cs_ge p) (mul_nonneg (sq_nonneg p.τ) hS)
  nlinarith

end StDgdg.Cut1d
