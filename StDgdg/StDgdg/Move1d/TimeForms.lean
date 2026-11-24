import StDgdg.Cut1d.Elements
import StDgdg.Move1d.Leibniz

/-!
# Validation example `d = 1`, moving domain, part 2: forms with time-dependent weights

* `Iw n ω`: the weighted form `∫_{I_n} ω(t) f(t) g(t) dt` on functions of time (used for the
  nodes, with `ω` the indicator of the times at which the node lies in the domain),
* `cutX n i a b`: `∫_{I_n} h ∫_{a(t)}^{b(t)} u v dξ dt` on element `i`, for time-dependent cut
  positions `a(t) ≤ b(t)`.
-/

namespace StDgdg.Move1d

open Finset SemiIP Cut1d intervalIntegral
open Ode hiding MX PwX Pw_mem' WhX X botX bot_M' dtX dt_M' hi_le' hi_pos phiX phi_le_one' tk tk_le tk_nonneg tk_succ topX top_M' τi_pos

variable (p : Base)

theorem slab_le (n : ℕ) : tk p n ≤ tk p n + p.τ := le_of_lt (lt_add_of_pos_right _ p.τ_pos)

/-! ### Weighted forms in time -/

section Iw

variable (n : ℕ) (ω : ℝ → ℝ) (hω : ∀ t, 0 ≤ ω t)
  (hint : IntervalIntegrable ω MeasureTheory.volume (tk p n) (tk p n + p.τ))

include hint in
theorem Iw_intble (f g : Sm) :
    IntervalIntegrable (fun t => ω t * (f t * g t)) MeasureTheory.volume (tk p n) (tk p n + p.τ) :=
  hint.mul_continuousOn ((cont f).mul (cont g)).continuousOn

/-- `∫_{I_n} ω f g` -/
noncomputable def Iw : SemiIP Sm where
  B := LinearMap.mk₂ ℝ (fun f g => ∫ t in (tk p n)..(tk p n + p.τ), ω t * (f t * g t))
    (fun f f' g => by
      simp only [Sm.add_apply, add_mul, mul_add]
      exact integral_add (Iw_intble p n ω hint f g) (Iw_intble p n ω hint f' g))
    (fun c f g => by
      simp only [Sm.smul_apply, smul_eq_mul]
      rw [← integral_const_mul]
      congr 1; ext t; ring)
    (fun f g g' => by
      simp only [Sm.add_apply, mul_add]
      exact integral_add (Iw_intble p n ω hint f g) (Iw_intble p n ω hint f g'))
    (fun c f g => by
      simp only [Sm.smul_apply, smul_eq_mul]
      rw [← integral_const_mul]
      congr 1; ext t; ring)
  symm f g := by
    show (∫ t in (tk p n)..(tk p n + p.τ), ω t * (f t * g t))
      = ∫ t in (tk p n)..(tk p n + p.τ), ω t * (g t * f t)
    congr 1; ext t; ring
  nonneg f := integral_nonneg (slab_le p n) fun t _ =>
    mul_nonneg (hω t) (mul_self_nonneg _)

theorem Iw_apply (f g : Sm) :
    Iw p n ω hω hint f g = ∫ t in (tk p n)..(tk p n + p.τ), ω t * (f t * g t) := rfl

theorem It_apply (f g : Sm) :
    It p n f g = ∫ t in (tk p n)..(tk p n + p.τ), f t * g t := rfl

/-- `ω ≤ 1` on the open slab: the weighted form is bounded by the unweighted one. -/
theorem Iw_le_It (h1 : ∀ t ∈ Set.Ioo (tk p n) (tk p n + p.τ), ω t ≤ 1) (f : Sm) :
    Iw p n ω hω hint f f ≤ It p n f f := by
  rw [Iw_apply, It_apply]
  refine integral_mono_on_of_le_Ioo (slab_le p n) (Iw_intble p n ω hint f f) (intble f f _ _)
    fun t ht => ?_
  have := mul_le_mul_of_nonneg_right (h1 t ht) (mul_self_nonneg (f t))
  linarith

/-- `ω = 1` on the open slab. -/
theorem Iw_eq_It (h1 : ∀ t ∈ Set.Ioo (tk p n) (tk p n + p.τ), ω t = 1) (f g : Sm) :
    Iw p n ω hω hint f g = It p n f g := by
  rw [Iw_apply, It_apply]
  refine integral_congr_Ioo_of_le (slab_le p n) fun t ht => ?_
  simp only [h1 t ht, one_mul]

/-- `ω = 0` on the open slab. -/
theorem Iw_eq_zero (h0 : ∀ t ∈ Set.Ioo (tk p n) (tk p n + p.τ), ω t = 0) (f g : Sm) :
    Iw p n ω hω hint f g = 0 := by
  rw [Iw_apply]
  have : (∫ t in (tk p n)..(tk p n + p.τ), ω t * (f t * g t))
      = ∫ _t in (tk p n)..(tk p n + p.τ), (0 : ℝ) :=
    integral_congr_Ioo_of_le (slab_le p n) fun t ht => by simp only [h0 t ht, zero_mul]
  rw [this]; simp

theorem Iw_symm (f g : Sm) :
    Iw p n ω hω hint (Mexp p.σ f) g = Iw p n ω hω hint f (Mexp p.σ g) := by
  rw [Iw_apply, Iw_apply]
  congr 1; ext t; simp only [Mexp_apply]; ring

theorem Iw_lo (f : Sm) :
    Real.exp (-p.σ * tk p (n + 1)) * Iw p n ω hω hint f f
      ≤ Iw p n ω hω hint f (Mexp p.σ f) := by
  rw [Iw_apply, Iw_apply, ← integral_const_mul]
  refine integral_mono_on (slab_le p n) ((Iw_intble p n ω hint f f).const_mul _)
    (Iw_intble p n ω hint f (Mexp p.σ f)) fun t ht => ?_
  simp only [Mexp_apply]
  have h1 : Real.exp (-p.σ * tk p (n + 1)) ≤ Real.exp (-p.σ * t) := by
    rw [tk_succ]
    exact Real.exp_le_exp.2 (by nlinarith [ht.2, p.σ_pos])
  have h2 := mul_nonneg (hω t) (mul_self_nonneg (f t))
  nlinarith

theorem Iw_hi (f : Sm) :
    Iw p n ω hω hint f (Mexp p.σ f)
      ≤ Real.exp (-p.σ * tk p n) * Iw p n ω hω hint f f := by
  rw [Iw_apply, Iw_apply, ← integral_const_mul]
  refine integral_mono_on (slab_le p n) (Iw_intble p n ω hint f (Mexp p.σ f))
    ((Iw_intble p n ω hint f f).const_mul _) fun t ht => ?_
  simp only [Mexp_apply]
  have h1 : Real.exp (-p.σ * t) ≤ Real.exp (-p.σ * tk p n) :=
    Real.exp_le_exp.2 (by nlinarith [ht.1, p.σ_pos])
  have h2 := mul_nonneg (hω t) (mul_self_nonneg (f t))
  nlinarith

theorem Iw_contr (f : Sm) :
    Iw p n ω hω hint (Mexp p.σ f) (Mexp p.σ f) ≤ Iw p n ω hω hint f f := by
  rw [Iw_apply, Iw_apply]
  refine integral_mono_on (slab_le p n) (Iw_intble p n ω hint _ _)
    (Iw_intble p n ω hint f f) fun t ht => ?_
  simp only [Mexp_apply]
  have h0 : 0 < Real.exp (-p.σ * t) := Real.exp_pos _
  have h1 : Real.exp (-p.σ * t) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.2 (by nlinarith [ht.1, p.σ_pos, tk_nonneg p n])
  have h2 : Real.exp (-p.σ * t) ^ 2 ≤ 1 := pow_le_one₀ h0.le h1
  have h3 := mul_nonneg (hω t) (mul_self_nonneg (f t))
  nlinarith

end Iw

/-! ### The cut element form -/

/-- `h ∫_a^b (x₀ + ξ x₁)(y₀ + ξ y₁) dξ` -/
noncomputable def qcf (h a b x0 x1 y0 y1 : ℝ) : ℝ :=
  h * ((b - a) * (x0 * y0) + (b ^ 2 - a ^ 2) / 2 * (x0 * y1 + x1 * y0)
    + (b ^ 3 - a ^ 3) / 3 * (x1 * y1))

/-- Simpson's rule: the closed form is a sum of squares. -/
theorem qcf_sos (h a b x0 x1 : ℝ) :
    qcf h a b x0 x1 x0 x1 = h * (b - a) / 6 * ((x0 + a * x1) ^ 2
      + 4 * (x0 + (a + b) / 2 * x1) ^ 2 + (x0 + b * x1) ^ 2) := by
  unfold qcf; ring

theorem qcf_nonneg {h a b : ℝ} (hh : 0 ≤ h) (hab : a ≤ b) (x0 x1 : ℝ) :
    0 ≤ qcf h a b x0 x1 x0 x1 := by
  rw [qcf_sos]
  have : 0 ≤ b - a := by linarith
  positivity

theorem qcf_le_full {h a b : ℝ} (hh : 0 ≤ h) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (x0 x1 : ℝ) : qcf h a b x0 x1 x0 x1 ≤ qcf h 0 1 x0 x1 x0 x1 := by
  have n1 := qcf_nonneg hh ha x0 x1
  have n2 := qcf_nonneg hh hb x0 x1
  unfold qcf at *
  linarith

section cut

variable (n : ℕ) (a b : ℝ → ℝ) (ha : Continuous a) (hb : Continuous b)
  (hab : ∀ t, a t ≤ b t)

include ha hb in
theorem qcf_cont (f0 f1 g0 g1 : Sm) :
    Continuous fun t => qcf p.h (a t) (b t) (f0 t) (f1 t) (g0 t) (g1 t) := by
  have := cont f0; have := cont f1; have := cont g0; have := cont g1
  unfold qcf
  fun_prop

/-- element-local form `∫_{I_n} h ∫_{a(t)}^{b(t)} f g dξ dt` -/
noncomputable def cutV : SemiIP V where
  B := LinearMap.mk₂ ℝ
    (fun f g => ∫ t in (tk p n)..(tk p n + p.τ),
      qcf p.h (a t) (b t) (f.1 t) (f.2 t) (g.1 t) (g.2 t))
    (fun f f' g => by
      rw [← integral_add ((qcf_cont p a b ha hb _ _ _ _).intervalIntegrable _ _)
        ((qcf_cont p a b ha hb _ _ _ _).intervalIntegrable _ _)]
      congr 1; ext t
      simp only [Prod.fst_add, Prod.snd_add, Sm.add_apply, qcf]; ring)
    (fun c f g => by
      simp only [smul_eq_mul]
      rw [← integral_const_mul]
      congr 1; ext t
      simp only [Prod.smul_fst, Prod.smul_snd, Sm.smul_apply, qcf]; ring)
    (fun f g g' => by
      rw [← integral_add ((qcf_cont p a b ha hb _ _ _ _).intervalIntegrable _ _)
        ((qcf_cont p a b ha hb _ _ _ _).intervalIntegrable _ _)]
      congr 1; ext t
      simp only [Prod.fst_add, Prod.snd_add, Sm.add_apply, qcf]; ring)
    (fun c f g => by
      simp only [smul_eq_mul]
      rw [← integral_const_mul]
      congr 1; ext t
      simp only [Prod.smul_fst, Prod.smul_snd, Sm.smul_apply, qcf]; ring)
  symm f g := by
    show (∫ t in (tk p n)..(tk p n + p.τ), qcf p.h (a t) (b t) (f.1 t) (f.2 t) (g.1 t) (g.2 t))
      = ∫ t in (tk p n)..(tk p n + p.τ), qcf p.h (a t) (b t) (g.1 t) (g.2 t) (f.1 t) (f.2 t)
    congr 1; ext t; unfold qcf; ring
  nonneg f := integral_nonneg (slab_le p n) fun t _ => qcf_nonneg p.h_pos.le (hab t) _ _

/-- the restriction to slab `n`, element `i` -/
def elL (n i : ℕ) : X →ₗ[ℝ] V where
  toFun u := u n i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `∫_{I_n} h ∫_{a(t)}^{b(t)} u v dξ dt` on element `i` -/
noncomputable def cutX (i : ℕ) : SemiIP X := (cutV p n a b ha hb hab).comap (elL n i)

theorem cutX_apply (i : ℕ) (u v : X) :
    cutX p n a b ha hb hab i u v = ∫ t in (tk p n)..(tk p n + p.τ),
      qcf p.h (a t) (b t) ((u n i).1 t) ((u n i).2 t) ((v n i).1 t) ((v n i).2 t) := rfl

end cut

/-- For constant cut positions, the integral in time reduces to `L²(I_n)` forms of the
coefficients. -/
theorem int_qcf_const (n : ℕ) (a b : ℝ) (f0 f1 g0 g1 : Sm) :
    ∫ t in (tk p n)..(tk p n + p.τ), qcf p.h a b (f0 t) (f1 t) (g0 t) (g1 t)
      = p.h * ((b - a) * It p n f0 g0 + (b ^ 2 - a ^ 2) / 2 * (It p n f0 g1 + It p n f1 g0)
        + (b ^ 3 - a ^ 3) / 3 * It p n f1 g1) := by
  have h00 := intble f0 g0 (tk p n) (tk p n + p.τ)
  have h01 := intble f0 g1 (tk p n) (tk p n + p.τ)
  have h10 := intble f1 g0 (tk p n) (tk p n + p.τ)
  have h11 := intble f1 g1 (tk p n) (tk p n + p.τ)
  unfold qcf
  rw [integral_const_mul, integral_add ((h00.const_mul _).add ((h01.add h10).const_mul _))
    (h11.const_mul _), integral_add (h00.const_mul _) ((h01.add h10).const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_add h01 h10]
  rfl

/-- the form on a full element as an integral in time -/
theorem full_eq_int (n i : ℕ) (u v : X) :
    full p n i u v = ∫ t in (tk p n)..(tk p n + p.τ),
      qcf p.h 0 1 ((u n i).1 t) ((u n i).2 t) ((v n i).1 t) ((v n i).2 t) := by
  rw [int_qcf_const]
  unfold full elem
  rw [simpson_closed]
  rfl

end StDgdg.Move1d
