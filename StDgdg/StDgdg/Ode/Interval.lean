import StDgdg.Basic

/-!
# Validation example `d = 0` (ODE), part 1: analysis on one time interval

Smooth functions on `ℝ`, the `L²(a,b)` form, integration by parts, the continuous trace
inequality, and the computations for affine functions (`P¹` in time).
Everything here is proven from Mathlib; there are no assumptions.
-/

namespace StDgdg.Ode

open scoped ContDiff
open intervalIntegral

/-- Smooth functions `ℝ → ℝ`. -/
def Sm : Submodule ℝ (ℝ → ℝ) where
  carrier := {f | ContDiff ℝ ∞ f}
  add_mem' := by
    intro f g hf hg
    have h : ContDiff ℝ ∞ (fun t => f t + g t) :=
      ContDiff.add (show ContDiff ℝ ∞ f from hf) (show ContDiff ℝ ∞ g from hg)
    exact h
  zero_mem' := by
    have h : ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℝ)) := contDiff_const
    exact h
  smul_mem' := fun c f hf => by
    have h : ContDiff ℝ ∞ (fun t => c * f t) := contDiff_const.mul (show ContDiff ℝ ∞ f from hf)
    exact h

instance : CoeFun Sm (fun _ => ℝ → ℝ) := ⟨fun f => f.1⟩

theorem cd (f : Sm) : ContDiff ℝ ∞ (f : ℝ → ℝ) := f.2
theorem cont (f : Sm) : Continuous (f : ℝ → ℝ) := (cd f).continuous
theorem diff (f : Sm) : Differentiable ℝ (f : ℝ → ℝ) := (cd f).differentiable (by simp)

/-- Constructor from a smooth function. -/
def mk (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) : Sm := ⟨f, hf⟩

@[simp] theorem Sm.add_apply (f g : Sm) (t : ℝ) : (f + g) t = f t + g t := rfl
@[simp] theorem Sm.sub_apply (f g : Sm) (t : ℝ) : (f - g) t = f t - g t := rfl
@[simp] theorem Sm.smul_apply (c : ℝ) (f : Sm) (t : ℝ) : (c • f) t = c * f t := rfl
@[simp] theorem Sm.zero_apply (t : ℝ) : (0 : Sm) t = 0 := rfl
@[simp] theorem mk_apply (f : ℝ → ℝ) (hf) (t : ℝ) : mk f hf t = f t := rfl

@[ext] theorem Sm.ext {f g : Sm} (h : ∀ t, f t = g t) : f = g := Subtype.ext (funext h)

/-- The derivative. -/
noncomputable def D : Sm →ₗ[ℝ] Sm where
  toFun f := mk (deriv f) (contDiff_infty_iff_deriv.1 (cd f)).2
  map_add' f g := by
    ext t; exact deriv_add (diff f t) (diff g t)
  map_smul' c f := by
    ext t; exact deriv_const_smul c (diff f t)

theorem D_apply (f : Sm) (t : ℝ) : D f t = deriv f t := rfl

theorem hasDerivAt (f : Sm) (t : ℝ) : HasDerivAt f (D f t) t :=
  (diff f t).hasDerivAt

/-- Point evaluation. -/
def ev (t : ℝ) : Sm →ₗ[ℝ] ℝ where
  toFun f := f t
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem ev_apply (t : ℝ) (f : Sm) : ev t f = f t := rfl

/-- Multiplication by `e^{-σ t}`. -/
noncomputable def Mexp (σ : ℝ) : Sm →ₗ[ℝ] Sm where
  toFun f := mk (fun t => Real.exp (-σ * t) * f t)
    ((Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).mul (cd f))
  map_add' f g := by ext t; simp [mul_add]
  map_smul' c f := by ext t; simp; ring

@[simp] theorem Mexp_apply (σ : ℝ) (f : Sm) (t : ℝ) : Mexp σ f t = Real.exp (-σ * t) * f t := rfl

/-- Product rule: `(e^{-σt} f)' = e^{-σt} f' - σ e^{-σt} f`. -/
theorem D_Mexp (σ : ℝ) (f : Sm) : D (Mexp σ f) = Mexp σ (D f) - σ • Mexp σ f := by
  ext t
  have h1 : HasDerivAt (fun t : ℝ => Real.exp (-σ * t)) (Real.exp (-σ * t) * (-σ)) t := by
    have := (hasDerivAt_id t).const_mul (-σ)
    simpa using this.exp
  have h2 := h1.mul (hasDerivAt f t)
  have h3 : D (Mexp σ f) t = _ := h2.deriv
  rw [h3]
  simp
  ring

/-- The affine function `t ↦ c + d t`. -/
def aff (c d : ℝ) : Sm := mk (fun t => c + d * t) (contDiff_const.add (contDiff_const.mul contDiff_id))

@[simp] theorem aff_apply (c d t : ℝ) : aff c d t = c + d * t := rfl

theorem D_aff (c d : ℝ) : D (aff c d) = aff d 0 := by
  ext t
  have : HasDerivAt (fun t : ℝ => c + d * t) d t := by
    simpa using ((hasDerivAt_id t).const_mul d).const_add c
  have h : D (aff c d) t = d := this.deriv
  simp [h]

/-- Affine functions (`P¹`). -/
def P1 : Submodule ℝ Sm where
  carrier := {f | ∃ c d, f = aff c d}
  add_mem' := by
    rintro _ _ ⟨c, d, rfl⟩ ⟨c', d', rfl⟩
    exact ⟨c + c', d + d', by ext t; simp; ring⟩
  zero_mem' := ⟨0, 0, by ext t; simp⟩
  smul_mem' := by
    rintro k _ ⟨c, d, rfl⟩
    exact ⟨k * c, k * d, by ext t; simp; ring⟩

theorem aff_mem (c d : ℝ) : aff c d ∈ P1 := ⟨c, d, rfl⟩

theorem D_mem_P1 {f : Sm} (hf : f ∈ P1) : D f ∈ P1 := by
  obtain ⟨c, d, rfl⟩ := hf
  rw [D_aff]; exact aff_mem _ _

/-! ### The `L²(a,b)` form -/

theorem intble (f g : Sm) (a b : ℝ) :
    IntervalIntegrable (fun t => f t * g t) MeasureTheory.volume a b :=
  ((cont f).mul (cont g)).intervalIntegrable _ _

/-- `(f, g)_{L²(a,b)}` for `a ≤ b`. -/
noncomputable def ip (a b : ℝ) (hab : a ≤ b) : SemiIP Sm where
  B := LinearMap.mk₂ ℝ (fun f g => ∫ t in a..b, f t * g t)
    (fun f f' g => by
      simp only [Sm.add_apply, add_mul]
      exact integral_add (intble f g a b) (intble f' g a b))
    (fun c f g => by
      simp only [Sm.smul_apply, mul_assoc, smul_eq_mul]
      exact integral_const_mul _ _)
    (fun f g g' => by
      simp only [Sm.add_apply, mul_add]
      exact integral_add (intble f g a b) (intble f g' a b))
    (fun c f g => by
      simp only [Sm.smul_apply, smul_eq_mul]
      rw [← integral_const_mul]
      congr 1; ext t; ring)
  symm f g := by
    show (∫ t in a..b, f t * g t) = ∫ t in a..b, g t * f t
    congr 1; ext t; ring
  nonneg f := integral_nonneg hab fun t _ => mul_self_nonneg _

variable {a b : ℝ} (hab : a ≤ b)

theorem ip_apply (f g : Sm) : ip a b hab f g = ∫ t in a..b, f t * g t := rfl

/-- Monotonicity of the integral, in the form needed below. -/
theorem ip_mono {f g f' g' : Sm} (h : ∀ t ∈ Set.Icc a b, f t * g t ≤ f' t * g' t) :
    ip a b hab f g ≤ ip a b hab f' g' :=
  integral_mono_on hab (intble f g a b) (intble f' g' a b) h

/-- **Integration by parts.** -/
theorem ip_D (f g : Sm) :
    ip a b hab (D f) g = -ip a b hab f (D g) + f b * g b - f a * g a := by
  have h := integral_mul_deriv_eq_deriv_mul (a := a) (b := b)
    (fun x _ => hasDerivAt f x) (fun x _ => hasDerivAt g x)
    ((cont (D f)).intervalIntegrable _ _) ((cont (D g)).intervalIntegrable _ _)
  simp only [ip_apply]
  linarith

/-- Continuous trace inequality at the left end point:
`(b-a) f(a)² ≤ 2 ‖f‖² + (b-a)² ‖f'‖²`. -/
theorem trace_left (f : Sm) :
    (b - a) * f a ^ 2 ≤ 2 * ip a b hab f f + (b - a) ^ 2 * ip a b hab (D f) (D f) := by
  -- integrate the derivative of `(t - b) f(t)²`
  have h1 := ip_D hab (aff (-b) 1) (mk (fun t => f t * f t) ((cd f).mul (cd f)))
  have hD : D (mk (fun t => f t * f t) ((cd f).mul (cd f)))
      = (2 : ℝ) • mk (fun t => f t * D f t) ((cd f).mul (cd (D f))) := by
    ext t
    have h : HasDerivAt (fun t => f t * f t) (D f t * f t + f t * D f t) t :=
      (hasDerivAt f t).mul (hasDerivAt f t)
    show deriv (fun t => f t * f t) t = 2 * (f t * D f t)
    rw [h.deriv]; ring
  rw [D_aff, hD] at h1
  simp only [ip_apply, aff_apply, mk_apply, Sm.smul_apply, add_zero, zero_mul, one_mul] at h1
  have key : (∫ t in a..b, ((-b + t) * (2 * (f t * D f t))))
      ≤ ∫ t in a..b, (f t * f t + (b - a) ^ 2 * (D f t * D f t)) := by
    apply integral_mono_on hab
    · exact Continuous.intervalIntegrable (by have := cont f; have := cont (D f); fun_prop) _ _
    · exact Continuous.intervalIntegrable (by have := cont f; have := cont (D f); fun_prop) _ _
    · intro t ht
      have h0 : 0 ≤ b - t := by linarith [ht.2]
      have h2 : (b - t) ^ 2 ≤ (b - a) ^ 2 := by
        apply pow_le_pow_left₀ h0; linarith [ht.1]
      have h3 := mul_le_mul_of_nonneg_right h2 (mul_self_nonneg (D f t))
      nlinarith [sq_nonneg (f t - (t - b) * D f t)]
  have e2 : (∫ t in a..b, (f t * f t + (b - a) ^ 2 * (D f t * D f t)))
      = (∫ t in a..b, f t * f t) + (b - a) ^ 2 * ∫ t in a..b, D f t * D f t := by
    rw [integral_add (intble f f a b) ((intble (D f) (D f) a b).const_mul _), integral_const_mul]
  rw [e2] at key
  have e4 : (b - a) * f a ^ 2 = (∫ t in a..b, f t * f t)
      + ∫ t in a..b, ((-b + t) * (2 * (f t * D f t))) := by
    linear_combination (-1 : ℝ) * h1
  simp only [ip_apply]
  linarith

/-- Continuous trace inequality at the right end point. -/
theorem trace_right (f : Sm) :
    (b - a) * f b ^ 2 ≤ 2 * ip a b hab f f + (b - a) ^ 2 * ip a b hab (D f) (D f) := by
  -- integrate the derivative of `(t - a) f(t)²`
  have h1 := ip_D hab (aff (-a) 1) (mk (fun t => f t * f t) ((cd f).mul (cd f)))
  have hD : D (mk (fun t => f t * f t) ((cd f).mul (cd f)))
      = (2 : ℝ) • mk (fun t => f t * D f t) ((cd f).mul (cd (D f))) := by
    ext t
    have h : HasDerivAt (fun t => f t * f t) (D f t * f t + f t * D f t) t :=
      (hasDerivAt f t).mul (hasDerivAt f t)
    show deriv (fun t => f t * f t) t = 2 * (f t * D f t)
    rw [h.deriv]; ring
  rw [D_aff, hD] at h1
  simp only [ip_apply, aff_apply, mk_apply, Sm.smul_apply, add_zero, zero_mul, one_mul] at h1
  have key : (∫ t in a..b, ((-a + t) * (2 * (f t * D f t))))
      ≤ ∫ t in a..b, (f t * f t + (b - a) ^ 2 * (D f t * D f t)) := by
    apply integral_mono_on hab
    · exact Continuous.intervalIntegrable (by have := cont f; have := cont (D f); fun_prop) _ _
    · exact Continuous.intervalIntegrable (by have := cont f; have := cont (D f); fun_prop) _ _
    · intro t ht
      have h0 : 0 ≤ t - a := by linarith [ht.1]
      have h2 : (t - a) ^ 2 ≤ (b - a) ^ 2 := by
        apply pow_le_pow_left₀ h0; linarith [ht.2]
      have h3 := mul_le_mul_of_nonneg_right h2 (mul_self_nonneg (D f t))
      nlinarith [sq_nonneg (f t - (t - a) * D f t)]
  have e2 : (∫ t in a..b, (f t * f t + (b - a) ^ 2 * (D f t * D f t)))
      = (∫ t in a..b, f t * f t) + (b - a) ^ 2 * ∫ t in a..b, D f t * D f t := by
    rw [integral_add (intble f f a b) ((intble (D f) (D f) a b).const_mul _), integral_const_mul]
  rw [e2] at key
  have e4 : (b - a) * f b ^ 2 = (∫ t in a..b, f t * f t)
      + ∫ t in a..b, ((-a + t) * (2 * (f t * D f t))) := by
    linear_combination (-1 : ℝ) * h1
  simp only [ip_apply]
  linarith

/-! ### Affine functions on `[a, a + τ]` -/

/-- `‖p + d (t - a)‖²_{L²(a, a+τ)} = τ p² + p d τ² + d² τ³ / 3`. -/
theorem int_aff_sq (a τ p d : ℝ) :
    ∫ t in a..(a + τ), (p + d * (t - a)) * (p + d * (t - a))
      = τ * p ^ 2 + p * d * τ ^ 2 + d ^ 2 * τ ^ 3 / 3 := by
  have h := integral_comp_sub_right (a := a) (b := a + τ) (fun s => (p + d * s) * (p + d * s)) a
  simp only [sub_self, add_sub_cancel_left] at h
  rw [h]
  have e : ∀ s : ℝ, (p + d * s) * (p + d * s) = p ^ 2 + 2 * p * d * s + d ^ 2 * s ^ 2 :=
    fun s => by ring
  simp_rw [e]
  rw [integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    integral_const_mul, integral_const_mul, integral_pow, integral_id, integral_const]
  simp
  ring

/-- Every affine function in local coordinates of `[a, a+τ]`. -/
theorem aff_local (c d a : ℝ) (t : ℝ) : aff c d t = (c + d * a) + d * (t - a) := by
  simp; ring

variable {τ : ℝ} (hτ : 0 < τ)

theorem ip_aff (a c d : ℝ) :
    ip a (a + τ) (by linarith) (aff c d) (aff c d)
      = τ * (c + d * a) ^ 2 + (c + d * a) * d * τ ^ 2 + d ^ 2 * τ ^ 3 / 3 := by
  rw [ip_apply, ← int_aff_sq]
  congr 1; ext t; rw [aff_local c d a]

include hτ in
/-- Discrete trace inequality in time for `P¹`. -/
theorem trace_P1 (a : ℝ) {f : Sm} (hf : f ∈ P1) :
    f a ^ 2 + f (a + τ) ^ 2 ≤ 6 * τ⁻¹ * ip a (a + τ) (by linarith) f f := by
  obtain ⟨c, d, rfl⟩ := hf
  rw [ip_aff hτ]
  have e : 6 * τ⁻¹ * (τ * (c + d * a) ^ 2 + (c + d * a) * d * τ ^ 2 + d ^ 2 * τ ^ 3 / 3)
      = 6 * ((c + d * a) ^ 2 + (c + d * a) * (d * τ) + (d * τ) ^ 2 / 3) := by
    field_simp
  rw [e]
  simp only [aff_apply]
  nlinarith [sq_nonneg (2 * (c + d * a) + d * τ)]

include hτ in
/-- Inverse inequality in time for `P¹`. -/
theorem inv_P1 (a : ℝ) {f : Sm} (hf : f ∈ P1) :
    ip a (a + τ) (by linarith) (D f) (D f) ≤ 12 * τ⁻¹ ^ 2 * ip a (a + τ) (by linarith) f f := by
  obtain ⟨c, d, rfl⟩ := hf
  rw [D_aff, ip_aff hτ, ip_aff hτ]
  have e : 12 * τ⁻¹ ^ 2 * (τ * (c + d * a) ^ 2 + (c + d * a) * d * τ ^ 2 + d ^ 2 * τ ^ 3 / 3)
      = 12 * τ⁻¹ * ((c + d * a) ^ 2 + (c + d * a) * (d * τ) + (d * τ) ^ 2 / 3) := by
    field_simp
  rw [e]
  have hi : 0 < τ⁻¹ := inv_pos.2 hτ
  have h1 : (d * τ) ^ 2 ≤ 12 * ((c + d * a) ^ 2 + (c + d * a) * (d * τ) + (d * τ) ^ 2 / 3) := by
    nlinarith [sq_nonneg (2 * (c + d * a) + d * τ)]
  have h2 := mul_le_mul_of_nonneg_left h1 hi.le
  have e2 : τ⁻¹ * (d * τ) ^ 2 = τ * (d + 0 * a) ^ 2 + (d + 0 * a) * 0 * τ ^ 2 + 0 ^ 2 * τ ^ 3 / 3 := by
    field_simp; ring
  rw [← e2]
  linarith

/-! ### The exponential weight on `[a, b]` -/

/-- `(e^{-σt} f, g) = (f, e^{-σt} g)`. -/
theorem ip_Mexp_symm (σ : ℝ) (f g : Sm) :
    ip a b hab (Mexp σ f) g = ip a b hab f (Mexp σ g) := by
  simp only [ip_apply, Mexp_apply]
  congr 1; ext t; ring

/-- `m ‖f‖² ≤ (f, e^{-σt} f)` if `m ≤ e^{-σ b}`. -/
theorem ip_Mexp_lo {σ : ℝ} (hσ : 0 ≤ σ) {m : ℝ} (hm : m ≤ Real.exp (-σ * b)) (f : Sm) :
    m * ip a b hab f f ≤ ip a b hab f (Mexp σ f) := by
  have h : ip a b hab (m • f) f ≤ ip a b hab f (Mexp σ f) := by
    apply ip_mono
    intro t ht
    simp only [Sm.smul_apply, Mexp_apply]
    have h1 : Real.exp (-σ * b) ≤ Real.exp (-σ * t) :=
      Real.exp_le_exp.2 (by nlinarith [ht.2])
    nlinarith [mul_self_nonneg (f t)]
  simpa using h

/-- `(f, e^{-σt} f) ≤ e^{-σ a} ‖f‖²`. -/
theorem ip_Mexp_hi {σ : ℝ} (hσ : 0 ≤ σ) (f : Sm) :
    ip a b hab f (Mexp σ f) ≤ Real.exp (-σ * a) * ip a b hab f f := by
  have h : ip a b hab f (Mexp σ f) ≤ ip a b hab (Real.exp (-σ * a) • f) f := by
    apply ip_mono
    intro t ht
    simp only [Sm.smul_apply, Mexp_apply]
    have h1 : Real.exp (-σ * t) ≤ Real.exp (-σ * a) :=
      Real.exp_le_exp.2 (by nlinarith [ht.1])
    nlinarith [mul_self_nonneg (f t)]
  simpa using h

/-- `‖e^{-σt} f‖² ≤ ‖f‖²` if `a ≥ 0`. -/
theorem ip_Mexp_contr {σ : ℝ} (hσ : 0 ≤ σ) (ha : 0 ≤ a) (f : Sm) :
    ip a b hab (Mexp σ f) (Mexp σ f) ≤ ip a b hab f f := by
  apply ip_mono
  intro t ht
  simp only [Mexp_apply]
  have h0 : 0 < Real.exp (-σ * t) := Real.exp_pos _
  have h1 : Real.exp (-σ * t) ≤ 1 := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.2 (by nlinarith [ht.1])
  have h2 : Real.exp (-σ * t) ^ 2 ≤ 1 := pow_le_one₀ h0.le h1
  nlinarith [mul_self_nonneg (f t)]

/-- `‖(e^{-σt} - e^{-σa}) f‖² ≤ σ² (b-a)² ‖f‖²` if `a ≥ 0`: the key to superapproximation. -/
theorem ip_Mexp_sub {σ : ℝ} (hσ : 0 ≤ σ) (ha : 0 ≤ a) (f : Sm) :
    ip a b hab (Mexp σ f - Real.exp (-σ * a) • f) (Mexp σ f - Real.exp (-σ * a) • f)
      ≤ σ ^ 2 * (b - a) ^ 2 * ip a b hab f f := by
  have h : ip a b hab (Mexp σ f - Real.exp (-σ * a) • f) (Mexp σ f - Real.exp (-σ * a) • f)
      ≤ ip a b hab ((σ ^ 2 * (b - a) ^ 2) • f) f := by
    apply ip_mono
    intro t ht
    simp only [Sm.sub_apply, Sm.smul_apply, Mexp_apply]
    -- `0 ≤ e^{-σa} - e^{-σt} ≤ σ (t - a)`
    have h1 : Real.exp (-σ * t) ≤ Real.exp (-σ * a) :=
      Real.exp_le_exp.2 (by nlinarith [ht.1])
    have h2 : Real.exp (-σ * a) ≤ 1 := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.2 (by nlinarith)
    have h3 : 1 - σ * (t - a) ≤ Real.exp (-(σ * (t - a))) := by
      have := Real.add_one_le_exp (-(σ * (t - a))); linarith
    have h4 : Real.exp (-σ * t) = Real.exp (-σ * a) * Real.exp (-(σ * (t - a))) := by
      rw [← Real.exp_add]; congr 1; ring
    have h5 : 0 < Real.exp (-σ * a) := Real.exp_pos _
    have h6 : 0 ≤ σ * (t - a) := mul_nonneg hσ (by linarith [ht.1])
    have h7 : Real.exp (-σ * a) - Real.exp (-σ * t) ≤ σ * (t - a) := by
      rw [h4]; nlinarith
    have h8 : σ * (t - a) ≤ σ * (b - a) := mul_le_mul_of_nonneg_left (by linarith [ht.2]) hσ
    have h9 : (Real.exp (-σ * a) - Real.exp (-σ * t)) ^ 2 ≤ (σ * (b - a)) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have := mul_le_mul_of_nonneg_right h9 (mul_self_nonneg (f t))
    nlinarith
  simpa using h

/-! ### The `L²` projection onto `P¹` on `[a, a+τ]` and superapproximation -/

section proj

variable (a : ℝ)

/-- `L²(a, a+τ)` -/
noncomputable abbrev Iv : SemiIP Sm := ip a (a + τ) (le_of_lt (lt_add_of_pos_right a hτ))

/-- The constant function `1`. -/
def e0 : Sm := aff 1 0
/-- `t - (a + τ/2)`. -/
noncomputable def e1 (a τ : ℝ) : Sm := aff (-(a + τ / 2)) 1

theorem ip_e0 : Iv hτ a e0 e0 = τ := by
  rw [e0, ip_aff hτ]; ring

theorem ip_e1 : Iv hτ a (e1 a τ) (e1 a τ) = τ ^ 3 / 12 := by
  rw [e1, ip_aff hτ]; ring

theorem ip_e01 : Iv hτ a e0 (e1 a τ) = 0 := by
  have h : e0 + e1 a τ = aff (1 - (a + τ / 2)) 1 := by ext t; simp [e0, e1]; ring
  have h2 := ip_aff hτ a (1 - (a + τ / 2)) 1
  rw [← h] at h2
  simp only [map_add, LinearMap.add_apply] at h2
  rw [(ip a (a + τ) _).symm (e1 a τ) e0] at h2
  have h3 := ip_e0 hτ a
  have h4 := ip_e1 hτ a
  linear_combination (1 / 2 : ℝ) * h2 - (1 / 2 : ℝ) * h3 - (1 / 2 : ℝ) * h4

theorem ip_e0_pos : 0 < Iv hτ a e0 e0 := by rw [ip_e0]; exact hτ
theorem ip_e1_pos : 0 < Iv hτ a (e1 a τ) (e1 a τ) := by rw [ip_e1]; positivity

theorem P1_span {f : Sm} (hf : f ∈ P1) : ∃ x y : ℝ, f = x • e0 + y • e1 a τ := by
  obtain ⟨c, d, rfl⟩ := hf
  exact ⟨c + d * (a + τ / 2), d, by ext t; simp [e0, e1]; ring⟩

theorem span_mem (x y : ℝ) : x • e0 + y • e1 a τ ∈ P1 :=
  P1.add_mem (P1.smul_mem _ (aff_mem _ _)) (P1.smul_mem _ (aff_mem _ _))

/-- The `L²(a,a+τ)` projection onto `P¹`. -/
noncomputable def Pi : Sm →ₗ[ℝ] Sm := (Iv hτ a).proj2 e0 (e1 a τ)

theorem Pi_mem (f : Sm) : Pi hτ a f ∈ P1 := span_mem a _ _

theorem Pi_fix {f : Sm} (hf : f ∈ P1) : Pi hτ a f = f := by
  obtain ⟨x, y, rfl⟩ := P1_span (τ := τ) a hf
  exact (Iv hτ a).proj2_fix (ip_e01 hτ a) (ip_e0_pos hτ a) (ip_e1_pos hτ a) x y

theorem Pi_best (f : Sm) {g : Sm} (hg : g ∈ P1) :
    Iv hτ a (Pi hτ a f - f) (Pi hτ a f - f) ≤ Iv hτ a (f - g) (f - g) := by
  obtain ⟨x, y, rfl⟩ := P1_span (τ := τ) a hg
  have h := (Iv hτ a).proj2_best (ip_e01 hτ a) (ip_e0_pos hτ a) (ip_e1_pos hτ a) f x y
  have e : f - (x • e0 + y • e1 a τ) = -(x • e0 + y • e1 a τ - f) := by abel
  rw [e, SemiIP.neg_sq]
  exact h

theorem Pi_stab (f : Sm) : Iv hτ a (Pi hτ a f) (Pi hτ a f) ≤ Iv hτ a f f :=
  (Iv hτ a).proj2_stab (ip_e01 hτ a) (ip_e0_pos hτ a) (ip_e1_pos hτ a) f

variable {σ : ℝ} (hσ : 0 ≤ σ) (ha : 0 ≤ a)

include hσ ha in
/-- **Superapproximation** (`eq_superapprox` for `d = 0`):
`‖(Π - Id)(e^{-σt} f)‖ ≤ σ τ ‖f‖` for `f ∈ P¹`. -/
theorem superapprox_iv {f : Sm} (hf : f ∈ P1) :
    Iv hτ a (Pi hτ a (Mexp σ f) - Mexp σ f) (Pi hτ a (Mexp σ f) - Mexp σ f)
      ≤ σ ^ 2 * τ ^ 2 * Iv hτ a f f := by
  have h1 := Pi_best hτ a (Mexp σ f) (P1.smul_mem (Real.exp (-σ * a)) hf)
  have h2 := ip_Mexp_sub (le_of_lt (lt_add_of_pos_right a hτ)) hσ ha f
  rw [add_sub_cancel_left] at h2
  exact h1.trans h2

include hσ ha in
/-- **Superapproximation for the time derivative** (`eq_superapprox_dt` for `d = 0`):
`‖∂_t (Π - Id)(e^{-σt} f)‖² ≤ 76 σ² ‖f‖²` for `f ∈ P¹`. -/
theorem superapprox_dt_iv {f : Sm} (hf : f ∈ P1) :
    Iv hτ a (D (Pi hτ a (Mexp σ f) - Mexp σ f)) (D (Pi hτ a (Mexp σ f) - Mexp σ f))
      ≤ 76 * σ ^ 2 * Iv hτ a f f := by
  have hτi : 0 < τ⁻¹ := inv_pos.2 hτ
  set c : ℝ := Real.exp (-σ * a) with hc
  set h : Sm := Mexp σ f - c • f with hh
  have hcf : c • f ∈ P1 := P1.smul_mem c hf
  -- `Π(φ f) - φ f = Π h - h`
  have e1 : Pi hτ a (Mexp σ f) - Mexp σ f = Pi hτ a h - h := by
    rw [hh, map_sub, Pi_fix hτ a hcf]; abel
  -- `h' = (φ - φ(a)) f' - σ φ f`
  have e2 : D h = (Mexp σ (D f) - c • D f) - σ • Mexp σ f := by
    rw [hh, map_sub, D_Mexp, map_smul]; abel
  have hff := (Iv hτ a).nonneg f
  -- bounds
  have b1 : Iv hτ a h h ≤ σ ^ 2 * τ ^ 2 * Iv hτ a f f := by
    have := ip_Mexp_sub (le_of_lt (lt_add_of_pos_right a hτ)) hσ ha f
    rwa [add_sub_cancel_left] at this
  have b2 : Iv hτ a (D (Pi hτ a h)) (D (Pi hτ a h)) ≤ 12 * σ ^ 2 * Iv hτ a f f := by
    have i1 := inv_P1 hτ a (Pi_mem hτ a h)
    have i2 := Pi_stab hτ a h
    have i3 : 12 * τ⁻¹ ^ 2 * Iv hτ a (Pi hτ a h) (Pi hτ a h)
        ≤ 12 * τ⁻¹ ^ 2 * (σ ^ 2 * τ ^ 2 * Iv hτ a f f) :=
      mul_le_mul_of_nonneg_left (i2.trans b1) (by positivity)
    have i4 : 12 * τ⁻¹ ^ 2 * (σ ^ 2 * τ ^ 2 * Iv hτ a f f) = 12 * σ ^ 2 * Iv hτ a f f := by
      field_simp
    linarith
  have b3 : Iv hτ a (D f) (D f) ≤ 12 * τ⁻¹ ^ 2 * Iv hτ a f f := inv_P1 hτ a hf
  have b4 : Iv hτ a (Mexp σ (D f) - c • D f) (Mexp σ (D f) - c • D f)
      ≤ 12 * σ ^ 2 * Iv hτ a f f := by
    have := ip_Mexp_sub (le_of_lt (lt_add_of_pos_right a hτ)) hσ ha (D f)
    rw [add_sub_cancel_left] at this
    have i3 : σ ^ 2 * τ ^ 2 * Iv hτ a (D f) (D f)
        ≤ σ ^ 2 * τ ^ 2 * (12 * τ⁻¹ ^ 2 * Iv hτ a f f) :=
      mul_le_mul_of_nonneg_left b3 (by positivity)
    have i4 : σ ^ 2 * τ ^ 2 * (12 * τ⁻¹ ^ 2 * Iv hτ a f f) = 12 * σ ^ 2 * Iv hτ a f f := by
      field_simp
    linarith
  have b5 : Iv hτ a (σ • Mexp σ f) (σ • Mexp σ f) ≤ σ ^ 2 * Iv hτ a f f := by
    rw [SemiIP.smul_sq]
    exact mul_le_mul_of_nonneg_left
      (ip_Mexp_contr (le_of_lt (lt_add_of_pos_right a hτ)) hσ ha f) (sq_nonneg σ)
  have b6 : Iv hτ a (D h) (D h) ≤ 26 * σ ^ 2 * Iv hτ a f f := by
    rw [e2]
    have := (Iv hτ a).sub_sq_le (Mexp σ (D f) - c • D f) (σ • Mexp σ f)
    linarith
  rw [e1, map_sub]
  have := (Iv hτ a).sub_sq_le (D (Pi hτ a h)) (D h)
  linarith

end proj

end StDgdg.Ode
