import StDgdg.Basic

/-!
# Validation example `d = 1`, part 1: exact integration of `P¹` functions on an element

A function which is affine in the local coordinate `ξ ∈ [0,1]` of an element is given by two
coefficients `c0 u + ξ c1 u` (with values in a space `Z` carrying a form `I`, e.g. functions
of time with the `L²` form in time, or real numbers). The integral of the product of two
such functions over `ξ ∈ [a, b]`, times the element size `h`, is evaluated exactly by
Simpson's rule, which exhibits it as a non-negative combination of point evaluations.
-/

namespace StDgdg

namespace SemiIP

variable {Y Z : Type*} [AddCommGroup Y] [Module ℝ Y] [AddCommGroup Z] [Module ℝ Z]
  (I : SemiIP Z) (c0 c1 : Y →ₗ[ℝ] Z)

/-- Evaluation at the local coordinate `ξ`: `u ↦ c0 u + ξ c1 u`. -/
def ptL (ξ : ℝ) : Y →ₗ[ℝ] Z := c0 + ξ • c1

theorem ptL_apply (ξ : ℝ) (u : Y) : ptL c0 c1 ξ u = c0 u + ξ • c1 u := rfl

/-- `h ∫_a^b (u(ξ), v(ξ))_I dξ`, evaluated by Simpson's rule. -/
noncomputable def simpson (h : ℝ) (hh : 0 ≤ h) (a b : ℝ) (hab : a ≤ b) : SemiIP Y where
  B := (h * (b - a) / 6) • ((I.comap (ptL c0 c1 a)).B
    + (4 : ℝ) • (I.comap (ptL c0 c1 ((a + b) / 2))).B + (I.comap (ptL c0 c1 b)).B)
  symm u v := by
    simp only [LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]
    rw [(I.comap (ptL c0 c1 a)).symm u v, (I.comap (ptL c0 c1 ((a + b) / 2))).symm u v,
      (I.comap (ptL c0 c1 b)).symm u v]
  nonneg u := by
    simp only [LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]
    have h1 := (I.comap (ptL c0 c1 a)).nonneg u
    have h2 := (I.comap (ptL c0 c1 ((a + b) / 2))).nonneg u
    have h3 := (I.comap (ptL c0 c1 b)).nonneg u
    have : 0 ≤ h * (b - a) / 6 := by
      have : 0 ≤ b - a := by linarith
      positivity
    positivity

variable {h : ℝ} (hh : 0 ≤ h) {a b : ℝ} (hab : a ≤ b)

theorem simpson_apply (u v : Y) :
    simpson I c0 c1 h hh a b hab u v = h * (b - a) / 6 *
      (I (ptL c0 c1 a u) (ptL c0 c1 a v)
        + 4 * I (ptL c0 c1 ((a + b) / 2) u) (ptL c0 c1 ((a + b) / 2) v)
        + I (ptL c0 c1 b u) (ptL c0 c1 b v)) := rfl

/-- Simpson's rule is exact: the closed form of `h ∫_a^b (c0 u + ξ c1 u, c0 v + ξ c1 v) dξ`. -/
theorem simpson_closed (u v : Y) :
    simpson I c0 c1 h hh a b hab u v = h * ((b - a) * I (c0 u) (c0 v)
      + (b ^ 2 - a ^ 2) / 2 * (I (c0 u) (c1 v) + I (c1 u) (c0 v))
      + (b ^ 3 - a ^ 3) / 3 * I (c1 u) (c1 v)) := by
  rw [simpson_apply]
  simp only [ptL_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul]
  ring

/-- Additivity in the domain of integration. -/
theorem simpson_split {m : ℝ} (ham : a ≤ m) (hmb : m ≤ b) (u v : Y) :
    simpson I c0 c1 h hh a b (ham.trans hmb) u v
      = simpson I c0 c1 h hh a m ham u v + simpson I c0 c1 h hh m b hmb u v := by
  simp only [simpson_closed]; ring

/-- Monotonicity in the domain of integration: `∫_a^b ≤ ∫_0^1` for `0 ≤ a ≤ b ≤ 1`. -/
theorem simpson_le_full (ha : 0 ≤ a) (hb : b ≤ 1) (u : Y) :
    simpson I c0 c1 h hh a b hab u u ≤ simpson I c0 c1 h hh 0 1 zero_le_one u u := by
  have e1 := simpson_split I c0 c1 hh ha (hab.trans hb) u u
  have e2 := simpson_split I c0 c1 hh hab hb u u
  have n1 := (simpson I c0 c1 h hh 0 a ha).nonneg u
  have n2 := (simpson I c0 c1 h hh b 1 hb).nonneg u
  linarith

/-- The full element contains the left end point with weight `1/6`. -/
theorem pt0_le_full (u : Y) :
    h * I (c0 u) (c0 u) ≤ 6 * simpson I c0 c1 h hh 0 1 zero_le_one u u := by
  rw [simpson_apply]
  have h1 := I.nonneg (ptL c0 c1 ((0 + 1) / 2) u)
  have h2 := I.nonneg (ptL c0 c1 1 u)
  have e : ptL c0 c1 0 u = c0 u := by simp [ptL_apply]
  rw [e]
  have := mul_nonneg hh h1; have := mul_nonneg hh h2
  nlinarith

/-- The full element contains the right end point with weight `1/6`. -/
theorem pt1_le_full (u : Y) :
    h * I (ptL c0 c1 1 u) (ptL c0 c1 1 u) ≤ 6 * simpson I c0 c1 h hh 0 1 zero_le_one u u := by
  rw [simpson_apply]
  have h1 := I.nonneg (ptL c0 c1 ((0 + 1) / 2) u)
  have h2 := I.nonneg (ptL c0 c1 0 u)
  have := mul_nonneg hh h1; have := mul_nonneg hh h2
  nlinarith

/-- Inverse inequality in space: the slope is controlled by the two end point values. -/
theorem c1_le_full (u : Y) :
    h * I (c1 u) (c1 u) ≤ 24 * simpson I c0 c1 h hh 0 1 zero_le_one u u := by
  have e : c1 u = ptL c0 c1 1 u - c0 u := by simp [ptL_apply]
  have h1 := I.sub_sq_le (ptL c0 c1 1 u) (c0 u)
  rw [← e] at h1
  have h2 := pt0_le_full I c0 c1 hh u
  have h3 := pt1_le_full I c0 c1 hh u
  have := mul_le_mul_of_nonneg_left h1 hh
  linarith

/-- Any point value is controlled by the end point values (affine in `ξ`):
`I(u(ξ)) ≤ 2 (1-ξ)² I(u(0)) + 2 ξ² I(u(1))`. -/
theorem pt_le (ξ : ℝ) (u : Y) :
    I (ptL c0 c1 ξ u) (ptL c0 c1 ξ u)
      ≤ 2 * (1 - ξ) ^ 2 * I (c0 u) (c0 u) + 2 * ξ ^ 2 * I (ptL c0 c1 1 u) (ptL c0 c1 1 u) := by
  have e : ptL c0 c1 ξ u = (1 - ξ) • c0 u + ξ • ptL c0 c1 1 u := by
    simp only [ptL_apply]; module
  rw [e]
  have h1 := I.add_sq_le ((1 - ξ) • c0 u) (ξ • ptL c0 c1 1 u)
  rw [I.smul_sq, I.smul_sq] at h1
  linarith

/-- For functions which are constant in space, the integral is `h (b - a)` times the value. -/
theorem simpson_const {u : Y} (hu : c1 u = 0) :
    simpson I c0 c1 h hh a b hab u u = h * (b - a) * I (c0 u) (c0 u) := by
  rw [simpson_closed, hu]; simp; ring

end SemiIP

end StDgdg
