import StDgdg.Ode.Interval

/-!
# Validation example `d = 1`, moving domain, part 1: the transport identity in time

The physical part of an element is `ξ ∈ [c_L(t), c_H(t)]` (local coordinate), where the cut
positions `c(t) = clamp (κ + μ t)` are continuous and piecewise affine in time: they move
with the boundary while `0 ≤ κ + μ t < 1` and are constant otherwise.

For `P(c, t) = c A(t) + c²/2 B(t) + c³/3 C(t) = ∫_0^c (A + ξ B + ξ² C)(t) dξ` we prove the
Leibniz rule

`P(c(b), b) - P(c(a), a) = ∫_a^b [ ∂_t P(c(t), t) + μ 1_{moving}(t) (A + c B + c² C)(t) ] dt`,

by the fundamental theorem of calculus for functions with a right derivative.
-/

namespace StDgdg.Move1d

open Ode intervalIntegral Set Filter Topology

/-- clamp to `[0, 1]` -/
noncomputable def clamp (s : ℝ) : ℝ := max 0 (min 1 s)

theorem clamp_nonneg (s : ℝ) : 0 ≤ clamp s := le_max_left _ _
theorem clamp_le_one (s : ℝ) : clamp s ≤ 1 := max_le zero_le_one (min_le_left _ _)

theorem clamp_of_nonpos {s : ℝ} (h : s ≤ 0) : clamp s = 0 := by
  unfold clamp; rw [min_eq_right (by linarith), max_eq_left h]

theorem clamp_of_ge {s : ℝ} (h : 1 ≤ s) : clamp s = 1 := by
  unfold clamp; rw [min_eq_left h, max_eq_right zero_le_one]

theorem clamp_mid {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) : clamp s = s := by
  unfold clamp; rw [min_eq_right h1, max_eq_right h0]

theorem clamp_mono {s s' : ℝ} (h : s ≤ s') : clamp s ≤ clamp s' := by
  unfold clamp; exact max_le_max le_rfl (min_le_min le_rfl h)

theorem continuous_clamp : Continuous clamp := by
  unfold clamp; fun_prop

/-- indicator of the regime in which the cut position moves -/
noncomputable def mov (s : ℝ) : ℝ := if 0 ≤ s ∧ s < 1 then 1 else 0

theorem mov_nonneg (s : ℝ) : 0 ≤ mov s := by unfold mov; split_ifs <;> norm_num

section

variable (κ μ : ℝ)

theorem continuous_cut : Continuous fun t : ℝ => clamp (κ + μ * t) :=
  continuous_clamp.comp (by fun_prop)

variable {μ} (hμ : 0 ≤ μ)

include hμ in
/-- The right derivative of the cut position. -/
theorem cut_deriv_right (t : ℝ) :
    HasDerivWithinAt (fun t : ℝ => clamp (κ + μ * t)) (μ * mov (κ + μ * t)) (Ioi t) t := by
  have hs : HasDerivAt (fun t : ℝ => κ + μ * t) μ t := by
    simpa using ((hasDerivAt_id t).const_mul μ).const_add κ
  have hc : Continuous fun t : ℝ => κ + μ * t := by fun_prop
  rcases lt_or_ge (κ + μ * t) 0 with h | h0
  · have ev : (fun t : ℝ => clamp (κ + μ * t)) =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      have : ∀ᶠ t' in 𝓝 t, κ + μ * t' < 0 := hc.continuousAt.eventually (gt_mem_nhds h)
      filter_upwards [this] with t' ht'
      exact clamp_of_nonpos ht'.le
    have h1 : HasDerivAt (fun t : ℝ => clamp (κ + μ * t)) 0 t :=
      (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq ev
    have e : μ * mov (κ + μ * t) = 0 := by
      unfold mov; rw [if_neg (fun hh => absurd hh.1 (not_le.2 h))]; ring
    rw [e]
    exact h1.hasDerivWithinAt
  · rcases lt_or_ge (κ + μ * t) 1 with h1 | h1
    · have ev : (fun t : ℝ => clamp (κ + μ * t)) =ᶠ[𝓝[>] t] fun t => κ + μ * t := by
        have e1 : ∀ᶠ t' in 𝓝[>] t, κ + μ * t' < 1 :=
          (hc.continuousAt.eventually (gt_mem_nhds h1)).filter_mono nhdsWithin_le_nhds
        filter_upwards [e1, self_mem_nhdsWithin] with t' h1' ht'
        have := mul_le_mul_of_nonneg_left (le_of_lt (mem_Ioi.1 ht')) hμ
        exact clamp_mid (by linarith) h1'.le
      have h2 := (hs.hasDerivWithinAt (s := Ioi t)).congr_of_eventuallyEq ev (clamp_mid h0 h1.le)
      have e : μ * mov (κ + μ * t) = μ := by
        unfold mov; rw [if_pos ⟨h0, h1⟩]; ring
      rw [e]
      exact h2
    · have ev : (fun t : ℝ => clamp (κ + μ * t)) =ᶠ[𝓝[>] t] fun _ => (1 : ℝ) :=
        eventually_nhdsWithin_of_forall fun t' ht' => by
          have := mul_le_mul_of_nonneg_left (le_of_lt (mem_Ioi.1 ht')) hμ
          exact clamp_of_ge (by linarith)
      have h2 := ((hasDerivAt_const t (1 : ℝ)).hasDerivWithinAt (s := Ioi t)).congr_of_eventuallyEq
        ev (clamp_of_ge h1)
      have e : μ * mov (κ + μ * t) = 0 := by
        unfold mov; rw [if_neg (fun hh => absurd hh.2 (not_lt.2 h1))]; ring
      rw [e]
      exact h2

include hμ in
theorem mov_intble (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => mov (κ + μ * t)) MeasureTheory.volume a b := by
  have m1 : Monotone fun t : ℝ => (if 0 ≤ κ + μ * t then (1 : ℝ) else 0) := by
    intro t t' h
    have := mul_le_mul_of_nonneg_left h hμ
    dsimp only
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd (by linarith : 0 ≤ κ + μ * t') h2
    · exact zero_le_one
    · exact le_rfl
  have m2 : Monotone fun t : ℝ => (if 1 ≤ κ + μ * t then (1 : ℝ) else 0) := by
    intro t t' h
    have := mul_le_mul_of_nonneg_left h hμ
    dsimp only
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd (by linarith : 1 ≤ κ + μ * t') h2
    · exact zero_le_one
    · exact le_rfl
  have e : (fun t : ℝ => mov (κ + μ * t))
      = fun t => (if 0 ≤ κ + μ * t then (1 : ℝ) else 0) - (if 1 ≤ κ + μ * t then (1 : ℝ) else 0) := by
    funext t
    unfold mov
    by_cases h0 : 0 ≤ κ + μ * t <;> by_cases h1 : 1 ≤ κ + μ * t
    · simp [h0, h1, not_lt.2 h1]
    · simp [h0, h1, not_le.1 h1]
    · exfalso; linarith
    · simp [h0, h1]
  rw [e]
  exact m1.intervalIntegrable.sub m2.intervalIntegrable

variable (A B C : Sm)

/-- `P(c(t), t)`, `c(t) = clamp (κ + μ t)` -/
noncomputable def Pc (μ : ℝ) (t : ℝ) : ℝ :=
  clamp (κ + μ * t) * A t + clamp (κ + μ * t) ^ 2 / 2 * B t + clamp (κ + μ * t) ^ 3 / 3 * C t

/-- the right derivative of `t ↦ P(c(t), t)` -/
noncomputable def dPc (μ : ℝ) (t : ℝ) : ℝ :=
  (clamp (κ + μ * t) * D A t + clamp (κ + μ * t) ^ 2 / 2 * D B t
      + clamp (κ + μ * t) ^ 3 / 3 * D C t)
    + μ * mov (κ + μ * t)
      * (A t + clamp (κ + μ * t) * B t + clamp (κ + μ * t) ^ 2 * C t)

include hμ in
theorem dPc_intble (a b : ℝ) : IntervalIntegrable (dPc κ A B C μ) MeasureTheory.volume a b := by
  have hc := continuous_cut κ μ
  have hA := cont A; have hB := cont B; have hC := cont C
  have hA' := cont (D A); have hB' := cont (D B); have hC' := cont (D C)
  have h1 : IntervalIntegrable (fun t : ℝ => clamp (κ + μ * t) * D A t
      + clamp (κ + μ * t) ^ 2 / 2 * D B t + clamp (κ + μ * t) ^ 3 / 3 * D C t)
      MeasureTheory.volume a b :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have h2 : ContinuousOn (fun t : ℝ => A t + clamp (κ + μ * t) * B t
      + clamp (κ + μ * t) ^ 2 * C t) (uIcc a b) :=
    Continuous.continuousOn (by fun_prop)
  exact h1.add (((mov_intble κ hμ a b).const_mul μ).mul_continuousOn h2)

include hμ in
/-- **Leibniz rule** for a clamped, piecewise affine cut position. -/
theorem leibniz {a b : ℝ} (hab : a ≤ b) :
    ∫ t in a..b, dPc κ A B C μ t = Pc κ A B C μ b - Pc κ A B C μ a := by
  have hc := continuous_cut κ μ
  have hA := cont A; have hB := cont B; have hC := cont C
  refine integral_eq_sub_of_hasDeriv_right_of_le hab
    (Continuous.continuousOn (by unfold Pc; fun_prop)) (fun t _ => ?_) (dPc_intble κ hμ A B C a b)
  have hg := cut_deriv_right κ hμ t
  have dA := (hasDerivAt A t).hasDerivWithinAt (s := Ioi t)
  have dB := (hasDerivAt B t).hasDerivWithinAt (s := Ioi t)
  have dC := (hasDerivAt C t).hasDerivWithinAt (s := Ioi t)
  have h := ((hg.mul dA).add (((hg.pow 2).div_const 2).mul dB)).add
    (((hg.pow 3).div_const 3).mul dC)
  have h' : HasDerivWithinAt (Pc κ A B C μ) _ (Ioi t) t := h
  refine h'.congr_deriv ?_
  unfold dPc
  simp only [Pi.pow_apply]
  norm_num
  ring

end

end StDgdg.Move1d
