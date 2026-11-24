import StDgdg.Continuity

/-!
# Layer 2, part 10: `lemma_approx` and `thm_apriori`

The interpolation estimates `eq_interpol` are assumptions (`ErrorData`); `lemma_approx` and
the a priori error bound are derived from them. All norms are squared.
-/

namespace StDgdg

open Finset Real

variable {P : Consts} {ι X Fs Ts : Type*} [Fintype ι]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Fs] [Module ℝ Fs] [AddCommGroup Ts] [Module ℝ Ts]

namespace ErrorData

variable {S : Setting P ι X Fs Ts} {Ci : ℝ} (D : ErrorData S Ci)

/-- the interpolation error `e = u^e - I_h u^e` -/
@[reducible] def e : X := D.ue - D.Ih

/-- `‖[I_h u^e]‖²` over all full facets -/
def FF : ℝ :=
  ∑ n ∈ range S.N, (S.Fgp n (S.jmp D.Ih) (S.jmp D.Ih) + S.Fint n (S.jmp D.Ih) (S.jmp D.Ih))

theorem FF_nonneg : 0 ≤ D.FF :=
  sum_nonneg fun n _ => add_nonneg ((S.Fgp n).nonneg _) ((S.Fint n).nonneg _)

/-- as `u` is continuous across facets, `[e] = -[I_h u^e]` -/
theorem jQ_e_le : S.jQ D.e ≤ D.FF := by
  unfold Setting.jQ FF
  refine sum_le_sum fun n _ => ?_
  have h : S.jmp D.e = -S.jmp D.Ih := by
    unfold e; rw [map_sub, D.jmp_ue, zero_sub]
  rw [h]
  have := S.FQ_le n (by in_range) (S.jmp D.Ih)
  simpa using this

theorem L2_e_le :
    S.L2 D.e ≤ 2 * (S.τ * S.nQT (S.dt D.e)) + 2 * (S.τ * S.wInf ^ 2 * S.gQT D.e) := by
  have hτ := S.τ_pos
  have h1 : S.nQ (S.Lc D.e) ≤ 2 * S.nQ (S.dt D.e) + 2 * S.nQ (S.Lc D.e - S.dt D.e) := by
    have e' : S.Lc D.e = S.dt D.e + (S.Lc D.e - S.dt D.e) := by abel
    have := S.nQ_add_le (S.dt D.e) (S.Lc D.e - S.dt D.e)
    rwa [← e'] at this
  have h2 := S.nQ_le_nQT (S.dt D.e)
  have h3 : S.nQ (S.Lc D.e - S.dt D.e) ≤ S.wInf ^ 2 * S.gQ D.e := by
    unfold Setting.nQ Setting.gQ Setting.gQs
    exact sum_le_mul_sum fun n _ => S.Lc_dt n (by in_range) D.e
  have h4 := mul_le_mul_of_nonneg_left (S.gQ_le_gQT D.e) (sq_nonneg S.wInf)
  have m := mul_le_mul_of_nonneg_left (h1.trans (by linarith :
    2 * S.nQ (S.dt D.e) + 2 * S.nQ (S.Lc D.e - S.dt D.e)
      ≤ 2 * S.nQT (S.dt D.e) + 2 * (S.wInf ^ 2 * S.gQT D.e))) hτ.le
  unfold Setting.L2
  linarith

theorem time_traces_e_le :
    ∑ n ∈ range S.N, (S.Om n (S.bot n D.e) (S.bot n D.e)
        + S.Om (n + 1) (S.top n D.e) (S.top n D.e))
      ≤ P.C * (S.τ⁻¹ * S.nQT D.e + S.τ * S.nQT (S.dt D.e)) := by
  unfold Setting.nQT
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  exact sum_le_mul_sum fun n _ => S.trace_time_cont n (by in_range) D.e

theorem TT_e_le : S.TT D.e ≤ P.C * (S.τ⁻¹ * S.nQT D.e + S.τ * S.nQT (S.dt D.e)) := by
  refine le_trans (sum_le_sum fun n _ => ?_) D.time_traces_e_le
  have := (S.Om n).nonneg (S.bot n D.e)
  linarith

theorem FU_e_le : S.h * S.FU D.e ≤ P.C * (S.nQT D.e + S.h ^ 2 * S.gQT D.e) := by
  have hh := S.h_pos
  unfold Setting.FU Setting.nQT Setting.gQT Setting.gQTs
  rw [mul_sum, mul_sum, ← sum_add_distrib, mul_sum]
  refine sum_le_sum fun n _ => ?_
  have h1 := mul_le_mul_of_nonneg_left (S.FQ_le n (by in_range) (S.up D.e)) hh.le
  have h2 := S.trace_up_cont n (by in_range) D.e
  linarith

/-- Constant of `approx_general`. -/
noncomputable def Kap (P : Consts) : ℝ := 2 + 4 * P.C + P.γJ

/-- The right hand side of the general approximation bound in terms of the four
interpolation quantities. -/
noncomputable def Θ : ℝ :=
  S.τ⁻¹ * S.nQT D.e + S.τ * S.nQT (S.dt D.e)
    + (S.α + S.τ * S.wInf ^ 2 + S.τ⁻¹ * S.h ^ 2) * S.gQT D.e + S.α * D.D2
    + (S.α + S.wInf * S.h) * (S.h⁻¹ * D.FF + S.h⁻¹ ^ 2 * S.jh D.Ih)

/-- **Regime-independent form of `lemma_approx`**: all summands of
`|||e|||_*² + |I_h u^e|_J²` in terms of the interpolation quantities of `eq_interpol`. -/
theorem approx_general : S.tnstar2 D.e + S.J2 D.Ih ≤ Kap P * D.Θ := by
  have hC := P.C_pos; have hγ := P.hγJ; have hτ := S.τ_pos; have hτ1 := S.τ_le_one
  have hτi := S.τinv_pos; have hh := S.h_pos; have hhi := S.hinv_pos
  have hα := S.α_nonneg; have hw := S.wInf_nonneg
  have ha0 := S.nQT_nonneg D.e; have ha1 := S.nQT_nonneg (S.dt D.e)
  have ha2 := S.gQT_nonneg D.e; have ha3 := D.hD2
  have hFF := D.FF_nonneg; have hjh := S.jh_nonneg D.Ih
  -- the ten summands
  have f1 := D.L2_e_le
  have f2 : S.nQ D.e ≤ S.τ⁻¹ * S.nQT D.e := by
    have h1 := S.nQ_le_nQT D.e
    have : 1 ≤ S.τ⁻¹ := (one_le_inv₀ hτ).2 hτ1
    nlinarith
  have f3 := mul_le_mul_of_nonneg_left (S.gQ_le_gQT D.e) hα
  have f4 : S.α * (S.h⁻¹ * S.jQ D.e) ≤ S.α * (S.h⁻¹ * D.FF) := by
    have := D.jQ_e_le; gcongr
  have f5 : S.upw2 D.e ≤ 2 * (P.C * (S.τ⁻¹ * S.nQT D.e + S.τ * S.nQT (S.dt D.e)))
      + S.wInf * S.h * (S.h⁻¹ * D.FF) := by
    have h1 := S.upw2_le_traces D.e
    have h2 := D.time_traces_e_le
    have h3 := mul_le_mul_of_nonneg_left D.jQ_e_le hw
    have e' : S.wInf * S.h * (S.h⁻¹ * D.FF) = S.wInf * D.FF := by field_simp
    linarith
  have f6 := mul_le_mul_of_nonneg_left (S.nQ_le_nQT D.e) hτi.le
  have f7 := D.TT_e_le
  have f8 : S.h * S.τ⁻¹ * S.FU D.e
      ≤ P.C * (S.τ⁻¹ * S.nQT D.e) + P.C * (S.τ⁻¹ * S.h ^ 2 * S.gQT D.e) := by
    have := mul_le_mul_of_nonneg_left D.FU_e_le hτi.le
    linarith
  have f9 : S.α * (S.h * S.FN D.e) ≤ P.C * (S.α * S.gQT D.e) + P.C * (S.α * D.D2) := by
    have := mul_le_mul_of_nonneg_left D.nfl_e hα
    linarith
  have f10 : S.J2 D.Ih = P.γJ * (S.α * (S.h⁻¹ ^ 2 * S.jh D.Ih))
      + P.γJ * (S.wInf * S.h * (S.h⁻¹ ^ 2 * S.jh D.Ih)) := by
    unfold Setting.J2 Setting.cJ; field_simp
  -- nonnegativity of the atoms
  have t1 : 0 ≤ S.τ⁻¹ * S.nQT D.e := by positivity
  have t2 : 0 ≤ S.τ * S.nQT (S.dt D.e) := by positivity
  have t3 : 0 ≤ S.τ * S.wInf ^ 2 * S.gQT D.e := by positivity
  have t4 : 0 ≤ S.α * S.gQT D.e := by positivity
  have t5 : 0 ≤ S.τ⁻¹ * S.h ^ 2 * S.gQT D.e := by positivity
  have t6 : 0 ≤ S.α * D.D2 := by positivity
  have t7 : 0 ≤ S.α * (S.h⁻¹ * D.FF) := by positivity
  have t8 : 0 ≤ S.wInf * S.h * (S.h⁻¹ * D.FF) := by positivity
  have t9 : 0 ≤ S.α * (S.h⁻¹ ^ 2 * S.jh D.Ih) := by positivity
  have t10 : 0 ≤ S.wInf * S.h * (S.h⁻¹ ^ 2 * S.jh D.Ih) := by positivity
  have c1 := mul_nonneg hC.le t1; have g1 := mul_nonneg hγ.le t1
  have c2 := mul_nonneg hC.le t2; have g2 := mul_nonneg hγ.le t2
  have c3 := mul_nonneg hC.le t3; have g3 := mul_nonneg hγ.le t3
  have c4 := mul_nonneg hC.le t4; have g4 := mul_nonneg hγ.le t4
  have c5 := mul_nonneg hC.le t5; have g5 := mul_nonneg hγ.le t5
  have c6 := mul_nonneg hC.le t6; have g6 := mul_nonneg hγ.le t6
  have c7 := mul_nonneg hC.le t7; have g7 := mul_nonneg hγ.le t7
  have c8 := mul_nonneg hC.le t8; have g8 := mul_nonneg hγ.le t8
  have c9 := mul_nonneg hC.le t9; have g9 := mul_nonneg hγ.le t9
  have c10 := mul_nonneg hC.le t10; have g10 := mul_nonneg hγ.le t10
  unfold Kap Θ Setting.tnstar2 Setting.tn2 Setting.c2
  rw [f10]
  linarith

/-! ### Case D -/

theorem Tt_nonneg : 0 ≤ S.τ ^ (2 * D.kt) := pow_nonneg S.τ_pos.le _
theorem Hs_nonneg : 0 ≤ S.h ^ (2 * D.ks) := pow_nonneg S.h_pos.le _

/-- **`lemma_approx`, Case D**, `eq_approx_caseD` (squared):
`|||e|||_*² + |I_h u^e|_J² ≲ (α h^{2k_s} + α Δt^{2k_t+2} + Δt^{2k_t+1}) ‖u‖²`. -/
theorem approx_D (hr : S.regime = .D) :
    D.Θ ≤ (2 + 5 * P.C) * Ci * (S.α * S.h ^ (2 * D.ks) + S.α * (S.τ ^ 2 * S.τ ^ (2 * D.kt))
      + S.τ * S.τ ^ (2 * D.kt)) * D.U := by
  obtain ⟨hD1, hD2⟩ := S.caseD hr
  have hwh := S.w_h_le hr
  have hC := P.C_pos; have hτ := S.τ_pos; have hτ1 := S.τ_le_one
  have hτi := S.τinv_pos; have hh := S.h_pos; have hhi := S.hinv_pos
  have hα := S.α_nonneg; have hw := S.wInf_nonneg
  have hT := D.Tt_nonneg; have hH := D.Hs_nonneg; have hCi := D.hCi; have hU := D.hU
  have ha2 := S.gQT_nonneg D.e; have ha3 := D.hD2
  set Tt : ℝ := S.τ ^ (2 * D.kt) with hTt
  set Hs : ℝ := S.h ^ (2 * D.ks) with hHs
  have i0 := D.i_L2; have i1 := D.i_dt; have i2 := D.i_grad; have i3 := D.i_jump
  rw [← hTt, ← hHs] at i0 i1 i2
  rw [← hHs] at i3
  have hCU : 0 ≤ Ci * D.U := mul_nonneg hCi hU
  -- `Δt⁻¹ h² ≤ C α`, `Δt h² ≤ C α`
  have k1 : S.τ⁻¹ * S.h ^ 2 ≤ P.C * S.α :=
    calc S.τ⁻¹ * S.h ^ 2 ≤ S.τ⁻¹ * (P.C * S.α * S.τ) := by gcongr
      _ = P.C * S.α := by field_simp
  have k2 : S.τ * S.h ^ 2 ≤ P.C * S.α := by
    have : S.τ * S.h ^ 2 ≤ 1 * (P.C * S.α * 1) := by
      have h0 : 0 ≤ P.C * S.α := by positivity
      calc S.τ * S.h ^ 2 ≤ 1 * S.h ^ 2 := by gcongr
        _ ≤ 1 * (P.C * S.α * S.τ) := by gcongr
        _ ≤ 1 * (P.C * S.α * 1) := by gcongr
    linarith
  -- the four groups
  have b0 : S.τ⁻¹ * S.nQT D.e ≤ Ci * D.U * (S.τ * Tt + P.C * (S.α * Hs)) :=
    calc S.τ⁻¹ * S.nQT D.e ≤ S.τ⁻¹ * (Ci * (S.τ ^ 2 * Tt + S.h ^ 2 * Hs) * D.U) := by gcongr
      _ = Ci * D.U * (S.τ * Tt + (S.τ⁻¹ * S.h ^ 2) * Hs) := by field_simp
      _ ≤ Ci * D.U * (S.τ * Tt + (P.C * S.α) * Hs) := by gcongr
      _ = Ci * D.U * (S.τ * Tt + P.C * (S.α * Hs)) := by ring
  have b1 : S.τ * S.nQT (S.dt D.e) ≤ Ci * D.U * (S.τ * Tt + P.C * (S.α * Hs)) :=
    calc S.τ * S.nQT (S.dt D.e) ≤ S.τ * (Ci * (Tt + S.h ^ 2 * Hs) * D.U) := by gcongr
      _ = Ci * D.U * (S.τ * Tt + (S.τ * S.h ^ 2) * Hs) := by ring
      _ ≤ Ci * D.U * (S.τ * Tt + (P.C * S.α) * Hs) := by gcongr
      _ = Ci * D.U * (S.τ * Tt + P.C * (S.α * Hs)) := by ring
  have b2 : (S.α + S.τ * S.wInf ^ 2 + S.τ⁻¹ * S.h ^ 2) * S.gQT D.e + S.α * D.D2
      ≤ Ci * D.U * ((1 + 2 * P.C) * (S.α * (S.τ ^ 2 * Tt)) + (1 + 2 * P.C) * (S.α * Hs)) := by
    have hcoef : S.α + S.τ * S.wInf ^ 2 + S.τ⁻¹ * S.h ^ 2 ≤ (1 + 2 * P.C) * S.α := by
      have : S.τ * S.wInf ^ 2 = S.wInf ^ 2 * S.τ := by ring
      linarith
    have h1 := mul_le_mul_of_nonneg_right hcoef ha2
    have h2 : S.α * D.D2 ≤ (1 + 2 * P.C) * S.α * D.D2 := by
      have : 0 ≤ S.α * D.D2 := by positivity
      nlinarith
    have h3 := mul_le_mul_of_nonneg_left i2 (by positivity : 0 ≤ (1 + 2 * P.C) * S.α)
    calc (S.α + S.τ * S.wInf ^ 2 + S.τ⁻¹ * S.h ^ 2) * S.gQT D.e + S.α * D.D2
        ≤ (1 + 2 * P.C) * S.α * (S.gQT D.e + D.D2) := by linarith
      _ ≤ (1 + 2 * P.C) * S.α * (Ci * (S.τ ^ 2 * Tt + Hs) * D.U) := h3
      _ = Ci * D.U * ((1 + 2 * P.C) * (S.α * (S.τ ^ 2 * Tt)) + (1 + 2 * P.C) * (S.α * Hs)) := by
          ring
  have b3 : (S.α + S.wInf * S.h) * (S.h⁻¹ * D.FF + S.h⁻¹ ^ 2 * S.jh D.Ih)
      ≤ Ci * D.U * ((1 + P.C) * (S.α * Hs)) := by
    have hcoef : S.α + S.wInf * S.h ≤ (1 + P.C) * S.α := by linarith
    have hG : 0 ≤ S.h⁻¹ * D.FF + S.h⁻¹ ^ 2 * S.jh D.Ih := by
      have := D.FF_nonneg; have := S.jh_nonneg D.Ih; positivity
    calc (S.α + S.wInf * S.h) * (S.h⁻¹ * D.FF + S.h⁻¹ ^ 2 * S.jh D.Ih)
        ≤ (1 + P.C) * S.α * (S.h⁻¹ * D.FF + S.h⁻¹ ^ 2 * S.jh D.Ih) :=
          mul_le_mul_of_nonneg_right hcoef hG
      _ ≤ (1 + P.C) * S.α * (Ci * Hs * D.U) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          unfold FF; exact i3
      _ = Ci * D.U * ((1 + P.C) * (S.α * Hs)) := by ring
  have s1 : 0 ≤ Ci * D.U * (S.τ * Tt) := by positivity
  have s2 : 0 ≤ Ci * D.U * (S.α * Hs) := by positivity
  have s3 : 0 ≤ Ci * D.U * (S.α * (S.τ ^ 2 * Tt)) := by positivity
  have s1' := mul_nonneg hC.le s1
  have s2' := mul_nonneg hC.le s2
  have s3' := mul_nonneg hC.le s3
  unfold Θ
  linarith

/-! ### Case C -/

/-- **`lemma_approx`, Case C** (squared), without using `‖w‖_∞ ≃ 1` or `h ≲ 1`:
`|||e|||_*² + |I_h u^e|_J² ≲ ((1 + h²) Δt^{2k_t+1} + ‖w‖_∞ h^{2k_s+1}
  + α (h^{2k_s} + Δt^{2k_t+2})) ‖u‖²`.
With `‖w‖_∞ ≃ 1` (so `Δt ≃ h`) and `h ≲ 1` this is `eq_approx_caseC`. -/
theorem approx_C (hr : S.regime = .C) :
    D.Θ ≤ (2 + 4 * P.C + 2 * P.C ^ 2) * Ci
      * ((1 + S.h ^ 2) * (S.τ * S.τ ^ (2 * D.kt)) + S.wInf * S.h * S.h ^ (2 * D.ks)
        + S.α * (S.h ^ (2 * D.ks) + S.τ ^ 2 * S.τ ^ (2 * D.kt))) * D.U := by
  obtain ⟨hC1, hC2⟩ := S.caseC hr
  have hC := P.C_pos; have hτ := S.τ_pos; have hτ1 := S.τ_le_one
  have hτi := S.τinv_pos; have hh := S.h_pos; have hhi := S.hinv_pos
  have hα := S.α_nonneg; have hw := S.wInf_nonneg
  have hT := D.Tt_nonneg; have hH := D.Hs_nonneg; have hCi := D.hCi; have hU := D.hU
  have ha2 := S.gQT_nonneg D.e; have ha3 := D.hD2
  set Tt : ℝ := S.τ ^ (2 * D.kt) with hTt
  set Hs : ℝ := S.h ^ (2 * D.ks) with hHs
  have i0 := D.i_L2; have i1 := D.i_dt; have i2 := D.i_grad; have i3 := D.i_jump
  rw [← hTt, ← hHs] at i0 i1 i2
  rw [← hHs] at i3
  -- `Δt⁻¹ h² ≤ C ‖w‖ h`, `Δt h² ≤ C ‖w‖ h`, `Δt ‖w‖² ≤ C ‖w‖ h`
  have k1 : S.τ⁻¹ * S.h ^ 2 ≤ P.C * (S.wInf * S.h) :=
    calc S.τ⁻¹ * S.h ^ 2 = S.τ⁻¹ * S.h * S.h := by ring
      _ ≤ S.τ⁻¹ * (P.C * S.wInf * S.τ) * S.h := by gcongr
      _ = P.C * (S.wInf * S.h) := by field_simp
  have k2 : S.τ * S.h ^ 2 ≤ P.C * (S.wInf * S.h) := by
    have : S.τ ≤ S.τ⁻¹ := le_trans hτ1 ((one_le_inv₀ hτ).2 hτ1)
    have := mul_le_mul_of_nonneg_right this (sq_nonneg S.h)
    linarith
  have k3 : S.τ * S.wInf ^ 2 ≤ P.C * (S.wInf * S.h) :=
    calc S.τ * S.wInf ^ 2 = (S.wInf * S.τ) * S.wInf := by ring
      _ ≤ (P.C * S.h) * S.wInf := by gcongr
      _ = P.C * (S.wInf * S.h) := by ring
  have b0 : S.τ⁻¹ * S.nQT D.e ≤ Ci * D.U * (S.τ * Tt + P.C * (S.wInf * S.h * Hs)) :=
    calc S.τ⁻¹ * S.nQT D.e ≤ S.τ⁻¹ * (Ci * (S.τ ^ 2 * Tt + S.h ^ 2 * Hs) * D.U) := by gcongr
      _ = Ci * D.U * (S.τ * Tt + (S.τ⁻¹ * S.h ^ 2) * Hs) := by field_simp
      _ ≤ Ci * D.U * (S.τ * Tt + (P.C * (S.wInf * S.h)) * Hs) := by gcongr
      _ = Ci * D.U * (S.τ * Tt + P.C * (S.wInf * S.h * Hs)) := by ring
  have b1 : S.τ * S.nQT (S.dt D.e) ≤ Ci * D.U * (S.τ * Tt + P.C * (S.wInf * S.h * Hs)) :=
    calc S.τ * S.nQT (S.dt D.e) ≤ S.τ * (Ci * (Tt + S.h ^ 2 * Hs) * D.U) := by gcongr
      _ = Ci * D.U * (S.τ * Tt + (S.τ * S.h ^ 2) * Hs) := by ring
      _ ≤ Ci * D.U * (S.τ * Tt + (P.C * (S.wInf * S.h)) * Hs) := by gcongr
      _ = Ci * D.U * (S.τ * Tt + P.C * (S.wInf * S.h * Hs)) := by ring
  -- `‖w‖ h Δt² ≤ C h² Δt`
  have k4 : S.wInf * S.h * S.τ ^ 2 ≤ P.C * (S.h ^ 2 * S.τ) :=
    calc S.wInf * S.h * S.τ ^ 2 = (S.wInf * S.τ) * S.h * S.τ := by ring
      _ ≤ (P.C * S.h) * S.h * S.τ := by gcongr
      _ = P.C * (S.h ^ 2 * S.τ) := by ring
  have b2 : (S.α + S.τ * S.wInf ^ 2 + S.τ⁻¹ * S.h ^ 2) * S.gQT D.e + S.α * D.D2
      ≤ Ci * D.U * (S.α * (S.τ ^ 2 * Tt + Hs) + 2 * P.C * (S.wInf * S.h * Hs)
        + 2 * P.C ^ 2 * (S.h ^ 2 * (S.τ * Tt))) := by
    have hcoef : S.α + S.τ * S.wInf ^ 2 + S.τ⁻¹ * S.h ^ 2
        ≤ S.α + 2 * P.C * (S.wInf * S.h) := by linarith
    have h1 := mul_le_mul_of_nonneg_right hcoef ha2
    have h2 : S.α * D.D2 ≤ (S.α + 2 * P.C * (S.wInf * S.h)) * D.D2 := by
      have : 0 ≤ 2 * P.C * (S.wInf * S.h) * D.D2 := by positivity
      linarith
    have h3 := mul_le_mul_of_nonneg_left i2
      (by positivity : 0 ≤ S.α + 2 * P.C * (S.wInf * S.h))
    have h4 : 2 * P.C * (S.wInf * S.h * S.τ ^ 2) * Tt ≤ 2 * P.C * (P.C * (S.h ^ 2 * S.τ)) * Tt := by
      gcongr
    have h5 := mul_le_mul_of_nonneg_left h4 (mul_nonneg hCi hU)
    calc (S.α + S.τ * S.wInf ^ 2 + S.τ⁻¹ * S.h ^ 2) * S.gQT D.e + S.α * D.D2
        ≤ (S.α + 2 * P.C * (S.wInf * S.h)) * (S.gQT D.e + D.D2) := by linarith
      _ ≤ (S.α + 2 * P.C * (S.wInf * S.h)) * (Ci * (S.τ ^ 2 * Tt + Hs) * D.U) := h3
      _ = Ci * D.U * (S.α * (S.τ ^ 2 * Tt + Hs) + 2 * P.C * (S.wInf * S.h * Hs))
          + Ci * D.U * (2 * P.C * (S.wInf * S.h * S.τ ^ 2) * Tt) := by ring
      _ ≤ Ci * D.U * (S.α * (S.τ ^ 2 * Tt + Hs) + 2 * P.C * (S.wInf * S.h * Hs))
          + Ci * D.U * (2 * P.C * (P.C * (S.h ^ 2 * S.τ)) * Tt) := by linarith
      _ = Ci * D.U * (S.α * (S.τ ^ 2 * Tt + Hs) + 2 * P.C * (S.wInf * S.h * Hs)
          + 2 * P.C ^ 2 * (S.h ^ 2 * (S.τ * Tt))) := by ring
  have b3 : (S.α + S.wInf * S.h) * (S.h⁻¹ * D.FF + S.h⁻¹ ^ 2 * S.jh D.Ih)
      ≤ Ci * D.U * (S.α * Hs + S.wInf * S.h * Hs) :=
    calc (S.α + S.wInf * S.h) * (S.h⁻¹ * D.FF + S.h⁻¹ ^ 2 * S.jh D.Ih)
        ≤ (S.α + S.wInf * S.h) * (Ci * Hs * D.U) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          unfold FF; exact i3
      _ = Ci * D.U * (S.α * Hs + S.wInf * S.h * Hs) := by ring
  have s1 : 0 ≤ Ci * D.U * (S.τ * Tt) := by positivity
  have s2 : 0 ≤ Ci * D.U * (S.wInf * S.h * Hs) := by positivity
  have s3 : 0 ≤ Ci * D.U * (S.α * (S.τ ^ 2 * Tt)) := by positivity
  have s4 : 0 ≤ Ci * D.U * (S.α * Hs) := by positivity
  have s5 : 0 ≤ Ci * D.U * (S.h ^ 2 * (S.τ * Tt)) := by positivity
  have s1' := mul_nonneg hC.le s1; have s1'' := mul_nonneg (sq_nonneg P.C) s1
  have s2' := mul_nonneg hC.le s2; have s2'' := mul_nonneg (sq_nonneg P.C) s2
  have s3' := mul_nonneg hC.le s3; have s3'' := mul_nonneg (sq_nonneg P.C) s3
  have s4' := mul_nonneg hC.le s4; have s4'' := mul_nonneg (sq_nonneg P.C) s4
  have s5' := mul_nonneg hC.le s5
  unfold Θ
  linarith

/-! ### `thm_apriori` -/

variable {Wc : WConsts} (E : ExpWeight S Wc)

include E in
/-- `prop_strang` with `w_h = I_h u^e`, combined with `approx_general`. -/
theorem error_le_Θ (hlam : P.lam0 Wc.Cφ ≤ P.lam)
    (hsmall : ExpWeight.Ksup P Wc * ExpWeight.Kw P Wc * √S.τ ≤ 1 / 8) :
    S.tn2 (D.ue - D.uh) ≤ ExpWeight.Kst P Wc * (Kap P * D.Θ) := by
  have h1 := E.strang hlam hsmall D.uh_mem D.Ih_mem D.f D.cons D.disc
  have h2 := D.approx_general
  have hK : 0 ≤ ExpWeight.Kst P Wc := by
    have := ExpWeight.Msq_pos P Wc; have := P.Kc1_pos; have := P.Kc2_pos
    unfold ExpWeight.Kst; positivity
  exact h1.trans (mul_le_mul_of_nonneg_left h2 hK)

include E in
/-- **`thm_apriori`, Case D**, `eq_apriori_caseD` (squared):
`|||u - u_h|||² ≲ (α (h^{2k_s} + Δt^{2k_t+2}) + Δt^{2k_t+1}) ‖u‖²_{H^{k_max+2}(Q)}`. -/
theorem apriori_D (hr : S.regime = .D) (hlam : P.lam0 Wc.Cφ ≤ P.lam)
    (hsmall : ExpWeight.Ksup P Wc * ExpWeight.Kw P Wc * √S.τ ≤ 1 / 8) :
    S.tn2 (D.ue - D.uh) ≤ ExpWeight.Kst P Wc * (Kap P * ((2 + 5 * P.C) * Ci
      * (S.α * S.h ^ (2 * D.ks) + S.α * (S.τ ^ 2 * S.τ ^ (2 * D.kt))
        + S.τ * S.τ ^ (2 * D.kt)) * D.U)) := by
  have h1 := D.error_le_Θ E hlam hsmall
  have hK : 0 ≤ ExpWeight.Kst P Wc * Kap P := by
    have := ExpWeight.Msq_pos P Wc; have := P.Kc1_pos; have := P.Kc2_pos
    have := P.C_pos; have := P.hγJ
    unfold ExpWeight.Kst Kap; positivity
  have h2 := mul_le_mul_of_nonneg_left (D.approx_D hr) hK
  linarith

include E in
/-- **`thm_apriori`, Case C** (squared), cf. `approx_C`:
`|||u - u_h|||² ≲ ((1 + h²) Δt^{2k_t+1} + ‖w‖_∞ h^{2k_s+1}
  + α (h^{2k_s} + Δt^{2k_t+2})) ‖u‖²_{H^{k_max+2}(Q)}`. -/
theorem apriori_C (hr : S.regime = .C) (hlam : P.lam0 Wc.Cφ ≤ P.lam)
    (hsmall : ExpWeight.Ksup P Wc * ExpWeight.Kw P Wc * √S.τ ≤ 1 / 8) :
    S.tn2 (D.ue - D.uh) ≤ ExpWeight.Kst P Wc * (Kap P * ((2 + 4 * P.C + 2 * P.C ^ 2) * Ci
      * ((1 + S.h ^ 2) * (S.τ * S.τ ^ (2 * D.kt)) + S.wInf * S.h * S.h ^ (2 * D.ks)
        + S.α * (S.h ^ (2 * D.ks) + S.τ ^ 2 * S.τ ^ (2 * D.kt))) * D.U)) := by
  have h1 := D.error_le_Θ E hlam hsmall
  have hK : 0 ≤ ExpWeight.Kst P Wc * Kap P := by
    have := ExpWeight.Msq_pos P Wc; have := P.Kc1_pos; have := P.Kc2_pos
    have := P.C_pos; have := P.hγJ
    unfold ExpWeight.Kst Kap; positivity
  have h2 := mul_le_mul_of_nonneg_left (D.approx_C hr) hK
  linarith

/-! ### Case C in the form of the paper -/

omit D in
theorem pow_le_pow_mul {C h : ℝ} (hC : 1 ≤ C) (hh0 : 0 < h) (hh : h ≤ C) {a b : ℕ}
    (hab : a ≤ b) : h ^ b ≤ C ^ b * h ^ a := by
  have e : h ^ b = h ^ (b - a) * h ^ a := by rw [← pow_add, Nat.sub_add_cancel hab]
  have h1 : h ^ (b - a) ≤ C ^ (b - a) := pow_le_pow_left₀ hh0.le hh _
  have h2 : C ^ (b - a) ≤ C ^ b := pow_le_pow_right₀ hC (Nat.sub_le _ _)
  rw [e]
  exact mul_le_mul_of_nonneg_right (h1.trans h2) (pow_nonneg hh0.le _)

omit D in
/-- The Case C rate in powers of `h` only, for `Δt ≲ h` and `h ≲ 1`. -/
theorem rate_C_le {C h τ w α : ℝ} {ks kt : ℕ} (hC : 1 ≤ C) (hh0 : 0 < h) (hh : h ≤ C)
    (hτ0 : 0 < τ) (hτ : τ ≤ C ^ 2 * h) (hw0 : 0 ≤ w) (hw : w ≤ C) (hα : 0 ≤ α) :
    (1 + h ^ 2) * (τ * τ ^ (2 * kt)) + w * h * h ^ (2 * ks) + α * (h ^ (2 * ks) + τ ^ 2 * τ ^ (2 * kt))
      ≤ 3 * C ^ (6 * (ks + kt) + 4)
        * (h * h ^ (2 * min ks kt) + α * (h ^ (2 * ks) + h ^ 2 * h ^ (2 * kt))) := by
  have hC0 : 0 < C := lt_of_lt_of_le one_pos hC
  set N : ℕ := 6 * (ks + kt) + 4 with hN
  set X : ℝ := h * h ^ (2 * min ks kt) with hX
  have hX0 : 0 ≤ X := by positivity
  have hCN : 1 ≤ C ^ N := one_le_pow₀ hC
  have mono : ∀ m : ℕ, m ≤ N → C ^ m ≤ C ^ N := fun m hm => pow_le_pow_right₀ hC hm
  -- `τ^{2kt} ≤ C^{4kt} h^{2kt}`
  have hτp : τ ^ (2 * kt) ≤ C ^ (4 * kt) * h ^ (2 * kt) := by
    calc τ ^ (2 * kt) ≤ (C ^ 2 * h) ^ (2 * kt) := pow_le_pow_left₀ hτ0.le hτ _
      _ = C ^ (4 * kt) * h ^ (2 * kt) := by rw [mul_pow, ← pow_mul]; congr 2; ring
  have hkt : h ^ (2 * kt) ≤ C ^ (2 * kt) * h ^ (2 * min ks kt) :=
    pow_le_pow_mul hC hh0 hh (by have := min_le_right ks kt; omega)
  have hks : h ^ (2 * ks) ≤ C ^ (2 * ks) * h ^ (2 * min ks kt) :=
    pow_le_pow_mul hC hh0 hh (by have := min_le_left ks kt; omega)
  have hh2 : 1 + h ^ 2 ≤ 2 * C ^ 2 := by nlinarith
  -- term A
  have A : (1 + h ^ 2) * (τ * τ ^ (2 * kt)) ≤ 2 * C ^ N * X := by
    have a1 : τ * τ ^ (2 * kt) ≤ (C ^ 2 * h) * (C ^ (4 * kt) * (C ^ (2 * kt) * h ^ (2 * min ks kt))) := by
      have := hτp.trans (mul_le_mul_of_nonneg_left hkt (by positivity))
      exact mul_le_mul hτ this (by positivity) (by positivity)
    have a2 : (1 + h ^ 2) * (τ * τ ^ (2 * kt))
        ≤ (2 * C ^ 2) * ((C ^ 2 * h) * (C ^ (4 * kt) * (C ^ (2 * kt) * h ^ (2 * min ks kt)))) :=
      mul_le_mul hh2 a1 (by positivity) (by positivity)
    have e : (2 * C ^ 2) * ((C ^ 2 * h) * (C ^ (4 * kt) * (C ^ (2 * kt) * h ^ (2 * min ks kt))))
        = 2 * C ^ (6 * kt + 4) * X := by rw [hX]; ring
    have m := mono (6 * kt + 4) (by omega)
    have := mul_le_mul_of_nonneg_right m hX0
    linarith
  -- term B
  have B : w * h * h ^ (2 * ks) ≤ C ^ N * X := by
    have b1 : w * h * h ^ (2 * ks) ≤ C * h * (C ^ (2 * ks) * h ^ (2 * min ks kt)) :=
      mul_le_mul (by gcongr) hks (by positivity) (by positivity)
    have e : C * h * (C ^ (2 * ks) * h ^ (2 * min ks kt)) = C ^ (2 * ks + 1) * X := by
      rw [hX]; ring
    have m := mono (2 * ks + 1) (by omega)
    have := mul_le_mul_of_nonneg_right m hX0
    linarith
  -- term D
  have Dq : α * (h ^ (2 * ks) + τ ^ 2 * τ ^ (2 * kt))
      ≤ C ^ N * (α * (h ^ (2 * ks) + h ^ 2 * h ^ (2 * kt))) := by
    have d1 : τ ^ 2 * τ ^ (2 * kt) ≤ (C ^ 2 * h) ^ 2 * (C ^ (4 * kt) * h ^ (2 * kt)) :=
      mul_le_mul (pow_le_pow_left₀ hτ0.le hτ _) hτp (by positivity) (by positivity)
    have e : (C ^ 2 * h) ^ 2 * (C ^ (4 * kt) * h ^ (2 * kt))
        = C ^ (4 * kt + 4) * (h ^ 2 * h ^ (2 * kt)) := by ring
    have m := mono (4 * kt + 4) (by omega)
    have p1 : 0 ≤ h ^ 2 * h ^ (2 * kt) := by positivity
    have p2 : 0 ≤ h ^ (2 * ks) := by positivity
    have d2 : τ ^ 2 * τ ^ (2 * kt) ≤ C ^ N * (h ^ 2 * h ^ (2 * kt)) := by
      have := mul_le_mul_of_nonneg_right m p1; linarith
    have d3 : h ^ (2 * ks) ≤ C ^ N * h ^ (2 * ks) := by nlinarith
    have := mul_le_mul_of_nonneg_left (add_le_add d3 d2) hα
    linarith
  have q1 : 0 ≤ C ^ N * (α * (h ^ (2 * ks) + h ^ 2 * h ^ (2 * kt))) := by positivity
  linarith

include E in
/-- **`thm_apriori`, Case C, in the form of the paper**, `eq_apriori_caseC` (squared):
with the convention `‖w‖_∞ ≃ 1` (`hw1`, `hw2`) and `h ≲ 1`,
`|||u - u_h|||² ≲ (h^{2k+1} + α (h^{2k_s} + h^{2k_t+2})) ‖u‖²`, `k = min{k_s, k_t}`.
The constant depends on the polynomial degrees through `C^{6(k_s+k_t)+4}`. -/
theorem apriori_C_paper (hr : S.regime = .C) (hw1 : S.wInf ≤ P.C) (hw2 : 1 ≤ P.C * S.wInf)
    (hlam : P.lam0 Wc.Cφ ≤ P.lam)
    (hsmall : ExpWeight.Ksup P Wc * ExpWeight.Kw P Wc * √S.τ ≤ 1 / 8) :
    S.tn2 (D.ue - D.uh) ≤ ExpWeight.Kst P Wc * (Kap P * ((2 + 4 * P.C + 2 * P.C ^ 2) * Ci
      * (3 * P.C ^ (6 * (D.ks + D.kt) + 4)
        * (S.h * S.h ^ (2 * min D.ks D.kt)
          + S.α * (S.h ^ (2 * D.ks) + S.h ^ 2 * S.h ^ (2 * D.kt)))) * D.U)) := by
  obtain ⟨_, hC2⟩ := S.caseC hr
  have hC := P.C_pos; have hτ := S.τ_pos; have hh := S.h_pos; have hw := S.wInf_nonneg
  have hτh : S.τ ≤ P.C ^ 2 * S.h := by
    have h1 : S.τ ≤ (P.C * S.wInf) * S.τ := by nlinarith
    have h2 : (P.C * S.wInf) * S.τ = P.C * (S.wInf * S.τ) := by ring
    have h3 := mul_le_mul_of_nonneg_left (S.caseC hr).1 hC.le
    nlinarith
  have hrate := rate_C_le (ks := D.ks) (kt := D.kt) P.hC hh S.h_le hτ hτh hw hw1 S.α_nonneg
  have h1 := D.apriori_C E hr hlam hsmall
  have hK : 0 ≤ ExpWeight.Kst P Wc * (Kap P * ((2 + 4 * P.C + 2 * P.C ^ 2) * Ci)) := by
    have := ExpWeight.Msq_pos P Wc; have := P.Kc1_pos; have := P.Kc2_pos
    have := P.hγJ; have := D.hCi
    unfold ExpWeight.Kst Kap; positivity
  have h2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hrate D.hU) hK
  linarith

end ErrorData

end StDgdg
