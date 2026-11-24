import StDgdg.Solvability

/-!
# Sanity check: the assumptions are not contradictory

A trivial model (all operators and inner products zero) of `Setting` and `ExpWeight`.
This only shows that the list of assumptions in `Setting.lean` is consistent; it says
nothing about whether the assumptions hold for the actual method (that is "Layer 3").
-/

namespace StDgdg

/-- A trivial model of the setting, for any admissible constants. -/
noncomputable def trivialSetting (P : Consts) : Setting P Unit ℝ ℝ ℝ where
  regime := .D
  N := 0
  h := 1
  τ := 1
  α := 1
  wInf := 0
  h_pos := one_pos
  τ_pos := one_pos
  τ_le_one := le_refl _
  h_le := P.hC
  α_nonneg := zero_le_one
  wInf_nonneg := le_refl _
  caseD := fun _ => by have := P.hC; constructor <;> norm_num <;> linarith
  caseC := fun h => by cases h
  Wh := ⊤
  Ws := ⊤
  Wh_le_Ws := le_refl _
  dt := 0
  dx := fun _ => 0
  mat := 0
  Lc := 0
  Lh := 0
  up := 0
  dn := 0
  nfl := 0
  bot := fun _ => 0
  top := fun _ => 0
  dx_mem := fun _ _ _ => trivial
  Lh_mem := fun _ _ => trivial
  Q := fun _ => SemiIP.zero ℝ
  QT := fun _ => SemiIP.zero ℝ
  j := fun _ => SemiIP.zero ℝ
  FQ := fun _ => SemiIP.zero ℝ
  FQw := fun _ => SemiIP.zero ℝ
  Fgp := fun _ => SemiIP.zero ℝ
  Fint := fun _ => SemiIP.zero ℝ
  Om := fun _ => SemiIP.zero ℝ
  Q_le_QT := by simp [SemiIP.zero]
  FQ_le := by simp [SemiIP.zero]
  Fint_le_FQ := by simp [SemiIP.zero]
  FQw_le := by simp [SemiIP.zero]
  trace_up := by simp [SemiIP.zero]
  trace_dn := by simp [SemiIP.zero]
  trace_nfl := by simp [SemiIP.zero]
  trace_time := by simp [SemiIP.zero]
  trace_time_cont := by simp [SemiIP.zero]
  inv_dx := by simp [SemiIP.zero]
  trace_up_cont := by simp [SemiIP.zero]
  gp := by simp [SemiIP.zero]
  gp_inv_dx := by simp [SemiIP.zero]
  gp_facet := by simp [SemiIP.zero]
  Lc_Lh := by simp [SemiIP.zero]
  Lh_inv_grad := by simp [SemiIP.zero]
  Lh_gp := by simp [SemiIP.zero]
  Lh_int_jump := by simp [SemiIP.zero]
  Lc_inv := by simp [SemiIP.zero]
  mat_dt := by simp [SemiIP.zero]
  Lc_dt := by simp [SemiIP.zero]
  mat_Lc := fun _ => rfl
  ibp := by simp [SemiIP.zero]

/-- A trivial model of the exponential weight. -/
noncomputable def trivialExpWeight (P : Consts) (Wc : WConsts) (hc0 : 0 < Wc.c0)
    (hc1 : Wc.c0 ≤ 1) : ExpWeight (trivialSetting P) Wc where
  M := 0
  Mf := 0
  lo := fun _ => 1
  hi := fun _ => 1
  phi := fun _ => 1
  σ_nonneg := Wc.hσ.le
  c0_pos := hc0
  Cφ_nonneg := le_trans zero_le_one Wc.hCφ
  c0_le_lo := fun _ _ => hc1
  hi_le := fun _ _ => by have := Wc.hCφ; linarith
  c0_le_phi := fun _ _ => hc1
  phi_le_one := fun _ _ => le_refl _
  dx_M := by simp [trivialSetting]
  up_M := by simp [trivialSetting]
  dn_M := by simp [trivialSetting]
  nfl_M := by simp [trivialSetting]
  bot_M := by simp [trivialSetting]
  top_M := by simp [trivialSetting]
  mat_M := by simp [trivialSetting]
  Lc_M := by simp [trivialSetting]
  Q_symm := by simp [trivialSetting, SemiIP.zero]
  j_symm := by simp [trivialSetting, SemiIP.zero]
  FQ_symm := by simp [trivialSetting, SemiIP.zero]
  FQw_symm := by simp [trivialSetting, SemiIP.zero]
  Q_lo := by simp [trivialSetting, SemiIP.zero]
  j_lo := by simp [trivialSetting, SemiIP.zero]
  FQ_lo := by simp [trivialSetting, SemiIP.zero]
  FQw_lo := by simp [trivialSetting, SemiIP.zero]
  FQ_hi := by simp [trivialSetting, SemiIP.zero]
  Q_contr := by simp [trivialSetting, SemiIP.zero]
  j_contr := by simp [trivialSetting, SemiIP.zero]
  FQ_contr := by simp [trivialSetting, SemiIP.zero]
  FQw_contr := by simp [trivialSetting, SemiIP.zero]
  Pw := 0
  Pw_mem := fun _ _ => trivial
  r_mem := fun _ _ => trivial
  r_dx := by simp [trivialSetting]
  superapprox := by simp [trivialSetting, SemiIP.zero]
  superapprox_dt := by simp [trivialSetting, SemiIP.zero]
  superapprox_gp := by simp [trivialSetting, SemiIP.zero]
  superapprox_int := by simp [trivialSetting, SemiIP.zero]
  superapprox_j := by simp [trivialSetting, SemiIP.zero]

end StDgdg
