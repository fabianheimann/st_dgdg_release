import StDgdg.Stability

/-!
# Layer 2, part 8: `thm_stability` in the form of the paper, unique solvability
-/

namespace StDgdg

open Finset Real

variable {P : Consts} {ι X Fs Ts : Type*} [Fintype ι]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Fs] [Module ℝ Fs] [AddCommGroup Ts] [Module ℝ Ts]

namespace Setting

variable (S : Setting P ι X Fs Ts)

/-! ### linearity in the trial function -/

theorem Cb_add_left (u u' v : X) : S.Cb (u + u') v = S.Cb u v + S.Cb u' v := by
  unfold Cb; simp only [map_add, LinearMap.add_apply, sum_add_distrib]
theorem Cb_smul_left (c : ℝ) (u v : X) : S.Cb (c • u) v = c * S.Cb u v := by
  unfold Cb; simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, mul_sum]
theorem Ab_add_left (u u' v : X) : S.Ab (u + u') v = S.Ab u v + S.Ab u' v := by
  unfold Ab; simp only [map_add, LinearMap.add_apply, sum_add_distrib, mul_add]
theorem Ab_smul_left (c : ℝ) (u v : X) : S.Ab (c • u) v = c * S.Ab u v := by
  unfold Ab; simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, ← mul_sum]; ring
theorem Ub_add_left (u u' v : X) : S.Ub (u + u') v = S.Ub u v + S.Ub u' v := by
  unfold Ub; simp only [map_add, LinearMap.add_apply, ← sum_add_distrib]
  refine sum_congr rfl fun n _ => ?_; ring
theorem Ub_smul_left (c : ℝ) (u v : X) : S.Ub (c • u) v = c * S.Ub u v := by
  unfold Ub; simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, mul_sum]
  refine sum_congr rfl fun n _ => ?_; ring
theorem Nb_add_left (u u' v : X) : S.Nb (u + u') v = S.Nb u v + S.Nb u' v := by
  unfold Nb; simp only [map_add, LinearMap.add_apply, ← sum_add_distrib]
  refine sum_congr rfl fun n _ => ?_; ring
theorem Nb_smul_left (c : ℝ) (u v : X) : S.Nb (c • u) v = c * S.Nb u v := by
  unfold Nb; simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, mul_sum]
  refine sum_congr rfl fun n _ => ?_; ring
theorem Jb_add_left (u u' v : X) : S.Jb (u + u') v = S.Jb u v + S.Jb u' v := by
  unfold Jb; simp only [map_add, LinearMap.add_apply, sum_add_distrib, mul_add]
theorem Jb_smul_left (c : ℝ) (u v : X) : S.Jb (c • u) v = c * S.Jb u v := by
  unfold Jb; simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, ← mul_sum]; ring
theorem BJ_add_left (u u' v : X) : S.BJ (u + u') v = S.BJ u v + S.BJ u' v := by
  unfold BJ; rw [Cb_add_left, Ub_add_left, Ab_add_left, Nb_add_left, Jb_add_left]; ring
theorem BJ_smul_left (c : ℝ) (u v : X) : S.BJ (c • u) v = c * S.BJ u v := by
  unfold BJ; rw [Cb_smul_left, Ub_smul_left, Ab_smul_left, Nb_smul_left, Jb_smul_left]; ring

/-- `B_h + J` as a bilinear form on `W_h`. -/
noncomputable def BJlin : S.Wh →ₗ[ℝ] S.Wh →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u v => S.BJ (u : X) (v : X))
    (fun u u' v => by simp only [Submodule.coe_add]; exact S.BJ_add_left _ _ _)
    (fun c u v => by simp only [Submodule.coe_smul, smul_eq_mul]; exact S.BJ_smul_left _ _ _)
    (fun u v v' => by simp only [Submodule.coe_add]; exact S.BJ_add _ _ _)
    (fun c u v => by simp only [Submodule.coe_smul, smul_eq_mul]; exact S.BJ_smul _ _ _)

end Setting

namespace ExpWeight

variable {S : Setting P ι X Fs Ts} {Wc : WConsts} (E : ExpWeight S Wc)

theorem Msq_pos (P : Consts) (Wc : WConsts) : 0 < Msq P Wc := by
  have hC := P.C_pos
  have h1 := Ktw_nonneg P Wc
  have h2 : 0 < P.Kty := by
    have := P.KL_nonneg; have := P.Kg_nonneg; have := P.Ky1_nonneg; have := P.KLJ_nonneg
    have hKL : 0 < P.KL := by
      have := P.hγJ; have := P.Kq_nonneg; unfold Consts.KL; positivity
    unfold Consts.Kty; positivity
  unfold Msq; positivity

include E in
/-- **Inf-sup stability, `thm_stability`, `eq_inf_sup`** (product form):
`(B_h + J)(u, ṽ(u)) ≥ C_stab |||u|||_j |||ṽ(u)|||_j` with `C_stab = 1 / (8 M)`, where
`ṽ(u) ≠ 0` whenever `|||u|||_j ≠ 0`. Without the latter the statement would be void, as
`ṽ(u) = 0` satisfies the inequality; the two-part form `inf_sup` (`eq_inf_sup_two`) is the
stronger statement and the one used in the sequel. -/
theorem inf_sup_product (hlam : P.lam0 Wc.Cφ ≤ P.lam)
    (hsmall : Ksup P Wc * Kw P Wc * √S.τ ≤ 1 / 8) {u : X} (hu : u ∈ S.Wh) :
    ∃ v ∈ S.Wh, (S.tnj2 u ≠ 0 → v ≠ 0) ∧
      1 / (8 * √(Msq P Wc)) * (√(S.tnj2 u) * √(S.tnj2 v)) ≤ S.BJ u v := by
  obtain ⟨v, hv, h1, h2⟩ := E.inf_sup hlam hsmall hu
  have hu0 := S.tnj2_nonneg u
  refine ⟨v, hv, fun hne hv0 => ?_, le_trans ?_ h2⟩
  · -- `(B_h + J)(u, 0) = 0`, but `(B_h + J)(u, v) ≥ ⅛ |||u|||_j² > 0`
    have hB : S.BJ u v = 0 := by
      have := S.BJ_smul 0 u v
      rw [hv0] at this ⊢
      simpa using this
    have hpos : 0 < S.tnj2 u := lt_of_le_of_ne hu0 (Ne.symm hne)
    linarith
  have hM := Msq_pos P Wc
  have hsM : 0 < √(Msq P Wc) := Real.sqrt_pos.2 hM
  have h3 : √(S.tnj2 v) ≤ √(Msq P Wc) * √(S.tnj2 u) := by
    rw [← Real.sqrt_mul hM.le]; exact Real.sqrt_le_sqrt h1
  have h4 : √(S.tnj2 u) * √(S.tnj2 u) = S.tnj2 u := Real.mul_self_sqrt hu0
  calc 1 / (8 * √(Msq P Wc)) * (√(S.tnj2 u) * √(S.tnj2 v))
      ≤ 1 / (8 * √(Msq P Wc)) * (√(S.tnj2 u) * (√(Msq P Wc) * √(S.tnj2 u))) := by gcongr
    _ = 1 / 8 * (√(S.tnj2 u) * √(S.tnj2 u)) := by field_simp
    _ = 1 / 8 * S.tnj2 u := by rw [h4]

include E in
/-- **Unique solvability of the discrete problem** (last claim of `thm_stability`).
`hdef` states that `‖·‖_{𝒬_T}` is a norm on `W_h`. -/
theorem unique_solvability [FiniteDimensional ℝ S.Wh] (hlam : P.lam0 Wc.Cφ ≤ P.lam)
    (hsmall : Ksup P Wc * Kw P Wc * √S.τ ≤ 1 / 8)
    (hdef : ∀ u ∈ S.Wh, S.nQT u = 0 → u = 0) (f : S.Wh →ₗ[ℝ] ℝ) :
    ∃! u : S.Wh, ∀ v : S.Wh, S.BJ (u : X) (v : X) = f v := by
  refine existsUnique_of_ker_trivial S.BJlin (fun u hu => ?_) f
  obtain ⟨v, hv, _, hB⟩ := E.inf_sup hlam hsmall u.2
  have h0 : S.BJ (u : X) v = 0 := hu ⟨v, hv⟩
  have ht : S.tnj2 (u : X) ≤ 0 := by linarith
  have hcj : S.cj2 (u : X) ≤ 0 := (S.cj2_le_tnj2 _).trans ht
  have hq := S.nQT_le_cj2 u.2
  have hq' : S.nQT (u : X) ≤ 0 := by
    have := mul_le_mul_of_nonneg_left hcj P.Kq_nonneg
    linarith
  exact Subtype.ext (hdef u u.2 (le_antisymm hq' (S.nQT_nonneg _)))

end ExpWeight

end StDgdg
