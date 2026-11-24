import StDgdg.Solvability

/-!
# Layer 2, part 9: `lemma_B_Bmc`, `lemma_continuity`, `prop_strang`
-/

namespace StDgdg

open Finset Real

variable {P : Consts} {ι X Fs Ts : Type*} [Fintype ι]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Fs] [Module ℝ Fs] [AddCommGroup Ts] [Module ℝ Ts]

namespace Setting

variable (S : Setting P ι X Fs Ts)

/-! ### `lemma_B_Bmc` -/

/-- **`lemma_B_Bmc`, `eq_B_Bmc`** (mass conserving form):
`(C + U_h)(u,v) = -(u, w^*·∇^* v)_Q - (|w·n| u_-, [v])_{𝒬_F∩Q} - ∑_n (u_-, [v])_{Ω^n}
  + (u_-, v_-)_{Ω^N}`. -/
theorem CU_mc (u v : X) :
    S.Cb u v + S.Ub u v
      = -(∑ n ∈ range S.N, S.Q n u (S.mat v))
        - ∑ n ∈ range S.N, S.FQw n (S.up u) (S.jmp v)
        - ∑ n ∈ range S.N, S.Om n (S.prev n u) (S.tjump n v)
        + S.Om S.N (S.prev S.N u) (S.prev S.N v) := by
  have slab : ∀ n, n < S.N → S.Q n (S.mat u) v
      + (S.FQw n (S.jmp u) (S.dn v) + S.Om n (S.tjump n u) (S.bot n v))
      = -(S.Q n u (S.mat v)) - S.FQw n (S.up u) (S.jmp v)
        - S.Om n (S.prev n u) (S.tjump n v)
        + (S.Om (n + 1) (S.top n u) (S.top n v) - S.Om n (S.prev n u) (S.prev n v)) := by
    intro n hn
    have h := S.ibp n hn u v
    simp only [jmp, tjump, LinearMap.sub_apply, map_sub]
    linear_combination h
  unfold Cb Ub
  rw [← sum_add_distrib, sum_congr rfl (fun n hn => slab n (mem_range.1 hn))]
  rw [sum_add_distrib, sum_sub_distrib, sum_sub_distrib, sum_neg_distrib]
  have ht := sum_range_sub (fun k => S.Om k (S.prev k u) (S.prev k v)) S.N
  have h0 : S.prev 0 u = 0 := rfl
  have hs : ∀ n, S.prev (n + 1) = S.top n := fun n => rfl
  simp only [h0, hs, map_zero, LinearMap.zero_apply, sub_zero] at ht
  rw [ht]

theorem sum_prev_eq (v : X) :
    ∑ n ∈ range S.N, S.Om n (S.prev n v) (S.prev n v) + S.Om S.N (S.prev S.N v) (S.prev S.N v)
      = S.TT v := by
  have hp2 := sum_range_succ (fun k => S.Om k (S.prev k v) (S.prev k v)) S.N
  beta_reduce at hp2
  rw [← hp2, sum_range_succ']
  simp [prev, TT]

theorem upw_time_le (v : X) :
    ∑ n ∈ range S.N, S.Om n (S.tjump n v) (S.tjump n v) + S.Om S.N (S.prev S.N v) (S.prev S.N v)
      ≤ S.upw2 v := by
  unfold upw2
  have h1 : ∑ n ∈ range S.N, S.Om n (S.tjump n v) (S.tjump n v)
      ≤ ∑ n ∈ range S.N, (S.Om n (S.tjump n v) (S.tjump n v)
        + S.FQw n (S.jmp v) (S.jmp v)) :=
    sum_le_sum fun n _ => by have := (S.FQw n).nonneg (S.jmp v); linarith
  linarith

theorem TT_nonneg (v : X) : 0 ≤ S.TT v := sum_nonneg fun n _ => (S.Om _).nonneg _
theorem FU_nonneg (v : X) : 0 ≤ S.FU v := sum_nonneg fun n _ => (S.FQ _).nonneg _
theorem FN_nonneg (v : X) : 0 ≤ S.FN v := sum_nonneg fun n _ => (S.FQ _).nonneg _
theorem tn2_nonneg (v : X) : 0 ≤ S.tn2 v := add_nonneg (S.L2_nonneg v) (S.c2_nonneg v)
theorem tn2_le_tnj2 (v : X) : S.tn2 v ≤ S.tnj2 v := by
  have := S.J2_nonneg v; unfold tn2 tnj2 cj2; linarith
theorem tn2_le_tnstar2 (v : X) : S.tn2 v ≤ S.tnstar2 v := by
  have h1 := S.nQ_nonneg v; have h2 := S.TT_nonneg v; have h3 := S.FU_nonneg v
  have h4 := S.FN_nonneg v; have := S.τinv_pos; have := S.h_pos; have := S.α_nonneg
  have p1 : 0 ≤ S.τ⁻¹ * S.nQ v := by positivity
  have p2 : 0 ≤ S.h * S.τ⁻¹ * S.FU v := by positivity
  have p3 : 0 ≤ S.α * (S.h * S.FN v) := by positivity
  unfold tnstar2; linarith

/-! ### `lemma_continuity` (in Young form) -/

/-- convective volume term of `B_mc` -/
theorem cont_C (x v : X) {s : ℝ} (hs : 0 < s) :
    -(2 * ∑ n ∈ range S.N, S.Q n x (S.mat v))
      ≤ s * (S.τ⁻¹ * S.nQ x) + s⁻¹ * ((2 + 8 * P.C) * S.tnj2 v) := by
  have hτ := S.τ_pos; have hτi := S.τinv_pos; have hC := P.C_pos
  have Y := SemiIP.sum_young (range S.N) S.Q (fun _ => x) (fun _ => S.mat v) (mul_pos hs hτi)
  beta_reduce at Y
  have f1 := S.τ_nQ_mat_le v
  have f2 := ((S.αgQ_le_c2 v).trans (S.c2_le_cj2 v)).trans (S.cj2_le_tnj2 v)
  have f3 := S.L2_le_tnj2 v
  have g : S.τ * S.nQ (S.mat v) ≤ (2 + 8 * P.C) * S.tnj2 v := by
    have := mul_le_mul_of_nonneg_left f2 (by positivity : 0 ≤ 8 * P.C)
    linarith
  have e : (s * S.τ⁻¹)⁻¹ * S.nQ (S.mat v) = s⁻¹ * (S.τ * S.nQ (S.mat v)) := by field_simp
  have g' := mul_le_mul_of_nonneg_left g (inv_pos.2 hs).le
  unfold nQ at e g' ⊢
  rw [e] at Y
  linarith

/-- spatial upwind term of `B_mc` (Case C: `‖w‖_∞ ≲ h/Δt`; Case D:
`‖w‖_∞² h / α ≲ h/Δt`) -/
theorem cont_U_facet (x v : X) {s : ℝ} (hs : 0 < s) :
    -(2 * ∑ n ∈ range S.N, S.FQw n (S.up x) (S.jmp v))
      ≤ s * (P.C * (S.h * S.τ⁻¹ * S.FU x)) + s⁻¹ * S.c2 v := by
  have hτ := S.τ_pos; have hC := P.C_pos; have hτi := S.τinv_pos
  have hh := S.h_pos; have hhi := S.hinv_pos
  have hw := S.wInf_nonneg; have hsi := inv_pos.2 hs
  have hc2 := S.c2_nonneg v; have hFU := S.FU_nonneg x
  have A1 : ∑ n ∈ range S.N, S.FQw n (S.up x) (S.up x) ≤ S.wInf * S.FU x := by
    unfold FU
    exact sum_le_mul_sum fun n _ => S.FQw_le n (by in_range) _
  have B1 : ∑ n ∈ range S.N, S.FQw n (S.jmp v) (S.jmp v) ≤ S.wInf * S.jQ v := by
    unfold jQ
    exact sum_le_mul_sum fun n _ => S.FQw_le n (by in_range) _
  have B2 : ∑ n ∈ range S.N, S.FQw n (S.jmp v) (S.jmp v) ≤ S.c2 v := by
    refine le_trans ?_ (S.upw2_le_c2 v)
    unfold upw2
    have h1 : ∑ n ∈ range S.N, S.FQw n (S.jmp v) (S.jmp v)
        ≤ ∑ n ∈ range S.N, (S.Om n (S.tjump n v) (S.tjump n v)
          + S.FQw n (S.jmp v) (S.jmp v)) :=
      sum_le_sum fun n _ => by have := (S.Om n).nonneg (S.tjump n v); linarith
    have := (S.Om S.N).nonneg (S.prev S.N v)
    linarith
  have f3 := S.αjQ_le_c2 v
  cases hr : S.regime with
  | C =>
    obtain ⟨hc1, _⟩ := S.caseC hr
    have Y := SemiIP.sum_young (range S.N) S.FQw (fun _ => S.up x) (fun _ => S.jmp v) hs
    beta_reduce at Y
    have a : s * ∑ n ∈ range S.N, S.FQw n (S.up x) (S.up x)
        ≤ s * (P.C * (S.h * S.τ⁻¹ * S.FU x)) := by
      refine mul_le_mul_of_nonneg_left (A1.trans ?_) hs.le
      calc S.wInf * S.FU x = (S.wInf * S.τ) * (S.τ⁻¹ * S.FU x) := by field_simp
        _ ≤ (P.C * S.h) * (S.τ⁻¹ * S.FU x) := by gcongr
        _ = P.C * (S.h * S.τ⁻¹ * S.FU x) := by ring
    have b := mul_le_mul_of_nonneg_left B2 hsi.le
    linarith
  | D =>
    obtain ⟨hD1, hD2⟩ := S.caseD hr
    rcases eq_or_lt_of_le hw with hw0 | hwpos
    · have Y := SemiIP.sum_young (range S.N) S.FQw (fun _ => S.up x) (fun _ => S.jmp v) one_pos
      beta_reduce at Y
      rw [← hw0] at A1 B1
      have : 0 ≤ s * (P.C * (S.h * S.τ⁻¹ * S.FU x)) + s⁻¹ * S.c2 v := by positivity
      simp only [zero_mul, inv_one, one_mul] at A1 B1 Y
      linarith
    · have hα : 0 < S.α := by
        rcases eq_or_lt_of_le S.α_nonneg with h0 | hpos
        · rw [← h0] at hD1; nlinarith
        · exact hpos
      have hs' : 0 < s * S.wInf * S.h / S.α := by positivity
      have Y := SemiIP.sum_young (range S.N) S.FQw (fun _ => S.up x) (fun _ => S.jmp v) hs'
      beta_reduce at Y
      have hratio : S.wInf ^ 2 * S.τ * S.α⁻¹ ≤ P.C :=
        calc S.wInf ^ 2 * S.τ * S.α⁻¹ ≤ P.C * S.α * S.α⁻¹ := by gcongr
          _ = P.C := by field_simp
      have a : s * S.wInf * S.h / S.α * ∑ n ∈ range S.N, S.FQw n (S.up x) (S.up x)
          ≤ s * (P.C * (S.h * S.τ⁻¹ * S.FU x)) :=
        calc s * S.wInf * S.h / S.α * ∑ n ∈ range S.N, S.FQw n (S.up x) (S.up x)
            ≤ s * S.wInf * S.h / S.α * (S.wInf * S.FU x) :=
              mul_le_mul_of_nonneg_left A1 hs'.le
          _ = s * ((S.wInf ^ 2 * S.τ * S.α⁻¹) * (S.h * S.τ⁻¹ * S.FU x)) := by field_simp
          _ ≤ s * (P.C * (S.h * S.τ⁻¹ * S.FU x)) := by gcongr
      have b : (s * S.wInf * S.h / S.α)⁻¹ * ∑ n ∈ range S.N, S.FQw n (S.jmp v) (S.jmp v)
          ≤ s⁻¹ * S.c2 v :=
        calc (s * S.wInf * S.h / S.α)⁻¹ * ∑ n ∈ range S.N, S.FQw n (S.jmp v) (S.jmp v)
            ≤ (s * S.wInf * S.h / S.α)⁻¹ * (S.wInf * S.jQ v) :=
              mul_le_mul_of_nonneg_left B1 (by positivity)
          _ = s⁻¹ * (S.α * (S.h⁻¹ * S.jQ v)) := by field_simp
          _ ≤ s⁻¹ * S.c2 v := by gcongr
      linarith

/-- temporal terms of `B_mc` -/
theorem cont_U_time (x v : X) {s : ℝ} (hs : 0 < s) :
    -(2 * ∑ n ∈ range S.N, S.Om n (S.prev n x) (S.tjump n v))
        + 2 * S.Om S.N (S.prev S.N x) (S.prev S.N v)
      ≤ s * S.TT x + s⁻¹ * S.upw2 v := by
  have hsi := inv_pos.2 hs
  have Y3 := SemiIP.sum_young (range S.N) S.Om (fun n => S.prev n x) (fun n => S.tjump n v) hs
  beta_reduce at Y3
  have Y4 := (S.Om S.N).young_le hs (S.prev S.N x) (S.prev S.N v)
  have a := S.sum_prev_eq x
  have b := mul_le_mul_of_nonneg_left (S.upw_time_le v) hsi.le
  have a' : s * S.TT x = s * ∑ n ∈ range S.N, S.Om n (S.prev n x) (S.prev n x)
      + s * S.Om S.N (S.prev S.N x) (S.prev S.N x) := by rw [← a]; ring
  linarith

/-- diffusion volume term -/
theorem cont_A (x v : X) {s : ℝ} (hs : 0 < s) :
    2 * S.Ab x v ≤ s * (S.α * S.gQ x) + s⁻¹ * (S.α * S.gQ v) := by
  have hα := S.α_nonneg
  have Y : 2 * ∑ n ∈ range S.N, ∑ i, S.Q n (S.dx i x) (S.dx i v)
      ≤ s * S.gQ x + s⁻¹ * S.gQ v := by
    unfold gQ gQs
    rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_le_sum fun n _ => ?_
    exact SemiIP.sum_young_le univ (fun _ => S.Q n) (fun i => S.dx i x) (fun i => S.dx i v) hs
  have Y' := mul_le_mul_of_nonneg_left Y hα
  unfold Ab
  linarith

/-- Nitsche terms -/
theorem cont_N (x : X) {v : X} (hv : v ∈ S.Wh) {s : ℝ} (hs : 0 < s) :
    2 * S.Nb x v ≤ s * (S.α * (S.h * S.FN x) + (1 + P.lam) * (S.α * (S.h⁻¹ * S.jQ x)))
      + s⁻¹ * ((1 + P.lam) * (S.α * (S.h⁻¹ * S.jQ v)) + P.C * P.Kg * S.cj2 v) := by
  have hα := S.α_nonneg; have hh := S.h_pos; have hhi := S.hinv_pos; have hC := P.C_pos
  have hlam := P.hlam; have hsi := inv_pos.2 hs
  have Y1 := SemiIP.sum_young_le (range S.N) S.FQ (fun _ => S.nfl x) (fun _ => S.jmp v)
    (mul_pos hs hh)
  have Y2 := SemiIP.sum_young_le (range S.N) S.FQ (fun _ => S.nfl v) (fun _ => S.jmp x)
    (mul_pos hsi hh)
  have Y3 := SemiIP.sum_young_le (range S.N) S.FQ (fun _ => S.jmp x) (fun _ => S.jmp v) hs
  beta_reduce at Y1 Y2 Y3
  have n2 := S.FQ_nfl_le (S.Wh_le_Ws hv)
  have g := S.α_gQT_le_cj2 hv
  have e1 : S.α * ((s * S.h)⁻¹ * S.jQ v) = s⁻¹ * (S.α * (S.h⁻¹ * S.jQ v)) := by field_simp
  have e1' : S.α * (s * S.h * S.FN x) = s * (S.α * (S.h * S.FN x)) := by ring
  have t2a : S.α * (s⁻¹ * S.h * ∑ n ∈ range S.N, S.FQ n (S.nfl v) (S.nfl v))
      ≤ s⁻¹ * (P.C * P.Kg * S.cj2 v) :=
    calc S.α * (s⁻¹ * S.h * ∑ n ∈ range S.N, S.FQ n (S.nfl v) (S.nfl v))
        ≤ S.α * (s⁻¹ * S.h * (P.C * S.h⁻¹ * S.gQT v)) := by gcongr
      _ = s⁻¹ * (P.C * (S.α * S.gQT v)) := by field_simp
      _ ≤ s⁻¹ * (P.C * (P.Kg * S.cj2 v)) := by gcongr
      _ = s⁻¹ * (P.C * P.Kg * S.cj2 v) := by ring
  have e2 : S.α * ((s⁻¹ * S.h)⁻¹ * S.jQ x) = s * (S.α * (S.h⁻¹ * S.jQ x)) := by field_simp
  have Y1' := mul_le_mul_of_nonneg_left Y1 hα
  have Y2' := mul_le_mul_of_nonneg_left Y2 hα
  have Y3' := mul_le_mul_of_nonneg_left Y3 (by positivity : 0 ≤ S.α * P.lam * S.h⁻¹)
  have eN : S.Nb x v
      = S.α * ∑ n ∈ range S.N, S.FQ n (S.nfl x) (S.jmp v)
        + S.α * ∑ n ∈ range S.N, S.FQ n (S.nfl v) (S.jmp x)
        + S.α * P.lam * S.h⁻¹ * ∑ n ∈ range S.N, S.FQ n (S.jmp x) (S.jmp v) := by
    unfold Nb
    simp only [sum_add_distrib, mul_sum]
  unfold jQ FN at *
  rw [eN]
  linarith

/-- Constants of `lemma_continuity`. -/
noncomputable def _root_.StDgdg.Consts.Kc1 (P : Consts) : ℝ := P.C + 2 + P.lam
noncomputable def _root_.StDgdg.Consts.Kc2 (P : Consts) : ℝ :=
  6 + 8 * P.C + P.C * P.Kg + P.lam

theorem _root_.StDgdg.Consts.Kc1_pos (P : Consts) : 0 < P.Kc1 := by
  have := P.C_pos; have := P.hlam; unfold Consts.Kc1; positivity
theorem _root_.StDgdg.Consts.Kc2_pos (P : Consts) : 0 < P.Kc2 := by
  have := P.C_pos; have := P.hlam; have := P.Kg_nonneg; unfold Consts.Kc2; positivity

/-- **`lemma_continuity`** in Young form: for all `x` (in `W_h + H²(Q)`), `v ∈ W_h`, `s > 0`,
`2 B_h(x,v) ≤ s C₁ |||x|||_*² + s⁻¹ C₂ |||v|||_j²`
(equivalent to `B_h(x,v) ≤ (C₁C₂)^{1/2} |||x|||_* |||v|||_j`). -/
theorem continuity (x : X) {v : X} (hv : v ∈ S.Wh) {s : ℝ} (hs : 0 < s) :
    2 * S.Bh x v ≤ s * (P.Kc1 * S.tnstar2 x) + s⁻¹ * (P.Kc2 * S.tnj2 v) := by
  have hC := P.C_pos; have hlam := P.hlam; have hKg := P.Kg_nonneg
  have hsi := inv_pos.2 hs
  have hα := S.α_nonneg; have hh := S.h_pos; have hhi := S.hinv_pos; have hτi := S.τinv_pos
  have c1 := S.cont_C x v hs
  have c2 := S.cont_U_facet x v hs
  have c3 := S.cont_U_time x v hs
  have c4 := S.cont_A x v hs
  have c5 := S.cont_N x hv hs
  have hmc := S.CU_mc x v
  -- the `x` side
  have px1 := S.L2_nonneg x; have px2 := S.c2_nonneg x; have px3 := S.nQ_nonneg x
  have px4 := S.TT_nonneg x; have px5 := S.FU_nonneg x; have px6 := S.FN_nonneg x
  have ax1 := S.αgQ_le_c2 x; have ax2 := S.αjQ_le_c2 x
  have q3 : 0 ≤ S.τ⁻¹ * S.nQ x := by positivity
  have q5 : 0 ≤ S.h * S.τ⁻¹ * S.FU x := by positivity
  have q6 : 0 ≤ S.α * (S.h * S.FN x) := by positivity
  have hx : S.τ⁻¹ * S.nQ x + P.C * (S.h * S.τ⁻¹ * S.FU x) + S.TT x + S.α * S.gQ x
      + (S.α * (S.h * S.FN x) + (1 + P.lam) * (S.α * (S.h⁻¹ * S.jQ x)))
      ≤ P.Kc1 * S.tnstar2 x := by
    have m1 := mul_le_mul_of_nonneg_left ax2 hlam.le
    have r1 : 0 ≤ P.C * S.L2 x := by positivity
    have r2 : 0 ≤ P.C * S.c2 x := by positivity
    have r3 : 0 ≤ P.C * (S.τ⁻¹ * S.nQ x) := by positivity
    have r4 : 0 ≤ P.C * S.TT x := by positivity
    have r6 : 0 ≤ P.C * (S.α * (S.h * S.FN x)) := by positivity
    have l1 : 0 ≤ P.lam * S.L2 x := by positivity
    have l3 : 0 ≤ P.lam * (S.τ⁻¹ * S.nQ x) := by positivity
    have l4 : 0 ≤ P.lam * S.TT x := by positivity
    have l5 : 0 ≤ P.lam * (S.h * S.τ⁻¹ * S.FU x) := by positivity
    have l6 : 0 ≤ P.lam * (S.α * (S.h * S.FN x)) := by positivity
    unfold Consts.Kc1 tnstar2 tn2
    linarith
  -- the `v` side
  have bv1 := S.c2_le_cj2 v; have bv2 := S.cj2_le_tnj2 v
  have av1 := S.αgQ_le_c2 v; have av2 := S.αjQ_le_c2 v; have av3 := S.upw2_le_c2 v
  have ht := S.tnj2_nonneg v
  have hv' : (2 + 8 * P.C) * S.tnj2 v + S.c2 v + S.upw2 v + S.α * S.gQ v
      + ((1 + P.lam) * (S.α * (S.h⁻¹ * S.jQ v)) + P.C * P.Kg * S.cj2 v)
      ≤ P.Kc2 * S.tnj2 v := by
    have m1 := mul_le_mul_of_nonneg_left (av2.trans (bv1.trans bv2)) hlam.le
    have m2 := mul_le_mul_of_nonneg_left bv2 (by positivity : 0 ≤ P.C * P.Kg)
    unfold Consts.Kc2
    linarith
  have X1 := mul_le_mul_of_nonneg_left hx hs.le
  have X2 := mul_le_mul_of_nonneg_left hv' hsi.le
  unfold Bh
  linarith

/-! ### `prop_strang` -/

theorem Bh_sub_left (u u' v : X) : S.Bh (u - u') v = S.Bh u v - S.Bh u' v := by
  have e : u - u' = u + (-1 : ℝ) • u' := by simp [sub_eq_add_neg]
  unfold Bh
  rw [e, Cb_add_left, Ub_add_left, Ab_add_left, Nb_add_left, Cb_smul_left, Ub_smul_left,
    Ab_smul_left, Nb_smul_left]
  ring

theorem BJ_sub_left (u u' v : X) : S.BJ (u - u') v = S.BJ u v - S.BJ u' v := by
  have e : u - u' = u + (-1 : ℝ) • u' := by simp [sub_eq_add_neg]
  rw [e, BJ_add_left, BJ_smul_left]; ring

theorem tn2_sub_le (x y : X) : S.tn2 (x - y) ≤ 2 * S.tn2 x + 2 * S.tn2 y := by
  have hα := S.α_nonneg; have hhi := S.hinv_pos; have hτ := S.τ_pos
  have e : x - y = x + (-1 : ℝ) • y := by simp [sub_eq_add_neg]
  have h1 : S.L2 (x - y) ≤ 2 * S.L2 x + 2 * S.L2 y := by
    unfold L2
    have hL : S.Lc ((-1 : ℝ) • y) = (-1 : ℝ) • S.Lc y := map_smul _ _ _
    have := mul_le_mul_of_nonneg_left (S.nQ_add_le (S.Lc x) ((-1 : ℝ) • S.Lc y)) hτ.le
    rw [nQ_smul] at this
    rw [e, map_add, hL]
    linarith
  have h2 := S.nQ_add_le x ((-1 : ℝ) • y)
  have h3 := mul_le_mul_of_nonneg_left (S.gQ_add_le x ((-1 : ℝ) • y)) hα
  have h4 := mul_le_mul_of_nonneg_left (S.jQ_add_le x ((-1 : ℝ) • y))
    (by positivity : 0 ≤ S.α * S.h⁻¹)
  have h5 := S.upw2_add_le x ((-1 : ℝ) • y)
  rw [← e] at h2 h3 h4 h5
  rw [nQ_smul] at h2
  rw [gQ_smul] at h3
  rw [jQ_smul] at h4
  rw [upw2_smul] at h5
  unfold tn2 c2
  linarith

end Setting

namespace ExpWeight

variable {S : Setting P ι X Fs Ts} {Wc : WConsts} (E : ExpWeight S Wc)

/-- Constant of `prop_strang` (squared). -/
noncomputable def Kst (P : Consts) (Wc : WConsts) : ℝ :=
  2 + 128 * (P.Kc2 + 1) * Msq P Wc * (P.Kc1 + 1)

include E in
/-- **`prop_strang`** (squared):
`|||u - u_h|||² ≲ |||u - w_h|||_*² + |w_h|_J²` for every `w_h ∈ W_h`, if `u` is consistent
(`B_h(u,v) = f_h(v)`) and `u_h` solves the discrete problem. -/
theorem strang (hlam : P.lam0 Wc.Cφ ≤ P.lam)
    (hsmall : Ksup P Wc * Kw P Wc * √S.τ ≤ 1 / 8)
    {u uh wh : X} (huh : uh ∈ S.Wh) (hwh : wh ∈ S.Wh) (f : X → ℝ)
    (hcons : ∀ v, v ∈ S.Wh → S.Bh u v = f v) (hdisc : ∀ v, v ∈ S.Wh → S.BJ uh v = f v) :
    S.tn2 (u - uh) ≤ Kst P Wc * (S.tnstar2 (u - wh) + S.J2 wh) := by
  have hM := Msq_pos P Wc; have hK1 := P.Kc1_pos; have hK2 := P.Kc2_pos
  set e : X := uh - wh with he
  have heW : e ∈ S.Wh := S.Wh.sub_mem huh hwh
  obtain ⟨v, hv, hv1, hv2⟩ := E.inf_sup hlam hsmall heW
  set T : ℝ := S.tnstar2 (u - wh) with hT
  have hT0 : 0 ≤ T := (S.tn2_nonneg _).trans (S.tn2_le_tnstar2 _)
  have hJ0 := S.J2_nonneg wh
  have hte := S.tnj2_nonneg e; have htv := S.tnj2_nonneg v
  -- error equation
  have herr : S.BJ e v = S.Bh (u - wh) v - S.Jb wh v := by
    rw [he, S.BJ_sub_left, S.Bh_sub_left, hdisc v hv, hcons v hv]
    unfold Setting.BJ Setting.Bh; ring
  -- continuity with `s = 8 (C₂ + 1) M`
  have hs : 0 < 8 * (P.Kc2 + 1) * Msq P Wc := by positivity
  have c1 := S.continuity (u - wh) hv hs
  have c2 : -(2 * S.Jb wh v) ≤ 8 * (P.Kc2 + 1) * Msq P Wc * S.J2 wh
      + (8 * (P.Kc2 + 1) * Msq P Wc)⁻¹ * S.J2 v := by
    have Y := SemiIP.sum_young (range S.N) S.j (fun _ => wh) (fun _ => v) hs
    beta_reduce at Y
    have := mul_le_mul_of_nonneg_left Y S.cJ_nonneg
    unfold Setting.Jb Setting.J2 Setting.jh
    linarith
  have c3 : (8 * (P.Kc2 + 1) * Msq P Wc)⁻¹ * (P.Kc2 * S.tnj2 v + S.J2 v)
      ≤ 1 / 8 * S.tnj2 e := by
    have h1 : P.Kc2 * S.tnj2 v + S.J2 v ≤ (P.Kc2 + 1) * (Msq P Wc * S.tnj2 e) := by
      have a1 := (S.J2_le_cj2 v).trans (S.cj2_le_tnj2 v)
      have a2 := mul_le_mul_of_nonneg_left hv1 (by positivity : 0 ≤ P.Kc2 + 1)
      linarith
    calc (8 * (P.Kc2 + 1) * Msq P Wc)⁻¹ * (P.Kc2 * S.tnj2 v + S.J2 v)
        ≤ (8 * (P.Kc2 + 1) * Msq P Wc)⁻¹ * ((P.Kc2 + 1) * (Msq P Wc * S.tnj2 e)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 1 / 8 * S.tnj2 e := by field_simp
  -- `|||e_h|||_j² ≤ 64 (C₂+1) M (C₁ T + |w_h|_J²)`
  have hE : S.tnj2 e ≤ 64 * (P.Kc2 + 1) * Msq P Wc * (P.Kc1 * T + S.J2 wh) := by
    rw [herr] at hv2
    linarith
  -- triangle inequality
  have hsplit : u - uh = (u - wh) - e := by rw [he]; abel
  have h1 := S.tn2_sub_le (u - wh) e
  rw [← hsplit] at h1
  have h2 := S.tn2_le_tnstar2 (u - wh)
  have h3 := S.tn2_le_tnj2 e
  have h4 : 64 * (P.Kc2 + 1) * Msq P Wc * (P.Kc1 * T + S.J2 wh)
      ≤ 64 * (P.Kc2 + 1) * Msq P Wc * ((P.Kc1 + 1) * (T + S.J2 wh)) := by
    have : P.Kc1 * T + S.J2 wh ≤ (P.Kc1 + 1) * (T + S.J2 wh) := by nlinarith
    exact mul_le_mul_of_nonneg_left this (by positivity)
  unfold Kst
  rw [← hT] at h2
  linarith

end ExpWeight

end StDgdg
