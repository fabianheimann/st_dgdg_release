import StDgdg.Derivative
import StDgdg.Abstract

/-!
# Layer 2, part 7: `lemma_test_fun_bnd` and `thm_stability`
-/

namespace StDgdg

open Finset Real

variable {P : Consts} {ι X Fs Ts : Type*} [Fintype ι]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Fs] [Module ℝ Fs] [AddCommGroup Ts] [Module ℝ Ts]

namespace Setting

variable (S : Setting P ι X Fs Ts)

/-! ### quadratic-form calculus for the norms -/

theorem gQ_add_le (x y : X) : S.gQ (x + y) ≤ 2 * S.gQ x + 2 * S.gQ y := by
  unfold gQ gQs
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun n _ => ?_
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun i _ => ?_
  rw [map_add]; exact (S.Q n).add_sq_le _ _

theorem jQ_add_le (x y : X) : S.jQ (x + y) ≤ 2 * S.jQ x + 2 * S.jQ y := by
  unfold jQ
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun n _ => ?_
  rw [map_add]; exact (S.FQ n).add_sq_le _ _

theorem J2_add_le (x y : X) : S.J2 (x + y) ≤ 2 * S.J2 x + 2 * S.J2 y := by
  have h : S.jh (x + y) ≤ 2 * S.jh x + 2 * S.jh y := by
    unfold jh
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_le_sum fun n _ => (S.j n).add_sq_le _ _
  have := mul_le_mul_of_nonneg_left h S.cJ_nonneg
  unfold J2; linarith

theorem upw2_add_le (x y : X) : S.upw2 (x + y) ≤ 2 * S.upw2 x + 2 * S.upw2 y := by
  unfold upw2
  have h1 := sum_le_sum (s := range S.N) fun n _ =>
    add_le_add ((S.Om n).add_sq_le_map (S.tjump n) x y)
      ((S.FQw n).add_sq_le_map S.jmp x y)
  have h2 := (S.Om S.N).add_sq_le_map (S.prev S.N) x y
  have e : ∑ n ∈ range S.N,
      (2 * S.Om n (S.tjump n x) (S.tjump n x) + 2 * S.Om n (S.tjump n y) (S.tjump n y)
        + (2 * S.FQw n (S.jmp x) (S.jmp x) + 2 * S.FQw n (S.jmp y) (S.jmp y)))
      = 2 * ∑ n ∈ range S.N, (S.Om n (S.tjump n x) (S.tjump n x)
          + S.FQw n (S.jmp x) (S.jmp x))
        + 2 * ∑ n ∈ range S.N, (S.Om n (S.tjump n y) (S.tjump n y)
          + S.FQw n (S.jmp y) (S.jmp y)) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun n _ => ?_; ring
  rw [e] at h1
  linarith

theorem tnj2_add_le (x y : X) : S.tnj2 (x + y) ≤ 2 * S.tnj2 x + 2 * S.tnj2 y := by
  have hα := S.α_nonneg; have hhi := S.hinv_pos; have hτ := S.τ_pos
  have h1 : S.L2 (x + y) ≤ 2 * S.L2 x + 2 * S.L2 y := by
    unfold L2; rw [map_add]
    have := mul_le_mul_of_nonneg_left (S.nQ_add_le (S.Lc x) (S.Lc y)) hτ.le
    linarith
  have h2 := S.nQ_add_le x y
  have h3 := mul_le_mul_of_nonneg_left (S.gQ_add_le x y) hα
  have h4 := mul_le_mul_of_nonneg_left (S.jQ_add_le x y)
    (by positivity : 0 ≤ S.α * S.h⁻¹)
  have h5 := S.upw2_add_le x y
  have h6 := S.J2_add_le x y
  unfold tnj2 cj2 c2
  linarith

theorem upw2_smul (c : ℝ) (u : X) : S.upw2 (c • u) = c ^ 2 * S.upw2 u := by
  unfold upw2
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [mul_add, mul_sum]
  congr 1
  · refine sum_congr rfl fun n _ => ?_; ring
  · ring

theorem tnj2_smul (c : ℝ) (u : X) : S.tnj2 (c • u) = c ^ 2 * S.tnj2 u := by
  unfold tnj2 cj2 c2 L2
  rw [map_smul, nQ_smul, nQ_smul, gQ_smul, jQ_smul, upw2_smul, J2_smul]
  ring

/-- The temporal part of the upwind norm is bounded by the one-sided traces. -/
theorem upw2_le_traces (v : X) :
    S.upw2 v ≤ 2 * ∑ n ∈ range S.N, (S.Om n (S.bot n v) (S.bot n v)
        + S.Om (n + 1) (S.top n v) (S.top n v)) + S.wInf * S.jQ v := by
  have hp : ∑ k ∈ range (S.N + 1), S.Om k (S.prev k v) (S.prev k v)
      = ∑ n ∈ range S.N, S.Om (n + 1) (S.top n v) (S.top n v) := by
    rw [sum_range_succ']
    simp [prev]
  have hp2 := sum_range_succ (fun k => S.Om k (S.prev k v) (S.prev k v)) S.N
  beta_reduce at hp2
  have h1 : ∑ n ∈ range S.N, S.Om n (S.tjump n v) (S.tjump n v)
      ≤ 2 * ∑ n ∈ range S.N, S.Om n (S.bot n v) (S.bot n v)
        + 2 * ∑ n ∈ range S.N, S.Om n (S.prev n v) (S.prev n v) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_le_sum fun n _ => (S.Om n).sub_sq_le _ _
  have h2 : ∑ n ∈ range S.N, S.FQw n (S.jmp v) (S.jmp v) ≤ S.wInf * S.jQ v := by
    unfold jQ
    exact sum_le_mul_sum fun n _ => S.FQw_le n (by in_range) _
  have h3 := (S.Om S.N).nonneg (S.prev S.N v)
  unfold upw2
  rw [sum_add_distrib, sum_add_distrib]
  linarith

/-! ### `lemma_test_fun_bnd`, first estimate -/

/-- Constant of `tnj2_y_le`. -/
noncomputable def _root_.StDgdg.Consts.Kty (P : Consts) : ℝ :=
  P.C * P.KL + P.KL + P.C * P.Kg + P.Ky1 + 2 * P.C * P.KL
    + (P.C * P.Ky1 + 4 * P.C ^ 2 * P.KL) + P.KLJ

theorem _root_.StDgdg.Consts.Kty_nonneg (P : Consts) : 0 ≤ P.Kty := by
  have := P.C_pos; have := P.KL_nonneg; have := P.Kg_nonneg; have := P.Ky1_nonneg
  have := P.KLJ_nonneg; unfold Consts.Kty; positivity

/-- **`lemma_test_fun_bnd`**, first estimate: `|||Δt 𝓛_h u|||_j² ≲ |||u|||_j²`. -/
theorem tnj2_y_le {u : X} (hu : u ∈ S.Wh) : S.tnj2 (S.τ • S.Lh u) ≤ P.Kty * S.tnj2 u := by
  have hC := P.C_pos; have hτ := S.τ_pos; have hτ1 := S.τ_le_one; have hτi := S.τinv_pos
  have hKL := P.KL_nonneg; have hKg := P.Kg_nonneg; have hKy1 := P.Ky1_nonneg
  have hKLJ := P.KLJ_nonneg
  have ht := S.tnj2_nonneg u
  have hct := S.cj2_le_tnj2 u
  set y : X := S.τ • S.Lh u with hy
  have hyW : y ∈ S.Wh := S.y_mem hu
  have q : S.τ⁻¹ * S.nQT y ≤ P.KL * S.tnj2 u := S.τinv_nQT_y_le hu
  have hq0 := S.nQT_nonneg y
  -- `Δt ‖𝓛 y‖²`
  have b1 : S.L2 y ≤ P.C * P.KL * S.tnj2 u := by
    have h1 : S.nQ (S.Lc y) ≤ P.C * S.τ⁻¹ ^ 2 * S.nQT y := by
      unfold nQ nQT
      exact sum_le_mul_sum fun n _ => S.Lc_inv n (by in_range) y hyW
    unfold L2
    calc S.τ * S.nQ (S.Lc y) ≤ S.τ * (P.C * S.τ⁻¹ ^ 2 * S.nQT y) := by gcongr
      _ = P.C * (S.τ⁻¹ * S.nQT y) := by field_simp
      _ ≤ P.C * (P.KL * S.tnj2 u) := by gcongr
      _ = P.C * P.KL * S.tnj2 u := by ring
  -- `‖y‖_Q²`
  have b2 : S.nQ y ≤ P.KL * S.tnj2 u := by
    have h1 := S.nQ_le_nQT y
    have h2 : S.nQT y ≤ S.τ⁻¹ * S.nQT y := by
      have : 1 ≤ S.τ⁻¹ := (one_le_inv₀ hτ).2 hτ1
      nlinarith
    linarith
  -- diffusion part
  have b3 : S.α * S.gQ y ≤ P.C * P.Kg * S.tnj2 u := by
    have h1 := mul_le_mul_of_nonneg_left (S.gQ_le_gQT y) S.α_nonneg
    have h2 : S.α * S.gQT y ≤ P.C * P.Kg * S.cj2 u := S.α_gQT_y_le hu
    have h3 := mul_le_mul_of_nonneg_left hct (by positivity : 0 ≤ P.C * P.Kg)
    linarith
  have b4 : S.α * (S.h⁻¹ * S.jQ y) ≤ P.Ky1 * S.tnj2 u := by
    have h2 : S.α * (S.h⁻¹ * S.jQ y) ≤ P.Ky1 * S.cj2 u := S.α_jQ_y_le hu
    have h3 := mul_le_mul_of_nonneg_left hct hKy1
    linarith
  -- upwind part
  have b5 : S.upw2 y ≤ (2 * P.C * P.KL + (P.C * P.Ky1 + 4 * P.C ^ 2 * P.KL)) * S.tnj2 u := by
    have h1 := S.upw2_le_traces y
    have h2 := S.time_traces_le hyW
    have h3 : S.wInf * S.jQ y ≤ (P.C * P.Ky1 + 4 * P.C ^ 2 * P.KL) * S.tnj2 u :=
      S.w_jQ_y_le hu
    have h4 := mul_le_mul_of_nonneg_left q (by positivity : 0 ≤ 2 * P.C)
    have e : 2 * (P.C * S.τ⁻¹ * S.nQT y) = 2 * P.C * (S.τ⁻¹ * S.nQT y) := by ring
    linarith
  -- Ghost penalty part
  have b6 : S.J2 y ≤ P.KLJ * S.tnj2 u := by
    have h2 : S.J2 y ≤ P.KLJ * S.cj2 u := S.J2_y_le hu
    have h3 := mul_le_mul_of_nonneg_left hct hKLJ
    linarith
  unfold Consts.Kty
  have e : S.tnj2 y = S.L2 y + (S.nQ y + S.α * (S.gQ y + S.h⁻¹ * S.jQ y) + S.upw2 y + S.J2 y) :=
    rfl
  rw [e]
  linarith

/-- `‖w‖_∞² Δt³ ‖∇u‖²_{𝒬_T} ≲ ‖u‖²_{c,j}` in both regimes. -/
theorem w2_τ3_gQT_le {u : X} (hu : u ∈ S.Wh) :
    S.wInf ^ 2 * S.τ ^ 3 * S.gQT u ≤ (P.C * P.Kg + P.C ^ 3 * P.Kq) * S.cj2 u := by
  have hC := P.C_pos; have hτ := S.τ_pos; have hτ1 := S.τ_le_one; have hh := S.h_pos
  have hw := S.wInf_nonneg; have hα := S.α_nonneg
  have hKq := P.Kq_nonneg; have hKg := P.Kg_nonneg
  have hcj := S.cj2_nonneg u; have hg := S.gQT_nonneg u
  have hτ2 : S.τ ^ 2 ≤ 1 := by nlinarith
  cases hr : S.regime with
  | D =>
    obtain ⟨_, h2⟩ := S.caseD hr
    have f := S.α_gQT_le_cj2 hu
    have h3 : S.wInf ^ 2 * S.τ ^ 3 * S.gQT u ≤ P.C * P.Kg * S.cj2 u :=
      calc S.wInf ^ 2 * S.τ ^ 3 * S.gQT u = (S.wInf ^ 2 * S.τ) * S.τ ^ 2 * S.gQT u := by ring
        _ ≤ (P.C * S.α) * 1 * S.gQT u := by gcongr
        _ = P.C * (S.α * S.gQT u) := by ring
        _ ≤ P.C * (P.Kg * S.cj2 u) := by gcongr
        _ = P.C * P.Kg * S.cj2 u := by ring
    have : 0 ≤ P.C ^ 3 * P.Kq * S.cj2 u := by positivity
    linarith
  | C =>
    have h1 := S.w_τ_hinv_le hr
    have h2 : S.gQT u ≤ P.C * S.h⁻¹ ^ 2 * S.nQT u := by
      unfold gQT nQT
      exact sum_le_mul_sum fun n _ => S.inv_dx n (by in_range) u (S.Wh_le_Ws hu)
    have h3 := S.τ_nQT_le_cj2 hu
    have hq := S.nQT_nonneg u
    have hhi := S.hinv_pos
    have h5 : (S.wInf * S.τ * S.h⁻¹) ^ 2 ≤ P.C ^ 2 := by
      have : 0 ≤ S.wInf * S.τ * S.h⁻¹ := by positivity
      gcongr
    have h4 : S.wInf ^ 2 * S.τ ^ 3 * S.gQT u ≤ P.C ^ 3 * P.Kq * S.cj2 u :=
      calc S.wInf ^ 2 * S.τ ^ 3 * S.gQT u
          ≤ S.wInf ^ 2 * S.τ ^ 3 * (P.C * S.h⁻¹ ^ 2 * S.nQT u) := by gcongr
        _ = P.C * (S.wInf * S.τ * S.h⁻¹) ^ 2 * (S.τ * S.nQT u) := by ring
        _ ≤ P.C * P.C ^ 2 * (P.Kq * S.cj2 u) := by gcongr
        _ = P.C ^ 3 * P.Kq * S.cj2 u := by ring
    have : 0 ≤ P.C * P.Kg * S.cj2 u := by positivity
    linarith

end Setting

namespace ExpWeight

variable {S : Setting P ι X Fs Ts} {Wc : WConsts} (E : ExpWeight S Wc)

/-! ### `lemma_test_fun_bnd`, second estimate -/

theorem phi_sq_le (k : ℕ) (hk : k ≤ S.N) : E.phi k ^ 2 ≤ 1 := by
  have h1 := E.c0_le_phi k hk; have h2 := E.phi_le_one k hk; have h3 := E.c0_pos
  nlinarith

theorem prev_M (k : ℕ) (hk : k ≤ S.N) (u : X) : S.prev k (E.M u) = E.phi k • S.prev k u := by
  cases k with
  | zero => simp [Setting.prev]
  | succ n => exact E.top_M n (by in_range) u

/-- the norms of `φ u` are bounded by those of `u` -/
theorem tnj2_M_le (u : X) : S.tnj2 (E.M u) ≤ (2 + 2 * Wc.σ ^ 2) * S.tnj2 u := by
  have hα := S.α_nonneg; have hhi := S.hinv_pos; have hτ := S.τ_pos; have hτ1 := S.τ_le_one
  have hσ := Wc.hσ
  have a1 : S.nQ (E.M u) ≤ S.nQ u := sum_le_sum fun n _ => E.Q_contr n (by in_range) u
  have a2 : S.gQ (E.M u) ≤ S.gQ u := by
    unfold Setting.gQ Setting.gQs
    refine sum_le_sum fun n _ => sum_le_sum fun i _ => ?_
    rw [E.dx_M]; exact E.Q_contr n (by in_range) _
  have a3 : S.jQ (E.M u) ≤ S.jQ u := by
    unfold Setting.jQ
    refine sum_le_sum fun n _ => ?_
    rw [E.toWeight.jmp_M]; exact E.FQ_contr n (by in_range) _
  have a4 : S.J2 (E.M u) ≤ S.J2 u := by
    have : S.jh (E.M u) ≤ S.jh u := sum_le_sum fun n _ => E.j_contr n (by in_range) u
    exact mul_le_mul_of_nonneg_left this S.cJ_nonneg
  have a5 : S.upw2 (E.M u) ≤ S.upw2 u := by
    unfold Setting.upw2
    refine add_le_add (sum_le_sum fun n _ => add_le_add ?_ ?_) ?_
    · have e : S.tjump n (E.M u) = E.phi n • S.tjump n u := by
        simp only [Setting.tjump, LinearMap.sub_apply, E.bot_M n (by in_range), E.prev_M n (by in_range),
          smul_sub]
      rw [e, SemiIP.smul_sq]
      have := mul_le_mul_of_nonneg_right (E.phi_sq_le n (by in_range)) ((S.Om n).nonneg (S.tjump n u))
      linarith
    · rw [E.toWeight.jmp_M]; exact E.FQw_contr n (by in_range) _
    · rw [E.prev_M S.N le_rfl, SemiIP.smul_sq]
      have := mul_le_mul_of_nonneg_right (E.phi_sq_le S.N le_rfl)
        ((S.Om S.N).nonneg (S.prev S.N u))
      linarith
  have a6 : S.L2 (E.M u) ≤ 2 * S.L2 u + 2 * Wc.σ ^ 2 * S.nQ u := by
    unfold Setting.L2
    rw [E.Lc_M]
    have h1 : S.nQ (E.M (S.Lc u) - Wc.σ • E.M u)
        ≤ 2 * S.nQ (E.M (S.Lc u)) + 2 * S.nQ (Wc.σ • E.M u) := by
      unfold Setting.nQ
      rw [mul_sum, mul_sum, ← sum_add_distrib]
      exact sum_le_sum fun n _ => (S.Q n).sub_sq_le _ _
    have h2 : S.nQ (E.M (S.Lc u)) ≤ S.nQ (S.Lc u) := sum_le_sum fun n _ => E.Q_contr n (by in_range) _
    rw [S.nQ_smul] at h1
    have hnQ := S.nQ_nonneg u
    have h3 : S.τ * (Wc.σ ^ 2 * S.nQ (E.M u)) ≤ Wc.σ ^ 2 * S.nQ u := by
      have : 0 ≤ Wc.σ ^ 2 * S.nQ (E.M u) := mul_nonneg (sq_nonneg _) (S.nQ_nonneg _)
      have h4 := mul_le_mul_of_nonneg_left a1 (sq_nonneg Wc.σ)
      nlinarith
    have g1 := mul_le_mul_of_nonneg_left h1 hτ.le
    have g2 := mul_le_mul_of_nonneg_left h2 hτ.le
    linarith
  have b3 := mul_le_mul_of_nonneg_left a2 hα
  have b4 := mul_le_mul_of_nonneg_left a3 (by positivity : 0 ≤ S.α * S.h⁻¹)
  have hL := S.L2_nonneg u; have hnQ := S.nQ_nonneg u
  have hg := S.gQ_nonneg u; have hj := S.jQ_nonneg u; have hup := S.upw2_nonneg u
  have hJ := S.J2_nonneg u
  have p1 : 0 ≤ Wc.σ ^ 2 * S.L2 u := by positivity
  have p2 : 0 ≤ Wc.σ ^ 2 * (S.α * (S.gQ u + S.h⁻¹ * S.jQ u)) := by positivity
  have p3 : 0 ≤ Wc.σ ^ 2 * S.upw2 u := by positivity
  have p4 : 0 ≤ Wc.σ ^ 2 * S.J2 u := by positivity
  have p5 : 0 ≤ S.α * (S.gQ u + S.h⁻¹ * S.jQ u) := by positivity
  have p6 : 0 ≤ Wc.σ ^ 2 * S.nQ u := by positivity
  unfold Setting.tnj2 Setting.cj2 Setting.c2
  linarith

/-- Constant of `tnj2_r_le`. -/
noncomputable def Ktr (P : Consts) (Wc : WConsts) : ℝ :=
  2 * Wc.Cs * P.Kq + 2 * Wc.Cs * (P.C * P.Kg + P.C ^ 3 * P.Kq) + Wc.Cs * P.Kq + Wc.Cs * P.Kg
    + Wc.Cs * (P.C * P.γJ⁻¹ + 1) + 4 * P.C * Wc.Cs * P.Kq
    + (P.C * Wc.Cs * (P.C * P.γJ⁻¹ + 1) + 4 * P.C ^ 2 * Wc.Cs * P.Kq) + Wc.Cs

theorem Ktr_nonneg (P : Consts) (Wc : WConsts) : 0 ≤ Ktr P Wc := by
  have := P.C_pos; have := P.hγJ; have := Wc.Cs_pos; have := P.Kg_nonneg; have := P.Kq_nonneg
  unfold Ktr; positivity

/-- the norms of the remainder `r` -/
theorem tnj2_r_le {u : X} (hu : u ∈ S.Wh) : S.tnj2 (E.r u) ≤ Ktr P Wc * S.cj2 u := by
  have hC := P.C_pos; have hγ := P.hγJ; have hCs := Wc.Cs_pos
  have hτ := S.τ_pos; have hτ1 := S.τ_le_one; have hα := S.α_nonneg; have hhi := S.hinv_pos
  have hw := S.wInf_nonneg; have hτi := S.τinv_pos
  have hKq := P.Kq_nonneg; have hKg := P.Kg_nonneg
  have hcj := S.cj2_nonneg u
  have hτ2 : S.τ ^ 2 ≤ 1 := by nlinarith
  have hq := S.nQT_nonneg u
  have fq := S.nQT_le_cj2 hu
  have fg := S.α_gQT_le_cj2 hu
  have hgT := S.gQT_nonneg u
  -- `Δt ‖𝓛 r‖²`
  have b1 : S.L2 (E.r u)
      ≤ (2 * Wc.Cs * P.Kq + 2 * Wc.Cs * (P.C * P.Kg + P.C ^ 3 * P.Kq)) * S.cj2 u := by
    have h1 : S.nQ (S.Lc (E.r u))
        ≤ 2 * S.nQ (S.dt (E.r u)) + 2 * S.nQ (S.Lc (E.r u) - S.dt (E.r u)) := by
      have e : S.Lc (E.r u) = S.dt (E.r u) + (S.Lc (E.r u) - S.dt (E.r u)) := by abel
      have := S.nQ_add_le (S.dt (E.r u)) (S.Lc (E.r u) - S.dt (E.r u))
      rwa [← e] at this
    have h2 := (S.nQ_le_nQT (S.dt (E.r u))).trans (E.nQT_dt_r_le hu)
    have h3 : S.nQ (S.Lc (E.r u) - S.dt (E.r u)) ≤ S.wInf ^ 2 * S.gQ (E.r u) := by
      unfold Setting.nQ Setting.gQ Setting.gQs
      exact sum_le_mul_sum fun n _ => S.Lc_dt n (by in_range) (E.r u)
    have h4 := (S.gQ_le_gQT (E.r u)).trans (E.gQT_r_le hu)
    have h5 := S.w2_τ3_gQT_le hu
    have g1 : S.τ * (Wc.Cs * S.nQT u) ≤ Wc.Cs * (P.Kq * S.cj2 u) := by
      have : 0 ≤ Wc.Cs * S.nQT u := by positivity
      have := mul_le_mul_of_nonneg_left fq hCs.le
      nlinarith
    have g2 : S.τ * (S.wInf ^ 2 * S.gQ (E.r u))
        ≤ Wc.Cs * ((P.C * P.Kg + P.C ^ 3 * P.Kq) * S.cj2 u) :=
      calc S.τ * (S.wInf ^ 2 * S.gQ (E.r u))
          ≤ S.τ * (S.wInf ^ 2 * (Wc.Cs * S.τ ^ 2 * S.gQT u)) := by gcongr
        _ = Wc.Cs * (S.wInf ^ 2 * S.τ ^ 3 * S.gQT u) := by ring
        _ ≤ Wc.Cs * ((P.C * P.Kg + P.C ^ 3 * P.Kq) * S.cj2 u) := by gcongr
    have m1 := mul_le_mul_of_nonneg_left h1 hτ.le
    have m2 := mul_le_mul_of_nonneg_left h2 hτ.le
    have m3 := mul_le_mul_of_nonneg_left h3 hτ.le
    unfold Setting.L2
    linarith
  have b2 : S.nQ (E.r u) ≤ Wc.Cs * P.Kq * S.cj2 u := by
    have h1 := (S.nQ_le_nQT (E.r u)).trans (E.nQT_r_le hu)
    have h2 : Wc.Cs * S.τ ^ 2 * S.nQT u ≤ Wc.Cs * 1 * (P.Kq * S.cj2 u) := by gcongr
    linarith
  have b3 : S.α * S.gQ (E.r u) ≤ Wc.Cs * P.Kg * S.cj2 u := by
    have h1 := mul_le_mul_of_nonneg_left ((S.gQ_le_gQT (E.r u)).trans (E.gQT_r_le hu)) hα
    have h2 : S.α * (Wc.Cs * S.τ ^ 2 * S.gQT u) ≤ Wc.Cs * 1 * (P.Kg * S.cj2 u) :=
      calc S.α * (Wc.Cs * S.τ ^ 2 * S.gQT u) = Wc.Cs * S.τ ^ 2 * (S.α * S.gQT u) := by ring
        _ ≤ Wc.Cs * 1 * (P.Kg * S.cj2 u) := by gcongr
    linarith
  have b4 : S.α * (S.h⁻¹ * S.jQ (E.r u)) ≤ Wc.Cs * (P.C * P.γJ⁻¹ + 1) * S.cj2 u := by
    have h1 := E.α_jQ_r_le hu
    have h2 : Wc.Cs * (P.C * P.γJ⁻¹ + 1) * S.τ ^ 2 * S.cj2 u
        ≤ Wc.Cs * (P.C * P.γJ⁻¹ + 1) * 1 * S.cj2 u := by gcongr
    linarith
  have b5 : S.upw2 (E.r u) ≤ (4 * P.C * Wc.Cs * P.Kq
      + (P.C * Wc.Cs * (P.C * P.γJ⁻¹ + 1) + 4 * P.C ^ 2 * Wc.Cs * P.Kq)) * S.cj2 u := by
    have h1 := S.upw2_le_traces (E.r u)
    have h2 := E.time_traces_r_le hu
    have h3 : 2 * P.C * Wc.Cs * S.τ * S.nQT u ≤ 2 * P.C * Wc.Cs * 1 * (P.Kq * S.cj2 u) := by
      gcongr
    have h4 : S.wInf * S.jQ (E.r u)
        ≤ (P.C * Wc.Cs * (P.C * P.γJ⁻¹ + 1) + 4 * P.C ^ 2 * Wc.Cs * P.Kq) * S.cj2 u := by
      cases hr : S.regime with
      | D =>
        have k1 := S.w_jQ_le_D hr (E.r u)
        have k2 := mul_le_mul_of_nonneg_left b4 hC.le
        have : 0 ≤ 4 * P.C ^ 2 * Wc.Cs * P.Kq * S.cj2 u := by positivity
        linarith
      | C =>
        have k1 := S.w_jQ_le_C hr (E.r_mem u hu)
        have k2 := E.nQT_r_le hu
        have k3 : 4 * P.C ^ 2 * S.τ⁻¹ * S.nQT (E.r u) ≤ 4 * P.C ^ 2 * Wc.Cs * P.Kq * S.cj2 u :=
          calc 4 * P.C ^ 2 * S.τ⁻¹ * S.nQT (E.r u)
              ≤ 4 * P.C ^ 2 * S.τ⁻¹ * (Wc.Cs * S.τ ^ 2 * S.nQT u) := by gcongr
            _ = 4 * P.C ^ 2 * Wc.Cs * (S.τ * S.nQT u) := by field_simp
            _ ≤ 4 * P.C ^ 2 * Wc.Cs * (1 * (P.Kq * S.cj2 u)) := by gcongr
            _ = 4 * P.C ^ 2 * Wc.Cs * P.Kq * S.cj2 u := by ring
        have : 0 ≤ P.C * Wc.Cs * (P.C * P.γJ⁻¹ + 1) * S.cj2 u := by positivity
        linarith
    linarith
  have b6 : S.J2 (E.r u) ≤ Wc.Cs * S.cj2 u := by
    have h1 := E.J2_r_le hu
    have h2 : Wc.Cs * S.τ ^ 2 * S.J2 u ≤ Wc.Cs * 1 * S.cj2 u := by
      have := S.J2_le_cj2 u; have := S.J2_nonneg u
      gcongr
    linarith
  unfold Ktr
  have e : S.tnj2 (E.r u) = S.L2 (E.r u) + (S.nQ (E.r u)
      + S.α * (S.gQ (E.r u) + S.h⁻¹ * S.jQ (E.r u)) + S.upw2 (E.r u) + S.J2 (E.r u)) := rfl
  rw [e]
  linarith

/-- Constant of `tnj2_Pw_le`. -/
noncomputable def Ktw (P : Consts) (Wc : WConsts) : ℝ := 4 + 4 * Wc.σ ^ 2 + 2 * Ktr P Wc

theorem Ktw_nonneg (P : Consts) (Wc : WConsts) : 0 ≤ Ktw P Wc := by
  have := Ktr_nonneg P Wc; unfold Ktw; positivity

/-- **`lemma_test_fun_bnd`**, second estimate: `|||Π_t(e^{-σt}u)|||_j² ≲ |||u|||_j²`. -/
theorem tnj2_Pw_le {u : X} (hu : u ∈ S.Wh) : S.tnj2 (E.Pw u) ≤ Ktw P Wc * S.tnj2 u := by
  have e : E.Pw u = E.M u + E.r u := by unfold r; abel
  have h1 := S.tnj2_add_le (E.M u) (E.r u)
  have h2 := E.tnj2_M_le u
  have h3 := E.tnj2_r_le hu
  have h4 := mul_le_mul_of_nonneg_left (S.cj2_le_tnj2 u) (Ktr_nonneg P Wc)
  rw [← e] at h1
  unfold Ktw
  linarith

/-! ### `thm_stability` -/

/-- The scaling `K = (C_{lemma_derivative_testing} + ¼) / c_σ` of the supremizer. -/
noncomputable def Ksup (P : Consts) (Wc : WConsts) : ℝ := (P.Kd + 1 / 4) / cσ Wc

/-- The constant `M` with `|||ṽ(u)|||_j ≤ M |||u|||_j` (squared). -/
noncomputable def Msq (P : Consts) (Wc : WConsts) : ℝ :=
  2 * Ksup P Wc ^ 2 * Ktw P Wc + 2 * P.Kty

include E in
/-- **Inf-sup stability, `thm_stability`, `eq_inf_sup_two`** (squared norms).

For `λ ≥ λ₀` and `Δt` so small that `K C Δt^{1/2} ≤ 1/8`, the supremizer
`ṽ(u) = K Π_t(e^{-σt}u) + Δt 𝓛_h u ∈ W_h` satisfies
`|||ṽ(u)|||_j² ≤ M² |||u|||_j²` and `(B_h + J)(u, ṽ(u)) ≥ 1/8 |||u|||_j²`.
All constants are functions of `P : Consts` and `Wc : WConsts` only. -/
theorem inf_sup (hlam : P.lam0 Wc.Cφ ≤ P.lam)
    (hsmall : Ksup P Wc * Kw P Wc * √S.τ ≤ 1 / 8) {u : X} (hu : u ∈ S.Wh) :
    ∃ v ∈ S.Wh, S.tnj2 v ≤ Msq P Wc * S.tnj2 u ∧ 1 / 8 * S.tnj2 u ≤ S.BJ u v := by
  have hcσ : 0 < cσ Wc := by
    unfold cσ
    have hσ := Wc.hσ
    have hc0 := E.c0_pos
    have : 0 < min 1 Wc.σ := lt_min one_pos hσ
    positivity
  have hK0 : 0 ≤ Ksup P Wc := by
    have := P.Kd_nonneg; unfold Ksup; positivity
  have hKc : Ksup P Wc * cσ Wc = P.Kd + 1 / 4 := by unfold Ksup; field_simp
  refine ⟨Ksup P Wc • E.Pw u + S.τ • S.Lh u,
    S.Wh.add_mem (S.Wh.smul_mem _ (E.Pw_mem u hu)) (S.y_mem hu), ?_, ?_⟩
  · have h1 := S.tnj2_add_le (Ksup P Wc • E.Pw u) (S.τ • S.Lh u)
    rw [S.tnj2_smul] at h1
    have h2 := E.tnj2_Pw_le hu
    have h3 := S.tnj2_y_le hu
    have h4 := mul_le_mul_of_nonneg_left h2 (sq_nonneg (Ksup P Wc))
    unfold Msq
    linarith
  · rw [S.BJ_add, S.BJ_smul]
    have h1 := mul_le_mul_of_nonneg_left (E.weighted_symm_testing hlam hu) hK0
    have h2 := S.derivative_testing hu
    have h3 := mul_le_mul_of_nonneg_right hsmall (S.tnj2_nonneg u)
    have e : Ksup P Wc * (cσ Wc * S.cj2 u - Kw P Wc * √S.τ * S.tnj2 u)
        = (P.Kd + 1 / 4) * S.cj2 u - Ksup P Wc * Kw P Wc * √S.τ * S.tnj2 u := by
      rw [← hKc]; ring
    rw [e] at h1
    unfold Setting.tnj2 at h1 h3 ⊢
    linarith

end ExpWeight

end StDgdg
