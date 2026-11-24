import StDgdg.WeightedTesting

/-!
# Layer 2, part 6: `lemma_derivative_testing`

Testing with `y = Δt 𝓛_h u`.
-/

namespace StDgdg

open Finset Real

variable {P : Consts} {ι X Fs Ts : Type*} [Fintype ι]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Fs] [Module ℝ Fs] [AddCommGroup Ts] [Module ℝ Ts]

namespace Setting

variable (S : Setting P ι X Fs Ts)

theorem y_mem {u : X} (hu : u ∈ S.Wh) : S.τ • S.Lh u ∈ S.Wh :=
  S.Wh.smul_mem _ (S.Lh_mem u hu)

/-- `Δt ‖w^*·∇^*u - 𝓛u‖_Q² ≲ ‖u‖_c²` (zero in Case C, `‖w‖_∞² Δt ≲ α` in Case D). -/
theorem τ_nQ_m_le (u : X) : S.τ * S.nQ (S.mat u - S.Lc u) ≤ 4 * P.C * S.cj2 u := by
  have hC := P.C_pos; have hτ := S.τ_pos; have hcj := S.cj2_nonneg u
  have hg := S.gQ_nonneg u
  cases hr : S.regime with
  | D =>
    obtain ⟨_, h2⟩ := S.caseD hr
    have f1 := S.nQ_mat_sub_Lc_le u
    have f2 := (S.αgQ_le_c2 u).trans (S.c2_le_cj2 u)
    calc S.τ * S.nQ (S.mat u - S.Lc u) ≤ S.τ * (4 * S.wInf ^ 2 * S.gQ u) := by gcongr
      _ = 4 * (S.wInf ^ 2 * S.τ) * S.gQ u := by ring
      _ ≤ 4 * (P.C * S.α) * S.gQ u := by gcongr
      _ = 4 * P.C * (S.α * S.gQ u) := by ring
      _ ≤ 4 * P.C * S.cj2 u := by gcongr
  | C =>
    rw [S.mat_Lc hr, sub_self]
    have : S.nQ (0 : X) = 0 := by unfold nQ; simp
    rw [this, mul_zero]; positivity

/-- `Δt ‖𝓛u - 𝓛_h u‖_Q² ≲ ‖u‖²_{c,j}`. -/
theorem τ_nQ_d_le {u : X} (hu : u ∈ S.Wh) :
    S.τ * S.nQ (S.Lc u - S.Lh u) ≤ P.C ^ 2 * P.Kq * S.cj2 u := by
  have hC := P.C_pos; have hτ := S.τ_pos; have hh := S.h_pos
  have f1 : S.nQ (S.Lc u - S.Lh u) ≤ P.C * S.h ^ 2 * S.gQ u := by
    unfold nQ gQ gQs
    exact sum_le_mul_sum fun n _ => S.Lc_Lh n (by in_range) u hu
  have f2 := S.gQ_le_gQT u
  have f3 := S.τ_h2_gQT_le hu
  calc S.τ * S.nQ (S.Lc u - S.Lh u) ≤ S.τ * (P.C * S.h ^ 2 * S.gQT u) := by
        gcongr; exact f1.trans (by gcongr)
    _ = P.C * (S.τ * S.h ^ 2 * S.gQT u) := by ring
    _ ≤ P.C * (P.C * P.Kq * S.cj2 u) := by gcongr
    _ = P.C ^ 2 * P.Kq * S.cj2 u := by ring

/-- term `(C)` -/
theorem deriv_C {u : X} (hu : u ∈ S.Wh) :
    3 / 4 * S.L2 u - (10 * P.C + 5 / 2 * P.C ^ 2 * P.Kq) * S.cj2 u
      ≤ S.Cb u (S.τ • S.Lh u) := by
  have hτ := S.τ_pos
  have slab : ∀ n, 3 / 4 * S.Q n (S.Lc u) (S.Lc u)
      - 5 / 2 * S.Q n (S.mat u - S.Lc u) (S.mat u - S.Lc u)
      - 5 / 2 * S.Q n (S.Lc u - S.Lh u) (S.Lc u - S.Lh u) ≤ S.Q n (S.mat u) (S.Lh u) := by
    intro n
    have := (S.Q n).cross_lower (S.Lc u) (S.mat u - S.Lc u) (S.Lc u - S.Lh u)
    rwa [add_sub_cancel, sub_sub_cancel] at this
  have hs := sum_le_sum (s := range S.N) fun n _ => slab n
  simp only [sum_sub_distrib, ← mul_sum] at hs
  have f1 := S.τ_nQ_m_le u
  have f2 := S.τ_nQ_d_le hu
  have g := mul_le_mul_of_nonneg_left hs hτ.le
  rw [Cb_smul]
  unfold Cb L2
  unfold nQ at f1 f2 ⊢
  linarith

/-- Young's inequality for the spatial upwind term with a test function `z` whose
downwind trace is controlled; covers Case C (CFL-type condition) and Case D
(`‖w‖_∞² Δt ≲ α`). -/
theorem U_facet_young (u z : X) {Zq θ : ℝ} (hZ : 0 ≤ Zq)
    (hz : ∑ n ∈ range S.N, S.FQ n (S.dn z) (S.dn z) ≤ P.C * S.h⁻¹ * Zq) (hθ : 0 < θ) :
    -(θ * S.c2 u + θ⁻¹ * (P.C ^ 2 * S.τ⁻¹ * Zq))
      ≤ 2 * ∑ n ∈ range S.N, S.FQw n (S.jmp u) (S.dn z) := by
  have hτ := S.τ_pos; have hC := P.C_pos; have hτi := S.τinv_pos
  have hh := S.h_pos; have hhi := S.hinv_pos
  have hw := S.wInf_nonneg
  have hc2 := S.c2_nonneg u
  have hjQ := S.jQ_nonneg u
  have A1 : ∑ n ∈ range S.N, S.FQw n (S.jmp u) (S.jmp u) ≤ S.wInf * S.jQ u := by
    unfold jQ
    exact sum_le_mul_sum fun n _ => S.FQw_le n (by in_range) _
  have A2 : ∑ n ∈ range S.N, S.FQw n (S.jmp u) (S.jmp u) ≤ S.c2 u := by
    refine le_trans ?_ (S.upw2_le_c2 u)
    unfold upw2
    have h1 : ∑ n ∈ range S.N, S.FQw n (S.jmp u) (S.jmp u)
        ≤ ∑ n ∈ range S.N, (S.Om n (S.tjump n u) (S.tjump n u)
          + S.FQw n (S.jmp u) (S.jmp u)) :=
      sum_le_sum fun n _ => by have := (S.Om n).nonneg (S.tjump n u); linarith
    have := (S.Om S.N).nonneg (S.prev S.N u)
    linarith
  have B1 : ∑ n ∈ range S.N, S.FQw n (S.dn z) (S.dn z) ≤ S.wInf * (P.C * S.h⁻¹ * Zq) := by
    have h1 : ∑ n ∈ range S.N, S.FQw n (S.dn z) (S.dn z)
        ≤ S.wInf * ∑ n ∈ range S.N, S.FQ n (S.dn z) (S.dn z) :=
      sum_le_mul_sum fun n _ => S.FQw_le n (by in_range) _
    exact h1.trans (mul_le_mul_of_nonneg_left hz hw)
  have f3 := S.αjQ_le_c2 u
  cases hr : S.regime with
  | C =>
    have hcfl := S.w_τ_hinv_le hr
    have Y := SemiIP.sum_young (range S.N) S.FQw (fun _ => S.jmp u) (fun _ => S.dn z) hθ
    beta_reduce at Y
    have b : θ⁻¹ * ∑ n ∈ range S.N, S.FQw n (S.dn z) (S.dn z)
        ≤ θ⁻¹ * (P.C ^ 2 * S.τ⁻¹ * Zq) :=
      calc θ⁻¹ * ∑ n ∈ range S.N, S.FQw n (S.dn z) (S.dn z)
          ≤ θ⁻¹ * (S.wInf * (P.C * S.h⁻¹ * Zq)) :=
            mul_le_mul_of_nonneg_left B1 (by positivity)
        _ = θ⁻¹ * (P.C * (S.wInf * S.τ * S.h⁻¹) * (S.τ⁻¹ * Zq)) := by field_simp
        _ ≤ θ⁻¹ * (P.C * P.C * (S.τ⁻¹ * Zq)) := by gcongr
        _ = θ⁻¹ * (P.C ^ 2 * S.τ⁻¹ * Zq) := by ring
    have a' := mul_le_mul_of_nonneg_left A2 hθ.le
    linarith
  | D =>
    obtain ⟨hD1, hD2⟩ := S.caseD hr
    rcases eq_or_lt_of_le hw with hw0 | hwpos
    · have Y := SemiIP.sum_young (range S.N) S.FQw (fun _ => S.jmp u) (fun _ => S.dn z) one_pos
      beta_reduce at Y
      rw [← hw0] at A1 B1
      have : 0 ≤ θ * S.c2 u + θ⁻¹ * (P.C ^ 2 * S.τ⁻¹ * Zq) := by positivity
      simp only [zero_mul, inv_one, one_mul] at A1 B1 Y
      linarith
    · have hα : 0 < S.α := by
        rcases eq_or_lt_of_le S.α_nonneg with h0 | hpos
        · rw [← h0] at hD1; nlinarith
        · exact hpos
      have hs : 0 < θ * S.α * S.h⁻¹ / S.wInf := by positivity
      have Y := SemiIP.sum_young (range S.N) S.FQw (fun _ => S.jmp u) (fun _ => S.dn z) hs
      beta_reduce at Y
      have a : θ * S.α * S.h⁻¹ / S.wInf * ∑ n ∈ range S.N, S.FQw n (S.jmp u) (S.jmp u)
          ≤ θ * S.c2 u :=
        calc θ * S.α * S.h⁻¹ / S.wInf * ∑ n ∈ range S.N, S.FQw n (S.jmp u) (S.jmp u)
            ≤ θ * S.α * S.h⁻¹ / S.wInf * (S.wInf * S.jQ u) :=
              mul_le_mul_of_nonneg_left A1 hs.le
          _ = θ * (S.α * (S.h⁻¹ * S.jQ u)) := by field_simp
          _ ≤ θ * S.c2 u := by gcongr
      have hratio : S.wInf ^ 2 * S.τ * S.α⁻¹ ≤ P.C :=
        calc S.wInf ^ 2 * S.τ * S.α⁻¹ ≤ P.C * S.α * S.α⁻¹ := by gcongr
          _ = P.C := by field_simp
      have b : (θ * S.α * S.h⁻¹ / S.wInf)⁻¹ * ∑ n ∈ range S.N, S.FQw n (S.dn z) (S.dn z)
          ≤ θ⁻¹ * (P.C ^ 2 * S.τ⁻¹ * Zq) :=
        calc (θ * S.α * S.h⁻¹ / S.wInf)⁻¹ * ∑ n ∈ range S.N, S.FQw n (S.dn z) (S.dn z)
            ≤ (θ * S.α * S.h⁻¹ / S.wInf)⁻¹ * (S.wInf * (P.C * S.h⁻¹ * Zq)) :=
              mul_le_mul_of_nonneg_left B1 (by positivity)
          _ = θ⁻¹ * (P.C * (S.wInf ^ 2 * S.τ * S.α⁻¹) * (S.τ⁻¹ * Zq)) := by field_simp
          _ ≤ θ⁻¹ * (P.C * P.C * (S.τ⁻¹ * Zq)) := by gcongr
          _ = θ⁻¹ * (P.C ^ 2 * S.τ⁻¹ * Zq) := by ring
      linarith

/-- `Δt⁻¹ ‖y‖²_{𝒬_T} = Δt ‖𝓛_h u‖²_{𝒬_T} ≲ |||u|||_j²`. -/
theorem τinv_nQT_y_le {u : X} (hu : u ∈ S.Wh) :
    S.τ⁻¹ * S.nQT (S.τ • S.Lh u) ≤ P.KL * S.tnj2 u := by
  have hτ := S.τ_pos
  rw [nQT_smul]
  have e : S.τ⁻¹ * (S.τ ^ 2 * S.nQT (S.Lh u)) = S.τ * S.nQT (S.Lh u) := by field_simp
  rw [e]; exact S.τ_nQT_Lh_le hu

/-- term `(U)`, spatial part -/
theorem deriv_U_facet {u : X} (hu : u ∈ S.Wh) {ε : ℝ} (hε : 0 < ε) :
    -(ε⁻¹ * S.cj2 u + ε * (P.C ^ 2 * P.KL * S.tnj2 u))
      ≤ 2 * ∑ n ∈ range S.N, S.FQw n (S.jmp u) (S.dn (S.τ • S.Lh u)) := by
  have hC := P.C_pos; have hτi := S.τinv_pos
  have hy := S.Wh_le_Ws (S.y_mem hu)
  have h1 := S.U_facet_young u (S.τ • S.Lh u) (S.nQT_nonneg _) (S.FQ_dn_le hy)
    (inv_pos.2 hε)
  rw [inv_inv] at h1
  have h2 := S.τinv_nQT_y_le hu
  have h3 := S.c2_le_cj2 u
  have a := mul_le_mul_of_nonneg_left h3 (inv_pos.2 hε).le
  have b : ε * (P.C ^ 2 * S.τ⁻¹ * S.nQT (S.τ • S.Lh u)) ≤ ε * (P.C ^ 2 * P.KL * S.tnj2 u) := by
    have := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ ε * P.C ^ 2)
    linarith
  linarith

/-- term `(U)`, temporal part -/
theorem deriv_U_time {u : X} (hu : u ∈ S.Wh) {ε : ℝ} (hε : 0 < ε) :
    -(ε⁻¹ * S.cj2 u + ε * (P.C * P.KL * S.tnj2 u))
      ≤ 2 * ∑ n ∈ range S.N, S.Om n (S.tjump n u) (S.bot n (S.τ • S.Lh u)) := by
  have hC := P.C_pos; have hτ := S.τ_pos; have hτi := S.τinv_pos
  have Y := SemiIP.sum_young (range S.N) S.Om (fun n => S.tjump n u)
    (fun n => S.bot n (S.τ • S.Lh u)) (inv_pos.2 hε)
  beta_reduce at Y
  rw [inv_inv] at Y
  have a : ∑ n ∈ range S.N, S.Om n (S.tjump n u) (S.tjump n u) ≤ S.cj2 u := by
    refine le_trans ?_ ((S.upw2_le_c2 u).trans (S.c2_le_cj2 u))
    unfold upw2
    have h1 : ∑ n ∈ range S.N, S.Om n (S.tjump n u) (S.tjump n u)
        ≤ ∑ n ∈ range S.N, (S.Om n (S.tjump n u) (S.tjump n u)
          + S.FQw n (S.jmp u) (S.jmp u)) :=
      sum_le_sum fun n _ => by have := (S.FQw n).nonneg (S.jmp u); linarith
    have := (S.Om S.N).nonneg (S.prev S.N u)
    linarith
  have f1 := S.time_traces_le (S.y_mem hu)
  have f2 : ∑ n ∈ range S.N, S.Om n (S.bot n (S.τ • S.Lh u)) (S.bot n (S.τ • S.Lh u))
      ≤ ∑ n ∈ range S.N, (S.Om n (S.bot n (S.τ • S.Lh u)) (S.bot n (S.τ • S.Lh u))
        + S.Om (n + 1) (S.top n (S.τ • S.Lh u)) (S.top n (S.τ • S.Lh u))) :=
    sum_le_sum fun n _ => by
      have := (S.Om (n + 1)).nonneg (S.top n (S.τ • S.Lh u)); linarith
  have f3 := S.τinv_nQT_y_le hu
  have b : ε * ∑ n ∈ range S.N, S.Om n (S.bot n (S.τ • S.Lh u)) (S.bot n (S.τ • S.Lh u))
      ≤ ε * (P.C * P.KL * S.tnj2 u) := by
    have g1 : ∑ n ∈ range S.N, S.Om n (S.bot n (S.τ • S.Lh u)) (S.bot n (S.τ • S.Lh u))
        ≤ P.C * (S.τ⁻¹ * S.nQT (S.τ • S.Lh u)) := by linarith
    have g2 := mul_le_mul_of_nonneg_left f3 hC.le
    exact mul_le_mul_of_nonneg_left (by linarith) hε.le
  have a' := mul_le_mul_of_nonneg_left a (inv_pos.2 hε).le
  linarith

/-- term `(A)` -/
theorem deriv_A {u : X} (hu : u ∈ S.Wh) :
    -((1 + P.C * P.Kg) * S.cj2 u) ≤ 2 * S.Ab u (S.τ • S.Lh u) := by
  have hα := S.α_nonneg
  have Y : -(1 * S.gQ u + 1⁻¹ * S.gQ (S.τ • S.Lh u))
      ≤ 2 * ∑ n ∈ range S.N, ∑ i, S.Q n (S.dx i u) (S.dx i (S.τ • S.Lh u)) := by
    unfold gQ gQs
    rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib, ← sum_neg_distrib]
    refine sum_le_sum fun n _ => ?_
    exact SemiIP.sum_young univ (fun _ => S.Q n) (fun i => S.dx i u)
      (fun i => S.dx i (S.τ • S.Lh u)) one_pos
  have f1 := (S.αgQ_le_c2 u).trans (S.c2_le_cj2 u)
  have f2 := S.gQ_le_gQT (S.τ • S.Lh u)
  have f3 := S.α_gQT_y_le hu
  have g2 := mul_le_mul_of_nonneg_left f2 hα
  have Y' := mul_le_mul_of_nonneg_left Y hα
  unfold Ab
  simp only [one_mul, inv_one] at Y'
  linarith

/-- term `(N)` -/
theorem deriv_N {u : X} (hu : u ∈ S.Wh) {ε : ℝ} (hε : 0 < ε) :
    -((ε⁻¹ * (P.C * P.Kg + P.lam) + (P.C ^ 2 * P.Kg + 1) + ε * (P.Ky1 + P.lam * P.Ky1))
        * S.cj2 u) ≤ 2 * S.Nb u (S.τ • S.Lh u) := by
  have hα := S.α_nonneg; have hKg := P.Kg_nonneg
  have hh := S.h_pos; have hhi := S.hinv_pos; have hC := P.C_pos
  have hlam := P.hlam; have hεi := inv_pos.2 hε
  have hcj := S.cj2_nonneg u
  set y : X := S.τ • S.Lh u with hy
  have hyW := S.Wh_le_Ws (S.y_mem hu)
  have Y1 := SemiIP.sum_young (range S.N) S.FQ (fun _ => S.nfl u) (fun _ => S.jmp y)
    (mul_pos hεi hh)
  have Y2 := SemiIP.sum_young (range S.N) S.FQ (fun _ => S.nfl y) (fun _ => S.jmp u) hh
  have Y3 := SemiIP.sum_young (range S.N) S.FQ (fun _ => S.jmp u) (fun _ => S.jmp y) hεi
  beta_reduce at Y1 Y2 Y3
  rw [inv_inv] at Y3
  have n1 := S.FQ_nfl_le (S.Wh_le_Ws hu)
  have n2 := S.FQ_nfl_le hyW
  have g := S.α_gQT_le_cj2 hu
  have gy : S.α * S.gQT y ≤ P.C * P.Kg * S.cj2 u := S.α_gQT_y_le hu
  have jy : S.α * (S.h⁻¹ * S.jQ y) ≤ P.Ky1 * S.cj2 u := S.α_jQ_y_le hu
  have ju := (S.αjQ_le_c2 u).trans (S.c2_le_cj2 u)
  have t1a : S.α * (ε⁻¹ * S.h * ∑ n ∈ range S.N, S.FQ n (S.nfl u) (S.nfl u))
      ≤ ε⁻¹ * (P.C * P.Kg * S.cj2 u) :=
    calc S.α * (ε⁻¹ * S.h * ∑ n ∈ range S.N, S.FQ n (S.nfl u) (S.nfl u))
        ≤ S.α * (ε⁻¹ * S.h * (P.C * S.h⁻¹ * S.gQT u)) := by gcongr
      _ = ε⁻¹ * (P.C * (S.α * S.gQT u)) := by field_simp
      _ ≤ ε⁻¹ * (P.C * (P.Kg * S.cj2 u)) := by gcongr
      _ = ε⁻¹ * (P.C * P.Kg * S.cj2 u) := by ring
  have t1b : S.α * ((ε⁻¹ * S.h)⁻¹ * S.jQ y) ≤ ε * (P.Ky1 * S.cj2 u) :=
    calc S.α * ((ε⁻¹ * S.h)⁻¹ * S.jQ y) = ε * (S.α * (S.h⁻¹ * S.jQ y)) := by field_simp
      _ ≤ ε * (P.Ky1 * S.cj2 u) := by gcongr
  have t2a : S.α * (S.h * ∑ n ∈ range S.N, S.FQ n (S.nfl y) (S.nfl y))
      ≤ P.C ^ 2 * P.Kg * S.cj2 u :=
    calc S.α * (S.h * ∑ n ∈ range S.N, S.FQ n (S.nfl y) (S.nfl y))
        ≤ S.α * (S.h * (P.C * S.h⁻¹ * S.gQT y)) := by gcongr
      _ = P.C * (S.α * S.gQT y) := by field_simp
      _ ≤ P.C * (P.C * P.Kg * S.cj2 u) := by gcongr
      _ = P.C ^ 2 * P.Kg * S.cj2 u := by ring
  have t3a : S.α * P.lam * S.h⁻¹ * (ε⁻¹ * S.jQ u) ≤ ε⁻¹ * (P.lam * S.cj2 u) :=
    calc S.α * P.lam * S.h⁻¹ * (ε⁻¹ * S.jQ u) = ε⁻¹ * (P.lam * (S.α * (S.h⁻¹ * S.jQ u))) := by
          ring
      _ ≤ ε⁻¹ * (P.lam * S.cj2 u) := by gcongr
  have t3b : S.α * P.lam * S.h⁻¹ * (ε * S.jQ y) ≤ ε * (P.lam * P.Ky1 * S.cj2 u) :=
    calc S.α * P.lam * S.h⁻¹ * (ε * S.jQ y) = ε * (P.lam * (S.α * (S.h⁻¹ * S.jQ y))) := by ring
      _ ≤ ε * (P.lam * (P.Ky1 * S.cj2 u)) := by gcongr
      _ = ε * (P.lam * P.Ky1 * S.cj2 u) := by ring
  have Y1' := mul_le_mul_of_nonneg_left Y1 hα
  have Y2' := mul_le_mul_of_nonneg_left Y2 hα
  have Y3' := mul_le_mul_of_nonneg_left Y3 (by positivity : 0 ≤ S.α * P.lam * S.h⁻¹)
  have eN : S.Nb u y
      = S.α * ∑ n ∈ range S.N, S.FQ n (S.nfl u) (S.jmp y)
        + S.α * ∑ n ∈ range S.N, S.FQ n (S.nfl y) (S.jmp u)
        + S.α * P.lam * S.h⁻¹ * ∑ n ∈ range S.N, S.FQ n (S.jmp u) (S.jmp y) := by
    unfold Nb
    simp only [sum_add_distrib, mul_sum]
  unfold jQ at t1b t3a t3b ju
  rw [eN]
  linarith

/-- term `(J)` -/
theorem deriv_J {u : X} (hu : u ∈ S.Wh) {ε : ℝ} (hε : 0 < ε) :
    -((ε⁻¹ + ε * P.KLJ) * S.cj2 u) ≤ 2 * S.Jb u (S.τ • S.Lh u) := by
  have hcJ := S.cJ_nonneg; have hεi := inv_pos.2 hε
  have Y := SemiIP.sum_young (range S.N) S.j (fun _ => u) (fun _ => S.τ • S.Lh u) hεi
  beta_reduce at Y
  rw [inv_inv] at Y
  have f1 := S.J2_y_le hu
  have f2 := S.J2_le_cj2 u
  have a := mul_le_mul_of_nonneg_left f2 hεi.le
  have b := mul_le_mul_of_nonneg_left f1 hε.le
  have Y' := mul_le_mul_of_nonneg_left Y hcJ
  unfold Jb
  unfold J2 jh at a b
  linarith

/-- Constants of `lemma_derivative_testing`. -/
noncomputable def _root_.StDgdg.Consts.Kd0 (P : Consts) : ℝ :=
  10 * P.C + 5 / 2 * P.C ^ 2 * P.Kq + (1 + P.C * P.Kg) / 2 + (P.C ^ 2 * P.Kg + 1) / 2
noncomputable def _root_.StDgdg.Consts.Kd1 (P : Consts) : ℝ :=
  (3 + P.C * P.Kg + P.lam) / 2
noncomputable def _root_.StDgdg.Consts.Kd2 (P : Consts) : ℝ :=
  (P.C * P.KL + P.C ^ 2 * P.KL + P.Ky1 + P.lam * P.Ky1 + P.KLJ) / 2
/-- The constant `C_{lemma_derivative_testing}`. -/
noncomputable def _root_.StDgdg.Consts.Kd (P : Consts) : ℝ :=
  P.Kd0 + (2 * P.Kd2 + 1) * P.Kd1 + 1 / 2

theorem _root_.StDgdg.Consts.Kd1_nonneg (P : Consts) : 0 ≤ P.Kd1 := by
  have := P.C_pos; have := P.Kg_nonneg; have := P.hlam; unfold Consts.Kd1; positivity
theorem _root_.StDgdg.Consts.Kd2_nonneg (P : Consts) : 0 ≤ P.Kd2 := by
  have := P.C_pos; have := P.KL_nonneg; have := P.hlam; have := P.Ky1_nonneg
  have := P.KLJ_nonneg; unfold Consts.Kd2; positivity
theorem _root_.StDgdg.Consts.Kd_nonneg (P : Consts) : 0 ≤ P.Kd := by
  have := P.C_pos; have := P.Kg_nonneg; have := P.Kq_nonneg
  have := P.Kd1_nonneg; have := P.Kd2_nonneg
  unfold Consts.Kd Consts.Kd0; positivity

/-- All terms collected, with the Young parameter `ε` still free. -/
theorem deriv_terms {u : X} (hu : u ∈ S.Wh) {ε : ℝ} (hε : 0 < ε) :
    3 / 4 * S.L2 u - (P.Kd0 + ε⁻¹ * P.Kd1) * S.cj2 u - ε * P.Kd2 * S.tnj2 u
      ≤ S.BJ u (S.τ • S.Lh u) := by
  have hεi := inv_pos.2 hε
  have hcj := S.cj2_nonneg u
  have c1 := S.deriv_C hu
  have c2 := S.deriv_U_facet hu hε
  have c3 := S.deriv_U_time hu hε
  have c4 := S.deriv_A hu
  have c5 := S.deriv_N hu hε
  have c6 := S.deriv_J hu hε
  have ct := S.cj2_le_tnj2 u
  have hKy1 := P.Ky1_nonneg; have hKLJ := P.KLJ_nonneg; have hlam := P.hlam
  have d1 := mul_le_mul_of_nonneg_left ct
    (by positivity : 0 ≤ ε * (P.Ky1 + P.lam * P.Ky1 + P.KLJ))
  have eU : S.Ub u (S.τ • S.Lh u)
      = ∑ n ∈ range S.N, S.FQw n (S.jmp u) (S.dn (S.τ • S.Lh u))
        + ∑ n ∈ range S.N, S.Om n (S.tjump n u) (S.bot n (S.τ • S.Lh u)) := by
    unfold Ub; rw [sum_add_distrib]
  unfold BJ Consts.Kd0 Consts.Kd1 Consts.Kd2
  rw [eU]
  linarith

/-- **`lemma_derivative_testing`**, `eq_derivative_testing`:
`(B_h + J)(u, Δt 𝓛_h u) ≥ ¼ Δt ‖𝓛u‖_Q² - C ‖u‖²_{c,j}`. -/
theorem derivative_testing {u : X} (hu : u ∈ S.Wh) :
    1 / 4 * S.L2 u - P.Kd * S.cj2 u ≤ S.BJ u (S.τ • S.Lh u) := by
  have hK1 := P.Kd1_nonneg; have hK2 := P.Kd2_nonneg
  have hcj := S.cj2_nonneg u; have hL := S.L2_nonneg u
  have hε : (0 : ℝ) < (2 * P.Kd2 + 1)⁻¹ := by positivity
  have h := S.deriv_terms hu hε
  rw [inv_inv] at h
  have hεK : (2 * P.Kd2 + 1)⁻¹ * P.Kd2 ≤ 1 / 2 := by
    rw [inv_mul_le_iff₀ (by positivity)]; linarith
  have ht : (2 * P.Kd2 + 1)⁻¹ * P.Kd2 * S.tnj2 u ≤ 1 / 2 * S.tnj2 u :=
    mul_le_mul_of_nonneg_right hεK (S.tnj2_nonneg u)
  unfold Consts.Kd
  unfold tnj2 at ht h
  linarith

end Setting

end StDgdg
