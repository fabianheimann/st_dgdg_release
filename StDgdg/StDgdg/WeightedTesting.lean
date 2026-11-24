import StDgdg.Remainder

/-!
# Layer 2, part 5: `lemma_weighted_symm_testing`

Estimate of the five contributions to `(B_h + J)(u, r)`, `r = (Π_t - Id)(φ u)`, and the
weighted symmetric testing estimate `eq_weighted_symm_testing`.
-/

namespace StDgdg

open Finset Real

variable {P : Consts} {ι X Fs Ts : Type*} [Fintype ι]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Fs] [Module ℝ Fs] [AddCommGroup Ts] [Module ℝ Ts]

namespace ExpWeight

variable {S : Setting P ι X Fs Ts} {Wc : WConsts} (E : ExpWeight S Wc)

/-- volume convection term `C(u, r)` -/
theorem rem_C {u : X} (hu : u ∈ S.Wh) :
    -(√S.τ * (2 * S.L2 u + (8 * P.C + Wc.Cs * P.Kq) * S.cj2 u)) ≤ 2 * S.Cb u (E.r u) := by
  have hrt := S.rt_pos; have hτ := S.τ_pos; have hC := P.C_pos; have hCs := Wc.Cs_pos
  have hKq := P.Kq_nonneg
  have Y := SemiIP.sum_young (range S.N) S.Q (fun _ => S.mat u) (fun _ => E.r u)
    (mul_pos hτ hrt)
  beta_reduce at Y
  have f1 := S.τ_nQ_mat_le u
  have f2 := (S.αgQ_le_c2 u).trans (S.c2_le_cj2 u)
  have f3 := (S.nQ_le_nQT (E.r u)).trans (E.nQT_r_le hu)
  have f4 := S.nQT_le_cj2 hu
  have a : S.τ * √S.τ * S.nQ (S.mat u) ≤ √S.τ * (2 * S.L2 u + 8 * P.C * S.cj2 u) := by
    have h1 : S.τ * S.nQ (S.mat u) ≤ 2 * S.L2 u + 8 * P.C * S.cj2 u := by
      have := mul_le_mul_of_nonneg_left f2 (by positivity : 0 ≤ 8 * P.C); linarith
    have := mul_le_mul_of_nonneg_left h1 hrt.le
    linarith
  have b : (S.τ * √S.τ)⁻¹ * S.nQ (E.r u) ≤ √S.τ * (Wc.Cs * P.Kq * S.cj2 u) :=
    calc (S.τ * √S.τ)⁻¹ * S.nQ (E.r u) ≤ (S.τ * √S.τ)⁻¹ * (Wc.Cs * S.τ ^ 2 * S.nQT u) :=
          mul_le_mul_of_nonneg_left f3 (by positivity)
      _ = ((S.τ * √S.τ)⁻¹ * S.τ ^ 2) * (Wc.Cs * S.nQT u) := by ring
      _ = √S.τ * (Wc.Cs * S.nQT u) := by rw [S.rt_inv1]
      _ ≤ √S.τ * (Wc.Cs * (P.Kq * S.cj2 u)) := by gcongr
      _ = √S.τ * (Wc.Cs * P.Kq * S.cj2 u) := by ring
  unfold Setting.Cb
  unfold Setting.nQ at a b
  linarith

/-- temporal upwind term -/
theorem rem_U_time {u : X} (hu : u ∈ S.Wh) :
    -(√S.τ * (S.upw2 u + 2 * P.C * Wc.Cs * P.Kq * S.cj2 u))
      ≤ 2 * ∑ n ∈ range S.N, S.Om n (S.tjump n u) (S.bot n (E.r u)) := by
  have hrt := S.rt_pos; have hτ := S.τ_pos; have hC := P.C_pos; have hCs := Wc.Cs_pos
  have hKq := P.Kq_nonneg
  have Y := SemiIP.sum_young (range S.N) S.Om (fun n => S.tjump n u)
    (fun n => S.bot n (E.r u)) hrt
  beta_reduce at Y
  have a : ∑ n ∈ range S.N, S.Om n (S.tjump n u) (S.tjump n u) ≤ S.upw2 u := by
    unfold Setting.upw2
    have h1 : ∑ n ∈ range S.N, S.Om n (S.tjump n u) (S.tjump n u)
        ≤ ∑ n ∈ range S.N, (S.Om n (S.tjump n u) (S.tjump n u)
          + S.FQw n (S.jmp u) (S.jmp u)) :=
      sum_le_sum fun n _ => by have := (S.FQw n).nonneg (S.jmp u); linarith
    have := (S.Om S.N).nonneg (S.prev S.N u)
    linarith
  have f1 := E.bot_r_le hu
  have f2 := S.nQT_le_cj2 hu
  have b : (√S.τ)⁻¹ * ∑ n ∈ range S.N, S.Om n (S.bot n (E.r u)) (S.bot n (E.r u))
      ≤ √S.τ * (2 * P.C * Wc.Cs * P.Kq * S.cj2 u) :=
    calc (√S.τ)⁻¹ * ∑ n ∈ range S.N, S.Om n (S.bot n (E.r u)) (S.bot n (E.r u))
        ≤ (√S.τ)⁻¹ * (2 * P.C * Wc.Cs * S.τ * S.nQT u) :=
          mul_le_mul_of_nonneg_left f1 (by positivity)
      _ = ((√S.τ)⁻¹ * S.τ) * (2 * P.C * Wc.Cs * S.nQT u) := by ring
      _ = √S.τ * (2 * P.C * Wc.Cs * S.nQT u) := by rw [S.rt_inv2]
      _ ≤ √S.τ * (2 * P.C * Wc.Cs * (P.Kq * S.cj2 u)) := by gcongr
      _ = √S.τ * (2 * P.C * Wc.Cs * P.Kq * S.cj2 u) := by ring
  have a' := mul_le_mul_of_nonneg_left a hrt.le
  linarith

/-- spatial upwind term -/
theorem rem_U_facet {u : X} (hu : u ∈ S.Wh) :
    -(√S.τ * (S.c2 u + P.C ^ 2 * Wc.Cs * P.Kq * S.cj2 u))
      ≤ 2 * ∑ n ∈ range S.N, S.FQw n (S.jmp u) (S.dn (E.r u)) := by
  have hrt := S.rt_pos; have hτ := S.τ_pos; have hC := P.C_pos; have hCs := Wc.Cs_pos
  have hKq := P.Kq_nonneg; have hh := S.h_pos; have hhi := S.hinv_pos
  have hw := S.wInf_nonneg
  have hc2 := S.c2_nonneg u; have hcj := S.cj2_nonneg u; have hq := S.nQT_nonneg u
  have hjQ := S.jQ_nonneg u
  -- the two diagonal sums
  have A1 : ∑ n ∈ range S.N, S.FQw n (S.jmp u) (S.jmp u) ≤ S.wInf * S.jQ u := by
    unfold Setting.jQ
    exact sum_le_mul_sum fun n _ => S.FQw_le n (by in_range) _
  have A2 : ∑ n ∈ range S.N, S.FQw n (S.jmp u) (S.jmp u) ≤ S.c2 u := by
    refine le_trans ?_ (S.upw2_le_c2 u)
    unfold Setting.upw2
    have h1 : ∑ n ∈ range S.N, S.FQw n (S.jmp u) (S.jmp u)
        ≤ ∑ n ∈ range S.N, (S.Om n (S.tjump n u) (S.tjump n u)
          + S.FQw n (S.jmp u) (S.jmp u)) :=
      sum_le_sum fun n _ => by have := (S.Om n).nonneg (S.tjump n u); linarith
    have := (S.Om S.N).nonneg (S.prev S.N u)
    linarith
  have B1 : ∑ n ∈ range S.N, S.FQw n (S.dn (E.r u)) (S.dn (E.r u))
      ≤ S.wInf * (P.C * Wc.Cs * S.h⁻¹ * S.τ ^ 2 * S.nQT u) := by
    have h1 : ∑ n ∈ range S.N, S.FQw n (S.dn (E.r u)) (S.dn (E.r u))
        ≤ S.wInf * ∑ n ∈ range S.N, S.FQ n (S.dn (E.r u)) (S.dn (E.r u)) :=
      sum_le_mul_sum fun n _ => S.FQw_le n (by in_range) _
    exact h1.trans (mul_le_mul_of_nonneg_left (E.FQ_dn_r_le hu) hw)
  have f2 := S.nQT_le_cj2 hu
  have f3 := (S.αjQ_le_c2 u)
  cases hr : S.regime with
  | C =>
    have hcfl := S.w_τ_hinv_le hr
    have Y := SemiIP.sum_young (range S.N) S.FQw (fun _ => S.jmp u)
      (fun _ => S.dn (E.r u)) hrt
    beta_reduce at Y
    have b : (√S.τ)⁻¹ * ∑ n ∈ range S.N, S.FQw n (S.dn (E.r u)) (S.dn (E.r u))
        ≤ √S.τ * (P.C ^ 2 * Wc.Cs * P.Kq * S.cj2 u) :=
      calc (√S.τ)⁻¹ * ∑ n ∈ range S.N, S.FQw n (S.dn (E.r u)) (S.dn (E.r u))
          ≤ (√S.τ)⁻¹ * (S.wInf * (P.C * Wc.Cs * S.h⁻¹ * S.τ ^ 2 * S.nQT u)) :=
            mul_le_mul_of_nonneg_left B1 (by positivity)
        _ = ((√S.τ)⁻¹ * S.τ) * (P.C * Wc.Cs * (S.wInf * S.τ * S.h⁻¹) * S.nQT u) := by ring
        _ = √S.τ * (P.C * Wc.Cs * (S.wInf * S.τ * S.h⁻¹) * S.nQT u) := by rw [S.rt_inv2]
        _ ≤ √S.τ * (P.C * Wc.Cs * P.C * (P.Kq * S.cj2 u)) := by gcongr
        _ = √S.τ * (P.C ^ 2 * Wc.Cs * P.Kq * S.cj2 u) := by ring
    have a' := mul_le_mul_of_nonneg_left A2 hrt.le
    linarith
  | D =>
    obtain ⟨hD1, hD2⟩ := S.caseD hr
    rcases eq_or_lt_of_le hw with hw0 | hwpos
    · -- `‖w‖_∞ = 0`: the term vanishes
      have Y := SemiIP.sum_young (range S.N) S.FQw (fun _ => S.jmp u)
        (fun _ => S.dn (E.r u)) one_pos
      beta_reduce at Y
      rw [← hw0] at A1 B1
      have : 0 ≤ √S.τ * (S.c2 u + P.C ^ 2 * Wc.Cs * P.Kq * S.cj2 u) := by positivity
      simp only [zero_mul, inv_one, one_mul] at A1 B1 Y
      linarith
    · have hα : 0 < S.α := by
        rcases eq_or_lt_of_le S.α_nonneg with h0 | hpos
        · rw [← h0] at hD1; nlinarith
        · exact hpos
      have hs : 0 < √S.τ * S.α * S.h⁻¹ / S.wInf := by positivity
      have Y := SemiIP.sum_young (range S.N) S.FQw (fun _ => S.jmp u)
        (fun _ => S.dn (E.r u)) hs
      beta_reduce at Y
      have a : √S.τ * S.α * S.h⁻¹ / S.wInf * ∑ n ∈ range S.N, S.FQw n (S.jmp u) (S.jmp u)
          ≤ √S.τ * S.c2 u :=
        calc √S.τ * S.α * S.h⁻¹ / S.wInf * ∑ n ∈ range S.N, S.FQw n (S.jmp u) (S.jmp u)
            ≤ √S.τ * S.α * S.h⁻¹ / S.wInf * (S.wInf * S.jQ u) :=
              mul_le_mul_of_nonneg_left A1 hs.le
          _ = √S.τ * (S.α * (S.h⁻¹ * S.jQ u)) := by field_simp
          _ ≤ √S.τ * S.c2 u := by gcongr
      have hratio : S.wInf ^ 2 * S.τ * S.α⁻¹ ≤ P.C :=
        calc S.wInf ^ 2 * S.τ * S.α⁻¹ ≤ P.C * S.α * S.α⁻¹ := by gcongr
          _ = P.C := by field_simp
      have b : (√S.τ * S.α * S.h⁻¹ / S.wInf)⁻¹
            * ∑ n ∈ range S.N, S.FQw n (S.dn (E.r u)) (S.dn (E.r u))
          ≤ √S.τ * (P.C ^ 2 * Wc.Cs * P.Kq * S.cj2 u) :=
        calc (√S.τ * S.α * S.h⁻¹ / S.wInf)⁻¹
              * ∑ n ∈ range S.N, S.FQw n (S.dn (E.r u)) (S.dn (E.r u))
            ≤ (√S.τ * S.α * S.h⁻¹ / S.wInf)⁻¹
              * (S.wInf * (P.C * Wc.Cs * S.h⁻¹ * S.τ ^ 2 * S.nQT u)) :=
              mul_le_mul_of_nonneg_left B1 (by positivity)
          _ = ((√S.τ)⁻¹ * S.τ) * (P.C * Wc.Cs * (S.wInf ^ 2 * S.τ * S.α⁻¹) * S.nQT u) := by
              field_simp
          _ = √S.τ * (P.C * Wc.Cs * (S.wInf ^ 2 * S.τ * S.α⁻¹) * S.nQT u) := by rw [S.rt_inv2]
          _ ≤ √S.τ * (P.C * Wc.Cs * P.C * (P.Kq * S.cj2 u)) := by gcongr
          _ = √S.τ * (P.C ^ 2 * Wc.Cs * P.Kq * S.cj2 u) := by ring
      linarith

/-- diffusion volume term `A(u, r)` -/
theorem rem_A {u : X} (hu : u ∈ S.Wh) :
    -(S.τ * ((1 + Wc.Cs * P.Kg) * S.cj2 u)) ≤ 2 * S.Ab u (E.r u) := by
  have hτ := S.τ_pos; have hCs := Wc.Cs_pos; have hα := S.α_nonneg; have hKg := P.Kg_nonneg
  have hτi := S.τinv_pos
  have Y : -(S.τ * S.gQ u + S.τ⁻¹ * S.gQ (E.r u))
      ≤ 2 * ∑ n ∈ range S.N, ∑ i, S.Q n (S.dx i u) (S.dx i (E.r u)) := by
    unfold Setting.gQ Setting.gQs
    rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib, ← sum_neg_distrib]
    refine sum_le_sum fun n _ => ?_
    exact SemiIP.sum_young univ (fun _ => S.Q n) (fun i => S.dx i u)
      (fun i => S.dx i (E.r u)) hτ
  have f1 := (S.αgQ_le_c2 u).trans (S.c2_le_cj2 u)
  have f2 := (S.gQ_le_gQT (E.r u)).trans (E.gQT_r_le hu)
  have f3 := S.α_gQT_le_cj2 hu
  have b : S.α * (S.τ⁻¹ * S.gQ (E.r u)) ≤ S.τ * (Wc.Cs * P.Kg * S.cj2 u) :=
    calc S.α * (S.τ⁻¹ * S.gQ (E.r u)) ≤ S.α * (S.τ⁻¹ * (Wc.Cs * S.τ ^ 2 * S.gQT u)) := by
          gcongr
      _ = S.τ * (Wc.Cs * (S.α * S.gQT u)) := by field_simp
      _ ≤ S.τ * (Wc.Cs * (P.Kg * S.cj2 u)) := by gcongr
      _ = S.τ * (Wc.Cs * P.Kg * S.cj2 u) := by ring
  have a := mul_le_mul_of_nonneg_left f1 hτ.le
  have Y' := mul_le_mul_of_nonneg_left Y hα
  unfold Setting.Ab
  linarith

/-- Constant of `rem_N`. -/
noncomputable def KN (P : Consts) (Wc : WConsts) : ℝ :=
  P.C * P.Kg + Wc.Cs * (P.C * P.γJ⁻¹ + 1) + P.C * Wc.Cs * P.Kg + 1
    + P.lam * (1 + Wc.Cs * (P.C * P.γJ⁻¹ + 1))

theorem KN_nonneg (P : Consts) (Wc : WConsts) : 0 ≤ KN P Wc := by
  have := P.C_pos; have := P.hγJ; have := P.hlam; have := Wc.Cs_pos; have := P.Kg_nonneg
  unfold KN; positivity

/-- Nitsche terms `N_h(u, r)` -/
theorem rem_N {u : X} (hu : u ∈ S.Wh) :
    -(S.τ * (KN P Wc * S.cj2 u)) ≤ 2 * S.Nb u (E.r u) := by
  have hτ := S.τ_pos; have hCs := Wc.Cs_pos; have hα := S.α_nonneg; have hKg := P.Kg_nonneg
  have hτi := S.τinv_pos; have hh := S.h_pos; have hhi := S.hinv_pos; have hC := P.C_pos
  have hγ := P.hγJ; have hlam := P.hlam
  have hcj := S.cj2_nonneg u
  set R : ℝ := Wc.Cs * (P.C * P.γJ⁻¹ + 1) with hR
  have Y1 := SemiIP.sum_young (range S.N) S.FQ (fun _ => S.nfl u) (fun _ => S.jmp (E.r u))
    (mul_pos hh hτ)
  have Y2 := SemiIP.sum_young (range S.N) S.FQ (fun _ => S.nfl (E.r u)) (fun _ => S.jmp u)
    (mul_pos hh hτi)
  have Y3 := SemiIP.sum_young (range S.N) S.FQ (fun _ => S.jmp u) (fun _ => S.jmp (E.r u)) hτ
  beta_reduce at Y1 Y2 Y3
  have n1 := S.FQ_nfl_le (S.Wh_le_Ws hu)
  have n2 := E.FQ_nfl_r_le hu
  have g := S.α_gQT_le_cj2 hu
  have jr : S.α * (S.h⁻¹ * S.jQ (E.r u)) ≤ R * S.τ ^ 2 * S.cj2 u := E.α_jQ_r_le hu
  have ju := (S.αjQ_le_c2 u).trans (S.c2_le_cj2 u)
  -- term 1
  have t1a : S.α * (S.h * S.τ * ∑ n ∈ range S.N, S.FQ n (S.nfl u) (S.nfl u))
      ≤ S.τ * (P.C * P.Kg * S.cj2 u) :=
    calc S.α * (S.h * S.τ * ∑ n ∈ range S.N, S.FQ n (S.nfl u) (S.nfl u))
        ≤ S.α * (S.h * S.τ * (P.C * S.h⁻¹ * S.gQT u)) := by gcongr
      _ = S.τ * (P.C * (S.α * S.gQT u)) := by field_simp
      _ ≤ S.τ * (P.C * (P.Kg * S.cj2 u)) := by gcongr
      _ = S.τ * (P.C * P.Kg * S.cj2 u) := by ring
  have t1b : S.α * ((S.h * S.τ)⁻¹ * S.jQ (E.r u)) ≤ S.τ * (R * S.cj2 u) :=
    calc S.α * ((S.h * S.τ)⁻¹ * S.jQ (E.r u)) = S.τ⁻¹ * (S.α * (S.h⁻¹ * S.jQ (E.r u))) := by
          field_simp
      _ ≤ S.τ⁻¹ * (R * S.τ ^ 2 * S.cj2 u) := by gcongr
      _ = S.τ * (R * S.cj2 u) := by field_simp
  -- term 2
  have t2a : S.α * (S.h * S.τ⁻¹ * ∑ n ∈ range S.N, S.FQ n (S.nfl (E.r u)) (S.nfl (E.r u)))
      ≤ S.τ * (P.C * Wc.Cs * P.Kg * S.cj2 u) :=
    calc S.α * (S.h * S.τ⁻¹ * ∑ n ∈ range S.N, S.FQ n (S.nfl (E.r u)) (S.nfl (E.r u)))
        ≤ S.α * (S.h * S.τ⁻¹ * (P.C * Wc.Cs * S.h⁻¹ * S.τ ^ 2 * S.gQT u)) := by gcongr
      _ = S.τ * (P.C * Wc.Cs * (S.α * S.gQT u)) := by field_simp
      _ ≤ S.τ * (P.C * Wc.Cs * (P.Kg * S.cj2 u)) := by gcongr
      _ = S.τ * (P.C * Wc.Cs * P.Kg * S.cj2 u) := by ring
  have t2b : S.α * ((S.h * S.τ⁻¹)⁻¹ * S.jQ u) ≤ S.τ * S.cj2 u :=
    calc S.α * ((S.h * S.τ⁻¹)⁻¹ * S.jQ u) = S.τ * (S.α * (S.h⁻¹ * S.jQ u)) := by field_simp
      _ ≤ S.τ * S.cj2 u := by gcongr
  -- term 3
  have t3a : S.α * P.lam * S.h⁻¹ * (S.τ * S.jQ u) ≤ S.τ * (P.lam * S.cj2 u) :=
    calc S.α * P.lam * S.h⁻¹ * (S.τ * S.jQ u) = S.τ * (P.lam * (S.α * (S.h⁻¹ * S.jQ u))) := by
          ring
      _ ≤ S.τ * (P.lam * S.cj2 u) := by gcongr
  have t3b : S.α * P.lam * S.h⁻¹ * (S.τ⁻¹ * S.jQ (E.r u)) ≤ S.τ * (P.lam * R * S.cj2 u) :=
    calc S.α * P.lam * S.h⁻¹ * (S.τ⁻¹ * S.jQ (E.r u))
        = P.lam * S.τ⁻¹ * (S.α * (S.h⁻¹ * S.jQ (E.r u))) := by ring
      _ ≤ P.lam * S.τ⁻¹ * (R * S.τ ^ 2 * S.cj2 u) := by gcongr
      _ = S.τ * (P.lam * R * S.cj2 u) := by field_simp
  have Y1' := mul_le_mul_of_nonneg_left Y1 hα
  have Y2' := mul_le_mul_of_nonneg_left Y2 hα
  have Y3' := mul_le_mul_of_nonneg_left Y3 (by positivity : 0 ≤ S.α * P.lam * S.h⁻¹)
  have eN : S.Nb u (E.r u)
      = S.α * ∑ n ∈ range S.N, S.FQ n (S.nfl u) (S.jmp (E.r u))
        + S.α * ∑ n ∈ range S.N, S.FQ n (S.nfl (E.r u)) (S.jmp u)
        + S.α * P.lam * S.h⁻¹ * ∑ n ∈ range S.N, S.FQ n (S.jmp u) (S.jmp (E.r u)) := by
    unfold Setting.Nb
    simp only [sum_add_distrib, mul_sum]
  unfold Setting.jQ at t1b t2b t3a t3b
  rw [eN]
  unfold KN
  rw [← hR]
  linarith

/-- Ghost penalty term `J(u, r)` -/
theorem rem_J {u : X} (hu : u ∈ S.Wh) :
    -(S.τ * ((1 + Wc.Cs) * S.cj2 u)) ≤ 2 * S.Jb u (E.r u) := by
  have hτ := S.τ_pos; have hCs := Wc.Cs_pos; have hτi := S.τinv_pos
  have hcJ := S.cJ_nonneg
  have Y := SemiIP.sum_young (range S.N) S.j (fun _ => u) (fun _ => E.r u) hτ
  beta_reduce at Y
  have f1 := E.J2_r_le hu
  have f2 := S.J2_le_cj2 u
  have hJ := S.J2_nonneg u
  have b : S.τ⁻¹ * S.J2 (E.r u) ≤ S.τ * (Wc.Cs * S.cj2 u) :=
    calc S.τ⁻¹ * S.J2 (E.r u) ≤ S.τ⁻¹ * (Wc.Cs * S.τ ^ 2 * S.J2 u) := by gcongr
      _ = S.τ * (Wc.Cs * S.J2 u) := by field_simp
      _ ≤ S.τ * (Wc.Cs * S.cj2 u) := by gcongr
  have a := mul_le_mul_of_nonneg_left f2 hτ.le
  have Y' := mul_le_mul_of_nonneg_left Y hcJ
  unfold Setting.Jb
  unfold Setting.J2 Setting.jh at b a
  linarith

/-- Constant of the remainder estimate. -/
noncomputable def KR (P : Consts) (Wc : WConsts) : ℝ :=
  (8 * P.C + Wc.Cs * P.Kq) + (1 + 2 * P.C * Wc.Cs * P.Kq) + (1 + P.C ^ 2 * Wc.Cs * P.Kq)
    + (1 + Wc.Cs * P.Kg) + KN P Wc + (1 + Wc.Cs)

theorem KR_nonneg (P : Consts) (Wc : WConsts) : 0 ≤ KR P Wc := by
  have := P.C_pos; have := Wc.Cs_pos; have := P.Kg_nonneg; have := P.Kq_nonneg
  have := KN_nonneg P Wc
  unfold KR; positivity

/-- Constant `C` of `lemma_weighted_symm_testing`. -/
noncomputable def Kw (P : Consts) (Wc : WConsts) : ℝ := 1 + KR P Wc / 2

theorem Kw_nonneg (P : Consts) (Wc : WConsts) : 0 ≤ Kw P Wc := by
  have := KR_nonneg P Wc; unfold Kw; positivity

/-- **Remainder estimate**: `(B_h + J)(u, r) ≥ - C Δt^{1/2} |||u|||_j²`. -/
theorem remainder {u : X} (hu : u ∈ S.Wh) :
    -(Kw P Wc * √S.τ * S.tnj2 u) ≤ S.BJ u (E.r u) := by
  have hrt := S.rt_pos; have hτrt := S.τ_le_rt
  have hC := P.C_pos; have hCs := Wc.Cs_pos; have hKg := P.Kg_nonneg; have hKq := P.Kq_nonneg
  have hKN := KN_nonneg P Wc
  have hcj := S.cj2_nonneg u; have hL := S.L2_nonneg u
  have c1 := E.rem_C hu
  have c2 := E.rem_U_time hu
  have c3 := E.rem_U_facet hu
  have c4 := E.rem_A hu
  have c5 := E.rem_N hu
  have c6 := E.rem_J hu
  have u1 := mul_le_mul_of_nonneg_left ((S.upw2_le_c2 u).trans (S.c2_le_cj2 u)) hrt.le
  have u2 := mul_le_mul_of_nonneg_left (S.c2_le_cj2 u) hrt.le
  have d4 := mul_le_mul_of_nonneg_right hτrt
    (by positivity : 0 ≤ (1 + Wc.Cs * P.Kg) * S.cj2 u)
  have d5 := mul_le_mul_of_nonneg_right hτrt (by positivity : 0 ≤ KN P Wc * S.cj2 u)
  have d6 := mul_le_mul_of_nonneg_right hτrt (by positivity : 0 ≤ (1 + Wc.Cs) * S.cj2 u)
  have eU : S.Ub u (E.r u) = ∑ n ∈ range S.N, S.FQw n (S.jmp u) (S.dn (E.r u))
      + ∑ n ∈ range S.N, S.Om n (S.tjump n u) (S.bot n (E.r u)) := by
    unfold Setting.Ub; rw [sum_add_distrib]
  have key : -(√S.τ * (2 * S.L2 u + KR P Wc * S.cj2 u)) ≤ 2 * S.BJ u (E.r u) := by
    unfold Setting.BJ KR
    rw [eU]
    linarith
  have h1 : 0 ≤ √S.τ * (KR P Wc / 2 * S.L2 u) := by
    have := KR_nonneg P Wc; positivity
  have h2 : 0 ≤ √S.τ * S.cj2 u := by positivity
  unfold Kw Setting.tnj2
  linarith

/-! ### `lemma_weighted_symm_testing` -/

/-- `c_σ = ½ e^{-σT} min{1, σ}` -/
noncomputable def cσ (Wc : WConsts) : ℝ := Wc.c0 / 2 * min 1 Wc.σ

/-- **`lemma_weighted_symm_testing`**, `eq_weighted_symm_testing`:
`(B_h + J)(u, Π_t(e^{-σt}u)) ≥ c_σ ‖u‖²_{c,j} - C Δt^{1/2} |||u|||_j²`. -/
theorem weighted_symm_testing (hlam : P.lam0 Wc.Cφ ≤ P.lam) {u : X} (hu : u ∈ S.Wh) :
    cσ Wc * S.cj2 u - Kw P Wc * √S.τ * S.tnj2 u ≤ S.BJ u (E.Pw u) := by
  have hc0 := E.c0_pos; have hσ := Wc.hσ; have hα := S.α_nonneg; have hhi := S.hinv_pos
  have h1 := E.toWeight.main_part hlam hu
  have h2 := E.remainder hu
  have e : E.Pw u = E.M u + E.r u := by unfold r; abel
  rw [e, S.BJ_add]
  set m : ℝ := min 1 Wc.σ with hm
  have hm0 : 0 ≤ m := le_min zero_le_one hσ.le
  have hm1 : m ≤ 1 := min_le_left _ _
  have hmσ : m ≤ Wc.σ := min_le_right _ _
  have hup := S.upw2_nonneg u; have hnQ := S.nQ_nonneg u; have hg := S.gQ_nonneg u
  have hj := S.jQ_nonneg u; have hJ := S.J2_nonneg u
  have inner : m / 2 * S.cj2 u ≤ 1 / 2 * S.upw2 u + Wc.σ / 2 * S.nQ u
      + S.α / 2 * (S.gQ u + S.h⁻¹ * S.jQ u) + 3 / 4 * S.J2 u := by
    have p1 := mul_le_mul_of_nonneg_right hm1 hup
    have p2 := mul_le_mul_of_nonneg_right hmσ hnQ
    have p3 := mul_le_mul_of_nonneg_right hm1
      (by positivity : 0 ≤ S.α * (S.gQ u + S.h⁻¹ * S.jQ u))
    have p4 := mul_le_mul_of_nonneg_right hm1 hJ
    unfold Setting.cj2 Setting.c2
    linarith
  have := mul_le_mul_of_nonneg_left inner hc0.le
  unfold cσ
  rw [← hm]
  linarith

end ExpWeight

end StDgdg
