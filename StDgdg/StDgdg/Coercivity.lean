import StDgdg.Lapp

/-!
# Layer 2, part 3: partial integration and symmetric testing

`lemma_B_Bmc` (in the form `eq_CU_symm`, with a temporal weight), `lemma_IP_coercivity`,
`prop_symm_testing`, and the main part of `lemma_weighted_symm_testing`.
-/

namespace StDgdg

open Finset

variable {P : Consts} {ι X Fs Ts : Type*} [Fintype ι]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Fs] [Module ℝ Fs] [AddCommGroup Ts] [Module ℝ Ts]

namespace Weight

variable {S : Setting P ι X Fs Ts} {σ c0 Cφ : ℝ} (Wt : Weight S σ c0 Cφ)

/-- `‖φ^{1/2} u‖_Q²` -/
def nQW (u : X) : ℝ := ∑ n ∈ range S.N, S.Q n u (Wt.M u)
/-- `‖φ^{1/2} ∇u‖_Q²` -/
def gW (u : X) : ℝ := ∑ n ∈ range S.N, ∑ i, S.Q n (S.dx i u) (Wt.M (S.dx i u))
/-- `‖φ^{1/2} [u]‖²_{𝒬_F ∩ Q}` -/
def jmpW (u : X) : ℝ := ∑ n ∈ range S.N, S.FQ n (S.jmp u) (Wt.Mf (S.jmp u))
/-- `∑_n j_h^n(u, φ u)` -/
def jW (u : X) : ℝ := ∑ n ∈ range S.N, S.j n u (Wt.M u)
/-- `|||φ^{1/2} u|||²_{upw}` -/
def upwW (u : X) : ℝ :=
  ∑ n ∈ range S.N, (Wt.phi n * S.Om n (S.tjump n u) (S.tjump n u)
      + S.FQw n (S.jmp u) (Wt.Mf (S.jmp u)))
    + Wt.phi S.N * S.Om S.N (S.prev S.N u) (S.prev S.N u)

theorem lo_pos (n : ℕ) (hn : n < S.N) : 0 < Wt.lo n := lt_of_lt_of_le Wt.c0_pos (Wt.c0_le_lo n (by in_range))

theorem jmp_M (u : X) : S.jmp (Wt.M u) = Wt.Mf (S.jmp u) := by
  simp [Setting.jmp, Wt.up_M, Wt.dn_M]

/-! ### `lemma_B_Bmc` / `eq_CU_symm` with a weight -/

/-- Slab-wise version of `eq_CU_symm` for the test function `φ u`:
integration by parts (`Setting.ibp`) plus the upwind terms. -/
theorem slab_CU (n : ℕ) (hn : n < S.N) (u : X) :
    S.Q n (S.mat u) (Wt.M u)
      + (S.FQw n (S.jmp u) (S.dn (Wt.M u)) + S.Om n (S.tjump n u) (S.bot n (Wt.M u)))
    = 1 / 2 * (Wt.phi n * S.Om n (S.tjump n u) (S.tjump n u)
        + S.FQw n (S.jmp u) (Wt.Mf (S.jmp u)))
      + σ / 2 * S.Q n u (Wt.M u)
      + 1 / 2 * (Wt.phi (n + 1) * S.Om (n + 1) (S.top n u) (S.top n u)
        - Wt.phi n * S.Om n (S.prev n u) (S.prev n u)) := by
  have h := S.ibp n (by in_range) u (Wt.M u)
  rw [Wt.mat_M, Wt.top_M n hn, Wt.bot_M n hn, Wt.up_M, Wt.dn_M] at h
  have s1 : S.Q n u (Wt.M (S.mat u)) = S.Q n (S.mat u) (Wt.M u) := by
    rw [← Wt.Q_symm n hn, (S.Q n).symm]
  have s2 : S.FQw n (S.dn u) (Wt.Mf (S.up u)) = S.FQw n (S.up u) (Wt.Mf (S.dn u)) := by
    rw [← Wt.FQw_symm n hn, (S.FQw n).symm]
  have s3 : S.Om n (S.prev n u) (S.bot n u) = S.Om n (S.bot n u) (S.prev n u) :=
    (S.Om n).symm _ _
  rw [Wt.dn_M, Wt.bot_M n hn]
  simp only [Setting.jmp, Setting.tjump, LinearMap.sub_apply, map_sub, map_smul,
    smul_eq_mul] at h ⊢
  linear_combination (1 / 2) * h - (1 / 2) * s1 + (1 / 2) * s2 - (1 / 2) * Wt.phi n * s3

/-- **`eq_CU_symm` with weight** (first display of the main part in the proof of
`lemma_weighted_symm_testing`):
`(C + U_h)(u, φu) = ½ |||φ^{1/2}u|||²_{upw} + σ/2 ‖φ^{1/2}u‖_Q²`. -/
theorem CU_weighted (u : X) :
    S.Cb u (Wt.M u) + S.Ub u (Wt.M u) = 1 / 2 * Wt.upwW u + σ / 2 * Wt.nQW u := by
  unfold Setting.Cb Setting.Ub upwW nQW
  rw [← sum_add_distrib, sum_congr rfl (fun n hn => Wt.slab_CU n (mem_range.1 hn) u)]
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum]
  have ht := sum_range_sub (fun k => Wt.phi k * S.Om k (S.prev k u) (S.prev k u)) S.N
  have h0 : S.prev 0 u = 0 := rfl
  have hs : ∀ n, S.prev (n + 1) u = S.top n u := fun n => rfl
  simp only [h0, hs, map_zero, mul_zero, sub_zero] at ht
  rw [ht]; ring

/-! ### `lemma_IP_coercivity` -/

/-- The weighted facet inner product `(φ ·,·)_{𝒬_F^n ∩ Q}`. -/
def FQM (n : ℕ) (hn : n < S.N) : SemiIP Fs where
  B := (S.FQ n).B.compl₂ Wt.Mf
  symm a b := by
    simp only [LinearMap.compl₂_apply]
    rw [← Wt.FQ_symm n hn, (S.FQ n).symm]
  nonneg a := by
    simp only [LinearMap.compl₂_apply]
    exact le_trans (mul_nonneg (Wt.lo_pos n (by in_range)).le ((S.FQ n).nonneg a)) (Wt.FQ_lo n (by in_range) a)

theorem FQM_apply (n : ℕ) (hn : n < S.N) (a b : Fs) : Wt.FQM n hn a b = S.FQ n a (Wt.Mf b) := rfl

theorem gW_nonneg (u : X) : 0 ≤ Wt.gW u :=
  sum_nonneg fun n _ => sum_nonneg fun i _ =>
    le_trans (mul_nonneg (Wt.lo_pos n (by in_range)).le ((S.Q n).nonneg _)) (Wt.Q_lo n (by in_range) _)
theorem jmpW_nonneg (u : X) : 0 ≤ Wt.jmpW u :=
  sum_nonneg fun n _ => le_trans (mul_nonneg (Wt.lo_pos n (by in_range)).le ((S.FQ n).nonneg _)) (Wt.FQ_lo n (by in_range) _)
theorem jW_nonneg (u : X) : 0 ≤ Wt.jW u :=
  sum_nonneg fun n _ => le_trans (mul_nonneg (Wt.lo_pos n (by in_range)).le ((S.j n).nonneg _)) (Wt.j_lo n (by in_range) _)

theorem Ab_M (u : X) : S.Ab u (Wt.M u) = S.α * Wt.gW u := by
  unfold Setting.Ab gW
  simp only [Wt.dx_M]

/-- `∑_n ({∇u·n}, φ [u])_{𝒬_F^n ∩ Q}` -/
def XW (u : X) : ℝ := ∑ n ∈ range S.N, S.FQ n (S.nfl u) (Wt.Mf (S.jmp u))
/-- `∑_n ‖φ^{1/2} {∇u·n}‖²_{𝒬_F^n ∩ Q}` -/
def WW (u : X) : ℝ := ∑ n ∈ range S.N, S.FQ n (S.nfl u) (Wt.Mf (S.nfl u))

theorem Nb_M (u : X) :
    S.Nb u (Wt.M u) = S.α * (2 * Wt.XW u) + S.α * P.lam * S.h⁻¹ * Wt.jmpW u := by
  unfold Setting.Nb XW jmpW
  rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun n _ => ?_
  rw [Wt.jmp_M, Wt.nfl_M, Wt.FQ_symm n (by in_range)]
  ring

theorem young_XW {s : ℝ} (hs : 0 < s) (u : X) :
    -(s * Wt.WW u + s⁻¹ * Wt.jmpW u) ≤ 2 * Wt.XW u := by
  unfold WW jmpW XW
  rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib, ← sum_neg_distrib]
  exact sum_le_sum fun n _ => (Wt.FQM n (by in_range)).young_ge hs (S.nfl u) (S.jmp u)

/-- The bound of the weighted normal flux: discrete trace inequality, `lemma_gp_E_IpGP` for
`∇u` and `gp_inv_ineq`, slab by slab, and `M_n ≤ C_φ m_n`. -/
theorem h_WW_le {u : X} (hu : u ∈ S.Wh) :
    S.h * Wt.WW u ≤ Cφ * P.C ^ 3 * (S.h⁻¹ ^ 2 * Wt.jW u + Wt.gW u) := by
  have hC := P.C_pos; have hC1 := P.hC; have hh := S.h_pos; have hhi := S.hinv_pos
  have hCφ := Wt.Cφ_nonneg
  have slab : ∀ n, n < S.N → S.h * S.FQ n (S.nfl u) (Wt.Mf (S.nfl u))
      ≤ Cφ * P.C ^ 3 * (S.h⁻¹ ^ 2 * S.j n u (Wt.M u)
        + ∑ i, S.Q n (S.dx i u) (Wt.M (S.dx i u))) := by
    intro n hn
    have hlo := Wt.lo_pos n (by in_range)
    have f1 := Wt.FQ_hi n (by in_range) (S.nfl u)
    have f2 := S.FQ_le n (by in_range) (S.nfl u)
    have f3 := S.trace_nfl n (by in_range) u (S.Wh_le_Ws hu)
    have f4 := S.gQTs_le n hn hu
    have f5 := Wt.hi_le n (by in_range)
    have f6 := Wt.j_lo n (by in_range) u
    have f7 : Wt.lo n * S.gQs n u ≤ ∑ i, S.Q n (S.dx i u) (Wt.M (S.dx i u)) := by
      unfold Setting.gQs; rw [mul_sum]
      exact sum_le_sum fun i _ => Wt.Q_lo n (by in_range) _
    have hF := (S.FQ n).nonneg (S.nfl u)
    have hj := (S.j n).nonneg u
    have hg := S.gQs_nonneg n u
    have g1 : S.FQ n (S.nfl u) (S.nfl u)
        ≤ P.C ^ 3 * S.h⁻¹ * (S.h⁻¹ ^ 2 * S.j n u u + S.gQs n u) := by
      have a1 : S.FQ n (S.nfl u) (S.nfl u) ≤ P.C * S.h⁻¹ * S.gQTs n u := by
        unfold Setting.gQTs; linarith
      have a2 : P.C * S.h⁻¹ * S.gQTs n u
          ≤ P.C * S.h⁻¹ * (P.C * (P.C * S.h⁻¹ ^ 2 * S.j n u u + S.gQs n u)) := by gcongr
      have a3 : P.C ^ 2 * S.h⁻¹ * S.gQs n u ≤ P.C ^ 3 * S.h⁻¹ * S.gQs n u := by
        have : P.C ^ 2 ≤ P.C ^ 3 := by nlinarith [sq_nonneg P.C]
        gcongr
      linarith
    have g2 : S.FQ n (S.nfl u) (Wt.Mf (S.nfl u))
        ≤ Cφ * Wt.lo n * S.FQ n (S.nfl u) (S.nfl u) :=
      f1.trans (mul_le_mul_of_nonneg_right f5 hF)
    have g3 : Cφ * Wt.lo n * S.FQ n (S.nfl u) (S.nfl u)
        ≤ Cφ * Wt.lo n * (P.C ^ 3 * S.h⁻¹ * (S.h⁻¹ ^ 2 * S.j n u u + S.gQs n u)) :=
      mul_le_mul_of_nonneg_left g1 (by positivity)
    calc S.h * S.FQ n (S.nfl u) (Wt.Mf (S.nfl u))
        ≤ S.h * (Cφ * Wt.lo n * (P.C ^ 3 * S.h⁻¹ * (S.h⁻¹ ^ 2 * S.j n u u + S.gQs n u))) :=
          mul_le_mul_of_nonneg_left (g2.trans g3) hh.le
      _ = Cφ * P.C ^ 3 * (S.h⁻¹ ^ 2 * (Wt.lo n * S.j n u u) + Wt.lo n * S.gQs n u) := by
          field_simp
      _ ≤ Cφ * P.C ^ 3 * (S.h⁻¹ ^ 2 * S.j n u (Wt.M u)
            + ∑ i, S.Q n (S.dx i u) (Wt.M (S.dx i u))) := by gcongr
  unfold WW jW gW
  rw [mul_sum, mul_sum, ← sum_add_distrib, mul_sum]
  exact sum_le_sum fun n hn => slab n (mem_range.1 hn)

/-- `α h⁻² ∑_n j_h^n(u, φu) ≤ γ_J⁻¹ J(u, φu)`. -/
theorem α_jW_le (u : X) : S.α * S.h⁻¹ ^ 2 * Wt.jW u ≤ P.γJ⁻¹ * S.Jb u (Wt.M u) := by
  have hγ := P.hγJ; have := S.wInf_nonneg; have := S.hinv_pos; have := Wt.jW_nonneg u
  have e : P.γJ⁻¹ * S.Jb u (Wt.M u)
      = S.α * S.h⁻¹ ^ 2 * Wt.jW u + S.wInf * S.h⁻¹ * Wt.jW u := by
    unfold Setting.Jb Setting.cJ jW; field_simp
  have : 0 ≤ S.wInf * S.h⁻¹ * Wt.jW u := by positivity
  linarith

theorem Jb_M_nonneg (u : X) : 0 ≤ S.Jb u (Wt.M u) :=
  mul_nonneg S.cJ_nonneg (Wt.jW_nonneg u)

end Weight

/-- The threshold `λ₀` for the interior penalty parameter, `lemma_IP_coercivity`
(`ε = ½ + 2 C₂ C_φ + 4 C₂ C_φ / γ_J`, `λ₀ = 2ε`, `C₂ = C³`). -/
noncomputable def Consts.lam0 (P : Consts) (Cφ : ℝ) : ℝ :=
  2 * (1 / 2 + 2 * (Cφ * P.C ^ 3) + 4 * (Cφ * P.C ^ 3) * P.γJ⁻¹)

namespace Weight

variable {S : Setting P ι X Fs Ts} {σ c0 Cφ : ℝ} (Wt : Weight S σ c0 Cφ)

/-- **`lemma_IP_coercivity`**, `eq_IP_coercivity`. -/
theorem IP_coercivity (hlam : P.lam0 Cφ ≤ P.lam) {u : X} (hu : u ∈ S.Wh) :
    S.α / 2 * (Wt.gW u + S.h⁻¹ * Wt.jmpW u) - 1 / 4 * S.Jb u (Wt.M u)
      ≤ S.Ab u (Wt.M u) + S.Nb u (Wt.M u) := by
  have hC := P.C_pos; have hγ := P.hγJ; have hh := S.h_pos; have hhi := S.hinv_pos
  have hα := S.α_nonneg; have hCφ := Wt.Cφ_nonneg
  have hg := Wt.gW_nonneg u; have hj := Wt.jmpW_nonneg u; have hjW := Wt.jW_nonneg u
  have hJ := Wt.Jb_M_nonneg u
  set K₂ : ℝ := Cφ * P.C ^ 3 with hK₂
  set ε : ℝ := 1 / 2 + 2 * K₂ + 4 * K₂ * P.γJ⁻¹ with hε
  have hK₂0 : 0 ≤ K₂ := by positivity
  have hε0 : 0 < ε := by positivity
  have hεlam : ε ≤ P.lam - 1 / 2 := by
    have : P.lam0 Cφ = 2 * ε := rfl
    have : (1 : ℝ) / 2 ≤ ε := by
      have : 0 ≤ 2 * K₂ + 4 * K₂ * P.γJ⁻¹ := by positivity
      linarith
    linarith
  set κ : ℝ := K₂ / ε with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hκ1 : κ ≤ 1 / 2 := by
    rw [hκ, div_le_iff₀ hε0]
    have : 0 ≤ 4 * K₂ * P.γJ⁻¹ := by positivity
    linarith
  have hκ2 : κ * P.γJ⁻¹ ≤ 1 / 4 := by
    rw [hκ, div_mul_eq_mul_div, div_le_iff₀ hε0]
    linarith
  have F3 := Wt.h_WW_le hu
  have F4 := Wt.young_XW (div_pos hh hε0) u
  have F5 := Wt.α_jW_le u
  have b1 := mul_le_mul_of_nonneg_left F4 hα
  have b2 : S.α * (S.h / ε * Wt.WW u) ≤ 1 / 4 * S.Jb u (Wt.M u) + 1 / 2 * (S.α * Wt.gW u) := by
    have c1 := mul_le_mul_of_nonneg_right hκ2 hJ
    have c2 := mul_le_mul_of_nonneg_right hκ1 (mul_nonneg hα hg)
    calc S.α * (S.h / ε * Wt.WW u) = S.α / ε * (S.h * Wt.WW u) := by ring
      _ ≤ S.α / ε * (K₂ * (S.h⁻¹ ^ 2 * Wt.jW u + Wt.gW u)) := by gcongr
      _ = κ * (S.α * S.h⁻¹ ^ 2 * Wt.jW u) + κ * (S.α * Wt.gW u) := by rw [hκ]; ring
      _ ≤ κ * (P.γJ⁻¹ * S.Jb u (Wt.M u)) + κ * (S.α * Wt.gW u) := by gcongr
      _ ≤ 1 / 4 * S.Jb u (Wt.M u) + 1 / 2 * (S.α * Wt.gW u) := by linarith
  have b3 : S.α * ((S.h / ε)⁻¹ * Wt.jmpW u)
      ≤ S.α * P.lam * S.h⁻¹ * Wt.jmpW u - 1 / 2 * (S.α * (S.h⁻¹ * Wt.jmpW u)) := by
    have e : (S.h / ε)⁻¹ = ε * S.h⁻¹ := by field_simp
    have h0 : 0 ≤ S.α * (S.h⁻¹ * Wt.jmpW u) := by positivity
    have := mul_le_mul_of_nonneg_right hεlam h0
    rw [e]; linarith
  rw [Wt.Ab_M, Wt.Nb_M]
  linarith

/-- Symmetric testing with a weight: `eq_CU_symm` plus `lemma_IP_coercivity`. -/
theorem symm_testing_weighted (hlam : P.lam0 Cφ ≤ P.lam) {u : X} (hu : u ∈ S.Wh) :
    1 / 2 * Wt.upwW u + σ / 2 * Wt.nQW u + S.α / 2 * (Wt.gW u + S.h⁻¹ * Wt.jmpW u)
      + 3 / 4 * S.Jb u (Wt.M u) ≤ S.BJ u (Wt.M u) := by
  have h1 := Wt.CU_weighted u
  have h2 := Wt.IP_coercivity hlam hu
  unfold Setting.BJ
  linarith

/-! ### lower bounds `φ ≥ c0` -/

theorem upwW_ge (u : X) : c0 * S.upw2 u ≤ Wt.upwW u := by
  have hc := Wt.c0_pos
  unfold Setting.upw2 upwW
  rw [mul_add, mul_sum]
  refine add_le_add (sum_le_sum fun n _ => ?_) ?_
  · have h1 := mul_le_mul_of_nonneg_right (Wt.c0_le_phi n (by in_range)) ((S.Om n).nonneg (S.tjump n u))
    have h2 := mul_le_mul_of_nonneg_right (Wt.c0_le_lo n (by in_range)) ((S.FQw n).nonneg (S.jmp u))
    have h3 := Wt.FQw_lo n (by in_range) (S.jmp u)
    linarith
  · exact mul_le_mul_of_nonneg_right (Wt.c0_le_phi _ (by in_range)) ((S.Om _).nonneg _)

theorem nQW_ge (u : X) : c0 * S.nQ u ≤ Wt.nQW u := by
  unfold Setting.nQ nQW; rw [mul_sum]
  exact sum_le_sum fun n _ =>
    (mul_le_mul_of_nonneg_right (Wt.c0_le_lo n (by in_range)) ((S.Q n).nonneg u)).trans (Wt.Q_lo n (by in_range) u)

theorem gW_ge (u : X) : c0 * S.gQ u ≤ Wt.gW u := by
  unfold Setting.gQ Setting.gQs gW; rw [mul_sum]
  refine sum_le_sum fun n _ => ?_
  rw [mul_sum]
  exact sum_le_sum fun i _ =>
    (mul_le_mul_of_nonneg_right (Wt.c0_le_lo n (by in_range)) ((S.Q n).nonneg _)).trans (Wt.Q_lo n (by in_range) _)

theorem jmpW_ge (u : X) : c0 * S.jQ u ≤ Wt.jmpW u := by
  unfold Setting.jQ jmpW; rw [mul_sum]
  exact sum_le_sum fun n _ =>
    (mul_le_mul_of_nonneg_right (Wt.c0_le_lo n (by in_range)) ((S.FQ n).nonneg _)).trans (Wt.FQ_lo n (by in_range) _)

theorem Jb_M_ge (u : X) : c0 * S.J2 u ≤ S.Jb u (Wt.M u) := by
  have hcJ := S.cJ_nonneg
  have h : c0 * S.jh u ≤ Wt.jW u := by
    unfold Setting.jh jW; rw [mul_sum]
    exact sum_le_sum fun n _ =>
      (mul_le_mul_of_nonneg_right (Wt.c0_le_lo n (by in_range)) ((S.j n).nonneg _)).trans (Wt.j_lo n (by in_range) _)
  have := mul_le_mul_of_nonneg_left h hcJ
  unfold Setting.J2 Setting.Jb
  change _ ≤ S.cJ * Wt.jW u
  linarith

/-- Main part of `lemma_weighted_symm_testing` (and `prop_symm_testing` for `φ ≡ 1`). -/
theorem main_part (hlam : P.lam0 Cφ ≤ P.lam) {u : X} (hu : u ∈ S.Wh) :
    c0 * (1 / 2 * S.upw2 u + σ / 2 * S.nQ u + S.α / 2 * (S.gQ u + S.h⁻¹ * S.jQ u)
      + 3 / 4 * S.J2 u) ≤ S.BJ u (Wt.M u) := by
  have hα := S.α_nonneg; have hhi := S.hinv_pos; have hσ := Wt.σ_nonneg
  have h0 := Wt.symm_testing_weighted hlam hu
  have h1 := Wt.upwW_ge u
  have h2 := mul_le_mul_of_nonneg_left (Wt.nQW_ge u) (by positivity : (0 : ℝ) ≤ σ / 2)
  have h3 := mul_le_mul_of_nonneg_left (Wt.gW_ge u) (by positivity : (0 : ℝ) ≤ S.α / 2)
  have h4 := mul_le_mul_of_nonneg_left (Wt.jmpW_ge u)
    (by positivity : (0 : ℝ) ≤ S.α / 2 * S.h⁻¹)
  have h5 := Wt.Jb_M_ge u
  linarith

end Weight

/-- The trivial weight `φ ≡ 1`. -/
def Weight.one (S : Setting P ι X Fs Ts) : Weight S 0 1 1 where
  M := LinearMap.id
  Mf := LinearMap.id
  lo := fun _ => 1
  hi := fun _ => 1
  phi := fun _ => 1
  σ_nonneg := le_refl _
  c0_pos := one_pos
  Cφ_nonneg := zero_le_one
  c0_le_lo := fun _ _ => le_refl _
  hi_le := fun _ _ => by norm_num
  c0_le_phi := fun _ _ => le_refl _
  phi_le_one := fun _ _ => le_refl _
  dx_M := fun _ _ => rfl
  up_M := fun _ => rfl
  dn_M := fun _ => rfl
  nfl_M := fun _ => rfl
  bot_M := fun _ _ _ => by simp
  top_M := fun _ _ _ => by simp
  mat_M := fun _ => by simp
  Lc_M := fun _ => by simp
  Q_symm := fun _ _ _ _ => rfl
  j_symm := fun _ _ _ _ => rfl
  FQ_symm := fun _ _ _ _ => rfl
  FQw_symm := fun _ _ _ _ => rfl
  Q_lo := fun _ _ _ => by simp
  j_lo := fun _ _ _ => by simp
  FQ_lo := fun _ _ _ => by simp
  FQw_lo := fun _ _ _ => by simp
  FQ_hi := fun _ _ _ => by simp
  Q_contr := fun _ _ _ => by simp
  j_contr := fun _ _ _ => by simp
  FQ_contr := fun _ _ _ => by simp
  FQw_contr := fun _ _ _ => by simp

/-- **`prop_symm_testing`**, `eq_symm_testing`:
`(B_h + J)(u,u) ≥ ½ |||u|||²_{upw} + α/2 |u|²_{1,h} + ¾ |u|_J²`. -/
theorem Setting.symm_testing (S : Setting P ι X Fs Ts) (hlam : P.lam0 1 ≤ P.lam)
    {u : X} (hu : u ∈ S.Wh) :
    1 / 2 * S.upw2 u + S.α / 2 * (S.gQ u + S.h⁻¹ * S.jQ u) + 3 / 4 * S.J2 u ≤ S.BJ u u := by
  have h := (Weight.one S).main_part hlam hu
  have e : (Weight.one S).M u = u := rfl
  rw [e] at h
  linarith

end StDgdg
