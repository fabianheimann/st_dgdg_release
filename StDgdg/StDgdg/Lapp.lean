import StDgdg.GP

/-!
# Layer 2, part 2: the derivative test function `y = Δt 𝓛_h u`

`lemma_Lapp_tripplenorm`, `lemma_w_jumps`, `lemma_y_jumps`.
-/

namespace StDgdg

open Finset

variable {P : Consts} {ι X Fs Ts : Type*} [Fintype ι]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Fs] [Module ℝ Fs] [AddCommGroup Ts] [Module ℝ Ts]

namespace Setting

variable (S : Setting P ι X Fs Ts)

/-! ### homogeneity of the squared norms -/

theorem nQ_smul (c : ℝ) (u : X) : S.nQ (c • u) = c ^ 2 * S.nQ u := by
  unfold nQ; rw [mul_sum]; refine sum_congr rfl fun n _ => ?_
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]; ring

theorem nQT_smul (c : ℝ) (u : X) : S.nQT (c • u) = c ^ 2 * S.nQT u := by
  unfold nQT; rw [mul_sum]; refine sum_congr rfl fun n _ => ?_
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]; ring

theorem jh_smul (c : ℝ) (u : X) : S.jh (c • u) = c ^ 2 * S.jh u := by
  unfold jh; rw [mul_sum]; refine sum_congr rfl fun n _ => ?_
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]; ring

theorem J2_smul (c : ℝ) (u : X) : S.J2 (c • u) = c ^ 2 * S.J2 u := by
  unfold J2; rw [jh_smul]; ring

theorem jQ_smul (c : ℝ) (u : X) : S.jQ (c • u) = c ^ 2 * S.jQ u := by
  unfold jQ; rw [mul_sum]; refine sum_congr rfl fun n _ => ?_
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]; ring

theorem gQ_smul (c : ℝ) (u : X) : S.gQ (c • u) = c ^ 2 * S.gQ u := by
  unfold gQ gQs; rw [mul_sum]; refine sum_congr rfl fun n _ => ?_
  rw [mul_sum]; refine sum_congr rfl fun i _ => ?_
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]; ring

theorem gQT_smul (c : ℝ) (u : X) : S.gQT (c • u) = c ^ 2 * S.gQT u := by
  unfold gQT gQTs; rw [mul_sum]; refine sum_congr rfl fun n _ => ?_
  rw [mul_sum]; refine sum_congr rfl fun i _ => ?_
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]; ring

/-! ### `lemma_Lapp_tripplenorm` -/

theorem nQ_Lh_le {u : X} (hu : u ∈ S.Wh) :
    S.nQ (S.Lh u) ≤ 2 * S.nQ (S.Lc u) + 2 * P.C * S.h ^ 2 * S.gQ u := by
  unfold nQ gQ
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun n _ => ?_
  have e : S.Lh u = S.Lc u - (S.Lc u - S.Lh u) := by abel
  have h1 := (S.Q n).sub_sq_le (S.Lc u) (S.Lc u - S.Lh u)
  rw [← e] at h1
  have h2 := S.Lc_Lh n (by in_range) u hu
  unfold gQs; linarith

theorem jh_Lh_le {u : X} (hu : u ∈ S.Wh) :
    S.jh (S.Lh u) ≤ P.C * (S.τ⁻¹ ^ 2 * S.jh u + S.h ^ 2 * S.gQT u) := by
  unfold jh gQT gQTs
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  exact sum_le_mul_sum fun n _ => S.Lh_gp n (by in_range) u hu

/-- `Δt⁻¹ ∑_n j_h^n(u,u) ≲ |u|_J²`. -/
theorem τinv_jh_le (u : X) : S.τ⁻¹ * S.jh u ≤ P.C * P.γJ⁻¹ * S.J2 u := by
  have hτ := S.τ_pos
  have h := mul_le_mul_of_nonneg_left (S.jh_le u) S.τinv_pos.le
  have e : S.τ⁻¹ * (P.C * P.γJ⁻¹ * S.τ * S.J2 u) = P.C * P.γJ⁻¹ * S.J2 u := by field_simp
  rw [e] at h; exact h

/-- Constant of `τ_nQT_Lh_le`. -/
noncomputable def _root_.StDgdg.Consts.KL (P : Consts) : ℝ :=
  2 * P.C + P.C ^ 3 * P.γJ⁻¹ + 3 * P.C ^ 3 * P.Kq

theorem _root_.StDgdg.Consts.KL_nonneg (P : Consts) : 0 ≤ P.KL := by
  have := P.C_pos; have := P.hγJ; have := P.Kq_nonneg; unfold Consts.KL; positivity

/-- `eq_Lapp_tripplenorm`, first term: `Δt ‖𝓛_h u‖²_{𝒬_T} ≲ |||u|||_j²`. -/
theorem τ_nQT_Lh_le {u : X} (hu : u ∈ S.Wh) :
    S.τ * S.nQT (S.Lh u) ≤ P.KL * S.tnj2 u := by
  have hC := P.C_pos; have hγ := P.hγJ; have hτ := S.τ_pos; have hKq := P.Kq_nonneg
  have hh := S.h_pos
  have f1 := S.nQT_le_jh (S.Lh_mem u hu)
  have f2 := S.jh_Lh_le hu
  have f3 := S.nQ_Lh_le hu
  have f4 := S.τinv_jh_le u
  have f5 := S.τ_h2_gQT_le hu
  have f6 := S.gQ_le_gQT u
  have f7 := S.J2_le_cj2 u
  have hcj := S.cj2_nonneg u
  have hL := S.L2_nonneg u
  have hg := S.gQ_nonneg u
  -- multiply out
  have g1 : S.τ * S.nQT (S.Lh u) ≤ S.τ * (P.C * (S.jh (S.Lh u) + S.nQ (S.Lh u))) := by gcongr
  have g2 : S.τ * P.C * S.jh (S.Lh u)
      ≤ S.τ * P.C * (P.C * (S.τ⁻¹ ^ 2 * S.jh u + S.h ^ 2 * S.gQT u)) := by gcongr
  have g3 : S.τ * P.C * S.nQ (S.Lh u)
      ≤ S.τ * P.C * (2 * S.nQ (S.Lc u) + 2 * P.C * S.h ^ 2 * S.gQ u) := by gcongr
  have e4 : S.τ * P.C * (P.C * (S.τ⁻¹ ^ 2 * S.jh u)) = P.C ^ 2 * (S.τ⁻¹ * S.jh u) := by
    field_simp
  have g4 : P.C ^ 2 * (S.τ⁻¹ * S.jh u) ≤ P.C ^ 2 * (P.C * P.γJ⁻¹ * S.cj2 u) := by
    exact mul_le_mul_of_nonneg_left
      (f4.trans (mul_le_mul_of_nonneg_left f7 (by positivity))) (by positivity)
  have g5 : P.C ^ 2 * (S.τ * S.h ^ 2 * S.gQT u) ≤ P.C ^ 2 * (P.C * P.Kq * S.cj2 u) := by gcongr
  have g6 : 2 * P.C ^ 2 * (S.τ * S.h ^ 2 * S.gQ u) ≤ 2 * P.C ^ 2 * (P.C * P.Kq * S.cj2 u) := by
    exact mul_le_mul_of_nonneg_left
      (le_trans (mul_le_mul_of_nonneg_left f6 (by positivity)) f5) (by positivity)
  have key : S.τ * S.nQT (S.Lh u)
      ≤ 2 * P.C * S.L2 u + (P.C ^ 3 * P.γJ⁻¹ + 3 * P.C ^ 3 * P.Kq) * S.cj2 u := by
    unfold L2; nlinarith
  have hA : 0 ≤ P.C ^ 3 * P.γJ⁻¹ + 3 * P.C ^ 3 * P.Kq := by positivity
  have hB : 0 ≤ 2 * P.C := by positivity
  unfold tnj2 Consts.KL
  nlinarith [mul_nonneg hA hL, mul_nonneg hB hcj]

/-- Constant of `J2_y_le`. -/
noncomputable def _root_.StDgdg.Consts.KLJ (P : Consts) : ℝ :=
  P.C + P.C * P.γJ * P.Kg + P.C * P.γJ * (P.C * P.Kg + P.C ^ 2 * P.Kq)

theorem _root_.StDgdg.Consts.KLJ_nonneg (P : Consts) : 0 ≤ P.KLJ := by
  have := P.C_pos; have := P.hγJ; have := P.Kq_nonneg; have := P.Kg_nonneg
  unfold Consts.KLJ; positivity

/-- `‖w‖_∞ h Δt² ‖∇u‖²_{𝒬_T} ≲ ‖u‖²_{c,j}`, in both regimes. -/
theorem w_h_τ2_gQT_le {u : X} (hu : u ∈ S.Wh) :
    S.wInf * S.h * S.τ ^ 2 * S.gQT u ≤ (P.C * P.Kg + P.C ^ 2 * P.Kq) * S.cj2 u := by
  have hC := P.C_pos; have hτ := S.τ_pos; have hτ1 := S.τ_le_one; have hh := S.h_pos
  have hw := S.wInf_nonneg; have hα := S.α_nonneg
  have hKq := P.Kq_nonneg; have hKg := P.Kg_nonneg
  have hcj := S.cj2_nonneg u; have hg := S.gQT_nonneg u
  have hτ2 : S.τ ^ 2 ≤ 1 := by nlinarith
  cases hr : S.regime with
  | D =>
    have h1 := S.w_h_le hr
    have h2 := S.α_gQT_le_cj2 hu
    have h3 : S.wInf * S.h * S.τ ^ 2 * S.gQT u ≤ P.C * P.Kg * S.cj2 u :=
      calc S.wInf * S.h * S.τ ^ 2 * S.gQT u ≤ (P.C * S.α) * 1 * S.gQT u := by gcongr
        _ = P.C * (S.α * S.gQT u) := by ring
        _ ≤ P.C * (P.Kg * S.cj2 u) := by gcongr
        _ = P.C * P.Kg * S.cj2 u := by ring
    have : 0 ≤ P.C ^ 2 * P.Kq * S.cj2 u := by positivity
    linarith
  | C =>
    have h1 := S.w_τ_hinv_le hr
    have h2 : S.gQT u ≤ P.C * S.h⁻¹ ^ 2 * S.nQT u := by
      unfold gQT nQT
      exact sum_le_mul_sum fun n _ => S.inv_dx n (by in_range) u (S.Wh_le_Ws hu)
    have h3 := S.τ_nQT_le_cj2 hu
    have hq := S.nQT_nonneg u
    have h4 : S.wInf * S.h * S.τ ^ 2 * S.gQT u ≤ P.C ^ 2 * P.Kq * S.cj2 u :=
      calc S.wInf * S.h * S.τ ^ 2 * S.gQT u
          ≤ S.wInf * S.h * S.τ ^ 2 * (P.C * S.h⁻¹ ^ 2 * S.nQT u) := by gcongr
        _ = P.C * (S.wInf * S.τ * S.h⁻¹) * (S.τ * S.nQT u) := by field_simp
        _ ≤ P.C * P.C * (P.Kq * S.cj2 u) := by gcongr
        _ = P.C ^ 2 * P.Kq * S.cj2 u := by ring
    have : 0 ≤ P.C * P.Kg * S.cj2 u := by positivity
    linarith

/-- `eq_Lapp_tripplenorm`, second term: `|Δt 𝓛_h u|_J² ≲ ‖u‖²_{c,j}`. -/
theorem J2_y_le {u : X} (hu : u ∈ S.Wh) : S.J2 (S.τ • S.Lh u) ≤ P.KLJ * S.cj2 u := by
  have hC := P.C_pos; have hγ := P.hγJ; have hτ := S.τ_pos; have hτ1 := S.τ_le_one
  have hh := S.h_pos; have hα := S.α_nonneg; have hw := S.wInf_nonneg
  have hcJ := S.cJ_nonneg
  have hKq := P.Kq_nonneg; have hKg := P.Kg_nonneg
  have hcj := S.cj2_nonneg u; have hg := S.gQT_nonneg u
  have hτ2 : S.τ ^ 2 ≤ 1 := by nlinarith
  have f2 := S.jh_Lh_le hu
  have f3 := S.α_gQT_le_cj2 hu
  have f4 := S.w_h_τ2_gQT_le hu
  have f5 := S.J2_le_cj2 u
  rw [J2_smul]
  have g1 : S.τ ^ 2 * S.J2 (S.Lh u)
      ≤ S.τ ^ 2 * (S.cJ * (P.C * (S.τ⁻¹ ^ 2 * S.jh u + S.h ^ 2 * S.gQT u))) := by
    unfold J2; gcongr
  have e1 : S.τ ^ 2 * (S.cJ * (P.C * (S.τ⁻¹ ^ 2 * S.jh u + S.h ^ 2 * S.gQT u)))
      = P.C * S.J2 u + P.C * P.γJ * (S.τ ^ 2 * (S.α * S.gQT u))
        + P.C * P.γJ * (S.wInf * S.h * S.τ ^ 2 * S.gQT u) := by
    unfold J2 cJ; field_simp; ring
  have g2 : S.τ ^ 2 * (S.α * S.gQT u) ≤ P.Kg * S.cj2 u := by
    have : 0 ≤ S.α * S.gQT u := by positivity
    nlinarith
  have g3 : P.C * P.γJ * (S.τ ^ 2 * (S.α * S.gQT u)) ≤ P.C * P.γJ * (P.Kg * S.cj2 u) := by gcongr
  have g4 : P.C * P.γJ * (S.wInf * S.h * S.τ ^ 2 * S.gQT u)
      ≤ P.C * P.γJ * ((P.C * P.Kg + P.C ^ 2 * P.Kq) * S.cj2 u) := by gcongr
  have g5 : P.C * S.J2 u ≤ P.C * S.cj2 u := by gcongr
  rw [e1] at g1
  unfold Consts.KLJ
  linarith

/-- `eq_alpha_grad_full`, first inequality: `α ‖Δt ∇𝓛_h u‖²_{𝒬_T} ≲ ‖u‖²_{c,j}`. -/
theorem α_gQT_y_le {u : X} (hu : u ∈ S.Wh) :
    S.α * S.gQT (S.τ • S.Lh u) ≤ P.C * P.Kg * S.cj2 u := by
  have hC := P.C_pos; have hτ := S.τ_pos; have hα := S.α_nonneg
  have h1 : S.gQT (S.Lh u) ≤ P.C * S.τ⁻¹ ^ 2 * S.gQT u := by
    unfold gQT gQTs
    exact sum_le_mul_sum fun n _ => S.Lh_inv_grad n (by in_range) u hu
  have h2 := S.α_gQT_le_cj2 hu
  rw [gQT_smul]
  calc S.α * (S.τ ^ 2 * S.gQT (S.Lh u)) ≤ S.α * (S.τ ^ 2 * (P.C * S.τ⁻¹ ^ 2 * S.gQT u)) := by
        gcongr
    _ = P.C * (S.α * S.gQT u) := by field_simp
    _ ≤ P.C * (P.Kg * S.cj2 u) := by gcongr
    _ = P.C * P.Kg * S.cj2 u := by ring

/-! ### `lemma_w_jumps` -/

/-- `lemma_w_jumps`, Case D. -/
theorem w_jQ_le_D (hr : S.regime = .D) (v : X) :
    S.wInf * S.jQ v ≤ P.C * (S.α * (S.h⁻¹ * S.jQ v)) := by
  have hh := S.h_pos; have hj := S.jQ_nonneg v; have hhi := S.hinv_pos
  have h1 := S.w_h_le hr
  calc S.wInf * S.jQ v = (S.wInf * S.h) * (S.h⁻¹ * S.jQ v) := by field_simp
    _ ≤ (P.C * S.α) * (S.h⁻¹ * S.jQ v) := by gcongr
    _ = P.C * (S.α * (S.h⁻¹ * S.jQ v)) := by ring

/-- jumps on the full facets are bounded by the two traces (slab-wise). -/
theorem Ffull_jmp_le (n : ℕ) (hn : n < S.N) {v : X} (hv : v ∈ S.Ws) :
    S.Ffull n (S.jmp v) ≤ 4 * P.C * S.h⁻¹ * S.QT n v v := by
  have h1 := (S.Fgp n).sub_sq_le (S.dn v) (S.up v)
  have h2 := (S.Fint n).sub_sq_le (S.dn v) (S.up v)
  have h3 := S.trace_up n (by in_range) v hv
  have h4 := S.trace_dn n (by in_range) v hv
  unfold Ffull jmp
  simp only [LinearMap.sub_apply]
  linarith

/-- `lemma_w_jumps`, Case C (with the physical facet parts on the left). -/
theorem w_jQ_le_C (hr : S.regime = .C) {v : X} (hv : v ∈ S.Ws) :
    S.wInf * S.jQ v ≤ 4 * P.C ^ 2 * S.τ⁻¹ * S.nQT v := by
  have hC := P.C_pos; have hh := S.h_pos; have hτ := S.τ_pos; have hw := S.wInf_nonneg
  have hq := S.nQT_nonneg v
  have h1 := S.w_τ_hinv_le hr
  have h2 : S.jQ v ≤ 4 * P.C * S.h⁻¹ * S.nQT v := by
    unfold jQ nQT
    refine sum_le_mul_sum fun n _ => ?_
    exact (S.FQ_le n (by in_range) _).trans (S.Ffull_jmp_le n (by in_range) hv)
  calc S.wInf * S.jQ v ≤ S.wInf * (4 * P.C * S.h⁻¹ * S.nQT v) := by gcongr
    _ = 4 * P.C * (S.wInf * S.τ * S.h⁻¹) * (S.τ⁻¹ * S.nQT v) := by field_simp
    _ ≤ 4 * P.C * P.C * (S.τ⁻¹ * S.nQT v) := by gcongr
    _ = 4 * P.C ^ 2 * S.τ⁻¹ * S.nQT v := by ring

/-! ### `lemma_y_jumps` -/

/-- Constant of `α_jQ_y_le`. -/
noncomputable def _root_.StDgdg.Consts.Ky1 (P : Consts) : ℝ :=
  P.C * (P.γJ⁻¹ * P.KLJ + 1 + P.Kg)

theorem _root_.StDgdg.Consts.Ky1_nonneg (P : Consts) : 0 ≤ P.Ky1 := by
  have := P.C_pos; have := P.hγJ; have := P.KLJ_nonneg; have := P.Kg_nonneg
  unfold Consts.Ky1; positivity

/-- jumps of `𝓛_h u`: stabilised facets by the Ghost penalty, interior facets by the
temporal inverse inequality. -/
theorem jQ_Lh_le {u : X} (hu : u ∈ S.Wh) :
    S.jQ (S.Lh u) ≤ P.C * S.h⁻¹ * S.jh (S.Lh u)
      + P.C * S.τ⁻¹ ^ 2 * (S.jQ u + S.h * S.gQT u) := by
  have hC := P.C_pos; have hτi := S.τinv_pos
  unfold jQ jh gQT
  rw [mul_sum, mul_sum, ← sum_add_distrib, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun n _ => ?_
  have h1 := S.FQ_le n (by in_range) (S.jmp (S.Lh u))
  have h2 := S.gp_facet n (by in_range) (S.Lh u) (S.Lh_mem u hu)
  have h3 := S.Lh_int_jump n (by in_range) u hu
  have h4 := S.Fint_le_FQ n (by in_range) (S.jmp u)
  have h5 : P.C * S.τ⁻¹ ^ 2 * (S.Fint n (S.jmp u) (S.jmp u) + S.h * S.gQTs n u)
      ≤ P.C * S.τ⁻¹ ^ 2 * (S.FQ n (S.jmp u) (S.jmp u) + S.h * S.gQTs n u) := by gcongr
  unfold jmp at *
  simp only [LinearMap.sub_apply] at *
  unfold gQTs at *
  linarith

/-- `lemma_y_jumps`, diffusive part: `α h⁻¹ ‖[y]‖²_{𝒬_F ∩ Q} ≲ ‖u‖²_{c,j}`. -/
theorem α_jQ_y_le {u : X} (hu : u ∈ S.Wh) :
    S.α * (S.h⁻¹ * S.jQ (S.τ • S.Lh u)) ≤ P.Ky1 * S.cj2 u := by
  have hC := P.C_pos; have hγ := P.hγJ; have hτ := S.τ_pos; have hh := S.h_pos
  have hα := S.α_nonneg; have hhi := S.hinv_pos
  have hKLJ := P.KLJ_nonneg; have hKg := P.Kg_nonneg
  have f1 := S.jQ_Lh_le hu
  have f2 := S.α_jh_le (S.τ • S.Lh u)
  have f3 := S.J2_y_le hu
  have f4 := S.αjQ_le_c2 u
  have f5 := S.c2_le_cj2 u
  have f6 := S.α_gQT_le_cj2 hu
  rw [jh_smul] at f2
  rw [jQ_smul]
  have g1 : S.α * (S.h⁻¹ * (S.τ ^ 2 * S.jQ (S.Lh u)))
      ≤ S.α * (S.h⁻¹ * (S.τ ^ 2 * (P.C * S.h⁻¹ * S.jh (S.Lh u)
        + P.C * S.τ⁻¹ ^ 2 * (S.jQ u + S.h * S.gQT u)))) := by gcongr
  have e1 : S.α * (S.h⁻¹ * (S.τ ^ 2 * (P.C * S.h⁻¹ * S.jh (S.Lh u)
        + P.C * S.τ⁻¹ ^ 2 * (S.jQ u + S.h * S.gQT u))))
      = P.C * (S.α * S.h⁻¹ ^ 2 * (S.τ ^ 2 * S.jh (S.Lh u)))
        + P.C * (S.α * (S.h⁻¹ * S.jQ u)) + P.C * (S.α * S.gQT u) := by
    field_simp
    ring
  have g2 : P.C * (S.α * S.h⁻¹ ^ 2 * (S.τ ^ 2 * S.jh (S.Lh u)))
      ≤ P.C * (P.γJ⁻¹ * (P.KLJ * S.cj2 u)) := by
    exact mul_le_mul_of_nonneg_left
      (f2.trans (mul_le_mul_of_nonneg_left f3 (by positivity))) hC.le
  have g3 : P.C * (S.α * (S.h⁻¹ * S.jQ u)) ≤ P.C * S.cj2 u := by
    gcongr; exact f4.trans f5
  have g4 : P.C * (S.α * S.gQT u) ≤ P.C * (P.Kg * S.cj2 u) := by gcongr
  rw [e1] at g1
  unfold Consts.Ky1
  linarith

/-- Constant of `y_jumps`. -/
noncomputable def _root_.StDgdg.Consts.Ky (P : Consts) : ℝ :=
  P.Ky1 + P.C * P.Ky1 + 4 * P.C ^ 2 * P.KL

theorem _root_.StDgdg.Consts.Ky_nonneg (P : Consts) : 0 ≤ P.Ky := by
  have := P.C_pos; have := P.Ky1_nonneg; have := P.KL_nonneg
  unfold Consts.Ky; positivity

/-- `lemma_y_jumps`, convective part: `‖w‖_∞ ‖[y]‖²_{𝒬_F ∩ Q} ≲ |||u|||_j²`. -/
theorem w_jQ_y_le {u : X} (hu : u ∈ S.Wh) :
    S.wInf * S.jQ (S.τ • S.Lh u) ≤ (P.C * P.Ky1 + 4 * P.C ^ 2 * P.KL) * S.tnj2 u := by
  have hC := P.C_pos; have hτ := S.τ_pos
  have hKy1 := P.Ky1_nonneg; have hKL := P.KL_nonneg
  have ht := S.tnj2_nonneg u
  have hct := S.cj2_le_tnj2 u
  cases hr : S.regime with
  | D =>
    have h1 := S.w_jQ_le_D hr (S.τ • S.Lh u)
    have h2 := S.α_jQ_y_le hu
    have h3 : S.wInf * S.jQ (S.τ • S.Lh u) ≤ P.C * P.Ky1 * S.tnj2 u :=
      calc S.wInf * S.jQ (S.τ • S.Lh u) ≤ P.C * (S.α * (S.h⁻¹ * S.jQ (S.τ • S.Lh u))) := h1
        _ ≤ P.C * (P.Ky1 * S.tnj2 u) :=
            mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left hct hKy1)) hC.le
        _ = P.C * P.Ky1 * S.tnj2 u := by ring
    have : 0 ≤ 4 * P.C ^ 2 * P.KL * S.tnj2 u := by positivity
    linarith
  | C =>
    have hy : S.τ • S.Lh u ∈ S.Ws := S.Wh_le_Ws (S.Wh.smul_mem _ (S.Lh_mem u hu))
    have h1 := S.w_jQ_le_C hr hy
    have h2 := S.τ_nQT_Lh_le hu
    rw [nQT_smul] at h1
    have h3 : S.wInf * S.jQ (S.τ • S.Lh u) ≤ 4 * P.C ^ 2 * P.KL * S.tnj2 u :=
      calc S.wInf * S.jQ (S.τ • S.Lh u) ≤ 4 * P.C ^ 2 * S.τ⁻¹ * (S.τ ^ 2 * S.nQT (S.Lh u)) := h1
        _ = 4 * P.C ^ 2 * (S.τ * S.nQT (S.Lh u)) := by field_simp
        _ ≤ 4 * P.C ^ 2 * (P.KL * S.tnj2 u) := by gcongr
        _ = 4 * P.C ^ 2 * P.KL * S.tnj2 u := by ring
    have : 0 ≤ P.C * P.Ky1 * S.tnj2 u := by positivity
    linarith

/-- `lemma_y_jumps`. -/
theorem y_jumps {u : X} (hu : u ∈ S.Wh) :
    S.α * (S.h⁻¹ * S.jQ (S.τ • S.Lh u)) + S.wInf * S.jQ (S.τ • S.Lh u) ≤ P.Ky * S.tnj2 u := by
  have h1 := S.α_jQ_y_le hu
  have h2 := S.w_jQ_y_le hu
  have h3 := S.cj2_le_tnj2 u
  have hKy1 := P.Ky1_nonneg
  have : P.Ky1 * S.cj2 u ≤ P.Ky1 * S.tnj2 u := by gcongr
  unfold Consts.Ky
  linarith

end Setting

end StDgdg
