import StDgdg.Setting

/-!
# Layer 2, part 1: parameter relations and Ghost-penalty consequences

`eq:ass_gp_scaling`, the global form of `lemma_gp_E_IpGP`, `eq_alpha_grad_full`
(second inequality), `lemma_bound_tn_ag_temporal_vol`.
-/

namespace StDgdg

open Finset

variable {P : Consts} {ι X Fs Ts : Type*} [Fintype ι]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Fs] [Module ℝ Fs] [AddCommGroup Ts] [Module ℝ Ts]

theorem Consts.C_pos (P : Consts) : 0 < P.C := lt_of_lt_of_le one_pos P.hC

namespace Setting

variable (S : Setting P ι X Fs Ts)

/-! ### positivity -/

theorem hinv_pos : 0 < S.h⁻¹ := inv_pos.2 S.h_pos
theorem τinv_pos : 0 < S.τ⁻¹ := inv_pos.2 S.τ_pos

theorem cJ_nonneg : 0 ≤ S.cJ := by
  have := P.hγJ; have := S.α_nonneg; have := S.wInf_nonneg; have := S.hinv_pos
  unfold cJ; positivity

theorem gQs_nonneg (n : ℕ) (u : X) : 0 ≤ S.gQs n u := sum_nonneg fun _ _ => (S.Q n).nonneg _
theorem gQTs_nonneg (n : ℕ) (u : X) : 0 ≤ S.gQTs n u := sum_nonneg fun _ _ => (S.QT n).nonneg _
theorem nQ_nonneg (u : X) : 0 ≤ S.nQ u := sum_nonneg fun n _ => (S.Q n).nonneg u
theorem nQT_nonneg (u : X) : 0 ≤ S.nQT u := sum_nonneg fun n _ => (S.QT n).nonneg u
theorem gQ_nonneg (u : X) : 0 ≤ S.gQ u := sum_nonneg fun n _ => S.gQs_nonneg n u
theorem gQT_nonneg (u : X) : 0 ≤ S.gQT u := sum_nonneg fun n _ => S.gQTs_nonneg n u
theorem jQ_nonneg (u : X) : 0 ≤ S.jQ u := sum_nonneg fun n _ => (S.FQ n).nonneg _
theorem jh_nonneg (u : X) : 0 ≤ S.jh u := sum_nonneg fun n _ => (S.j n).nonneg u
theorem J2_nonneg (u : X) : 0 ≤ S.J2 u := mul_nonneg S.cJ_nonneg (S.jh_nonneg u)
theorem upw2_nonneg (u : X) : 0 ≤ S.upw2 u :=
  add_nonneg (sum_nonneg fun n _ => add_nonneg ((S.Om n).nonneg _) ((S.FQw n).nonneg _))
    ((S.Om S.N).nonneg _)
theorem c2_nonneg (u : X) : 0 ≤ S.c2 u := by
  have := S.nQ_nonneg u; have := S.gQ_nonneg u; have := S.jQ_nonneg u
  have := S.upw2_nonneg u; have := S.α_nonneg; have := S.hinv_pos
  unfold c2; positivity
theorem cj2_nonneg (u : X) : 0 ≤ S.cj2 u := add_nonneg (S.c2_nonneg u) (S.J2_nonneg u)
theorem L2_nonneg (u : X) : 0 ≤ S.L2 u := mul_nonneg S.τ_pos.le (S.nQ_nonneg _)
theorem tnj2_nonneg (u : X) : 0 ≤ S.tnj2 u := add_nonneg (S.L2_nonneg u) (S.cj2_nonneg u)

/-! ### the parts of the norms -/

theorem nQ_le_c2 (u : X) : S.nQ u ≤ S.c2 u := by
  have := S.gQ_nonneg u; have := S.jQ_nonneg u
  have := S.upw2_nonneg u; have := S.α_nonneg; have := S.hinv_pos
  have : 0 ≤ S.α * (S.gQ u + S.h⁻¹ * S.jQ u) := by positivity
  unfold c2; linarith
theorem αgQ_le_c2 (u : X) : S.α * S.gQ u ≤ S.c2 u := by
  have := S.nQ_nonneg u; have := S.jQ_nonneg u
  have := S.upw2_nonneg u; have := S.α_nonneg; have := S.hinv_pos
  have : 0 ≤ S.α * (S.h⁻¹ * S.jQ u) := by positivity
  unfold c2; linarith
theorem αjQ_le_c2 (u : X) : S.α * (S.h⁻¹ * S.jQ u) ≤ S.c2 u := by
  have := S.nQ_nonneg u; have := S.gQ_nonneg u
  have := S.upw2_nonneg u; have := S.α_nonneg
  have : 0 ≤ S.α * S.gQ u := by positivity
  unfold c2; linarith
theorem upw2_le_c2 (u : X) : S.upw2 u ≤ S.c2 u := by
  have := S.nQ_nonneg u; have := S.gQ_nonneg u; have := S.jQ_nonneg u
  have := S.α_nonneg; have := S.hinv_pos
  have : 0 ≤ S.α * (S.gQ u + S.h⁻¹ * S.jQ u) := by positivity
  unfold c2; linarith
theorem c2_le_cj2 (u : X) : S.c2 u ≤ S.cj2 u := by
  have := S.J2_nonneg u; unfold cj2; linarith
theorem J2_le_cj2 (u : X) : S.J2 u ≤ S.cj2 u := by
  have := S.c2_nonneg u; unfold cj2; linarith
theorem cj2_le_tnj2 (u : X) : S.cj2 u ≤ S.tnj2 u := by
  have := S.L2_nonneg u; unfold tnj2; linarith
theorem L2_le_tnj2 (u : X) : S.L2 u ≤ S.tnj2 u := by
  have := S.cj2_nonneg u; unfold tnj2; linarith

/-! ### parameter relations -/

/-- `eq:ass_gp_scaling`: `Δt⁻¹ ≲ c_J`, in both regimes. -/
theorem τinv_le : S.τ⁻¹ ≤ P.C * P.γJ⁻¹ * S.cJ := by
  have hC := P.C_pos; have hγ := P.hγJ; have hh := S.h_pos; have hτ := S.τ_pos
  have hα := S.α_nonneg; have hw := S.wInf_nonneg
  have hhi := S.hinv_pos; have hτi := S.τinv_pos
  have key : S.τ⁻¹ ≤ P.C * (S.α * S.h⁻¹ ^ 2 + S.wInf * S.h⁻¹) := by
    cases hr : S.regime with
    | D =>
      obtain ⟨h1, _⟩ := S.caseD hr
      have : S.τ⁻¹ ≤ P.C * (S.α * S.h⁻¹ ^ 2) :=
        calc S.τ⁻¹ = S.h ^ 2 * (S.τ⁻¹ * S.h⁻¹ ^ 2) := by field_simp
          _ ≤ (P.C * S.α * S.τ) * (S.τ⁻¹ * S.h⁻¹ ^ 2) := by gcongr
          _ = P.C * (S.α * S.h⁻¹ ^ 2) := by field_simp
      have : 0 ≤ P.C * (S.wInf * S.h⁻¹) := by positivity
      linarith
    | C =>
      obtain ⟨_, h2⟩ := S.caseC hr
      have : S.τ⁻¹ ≤ P.C * (S.wInf * S.h⁻¹) :=
        calc S.τ⁻¹ = S.h * (S.τ⁻¹ * S.h⁻¹) := by field_simp
          _ ≤ (P.C * S.wInf * S.τ) * (S.τ⁻¹ * S.h⁻¹) := by gcongr
          _ = P.C * (S.wInf * S.h⁻¹) := by field_simp
      have : 0 ≤ P.C * (S.α * S.h⁻¹ ^ 2) := by positivity
      linarith
  have e : P.C * P.γJ⁻¹ * S.cJ = P.C * (S.α * S.h⁻¹ ^ 2 + S.wInf * S.h⁻¹) := by
    unfold cJ; field_simp
  rw [e]; exact key

/-- `∑_n j_h^n(u,u) = c_J⁻¹ |u|_J² ≲ Δt |u|_J²`. -/
theorem jh_le (u : X) : S.jh u ≤ P.C * P.γJ⁻¹ * S.τ * S.J2 u := by
  have hτ := S.τ_pos
  have h1 := mul_le_mul_of_nonneg_left S.τinv_le (mul_nonneg hτ.le (S.jh_nonneg u))
  have e1 : S.τ * S.jh u * S.τ⁻¹ = S.jh u := by field_simp
  rw [e1] at h1
  unfold J2
  linarith

/-- `α h⁻² ∑_n j_h^n(u,u) ≤ γ_J⁻¹ |u|_J²`. -/
theorem α_jh_le (u : X) : S.α * S.h⁻¹ ^ 2 * S.jh u ≤ P.γJ⁻¹ * S.J2 u := by
  have hγ := P.hγJ; have := S.wInf_nonneg; have := S.hinv_pos; have := S.jh_nonneg u
  have e : P.γJ⁻¹ * S.J2 u = S.α * S.h⁻¹ ^ 2 * S.jh u + S.wInf * S.h⁻¹ * S.jh u := by
    unfold J2 cJ; field_simp
  have : 0 ≤ S.wInf * S.h⁻¹ * S.jh u := by positivity
  linarith

/-- `‖w‖_∞ h⁻¹ ∑_n j_h^n(u,u) ≤ γ_J⁻¹ |u|_J²`. -/
theorem w_jh_le (u : X) : S.wInf * S.h⁻¹ * S.jh u ≤ P.γJ⁻¹ * S.J2 u := by
  have hγ := P.hγJ; have := S.α_nonneg; have := S.hinv_pos; have := S.jh_nonneg u
  have e : P.γJ⁻¹ * S.J2 u = S.α * S.h⁻¹ ^ 2 * S.jh u + S.wInf * S.h⁻¹ * S.jh u := by
    unfold J2 cJ; field_simp
  have : 0 ≤ S.α * S.h⁻¹ ^ 2 * S.jh u := by positivity
  linarith

/-- In Case D, `‖w‖_∞ h ≲ α` (stated after `eq:ass_gp_scaling`). -/
theorem w_h_le (hr : S.regime = .D) : S.wInf * S.h ≤ P.C * S.α := by
  obtain ⟨h1, h2⟩ := S.caseD hr
  have hC := P.C_pos; have hα := S.α_nonneg; have hw := S.wInf_nonneg; have hh := S.h_pos
  have hτ := S.τ_pos
  have hsq : (S.wInf * S.h) ^ 2 ≤ (P.C * S.α) ^ 2 :=
    calc (S.wInf * S.h) ^ 2 = S.wInf ^ 2 * S.h ^ 2 := by ring
      _ ≤ S.wInf ^ 2 * (P.C * S.α * S.τ) := by gcongr
      _ = P.C * S.α * (S.wInf ^ 2 * S.τ) := by ring
      _ ≤ P.C * S.α * (P.C * S.α) := by gcongr
      _ = (P.C * S.α) ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hsq

/-- In Case C, the CFL-type condition `‖w‖_∞ Δt h⁻¹ ≲ 1`. -/
theorem w_τ_hinv_le (hr : S.regime = .C) : S.wInf * S.τ * S.h⁻¹ ≤ P.C := by
  obtain ⟨h1, _⟩ := S.caseC hr
  have hh := S.h_pos; have hhi := S.hinv_pos
  calc S.wInf * S.τ * S.h⁻¹ ≤ P.C * S.h * S.h⁻¹ := by gcongr
    _ = P.C := by field_simp

/-! ### Ghost penalty consequences -/

/-- `lemma_gp_E_IpGP`, summed over the time slabs. -/
theorem nQT_le_jh {u : X} (hu : u ∈ S.Wh) : S.nQT u ≤ P.C * (S.jh u + S.nQ u) := by
  unfold nQT jh nQ
  rw [← sum_add_distrib]
  exact sum_le_mul_sum fun n _ => S.gp n (by in_range) u hu

/-- `lemma_gp_E_IpGP` (second form): `‖u‖²_{𝒬_T} ≲ c_J⁻¹ |u|_J² + ‖u‖_Q²`. -/
theorem nQT_le {u : X} (hu : u ∈ S.Wh) :
    S.nQT u ≤ P.C * (P.C * P.γJ⁻¹ * S.τ * S.J2 u + S.nQ u) := by
  have hC := P.C_pos
  calc S.nQT u ≤ P.C * (S.jh u + S.nQ u) := S.nQT_le_jh hu
    _ ≤ P.C * (P.C * P.γJ⁻¹ * S.τ * S.J2 u + S.nQ u) := by
        gcongr; exact S.jh_le u

/-- Constant of `τ_nQT_le`. -/
noncomputable def _root_.StDgdg.Consts.Kq (P : Consts) : ℝ := P.C * (P.C * P.γJ⁻¹ + 1)

theorem _root_.StDgdg.Consts.Kq_nonneg (P : Consts) : 0 ≤ P.Kq := by
  have := P.C_pos; have := P.hγJ; unfold Consts.Kq; positivity

/-- `‖u‖²_{𝒬_T} ≲ ‖u‖_{c,j}²` (for `Δt ≤ 1`); in particular `Δt ‖u‖²_{𝒬_T} ≲ ‖u‖²_{c,j}`. -/
theorem nQT_le_cj2 {u : X} (hu : u ∈ S.Wh) : S.nQT u ≤ P.Kq * S.cj2 u := by
  have hC := P.C_pos; have hγ := P.hγJ; have hτ := S.τ_pos; have hτ1 := S.τ_le_one
  have h1 := S.nQT_le hu
  have hJ := S.J2_le_cj2 u
  have hJ0 := S.J2_nonneg u
  have hQ := (S.nQ_le_c2 u).trans (S.c2_le_cj2 u)
  have h2 : P.C * P.γJ⁻¹ * S.τ * S.J2 u ≤ P.C * P.γJ⁻¹ * S.cj2 u :=
    calc P.C * P.γJ⁻¹ * S.τ * S.J2 u ≤ P.C * P.γJ⁻¹ * 1 * S.cj2 u := by gcongr
      _ = P.C * P.γJ⁻¹ * S.cj2 u := by ring
  calc S.nQT u ≤ P.C * (P.C * P.γJ⁻¹ * S.τ * S.J2 u + S.nQ u) := h1
    _ ≤ P.C * (P.C * P.γJ⁻¹ * S.cj2 u + S.cj2 u) := by gcongr
    _ = P.Kq * S.cj2 u := by unfold Consts.Kq; ring

theorem τ_nQT_le_cj2 {u : X} (hu : u ∈ S.Wh) : S.τ * S.nQT u ≤ P.Kq * S.cj2 u := by
  have h := S.nQT_le_cj2 hu
  have h0 := S.nQT_nonneg u
  have hτ1 := S.τ_le_one
  nlinarith

/-- Slab-wise: `‖∇u‖²_{𝒬_T^n} ≲ h⁻² j_h^n(u,u) + ‖∇u‖²_{Q^n}`
(`lemma_gp_E_IpGP` applied to `∇u ∈ [W_h]^d` and `gp_inv_ineq`). -/
theorem gQTs_le (n : ℕ) (hn : n < S.N) {u : X} (hu : u ∈ S.Wh) :
    S.gQTs n u ≤ P.C * (P.C * S.h⁻¹ ^ 2 * S.j n u u + S.gQs n u) := by
  have hC := P.C_pos
  have h1 : S.gQTs n u ≤ P.C * (∑ i, S.j n (S.dx i u) (S.dx i u) + S.gQs n u) := by
    unfold gQTs gQs
    rw [← sum_add_distrib, mul_sum]
    exact sum_le_sum fun i _ => S.gp n (by in_range) _ (S.dx_mem i u hu)
  calc S.gQTs n u ≤ P.C * (∑ i, S.j n (S.dx i u) (S.dx i u) + S.gQs n u) := h1
    _ ≤ P.C * (P.C * S.h⁻¹ ^ 2 * S.j n u u + S.gQs n u) := by
        gcongr; exact S.gp_inv_dx n (by in_range) u hu

/-- `‖∇u‖²_{𝒬_T} ≲ h⁻² ∑_n j_h^n(u,u) + ‖∇u‖_Q²`. -/
theorem gQT_le {u : X} (hu : u ∈ S.Wh) :
    S.gQT u ≤ P.C * (P.C * S.h⁻¹ ^ 2 * S.jh u + S.gQ u) := by
  unfold gQT jh gQ
  rw [mul_sum, ← sum_add_distrib]
  exact sum_le_mul_sum fun n _ => S.gQTs_le n (by in_range) hu

/-- `eq_alpha_grad_full` (second inequality):
`α ‖∇u‖²_{𝒬_T} ≲ α ‖∇u‖_Q² + γ_J⁻¹ |u|_J²`. -/
theorem α_gQT_le {u : X} (hu : u ∈ S.Wh) :
    S.α * S.gQT u ≤ P.C * S.α * S.gQ u + P.C ^ 2 * P.γJ⁻¹ * S.J2 u := by
  have hC := P.C_pos; have hα := S.α_nonneg
  have h1 := mul_le_mul_of_nonneg_left (S.gQT_le hu) hα
  have h2 := mul_le_mul_of_nonneg_left (S.α_jh_le u) (sq_nonneg P.C)
  nlinarith

/-- Constant of `α_gQT_le_cj2`. -/
noncomputable def _root_.StDgdg.Consts.Kg (P : Consts) : ℝ := P.C + P.C ^ 2 * P.γJ⁻¹

theorem _root_.StDgdg.Consts.Kg_nonneg (P : Consts) : 0 ≤ P.Kg := by
  have := P.C_pos; have := P.hγJ; unfold Consts.Kg; positivity

/-- `eq_alpha_grad_full`: `α ‖∇u‖²_{𝒬_T} ≲ ‖u‖²_{c,j}`. -/
theorem α_gQT_le_cj2 {u : X} (hu : u ∈ S.Wh) : S.α * S.gQT u ≤ P.Kg * S.cj2 u := by
  have hC := P.C_pos; have hγ := P.hγJ
  have h1 := S.α_gQT_le hu
  have h2 := (S.αgQ_le_c2 u).trans (S.c2_le_cj2 u)
  have h3 := S.J2_le_cj2 u
  have h4 : P.C * S.α * S.gQ u ≤ P.C * S.cj2 u := by
    rw [mul_assoc]; gcongr
  have h5 : P.C ^ 2 * P.γJ⁻¹ * S.J2 u ≤ P.C ^ 2 * P.γJ⁻¹ * S.cj2 u := by gcongr
  unfold Consts.Kg; linarith

theorem gQ_le_gQT (u : X) : S.gQ u ≤ S.gQT u :=
  sum_le_sum fun n _ => sum_le_sum fun i _ => S.Q_le_QT n (by in_range) _

theorem nQ_le_nQT (u : X) : S.nQ u ≤ S.nQT u := sum_le_sum fun n _ => S.Q_le_QT n (by in_range) u

/-- `Δt h² ‖∇u‖²_{𝒬_T} ≲ ‖u‖²_{c,j}` (used several times in the paper). -/
theorem τ_h2_gQT_le {u : X} (hu : u ∈ S.Wh) :
    S.τ * S.h ^ 2 * S.gQT u ≤ P.C * P.Kq * S.cj2 u := by
  have hC := P.C_pos; have hh := S.h_pos; have hτ := S.τ_pos
  have h1 : S.gQT u ≤ P.C * S.h⁻¹ ^ 2 * S.nQT u := by
    unfold gQT nQT
    exact sum_le_mul_sum fun n _ => S.inv_dx n (by in_range) u (S.Wh_le_Ws hu)
  have h2 := S.τ_nQT_le_cj2 hu
  calc S.τ * S.h ^ 2 * S.gQT u ≤ S.τ * S.h ^ 2 * (P.C * S.h⁻¹ ^ 2 * S.nQT u) := by gcongr
    _ = P.C * (S.τ * S.nQT u) := by field_simp
    _ ≤ P.C * (P.Kq * S.cj2 u) := by gcongr
    _ = P.C * P.Kq * S.cj2 u := by ring

/-- `lemma_bound_tn_ag_temporal_vol`, summed over the slabs. -/
theorem time_traces_le {u : X} (hu : u ∈ S.Wh) :
    ∑ n ∈ range S.N, (S.Om n (S.bot n u) (S.bot n u) + S.Om (n + 1) (S.top n u) (S.top n u))
      ≤ P.C * S.τ⁻¹ * S.nQT u := by
  unfold nQT
  exact sum_le_mul_sum fun n _ => S.trace_time n (by in_range) u hu

end Setting

end StDgdg
