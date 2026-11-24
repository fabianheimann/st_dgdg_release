import StDgdg.Coercivity

/-!
# Layer 2, part 4: `lemma_weighted_symm_testing`

Properties of the remainder `r = (Π_t - Id)(φ u)` (`eq_r_props`, `eq_r_jumps`) and the
estimate of `(B_h + J)(u, r)`.
-/

namespace StDgdg

open Finset Real

variable {P : Consts} {ι X Fs Ts : Type*} [Fintype ι]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Fs] [Module ℝ Fs] [AddCommGroup Ts] [Module ℝ Ts]

namespace Setting

variable (S : Setting P ι X Fs Ts)

/-! ### `√Δt` -/

theorem rt_pos : 0 < √S.τ := Real.sqrt_pos.2 S.τ_pos
theorem rt_mul_self : √S.τ * √S.τ = S.τ := Real.mul_self_sqrt S.τ_pos.le
theorem rt_le_one : √S.τ ≤ 1 := by
  have := Real.sqrt_le_sqrt S.τ_le_one
  simpa using this
theorem τ_le_rt : S.τ ≤ √S.τ := by
  have h1 := S.rt_pos; have h2 := S.rt_le_one; have h3 := S.rt_mul_self
  nlinarith
theorem rt_inv1 : (S.τ * √S.τ)⁻¹ * S.τ ^ 2 = √S.τ := by
  have h1 := S.rt_pos; have h2 := S.τ_pos; have h3 := S.rt_mul_self
  rw [inv_mul_eq_div, div_eq_iff (by positivity)]
  calc S.τ ^ 2 = S.τ * (√S.τ * √S.τ) := by rw [h3]; ring
    _ = √S.τ * (S.τ * √S.τ) := by ring
theorem rt_inv2 : (√S.τ)⁻¹ * S.τ = √S.τ := by
  have h1 := S.rt_pos; have h3 := S.rt_mul_self
  rw [inv_mul_eq_div, div_eq_iff (by positivity)]
  exact h3.symm

/-! ### the material derivative versus `𝓛` -/

theorem nQ_add_le (x y : X) : S.nQ (x + y) ≤ 2 * S.nQ x + 2 * S.nQ y := by
  unfold nQ
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  exact sum_le_sum fun n _ => (S.Q n).add_sq_le x y

theorem nQ_mat_sub_Lc_le (u : X) : S.nQ (S.mat u - S.Lc u) ≤ 4 * S.wInf ^ 2 * S.gQ u := by
  unfold nQ gQ
  refine sum_le_mul_sum fun n _ => ?_
  have e : S.mat u - S.Lc u = (S.mat u - S.dt u) - (S.Lc u - S.dt u) := by abel
  have h1 := (S.Q n).sub_sq_le (S.mat u - S.dt u) (S.Lc u - S.dt u)
  rw [← e] at h1
  have h2 := S.mat_dt n (by in_range) u
  have h3 := S.Lc_dt n (by in_range) u
  unfold gQs; linarith

/-- `Δt ‖w^*·∇^* u‖_Q² ≲ Δt ‖𝓛u‖_Q² + α ‖∇u‖_Q²` in both regimes. -/
theorem τ_nQ_mat_le (u : X) :
    S.τ * S.nQ (S.mat u) ≤ 2 * S.L2 u + 8 * P.C * (S.α * S.gQ u) := by
  have hC := P.C_pos; have hτ := S.τ_pos; have hα := S.α_nonneg
  have hg := S.gQ_nonneg u; have hL := S.L2_nonneg u
  cases hr : S.regime with
  | D =>
    obtain ⟨_, h2⟩ := S.caseD hr
    have e : S.mat u = S.Lc u + (S.mat u - S.Lc u) := by abel
    have f1 := S.nQ_add_le (S.Lc u) (S.mat u - S.Lc u)
    rw [← e] at f1
    have f2 := S.nQ_mat_sub_Lc_le u
    have f3 : S.τ * (4 * S.wInf ^ 2 * S.gQ u) ≤ 4 * P.C * (S.α * S.gQ u) :=
      calc S.τ * (4 * S.wInf ^ 2 * S.gQ u) = 4 * (S.wInf ^ 2 * S.τ) * S.gQ u := by ring
        _ ≤ 4 * (P.C * S.α) * S.gQ u := by gcongr
        _ = 4 * P.C * (S.α * S.gQ u) := by ring
    have g1 := mul_le_mul_of_nonneg_left f1 hτ.le
    have g2 := mul_le_mul_of_nonneg_left f2 hτ.le
    unfold L2
    linarith
  | C =>
    rw [S.mat_Lc hr]
    have : 0 ≤ 8 * P.C * (S.α * S.gQ u) := by positivity
    unfold L2 at *
    linarith

/-- full-facet bound of the normal flux for piecewise polynomials in space -/
theorem FQ_nfl_le {v : X} (hv : v ∈ S.Ws) :
    ∑ n ∈ range S.N, S.FQ n (S.nfl v) (S.nfl v) ≤ P.C * S.h⁻¹ * S.gQT v := by
  unfold gQT
  refine sum_le_mul_sum fun n _ => ?_
  exact (S.FQ_le n (by in_range) _).trans (S.trace_nfl n (by in_range) v hv)

theorem FQ_dn_le {v : X} (hv : v ∈ S.Ws) :
    ∑ n ∈ range S.N, S.FQ n (S.dn v) (S.dn v) ≤ P.C * S.h⁻¹ * S.nQT v := by
  unfold nQT
  refine sum_le_mul_sum fun n _ => ?_
  exact (S.FQ_le n (by in_range) _).trans (S.trace_dn n (by in_range) v hv)

/-! ### linearity of the bilinear forms in the test function -/

theorem Cb_add (u v w : X) : S.Cb u (v + w) = S.Cb u v + S.Cb u w := by
  unfold Cb; simp only [map_add, sum_add_distrib]
theorem Cb_smul (c : ℝ) (u v : X) : S.Cb u (c • v) = c * S.Cb u v := by
  unfold Cb; simp only [map_smul, smul_eq_mul, mul_sum]
theorem Ab_add (u v w : X) : S.Ab u (v + w) = S.Ab u v + S.Ab u w := by
  unfold Ab; simp only [map_add, sum_add_distrib, mul_add]
theorem Ab_smul (c : ℝ) (u v : X) : S.Ab u (c • v) = c * S.Ab u v := by
  unfold Ab; simp only [map_smul, smul_eq_mul, ← mul_sum]; ring
theorem Ub_add (u v w : X) : S.Ub u (v + w) = S.Ub u v + S.Ub u w := by
  unfold Ub; simp only [map_add, ← sum_add_distrib]
  refine sum_congr rfl fun n _ => ?_; ring
theorem Ub_smul (c : ℝ) (u v : X) : S.Ub u (c • v) = c * S.Ub u v := by
  unfold Ub; simp only [map_smul, smul_eq_mul, mul_sum]
  refine sum_congr rfl fun n _ => ?_; ring
theorem Nb_add (u v w : X) : S.Nb u (v + w) = S.Nb u v + S.Nb u w := by
  unfold Nb; simp only [map_add, LinearMap.add_apply, ← sum_add_distrib]
  refine sum_congr rfl fun n _ => ?_; ring
theorem Nb_smul (c : ℝ) (u v : X) : S.Nb u (c • v) = c * S.Nb u v := by
  unfold Nb; simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, mul_sum]
  refine sum_congr rfl fun n _ => ?_; ring
theorem Jb_add (u v w : X) : S.Jb u (v + w) = S.Jb u v + S.Jb u w := by
  unfold Jb; simp only [map_add, sum_add_distrib, mul_add]
theorem Jb_smul (c : ℝ) (u v : X) : S.Jb u (c • v) = c * S.Jb u v := by
  unfold Jb; simp only [map_smul, smul_eq_mul, ← mul_sum]; ring
theorem BJ_add (u v w : X) : S.BJ u (v + w) = S.BJ u v + S.BJ u w := by
  unfold BJ; rw [Cb_add, Ub_add, Ab_add, Nb_add, Jb_add]; ring
theorem BJ_smul (c : ℝ) (u v : X) : S.BJ u (c • v) = c * S.BJ u v := by
  unfold BJ; rw [Cb_smul, Ub_smul, Ab_smul, Nb_smul, Jb_smul]; ring

end Setting

theorem WConsts.Cs_pos (Wc : WConsts) : 0 < Wc.Cs := lt_of_lt_of_le one_pos Wc.hCs

namespace ExpWeight

variable {S : Setting P ι X Fs Ts} {Wc : WConsts} (E : ExpWeight S Wc)

/-- the remainder `r = (Π_t - Id)(φ u)` -/
@[reducible] def r (u : X) : X := E.Pw u - E.M u


/-! ### `eq_r_props` -/

theorem nQT_r_le {u : X} (hu : u ∈ S.Wh) : S.nQT (E.r u) ≤ Wc.Cs * S.τ ^ 2 * S.nQT u := by
  unfold Setting.nQT
  exact sum_le_mul_sum fun n _ => E.superapprox n (by in_range) u hu

theorem nQT_dt_r_le {u : X} (hu : u ∈ S.Wh) : S.nQT (S.dt (E.r u)) ≤ Wc.Cs * S.nQT u := by
  unfold Setting.nQT
  exact sum_le_mul_sum fun n _ => E.superapprox_dt n (by in_range) u hu

theorem gQT_r_le {u : X} (hu : u ∈ S.Wh) : S.gQT (E.r u) ≤ Wc.Cs * S.τ ^ 2 * S.gQT u := by
  unfold Setting.gQT Setting.gQTs
  refine sum_le_mul_sum fun n _ => ?_
  rw [mul_sum]
  refine sum_le_sum fun i _ => ?_
  rw [show S.dx i (E.r u) = E.Pw (S.dx i u) - E.M (S.dx i u) from E.r_dx i u]
  exact E.superapprox n (by in_range) _ (S.dx_mem i u hu)

theorem jh_r_le {u : X} (hu : u ∈ S.Wh) : S.jh (E.r u) ≤ Wc.Cs * S.τ ^ 2 * S.jh u := by
  unfold Setting.jh
  exact sum_le_mul_sum fun n _ => E.superapprox_j n (by in_range) u hu

theorem J2_r_le {u : X} (hu : u ∈ S.Wh) : S.J2 (E.r u) ≤ Wc.Cs * S.τ ^ 2 * S.J2 u := by
  have := mul_le_mul_of_nonneg_left (E.jh_r_le hu) S.cJ_nonneg
  unfold Setting.J2; linarith

theorem jQ_r_le {u : X} (hu : u ∈ S.Wh) :
    S.jQ (E.r u) ≤ Wc.Cs * S.τ ^ 2 * (P.C * S.h⁻¹ * S.jh u + S.jQ u) := by
  have hCs := Wc.Cs_pos; have hτ := S.τ_pos
  unfold Setting.jQ Setting.jh
  rw [mul_sum (a := P.C * S.h⁻¹), ← sum_add_distrib]
  refine sum_le_mul_sum fun n _ => ?_
  have h1 := S.FQ_le n (by in_range) (S.jmp (E.r u))
  have h2 := E.superapprox_gp n (by in_range) u hu
  have h3 := E.superapprox_int n (by in_range) u hu
  have h4 : S.Fgp n (S.jmp u) (S.jmp u) ≤ P.C * S.h⁻¹ * S.j n u u := S.gp_facet n (by in_range) u hu
  have h5 := S.Fint_le_FQ n (by in_range) (S.jmp u)
  have h6 : Wc.Cs * S.τ ^ 2 * (S.Fgp n (S.jmp u) (S.jmp u) + S.Fint n (S.jmp u) (S.jmp u))
      ≤ Wc.Cs * S.τ ^ 2 * (P.C * S.h⁻¹ * S.j n u u + S.FQ n (S.jmp u) (S.jmp u)) := by
    gcongr
  linarith

/-- `eq_r_jumps`. -/
theorem α_jQ_r_le {u : X} (hu : u ∈ S.Wh) :
    S.α * (S.h⁻¹ * S.jQ (E.r u)) ≤ Wc.Cs * (P.C * P.γJ⁻¹ + 1) * S.τ ^ 2 * S.cj2 u := by
  have hCs := Wc.Cs_pos; have hτ := S.τ_pos; have hC := P.C_pos; have hγ := P.hγJ
  have hα := S.α_nonneg; have hhi := S.hinv_pos
  have f1 := E.jQ_r_le hu
  have f2 := S.α_jh_le u
  have f3 := (S.αjQ_le_c2 u).trans (S.c2_le_cj2 u)
  have f4 := S.J2_le_cj2 u
  have g1 : S.α * (S.h⁻¹ * S.jQ (E.r u))
      ≤ S.α * (S.h⁻¹ * (Wc.Cs * S.τ ^ 2 * (P.C * S.h⁻¹ * S.jh u + S.jQ u))) := by gcongr
  have e1 : S.α * (S.h⁻¹ * (Wc.Cs * S.τ ^ 2 * (P.C * S.h⁻¹ * S.jh u + S.jQ u)))
      = Wc.Cs * S.τ ^ 2 * (P.C * (S.α * S.h⁻¹ ^ 2 * S.jh u) + S.α * (S.h⁻¹ * S.jQ u)) := by ring
  have g2 : P.C * (S.α * S.h⁻¹ ^ 2 * S.jh u) + S.α * (S.h⁻¹ * S.jQ u)
      ≤ P.C * (P.γJ⁻¹ * S.cj2 u) + S.cj2 u := by
    have := mul_le_mul_of_nonneg_left (f2.trans (mul_le_mul_of_nonneg_left f4 (by positivity)))
      hC.le
    linarith
  have g3 := mul_le_mul_of_nonneg_left g2 (by positivity : 0 ≤ Wc.Cs * S.τ ^ 2)
  rw [e1] at g1
  linarith

theorem FQ_dn_r_le {u : X} (hu : u ∈ S.Wh) :
    ∑ n ∈ range S.N, S.FQ n (S.dn (E.r u)) (S.dn (E.r u))
      ≤ P.C * Wc.Cs * S.h⁻¹ * S.τ ^ 2 * S.nQT u := by
  have hC := P.C_pos; have hhi := S.hinv_pos
  have h1 := S.FQ_dn_le (E.r_mem u hu)
  have h2 := E.nQT_r_le hu
  have := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ P.C * S.h⁻¹)
  linarith

theorem FQ_nfl_r_le {u : X} (hu : u ∈ S.Wh) :
    ∑ n ∈ range S.N, S.FQ n (S.nfl (E.r u)) (S.nfl (E.r u))
      ≤ P.C * Wc.Cs * S.h⁻¹ * S.τ ^ 2 * S.gQT u := by
  have hC := P.C_pos; have hhi := S.hinv_pos
  have h1 := S.FQ_nfl_le (E.r_mem u hu)
  have h2 := E.gQT_r_le hu
  have := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ P.C * S.h⁻¹)
  linarith

/-- `eq_r_props`, last line. -/
theorem time_traces_r_le {u : X} (hu : u ∈ S.Wh) :
    ∑ n ∈ range S.N, (S.Om n (S.bot n (E.r u)) (S.bot n (E.r u))
        + S.Om (n + 1) (S.top n (E.r u)) (S.top n (E.r u)))
      ≤ 2 * P.C * Wc.Cs * S.τ * S.nQT u := by
  have hC := P.C_pos; have hτ := S.τ_pos; have hτi := S.τinv_pos
  have h1 : ∑ n ∈ range S.N, (S.Om n (S.bot n (E.r u)) (S.bot n (E.r u))
        + S.Om (n + 1) (S.top n (E.r u)) (S.top n (E.r u)))
      ≤ P.C * (S.τ⁻¹ * S.nQT (E.r u) + S.τ * S.nQT (S.dt (E.r u))) := by
    unfold Setting.nQT
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_le_mul_sum fun n _ => S.trace_time_cont n (by in_range) (E.r u)
  have h2 := E.nQT_r_le hu
  have h3 := E.nQT_dt_r_le hu
  have g2 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ P.C * S.τ⁻¹)
  have g3 := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ P.C * S.τ)
  have e : P.C * S.τ⁻¹ * (Wc.Cs * S.τ ^ 2 * S.nQT u) = P.C * Wc.Cs * S.τ * S.nQT u := by
    field_simp
  linarith

theorem bot_r_le {u : X} (hu : u ∈ S.Wh) :
    ∑ n ∈ range S.N, S.Om n (S.bot n (E.r u)) (S.bot n (E.r u))
      ≤ 2 * P.C * Wc.Cs * S.τ * S.nQT u := by
  refine le_trans (sum_le_sum fun n _ => ?_) (E.time_traces_r_le hu)
  have := (S.Om (n + 1)).nonneg (S.top n (E.r u))
  linarith

end ExpWeight

end StDgdg
