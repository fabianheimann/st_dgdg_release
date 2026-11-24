import StDgdg.Apriori
import StDgdg.Ode.Model

/-!
# Validation example `d = 0` (ODE), part 3: the error analysis

A model of `ErrorData` for the ODE: the exact solution is any smooth `u`, the interpolant
is the slab-wise Taylor polynomial of degree one, `U = ‖u''‖²_{L²(0,T)}`, and the discrete
solution is the one provided by `unique_solvability`. All interpolation estimates
(`eq_interpol`) are proven. As a result, the a priori error estimate of the paper holds for
DG(1) in time **without any assumption**.
-/

namespace StDgdg.Ode

open Finset intervalIntegral

/-! ### Poincaré inequality and Taylor interpolation on one interval -/

section interval

variable {a b : ℝ} (hab : a ≤ b)

/-- Poincaré inequality: `‖g‖² ≤ 4 (b-a)² ‖g'‖²` if `g(a) = 0`. -/
theorem poincare (g : Sm) (h0 : g a = 0) :
    ip a b hab g g ≤ 4 * (b - a) ^ 2 * ip a b hab (D g) (D g) := by
  have h1 := ip_D hab (aff (-b) 1) (mk (fun t => g t * g t) ((cd g).mul (cd g)))
  have hD : D (mk (fun t => g t * g t) ((cd g).mul (cd g)))
      = (2 : ℝ) • mk (fun t => g t * D g t) ((cd g).mul (cd (D g))) := by
    ext t
    have h : HasDerivAt (fun t => g t * g t) (D g t * g t + g t * D g t) t :=
      (hasDerivAt g t).mul (hasDerivAt g t)
    show deriv (fun t => g t * g t) t = 2 * (g t * D g t)
    rw [h.deriv]; ring
  rw [D_aff, hD] at h1
  simp only [ip_apply, aff_apply, mk_apply, Sm.smul_apply, add_zero, zero_mul, one_mul] at h1
  rw [h0] at h1
  have key : (∫ t in a..b, (-((-b + t) * (2 * (g t * D g t)))))
      ≤ ∫ t in a..b, (1 / 2 * (g t * g t) + 2 * (b - a) ^ 2 * (D g t * D g t)) := by
    apply integral_mono_on hab
    · exact Continuous.intervalIntegrable (by have := cont g; have := cont (D g); fun_prop) _ _
    · exact Continuous.intervalIntegrable (by have := cont g; have := cont (D g); fun_prop) _ _
    · intro t ht
      have h0 : 0 ≤ b - t := by linarith [ht.2]
      have h2 : (b - t) ^ 2 ≤ (b - a) ^ 2 := by
        apply pow_le_pow_left₀ h0; linarith [ht.1]
      have h3 := mul_le_mul_of_nonneg_right h2 (mul_self_nonneg (D g t))
      nlinarith [sq_nonneg (g t - 2 * (b - t) * D g t)]
  have e2 : (∫ t in a..b, (1 / 2 * (g t * g t) + 2 * (b - a) ^ 2 * (D g t * D g t)))
      = 1 / 2 * (∫ t in a..b, g t * g t) + 2 * (b - a) ^ 2 * ∫ t in a..b, D g t * D g t := by
    rw [integral_add ((intble g g a b).const_mul _) ((intble (D g) (D g) a b).const_mul _),
      integral_const_mul, integral_const_mul]
  rw [e2, intervalIntegral.integral_neg] at key
  have e4 : (∫ t in a..b, g t * g t) = -∫ t in a..b, ((-b + t) * (2 * (g t * D g t))) := by
    linear_combination h1
  simp only [ip_apply]
  linarith

/-- The Taylor polynomial of degree one at `a`. -/
noncomputable def Tay (a : ℝ) (f : Sm) : Sm := aff (f a - D f a * a) (D f a)

theorem Tay_mem (a : ℝ) (f : Sm) : Tay a f ∈ P1 := aff_mem _ _

theorem D_Tay_err (f : Sm) : D (D (f - Tay a f)) = D (D f) := by
  rw [Tay, map_sub, map_sub, D_aff, D_aff]
  ext t; simp

/-- `‖(f - T f)'‖² ≤ 4 (b-a)² ‖f''‖²`. -/
theorem taylor_dt (f : Sm) :
    ip a b hab (D (f - Tay a f)) (D (f - Tay a f))
      ≤ 4 * (b - a) ^ 2 * ip a b hab (D (D f)) (D (D f)) := by
  have h := poincare hab (D (f - Tay a f)) (by rw [Tay, map_sub, D_aff]; simp)
  rwa [D_Tay_err] at h

/-- `‖f - T f‖² ≤ 16 (b-a)⁴ ‖f''‖²`. -/
theorem taylor_L2 (f : Sm) :
    ip a b hab (f - Tay a f) (f - Tay a f)
      ≤ 16 * (b - a) ^ 4 * ip a b hab (D (D f)) (D (D f)) := by
  have h1 := poincare hab (f - Tay a f) (by simp [Tay])
  have h2 := taylor_dt hab f
  have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4 * (b - a) ^ 2)
  nlinarith

/-- A non-zero affine function has non-zero `L²` norm. -/
theorem aff_eq_zero_of_ip {τ : ℝ} (hτ : 0 < τ) (a c d : ℝ)
    (h : Iv hτ a (aff c d) (aff c d) = 0) : aff c d = 0 := by
  rw [ip_aff hτ] at h
  have h3 : 0 < τ ^ 3 := pow_pos hτ 3
  have e : τ * ((c + d * a) + d * τ / 2) ^ 2 + d ^ 2 * τ ^ 3 / 12 = 0 := by linear_combination h
  have a1 : 0 ≤ τ * ((c + d * a) + d * τ / 2) ^ 2 := by positivity
  have a2 : 0 ≤ d ^ 2 * τ ^ 3 / 12 := by positivity
  have hd : d = 0 := by
    have : d ^ 2 * τ ^ 3 = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact pow_eq_zero_iff two_ne_zero |>.1 h
    · exact absurd h h3.ne'
  have hq : τ * ((c + d * a) + d * τ / 2) ^ 2 = 0 := by linarith
  rw [hd] at hq
  have hc : c = 0 := by
    rcases mul_eq_zero.1 hq with h | h
    · exact absurd h hτ.ne'
    · have := pow_eq_zero_iff two_ne_zero |>.1 h
      linarith
  ext t; simp [hc, hd]

end interval

/-! ### `W_h` is finite dimensional and `‖·‖_{𝒬_T}` is a norm on it -/

variable {P : Consts} (p : Params P)

/-- Coordinates of a discrete function: value and slope at `0` on each slab. -/
noncomputable def coords : WhX p →ₗ[ℝ] (Fin p.N → ℝ × ℝ) where
  toFun u := fun i => ((u : X) i 0, D ((u : X) i) 0)
  map_add' u v := by funext i; simp
  map_smul' c u := by funext i; simp

theorem coords_inj : Function.Injective (coords p) := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  apply Subtype.ext
  funext n
  show (u : X) n = 0
  by_cases hn : n < p.N
  · obtain ⟨c, d, hcd⟩ := (u.2 n).1
    have h := congrFun hu ⟨n, hn⟩
    have h1 : (u : X) n 0 = 0 := congrArg Prod.fst h
    have h2 : D ((u : X) n) 0 = 0 := congrArg Prod.snd h
    rw [hcd] at h1 h2 ⊢
    rw [D_aff] at h2
    simp only [aff_apply, mul_zero, add_zero] at h1 h2
    ext t; simp [h1, h2]
  · exact (u.2 n).2 (by omega)

instance : FiniteDimensional ℝ (WhX p) := FiniteDimensional.of_injective (coords p) (coords_inj p)

theorem hdef' (u : X) (hu : u ∈ WhX p) (h : (odeSetting p).nQT u = 0) : u = 0 := by
  have h' : ∑ n ∈ range p.N, QX p n u u = 0 := h
  have h0 := (sum_eq_zero_iff_of_nonneg fun n _ => QX_nonneg p n u).1 h'
  funext n
  show u n = 0
  by_cases hn : n < p.N
  · obtain ⟨c, d, hcd⟩ := (hu n).1
    have h1 := h0 n (mem_range.2 hn)
    rw [QX_apply, sl_of_lt p hn, hcd] at h1
    rw [hcd]
    exact aff_eq_zero_of_ip p.τ_pos _ c d h1
  · exact (hu n).2 (by omega)

/-! ### Exact solution, interpolant, discrete solution -/

variable (u : Sm)

/-- The exact solution on every slab. -/
def ueX : X := fun _ => u

/-- The slab-wise Taylor interpolant. -/
noncomputable def IhX : X := fun n => if n < p.N then Tay (tk p n) u else 0

theorem IhX_mem : IhX p u ∈ WhX p := fun n => by
  by_cases hn : n < p.N
  · have e : IhX p u n = Tay (tk p n) u := by simp [IhX, hn]
    exact ⟨e ▸ Tay_mem _ _, fun h => absurd hn (by omega)⟩
  · have e : IhX p u n = 0 := by simp [IhX, hn]
    exact ⟨e ▸ P1.zero_mem, fun _ => e⟩

theorem sl_err {n : ℕ} (hn : n < p.N) : sl p n (ueX u - IhX p u) = u - Tay (tk p n) u := by
  rw [sl_of_lt p hn]; simp [ueX, IhX, hn]

/-- `‖u''‖²_{L²(0,T)}`. -/
noncomputable def UX : ℝ := ∑ n ∈ range p.N, Iv p.τ_pos (tk p n) (D (D u)) (D (D u))

theorem UX_nonneg : 0 ≤ UX p u := sum_nonneg fun n _ => (Iv p.τ_pos (tk p n)).nonneg _

/-- `eq_interpol_L2`: `‖u - I_h u‖²_{L²(0,T)} ≤ 16 Δt⁴ ‖u''‖²`. -/
theorem i_L2' : (odeSetting p).nQT (ueX u - IhX p u) ≤ 16 * p.τ ^ 4 * UX p u := by
  show ∑ n ∈ range p.N, QX p n (ueX u - IhX p u) (ueX u - IhX p u) ≤ _
  unfold UX
  rw [mul_sum]
  refine sum_le_sum fun n hn => ?_
  rw [QX_apply, sl_err p u (mem_range.1 hn)]
  have h := taylor_L2 (le_of_lt (lt_add_of_pos_right (tk p n) p.τ_pos)) u
  rwa [add_sub_cancel_left] at h

/-- `eq_interpol_dt`: `‖(u - I_h u)'‖²_{L²(0,T)} ≤ 4 Δt² ‖u''‖²`. -/
theorem i_dt' : (odeSetting p).nQT (dtX (ueX u - IhX p u)) ≤ 4 * p.τ ^ 2 * UX p u := by
  show ∑ n ∈ range p.N, QX p n (dtX (ueX u - IhX p u)) (dtX (ueX u - IhX p u)) ≤ _
  unfold UX
  rw [mul_sum]
  refine sum_le_sum fun n hn => ?_
  rw [QX_apply, sl_dt, sl_err p u (mem_range.1 hn)]
  have h := taylor_dt (le_of_lt (lt_add_of_pos_right (tk p n) p.τ_pos)) u
  rwa [add_sub_cancel_left] at h

/-- There is no Ghost penalty for `d = 0`. -/
theorem Jb_zero (v w : X) : (odeSetting p).Jb v w = 0 := by
  simp [Setting.Jb, odeSetting, SemiIP.zero]

theorem Bh_eq_BJ (v w : X) : (odeSetting p).Bh v w = (odeSetting p).BJ v w := by
  unfold Setting.Bh Setting.BJ; rw [Jb_zero]; ring

/-! ### Consistency: `B_h(u, ·)` only depends on the data `u'` and `u(0)` -/

theorem tk_zero : tk p 0 = 0 := by simp [tk]

theorem tjump_ue_succ {n : ℕ} (hn : n + 1 < p.N) :
    (odeSetting p).tjump (n + 1) (ueX u) = 0 := by
  show botX p (n + 1) (ueX u) - topX p n (ueX u) = 0
  rw [botX_apply, topX_apply, sl_of_lt p hn, sl_of_lt p (by omega), tk_succ]
  simp [ueX]

theorem Ub_ue (v : X) :
    (odeSetting p).Ub (ueX u) v = if 0 < p.N then u 0 * v 0 0 else 0 := by
  have hU : (odeSetting p).Ub (ueX u) v
      = ∑ n ∈ range p.N, OmR ((odeSetting p).tjump n (ueX u)) (botX p n v) := by
    simp [Setting.Ub, odeSetting, SemiIP.zero]
  rw [hU]
  rcases Nat.eq_zero_or_pos p.N with h0 | hpos
  · simp [h0]
  · obtain ⟨m, hm⟩ : ∃ m, p.N = m + 1 := ⟨p.N - 1, by omega⟩
    simp only [hpos, ↓reduceIte]
    rw [show range p.N = range (m + 1) from by rw [hm], sum_range_succ']
    have h1 : ∑ n ∈ range m, OmR ((odeSetting p).tjump (n + 1) (ueX u)) (botX p (n + 1) v) = 0 := by
      refine sum_eq_zero fun n hn => ?_
      rw [tjump_ue_succ p u (by have := mem_range.1 hn; omega)]
      simp
    rw [h1, zero_add]
    show (botX p 0 (ueX u) - 0) * botX p 0 v = _
    rw [botX_apply, botX_apply, sl_of_lt p hpos, sl_of_lt p hpos, tk_zero]
    simp [ueX]

/-- **Consistency (`lemma_consistency`) for `d = 0`**: the right hand side
`f_h(v) = B_h(u, v)` is `(u', v)_{L²(0,T)} + u(0) v_+(0)`, i.e. it only depends on the
data `f = u'` and `u_0 = u(0)` of the ODE. -/
theorem consistency (v : X) :
    (odeSetting p).Bh (ueX u) v
      = ∑ n ∈ range p.N, QX p n (dtX (ueX u)) v + (if 0 < p.N then u 0 * v 0 0 else 0) := by
  have hA : (odeSetting p).Ab (ueX u) v = 0 := by simp [Setting.Ab, odeSetting]
  have hN : (odeSetting p).Nb (ueX u) v = 0 := by simp [Setting.Nb, odeSetting, SemiIP.zero]
  have hC : (odeSetting p).Cb (ueX u) v = ∑ n ∈ range p.N, QX p n (dtX (ueX u)) v := rfl
  unfold Setting.Bh
  rw [hA, hN, hC, Ub_ue]
  ring

/-- The right hand side `f_h(v) = B_h(u, v)` as a functional on `W_h`. -/
noncomputable def rhs : (odeSetting p).Wh →ₗ[ℝ] ℝ where
  toFun v := (odeSetting p).BJ (ueX u) (v : X)
  map_add' _ _ := (odeSetting p).BJ_add _ _ _
  map_smul' _ _ := (odeSetting p).BJ_smul _ _ _

variable (hlam : P.lam0 (odeWConsts p).Cφ ≤ P.lam)
  (hsmall : ExpWeight.Ksup P (odeWConsts p) * ExpWeight.Kw P (odeWConsts p) * √p.τ ≤ 1 / 8)

include hlam hsmall in
/-- The DG(1) time stepping scheme has a unique solution. -/
theorem ode_exists_unique :
    ∃! uh : (odeSetting p).Wh, ∀ v : (odeSetting p).Wh,
      (odeSetting p).BJ (uh : X) (v : X) = rhs p u v :=
  haveI : FiniteDimensional ℝ (odeSetting p).Wh := inferInstanceAs (FiniteDimensional ℝ (WhX p))
  (odeExpWeight p).unique_solvability hlam hsmall (hdef' p) (rhs p u)

/-- The discrete solution. -/
noncomputable def uhX : (odeSetting p).Wh := (ode_exists_unique p u hlam hsmall).exists.choose

theorem uhX_spec (v : X) (hv : v ∈ (odeSetting p).Wh) :
    (odeSetting p).BJ (uhX p u hlam hsmall : X) v = (odeSetting p).Bh (ueX u) v := by
  rw [Bh_eq_BJ]
  exact (ode_exists_unique p u hlam hsmall).exists.choose_spec ⟨v, hv⟩

/-- **The ODE model of the data of the error analysis** (`k_t = 1`, interpolation
constant `16`). -/
noncomputable def odeErrorData : ErrorData (odeSetting p) 16 where
  ue := ueX u
  uh := uhX p u hlam hsmall
  Ih := IhX p u
  f := fun v => (odeSetting p).Bh (ueX u) v
  uh_mem := (uhX p u hlam hsmall).2
  Ih_mem := IhX_mem p u
  cons := fun _ _ => rfl
  disc := uhX_spec p u hlam hsmall
  jmp_ue := by simp [Setting.jmp, odeSetting]
  ks := 1
  kt := 1
  U := UX p u
  D2 := 0
  hCi := by norm_num
  hU := UX_nonneg p u
  hD2 := le_refl _
  nfl_e := by simp [Setting.FN, Setting.gQT, Setting.gQTs, odeSetting, SemiIP.zero]
  i_L2 := by
    have h := i_L2' p u
    have hU := UX_nonneg p u
    have hh : 0 ≤ p.h ^ 2 * p.h ^ (2 * 1) := by have := p.h_pos; positivity
    show (odeSetting p).nQT (ueX u - IhX p u)
      ≤ 16 * (p.τ ^ 2 * p.τ ^ (2 * 1) + p.h ^ 2 * p.h ^ (2 * 1)) * UX p u
    have e1 : p.τ ^ 2 * p.τ ^ (2 * 1) = p.τ ^ 4 := by ring
    have := mul_nonneg hh hU
    rw [e1]
    linarith
  i_dt := by
    have h := i_dt' p u
    have hU := UX_nonneg p u
    have hh : 0 ≤ p.h ^ 2 * p.h ^ (2 * 1) := by have := p.h_pos; positivity
    have hτ : 0 ≤ p.τ ^ 2 := sq_nonneg _
    show (odeSetting p).nQT (dtX (ueX u - IhX p u))
      ≤ 16 * (p.τ ^ (2 * 1) + p.h ^ 2 * p.h ^ (2 * 1)) * UX p u
    have e1 : p.τ ^ (2 * 1) = p.τ ^ 2 := by norm_num
    have := mul_nonneg hh hU
    have := mul_nonneg hτ hU
    rw [e1]
    linarith
  i_grad := by
    have hU := UX_nonneg p u
    have : 0 ≤ 16 * (p.τ ^ 2 * p.τ ^ (2 * 1) + p.h ^ (2 * 1)) * UX p u := by
      have := p.τ_pos; have := p.h_pos; positivity
    simpa [Setting.gQT, Setting.gQTs, odeSetting] using this
  i_jump := by
    have hU := UX_nonneg p u
    have : 0 ≤ 16 * p.h ^ (2 * 1) * UX p u := by have := p.h_pos; positivity
    simpa [Setting.jmp, Setting.jh, odeSetting, SemiIP.zero] using this

/-! ### The a priori error estimate for DG(1) in time, without assumptions -/

include hlam hsmall in
/-- **A priori error estimate for the ODE, Case D** (`thm_apriori`): for every smooth `u`,
the DG(1) solution `u_h` with data `f = u'`, `u_0 = u(0)` satisfies
`|||u - u_h|||² ≲ (α (h² + Δt⁴) + Δt³) ‖u''‖²_{L²(0,T)}`. -/
theorem ode_apriori_D (hr : p.regime = .D) :
    (odeSetting p).tn2 (ueX u - uhX p u hlam hsmall)
      ≤ ExpWeight.Kst P (odeWConsts p) * (ErrorData.Kap P * ((2 + 5 * P.C) * 16
        * (p.α * p.h ^ (2 * 1) + p.α * (p.τ ^ 2 * p.τ ^ (2 * 1)) + p.τ * p.τ ^ (2 * 1))
        * UX p u)) :=
  (odeErrorData p u hlam hsmall).apriori_D (odeExpWeight p) hr hlam hsmall

include hlam hsmall in
/-- **A priori error estimate for the ODE, Case C** (`thm_apriori`). -/
theorem ode_apriori_C (hr : p.regime = .C) :
    (odeSetting p).tn2 (ueX u - uhX p u hlam hsmall)
      ≤ ExpWeight.Kst P (odeWConsts p) * (ErrorData.Kap P * ((2 + 4 * P.C + 2 * P.C ^ 2) * 16
        * ((1 + p.h ^ 2) * (p.τ * p.τ ^ (2 * 1)) + p.wInf * p.h * p.h ^ (2 * 1)
          + p.α * (p.h ^ (2 * 1) + p.τ ^ 2 * p.τ ^ (2 * 1))) * UX p u)) :=
  (odeErrorData p u hlam hsmall).apriori_C (odeExpWeight p) hr hlam hsmall

end StDgdg.Ode
