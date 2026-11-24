import StDgdg.Move1d.TimeForms

/-!
# Validation example `d = 1`, moving domain: convection-diffusion on a moving interval

Space-time DG (`P¹` in space and time) for `∂_t u + w ∂_x u - α ∂_xx u = f` on the moving
domain `Ω(t) = (ℓ₀ + w t, r₀ + w t)` with constant velocity `w > 0`, on the fixed uniform
background mesh `K_i = [ih, (i+1)h]`, `i < m`. Both regimes (Case D and Case C) are covered;
the only additional requirements are `w Δt ≤ h` (the boundary crosses at most one element
per time step), a domain width of at least `4h`, and `C ≥ 13000`.

The physical part of element `i` at time `t` is `ξ ∈ [lo i t, hi i t]` in the local
coordinate, where `lo`, `hi` are clamped affine functions of time: within one time slab an
element can be uncut, cut by the moving boundary, entered or left.

* active elements of slab `n`: `x_i ≤ r(t_{n+1})` and `ℓ(t_n) < x_{i+1}`,
* interior elements (`K_i × I_n ⊆ closure Q`): `ℓ(t_{n+1}) ≤ x_i` and `x_{i+1} ≤ r(t_n)`,
* Ghost penalty nodes: between two active elements which are not both interior,
* a node lies in the domain at time `t` if `ℓ(t) < x ≤ r(t)` (the upwind facet terms).

**Every assumption of `Setting.lean` is proven**, including space-time integration by parts
on the moving cut elements (`ibp'`, via the Leibniz rule of `Leibniz.lean`).
-/

namespace StDgdg.Move1d

open Finset SemiIP Cut1d intervalIntegral
open Ode hiding MX PwX Pw_mem' WhX X botX bot_M' dtX dt_M' hi_le' hi_pos phiX phi_le_one' tk tk_le tk_nonneg tk_succ topX top_M' τi_pos

/-- Parameters of the example. -/
structure Params (P : Consts) extends Base where
  regime : Regime
  N : ℕ
  /-- number of background elements -/
  m : ℕ
  α : ℝ
  /-- the velocity -/
  w : ℝ
  /-- left end of the domain at `t = 0` -/
  ℓ0 : ℝ
  /-- right end of the domain at `t = 0` -/
  r0 : ℝ
  h_le : h ≤ P.C
  α_nonneg : 0 ≤ α
  w_pos : 0 < w
  caseD : regime = .D → h ^ 2 ≤ P.C * α * τ ∧ w ^ 2 * τ ≤ P.C * α
  caseC : regime = .C → w * τ ≤ P.C * h ∧ h ≤ P.C * w * τ
  /-- the boundary crosses at most one element per time step -/
  cfl : w * τ ≤ h
  /-- the domain stays inside the background mesh `[0, m h]` up to the final time -/
  ℓ0_nonneg : 0 ≤ ℓ0
  r_lt : r0 + w * (N * τ) < m * h
  /-- the domain is at least four elements wide -/
  width : 4 * h ≤ r0 - ℓ0
  hC : 13000 ≤ P.C

instance {P : Consts} : CoeOut (Params P) Base := ⟨Params.toBase⟩

variable {P : Consts} (p : Params P)

/-! ### Geometry -/

/-- the nodes `x_i = i h` -/
def x (i : ℕ) : ℝ := i * p.h
/-- left end of the domain -/
def ℓ (t : ℝ) : ℝ := p.ℓ0 + p.w * t
/-- right end of the domain -/
def r (t : ℝ) : ℝ := p.r0 + p.w * t

theorem x_succ (i : ℕ) : x p (i + 1) = x p i + p.h := by unfold x; push_cast; ring

theorem x_lt_x {i j : ℕ} : x p i < x p j ↔ i < j := by
  unfold x
  rw [mul_lt_mul_iff_left₀ p.h_pos, Nat.cast_lt]

theorem x_le_x {i j : ℕ} : x p i ≤ x p j ↔ i ≤ j := by
  unfold x
  rw [mul_le_mul_iff_left₀ p.h_pos, Nat.cast_le]

theorem ℓ_mono {t t' : ℝ} (h : t ≤ t') : ℓ p t ≤ ℓ p t' := by
  unfold ℓ; have := mul_le_mul_of_nonneg_left h p.w_pos.le; linarith

theorem r_mono {t t' : ℝ} (h : t ≤ t') : r p t ≤ r p t' := by
  unfold r; have := mul_le_mul_of_nonneg_left h p.w_pos.le; linarith

theorem r_sub_ℓ (t : ℝ) : r p t - ℓ p t = p.r0 - p.ℓ0 := by unfold r ℓ; ring

theorem ℓ_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ ℓ p t := by
  unfold ℓ; have := mul_nonneg p.w_pos.le ht; have := p.ℓ0_nonneg; linarith

/-- the boundary moves by at most `h` per time step -/
theorem ℓ_step (n : ℕ) : ℓ p (tk p (n + 1)) ≤ ℓ p (tk p n) + p.h := by
  rw [tk_succ]; unfold ℓ; have := p.cfl; linarith

theorem r_step (n : ℕ) : r p (tk p (n + 1)) ≤ r p (tk p n) + p.h := by
  rw [tk_succ]; unfold r; have := p.cfl; linarith

/-- the domain stays inside the background mesh -/
theorem r_lt_xm {n : ℕ} (hn : n < p.N) {t : ℝ} (ht : t ≤ tk p (n + 1)) : r p t < x p p.m := by
  have h1 : tk p (n + 1) ≤ tk p p.N := tk_le p (by omega)
  have h2 := r_mono p (ht.trans h1)
  have h3 : r p (tk p p.N) = p.r0 + p.w * (p.N * p.τ) := rfl
  have := p.r_lt
  unfold x
  linarith

/-- offsets of the cut positions: `s = κ + μ t` with `μ = w / h` -/
noncomputable def κL (i : ℕ) : ℝ := (p.ℓ0 - x p i) / p.h
noncomputable def κR (i : ℕ) : ℝ := (p.r0 - x p i) / p.h
noncomputable def μ : ℝ := p.w / p.h

theorem μ_nonneg : 0 ≤ μ p := div_nonneg p.w_pos.le p.h_pos.le

theorem h_mul_μ : p.h * μ p = p.w := by
  unfold μ; have := p.h_pos; field_simp

theorem sL_eq (i : ℕ) (t : ℝ) : κL p i + μ p * t = (ℓ p t - x p i) / p.h := by
  unfold κL μ ℓ; have := p.h_pos; field_simp; ring

theorem sR_eq (i : ℕ) (t : ℝ) : κR p i + μ p * t = (r p t - x p i) / p.h := by
  unfold κR μ r; have := p.h_pos; field_simp; ring

theorem sL_neg_iff (i : ℕ) (t : ℝ) : κL p i + μ p * t < 0 ↔ ℓ p t < x p i := by
  rw [sL_eq, div_lt_iff₀ p.h_pos]; constructor <;> intro h <;> linarith

theorem sL_lt_one_iff (i : ℕ) (t : ℝ) : κL p i + μ p * t < 1 ↔ ℓ p t < x p (i + 1) := by
  rw [sL_eq, div_lt_iff₀ p.h_pos, x_succ]; constructor <;> intro h <;> linarith

theorem sR_nonneg_iff (i : ℕ) (t : ℝ) : 0 ≤ κR p i + μ p * t ↔ x p i ≤ r p t := by
  rw [sR_eq, le_div_iff₀ p.h_pos]; constructor <;> intro h <;> linarith

theorem sR_ge_one_iff (i : ℕ) (t : ℝ) : 1 ≤ κR p i + μ p * t ↔ x p (i + 1) ≤ r p t := by
  rw [sR_eq, le_div_iff₀ p.h_pos, x_succ]; constructor <;> intro h <;> linarith

theorem sL_lt_sR (i : ℕ) (t : ℝ) : κL p i + μ p * t < κR p i + μ p * t := by
  rw [sL_eq, sR_eq, div_lt_div_iff_of_pos_right p.h_pos]
  have := r_sub_ℓ p t; have := p.width; have := p.h_pos
  linarith

/-- lower and upper end of the physical part of element `i` at time `t` (local coordinate) -/
noncomputable def lo (i : ℕ) (t : ℝ) : ℝ := clamp (κL p i + μ p * t)
noncomputable def hi (i : ℕ) (t : ℝ) : ℝ := clamp (κR p i + μ p * t)

theorem lo_cont (i : ℕ) : Continuous (lo p i) := continuous_cut _ _
theorem hi_cont (i : ℕ) : Continuous (hi p i) := continuous_cut _ _
theorem lo_le_hi (i : ℕ) (t : ℝ) : lo p i t ≤ hi p i t := clamp_mono (sL_lt_sR p i t).le
theorem lo_nonneg (i : ℕ) (t : ℝ) : 0 ≤ lo p i t := clamp_nonneg _
theorem hi_le_one (i : ℕ) (t : ℝ) : hi p i t ≤ 1 := clamp_le_one _

/-- indicator: the node `x_k` lies in the domain at time `t` -/
noncomputable def ind (k : ℕ) (t : ℝ) : ℝ := if ℓ p t < x p k ∧ x p k ≤ r p t then 1 else 0

theorem ind_nonneg (k : ℕ) (t : ℝ) : 0 ≤ ind p k t := by unfold ind; split_ifs <;> norm_num
theorem ind_le_one (k : ℕ) (t : ℝ) : ind p k t ≤ 1 := by unfold ind; split_ifs <;> norm_num

theorem ind_eq (k : ℕ) (t : ℝ) :
    ind p k t = (if x p k ≤ r p t then (1 : ℝ) else 0) - (if x p k ≤ ℓ p t then (1 : ℝ) else 0) := by
  have hlr : ℓ p t < r p t := by
    have := r_sub_ℓ p t; have := p.width; have := p.h_pos; linarith
  unfold ind
  by_cases h1 : x p k ≤ r p t <;> by_cases h2 : x p k ≤ ℓ p t
  · simp [h1, h2, not_lt.2 h2]
  · simp [h1, h2, not_le.1 h2]
  · exfalso; linarith
  · simp [h1, h2]

theorem ind_intble (k : ℕ) (a b : ℝ) : IntervalIntegrable (ind p k) MeasureTheory.volume a b := by
  have m1 : Monotone fun t : ℝ => (if x p k ≤ r p t then (1 : ℝ) else 0) := by
    intro t t' h
    have := r_mono p h
    dsimp only
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd (h1.trans this) h2
    · exact zero_le_one
    · exact le_rfl
  have m2 : Monotone fun t : ℝ => (if x p k ≤ ℓ p t then (1 : ℝ) else 0) := by
    intro t t' h
    have := ℓ_mono p h
    dsimp only
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd (h1.trans this) h2
    · exact zero_le_one
    · exact le_rfl
  have e : ind p k = fun t => (if x p k ≤ r p t then (1 : ℝ) else 0)
      - (if x p k ≤ ℓ p t then (1 : ℝ) else 0) := funext fun t => ind_eq p k t
  rw [e]
  exact m1.intervalIntegrable.sub m2.intervalIntegrable

/-- the node `x_0` is never in the domain -/
theorem ind_zero {t : ℝ} (ht : 0 ≤ t) : ind p 0 t = 0 := by
  unfold ind
  rw [if_neg]
  intro h
  have := ℓ_nonneg p ht
  have : x p 0 = 0 := by simp [x]
  linarith [h.1]

/-- the node `x_m` is never in the domain (up to the final time) -/
theorem ind_m {n : ℕ} (hn : n < p.N) {t : ℝ} (ht : t ≤ tk p (n + 1)) : ind p p.m t = 0 := by
  unfold ind
  rw [if_neg]
  intro h
  have := r_lt_xm p hn ht
  linarith [h.2]

/-! ### Active and interior elements, nodes -/

open scoped Classical in
/-- active elements of slab `n` -/
noncomputable def act (n : ℕ) : Finset ℕ :=
  (range p.m).filter fun i => x p i ≤ r p (tk p (n + 1)) ∧ ℓ p (tk p n) < x p (i + 1)

open scoped Classical in
/-- interior elements of slab `n`: `K_i × I_n ⊆ closure Q` -/
noncomputable def intr (n : ℕ) : Finset ℕ :=
  (range p.m).filter fun i => ℓ p (tk p (n + 1)) ≤ x p i ∧ x p (i + 1) ≤ r p (tk p n)

open scoped Classical in
/-- nodes between two active elements -/
noncomputable def allN (n : ℕ) : Finset ℕ :=
  (range p.m).filter fun j => j ∈ act p n ∧ j + 1 ∈ act p n

open scoped Classical in
/-- interior nodes: both neighbours are interior elements -/
noncomputable def intN (n : ℕ) : Finset ℕ :=
  (allN p n).filter fun j => j ∈ intr p n ∧ j + 1 ∈ intr p n

open scoped Classical in
/-- Ghost penalty nodes: at least one neighbour is not interior -/
noncomputable def gpN (n : ℕ) : Finset ℕ :=
  (allN p n).filter fun j => ¬(j ∈ intr p n ∧ j + 1 ∈ intr p n)

theorem mem_act {n i : ℕ} : i ∈ act p n ↔
    i < p.m ∧ x p i ≤ r p (tk p (n + 1)) ∧ ℓ p (tk p n) < x p (i + 1) := by
  simp [act]

theorem mem_intr {n i : ℕ} : i ∈ intr p n ↔
    i < p.m ∧ ℓ p (tk p (n + 1)) ≤ x p i ∧ x p (i + 1) ≤ r p (tk p n) := by
  simp [intr]

theorem mem_allN {n j : ℕ} : j ∈ allN p n ↔ j ∈ act p n ∧ j + 1 ∈ act p n := by
  simp only [allN, mem_filter, mem_range]
  exact ⟨fun h => h.2, fun h => ⟨((mem_act p).1 h.1).1, h⟩⟩

theorem intr_sub_act (n : ℕ) : intr p n ⊆ act p n := by
  intro i hi
  obtain ⟨h1, h2, h3⟩ := (mem_intr p).1 hi
  refine (mem_act p).2 ⟨h1, ?_, ?_⟩
  · have := (x_le_x p).2 (Nat.le_succ i)
    have := r_mono p (tk_le p (Nat.le_succ n))
    linarith
  · have := (x_lt_x p).2 (Nat.lt_succ_self i)
    have := ℓ_mono p (tk_le p (Nat.le_succ n))
    linarith

theorem sum_nodes (n : ℕ) (f : ℕ → ℝ) :
    ∑ j ∈ gpN p n, f j + ∑ j ∈ intN p n, f j = ∑ j ∈ allN p n, f j := by
  unfold gpN intN
  rw [add_comm]
  exact sum_filter_add_sum_filter_not _ _ _

/-! ### The cut positions within one time slab -/

theorem sL_nonpos_iff (i : ℕ) (t : ℝ) : κL p i + μ p * t ≤ 0 ↔ ℓ p t ≤ x p i := by
  rw [sL_eq, div_le_iff₀ p.h_pos]; constructor <;> intro h <;> linarith

theorem slab_left (n : ℕ) : tk p n ∈ Set.Icc (tk p n) (tk p n + p.τ) :=
  ⟨le_rfl, slab_le p n⟩
theorem slab_right (n : ℕ) : tk p (n + 1) ∈ Set.Icc (tk p n) (tk p n + p.τ) := by
  rw [tk_succ]; exact ⟨slab_le p n, le_rfl⟩

/-- on an inactive element the physical part is empty during the whole slab -/
theorem lo_eq_hi {n i : ℕ} (hi' : ¬(x p i ≤ r p (tk p (n + 1)) ∧ ℓ p (tk p n) < x p (i + 1)))
    {t : ℝ} (ht : t ∈ Set.Icc (tk p n) (tk p n + p.τ)) : lo p i t = hi p i t := by
  have hlt := sL_lt_sR p i t
  by_cases h1 : x p i ≤ r p (tk p (n + 1))
  · have h2 : x p (i + 1) ≤ ℓ p (tk p n) := not_lt.1 fun h => hi' ⟨h1, h⟩
    have h3 : ¬ κL p i + μ p * t < 1 := by
      rw [sL_lt_one_iff]; have := ℓ_mono p ht.1; linarith
    unfold lo hi
    rw [clamp_of_ge (not_lt.1 h3), clamp_of_ge (by linarith [not_lt.1 h3])]
  · have h3 : ¬ 0 ≤ κR p i + μ p * t := by
      rw [sR_nonneg_iff]
      have := r_mono p (show t ≤ tk p (n + 1) by rw [tk_succ]; exact ht.2)
      linarith [not_le.1 h1]
    unfold lo hi
    rw [clamp_of_nonpos (by linarith [not_le.1 h3]), clamp_of_nonpos (not_le.1 h3).le]

/-- an interior element is uncut during the whole slab -/
theorem lo_hi_interior {n i : ℕ} (hi' : i ∈ intr p n) {t : ℝ}
    (ht : t ∈ Set.Icc (tk p n) (tk p n + p.τ)) : lo p i t = 0 ∧ hi p i t = 1 := by
  obtain ⟨_, h2, h3⟩ := (mem_intr p).1 hi'
  constructor
  · apply clamp_of_nonpos
    rw [sL_nonpos_iff]
    have := ℓ_mono p (show t ≤ tk p (n + 1) by rw [tk_succ]; exact ht.2)
    linarith
  · apply clamp_of_ge
    rw [sR_ge_one_iff]
    have := r_mono p ht.1
    linarith

/-! ### The forms -/

/-- `∫_{I_n} ∫_{K_i ∩ Ω(t)} u v dx dt` -/
noncomputable def cutE (n i : ℕ) : SemiIP X :=
  cutX p n (lo p i) (hi p i) (lo_cont p i) (hi_cont p i) (lo_le_hi p i) i

/-- `(·,·)_{Q^n}` -/
noncomputable def QX (n : ℕ) : SemiIP X := SemiIP.sum (range p.m) fun i => cutE p n i

/-- `(·,·)_{𝒬_T^n}`: the active elements -/
noncomputable def QTX (n : ℕ) : SemiIP X := SemiIP.sum (act p n) fun i => full p n i

/-- `j_h^n` -/
noncomputable def jX (n : ℕ) : SemiIP X := SemiIP.sum (gpN p n) fun i => jF p n i

noncomputable def FgpX (n : ℕ) : SemiIP Fs :=
  SemiIP.sum (gpN p n) fun j => (It p n).comap (fN n j)
noncomputable def FintX (n : ℕ) : SemiIP Fs :=
  SemiIP.sum (intN p n) fun j => (It p n).comap (fN n j)

/-- `(·,·)_{𝒬_F^n ∩ Q}`: node `j` (at `x_{j+1}`) counts while it lies in the domain -/
noncomputable def FQX (n : ℕ) : SemiIP Fs :=
  SemiIP.sum (range p.m) fun j =>
    (Iw p n (ind p (j + 1)) (ind_nonneg p (j + 1)) (ind_intble p (j + 1) _ _)).comap (fN n j)

/-- `(|w·n| ·,·)_{𝒬_F^n ∩ Q}` -/
noncomputable def FQwX (n : ℕ) : SemiIP Fs :=
  SemiIP.sum (range p.m) fun j =>
    (Iw p n (fun t => p.w * ind p (j + 1) t)
      (fun t => mul_nonneg p.w_pos.le (ind_nonneg p (j + 1) t))
      ((ind_intble p (j + 1) _ _).const_mul p.w)).comap (fN n j)

/-- `(·,·)_{Ω(t_k)}` -/
noncomputable def OmX (k : ℕ) : SemiIP Ts :=
  SemiIP.sum (range p.m) fun i =>
    elemR p i (lo p i (tk p k)) (hi p i (tk p k)) (lo_le_hi p i (tk p k))

theorem QX_apply (n : ℕ) (u v : X) : QX p n u v = ∑ i ∈ range p.m, cutE p n i u v :=
  SemiIP.sum_apply _ _ _ _
theorem QTX_apply (n : ℕ) (u v : X) : QTX p n u v = ∑ i ∈ act p n, full p n i u v :=
  SemiIP.sum_apply _ _ _ _
theorem jX_apply (n : ℕ) (u v : X) : jX p n u v = ∑ i ∈ gpN p n, jF p n i u v :=
  SemiIP.sum_apply _ _ _ _
theorem FgpX_apply (n : ℕ) (a b : Fs) :
    FgpX p n a b = ∑ j ∈ gpN p n, It p n (a n j) (b n j) := SemiIP.sum_apply _ _ _ _
theorem FintX_apply (n : ℕ) (a b : Fs) :
    FintX p n a b = ∑ j ∈ intN p n, It p n (a n j) (b n j) := SemiIP.sum_apply _ _ _ _
theorem FQX_apply (n : ℕ) (a b : Fs) :
    FQX p n a b = ∑ j ∈ range p.m, Iw p n (ind p (j + 1)) (ind_nonneg p (j + 1))
      (ind_intble p (j + 1) _ _) (a n j) (b n j) := SemiIP.sum_apply _ _ _ _
theorem FQwX_apply (n : ℕ) (a b : Fs) :
    FQwX p n a b = ∑ j ∈ range p.m, Iw p n (fun t => p.w * ind p (j + 1) t)
      (fun t => mul_nonneg p.w_pos.le (ind_nonneg p (j + 1) t))
      ((ind_intble p (j + 1) _ _).const_mul p.w) (a n j) (b n j) := SemiIP.sum_apply _ _ _ _
theorem OmX_apply (k : ℕ) (a b : Ts) :
    OmX p k a b = ∑ i ∈ range p.m,
      elemR p i (lo p i (tk p k)) (hi p i (tk p k)) (lo_le_hi p i (tk p k)) a b :=
  SemiIP.sum_apply _ _ _ _

theorem cutE_apply (n i : ℕ) (u v : X) :
    cutE p n i u v = ∫ t in (tk p n)..(tk p n + p.τ),
      qcf p.h (lo p i t) (hi p i t) ((u n i).1 t) ((u n i).2 t) ((v n i).1 t) ((v n i).2 t) :=
  rfl

theorem QTX_nonneg (n : ℕ) (u : X) : 0 ≤ QTX p n u u := (QTX p n).nonneg u
theorem QX_nonneg (n : ℕ) (u : X) : 0 ≤ QX p n u u := (QX p n).nonneg u

/-! ### `Q^n` versus the active mesh -/

theorem cut_inactive {n i : ℕ} (hm : i < p.m) (hi' : i ∉ act p n) (u v : X) :
    cutE p n i u v = 0 := by
  have h' : ¬(x p i ≤ r p (tk p (n + 1)) ∧ ℓ p (tk p n) < x p (i + 1)) :=
    fun h => hi' ((mem_act p).2 ⟨hm, h⟩)
  rw [cutE_apply]
  have : (∫ t in (tk p n)..(tk p n + p.τ),
      qcf p.h (lo p i t) (hi p i t) ((u n i).1 t) ((u n i).2 t) ((v n i).1 t) ((v n i).2 t))
      = ∫ _t in (tk p n)..(tk p n + p.τ), (0 : ℝ) := by
    refine integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le (slab_le p n)] at ht
    simp only [qcf, lo_eq_hi p h' ht]
    ring
  rw [this]; simp

theorem cut_interior {n i : ℕ} (hi' : i ∈ intr p n) (u v : X) :
    cutE p n i u v = full p n i u v := by
  rw [cutE_apply, full_eq_int]
  refine integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le (slab_le p n)] at ht
  obtain ⟨h1, h2⟩ := lo_hi_interior p hi' ht
  simp only [h1, h2]

theorem cut_le_full (n i : ℕ) (u : X) : cutE p n i u u ≤ full p n i u u := by
  rw [cutE_apply, full_eq_int]
  refine integral_mono_on (slab_le p n)
    ((qcf_cont p _ _ (lo_cont p i) (hi_cont p i) _ _ _ _).intervalIntegrable _ _)
    ((qcf_cont p _ _ continuous_const continuous_const _ _ _ _).intervalIntegrable _ _)
    fun t _ => ?_
  exact qcf_le_full p.h_pos.le (lo_nonneg p i t) (lo_le_hi p i t) (hi_le_one p i t) _ _

theorem act_sub (n : ℕ) : act p n ⊆ range p.m := by
  intro i hi; exact mem_range.2 ((mem_act p).1 hi).1

/-- `Q^n` only sees the active elements -/
theorem QX_eq_act (n : ℕ) (u v : X) : QX p n u v = ∑ i ∈ act p n, cutE p n i u v := by
  rw [QX_apply]
  exact (sum_subset (act_sub p n) fun i hi hi' => cut_inactive p (mem_range.1 hi) hi' u v).symm

theorem Q_le_QT' (n : ℕ) (u : X) : QX p n u u ≤ QTX p n u u := by
  rw [QX_eq_act, QTX_apply]
  exact sum_le_sum fun i _ => cut_le_full p n i u

/-- `Q^n` contains the interior elements -/
theorem intr_le_Q (n : ℕ) (u : X) : ∑ i ∈ intr p n, full p n i u u ≤ QX p n u u := by
  rw [QX_eq_act]
  have e : ∑ i ∈ intr p n, full p n i u u = ∑ i ∈ intr p n, cutE p n i u u :=
    sum_congr rfl fun i hi => (cut_interior p hi u u).symm
  rw [e]
  exact sum_le_sum_of_subset_of_nonneg (intr_sub_act p n) fun i _ _ => (cutE p n i).nonneg u

/-! ### Sums over nodes and elements -/

theorem sum_shift_le {s t : Finset ℕ} (h : ∀ j ∈ s, j + 1 ∈ t) {g : ℕ → ℝ} (hg : ∀ i, 0 ≤ g i) :
    ∑ j ∈ s, g (j + 1) ≤ ∑ i ∈ t, g i := by
  have e : ∑ i ∈ s.image (· + 1), g i = ∑ j ∈ s, g (j + 1) :=
    sum_image fun a _ b _ hab => by simpa using hab
  rw [← e]
  refine sum_le_sum_of_subset_of_nonneg (fun i hi => ?_) fun i _ _ => hg i
  obtain ⟨j, hj, rfl⟩ := mem_image.1 hi
  exact h j hj

theorem allN_left {n j : ℕ} (h : j ∈ allN p n) : j ∈ act p n := ((mem_allN p).1 h).1
theorem allN_right {n j : ℕ} (h : j ∈ allN p n) : j + 1 ∈ act p n := ((mem_allN p).1 h).2
theorem intN_sub (n : ℕ) : intN p n ⊆ allN p n := filter_subset _ _
theorem gpN_sub (n : ℕ) : gpN p n ⊆ allN p n := filter_subset _ _

theorem nodes_le (n : ℕ) {f g : ℕ → ℝ} {K : ℝ} (hK : 0 ≤ K) (hg : ∀ i, 0 ≤ g i)
    (h : ∀ j, f j ≤ K * g j) : ∑ j ∈ allN p n, f j ≤ K * ∑ i ∈ act p n, g i := by
  have h1 : ∑ j ∈ allN p n, f j ≤ K * ∑ j ∈ allN p n, g j := sum_le_mul_sum fun j _ => h j
  have h2 : ∑ j ∈ allN p n, g j ≤ ∑ i ∈ act p n, g i :=
    sum_le_sum_of_subset_of_nonneg (fun j hj => allN_left p hj) fun i _ _ => hg i
  have := mul_le_mul_of_nonneg_left h2 hK
  linarith

theorem nodes_le' (n : ℕ) {f g : ℕ → ℝ} {K : ℝ} (hK : 0 ≤ K) (hg : ∀ i, 0 ≤ g i)
    (h : ∀ j, f j ≤ K * g (j + 1)) : ∑ j ∈ allN p n, f j ≤ K * ∑ i ∈ act p n, g i := by
  have h1 : ∑ j ∈ allN p n, f j ≤ K * ∑ j ∈ allN p n, g (j + 1) :=
    sum_le_mul_sum fun j _ => h j
  have h2 : ∑ j ∈ allN p n, g (j + 1) ≤ ∑ i ∈ act p n, g i :=
    sum_shift_le (fun j hj => allN_right p hj) hg
  have := mul_le_mul_of_nonneg_left h2 hK
  linarith

theorem nodes_le2 (n : ℕ) {f g : ℕ → ℝ} {K : ℝ} (hK : 0 ≤ K) (hg : ∀ i, 0 ≤ g i)
    (h : ∀ j, f j ≤ K * (g j + g (j + 1))) :
    ∑ j ∈ allN p n, f j ≤ 2 * K * ∑ i ∈ act p n, g i := by
  have h1 : ∑ j ∈ allN p n, f j
      ≤ K * ∑ j ∈ allN p n, g j + K * ∑ j ∈ allN p n, g (j + 1) := by
    rw [← mul_add, ← sum_add_distrib]
    exact sum_le_mul_sum fun j _ => h j
  have h2 : ∑ j ∈ allN p n, g j ≤ ∑ i ∈ act p n, g i :=
    sum_le_sum_of_subset_of_nonneg (fun j hj => allN_left p hj) fun i _ _ => hg i
  have h3 : ∑ j ∈ allN p n, g (j + 1) ≤ ∑ i ∈ act p n, g i :=
    sum_shift_le (fun j hj => allN_right p hj) hg
  have := mul_le_mul_of_nonneg_left h2 hK
  have := mul_le_mul_of_nonneg_left h3 hK
  linarith

/-- all nodes between active elements are either Ghost penalty nodes or interior nodes -/
theorem Fall (n : ℕ) (a : Fs) :
    FgpX p n a a + FintX p n a a = ∑ j ∈ allN p n, It p n (a n j) (a n j) := by
  rw [FgpX_apply, FintX_apply, sum_nodes]

theorem act_full_nonneg (n : ℕ) (u : X) : 0 ≤ ∑ i ∈ act p n, full p n i u u :=
  sum_nonneg fun i _ => full_nonneg p n i u

/-! ### The facets in the domain -/

/-- a node which is not between two active elements is outside the domain during the slab -/
theorem ind_off {n j : ℕ} (hn : n < p.N) (hj : j < p.m) (hj' : j ∉ allN p n) {t : ℝ}
    (ht : t ∈ Set.Ioo (tk p n) (tk p n + p.τ)) : ind p (j + 1) t = 0 := by
  unfold ind
  rw [if_neg]
  intro h
  apply hj'
  have ht1 : t ≤ tk p (n + 1) := by rw [tk_succ]; exact ht.2.le
  have hr := r_mono p ht1
  have hl := ℓ_mono p ht.1.le
  have hx := (x_lt_x p).2 (Nat.lt_succ_self j)
  have hx' := (x_lt_x p).2 (Nat.lt_succ_self (j + 1))
  have hm : j + 1 < p.m := (x_lt_x p).1 (lt_of_le_of_lt h.2 (r_lt_xm p hn ht1))
  exact (mem_allN p).2 ⟨(mem_act p).2 ⟨hj, by linarith [h.2], by linarith [h.1]⟩,
    (mem_act p).2 ⟨hm, by linarith [h.2], by linarith [h.1]⟩⟩

/-- an interior node is inside the domain during the slab -/
theorem ind_int {n j : ℕ} (hj : j ∈ intN p n) {t : ℝ}
    (ht : t ∈ Set.Ioo (tk p n) (tk p n + p.τ)) : ind p (j + 1) t = 1 := by
  have h1 : j ∈ intr p n := ((mem_filter.1 hj).2).1
  obtain ⟨_, h2, h3⟩ := (mem_intr p).1 h1
  unfold ind
  rw [if_pos]
  have ht1 : t ≤ tk p (n + 1) := by rw [tk_succ]; exact ht.2.le
  have hr := r_mono p ht.1.le
  have hl := ℓ_mono p ht1
  have hx := (x_lt_x p).2 (Nat.lt_succ_self j)
  exact ⟨by linarith, by linarith⟩

theorem FQ_le' {n : ℕ} (hn : n < p.N) (a : Fs) :
    FQX p n a a ≤ FgpX p n a a + FintX p n a a := by
  rw [Fall, FQX_apply]
  have e : ∑ j ∈ allN p n, Iw p n (ind p (j + 1)) (ind_nonneg p (j + 1))
      (ind_intble p (j + 1) _ _) (a n j) (a n j)
      = ∑ j ∈ range p.m, Iw p n (ind p (j + 1)) (ind_nonneg p (j + 1))
        (ind_intble p (j + 1) _ _) (a n j) (a n j) :=
    sum_subset (filter_subset _ _) fun j hj hj' =>
      Iw_eq_zero p n _ _ _ (fun t ht => ind_off p hn (mem_range.1 hj) hj' ht) _ _
  rw [← e]
  exact sum_le_sum fun j _ => Iw_le_It p n _ _ _ (fun t _ => ind_le_one p (j + 1) t) _

theorem Fint_le_FQ' (n : ℕ) (a : Fs) : FintX p n a a ≤ FQX p n a a := by
  rw [FintX_apply, FQX_apply]
  have e : ∑ j ∈ intN p n, It p n (a n j) (a n j)
      = ∑ j ∈ intN p n, Iw p n (ind p (j + 1)) (ind_nonneg p (j + 1))
        (ind_intble p (j + 1) _ _) (a n j) (a n j) :=
    sum_congr rfl fun j hj => (Iw_eq_It p n _ _ _ (fun t ht => ind_int p hj ht) _ _).symm
  rw [e]
  exact sum_le_sum_of_subset_of_nonneg ((intN_sub p n).trans (filter_subset _ _))
    fun j _ _ => (Iw p n _ _ _).nonneg _

/-- `(|w·n| a, b) = w (a, b)` on the facets -/
theorem FQw_eq (n : ℕ) (a b : Fs) : FQwX p n a b = p.w * FQX p n a b := by
  rw [FQwX_apply, FQX_apply, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [Iw_apply, Iw_apply, ← integral_const_mul]
  congr 1; ext t; ring

/-! ### Traces and inverse inequalities on the active mesh -/

include p in
theorem six_le : (6 : ℝ) ≤ P.C := by have := p.hC; linarith

theorem trace_up' (n : ℕ) (u : X) :
    FgpX p n (upX u) (upX u) + FintX p n (upX u) (upX u) ≤ P.C * p.h⁻¹ * QTX p n u u := by
  rw [Fall, QTX_apply]
  have h1 : ∑ j ∈ allN p n, It p n (upX u n j) (upX u n j)
      ≤ 6 * p.h⁻¹ * ∑ i ∈ act p n, full p n i u u :=
    nodes_le p n (by have := hi_pos p; positivity) (fun i => full_nonneg p n i u)
      (fun j => pt1_le p n j u)
  have h2 := mul_le_mul_of_nonneg_right (six_le p)
    (mul_nonneg (hi_pos p).le (act_full_nonneg p n u))
  linarith

theorem trace_dn' (n : ℕ) (u : X) :
    FgpX p n (dnX u) (dnX u) + FintX p n (dnX u) (dnX u) ≤ P.C * p.h⁻¹ * QTX p n u u := by
  rw [Fall, QTX_apply]
  have h1 : ∑ j ∈ allN p n, It p n (dnX u n j) (dnX u n j)
      ≤ 6 * p.h⁻¹ * ∑ i ∈ act p n, full p n i u u :=
    nodes_le' p n (by have := hi_pos p; positivity) (fun i => full_nonneg p n i u)
      (fun j => c0_le p n (j + 1) u)
  have h2 := mul_le_mul_of_nonneg_right (six_le p)
    (mul_nonneg (hi_pos p).le (act_full_nonneg p n u))
  linarith

/-- `‖∂_x u‖²_{𝒬_T^n} = h⁻¹ ∑_i ‖g₁^i‖²` -/
theorem QT_dx (n : ℕ) (u : X) :
    QTX p n (dxX p u) (dxX p u) = p.h⁻¹ * ∑ i ∈ act p n, It p n (c1 n i u) (c1 n i u) := by
  rw [QTX_apply, mul_sum]
  exact sum_congr rfl fun i _ => full_dx p n i u

theorem act_c1_nonneg (n : ℕ) (u : X) : 0 ≤ ∑ i ∈ act p n, It p n (c1 n i u) (c1 n i u) :=
  sum_nonneg fun i _ => It_nonneg p n _

/-- `∑_i ‖g₁^i‖² = h ‖∂_x u‖²_{𝒬_T^n}` -/
theorem act_c1_eq (n : ℕ) (u : X) :
    ∑ i ∈ act p n, It p n (c1 n i u) (c1 n i u) = p.h * QTX p n (dxX p u) (dxX p u) := by
  rw [QT_dx]; have := p.h_pos; field_simp

theorem trace_nfl' (n : ℕ) (u : X) :
    FgpX p n (nflX p u) (nflX p u) + FintX p n (nflX p u) (nflX p u)
      ≤ P.C * p.h⁻¹ * QTX p n (dxX p u) (dxX p u) := by
  rw [Fall, QT_dx]
  have hh := p.h_pos; have hhi := hi_pos p
  have h1 : ∑ j ∈ allN p n, It p n (nflX p u n j) (nflX p u n j)
      ≤ 2 * (p.h⁻¹ ^ 2 / 2) * ∑ i ∈ act p n, It p n (c1 n i u) (c1 n i u) := by
    refine nodes_le2 p n (by positivity) (fun i => It_nonneg p n _) (fun j => ?_)
    have e : nflX p u n j = (-(2 * p.h)⁻¹) • (c1 n j u + c1 n (j + 1) u) := rfl
    rw [e, SemiIP.smul_sq]
    have h2 := (It p n).add_sq_le (c1 n j u) (c1 n (j + 1) u)
    have h3 := mul_le_mul_of_nonneg_left h2 (sq_nonneg (-(2 * p.h)⁻¹))
    have e2 : (-(2 * p.h)⁻¹) ^ 2 * (2 * It p n (c1 n j u) (c1 n j u)
        + 2 * It p n (c1 n (j + 1) u) (c1 n (j + 1) u))
        = p.h⁻¹ ^ 2 / 2 * (It p n (c1 n j u) (c1 n j u)
          + It p n (c1 n (j + 1) u) (c1 n (j + 1) u)) := by
      field_simp
    linarith
  have hS := act_c1_nonneg p n u
  have h1C : (1 : ℝ) ≤ P.C := P.hC
  have h3 := mul_le_mul_of_nonneg_right h1C (mul_nonneg (sq_nonneg p.h⁻¹) hS)
  have e3 : P.C * p.h⁻¹ * (p.h⁻¹ * ∑ i ∈ act p n, It p n (c1 n i u) (c1 n i u))
      = P.C * (p.h⁻¹ ^ 2 * ∑ i ∈ act p n, It p n (c1 n i u) (c1 n i u)) := by ring
  rw [e3]
  linarith

theorem elemR_zero (i : ℕ) {a b : ℝ} (hab : a ≤ b) (h : a = b) (y z : Ts) :
    elemR p i a b hab y z = 0 := by
  unfold elemR
  rw [simpson_closed]
  subst h
  ring

theorem elemR_le_full (i : ℕ) (t : ℝ) (a : Ts) :
    elemR p i (lo p i t) (hi p i t) (lo_le_hi p i t) a a ≤ elemR p i 0 1 zero_le_one a a :=
  simpson_le_full _ _ _ _ _ (lo_nonneg p i t) (hi_le_one p i t) a

/-- at the time levels of slab `n`, `Ω` only meets active elements -/
theorem Om_eq_act (n : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (tk p n) (tk p n + p.τ)) (a b : Ts) :
    ∑ i ∈ range p.m, elemR p i (lo p i t) (hi p i t) (lo_le_hi p i t) a b
      = ∑ i ∈ act p n, elemR p i (lo p i t) (hi p i t) (lo_le_hi p i t) a b :=
  (sum_subset (act_sub p n) fun i hi hi' =>
    elemR_zero p i _ (lo_eq_hi p (fun h => hi' ((mem_act p).2 ⟨mem_range.1 hi, h⟩)) ht) a b).symm

theorem trace_time_sum (n : ℕ) (v : X) :
    OmX p n (botX p n v) (botX p n v) + OmX p (n + 1) (topX p n v) (topX p n v)
      ≤ ∑ i ∈ act p n, (elemR p i 0 1 zero_le_one (botX p n v) (botX p n v)
        + elemR p i 0 1 zero_le_one (topX p n v) (topX p n v)) := by
  rw [OmX_apply, OmX_apply, Om_eq_act p n (slab_left p n), Om_eq_act p n (slab_right p n),
    ← sum_add_distrib]
  exact sum_le_sum fun i _ => add_le_add (elemR_le_full p i _ _) (elemR_le_full p i _ _)

theorem trace_time' (n : ℕ) (v : X) (hv : v ∈ WhX) :
    OmX p n (botX p n v) (botX p n v) + OmX p (n + 1) (topX p n v) (topX p n v)
      ≤ P.C * p.τ⁻¹ * QTX p n v v := by
  have h0 := trace_time_sum p n v
  rw [QTX_apply]
  have h1 : ∑ i ∈ act p n, (elemR p i 0 1 zero_le_one (botX p n v) (botX p n v)
        + elemR p i 0 1 zero_le_one (topX p n v) (topX p n v))
      ≤ 6 * p.τ⁻¹ * ∑ i ∈ act p n, full p n i v v :=
    sum_le_mul_sum fun i _ => elem_time p n i hv
  have h2 := mul_le_mul_of_nonneg_right (six_le p)
    (mul_nonneg (τi_pos p).le (act_full_nonneg p n v))
  linarith

theorem trace_time_cont' (n : ℕ) (v : X) :
    OmX p n (botX p n v) (botX p n v) + OmX p (n + 1) (topX p n v) (topX p n v)
      ≤ P.C * (p.τ⁻¹ * QTX p n v v + p.τ * QTX p n (dtX v) (dtX v)) := by
  have h0 := trace_time_sum p n v
  rw [QTX_apply, QTX_apply]
  have h1 : ∑ i ∈ act p n, (elemR p i 0 1 zero_le_one (botX p n v) (botX p n v)
        + elemR p i 0 1 zero_le_one (topX p n v) (topX p n v))
      ≤ ∑ i ∈ act p n, (4 * (p.τ⁻¹ * full p n i v v)
        + 2 * (p.τ * full p n i (dtX v) (dtX v))) :=
    sum_le_sum fun i _ => elem_time_cont p n i v
  have e : ∑ i ∈ act p n, (4 * (p.τ⁻¹ * full p n i v v)
        + 2 * (p.τ * full p n i (dtX v) (dtX v)))
      = 4 * (p.τ⁻¹ * ∑ i ∈ act p n, full p n i v v)
        + 2 * (p.τ * ∑ i ∈ act p n, full p n i (dtX v) (dtX v)) := by
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum, ← mul_sum]
  rw [e] at h1
  have hA := mul_nonneg (τi_pos p).le (act_full_nonneg p n v)
  have hB := mul_nonneg p.τ_pos.le (act_full_nonneg p n (dtX v))
  have h4 : (4 : ℝ) ≤ P.C := by have := p.hC; linarith
  nlinarith

theorem trace_up_cont' (n : ℕ) (v : X) :
    p.h * (FgpX p n (upX v) (upX v) + FintX p n (upX v) (upX v))
      ≤ P.C * (QTX p n v v + p.h ^ 2 * QTX p n (dxX p v) (dxX p v)) := by
  rw [Fall, mul_sum]
  have h1 : ∑ j ∈ allN p n, p.h * It p n (upX v n j) (upX v n j)
      ≤ 6 * ∑ i ∈ act p n, full p n i v v :=
    nodes_le p n (by norm_num) (fun i => full_nonneg p n i v)
      (fun j => pt1_le_full _ _ _ _ v)
  rw [← QTX_apply] at h1
  have h2 := mul_le_mul_of_nonneg_right (six_le p) (QTX_nonneg p n v)
  have h3 : 0 ≤ P.C * (p.h ^ 2 * QTX p n (dxX p v) (dxX p v)) :=
    mul_nonneg P.C_pos.le (mul_nonneg (sq_nonneg _) (QTX_nonneg p n _))
  linarith

theorem inv_dx' (n : ℕ) (v : X) :
    QTX p n (dxX p v) (dxX p v) ≤ P.C * p.h⁻¹ ^ 2 * QTX p n v v := by
  rw [QT_dx, QTX_apply]
  have hhi := hi_pos p
  have h1 : ∑ i ∈ act p n, It p n (c1 n i v) (c1 n i v)
      ≤ 24 * p.h⁻¹ * ∑ i ∈ act p n, full p n i v v :=
    sum_le_mul_sum fun i _ => c1_le p n i v
  have h2 := mul_le_mul_of_nonneg_left h1 hhi.le
  have hS := act_full_nonneg p n v
  have h24 : (24 : ℝ) ≤ P.C := by have := p.hC; linarith
  have h3 := mul_le_mul_of_nonneg_right h24 (mul_nonneg (sq_nonneg p.h⁻¹) hS)
  nlinarith

theorem jX_nonneg (n : ℕ) (u : X) : 0 ≤ jX p n u u := (jX p n).nonneg u

theorem gp_inv_dx' (n : ℕ) (v : X) :
    jX p n (dxX p v) (dxX p v) ≤ P.C * p.h⁻¹ ^ 2 * jX p n v v := by
  have h0 := jX_nonneg p n v
  rw [jX_apply] at h0 ⊢
  rw [jX_apply]
  have h1 : ∑ i ∈ gpN p n, jF p n i (dxX p v) (dxX p v)
      ≤ 3 * p.h⁻¹ ^ 2 * ∑ i ∈ gpN p n, jF p n i v v :=
    sum_le_mul_sum fun i _ => jF_dx p n i v
  have h3 : (3 : ℝ) ≤ P.C := by have := p.hC; linarith
  have := mul_le_mul_of_nonneg_right h3 (mul_nonneg (sq_nonneg p.h⁻¹) h0)
  nlinarith

theorem gp_facet' (n : ℕ) (v : X) :
    FgpX p n (dnX v - upX v) (dnX v - upX v) ≤ P.C * p.h⁻¹ * jX p n v v := by
  have h0 := jX_nonneg p n v
  rw [jX_apply] at h0 ⊢
  rw [FgpX_apply]
  have hh := p.h_pos; have hhi := hi_pos p
  have h1 : ∑ j ∈ gpN p n, It p n ((dnX v - upX v) n j) ((dnX v - upX v) n j)
      ≤ p.h⁻¹ * ∑ j ∈ gpN p n, jF p n j v v :=
    sum_le_mul_sum fun j _ => by
      rw [jump_node, SemiIP.neg_sq, jF_apply]
      have a := It_nonneg p n (jA n j v)
      have b := It_nonneg p n (jB n j v)
      have e : p.h⁻¹ * (2 * p.h * It p n (jA n j v) (jA n j v)
          + 2 / 3 * p.h * It p n (jB n j v) (jB n j v))
          = 2 * It p n (jA n j v) (jA n j v) + 2 / 3 * It p n (jB n j v) (jB n j v) := by
        field_simp
      rw [e]; linarith
  have h1C : (1 : ℝ) ≤ P.C := P.hC
  have := mul_le_mul_of_nonneg_right h1C (mul_nonneg hhi.le h0)
  nlinarith

/-! ### The material derivative and its discrete version -/

/-- the velocity used in `𝓛` (`0` in Case D, `w` in Case C) -/
noncomputable def wL : ℝ := if p.regime = .D then 0 else p.w

theorem wL_nonneg : 0 ≤ wL p := by unfold wL; split_ifs <;> [exact le_rfl; exact p.w_pos.le]
theorem wL_le : wL p ≤ p.w := by unfold wL; split_ifs <;> [exact p.w_pos.le; exact le_rfl]

/-- `‖w‖ / h ≤ 1 / Δt` (from `w Δt ≤ h`) -/
theorem wL_sq : wL p ^ 2 * p.h⁻¹ ^ 2 ≤ p.τ⁻¹ ^ 2 := by
  have hh := p.h_pos; have hτ := p.τ_pos
  have h1 : wL p * p.τ ≤ p.h := (mul_le_mul_of_nonneg_right (wL_le p) hτ.le).trans p.cfl
  have h2 : (wL p * p.τ) ^ 2 ≤ p.h ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (wL_nonneg p) hτ.le) h1 2
  have e1 : wL p ^ 2 * p.h⁻¹ ^ 2 = (wL p * p.τ) ^ 2 * (p.h⁻¹ ^ 2 * p.τ⁻¹ ^ 2) := by field_simp
  have e2 : p.τ⁻¹ ^ 2 = p.h ^ 2 * (p.h⁻¹ ^ 2 * p.τ⁻¹ ^ 2) := by field_simp
  calc wL p ^ 2 * p.h⁻¹ ^ 2 = (wL p * p.τ) ^ 2 * (p.h⁻¹ ^ 2 * p.τ⁻¹ ^ 2) := e1
    _ ≤ p.h ^ 2 * (p.h⁻¹ ^ 2 * p.τ⁻¹ ^ 2) := mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = p.τ⁻¹ ^ 2 := e2.symm

/-- `w^* · ∇^* = ∂_t + w ∂_x` -/
noncomputable def matX : X →ₗ[ℝ] X := dtX + p.w • dxX p
/-- `𝓛 = 𝓛_h` (`w` is constant) -/
noncomputable def LcX : X →ₗ[ℝ] X := dtX + wL p • dxX p

theorem LcX_apply (u : X) : LcX p u = dtX u + wL p • dxX p u := rfl
theorem matX_apply (u : X) : matX p u = dtX u + p.w • dxX p u := rfl

theorem dx_dx (u : X) : dxX p (dxX p u) = 0 := by
  funext n i
  show ((p.h⁻¹ • (0 : Sm), (0 : Sm)) : V) = 0
  simp

theorem Lc_mem' (u : X) (hu : u ∈ WhX) : LcX p u ∈ WhX :=
  WhX.add_mem (dt_mem' u hu) (WhX.smul_mem _ (dx_mem' p u hu))

theorem Lh_inv_grad' (n : ℕ) (u : X) (hu : u ∈ WhX) :
    QTX p n (dxX p (LcX p u)) (dxX p (LcX p u))
      ≤ P.C * p.τ⁻¹ ^ 2 * QTX p n (dxX p u) (dxX p u) := by
  have e : dxX p (LcX p u) = dxX p (dtX u) := by
    rw [LcX_apply, map_add, map_smul, dx_dx, smul_zero, add_zero]
  rw [e, QT_dx, QT_dx]
  have hhi := hi_pos p
  have h1 : ∑ i ∈ act p n, It p n (c1 n i (dtX u)) (c1 n i (dtX u))
      ≤ 12 * p.τ⁻¹ ^ 2 * ∑ i ∈ act p n, It p n (c1 n i u) (c1 n i u) :=
    sum_le_mul_sum fun i _ => T_inv (compat_c1 p n i) hu
  have h2 := mul_le_mul_of_nonneg_left h1 hhi.le
  have hS := act_c1_nonneg p n u
  have h12 : (12 : ℝ) ≤ P.C := by have := p.hC; linarith
  have h3 := mul_le_mul_of_nonneg_right h12
    (mul_nonneg (sq_nonneg p.τ⁻¹) (mul_nonneg hhi.le hS))
  nlinarith

/-- `‖𝓛 v‖² ≤ 2 ‖∂_t v‖² + 2 w² ‖∂_x v‖²` for any form -/
theorem Lc_sq_le (b : SemiIP X) (v : X) :
    b (LcX p v) (LcX p v) ≤ 2 * b (dtX v) (dtX v) + 2 * (wL p ^ 2 * b (dxX p v) (dxX p v)) := by
  have := b.add_sq_le (dtX v) (wL p • dxX p v)
  rw [SemiIP.smul_sq] at this
  rw [LcX_apply]
  linarith

theorem jF_Lc (n i : ℕ) {u : X} (hu : u ∈ WhX) :
    jF p n i (LcX p u) (LcX p u) ≤ 30 * p.τ⁻¹ ^ 2 * jF p n i u u := by
  have h1 := Lc_sq_le p (jF p n i) u
  have h2 := jF_dt p n i hu
  have h3 := jF_dx p n i u
  have h0 := (jF p n i).nonneg u
  have h4 := mul_le_mul_of_nonneg_left h3 (sq_nonneg (wL p))
  have h5 := mul_le_mul_of_nonneg_right (wL_sq p) h0
  nlinarith

theorem Lh_gp' (n : ℕ) (u : X) (hu : u ∈ WhX) :
    jX p n (LcX p u) (LcX p u)
      ≤ P.C * (p.τ⁻¹ ^ 2 * jX p n u u + p.h ^ 2 * QTX p n (dxX p u) (dxX p u)) := by
  have h0 := jX_nonneg p n u
  rw [jX_apply] at h0 ⊢
  rw [jX_apply]
  have h1 : ∑ i ∈ gpN p n, jF p n i (LcX p u) (LcX p u)
      ≤ 30 * p.τ⁻¹ ^ 2 * ∑ i ∈ gpN p n, jF p n i u u :=
    sum_le_mul_sum fun i _ => jF_Lc p n i hu
  have h30 : (30 : ℝ) ≤ P.C := by have := p.hC; linarith
  have h3 := mul_le_mul_of_nonneg_right h30 (mul_nonneg (sq_nonneg p.τ⁻¹) h0)
  have h4 : 0 ≤ P.C * (p.h ^ 2 * QTX p n (dxX p u) (dxX p u)) :=
    mul_nonneg P.C_pos.le (mul_nonneg (sq_nonneg _) (QTX_nonneg p n _))
  nlinarith

theorem full_Lc (n i : ℕ) {v : X} (hv : v ∈ WhX) :
    full p n i (LcX p v) (LcX p v) ≤ 72 * p.τ⁻¹ ^ 2 * full p n i v v := by
  have h1 := Lc_sq_le p (full p n i) v
  have h2 := full_dt p n i hv
  have h3 := full_dx p n i v
  have h4 := c1_le p n i v
  have h0 := full_nonneg p n i v
  have hhi := hi_pos p
  have h5 : wL p ^ 2 * full p n i (dxX p v) (dxX p v)
      ≤ 24 * (wL p ^ 2 * p.h⁻¹ ^ 2) * full p n i v v := by
    rw [h3]
    have := mul_le_mul_of_nonneg_left h4 (mul_nonneg (sq_nonneg (wL p)) hhi.le)
    nlinarith
  have h6 := mul_le_mul_of_nonneg_right (wL_sq p) h0
  nlinarith

theorem Lc_inv' (n : ℕ) (v : X) (hv : v ∈ WhX) :
    QX p n (LcX p v) (LcX p v) ≤ P.C * p.τ⁻¹ ^ 2 * QTX p n v v := by
  have h0 := Q_le_QT' p n (LcX p v)
  rw [QTX_apply] at h0
  rw [QTX_apply]
  have h1 : ∑ i ∈ act p n, full p n i (LcX p v) (LcX p v)
      ≤ 72 * p.τ⁻¹ ^ 2 * ∑ i ∈ act p n, full p n i v v :=
    sum_le_mul_sum fun i _ => full_Lc p n i hv
  have hS := act_full_nonneg p n v
  have h72 : (72 : ℝ) ≤ P.C := by have := p.hC; linarith
  have h3 := mul_le_mul_of_nonneg_right h72 (mul_nonneg (sq_nonneg p.τ⁻¹) hS)
  nlinarith

theorem jA_Lc (n j : ℕ) (u : X) (hu : u ∈ WhX) :
    It p n (jA n j (LcX p u)) (jA n j (LcX p u))
      ≤ 24 * p.τ⁻¹ ^ 2 * It p n (jA n j u) (jA n j u)
        + 4 * p.τ⁻¹ ^ 2 * (It p n (c1 n j u) (c1 n j u)
          + It p n (c1 n (j + 1) u) (c1 n (j + 1) u)) := by
  have e : jA n j (LcX p u) = jA n j (dtX u) + (wL p * p.h⁻¹) • jB n j u := by
    rw [LcX_apply, map_add, map_smul, jA_dx, smul_smul]
  rw [e]
  have h1 := add_smul_le (It p n) (jA n j (dtX u)) (jB n j u) (wL p * p.h⁻¹)
  have h2 := T_inv (compat_jA p n j) hu
  have h3 : It p n (jB n j u) (jB n j u)
      ≤ 2 * It p n (c1 n j u) (c1 n j u) + 2 * It p n (c1 n (j + 1) u) (c1 n (j + 1) u) :=
    (It p n).sub_sq_le _ _
  have hB := It_nonneg p n (jB n j u)
  have e2 : (wL p * p.h⁻¹) ^ 2 = wL p ^ 2 * p.h⁻¹ ^ 2 := by ring
  rw [e2] at h1
  have h4 := mul_le_mul_of_nonneg_right (wL_sq p) hB
  have h5 := mul_le_mul_of_nonneg_left h3 (sq_nonneg p.τ⁻¹)
  nlinarith

theorem Lh_int_jump' (n : ℕ) (u : X) (hu : u ∈ WhX) :
    FintX p n (dnX (LcX p u) - upX (LcX p u)) (dnX (LcX p u) - upX (LcX p u))
      ≤ P.C * p.τ⁻¹ ^ 2 * (FintX p n (dnX u - upX u) (dnX u - upX u)
        + p.h * QTX p n (dxX p u) (dxX p u)) := by
  rw [FintX_apply, FintX_apply, ← act_c1_eq]
  have h1 : ∑ j ∈ intN p n, It p n ((dnX (LcX p u) - upX (LcX p u)) n j)
        ((dnX (LcX p u) - upX (LcX p u)) n j)
      ≤ ∑ j ∈ intN p n, (24 * p.τ⁻¹ ^ 2 * It p n ((dnX u - upX u) n j) ((dnX u - upX u) n j)
        + 4 * p.τ⁻¹ ^ 2 * (It p n (c1 n j u) (c1 n j u)
          + It p n (c1 n (j + 1) u) (c1 n (j + 1) u))) :=
    sum_le_sum fun j _ => by
      rw [jump_node, jump_node, SemiIP.neg_sq, SemiIP.neg_sq]
      exact jA_Lc p n j u hu
  rw [sum_add_distrib, ← mul_sum, ← mul_sum] at h1
  have h2 : ∑ j ∈ intN p n, (It p n (c1 n j u) (c1 n j u)
        + It p n (c1 n (j + 1) u) (c1 n (j + 1) u))
      ≤ 2 * 1 * ∑ i ∈ act p n, It p n (c1 n i u) (c1 n i u) :=
    (sum_le_sum_of_subset_of_nonneg (intN_sub p n)
      fun j _ _ => add_nonneg (It_nonneg p n _) (It_nonneg p n _)).trans
      (nodes_le2 p n zero_le_one (fun i => It_nonneg p n _) fun j => by linarith)
  have hS : 0 ≤ ∑ j ∈ intN p n, It p n ((dnX u - upX u) n j) ((dnX u - upX u) n j) :=
    sum_nonneg fun j _ => It_nonneg p n _
  have hS2 := act_c1_nonneg p n u
  have hτ2 := sq_nonneg p.τ⁻¹
  have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4 * p.τ⁻¹ ^ 2)
  have h24 : (24 : ℝ) ≤ P.C := by have := p.hC; linarith
  have h4 := mul_le_mul_of_nonneg_right h24 (mul_nonneg hτ2 hS)
  have h5 := mul_le_mul_of_nonneg_right h24 (mul_nonneg hτ2 hS2)
  nlinarith

theorem mat_dt' (n : ℕ) (v : X) :
    QX p n (matX p v - dtX v) (matX p v - dtX v) ≤ p.w ^ 2 * QX p n (dxX p v) (dxX p v) := by
  have e : matX p v - dtX v = p.w • dxX p v := by rw [matX_apply]; abel
  rw [e, SemiIP.smul_sq]

theorem Lc_dt' (n : ℕ) (v : X) :
    QX p n (LcX p v - dtX v) (LcX p v - dtX v) ≤ p.w ^ 2 * QX p n (dxX p v) (dxX p v) := by
  have e : LcX p v - dtX v = wL p • dxX p v := by rw [LcX_apply]; abel
  rw [e, SemiIP.smul_sq]
  have h1 : wL p ^ 2 ≤ p.w ^ 2 := pow_le_pow_left₀ (wL_nonneg p) (wL_le p) 2
  exact mul_le_mul_of_nonneg_right h1 (QX_nonneg p n _)

/-! ### The Ghost penalty estimate -/

theorem x_add2 (i : ℕ) : x p (i + 2) = x p i + 2 * p.h := by unfold x; push_cast; ring
theorem x_add3 (i : ℕ) : x p (i + 3) = x p i + 3 * p.h := by unfold x; push_cast; ring

theorem mem_gpN {n j : ℕ} : j ∈ gpN p n ↔
    j ∈ act p n ∧ j + 1 ∈ act p n ∧ ¬(j ∈ intr p n ∧ j + 1 ∈ intr p n) := by
  unfold gpN
  rw [mem_filter, mem_allN]
  tauto

/-- **Every active element which is not interior is controlled by the Ghost penalty and
the interior elements**, through a chain of at most two Ghost penalty nodes. -/
theorem nonint_le {n : ℕ} (hn : n < p.N) (v : X) {i : ℕ} (hi : i ∈ act p n)
    (hi' : i ∉ intr p n) :
    full p n i v v ≤ 114 * ∑ j ∈ gpN p n, jF p n j v v
      + 3136 * ∑ k ∈ intr p n, full p n k v v := by
  have hh := p.h_pos
  have hJ : ∀ j ∈ gpN p n, jF p n j v v ≤ ∑ j ∈ gpN p n, jF p n j v v := fun j hj =>
    single_le_sum (f := fun j => jF p n j v v) (fun j _ => (jF p n j).nonneg v) hj
  have hS : ∀ k ∈ intr p n, full p n k v v ≤ ∑ k ∈ intr p n, full p n k v v := fun k hk =>
    single_le_sum (f := fun k => full p n k v v) (fun k _ => full_nonneg p n k v) hk
  have hJ0 : 0 ≤ ∑ j ∈ gpN p n, jF p n j v v := sum_nonneg fun j _ => (jF p n j).nonneg v
  have hS0 : 0 ≤ ∑ k ∈ intr p n, full p n k v v := sum_nonneg fun k _ => full_nonneg p n k v
  -- the geometry of the slab
  have ℓs := ℓ_step p n
  have rs := r_step p n
  have ℓm := ℓ_mono p (tk_le p (Nat.le_succ n))
  have rm := r_mono p (tk_le p (Nat.le_succ n))
  have wd : 4 * p.h ≤ r p (tk p n) - ℓ p (tk p n) := by rw [r_sub_ℓ]; exact p.width
  have ℓ0 := ℓ_nonneg p (tk_nonneg p n)
  have rM := r_lt_xm p hn (tk_le p (Nat.le_succ n))
  obtain ⟨hm, h1, h2⟩ := (mem_act p).1 hi
  have x1 := x_succ p i
  by_cases hR : x p (i + 1) ≤ r p (tk p n)
  · -- left boundary: `x_i < ℓ(t_{n+1})`
    have hL : x p i < ℓ p (tk p (n + 1)) := by
      by_contra hc
      exact hi' ((mem_intr p).2 ⟨hm, not_lt.1 hc, hR⟩)
    have x2 := x_add2 p i
    have x3 := x_add3 p i
    by_cases hL1 : ℓ p (tk p (n + 1)) ≤ x p (i + 1)
    · have hm1 : i + 1 < p.m := by
        have : i + 2 < p.m := (x_lt_x p).1 (by linarith)
        omega
      have i1 : i + 1 ∈ intr p n := (mem_intr p).2 ⟨hm1, hL1, by
        have : x p (i + 1 + 1) = x p (i + 2) := rfl
        linarith⟩
      have g : i ∈ gpN p n :=
        (mem_gpN p).2 ⟨hi, intr_sub_act p n i1, fun hc => hi' hc.1⟩
      have := patchL p n i v
      have := hJ i g
      have := hS (i + 1) i1
      linarith
    · have hL2 : x p (i + 1) < ℓ p (tk p (n + 1)) := not_le.1 hL1
      have hm2 : i + 2 < p.m := by
        have : i + 3 < p.m := (x_lt_x p).1 (by linarith)
        omega
      have e2 : x p (i + 1 + 1) = x p (i + 2) := rfl
      have e3 : x p (i + 2 + 1) = x p (i + 3) := rfl
      have a1 : i + 1 ∈ act p n := (mem_act p).2 ⟨by omega, by linarith, by linarith⟩
      have n1 : i + 1 ∉ intr p n := fun hc => by
        have := ((mem_intr p).1 hc).2.1; linarith
      have i2 : i + 2 ∈ intr p n := (mem_intr p).2 ⟨hm2, by linarith, by linarith⟩
      have g0 : i ∈ gpN p n := (mem_gpN p).2 ⟨hi, a1, fun hc => hi' hc.1⟩
      have g1 : i + 1 ∈ gpN p n :=
        (mem_gpN p).2 ⟨a1, intr_sub_act p n i2, fun hc => n1 hc.1⟩
      have := patchL p n i v
      have := patchL p n (i + 1) v
      have := hJ i g0
      have := hJ (i + 1) g1
      have := hS (i + 2) i2
      linarith
  · -- right boundary: `r(t_n) < x_{i+1}`
    have hR' : r p (tk p n) < x p (i + 1) := not_le.1 hR
    have x0 : x p 0 = 0 := by simp [x]
    by_cases hR1 : x p i ≤ r p (tk p n)
    · have hpos : 0 < i := (x_lt_x p).1 (by linarith)
      obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      have xk := x_succ p k
      have ik : k ∈ intr p n := (mem_intr p).2 ⟨by omega, by linarith, hR1⟩
      have g : k ∈ gpN p n := (mem_gpN p).2 ⟨intr_sub_act p n ik, hi, fun hc => hi' hc.2⟩
      have := patchR p n k v
      have := hJ k g
      have := hS k ik
      linarith
    · have hR2 : r p (tk p n) < x p i := not_le.1 hR1
      have x2' : x p 2 = 2 * p.h := by simp [x]
      have h2i : 2 < i := (x_lt_x p).1 (by linarith)
      obtain ⟨k, rfl⟩ : ∃ k, i = k + 2 := ⟨i - 2, by omega⟩
      have xk1 := x_succ p k
      have xk2 := x_add2 p k
      have e2 : x p (k + 1 + 1) = x p (k + 2) := rfl
      have a1 : k + 1 ∈ act p n := (mem_act p).2 ⟨by omega, by linarith, by linarith⟩
      have n1 : k + 1 ∉ intr p n := fun hc => by
        have := ((mem_intr p).1 hc).2.2; linarith
      have ik : k ∈ intr p n := (mem_intr p).2 ⟨by omega, by linarith, by linarith⟩
      have g1 : k + 1 ∈ gpN p n := (mem_gpN p).2 ⟨a1, hi, fun hc => n1 hc.1⟩
      have g0 : k ∈ gpN p n := (mem_gpN p).2 ⟨intr_sub_act p n ik, a1, fun hc => n1 hc.2⟩
      have := patchR p n (k + 1) v
      have := patchR p n k v
      have := hJ (k + 1) g1
      have := hJ k g0
      have := hS k ik
      linarith

/-- a natural number in a real interval of length two takes one of two values -/
theorem two_vals {ρ : ℝ} (hρ : 0 ≤ ρ) {i : ℕ} (h1 : ρ < (i : ℝ) + 1) (h2 : (i : ℝ) ≤ ρ + 1) :
    i = ⌊ρ⌋₊ ∨ i = ⌊ρ⌋₊ + 1 := by
  have f1 := Nat.floor_le hρ
  have f2 := Nat.lt_floor_add_one ρ
  have a1 : ((⌊ρ⌋₊ : ℕ) : ℝ) < ((i + 1 : ℕ) : ℝ) := by push_cast; linarith
  have a2 : ((i : ℕ) : ℝ) < ((⌊ρ⌋₊ + 2 : ℕ) : ℝ) := by push_cast; linarith
  have b1 := Nat.cast_lt.1 a1
  have b2 := Nat.cast_lt.1 a2
  omega

/-- at most four active elements of a slab are not interior -/
theorem nonint_card {n : ℕ} (hn : n < p.N) :
    ((act p n).filter fun i => i ∉ intr p n).card ≤ 4 := by
  have hh := p.h_pos
  have ℓs := ℓ_step p n
  have rs := r_step p n
  have ℓ0 := ℓ_nonneg p (tk_nonneg p n)
  have wd : 4 * p.h ≤ r p (tk p n) - ℓ p (tk p n) := by rw [r_sub_ℓ]; exact p.width
  set kR := ⌊r p (tk p n) / p.h⌋₊ with hkR
  set kL := ⌊ℓ p (tk p n) / p.h⌋₊ with hkL
  have hsub : ((act p n).filter fun i => i ∉ intr p n) ⊆ {kR, kR + 1, kL, kL + 1} := by
    intro i hi
    obtain ⟨ha, hni⟩ := mem_filter.1 hi
    obtain ⟨hm, h1, h2⟩ := (mem_act p).1 ha
    have xi : x p i = i * p.h := rfl
    have x1 : x p (i + 1) = ((i : ℝ) + 1) * p.h := by unfold x; push_cast; ring
    simp only [mem_insert, mem_singleton]
    by_cases hR : x p (i + 1) ≤ r p (tk p n)
    · have hL : x p i < ℓ p (tk p (n + 1)) := by
        by_contra hc
        exact hni ((mem_intr p).2 ⟨hm, not_lt.1 hc, hR⟩)
      have hρ : 0 ≤ ℓ p (tk p n) / p.h := div_nonneg ℓ0 hh.le
      have c1 : ℓ p (tk p n) / p.h < (i : ℝ) + 1 := by
        rw [div_lt_iff₀ hh]; linarith
      have c2 : (i : ℝ) ≤ ℓ p (tk p n) / p.h + 1 := by
        rw [← sub_le_iff_le_add, le_div_iff₀ hh]; linarith
      rcases two_vals hρ c1 c2 with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
    · have hρ : 0 ≤ r p (tk p n) / p.h := div_nonneg (by linarith) hh.le
      have c1 : r p (tk p n) / p.h < (i : ℝ) + 1 := by
        rw [div_lt_iff₀ hh]; linarith [not_le.1 hR]
      have c2 : (i : ℝ) ≤ r p (tk p n) / p.h + 1 := by
        rw [← sub_le_iff_le_add, le_div_iff₀ hh]; linarith
      rcases two_vals hρ c1 c2 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  exact (card_le_card hsub).trans card_le_four

/-- **`lemma_gp_E_IpGP`** for the moving domain. -/
theorem gp' {n : ℕ} (hn : n < p.N) (v : X) :
    QTX p n v v ≤ P.C * (jX p n v v + QX p n v v) := by
  have hQ := intr_le_Q p n v
  rw [QTX_apply, jX_apply]
  set J : ℝ := ∑ j ∈ gpN p n, jF p n j v v with hJ
  set S : ℝ := ∑ k ∈ intr p n, full p n k v v with hS
  have hJ0 : 0 ≤ J := sum_nonneg fun j _ => (jF p n j).nonneg v
  have hS0 : 0 ≤ S := sum_nonneg fun k _ => full_nonneg p n k v
  have e := sum_filter_add_sum_filter_not (act p n) (fun i => i ∈ intr p n)
    (fun i => full p n i v v)
  have h1 : ∑ i ∈ (act p n).filter (fun i => i ∈ intr p n), full p n i v v ≤ S :=
    sum_le_sum_of_subset_of_nonneg (fun i hi => (mem_filter.1 hi).2)
      fun i _ _ => full_nonneg p n i v
  have h2 : ∑ i ∈ (act p n).filter (fun i => i ∉ intr p n), full p n i v v
      ≤ 4 * (114 * J + 3136 * S) := by
    have h3 := sum_le_card_nsmul ((act p n).filter fun i => i ∉ intr p n)
      (fun i => full p n i v v) (114 * J + 3136 * S)
      (fun i hi => nonint_le p hn v (mem_filter.1 hi).1 (mem_filter.1 hi).2)
    rw [nsmul_eq_mul] at h3
    have hc : (((act p n).filter fun i => i ∉ intr p n).card : ℝ) ≤ 4 := by
      exact_mod_cast nonint_card p hn
    have := mul_le_mul_of_nonneg_right hc (by positivity : (0 : ℝ) ≤ 114 * J + 3136 * S)
    linarith
  have hC := p.hC
  nlinarith

/-! ### Integration by parts on the moving cut elements -/

/-- product of smooth functions -/
noncomputable def mulS (f g : Sm) : Sm := Ode.mk (fun t => f t * g t) ((cd f).mul (cd g))

theorem mulS_apply (f g : Sm) (t : ℝ) : mulS f g t = f t * g t := rfl

theorem D_mulS (f g : Sm) (t : ℝ) : D (mulS f g) t = D f t * g t + f t * D g t := by
  have h : HasDerivAt (fun t => f t * g t) (D f t * g t + f t * D g t) t :=
    (hasDerivAt f t).mul (hasDerivAt g t)
  exact h.deriv

/-- The algebra behind the cancellation of the lateral boundary terms (`w^*·n^* = 0`) and the
appearance of the facet terms: for cut positions `clamp s_L`, `clamp s_H` with `s_L < s_H`. -/
theorem cases_id (sL sH A B C : ℝ) (hLH : sL < sH) :
    (1 - mov sH) * (A + clamp sH * B + clamp sH ^ 2 * C)
        - (1 - mov sL) * (A + clamp sL * B + clamp sL ^ 2 * C)
      = (if sL < 1 ∧ 1 ≤ sH then (1 : ℝ) else 0) * (A + B + C)
        - (if sL < 0 ∧ 0 ≤ sH then (1 : ℝ) else 0) * A := by
  have key : ∀ s : ℝ, (s < 0 ∧ clamp s = 0 ∧ mov s = 0) ∨ (0 ≤ s ∧ s < 1 ∧ clamp s = s ∧ mov s = 1)
      ∨ (1 ≤ s ∧ clamp s = 1 ∧ mov s = 0) := by
    intro s
    rcases lt_or_ge s 0 with h | h
    · exact Or.inl ⟨h, clamp_of_nonpos h.le, by unfold mov; rw [if_neg]; intro hh; linarith [hh.1]⟩
    · rcases lt_or_ge s 1 with h1 | h1
      · exact Or.inr (Or.inl ⟨h, h1, clamp_mid h h1.le, by unfold mov; rw [if_pos ⟨h, h1⟩]⟩)
      · exact Or.inr (Or.inr ⟨h1, clamp_of_ge h1,
          by unfold mov; rw [if_neg]; intro hh; linarith [hh.2]⟩)
  have i1 : ∀ c : ℝ, (if sL < c ∧ c ≤ sH then (1 : ℝ) else 0)
      = (if c ≤ sH then (1 : ℝ) else 0) - (if c ≤ sL then (1 : ℝ) else 0) := by
    intro c
    by_cases h1 : c ≤ sH <;> by_cases h2 : c ≤ sL
    · simp [h1, h2, not_lt.2 h2]
    · simp [h1, h2, not_le.1 h2]
    · exfalso; linarith
    · simp [h1, h2]
  rw [i1 1, i1 0]
  rcases key sL with ⟨l1, l2, l3⟩ | ⟨l1, l1', l2, l3⟩ | ⟨l1, l2, l3⟩ <;>
    rcases key sH with ⟨r1, r2, r3⟩ | ⟨r1, r1', r2, r3⟩ | ⟨r1, r2, r3⟩ <;>
    rw [l2, l3, r2, r3] <;> split_ifs <;> first | (exfalso; linarith) | ring

theorem ind_succ_eq (i : ℕ) (t : ℝ) :
    ind p (i + 1) t = if κL p i + μ p * t < 1 ∧ 1 ≤ κR p i + μ p * t then 1 else 0 := by
  unfold ind; simp only [sL_lt_one_iff, sR_ge_one_iff]

theorem ind_self_eq (i : ℕ) (t : ℝ) :
    ind p i t = if κL p i + μ p * t < 0 ∧ 0 ≤ κR p i + μ p * t then 1 else 0 := by
  unfold ind; simp only [sL_neg_iff, sR_nonneg_iff]

theorem mat_fst (u : X) (n i : ℕ) (t : ℝ) :
    (matX p u n i).1 t = D (u n i).1 t + p.w * (p.h⁻¹ * (u n i).2 t) := rfl
theorem mat_snd (u : X) (n i : ℕ) (t : ℝ) :
    (matX p u n i).2 t = D (u n i).2 t + p.w * 0 := rfl

/-- weight of the upwind facet terms at the node `x_k` -/
noncomputable def Iwk (n k : ℕ) : SemiIP Sm :=
  Iw p n (fun t => p.w * ind p k t) (fun t => mul_nonneg p.w_pos.le (ind_nonneg p k t))
    ((ind_intble p k _ _).const_mul p.w)

theorem Iwk_apply (n k : ℕ) (f g : Sm) :
    Iwk p n k f g = ∫ t in (tk p n)..(tk p n + p.τ), p.w * ind p k t * (f t * g t) := rfl

/-- **Integration by parts in space-time on the physical part of one element**: the
contribution of the moving boundary vanishes, the nodes contribute while they are in the
domain. -/
theorem cut_ibp (n i : ℕ) (u v : X) :
    cutE p n i (matX p u) v + cutE p n i u (matX p v)
      = elemR p i (lo p i (tk p (n + 1))) (hi p i (tk p (n + 1))) (lo_le_hi p i _)
          (topX p n u) (topX p n v)
        - elemR p i (lo p i (tk p n)) (hi p i (tk p n)) (lo_le_hi p i _)
          (botX p n u) (botX p n v)
        + Iwk p n (i + 1) (pt n i 1 u) (pt n i 1 v) - Iwk p n i (c0 n i u) (c0 n i v) := by
  set u0 : Sm := (u n i).1 with hu0
  set u1 : Sm := (u n i).2 with hu1
  set v0 : Sm := (v n i).1 with hv0
  set v1 : Sm := (v n i).2 with hv1
  set A : Sm := mulS u0 v0 with hA
  set B : Sm := mulS u0 v1 + mulS u1 v0 with hB
  set C : Sm := mulS u1 v1 with hC
  have hLb := leibniz (κL p i) (μ_nonneg p) A B C (slab_le p n)
  have hRb := leibniz (κR p i) (μ_nonneg p) A B C (slab_le p n)
  have iL := (dPc_intble (κL p i) (μ_nonneg p) A B C (tk p n) (tk p n + p.τ)).const_mul p.h
  have iR := (dPc_intble (κR p i) (μ_nonneg p) A B C (tk p n) (tk p n + p.τ)).const_mul p.h
  have i3 := Iw_intble p n (fun t => p.w * ind p (i + 1) t)
    ((ind_intble p (i + 1) _ _).const_mul p.w) (pt n i 1 u) (pt n i 1 v)
  have i4 := Iw_intble p n (fun t => p.w * ind p i t)
    ((ind_intble p i _ _).const_mul p.w) (c0 n i u) (c0 n i v)
  -- the pointwise identity
  have pw : ∀ t : ℝ,
      qcf p.h (lo p i t) (hi p i t) ((matX p u n i).1 t) ((matX p u n i).2 t) (v0 t) (v1 t)
        + qcf p.h (lo p i t) (hi p i t) (u0 t) (u1 t) ((matX p v n i).1 t) ((matX p v n i).2 t)
      = p.h * dPc (κR p i) A B C (μ p) t - p.h * dPc (κL p i) A B C (μ p) t
        + p.w * ind p (i + 1) t * (pt n i 1 u t * pt n i 1 v t)
        - p.w * ind p i t * (c0 n i u t * c0 n i v t) := by
    intro t
    have key := cases_id (κL p i + μ p * t) (κR p i + μ p * t) (A t) (B t) (C t) (sL_lt_sR p i t)
    have hμ := h_mul_μ p
    have hh := p.h_pos
    have e1 : pt n i 1 u t = u0 t + 1 * u1 t := rfl
    have e2 : pt n i 1 v t = v0 t + 1 * v1 t := rfl
    have e3 : c0 n i u t = u0 t := rfl
    have e4 : c0 n i v t = v0 t := rfl
    have ehh : p.h * p.h⁻¹ = 1 := by field_simp
    rw [ind_succ_eq, ind_self_eq, e1, e2, e3, e4, mat_fst, mat_snd, mat_fst, mat_snd]
    simp only [qcf, dPc, lo, hi, hA, hB, hC, map_add, Sm.add_apply, D_mulS, mulS_apply] at key ⊢
    linear_combination p.w * key
      - (mov (κR p i + μ p * t) * (u0 t * v0 t + clamp (κR p i + μ p * t)
          * (u0 t * v1 t + u1 t * v0 t) + clamp (κR p i + μ p * t) ^ 2 * (u1 t * v1 t))
        - mov (κL p i + μ p * t) * (u0 t * v0 t + clamp (κL p i + μ p * t)
          * (u0 t * v1 t + u1 t * v0 t) + clamp (κL p i + μ p * t) ^ 2 * (u1 t * v1 t))) * hμ
      + (p.w * ((clamp (κR p i + μ p * t) - clamp (κL p i + μ p * t))
            * (u1 t * v0 t + u0 t * v1 t)
          + (clamp (κR p i + μ p * t) ^ 2 - clamp (κL p i + μ p * t) ^ 2) / 2
            * (2 * (u1 t * v1 t)))) * ehh
  -- integrate
  rw [cutE_apply, cutE_apply, ← integral_add
    ((qcf_cont p _ _ (lo_cont p i) (hi_cont p i) _ _ _ _).intervalIntegrable _ _)
    ((qcf_cont p _ _ (lo_cont p i) (hi_cont p i) _ _ _ _).intervalIntegrable _ _)]
  have e : (∫ t in (tk p n)..(tk p n + p.τ),
      (qcf p.h (lo p i t) (hi p i t) ((matX p u n i).1 t) ((matX p u n i).2 t) (v0 t) (v1 t)
        + qcf p.h (lo p i t) (hi p i t) (u0 t) (u1 t) ((matX p v n i).1 t) ((matX p v n i).2 t)))
      = ∫ t in (tk p n)..(tk p n + p.τ),
        (p.h * dPc (κR p i) A B C (μ p) t - p.h * dPc (κL p i) A B C (μ p) t
          + p.w * ind p (i + 1) t * (pt n i 1 u t * pt n i 1 v t)
          - p.w * ind p i t * (c0 n i u t * c0 n i v t)) :=
    integral_congr fun t _ => pw t
  rw [e, integral_sub ((iR.sub iL).add i3) i4, integral_add (iR.sub iL) i3, integral_sub iR iL,
    integral_const_mul, integral_const_mul, hLb, hRb, Iwk_apply, Iwk_apply]
  have eT : elemR p i (lo p i (tk p (n + 1))) (hi p i (tk p (n + 1))) (lo_le_hi p i _)
      (topX p n u) (topX p n v)
      = p.h * (Pc (κR p i) A B C (μ p) (tk p n + p.τ) - Pc (κL p i) A B C (μ p) (tk p n + p.τ)) := by
    unfold elemR
    rw [simpson_closed]
    have d0u : d0 i (topX p n u) = u0 (tk p n + p.τ) := rfl
    have d1u : d1 i (topX p n u) = u1 (tk p n + p.τ) := rfl
    have d0v : d0 i (topX p n v) = v0 (tk p n + p.τ) := rfl
    have d1v : d1 i (topX p n v) = v1 (tk p n + p.τ) := rfl
    simp only [d0u, d1u, d0v, d1v, OmR_apply, Pc, lo, hi, tk_succ, hA, hB, hC, Sm.add_apply,
      mulS_apply]
    ring
  have eB : elemR p i (lo p i (tk p n)) (hi p i (tk p n)) (lo_le_hi p i _)
      (botX p n u) (botX p n v)
      = p.h * (Pc (κR p i) A B C (μ p) (tk p n) - Pc (κL p i) A B C (μ p) (tk p n)) := by
    unfold elemR
    rw [simpson_closed]
    have d0u : d0 i (botX p n u) = u0 (tk p n) := rfl
    have d1u : d1 i (botX p n u) = u1 (tk p n) := rfl
    have d0v : d0 i (botX p n v) = v0 (tk p n) := rfl
    have d1v : d1 i (botX p n v) = v1 (tk p n) := rfl
    simp only [d0u, d1u, d0v, d1v, OmR_apply, Pc, lo, hi, hA, hB, hC, Sm.add_apply, mulS_apply]
    ring
  rw [eT, eB]
  ring

theorem FQwX_apply' (n : ℕ) (a b : Fs) :
    FQwX p n a b = ∑ j ∈ range p.m, Iwk p n (j + 1) (a n j) (b n j) := FQwX_apply p n a b

/-- **Space-time integration by parts** on the moving domain
(first display in the proof of `lemma_B_Bmc`). -/
theorem ibp' {n : ℕ} (hn : n < p.N) (u v : X) :
    QX p n (matX p u) v = -QX p n u (matX p v)
      + OmX p (n + 1) (topX p n u) (topX p n v) - OmX p n (botX p n u) (botX p n v)
      + FQwX p n (upX u) (upX v) - FQwX p n (dnX u) (dnX v) := by
  -- the nodes `x_0` and `x_m` are never in the domain
  have G0 : Iwk p n 0 (c0 n 0 u) (c0 n 0 v) = 0 :=
    Iw_eq_zero p n _ _ _ (fun t ht => by
      rw [ind_zero p ((tk_nonneg p n).trans ht.1.le), mul_zero]) _ _
  have Gm : Iwk p n p.m (c0 n p.m u) (c0 n p.m v) = 0 :=
    Iw_eq_zero p n _ _ _ (fun t ht => by
      rw [ind_m p hn (by rw [tk_succ]; exact ht.2.le), mul_zero]) _ _
  have s1 := sum_range_succ (fun i => Iwk p n i (c0 n i u) (c0 n i v)) p.m
  have s2 := sum_range_succ' (fun i => Iwk p n i (c0 n i u) (c0 n i v)) p.m
  have key := sum_congr (s₁ := range p.m) rfl (fun i _ => cut_ibp p n i u v)
  simp only [sum_add_distrib, sum_sub_distrib] at key
  rw [QX_apply, QX_apply, OmX_apply, OmX_apply, FQwX_apply', FQwX_apply']
  have eup : ∑ j ∈ range p.m, Iwk p n (j + 1) (upX u n j) (upX v n j)
      = ∑ i ∈ range p.m, Iwk p n (i + 1) (pt n i 1 u) (pt n i 1 v) := rfl
  have edn : ∑ j ∈ range p.m, Iwk p n (j + 1) (dnX u n j) (dnX v n j)
      = ∑ j ∈ range p.m, Iwk p n (j + 1) (c0 n (j + 1) u) (c0 n (j + 1) v) := rfl
  rw [eup, edn]
  linarith

/-! ### The model of `Setting` -/

/-- **The convection-diffusion problem on a moving interval as a model of the abstract
setting.** -/
noncomputable def moveSetting : Setting P Unit X Fs Ts where
  regime := p.regime
  N := p.N
  h := p.h
  τ := p.τ
  α := p.α
  wInf := p.w
  h_pos := p.h_pos
  τ_pos := p.τ_pos
  τ_le_one := p.τ_le_one
  h_le := p.h_le
  α_nonneg := p.α_nonneg
  wInf_nonneg := p.w_pos.le
  caseD := p.caseD
  caseC := p.caseC
  Wh := WhX
  Ws := ⊤
  Wh_le_Ws := le_top
  dt := dtX
  dx := fun _ => dxX p
  mat := matX p
  Lc := LcX p
  Lh := LcX p
  up := upX
  dn := dnX
  nfl := nflX p
  bot := botX p
  top := topX p
  dx_mem := fun _ => dx_mem' p
  Lh_mem := Lc_mem' p
  Q := QX p
  QT := QTX p
  j := jX p
  FQ := FQX p
  FQw := FQwX p
  Fgp := FgpX p
  Fint := FintX p
  Om := OmX p
  Q_le_QT := fun n _ => Q_le_QT' p n
  FQ_le := fun n hn => FQ_le' p hn
  Fint_le_FQ := fun n _ => Fint_le_FQ' p n
  FQw_le := fun n _ a => le_of_eq (FQw_eq p n a a)
  trace_up := fun n _ v _ => trace_up' p n v
  trace_dn := fun n _ v _ => trace_dn' p n v
  trace_nfl := fun n _ v _ => by simpa using trace_nfl' p n v
  trace_time := fun n _ => trace_time' p n
  trace_time_cont := fun n _ => trace_time_cont' p n
  trace_up_cont := fun n _ v => by simpa using trace_up_cont' p n v
  inv_dx := fun n _ v _ => by simpa using inv_dx' p n v
  gp := fun n hn v _ => gp' p hn v
  gp_inv_dx := fun n _ v _ => by simpa using gp_inv_dx' p n v
  gp_facet := fun n _ v _ => gp_facet' p n v
  Lc_Lh := fun n _ u _ => by
    have := mul_nonneg (mul_nonneg P.C_pos.le (sq_nonneg p.h)) (QX_nonneg p n (dxX p u))
    simpa using this
  Lh_inv_grad := fun n _ u hu => by simpa using Lh_inv_grad' p n u hu
  Lh_gp := fun n _ u hu => by simpa using Lh_gp' p n u hu
  Lh_int_jump := fun n _ u hu => by simpa using Lh_int_jump' p n u hu
  Lc_inv := fun n _ => Lc_inv' p n
  mat_dt := fun n _ v => by simpa using mat_dt' p n v
  Lc_dt := fun n _ v => by simpa using Lc_dt' p n v
  mat_Lc := fun h => by
    show matX p = LcX p
    unfold matX LcX wL
    rw [if_neg (by rw [h]; decide)]
  ibp := fun n hn u v => ibp' p hn u v

/-! ### The exponential weight -/

/-- The constants of the weight: `c0 = e^{-σT}`, `C_φ = e`, `C_s = 1 + 76 σ²`. -/
noncomputable def moveWConsts : WConsts where
  σ := p.σ
  c0 := Real.exp (-p.σ * tk p p.N)
  Cφ := Real.exp 1
  Cs := 1 + 76 * p.σ ^ 2
  hσ := p.σ_pos
  hCφ := Real.one_le_exp zero_le_one
  hCs := by nlinarith [sq_nonneg p.σ]

theorem c0_le_phi' {k : ℕ} (hk : k ≤ p.N) : Real.exp (-p.σ * tk p p.N) ≤ phiX p k := by
  have h2 := mul_le_mul_of_nonneg_left (tk_le p hk) p.σ_pos.le
  exact Real.exp_le_exp.2 (by linarith)

theorem mat_M' (u : X) : matX p (MX p u) = MX p (matX p u) - p.σ • MX p u := by
  rw [matX_apply, matX_apply, dt_M', dx_M', map_add, map_smul]; abel

theorem Lc_M' (u : X) : LcX p (MX p u) = MX p (LcX p u) - p.σ • MX p u := by
  rw [LcX_apply, LcX_apply, dt_M', dx_M', map_add, map_smul]; abel

theorem M_fst (u : X) (n i : ℕ) (t : ℝ) :
    (MX p u n i).1 t = Real.exp (-p.σ * t) * (u n i).1 t := rfl
theorem M_snd (u : X) (n i : ℕ) (t : ℝ) :
    (MX p u n i).2 t = Real.exp (-p.σ * t) * (u n i).2 t := rfl

theorem Q_symm' (n : ℕ) (u v : X) : QX p n (MX p u) v = QX p n u (MX p v) := by
  rw [QX_apply, QX_apply]
  refine sum_congr rfl fun i _ => ?_
  rw [cutE_apply, cutE_apply]
  congr 1; ext t
  simp only [M_fst, M_snd, qcf]; ring

theorem qcf_e (h a b x0 x1 e : ℝ) :
    qcf h a b x0 x1 (e * x0) (e * x1) = e * qcf h a b x0 x1 x0 x1 := by unfold qcf; ring

theorem qcf_ee (h a b x0 x1 e : ℝ) :
    qcf h a b (e * x0) (e * x1) (e * x0) (e * x1) = e ^ 2 * qcf h a b x0 x1 x0 x1 := by
  unfold qcf; ring

theorem cutE_cont (n i : ℕ) (u v : X) : Continuous fun t =>
    qcf p.h (lo p i t) (hi p i t) ((u n i).1 t) ((u n i).2 t) ((v n i).1 t) ((v n i).2 t) :=
  qcf_cont p _ _ (lo_cont p i) (hi_cont p i) _ _ _ _

theorem Q_lo' (n : ℕ) (u : X) : phiX p (n + 1) * QX p n u u ≤ QX p n u (MX p u) := by
  rw [QX_apply, QX_apply, mul_sum]
  refine sum_le_sum fun i _ => ?_
  rw [cutE_apply, cutE_apply, ← integral_const_mul]
  refine integral_mono_on (slab_le p n) (((cutE_cont p n i u u).intervalIntegrable _ _).const_mul _)
    ((cutE_cont p n i u (MX p u)).intervalIntegrable _ _) fun t ht => ?_
  simp only [M_fst, M_snd, qcf_e]
  have h1 : phiX p (n + 1) ≤ Real.exp (-p.σ * t) := by
    unfold phiX; rw [tk_succ]
    exact Real.exp_le_exp.2 (by nlinarith [ht.2, p.σ_pos])
  exact mul_le_mul_of_nonneg_right h1 (qcf_nonneg p.h_pos.le (lo_le_hi p i t) _ _)

theorem Q_contr' (n : ℕ) (u : X) : QX p n (MX p u) (MX p u) ≤ QX p n u u := by
  rw [QX_apply, QX_apply]
  refine sum_le_sum fun i _ => ?_
  rw [cutE_apply, cutE_apply]
  refine integral_mono_on (slab_le p n) ((cutE_cont p n i _ _).intervalIntegrable _ _)
    ((cutE_cont p n i u u).intervalIntegrable _ _) fun t ht => ?_
  simp only [M_fst, M_snd, qcf_ee]
  have h0 : 0 < Real.exp (-p.σ * t) := Real.exp_pos _
  have h1 : Real.exp (-p.σ * t) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.2 (by nlinarith [ht.1, p.σ_pos, tk_nonneg p n])
  have h2 : Real.exp (-p.σ * t) ^ 2 ≤ 1 := pow_le_one₀ h0.le h1
  have := mul_le_mul_of_nonneg_right h2 (qcf_nonneg p.h_pos.le (lo_le_hi p i t)
    ((u n i).1 t) ((u n i).2 t))
  linarith

theorem superapprox' (n : ℕ) (u : X) (hu : u ∈ WhX) :
    QTX p n (PwX p u - MX p u) (PwX p u - MX p u)
      ≤ (1 + 76 * p.σ ^ 2) * p.τ ^ 2 * QTX p n u u := by
  rw [QTX_apply, QTX_apply]
  have h1 : ∑ i ∈ act p n, full p n i (PwX p u - MX p u) (PwX p u - MX p u)
      ≤ p.σ ^ 2 * p.τ ^ 2 * ∑ i ∈ act p n, full p n i u u :=
    sum_le_mul_sum fun i _ => full_sa p n i hu
  have hS := act_full_nonneg p n u
  have := mul_le_mul_of_nonneg_right (Cs_ge p) (mul_nonneg (sq_nonneg p.τ) hS)
  nlinarith

theorem superapprox_dt' (n : ℕ) (u : X) (hu : u ∈ WhX) :
    QTX p n (dtX (PwX p u - MX p u)) (dtX (PwX p u - MX p u))
      ≤ (1 + 76 * p.σ ^ 2) * QTX p n u u := by
  rw [QTX_apply, QTX_apply]
  have h1 : ∑ i ∈ act p n, full p n i (dtX (PwX p u - MX p u)) (dtX (PwX p u - MX p u))
      ≤ 76 * p.σ ^ 2 * ∑ i ∈ act p n, full p n i u u :=
    sum_le_mul_sum fun i _ => full_sa_dt p n i hu
  have hS := act_full_nonneg p n u
  linarith

/-- **The exponential weight `e^{-σt}` with the temporal `L²` projection on the moving
domain.** -/
noncomputable def moveExpWeight : ExpWeight (moveSetting p) (moveWConsts p) where
  M := MX p
  Mf := MfX p
  lo := fun n => phiX p (n + 1)
  hi := phiX p
  phi := phiX p
  σ_nonneg := p.σ_pos.le
  c0_pos := Real.exp_pos _
  Cφ_nonneg := (Real.exp_pos _).le
  c0_le_lo := fun n hn => c0_le_phi' p (by exact hn)
  hi_le := fun n _ => hi_le' p n
  c0_le_phi := fun n hn => c0_le_phi' p hn
  phi_le_one := fun n _ => phi_le_one' p n
  dx_M := fun _ => dx_M' p
  up_M := up_M' p
  dn_M := fun _ => rfl
  nfl_M := nfl_M' p
  bot_M := fun n _ => bot_M' p n
  top_M := fun n _ => top_M' p n
  mat_M := mat_M' p
  Lc_M := Lc_M' p
  Q_symm := fun n _ => Q_symm' p n
  j_symm := fun n _ u v => by
    show jX p n (MX p u) v = jX p n u (MX p v)
    rw [jX_apply, jX_apply]
    exact sum_congr rfl fun i _ => jF_symm p n i u v
  FQ_symm := fun n _ a b => by
    show FQX p n (MfX p a) b = FQX p n a (MfX p b)
    rw [FQX_apply, FQX_apply]
    exact sum_congr rfl fun j _ => Iw_symm p n _ _ _ _ _
  FQw_symm := fun n _ a b => by
    show FQwX p n (MfX p a) b = FQwX p n a (MfX p b)
    rw [FQwX_apply, FQwX_apply]
    exact sum_congr rfl fun j _ => Iw_symm p n _ _ _ _ _
  Q_lo := fun n _ => Q_lo' p n
  j_lo := fun n _ u => by
    show phiX p (n + 1) * jX p n u u ≤ jX p n u (MX p u)
    rw [jX_apply, jX_apply, mul_sum]
    exact sum_le_sum fun i _ => jF_lo p n i u
  FQ_lo := fun n _ a => by
    show phiX p (n + 1) * FQX p n a a ≤ FQX p n a (MfX p a)
    rw [FQX_apply, FQX_apply, mul_sum]
    exact sum_le_sum fun j _ => Iw_lo p n _ _ _ _
  FQw_lo := fun n _ a => by
    show phiX p (n + 1) * FQwX p n a a ≤ FQwX p n a (MfX p a)
    rw [FQwX_apply, FQwX_apply, mul_sum]
    exact sum_le_sum fun j _ => Iw_lo p n _ _ _ _
  FQ_hi := fun n _ a => by
    show FQX p n a (MfX p a) ≤ phiX p n * FQX p n a a
    rw [FQX_apply, FQX_apply, mul_sum]
    exact sum_le_sum fun j _ => Iw_hi p n _ _ _ _
  Q_contr := fun n _ => Q_contr' p n
  j_contr := fun n _ u => by
    show jX p n (MX p u) (MX p u) ≤ jX p n u u
    rw [jX_apply, jX_apply]
    exact sum_le_sum fun i _ => jF_contr p n i u
  FQ_contr := fun n _ a => by
    show FQX p n (MfX p a) (MfX p a) ≤ FQX p n a a
    rw [FQX_apply, FQX_apply]
    exact sum_le_sum fun j _ => Iw_contr p n _ _ _ _
  FQw_contr := fun n _ a => by
    show FQwX p n (MfX p a) (MfX p a) ≤ FQwX p n a a
    rw [FQwX_apply, FQwX_apply]
    exact sum_le_sum fun j _ => Iw_contr p n _ _ _ _
  Pw := PwX p
  Pw_mem := fun u _ => Pw_mem' p u
  r_mem := fun _ _ => Submodule.mem_top
  r_dx := fun _ => r_dx' p
  superapprox := fun n _ => superapprox' p n
  superapprox_dt := fun n _ => superapprox_dt' p n
  superapprox_gp := fun n _ u hu => by
    show FgpX p n _ _ ≤ (1 + 76 * p.σ ^ 2) * p.τ ^ 2 * FgpX p n _ _
    rw [FgpX_apply, FgpX_apply]
    exact jump_sa p n (gpN p n) hu
  superapprox_int := fun n _ u hu => by
    show FintX p n _ _ ≤ (1 + 76 * p.σ ^ 2) * p.τ ^ 2 * FintX p n _ _
    rw [FintX_apply, FintX_apply]
    exact jump_sa p n (intN p n) hu
  superapprox_j := fun n _ u hu => by
    show jX p n (PwX p u - MX p u) (PwX p u - MX p u)
      ≤ (1 + 76 * p.σ ^ 2) * p.τ ^ 2 * jX p n u u
    have h0 := jX_nonneg p n u
    rw [jX_apply] at h0 ⊢
    rw [jX_apply]
    have h1 : ∑ i ∈ gpN p n, jF p n i (PwX p u - MX p u) (PwX p u - MX p u)
        ≤ p.σ ^ 2 * p.τ ^ 2 * ∑ i ∈ gpN p n, jF p n i u u :=
      sum_le_mul_sum fun i _ => jF_sa p n i hu
    have := mul_le_mul_of_nonneg_right (Cs_ge p) (mul_nonneg (sq_nonneg p.τ) h0)
    nlinarith

/-! ### Consequence: inf-sup stability on the moving domain -/

/-- Inf-sup stability (`thm_stability`) of the unfitted space-time DG method for
convection-diffusion on a moving interval, in both regimes, uniformly in the position of
the domain relative to the mesh, the number of elements and time steps, `h` and `Δt`. -/
theorem move_inf_sup (hlam : P.lam0 (moveWConsts p).Cφ ≤ P.lam)
    (hsmall : ExpWeight.Ksup P (moveWConsts p) * ExpWeight.Kw P (moveWConsts p) * √p.τ ≤ 1 / 8)
    {u : X} (hu : u ∈ WhX) :
    ∃ v ∈ WhX, (moveSetting p).tnj2 v ≤ ExpWeight.Msq P (moveWConsts p) * (moveSetting p).tnj2 u
      ∧ 1 / 8 * (moveSetting p).tnj2 u ≤ (moveSetting p).BJ u v :=
  (moveExpWeight p).inf_sup hlam hsmall hu

/-! ### The parameter assumptions are satisfiable in both regimes -/

/-- Case C: `h = Δt`, `w = 1`, `α = 0`, the domain `(t, 4h + t)` in `[0, (N+5) h]`. -/
noncomputable def paramsC (hC : 13000 ≤ P.C) (N : ℕ) (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    Params P where
  h := τ
  τ := τ
  σ := 1
  h_pos := hτ
  τ_pos := hτ
  τ_le_one := hτ1
  σ_pos := one_pos
  στ := by linarith
  regime := .C
  N := N
  m := N + 5
  α := 0
  w := 1
  ℓ0 := 0
  r0 := 4 * τ
  h_le := by linarith
  α_nonneg := le_refl _
  w_pos := one_pos
  caseD := fun h => by cases h
  caseC := fun _ => by constructor <;> nlinarith
  cfl := by linarith
  ℓ0_nonneg := le_refl _
  r_lt := by push_cast; nlinarith
  width := by linarith
  hC := hC

/-- Case D: as `paramsC`, with `α = 1`. -/
noncomputable def paramsD (hC : 13000 ≤ P.C) (N : ℕ) (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    Params P where
  h := τ
  τ := τ
  σ := 1
  h_pos := hτ
  τ_pos := hτ
  τ_le_one := hτ1
  σ_pos := one_pos
  στ := by linarith
  regime := .D
  N := N
  m := N + 5
  α := 1
  w := 1
  ℓ0 := 0
  r0 := 4 * τ
  h_le := by linarith
  α_nonneg := zero_le_one
  w_pos := one_pos
  caseD := fun _ => by constructor <;> nlinarith
  caseC := fun h => by cases h
  cfl := by linarith
  ℓ0_nonneg := le_refl _
  r_lt := by push_cast; nlinarith
  width := by linarith
  hC := hC

end StDgdg.Move1d
