import StDgdg.Solvability
import StDgdg.Ode.Interval

/-!
# Validation example `d = 0` (ODE), part 2: the model

The DG(1) time stepping method for `u' = f` on `(0, T]`, `T = N Δt`, as a model of
`Setting` and `ExpWeight`: **every assumption of `Setting.lean` is proven** in this case,
uniformly in `N` and `Δt`, for any `Consts` with `C ≥ 12`.

* no space: `ι = Empty`, all facet forms and the Ghost penalty vanish,
* `X` = slab-wise smooth functions, `W_h` = slab-wise affine functions,
* `Q^n = 𝒬_T^n = L²(t_n, t_{n+1})`, `∂_t = w^*·∇^* = 𝓛 = 𝓛_h` = slab-wise derivative,
* the weight is the actual `e^{-σt}`, and `Π_t` the actual slab-wise `L²` projection.

Slab-wise objects are indexed by `ℕ`; the slabs `n ≥ N` are empty here (the restriction
`sl n` vanishes), and `Setting` only asks for the slabs `n < N`.
-/

namespace StDgdg.Ode

open Finset

/-- Parameters of the ODE example: exactly the parameter fields of `Setting`, the weighting
parameter `σ` with `σ Δt ≤ 1`, and `C ≥ 12`. -/
structure Params (P : Consts) where
  regime : Regime
  N : ℕ
  h : ℝ
  τ : ℝ
  α : ℝ
  wInf : ℝ
  σ : ℝ
  h_pos : 0 < h
  τ_pos : 0 < τ
  τ_le_one : τ ≤ 1
  h_le : h ≤ P.C
  α_nonneg : 0 ≤ α
  wInf_nonneg : 0 ≤ wInf
  caseD : regime = .D → h ^ 2 ≤ P.C * α * τ ∧ wInf ^ 2 * τ ≤ P.C * α
  caseC : regime = .C → wInf * τ ≤ P.C * h ∧ h ≤ P.C * wInf * τ
  hC : 12 ≤ P.C
  σ_pos : 0 < σ
  στ : σ * τ ≤ 1

variable {P : Consts} (p : Params P)

/-- Slab-wise smooth functions. -/
abbrev X := ℕ → Sm

/-- `t_k = k Δt`. -/
def tk (k : ℕ) : ℝ := k * p.τ

theorem tk_succ (k : ℕ) : tk p (k + 1) = tk p k + p.τ := by
  unfold tk; push_cast; ring

theorem tk_nonneg (k : ℕ) : 0 ≤ tk p k := mul_nonneg (Nat.cast_nonneg k) p.τ_pos.le

theorem tk_le {k m : ℕ} (h : k ≤ m) : tk p k ≤ tk p m :=
  mul_le_mul_of_nonneg_right (Nat.cast_le.2 h) p.τ_pos.le

/-- Restriction to slab `n` (zero for `n ≥ N`). -/
noncomputable def sl (n : ℕ) : X →ₗ[ℝ] Sm := if n < p.N then LinearMap.proj n else 0

theorem sl_of_lt {n : ℕ} (hn : n < p.N) (u : X) : sl p n u = u n := by simp [sl, hn]
theorem sl_of_not {n : ℕ} (hn : ¬ n < p.N) (u : X) : sl p n u = 0 := by simp [sl, hn]

/-- Slab-wise time derivative. -/
noncomputable def dtX : X →ₗ[ℝ] X := LinearMap.pi fun n => D.comp (LinearMap.proj n)

@[simp] theorem dtX_apply (u : X) (n : ℕ) : dtX u n = D (u n) := rfl

theorem sl_dt (n : ℕ) (u : X) : sl p n (dtX u) = D (sl p n u) := by
  by_cases hn : n < p.N
  · simp [sl_of_lt p hn]
  · simp [sl_of_not p hn]

/-- `(·,·)_{Q^n} = (·,·)_{L²(t_n, t_{n+1})}`. -/
noncomputable def QX (n : ℕ) : SemiIP X := (Iv p.τ_pos (tk p n)).comap (sl p n)

theorem QX_apply (n : ℕ) (u v : X) :
    QX p n u v = Iv p.τ_pos (tk p n) (sl p n u) (sl p n v) := rfl

theorem QX_nonneg (n : ℕ) (u : X) : 0 ≤ QX p n u u := (QX p n).nonneg u

/-- Multiplication on `ℝ` (the "inner product" on a time level for `d = 0`). -/
def OmR : SemiIP ℝ where
  B := LinearMap.mul ℝ ℝ
  symm := mul_comm
  nonneg := mul_self_nonneg

@[simp] theorem OmR_apply (x y : ℝ) : OmR x y = x * y := rfl

/-- Slab-wise affine functions (vanishing on the empty slabs `n ≥ N`). -/
def WhX : Submodule ℝ X where
  carrier := {u | ∀ n, u n ∈ P1 ∧ (p.N ≤ n → u n = 0)}
  add_mem' := fun {u v} hu hv n =>
    ⟨P1.add_mem (hu n).1 (hv n).1, fun h => by
      show u n + v n = 0
      rw [(hu n).2 h, (hv n).2 h, add_zero]⟩
  zero_mem' := fun _ => ⟨P1.zero_mem, fun _ => rfl⟩
  smul_mem' := fun c u hu n =>
    ⟨P1.smul_mem c (hu n).1, fun h => by
      show c • u n = 0
      rw [(hu n).2 h, smul_zero]⟩

theorem mem_WhX {u : X} : u ∈ WhX p ↔ ∀ n, u n ∈ P1 ∧ (p.N ≤ n → u n = 0) := Iff.rfl

theorem sl_mem (n : ℕ) {u : X} (hu : u ∈ WhX p) : sl p n u ∈ P1 := by
  by_cases hn : n < p.N
  · rw [sl_of_lt p hn]; exact (hu n).1
  · rw [sl_of_not p hn]; exact P1.zero_mem

theorem dt_mem {u : X} (hu : u ∈ WhX p) : dtX u ∈ WhX p := fun n =>
  ⟨D_mem_P1 (hu n).1, fun h => by
    show D (u n) = 0
    rw [(hu n).2 h, map_zero]⟩

/-- trace at the bottom of slab `n` -/
noncomputable def botX (n : ℕ) : X →ₗ[ℝ] ℝ := (ev (tk p n)).comp (sl p n)
/-- trace at the top of slab `n` -/
noncomputable def topX (n : ℕ) : X →ₗ[ℝ] ℝ := (ev (tk p n + p.τ)).comp (sl p n)

theorem botX_apply (n : ℕ) (u : X) : botX p n u = sl p n u (tk p n) := rfl
theorem topX_apply (n : ℕ) (u : X) : topX p n u = sl p n u (tk p n + p.τ) := rfl

theorem τi_pos : 0 < p.τ⁻¹ := inv_pos.2 p.τ_pos
theorem hi_pos : 0 < p.h⁻¹ := inv_pos.2 p.h_pos

/-! ### The non-trivial assumptions -/

/-- `eq:std_trace` in time. -/
theorem trace_time' (n : ℕ) (v : X) (hv : v ∈ WhX p) :
    OmR (botX p n v) (botX p n v) + OmR (topX p n v) (topX p n v)
      ≤ P.C * p.τ⁻¹ * QX p n v v := by
  have h := trace_P1 p.τ_pos (tk p n) (sl_mem p n hv)
  have h6 : (6 : ℝ) ≤ P.C := by have := p.hC; linarith
  have h2 := mul_le_mul_of_nonneg_right h6 (mul_nonneg (τi_pos p).le (QX_nonneg p n v))
  simp only [OmR_apply, botX_apply, topX_apply, QX_apply] at h2 ⊢
  linarith

/-- `eq:cont_trace` in time. -/
theorem trace_time_cont' (n : ℕ) (v : X) :
    OmR (botX p n v) (botX p n v) + OmR (topX p n v) (topX p n v)
      ≤ P.C * (p.τ⁻¹ * QX p n v v + p.τ * QX p n (dtX v) (dtX v)) := by
  have hab : tk p n ≤ tk p n + p.τ := le_of_lt (lt_add_of_pos_right _ p.τ_pos)
  have h1 := trace_left hab (sl p n v)
  have h2 := trace_right hab (sl p n v)
  rw [add_sub_cancel_left] at h1 h2
  have hτ := p.τ_pos
  have hI := QX_nonneg p n v
  have hI' := QX_nonneg p n (dtX v)
  have h1' := mul_le_mul_of_nonneg_left h1 (τi_pos p).le
  have h2' := mul_le_mul_of_nonneg_left h2 (τi_pos p).le
  have e1 : ∀ x : ℝ, p.τ⁻¹ * (p.τ * x) = x := fun x => by field_simp
  have e2 : ∀ x y : ℝ, p.τ⁻¹ * (2 * x + p.τ ^ 2 * y) = 2 * (p.τ⁻¹ * x) + p.τ * y :=
    fun x y => by field_simp
  rw [e1, e2] at h1' h2'
  have h4 : (4 : ℝ) ≤ P.C := by have := p.hC; linarith
  have h5 := mul_le_mul_of_nonneg_right h4
    (add_nonneg (mul_nonneg (τi_pos p).le hI) (mul_nonneg hτ.le hI'))
  simp only [OmR_apply, botX_apply, topX_apply, QX_apply, sl_dt] at h5 hI hI' ⊢
  nlinarith [mul_nonneg (τi_pos p).le hI, mul_nonneg hτ.le hI']

/-- `eq:std_inverse` in time. -/
theorem Lc_inv' (n : ℕ) (v : X) (hv : v ∈ WhX p) :
    QX p n (dtX v) (dtX v) ≤ P.C * p.τ⁻¹ ^ 2 * QX p n v v := by
  have h := inv_P1 p.τ_pos (tk p n) (sl_mem p n hv)
  have h2 := mul_le_mul_of_nonneg_right p.hC
    (mul_nonneg (sq_nonneg p.τ⁻¹) (QX_nonneg p n v))
  simp only [QX_apply, sl_dt] at h2 ⊢
  linarith

/-- Integration by parts in time. -/
theorem ibp' (n : ℕ) (u v : X) :
    QX p n (dtX u) v = -QX p n u (dtX v) + OmR (topX p n u) (topX p n v)
      - OmR (botX p n u) (botX p n v) := by
  simp only [QX_apply, sl_dt, OmR_apply, botX_apply, topX_apply]
  exact ip_D _ _ _

/-! ### The model of `Setting` -/

/-- **The ODE model of the abstract setting.** -/
noncomputable def odeSetting : Setting P Empty X ℝ ℝ where
  regime := p.regime
  N := p.N
  h := p.h
  τ := p.τ
  α := p.α
  wInf := p.wInf
  h_pos := p.h_pos
  τ_pos := p.τ_pos
  τ_le_one := p.τ_le_one
  h_le := p.h_le
  α_nonneg := p.α_nonneg
  wInf_nonneg := p.wInf_nonneg
  caseD := p.caseD
  caseC := p.caseC
  Wh := WhX p
  Ws := ⊤
  Wh_le_Ws := le_top
  dt := dtX
  dx := fun i => i.elim
  mat := dtX
  Lc := dtX
  Lh := dtX
  up := 0
  dn := 0
  nfl := 0
  bot := botX p
  top := topX p
  dx_mem := fun i => i.elim
  Lh_mem := fun _ hu => dt_mem p hu
  Q := QX p
  QT := QX p
  j := fun _ => SemiIP.zero X
  FQ := fun _ => SemiIP.zero ℝ
  FQw := fun _ => SemiIP.zero ℝ
  Fgp := fun _ => SemiIP.zero ℝ
  Fint := fun _ => SemiIP.zero ℝ
  Om := fun _ => OmR
  Q_le_QT := fun _ _ _ => le_refl _
  FQ_le := by simp [SemiIP.zero]
  Fint_le_FQ := by simp [SemiIP.zero]
  FQw_le := by simp [SemiIP.zero]
  trace_up := fun n _ v _ => by
    simpa [SemiIP.zero] using mul_nonneg (mul_nonneg P.C_pos.le (hi_pos p).le) (QX_nonneg p n v)
  trace_dn := fun n _ v _ => by
    simpa [SemiIP.zero] using mul_nonneg (mul_nonneg P.C_pos.le (hi_pos p).le) (QX_nonneg p n v)
  trace_nfl := by simp [SemiIP.zero]
  trace_time := fun n _ => trace_time' p n
  trace_time_cont := fun n _ => trace_time_cont' p n
  trace_up_cont := fun n _ v => by
    simpa [SemiIP.zero] using mul_nonneg P.C_pos.le (QX_nonneg p n v)
  inv_dx := fun n _ v _ => by
    simpa using mul_nonneg (mul_nonneg P.C_pos.le (sq_nonneg p.h⁻¹)) (QX_nonneg p n v)
  gp := fun n _ v _ => by
    have h1 : (1 : ℝ) ≤ P.C := P.hC
    have := mul_le_mul_of_nonneg_right h1 (QX_nonneg p n v)
    simpa [SemiIP.zero] using this
  gp_inv_dx := by simp [SemiIP.zero]
  gp_facet := by simp [SemiIP.zero]
  Lc_Lh := by simp
  Lh_inv_grad := by simp
  Lh_gp := by simp [SemiIP.zero]
  Lh_int_jump := by simp [SemiIP.zero]
  Lc_inv := fun n _ => Lc_inv' p n
  mat_dt := by simp
  Lc_dt := by simp
  mat_Lc := fun _ => rfl
  ibp := fun n _ u v => by
    simpa [SemiIP.zero] using ibp' p n u v

/-! ### The exponential weight and the temporal `L²` projection -/

/-- `u ↦ e^{-σt} u`. -/
noncomputable def MX : X →ₗ[ℝ] X := LinearMap.pi fun n => (Mexp p.σ).comp (LinearMap.proj n)

@[simp] theorem MX_apply (u : X) (n : ℕ) : MX p u n = Mexp p.σ (u n) := rfl

theorem sl_M (n : ℕ) (u : X) : sl p n (MX p u) = Mexp p.σ (sl p n u) := by
  by_cases hn : n < p.N
  · simp [sl_of_lt p hn]
  · simp [sl_of_not p hn]

/-- `u ↦ Π_t(e^{-σt} u)`, the slab-wise `L²` projection onto `P¹`. -/
noncomputable def PwX : X →ₗ[ℝ] X :=
  LinearMap.pi fun n => (Pi p.τ_pos (tk p n)).comp ((Mexp p.σ).comp (LinearMap.proj n))

@[simp] theorem PwX_apply (u : X) (n : ℕ) :
    PwX p u n = Pi p.τ_pos (tk p n) (Mexp p.σ (u n)) := rfl

/-- `φ(t_k)`, capped at `t_N = T`. -/
noncomputable def phiX (k : ℕ) : ℝ := Real.exp (-p.σ * tk p (min k p.N))

/-- The constants of the weight: `c0 = e^{-σT}`, `C_φ = e`, `C_s = 1 + 76 σ²`. -/
noncomputable def odeWConsts : WConsts where
  σ := p.σ
  c0 := Real.exp (-p.σ * tk p p.N)
  Cφ := Real.exp 1
  Cs := 1 + 76 * p.σ ^ 2
  hσ := p.σ_pos
  hCφ := Real.one_le_exp zero_le_one
  hCs := by nlinarith [sq_nonneg p.σ]

theorem c0_le_phi' (k : ℕ) : Real.exp (-p.σ * tk p p.N) ≤ phiX p k := by
  have h1 := tk_le p (min_le_right k p.N)
  have h2 := mul_le_mul_of_nonneg_left h1 p.σ_pos.le
  exact Real.exp_le_exp.2 (by linarith)

theorem phi_le_one' (k : ℕ) : phiX p k ≤ 1 := by
  have := mul_nonneg p.σ_pos.le (tk_nonneg p (min k p.N))
  exact Real.exp_le_one_iff.2 (by linarith)

theorem hi_le' (n : ℕ) : phiX p n ≤ Real.exp 1 * phiX p (n + 1) := by
  unfold phiX
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have h1 : tk p (min (n + 1) p.N) ≤ tk p (min n p.N) + p.τ := by
    rw [← tk_succ]; exact tk_le p (by omega)
  have h2 := mul_le_mul_of_nonneg_left h1 p.σ_pos.le
  have := p.στ
  linarith

theorem Q_symm' (n : ℕ) (u v : X) : QX p n (MX p u) v = QX p n u (MX p v) := by
  simp only [QX_apply, sl_M]
  exact ip_Mexp_symm _ _ _ _

theorem Q_lo' (n : ℕ) (u : X) : phiX p (n + 1) * QX p n u u ≤ QX p n u (MX p u) := by
  by_cases hn : n < p.N
  · simp only [QX_apply, sl_M]
    apply ip_Mexp_lo _ p.σ_pos.le
    unfold phiX
    rw [Nat.min_eq_left (by omega), tk_succ]
  · simp [QX_apply, sl_of_not p hn]

theorem Q_contr' (n : ℕ) (u : X) : QX p n (MX p u) (MX p u) ≤ QX p n u u := by
  simp only [QX_apply, sl_M]
  exact ip_Mexp_contr _ p.σ_pos.le (tk_nonneg p n) _

theorem bot_M' (n : ℕ) (u : X) : botX p n (MX p u) = phiX p n • botX p n u := by
  by_cases hn : n < p.N
  · simp only [botX_apply, sl_M, Mexp_apply, smul_eq_mul]
    unfold phiX
    rw [Nat.min_eq_left hn.le]
  · simp [botX_apply, sl_of_not p hn]

theorem top_M' (n : ℕ) (u : X) : topX p n (MX p u) = phiX p (n + 1) • topX p n u := by
  by_cases hn : n < p.N
  · simp only [topX_apply, sl_M, Mexp_apply, smul_eq_mul]
    unfold phiX
    rw [Nat.min_eq_left (by omega), tk_succ]
  · simp [topX_apply, sl_of_not p hn]

theorem dt_M' (u : X) : dtX (MX p u) = MX p (dtX u) - p.σ • MX p u := by
  funext n
  exact D_Mexp p.σ (u n)

theorem Pw_mem' {u : X} (hu : u ∈ WhX p) : PwX p u ∈ WhX p := fun n =>
  ⟨Pi_mem _ _ _, fun h => by
    show Pi p.τ_pos (tk p n) (Mexp p.σ (u n)) = 0
    rw [(hu n).2 h, map_zero, map_zero]⟩

/-- `lemma_superapprox`, `eq_superapprox`. -/
theorem superapprox' (n : ℕ) (u : X) (hu : u ∈ WhX p) :
    QX p n (PwX p u - MX p u) (PwX p u - MX p u)
      ≤ (1 + 76 * p.σ ^ 2) * p.τ ^ 2 * QX p n u u := by
  by_cases hn : n < p.N
  · have h := superapprox_iv p.τ_pos (tk p n) p.σ_pos.le (tk_nonneg p n) (hu n).1
    have hI := (Iv p.τ_pos (tk p n)).nonneg (u n)
    simp only [QX_apply, sl_of_lt p hn, Pi.sub_apply, PwX_apply, MX_apply]
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg p.σ) (sq_nonneg p.τ)) hI,
      mul_nonneg (sq_nonneg p.τ) hI]
  · simp [QX_apply, sl_of_not p hn]

/-- `lemma_superapprox`, `eq_superapprox_dt`. -/
theorem superapprox_dt' (n : ℕ) (u : X) (hu : u ∈ WhX p) :
    QX p n (dtX (PwX p u - MX p u)) (dtX (PwX p u - MX p u))
      ≤ (1 + 76 * p.σ ^ 2) * QX p n u u := by
  by_cases hn : n < p.N
  · have h := superapprox_dt_iv p.τ_pos (tk p n) p.σ_pos.le (tk_nonneg p n) (hu n).1
    have hI := (Iv p.τ_pos (tk p n)).nonneg (u n)
    simp only [QX_apply, sl_of_lt p hn, dtX_apply, Pi.sub_apply, PwX_apply, MX_apply]
    linarith
  · simp [QX_apply, sl_of_not p hn]

/-- **The ODE model of the exponential weight** `e^{-σt}` with the temporal `L²`
projection. -/
noncomputable def odeExpWeight : ExpWeight (odeSetting p) (odeWConsts p) where
  M := MX p
  Mf := 0
  lo := fun n => phiX p (n + 1)
  hi := phiX p
  phi := phiX p
  σ_nonneg := p.σ_pos.le
  c0_pos := Real.exp_pos _
  Cφ_nonneg := (Real.exp_pos _).le
  c0_le_lo := fun n _ => c0_le_phi' p (n + 1)
  hi_le := fun n _ => hi_le' p n
  c0_le_phi := fun n _ => c0_le_phi' p n
  phi_le_one := fun n _ => phi_le_one' p n
  dx_M := fun i => i.elim
  up_M := by simp [odeSetting]
  dn_M := by simp [odeSetting]
  nfl_M := by simp [odeSetting]
  bot_M := fun n _ => bot_M' p n
  top_M := fun n _ => top_M' p n
  mat_M := dt_M' p
  Lc_M := dt_M' p
  Q_symm := fun n _ => Q_symm' p n
  j_symm := by simp [odeSetting, SemiIP.zero]
  FQ_symm := by simp [odeSetting, SemiIP.zero]
  FQw_symm := by simp [odeSetting, SemiIP.zero]
  Q_lo := fun n _ => Q_lo' p n
  j_lo := by simp [odeSetting, SemiIP.zero]
  FQ_lo := by simp [odeSetting, SemiIP.zero]
  FQw_lo := by simp [odeSetting, SemiIP.zero]
  FQ_hi := by simp [odeSetting, SemiIP.zero]
  Q_contr := fun n _ => Q_contr' p n
  j_contr := by simp [odeSetting, SemiIP.zero]
  FQ_contr := by simp [odeSetting, SemiIP.zero]
  FQw_contr := by simp [odeSetting, SemiIP.zero]
  Pw := PwX p
  Pw_mem := fun _ hu => Pw_mem' p hu
  r_mem := fun _ _ => Submodule.mem_top
  r_dx := fun i => i.elim
  superapprox := fun n _ => superapprox' p n
  superapprox_dt := fun n _ => superapprox_dt' p n
  superapprox_gp := by simp [odeSetting, SemiIP.zero]
  superapprox_int := by simp [odeSetting, SemiIP.zero]
  superapprox_j := by simp [odeSetting, SemiIP.zero]

/-! ### Consequences: the abstract theorems hold for the DG(1) time stepping method -/

/-- Inf-sup stability (`thm_stability`) of DG(1) in time for the ODE, uniformly in `N`
and `Δt`. -/
theorem ode_inf_sup (hlam : P.lam0 (odeWConsts p).Cφ ≤ P.lam)
    (hsmall : ExpWeight.Ksup P (odeWConsts p) * ExpWeight.Kw P (odeWConsts p) * √p.τ ≤ 1 / 8)
    {u : X} (hu : u ∈ WhX p) :
    ∃ v ∈ WhX p, (odeSetting p).tnj2 v ≤ ExpWeight.Msq P (odeWConsts p) * (odeSetting p).tnj2 u
      ∧ 1 / 8 * (odeSetting p).tnj2 u ≤ (odeSetting p).BJ u v :=
  (odeExpWeight p).inf_sup hlam hsmall hu

/-! ### The parameter assumptions are satisfiable in both regimes -/

/-- Case D with `h = Δt`, `α = ‖w‖_∞ = σ = 1`. -/
noncomputable def paramsD (hC : 12 ≤ P.C) (N : ℕ) (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    Params P where
  regime := .D
  N := N
  h := τ
  τ := τ
  α := 1
  wInf := 1
  σ := 1
  h_pos := hτ
  τ_pos := hτ
  τ_le_one := hτ1
  h_le := by linarith
  α_nonneg := zero_le_one
  wInf_nonneg := zero_le_one
  caseD := fun _ => by constructor <;> nlinarith
  caseC := fun h => by cases h
  hC := hC
  σ_pos := one_pos
  στ := by linarith

/-- Case C with `h = Δt`, `α = 0`, `‖w‖_∞ = σ = 1`. -/
noncomputable def paramsC (hC : 12 ≤ P.C) (N : ℕ) (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    Params P where
  regime := .C
  N := N
  h := τ
  τ := τ
  α := 0
  wInf := 1
  σ := 1
  h_pos := hτ
  τ_pos := hτ
  τ_le_one := hτ1
  h_le := by linarith
  α_nonneg := le_refl _
  wInf_nonneg := zero_le_one
  caseD := fun h => by cases h
  caseC := fun _ => by constructor <;> nlinarith
  hC := hC
  σ_pos := one_pos
  στ := by linarith

end StDgdg.Ode
