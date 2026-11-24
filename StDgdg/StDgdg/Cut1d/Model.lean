import StDgdg.Cut1d.Elements

/-!
# Validation example `d = 1`: the unfitted heat equation on an interval

Space-time DG (`P¹` in space, `P¹` in time) for `∂_t u - α ∂_xx u = f` on the fixed domain
`Ω = ((1-δ_L) h, (M+1+δ_R) h)`, which cuts the uniform background mesh `K_i = [ih, (i+1)h]`
in the elements `K_0` and `K_{M+1}` at **arbitrary** positions `δ_L, δ_R ∈ (0,1)`; the
elements `K_1, …, K_M` (`M ≥ 1`) are uncut. Here `w = 0` (Case D).

**Every assumption of `Setting.lean` is proven, uniformly in `δ_L, δ_R`, `M`, `N`, `h`,
`Δt`**, for any `Consts` with `C ≥ 120`.

The Ghost penalty acts on the nodes `0` and `M` (see `Elements.lean` for the modelling).
-/

namespace StDgdg.Cut1d

open Finset Ode SemiIP

/-- Parameters of the example. -/
structure Params (P : Consts) extends Base where
  N : ℕ
  M : ℕ
  α : ℝ
  δL : ℝ
  δR : ℝ
  hM : 1 ≤ M
  h_le : h ≤ P.C
  α_nonneg : 0 ≤ α
  caseD : h ^ 2 ≤ P.C * α * τ
  hC : 120 ≤ P.C
  δL_pos : 0 < δL
  δL_lt : δL < 1
  δR_pos : 0 < δR
  δR_lt : δR < 1

instance {P : Consts} : CoeOut (Params P) Base := ⟨Params.toBase⟩

variable {P : Consts} (p : Params P)

/-! ### Geometry: the physical part `[lo i, hi i]` of element `i` (in local coordinates) -/

noncomputable def lo (i : ℕ) : ℝ := if i = 0 then 1 - p.δL else 0
noncomputable def hi (i : ℕ) : ℝ := if i = p.M + 1 then p.δR else 1

theorem lo_nonneg (i : ℕ) : 0 ≤ lo p i := by
  unfold lo; split_ifs <;> linarith [p.δL_lt]

theorem hi_le_one (i : ℕ) : hi p i ≤ 1 := by
  unfold hi; split_ifs <;> linarith [p.δR_lt]

theorem lo_le_hi (i : ℕ) : lo p i ≤ hi p i := by
  unfold lo hi
  split_ifs with h1 h2
  · exfalso; omega
  · linarith [p.δL_pos]
  · linarith [p.δR_pos]
  · norm_num

/-! ### Volume forms -/

/-- `(·,·)_{Q^n}` -/
noncomputable def QX (n : ℕ) : SemiIP X :=
  SemiIP.sum (range (p.M + 2)) fun i => elem p n i (lo p i) (hi p i) (lo_le_hi p i)

/-- `(·,·)_{𝒬_T^n}` -/
noncomputable def QTX (n : ℕ) : SemiIP X := SemiIP.sum (range (p.M + 2)) fun i => full p n i

theorem QX_apply (n : ℕ) (u v : X) :
    QX p n u v = ∑ i ∈ range (p.M + 2), elem p n i (lo p i) (hi p i) (lo_le_hi p i) u v :=
  SemiIP.sum_apply _ _ _ _

theorem QTX_apply (n : ℕ) (u v : X) : QTX p n u v = ∑ i ∈ range (p.M + 2), full p n i u v :=
  SemiIP.sum_apply _ _ _ _

/-! ### Time levels -/

/-- `(·,·)_Ω` -/
noncomputable def OmX : SemiIP Ts :=
  SemiIP.sum (range (p.M + 2)) fun i => elemR p i (lo p i) (hi p i) (lo_le_hi p i)

theorem OmX_apply (a b : Ts) :
    OmX p a b = ∑ i ∈ range (p.M + 2), elemR p i (lo p i) (hi p i) (lo_le_hi p i) a b :=
  SemiIP.sum_apply _ _ _ _

/-! ### Facets (nodes) -/

/-- the Ghost penalty nodes: those adjacent to a cut element -/
def gpS : Finset ℕ := {0, p.M}
/-- the remaining (interior) nodes -/
def intS : Finset ℕ := Ico 1 p.M

/-- `(·,·)` over all nodes `× I_n` (all nodes lie in `Ω`) -/
noncomputable def FQX (n : ℕ) : SemiIP Fs :=
  SemiIP.sum (range (p.M + 1)) fun i => (It p n).comap (fN n i)
noncomputable def FgpX (n : ℕ) : SemiIP Fs :=
  SemiIP.sum (gpS p) fun i => (It p n).comap (fN n i)
noncomputable def FintX (n : ℕ) : SemiIP Fs :=
  SemiIP.sum (intS p) fun i => (It p n).comap (fN n i)

theorem nodes_split (f : ℕ → ℝ) :
    ∑ i ∈ range (p.M + 1), f i = ∑ i ∈ gpS p, f i + ∑ i ∈ intS p, f i := by
  have hM := p.hM
  have e : range (p.M + 1) = gpS p ∪ intS p := by
    ext i; simp only [gpS, intS, mem_range, mem_union, mem_insert, mem_singleton, mem_Ico]; omega
  have hd : Disjoint (gpS p) (intS p) := by
    rw [Finset.disjoint_left]
    intro i hi
    simp only [gpS, intS, mem_insert, mem_singleton, mem_Ico] at hi ⊢
    omega
  rw [e, sum_union hd]

theorem gp_sum (f : ℕ → ℝ) : ∑ i ∈ gpS p, f i = f 0 + f p.M := by
  have hM := p.hM
  unfold gpS
  rw [sum_pair (by omega)]

/-- `j_h^n` -/
noncomputable def jX (n : ℕ) : SemiIP X := SemiIP.sum (gpS p) fun i => jF p n i

theorem jX_apply (n : ℕ) (u v : X) : jX p n u v = jF p n 0 u v + jF p n p.M u v := by
  unfold jX; rw [SemiIP.sum_apply, gp_sum]

/-! ### Element-wise facts -/

theorem elem_le_full (n i : ℕ) (u : X) :
    elem p n i (lo p i) (hi p i) (lo_le_hi p i) u u ≤ full p n i u u :=
  simpson_le_full _ _ _ _ _ (lo_nonneg p i) (hi_le_one p i) u

/-- for the uncut elements, the physical part is the whole element -/
theorem elem_mid (n : ℕ) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ p.M) (u v : X) :
    elem p n i (lo p i) (hi p i) (lo_le_hi p i) u v = full p n i u v := by
  have e1 : lo p i = 0 := by
    unfold lo; split_ifs with h
    · omega
    · rfl
  have e2 : hi p i = 1 := by
    unfold hi; split_ifs with h
    · omega
    · rfl
  simp only [elem, simpson_closed, e1, e2]

/-! ### Sums over nodes and elements -/

theorem sum_nodes_le {m : ℕ} {f g : ℕ → ℝ} {K : ℝ} (hK : 0 ≤ K) (hg : ∀ i, 0 ≤ g i)
    (h : ∀ i, f i ≤ K * g i) : ∑ i ∈ range (m + 1), f i ≤ K * ∑ i ∈ range (m + 2), g i := by
  rw [sum_range_succ _ (m + 1), mul_add]
  have h1 : ∑ i ∈ range (m + 1), f i ≤ K * ∑ i ∈ range (m + 1), g i :=
    sum_le_mul_sum fun i _ => h i
  have := mul_nonneg hK (hg (m + 1))
  linarith

theorem sum_nodes_le' {m : ℕ} {f g : ℕ → ℝ} {K : ℝ} (hK : 0 ≤ K) (hg : ∀ i, 0 ≤ g i)
    (h : ∀ i, f i ≤ K * g (i + 1)) :
    ∑ i ∈ range (m + 1), f i ≤ K * ∑ i ∈ range (m + 2), g i := by
  rw [sum_range_succ' _ (m + 1), mul_add]
  have h1 : ∑ i ∈ range (m + 1), f i ≤ K * ∑ i ∈ range (m + 1), g (i + 1) :=
    sum_le_mul_sum fun i _ => h i
  have := mul_nonneg hK (hg 0)
  linarith

theorem sum_nodes_le2 {m : ℕ} {f g : ℕ → ℝ} {K : ℝ} (hK : 0 ≤ K) (hg : ∀ i, 0 ≤ g i)
    (h : ∀ i, f i ≤ K * (g i + g (i + 1))) :
    ∑ i ∈ range (m + 1), f i ≤ 2 * K * ∑ i ∈ range (m + 2), g i := by
  have h1 : ∑ i ∈ range (m + 1), f i
      ≤ K * ∑ i ∈ range (m + 1), g i + K * ∑ i ∈ range (m + 1), g (i + 1) := by
    rw [← mul_add, ← sum_add_distrib]
    exact sum_le_mul_sum fun i _ => h i
  have e1 := sum_range_succ g (m + 1)
  have e2 := sum_range_succ' g (m + 1)
  have := mul_nonneg hK (hg (m + 1))
  have := mul_nonneg hK (hg 0)
  nlinarith

/-- `∑_{i ≤ M+1} = ∑_{uncut} + (i = 0) + (i = M+1)` -/
theorem elems_split (g : ℕ → ℝ) :
    ∑ i ∈ range (p.M + 2), g i = ∑ i ∈ range p.M, g (i + 1) + g 0 + g (p.M + 1) := by
  rw [sum_range_succ _ (p.M + 1), sum_range_succ' _ p.M]

/-! ### The assumptions of `Setting` -/

theorem QTX_nonneg (n : ℕ) (u : X) : 0 ≤ QTX p n u u := (QTX p n).nonneg u
theorem QX_nonneg (n : ℕ) (u : X) : 0 ≤ QX p n u u := (QX p n).nonneg u

theorem Q_le_QT' (n : ℕ) (u : X) : QX p n u u ≤ QTX p n u u := by
  rw [QX_apply, QTX_apply]
  exact sum_le_sum fun i _ => elem_le_full p n i u

theorem FQX_apply (n : ℕ) (a b : Fs) :
    FQX p n a b = ∑ i ∈ range (p.M + 1), It p n (a n i) (b n i) := SemiIP.sum_apply _ _ _ _
theorem FgpX_apply (n : ℕ) (a b : Fs) :
    FgpX p n a b = ∑ i ∈ gpS p, It p n (a n i) (b n i) := SemiIP.sum_apply _ _ _ _
theorem FintX_apply (n : ℕ) (a b : Fs) :
    FintX p n a b = ∑ i ∈ intS p, It p n (a n i) (b n i) := SemiIP.sum_apply _ _ _ _

/-- all nodes are either Ghost penalty nodes or interior nodes -/
theorem Fall (n : ℕ) (a : Fs) :
    FgpX p n a a + FintX p n a a = ∑ i ∈ range (p.M + 1), It p n (a n i) (a n i) := by
  rw [FgpX_apply, FintX_apply, ← nodes_split]

theorem FQ_le' (n : ℕ) (a : Fs) : FQX p n a a ≤ FgpX p n a a + FintX p n a a := by
  rw [Fall, FQX_apply]

theorem Fint_le_FQ' (n : ℕ) (a : Fs) : FintX p n a a ≤ FQX p n a a := by
  have := Fall p n a
  rw [← FQX_apply] at this
  have := (FgpX p n).nonneg a
  linarith

include p in
theorem six_le : (6 : ℝ) ≤ P.C := by have := p.hC; linarith

theorem trace_up' (n : ℕ) (u : X) :
    FgpX p n (upX u) (upX u) + FintX p n (upX u) (upX u) ≤ P.C * p.h⁻¹ * QTX p n u u := by
  rw [Fall, QTX_apply]
  have h1 : ∑ i ∈ range (p.M + 1), It p n (upX u n i) (upX u n i)
      ≤ 6 * p.h⁻¹ * ∑ i ∈ range (p.M + 2), full p n i u u :=
    sum_nodes_le (by have := hi_pos p; positivity) (fun i => full_nonneg p n i u)
      (fun i => pt1_le p n i u)
  have hS : 0 ≤ ∑ i ∈ range (p.M + 2), full p n i u u :=
    sum_nonneg fun i _ => full_nonneg p n i u
  have h2 := mul_le_mul_of_nonneg_right (six_le p) (mul_nonneg (hi_pos p).le hS)
  linarith

theorem trace_dn' (n : ℕ) (u : X) :
    FgpX p n (dnX u) (dnX u) + FintX p n (dnX u) (dnX u) ≤ P.C * p.h⁻¹ * QTX p n u u := by
  rw [Fall, QTX_apply]
  have h1 : ∑ i ∈ range (p.M + 1), It p n (dnX u n i) (dnX u n i)
      ≤ 6 * p.h⁻¹ * ∑ i ∈ range (p.M + 2), full p n i u u :=
    sum_nodes_le' (by have := hi_pos p; positivity) (fun i => full_nonneg p n i u)
      (fun i => c0_le p n (i + 1) u)
  have hS : 0 ≤ ∑ i ∈ range (p.M + 2), full p n i u u :=
    sum_nonneg fun i _ => full_nonneg p n i u
  have h2 := mul_le_mul_of_nonneg_right (six_le p) (mul_nonneg (hi_pos p).le hS)
  linarith

/-- `‖∂_x u‖²_{𝒬_T^n} = h⁻¹ ∑_i ‖g₁^i‖²` -/
theorem QT_dx (n : ℕ) (u : X) :
    QTX p n (dxX p u) (dxX p u) = p.h⁻¹ * ∑ i ∈ range (p.M + 2), It p n (c1 n i u) (c1 n i u) := by
  rw [QTX_apply, mul_sum]
  exact sum_congr rfl fun i _ => full_dx p n i u

theorem QT_dx_nonneg (n : ℕ) (u : X) : 0 ≤ QTX p n (dxX p u) (dxX p u) := QTX_nonneg p n _

theorem trace_nfl' (n : ℕ) (u : X) :
    FgpX p n (nflX p u) (nflX p u) + FintX p n (nflX p u) (nflX p u)
      ≤ P.C * p.h⁻¹ * QTX p n (dxX p u) (dxX p u) := by
  rw [Fall, QT_dx]
  have hh := p.h_pos; have hhi := hi_pos p
  have h1 : ∑ i ∈ range (p.M + 1), It p n (nflX p u n i) (nflX p u n i)
      ≤ 2 * (p.h⁻¹ ^ 2 / 2) * ∑ i ∈ range (p.M + 2), It p n (c1 n i u) (c1 n i u) := by
    refine sum_nodes_le2 (by positivity) (fun i => It_nonneg p n _) (fun i => ?_)
    have e : nflX p u n i = (-(2 * p.h)⁻¹) • (c1 n i u + c1 n (i + 1) u) := rfl
    rw [e, SemiIP.smul_sq]
    have h2 := (It p n).add_sq_le (c1 n i u) (c1 n (i + 1) u)
    have h3 := mul_le_mul_of_nonneg_left h2 (sq_nonneg (-(2 * p.h)⁻¹))
    have e2 : (-(2 * p.h)⁻¹) ^ 2 * (2 * It p n (c1 n i u) (c1 n i u)
        + 2 * It p n (c1 n (i + 1) u) (c1 n (i + 1) u))
        = p.h⁻¹ ^ 2 / 2 * (It p n (c1 n i u) (c1 n i u)
          + It p n (c1 n (i + 1) u) (c1 n (i + 1) u)) := by
      field_simp
    linarith
  have hS : 0 ≤ ∑ i ∈ range (p.M + 2), It p n (c1 n i u) (c1 n i u) :=
    sum_nonneg fun i _ => It_nonneg p n _
  have h1C : (1 : ℝ) ≤ P.C := P.hC
  have h3 := mul_le_mul_of_nonneg_right h1C (mul_nonneg (sq_nonneg p.h⁻¹) hS)
  have e3 : P.C * p.h⁻¹ * (p.h⁻¹ * ∑ i ∈ range (p.M + 2), It p n (c1 n i u) (c1 n i u))
      = P.C * (p.h⁻¹ ^ 2 * ∑ i ∈ range (p.M + 2), It p n (c1 n i u) (c1 n i u)) := by ring
  rw [e3]
  linarith

theorem elemR_le_full (i : ℕ) (a : Ts) :
    elemR p i (lo p i) (hi p i) (lo_le_hi p i) a a ≤ elemR p i 0 1 zero_le_one a a :=
  simpson_le_full _ _ _ _ _ (lo_nonneg p i) (hi_le_one p i) a

theorem trace_time' (n : ℕ) (v : X) (hv : v ∈ WhX) :
    OmX p (botX p n v) (botX p n v) + OmX p (topX p n v) (topX p n v)
      ≤ P.C * p.τ⁻¹ * QTX p n v v := by
  rw [OmX_apply, OmX_apply, QTX_apply, ← sum_add_distrib]
  have h1 : ∑ i ∈ range (p.M + 2), (elemR p i (lo p i) (hi p i) (lo_le_hi p i) (botX p n v)
      (botX p n v) + elemR p i (lo p i) (hi p i) (lo_le_hi p i) (topX p n v) (topX p n v))
      ≤ 6 * p.τ⁻¹ * ∑ i ∈ range (p.M + 2), full p n i v v :=
    sum_le_mul_sum fun i _ =>
      (add_le_add (elemR_le_full p i _) (elemR_le_full p i _)).trans (elem_time p n i hv)
  have hS : 0 ≤ ∑ i ∈ range (p.M + 2), full p n i v v :=
    sum_nonneg fun i _ => full_nonneg p n i v
  have h2 := mul_le_mul_of_nonneg_right (six_le p) (mul_nonneg (τi_pos p).le hS)
  linarith

theorem trace_time_cont' (n : ℕ) (v : X) :
    OmX p (botX p n v) (botX p n v) + OmX p (topX p n v) (topX p n v)
      ≤ P.C * (p.τ⁻¹ * QTX p n v v + p.τ * QTX p n (dtX v) (dtX v)) := by
  rw [OmX_apply, OmX_apply, QTX_apply, QTX_apply, ← sum_add_distrib]
  have h1 : ∑ i ∈ range (p.M + 2), (elemR p i (lo p i) (hi p i) (lo_le_hi p i) (botX p n v)
      (botX p n v) + elemR p i (lo p i) (hi p i) (lo_le_hi p i) (topX p n v) (topX p n v))
      ≤ ∑ i ∈ range (p.M + 2), (4 * (p.τ⁻¹ * full p n i v v)
        + 2 * (p.τ * full p n i (dtX v) (dtX v))) :=
    sum_le_sum fun i _ =>
      (add_le_add (elemR_le_full p i _) (elemR_le_full p i _)).trans (elem_time_cont p n i v)
  have e : ∑ i ∈ range (p.M + 2), (4 * (p.τ⁻¹ * full p n i v v)
        + 2 * (p.τ * full p n i (dtX v) (dtX v)))
      = 4 * (p.τ⁻¹ * ∑ i ∈ range (p.M + 2), full p n i v v)
        + 2 * (p.τ * ∑ i ∈ range (p.M + 2), full p n i (dtX v) (dtX v)) := by
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum, ← mul_sum]
  rw [e] at h1
  have hS : 0 ≤ ∑ i ∈ range (p.M + 2), full p n i v v :=
    sum_nonneg fun i _ => full_nonneg p n i v
  have hS' : 0 ≤ ∑ i ∈ range (p.M + 2), full p n i (dtX v) (dtX v) :=
    sum_nonneg fun i _ => full_nonneg p n i _
  have hA : 0 ≤ p.τ⁻¹ * ∑ i ∈ range (p.M + 2), full p n i v v := mul_nonneg (τi_pos p).le hS
  have hB : 0 ≤ p.τ * ∑ i ∈ range (p.M + 2), full p n i (dtX v) (dtX v) :=
    mul_nonneg p.τ_pos.le hS'
  have h4 : (4 : ℝ) ≤ P.C := by have := p.hC; linarith
  nlinarith

theorem trace_up_cont' (n : ℕ) (v : X) :
    p.h * (FgpX p n (upX v) (upX v) + FintX p n (upX v) (upX v))
      ≤ P.C * (QTX p n v v + p.h ^ 2 * QTX p n (dxX p v) (dxX p v)) := by
  rw [Fall, mul_sum]
  have h1 : ∑ i ∈ range (p.M + 1), p.h * It p n (upX v n i) (upX v n i)
      ≤ 6 * ∑ i ∈ range (p.M + 2), full p n i v v :=
    sum_nodes_le (by norm_num) (fun i => full_nonneg p n i v)
      (fun i => pt1_le_full _ _ _ _ v)
  rw [← QTX_apply] at h1
  have h2 := mul_le_mul_of_nonneg_right (six_le p) (QTX_nonneg p n v)
  have h3 : 0 ≤ P.C * (p.h ^ 2 * QTX p n (dxX p v) (dxX p v)) :=
    mul_nonneg P.C_pos.le (mul_nonneg (sq_nonneg _) (QT_dx_nonneg p n v))
  linarith

theorem inv_dx' (n : ℕ) (v : X) :
    QTX p n (dxX p v) (dxX p v) ≤ P.C * p.h⁻¹ ^ 2 * QTX p n v v := by
  rw [QT_dx, QTX_apply]
  have hhi := hi_pos p
  have h1 : ∑ i ∈ range (p.M + 2), It p n (c1 n i v) (c1 n i v)
      ≤ 24 * p.h⁻¹ * ∑ i ∈ range (p.M + 2), full p n i v v :=
    sum_le_mul_sum fun i _ => c1_le p n i v
  have h2 := mul_le_mul_of_nonneg_left h1 hhi.le
  have hS : 0 ≤ ∑ i ∈ range (p.M + 2), full p n i v v :=
    sum_nonneg fun i _ => full_nonneg p n i v
  have h24 : (24 : ℝ) ≤ P.C := by have := p.hC; linarith
  have h3 := mul_le_mul_of_nonneg_right h24 (mul_nonneg (sq_nonneg p.h⁻¹) hS)
  nlinarith

/-- **`lemma_gp_E_IpGP`**, uniformly in the cut positions. -/
theorem gp' (n : ℕ) (v : X) : QTX p n v v ≤ P.C * (jX p n v v + QX p n v v) := by
  have hM := p.hM
  rw [QTX_apply, QX_apply, jX_apply, elems_split, elems_split]
  set S : ℝ := ∑ i ∈ range p.M, full p n (i + 1) v v with hS
  have hS0 : 0 ≤ S := sum_nonneg fun i _ => full_nonneg p n _ v
  have e : ∑ i ∈ range p.M, elem p n (i + 1) (lo p (i + 1)) (hi p (i + 1)) (lo_le_hi p (i + 1)) v v
      = S := sum_congr rfl fun i hi =>
    elem_mid p n (by omega) (by have := mem_range.1 hi; omega) v v
  rw [e]
  have f1 : full p n 1 v v ≤ S := by
    have := single_le_sum (f := fun i => full p n (i + 1) v v)
      (fun i _ => full_nonneg p n _ v) (mem_range.2 (by omega : 0 < p.M))
    simpa using this
  have f2 : full p n p.M v v ≤ S := by
    have := single_le_sum (f := fun i => full p n (i + 1) v v)
      (fun i _ => full_nonneg p n _ v) (mem_range.2 (by omega : p.M - 1 < p.M))
    have e : p.M - 1 + 1 = p.M := by omega
    simp only [e] at this
    exact this
  have g1 := patchL p n 0 v
  have g2 := patchR p n p.M v
  rw [zero_add] at g1
  have n1 := (elem p n 0 (lo p 0) (hi p 0) (lo_le_hi p 0)).nonneg v
  have n2 := (elem p n (p.M + 1) (lo p (p.M + 1)) (hi p (p.M + 1)) (lo_le_hi p (p.M + 1))).nonneg v
  have j1 := (jF p n 0).nonneg v
  have j2 := (jF p n p.M).nonneg v
  have hC := p.hC
  nlinarith

theorem gp_inv_dx' (n : ℕ) (v : X) :
    jX p n (dxX p v) (dxX p v) ≤ P.C * p.h⁻¹ ^ 2 * jX p n v v := by
  rw [jX_apply, jX_apply]
  have h1 := jF_dx p n 0 v
  have h2 := jF_dx p n p.M v
  have j1 := (jF p n 0).nonneg v
  have j2 := (jF p n p.M).nonneg v
  have h3 : (3 : ℝ) ≤ P.C := by have := p.hC; linarith
  have := mul_le_mul_of_nonneg_right h3
    (mul_nonneg (sq_nonneg p.h⁻¹) (add_nonneg j1 j2))
  nlinarith

theorem gp_facet' (n : ℕ) (v : X) :
    FgpX p n (dnX v - upX v) (dnX v - upX v) ≤ P.C * p.h⁻¹ * jX p n v v := by
  rw [FgpX_apply, gp_sum, jX_apply, jump_node, jump_node, SemiIP.neg_sq, SemiIP.neg_sq,
    jF_apply, jF_apply]
  have hh := p.h_pos; have hhi := hi_pos p
  have a0 := It_nonneg p n (jA n 0 v); have aM := It_nonneg p n (jA n p.M v)
  have b0 := It_nonneg p n (jB n 0 v); have bM := It_nonneg p n (jB n p.M v)
  have hC := p.hC
  have e : P.C * p.h⁻¹ * (2 * p.h * It p n (jA n 0 v) (jA n 0 v)
        + 2 / 3 * p.h * It p n (jB n 0 v) (jB n 0 v)
        + (2 * p.h * It p n (jA n p.M v) (jA n p.M v)
          + 2 / 3 * p.h * It p n (jB n p.M v) (jB n p.M v)))
      = P.C * (2 * It p n (jA n 0 v) (jA n 0 v) + 2 / 3 * It p n (jB n 0 v) (jB n 0 v)
        + (2 * It p n (jA n p.M v) (jA n p.M v) + 2 / 3 * It p n (jB n p.M v) (jB n p.M v))) := by
    field_simp
  rw [e]
  nlinarith

theorem QX_dx_nonneg (n : ℕ) (u : X) : 0 ≤ QX p n (dxX p u) (dxX p u) := QX_nonneg p n _

theorem Lh_inv_grad' (n : ℕ) (u : X) (hu : u ∈ WhX) :
    QTX p n (dxX p (dtX u)) (dxX p (dtX u))
      ≤ P.C * p.τ⁻¹ ^ 2 * QTX p n (dxX p u) (dxX p u) := by
  rw [QT_dx, QT_dx]
  have hhi := hi_pos p
  have h1 : ∑ i ∈ range (p.M + 2), It p n (c1 n i (dtX u)) (c1 n i (dtX u))
      ≤ 12 * p.τ⁻¹ ^ 2 * ∑ i ∈ range (p.M + 2), It p n (c1 n i u) (c1 n i u) :=
    sum_le_mul_sum fun i _ => T_inv (compat_c1 p n i) hu
  have h2 := mul_le_mul_of_nonneg_left h1 hhi.le
  have hS : 0 ≤ ∑ i ∈ range (p.M + 2), It p n (c1 n i u) (c1 n i u) :=
    sum_nonneg fun i _ => It_nonneg p n _
  have h12 : (12 : ℝ) ≤ P.C := by have := p.hC; linarith
  have h3 := mul_le_mul_of_nonneg_right h12
    (mul_nonneg (sq_nonneg p.τ⁻¹) (mul_nonneg hhi.le hS))
  nlinarith

theorem Lh_gp' (n : ℕ) (u : X) (hu : u ∈ WhX) :
    jX p n (dtX u) (dtX u)
      ≤ P.C * (p.τ⁻¹ ^ 2 * jX p n u u + p.h ^ 2 * QTX p n (dxX p u) (dxX p u)) := by
  rw [jX_apply, jX_apply]
  have h1 := jF_dt p n 0 hu
  have h2 := jF_dt p n p.M hu
  have j1 := (jF p n 0).nonneg u
  have j2 := (jF p n p.M).nonneg u
  have h12 : (12 : ℝ) ≤ P.C := by have := p.hC; linarith
  have h3 := mul_le_mul_of_nonneg_right h12
    (mul_nonneg (sq_nonneg p.τ⁻¹) (add_nonneg j1 j2))
  have h4 : 0 ≤ P.C * (p.h ^ 2 * QTX p n (dxX p u) (dxX p u)) :=
    mul_nonneg P.C_pos.le (mul_nonneg (sq_nonneg _) (QT_dx_nonneg p n u))
  nlinarith

theorem Lh_int_jump' (n : ℕ) (u : X) (hu : u ∈ WhX) :
    FintX p n (dnX (dtX u) - upX (dtX u)) (dnX (dtX u) - upX (dtX u))
      ≤ P.C * p.τ⁻¹ ^ 2 * (FintX p n (dnX u - upX u) (dnX u - upX u)
        + p.h * QTX p n (dxX p u) (dxX p u)) := by
  rw [FintX_apply, FintX_apply]
  have h1 : ∑ i ∈ intS p, It p n ((dnX (dtX u) - upX (dtX u)) n i) ((dnX (dtX u) - upX (dtX u)) n i)
      ≤ 12 * p.τ⁻¹ ^ 2 * ∑ i ∈ intS p, It p n ((dnX u - upX u) n i) ((dnX u - upX u) n i) :=
    sum_le_mul_sum fun i _ => by
      rw [jump_node, jump_node, SemiIP.neg_sq, SemiIP.neg_sq]
      exact T_inv (compat_jA p n i) hu
  have hS : 0 ≤ ∑ i ∈ intS p, It p n ((dnX u - upX u) n i) ((dnX u - upX u) n i) :=
    sum_nonneg fun i _ => It_nonneg p n _
  have h12 : (12 : ℝ) ≤ P.C := by have := p.hC; linarith
  have h3 := mul_le_mul_of_nonneg_right h12 (mul_nonneg (sq_nonneg p.τ⁻¹) hS)
  have h4 : 0 ≤ P.C * p.τ⁻¹ ^ 2 * (p.h * QTX p n (dxX p u) (dxX p u)) :=
    mul_nonneg (mul_nonneg P.C_pos.le (sq_nonneg _))
      (mul_nonneg p.h_pos.le (QT_dx_nonneg p n u))
  nlinarith

theorem Lc_inv' (n : ℕ) (v : X) (hv : v ∈ WhX) :
    QX p n (dtX v) (dtX v) ≤ P.C * p.τ⁻¹ ^ 2 * QTX p n v v := by
  have h0 := Q_le_QT' p n (dtX v)
  rw [QTX_apply] at h0
  rw [QTX_apply]
  have h1 : ∑ i ∈ range (p.M + 2), full p n i (dtX v) (dtX v)
      ≤ 12 * p.τ⁻¹ ^ 2 * ∑ i ∈ range (p.M + 2), full p n i v v :=
    sum_le_mul_sum fun i _ => full_dt p n i hv
  have hS : 0 ≤ ∑ i ∈ range (p.M + 2), full p n i v v :=
    sum_nonneg fun i _ => full_nonneg p n i v
  have h12 : (12 : ℝ) ≤ P.C := by have := p.hC; linarith
  have h3 := mul_le_mul_of_nonneg_right h12 (mul_nonneg (sq_nonneg p.τ⁻¹) hS)
  nlinarith

theorem ibp' (n : ℕ) (u v : X) :
    QX p n (dtX u) v = -QX p n u (dtX v) + OmX p (topX p n u) (topX p n v)
      - OmX p (botX p n u) (botX p n v) := by
  rw [QX_apply, QX_apply, OmX_apply, OmX_apply, ← sum_neg_distrib, ← sum_add_distrib,
    ← sum_sub_distrib]
  exact sum_congr rfl fun i _ => elem_ibp p n i _ u v

/-! ### The model of `Setting` -/

/-- **The unfitted heat equation in one space dimension as a model of the abstract
setting.** -/
noncomputable def cutSetting : Setting P Unit X Fs Ts where
  regime := .D
  N := p.N
  h := p.h
  τ := p.τ
  α := p.α
  wInf := 0
  h_pos := p.h_pos
  τ_pos := p.τ_pos
  τ_le_one := p.τ_le_one
  h_le := p.h_le
  α_nonneg := p.α_nonneg
  wInf_nonneg := le_refl _
  caseD := fun _ => ⟨p.caseD, by
    have := mul_nonneg P.C_pos.le p.α_nonneg
    simpa using this⟩
  caseC := fun h => by cases h
  Wh := WhX
  Ws := ⊤
  Wh_le_Ws := le_top
  dt := dtX
  dx := fun _ => dxX p
  mat := dtX
  Lc := dtX
  Lh := dtX
  up := upX
  dn := dnX
  nfl := nflX p
  bot := botX p
  top := topX p
  dx_mem := fun _ => dx_mem' p
  Lh_mem := dt_mem'
  Q := QX p
  QT := QTX p
  j := jX p
  FQ := FQX p
  FQw := fun _ => SemiIP.zero Fs
  Fgp := FgpX p
  Fint := FintX p
  Om := fun _ => OmX p
  Q_le_QT := fun n _ => Q_le_QT' p n
  FQ_le := fun n _ => FQ_le' p n
  Fint_le_FQ := fun n _ => Fint_le_FQ' p n
  FQw_le := by simp [SemiIP.zero]
  trace_up := fun n _ v _ => trace_up' p n v
  trace_dn := fun n _ v _ => trace_dn' p n v
  trace_nfl := fun n _ v _ => by simpa using trace_nfl' p n v
  trace_time := fun n _ => trace_time' p n
  trace_time_cont := fun n _ => trace_time_cont' p n
  trace_up_cont := fun n _ v => by simpa using trace_up_cont' p n v
  inv_dx := fun n _ v _ => by simpa using inv_dx' p n v
  gp := fun n _ v _ => gp' p n v
  gp_inv_dx := fun n _ v _ => by simpa using gp_inv_dx' p n v
  gp_facet := fun n _ v _ => gp_facet' p n v
  Lc_Lh := fun n _ u _ => by
    have := mul_nonneg (mul_nonneg P.C_pos.le (sq_nonneg p.h)) (QX_dx_nonneg p n u)
    simpa using this
  Lh_inv_grad := fun n _ u hu => by simpa using Lh_inv_grad' p n u hu
  Lh_gp := fun n _ u hu => by simpa using Lh_gp' p n u hu
  Lh_int_jump := fun n _ u hu => by simpa using Lh_int_jump' p n u hu
  Lc_inv := fun n _ => Lc_inv' p n
  mat_dt := by simp
  Lc_dt := by simp
  mat_Lc := fun _ => rfl
  ibp := fun n _ u v => by simpa [SemiIP.zero] using ibp' p n u v

/-! ### The exponential weight -/

/-- The constants of the weight: `c0 = e^{-σT}`, `C_φ = e`, `C_s = 1 + 76 σ²`. -/
noncomputable def cutWConsts : WConsts where
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

theorem wgt_nonneg (i : ℕ) : 0 ≤ p.h * (hi p i - lo p i) / 6 := by
  have := p.h_pos; have := lo_le_hi p i
  have : 0 ≤ hi p i - lo p i := by linarith
  positivity

theorem Q_symm' (n : ℕ) (u v : X) : QX p n (MX p u) v = QX p n u (MX p v) := by
  rw [QX_apply, QX_apply]
  refine sum_congr rfl fun i _ => ?_
  unfold elem
  rw [simpson_apply, simpson_apply]
  rw [T_symm (compat_pt p n i (lo p i)), T_symm (compat_pt p n i ((lo p i + hi p i) / 2)),
    T_symm (compat_pt p n i (hi p i))]

theorem Q_lo' (n : ℕ) (u : X) : phiX p (n + 1) * QX p n u u ≤ QX p n u (MX p u) := by
  rw [QX_apply, QX_apply, mul_sum]
  refine sum_le_sum fun i _ => ?_
  unfold elem
  rw [simpson_apply, simpson_apply]
  exact lift3_ge (wgt_nonneg p i) (T_lo (compat_pt p n i _) u) (T_lo (compat_pt p n i _) u)
    (T_lo (compat_pt p n i _) u)

theorem Q_contr' (n : ℕ) (u : X) : QX p n (MX p u) (MX p u) ≤ QX p n u u := by
  rw [QX_apply, QX_apply]
  refine sum_le_sum fun i _ => ?_
  unfold elem
  rw [simpson_apply, simpson_apply]
  have := lift3 (K := 1) (wgt_nonneg p i)
    (by simpa using T_contr (compat_pt p n i (lo p i)) u)
    (by simpa using T_contr (compat_pt p n i ((lo p i + hi p i) / 2)) u)
    (by simpa using T_contr (compat_pt p n i (hi p i)) u)
  linarith

theorem superapprox' (n : ℕ) (u : X) (hu : u ∈ WhX) :
    QTX p n (PwX p u - MX p u) (PwX p u - MX p u)
      ≤ (1 + 76 * p.σ ^ 2) * p.τ ^ 2 * QTX p n u u := by
  rw [QTX_apply, QTX_apply]
  have h1 : ∑ i ∈ range (p.M + 2), full p n i (PwX p u - MX p u) (PwX p u - MX p u)
      ≤ p.σ ^ 2 * p.τ ^ 2 * ∑ i ∈ range (p.M + 2), full p n i u u :=
    sum_le_mul_sum fun i _ => full_sa p n i hu
  have hS : 0 ≤ ∑ i ∈ range (p.M + 2), full p n i u u :=
    sum_nonneg fun i _ => full_nonneg p n i u
  have := mul_le_mul_of_nonneg_right (Cs_ge p) (mul_nonneg (sq_nonneg p.τ) hS)
  nlinarith

theorem superapprox_dt' (n : ℕ) (u : X) (hu : u ∈ WhX) :
    QTX p n (dtX (PwX p u - MX p u)) (dtX (PwX p u - MX p u))
      ≤ (1 + 76 * p.σ ^ 2) * QTX p n u u := by
  rw [QTX_apply, QTX_apply]
  have h1 : ∑ i ∈ range (p.M + 2), full p n i (dtX (PwX p u - MX p u)) (dtX (PwX p u - MX p u))
      ≤ 76 * p.σ ^ 2 * ∑ i ∈ range (p.M + 2), full p n i u u :=
    sum_le_mul_sum fun i _ => full_sa_dt p n i hu
  have hS : 0 ≤ ∑ i ∈ range (p.M + 2), full p n i u u :=
    sum_nonneg fun i _ => full_nonneg p n i u
  linarith

/-- **The exponential weight `e^{-σt}` with the temporal `L²` projection for the unfitted
heat equation.** -/
noncomputable def cutExpWeight : ExpWeight (cutSetting p) (cutWConsts p) where
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
  mat_M := dt_M' p
  Lc_M := dt_M' p
  Q_symm := fun n _ => Q_symm' p n
  j_symm := fun n _ u v => by
    show jX p n (MX p u) v = jX p n u (MX p v)
    rw [jX_apply, jX_apply, jF_symm, jF_symm]
  FQ_symm := fun n _ a b => by
    show FQX p n (MfX p a) b = FQX p n a (MfX p b)
    rw [FQX_apply, FQX_apply]
    exact sum_congr rfl fun i _ => ip_Mexp_symm _ _ _ _
  FQw_symm := by simp [cutSetting, SemiIP.zero]
  Q_lo := fun n _ => Q_lo' p n
  j_lo := fun n _ u => by
    show phiX p (n + 1) * jX p n u u ≤ jX p n u (MX p u)
    rw [jX_apply, jX_apply]
    have := jF_lo p n 0 u; have := jF_lo p n p.M u
    linarith
  FQ_lo := fun n _ a => by
    show phiX p (n + 1) * FQX p n a a ≤ FQX p n a (MfX p a)
    rw [FQX_apply, FQX_apply, mul_sum]
    exact sum_le_sum fun i _ => ip_Mexp_lo _ p.σ_pos.le (by unfold phiX; rw [tk_succ]) _
  FQw_lo := by simp [cutSetting, SemiIP.zero]
  FQ_hi := fun n _ a => by
    show FQX p n a (MfX p a) ≤ phiX p n * FQX p n a a
    rw [FQX_apply, FQX_apply, mul_sum]
    exact sum_le_sum fun i _ => ip_Mexp_hi _ p.σ_pos.le _
  Q_contr := fun n _ => Q_contr' p n
  j_contr := fun n _ u => by
    show jX p n (MX p u) (MX p u) ≤ jX p n u u
    rw [jX_apply, jX_apply]
    have := jF_contr p n 0 u; have := jF_contr p n p.M u
    linarith
  FQ_contr := fun n _ a => by
    show FQX p n (MfX p a) (MfX p a) ≤ FQX p n a a
    rw [FQX_apply, FQX_apply]
    exact sum_le_sum fun i _ => ip_Mexp_contr _ p.σ_pos.le (tk_nonneg p n) _
  FQw_contr := by simp [cutSetting, SemiIP.zero]
  Pw := PwX p
  Pw_mem := fun u _ => Pw_mem' p u
  r_mem := fun _ _ => Submodule.mem_top
  r_dx := fun _ => r_dx' p
  superapprox := fun n _ => superapprox' p n
  superapprox_dt := fun n _ => superapprox_dt' p n
  superapprox_gp := fun n _ u hu => by
    show FgpX p n _ _ ≤ (1 + 76 * p.σ ^ 2) * p.τ ^ 2 * FgpX p n _ _
    rw [FgpX_apply, FgpX_apply]
    exact jump_sa p n (gpS p) hu
  superapprox_int := fun n _ u hu => by
    show FintX p n _ _ ≤ (1 + 76 * p.σ ^ 2) * p.τ ^ 2 * FintX p n _ _
    rw [FintX_apply, FintX_apply]
    exact jump_sa p n (intS p) hu
  superapprox_j := fun n _ u hu => by
    show jX p n (PwX p u - MX p u) (PwX p u - MX p u)
      ≤ (1 + 76 * p.σ ^ 2) * p.τ ^ 2 * jX p n u u
    rw [jX_apply, jX_apply]
    have h1 := jF_sa p n 0 hu
    have h2 := jF_sa p n p.M hu
    have j1 := (jF p n 0).nonneg u
    have j2 := (jF p n p.M).nonneg u
    have := mul_le_mul_of_nonneg_right (Cs_ge p)
      (mul_nonneg (sq_nonneg p.τ) (add_nonneg j1 j2))
    nlinarith

/-! ### Consequence: inf-sup stability of the unfitted space-time DG method -/

/-- Inf-sup stability (`thm_stability`) for the unfitted heat equation in one space
dimension, uniformly in the cut positions `δ_L, δ_R`, the number of elements and time
steps, `h` and `Δt`. -/
theorem cut_inf_sup (hlam : P.lam0 (cutWConsts p).Cφ ≤ P.lam)
    (hsmall : ExpWeight.Ksup P (cutWConsts p) * ExpWeight.Kw P (cutWConsts p) * √p.τ ≤ 1 / 8)
    {u : X} (hu : u ∈ WhX) :
    ∃ v ∈ WhX, (cutSetting p).tnj2 v ≤ ExpWeight.Msq P (cutWConsts p) * (cutSetting p).tnj2 u
      ∧ 1 / 8 * (cutSetting p).tnj2 u ≤ (cutSetting p).BJ u v :=
  (cutExpWeight p).inf_sup hlam hsmall hu

end StDgdg.Cut1d
