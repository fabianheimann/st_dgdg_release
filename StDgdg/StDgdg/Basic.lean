import Mathlib

/-!
# Symmetric positive semidefinite bilinear forms

All `L²`-type inner products of the paper (over `Q^n`, over the active prisms, over facets,
over time levels, the Ghost penalty form `j_h^n`) are modelled as symmetric positive
semidefinite bilinear forms on abstract real vector spaces. Cauchy–Schwarz / Young
inequalities then need no assumption.
-/

namespace StDgdg

/-- A symmetric positive semidefinite bilinear form. -/
structure SemiIP (Y : Type*) [AddCommGroup Y] [Module ℝ Y] where
  B : Y →ₗ[ℝ] Y →ₗ[ℝ] ℝ
  symm : ∀ a b, B a b = B b a
  nonneg : ∀ a, 0 ≤ B a a

namespace SemiIP

variable {Y : Type*} [AddCommGroup Y] [Module ℝ Y] (b : SemiIP Y)

instance : CoeFun (SemiIP Y) (fun _ => Y → Y →ₗ[ℝ] ℝ) := ⟨fun b => b.B⟩

/-- Young's inequality `2 |b(x,y)| ≤ s b(x,x) + s⁻¹ b(y,y)`. -/
theorem young {s : ℝ} (hs : 0 < s) (x y : Y) :
    |2 * b x y| ≤ s * b x x + s⁻¹ * b y y := by
  have h1 := b.nonneg (s • x - y)
  have h2 := b.nonneg (s • x + y)
  simp only [map_sub, map_add, map_smul, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul] at h1 h2
  rw [b.symm y x] at h1 h2
  have h1' : 0 ≤ s * (s * b x x - 2 * b x y) + b y y := by linarith
  have h2' : 0 ≤ s * (s * b x x + 2 * b x y) + b y y := by linarith
  have e1 : s⁻¹ * (s * (s * b x x - 2 * b x y) + b y y)
      = s * b x x - 2 * b x y + s⁻¹ * b y y := by field_simp
  have e2 : s⁻¹ * (s * (s * b x x + 2 * b x y) + b y y)
      = s * b x x + 2 * b x y + s⁻¹ * b y y := by field_simp
  have g1 := mul_nonneg (inv_nonneg.2 hs.le) h1'
  have g2 := mul_nonneg (inv_nonneg.2 hs.le) h2'
  rw [e1] at g1
  rw [e2] at g2
  rw [abs_le]
  constructor <;> linarith

theorem young_le {s : ℝ} (hs : 0 < s) (x y : Y) :
    2 * b x y ≤ s * b x x + s⁻¹ * b y y :=
  (le_abs_self _).trans (b.young hs x y)

theorem young_ge {s : ℝ} (hs : 0 < s) (x y : Y) :
    -(s * b x x + s⁻¹ * b y y) ≤ 2 * b x y :=
  (abs_le.1 (b.young hs x y)).1

theorem add_sq_le (x y : Y) : b (x + y) (x + y) ≤ 2 * b x x + 2 * b y y := by
  have h := b.nonneg (x - y)
  simp only [map_sub, map_add, LinearMap.sub_apply, LinearMap.add_apply] at h ⊢
  rw [b.symm y x] at h ⊢
  linarith

theorem sub_sq_le (x y : Y) : b (x - y) (x - y) ≤ 2 * b x x + 2 * b y y := by
  have h := b.nonneg (x + y)
  simp only [map_sub, map_add, LinearMap.sub_apply, LinearMap.add_apply] at h ⊢
  rw [b.symm y x] at h ⊢
  linarith

theorem add_sq_le_map {Z : Type*} [AddCommGroup Z] [Module ℝ Z] (f : Z →ₗ[ℝ] Y) (x y : Z) :
    b (f (x + y)) (f (x + y)) ≤ 2 * b (f x) (f x) + 2 * b (f y) (f y) := by
  have := b.add_sq_le (f x) (f y)
  rwa [← map_add] at this

theorem smul_sq (c : ℝ) (x : Y) : b (c • x) (c • x) = c ^ 2 * b x x := by
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- Lower bound for `b(a + m, a - d)` (used for the term `(C)` in `lemma_derivative_testing`). -/
theorem cross_lower (a m d : Y) :
    3 / 4 * b a a - 5 / 2 * b m m - 5 / 2 * b d d ≤ b (a + m) (a - d) := by
  have y1 := b.young_le (by norm_num : (0 : ℝ) < 1 / 4) a d
  have y2 := b.young_ge (by norm_num : (0 : ℝ) < 4) m a
  have y3 := b.young_le one_pos m d
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
  norm_num at y1 y2 y3
  linarith

/-- Young's inequality for sums of inner products. -/
theorem sum_young {κ : Type*} (t : Finset κ) (b : κ → SemiIP Y) (x y : κ → Y) {s : ℝ}
    (hs : 0 < s) :
    -(s * ∑ k ∈ t, b k (x k) (x k) + s⁻¹ * ∑ k ∈ t, b k (y k) (y k))
      ≤ 2 * ∑ k ∈ t, b k (x k) (y k) := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_le_sum fun k _ => (b k).young_ge hs _ _

/-- Young's inequality for sums of inner products, upper bound. -/
theorem sum_young_le {κ : Type*} (t : Finset κ) (b : κ → SemiIP Y) (x y : κ → Y) {s : ℝ}
    (hs : 0 < s) :
    2 * ∑ k ∈ t, b k (x k) (y k)
      ≤ s * ∑ k ∈ t, b k (x k) (x k) + s⁻¹ * ∑ k ∈ t, b k (y k) (y k) := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun k _ => (b k).young_le hs _ _

/-- The zero form. -/
def zero (Y : Type*) [AddCommGroup Y] [Module ℝ Y] : SemiIP Y where
  B := 0
  symm := by simp
  nonneg := by simp

/-- Pull-back of a form along a linear map. -/
def comap {Z : Type*} [AddCommGroup Z] [Module ℝ Z] (f : Z →ₗ[ℝ] Y) : SemiIP Z where
  B := b.B.compl₁₂ f f
  symm _ _ := b.symm _ _
  nonneg _ := b.nonneg _

@[simp] theorem comap_apply {Z : Type*} [AddCommGroup Z] [Module ℝ Z] (f : Z →ₗ[ℝ] Y) (x y : Z) :
    b.comap f x y = b (f x) (f y) := rfl

/-- A finite sum of forms. -/
def sum {κ : Type*} (s : Finset κ) (b : κ → SemiIP Y) : SemiIP Y where
  B := ∑ k ∈ s, (b k).B
  symm x y := by
    simp only [LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun k _ => (b k).symm x y
  nonneg x := by
    simp only [LinearMap.sum_apply]
    exact Finset.sum_nonneg fun k _ => (b k).nonneg x

theorem sum_apply {κ : Type*} (s : Finset κ) (b : κ → SemiIP Y) (x y : Y) :
    sum s b x y = ∑ k ∈ s, b k x y := by
  simp [sum, LinearMap.sum_apply]

theorem neg_sq (x : Y) : b (-x) (-x) = b x x := by simp

/-- Pythagoras. -/
theorem pythag {k r : Y} (h : b r k = 0) : b (k + r) (k + r) = b k k + b r r := by
  simp only [map_add, LinearMap.add_apply]
  rw [b.symm k r, h]; ring

/-! ### Orthogonal projection onto the span of two orthogonal vectors -/

section proj2
variable (e0 e1 : Y)

/-- `Π f = (f,e₀)/(e₀,e₀) e₀ + (f,e₁)/(e₁,e₁) e₁`. -/
noncomputable def proj2 : Y →ₗ[ℝ] Y :=
  ((b e0 e0)⁻¹ • b.B.flip e0).smulRight e0 + ((b e1 e1)⁻¹ • b.B.flip e1).smulRight e1

theorem proj2_apply (f : Y) :
    b.proj2 e0 e1 f = ((b e0 e0)⁻¹ * b f e0) • e0 + ((b e1 e1)⁻¹ * b f e1) • e1 := rfl

variable {e0 e1} (h01 : b e0 e1 = 0) (h0 : 0 < b e0 e0) (h1 : 0 < b e1 e1)

include h01 h0 in
theorem proj2_orth0 (f : Y) : b (b.proj2 e0 e1 f - f) e0 = 0 := by
  simp only [proj2_apply, map_sub, map_add, map_smul, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul]
  rw [b.symm e1 e0, h01]
  field_simp
  ring

include h01 h1 in
theorem proj2_orth1 (f : Y) : b (b.proj2 e0 e1 f - f) e1 = 0 := by
  simp only [proj2_apply, map_sub, map_add, map_smul, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul]
  rw [h01]
  field_simp
  ring

include h01 h0 h1 in
theorem proj2_orth (f : Y) (x y : ℝ) : b (b.proj2 e0 e1 f - f) (x • e0 + y • e1) = 0 := by
  simp only [map_add, map_smul, smul_eq_mul, b.proj2_orth0 h01 h0, b.proj2_orth1 h01 h1]
  ring

include h01 h0 h1 in
/-- Best approximation. -/
theorem proj2_best (f : Y) (x y : ℝ) :
    b (b.proj2 e0 e1 f - f) (b.proj2 e0 e1 f - f)
      ≤ b (x • e0 + y • e1 - f) (x • e0 + y • e1 - f) := by
  have e : x • e0 + y • e1 - f
      = ((x - (b e0 e0)⁻¹ * b f e0) • e0 + (y - (b e1 e1)⁻¹ * b f e1) • e1)
        + (b.proj2 e0 e1 f - f) := by
    rw [proj2_apply]; module
  rw [e, b.pythag (b.proj2_orth h01 h0 h1 f _ _)]
  linarith [b.nonneg ((x - (b e0 e0)⁻¹ * b f e0) • e0 + (y - (b e1 e1)⁻¹ * b f e1) • e1)]

include h01 h0 h1 in
/-- Stability. -/
theorem proj2_stab (f : Y) : b (b.proj2 e0 e1 f) (b.proj2 e0 e1 f) ≤ b f f := by
  have e : f = (((b e0 e0)⁻¹ * b f e0) • e0 + ((b e1 e1)⁻¹ * b f e1) • e1)
      + -(b.proj2 e0 e1 f - f) := by
    rw [proj2_apply]; module
  have h : b (-(b.proj2 e0 e1 f - f))
      (((b e0 e0)⁻¹ * b f e0) • e0 + ((b e1 e1)⁻¹ * b f e1) • e1) = 0 := by
    rw [map_neg, LinearMap.neg_apply, b.proj2_orth h01 h0 h1, neg_zero]
  have p := b.pythag h
  rw [← e] at p
  rw [p]
  exact le_add_of_nonneg_right (b.nonneg _)

include h01 h0 h1 in
/-- `Π` is the identity on the span. -/
theorem proj2_fix (x y : ℝ) : b.proj2 e0 e1 (x • e0 + y • e1) = x • e0 + y • e1 := by
  rw [proj2_apply]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [b.symm e1 e0, h01]
  have e0' : (b e0 e0)⁻¹ * (x * b e0 e0 + y * 0) = x := by field_simp; ring
  have e1' : (b e1 e1)⁻¹ * (x * 0 + y * b e1 e1) = y := by field_simp; ring
  rw [e0', e1']

end proj2

end SemiIP

/-- Discharges the side conditions `n < N` / `n ≤ N` of slab-wise facts. -/
macro "in_range" : tactic =>
  `(tactic| first | assumption | (simp only [Finset.mem_range] at *; omega) | omega)

/-- Summation of a slab-wise estimate. -/
theorem sum_le_mul_sum {s : Finset ℕ} {a b : ℕ → ℝ} {K : ℝ} (h : ∀ n ∈ s, a n ≤ K * b n) :
    ∑ n ∈ s, a n ≤ K * ∑ n ∈ s, b n := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun n hn => h n hn

end StDgdg
