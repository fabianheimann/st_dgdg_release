import Mathlib

/-!
# Layer 1: abstract skeleton

Abstract versions of
* `thm_stability`  (inf-sup stability from the two testing lemmas),
* unique solvability of the discrete problem,
* `prop_strang`    (Strang-type error bound),
of `st_article.tex`. Nothing in this file knows about meshes, cut cells or polynomials:
all analytic input enters as hypotheses, which are discharged in Layer 2.
-/

namespace StDgdg

open Real

section InfSup

variable {W : Type*} [AddCommGroup W] [Module ℝ W]

/-- **Inf-sup stability, abstract form of `thm_stability`.**

* `B`   : the bilinear form `B_h + J`,
* `tn`  : the norm `|||·|||_j`,
* `cj2` : `‖·‖_{c,j}^2`,
* `L2`  : `Δt ‖𝓛 ·‖_Q^2`,
* `Pw`  : `u ↦ Π_t (e^{-σ t} u)`,
* `D`   : `u ↦ Δt 𝓛_h u`,
* `hw`  : `lemma_weighted_symm_testing`,
* `hd`  : `lemma_derivative_testing`,
* `hPw`, `hD` : `lemma_test_fun_bnd`,
* `hsmall` : the smallness condition `K C √Δt ≤ 1/8`, `K = (C₂ + 1/4)/c_σ`.

Conclusion: the supremizer `ṽ(u) = K Π_t(e^{-σ t}u) + Δt 𝓛_h u` satisfies
`|||ṽ|||_j ≤ (K C' + C'') |||u|||_j` and `(B_h+J)(u, ṽ) ≥ 1/8 |||u|||_j^2`. -/
theorem inf_sup
    (B : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (tn : Seminorm ℝ W) (cj2 L2 : W → ℝ)
    (htn : ∀ u, tn u ^ 2 = L2 u + cj2 u)
    (Pw D : W → W)
    {cσ C₁ C₂ C' C'' dt : ℝ} (hcσ : 0 < cσ) (hC₂ : 0 ≤ C₂)
    (hw : ∀ u, cσ * cj2 u - C₁ * √dt * tn u ^ 2 ≤ B u (Pw u))
    (hd : ∀ u, 1 / 4 * L2 u - C₂ * cj2 u ≤ B u (D u))
    (hPw : ∀ u, tn (Pw u) ≤ C' * tn u) (hD : ∀ u, tn (D u) ≤ C'' * tn u)
    (hsmall : (C₂ + 1 / 4) / cσ * C₁ * √dt ≤ 1 / 8) (u : W) :
    ∃ v : W, tn v ≤ ((C₂ + 1 / 4) / cσ * C' + C'') * tn u ∧ 1 / 8 * tn u ^ 2 ≤ B u v := by
  set K : ℝ := (C₂ + 1 / 4) / cσ with hK
  have hK0 : 0 ≤ K := by positivity
  have hKc : K * cσ = C₂ + 1 / 4 := by rw [hK]; field_simp
  refine ⟨K • Pw u + D u, ?_, ?_⟩
  · calc tn (K • Pw u + D u) ≤ tn (K • Pw u) + tn (D u) := map_add_le_add tn _ _
      _ = K * tn (Pw u) + tn (D u) := by
          rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg hK0]
      _ ≤ K * (C' * tn u) + C'' * tn u := by
          gcongr
          · exact hPw u
          · exact hD u
      _ = (K * C' + C'') * tn u := by ring
  · have h1 := mul_le_mul_of_nonneg_left (hw u) hK0
    have h2 := hd u
    have h3 : K * C₁ * √dt * tn u ^ 2 ≤ 1 / 8 * tn u ^ 2 :=
      mul_le_mul_of_nonneg_right hsmall (sq_nonneg _)
    have h4 := htn u
    have hB : B u (K • Pw u + D u) = K * B u (Pw u) + B u (D u) := by
      simp [map_add, map_smul]
    rw [hB]
    have h5 : K * (cσ * cj2 u - C₁ * √dt * tn u ^ 2)
        = (C₂ + 1 / 4) * cj2 u - K * C₁ * √dt * tn u ^ 2 := by
      rw [← hKc]; ring
    rw [h5] at h1
    linarith

/-- The form of `eq_inf_sup` in the paper, `(B_h+J)(u,ṽ) ≥ C_stab |||u|||_j |||ṽ|||_j`
with `C_stab = 1 / (8 M)`, from the two-part statement of `inf_sup`. -/
theorem inf_sup_product_form
    (B : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (tn : Seminorm ℝ W) {M : ℝ} (hM : 0 < M) (u v : W)
    (hv : tn v ≤ M * tn u) (hB : 1 / 8 * tn u ^ 2 ≤ B u v) :
    1 / (8 * M) * (tn u * tn v) ≤ B u v := by
  have hu : 0 ≤ tn u := apply_nonneg tn u
  have : 1 / (8 * M) * (tn u * tn v) ≤ 1 / (8 * M) * (tn u * (M * tn u)) := by gcongr
  have h2 : 1 / (8 * M) * (tn u * (M * tn u)) = 1 / 8 * tn u ^ 2 := by
    field_simp
  linarith

/-- The smallness condition of `thm_stability` in the form stated in the paper:
`Δt ≤ (8 K C)^{-2}` implies `K C √Δt ≤ 1/8`. -/
theorem small_of_dt_le {KC dt : ℝ} (hKC : 0 < KC) (hdt : dt ≤ (8 * KC)⁻¹ ^ 2) :
    KC * √dt ≤ 1 / 8 := by
  have h8 : 0 < 8 * KC := by positivity
  have hs : √dt ≤ (8 * KC)⁻¹ := by
    calc √dt ≤ √((8 * KC)⁻¹ ^ 2) := Real.sqrt_le_sqrt hdt
      _ = (8 * KC)⁻¹ := Real.sqrt_sq (by positivity)
  calc KC * √dt ≤ KC * (8 * KC)⁻¹ := by gcongr
    _ = 1 / 8 := by field_simp

end InfSup

section WellPosed

variable {W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]

/-- **Unique solvability** (last claim of `thm_stability`): on a finite dimensional space,
a bilinear form with trivial left kernel yields a unique solution for every right hand side. -/
theorem existsUnique_of_ker_trivial (B : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (hker : ∀ u, (∀ v, B u v = 0) → u = 0) (f : W →ₗ[ℝ] ℝ) :
    ∃! u, ∀ v, B u v = f v := by
  have hinj : Function.Injective B := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    exact hker u fun v => by rw [hu]; rfl
  have hsurj : Function.Surjective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := ℝ) (V := W)).symm).1 hinj
  obtain ⟨u, hu⟩ := hsurj f
  refine ⟨u, fun v => by rw [hu], fun u' hu' => hinj ?_⟩
  ext v
  rw [hu' v, hu]

/-- Unique solvability from the inf-sup estimate, if `|||·|||_j` is definite on `W_h`. -/
theorem existsUnique_of_inf_sup (B : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (tn : Seminorm ℝ W)
    (hdef : ∀ u, tn u = 0 → u = 0)
    (hinfsup : ∀ u, ∃ v, 1 / 8 * tn u ^ 2 ≤ B u v) (f : W →ₗ[ℝ] ℝ) :
    ∃! u, ∀ v, B u v = f v := by
  refine existsUnique_of_ker_trivial B (fun u hu => hdef u ?_) f
  obtain ⟨v, hv⟩ := hinfsup u
  rw [hu v] at hv
  have : tn u ^ 2 ≤ 0 := by linarith
  exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm this (sq_nonneg _))

end WellPosed

section Strang

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **Strang-type bound, abstract form of `prop_strang`.**

* `V` : the space `W_h + H^2(Q)`, `W` : the discrete space `W_h`,
* `B` : `B_h` on `V × W_h`, `J` : the Ghost penalty on `W_h × W_h`, `f` : `f_h`,
* `tn` : `|||·|||`, `tnstar` : `|||·|||_*`, `tnj` : `|||·|||_j` (on `W_h`), `sJ` : `|·|_J`,
* `hcons` : consistency (`lemma_consistency`), `hdisc` : the discrete problem,
* `hcontB`, `hcontJ` : continuity (`lemma_continuity`),
* `hinfsup` : inf-sup stability in the two-part form of `inf_sup`
  (with `c = 1/8`, `M = K C' + C''`).

Conclusion: `|||u - u_h||| ≤ (1 + M (C_c + 1) / c) (|||u - w_h|||_* + |w_h|_J)`. -/
theorem strang (W : Submodule ℝ V)
    (B : V →ₗ[ℝ] W →ₗ[ℝ] ℝ) (J : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (f : W →ₗ[ℝ] ℝ)
    (tn tnstar : Seminorm ℝ V) (tnj sJ : Seminorm ℝ W)
    {Cc M c : ℝ} (hCc : 0 ≤ Cc) (hM : 0 ≤ M) (hc : 0 < c)
    (htn_star : ∀ x, tn x ≤ tnstar x) (htn_j : ∀ w : W, tn (w : V) ≤ tnj w)
    (hsJ : ∀ w, sJ w ≤ tnj w)
    (hcontB : ∀ x v, |B x v| ≤ Cc * tnstar x * tnj v)
    (hcontJ : ∀ w v, |J w v| ≤ sJ w * sJ v)
    (hinfsup : ∀ e : W, ∃ v : W, tnj v ≤ M * tnj e ∧ c * tnj e ^ 2 ≤ B (e : V) v + J e v)
    (u : V) (uh : W)
    (hcons : ∀ v : W, B u v = f v)
    (hdisc : ∀ v : W, B (uh : V) v + J uh v = f v)
    (wh : W) :
    tn (u - uh) ≤ (1 + M * (Cc + 1) / c) * (tnstar (u - wh) + sJ wh) := by
  set e : W := uh - wh with he
  set R : ℝ := tnstar (u - wh) + sJ wh with hR
  have hR0 : 0 ≤ R := add_nonneg (apply_nonneg _ _) (apply_nonneg _ _)
  have he0 : 0 ≤ tnj e := apply_nonneg _ _
  -- error equation and its consequences
  obtain ⟨v, hv, hBv⟩ := hinfsup e
  have hv0 : 0 ≤ tnj v := apply_nonneg _ _
  have herr : B (e : V) v + J e v = B (u - wh) v - J wh v := by
    have h1 := hcons v
    have h2 := hdisc v
    have h3 : B ((e : W) : V) v = B (uh : V) v - B (wh : V) v := by
      simp [he, map_sub]
    have h4 : J e v = J uh v - J wh v := by simp [he, map_sub]
    have h5 : B (u - (wh : V)) v = B u v - B (wh : V) v := by simp [map_sub]
    rw [h3, h4, h5]; linarith
  have hb1 : B (u - wh) v ≤ Cc * tnstar (u - wh) * tnj v :=
    (le_abs_self _).trans (hcontB _ _)
  have hb2 : -J wh v ≤ sJ wh * tnj v :=
    (neg_le_abs _).trans ((hcontJ _ _).trans
      (mul_le_mul_of_nonneg_left (hsJ v) (apply_nonneg _ _)))
  have hkey : c * tnj e ^ 2 ≤ (Cc + 1) * R * (M * tnj e) := by
    have hA : (Cc * tnstar (u - wh) + sJ wh) * tnj v ≤ (Cc + 1) * R * (M * tnj e) := by
      have hx : 0 ≤ tnstar (u - (wh : V)) := apply_nonneg _ _
      have hy : 0 ≤ sJ wh := apply_nonneg _ _
      have : Cc * tnstar (u - wh) + sJ wh ≤ (Cc + 1) * R := by
        rw [hR]; nlinarith
      exact mul_le_mul this hv hv0 (by positivity)
    nlinarith
  have hE : tnj e ≤ M * (Cc + 1) / c * R := by
    rcases eq_or_lt_of_le he0 with h0 | hpos
    · rw [← h0]; positivity
    · have : c * tnj e ≤ (Cc + 1) * R * M := by
        have h := hkey
        have : tnj e * (c * tnj e) ≤ tnj e * ((Cc + 1) * R * M) := by nlinarith
        exact le_of_mul_le_mul_left this hpos
      rw [div_mul_eq_mul_div, le_div_iff₀ hc]
      linarith
  -- triangle inequality
  have hsplit : u - (uh : V) = (u - (wh : V)) - ((e : W) : V) := by
    simp [he]
  calc tn (u - uh) = tn ((u - (wh : V)) - ((e : W) : V)) := by rw [hsplit]
    _ ≤ tn (u - wh) + tn ((e : W) : V) := map_sub_le_add tn _ _
    _ ≤ tnstar (u - wh) + tnj e := add_le_add (htn_star _) (htn_j _)
    _ ≤ R + M * (Cc + 1) / c * R := by
        have : tnstar (u - (wh : V)) ≤ R := by
          rw [hR]; linarith [apply_nonneg sJ wh]
        linarith
    _ = (1 + M * (Cc + 1) / c) * R := by ring

end Strang

end StDgdg
