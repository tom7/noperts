module

public import Mathlib
public import MinimalityExtra
public import Minimality.BoxLemma

/-!
# The box rule in shadow form

Lemma R (`Minimality.isRupert_of_box_frame`) takes the four rectangle corners as positive
combinations of the outer projected vertices. Here the hypothesis is that the corners lie in the
interior of the outer shadow, which is the form used by the closed-form thin-shape rules.
-/

@[expose] public section

open scoped RealInnerProductSpace


namespace MinimalityExtra
open Minimality


theorem posComb_of_mem_interior (V : Finset ℝ³) (Φ : ℝ³ →ₗ[ℝ] ℝ²) (q : ℝ²)
    (hq : q ∈ interior (Φ '' convexHull ℝ (V : Set ℝ³))) :
    ∃ μ : ℝ³ → ℝ, (∀ w ∈ V, 0 < μ w) ∧ ∑ w ∈ V, μ w = 1 ∧ q = ∑ w ∈ V, μ w • Φ w := by
  classical
  have hne : V.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    subst h
    simp at hq
  set n : ℝ := (V.card : ℝ) with hn
  have hnpos : 0 < n := by rw [hn]; exact_mod_cast hne.card_pos
  set b : ℝ² := ∑ w ∈ V, (1 / n) • Φ w with hb
  have hev : ∀ᶠ t : ℝ in nhds 0, q + t • (q - b) ∈ Φ '' convexHull ℝ (V : Set ℝ³) := by
    have hc : Filter.Tendsto (fun t : ℝ => q + t • (q - b)) (nhds 0) (nhds q) := by
      have : Continuous (fun t : ℝ => q + t • (q - b)) := by fun_prop
      simpa using this.tendsto 0
    exact hc (mem_interior_iff_mem_nhds.mp hq)
  obtain ⟨ε, hε, hεpos⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Set.Ioi (0:ℝ) ∈ nhdsWithin 0 (Set.Ioi 0))).exists
  have hεpos : 0 < ε := hεpos
  obtain ⟨p, hp, hpq⟩ := hε
  obtain ⟨ν, hν0, hν1, hνp⟩ := Finset.mem_convexHull.mp hp
  rw [Finset.centerMass_eq_of_sum_1 _ _ hν1] at hνp
  refine ⟨fun w => ν w / (1 + ε) + ε / ((1 + ε) * n), ?_, ?_, ?_⟩
  · intro w hw
    have := hν0 w hw
    have h1 : 0 < ε / ((1 + ε) * n) := by positivity
    have h2 : 0 ≤ ν w / (1 + ε) := div_nonneg this (by linarith)
    linarith
  · simp only [Finset.sum_add_distrib, ← Finset.sum_div, hν1, Finset.sum_const, nsmul_eq_mul]
    rw [← hn]
    field_simp
  · have hΦp : Φ p = ∑ w ∈ V, ν w • Φ w := by
      rw [← hνp, map_sum]; simp [map_smul]
    have hqe : q = (1 / (1 + ε)) • (q + ε • (q - b)) + (ε / (1 + ε)) • b := by
      have : (1 + ε) ≠ 0 := by linarith
      ext i
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      field_simp
      ring
    have hbe : (ε / (1 + ε)) • b = ∑ w ∈ V, (ε / ((1 + ε) * n)) • Φ w := by
      rw [hb, Finset.smul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [smul_smul]; congr 1; field_simp
    rw [hqe, ← hpq, hΦp, hbe, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [smul_smul, ← add_smul]
    congr 1; field_simp


/-- **Box rule (Lemma R, shadow form).** -/
theorem isRupert_of_box_rule (V : Finset ℝ³)
    (hsol : (interior (convexHull ℝ (V : Set ℝ³))).Nonempty)
    (e n : ℝ³) (hee : ⟪e, e⟫ = 1) (hnn : ⟪n, n⟫ = 1) (hen : ⟪e, n⟫ = 0)
    {R₂ : Matrix (Fin 3) (Fin 3) ℝ} (hR₂ : R₂ ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (a b μ w c₀ c₁ L H : ℝ) (hL : 0 < L) (hH : 0 < H) (hμL : μ ≤ L) (hwH : w ≤ H)
    (hbox : ∀ v ∈ V, a ≤ ⟪e, v⟫ ∧ ⟪e, v⟫ ≤ a + μ ∧ b ≤ ⟪n, v⟫ ∧ ⟪n, v⟫ ≤ b + w)
    (hcorner : ∀ s t : ℝ, (s = 0 ∨ s = 1) → (t = 0 ∨ t = 1) →
      !₂[c₀ + s * L, c₁ + t * H] ∈
        interior {q : ℝ² | ∃ p ∈ convexHull ℝ (V : Set ℝ³), proj_xy (R₂.toEuclideanLin p) = q}) :
    IsRupert V := by
  refine isRupert_of_box_frame V hsol e n hee hnn hen hR₂ a b μ w c₀ c₁ L H hL hH hμL hwH hbox ?_
  intro s t hs ht
  have h := hcorner s t hs ht
  have e1 : {q : ℝ² | ∃ p ∈ convexHull ℝ (V : Set ℝ³), proj_xy (R₂.toEuclideanLin p) = q} =
      (projL ∘ₗ R₂.toEuclideanLin) '' convexHull ℝ (V : Set ℝ³) := by
    ext q; simp only [Set.mem_setOf_eq, Set.mem_image, LinearMap.comp_apply]; rfl
  rw [e1] at h
  obtain ⟨μ', h1, h2, h3⟩ := posComb_of_mem_interior V (projL ∘ₗ R₂.toEuclideanLin) _ h
  exact ⟨μ', h1, h2, h3⟩

theorem boxRule : BoxRule := by
  intro V hsol e n hee hnn hen R₂ hR₂ a b μ w c₀ c₁ L H hL hH hμL hwH hbox hc
  exact isRupert_of_box_rule V hsol e n hee hnn hen hR₂ a b μ w c₀ c₁ L H hL hH hμL hwH hbox hc

end MinimalityExtra
