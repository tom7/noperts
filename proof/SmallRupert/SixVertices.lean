module

public import SmallRupert.BicappedTetrahedron
public import SmallRupert.Crossing

@[expose] public section

/-!
# L6 (partial): six-vertex types covered by the coplanar-silhouette theorem

* T2, pentagonal pyramids: `isRupert_of_pyramid`.
* T7, bicapped tetrahedra: `isRupert_bicappedTetrahedron`.
* T1, triangular prisms whose lateral lines meet (`isRupert_frustum`), and
  prisms with parallel lateral edges not all of the same length
  (`isRupert_parallelPrism`).  Translation prisms `T + [0, w]` are open.
* T5 (capped square pyramid) in normal form, unless `S₁S₄ ∥ S₂S₃`
  (`isRupert_cappedSquarePyramid_normalForm`).
* T3, T4, T6: not covered in general (LEMMAS.md L6); nothing stated.
-/

namespace SmallRupert

open scoped RealInnerProductSpace

/-- **T1, concurrent lateral lines (frustum).**  A triangular prism whose
three lateral lines meet at a point `O` (LEMMAS.md L6, first T1 case): the
small end is `A' = O + α (A - O)` etc. with `α, β, γ ∈ (0, 1)`, and `OABC` is
a nondegenerate tetrahedron.  View from `O` through the centroid of the big
end `ABC`. -/
theorem isRupert_frustum (A B C O : ℝ³) (hind : AffineIndependent ℝ ![A, B, C, O]) (α β γ : ℝ)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    IsRupert {A, B, C, O + α • (A - O), O + β • (B - O), O + γ • (C - O)} := by
  classical
  obtain ⟨hα0, hα1⟩ := hα
  obtain ⟨hβ0, hβ1⟩ := hβ
  obtain ⟨hγ0, hγ1⟩ := hγ
  have hdet : det4 A B C O ≠ 0 := fun h0 =>
    not_coplanar_of_affineIndependent hind (coplanar_of_det4_eq_zero h0)
  set N := cross (B - A) (C - A) with hNdef
  set c := ⟪N, A⟫ with hc
  have hN : N ≠ 0 := fun h0 => hdet (by simp [det4, ← hNdef, h0])
  have hind3 : AffineIndependent ℝ ![A, B, C] := affineIndependent_of_cross_ne_zero hN
  have hinj := hind3.injective
  have hAB : A ≠ B := fun h => by have := @hinj 0 1 (by simp [h]); exact absurd this (by decide)
  have hAC : A ≠ C := fun h => by have := @hinj 0 2 (by simp [h]); exact absurd this (by decide)
  have hBC : B ≠ C := fun h => by have := @hinj 1 2 (by simp [h]); exact absurd this (by decide)
  have hNB : ⟪N, B⟫ = c := by
    have := inner_cross_left (B - A) (C - A); rw [← hNdef, inner_sub_right] at this; linarith
  have hNC : ⟪N, C⟫ = c := by
    have := inner_cross_right (B - A) (C - A); rw [← hNdef, inner_sub_right] at this; linarith
  have hWN : ∀ w ∈ ({A, B, C} : Finset ℝ³), ⟪N, w⟫ = c := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · rfl
    · exact hNB
    · exact hNC
  set G := (1 / 3 : ℝ) • A + (1 / 3 : ℝ) • B + (1 / 3 : ℝ) • C
  have hNG : ⟪N, G⟫ = c := by
    simp only [G, inner_add_right, real_inner_smul_right, hNB, hNC, ← hc]; ring
  have hu₀ : ⟪N, G - O⟫ ≠ 0 := by
    rw [inner_sub_right, hNG]
    intro h0; apply hdet
    simp only [det4, ← hNdef, inner_sub_right]; linarith
  refine isRupert_of_crossing _ {A, B, C} (by intro x hx; simp at hx ⊢; tauto) N c hWN
    (by simp) (by simp) (by simp) hind3 (G - O) hu₀ ?_
  intro v hv hvW
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv hvW
  push Not at hvW
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hvW.1
  · exact absurd rfl hvW.2.1
  · exact absurd rfl hvW.2.2
  · exact exists_weights3 hAB hAC hBC (t := 1 - α) (α := α + (1 - α) / 3)
      (β := (1 - α) / 3) (γ := (1 - α) / 3) (by linarith) (by linarith) (by linarith)
      (by ring) (by simp only [G]; module)
  · exact exists_weights3 hAB hAC hBC (t := 1 - β) (α := (1 - β) / 3)
      (β := β + (1 - β) / 3) (γ := (1 - β) / 3) (by linarith) (by linarith) (by linarith)
      (by ring) (by simp only [G]; module)
  · exact exists_weights3 hAB hAC hBC (t := 1 - γ) (α := (1 - γ) / 3)
      (β := (1 - γ) / 3) (γ := γ + (1 - γ) / 3) (by linarith) (by linarith) (by linarith)
      (by ring) (by simp only [G]; module)

/-- Weights on a four-point `Finset`. -/
theorem exists_weights4 {A B P Q v u : ℝ³} (hAB : A ≠ B) (hAP : A ≠ P) (hAQ : A ≠ Q)
    (hBP : B ≠ P) (hBQ : B ≠ Q) (hPQ : P ≠ Q)
    {t α β γ δ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hδ : 0 < δ)
    (h1 : α + β + γ + δ = 1) (h : v + t • u = α • A + β • B + γ • P + δ • Q) :
    ∃ t' : ℝ, ∃ μ : ℝ³ → ℝ, (∀ w ∈ ({A, B, P, Q} : Finset ℝ³), 0 < μ w) ∧
      ∑ w ∈ ({A, B, P, Q} : Finset ℝ³), μ w = 1 ∧
      v + t' • u = ∑ w ∈ ({A, B, P, Q} : Finset ℝ³), μ w • w := by
  classical
  refine ⟨t, fun w => if w = A then α else if w = B then β else if w = P then γ else δ,
    ?_, ?_, ?_⟩
  · intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl <;>
      simp [hAB.symm, hAP.symm, hAQ.symm, hBP.symm, hBQ.symm, hPQ.symm, *]
  · rw [Finset.sum_insert (by simp [hAB, hAP, hAQ]), Finset.sum_insert (by simp [hBP, hBQ]),
      Finset.sum_insert (by simp [hPQ]), Finset.sum_singleton]
    simp [hAB.symm, hAP.symm, hAQ.symm, hBP.symm, hBQ.symm, hPQ.symm, ← h1, add_assoc]
  · rw [Finset.sum_insert (by simp [hAB, hAP, hAQ]), Finset.sum_insert (by simp [hBP, hBQ]),
      Finset.sum_insert (by simp [hPQ]), Finset.sum_singleton, h]
    simp [hAB.symm, hAP.symm, hAQ.symm, hBP.symm, hBQ.symm, hPQ.symm, add_assoc]

theorem cross_smul_left_self (k : ℝ) (w : ℝ³) : cross (k • w) w = 0 := by
  ext i; fin_cases i <;> simp [cross] <;> ring

theorem cross_smul_right' (a : ℝ³) (k : ℝ) (w : ℝ³) : cross a (k • w) = k • cross a w := by
  ext i; fin_cases i <;> simp [cross] <;> ring

/-- **Parallel prism, one quad face.**  The quad `A B B' A'` is admissible when
the opposite lateral edge `CC'` is shorter than `BB'`. -/
theorem isRupert_prism_core (A B C w : ℝ³) (hdet : ⟪cross (B - A) w, C - A⟫ ≠ 0)
    (sA sB sC : ℝ) (hA : 0 < sA) (hB : 0 < sB) (hC : 0 < sC) (hlt : sC < sB) :
    IsRupert {A, B, C, A + sA • w, B + sB • w, C + sC • w} := by
  classical
  set N := cross (B - A) w with hNdef
  set c := ⟪N, A⟫ with hc
  have hN : N ≠ 0 := fun h0 => hdet (by rw [h0, inner_zero_left])
  have hNw : ⟪N, w⟫ = 0 := inner_cross_right _ _
  have hNB : ⟪N, B⟫ = c := by
    have := inner_cross_left (B - A) w; rw [← hNdef, inner_sub_right] at this; linarith
  have hw0 : w ≠ 0 := fun h0 => hN (by rw [hNdef, h0]; ext i; fin_cases i <;> simp [cross])
  have hBA : ∀ k : ℝ, B - A ≠ k • w := fun k h => hN (by rw [hNdef, h, cross_smul_left_self])
  -- the four quad vertices are distinct
  have hAB : A ≠ B := fun h => hBA 0 (by rw [h, sub_self, zero_smul])
  have hAA' : A ≠ A + sA • w := fun h => hw0 (by
    have : sA • w = 0 := by
      have := congrArg (fun x => x - A) h; simpa using this.symm
    exact (smul_eq_zero.mp this).resolve_left hA.ne')
  have hAB' : A ≠ B + sB • w := fun h => hBA (-sB) (by rw [h]; module)
  have hBA' : B ≠ A + sA • w := fun h => hBA sA (by rw [h]; module)
  have hBB' : B ≠ B + sB • w := fun h => hw0 (by
    have : sB • w = 0 := by
      have := congrArg (fun x => x - B) h; simpa using this.symm
    exact (smul_eq_zero.mp this).resolve_left hB.ne')
  have hA'B' : A + sA • w ≠ B + sB • w := fun h => hBA (sA - sB) (by
    have : B = A + sA • w - sB • w := by rw [h]; module
    rw [this]; module)
  have hWN : ∀ x ∈ ({A, B, A + sA • w, B + sB • w} : Finset ℝ³), ⟪N, x⟫ = c := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · rfl
    · exact hNB
    · rw [inner_add_right, real_inner_smul_right, hNw, mul_zero, add_zero]
    · rw [inner_add_right, real_inner_smul_right, hNw, mul_zero, add_zero, hNB]
  have hind3 : AffineIndependent ℝ ![A, B, A + sA • w] := by
    apply affineIndependent_of_cross_ne_zero
    rw [add_sub_cancel_left, cross_smul_right', ← hNdef]
    exact smul_ne_zero hA.ne' hN
  -- weights
  set r := sC / sB with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := by rw [hr, div_lt_one hB]; exact hlt
  have hrs : r * sB = sC := by rw [hr]; field_simp
  set δ := (1 - r) / 2
  set q := (1 + r) / 2
  set m := (q - r) / 2
  have hδ : 0 < δ := by simp only [δ]; linarith
  have hm : 0 < m := by simp only [m, q]; linarith
  have hqm : 0 < q - m := by simp only [m, q]; linarith
  have hqmr : 0 < q - m - r := by simp only [m, q]; linarith
  have hsum : δ / 2 + (q - m) + δ / 2 + m = 1 := by simp only [δ, q]; ring
  set X := (δ / 2) • A + (q - m) • B + (δ / 2) • (A + sA • w) + m • (B + sB • w)
  have hNX : ⟪N, X⟫ = c := by
    simp only [X, inner_add_right, real_inner_smul_right, hNw, hNB, ← hc]
    linear_combination c * hsum
  have hu₀ : ⟪N, X - C⟫ ≠ 0 := by
    rw [inner_sub_right, hNX]
    intro h0; apply hdet
    rw [inner_sub_right]; linarith
  refine isRupert_of_crossing _ {A, B, A + sA • w, B + sB • w}
    (by intro x hx; simp at hx ⊢; tauto) N c hWN (by simp) (by simp) (by simp) hind3
    (X - C) hu₀ ?_
  intro v hv hvW
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv hvW
  push Not at hvW
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hvW.1
  · exact absurd rfl hvW.2.1
  · exact exists_weights4 hAB hAA' hAB' hBA' hBB' hA'B' (t := 1) (by positivity) hqm
      (by positivity) hm hsum (by simp only [X]; module)
  · exact absurd rfl hvW.2.2.1
  · exact absurd rfl hvW.2.2.2
  · refine exists_weights4 hAB hAA' hAB' hBA' hBB' hA'B' (t := 1) (α := δ / 2)
      (β := q - m - r) (γ := δ / 2) (δ := m + r) (by positivity) hqmr (by positivity)
      (by positivity) (by linear_combination hsum) ?_
    rw [← hrs]; simp only [X]; module

/-- **T1, parallel lateral edges of unequal lengths.**  A triangular prism
with parallel lateral edges `A' = A + s_A w` etc. (`s_A, s_B, s_C > 0`, `w`
not parallel to the plane `ABC`), not a translation prism (the lengths are not
all equal): view through a lateral quadrilateral whose opposite lateral edge is
shorter than the longer of its two. -/
theorem isRupert_parallelPrism (A B C w : ℝ³) (hind : AffineIndependent ℝ ![A, B, C, A + w])
    (sA sB sC : ℝ) (hA : 0 < sA) (hB : 0 < sB) (hC : 0 < sC) (hne : ¬ (sA = sB ∧ sB = sC)) :
    IsRupert {A, B, C, A + sA • w, B + sB • w, C + sC • w} := by
  have hD0 : det4 A B C (A + w) ≠ 0 := fun h0 =>
    not_coplanar_of_affineIndependent hind (coplanar_of_det4_eq_zero h0)
  have hperm : ∀ P Q R : ℝ³, (P = A ∧ Q = B ∧ R = C) ∨ (P = B ∧ Q = A ∧ R = C) ∨
      (P = B ∧ Q = C ∧ R = A) ∨ (P = A ∧ Q = C ∧ R = B) →
      ⟪cross (Q - P) w, R - P⟫ ≠ 0 := by
    intro P Q R h h0
    apply hD0
    simp only [det4, cross, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply,
      conj_trivial] at h0 ⊢
    simp at h0 ⊢
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      first | linear_combination h0 | linear_combination -h0
  have hset : ∀ {X : Finset ℝ³}, X = {A, B, C, A + sA • w, B + sB • w, C + sC • w} →
      IsRupert X → IsRupert {A, B, C, A + sA • w, B + sB • w, C + sC • w} := by
    intro X hX h; rwa [← hX]
  by_cases h1 : sC < sB
  · exact isRupert_prism_core A B C w (hperm A B C (Or.inl ⟨rfl, rfl, rfl⟩)) sA sB sC hA hB hC h1
  by_cases h2 : sC < sA
  · refine hset ?_ (isRupert_prism_core B A C w
      (hperm B A C (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))) sB sA sC hB hA hC h2)
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  push Not at h1 h2
  by_cases h3 : sA < sC
  · refine hset ?_ (isRupert_prism_core B C A w
      (hperm B C A (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))) sB sC sA hB hC hA h3)
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  · have h4 : sB < sC := by
      rcases lt_or_eq_of_le h1 with h | h
      · exact h
      · exact absurd ⟨by linarith, h⟩ hne
    refine hset ?_ (isRupert_prism_core A C B w
      (hperm A C B (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)))) sA sC sB hA hC hB h4)
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto

theorem cross_self (a : ℝ³) : cross a a = 0 := by
  ext i; fin_cases i <;> simp [cross] <;> ring

/-- **T5, the lateral face `E S₃ S₄`** (case `b₂ < γ₂`): project along
`X - S₂` with `X` close to `S₃` on the face (LEMMAS.md L6). -/
theorem isRupert_cappedSquarePyramid_lateral (A B C T : ℝ³)
    (hind : AffineIndependent ℝ ![A, B, C, T])
    (a₁ β₁ c₁ t₁ b₂ γ₂ t₂ : ℝ) (ha₁ : 0 < a₁) (hβ₁ : 0 < β₁) (hc₁ : 0 < c₁) (ht₁ : 0 < t₁)
    (hb₂ : 0 < b₂) (hγ₂ : 0 < γ₂) (ht₂ : 0 < t₂)
    (hsum₁ : a₁ - β₁ + c₁ + t₁ = 1) (hsum₂ : b₂ - γ₂ + t₂ = 1)
    (hconv : β₁ * γ₂ < c₁ * b₂) (hlt : b₂ < γ₂) :
    IsRupert {A, B, C, T, a₁ • A - β₁ • B + c₁ • C + t₁ • T, b₂ • B - γ₂ • C + t₂ • T} := by
  classical
  set S := b₂ • B - γ₂ • C + t₂ • T with hS
  set K := a₁ • A - β₁ • B + c₁ • C + t₁ • T with hK
  have hnc := not_coplanar_of_affineIndependent hind
  have hdet0 : det4 A B T C ≠ 0 := fun h0 => hnc ((coplanar_of_det4_eq_zero h0).subset
    (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto))
  set N := cross (B - A) (S - A) with hNdef
  set c := ⟪N, A⟫ with hc
  have hNC : ⟪N, C - A⟫ = t₂ * det4 A B T C := by
    have ht : t₂ = 1 - b₂ + γ₂ := by linarith
    simp only [hNdef, hS, det4, cross, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply,
      conj_trivial, ht]
    simp
    ring
  have hNC0 : ⟪N, C - A⟫ ≠ 0 := by rw [hNC]; exact mul_ne_zero ht₂.ne' hdet0
  have hN : N ≠ 0 := fun h0 => hNC0 (by rw [h0, inner_zero_left])
  have hindW : AffineIndependent ℝ ![A, B, S] := affineIndependent_of_cross_ne_zero hN
  have hAB : A ≠ B := fun h => hN (by rw [hNdef, h, sub_self]; ext i; fin_cases i <;> simp [cross])
  have hAS : A ≠ S := fun h => hN (by rw [hNdef, ← h, sub_self]; ext i; fin_cases i <;> simp [cross])
  have hBS : B ≠ S := fun h => hN (by rw [hNdef, ← h, cross_self])
  have hNB : ⟪N, B⟫ = c := by
    have := inner_cross_left (B - A) (S - A); rw [← hNdef, inner_sub_right] at this; linarith
  have hNS : ⟪N, S⟫ = c := by
    have := inner_cross_right (B - A) (S - A); rw [← hNdef, inner_sub_right] at this; linarith
  have hWN : ∀ w ∈ ({A, B, S} : Finset ℝ³), ⟪N, w⟫ = c := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · rfl
    · exact hNB
    · exact hNS
  -- the crossing point `X = ξA A + ξB B + ξS S`, with `ξB` close to `1`
  have hβc : β₁ < c₁ := by
    have h1 : c₁ * b₂ < c₁ * γ₂ := mul_lt_mul_of_pos_left hlt hc₁
    have h2 : β₁ * γ₂ < c₁ * γ₂ := hconv.trans h1
    exact lt_of_mul_lt_mul_right h2 hγ₂.le
  set φK := t₂ * c₁ + γ₂ * t₁
  have hφK : 0 < φK := by positivity
  set D1 := γ₂ - b₂
  set D2 := t₂ * (c₁ - β₁) + t₁ * (γ₂ - b₂)
  have hD1 : 0 < D1 := by simp only [D1]; linarith
  have hD2 : 0 < D2 := by
    simp only [D2]
    have := mul_pos ht₂ (sub_pos.mpr hβc)
    have := mul_pos ht₁ (sub_pos.mpr hlt)
    linarith
  have hD1γ : D1 < γ₂ := by simp only [D1]; linarith
  have hD2φ : D2 < φK := by
    simp only [D2, φK]; nlinarith [mul_pos ht₂ hβ₁, mul_pos ht₁ hb₂]
  set ε := D1 * D2 / (2 * γ₂ * φK)
  have hε : 0 < ε := by positivity
  have hεγ : γ₂ * ε < D1 := by
    simp only [ε]; rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    linarith [mul_lt_mul_of_pos_left hD2φ (mul_pos hγ₂ hD1), mul_pos (mul_pos hγ₂ hD1) hφK]
  have hεφ : φK * ε < D2 := by
    simp only [ε]; rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    linarith [mul_lt_mul_of_pos_left hD1γ (mul_pos hφK hD2), mul_pos (mul_pos hφK hD2) hγ₂]
  have hε1 : ε < 1 := by
    by_contra h; push Not at h
    have := mul_le_mul_of_nonneg_left h hγ₂.le
    linarith
  set ξA := ε / 2
  set ξB := 1 - ε
  set ξS := ε / 2
  have hξ : ξA + ξB + ξS = 1 := by simp only [ξA, ξB, ξS]; ring
  set X := ξA • A + ξB • B + ξS • S
  have hNX : ⟪N, X⟫ = c := by
    simp only [X, inner_add_right, real_inner_smul_right, hNB, hNS, ← hc]
    linear_combination c * hξ
  have hu₀ : ⟪N, X - C⟫ ≠ 0 := by
    rw [inner_sub_right, hNX]
    intro h0; apply hNC0
    rw [inner_sub_right]; linarith
  refine isRupert_of_crossing _ {A, B, S} (by intro x hx; simp at hx ⊢; tauto) N c hWN
    (by simp) (by simp) (by simp) hindW (X - C) hu₀ ?_
  intro v hv hvW
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv hvW
  push Not at hvW
  have ht₂0 : t₂ ≠ 0 := ht₂.ne'
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hvW.1
  · exact absurd rfl hvW.2.1
  · exact exists_weights3 hAB hAS hBS (t := 1) (by positivity) (by simp only [ξB]; linarith)
      (by positivity) hξ (by simp only [X]; module)
  · -- `S₁ = T`
    refine exists_weights3 hAB hAS hBS (t := γ₂ / t₂) (α := γ₂ * ξA / t₂)
      (β := (γ₂ * ξB - b₂) / t₂) (γ := (1 + γ₂ * ξS) / t₂) (by positivity) ?_ (by positivity)
      ?_ ?_
    · apply div_pos _ ht₂
      simp only [ξB]; nlinarith
    · rw [← add_div, ← add_div, div_eq_one_iff_eq ht₂0]
      linear_combination γ₂ * hξ - hsum₂
    · simp only [X, hS]
      match_scalars <;> field_simp <;> ring
  · -- the cap `K`
    refine exists_weights3 hAB hAS hBS (t := φK / t₂) (α := a₁ + φK / t₂ * ξA)
      (β := (φK * ξB - β₁ * t₂ - t₁ * b₂) / t₂) (γ := t₁ / t₂ + φK / t₂ * ξS)
      (by positivity) ?_ (by positivity) ?_ ?_
    · apply div_pos _ ht₂
      have : φK * ξB = φK - φK * ε := by simp only [ξB]; ring
      have h3 : φK - D2 = β₁ * t₂ + t₁ * b₂ := by simp only [φK, D2]; ring
      linarith
    · field_simp
      simp only [φK, ξA, ξB, ξS]
      first
        | linear_combination t₂ * hsum₁ - t₁ * hsum₂
        | linear_combination -(t₂ * hsum₁ - t₁ * hsum₂)
    · simp only [X, hS, hK, φK]
      match_scalars <;> field_simp <;> ring
  · exact absurd rfl hvW.2.2

/-- **T5 in normal form.**  `(A, B, C, T) = (E, S₃, S₂, S₁)`, the cap
`K = (a₁, -β₁, c₁, t₁)` and `S₄ = (0, b₂, -γ₂, t₂)` in barycentrics, convexity
at `ES₁`: `β₁ γ₂ < c₁ b₂`.  If `γ₂ ≠ b₂` (i.e. `S₁S₄ ∦ S₂S₃`), the view
through `ES₁S₂` (`γ₂ < b₂`) or through `ES₃S₄` (`γ₂ > b₂`) is admissible. -/
theorem isRupert_cappedSquarePyramid_normalForm (A B C T : ℝ³)
    (hind : AffineIndependent ℝ ![A, B, C, T])
    (a₁ β₁ c₁ t₁ b₂ γ₂ t₂ : ℝ) (ha₁ : 0 < a₁) (hβ₁ : 0 < β₁) (hc₁ : 0 < c₁) (ht₁ : 0 < t₁)
    (hb₂ : 0 < b₂) (hγ₂ : 0 < γ₂) (ht₂ : 0 < t₂)
    (hsum₁ : a₁ - β₁ + c₁ + t₁ = 1) (hsum₂ : b₂ - γ₂ + t₂ = 1)
    (hconv : β₁ * γ₂ < c₁ * b₂) (hpar : γ₂ ≠ b₂) :
    IsRupert {A, B, C, T, a₁ • A - β₁ • B + c₁ • C + t₁ • T, b₂ • B - γ₂ • C + t₂ • T} := by
  rcases lt_or_gt_of_ne hpar with h | h
  · have := isRupert_bicap_case A B C T hind a₁ β₁ c₁ t₁ 0 b₂ γ₂ t₂ ha₁ hβ₁ hc₁ ht₁ le_rfl hb₂
      hγ₂ ht₂ hsum₁ (by linarith) hconv h
    simpa using this
  · exact isRupert_cappedSquarePyramid_lateral A B C T hind a₁ β₁ c₁ t₁ b₂ γ₂ t₂ ha₁ hβ₁ hc₁ ht₁
      hb₂ hγ₂ ht₂ hsum₁ hsum₂ hconv h

end SmallRupert

end
