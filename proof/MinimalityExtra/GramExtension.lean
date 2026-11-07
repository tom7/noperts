module

public import Mathlib
public import MinimalityExtra

/-!
# The Gram extension lemmas

Proof of `GramExtensionTwoViews` and `GramExtensionOneView` of `MinimalityExtra.lean`. The necessity
direction is positivity of the metric on `c u₁ - a u₂`. The sufficiency direction completes the
two-by-two Gram matrix of the views to a three-by-three positive definite one (`exists_pd_completion`),
conjugated back by the basis `u₁, u₂, u₁ × u₂`. The one-view case is an explicit rank-one-plus-identity
matrix.
-/

@[expose] public section

open Matrix

namespace GramExt

/-- A 3x3 symmetric matrix with a positive leading 2x2 block can be completed to a positive definite
one. -/
theorem exists_pd_completion (a b c p q : ℝ) (ha : 0 < a) (hD : c ^ 2 < a * b) :
    ∃ l : ℝ, (!![a, c, p; c, b, q; p, q, l] : Matrix (Fin 3) (Fin 3) ℝ).PosDef := by
  have hD' : 0 < a * b - c ^ 2 := by linarith
  refine ⟨p ^ 2 / a + (a * q - c * p) ^ 2 / (a * (a * b - c ^ 2)) + 1, ?_⟩
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · intro x hx
    have hQ : star x ⬝ᵥ ((!![a, c, p; c, b, q; p, q,
        p ^ 2 / a + (a * q - c * p) ^ 2 / (a * (a * b - c ^ 2)) + 1] : Matrix (Fin 3) (Fin 3) ℝ)
          *ᵥ x) =
        a * (x 0 + (c * x 1 + p * x 2) / a) ^ 2 +
        ((a * b - c ^ 2) / a) * (x 1 + ((a * q - c * p) / (a * b - c ^ 2)) * x 2) ^ 2
        + (x 2) ^ 2 := by
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
      field_simp
      ring
    rw [hQ]
    by_contra hneg
    push Not at hneg
    have h1 : 0 ≤ a * (x 0 + (c * x 1 + p * x 2) / a) ^ 2 := by positivity
    have h2 : 0 ≤ ((a * b - c ^ 2) / a) * (x 1 + ((a * q - c * p) / (a * b - c ^ 2)) * x 2) ^ 2 := by
      positivity
    have h3 : 0 ≤ (x 2) ^ 2 := sq_nonneg _
    have e3 : x 2 = 0 := by nlinarith
    have e2 : x 1 = 0 := by
      have : ((a * b - c ^ 2) / a) * (x 1 + ((a * q - c * p) / (a * b - c ^ 2)) * x 2) ^ 2 = 0 := by
        nlinarith
      rw [e3] at this
      simpa [ha.ne', hD'.ne'] using this
    have e1 : x 0 = 0 := by
      have : a * (x 0 + (c * x 1 + p * x 2) / a) ^ 2 = 0 := by nlinarith
      rw [e3, e2] at this
      simpa [ha.ne'] using this
    apply hx
    ext i
    fin_cases i <;> simp [e1, e2, e3]

/-- Necessity direction. -/
theorem gram_necessary (u1 u2 w1 w2 : Fin 3 → ℝ) (hli : LinearIndependent ℝ ![u1, u2])
    (G : Matrix (Fin 3) (Fin 3) ℝ) (hG : G.PosDef) (h1 : G *ᵥ u1 = w1) (h2 : G *ᵥ u2 = w2) :
    w1 ⬝ᵥ u2 = w2 ⬝ᵥ u1 ∧ 0 < w1 ⬝ᵥ u1 ∧ 0 < w2 ⬝ᵥ u2 ∧
      (w1 ⬝ᵥ u2) ^ 2 < (w1 ⬝ᵥ u1) * (w2 ⬝ᵥ u2) := by
  have hsym : ∀ x y : Fin 3 → ℝ, (G *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (G *ᵥ y) := by
    intro x y
    have e : ∀ i j, G i j = G j i := fun i j => by
      have := hG.isHermitian.apply j i
      simpa using this
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
    linear_combination (x 1 * y 0 - x 0 * y 1) * e 0 1 + (x 2 * y 0 - x 0 * y 2) * e 0 2
      + (x 2 * y 1 - x 1 * y 2) * e 1 2
  have hpos : ∀ x : Fin 3 → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (G *ᵥ x) := fun x hx => by
    simpa using hG.dotProduct_mulVec_pos hx
  have hu1 : u1 ≠ 0 := hli.ne_zero 0
  have hu2 : u2 ≠ 0 := hli.ne_zero 1
  have hc : w1 ⬝ᵥ u2 = w2 ⬝ᵥ u1 := by
    rw [← h1, ← h2, hsym, dotProduct_comm]
  have ha : 0 < w1 ⬝ᵥ u1 := by
    have := hpos u1 hu1
    rw [h1] at this
    rwa [dotProduct_comm] at this
  have hb : 0 < w2 ⬝ᵥ u2 := by
    have := hpos u2 hu2
    rw [h2] at this
    rwa [dotProduct_comm] at this
  refine ⟨hc, ha, hb, ?_⟩
  set a := w1 ⬝ᵥ u1 with hadef
  set b := w2 ⬝ᵥ u2 with hbdef
  set c := w1 ⬝ᵥ u2 with hcdef
  have hx : c • u1 - a • u2 ≠ 0 := by
    intro h
    have := (LinearIndependent.pair_iff.1 hli) c (-a) (by rw [neg_smul, ← sub_eq_add_neg]; exact h)
    exact ha.ne' (by linarith [this.2])
  have key := hpos _ hx
  have e1 : u1 ⬝ᵥ w1 = a := dotProduct_comm _ _
  have e2 : u2 ⬝ᵥ w2 = b := dotProduct_comm _ _
  have e3 : u1 ⬝ᵥ w2 = c := by rw [dotProduct_comm, ← hc]
  have e4 : u2 ⬝ᵥ w1 = c := by rw [dotProduct_comm]
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, h1, h2] at key
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul, e1, e2,
    e3, e4] at key
  nlinarith


/-- Sufficiency direction. -/
theorem gram_sufficient (u1 u2 w1 w2 : Fin 3 → ℝ) (hli : LinearIndependent ℝ ![u1, u2])
    (hc : w1 ⬝ᵥ u2 = w2 ⬝ᵥ u1) (ha : 0 < w1 ⬝ᵥ u1) (hb : 0 < w2 ⬝ᵥ u2)
    (hd : (w1 ⬝ᵥ u2) ^ 2 < (w1 ⬝ᵥ u1) * (w2 ⬝ᵥ u2)) :
    ∃ G : Matrix (Fin 3) (Fin 3) ℝ, G.PosDef ∧ G *ᵥ u1 = w1 ∧ G *ᵥ u2 = w2 := by
  set n : Fin 3 → ℝ := crossProduct u1 u2 with hn
  have hn0 : n ≠ 0 := crossProduct_ne_zero_iff_linearIndependent.2 hli
  set B : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of ![u1, u2, n] with hB
  set C : Matrix (Fin 3) (Fin 3) ℝ := Bᵀ with hC
  have hdet : B.det = n ⬝ᵥ n := by
    simp [hB, hn, Matrix.det_fin_three, crossProduct, dotProduct, Fin.sum_univ_three]
    ring
  have hdet0 : B.det ≠ 0 := by
    rw [hdet]; exact fun h => hn0 (dotProduct_self_eq_zero.1 h)
  have hU : IsUnit C.det := by
    rw [hC, Matrix.det_transpose]; exact isUnit_iff_ne_zero.2 hdet0
  set K : Matrix (Fin 3) (Fin 3) ℝ := C⁻¹ with hK
  have hCK : C * K = 1 := Matrix.mul_nonsing_inv C hU
  have hKC : K * C = 1 := Matrix.nonsing_inv_mul C hU
  obtain ⟨l, hM⟩ := exists_pd_completion (w1 ⬝ᵥ u1) (w2 ⬝ᵥ u2) (w1 ⬝ᵥ u2) (n ⬝ᵥ w1) (n ⬝ᵥ w2)
    ha hd
  set M : Matrix (Fin 3) (Fin 3) ℝ := !![w1 ⬝ᵥ u1, w1 ⬝ᵥ u2, n ⬝ᵥ w1; w1 ⬝ᵥ u2, w2 ⬝ᵥ u2, n ⬝ᵥ w2;
    n ⬝ᵥ w1, n ⬝ᵥ w2, l] with hMdef
  have hKinj : Function.Injective K.mulVec := by
    intro x y hxy
    have := congrArg (fun z => C *ᵥ z) hxy
    simpa [Matrix.mulVec_mulVec, hCK] using this
  have hG : (Kᴴ * M * K).PosDef := hM.conjTranspose_mul_mul_same hKinj
  have KB : Kᵀ * B = 1 := by
    have : (C * K)ᵀ = 1 := by rw [hCK]; simp
    rw [Matrix.transpose_mul, hC, Matrix.transpose_transpose] at this
    exact this
  have gen : ∀ (e u w : Fin 3 → ℝ), C *ᵥ e = u → M *ᵥ e = B *ᵥ w → (Kᵀ * M * K) *ᵥ u = w := by
    intro e u w h1 h2
    have hKu : K *ᵥ u = e := by rw [← h1, Matrix.mulVec_mulVec, hKC]; simp
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hKu, h2, Matrix.mulVec_mulVec, KB]
    simp
  have hc' := hc
  simp only [dotProduct, Fin.sum_univ_three] at hc'
  refine ⟨Kᴴ * M * K, hG, ?_, ?_⟩
  · rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    refine gen (Pi.single 0 1) u1 w1 ?_ ?_
    · ext i; fin_cases i <;> simp [hC, hB]
    · ext i; fin_cases i <;> simp [hMdef, hB, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
        dotProduct_comm] <;> linarith
  · rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    refine gen (Pi.single 1 1) u2 w2 ?_ ?_
    · ext i; fin_cases i <;> simp [hC, hB]
    · ext i; fin_cases i <;> simp [hMdef, hB, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
        dotProduct_comm] <;> linarith

theorem one_view_sufficient (u w : Fin 3 → ℝ) (hu : u ≠ 0) (hs0 : 0 < w ⬝ᵥ u) :
    ∃ G : Matrix (Fin 3) (Fin 3) ℝ, G.PosDef ∧ G *ᵥ u = w := by
  have huu0 : 0 < u ⬝ᵥ u := by
    rcases (dotProduct_self_star_nonneg (v := u)).lt_or_eq with h | h
    · simpa using h
    · exact absurd (dotProduct_self_eq_zero.1 (by simpa using h.symm)) hu
  obtain ⟨s, hsd⟩ : ∃ s, s = w 0 * u 0 + w 1 * u 1 + w 2 * u 2 := ⟨_, rfl⟩
  obtain ⟨uu, hud⟩ : ∃ uu, uu = u 0 * u 0 + u 1 * u 1 + u 2 * u 2 := ⟨_, rfl⟩
  have hs : 0 < s := by
    rw [hsd]; simpa [dotProduct, Fin.sum_univ_three] using hs0
  have huu : 0 < uu := by
    rw [hud]; simpa [dotProduct, Fin.sum_univ_three] using huu0
  refine ⟨Matrix.of fun i j => w i * w j / s + (if i = j then 1 else 0) - u i * u j / uu, ?_, ?_⟩
  · refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
    · ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial]
      rw [mul_comm (w j), mul_comm (u j)]
      simp only [eq_comm (a := j)]
    · intro x hx
      obtain ⟨t, ht⟩ : ∃ t, t = (u 0 * x 0 + u 1 * x 1 + u 2 * x 2) / uu := ⟨_, rfl⟩
      have hQ : star x ⬝ᵥ ((Matrix.of fun i j => w i * w j / s + (if i = j then 1 else 0)
          - u i * u j / uu) *ᵥ x) =
          (w 0 * x 0 + w 1 * x 1 + w 2 * x 2) ^ 2 / s +
            ((x 0 - t * u 0) ^ 2 + (x 1 - t * u 1) ^ 2 + (x 2 - t * u 2) ^ 2) := by
        simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three, star_trivial, Matrix.of_apply, ht]
        simp
        subst hud
        have hne := huu.ne'
        have hne2 : u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 ≠ 0 := by intro h; apply hne; nlinarith
        field_simp
        ring
      rw [hQ]
      have e1 : 0 ≤ (w 0 * x 0 + w 1 * x 1 + w 2 * x 2) ^ 2 / s := by positivity
      by_cases hy : x 0 - t * u 0 = 0 ∧ x 1 - t * u 1 = 0 ∧ x 2 - t * u 2 = 0
      · obtain ⟨y0, y1, y2⟩ := hy
        have ht0 : t ≠ 0 := by
          intro h0
          apply hx
          rw [h0] at y0 y1 y2
          ext i; fin_cases i <;> simp <;> linarith
        have hwx : w 0 * x 0 + w 1 * x 1 + w 2 * x 2 = t * s := by
          have a0 : x 0 = t * u 0 := by linarith
          have a1 : x 1 = t * u 1 := by linarith
          have a2 : x 2 = t * u 2 := by linarith
          rw [a0, a1, a2, hsd]; ring
        rw [y0, y1, y2, hwx]
        have : 0 < (t * s) ^ 2 / s := by positivity
        simpa using this
      · have : 0 < (x 0 - t * u 0) ^ 2 + (x 1 - t * u 1) ^ 2 + (x 2 - t * u 2) ^ 2 := by
          by_contra hc
          apply hy
          refine ⟨?_, ?_, ?_⟩ <;> nlinarith [sq_nonneg (x 0 - t * u 0), sq_nonneg (x 1 - t * u 1),
            sq_nonneg (x 2 - t * u 2)]
        linarith
  · ext i
    fin_cases i <;> (simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]; field_simp; rw [hsd, hud]; ring)

end GramExt

namespace MinimalityExtra

open GramExt

/-- Proof of `GramExtensionTwoViews`. -/
theorem gramExtensionTwoViews : GramExtensionTwoViews := by
  intro u₁ u₂ w₁ w₂ hli
  constructor
  · rintro ⟨G, hG, h1, h2⟩
    exact gram_necessary u₁ u₂ w₁ w₂ hli G hG h1 h2
  · rintro ⟨hc, ha, hb, hd⟩
    exact gram_sufficient u₁ u₂ w₁ w₂ hli hc ha hb hd

/-- Proof of `GramExtensionOneView`. -/
theorem gramExtensionOneView : GramExtensionOneView := by
  intro u w hu
  constructor
  · rintro ⟨G, hG, h⟩
    have := hG.dotProduct_mulVec_pos hu
    rw [h] at this
    simpa [dotProduct_comm] using this
  · exact one_view_sufficient u w hu

end MinimalityExtra

#print axioms MinimalityExtra.gramExtensionTwoViews
#print axioms MinimalityExtra.gramExtensionOneView
