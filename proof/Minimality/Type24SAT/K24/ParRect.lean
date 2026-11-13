module

public import Minimality.Type24SAT.K24.ParEdge
public import Minimality.RightSlide

@[expose] public section

/-!
# Type 24, `D` a parallelogram, `E ∥ G`: the wall piece `R` (`D` a rectangle perpendicular to `E`, `G`)

On the wall `05 ⊥ 23` with `05 ⊥ 06` the edge `05` is perpendicular to the planes `E` and `G`, so `D = 0 4 3 5` is a
rectangle standing between the parallel facets `E` (front vertex `6`) and `G` (front vertex `2`): the Slide Lemma with
triangular walls (`Minimality.Split.Slide.slide_walls`) applies unless the front vertices `1 2 6` overhang both ends of
the edge `04`.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.Par
open Minimality Minimality.H21 Minimality.T24.SAT

variable {x : Fin 7 → ℝ³}

/-- **The rectangle piece of the wall.**  `D` a parallelogram, `E ∥ G`, `05 ⊥ 23` and `05 ⊥ 06`, and the front
vertices (off `D`) all strictly beyond the plane through `0` orthogonal to `04`, or all strictly short of the plane
through `4`: Rupert (Slide Lemma). -/
theorem isRupert_eg_rect (F : S0xFac 9 s0x_S24 x) (hP : x 3 = x 4 + x 5 - x 0)
    (hE : ⟪F.N 4, x 2 - x 3⟫ = 0) (hw : ⟪x 5 - x 0, x 2 - x 3⟫ = 0)
    (hs : ⟪x 5 - x 0, x 6 - x 0⟫ = 0)
    (hSl : (∀ i, i ∉ s0x_S24 3 → 0 < ⟪x i - x 0, x 4 - x 0⟫) ∨
      (∀ i, i ∉ s0x_S24 3 → ⟪x i - x 0, x 4 - x 0⟫ < ⟪x 4 - x 0, x 4 - x 0⟫)) :
    IsRupert (univ.image x) := by
  have IS := F.inner_sub
  have hx := Minimality.H24.SAT.inj_of_fac F
  set d := x 2 - x 3 with hd
  set b := x 6 - x 0 with hb
  set g := x 5 - x 0 with hg
  -- the plane of `E` is spanned by `d` and `b`
  have hD2 := F.neg 3 2 (by decide); have hH0 := F.neg 7 0 (by decide)
  have zH2 := F.zero 7 2 (by decide); have zH3 := F.zero 7 3 (by decide)
  have zH6 := F.zero 7 6 (by decide); have zD3 := F.zero 3 3 (by decide)
  have zE0 := F.zero 4 0 (by decide); have zE6 := F.zero 4 6 (by decide)
  have hK : cross d b ≠ 0 := by
    intro h
    have hb' := h21_binet (F.N 3) (F.N 7) d b
    rw [real_inner_comm (cross _ _), h, inner_zero_left] at hb'
    rw [hd, IS, IS, hb, IS, IS, zD3, zH2, zH3, zH6] at hb'
    nlinarith only [hb', mul_pos (neg_pos.2 hD2) (neg_pos.2 hH0)]
  -- `N_E`, `N_G` and `g` are multiples of `K = d × b`
  have hEb : ⟪F.N 4, b⟫ = 0 := by rw [hb, IS, zE6, zE0]; ring
  obtain ⟨μE, hμE⟩ := h21_mul_cross hK (by rw [real_inner_comm]; exact hE)
    (by rw [real_inner_comm]; exact hEb)
  obtain ⟨μ, hμ⟩ := h21_mul_cross hK (by rw [real_inner_comm, ← hw]) (by rw [real_inner_comm]; exact hs)
  obtain ⟨q, u, hq0, hq1, hu0, hu1, hdec⟩ := eg_decomp F hP hE
  have zG2 := F.zero 6 2 (by decide); have zG3 := F.zero 6 3 (by decide)
  have zG5 := F.zero 6 5 (by decide); have hG0 := F.neg 6 0 (by decide)
  have hE5 := F.neg 4 5 (by decide)
  have hGd : ⟪F.N 6, d⟫ = 0 := by rw [hd, IS, zG2, zG3]; ring
  have hGb : ⟪F.N 6, b⟫ = 0 := by
    have h1 : ⟪F.N 6, x 4 - x 0⟫ = -q * ⟪F.N 6, d⟫ + u * ⟪F.N 6, b⟫ := by
      rw [hdec, inner_add_right, inner_smul_right, inner_smul_right]
    have e35 : x 4 - x 0 = x 3 - x 5 := by rw [hP]; abel
    rw [e35, IS, zG3, zG5, hGd] at h1
    have : u * ⟪F.N 6, b⟫ = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hu0.ne'
    · exact h
  obtain ⟨μG, hμG⟩ := h21_mul_cross hK (by rw [real_inner_comm]; exact hGd)
    (by rw [real_inner_comm]; exact hGb)
  set K := cross d b with hKdef
  -- values along `K`
  have fE : ∀ i, F.f 4 (x i) = μE * ⟪x i - x 0, K⟫ := by
    intro i
    have := IS 4 i 0
    rw [zE0, sub_zero, hμE, real_inner_smul_left, real_inner_comm] at this
    exact this.symm
  have fG : ∀ i, F.f 6 (x i) = μG * ⟪x i - x 5, K⟫ := by
    intro i
    have := IS 6 i 5
    rw [zG5, sub_zero, hμG, real_inner_smul_left, real_inner_comm] at this
    exact this.symm
  have gK : ∀ i, ⟪x i - x 0, g⟫ = μ * ⟪x i - x 0, K⟫ := by
    intro i; rw [hμ, real_inner_smul_right]
  have gK5 : ∀ i, ⟪x i - x 5, g⟫ = μ * ⟪x i - x 5, K⟫ := by
    intro i; rw [hμ, real_inner_smul_right]
  have hgg : 0 < ⟪g, g⟫ := by
    have : g ≠ 0 := fun h => absurd (hx (sub_eq_zero.1 h)) (by decide)
    exact real_inner_self_pos.2 this
  -- signs: μ μE < 0 and μ μG > 0
  have s1 : μ * μE < 0 := by
    have a1 := gK 5; have a2 := fE 5
    have key : (μ * μE) * (⟪x 5 - x 0, K⟫ * ⟪x 5 - x 0, K⟫) = ⟪g, g⟫ * F.f 4 (x 5) := by
      rw [a2]; rw [hg] at a1 ⊢; rw [a1]; ring
    by_contra h; push Not at h
    have := mul_nonneg h (mul_self_nonneg ⟪x 5 - x 0, K⟫)
    linarith [mul_neg_of_pos_of_neg hgg hE5]
  have s2 : 0 < μ * μG := by
    have a1 := gK5 0; have a2 := fG 0
    have e0 : ⟪x 0 - x 5, g⟫ = -⟪g, g⟫ := by
      rw [show x 0 - x 5 = -g by rw [hg]; abel, inner_neg_left]
    rw [e0] at a1
    have key : (μ * μG) * (⟪x 0 - x 5, K⟫ * ⟪x 0 - x 5, K⟫) = -⟪g, g⟫ * F.f 6 (x 0) := by
      rw [a2, a1]; ring
    by_contra h; push Not at h
    have := mul_nonpos_of_nonpos_of_nonneg h (mul_self_nonneg ⟪x 0 - x 5, K⟫)
    linarith [mul_pos_of_neg_of_neg (neg_neg_of_pos hgg) hG0]
  -- the slab
  have Glo : ∀ i, 0 ≤ ⟪x i - x 0, g⟫ := by
    intro i
    have h1 := fE i; have h2 := gK i; have h3 := F.le 4 i
    have hμE0 : μE ≠ 0 := by rintro rfl; rw [mul_zero] at s1; exact lt_irrefl 0 s1
    have key : ⟪x i - x 0, g⟫ * (μE * μE) = (μ * μE) * F.f 4 (x i) := by rw [h2, h1]; ring
    by_contra hc; push Not at hc
    have := mul_neg_of_neg_of_pos hc (mul_self_pos.2 hμE0)
    linarith [mul_nonneg_of_nonpos_of_nonpos s1.le h3]
  have Gz : ∀ i, ⟪x i - x 0, g⟫ = 0 → F.f 4 (x i) = 0 := by
    intro i h0
    have h1 := fE i; have h2 := gK i
    rw [h0] at h2
    rcases mul_eq_zero.1 h2.symm with h | h
    · rw [h, zero_mul] at s1; exact absurd s1 (lt_irrefl 0)
    · rw [h1, h, mul_zero]
  have e5 : ∀ i, ⟪x i - x 0, g⟫ = ⟪x i - x 5, g⟫ + ⟪g, g⟫ := by
    intro i
    rw [show x i - x 0 = (x i - x 5) + g by rw [hg]; abel, inner_add_left]
  have Ghi : ∀ i, ⟪x i - x 5, g⟫ ≤ 0 := by
    intro i
    have h1 := fG i; have h2 := gK5 i; have h3 := F.le 6 i
    have hμG0 : μG ≠ 0 := by rintro rfl; rw [mul_zero] at s2; exact lt_irrefl 0 s2
    have key : ⟪x i - x 5, g⟫ * (μG * μG) = (μ * μG) * F.f 6 (x i) := by rw [h2, h1]; ring
    by_contra hc; push Not at hc
    have := mul_pos hc (mul_self_pos.2 hμG0)
    linarith [mul_nonpos_of_nonneg_of_nonpos s2.le h3]
  have Gt : ∀ i, ⟪x i - x 5, g⟫ = 0 → F.f 6 (x i) = 0 := by
    intro i h0
    have h1 := fG i; have h2 := gK5 i
    rw [h0] at h2
    rcases mul_eq_zero.1 h2.symm with h | h
    · rw [h, zero_mul] at s2; exact absurd s2 (lt_irrefl 0)
    · rw [h1, h, mul_zero]
  -- facet D values
  have zD0 := F.zero 3 0 (by decide)
  have Yv : ∀ i, ⟪x i - x 0, -F.N 3⟫ = -F.f 3 (x i) := by
    intro i; rw [inner_neg_right, real_inner_comm, IS, zD0]; ring
  have Ypos : ∀ i, 0 < ⟪x i - x 0, -F.N 3⟫ → i ∉ s0x_S24 3 := by
    intro i h hi; rw [Yv, F.zero 3 i hi] at h; simp at h
  have hn0 : -F.N 3 ≠ 0 := by
    have := nn24 F 3
    intro h; rw [neg_eq_zero] at h; rw [h, inner_zero_left] at this; exact lt_irrefl 0 this
  refine Minimality.Split.Slide.slide_walls x 0 4 5 3 6 2 (x 4 - x 0) g (-F.N 3)
    (fun i => ⟪x i - x 0, x 4 - x 0⟫) (fun i => ⟪x i - x 0, -F.N 3⟫) (fun i => ⟪x i - x 0, g⟫)
    (fun i => rfl) (fun i => rfl) (fun i => rfl) rfl rfl (by rw [hP, hg]; abel)
    (fun h => absurd (hx (sub_eq_zero.1 h)) (by decide))
    (fun h => absurd (hx (sub_eq_zero.1 h)) (by decide)) hn0 ?_ ?_ ?_ ?_
    (fun i => ⟨Glo i, by
      have h1 := e5 i; have h2 := Ghi i; show ⟪x i - x 0, g⟫ ≤ ⟪g, g⟫; linarith⟩) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- ⟪e, g⟫ = 0
    have h1 := fE 4; have h2 := gK 4
    rw [F.zero 4 4 (by decide)] at h1
    rcases mul_eq_zero.1 h1.symm with h | h
    · rw [h, mul_zero] at s1; exact absurd s1 (lt_irrefl 0)
    · rw [h2, h, mul_zero]
  · rw [inner_neg_right, real_inner_comm, IS, F.zero 3 4 (by decide), zD0]; simp
  · rw [hg, inner_neg_right, real_inner_comm, IS, F.zero 3 5 (by decide), zD0]; simp
  · intro i h0 h4 h5 h3
    rw [Yv]
    have key : ∀ j : Fin 7, j ≠ 0 → j ≠ 4 → j ≠ 5 → j ≠ 3 → j ∉ s0x_S24 3 := by decide
    have : i ∉ s0x_S24 3 := key i h0 h4 h5 h3
    linarith [F.neg 3 i this]
  · rw [Yv]; linarith [F.neg 3 6 (by decide)]
  · show ⟪x 6 - x 0, g⟫ = 0
    have h6 := fE 6; rw [zE6] at h6
    rw [gK]
    rcases mul_eq_zero.1 h6.symm with h | h
    · rw [h, mul_zero] at s1; exact absurd s1 (lt_irrefl 0)
    · rw [h, mul_zero]
  · intro i hY hG0
    have hi := Ypos i hY
    have hE0 := Gz i hG0
    have hiE : i ∈ s0x_S24 4 := by
      by_contra h; exact (F.neg 4 i h).ne hE0
    have key : ∀ j : Fin 7, j ∉ s0x_S24 3 → j ∈ s0x_S24 4 → j = 6 := by decide
    exact key i hi hiE
  · rw [Yv]; linarith [F.neg 3 2 (by decide)]
  · show ⟪x 2 - x 0, g⟫ = ⟪g, g⟫
    have := Gt 2
    rw [e5]
    have h1 := fG 2; have h2 := gK5 2
    rw [zG2] at h1
    rcases mul_eq_zero.1 h1.symm with h | h
    · rw [h, mul_zero] at s2; exact absurd s2 (lt_irrefl 0)
    · rw [h2, h, mul_zero, zero_add]
  · intro i hY hG0
    have hi := Ypos i hY
    have hG' : ⟪x i - x 5, g⟫ = 0 := by have := e5 i; linarith
    have hG0' := Gt i hG'
    have hiG : i ∈ s0x_S24 6 := by
      by_contra h; exact (F.neg 6 i h).ne hG0'
    have key : ∀ j : Fin 7, j ∉ s0x_S24 3 → j ∈ s0x_S24 6 → j = 2 := by decide
    exact key i hi hiG
  · rcases hSl with h | h
    · exact Or.inl fun i hY => h i (Ypos i hY)
    · exact Or.inr fun i hY => h i (Ypos i hY)

open Minimality.H24K.SAT in
/-- **The rectangle piece of the `C ∥ I` wall** (the image of `isRupert_eg_rect` under `σ = (2 6)(4 5)`):
`04 ⊥ 36`, `04 ⊥ 02`, front vertices all beyond the plane through `0` orthogonal to `05` or all short of the
plane through `5`. -/
theorem isRupert_ci_rect (F : S0xFac 9 s0x_S24 x) (hP : x 3 = x 4 + x 5 - x 0)
    (hC : ⟪F.N 2, x 6 - x 3⟫ = 0) (hw : ⟪x 4 - x 0, x 6 - x 3⟫ = 0)
    (hs : ⟪x 4 - x 0, x 2 - x 0⟫ = 0)
    (hSl : (∀ i, i ∉ s0x_S24 3 → 0 < ⟪x i - x 0, x 5 - x 0⟫) ∨
      (∀ i, i ∉ s0x_S24 3 → ⟪x i - x 0, x 5 - x 0⟫ < ⟪x 5 - x 0, x 5 - x 0⟫)) :
    IsRupert (univ.image x) := by
  have hmem : ∀ i, i ∉ s0x_S24 3 ↔ wallSig i ∉ s0x_S24 3 := by decide
  have h := isRupert_eg_rect (facSig F) (x := x ∘ wallSig)
    (by show x 3 = x 5 + x 4 - x 0; rw [hP]; abel) hC hw hs (by
      rcases hSl with h | h
      · exact Or.inl fun i hi => h (wallSig i) ((hmem i).1 hi)
      · exact Or.inr fun i hi => h (wallSig i) ((hmem i).1 hi))
  have e : Finset.univ.image (x ∘ wallSig) = Finset.univ.image x := by
    ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨i, rfl⟩; exact ⟨wallSig i, by rw [wallSig_invol]⟩
  rwa [e] at h

end Minimality.T24.Par
