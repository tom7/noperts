module

public import Minimality.Type10

@[expose] public section

/-!
# Type 26 is Rupert in general position

Theorem L of `FEWER-FACES-PROOFS.md` §7, by the algebraic method of
`Type10.lean`. Faces `A = 0246` (a quadrilateral) and the triangles `013, 016,
034, 136, 235, 236, 245, 345`; the relabelling `0 ↔ 4, 1 ↔ 5, 2 ↔ 6` is an
automorphism. View `P` along the edge `04` (faces `A`, `T = 034`) with the far
end `a ∈ {2, 6}` of `A`. If `a = 2` (`fT x6 / fT x2 ≤ 1`), `P` holds at `1`
(vertex `1` has degree 3: Cramer for `x2` in the frame `x1; x0, x3, x6`), and if
it fails at `5`, the view along the planes of `A` and `235` (through `x2`)
holds (frame `x0; x4, x2, x3`).
It still holds at the tie (`x5` on the far side in `P`). The case `a = 6` is the image under the
automorphism (`type26_core` applied to the relabelled points).
-/

namespace Minimality

open Finset
open scoped RealInnerProductSpace

set_option maxHeartbeats 8000000 in
/-- Theorem L in the case where the far end of `0246` in the view along `04` is
`2` (`fT x6 / fT x2 ≤ 1`). -/
theorem type26_core (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (hgen : GenPos (univ.image x)) (fA fT fG fH fU fW fY : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 2, 4, 6} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 2, 4, 6} : Finset (Fin 7)) → fA (x i) < 0))
    (hT : ∀ i, (i ∈ ({0, 3, 4} : Finset (Fin 7)) → fT (x i) = 0) ∧
      (i ∉ ({0, 3, 4} : Finset (Fin 7)) → fT (x i) < 0))
    (hG : ∀ i, (i ∈ ({2, 3, 5} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({2, 3, 5} : Finset (Fin 7)) → fG (x i) < 0))
    (hH : ∀ i, (i ∈ ({1, 3, 6} : Finset (Fin 7)) → fH (x i) = 0) ∧
      (i ∉ ({1, 3, 6} : Finset (Fin 7)) → fH (x i) < 0))
    (hU : ∀ i, (i ∈ ({0, 1, 3} : Finset (Fin 7)) → fU (x i) = 0) ∧
      (i ∉ ({0, 1, 3} : Finset (Fin 7)) → fU (x i) < 0))
    (hW : ∀ i, (i ∈ ({0, 1, 6} : Finset (Fin 7)) → fW (x i) = 0) ∧
      (i ∉ ({0, 1, 6} : Finset (Fin 7)) → fW (x i) < 0))
    (hY : ∀ i, (i ∈ ({2, 4, 5} : Finset (Fin 7)) → fY (x i) = 0) ∧
      (i ∉ ({2, 4, 5} : Finset (Fin 7)) → fY (x i) < 0))
    (hcase : fT (x 6) / fT (x 2) ≤ 1)
    (hZ1 : EdgeFar (univ.image x) (({0, 2, 4, 6} : Finset (Fin 7)).image x)
      (({0, 3, 4} : Finset (Fin 7)).image x) (x 0) (x 4))
    (hT2 : TriGenFar (univ.image x) (({0, 2, 4, 6} : Finset (Fin 7)).image x)
      (({2, 3, 5} : Finset (Fin 7)).image x) (x 2)) :
    IsRupert (univ.image x) := by
  classical
  set V := univ.image x with hV
  have hxV : ∀ i, x i ∈ V := fun i => Finset.mem_image_of_mem x (Finset.mem_univ i)
  have memQ : ∀ (P : Finset (Fin 7)) i, x i ∈ P.image x ↔ i ∈ P := fun P i => hx.mem_finset_image
  have inter : ∀ P R : Finset (Fin 7), P.image x ∩ R.image x = (P ∩ R).image x :=
    fun P R => (Finset.image_inter P R hx).symm
  have ncol : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k → ∀ c : ℝ, x k - x i ≠ c • (x j - x i) := by
    intro i j k hij hik hjk c
    exact (hgen (x i) (hxV i) (x k) (hxV k) (x i) (hxV i) (x j) (hxV j)
      (fun h => hik (hx h)) (fun h => hij (hx h)) (by
        intro h
        have : x k ∈ ({x i, x j} : Finset ℝ³) := h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with h' | h'
        · exact hik (hx h').symm
        · exact hjk (hx h').symm)).1 c
  have ratio : ∀ (f g : ℝ³ →ᵃ[ℝ] ℝ) (i j k : Fin 7), i ≠ j → i ≠ k → j ≠ k →
      f (x i) = 0 → f (x j) = 0 → f (x k) = 0 → g (x i) = 0 → g (x j) = 0 → g (x k) = 0 →
      ∀ y w, f w ≠ 0 → g w ≠ 0 → f y / f w = g y / g w := by
    intro f g i j k hij hik hjk fi fj fk gi gj gk y w hfw hgw
    rw [div_eq_div_iff hfw hgw]
    have := vanish3_ratio f g (fun h => hij (hx h)) (ncol i j k hij hik hjk) fi fj fk gi gj gk y w
    linarith
  set QA := ({0, 2, 4, 6} : Finset (Fin 7)).image x
  set QT := ({0, 3, 4} : Finset (Fin 7)).image x
  set QG := ({2, 3, 5} : Finset (Fin 7)).image x
  have sub : ∀ P : Finset (Fin 7), P.image x ⊆ V := fun P => Finset.image_subset_image (Finset.subset_univ P)
  have a0 := (hA 0).1 (by decide); have a2 := (hA 2).1 (by decide); have a4 := (hA 4).1 (by decide)
  have a6 := (hA 6).1 (by decide); have a1 := (hA 1).2 (by decide); have a3 := (hA 3).2 (by decide)
  have a5 := (hA 5).2 (by decide)
  have t0 := (hT 0).1 (by decide); have t3 := (hT 3).1 (by decide); have t4 := (hT 4).1 (by decide)
  have t1 := (hT 1).2 (by decide); have t2 := (hT 2).2 (by decide); have t5 := (hT 5).2 (by decide)
  have t6 := (hT 6).2 (by decide)
  have g2 := (hG 2).1 (by decide); have g3 := (hG 3).1 (by decide); have g5 := (hG 5).1 (by decide)
  have g0 := (hG 0).2 (by decide); have g1 := (hG 1).2 (by decide); have g4 := (hG 4).2 (by decide)
  have h1 := (hH 1).1 (by decide); have h3 := (hH 3).1 (by decide); have h6 := (hH 6).1 (by decide)
  have h0 := (hH 0).2 (by decide); have h2 := (hH 2).2 (by decide)
  have u0 := (hU 0).1 (by decide); have u1 := (hU 1).1 (by decide); have u3 := (hU 3).1 (by decide)
  have u2 := (hU 2).2 (by decide); have u4 := (hU 4).2 (by decide); have u6 := (hU 6).2 (by decide)
  have w0 := (hW 0).1 (by decide); have w1 := (hW 1).1 (by decide); have w6 := (hW 6).1 (by decide)
  have w2 := (hW 2).2 (by decide); have w3 := (hW 3).2 (by decide)
  have y2 := (hY 2).1 (by decide); have y4 := (hY 4).1 (by decide); have y5 := (hY 5).1 (by decide)
  have y0 := (hY 0).2 (by decide); have y3 := (hY 3).2 (by decide)
  have na1 := a1.ne; have na3 := a3.ne; have nt2 := t2.ne; have ng4 := g4.ne
  -- (i) `P` holds at `1`: Cramer for `x2` in the frame `x1; x0, x3, x6`
  have hP1 : fT (x 1) / fT (x 2) + fA (x 1) / fA (x 3) < 1 := by
    have hΔ : vol3 (x 0 - x 1) (x 3 - x 1) (x 6 - x 1) ≠ 0 := by
      intro h0'
      have k := affine_vanish3 fH h1 h3 h6 (x 0) (x 1 + crs3 (x 3 - x 1) (x 6 - x 1))
      have pos := vol3_crs3_pos (p := x 1) (q := x 3) (r := x 6) (fun h => by have := hx h; omega)
        (ncol 1 3 6 (by decide) (by decide) (by decide))
      have e : vol3 (x 3 - x 1) (x 6 - x 1) (x 0 - x 1) = vol3 (x 0 - x 1) (x 3 - x 1) (x 6 - x 1) := by
        simp only [vol3, PiLp.sub_apply]; ring
      rw [add_sub_cancel_left, e, h0', zero_mul] at k
      have := mul_neg_of_pos_of_neg pos h0
      linarith
    have co := fun (f : ℝ³ →ᵃ[ℝ] ℝ) => affine_coord f (x 1) (x 0) (x 3) (x 6) (x 2) hΔ
    have cH := co fH; have cU := co fU; have cW := co fW; have cA := co fA; have cT := co fT
    set l0 := vol3 (x 2 - x 1) (x 3 - x 1) (x 6 - x 1) / vol3 (x 0 - x 1) (x 3 - x 1) (x 6 - x 1)
    set l3 := vol3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) / vol3 (x 0 - x 1) (x 3 - x 1) (x 6 - x 1)
    set l6 := vol3 (x 0 - x 1) (x 3 - x 1) (x 2 - x 1) / vol3 (x 0 - x 1) (x 3 - x 1) (x 6 - x 1)
    rw [h1, h3, h6] at cH; rw [u0, u1, u3] at cU; rw [w0, w1, w6] at cW
    rw [a0, a2, a6] at cA; rw [t0, t3] at cT
    have hl0 : 0 < l0 := by
      have : fH (x 2) = l0 * fH (x 0) := by linear_combination cH
      nlinarith
    have hl6 : 0 < l6 := by
      have : fU (x 2) = l6 * fU (x 6) := by linear_combination cU
      nlinarith
    have hl3 : 0 < l3 := by
      have : fW (x 2) = l3 * fW (x 3) := by linear_combination cW
      nlinarith
    have hΛ : 0 < l0 + l3 + l6 - 1 := by
      have k : fA (x 1) * (l0 + l3 + l6 - 1) = l3 * fA (x 3) := by linear_combination cA
      have := mul_neg_of_pos_of_neg hl3 a3
      nlinarith
    have hk : (1 - (fT (x 1) / fT (x 2) + fA (x 1) / fA (x 3))) * (l0 + l3 + l6 - 1) =
        l0 + l6 * (1 - fT (x 6) / fT (x 2)) := by
      field_simp; linear_combination (-fA (x 3)) * cT - fT (x 2) * cA
    have : 0 < l0 + l6 * (1 - fT (x 6) / fT (x 2)) := by
      have := mul_nonneg hl6.le (sub_nonneg.mpr hcase); linarith
    rw [← hk] at this
    by_contra hle; push Not at hle
    have := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hle) hΛ.le
    linarith
  rcases lt_or_ge (fT (x 5) / fT (x 2) + fA (x 5) / fA (x 3)) 1 with h5lt | h5gt
  · -- the view `P` along the edge `04`
    refine isRupert_of_facets_edge V hgen QA QT (sub _) (sub _) (isFacet_of_index x _ fA hA)
      (isFacet_of_index x _ fT hT) (x 0) (x 4) (fun h => by have := hx h; omega) ?_
      ⟨x 2, (memQ _ 2).mpr (by decide), by rw [memQ]; decide⟩
      ⟨x 3, (memQ _ 3).mpr (by decide), by rw [memQ]; decide⟩ hZ1 ?_
    · rw [inter, show ({0, 2, 4, 6} ∩ {0, 3, 4} : Finset (Fin 7)) = {0, 4} by decide]
      simp [Finset.image_insert]
    refine ⟨x 2, (memQ _ 2).mpr (by decide), x 3, (memQ _ 3).mpr (by decide),
      by rw [memQ]; decide, by rw [memQ]; decide, ?_⟩
    intro f1 f2 z1 n1 z2 n2 y hy hy1 hy2
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
    rw [memQ] at hy1 hy2
    have hi : i = 1 ∨ i = 5 := by clear * - hy1 hy2; fin_cases i <;> simp_all
    have e2' : ∀ k : Fin 7, f2 (x k) / f2 (x 2) = fT (x k) / fT (x 2) :=
      fun k => ratio f2 fT 0 3 4 (by decide) (by decide) (by decide)
        (z2 _ ((memQ _ 0).mpr (by decide))) (z2 _ ((memQ _ 3).mpr (by decide)))
        (z2 _ ((memQ _ 4).mpr (by decide))) ((hT 0).1 (by decide)) ((hT 3).1 (by decide))
        ((hT 4).1 (by decide)) _ _ (n2 _ (hxV 2) (by rw [memQ]; decide)).ne
        ((hT 2).2 (by decide)).ne
    have e1' : ∀ k : Fin 7, f1 (x k) / f1 (x 3) = fA (x k) / fA (x 3) :=
      fun k => ratio f1 fA 0 2 4 (by decide) (by decide) (by decide)
        (z1 _ ((memQ _ 0).mpr (by decide))) (z1 _ ((memQ _ 2).mpr (by decide)))
        (z1 _ ((memQ _ 4).mpr (by decide))) ((hA 0).1 (by decide)) ((hA 2).1 (by decide))
        ((hA 4).1 (by decide)) _ _ (n1 _ (hxV 3) (by rw [memQ]; decide)).ne
        ((hA 3).2 (by decide)).ne
    rcases hi with rfl | rfl
    · rw [e2' 1, e1' 1]; exact hP1
    · rw [e2' 5, e1' 5]; exact h5lt
  · -- (ii) `P` fails at `5`: the view along the planes of `0246` and `235`
    have hΔ : vol3 (x 4 - x 0) (x 2 - x 0) (x 3 - x 0) ≠ 0 := by
      intro h0'
      have k := affine_vanish3 fT t0 t4 t3 (x 2) (x 0 + crs3 (x 4 - x 0) (x 3 - x 0))
      have pos := vol3_crs3_pos (p := x 0) (q := x 4) (r := x 3) (fun h => by have := hx h; omega)
        (ncol 0 4 3 (by decide) (by decide) (by decide))
      have e : vol3 (x 4 - x 0) (x 3 - x 0) (x 2 - x 0) = -vol3 (x 4 - x 0) (x 2 - x 0) (x 3 - x 0) := by
        simp only [vol3, PiLp.sub_apply]; ring
      rw [add_sub_cancel_left, e, h0', neg_zero, zero_mul] at k
      have := mul_neg_of_pos_of_neg pos t2
      linarith
    have co := fun (f : ℝ³ →ᵃ[ℝ] ℝ) (i : Fin 7) => affine_coord f (x 0) (x 4) (x 2) (x 3) (x i) hΔ
    have cA1 := co fA 1; have cT1 := co fT 1; have cG1 := co fG 1; have cU1 := co fU 1
    have cA5 := co fA 5; have cT5 := co fT 5; have cG5 := co fG 5; have cY5 := co fY 5
    set Δ := vol3 (x 4 - x 0) (x 2 - x 0) (x 3 - x 0)
    set α1 := vol3 (x 1 - x 0) (x 2 - x 0) (x 3 - x 0) / Δ
    set β1 := vol3 (x 4 - x 0) (x 1 - x 0) (x 3 - x 0) / Δ
    set γ1 := vol3 (x 4 - x 0) (x 2 - x 0) (x 1 - x 0) / Δ
    set α5 := vol3 (x 5 - x 0) (x 2 - x 0) (x 3 - x 0) / Δ
    set β5 := vol3 (x 4 - x 0) (x 5 - x 0) (x 3 - x 0) / Δ
    set γ5 := vol3 (x 4 - x 0) (x 2 - x 0) (x 5 - x 0) / Δ
    rw [a0, a4, a2] at cA1 cA5; rw [t0, t4, t3] at cT1 cT5; rw [g2, g3] at cG1
    rw [g2, g3, g5] at cG5; rw [u0, u1, u3] at cU1; rw [y2, y4, y5] at cY5
    have hγ5 : 0 < γ5 := by
      have : fA (x 5) = γ5 * fA (x 3) := by linear_combination cA5
      nlinarith
    have hσ5 : 1 - (α5 + β5 + γ5) < 0 := by
      have : fY (x 0) * (1 - (α5 + β5 + γ5)) = -(γ5 * fY (x 3)) := by linear_combination -cY5
      nlinarith
    have hβ1 : 0 < β1 := by
      have : fT (x 1) = β1 * fT (x 2) := by linear_combination cT1
      nlinarith
    have hα1 : α1 < 0 := by
      have : α1 * fU (x 4) = -(β1 * fU (x 2)) := by linear_combination -cU1
      nlinarith
    have hσ1 : 0 < 1 - (α1 + β1 + γ1) := by
      have : fG (x 1) = fG (x 0) * (1 - (α1 + β1 + γ1)) + α1 * fG (x 4) := by linear_combination cG1
      nlinarith
    have P5 : fT (x 5) / fT (x 2) + fA (x 5) / fA (x 3) = β5 + γ5 := by
      field_simp; linear_combination fA (x 3) * cT5 + fT (x 2) * cA5
    rw [P5] at h5gt
    have hr : fG (x 0) / fG (x 4) ≤ 1 := by
      have k : fG (x 0) / fG (x 4) * (1 - (α5 + β5 + γ5)) = -α5 := by
        field_simp; linear_combination -cG5
      by_contra hle; push Not at hle
      have := mul_lt_mul_of_neg_right hle hσ5
      linarith
    refine isRupert_of_facets_vertex V hgen QA QG (sub _) (sub _) (isFacet_of_index x _ fA hA)
      (isFacet_of_index x _ fG hG) (x 2) ?_
      ⟨x 4, (memQ _ 4).mpr (by decide), fun h => by have := hx h; omega⟩
      ⟨x 3, (memQ _ 3).mpr (by decide), fun h => by have := hx h; omega⟩ hT2 ?_
    · rw [inter, show ({0, 2, 4, 6} ∩ {2, 3, 5} : Finset (Fin 7)) = {2} by decide]
      simp
    refine ⟨x 4, (memQ _ 4).mpr (by decide), x 3, (memQ _ 3).mpr (by decide),
      fun h => by have := hx h; omega, fun h => by have := hx h; omega, ?_⟩
    intro f1 f2 z1 n1 z2 n2 y hy hy1 hy2
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
    rw [memQ] at hy1 hy2
    have hi : i = 1 := by clear * - hy1 hy2; fin_cases i <;> simp_all
    subst hi
    have e2' : f2 (x 1) / f2 (x 4) = fG (x 1) / fG (x 4) :=
      ratio f2 fG 2 3 5 (by decide) (by decide) (by decide)
        (z2 _ ((memQ _ 2).mpr (by decide))) (z2 _ ((memQ _ 3).mpr (by decide)))
        (z2 _ ((memQ _ 5).mpr (by decide))) ((hG 2).1 (by decide)) ((hG 3).1 (by decide))
        ((hG 5).1 (by decide)) _ _ (n2 _ (hxV 4) (by rw [memQ]; decide)).ne
        ((hG 4).2 (by decide)).ne
    have e1' : f1 (x 1) / f1 (x 3) = fA (x 1) / fA (x 3) :=
      ratio f1 fA 0 2 4 (by decide) (by decide) (by decide)
        (z1 _ ((memQ _ 0).mpr (by decide))) (z1 _ ((memQ _ 2).mpr (by decide)))
        (z1 _ ((memQ _ 4).mpr (by decide))) ((hA 0).1 (by decide)) ((hA 2).1 (by decide))
        ((hA 4).1 (by decide)) _ _ (n1 _ (hxV 3) (by rw [memQ]; decide)).ne
        ((hA 3).2 (by decide)).ne
    rw [e1', e2']
    have k : fG (x 1) / fG (x 4) + fA (x 1) / fA (x 3) =
        fG (x 0) / fG (x 4) * (1 - (α1 + β1 + γ1)) + α1 + γ1 := by
      field_simp; linear_combination fA (x 3) * cG1 + fG (x 4) * cA1
    rw [k]
    have := mul_le_mul_of_nonneg_right hr hσ1.le
    linarith

set_option maxHeartbeats 8000000 in
/-- **Theorem L (type 26).** Seven labelled points in general position with
facets `0246` (a quadrilateral), `034`, `235`, `136`, `013`, `016`, `245`, `345`,
given by functionals negative off them, are Rupert, given
distinct far depths along `04` (`EdgeFar`) and `TriGenFar` at the lines of the planes of `0246`
and `235` and of `0246` and `136`. -/
theorem isRupert_type26 (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (hgen : GenPos (univ.image x)) (fA fT fG fH fU fW fY fZ : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 2, 4, 6} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 2, 4, 6} : Finset (Fin 7)) → fA (x i) < 0))
    (hT : ∀ i, (i ∈ ({0, 3, 4} : Finset (Fin 7)) → fT (x i) = 0) ∧
      (i ∉ ({0, 3, 4} : Finset (Fin 7)) → fT (x i) < 0))
    (hG : ∀ i, (i ∈ ({2, 3, 5} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({2, 3, 5} : Finset (Fin 7)) → fG (x i) < 0))
    (hH : ∀ i, (i ∈ ({1, 3, 6} : Finset (Fin 7)) → fH (x i) = 0) ∧
      (i ∉ ({1, 3, 6} : Finset (Fin 7)) → fH (x i) < 0))
    (hU : ∀ i, (i ∈ ({0, 1, 3} : Finset (Fin 7)) → fU (x i) = 0) ∧
      (i ∉ ({0, 1, 3} : Finset (Fin 7)) → fU (x i) < 0))
    (hW : ∀ i, (i ∈ ({0, 1, 6} : Finset (Fin 7)) → fW (x i) = 0) ∧
      (i ∉ ({0, 1, 6} : Finset (Fin 7)) → fW (x i) < 0))
    (hY : ∀ i, (i ∈ ({2, 4, 5} : Finset (Fin 7)) → fY (x i) = 0) ∧
      (i ∉ ({2, 4, 5} : Finset (Fin 7)) → fY (x i) < 0))
    (hZ : ∀ i, (i ∈ ({3, 4, 5} : Finset (Fin 7)) → fZ (x i) = 0) ∧
      (i ∉ ({3, 4, 5} : Finset (Fin 7)) → fZ (x i) < 0))
    (hZ1 : EdgeFar (univ.image x) (({0, 2, 4, 6} : Finset (Fin 7)).image x)
      (({0, 3, 4} : Finset (Fin 7)).image x) (x 0) (x 4))
    (hT2 : TriGenFar (univ.image x) (({0, 2, 4, 6} : Finset (Fin 7)).image x)
      (({2, 3, 5} : Finset (Fin 7)).image x) (x 2))
    (hT6 : TriGenFar (univ.image x) (({0, 2, 4, 6} : Finset (Fin 7)).image x)
      (({1, 3, 6} : Finset (Fin 7)).image x) (x 6)) :
    IsRupert (univ.image x) := by
  classical
  by_cases hc : fT (x 6) / fT (x 2) ≤ 1
  · exact type26_core x hx hgen fA fT fG fH fU fW fY hA hT hG hH hU hW hY hc hZ1 hT2
  -- the automorphism `0 ↔ 4, 1 ↔ 5, 2 ↔ 6`
  set σ : Fin 7 → Fin 7 := ![4, 5, 6, 3, 0, 1, 2] with hσ
  have σσ : ∀ i, σ (σ i) = i := by decide
  have σinj : Function.Injective σ := fun i j h => by rw [← σσ i, h, σσ]
  set y := x ∘ σ with hy
  have imgσ : ∀ P R : Finset (Fin 7), P.image σ = R → P.image y = R.image x := by
    intro P R h; rw [hy, ← Finset.image_image, h]
  have hV : univ.image y = univ.image x := imgσ _ _ (by decide)
  have tr : ∀ (f : ℝ³ →ᵃ[ℝ] ℝ) (P R : Finset (Fin 7)), (∀ i, σ i ∈ R ↔ i ∈ P) →
      (∀ i, (i ∈ R → f (x i) = 0) ∧ (i ∉ R → f (x i) < 0)) →
      ∀ i, (i ∈ P → f (y i) = 0) ∧ (i ∉ P → f (y i) < 0) :=
    fun f P R hPR h i => ⟨fun hi => (h (σ i)).1 ((hPR i).mpr hi),
      fun hi => (h (σ i)).2 (fun h' => hi ((hPR i).mp h'))⟩
  have ev : ∀ i, y i = x (σ i) := fun i => rfl
  have y0 : y 0 = x 4 := rfl
  have y1 : y 1 = x 5 := rfl
  have y2 : y 2 = x 6 := rfl
  have y3 : y 3 = x 3 := rfl
  have y4 : y 4 = x 0 := rfl
  have y5 : y 5 = x 1 := rfl
  have y6 : y 6 = x 2 := rfl
  rw [← hV]
  have t2 := (hT 2).2 (by decide); have t6 := (hT 6).2 (by decide)
  refine type26_core y (hx.comp σinj) (hV ▸ hgen) fA fT fH fG fZ fY fW
    (tr fA _ _ (by decide) hA) (tr fT _ _ (by decide) hT) (tr fH _ _ (by decide) hH)
    (tr fG _ _ (by decide) hG) (tr fZ _ _ (by decide) hZ) (tr fY _ _ (by decide) hY)
    (tr fW _ _ (by decide) hW) ?_ ?_ ?_
  · rw [y6, y2, div_le_one_of_neg t6]
    push Not at hc
    exact ((one_lt_div_of_neg t2).mp hc).le
  · rw [hV, imgσ _ ({0, 2, 4, 6} : Finset (Fin 7)) (by decide),
      imgσ _ ({0, 3, 4} : Finset (Fin 7)) (by decide), y4, y0]
    intro f1 f2 a1 a2 a3 a4 p hp q hq hpq h1 h2 h
    apply hZ1 f1 f2 a1 a2 a3 a4 p hp q hq hpq h1 h2
    have e : ∀ r : ℝ³, ⟪r, x 0 - x 4⟫ = -⟪r, x 4 - x 0⟫ := fun r => by
      rw [← inner_neg_right, neg_sub]
    rw [e, e] at h; linarith
  · rw [hV, imgσ _ ({0, 2, 4, 6} : Finset (Fin 7)) (by decide),
      imgσ _ ({1, 3, 6} : Finset (Fin 7)) (by decide), y2]
    exact hT6

end Minimality

end
