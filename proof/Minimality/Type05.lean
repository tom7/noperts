module

public import Minimality.Type10
public import Minimality.TriFacetsChord

@[expose] public section

/-!
# Type 05 at the facet level

Type 05 (three quadrilaterals `0123`, `0145`, `1256` and the triangles `034`,
`234`, `246`, `456`), by the algebraic method of `Type10.lean` instead of
Theorem B′: view `P` along the line of the planes of `A = 0123` and `G = 246`
(through `x2`), view `Q` along that of `B = 0145` and `G` (through `x4`). In the
frame `x0; x2, x4, x6`, with `c = fA x6 / fA x4 + fB x6 / fB x2 - 1`, the values
are `1 + γ5 c` (`P`) and `1 + γ3 c` (`Q`), with `γ3 < 0 < γ5` (faces `234`,
`456`).
At `c = 0` the only point `x5` off both planes of `P` is on the far side, and
`P` works by Lemma T′ (`isRupert_of_facets_vertex_chord`).
-/

namespace Minimality

open Finset
open scoped RealInnerProductSpace

set_option maxHeartbeats 8000000 in
/-- **Type 05 by Lemma T.** Seven labelled points, no three collinear, with
facets `0123`, `0145` (quadrilaterals), `246`, `456`, `234`, given by
functionals negative off them, are Rupert, given `TriGenFar` at the lines of the
planes of `0123` and `246` and of `0145` and `246`. -/
theorem isRupert_type05_facets (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (hgen : NoThreeCollinear (univ.image x)) (fA fB fG fK fH : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 1, 2, 3} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 1, 2, 3} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({0, 1, 4, 5} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({0, 1, 4, 5} : Finset (Fin 7)) → fB (x i) < 0))
    (hG : ∀ i, (i ∈ ({2, 4, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({2, 4, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hK : ∀ i, (i ∈ ({4, 5, 6} : Finset (Fin 7)) → fK (x i) = 0) ∧
      (i ∉ ({4, 5, 6} : Finset (Fin 7)) → fK (x i) < 0))
    (hH : ∀ i, (i ∈ ({2, 3, 4} : Finset (Fin 7)) → fH (x i) = 0) ∧
      (i ∉ ({2, 3, 4} : Finset (Fin 7)) → fH (x i) < 0))
    (hT1 : TriGenFar (univ.image x) (({0, 1, 2, 3} : Finset (Fin 7)).image x)
      (({2, 4, 6} : Finset (Fin 7)).image x) (x 2))
    (hT2 : TriGenFar (univ.image x) (({0, 1, 4, 5} : Finset (Fin 7)).image x)
      (({2, 4, 6} : Finset (Fin 7)).image x) (x 4)) :
    IsRupert (univ.image x) := by
  classical
  set V := univ.image x with hV
  have hxV : ∀ i, x i ∈ V := fun i => Finset.mem_image_of_mem x (Finset.mem_univ i)
  have memQ : ∀ (P : Finset (Fin 7)) i, x i ∈ P.image x ↔ i ∈ P := fun P i => hx.mem_finset_image
  have inter : ∀ P R : Finset (Fin 7), P.image x ∩ R.image x = (P ∩ R).image x :=
    fun P R => (Finset.image_inter P R hx).symm
  have ncol : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k → ∀ c : ℝ, x k - x i ≠ c • (x j - x i) := by
    intro i j k hij hik hjk c
    exact hgen (x i) (hxV i) (x j) (hxV j) (x k) (hxV k) (fun h => hij (hx h))
      (fun h => hik (hx h)) (fun h => hjk (hx h)) c
  have ratio : ∀ (f g : ℝ³ →ᵃ[ℝ] ℝ) (i j k : Fin 7), i ≠ j → i ≠ k → j ≠ k →
      f (x i) = 0 → f (x j) = 0 → f (x k) = 0 → g (x i) = 0 → g (x j) = 0 → g (x k) = 0 →
      ∀ y w, f w ≠ 0 → g w ≠ 0 → f y / f w = g y / g w := by
    intro f g i j k hij hik hjk fi fj fk gi gj gk y w hfw hgw
    rw [div_eq_div_iff hfw hgw]
    have := vanish3_ratio f g (fun h => hij (hx h)) (ncol i j k hij hik hjk) fi fj fk gi gj gk y w
    linarith
  set QA := ({0, 1, 2, 3} : Finset (Fin 7)).image x
  set QB := ({0, 1, 4, 5} : Finset (Fin 7)).image x
  set QG := ({2, 4, 6} : Finset (Fin 7)).image x
  have sub : ∀ P : Finset (Fin 7), P.image x ⊆ V := fun P => Finset.image_subset_image (Finset.subset_univ P)
  have a0 := (hA 0).1 (by decide); have a2 := (hA 2).1 (by decide); have a3 := (hA 3).1 (by decide)
  have a4 := (hA 4).2 (by decide); have a5 := (hA 5).2 (by decide); have a6 := (hA 6).2 (by decide)
  have b0 := (hB 0).1 (by decide); have b4 := (hB 4).1 (by decide); have b5 := (hB 5).1 (by decide)
  have b2 := (hB 2).2 (by decide); have b3 := (hB 3).2 (by decide); have b6 := (hB 6).2 (by decide)
  have g2 := (hG 2).1 (by decide); have g4 := (hG 4).1 (by decide); have g6 := (hG 6).1 (by decide)
  have g0 := (hG 0).2 (by decide); have g3 := (hG 3).2 (by decide); have g5 := (hG 5).2 (by decide)
  have k4 := (hK 4).1 (by decide); have k5 := (hK 5).1 (by decide); have k6 := (hK 6).1 (by decide)
  have k0 := (hK 0).2 (by decide); have k2 := (hK 2).2 (by decide)
  have h2 := (hH 2).1 (by decide); have h3 := (hH 3).1 (by decide); have h4 := (hH 4).1 (by decide)
  have h0 := (hH 0).2 (by decide); have h6 := (hH 6).2 (by decide)
  -- the frame `x0; x2, x4, x6`
  have hΔ : vol3 (x 2 - x 0) (x 4 - x 0) (x 6 - x 0) ≠ 0 := by
    intro h0'
    have k := affine_vanish3 fG g2 g4 g6 (x 0) (x 2 + crs3 (x 4 - x 2) (x 6 - x 2))
    have pos := vol3_crs3_pos (p := x 2) (q := x 4) (r := x 6) (fun h => by have := hx h; omega)
      (ncol 2 4 6 (by decide) (by decide) (by decide))
    have e : vol3 (x 4 - x 2) (x 6 - x 2) (x 0 - x 2) = -vol3 (x 2 - x 0) (x 4 - x 0) (x 6 - x 0) := by
      simp only [vol3, PiLp.sub_apply]; ring
    rw [add_sub_cancel_left, e, h0', neg_zero, zero_mul] at k
    have := mul_neg_of_pos_of_neg pos g0
    linarith
  have co := fun (f : ℝ³ →ᵃ[ℝ] ℝ) (i : Fin 7) => affine_coord f (x 0) (x 2) (x 4) (x 6) (x i) hΔ
  have cG5 := co fG 5; have cA5 := co fA 5; have cB5 := co fB 5; have cK5 := co fK 5
  have cG3 := co fG 3; have cA3 := co fA 3; have cB3 := co fB 3; have cH3 := co fH 3
  set Δ := vol3 (x 2 - x 0) (x 4 - x 0) (x 6 - x 0)
  set α5 := vol3 (x 5 - x 0) (x 4 - x 0) (x 6 - x 0) / Δ
  set β5 := vol3 (x 2 - x 0) (x 5 - x 0) (x 6 - x 0) / Δ
  set γ5 := vol3 (x 2 - x 0) (x 4 - x 0) (x 5 - x 0) / Δ
  set α3 := vol3 (x 3 - x 0) (x 4 - x 0) (x 6 - x 0) / Δ
  set β3 := vol3 (x 2 - x 0) (x 3 - x 0) (x 6 - x 0) / Δ
  set γ3 := vol3 (x 2 - x 0) (x 4 - x 0) (x 3 - x 0) / Δ
  rw [g2, g4, g6] at cG5 cG3; rw [a0, a2] at cA5; rw [a0, a2, a3] at cA3
  rw [b0, b4, b5] at cB5; rw [b0, b4] at cB3; rw [k4, k5, k6] at cK5; rw [h2, h3, h4] at cH3
  have na4 := a4.ne; have nb2 := b2.ne; have ng0 := g0.ne
  set c := fA (x 6) / fA (x 4) + fB (x 6) / fB (x 2) - 1 with hc
  have hP : fG (x 5) / fG (x 0) + fA (x 5) / fA (x 4) = 1 + γ5 * c := by
    simp only [hc]; field_simp
    linear_combination fA (x 4) * fB (x 2) * cG5 + fG (x 0) * fB (x 2) * cA5 +
      fG (x 0) * fA (x 4) * cB5
  have hQ : fG (x 3) / fG (x 0) + fB (x 3) / fB (x 2) = 1 + γ3 * c := by
    simp only [hc]; field_simp
    linear_combination fB (x 2) * fA (x 4) * cG3 + fG (x 0) * fA (x 4) * cB3 +
      fG (x 0) * fB (x 2) * cA3
  have hσ5 : 0 < 1 - (α5 + β5 + γ5) := by
    have : fG (x 5) = fG (x 0) * (1 - (α5 + β5 + γ5)) := by linear_combination cG5
    nlinarith
  have hα5 : α5 < 0 := by
    have : α5 * fK (x 2) = -(fK (x 0) * (1 - (α5 + β5 + γ5))) := by linear_combination -cK5
    nlinarith
  have hγ5 : 0 < γ5 := by
    have : γ5 * fB (x 6) = -(α5 * fB (x 2)) := by linear_combination -cB5
    nlinarith
  have hσ3 : 0 < 1 - (α3 + β3 + γ3) := by
    have : fG (x 3) = fG (x 0) * (1 - (α3 + β3 + γ3)) := by linear_combination cG3
    nlinarith
  have hγ3 : γ3 < 0 := by
    have : γ3 * fH (x 6) = -(fH (x 0) * (1 - (α3 + β3 + γ3))) := by linear_combination -cH3
    nlinarith
  rcases le_or_gt c 0 with hcl | hcg
  · -- the view `P` along the planes of `0123` and `246`
    refine isRupert_of_facets_vertex_chord V hgen QA QG (sub _) (sub _)
      (isFacet_of_index x _ fA hA) (isFacet_of_index x _ fG hG) (x 2) ?_
      ⟨x 0, (memQ _ 0).mpr (by decide), fun h => by have := hx h; omega⟩
      ⟨x 4, (memQ _ 4).mpr (by decide), fun h => by have := hx h; omega⟩ hT1 (x 0) (x 4)
      ((memQ _ 0).mpr (by decide)) ((memQ _ 4).mpr (by decide))
      (fun h => by have := hx h; omega) (fun h => by have := hx h; omega) (x 5) (hxV 5)
      (by rw [memQ]; decide) (by rw [memQ]; decide) ?_
    · rw [inter, show ({0, 1, 2, 3} ∩ {2, 4, 6} : Finset (Fin 7)) = {2} by decide]
      simp
    intro f1' f2' z1 n1' z2 n2'
    refine ⟨fun y hy hy1 hy2 hne => ?_, ?_⟩
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      rw [memQ] at hy1 hy2
      have hi : i = 5 := by clear * - hy1 hy2; fin_cases i <;> simp_all
      exact absurd (by rw [hi]) hne
    have e2' : f2' (x 5) / f2' (x 0) = fG (x 5) / fG (x 0) :=
      ratio f2' fG 2 4 6 (by decide) (by decide) (by decide)
        (z2 _ ((memQ _ 2).mpr (by decide))) (z2 _ ((memQ _ 4).mpr (by decide)))
        (z2 _ ((memQ _ 6).mpr (by decide))) ((hG 2).1 (by decide)) ((hG 4).1 (by decide))
        ((hG 6).1 (by decide)) _ _ (n2' _ (hxV 0) (by rw [memQ]; decide)).ne
        ((hG 0).2 (by decide)).ne
    have e1' : f1' (x 5) / f1' (x 4) = fA (x 5) / fA (x 4) :=
      ratio f1' fA 0 1 2 (by decide) (by decide) (by decide)
        (z1 _ ((memQ _ 0).mpr (by decide))) (z1 _ ((memQ _ 1).mpr (by decide)))
        (z1 _ ((memQ _ 2).mpr (by decide))) ((hA 0).1 (by decide)) ((hA 1).1 (by decide))
        ((hA 2).1 (by decide)) _ _ (n1' _ (hxV 4) (by rw [memQ]; decide)).ne
        ((hA 4).2 (by decide)).ne
    rw [e1', e2', hP]
    nlinarith

  · -- the view `Q` along the planes of `0145` and `246`
    refine isRupert_of_facets_vertex V hgen QB QG (sub _) (sub _) (isFacet_of_index x _ fB hB)
      (isFacet_of_index x _ fG hG) (x 4) ?_
      ⟨x 0, (memQ _ 0).mpr (by decide), fun h => by have := hx h; omega⟩
      ⟨x 2, (memQ _ 2).mpr (by decide), fun h => by have := hx h; omega⟩ hT2 ?_
    · rw [inter, show ({0, 1, 4, 5} ∩ {2, 4, 6} : Finset (Fin 7)) = {4} by decide]
      simp
    refine ⟨x 0, (memQ _ 0).mpr (by decide), x 2, (memQ _ 2).mpr (by decide),
      fun h => by have := hx h; omega, fun h => by have := hx h; omega, ?_⟩
    intro f1' f2' z1 n1' z2 n2' y hy hy1 hy2
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
    rw [memQ] at hy1 hy2
    have hi : i = 3 := by clear * - hy1 hy2; fin_cases i <;> simp_all
    subst hi
    have e2' : f2' (x 3) / f2' (x 0) = fG (x 3) / fG (x 0) :=
      ratio f2' fG 2 4 6 (by decide) (by decide) (by decide)
        (z2 _ ((memQ _ 2).mpr (by decide))) (z2 _ ((memQ _ 4).mpr (by decide)))
        (z2 _ ((memQ _ 6).mpr (by decide))) ((hG 2).1 (by decide)) ((hG 4).1 (by decide))
        ((hG 6).1 (by decide)) _ _ (n2' _ (hxV 0) (by rw [memQ]; decide)).ne
        ((hG 0).2 (by decide)).ne
    have e1' : f1' (x 3) / f1' (x 2) = fB (x 3) / fB (x 2) :=
      ratio f1' fB 0 1 4 (by decide) (by decide) (by decide)
        (z1 _ ((memQ _ 0).mpr (by decide))) (z1 _ ((memQ _ 1).mpr (by decide)))
        (z1 _ ((memQ _ 4).mpr (by decide))) ((hB 0).1 (by decide)) ((hB 1).1 (by decide))
        ((hB 4).1 (by decide)) _ _ (n1' _ (hxV 2) (by rw [memQ]; decide)).ne
        ((hB 2).2 (by decide)).ne
    rw [e1', e2', hQ]
    have := mul_neg_of_neg_of_pos hγ3 hcg
    linarith

end Minimality

end
