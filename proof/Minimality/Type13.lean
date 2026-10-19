module

public import Minimality.Type10
public import Minimality.TriTie
public import Minimality.TriFacetsChord

@[expose] public section

/-!
# Type 13 is Rupert

Theorem G of `FEWER-FACES-PROOFS.md` §7, by the algebraic method of
`Type10.lean`: faces `A = 0145`, `B = 2456` (quadrilaterals), `D = 123`,
`G = 126`; with `s = fB x3 / fB x1 + fA x3 / fA x2`, the view along the edge
`45` has a triangle shadow if `s < 1`, and the view along the line of the
planes of `A` and `D` (through `x1`) has one if `s ≥ 1`: with
`x3 - x6 = α (x1 - x6) + β (x2 - x6) + γ (x5 - x6)` (Cramer) and
`σ = α + β + γ`, `t - 1 = (1 - s) / (σ - 1)` for
`t = fD x6 / fD x5 + fA x6 / fA x2`, and `σ > 1` (from `D` and `G`).
At `s = 1` the only point `x6` off both planes of the second view is on the far
side, and that view works by Lemma T′ (`isRupert_of_facets_vertex_chord`).
-/

namespace Minimality

open Finset
open scoped RealInnerProductSpace

set_option maxHeartbeats 4000000 in
/-- **Theorem G (type 13).** Seven labelled points, no three collinear, with facets
`0145`, `2456` (quadrilaterals), `123`, `126`, given by functionals negative off
them, are Rupert, given no other segment parallel to `45` and a settled tie of
the far depths there (`EdgeTie`) and `TriGenTri` at the line of the planes of
`0145` and `123` (`TriGenFar` there only where the deciding number is 1, at
Lemma T′). -/
theorem isRupert_type13 (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (hgen : NoThreeCollinear (univ.image x)) (fA fB fD fG : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 1, 4, 5} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 1, 4, 5} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({2, 4, 5, 6} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({2, 4, 5, 6} : Finset (Fin 7)) → fB (x i) < 0))
    (hD : ∀ i, (i ∈ ({1, 2, 3} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({1, 2, 3} : Finset (Fin 7)) → fD (x i) < 0))
    (hG : ∀ i, (i ∈ ({1, 2, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({1, 2, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hZ1 : EdgeTie (univ.image x) (({0, 1, 4, 5} : Finset (Fin 7)).image x)
      (({2, 4, 5, 6} : Finset (Fin 7)).image x) (x 4) (x 5))
    (hT2 : TriGenTri (univ.image x) (({0, 1, 4, 5} : Finset (Fin 7)).image x)
        (({1, 2, 3} : Finset (Fin 7)).image x) (x 1) ∧
      (fB (x 3) / fB (x 1) + fA (x 3) / fA (x 2) = 1 →
        TriGenFar (univ.image x) (({0, 1, 4, 5} : Finset (Fin 7)).image x)
          (({1, 2, 3} : Finset (Fin 7)).image x) (x 1))) :
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
  set QA := ({0, 1, 4, 5} : Finset (Fin 7)).image x
  set QB := ({2, 4, 5, 6} : Finset (Fin 7)).image x
  set QD := ({1, 2, 3} : Finset (Fin 7)).image x
  have sub : ∀ P : Finset (Fin 7), P.image x ⊆ V := fun P => Finset.image_subset_image (Finset.subset_univ P)
  rcases lt_or_ge (fB (x 3) / fB (x 1) + fA (x 3) / fA (x 2)) 1 with hlt | hgt
  · -- the view along the edge `45`
    refine isRupert_of_facets_edge_tie V hgen QA QB (sub _) (sub _) (isFacet_of_index x _ fA hA)
      (isFacet_of_index x _ fB hB) (x 4) (x 5) (fun h => by have := hx h; omega) ?_
      ⟨x 1, (memQ _ 1).mpr (by decide), by rw [memQ]; decide⟩
      ⟨x 2, (memQ _ 2).mpr (by decide), by rw [memQ]; decide⟩ hZ1 ?_
    · rw [inter, show ({0, 1, 4, 5} ∩ {2, 4, 5, 6} : Finset (Fin 7)) = {4, 5} by decide]
      simp [Finset.image_insert]
    refine ⟨x 1, (memQ _ 1).mpr (by decide), x 2, (memQ _ 2).mpr (by decide),
      by rw [memQ]; decide, by rw [memQ]; decide, ?_⟩
    intro f1 f2 z1 n1 z2 n2 y hy hy1 hy2
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
    rw [memQ] at hy1 hy2
    have hi : i = 3 := by fin_cases i <;> simp_all
    subst hi
    have e2 : f2 (x 3) / f2 (x 1) = fB (x 3) / fB (x 1) :=
      ratio f2 fB 2 4 5 (by decide) (by decide) (by decide)
        (z2 _ ((memQ _ 2).mpr (by decide))) (z2 _ ((memQ _ 4).mpr (by decide)))
        (z2 _ ((memQ _ 5).mpr (by decide))) ((hB 2).1 (by decide)) ((hB 4).1 (by decide))
        ((hB 5).1 (by decide)) _ _ (n2 _ (hxV 1) (by rw [memQ]; decide)).ne
        ((hB 1).2 (by decide)).ne
    have e1 : f1 (x 3) / f1 (x 2) = fA (x 3) / fA (x 2) :=
      ratio f1 fA 0 1 4 (by decide) (by decide) (by decide)
        (z1 _ ((memQ _ 0).mpr (by decide))) (z1 _ ((memQ _ 1).mpr (by decide)))
        (z1 _ ((memQ _ 4).mpr (by decide))) ((hA 0).1 (by decide)) ((hA 1).1 (by decide))
        ((hA 4).1 (by decide)) _ _ (n1 _ (hxV 2) (by rw [memQ]; decide)).ne
        ((hA 2).2 (by decide)).ne
    rw [e1, e2]; exact hlt
  · -- the view along the line of the planes of `0145` and `123`
    -- Cramer for `x3` in the frame `x6; x1, x2, x5`
    have EA := affine_cramer fA (x 6) (x 1) (x 2) (x 5) (x 3)
    have EB := affine_cramer fB (x 6) (x 1) (x 2) (x 5) (x 3)
    have ED := affine_cramer fD (x 6) (x 1) (x 2) (x 5) (x 3)
    have EG := affine_cramer fG (x 6) (x 1) (x 2) (x 5) (x 3)
    set Δ := vol3 (x 1 - x 6) (x 2 - x 6) (x 5 - x 6)
    set Δ1 := vol3 (x 3 - x 6) (x 2 - x 6) (x 5 - x 6)
    set Δ2 := vol3 (x 1 - x 6) (x 3 - x 6) (x 5 - x 6)
    set Δ3 := vol3 (x 1 - x 6) (x 2 - x 6) (x 3 - x 6)
    have a1 := (hA 1).1 (by decide); have a5 := (hA 5).1 (by decide)
    have a2 := (hA 2).2 (by decide); have a3 := (hA 3).2 (by decide); have a6 := (hA 6).2 (by decide)
    have b2 := (hB 2).1 (by decide); have b5 := (hB 5).1 (by decide); have b6 := (hB 6).1 (by decide)
    have b1 := (hB 1).2 (by decide); have b3 := (hB 3).2 (by decide)
    have d1 := (hD 1).1 (by decide); have d2 := (hD 2).1 (by decide); have d3 := (hD 3).1 (by decide)
    have d5 := (hD 5).2 (by decide); have d6 := (hD 6).2 (by decide)
    have g1 := (hG 1).1 (by decide); have g2 := (hG 2).1 (by decide); have g6 := (hG 6).1 (by decide)
    have g3 := (hG 3).2 (by decide); have g5 := (hG 5).2 (by decide)
    rw [a1, a5] at EA; rw [b2, b5, b6] at EB; rw [d1, d2, d3] at ED; rw [g1, g2, g6] at EG
    -- `Δ ≠ 0`: `x5` is off the plane of `126`
    have hΔ : Δ ≠ 0 := by
      intro h0
      have k := affine_vanish3 fG g6 g1 g2 (x 5) (x 6 + crs3 (x 1 - x 6) (x 2 - x 6))
      have pos := vol3_crs3_pos (p := x 6) (q := x 1) (r := x 2) (fun h => by have := hx h; omega)
        (ncol 6 1 2 (by decide) (by decide) (by decide))
      rw [add_sub_cancel_left] at k
      change _ * fG (x 5) = Δ * _ at k
      rw [h0, zero_mul] at k
      have := mul_neg_of_pos_of_neg pos g5
      linarith
    have eD : (Δ1 + Δ2 + Δ3 - Δ) * fD (x 6) - Δ3 * fD (x 5) = 0 := by linear_combination ED
    have eA : (Δ1 + Δ2 + Δ3 - Δ) * fA (x 6) - Δ2 * fA (x 2) + Δ * fA (x 3) = 0 := by
      linear_combination EA
    have eB : fB (x 3) * Δ - Δ1 * fB (x 1) = 0 := by linear_combination EB
    have eG : Δ * fG (x 3) = Δ3 * fG (x 5) := by linear_combination EG
    have nd5 := d5.ne; have nd6 := d6.ne; have na2 := a2.ne; have nb1 := b1.ne; have ng5 := g5.ne
    set u := (Δ1 + Δ2 + Δ3 - Δ) / Δ
    have hu : u = fG (x 3) / fG (x 5) * (fD (x 5) / fD (x 6)) := by
      simp only [u]; field_simp; linear_combination fG (x 5) * eD - fD (x 5) * eG
    have hu0 : 0 < u := by
      rw [hu]; exact mul_pos (div_pos_of_neg_of_neg g3 g5) (div_pos_of_neg_of_neg d5 d6)
    have hk : (fD (x 6) / fD (x 5) + fA (x 6) / fA (x 2) - 1) * u =
        1 - (fB (x 3) / fB (x 1) + fA (x 3) / fA (x 2)) := by
      simp only [u]; field_simp
      linear_combination fB (x 1) * fA (x 2) * eD + fB (x 1) * fD (x 5) * eA +
        fA (x 2) * fD (x 5) * eB
    have hiv : QA ∩ QD = {x 1} := by
      rw [inter, show ({0, 1, 4, 5} ∩ {1, 2, 3} : Finset (Fin 7)) = {1} by decide]
      simp
    rcases hgt.lt_or_eq with hgt' | hgeq
    · -- `s > 1`: the point off both planes strictly inside; Lemma T (the tie allowed)
      refine isRupert_of_facets_vertex_tie V hgen QA QD (sub _) (sub _)
        (isFacet_of_index x _ fA hA) (isFacet_of_index x _ fD hD) (x 1) hiv
        ⟨x 5, (memQ _ 5).mpr (by decide), fun h => by have := hx h; omega⟩
        ⟨x 2, (memQ _ 2).mpr (by decide), fun h => by have := hx h; omega⟩
        (hT2.1.tie (sub _) (sub _) hiv
          (Or.inr (by show (({1, 2, 3} : Finset (Fin 7)).image x).card = 3
                      rw [Finset.card_image_of_injective _ hx]; decide)))
        ⟨x 5, (memQ _ 5).mpr (by decide), x 2, (memQ _ 2).mpr (by decide),
          fun h => by have := hx h; omega, fun h => by have := hx h; omega, ?_⟩
      intro f1 f2 z1 n1 z2 n2 y hy hy1 hy2
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      rw [memQ] at hy1 hy2
      have hi : i = 6 := by clear * - hy1 hy2; fin_cases i <;> simp_all
      subst hi
      have e2 : f2 (x 6) / f2 (x 5) = fD (x 6) / fD (x 5) :=
        ratio f2 fD 1 2 3 (by decide) (by decide) (by decide)
          (z2 _ ((memQ _ 1).mpr (by decide))) (z2 _ ((memQ _ 2).mpr (by decide)))
          (z2 _ ((memQ _ 3).mpr (by decide))) ((hD 1).1 (by decide)) ((hD 2).1 (by decide))
          ((hD 3).1 (by decide)) _ _ (n2 _ (hxV 5) (by rw [memQ]; decide)).ne
          ((hD 5).2 (by decide)).ne
      have e1 : f1 (x 6) / f1 (x 2) = fA (x 6) / fA (x 2) :=
        ratio f1 fA 0 1 4 (by decide) (by decide) (by decide)
          (z1 _ ((memQ _ 0).mpr (by decide))) (z1 _ ((memQ _ 1).mpr (by decide)))
          (z1 _ ((memQ _ 4).mpr (by decide))) ((hA 0).1 (by decide)) ((hA 1).1 (by decide))
          ((hA 4).1 (by decide)) _ _ (n1 _ (hxV 2) (by rw [memQ]; decide)).ne
          ((hA 2).2 (by decide)).ne
      rw [e1, e2]
      nlinarith
    · -- `s = 1`: that point on the far side; Lemma T′
      refine isRupert_of_facets_vertex_chord V hgen QA QD (sub _) (sub _)
        (isFacet_of_index x _ fA hA) (isFacet_of_index x _ fD hD) (x 1) hiv
        ⟨x 5, (memQ _ 5).mpr (by decide), fun h => by have := hx h; omega⟩
        ⟨x 2, (memQ _ 2).mpr (by decide), fun h => by have := hx h; omega⟩
        (hT2.2 hgeq.symm) (x 5) (x 2)
        ((memQ _ 5).mpr (by decide)) ((memQ _ 2).mpr (by decide))
        (fun h => by have := hx h; omega) (fun h => by have := hx h; omega) (x 6) (hxV 6)
        (by rw [memQ]; decide) (by rw [memQ]; decide) ?_
      intro f1 f2 z1 n1 z2 n2
      refine ⟨fun y hy hy1 hy2 hne => ?_, ?_⟩
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
        rw [memQ] at hy1 hy2
        have hi : i = 6 := by clear * - hy1 hy2; fin_cases i <;> simp_all
        exact absurd (by rw [hi]) hne
      have e2 : f2 (x 6) / f2 (x 5) = fD (x 6) / fD (x 5) :=
        ratio f2 fD 1 2 3 (by decide) (by decide) (by decide)
          (z2 _ ((memQ _ 1).mpr (by decide))) (z2 _ ((memQ _ 2).mpr (by decide)))
          (z2 _ ((memQ _ 3).mpr (by decide))) ((hD 1).1 (by decide)) ((hD 2).1 (by decide))
          ((hD 3).1 (by decide)) _ _ (n2 _ (hxV 5) (by rw [memQ]; decide)).ne
          ((hD 5).2 (by decide)).ne
      have e1 : f1 (x 6) / f1 (x 2) = fA (x 6) / fA (x 2) :=
        ratio f1 fA 0 1 4 (by decide) (by decide) (by decide)
          (z1 _ ((memQ _ 0).mpr (by decide))) (z1 _ ((memQ _ 1).mpr (by decide)))
          (z1 _ ((memQ _ 4).mpr (by decide))) ((hA 0).1 (by decide)) ((hA 1).1 (by decide))
          ((hA 4).1 (by decide)) _ _ (n1 _ (hxV 2) (by rw [memQ]; decide)).ne
          ((hA 2).2 (by decide)).ne
      rw [e1, e2]
      nlinarith

end Minimality

end
