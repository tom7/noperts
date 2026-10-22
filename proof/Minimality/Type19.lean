module

public import Minimality.Type10
public import Minimality.TriTie
public import Minimality.ParallelOr
public import Minimality.TriFacetsChord
public import Minimality.EdgeChord

@[expose] public section

/-!
# Type 19 is Rupert

Theorem F of `FEWER-FACES-PROOFS.md` §7, by the algebraic method of
`Type10.lean`: faces `A = 0235`, `B = 1356` (quadrilaterals), `D = 046`,
`G = 346`; with `s = fB x4 / fB x0 + fA x4 / fA x6`, the view along the edge
`35` has a triangle shadow if `s < 1`, and the view along the line of the
planes of `A` and `D` (through `x0`) has one if `s ≥ 1`: Cramer for `x1` in
the frame `x3; x0, x4, x6` gives
`fD x1 / fD x3 + fA x1 / fA x6 = 1 + ρ (s - 1)` with `ρ < 0` (from `B`, `G`).
At `s = 1` the edge `35` is parallel to the line of the second view (the plane
of `046` is parallel to it, `ParallelEdge.lean`), and the view along `35` has
`x4` on its far side: Lemma T′ over the edge (`isRupert_of_facets_edge_chord`),
given `EdgeFar` along `35` there (`FEWER-FACES-PROOFS.md` §23, item (ii)).
-/

namespace Minimality

open Finset
open scoped RealInnerProductSpace

set_option maxHeartbeats 4000000 in
/-- **Theorem F (type 19).** Seven labelled points, no three collinear, with facets
`0235`, `1356` (quadrilaterals), `046`, `346`, given by functionals negative off
them, are Rupert, given no other segment parallel to `35` and a settled tie of
the far depths there, or at a tie no right angle at the far ends (`EdgeTieR`)
and `TriGenTri` at the line of the planes of `0235` and `046` (at the special
value where the deciding number is 1, `EdgeFar` along `35` instead, for Lemma T′
over that edge). -/
theorem isRupert_type19 (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (hgen : NoThreeCollinear (univ.image x))
    (hsol : (interior (convexHull ℝ ((univ.image x : Finset ℝ³) : Set ℝ³))).Nonempty)
    (fA fB fD fG : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 2, 3, 5} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 2, 3, 5} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({1, 3, 5, 6} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({1, 3, 5, 6} : Finset (Fin 7)) → fB (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 4, 6} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 4, 6} : Finset (Fin 7)) → fD (x i) < 0))
    (hG : ∀ i, (i ∈ ({3, 4, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({3, 4, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hZ1 : EdgeTieR (univ.image x) (({0, 2, 3, 5} : Finset (Fin 7)).image x)
      (({1, 3, 5, 6} : Finset (Fin 7)).image x) (x 3) (x 5) ∨
      EdgeFarP (univ.image x) (({0, 2, 3, 5} : Finset (Fin 7)).image x)
      (({1, 3, 5, 6} : Finset (Fin 7)).image x) (x 3) (x 5))
    (hT2 : (TriGenTri (univ.image x) (({0, 2, 3, 5} : Finset (Fin 7)).image x)
        (({0, 4, 6} : Finset (Fin 7)).image x) (x 0) ∨
      TriGenFarP (univ.image x) (({0, 2, 3, 5} : Finset (Fin 7)).image x)
        (({0, 4, 6} : Finset (Fin 7)).image x) (x 0)) ∧
      (fB (x 4) / fB (x 0) + fA (x 4) / fA (x 6) = 1 →
        EdgeFar (univ.image x) (({0, 2, 3, 5} : Finset (Fin 7)).image x)
          (({1, 3, 5, 6} : Finset (Fin 7)).image x) (x 3) (x 5))) :
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
  set QA := ({0, 2, 3, 5} : Finset (Fin 7)).image x
  set QB := ({1, 3, 5, 6} : Finset (Fin 7)).image x
  set QD := ({0, 4, 6} : Finset (Fin 7)).image x
  have sub : ∀ P : Finset (Fin 7), P.image x ⊆ V := fun P => Finset.image_subset_image (Finset.subset_univ P)
  rcases lt_or_ge (fB (x 4) / fB (x 0) + fA (x 4) / fA (x 6)) 1 with hlt | hgt
  · -- the view along the edge `35`
    refine isRupert_of_facets_edge_tieR_or V hgen QA QB (sub _) (sub _) (isFacet_of_index x _ fA hA)
      (isFacet_of_index x _ fB hB) (x 3) (x 5) (fun h => by have := hx h; omega) ?_
      ⟨x 0, (memQ _ 0).mpr (by decide), by rw [memQ]; decide⟩
      ⟨x 6, (memQ _ 6).mpr (by decide), by rw [memQ]; decide⟩ hZ1 ?_ hsol
    · rw [inter, show ({0, 2, 3, 5} ∩ {1, 3, 5, 6} : Finset (Fin 7)) = {3, 5} by decide]
      simp [Finset.image_insert]
    refine ⟨x 0, (memQ _ 0).mpr (by decide), x 6, (memQ _ 6).mpr (by decide),
      by rw [memQ]; decide, by rw [memQ]; decide, ?_⟩
    intro f1 f2 z1 n1 z2 n2 y hy hy1 hy2
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
    rw [memQ] at hy1 hy2
    have hi : i = 4 := by fin_cases i <;> simp_all
    subst hi
    have e2 : f2 (x 4) / f2 (x 0) = fB (x 4) / fB (x 0) :=
      ratio f2 fB 1 3 6 (by decide) (by decide) (by decide)
        (z2 _ ((memQ _ 1).mpr (by decide))) (z2 _ ((memQ _ 3).mpr (by decide)))
        (z2 _ ((memQ _ 6).mpr (by decide))) ((hB 1).1 (by decide)) ((hB 3).1 (by decide))
        ((hB 6).1 (by decide)) _ _ (n2 _ (hxV 0) (by rw [memQ]; decide)).ne
        ((hB 0).2 (by decide)).ne
    have e1 : f1 (x 4) / f1 (x 6) = fA (x 4) / fA (x 6) :=
      ratio f1 fA 0 2 3 (by decide) (by decide) (by decide)
        (z1 _ ((memQ _ 0).mpr (by decide))) (z1 _ ((memQ _ 2).mpr (by decide)))
        (z1 _ ((memQ _ 3).mpr (by decide))) ((hA 0).1 (by decide)) ((hA 2).1 (by decide))
        ((hA 3).1 (by decide)) _ _ (n1 _ (hxV 6) (by rw [memQ]; decide)).ne
        ((hA 6).2 (by decide)).ne
    rw [e1, e2]; exact hlt
  · -- the view along the line of the planes of `0235` and `046`
    -- Cramer for `x1` in the frame `x3; x0, x4, x6`
    have EA := affine_cramer fA (x 3) (x 0) (x 4) (x 6) (x 1)
    have EB := affine_cramer fB (x 3) (x 0) (x 4) (x 6) (x 1)
    have ED := affine_cramer fD (x 3) (x 0) (x 4) (x 6) (x 1)
    have EG := affine_cramer fG (x 3) (x 0) (x 4) (x 6) (x 1)
    set Δ := vol3 (x 0 - x 3) (x 4 - x 3) (x 6 - x 3)
    set Δ1 := vol3 (x 1 - x 3) (x 4 - x 3) (x 6 - x 3)
    set Δ2 := vol3 (x 0 - x 3) (x 1 - x 3) (x 6 - x 3)
    set Δ3 := vol3 (x 0 - x 3) (x 4 - x 3) (x 1 - x 3)
    have a0 := (hA 0).1 (by decide); have a3 := (hA 3).1 (by decide)
    have a1 := (hA 1).2 (by decide); have a4 := (hA 4).2 (by decide); have a6 := (hA 6).2 (by decide)
    have b1 := (hB 1).1 (by decide); have b3 := (hB 3).1 (by decide); have b6 := (hB 6).1 (by decide)
    have b0 := (hB 0).2 (by decide); have b4 := (hB 4).2 (by decide)
    have d0 := (hD 0).1 (by decide); have d4 := (hD 4).1 (by decide); have d6 := (hD 6).1 (by decide)
    have d1 := (hD 1).2 (by decide); have d3 := (hD 3).2 (by decide)
    have g3 := (hG 3).1 (by decide); have g4 := (hG 4).1 (by decide); have g6 := (hG 6).1 (by decide)
    have g0 := (hG 0).2 (by decide); have g1 := (hG 1).2 (by decide)
    rw [a0, a3] at EA; rw [b1, b3, b6] at EB; rw [d0, d4, d6] at ED; rw [g3, g4, g6] at EG
    -- `Δ ≠ 0`: `x3` is off the plane of `046`
    have hΔ : Δ ≠ 0 := by
      intro h0
      have k := affine_vanish3 fD d0 d4 d6 (x 3) (x 0 + crs3 (x 4 - x 0) (x 6 - x 0))
      have pos := vol3_crs3_pos (p := x 0) (q := x 4) (r := x 6) (fun h => by have := hx h; omega)
        (ncol 0 4 6 (by decide) (by decide) (by decide))
      have e : vol3 (x 4 - x 0) (x 6 - x 0) (x 3 - x 0) = -Δ := by
        simp only [Δ, vol3, PiLp.sub_apply]; ring
      rw [add_sub_cancel_left, e, h0, neg_zero, zero_mul] at k
      have := mul_neg_of_pos_of_neg pos d3
      linarith
    have nd3 := d3.ne; have na6 := a6.ne; have nb0 := b0.ne; have nb4 := b4.ne; have ng0 := g0.ne
    set ρ := Δ2 / Δ
    have hl : ρ = -(fG (x 1) / fG (x 0)) * (fB (x 0) / fB (x 4)) := by
      simp only [ρ]; field_simp; linear_combination (-fG (x 0)) * EB + fB (x 0) * EG
    have hk : fD (x 1) / fD (x 3) + fA (x 1) / fA (x 6) =
        1 + ρ * (fB (x 4) / fB (x 0) + fA (x 4) / fA (x 6) - 1) := by
      simp only [ρ]; field_simp
      linear_combination fA (x 6) * fB (x 0) * ED + fD (x 3) * fB (x 0) * EA +
        fA (x 6) * fD (x 3) * EB
    have hρ : ρ < 0 := by
      rw [hl]
      have p1 : 0 < fG (x 1) / fG (x 0) := div_pos_of_neg_of_neg g1 g0
      have p2 : 0 < fB (x 0) / fB (x 4) := div_pos_of_neg_of_neg b0 b4
      nlinarith
    have hiv : QA ∩ QD = {x 0} := by
      rw [inter, show ({0, 2, 3, 5} ∩ {0, 4, 6} : Finset (Fin 7)) = {0} by decide]
      simp
    rcases hgt.lt_or_eq with hgt' | hgeq
    · -- `s > 1`: the point off both planes strictly inside; Lemma T (the tie allowed)
      refine isRupert_of_facets_vertex_tie_or V hgen QA QD (sub _) (sub _)
        (isFacet_of_index x _ fA hA) (isFacet_of_index x _ fD hD) (x 0) hiv
        ⟨x 3, (memQ _ 3).mpr (by decide), fun h => by have := hx h; omega⟩
        ⟨x 6, (memQ _ 6).mpr (by decide), fun h => by have := hx h; omega⟩
        (hT2.1.imp (fun h => h.tie (sub _) (sub _) hiv
          (Or.inr (by show (({0, 4, 6} : Finset (Fin 7)).image x).card = 3
                      rw [Finset.card_image_of_injective _ hx]; decide))) id)
        ⟨x 3, (memQ _ 3).mpr (by decide), x 6, (memQ _ 6).mpr (by decide),
          fun h => by have := hx h; omega, fun h => by have := hx h; omega, ?_⟩
      intro f1 f2 z1 n1 z2 n2 y hy hy1 hy2
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      rw [memQ] at hy1 hy2
      have hi : i = 1 := by clear * - hy1 hy2; fin_cases i <;> simp_all
      subst hi
      have e2 : f2 (x 1) / f2 (x 3) = fD (x 1) / fD (x 3) :=
        ratio f2 fD 0 4 6 (by decide) (by decide) (by decide)
          (z2 _ ((memQ _ 0).mpr (by decide))) (z2 _ ((memQ _ 4).mpr (by decide)))
          (z2 _ ((memQ _ 6).mpr (by decide))) ((hD 0).1 (by decide)) ((hD 4).1 (by decide))
          ((hD 6).1 (by decide)) _ _ (n2 _ (hxV 3) (by rw [memQ]; decide)).ne
          ((hD 3).2 (by decide)).ne
      have e1 : f1 (x 1) / f1 (x 6) = fA (x 1) / fA (x 6) :=
        ratio f1 fA 0 2 3 (by decide) (by decide) (by decide)
          (z1 _ ((memQ _ 0).mpr (by decide))) (z1 _ ((memQ _ 2).mpr (by decide)))
          (z1 _ ((memQ _ 3).mpr (by decide))) ((hA 0).1 (by decide)) ((hA 2).1 (by decide))
          ((hA 3).1 (by decide)) _ _ (n1 _ (hxV 6) (by rw [memQ]; decide)).ne
          ((hA 6).2 (by decide)).ne
      rw [e1, e2]
      rw [hk]; nlinarith
    · -- `s = 1`: the view along the edge `35` has `x4` on its far side; Lemma T′ over the edge
      refine isRupert_of_facets_edge_chord V hgen QA QB (sub _) (sub _) (isFacet_of_index x _ fA hA)
        (isFacet_of_index x _ fB hB) (x 3) (x 5) (fun h => by have := hx h; omega) ?_
        (hT2.2 hgeq.symm) (x 0) (x 6) ((memQ _ 0).mpr (by decide)) ((memQ _ 6).mpr (by decide))
        (by rw [memQ]; decide) (by rw [memQ]; decide) (x 4) (hxV 4) (by rw [memQ]; decide)
        (by rw [memQ]; decide) ?_
      · rw [inter, show ({0, 2, 3, 5} ∩ {1, 3, 5, 6} : Finset (Fin 7)) = {3, 5} by decide]
        simp [Finset.image_insert]
      intro f1 f2 z1 n1 z2 n2
      have e2 : ∀ k : Fin 7, f2 (x k) / f2 (x 0) = fB (x k) / fB (x 0) := fun k =>
        ratio f2 fB 1 3 5 (by decide) (by decide) (by decide)
          (z2 _ ((memQ _ 1).mpr (by decide))) (z2 _ ((memQ _ 3).mpr (by decide)))
          (z2 _ ((memQ _ 5).mpr (by decide))) ((hB 1).1 (by decide)) ((hB 3).1 (by decide))
          ((hB 5).1 (by decide)) _ _ (n2 _ (hxV 0) (by rw [memQ]; decide)).ne
          ((hB 0).2 (by decide)).ne
      have e1 : ∀ k : Fin 7, f1 (x k) / f1 (x 6) = fA (x k) / fA (x 6) := fun k =>
        ratio f1 fA 0 2 3 (by decide) (by decide) (by decide)
          (z1 _ ((memQ _ 0).mpr (by decide))) (z1 _ ((memQ _ 2).mpr (by decide)))
          (z1 _ ((memQ _ 3).mpr (by decide))) ((hA 0).1 (by decide)) ((hA 2).1 (by decide))
          ((hA 3).1 (by decide)) _ _ (n1 _ (hxV 6) (by rw [memQ]; decide)).ne
          ((hA 6).2 (by decide)).ne
      refine ⟨fun y hy hy1 hy2 hne => ?_, by rw [e1, e2]; exact hgeq.symm.le⟩
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      rw [memQ] at hy1 hy2
      have hi : i = 4 := by clear * - hy1 hy2; fin_cases i <;> simp_all
      exact absurd (by rw [hi]) hne

end Minimality

end
