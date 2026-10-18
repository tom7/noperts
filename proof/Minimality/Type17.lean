module

public import Minimality.Type10
public import Minimality.TriFacetsChord
public import Minimality.TriTie

@[expose] public section

/-!
# Type 17 is Rupert

Theorem H of `FEWER-FACES-PROOFS.md` §7, by the algebraic method of
`Type10.lean`: faces `A = 0246`, `B = 2345` (quadrilaterals), `D = 136`,
`E = 034`; with `s = fB x0 / fB x6 + fD x0 / fD x4`, the view along the line
of the planes of `D` and `B` (through `x3`) has a triangle shadow if `s < 1`
(and `x0` is on its far side if `s = 1`, Lemma T′), and the view along the line
of the planes of `A` and `D` (through `x6`) has one if `s > 1`: Cramer for `x5` in the frame `x4; x0, x3, x6` gives
`fD x5 / fD x4 + fA x5 / fA x3 = 1 + α (s - 1)` with `α < 0` (from `B`, `E`).
-/

namespace Minimality

open Finset
open scoped RealInnerProductSpace

set_option maxHeartbeats 4000000 in
/-- **Theorem H (type 17).** Seven labelled points, no three collinear, with
facets `0246`, `2345` (quadrilaterals), `136`, `034`, given by functionals
negative off them, are Rupert, given `TriGenFar` at the lines of the planes of
`136` and `2345` and of `0246` and `136`. -/
theorem isRupert_type17 (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (hgen : NoThreeCollinear (univ.image x)) (fA fB fD fE : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 2, 4, 6} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 2, 4, 6} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({2, 3, 4, 5} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({2, 3, 4, 5} : Finset (Fin 7)) → fB (x i) < 0))
    (hD : ∀ i, (i ∈ ({1, 3, 6} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({1, 3, 6} : Finset (Fin 7)) → fD (x i) < 0))
    (hE : ∀ i, (i ∈ ({0, 3, 4} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({0, 3, 4} : Finset (Fin 7)) → fE (x i) < 0))
    (hT1 : TriGenTri (univ.image x) (({1, 3, 6} : Finset (Fin 7)).image x)
        (({2, 3, 4, 5} : Finset (Fin 7)).image x) (x 3) ∧
      (fB (x 0) / fB (x 6) + fD (x 0) / fD (x 4) = 1 →
        TriGenFar (univ.image x) (({1, 3, 6} : Finset (Fin 7)).image x)
          (({2, 3, 4, 5} : Finset (Fin 7)).image x) (x 3)))
    (hT2 : TriGenTri (univ.image x) (({0, 2, 4, 6} : Finset (Fin 7)).image x)
      (({1, 3, 6} : Finset (Fin 7)).image x) (x 6)) :
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
  set QA := ({0, 2, 4, 6} : Finset (Fin 7)).image x
  set QB := ({2, 3, 4, 5} : Finset (Fin 7)).image x
  set QD := ({1, 3, 6} : Finset (Fin 7)).image x
  have sub : ∀ P : Finset (Fin 7), P.image x ⊆ V := fun P => Finset.image_subset_image (Finset.subset_univ P)
  have hiP : QD ∩ QB = {x 3} := by
    rw [inter, show ({1, 3, 6} ∩ {2, 3, 4, 5} : Finset (Fin 7)) = {3} by decide]
    simp
  rcases le_or_gt (fB (x 0) / fB (x 6) + fD (x 0) / fD (x 4)) 1 with hle | hgt
  · rcases hle.lt_or_eq with hlt | heq
    · -- `s < 1`: the plain view along the planes of `136` and `2345`, the tie allowed
      refine isRupert_of_facets_vertex_tie V hgen QD QB (sub _) (sub _)
        (isFacet_of_index x _ fD hD) (isFacet_of_index x _ fB hB) (x 3) hiP
        ⟨x 6, (memQ _ 6).mpr (by decide), fun h => by have := hx h; omega⟩
        ⟨x 4, (memQ _ 4).mpr (by decide), fun h => by have := hx h; omega⟩
        (hT1.1.tie (sub _) (sub _) hiP
          (Or.inl (by show (({1, 3, 6} : Finset (Fin 7)).image x).card = 3
                      rw [Finset.card_image_of_injective _ hx]; decide)))
        ⟨x 6, (memQ _ 6).mpr (by decide), x 4, (memQ _ 4).mpr (by decide),
          fun h => by have := hx h; omega, fun h => by have := hx h; omega, ?_⟩
      intro f1 f2 z1 n1 z2 n2 y hy hy1 hy2
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      rw [memQ] at hy1 hy2
      have hi : i = 0 := by clear * - hy1 hy2; fin_cases i <;> simp_all
      subst hi
      have e2 : f2 (x 0) / f2 (x 6) = fB (x 0) / fB (x 6) :=
        ratio f2 fB 2 3 4 (by decide) (by decide) (by decide)
          (z2 _ ((memQ _ 2).mpr (by decide))) (z2 _ ((memQ _ 3).mpr (by decide)))
          (z2 _ ((memQ _ 4).mpr (by decide))) ((hB 2).1 (by decide)) ((hB 3).1 (by decide))
          ((hB 4).1 (by decide)) _ _ (n2 _ (hxV 6) (by rw [memQ]; decide)).ne
          ((hB 6).2 (by decide)).ne
      have e1 : f1 (x 0) / f1 (x 4) = fD (x 0) / fD (x 4) :=
        ratio f1 fD 1 3 6 (by decide) (by decide) (by decide)
          (z1 _ ((memQ _ 1).mpr (by decide))) (z1 _ ((memQ _ 3).mpr (by decide)))
          (z1 _ ((memQ _ 6).mpr (by decide))) ((hD 1).1 (by decide)) ((hD 3).1 (by decide))
          ((hD 6).1 (by decide)) _ _ (n1 _ (hxV 4) (by rw [memQ]; decide)).ne
          ((hD 4).2 (by decide)).ne
      rw [e1, e2]; exact hlt
    · -- `s = 1`: Lemma T′ (`x0` on the far side)
      refine isRupert_of_facets_vertex_chord V hgen QD QB (sub _) (sub _)
        (isFacet_of_index x _ fD hD) (isFacet_of_index x _ fB hB) (x 3) hiP
        ⟨x 6, (memQ _ 6).mpr (by decide), fun h => by have := hx h; omega⟩
        ⟨x 4, (memQ _ 4).mpr (by decide), fun h => by have := hx h; omega⟩ (hT1.2 heq) (x 6) (x 4)
        ((memQ _ 6).mpr (by decide)) ((memQ _ 4).mpr (by decide))
        (fun h => by have := hx h; omega) (fun h => by have := hx h; omega) (x 0) (hxV 0)
        (by rw [memQ]; decide) (by rw [memQ]; decide) ?_
      intro f1 f2 z1 n1 z2 n2
      refine ⟨fun y hy hy1 hy2 hne => ?_, ?_⟩
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
        rw [memQ] at hy1 hy2
        have hi : i = 0 := by clear * - hy1 hy2; fin_cases i <;> simp_all
        exact absurd (by rw [hi]) hne
      have e2 : f2 (x 0) / f2 (x 6) = fB (x 0) / fB (x 6) :=
        ratio f2 fB 2 3 4 (by decide) (by decide) (by decide)
          (z2 _ ((memQ _ 2).mpr (by decide))) (z2 _ ((memQ _ 3).mpr (by decide)))
          (z2 _ ((memQ _ 4).mpr (by decide))) ((hB 2).1 (by decide)) ((hB 3).1 (by decide))
          ((hB 4).1 (by decide)) _ _ (n2 _ (hxV 6) (by rw [memQ]; decide)).ne
          ((hB 6).2 (by decide)).ne
      have e1 : f1 (x 0) / f1 (x 4) = fD (x 0) / fD (x 4) :=
        ratio f1 fD 1 3 6 (by decide) (by decide) (by decide)
          (z1 _ ((memQ _ 1).mpr (by decide))) (z1 _ ((memQ _ 3).mpr (by decide)))
          (z1 _ ((memQ _ 6).mpr (by decide))) ((hD 1).1 (by decide)) ((hD 3).1 (by decide))
          ((hD 6).1 (by decide)) _ _ (n1 _ (hxV 4) (by rw [memQ]; decide)).ne
          ((hD 4).2 (by decide)).ne
      rw [e1, e2]; exact heq.le
  · -- the view along the line of the planes of `0246` and `136`
    have hivhT2 : QA ∩ QD = {x 6} := by
      rw [inter, show ({0, 2, 4, 6} ∩ {1, 3, 6} : Finset (Fin 7)) = {6} by decide]
      simp
    refine isRupert_of_facets_vertex_tie V hgen QA QD (sub _) (sub _) (isFacet_of_index x _ fA hA)
      (isFacet_of_index x _ fD hD) (x 6) hivhT2
      ⟨x 4, (memQ _ 4).mpr (by decide), fun h => by have := hx h; omega⟩
      ⟨x 3, (memQ _ 3).mpr (by decide), fun h => by have := hx h; omega⟩
      (hT2.tie (sub _) (sub _) hivhT2
        (Or.inr (by show (({1, 3, 6} : Finset (Fin 7)).image x).card = 3; rw [Finset.card_image_of_injective _ hx]; decide))) ?_
    refine ⟨x 4, (memQ _ 4).mpr (by decide), x 3, (memQ _ 3).mpr (by decide),
      fun h => by have := hx h; omega, fun h => by have := hx h; omega, ?_⟩
    intro f1 f2 z1 n1 z2 n2 y hy hy1 hy2
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
    rw [memQ] at hy1 hy2
    have hi : i = 5 := by fin_cases i <;> simp_all
    subst hi
    have e2 : f2 (x 5) / f2 (x 4) = fD (x 5) / fD (x 4) :=
      ratio f2 fD 1 3 6 (by decide) (by decide) (by decide)
        (z2 _ ((memQ _ 1).mpr (by decide))) (z2 _ ((memQ _ 3).mpr (by decide)))
        (z2 _ ((memQ _ 6).mpr (by decide))) ((hD 1).1 (by decide)) ((hD 3).1 (by decide))
        ((hD 6).1 (by decide)) _ _ (n2 _ (hxV 4) (by rw [memQ]; decide)).ne
        ((hD 4).2 (by decide)).ne
    have e1 : f1 (x 5) / f1 (x 3) = fA (x 5) / fA (x 3) :=
      ratio f1 fA 0 2 4 (by decide) (by decide) (by decide)
        (z1 _ ((memQ _ 0).mpr (by decide))) (z1 _ ((memQ _ 2).mpr (by decide)))
        (z1 _ ((memQ _ 4).mpr (by decide))) ((hA 0).1 (by decide)) ((hA 2).1 (by decide))
        ((hA 4).1 (by decide)) _ _ (n1 _ (hxV 3) (by rw [memQ]; decide)).ne
        ((hA 3).2 (by decide)).ne
    rw [e1, e2]
    -- Cramer for `x5` in the frame `x4; x0, x3, x6`
    have EA := affine_cramer fA (x 4) (x 0) (x 3) (x 6) (x 5)
    have EB := affine_cramer fB (x 4) (x 0) (x 3) (x 6) (x 5)
    have ED := affine_cramer fD (x 4) (x 0) (x 3) (x 6) (x 5)
    have EE := affine_cramer fE (x 4) (x 0) (x 3) (x 6) (x 5)
    set Δ := vol3 (x 0 - x 4) (x 3 - x 4) (x 6 - x 4)
    set Δ1 := vol3 (x 5 - x 4) (x 3 - x 4) (x 6 - x 4)
    set Δ2 := vol3 (x 0 - x 4) (x 5 - x 4) (x 6 - x 4)
    set Δ3 := vol3 (x 0 - x 4) (x 3 - x 4) (x 5 - x 4)
    have a0 := (hA 0).1 (by decide); have a4 := (hA 4).1 (by decide); have a6 := (hA 6).1 (by decide)
    have a3 := (hA 3).2 (by decide); have a5 := (hA 5).2 (by decide)
    have b3 := (hB 3).1 (by decide); have b4 := (hB 4).1 (by decide); have b5 := (hB 5).1 (by decide)
    have b0 := (hB 0).2 (by decide); have b6 := (hB 6).2 (by decide)
    have d3 := (hD 3).1 (by decide); have d6 := (hD 6).1 (by decide)
    have d0 := (hD 0).2 (by decide); have d4 := (hD 4).2 (by decide); have d5 := (hD 5).2 (by decide)
    have e0 := (hE 0).1 (by decide); have e3 := (hE 3).1 (by decide); have e4 := (hE 4).1 (by decide)
    have e5 := (hE 5).2 (by decide); have e6 := (hE 6).2 (by decide)
    rw [a0, a4, a6] at EA; rw [b3, b4, b5] at EB; rw [d3, d6] at ED; rw [e0, e3, e4] at EE
    -- `Δ ≠ 0`: `x6` is off the plane of `034`
    have hΔ : Δ ≠ 0 := by
      intro h0
      have k := affine_vanish3 fE e4 e0 e3 (x 6) (x 4 + crs3 (x 0 - x 4) (x 3 - x 4))
      have pos := vol3_crs3_pos (p := x 4) (q := x 0) (r := x 3) (fun h => by have := hx h; omega)
        (ncol 4 0 3 (by decide) (by decide) (by decide))
      rw [add_sub_cancel_left] at k
      change _ * fE (x 6) = Δ * _ at k
      rw [h0, zero_mul] at k
      have := mul_neg_of_pos_of_neg pos e6
      linarith
    have nd4 := d4.ne; have na3 := a3.ne; have nb0 := b0.ne; have nb6 := b6.ne; have ne6 := e6.ne
    set r := Δ1 / Δ
    have hl : r = -(fE (x 5) / fE (x 6)) * (fB (x 6) / fB (x 0)) := by
      simp only [r]; field_simp; linear_combination -fE (x 6) * EB + fB (x 6) * EE
    have hk : fD (x 5) / fD (x 4) + fA (x 5) / fA (x 3) =
        1 + r * (fB (x 0) / fB (x 6) + fD (x 0) / fD (x 4) - 1) := by
      simp only [r]; field_simp
      linear_combination fA (x 3) * fB (x 6) * ED + fD (x 4) * fB (x 6) * EA +
        fA (x 3) * fD (x 4) * EB
    have hr : r < 0 := by
      rw [hl]
      have p1 : 0 < fE (x 5) / fE (x 6) := div_pos_of_neg_of_neg e5 e6
      have p2 : 0 < fB (x 6) / fB (x 0) := div_pos_of_neg_of_neg b6 b0
      nlinarith
    rw [hk]; nlinarith

end Minimality

end
