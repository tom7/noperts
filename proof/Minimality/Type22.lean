module

public import Minimality.Type10
public import Minimality.TriFacetsChord
public import Minimality.TriTie

@[expose] public section

/-!
# Type 22 is Rupert

Theorem N of `FEWER-FACES-PROOFS.md` §7, by the algebraic method of
`Type10.lean`. Faces `A = 0134` (a quadrilateral), `D = 125`, `G = 246`,
`N = 146`, `I = 256` (and others). View `P` along the line of the planes of `D`
and `G` (through `x2`), view `Q` along that of `A` and `G` (through `x4`). In the
frame `x4; x1, x2, x6`, with `c = fA x6 / fA x2 + fD x6 / fD x4 - 1`, the values
are `1 + γ_y c` (`P`, `y = 0, 3`) and `1 + γ5 c` (`Q`), with `γ_y < 0 < γ5`.
At `c = 0` the only point `x5` off both planes of `Q` is on the far side, and
`Q` works by Lemma T′ (`isRupert_of_facets_vertex_chord`).
-/

namespace Minimality

open Finset
open scoped RealInnerProductSpace

set_option maxHeartbeats 8000000 in
/-- **Theorem N (type 22).** Seven labelled points, no three collinear, with facets
`0134` (a quadrilateral), `125`, `246`, `146`, `256`, given by functionals
negative off them, are Rupert, given `TriGenFar` at the lines of the planes of
`125` and `246` and of `0134` and `246`. -/
theorem isRupert_type22 (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (hgen : NoThreeCollinear (univ.image x)) (fA fD fG fN fI : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 1, 3, 4} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 1, 3, 4} : Finset (Fin 7)) → fA (x i) < 0))
    (hD : ∀ i, (i ∈ ({1, 2, 5} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({1, 2, 5} : Finset (Fin 7)) → fD (x i) < 0))
    (hG : ∀ i, (i ∈ ({2, 4, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({2, 4, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hN : ∀ i, (i ∈ ({1, 4, 6} : Finset (Fin 7)) → fN (x i) = 0) ∧
      (i ∉ ({1, 4, 6} : Finset (Fin 7)) → fN (x i) < 0))
    (hI : ∀ i, (i ∈ ({2, 5, 6} : Finset (Fin 7)) → fI (x i) = 0) ∧
      (i ∉ ({2, 5, 6} : Finset (Fin 7)) → fI (x i) < 0))
    (hT1 : TriGenTri (univ.image x) (({1, 2, 5} : Finset (Fin 7)).image x)
      (({2, 4, 6} : Finset (Fin 7)).image x) (x 2))
    (hT2 : TriGenTri (univ.image x) (({0, 1, 3, 4} : Finset (Fin 7)).image x)
        (({2, 4, 6} : Finset (Fin 7)).image x) (x 4) ∧
      (fG (x 5) / fG (x 1) + fA (x 5) / fA (x 2) = 1 →
        TriGenFar (univ.image x) (({0, 1, 3, 4} : Finset (Fin 7)).image x)
          (({2, 4, 6} : Finset (Fin 7)).image x) (x 4))) :
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
  set QA := ({0, 1, 3, 4} : Finset (Fin 7)).image x
  set QD := ({1, 2, 5} : Finset (Fin 7)).image x
  set QG := ({2, 4, 6} : Finset (Fin 7)).image x
  have sub : ∀ P : Finset (Fin 7), P.image x ⊆ V := fun P => Finset.image_subset_image (Finset.subset_univ P)
  have a0 := (hA 0).1 (by decide); have a1 := (hA 1).1 (by decide); have a3 := (hA 3).1 (by decide)
  have a4 := (hA 4).1 (by decide); have a2 := (hA 2).2 (by decide); have a5 := (hA 5).2 (by decide)
  have a6 := (hA 6).2 (by decide)
  have d1 := (hD 1).1 (by decide); have d2 := (hD 2).1 (by decide); have d5 := (hD 5).1 (by decide)
  have d0 := (hD 0).2 (by decide); have d3 := (hD 3).2 (by decide); have d4 := (hD 4).2 (by decide)
  have d6 := (hD 6).2 (by decide)
  have g2 := (hG 2).1 (by decide); have g4 := (hG 4).1 (by decide); have g6 := (hG 6).1 (by decide)
  have g0 := (hG 0).2 (by decide); have g1 := (hG 1).2 (by decide); have g3 := (hG 3).2 (by decide)
  have g5 := (hG 5).2 (by decide)
  have n1 := (hN 1).1 (by decide); have n4 := (hN 4).1 (by decide); have n6 := (hN 6).1 (by decide)
  have n0 := (hN 0).2 (by decide); have n2 := (hN 2).2 (by decide); have n3 := (hN 3).2 (by decide)
  have i2 := (hI 2).1 (by decide); have i5 := (hI 5).1 (by decide); have i6 := (hI 6).1 (by decide)
  have i1 := (hI 1).2 (by decide); have i4 := (hI 4).2 (by decide)
  -- the frame `x4; x1, x2, x6`
  have hΔ : vol3 (x 1 - x 4) (x 2 - x 4) (x 6 - x 4) ≠ 0 := by
    intro h0'
    have k := affine_vanish3 fG g4 g2 g6 (x 1) (x 4 + crs3 (x 2 - x 4) (x 6 - x 4))
    have pos := vol3_crs3_pos (p := x 4) (q := x 2) (r := x 6) (fun h => by have := hx h; omega)
      (ncol 4 2 6 (by decide) (by decide) (by decide))
    have e : vol3 (x 2 - x 4) (x 6 - x 4) (x 1 - x 4) = vol3 (x 1 - x 4) (x 2 - x 4) (x 6 - x 4) := by
      simp only [vol3, PiLp.sub_apply]; ring
    rw [add_sub_cancel_left, e, h0', zero_mul] at k
    have := mul_neg_of_pos_of_neg pos g1
    linarith
  have co := fun (f : ℝ³ →ᵃ[ℝ] ℝ) (i : Fin 7) => affine_coord f (x 4) (x 1) (x 2) (x 6) (x i) hΔ
  have cG0 := co fG 0; have cD0 := co fD 0; have cA0 := co fA 0; have cN0 := co fN 0
  have cG3 := co fG 3; have cD3 := co fD 3; have cA3 := co fA 3; have cN3 := co fN 3
  have cG5 := co fG 5; have cD5 := co fD 5; have cA5 := co fA 5; have cI5 := co fI 5
  set Δ := vol3 (x 1 - x 4) (x 2 - x 4) (x 6 - x 4)
  set α0 := vol3 (x 0 - x 4) (x 2 - x 4) (x 6 - x 4) / Δ
  set β0 := vol3 (x 1 - x 4) (x 0 - x 4) (x 6 - x 4) / Δ
  set γ0 := vol3 (x 1 - x 4) (x 2 - x 4) (x 0 - x 4) / Δ
  set α3 := vol3 (x 3 - x 4) (x 2 - x 4) (x 6 - x 4) / Δ
  set β3 := vol3 (x 1 - x 4) (x 3 - x 4) (x 6 - x 4) / Δ
  set γ3 := vol3 (x 1 - x 4) (x 2 - x 4) (x 3 - x 4) / Δ
  set α5 := vol3 (x 5 - x 4) (x 2 - x 4) (x 6 - x 4) / Δ
  set β5 := vol3 (x 1 - x 4) (x 5 - x 4) (x 6 - x 4) / Δ
  set γ5 := vol3 (x 1 - x 4) (x 2 - x 4) (x 5 - x 4) / Δ
  rw [g4, g2, g6] at cG0 cG3 cG5; rw [d1, d2] at cD0 cD3; rw [d1, d2, d5] at cD5
  rw [a4, a1, a0] at cA0; rw [a4, a1, a3] at cA3; rw [a4, a1] at cA5
  rw [n4, n1, n6] at cN0 cN3; rw [i2, i5, i6] at cI5
  have nd4 := d4.ne; have na2 := a2.ne; have ng1 := g1.ne
  set c := fA (x 6) / fA (x 2) + fD (x 6) / fD (x 4) - 1 with hc
  -- the values of `P` at `0, 3`
  have hP : ∀ (gy dy α β γ : ℝ), gy - 0 = α * (fG (x 1) - 0) + β * (0 - 0) + γ * (0 - 0) →
      dy - fD (x 4) = α * (0 - fD (x 4)) + β * (0 - fD (x 4)) + γ * (fD (x 6) - fD (x 4)) →
      0 - 0 = α * (0 - 0) + β * (fA (x 2) - 0) + γ * (fA (x 6) - 0) →
      gy / fG (x 1) + dy / fD (x 4) = 1 + γ * c := by
    intro gy dy α β γ h1' h2' h3'
    simp only [hc]; field_simp
    linear_combination fD (x 4) * fA (x 2) * h1' + fG (x 1) * fA (x 2) * h2' +
      fG (x 1) * fD (x 4) * h3'
  have hQ : fG (x 5) / fG (x 1) + fA (x 5) / fA (x 2) = 1 + γ5 * c := by
    simp only [hc]; field_simp
    linear_combination fA (x 2) * fD (x 4) * cG5 + fG (x 1) * fD (x 4) * cA5 +
      fG (x 1) * fA (x 2) * cD5
  -- signs
  have hγy : ∀ (ny α β γ : ℝ), ny < 0 →
      ny - 0 = α * (0 - 0) + β * (fN (x 2) - 0) + γ * (0 - 0) →
      0 - 0 = α * (0 - 0) + β * (fA (x 2) - 0) + γ * (fA (x 6) - 0) → γ < 0 := by
    intro ny α β γ hn h1' h2'
    have hβ : 0 < β := by
      have : ny = β * fN (x 2) := by linear_combination h1'
      nlinarith
    have : γ * fA (x 6) = -(β * fA (x 2)) := by linear_combination -h2'
    nlinarith
  have hγ0 := hγy _ _ _ _ n0 cN0 cA0
  have hγ3 := hγy _ _ _ _ n3 cN3 cA3
  have hα5 : 0 < α5 := by
    have : fG (x 5) = α5 * fG (x 1) := by linear_combination cG5
    nlinarith
  have hσ5 : 1 - (α5 + β5 + γ5) < 0 := by
    have : fI (x 4) * (1 - (α5 + β5 + γ5)) = -(α5 * fI (x 1)) := by linear_combination -cI5
    nlinarith
  have hγ5 : 0 < γ5 := by
    have : γ5 * fD (x 6) = fD (x 4) * ((α5 + β5 + γ5) - 1) := by linear_combination -cD5
    nlinarith
  have hiP : QA ∩ QG = {x 4} := by
    rw [inter, show ({0, 1, 3, 4} ∩ {2, 4, 6} : Finset (Fin 7)) = {4} by decide]
    simp
  rcases le_or_gt c 0 with hcl | hcg
  · rcases hcl.lt_or_eq with hlt | heq
    · -- `c < 0`: the plain view, the tie allowed
      refine isRupert_of_facets_vertex_tie V hgen QA QG (sub _) (sub _)
        (isFacet_of_index x _ fA hA) (isFacet_of_index x _ fG hG) (x 4) hiP
        ⟨x 1, (memQ _ 1).mpr (by decide), fun h => by have := hx h; omega⟩
        ⟨x 2, (memQ _ 2).mpr (by decide), fun h => by have := hx h; omega⟩
        (hT2.1.tie (sub _) (sub _) hiP
          (Or.inr (by show (({2, 4, 6} : Finset (Fin 7)).image x).card = 3
                      rw [Finset.card_image_of_injective _ hx]; decide)))
        ⟨x 1, (memQ _ 1).mpr (by decide), x 2, (memQ _ 2).mpr (by decide),
          fun h => by have := hx h; omega, fun h => by have := hx h; omega, ?_⟩
      intro f1 f2 z1 n1' z2 n2' y hy hy1 hy2
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      rw [memQ] at hy1 hy2
      have hi : i = 5 := by clear * - hy1 hy2; fin_cases i <;> simp_all
      subst hi
      have e2' : f2 (x 5) / f2 (x 1) = fG (x 5) / fG (x 1) :=
        ratio f2 fG 2 4 6 (by decide) (by decide) (by decide)
          (z2 _ ((memQ _ 2).mpr (by decide))) (z2 _ ((memQ _ 4).mpr (by decide)))
          (z2 _ ((memQ _ 6).mpr (by decide))) ((hG 2).1 (by decide)) ((hG 4).1 (by decide))
          ((hG 6).1 (by decide)) _ _ (n2' _ (hxV 1) (by rw [memQ]; decide)).ne
          ((hG 1).2 (by decide)).ne
      have e1' : f1 (x 5) / f1 (x 2) = fA (x 5) / fA (x 2) :=
        ratio f1 fA 0 1 3 (by decide) (by decide) (by decide)
          (z1 _ ((memQ _ 0).mpr (by decide))) (z1 _ ((memQ _ 1).mpr (by decide)))
          (z1 _ ((memQ _ 3).mpr (by decide))) ((hA 0).1 (by decide)) ((hA 1).1 (by decide))
          ((hA 3).1 (by decide)) _ _ (n1' _ (hxV 2) (by rw [memQ]; decide)).ne
          ((hA 2).2 (by decide)).ne
      rw [e1', e2', hQ]
      nlinarith
    · -- `c = 0`: Lemma T′ (`x5` on the far side)
      refine isRupert_of_facets_vertex_chord V hgen QA QG (sub _) (sub _)
        (isFacet_of_index x _ fA hA) (isFacet_of_index x _ fG hG) (x 4) hiP
        ⟨x 1, (memQ _ 1).mpr (by decide), fun h => by have := hx h; omega⟩
        ⟨x 2, (memQ _ 2).mpr (by decide), fun h => by have := hx h; omega⟩ (hT2.2 (by rw [hQ, heq]; ring)) (x 1) (x 2)
        ((memQ _ 1).mpr (by decide)) ((memQ _ 2).mpr (by decide))
        (fun h => by have := hx h; omega) (fun h => by have := hx h; omega) (x 5) (hxV 5)
        (by rw [memQ]; decide) (by rw [memQ]; decide) ?_
      intro f1 f2 z1 n1' z2 n2'
      refine ⟨fun y hy hy1 hy2 hne => ?_, ?_⟩
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
        rw [memQ] at hy1 hy2
        have hi : i = 5 := by clear * - hy1 hy2; fin_cases i <;> simp_all
        exact absurd (by rw [hi]) hne
      have e2' : f2 (x 5) / f2 (x 1) = fG (x 5) / fG (x 1) :=
        ratio f2 fG 2 4 6 (by decide) (by decide) (by decide)
          (z2 _ ((memQ _ 2).mpr (by decide))) (z2 _ ((memQ _ 4).mpr (by decide)))
          (z2 _ ((memQ _ 6).mpr (by decide))) ((hG 2).1 (by decide)) ((hG 4).1 (by decide))
          ((hG 6).1 (by decide)) _ _ (n2' _ (hxV 1) (by rw [memQ]; decide)).ne
          ((hG 1).2 (by decide)).ne
      have e1' : f1 (x 5) / f1 (x 2) = fA (x 5) / fA (x 2) :=
        ratio f1 fA 0 1 3 (by decide) (by decide) (by decide)
          (z1 _ ((memQ _ 0).mpr (by decide))) (z1 _ ((memQ _ 1).mpr (by decide)))
          (z1 _ ((memQ _ 3).mpr (by decide))) ((hA 0).1 (by decide)) ((hA 1).1 (by decide))
          ((hA 3).1 (by decide)) _ _ (n1' _ (hxV 2) (by rw [memQ]; decide)).ne
          ((hA 2).2 (by decide)).ne
      rw [e1', e2', hQ]
      nlinarith
  · -- the view `P` along the planes of `125` and `246`
    have hivhT1 : QD ∩ QG = {x 2} := by
      rw [inter, show ({1, 2, 5} ∩ {2, 4, 6} : Finset (Fin 7)) = {2} by decide]
      simp
    refine isRupert_of_facets_vertex_tie V hgen QD QG (sub _) (sub _) (isFacet_of_index x _ fD hD)
      (isFacet_of_index x _ fG hG) (x 2) hivhT1
      ⟨x 1, (memQ _ 1).mpr (by decide), fun h => by have := hx h; omega⟩
      ⟨x 4, (memQ _ 4).mpr (by decide), fun h => by have := hx h; omega⟩
      (hT1.tie (sub _) (sub _) hivhT1
        (Or.inl (by show (({1, 2, 5} : Finset (Fin 7)).image x).card = 3; rw [Finset.card_image_of_injective _ hx]; decide))) ?_
    refine ⟨x 1, (memQ _ 1).mpr (by decide), x 4, (memQ _ 4).mpr (by decide),
      fun h => by have := hx h; omega, fun h => by have := hx h; omega, ?_⟩
    intro f1 f2 z1 n1' z2 n2' y hy hy1 hy2
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
    rw [memQ] at hy1 hy2
    have hi : i = 0 ∨ i = 3 := by clear * - hy1 hy2; fin_cases i <;> simp_all
    have e2' : ∀ k : Fin 7, f2 (x k) / f2 (x 1) = fG (x k) / fG (x 1) :=
      fun k => ratio f2 fG 2 4 6 (by decide) (by decide) (by decide)
        (z2 _ ((memQ _ 2).mpr (by decide))) (z2 _ ((memQ _ 4).mpr (by decide)))
        (z2 _ ((memQ _ 6).mpr (by decide))) ((hG 2).1 (by decide)) ((hG 4).1 (by decide))
        ((hG 6).1 (by decide)) _ _ (n2' _ (hxV 1) (by rw [memQ]; decide)).ne
        ((hG 1).2 (by decide)).ne
    have e1' : ∀ k : Fin 7, f1 (x k) / f1 (x 4) = fD (x k) / fD (x 4) :=
      fun k => ratio f1 fD 1 2 5 (by decide) (by decide) (by decide)
        (z1 _ ((memQ _ 1).mpr (by decide))) (z1 _ ((memQ _ 2).mpr (by decide)))
        (z1 _ ((memQ _ 5).mpr (by decide))) ((hD 1).1 (by decide)) ((hD 2).1 (by decide))
        ((hD 5).1 (by decide)) _ _ (n1' _ (hxV 4) (by rw [memQ]; decide)).ne
        ((hD 4).2 (by decide)).ne
    rcases hi with rfl | rfl
    · rw [e2' 0, e1' 0, hP _ _ _ _ _ cG0 cD0 cA0]
      have := mul_neg_of_neg_of_pos hγ0 hcg
      linarith
    · rw [e2' 3, e1' 3, hP _ _ _ _ _ cG3 cD3 cA3]
      have := mul_neg_of_neg_of_pos hγ3 hcg
      linarith

end Minimality

end
