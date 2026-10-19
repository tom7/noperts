module

public import Minimality.Type10
public import Minimality.TriFacetsChord
public import Minimality.TriTie

@[expose] public section

/-!
# Type 27 is Rupert

Theorem I of `FEWER-FACES-PROOFS.md` §7, by the algebraic method of
`Type10.lean`, with three views: `P` along the edge `25` (faces `025`, `B = 2356`),
`Q1` along the line of the planes of `016` and `B` (through `x6`), `Q2` along the
line of the planes of `025` and `046` (through `x0`). In the affine frame
`x0; x2, x5, x6` (coordinates `α, β, γ`), `P` holds at `y` iff `α_y + β_y > 0`;
if it fails at `1` then `fE x2 / fE x5 ≥ 1`, which gives `Q1`; if it fails at
`4` then `fG x2 / fG x5 < 1`, which gives `Q2` at `1` and at `3`.
At the tie (`x4` on the far side in `P`), `fG x2 / fG x5 = 1` and `x3` is on the
far side in `Q2`, which then works by Lemma T′ (`isRupert_of_facets_vertex_chord`).
-/

namespace Minimality

open Finset
open scoped RealInnerProductSpace

set_option maxHeartbeats 8000000 in
/-- **Theorem I (type 27).** Seven labelled points, no three collinear, with facets
`2356` (a quadrilateral), `025`, `016`, `046`, `045`, `012`, `456`, given by
functionals negative off them, are Rupert, given no other segment parallel to `25`
(`EdgePar`) and `TriGenTri` at the lines of the planes of `016` and `2356` and
of `025` and `046` (with `TriGenFar` at the latter when `fG x2 / fG x5 = 1`,
where Lemma T′ is used). -/
theorem isRupert_type27 (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (hgen : NoThreeCollinear (univ.image x)) (fB fD fE fG fH fI fJ : ℝ³ →ᵃ[ℝ] ℝ)
    (hB : ∀ i, (i ∈ ({2, 3, 5, 6} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({2, 3, 5, 6} : Finset (Fin 7)) → fB (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 2, 5} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 2, 5} : Finset (Fin 7)) → fD (x i) < 0))
    (hE : ∀ i, (i ∈ ({0, 1, 6} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({0, 1, 6} : Finset (Fin 7)) → fE (x i) < 0))
    (hG : ∀ i, (i ∈ ({0, 4, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({0, 4, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hH : ∀ i, (i ∈ ({0, 4, 5} : Finset (Fin 7)) → fH (x i) = 0) ∧
      (i ∉ ({0, 4, 5} : Finset (Fin 7)) → fH (x i) < 0))
    (hI : ∀ i, (i ∈ ({0, 1, 2} : Finset (Fin 7)) → fI (x i) = 0) ∧
      (i ∉ ({0, 1, 2} : Finset (Fin 7)) → fI (x i) < 0))
    (hJ : ∀ i, (i ∈ ({4, 5, 6} : Finset (Fin 7)) → fJ (x i) = 0) ∧
      (i ∉ ({4, 5, 6} : Finset (Fin 7)) → fJ (x i) < 0))
    (hZ1 : EdgePar (univ.image x) (x 2) (x 5))
    (hT1 : TriGenTri (univ.image x) (({0, 1, 6} : Finset (Fin 7)).image x)
      (({2, 3, 5, 6} : Finset (Fin 7)).image x) (x 6))
    (hT2 : TriGenTri (univ.image x) (({0, 2, 5} : Finset (Fin 7)).image x)
        (({0, 4, 6} : Finset (Fin 7)).image x) (x 0) ∧
      (fG (x 2) / fG (x 5) = 1 →
        TriGenFar (univ.image x) (({0, 2, 5} : Finset (Fin 7)).image x)
          (({0, 4, 6} : Finset (Fin 7)).image x) (x 0))) :
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
  set QB := ({2, 3, 5, 6} : Finset (Fin 7)).image x
  set QD := ({0, 2, 5} : Finset (Fin 7)).image x
  set QE := ({0, 1, 6} : Finset (Fin 7)).image x
  set QG := ({0, 4, 6} : Finset (Fin 7)).image x
  have sub : ∀ P : Finset (Fin 7), P.image x ⊆ V := fun P => Finset.image_subset_image (Finset.subset_univ P)
  -- the affine frame `x0; x2, x5, x6`
  set Δ := vol3 (x 2 - x 0) (x 5 - x 0) (x 6 - x 0) with hΔdef
  have d0 := (hD 0).1 (by decide); have d2 := (hD 2).1 (by decide); have d5 := (hD 5).1 (by decide)
  have d6 := (hD 6).2 (by decide)
  have hΔ : Δ ≠ 0 := by
    intro h0
    have k := affine_vanish3 fD d0 d2 d5 (x 6) (x 0 + crs3 (x 2 - x 0) (x 5 - x 0))
    have pos := vol3_crs3_pos (p := x 0) (q := x 2) (r := x 5) (fun h => by have := hx h; omega)
      (ncol 0 2 5 (by decide) (by decide) (by decide))
    rw [add_sub_cancel_left] at k
    change _ * fD (x 6) = Δ * _ at k
    rw [h0, zero_mul] at k
    have := mul_neg_of_pos_of_neg pos d6
    linarith
  have co := fun (f : ℝ³ →ᵃ[ℝ] ℝ) (i : Fin 7) => affine_coord f (x 0) (x 2) (x 5) (x 6) (x i) hΔ
  have cB1 := co fB 1; have cD1 := co fD 1; have cE1 := co fE 1; have cI1 := co fI 1
  have cG1 := co fG 1
  have cB4 := co fB 4; have cD4 := co fD 4; have cE4 := co fE 4; have cG4 := co fG 4
  have cH4 := co fH 4
  have cB3 := co fB 3; have cD3 := co fD 3; have cG3 := co fG 3; have cJ3 := co fJ 3
  set α1 := vol3 (x 1 - x 0) (x 5 - x 0) (x 6 - x 0) / Δ
  set β1 := vol3 (x 2 - x 0) (x 1 - x 0) (x 6 - x 0) / Δ
  set γ1 := vol3 (x 2 - x 0) (x 5 - x 0) (x 1 - x 0) / Δ
  set α4 := vol3 (x 4 - x 0) (x 5 - x 0) (x 6 - x 0) / Δ
  set β4 := vol3 (x 2 - x 0) (x 4 - x 0) (x 6 - x 0) / Δ
  set γ4 := vol3 (x 2 - x 0) (x 5 - x 0) (x 4 - x 0) / Δ
  set α3 := vol3 (x 3 - x 0) (x 5 - x 0) (x 6 - x 0) / Δ
  set β3 := vol3 (x 2 - x 0) (x 3 - x 0) (x 6 - x 0) / Δ
  set γ3 := vol3 (x 2 - x 0) (x 5 - x 0) (x 3 - x 0) / Δ
  have b2 := (hB 2).1 (by decide); have b3 := (hB 3).1 (by decide); have b5 := (hB 5).1 (by decide)
  have b6 := (hB 6).1 (by decide); have b0 := (hB 0).2 (by decide); have b1 := (hB 1).2 (by decide)
  have b4 := (hB 4).2 (by decide)
  have d1 := (hD 1).2 (by decide); have d4 := (hD 4).2 (by decide); have d3 := (hD 3).2 (by decide)
  have e0 := (hE 0).1 (by decide); have e1 := (hE 1).1 (by decide); have e6 := (hE 6).1 (by decide)
  have e2 := (hE 2).2 (by decide); have e5 := (hE 5).2 (by decide)
  have g0 := (hG 0).1 (by decide); have g4 := (hG 4).1 (by decide); have g6 := (hG 6).1 (by decide)
  have g2 := (hG 2).2 (by decide); have g5 := (hG 5).2 (by decide)
  have h0 := (hH 0).1 (by decide); have h4 := (hH 4).1 (by decide); have h5 := (hH 5).1 (by decide)
  have h2 := (hH 2).2 (by decide); have h6 := (hH 6).2 (by decide)
  have i0 := (hI 0).1 (by decide); have i1 := (hI 1).1 (by decide); have i2 := (hI 2).1 (by decide)
  have i5 := (hI 5).2 (by decide); have i6 := (hI 6).2 (by decide)
  have j4 := (hJ 4).1 (by decide); have j5 := (hJ 5).1 (by decide); have j6 := (hJ 6).1 (by decide)
  have j2 := (hJ 2).2 (by decide); have j3 := (hJ 3).2 (by decide)
  rw [b2, b5, b6] at cB1 cB4; rw [b2, b3, b5, b6] at cB3
  rw [d0, d2, d5] at cD1 cD4 cD3
  rw [e0, e1, e6] at cE1; rw [e0, e6] at cE4
  rw [g0, g6] at cG1 cG3; rw [g0, g4, g6] at cG4
  rw [h0, h4, h5] at cH4
  rw [i0, i1, i2] at cI1
  rw [j5, j6] at cJ3
  -- signs of the coordinates of `x1`
  have hγ1 : 0 < γ1 := by
    have : fD (x 1) = γ1 * fD (x 6) := by linear_combination cD1
    nlinarith
  have hβ1 : β1 < 0 := by
    have : β1 * fI (x 5) = -(γ1 * fI (x 6)) := by linear_combination -cI1
    nlinarith
  have hα1 : 0 < α1 := by
    have : α1 * fE (x 2) = -(β1 * fE (x 5)) := by linear_combination -cE1
    nlinarith
  have hσ1 : α1 + β1 + γ1 < 1 := by
    have : fB (x 1) = (1 - (α1 + β1 + γ1)) * fB (x 0) := by linear_combination cB1
    nlinarith
  -- signs of the coordinates of `x4`
  have hγ4 : 0 < γ4 := by
    have : fD (x 4) = γ4 * fD (x 6) := by linear_combination cD4
    nlinarith
  have hα4 : α4 < 0 := by
    have : α4 * fH (x 2) = -(γ4 * fH (x 6)) := by linear_combination -cH4
    nlinarith
  have nb0 := b0.ne; have nd6 := d6.ne; have ne5 := e5.ne; have ng5 := g5.ne; have nj2 := j2.ne
  have P1 : fB (x 1) / fB (x 0) + fD (x 1) / fD (x 6) = 1 - (α1 + β1) := by
    field_simp; linear_combination fD (x 6) * cB1 + fB (x 0) * cD1
  have P4 : fB (x 4) / fB (x 0) + fD (x 4) / fD (x 6) = 1 - (α4 + β4) := by
    field_simp; linear_combination fD (x 6) * cB4 + fB (x 0) * cD4
  rcases lt_or_ge (fB (x 4) / fB (x 0) + fD (x 4) / fD (x 6)) 1 with h4lt | h4gt
  · by_cases h1lt : fB (x 1) / fB (x 0) + fD (x 1) / fD (x 6) < 1
    · -- the view `P` along the edge `25`
      refine isRupert_of_facets_edge_tri V hgen QD QB (sub _) (sub _) (isFacet_of_index x _ fD hD)
        (isFacet_of_index x _ fB hB) (x 2) (x 5) (fun h => by have := hx h; omega) ?_
        ⟨x 0, (memQ _ 0).mpr (by decide), by rw [memQ]; decide⟩
        ⟨x 6, (memQ _ 6).mpr (by decide), by rw [memQ]; decide⟩
        (Or.inl (by rw [Finset.card_image_of_injective _ hx]; rfl)) hZ1 ?_
      · rw [inter, show ({0, 2, 5} ∩ {2, 3, 5, 6} : Finset (Fin 7)) = {2, 5} by decide]
        simp [Finset.image_insert]
      refine ⟨x 0, (memQ _ 0).mpr (by decide), x 6, (memQ _ 6).mpr (by decide),
        by rw [memQ]; decide, by rw [memQ]; decide, ?_⟩
      intro f1 f2 z1 n1 z2 n2 y hy hy1 hy2
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      rw [memQ] at hy1 hy2
      have hi : i = 1 ∨ i = 4 := by clear * - hy1 hy2; fin_cases i <;> simp_all
      have e2' : ∀ k : Fin 7, k ∉ ({0, 2, 5} : Finset (Fin 7)) → f2 (x k) / f2 (x 0) = fB (x k) / fB (x 0) :=
        fun k _ => ratio f2 fB 2 5 6 (by decide) (by decide) (by decide)
        (z2 _ ((memQ _ 2).mpr (by decide))) (z2 _ ((memQ _ 5).mpr (by decide)))
        (z2 _ ((memQ _ 6).mpr (by decide))) ((hB 2).1 (by decide)) ((hB 5).1 (by decide))
        ((hB 6).1 (by decide)) _ _ (n2 _ (hxV 0) (by rw [memQ]; decide)).ne
        ((hB 0).2 (by decide)).ne
      have e1' : ∀ k : Fin 7, f1 (x k) / f1 (x 6) = fD (x k) / fD (x 6) :=
        fun k => ratio f1 fD 0 2 5 (by decide) (by decide) (by decide)
        (z1 _ ((memQ _ 0).mpr (by decide))) (z1 _ ((memQ _ 2).mpr (by decide)))
        (z1 _ ((memQ _ 5).mpr (by decide))) ((hD 0).1 (by decide)) ((hD 2).1 (by decide))
        ((hD 5).1 (by decide)) _ _ (n1 _ (hxV 6) (by rw [memQ]; decide)).ne
        ((hD 6).2 (by decide)).ne
      rcases hi with rfl | rfl
      · rw [e2' 1 (by decide), e1' 1]; exact h1lt
      · rw [e2' 4 (by decide), e1' 4]; exact h4lt
    · -- `P` fails at `1`: the view `Q1` along the planes of `016` and `2356`
      push Not at h1lt
      have hr : 1 ≤ fE (x 2) / fE (x 5) := by
        rw [P1] at h1lt
        have : α1 * fE (x 2) = -(β1 * fE (x 5)) := by linear_combination -cE1
        rw [le_div_iff_of_neg e5]; nlinarith
      have hivhT1 : QE ∩ QB = {x 6} := by
        rw [inter, show ({0, 1, 6} ∩ {2, 3, 5, 6} : Finset (Fin 7)) = {6} by decide]
        simp
      refine isRupert_of_facets_vertex_tie V hgen QE QB (sub _) (sub _) (isFacet_of_index x _ fE hE)
        (isFacet_of_index x _ fB hB) (x 6) hivhT1
        ⟨x 0, (memQ _ 0).mpr (by decide), fun h => by have := hx h; omega⟩
        ⟨x 5, (memQ _ 5).mpr (by decide), fun h => by have := hx h; omega⟩
        (hT1.tie (sub _) (sub _) hivhT1
          (Or.inl (by show (({0, 1, 6} : Finset (Fin 7)).image x).card = 3; rw [Finset.card_image_of_injective _ hx]; decide))) ?_
      refine ⟨x 0, (memQ _ 0).mpr (by decide), x 5, (memQ _ 5).mpr (by decide),
        fun h => by have := hx h; omega, fun h => by have := hx h; omega, ?_⟩
      intro f1 f2 z1 n1 z2 n2 y hy hy1 hy2
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      rw [memQ] at hy1 hy2
      have hi : i = 4 := by clear * - hy1 hy2; fin_cases i <;> simp_all
      subst hi
      have e2' : f2 (x 4) / f2 (x 0) = fB (x 4) / fB (x 0) :=
        ratio f2 fB 2 5 6 (by decide) (by decide) (by decide)
        (z2 _ ((memQ _ 2).mpr (by decide))) (z2 _ ((memQ _ 5).mpr (by decide)))
        (z2 _ ((memQ _ 6).mpr (by decide))) ((hB 2).1 (by decide)) ((hB 5).1 (by decide))
        ((hB 6).1 (by decide)) _ _ (n2 _ (hxV 0) (by rw [memQ]; decide)).ne
        ((hB 0).2 (by decide)).ne
      have e1' : f1 (x 4) / f1 (x 5) = fE (x 4) / fE (x 5) :=
        ratio f1 fE 0 1 6 (by decide) (by decide) (by decide)
        (z1 _ ((memQ _ 0).mpr (by decide))) (z1 _ ((memQ _ 1).mpr (by decide)))
        (z1 _ ((memQ _ 6).mpr (by decide))) ((hE 0).1 (by decide)) ((hE 1).1 (by decide))
        ((hE 6).1 (by decide)) _ _ (n1 _ (hxV 5) (by rw [memQ]; decide)).ne
        ((hE 5).2 (by decide)).ne
      rw [e1', e2']
      have k : fB (x 4) / fB (x 0) + fE (x 4) / fE (x 5) =
          1 - γ4 - α4 * (1 - fE (x 2) / fE (x 5)) := by
        field_simp; linear_combination fE (x 5) * cB4 + fB (x 0) * cE4
      rw [k]; nlinarith
  · -- `P` fails at `4`: the view `Q2` along the planes of `025` and `046`
    have hq : fG (x 2) / fG (x 5) ≤ 1 := by
      rw [P4] at h4gt
      have : β4 * fG (x 5) = -(α4 * fG (x 2)) := by linear_combination -cG4
      rw [div_le_one_of_neg g5]; nlinarith
    have hq0 : 0 < fG (x 2) / fG (x 5) := div_pos_of_neg_of_neg g2 g5
    have hiv : QD ∩ QG = {x 0} := by
      rw [inter, show ({0, 2, 5} ∩ {0, 4, 6} : Finset (Fin 7)) = {0} by decide]
      simp
    have hσ3 : α3 + β3 + γ3 = 1 := by
      have : (α3 + β3 + γ3 - 1) * fB (x 0) = 0 := by linear_combination cB3
      have := (mul_eq_zero.mp this).resolve_right nb0; linarith
    have hα3 : 0 < α3 := by
      have : fJ (x 3) = α3 * fJ (x 2) := by linear_combination cJ3 - fJ (x 0) * hσ3
      nlinarith
    rcases hq.lt_or_eq with hqlt | hqeq
    · -- `fG x2 < fG x5` in ratio: `x3` strictly inside, the view `Q2` by Lemma T (the tie allowed)
      refine isRupert_of_facets_vertex_tie V hgen QD QG (sub _) (sub _)
        (isFacet_of_index x _ fD hD) (isFacet_of_index x _ fG hG) (x 0) hiv
        ⟨x 5, (memQ _ 5).mpr (by decide), fun h => by have := hx h; omega⟩
        ⟨x 6, (memQ _ 6).mpr (by decide), fun h => by have := hx h; omega⟩
        (hT2.1.tie (sub _) (sub _) hiv
          (Or.inl (by show (({0, 2, 5} : Finset (Fin 7)).image x).card = 3
                      rw [Finset.card_image_of_injective _ hx]; decide)))
        ⟨x 5, (memQ _ 5).mpr (by decide), x 6, (memQ _ 6).mpr (by decide),
          fun h => by have := hx h; omega, fun h => by have := hx h; omega, ?_⟩
      intro f1 f2 z1 n1 z2 n2 y hy hy1 hy2
      have e2' : ∀ k : Fin 7, f2 (x k) / f2 (x 5) = fG (x k) / fG (x 5) :=
        fun k => ratio f2 fG 0 4 6 (by decide) (by decide) (by decide)
          (z2 _ ((memQ _ 0).mpr (by decide))) (z2 _ ((memQ _ 4).mpr (by decide)))
          (z2 _ ((memQ _ 6).mpr (by decide))) ((hG 0).1 (by decide)) ((hG 4).1 (by decide))
          ((hG 6).1 (by decide)) _ _ (n2 _ (hxV 5) (by rw [memQ]; decide)).ne
          ((hG 5).2 (by decide)).ne
      have e1' : ∀ k : Fin 7, f1 (x k) / f1 (x 6) = fD (x k) / fD (x 6) :=
        fun k => ratio f1 fD 0 2 5 (by decide) (by decide) (by decide)
          (z1 _ ((memQ _ 0).mpr (by decide))) (z1 _ ((memQ _ 2).mpr (by decide)))
          (z1 _ ((memQ _ 5).mpr (by decide))) ((hD 0).1 (by decide)) ((hD 2).1 (by decide))
          ((hD 5).1 (by decide)) _ _ (n1 _ (hxV 6) (by rw [memQ]; decide)).ne
          ((hD 6).2 (by decide)).ne
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      rw [memQ] at hy1 hy2
      have hi : i = 1 ∨ i = 3 := by clear * - hy1 hy2; fin_cases i <;> simp_all
      rcases hi with rfl | rfl
      · rw [e2' 1, e1' 1]
        have k : fG (x 1) / fG (x 5) + fD (x 1) / fD (x 6) =
            α1 * (fG (x 2) / fG (x 5)) + β1 + γ1 := by
          field_simp; linear_combination fD (x 6) * cG1 + fG (x 5) * cD1
        rw [k]; nlinarith
      · rw [e2' 3, e1' 3]
        have k : fG (x 3) / fG (x 5) + fD (x 3) / fD (x 6) =
            α3 * (fG (x 2) / fG (x 5)) + β3 + γ3 := by
          field_simp; linear_combination fD (x 6) * cG3 + fG (x 5) * cD3
        rw [k]
        have := mul_lt_mul_of_pos_left hqlt hα3
        linarith
    -- `fG x2 / fG x5 = 1`: `x3` on the far side, the view `Q2` by Lemma T′
    refine isRupert_of_facets_vertex_chord V hgen QD QG (sub _) (sub _)
      (isFacet_of_index x _ fD hD) (isFacet_of_index x _ fG hG) (x 0) hiv
      ⟨x 5, (memQ _ 5).mpr (by decide), fun h => by have := hx h; omega⟩
      ⟨x 6, (memQ _ 6).mpr (by decide), fun h => by have := hx h; omega⟩ (hT2.2 hqeq) (x 5) (x 6)
      ((memQ _ 5).mpr (by decide)) ((memQ _ 6).mpr (by decide))
      (fun h => by have := hx h; omega) (fun h => by have := hx h; omega) (x 3) (hxV 3)
      (by rw [memQ]; decide) (by rw [memQ]; decide) ?_
    intro f1 f2 z1 n1 z2 n2
    have e2' : ∀ k : Fin 7, f2 (x k) / f2 (x 5) = fG (x k) / fG (x 5) :=
      fun k => ratio f2 fG 0 4 6 (by decide) (by decide) (by decide)
        (z2 _ ((memQ _ 0).mpr (by decide))) (z2 _ ((memQ _ 4).mpr (by decide)))
        (z2 _ ((memQ _ 6).mpr (by decide))) ((hG 0).1 (by decide)) ((hG 4).1 (by decide))
        ((hG 6).1 (by decide)) _ _ (n2 _ (hxV 5) (by rw [memQ]; decide)).ne
        ((hG 5).2 (by decide)).ne
    have e1' : ∀ k : Fin 7, f1 (x k) / f1 (x 6) = fD (x k) / fD (x 6) :=
      fun k => ratio f1 fD 0 2 5 (by decide) (by decide) (by decide)
        (z1 _ ((memQ _ 0).mpr (by decide))) (z1 _ ((memQ _ 2).mpr (by decide)))
        (z1 _ ((memQ _ 5).mpr (by decide))) ((hD 0).1 (by decide)) ((hD 2).1 (by decide))
        ((hD 5).1 (by decide)) _ _ (n1 _ (hxV 6) (by rw [memQ]; decide)).ne
        ((hD 6).2 (by decide)).ne
    have vyc : f2 (x 3) / f2 (x 5) + f1 (x 3) / f1 (x 6) ≤ 1 := by
      rw [e2' 3, e1' 3]
      have k : fG (x 3) / fG (x 5) + fD (x 3) / fD (x 6) =
          α3 * (fG (x 2) / fG (x 5)) + β3 + γ3 := by
        field_simp; linear_combination fD (x 6) * cG3 + fG (x 5) * cD3
      rw [k, hqeq]; linarith
    refine ⟨fun y hy hy1 hy2 hne => ?_, vyc⟩
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
    rw [memQ] at hy1 hy2
    have hi : i = 1 := by
      have : i ≠ 3 := fun h => hne (by rw [h])
      clear * - hy1 hy2 this; fin_cases i <;> simp_all
    subst hi
    rw [e2' 1, e1' 1]
    have k : fG (x 1) / fG (x 5) + fD (x 1) / fD (x 6) =
        α1 * (fG (x 2) / fG (x 5)) + β1 + γ1 := by
      field_simp; linear_combination fD (x 6) * cG1 + fG (x 5) * cD1
    rw [k, hqeq]; nlinarith

end Minimality

end
