module

public import Minimality.Type10

@[expose] public section

/-!
# Type 25 is Rupert in general position

Theorem K of `FEWER-FACES-PROOFS.md` §7, by the algebraic method of
`Type10.lean`, with three views: `P` along the edge `13` (faces `013`, `136`),
`Q1` along the line of the planes of `013` and `A = 0246`, `Q2` along that of
`013` and `056` (both through `x0`). In the frame `x1; x0, x3, x6` the edge view
holds at `y` iff `α_y + γ_y < 1`; failing at `2` or `4` forces
`fA x1 / fA x3 ≥ 1`, which gives `Q1`; failing at `5` forces
`fG x1 / fG x3 < 1`, which gives `Q2`.
At the tie (`x5` on the far side in `P`), `fG x1 / fG x3 = 1` and `Q2` still
works.
-/

namespace Minimality

open Finset
open scoped RealInnerProductSpace

set_option maxHeartbeats 8000000 in
/-- **Theorem K (type 25).** Seven labelled points in general position with
facets `0246` (a quadrilateral), `013`, `136`, `056`, `035`, `014`, `126`, given
by functionals negative off them, are Rupert, given distinct depths along `13` and
`TriGen` at the lines of the planes of `013` and `0246` and of `013` and
`056`. -/
theorem isRupert_type25 (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (hgen : GenPos (univ.image x)) (fA fD fF fG fH fE fI : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 2, 4, 6} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 2, 4, 6} : Finset (Fin 7)) → fA (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 1, 3} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 1, 3} : Finset (Fin 7)) → fD (x i) < 0))
    (hF : ∀ i, (i ∈ ({1, 3, 6} : Finset (Fin 7)) → fF (x i) = 0) ∧
      (i ∉ ({1, 3, 6} : Finset (Fin 7)) → fF (x i) < 0))
    (hG : ∀ i, (i ∈ ({0, 5, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({0, 5, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hH : ∀ i, (i ∈ ({0, 3, 5} : Finset (Fin 7)) → fH (x i) = 0) ∧
      (i ∉ ({0, 3, 5} : Finset (Fin 7)) → fH (x i) < 0))
    (hE : ∀ i, (i ∈ ({0, 1, 4} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({0, 1, 4} : Finset (Fin 7)) → fE (x i) < 0))
    (hI : ∀ i, (i ∈ ({1, 2, 6} : Finset (Fin 7)) → fI (x i) = 0) ∧
      (i ∉ ({1, 2, 6} : Finset (Fin 7)) → fI (x i) < 0))
    (hZ1 : Set.InjOn (fun p : ℝ³ => ⟪p, x 3 - x 1⟫) (univ.image x : Set ℝ³))
    (hT1 : TriGen (univ.image x) (({0, 1, 3} : Finset (Fin 7)).image x)
      (({0, 2, 4, 6} : Finset (Fin 7)).image x) (x 0))
    (hT2 : TriGen (univ.image x) (({0, 1, 3} : Finset (Fin 7)).image x)
      (({0, 5, 6} : Finset (Fin 7)).image x) (x 0)) :
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
  set QD := ({0, 1, 3} : Finset (Fin 7)).image x
  set QF := ({1, 3, 6} : Finset (Fin 7)).image x
  set QG := ({0, 5, 6} : Finset (Fin 7)).image x
  have sub : ∀ P : Finset (Fin 7), P.image x ⊆ V := fun P => Finset.image_subset_image (Finset.subset_univ P)
  have a0 := (hA 0).1 (by decide); have a2 := (hA 2).1 (by decide); have a4 := (hA 4).1 (by decide)
  have a6 := (hA 6).1 (by decide); have a1 := (hA 1).2 (by decide); have a3 := (hA 3).2 (by decide)
  have a5 := (hA 5).2 (by decide)
  have d0 := (hD 0).1 (by decide); have d1 := (hD 1).1 (by decide); have d3 := (hD 3).1 (by decide)
  have d6 := (hD 6).2 (by decide); have d2 := (hD 2).2 (by decide); have d4 := (hD 4).2 (by decide)
  have d5 := (hD 5).2 (by decide)
  have f1 := (hF 1).1 (by decide); have f3 := (hF 3).1 (by decide); have f6 := (hF 6).1 (by decide)
  have f0 := (hF 0).2 (by decide); have f2 := (hF 2).2 (by decide); have f4 := (hF 4).2 (by decide)
  have f5 := (hF 5).2 (by decide)
  have g0 := (hG 0).1 (by decide); have g5 := (hG 5).1 (by decide); have g6 := (hG 6).1 (by decide)
  have g1 := (hG 1).2 (by decide); have g3 := (hG 3).2 (by decide)
  have h0 := (hH 0).1 (by decide); have h3 := (hH 3).1 (by decide); have h5 := (hH 5).1 (by decide)
  have h1 := (hH 1).2 (by decide); have h6 := (hH 6).2 (by decide)
  have e0 := (hE 0).1 (by decide); have e1 := (hE 1).1 (by decide); have e4 := (hE 4).1 (by decide)
  have e3 := (hE 3).2 (by decide); have e6 := (hE 6).2 (by decide)
  have i1 := (hI 1).1 (by decide); have i2 := (hI 2).1 (by decide); have i6 := (hI 6).1 (by decide)
  have i0 := (hI 0).2 (by decide); have i3 := (hI 3).2 (by decide)
  -- the frame `x1; x0, x3, x6`
  have hΔ : vol3 (x 0 - x 1) (x 3 - x 1) (x 6 - x 1) ≠ 0 := by
    intro h0'
    have k := affine_vanish3 fD d1 d0 d3 (x 6) (x 1 + crs3 (x 0 - x 1) (x 3 - x 1))
    have pos := vol3_crs3_pos (p := x 1) (q := x 0) (r := x 3) (fun h => by have := hx h; omega)
      (ncol 1 0 3 (by decide) (by decide) (by decide))
    rw [add_sub_cancel_left, h0', zero_mul] at k
    have := mul_neg_of_pos_of_neg pos d6
    linarith
  have co := fun (f : ℝ³ →ᵃ[ℝ] ℝ) (i : Fin 7) => affine_coord f (x 1) (x 0) (x 3) (x 6) (x i) hΔ
  have cD2 := co fD 2; have cF2 := co fF 2; have cA2 := co fA 2; have cI2 := co fI 2
  have cG2 := co fG 2
  have cD4 := co fD 4; have cF4 := co fF 4; have cA4 := co fA 4; have cE4 := co fE 4
  have cG4 := co fG 4
  have cD5 := co fD 5; have cF5 := co fF 5; have cA5 := co fA 5; have cH5 := co fH 5
  have cG5 := co fG 5
  set Δ := vol3 (x 0 - x 1) (x 3 - x 1) (x 6 - x 1)
  set α2 := vol3 (x 2 - x 1) (x 3 - x 1) (x 6 - x 1) / Δ
  set β2 := vol3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) / Δ
  set γ2 := vol3 (x 0 - x 1) (x 3 - x 1) (x 2 - x 1) / Δ
  set α4 := vol3 (x 4 - x 1) (x 3 - x 1) (x 6 - x 1) / Δ
  set β4 := vol3 (x 0 - x 1) (x 4 - x 1) (x 6 - x 1) / Δ
  set γ4 := vol3 (x 0 - x 1) (x 3 - x 1) (x 4 - x 1) / Δ
  set α5 := vol3 (x 5 - x 1) (x 3 - x 1) (x 6 - x 1) / Δ
  set β5 := vol3 (x 0 - x 1) (x 5 - x 1) (x 6 - x 1) / Δ
  set γ5 := vol3 (x 0 - x 1) (x 3 - x 1) (x 5 - x 1) / Δ
  rw [d1, d0, d3] at cD2 cD4 cD5; rw [f1, f3, f6] at cF2 cF4 cF5
  rw [a0, a6, a2] at cA2; rw [a0, a6, a4] at cA4; rw [a0, a6] at cA5
  rw [i1, i2, i6] at cI2; rw [e0, e1, e4] at cE4; rw [h0, h3, h5] at cH5
  rw [g0, g6] at cG2 cG4; rw [g0, g5, g6] at cG5
  have nd6 := d6.ne; have nf0 := f0.ne; have na3 := a3.ne; have ng3 := g3.ne
  -- the edge view's values: `α + γ`
  have Pv : ∀ (fy dy α β γ : ℝ), fy - 0 = α * (fF (x 0) - 0) + β * (0 - 0) + γ * (0 - 0) →
      dy - 0 = α * (0 - 0) + β * (0 - 0) + γ * (fD (x 6) - 0) →
      fy / fF (x 0) + dy / fD (x 6) = α + γ := by
    intro fy dy α β γ h1' h2'
    field_simp; linear_combination fD (x 6) * h1' + fF (x 0) * h2'
  have P2 := Pv _ _ _ _ _ cF2 cD2
  have P4 := Pv _ _ _ _ _ cF4 cD4
  have P5 := Pv _ _ _ _ _ cF5 cD5
  -- signs
  have hα : ∀ (fy α β γ : ℝ), fy < 0 → fy - 0 = α * (fF (x 0) - 0) + β * (0 - 0) + γ * (0 - 0) →
      0 < α := by
    intro fy α β γ hy h; nlinarith
  have hα2 := hα _ _ _ _ f2 cF2; have hα4 := hα _ _ _ _ f4 cF4; have hα5 := hα _ _ _ _ f5 cF5
  have hγ5 : 0 < γ5 := by nlinarith
  have hγ4 : 0 < γ4 := by nlinarith
  have hβ2 : β2 < 0 := by nlinarith
  have hβ4 : β4 < 0 := by nlinarith
  have hσ2 : 0 < 1 - (α2 + β2 + γ2) := by nlinarith
  have hσ4 : 0 < 1 - (α4 + β4 + γ4) := by nlinarith
  have hσ5 : 1 - (α5 + β5 + γ5) < 0 := by nlinarith
  rcases lt_or_ge (fF (x 5) / fF (x 0) + fD (x 5) / fD (x 6)) 1 with h5lt | h5gt
  · by_cases h24 : fF (x 2) / fF (x 0) + fD (x 2) / fD (x 6) < 1 ∧
        fF (x 4) / fF (x 0) + fD (x 4) / fD (x 6) < 1
    · -- the view `P` along the edge `13`
      refine isRupert_of_facets_edge V hgen QD QF (sub _) (sub _) (isFacet_of_index x _ fD hD)
        (isFacet_of_index x _ fF hF) (x 1) (x 3) (fun h => by have := hx h; omega) ?_
        ⟨x 0, (memQ _ 0).mpr (by decide), by rw [memQ]; decide⟩
        ⟨x 6, (memQ _ 6).mpr (by decide), by rw [memQ]; decide⟩ hZ1 ?_
      · rw [inter, show ({0, 1, 3} ∩ {1, 3, 6} : Finset (Fin 7)) = {1, 3} by decide]
        simp [Finset.image_insert]
      refine ⟨x 0, (memQ _ 0).mpr (by decide), x 6, (memQ _ 6).mpr (by decide),
        by rw [memQ]; decide, by rw [memQ]; decide, ?_⟩
      intro f1' f2' z1 n1 z2 n2 y hy hy1 hy2
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      rw [memQ] at hy1 hy2
      have hi : i = 2 ∨ i = 4 ∨ i = 5 := by clear * - hy1 hy2; fin_cases i <;> simp_all
      have e2' : ∀ k : Fin 7, f2' (x k) / f2' (x 0) = fF (x k) / fF (x 0) :=
        fun k => ratio f2' fF 1 3 6 (by decide) (by decide) (by decide)
        (z2 _ ((memQ _ 1).mpr (by decide))) (z2 _ ((memQ _ 3).mpr (by decide)))
        (z2 _ ((memQ _ 6).mpr (by decide))) ((hF 1).1 (by decide)) ((hF 3).1 (by decide))
        ((hF 6).1 (by decide)) _ _ (n2 _ (hxV 0) (by rw [memQ]; decide)).ne
        ((hF 0).2 (by decide)).ne
      have e1' : ∀ k : Fin 7, f1' (x k) / f1' (x 6) = fD (x k) / fD (x 6) :=
        fun k => ratio f1' fD 0 1 3 (by decide) (by decide) (by decide)
        (z1 _ ((memQ _ 0).mpr (by decide))) (z1 _ ((memQ _ 1).mpr (by decide)))
        (z1 _ ((memQ _ 3).mpr (by decide))) ((hD 0).1 (by decide)) ((hD 1).1 (by decide))
        ((hD 3).1 (by decide)) _ _ (n1 _ (hxV 6) (by rw [memQ]; decide)).ne
        ((hD 6).2 (by decide)).ne
      rcases hi with rfl | rfl | rfl
      · rw [e2' 2, e1' 2]; exact h24.1
      · rw [e2' 4, e1' 4]; exact h24.2
      · rw [e2' 5, e1' 5]; exact h5lt
    · -- `P` fails at `2` or `4`: the view `Q1` along the planes of `013` and `0246`
      have hr : 1 ≤ fA (x 1) / fA (x 3) := by
        rw [not_and_or] at h24; push Not at h24
        rcases h24 with h | h
        · rw [P2] at h
          have k : fA (x 1) / fA (x 3) * (1 - (α2 + β2 + γ2)) = -β2 := by
            field_simp; linear_combination -cA2
          by_contra hlt; push Not at hlt
          have := mul_lt_mul_of_pos_right hlt hσ2
          linarith
        · rw [P4] at h
          have k : fA (x 1) / fA (x 3) * (1 - (α4 + β4 + γ4)) = -β4 := by
            field_simp; linear_combination -cA4
          by_contra hlt; push Not at hlt
          have := mul_lt_mul_of_pos_right hlt hσ4
          linarith
      refine isRupert_of_facets_vertex V hgen QD QA (sub _) (sub _) (isFacet_of_index x _ fD hD)
        (isFacet_of_index x _ fA hA) (x 0) ?_
        ⟨x 3, (memQ _ 3).mpr (by decide), fun h => by have := hx h; omega⟩
        ⟨x 6, (memQ _ 6).mpr (by decide), fun h => by have := hx h; omega⟩ hT1 ?_
      · rw [inter, show ({0, 1, 3} ∩ {0, 2, 4, 6} : Finset (Fin 7)) = {0} by decide]
        simp
      refine ⟨x 3, (memQ _ 3).mpr (by decide), x 6, (memQ _ 6).mpr (by decide),
        fun h => by have := hx h; omega, fun h => by have := hx h; omega, ?_⟩
      intro f1' f2' z1 n1 z2 n2 y hy hy1 hy2
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      rw [memQ] at hy1 hy2
      have hi : i = 5 := by clear * - hy1 hy2; fin_cases i <;> simp_all
      subst hi
      have e2' : f2' (x 5) / f2' (x 3) = fA (x 5) / fA (x 3) :=
        ratio f2' fA 0 2 4 (by decide) (by decide) (by decide)
        (z2 _ ((memQ _ 0).mpr (by decide))) (z2 _ ((memQ _ 2).mpr (by decide)))
        (z2 _ ((memQ _ 4).mpr (by decide))) ((hA 0).1 (by decide)) ((hA 2).1 (by decide))
        ((hA 4).1 (by decide)) _ _ (n2 _ (hxV 3) (by rw [memQ]; decide)).ne
        ((hA 3).2 (by decide)).ne
      have e1' : f1' (x 5) / f1' (x 6) = fD (x 5) / fD (x 6) :=
        ratio f1' fD 0 1 3 (by decide) (by decide) (by decide)
        (z1 _ ((memQ _ 0).mpr (by decide))) (z1 _ ((memQ _ 1).mpr (by decide)))
        (z1 _ ((memQ _ 3).mpr (by decide))) ((hD 0).1 (by decide)) ((hD 1).1 (by decide))
        ((hD 3).1 (by decide)) _ _ (n1 _ (hxV 6) (by rw [memQ]; decide)).ne
        ((hD 6).2 (by decide)).ne
      rw [e1', e2']
      have k : fA (x 5) / fA (x 3) + fD (x 5) / fD (x 6) =
          fA (x 1) / fA (x 3) * (1 - (α5 + β5 + γ5)) + β5 + γ5 := by
        field_simp; linear_combination fD (x 6) * cA5 + fA (x 3) * cD5
      rw [k]
      have := mul_le_mul_of_nonpos_right hr hσ5.le
      linarith
  · -- `P` fails at `5`: the view `Q2` along the planes of `013` and `056`
    have hq : fG (x 1) / fG (x 3) ≤ 1 := by
      rw [P5] at h5gt
      have k : fG (x 1) / fG (x 3) * (1 - (α5 + β5 + γ5)) = -β5 := by
        field_simp; linear_combination -cG5
      by_contra hle; push Not at hle
      have := mul_lt_mul_of_neg_right hle hσ5
      linarith
    have hq0 : 0 < fG (x 1) / fG (x 3) := div_pos_of_neg_of_neg g1 g3
    refine isRupert_of_facets_vertex V hgen QD QG (sub _) (sub _) (isFacet_of_index x _ fD hD)
      (isFacet_of_index x _ fG hG) (x 0) ?_
      ⟨x 3, (memQ _ 3).mpr (by decide), fun h => by have := hx h; omega⟩
      ⟨x 6, (memQ _ 6).mpr (by decide), fun h => by have := hx h; omega⟩ hT2 ?_
    · rw [inter, show ({0, 1, 3} ∩ {0, 5, 6} : Finset (Fin 7)) = {0} by decide]
      simp
    refine ⟨x 3, (memQ _ 3).mpr (by decide), x 6, (memQ _ 6).mpr (by decide),
      fun h => by have := hx h; omega, fun h => by have := hx h; omega, ?_⟩
    intro f1' f2' z1 n1 z2 n2 y hy hy1 hy2
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
    rw [memQ] at hy1 hy2
    have hi : i = 2 ∨ i = 4 := by clear * - hy1 hy2; fin_cases i <;> simp_all
    have e2' : ∀ k : Fin 7, f2' (x k) / f2' (x 3) = fG (x k) / fG (x 3) :=
      fun k => ratio f2' fG 0 5 6 (by decide) (by decide) (by decide)
        (z2 _ ((memQ _ 0).mpr (by decide))) (z2 _ ((memQ _ 5).mpr (by decide)))
        (z2 _ ((memQ _ 6).mpr (by decide))) ((hG 0).1 (by decide)) ((hG 5).1 (by decide))
        ((hG 6).1 (by decide)) _ _ (n2 _ (hxV 3) (by rw [memQ]; decide)).ne
        ((hG 3).2 (by decide)).ne
    have e1' : ∀ k : Fin 7, f1' (x k) / f1' (x 6) = fD (x k) / fD (x 6) :=
      fun k => ratio f1' fD 0 1 3 (by decide) (by decide) (by decide)
        (z1 _ ((memQ _ 0).mpr (by decide))) (z1 _ ((memQ _ 1).mpr (by decide)))
        (z1 _ ((memQ _ 3).mpr (by decide))) ((hD 0).1 (by decide)) ((hD 1).1 (by decide))
        ((hD 3).1 (by decide)) _ _ (n1 _ (hxV 6) (by rw [memQ]; decide)).ne
        ((hD 6).2 (by decide)).ne
    rcases hi with rfl | rfl
    · rw [e2' 2, e1' 2]
      have k : fG (x 2) / fG (x 3) + fD (x 2) / fD (x 6) =
          fG (x 1) / fG (x 3) * (1 - (α2 + β2 + γ2)) + β2 + γ2 := by
        field_simp; linear_combination fD (x 6) * cG2 + fG (x 3) * cD2
      rw [k]
      have := mul_le_mul_of_nonneg_right hq hσ2.le
      linarith
    · rw [e2' 4, e1' 4]
      have k : fG (x 4) / fG (x 3) + fD (x 4) / fD (x 6) =
          fG (x 1) / fG (x 3) * (1 - (α4 + β4 + γ4)) + β4 + γ4 := by
        field_simp; linear_combination fD (x 6) * cG4 + fG (x 3) * cD4
      rw [k]
      have := mul_le_mul_of_nonneg_right hq hσ4.le
      linarith

end Minimality

end
