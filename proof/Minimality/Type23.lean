module

public import Minimality.Type10
public import Minimality.TriFacetsChord

@[expose] public section

/-!
# Type 23 is Rupert in general position

Theorem J of `FEWER-FACES-PROOFS.md` §7, by the algebraic method of
`Type10.lean`, with three views: `P` along the edge `04` (faces `014`,
`A = 0345`), `Q1` along the line of the planes of `014` and `156` (through
`x1`), `Q2` along the line of the planes of `A` and `125` (through `x5`). If `P`
fails at `6`, the frame `x1; x4, x5, x6` and `fA ≤ 0` at `x2, x3` give `Q1`; if it
fails at `2`, the frame `x5; x1, x2, x4` and `fD x6 < 0` give `Q2`.
At the tie (`x6` on the far side in `P`), `x3` is on the far side in `Q1`, which
then works by Lemma T′ (`isRupert_of_facets_vertex_chord`).
-/

namespace Minimality

open Finset
open scoped RealInnerProductSpace

set_option maxHeartbeats 8000000 in
/-- **Theorem J (type 23).** Seven labelled points in general position with
facets `0345` (a quadrilateral), `014`, `125`, `156`, `456`, given by
functionals negative off them, are Rupert, given distinct depths along `04` and
`TriGen` at the lines of the planes of `014` and `156` and of `0345` and
`125`. -/
theorem isRupert_type23 (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (hgen : GenPos (univ.image x)) (fA fD fE fH fK : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 3, 4, 5} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 3, 4, 5} : Finset (Fin 7)) → fA (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 1, 4} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 1, 4} : Finset (Fin 7)) → fD (x i) < 0))
    (hE : ∀ i, (i ∈ ({1, 2, 5} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({1, 2, 5} : Finset (Fin 7)) → fE (x i) < 0))
    (hH : ∀ i, (i ∈ ({1, 5, 6} : Finset (Fin 7)) → fH (x i) = 0) ∧
      (i ∉ ({1, 5, 6} : Finset (Fin 7)) → fH (x i) < 0))
    (hK : ∀ i, (i ∈ ({4, 5, 6} : Finset (Fin 7)) → fK (x i) = 0) ∧
      (i ∉ ({4, 5, 6} : Finset (Fin 7)) → fK (x i) < 0))
    (hZ1 : Set.InjOn (fun p : ℝ³ => ⟪p, x 4 - x 0⟫) (univ.image x : Set ℝ³))
    (hT1 : TriGen (univ.image x) (({0, 1, 4} : Finset (Fin 7)).image x)
      (({1, 5, 6} : Finset (Fin 7)).image x) (x 1))
    (hT2 : TriGen (univ.image x) (({0, 3, 4, 5} : Finset (Fin 7)).image x)
      (({1, 2, 5} : Finset (Fin 7)).image x) (x 5)) :
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
  set QA := ({0, 3, 4, 5} : Finset (Fin 7)).image x
  set QD := ({0, 1, 4} : Finset (Fin 7)).image x
  set QE := ({1, 2, 5} : Finset (Fin 7)).image x
  set QH := ({1, 5, 6} : Finset (Fin 7)).image x
  have sub : ∀ P : Finset (Fin 7), P.image x ⊆ V := fun P => Finset.image_subset_image (Finset.subset_univ P)
  have a0 := (hA 0).1 (by decide); have a3 := (hA 3).1 (by decide); have a4 := (hA 4).1 (by decide)
  have a5 := (hA 5).1 (by decide); have a1 := (hA 1).2 (by decide); have a2 := (hA 2).2 (by decide)
  have a6 := (hA 6).2 (by decide)
  have d0 := (hD 0).1 (by decide); have d1 := (hD 1).1 (by decide); have d4 := (hD 4).1 (by decide)
  have d2 := (hD 2).2 (by decide); have d3 := (hD 3).2 (by decide); have d5 := (hD 5).2 (by decide)
  have d6 := (hD 6).2 (by decide)
  have e1 := (hE 1).1 (by decide); have e2 := (hE 2).1 (by decide); have e5 := (hE 5).1 (by decide)
  have e4 := (hE 4).2 (by decide); have e6 := (hE 6).2 (by decide)
  have h1 := (hH 1).1 (by decide); have h5 := (hH 5).1 (by decide); have h6 := (hH 6).1 (by decide)
  have h2 := (hH 2).2 (by decide); have h3 := (hH 3).2 (by decide); have h4 := (hH 4).2 (by decide)
  have k4 := (hK 4).1 (by decide); have k5 := (hK 5).1 (by decide); have k6 := (hK 6).1 (by decide)
  have k1 := (hK 1).2 (by decide); have k3 := (hK 3).2 (by decide)
  have na1 := a1.ne; have nd5 := d5.ne; have ne4 := e4.ne; have nh4 := h4.ne
  rcases lt_or_ge (fA (x 6) / fA (x 1) + fD (x 6) / fD (x 5)) 1 with h6lt | h6gt
  · by_cases h2lt : fA (x 2) / fA (x 1) + fD (x 2) / fD (x 5) < 1
    · -- the view `P` along the edge `04`
      refine isRupert_of_facets_edge V hgen QD QA (sub _) (sub _) (isFacet_of_index x _ fD hD)
        (isFacet_of_index x _ fA hA) (x 0) (x 4) (fun h => by have := hx h; omega) ?_
        ⟨x 1, (memQ _ 1).mpr (by decide), by rw [memQ]; decide⟩
        ⟨x 5, (memQ _ 5).mpr (by decide), by rw [memQ]; decide⟩ hZ1 ?_
      · rw [inter, show ({0, 1, 4} ∩ {0, 3, 4, 5} : Finset (Fin 7)) = {0, 4} by decide]
        simp [Finset.image_insert]
      refine ⟨x 1, (memQ _ 1).mpr (by decide), x 5, (memQ _ 5).mpr (by decide),
        by rw [memQ]; decide, by rw [memQ]; decide, ?_⟩
      intro f1 f2 z1 n1 z2 n2 y hy hy1 hy2
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      rw [memQ] at hy1 hy2
      have hi : i = 2 ∨ i = 6 := by clear * - hy1 hy2; fin_cases i <;> simp_all
      have e2' : ∀ k : Fin 7, f2 (x k) / f2 (x 1) = fA (x k) / fA (x 1) :=
        fun k => ratio f2 fA 0 4 5 (by decide) (by decide) (by decide)
        (z2 _ ((memQ _ 0).mpr (by decide))) (z2 _ ((memQ _ 4).mpr (by decide)))
        (z2 _ ((memQ _ 5).mpr (by decide))) ((hA 0).1 (by decide)) ((hA 4).1 (by decide))
        ((hA 5).1 (by decide)) _ _ (n2 _ (hxV 1) (by rw [memQ]; decide)).ne
        ((hA 1).2 (by decide)).ne
      have e1' : ∀ k : Fin 7, f1 (x k) / f1 (x 5) = fD (x k) / fD (x 5) :=
        fun k => ratio f1 fD 0 1 4 (by decide) (by decide) (by decide)
        (z1 _ ((memQ _ 0).mpr (by decide))) (z1 _ ((memQ _ 1).mpr (by decide)))
        (z1 _ ((memQ _ 4).mpr (by decide))) ((hD 0).1 (by decide)) ((hD 1).1 (by decide))
        ((hD 4).1 (by decide)) _ _ (n1 _ (hxV 5) (by rw [memQ]; decide)).ne
        ((hD 5).2 (by decide)).ne
      rcases hi with rfl | rfl
      · rw [e2' 2, e1' 2]; exact h2lt
      · rw [e2' 6, e1' 6]; exact h6lt
    · -- `P` fails at `2`: the view `Q2` along the planes of `0345` and `125`
      push Not at h2lt
      have hΔ : vol3 (x 1 - x 5) (x 2 - x 5) (x 4 - x 5) ≠ 0 := by
        intro h0
        have k := affine_vanish3 fE e5 e1 e2 (x 4) (x 5 + crs3 (x 1 - x 5) (x 2 - x 5))
        have pos := vol3_crs3_pos (p := x 5) (q := x 1) (r := x 2) (fun h => by have := hx h; omega)
          (ncol 5 1 2 (by decide) (by decide) (by decide))
        rw [add_sub_cancel_left, h0, zero_mul] at k
        have := mul_neg_of_pos_of_neg pos e4
        linarith
      have cE := affine_coord fE (x 5) (x 1) (x 2) (x 4) (x 6) hΔ
      have cH := affine_coord fH (x 5) (x 1) (x 2) (x 4) (x 6) hΔ
      have cD := affine_coord fD (x 5) (x 1) (x 2) (x 4) (x 6) hΔ
      have cA := affine_coord fA (x 5) (x 1) (x 2) (x 4) (x 6) hΔ
      set α := vol3 (x 6 - x 5) (x 2 - x 5) (x 4 - x 5) / vol3 (x 1 - x 5) (x 2 - x 5) (x 4 - x 5)
      set β := vol3 (x 1 - x 5) (x 6 - x 5) (x 4 - x 5) / vol3 (x 1 - x 5) (x 2 - x 5) (x 4 - x 5)
      set γ := vol3 (x 1 - x 5) (x 2 - x 5) (x 6 - x 5) / vol3 (x 1 - x 5) (x 2 - x 5) (x 4 - x 5)
      rw [e5, e1, e2] at cE; rw [h5, h1, h6] at cH; rw [d1, d4] at cD; rw [a5, a4] at cA
      have hγ : 0 < γ := by
        have : fE (x 6) = γ * fE (x 4) := by linear_combination cE
        nlinarith
      have hβ : β < 0 := by
        have : β * fH (x 2) = -(γ * fH (x 4)) := by linear_combination -cH
        nlinarith
      have hD6 : 0 < (1 - (α + β + γ)) + β * (fD (x 2) / fD (x 5)) := by
        have k : (1 - (α + β + γ)) + β * (fD (x 2) / fD (x 5)) = fD (x 6) / fD (x 5) := by
          field_simp; linear_combination -cD
        rw [k]; exact div_pos_of_neg_of_neg d6 d5
      refine isRupert_of_facets_vertex V hgen QA QE (sub _) (sub _) (isFacet_of_index x _ fA hA)
        (isFacet_of_index x _ fE hE) (x 5) ?_
        ⟨x 4, (memQ _ 4).mpr (by decide), fun h => by have := hx h; omega⟩
        ⟨x 1, (memQ _ 1).mpr (by decide), fun h => by have := hx h; omega⟩ hT2 ?_
      · rw [inter, show ({0, 3, 4, 5} ∩ {1, 2, 5} : Finset (Fin 7)) = {5} by decide]
        simp
      refine ⟨x 4, (memQ _ 4).mpr (by decide), x 1, (memQ _ 1).mpr (by decide),
        fun h => by have := hx h; omega, fun h => by have := hx h; omega, ?_⟩
      intro f1 f2 z1 n1 z2 n2 y hy hy1 hy2
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      rw [memQ] at hy1 hy2
      have hi : i = 6 := by clear * - hy1 hy2; fin_cases i <;> simp_all
      subst hi
      have e2' : f2 (x 6) / f2 (x 4) = fE (x 6) / fE (x 4) :=
        ratio f2 fE 1 2 5 (by decide) (by decide) (by decide)
        (z2 _ ((memQ _ 1).mpr (by decide))) (z2 _ ((memQ _ 2).mpr (by decide)))
        (z2 _ ((memQ _ 5).mpr (by decide))) ((hE 1).1 (by decide)) ((hE 2).1 (by decide))
        ((hE 5).1 (by decide)) _ _ (n2 _ (hxV 4) (by rw [memQ]; decide)).ne
        ((hE 4).2 (by decide)).ne
      have e1' : f1 (x 6) / f1 (x 1) = fA (x 6) / fA (x 1) :=
        ratio f1 fA 0 4 5 (by decide) (by decide) (by decide)
        (z1 _ ((memQ _ 0).mpr (by decide))) (z1 _ ((memQ _ 4).mpr (by decide)))
        (z1 _ ((memQ _ 5).mpr (by decide))) ((hA 0).1 (by decide)) ((hA 4).1 (by decide))
        ((hA 5).1 (by decide)) _ _ (n1 _ (hxV 1) (by rw [memQ]; decide)).ne
        ((hA 1).2 (by decide)).ne
      rw [e1', e2']
      have k : fE (x 6) / fE (x 4) + fA (x 6) / fA (x 1) =
          (α + β + γ) + β * (fA (x 2) / fA (x 1) - 1) := by
        field_simp; linear_combination fA (x 1) * cE + fE (x 4) * cA
      rw [k]
      have : β * (fA (x 2) / fA (x 1) - 1) ≤ β * (-(fD (x 2) / fD (x 5))) := by
        apply mul_le_mul_of_nonpos_left _ hβ.le; linarith
      nlinarith
  · -- `P` fails at `6`: the view `Q1` along the planes of `014` and `156`
    have hΔ : vol3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1) ≠ 0 := by
      intro h0
      have k := affine_vanish3 fH h1 h5 h6 (x 4) (x 1 + crs3 (x 5 - x 1) (x 6 - x 1))
      have pos := vol3_crs3_pos (p := x 1) (q := x 5) (r := x 6) (fun h => by have := hx h; omega)
        (ncol 1 5 6 (by decide) (by decide) (by decide))
      have e : vol3 (x 5 - x 1) (x 6 - x 1) (x 4 - x 1) = vol3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1) := by
        simp only [vol3, PiLp.sub_apply]; ring
      rw [add_sub_cancel_left, e, h0, zero_mul] at k
      have := mul_neg_of_pos_of_neg pos h4
      linarith
    have co := fun (f : ℝ³ →ᵃ[ℝ] ℝ) (i : Fin 7) => affine_coord f (x 1) (x 4) (x 5) (x 6) (x i) hΔ
    have cH2 := co fH 2; have cD2 := co fD 2; have cE2 := co fE 2; have cA2 := co fA 2
    have cH3 := co fH 3; have cD3 := co fD 3; have cK3 := co fK 3; have cA3 := co fA 3
    set α2 := vol3 (x 2 - x 1) (x 5 - x 1) (x 6 - x 1) / vol3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1)
    set β2 := vol3 (x 4 - x 1) (x 2 - x 1) (x 6 - x 1) / vol3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1)
    set γ2 := vol3 (x 4 - x 1) (x 5 - x 1) (x 2 - x 1) / vol3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1)
    set α3 := vol3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) / vol3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1)
    set β3 := vol3 (x 4 - x 1) (x 3 - x 1) (x 6 - x 1) / vol3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1)
    set γ3 := vol3 (x 4 - x 1) (x 5 - x 1) (x 3 - x 1) / vol3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1)
    rw [h1, h5, h6] at cH2 cH3; rw [d1, d4] at cD2 cD3; rw [e1, e2, e5] at cE2
    rw [a4, a5] at cA2; rw [a3, a4, a5] at cA3; rw [k4, k5, k6] at cK3
    have hα2 : 0 < α2 := by
      have : fH (x 2) = α2 * fH (x 4) := by linear_combination cH2
      nlinarith
    have hγ2 : γ2 < 0 := by
      have : γ2 * fE (x 6) = -(α2 * fE (x 4)) := by linear_combination -cE2
      nlinarith
    have hA2 : 0 < (1 - (α2 + β2 + γ2)) + γ2 * (fA (x 6) / fA (x 1)) := by
      have k : (1 - (α2 + β2 + γ2)) + γ2 * (fA (x 6) / fA (x 1)) = fA (x 2) / fA (x 1) := by
        field_simp; linear_combination -cA2
      rw [k]; exact div_pos_of_neg_of_neg a2 a1
    have hσ3 : 0 < 1 - (α3 + β3 + γ3) := by
      have : fK (x 3) = (1 - (α3 + β3 + γ3)) * fK (x 1) := by linear_combination cK3
      nlinarith
    have hA3 : (1 - (α3 + β3 + γ3)) + γ3 * (fA (x 6) / fA (x 1)) = 0 := by
      field_simp; linear_combination -cA3
    have hγ3 : γ3 < 0 := by
      have : γ3 * (fA (x 6) / fA (x 1)) < 0 := by linarith
      have : 0 < fA (x 6) / fA (x 1) := div_pos_of_neg_of_neg a6 a1
      nlinarith
    refine isRupert_of_facets_vertex_chord V hgen QD QH (sub _) (sub _)
      (isFacet_of_index x _ fD hD) (isFacet_of_index x _ fH hH) (x 1) ?_
      ⟨x 4, (memQ _ 4).mpr (by decide), fun h => by have := hx h; omega⟩
      ⟨x 5, (memQ _ 5).mpr (by decide), fun h => by have := hx h; omega⟩ hT1 (x 4) (x 5)
      ((memQ _ 4).mpr (by decide)) ((memQ _ 5).mpr (by decide))
      (fun h => by have := hx h; omega) (fun h => by have := hx h; omega) (x 3) (hxV 3)
      (by rw [memQ]; decide) (by rw [memQ]; decide) ?_
    · rw [inter, show ({0, 1, 4} ∩ {1, 5, 6} : Finset (Fin 7)) = {1} by decide]
      simp
    intro f1 f2 z1 n1 z2 n2
    have e2' : ∀ k : Fin 7, f2 (x k) / f2 (x 4) = fH (x k) / fH (x 4) :=
      fun k => ratio f2 fH 1 5 6 (by decide) (by decide) (by decide)
        (z2 _ ((memQ _ 1).mpr (by decide))) (z2 _ ((memQ _ 5).mpr (by decide)))
        (z2 _ ((memQ _ 6).mpr (by decide))) ((hH 1).1 (by decide)) ((hH 5).1 (by decide))
        ((hH 6).1 (by decide)) _ _ (n2 _ (hxV 4) (by rw [memQ]; decide)).ne
        ((hH 4).2 (by decide)).ne
    have e1' : ∀ k : Fin 7, f1 (x k) / f1 (x 5) = fD (x k) / fD (x 5) :=
      fun k => ratio f1 fD 0 1 4 (by decide) (by decide) (by decide)
        (z1 _ ((memQ _ 0).mpr (by decide))) (z1 _ ((memQ _ 1).mpr (by decide)))
        (z1 _ ((memQ _ 4).mpr (by decide))) ((hD 0).1 (by decide)) ((hD 1).1 (by decide))
        ((hD 4).1 (by decide)) _ _ (n1 _ (hxV 5) (by rw [memQ]; decide)).ne
        ((hD 5).2 (by decide)).ne
    have vyc : f2 (x 3) / f2 (x 4) + f1 (x 3) / f1 (x 5) ≤ 1 := by
      rw [e2' 3, e1' 3]
      have k : fH (x 3) / fH (x 4) + fD (x 3) / fD (x 5) =
          (α3 + β3 + γ3) - γ3 * (1 - fD (x 6) / fD (x 5)) := by
        field_simp; linear_combination fD (x 5) * cH3 + fH (x 4) * cD3
      rw [k]
      have : -γ3 * (1 - fD (x 6) / fD (x 5)) ≤ -γ3 * (fA (x 6) / fA (x 1)) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
      nlinarith
    refine ⟨fun y hy hy1 hy2 hne => ?_, vyc⟩
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
    rw [memQ] at hy1 hy2
    have hi : i = 2 := by
      have : i ≠ 3 := fun h => hne (by rw [h])
      clear * - hy1 hy2 this; fin_cases i <;> simp_all
    subst hi
    rw [e2' 2, e1' 2]
    have k : fH (x 2) / fH (x 4) + fD (x 2) / fD (x 5) =
        (α2 + β2 + γ2) - γ2 * (1 - fD (x 6) / fD (x 5)) := by
      field_simp; linear_combination fD (x 5) * cH2 + fH (x 4) * cD2
    rw [k]
    have : -γ2 * (1 - fD (x 6) / fD (x 5)) ≤ -γ2 * (fA (x 6) / fA (x 1)) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
    nlinarith

end Minimality

end
