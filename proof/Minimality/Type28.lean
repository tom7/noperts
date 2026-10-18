module

public import Minimality.Type10
public import Minimality.TriFacetsChord

@[expose] public section

/-!
# Type 28 is Rupert in general position

Theorem O of `FEWER-FACES-PROOFS.md` §7, by the algebraic method of
`Type10.lean`. Faces `A = 0245` (a quadrilateral), `D = 036`, `G = 146`,
`H = 023`, `F = 015`, `M = 145` (and others). View `P` along the line of the
planes of `A` and `G` (through `x4`), view `Q` along that of `A` and `D` (through
`x0`). In the frame `x0; x4, x6, x2`, with `c = fD x2 / fD x4 + fG x2 / fG x0 - 1`,
the values are `1 + γ3 c` (`P`) and `1 + γ1 c` (`Q`), with `γ1 < 0 < γ3`.
At `c = 0` the only point `x3` off both planes of `P` is on the far side, and
`P` works by Lemma T′ (`isRupert_of_facets_vertex_chord`).
-/

namespace Minimality

open Finset
open scoped RealInnerProductSpace

set_option maxHeartbeats 8000000 in
/-- **Theorem O (type 28).** Seven labelled points in general position with
facets `0245` (a quadrilateral), `036`, `146`, `023`, `015`, `145`, given by
functionals negative off them, are Rupert, given `TriGen` at the lines of the planes
of `0245` and `146` and of `0245` and `036`. -/
theorem isRupert_type28 (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (hgen : GenPos (univ.image x)) (fA fD fG fH fF fM : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 2, 4, 5} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 2, 4, 5} : Finset (Fin 7)) → fA (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 3, 6} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 3, 6} : Finset (Fin 7)) → fD (x i) < 0))
    (hG : ∀ i, (i ∈ ({1, 4, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({1, 4, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hH : ∀ i, (i ∈ ({0, 2, 3} : Finset (Fin 7)) → fH (x i) = 0) ∧
      (i ∉ ({0, 2, 3} : Finset (Fin 7)) → fH (x i) < 0))
    (hF : ∀ i, (i ∈ ({0, 1, 5} : Finset (Fin 7)) → fF (x i) = 0) ∧
      (i ∉ ({0, 1, 5} : Finset (Fin 7)) → fF (x i) < 0))
    (hM : ∀ i, (i ∈ ({1, 4, 5} : Finset (Fin 7)) → fM (x i) = 0) ∧
      (i ∉ ({1, 4, 5} : Finset (Fin 7)) → fM (x i) < 0))
    (hT1 : TriGen (univ.image x) (({0, 2, 4, 5} : Finset (Fin 7)).image x)
      (({1, 4, 6} : Finset (Fin 7)).image x) (x 4))
    (hT2 : TriGen (univ.image x) (({0, 2, 4, 5} : Finset (Fin 7)).image x)
      (({0, 3, 6} : Finset (Fin 7)).image x) (x 0)) :
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
  set QA := ({0, 2, 4, 5} : Finset (Fin 7)).image x
  set QD := ({0, 3, 6} : Finset (Fin 7)).image x
  set QG := ({1, 4, 6} : Finset (Fin 7)).image x
  have sub : ∀ P : Finset (Fin 7), P.image x ⊆ V := fun P => Finset.image_subset_image (Finset.subset_univ P)
  have a0 := (hA 0).1 (by decide); have a2 := (hA 2).1 (by decide); have a4 := (hA 4).1 (by decide)
  have a5 := (hA 5).1 (by decide); have a1 := (hA 1).2 (by decide); have a3 := (hA 3).2 (by decide)
  have a6 := (hA 6).2 (by decide)
  have d0 := (hD 0).1 (by decide); have d3 := (hD 3).1 (by decide); have d6 := (hD 6).1 (by decide)
  have d1 := (hD 1).2 (by decide); have d2 := (hD 2).2 (by decide); have d4 := (hD 4).2 (by decide)
  have g1 := (hG 1).1 (by decide); have g4 := (hG 4).1 (by decide); have g6 := (hG 6).1 (by decide)
  have g0 := (hG 0).2 (by decide); have g2 := (hG 2).2 (by decide); have g3 := (hG 3).2 (by decide)
  have g5 := (hG 5).2 (by decide)
  have h0 := (hH 0).1 (by decide); have h2 := (hH 2).1 (by decide); have h3 := (hH 3).1 (by decide)
  have h4 := (hH 4).2 (by decide); have h5 := (hH 5).2 (by decide); have h6 := (hH 6).2 (by decide)
  have f0 := (hF 0).1 (by decide); have f1 := (hF 1).1 (by decide); have f5 := (hF 5).1 (by decide)
  have f2 := (hF 2).2 (by decide); have f4 := (hF 4).2 (by decide)
  have m1 := (hM 1).1 (by decide); have m4 := (hM 4).1 (by decide); have m5 := (hM 5).1 (by decide)
  have m0 := (hM 0).2 (by decide); have m2 := (hM 2).2 (by decide); have m6 := (hM 6).2 (by decide)
  -- the frame `x0; x4, x6, x2`
  have hΔ : vol3 (x 4 - x 0) (x 6 - x 0) (x 2 - x 0) ≠ 0 := by
    intro h0'
    have k := affine_vanish3 fA a0 a4 a2 (x 6) (x 0 + crs3 (x 4 - x 0) (x 2 - x 0))
    have pos := vol3_crs3_pos (p := x 0) (q := x 4) (r := x 2) (fun h => by have := hx h; omega)
      (ncol 0 4 2 (by decide) (by decide) (by decide))
    have e : vol3 (x 4 - x 0) (x 2 - x 0) (x 6 - x 0) = -vol3 (x 4 - x 0) (x 6 - x 0) (x 2 - x 0) := by
      simp only [vol3, PiLp.sub_apply]; ring
    rw [add_sub_cancel_left, e, h0', neg_zero, zero_mul] at k
    have := mul_neg_of_pos_of_neg pos a6
    linarith
  have co := fun (f : ℝ³ →ᵃ[ℝ] ℝ) (i : Fin 7) => affine_coord f (x 0) (x 4) (x 6) (x 2) (x i) hΔ
  have cG3 := co fG 3; have cA3 := co fA 3; have cD3 := co fD 3; have cH3 := co fH 3
  have cG1 := co fG 1; have cA1 := co fA 1; have cD1 := co fD 1; have cM1 := co fM 1
  have cG5 := co fG 5; have cA5 := co fA 5; have cM5 := co fM 5; have cF5 := co fF 5
  have cH5 := co fH 5
  set Δ := vol3 (x 4 - x 0) (x 6 - x 0) (x 2 - x 0)
  set α3 := vol3 (x 3 - x 0) (x 6 - x 0) (x 2 - x 0) / Δ
  set β3 := vol3 (x 4 - x 0) (x 3 - x 0) (x 2 - x 0) / Δ
  set γ3 := vol3 (x 4 - x 0) (x 6 - x 0) (x 3 - x 0) / Δ
  set α1 := vol3 (x 1 - x 0) (x 6 - x 0) (x 2 - x 0) / Δ
  set β1 := vol3 (x 4 - x 0) (x 1 - x 0) (x 2 - x 0) / Δ
  set γ1 := vol3 (x 4 - x 0) (x 6 - x 0) (x 1 - x 0) / Δ
  set α5 := vol3 (x 5 - x 0) (x 6 - x 0) (x 2 - x 0) / Δ
  set β5 := vol3 (x 4 - x 0) (x 5 - x 0) (x 2 - x 0) / Δ
  set γ5 := vol3 (x 4 - x 0) (x 6 - x 0) (x 5 - x 0) / Δ
  rw [g4, g6] at cG3 cG5; rw [g4, g6, g1] at cG1
  rw [a0, a4, a2] at cA3 cA1; rw [a0, a4, a2, a5] at cA5
  rw [d0, d6, d3] at cD3; rw [d0, d6] at cD1
  rw [h0, h2, h3] at cH3; rw [h0, h2] at cH5
  rw [m4, m1] at cM1; rw [m4, m5] at cM5; rw [f0, f5] at cF5
  have nd4 := d4.ne; have na6 := a6.ne; have ng0 := g0.ne
  set c := fD (x 2) / fD (x 4) + fG (x 2) / fG (x 0) - 1 with hc
  -- the two values
  have hP : fG (x 3) / fG (x 0) + fA (x 3) / fA (x 6) = 1 + γ3 * c := by
    simp only [hc]; field_simp
    linear_combination fA (x 6) * fD (x 4) * cG3 + fG (x 0) * fD (x 4) * cA3 +
      fG (x 0) * fA (x 6) * cD3
  have hQ : fD (x 1) / fD (x 4) + fA (x 1) / fA (x 6) = 1 + γ1 * c := by
    simp only [hc]; field_simp
    linear_combination fA (x 6) * fG (x 0) * cD1 + fD (x 4) * fG (x 0) * cA1 +
      fD (x 4) * fA (x 6) * cG1
  -- `γ3 > 0`
  have hβ3 : 0 < β3 := by
    have : fA (x 3) = β3 * fA (x 6) := by linear_combination cA3
    nlinarith
  have hα3 : α3 < 0 := by
    have : α3 * fH (x 4) = -(β3 * fH (x 6)) := by linear_combination -cH3
    nlinarith
  have hγ3 : 0 < γ3 := by
    have : γ3 * fD (x 2) = -(α3 * fD (x 4)) := by linear_combination -cD3
    nlinarith
  -- `γ1 < 0`
  have hβ5 : β5 = 0 := by
    have : β5 * fA (x 6) = 0 := by linear_combination -cA5
    exact (mul_eq_zero.mp this).resolve_right na6
  have hα5 : 0 < α5 := by
    have : fH (x 5) = α5 * fH (x 4) + β5 * fH (x 6) := by linear_combination cH5
    rw [hβ5, zero_mul, add_zero] at this
    nlinarith
  have hγ5 : γ5 < 0 := by
    have : γ5 * fF (x 2) = -(α5 * fF (x 4) + β5 * fF (x 6)) := by linear_combination -cF5
    rw [hβ5, zero_mul, add_zero] at this
    nlinarith
  have hW : 0 < fM (x 2) * fG (x 0) - fG (x 2) * fM (x 0) := by
    have k : fG (x 5) * fM (x 0) = γ5 * (fG (x 2) * fM (x 0) - fM (x 2) * fG (x 0)) := by
      rw [hβ5] at cG5 cM5; linear_combination fM (x 0) * cG5 - fG (x 0) * cM5
    have : 0 < fG (x 5) * fM (x 0) := mul_pos_of_neg_of_neg g5 m0
    nlinarith
  have hβ1 : 0 < β1 := by
    have : fA (x 1) = β1 * fA (x 6) := by linear_combination cA1
    nlinarith
  have hγ1 : γ1 < 0 := by
    have k : γ1 * (fM (x 2) * fG (x 0) - fG (x 2) * fM (x 0)) = -(fG (x 0) * β1 * fM (x 6)) := by
      linear_combination -fG (x 0) * cM1 + fM (x 0) * cG1
    have : 0 < fG (x 0) * fM (x 6) := mul_pos_of_neg_of_neg g0 m6
    nlinarith
  rcases le_or_gt c 0 with hcl | hcg
  · -- the view `P` along the planes of `0245` and `146`
    refine isRupert_of_facets_vertex_chord V hgen QA QG (sub _) (sub _)
      (isFacet_of_index x _ fA hA) (isFacet_of_index x _ fG hG) (x 4) ?_
      ⟨x 0, (memQ _ 0).mpr (by decide), fun h => by have := hx h; omega⟩
      ⟨x 6, (memQ _ 6).mpr (by decide), fun h => by have := hx h; omega⟩ hT1 (x 0) (x 6)
      ((memQ _ 0).mpr (by decide)) ((memQ _ 6).mpr (by decide))
      (fun h => by have := hx h; omega) (fun h => by have := hx h; omega) (x 3) (hxV 3)
      (by rw [memQ]; decide) (by rw [memQ]; decide) ?_
    · rw [inter, show ({0, 2, 4, 5} ∩ {1, 4, 6} : Finset (Fin 7)) = {4} by decide]
      simp
    intro f1' f2' z1 n1' z2 n2'
    refine ⟨fun y hy hy1 hy2 hne => ?_, ?_⟩
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      rw [memQ] at hy1 hy2
      have hi : i = 3 := by clear * - hy1 hy2; fin_cases i <;> simp_all
      exact absurd (by rw [hi]) hne
    have e2' : f2' (x 3) / f2' (x 0) = fG (x 3) / fG (x 0) :=
      ratio f2' fG 1 4 6 (by decide) (by decide) (by decide)
        (z2 _ ((memQ _ 1).mpr (by decide))) (z2 _ ((memQ _ 4).mpr (by decide)))
        (z2 _ ((memQ _ 6).mpr (by decide))) ((hG 1).1 (by decide)) ((hG 4).1 (by decide))
        ((hG 6).1 (by decide)) _ _ (n2' _ (hxV 0) (by rw [memQ]; decide)).ne
        ((hG 0).2 (by decide)).ne
    have e1' : f1' (x 3) / f1' (x 6) = fA (x 3) / fA (x 6) :=
      ratio f1' fA 0 2 4 (by decide) (by decide) (by decide)
        (z1 _ ((memQ _ 0).mpr (by decide))) (z1 _ ((memQ _ 2).mpr (by decide)))
        (z1 _ ((memQ _ 4).mpr (by decide))) ((hA 0).1 (by decide)) ((hA 2).1 (by decide))
        ((hA 4).1 (by decide)) _ _ (n1' _ (hxV 6) (by rw [memQ]; decide)).ne
        ((hA 6).2 (by decide)).ne
    rw [e1', e2', hP]
    nlinarith

  · -- the view `Q` along the planes of `0245` and `036`
    refine isRupert_of_facets_vertex V hgen QA QD (sub _) (sub _) (isFacet_of_index x _ fA hA)
      (isFacet_of_index x _ fD hD) (x 0) ?_
      ⟨x 4, (memQ _ 4).mpr (by decide), fun h => by have := hx h; omega⟩
      ⟨x 6, (memQ _ 6).mpr (by decide), fun h => by have := hx h; omega⟩ hT2 ?_
    · rw [inter, show ({0, 2, 4, 5} ∩ {0, 3, 6} : Finset (Fin 7)) = {0} by decide]
      simp
    refine ⟨x 4, (memQ _ 4).mpr (by decide), x 6, (memQ _ 6).mpr (by decide),
      fun h => by have := hx h; omega, fun h => by have := hx h; omega, ?_⟩
    intro f1' f2' z1 n1' z2 n2' y hy hy1 hy2
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
    rw [memQ] at hy1 hy2
    have hi : i = 1 := by clear * - hy1 hy2; fin_cases i <;> simp_all
    subst hi
    have e2' : f2' (x 1) / f2' (x 4) = fD (x 1) / fD (x 4) :=
      ratio f2' fD 0 3 6 (by decide) (by decide) (by decide)
        (z2 _ ((memQ _ 0).mpr (by decide))) (z2 _ ((memQ _ 3).mpr (by decide)))
        (z2 _ ((memQ _ 6).mpr (by decide))) ((hD 0).1 (by decide)) ((hD 3).1 (by decide))
        ((hD 6).1 (by decide)) _ _ (n2' _ (hxV 4) (by rw [memQ]; decide)).ne
        ((hD 4).2 (by decide)).ne
    have e1' : f1' (x 1) / f1' (x 6) = fA (x 1) / fA (x 6) :=
      ratio f1' fA 0 2 4 (by decide) (by decide) (by decide)
        (z1 _ ((memQ _ 0).mpr (by decide))) (z1 _ ((memQ _ 2).mpr (by decide)))
        (z1 _ ((memQ _ 4).mpr (by decide))) ((hA 0).1 (by decide)) ((hA 2).1 (by decide))
        ((hA 4).1 (by decide)) _ _ (n1' _ (hxV 6) (by rw [memQ]; decide)).ne
        ((hA 6).2 (by decide)).ne
    rw [e1', e2', hQ]
    have := mul_neg_of_neg_of_pos hγ1 hcg
    linarith

end Minimality

end
