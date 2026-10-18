module

public import Minimality.Type10
public import Minimality.TriFacetsChord

@[expose] public section

/-!
# Type 12 is Rupert in general position

Theorem M of `FEWER-FACES-PROOFS.md` §7, by the algebraic method of
`Type10.lean`. Faces `A = 0135`, `B = 0346` (quadrilaterals), `D = 024`,
`G = 236`, `J = 246` (and others). View `P` along the line of the planes of `A`
and `D` (through `x0`), view `Q` along that of `D` and `G` (through `x2`). In the
frame `x2; x0, x3, x4`, with `c = fA x4 / fA x2 + fG x4 / fG x0 - 1`, the value of
`P` is `1 + γ6 c` and that of `Q` at `y = 1, 5` is `1 + γ_y c`, where `γ6 > 0`
and `γ_y < 0`: `P` works for `c < 0`, `Q` for `c > 0`, and at `c = 0` the only
point `x6` off both planes of `P` is on the far side, so `P` works by Lemma T′.
-/

namespace Minimality

open Finset
open scoped RealInnerProductSpace

set_option maxHeartbeats 8000000 in
/-- **Theorem M (type 12).** Seven labelled points in general position with
facets `0135`, `0346` (quadrilaterals), `024`, `236`, `246`, given by
functionals negative off them, are Rupert, given `TriGen` at the lines of the planes
of `0135` and `024` and of `024` and `236`. -/
theorem isRupert_type12 (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (hgen : GenPos (univ.image x)) (fA fB fD fG fJ : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 1, 3, 5} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 1, 3, 5} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({0, 3, 4, 6} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({0, 3, 4, 6} : Finset (Fin 7)) → fB (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 2, 4} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 2, 4} : Finset (Fin 7)) → fD (x i) < 0))
    (hG : ∀ i, (i ∈ ({2, 3, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({2, 3, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hJ : ∀ i, (i ∈ ({2, 4, 6} : Finset (Fin 7)) → fJ (x i) = 0) ∧
      (i ∉ ({2, 4, 6} : Finset (Fin 7)) → fJ (x i) < 0))
    (hT1 : TriGen (univ.image x) (({0, 1, 3, 5} : Finset (Fin 7)).image x)
      (({0, 2, 4} : Finset (Fin 7)).image x) (x 0))
    (hT2 : TriGen (univ.image x) (({0, 2, 4} : Finset (Fin 7)).image x)
      (({2, 3, 6} : Finset (Fin 7)).image x) (x 2)) :
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
  set QA := ({0, 1, 3, 5} : Finset (Fin 7)).image x
  set QD := ({0, 2, 4} : Finset (Fin 7)).image x
  set QG := ({2, 3, 6} : Finset (Fin 7)).image x
  have sub : ∀ P : Finset (Fin 7), P.image x ⊆ V := fun P => Finset.image_subset_image (Finset.subset_univ P)
  have a0 := (hA 0).1 (by decide); have a1 := (hA 1).1 (by decide); have a3 := (hA 3).1 (by decide)
  have a5 := (hA 5).1 (by decide); have a2 := (hA 2).2 (by decide); have a4 := (hA 4).2 (by decide)
  have a6 := (hA 6).2 (by decide)
  have b0 := (hB 0).1 (by decide); have b3 := (hB 3).1 (by decide); have b4 := (hB 4).1 (by decide)
  have b6 := (hB 6).1 (by decide); have b1 := (hB 1).2 (by decide); have b2 := (hB 2).2 (by decide)
  have b5 := (hB 5).2 (by decide)
  have d0 := (hD 0).1 (by decide); have d2 := (hD 2).1 (by decide); have d4 := (hD 4).1 (by decide)
  have d1 := (hD 1).2 (by decide); have d3 := (hD 3).2 (by decide); have d5 := (hD 5).2 (by decide)
  have d6 := (hD 6).2 (by decide)
  have g2 := (hG 2).1 (by decide); have g3 := (hG 3).1 (by decide); have g6 := (hG 6).1 (by decide)
  have g0 := (hG 0).2 (by decide); have g4 := (hG 4).2 (by decide)
  have j2 := (hJ 2).1 (by decide); have j4 := (hJ 4).1 (by decide); have j6 := (hJ 6).1 (by decide)
  have j0 := (hJ 0).2 (by decide); have j3 := (hJ 3).2 (by decide)
  -- the frame `x2; x0, x3, x4`
  have hΔ : vol3 (x 0 - x 2) (x 3 - x 2) (x 4 - x 2) ≠ 0 := by
    intro h0'
    have k := affine_vanish3 fD d2 d0 d4 (x 3) (x 2 + crs3 (x 0 - x 2) (x 4 - x 2))
    have pos := vol3_crs3_pos (p := x 2) (q := x 0) (r := x 4) (fun h => by have := hx h; omega)
      (ncol 2 0 4 (by decide) (by decide) (by decide))
    have e : vol3 (x 0 - x 2) (x 4 - x 2) (x 3 - x 2) = -vol3 (x 0 - x 2) (x 3 - x 2) (x 4 - x 2) := by
      simp only [vol3, PiLp.sub_apply]; ring
    rw [add_sub_cancel_left, e, h0', neg_zero, zero_mul] at k
    have := mul_neg_of_pos_of_neg pos d3
    linarith
  have co := fun (f : ℝ³ →ᵃ[ℝ] ℝ) (i : Fin 7) => affine_coord f (x 2) (x 0) (x 3) (x 4) (x i) hΔ
  have cD6 := co fD 6; have cA6 := co fA 6; have cG6 := co fG 6; have cJ6 := co fJ 6
  have cD1 := co fD 1; have cA1 := co fA 1; have cG1 := co fG 1; have cB1 := co fB 1
  have cD5 := co fD 5; have cA5 := co fA 5; have cG5 := co fG 5; have cB5 := co fB 5
  set Δ := vol3 (x 0 - x 2) (x 3 - x 2) (x 4 - x 2)
  set α6 := vol3 (x 6 - x 2) (x 3 - x 2) (x 4 - x 2) / Δ
  set β6 := vol3 (x 0 - x 2) (x 6 - x 2) (x 4 - x 2) / Δ
  set γ6 := vol3 (x 0 - x 2) (x 3 - x 2) (x 6 - x 2) / Δ
  set α1 := vol3 (x 1 - x 2) (x 3 - x 2) (x 4 - x 2) / Δ
  set β1 := vol3 (x 0 - x 2) (x 1 - x 2) (x 4 - x 2) / Δ
  set γ1 := vol3 (x 0 - x 2) (x 3 - x 2) (x 1 - x 2) / Δ
  set α5 := vol3 (x 5 - x 2) (x 3 - x 2) (x 4 - x 2) / Δ
  set β5 := vol3 (x 0 - x 2) (x 5 - x 2) (x 4 - x 2) / Δ
  set γ5 := vol3 (x 0 - x 2) (x 3 - x 2) (x 5 - x 2) / Δ
  rw [d2, d0, d4] at cD6 cD1 cD5; rw [a0, a3] at cA6; rw [a0, a3, a1] at cA1; rw [a0, a3, a5] at cA5
  rw [g2, g3, g6] at cG6; rw [g2, g3] at cG1 cG5; rw [j2, j4, j6] at cJ6
  rw [b0, b3, b4] at cB1 cB5
  have nd3 := d3.ne; have na2 := a2.ne; have ng0 := g0.ne
  set c := fA (x 4) / fA (x 2) + fG (x 4) / fG (x 0) - 1 with hc
  -- the two values
  have hP : fD (x 6) / fD (x 3) + fA (x 6) / fA (x 2) = 1 + γ6 * c := by
    simp only [hc]; field_simp
    linear_combination fA (x 2) * fG (x 0) * cD6 + fD (x 3) * fG (x 0) * cA6 +
      fD (x 3) * fA (x 2) * cG6
  have hQ : ∀ (gy dy α β γ : ℝ), gy - 0 = α * (fG (x 0) - 0) + β * (0 - 0) + γ * (fG (x 4) - 0) →
      dy - 0 = α * (0 - 0) + β * (fD (x 3) - 0) + γ * (0 - 0) →
      0 - fA (x 2) = α * (0 - fA (x 2)) + β * (0 - fA (x 2)) + γ * (fA (x 4) - fA (x 2)) →
      gy / fG (x 0) + dy / fD (x 3) = 1 + γ * c := by
    intro gy dy α β γ h1' h2' h3'
    simp only [hc]; field_simp
    linear_combination fD (x 3) * fA (x 2) * h1' + fG (x 0) * fA (x 2) * h2' +
      fG (x 0) * fD (x 3) * h3'
  -- signs
  have hβ6 : 0 < β6 := by
    have : fD (x 6) = β6 * fD (x 3) := by linear_combination cD6
    nlinarith
  have hα6 : α6 < 0 := by
    have : α6 * fJ (x 0) = -(β6 * fJ (x 3)) := by linear_combination -cJ6
    nlinarith
  have hγ6 : 0 < γ6 := by
    have : γ6 * fG (x 4) = -(α6 * fG (x 0)) := by linear_combination -cG6
    nlinarith
  have hγy : ∀ (by' α β γ : ℝ), by' < 0 →
      by' - fB (x 2) = α * (0 - fB (x 2)) + β * (0 - fB (x 2)) + γ * (0 - fB (x 2)) →
      0 - fA (x 2) = α * (0 - fA (x 2)) + β * (0 - fA (x 2)) + γ * (fA (x 4) - fA (x 2)) →
      γ < 0 := by
    intro by' α β γ hb h1' h2'
    have hσ : 0 < 1 - (α + β + γ) := by
      have : by' = fB (x 2) * (1 - (α + β + γ)) := by linear_combination h1'
      nlinarith
    have : γ * fA (x 4) = fA (x 2) * ((α + β + γ) - 1) := by linear_combination -h2'
    nlinarith
  have hγ1 := hγy _ _ _ _ b1 cB1 cA1
  have hγ5 := hγy _ _ _ _ b5 cB5 cA5
  rcases le_or_gt c 0 with hcl | hcg
  · -- the view `P` along the planes of `0135` and `024` (Lemma T′ at `c = 0`)
    refine isRupert_of_facets_vertex_chord V hgen QA QD (sub _) (sub _)
      (isFacet_of_index x _ fA hA) (isFacet_of_index x _ fD hD) (x 0) ?_
      ⟨x 3, (memQ _ 3).mpr (by decide), fun h => by have := hx h; omega⟩
      ⟨x 2, (memQ _ 2).mpr (by decide), fun h => by have := hx h; omega⟩ hT1 (x 3) (x 2)
      ((memQ _ 3).mpr (by decide)) ((memQ _ 2).mpr (by decide))
      (fun h => by have := hx h; omega) (fun h => by have := hx h; omega) (x 6) (hxV 6)
      (by rw [memQ]; decide) (by rw [memQ]; decide) ?_
    · rw [inter, show ({0, 1, 3, 5} ∩ {0, 2, 4} : Finset (Fin 7)) = {0} by decide]
      simp
    intro f1 f2 z1 n1 z2 n2
    refine ⟨fun y hy hy1 hy2 hne => ?_, ?_⟩
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      rw [memQ] at hy1 hy2
      have hi : i = 6 := by clear * - hy1 hy2; fin_cases i <;> simp_all
      exact absurd (by rw [hi]) hne
    have e2' : f2 (x 6) / f2 (x 3) = fD (x 6) / fD (x 3) :=
      ratio f2 fD 0 2 4 (by decide) (by decide) (by decide)
        (z2 _ ((memQ _ 0).mpr (by decide))) (z2 _ ((memQ _ 2).mpr (by decide)))
        (z2 _ ((memQ _ 4).mpr (by decide))) ((hD 0).1 (by decide)) ((hD 2).1 (by decide))
        ((hD 4).1 (by decide)) _ _ (n2 _ (hxV 3) (by rw [memQ]; decide)).ne
        ((hD 3).2 (by decide)).ne
    have e1' : f1 (x 6) / f1 (x 2) = fA (x 6) / fA (x 2) :=
      ratio f1 fA 0 1 3 (by decide) (by decide) (by decide)
        (z1 _ ((memQ _ 0).mpr (by decide))) (z1 _ ((memQ _ 1).mpr (by decide)))
        (z1 _ ((memQ _ 3).mpr (by decide))) ((hA 0).1 (by decide)) ((hA 1).1 (by decide))
        ((hA 3).1 (by decide)) _ _ (n1 _ (hxV 2) (by rw [memQ]; decide)).ne
        ((hA 2).2 (by decide)).ne
    rw [e1', e2', hP]
    nlinarith
  · -- the view `Q` along the planes of `024` and `236`
    refine isRupert_of_facets_vertex V hgen QD QG (sub _) (sub _) (isFacet_of_index x _ fD hD)
      (isFacet_of_index x _ fG hG) (x 2) ?_
      ⟨x 0, (memQ _ 0).mpr (by decide), fun h => by have := hx h; omega⟩
      ⟨x 3, (memQ _ 3).mpr (by decide), fun h => by have := hx h; omega⟩ hT2 ?_
    · rw [inter, show ({0, 2, 4} ∩ {2, 3, 6} : Finset (Fin 7)) = {2} by decide]
      simp
    refine ⟨x 0, (memQ _ 0).mpr (by decide), x 3, (memQ _ 3).mpr (by decide),
      fun h => by have := hx h; omega, fun h => by have := hx h; omega, ?_⟩
    intro f1 f2 z1 n1 z2 n2 y hy hy1 hy2
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
    rw [memQ] at hy1 hy2
    have hi : i = 1 ∨ i = 5 := by clear * - hy1 hy2; fin_cases i <;> simp_all
    have e2' : ∀ k : Fin 7, f2 (x k) / f2 (x 0) = fG (x k) / fG (x 0) :=
      fun k => ratio f2 fG 2 3 6 (by decide) (by decide) (by decide)
        (z2 _ ((memQ _ 2).mpr (by decide))) (z2 _ ((memQ _ 3).mpr (by decide)))
        (z2 _ ((memQ _ 6).mpr (by decide))) ((hG 2).1 (by decide)) ((hG 3).1 (by decide))
        ((hG 6).1 (by decide)) _ _ (n2 _ (hxV 0) (by rw [memQ]; decide)).ne
        ((hG 0).2 (by decide)).ne
    have e1' : ∀ k : Fin 7, f1 (x k) / f1 (x 3) = fD (x k) / fD (x 3) :=
      fun k => ratio f1 fD 0 2 4 (by decide) (by decide) (by decide)
        (z1 _ ((memQ _ 0).mpr (by decide))) (z1 _ ((memQ _ 2).mpr (by decide)))
        (z1 _ ((memQ _ 4).mpr (by decide))) ((hD 0).1 (by decide)) ((hD 2).1 (by decide))
        ((hD 4).1 (by decide)) _ _ (n1 _ (hxV 3) (by rw [memQ]; decide)).ne
        ((hD 3).2 (by decide)).ne
    rcases hi with rfl | rfl
    · rw [e2' 1, e1' 1, hQ _ _ _ _ _ cG1 cD1 cA1]
      have := mul_neg_of_neg_of_pos hγ1 hcg
      linarith
    · rw [e2' 5, e1' 5, hQ _ _ _ _ _ cG5 cD5 cA5]
      have := mul_neg_of_neg_of_pos hγ5 hcg
      linarith

end Minimality

end
