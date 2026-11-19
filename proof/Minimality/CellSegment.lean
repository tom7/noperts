module

public import Minimality.OrthoView2
public import Minimality.CRay

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped RealInnerProductSpace Topology
open Filter Finset

namespace Minimality.H21

variable {m n : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}

/-- **Lemma A (Cell segment mixing).**  If `u` is in the strict cell and `w` is in the
closed cell, then any convex combination `(1 - s) • u + s • w` with `0 ≤ s < 1` is in
the strict cell. -/
theorem cellAt_segment {F : S0xFac m S x} {U Dn : Finset (Fin m)} {u w : ℝ³}
    (hu : CellAt F U Dn u) (hw : CellLe F U Dn w) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    CellAt F U Dn ((1 - s) • u + s • w) := by
  have hs_pos : 0 < 1 - s := by linarith
  have h_inner : ∀ N : ℝ³, ⟪N, (1 - s) • u + s • w⟫ = (1 - s) * ⟪N, u⟫ + s * ⟪N, w⟫ := by
    intro N
    rw [inner_add_right, inner_smul_right, inner_smul_right]
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · rw [h_inner]
    have hu_t := hu.1 t ht
    have hw_t := hw.1 t ht
    have h1 : 0 < (1 - s) * ⟪F.N t, u⟫ := mul_pos hs_pos hu_t
    have h2 : 0 ≤ s * ⟪F.N t, w⟫ := mul_nonneg hs0 hw_t
    linarith
  · rw [h_inner]
    have hu_t := hu.2 t ht
    have hw_t := hw.2 t ht
    have h1 : (1 - s) * ⟪F.N t, u⟫ < 0 := mul_neg_of_pos_of_neg hs_pos hu_t
    have h2 : s * ⟪F.N t, w⟫ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs0 hw_t
    linarith

/-- **Lemma B (Cell membership along a ray segment).**  If `u` is in the open cell and
the facings at `tau1 > 0` are weak (`CellLe F U Dn (u + tau1 • d)`), then every intermediate
point `u + tau • d` for `0 ≤ tau < tau1` lies in the open cell `CellAt F U Dn`. -/
theorem cellAt_ray_segment {F : S0xFac m S x} {U Dn : Finset (Fin m)} {u d : ℝ³}
    (hu : CellAt F U Dn u) {tau1 : ℝ} (htau1 : 0 < tau1)
    (hw : CellLe F U Dn (u + tau1 • d)) {tau : ℝ} (htau0 : 0 ≤ tau) (htau : tau < tau1) :
    CellAt F U Dn (u + tau • d) := by
  have hs0 : 0 ≤ tau / tau1 := div_nonneg htau0 htau1.le
  have hs1 : tau / tau1 < 1 := (div_lt_one htau1).2 htau
  have h_comb : (1 - tau / tau1) • u + (tau / tau1) • (u + tau1 • d) = u + tau • d := by
    rw [smul_add, ← add_assoc, ← add_smul]
    have : (1 - tau / tau1) + tau / tau1 = 1 := sub_add_cancel 1 (tau / tau1)
    rw [this, one_smul, smul_smul, div_mul_cancel₀ _ htau1.ne']
  rw [← h_comb]
  exact cellAt_segment hu hw hs0 hs1

/-- **Lemma B (unfolded facing version).** -/
theorem cellAt_ray_segment_of_facings {F : S0xFac m S x} {U Dn : Finset (Fin m)} {u d : ℝ³}
    (hu : CellAt F U Dn u) {tau1 : ℝ} (htau1 : 0 < tau1)
    (hU : ∀ t ∈ U, 0 ≤ ⟪F.N t, u + tau1 • d⟫)
    (hDn : ∀ t ∈ Dn, ⟪F.N t, u + tau1 • d⟫ ≤ 0)
    {tau : ℝ} (htau0 : 0 ≤ tau) (htau : tau < tau1) :
    CellAt F U Dn (u + tau • d) :=
  cellAt_ray_segment hu htau1 ⟨hU, hDn⟩ htau0 htau

/-- A real affine function `A + tau * B` with `0 < A` has no roots on `(0, tau1)` iff it remains
strictly positive on `[0, tau1)`. -/
theorem pos_of_affine_no_roots {A B tau1 : ℝ} (hA : 0 < A)
    (h_roots : ∀ r, 0 < r → r < tau1 → A + r * B ≠ 0)
    {tau : ℝ} (htau0 : 0 ≤ tau) (htau : tau < tau1) : 0 < A + tau * B := by
  by_contra! hle
  rcases htau0.eq_or_lt with rfl | htau_pos
  · simp only [MulZeroClass.zero_mul, add_zero] at hle; linarith
  · have hB_neg : B < 0 := by
      by_contra! hB_nonneg
      have : 0 ≤ tau * B := mul_nonneg htau_pos.le hB_nonneg
      linarith
    set C := -B
    have hC : 0 < C := by linarith
    have hr_pos : 0 < A / C := div_pos hA hC
    have hr_le : A / C ≤ tau := by
      rw [div_le_iff₀ hC]
      linarith
    have hr_lt : A / C < tau1 := hr_le.trans_lt htau
    have hr_zero : A + (A / C) * B = 0 := by
      have hBC : B = -C := by linarith
      rw [hBC]
      have : (A / C) * -C = -((A / C) * C) := by ring
      rw [this, div_mul_cancel₀ A hC.ne']
      ring
    exact h_roots (A / C) hr_pos hr_lt hr_zero

/-- A real affine function `A + tau * B` with `A < 0` has no roots on `(0, tau1)` iff it remains
strictly negative on `[0, tau1)`. -/
theorem neg_of_affine_no_roots {A B tau1 : ℝ} (hA : A < 0)
    (h_roots : ∀ r, 0 < r → r < tau1 → A + r * B ≠ 0)
    {tau : ℝ} (htau0 : 0 ≤ tau) (htau : tau < tau1) : A + tau * B < 0 := by
  have hpos := pos_of_affine_no_roots (A := -A) (B := -B) (by linarith)
    (fun r hr1 hr2 h => by
      have : A + r * B = 0 := by linarith
      exact h_roots r hr1 hr2 this)
    htau0 htau
  linarith

/-- **Lemma B (root version).**  If `u` is in the open cell and no facing has a root on `(0, tau1)`,
then every intermediate point `u + tau • d` for `0 ≤ tau < tau1` lies in the open cell. -/
theorem cellAt_ray_of_no_roots {F : S0xFac m S x} {U Dn : Finset (Fin m)} {u d : ℝ³}
    (hu : CellAt F U Dn u) {tau1 : ℝ}
    (hU_roots : ∀ t ∈ U, ∀ r, 0 < r → r < tau1 → ⟪F.N t, u + r • d⟫ ≠ 0)
    (hDn_roots : ∀ t ∈ Dn, ∀ r, 0 < r → r < tau1 → ⟪F.N t, u + r • d⟫ ≠ 0)
    {tau : ℝ} (htau0 : 0 ≤ tau) (htau : tau < tau1) :
    CellAt F U Dn (u + tau • d) := by
  have e : ∀ t (s : ℝ), ⟪F.N t, u + s • d⟫ = ⟪F.N t, u⟫ + s * ⟪F.N t, d⟫ := by
    intro t s; rw [inner_add_right, inner_smul_right]
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · rw [e]
    have hU_r : ∀ r, 0 < r → r < tau1 → ⟪F.N t, u⟫ + r * ⟪F.N t, d⟫ ≠ 0 := by
      intro r hr1 hr2
      have := hU_roots t ht r hr1 hr2
      rwa [e] at this
    exact pos_of_affine_no_roots (hu.1 t ht) hU_r htau0 htau
  · rw [e]
    have hDn_r : ∀ r, 0 < r → r < tau1 → ⟪F.N t, u⟫ + r * ⟪F.N t, d⟫ ≠ 0 := by
      intro r hr1 hr2
      have := hDn_roots t ht r hr1 hr2
      rwa [e] at this
    exact neg_of_affine_no_roots (hu.2 t ht) hDn_r htau0 htau

open Minimality.CRay in
/-- **Lemma CR5 (K+), cell hypothesis discharged along a segment.** -/
theorem isRupert_of_cr5_kplus_segment {F : S0xFac m S x} (hx : Function.Injective x)
    {c : ZMod 5 → Fin n} (hc : Function.Injective c) {U Dn : Finset (Fin m)}
    (hcyc : S0xCycUD S c U Dn) {u d : ℝ³} (hu : CellAt F U Dn u)
    {tau1 : ℝ} (htau1 : 0 < tau1) (hw : CellLe F U Dn (u + tau1 • d))
    {tau : ℝ} (htau0 : 0 ≤ tau) (htau : tau < tau1)
    (hKJ : ⟪x (c 2), u + tau • d⟫ < ⟪x (c 0), u + tau • d⟫)
    (hKM : ⟪x (c 3), u + tau • d⟫ < ⟪x (c 0), u + tau • d⟫)
    (hK : ⟪x (c 1), u + tau • d⟫ < ⟪x (c 0), u + tau • d⟫ ∨
          ⟪x (c 4), u + tau • d⟫ < ⟪x (c 0), u + tau • d⟫)
    (hJ0 : (⟪x (c 3), u + tau • d⟫ < ⟪x (c 2), u + tau • d⟫ ∧
            ⟪x (c 2), u + tau • d⟫ < ⟪x (c 1), u + tau • d⟫) ∨
          (⟪x (c 2), u + tau • d⟫ < ⟪x (c 3), u + tau • d⟫ ∧
            ⟪x (c 3), u + tau • d⟫ < ⟪x (c 4), u + tau • d⟫)) :
    IsRupert (Finset.univ.image x) :=
  isRupert_of_cr5_kplus F hx hc hcyc (cellAt_ray_segment hu htau1 hw htau0 htau)
    hKJ hKM hK hJ0

open Minimality.CRay in
/-- **Lemma CR5 (K-), cell hypothesis discharged along a segment.** -/
theorem isRupert_of_cr5_kminus_segment {F : S0xFac m S x} (hx : Function.Injective x)
    {c : ZMod 5 → Fin n} (hc : Function.Injective c) {U Dn : Finset (Fin m)}
    (hcyc : S0xCycUD S c U Dn) {u d : ℝ³} (hu : CellAt F U Dn u)
    {tau1 : ℝ} (htau1 : 0 < tau1) (hw : CellLe F U Dn (u + tau1 • d))
    {tau : ℝ} (htau0 : 0 ≤ tau) (htau : tau < tau1)
    (hKJ : ⟪x (c 0), u + tau • d⟫ < ⟪x (c 2), u + tau • d⟫)
    (hKM : ⟪x (c 0), u + tau • d⟫ < ⟪x (c 3), u + tau • d⟫)
    (hK : ⟪x (c 0), u + tau • d⟫ < ⟪x (c 1), u + tau • d⟫ ∨
          ⟪x (c 0), u + tau • d⟫ < ⟪x (c 4), u + tau • d⟫)
    (hJ0 : (⟪x (c 2), u + tau • d⟫ < ⟪x (c 3), u + tau • d⟫ ∧
            ⟪x (c 1), u + tau • d⟫ < ⟪x (c 2), u + tau • d⟫) ∨
          (⟪x (c 3), u + tau • d⟫ < ⟪x (c 2), u + tau • d⟫ ∧
            ⟪x (c 4), u + tau • d⟫ < ⟪x (c 3), u + tau • d⟫)) :
    IsRupert (Finset.univ.image x) :=
  isRupert_of_cr5_kminus F hx hc hcyc (cellAt_ray_segment hu htau1 hw htau0 htau)
    hKJ hKM hK hJ0

end Minimality.H21
