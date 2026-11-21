module

public import Minimality.Type24SAT.K24.ParR2

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true

open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.RTope
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.Par

variable {x : Fin 7 → ℝ³}

/-- Rim `6 1 0 5 3`: edges `61` (B up, F down), `10` (B, A), `05` (D, C), `53` (D, G), `36` (I, H). -/
def cT5 : ZMod 5 → Fin 7 := ![6, 1, 0, 5, 3]
def UT5 : Finset (Fin 9) := {1, 3, 8}
def DT5 : Finset (Fin 9) := {0, 2, 5, 6, 7}

theorem injT5 : Function.Injective cT5 := by decide

theorem cycT5 : S0xCycUD s0x_S24 cT5 UT5 DT5 := by decide

/-- **Tope leaf T5** (generic view). At a view `u` with the facets `016, 0345, 346` facing up and
`012, 025, 126, 235, 236` facing down (strictly), and the depths `x1 < x0 < x5 < x3`, the point set
is Rupert (rim `6 1 0 5 3`, depths robustly unimodal, vertex 6 free). -/
theorem leaf_T5 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hA : ⟪F.N 0, u⟫ < 0) (hB : 0 < ⟪F.N 1, u⟫) (hC : ⟪F.N 2, u⟫ < 0)
    (hD : 0 < ⟪F.N 3, u⟫) (hF : ⟪F.N 5, u⟫ < 0) (hG : ⟪F.N 6, u⟫ < 0)
    (hH : ⟪F.N 7, u⟫ < 0) (hI : 0 < ⟪F.N 8, u⟫)
    (h10 : ⟪x 1, u⟫ < ⟪x 0, u⟫) (h05 : ⟪x 0, u⟫ < ⟪x 5, u⟫) (h53 : ⟪x 5, u⟫ < ⟪x 3, u⟫) :
    IsRupert (univ.image x) := by
  have hcell : CellAt F UT5 DT5 u := by
    refine ⟨?_, ?_⟩
    · intro t ht
      simp only [UT5, mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl | rfl <;> assumption
    · intro t ht
      simp only [DT5, mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl <;> assumption
  refine isRupert_of_closedCell (by omega) F (Minimality.H24.SAT.inj_of_fac F) ?_ cycT5 hcell
    hcell.cellLe ?_
  · exact injT5
  · exact robUni_v5d _ (by simpa [cT5] using h10) (by simpa [cT5] using h05) (by simpa [cT5] using h53)

/-- The view built from the three edges at vertex 1 (the frame of the normal form). -/
def vT5 (x : Fin 7 → ℝ³) (a b c : ℝ) : ℝ³ := a • (x 0 - x 1) - b • (x 2 - x 1) + c • (x 6 - x 1)

theorem inner_vT5 (F : S0xFac 9 s0x_S24 x) (t : Fin 9) (a b c : ℝ) :
    ⟪F.N t, vT5 x a b c⟫ = a * (F.f t (x 0) - F.f t (x 1)) - b * (F.f t (x 2) - F.f t (x 1))
      + c * (F.f t (x 6) - F.f t (x 1)) := by
  simp only [vT5, inner_add_right, inner_sub_right, inner_smul_right, F.inner_sub]

/-- **Tope leaf T5, explicit view** `u = a (x0 - x1) - b (x2 - x1) + c (x6 - x1)`, `a, b, c > 0`.
The facings of `012`, `016`, `126` are automatic (each contains two of the three edges at 1); the
remaining five facings and the depth chain `x1 < x0 < x5 < x3` are the testable hypotheses. -/
theorem leaf_T5_frame (F : S0xFac 9 s0x_S24 x) {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hC : ⟪F.N 2, vT5 x a b c⟫ < 0) (hD : 0 < ⟪F.N 3, vT5 x a b c⟫)
    (hG : ⟪F.N 6, vT5 x a b c⟫ < 0) (hH : ⟪F.N 7, vT5 x a b c⟫ < 0)
    (hI : 0 < ⟪F.N 8, vT5 x a b c⟫)
    (h10 : ⟪x 1, vT5 x a b c⟫ < ⟪x 0, vT5 x a b c⟫)
    (h05 : ⟪x 0, vT5 x a b c⟫ < ⟪x 5, vT5 x a b c⟫)
    (h53 : ⟪x 5, vT5 x a b c⟫ < ⟪x 3, vT5 x a b c⟫) :
    IsRupert (univ.image x) := by
  have z0 := fun q (h : q ∈ s0x_S24 0) => F.zero 0 q h
  have z1 := fun q (h : q ∈ s0x_S24 1) => F.zero 1 q h
  have z5 := fun q (h : q ∈ s0x_S24 5) => F.zero 5 q h
  refine leaf_T5 F (u := vT5 x a b c) ?_ ?_ hC hD ?_ hG hH hI h10 h05 h53
  · rw [inner_vT5, z0 0 (by decide), z0 1 (by decide), z0 2 (by decide)]
    have := F.neg 0 6 (by decide); nlinarith
  · rw [inner_vT5, z1 0 (by decide), z1 1 (by decide), z1 6 (by decide)]
    have := F.neg 1 2 (by decide); nlinarith
  · rw [inner_vT5, z5 1 (by decide), z5 2 (by decide), z5 6 (by decide)]
    have := F.neg 5 0 (by decide); nlinarith

end Minimality.T24.RTope
