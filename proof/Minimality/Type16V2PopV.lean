module

public import Minimality.Type16V2PopT

@[expose] public section

/-!
# V2: the four quad-triangle vertex views as pop cells (statements for type 16)

Views `popTab`: `AE` (P = A, Q = E, w = 0, far 5), `AF` (A, F, 5, far 0), `BE` (B, E, 6, far 5), `BH` (B, H, 5, far 6).
-/

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped RealInnerProductSpace
open Finset Filter

namespace Minimality
namespace V2
open Type08Sp Type08Sp.C2

variable {x : Fin 7 → ℝ³}

/-- The ring points `(m1, m2)` of the quadrilateral `P` (`A`: `3, 2`; `B`: `3, 1`) on the two sides of the diagonal. -/
def ringPts (P : Fin 8) : Fin 7 × Fin 7 := if P = 0 then (3, 2) else (3, 1)

/-- `(P, Q, w, far)` of the four quadrilateral-triangle vertex views AE, AF, BE, BH. -/
def popTab : Fin 4 → Fin 8 × Fin 8 × Fin 7 × Fin 7 := ![(0, 4, 0, 5), (0, 5, 5, 0), (1, 4, 6, 5), (1, 7, 5, 6)]

/-- The pop cell at `(P, Q, w, a)`: far vertex `a` opposite `w` in the quadrilateral, far `b` of the triangle `Q`,
edge facet `eQ`. -/
def FreePopAt (T : Type16 x) (P Q eQ : Fin 8) (w a b : Fin 7) : Prop :=
  ((P = 0 ∧ ((w = 0 ∧ a = 5) ∨ (w = 5 ∧ a = 0))) ∨ (P = 1 ∧ ((w = 5 ∧ a = 6) ∨ (w = 6 ∧ a = 5)))) ∧
  PopCond T P Q eQ w a b (ringPts P).1 (ringPts P).2

theorem popAt_cell (T : Type16 x) {P Q eQ : Fin 8} {w a b : Fin 7} (h : FreePopAt T P Q eQ w a b)
    {r : ℝ³} (hr : r ≠ 0) (hPr : ⟪T.fN P, r⟫ = 0) (hQr : ⟪T.fN Q, r⟫ = 0)
    (hD : DepthOK5 x r w a b (ringPts P).1 (ringPts P).2) : HasLexCellAt (univ.image x) r := by
  obtain ⟨hdiag, hc⟩ := h
  rcases hdiag with ⟨rfl, hwa⟩ | ⟨rfl, hwa⟩
  · -- P = A
    have F := popG_facts T 1 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have g2 : 0 < popG T 1 0 (x 2) := by
      have := T.coords0235.2.2.1
      have e : popG T 1 0 (x 2) = T.q1356.f (x 2) / T.q1356.f (x 0) + T.t036.f (x 2) / T.t036.f (x 5) - 1 := rfl
      rw [e]; linarith
    have hring : ringPts 0 = (3, 2) := by simp [ringPts]
    rw [hring] at hc hD
    rcases hwa with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact popCond_cell T hc (popG T 1 0) (popN T 1 0) (popG_hN T 1 0) F.1 F.2.1 (by simp only [F.2.2]; norm_num) g2
        hr hPr hQr hD
    · exact popCond_cell T hc (popG T 1 0) (popN T 1 0) (popG_hN T 1 0) F.2.1 F.1 (by simp only [F.2.2]; norm_num) g2
        hr hPr hQr hD
  · -- P = B
    have F := popG_facts T 0 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have g1 : 0 < popG T 0 6 (x 1) := by
      have := T.coords1356.2.2.1
      have e : popG T 0 6 (x 1) = T.q0235.f (x 1) / T.q0235.f (x 6) + T.t036.f (x 1) / T.t036.f (x 5) - 1 := rfl
      rw [e]; linarith
    have hring : ringPts 1 = (3, 1) := by simp [ringPts]
    rw [hring] at hc hD
    rcases hwa with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact popCond_cell T hc (popG T 0 6) (popN T 0 6) (popG_hN T 0 6) F.2.1 F.1 (by simp only [F.2.2]; norm_num) g1
        hr hPr hQr hD
    · exact popCond_cell T hc (popG T 0 6) (popN T 0 6) (popG_hN T 0 6) F.1 F.2.1 (by simp only [F.2.2]; norm_num) g1
        hr hPr hQr hD

/-- The pop cell at the `k`-th quad-triangle view (`popTab`), with the depth condition for all view directions. -/
def FreePop16D (T : Type16 x) (k : Fin 4) : Prop :=
  ∃ eQ b, FreePopAt T (popTab k).1 (popTab k).2.1 eQ (popTab k).2.2.1 (popTab k).2.2.2 b ∧
    ∀ r : ℝ³, r ≠ 0 → ⟪T.fN (popTab k).1, r⟫ = 0 → ⟪T.fN (popTab k).2.1, r⟫ = 0 →
      DepthOK5 x r (popTab k).2.2.1 (popTab k).2.2.2 b (ringPts (popTab k).1).1 (ringPts (popTab k).1).2

theorem freePop16_hasLexCell (T : Type16 x) (k : Fin 4) (h : FreePop16D T k) : HasLexCell (univ.image x) := by
  obtain ⟨eQ, b, hf, hd⟩ := h
  obtain ⟨r, hr, h1, h2⟩ := exists_kernel2 (T.fN (popTab k).1) (T.fN (popTab k).2.1)
  exact ⟨r, hr, popAt_cell T hf hr h1 h2 (hd r hr h1 h2)⟩

theorem freePop16_isRupert (T : Type16 x) (k : Fin 4) (h : FreePop16D T k) : IsRupert (univ.image x) :=
  isRupert_of_hasLexCell _ (freePop16_hasLexCell T k h)

end V2
end Minimality
