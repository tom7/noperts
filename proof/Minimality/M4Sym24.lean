module

public import Minimality.Sym24Transport
public import Minimality.M4bType24

/-!
# Type 24 — `(2 6)(4 5)` Frame Transport & Twin Check (Task CC)

Transport lemmas for Type 24 frame coordinates (`det24`, `oblX0`, `oblX2`, `oblX6`,
`omega3`, `omega4`, `omega5`, `Delta24`, `CbarIn`), facet-value / quantity transport
(`sym24_f_apply`, `D45`, `nB`, `nC`, `kappa5`/`kappa4`, `v31`/`v30`), and the derived
edge-`06` twin of `isRupert_of_m4half`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.Sym

open Minimality Minimality.H21 Minimality.H24.SAT Minimality.T24.SAT Minimality.T24.RCell
  Minimality.T24.M4 Minimality.T24.A7

/-! ### Frame Coordinate Transport under `x ∘ pi24` -/

@[simp] theorem pi24_0 : pi24 0 = 0 := by decide
@[simp] theorem pi24_1 : pi24 1 = 1 := by decide
@[simp] theorem pi24_2 : pi24 2 = 6 := by decide
@[simp] theorem pi24_3 : pi24 3 = 3 := by decide
@[simp] theorem pi24_4 : pi24 4 = 5 := by decide
@[simp] theorem pi24_5 : pi24 5 = 4 := by decide
@[simp] theorem pi24_6 : pi24 6 = 2 := by decide

@[simp] theorem sig24_0 : sig24 0 = 1 := by decide
@[simp] theorem sig24_1 : sig24 1 = 0 := by decide
@[simp] theorem sig24_2 : sig24 2 = 4 := by decide
@[simp] theorem sig24_3 : sig24 3 = 3 := by decide
@[simp] theorem sig24_4 : sig24 4 = 2 := by decide
@[simp] theorem sig24_5 : sig24 5 = 5 := by decide
@[simp] theorem sig24_6 : sig24 6 = 8 := by decide
@[simp] theorem sig24_7 : sig24 7 = 7 := by decide
@[simp] theorem sig24_8 : sig24 8 = 6 := by decide

theorem det24_comp_pi24 (x : Fin 7 → ℝ³) :
    det24 (x ∘ pi24) = -det24 x := by
  simp only [det24, Function.comp_apply, pi24_0, pi24_1, pi24_2, pi24_6, vol3]
  ring

theorem oblX0_comp_pi24 (x : Fin 7 → ℝ³) (v : Fin 7) :
    oblX0 (x ∘ pi24) v = oblX0 x (pi24 v) := by
  simp only [oblX0, det24_comp_pi24, Function.comp_apply, pi24_1, pi24_2, pi24_6]
  have h : vol3 (x (pi24 v) - x 1) (x 6 - x 1) (x 2 - x 1) =
      -vol3 (x (pi24 v) - x 1) (x 2 - x 1) (x 6 - x 1) := by
    simp only [vol3]; ring
  rw [h, neg_div_neg_eq]

theorem oblX2_comp_pi24 (x : Fin 7 → ℝ³) (v : Fin 7) :
    oblX2 (x ∘ pi24) v = oblX6 x (pi24 v) := by
  simp only [oblX2, oblX6, det24_comp_pi24, Function.comp_apply, pi24_0, pi24_1, pi24_6]
  have h : vol3 (x 0 - x 1) (x (pi24 v) - x 1) (x 2 - x 1) =
      -vol3 (x 0 - x 1) (x 2 - x 1) (x (pi24 v) - x 1) := by
    simp only [vol3]; ring
  rw [h, neg_div_neg_eq]

theorem oblX6_comp_pi24 (x : Fin 7 → ℝ³) (v : Fin 7) :
    oblX6 (x ∘ pi24) v = oblX2 x (pi24 v) := by
  simp only [oblX6, oblX2, det24_comp_pi24, Function.comp_apply, pi24_0, pi24_1, pi24_2]
  have h : vol3 (x 0 - x 1) (x 6 - x 1) (x (pi24 v) - x 1) =
      -vol3 (x 0 - x 1) (x (pi24 v) - x 1) (x 6 - x 1) := by
    simp only [vol3]; ring
  rw [h, neg_div_neg_eq]

theorem omega3_comp_pi24 (x : Fin 7 → ℝ³) :
    omega3 (x ∘ pi24) = omega3 x := by
  simp only [omega3, oblX0_comp_pi24, oblX2_comp_pi24, oblX6_comp_pi24, pi24_3]
  ring

theorem omega4_comp_pi24 (x : Fin 7 → ℝ³) :
    omega4 (x ∘ pi24) = omega5 x := by
  simp only [omega4, omega5, oblX0_comp_pi24, oblX2_comp_pi24, oblX6_comp_pi24, pi24_4]

theorem omega5_comp_pi24 (x : Fin 7 → ℝ³) :
    omega5 (x ∘ pi24) = omega4 x := by
  simp only [omega5, omega4, oblX0_comp_pi24, oblX2_comp_pi24, oblX6_comp_pi24, pi24_5]

theorem Delta24_comp_pi24 (x : Fin 7 → ℝ³) :
    Delta24 (x ∘ pi24) = Delta24 x := by
  simp only [Delta24, omega3_comp_pi24, omega4_comp_pi24, omega5_comp_pi24]
  ring

theorem cbarIn_comp_pi24 (x : Fin 7 → ℝ³) :
    CbarIn (x ∘ pi24) ↔ CbarIn x := by
  simp only [CbarIn, omega3_comp_pi24, omega4_comp_pi24, omega5_comp_pi24, Delta24_comp_pi24]
  tauto

/-! ### Facet-Value and Quantity Transport -/

@[simp] theorem sym24_f_apply {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : Fin 9) (v : Fin 7) :
    (sym24 F).f t ((x ∘ pi24) v) = F.f (sig24 t) (x (pi24 v)) := rfl

theorem d45_comp_pi24 (x : Fin 7 → ℝ³) :
    D45 (x ∘ pi24) = D45 x := by
  simp only [D45, oblX2_comp_pi24, oblX6_comp_pi24, pi24_4, pi24_5]
  ring

theorem nB_comp_pi24 (x : Fin 7 → ℝ³) :
    nB (x ∘ pi24) = nC x := by
  simp only [nB, nC, oblX0_comp_pi24, oblX6_comp_pi24, pi24_4, pi24_5]

theorem nC_comp_pi24 (x : Fin 7 → ℝ³) :
    nC (x ∘ pi24) = nB x := by
  simp only [nC, nB, oblX0_comp_pi24, oblX2_comp_pi24, pi24_4, pi24_5]

/-- Twin of `kappa5` for the `(2 6)(4 5)` mirror (`06` edge). -/
noncomputable def kappa4 (x : Fin 7 → ℝ³) : ℝ :=
  oblX2 x 3 * (omega3 x * oblX0 x 4 - oblX6 x 4) + oblX2 x 4 * (1 - oblX2 x 3)

theorem kappa5_comp_pi24 (x : Fin 7 → ℝ³) :
    kappa5 (x ∘ pi24) = kappa4 x := by
  simp only [kappa5, kappa4, oblX0_comp_pi24, oblX2_comp_pi24, oblX6_comp_pi24,
    omega3_comp_pi24, pi24_3, pi24_5]

theorem v31_comp_pi24 (x : Fin 7 → ℝ³) :
    v31 (x ∘ pi24) = v30 x := by
  simp only [v31, v30, nC_comp_pi24, d45_comp_pi24, Function.comp_apply, pi24_0, pi24_1, pi24_6]

theorem v30_comp_pi24 (x : Fin 7 → ℝ³) :
    v30 (x ∘ pi24) = v31 x := by
  simp only [v30, v31, nB_comp_pi24, d45_comp_pi24, Function.comp_apply, pi24_0, pi24_1, pi24_2]

/-! ### Twin Check: Edge-`06` Mirror of `m4half` and `isRupert_of_m4half` -/

theorem m4half_twin {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (hac : ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0)
    (h235 : F.f 6 (x 6) < F.f 6 (x 0)) (hb3 : oblX2 x 3 < 1) (hk4 : kappa4 x < 0)
    (hL : ¬ LexAny F) (hS : ¬ SplitAny24 F) :
    0 ≤ ⟪x 2 - x 6, x 6 - x 0⟫ := by
  have hm := m4half (sym24 F)
    ((cbarIn_comp_pi24 x).2 hC)
    (by simpa [Function.comp_apply] using hac)
    (by simpa [sym24_f_apply] using h235)
    (by simpa [oblX6_comp_pi24] using hb3)
    (by simpa [kappa5_comp_pi24] using hk4)
    (fun h => hL (lexAny_sym F h))
    (fun h => hS (splitAny24_sym F h))
  simpa [Function.comp_apply] using hm

theorem isRupert_of_m4half_twin {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hC : CbarIn x) (hac : ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0)
    (h235 : F.f 6 (x 6) < F.f 6 (x 0)) (hb3 : oblX2 x 3 < 1) (hk4 : kappa4 x < 0)
    (hz : ⟪x 2 - x 6, x 6 - x 0⟫ < 0) :
    IsRupert (univ.image x) :=
  isRupert_of_comp_pi24 (isRupert_of_m4half (sym24 F)
    ((cbarIn_comp_pi24 x).2 hC)
    (by simpa [Function.comp_apply] using hac)
    (by simpa [sym24_f_apply] using h235)
    (by simpa [oblX6_comp_pi24] using hb3)
    (by simpa [kappa5_comp_pi24] using hk4)
    (by simpa [Function.comp_apply] using hz))

end Minimality.T24.Sym
