module

public import Minimality.Type24TwoCone

/-!
# `T_0`-family leaf in line-separation form (`FP1`–`FP2`)

* `FP1`, `FP2`: the line-separation leaf `fam_edgePlaneAny_core` / `famA_edgePlaneAny` /
  `famB_edgePlaneAny`, the hole facts and `TwoConeResidue'` were deleted (11-27 pass 2); what
  remains is `FamACertAt` / `FamBCertAt` and their helpers (cell translations `famACert_cellCert`).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace Topology
open Finset Filter
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.M4
open Minimality.T24.HC Minimality.T24.SF Minimality.T24.DeepC

namespace Minimality.T24.TwoCone

/-! ## FP2: Hole facts and `TwoConeResidue'` -/

/-- `FamACertAt x F x0`: `InI5 x x0`, `patA` (`h6 > 0, h8 < 0`), `hhid4` at `uB x x0`, and
strict line separation at `uB x x0` on some edge `a : ZMod 5` of `cA`. -/
def FamACertAt (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) (x0 : ℝ) : Prop :=
  InI5 x x0 ∧ 0 < ⟪F.N 6, uB x x0⟫ ∧ ⟪F.N 8, uB x x0⟫ < 0 ∧
  (∃ p ∈ ({1, 2, 5, 3, 6} : Finset (Fin 7)).image x,
    ∃ q ∈ ({1, 2, 5, 3, 6} : Finset (Fin 7)).image x,
    ∃ r ∈ ({1, 2, 5, 3, 6} : Finset (Fin 7)).image x,
    0 < Split.det3 (q - p) (r - p) (uB x x0) ∧ 0 < Split.det3 (q - p) (x 4 - p) (uB x x0) ∧
    0 < Split.det3 (r - q) (x 4 - q) (uB x x0) ∧ 0 < Split.det3 (p - r) (x 4 - r) (uB x x0)) ∧
  ∃ a : ZMod 5,
    ⟪x (cA (a + 1)) - x (cA a), uB x x0⟫ ≠ 0 ∧
    (∀ i : ZMod 5, i ≠ a →
      Split.det3 (x (cA (i + 1)) - x (cA i)) (x (cA (a + 1)) - x (cA a)) (uB x x0) ≠ 0) ∧
    ∃ sh α' μ' : ℝ, (sh = 1 ∨ sh = -1) ∧
      (∀ i j : ZMod 5, i ≠ a → (j = i ∨ j = i + 1) →
        0 < Split.det3 (x (cA (i + 1)) - x (cA i)) (x (cA (a + 1)) - x (cA a)) (uB x x0) →
        (-sh * ⟪Split.Slope.linSpinVec (fun t => x (cA t)) a i j, uB x x0⟫ /
            Split.det3 (x (cA (i + 1)) - x (cA i)) (x (cA (a + 1)) - x (cA a)) (uB x x0)) -
          μ' * ⟪x (cA j) - x (cA a), uB x x0⟫ < α') ∧
      (∀ p q : ZMod 5, p ≠ a → (q = p ∨ q = p + 1) →
        Split.det3 (x (cA (p + 1)) - x (cA p)) (x (cA (a + 1)) - x (cA a)) (uB x x0) < 0 →
        α' < (-sh * ⟪Split.Slope.linSpinVec (fun t => x (cA t)) a p q, uB x x0⟫ /
            Split.det3 (x (cA (p + 1)) - x (cA p)) (x (cA (a + 1)) - x (cA a)) (uB x x0)) -
          μ' * ⟪x (cA q) - x (cA a), uB x x0⟫)

/-- `FamBCertAt x F x0`: `InI5 x x0`, `patB` (`h6 > 0, h8 > 0`), and strict line separation at
`uB x x0` on some edge `a : ZMod 6` of `cB`. -/
def FamBCertAt (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) (x0 : ℝ) : Prop :=
  InI5 x x0 ∧ 0 < ⟪F.N 6, uB x x0⟫ ∧ 0 < ⟪F.N 8, uB x x0⟫ ∧
  ∃ a : ZMod 6,
    ⟪x (cB (a + 1)) - x (cB a), uB x x0⟫ ≠ 0 ∧
    (∀ i : ZMod 6, i ≠ a →
      Split.det3 (x (cB (i + 1)) - x (cB i)) (x (cB (a + 1)) - x (cB a)) (uB x x0) ≠ 0) ∧
    ∃ sh α' μ' : ℝ, (sh = 1 ∨ sh = -1) ∧
      (∀ i j : ZMod 6, i ≠ a → (j = i ∨ j = i + 1) →
        0 < Split.det3 (x (cB (i + 1)) - x (cB i)) (x (cB (a + 1)) - x (cB a)) (uB x x0) →
        (-sh * ⟪Split.Slope.linSpinVec (fun t => x (cB t)) a i j, uB x x0⟫ /
            Split.det3 (x (cB (i + 1)) - x (cB i)) (x (cB (a + 1)) - x (cB a)) (uB x x0)) -
          μ' * ⟪x (cB j) - x (cB a), uB x x0⟫ < α') ∧
      (∀ p q : ZMod 6, p ≠ a → (q = p ∨ q = p + 1) →
        Split.det3 (x (cB (p + 1)) - x (cB p)) (x (cB (a + 1)) - x (cB a)) (uB x x0) < 0 →
        α' < (-sh * ⟪Split.Slope.linSpinVec (fun t => x (cB t)) a p q, uB x x0⟫ /
            Split.det3 (x (cB (p + 1)) - x (cB p)) (x (cB (a + 1)) - x (cB a)) (uB x x0)) -
          μ' * ⟪x (cB q) - x (cB a), uB x x0⟫)

/-! ## FQ1: `π_24` twins of `famA` / `famB` and `TwoConeResidue''` -/

/-! ## FQ2: `T_0` rim determinants (`cA = ![1, 2, 5, 3, 6]`, edge `3 → 6`, Lemma T1) -/

/-- `γ_0(x0) := (1 - x0) / ω_5(x)` used in `uB x x0`. -/
noncomputable def gamma0 (x : Fin 7 → ℝ³) (x0 : ℝ) : ℝ := (1 - x0) / omega5 x

/-- `τ_1(x0)` (`2 → 5` determinant factor). -/
noncomputable def tau1 (x : Fin 7 → ℝ³) (x0 : ℝ) : ℝ :=
  -oblX0 x 5 * (1 - oblX6 x 3 + oblX2 x 3 * gamma0 x x0) +
    (oblX2 x 5 - 1) * (Hh x x0 (gamma0 x x0) 3 - x0) -
    oblX6 x 5 * (oblX0 x 3 + oblX2 x 3 * x0)

end Minimality.T24.TwoCone
