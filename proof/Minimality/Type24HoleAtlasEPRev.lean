module

public import Minimality.Type24HoleAtlas
public import Minimality.EdgePlaneRim4Level
public import Minimality.EdgePlaneLevel
public import Minimality.EdgePlaneLWrap
public import Minimality.Type24NoCoplanar
public import Minimality.EdgePlaneRev

/-!
# Type 24: atlas facts of the twoBlue L-Wrap arrow (2026-11-26)

Contrapositives on `HoleLeaf x F` / `Hole24 x F` of
`Split.Rev.edgePlaneAny_of_lwrap_adj_twoBlue` (certifying Edge-Plane at the adjacent edge `a - 1`
with zero tilt), through `holeLeaf_not_edgePlaneAny`.  No new mathematics.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.RimCell Minimality.T24.HC

namespace Minimality.T24.Atlas

variable {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x}

/-- Arrow `Split.Rev.edgePlaneAny_of_lwrap_adj_twoBlue`: at a hole point, under `H1a`
(`⟪x (lab (a + 1)) - x (lab a), w₀⟫ = 0`), `H1b` (`0 < ε * ⟪x (lab j) - x (lab a), w₀⟫` for
`j ∉ {a, a + 1}`), `H2a` (`0 < det3 E_{a-1} E_{a+1} w₀`), and `H2b`
(`0 < det3 E_i E_{a-1} w₀` for `i ∉ {a - 1, a, a + 1}`), the slope inequality `H3` at edge
`a - 1` fails for every `σ`. -/
theorem holeLeaf_lwrap_slope_twoBlue (h : HoleLeaf x F) {k : ℕ} [NeZero k] (hk : 4 ≤ k)
    (lab : ZMod k → Fin 7) (hinj : Function.Injective lab) (w₀ : ℝ³)
    (hrim : Split.StrictRimN x w₀ lab) (hhid : Split.HiddenInTriangles x w₀ lab) (a : ZMod k)
    (ε : ℝ)
    (H1a : ⟪x (lab (a + 1)) - x (lab a), w₀⟫ = 0)
    (H1b : ∀ j, j ≠ a → j ≠ a + 1 → 0 < ε * ⟪x (lab j) - x (lab a), w₀⟫)
    (H2a : 0 < Split.det3 (x (lab a) - x (lab (a - 1))) (x (lab (a + 1 + 1)) - x (lab (a + 1))) w₀)
    (H2b : ∀ i, i ≠ a - 1 → i ≠ a → i ≠ a + 1 →
      0 < Split.det3 (x (lab (i + 1)) - x (lab i)) (x (lab a) - x (lab (a - 1))) w₀)
    (σ : ℝ) :
    ¬ (∀ i j : ZMod k, i ≠ a - 1 → i ≠ a → i ≠ a + 1 → (j = i ∨ j = i + 1) →
      (σ * Split.LWrap.lwY (fun i => x (lab i)) w₀ (a - 1) (a + 1) (a + 1 + 1) -
          max 0 (max (σ * Split.LWrap.lwY (fun i => x (lab i)) w₀ (a - 1) a (a + 1))
            (σ * Split.LWrap.lwY (fun i => x (lab i)) w₀ (a - 1) (a + 1) (a + 1)))) /
        (ε * ⟪x (lab (a + 1 + 1)) - x (lab a), w₀⟫) <
      (σ * Split.LWrap.lwY (fun i => x (lab i)) w₀ (a - 1) i j -
          max 0 (max (σ * Split.LWrap.lwY (fun i => x (lab i)) w₀ (a - 1) a (a + 1))
            (σ * Split.LWrap.lwY (fun i => x (lab i)) w₀ (a - 1) (a + 1) (a + 1)))) /
        (ε * ⟪x (lab j) - x (lab a), w₀⟫)) := fun H3 =>
  holeLeaf_not_edgePlaneAny h
    (Split.Rev.edgePlaneAny_of_lwrap_adj_twoBlue hk x lab hinj w₀ hrim hhid a ε H1a H1b H2a H2b σ H3)

/-- `Hole24` form of `holeLeaf_lwrap_slope_twoBlue` (arrow
`Split.Rev.edgePlaneAny_of_lwrap_adj_twoBlue`, certifying at edge `a - 1` under the same sign
conditions `H1a`, `H1b`, `H2a`, `H2b`). -/
theorem hole24_lwrap_slope_twoBlue (h : Hole24 x F) {k : ℕ} [NeZero k] (hk : 4 ≤ k)
    (lab : ZMod k → Fin 7) (hinj : Function.Injective lab) (w₀ : ℝ³)
    (hrim : Split.StrictRimN x w₀ lab) (hhid : Split.HiddenInTriangles x w₀ lab) (a : ZMod k)
    (ε : ℝ)
    (H1a : ⟪x (lab (a + 1)) - x (lab a), w₀⟫ = 0)
    (H1b : ∀ j, j ≠ a → j ≠ a + 1 → 0 < ε * ⟪x (lab j) - x (lab a), w₀⟫)
    (H2a : 0 < Split.det3 (x (lab a) - x (lab (a - 1))) (x (lab (a + 1 + 1)) - x (lab (a + 1))) w₀)
    (H2b : ∀ i, i ≠ a - 1 → i ≠ a → i ≠ a + 1 →
      0 < Split.det3 (x (lab (i + 1)) - x (lab i)) (x (lab a) - x (lab (a - 1))) w₀)
    (σ : ℝ) :
    ¬ (∀ i j : ZMod k, i ≠ a - 1 → i ≠ a → i ≠ a + 1 → (j = i ∨ j = i + 1) →
      (σ * Split.LWrap.lwY (fun i => x (lab i)) w₀ (a - 1) (a + 1) (a + 1 + 1) -
          max 0 (max (σ * Split.LWrap.lwY (fun i => x (lab i)) w₀ (a - 1) a (a + 1))
            (σ * Split.LWrap.lwY (fun i => x (lab i)) w₀ (a - 1) (a + 1) (a + 1)))) /
        (ε * ⟪x (lab (a + 1 + 1)) - x (lab a), w₀⟫) <
      (σ * Split.LWrap.lwY (fun i => x (lab i)) w₀ (a - 1) i j -
          max 0 (max (σ * Split.LWrap.lwY (fun i => x (lab i)) w₀ (a - 1) a (a + 1))
            (σ * Split.LWrap.lwY (fun i => x (lab i)) w₀ (a - 1) (a + 1) (a + 1)))) /
        (ε * ⟪x (lab j) - x (lab a), w₀⟫)) :=
  holeLeaf_lwrap_slope_twoBlue h.1 hk lab hinj w₀ hrim hhid a ε H1a H1b H2a H2b σ

end Minimality.T24.Atlas
