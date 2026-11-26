module

public import Minimality.Type24HoleAtlas
public import Minimality.EdgePlaneRim4Level
public import Minimality.EdgePlaneLevel
public import Minimality.EdgePlaneLWrap
public import Minimality.Type24NoCoplanar

/-!
# Type 24: atlas facts of the Edge-Plane arrows (2026-11-26)

Contrapositives on `HoleLeaf x F` / `Hole24 x F` of `Split.Rim4.edgePlaneAny_core4`,
`T24.NC.edgePlaneAny_of_strictRim4_level'`, `Split.Level.edgePlaneAny_of_level_extremum` and
`Split.LWrap.edgePlaneAny_of_lwrap_adj_twoRed`, through `holeLeaf_not_edgePlaneAny`.  No new mathematics.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.RimCell Minimality.T24.HC

namespace Minimality.T24.Atlas

variable {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x}

/-- Arrow `Rim4.edgePlaneAny_core4`: at a hole point a generic strict 4-rim view has alternating depths
(the depth 4-cycle is one of the two non-unimodal patterns). -/
theorem holeLeaf_rim4_alternates (h : HoleLeaf x F) (lab : ZMod 4 → Fin 7) (hinj : Function.Injective lab)
    (w : ℝ³) (hR : Split.StrictRimN x w lab)
    (hT : ∀ r : ZMod 4, Split.det3 (x (lab (2 + r)) - x (lab (1 + r))) (x (lab (0 + r)) - x (lab (3 + r))) w ≠ 0)
    (hz : ∀ i j : ZMod 4, i ≠ j → ⟪x (lab i), w⟫ ≠ ⟪x (lab j), w⟫)
    (hre : ∀ a c : ZMod 4, c ≠ a → c ≠ a + 1 → ⟪Split.Rim4.rv x lab a c, w⟫ ≠ 0)
    (hh : ∀ m, (∀ i, m ≠ lab i) →
      ∃ i : ZMod 4, Split.det3 (x (lab (i + 2)) - x (lab i)) (x m - x (lab i)) w ≠ 0) :
    (⟪x (lab 0), w⟫ < ⟪x (lab 1), w⟫ ∧ ⟪x (lab 0), w⟫ < ⟪x (lab 3), w⟫ ∧
      ⟪x (lab 2), w⟫ < ⟪x (lab 1), w⟫ ∧ ⟪x (lab 2), w⟫ < ⟪x (lab 3), w⟫) ∨
    (⟪x (lab 1), w⟫ < ⟪x (lab 0), w⟫ ∧ ⟪x (lab 1), w⟫ < ⟪x (lab 2), w⟫ ∧
      ⟪x (lab 3), w⟫ < ⟪x (lab 0), w⟫ ∧ ⟪x (lab 3), w⟫ < ⟪x (lab 2), w⟫) := by
  by_contra hc
  obtain ⟨hn1, hn2⟩ := not_or.1 hc
  exact holeLeaf_not_edgePlaneAny h (Split.Rim4.edgePlaneAny_core4 x lab hinj w hR hT hz hre hh hn1 hn2)

/-- `Hole24` form of `holeLeaf_rim4_alternates`. -/
theorem hole24_rim4_alternates (h : Hole24 x F) (lab : ZMod 4 → Fin 7) (hinj : Function.Injective lab)
    (w : ℝ³) (hR : Split.StrictRimN x w lab)
    (hT : ∀ r : ZMod 4, Split.det3 (x (lab (2 + r)) - x (lab (1 + r))) (x (lab (0 + r)) - x (lab (3 + r))) w ≠ 0)
    (hz : ∀ i j : ZMod 4, i ≠ j → ⟪x (lab i), w⟫ ≠ ⟪x (lab j), w⟫)
    (hre : ∀ a c : ZMod 4, c ≠ a → c ≠ a + 1 → ⟪Split.Rim4.rv x lab a c, w⟫ ≠ 0)
    (hh : ∀ m, (∀ i, m ≠ lab i) →
      ∃ i : ZMod 4, Split.det3 (x (lab (i + 2)) - x (lab i)) (x m - x (lab i)) w ≠ 0) :
    (⟪x (lab 0), w⟫ < ⟪x (lab 1), w⟫ ∧ ⟪x (lab 0), w⟫ < ⟪x (lab 3), w⟫ ∧
      ⟪x (lab 2), w⟫ < ⟪x (lab 1), w⟫ ∧ ⟪x (lab 2), w⟫ < ⟪x (lab 3), w⟫) ∨
    (⟪x (lab 1), w⟫ < ⟪x (lab 0), w⟫ ∧ ⟪x (lab 1), w⟫ < ⟪x (lab 2), w⟫ ∧
      ⟪x (lab 3), w⟫ < ⟪x (lab 0), w⟫ ∧ ⟪x (lab 3), w⟫ < ⟪x (lab 2), w⟫) :=
  holeLeaf_rim4_alternates h.1 lab hinj w hR hT hz hre hh

/-- Arrow `NC.edgePlaneAny_of_strictRim4_level'`: no strict 4-rim view of a hole point has a level rim edge
(rim image off `badRims`). -/
theorem holeLeaf_no_level4 (h : HoleLeaf x F) (lab : ZMod 4 → Fin 7) (hinj : Function.Injective lab)
    (himg : Finset.univ.image lab ∉ T24.NC.badRims) (w₀ : ℝ³) (hR : Split.StrictRimN x w₀ lab)
    (a : ZMod 4) : ⟪x (lab (a + 1)) - x (lab a), w₀⟫ ≠ 0 := fun hlev =>
  holeLeaf_not_edgePlaneAny h (T24.NC.edgePlaneAny_of_strictRim4_level' F lab hinj himg w₀ hR a hlev)

/-- `Hole24` form of `holeLeaf_no_level4`. -/
theorem hole24_no_level4 (h : Hole24 x F) (lab : ZMod 4 → Fin 7) (hinj : Function.Injective lab)
    (himg : Finset.univ.image lab ∉ T24.NC.badRims) (w₀ : ℝ³) (hR : Split.StrictRimN x w₀ lab)
    (a : ZMod 4) : ⟪x (lab (a + 1)) - x (lab a), w₀⟫ ≠ 0 :=
  holeLeaf_no_level4 h.1 lab hinj himg w₀ hR a

/-- Arrow `Level.edgePlaneAny_of_level_extremum`: at a hole point a level rim edge whose pair is the strict
shallowest or deepest has the L-Wrap sign `0 <= det3 (X a - X (a-1)) (X (a+2) - X (a+1)) w₀`. -/
theorem holeLeaf_level_extremum_wrap (h : HoleLeaf x F) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (lab : ZMod k → Fin 7) (hinj : Function.Injective lab) (w₀ : ℝ³)
    (hR : Split.StrictRimN x w₀ lab) (hH : Split.HiddenInTriangles x w₀ lab) (a : ZMod k)
    (hlev : ⟪x (lab (a + 1)) - x (lab a), w₀⟫ = 0) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (hside : ∀ j, j ≠ a → j ≠ a + 1 → 0 < ε * ⟪x (lab j) - x (lab a), w₀⟫) :
    0 ≤ Split.det3 (x (lab a) - x (lab (a - 1))) (x (lab (a + 2)) - x (lab (a + 1))) w₀ := by
  by_contra hc
  exact holeLeaf_not_edgePlaneAny h
    (Split.Level.edgePlaneAny_of_level_extremum hk x lab hinj w₀ hR hH a hlev ε hε hside (not_le.1 hc))

/-- `Hole24` form of `holeLeaf_level_extremum_wrap`. -/
theorem hole24_level_extremum_wrap (h : Hole24 x F) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (lab : ZMod k → Fin 7) (hinj : Function.Injective lab) (w₀ : ℝ³)
    (hR : Split.StrictRimN x w₀ lab) (hH : Split.HiddenInTriangles x w₀ lab) (a : ZMod k)
    (hlev : ⟪x (lab (a + 1)) - x (lab a), w₀⟫ = 0) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (hside : ∀ j, j ≠ a → j ≠ a + 1 → 0 < ε * ⟪x (lab j) - x (lab a), w₀⟫) :
    0 ≤ Split.det3 (x (lab a) - x (lab (a - 1))) (x (lab (a + 2)) - x (lab (a + 1))) w₀ :=
  holeLeaf_level_extremum_wrap h.1 hk lab hinj w₀ hR hH a hlev ε hε hside

/-- Arrow `LWrap.edgePlaneAny_of_lwrap_adj_twoRed`: under H1a H1b H2a H2b the slope inequality H3 fails at a
hole point, for every `σ`. -/
theorem holeLeaf_lwrap_slope (h : HoleLeaf x F) {k : ℕ} [NeZero k] (hk : 4 ≤ k)
    (lab : ZMod k → Fin 7) (hinj : Function.Injective lab) (w₀ : ℝ³)
    (hrim : Split.StrictRimN x w₀ lab) (hhid : Split.HiddenInTriangles x w₀ lab) (a : ZMod k) (ε : ℝ)
    (H1a : ⟪x (lab (a + 1)) - x (lab a), w₀⟫ = 0)
    (H1b : ∀ j, j ≠ a → j ≠ a + 1 → 0 < ε * ⟪x (lab j) - x (lab (a + 1)), w₀⟫)
    (H2a : 0 < Split.det3 (x (lab a) - x (lab (a - 1))) (x (lab (a + 1 + 1)) - x (lab (a + 1))) w₀)
    (H2b : ∀ i, i ≠ a - 1 → i ≠ a → i ≠ a + 1 →
      Split.det3 (x (lab (i + 1)) - x (lab i)) (x (lab (a + 1 + 1)) - x (lab (a + 1))) w₀ < 0)
    (σ : ℝ) :
    ¬ (∀ i j : ZMod k, i ≠ a - 1 → i ≠ a → i ≠ a + 1 → (j = i ∨ j = i + 1) →
      (σ * Split.LWrap.lwY (fun i => x (lab i)) w₀ (a + 1) (a - 1) (a - 1) -
          max 0 (max (σ * Split.LWrap.lwY (fun i => x (lab i)) w₀ (a + 1) a a)
            (σ * Split.LWrap.lwY (fun i => x (lab i)) w₀ (a + 1) (a - 1) a))) /
        (ε * ⟪x (lab (a - 1)) - x (lab (a + 1)), w₀⟫) <
      (σ * Split.LWrap.lwY (fun i => x (lab i)) w₀ (a + 1) i j -
          max 0 (max (σ * Split.LWrap.lwY (fun i => x (lab i)) w₀ (a + 1) a a)
            (σ * Split.LWrap.lwY (fun i => x (lab i)) w₀ (a + 1) (a - 1) a))) /
        (ε * ⟪x (lab j) - x (lab (a + 1)), w₀⟫)) := fun H3 =>
  holeLeaf_not_edgePlaneAny h
    (Split.LWrap.edgePlaneAny_of_lwrap_adj_twoRed hk x lab hinj w₀ hrim hhid a ε H1a H1b H2a H2b σ H3)

/-- `Hole24` form of `holeLeaf_lwrap_slope`. -/
theorem hole24_lwrap_slope (h : Hole24 x F) {k : ℕ} [NeZero k] (hk : 4 ≤ k)
    (lab : ZMod k → Fin 7) (hinj : Function.Injective lab) (w₀ : ℝ³)
    (hrim : Split.StrictRimN x w₀ lab) (hhid : Split.HiddenInTriangles x w₀ lab) (a : ZMod k) (ε : ℝ)
    (H1a : ⟪x (lab (a + 1)) - x (lab a), w₀⟫ = 0)
    (H1b : ∀ j, j ≠ a → j ≠ a + 1 → 0 < ε * ⟪x (lab j) - x (lab (a + 1)), w₀⟫)
    (H2a : 0 < Split.det3 (x (lab a) - x (lab (a - 1))) (x (lab (a + 1 + 1)) - x (lab (a + 1))) w₀)
    (H2b : ∀ i, i ≠ a - 1 → i ≠ a → i ≠ a + 1 →
      Split.det3 (x (lab (i + 1)) - x (lab i)) (x (lab (a + 1 + 1)) - x (lab (a + 1))) w₀ < 0)
    (σ : ℝ) :
    ¬ (∀ i j : ZMod k, i ≠ a - 1 → i ≠ a → i ≠ a + 1 → (j = i ∨ j = i + 1) →
      (σ * Split.LWrap.lwY (fun i => x (lab i)) w₀ (a + 1) (a - 1) (a - 1) -
          max 0 (max (σ * Split.LWrap.lwY (fun i => x (lab i)) w₀ (a + 1) a a)
            (σ * Split.LWrap.lwY (fun i => x (lab i)) w₀ (a + 1) (a - 1) a))) /
        (ε * ⟪x (lab (a - 1)) - x (lab (a + 1)), w₀⟫) <
      (σ * Split.LWrap.lwY (fun i => x (lab i)) w₀ (a + 1) i j -
          max 0 (max (σ * Split.LWrap.lwY (fun i => x (lab i)) w₀ (a + 1) a a)
            (σ * Split.LWrap.lwY (fun i => x (lab i)) w₀ (a + 1) (a - 1) a))) /
        (ε * ⟪x (lab j) - x (lab (a + 1)), w₀⟫)) :=
  holeLeaf_lwrap_slope h.1 hk lab hinj w₀ hrim hhid a ε H1a H1b H2a H2b σ

end Minimality.T24.Atlas
