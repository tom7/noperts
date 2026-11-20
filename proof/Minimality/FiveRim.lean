module

public import Mathlib
public import Minimality.DiagCross
public import Minimality.SlideDS
public import Minimality.Thm73

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped RealInnerProductSpace
open Minimality Minimality.T24.Q45

namespace Minimality

/-!
# Task AI: Theorem K5 and Theorem K5-DS (Universal 5-Rim Tools)

This module formalizes:
1. `StrictConvex5` and `subquad`: Strict convexity of 5-cycles along view `u` with
   orientation `ρ`, and deletion of corner `m : ZMod 5` to obtain a 4-sub-quad.
2. `subquad_strictConvex`: Sub-quad convexity inheritance lemma (deleting any corner
   of a strictly convex 5-cycle preserves strict convexity with the same `ρ`).
3. `Theorem K5` (`fiveRim_structure`, `fiveRim_unimodal_of_subquads`):
   Every injective non-unimodal 5-cycle has a unique monotone corner `M` whose deletion
   leaves a strictly alternating 4-sub-quad. DiagCross (`Lemma K`) refutes non-unimodality
   when each sub-quad forbids the alternation that would occur at `m`.
4. `Theorem K5-DS` (`depthClause_k5_iff`, `depthSepAt_k5_iff`):
   Characterization of `DepthSepAt` on the two-peaked 5-cycle `(P1, V1, P2, M, V2)`:
   corner `M` satisfies the depth clause of `DepthSepAt` iff `z M < z V1` (edge `[V2, P1]`)
   or `z P1 < z M` (edge `[V1, P2]`).
-/

/-! ### Definitions for 5-Cycles and Sub-Quads -/

/-- Strict convexity of a 5-cycle along view `u` with orientation `ρ`
(non-adjacent vertex determinant test). -/
def StrictConvex5 (p : ZMod 5 → ℝ³) (u : ℝ³) (ρ : ℝ) : Prop :=
  ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 → 0 < ρ * det3 (p (i + 1) - p i) (p j - p i) u

/-- Strict convexity of a 4-cycle along view `u` with orientation `ρ`
(corner triangle test). -/
def StrictConvex4 (q : ZMod 4 → ℝ³) (u : ℝ³) (ρ : ℝ) : Prop :=
  ∀ i : ZMod 4, 0 < ρ * triD q u i

/-- The 4-sub-quad obtained by deleting vertex `m : ZMod 5` from a 5-cycle `p`,
preserving cyclic order: corners `m+1, m+2, m+3, m+4`. -/
def subquad (p : ZMod 5 → ℝ³) (m : ZMod 5) : ZMod 4 → ℝ³ :=
  fun j => p (m + 1 + (j.val : ZMod 5))

/-- The DiagCross determinant invariant `κ` of a 4-cycle `q`. -/
noncomputable def quadKappa (q : ZMod 4 → ℝ³) : ℝ :=
  det3 (q 2 - q 0) (q 3 - q 1) (q 0 - q 1)

/-- Strict alternation where odd corners `{1, 3}` are strictly below even corners `{0, 2}`.
Ruled out by `diagCross_not_high` when `ρ * κ < 0`. -/
def QuadOddBelowEven (q : ZMod 4 → ℝ³) (u : ℝ³) : Prop :=
  max ⟪q 1, u⟫ ⟪q 3, u⟫ < min ⟪q 0, u⟫ ⟪q 2, u⟫

/-- Strict alternation where even corners `{0, 2}` are strictly below odd corners `{1, 3}`.
Ruled out by `diagCross_not_low` when `0 < ρ * κ`. -/
def QuadEvenBelowOdd (q : ZMod 4 → ℝ³) (u : ℝ³) : Prop :=
  max ⟪q 0, u⟫ ⟪q 2, u⟫ < min ⟪q 1, u⟫ ⟪q 3, u⟫

/-- A corner `m : ZMod 5` is monotone along `z` if the depth increments into and out of `m`
have the same sign, i.e. `z m` is strictly between `z (m - 1)` and `z (m + 1)`. -/
def IsMonotoneCorner (z : ZMod 5 → ℝ) (m : ZMod 5) : Prop :=
  (z (m - 1) < z m ∧ z m < z (m + 1)) ∨ (z (m + 1) < z m ∧ z m < z (m - 1))

/-- The specific strict alternation associated with a monotone corner `m`:
- If increasing through `m`, odd corners are below even corners (`QuadOddBelowEven`).
- If decreasing through `m`, even corners are below odd corners (`QuadEvenBelowOdd`). -/
def MonotoneAlternation (p : ZMod 5 → ℝ³) (u : ℝ³) (m : ZMod 5) : Prop :=
  (⟪p (m - 1), u⟫ < ⟪p m, u⟫ ∧ ⟪p m, u⟫ < ⟪p (m + 1), u⟫ ∧ QuadOddBelowEven (subquad p m) u) ∨
  (⟪p (m + 1), u⟫ < ⟪p m, u⟫ ∧ ⟪p m, u⟫ < ⟪p (m - 1), u⟫ ∧ QuadEvenBelowOdd (subquad p m) u)

/-- A sub-quad `subquad p m` rules out corner `m` from being monotone along `u`:
- If `z` increases through `m`, the resulting odd-below-even alternation is refuted.
- If `z` decreases through `m`, the resulting even-below-odd alternation is refuted. -/
def SubquadRulesOut (p : ZMod 5 → ℝ³) (u : ℝ³) (m : ZMod 5) : Prop :=
  (⟪p (m - 1), u⟫ < ⟪p m, u⟫ ∧ ⟪p m, u⟫ < ⟪p (m + 1), u⟫ → ¬ QuadOddBelowEven (subquad p m) u) ∧
  (⟪p (m + 1), u⟫ < ⟪p m, u⟫ ∧ ⟪p m, u⟫ < ⟪p (m - 1), u⟫ → ¬ QuadEvenBelowOdd (subquad p m) u)

/-! ### Sub-quad Convexity Inheritance Lemma -/

theorem det3_cycle_triangle (a b c u : ℝ³) :
    det3 (b - a) (c - a) u = det3 (c - b) (a - b) u := by
  simp only [det3_expand, PiLp.sub_apply]
  ring

/-- **Sub-quad Convexity Inheritance**.
Deleting any vertex `m` of a strictly convex 5-cycle leaves a strictly convex
4-cycle with the same view `u` and orientation `ρ`. -/
theorem subquad_strictConvex (p : ZMod 5 → ℝ³) (u : ℝ³) (ρ : ℝ)
    (hcvx : StrictConvex5 p u ρ) (m : ZMod 5) :
    StrictConvex4 (subquad p m) u ρ := by
  intro i
  fin_cases i
  · -- i = 0: corners m+1, m+2, m+3
    change 0 < ρ * det3 (p (m + 1 + ((1 : ZMod 4).val : ZMod 5)) - p (m + 1 + ((0 : ZMod 4).val : ZMod 5)))
      (p (m + 1 + ((2 : ZMod 4).val : ZMod 5)) - p (m + 1 + ((0 : ZMod 4).val : ZMod 5))) u
    have h0 : ((0 : ZMod 4).val : ZMod 5) = 0 := rfl
    have h1 : ((1 : ZMod 4).val : ZMod 5) = 1 := rfl
    have h2 : ((2 : ZMod 4).val : ZMod 5) = 2 := rfl
    rw [h0, h1, h2, add_zero]
    have h_adj1 : (m + 1 + 1 : ZMod 5) = (m + 1) + 1 := rfl
    rw [h_adj1]
    have hj_ne1 : (m + 1 + 2 : ZMod 5) ≠ m + 1 := by
      intro h
      have : (2 : ZMod 5) = 0 := by
        calc (2 : ZMod 5) = (m + 1 + 2) - (m + 1) := by ring
        _ = (m + 1) - (m + 1) := by rw [h]
        _ = 0 := sub_self _
      revert this; decide
    have hj_ne2 : (m + 1 + 2 : ZMod 5) ≠ (m + 1) + 1 := by
      intro h
      have : (1 : ZMod 5) = 0 := by
        calc (1 : ZMod 5) = (m + 1 + 2) - ((m + 1) + 1) := by ring
        _ = ((m + 1) + 1) - ((m + 1) + 1) := by rw [h]
        _ = 0 := sub_self _
      revert this; decide
    exact hcvx (m + 1) (m + 1 + 2) hj_ne1 hj_ne2
  · -- i = 1: corners m+2, m+3, m+4
    change 0 < ρ * det3 (p (m + 1 + ((2 : ZMod 4).val : ZMod 5)) - p (m + 1 + ((1 : ZMod 4).val : ZMod 5)))
      (p (m + 1 + ((3 : ZMod 4).val : ZMod 5)) - p (m + 1 + ((1 : ZMod 4).val : ZMod 5))) u
    have h1 : ((1 : ZMod 4).val : ZMod 5) = 1 := rfl
    have h2 : ((2 : ZMod 4).val : ZMod 5) = 2 := rfl
    have h3 : ((3 : ZMod 4).val : ZMod 5) = 3 := rfl
    rw [h1, h2, h3]
    have he1 : (m + 1 + 1 : ZMod 5) = m + 2 := by ring
    have he2 : (m + 1 + 2 : ZMod 5) = (m + 2) + 1 := by ring
    have he3 : (m + 1 + 3 : ZMod 5) = m + 4 := by ring
    rw [he1, he2, he3]
    have hj_ne1 : (m + 4 : ZMod 5) ≠ m + 2 := by
      intro h
      have : (2 : ZMod 5) = 0 := by
        calc (2 : ZMod 5) = (m + 4) - (m + 2) := by ring
        _ = (m + 2) - (m + 2) := by rw [h]
        _ = 0 := sub_self _
      revert this; decide
    have hj_ne2 : (m + 4 : ZMod 5) ≠ (m + 2) + 1 := by
      intro h
      have : (1 : ZMod 5) = 0 := by
        calc (1 : ZMod 5) = (m + 4) - ((m + 2) + 1) := by ring
        _ = ((m + 2) + 1) - ((m + 2) + 1) := by rw [h]
        _ = 0 := sub_self _
      revert this; decide
    exact hcvx (m + 2) (m + 4) hj_ne1 hj_ne2
  · -- i = 2: corners m+3, m+4, m+1
    change 0 < ρ * det3 (p (m + 1 + ((3 : ZMod 4).val : ZMod 5)) - p (m + 1 + ((2 : ZMod 4).val : ZMod 5)))
      (p (m + 1 + ((0 : ZMod 4).val : ZMod 5)) - p (m + 1 + ((2 : ZMod 4).val : ZMod 5))) u
    have h0 : ((0 : ZMod 4).val : ZMod 5) = 0 := rfl
    have h2 : ((2 : ZMod 4).val : ZMod 5) = 2 := rfl
    have h3 : ((3 : ZMod 4).val : ZMod 5) = 3 := rfl
    rw [h0, h2, h3, add_zero]
    have he1 : (m + 1 + 2 : ZMod 5) = m + 3 := by ring
    have he2 : (m + 1 + 3 : ZMod 5) = (m + 3) + 1 := by ring
    rw [he1, he2]
    have hj_ne1 : (m + 1 : ZMod 5) ≠ m + 3 := by
      intro h
      have : (2 : ZMod 5) = 0 := by
        calc (2 : ZMod 5) = (m + 3) - (m + 1) := by ring
        _ = (m + 1) - (m + 1) := by rw [← h]
        _ = 0 := sub_self _
      revert this; decide
    have hj_ne2 : (m + 1 : ZMod 5) ≠ (m + 3) + 1 := by
      intro h
      have : (3 : ZMod 5) = 0 := by
        calc (3 : ZMod 5) = ((m + 3) + 1) - (m + 1) := by ring
        _ = (m + 1) - (m + 1) := by rw [← h]
        _ = 0 := sub_self _
      revert this; decide
    exact hcvx (m + 3) (m + 1) hj_ne1 hj_ne2
  · -- i = 3: corners m+4, m+1, m+2
    change 0 < ρ * det3 (p (m + 1 + ((0 : ZMod 4).val : ZMod 5)) - p (m + 1 + ((3 : ZMod 4).val : ZMod 5)))
      (p (m + 1 + ((1 : ZMod 4).val : ZMod 5)) - p (m + 1 + ((3 : ZMod 4).val : ZMod 5))) u
    have h0 : ((0 : ZMod 4).val : ZMod 5) = 0 := rfl
    have h1 : ((1 : ZMod 4).val : ZMod 5) = 1 := rfl
    have h3 : ((3 : ZMod 4).val : ZMod 5) = 3 := rfl
    rw [h0, h1, h3, add_zero]
    have he1 : (m + 1 + 3 : ZMod 5) = m + 4 := by ring
    have he3 : (m + 1 + 1 : ZMod 5) = (m + 1) + 1 := rfl
    rw [he1, he3]
    rw [det3_cycle_triangle (p (m + 4)) (p (m + 1)) (p ((m + 1) + 1))]
    have hj_ne1 : (m + 4 : ZMod 5) ≠ m + 1 := by
      intro h
      have : (3 : ZMod 5) = 0 := by
        calc (3 : ZMod 5) = (m + 4) - (m + 1) := by ring
        _ = (m + 1) - (m + 1) := by rw [h]
        _ = 0 := sub_self _
      revert this; decide
    have hj_ne2 : (m + 4 : ZMod 5) ≠ (m + 1) + 1 := by
      intro h
      have : (2 : ZMod 5) = 0 := by
        calc (2 : ZMod 5) = (m + 4) - ((m + 1) + 1) := by ring
        _ = ((m + 1) + 1) - ((m + 1) + 1) := by rw [h]
        _ = 0 := sub_self _
      revert this; decide
    exact hcvx (m + 1) (m + 4) hj_ne1 hj_ne2

/-! ### DiagCross Refutation Lemmas for Sub-Quads -/

/-- Refutation of odd-below-even alternation from negative `ρ * κ`. -/
theorem not_quadOddBelowEven_of_kappa_neg (p : ZMod 5 → ℝ³) (u : ℝ³) (ρ : ℝ)
    (hcvx : StrictConvex5 p u ρ) (m : ZMod 5)
    (hk : ρ * quadKappa (subquad p m) < 0) :
    ¬ QuadOddBelowEven (subquad p m) u := by
  intro hlt
  have hcvx4 := subquad_strictConvex p u ρ hcvx m
  have hnh := diagCross_not_high (subquad p m) u hcvx4 hk
  exact hnh (le_of_lt hlt)

/-- Refutation of even-below-odd alternation from positive `ρ * κ`. -/
theorem not_quadEvenBelowOdd_of_kappa_pos (p : ZMod 5 → ℝ³) (u : ℝ³) (ρ : ℝ)
    (hcvx : StrictConvex5 p u ρ) (m : ZMod 5)
    (hk : 0 < ρ * quadKappa (subquad p m)) :
    ¬ QuadEvenBelowOdd (subquad p m) u := by
  intro hlt
  have hcvx4 := subquad_strictConvex p u ρ hcvx m
  have hnl := diagCross_not_low (subquad p m) u hcvx4 hk
  exact hnl (le_of_lt hlt)

/-! ### Theorem K5: 5-Rim Structure and Unimodality -/

/-- **Theorem K5 (Two-peaked 5-Rim Structure / Carbon A21 Rank 2)**.
For a strictly convex 5-cycle `p` with injective depths `z = ⟪p ·, u⟫` that is not
cyclically unimodal:
1. There is a unique monotone corner `M : ZMod 5`.
2. The sub-quad `subquad p M` inherits strict convexity with the same `ρ`.
3. The depths of `subquad p M` strictly alternate in the sense matching `M`'s slope. -/
theorem fiveRim_structure (p : ZMod 5 → ℝ³) (u : ℝ³) (ρ : ℝ)
    (hcvx : StrictConvex5 p u ρ)
    (hinj : Function.Injective (fun i => ⟪p i, u⟫))
    (hnu : ¬ IsCyclicUnimodal (fun i => ⟪p i, u⟫)) :
    ∃! M : ZMod 5, IsMonotoneCorner (fun i => ⟪p i, u⟫) M ∧
      MonotoneAlternation p u M := by
  sorry

/-- **Theorem K5 Corollary: 5-Rim Unimodality via Sub-quad Alternation Refutation**.
If every sub-quad `subquad p m` of a strictly convex 5-cycle `p` rules out the
alternation that would occur if `m` were monotone, and depths are injective,
then the depths along `u` are cyclically unimodal. -/
theorem fiveRim_unimodal_of_subquads (p : ZMod 5 → ℝ³) (u : ℝ³) (ρ : ℝ)
    (hcvx : StrictConvex5 p u ρ)
    (hinj : Function.Injective (fun i => ⟪p i, u⟫))
    (hrules : ∀ m : ZMod 5, SubquadRulesOut p u m) :
    IsCyclicUnimodal (fun i => ⟪p i, u⟫) := by
  sorry

/-! ### Theorem K5-DS: Characterization of DepthSepAt on a Two-Peaked 5-Rim -/

/-- The depth clause of `DepthSepAt x u a c` on a cycle of length `k`.
Corners from `c` to `a` lie strictly on one side of depth `⟪x c, u⟫`,
and corners from `a + 1` back to `c` lie strictly on the other side. -/
def DepthClause {k : ℕ} (x : ZMod k → ℝ³) (u : ℝ³) (a c : ZMod k) : Prop :=
  ((∀ s : ℕ, 0 < s → s ≤ (a - c).val → ⟪x c, u⟫ < ⟪x (c + s), u⟫) ∧
      ∀ s : ℕ, (a - c).val < s → s < k → ⟪x (c + s), u⟫ < ⟪x c, u⟫) ∨
  ((∀ s : ℕ, 0 < s → s ≤ (a - c).val → ⟪x (c + s), u⟫ < ⟪x c, u⟫) ∧
      ∀ s : ℕ, (a - c).val < s → s < k → ⟪x c, u⟫ < ⟪x (c + s), u⟫)

/-- Theorem K5-DS: edge `a = 4` (`[V2, P1]`) separates corner `c = 3` (`M`)
if and only if `z M < z V1`. -/
theorem depthClause_k5_edge4 (x : ZMod 5 → ℝ³) (u : ℝ³)
    (hV2M : ⟪x 4, u⟫ < ⟪x 3, u⟫)
    (hMP2 : ⟪x 3, u⟫ < ⟪x 2, u⟫)
    (hV1P1 : ⟪x 1, u⟫ < ⟪x 0, u⟫) :
    DepthClause x u 4 3 ↔ ⟪x 3, u⟫ < ⟪x 1, u⟫ := by
  have hd : ((4 : ZMod 5) - 3).val = 1 := rfl
  dsimp [DepthClause]
  rw [hd]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · have := h1 1 (by omega) (by omega)
      have hc : (3 : ZMod 5) + (1 : ℕ) = (4 : ZMod 5) := by decide
      rw [hc] at this
      linarith
    · have := h2 3 (by omega) (by omega)
      have hc : (3 : ZMod 5) + (3 : ℕ) = (1 : ZMod 5) := by decide
      rw [hc] at this
      exact this
  · intro hM1
    right
    constructor
    · intro s hs0 hs1
      have hs : s = 1 := by omega
      subst hs
      have hc : (3 : ZMod 5) + (1 : ℕ) = (4 : ZMod 5) := by decide
      rw [hc]
      exact hV2M
    · intro s hs1 hs5
      interval_cases s
      · have hc : (3 : ZMod 5) + (2 : ℕ) = (0 : ZMod 5) := by decide
        rw [hc]; linarith
      · have hc : (3 : ZMod 5) + (3 : ℕ) = (1 : ZMod 5) := by decide
        rw [hc]; exact hM1
      · have hc : (3 : ZMod 5) + (4 : ℕ) = (2 : ZMod 5) := by decide
        rw [hc]; exact hMP2

/-- Theorem K5-DS: edge `a = 1` (`[V1, P2]`) separates corner `c = 3` (`M`)
if and only if `z P1 < z M`. -/
theorem depthClause_k5_edge1 (x : ZMod 5 → ℝ³) (u : ℝ³)
    (hV2M : ⟪x 4, u⟫ < ⟪x 3, u⟫)
    (hMP2 : ⟪x 3, u⟫ < ⟪x 2, u⟫)
    (hV1P1 : ⟪x 1, u⟫ < ⟪x 0, u⟫) :
    DepthClause x u 1 3 ↔ ⟪x 0, u⟫ < ⟪x 3, u⟫ := by
  have hd : ((1 : ZMod 5) - 3).val = 3 := rfl
  dsimp [DepthClause]
  rw [hd]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · have := h2 4 (by omega) (by omega)
      have hc : (3 : ZMod 5) + (4 : ℕ) = (2 : ZMod 5) := by decide
      rw [hc] at this
      linarith
    · have := h1 2 (by omega) (by omega)
      have hc : (3 : ZMod 5) + (2 : ℕ) = (0 : ZMod 5) := by decide
      rw [hc] at this
      exact this
  · intro h0M
    right
    constructor
    · intro s hs0 hs3
      interval_cases s
      · have hc : (3 : ZMod 5) + (1 : ℕ) = (4 : ZMod 5) := by decide
        rw [hc]; exact hV2M
      · have hc : (3 : ZMod 5) + (2 : ℕ) = (0 : ZMod 5) := by decide
        rw [hc]; exact h0M
      · have hc : (3 : ZMod 5) + (3 : ℕ) = (1 : ZMod 5) := by decide
        rw [hc]; linarith
    · intro s hs3 hs5
      have hs : s = 4 := by omega
      subst hs
      have hc : (3 : ZMod 5) + (4 : ℕ) = (2 : ZMod 5) := by decide
      rw [hc]
      exact hMP2

/-- Corner `c = 3` is never depth-separated across edge `a = 3`. -/
theorem not_depthClause_k5_edge3 (x : ZMod 5 → ℝ³) (u : ℝ³)
    (hV2M : ⟪x 4, u⟫ < ⟪x 3, u⟫)
    (hMP2 : ⟪x 3, u⟫ < ⟪x 2, u⟫) :
    ¬ DepthClause x u 3 3 := by
  have hd : ((3 : ZMod 5) - 3).val = 0 := rfl
  dsimp [DepthClause]
  rw [hd]
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · have h_gt := h2 4 (by omega) (by omega)
    have hc : (3 : ZMod 5) + (4 : ℕ) = (2 : ZMod 5) := by decide
    rw [hc] at h_gt
    linarith
  · have h_lt := h2 1 (by omega) (by omega)
    have hc : (3 : ZMod 5) + (1 : ℕ) = (4 : ZMod 5) := by decide
    rw [hc] at h_lt
    linarith

/-- Corner `c = 3` is never depth-separated across edge `a = 2`. -/
theorem not_depthClause_k5_edge2 (x : ZMod 5 → ℝ³) (u : ℝ³)
    (hV2M : ⟪x 4, u⟫ < ⟪x 3, u⟫)
    (hMP2 : ⟪x 3, u⟫ < ⟪x 2, u⟫) :
    ¬ DepthClause x u 2 3 := by
  have hd : ((2 : ZMod 5) - 3).val = 4 := rfl
  dsimp [DepthClause]
  rw [hd]
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · have h_lt := h1 1 (by omega) (by omega)
    have hc : (3 : ZMod 5) + (1 : ℕ) = (4 : ZMod 5) := by decide
    rw [hc] at h_lt
    linarith
  · have h_gt := h1 4 (by omega) (by omega)
    have hc : (3 : ZMod 5) + (4 : ℕ) = (2 : ZMod 5) := by decide
    rw [hc] at h_gt
    linarith

/-- Corner `c = 3` is never depth-separated across edge `a = 0`. -/
theorem not_depthClause_k5_edge0 (x : ZMod 5 → ℝ³) (u : ℝ³)
    (hV2M : ⟪x 4, u⟫ < ⟪x 3, u⟫)
    (hV1P1 : ⟪x 1, u⟫ < ⟪x 0, u⟫) :
    ¬ DepthClause x u 0 3 := by
  have hd : ((0 : ZMod 5) - 3).val = 2 := rfl
  dsimp [DepthClause]
  rw [hd]
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · have h_lt := h1 1 (by omega) (by omega)
    have hc : (3 : ZMod 5) + (1 : ℕ) = (4 : ZMod 5) := by decide
    rw [hc] at h_lt
    linarith
  · have h_0 := h1 2 (by omega) (by omega)
    have hc0 : (3 : ZMod 5) + (2 : ℕ) = (0 : ZMod 5) := by decide
    rw [hc0] at h_0
    have h_1 := h2 3 (by omega) (by omega)
    have hc1 : (3 : ZMod 5) + (3 : ℕ) = (1 : ZMod 5) := by decide
    rw [hc1] at h_1
    linarith

/-- **Theorem K5-DS (Depth Clause Equivalence)**.
Corner `c = 3` (`M`) satisfies `DepthClause` for some edge `a` if and only if
`z M < z V1` (with unique edge `a = 4`) or `z P1 < z M` (with unique edge `a = 1`). -/
theorem depthClause_k5_iff (x : ZMod 5 → ℝ³) (u : ℝ³)
    (hV2M : ⟪x 4, u⟫ < ⟪x 3, u⟫)
    (hMP2 : ⟪x 3, u⟫ < ⟪x 2, u⟫)
    (hV1P1 : ⟪x 1, u⟫ < ⟪x 0, u⟫) :
    (∃ a : ZMod 5, DepthClause x u a 3) ↔
      (⟪x 3, u⟫ < ⟪x 1, u⟫ ∨ ⟪x 0, u⟫ < ⟪x 3, u⟫) := by
  constructor
  · rintro ⟨a, hdc⟩
    fin_cases a
    · exact False.elim (not_depthClause_k5_edge0 x u hV2M hV1P1 hdc)
    · have h := (depthClause_k5_edge1 x u hV2M hMP2 hV1P1).mp hdc
      exact Or.inr h
    · exact False.elim (not_depthClause_k5_edge2 x u hV2M hMP2 hdc)
    · exact False.elim (not_depthClause_k5_edge3 x u hV2M hMP2 hdc)
    · have h := (depthClause_k5_edge4 x u hV2M hMP2 hV1P1).mp hdc
      exact Or.inl h
  · rintro (hM1 | h0M)
    · exact ⟨4, (depthClause_k5_edge4 x u hV2M hMP2 hV1P1).mpr hM1⟩
    · exact ⟨1, (depthClause_k5_edge1 x u hV2M hMP2 hV1P1).mpr h0M⟩

/-- **Theorem K5-DS (Full DepthSepAt Equivalence)**.
In the K5 decomposition `(P1, V1, P2, M, V2)` where `x 3 = M` and `z V2 < z M < z P2`,
corner `M` satisfies `DepthSepAt` if and only if:
- `z M < z V1` and normal cone det3 condition holds at edge `[V2, P1]`, or
- `z P1 < z M` and normal cone det3 condition holds at edge `[V1, P2]`.
When `z V1 < z M < z P1`, `DepthSepAt` is false at `c = M` for all edges. -/
theorem depthSepAt_k5_iff (x : ZMod 5 → ℝ³) (u : ℝ³)
    (hV2M : ⟪x 4, u⟫ < ⟪x 3, u⟫)
    (hMP2 : ⟪x 3, u⟫ < ⟪x 2, u⟫)
    (hV1P1 : ⟪x 1, u⟫ < ⟪x 0, u⟫) :
    (∃ a : ZMod 5, DepthSepAt x u a 3) ↔
      ((⟪x 3, u⟫ < ⟪x 1, u⟫ ∧ (∀ j : ZMod 5, j ≠ 3 →
          det3 (x 0 - x 4) (x j - x 3) u * det3 (x 0 - x 4) (x 3 - x 4) u < 0)) ∨
       (⟪x 0, u⟫ < ⟪x 3, u⟫ ∧ (∀ j : ZMod 5, j ≠ 3 →
          det3 (x 2 - x 1) (x j - x 3) u * det3 (x 2 - x 1) (x 3 - x 1) u < 0))) := by
  constructor
  · rintro ⟨a, hds⟩
    have hdet := hds.1
    have hdc : DepthClause x u a 3 := hds.2
    fin_cases a
    · exact False.elim (not_depthClause_k5_edge0 x u hV2M hV1P1 hdc)
    · have h1 := (depthClause_k5_edge1 x u hV2M hMP2 hV1P1).mp hdc
      exact Or.inr ⟨h1, hdet⟩
    · exact False.elim (not_depthClause_k5_edge2 x u hV2M hMP2 hdc)
    · exact False.elim (not_depthClause_k5_edge3 x u hV2M hMP2 hdc)
    · have h4 := (depthClause_k5_edge4 x u hV2M hMP2 hV1P1).mp hdc
      exact Or.inl ⟨h4, hdet⟩
  · rintro (⟨hM1, hdet⟩ | ⟨h0M, hdet⟩)
    · exact ⟨4, hdet, (depthClause_k5_edge4 x u hV2M hMP2 hV1P1).mpr hM1⟩
    · exact ⟨1, hdet, (depthClause_k5_edge1 x u hV2M hMP2 hV1P1).mpr h0M⟩

end Minimality
