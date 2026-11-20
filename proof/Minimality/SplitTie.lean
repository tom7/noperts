module

public import Mathlib
public import Minimality.Thm73
public import Minimality.TurnCalculus
public import Minimality.Generic.PV.SK
public import Minimality.ZModLemmas

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped RealInnerProductSpace Topology
open Filter Finset
open Minimality

namespace Minimality

/-!
# Task AJ: Lemma Split-Unimodal (A22 Rank 1)

This module formalizes Carbon's Lemma Split-Unimodal (A22 Rank 1):
A general tool for 5-rim (and general k-rim, k ≥ 4) adjacent tie perturbation.

## Setting

Let `x : ZMod (m + 1) → ℝ³` be a rim cycle with `m ≥ 3` (so rim length `k = m + 1 ≥ 4`).
At base view `b : ℝ³`, there is a single adjacent tie between `a` and `a + 1`:
`⟪x a, b⟫ = ⟪x (a + 1), b⟫`, and all other pairs of rim depths are distinct at `b`.
Let `d : ℝ³` be a direction breaking the tie: `⟪x a - x (a + 1), d⟫ ≠ 0`.

The merged `m`-cycle (obtained by identifying `a` and `a + 1`) has depths at `b`
given by `mergedDepths (fun i => ⟪x i, b⟫) a := skipAt (fun i => ⟪x i, b⟫) a`.
In this merged cycle, index `0 : ZMod m` corresponds to the merged vertex `{a, a + 1}`,
index `-1 : ZMod m` corresponds to `a - 1`, and index `1 : ZMod m` to `a + 2`.

## Main Results

If the merged depths are strictly cyclically unimodal (`IsCyclicUnimodal`):
1. **Extremum Case (`splitUnimodal_extremum`)**:
   If the merged vertex `0` is a strict local extremum (peak or valley) of the merged cycle,
   BOTH `b + ε • d` and `b - ε • d` have injective, cyclically unimodal rim depths for small `ε > 0`.
2. **Monotone Case (`splitUnimodal_monotone`)**:
   If the merged vertex `0` is a strict monotone corner (increasing or decreasing),
   the sign `σ ∈ {1, -1}` matching the slope through the tie makes `b + (σ * ε) • d`
   have injective, cyclically unimodal rim depths for small `ε > 0`.
3. **Instance-Free Corollary (`splitUnimodal_exists_sign`)**:
   In all cases, `∃ σ ∈ {1, -1}, ∀ᶠ ε in 𝓝[>] 0, Injective ∧ IsCyclicUnimodal`.
4. **5-Rim Specialization (`splitUnimodal_exists_sign_5`)**:
   Direct specialization to 5-rims (`m = 4`, `k = 5`).
-/

/-- Single adjacent depth tie between `a` and `a+1` at view `b`, with all other pairs distinct. -/
def SingleAdjacentTie {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) (b : ℝ³) (a : ZMod k) : Prop :=
  ⟪x a, b⟫ = ⟪x (a + 1), b⟫ ∧
  ∀ i j : ZMod k, ⟪x i, b⟫ = ⟪x j, b⟫ → i = j ∨ (i = a ∧ j = a + 1) ∨ (i = a + 1 ∧ j = a)

/-- Depths of the merged (k-1)-cycle obtained by identifying adjacent tied corners `a` and `a+1`.
In the merged cycle on `ZMod m` (where `k = m + 1`), index `0` is the merged vertex,
`-1` is `a - 1`, and `1` is `a + 2`. -/
def mergedDepths {m : ℕ} [NeZero m] (z : ZMod (m + 1) → ℝ) (a : ZMod (m + 1)) : ZMod m → ℝ :=
  skipAt z a

/-- The merged vertex `0` is a strict local extremum (peak or valley) in the merged cycle. -/
def IsMergedExtremum {m : ℕ} [NeZero m] (w : ZMod m → ℝ) : Prop :=
  (w (-1) < w 0 ∧ w 1 < w 0) ∨ (w 0 < w (-1) ∧ w 0 < w 1)

/-- The merged vertex `0` is a strict monotone corner (increasing or decreasing) in the merged cycle. -/
def IsMergedMonotone {m : ℕ} [NeZero m] (w : ZMod m → ℝ) : Prop :=
  (w (-1) < w 0 ∧ w 0 < w 1) ∨ (w 1 < w 0 ∧ w 0 < w (-1))

/-- Explicit sign `σ ∈ {1, -1}` for a monotone merged corner, matching perturbation
slope to the slope through the tie. -/
noncomputable def splitTieSlopeSign {m : ℕ} [NeZero m] (x : ZMod (m + 1) → ℝ³) (b d : ℝ³) (a : ZMod (m + 1)) : ℝ :=
  if (0 < ⟪x (a + 1) - x a, d⟫ ↔ ⟪x (a - 1), b⟫ < ⟪x (a + 2), b⟫) then 1 else -1

/-- **Lemma Split-Unimodal: Extremum Case**.
If the merged vertex is a strict local extremum in the merged cycle, then BOTH perturbations
`b + ε • d` and `b - ε • d` have injective and cyclically unimodal rim depths for small `ε > 0`. -/
theorem splitUnimodal_extremum {m : ℕ} [NeZero m] (hm : 3 ≤ m)
    (x : ZMod (m + 1) → ℝ³) (b d : ℝ³) (a : ZMod (m + 1))
    (htie : SingleAdjacentTie x b a)
    (hdir : ⟪x a - x (a + 1), d⟫ ≠ 0)
    (huni : IsCyclicUnimodal (mergedDepths (fun i => ⟪x i, b⟫) a))
    (hext : IsMergedExtremum (mergedDepths (fun i => ⟪x i, b⟫) a)) :
    (∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Function.Injective (fun i => ⟪x i, b + ε • d⟫) ∧
      IsCyclicUnimodal (fun i => ⟪x i, b + ε • d⟫)) ∧
    (∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Function.Injective (fun i => ⟪x i, b - ε • d⟫) ∧
      IsCyclicUnimodal (fun i => ⟪x i, b - ε • d⟫)) := by
  sorry

/-- **Lemma Split-Unimodal: Monotone Case**.
If the merged vertex is a strict monotone corner in the merged cycle, then the perturbation
`b + (σ * ε) • d` with `σ = splitTieSlopeSign x b d a` has injective and cyclically unimodal
rim depths for small `ε > 0`. -/
theorem splitUnimodal_monotone {m : ℕ} [NeZero m] (hm : 3 ≤ m)
    (x : ZMod (m + 1) → ℝ³) (b d : ℝ³) (a : ZMod (m + 1))
    (htie : SingleAdjacentTie x b a)
    (hdir : ⟪x a - x (a + 1), d⟫ ≠ 0)
    (huni : IsCyclicUnimodal (mergedDepths (fun i => ⟪x i, b⟫) a))
    (hmono : IsMergedMonotone (mergedDepths (fun i => ⟪x i, b⟫) a)) :
    let σ := splitTieSlopeSign x b d a
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Function.Injective (fun i => ⟪x i, b + (σ * ε) • d⟫) ∧
      IsCyclicUnimodal (fun i => ⟪x i, b + (σ * ε) • d⟫) := by
  sorry

/-- **Lemma Split-Unimodal (Instance-Free Corollary, A22 Rank 1)**.
For any rim `x` with adjacent tie at `(a, a+1)` whose merged cycle depths are cyclically unimodal,
there exists a sign `σ ∈ {1, -1}` such that the perturbed depths along `b + (σ * ε) • d` are
injective and cyclically unimodal for all small `ε > 0`. -/
theorem splitUnimodal_exists_sign {m : ℕ} [NeZero m] (hm : 3 ≤ m)
    (x : ZMod (m + 1) → ℝ³) (b d : ℝ³) (a : ZMod (m + 1))
    (htie : SingleAdjacentTie x b a)
    (hdir : ⟪x a - x (a + 1), d⟫ ≠ 0)
    (huni : IsCyclicUnimodal (mergedDepths (fun i => ⟪x i, b⟫) a)) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        Function.Injective (fun i => ⟪x i, b + (σ * ε) • d⟫) ∧
        IsCyclicUnimodal (fun i => ⟪x i, b + (σ * ε) • d⟫) := by
  sorry

/-- **Lemma Split-Unimodal (5-Rim Specialization)**.
Direct specialization to 5-rims (`k = 5, m = 4`). -/
theorem splitUnimodal_exists_sign_5
    (x : ZMod 5 → ℝ³) (b d : ℝ³) (a : ZMod 5)
    (htie : SingleAdjacentTie x b a)
    (hdir : ⟪x a - x (a + 1), d⟫ ≠ 0)
    (huni : IsCyclicUnimodal (mergedDepths (fun i => ⟪x i, b⟫) a)) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        Function.Injective (fun i => ⟪x i, b + (σ * ε) • d⟫) ∧
        IsCyclicUnimodal (fun i => ⟪x i, b + (σ * ε) • d⟫) := by
  exact splitUnimodal_exists_sign (by decide) x b d a htie hdir huni

end Minimality
