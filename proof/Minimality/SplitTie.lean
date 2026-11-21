module

public import Mathlib
public import Minimality.Thm73
public import Minimality.TurnCalculus
public import Minimality.Generic.PV.SK
public import Minimality.ZModLemmas
public import Minimality.RobustUnimodal

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

/-! ### Indexing and Cycle-Order Lemmas for `mergedDepths` -/

lemma mergedDepths_zero {m : ℕ} [NeZero m] (z : ZMod (m + 1) → ℝ) (a : ZMod (m + 1))
    (htie : z a = z (a + 1)) :
    mergedDepths z a 0 = z a := by
  have : mergedDepths z a 0 = z (phi a 0) := rfl
  rw [this, phi_zero, ← htie]

lemma mergedDepths_zero' {m : ℕ} [NeZero m] (z : ZMod (m + 1) → ℝ) (a : ZMod (m + 1)) :
    mergedDepths z a 0 = z (a + 1) := by
  have : mergedDepths z a 0 = z (phi a 0) := rfl
  rw [this, phi_zero]

lemma mergedDepths_neg_one {m : ℕ} [NeZero m] (z : ZMod (m + 1) → ℝ) (a : ZMod (m + 1)) :
    mergedDepths z a (-1) = z (a - 1) := by
  have : mergedDepths z a (-1) = z (phi a (-1)) := rfl
  rw [this, phi_neg_one]

lemma mergedDepths_one {m : ℕ} [NeZero m] (hm : 2 ≤ m) (z : ZMod (m + 1) → ℝ) (a : ZMod (m + 1)) :
    mergedDepths z a 1 = z (a + 2) := by
  have : Fact (1 < m) := ⟨by omega⟩
  have h0 : (0 : ZMod m) ≠ -1 := by
    intro h
    apply one_ne_zero (α := ZMod m)
    simpa using h.symm
  have : mergedDepths z a 1 = z (phi a 1) := rfl
  rw [this]
  have hsucc := phi_succ a 0 h0
  rw [zero_add] at hsucc
  rw [hsucc, phi_zero]
  have h2 : (a + 1 : ZMod (m + 1)) + 1 = a + 2 := by ring
  rw [h2]

lemma mergedDepths_succ {m : ℕ} [NeZero m] (z : ZMod (m + 1) → ℝ) (a : ZMod (m + 1))
    (j : ZMod m) (hj : j ≠ -1) :
    mergedDepths z a (j + 1) = z (phi a j + 1) := by
  have : mergedDepths z a (j + 1) = z (phi a (j + 1)) := rfl
  rw [this, phi_succ a j hj]

/-- `mergedDepths` visits the remaining corners in cyclic order: for all `j ≠ -1`,
the successor in `ZMod m` maps to the successor in `ZMod (m + 1)`. -/
lemma phi_order {m : ℕ} [NeZero m] (a : ZMod (m + 1)) (j : ZMod m) (hj : j ≠ -1) :
    phi a (j + 1) = phi a j + 1 :=
  phi_succ a j hj

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

/-! ### Helper Lemmas for Perturbation and Turn Calculus -/

lemma tendsto_inner_aff (v b d : ℝ³) (σ : ℝ) :
    Tendsto (fun ε : ℝ => ⟪v, b + (σ * ε) • d⟫) (𝓝[>] (0 : ℝ)) (𝓝 ⟪v, b⟫) := by
  have hc : Continuous (fun ε : ℝ => ⟪v, b + (σ * ε) • d⟫) := by fun_prop
  have h0 : ⟪v, b + (σ * (0 : ℝ)) • d⟫ = ⟪v, b⟫ := by simp
  rw [← h0]
  exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds

lemma eventually_strict_pres {m : ℕ} [NeZero m] (x : ZMod (m + 1) → ℝ³) (b d : ℝ³) (σ : ℝ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i j : ZMod (m + 1),
      ⟪x i, b⟫ < ⟪x j, b⟫ → ⟪x i, b + (σ * ε) • d⟫ < ⟪x j, b + (σ * ε) • d⟫ := by
  refine eventually_all.mpr fun i => eventually_all.mpr fun j => ?_
  by_cases h : ⟪x i, b⟫ < ⟪x j, b⟫
  · have hti := tendsto_inner_aff (x i) b d σ
    have htj := tendsto_inner_aff (x j) b d σ
    exact (hti.eventually_lt htj h).mono fun ε hε _ => hε
  · exact Eventually.of_forall fun ε hε => absurd hε h

lemma iff_of_strict_order {α : Type*} {z : α → ℝ} {w : α → ℝ}
    (hinj : Function.Injective z)
    (hord : ∀ a b, z a < z b → w a < w b) (a b : α) :
    w a < w b ↔ z a < z b := by
  rcases lt_trichotomy (z a) (z b) with h | h | h
  · exact iff_of_true (hord a b h) h
  · have : a = b := hinj h
    subst this
    exact iff_of_false (lt_irrefl _) (lt_irrefl _)
  · have hw := hord b a h
    exact iff_of_false (not_lt_of_gt hw) (not_lt_of_gt h)

lemma numPeaks_eq_of_strict_order {m : ℕ} [NeZero m] {z : ZMod m → ℝ} {w : ZMod m → ℝ}
    (hinj : Function.Injective z)
    (hord : ∀ a b, z a < z b → w a < w b) :
    numPeaks w = numPeaks z := by
  have hext : cycPeaks w = cycPeaks z := by
    ext j
    simp only [mem_cycPeaks]
    rw [iff_of_strict_order hinj hord (j - 1) j, iff_of_strict_order hinj hord (j + 1) j]
  exact congrArg card hext

lemma injective_split {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) (b d : ℝ³) (a : ZMod k) (σ ε : ℝ)
    (htie : SingleAdjacentTie x b a)
    (hdir : ⟪x a - x (a + 1), d⟫ ≠ 0)
    (hσ : σ ≠ 0) (hε : 0 < ε)
    (hord : ∀ i j : ZMod k, ⟪x i, b⟫ < ⟪x j, b⟫ → ⟪x i, b + (σ * ε) • d⟫ < ⟪x j, b + (σ * ε) • d⟫) :
    Function.Injective (fun i => ⟪x i, b + (σ * ε) • d⟫) := by
  intro i j hij
  rcases lt_trichotomy ⟪x i, b⟫ ⟪x j, b⟫ with h | h | h
  · have := hord i j h
    linarith
  · rcases htie.2 i j h with heq | ⟨hi, hj⟩ | ⟨hi, hj⟩
    · exact heq
    · exfalso
      have hdiff : ⟪x a, b + (σ * ε) • d⟫ - ⟪x (a + 1), b + (σ * ε) • d⟫ = (σ * ε) * ⟪x a - x (a + 1), d⟫ := by
        simp only [inner_add_right, inner_smul_right, inner_sub_left]
        have heq : ⟪x a, b⟫ = ⟪x (a + 1), b⟫ := htie.1
        rw [heq]; ring
      have hnonzero : (σ * ε) * ⟪x a - x (a + 1), d⟫ ≠ 0 := by
        apply mul_ne_zero
        · exact mul_ne_zero hσ (ne_of_gt hε)
        · exact hdir
      have heq2 : ⟪x a, b + (σ * ε) • d⟫ = ⟪x (a + 1), b + (σ * ε) • d⟫ := by
        calc ⟪x a, b + (σ * ε) • d⟫ = ⟪x i, b + (σ * ε) • d⟫ := by rw [hi]
        _ = ⟪x j, b + (σ * ε) • d⟫ := hij
        _ = ⟪x (a + 1), b + (σ * ε) • d⟫ := by rw [hj]
      rw [heq2, sub_self] at hdiff
      exact hnonzero hdiff.symm
    · exfalso
      have hdiff : ⟪x (a + 1), b + (σ * ε) • d⟫ - ⟪x a, b + (σ * ε) • d⟫ = (σ * ε) * ⟪x (a + 1) - x a, d⟫ := by
        simp only [inner_add_right, inner_smul_right, inner_sub_left]
        have heq : ⟪x a, b⟫ = ⟪x (a + 1), b⟫ := htie.1
        rw [heq]; ring
      have hnonzero : (σ * ε) * ⟪x (a + 1) - x a, d⟫ ≠ 0 := by
        apply mul_ne_zero
        · exact mul_ne_zero hσ (ne_of_gt hε)
        · have : x (a + 1) - x a = - (x a - x (a + 1)) := by abel
          rw [this, inner_neg_left]
          exact neg_ne_zero.mpr hdir
      have heq2 : ⟪x (a + 1), b + (σ * ε) • d⟫ = ⟪x a, b + (σ * ε) • d⟫ := by
        calc ⟪x (a + 1), b + (σ * ε) • d⟫ = ⟪x i, b + (σ * ε) • d⟫ := by rw [hi]
        _ = ⟪x j, b + (σ * ε) • d⟫ := hij
        _ = ⟪x a, b + (σ * ε) • d⟫ := by rw [hj]
      rw [heq2, sub_self] at hdiff
      exact hnonzero hdiff.symm
  · have := hord j i h
    linarith

lemma numPeaks_extremum_max {m : ℕ} [NeZero m] (hm : 2 ≤ m) (z : ZMod (m + 1) → ℝ) (a : ZMod (m + 1))
    (hw_peaks : numPeaks (skipAt z a) = 1)
    (h_v1 : z (a - 1) < z (a + 1))
    (h_v2 : z (a + 2) < z (a + 1))
    (h_v3 : z (a - 1) < z a)
    (h_tie : z a < z (a + 1) ∨ z (a + 1) < z a) :
    numPeaks z = 1 := by
  have hid := numPeaks_skipAt_add hm z a
  have hp_w0 : peakInd (z (a - 1)) (z (a + 1)) (z (a + 2)) = 1 := by
    simp [peakInd, h_v1, h_v2]
  have h2 : (a + 1 + 1 : ZMod (m + 1)) = a + 2 := by ring
  rw [h2] at hid
  have hL2_eq_R1 : peakInd (z (a - 1 - 1)) (z (a - 1)) (z (a + 1)) =
      peakInd (z (a - 1 - 1)) (z (a - 1)) (z a) := by
    unfold peakInd
    have h1 : ¬ (z (a + 1) < z (a - 1)) := not_lt_of_gt h_v1
    have h2 : ¬ (z a < z (a - 1)) := not_lt_of_gt h_v3
    simp [h1, h2]
  rcases h_tie with h_lt | h_gt
  · have hR2 : peakInd (z (a - 1)) (z a) (z (a + 1)) = 0 := by
      unfold peakInd
      have : ¬ (z (a + 1) < z a) := not_lt_of_gt h_lt
      simp [this]
    have hR3 : peakInd (z a) (z (a + 1)) (z (a + 2)) = 1 := by
      unfold peakInd
      simp [h_lt, h_v2]
    rw [hw_peaks, hp_w0, hR2, hR3, hL2_eq_R1] at hid
    omega
  · have hR2 : peakInd (z (a - 1)) (z a) (z (a + 1)) = 1 := by
      unfold peakInd
      simp [h_v3, h_gt]
    have hR3 : peakInd (z a) (z (a + 1)) (z (a + 2)) = 0 := by
      unfold peakInd
      have : ¬ (z a < z (a + 1)) := not_lt_of_gt h_gt
      simp [this]
    rw [hw_peaks, hp_w0, hR2, hR3, hL2_eq_R1] at hid
    omega

lemma numPeaks_extremum_min {m : ℕ} [NeZero m] (hm : 2 ≤ m) (z : ZMod (m + 1) → ℝ) (a : ZMod (m + 1))
    (hw_peaks : numPeaks (skipAt z a) = 1)
    (h_v1 : z (a + 1) < z (a - 1))
    (h_v2 : z (a + 1) < z (a + 2))
    (h_v3 : z a < z (a - 1)) :
    numPeaks z = 1 := by
  have hid := numPeaks_skipAt_add hm z a
  have hp_w0 : peakInd (z (a - 1)) (z (a + 1)) (z (a + 2)) = 0 := by
    unfold peakInd
    have : ¬ (z (a - 1) < z (a + 1)) := not_lt_of_gt h_v1
    simp [this]
  have h2 : (a + 1 + 1 : ZMod (m + 1)) = a + 2 := by ring
  rw [h2] at hid
  have hL2_eq_R1 : peakInd (z (a - 1 - 1)) (z (a - 1)) (z (a + 1)) =
      peakInd (z (a - 1 - 1)) (z (a - 1)) (z a) := by
    unfold peakInd
    simp [h_v1, h_v3]
  have hR2 : peakInd (z (a - 1)) (z a) (z (a + 1)) = 0 := by
    unfold peakInd
    have : ¬ (z (a - 1) < z a) := not_lt_of_gt h_v3
    simp [this]
  have hR3 : peakInd (z a) (z (a + 1)) (z (a + 2)) = 0 := by
    unfold peakInd
    have : ¬ (z (a + 2) < z (a + 1)) := not_lt_of_gt h_v2
    simp [this]
  rw [hw_peaks, hp_w0, hR2, hR3, hL2_eq_R1] at hid
  omega

lemma numPeaks_monotone_incr {m : ℕ} [NeZero m] (hm : 2 ≤ m) (z : ZMod (m + 1) → ℝ) (a : ZMod (m + 1))
    (hw_peaks : numPeaks (skipAt z a) = 1)
    (h_v1 : z (a - 1) < z (a + 1))
    (h_v2 : z (a + 1) < z (a + 2))
    (h_v3 : z (a - 1) < z a)
    (h_tie : z a < z (a + 1)) :
    numPeaks z = 1 := by
  have hid := numPeaks_skipAt_add hm z a
  have hp_w0 : peakInd (z (a - 1)) (z (a + 1)) (z (a + 2)) = 0 := by
    unfold peakInd
    have : ¬ (z (a + 2) < z (a + 1)) := not_lt_of_gt h_v2
    simp [this]
  have h2 : (a + 1 + 1 : ZMod (m + 1)) = a + 2 := by ring
  rw [h2] at hid
  have hL2_eq_R1 : peakInd (z (a - 1 - 1)) (z (a - 1)) (z (a + 1)) =
      peakInd (z (a - 1 - 1)) (z (a - 1)) (z a) := by
    unfold peakInd
    have h1 : ¬ (z (a + 1) < z (a - 1)) := not_lt_of_gt h_v1
    have h2 : ¬ (z a < z (a - 1)) := not_lt_of_gt h_v3
    simp [h1, h2]
  have hR2 : peakInd (z (a - 1)) (z a) (z (a + 1)) = 0 := by
    unfold peakInd
    have : ¬ (z (a + 1) < z a) := not_lt_of_gt h_tie
    simp [this]
  have hR3 : peakInd (z a) (z (a + 1)) (z (a + 2)) = 0 := by
    unfold peakInd
    have : ¬ (z (a + 2) < z (a + 1)) := not_lt_of_gt h_v2
    simp [this]
  rw [hw_peaks, hp_w0, hR2, hR3, hL2_eq_R1] at hid
  omega

lemma numPeaks_monotone_decr {m : ℕ} [NeZero m] (hm : 2 ≤ m) (z : ZMod (m + 1) → ℝ) (a : ZMod (m + 1))
    (hw_peaks : numPeaks (skipAt z a) = 1)
    (h_v1 : z (a + 1) < z (a - 1))
    (h_v3 : z a < z (a - 1))
    (h_tie : z (a + 1) < z a) :
    numPeaks z = 1 := by
  have hid := numPeaks_skipAt_add hm z a
  have hp_w0 : peakInd (z (a - 1)) (z (a + 1)) (z (a + 2)) = 0 := by
    unfold peakInd
    have : ¬ (z (a - 1) < z (a + 1)) := not_lt_of_gt h_v1
    simp [this]
  have h2 : (a + 1 + 1 : ZMod (m + 1)) = a + 2 := by ring
  rw [h2] at hid
  have hL2_eq_R1 : peakInd (z (a - 1 - 1)) (z (a - 1)) (z (a + 1)) =
      peakInd (z (a - 1 - 1)) (z (a - 1)) (z a) := by
    unfold peakInd
    simp [h_v1, h_v3]
  have hR2 : peakInd (z (a - 1)) (z a) (z (a + 1)) = 0 := by
    unfold peakInd
    have : ¬ (z (a - 1) < z a) := not_lt_of_gt h_v3
    simp [this]
  have hR3 : peakInd (z a) (z (a + 1)) (z (a + 2)) = 0 := by
    unfold peakInd
    have : ¬ (z a < z (a + 1)) := not_lt_of_gt h_tie
    simp [this]
  rw [hw_peaks, hp_w0, hR2, hR3, hL2_eq_R1] at hid
  omega

/-! ### Core Unimodality Step -/

lemma splitUnimodal_step {m : ℕ} [NeZero m] (hm : 3 ≤ m)
    (x : ZMod (m + 1) → ℝ³) (b d : ℝ³) (a : ZMod (m + 1)) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (htie : SingleAdjacentTie x b a)
    (hdir : ⟪x a - x (a + 1), d⟫ ≠ 0)
    (huni : IsCyclicUnimodal (mergedDepths (fun i => ⟪x i, b⟫) a))
    (hbranch :
      (IsMergedExtremum (mergedDepths (fun i => ⟪x i, b⟫) a)) ∨
      (IsMergedMonotone (mergedDepths (fun i => ⟪x i, b⟫) a) ∧
        (0 < ⟪x (a - 1), b⟫ - ⟪x (a + 2), b⟫ ↔ 0 < σ * ⟪x a - x (a + 1), d⟫))) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Function.Injective (fun i => ⟪x i, b + (σ * ε) • d⟫) ∧
      IsCyclicUnimodal (fun i => ⟪x i, b + (σ * ε) • d⟫) := by
  have hm2 : 2 ≤ m := by omega
  have hσ_ne : σ ≠ 0 := by
    rcases hσ with rfl | rfl <;> norm_num
  have hev_strict := eventually_strict_pres x b d σ
  filter_upwards [hev_strict, self_mem_nhdsWithin] with ε hord hε
  have hinj := injective_split x b d a σ ε htie hdir hσ_ne hε hord
  refine ⟨hinj, ?_⟩
  rw [isCyclicUnimodal_iff_numPeaks]
  refine ⟨hinj, ?_⟩
  -- 1. skipAt z a has numPeaks = 1
  have huni_w0 : IsCyclicUnimodal (mergedDepths (fun i => ⟪x i, b⟫) a) := huni
  have hinj_w0 : Function.Injective (mergedDepths (fun i => ⟪x i, b⟫) a) := huni_w0.1
  have hord_w : ∀ j₁ j₂ : ZMod m,
      mergedDepths (fun i => ⟪x i, b⟫) a j₁ < mergedDepths (fun i => ⟪x i, b⟫) a j₂ →
      skipAt (fun i => ⟪x i, b + (σ * ε) • d⟫) a j₁ < skipAt (fun i => ⟪x i, b + (σ * ε) • d⟫) a j₂ := by
    intro j₁ j₂ hj
    have : mergedDepths (fun i => ⟪x i, b⟫) a j₁ = ⟪x (phi a j₁), b⟫ := rfl
    have : mergedDepths (fun i => ⟪x i, b⟫) a j₂ = ⟪x (phi a j₂), b⟫ := rfl
    have hlt : ⟪x (phi a j₁), b⟫ < ⟪x (phi a j₂), b⟫ := hj
    have hres := hord (phi a j₁) (phi a j₂) hlt
    exact hres
  have hw_peaks : numPeaks (skipAt (fun i => ⟪x i, b + (σ * ε) • d⟫) a) = 1 := by
    rw [numPeaks_eq_of_strict_order hinj_w0 hord_w]
    exact huni_w0.2
  -- tie at ε
  have hdiff : ⟪x a, b + (σ * ε) • d⟫ - ⟪x (a + 1), b + (σ * ε) • d⟫ = (σ * ε) * ⟪x a - x (a + 1), d⟫ := by
    simp only [inner_add_right, inner_smul_right, inner_sub_left]
    have heq : ⟪x a, b⟫ = ⟪x (a + 1), b⟫ := htie.1
    rw [heq]; ring
  have htie_ne : ⟪x a, b + (σ * ε) • d⟫ ≠ ⟪x (a + 1), b + (σ * ε) • d⟫ := by
    intro hc
    have h0 : (σ * ε) * ⟪x a - x (a + 1), d⟫ = 0 := by rw [← hdiff, hc, sub_self]
    have h_prod : (σ * ε) * ⟪x a - x (a + 1), d⟫ ≠ 0 := by
      apply mul_ne_zero
      · exact mul_ne_zero hσ_ne (ne_of_gt hε)
      · exact hdir
    exact h_prod h0
  have htie_cases : ⟪x a, b + (σ * ε) • d⟫ < ⟪x (a + 1), b + (σ * ε) • d⟫ ∨
      ⟪x (a + 1), b + (σ * ε) • d⟫ < ⟪x a, b + (σ * ε) • d⟫ := lt_or_gt_of_ne htie_ne
  set z := fun i => ⟪x i, b + (σ * ε) • d⟫
  set w0 := mergedDepths (fun i => ⟪x i, b⟫) a
  have hw0_0 : w0 0 = ⟪x (a + 1), b⟫ := mergedDepths_zero' (fun i => ⟪x i, b⟫) a
  have hw0_0a : w0 0 = ⟪x a, b⟫ := mergedDepths_zero (fun i => ⟪x i, b⟫) a htie.1
  have hw0_m1 : w0 (-1) = ⟪x (a - 1), b⟫ := mergedDepths_neg_one (fun i => ⟪x i, b⟫) a
  have hw0_1 : w0 1 = ⟪x (a + 2), b⟫ := mergedDepths_one hm2 (fun i => ⟪x i, b⟫) a
  rcases hbranch with hext | ⟨hmono, hmatch⟩
  · -- Extremum case
    rcases hext with ⟨hm1_lt, h1_lt⟩ | ⟨lt_m1, lt_1⟩
    · -- Local maximum
      have hv1 : z (a - 1) < z (a + 1) := by
        have : ⟪x (a - 1), b⟫ < ⟪x (a + 1), b⟫ := by rw [← hw0_m1, ← hw0_0]; exact hm1_lt
        exact hord (a - 1) (a + 1) this
      have hv2 : z (a + 2) < z (a + 1) := by
        have : ⟪x (a + 2), b⟫ < ⟪x (a + 1), b⟫ := by rw [← hw0_1, ← hw0_0]; exact h1_lt
        exact hord (a + 2) (a + 1) this
      have hv3 : z (a - 1) < z a := by
        have : ⟪x (a - 1), b⟫ < ⟪x a, b⟫ := by rw [← hw0_m1, ← hw0_0a]; exact hm1_lt
        exact hord (a - 1) a this
      exact numPeaks_extremum_max hm2 z a hw_peaks hv1 hv2 hv3 htie_cases
    · -- Local minimum
      have hv1 : z (a + 1) < z (a - 1) := by
        have : ⟪x (a + 1), b⟫ < ⟪x (a - 1), b⟫ := by rw [← hw0_m1, ← hw0_0]; exact lt_m1
        exact hord (a + 1) (a - 1) this
      have hv2 : z (a + 1) < z (a + 2) := by
        have : ⟪x (a + 1), b⟫ < ⟪x (a + 2), b⟫ := by rw [← hw0_1, ← hw0_0]; exact lt_1
        exact hord (a + 1) (a + 2) this
      have hv3 : z a < z (a - 1) := by
        have : ⟪x a, b⟫ < ⟪x (a - 1), b⟫ := by rw [← hw0_m1, ← hw0_0a]; exact lt_m1
        exact hord a (a - 1) this
      exact numPeaks_extremum_min hm2 z a hw_peaks hv1 hv2 hv3
  · -- Monotone case
    have htie_sign : (0 < z a - z (a + 1)) ↔ (0 < σ * ⟪x a - x (a + 1), d⟫) := by
      rw [hdiff]
      have hpos : 0 < ε := hε
      constructor
      · intro h; have : 0 < (σ * ε) * ⟪x a - x (a + 1), d⟫ := h
        have heq : (σ * ε) * ⟪x a - x (a + 1), d⟫ = ε * (σ * ⟪x a - x (a + 1), d⟫) := by ring
        rw [heq] at this
        exact (pos_iff_pos_of_mul_pos this).mp hpos
      · intro h; have heq : (σ * ε) * ⟪x a - x (a + 1), d⟫ = ε * (σ * ⟪x a - x (a + 1), d⟫) := by ring
        rw [heq]
        exact mul_pos hpos h
    rcases hmono with ⟨hm1_lt, lt_1⟩ | ⟨lt_m1, h1_lt⟩
    · -- Increasing: w0 (-1) < w0 0 < w0 1
      have hv1 : z (a - 1) < z (a + 1) := by
        have : ⟪x (a - 1), b⟫ < ⟪x (a + 1), b⟫ := by rw [← hw0_m1, ← hw0_0]; exact hm1_lt
        exact hord (a - 1) (a + 1) this
      have hv2 : z (a + 1) < z (a + 2) := by
        have : ⟪x (a + 1), b⟫ < ⟪x (a + 2), b⟫ := by rw [← hw0_1, ← hw0_0]; exact lt_1
        exact hord (a + 1) (a + 2) this
      have hv3 : z (a - 1) < z a := by
        have : ⟪x (a - 1), b⟫ < ⟪x a, b⟫ := by rw [← hw0_m1, ← hw0_0a]; exact hm1_lt
        exact hord (a - 1) a this
      have hnot_pos : ¬ (0 < ⟪x (a - 1), b⟫ - ⟪x (a + 2), b⟫) := by
        have : ⟪x (a - 1), b⟫ < ⟪x (a + 2), b⟫ := by rw [← hw0_m1, ← hw0_1]; linarith
        linarith
      have hnot_tie_pos : ¬ (0 < σ * ⟪x a - x (a + 1), d⟫) := by
        rwa [← hmatch]
      have htie_incr : z a < z (a + 1) := by
        rcases htie_cases with h | h
        · exact h
        · exfalso
          have : 0 < z a - z (a + 1) := sub_pos.mpr h
          have : 0 < σ * ⟪x a - x (a + 1), d⟫ := htie_sign.mp this
          exact hnot_tie_pos this
      exact numPeaks_monotone_incr hm2 z a hw_peaks hv1 hv2 hv3 htie_incr
    · -- Decreasing: w0 1 < w0 0 < w0 (-1)
      have hv1 : z (a + 1) < z (a - 1) := by
        have : ⟪x (a + 1), b⟫ < ⟪x (a - 1), b⟫ := by rw [← hw0_m1, ← hw0_0]; exact h1_lt
        exact hord (a + 1) (a - 1) this
      have hv3 : z a < z (a - 1) := by
        have : ⟪x a, b⟫ < ⟪x (a - 1), b⟫ := by rw [← hw0_m1, ← hw0_0a]; exact h1_lt
        exact hord a (a - 1) this
      have hpos_diff : 0 < ⟪x (a - 1), b⟫ - ⟪x (a + 2), b⟫ := by
        have : ⟪x (a + 2), b⟫ < ⟪x (a - 1), b⟫ := by rw [← hw0_m1, ← hw0_1]; linarith
        linarith
      have htie_pos : 0 < σ * ⟪x a - x (a + 1), d⟫ := hmatch.mp hpos_diff
      have htie_decr : z (a + 1) < z a := by
        rcases htie_cases with h | h
        · exfalso
          have : 0 < z (a + 1) - z a := sub_pos.mpr h
          have hneg : z a - z (a + 1) < 0 := by linarith
          have : 0 < z a - z (a + 1) := htie_sign.mpr htie_pos
          linarith
        · exact h
      exact numPeaks_monotone_decr hm2 z a hw_peaks hv1 hv3 htie_decr

lemma sign_match_lemma (p q : ℝ) (hp : p ≠ 0) (hq : q ≠ 0) :
    let σ : ℝ := if (p < 0 ↔ q < 0) then 1 else -1
    (0 < q ↔ 0 < σ * p) := by
  intro σ
  dsimp [σ]
  split_ifs with h
  · rw [one_mul]
    rcases lt_or_gt_of_ne hp with hp' | hp' <;> rcases lt_or_gt_of_ne hq with hq' | hq'
    · exact iff_of_false (not_lt_of_gt hq') (not_lt_of_gt hp')
    · have : q < 0 := h.mp hp'
      linarith
    · have : p < 0 := h.mpr hq'
      linarith
    · exact iff_of_true hq' hp'
  · have hneg : (-1 : ℝ) * p = -p := by ring
    rw [hneg, neg_pos]
    rcases lt_or_gt_of_ne hp with hp' | hp' <;> rcases lt_or_gt_of_ne hq with hq' | hq'
    · exfalso; apply h; exact ⟨fun _ => hq', fun _ => hp'⟩
    · exact iff_of_true hq' hp'
    · exact iff_of_false (not_lt_of_gt hq') (not_lt_of_gt hp')
    · exfalso; apply h; exact ⟨fun h_neg => absurd hp' (not_lt_of_gt h_neg), fun h_neg => absurd hq' (not_lt_of_gt h_neg)⟩

lemma splitTieSlopeSign_spec {m : ℕ} [NeZero m] (x : ZMod (m + 1) → ℝ³) (b d : ℝ³) (a : ZMod (m + 1))
    (hdir : ⟪x a - x (a + 1), d⟫ ≠ 0)
    (hq : ⟪x (a - 1), b⟫ - ⟪x (a + 2), b⟫ ≠ 0) :
    0 < ⟪x (a - 1), b⟫ - ⟪x (a + 2), b⟫ ↔ 0 < splitTieSlopeSign x b d a * ⟪x a - x (a + 1), d⟫ := by
  set p := ⟪x a - x (a + 1), d⟫
  set q := ⟪x (a - 1), b⟫ - ⟪x (a + 2), b⟫
  have hp : (0 < ⟪x (a + 1) - x a, d⟫) ↔ p < 0 := by
    have : x (a + 1) - x a = - (x a - x (a + 1)) := by abel
    rw [this, inner_neg_left, neg_pos]
  have hq_iff : (⟪x (a - 1), b⟫ < ⟪x (a + 2), b⟫) ↔ q < 0 := by
    rw [sub_lt_zero]
  have hsign : splitTieSlopeSign x b d a = if (p < 0 ↔ q < 0) then 1 else -1 := by
    unfold splitTieSlopeSign
    simp only [hp, hq_iff]
  rw [hsign]
  exact sign_match_lemma p q hdir hq

/-! ### Theorems -/

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
  have h1 := splitUnimodal_step hm x b d a 1 (Or.inl rfl) htie hdir huni (Or.inl hext)
  have h2 := splitUnimodal_step hm x b d a (-1) (Or.inr rfl) htie hdir huni (Or.inl hext)
  have h1' : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Function.Injective (fun i => ⟪x i, b + ε • d⟫) ∧
      IsCyclicUnimodal (fun i => ⟪x i, b + ε • d⟫) := by
    filter_upwards [h1] with ε hε
    have : (fun i => ⟪x i, b + (1 * ε) • d⟫) = (fun i => ⟪x i, b + ε • d⟫) := by
      ext i; simp only [one_mul]
    rwa [this] at hε
  have h2' : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Function.Injective (fun i => ⟪x i, b - ε • d⟫) ∧
      IsCyclicUnimodal (fun i => ⟪x i, b - ε • d⟫) := by
    filter_upwards [h2] with ε hε
    have : (fun i => ⟪x i, b + (-1 * ε) • d⟫) = (fun i => ⟪x i, b - ε • d⟫) := by
      ext i; simp only [neg_mul, one_mul, neg_smul, sub_eq_add_neg]
    rwa [this] at hε
  exact ⟨h1', h2'⟩

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
  intro σ
  have hσ_cases : σ = 1 ∨ σ = -1 := by
    dsimp [σ, splitTieSlopeSign]
    split_ifs <;> [exact Or.inl rfl; exact Or.inr rfl]
  have hq_ne : ⟪x (a - 1), b⟫ - ⟪x (a + 2), b⟫ ≠ 0 := by
    intro hc
    have heq : ⟪x (a - 1), b⟫ = ⟪x (a + 2), b⟫ := sub_eq_zero.mp hc
    have hw_m1 : mergedDepths (fun i => ⟪x i, b⟫) a (-1) = ⟪x (a - 1), b⟫ := mergedDepths_neg_one _ a
    have hw_1 : mergedDepths (fun i => ⟪x i, b⟫) a 1 = ⟪x (a + 2), b⟫ := mergedDepths_one (by omega) _ a
    have h_w_eq : mergedDepths (fun i => ⟪x i, b⟫) a (-1) = mergedDepths (fun i => ⟪x i, b⟫) a 1 := by
      rw [hw_m1, hw_1, heq]
    have h_m1_1 : (-1 : ZMod m) = 1 := huni.1 h_w_eq
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    have h_val := congrArg ZMod.val h_m1_1
    have : Fact (1 < n + 1) := ⟨by omega⟩
    rw [ZMod.val_neg_one, ZMod.val_one] at h_val
    omega
  have hmatch : 0 < ⟪x (a - 1), b⟫ - ⟪x (a + 2), b⟫ ↔ 0 < σ * ⟪x a - x (a + 1), d⟫ :=
    splitTieSlopeSign_spec x b d a hdir hq_ne
  exact splitUnimodal_step hm x b d a σ hσ_cases htie hdir huni (Or.inr ⟨hmono, hmatch⟩)

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
  set w0 := mergedDepths (fun i => ⟪x i, b⟫) a
  have hinj : Function.Injective w0 := huni.1
  have : Fact (1 < m) := ⟨by omega⟩
  have hm1_ne : (-1 : ZMod m) ≠ 0 := by
    intro h
    apply one_ne_zero (α := ZMod m)
    calc (1 : ZMod m) = - (-1) := by ring
    _ = - 0 := by rw [h]
    _ = 0 := neg_zero
  have h1_ne : (1 : ZMod m) ≠ 0 := one_ne_zero (α := ZMod m)
  have hm1_ne_w : w0 (-1) ≠ w0 0 := fun h => hm1_ne (hinj h)
  have h1_ne_w : w0 1 ≠ w0 0 := fun h => h1_ne (hinj h)
  rcases lt_or_gt_of_ne hm1_ne_w with h_m1 | h_m1 <;> rcases lt_or_gt_of_ne h1_ne_w with h_1 | h_1
  · -- Extremum (Max)
    have hext : IsMergedExtremum w0 := Or.inl ⟨h_m1, h_1⟩
    have h1 := (splitUnimodal_extremum hm x b d a htie hdir huni hext).1
    have h1' : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        Function.Injective (fun i => ⟪x i, b + (1 * ε) • d⟫) ∧
        IsCyclicUnimodal (fun i => ⟪x i, b + (1 * ε) • d⟫) := by
      filter_upwards [h1] with ε hε
      have : (fun i => ⟪x i, b + ε • d⟫) = (fun i => ⟪x i, b + (1 * ε) • d⟫) := by
        ext i; simp only [one_mul]
      rwa [this] at hε
    refine ⟨1, Or.inl rfl, h1'⟩
  · -- Monotone (Incr)
    have hmono : IsMergedMonotone w0 := Or.inl ⟨h_m1, h_1⟩
    set σ := splitTieSlopeSign x b d a
    have hσ : σ = 1 ∨ σ = -1 := by
      dsimp [σ, splitTieSlopeSign]; split_ifs <;> [exact Or.inl rfl; exact Or.inr rfl]
    refine ⟨σ, hσ, splitUnimodal_monotone hm x b d a htie hdir huni hmono⟩
  · -- Monotone (Decr)
    have hmono : IsMergedMonotone w0 := Or.inr ⟨h_1, h_m1⟩
    set σ := splitTieSlopeSign x b d a
    have hσ : σ = 1 ∨ σ = -1 := by
      dsimp [σ, splitTieSlopeSign]; split_ifs <;> [exact Or.inl rfl; exact Or.inr rfl]
    refine ⟨σ, hσ, splitUnimodal_monotone hm x b d a htie hdir huni hmono⟩
  · -- Extremum (Min)
    have hext : IsMergedExtremum w0 := Or.inr ⟨h_m1, h_1⟩
    have h1 := (splitUnimodal_extremum hm x b d a htie hdir huni hext).1
    have h1' : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        Function.Injective (fun i => ⟪x i, b + (1 * ε) • d⟫) ∧
        IsCyclicUnimodal (fun i => ⟪x i, b + (1 * ε) • d⟫) := by
      filter_upwards [h1] with ε hε
      have : (fun i => ⟪x i, b + ε • d⟫) = (fun i => ⟪x i, b + (1 * ε) • d⟫) := by
        ext i; simp only [one_mul]
      rwa [this] at hε
    refine ⟨1, Or.inl rfl, h1'⟩

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
