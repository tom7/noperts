module

public import Minimality.DiagCross
public import Minimality.RimCell
public import Minimality.Slide
public import Minimality.UnimodalCert

@[expose] public section

open scoped RealInnerProductSpace Topology
open Filter

namespace Minimality.T24.Q45

/-!
# Generic Corner Swap Lemma (`cornerU`, Q45 Plan Item 6)

This module provides the generic swap lemma `cornerU` and its mirror for quad rims along an affine
arc of views `u(ε) = b + ε • d` for `ε ∈ 𝓝[>] 0`.

## Mathematical Setting

Let `p : ZMod 4 → ℝ³` be a fixed quad rim with DiagCross convention
`κ := det3 (p 2 - p 0) (p 3 - p 1) (p 0 - p 1)`.
Consider the depth values along `u(ε)`: `z(ε)(i) := ⟪p i, u(ε)⟫`.

By Lemma K (`Minimality.T24.Q45.diagCross_not_high` / `diagCross_not_low`):
- When `ρ * κ < 0`, pair `{0, 2}` cannot be strictly above pair `{1, 3}`:
  `¬ (max ⟪p 1, u⟫ ⟪p 3, u⟫ ≤ min ⟪p 0, u⟫ ⟪p 2, u⟫)`.
  This is equivalent to `min (z 0) (z 2) < max (z 1) (z 3)`, which yields the `hn` disjunction of
  `RimCell.isCyclicUnimodal_four`.
- When pair `{1, 3}` is strictly not above `{0, 2}` at the base view `b`:
  `min ⟪p 1, b⟫ ⟪p 3, b⟫ < max ⟪p 0, b⟫ ⟪p 2, b⟫`,
  this condition persists for small `ε > 0` by continuity, yielding the `hp` disjunction.
- When no pairwise difference `p i - p j` vanishes on both `b` and `d`, depth values are eventually
  injective on `ZMod 4`.
Together, `isCyclicUnimodal_four` ensures that `z(ε)` is cyclically unimodal (and thus strictly
unimodal via `strictUnimodal_of_cyclic`).

## Frame Duality & Corner Leaf Usage

Under a global view negation `u ↦ -u`:
- The orientation scalar flips: `ρ ↦ -ρ`.
- The rim determinant `κ` is intrinsic to the vertices `p` and remains unchanged: `κ ↦ κ`.
- Therefore, the product `ρ * κ` flips sign: `(ρ * κ) ↦ -(ρ * κ)`.
- The depth values negate: `z(i) ↦ -z(i)`, which swaps "high" and "low".

Consequently:
- In the doc frame ($u_{\text{doc}} \approx e_5 - \varepsilon e_4$, $\rho_{\text{doc}} = +1$):
  - Corner $B_1$ (rim 6402) has $\kappa < 0$, so $\rho_{\text{doc}} \kappa < 0$.
    Lemma K forbids $\{0, 2\}$ high ($\{6, 0\}$ high). At base $e_5$, $\{1, 3\}$ high fails strictly.
    Thus $B_1$ uses `cornerU`.
- In our frame ($u = -u_{\text{doc}} \approx -e_5 + \varepsilon e_4$, $\rho_{\text{our}} = -1$):
  - Corner $B_1$ (rim 6402) has $\rho_{\text{our}} \kappa > 0$.
    Lemma K (`diagCross_not_low`) forbids $\{0, 2\}$ low ($\{6, 0\}$ low, corresponding to high in doc).
    At base $-e_5$, $\{0, 2\}$ high fails strictly (`min z0 z2 < max z1 z3`).
    Thus $B_1$ in our frame uses `cornerU_mirror`.
- Both `cornerU` and `cornerU_mirror` are stated frame-free with explicit $\rho, \kappa, b, d$.
-/

/-- Order helper: when `min {z0, z2} < max {z1, z3}`, at least one `zk < zl` holds
with `k ∈ {0, 2}, l ∈ {1, 3}`. This supplies the `hn` disjunction of `isCyclicUnimodal_four`. -/
lemma hn_of_min_lt_max {z : ZMod 4 → ℝ}
    (h : min (z 0) (z 2) < max (z 1) (z 3)) :
    z 0 < z 1 ∨ z 0 < z 3 ∨ z 2 < z 1 ∨ z 2 < z 3 := by
  contrapose! h
  rcases h with ⟨h1, h2, h3, h4⟩
  exact max_le (le_min h1 h3) (le_min h2 h4)

/-- Order helper: when `min {z1, z3} < max {z0, z2}`, at least one `zl < zk` holds
with `l ∈ {1, 3}, k ∈ {0, 2}`. This supplies the `hp` disjunction of `isCyclicUnimodal_four`. -/
lemma hp_of_min_lt_max {z : ZMod 4 → ℝ}
    (h : min (z 1) (z 3) < max (z 0) (z 2)) :
    z 1 < z 0 ∨ z 3 < z 0 ∨ z 1 < z 2 ∨ z 3 < z 2 := by
  contrapose! h
  rcases h with ⟨h1, h2, h3, h4⟩
  exact max_le (le_min h1 h2) (le_min h3 h4)

/-- Contrapositive conversion: negation of `max c d ≤ min a b` is `min a b < max c d`. -/
lemma min_lt_max_of_not_le {a b c d : ℝ} (h : ¬ (max c d ≤ min a b)) :
    min a b < max c d :=
  lt_of_not_ge h

/-- Strict inequality between inner products along `b` persists along `b + ε • d` for small `ε > 0`. -/
lemma eventually_inner_lt (v w b d : ℝ³) (h : ⟪v, b⟫ < ⟪w, b⟫) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪v, b + ε • d⟫ < ⟪w, b + ε • d⟫ := by
  have hlin : ∀ x : ℝ³, ∀ ε : ℝ, ⟪x, b + ε • d⟫ = ⟪x, b⟫ + ε * ⟪x, d⟫ := by
    intro x ε; rw [inner_add_right, real_inner_smul_right]
  filter_upwards [Minimality.eventually_pos_affine (A := ⟪w, b⟫ - ⟪v, b⟫) (B := ⟪w, d⟫ - ⟪v, d⟫)
    (Or.inl (sub_pos.mpr h))] with ε hε
  rw [hlin, hlin]
  linarith

/-- Strict failure of `{1, 3}` high at `b` persists along `b + ε • d` for small `ε > 0`. -/
lemma eventually_min13_lt_max02 (p : ZMod 4 → ℝ³) (b d : ℝ³)
    (hbase : min ⟪p 1, b⟫ ⟪p 3, b⟫ < max ⟪p 0, b⟫ ⟪p 2, b⟫) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), min ⟪p 1, b + ε • d⟫ ⟪p 3, b + ε • d⟫ < max ⟪p 0, b + ε • d⟫ ⟪p 2, b + ε • d⟫ := by
  have hdisj := hp_of_min_lt_max (z := fun i => ⟪p i, b⟫) hbase
  rcases hdisj with h10 | h30 | h12 | h32
  · filter_upwards [eventually_inner_lt (p 1) (p 0) b d h10] with ε hε
    calc
      min ⟪p 1, b + ε • d⟫ ⟪p 3, b + ε • d⟫ ≤ ⟪p 1, b + ε • d⟫ := min_le_left _ _
      _ < ⟪p 0, b + ε • d⟫ := hε
      _ ≤ max ⟪p 0, b + ε • d⟫ ⟪p 2, b + ε • d⟫ := le_max_left _ _
  · filter_upwards [eventually_inner_lt (p 3) (p 0) b d h30] with ε hε
    calc
      min ⟪p 1, b + ε • d⟫ ⟪p 3, b + ε • d⟫ ≤ ⟪p 3, b + ε • d⟫ := min_le_right _ _
      _ < ⟪p 0, b + ε • d⟫ := hε
      _ ≤ max ⟪p 0, b + ε • d⟫ ⟪p 2, b + ε • d⟫ := le_max_left _ _
  · filter_upwards [eventually_inner_lt (p 1) (p 2) b d h12] with ε hε
    calc
      min ⟪p 1, b + ε • d⟫ ⟪p 3, b + ε • d⟫ ≤ ⟪p 1, b + ε • d⟫ := min_le_left _ _
      _ < ⟪p 2, b + ε • d⟫ := hε
      _ ≤ max ⟪p 0, b + ε • d⟫ ⟪p 2, b + ε • d⟫ := le_max_right _ _
  · filter_upwards [eventually_inner_lt (p 3) (p 2) b d h32] with ε hε
    calc
      min ⟪p 1, b + ε • d⟫ ⟪p 3, b + ε • d⟫ ≤ ⟪p 3, b + ε • d⟫ := min_le_right _ _
      _ < ⟪p 2, b + ε • d⟫ := hε
      _ ≤ max ⟪p 0, b + ε • d⟫ ⟪p 2, b + ε • d⟫ := le_max_right _ _

/-- Strict failure of `{0, 2}` high at `b` persists along `b + ε • d` for small `ε > 0`. -/
lemma eventually_min02_lt_max13 (p : ZMod 4 → ℝ³) (b d : ℝ³)
    (hbase : min ⟪p 0, b⟫ ⟪p 2, b⟫ < max ⟪p 1, b⟫ ⟪p 3, b⟫) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), min ⟪p 0, b + ε • d⟫ ⟪p 2, b + ε • d⟫ < max ⟪p 1, b + ε • d⟫ ⟪p 3, b + ε • d⟫ := by
  have hdisj := hn_of_min_lt_max (z := fun i => ⟪p i, b⟫) hbase
  rcases hdisj with h01 | h03 | h21 | h23
  · filter_upwards [eventually_inner_lt (p 0) (p 1) b d h01] with ε hε
    calc
      min ⟪p 0, b + ε • d⟫ ⟪p 2, b + ε • d⟫ ≤ ⟪p 0, b + ε • d⟫ := min_le_left _ _
      _ < ⟪p 1, b + ε • d⟫ := hε
      _ ≤ max ⟪p 1, b + ε • d⟫ ⟪p 3, b + ε • d⟫ := le_max_left _ _
  · filter_upwards [eventually_inner_lt (p 0) (p 3) b d h03] with ε hε
    calc
      min ⟪p 0, b + ε • d⟫ ⟪p 2, b + ε • d⟫ ≤ ⟪p 0, b + ε • d⟫ := min_le_left _ _
      _ < ⟪p 3, b + ε • d⟫ := hε
      _ ≤ max ⟪p 1, b + ε • d⟫ ⟪p 3, b + ε • d⟫ := le_max_right _ _
  · filter_upwards [eventually_inner_lt (p 2) (p 1) b d h21] with ε hε
    calc
      min ⟪p 0, b + ε • d⟫ ⟪p 2, b + ε • d⟫ ≤ ⟪p 2, b + ε • d⟫ := min_le_right _ _
      _ < ⟪p 1, b + ε • d⟫ := hε
      _ ≤ max ⟪p 1, b + ε • d⟫ ⟪p 3, b + ε • d⟫ := le_max_left _ _
  · filter_upwards [eventually_inner_lt (p 2) (p 3) b d h23] with ε hε
    calc
      min ⟪p 0, b + ε • d⟫ ⟪p 2, b + ε • d⟫ ≤ ⟪p 2, b + ε • d⟫ := min_le_right _ _
      _ < ⟪p 3, b + ε • d⟫ := hε
      _ ≤ max ⟪p 1, b + ε • d⟫ ⟪p 3, b + ε • d⟫ := le_max_right _ _

/-- An affine expression `A + ε * B` with `A ≠ 0 ∨ B ≠ 0` is eventually nonzero in `𝓝[>] 0`. -/
lemma eventually_ne_affine_or {A B : ℝ} (h : A ≠ 0 ∨ B ≠ 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), A + ε * B ≠ 0 := by
  rcases h with hA | hB
  · by_cases hB : B = 0
    · filter_upwards with ε
      rw [hB, mul_zero, add_zero]
      exact hA
    · exact eventually_ne_affine hB
  · exact eventually_ne_affine hB

/-- An affine depth function on `ZMod 4` is eventually injective along `b + ε • d` if no pairwise
difference vanishes on both `b` and `d`. -/
lemma eventually_injective_quad (p : ZMod 4 → ℝ³) (b d : ℝ³)
    (hgen : ∀ i j : ZMod 4, i ≠ j → ⟪p i - p j, b⟫ ≠ 0 ∨ ⟪p i - p j, d⟫ ≠ 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), Function.Injective (fun i => ⟪p i, b + ε • d⟫) := by
  have hlin : ∀ i j : ZMod 4, ∀ ε : ℝ,
      ⟪p i, b + ε • d⟫ - ⟪p j, b + ε • d⟫ = ⟪p i - p j, b⟫ + ε * ⟪p i - p j, d⟫ := by
    intro i j ε
    rw [← inner_sub_left, inner_add_right, real_inner_smul_right]
  have hevij : ∀ i j : ZMod 4, ∀ᶠ ε in 𝓝[>] (0 : ℝ), i ≠ j → ⟪p i, b + ε • d⟫ ≠ ⟪p j, b + ε • d⟫ := by
    intro i j
    by_cases hij : i = j
    · filter_upwards with ε h; exact (h hij).elim
    · have hg := hgen i j hij
      have hev := eventually_ne_affine_or hg
      filter_upwards [hev] with ε hε _ heq
      have : ⟪p i, b + ε • d⟫ - ⟪p j, b + ε • d⟫ = 0 := sub_eq_zero.mpr heq
      rw [hlin] at this
      exact hε this
  have hall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i j : ZMod 4, i ≠ j → ⟪p i, b + ε • d⟫ ≠ ⟪p j, b + ε • d⟫ := by
    rw [eventually_all]
    intro i
    rw [eventually_all]
    intro j
    exact hevij i j
  filter_upwards [hall] with ε h_all
  intro i j heq
  by_contra hij
  exact h_all i j hij heq

/-- **Lemma cornerU (Eventual Formulation).**
When `ρ * κ < 0`, Lemma K (`diagCross_not_high`) forbids pair `{0, 2}` from being strictly above `{1, 3}`.
If pair `{1, 3}` is also not strictly above `{0, 2}` eventually along the arc, depth values are
eventually injective and cyclically unimodal. -/
theorem cornerU_of_eventual (p : ZMod 4 → ℝ³) (b d : ℝ³) (ρ : ℝ)
    (hcyc : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i, 0 < ρ * triD p (b + ε • d) i)
    (hk : ρ * det3 (p 2 - p 0) (p 3 - p 1) (p 0 - p 1) < 0)
    (hbase_ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), min ⟪p 1, b + ε • d⟫ ⟪p 3, b + ε • d⟫ < max ⟪p 0, b + ε • d⟫ ⟪p 2, b + ε • d⟫)
    (hgen : ∀ i j, i ≠ j → ⟪p i - p j, b⟫ ≠ 0 ∨ ⟪p i - p j, d⟫ ≠ 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Function.Injective (fun i => ⟪p i, b + ε • d⟫) ∧
      IsCyclicUnimodal (fun i => ⟪p i, b + ε • d⟫) := by
  have hinj_ev := eventually_injective_quad p b d hgen
  filter_upwards [hcyc, hbase_ev, hinj_ev] with ε hc hb hinj
  refine ⟨hinj, ?_⟩
  have hnot_high := diagCross_not_high p (b + ε • d) hc hk
  have hmin_lt := min_lt_max_of_not_le hnot_high
  have hn := hn_of_min_lt_max (z := fun i => ⟪p i, b + ε • d⟫) hmin_lt
  have hp := hp_of_min_lt_max (z := fun i => ⟪p i, b + ε • d⟫) hb
  exact Minimality.RimCell.isCyclicUnimodal_four (fun i => ⟪p i, b + ε • d⟫) hinj hn hp

/-- **Lemma cornerU (Base-View Formulation).**
Base-view form of `cornerU`: strict failure of `{1, 3}` high at the base view `b` persists for small `ε > 0`. -/
theorem cornerU (p : ZMod 4 → ℝ³) (b d : ℝ³) (ρ : ℝ)
    (hcyc : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i, 0 < ρ * triD p (b + ε • d) i)
    (hk : ρ * det3 (p 2 - p 0) (p 3 - p 1) (p 0 - p 1) < 0)
    (hbase : min ⟪p 1, b⟫ ⟪p 3, b⟫ < max ⟪p 0, b⟫ ⟪p 2, b⟫)
    (hgen : ∀ i j, i ≠ j → ⟪p i - p j, b⟫ ≠ 0 ∨ ⟪p i - p j, d⟫ ≠ 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Function.Injective (fun i => ⟪p i, b + ε • d⟫) ∧
      IsCyclicUnimodal (fun i => ⟪p i, b + ε • d⟫) := by
  have hbase_ev := eventually_min13_lt_max02 p b d hbase
  exact cornerU_of_eventual p b d ρ hcyc hk hbase_ev hgen

/-- Strict unimodality corollary for `cornerU`. -/
theorem cornerU_strictUnimodal (p : ZMod 4 → ℝ³) (b d : ℝ³) (ρ : ℝ)
    (hcyc : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i, 0 < ρ * triD p (b + ε • d) i)
    (hk : ρ * det3 (p 2 - p 0) (p 3 - p 1) (p 0 - p 1) < 0)
    (hbase : min ⟪p 1, b⟫ ⟪p 3, b⟫ < max ⟪p 0, b⟫ ⟪p 2, b⟫)
    (hgen : ∀ i j, i ≠ j → ⟪p i - p j, b⟫ ≠ 0 ∨ ⟪p i - p j, d⟫ ≠ 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), Minimality.StrictUnimodal (fun i => ⟪p i, b + ε • d⟫) := by
  have hu := cornerU p b d ρ hcyc hk hbase hgen
  filter_upwards [hu] with ε hε
  exact Minimality.strictUnimodal_of_cyclic (by decide) hε.2

/-- **Lemma cornerU Mirror (Eventual Formulation).**
When `0 < ρ * κ`, Lemma K (`diagCross_not_low`) forbids pair `{0, 2}` from being strictly below `{1, 3}`. -/
theorem cornerU_mirror_of_eventual (p : ZMod 4 → ℝ³) (b d : ℝ³) (ρ : ℝ)
    (hcyc : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i, 0 < ρ * triD p (b + ε • d) i)
    (hk : 0 < ρ * det3 (p 2 - p 0) (p 3 - p 1) (p 0 - p 1))
    (hbase_ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), min ⟪p 0, b + ε • d⟫ ⟪p 2, b + ε • d⟫ < max ⟪p 1, b + ε • d⟫ ⟪p 3, b + ε • d⟫)
    (hgen : ∀ i j, i ≠ j → ⟪p i - p j, b⟫ ≠ 0 ∨ ⟪p i - p j, d⟫ ≠ 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Function.Injective (fun i => ⟪p i, b + ε • d⟫) ∧
      IsCyclicUnimodal (fun i => ⟪p i, b + ε • d⟫) := by
  have hinj_ev := eventually_injective_quad p b d hgen
  filter_upwards [hcyc, hbase_ev, hinj_ev] with ε hc hb hinj
  refine ⟨hinj, ?_⟩
  have hnot_low := diagCross_not_low p (b + ε • d) hc hk
  have hmin_lt := min_lt_max_of_not_le hnot_low
  have hn := hn_of_min_lt_max (z := fun i => ⟪p i, b + ε • d⟫) hb
  have hp := hp_of_min_lt_max (z := fun i => ⟪p i, b + ε • d⟫) hmin_lt
  exact Minimality.RimCell.isCyclicUnimodal_four (fun i => ⟪p i, b + ε • d⟫) hinj hn hp

/-- **Lemma cornerU Mirror (Base-View Formulation).**
Base-view form of the mirror: strict failure of `{0, 2}` high (`min z0 z2 < max z1 z3`) at `b` persists. -/
theorem cornerU_mirror (p : ZMod 4 → ℝ³) (b d : ℝ³) (ρ : ℝ)
    (hcyc : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i, 0 < ρ * triD p (b + ε • d) i)
    (hk : 0 < ρ * det3 (p 2 - p 0) (p 3 - p 1) (p 0 - p 1))
    (hbase : min ⟪p 0, b⟫ ⟪p 2, b⟫ < max ⟪p 1, b⟫ ⟪p 3, b⟫)
    (hgen : ∀ i j, i ≠ j → ⟪p i - p j, b⟫ ≠ 0 ∨ ⟪p i - p j, d⟫ ≠ 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Function.Injective (fun i => ⟪p i, b + ε • d⟫) ∧
      IsCyclicUnimodal (fun i => ⟪p i, b + ε • d⟫) := by
  have hbase_ev := eventually_min02_lt_max13 p b d hbase
  exact cornerU_mirror_of_eventual p b d ρ hcyc hk hbase_ev hgen

/-- Strict unimodality corollary for `cornerU_mirror`. -/
theorem cornerU_mirror_strictUnimodal (p : ZMod 4 → ℝ³) (b d : ℝ³) (ρ : ℝ)
    (hcyc : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i, 0 < ρ * triD p (b + ε • d) i)
    (hk : 0 < ρ * det3 (p 2 - p 0) (p 3 - p 1) (p 0 - p 1))
    (hbase : min ⟪p 0, b⟫ ⟪p 2, b⟫ < max ⟪p 1, b⟫ ⟪p 3, b⟫)
    (hgen : ∀ i j, i ≠ j → ⟪p i - p j, b⟫ ≠ 0 ∨ ⟪p i - p j, d⟫ ≠ 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), Minimality.StrictUnimodal (fun i => ⟪p i, b + ε • d⟫) := by
  have hu := cornerU_mirror p b d ρ hcyc hk hbase hgen
  filter_upwards [hu] with ε hε
  exact Minimality.strictUnimodal_of_cyclic (by decide) hε.2

end Minimality.T24.Q45
