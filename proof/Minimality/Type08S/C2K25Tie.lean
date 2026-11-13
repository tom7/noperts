module

public import Minimality.Type08S.C2K18A
public import Minimality.Type08S.C2K19C

@[expose] public section

/-!
# K25 tie lemma (design sketch; see HANDOFF.md)

A `k18_cone_cell` whose depth comparisons are WEAK (`z s ≤ z t`) and whose ties are broken on the cone by the pair's
tie functional `m(s,t) = (⟪X t - X s, p⟫, ⟪X t - X s, q⟫)` (`w t - w s = m · v`, `k18_wdiff`).  Same for the tilt
tests: first-order term `≥ 0`, and at `= 0` the linear tilt term is positive on the cone.
STATUS: compiles (leanchk exit 0, no sorry); scratch, not yet in the tree.
-/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- One certificate step `s ≤lex t` that is weak in depth: `z s ≤ z t`, and on a depth tie the tie functional of
`(s, t)` is positive on the open cone of `L` (so `w s < w t`). -/
def K25Step (p q r d : ℝ³) (L : List (ℝ × ℝ)) (s t : ℝ × ℝ × ℝ) : Prop :=
  ⟪fpoint p q r d s, r⟫ ≤ ⟪fpoint p q r d t, r⟫ ∧
    (⟪fpoint p q r d s, r⟫ = ⟪fpoint p q r d t, r⟫ → ∀ v1 v2 : ℝ, k18Cone L v1 v2 →
      0 < ⟪fpoint p q r d t - fpoint p q r d s, p⟫ * v1 + ⟪fpoint p q r d t - fpoint p q r d s, q⟫ * v2)

theorem k25_step_lexLt {p q r d : ℝ³} {L : List (ℝ × ℝ)} {s t : ℝ × ℝ × ℝ} {v1 v2 : ℝ}
    (h : K25Step p q r d L s t) (hv : k18Cone L v1 v2) :
    LexLt (⟪fpoint p q r d s, r⟫, ⟪fpoint p q r d s, fcomb p q r v1 v2 0⟫)
      (⟪fpoint p q r d t, r⟫, ⟪fpoint p q r d t, fcomb p q r v1 v2 0⟫) := by
  rcases h.1.lt_or_eq with h1 | h1
  · exact Or.inl h1
  · refine Or.inr ⟨h1, ?_⟩
    have e := k18_wdiff p q r d t s v1 v2
    have := h.2 h1 v1 v2 hv
    simp only
    linarith

/-- **Tie cell (peak form).**  `k18_cone_cell` with `hlex` replaced by a weak-depth peak certificate: peak `i0`
above both neighbours, every other vertex below one neighbour, each step a `K25Step` (depth `≤`, ties broken by the
pair's tie functional on the cone). -/
theorem k25_tie_cell (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (Y : ZMod k → ℝ × ℝ × ℝ) (hYinj : ∀ i j, Y i = Y j → i = j) (hmem : ∀ i, fpoint p q r d (Y i) ∈ V)
    (L : List (ℝ × ℝ)) (hL : L ≠ [])
    (hcyc : ∀ v1 v2 : ℝ, k18Cone L v1 v2 → ∀ D : ℝ, 0 < D → ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 →
      TSc D (Y (i + 1) - Y i) (Y j - Y i) (v1, v2, 0))
    (hrest : ∀ y ∈ V, (∀ j, y ≠ fpoint p q r d (Y j)) → ∃ t, y = fpoint p q r d t ∧
      ∀ v1 v2 : ℝ, k18Cone L v1 v2 → ∀ D : ℝ, 0 < D → ∀ i, TSc D (Y (i + 1) - Y i) (t - Y i) (v1, v2, 0))
    (i0 : ZMod k) (hP1 : K25Step p q r d L (Y (i0 - 1)) (Y i0)) (hP2 : K25Step p q r d L (Y (i0 + 1)) (Y i0))
    (hnb : ∀ i, i ≠ i0 → K25Step p q r d L (Y i) (Y (i - 1)) ∨ K25Step p q r d L (Y i) (Y (i + 1)))
    {ρ1 ρ2 δ1 δ2 : ℝ} (hray : ∀ l ∈ L, k18LexPos (l.1 * ρ1 + l.2 * ρ2) (l.1 * δ1 + l.2 * δ2)) :
    HasLexCellAt V r :=
  k18_cone_cell V p q r d hΔ hk Y hYinj hmem L hL hcyc hrest
    (fun v1 v2 hv hinj => k19_lexUni_nb _ _ hinj i0 (k25_step_lexLt hP1 hv) (k25_step_lexLt hP2 hv)
      (fun i hi => (hnb i hi).imp (fun h => k25_step_lexLt h hv) (fun h => k25_step_lexLt h hv))) hray

/-- **Tie cell (free top pair)**: as `k25_tie_cell`, but the order of the adjacent top pair `i0, i0 + 1` is left
free (decided by the generic tilt, `k19_lexUni_nb2`); covers a 2-way top tie with no tie functional. -/
theorem k25_tie_cell2 (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (Y : ZMod k → ℝ × ℝ × ℝ) (hYinj : ∀ i j, Y i = Y j → i = j) (hmem : ∀ i, fpoint p q r d (Y i) ∈ V)
    (L : List (ℝ × ℝ)) (hL : L ≠ [])
    (hcyc : ∀ v1 v2 : ℝ, k18Cone L v1 v2 → ∀ D : ℝ, 0 < D → ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 →
      TSc D (Y (i + 1) - Y i) (Y j - Y i) (v1, v2, 0))
    (hrest : ∀ y ∈ V, (∀ j, y ≠ fpoint p q r d (Y j)) → ∃ t, y = fpoint p q r d t ∧
      ∀ v1 v2 : ℝ, k18Cone L v1 v2 → ∀ D : ℝ, 0 < D → ∀ i, TSc D (Y (i + 1) - Y i) (t - Y i) (v1, v2, 0))
    (i0 : ZMod k) (hne : i0 + 1 ≠ i0)
    (hP1 : K25Step p q r d L (Y (i0 - 1)) (Y i0)) (hP2 : K25Step p q r d L (Y (i0 + 1 + 1)) (Y (i0 + 1)))
    (hnb : ∀ i, i ≠ i0 → i ≠ i0 + 1 →
      K25Step p q r d L (Y i) (Y (i - 1)) ∨ K25Step p q r d L (Y i) (Y (i + 1)))
    {ρ1 ρ2 δ1 δ2 : ℝ} (hray : ∀ l ∈ L, k18LexPos (l.1 * ρ1 + l.2 * ρ2) (l.1 * δ1 + l.2 * δ2)) :
    HasLexCellAt V r :=
  k18_cone_cell V p q r d hΔ hk Y hYinj hmem L hL hcyc hrest
    (fun v1 v2 hv hinj => k19_lexUni_nb2 _ _ hinj i0 hne (k25_step_lexLt hP1 hv) (k25_step_lexLt hP2 hv)
      (fun i hi hi' => (hnb i hi hi').imp (fun h => k25_step_lexLt h hv) (fun h => k25_step_lexLt h hv))) hray

end C2
end Type08Sp
end Minimality
