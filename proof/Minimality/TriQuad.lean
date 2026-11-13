module

public import Minimality.TriShadow

@[expose] public section

/-!
# Lemma T for two quadrilaterals sharing a vertex

Corollary T1 of `FEWER-FACES-PROOFS.md` §7 for two quadrilateral facets that
meet in one vertex and contain all seven points (types 02, 07, 09, 14, 18, 20).
This file works in the oblique frame of `TriShadow.lean`: each quadrilateral is
a convex quadrilateral in its `(t, z)`-plane with the apex at `t = 0`, and its
upper and lower chains from the apex to the far vertex feed
`isRupert_triShadow`.
-/

namespace Minimality

open Finset Filter Topology
open scoped RealInnerProductSpace

/-- A chain `(ca l, cz l)`, `l ≤ m`, of the point set `Q` from the apex `(0, z0)`
to the far point: increasing in `t`, through points of `Q`, ending at the unique
point of largest `t`, with every other point of `Q` strictly on the `s`-side of
each segment (`s = 1`: below, the upper chain; `s = -1`: above, the lower one). -/
structure ChainOK (Q : ℝ → ℝ → Prop) (z0 s : ℝ) (m : ℕ) (ca cz : ℕ → ℝ) : Prop where
  one_le : 1 ≤ m
  start : ca 0 = 0 ∧ cz 0 = z0
  inc : ∀ l, l < m → ca l < ca (l + 1)
  mem : ∀ l, l ≤ m → Q (ca l) (cz l)
  far : ∀ a z, Q a z → ¬ (a = ca m ∧ z = cz m) → a < ca m
  side : ∀ a z, Q a z → ∀ l, l < m → ¬ (a = ca l ∧ z = cz l) → ¬ (a = ca (l + 1) ∧ z = cz (l + 1)) →
    s * ((ca (l + 1) - ca l) * (z - cz l) - (cz (l + 1) - cz l) * (a - ca l)) < 0

set_option linter.unnecessarySeqFocus false

/-- All chains of one point set end at the same far point. -/
theorem ChainOK.far_eq {Q : ℝ → ℝ → Prop} {z0 z0' s s' : ℝ} {m m' : ℕ} {ca cz ca' cz' : ℕ → ℝ}
    (h : ChainOK Q z0 s m ca cz) (h' : ChainOK Q z0' s' m' ca' cz') :
    ca m = ca' m' ∧ cz m = cz' m' := by
  by_contra hne
  have h1 := h.far _ _ (h'.mem m' le_rfl) (fun e => hne ⟨e.1.symm, e.2.symm⟩)
  have h2 := h'.far _ _ (h.mem m le_rfl) hne
  linarith

theorem ChainOK.far_pos {Q : ℝ → ℝ → Prop} {z0 s : ℝ} {m : ℕ} {ca cz : ℕ → ℝ}
    (h : ChainOK Q z0 s m ca cz) : 0 < ca m := by
  have : ∀ j, j ≤ m → ca 0 < ca j ∨ j = 0 := by
    intro j hj
    induction j with
    | zero => right; rfl
    | succ j ih =>
      left
      rcases ih (by omega) with h' | h'
      · exact lt_trans h' (h.inc j (by omega))
      · subst h'; exact h.inc 0 (by omega)
  rcases this m le_rfl with h' | h'
  · rw [h.start.1] at h'; exact h'
  · have := h.one_le; omega

/-! ### Chains of a quadrilateral seen along an edge, and of triangles -/

end Minimality

end
