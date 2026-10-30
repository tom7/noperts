module

public import Minimality.Type08S.P2Defs

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# G-RS, step 0: robust unimodality passes to ordinal refinements.

If `z'` keeps every strict comparison of `z` (e.g. `z' = z + t w`, `t > 0` small), and `z` is robustly
unimodal, so is `z'`.  (From `rob_weak4`, `rob_levelL`; this replaces `QRob_open` + the converse
`QRob → IsRobustUnimodal`, which is false for the level triangle.)
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality

theorem IsRobustUnimodal.refine {k : ℕ} [NeZero k] {z z' : ZMod k → ℝ} (hz : IsRobustUnimodal z)
    (hH : ∀ a b, z a < z b → z' a < z' b) : IsRobustUnimodal z' where
  noPeaks B a b c d hab hbc hcd hdk h := by
    obtain ⟨h1, h2, h3, h4⟩ := h
    have hw : ∀ x y, z' x < z' y → z x ≤ z y := fun x y hxy => by
      by_contra hc
      exact absurd (hH _ _ (not_le.mp hc)) (not_lt.mpr hxy.le)
    exact CaseC18.rob_weak4 hz (P0 := B + a) (P1 := B + b) (P2 := B + c) (P3 := B + d)
      ⟨B, a, b, c, d, hab, hbc, hcd, hdk, rfl, rfl, rfl, rfl⟩ (hw _ _ h1) (hw _ _ h2) (hw _ _ h3)
      (hw _ _ h4)
  noTriple i j l hij hjl hil h1 h2 := by
    have heq : ∀ x y, z' x = z' y → z x = z y := fun x y h => by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hl | hl
      · exact absurd h (hH _ _ hl).ne
      · exact absurd h.symm (hH _ _ hl).ne
    exact hz.noTriple i j l hij hjl hil (heq _ _ h1) (heq _ _ h2)
  noLevelRun B a b c d hab hbc hcd hdk h := by
    have hw : ∀ x y, z' x < z' y → z x ≤ z y := fun x y hxy => by
      by_contra hc
      exact absurd (hH _ _ (not_le.mp hc)) (not_lt.mpr hxy.le)
    have heq : ∀ x y, z' x = z' y → z x = z y := fun x y h => by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hl | hl
      · exact absurd h (hH _ _ hl).ne
      · exact absurd h.symm (hH _ _ hl).ne
    refine ⟨fun ⟨h1, h2⟩ => ?_, fun ⟨h1, h2⟩ => ?_⟩
    · exact CaseC18.rob_levelL hz (P0 := B + a) (P1 := B + b) (P2 := B + c) (P3 := B + d)
        ⟨B, a, b, c, d, hab, hbc, hcd, hdk, rfl, rfl, rfl, rfl⟩ (heq _ _ h)
        (Or.inl ⟨hw _ _ h1, hw _ _ h2⟩)
    · exact CaseC18.rob_levelL hz (P0 := B + a) (P1 := B + b) (P2 := B + c) (P3 := B + d)
        ⟨B, a, b, c, d, hab, hbc, hcd, hdk, rfl, rfl, rfl, rfl⟩ (heq _ _ h)
        (Or.inr ⟨hw _ _ h1, hw _ _ h2⟩)

end Minimality

#print axioms Minimality.IsRobustUnimodal.refine
