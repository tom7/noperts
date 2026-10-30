module

public import Minimality.Type08S.P2H1

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# pkH H3: P-G, classification of a persistent HDN of a robust 4-corner closing (29.5 + sp08d Lemma 2.1)

Frame numbers as in `PersF` (`x̄ = (0, zx)`, `f̄ = (L, zf)` in F's `(X, z)`-plane; `r`, `g` at heights `Yr`, `Yg`).
`classify_pers`: a persistent HDN of a robust closing is one of
* class (c) (`ClassC5`, with Lemma 2.1 (c)'s robust order facts);
* class (d) (`DCross`: the top side meets the open chord, the meeting point allowed at `r̄` or `ḡ`), not collinear;
* chord end at `x` (`XEnd`, the five sub-cases of `ClassX5` with their robust order facts, without `x ∉ Π'`);
* chord end at `f` (`CEf5`);
* the parallel set (`Par5`: top side with `r̄`, `ḡ` on the chord's line).
-/

set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- `r̄`, `ḡ` on the chord line through `x̄`, `f̄`. -/
def Coll5 (L zx zf Xr zr Xg zg : ℝ) : Prop :=
  (zr - zx) * L = (zf - zx) * Xr ∧ (zg - zx) * L = (zf - zx) * Xg

/-- Class (d): top side `Yr = Yg` crossing the open chord at `s L` (`0 < s < 1`), at the point `r̄ + s' (ḡ - r̄)`. -/
def DCross (L zx zf Xr Yr zr Xg Yg zg : ℝ) : Prop :=
  Yr = Yg ∧ ∃ s s' : ℝ, 0 < s ∧ s < 1 ∧ 0 ≤ s' ∧ s' ≤ 1 ∧ s * L = Xr + s' * (Xg - Xr) ∧
    zx + s * (zf - zx) = zr + s' * (zg - zr)

/-- Chord end at `x` (the clauses of pkD's `ClassX5` without the `x ∉ Π'` sign). -/
def XEnd (L zx zf Xr Yr zr Xg Yg zg : ℝ) : Prop :=
  (Yg = Yr ∧ Xg < 0 ∧ 0 < Xr ∧ (zg - zx) * Xr = (zr - zx) * Xg ∧ 0 < (zf - zx) * (zr - zx)) ∨
  (Yr < Yg ∧ Xg = 0 ∧ zg = zx ∧ 0 < (zf - zx) * (zr - zx)) ∨
  (Yg < Yr ∧ Xr = 0 ∧ zr = zx ∧ (zf - zx) * (zg - zx) < 0) ∨
  (Yg = Yr ∧ Xg = 0 ∧ zg = zx ∧ 0 < (zf - zx) * (zr - zx)) ∨
  (Yg = Yr ∧ Xr = 0 ∧ zr = zx ∧ (zf - zx) * (zg - zx) < 0)

/-- Chord end at `f`: the top (vertex or side) projects onto `f̄` (29.5 (b), (c) at `f`). -/
def CEf5 (L zx zf Xr Yr zr Xg Yg zg : ℝ) : Prop :=
  ∃ s' : ℝ, 0 ≤ s' ∧ s' ≤ 1 ∧ (Yr = Yg ∨ (s' = 0 ∧ Yg < Yr) ∨ (s' = 1 ∧ Yr < Yg)) ∧
    L = Xr + s' * (Xg - Xr) ∧ zf = zr + s' * (zg - zr)

/-- The parallel set: a top side whose projection lies on the chord's line, with the persistent HDN. -/
def Par5 (L zx zf Xr Yr zr Xg Yg zg : ℝ) : Prop :=
  Yr = Yg ∧ Coll5 L zx zf Xr zr Xg zg ∧ PersF L zx zf Xr Yr zr Xg Yg zg

/-- **P-G (classification).** -/
theorem classify_pers {L zx zf Xr Yr zr Xg Yg zg : ℝ} (hL : 0 < L) (hYr : 0 < Yr) (hYg : 0 < Yg)
    (hcg : 0 < Yg * Xr - Xg * Yr) (hrob : Rob4 zx zf zr zg) (hp : PersF L zx zf Xr Yr zr Xg Yg zg) :
    ClassC5 L zx zf Xr Yr zr Xg Yg zg ∨
    (DCross L zx zf Xr Yr zr Xg Yg zg ∧ ¬ Coll5 L zx zf Xr zr Xg zg) ∨
    (XEnd L zx zf Xr Yr zr Xg Yg zg ∧ (Yr = Yg → ¬ Coll5 L zx zf Xr zr Xg zg)) ∨
    CEf5 L zx zf Xr Yr zr Xg Yg zg ∨
    Par5 L zx zf Xr Yr zr Xg Yg zg := by
  by_cases hpar : Yr = Yg ∧ Coll5 L zx zf Xr zr Xg zg
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hpar.1, hpar.2, hp⟩)))
  have hnc : Yr = Yg → ¬ Coll5 L zx zf Xr zr Xg zg := fun h hc => hpar ⟨h, hc⟩
  obtain ⟨s, s', hs0, hs1, ht0, ht1, htop, hX, hz⟩ := hp
  rcases eq_or_lt_of_le hs1 with hs | hs
  · -- chord end at f
    subst hs
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨s', ht0, ht1, htop, by linarith, by linarith⟩)))
  rcases eq_or_lt_of_le hs0 with hs' | hs'
  · -- chord end at x
    subst hs'
    refine Or.inr (Or.inr (Or.inl ⟨?_, hnc⟩))
    rcases htop with hY | ⟨rfl, hY⟩ | ⟨rfl, hY⟩
    · -- top side
      have hXrg : Xg < Xr := by rw [hY] at hcg; nlinarith
      rcases eq_or_lt_of_le ht0 with h0 | h0
      · subst h0
        have e1 : Xr = 0 := by linarith
        have e2 : zr = zx := by linarith
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hY.symm, e1, e2, rob4_xr hrob e2⟩)))
      rcases eq_or_lt_of_le ht1 with h1 | h1
      · subst h1
        have e1 : Xg = 0 := by linarith
        have e2 : zg = zx := by linarith
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hY.symm, e1, e2, rob4_xg hrob e2⟩)))
      · left
        refine ⟨hY.symm, by nlinarith, by nlinarith, ?_, rob4_xside hrob h0 h1 (by linarith)⟩
        have e1 : Xr = s' * (Xr - Xg) := by linarith
        have e2 : zx = zr + s' * (zg - zr) := by linarith
        have e3 : Xg = -(1 - s') * (Xr - Xg) := by linarith
        linear_combination (zg - zr) * e1 - (Xr - Xg) * e2
    · -- top vertex r
      have e1 : Xr = 0 := by linarith
      have e2 : zr = zx := by linarith
      exact Or.inr (Or.inr (Or.inl ⟨hY, e1, e2, rob4_xr hrob e2⟩))
    · -- top vertex g
      have e1 : Xg = 0 := by linarith
      have e2 : zg = zx := by linarith
      exact Or.inr (Or.inl ⟨hY, e1, e2, rob4_xg hrob e2⟩)
  -- 0 < s < 1
  rcases htop with hY | ⟨rfl, hY⟩ | ⟨rfl, hY⟩
  · exact Or.inr (Or.inl ⟨⟨hY, s, s', hs', hs, ht0, ht1, hX, hz⟩, hnc hY⟩)
  · -- top vertex r on the open chord
    left; right
    have e1 : Xr = s * L := by linarith
    have e2 : zr = zx + s * (zf - zx) := by linarith
    obtain ⟨k1, k2⟩ := rob4_cr hrob hs' hs e2.symm
    refine ⟨hY, by rw [e1]; positivity, by rw [e1]; nlinarith, by rw [e1, e2]; ring, k1, k2⟩
  · left; left
    have e1 : Xg = s * L := by linarith
    have e2 : zg = zx + s * (zf - zx) := by linarith
    obtain ⟨k1, k2⟩ := rob4_cg hrob hs' hs e2.symm
    refine ⟨hY, by rw [e1]; positivity, by rw [e1]; nlinarith, by rw [e1, e2]; ring, k1, k2⟩

end Type08Sp
end Minimality
