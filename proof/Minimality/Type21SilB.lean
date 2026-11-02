module

public import Minimality.Type21SilA

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace H21

open Classical in
/-- Strict cyclic unimodality: consecutive values differ and exactly one strict local maximum. -/
noncomputable def Uni {k : ℕ} [NeZero k] (z : ZMod k → ℝ) : Prop :=
  (∀ i, z i ≠ z (i + 1)) ∧
    (Finset.univ.filter (fun i : ZMod k => z (i - 1) < z i ∧ z (i + 1) < z i)).card = 1

theorem lexUni_of_uni {k : ℕ} [NeZero k] {z : ZMod k → ℝ} (hz : Uni z) (w : ZMod k → ℝ)
    (hinj : ∀ i j, z i = z j → w i = w j → i = j) : LexUni z w := by
  classical
  refine ⟨hinj, ?_⟩
  rw [← hz.2]
  congr 1
  apply Finset.filter_congr
  intro i _
  have h1 : z (i - 1) ≠ z i := by
    have := hz.1 (i - 1); rwa [sub_add_cancel] at this
  have h2 : z i ≠ z (i + 1) := hz.1 i
  have e1 : LexLt (z (i - 1), w (i - 1)) (z i, w i) ↔ z (i - 1) < z i := by
    unfold LexLt
    constructor
    · rintro (h | ⟨h, _⟩); exact h; exact absurd h h1
    · exact Or.inl
  have e2 : LexLt (z (i + 1), w (i + 1)) (z i, w i) ↔ z (i + 1) < z i := by
    unfold LexLt
    constructor
    · rintro (h | ⟨h, _⟩); exact h; exact absurd h.symm h2
    · exact Or.inl
  rw [e1, e2]

/-- The facet data along a cycle `c` (indices into the points `x`) at the view `u₀`:
edge `i` is `c i → c (i+1)`, lying in the facets `fA i` (faces up) and `fB i` (faces down). -/
structure SilData {n : ℕ} (k : ℕ) (x : Fin n → ℝ³) (c : ZMod k → Fin n) (u₀ : ℝ³) where
  A : ZMod k → ℝ³
  B : ZMod k → ℝ³
  fA : ZMod k → ℝ³ → ℝ
  fB : ZMod k → ℝ³ → ℝ
  hA : ∀ i y z, fA i y - fA i z = ⟪A i, y - z⟫
  hB : ∀ i y z, fB i y - fB i z = ⟪B i, y - z⟫
  zA0 : ∀ i, fA i (x (c i)) = 0
  zA1 : ∀ i, fA i (x (c (i + 1))) = 0
  zB0 : ∀ i, fB i (x (c i)) = 0
  zB1 : ∀ i, fB i (x (c (i + 1))) = 0
  nA : ∀ i m, fA i (x m) ≤ 0
  nB : ∀ i m, fB i (x m) ≤ 0
  strict : ∀ i m, m ≠ c i → m ≠ c (i + 1) → fA i (x m) < 0 ∨ fB i (x m) < 0
  up : ∀ i, 0 < ⟪A i, u₀⟫
  dn : ∀ i, ⟪B i, u₀⟫ < 0

/-- The reversed cycle `i ↦ c (-i)`. -/
def SilData.rev {n k : ℕ} {x : Fin n → ℝ³} {c : ZMod k → Fin n} {u₀ : ℝ³} (D : SilData k x c u₀) :
    SilData k x (fun i => c (-i)) u₀ where
  A i := D.A (-i - 1)
  B i := D.B (-i - 1)
  fA i := D.fA (-i - 1)
  fB i := D.fB (-i - 1)
  hA i := D.hA (-i - 1)
  hB i := D.hB (-i - 1)
  zA0 i := by
    have := D.zA1 (-i - 1); rwa [sub_add_cancel] at this
  zA1 i := by
    have := D.zA0 (-i - 1); rwa [show -(i + 1) = -i - 1 by ring]
  zB0 i := by
    have := D.zB1 (-i - 1); rwa [sub_add_cancel] at this
  zB1 i := by
    have := D.zB0 (-i - 1); rwa [show -(i + 1) = -i - 1 by ring]
  nA i := D.nA (-i - 1)
  nB i := D.nB (-i - 1)
  strict i m h0 h1 := by
    apply D.strict (-i - 1) m
    · rw [show -i - 1 = -(i + 1) by ring]; exact h1
    · rw [sub_add_cancel]; exact h0
  up i := D.up _
  dn i := D.dn _

end H21
end Minimality
