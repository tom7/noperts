module

public import Minimality.Type21Sl2D

@[expose] public section

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace H21
variable {x : Fin 7 → ℝ³}

/-! ### Segment views -/

/-- A segment-view leaf at `r = x j - x i`: the two edge-on facets `X`, `Y` (through both), the facing
pattern `pat` (true = up; forced for facets through exactly one of `i`, `j`, a literal for the
facets through neither, tilt-chosen for `X`, `Y`) and the silhouette cycle `c`. -/
structure h21b_SegSpec (k : ℕ) where
  i : Fin 7
  j : Fin 7
  X : Fin 8
  Y : Fin 8
  pat : Fin 8 → Bool
  c : ZMod k → Fin 7

/-- The decidable side conditions of a segment leaf. -/
def h21b_SegSpec.Good {k : ℕ} [NeZero k] (s : h21b_SegSpec k) : Prop :=
  s.i ≠ s.j ∧ s.X ≠ s.Y ∧ s.i ∈ h21S s.X ∧ s.j ∈ h21S s.X ∧ s.i ∈ h21S s.Y ∧ s.j ∈ h21S s.Y ∧
  (∀ t, s.i ∈ h21S t → s.j ∈ h21S t → t = s.X ∨ t = s.Y) ∧
  (∀ t, s.j ∈ h21S t → s.i ∉ h21S t → s.pat t = true) ∧
  (∀ t, s.i ∈ h21S t → s.j ∉ h21S t → s.pat t = false) ∧
  (∃ m, m ∈ h21S s.X ∧ m ∉ h21S s.Y) ∧ (∃ m, m ∈ h21S s.Y ∧ m ∉ h21S s.X) ∧
  Function.Injective s.c ∧ 3 ≤ k ∧ h21b_CycOK s.c s.pat

instance {k : ℕ} [NeZero k] (s : h21b_SegSpec k) : Decidable s.Good := by
  unfold h21b_SegSpec.Good; infer_instance

/-! ### Line views -/

/-- A line-view leaf: the view `u = N_X × N_Y`, the facing pattern of the other six facets (true =
up, the sign of `⟪N_t, u⟫`), the tilt-chosen facings of `X`, `Y`, and the silhouette cycle. -/
structure h21b_LinSpec (k : ℕ) where
  X : Fin 8
  Y : Fin 8
  pat : Fin 8 → Bool
  c : ZMod k → Fin 7

def h21b_LinSpec.Good {k : ℕ} [NeZero k] (s : h21b_LinSpec k) : Prop :=
  s.X ≠ s.Y ∧ Function.Injective s.c ∧ 3 ≤ k ∧ h21b_CycOK s.c s.pat

instance {k : ℕ} [NeZero k] (s : h21b_LinSpec k) : Decidable s.Good := by
  unfold h21b_LinSpec.Good; infer_instance

theorem h21b_dual {n1 n2 : ℝ³} (h : cross n1 n2 ≠ 0) :
    ∃ v1 v2 : ℝ³, ⟪n1, v1⟫ < 0 ∧ ⟪n2, v1⟫ = 0 ∧ ⟪n1, v2⟫ = 0 ∧ ⟪n2, v2⟫ < 0 := by
  have hn : 0 < ⟪cross n1 n2, cross n1 n2⟫ := real_inner_self_pos.2 h
  refine ⟨-cross n2 (cross n1 n2), -cross (cross n1 n2) n1, ?_, ?_, ?_, ?_⟩
  · simp only [inner3, cross_apply_zero, cross_apply_one, cross_apply_two, PiLp.neg_apply] at hn ⊢
    nlinarith
  · simp only [inner3, cross_apply_zero, cross_apply_one, cross_apply_two, PiLp.neg_apply]; ring
  · simp only [inner3, cross_apply_zero, cross_apply_one, cross_apply_two, PiLp.neg_apply]; ring
  · simp only [inner3, cross_apply_zero, cross_apply_one, cross_apply_two, PiLp.neg_apply] at hn ⊢
    nlinarith

end H21
end Minimality
