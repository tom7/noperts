module

public import Minimality.Type21SilF

@[expose] public section

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace H21

/-- Lexicographic positivity of a pair. -/
def h21b_LP (a b : ℝ) : Prop := 0 < a ∨ (a = 0 ∧ 0 < b)

/-- Silhouette data with lex facings at `(u₀, v)`: edge `i` has the up facet `fA i` and the down facet
`fB i`; either may be edge-on at `u₀`, in which case the tilt `v` decides. -/
structure h21b_SilDataL {n : ℕ} (k : ℕ) (x : Fin n → ℝ³) (c : ZMod k → Fin n) (u₀ v : ℝ³) where
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
  up : ∀ i, h21b_LP ⟪A i, u₀⟫ ⟪A i, v⟫
  dn : ∀ i, h21b_LP (-⟪B i, u₀⟫) (-⟪B i, v⟫)

def h21b_SilDataL.rev {n k : ℕ} {x : Fin n → ℝ³} {c : ZMod k → Fin n} {u₀ v : ℝ³}
    (D : h21b_SilDataL k x c u₀ v) : h21b_SilDataL k x (fun i => c (-i)) u₀ v where
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

variable {n k : ℕ} [NeZero k] {x : Fin n → ℝ³} {c : ZMod k → Fin n} {u₀ v : ℝ³}

/-- Scalar core of `h21b_Q_pos`. -/
theorem h21b_Q_scalar {fa fb a0 a1 b0 b1 : ℝ} (a : fa ≤ 0) (b : fb ≤ 0) (hs : fa < 0 ∨ fb < 0)
    (hu : h21b_LP a0 a1) (hd : h21b_LP (-b0) (-b1)) :
    h21b_LP (fa * b0 - fb * a0) (fa * b1 - fb * a1) := by
  unfold h21b_LP at *
  have ha0 : 0 ≤ a0 := by rcases hu with h | ⟨h, _⟩ <;> linarith
  have hb0 : b0 ≤ 0 := by rcases hd with h | ⟨h, _⟩ <;> linarith
  have t1 : 0 ≤ fa * b0 := mul_nonneg_of_nonpos_of_nonpos a hb0
  have t2 : 0 ≤ -(fb * a0) := by nlinarith [mul_nonpos_of_nonpos_of_nonneg b ha0]
  rcases (show 0 ≤ fa * b0 - fb * a0 by linarith).lt_or_eq with h | h
  · exact Or.inl h
  right
  refine ⟨h.symm, ?_⟩
  have e1 : fa * b0 = 0 := by linarith
  have e2 : fb * a0 = 0 := by linarith
  rcases hs with hs | hs
  · have hb : b0 = 0 := by
      rcases mul_eq_zero.1 e1 with h | h
      · exact absurd h hs.ne
      · exact h
    have hb1 : b1 < 0 := by
      rcases hd with h | ⟨_, h⟩
      · linarith
      · linarith
    have : 0 < fa * b1 := mul_pos_of_neg_of_neg hs hb1
    rcases hu with h | ⟨h0, h1⟩
    · have : fb = 0 := by
        rcases mul_eq_zero.1 e2 with h' | h'
        · exact h'
        · exact absurd h' h.ne'
      rw [this]; linarith
    · nlinarith [mul_nonpos_of_nonpos_of_nonneg b h1.le]
  · have ha : a0 = 0 := by
      rcases mul_eq_zero.1 e2 with h | h
      · exact absurd h hs.ne
      · exact h
    have ha1 : 0 < a1 := by
      rcases hu with h | ⟨_, h⟩
      · linarith
      · exact h
    have t3 : 0 < -(fb * a1) := by nlinarith [mul_neg_of_neg_of_pos hs ha1]
    have t4 : 0 ≤ fa * b1 := by
      rcases hd with h | ⟨h0, h1⟩
      · have : fa = 0 := by
          rcases mul_eq_zero.1 e1 with h' | h'
          · exact h'
          · linarith
        rw [this]; simp
      · exact mul_nonneg_of_nonpos_of_nonpos a (by linarith)
    linarith

/-- The bracket pair at an off-edge point is lex positive. -/
theorem h21b_Q_pos (D : h21b_SilDataL k x c u₀ v) (i : ZMod k) (m : Fin n) (h0 : m ≠ c i)
    (h1 : m ≠ c (i + 1)) :
    h21b_LP (D.fA i (x m) * ⟪D.B i, u₀⟫ - D.fB i (x m) * ⟪D.A i, u₀⟫)
      (D.fA i (x m) * ⟪D.B i, v⟫ - D.fB i (x m) * ⟪D.A i, v⟫) :=
  h21b_Q_scalar (D.nA i m) (D.nB i m) (D.strict i m h0 h1) (D.up i) (D.dn i)

end H21
end Minimality
