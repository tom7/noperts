module

public import Minimality.Type08S.P2RKBridge

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkR / K, lex part helper: `LexUni` is invariant under reversing the cycle (`i ↦ -i`), so the caller may prove it
for the unreversed cycle and transfer it to `orient σ x`.
-/
set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace K

theorem LexUni.of_neg {k : ℕ} [NeZero k] {z w : ZMod k → ℝ} (h : LexUni (fun i => z (-i)) (fun i => w (-i))) :
    LexUni z w := by
  classical
  obtain ⟨hinj, hcard⟩ := h
  refine ⟨fun i j h1 h2 => ?_, ?_⟩
  · have := hinj (-i) (-j) (by simpa using h1) (by simpa using h2)
    simpa using this
  · rw [← hcard]
    refine Finset.card_bij (fun i _ => -i) ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      refine ⟨?_, ?_⟩
      · have e : -(-i - 1) = i + 1 := by ring
        rw [e, neg_neg]; exact hi.2
      · have e : -(-i + 1) = i - 1 := by ring
        rw [e, neg_neg]; exact hi.1
    · intro i _ j _ hij; simpa using hij
    · intro j hj
      refine ⟨-j, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      refine ⟨?_, ?_⟩
      · have e : -j - 1 = -(j + 1) := by ring
        rw [e]; exact hj.2
      · have e : -j + 1 = -(j - 1) := by ring
        rw [e]; exact hj.1

theorem orient_one {α : Type*} {k : ℕ} (f : ZMod k → α) : orient (1 : ℝ) f = f := by
  funext i; unfold orient; simp

theorem orient_neg {α : Type*} {k : ℕ} (f : ZMod k → α) : orient (-1 : ℝ) f = fun i => f (-i) := by
  funext i; unfold orient
  have hne : (-1 : ℝ) ≠ 1 := by norm_num
  simp [hne]

theorem LexUni.orient {k : ℕ} [NeZero k] {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {z w : ZMod k → ℝ}
    (h : LexUni z w) : LexUni (K.orient σ z) (K.orient σ w) := by
  rcases hσ with rfl | rfl
  · rw [orient_one, orient_one]; exact h
  · rw [orient_neg, orient_neg]
    apply LexUni.of_neg
    simpa using h

end K
end Type08Sp
end Minimality
