module

public import Minimality.Type08S.P2CR4

@[expose] public section

set_option relaxedAutoImplicit true

set_option autoImplicit true

namespace Minimality
namespace Type08Sp

/-- `(a, b, c)` is a cyclically increasing triple of `ZMod 4`. -/
def inc (a b c : ZMod 4) : Prop := 0 < (b - a).val ∧ (b - a).val < (c - a).val

instance (a b c : ZMod 4) : Decidable (inc a b c) := by unfold inc; infer_instance

theorem comb3 : ∀ τ : ZMod 3 → ZMod 4, (∀ i j : ZMod 3, j ≠ i → j ≠ i + 1 → inc (τ i) (τ (i + 1)) (τ j)) →
    (∀ (i : ZMod 3) (m : ZMod 4), ¬ inc (τ i) m (τ (i + 1))) → False := by
  decide

theorem comb3' : ∀ τ : ZMod 3 → ZMod 4, (∀ i j : ZMod 3, j ≠ i → j ≠ i + 1 → inc (τ i) (τ j) (τ (i + 1))) →
    (∀ (i : ZMod 3) (m : ZMod 4), ¬ inc (τ i) (τ (i + 1)) m) → False := by
  decide

theorem comb4 : ∀ τ : ZMod 4 → ZMod 4, (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 → inc (τ i) (τ (i + 1)) (τ j)) →
    (∀ (i : ZMod 4) (m : ZMod 4), ¬ inc (τ i) m (τ (i + 1))) → ∃ c : ZMod 4, ∀ i, τ i = c + i := by
  decide +kernel

theorem comb4' : ∀ τ : ZMod 4 → ZMod 4, (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 → inc (τ i) (τ j) (τ (i + 1))) →
    (∀ (i : ZMod 4) (m : ZMod 4), ¬ inc (τ i) (τ (i + 1)) m) → ∃ c : ZMod 4, ∀ i, τ i = c - i := by
  decide +kernel

end Type08Sp
end Minimality

#print axioms Minimality.Type08Sp.comb4
#print axioms Minimality.Type08Sp.comb3
