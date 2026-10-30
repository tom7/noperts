module

public import Minimality.Type08S.P2TT1

@[expose] public section

set_option relaxedAutoImplicit true
set_option autoImplicit true
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

theorem close_touchT {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) (hT : IsT a' b c d)
    (h : TouchT b b' c c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) ∨ S4T' a a' b b' c c' d := by
  classical
  rcases (h.2.2).eq_or_lt with heq | hlt
  · exact Or.inr ⟨hT, Or.inl ⟨h, heq⟩⟩
  have hrob := touchT_Xba_robust N hT h hlt
  by_cases hang : AngBig a b b' c d
  · exact Or.inl (cellXba_rupert N hT hang hrob)
  by_cases hno : NoHDNAt ({b, c', b', a'} : Finset ℝ³) (b - d)
  · exact Or.inl (poly_rupert_off N hT (x0 := b) (x0' := d) (y0 := a') (y0' := c) (Or.inl ⟨rfl, rfl⟩)
      (Or.inr ⟨rfl, rfl⟩) hrob hno)
  · exact Or.inr ⟨hT, Or.inr (Or.inl ⟨h, hang, hno⟩)⟩


end Type08Sp
end Minimality
