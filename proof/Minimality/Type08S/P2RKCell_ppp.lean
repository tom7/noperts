module

public import Minimality.Type08S.P2RKCore

@[expose] public section

set_option relaxedAutoImplicit true
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unreachableTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace K

set_option maxHeartbeats 3200000 in
theorem cell_ppp {r W T1 t2 w3 C0 ν ha α1 α4 γ4 β1 β6 : ℝ}
    (hr : 0 < r) (hν : 0 < ν) (hha : 0 < ha) (hα1 : 1 < α1) (hα4 : 0 < α4) (hγ4 : 0 < γ4)
    (hβ1 : 0 < β1) (hβ6 : 0 < β6) (hE : 0 < α4 - α4 * β1 - α1 * (1 - γ4))
    (hp1 : 0 < -(W * t2 - ha * T1)) (hp3 : 0 < -(r * (γ4 - 1) * t2 - α4 * (W * t2 - ha * T1)))
    (hp4 : 0 < -(r * t2)) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 → LT 1 T1 t2 ((cyc5 (kd r) (ka r W ha w3) (kc' r W ha w3 ν α1 β1) (kb' r W ha w3 C0 α4 γ4) (kc C0)) i) ((cyc5 (kd r) (ka r W ha w3) (kc' r W ha w3 ν α1 β1) (kb' r W ha w3 C0 α4 γ4) (kc C0)) (i + 1)) ((cyc5 (kd r) (ka r W ha w3) (kc' r W ha w3 ν α1 β1) (kb' r W ha w3 C0 α4 γ4) (kc C0)) j)) ∧
    (∀ i : ZMod 5, LT 1 T1 t2 ((cyc5 (kd r) (ka r W ha w3) (kc' r W ha w3 ν α1 β1) (kb' r W ha w3 C0 α4 γ4) (kc C0)) i) ((cyc5 (kd r) (ka r W ha w3) (kc' r W ha w3 ν α1 β1) (kb' r W ha w3 C0 α4 γ4) (kc C0)) (i + 1)) (ka' ν β6 C0)) ∧
    (∀ i : ZMod 5, LT 1 T1 t2 ((cyc5 (kd r) (ka r W ha w3) (kc' r W ha w3 ν α1 β1) (kb' r W ha w3 C0 α4 γ4) (kc C0)) i) ((cyc5 (kd r) (ka r W ha w3) (kc' r W ha w3 ν α1 β1) (kb' r W ha w3 C0 α4 γ4) (kc C0)) (i + 1)) (kb r ν)) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5s
  have hα1pos : (0:ℝ) < α1 := by linarith
  kfacts
  refine ⟨?_, ?_, ?_⟩
  · intro i j h1 h2'
    rcases z5c i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5c j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2' (by decide)).elim
      | (simp only [LT, ori, fo, kd, kb, kc, ka, ka', kb', kc', s0, s1, s2, s3, s4, c5_0, c5_1, c5_2, c5_3, c5_4]
         first
         | (left; linarith)
         | (right; refine ⟨by ring, by linarith⟩))
  · intro i
    rcases z5c i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [LT, ori, fo, kd, kb, kc, ka, ka', kb', kc', s0, s1, s2, s3, s4, c5_0, c5_1, c5_2, c5_3, c5_4]
       first
       | (left; linarith)
       | (right; refine ⟨by ring, by linarith⟩))
  · intro i
    rcases z5c i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [LT, ori, fo, kd, kb, kc, ka, ka', kb', kc', s0, s1, s2, s3, s4, c5_0, c5_1, c5_2, c5_3, c5_4]
       first
       | (left; linarith)
       | (right; refine ⟨by ring, by linarith⟩))

end K
end Type08Sp
end Minimality
