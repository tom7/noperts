module

public import Minimality.Type08S.C2K5AC

@[expose] public section


/-!
# K5a / E: helper lemmas for the generic cell (rest point `c`, peak lemma with a single peak `a'`).
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

set_option maxHeartbeats 1600000 in
/-- Tilt tests of the rest point `c = (0, 1, 0)` against `kCyc` (no `γ6 ≤ 1` needed). -/
theorem k5a_rest0 {D α4 β6 γ6 v1 v2 v3 : ℝ} (hD : 0 < D) (hα4 : 0 < α4) (hβ6 : 0 < β6)
    (hγ6 : 0 < γ6) (hs : 1 < β6 + γ6) (hv1 : 0 < v1) (hv2 : v2 < 0)
    (hcone : (1 - γ6) * v1 + β6 * v2 < 0) :
    ∀ i : ZMod 5, TSc D (kCyc β6 γ6 α4 (i + 1) - kCyc β6 γ6 α4 i) ((0, 1, 0) - kCyc β6 γ6 α4 i)
      (v1, v2, v3) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have k1 := hD
  have kb6 := mul_pos hD hβ6
  have kg6 := mul_pos hD hγ6
  have ks := mul_pos hD (sub_pos.2 hs)
  have kv1 := mul_pos hD hv1
  have kv2 := mul_pos hD (neg_pos.2 hv2)
  have kgv := mul_pos (mul_pos hD hγ6) hv1
  have kbv := mul_pos (mul_pos hD hβ6) (neg_pos.2 hv2)
  have ka4v1 := mul_pos (mul_pos hD hα4) hv1
  have kcone := mul_pos (mul_pos hD hα4) (neg_pos.2 hcone)
  intro i
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [TSc, d3, kCyc, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
     first
     | (left; nlinarith)
     | (right; refine ⟨by ring, by nlinarith⟩))

/-- 5-cycle with exactly one peak, at `3`. -/
theorem k5a_lexUni5_three (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h10 : LexLt (z 1, w 1) (z 0, w 0)) (h04 : LexLt (z 0, w 0) (z 4, w 4))
    (h23 : LexLt (z 2, w 2) (z 3, w 3)) (h43 : LexLt (z 4, w 4) (z 3, w 3)) : LexUni z w := by
  classical
  refine ⟨hinj, ?_⟩
  rw [Finset.card_filter]
  have hs : ∀ g : ZMod 5 → ℕ, ∑ i, g i = g 0 + g 1 + g 2 + g 3 + g 4 := fun g => Fin.sum_univ_five (f := g)
  rw [hs]
  have e0 : (0 : ZMod 5) - 1 = 4 := by decide
  have e1 : (1 : ZMod 5) - 1 = 0 := by decide
  have e2 : (2 : ZMod 5) - 1 = 1 := by decide
  have e3 : (3 : ZMod 5) - 1 = 2 := by decide
  have e4 : (4 : ZMod 5) - 1 = 3 := by decide
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  show (if LexLt (z (0 - 1), w (0 - 1)) (z 0, w 0) ∧ LexLt (z (0 + 1), w (0 + 1)) (z 0, w 0) then 1 else 0) +
    (if LexLt (z (1 - 1), w (1 - 1)) (z 1, w 1) ∧ LexLt (z (1 + 1), w (1 + 1)) (z 1, w 1) then 1 else 0) +
    (if LexLt (z (2 - 1), w (2 - 1)) (z 2, w 2) ∧ LexLt (z (2 + 1), w (2 + 1)) (z 2, w 2) then 1 else 0) +
    (if LexLt (z (3 - 1), w (3 - 1)) (z 3, w 3) ∧ LexLt (z (3 + 1), w (3 + 1)) (z 3, w 3) then 1 else 0) +
    (if LexLt (z (4 - 1), w (4 - 1)) (z 4, w 4) ∧ LexLt (z (4 + 1), w (4 + 1)) (z 4, w 4) then 1 else 0) = 1
  rw [e0, e1, e2, e3, e4, f0, f1, f2, f3, f4]
  have a10 := lexLt_asymm h10
  have a04 := lexLt_asymm h04
  have a23 := lexLt_asymm h23
  have a43 := lexLt_asymm h43
  simp [h10, a10, h04, a04, h23, a23, h43, a43]

end C2
end Type08Sp
end Minimality
