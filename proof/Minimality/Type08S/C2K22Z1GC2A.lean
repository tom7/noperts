module

public import Minimality.Type08S.C2K22ZA
public import Minimality.Type08S.C2K19G
public import Minimality.Type08S.C2K18A

@[expose] public section


set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- Cycle `a, d, b, a', b', c'` in the frame `(b-d, c-d, a-c')`, `w = 1/(α1-1)`, `β6 = 1+k`, `γ4 = 1`. -/
def k22z1gc2Y (w k : ℝ) : ZMod 6 → ℝ × ℝ × ℝ :=
  ![(-w, 0, -w), (0, 0, 0), (1, 0, 0), (1 + k, 1, 0), (-(1 + k) * w, 1, -(1 + k) * w), (-w, 0, -w - 1)]

theorem k22z1gc2Y_0 : k22z1gc2Y w k 0 = (-w, 0, -w) := rfl
theorem k22z1gc2Y_1 : k22z1gc2Y w k 1 = (0, 0, 0) := rfl
theorem k22z1gc2Y_2 : k22z1gc2Y w k 2 = (1, 0, 0) := rfl
theorem k22z1gc2Y_3 : k22z1gc2Y w k 3 = (1 + k, 1, 0) := rfl
theorem k22z1gc2Y_4 : k22z1gc2Y w k 4 = (-(1 + k) * w, 1, -(1 + k) * w) := rfl
theorem k22z1gc2Y_5 : k22z1gc2Y w k 5 = (-w, 0, -w - 1) := rfl

theorem k22z1gc2Y_inj {w k : ℝ} (hw : 0 < w) (hk : 0 < k) :
    ∀ i j, k22z1gc2Y w k i = k22z1gc2Y w k j → i = j := by
  intro i j h
  have h1 := mul_pos hw hk
  rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases z6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [k22z1gc2Y_0, k22z1gc2Y_1, k22z1gc2Y_2, k22z1gc2Y_3, k22z1gc2Y_4, k22z1gc2Y_5, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith)

theorem k22z1gc2_tsc_of {D : ℝ} {e f v : ℝ × ℝ × ℝ} (hD : 0 < D)
    (h : 0 < d3 e.1 e.2.1 e.2.2 f.1 f.2.1 f.2.2 0 0 1 ∨
      (d3 e.1 e.2.1 e.2.2 f.1 f.2.1 f.2.2 0 0 1 = 0 ∧ 0 < d3 e.1 e.2.1 e.2.2 f.1 f.2.1 f.2.2 v.1 v.2.1 v.2.2)) :
    TSc D e f v := by
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl (mul_pos hD h)
  · exact Or.inr ⟨by rw [h1]; simp, mul_pos hD h2⟩

set_option maxHeartbeats 12800000 in
theorem k22z1gc2_tsc {D w k v1 v2 : ℝ} (hD : 0 < D) (hw : 0 < w) (hk : 0 < k)
    (hv2 : 0 < v2) (hs : v1 + w * k * v2 < 0) :
    (∀ i j : ZMod 6, j ≠ i → j ≠ i + 1 →
      TSc D (k22z1gc2Y w k (i + 1) - k22z1gc2Y w k i) (k22z1gc2Y w k j - k22z1gc2Y w k i) (v1, v2, 0)) ∧
    (∀ i : ZMod 6,
      TSc D (k22z1gc2Y w k (i + 1) - k22z1gc2Y w k i) ((0, 1, 0) - k22z1gc2Y w k i) (v1, v2, 0)) := by
  obtain ⟨s, hs0, hsd⟩ : ∃ s, 0 < s ∧ s = -(v1 + w * k * v2) := ⟨_, by linarith, rfl⟩
  have e1 := k19_z6
  have z6a : (0 : ZMod 6) + 1 = 1 ∧ (1 : ZMod 6) + 1 = 2 ∧ (2 : ZMod 6) + 1 = 3 ∧
    (3 : ZMod 6) + 1 = 4 ∧ (4 : ZMod 6) + 1 = 5 ∧ (5 : ZMod 6) + 1 = 0 := z6_add_one
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := z6a
  have pwk := mul_pos hw hk
  have pwv := mul_pos hw hv2
  have pkv := mul_pos hk hv2
  have pwkv := mul_pos pwk hv2
  have pws := mul_pos hw hs0
  have pks := mul_pos hk hs0
  have pwks := mul_pos pwk hs0
  have pww := mul_pos hw hw
  have pwwk := mul_pos pww hk
  have pwwv := mul_pos pww hv2
  have pwkk := mul_pos pwk hk
  have pwkkv := mul_pos pwkk hv2
  have pwwkv := mul_pos pwwk hv2
  have pwwks := mul_pos pwwk hs0
  have pkkv := mul_pos (mul_pos hk hk) hv2
  have pwkks := mul_pos pwkk hs0
  have pkks := mul_pos (mul_pos hk hk) hs0
  have pwws := mul_pos pww hs0
  refine ⟨?_, ?_⟩
  · intro i j h1 h2'
    rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases z6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2' (by decide)).elim
      | (apply k22z1gc2_tsc_of hD
         simp only [d3, a0, a1, a2, a3, a4, a5, k22z1gc2Y_0, k22z1gc2Y_1, k22z1gc2Y_2,
          k22z1gc2Y_3, k22z1gc2Y_4, k22z1gc2Y_5, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first
         | (left; nlinarith)
         | (right; refine ⟨by ring, by nlinarith⟩))
  · intro i
    rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      (apply k22z1gc2_tsc_of hD
       simp only [d3, a0, a1, a2, a3, a4, a5, k22z1gc2Y_0, k22z1gc2Y_1, k22z1gc2Y_2,
          k22z1gc2Y_3, k22z1gc2Y_4, k22z1gc2Y_5, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
