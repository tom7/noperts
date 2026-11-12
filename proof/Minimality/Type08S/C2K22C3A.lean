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

/-- Pentagon `a' (0,1,γ6), c (0,0,1), d (0,0,0), a (1,0,0), c' (1,β1,0)` in the frame `(a-d, b-d, c-d)`. -/
def k22c3Y (β1 γ6 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  ![(0, 1, γ6), (0, 0, 1), (0, 0, 0), (1, 0, 0), (1, β1, 0)]

theorem k22c3Y_0 : k22c3Y β1 γ6 0 = (0, 1, γ6) := rfl
theorem k22c3Y_1 : k22c3Y β1 γ6 1 = (0, 0, 1) := rfl
theorem k22c3Y_2 : k22c3Y β1 γ6 2 = (0, 0, 0) := rfl
theorem k22c3Y_3 : k22c3Y β1 γ6 3 = (1, 0, 0) := rfl
theorem k22c3Y_4 : k22c3Y β1 γ6 4 = (1, β1, 0) := rfl

theorem k22c3Y_inj {β1 γ6 : ℝ} (hβ1 : 0 < β1) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) :
    ∀ i j, k22c3Y β1 γ6 i = k22c3Y β1 γ6 j → i = j := by
  intro i j h
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [k22c3Y_0, k22c3Y_1, k22c3Y_2, k22c3Y_3, k22c3Y_4, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith)

set_option maxHeartbeats 12800000 in
theorem k22c3_tsc {D β1 γ4 γ6 v1 v2 : ℝ} (hD : 0 < D) (hβ1 : 0 < β1) (hγ4 : 0 < γ4)
    (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) (hv1 : 0 < v1) (hw : v1 + v2 < 0) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc D (k22c3Y β1 γ6 (i + 1) - k22c3Y β1 γ6 i) (k22c3Y β1 γ6 j - k22c3Y β1 γ6 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (1 : ℝ), (0 : ℝ)), (1, 0, γ4)], ∀ i : ZMod 5,
      TSc D (k22c3Y β1 γ6 (i + 1) - k22c3Y β1 γ6 i) (t - k22c3Y β1 γ6 i) (v1, v2, 0)) := by
  obtain ⟨e0, e1, e2, e3, e4, f0, f1, f2, f3, f4⟩ := k19_z5
  have hn2 : 0 < -v2 := by linarith
  have hw' : 0 < -(v1 + v2) := by linarith
  have hs : 0 < β1 * v1 + -v2 := by nlinarith
  have k1 := hD
  have kb := mul_pos hD hβ1
  have kg := mul_pos hD hγ6
  have kg4 := mul_pos hD hγ4
  have kv1 := mul_pos hD hv1
  have kn2 := mul_pos hD hn2
  have kw := mul_pos hD hw'
  have ks := mul_pos hD hs
  have kbv := mul_pos kb hv1
  have kgv := mul_pos kg hv1
  have kg4n := mul_pos kg4 hn2
  have kbg4v := mul_pos (mul_pos kb hγ4) hv1
  have kgs := mul_pos kg hs
  have kgw := mul_pos kg hw'
  have kgbv := mul_pos (mul_pos kg hβ1) hv1
  have kg1 := mul_pos hD (sub_pos.2 hγ61)
  have kbs := mul_pos kb hs
  have kbn := mul_pos kb hn2
  refine ⟨?_, ?_⟩
  · intro i j h1 h2'
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2' (by decide)).elim
      | (simp only [TSc, d3, e0, e1, e2, e3, e4, f0, f1, f2, f3, f4, k22c3Y_0, k22c3Y_1, k22c3Y_2, k22c3Y_3,
          k22c3Y_4, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first
         | (left; nlinarith)
         | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;>
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, e0, e1, e2, e3, e4, f0, f1, f2, f3, f4, k22c3Y_0, k22c3Y_1, k22c3Y_2, k22c3Y_3,
          k22c3Y_4, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
