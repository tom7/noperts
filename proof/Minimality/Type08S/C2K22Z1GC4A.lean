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

/-- Cycle `c', b, a', c, b'` in the frame `(b-d, c-d, a-c')` (`γ4 = 1`), `w = 1/(α1-1)`, `β6 = α4 = 1+k`. -/
def k22z1gc4Y (w k : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  ![(-w, 0, -w - 1), (1, 0, 0), (1 + k, 1, 0), (0, 1, 0), (-(1 + k) * w, 1, -(1 + k) * w)]

theorem k22z1gc4Y_0 : k22z1gc4Y w k 0 = (-w, 0, -w - 1) := rfl
theorem k22z1gc4Y_1 : k22z1gc4Y w k 1 = (1, 0, 0) := rfl
theorem k22z1gc4Y_2 : k22z1gc4Y w k 2 = (1 + k, 1, 0) := rfl
theorem k22z1gc4Y_3 : k22z1gc4Y w k 3 = (0, 1, 0) := rfl
theorem k22z1gc4Y_4 : k22z1gc4Y w k 4 = (-(1 + k) * w, 1, -(1 + k) * w) := rfl

theorem k22z1gc4Y_inj {w k : ℝ} (hw : 0 < w) (hk : 0 < k) :
    ∀ i j, k22z1gc4Y w k i = k22z1gc4Y w k j → i = j := by
  intro i j h
  have h1 := mul_pos hw hk
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [k22z1gc4Y_0, k22z1gc4Y_1, k22z1gc4Y_2, k22z1gc4Y_3, k22z1gc4Y_4, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith)

set_option maxHeartbeats 12800000 in
theorem k22z1gc4_tsc {D w k s1 s2 : ℝ} (hD : 0 < D) (hw : 0 < w) (hk : 0 < k)
    (hs1 : 0 < s1) (hs2 : 0 < s2) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc D (k22z1gc4Y w k (i + 1) - k22z1gc4Y w k i) (k22z1gc4Y w k j - k22z1gc4Y w k i) (-s1, -s2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (-w, 0, -w)], ∀ i : ZMod 5,
      TSc D (k22z1gc4Y w k (i + 1) - k22z1gc4Y w k i) (t - k22z1gc4Y w k i) (-s1, -s2, 0)) := by
  obtain ⟨e0, e1, e2, e3, e4, f0, f1, f2, f3, f4⟩ := k19_z5
  have H0 : 0 < D * (s1) := by positivity
  have H1 : 0 < D * (s2) := by positivity
  have H2 : 0 < D * (k) := by positivity
  have H3 : 0 < D * (k*s1) := by positivity
  have H4 : 0 < D * (k*s2) := by positivity
  have H5 : 0 < D * (k*k) := by positivity
  have H6 : 0 < D * (k*k*s1) := by positivity
  have H7 : 0 < D * (k*k*s2) := by positivity
  have H8 : 0 < D * (w) := by positivity
  have H9 : 0 < D * (w*s1) := by positivity
  have H10 : 0 < D * (w*s2) := by positivity
  have H11 : 0 < D * (w*k) := by positivity
  have H12 : 0 < D * (w*k*s1) := by positivity
  have H13 : 0 < D * (w*k*s2) := by positivity
  have H14 : 0 < D * (w*k*k) := by positivity
  have H15 : 0 < D * (w*k*k*s1) := by positivity
  have H16 : 0 < D * (w*k*k*s2) := by positivity
  have H17 : 0 < D * (w*w) := by positivity
  have H18 : 0 < D * (w*w*s1) := by positivity
  have H19 : 0 < D * (w*w*s2) := by positivity
  have H20 : 0 < D * (w*w*k) := by positivity
  have H21 : 0 < D * (w*w*k*s1) := by positivity
  have H22 : 0 < D * (w*w*k*s2) := by positivity
  have H23 : 0 < D * (w*w*k*k) := by positivity
  have H24 : 0 < D * (w*w*k*k*s1) := by positivity
  have H25 : 0 < D * (w*w*k*k*s2) := by positivity
  have H0 := hD
  refine ⟨?_, ?_⟩
  · intro i j h1 h2'
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2' (by decide)).elim
      | (simp only [TSc, d3, e0, e1, e2, e3, e4, f0, f1, f2, f3, f4, k22z1gc4Y_0, k22z1gc4Y_1, k22z1gc4Y_2,
          k22z1gc4Y_3, k22z1gc4Y_4, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk] <;>
        first
        | (left; linarith)
        | (right; refine ⟨by ring, by linarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;>
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, e0, e1, e2, e3, e4, f0, f1, f2, f3, f4, k22z1gc4Y_0, k22z1gc4Y_1, k22z1gc4Y_2,
          k22z1gc4Y_3, k22z1gc4Y_4, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk] <;>
        first
        | (left; linarith)
        | (right; refine ⟨by ring, by linarith⟩))

end C2
end Type08Sp
end Minimality
