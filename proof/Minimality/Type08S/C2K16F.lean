module

public import Minimality.Type08S.C2K16E

@[expose] public section


/-!
# K16 / F: H5 rule r1 (view `c - d`, pentagon `(c', b, a', c, b')`): the cell lemma (frame, TSc, unimodality)
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- Pentagon `(c', b, a', c, b')` in the frame `(a - d, b - d, c - d)`. -/
def k16R1Cyc (α1 β1 β6 γ6 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  ![(α1, β1, 0), (0, 1, 0), (0, β6, γ6), (0, 0, 1), (α1, 0, β1)]

theorem k16R1Cyc_0 : k16R1Cyc α1 β1 β6 γ6 0 = (α1, β1, 0) := rfl
theorem k16R1Cyc_1 : k16R1Cyc α1 β1 β6 γ6 1 = (0, 1, 0) := rfl
theorem k16R1Cyc_2 : k16R1Cyc α1 β1 β6 γ6 2 = (0, β6, γ6) := rfl
theorem k16R1Cyc_3 : k16R1Cyc α1 β1 β6 γ6 3 = (0, 0, 1) := rfl
theorem k16R1Cyc_4 : k16R1Cyc α1 β1 β6 γ6 4 = (α1, 0, β1) := rfl

theorem k16R1_inj {α1 β1 β6 γ6 : ℝ} (hα1 : 0 < α1) (hβ1 : 1 < β1) (hb6 : 0 < β6) (hγ6 : 0 < γ6) :
    ∀ i j : ZMod 5, k16R1Cyc α1 β1 β6 γ6 i = k16R1Cyc α1 β1 β6 γ6 j → i = j := by
  intro i j h
  have e1 := congrArg Prod.fst h
  have e2 := congrArg (fun t => t.2.1) h
  have e3 := congrArg (fun t => t.2.2) h
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; simp only [k16R1Cyc_0, k16R1Cyc_1, k16R1Cyc_2, k16R1Cyc_3, k16R1Cyc_4] at e1 e2 e3; linarith)

set_option maxHeartbeats 3200000 in
theorem k16R1_tsc {α1 β1 β6 γ6 v1 v2 : ℝ} (hα1 : 1 < α1) (hβ1 : 1 < β1) (hb6 : 0 < β6) (hb61 : β6 < 1)
    (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) (hσ : β1 < β6 + γ6) (hv1 : 0 < v1) (hv2 : 0 < v2) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc 1 (k16R1Cyc α1 β1 β6 γ6 (i + 1) - k16R1Cyc α1 β1 β6 γ6 i)
        (k16R1Cyc α1 β1 β6 γ6 j - k16R1Cyc α1 β1 β6 γ6 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((1 : ℝ), (0 : ℝ), (0 : ℝ)), (0, 0, 0)], ∀ i : ZMod 5,
      TSc 1 (k16R1Cyc α1 β1 β6 γ6 (i + 1) - k16R1Cyc α1 β1 β6 γ6 i)
        (t - k16R1Cyc α1 β1 β6 γ6 i) (v1, v2, 0)) := by
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  have a1 : 0 < α1 - 1 := by linarith
  have b1 : 0 < β1 - 1 := by linarith
  have sg : 0 < β6 + γ6 - β1 := by linarith
  have c6 : 0 < 1 - β6 := by linarith
  have g6 : 0 < 1 - γ6 := by linarith
  have h1 := mul_pos hv1 hv2
  have h2 := mul_pos hv1 a1
  have h3 := mul_pos hv2 a1
  have h4 := mul_pos hv1 b1
  have h5 := mul_pos hv2 b1
  have h6 := mul_pos hv1 sg
  have h7 := mul_pos hv2 sg
  have h8 := mul_pos hv1 hb6
  have h9 := mul_pos hv2 hb6
  have h10 := mul_pos hv1 hγ6
  have h11 := mul_pos hv2 hγ6
  have h12 := mul_pos a1 b1
  have h13 := mul_pos a1 sg
  have h14 := mul_pos b1 sg
  have h15 := mul_pos hv1 c6
  have h16 := mul_pos hv2 c6
  have h17 := mul_pos hv1 g6
  have h18 := mul_pos hv2 g6
  have h19 := mul_pos hb6 hγ6
  constructor
  · intro i j h1 h2
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, k16R1Cyc_0, k16R1Cyc_1, k16R1Cyc_2, k16R1Cyc_3, k16R1Cyc_4, f0, f1, f2, f3, f4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;>
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k16R1Cyc_0, k16R1Cyc_1, k16R1Cyc_2, k16R1Cyc_3, k16R1Cyc_4, f0, f1, f2, f3, f4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
