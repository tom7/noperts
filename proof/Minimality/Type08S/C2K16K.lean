module

public import Minimality.Type08S.C2K16J

@[expose] public section


/-!
# K16 / K: H5 rule r2 (view `c' - a'`, pentagon `(b', a', b, d, a)`): cycle, injectivity, TSc
Frame `(a - d, b - d, c' - a')`, `g = 1/γ6`: `c = (α1 g, (β1-β6) g, -g)`, `b' = (α1 (1 + β1 g), β1 (β1-β6) g, -β1 g)`, `a' = (α1, β1, -1)`.
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

def k16R2Cyc (α1 β1 β6 g : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  ![(α1 * (1 + β1 * g), β1 * (β1 - β6) * g, -(β1 * g)), (α1, β1, -1), (0, 1, 0), (0, 0, 0), (1, 0, 0)]

theorem k16R2Cyc_0 : k16R2Cyc α1 β1 β6 g 0 = (α1 * (1 + β1 * g), β1 * (β1 - β6) * g, -(β1 * g)) := rfl
theorem k16R2Cyc_1 : k16R2Cyc α1 β1 β6 g 1 = (α1, β1, -1) := rfl
theorem k16R2Cyc_2 : k16R2Cyc α1 β1 β6 g 2 = (0, 1, 0) := rfl
theorem k16R2Cyc_3 : k16R2Cyc α1 β1 β6 g 3 = (0, 0, 0) := rfl
theorem k16R2Cyc_4 : k16R2Cyc α1 β1 β6 g 4 = (1, 0, 0) := rfl

theorem k16R2_inj {α1 β1 β6 g : ℝ} (hα1 : 0 < α1) (hβ1 : 1 < β1) (hg : 0 < g) :
    ∀ i j : ZMod 5, k16R2Cyc α1 β1 β6 g i = k16R2Cyc α1 β1 β6 g j → i = j := by
  intro i j h
  have e1 := congrArg Prod.fst h
  have e2 := congrArg (fun t => t.2.1) h
  have e3 := congrArg (fun t => t.2.2) h
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; simp only [k16R2Cyc_0, k16R2Cyc_1, k16R2Cyc_2, k16R2Cyc_3, k16R2Cyc_4] at e1 e2 e3; nlinarith)

set_option maxHeartbeats 6400000 in
theorem k16R2_tsc {α1 β1 β6 γ6 g v1 v2 : ℝ} (hα1 : 1 < α1) (hβ1 : 1 < β1) (hb6 : 0 < β6) (hb61 : β6 < 1)
    (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) (hσ : β1 < β6 + γ6) (hg : g * γ6 = 1)
    (hc1 : (β1 - 1) * v1 < α1 * v2) (hc2 : -(β6 + γ6 - β1) * v1 < α1 * v2) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc 1 (k16R2Cyc α1 β1 β6 g (i + 1) - k16R2Cyc α1 β1 β6 g i)
        (k16R2Cyc α1 β1 β6 g j - k16R2Cyc α1 β1 β6 g i) (v1, v2, 0)) ∧
    (∀ t ∈ [((α1 : ℝ), (β1 : ℝ), (0 : ℝ)), (α1 * g, (β1 - β6) * g, -g)], ∀ i : ZMod 5,
      TSc 1 (k16R2Cyc α1 β1 β6 g (i + 1) - k16R2Cyc α1 β1 β6 g i)
        (t - k16R2Cyc α1 β1 β6 g i) (v1, v2, 0)) := by
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  have hgp : 0 < g := by
    by_contra h; push Not at h; nlinarith
  have a1 : 0 < α1 - 1 := by linarith
  have b1 : 0 < β1 - 1 := by linarith
  have sg : 0 < β6 + γ6 - β1 := by linarith
  have c6 : 0 < 1 - β6 := by linarith
  have bb : 0 < β1 - β6 := by linarith
  have h1 := mul_pos hgp hb6
  have h2 := mul_pos hgp (by linarith : (0:ℝ) < α1)
  have h3 := mul_pos hgp (by linarith : (0:ℝ) < β1)
  have h4 := mul_pos (by linarith : (0:ℝ) < α1) (by linarith : (0:ℝ) < β1)
  have h5 := mul_pos hgp bb
  have h6 := mul_pos (by linarith : (0:ℝ) < α1) bb
  have h7 := mul_pos (by linarith : (0:ℝ) < α1) sg
  have h8 := mul_pos (by linarith : (0:ℝ) < α1) b1
  have h9 := mul_pos (mul_pos hgp (by linarith : (0:ℝ) < α1)) (by linarith : (0:ℝ) < β1)
  have h10 := mul_pos (mul_pos hgp (by linarith : (0:ℝ) < α1)) bb
  have h11 := mul_pos (mul_pos hgp (by linarith : (0:ℝ) < α1)) sg
  have h12 := mul_pos (mul_pos hgp (by linarith : (0:ℝ) < α1)) b1
  have h13 := mul_pos (mul_pos hgp (by linarith : (0:ℝ) < β1)) bb
  have h14 := mul_pos (mul_pos hgp (by linarith : (0:ℝ) < β1)) sg
  have h15 := mul_pos (mul_pos hgp (by linarith : (0:ℝ) < β1)) b1
  have h16 := mul_pos (mul_pos hgp a1) b1
  have h17 := mul_pos (mul_pos hgp a1) bb
  have h18 := mul_pos (mul_pos hgp a1) sg
  have h19 := mul_pos (mul_pos (mul_pos hgp (by linarith : (0:ℝ) < α1)) (by linarith : (0:ℝ) < β1)) bb
  have h20 := mul_pos (mul_pos (mul_pos hgp (by linarith : (0:ℝ) < α1)) (by linarith : (0:ℝ) < β1)) sg
  have h21 := mul_pos (mul_pos (mul_pos hgp (by linarith : (0:ℝ) < α1)) (by linarith : (0:ℝ) < β1)) b1
  have hc2' : 0 < α1 * v2 + (β6 + γ6 - β1) * v1 := by linarith
  have hc1' : 0 < α1 * v2 - (β1 - 1) * v1 := by linarith
  have P1 := mul_pos h3 hc2'
  have P2 := mul_pos hgp hc2'
  have P3 := mul_pos hgp hc1'
  have P4 := mul_pos h3 hc1'
  have hgv : g * γ6 * (β1 * v1) = β1 * v1 := by rw [hg]; ring
  have hgv2 : g * γ6 * v1 = v1 := by rw [hg]; ring
  constructor
  · intro i j h1 h2
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, k16R2Cyc_0, k16R2Cyc_1, k16R2Cyc_2, k16R2Cyc_3, k16R2Cyc_4, f0, f1, f2, f3, f4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;>
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k16R2Cyc_0, k16R2Cyc_1, k16R2Cyc_2, k16R2Cyc_3, k16R2Cyc_4, f0, f1, f2, f3, f4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
