module

public import Minimality.Type08S.C2K14D
public import Minimality.Type08S.C2K16E
public import Minimality.Type08S.C2K22ZA
public import Minimality.Type08S.C2K19G
public import Minimality.Type08S.C2K18A
public import Minimality.Type08S.C2K25Tie

@[expose] public section

set_option maxHeartbeats 1000000
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace Type08Sp
namespace C2

/-- Cycle `(a, c', a', c, b')` in the frame `(a-d, b-d, μ(a-d) - (c-d))`. -/
def k28b4pY (α1 β1 γ6 μ : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  ![(1, 0, 0), (α1, β1, 0), (γ6 * μ, 1, -γ6), (μ, 0, -1), (α1 + β1 * μ, 0, -β1)]

theorem k28b4pY_0 : k28b4pY α1 β1 γ6 μ 0 = (1, 0, 0) := rfl
theorem k28b4pY_1 : k28b4pY α1 β1 γ6 μ 1 = (α1, β1, 0) := rfl
theorem k28b4pY_2 : k28b4pY α1 β1 γ6 μ 2 = (γ6 * μ, 1, -γ6) := rfl
theorem k28b4pY_3 : k28b4pY α1 β1 γ6 μ 3 = (μ, 0, -1) := rfl
theorem k28b4pY_4 : k28b4pY α1 β1 γ6 μ 4 = (α1 + β1 * μ, 0, -β1) := rfl

theorem k28b4pY_inj {α1 β1 γ6 μ : ℝ} (hα1 : 1 < α1) (hβ1 : 1 < β1) (hγ6 : 0 < γ6) (hμ : μ < 0) :
    ∀ i j, k28b4pY α1 β1 γ6 μ i = k28b4pY α1 β1 γ6 μ j → i = j := by
  intro i j h
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [k28b4pY_0, k28b4pY_1, k28b4pY_2, k28b4pY_3, k28b4pY_4, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; obtain ⟨h1, h2, h3⟩ := h; linarith) |
      (exfalso; obtain ⟨h1, h2, h3⟩ := h; nlinarith)

set_option maxHeartbeats 12800000 in
theorem k28b4p_tsc {D α1 β1 γ6 μ v1 v2 : ℝ} (hD : 0 < D) (hα1 : 1 < α1) (hβ1 : 1 < β1)
    (hγ6 : 0 < γ6) (hσ : β1 < 1 + γ6) (hμ : μ < 0) (hLp : α1 + (β1 - 1) * μ = 0)
    (hLq : α1 - 1 + β1 * μ < 0) (hv2 : v2 < 0) (hr1 : 0 < v1 + μ * v2) (hr2 : 0 < v1 + (1 - γ6) * μ * v2) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc D (k28b4pY α1 β1 γ6 μ (i + 1) - k28b4pY α1 β1 γ6 μ i) (k28b4pY α1 β1 γ6 μ j - k28b4pY α1 β1 γ6 μ i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (0, 1, 0)], ∀ i : ZMod 5,
      TSc D (k28b4pY α1 β1 γ6 μ (i + 1) - k28b4pY α1 β1 γ6 μ i) (t - k28b4pY α1 β1 γ6 μ i) (v1, v2, 0)) := by
  obtain ⟨e0, e1, e2, e3, e4, f0, f1, f2, f3, f4⟩ := k19_z5
  obtain rfl : α1 = -((β1 - 1) * μ) := by linarith
  have a1 := sub_pos.2 hα1
  have b1 := sub_pos.2 hβ1
  have s1 : 0 < 1 + γ6 - β1 := by linarith
  have n1 : 0 < -μ := by linarith
  have L2 : 0 < -(-((β1 - 1) * μ) - 1 + β1 * μ) := by linarith
  have hb0 : (0:ℝ) < β1 := by linarith
  have k0 := mul_pos hD hγ6
  have q1 := mul_pos hD hr1
  have q2 := mul_pos hD hr2
  have q3 := mul_pos (mul_pos hD hr1) hb0
  have q4 := mul_pos (mul_pos hD hr2) hb0
  have q5 := mul_pos (mul_pos hD hr1) b1
  have q6 := mul_pos (mul_pos hD hr2) b1
  have q7 := mul_pos (mul_pos hD hr1) hγ6
  have q8 := mul_pos (mul_pos hD hr2) hγ6
  have k1 := mul_pos hD a1
  have k2 := mul_pos hD b1
  have k3 := mul_pos hD n1
  have n2 : 0 < -v2 := by linarith
  have k4 := mul_pos hD n2
  have k5 := mul_pos hD hb0
  have k8 := mul_pos hD L2
  have k9 := mul_pos hD s1
  have k10 := mul_pos (mul_pos hD hb0) n2
  have k12 := mul_pos (mul_pos hD hγ6) n2
  have k13 := mul_pos (mul_pos hD hγ6) n1
  have k15 := mul_pos (mul_pos hD hb0) n1
  have k16 := mul_pos (mul_pos hD n2) n1
  have k18 := mul_pos (mul_pos hD hb0) L2
  have k20 := mul_pos (mul_pos hD hγ6) L2
  refine ⟨?_, ?_⟩
  · intro i j h1 h2'
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2' (by decide)).elim
      | (simp only [TSc, d3, e0, e1, e2, e3, e4, f0, f1, f2, f3, f4, k28b4pY_0, k28b4pY_1, k28b4pY_2, k28b4pY_3, k28b4pY_4,
            Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first
         | (left; nlinarith)
         | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;>
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, e0, e1, e2, e3, e4, f0, f1, f2, f3, f4, k28b4pY_0, k28b4pY_1, k28b4pY_2, k28b4pY_3, k28b4pY_4,
            Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
