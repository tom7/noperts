module

public import Minimality.Type08S.C2K14D
public import Minimality.Type08S.C2K16E
public import Minimality.Type08S.C2K22ZA
public import Minimality.Type08S.C2K19G
public import Minimality.Type08S.C2K18A
public import Minimality.Type08S.C2K25Tie
public import Minimality.Type08S.C2K19B
public import Minimality.Type08S.C2K28B4a1

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

/-- Cycle `(a, b', c', a', c, d)` in the frame `(a-d, b-d, μ(a-d) - (c-d))`. -/
def k28b4eY (α1 β1 γ6 μ : ℝ) : ZMod 6 → ℝ × ℝ × ℝ :=
  ![(1, 0, 0), (α1 + β1 * μ, 0, -β1), (α1, β1, 0), (γ6 * μ, 1, -γ6), (μ, 0, -1), (0, 0, 0)]

theorem k28b4e_z6 (i : ZMod 6) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by revert i; decide

theorem k28b4eY_0 : k28b4eY α1 β1 γ6 μ 0 = (1, 0, 0) := rfl
theorem k28b4eY_1 : k28b4eY α1 β1 γ6 μ 1 = (α1 + β1 * μ, 0, -β1) := rfl
theorem k28b4eY_2 : k28b4eY α1 β1 γ6 μ 2 = (α1, β1, 0) := rfl
theorem k28b4eY_3 : k28b4eY α1 β1 γ6 μ 3 = (γ6 * μ, 1, -γ6) := rfl
theorem k28b4eY_4 : k28b4eY α1 β1 γ6 μ 4 = (μ, 0, -1) := rfl
theorem k28b4eY_5 : k28b4eY α1 β1 γ6 μ 5 = (0, 0, 0) := rfl

theorem k28b4eY_inj {α1 β1 γ6 μ : ℝ} (hα1 : 1 < α1) (hβ1 : 1 < β1) (hγ6 : 0 < γ6) (hμ : μ < 0) :
    ∀ i j, k28b4eY α1 β1 γ6 μ i = k28b4eY α1 β1 γ6 μ j → i = j := by
  intro i j h
  rcases k28b4e_z6 i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases k28b4e_z6 j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [k28b4eY_0, k28b4eY_1, k28b4eY_2, k28b4eY_3, k28b4eY_4, k28b4eY_5, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; obtain ⟨h1, h2, h3⟩ := h; linarith) |
      (exfalso; obtain ⟨h1, h2, h3⟩ := h; nlinarith)

set_option maxHeartbeats 12800000 in
theorem k28b4e_tsc {D α1 β1 γ6 μ v1 v2 : ℝ} (hD : 0 < D) (hα1 : 1 < α1) (hβ1 : 1 < β1)
    (hγ6 : 0 < γ6) (hσ : β1 < 1 + γ6) (hμ : μ < 0) (hLp : 0 < α1 + (β1 - 1) * μ)
    (hLq : 0 < α1 - 1 + β1 * μ) (hv2 : 0 < v2) :
    (∀ i j : ZMod 6, j ≠ i → j ≠ i + 1 →
      TSc D (k28b4eY α1 β1 γ6 μ (i + 1) - k28b4eY α1 β1 γ6 μ i) (k28b4eY α1 β1 γ6 μ j - k28b4eY α1 β1 γ6 μ i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (1 : ℝ), (0 : ℝ))], ∀ i : ZMod 6,
      TSc D (k28b4eY α1 β1 γ6 μ (i + 1) - k28b4eY α1 β1 γ6 μ i) (t - k28b4eY α1 β1 γ6 μ i) (v1, v2, 0)) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, e0, e1, e2, e3, e4, e5⟩ := k19_z6
  have a1 := sub_pos.2 hα1
  have b1 := sub_pos.2 hβ1
  have s1 : 0 < 1 + γ6 - β1 := by linarith
  have n1 : 0 < -μ := by linarith
  have L2 : 0 < α1 - 1 + β1 * μ := hLq
  have hb0 : (0:ℝ) < β1 := by linarith
  have ha0 : (0:ℝ) < α1 := by linarith
  have k0 := mul_pos hD hγ6
  have k1 := mul_pos hD a1
  have k2 := mul_pos hD b1
  have k3 := mul_pos hD n1
  have k4 := mul_pos hD hv2
  have k5 := mul_pos hD hb0
  have k6 := mul_pos hD hLp
  have k8 := mul_pos hD L2
  have k9 := mul_pos hD s1
  have k10 := mul_pos (mul_pos hD hb0) hv2
  have k12 := mul_pos (mul_pos hD hγ6) hv2
  have k13 := mul_pos (mul_pos hD hγ6) n1
  have k15 := mul_pos (mul_pos hD hb0) n1
  have k16 := mul_pos (mul_pos hD hv2) n1
  have k17 := mul_pos (mul_pos hD hb0) hLp
  have k18 := mul_pos (mul_pos hD hb0) L2
  have k19 := mul_pos (mul_pos hD hγ6) hLp
  have k20 := mul_pos (mul_pos hD hγ6) L2
  refine ⟨?_, ?_⟩
  · intro i j h1 h2'
    rcases k28b4e_z6 i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases k28b4e_z6 j with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2' (by decide)).elim
      | (simp only [TSc, d3, e0, e1, e2, e3, e4, e5, f0, f1, f2, f3, f4, f5, k28b4eY_0, k28b4eY_1, k28b4eY_2, k28b4eY_3, k28b4eY_4, k28b4eY_5,
            Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first
         | (left; nlinarith)
         | (right; refine ⟨by ring, by nlinarith⟩))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl <;>
    rcases k28b4e_z6 i with rfl | rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, e0, e1, e2, e3, e4, e5, f0, f1, f2, f3, f4, f5, k28b4eY_0, k28b4eY_1, k28b4eY_2, k28b4eY_3, k28b4eY_4, k28b4eY_5,
            Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
