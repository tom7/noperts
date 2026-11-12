module

public import Minimality.Type08S.C2K25Tie
public import Minimality.Type08S.C2K16E
public import Minimality.Type08S.C2K6HF
public import Minimality.Type08S.C2K17B2Z
public import Minimality.Type08S.C2K19G
public import Minimality.Type08S.C2K18A

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

/-- Cycle `(a, c', a', c, d)` in the frame `(a-d, b-d, (c-d) + μ (a-d))`. -/
def k28l2bY (α1 β1 β6 γ6 μ : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  ![(1, 0, 0), (α1, β1, 0), (-(γ6 * μ), β6, γ6), (-μ, 0, 1), (0, 0, 0)]

theorem k28l2bY_0 : k28l2bY α1 β1 β6 γ6 μ 0 = (1, 0, 0) := rfl
theorem k28l2bY_1 : k28l2bY α1 β1 β6 γ6 μ 1 = (α1, β1, 0) := rfl
theorem k28l2bY_2 : k28l2bY α1 β1 β6 γ6 μ 2 = (-(γ6 * μ), β6, γ6) := rfl
theorem k28l2bY_3 : k28l2bY α1 β1 β6 γ6 μ 3 = (-μ, 0, 1) := rfl
theorem k28l2bY_4 : k28l2bY α1 β1 β6 γ6 μ 4 = (0, 0, 0) := rfl

theorem k28l2b_z5 : (0 : ZMod 5) + 1 = 1 ∧ (1 : ZMod 5) + 1 = 2 ∧ (2 : ZMod 5) + 1 = 3 ∧ (3 : ZMod 5) + 1 = 4 ∧
    (4 : ZMod 5) + 1 = 0 ∧ (0 : ZMod 5) - 1 = 4 ∧ (1 : ZMod 5) - 1 = 0 ∧ (2 : ZMod 5) - 1 = 1 ∧
    (3 : ZMod 5) - 1 = 2 ∧ (4 : ZMod 5) - 1 = 3 := by decide

theorem k28l2b_z5_cases (i : ZMod 5) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by revert i; decide

theorem k28l2bY_inj {α1 β1 β6 γ6 μ : ℝ} (hβ1 : 0 < β1) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hμ : 0 < μ) :
    ∀ i j, k28l2bY α1 β1 β6 γ6 μ i = k28l2bY α1 β1 β6 γ6 μ j → i = j := by
  intro i j h
  rcases k28l2b_z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases k28l2b_z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [k28l2bY_0, k28l2bY_1, k28l2bY_2, k28l2bY_3, k28l2bY_4, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; obtain ⟨h1, h2, h3⟩ := h; linarith)

set_option maxHeartbeats 12800000 in
theorem k28l2b_tsc {D α1 β1 β6 γ6 μ v1 v2 : ℝ} (hD : 0 < D) (hα1 : 1 < α1) (hβ1 : 1 < β1) (hβ6 : 1 < β6)
    (hγ6 : 1 < γ6) (hσ : β1 < β6 + γ6) (hμ : 0 < μ) (hE5 : α1 ≤ β1 * μ + 1) (hE6 : (β1 - 1) * μ < α1)
    (hv2 : v2 < 0) (hv3 : 0 < β1 * v1 - (α1 - 1) * v2) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc D (k28l2bY α1 β1 β6 γ6 μ (i + 1) - k28l2bY α1 β1 β6 γ6 μ i)
        (k28l2bY α1 β1 β6 γ6 μ j - k28l2bY α1 β1 β6 γ6 μ i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (1 : ℝ), (0 : ℝ)), (α1 - β1 * μ, 0, β1)], ∀ i : ZMod 5,
      TSc D (k28l2bY α1 β1 β6 γ6 μ (i + 1) - k28l2bY α1 β1 β6 γ6 μ i)
        (t - k28l2bY α1 β1 β6 γ6 μ i) (v1, v2, 0)) := by
  obtain ⟨e0, e1, e2, e3, e4, f0, f1, f2, f3, f4⟩ := k28l2b_z5
  have a1 := sub_pos.2 hα1
  have b1 := sub_pos.2 hβ1
  have c1 := sub_pos.2 hβ6
  have g1 := sub_pos.2 hγ6
  have s1 := sub_pos.2 hσ
  have e6 := sub_pos.2 hE6
  have hα : 0 < α1 := by linarith
  have hβ : 0 < β1 := by linarith
  have hβ6p : 0 < β6 := by linarith
  have hγ : 0 < γ6 := by linarith
  have nv2 : 0 < -v2 := by linarith
  -- cross products at (0,0,1)
  have c02 : 0 < (α1 - 1) * β6 + β1 * (γ6 * μ + 1) := by
    nlinarith [mul_pos a1 hβ6p, mul_pos (mul_pos hβ hγ) hμ]
  have c03 : 0 < β1 * (μ + 1) := by positivity
  have c04 : 0 < β1 := hβ
  have c0b : 0 < (α1 - 1) + β1 := by linarith
  have c13 : 0 < μ * (β1 * (γ6 - 1) + β6) + α1 * β6 := by
    nlinarith [mul_pos hμ (mul_pos hβ g1), mul_pos hμ hβ6p, mul_pos hα hβ6p]
  have c14 : 0 < β1 * (γ6 * μ) + α1 * β6 := by
    nlinarith [mul_pos hβ (mul_pos hγ hμ), mul_pos hα hβ6p]
  have c10 : 0 < β1 * (γ6 * μ) + β6 * (α1 - 1) + β1 := by
    nlinarith [mul_pos hβ (mul_pos hγ hμ), mul_pos hβ6p a1]
  have c1b : 0 < γ6 * μ * (β1 - 1) + α1 * (β6 - 1) := by
    nlinarith [mul_pos (mul_pos hγ hμ) b1, mul_pos hα c1]
  have c1b' : 0 < β1 * (α1 + μ * (γ6 + β6 - β1)) := by
    nlinarith [mul_pos hμ s1, mul_pos hβ (mul_pos hμ (by linarith : (0:ℝ) < γ6 + β6 - β1))]
  have c24 : 0 < β6 * μ := mul_pos hβ6p hμ
  have c20 : 0 < β6 * (1 + μ) := by positivity
  have c21 : 0 < μ * ((γ6 - 1) * β1 + β6) + α1 * β6 := by
    nlinarith [mul_pos hμ (mul_pos g1 hβ), mul_pos hμ hβ6p, mul_pos hα hβ6p]
  have c2b : 0 < μ * (γ6 + β6 - 1) := by nlinarith [mul_pos hμ (by linarith : (0:ℝ) < γ6 + β6 - 1)]
  have c2b' : 0 < β6 * (α1 - (β1 - 1) * μ) := mul_pos hβ6p (by linarith)
  have c30 : 0 < μ * β1 := mul_pos hμ hβ
  have c32 : 0 < μ * β6 := mul_pos hμ hβ6p
  have c3b : 0 < μ := hμ
  refine ⟨?_, ?_⟩
  · intro i j h1 h2'
    rcases k28l2b_z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases k28l2b_z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2' (by decide)).elim
      | (simp only [TSc, d3, e0, e1, e2, e3, e4, f0, f1, f2, f3, f4, k28l2bY_0, k28l2bY_1, k28l2bY_2,
            k28l2bY_3, k28l2bY_4, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first
         | (left; apply mul_pos hD; linarith [c02, c03, c04, c0b, c13, c14, c10, c1b, c1b', c24, c20, c21, c2b, c2b', c30, c32, c3b])
         | (right; refine ⟨?_, ?_⟩; ring1; apply mul_pos hD; nlinarith [mul_pos hα nv2, mul_pos hβ nv2, mul_pos hβ hv3, nv2]))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;>
    rcases k28l2b_z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, e0, e1, e2, e3, e4, f0, f1, f2, f3, f4, k28l2bY_0, k28l2bY_1, k28l2bY_2,
            k28l2bY_3, k28l2bY_4, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; apply mul_pos hD; linarith [c02, c03, c04, c0b, c13, c14, c10, c1b, c1b', c24, c20, c21, c2b, c2b', c30, c32, c3b])
       | (right; refine ⟨?_, ?_⟩; ring1; apply mul_pos hD; nlinarith [mul_pos hα nv2, mul_pos hβ nv2, mul_pos hβ hv3, nv2])
       | (rcases hE5.lt_or_eq with h | h
          · left; apply mul_pos hD; nlinarith [mul_pos hβ (sub_pos.2 h)]
          · right; refine ⟨?_, ?_⟩; linear_combination (-(D * β1)) * h; apply mul_pos hD; nlinarith [mul_pos hβ hv3]))

end C2
end Type08Sp
end Minimality
