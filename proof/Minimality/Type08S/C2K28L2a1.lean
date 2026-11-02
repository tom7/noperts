import Minimality.Type08S.C2K22ZA
import Minimality.Type08S.C2K19G
import Minimality.Type08S.C2K18A
import Minimality.Type08S.C2K25Tie

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- Pentagon `(b', a, c', a', c)` in the frame `(a-d, b-d, c-d+ρ(a-d))`. -/
def k28l2aY (α1 β1 β6 γ6 ρ : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  ![(α1 - β1 * ρ, 0, β1), (1, 0, 0), (α1, β1, 0), (-(γ6 * ρ), β6, γ6), (-ρ, 0, 1)]

theorem k28l2aY_0 : k28l2aY α1 β1 β6 γ6 ρ 0 = (α1 - β1 * ρ, 0, β1) := rfl
theorem k28l2aY_1 : k28l2aY α1 β1 β6 γ6 ρ 1 = (1, 0, 0) := rfl
theorem k28l2aY_2 : k28l2aY α1 β1 β6 γ6 ρ 2 = (α1, β1, 0) := rfl
theorem k28l2aY_3 : k28l2aY α1 β1 β6 γ6 ρ 3 = (-(γ6 * ρ), β6, γ6) := rfl
theorem k28l2aY_4 : k28l2aY α1 β1 β6 γ6 ρ 4 = (-ρ, 0, 1) := rfl

theorem k28l2aY_inj {α1 β1 β6 γ6 ρ : ℝ} (hα1 : 1 < α1) (hβ1 : 1 < β1) (hβ6 : 1 < β6) (hγ6 : 1 < γ6)
    (hρ : 0 < ρ) (hx1 : α1 - 1 < β1 * ρ) (hx2 : (β1 - 1) * ρ < α1) :
    ∀ i j, k28l2aY α1 β1 β6 γ6 ρ i = k28l2aY α1 β1 β6 γ6 ρ j → i = j := by
  intro i j h
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [k28l2aY_0, k28l2aY_1, k28l2aY_2, k28l2aY_3, k28l2aY_4, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith) | (exfalso; linarith [h.1, h.2.1, h.2.2]) |
      (exfalso; obtain ⟨h1, h2, h3⟩ := h; linarith) |
      (exfalso; obtain ⟨h1, h2, h3⟩ := h; nlinarith)

set_option maxHeartbeats 12800000 in
theorem k28l2a_tsc {D α1 β1 β6 γ6 ρ v1 v2 : ℝ} (hD : 0 < D) (hα1 : 1 < α1) (hβ1 : 1 < β1) (hβ6 : 1 < β6)
    (hγ6 : 1 < γ6) (hσ : β1 < β6 + γ6) (hρ : 0 < ρ) (hx1 : α1 - 1 < β1 * ρ) (hx2 : (β1 - 1) * ρ < α1)
    (hv2 : 0 < v2) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc D (k28l2aY α1 β1 β6 γ6 ρ (i + 1) - k28l2aY α1 β1 β6 γ6 ρ i)
        (k28l2aY α1 β1 β6 γ6 ρ j - k28l2aY α1 β1 β6 γ6 ρ i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (0, 1, 0)], ∀ i : ZMod 5,
      TSc D (k28l2aY α1 β1 β6 γ6 ρ (i + 1) - k28l2aY α1 β1 β6 γ6 ρ i)
        (t - k28l2aY α1 β1 β6 γ6 ρ i) (v1, v2, 0)) := by
  obtain ⟨e0, e1, e2, e3, e4, f0, f1, f2, f3, f4⟩ := k19_z5
  have a1 := sub_pos.2 hα1
  have b1 := sub_pos.2 hβ1
  have B1 := sub_pos.2 hβ6
  have g1 := sub_pos.2 hγ6
  have s1 := sub_pos.2 hσ
  have x1 := sub_pos.2 hx1
  have x2 := sub_pos.2 hx2
  have p0 : 0 < α1 := by linarith
  have p1 : 0 < β1 := by linarith
  have p2 : 0 < β6 := by linarith
  have p3 : 0 < γ6 := by linarith
  refine ⟨?_, ?_⟩
  · intro i j h1 h2'
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2' (by decide)).elim
      | (simp only [TSc, d3, e0, e1, e2, e3, e4, f0, f1, f2, f3, f4, k28l2aY_0, k28l2aY_1, k28l2aY_2,
            k28l2aY_3, k28l2aY_4, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first
         | (left; apply mul_pos hD; nlinarith [mul_pos p1 x1, mul_pos p2 x2, mul_pos p2 hρ, mul_pos p1 hρ, mul_pos p3 hρ,  mul_pos p2 p0, mul_pos p1 p3, mul_pos (mul_pos p1 g1) hρ, mul_pos p2 x1, mul_pos p1 x2, mul_pos p1 s1, mul_pos hρ s1, mul_pos p0 B1, mul_pos B1 hρ, mul_pos (mul_pos p3 b1) hρ, mul_pos p0 a1, mul_pos a1 p2, mul_pos p1 a1])
         | (left; nlinarith)
         | (right; refine ⟨by ring, ?_⟩; apply mul_pos hD; nlinarith [mul_pos p1 hv2, mul_pos p0 hv2, mul_pos hv2 b1]))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;>
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, e0, e1, e2, e3, e4, f0, f1, f2, f3, f4, k28l2aY_0, k28l2aY_1, k28l2aY_2,
            k28l2aY_3, k28l2aY_4, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; apply mul_pos hD; nlinarith [mul_pos p1 x1, mul_pos p2 x2, mul_pos p2 hρ, mul_pos p1 hρ, mul_pos p3 hρ,  mul_pos p2 p0, mul_pos p1 p3, mul_pos (mul_pos p1 g1) hρ, mul_pos p2 x1, mul_pos p1 x2, mul_pos p1 s1, mul_pos hρ s1, mul_pos p0 B1, mul_pos B1 hρ, mul_pos (mul_pos p3 b1) hρ, mul_pos p0 a1, mul_pos a1 p2, mul_pos p1 a1])
       | (left; nlinarith)
       | (right; refine ⟨by ring, ?_⟩; apply mul_pos hD; nlinarith [mul_pos p1 hv2, mul_pos p0 hv2, mul_pos hv2 b1]))

end C2
end Type08Sp
end Minimality
