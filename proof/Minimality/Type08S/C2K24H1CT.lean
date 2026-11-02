module

public import Minimality.Type08S.C2K24H1CA

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

/-- Cycle `b', a, c', a', c` (ccw) in the frame `(b-d, c-d, a-b')`, `w = 1/(α1-1)`. -/
def k24h1cY (w β1 β6 γ6 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  ![(0, -w * β1, -w - 1), (0, -w * β1, -w), (β1, -(1 + w) * β1, -(1 + w)), (β6, γ6, 0), (0, 1, 0)]

theorem k24h1cY_0 : k24h1cY w β1 β6 γ6 0 = (0, -w * β1, -w - 1) := rfl
theorem k24h1cY_1 : k24h1cY w β1 β6 γ6 1 = (0, -w * β1, -w) := rfl
theorem k24h1cY_2 : k24h1cY w β1 β6 γ6 2 = (β1, -(1 + w) * β1, -(1 + w)) := rfl
theorem k24h1cY_3 : k24h1cY w β1 β6 γ6 3 = (β6, γ6, 0) := rfl
theorem k24h1cY_4 : k24h1cY w β1 β6 γ6 4 = (0, 1, 0) := rfl

theorem k24h1cY_inj {w β1 β6 γ6 : ℝ} (hw : 0 < w) (hβ1 : 1 < β1) (hβ6 : 1 < β6) (hγ6 : 1 < γ6) :
    ∀ i j, k24h1cY w β1 β6 γ6 i = k24h1cY w β1 β6 γ6 j → i = j := by
  intro i j h
  have h1 := mul_pos hw (by linarith : (0:ℝ) < β1)
  have h2 := mul_pos hw (by linarith : (0:ℝ) < β1)
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [k24h1cY_0, k24h1cY_1, k24h1cY_2, k24h1cY_3, k24h1cY_4, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith) | (exfalso; linarith [h.1, h.2.1, h.2.2]) |
      (exfalso; obtain ⟨h1, h2, h3⟩ := h; nlinarith)

set_option maxHeartbeats 12800000 in
theorem k24h1c_tsc {D w β1 β6 γ6 v1 v2 : ℝ} (hD : 0 < D) (hw : 0 < w) (hβ1 : 1 < β1) (hβ6 : 1 < β6)
    (hγ6 : 1 < γ6) (hσ : β1 < β6 + γ6) (hv1 : v1 < 0) (hv2 : 0 < v1 + v2) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc D (k24h1cY w β1 β6 γ6 (i + 1) - k24h1cY w β1 β6 γ6 i) (k24h1cY w β1 β6 γ6 j - k24h1cY w β1 β6 γ6 i) (v1, v2, 0)) ∧
    (∀ t ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (1, 0, 0)], ∀ i : ZMod 5,
      TSc D (k24h1cY w β1 β6 γ6 (i + 1) - k24h1cY w β1 β6 γ6 i) (t - k24h1cY w β1 β6 γ6 i) (v1, v2, 0)) := by
  obtain ⟨e0, e1, e2, e3, e4, f0, f1, f2, f3, f4⟩ := k19_z5
  obtain ⟨x, hx⟩ : ∃ x, x = β1 - 1 := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = β6 - 1 := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g, g = γ6 - 1 := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = β6 + γ6 - β1 := ⟨_, rfl⟩
  obtain ⟨n1, hn1⟩ : ∃ n1, n1 = -v1 := ⟨_, rfl⟩
  obtain ⟨n2, hn2⟩ : ∃ n2, n2 = v1 + v2 := ⟨_, rfl⟩
  have px : 0 < x := by linarith
  have py : 0 < y := by linarith
  have pg : 0 < g := by linarith
  have ps : 0 < s := by linarith
  have pn1 : 0 < n1 := by linarith
  have pn2 : 0 < n2 := by linarith
  have hb1 : β1 = 1 + x := by linarith
  have hb6 : β6 = 1 + y := by linarith
  have hg6 : γ6 = 1 + g := by linarith
  have hv1' : v1 = -n1 := by linarith
  have hv2' : v2 = n2 + n1 := by linarith
  subst hb1 hb6 hg6 hv1' hv2'
  refine ⟨?_, ?_⟩
  · intro i j h1 h2'
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2' (by decide)).elim
      | (simp only [TSc, d3, e0, e1, e2, e3, e4, f0, f1, f2, f3, f4, k24h1cY_0, k24h1cY_1, k24h1cY_2,
            k24h1cY_3, k24h1cY_4, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first
         | (left; apply mul_pos hD; nlinarith [mul_pos hw px, mul_pos px py, mul_pos px pg, mul_pos hw py, mul_pos hw pg, mul_pos hw ps, mul_pos px ps, mul_pos py pg, mul_pos (mul_pos hw px) py, mul_pos (mul_pos hw px) pg, mul_pos (mul_pos hw px) px, mul_pos (mul_pos hw px) ps, mul_pos pn1 hw, mul_pos pn2 hw, mul_pos pn1 px, mul_pos pn2 px, mul_pos pn1 py, mul_pos pn2 py, mul_pos pn1 pg, mul_pos pn2 pg, mul_pos pn1 ps, mul_pos pn2 ps])
         | (right; refine ⟨by ring, ?_⟩; apply mul_pos hD; nlinarith [mul_pos hw px, mul_pos px py, mul_pos px pg, mul_pos hw py, mul_pos hw pg, mul_pos pn1 hw, mul_pos pn2 hw, mul_pos pn1 px, mul_pos pn2 px, mul_pos pn1 py, mul_pos pn2 py, mul_pos pn1 pg, mul_pos pn2 pg, mul_pos pn1 ps, mul_pos pn2 ps, mul_pos (mul_pos hw px) pn1, mul_pos (mul_pos hw px) pn2]))
  · intro t ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;>
    rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, e0, e1, e2, e3, e4, f0, f1, f2, f3, f4, k24h1cY_0, k24h1cY_1, k24h1cY_2,
            k24h1cY_3, k24h1cY_4, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; apply mul_pos hD; nlinarith [mul_pos hw px, mul_pos px py, mul_pos px pg, mul_pos hw py, mul_pos hw pg, mul_pos hw ps, mul_pos px ps, mul_pos py pg, mul_pos (mul_pos hw px) py, mul_pos (mul_pos hw px) pg, mul_pos (mul_pos hw px) px, mul_pos (mul_pos hw px) ps, mul_pos pn1 hw, mul_pos pn2 hw, mul_pos pn1 px, mul_pos pn2 px, mul_pos pn1 py, mul_pos pn2 py, mul_pos pn1 pg, mul_pos pn2 pg, mul_pos pn1 ps, mul_pos pn2 ps])
       | (right; refine ⟨by ring, ?_⟩; apply mul_pos hD; nlinarith [mul_pos hw px, mul_pos px py, mul_pos px pg, mul_pos hw py, mul_pos hw pg, mul_pos pn1 hw, mul_pos pn2 hw, mul_pos pn1 px, mul_pos pn2 px, mul_pos pn1 py, mul_pos pn2 py, mul_pos pn1 pg, mul_pos pn2 pg, mul_pos pn1 ps, mul_pos pn2 ps, mul_pos (mul_pos hw px) pn1, mul_pos (mul_pos hw px) pn2])
       )

end C2
end Type08Sp
end Minimality
