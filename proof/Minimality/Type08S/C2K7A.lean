module

public import Minimality.Type08S.C2K6

@[expose] public section

/-!
# K7 / A: the 5-cycle `(b, a', c, b', c')` at the view `b - d` (frame `(P, Q, R) = (c - d, a - d, b - d)`)
Tests (`TSc`) in the cone `v1 > 0, v2 > 0`, and the peak lemma.
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

/-- Peak lemma: `P1 > P0`, `P1 > P2`, `P3 < P4`, `P4 < P0`: the unique peak is `1`. -/
theorem lexUni5_v7 (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h01 : LexLt (z 0, w 0) (z 1, w 1)) (h21 : LexLt (z 2, w 2) (z 1, w 1))
    (h34 : LexLt (z 3, w 3) (z 4, w 4)) (h40 : LexLt (z 4, w 4) (z 0, w 0)) : LexUni z w := by
  classical
  refine ⟨hinj, ?_⟩
  rw [Finset.card_filter]
  have hs : ∀ g : ZMod 5 → ℕ, ∑ i, g i = g 0 + g 1 + g 2 + g 3 + g 4 := fun g => Fin.sum_univ_five (f := g)
  rw [hs]
  have e0 : (0 : ZMod 5) - 1 = 4 := by decide
  have e1 : (1 : ZMod 5) - 1 = 0 := by decide
  have e2 : (2 : ZMod 5) - 1 = 1 := by decide
  have e3 : (3 : ZMod 5) - 1 = 2 := by decide
  have e4 : (4 : ZMod 5) - 1 = 3 := by decide
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  show (if LexLt (z (0 - 1), w (0 - 1)) (z 0, w 0) ∧ LexLt (z (0 + 1), w (0 + 1)) (z 0, w 0) then 1 else 0) +
    (if LexLt (z (1 - 1), w (1 - 1)) (z 1, w 1) ∧ LexLt (z (1 + 1), w (1 + 1)) (z 1, w 1) then 1 else 0) +
    (if LexLt (z (2 - 1), w (2 - 1)) (z 2, w 2) ∧ LexLt (z (2 + 1), w (2 + 1)) (z 2, w 2) then 1 else 0) +
    (if LexLt (z (3 - 1), w (3 - 1)) (z 3, w 3) ∧ LexLt (z (3 + 1), w (3 + 1)) (z 3, w 3) then 1 else 0) +
    (if LexLt (z (4 - 1), w (4 - 1)) (z 4, w 4) ∧ LexLt (z (4 + 1), w (4 + 1)) (z 4, w 4) then 1 else 0) = 1
  rw [e0, e1, e2, e3, e4, f0, f1, f2, f3, f4]
  have a01 := lexLt_asymm h01
  have a21 := lexLt_asymm h21
  have a34 := lexLt_asymm h34
  have a40 := lexLt_asymm h40
  simp [h01, a01, h21, a21, h34, a34, h40, a40]

/-- The ccw cycle `(b, a', c, b', c')` in the frame `(P, Q, R)`: `b = (0,0,1)`, `a' = (1,0,β6)`, `c = (1,0,0)`,
`b' = (1,α4,0)`, `c' = (0,α1,β1)`. -/
def k7Cyc (α1 β1 α4 β6 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  pc5 (0, 0, 1) (1, 0, β6) (1, 0, 0) (1, α4, 0) (0, α1, β1)

theorem k7Cyc_inj {α1 β1 α4 β6 : ℝ} (hα1 : 0 < α1) (hα4 : 0 < α4) (hβ6 : 0 < β6) :
    ∀ i j, k7Cyc α1 β1 α4 β6 i = k7Cyc α1 β1 α4 β6 j → i = j := by
  intro i j h
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [k7Cyc, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith [h.1, h.2.1, h.2.2]) | (exfalso; norm_num at h) |
      (exfalso; obtain ⟨h1, h2, h3⟩ := h; linarith)

set_option maxHeartbeats 3200000 in
theorem k7_cyc {D α1 β1 α4 β6 v1 v2 v3 : ℝ} (hD : 0 < D) (hα1 : 0 < α1) (hα4 : 0 < α4) (hβ6 : 0 < β6)
    (hv1 : 0 < v1) (hv2 : 0 < v2) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc D (k7Cyc α1 β1 α4 β6 (i + 1) - k7Cyc α1 β1 α4 β6 i) (k7Cyc α1 β1 α4 β6 j - k7Cyc α1 β1 α4 β6 i)
        (v1, v2, v3) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add_one
  have k1 := hD
  have ka1 := mul_pos hD hα1
  have ka4 := mul_pos hD hα4
  have kb6 := mul_pos hD hβ6
  have kv1 := mul_pos hD hv1
  have kv2 := mul_pos hD hv2
  have ka1v1 := mul_pos (mul_pos hD hα1) hv1
  have ka1v2 := mul_pos (mul_pos hD hα1) hv2
  have ka4v1 := mul_pos (mul_pos hD hα4) hv1
  have ka4v2 := mul_pos (mul_pos hD hα4) hv2
  have kb6v1 := mul_pos (mul_pos hD hβ6) hv1
  have kb6v2 := mul_pos (mul_pos hD hβ6) hv2
  have ka4b6v1 := mul_pos (mul_pos (mul_pos hD hα4) hβ6) hv1
  intro i j h1 h2'
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2' (by decide)).elim
    | (simp only [TSc, d3, k7Cyc, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 3200000 in
theorem k7_rest_d {D α1 β1 α4 β6 v1 v2 v3 : ℝ} (hD : 0 < D) (hα1 : 0 < α1) (hα4 : 0 < α4) (hβ6 : 0 < β6)
    (hv1 : 0 < v1) (hv2 : 0 < v2) :
    ∀ i : ZMod 5, TSc D (k7Cyc α1 β1 α4 β6 (i + 1) - k7Cyc α1 β1 α4 β6 i) ((0, 0, 0) - k7Cyc α1 β1 α4 β6 i)
      (v1, v2, v3) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add_one
  have k1 := hD
  have ka1 := mul_pos hD hα1
  have ka4 := mul_pos hD hα4
  have kb6 := mul_pos hD hβ6
  have kv1 := mul_pos hD hv1
  have kv2 := mul_pos hD hv2
  have ka1v1 := mul_pos (mul_pos hD hα1) hv1
  have ka1v2 := mul_pos (mul_pos hD hα1) hv2
  have ka4v1 := mul_pos (mul_pos hD hα4) hv1
  have kb6v1 := mul_pos (mul_pos hD hβ6) hv1
  have kb6v2 := mul_pos (mul_pos hD hβ6) hv2
  have ka4b6v1 := mul_pos (mul_pos (mul_pos hD hα4) hβ6) hv1
  intro i
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [TSc, d3, k7Cyc, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
     first
     | (left; nlinarith)
     | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 3200000 in
theorem k7_rest_a {D α1 β1 α4 β6 v1 v2 v3 : ℝ} (hD : 0 < D) (hα1 : 1 < α1) (hα4 : 0 < α4) (hβ6 : 0 < β6)
    (hβ1 : 0 < β1) (hv1 : 0 < v1) (hv2 : 0 < v2) :
    ∀ i : ZMod 5, TSc D (k7Cyc α1 β1 α4 β6 (i + 1) - k7Cyc α1 β1 α4 β6 i) ((0, 1, 0) - k7Cyc α1 β1 α4 β6 i)
      (v1, v2, v3) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add_one
  have hα1' : 0 < α1 := by linarith
  have hα11 : 0 < α1 - 1 := by linarith
  have k1 := hD
  have ka1 := mul_pos hD hα1'
  have ka11 := mul_pos hD hα11
  have ka4 := mul_pos hD hα4
  have kb6 := mul_pos hD hβ6
  have kv1 := mul_pos hD hv1
  have kv2 := mul_pos hD hv2
  have ka1v1 := mul_pos (mul_pos hD hα1') hv1
  have ka11v1 := mul_pos (mul_pos hD hα11) hv1
  have ka11v2 := mul_pos (mul_pos hD hα11) hv2
  have ka1v2 := mul_pos (mul_pos hD hα1') hv2
  have ka4v1 := mul_pos (mul_pos hD hα4) hv1
  have kb6v1 := mul_pos (mul_pos hD hβ6) hv1
  have kb6v2 := mul_pos (mul_pos hD hβ6) hv2
  have ka4b6v1 := mul_pos (mul_pos (mul_pos hD hα4) hβ6) hv1
  have kb1v1 := mul_pos (mul_pos hD hβ1) hv1
  intro i
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [TSc, d3, k7Cyc, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
     first
     | (left; nlinarith)
     | (right; refine ⟨by ring, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
