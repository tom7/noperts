module

public import Minimality.Type08S.C2K25Tie
public import Minimality.Type08S.C2K20HI
public import Minimality.Type08S.C2K14O
public import Minimality.Type08S.C2K17BA

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem k28bq_z5 (i : ZMod 5) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by revert i; decide
theorem k28bq_z5_add : (0 : ZMod 5) + 1 = 1 ∧ (1 : ZMod 5) + 1 = 2 ∧ (2 : ZMod 5) + 1 = 3 ∧
    (3 : ZMod 5) + 1 = 4 ∧ (4 : ZMod 5) + 1 = 0 := by decide

/-- R2.5 cycle (ccw in frame coordinates): `(c, b', c', b, a')`. frame origin `a`, `γ6 = β1 - β6`. -/
def k28bqCyc5 (α1 β1 β6 t : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  ![(1, -(α1 + β1 - 1), 0), (β1, 0, 0), (t * β1, 0, -β1), (t, -(α1 + β1 - 1), -1),
    (β6 * t + (β1 - β6), -(α1 * β1), -β6)]

/-- R2.4 cycle: `(a', c, b', c')`. -/
def k28bqCyc4 (α1 β1 β6 t : ℝ) : ZMod 4 → ℝ × ℝ × ℝ :=
  ![(β6 * t + (β1 - β6), -(α1 * β1), -β6), (1, -(α1 + β1 - 1), 0), (β1, 0, 0), (t * β1, 0, -β1)]

theorem k28bqCyc5_0 : k28bqCyc5 α1 β1 β6 t 0 = (1, -(α1 + β1 - 1), 0) := rfl
theorem k28bqCyc5_1 : k28bqCyc5 α1 β1 β6 t 1 = (β1, 0, 0) := rfl
theorem k28bqCyc5_2 : k28bqCyc5 α1 β1 β6 t 2 = (t * β1, 0, -β1) := rfl
theorem k28bqCyc5_3 : k28bqCyc5 α1 β1 β6 t 3 = (t, -(α1 + β1 - 1), -1) := rfl
theorem k28bqCyc5_4 : k28bqCyc5 α1 β1 β6 t 4 = (β6 * t + (β1 - β6), -(α1 * β1), -β6) := rfl
theorem k28bqCyc4_0 : k28bqCyc4 α1 β1 β6 t 0 = (β6 * t + (β1 - β6), -(α1 * β1), -β6) := rfl
theorem k28bqCyc4_1 : k28bqCyc4 α1 β1 β6 t 1 = (1, -(α1 + β1 - 1), 0) := rfl
theorem k28bqCyc4_2 : k28bqCyc4 α1 β1 β6 t 2 = (β1, 0, 0) := rfl
theorem k28bqCyc4_3 : k28bqCyc4 α1 β1 β6 t 3 = (t * β1, 0, -β1) := rfl

theorem k28bq_inj5 {α1 β1 β6 t : ℝ} (hα : 1 < α1) (hβ1 : 1 < β1) (hb6 : 0 < β6) (hg6 : 0 < β1 - β6)
    (ht : t < 0) :
    ∀ i j : ZMod 5, k28bqCyc5 α1 β1 β6 t i = k28bqCyc5 α1 β1 β6 t j → i = j := by
  intro i j h
  have e1 := congrArg Prod.fst h
  have e2 := congrArg (fun t => t.2.1) h
  have e3 := congrArg (fun t => t.2.2) h
  have p1 := mul_pos (sub_pos.2 hα) (sub_pos.2 hβ1)
  have p2 := mul_pos (by linarith : (0:ℝ) < α1) (by linarith : (0:ℝ) < β1)
  have p3 := mul_neg_of_neg_of_pos ht (by linarith : (0:ℝ) < β1)
  have p4 := mul_neg_of_pos_of_neg hb6 ht
  rcases k28bq_z5 i with rfl | rfl | rfl | rfl | rfl <;> rcases k28bq_z5 j with rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; simp only [k28bqCyc5_0, k28bqCyc5_1, k28bqCyc5_2, k28bqCyc5_3, k28bqCyc5_4] at e1 e2 e3; nlinarith)

theorem k28bq_inj4 {α1 β1 β6 t : ℝ} (hα : 1 < α1) (hβ1 : 1 < β1) (hb6 : 0 < β6) (hg6 : 0 < β1 - β6)
    (ht : t < 0) :
    ∀ i j : ZMod 4, k28bqCyc4 α1 β1 β6 t i = k28bqCyc4 α1 β1 β6 t j → i = j := by
  intro i j h
  have e1 := congrArg Prod.fst h
  have e2 := congrArg (fun t => t.2.1) h
  have e3 := congrArg (fun t => t.2.2) h
  have p1 := mul_pos (sub_pos.2 hα) (sub_pos.2 hβ1)
  have p2 := mul_pos (by linarith : (0:ℝ) < α1) (by linarith : (0:ℝ) < β1)
  have p3 := mul_neg_of_neg_of_pos ht (by linarith : (0:ℝ) < β1)
  have p4 := mul_neg_of_pos_of_neg hb6 ht
  rcases z4_cases i with rfl | rfl | rfl | rfl <;> rcases z4_cases j with rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; simp only [k28bqCyc4_0, k28bqCyc4_1, k28bqCyc4_2, k28bqCyc4_3] at e1 e2 e3; nlinarith)

set_option maxHeartbeats 3200000 in
theorem k28bq_tsc5 {α1 β1 β6 t v1 v2 : ℝ} (hα : 1 < α1) (hβ1 : 1 < β1) (hb6 : 0 < β6)
    (hg6 : 0 < β1 - β6) (hg1 : β1 - β6 < 1) (ht : t < 0) (hv2 : 0 < v2)
    (o1 : 0 < t * (α1 * β1 * (β1 - 1) - (α1 + β1 - 1) * (β1 - β6)) + (α1 + β1 - 1) * (β1 - β6))
    (o2 : t * ((α1 + β1 - 1) * β6) + α1 * β1 * (β1 - 1) - (α1 + β1 - 1) * β6 < 0) :
    (∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc 1 (k28bqCyc5 α1 β1 β6 t (i + 1) - k28bqCyc5 α1 β1 β6 t i)
        (k28bqCyc5 α1 β1 β6 t j - k28bqCyc5 α1 β1 β6 t i) (v1, v2, 0)) ∧
    (∀ x ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (0, -β1, 0)], ∀ i : ZMod 5,
      TSc 1 (k28bqCyc5 α1 β1 β6 t (i + 1) - k28bqCyc5 α1 β1 β6 t i)
        (x - k28bqCyc5 α1 β1 β6 t i) (v1, v2, 0)) := by
  obtain ⟨f0, f1, f2, f3, f4⟩ := k28bq_z5_add
  have e1 : 0 < β1 - 1 := by linarith
  have e2 : 0 < α1 - 1 := by linarith
  have a0 : 0 < α1 := by linarith
  have b0 : 0 < β1 := by linarith
  have nt : 0 < -t := by linarith
  have p1 := mul_pos e1 e2
  have p2 := mul_pos a0 b0
  have p3 := mul_pos nt b0
  have p4 := mul_pos nt hb6
  have p5 := mul_pos nt hg6
  have p6 := mul_pos nt e1
  have p7 := mul_pos nt e2
  have p8 := mul_pos hb6 hg6
  have p9 := mul_pos p2 e1
  have p10 := mul_pos p2 e2
  constructor
  · intro i j h1 h2
    rcases k28bq_z5 i with rfl | rfl | rfl | rfl | rfl <;>
      rcases k28bq_z5 j with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, k28bqCyc5_0, k28bqCyc5_1, k28bqCyc5_2, k28bqCyc5_3, k28bqCyc5_4, f0, f1, f2, f3, f4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
  · intro x hx i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;>
      rcases k28bq_z5 i with rfl | rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k28bqCyc5_0, k28bqCyc5_1, k28bqCyc5_2, k28bqCyc5_3, k28bqCyc5_4, f0, f1, f2, f3, f4,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 3200000 in
theorem k28bq_tsc4 {α1 β1 β6 t v1 v2 : ℝ} (hα : 1 < α1) (hβ1 : 1 < β1) (hb6 : 0 < β6)
    (hg6 : 0 < β1 - β6) (hg1 : β1 - β6 < 1) (ht : t < 0) (hv2 : 0 < v2)
    (o1 : t * (α1 * β1 * (β1 - 1) - (α1 + β1 - 1) * (β1 - β6)) + (α1 + β1 - 1) * (β1 - β6) < 0)
    (o2 : t * ((α1 + β1 - 1) * β6) + α1 * β1 * (β1 - 1) - (α1 + β1 - 1) * β6 < 0) :
    (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      TSc 1 (k28bqCyc4 α1 β1 β6 t (i + 1) - k28bqCyc4 α1 β1 β6 t i)
        (k28bqCyc4 α1 β1 β6 t j - k28bqCyc4 α1 β1 β6 t i) (v1, v2, 0)) ∧
    (∀ x ∈ [((0 : ℝ), (0 : ℝ), (0 : ℝ)), (0, -β1, 0), (t, -(α1 + β1 - 1), -1)], ∀ i : ZMod 4,
      TSc 1 (k28bqCyc4 α1 β1 β6 t (i + 1) - k28bqCyc4 α1 β1 β6 t i)
        (x - k28bqCyc4 α1 β1 β6 t i) (v1, v2, 0)) := by
  obtain ⟨f0, f1, f2, f3⟩ := z4_add
  have e1 : 0 < β1 - 1 := by linarith
  have e2 : 0 < α1 - 1 := by linarith
  have a0 : 0 < α1 := by linarith
  have b0 : 0 < β1 := by linarith
  have nt : 0 < -t := by linarith
  have p1 := mul_pos e1 e2
  have p2 := mul_pos a0 b0
  have p3 := mul_pos nt b0
  have p4 := mul_pos nt hb6
  have p5 := mul_pos nt hg6
  have p6 := mul_pos nt e1
  have p7 := mul_pos nt e2
  have p8 := mul_pos hb6 hg6
  have p9 := mul_pos p2 e1
  have p10 := mul_pos p2 e2
  constructor
  · intro i j h1 h2
    rcases z4_cases i with rfl | rfl | rfl | rfl <;>
      rcases z4_cases j with rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl h1
      | exact (h2 (by decide)).elim
      | (simp only [TSc, d3, k28bqCyc4_0, k28bqCyc4_1, k28bqCyc4_2, k28bqCyc4_3, f0, f1, f2, f3,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
         first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))
  · intro x hx i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;>
      rcases z4_cases i with rfl | rfl | rfl | rfl <;>
      (simp only [TSc, d3, k28bqCyc4_0, k28bqCyc4_1, k28bqCyc4_2, k28bqCyc4_3, f0, f1, f2, f3,
          Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first | (left; nlinarith) | (right; refine ⟨by ring, by nlinarith⟩))

end C2
end Type08Sp
end Minimality
