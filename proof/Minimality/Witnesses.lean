module

public import Minimality.L8T3
public import Minimality.L8T4
public import Minimality.OctahedronAll
public import Minimality.Planar

@[expose] public section

/-!
# Non-vacuity witnesses

Explicit rational examples showing that every hypothesis structure of the
headline theorems can be satisfied.
-/

namespace Minimality

/-- Numeric evaluation of explicit vectors. -/
local macro "wnum" : tactic => `(tactic| ((try simp [Matrix.cons_val]) <;> norm_num))

open scoped RealInnerProductSpace
open Finset

/-- The affine functional `x ↦ ⟪n, x⟫ + c`. -/
noncomputable def affOf (n : ℝ³) (c : ℝ) : ℝ³ →ᵃ[ℝ] ℝ :=
  (innerₛₗ ℝ n).toAffineMap + AffineMap.const ℝ ℝ³ c

@[simp] theorem affOf_apply (n x : ℝ³) (c : ℝ) :
    affOf n c x = n 0 * x 0 + n 1 * x 1 + n 2 * x 2 + c := by
  simp [affOf, PiLp.inner_apply, Fin.sum_univ_three]; ring

/-- Four points with nonzero orientation determinant are affinely independent. -/
theorem affineIndependent_of_det3 {a b c d : ℝ³} (h : det3 (b - a) (c - a) (d - a) ≠ 0) :
    AffineIndependent ℝ ![a, b, c, d] := by
  rw [affineIndependent_iff_of_fintype]
  intro w hw hs
  rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ w _ hw a,
    Finset.weightedVSubOfPoint_apply, Fin.sum_univ_four] at hs
  have hc : cmb (b - a) (c - a) (d - a) (w 1) (w 2) (w 3) = 0 := by
    simpa [cmb] using hs
  obtain ⟨h1, h2, h3⟩ := cmb_eq_zero h hc
  rw [Fin.sum_univ_four] at hw
  intro i; fin_cases i <;> simp <;> linarith

/-- A bicapped tetrahedron (hypothesis of `isRupert_bicappedTetrahedron`). -/
theorem witness_bicappedTetrahedron : IsBicappedTetrahedron !₂[0, 0, 0] !₂[4, 0, 0] !₂[0, 4, 0] !₂[0, 0, 4] !₂[-3, 2, 1] !₂[2, -1, 1] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply List.Nodup.of_map (fun v : ℝ³ => (v 0, v 1, v 2))
    simp [List.nodup_cons, Matrix.cons_val] <;> norm_num
  · apply affineIndependent_of_det3
    simp only [det3, cross, PiLp.inner_apply, Fin.sum_univ_three, PiLp.sub_apply,
      RCLike.inner_apply, conj_trivial]
    simp [Matrix.cons_val] <;> norm_num
  · refine ⟨affOf !₂[-1, 0, -3] (0), by wnum, by wnum, by wnum, ?_⟩
    intro x hx h1 h2 h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl ‹_› | wnum
  · refine ⟨affOf !₂[-1, 3, 3] (-12), by wnum, by wnum, by wnum, ?_⟩
    intro x hx h1 h2 h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl ‹_› | wnum
  · refine ⟨affOf !₂[-2, -3, 0] (0), by wnum, by wnum, by wnum, ?_⟩
    intro x hx h1 h2 h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl ‹_› | wnum
  · refine ⟨affOf !₂[0, -1, -1] (0), by wnum, by wnum, by wnum, ?_⟩
    intro x hx h1 h2 h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl ‹_› | wnum
  · refine ⟨affOf !₂[1, -1, 1] (-4), by wnum, by wnum, by wnum, ?_⟩
    intro x hx h1 h2 h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl ‹_› | wnum
  · refine ⟨affOf !₂[-1, -2, 0] (0), by wnum, by wnum, by wnum, ?_⟩
    intro x hx h1 h2 h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl ‹_› | wnum
  · refine ⟨affOf !₂[0, 0, -1] (0), by wnum, by wnum, by wnum, ?_⟩
    intro x hx h1 h2 h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl ‹_› | wnum
  · refine ⟨affOf !₂[1, 1, 1] (-4), by wnum, by wnum, by wnum, ?_⟩
    intro x hx h1 h2 h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl ‹_› | wnum

/-- A generic capped square pyramid (T5), `S₁S₄ ∦ S₂S₃`. -/
theorem witness_cappedSquarePyramid : IsCappedSquarePyramid !₂[1, 1, 4] !₂[0, 0, 0] !₂[4, 0, 0] !₂[3, 3, 0] !₂[0, 2, 0] !₂[1, -4, 1] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply List.Nodup.of_map (fun v : ℝ³ => (v 0, v 1, v 2))
    simp [List.nodup_cons, Matrix.cons_val] <;> norm_num
  · apply affineIndependent_of_det3
    simp only [det3, cross, PiLp.inner_apply, Fin.sum_univ_three, PiLp.sub_apply,
      RCLike.inner_apply, conj_trivial]
    simp [Matrix.cons_val] <;> norm_num
  · refine ⟨affOf !₂[0, 0, -1] (0), ?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> wnum
    · intro x hx hxF
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · wnum
      · exact (hxF (by simp only [Finset.mem_insert, Finset.mem_singleton, true_or])).elim
      · exact (hxF (by simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true])).elim
      · exact (hxF (by simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true])).elim
      · exact (hxF (by simp only [Finset.mem_insert, Finset.mem_singleton, or_true])).elim
      · wnum
  · refine ⟨affOf !₂[3, 1, 2] (-12), by wnum, by wnum, by wnum, ?_⟩
    intro x hx h1 h2 h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl ‹_› | wnum
  · refine ⟨affOf !₂[-1, 3, 1] (-6), by wnum, by wnum, by wnum, ?_⟩
    intro x hx h1 h2 h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl ‹_› | wnum
  · refine ⟨affOf !₂[-4, 0, 1] (0), by wnum, by wnum, by wnum, ?_⟩
    intro x hx h1 h2 h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl ‹_› | wnum
  · refine ⟨affOf !₂[-17, -3, 5] (0), by wnum, by wnum, by wnum, ?_⟩
    intro x hx h1 h2 h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl ‹_› | wnum
  · refine ⟨affOf !₂[0, -1, -4] (0), by wnum, by wnum, by wnum, ?_⟩
    intro x hx h1 h2 h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl ‹_› | wnum
  · refine ⟨affOf !₂[17, -9, 15] (-68), by wnum, by wnum, by wnum, ?_⟩
    intro x hx h1 h2 h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl ‹_› | wnum

/-- A capped square pyramid with `S₁S₄ ∥ S₂S₃` (the L6 exception, Theorem 8.2). -/
theorem witness_cappedSquarePyramid_parallel : IsCappedSquarePyramid !₂[2, 2, 4] !₂[0, 0, 0] !₂[4, 0, 0] !₂[4, 4, 0] !₂[0, 4, 0] !₂[1, -4, 1] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply List.Nodup.of_map (fun v : ℝ³ => (v 0, v 1, v 2))
    simp [List.nodup_cons, Matrix.cons_val] <;> norm_num
  · apply affineIndependent_of_det3
    simp only [det3, cross, PiLp.inner_apply, Fin.sum_univ_three, PiLp.sub_apply,
      RCLike.inner_apply, conj_trivial]
    simp [Matrix.cons_val] <;> norm_num
  · refine ⟨affOf !₂[0, 0, -1] (0), ?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> wnum
    · intro x hx hxF
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · wnum
      · exact (hxF (by simp only [Finset.mem_insert, Finset.mem_singleton, true_or])).elim
      · exact (hxF (by simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true])).elim
      · exact (hxF (by simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true])).elim
      · exact (hxF (by simp only [Finset.mem_insert, Finset.mem_singleton, or_true])).elim
      · wnum
  · refine ⟨affOf !₂[2, 0, 1] (-8), by wnum, by wnum, by wnum, ?_⟩
    intro x hx h1 h2 h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl ‹_› | wnum
  · refine ⟨affOf !₂[0, 2, 1] (-8), by wnum, by wnum, by wnum, ?_⟩
    intro x hx h1 h2 h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl ‹_› | wnum
  · refine ⟨affOf !₂[-2, 0, 1] (0), by wnum, by wnum, by wnum, ?_⟩
    intro x hx h1 h2 h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl ‹_› | wnum
  · refine ⟨affOf !₂[-9, -1, 5] (0), by wnum, by wnum, by wnum, ?_⟩
    intro x hx h1 h2 h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl ‹_› | wnum
  · refine ⟨affOf !₂[0, -1, -4] (0), by wnum, by wnum, by wnum, ?_⟩
    intro x hx h1 h2 h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl ‹_› | wnum
  · refine ⟨affOf !₂[9, -5, 7] (-36), by wnum, by wnum, by wnum, ?_⟩
    intro x hx h1 h2 h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl ‹_› | wnum

/-- A T4 (hypothesis of `isRupert_T4`). -/
theorem witness_T4 : IsT4 !₂[0, 0, 0] !₂[4, 0, 0] !₂[0, 4, 0] !₂[0, 0, 4] !₂[-8, 4, 2] !₂[4, -2, 1] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply List.Nodup.of_map (fun v : ℝ³ => (v 0, v 1, v 2))
    simp [List.nodup_cons, Matrix.cons_val] <;> norm_num
  · apply affineIndependent_of_det3
    simp only [det3, cross, PiLp.inner_apply, Fin.sum_univ_three, PiLp.sub_apply,
      RCLike.inner_apply, conj_trivial]
    simp [Matrix.cons_val] <;> norm_num
  · refine ⟨affOf !₂[-1, -2, 0] (0), ?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> wnum
    · intro x hx hxF
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact (hxF (by simp only [Finset.mem_insert, Finset.mem_singleton, true_or])).elim
      · wnum
      · wnum
      · exact (hxF (by simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true])).elim
      · exact (hxF (by simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true])).elim
      · exact (hxF (by simp only [Finset.mem_insert, Finset.mem_singleton, or_true])).elim
  · refine ⟨affOf !₂[-1, 0, -4] (0), by wnum, by wnum, by wnum, ?_⟩
    intro x hx h1 h2 h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl ‹_› | wnum
  · refine ⟨affOf !₂[1, 4, 4] (-16), by wnum, by wnum, by wnum, ?_⟩
    intro x hx h1 h2 h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl ‹_› | wnum
  · refine ⟨affOf !₂[0, -1, -2] (0), by wnum, by wnum, by wnum, ?_⟩
    intro x hx h1 h2 h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl ‹_› | wnum
  · refine ⟨affOf !₂[2, 1, 2] (-8), by wnum, by wnum, by wnum, ?_⟩
    intro x hx h1 h2 h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl ‹_› | wnum
  · refine ⟨affOf !₂[0, 0, -1] (0), by wnum, by wnum, by wnum, ?_⟩
    intro x hx h1 h2 h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl ‹_› | wnum
  · refine ⟨affOf !₂[1, 1, 1] (-4), by wnum, by wnum, by wnum, ?_⟩
    intro x hx h1 h2 h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl ‹_› | wnum

/-- A generic T3 (hypothesis of `isRupert_T3`). -/
theorem witness_T3 : IsT3 !₂[2, 0, 0] !₂[0, 2, 0] !₂[0, 0, 0] !₂[1, 0, 4] !₂[0, 4, 2] !₂[0, 0, 2] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply List.Nodup.of_map (fun v : ℝ³ => (v 0, v 1, v 2))
    simp [List.nodup_cons, Matrix.cons_val] <;> norm_num
  · apply affineIndependent_of_det3
    simp only [det3, cross, PiLp.inner_apply, Fin.sum_univ_three, PiLp.sub_apply,
      RCLike.inner_apply, conj_trivial]
    simp [Matrix.cons_val] <;> norm_num
  · refine ⟨affOf !₂[0, -1, 0] (0), ?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> wnum
    · intro x hx hxF
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact (hxF (by simp only [Finset.mem_insert, Finset.mem_singleton, true_or])).elim
      · wnum
      · exact (hxF (by simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true])).elim
      · exact (hxF (by simp only [Finset.mem_insert, Finset.mem_singleton, or_true])).elim
      · wnum
      · exact (hxF (by simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true])).elim
  · refine ⟨affOf !₂[-1, 0, 0] (0), ?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> wnum
    · intro x hx hxF
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · wnum
      · exact (hxF (by simp only [Finset.mem_insert, Finset.mem_singleton, true_or])).elim
      · exact (hxF (by simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true])).elim
      · wnum
      · exact (hxF (by simp only [Finset.mem_insert, Finset.mem_singleton, or_true])).elim
      · exact (hxF (by simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true])).elim
  · refine ⟨affOf !₂[0, 0, -1] (0), by wnum, by wnum, by wnum, ?_⟩
    intro x hx h1 h2 h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl ‹_› | wnum
  · refine ⟨affOf !₂[-2, 0, 1] (-2), by wnum, by wnum, by wnum, ?_⟩
    intro x hx h1 h2 h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl ‹_› | wnum
  · refine ⟨affOf !₂[1, 1, -1] (-2), by wnum, by wnum, by wnum, ?_⟩
    intro x hx h1 h2 h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl ‹_› | wnum
  · refine ⟨affOf !₂[8, 3, 2] (-16), by wnum, by wnum, by wnum, ?_⟩
    intro x hx h1 h2 h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl ‹_› | wnum

/-- A T3 with `BB' ∥ CC'` (the degenerate case of Theorem 8.4). -/
theorem witness_T3_parallel : IsT3 !₂[2, 0, 0] !₂[0, 2, 0] !₂[0, 0, 0] !₂[1, 0, 4] !₂[0, 2, 2] !₂[0, 0, 2] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply List.Nodup.of_map (fun v : ℝ³ => (v 0, v 1, v 2))
    simp [List.nodup_cons, Matrix.cons_val] <;> norm_num
  · apply affineIndependent_of_det3
    simp only [det3, cross, PiLp.inner_apply, Fin.sum_univ_three, PiLp.sub_apply,
      RCLike.inner_apply, conj_trivial]
    simp [Matrix.cons_val] <;> norm_num
  · refine ⟨affOf !₂[0, -1, 0] (0), ?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> wnum
    · intro x hx hxF
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact (hxF (by simp only [Finset.mem_insert, Finset.mem_singleton, true_or])).elim
      · wnum
      · exact (hxF (by simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true])).elim
      · exact (hxF (by simp only [Finset.mem_insert, Finset.mem_singleton, or_true])).elim
      · wnum
      · exact (hxF (by simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true])).elim
  · refine ⟨affOf !₂[-1, 0, 0] (0), ?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> wnum
    · intro x hx hxF
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · wnum
      · exact (hxF (by simp only [Finset.mem_insert, Finset.mem_singleton, true_or])).elim
      · exact (hxF (by simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true])).elim
      · wnum
      · exact (hxF (by simp only [Finset.mem_insert, Finset.mem_singleton, or_true])).elim
      · exact (hxF (by simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true])).elim
  · refine ⟨affOf !₂[0, 0, -1] (0), by wnum, by wnum, by wnum, ?_⟩
    intro x hx h1 h2 h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl ‹_› | wnum
  · refine ⟨affOf !₂[-2, 0, 1] (-2), by wnum, by wnum, by wnum, ?_⟩
    intro x hx h1 h2 h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl ‹_› | wnum
  · refine ⟨affOf !₂[1, 1, 0] (-2), by wnum, by wnum, by wnum, ?_⟩
    intro x hx h1 h2 h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl ‹_› | wnum
  · refine ⟨affOf !₂[4, 3, 1] (-8), by wnum, by wnum, by wnum, ?_⟩
    intro x hx h1 h2 h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl ‹_› | wnum

/-- A nearly regular octahedron (hypothesis of `isRupert_octahedron_conditionA`). -/
theorem witness_octahedron : IsOctahedron !₂[0, 0, 10] !₂[0, 0, -10] !₂[10, 0, 1] !₂[-10, 0, -1] !₂[0, 10, 1] !₂[0, -10, -1] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply List.Nodup.of_map (fun v : ℝ³ => (v 0, v 1, v 2))
    simp [List.nodup_cons, Matrix.cons_val] <;> norm_num
  · refine ⟨affOf !₂[9, 9, 10] (-100), by wnum, by wnum, by wnum, ?_⟩
    intro x hx h1 h2 h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl ‹_› | wnum
  · refine ⟨affOf !₂[9, -11, 10] (-100), by wnum, by wnum, by wnum, ?_⟩
    intro x hx h1 h2 h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl ‹_› | wnum
  · refine ⟨affOf !₂[-11, 9, 10] (-100), by wnum, by wnum, by wnum, ?_⟩
    intro x hx h1 h2 h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl ‹_› | wnum
  · refine ⟨affOf !₂[-11, -11, 10] (-100), by wnum, by wnum, by wnum, ?_⟩
    intro x hx h1 h2 h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl ‹_› | wnum
  · refine ⟨affOf !₂[11, 11, -10] (-100), by wnum, by wnum, by wnum, ?_⟩
    intro x hx h1 h2 h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl ‹_› | wnum
  · refine ⟨affOf !₂[11, -9, -10] (-100), by wnum, by wnum, by wnum, ?_⟩
    intro x hx h1 h2 h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl ‹_› | wnum
  · refine ⟨affOf !₂[-9, 11, -10] (-100), by wnum, by wnum, by wnum, ?_⟩
    intro x hx h1 h2 h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl ‹_› | wnum
  · refine ⟨affOf !₂[-9, -9, -10] (-100), by wnum, by wnum, by wnum, ?_⟩
    intro x hx h1 h2 h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl ‹_› | wnum

/-- Theorem 9.9 applied to the witness octahedron. -/
theorem witness_octahedron_rupert :
    IsRupert {!₂[0, 0, 10], !₂[0, 0, -10], !₂[10, 0, 1], !₂[-10, 0, -1], !₂[0, 10, 1],
      !₂[0, -10, -1]} :=
  isRupert_octahedron witness_octahedron

/-- Condition A holds for `witness_octahedron`. -/
theorem witness_conditionA :
    let a : ℝ³ := !₂[0, 0, 10]; let a' : ℝ³ := !₂[0, 0, -10]
    let b : ℝ³ := !₂[10, 0, 1]; let b' : ℝ³ := !₂[-10, 0, -1]
    let c : ℝ³ := !₂[0, 10, 1]; let c' : ℝ³ := !₂[0, -10, -1]
    max (min ⟪a - a', b⟫ ⟪a - a', b'⟫) (min ⟪a - a', c⟫ ⟪a - a', c'⟫) <
      min (max ⟪a - a', b⟫ ⟪a - a', b'⟫) (max ⟪a - a', c⟫ ⟪a - a', c'⟫) := by
  intro a a' b b' c c'
  have e : ∀ x : ℝ³, ⟪a - a', x⟫ = 20 * x 2 := fun x => by
    simp only [a, a', PiLp.inner_apply, Fin.sum_univ_three, PiLp.sub_apply, RCLike.inner_apply,
      conj_trivial]
    simp [Matrix.cons_val]; ring
  rw [e, e, e, e]
  simp only [b, b', c, c']
  simp [Matrix.cons_val]

/-- The witness T5 of the exceptional case has `S₁S₄ ∥ S₂S₃`. -/
theorem witness_cappedSquarePyramid_parallel_par :
    (!₂[0, 4, 0] : ℝ³) - !₂[0, 0, 0] = (1 : ℝ) • ((!₂[4, 4, 0] : ℝ³) - !₂[4, 0, 0]) := by
  ext i; fin_cases i <;> wnum

/-- The witness T5 of the generic case has `S₁S₄ ∦ S₂S₃`. -/
theorem witness_cappedSquarePyramid_not_par (k : ℝ) :
    (!₂[0, 2, 0] : ℝ³) - !₂[0, 0, 0] ≠ k • ((!₂[3, 3, 0] : ℝ³) - !₂[4, 0, 0]) := by
  intro h
  have h0 := congrArg (· 0) h; have h1 := congrArg (· 1) h
  simp at h0 h1
  rcases h0 with h0 | h0
  · norm_num [h0] at h1
  · norm_num at h0

/-- The witness T3 of the degenerate case has `BB' ∥ CC'`. -/
theorem witness_T3_parallel_par :
    (!₂[0, 2, 2] : ℝ³) - !₂[0, 2, 0] = (1 : ℝ) • ((!₂[0, 0, 2] : ℝ³) - !₂[0, 0, 0]) := by
  ext i; fin_cases i <;> wnum

/-! The headline theorems apply to the witnesses. -/

example := isRupert_bicappedTetrahedron witness_bicappedTetrahedron
example := isRupert_cappedSquarePyramid witness_cappedSquarePyramid
  witness_cappedSquarePyramid_not_par
example := isRupert_cappedSquarePyramid_all witness_cappedSquarePyramid_parallel
example := isRupert_T4 witness_T4
example := isRupert_T3 witness_T3
example := isRupert_T3 witness_T3_parallel
example := isRupert_octahedron_conditionA witness_octahedron witness_conditionA

/-! Flat sets: a square is Rupert, a single point is not. -/

/-- The unit square in the plane `z = 0` (four coplanar, non-collinear points)
is Rupert. -/
example : IsRupert {!₂[0, 0, 0], !₂[1, 0, 0], !₂[1, 1, 0], !₂[0, 1, 0]} := by
  apply isRupert_of_coplanar_of_not_collinear
  · refine coplanar_of_plane (N := ez) (by simp [ez]) (c := 0) fun x hx => ?_
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp [ez, PiLp.inner_apply]
  · intro hcol
    rw [collinear_iff_of_mem (p₀ := !₂[0, 0, 0]) (by simp)] at hcol
    obtain ⟨v, hv⟩ := hcol
    obtain ⟨r₁, h₁⟩ := hv !₂[1, 0, 0] (by simp)
    obtain ⟨r₂, h₂⟩ := hv !₂[0, 1, 0] (by simp)
    have a0 := congrArg (· 0) h₁
    have a1 := congrArg (· 1) h₁
    have b1 := congrArg (· 1) h₂
    simp only [vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at a0 a1 b1
    simp at a0 a1 b1
    have hr₁ : r₁ ≠ 0 := by rintro rfl; simp at a0
    have hv1 : v 1 = 0 := a1.resolve_left hr₁
    rw [hv1, mul_zero] at b1
    exact one_ne_zero b1

/-- A single point is not Rupert. -/
example (p : ℝ³) : ¬ IsRupert {p} :=
  not_isRupert_of_collinear {p} (by simp [collinear_singleton]) (Finset.singleton_nonempty p)

end Minimality

end
