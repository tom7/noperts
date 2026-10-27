module

public import Minimality.Arc016

@[expose] public section


namespace Minimality
open scoped RealInnerProductSpace
open Finset

namespace Arc016Witness

noncomputable def ea : ℝ³ := !₂[1, 0, 0]
noncomputable def eb : ℝ³ := !₂[-1/4, 1, 0]
noncomputable def ec : ℝ³ := !₂[-1/4, -1/4, 1]
noncomputable def fp (a b c : ℝ) : ℝ³ := a • ea + b • eb + c • ec
noncomputable def P3 : ℝ³ := fp (1/5) (107/10) 8
noncomputable def P4 : ℝ³ := fp (7/10) (16/5) (31/10)
noncomputable def P5 : ℝ³ := fp (9/10) (19/10) (4/5)
noncomputable def dA : ℝ³ := (1/5 : ℝ) • ea + (177/10 : ℝ) • ec
noncomputable def dB : ℝ³ := (9/5 : ℝ) • ea + (4/5 : ℝ) • ec

noncomputable def P2 : ℝ³ := eb

/-- The 7 vertices `X0 = e_a, X1 = 0, X2 = e_b, X3, X4, X5, X6 = e_c`. -/
noncomputable def V : Finset ℝ³ := {ea, 0, eb, P3, P4, P5, ec}

noncomputable def X : ZMod 4 → ℝ³ := quad ea P5 P3 ec

local macro "numtac" : tactic =>
  `(tactic| (simp [EndsPos, det3_expand, P5, P3, P4, fp, ea, eb, ec, dA, dB, X, quad_0, quad_1,
    quad_2, quad_3, PiLp.inner_apply, Fin.sum_univ_three, cross_apply_zero, cross_apply_one,
    cross_apply_two] <;> norm_num))

theorem ea_ne : ea ≠ 0 := fun h => by
  have := congrArg (fun v : ℝ³ => v 0) h; simp [ea] at this
theorem ec_ne : ec ≠ 0 := fun h => by
  have := congrArg (fun v : ℝ³ => v 2) h; simp [ec] at this
theorem P3_ne : P3 ≠ 0 := fun h => by
  have := congrArg (fun v : ℝ³ => v 2) h; simp [P3, fp, ea, eb, ec] at this
theorem P5_ne : P5 ≠ 0 := fun h => by
  have := congrArg (fun v : ℝ³ => v 2) h; simp [P5, fp, ea, eb, ec] at this

theorem X_mem (i : ZMod 4) : X i ∈ V := by
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> simp [X, V, quad_0, quad_1, quad_2, quad_3]

/-- **The arc of 016 of the type-24 class R4_4** (rounded to one decimal; frame
`e_a = (1,0,0)`, `e_b = (-1/4,1,0)`, `e_c = (-1/4,-1/4,1)`, all `G_ij < 0`,
positively oriented): `(X0, X5, X3, X6)`, front diagonal 03, middle `X1 = 0` over the chord 06. -/
noncomputable def arc : Arc V where
  x := X
  da := dA
  db := dB
  M := {0}
  n := cross ea ec
  hxV := X_mem
  hxM := by
    intro i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp [X, quad_0, quad_1, quad_2, quad_3, ea_ne, ec_ne, P3_ne, P5_ne]
  hn_a := by numtac
  hn_b := by numtac
  hcyc := by
    obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
    intro i j hi hj
    rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [a0, a1, a2, a3] <;> numtac
  hrest := by
    obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
    intro y hy hyM hyx i
    simp only [V, mem_insert, mem_singleton] at hy hyM
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp [X, quad_0, quad_1, quad_2, quad_3])).elim
    · exact absurd rfl hyM
    · rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> simp only [a0, a1, a2, a3] <;> numtac
    · exact (hyx 2 (by simp [X, quad_0, quad_1, quad_2, quad_3])).elim
    · rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> simp only [a0, a1, a2, a3] <;> numtac
    · exact (hyx 1 (by simp [X, quad_0, quad_1, quad_2, quad_3])).elim
    · exact (hyx 3 (by simp [X, quad_0, quad_1, quad_2, quad_3])).elim
  hfront := by numtac
  hmid := by
    obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
    intro m hm
    rw [mem_singleton] at hm
    subst hm
    refine ⟨3, 1, Or.inl rfl, ?_⟩
    simp only [a3]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> numtac

theorem arc_x : arc.x = ![ea, P5, P3, ec] := rfl

/-- **Non-vacuity of Proposition 33.3**: all its hypotheses (the arc `(a)`, `(b)`, the obtuse
octant) hold for this concrete realization of the class, except (E2), kept as a hypothesis. -/
theorem witness_prop33_3 (hnd : arc.NoHDNNearEnds) :
    IsRupert V ∨
      (⟪ea - ec, (1/5 : ℝ) • ea + (177/10 : ℝ) • ec⟫ = 0 ∧
        ⟪P3 - P5, (9/5 : ℝ) • ea + (4/5 : ℝ) • ec⟫ = 0 ∧
        ((-423/20 : ℝ) < 0 → ⟪ea - ec, (9/5 : ℝ) • ea + (4/5 : ℝ) • ec⟫ = 0) ∧
        ⟪ea, eb⟫ = 0 ∧ ⟪eb, ec⟫ = 0 ∧ (1 < (9/10 : ℝ) + 19/10 + 4/5 → ⟪ea, ec⟫ = 0)) := by
  refine prop33_3 (V := V) ea eb ec P3 P5 (1/5) (107/10) 8 (9/10) (19/10) (4/5) (177/10) (9/5)
    (-317/10) (13/2) (-423/20) (by simp [P3, fp]) (by simp [P5, fp]) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) arc arc_x rfl rfl rfl (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_
    hnd
  all_goals simp [ea, eb, ec, PiLp.inner_apply, Fin.sum_univ_three] <;> norm_num

end Arc016Witness
end Minimality
