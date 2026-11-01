module

public import Minimality.Type08S.C2K5DD
public import Minimality.Type08S.C2K5DG4
public import Minimality.Type08S.C2K5DG3
public import Minimality.Type08S.C2K5DG5
public import Minimality.Type08S.C2K5DG6

@[expose] public section


/-!
# K5d / H: real lex parts of cells 3, 4, 5, 6, 8
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

theorem k5d_z6_sub : (0 : ZMod 6) - 1 = 5 ∧ (1 : ZMod 6) - 1 = 0 ∧ (2 : ZMod 6) - 1 = 1 ∧
    (3 : ZMod 6) - 1 = 2 ∧ (4 : ZMod 6) - 1 = 3 ∧ (5 : ZMod 6) - 1 = 4 := by decide

set_option maxHeartbeats 6400000 in
theorem k5d_c4_real {α4 γ4 β1 β6 γ6 k0 U T B : ℝ} (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hs : 1 < α4 + γ4) (hβ1 : 0 < β1) (hb6 : 0 < β6) (hB : 0 < B)
    (hα41 : α4 < 1) (hκ : α4 * (1 - β1) = 1 - γ4) (hTU : T < U) (hbc : α4 * U + γ4 * T < T)
    (hinj : ∀ i j, k0 + (k5dX4 α4 γ4 β1 β6 γ6 i).1 * U + (k5dX4 α4 γ4 β1 β6 γ6 i).2.1 * T + (k5dX4 α4 γ4 β1 β6 γ6 i).2.2 * B =
      k0 + (k5dX4 α4 γ4 β1 β6 γ6 j).1 * U + (k5dX4 α4 γ4 β1 β6 γ6 j).2.1 * T + (k5dX4 α4 γ4 β1 β6 γ6 j).2.2 * B → i = j) :
    LexUni (fun _ => (0 : ℝ)) (fun i => k0 + (k5dX4 α4 γ4 β1 β6 γ6 i).1 * U + (k5dX4 α4 γ4 β1 β6 γ6 i).2.1 * T + (k5dX4 α4 γ4 β1 β6 γ6 i).2.2 * B) := by
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  obtain ⟨s0, s1, s2, s3, s4⟩ := k5d_z5_sub
  refine k5d_uni_of_nopair (by decide) _ hinj ?_
  intro i j h1 h2 h3
  have hg : γ4 = 1 - α4 + α4 * β1 := by linarith
  subst hg
  have p1 := mul_pos hα4 hβ1
  have p2 := mul_pos hα4 hB
  have p3 := mul_pos hβ1 hB
  have p5 := mul_pos hγ4 hB
  have p6 := mul_pos (sub_pos.2 hs) hB
  have p7 := mul_pos hb6 hB
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2 (by decide)).elim
    | exact (h3 (by decide)).elim
    | (simp only [k5dX4_0, k5dX4_1, k5dX4_2, k5dX4_3, k5dX4_4, f0, f1, f2, f3, f4, s0, s1, s2, s3, s4]
       rintro ⟨⟨h5, h6⟩, h7, h8⟩
       first
       | nlinarith
       | nlinarith [mul_pos hα4 hγ4, mul_pos hα4 hB, mul_pos hγ4 hB, mul_pos hβ1 hB, mul_pos hb6 hB])

set_option maxHeartbeats 6400000 in
theorem k5d_c3_real {α4 γ4 β1 β6 γ6 k0 U T B : ℝ} (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hs : 1 < α4 + γ4) (hβ1 : 0 < β1) (hb6 : 0 < β6) (hγ6 : 0 < γ6) (hg61 : γ6 < 1)
    (hbg : 1 < β6 + γ6) (hB : 0 < B)
    (hα41 : α4 < 1) (hκ : α4 * (1 - β1) = 1 - γ4) (hTU : T < U) (hcb : T < α4 * U + γ4 * T)
    (hinj : ∀ i j, k0 + (k5dX3 α4 γ4 β1 β6 γ6 i).1 * U + (k5dX3 α4 γ4 β1 β6 γ6 i).2.1 * T + (k5dX3 α4 γ4 β1 β6 γ6 i).2.2 * B =
      k0 + (k5dX3 α4 γ4 β1 β6 γ6 j).1 * U + (k5dX3 α4 γ4 β1 β6 γ6 j).2.1 * T + (k5dX3 α4 γ4 β1 β6 γ6 j).2.2 * B → i = j) :
    LexUni (fun _ => (0 : ℝ)) (fun i => k0 + (k5dX3 α4 γ4 β1 β6 γ6 i).1 * U + (k5dX3 α4 γ4 β1 β6 γ6 i).2.1 * T + (k5dX3 α4 γ4 β1 β6 γ6 i).2.2 * B) := by
  obtain ⟨f0, f1, f2, f3, f4, f5⟩ := z6_add_one
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := k5d_z6_sub
  refine k5d_uni_of_nopair (by decide) _ hinj ?_
  intro i j h1 h2 h3
  have hg : γ4 = 1 - α4 + α4 * β1 := by linarith
  subst hg
  have p1 := mul_pos hα4 hβ1
  have p2 := mul_pos hα4 hB
  have p3 := mul_pos hβ1 hB
  have p5 := mul_pos hγ4 hB
  have p6 := mul_pos (sub_pos.2 hs) hB
  have p7 := mul_pos hb6 hB
  have p8 := mul_pos hγ6 hB
  have p9 := mul_pos (sub_pos.2 hg61) hB
  rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases z6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2 (by decide)).elim
    | exact (h3 (by decide)).elim
    | (simp only [k5dX3_0, k5dX3_1, k5dX3_2, k5dX3_3, k5dX3_4, k5dX3_5, f0, f1, f2, f3, f4, f5, s0, s1, s2, s3, s4, s5]
       rintro ⟨⟨h5, h6⟩, h7, h8⟩
       first
       | nlinarith
       | nlinarith [mul_pos hα4 hγ4, mul_pos hα4 hB, mul_pos hγ4 hB, mul_pos hβ1 hB, mul_pos hb6 hB])

set_option maxHeartbeats 6400000 in
theorem k5d_c5_real {α4 γ4 β1 β6 γ6 k0 U T B : ℝ} (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hs : 1 < α4 + γ4) (hβ1 : 0 < β1) (hb6 : 0 < β6) (hg6 : γ6 = 1) (hB : 0 < B)
    (hab : α4 * U + γ4 * T < U) (hba : T - β6 * B < α4 * U + γ4 * T)
    (hinj : ∀ i j, k0 + (k5dX5 α4 γ4 β1 β6 γ6 i).1 * U + (k5dX5 α4 γ4 β1 β6 γ6 i).2.1 * T + (k5dX5 α4 γ4 β1 β6 γ6 i).2.2 * B =
      k0 + (k5dX5 α4 γ4 β1 β6 γ6 j).1 * U + (k5dX5 α4 γ4 β1 β6 γ6 j).2.1 * T + (k5dX5 α4 γ4 β1 β6 γ6 j).2.2 * B → i = j) :
    LexUni (fun _ => (0 : ℝ)) (fun i => k0 + (k5dX5 α4 γ4 β1 β6 γ6 i).1 * U + (k5dX5 α4 γ4 β1 β6 γ6 i).2.1 * T + (k5dX5 α4 γ4 β1 β6 γ6 i).2.2 * B) := by
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  obtain ⟨s0, s1, s2, s3, s4⟩ := k5d_z5_sub
  refine k5d_uni_of_nopair (by decide) _ hinj ?_
  intro i j h1 h2 h3
  subst hg6
  have p1 := mul_pos hα4 hβ1
  have p2 := mul_pos hα4 hB
  have p3 := mul_pos hβ1 hB
  have p5 := mul_pos hγ4 hB
  have p6 := mul_pos (sub_pos.2 hs) hB
  have p7 := mul_pos hb6 hB
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2 (by decide)).elim
    | exact (h3 (by decide)).elim
    | (simp only [k5dX5_0, k5dX5_1, k5dX5_2, k5dX5_3, k5dX5_4, f0, f1, f2, f3, f4, s0, s1, s2, s3, s4]
       rintro ⟨⟨h5, h6⟩, h7, h8⟩
       first
       | nlinarith
       | nlinarith [mul_pos hα4 hγ4, mul_pos hα4 hB, mul_pos hγ4 hB, mul_pos hβ1 hB, mul_pos hb6 hB])

set_option maxHeartbeats 6400000 in
theorem k5d_c8_real {α4 γ4 β1 β6 γ6 k0 U T B : ℝ} (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hs : 1 < α4 + γ4) (hβ1 : 0 < β1) (hb6 : 0 < β6) (hg6 : γ6 = 1) (hB : 0 < B)
    (hab : U < α4 * U + γ4 * T) (hU0 : 0 < U)
    (hinj : ∀ i j, k0 + (k5dX5 α4 γ4 β1 β6 γ6 i).1 * U + (k5dX5 α4 γ4 β1 β6 γ6 i).2.1 * T + (k5dX5 α4 γ4 β1 β6 γ6 i).2.2 * B =
      k0 + (k5dX5 α4 γ4 β1 β6 γ6 j).1 * U + (k5dX5 α4 γ4 β1 β6 γ6 j).2.1 * T + (k5dX5 α4 γ4 β1 β6 γ6 j).2.2 * B → i = j) :
    LexUni (fun _ => (0 : ℝ)) (fun i => k0 + (k5dX5 α4 γ4 β1 β6 γ6 i).1 * U + (k5dX5 α4 γ4 β1 β6 γ6 i).2.1 * T + (k5dX5 α4 γ4 β1 β6 γ6 i).2.2 * B) := by
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  obtain ⟨s0, s1, s2, s3, s4⟩ := k5d_z5_sub
  refine k5d_uni_of_nopair (by decide) _ hinj ?_
  intro i j h1 h2 h3
  subst hg6
  have p1 := mul_pos hα4 hβ1
  have p2 := mul_pos hα4 hB
  have p3 := mul_pos hβ1 hB
  have p5 := mul_pos hγ4 hB
  have p6 := mul_pos (sub_pos.2 hs) hB
  have p7 := mul_pos hb6 hB
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2 (by decide)).elim
    | exact (h3 (by decide)).elim
    | (simp only [k5dX5_0, k5dX5_1, k5dX5_2, k5dX5_3, k5dX5_4, f0, f1, f2, f3, f4, s0, s1, s2, s3, s4]
       rintro ⟨⟨h5, h6⟩, h7, h8⟩
       first
       | nlinarith
       | nlinarith [mul_pos hα4 hγ4, mul_pos hα4 hB, mul_pos hγ4 hB, mul_pos hβ1 hB, mul_pos hb6 hB])

set_option maxHeartbeats 6400000 in
theorem k5d_c6_real {α4 γ4 β1 β6 γ6 k0 U T B : ℝ} (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hs : 1 < α4 + γ4) (hβ1 : 0 < β1) (hb6 : 0 < β6) (hg6 : γ6 = 1) (hB : 0 < B)
    (hab : α4 * U + γ4 * T < U) (hba : α4 * U + γ4 * T < T - β6 * B)
    (hinj : ∀ i j, k0 + (k5dX6 α4 γ4 β1 β6 γ6 i).1 * U + (k5dX6 α4 γ4 β1 β6 γ6 i).2.1 * T + (k5dX6 α4 γ4 β1 β6 γ6 i).2.2 * B =
      k0 + (k5dX6 α4 γ4 β1 β6 γ6 j).1 * U + (k5dX6 α4 γ4 β1 β6 γ6 j).2.1 * T + (k5dX6 α4 γ4 β1 β6 γ6 j).2.2 * B → i = j) :
    LexUni (fun _ => (0 : ℝ)) (fun i => k0 + (k5dX6 α4 γ4 β1 β6 γ6 i).1 * U + (k5dX6 α4 γ4 β1 β6 γ6 i).2.1 * T + (k5dX6 α4 γ4 β1 β6 γ6 i).2.2 * B) := by
  obtain ⟨f0, f1, f2, f3, f4, f5⟩ := z6_add_one
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := k5d_z6_sub
  refine k5d_uni_of_nopair (by decide) _ hinj ?_
  intro i j h1 h2 h3
  subst hg6
  have p1 := mul_pos hα4 hβ1
  have p2 := mul_pos hα4 hB
  have p3 := mul_pos hβ1 hB
  have p5 := mul_pos hγ4 hB
  have p6 := mul_pos (sub_pos.2 hs) hB
  have p7 := mul_pos hb6 hB
  rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases z6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2 (by decide)).elim
    | exact (h3 (by decide)).elim
    | (simp only [k5dX6_0, k5dX6_1, k5dX6_2, k5dX6_3, k5dX6_4, k5dX6_5, f0, f1, f2, f3, f4, f5, s0, s1, s2, s3, s4, s5]
       rintro ⟨⟨h5, h6⟩, h7, h8⟩
       first
       | nlinarith
       | nlinarith [mul_pos hα4 hγ4, mul_pos hα4 hB, mul_pos hγ4 hB, mul_pos hβ1 hB, mul_pos hb6 hB]
       | (have hU0 : 0 < U := by linarith
          have hT0 : 0 < T := by linarith
          rcases le_total U T with hle | hle <;>
          nlinarith [mul_nonneg hα4.le (sub_nonneg.2 hle), mul_nonneg hγ4.le (sub_nonneg.2 hle),
            mul_pos (sub_pos.2 hs) hU0, mul_pos (sub_pos.2 hs) hT0, mul_pos hb6 hB]))

end C2
end Type08Sp
end Minimality
