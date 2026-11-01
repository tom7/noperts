module

public import Minimality.Type08S.C2K5DC

@[expose] public section


/-!
# K5d / D: cell 1, real lex part (QPa version, with `κ_a`)
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

theorem k5d_z5_sub : (0 : ZMod 5) - 1 = 4 ∧ (1 : ZMod 5) - 1 = 0 ∧ (2 : ZMod 5) - 1 = 1 ∧
    (3 : ZMod 5) - 1 = 2 ∧ (4 : ZMod 5) - 1 = 3 := by decide

set_option maxHeartbeats 3200000 in
theorem k5d_c1_real_pa {α4 γ4 β1 k0 U T B : ℝ} (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hs : 1 < α4 + γ4)
    (hβ1 : 0 < β1) (hκ : α4 * (1 - β1) = 1 - γ4) (hB : 0 < B) (hUT : U < T)
    (hinj : ∀ i j, k0 + (k5dX1 α4 γ4 β1 i).1 * U + (k5dX1 α4 γ4 β1 i).2.1 * T + (k5dX1 α4 γ4 β1 i).2.2 * B =
      k0 + (k5dX1 α4 γ4 β1 j).1 * U + (k5dX1 α4 γ4 β1 j).2.1 * T + (k5dX1 α4 γ4 β1 j).2.2 * B → i = j) :
    LexUni (fun _ => (0 : ℝ))
      (fun i => k0 + (k5dX1 α4 γ4 β1 i).1 * U + (k5dX1 α4 γ4 β1 i).2.1 * T + (k5dX1 α4 γ4 β1 i).2.2 * B) := by
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  obtain ⟨s0, s1, s2, s3, s4⟩ := k5d_z5_sub
  refine k5d_uni_of_nopair (by decide) _ hinj ?_
  intro i j h1 h2 h3
  have hg : γ4 = 1 - α4 + α4 * β1 := by linarith
  subst hg
  have p1 := mul_pos hα4 hβ1
  have p2 := mul_pos hα4 hB
  have p3 := mul_pos hβ1 hB
  have p4 := mul_pos (mul_pos hα4 hβ1) hB
  have p5 := mul_pos hγ4 hB
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2 (by decide)).elim
    | exact (h3 (by decide)).elim
    | (simp only [k5dX1_0, k5dX1_1, k5dX1_2, k5dX1_3, k5dX1_4, f0, f1, f2, f3, f4, s0, s1, s2, s3, s4]
       rintro ⟨⟨h5, h6⟩, h7, h8⟩
       nlinarith)

set_option maxHeartbeats 3200000 in
theorem k5d_c1_real_tt {α4 γ4 β1 k0 U T B : ℝ} (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hs : 1 < α4 + γ4)
    (hβ1 : 0 < β1) (hB : 0 < B) (hU0 : U < 0) (hUb : U < α4 * U + γ4 * T)
    (hinj : ∀ i j, k0 + (k5dX1 α4 γ4 β1 i).1 * U + (k5dX1 α4 γ4 β1 i).2.1 * T + (k5dX1 α4 γ4 β1 i).2.2 * B =
      k0 + (k5dX1 α4 γ4 β1 j).1 * U + (k5dX1 α4 γ4 β1 j).2.1 * T + (k5dX1 α4 γ4 β1 j).2.2 * B → i = j) :
    LexUni (fun _ => (0 : ℝ))
      (fun i => k0 + (k5dX1 α4 γ4 β1 i).1 * U + (k5dX1 α4 γ4 β1 i).2.1 * T + (k5dX1 α4 γ4 β1 i).2.2 * B) := by
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  obtain ⟨s0, s1, s2, s3, s4⟩ := k5d_z5_sub
  refine k5d_uni_of_nopair (by decide) _ hinj ?_
  intro i j h1 h2 h3
  have p1 := mul_pos hα4 hβ1
  have p2 := mul_pos hα4 hB
  have p3 := mul_pos hβ1 hB
  have p5 := mul_pos hγ4 hB
  have p6 := mul_pos (sub_pos.2 hs) hB
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2 (by decide)).elim
    | exact (h3 (by decide)).elim
    | (simp only [k5dX1_0, k5dX1_1, k5dX1_2, k5dX1_3, k5dX1_4, f0, f1, f2, f3, f4, s0, s1, s2, s3, s4]
       rintro ⟨⟨h5, h6⟩, h7, h8⟩
       first
       | nlinarith
       | (have hT0 : T < 0 := by linarith
          rcases le_total U T with hle | hle <;>
          nlinarith [mul_nonneg hα4.le (sub_nonneg.2 hle), mul_nonneg hγ4.le (sub_nonneg.2 hle),
            mul_pos (sub_pos.2 hs) (neg_pos.2 hT0), mul_pos (sub_pos.2 hs) (neg_pos.2 hU0)]))

end C2
end Type08Sp
end Minimality
