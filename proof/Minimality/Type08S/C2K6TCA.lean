module

public import Minimality.Type08S.C2K6TBZ

@[expose] public section

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

set_option maxHeartbeats 6400000 in
/-- Lex part of the pentagon `(c',b',c,d,b) = k5dX1` at the TT tie `ζ(b',a') = 0`, `ζ(a,b') > 0`, `γ4 ≤ 1`,
using the facet `a'bc'` inequality `hF : α4(1-β1) + γ4(1-β6) < 1`. -/
theorem k6t3_c1_tt5b_real {α4 γ4 β1 β6 k0 U T B u t A : ℝ} (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hs : 1 < α4 + γ4)
    (hβ1 : 0 < β1) (hb6 : 0 < β6) (hγ41 : γ4 ≤ 1)
    (hA : 0 < A) (hB : 0 < B)
    (htie : α4 * u + γ4 * t = t - β6 * A) (hζ : α4 * u + γ4 * t < u)
    (hF : α4 * (1 - β1) + γ4 * (1 - β6) < 1)
    (hdep : ∀ i j : ZMod 5,
      k0 + (k5dX1 α4 γ4 β1 i).1 * U + (k5dX1 α4 γ4 β1 i).2.1 * T + (k5dX1 α4 γ4 β1 i).2.2 * B <
      k0 + (k5dX1 α4 γ4 β1 j).1 * U + (k5dX1 α4 γ4 β1 j).2.1 * T + (k5dX1 α4 γ4 β1 j).2.2 * B →
      (k5dX1 α4 γ4 β1 i).1 * u + (k5dX1 α4 γ4 β1 i).2.1 * t + (k5dX1 α4 γ4 β1 i).2.2 * A ≤
      (k5dX1 α4 γ4 β1 j).1 * u + (k5dX1 α4 γ4 β1 j).2.1 * t + (k5dX1 α4 γ4 β1 j).2.2 * A)
    (hinj : ∀ i j, k0 + (k5dX1 α4 γ4 β1 i).1 * U + (k5dX1 α4 γ4 β1 i).2.1 * T + (k5dX1 α4 γ4 β1 i).2.2 * B =
      k0 + (k5dX1 α4 γ4 β1 j).1 * U + (k5dX1 α4 γ4 β1 j).2.1 * T + (k5dX1 α4 γ4 β1 j).2.2 * B → i = j) :
    LexUni (fun _ => (0 : ℝ)) (fun i => k0 + (k5dX1 α4 γ4 β1 i).1 * U + (k5dX1 α4 γ4 β1 i).2.1 * T + (k5dX1 α4 γ4 β1 i).2.2 * B) := by
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  obtain ⟨s0, s1, s2, s3, s4⟩ := k5d_z5_sub
  refine k5d_uni_of_nopair (by decide) _ hinj ?_
  intro i j h1 h2 h3
  have p1 := mul_pos hα4 hβ1
  have p3 := mul_pos hβ1 hA
  have p4 := mul_pos hγ4 hA
  have p5 := mul_pos hb6 hA
  rintro ⟨⟨h5, h6⟩, h7, h8⟩
  have d5 := hdep _ _ h5
  have d6 := hdep _ _ h6
  have d7 := hdep _ _ h7
  have d8 := hdep _ _ h8
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2 (by decide)).elim
    | exact (h3 (by decide)).elim
    | (simp only [k5dX1_0, k5dX1_1, k5dX1_2, k5dX1_3, k5dX1_4, f0, f1, f2, f3, f4, s0, s1, s2, s3, s4] at d5 d6 d7 d8
       nlinarith)

end C2
end Type08Sp
end Minimality
