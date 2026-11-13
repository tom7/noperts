module

public import Minimality.Type08S.C2K6TDG

@[expose] public section


/-!
# K14 / A: lex peak lemmas for the H2 tie `ζ_{a-b'}(c, a') = 0` (pentagon and quadrilateral)
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

/-- Pentagon `(a, c', a', c, d)` (indices `0..4`) with the tie order `c <lex a' < c'` (depth), `c < d`,
and `c' < a` or `d < a`: unimodal (peaks only at `a`, `c'`, `d`; `c'`, `d` are not both peaks). -/
theorem k14_pent_uni (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h32 : LexLt (z 3, w 3) (z 2, w 2)) (h21 : z 2 < z 1) (h34 : z 3 < z 4)
    (h : z 1 < z 0 ∨ z 4 < z 0) : LexUni z w := by
  obtain ⟨M, hM⟩ := exists_key z w hinj
  refine lexUni_of_key z w (fun i => M * z i + w i) hinj hM ?_
  have lt : ∀ i j, z i < z j → M * z i + w i < M * z j + w j := fun i j h => (hM i j).1 (Or.inl h)
  have hk := k6m_key_inj z w hinj M hM
  refine k5d_uni_of_nopair (by decide) _ hk ?_
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_sub1
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  have k32 := (hM 3 2).1 h32
  have k21 := lt _ _ h21
  have k34 := lt _ _ h34
  have hh : M * z 1 + w 1 < M * z 0 + w 0 ∨ M * z 4 + w 4 < M * z 0 + w 0 := by
    rcases h with h | h
    · exact Or.inl (lt _ _ h)
    · exact Or.inr (lt _ _ h)
  intro i j h1 h2 h3 ⟨⟨pi1, pi2⟩, ⟨pj1, pj2⟩⟩
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact h1 rfl
    | exact h2 (by decide)
    | exact h3 (by decide)
    | (simp only [s0, s1, s2, s3, s4, f0, f1, f2, f3, f4] at pi1 pi2 pj1 pj2
       rcases hh with hh | hh <;> linarith)

/-- Quadrilateral `(b', c', a', c)` (indices `0..3`): `b' < c' < a'` (depth) is unimodal (no tie input). -/
theorem k14_quad_uni (z w : ZMod 4 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h01 : z 0 < z 1) (h12 : z 1 < z 2) : LexUni z w := by
  obtain ⟨M, hM⟩ := exists_key z w hinj
  refine lexUni_of_key z w (fun i => M * z i + w i) hinj hM ?_
  have lt : ∀ i j, z i < z j → M * z i + w i < M * z j + w j := fun i j h => (hM i j).1 (Or.inl h)
  have hk := k6m_key_inj z w hinj M hM
  refine k5d_uni_of_nopair (by decide) _ hk ?_
  obtain ⟨s0, s1, s2, s3⟩ := z4_sub1
  obtain ⟨f0, f1, f2, f3⟩ := z4_add
  have k01 := lt _ _ h01
  have k12 := lt _ _ h12
  intro i j h1 h2 h3 ⟨⟨pi1, pi2⟩, ⟨pj1, pj2⟩⟩
  rcases z4_cases i with rfl | rfl | rfl | rfl <;> rcases z4_cases j with rfl | rfl | rfl | rfl <;>
    first
    | exact h1 rfl
    | exact h2 (by decide)
    | exact h3 (by decide)
    | (simp only [s0, s1, s2, s3, f0, f1, f2, f3] at pi1 pi2 pj1 pj2
       linarith)

end C2
end Type08Sp
end Minimality
