module

public import Minimality.Type08S.C2K6MI

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped RealInnerProductSpace Topology
open Finset Filter
namespace Minimality
namespace Type08Sp
namespace C2

/-- Keys of lex pairs: total, injective on distinct pairs. -/
theorem k6m_key_inj {k : ℕ} [NeZero k] (z w : ZMod k → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j) (M : ℝ)
    (hM : ∀ i j, LexLt (z i, w i) (z j, w j) ↔ M * z i + w i < M * z j + w j) :
    ∀ i j, M * z i + w i = M * z j + w j → i = j := by
  intro i j h
  by_contra hij
  have hne : (z i, w i) ≠ (z j, w j) := fun e => hij (hinj i j (congrArg Prod.fst e) (congrArg Prod.snd e))
  have ht : LexLt (z i, w i) (z j, w j) ∨ LexLt (z j, w j) (z i, w i) := by
    simp only [LexLt]
    rcases lt_trichotomy (z i) (z j) with h1 | h1 | h1
    · exact Or.inl (Or.inl h1)
    · rcases lt_trichotomy (w i) (w j) with h2 | h2 | h2
      · exact Or.inl (Or.inr ⟨h1, h2⟩)
      · exact absurd (Prod.ext h1 h2) hne
      · exact Or.inr (Or.inr ⟨h1.symm, h2⟩)
    · exact Or.inr (Or.inl h1)
  rcases ht with ht | ht
  · have := (hM i j).1 ht; linarith
  · have := (hM j i).1 ht; linarith

theorem z5_sub1 : (0 : ZMod 5) - 1 = 4 ∧ (1 : ZMod 5) - 1 = 0 ∧ (2 : ZMod 5) - 1 = 1 ∧ (3 : ZMod 5) - 1 = 2 ∧
    (4 : ZMod 5) - 1 = 3 := by decide

/-- Pentagon `(a, c', a', c, d)` (indices `0..4`): depths `a' < c < d` and one of `c' < a`, `c' < a'`, `d < a`
(strict in the depth) give lex unimodality: peaks can only sit at `a`, `c'`, `d`, and `c', d` are not both peaks. -/
theorem k6m_pent_uni (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h23 : z 2 < z 3) (h34 : z 3 < z 4) (h : z 1 < z 0 ∨ z 1 < z 2 ∨ z 4 < z 0) : LexUni z w := by
  obtain ⟨M, hM⟩ := exists_key z w hinj
  refine lexUni_of_key z w (fun i => M * z i + w i) hinj hM ?_
  have lt : ∀ i j, z i < z j → M * z i + w i < M * z j + w j := fun i j h => (hM i j).1 (Or.inl h)
  have hk := k6m_key_inj z w hinj M hM
  refine k5d_uni_of_nopair (by decide) _ hk ?_
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_sub1
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  have k23 := lt _ _ h23
  have k34 := lt _ _ h34
  have hh : M * z 1 + w 1 < M * z 0 + w 0 ∨ M * z 1 + w 1 < M * z 2 + w 2 ∨ M * z 4 + w 4 < M * z 0 + w 0 := by
    rcases h with h | h | h
    · exact Or.inl (lt _ _ h)
    · exact Or.inr (Or.inl (lt _ _ h))
    · exact Or.inr (Or.inr (lt _ _ h))
  intro i j h1 h2 h3 ⟨⟨pi1, pi2⟩, ⟨pj1, pj2⟩⟩
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact h1 rfl
    | exact h2 (by decide)
    | exact h3 (by decide)
    | (simp only [s0, s1, s2, s3, s4, f0, f1, f2, f3, f4] at pi1 pi2 pj1 pj2
       rcases hh with hh | hh | hh <;> linarith)

theorem z4_sub1 : (0 : ZMod 4) - 1 = 3 ∧ (1 : ZMod 4) - 1 = 0 ∧ (2 : ZMod 4) - 1 = 1 ∧ (3 : ZMod 4) - 1 = 2 := by decide

/-- Quadrilateral `(b', c', a', c)` (indices `0..3`): `b' < c'` and `c < a'` (strict in the depth). -/
theorem k6m_quad_uni (z w : ZMod 4 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h01 : z 0 < z 1) (h32 : z 3 < z 2) : LexUni z w := by
  obtain ⟨M, hM⟩ := exists_key z w hinj
  refine lexUni_of_key z w (fun i => M * z i + w i) hinj hM ?_
  have lt : ∀ i j, z i < z j → M * z i + w i < M * z j + w j := fun i j h => (hM i j).1 (Or.inl h)
  have hk := k6m_key_inj z w hinj M hM
  refine k5d_uni_of_nopair (by decide) _ hk ?_
  obtain ⟨s0, s1, s2, s3⟩ := z4_sub1
  obtain ⟨f0, f1, f2, f3⟩ := z4_add
  have k01 := lt _ _ h01
  have k32 := lt _ _ h32
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
