module

public import Minimality.Type08S.C2K17F2A
public import Minimality.Type08S.C2K17F0A

@[expose] public section

/-!
# K17GB / GB0: lex-unimodality toolkit for the Bundle B cells (keys: `exists_key` reduces every lex statement to reals)
-/
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

open Classical in
/-- Workhorse (5-cycle): reduce to real keys. -/
theorem k17gb_uni5 (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (hP : ∀ key : ZMod 5 → ℝ, (∀ i j, LexLt (z i, w i) (z j, w j) ↔ key i < key j) →
      ∃ m, (key (m - 1) < key m ∧ key (m + 1) < key m) ∧
        ∀ i, i ≠ m → ¬ (key (i - 1) < key i ∧ key (i + 1) < key i)) : LexUni z w := by
  obtain ⟨M, hM⟩ := exists_key z w hinj
  obtain ⟨m, hm, ho⟩ := hP (fun i => M * z i + w i) hM
  refine lexUni_of_key z w (fun i => M * z i + w i) hinj hM ?_
  have hinj0 : ∀ i j, (fun _ : ZMod 5 => (0 : ℝ)) i = (fun _ : ZMod 5 => (0 : ℝ)) j →
      (M * z i + w i) = (M * z j + w j) → i = j := by
    intro i j _ h
    by_contra hne
    have hne' : (z i, w i) ≠ (z j, w j) := fun h' =>
      hne (hinj i j (congrArg Prod.fst h') (congrArg Prod.snd h'))
    rcases lexLt_total hne' with h1 | h1
    · have := (hM i j).1 h1; linarith
    · have := (hM j i).1 h1; linarith
  refine k17f_lexUni5_of_peak (fun _ => 0) (fun i => M * z i + w i) hinj0 m ?_ ?_
  · simp only [LexLt]; simpa using hm
  · intro i hi; simp only [LexLt]; simpa using ho i hi

/-- Cycle `(x0..x4)`, `z0 = z1 < z2 < z3 < z4` (plateau at `0,1`, then increasing to the peak `4`). -/
theorem k17gb_lex5_plat01 (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h02 : z 0 < z 2) (h12 : z 1 < z 2) (h23 : z 2 < z 3) (h34 : z 3 < z 4) : LexUni z w := by
  refine k17gb_uni5 z w hinj (fun key hk => ?_)
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add_one
  obtain ⟨t0, t1, t2, t3, t4⟩ := k17f_zsub
  have k02 : key 0 < key 2 := (hk 0 2).1 (Or.inl h02)
  have k12 : key 1 < key 2 := (hk 1 2).1 (Or.inl h12)
  have k23 : key 2 < key 3 := (hk 2 3).1 (Or.inl h23)
  have k34 : key 3 < key 4 := (hk 3 4).1 (Or.inl h34)
  refine ⟨4, ?_, fun i hi => ?_⟩
  · simp only [t4, s4]; exact ⟨k34, by linarith⟩
  · rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
    · simp only [t0, s0]; rintro ⟨a, b⟩; linarith
    · simp only [t1, s1]; rintro ⟨a, b⟩; linarith
    · simp only [t2, s2]; rintro ⟨a, b⟩; linarith
    · simp only [t3, s3]; rintro ⟨a, b⟩; linarith
    · exact absurd rfl hi

/-- Plateau `x1,x2,x3` with `w3 < w2` (`x2` not a w-valley), flanks `z0 < z4 < z1`. -/
theorem k17gb_lex5_plat123 (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h04 : z 0 < z 4) (h41 : z 4 < z 1) (h12 : z 1 = z 2) (h23 : z 2 = z 3) (hw : w 3 < w 2) :
    LexUni z w := by
  refine k17gb_uni5 z w hinj (fun key hk => ?_)
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add_one
  obtain ⟨t0, t1, t2, t3, t4⟩ := k17f_zsub
  have k04 : key 0 < key 4 := (hk 0 4).1 (Or.inl h04)
  have k41 : key 4 < key 1 := (hk 4 1).1 (Or.inl h41)
  have k42 : key 4 < key 2 := (hk 4 2).1 (Or.inl (by linarith))
  have k43 : key 4 < key 3 := (hk 4 3).1 (Or.inl (by linarith))
  have k32 : key 3 < key 2 := (hk 3 2).1 (Or.inr ⟨h23.symm, hw⟩)
  by_cases h12' : key 2 < key 1
  · refine ⟨1, ?_, fun i hi => ?_⟩
    · simp only [t1, s1]; exact ⟨by linarith, h12'⟩
    · rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · simp only [t0, s0]; rintro ⟨a, b⟩; linarith
      · exact absurd rfl hi
      · simp only [t2, s2]; rintro ⟨a, b⟩; linarith
      · simp only [t3, s3]; rintro ⟨a, b⟩; linarith
      · simp only [t4, s4]; rintro ⟨a, b⟩; linarith
  · push Not at h12'
    have hlt : key 1 < key 2 := by
      rcases h12'.lt_or_eq with h | h
      · exact h
      · exfalso
        have hn : (z 1, w 1) ≠ (z 2, w 2) := fun h' => by
          have := hinj 1 2 (congrArg Prod.fst h') (congrArg Prod.snd h'); exact absurd this (by decide)
        rcases lexLt_total hn with h' | h'
        · have := (hk _ _).1 h'; linarith
        · have := (hk _ _).1 h'; linarith
    refine ⟨2, ?_, fun i hi => ?_⟩
    · simp only [t2, s2]; exact ⟨hlt, k32⟩
    · rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · simp only [t0, s0]; rintro ⟨a, b⟩; linarith
      · simp only [t1, s1]; rintro ⟨a, b⟩; linarith
      · exact absurd rfl hi
      · simp only [t3, s3]; rintro ⟨a, b⟩; linarith
      · simp only [t4, s4]; rintro ⟨a, b⟩; linarith

end C2
end Type08Sp
end Minimality
