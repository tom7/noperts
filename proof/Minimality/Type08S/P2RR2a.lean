module

public import Minimality.Type08S.P2RKLex

@[expose] public section

set_option relaxedAutoImplicit true
/-!
# pkR / R2a: abstract lemmas for the lex cell of R2: lex asymmetry, a root-avoiding choice of `ε`,
and `LexUni` of the five-cycle `(d, a, c', b', c)` in which `c', b'` are the two top entries.
-/
set_option autoImplicit true
set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace R2

theorem lexLt_asymm {p q : ℝ × ℝ} (h : LexLt p q) : ¬ LexLt q p := by
  unfold LexLt at *
  rcases h with h | ⟨h1, h2⟩ <;> rintro (h' | ⟨h1', h2'⟩) <;> linarith

theorem lexLt_total {p q : ℝ × ℝ} (h : p ≠ q) : LexLt p q ∨ LexLt q p := by
  unfold LexLt
  rcases lt_trichotomy p.1 q.1 with h1 | h1 | h1
  · exact Or.inl (Or.inl h1)
  · rcases lt_trichotomy p.2 q.2 with h2 | h2 | h2
    · exact Or.inl (Or.inr ⟨h1, h2⟩)
    · exact absurd (Prod.ext h1 h2) h
    · exact Or.inr (Or.inr ⟨h1.symm, h2⟩)
  · exact Or.inr (Or.inl h1)

theorem lexLt_ne {p q : ℝ × ℝ} (h : LexLt p q) : p ≠ q := by
  rintro rfl
  exact lexLt_asymm h h

/-- Avoid the roots of finitely many affine functions of `ε`, none identically zero. -/
theorem exists_avoid {ι : Type*} (s : Finset ι) (p q : ι → ℝ) (h : ∀ i, p i ≠ 0 ∨ q i ≠ 0) {E : ℝ}
    (hE : 0 < E) : ∃ ε : ℝ, 0 < ε ∧ ε < E ∧ ∀ i ∈ s, p i + q i * ε ≠ 0 := by
  classical
  obtain ⟨ε, hε, hn⟩ := (Set.Ioo_infinite hE).exists_notMem_finset (s.image fun i => -p i / q i)
  refine ⟨ε, hε.1, hε.2, fun i hi h0 => ?_⟩
  rcases h i with hp | hq
  · by_cases hq : q i = 0
    · rw [hq] at h0; apply hp; linarith
    · apply hn; rw [Finset.mem_image]
      exact ⟨i, hi, by field_simp; linarith⟩
  · apply hn; rw [Finset.mem_image]
    exact ⟨i, hi, by field_simp; linarith⟩

/-- `LexUni` of the five-cycle `(d, a, c', b', c)`: `a < c'`, `c < b'`, `d` is not above both `a`, `c`
(so the peak is the larger of `c', b'`), all five pairs distinct. -/
theorem lexUni_cyc5 {zd za zc' zb' zc wd wa wc' wb' wc : ℝ}
    (hac : LexLt (za, wa) (zc', wc')) (hcb : LexLt (zc, wc) (zb', wb'))
    (hd : LexLt (zd, wd) (za, wa) ∨ LexLt (zd, wd) (zc, wc))
    (hdc' : (zd, wd) ≠ (zc', wc')) (hdb' : (zd, wd) ≠ (zb', wb')) (hda : (zd, wd) ≠ (za, wa))
    (hdc : (zd, wd) ≠ (zc, wc)) (hab' : (za, wa) ≠ (zb', wb')) (hacc : (za, wa) ≠ (zc, wc))
    (hcc' : (zc, wc) ≠ (zc', wc')) (hcb' : (zc', wc') ≠ (zb', wb')) :
    LexUni (K.cyc5 zd za zc' zb' zc) (K.cyc5 wd wa wc' wb' wc) := by
  classical
  have e5 := K.z5s
  refine ⟨?_, ?_⟩
  · have key : ∀ i j : ZMod 5, K.cyc5 zd za zc' zb' zc i = K.cyc5 zd za zc' zb' zc j →
        K.cyc5 wd wa wc' wb' wc i = K.cyc5 wd wa wc' wb' wc j → i = j := by
      intro i j h1 h2
      have hp : ∀ i j : ZMod 5, K.cyc5 zd za zc' zb' zc i = K.cyc5 zd za zc' zb' zc j →
          K.cyc5 wd wa wc' wb' wc i = K.cyc5 wd wa wc' wb' wc j → (K.cyc5 zd za zc' zb' zc i,
            K.cyc5 wd wa wc' wb' wc i) = (K.cyc5 zd za zc' zb' zc j, K.cyc5 wd wa wc' wb' wc j) :=
        fun i j a b => Prod.ext a b
      have := hp i j h1 h2
      rcases K.z5c i with rfl | rfl | rfl | rfl | rfl <;> rcases K.z5c j with rfl | rfl | rfl | rfl | rfl <;>
        first | rfl | (exfalso; simp only [K.c5_0, K.c5_1, K.c5_2, K.c5_3, K.c5_4] at this
                       first | exact hdc' this | exact hdb' this | exact hda this | exact hdc this
                             | exact hab' this | exact hacc this | exact hcc' this | exact hcb' this
                             | exact hdc' this.symm | exact hdb' this.symm | exact hda this.symm
                             | exact hdc this.symm | exact hab' this.symm | exact hacc this.symm
                             | exact hcc' this.symm | exact hcb' this.symm
                             | exact (lexLt_ne hac) this | exact (lexLt_ne hac) this.symm
                             | exact (lexLt_ne hcb) this | exact (lexLt_ne hcb) this.symm)
    exact key
  · have pred : ∀ i : ZMod 5, (LexLt (K.cyc5 zd za zc' zb' zc (i - 1), K.cyc5 wd wa wc' wb' wc (i - 1))
        (K.cyc5 zd za zc' zb' zc i, K.cyc5 wd wa wc' wb' wc i) ∧
        LexLt (K.cyc5 zd za zc' zb' zc (i + 1), K.cyc5 wd wa wc' wb' wc (i + 1))
        (K.cyc5 zd za zc' zb' zc i, K.cyc5 wd wa wc' wb' wc i)) ↔
        (i = 2 ∧ LexLt (zb', wb') (zc', wc')) ∨ (i = 3 ∧ LexLt (zc', wc') (zb', wb')) := by
      intro i
      have s1 : (0:ZMod 5) - 1 = 4 := by decide
      have s2 : (1:ZMod 5) - 1 = 0 := by decide
      have s3 : (2:ZMod 5) - 1 = 1 := by decide
      have s4 : (3:ZMod 5) - 1 = 2 := by decide
      have s5 : (4:ZMod 5) - 1 = 3 := by decide
      have p0 : (0:ZMod 5) + 1 = 1 := by decide
      have p1 : (1:ZMod 5) + 1 = 2 := by decide
      have p2 : (2:ZMod 5) + 1 = 3 := by decide
      have p3 : (3:ZMod 5) + 1 = 4 := by decide
      have p4 : (4:ZMod 5) + 1 = 0 := by decide
      have d2 : (2:ZMod 5) ≠ 3 := by decide
      have d3 : (3:ZMod 5) ≠ 2 := by decide
      have n0 : ∀ x : ZMod 5, x = 0 → x ≠ 2 ∧ x ≠ 3 := by rintro x rfl; decide
      have n1 : ∀ x : ZMod 5, x = 1 → x ≠ 2 ∧ x ≠ 3 := by rintro x rfl; decide
      have n4 : ∀ x : ZMod 5, x = 4 → x ≠ 2 ∧ x ≠ 3 := by rintro x rfl; decide
      rcases K.z5c i with rfl | rfl | rfl | rfl | rfl
      · rw [s1, p0]; simp only [K.c5_0, K.c5_1, K.c5_4]
        constructor
        · rintro ⟨h1, h2⟩
          rcases hd with h | h
          · exact (lexLt_asymm h h2).elim
          · exact (lexLt_asymm h h1).elim
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact absurd h (by decide)
      · rw [s2, p1]; simp only [K.c5_0, K.c5_1, K.c5_2]
        constructor
        · rintro ⟨h1, h2⟩; exact (lexLt_asymm hac h2).elim
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact absurd h (by decide)
      · rw [s3, p2]; simp only [K.c5_1, K.c5_2, K.c5_3]
        constructor
        · rintro ⟨h1, h2⟩; exact Or.inl ⟨trivial, h2⟩
        · rintro (⟨_, h⟩ | ⟨h, _⟩)
          · exact ⟨hac, h⟩
          · exact absurd h d2
      · rw [s4, p3]; simp only [K.c5_2, K.c5_3, K.c5_4]
        constructor
        · rintro ⟨h1, h2⟩; exact Or.inr ⟨trivial, h1⟩
        · rintro (⟨h, _⟩ | ⟨_, h⟩)
          · exact absurd h d3
          · exact ⟨h, hcb⟩
      · rw [s5, p4]; simp only [K.c5_3, K.c5_4, K.c5_0]
        constructor
        · rintro ⟨h1, h2⟩; exact (lexLt_asymm hcb h1).elim
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact absurd h (by decide)
    rw [Finset.card_eq_one]
    rcases lexLt_total hcb' with h | h
    · refine ⟨3, ?_⟩
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, pred]
      constructor
      · rintro (⟨_, h'⟩ | ⟨h', _⟩)
        · exact (lexLt_asymm h h').elim
        · exact h'
      · rintro rfl; exact Or.inr ⟨rfl, h⟩
    · refine ⟨2, ?_⟩
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, pred]
      constructor
      · rintro (⟨h', _⟩ | ⟨_, h'⟩)
        · exact h'
        · exact (lexLt_asymm h h').elim
      · rintro rfl; exact Or.inl ⟨rfl, h⟩
end R2
end Type08Sp
end Minimality
