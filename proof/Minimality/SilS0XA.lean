module

public import Minimality.Type21SilE
public import Minimality.Sector

@[expose] public section


/-!
# S0X-A: robust unimodality in the Lemma AQ form, and lex unimodality from it

`RobUni z`: no weak alternating quadruple (sp20e Lemma AQ).  Any strict refinement of a `RobUni`
sequence is cyclically unimodal (`s0x_cyclicUni_of_order`, the proof of
`IsRobustUnimodal.isCyclicUnimodal_of_order` with `not_weak_peaks` replaced by the hypothesis),
hence the lex depths `(z, w)` are lex unimodal for any `w` making the pairs distinct
(`s0x_lexUni_of_robUni`).  `RobUni` is vacuous for `k ≤ 3`.
-/

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace H21

/-- **Robust unimodality, Lemma AQ form**: no positions `B, B+b, B+c, B+d` in cyclic order
(`0 < b < c < d < k`) with `z (B+b)` and `z (B+d)` both weakly below both `z B` and `z (B+c)`.
Vacuous for `k ≤ 3` (every 3-cycle). -/
def RobUni {k : ℕ} (z : ZMod k → ℝ) : Prop :=
  ∀ (B : ZMod k) (b c d : ℕ), 0 < b → b < c → c < d → d < k →
    ¬ (z (B + b) ≤ z B ∧ z (B + b) ≤ z (B + c) ∧ z (B + d) ≤ z B ∧ z (B + d) ≤ z (B + c))

/-- The tree's robust unimodality (R1)–(R3) implies the AQ form. -/
theorem s0x_robUni_of_isRobustUnimodal {k : ℕ} {z : ZMod k → ℝ} (hz : IsRobustUnimodal z) :
    RobUni z := by
  intro B b c d h0 h1 h2 h3 ⟨e1, e2, e3, e4⟩
  exact hz.not_weak_peaks B h0 h1 h2 h3 (by simpa using e1) e2 (by simpa using e3) e4

/-- A strict refinement `z'` (distinct entries, keeping every strict comparison of `z`) of a
`RobUni` sequence is cyclically unimodal. -/
theorem s0x_cyclicUni_of_order {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    {z z' : ZMod k → ℝ} (hz : RobUni z) (hord : ∀ i j, z i < z j → z' i < z' j)
    (hinj : Function.Injective z') : IsCyclicUnimodal z' := by
  refine isCyclicUnimodal_of_localMax_unique (by omega) z' hinj ?_
  intro a b ha1 ha2 hb1 hb2
  by_contra hab
  have hle : ∀ i j, z' i < z' j → z i ≤ z j := fun i j h =>
    not_lt.mp fun h' => lt_asymm h (hord j i h')
  set n := (b - a).val with hn
  have hb : b = a + (n : ZMod k) := by rw [hn, ZMod.natCast_zmod_val]; ring
  have hnk : n < k := ZMod.val_lt _
  have hn0 : n ≠ 0 := by
    intro h0
    apply hab
    rw [hb, h0, Nat.cast_zero, add_zero]
  have hn1 : n ≠ 1 := by
    intro h1
    rw [hb, h1, Nat.cast_one, add_sub_cancel_right] at hb1
    exact lt_asymm ha2 hb1
  have hnk1 : n ≠ k - 1 := by
    intro h1
    have e : b + 1 = a := by
      rw [hb, h1, Nat.cast_sub (by omega), ZMod.natCast_self]; ring
    have e' : a - 1 = b := by rw [← e]; ring
    rw [e] at hb2
    rw [e'] at ha1
    exact lt_asymm ha1 hb2
  obtain ⟨c, hc, hcmin⟩ := (Finset.Ioo 0 n).exists_min_image (fun m => z' (a + (m : ZMod k)))
    ⟨1, by simp only [Finset.mem_Ioo]; omega⟩
  obtain ⟨d, hd, hdmin⟩ := (Finset.Ioo n k).exists_min_image (fun m => z' (a + (m : ZMod k)))
    ⟨n + 1, by simp only [Finset.mem_Ioo]; omega⟩
  simp only [Finset.mem_Ioo] at hc hd
  have e1 : a + ((1 : ℕ) : ZMod k) = a + 1 := by rw [Nat.cast_one]
  have en1 : a + ((n - 1 : ℕ) : ZMod k) = b - 1 := by
    rw [hb, Nat.cast_sub (by omega), Nat.cast_one]; ring
  have en2 : a + ((n + 1 : ℕ) : ZMod k) = b + 1 := by
    rw [hb, Nat.cast_add, Nat.cast_one]; ring
  have ek : a + ((k - 1 : ℕ) : ZMod k) = a - 1 := by
    rw [Nat.cast_sub (by omega), ZMod.natCast_self, Nat.cast_one]; ring
  have c1 : z' (a + (c : ZMod k)) < z' a := by
    have := hcmin 1 (by simp only [Finset.mem_Ioo]; omega)
    rw [e1] at this
    exact lt_of_le_of_lt this ha2
  have c2 : z' (a + (c : ZMod k)) < z' (a + (n : ZMod k)) := by
    have := hcmin (n - 1) (by simp only [Finset.mem_Ioo]; omega)
    rw [en1] at this
    rw [← hb]; exact lt_of_le_of_lt this hb1
  have c3 : z' (a + (d : ZMod k)) < z' a := by
    have := hdmin (k - 1) (by simp only [Finset.mem_Ioo]; omega)
    rw [ek] at this
    exact lt_of_le_of_lt this ha1
  have c4 : z' (a + (d : ZMod k)) < z' (a + (n : ZMod k)) := by
    have := hdmin (n + 1) (by simp only [Finset.mem_Ioo]; omega)
    rw [en2] at this
    rw [← hb]; exact lt_of_le_of_lt this hb2
  exact hz a c n d hc.1 hc.2 hd.1 hd.2 ⟨hle _ _ c1, hle _ _ c2, hle _ _ c3, hle _ _ c4⟩

/-- Two distinct lex pairs are lex comparable. -/
theorem s0x_lexLt_total {k : ℕ} {z w : ZMod k → ℝ} (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    {i j : ZMod k} (hij : i ≠ j) :
    LexLt (z i, w i) (z j, w j) ∨ LexLt (z j, w j) (z i, w i) := by
  unfold LexLt; dsimp only
  rcases lt_trichotomy (z i) (z j) with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases lt_trichotomy (w i) (w j) with h' | h' | h'
    · exact Or.inl (Or.inr ⟨h, h'⟩)
    · exact absurd (hinj i j h h') hij
    · exact Or.inr (Or.inr ⟨h.symm, h'⟩)
  · exact Or.inr (Or.inl h)

/-- **Lex unimodality from robust unimodality**: the lex depths `(z, w)` with distinct pairs
strictly refine `z`, so they are lex unimodal (`k ≥ 3`; any `z` for `k = 3`). -/
theorem s0x_lexUni_of_robUni {k : ℕ} [NeZero k] (hk : 3 ≤ k) {z : ZMod k → ℝ} (hz : RobUni z)
    (w : ZMod k → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j) : LexUni z w := by
  classical
  -- realize the lex order by `z + t w` for a small `t`
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i j, LexLt (z i, w i) (z j, w j) →
      z i + t * w i < z j + t * w j := by
    refine eventually_all.2 fun i => eventually_all.2 fun j => ?_
    by_cases h : LexLt (z i, w i) (z j, w j)
    · have := eventually_pos_affine (A := z j - z i) (B := w j - w i) (by
        rcases h with h | ⟨h1, h2⟩
        · exact Or.inl (sub_pos.2 h)
        · exact Or.inr ⟨sub_eq_zero.2 h1.symm, sub_pos.2 h2⟩)
      exact this.mono fun t ht _ => by linarith
    · exact Eventually.of_forall fun _ h' => absurd h' h
  obtain ⟨t, ht⟩ := hev.exists
  have hiff : ∀ i j, LexLt (z i, w i) (z j, w j) ↔ z i + t * w i < z j + t * w j := by
    intro i j
    refine ⟨ht i j, fun h => ?_⟩
    have hij : i ≠ j := by rintro rfl; exact lt_irrefl _ h
    rcases s0x_lexLt_total hinj hij with h' | h'
    · exact h'
    · exact absurd (ht j i h') (not_lt.2 h.le)
  have hinj' : Function.Injective fun i => z i + t * w i := by
    intro i j h
    by_contra hij
    rcases s0x_lexLt_total hinj hij with h' | h'
    · exact (ht i j h').ne h
    · exact (ht j i h').ne h.symm
  have hU := s0x_cyclicUni_of_order hk hz (z' := fun i => z i + t * w i)
    (fun i j h => ht i j (Or.inl h)) hinj'
  refine ⟨hinj, ?_⟩
  rw [← hU.2]
  congr 1
  apply Finset.filter_congr
  intro i _
  rw [hiff, hiff]

/-- A window `P + 0, …, P + L` whose interior entry `q` is weakly above both ends has an interior
strict local maximum, if consecutive entries differ. -/
theorem s0x_window_max {k : ℕ} {z : ZMod k → ℝ} (hcons : ∀ i, z i ≠ z (i + 1)) (P : ZMod k)
    (L q : ℕ) (hq0 : 0 < q) (hqL : q < L) (h0 : z P ≤ z (P + q)) (hL : z (P + L) ≤ z (P + q)) :
    ∃ p : ℕ, 0 < p ∧ p < L ∧ z (P + p - 1) < z (P + p) ∧ z (P + p + 1) < z (P + p) := by
  obtain ⟨p, hp, hmax⟩ := (Finset.Ioo 0 L).exists_max_image (fun m : ℕ => z (P + m))
    ⟨q, by simp only [Finset.mem_Ioo]; omega⟩
  simp only [Finset.mem_Ioo] at hp
  have hq := hmax q (by simp only [Finset.mem_Ioo]; omega)
  have hle : ∀ m, m ≤ L → z (P + m) ≤ z (P + p) := by
    intro m hm
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · rw [Nat.cast_zero, add_zero]; exact h0.trans hq
    rcases hm.lt_or_eq with hm' | rfl
    · exact hmax m (by simp only [Finset.mem_Ioo]; omega)
    · exact hL.trans hq
  refine ⟨p, hp.1, hp.2, ?_, ?_⟩
  · have e : P + (p : ZMod k) - 1 = P + ((p - 1 : ℕ) : ZMod k) := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]; ring
    have h1 := hle (p - 1) (by omega)
    rw [← e] at h1
    have h2 := hcons (P + (p : ZMod k) - 1)
    rw [sub_add_cancel] at h2
    exact lt_of_le_of_ne h1 h2
  · have e : P + (p : ZMod k) + 1 = P + ((p + 1 : ℕ) : ZMod k) := by push_cast; ring
    have h1 := hle (p + 1) (by omega)
    rw [← e] at h1
    exact lt_of_le_of_ne h1 (hcons _).symm

/-- Strict unimodality (`Uni`: consecutive entries differ, one strict local maximum) implies `RobUni`:
a weak alternation would give a strict local maximum on each of its two top arcs. -/
theorem s0x_robUni_of_uni {k : ℕ} [NeZero k] {z : ZMod k → ℝ} (hz : Uni z) : RobUni z := by
  classical
  intro B b c d hb hbc hcd hdk ⟨e1, e2, e3, e4⟩
  have cs : ∀ m, b ≤ m → B + (b : ZMod k) + ((m - b : ℕ) : ZMod k) = B + (m : ZMod k) := by
    intro m hm; rw [Nat.cast_sub hm]; ring
  obtain ⟨p, hp0, hpL, hp1, hp2⟩ := s0x_window_max hz.1 (B + (b : ZMod k)) (d - b) (c - b)
    (by omega) (by omega) (by rw [cs c hbc.le]; exact e2)
    (by rw [cs c hbc.le, cs d (by omega)]; exact e4)
  have w1 : B + (d : ZMod k) + ((k - d : ℕ) : ZMod k) = B := by
    rw [Nat.cast_sub hdk.le, ZMod.natCast_self]; ring
  have w2 : B + (d : ZMod k) + ((k - d + b : ℕ) : ZMod k) = B + b := by
    rw [Nat.cast_add, Nat.cast_sub hdk.le, ZMod.natCast_self]; ring
  obtain ⟨p', hp0', hpL', hp1', hp2'⟩ := s0x_window_max hz.1 (B + (d : ZMod k)) (k - d + b) (k - d)
    (by omega) (by omega) (by rw [w1]; exact e3) (by rw [w1, w2]; exact e1)
  have hne : B + (b : ZMod k) + (p : ZMod k) ≠ B + (d : ZMod k) + (p' : ZMod k) := by
    intro heq
    have h' : ((b + p : ℕ) : ZMod k) = ((d + p' : ℕ) : ZMod k) := by
      push_cast; linear_combination heq
    rw [ZMod.natCast_eq_natCast_iff'] at h'
    rw [Nat.mod_eq_of_lt (by omega : b + p < k)] at h'
    rcases lt_or_ge (d + p') k with h | h
    · rw [Nat.mod_eq_of_lt h] at h'; omega
    · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega : d + p' - k < k)] at h'; omega
  have m1 : B + (b : ZMod k) + (p : ZMod k) ∈ Finset.univ.filter
      (fun i : ZMod k => z (i - 1) < z i ∧ z (i + 1) < z i) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hp1, hp2⟩
  have m2 : B + (d : ZMod k) + (p' : ZMod k) ∈ Finset.univ.filter
      (fun i : ZMod k => z (i - 1) < z i ∧ z (i + 1) < z i) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hp1', hp2'⟩
  have hc := Finset.one_lt_card.2 ⟨_, m1, _, m2, hne⟩
  rw [hz.2] at hc
  exact lt_irrefl _ hc

end H21
end Minimality

