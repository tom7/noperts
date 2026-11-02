module

public import Minimality.MaxwellRadonD

@[expose] public section


namespace Minimality.MRB

open Real Finset

structure MRBData (r : ℕ) (X Y δ : ℕ → ℝ) : Prop where
  hO : ∀ i j k, i < j → j < k → k < r → 0 < mrb_O X Y i j k
  hne : ∀ i j, i < j → j < r → ¬ (X i = X j ∧ Y i = Y j)
  h0 : ∑ k ∈ Finset.range r, δ k = 0
  hX : ∑ k ∈ Finset.range r, δ k * X k = 0
  hY : ∑ k ∈ Finset.range r, δ k * Y k = 0

theorem MRBData.neg {r X Y δ} (D : MRBData r X Y δ) : MRBData r X Y (fun k => -δ k) where
  hO := D.hO
  hne := D.hne
  h0 := by simp [Finset.sum_neg_distrib, D.h0]
  hX := by simp [Finset.sum_neg_distrib, neg_mul, D.hX]
  hY := by simp [Finset.sum_neg_distrib, neg_mul, D.hY]

theorem mrb_chordB {r X Y δ} (D : MRBData r X Y δ) {i j : ℕ} (hij : i < j) (hj : j < r)
    (hin : ∀ k, i < k → k < j → 0 ≤ δ k)
    (hout : ∀ k, k < r → (k < i ∨ j < k) → δ k ≤ 0) : ∀ k, k < r → δ k = 0 := by
  intro k hk
  have := mrb_chordA r X Y (fun k => -δ k) D.neg.hO D.neg.hne D.neg.h0 D.neg.hX D.neg.hY hij hj
    (fun k h1 h2 => by simpa using hin k h1 h2) (fun k h1 h2 => by simpa using hout k h1 h2) k hk
  simpa using this

theorem mrb_single_neg {r X Y δ} (D : MRBData r X Y δ) (hr : 2 ≤ r) {a : ℕ} (ha : a < r)
    (h : ∀ k, k < r → k ≠ a → 0 ≤ δ k) : ∀ k, k < r → δ k = 0 := by
  by_cases h1 : a + 1 < r
  · exact mrb_chordA r X Y δ D.hO D.hne D.h0 D.hX D.hY (i := a) (j := a + 1) (by omega) h1
      (fun k h1 h2 => by omega) (fun k hk hk' => h k hk (by omega))
  · exact mrb_chordA r X Y δ D.hO D.hne D.h0 D.hX D.hY (i := a - 1) (j := a) (by omega) ha
      (fun k h1 h2 => by omega) (fun k hk hk' => h k hk (by omega))

theorem mrb_single_pos {r X Y δ} (D : MRBData r X Y δ) (hr : 2 ≤ r) {a : ℕ} (ha : a < r)
    (h : ∀ k, k < r → k ≠ a → δ k ≤ 0) : ∀ k, k < r → δ k = 0 := by
  intro k hk
  have := mrb_single_neg D.neg hr ha (fun k hk h' => by simpa using h k hk h') k hk
  simpa using this

theorem mrb_nocrown {r X Y δ} (D : MRBData r X Y δ) (hr : 2 ≤ r) (hnc : ¬ mrb_crown r δ) :
    ∀ k, k < r → δ k = 0 := by
  by_contra hnz
  push_neg at hnz
  obtain ⟨p, hp, hp0⟩ := hnz
  -- there are positive and negative entries
  have hposex : ∃ q, q < r ∧ 0 < δ q := by
    by_contra hh; push_neg at hh
    have := (Finset.sum_eq_zero_iff_of_nonpos (fun k hk => hh k (Finset.mem_range.1 hk))).1 D.h0
      p (Finset.mem_range.2 hp)
    exact hp0 this
  have hnegex : ∃ q, q < r ∧ δ q < 0 := by
    by_contra hh; push_neg at hh
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun k hk => hh k (Finset.mem_range.1 hk))).1 D.h0
      p (Finset.mem_range.2 hp)
    exact hp0 this
  obtain ⟨q1, hq1, hq1p⟩ := hposex
  obtain ⟨q2, hq2, hq2n⟩ := hnegex
  set N := (Finset.range r).filter (fun k => δ k < 0) with hN
  set P := (Finset.range r).filter (fun k => 0 < δ k) with hP
  have hNne : N.Nonempty := ⟨q2, by simp [hN, hq2, hq2n]⟩
  have hPne : P.Nonempty := ⟨q1, by simp [hP, hq1, hq1p]⟩
  have memN : ∀ k, k ∈ N ↔ k < r ∧ δ k < 0 := fun k => by simp [hN]
  have memP : ∀ k, k ∈ P ↔ k < r ∧ 0 < δ k := fun k => by simp [hP]
  set a := N.min' hNne with ha
  set b := N.max' hNne with hb
  set c := P.min' hPne with hc
  set d := P.max' hPne with hd
  have haN : a ∈ N := Finset.min'_mem _ _
  have hbN : b ∈ N := Finset.max'_mem _ _
  have hcP : c ∈ P := Finset.min'_mem _ _
  have hdP : d ∈ P := Finset.max'_mem _ _
  have hNa : ∀ k, k < r → δ k < 0 → a ≤ k ∧ k ≤ b := fun k hk h =>
    ⟨Finset.min'_le _ _ ((memN k).2 ⟨hk, h⟩), Finset.le_max' _ _ ((memN k).2 ⟨hk, h⟩)⟩
  have hPc : ∀ k, k < r → 0 < δ k → c ≤ k ∧ k ≤ d := fun k hk h =>
    ⟨Finset.min'_le _ _ ((memP k).2 ⟨hk, h⟩), Finset.le_max' _ _ ((memP k).2 ⟨hk, h⟩)⟩
  obtain ⟨har, hav⟩ := (memN a).1 haN
  obtain ⟨hbr, hbv⟩ := (memN b).1 hbN
  obtain ⟨hcr, hcv⟩ := (memP c).1 hcP
  obtain ⟨hdr, hdv⟩ := (memP d).1 hdP
  have hab : a ≤ b := Finset.min'_le _ _ hbN
  have hcd : c ≤ d := Finset.min'_le _ _ hdP
  by_cases C1 : ∃ p0, p0 < r ∧ 0 < δ p0 ∧ a < p0 ∧ p0 < b
  · -- P has an element strictly inside (a, b)
    obtain ⟨p0, hp0r, hp0v, hap0, hp0b⟩ := C1
    have hin : ∀ k, k < r → 0 < δ k → a < k ∧ k < b := by
      intro k hk hv
      by_contra hcon
      have hk' : k < a ∨ b < k := by
        by_contra h2; push_neg at h2
        rcases h2 with h2
        have : k ≠ a := by rintro rfl; linarith
        have : k ≠ b := by rintro rfl; linarith
        omega
      rcases hk' with h3 | h3
      · exact hnc ⟨k, a, p0, b, h3, hap0, hp0b, hbr, Or.inl ⟨hv, hav, hp0v, hbv⟩⟩
      · exact hnc ⟨a, p0, b, k, hap0, hp0b, h3, hk, Or.inr ⟨hav, hp0v, hbv, hv⟩⟩
    have hac : a < c := (hin c hcr hcv).1
    have hdb : d < b := (hin d hdr hdv).2
    by_cases C2 : ∃ n, n < r ∧ δ n < 0 ∧ c < n ∧ n < d
    · obtain ⟨n, hnr, hnv, hcn, hnd⟩ := C2
      exact hnc ⟨a, c, n, d, hac, hcn, hnd, hdr, Or.inr ⟨hav, hcv, hnv, hdv⟩⟩
    · push_neg at C2
      rcases hcd.lt_or_eq with hlt | heq
      · refine hp0 (mrb_chordB D (i := c) (j := d) hlt hdr ?_ ?_ p hp)
        · intro k h1 h2
          by_contra hh; push_neg at hh
          have := C2 k (by omega) hh h1
          omega
        · intro k hk hk'
          by_contra hh; push_neg at hh
          have := hPc k hk hh
          omega
      · refine hp0 (mrb_single_pos D hr hcr (a := c) ?_ p hp)
        intro k hk hk'
        by_contra hh; push_neg at hh
        have := hPc k hk hh
        omega
  · push_neg at C1
    rcases hab.lt_or_eq with hlt | heq
    · refine hp0 (mrb_chordA r X Y δ D.hO D.hne D.h0 D.hX D.hY (i := a) (j := b) hlt hbr ?_ ?_ p hp)
      · intro k h1 h2
        by_contra hh; push_neg at hh
        exact absurd (C1 k (by omega) hh h1) (by omega)
      · intro k hk hk'
        by_contra hh; push_neg at hh
        have := hNa k hk hh
        omega
    · refine hp0 (mrb_single_neg D hr har (a := a) ?_ p hp)
      intro k hk hk'
      by_contra hh; push_neg at hh
      have := hNa k hk hh
      omega

end Minimality.MRB
