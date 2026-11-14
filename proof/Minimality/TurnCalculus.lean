module

public import Minimality.Generic.PV.SK

@[expose] public section

/-!
# Turn calculus (Lemma W′ / Lemma TC / Lemma VM, combinatorial core)

Peak counts of cyclic sequences of reals `z : ZMod k → ℝ` (the corner cycles of
`IsCyclicUnimodal`), and how they change when an entry is deleted (a corner hidden) or inserted,
or when the order of one adjacent pair is reversed (a depth tie broken the other way).

* `cycPeaks z`, `numPeaks z`: the strict local maxima and their number (κ of the paper; for an
  injective cycle κ is also the number of `(+, −)` adjacencies of the cyclic step word).
  `isCyclicUnimodal_iff_numPeaks`: unimodal iff injective with one peak;
  `one_le_numPeaks`: an injective cycle with at least two entries has a peak.
* `numPeaks_skipAt_add` (Lemma TC (ii), exact local form): deleting entry `i` changes the peak
  count only through the peaks at `i - 1, i, i + 1` before and at the two new neighbours after
  (`peakInd a b c`: indicator of `b` above both `a` and `c`).  Insertion is read backwards: `z` is
  the cycle with the corner, `skipAt z i` the one without.
* `numPeaks_skipAt_le` (deletion never raises κ, i.e. insertion never lowers it) and
  `numPeaks_le_skipAt_add_one` (deletion lowers κ by at most one): Δκ ∈ {0, 1}.
* `numPeaks_skipAt_of_between`, `numPeaks_skipAt_high`, `numPeaks_skipAt_low` (σ = +) and
  `numPeaks_skipAt_high'`, `numPeaks_skipAt_low'` (σ = −): the Δκ rules of Lemma TC (ii).
* `IsCyclicUnimodal.skipAt` (Lemma VM, combinatorial core): hiding a corner of a unimodal cycle
  keeps it unimodal.
* `numPeaks_le_add_one_of_flip` (Lemma TC (i)): two cycles with the same strict comparisons except
  for the adjacent pair `(a, a + 1)` have peak counts differing by at most one.
  `numPeaks_le_add_one_of_tie`: the two strict refinements of a cycle whose only tie is the
  adjacent pair `(a, a + 1)`.
-/

namespace Minimality

open Finset

/-- The peaks (strict local maxima) of a cyclic sequence. -/
noncomputable def cycPeaks {k : ℕ} [NeZero k] (z : ZMod k → ℝ) : Finset (ZMod k) :=
  univ.filter (fun i : ZMod k => z (i - 1) < z i ∧ z (i + 1) < z i)

/-- The number of peaks of a cyclic sequence (κ). -/
noncomputable def numPeaks {k : ℕ} [NeZero k] (z : ZMod k → ℝ) : ℕ := (cycPeaks z).card

theorem mem_cycPeaks {k : ℕ} [NeZero k] {z : ZMod k → ℝ} {i : ZMod k} :
    i ∈ cycPeaks z ↔ z (i - 1) < z i ∧ z (i + 1) < z i := by
  simp [cycPeaks]

theorem isCyclicUnimodal_iff_numPeaks {k : ℕ} [NeZero k] (z : ZMod k → ℝ) :
    IsCyclicUnimodal z ↔ Function.Injective z ∧ numPeaks z = 1 := Iff.rfl

/-- An injective cycle with at least two entries has a peak (its maximum). -/
theorem one_le_numPeaks {k : ℕ} [NeZero k] (hk : 2 ≤ k) {z : ZMod k → ℝ}
    (hz : Function.Injective z) : 1 ≤ numPeaks z := by
  obtain ⟨p, -, hp⟩ := (univ : Finset (ZMod k)).exists_max_image z univ_nonempty
  have : Fact (1 < k) := ⟨by omega⟩
  have h1 : p - 1 ≠ p := by simp
  have h2 : p + 1 ≠ p := by simp
  refine Finset.card_pos.mpr ⟨p, mem_cycPeaks.mpr ⟨?_, ?_⟩⟩
  · exact lt_of_le_of_ne (hp _ (mem_univ _)) (fun h => h1 (hz h))
  · exact lt_of_le_of_ne (hp _ (mem_univ _)) (fun h => h2 (hz h))

section skip
variable {m : ℕ} [NeZero m]

lemma phi_ne (i : ZMod (m + 1)) (j : ZMod m) : phi i j ≠ i := by
  intro h
  have e : phi i j = i + ((j.val + 1 : ℕ) : ZMod (m + 1)) := by
    simp only [phi]; push_cast; ring
  have h0 : ((j.val + 1 : ℕ) : ZMod (m + 1)) = 0 := by
    rw [e] at h; simpa using h
  rw [ZMod.natCast_eq_zero_iff] at h0
  have := Nat.le_of_dvd (by omega) h0
  have := j.val_lt
  omega

/-- The indicator of a peak with neighbours `a`, `c` and value `b`. -/
noncomputable def peakInd (a b c : ℝ) : ℕ := if a < b ∧ c < b then 1 else 0

lemma card_cycPeaks_inter_three {k : ℕ} [NeZero k] (z : ZMod k → ℝ) (i : ZMod k)
    (h1 : i - 1 ≠ i) (h2 : i - 1 ≠ i + 1) (h3 : i ≠ i + 1) :
    (cycPeaks z ∩ {i - 1, i, i + 1}).card =
      peakInd (z (i - 1 - 1)) (z (i - 1)) (z i) + peakInd (z (i - 1)) (z i) (z (i + 1)) +
        peakInd (z i) (z (i + 1)) (z (i + 1 + 1)) := by
  have e : cycPeaks z ∩ {i - 1, i, i + 1} =
      ({i - 1, i, i + 1} : Finset (ZMod k)).filter
        (fun a => z (a - 1) < z a ∧ z (a + 1) < z a) := by
    ext a; simp only [mem_inter, mem_cycPeaks, mem_filter]; tauto
  rw [e, Finset.card_filter, sum_insert (by simp [h1, h2]), sum_insert (by simp [h3]),
    sum_singleton]
  simp only [peakInd, sub_add_cancel, add_sub_cancel_right]
  ring

lemma card_cycPeaks_inter_two (z : ZMod m → ℝ) (h : (0 : ZMod m) ≠ -1) :
    (cycPeaks z ∩ {0, -1}).card =
      peakInd (z (-1)) (z 0) (z 1) + peakInd (z (-1 - 1)) (z (-1)) (z 0) := by
  have e : cycPeaks z ∩ {0, -1} =
      ({0, -1} : Finset (ZMod m)).filter (fun a => z (a - 1) < z a ∧ z (a + 1) < z a) := by
    ext a; simp only [mem_inter, mem_cycPeaks, mem_filter]; tauto
  rw [e, Finset.card_filter, sum_insert (by simp [h]), sum_singleton]
  simp only [peakInd, zero_sub, zero_add, neg_add_cancel]

/-- Away from the deleted entry and its two neighbours, the peaks correspond under `phi`. -/
lemma cycPeaks_sdiff (hm : 2 ≤ m) (z : ZMod (m + 1) → ℝ) (i : ZMod (m + 1)) :
    cycPeaks z \ {i - 1, i, i + 1} = (cycPeaks (skipAt z i) \ {0, -1}).image (phi i) := by
  have : Fact (1 < m) := ⟨by omega⟩
  ext a
  simp only [mem_sdiff, mem_cycPeaks, mem_insert, mem_singleton, not_or, mem_image]
  constructor
  · rintro ⟨ha, h1, h2, h3⟩
    obtain ⟨j, rfl⟩ := phi_surj i a h2
    have hj0 : j ≠ 0 := by rintro rfl; exact h3 (phi_zero i)
    have hj1 : j ≠ -1 := by rintro rfl; exact h1 (phi_neg_one i)
    refine ⟨j, ⟨?_, hj0, hj1⟩, rfl⟩
    simp only [skipAt]
    change z (phi i (j - 1)) < z (phi i j) ∧ z (phi i (j + 1)) < z (phi i j)
    rw [phi_pred i j hj0, phi_succ i j hj1]
    exact ha
  · rintro ⟨j, ⟨hj, hj0, hj1⟩, rfl⟩
    refine ⟨?_, ?_, phi_ne i j, ?_⟩
    · change z (phi i (j - 1)) < z (phi i j) ∧ z (phi i (j + 1)) < z (phi i j) at hj
      rwa [phi_pred i j hj0, phi_succ i j hj1] at hj
    · intro h; rw [← phi_neg_one i] at h; exact hj1 (phi_inj i h)
    · intro h; rw [← phi_zero i] at h; exact hj0 (phi_inj i h)

/-- **Lemma TC (ii), local form.**  Deleting entry `i` of a cycle of `m + 1 ≥ 3` reals: the peak
count before, plus the peak indicators at the two new neighbours `i - 1, i + 1` after, equals the
count after plus the peak indicators at `i - 1, i, i + 1` before. -/
theorem numPeaks_skipAt_add (hm : 2 ≤ m) (z : ZMod (m + 1) → ℝ) (i : ZMod (m + 1)) :
    numPeaks z + (peakInd (z (i - 1)) (z (i + 1)) (z (i + 1 + 1)) +
        peakInd (z (i - 1 - 1)) (z (i - 1)) (z (i + 1))) =
      numPeaks (skipAt z i) + (peakInd (z (i - 1 - 1)) (z (i - 1)) (z i) +
        peakInd (z (i - 1)) (z i) (z (i + 1)) + peakInd (z i) (z (i + 1)) (z (i + 1 + 1))) := by
  have : Fact (1 < m) := ⟨by omega⟩
  have : Fact (1 < m + 1) := ⟨by omega⟩
  have h0 : (0 : ZMod m) ≠ -1 := by
    intro h; apply one_ne_zero (α := ZMod m); simpa using h.symm
  have h1 : i - 1 ≠ i := by simp
  have h3 : i ≠ i + 1 := by simp
  have h2 : i - 1 ≠ i + 1 := by
    intro h
    have e2 : ((2 : ℕ) : ZMod (m + 1)) = 0 := by
      have : i + 1 - (i - 1) = ((2 : ℕ) : ZMod (m + 1)) := by push_cast; ring
      rw [← this, h, sub_self]
    rw [ZMod.natCast_eq_zero_iff] at e2
    have := Nat.le_of_dvd (by norm_num) e2; omega
  have hA := card_sdiff_add_card_inter (cycPeaks z) {i - 1, i, i + 1}
  have hB := card_sdiff_add_card_inter (cycPeaks (skipAt z i)) {0, -1}
  rw [cycPeaks_sdiff hm z i, card_image_of_injective _ (phi_inj i)] at hA
  rw [card_cycPeaks_inter_three z i h1 h2 h3] at hA
  rw [card_cycPeaks_inter_two _ h0] at hB
  have s0 : skipAt z i 0 = z (i + 1) := by simp [skipAt]
  have s1 : skipAt z i 1 = z (i + 1 + 1) := by
    change z (phi i 1) = _
    have := phi_succ i 0 h0
    rw [zero_add] at this; rw [this, phi_zero]
  have sm1 : skipAt z i (-1) = z (i - 1) := by
    change z (phi i (-1)) = _; rw [phi_neg_one]
  have sm2 : skipAt z i (-1 - 1) = z (i - 1 - 1) := by
    change z (phi i (-1 - 1)) = _; rw [phi_pred i (-1) (Ne.symm h0), phi_neg_one]
  rw [s0, s1, sm1, sm2] at hB
  unfold numPeaks
  omega

/-- The local inequalities behind Δκ ∈ {0, 1}. -/
lemma peakInd_local_le (a b c d e : ℝ) (hbc : b ≠ c) (hcd : c ≠ d) :
    peakInd b d e + peakInd a b d ≤ peakInd a b c + peakInd b c d + peakInd c d e := by
  unfold peakInd
  rcases lt_or_gt_of_ne hbc with h1 | h1 <;> rcases lt_or_gt_of_ne hcd with h2 | h2 <;>
    split_ifs <;> first | omega | (exfalso; simp_all; done) | (exfalso; simp_all; linarith)

lemma peakInd_local_le' (a b c d e : ℝ) (hbc : b ≠ c) (hcd : c ≠ d) (hbd : b ≠ d) :
    peakInd a b c + peakInd b c d + peakInd c d e ≤ peakInd b d e + peakInd a b d + 1 := by
  unfold peakInd
  rcases lt_or_gt_of_ne hbc with h1 | h1 <;> rcases lt_or_gt_of_ne hcd with h2 | h2 <;>
    rcases lt_or_gt_of_ne hbd with h3 | h3 <;>
    split_ifs <;> first | omega | (exfalso; simp_all; done) | (exfalso; simp_all; linarith)

/-- **Deletion never raises κ; insertion never lowers it** (Lemma TC (ii), Lemma W′).  Only the
two comparisons of the deleted entry with its neighbours need to be strict. -/
theorem numPeaks_skipAt_le (hm : 2 ≤ m) {z : ZMod (m + 1) → ℝ} {i : ZMod (m + 1)}
    (h1 : z (i - 1) ≠ z i) (h2 : z i ≠ z (i + 1)) : numPeaks (skipAt z i) ≤ numPeaks z := by
  have := numPeaks_skipAt_add hm z i
  have := peakInd_local_le (z (i - 1 - 1)) (z (i - 1)) (z i) (z (i + 1)) (z (i + 1 + 1)) h1 h2
  omega

/-- **Deletion lowers κ by at most one** (Lemma TC (ii): Δκ ∈ {0, 1}). -/
theorem numPeaks_le_skipAt_add_one (hm : 2 ≤ m) {z : ZMod (m + 1) → ℝ} {i : ZMod (m + 1)}
    (h1 : z (i - 1) ≠ z i) (h2 : z i ≠ z (i + 1)) (h3 : z (i - 1) ≠ z (i + 1)) :
    numPeaks z ≤ numPeaks (skipAt z i) + 1 := by
  have := numPeaks_skipAt_add hm z i
  have := peakInd_local_le' (z (i - 1 - 1)) (z (i - 1)) (z i) (z (i + 1)) (z (i + 1 + 1)) h1 h2 h3
  omega

/-- **Lemma VM, combinatorial core (hiding a corner never breaks unimodality).**  Deleting any
entry of a cyclically unimodal cycle of `m + 1 ≥ 3` reals leaves it cyclically unimodal. -/
theorem isCyclicUnimodal_skipAt (hm : 2 ≤ m) {z : ZMod (m + 1) → ℝ} (hz : IsCyclicUnimodal z)
    (i : ZMod (m + 1)) : IsCyclicUnimodal (skipAt z i) := by
  have : Fact (1 < m + 1) := ⟨by omega⟩
  have hinj : Function.Injective (skipAt z i) := hz.1.comp (phi_inj i)
  have hle := numPeaks_skipAt_le hm (i := i) (hz.1.ne (by simp)) (hz.1.ne (by simp))
  have hge := one_le_numPeaks hm hinj
  have h1 : numPeaks z = 1 := hz.2
  exact ⟨hinj, show numPeaks (skipAt z i) = 1 by omega⟩

/-- Lemma TC (ii), constant pair: deleting an entry strictly between its neighbours keeps κ. -/
theorem numPeaks_skipAt_of_between (hm : 2 ≤ m) {z : ZMod (m + 1) → ℝ} {i : ZMod (m + 1)}
    (hb : (z (i - 1) < z i ∧ z i < z (i + 1)) ∨ (z (i + 1) < z i ∧ z i < z (i - 1))) :
    numPeaks (skipAt z i) = numPeaks z := by
  have := numPeaks_skipAt_add hm z i
  unfold peakInd at this
  rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    split_ifs at this <;> first | omega | (exfalso; simp_all; done) | (exfalso; simp_all; linarith)

/-- Lemma TC (ii), rising step `σ = +` (`z (i-1) < z (i+1)`), `x = z i` high: inserting `x`
raises κ by `1 - [b = −]`, `b` the step after `σ`. -/
theorem numPeaks_skipAt_high (hm : 2 ≤ m) {z : ZMod (m + 1) → ℝ} {i : ZMod (m + 1)}
    (h1 : z (i - 1) < z (i + 1)) (h2 : z (i + 1) < z i) :
    numPeaks z + (if z (i + 1 + 1) < z (i + 1) then 1 else 0) = numPeaks (skipAt z i) + 1 := by
  have := numPeaks_skipAt_add hm z i
  unfold peakInd at this
  split_ifs at this ⊢ <;> first | omega | (exfalso; simp_all; done) | (exfalso; simp_all; linarith)

/-- Lemma TC (ii), rising step `σ = +`, `x = z i` low: inserting `x` raises κ by `[a = +]`, `a` the
step before `σ`. -/
theorem numPeaks_skipAt_low (hm : 2 ≤ m) {z : ZMod (m + 1) → ℝ} {i : ZMod (m + 1)}
    (h1 : z (i - 1) < z (i + 1)) (h2 : z i < z (i - 1)) :
    numPeaks z = numPeaks (skipAt z i) + (if z (i - 1 - 1) < z (i - 1) then 1 else 0) := by
  have := numPeaks_skipAt_add hm z i
  unfold peakInd at this
  split_ifs at this ⊢ <;> first | omega | (exfalso; simp_all; done) | (exfalso; simp_all; linarith)

/-- Lemma TC (ii), falling step `σ = −` (`z (i+1) < z (i-1)`), `x = z i` high: inserting `x`
raises κ by `1 - [a = +]`. -/
theorem numPeaks_skipAt_high' (hm : 2 ≤ m) {z : ZMod (m + 1) → ℝ} {i : ZMod (m + 1)}
    (h1 : z (i + 1) < z (i - 1)) (h2 : z (i - 1) < z i) :
    numPeaks z + (if z (i - 1 - 1) < z (i - 1) then 1 else 0) = numPeaks (skipAt z i) + 1 := by
  have := numPeaks_skipAt_add hm z i
  unfold peakInd at this
  split_ifs at this ⊢ <;> first | omega | (exfalso; simp_all; done) | (exfalso; simp_all; linarith)

/-- Lemma TC (ii), falling step `σ = −`, `x = z i` low: inserting `x` raises κ by `[b = −]`. -/
theorem numPeaks_skipAt_low' (hm : 2 ≤ m) {z : ZMod (m + 1) → ℝ} {i : ZMod (m + 1)}
    (h1 : z (i + 1) < z (i - 1)) (h2 : z i < z (i + 1)) :
    numPeaks z = numPeaks (skipAt z i) + (if z (i + 1 + 1) < z (i + 1) then 1 else 0) := by
  have := numPeaks_skipAt_add hm z i
  unfold peakInd at this
  split_ifs at this ⊢ <;> first | omega | (exfalso; simp_all; done) | (exfalso; simp_all; linarith)

end skip

/-- **Lemma TC (i) (a depth tie changes κ by at most one).**  If `z` and `w` make the same strict
comparisons on every ordered pair except `(a, a + 1)` and `(a + 1, a)`, their peak counts differ by
at most one (apply it both ways).  No injectivity is needed. -/
theorem numPeaks_le_add_one_of_flip {k : ℕ} [NeZero k] {z w : ZMod k → ℝ} (a : ZMod k)
    (h : ∀ p q, ¬ (p = a ∧ q = a + 1) → ¬ (p = a + 1 ∧ q = a) → (z p < z q ↔ w p < w q)) :
    numPeaks w ≤ numPeaks z + 1 := by
  set S : Finset (ZMod k) := {a, a + 1} with hS
  have hsd : cycPeaks w \ S = cycPeaks z \ S := by
    ext p
    simp only [hS, mem_sdiff, mem_cycPeaks, mem_insert, mem_singleton, not_or]
    constructor
    · rintro ⟨⟨h1, h2⟩, hpa, hpa1⟩
      exact ⟨⟨(h _ _ (fun hh => hpa1 hh.2) (fun hh => hpa hh.2)).2 h1,
        (h _ _ (fun hh => hpa1 hh.2) (fun hh => hpa hh.2)).2 h2⟩, hpa, hpa1⟩
    · rintro ⟨⟨h1, h2⟩, hpa, hpa1⟩
      exact ⟨⟨(h _ _ (fun hh => hpa1 hh.2) (fun hh => hpa hh.2)).1 h1,
        (h _ _ (fun hh => hpa1 hh.2) (fun hh => hpa hh.2)).1 h2⟩, hpa, hpa1⟩
  have hle : (cycPeaks w ∩ S).card ≤ 1 := by
    refine Finset.card_le_one.2 fun x hx y hy => ?_
    simp only [hS, mem_inter, mem_cycPeaks, mem_insert, mem_singleton] at hx hy
    obtain ⟨⟨hx1, hx2⟩, hx | hx⟩ := hx <;> obtain ⟨⟨hy1, hy2⟩, hy | hy⟩ := hy <;> subst hx hy <;>
      first | rfl | (exfalso; simp only [add_sub_cancel_right] at *; linarith)
  have hA := card_sdiff_add_card_inter (cycPeaks w) S
  have hB := card_sdiff_add_card_inter (cycPeaks z) S
  rw [hsd] at hA
  unfold numPeaks
  omega

/-- **Lemma TC (i), tie form.**  `z` has no tie except possibly the adjacent pair `(a, a + 1)`;
`zp`, `zm` keep every strict comparison of `z` (e.g. the two ways of breaking the tie).  Then
their peak counts differ by at most one. -/
theorem numPeaks_le_add_one_of_tie {k : ℕ} [NeZero k] {z zp zm : ZMod k → ℝ} (a : ZMod k)
    (hz : ∀ p q, z p = z q → p = q ∨ (p = a ∧ q = a + 1) ∨ (p = a + 1 ∧ q = a))
    (hp : ∀ p q, z p < z q → zp p < zp q) (hm : ∀ p q, z p < z q → zm p < zm q) :
    numPeaks zm ≤ numPeaks zp + 1 := by
  refine numPeaks_le_add_one_of_flip a fun p q h1 h2 => ?_
  rcases lt_trichotomy (z p) (z q) with e | e | e
  · exact iff_of_true (hp p q e) (hm p q e)
  · rcases hz p q e with rfl | h | h
    · exact iff_of_false (lt_irrefl _) (lt_irrefl _)
    · exact absurd h h1
    · exact absurd h h2
  · exact iff_of_false (lt_asymm (hp q p e)) (lt_asymm (hm q p e))

end Minimality

end
