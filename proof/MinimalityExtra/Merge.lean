module

public import Mathlib
public import MinimalityExtra

/-!
# The merge lemma on cyclic sequences
-/

@[expose] public section

open Filter Topology

namespace MinimalityExtra

/-- Collapse of the cycle `ZMod (n+2)` onto `ZMod (n+1)` identifying the entries `0` and `1`. -/
def collapse (n : ℕ) (j : ZMod (n + 2)) : ZMod (n + 1) := ((j.val - 1 : ℕ) : ZMod (n + 1))

theorem collapse_val (n : ℕ) (j : ZMod (n + 2)) : (collapse n j).val = j.val - 1 := by
  have := ZMod.val_lt j
  exact ZMod.val_natCast_of_lt (by omega)

theorem zmod_val_one (n : ℕ) : (1 : ZMod (n + 2)).val = 1 := by
  have : Fact (1 < n + 2) := ⟨by omega⟩
  exact ZMod.val_one (n + 2)

theorem collapse_zero (n : ℕ) : collapse n 0 = 0 := by simp [collapse]

theorem collapse_one (n : ℕ) : collapse n 1 = 0 := by
  simp [collapse, zmod_val_one]

theorem collapse_eq_iff (n : ℕ) (i j : ZMod (n + 2)) :
    collapse n i = collapse n j ↔ i = j ∨ (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
  rw [← ZMod.val_injective (n + 1)|>.eq_iff, collapse_val, collapse_val,
    ← (ZMod.val_injective (n + 2)).eq_iff, ← (ZMod.val_injective (n + 2)).eq_iff (a := i) (b := 0),
    ← (ZMod.val_injective (n + 2)).eq_iff (a := j) (b := 1),
    ← (ZMod.val_injective (n + 2)).eq_iff (a := i) (b := 1),
    ← (ZMod.val_injective (n + 2)).eq_iff (a := j) (b := 0)]
  simp only [ZMod.val_zero, zmod_val_one]
  omega

theorem collapse_succ (n : ℕ) (j : ZMod (n + 2)) (hj : j ≠ 0) :
    collapse n (j + 1) = collapse n j + 1 := by
  have hv : (j + 1).val = (j.val + 1) % (n + 2) := by
    rw [ZMod.val_add, zmod_val_one]
  have hj1 : 1 ≤ j.val := by
    rcases Nat.eq_zero_or_pos j.val with h | h
    · exact absurd ((ZMod.val_eq_zero _).mp h) hj
    · exact h
  have hlt := ZMod.val_lt j
  unfold collapse
  rw [hv]
  by_cases h : j.val + 1 < n + 2
  · rw [Nat.mod_eq_of_lt h]
    obtain ⟨t, ht⟩ : ∃ t, j.val = t + 1 := ⟨j.val - 1, by omega⟩
    rw [ht]; simp
  · have h2 : j.val + 1 = n + 2 := by omega
    rw [h2, Nat.mod_self]
    obtain ⟨t, ht⟩ : ∃ t, j.val = t + 1 := ⟨j.val - 1, by omega⟩
    have : t = n := by omega
    rw [ht, this]
    simp

theorem collapse_pred (n : ℕ) (j : ZMod (n + 2)) (hj : j ≠ 1) :
    collapse n (j - 1) = collapse n j - 1 := by
  have h := collapse_succ n (j - 1) (sub_ne_zero.mpr hj)
  rw [sub_add_cancel] at h
  rw [h]; ring

theorem collapse_surj (n : ℕ) (s : ZMod (n + 1)) (hs : s ≠ 0) :
    ∃ j : ZMod (n + 2), j ≠ 0 ∧ j ≠ 1 ∧ collapse n j = s := by
  have hlt := ZMod.val_lt s
  have hs1 : 1 ≤ s.val := by
    rcases Nat.eq_zero_or_pos s.val with h | h
    · exact absurd ((ZMod.val_eq_zero _).mp h) hs
    · exact h
  have hv : (((s.val + 1 : ℕ)) : ZMod (n + 2)).val = s.val + 1 :=
    ZMod.val_natCast_of_lt (by omega)
  refine ⟨((s.val + 1 : ℕ) : ZMod (n + 2)), ?_, ?_, ?_⟩
  · intro h; rw [h] at hv; simp at hv
  · intro h; rw [h, zmod_val_one] at hv; omega
  · unfold collapse; rw [hv]; simp

theorem merge_comb (n : ℕ) (z : ZMod (n + 2) → ℝ) (m : ZMod (n + 1) → ℝ)
    (hm : IsCyclicUnimodal m)
    (hfw : ∀ i j, ¬(i = 0 ∧ j = 1) → ¬(i = 1 ∧ j = 0) →
      m (collapse n i) < m (collapse n j) → z i < z j)
    (h01 : z 0 ≠ z 1)
    (hord : (m (0 - 1) < m 0 ∧ m 0 < m (0 + 1) → z 0 < z 1) ∧
      (m (0 + 1) < m 0 ∧ m 0 < m (0 - 1) → z 1 < z 0)) :
    IsCyclicUnimodal z := by
  obtain ⟨hmi, hS⟩ := hm
  have hn : 1 ≤ n := by
    by_contra hcon
    have : n = 0 := by omega
    subst this
    have h0 : (Finset.univ.filter (fun i : ZMod (0 + 1) => m (i - 1) < m i ∧ m (i + 1) < m i)).card
        = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i _ ⟨h, _⟩
      have hsub : Subsingleton (ZMod (0 + 1)) := inferInstanceAs (Subsingleton (Fin 1))
      rw [Subsingleton.elim (i - 1) i] at h
      exact lt_irrefl _ h
    omega
  have : Fact (1 < n + 2) := ⟨by omega⟩
  have : Fact (1 < n + 1) := ⟨by omega⟩
  have h2 : (1 + 1 : ZMod (n + 2)) ≠ 0 := by
    intro h
    have := congrArg ZMod.val h
    rw [ZMod.val_add, zmod_val_one, ZMod.val_zero, Nat.mod_eq_of_lt (by omega)] at this
    omega
  have hm1 : (0 - 1 : ZMod (n + 2)) ≠ 1 := by
    intro h; apply h2; linear_combination -h
  have hm10 : (0 - 1 : ZMod (n + 2)) ≠ 0 := by simp
  have h10 : (0 + 1 : ZMod (n + 1)) ≠ 0 := by simp
  have h10' : (0 - 1 : ZMod (n + 1)) ≠ 0 := by simp
  have c1 := collapse_one n
  have c0 := collapse_zero n
  have c2 : collapse n (1 + 1) = 0 + 1 := by rw [collapse_succ n 1 one_ne_zero, c1]
  have cm1 : collapse n (0 - 1) = 0 - 1 := by rw [collapse_pred n 0 zero_ne_one, c0]
  have hne : ∀ i j : ZMod (n + 2), i ≠ j → ¬(i = 0 ∧ j = 1) → ¬(i = 1 ∧ j = 0) →
      collapse n i ≠ collapse n j := by
    intro i j h h1 h2 e
    rcases (collapse_eq_iff n i j).mp e with h3 | h3 | h3
    · exact h h3
    · exact h1 h3
    · exact h2 h3
  have hag : ∀ i j, ¬(i = 0 ∧ j = 1) → ¬(i = 1 ∧ j = 0) →
      (z i < z j ↔ m (collapse n i) < m (collapse n j)) := by
    intro i j h1 h2
    constructor
    · intro h
      by_contra hn'
      have hij : i ≠ j := by rintro rfl; exact lt_irrefl _ h
      have hne' := hne i j hij h1 h2
      have : m (collapse n j) < m (collapse n i) :=
        lt_of_le_of_ne (not_lt.mp hn') (fun e => hne' (hmi e.symm))
      have := hfw j i (fun ⟨a, b⟩ => h2 ⟨b, a⟩) (fun ⟨a, b⟩ => h1 ⟨b, a⟩) this
      linarith
    · exact hfw i j h1 h2
  have hA : ∀ j : ZMod (n + 2), j ≠ 0 → j ≠ 1 →
      ((z (j - 1) < z j ∧ z (j + 1) < z j) ↔
        (m (collapse n j - 1) < m (collapse n j) ∧ m (collapse n j + 1) < m (collapse n j))) := by
    intro j hj0 hj1
    have e1 := collapse_pred n j hj1
    have e2 := collapse_succ n j hj0
    have a1 := hag (j - 1) j (fun ⟨_, b⟩ => hj1 b) (fun ⟨_, b⟩ => hj0 b)
    have a2 := hag (j + 1) j (fun ⟨_, b⟩ => hj1 b) (fun ⟨_, b⟩ => hj0 b)
    rw [e1] at a1; rw [e2] at a2
    rw [a1, a2]
  have hout_of : ∀ (s : ZMod (n + 1)),
      (Finset.univ.filter (fun i : ZMod (n + 1) => m (i - 1) < m i ∧ m (i + 1) < m i)) = {s} →
      ∀ j : ZMod (n + 2), j ≠ 0 → j ≠ 1 → (z (j - 1) < z j ∧ z (j + 1) < z j) →
        collapse n j = s := by
    intro s hs j hj0 hj1 hL
    have : collapse n j ∈ (Finset.univ.filter (fun i : ZMod (n + 1) =>
        m (i - 1) < m i ∧ m (i + 1) < m i)) := by
      rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, (hA j hj0 hj1).mp hL⟩
    rw [hs] at this
    exact Finset.mem_singleton.mp this
  have hinj : Function.Injective z := by
    intro i j e
    by_contra hij
    by_cases hp : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)
    · rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h01 e
      · exact h01 e.symm
    · push Not at hp
      have a1 := hag i j (fun ⟨a, b⟩ => hp.1 a b) (fun ⟨a, b⟩ => hp.2 a b)
      have a2 := hag j i (fun ⟨a, b⟩ => hp.2 b a) (fun ⟨a, b⟩ => hp.1 b a)
      have b1 : ¬ m (collapse n i) < m (collapse n j) := fun h => by
        have := a1.mpr h; linarith
      have b2 : ¬ m (collapse n j) < m (collapse n i) := fun h => by
        have := a2.mpr h; linarith
      have : m (collapse n i) = m (collapse n j) :=
        le_antisymm (not_lt.mp b2) (not_lt.mp b1)
      exact hne i j hij (fun ⟨a, b⟩ => hp.1 a b) (fun ⟨a, b⟩ => hp.2 a b) (hmi this)
  refine ⟨hinj, ?_⟩
  obtain ⟨s, hs⟩ := Finset.card_eq_one.mp hS
  by_cases hL : m (0 - 1) < m 0 ∧ m (0 + 1) < m 0
  · -- the merged entry is a maximum
    have hs0 : s = 0 := by
      have : (0 : ZMod (n + 1)) ∈ (Finset.univ.filter (fun i : ZMod (n + 1) =>
        m (i - 1) < m i ∧ m (i + 1) < m i)) := by
        rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hL⟩
      rw [hs] at this
      exact (Finset.mem_singleton.mp this).symm
    subst hs0
    have hout : ∀ j : ZMod (n + 2), j ≠ 0 → j ≠ 1 → ¬ (z (j - 1) < z j ∧ z (j + 1) < z j) := by
      intro j hj0 hj1 hLj
      have := hout_of 0 hs j hj0 hj1 hLj
      rw [← c0, collapse_eq_iff] at this
      rcases this with h | ⟨h, _⟩ | ⟨h, _⟩
      · exact hj0 h
      · exact hj0 h
      · exact hj1 h
    have hz1 : z (0 - 1) < z 0 :=
      (hag (0 - 1) 0 (fun ⟨_, b⟩ => zero_ne_one b) (fun ⟨a, _⟩ => hm1 a)).mpr
        (by rw [cm1, c0]; exact hL.1)
    have hz2 : z (1 + 1) < z 1 :=
      (hag (1 + 1) 1 (fun ⟨a, _⟩ => h2 a) (fun ⟨_, b⟩ => one_ne_zero b)).mpr
        (by rw [c2, c1]; exact hL.2)
    rw [Finset.card_eq_one]
    by_cases hlt : z 1 < z 0
    · refine ⟨0, ?_⟩
      ext j
      rw [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨_, h⟩
        by_contra hj0
        by_cases hj1 : j = 1
        · subst hj1
          have := h.1
          rw [sub_self] at this
          linarith
        · exact hout j hj0 hj1 h
      · rintro rfl
        exact ⟨Finset.mem_univ _, hz1, by rw [zero_add]; exact hlt⟩
    · have hlt' : z 0 < z 1 := lt_of_le_of_ne (not_lt.mp hlt) h01
      refine ⟨1, ?_⟩
      ext j
      rw [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨_, h⟩
        by_contra hj1
        by_cases hj0 : j = 0
        · subst hj0
          have := h.2
          rw [zero_add] at this
          exact hlt this
        · exact hout j hj0 hj1 h
      · rintro rfl
        exact ⟨Finset.mem_univ _, by rw [sub_self]; exact hlt', hz2⟩
  · -- not a maximum: the two entries are not maxima, and the maxima correspond
    have noL0 : ¬ (z (0 - 1) < z 0 ∧ z (0 + 1) < z 0) := by
      rintro ⟨h1, h2'⟩
      have ha : m (0 - 1) < m 0 :=
        (by have := (hag (0 - 1) 0 (fun ⟨_, b⟩ => zero_ne_one b) (fun ⟨a, _⟩ => hm1 a)).mp h1
            rwa [cm1, c0] at this)
      have hb : m 0 < m (0 + 1) :=
        lt_of_le_of_ne (not_lt.mp fun hb => hL ⟨ha, hb⟩) (fun e => h10 (hmi e).symm)
      have := hord.1 ⟨ha, hb⟩
      rw [zero_add] at h2'
      linarith
    have noL1 : ¬ (z (1 - 1) < z 1 ∧ z (1 + 1) < z 1) := by
      rintro ⟨h1, h2'⟩
      rw [sub_self] at h1
      have hb : m (0 + 1) < m 0 :=
        (by have := (hag (1 + 1) 1 (fun ⟨a, _⟩ => h2 a) (fun ⟨_, b⟩ => one_ne_zero b)).mp h2'
            rwa [c2, c1] at this)
      have ha : m 0 < m (0 - 1) :=
        lt_of_le_of_ne (not_lt.mp fun ha => hL ⟨ha, hb⟩) (fun e => h10' (hmi e).symm)
      have := hord.2 ⟨hb, ha⟩
      linarith
    refine Eq.trans (Finset.card_bij (fun j _ => collapse n j) ?_ ?_ ?_) hS
    · intro j hj
      rw [Finset.mem_filter] at hj ⊢
      have hj0 : j ≠ 0 := by rintro rfl; exact noL0 hj.2
      have hj1 : j ≠ 1 := by rintro rfl; exact noL1 hj.2
      exact ⟨Finset.mem_univ _, (hA j hj0 hj1).mp hj.2⟩
    · intro j hj k hk e
      rw [Finset.mem_filter] at hj hk
      have hj0 : j ≠ 0 := by rintro rfl; exact noL0 hj.2
      have hj1 : j ≠ 1 := by rintro rfl; exact noL1 hj.2
      have hk0 : k ≠ 0 := by rintro rfl; exact noL0 hk.2
      have hk1 : k ≠ 1 := by rintro rfl; exact noL1 hk.2
      rcases (collapse_eq_iff n j k).mp e with h | ⟨h, _⟩ | ⟨h, _⟩
      · exact h
      · exact absurd h hj0
      · exact absurd h hj1
    · intro t ht
      rw [Finset.mem_filter] at ht
      have ht0 : t ≠ 0 := by rintro rfl; exact hL ht.2
      obtain ⟨j, hj0, hj1, hj⟩ := collapse_surj n t ht0
      refine ⟨j, ?_, hj⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, (hA j hj0 hj1).mpr ?_⟩
      rw [hj]; exact ht.2

theorem mergeLemma : MergeLemma := by
  intro n α β lam0 m hβ hval hm
  have hval' : ∀ j, α j + β j * lam0 = m (collapse n j) := hval
  have hE : ∀ᶠ lam in 𝓝 lam0, ∀ i j : ZMod (n + 2), ¬(i = 0 ∧ j = 1) → ¬(i = 1 ∧ j = 0) →
      m (collapse n i) < m (collapse n j) → α i + β i * lam < α j + β j * lam := by
    rw [Filter.eventually_all]; intro i
    rw [Filter.eventually_all]; intro j
    by_cases h1 : ¬(i = 0 ∧ j = 1)
    · by_cases h2 : ¬(i = 1 ∧ j = 0)
      · by_cases h3 : m (collapse n i) < m (collapse n j)
        · have hc : ∀ k : ZMod (n + 2), Continuous (fun lam : ℝ => α k + β k * lam) :=
            fun k => by fun_prop
          have := ((hc i).tendsto lam0).eventually_lt ((hc j).tendsto lam0)
            (by rw [hval', hval']; exact h3)
          exact this.mono fun lam h _ _ _ => h
        · exact Filter.Eventually.of_forall fun lam _ _ h => absurd h h3
      · exact Filter.Eventually.of_forall fun lam h _ => absurd h2 (by tauto)
    · exact Filter.Eventually.of_forall fun lam h _ => absurd h1 (by tauto)
  obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.mp hE
  have hD : β 1 - β 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hβ)
  have hcross : α 0 + β 0 * lam0 = α 1 + β 1 * lam0 := by
    rw [hval', hval', collapse_zero, collapse_one]
  have hdiff : ∀ lam, (α 1 + β 1 * lam) - (α 0 + β 0 * lam) = (β 1 - β 0) * (lam - lam0) := by
    intro lam; linear_combination -hcross
  have key : ∀ lam, lam0 - ε < lam → lam < lam0 + ε → lam ≠ lam0 →
      ((m (0 - 1) < m 0 ∧ m 0 < m (0 + 1) → α 0 + β 0 * lam < α 1 + β 1 * lam) ∧
        (m (0 + 1) < m 0 ∧ m 0 < m (0 - 1) → α 1 + β 1 * lam < α 0 + β 0 * lam)) →
      IsCyclicUnimodal (fun j => α j + β j * lam) := by
    intro lam h1 h2 h3 hord
    refine merge_comb n (fun j => α j + β j * lam) m hm ?_ ?_ hord
    · intro i j hi hj hlt
      exact hεP (by rw [Real.dist_eq, abs_sub_lt_iff]; constructor <;> linarith) i j hi hj hlt
    · intro h
      have := hdiff lam
      have h0 : (β 1 - β 0) * (lam - lam0) = 0 := by rw [← this]; linarith
      rcases mul_eq_zero.mp h0 with h4 | h4
      · exact hD h4
      · exact h3 (by linarith)
  have R : ∀ lam, lam0 < lam →
      (0 < β 1 - β 0 → α 0 + β 0 * lam < α 1 + β 1 * lam) ∧
        (β 1 - β 0 < 0 → α 1 + β 1 * lam < α 0 + β 0 * lam) := by
    intro lam h
    have := hdiff lam
    constructor
    · intro hp; nlinarith [mul_pos hp (sub_pos.mpr h)]
    · intro hp; nlinarith [mul_pos_of_neg_of_neg hp (sub_neg.mpr h)]
  have L : ∀ lam, lam < lam0 →
      (0 < β 1 - β 0 → α 1 + β 1 * lam < α 0 + β 0 * lam) ∧
        (β 1 - β 0 < 0 → α 0 + β 0 * lam < α 1 + β 1 * lam) := by
    intro lam h
    have := hdiff lam
    constructor
    · intro hp; nlinarith [mul_neg_of_pos_of_neg hp (sub_neg.mpr h)]
    · intro hp; nlinarith [mul_pos_of_neg_of_neg hp (sub_neg.mpr h)]
  refine ⟨ε, hε, ?_⟩
  by_cases hc2 : m (0 + 1) < m 0 ∧ m 0 < m (0 - 1)
  · have hc1 : ¬ (m (0 - 1) < m 0 ∧ m 0 < m (0 + 1)) := by
      rintro ⟨h1, h2⟩; linarith [hc2.1, hc2.2]
    rcases lt_or_gt_of_ne hD with hp | hp
    · left
      intro lam h1 h2
      exact key lam (by linarith) (by linarith) (by linarith)
        ⟨fun h => absurd h hc1, fun _ => (R lam h1).2 hp⟩
    · right
      intro lam h1 h2
      exact key lam (by linarith) (by linarith) (by linarith)
        ⟨fun h => absurd h hc1, fun _ => (L lam h2).1 hp⟩
  · rcases lt_or_gt_of_ne hD with hp | hp
    · right
      intro lam h1 h2
      exact key lam (by linarith) (by linarith) (by linarith)
        ⟨fun _ => (L lam h2).2 hp, fun h => absurd h hc2⟩
    · left
      intro lam h1 h2
      exact key lam (by linarith) (by linarith) (by linarith)
        ⟨fun _ => (R lam h1).1 hp, fun h => absurd h hc2⟩

#print axioms mergeLemma

end MinimalityExtra
