module

public import Minimality.TriQuad

@[expose] public section

/-!
# Upper and lower chains of a finite point set

The frame theorems of `TriQuad.lean` and `TriFaces.lean` take each face as a
point set `Q` in its `(t, z)`-plane together with chains (`ChainOK`): the
upper and lower boundary from the apex to the point of largest `t`.  Here such
chains are built for any finite point set with distinct `t`, no three points
collinear, and every other point at `t > 0` (gift wrapping: from each chain
point, the next one is the point to its right of largest slope).
-/

namespace Minimality

/-- Prepend `x` to the sequence `f`. -/
def consSeq (x : ℝ) (f : ℕ → ℝ) : ℕ → ℝ
  | 0 => x
  | l + 1 => f l

@[simp] theorem consSeq_zero (x : ℝ) (f : ℕ → ℝ) : consSeq x f 0 = x := rfl

@[simp] theorem consSeq_succ (x : ℝ) (f : ℕ → ℝ) (l : ℕ) : consSeq x f (l + 1) = f l := rfl

/-- An upper chain of `S` from `c`: increasing in `t`, through points of `S`,
ending at the point of largest `t`, every other point of `S` strictly below
each segment. -/
structure ChainFrom (S : Finset (ℝ × ℝ)) (c : ℝ × ℝ) (m : ℕ) (ca cz : ℕ → ℝ) : Prop where
  start : ca 0 = c.1 ∧ cz 0 = c.2
  inc : ∀ l, l < m → ca l < ca (l + 1)
  mem : ∀ l, l ≤ m → (ca l, cz l) ∈ S
  far : ∀ q ∈ S, q ≠ (ca m, cz m) → q.1 < ca m
  side : ∀ q ∈ S, ∀ l, l < m → q ≠ (ca l, cz l) → q ≠ (ca (l + 1), cz (l + 1)) →
    (ca (l + 1) - ca l) * (q.2 - cz l) - (cz (l + 1) - cz l) * (q.1 - ca l) < 0

/-- A finite set of points `(d q, h q)` with `d q > 0` lies strictly below some
line of slope `σ` through the origin. -/
theorem exists_slope_above {α : Type*} [DecidableEq α] (T : Finset α) (d h : α → ℝ)
    (hd : ∀ q ∈ T, 0 < d q) : ∃ σ : ℝ, ∀ q ∈ T, h q < σ * d q := by
  induction T using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert q T hq ih =>
    obtain ⟨σ, hσ⟩ := ih (fun p hp => hd p (Finset.mem_insert_of_mem hp))
    have hq0 := hd q (Finset.mem_insert_self q T)
    refine ⟨max σ (h q / d q + 1), fun p hp => ?_⟩
    rcases Finset.mem_insert.mp hp with rfl | hp
    · have e : (h p / d p + 1) * d p = h p + d p := by field_simp
      have := mul_le_mul_of_nonneg_right (le_max_right σ (h p / d p + 1)) hq0.le
      linarith
    · have := mul_le_mul_of_nonneg_right (le_max_left σ (h q / d q + 1))
        (hd p (Finset.mem_insert_of_mem hp)).le
      linarith [hσ p hp]

/-- A finite set of points strictly below a line of slope `σ` through the origin,
with `d q > 0`, lies strictly below a line of some smaller slope. -/
theorem exists_lt_slope {α : Type*} [DecidableEq α] (T : Finset α) (d h : α → ℝ) (σ : ℝ)
    (hd : ∀ q ∈ T, 0 < d q ∧ h q < σ * d q) : ∃ σ' < σ, ∀ q ∈ T, h q < σ' * d q := by
  induction T using Finset.induction_on with
  | empty => exact ⟨σ - 1, by linarith, by simp⟩
  | insert q T hq ih =>
    obtain ⟨σ1, hσ1, hT⟩ := ih (fun p hp => hd p (Finset.mem_insert_of_mem hp))
    obtain ⟨hq0, hqσ⟩ := hd q (Finset.mem_insert_self q T)
    have hsq : h q / d q < σ := by rw [div_lt_iff₀ hq0]; exact hqσ
    refine ⟨max σ1 ((h q / d q + σ) / 2), max_lt hσ1 (by linarith), fun p hp => ?_⟩
    rcases Finset.mem_insert.mp hp with rfl | hp
    · have e : h p / d p * d p = h p := by field_simp
      have := mul_lt_mul_of_pos_right
        (show h p / d p < max σ1 ((h p / d p + σ) / 2) from
          lt_of_lt_of_le (by linarith) (le_max_right _ _)) hq0
      linarith
    · have := mul_le_mul_of_nonneg_right (le_max_left σ1 ((h q / d q + σ) / 2))
        (hd p (Finset.mem_insert_of_mem hp)).1.le
      linarith [hT p hp]

set_option maxHeartbeats 1000000 in
/-- **Gift wrapping.**  A finite set with distinct `t`, no three points
collinear, and a strict supporting line of slope `σ` at `c ∈ S` has an upper
chain from `c`. -/
theorem exists_chainFrom (S : Finset (ℝ × ℝ)) (hinj : Set.InjOn Prod.fst (S : Set (ℝ × ℝ)))
    (hcol : ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → p ≠ r → q ≠ r →
      (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1) ≠ 0) :
    ∀ (k : ℕ) (c : ℝ × ℝ) (σ : ℝ), c ∈ S → (S.filter (fun q => c.1 < q.1)).card = k →
      (∀ q ∈ S, q ≠ c → q.2 < c.2 + σ * (q.1 - c.1)) →
      ∃ m ca cz, ChainFrom S c m ca cz := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro c σ hc hk hσ
  set R := S.filter (fun q => c.1 < q.1) with hR
  have neq : ∀ q ∈ S, q ≠ c → q.1 ≠ c.1 := fun q hq hne h => hne (hinj hq hc h)
  rcases R.eq_empty_or_nonempty with hRe | hRn
  · -- `c` is the far point
    refine ⟨0, fun _ => c.1, fun _ => c.2, ⟨rfl, rfl⟩, fun l hl => absurd hl (Nat.not_lt_zero _),
      fun l _ => by simpa using hc, ?_, fun q _ l hl => absurd hl (Nat.not_lt_zero _)⟩
    intro q hq hne
    have hnR : q ∉ R := by rw [hRe]; exact Finset.notMem_empty q
    rw [hR, Finset.mem_filter] at hnR
    push Not at hnR
    exact lt_of_le_of_ne (hnR hq) (neq q hq (by simpa using hne))
  -- the next point: largest slope from `c`
  obtain ⟨n, hnR, hnmax⟩ := R.exists_max_image (fun q => (q.2 - c.2) / (q.1 - c.1)) hRn
  rw [hR, Finset.mem_filter] at hnR
  obtain ⟨hnS, hcn⟩ := hnR
  have hdn : 0 < n.1 - c.1 := by linarith
  set σ' := (n.2 - c.2) / (n.1 - c.1) with hσ'
  have hn2 : n.2 = c.2 + σ' * (n.1 - c.1) := by rw [hσ']; field_simp; ring
  have hnc : n ≠ c := fun h => by rw [h] at hcn; exact lt_irrefl _ hcn
  have hσσ : σ' < σ := by
    have := hσ n hnS hnc
    rw [hσ', div_lt_iff₀ hdn]; linarith
  -- every point is on or below the line `c n`
  have below : ∀ q ∈ S, q.2 ≤ c.2 + σ' * (q.1 - c.1) := by
    intro q hq
    by_cases hqc : q = c
    · rw [hqc]; simp
    rcases lt_or_gt_of_ne (neq q hq hqc) with hlt | hgt
    · have := hσ q hq hqc
      have : σ * (q.1 - c.1) ≤ σ' * (q.1 - c.1) :=
        mul_le_mul_of_nonpos_right hσσ.le (by linarith)
      linarith
    · have hm := hnmax q (by rw [hR, Finset.mem_filter]; exact ⟨hq, hgt⟩)
      have hd : 0 < q.1 - c.1 := by linarith
      rw [div_le_iff₀ hd] at hm
      linarith
  -- the first segment `c n`
  have side0 : ∀ q ∈ S, q ≠ c → q ≠ n →
      (n.1 - c.1) * (q.2 - c.2) - (n.2 - c.2) * (q.1 - c.1) < 0 := by
    intro q hq hqc hqn
    have h1 := below q hq
    have hle : (n.1 - c.1) * (q.2 - c.2) - (n.2 - c.2) * (q.1 - c.1) ≤ 0 := by
      rw [hn2]
      have := mul_le_mul_of_nonneg_left (show q.2 - c.2 ≤ σ' * (q.1 - c.1) by linarith) hdn.le
      nlinarith
    exact lt_of_le_of_ne hle (hcol c hc n hnS q hq (Ne.symm hnc) (Ne.symm hqc) (Ne.symm hqn))
  -- a strict supporting line at `n`
  obtain ⟨σ'', hσ'', hright⟩ := exists_lt_slope (S.filter (fun q => n.1 < q.1))
    (fun q => q.1 - n.1) (fun q => q.2 - n.2) σ' (by
      intro q hq
      rw [Finset.mem_filter] at hq
      refine ⟨by linarith [hq.2], ?_⟩
      have hqc : q ≠ c := fun h => by rw [h] at hq; linarith [hq.2]
      have hqn : q ≠ n := fun h => by rw [h] at hq; exact lt_irrefl _ hq.2
      have := side0 q hq.1 hqc hqn
      rw [hn2] at this ⊢
      have hd : 0 < q.1 - n.1 := by linarith [hq.2]
      nlinarith)
  have hσn : ∀ q ∈ S, q ≠ n → q.2 < n.2 + σ'' * (q.1 - n.1) := by
    intro q hq hqn
    rcases lt_or_gt_of_ne (fun h => hqn (hinj hq hnS h)) with hlt | hgt
    · have h1 := below q hq
      have : σ' * (q.1 - n.1) < σ'' * (q.1 - n.1) :=
        mul_lt_mul_of_neg_right hσ'' (by linarith)
      linarith
    · have := hright q (by rw [Finset.mem_filter]; exact ⟨hq, hgt⟩)
      linarith
  -- the rest of the chain, from `n`
  have hlt : (S.filter (fun q => n.1 < q.1)).card < k := by
    rw [← hk]
    apply Finset.card_lt_card
    refine ⟨fun q hq => ?_, fun h => ?_⟩
    · rw [Finset.mem_filter] at hq ⊢; exact ⟨hq.1, by linarith [hq.2]⟩
    · have := h (show n ∈ R by rw [hR, Finset.mem_filter]; exact ⟨hnS, hcn⟩)
      rw [Finset.mem_filter] at this; exact lt_irrefl _ this.2
  obtain ⟨m, ca, cz, C⟩ := ih _ hlt n σ'' hnS rfl hσn
  refine ⟨m + 1, consSeq c.1 ca, consSeq c.2 cz, ⟨rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro l hl
    cases l with
    | zero => simp only [consSeq_zero, zero_add, consSeq_succ]; rw [C.start.1]; exact hcn
    | succ l => simp only [consSeq_succ]; exact C.inc l (by omega)
  · intro l hl
    cases l with
    | zero => simpa using hc
    | succ l => simp only [consSeq_succ]; exact C.mem l (by omega)
  · simpa using C.far
  · intro q hq l hl h1 h2
    cases l with
    | zero =>
      simp only [consSeq_zero, zero_add, consSeq_succ, C.start.1, C.start.2] at h1 h2 ⊢
      exact side0 q hq (by simpa using h1) (by simpa using h2)
    | succ l =>
      simp only [consSeq_succ] at h1 h2 ⊢
      exact C.side q hq l (by omega) h1 h2

/-- **Upper and lower chains of a finite point set** with the apex `(0, z0)`,
every other point at `t > 0`, distinct `t`, and no three points collinear. -/
theorem exists_chainOK (S : Finset (ℝ × ℝ)) (z0 : ℝ) (h0 : (0, z0) ∈ S)
    (hpos : ∀ q ∈ S, q ≠ (0, z0) → 0 < q.1) (hne : ∃ q ∈ S, q ≠ (0, z0))
    (hinj : Set.InjOn Prod.fst (S : Set (ℝ × ℝ)))
    (hcol : ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → p ≠ r → q ≠ r →
      (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1) ≠ 0)
    (s : ℝ) (hs : s = 1 ∨ s = -1) :
    ∃ m ca cz, ChainOK (fun a z => (a, z) ∈ S) z0 s m ca cz := by
  classical
  -- reflect for the lower chain
  set S' := S.image (fun q : ℝ × ℝ => (q.1, s * q.2)) with hS'
  have hss : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  have memS' : ∀ q : ℝ × ℝ, q ∈ S' ↔ (q.1, s * q.2) ∈ S := by
    intro q; rw [hS', Finset.mem_image]
    constructor
    · rintro ⟨p, hp, rfl⟩; simpa [← mul_assoc, hss] using hp
    · intro h; exact ⟨_, h, by simp [← mul_assoc, hss]⟩
  have hinj' : Set.InjOn Prod.fst (S' : Set (ℝ × ℝ)) := by
    intro p hp q hq h
    have e := hinj ((memS' p).mp hp) ((memS' q).mp hq) h
    simp only [Prod.mk.injEq] at e
    have : p.2 = q.2 := by
      have := congrArg (fun x => s * x) e.2; simpa [← mul_assoc, hss] using this
    exact Prod.ext h this
  have hcol' : ∀ p ∈ S', ∀ q ∈ S', ∀ r ∈ S', p ≠ q → p ≠ r → q ≠ r →
      (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1) ≠ 0 := by
    intro p hp q hq r hr hpq hpr hqr
    have ne : ∀ x y : ℝ × ℝ, x ≠ y → (x.1, s * x.2) ≠ (y.1, s * y.2) := by
      intro x y hxy h; apply hxy
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.1 (by have := congrArg (fun x => s * x) h.2; simpa [← mul_assoc, hss] using this)
    have := hcol _ ((memS' p).mp hp) _ ((memS' q).mp hq) _ ((memS' r).mp hr) (ne _ _ hpq)
      (ne _ _ hpr) (ne _ _ hqr)
    intro h; apply this
    simp only
    linear_combination s * h
  have h0' : (0, s * z0) ∈ S' := (memS' _).mpr (by simpa [← mul_assoc, hss] using h0)
  have hpos' : ∀ q ∈ S', q ≠ (0, s * z0) → 0 < q.1 := by
    intro q hq hne
    refine hpos (q.1, s * q.2) ((memS' q).mp hq) (fun h => hne ?_)
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 (by rw [← h.2, ← mul_assoc, hss, one_mul])
  obtain ⟨σ, hσ⟩ := exists_slope_above (S'.erase (0, s * z0)) Prod.fst
    (fun q => q.2 - s * z0) (fun q hq => hpos' q (Finset.mem_of_mem_erase hq)
      (Finset.ne_of_mem_erase hq))
  obtain ⟨m, ca, cz, C⟩ := exists_chainFrom S' hinj' hcol' _ (0, s * z0) σ h0' rfl (by
    intro q hq hne
    have := hσ q (Finset.mem_erase.mpr ⟨hne, hq⟩)
    simp only at this ⊢; linarith)
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · exfalso
      obtain ⟨q, hq, hq0⟩ := hne
      have hq' : (q.1, s * q.2) ∈ S' := (memS' _).mpr (by simpa [← mul_assoc, hss] using hq)
      have hqne : (q.1, s * q.2) ≠ (0, s * z0) := by
        intro h; apply hq0; simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1 (by have := congrArg (fun x => s * x) h.2; simpa [← mul_assoc, hss] using this)
      have h1 := hpos' _ hq' hqne
      by_cases he : (q.1, s * q.2) = (ca 0, cz 0)
      · have := congrArg Prod.fst he; simp only at this
        rw [C.start.1] at this; simp at this; linarith
      · have := C.far _ hq' he; rw [C.start.1] at this; simp at this; linarith
    · exact h
  refine ⟨m, ca, fun l => s * cz l, hm, ⟨C.start.1, by simp [C.start.2, ← mul_assoc, hss]⟩,
    C.inc, fun l hl => ?_, fun a z hq hn => ?_, fun a z hq l hl h1 h2 => ?_⟩
  · have := (memS' _).mp (C.mem l hl); simpa using this
  · have hq' : (a, s * z) ∈ S' := (memS' _).mpr (by simpa [← mul_assoc, hss] using hq)
    refine C.far _ hq' (fun h => hn ?_)
    simp only [Prod.mk.injEq] at h
    exact ⟨h.1, by rw [← h.2, ← mul_assoc, hss, one_mul]⟩
  · have hq' : (a, s * z) ∈ S' := (memS' _).mpr (by simpa [← mul_assoc, hss] using hq)
    have ne : ∀ l, ¬ (a = ca l ∧ z = s * cz l) → (a, s * z) ≠ (ca l, cz l) := by
      intro l h e; apply h
      simp only [Prod.mk.injEq] at e
      exact ⟨e.1, by rw [← e.2, ← mul_assoc, hss, one_mul]⟩
    have := C.side _ hq' l hl (ne l h1) (ne (l + 1) h2)
    simp only at this
    have e : s * ((ca (l + 1) - ca l) * (z - s * cz l) - (s * cz (l + 1) - s * cz l) * (a - ca l)) =
        (ca (l + 1) - ca l) * (s * z - cz l) - (cz (l + 1) - cz l) * (a - ca l) := by
      linear_combination (-((ca (l + 1) - ca l) * cz l + (cz (l + 1) - cz l) * (a - ca l))) * hss
    rw [e]; exact this

end Minimality

end
