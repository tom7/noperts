module

public import Minimality.Thm73

@[expose] public section


/-! Lemma SK (skeleton): deleting a cycle entry strictly between its neighbours preserves
cyclic unimodality (`Minimality.IsCyclicUnimodal`, the predicate of `isRupert_of_tilted_unimodal'`). -/

namespace Minimality
open Finset

/-- The cycle `z` with the entry at `i` removed, read from `i+1` around to `i-1`. -/
def skipAt {m : ℕ} [NeZero m] (z : ZMod (m + 1) → ℝ) (i : ZMod (m + 1)) : ZMod m → ℝ :=
  fun j => z (i + 1 + (j.val : ZMod (m + 1)))

section phi
variable {m : ℕ} [NeZero m]

/-- the embedding `ZMod m → ZMod (m+1) \ {i}` used by `skipAt`. -/
def phi (i : ZMod (m + 1)) (j : ZMod m) : ZMod (m + 1) := i + 1 + (j.val : ZMod (m + 1))

lemma phi_inj (i : ZMod (m + 1)) : Function.Injective (phi i) := by
  intro a b h
  have h2 : ((a.val : ℕ) : ZMod (m + 1)) = ((b.val : ℕ) : ZMod (m + 1)) := by
    simpa [phi] using h
  have ha := a.val_lt
  have hb := b.val_lt
  have := congrArg ZMod.val h2
  rw [ZMod.val_cast_of_lt (by omega), ZMod.val_cast_of_lt (by omega)] at this
  exact ZMod.val_injective m this

lemma phi_succ (i : ZMod (m + 1)) (j : ZMod m) (hj : j ≠ -1) :
    phi i (j + 1) = phi i j + 1 := by
  have h1 : j.val + 1 ≠ m := by
    intro h
    apply hj
    have : j + 1 = 0 := by
      have e : ((j.val + 1 : ℕ) : ZMod m) = j + 1 := by
        rw [Nat.cast_add, ZMod.natCast_zmod_val]; simp
      rw [← e, h]; simp
    exact eq_neg_of_add_eq_zero_left this
  have h2 : j.val + 1 < m := lt_of_le_of_ne j.val_lt h1
  have e : ((j.val + 1 : ℕ) : ZMod m) = j + 1 := by
    rw [Nat.cast_add, ZMod.natCast_zmod_val]; simp
  have hv : (j + 1).val = j.val + 1 := by rw [← e, ZMod.val_cast_of_lt h2]
  simp only [phi, hv]; push_cast; ring

lemma phi_pred (i : ZMod (m + 1)) (j : ZMod m) (hj : j ≠ 0) :
    phi i (j - 1) = phi i j - 1 := by
  have hp : 0 < j.val := by
    rcases Nat.eq_zero_or_pos j.val with h | h
    · exact absurd ((ZMod.val_eq_zero j).mp h) hj
    · exact h
  have e : ((j.val - 1 : ℕ) : ZMod m) = j - 1 := by
    rw [Nat.cast_sub hp, ZMod.natCast_zmod_val]; simp
  have hv : (j - 1).val = j.val - 1 := by
    rw [← e, ZMod.val_cast_of_lt (by have := j.val_lt; omega)]
  simp only [phi, hv]
  have : ((j.val : ℕ) : ZMod (m + 1)) = ((j.val - 1 : ℕ) : ZMod (m + 1)) + 1 := by
    rw [← Nat.cast_succ]; congr 1; omega
  rw [this]; ring

lemma phi_zero (i : ZMod (m + 1)) : phi i 0 = i + 1 := by simp [phi]

lemma phi_neg_one (i : ZMod (m + 1)) : phi i (-1) = i - 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by have := NeZero.pos m; omega⟩
  have hv : (-1 : ZMod (n + 1)).val = n := ZMod.val_neg_one n
  have h0 : ((n + 2 : ℕ) : ZMod (n + 1 + 1)) = 0 := ZMod.natCast_self _
  have : ((n : ℕ) : ZMod (n + 1 + 1)) = -2 := by
    have : ((n : ℕ) : ZMod (n + 1 + 1)) + 2 = 0 := by exact_mod_cast h0
    exact eq_neg_of_add_eq_zero_left this
  simp only [phi, hv, this]; ring

lemma phi_surj (i a : ZMod (m + 1)) (ha : a ≠ i) : ∃ j, phi i j = a := by
  have hne : a - i - 1 ≠ -1 := by intro h; apply ha; linear_combination h
  refine ⟨((a - i - 1).val : ZMod m), ?_⟩
  have hlt : (a - i - 1).val < m := by
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by have := NeZero.pos m; omega⟩
    have h1 := ZMod.val_lt (a - i - 1)
    have h2 : (a - i - 1).val ≠ n + 1 := by
      intro h
      apply hne
      have : (a - i - 1) = (((a - i - 1).val : ℕ) : ZMod (n + 1 + 1)) := (ZMod.natCast_zmod_val _).symm
      have h3 : (((n + 1 : ℕ)) : ZMod (n + 1 + 1)) + 1 = 0 := by exact_mod_cast ZMod.natCast_self (n + 1 + 1)
      rw [this, h]; exact eq_neg_of_add_eq_zero_left h3
    omega
  have hv : (((a - i - 1).val : ZMod m)).val = (a - i - 1).val := ZMod.val_cast_of_lt hlt
  simp only [phi, hv, ZMod.natCast_zmod_val]; ring


/-- local maxima of the shortened cycle correspond to those of the original. -/
lemma lm_iff (hm : 2 ≤ m) (z : ZMod (m + 1) → ℝ) (i : ZMod (m + 1))
    (hb : (z (i - 1) < z i ∧ z i < z (i + 1)) ∨ (z (i + 1) < z i ∧ z i < z (i - 1)))
    (j : ZMod m) :
    (z (phi i (j - 1)) < z (phi i j) ∧ z (phi i (j + 1)) < z (phi i j)) ↔
    (z (phi i j - 1) < z (phi i j) ∧ z (phi i j + 1) < z (phi i j)) := by
  haveI : Fact (1 < m) := ⟨by omega⟩
  have hn : (0 : ZMod m) ≠ -1 := by
    intro h; apply one_ne_zero (α := ZMod m); simpa using h.symm
  have e1 : z (i - 1) < z (i + 1) ↔ z i < z (i + 1) := by
    rcases hb with h | h <;> constructor <;> intro <;> linarith [h.1, h.2]
  have e2 : z (i + 1) < z (i - 1) ↔ z i < z (i - 1) := by
    rcases hb with h | h <;> constructor <;> intro <;> linarith [h.1, h.2]
  by_cases h0 : j = 0
  · subst h0
    have a1 : phi i (0 - 1) = i - 1 := by rw [zero_sub, phi_neg_one]
    have a2 : phi i (0 + 1) = phi i 0 + 1 := by rw [zero_add]; have := phi_succ i 0 hn; simpa using this
    rw [a1, a2, phi_zero]
    have : i + 1 - 1 = i := by ring
    rw [this]
    constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨?_, h2⟩
    · exact e1.mp h1
    · exact e1.mpr h1
  by_cases h1 : j = -1
  · subst h1
    have a1 : phi i (-1 - 1) = phi i (-1) - 1 := phi_pred i (-1) (Ne.symm hn)
    have a2 : phi i (-1 + 1) = i + 1 := by rw [neg_add_cancel, phi_zero]
    rw [a1, a2, phi_neg_one]
    have : i - 1 + 1 = i := by ring
    rw [this]
    constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩
    · exact e2.mp h2
    · exact e2.mpr h2
  · rw [phi_pred i j h0, phi_succ i j h1]

theorem skipAt_unimodal_iff (hm : 2 ≤ m) (z : ZMod (m + 1) → ℝ) (i : ZMod (m + 1))
    (hinj : Function.Injective z)
    (hb : (z (i - 1) < z i ∧ z i < z (i + 1)) ∨ (z (i + 1) < z i ∧ z i < z (i - 1))) :
    IsCyclicUnimodal z ↔ IsCyclicUnimodal (skipAt z i) := by
  have hw : Function.Injective (skipAt z i) := hinj.comp (phi_inj i)
  have key : (Finset.univ.filter (fun a : ZMod (m + 1) => z (a - 1) < z a ∧ z (a + 1) < z a)) =
      (Finset.univ.filter (fun j : ZMod m => skipAt z i (j - 1) < skipAt z i j ∧
        skipAt z i (j + 1) < skipAt z i j)).image (phi i) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro ha
      have hai : a ≠ i := by
        rintro rfl
        rcases hb with h | h <;> linarith [h.1, h.2, ha.1, ha.2]
      obtain ⟨j, rfl⟩ := phi_surj i a hai
      exact ⟨j, (lm_iff hm z i hb j).mpr ha, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact (lm_iff hm z i hb j).mp hj
  unfold IsCyclicUnimodal
  rw [key, Finset.card_image_of_injective _ (phi_inj i)]
  exact ⟨fun h => ⟨hw, h.2⟩, fun h => ⟨hinj, h.2⟩⟩

end phi


/-! ### Cyclic unimodality of lists, rotation, and deletion -/

/-- Unimodality of the cycle `k` entries `f 0, …, f (k-1)`. -/
def CUn (k : ℕ) (f : ℕ → ℝ) : Prop :=
  ∃ h : k ≠ 0, @IsCyclicUnimodal k ⟨h⟩ (fun i : ZMod k => f i.val)

/-- Cyclic unimodality of a list read as a cycle. -/
def CU (l : List ℝ) : Prop := CUn l.length (fun i => l.getD i 0)

lemma isCyclicUnimodal_shift {k : ℕ} [NeZero k] (z : ZMod k → ℝ) (s : ZMod k) :
    IsCyclicUnimodal z ↔ IsCyclicUnimodal (fun i => z (i + s)) := by
  unfold IsCyclicUnimodal
  have hi : Function.Injective z ↔ Function.Injective (fun i => z (i + s)) := by
    constructor
    · intro h; exact h.comp (add_left_injective s)
    · intro h a b hab
      have := @h (a - s) (b - s) (by simpa using hab)
      simpa using this
  have hc : (Finset.univ.filter (fun i : ZMod k => z (i - 1) < z i ∧ z (i + 1) < z i)).card =
      (Finset.univ.filter (fun i : ZMod k => z (i + s - 1) < z (i + s) ∧
        z (i + s + 1) < z (i + s))).card := by
    refine Finset.card_equiv (Equiv.subRight s) ?_
    intro a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.subRight_apply]
    have : a - s + s = a := by ring
    rw [this]
  have hc2 : (Finset.univ.filter (fun i : ZMod k => (fun i => z (i + s)) (i - 1) < (fun i => z (i + s)) i ∧
        (fun i => z (i + s)) (i + 1) < (fun i => z (i + s)) i)).card =
      (Finset.univ.filter (fun i : ZMod k => z (i + s - 1) < z (i + s) ∧
        z (i + s + 1) < z (i + s))).card := by
    congr 1; ext i; simp only [Finset.mem_filter]
    have e1 : i - 1 + s = i + s - 1 := by ring
    have e2 : i + 1 + s = i + s + 1 := by ring
    simp only [e1, e2]
  rw [hi, hc, ← hc2]

lemma CUn_rot (k : ℕ) (f : ℕ → ℝ) : CUn k f ↔ CUn k (fun i => f ((i + 1) % k)) := by
  unfold CUn
  by_cases hk : k = 0
  · simp [hk]
  · simp only [ne_eq, hk, not_false_eq_true, exists_true_left]
    haveI : NeZero k := ⟨hk⟩
    have := isCyclicUnimodal_shift (fun i : ZMod k => f i.val) 1
    refine this.trans ?_
    have h : (fun i : ZMod k => f (i + 1).val) = fun i : ZMod k => f ((i.val + 1) % k) := by
      funext i
      congr 1
      rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod]
    rw [h]

lemma CUn_congr {k : ℕ} {f g : ℕ → ℝ} (h : ∀ i < k, f i = g i) : CUn k f ↔ CUn k g := by
  unfold CUn
  by_cases hk : k = 0
  · simp [hk]
  · haveI : NeZero k := ⟨hk⟩
    have : (fun i : ZMod k => f i.val) = fun i : ZMod k => g i.val := by
      funext i; exact h _ i.val_lt
    simp only [ne_eq, hk, not_false_eq_true, exists_true_left, this]

lemma CU_rotate_one (x : ℝ) (l : List ℝ) : CU (x :: l) ↔ CU (l ++ [x]) := by
  unfold CU
  have hl : (l ++ [x]).length = l.length + 1 := by simp
  rw [hl]
  refine (CUn_rot _ _).trans (CUn_congr ?_)
  intro i hi
  simp only [List.length_cons] at hi ⊢
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
  · rw [Nat.mod_eq_of_lt (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]

lemma CU_rot (l₁ l₂ : List ℝ) : CU (l₁ ++ l₂) ↔ CU (l₂ ++ l₁) := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons x r ih =>
    have := ih (l₂ ++ [x])
    simp only [List.cons_append]
    rw [CU_rotate_one, List.append_assoc]
    simpa using this


lemma CU_cons_iff (b : ℝ) (q : List ℝ) (hq : 2 ≤ q.length) (hnd : (b :: q).Nodup)
    (hb : (q.getD (q.length - 1) 0 < b ∧ b < q.getD 0 0) ∨
      (q.getD 0 0 < b ∧ b < q.getD (q.length - 1) 0)) :
    CU (b :: q) ↔ CU q := by
  unfold CU CUn
  have h1 : (b :: q).length ≠ 0 := by simp
  have h2 : q.length ≠ 0 := by omega
  simp only [ne_eq, h1, h2, not_false_eq_true, exists_true_left]
  haveI : NeZero q.length := ⟨h2⟩
  set m := q.length with hmdef
  let z : ZMod (m + 1) → ℝ := fun i => (b :: q).getD i.val 0
  have hinj : Function.Injective z := by
    intro i j hij
    apply ZMod.val_injective
    have hi := i.val_lt
    have hj := j.val_lt
    simp only [z, List.getD_eq_getElem?_getD] at hij
    rw [List.getElem?_eq_getElem (by simpa using hi), List.getElem?_eq_getElem (by simpa using hj)] at hij
    simpa [hnd.getElem_inj_iff] using hij
  have hv : ∀ j : ZMod m, ((1 : ZMod (m + 1)) + (j.val : ZMod (m + 1))).val = j.val + 1 := by
    intro j
    have : (1 + (j.val : ZMod (m + 1))) = ((j.val + 1 : ℕ) : ZMod (m + 1)) := by push_cast; ring
    rw [this, ZMod.val_cast_of_lt (by have := j.val_lt; omega)]
  have hskip : skipAt z 0 = fun i : ZMod m => q.getD i.val 0 := by
    funext j
    simp only [skipAt, z, zero_add, hv, List.getD_cons_succ]
  have hz0 : z 0 = b := by simp [z]
  have hz1 : z (0 + 1) = q.getD 0 0 := by
    have := hv (0 : ZMod m)
    simp only [ZMod.val_zero, Nat.cast_zero, add_zero, zero_add] at this ⊢
    simp [z, this]
  have hzm : z (0 - 1) = q.getD (m - 1) 0 := by
    obtain ⟨n, hn⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    have : (0 - 1 : ZMod (m + 1)).val = m := by
      rw [zero_sub, hn]; exact ZMod.val_neg_one (n + 1)
    simp only [z, this]
    rw [hn]; simp
  have := skipAt_unimodal_iff hq z 0 hinj (by rw [hz0, hz1, hzm]; exact hb)
  rw [hskip] at this
  exact this


/-- Lemma SK for lists, with an arbitrary prefix: an entry strictly between its neighbours may be
deleted without affecting cyclic unimodality (the entries being distinct). -/
theorem CU_del_mid (p : List ℝ) (a b c : ℝ) (t : List ℝ) (hnd : (p ++ a :: b :: c :: t).Nodup)
    (hb : (a < b ∧ b < c) ∨ (c < b ∧ b < a)) :
    CU (p ++ a :: b :: c :: t) ↔ CU (p ++ a :: c :: t) := by
  have e1 : p ++ a :: b :: c :: t = (p ++ [a]) ++ (b :: c :: t) := by simp
  have e2 : p ++ a :: c :: t = (p ++ [a]) ++ (c :: t) := by simp
  have hperm : (b :: (c :: t ++ (p ++ [a]))).Perm (p ++ a :: b :: c :: t) := by
    rw [e1]
    refine List.Perm.trans ?_ (List.perm_append_comm)
    simpa using List.Perm.refl _
  have hnd' : (b :: (c :: t ++ (p ++ [a]))).Nodup := hperm.nodup_iff.mpr hnd
  rw [e1, e2, CU_rot (p ++ [a]) (b :: c :: t), CU_rot (p ++ [a]) (c :: t)]
  have := CU_cons_iff b (c :: t ++ (p ++ [a])) (by simp; omega) (by simpa using hnd') (by
    have h1 : (c :: t ++ (p ++ [a])).getD 0 0 = c := by simp
    have h2 : (c :: t ++ (p ++ [a])).getD ((c :: t ++ (p ++ [a])).length - 1) 0 = a := by
      have e : c :: t ++ (p ++ [a]) = (c :: t ++ p) ++ [a] := by simp
      rw [e]
      generalize c :: t ++ p = L
      simp [List.getD_eq_getElem?_getD]
    rw [h1, h2]; rcases hb with h | h
    · left; exact h
    · right; exact h)
  simpa using this


/-- Deleting the interior of a strictly monotone run (`r` is `<` or `>`). -/
theorem CU_del_run (r : ℝ → ℝ → Prop)
    (hr : ∀ x y z, r x y → r y z → (x < y ∧ y < z) ∨ (z < y ∧ y < x))
    (p S : List ℝ) (t : List ℝ) (a c : ℝ) (hnd : (p ++ a :: (S ++ c :: t)).Nodup)
    (hch : (a :: (S ++ [c])).Pairwise r) :
    CU (p ++ a :: (S ++ c :: t)) ↔ CU (p ++ a :: c :: t) := by
  induction S generalizing a with
  | nil => simp
  | cons b S' ih =>
    have hab : r a b := by
      simp only [List.cons_append, List.pairwise_cons] at hch
      exact hch.1 b (by simp)
    have hch' : (a :: (S' ++ [c])).Pairwise r := by
      simp only [List.cons_append, List.pairwise_cons] at hch ⊢
      exact ⟨fun x hx => hch.1 x (by simp at hx ⊢; tauto), hch.2.2⟩
    have hnd' : (p ++ a :: (S' ++ c :: t)).Nodup := by
      refine hnd.sublist ?_
      exact List.Sublist.append (List.Sublist.refl p)
        (List.Sublist.cons₂ a (List.Sublist.append (List.sublist_cons_self b S') (List.Sublist.refl _)))
    cases S' with
    | nil =>
      have hbc : r b c := by
        simp only [List.cons_append, List.pairwise_cons] at hch
        exact hch.2.1 c (by simp)
      have := CU_del_mid p a b c t (by simpa using hnd) (hr a b c hab hbc)
      simpa using this
    | cons s S'' =>
      have hbs : r b s := by
        simp only [List.cons_append, List.pairwise_cons] at hch
        exact hch.2.1 s (by simp)
      have h1 := CU_del_mid p a b s (S'' ++ c :: t) (by simpa using hnd) (hr a b s hab hbs)
      have h2 := ih a (by simpa using hnd') hch'
      simp only [List.cons_append] at h1 h2 ⊢
      exact h1.trans h2

/-- V-run: strictly decreasing `a, D…, m` then strictly increasing `m, U…, c`; only `a, m, c`
survive in the skeleton. -/
theorem CU_del_Vrun (p D U t : List ℝ) (a m c : ℝ)
    (hnd : (p ++ a :: (D ++ m :: (U ++ c :: t))).Nodup)
    (hD : (a :: (D ++ [m])).Pairwise (· > ·)) (hU : (m :: (U ++ [c])).Pairwise (· < ·)) :
    CU (p ++ a :: (D ++ m :: (U ++ c :: t))) ↔ CU (p ++ a :: m :: c :: t) := by
  have h1 := CU_del_run (· > ·) (fun x y z h1 h2 => Or.inr ⟨h2, h1⟩) p D (U ++ c :: t) a m
    hnd hD
  have h2 := CU_del_run (· < ·) (fun x y z h1 h2 => Or.inl ⟨h1, h2⟩) (p ++ [a]) U t m c
    (by
      have : (p ++ a :: m :: (U ++ c :: t)).Nodup := by
        refine hnd.sublist ?_
        exact List.Sublist.append (List.Sublist.refl p)
          (List.Sublist.cons₂ a (List.sublist_append_right D _))
      simpa using this) hU
  simp only [List.append_assoc, List.singleton_append, List.cons_append] at h1 h2 ⊢
  exact h1.trans h2

/-- Λ-run: strictly increasing `a, …, M` then strictly decreasing `M, …, c`. -/
theorem CU_del_Lrun (p D U t : List ℝ) (a M c : ℝ)
    (hnd : (p ++ a :: (D ++ M :: (U ++ c :: t))).Nodup)
    (hD : (a :: (D ++ [M])).Pairwise (· < ·)) (hU : (M :: (U ++ [c])).Pairwise (· > ·)) :
    CU (p ++ a :: (D ++ M :: (U ++ c :: t))) ↔ CU (p ++ a :: M :: c :: t) := by
  have h1 := CU_del_run (· < ·) (fun x y z h1 h2 => Or.inl ⟨h1, h2⟩) p D (U ++ c :: t) a M
    hnd hD
  have h2 := CU_del_run (· > ·) (fun x y z h1 h2 => Or.inr ⟨h2, h1⟩) (p ++ [a]) U t M c
    (by
      have : (p ++ a :: M :: (U ++ c :: t)).Nodup := by
        refine hnd.sublist ?_
        exact List.Sublist.append (List.Sublist.refl p)
          (List.Sublist.cons₂ a (List.sublist_append_right D _))
      simpa using this) hU
  simp only [List.append_assoc, List.singleton_append, List.cons_append] at h1 h2 ⊢
  exact h1.trans h2

/-- Bridge to the tree's predicate: a `ZMod k` cycle is the list of its values at `0, …, k-1`. -/
theorem CU_ofFn {k : ℕ} [NeZero k] (z : ZMod k → ℝ) :
    CU (List.ofFn fun i : Fin k => z ((i : ℕ) : ZMod k)) ↔ IsCyclicUnimodal z := by
  unfold CU
  rw [List.length_ofFn]
  have hk : k ≠ 0 := NeZero.ne k
  refine (CUn_congr (g := fun i => z ((i : ℕ) : ZMod k)) ?_).trans ?_
  · intro i hi
    simp [List.getD_eq_getElem?_getD, hi]
  · unfold CUn
    simp only [ne_eq, hk, not_false_eq_true, exists_true_left, ZMod.natCast_zmod_val]

end Minimality
