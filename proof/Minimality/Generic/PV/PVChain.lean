module

public import Minimality.Generic.PV.PVReal
public import Minimality.FaceChain

@[expose] public section


/-! Task 3: chain depths are V-shaped (lower chain) / Λ-shaped (upper chain), and the list-level
Lemma SK bridge `CU (chain ++ R) ↔ CU (skeleton ++ R)`. -/

namespace Minimality
open Finset

/-- A sequence strictly decreasing up to `m`, strictly increasing from `m`. -/
def VShapedSeq {n : ℕ} (f : Fin n → ℝ) : Prop :=
  ∃ m : Fin n, (∀ i j, i < j → j ≤ m → f j < f i) ∧ (∀ i j, m ≤ i → i < j → f i < f j)

theorem vshaped_of_nolocmax {n : ℕ} (f : Fin n → ℝ) (hn : 0 < n) (hinj : Function.Injective f)
    (h : ∀ i j l : Fin n, i < j → j < l → f j < max (f i) (f l)) : VShapedSeq f := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨m, hm⟩ := Finite.exists_min f
  have hlt : ∀ i, i ≠ m → f m < f i := fun i hi =>
    lt_of_le_of_ne (hm i) (fun e => hi (hinj e.symm))
  refine ⟨m, fun i j hij hjm => ?_, fun i j hmi hij => ?_⟩
  · rcases hjm.eq_or_lt with rfl | hjm'
    · exact hlt i (ne_of_lt hij)
    · have h1 := h i j m hij hjm'
      have h2 := hlt j (ne_of_lt hjm')
      rcases le_total (f i) (f m) with h3 | h3
      · rw [max_eq_right h3] at h1; linarith
      · rw [max_eq_left h3] at h1; exact h1
  · rcases hmi.eq_or_lt with rfl | hmi'
    · exact hlt j (ne_of_gt hij)
    · have h1 := h m i j hmi' hij
      have h2 := hlt i (ne_of_gt hmi')
      rcases le_total (f m) (f j) with h3 | h3
      · rw [max_eq_right h3] at h1; exact h1
      · rw [max_eq_left h3] at h1; linarith

theorem vshaped_of_nolocmin {n : ℕ} (f : Fin n → ℝ) (hn : 0 < n) (hinj : Function.Injective f)
    (h : ∀ i j l : Fin n, i < j → j < l → min (f i) (f l) < f j) : VShapedSeq fun i => -f i := by
  refine vshaped_of_nolocmax _ hn (fun a b hab => hinj (neg_injective hab)) fun i j l hij hjl => ?_
  have := h i j l hij hjl
  rw [max_neg_neg]; linarith

/-- Lower chain of a planar set in convex position: second coordinate is V-shaped. -/
theorem lowerChain_vshaped {n : ℕ} (hn : 0 < n) (c : Fin n → ℝ²)
    (hnolocmax : ∀ i j l : Fin n, i < j → j < l → c j 1 < max (c i 1) (c l 1))
    (hinj : Function.Injective fun i => c i 1) : VShapedSeq fun i => c i 1 :=
  vshaped_of_nolocmax _ hn hinj hnolocmax

/-- Upper chain: Λ-shaped. -/
theorem upperChain_lambdashaped {n : ℕ} (hn : 0 < n) (c : Fin n → ℝ²)
    (hnolocmin : ∀ i j l : Fin n, i < j → j < l → min (c i 1) (c l 1) < c j 1)
    (hinj : Function.Injective fun i => c i 1) : VShapedSeq fun i => -(c i 1) :=
  vshaped_of_nolocmin _ hn hinj hnolocmin



/-- **Lemma SK for chains (V-shaped).**  A chain whose depth list is `A ++ B` (`A` strictly decreasing,
`B` strictly increasing) followed by the rest `R` of the rim: the rim is cyclically unimodal iff the
skeleton `(first, extreme, last) ++ R` is (the extreme is omitted when it is an end). -/
theorem CU_chain_V : ∀ (n : ℕ) (A B R : List ℝ) (a e c : ℝ), A.length + B.length = n →
    A.Pairwise (· > ·) → B.Pairwise (· < ·) → (A ++ B ++ R).Nodup → 2 ≤ n →
    (A ++ B).head? = some a → (A ++ B).getLast? = some c → e ∈ A ++ B →
    (∀ x ∈ A ++ B, e ≤ x) → (CU (A ++ B ++ R) ↔ CU (skel1 a e c ++ R)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A B R a e c hn hA hB hnd hn2 ha hc he hmin
  by_cases hA3 : 3 ≤ A.length
  · obtain ⟨a0, y, z, A2, rfl⟩ : ∃ a0 y z A2, A = a0 :: y :: z :: A2 := by
      rcases A with _ | ⟨a0, _ | ⟨y, _ | ⟨z, A2⟩⟩⟩ <;> simp at hA3 ⊢
    have hy : y < a0 := (List.pairwise_cons.mp hA).1 y (by simp)
    have hz : z < y := (List.pairwise_cons.mp (List.pairwise_cons.mp hA).2).1 z (by simp)
    have hdel := CU_del_mid [] a0 y z (A2 ++ B ++ R) (by simpa using hnd)
      (by first | exact Or.inl ⟨by linarith, by linarith⟩ | exact Or.inr ⟨by linarith, by linarith⟩)
    have hsub : (a0 :: z :: A2).Sublist (a0 :: y :: z :: A2) :=
      List.Sublist.cons₂ a0 (List.Sublist.cons y (List.Sublist.refl _))
    have hey : e ≠ y := by
      intro h; subst h
      have := hmin z (by simp); linarith
    have := ih (n - 1) (by simp at hn ⊢; omega) (a0 :: z :: A2) B R a e c (by simp at hn ⊢; omega)
      (hA.sublist hsub) hB (by
        refine List.Nodup.sublist ?_ hnd
        simp only [List.cons_append, List.append_assoc]
        exact List.Sublist.cons₂ a0 (List.Sublist.cons y (List.Sublist.refl _)))
      (by simp at hn ⊢; omega) (by simpa using ha)
      (by simpa [List.getLast?_cons_cons] using hc)
      (by
        simp only [List.mem_append, List.mem_cons] at he ⊢
        rcases he with (h | h | h | h) | h
        · exact Or.inl (Or.inl h)
        · exact absurd h hey
        · exact Or.inl (Or.inr (Or.inl h))
        · exact Or.inl (Or.inr (Or.inr h))
        · exact Or.inr h)
      (by
        intro x hx
        apply hmin
        simp only [List.mem_append, List.mem_cons] at hx ⊢
        tauto)
    simp only [List.cons_append, List.append_assoc, List.nil_append] at hdel this ⊢
    exact hdel.trans this
  by_cases hB3 : 3 ≤ B.length
  · obtain ⟨b1, y, z, B2, rfl⟩ : ∃ b1 y z B2, B = b1 :: y :: z :: B2 := by
      rcases B with _ | ⟨b1, _ | ⟨y, _ | ⟨z, B2⟩⟩⟩ <;> simp at hB3 ⊢
    have hy : b1 < y := (List.pairwise_cons.mp hB).1 y (by simp)
    have hz : y < z := (List.pairwise_cons.mp (List.pairwise_cons.mp hB).2).1 z (by simp)
    have hdel := CU_del_mid A b1 y z (B2 ++ R) (by simpa using hnd)
      (by first | exact Or.inl ⟨by linarith, by linarith⟩ | exact Or.inr ⟨by linarith, by linarith⟩)
    have hsub : (b1 :: z :: B2).Sublist (b1 :: y :: z :: B2) :=
      List.Sublist.cons₂ b1 (List.Sublist.cons y (List.Sublist.refl _))
    have hey : e ≠ y := by
      intro h; subst h
      have := hmin b1 (by simp); linarith
    have := ih (n - 1) (by simp at hn ⊢; omega) A (b1 :: z :: B2) R a e c (by simp at hn ⊢; omega)
      hA (hB.sublist hsub) (by
        refine List.Nodup.sublist ?_ hnd
        simp only [List.append_assoc]
        exact List.Sublist.append (List.Sublist.refl _) (List.Sublist.append
          (List.Sublist.cons₂ b1 (List.Sublist.cons y (List.Sublist.refl _))) (List.Sublist.refl _)))
      (by simp at hn ⊢; omega) (by simpa [List.head?_append] using ha)
      (by simpa [List.getLast?_append, List.getLast?_cons_cons] using hc)
      (by
        simp only [List.mem_append, List.mem_cons] at he ⊢
        rcases he with h | h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact absurd h hey
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h)))
      (by
        intro x hx
        apply hmin
        simp only [List.mem_append, List.mem_cons] at hx ⊢
        tauto)
    simp only [List.cons_append, List.append_assoc, List.nil_append] at hdel this ⊢
    exact hdel.trans this
  -- base cases: |A|, |B| ≤ 2
  rcases A with _ | ⟨a0, _ | ⟨p, _ | ⟨_, _⟩⟩⟩ <;> rcases B with _ | ⟨q, _ | ⟨c', _ | ⟨_, _⟩⟩⟩
  all_goals (try (exfalso; simp at hA3 hB3 hn <;> omega))
  · -- (0,2)
    simp at ha hc he hmin hB hnd ⊢
    obtain ⟨hm1, hm2⟩ := hmin
    subst ha; subst hc
    have : e = q := by rcases he with h1 | h1 <;> first | exact h1 | (exfalso; linarith)
    subst this; simp [skel1_end_l]
  · -- (1,1)
    simp at ha hc he hmin hnd ⊢
    subst ha; subst hc
    rcases he with rfl | rfl <;> simp [skel1_end_l, skel1_end_r]
  · -- (1,2)
    simp at ha hc he hmin hB hnd ⊢
    obtain ⟨hm1, hm2, hm3⟩ := hmin
    subst ha; subst hc
    have hne : a0 ≠ q := by intro h; subst h; simp at hnd
    rcases lt_trichotomy a0 q with h | h | h
    · have : e = a0 := by rcases he with h1 | h1 | h1 <;> first | exact h1 | (exfalso; linarith)
      subst this
      have hdel := CU_del_mid [] e q c' R (by simpa using hnd)
        (by first | exact Or.inl ⟨by linarith, by linarith⟩ | exact Or.inr ⟨by linarith, by linarith⟩)
      rw [skel1_end_l]; simpa using hdel
    · exact absurd (by first | exact h | exact h.symm) hne
    · have : e = q := by rcases he with h1 | h1 | h1 <;> first | exact h1 | (exfalso; linarith)
      subst this
      rw [skel1_mid (by intro h'; linarith) (by intro h'; linarith)]; simp
  · -- (2,0)
    simp at ha hc he hmin hA hnd ⊢
    obtain ⟨hm1, hm2⟩ := hmin
    subst ha; subst hc
    have : e = p := by rcases he with h1 | h1 <;> first | exact h1 | (exfalso; linarith)
    subst this; simp [skel1_end_r]
  · -- (2,1)
    simp at ha hc he hmin hA hnd ⊢
    obtain ⟨hm1, hm2, hm3⟩ := hmin
    subst ha; subst hc
    have hne : p ≠ q := by intro h; subst h; simp at hnd
    rcases lt_trichotomy p q with h | h | h
    · have : e = p := by rcases he with h1 | h1 | h1 <;> first | exact h1 | (exfalso; linarith)
      subst this
      rw [skel1_mid (by intro h'; linarith) (by intro h'; linarith)]; simp
    · exact absurd (by first | exact h | exact h.symm) hne
    · have : e = q := by rcases he with h1 | h1 | h1 <;> first | exact h1 | (exfalso; linarith)
      subst this
      have hdel := CU_del_mid [] a0 p e R (by simpa using hnd)
        (by first | exact Or.inl ⟨by linarith, by linarith⟩ | exact Or.inr ⟨by linarith, by linarith⟩)
      rw [skel1_end_r]; simpa using hdel
  · -- (2,2)
    simp at ha hc he hmin hA hB hnd ⊢
    obtain ⟨hm1, hm2, hm3, hm4⟩ := hmin
    subst ha; subst hc
    have hne : p ≠ q := by intro h; subst h; simp at hnd
    rcases lt_trichotomy p q with h | h | h
    · have : e = p := by rcases he with h1 | h1 | h1 | h1 <;> first | exact h1 | (exfalso; linarith)
      subst this
      have hdel := CU_del_mid [a0] e q c' R (by simpa using hnd)
        (by first | exact Or.inl ⟨by linarith, by linarith⟩ | exact Or.inr ⟨by linarith, by linarith⟩)
      rw [skel1_mid (by intro h'; linarith) (by intro h'; linarith)]; simpa using hdel
    · exact absurd (by first | exact h | exact h.symm) hne
    · have : e = q := by rcases he with h1 | h1 | h1 | h1 <;> first | exact h1 | (exfalso; linarith)
      subst this
      have hdel := CU_del_mid [] a0 p e (c' :: R) (by simpa using hnd)
        (by first | exact Or.inl ⟨by linarith, by linarith⟩ | exact Or.inr ⟨by linarith, by linarith⟩)
      rw [skel1_mid (by intro h'; linarith) (by intro h'; linarith)]; simpa using hdel


/-- **Lemma SK for chains (Λ-shaped).**  A chain whose depth list is `A ++ B` (`A` strictly increasing,
`B` strictly increasing) followed by the rest `R` of the rim: the rim is cyclically unimodal iff the
skeleton `(first, extreme, last) ++ R` is (the extreme is omitted when it is an end). -/
theorem CU_chain_L : ∀ (n : ℕ) (A B R : List ℝ) (a e c : ℝ), A.length + B.length = n →
    A.Pairwise (· < ·) → B.Pairwise (· > ·) → (A ++ B ++ R).Nodup → 2 ≤ n →
    (A ++ B).head? = some a → (A ++ B).getLast? = some c → e ∈ A ++ B →
    (∀ x ∈ A ++ B, x ≤ e) → (CU (A ++ B ++ R) ↔ CU (skel1 a e c ++ R)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A B R a e c hn hA hB hnd hn2 ha hc he hmin
  by_cases hA3 : 3 ≤ A.length
  · obtain ⟨a0, y, z, A2, rfl⟩ : ∃ a0 y z A2, A = a0 :: y :: z :: A2 := by
      rcases A with _ | ⟨a0, _ | ⟨y, _ | ⟨z, A2⟩⟩⟩ <;> simp at hA3 ⊢
    have hy : a0 < y := (List.pairwise_cons.mp hA).1 y (by simp)
    have hz : y < z := (List.pairwise_cons.mp (List.pairwise_cons.mp hA).2).1 z (by simp)
    have hdel := CU_del_mid [] a0 y z (A2 ++ B ++ R) (by simpa using hnd)
      (by first | exact Or.inl ⟨by linarith, by linarith⟩ | exact Or.inr ⟨by linarith, by linarith⟩)
    have hsub : (a0 :: z :: A2).Sublist (a0 :: y :: z :: A2) :=
      List.Sublist.cons₂ a0 (List.Sublist.cons y (List.Sublist.refl _))
    have hey : e ≠ y := by
      intro h; subst h
      have := hmin z (by simp); linarith
    have := ih (n - 1) (by simp at hn ⊢; omega) (a0 :: z :: A2) B R a e c (by simp at hn ⊢; omega)
      (hA.sublist hsub) hB (by
        refine List.Nodup.sublist ?_ hnd
        simp only [List.cons_append, List.append_assoc]
        exact List.Sublist.cons₂ a0 (List.Sublist.cons y (List.Sublist.refl _)))
      (by simp at hn ⊢; omega) (by simpa using ha)
      (by simpa [List.getLast?_cons_cons] using hc)
      (by
        simp only [List.mem_append, List.mem_cons] at he ⊢
        rcases he with (h | h | h | h) | h
        · exact Or.inl (Or.inl h)
        · exact absurd h hey
        · exact Or.inl (Or.inr (Or.inl h))
        · exact Or.inl (Or.inr (Or.inr h))
        · exact Or.inr h)
      (by
        intro x hx
        apply hmin
        simp only [List.mem_append, List.mem_cons] at hx ⊢
        tauto)
    simp only [List.cons_append, List.append_assoc, List.nil_append] at hdel this ⊢
    exact hdel.trans this
  by_cases hB3 : 3 ≤ B.length
  · obtain ⟨b1, y, z, B2, rfl⟩ : ∃ b1 y z B2, B = b1 :: y :: z :: B2 := by
      rcases B with _ | ⟨b1, _ | ⟨y, _ | ⟨z, B2⟩⟩⟩ <;> simp at hB3 ⊢
    have hy : y < b1 := (List.pairwise_cons.mp hB).1 y (by simp)
    have hz : z < y := (List.pairwise_cons.mp (List.pairwise_cons.mp hB).2).1 z (by simp)
    have hdel := CU_del_mid A b1 y z (B2 ++ R) (by simpa using hnd)
      (by first | exact Or.inl ⟨by linarith, by linarith⟩ | exact Or.inr ⟨by linarith, by linarith⟩)
    have hsub : (b1 :: z :: B2).Sublist (b1 :: y :: z :: B2) :=
      List.Sublist.cons₂ b1 (List.Sublist.cons y (List.Sublist.refl _))
    have hey : e ≠ y := by
      intro h; subst h
      have := hmin b1 (by simp); linarith
    have := ih (n - 1) (by simp at hn ⊢; omega) A (b1 :: z :: B2) R a e c (by simp at hn ⊢; omega)
      hA (hB.sublist hsub) (by
        refine List.Nodup.sublist ?_ hnd
        simp only [List.append_assoc]
        exact List.Sublist.append (List.Sublist.refl _) (List.Sublist.append
          (List.Sublist.cons₂ b1 (List.Sublist.cons y (List.Sublist.refl _))) (List.Sublist.refl _)))
      (by simp at hn ⊢; omega) (by simpa [List.head?_append] using ha)
      (by simpa [List.getLast?_append, List.getLast?_cons_cons] using hc)
      (by
        simp only [List.mem_append, List.mem_cons] at he ⊢
        rcases he with h | h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact absurd h hey
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h)))
      (by
        intro x hx
        apply hmin
        simp only [List.mem_append, List.mem_cons] at hx ⊢
        tauto)
    simp only [List.cons_append, List.append_assoc, List.nil_append] at hdel this ⊢
    exact hdel.trans this
  -- base cases: |A|, |B| ≤ 2
  rcases A with _ | ⟨a0, _ | ⟨p, _ | ⟨_, _⟩⟩⟩ <;> rcases B with _ | ⟨q, _ | ⟨c', _ | ⟨_, _⟩⟩⟩
  all_goals (try (exfalso; simp at hA3 hB3 hn <;> omega))
  · -- (0,2)
    simp at ha hc he hmin hB hnd ⊢
    obtain ⟨hm1, hm2⟩ := hmin
    subst ha; subst hc
    have : e = q := by rcases he with h1 | h1 <;> first | exact h1 | (exfalso; linarith)
    subst this; simp [skel1_end_l]
  · -- (1,1)
    simp at ha hc he hmin hnd ⊢
    subst ha; subst hc
    rcases he with rfl | rfl <;> simp [skel1_end_l, skel1_end_r]
  · -- (1,2)
    simp at ha hc he hmin hB hnd ⊢
    obtain ⟨hm1, hm2, hm3⟩ := hmin
    subst ha; subst hc
    have hne : a0 ≠ q := by intro h; subst h; simp at hnd
    rcases lt_trichotomy q a0 with h | h | h
    · have : e = a0 := by rcases he with h1 | h1 | h1 <;> first | exact h1 | (exfalso; linarith)
      subst this
      have hdel := CU_del_mid [] e q c' R (by simpa using hnd)
        (by first | exact Or.inl ⟨by linarith, by linarith⟩ | exact Or.inr ⟨by linarith, by linarith⟩)
      rw [skel1_end_l]; simpa using hdel
    · exact absurd (by first | exact h | exact h.symm) hne
    · have : e = q := by rcases he with h1 | h1 | h1 <;> first | exact h1 | (exfalso; linarith)
      subst this
      rw [skel1_mid (by intro h'; linarith) (by intro h'; linarith)]; simp
  · -- (2,0)
    simp at ha hc he hmin hA hnd ⊢
    obtain ⟨hm1, hm2⟩ := hmin
    subst ha; subst hc
    have : e = p := by rcases he with h1 | h1 <;> first | exact h1 | (exfalso; linarith)
    subst this; simp [skel1_end_r]
  · -- (2,1)
    simp at ha hc he hmin hA hnd ⊢
    obtain ⟨hm1, hm2, hm3⟩ := hmin
    subst ha; subst hc
    have hne : p ≠ q := by intro h; subst h; simp at hnd
    rcases lt_trichotomy q p with h | h | h
    · have : e = p := by rcases he with h1 | h1 | h1 <;> first | exact h1 | (exfalso; linarith)
      subst this
      rw [skel1_mid (by intro h'; linarith) (by intro h'; linarith)]; simp
    · exact absurd (by first | exact h | exact h.symm) hne
    · have : e = q := by rcases he with h1 | h1 | h1 <;> first | exact h1 | (exfalso; linarith)
      subst this
      have hdel := CU_del_mid [] a0 p e R (by simpa using hnd)
        (by first | exact Or.inl ⟨by linarith, by linarith⟩ | exact Or.inr ⟨by linarith, by linarith⟩)
      rw [skel1_end_r]; simpa using hdel
  · -- (2,2)
    simp at ha hc he hmin hA hB hnd ⊢
    obtain ⟨hm1, hm2, hm3, hm4⟩ := hmin
    subst ha; subst hc
    have hne : p ≠ q := by intro h; subst h; simp at hnd
    rcases lt_trichotomy q p with h | h | h
    · have : e = p := by rcases he with h1 | h1 | h1 | h1 <;> first | exact h1 | (exfalso; linarith)
      subst this
      have hdel := CU_del_mid [a0] e q c' R (by simpa using hnd)
        (by first | exact Or.inl ⟨by linarith, by linarith⟩ | exact Or.inr ⟨by linarith, by linarith⟩)
      rw [skel1_mid (by intro h'; linarith) (by intro h'; linarith)]; simpa using hdel
    · exact absurd (by first | exact h | exact h.symm) hne
    · have : e = q := by rcases he with h1 | h1 | h1 | h1 <;> first | exact h1 | (exfalso; linarith)
      subst this
      have hdel := CU_del_mid [] a0 p e (c' :: R) (by simpa using hnd)
        (by first | exact Or.inl ⟨by linarith, by linarith⟩ | exact Or.inr ⟨by linarith, by linarith⟩)
      rw [skel1_mid (by intro h'; linarith) (by intro h'; linarith)]; simpa using hdel

end Minimality
