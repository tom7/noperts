module

public import Minimality.Generic.PV.SK
public import Minimality.Thm73

@[expose] public section


/-! Task 2: the pure-real skeleton lemma of Lemma PV (paper §3 "Same signs" / "Mixed"). -/

namespace Minimality
open Finset

/-- cyclic strict local maximum at position `j` of a list -/
def lm (l : List ℝ) (j : ℕ) : Prop :=
  l.getD ((j + l.length - 1) % l.length) 0 < l.getD j 0 ∧ l.getD ((j + 1) % l.length) 0 < l.getD j 0

theorem CU_of_unique (l : List ℝ) (hnd : l.Nodup) (hl : 2 ≤ l.length) (i : ℕ) (hi : i < l.length)
    (hm : lm l i) (hu : ∀ j < l.length, lm l j → j = i) : CU l := by
  have hn : l.length ≠ 0 := by omega
  unfold CU CUn
  refine ⟨hn, ?_⟩
  have : NeZero l.length := ⟨hn⟩
  set n := l.length with hndef
  have hnn : 1 < n := by omega
  have : Fact (1 < n) := ⟨hnn⟩
  have hv1 : ∀ j : ZMod n, (j + 1).val = (j.val + 1) % n := by
    intro j; rw [ZMod.val_add, ZMod.val_one]
  have hvm : ∀ j : ZMod n, (j - 1).val = (j.val + n - 1) % n := by
    intro j
    have : j - 1 = j + ((n - 1 : ℕ) : ZMod n) := by
      rw [Nat.cast_sub (by omega)]; simp [sub_eq_add_neg]
    rw [this, ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : n - 1 < n)]
    have : (j.val + (n - 1)) = (j.val + n - 1) := by omega
    rw [this]
  refine ⟨?_, ?_⟩
  · intro a b hab
    apply ZMod.val_injective
    have ha := a.val_lt
    have hb := b.val_lt
    simp only [List.getD_eq_getElem?_getD] at hab
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hab
    simpa [hnd.getElem_inj_iff] using hab
  · rw [Finset.card_eq_one]
    refine ⟨(i : ZMod n), ?_⟩
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      have hj := j.val_lt
      have := hu j.val hj (by
        unfold lm
        rw [hv1, hvm] at h
        simpa [hndef] using h)
      apply ZMod.val_injective
      rw [this, ZMod.val_natCast, Nat.mod_eq_of_lt hi]
    · rintro rfl
      rw [hv1, hvm, ZMod.val_natCast, Nat.mod_eq_of_lt hi]
      simpa [hndef, lm] using hm

end Minimality

namespace Minimality

/-- One face's contribution to the skeleton: the end `a`, the extreme `e` (omitted if it is an end),
the other end `b`. -/
noncomputable def skel1 (a e b : ℝ) : List ℝ := if e = a ∨ e = b then [a, b] else [a, e, b]

/-- Skeleton cycle `(A₁, e₁, B₁, B₂, e₂, A₂)` with `eᵢ` omitted when it equals an end. -/
noncomputable def skelList (a₁ e₁ b₁ b₂ e₂ a₂ : ℝ) : List ℝ := skel1 a₁ e₁ b₁ ++ skel1 b₂ e₂ a₂

set_option hygiene false in
macro "cu_at " i:term : tactic => `(tactic| (
  refine CU_of_unique _ ?_ (by simp) $i (by simp) ?_ ?_
  · simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true]
    repeat' apply And.intro
    all_goals (intro h; first | linarith | exact absurd h ‹_› | exact absurd h.symm ‹_› | exact hx _ (by simp) _ (by simp) h | exact hx _ (by simp) _ (by simp) h.symm)
  · simp [lm]; constructor <;> linarith
  · intro j hj
    (try simp only [List.length_cons, List.length_nil, Nat.reduceAdd] at hj)
    interval_cases j <;> first | (intro _; rfl) | (intro hl; simp [lm] at hl; exfalso; (try obtain ⟨hl1, hl2⟩ := hl); linarith)))

theorem skel1_end_l (a b : ℝ) : skel1 a a b = [a, b] := by simp [skel1]
theorem skel1_end_r (a b : ℝ) : skel1 a b b = [a, b] := by simp [skel1]
theorem skel1_mid {a e b : ℝ} (h1 : e ≠ a) (h2 : e ≠ b) : skel1 a e b = [a, e, b] := by simp [skel1, h1, h2]

macro "cu_any" : tactic => `(tactic| first | cu_at 0 | cu_at 1 | cu_at 2 | cu_at 3 | cu_at 4 | cu_at 5)

/-- shape of a V-piece -/
theorem shapeV {a e b : ℝ} (hab : a ≠ b) (h : e ≤ a ∧ e ≤ b) :
    (e = a ∧ a < b) ∨ (e = b ∧ b < a) ∨ (e < a ∧ e < b) := by
  rcases h.1.eq_or_lt with h1 | h1
  · left; exact ⟨h1, lt_of_le_of_ne (h1 ▸ h.2) hab⟩
  · rcases h.2.eq_or_lt with h2 | h2
    · right; left; exact ⟨h2, lt_of_le_of_ne (h2 ▸ h.1) hab.symm⟩
    · right; right; exact ⟨h1, h2⟩

/-- shape of a Λ-piece -/
theorem shapeL {a e b : ℝ} (hab : a ≠ b) (h : a ≤ e ∧ b ≤ e) :
    (e = a ∧ b < a) ∨ (e = b ∧ a < b) ∨ (a < e ∧ b < e) := by
  rcases h.1.eq_or_lt with h1 | h1
  · left; exact ⟨h1.symm, lt_of_le_of_ne (h1 ▸ h.2) hab.symm⟩
  · rcases h.2.eq_or_lt with h2 | h2
    · right; left; exact ⟨h2.symm, lt_of_le_of_ne (h2 ▸ h.1) hab⟩
    · right; right; exact ⟨h1, h2⟩

theorem skel_VL_up (a1 e1 b1 b2 e2 a2 : ℝ)
    (hs1 : (e1 = a1 ∧ a1 < b1) ∨ (e1 = b1 ∧ b1 < a1) ∨ (e1 < a1 ∧ e1 < b1))
    (hs2 : (e2 = a2 ∧ b2 < a2) ∨ (e2 = b2 ∧ a2 < b2) ∨ (a2 < e2 ∧ b2 < e2))
    (hab1 : a1 ≠ b1) (hab2 : a2 ≠ b2) (hx : ∀ x ∈ [a1, e1, b1], ∀ y ∈ [a2, e2, b2], x ≠ y)
    (hb : b1 < b2) (ha : a1 < a2) : CU (skelList a1 e1 b1 b2 e2 a2) := by
  rcases hs1 with ⟨rfl, s1⟩ | ⟨rfl, s1⟩ | ⟨s1, t1⟩ <;>
  rcases hs2 with ⟨rfl, s2⟩ | ⟨rfl, s2⟩ | ⟨s2, t2⟩
  all_goals (simp only [skelList, skel1_end_l, skel1_end_r])
  all_goals (try rw [skel1_mid])
  all_goals (try rw [skel1_mid])
  all_goals (try simp only [List.cons_append, List.nil_append])
  all_goals (first | (intro h; linarith) | cu_any)


theorem skel_LV_dn (a1 e1 b1 b2 e2 a2 : ℝ)
    (hs1 : (e1 = a1 ∧ b1 < a1) ∨ (e1 = b1 ∧ a1 < b1) ∨ (a1 < e1 ∧ b1 < e1))
    (hs2 : (e2 = a2 ∧ a2 < b2) ∨ (e2 = b2 ∧ b2 < a2) ∨ (e2 < a2 ∧ e2 < b2))
    (hab1 : a1 ≠ b1) (hab2 : a2 ≠ b2) (hx : ∀ x ∈ [a1, e1, b1], ∀ y ∈ [a2, e2, b2], x ≠ y)
    (hb : b2 < b1) (ha : a2 < a1) : CU (skelList a1 e1 b1 b2 e2 a2) := by
  rcases hs1 with ⟨rfl, s1⟩ | ⟨rfl, s1⟩ | ⟨s1, t1⟩ <;>
  rcases hs2 with ⟨rfl, s2⟩ | ⟨rfl, s2⟩ | ⟨s2, t2⟩
  all_goals (simp only [skelList, skel1_end_l, skel1_end_r])
  all_goals (try rw [skel1_mid])
  all_goals (try rw [skel1_mid])
  all_goals (try simp only [List.cons_append, List.nil_append])
  all_goals (first | (intro h; linarith) | (exfalso; linarith) | cu_any)

theorem skel_VV_minus (a1 e1 b1 b2 e2 a2 : ℝ)
    (hs1 : (e1 = a1 ∧ a1 < b1) ∨ (e1 = b1 ∧ b1 < a1) ∨ (e1 < a1 ∧ e1 < b1))
    (hs2 : (e2 = a2 ∧ a2 < b2) ∨ (e2 = b2 ∧ b2 < a2) ∨ (e2 < a2 ∧ e2 < b2))
    (hab1 : a1 ≠ b1) (hab2 : a2 ≠ b2) (hx : ∀ x ∈ [a1, e1, b1], ∀ y ∈ [a2, e2, b2], x ≠ y)
    (hb : b1 < b2) (ha : a2 < a1)
    (hc : e1 = a1 ∨ e2 = b2) : CU (skelList a1 e1 b1 b2 e2 a2) := by
  rcases hc with hc | hc <;>
  rcases hs1 with ⟨rfl, s1⟩ | ⟨rfl, s1⟩ | ⟨s1, t1⟩ <;>
  rcases hs2 with ⟨rfl, s2⟩ | ⟨rfl, s2⟩ | ⟨s2, t2⟩
  all_goals (simp only [skelList, skel1_end_l, skel1_end_r])
  all_goals (try rw [skel1_mid])
  all_goals (try rw [skel1_mid])
  all_goals (try simp only [List.cons_append, List.nil_append])
  all_goals (first | (intro h; linarith) | (exfalso; linarith) | cu_any)

theorem skel_LL_minus (a1 e1 b1 b2 e2 a2 : ℝ)
    (hs1 : (e1 = a1 ∧ b1 < a1) ∨ (e1 = b1 ∧ a1 < b1) ∨ (a1 < e1 ∧ b1 < e1))
    (hs2 : (e2 = a2 ∧ b2 < a2) ∨ (e2 = b2 ∧ a2 < b2) ∨ (a2 < e2 ∧ b2 < e2))
    (hab1 : a1 ≠ b1) (hab2 : a2 ≠ b2) (hx : ∀ x ∈ [a1, e1, b1], ∀ y ∈ [a2, e2, b2], x ≠ y)
    (hb : b1 < b2) (ha : a2 < a1)
    (hc : e1 = b1 ∨ e2 = a2) : CU (skelList a1 e1 b1 b2 e2 a2) := by
  rcases hc with hc | hc <;>
  rcases hs1 with ⟨rfl, s1⟩ | ⟨rfl, s1⟩ | ⟨s1, t1⟩ <;>
  rcases hs2 with ⟨rfl, s2⟩ | ⟨rfl, s2⟩ | ⟨s2, t2⟩
  all_goals (simp only [skelList, skel1_end_l, skel1_end_r])
  all_goals (try rw [skel1_mid])
  all_goals (try rw [skel1_mid])
  all_goals (try simp only [List.cons_append, List.nil_append])
  all_goals (first | (intro h; linarith) | (exfalso; linarith) | cu_any)

theorem skel_LL_plus (a1 e1 b1 b2 e2 a2 : ℝ)
    (hs1 : (e1 = a1 ∧ b1 < a1) ∨ (e1 = b1 ∧ a1 < b1) ∨ (a1 < e1 ∧ b1 < e1))
    (hs2 : (e2 = a2 ∧ b2 < a2) ∨ (e2 = b2 ∧ a2 < b2) ∨ (a2 < e2 ∧ b2 < e2))
    (hab1 : a1 ≠ b1) (hab2 : a2 ≠ b2) (hx : ∀ x ∈ [a1, e1, b1], ∀ y ∈ [a2, e2, b2], x ≠ y)
    (hb : b2 < b1) (ha : a1 < a2)
    (hc : e1 = a1 ∨ e2 = b2) : CU (skelList a1 e1 b1 b2 e2 a2) := by
  rcases hc with hc | hc <;>
  rcases hs1 with ⟨rfl, s1⟩ | ⟨rfl, s1⟩ | ⟨s1, t1⟩ <;>
  rcases hs2 with ⟨rfl, s2⟩ | ⟨rfl, s2⟩ | ⟨s2, t2⟩
  all_goals (simp only [skelList, skel1_end_l, skel1_end_r])
  all_goals (try rw [skel1_mid])
  all_goals (try rw [skel1_mid])
  all_goals (try simp only [List.cons_append, List.nil_append])
  all_goals (first | (intro h; linarith) | (exfalso; linarith) | cu_any)

theorem skel_VV_plus (a1 e1 b1 b2 e2 a2 : ℝ)
    (hs1 : (e1 = a1 ∧ a1 < b1) ∨ (e1 = b1 ∧ b1 < a1) ∨ (e1 < a1 ∧ e1 < b1))
    (hs2 : (e2 = a2 ∧ a2 < b2) ∨ (e2 = b2 ∧ b2 < a2) ∨ (e2 < a2 ∧ e2 < b2))
    (hab1 : a1 ≠ b1) (hab2 : a2 ≠ b2) (hx : ∀ x ∈ [a1, e1, b1], ∀ y ∈ [a2, e2, b2], x ≠ y)
    (hb : b2 < b1) (ha : a1 < a2)
    (hc : e1 = b1 ∨ e2 = a2) : CU (skelList a1 e1 b1 b2 e2 a2) := by
  rcases hc with hc | hc <;>
  rcases hs1 with ⟨rfl, s1⟩ | ⟨rfl, s1⟩ | ⟨s1, t1⟩ <;>
  rcases hs2 with ⟨rfl, s2⟩ | ⟨rfl, s2⟩ | ⟨s2, t2⟩
  all_goals (simp only [skelList, skel1_end_l, skel1_end_r])
  all_goals (try rw [skel1_mid])
  all_goals (try rw [skel1_mid])
  all_goals (try simp only [List.cons_append, List.nil_append])
  all_goals (first | (intro h; linarith) | (exfalso; linarith) | cu_any)


/-- **The pure-real skeleton lemma of Lemma PV** (paper §3).  `aᵢ, bᵢ` are the near/far end depths of
face `Fᵢ`, `loᵢ, hiᵢ` its extreme depths (so `loᵢ ≤ aᵢ, bᵢ ≤ hiᵢ`); depths of the two faces are
distinct (`hx`), the ends of each face differ.  If neither (M−) nor (M+) holds, one of the four
skeletons `(A₁, eᵢ, B₁, B₂, e₂, A₂)` is cyclically unimodal.

Tightening relative to the sketch in `PVSkel.lean`: the hypotheses are exactly "ends of a face
differ" and "depth values of different faces differ"; `loᵢ = hiᵢ` is allowed. -/
theorem pv_skeleton_unimodal (a₁ b₁ a₂ b₂ lo₁ hi₁ lo₂ hi₂ : ℝ)
    (hab₁ : a₁ ≠ b₁) (hab₂ : a₂ ≠ b₂)
    (hx : ∀ x ∈ [a₁, b₁, lo₁, hi₁], ∀ y ∈ [a₂, b₂, lo₂, hi₂], x ≠ y)
    (hlo₁ : lo₁ ≤ a₁ ∧ lo₁ ≤ b₁) (hhi₁ : a₁ ≤ hi₁ ∧ b₁ ≤ hi₁)
    (hlo₂ : lo₂ ≤ a₂ ∧ lo₂ ≤ b₂) (hhi₂ : a₂ ≤ hi₂ ∧ b₂ ≤ hi₂)
    (hnotM : ¬ ((b₁ < b₂ ∧ a₂ < a₁ ∧ a₁ ≠ lo₁ ∧ b₁ ≠ hi₁ ∧ a₂ ≠ hi₂ ∧ b₂ ≠ lo₂) ∨
               (b₂ < b₁ ∧ a₁ < a₂ ∧ a₁ ≠ hi₁ ∧ b₁ ≠ lo₁ ∧ a₂ ≠ lo₂ ∧ b₂ ≠ hi₂))) :
    ∃ e₁ ∈ ({lo₁, hi₁} : Set ℝ), ∃ e₂ ∈ ({lo₂, hi₂} : Set ℝ), CU (skelList a₁ e₁ b₁ b₂ e₂ a₂) := by
  have hb12 : b₁ ≠ b₂ := hx b₁ (by simp) b₂ (by simp)
  have ha12 : a₁ ≠ a₂ := hx a₁ (by simp) a₂ (by simp)
  have sV₁ := shapeV hab₁ hlo₁
  have sL₁ := shapeL hab₁ hhi₁
  have sV₂ := shapeV hab₂ hlo₂
  have sL₂ := shapeL hab₂ hhi₂
  -- cross-face distinctness for the chosen extremes
  have hmem : ∀ (a e b l h : ℝ), e ∈ [l, h] → ∀ x ∈ [a, e, b], x ∈ [a, b, l, h] := by
    intro a e b l h he x hx'
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx' he ⊢
    rcases hx' with rfl | rfl | rfl <;> rcases he with rfl | rfl <;> simp
  have hxe : ∀ e₁ ∈ [lo₁, hi₁], ∀ e₂ ∈ [lo₂, hi₂],
      ∀ x ∈ [a₁, e₁, b₁], ∀ y ∈ [a₂, e₂, b₂], x ≠ y := fun e₁ he₁ e₂ he₂ x hx' y hy' =>
    hx x (hmem a₁ e₁ b₁ lo₁ hi₁ he₁ x hx') y (by
      have := hmem a₂ e₂ b₂ lo₂ hi₂ he₂ y hy'
      simpa using this)
  rcases lt_or_gt_of_ne hb12 with hb | hb <;> rcases lt_or_gt_of_ne ha12 with ha | ha
  · -- b₁ < b₂, a₁ < a₂
    exact ⟨lo₁, by simp, hi₂, by simp,
      skel_VL_up a₁ lo₁ b₁ b₂ hi₂ a₂ sV₁ sL₂ hab₁ hab₂ (hxe _ (by simp) _ (by simp)) hb ha⟩
  · -- b₁ < b₂, a₂ < a₁ : (M−) bridges
    by_cases hc : lo₁ = a₁ ∨ lo₂ = b₂
    · exact ⟨lo₁, by simp, lo₂, by simp,
        skel_VV_minus a₁ lo₁ b₁ b₂ lo₂ a₂ sV₁ sV₂ hab₁ hab₂ (hxe _ (by simp) _ (by simp)) hb ha hc⟩
    · have hn : b₁ = hi₁ ∨ a₂ = hi₂ := by
        by_contra hcon
        push Not at hcon
        apply hnotM
        left
        refine ⟨hb, ha, ?_, hcon.1, hcon.2, ?_⟩
        · intro h; exact hc (Or.inl h.symm)
        · intro h; exact hc (Or.inr h.symm)
      refine ⟨hi₁, by simp, hi₂, by simp,
        skel_LL_minus a₁ hi₁ b₁ b₂ hi₂ a₂ sL₁ sL₂ hab₁ hab₂ (hxe _ (by simp) _ (by simp)) hb ha ?_⟩
      rcases hn with h | h
      · exact Or.inl h.symm
      · exact Or.inr h.symm
  · -- b₂ < b₁, a₁ < a₂ : (M+) bridges
    by_cases hc : hi₁ = a₁ ∨ hi₂ = b₂
    · exact ⟨hi₁, by simp, hi₂, by simp,
        skel_LL_plus a₁ hi₁ b₁ b₂ hi₂ a₂ sL₁ sL₂ hab₁ hab₂ (hxe _ (by simp) _ (by simp)) hb ha hc⟩
    · have hn : b₁ = lo₁ ∨ a₂ = lo₂ := by
        by_contra hcon
        push Not at hcon
        apply hnotM
        right
        refine ⟨hb, ha, ?_, hcon.1, hcon.2, ?_⟩
        · intro h; exact hc (Or.inl h.symm)
        · intro h; exact hc (Or.inr h.symm)
      refine ⟨lo₁, by simp, lo₂, by simp,
        skel_VV_plus a₁ lo₁ b₁ b₂ lo₂ a₂ sV₁ sV₂ hab₁ hab₂ (hxe _ (by simp) _ (by simp)) hb ha ?_⟩
      rcases hn with h | h
      · exact Or.inl h.symm
      · exact Or.inr h.symm
  · -- b₂ < b₁, a₂ < a₁
    exact ⟨hi₁, by simp, lo₂, by simp,
      skel_LV_dn a₁ hi₁ b₁ b₂ lo₂ a₂ sL₁ sV₂ hab₁ hab₂ (hxe _ (by simp) _ (by simp)) hb ha⟩

end Minimality
