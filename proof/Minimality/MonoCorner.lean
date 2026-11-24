module

public import Minimality.EdgeLeaf

/-!
# Monotone corners give `RobUni` (Carbon A58 Lemma 1.1(a), generalised)

* `robUni_of_monoCorners`: for `k ≥ 4`, if at least `k - 3` rim vertices are strictly monotone,
  the depths satisfy `RobUni`.
* Hydrogen Task EB (2026-11-24).  Use: a pointwise RobUni test by corner signs g_v < 0 (A58 Theorem 1.2).
-/

set_option autoImplicit false

open Finset

@[expose] public section

namespace Minimality.GenPlus

open Minimality Minimality.H21

/-! ### Helper lemmas on finite paths -/

private def isMono {k : ℕ} (z : ZMod k → ℝ) (v : ZMod k) : Prop :=
  0 < (z v - z (v - 1)) * (z (v + 1) - z v)

private theorem mono_step_inc {a b c : ℝ} (hab : a < b) (hm : 0 < (b - a) * (c - b)) : b < c := by
  have h1 : 0 < b - a := sub_pos.mpr hab
  have h2 : 0 < c - b := pos_of_mul_pos_right hm h1.le
  linarith

private theorem mono_step_dec {a b c : ℝ} (hab : b < a) (hm : 0 < (b - a) * (c - b)) : c < b := by
  have h1 : b - a < 0 := sub_neg.mpr hab
  have h2 : c - b < 0 := neg_of_mul_pos_right hm h1.le
  linarith

private theorem path_inc {w : ℕ → ℝ} {n : ℕ} (hn : 1 ≤ n) (h0 : w 0 < w 1)
    (hm : ∀ m, 1 ≤ m → m < n → 0 < (w m - w (m - 1)) * (w (m + 1) - w m)) :
    w 0 < w n ∧ w (n - 1) < w n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hn with h1 | hgt
    · have : n = 0 := by omega
      subst this
      exact ⟨h0, h0⟩
    · have ih' := ih (by omega) (fun m hm1 hmn => hm m hm1 (by omega))
      have h_step : w n < w (n + 1) := by
        have := hm n (by omega) (by omega)
        exact mono_step_inc ih'.2 this
      exact ⟨lt_trans ih'.1 h_step, by simpa using h_step⟩

private theorem path_dec {w : ℕ → ℝ} {n : ℕ} (hn : 1 ≤ n) (h0 : w 1 < w 0)
    (hm : ∀ m, 1 ≤ m → m < n → 0 < (w m - w (m - 1)) * (w (m + 1) - w m)) :
    w n < w 0 ∧ w n < w (n - 1) := by
  have h := path_inc (w := fun m => -w m) hn (neg_lt_neg h0) (fun m hm1 hmn => by
    have := hm m hm1 hmn
    have heq : (-w m - -w (m - 1)) * (-w (m + 1) - -w m) =
        (w m - w (m - 1)) * (w (m + 1) - w m) := by ring
    rwa [heq])
  exact ⟨neg_lt_neg_iff.mp h.1, neg_lt_neg_iff.mp h.2⟩

private theorem path_turn_inc {w : ℕ → ℝ} {n : ℕ} (hn : 2 ≤ n) (hle : w n ≤ w 0)
    (h0 : w 0 < w 1) (hn1 : w (n - 1) < w n) :
    2 ≤ ((Finset.Ico 1 n).filter fun m => ¬ (0 < (w m - w (m - 1)) * (w (m + 1) - w m))).card := by
  classical
  set B := (Finset.Ico 1 n).filter fun m => ¬ (0 < (w m - w (m - 1)) * (w (m + 1) - w m))
  by_contra hlt
  have hle1 : B.card ≤ 1 := by omega
  rcases Nat.eq_or_lt_of_le hle1 with h1 | h0_card
  · obtain ⟨m0, hm0⟩ := Finset.card_eq_one.mp h1
    have hm0_mem : m0 ∈ B := by rw [hm0]; exact mem_singleton_self m0
    have hm0_ico := (mem_filter.mp hm0_mem).1
    have hm0_ge : 1 ≤ m0 := (mem_Ico.mp hm0_ico).1
    have hm0_lt : m0 < n := (mem_Ico.mp hm0_ico).2
    have h_mono_all : ∀ m, 1 ≤ m → m < n → m ≠ m0 →
        0 < (w m - w (m - 1)) * (w (m + 1) - w m) := by
      intro m hm1 hmn hne
      by_contra hbad
      have : m ∈ B := mem_filter.mpr ⟨mem_Ico.mpr ⟨hm1, hmn⟩, hbad⟩
      rw [hm0, mem_singleton] at this
      exact hne this
    have h_left : w 0 < w m0 := (path_inc hm0_ge h0 (fun m hm1 hmm => h_mono_all m hm1 (by omega) (by omega))).1
    have h_right_gt : m0 + 1 ≤ n := by omega
    rcases lt_trichotomy (w (m0 + 1)) (w m0) with hr_lt | hr_eq | hr_gt
    · have h_dec := path_dec (w := fun t => w (m0 + t)) (n := n - m0) (by omega)
        (by simpa using hr_lt) (fun t ht1 htn => by
          have := h_mono_all (m0 + t) (by omega) (by omega) (by omega)
          rwa [show m0 + t - 1 = m0 + (t - 1) by omega, show m0 + t + 1 = m0 + (t + 1) by omega] at this)
      have h_last : w n < w (n - 1) := by
        have := h_dec.2
        rwa [show m0 + (n - m0) = n by omega, show m0 + (n - m0 - 1) = n - 1 by omega] at this
      linarith
    · have hm01_lt : m0 + 1 < n := by
        by_contra h_ge
        have : m0 + 1 = n := by omega
        subst this
        linarith
      have hbad := h_mono_all (m0 + 1) (by omega) hm01_lt (by omega)
      rw [add_tsub_cancel_right, hr_eq, sub_self, zero_mul] at hbad
      exact lt_irrefl 0 hbad
    · have h_inc := path_inc (w := fun t => w (m0 + t)) (n := n - m0) (by omega)
        (by simpa using hr_gt) (fun t ht1 htn => by
          have := h_mono_all (m0 + t) (by omega) (by omega) (by omega)
          rwa [show m0 + t - 1 = m0 + (t - 1) by omega, show m0 + t + 1 = m0 + (t + 1) by omega] at this)
      have h_end : w m0 < w n := by
        have := h_inc.1
        rwa [show m0 + (n - m0) = n by omega, add_zero] at this
      linarith
  · have h_empty : B = ∅ := Finset.card_eq_zero.mp (by omega)
    have h_all : ∀ m, 1 ≤ m → m < n → 0 < (w m - w (m - 1)) * (w (m + 1) - w m) := by
      intro m hm1 hmn
      by_contra hbad
      have : m ∈ B := mem_filter.mpr ⟨mem_Ico.mpr ⟨hm1, hmn⟩, hbad⟩
      rw [h_empty] at this
      exact notMem_empty m this
    have := (path_inc (by omega) h0 h_all).1
    linarith

private theorem path_turn_dec {w : ℕ → ℝ} {n : ℕ} (hn : 2 ≤ n) (hle : w 0 ≤ w n)
    (h0 : w 1 < w 0) (hn1 : w n < w (n - 1)) :
    2 ≤ ((Finset.Ico 1 n).filter fun m => ¬ (0 < (w m - w (m - 1)) * (w (m + 1) - w m))).card := by
  have h := path_turn_inc (w := fun m => -w m) hn (neg_le_neg hle) (neg_lt_neg h0) (neg_lt_neg hn1)
  convert h using 2
  ext m
  simp only [mem_filter, mem_Ico]
  have heq : (-w m - -w (m - 1)) * (-w (m + 1) - -w m) =
      (w m - w (m - 1)) * (w (m + 1) - w m) := by ring
  rw [heq]

/-! ### Main theorem `robUni_of_monoCorners` -/

/-- **APPROVED.**  Monotone corners give `RobUni` (A58 Lemma 1.1(a) for k = 5, generalised; checked exactly over
all weak orders for k = 4..7, 0 failures): if at least `k - 3` rim vertices `v` are strictly monotone
(the two incident edges have the same strict sign), the depths are `RobUni`. -/
theorem robUni_of_monoCorners {k : ℕ} [NeZero k] (hk : 4 ≤ k) {z : ZMod k → ℝ} (S : Finset (ZMod k))
    (hS : k - 3 ≤ S.card) (h : ∀ v ∈ S, 0 < (z v - z (v - 1)) * (z (v + 1) - z v)) : RobUni z := by
  classical
  have : Fact (1 < k) := ⟨by omega⟩
  intro B b c d hb hbc hcd hd ⟨e1, e2, e3, e4⟩
  set Sc := Finset.univ \ S
  have hSc_card : Sc.card ≤ 3 := by
    have hsum : S.card + (Finset.univ \ S).card = k := by
      have := Finset.card_sdiff_add_card_inter (Finset.univ : Finset (ZMod k)) S
      rw [Finset.univ_inter, Finset.card_univ, ZMod.card] at this
      omega
    change S.card + Sc.card = k at hsum
    omega
  -- Map each open arc `Ico 1 len` into `ZMod k`
  let arcMap (p : ZMod k) (m : ℕ) : ZMod k := p + (m : ZMod k)
  have arcInj : ∀ (p : ZMod k) (len : ℕ), len ≤ k →
      Set.InjOn (arcMap p) (Finset.Ico 1 len : Set ℕ) := by
    intro p len hlen x hx y hy hxy
    simp only [Finset.coe_Ico, Set.mem_Ico] at hx hy
    have hdiff : ((x : ZMod k)) = (y : ZMod k) := by linear_combination hxy
    have hx' : (x : ZMod k).val = x := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    have hy' : (y : ZMod k).val = y := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    rw [← hx', ← hy', hdiff]
  let badSet (p : ZMod k) (len : ℕ) : Finset (ZMod k) :=
    (Finset.Ico 1 len).image (arcMap p) ∩ Sc
  have hbad_le : ∀ (p : ZMod k) (len : ℕ), len ≤ k →
      ((Finset.Ico 1 len).filter fun m : ℕ =>
        ¬ (0 < (z (p + (m : ZMod k)) - z (p + ((m - 1 : ℕ) : ZMod k))) *
               (z (p + ((m + 1 : ℕ) : ZMod k)) - z (p + (m : ZMod k))))).card ≤
      (badSet p len).card := by
    intro p len hlen
    have himg : ((Finset.Ico 1 len).filter fun m : ℕ => arcMap p m ∈ Sc).image (arcMap p) = badSet p len := by
      ext v
      simp only [badSet, mem_inter, mem_image, mem_filter]
      constructor
      · rintro ⟨m, ⟨hm, hmSc⟩, rfl⟩; exact ⟨⟨m, hm, rfl⟩, hmSc⟩
      · rintro ⟨⟨m, hm, rfl⟩, hmSc⟩; exact ⟨m, ⟨hm, hmSc⟩, rfl⟩
    rw [← himg, Finset.card_image_of_injOn (fun x hx y hy =>
      arcInj p len hlen (mem_filter.mp hx).1 (mem_filter.mp hy).1)]
    apply Finset.card_le_card
    intro m hm
    simp only [mem_filter, mem_Ico, Sc, mem_sdiff, mem_univ, true_and] at hm ⊢
    refine ⟨hm.1, fun hmS => hm.2 ?_⟩
    have hm1 : p + ((m - 1 : ℕ) : ZMod k) = p + (m : ZMod k) - 1 := by
      rw [Nat.cast_sub hm.1.1, Nat.cast_one]; ring
    have hm2 : p + ((m + 1 : ℕ) : ZMod k) = p + (m : ZMod k) + 1 := by
      rw [Nat.cast_add, Nat.cast_one]; ring
    rw [hm1, hm2]
    exact h _ hmS
  -- Disjointness of the 4 open arcs and 4 endpoints
  set A1 := (Finset.Ico 1 b).image (arcMap B)
  set A2 := (Finset.Ico 1 (c - b)).image (arcMap (B + b))
  set A3 := (Finset.Ico 1 (d - c)).image (arcMap (B + c))
  set A4 := (Finset.Ico 1 (k - d)).image (arcMap (B + d))
  set E : Finset (ZMod k) := {B, B + b, B + c, B + d}
  -- Helper: every vertex `B + n` (`n < k`) belongs to a unique piece
  have hE_card : E.card = 4 := by
    have hneq : ∀ x y : ℕ, x < y → y < k → B + (x : ZMod k) ≠ B + (y : ZMod k) := by
      intro x y hxy hyk heq
      have hdiff : ((y - x : ℕ) : ZMod k) = 0 := by
        rw [Nat.cast_sub hxy.le]; linear_combination -heq
      have hval : ((y - x : ℕ) : ZMod k).val = 0 := by rw [hdiff, ZMod.val_zero]
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)] at hval
      omega
    have h01 := (hneq 0 b hb (hbc.trans (hcd.trans hd))).symm
    have h02 := (hneq 0 c (by omega) (hcd.trans hd)).symm
    have h03 := (hneq 0 d (by omega) hd).symm
    have h12 := hneq b c hbc (hcd.trans hd)
    have h13 := hneq b d (by omega) hd
    have h23 := hneq c d hcd hd
    dsimp only [E]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [h23]
    · simp [h12, h13]
    · simp only [mem_insert, mem_singleton]
      rintro (hh | hh | hh)
      · exact h01 (by simpa using hh.symm)
      · exact h02 (by simpa using hh.symm)
      · exact h03 (by simpa using hh.symm)
  -- Helper: `A_i ∩ E = ∅` and `A_i ∩ A_j = ∅` via offset in `(0, k)`
  have h_offset : ∀ p len n, n ∈ Finset.Ico 1 len →
      (p = B → arcMap p n = B + (n : ZMod k)) ∧
      (p = B + b → arcMap p n = B + ((b + n : ℕ) : ZMod k)) ∧
      (p = B + c → arcMap p n = B + ((c + n : ℕ) : ZMod k)) ∧
      (p = B + d → arcMap p n = B + ((d + n : ℕ) : ZMod k)) := by
    intro p len n _
    refine ⟨fun hp => by subst hp; rfl,
      fun hp => by subst hp; simp [arcMap, Nat.cast_add, add_assoc],
      fun hp => by subst hp; simp [arcMap, Nat.cast_add, add_assoc],
      fun hp => by subst hp; simp [arcMap, Nat.cast_add, add_assoc]⟩
  have h_eq_nat : ∀ x y : ℕ, x < k → y < k → B + (x : ZMod k) = B + (y : ZMod k) → x = y := by
    intro x y hx hy heq
    have hdiff : (x : ZMod k) = (y : ZMod k) := by linear_combination heq
    have hx' : (x : ZMod k).val = x := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt hx]
    have hy' : (y : ZMod k).val = y := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt hy]
    rw [← hx', ← hy', hdiff]
  have h_disj_all :
      (A1 ∩ Sc).card + (A2 ∩ Sc).card + (A3 ∩ Sc).card + (A4 ∩ Sc).card + (E ∩ Sc).card ≤ 3 := by
    have hdisj : Disjoint (A1 ∩ Sc) (A2 ∩ Sc) ∧ Disjoint (A1 ∩ Sc) (A3 ∩ Sc) ∧
        Disjoint (A1 ∩ Sc) (A4 ∩ Sc) ∧ Disjoint (A1 ∩ Sc) (E ∩ Sc) ∧
        Disjoint (A2 ∩ Sc) (A3 ∩ Sc) ∧ Disjoint (A2 ∩ Sc) (A4 ∩ Sc) ∧
        Disjoint (A2 ∩ Sc) (E ∩ Sc) ∧ Disjoint (A3 ∩ Sc) (A4 ∩ Sc) ∧
        Disjoint (A3 ∩ Sc) (E ∩ Sc) ∧ Disjoint (A4 ∩ Sc) (E ∩ Sc) := by
      have h_no : ∀ (P Q : Finset (ZMod k)),
          (∀ v ∈ P, ∃ n < k, v = B + (n : ZMod k) ∧
            (v ∈ A1 → 0 < n ∧ n < b) ∧ (v ∈ A2 → b < n ∧ n < c) ∧
            (v ∈ A3 → c < n ∧ n < d) ∧ (v ∈ A4 → d < n ∧ n < k) ∧
            (v ∈ E → n = 0 ∨ n = b ∨ n = c ∨ n = d)) → True := fun _ _ _ => trivial
      -- Direct disjointness on elements
      have hmem1 : ∀ v ∈ A1, ∃ n, 0 < n ∧ n < b ∧ v = B + (n : ZMod k) := by
        rintro v hv; rcases mem_image.mp hv with ⟨n, hn, rfl⟩
        exact ⟨n, (mem_Ico.mp hn).1, (mem_Ico.mp hn).2, rfl⟩
      have hmem2 : ∀ v ∈ A2, ∃ n, b < n ∧ n < c ∧ v = B + (n : ZMod k) := by
        rintro v hv; rcases mem_image.mp hv with ⟨n, hn, rfl⟩
        rcases mem_Ico.mp hn with ⟨hn1, hn2⟩
        exact ⟨b + n, by omega, by omega, by simp [arcMap, Nat.cast_add, add_assoc]⟩
      have hmem3 : ∀ v ∈ A3, ∃ n, c < n ∧ n < d ∧ v = B + (n : ZMod k) := by
        rintro v hv; rcases mem_image.mp hv with ⟨n, hn, rfl⟩
        rcases mem_Ico.mp hn with ⟨hn1, hn2⟩
        exact ⟨c + n, by omega, by omega, by simp [arcMap, Nat.cast_add, add_assoc]⟩
      have hmem4 : ∀ v ∈ A4, ∃ n, d < n ∧ n < k ∧ v = B + (n : ZMod k) := by
        rintro v hv; rcases mem_image.mp hv with ⟨n, hn, rfl⟩
        rcases mem_Ico.mp hn with ⟨hn1, hn2⟩
        exact ⟨d + n, by omega, by omega, by simp [arcMap, Nat.cast_add, add_assoc]⟩
      have hmemE : ∀ v ∈ E, ∃ n < k, (n = 0 ∨ n = b ∨ n = c ∨ n = d) ∧ v = B + (n : ZMod k) := by
        rintro v hv
        simp only [E, mem_insert, mem_singleton] at hv
        rcases hv with rfl | rfl | rfl | rfl
        · exact ⟨0, by omega, Or.inl rfl, by simp⟩
        · exact ⟨b, by omega, Or.inr (Or.inl rfl), rfl⟩
        · exact ⟨c, by omega, Or.inr (Or.inr (Or.inl rfl)), rfl⟩
        · exact ⟨d, by omega, Or.inr (Or.inr (Or.inr rfl)), rfl⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        rw [Finset.disjoint_left] <;> intro v hv1 hv2
      · obtain ⟨n1, _, h1b, hv1'⟩ := hmem1 v (mem_inter.mp hv1).1
        obtain ⟨n2, hb2, h2c, hv2'⟩ := hmem2 v (mem_inter.mp hv2).1
        have := h_eq_nat n1 n2 (by omega) (by omega) (hv1'.symm.trans hv2'); omega
      · obtain ⟨n1, _, h1b, hv1'⟩ := hmem1 v (mem_inter.mp hv1).1
        obtain ⟨n2, hc2, h2d, hv2'⟩ := hmem3 v (mem_inter.mp hv2).1
        have := h_eq_nat n1 n2 (by omega) (by omega) (hv1'.symm.trans hv2'); omega
      · obtain ⟨n1, _, h1b, hv1'⟩ := hmem1 v (mem_inter.mp hv1).1
        obtain ⟨n2, hd2, h2k, hv2'⟩ := hmem4 v (mem_inter.mp hv2).1
        have := h_eq_nat n1 n2 (by omega) (by omega) (hv1'.symm.trans hv2'); omega
      · obtain ⟨n1, hn1, h1b, hv1'⟩ := hmem1 v (mem_inter.mp hv1).1
        obtain ⟨n2, h2k, h2E, hv2'⟩ := hmemE v (mem_inter.mp hv2).1
        have := h_eq_nat n1 n2 (by omega) h2k (hv1'.symm.trans hv2'); omega
      · obtain ⟨n1, hb1, h1c, hv1'⟩ := hmem2 v (mem_inter.mp hv1).1
        obtain ⟨n2, hc2, h2d, hv2'⟩ := hmem3 v (mem_inter.mp hv2).1
        have := h_eq_nat n1 n2 (by omega) (by omega) (hv1'.symm.trans hv2'); omega
      · obtain ⟨n1, hb1, h1c, hv1'⟩ := hmem2 v (mem_inter.mp hv1).1
        obtain ⟨n2, hd2, h2k, hv2'⟩ := hmem4 v (mem_inter.mp hv2).1
        have := h_eq_nat n1 n2 (by omega) (by omega) (hv1'.symm.trans hv2'); omega
      · obtain ⟨n1, hb1, h1c, hv1'⟩ := hmem2 v (mem_inter.mp hv1).1
        obtain ⟨n2, h2k, h2E, hv2'⟩ := hmemE v (mem_inter.mp hv2).1
        have := h_eq_nat n1 n2 (by omega) h2k (hv1'.symm.trans hv2'); omega
      · obtain ⟨n1, hc1, h1d, hv1'⟩ := hmem3 v (mem_inter.mp hv1).1
        obtain ⟨n2, hd2, h2k, hv2'⟩ := hmem4 v (mem_inter.mp hv2).1
        have := h_eq_nat n1 n2 (by omega) (by omega) (hv1'.symm.trans hv2'); omega
      · obtain ⟨n1, hc1, h1d, hv1'⟩ := hmem3 v (mem_inter.mp hv1).1
        obtain ⟨n2, h2k, h2E, hv2'⟩ := hmemE v (mem_inter.mp hv2).1
        have := h_eq_nat n1 n2 (by omega) h2k (hv1'.symm.trans hv2'); omega
      · obtain ⟨n1, hd1, h1k, hv1'⟩ := hmem4 v (mem_inter.mp hv1).1
        obtain ⟨n2, h2k, h2E, hv2'⟩ := hmemE v (mem_inter.mp hv2).1
        have := h_eq_nat n1 n2 (by omega) h2k (hv1'.symm.trans hv2'); omega
    have hunion : (A1 ∩ Sc) ∪ (A2 ∩ Sc) ∪ (A3 ∩ Sc) ∪ (A4 ∩ Sc) ∪ (E ∩ Sc) ⊆ Sc := by
      intro v hv
      simp only [mem_union, mem_inter] at hv
      rcases hv with ((((h | h) | h) | h) | h) <;> exact h.2
    have hcard_le := Finset.card_le_card hunion
    rw [Finset.card_union_of_disjoint (by
        simp only [disjoint_union_left, and_assoc]
        exact ⟨hdisj.2.2.2.1, hdisj.2.2.2.2.2.2.1, hdisj.2.2.2.2.2.2.2.2.1, hdisj.2.2.2.2.2.2.2.2.2⟩),
      Finset.card_union_of_disjoint (by
        simp only [disjoint_union_left, and_assoc]
        exact ⟨hdisj.2.2.1, hdisj.2.2.2.2.2.1, hdisj.2.2.2.2.2.2.2.1⟩),
      Finset.card_union_of_disjoint (by
        simp only [disjoint_union_left]
        exact ⟨hdisj.2.1, hdisj.2.2.2.2.1⟩),
      Finset.card_union_of_disjoint hdisj.1] at hcard_le
    omega
  -- Express `(E ∩ Sc).card` as sum of 4 indicator bits
  set b1 := (A1 ∩ Sc).card
  set b2 := (A2 ∩ Sc).card
  set b3 := (A3 ∩ Sc).card
  set b4 := (A4 ∩ Sc).card
  let ind (v : ZMod k) : ℕ := if v ∈ Sc then 1 else 0
  have hE_sum : (E ∩ Sc).card = ind B + ind (B + b) + ind (B + c) + ind (B + d) := by
    have h01 : B ≠ B + b := by
      intro heq
      have : (0 : ZMod k) = (b : ZMod k) := by linear_combination heq
      have := h_eq_nat 0 b (by omega) (by omega) (by simpa using heq)
      omega
    have h02 : B ≠ B + c := fun heq => by
      have := h_eq_nat 0 c (by omega) (by omega) (by simpa using heq); omega
    have h03 : B ≠ B + d := fun heq => by
      have := h_eq_nat 0 d (by omega) (by omega) (by simpa using heq); omega
    have h12 : B + b ≠ B + c := fun heq => by
      have := h_eq_nat b c (by omega) (by omega) heq; omega
    have h13 : B + b ≠ B + d := fun heq => by
      have := h_eq_nat b d (by omega) (by omega) heq; omega
    have h23 : B + c ≠ B + d := fun heq => by
      have := h_eq_nat c d (by omega) (by omega) heq; omega
    have h_split : ∀ v : ZMod k, ({v} ∩ Sc : Finset (ZMod k)).card = ind v := fun v => by
      dsimp [ind]; split_ifs with hv <;> simp [hv]
    have hE_eq : E ∩ Sc = ({B} ∩ Sc) ∪ ({B + b} ∩ Sc) ∪ ({B + c} ∩ Sc) ∪ ({B + d} ∩ Sc) := by
      ext v; simp [E, mem_inter, mem_union, mem_insert, mem_singleton]; tauto
    have h_disj_pt : ∀ x y : ZMod k, x ≠ y → Disjoint ({x} ∩ Sc) ({y} ∩ Sc) :=
      fun x y hxy => Finset.disjoint_left.mpr fun v hv1 hv2 => hxy (by simp_all)
    rw [hE_eq,
      Finset.card_union_of_disjoint (by
        simp only [disjoint_union_left]
        exact ⟨⟨h_disj_pt _ _ h03, h_disj_pt _ _ h13⟩, h_disj_pt _ _ h23⟩),
      Finset.card_union_of_disjoint (by
        simp only [disjoint_union_left]
        exact ⟨h_disj_pt _ _ h02, h_disj_pt _ _ h12⟩),
      Finset.card_union_of_disjoint (h_disj_pt _ _ h01),
      h_split, h_split, h_split, h_split]
  -- Generic arc lemmas: decreasing arc `(z (p + len) ≤ z p)` and increasing arc `(z p ≤ z (p + len))`
  have h_arc_dec : ∀ (p : ZMod k) (len : ℕ), 1 ≤ len → len ≤ k → z (p + (len : ZMod k)) ≤ z p →
      ((badSet p len).card = 0 →
        (z (p + 1) < z p ∧ z (p + (len : ZMod k)) < z (p + (len : ZMod k) - 1)) ∨
        (len = 1 ∧ p ∈ Sc ∧ p + (len : ZMod k) ∈ Sc)) ∧
      (z p < z (p + 1) → z (p + (len : ZMod k) - 1) < z (p + (len : ZMod k)) →
        2 ≤ (badSet p len).card) := by
    intro p len hlen hlenk hle
    constructor
    · intro hbad0
      have hbad0' : ((Finset.Ico 1 len).filter fun m : ℕ =>
          ¬ (0 < (z (p + (m : ZMod k)) - z (p + ((m - 1 : ℕ) : ZMod k))) *
                 (z (p + ((m + 1 : ℕ) : ZMod k)) - z (p + (m : ZMod k))))).card = 0 :=
        Nat.eq_zero_of_le_zero (hbad0 ▸ hbad_le p len hlenk)
      have h_emp : (Finset.Ico 1 len).filter (fun m : ℕ =>
          ¬ (0 < (z (p + (m : ZMod k)) - z (p + ((m - 1 : ℕ) : ZMod k))) *
                 (z (p + ((m + 1 : ℕ) : ZMod k)) - z (p + (m : ZMod k))))) = ∅ :=
        Finset.card_eq_zero.mp hbad0'
      have h_all : ∀ m, 1 ≤ m → m < len →
          0 < (z (p + (m : ZMod k)) - z (p + ((m - 1 : ℕ) : ZMod k))) *
              (z (p + ((m + 1 : ℕ) : ZMod k)) - z (p + (m : ZMod k))) := by
        intro m hm1 hml
        by_contra hnot
        have : m ∈ (Finset.Ico 1 len).filter (fun m : ℕ =>
            ¬ (0 < (z (p + (m : ZMod k)) - z (p + ((m - 1 : ℕ) : ZMod k))) *
                   (z (p + ((m + 1 : ℕ) : ZMod k)) - z (p + (m : ZMod k))))) :=
          mem_filter.mpr ⟨mem_Ico.mpr ⟨hm1, hml⟩, hnot⟩
        rw [h_emp] at this
        exact notMem_empty m this
      rcases Nat.eq_or_lt_of_le hlen with rfl | hlen2
      · rw [Nat.cast_one] at hle ⊢
        rcases eq_or_lt_of_le hle with heq | hlt
        · right
          refine ⟨rfl, ?_, ?_⟩ <;> simp only [Sc, mem_sdiff, mem_univ, true_and] <;> intro hS' <;>
            have hh := h _ hS' <;> simp [heq] at hh
        · left
          exact ⟨hlt, by simpa using hlt⟩
      · left
        have h_first : z (p + 1) < z p := by
          by_contra h_ge
          push Not at h_ge
          rcases eq_or_lt_of_le h_ge with heq | hlt
          · have := h_all 1 (le_refl 1) hlen2
            simp only [Nat.cast_one, tsub_self, Nat.cast_zero, add_zero] at this
            rw [heq, sub_self, zero_mul] at this
            exact lt_irrefl 0 this
          · have := (path_inc (w := fun m => z (p + (m : ZMod k))) hlen (by simpa using hlt) h_all).1
            simp at this; linarith
        have h_last := (path_dec (w := fun m => z (p + (m : ZMod k))) hlen (by simpa using h_first) h_all).2
        refine ⟨h_first, ?_⟩
        rwa [show p + ((len - 1 : ℕ) : ZMod k) = p + (len : ZMod k) - 1 by
          rw [Nat.cast_sub hlen, Nat.cast_one]; ring] at h_last
    · intro h0 h1
      by_cases hlen1 : len = 1
      · subst hlen1; simp only [Nat.cast_one] at hle; linarith
      · refine le_trans ?_ (hbad_le p len hlenk)
        refine path_turn_inc (w := fun m => z (p + (m : ZMod k))) (n := len) (by omega)
          (by simpa using hle) (by simpa using h0) ?_
        rwa [show p + ((len - 1 : ℕ) : ZMod k) = p + (len : ZMod k) - 1 by
          rw [Nat.cast_sub hlen, Nat.cast_one]; ring]
  have h_arc_inc : ∀ (p : ZMod k) (len : ℕ), 1 ≤ len → len ≤ k → z p ≤ z (p + (len : ZMod k)) →
      ((badSet p len).card = 0 →
        (z p < z (p + 1) ∧ z (p + (len : ZMod k) - 1) < z (p + (len : ZMod k))) ∨
        (len = 1 ∧ p ∈ Sc ∧ p + (len : ZMod k) ∈ Sc)) ∧
      (z (p + 1) < z p → z (p + (len : ZMod k)) < z (p + (len : ZMod k) - 1) →
        2 ≤ (badSet p len).card) := by
    intro p len hlen hlenk hle
    constructor
    · intro hbad0
      have hbad0' : ((Finset.Ico 1 len).filter fun m : ℕ =>
          ¬ (0 < (z (p + (m : ZMod k)) - z (p + ((m - 1 : ℕ) : ZMod k))) *
                 (z (p + ((m + 1 : ℕ) : ZMod k)) - z (p + (m : ZMod k))))).card = 0 :=
        Nat.eq_zero_of_le_zero (hbad0 ▸ hbad_le p len hlenk)
      have h_emp : (Finset.Ico 1 len).filter (fun m : ℕ =>
          ¬ (0 < (z (p + (m : ZMod k)) - z (p + ((m - 1 : ℕ) : ZMod k))) *
                 (z (p + ((m + 1 : ℕ) : ZMod k)) - z (p + (m : ZMod k))))) = ∅ :=
        Finset.card_eq_zero.mp hbad0'
      have h_all : ∀ m, 1 ≤ m → m < len →
          0 < (z (p + (m : ZMod k)) - z (p + ((m - 1 : ℕ) : ZMod k))) *
              (z (p + ((m + 1 : ℕ) : ZMod k)) - z (p + (m : ZMod k))) := by
        intro m hm1 hml
        by_contra hnot
        have : m ∈ (Finset.Ico 1 len).filter (fun m : ℕ =>
            ¬ (0 < (z (p + (m : ZMod k)) - z (p + ((m - 1 : ℕ) : ZMod k))) *
                   (z (p + ((m + 1 : ℕ) : ZMod k)) - z (p + (m : ZMod k))))) :=
          mem_filter.mpr ⟨mem_Ico.mpr ⟨hm1, hml⟩, hnot⟩
        rw [h_emp] at this
        exact notMem_empty m this
      rcases Nat.eq_or_lt_of_le hlen with rfl | hlen2
      · rw [Nat.cast_one] at hle ⊢
        rcases eq_or_lt_of_le hle with heq | hlt
        · right
          refine ⟨rfl, ?_, ?_⟩ <;> simp only [Sc, mem_sdiff, mem_univ, true_and] <;> intro hS' <;>
            have hh := h _ hS' <;> simp [heq] at hh
        · left
          exact ⟨hlt, by simpa using hlt⟩
      · left
        have h_first : z p < z (p + 1) := by
          by_contra h_le
          push Not at h_le
          rcases eq_or_lt_of_le h_le with heq | hlt
          · have := h_all 1 (le_refl 1) hlen2
            simp only [Nat.cast_one, tsub_self, Nat.cast_zero, add_zero] at this
            rw [heq, sub_self, zero_mul] at this
            exact lt_irrefl 0 this
          · have := (path_dec (w := fun m => z (p + (m : ZMod k))) hlen (by simpa using hlt) h_all).1
            simp at this; linarith
        have h_last := (path_inc (w := fun m => z (p + (m : ZMod k))) hlen (by simpa using h_first) h_all).2
        refine ⟨h_first, ?_⟩
        rwa [show p + ((len - 1 : ℕ) : ZMod k) = p + (len : ZMod k) - 1 by
          rw [Nat.cast_sub hlen, Nat.cast_one]; ring] at h_last
    · intro h0 h1
      by_cases hlen1 : len = 1
      · subst hlen1; simp only [Nat.cast_one] at hle; linarith
      · refine le_trans ?_ (hbad_le p len hlenk)
        refine path_turn_dec (w := fun m => z (p + (m : ZMod k))) (n := len) (by omega)
          (by simpa using hle) (by simpa using h0) ?_
        rwa [show p + ((len - 1 : ℕ) : ZMod k) = p + (len : ZMod k) - 1 by
          rw [Nat.cast_sub hlen, Nat.cast_one]; ring]
  -- Instantiate the 4 arcs
  have ha1 := h_arc_dec B b (by omega) (by omega) e1
  have ha2 := h_arc_inc (B + b) (c - b) (by omega) (by omega) (by
    rwa [add_assoc, ← Nat.cast_add, Nat.add_sub_cancel' hbc.le])
  have ha3 := h_arc_dec (B + c) (d - c) (by omega) (by omega) (by
    rwa [add_assoc, ← Nat.cast_add, Nat.add_sub_cancel' hcd.le])
  have ha4 := h_arc_inc (B + d) (k - d) (by omega) (by omega) (by
    rwa [add_assoc, ← Nat.cast_add, Nat.add_sub_cancel' hd.le, ZMod.natCast_self, add_zero])
  -- Helper at endpoints: if `v ∉ Sc`, then `v ∈ S` so `z (v - 1) < z v ↔ z v < z (v + 1)`
  have h_end : ∀ v : ZMod k, v ∉ Sc →
      (z (v - 1) < z v → z v < z (v + 1)) ∧ (z v < z (v - 1) → z (v + 1) < z v) ∧
      (z (v + 1) < z v → z v < z (v - 1)) ∧ (z v < z (v + 1) → z (v - 1) < z v) := by
    intro v hv
    have hvS : v ∈ S := by simpa [Sc] using hv
    have hm := h v hvS
    refine ⟨fun h1 => mono_step_inc h1 hm, fun h1 => mono_step_dec h1 hm, fun h1 => ?_, fun h1 => ?_⟩
    · have h2 : z (v + 1) - z v < 0 := sub_neg.mpr h1
      have h3 : z v - z (v - 1) < 0 := neg_of_mul_pos_left hm h2.le
      linarith
    · have h2 : 0 < z (v + 1) - z v := sub_pos.mpr h1
      have h3 : 0 < z v - z (v - 1) := pos_of_mul_pos_left hm h2.le
      linarith
  -- Normalize endpoint shifts
  have e2_idx : B + (b : ZMod k) + ((c - b : ℕ) : ZMod k) = B + c := by
    rw [add_assoc, ← Nat.cast_add, Nat.add_sub_cancel' hbc.le]
  have e3_idx : B + (c : ZMod k) + ((d - c : ℕ) : ZMod k) = B + d := by
    rw [add_assoc, ← Nat.cast_add, Nat.add_sub_cancel' hcd.le]
  have e4_idx : B + (d : ZMod k) + ((k - d : ℕ) : ZMod k) = B := by
    rw [add_assoc, ← Nat.cast_add, Nat.add_sub_cancel' hd.le, ZMod.natCast_self, add_zero]
  rw [e2_idx] at ha2
  rw [e3_idx] at ha3
  rw [e4_idx] at ha4
  -- Endpoint indicators and direction booleans
  let c1 : Prop := B ∈ Sc
  let c2 : Prop := B + b ∈ Sc
  let c3 : Prop := B + c ∈ Sc
  let c4 : Prop := B + d ∈ Sc
  let u1 : Prop := z (B - 1) < z B
  let u2 : Prop := z (B + b - 1) < z (B + b)
  let u3 : Prop := z (B + c - 1) < z (B + c)
  let u4 : Prop := z (B + d - 1) < z (B + d)
  -- Helper: each arc `b_i` bounds the number of its endpoints that fail its preferred direction
  have hb1_bound : (if ¬c1 ∧ u1 then 1 else 0) + (if ¬c2 ∧ u2 then 1 else 0) ≤ b1 := by
    by_cases h1 : ¬c1 ∧ u1 <;> by_cases h2 : ¬c2 ∧ u2 <;>
      simp only [h1, h2, not_false_eq_true, and_true, ↓reduceIte]
    · exact ha1.2 ((h_end B h1.1).1 h1.2) h2.2
    · by_contra hlt; have hb0 : b1 = 0 := by omega
      rcases ha1.1 hb0 with ⟨hf, _⟩ | ⟨_, hB, _⟩
      · exact absurd ((h_end B h1.1).1 h1.2) (not_lt.mpr hf.le)
      · exact h1.1 hB
    · by_contra hlt; have hb0 : b1 = 0 := by omega
      rcases ha1.1 hb0 with ⟨_, hl⟩ | ⟨_, _, hBb⟩
      · exact absurd h2.2 (not_lt.mpr hl.le)
      · exact h2.1 hBb
    · omega
  have hb2_bound : (if ¬c2 ∧ ¬u2 then 1 else 0) + (if ¬c3 ∧ ¬u3 then 1 else 0) ≤ b2 := by
    by_cases h2 : ¬c2 ∧ ¬u2 <;> by_cases h3 : ¬c3 ∧ ¬u3 <;>
      simp only [h2, h3, not_false_eq_true, and_true, ↓reduceIte]
    · have hu2' : z (B + b + 1) < z (B + b) := (h_end (B + b) h2.1).2.1
        (lt_of_le_of_ne (not_lt.mp h2.2) fun heq => by
          have := h (B + b) (by simpa [c2, Sc] using h2.1)
          simp [heq] at this)
      have hu3' : z (B + c) < z (B + c - 1) := lt_of_le_of_ne (not_lt.mp h3.2) fun heq => by
        have := h (B + c) (by simpa [c3, Sc] using h3.1)
        simp [heq] at this
      exact ha2.2 hu2' hu3'
    · by_contra hlt; have hb0 : b2 = 0 := by omega
      rcases ha2.1 hb0 with ⟨hf, _⟩ | ⟨_, hBb, _⟩
      · exact h2.2 ((h_end (B + b) h2.1).2.2.2 hf)
      · exact h2.1 hBb
    · by_contra hlt; have hb0 : b2 = 0 := by omega
      rcases ha2.1 hb0 with ⟨_, hl⟩ | ⟨_, _, hBc⟩
      · exact h3.2 hl
      · exact h3.1 hBc
    · omega
  have hb3_bound : (if ¬c3 ∧ u3 then 1 else 0) + (if ¬c4 ∧ u4 then 1 else 0) ≤ b3 := by
    by_cases h3 : ¬c3 ∧ u3 <;> by_cases h4 : ¬c4 ∧ u4 <;>
      simp only [h3, h4, not_false_eq_true, and_true, ↓reduceIte]
    · exact ha3.2 ((h_end (B + c) h3.1).1 h3.2) h4.2
    · by_contra hlt; have hb0 : b3 = 0 := by omega
      rcases ha3.1 hb0 with ⟨hf, _⟩ | ⟨_, hBc, _⟩
      · exact absurd ((h_end (B + c) h3.1).1 h3.2) (not_lt.mpr hf.le)
      · exact h3.1 hBc
    · by_contra hlt; have hb0 : b3 = 0 := by omega
      rcases ha3.1 hb0 with ⟨_, hl⟩ | ⟨_, _, hBd⟩
      · exact absurd h4.2 (not_lt.mpr hl.le)
      · exact h4.1 hBd
    · omega
  have hb4_bound : (if ¬c4 ∧ ¬u4 then 1 else 0) + (if ¬c1 ∧ ¬u1 then 1 else 0) ≤ b4 := by
    by_cases h4 : ¬c4 ∧ ¬u4 <;> by_cases h1 : ¬c1 ∧ ¬u1 <;>
      simp only [h4, h1, not_false_eq_true, and_true, ↓reduceIte]
    · have hu4' : z (B + d + 1) < z (B + d) := (h_end (B + d) h4.1).2.1
        (lt_of_le_of_ne (not_lt.mp h4.2) fun heq => by
          have := h (B + d) (by simpa [c4, Sc] using h4.1)
          simp [heq] at this)
      have hu1' : z B < z (B - 1) := lt_of_le_of_ne (not_lt.mp h1.2) fun heq => by
        have := h B (by simpa [c1, Sc] using h1.1)
        simp [heq] at this
      exact ha4.2 hu4' hu1'
    · by_contra hlt
      have hb0 : (badSet (B + d) (k - d)).card = 0 := by
        have : b4 = (badSet (B + d) (k - d)).card := rfl
        omega
      rcases ha4.1 hb0 with ⟨hf, _⟩ | ⟨_, hBd, _⟩
      · exact h4.2 ((h_end (B + d) h4.1).2.2.2 hf)
      · exact h4.1 hBd
    · by_contra hlt
      have hb0 : (badSet (B + d) (k - d)).card = 0 := by
        have : b4 = (badSet (B + d) (k - d)).card := rfl
        omega
      rcases ha4.1 hb0 with ⟨_, hl⟩ | ⟨_, _, hB⟩
      · exact h1.2 hl
      · exact h1.1 hB
    · omega
  have hind_split : ∀ (P Q : Prop) [Decidable P] [Decidable Q],
      (if P then 1 else 0) + (if ¬P ∧ Q then 1 else 0) + (if ¬P ∧ ¬Q then 1 else 0) = 1 := by
    intro P Q _ _; by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]
  have hs1 := hind_split c1 u1
  have hs2 := hind_split c2 u2
  have hs3 := hind_split c3 u3
  have hs4 := hind_split c4 u4
  have hE_bits : (E ∩ Sc).card = (if c1 then 1 else 0) + (if c2 then 1 else 0) +
      (if c3 then 1 else 0) + (if c4 then 1 else 0) := hE_sum
  have h_arith : ∀ x1 x2 x3 x4 y1 y2 y3 y4 z1 z2 z3 z4 b1 b2 b3 b4 e : ℕ,
      y1 + y2 ≤ b1 → z2 + z3 ≤ b2 → y3 + y4 ≤ b3 → z4 + z1 ≤ b4 →
      x1 + y1 + z1 = 1 → x2 + y2 + z2 = 1 → x3 + y3 + z3 = 1 → x4 + y4 + z4 = 1 →
      e = x1 + x2 + x3 + x4 → b1 + b2 + b3 + b4 + e ≤ 3 → False := by
    intros; omega
  exact h_arith _ _ _ _ _ _ _ _ _ _ _ _ b1 b2 b3 b4 (E ∩ Sc).card
    hb1_bound hb2_bound hb3_bound hb4_bound hs1 hs2 hs3 hs4 hE_bits h_disj_all

end Minimality.GenPlus
