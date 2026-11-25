module

public import Minimality.MonoCorner
public import Minimality.EdgeLeaf
public import Minimality.SplitRim4
public import Minimality.AdjTie4
public import Minimality.LexCell
public import Minimality.GenRev24

@[expose] public section

/-!
# RimOrderInst: short `robUniO_of_noAlt` proofs of the existing `RobUni` / `RobUniLex` lemmas

Hydrogen Task EN: proves the exact same statements as:
1. `Minimality.MonoCorner.robUni_of_monoCorners` -> `robUni_of_monoCorners_viaNoAlt`
2. `Minimality.EdgeLeaf.robUni_of_edgeCone` -> `robUni_of_edgeCone_viaNoAlt`
3. `Minimality.GenPlus.robUni_of_splitRows4` -> `robUni_of_splitRows4_viaNoAlt`
4. `Minimality.GenPlus.robUniLex_adjTie` -> `robUniLex_adjTie_viaNoAlt`
5. `Minimality.LexCell.robUniLex_four_of_mixed` -> `robUniLex_four_of_mixed_viaNoAlt`
-/

set_option autoImplicit false

open scoped RealInnerProductSpace
open Finset

namespace Minimality.RimOrderInst

open Minimality Minimality.H21 Minimality.GenRev Minimality.LexCell Minimality.RimCell

/-! ## 1. `robUni_of_monoCorners_viaNoAlt` -/

theorem robUni_of_monoCorners_viaNoAlt {k : ℕ} [NeZero k] (hk : 4 ≤ k) {z : ZMod k → ℝ}
    (S : Finset (ZMod k)) (hS : k - 3 ≤ S.card)
    (h : ∀ v ∈ S, 0 < (z v - z (v - 1)) * (z (v + 1) - z v)) : RobUni z := by
  have : Fact (1 < k) := ⟨by omega⟩
  refine robUni_of_noAlt (univ \ S) (univ \ S) ?_ ?_ ?_
  · intro v hv
    have hvS : v ∈ S := by
      by_contra hnot; exact hv (mem_sdiff.2 ⟨mem_univ v, hnot⟩)
    rcases mul_pos_iff.1 (h v hvS) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · intro v hv
    have hvS : v ∈ S := by
      by_contra hnot; exact hv (mem_sdiff.2 ⟨mem_univ v, hnot⟩)
    rcases mul_pos_iff.1 (h v hvS) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
  · intro B b c d hb hbc hcd hd ⟨hB, hBb, hBc, hBd⟩
    have hcard : (univ \ S).card ≤ 3 := by
      have hsum := card_sdiff_add_card_inter (univ : Finset (ZMod k)) S
      rw [univ_inter, card_univ, ZMod.card] at hsum
      omega
    have hsub : {B, B + (b : ZMod k), B + (c : ZMod k), B + (d : ZMod k)} ⊆ univ \ S := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    have hinj : ∀ m n : ℕ, m < n → n < k → B + (m : ZMod k) ≠ B + (n : ZMod k) := by
      intro m n hmn hnk heq
      have hmn0 : ((n - m : ℕ) : ZMod k) = 0 := by
        have : (m : ZMod k) = (n : ZMod k) := add_left_cancel heq
        rw [Nat.cast_sub (by omega), this, sub_self]
      have hval := congrArg ZMod.val hmn0
      rw [ZMod.val_natCast, ZMod.val_zero, Nat.mod_eq_of_lt (by omega)] at hval
      omega
    have hc4 : ({B, B + (b : ZMod k), B + (c : ZMod k), B + (d : ZMod k)} : Finset (ZMod k)).card = 4 := by
      rw [card_insert_of_notMem, card_insert_of_notMem, card_insert_of_notMem, card_singleton]
      · simp only [mem_singleton]; exact hinj c d hcd hd
      · simp only [mem_insert, mem_singleton]
        rintro (h1 | h1)
        · exact hinj b c hbc (by omega) h1
        · exact hinj b d (by omega) hd h1
      · simp only [mem_insert, mem_singleton]
        rintro (h1 | h1 | h1)
        · exact hinj 0 b hb (by omega) (by simpa using h1)
        · exact hinj 0 c (by omega) (by omega) (by simpa using h1)
        · exact hinj 0 d (by omega) hd (by simpa using h1)
    have hle := card_le_card hsub
    omega

/-! ## 2. `robUni_of_edgeCone_viaNoAlt` -/

private lemma zmod_add_nat_ne_add {k : ℕ} (hk : 4 ≤ k) (i : ZMod k) {a b : ℕ}
    (ha : a < k) (hb : b < k) (hab : a ≠ b) : i + (a : ZMod k) ≠ i + (b : ZMod k) := by
  have : Fact (1 < k) := ⟨by omega⟩
  intro heq
  have h1 : ((a : ZMod k)) = (b : ZMod k) := add_left_cancel heq
  have h2 := congrArg ZMod.val h1
  rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h2
  exact hab h2

private lemma arc_noAlt {k : ℕ} (hk : 4 ≤ k) (i : ZMod k) {B : ZMod k} {b c d : ℕ}
    (hb : 0 < b) (hbc : b < c) (hcd : c < d) (hd : d < k)
    (h1 : B ∈ ({i + 2, i + 3} : Finset (ZMod k)) ∧ B + (b : ZMod k) ∈ ({i, i + 1} : Finset (ZMod k)) ∧
          B + (c : ZMod k) ∈ ({i + 2, i + 3} : Finset (ZMod k)) ∧ B + (d : ZMod k) ∈ ({i, i + 1} : Finset (ZMod k))) :
    False := by
  have : Fact (1 < k) := ⟨by omega⟩
  rcases h1 with ⟨hB, hBb, hBc, hBd⟩
  simp only [mem_insert, mem_singleton] at hB hBc
  rcases hB with rfl | rfl
  · rcases hBc with hBc | hBc
    · have hc0 : (c : ZMod k) = 0 := by linear_combination hBc
      have hcval := congrArg ZMod.val hc0
      rw [ZMod.val_natCast, ZMod.val_zero, Nat.mod_eq_of_lt (by omega)] at hcval
      omega
    · have hc1 : (c : ZMod k) = (1 : ℕ) := by linear_combination hBc
      have hcval := congrArg ZMod.val hc1
      rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hcval
      omega
  · rcases hBc with hBc | hBc
    · have hck1 : (c : ZMod k) = ((k - 1 : ℕ) : ZMod k) := by
        have hk0 : (k : ZMod k) = 0 := ZMod.natCast_self k
        have : ((k - 1 : ℕ) : ZMod k) = -1 := by
          rw [Nat.cast_sub (by omega), hk0]; ring
        rw [this]; linear_combination hBc
      have hcval := congrArg ZMod.val hck1
      rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hcval
      omega
    · have hc0 : (c : ZMod k) = 0 := by linear_combination hBc
      have hcval := congrArg ZMod.val hc0
      rw [ZMod.val_natCast, ZMod.val_zero, Nat.mod_eq_of_lt (by omega)] at hcval
      omega

theorem robUni_of_edgeCone_viaNoAlt {k : ℕ} [NeZero k] (hk : 4 ≤ k) {z : ZMod k → ℝ} (i : ZMod k)
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (h0 : 0 < ε * (z (i + 2) - z (i + 1)))
    (hrun : ∀ j : ℕ, 3 ≤ j → j < k → ε * (z (i + ((j + 1 : ℕ) : ZMod k)) - z (i + (j : ZMod k))) < 0) :
    RobUni z := by
  have : Fact (1 < k) := ⟨by omega⟩
  have edge_pos : ∀ {ε' : ℝ} {z' : ZMod k → ℝ},
      0 < ε' * (z' (i + 2) - z' (i + 1)) →
      (∀ j : ℕ, 3 ≤ j → j < k → ε' * (z' (i + ((j + 1 : ℕ) : ZMod k)) - z' (i + (j : ZMod k))) < 0) →
      ε' = 1 →
      (∀ v ∉ ({i, i + 1} : Finset (ZMod k)), z' (v - 1) < z' v ∨ z' (v + 1) < z' v) ∧
      (∀ v ∉ ({i + 2, i + 3} : Finset (ZMod k)), z' v < z' (v - 1) ∨ z' v < z' (v + 1)) := by
    intro ε' z' h0' hrun' heps
    subst heps
    simp only [one_mul, sub_pos, sub_neg] at h0' hrun'
    constructor
    · intro v hv
      simp only [mem_insert, mem_singleton, not_or] at hv
      have hm : 2 ≤ (v - i).val ∧ (v - i).val < k := by
        have hlt := ZMod.val_lt (v - i)
        have hne0 : (v - i).val ≠ 0 := fun h => hv.1 (by
          have : v - i = 0 := by rw [← ZMod.natCast_zmod_val (v - i), h]; simp
          linear_combination this)
        have hne1 : (v - i).val ≠ 1 := fun h => hv.2 (by
          have : v - i = 1 := by rw [← ZMod.natCast_zmod_val (v - i), h]; simp
          linear_combination this)
        omega
      set m := (v - i).val
      have hv_eq : v = i + (m : ZMod k) := by
        dsimp [m]; rw [ZMod.natCast_zmod_val]; ring
      rcases (by omega : m = 2 ∨ 3 ≤ m) with hm2 | hm3
      · left; rw [hv_eq, hm2]
        rw [show i + ((2 : ℕ) : ZMod k) - 1 = i + 1 by push_cast; ring]
        rw [show i + ((2 : ℕ) : ZMod k) = i + 2 by push_cast; ring]
        exact h0'
      · right; rw [hv_eq]
        have h1 := hrun' m hm3 hm.2
        rwa [show i + ((m + 1 : ℕ) : ZMod k) = i + (m : ZMod k) + 1 by push_cast; ring] at h1
    · intro v hv
      simp only [mem_insert, mem_singleton, not_or] at hv
      have hlt := ZMod.val_lt (v - i)
      set m := (v - i).val
      have hv_eq : v = i + (m : ZMod k) := by
        dsimp [m]; rw [ZMod.natCast_zmod_val]; ring
      have hne2 : m ≠ 2 := fun h => hv.1 (by rw [hv_eq, h]; norm_num)
      have hne3 : m ≠ 3 := fun h => hv.2 (by rw [hv_eq, h]; norm_num)
      rcases (by omega : m = 0 ∨ m = 1 ∨ 4 ≤ m) with hm0 | hm1 | hm4
      · left
        have h00 : v = i + ((k : ℕ) : ZMod k) := by rw [hv_eq, hm0, ZMod.natCast_self]; simp
        have h1 := hrun' (k - 1) (by omega) (by omega)
        have hk1 : ((k - 1 + 1 : ℕ) : ZMod k) = (k : ZMod k) := by congr 1; omega
        rw [hk1] at h1
        rwa [h00, show i + (k : ZMod k) - 1 = i + ((k - 1 : ℕ) : ZMod k) by
          rw [Nat.cast_sub (by omega), ZMod.natCast_self]; ring]
      · right; rw [hv_eq, hm1]
        rw [show i + ((1 : ℕ) : ZMod k) + 1 = i + 2 by push_cast; ring]
        rw [show i + ((1 : ℕ) : ZMod k) = i + 1 by push_cast; ring]
        exact h0'
      · left; rw [hv_eq]
        have h1 := hrun' (m - 1) (by omega) (by omega)
        have hm11 : ((m - 1 + 1 : ℕ) : ZMod k) = (m : ZMod k) := by congr 1; omega
        rw [hm11] at h1
        rwa [show i + (m : ZMod k) - 1 = i + ((m - 1 : ℕ) : ZMod k) by
          rw [Nat.cast_sub (by omega)]; ring]
  rcases hε with hε1 | hε1
  · rw [hε1] at h0 hrun
    obtain ⟨hMn, hMx⟩ := edge_pos h0 hrun rfl
    exact robUni_of_noAlt {i, i + 1} {i + 2, i + 3} hMn hMx (fun B b c d hb hbc hcd hd h =>
      arc_noAlt hk i hb hbc hcd hd h)
  · rw [hε1] at h0 hrun
    have h0' : 0 < (1 : ℝ) * ((-z (i + 2)) - (-z (i + 1))) := by linarith
    have hrun' : ∀ j : ℕ, 3 ≤ j → j < k →
        (1 : ℝ) * ((-z (i + ((j + 1 : ℕ) : ZMod k))) - (-z (i + (j : ZMod k)))) < 0 := by
      intro j hj hjk; have := hrun j hj hjk; linarith
    obtain ⟨hMn, hMx⟩ := edge_pos (z' := fun j => -z j) h0' hrun' rfl
    refine robUni_of_noAlt {i + 2, i + 3} {i, i + 1} ?_ ?_ ?_
    · intro v hv; rcases hMx v hv with h | h <;> [left; right] <;> linarith
    · intro v hv; rcases hMn v hv with h | h <;> [left; right] <;> linarith
    · intro B b c d hb hbc hcd hd ⟨hB, hBb, hBc, hBd⟩
      exact arc_noAlt hk i (B := B + (b : ZMod k)) (b := c - b) (c := d - b) (d := k - b)
        (by omega) (by omega) (by omega) (by omega)
        ⟨hBb, by rw [add_assoc, ← Nat.cast_add, show b + (c - b) = c by omega]; exact hBc,
          by rw [add_assoc, ← Nat.cast_add, show b + (d - b) = d by omega]; exact hBd,
          by rw [add_assoc, ← Nat.cast_add, show b + (k - b) = k by omega, ZMod.natCast_self, add_zero]; exact hB⟩

/-! ## 3. `robUni_of_splitRows4_viaNoAlt` -/

theorem robUni_of_splitRows4_viaNoAlt {X : ZMod 4 → ℝ³} {w : ℝ³} {ρ : ℝ} (hρ : ρ ≠ 0)
    (hcyc : ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 → 0 < ρ * det3 (X (i + 1) - X i) (X j - X i) w)
    {a c : ZMod 4} {σ : ℝ} (hS : Minimality.Split.SplitRows X w a c σ) :
    RobUni (fun i => ⟪X i, w⟫) := by
  let z : ZMod 4 → ℝ := fun i => ⟪X i, w⟫
  let h : ZMod 4 → ℝ := fun m => ρ * det3 (X (a + 1) - X a) (X m - X a) w
  let rise : ZMod 4 → ℝ := fun i => det3 (X (i + 1) - X i) (X (a + 1) - X a) w
  have ha2_ne_a : a + 2 ≠ a := fun h0 => absurd (show (2 : ZMod 4) = 0 by linear_combination h0) (by decide)
  have ha2_ne_a1 : a + 2 ≠ a + 1 := fun h0 => absurd (show (1 : ZMod 4) = 0 by linear_combination h0) (by decide)
  have ha3_ne_a : a + 3 ≠ a := fun h0 => absurd (show (3 : ZMod 4) = 0 by linear_combination h0) (by decide)
  have ha3_ne_a1 : a + 3 ≠ a + 1 := fun h0 => absurd (show (2 : ZMod 4) = 0 by linear_combination h0) (by decide)
  have ha1_ne_a : a + 1 ≠ a := fun h0 => absurd (show (1 : ZMod 4) = 0 by linear_combination h0) (by decide)
  have hh2 : 0 < h (a + 2) := hcyc a (a + 2) ha2_ne_a ha2_ne_a1
  have hh3 : 0 < h (a + 3) := hcyc a (a + 3) ha3_ne_a ha3_ne_a1
  have hrise_a1 : -ρ * rise (a + 1) = h (a + 2) := by
    dsimp [h, rise]; rw [add_assoc, show (1 + 1 : ZMod 4) = 2 by decide]
    simp only [det3, inner3, PiLp.sub_apply, cross_apply_zero, cross_apply_one, cross_apply_two]; ring
  have hrise_a3 : -ρ * rise (a + 3) = -h (a + 3) := by
    dsimp [h, rise]; rw [add_assoc, show (3 + 1 : ZMod 4) = 0 by decide, add_zero]
    simp only [det3, inner3, PiLp.sub_apply, cross_apply_zero, cross_apply_one, cross_apply_two]; ring
  have hopp : rise (a + 1) * rise (a + 3) < 0 := by
    have hmul : (-ρ * rise (a + 1)) * (-ρ * rise (a + 3)) < 0 := by rw [hrise_a1, hrise_a3]; nlinarith
    have hid : (-ρ * rise (a + 1)) * (-ρ * rise (a + 3)) = ρ ^ 2 * (rise (a + 1) * rise (a + 3)) := by ring
    rw [hid] at hmul
    exact neg_of_mul_neg_right hmul (sq_pos_of_ne_zero hρ).le
  have hdet_eq : ∀ u v : ℝ³, Minimality.Split.det3 u v w = det3 u v w := fun u v => by
    simp only [Minimality.Split.det3, det3, Minimality.Split.inner3,
      Minimality.Split.cross_0, Minimality.Split.cross_1, Minimality.Split.cross_2]
  have hS' : ∀ i j : ZMod 4, i ≠ a → (j = i ∨ j = i + 1) → j ≠ c →
      0 < σ * ((z j - z c) * rise i) := fun i j hi hij hjc => by
    have hs := hS i j hi hij hjc
    dsimp [rise]
    rwa [show ⟪X j - X c, w⟫ = z j - z c from inner_sub_left _ _ _, hdet_eq] at hs
  have hc_mono : 0 < (z c - z (c - 1)) * (z (c + 1) - z c) := by
    by_cases hca : c = a
    · subst hca
      have h1 := hS' (c + 1) (c + 1) ha1_ne_a (Or.inl rfl) ha1_ne_a
      have h3 := hS' (c + 3) (c + 3) ha3_ne_a (Or.inl rfl) ha3_ne_a
      have hprod : 0 < (σ ^ 2 * (rise (c + 1) * rise (c + 3))) * ((z (c + 1) - z c) * (z (c + 3) - z c)) := by
        have := mul_pos h1 h3; linarith
      have hσ_ne : σ ≠ 0 := fun h0 => by rw [h0, zero_mul] at h1; exact lt_irrefl 0 h1
      have hneg : σ ^ 2 * (rise (c + 1) * rise (c + 3)) < 0 :=
        mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hσ_ne) hopp
      have hopp_z : (z (c + 1) - z c) * (z (c + 3) - z c) < 0 := neg_of_mul_pos_right hprod hneg.le
      have hcm1 : c - 1 = c + 3 := by rw [sub_eq_add_neg, show (-1 : ZMod 4) = 3 by decide]
      rw [hcm1]
      nlinarith
    · by_cases hca1 : c = a + 1
      · subst hca1
        have h1 := hS' (a + 1) (a + 2) ha1_ne_a (Or.inr (by rw [add_assoc]; ring_nf))
          (fun heq => ha2_ne_a1 heq)
        have h3 := hS' (a + 3) a ha3_ne_a (Or.inr (by rw [add_assoc, show (3 + 1 : ZMod 4) = 0 by decide, add_zero]))
          ha1_ne_a.symm
        have hprod : 0 < (σ ^ 2 * (rise (a + 1) * rise (a + 3))) * ((z (a + 2) - z (a + 1)) * (z a - z (a + 1))) := by
          have := mul_pos h1 h3; linarith
        have hσ_ne : σ ≠ 0 := fun h0 => by rw [h0, zero_mul] at h1; exact lt_irrefl 0 h1
        have hneg : σ ^ 2 * (rise (a + 1) * rise (a + 3)) < 0 :=
          mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hσ_ne) hopp
        have hopp_z : (z (a + 2) - z (a + 1)) * (z a - z (a + 1)) < 0 := neg_of_mul_pos_right hprod hneg.le
        have hsub : a + 1 - 1 = a := by ring
        have hadd : a + 1 + 1 = a + 2 := by rw [add_assoc]; ring_nf
        rw [hsub, hadd]
        nlinarith
      · exact Minimality.GenRev.mono_at_c_of_splitRows (by decide) hρ
          (fun i j hij hij1 => by
            have := hcyc i j hij hij1
            simp only [det3, inner3, cross_apply_zero, cross_apply_one, cross_apply_two] at this ⊢
            convert this using 2)
          hca hca1 hS
  exact robUni_of_monoCorners_viaNoAlt (by decide) {c} (by simp) (fun v hv => by
    rw [mem_singleton.1 hv]; exact hc_mono)

/-! ## 4. `robUniLex_adjTie_viaNoAlt` and `robUniLex_four_of_mixed_viaNoAlt` -/

private lemma toLex3_lt_first {p q : ℝ × ℝ × ℝ} (h : p.1 < q.1) :
    toLex (p.1, toLex (p.2.1, p.2.2)) < toLex (q.1, toLex (q.2.1, q.2.2)) :=
  Prod.Lex.lt_iff.2 (Or.inl h)

private lemma toLex3_lt_second {p q : ℝ × ℝ × ℝ} (h1 : p.1 = q.1) (h2 : p.2.1 < q.2.1) :
    toLex (p.1, toLex (p.2.1, p.2.2)) < toLex (q.1, toLex (q.2.1, q.2.2)) :=
  Prod.Lex.lt_iff.2 (Or.inr ⟨h1, Prod.Lex.lt_iff.2 (Or.inl h2)⟩)

private lemma zmod4_cases (v : ZMod 4) : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by
  fin_cases v
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

private lemma zmod4_noAlt_of_skip {B : ZMod 4} {b c d : ℕ} (hb : 0 < b) (hbc : b < c) (hcd : c < d) (hd : d < 4)
    {s : ZMod 4} (hs : s ≠ B ∧ s ≠ B + b ∧ s ≠ B + c ∧ s ≠ B + d) : False := by
  have hb1 : b = 1 := by omega
  have hc2 : c = 2 := by omega
  have hd3 : d = 3 := by omega
  subst hb1 hc2 hd3
  rcases zmod4_cases B with rfl | rfl | rfl | rfl <;>
  rcases zmod4_cases s with rfl | rfl | rfl | rfl <;>
  simp only [Nat.cast_one, Nat.cast_ofNat, zero_add] at hs <;>
  first | exact hs.1 rfl | exact hs.2.1 rfl | exact hs.2.2.1 rfl | exact hs.2.2.2 rfl

theorem robUniLex_adjTie_viaNoAlt {z : ZMod 4 → ℝ} (i : ZMod 4) (h01 : z i = z (i + 1))
    (hn : ¬ (z (i + 2) = z i ∧ z (i + 3) = z i)) :
    RobUniLex (fun j => (z j, (if j = i then 1 else if j = i + 1 then -1 else 0 : ℝ), (0 : ℝ))) ∨
      RobUniLex (fun j => (z j, (if j = i then -1 else if j = i + 1 then 1 else 0 : ℝ), (0 : ℝ))) := by
  have h10 : i + 1 ≠ i := fun h => absurd (show (1 : ZMod 4) = 0 by linear_combination h) (by decide)
  have h_one_skip : ∀ (f : ZMod 4 → ℝ × ℝ × ℝ) (s : ZMod 4),
      ((toLex ((f (s - 1)).1, toLex ((f (s - 1)).2.1, (f (s - 1)).2.2)) <
          toLex ((f s).1, toLex ((f s).2.1, (f s).2.2)) ∧
        toLex ((f s).1, toLex ((f s).2.1, (f s).2.2)) <
          toLex ((f (s + 1)).1, toLex ((f (s + 1)).2.1, (f (s + 1)).2.2))) ∨
       (toLex ((f (s + 1)).1, toLex ((f (s + 1)).2.1, (f (s + 1)).2.2)) <
          toLex ((f s).1, toLex ((f s).2.1, (f s).2.2)) ∧
        toLex ((f s).1, toLex ((f s).2.1, (f s).2.2)) <
          toLex ((f (s - 1)).1, toLex ((f (s - 1)).2.1, (f (s - 1)).2.2)))) →
      RobUniLex f := by
    intro f s hs
    rw [robUniLex_iff_O]
    refine robUniO_of_noAlt (univ \ {s}) (univ \ {s}) ?_ ?_ ?_
    · intro v hv
      have hvs : v = s := by by_contra hne; exact hv (mem_sdiff.2 ⟨mem_univ v, fun h => hne (mem_singleton.1 h)⟩)
      subst hvs; rcases hs with ⟨h1, _⟩ | ⟨h2, _⟩ <;> [exact Or.inl h1; exact Or.inr h2]
    · intro v hv
      have hvs : v = s := by by_contra hne; exact hv (mem_sdiff.2 ⟨mem_univ v, fun h => hne (mem_singleton.1 h)⟩)
      subst hvs; rcases hs with ⟨_, h2⟩ | ⟨_, h1⟩ <;> [exact Or.inr h2; exact Or.inl h1]
    · intro B b c d hb hbc hcd hd ⟨hB, hBb, hBc, hBd⟩
      simp only [mem_sdiff, mem_univ, mem_singleton, true_and] at hB hBb hBc hBd
      exact zmod4_noAlt_of_skip hb hbc hcd hd ⟨Ne.symm hB, Ne.symm hBb, Ne.symm hBc, Ne.symm hBd⟩
  by_cases h2 : z (i + 2) = z i
  · have h3 : z (i + 3) ≠ z i := fun h => hn ⟨h2, h⟩
    have hi_sub : i - 1 = i + 3 := by rw [sub_eq_add_neg, show (-1 : ZMod 4) = 3 by decide]
    rcases lt_or_gt_of_ne h3 with h3lt | h3gt
    · right; refine h_one_skip _ i (Or.inl ⟨?_, ?_⟩)
      · rw [hi_sub]; exact toLex3_lt_first h3lt
      · exact toLex3_lt_second h01 (by simp [h10])
    · left; refine h_one_skip _ i (Or.inr ⟨?_, ?_⟩)
      · exact toLex3_lt_second h01.symm (by simp [h10])
      · rw [hi_sub]; exact toLex3_lt_first h3gt
  · have hi1_add : i + 1 + 1 = i + 2 := by ring
    have hi1_sub : i + 1 - 1 = i := by ring
    rcases lt_or_gt_of_ne h2 with h2lt | h2gt
    · left; refine h_one_skip _ (i + 1) (Or.inr ⟨?_, ?_⟩)
      · rw [hi1_add]; exact toLex3_lt_first (by linarith)
      · rw [hi1_sub]; exact toLex3_lt_second h01.symm (by simp [h10])
    · right; refine h_one_skip _ (i + 1) (Or.inl ⟨?_, ?_⟩)
      · rw [hi1_sub]; exact toLex3_lt_second h01 (by simp [h10])
      · rw [hi1_add]; exact toLex3_lt_first (by linarith)

theorem robUniLex_four_of_mixed_viaNoAlt {z : ZMod 4 → ℝ × ℝ × ℝ}
    (hn : ∃ p ∈ diagPairs, LexLt3 (z p.1) (z p.2))
    (hp : ∃ q ∈ diagPairs, LexLt3 (z q.2) (z q.1)) :
    RobUniLex z := by
  classical
  rw [robUniLex_iff_O]
  let zz : ZMod 4 → ℝ ×ₗ ℝ ×ₗ ℝ := fun i => toLex ((z i).1, toLex ((z i).2.1, (z i).2.2))
  let Mn : Finset (ZMod 4) := univ.filter (fun v => ¬ (zz (v - 1) < zz v ∨ zz (v + 1) < zz v))
  let Mx : Finset (ZMod 4) := univ.filter (fun v => ¬ (zz v < zz (v - 1) ∨ zz v < zz (v + 1)))
  refine robUniO_of_noAlt Mn Mx ?_ ?_ ?_
  · intro v hv; by_contra hnot; exact hv (mem_filter.2 ⟨mem_univ v, hnot⟩)
  · intro v hv; by_contra hnot; exact hv (mem_filter.2 ⟨mem_univ v, hnot⟩)
  · intro B b c d hb hbc hcd hd ⟨hB, hBb, hBc, hBd⟩
    have hb1 : b = 1 := by omega
    have hc2 : c = 2 := by omega
    have hd3 : d = 3 := by omega
    subst hb1 hc2 hd3
    simp only [Mn, Mx, mem_filter, mem_univ, true_and, not_or, not_lt] at hB hBb hBc hBd
    have hB_cases : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 := by
      fin_cases B
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
    obtain ⟨p, hpm, hpn⟩ := hn
    obtain ⟨q, hqm, hqp⟩ := hp
    simp only [diagPairs, mem_product, mem_insert, mem_singleton] at hpm hqm
    have h_toLex : ∀ {p q : ℝ × ℝ × ℝ}, LexLt3 p q →
        toLex (p.1, toLex (p.2.1, p.2.2)) < toLex (q.1, toLex (q.2.1, q.2.2)) := by
      intro p q h
      simp only [LexLt3, LexPos3, Prod.Lex.lt_iff, ofLex_toLex] at h ⊢
      rcases h with h1 | ⟨h1, h2 | ⟨h2, h3⟩⟩
      · exact Or.inl (by linarith)
      · exact Or.inr ⟨by linarith, Or.inl (by linarith)⟩
      · exact Or.inr ⟨by linarith, Or.inr ⟨by linarith, by linarith⟩⟩
    have hp' : zz p.1 < zz p.2 := h_toLex hpn
    have hq' : zz q.2 < zz q.1 := h_toLex hqp
    rcases hB_cases with rfl | rfl | rfl | rfl
    · have h10 : zz 1 ≤ zz 0 := hBb.1
      have h12 : zz 1 ≤ zz 2 := hBb.2
      have h32 : zz 3 ≤ zz 2 := hBd.1
      have h30 : zz 3 ≤ zz 0 := hBd.2
      rcases hpm with ⟨hp1 | hp1, hp2 | hp2⟩ <;> rw [hp1, hp2] at hp' <;> exact absurd hp' (not_lt_of_ge (by assumption))
    · have h21 : zz 2 ≤ zz 1 := hBb.1
      have h23 : zz 2 ≤ zz 3 := hBb.2
      have h03 : zz 0 ≤ zz 3 := hBd.1
      have h01 : zz 0 ≤ zz 1 := hBd.2
      rcases hqm with ⟨hq1 | hq1, hq2 | hq2⟩ <;> rw [hq1, hq2] at hq' <;> exact absurd hq' (not_lt_of_ge (by assumption))
    · have h32 : zz 3 ≤ zz 2 := hBb.1
      have h30 : zz 3 ≤ zz 0 := hBb.2
      have h10 : zz 1 ≤ zz 0 := hBd.1
      have h12 : zz 1 ≤ zz 2 := hBd.2
      rcases hpm with ⟨hp1 | hp1, hp2 | hp2⟩ <;> rw [hp1, hp2] at hp' <;> exact absurd hp' (not_lt_of_ge (by assumption))
    · have h03 : zz 0 ≤ zz 3 := hBb.1
      have h01 : zz 0 ≤ zz 1 := hBb.2
      have h21 : zz 2 ≤ zz 1 := hBd.1
      have h23 : zz 2 ≤ zz 3 := hBd.2
      rcases hqm with ⟨hq1 | hq1, hq2 | hq2⟩ <;> rw [hq1, hq2] at hq' <;> exact absurd hq' (not_lt_of_ge (by assumption))

end Minimality.RimOrderInst
