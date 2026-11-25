module

public import Minimality.Q4Leaf
public import Minimality.Sym24Transport

/-!
# Edge-cone leaf for `k`-rim closed cells (Carbon A57, generalised; Hydrogen Task EA)

Not a hole shrink by itself (an edge-cone point of a closed cell is a closed-cell RobUni view, as for `Q4Any`): it
makes that leaf checkable from two closure views `g`, `g'` (signs and 2x2 determinants).  `Hole24` carries
`¬ EdgeAny F`.

* `robUni_of_edgeCone`: edge cone `E_{k,i}^ε` implies `RobUni` for all `k ≥ 4`.
* `Overlap`, `exists_pos_of_overlap`: 1D Helly for affine functions on `[0, 1]`.
* `edgeVec`, `EdgeAny`, `edgeAny_isRupert`, `hole24_edge`: closed-cell edge-cone leaf.
-/

set_option autoImplicit false

open scoped RealInnerProductSpace
open Finset

@[expose] public section

namespace Minimality.GenPlus

open Minimality Minimality.H21

/-! ### Edge cone implies `RobUni` -/

private theorem robUni_shift {k : ℕ} {z : ZMod k → ℝ} (i : ZMod k)
    (h : RobUni fun j : ZMod k => z (i + j)) : RobUni z := by
  intro B b c d hb hbc hcd hd ⟨h1, h2, h3, h4⟩
  refine h (B - i) b c d hb hbc hcd hd ⟨?_, ?_, ?_, ?_⟩
  · simpa [← add_assoc] using h1
  · simpa [← add_assoc] using h2
  · simpa [← add_assoc] using h3
  · simpa [← add_assoc] using h4

private theorem robUni_neg {k : ℕ} {z : ZMod k → ℝ} (h : RobUni fun j : ZMod k => -z j) :
    RobUni z := by
  intro B b c d hb hbc hcd hd ⟨h1, h2, h3, h4⟩
  refine h (B + b) (c - b) (d - b) (k - b) (by omega) (by omega) (by omega) (by omega) ?_
  have hb1 : B + (b : ZMod k) + ((c - b : ℕ) : ZMod k) = B + (c : ZMod k) := by
    rw [add_assoc, ← Nat.cast_add, Nat.add_sub_cancel' hbc.le]
  have hb2 : B + (b : ZMod k) + ((d - b : ℕ) : ZMod k) = B + (d : ZMod k) := by
    rw [add_assoc, ← Nat.cast_add, Nat.add_sub_cancel' (le_trans hbc.le hcd.le)]
  have hb3 : B + (b : ZMod k) + ((k - b : ℕ) : ZMod k) = B := by
    rw [add_assoc, ← Nat.cast_add, Nat.add_sub_cancel' (le_trans (le_trans hbc.le hcd.le) hd.le),
      ZMod.natCast_self, add_zero]
  rw [hb1, hb2, hb3]
  exact ⟨neg_le_neg h2, neg_le_neg h4, neg_le_neg h1, neg_le_neg h3⟩

private theorem robUni_canon {k : ℕ} [NeZero k] (_hk : 4 ≤ k) {w : ZMod k → ℝ}
    (h12 : w 1 < w 2)
    (hrun : ∀ j : ℕ, 3 ≤ j → j < k → w ((j + 1 : ℕ) : ZMod k) < w (j : ZMod k)) :
    RobUni w := by
  have hdec : ∀ m n : ℕ, 3 ≤ m → m < n → n ≤ k → w (n : ZMod k) < w (m : ZMod k) := by
    intro m n hm hmn hnk
    induction n with
    | zero => omega
    | succ n ih =>
      rcases Nat.eq_or_lt_of_le hmn with h_eq | hlt
      · have hnm : n = m := by omega
        subst hnm
        exact hrun n hm hnk
      · exact lt_trans (hrun n (by omega) (by omega)) (ih (by omega) (by omega))
  have hdec_mod : ∀ a b : ℕ, 3 ≤ a → a < b → b < k → w (b : ZMod k) < w (a : ZMod k) :=
    fun a b ha hab hbk => hdec a b ha hab hbk.le
  have hdec_zero : ∀ a : ℕ, 3 ≤ a → a < k → w 0 < w (a : ZMod k) := fun a ha hak => by
    have := hdec a k ha hak (le_refl k)
    simpa [ZMod.natCast_self] using this
  -- Core case: `a0 < a1 < a2 < a3 < k` (natural numbers)
  have h_core : ∀ a0 a1 a2 a3 : ℕ, a0 < a1 → a1 < a2 → a2 < a3 → a3 < k →
      ¬ (w (a1 : ZMod k) ≤ w (a0 : ZMod k) ∧ w (a1 : ZMod k) ≤ w (a2 : ZMod k) ∧
         w (a3 : ZMod k) ≤ w (a0 : ZMod k) ∧ w (a3 : ZMod k) ≤ w (a2 : ZMod k)) := by
    intro a0 a1 a2 a3 h01 h12' h23 h3k ⟨e1, e2, e3, e4⟩
    by_cases ha0_3 : 3 ≤ a0
    · have := hdec_mod a1 a2 (by omega) h12' (by omega); linarith
    · interval_cases a0
      · -- a0 = 0
        have := hdec_zero a3 (by omega) h3k
        rw [Nat.cast_zero] at e3
        linarith
      · -- a0 = 1
        by_cases ha1_2 : a1 = 2
        · subst ha1_2
          have : w ((1 : ℕ) : ZMod k) < w ((2 : ℕ) : ZMod k) := by simpa using h12
          linarith
        · have := hdec_mod a1 a2 (by omega) h12' (by omega); linarith
      · -- a0 = 2
        have := hdec_mod a1 a2 (by omega) h12' (by omega); linarith
  -- Second case: `a1 < a2 < a3 < a0 < k` (natural numbers)
  have h_core2 : ∀ a0 a1 a2 a3 : ℕ, a1 < a2 → a2 < a3 → a3 < a0 → a0 < k →
      ¬ (w (a1 : ZMod k) ≤ w (a0 : ZMod k) ∧ w (a1 : ZMod k) ≤ w (a2 : ZMod k) ∧
         w (a3 : ZMod k) ≤ w (a0 : ZMod k) ∧ w (a3 : ZMod k) ≤ w (a2 : ZMod k)) := by
    intro a0 a1 a2 a3 h12' h23 h30 h0k ⟨e1, e2, e3, e4⟩
    by_cases ha1_3 : 3 ≤ a1
    · have := hdec_mod a1 a0 ha1_3 (by omega) h0k; linarith
    · interval_cases a1
      · -- a1 = 0
        by_cases ha2_3 : 3 ≤ a2
        · have := hdec_mod a3 a0 (by omega) h30 h0k; linarith
        · interval_cases a2
          · -- a2 = 1
            by_cases ha3_2 : a3 = 2
            · subst ha3_2
              have : w ((1 : ℕ) : ZMod k) < w ((2 : ℕ) : ZMod k) := by simpa using h12
              linarith
            · have := hdec_mod a3 a0 (by omega) h30 h0k; linarith
          · -- a2 = 2
            have := hdec_mod a3 a0 (by omega) h30 h0k; linarith
      · -- a1 = 1
        have := hdec_mod a3 a0 (by omega) h30 h0k; linarith
      · -- a1 = 2
        have := hdec_mod a3 a0 (by omega) h30 h0k; linarith
  -- Main proof for arbitrary B, b, c, d
  intro B b c d hb hbc hcd hd ⟨e1, e2, e3, e4⟩
  set a0 := B.val
  have ha0 : a0 < k := B.val_lt
  have hval : ∀ n : ℕ, (B + (n : ZMod k) : ZMod k) = ((a0 + n : ℕ) : ZMod k) := fun n => by
    rw [Nat.cast_add, ZMod.natCast_zmod_val]
  by_cases h_d : a0 + d < k
  · rw [hval b] at e1 e2
    rw [hval c] at e2 e4
    rw [hval d] at e3 e4
    rw [← ZMod.natCast_zmod_val B] at e1 e3
    exact h_core a0 (a0 + b) (a0 + c) (a0 + d) (by omega) (by omega) (by omega) h_d
      ⟨e1, e2, e3, e4⟩
  · by_cases h_b : k ≤ a0 + b
    · have hval' : ∀ n : ℕ, b ≤ n → n < k → B + (n : ZMod k) = ((a0 + n - k : ℕ) : ZMod k) := by
        intro n hbn _
        rw [hval n, ← ZMod.natCast_mod, Nat.mod_eq_sub_mod (by omega),
          Nat.mod_eq_of_lt (by omega)]
      rw [hval' b (le_refl b) (by omega)] at e1 e2
      rw [hval' c (by omega) (by omega)] at e2 e4
      rw [hval' d (by omega) hd] at e3 e4
      rw [← ZMod.natCast_zmod_val B] at e1 e3
      exact h_core2 a0 (a0 + b - k) (a0 + c - k) (a0 + d - k)
        (by omega) (by omega) (by omega) ha0 ⟨e1, e2, e3, e4⟩
    · by_cases h_c : k ≤ a0 + c
      · have hvb : B + (b : ZMod k) = ((a0 + b : ℕ) : ZMod k) := hval b
        have hvc : B + (c : ZMod k) = ((a0 + c - k : ℕ) : ZMod k) := by
          rw [hval c, ← ZMod.natCast_mod, Nat.mod_eq_sub_mod h_c, Nat.mod_eq_of_lt (by omega)]
        have hvd : B + (d : ZMod k) = ((a0 + d - k : ℕ) : ZMod k) := by
          rw [hval d, ← ZMod.natCast_mod, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [hvb] at e1 e2
        rw [hvc] at e2 e4
        rw [hvd] at e3 e4
        rw [← ZMod.natCast_zmod_val B] at e1 e3
        exact h_core (a0 + c - k) (a0 + d - k) a0 (a0 + b)
          (by omega) (by omega) (by omega) (by omega) ⟨e4, e3, e2, e1⟩
      · have hvb : B + (b : ZMod k) = ((a0 + b : ℕ) : ZMod k) := hval b
        have hvc : B + (c : ZMod k) = ((a0 + c : ℕ) : ZMod k) := hval c
        have hvd : B + (d : ZMod k) = ((a0 + d - k : ℕ) : ZMod k) := by
          rw [hval d, ← ZMod.natCast_mod, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [hvb] at e1 e2
        rw [hvc] at e2 e4
        rw [hvd] at e3 e4
        rw [← ZMod.natCast_zmod_val B] at e1 e3
        exact h_core2 (a0 + c) (a0 + d - k) a0 (a0 + b)
          (by omega) (by omega) (by omega) (by omega) ⟨e4, e3, e2, e1⟩

/-- **APPROVED.**  Edge cone `E_{k,i}^ε` implies `RobUni` (A57 Theorem 1.1 "if", generalised from k = 5 to all
k ≥ 4; checked exactly over all weak orders for k = 4..7, 0 failures): one rising edge `i+1 → i+2` and a strictly
falling run `i+3 → i+4 → ... → i+k = i` (sign `ε`). -/
theorem robUni_of_edgeCone {k : ℕ} [NeZero k] (hk : 4 ≤ k) {z : ZMod k → ℝ} (i : ZMod k) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) (h0 : 0 < ε * (z (i + 2) - z (i + 1)))
    (hrun : ∀ j : ℕ, 3 ≤ j → j < k → ε * (z (i + ((j + 1 : ℕ) : ZMod k)) - z (i + (j : ZMod k))) < 0) :
    RobUni z := by
  rcases hε with rfl | rfl
  · refine robUni_shift i (robUni_canon hk (w := fun j => z (i + j)) ?_ ?_)
    · simpa using h0
    · intro j hj hjk
      have := hrun j hj hjk
      simpa using this
  · refine robUni_shift i (robUni_neg (robUni_canon hk (w := fun j => -z (i + j)) ?_ ?_))
    · linarith
    · intro j hj hjk
      have := hrun j hj hjk
      linarith

/-! ### 1D Helly for affine functions on `[0, 1]` -/

/-- **APPROVED.**  Two affine functions with values `pa, qa` and `pb, qb` at the ends of `[0, 1]` are positive
together somewhere on it (A57 Theorem 2.3(B)). -/
def Overlap (pa qa pb qb : ℝ) : Prop :=
  (0 < pa ∧ 0 < pb) ∨ (0 < qa ∧ 0 < qb) ∨ (0 < pa ∧ 0 < qb ∧ 0 < pa * qb - pb * qa) ∨
    (0 < pb ∧ 0 < qa ∧ 0 < pb * qa - pa * qb)

/-- **APPROVED.**  1D Helly for affine functions on a segment: pairwise overlap (including `j = l`) gives a common
positive point. -/
theorem exists_pos_of_overlap {r : ℕ} (p q : Fin r → ℝ)
    (h : ∀ j l : Fin r, Overlap (p j) (q j) (p l) (q l)) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ ∀ j : Fin r, 0 < (1 - t) * p j + t * q j := by
  by_cases hr : r = 0
  · subst hr
    exact ⟨0, le_rfl, zero_le_one, fun j => Fin.elim0 j⟩
  · have : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hr)
    have h_pos_end : ∀ j : Fin r, 0 < p j ∨ 0 < q j := fun j => by
      rcases h j j with ⟨hp, _⟩ | ⟨hq, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩
      · exact Or.inl hp
      · exact Or.inr hq
      · exact Or.inl hp
      · exact Or.inl hp
    let lo : Fin r → ℝ := fun j => if 0 < p j then 0 else (-p j) / (q j - p j)
    let hi : Fin r → ℝ := fun j => if 0 ≤ q j then 1 else p j / (p j - q j)
    have hlo_lt_hi : ∀ j l : Fin r, lo j < hi l := by
      intro j l
      have hlo_lt1 : lo j < 1 := by
        dsimp [lo]
        split_ifs with hp
        · exact zero_lt_one
        · rcases h_pos_end j with hpj | hqj
          · exact absurd hpj hp
          · rw [div_lt_one (by linarith)]; linarith
      have hhi_pos : 0 < hi l := by
        dsimp [hi]
        split_ifs with hq
        · exact zero_lt_one
        · rcases h_pos_end l with hpl | hql
          · exact div_pos hpl (by linarith)
          · exact absurd hql.le hq
      rcases h j l with ⟨hpj, hpl⟩ | ⟨hqj, hql⟩ | ⟨hpj, hql, _⟩ | ⟨hpl, hqj, hdet⟩
      · simp [lo, hpj, hhi_pos]
      · simp [hi, hql.le, hlo_lt1]
      · simp [lo, hi, hpj, hql.le]
      · by_cases hpj : 0 < p j
        · simp [lo, hpj, hhi_pos]
        · by_cases hql : 0 ≤ q l
          · simp [hi, hql, hlo_lt1]
          · dsimp [lo, hi]
            simp only [hpj, ↓reduceIte, hql]
            have h1 : 0 < q j - p j := by linarith
            have h2 : 0 < p l - q l := by linarith
            rw [div_lt_div_iff₀ h1 h2]
            linarith
    have hlo_nonneg : ∀ j : Fin r, 0 ≤ lo j := fun j => by
      dsimp [lo]
      split_ifs with hp
      · exact le_rfl
      · rcases h_pos_end j with hpj | hqj
        · exact absurd hpj hp
        · exact div_nonneg (by linarith) (by linarith)
    have hhi_le_one : ∀ l : Fin r, hi l ≤ 1 := fun l => by
      dsimp [hi]
      split_ifs with hq
      · exact le_rfl
      · rcases h_pos_end l with hpl | hql
        · rw [div_le_one (by linarith)]; linarith
        · exact absurd hql.le hq
    set L := Finset.univ.sup' Finset.univ_nonempty lo
    set H := Finset.univ.inf' Finset.univ_nonempty hi
    have hLH : L < H := by
      rw [Finset.lt_inf'_iff]
      intro l _
      rw [Finset.sup'_lt_iff]
      intro j _
      exact hlo_lt_hi j l
    have hL0 : 0 ≤ L := by
      obtain ⟨j0⟩ := ‹Nonempty (Fin r)›
      exact le_trans (hlo_nonneg j0) (Finset.le_sup' lo (Finset.mem_univ j0))
    have hH1 : H ≤ 1 := by
      obtain ⟨l0⟩ := ‹Nonempty (Fin r)›
      exact le_trans (Finset.inf'_le hi (Finset.mem_univ l0)) (hhi_le_one l0)
    refine ⟨(L + H) / 2, by linarith, by linarith, fun j => ?_⟩
    set t := (L + H) / 2
    have ht_lo : lo j < t := lt_of_le_of_lt (Finset.le_sup' lo (Finset.mem_univ j)) (by dsimp [t]; linarith)
    have ht_hi : t < hi j := lt_of_lt_of_le (by dsimp [t]; linarith) (Finset.inf'_le hi (Finset.mem_univ j))
    have ht0 : 0 ≤ t := by dsimp [t]; linarith
    have ht1 : t ≤ 1 := by dsimp [t]; linarith
    by_cases hpj : 0 < p j
    · by_cases hqj : 0 ≤ q j
      · have ht_lt1 : t < 1 := lt_of_lt_of_le ht_hi (hhi_le_one j)
        have h1 : 0 < (1 - t) * p j := mul_pos (by linarith) hpj
        have h2 : 0 ≤ t * q j := mul_nonneg ht0 hqj
        linarith
      · dsimp [hi] at ht_hi
        simp only [hqj, ↓reduceIte] at ht_hi
        have hden : 0 < p j - q j := by linarith
        rw [lt_div_iff₀ hden] at ht_hi
        linarith
    · rcases h_pos_end j with hpj' | hqj
      · exact absurd hpj' hpj
      · dsimp [lo] at ht_lo
        simp only [hpj, ↓reduceIte] at ht_lo
        have hden : 0 < q j - p j := by linarith
        rw [div_lt_iff₀ hden] at ht_lo
        linarith

/-! ### Edge-cone closed-cell leaf -/

/-- **APPROVED.**  The `k - 2` edge vectors of the cone `E_{k,i}^ε` for a rim `c`: form 0 is the rising edge, form
`j ≥ 1` the falling edge `i+j+2 → i+j+3`. -/
def edgeVec {n k : ℕ} (x : Fin n → ℝ³) (c : ZMod k → Fin n) (i : ZMod k) (ε : ℝ) (j : ℕ) : ℝ³ :=
  if j = 0 then ε • (x (c (i + 2)) - x (c (i + 1)))
  else (-ε) • (x (c (i + ((j + 3 : ℕ) : ZMod k))) - x (c (i + ((j + 2 : ℕ) : ZMod k))))

/-- **APPROVED.**  Edge-cone leaf on a closed rim cone: a `k`-cycle silhouette `c` (k ≥ 4) of up facets `U` and down
facets `Dn`, a strict cone point `a`, closure points `g`, `g'`, and a cone `(i, ε)` whose `k - 2` forms pass the
pairwise overlap test on `[g, g']`. -/
def EdgeAny {m n : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³} (F : S0xFac m S x) : Prop :=
  ∃ (k : ℕ) (_ : NeZero k) (c : ZMod k → Fin n) (U Dn : Finset (Fin m)) (a g g' : ℝ³) (i : ZMod k) (ε : ℝ),
    4 ≤ k ∧ Function.Injective c ∧ S0xCycUD S c U Dn ∧ CellAt F U Dn a ∧ CellLe F U Dn g ∧
    CellLe F U Dn g' ∧ (ε = 1 ∨ ε = -1) ∧
    ∀ j l : Fin (k - 2), Overlap ⟪edgeVec x c i ε j, g⟫ ⟪edgeVec x c i ε j, g'⟫
      ⟪edgeVec x c i ε l, g⟫ ⟪edgeVec x c i ε l, g'⟫

/-- **APPROVED.** -/
theorem edgeAny_isRupert {m n : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) (hx : Function.Injective x) (h : EdgeAny F) : IsRupert (univ.image x) := by
  rcases h with ⟨k, hk_ne, c, U, Dn, a, g, g', i, ε, hk, hc, hcyc, ha, hg, hg', hε, hov⟩
  obtain ⟨t, ht0, ht1, ht_pos⟩ := exists_pos_of_overlap
    (fun j : Fin (k - 2) => ⟪edgeVec x c i ε j, g⟫)
    (fun j : Fin (k - 2) => ⟪edgeVec x c i ε j, g'⟫) hov
  set u₀ := (1 - t) • g + t • g'
  have hu₀ : CellLe F U Dn u₀ := by
    refine ⟨fun s hs => ?_, fun s hs => ?_⟩
    · dsimp [u₀]
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
      exact add_nonneg (mul_nonneg (by linarith) (hg.1 s hs)) (mul_nonneg ht0 (hg'.1 s hs))
    · dsimp [u₀]
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
      exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos (by linarith) (hg.2 s hs))
        (mul_nonpos_of_nonneg_of_nonpos ht0 (hg'.2 s hs))
  have h_form : ∀ j : Fin (k - 2), 0 < ⟪edgeVec x c i ε j, u₀⟫ := fun j => by
    have := ht_pos j
    dsimp [u₀]
    rwa [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  have hR : RobUni fun m => ⟪x (c m), u₀⟫ := by
    refine robUni_of_edgeCone hk i ε hε ?_ ?_
    · have hf0 := h_form ⟨0, by omega⟩
      dsimp [edgeVec] at hf0
      rwa [real_inner_smul_left, inner_sub_left] at hf0
    · intro j hj hjk
      have hf := h_form ⟨j - 2, by omega⟩
      have hne : j - 2 ≠ 0 := by omega
      dsimp [edgeVec] at hf
      simp only [hne, ↓reduceIte, real_inner_smul_left, inner_sub_left] at hf
      rw [show j - 2 + 3 = j + 1 by omega, show j - 2 + 2 = j by omega] at hf
      linarith
  exact isRupert_of_closedCell hk F hx hc hcyc ha hu₀ hR

/-- **APPROVED.**  Type-24 instance. -/
theorem hole24_edge {x : Fin 7 → ℝ³} (F : S0xFac 9 Minimality.T24.SAT.s0x_S24 x)
    (hx : Function.Injective x) (h : EdgeAny F) : IsRupert (univ.image x) :=
  edgeAny_isRupert F hx h

end Minimality.GenPlus
