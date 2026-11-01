module

public import Minimality.Type08S.C2K5LM

@[expose] public section


/-!
# K5L / N: lex-plane algebra, rotations of `lexUni5_two`, and the lex proofs of the two QTc `α4 > 1` cells
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- `(x, y)` is lex positive. -/
def LP (x y : ℝ) : Prop := 0 < x ∨ (x = 0 ∧ 0 < y)
/-- lex nonnegative. -/
def LPe (x y : ℝ) : Prop := LP x y ∨ (x = 0 ∧ y = 0)

theorem lexLt_iff_LP {a1 a2 b1 b2 : ℝ} : LexLt (a1, a2) (b1, b2) ↔ LP (b1 - a1) (b2 - a2) := by
  unfold LexLt LP
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl (by simp only at h; linarith)
    · right; simp only at h1 h2; exact ⟨by linarith, by linarith⟩
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl (by simp only; linarith)
    · right; simp only; exact ⟨by linarith, by linarith⟩

theorem LP_add {x y x' y' : ℝ} (h : LP x y) (h' : LP x' y') : LP (x + x') (y + y') := by
  unfold LP at *
  rcases h with h | ⟨h1, h2⟩ <;> rcases h' with h' | ⟨h1', h2'⟩
  · left; linarith
  · left; linarith
  · left; linarith
  · right; exact ⟨by linarith, by linarith⟩

theorem LP_add_e {x y x' y' : ℝ} (h : LP x y) (h' : LPe x' y') : LP (x + x') (y + y') := by
  rcases h' with h' | ⟨h1, h2⟩
  · exact LP_add h h'
  · rw [h1, h2, add_zero, add_zero]; exact h

theorem LPe_add {x y x' y' : ℝ} (h : LPe x y) (h' : LPe x' y') : LPe (x + x') (y + y') := by
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl (LP_add_e h h')
  · rw [h1, h2, zero_add, zero_add]; exact h'

theorem LP_smul {c x y : ℝ} (hc : 0 < c) (h : LP x y) : LP (c * x) (c * y) := by
  unfold LP at *
  rcases h with h | ⟨h1, h2⟩
  · left; exact mul_pos hc h
  · right; exact ⟨by rw [h1]; ring, mul_pos hc h2⟩

theorem LPe_smul {c x y : ℝ} (hc : 0 ≤ c) (h : LP x y) : LPe (c * x) (c * y) := by
  rcases hc.lt_or_eq with hc | rfl
  · exact Or.inl (LP_smul hc h)
  · right; simp

theorem LP_ne_zero {x y : ℝ} (h : LP x y) : ¬ (x = 0 ∧ y = 0) := by
  rintro ⟨h1, h2⟩
  unfold LP at h
  rcases h with h | ⟨-, h⟩ <;> linarith

theorem LP_nonneg {x y : ℝ} (h : LP x y) : 0 ≤ x := by
  rcases h with h | ⟨h, -⟩ <;> linarith

theorem LP_neg_not {x y : ℝ} (h : LP x y) : ¬ LP (-x) (-y) := by
  intro h'
  have := LP_add h h'
  simp only [add_neg_cancel] at this
  exact LP_ne_zero this ⟨rfl, rfl⟩

theorem lexUni_shift_k {k : ℕ} [NeZero k] {z w : ZMod k → ℝ} (n : ZMod k)
    (h : LexUni (fun i => z (i + n)) (fun i => w (i + n))) : LexUni z w := by
  classical
  refine ⟨fun i j h1 h2 => ?_, ?_⟩
  · have := h.1 (i - n) (j - n) (by simpa using h1) (by simpa using h2)
    exact sub_left_injective this
  · rw [← h.2]
    have key : ∀ j : ZMod k, (LexLt (z (j - 1), w (j - 1)) (z j, w j) ∧
        LexLt (z (j + 1), w (j + 1)) (z j, w j)) ↔
        (LexLt (z (j - n - 1 + n), w (j - n - 1 + n)) (z (j - n + n), w (j - n + n)) ∧
        LexLt (z (j - n + 1 + n), w (j - n + 1 + n)) (z (j - n + n), w (j - n + n))) := by
      intro j
      have e1 : j - n - 1 + n = j - 1 := by ring
      have e2 : j - n + n = j := by ring
      have e3 : j - n + 1 + n = j + 1 := by ring
      rw [e1, e2, e3]
    refine Finset.card_nbij' (fun i => i - n) (fun i => i + n) ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact (key i).1 hi
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact (key (i + n)).2 (by simpa using hi)
    · intro i _; simp
    · intro i _; simp

theorem lexUni5_r3 (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h : LexLt (z 4, w 4) (z 0, w 0)) (h' : LexLt (z 2, w 2) (z 1, w 1))
    (h0 : LexLt (z 3, w 3) (z 4, w 4) ∨ LexLt (z 3, w 3) (z 2, w 2)) : LexUni z w := by
  apply lexUni_shift_k 3
  have e1 : (1 : ZMod 5) + 3 = 4 := by decide
  have e2 : (2 : ZMod 5) + 3 = 0 := by decide
  have e3 : (3 : ZMod 5) + 3 = 1 := by decide
  have e4 : (4 : ZMod 5) + 3 = 2 := by decide
  have e0 : (0 : ZMod 5) + 3 = 3 := by decide
  refine lexUni5_two _ _ (fun i j h1 h2 => ?_) ?_ ?_ ?_
  · exact add_right_cancel (hinj _ _ h1 h2)
  · simp only [e1, e2]; exact h
  · simp only [e3, e4]; exact h'
  · simp only [e0, e1, e4]; exact h0

theorem lexUni5_r2 (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h : LexLt (z 3, w 3) (z 4, w 4)) (h' : LexLt (z 1, w 1) (z 0, w 0))
    (h0 : LexLt (z 2, w 2) (z 3, w 3) ∨ LexLt (z 2, w 2) (z 1, w 1)) : LexUni z w := by
  apply lexUni_shift_k 2
  have e1 : (1 : ZMod 5) + 2 = 3 := by decide
  have e2 : (2 : ZMod 5) + 2 = 4 := by decide
  have e3 : (3 : ZMod 5) + 2 = 0 := by decide
  have e4 : (4 : ZMod 5) + 2 = 1 := by decide
  have e0 : (0 : ZMod 5) + 2 = 2 := by decide
  refine lexUni5_two _ _ (fun i j h1 h2 => ?_) ?_ ?_ ?_
  · exact add_right_cancel (hinj _ _ h1 h2)
  · simp only [e1, e2]; exact h
  · simp only [e3, e4]; exact h'
  · simp only [e0, e1, e4]; exact h0

theorem lexUni5_r1 (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h : LexLt (z 2, w 2) (z 3, w 3)) (h' : LexLt (z 0, w 0) (z 4, w 4))
    (h0 : LexLt (z 1, w 1) (z 2, w 2) ∨ LexLt (z 1, w 1) (z 0, w 0)) : LexUni z w := by
  apply lexUni_shift_k 1
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  have e2 : (2 : ZMod 5) + 1 = 3 := by decide
  refine lexUni5_two _ _ (fun i j h1 h2 => ?_) ?_ ?_ ?_
  · exact add_right_cancel (hinj _ _ h1 h2)
  · simp only [f1, e2]; exact h
  · simp only [f3, f4]; exact h'
  · simp only [f0, f1, f4]; exact h0

/-- **QTc `α4 > 1`, cell 1: the pentagon `(a, c', a', c, d)`** (indices `0..4`), `ζ(d,b) > 0` (`bz < 0`). -/
theorem pent1_lexUni (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    {κ σ α1 β1 β6 bz bw cz cw A uw : ℝ} (hbz : bz < 0) (hA : 0 < A) (hκ : κ < 0) (hσ : σ < 0)
    (hα1 : 1 ≤ α1) (hβ1 : 0 < β1) (hβ6 : 0 < β6)
    (h0z : z 0 - z 4 = κ * cz + σ * A) (h0w : w 0 - w 4 = κ * cw + σ * uw)
    (h1z : z 1 - z 4 = β1 * bz + α1 * (κ * cz + σ * A))
    (h1w : w 1 - w 4 = β1 * bw + α1 * (κ * cw + σ * uw))
    (h2z : z 2 - z 4 = β6 * bz + cz) (h2w : w 2 - w 4 = β6 * bw + cw)
    (h3z : z 3 - z 4 = cz) (h3w : w 3 - w 4 = cw) : LexUni z w := by
  have nB : LP (-bz) (-bw) := Or.inl (by linarith)
  have pU : LP A uw := Or.inl hA
  have l_a'c : LexLt (z 2, w 2) (z 3, w 3) := by
    rw [lexLt_iff_LP]
    have := LP_smul hβ6 nB
    convert this using 1 <;> linarith
  rcases lexLt_total (show (z 0, w 0) ≠ (z 4, w 4) from fun h =>
      absurd (hinj 0 4 (congrArg Prod.fst h) (congrArg Prod.snd h)) (by decide)) with l_ad | l_da
  · -- `a < d`
    have na : LP (-(κ * cz + σ * A)) (-(κ * cw + σ * uw)) := by
      rw [lexLt_iff_LP] at l_ad
      convert l_ad using 1 <;> linarith
    have l_c'a : LexLt (z 1, w 1) (z 0, w 0) := by
      rw [lexLt_iff_LP]
      have := LP_add_e (LP_smul hβ1 nB) (LPe_smul (sub_nonneg.2 hα1) na)
      convert this using 1 <;> nlinarith
    exact lexUni5_r1 z w hinj l_a'c l_ad (Or.inr l_c'a)
  · -- `d < a`
    have pa : LP (κ * cz + σ * A) (κ * cw + σ * uw) := by
      rw [lexLt_iff_LP] at l_da
      convert l_da using 1 <;> linarith
    have kc : LP (κ * cz) (κ * cw) := by
      have := LP_add pa (LP_smul (neg_pos.2 hσ) pU)
      convert this using 1 <;> ring
    have nc : LP (-cz) (-cw) := by
      have := LP_smul (show 0 < -1 / κ from div_pos_of_neg_of_neg (by norm_num) hκ) kc
      have hk0 : κ ≠ 0 := hκ.ne
      convert this using 1 <;> field_simp
    have l_cd : LexLt (z 3, w 3) (z 4, w 4) := by
      rw [lexLt_iff_LP]; convert nc using 1 <;> linarith
    have l_da' : LexLt (z 4, w 4) (z 0, w 0) := l_da
    rcases lexLt_total (show (z 0, w 0) ≠ (z 1, w 1) from fun h =>
      absurd (hinj 0 1 (congrArg Prod.fst h) (congrArg Prod.snd h)) (by decide)) with l_ac' | l_c'a
    · refine lexUni5_r3 z w hinj l_da' ?_ (Or.inl l_cd)
      exact lexLt_trans_K2 l_a'c (lexLt_trans_K2 l_cd (lexLt_trans_K2 l_da' l_ac'))
    · exact lexUni5_r2 z w hinj l_cd l_c'a (Or.inl l_a'c)

/-- **QTc `α4 > 1`, cell 2: the quadrilateral `(b', c', a', c)`**, `ζ(d,b) < 0` (`bz > 0`).  Needs `κ_a ≥ 0`
in the form `(σ-1)(1-β1) ≤ α1 (σ-κ)`. -/
theorem quad2_lexUni (z w : ZMod 4 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j) {zd wd : ℝ}
    {κ σ α1 β1 β6 bz bw cz cw A uw : ℝ} (hbz : 0 < bz) (hA : 0 < A) (hκ : κ < 0) (hσ : σ < 0)
    (hα1 : 1 < α1) (hβ1 : 0 < β1) (hβ6 : 0 < β6) (hE : (σ - 1) * (1 - β1) ≤ α1 * (σ - κ))
    (h0z : z 0 - zd = κ * cz + (σ - 1) * A) (h0w : w 0 - wd = κ * cw + (σ - 1) * uw)
    (h1z : z 1 - zd = β1 * bz + α1 * (κ * cz + σ * A))
    (h1w : w 1 - wd = β1 * bw + α1 * (κ * cw + σ * uw))
    (h2z : z 2 - zd = β6 * bz + cz) (h2w : w 2 - wd = β6 * bw + cw)
    (h3z : z 3 - zd = cz) (h3w : w 3 - wd = cw) : LexUni z w := by
  obtain ⟨M, hM⟩ := exists_key z w hinj
  set key : ZMod 4 → ℝ := fun i => M * z i + w i with hkey
  refine lexUni_of_key z w key hinj hM ?_
  have pB : LP bz bw := Or.inl hbz
  have pU : LP A uw := Or.inl hA
  refine lexUni_four _ key (fun _ _ => rfl) ?_ ?_ ?_
  · intro i j hij hk
    have hne : (z i, w i) ≠ (z j, w j) := fun h => hij (hinj i j (congrArg Prod.fst h) (congrArg Prod.snd h))
    rcases lexLt_total hne with h | h
    · exact absurd hk (ne_of_lt ((hM i j).1 h))
    · exact absurd hk.symm (ne_of_lt ((hM j i).1 h))
  · intro h
    rw [max_lt_iff, lt_min_iff, lt_min_iff] at h
    obtain ⟨⟨h10, h12⟩, h30, h32⟩ := h
    have l10 : LexLt (z 1, w 1) (z 0, w 0) := (hM 1 0).2 h10
    have l30 : LexLt (z 3, w 3) (z 0, w 0) := (hM 3 0).2 h30
    rw [lexLt_iff_LP] at l10 l30
    have hD : 0 < 1 - κ := by linarith
    have he : 0 < -(α1 - 1) * κ := by nlinarith
    have hN : 0 < (α1 - 1) * (σ - κ) + (1 - κ) := by nlinarith
    have S := LP_add (LP_smul hD l10) (LP_add (LP_smul he l30)
      (LP_add (LP_smul (mul_pos hD hβ1) pB) (LP_smul hN pU)))
    apply LP_ne_zero S
    constructor
    · linear_combination ((1 - κ) + -(α1 - 1) * κ) * h0z - (1 - κ) * h1z - (-(α1 - 1) * κ) * h3z
    · linear_combination ((1 - κ) + -(α1 - 1) * κ) * h0w - (1 - κ) * h1w - (-(α1 - 1) * κ) * h3w
  · intro h
    rw [max_lt_iff, lt_min_iff, lt_min_iff] at h
    obtain ⟨⟨h01, h03⟩, h21, h23⟩ := h
    have l23 : LexLt (z 2, w 2) (z 3, w 3) := (hM 2 3).2 h23
    rw [lexLt_iff_LP] at l23
    have := LP_nonneg l23
    nlinarith [mul_pos hβ6 hbz]

end C2
end Type08Sp
end Minimality
