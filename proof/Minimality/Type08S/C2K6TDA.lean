module

public import Minimality.Type08S.C2K6TAM
public import Minimality.Type08S.C2K6TBZ
public import Minimality.Type08S.C2K6TCZ
public import Minimality.Type08S.C2K6HF

@[expose] public section

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

/-- 4-cycle, peak only at `2` (`x1 < x2`, `x3 < x2`, `x0 < x3 ∨ x0 < x1`). -/
theorem k6t4_lexUni4_a (z w : ZMod 4 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h12 : LexLt (z 1, w 1) (z 2, w 2)) (h32 : LexLt (z 3, w 3) (z 2, w 2))
    (h0 : LexLt (z 0, w 0) (z 3, w 3) ∨ LexLt (z 0, w 0) (z 1, w 1)) : LexUni z w := by
  classical
  refine ⟨hinj, ?_⟩
  rw [Finset.card_filter]
  have hs : ∀ g : ZMod 4 → ℕ, ∑ i, g i = g 0 + g 1 + g 2 + g 3 := fun g => Fin.sum_univ_four (f := g)
  rw [hs]
  have e0 : (0 : ZMod 4) - 1 = 3 := by decide
  have e1 : (1 : ZMod 4) - 1 = 0 := by decide
  have e2 : (2 : ZMod 4) - 1 = 1 := by decide
  have e3 : (3 : ZMod 4) - 1 = 2 := by decide
  obtain ⟨f0, f1, f2, f3⟩ := z4_add
  show (if LexLt (z (0 - 1), w (0 - 1)) (z 0, w 0) ∧ LexLt (z (0 + 1), w (0 + 1)) (z 0, w 0) then 1 else 0) +
    (if LexLt (z (1 - 1), w (1 - 1)) (z 1, w 1) ∧ LexLt (z (1 + 1), w (1 + 1)) (z 1, w 1) then 1 else 0) +
    (if LexLt (z (2 - 1), w (2 - 1)) (z 2, w 2) ∧ LexLt (z (2 + 1), w (2 + 1)) (z 2, w 2) then 1 else 0) +
    (if LexLt (z (3 - 1), w (3 - 1)) (z 3, w 3) ∧ LexLt (z (3 + 1), w (3 + 1)) (z 3, w 3) then 1 else 0) = 1
  rw [e0, e1, e2, e3, f0, f1, f2, f3]
  have a12 := lexLt_asymm h12
  have a32 := lexLt_asymm h32
  rcases h0 with h0 | h0 <;> have a0 := lexLt_asymm h0 <;> simp [h12, a12, h32, a32, h0, a0]

/-- 4-cycle, peak only at `3` (`x1 < x2`, `x2 < x3`, `x0 < x3`). -/
theorem k6t4_lexUni4_b (z w : ZMod 4 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    (h12 : LexLt (z 1, w 1) (z 2, w 2)) (h23 : LexLt (z 2, w 2) (z 3, w 3))
    (h03 : LexLt (z 0, w 0) (z 3, w 3)) : LexUni z w := by
  classical
  refine ⟨hinj, ?_⟩
  rw [Finset.card_filter]
  have hs : ∀ g : ZMod 4 → ℕ, ∑ i, g i = g 0 + g 1 + g 2 + g 3 := fun g => Fin.sum_univ_four (f := g)
  rw [hs]
  have e0 : (0 : ZMod 4) - 1 = 3 := by decide
  have e1 : (1 : ZMod 4) - 1 = 0 := by decide
  have e2 : (2 : ZMod 4) - 1 = 1 := by decide
  have e3 : (3 : ZMod 4) - 1 = 2 := by decide
  obtain ⟨f0, f1, f2, f3⟩ := z4_add
  show (if LexLt (z (0 - 1), w (0 - 1)) (z 0, w 0) ∧ LexLt (z (0 + 1), w (0 + 1)) (z 0, w 0) then 1 else 0) +
    (if LexLt (z (1 - 1), w (1 - 1)) (z 1, w 1) ∧ LexLt (z (1 + 1), w (1 + 1)) (z 1, w 1) then 1 else 0) +
    (if LexLt (z (2 - 1), w (2 - 1)) (z 2, w 2) ∧ LexLt (z (2 + 1), w (2 + 1)) (z 2, w 2) then 1 else 0) +
    (if LexLt (z (3 - 1), w (3 - 1)) (z 3, w 3) ∧ LexLt (z (3 + 1), w (3 + 1)) (z 3, w 3) then 1 else 0) = 1
  rw [e0, e1, e2, e3, f0, f1, f2, f3]
  have a12 := lexLt_asymm h12
  have a23 := lexLt_asymm h23
  have a03 := lexLt_asymm h03
  simp [h12, a12, h23, a23, h03, a03]

/-- **Pentagon `(a, c', a', c, d)` at the depth tie `bz = 0`, `ζ(c',c) > 0`, `Z := κ cz + σ A ≠ 0`**
(`bz = 0` plugged in; no sign condition on `bw`). -/
theorem k6t4_pent1_lexUni (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    {κ σ α1 β1 β6 bz bw cz cw A uw : ℝ} (hbz : bz = 0) (hA : 0 < A) (hκ : κ < 0) (hσ : σ < 0)
    (hα1 : 1 < α1) (hβ1 : 0 < β1) (hβ6 : 0 < β6)
    (hZ : κ * cz + σ * A ≠ 0) (hζ : cz < α1 * (κ * cz + σ * A))
    (h0z : z 0 - z 4 = κ * cz + σ * A) (h0w : w 0 - w 4 = κ * cw + σ * uw)
    (h1z' : z 1 - z 4 = β1 * bz + α1 * (κ * cz + σ * A))
    (h1w : w 1 - w 4 = β1 * bw + α1 * (κ * cw + σ * uw))
    (h2z' : z 2 - z 4 = β6 * bz + cz) (h2w : w 2 - w 4 = β6 * bw + cw)
    (h3z : z 3 - z 4 = cz) (h3w : w 3 - w 4 = cw) : LexUni z w := by
  have h1z : z 1 - z 4 = α1 * (κ * cz + σ * A) := by rw [h1z', hbz]; ring
  have h2z : z 2 - z 4 = cz := by rw [h2z', hbz]; ring
  have l_a'c' : LexLt (z 2, w 2) (z 1, w 1) := Or.inl (by simp only; linarith)
  rcases lexLt_total (show (z 0, w 0) ≠ (z 4, w 4) from fun h =>
      absurd (hinj 0 4 (congrArg Prod.fst h) (congrArg Prod.snd h)) (by decide)) with l_ad | l_da
  · -- `a < d`
    have hZneg : κ * cz + σ * A < 0 := by
      rcases l_ad with h | ⟨h, -⟩
      · simp only at h; linarith
      · exfalso; apply hZ; simp only at h; linarith
    have hneg : α1 * (κ * cz + σ * A) < 0 := by nlinarith
    have l_cd : LexLt (z 3, w 3) (z 4, w 4) := Or.inl (by simp only; linarith)
    have l_c'a : LexLt (z 1, w 1) (z 0, w 0) := Or.inl (by simp only; nlinarith)
    exact lexUni5_r2 z w hinj l_cd l_c'a (Or.inr l_a'c')
  · -- `d < a`
    have hZpos : 0 < κ * cz + σ * A := by
      rcases l_da with h | ⟨h, -⟩
      · simp only at h; linarith
      · exfalso; apply hZ; simp only at h; linarith
    have hcz : cz < 0 := by nlinarith
    have l_cd : LexLt (z 3, w 3) (z 4, w 4) := Or.inl (by simp only; linarith)
    exact lexUni5_r3 z w hinj l_da l_a'c' (Or.inl l_cd)

/-- **Quadrilateral `(b', c', a', c)` at the depth tie `bz = 0`, `ζ(c',c) < 0`** (no sign condition on `bw`). -/
theorem k6t4_quad2_lexUni (z w : ZMod 4 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j) {zd wd : ℝ}
    {κ σ α1 β1 β6 bz bw cz cw A uw : ℝ} (hbz : bz = 0) (hA : 0 < A) (hκ : κ < 0) (hσ : σ < 0)
    (hα1 : 1 < α1) (hβ1 : 0 < β1) (hβ6 : 0 < β6) (hE : (σ - 1) * (1 - β1) ≤ α1 * (σ - κ))
    (hζ : α1 * (κ * cz + σ * A) < cz)
    (h0z : z 0 - zd = κ * cz + (σ - 1) * A) (h0w : w 0 - wd = κ * cw + (σ - 1) * uw)
    (h1z' : z 1 - zd = β1 * bz + α1 * (κ * cz + σ * A))
    (h1w : w 1 - wd = β1 * bw + α1 * (κ * cw + σ * uw))
    (h2z' : z 2 - zd = β6 * bz + cz) (h2w : w 2 - wd = β6 * bw + cw)
    (h3z : z 3 - zd = cz) (h3w : w 3 - wd = cw) : LexUni z w := by
  have h1z : z 1 - zd = α1 * (κ * cz + σ * A) := by rw [h1z', hbz]; ring
  have h2z : z 2 - zd = cz := by rw [h2z', hbz]; ring
  have l12 : LexLt (z 1, w 1) (z 2, w 2) := Or.inl (by simp only; linarith)
  have l13 : LexLt (z 1, w 1) (z 3, w 3) := Or.inl (by simp only; linarith)
  have hN : 0 < (α1 - 1) * (σ - κ) + (1 - κ) := by nlinarith
  have h0 : LexLt (z 0, w 0) (z 3, w 3) ∨ LexLt (z 0, w 0) (z 1, w 1) := by
    by_cases hh : κ * cz + (σ - 1) * A < cz
    · exact Or.inl (Or.inl (by simp only; linarith))
    · refine Or.inr (Or.inl ?_)
      push Not at hh
      have hG : 0 < (α1 - 1) * (κ * cz + σ * A) + A := by
        by_contra hG
        push Not at hG
        have p1 := mul_nonneg (mul_nonneg (sub_nonneg.2 hα1.le) (neg_nonneg.2 hκ.le)) (sub_nonneg.2 hh)
        have p2 := mul_nonneg (show (0:ℝ) ≤ 1 - κ by linarith) (neg_nonneg.2 hG)
        nlinarith [mul_pos hA hN]
      simp only
      linarith
  have hne : (z 2, w 2) ≠ (z 3, w 3) := fun h =>
    absurd (hinj 2 3 (congrArg Prod.fst h) (congrArg Prod.snd h)) (by decide)
  rcases lexLt_total hne with l23 | l32
  · refine k6t4_lexUni4_b z w hinj l12 l23 ?_
    rcases h0 with h | h
    · exact h
    · exact lexLt_trans_K2 h (lexLt_trans_K2 l12 l23)
  · exact k6t4_lexUni4_a z w hinj l12 l32 h0

end C2
end Type08Sp
end Minimality
