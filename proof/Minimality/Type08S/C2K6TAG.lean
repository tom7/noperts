module

public import Minimality.Type08S.C2K6TAF

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


/-- **QTc `α4 > 1`, cell 1: the pentagon `(a, c', a', c, d)`** (indices `0..4`), `ζ(d,b) > 0` (`bz < 0`). -/
theorem k6t1_pent1_lexUni (z w : ZMod 5 → ℝ) (hinj : ∀ i j, z i = z j → w i = w j → i = j)
    {κ σ α1 β1 β6 bz bw cz cw A uw : ℝ} (hnB : LP (-bz) (-bw)) (hA : 0 < A) (hκ : κ < 0) (hσ : σ < 0)
    (hα1 : 1 ≤ α1) (hβ1 : 0 < β1) (hβ6 : 0 < β6)
    (h0z : z 0 - z 4 = κ * cz + σ * A) (h0w : w 0 - w 4 = κ * cw + σ * uw)
    (h1z : z 1 - z 4 = β1 * bz + α1 * (κ * cz + σ * A))
    (h1w : w 1 - w 4 = β1 * bw + α1 * (κ * cw + σ * uw))
    (h2z : z 2 - z 4 = β6 * bz + cz) (h2w : w 2 - w 4 = β6 * bw + cw)
    (h3z : z 3 - z 4 = cz) (h3w : w 3 - w 4 = cw) : LexUni z w := by
  have nB := hnB
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

end C2
end Type08Sp
end Minimality
