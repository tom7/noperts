module

public import Minimality.Type08S.C2K25Tie

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false

namespace Minimality
namespace Type08Sp
namespace C2

/-- Gram expansions in the basis `(p,q,r)` with `⟪p,q⟫ = ⟪p,r⟫ = s`; `A = c'-a`, `B = b'-a`, `C = c-a'`. -/
def k28bqAA (α1 β1 pp s qq : ℝ) : ℝ := (α1 - 1) ^ 2 * pp + 2 * (α1 - 1) * β1 * s + β1 ^ 2 * qq
def k28bqAB (α1 β1 pp s qr : ℝ) : ℝ := (α1 - 1) ^ 2 * pp + 2 * (α1 - 1) * β1 * s + β1 ^ 2 * qr
def k28bqBB (α1 β1 pp s rr : ℝ) : ℝ := (α1 - 1) ^ 2 * pp + 2 * (α1 - 1) * β1 * s + β1 ^ 2 * rr
def k28bqAC (α1 β1 β6 s qq qr : ℝ) : ℝ :=
  (α1 - 1) * (1 - (β1 - β6) - β6) * s + β1 * ((1 - (β1 - β6)) * qr - β6 * qq)
def k28bqBC (α1 β1 β6 s qr rr : ℝ) : ℝ :=
  (α1 - 1) * (1 - (β1 - β6) - β6) * s + β1 * ((1 - (β1 - β6)) * rr - β6 * qr)

theorem k28bq_aux {E F c b6 b1 : ℝ} (hc : 0 < c) (hb6 : 0 < b6) (hF : F < 0) (ht : c * E = b6 * F)
    (hk : 0 < b6 - b1 * c) : E < 0 ∧ E < b1 * F := by
  have h1 : c * E < 0 := by rw [ht]; exact mul_neg_of_pos_of_neg hb6 hF
  have h2 : c * (E - b1 * F) < 0 := by
    have : c * (E - b1 * F) = (b6 - b1 * c) * F := by linear_combination ht
    rw [this]; exact mul_neg_of_pos_of_neg hk hF
  exact ⟨by by_contra hh; push Not at hh; nlinarith [mul_nonneg hc.le hh],
    by by_contra hh; push Not at hh; nlinarith [mul_nonneg hc.le (sub_nonneg.2 hh)]⟩

theorem k28bq_kpos {α1 β1 β6 pp s qr rr : ℝ} (hpp : 0 < pp)
    (hL : (α1 - 1) * pp + β1 * s = 0) (hβ1 : 0 < β1)
    (hΛ : (β1 - 1) * (pp * qr - s ^ 2) + ((β1 - β6) - 1) * (rr - qr) * pp < 0) :
    0 < k28bqBC α1 β1 β6 s qr rr := by
  unfold k28bqBC
  have e : pp * ((α1 - 1) * (1 - (β1 - β6) - β6) * s + β1 * ((1 - (β1 - β6)) * rr - β6 * qr))
      = -β1 * ((β1 - 1) * (pp * qr - s ^ 2) + ((β1 - β6) - 1) * (rr - qr) * pp) := by
    linear_combination (1 - β1) * s * hL
  have : 0 < pp * ((α1 - 1) * (1 - (β1 - β6) - β6) * s + β1 * ((1 - (β1 - β6)) * rr - β6 * qr)) := by
    rw [e]; nlinarith
  exact (pos_iff_pos_of_mul_pos this).1 hpp

set_option maxHeartbeats 1600000 in
theorem k28bq_real {α1 β1 β6 pp s qq qr rr t : ℝ} (hα : 1 < α1) (hβ1 : 1 < β1) (hb6 : 0 < β6)
    (hg6 : 0 < β1 - β6) (hg1 : β1 - β6 < 1) (hpp : 0 < pp) (hs : s < 0)
    (hL : (α1 - 1) * pp + β1 * s = 0) (hqq : qr < qq) (hrr : qr < rr) (hD : 0 < qq * rr - qr ^ 2) (hM0 : 0 ≤ pp * qr - s ^ 2)
    (hRel : α1 * s * (qq + rr - 2 * qr) = -(β1 - 1) * (qq * rr - qr ^ 2))
    (hΛ : (β1 - 1) * (pp * qr - s ^ 2) + ((β1 - β6) - 1) * (rr - qr) * pp < 0)
    (ht : t * k28bqBC α1 β1 β6 s qr rr = k28bqAC α1 β1 β6 s qq qr) :
    0 < k28bqBC α1 β1 β6 s qr rr ∧ t < 0 ∧
    (t * k28bqAB α1 β1 pp s qr - k28bqAA α1 β1 pp s qq) < 0 ∧
    (1 - (β1 - β6)) * (t * k28bqBB α1 β1 pp s rr - k28bqAB α1 β1 pp s qr)
      = β6 * (t * k28bqAB α1 β1 pp s qr - k28bqAA α1 β1 pp s qq) ∧
    (t * k28bqBB α1 β1 pp s rr - k28bqAB α1 β1 pp s qr) < 0 ∧
    (t * k28bqBB α1 β1 pp s rr - k28bqAB α1 β1 pp s qr) <
      β1 * (t * k28bqAB α1 β1 pp s qr - k28bqAA α1 β1 pp s qq) := by
  have ha : 0 < α1 - 1 := by linarith
  have hb : 0 < β1 - 1 := by linarith
  have hc : 0 < 1 - (β1 - β6) := by linarith
  have hW : 0 < qq + rr - 2 * qr := by linarith
  unfold k28bqAA k28bqAB k28bqBB k28bqAC k28bqBC at *
  -- κA > 0
  have hκ : 0 < (α1 - 1) * (1 - (β1 - β6) - β6) * s + β1 * ((1 - (β1 - β6)) * rr - β6 * qr) := by
    have e : pp * ((α1 - 1) * (1 - (β1 - β6) - β6) * s + β1 * ((1 - (β1 - β6)) * rr - β6 * qr))
        = -β1 * ((β1 - 1) * (pp * qr - s ^ 2) + ((β1 - β6) - 1) * (rr - qr) * pp) := by
      linear_combination (1 - β1) * s * hL
    have : 0 < pp * ((α1 - 1) * (1 - (β1 - β6) - β6) * s + β1 * ((1 - (β1 - β6)) * rr - β6 * qr)) := by
      rw [e]; nlinarith
    exact (pos_iff_pos_of_mul_pos this).1 hpp
  -- N < 0
  have hN : ((α1 - 1) * (1 - (β1 - β6) - β6) * s + β1 * ((1 - (β1 - β6)) * qr - β6 * qq)) *
      ((α1 - 1) ^ 2 * pp + 2 * (α1 - 1) * β1 * s + β1 ^ 2 * qr) -
      ((α1 - 1) * (1 - (β1 - β6) - β6) * s + β1 * ((1 - (β1 - β6)) * rr - β6 * qr)) *
      ((α1 - 1) ^ 2 * pp + 2 * (α1 - 1) * β1 * s + β1 ^ 2 * qq) < 0 := by
    have e : ((α1 - 1) * (1 - (β1 - β6) - β6) * s + β1 * ((1 - (β1 - β6)) * qr - β6 * qq)) *
      ((α1 - 1) ^ 2 * pp + 2 * (α1 - 1) * β1 * s + β1 ^ 2 * qr) -
      ((α1 - 1) * (1 - (β1 - β6) - β6) * s + β1 * ((1 - (β1 - β6)) * rr - β6 * qr)) *
      ((α1 - 1) ^ 2 * pp + 2 * (α1 - 1) * β1 * s + β1 ^ 2 * qq)
      = -β1 ^ 2 * (1 - (β1 - β6)) * ((α1 - 1) * s * (qq + rr - 2 * qr) + β1 * (qq * rr - qr ^ 2)) := by
      linear_combination ((α1 - 1) * (β1 * ((1 - (β1 - β6)) * (qr - rr) - β6 * (qq - qr)))) * hL
    rw [e]
    have hX : 0 < (α1 - 1) * s * (qq + rr - 2 * qr) + β1 * (qq * rr - qr ^ 2) := by
      have e2 : α1 * ((α1 - 1) * s * (qq + rr - 2 * qr) + β1 * (qq * rr - qr ^ 2))
          = (α1 + β1 - 1) * (qq * rr - qr ^ 2) := by
        linear_combination (α1 - 1) * hRel
      have : 0 < α1 * ((α1 - 1) * s * (qq + rr - 2 * qr) + β1 * (qq * rr - qr ^ 2)) := by
        rw [e2]; exact mul_pos (by linarith) hD
      exact (pos_iff_pos_of_mul_pos this).1 (by linarith)
    have : 0 < β1 ^ 2 * (1 - (β1 - β6)) * ((α1 - 1) * s * (qq + rr - 2 * qr) + β1 * (qq * rr - qr ^ 2)) :=
      mul_pos (mul_pos (by positivity) hc) hX
    linarith
  -- combine
  have hBC := hκ
  have hf : t * ((α1 - 1) ^ 2 * pp + 2 * (α1 - 1) * β1 * s + β1 ^ 2 * qr) -
      ((α1 - 1) ^ 2 * pp + 2 * (α1 - 1) * β1 * s + β1 ^ 2 * qq) < 0 := by
    have e3 : ((α1 - 1) * (1 - (β1 - β6) - β6) * s + β1 * ((1 - (β1 - β6)) * rr - β6 * qr)) *
        (t * ((α1 - 1) ^ 2 * pp + 2 * (α1 - 1) * β1 * s + β1 ^ 2 * qr) -
      ((α1 - 1) ^ 2 * pp + 2 * (α1 - 1) * β1 * s + β1 ^ 2 * qq)) =
      ((α1 - 1) * (1 - (β1 - β6) - β6) * s + β1 * ((1 - (β1 - β6)) * qr - β6 * qq)) *
      ((α1 - 1) ^ 2 * pp + 2 * (α1 - 1) * β1 * s + β1 ^ 2 * qr) -
      ((α1 - 1) * (1 - (β1 - β6) - β6) * s + β1 * ((1 - (β1 - β6)) * rr - β6 * qr)) *
      ((α1 - 1) ^ 2 * pp + 2 * (α1 - 1) * β1 * s + β1 ^ 2 * qq) := by
      linear_combination ((α1 - 1) ^ 2 * pp + 2 * (α1 - 1) * β1 * s + β1 ^ 2 * qr) * ht
    have : ((α1 - 1) * (1 - (β1 - β6) - β6) * s + β1 * ((1 - (β1 - β6)) * rr - β6 * qr)) *
        (t * ((α1 - 1) ^ 2 * pp + 2 * (α1 - 1) * β1 * s + β1 ^ 2 * qr) -
      ((α1 - 1) ^ 2 * pp + 2 * (α1 - 1) * β1 * s + β1 ^ 2 * qq)) < 0 := by rw [e3]; exact hN
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg hBC.le hh]
  have htie : (1 - (β1 - β6)) * (t * ((α1 - 1) ^ 2 * pp + 2 * (α1 - 1) * β1 * s + β1 ^ 2 * rr) -
      ((α1 - 1) ^ 2 * pp + 2 * (α1 - 1) * β1 * s + β1 ^ 2 * qr))
      = β6 * (t * ((α1 - 1) ^ 2 * pp + 2 * (α1 - 1) * β1 * s + β1 ^ 2 * qr) -
      ((α1 - 1) ^ 2 * pp + 2 * (α1 - 1) * β1 * s + β1 ^ 2 * qq)) := by
    linear_combination β1 * ht + (t - 1) * (1 - β1) * (α1 - 1) * hL
  have htn : t < 0 := by
    have hAC : ((α1 - 1) * (1 - (β1 - β6) - β6) * s + β1 * ((1 - (β1 - β6)) * qr - β6 * qq)) < 0 := by
      have e : pp * ((α1 - 1) * (1 - (β1 - β6) - β6) * s + β1 * ((1 - (β1 - β6)) * qr - β6 * qq))
          = -β1 * ((β1 - 1) * (pp * qr - s ^ 2) + β6 * pp * (qq - qr)) := by
        linear_combination (1 - β1) * s * hL
      have h1 : 0 < pp * (-((α1 - 1) * (1 - (β1 - β6) - β6) * s + β1 * ((1 - (β1 - β6)) * qr - β6 * qq))) := by
        have : 0 < β1 * ((β1 - 1) * (pp * qr - s ^ 2) + β6 * pp * (qq - qr)) := by
          apply mul_pos (by linarith)
          exact add_pos_of_nonneg_of_pos (mul_nonneg hb.le hM0)
            (mul_pos (mul_pos hb6 hpp) (sub_pos.2 hqq))
        rw [mul_neg, e]; linarith
      have := (pos_iff_pos_of_mul_pos h1).1 hpp
      linarith
    by_contra hh; push Not at hh
    have := mul_nonneg hh hκ.le
    linarith [ht]
  have hk : 0 < β6 - β1 * (1 - (β1 - β6)) := by
    have e : β6 - β1 * (1 - (β1 - β6)) = (β1 - 1) * (β1 - β6) := by ring
    rw [e]; exact mul_pos hb hg6
  refine ⟨hκ, htn, hf, htie, ?_, ?_⟩
  · exact (k28bq_aux hc hb6 hf htie hk).1
  · exact (k28bq_aux hc hb6 hf htie hk).2

end C2
end Type08Sp
end Minimality
