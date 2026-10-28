module

public import Minimality.Type08S.G6p

@[expose] public section

set_option autoImplicit true

/-!
# G6' bridge, part 5: the parametrised frame statement (Theorem 08.T' from normal-form data)

All hypotheses are real-number facts about the normal-form parameters; the foot of the
class-(d) HDN enters through the two equations `eqX`, `eqz` (equal screen position and depth
of the points on `[c', b']` and on the diagonal `[c, b]`).
-/

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

variable {e1 e2 e3 : ℝ³}

set_option maxHeartbeats 1000000 in
theorem param_core (hF : Fr e1 e2 e3) (o : ℝ³)
    {L ν C0 ha w1 w3 α β1 γ4 β6 s t X0 X1 P R : ℝ}
    (hX0 : X0 = L * (1 - γ4) + α * w1) (hX1 : X1 = L + α * w1)
    (hP : P = α * w3 + γ4 * C0) (hR : R = α * w3 + β1 * ν)
    (hL : 0 < L) (hν : 0 < ν) (hha : 0 < ha) (hα : 1 < α) (hβ1 : 0 < β1) (hγ : β1 < γ4)
    (hβ6 : 0 < β6) (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1)
    (eqX : X1 + s * (X0 - X1) = t * L)
    (eqz : R + s * (P - R) = (1 - t) * C0 + t * ν)
    (hR1 : ¬ Sep ν P C0 R) (hR2' : Sep 0 P R C0) (hXba' : Sep ν P R (β6 * ν + C0)) :
    IsRupert ({pt e1 e2 e3 o L 0 0, pt e1 e2 e3 o (L + w1) ha w3,
      pt e1 e2 e3 o 0 0 (β6 * ν + C0), pt e1 e2 e3 o L 0 ν,
      pt e1 e2 e3 o X0 (α * ha) P, pt e1 e2 e3 o 0 0 C0, pt e1 e2 e3 o X1 (α * ha) R} :
      Finset ℝ³) := by
  have hα0 : 0 < α := by linarith
  have hγ0 : 0 < γ4 := by linarith
  have hXX : X1 - X0 = γ4 * L := by rw [hX0, hX1]; ring
  have hX : X0 < X1 := by rw [← sub_pos, hXX]; positivity
  obtain ⟨κ, hκd⟩ : ∃ κ, κ = (R - P) / (X1 - X0) := ⟨_, rfl⟩
  have hκ : κ * (X1 - X0) = R - P := by
    rw [hκd]; exact div_mul_cancel₀ _ (by rw [hXX]; positivity)
  have hRP : R - P = β1 * ν - γ4 * C0 := by rw [hR, hP]; ring
  have hfoot : P + κ * (t * L - X0) = (1 - t) * C0 + t * ν := by
    have e1' : t * L - X0 = (1 - s) * (X1 - X0) := by rw [← eqX]; ring
    rw [e1']
    have : κ * ((1 - s) * (X1 - X0)) = (1 - s) * (R - P) := by rw [← hκ]; ring
    rw [this, ← eqz]; ring
  obtain ⟨q, hq⟩ : ∃ q, q = κ * L := ⟨_, rfl⟩
  have hqγ : q * γ4 = β1 * ν - γ4 * C0 := by
    rw [← hRP, ← hκ, hXX, hq]; ring
  have hq1 : q < ν - C0 := by
    by_contra hcon; push Not at hcon
    nlinarith [mul_le_mul_of_nonneg_right hcon hγ0.le, mul_pos hν (sub_pos.mpr hγ)]
  have hσL : P + κ * (L - X0) < ν := by
    have : P + κ * (L - X0) = (1 - t) * C0 + t * ν + (1 - t) * q := by
      rw [← hfoot, hq]; ring
    rw [this]; nlinarith [mul_pos (sub_pos.mpr ht1) (sub_pos.mpr hq1)]
  have hσ0 : C0 < P + κ * (0 - X0) := by
    have : P + κ * (0 - X0) = (1 - t) * C0 + t * ν - t * q := by
      rw [← hfoot, hq]; ring
    rw [this]; nlinarith [mul_pos ht0 (sub_pos.mpr hq1)]
  have hza : w3 < ν + (1 / α) * (R - ν) := by
    have : ν + (1 / α) * (R - ν) = w3 + (α - 1 + β1) * ν / α := by
      rw [hR]; field_simp; ring
    rw [this]
    have : 0 < (α - 1 + β1) * ν / α := by
      apply div_pos (mul_pos (by linarith) hν) hα0
    linarith
  have hz1 : Btw C0 ν (R + s * (P - R)) := by
    rw [eqz]
    rcases lt_trichotomy C0 ν with h | h | h
    · left
      have m1 := mul_pos ht0 (sub_pos.mpr h)
      have m2 := mul_pos (sub_pos.mpr ht1) (sub_pos.mpr h)
      constructor <;> linarith
    · right; right; subst h; constructor <;> first | rfl | ring
    · right; left
      have m1 := mul_pos ht0 (sub_pos.mpr h)
      have m2 := mul_pos (sub_pos.mpr ht1) (sub_pos.mpr h)
      constructor <;> linarith
  have hz2 : Btw P R (R + s * (P - R)) := by
    rcases lt_trichotomy P R with h | h | h
    · left
      have m1 := mul_pos hs0 (sub_pos.mpr h)
      have m2 := mul_pos (sub_pos.mpr hs1) (sub_pos.mpr h)
      constructor <;> linarith
    · right; right; rw [h]; constructor <;> first | rfl | ring
    · right; left
      have m1 := mul_pos hs0 (sub_pos.mpr h)
      have m2 := mul_pos (sub_pos.mpr hs1) (sub_pos.mpr h)
      constructor <;> linarith
  have key := thm08Tp_frame (L := L) (h := α * ha) (X0 := X0) (X1 := X1) (C := C0) (W := 0)
    (B := ν) (A := β6 * ν + C0) (P := P) (R := R) (t := 1 / α) (za := w3) (κ := κ)
    (zs := R + s * (P - R)) hF o hL
    (by positivity) hX hν (by have := mul_pos hβ6 hν; linarith) (by positivity) (by rw [div_lt_one hα0]; exact hα) hza
    hR1 hR2' hXba' hz1 hz2 hκ hσL hσ0
  have ea : L + 1 / α * (X1 - L) = L + w1 := by rw [hX1]; field_simp; ring
  have eb : 1 / α * (α * ha) = ha := by field_simp
  rw [ea, eb] at key
  exact key

end Type08Sp
end Minimality
