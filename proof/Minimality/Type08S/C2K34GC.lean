module

public import Minimality.Type08S.C2K34GA

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace
namespace Minimality
namespace Type08Sp
namespace C2

theorem k32g_hE_real {α1 β1 γ6 pp s qq qr rr m1 m3 : ℝ} (hα1 : 1 < α1) (hβ1 : 1 < β1) (hγ6 : 0 < γ6)
    (hm1 : m1 = α1 * pp + (β1 - 1 - γ6) * s) (hm3 : m3 = α1 * s + (β1 - 1) * qr - γ6 * rr)
    (hm3n : m3 < 0) (hLp : α1 * m1 + (β1 - 1) * m3 = 0)
    (hLz : m3 * (α1 * pp + (β1 - 1) * s) - m1 * (α1 * s + β1 * qr - rr) = 0)
    (hr1 : α1 * s * (qq + rr - 2 * qr) = -(β1 - 1) * (qq * rr - qr ^ 2))
    (hu : qr < qq) (hv : qr < rr) (hD : 0 < qq * rr - qr ^ 2) :
    0 < (1 - γ6) * m3 - (α1 * s + (β1 - 1) * qq - γ6 * qr) := by
  have h1 : m3 * (α1 * (α1 * pp + (β1 - 1) * s) + (β1 - 1) * (α1 * s + β1 * qr - rr)) = 0 := by
    linear_combination α1 * hLz + (α1 * s + β1 * qr - rr) * hLp
  have E1 : α1 * (α1 * pp + (β1 - 1) * s) + (β1 - 1) * (α1 * s + β1 * qr - rr) = 0 := by
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd h hm3n.ne
    · exact h
  have W : α1 * γ6 * s + (β1 - 1) * qr + (β1 - 1) * (γ6 - 1) * rr = 0 := by
    rw [hm1, hm3] at hLp
    linear_combination E1 - hLp
  have hV : (β1 - 1) * ((rr - qr) * (γ6 * (rr - qr) - (qq + rr - 2 * qr))) = 0 := by
    linear_combination (qq + rr - 2 * qr) * W - γ6 * hr1
  have V : γ6 * (rr - qr) = qq + rr - 2 * qr := by
    rcases mul_eq_zero.1 hV with h | h
    · exact absurd h (by linarith)
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h (by linarith)
      · linarith
  have key : (1 - γ6) * m3 - (α1 * s + (β1 - 1) * qq - γ6 * qr) = γ6 * (γ6 * qr + (qq - qr)) := by
    rw [hm3]
    nlinarith [W, V]
  rw [key]
  have hpos : 0 < γ6 * qr + (qq - qr) := by
    have : (γ6 * qr + (qq - qr)) * (rr - qr) = qq * rr - qr ^ 2 := by
      nlinarith [V]
    by_contra hn; push_neg at hn
    nlinarith [mul_nonneg (neg_nonneg.2 hn) (sub_pos.2 hv).le]
  exact mul_pos hγ6 hpos

end C2
end Type08Sp
end Minimality
