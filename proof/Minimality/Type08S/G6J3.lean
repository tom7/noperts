module

public import Minimality.Type08S.G6J2
public import Minimality.Type08S.G6O

@[expose] public section

set_option autoImplicit true

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

set_option maxHeartbeats 4000000 in
theorem allsep4_real {n q B C α1 α4 β1 γ4 β6 : ℝ} (hn : 0 < n) (hα : 1 < α1) (h4 : 0 < α4)
    (hγ : 0 < γ4) (hb1 : 0 < β1) (hb6 : 0 < β6) (hE : 0 < α4 - α4 * β1 - α1 * (1 - γ4))
    (ec : α4 * C - α1 * B = α4 * β1 * n - α1 * γ4 * q)
    (s1 : Sep n B q C) (s2 : Sep 0 B q C) (s3 : Sep n B (β6 * n + q) C)
    (s4 : Sep 0 B (β6 * n + q) C) : False := by
  have p1 : 0 < β6 * n := mul_pos hb6 hn
  have p2 : 0 < α4 * β1 := mul_pos h4 hb1
  have hα0 : 0 < α1 := by linarith
  have p3 : 0 < α1 * γ4 := mul_pos hα0 hγ
  unfold Sep at s1 s2 s3 s4
  simp only [max_le_iff, le_min_iff] at s1 s2 s3 s4
  rcases s1 with ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ | ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ <;>
  rcases s2 with ⟨⟨b1, b2⟩, ⟨b3, b4⟩⟩ | ⟨⟨b1, b2⟩, ⟨b3, b4⟩⟩ <;>
  rcases s3 with ⟨⟨c1, c2⟩, ⟨c3, c4⟩⟩ | ⟨⟨c1, c2⟩, ⟨c3, c4⟩⟩ <;>
  rcases s4 with ⟨⟨d1, d2⟩, ⟨d3, d4⟩⟩ | ⟨⟨d1, d2⟩, ⟨d3, d4⟩⟩ <;>
  try linarith
  · -- all of q, a', C below 0 and below B
    have hq : q < 0 := by nlinarith
    rcases le_total α4 α1 with h | h
    · nlinarith [mul_nonneg h4.le (sub_nonneg.2 d4), mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 d3),
        mul_pos hE (neg_pos.2 hq)]
    · have hB : 0 < B := by
        by_contra hB; push_neg at hB
        nlinarith [mul_nonneg h4.le (sub_nonneg.2 d4), mul_nonneg (sub_nonneg.2 h) (neg_nonneg.2 hB),
          mul_pos p3 (neg_pos.2 hq)]
      nlinarith [mul_nonneg h4.le (neg_nonneg.2 d2), mul_pos hα0 hB, mul_pos p3 (neg_pos.2 hq)]
  · have hB : B = β6 * n + q := by linarith
    have hC : C = 0 := by linarith
    subst hC
    have hq : q = -(β6 * n) := by linarith
    subst hq
    nlinarith [mul_pos p3 p1]
  · have hB : B = q := by linarith
    have hC : C = q := by linarith
    have hqn : q = n := by linarith
    subst hB hC hqn
    nlinarith
  · rcases le_total α4 α1 with h | h
    · nlinarith [mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 a1), mul_nonneg h4.le (sub_nonneg.2 a2),
        mul_pos hE hn, mul_nonneg hE.le (sub_nonneg.2 a1)]
    · nlinarith [mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 a3), mul_nonneg p3.le (sub_nonneg.2 a1),
        mul_nonneg h4.le (sub_nonneg.2 a4)]

end Type08Sp
end Minimality
