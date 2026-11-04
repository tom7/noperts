module

public import Minimality.Type08S.L2.K92A

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option maxHeartbeats 3200000
namespace Minimality.Type08Sp.C2

theorem k92_scale (s P Q R T : ℝ) (x1 x2 x3 y1 y2 y3 : ℝ) :
    k91G (s*P) (-s) (s*Q) (s*R) (s*T) x1 x2 x3 y1 y2 y3 = s * k91G P (-1) Q R T x1 x2 x3 y1 y2 y3 := by
  unfold k91G; ring

theorem k92_lin (u v x y x1 x2 x3 y1 y2 y3 : ℝ) :
    k92G u v x y x1 x2 x3 y1 y2 y3 = y1 * k92G u v x y x1 x2 x3 1 0 0 + y2 * k92G u v x y x1 x2 x3 0 1 0 + y3 * k92G u v x y x1 x2 x3 0 0 1 := by
  unfold k92G k91G; ring

theorem k92_chart {pp s qq qr rr al be : ℝ} (hs : 0 < s) (hal : 1 < al) (hbe : 1 < be)
    (hqx : qr < qq) (hqy : qr < rr)
    (hrel : al*s*(qq+rr-2*qr) = (be-1)*(qq*rr-qr^2))
    (hppE : pp*((al-1)*rr+be*qr) = s*((al+be-1)*s+be*(rr-qr)))
    (hW : 0 < (al-1)*rr+be*qr) :
    ∃ u v x y : ℝ, u = al-1 ∧ v = be-1 ∧ 0 < x ∧ 0 < y ∧ qr = s*k92qr u v x y ∧ qq = s*(k92qr u v x y + x) ∧
      rr = s*(k92qr u v x y + y) ∧ pp = s*k92pp u v x y ∧ 0 < k92Wn u v x y := by
  obtain ⟨u, rfl⟩ : ∃ u, al = u + 1 := ⟨al - 1, by ring⟩
  obtain ⟨v, rfl⟩ : ∃ v, be = v + 1 := ⟨be - 1, by ring⟩
  have hu : 0 < u := by linarith
  have hv : 0 < v := by linarith
  obtain ⟨x, hxd⟩ : ∃ x, qq = qr + s*x := ⟨(qq-qr)/s, by field_simp; ring⟩
  obtain ⟨y, hyd⟩ : ∃ y, rr = qr + s*y := ⟨(rr-qr)/s, by field_simp; ring⟩
  have hx : 0 < x := by
    have : 0 < s*x := by linarith
    exact pos_of_mul_pos_right this hs.le
  have hy : 0 < y := by
    have : 0 < s*y := by linarith
    exact pos_of_mul_pos_right this hs.le
  have hxy : 0 < x + y := by linarith
  subst hxd hyd
  have h1 : s * ((u+1)*s*(x+y) - v*(qr*(x+y)+s*x*y)) = 0 := by linear_combination hrel
  have h2 : (u+1)*s*(x+y) - v*(qr*(x+y)+s*x*y) = 0 := (mul_eq_zero.1 h1).resolve_left hs.ne'
  have hqr : qr = s*k92qr u v x y := by
    unfold k92qr; field_simp; linear_combination (-1) * h2
  have hWq : u*(qr + s*y) + (v+1)*qr = s*(k92Wn u v x y/(v*(x+y))) := by
    rw [hqr]; unfold k92qr k92Wn; field_simp; ring
  have hWn : 0 < k92Wn u v x y := by
    have : 0 < s*(k92Wn u v x y/(v*(x+y))) := by
      have := hW; simp only [add_sub_cancel_right] at this; linarith
    have h3 := pos_of_mul_pos_right this hs.le
    exact (div_pos_iff_of_pos_right (by positivity)).1 h3
  refine ⟨u, v, x, y, by ring, by ring, hx, hy, hqr, by rw [hqr]; ring, by rw [hqr]; ring, ?_, hWn⟩
  have h4 : pp * (s*(k92Wn u v x y/(v*(x+y)))) = s*((u+1+(v+1)-1)*s+(v+1)*(qr + s*y - qr)) := by
    have := hppE; rw [show u + 1 - 1 = u by ring] at this; rw [← hWq]; exact this
  unfold k92pp
  have hW0 : k92Wn u v x y ≠ 0 := hWn.ne'
  field_simp
  field_simp at h4
  nlinarith [h4]
end Minimality.Type08Sp.C2
