module

public import Minimality.Type08S.L2.K92B

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
namespace Minimality.Type08Sp.C2

set_option maxHeartbeats 12800000 in
/-- fQT: Q1 at the tie PB = 0 (also for PB > 0). -/
theorem k95_fQT (u v m x y : ℝ) (hu : 0 < u) (hv : 0 < v) (hm : 0 < m) (hx : 0 < x) (hy : 0 < y)
    (hWn : 0 < k92Wn u v x y) (hl : 0 ≤ k92l u v x y) (hlK : 0 ≤ k92l u v x y * k92K u v x y)
    (hB : 0 ≤ -u*k92Ac u v m x y - (v+1)*k92Bc u v m x y) :
    0 < k92G u v x y (u+1) (-((v+1)*m)) (v+1-(1+u*m)) 0 0 1 := by
  have hxy : 0 < x + y := by positivity
  have hW0 : k92Wn u v x y ≠ 0 := hWn.ne'
  have hPm : 0 < k92Pm u v m x y := by
    unfold k92Pm; have : 0 < v*y*(v*x+x+y) := by positivity
    nlinarith [mul_pos hm hWn]
  have hP0 := hPm.ne'
  have hWN' : 0 < u^2*x + u^2*y + u*v*x + u*v*y^2 + u*v*y + 2*u*x + 2*u*y - v^2*x*y - v*x*y + v*x + v*y + x + y := hWn
  have hl2 : 0 ≤ -u*y + x*(v + 1) := by unfold k92l at hl; linarith
  have hlK2 : 0 ≤ (-u*y + x*(v + 1))*(v^2*x*y + v*x*y - (x + y)*(u + v + 1)) := by
    unfold k92l k92K at hlK; nlinarith [hlK]
  have hTB : 0 < k92TB u v x y := k92_c_TB u v x y hu hv hx hy hWN' hl2 hlK2
  rw [k92_PB u v m x y hv hx hy hW0 hP0] at hB
  rw [k92_Q1 u v m x y hv hx hy hW0 hP0]
  have hd : 0 < v*(x+y)*k92Wn u v x y := by positivity
  have hN : 0 ≤ v^2*y*k92l u v x y*k92K u v x y - k92Wn u v x y*k92TB u v x y*m :=
    (div_nonneg_iff.1 hB).elim (fun h => h.1) (fun h => absurd h.2 (not_le.2 hd))
  have hid : k92TB u v x y * (v^2*y^2 - m*k92Wn u v x y) = (v^2*y*k92l u v x y*k92K u v x y - k92Wn u v x y*k92TB u v x y*m) + v^2*y*(v+1)*(x+y)^2*(u+v+1) := by
    simp only [k92Wn, k92K, k92l, k92TB]; ring
  have h1 : 0 < k92TB u v x y * (v^2*y^2 - m*k92Wn u v x y) := by
    rw [hid]; have : 0 < v^2*y*(v+1)*(x+y)^2*(u+v+1) := by positivity
    linarith
  have h2 := pos_of_mul_pos_right h1 hTB.le
  exact div_pos h2 (by positivity)

set_option maxHeartbeats 12800000 in
/-- fQ2T: <a'-b, c-d> > 0 whenever m l = y (zab = 0 with K != 0). -/
theorem k95_fQ2T (u v m x y : ℝ) (hu : 0 < u) (hv : 0 < v) (hm : 0 < m) (hx : 0 < x) (hy : 0 < y)
    (hWn : 0 < k92Wn u v x y) (hl : 0 ≤ k92l u v x y) (hml : m * k92l u v x y = y) :
    0 < k92G u v x y 0 ((v+1)*m-1) (1+u*m) 0 0 1 := by
  have hxy : 0 < x + y := by positivity
  have hl0 : k92l u v x y ≠ 0 := by
    intro h; rw [h] at hml; linarith
  have hlp : 0 < k92l u v x y := lt_of_le_of_ne hl (Ne.symm hl0)
  have hmy : m = y / k92l u v x y := by field_simp; linarith
  have hN : 0 < u^2*x + u^2*y - u*v*x*y + u*v*x + u*v*y + 2*u*x + 2*u*y + v^2*x^2 + v*x^2 + v*x + v*y + x + y := by
    have : u*v*x*y ≤ v*(1+v)*x^2 := by
      unfold k92l at hlp; nlinarith [mul_pos hv hx]
    nlinarith [mul_pos hu hx, mul_pos hu hy, mul_pos hv hx, mul_pos hv hy, mul_pos hu hu, mul_pos hx hx, mul_pos hu hv,
      mul_pos (mul_pos hu hu) hx, mul_pos (mul_pos hu hu) hy, mul_pos (mul_pos hu hv) hx, mul_pos (mul_pos hu hv) hy,
      mul_pos (mul_pos hv hx) hx]
  have e : k92G u v x y 0 ((v+1)*m-1) (1+u*m) 0 0 1 =
      y * (u^2*x + u^2*y - u*v*x*y + u*v*x + u*v*y + 2*u*x + 2*u*y + v^2*x^2 + v*x^2 + v*x + v*y + x + y) / (v*(x+y)*k92l u v x y) := by
    rw [hmy]
    simp only [k92G, k91G, k92pp, k92qr]
    have hW0 : k92Wn u v x y ≠ 0 := hWn.ne'
    have hv' : v ≠ 0 := hv.ne'
    field_simp
    simp only [k92Wn, k92l]
    ring
  rw [e]
  positivity
end Minimality.Type08Sp.C2
