module

public import Minimality.Type08S.C2K35DA

@[expose] public section

set_option maxHeartbeats 1000000

namespace Minimality.Type08Sp.C2

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option maxHeartbeats 0
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
theorem k28h5bd_d2_core (u1 u2 m y al be ob og b g : ℝ) (hu1 : 0 < u1) (hu2 : 0 < u2) (hm : 0 < m) (hy : 0 < y)
    (hal : 0 < al) (hbe : 0 < be) (hob : 0 < ob) (hog : 0 < og) (hb : 0 < b) (hg : 0 < g)
    (eb : b = 1 - ob) (eg : g = 1 - og)
    (hT : 0 ≤ al * (((be*m/((1+al)*(u1+u2)))^2*(u1+u2)+y)/m) - (1+be) * (be*m/((1+al)*(u1+u2)))) :
    0 < k28h5bd_G (((be*m/((1+al)*(u1+u2)))^2*(u1+u2)+y)/m) (be*m/((1+al)*(u1+u2)))
      (u1 + (m-u1*u2)/(u1+u2)) ((m-u1*u2)/(u1+u2)) (u2 + (m-u1*u2)/(u1+u2)) al be 0 (-b) og := by
  have hW : 0 < u1 + u2 := by positivity
  have hA : 0 < 1 + al := by positivity
  have hLam : 0 < m*((1+al)*(u1+u2))^2*(u1+u2)^2 := by positivity
  have hc1 : 0 ≤ k28h5bd_d2c1 u1 u2 al be ob og := by
    have e : (k28h5bd_d2c1 u1 u2 al be ob og) = k28h5bd_hand u1 u2 al be ob og b g := by
      unfold k28h5bd_d2c1 k28h5bd_hand; rw [eb, eg]; ring
    rw [e]; unfold k28h5bd_hand; positivity
  have hT1 : 0 < (k28h5bd_T1 u1 u2 al) := by unfold k28h5bd_T1; positivity
  have hG : 0 < m^2*al*og*(k28h5bd_G2 u1 u2 m al be ob og) := by unfold k28h5bd_G2; positivity
  have hTe : 0 ≤ (m*((1+al)*(u1+u2))^2*(u1+u2)^2) * (al * (((be*m/((1+al)*(u1+u2)))^2*(u1+u2)+y)/m) - (1+be) * (be*m/((1+al)*(u1+u2)))) :=
    mul_nonneg hLam.le hT
  have iden : ((k28h5bd_T1 u1 u2 al)) * ((m*((1+al)*(u1+u2))^2*(u1+u2)^2) * k28h5bd_G (((be*m/((1+al)*(u1+u2)))^2*(u1+u2)+y)/m) (be*m/((1+al)*(u1+u2)))
      (u1 + (m-u1*u2)/(u1+u2)) ((m-u1*u2)/(u1+u2)) (u2 + (m-u1*u2)/(u1+u2)) al be 0 (-b) og)
      = (k28h5bd_d2c1 u1 u2 al be ob og) * ((m*((1+al)*(u1+u2))^2*(u1+u2)^2) * (al * (((be*m/((1+al)*(u1+u2)))^2*(u1+u2)+y)/m) - (1+be) * (be*m/((1+al)*(u1+u2)))))
        + m^2*al*og*(k28h5bd_G2 u1 u2 m al be ob og) := by
    rw [eb]
    unfold k28h5bd_G k28h5bd_ip k28h5bd_d2c1 k28h5bd_T1 k28h5bd_G2
    field_simp
    ring
  have h1 : 0 < ((k28h5bd_T1 u1 u2 al)) * ((m*((1+al)*(u1+u2))^2*(u1+u2)^2) * k28h5bd_G (((be*m/((1+al)*(u1+u2)))^2*(u1+u2)+y)/m) (be*m/((1+al)*(u1+u2)))
      (u1 + (m-u1*u2)/(u1+u2)) ((m-u1*u2)/(u1+u2)) (u2 + (m-u1*u2)/(u1+u2)) al be 0 (-b) og) := by
    rw [iden]; nlinarith [mul_nonneg hc1 hTe]
  have h2 := pos_of_mul_pos_right h1 hT1.le
  exact pos_of_mul_pos_right h2 hLam.le

end Minimality.Type08Sp.C2
