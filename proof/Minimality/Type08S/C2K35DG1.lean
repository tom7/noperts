module

public import Minimality.Type08S.C2K35DA

@[expose] public section

set_option maxHeartbeats 1000000

namespace Minimality.Type08Sp.C2

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

theorem k28h5bd_d1_gram (pp pq qq qr rr al be : ℝ) (hal : 0 < al) (hbe : 0 < be)
    (hu1 : 0 < qq - qr) (hu2 : 0 < rr - qr) (hm : 0 < qq*rr - qr^2) (ht : 0 < -pq)
    (hrel : (1+al)*pq*(qq+rr-2*qr) = -be*(qq*rr-qr^2))
    (hy : 0 < pp*(qq*rr-qr^2) - pq^2*(qq+rr-2*qr)) :
    0 < k28h5bd_G pp (-pq) qq qr rr al be (1+al) 0 be := by
  have hW : 0 < qq + rr - 2*qr := by linarith
  have hA : 0 < 1 + al := by linarith
  have ht' : -pq = be*(qq*rr-qr^2)/((1+al)*((qq-qr)+(rr-qr))) := by
    rw [eq_div_iff (by positivity)]; nlinarith
  have h := k28h5bd_d1_core (qq-qr) (rr-qr) (qq*rr-qr^2) (pp*(qq*rr-qr^2) - pq^2*(qq+rr-2*qr)) al be hu1 hu2 hm hy hal hbe
  rw [← ht'] at h
  have e1 : (-pq)^2*((qq-qr)+(rr-qr)) = pq^2*(qq+rr-2*qr) := by ring
  have e2 : ((-pq)^2*((qq-qr)+(rr-qr)) + (pp*(qq*rr-qr^2) - pq^2*(qq+rr-2*qr)))/(qq*rr-qr^2) = pp := by
    rw [e1]; field_simp; ring
  have e3 : (qq*rr-qr^2 - (qq-qr)*(rr-qr))/((qq-qr)+(rr-qr)) = qr := by
    field_simp; ring
  rw [e2, e3] at h
  have e4 : qq - qr + qr = qq := by ring
  have e5 : rr - qr + qr = rr := by ring
  rw [e4, e5] at h
  exact h

end Minimality.Type08Sp.C2
