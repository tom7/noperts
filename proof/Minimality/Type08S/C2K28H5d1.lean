module

public import Mathlib

@[expose] public section

set_option maxHeartbeats 1000000
set_option autoImplicit true
set_option relaxedAutoImplicit true

theorem k28h5d2_core (P t u1 u2 M al be ob og sg b g A B T L5 m2 S : ℝ)
    (hal : 0 < al) (hbe : 0 < be) (hob : 0 < ob) (hog : 0 < og) (hsg : 0 < sg)
    (hb : 0 < b) (hg : 0 < g) (hA : 0 < A) (hB : 0 < B)
    (hu1 : 0 < u1) (hu2 : 0 < u2) (ht : 0 < t) (hm2 : 0 < m2)
    (hT0 : 0 ≤ T) (hL50 : 0 ≤ L5) (hS0 : 0 < S)
    (eb : b = 1 - ob) (eg : g = 1 - og) (eA : A = 1 + al) (eB : B = 1 + be)
    (esg : sg = 1 - ob - og - be) (em2 : m2 = u1*u2 + M*(u1+u2))
    (eT : T = al*P - B*t)
    (eL5 : L5 = -(A*(al*P - B*t) - sg*(B*(u2+M) - al*t)))
    (eS : S = al^2*P - 2*al*B*t + B^2*M)
    (hrel : A * t * (u1 + u2) = be * m2) :
    0 < A * ((al^2*P - 2*al*B*t + B^2*(u1+M)) * (g*u2 - b*u1)
      - B*u1*(T - (b+g)*al*(-t) - B*(b*(u1+M) + g*M))) := by
  have p0 : 0 < u1 * u2 * be * be * ob := by positivity
  have p1 : 0 < u1 * u2 * be * ob * ob := by positivity
  have p2 : 0 < u1 * u2 * be * ob * og := by positivity
  have p3 : 0 < u1 * u2 * be * ob * sg := by positivity
  have p4 : 0 < u1 * u2 * ob * ob * b := by positivity
  have p5 : 0 < u1 * u2 * ob * ob * B := by positivity
  have p6 : 0 < u1 * u2 * ob * og * b := by positivity
  have p7 : 0 < u1 * u2 * ob * sg * b := by positivity
  have p8 : 0 < u1 * t * al * ob := by positivity
  have p9 : 0 < u1 * t * al * og := by positivity
  have p10 : 0 < u1 * t * be * og := by positivity
  have p11 : 0 < u1 * t * ob * og := by positivity
  have p12 : 0 < u1 * t * og * sg := by positivity
  have p13 : 0 < u1 * t * al * be * ob := by positivity
  have p14 : 0 < u1 * t * al * be * A := by positivity
  have p15 : 0 < u1 * t * al * og * A := by positivity
  have p16 : 0 < u1 * t * og * og * og := by positivity
  have p17 : 0 < u1 * t * og * og * g := by positivity
  have p18 : 0 ≤ u1 * T * al * al * ob := by positivity
  have p19 : 0 ≤ u1 * T * al * be * A := by positivity
  have p20 : 0 ≤ u1 * L5 := by positivity
  have p21 : 0 ≤ u1 * L5 * be := by positivity
  have p22 : 0 ≤ u1 * L5 * al * be := by positivity
  have p23 : 0 ≤ u1 * L5 * al * og := by positivity
  have p24 : 0 ≤ u1 * L5 * al * g := by positivity
  have p25 : 0 < u1 * S * be * be * ob := by positivity
  have p26 : 0 < u1 * S * be * ob * ob := by positivity
  have p27 : 0 < u1 * S * be * ob * og := by positivity
  have p28 : 0 < u1 * S * ob * ob * ob := by positivity
  have p29 : 0 < u1 * S * ob * ob * og := by positivity
  have p30 : 0 < u1 * S * ob * ob * sg := by positivity
  have p31 : 0 < u1 * S * ob * og * og := by positivity
  have p32 : 0 < u1 * S * ob * og * sg := by positivity
  have p33 : 0 < u1 * S * ob * sg * B := by positivity
  have p34 : 0 < u2 * t * og := by positivity
  have p35 : 0 < u2 * t * al * be := by positivity
  have p36 : 0 < u2 * t * al * ob := by positivity
  have p37 : 0 < u2 * t * al * al * be := by positivity
  have p38 : 0 < u2 * t * al * al * og := by positivity
  have p39 : 0 < u2 * t * al * be * ob := by positivity
  have p40 : 0 < u2 * t * al * ob * og := by positivity
  have p41 : 0 < u2 * t * al * og * b := by positivity
  have p42 : 0 ≤ u2 * T * al * be := by positivity
  have p43 : 0 ≤ u2 * T * al * al * be := by positivity
  have p44 : 0 ≤ u2 * T * al * al * ob := by positivity
  have p45 : 0 < u2 * S * ob * ob := by positivity
  have p46 : 0 < u2 * S * al * ob * sg := by positivity
  have p47 : 0 < u2 * S * al * og * sg := by positivity
  have p48 : 0 < u2 * S * be * sg * A := by positivity
  have p49 : 0 < u2 * S * ob * ob * sg := by positivity
  have p50 : 0 < u2 * S * ob * og * sg := by positivity
  have p51 : 0 < u2 * S * ob * og * b := by positivity
  have p52 : 0 < u2 * S * ob * sg * b := by positivity
  have p53 : 0 < u2 * S * ob * b * g := by positivity
  have p54 : 0 < u2 * S * og * sg * b := by positivity
  have p55 : 0 < u2 * S * sg * sg * A := by positivity
  have p56 : 0 < m2 * al * be * g := by positivity
  have p57 : 0 < m2 * al * ob * B := by positivity
  have p58 : 0 < m2 * be * be * be := by positivity
  have p59 : 0 < m2 * be * be * ob := by positivity
  have p60 : 0 < m2 * be * be * og := by positivity
  have p61 : 0 < m2 * be * be * b := by positivity
  have p62 : 0 < m2 * be * ob * og := by positivity
  have p63 : 0 < m2 * be * ob * g := by positivity
  have p64 : 0 < m2 * be * sg * B := by positivity
  have r0 : (og) * (A * t * (u1 + u2)) = (og) * (be * (u1*u2 + M*(u1+u2))) := by rw [hrel, em2]
  have r1 : (al * be) * (A * t * (u1 + u2)) = (al * be) * (be * (u1*u2 + M*(u1+u2))) := by rw [hrel, em2]
  have r2 : (al * ob) * (A * t * (u1 + u2)) = (al * ob) * (be * (u1*u2 + M*(u1+u2))) := by rw [hrel, em2]
  have r3 : (al * og) * (A * t * (u1 + u2)) = (al * og) * (be * (u1*u2 + M*(u1+u2))) := by rw [hrel, em2]
  have r4 : (al * be * be) * (A * t * (u1 + u2)) = (al * be * be) * (be * (u1*u2 + M*(u1+u2))) := by rw [hrel, em2]
  have r5 : (al * be * ob) * (A * t * (u1 + u2)) = (al * be * ob) * (be * (u1*u2 + M*(u1+u2))) := by rw [hrel, em2]
  subst eb eg eA eB esg eT eL5 eS
  subst em2
  linarith [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, p29, p30, p31, p32, p33, p34, p35, p36, p37, p38, p39, p40, p41, p42, p43, p44, p45, p46, p47, p48, p49, p50, p51, p52, p53, p54, p55, p56, p57, p58, p59, p60, p61, p62, p63, p64, r0, r1, r2, r3, r4, r5]
