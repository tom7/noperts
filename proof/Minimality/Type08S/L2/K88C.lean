module

public import Minimality.Type08S.L2.K88A
public import Minimality.Type08S.L2.K77B

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option maxHeartbeats 1000000
open scoped RealInnerProductSpace
open Minimality Minimality.Type08Sp Minimality.Type08Sp.C2

theorem k88_scr (B P Q W Y dx cx ex : ℝ) (hB : 0 < B) (hQ : 0 < Q) (hY : 0 < Y)
    (hd0 : 0 < dx) (hd1 : dx < B) (hc0 : 0 < cx) (hc1 : cx < B)
    (hin3 : Q * ex + (B - P) * 1 < Q * B) (hin4 : (Y - Q) * ex + (P - W) * 1 < P * Y - W * Q)
    (hin5 : -Y * ex + W * 1 < 0) (hW : W ≤ 0)
    (hcase : (Y < Q ∧ B < P) ∨ (Q < Y ∧ W < 0 ∧ B ≤ P) ∨ (Q < Y ∧ W = 0 ∧ B * (Y - Q) < P * Y ∧ 0 < P))
    (sx sy dz cz ez : ℝ) (hsx : 0 < sx) (hsy : 0 < sy) :
    IsRupert (K78.VV (sx*B) (sx*P) (sy*Q) (sx*W) (sy*Y) (sx*dx) dz (sx*cx) cz (sx*ex) (sy*1) ez) := by
  have hxy := mul_pos hsx hsy
  have h3 : (sy*Q) * (sx*ex) + (sx*B - sx*P) * (sy*1) < (sy*Q) * (sx*B) := by
    have := mul_lt_mul_of_pos_left hin3 hxy; nlinarith [this]
  have h4 : (sy*Y - sy*Q) * (sx*ex) + (sx*P - sx*W) * (sy*1) < (sx*P) * (sy*Y) - (sx*W)*(sy*Q) := by
    have := mul_lt_mul_of_pos_left hin4 hxy; nlinarith [this]
  have h5 : -(sy*Y) * (sx*ex) + (sx*W) * (sy*1) < 0 := by
    have := mul_lt_mul_of_pos_left hin5 hxy; nlinarith [this]
  have hd1' : sx*dx < sx*B := by nlinarith
  have hc1' : sx*cx < sx*B := by nlinarith
  have hd0' : 0 < sx*dx := by positivity
  have hc0' : 0 < sx*cx := by positivity
  have hW' : sx*W ≤ 0 := by nlinarith
  have hey : 0 < sy*1 := by positivity
  rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2, h6⟩ | ⟨h1, h2, h6, h7⟩
  · exact K78.k78_thmA _ _ _ _ _ _ dz _ cz _ _ ez (by positivity) (by positivity) (by positivity) hW'
      (by nlinarith) (by nlinarith) hd0' hd1' hc0' hc1' hey h3 h4 h5
  · exact K78.k78_thmB _ _ _ _ _ _ dz _ cz _ _ ez (by positivity) (by positivity) (by positivity)
      (by nlinarith) (by nlinarith) (by nlinarith) hd0' hd1' hc0' hc1' hey h3 h4 h5
  · subst h2
    have hex : 0 < ex := by
      have : 0 < Y * ex := by linarith
      exact pos_of_mul_pos_right this hY.le
    have := K77.k77_thm1 (sx*B) (sx*P) (sy*Q) (sy*Y) (sx*dx) dz (sx*cx) cz (sx*ex) (sy*1) ez
      (by positivity) (by positivity) (by positivity) (by positivity) (by nlinarith) (by nlinarith)
      hd0' hd1' hc0' hc1' hey (by positivity) (by simpa using h3) (by simpa using h4)
    simpa [K77.VV, K78.VV] using this

theorem k88_of_screen {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6)
    (hAv : ⟪a - d, a' - b'⟫ < 0)
    (hzab : ⟪a - b', k61_R a a' b b' d⟫ = 0) (hzba : ⟪a' - b, k61_R a a' b b' d⟫ = 0)
    (B P W dx cx ex : ℝ) (eB : B = ⟪b - a, b - a⟫) (eP : P = ⟪a' - a, b - a⟫) (eW : W = ⟪b' - a, b - a⟫)
    (edx : dx = ⟪d - a, b - a⟫) (ecx : cx = ⟪c' - a, b - a⟫) (eex : ex = ⟪c - a, b - a⟫)
    (hB : 0 < B) (hQ : 0 < γ6) (hY : 0 < β1)
    (hd0 : 0 < dx) (hd1 : dx < B) (hc0 : 0 < cx) (hc1 : cx < B)
    (hin3 : γ6 * ex + (B - P) * 1 < γ6 * B) (hin4 : (β1 - γ6) * ex + (P - W) * 1 < P * β1 - W * γ6)
    (hin5 : -β1 * ex + W * 1 < 0) (hW : W ≤ 0)
    (hcase : (β1 < γ6 ∧ B < P) ∨ (γ6 < β1 ∧ W < 0 ∧ B ≤ P) ∨
      (γ6 < β1 ∧ W = 0 ∧ B * (β1 - γ6) < P * β1 ∧ 0 < P)) :
    IsRupert (V8 a a' b b' c c' d) := by
  obtain ⟨sx, sy, dz, cz, ez, hsx, hsy, h⟩ := k88_geom hC hAv hzab hzba
  rw [← eB, ← eP, ← eW, ← edx, ← ecx, ← eex] at h
  apply h
  have := k88_scr B P γ6 W β1 dx cx ex hB hQ hY hd0 hd1 hc0 hc1 hin3 hin4 hin5 hW hcase sx sy dz cz ez hsx hsy
  simpa only [mul_one] using this
