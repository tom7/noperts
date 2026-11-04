module

public import Minimality.Type08S.L2.K86F
public import Minimality.Type08S.L2.K91Q

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace
namespace Minimality.Type08Sp.C2

set_option maxHeartbeats 12800000 in
theorem k91_facts {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 lam ν : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hα : 1 < α1) (hβ : 1 < β1) (hb6 : 1 < β6) (hg6 : 1 < γ6)
    (hσ : β1 < β6 + γ6) (hU0 : k28l2aU0 a b c d α1 β1 = 0)
    (hlamdef : lam * ⟪a - d, a' - b'⟫ = -⟪b - d, a' - b'⟫)
    (hνdef : ν * ⟪a - a', a - d⟫ = β1 * (-⟪a - a', c - d⟫))
    (hH : 0 ≤ ⟪c' - a', b' - c⟫) :
    α1 - 1 < ν ∧ 0 ≤ α1 * β1 - (β1 - 1) * ν ∧
    ⟪a, (c - d) + (ν / β1) • (a - d)⟫ < ⟪b', (c - d) + (ν / β1) • (a - d)⟫ ∧
    ⟪c, (c - d) + (ν / β1) • (a - d)⟫ < ⟪b', (c - d) + (ν / β1) • (a - d)⟫ ∧
    (0 < β6 * (α1 - 1) - β1 * (γ6 - 1) →
      ⟪a', (c - d) + (ν / β1) • (a - d)⟫ < ⟪c, (c - d) + (ν / β1) • (a - d)⟫) ∧
    ⟪c', (c - d) + (ν / β1) • (a - d)⟫ = ⟪a, (c - d) + (ν / β1) • (a - d)⟫ ∧
    (β6 * (α1 - 1) - β1 * (γ6 - 1) = 0 → α1 ≤ (β1 - 1) * lam → 0 < ⟪a' - b', c - d⟫) := by
  obtain ⟨fAv, flam, fac, fpq, fU1, fU2, -⟩ := k86_facts hC hM hrel hα hβ hb6 hg6 hσ hU0 hlamdef
  obtain ⟨hPR, hpp0, hqq, hrr⟩ := k32e_facts hC hM
  obtain ⟨hr1, hr2⟩ := hrel
  obtain ⟨hdet, hc', hb', ha', -⟩ := hC
  have ipc : ∀ (x y : ℝ³) (x1 x2 x3 y1 y2 y3 : ℝ),
      x = x1 • (a - d) + x2 • (b - d) + x3 • (c - d) → y = y1 • (a - d) + y2 • (b - d) + y3 • (c - d) →
      ⟪x, y⟫ = k91G ⟪a - d, a - d⟫ ⟪a - d, b - d⟫ ⟪b - d, b - d⟫ ⟪b - d, c - d⟫ ⟪c - d, c - d⟫ x1 x2 x3 y1 y2 y3 := by
    intro x y x1 x2 x3 y1 y2 y3 hx hy
    rw [hx, hy]; exact k32e_ip _ _ _ hPR _ _ _ _ _ _
  obtain ⟨u, rfl⟩ : ∃ u, α1 = u + 1 := ⟨α1 - 1, by ring⟩
  obtain ⟨v, rfl⟩ : ∃ v, β1 = v + 1 := ⟨β1 - 1, by ring⟩
  have hu : 0 < u := by linarith
  have hv : 0 < v := by linarith
  rw [hPR] at fU1 fU2 fpq
  have ht : 0 < -⟪a - d, b - d⟫ := by linarith
  have hx : 0 < ⟪b - d, b - d⟫ - ⟪b - d, c - d⟫ := by linarith
  have hrel' : (⟪c - d, c - d⟫ - ⟪b - d, c - d⟫) *
      (v * (v + 1) * (⟪b - d, b - d⟫ - ⟪b - d, c - d⟫) - (-⟪a - d, b - d⟫) * (u + v + 1)) =
      (-⟪a - d, b - d⟫) * (u + v + 1) * (⟪b - d, b - d⟫ - ⟪b - d, c - d⟫) := by
    linear_combination (v + 1) * hr1 + (-(v) * (⟪b - d, b - d⟫ + ⟪c - d, c - d⟫ - 2 * ⟪b - d, c - d⟫)) * fU2
  set pp := ⟪a - d, a - d⟫ with hpp
  set pq := ⟪a - d, b - d⟫ with hpq
  set qq := ⟪b - d, b - d⟫ with hqq'
  set qr := ⟪b - d, c - d⟫ with hqr
  set rr := ⟪c - d, c - d⟫ with hrr'
  have hW : 0 < v * (v + 1) * (qq - qr) - (-pq) * (u + v + 1) := by
    have h1 : 0 < (-pq) * (u + v + 1) * (qq - qr) := by positivity
    rw [← hrel'] at h1
    exact pos_of_mul_pos_right h1 (by linarith) |>.trans_eq rfl
  have e_a_a' : a - a' = (1:ℝ) • (a - d) + (-β6) • (b - d) + (-γ6) • (c - d) := by rw [ha']; module
  have e_a : a - d = (1:ℝ) • (a - d) + (0:ℝ) • (b - d) + (0:ℝ) • (c - d) := by module
  have e_c : c - d = (0:ℝ) • (a - d) + (0:ℝ) • (b - d) + (1:ℝ) • (c - d) := by module
  have e_b : b - d = (0:ℝ) • (a - d) + (1:ℝ) • (b - d) + (0:ℝ) • (c - d) := by module
  have e_apb : a' - b' = (-(u+1)) • (a - d) + β6 • (b - d) + (γ6 - (v+1)) • (c - d) := by rw [ha', hb']; module
  have hnu : ν * k91G pp pq qq qr rr 1 (-β6) (-γ6) 1 0 0 = (v+1) * (- k91G pp pq qq qr rr 1 (-β6) (-γ6) 0 0 1) := by
    rw [← ipc _ _ 1 (-β6) (-γ6) 1 0 0 e_a_a' e_a, ← ipc _ _ 1 (-β6) (-γ6) 0 0 1 e_a_a' e_c]
    exact hνdef
  have hlam : lam * k91G pp pq qq qr rr 1 0 0 (-(u+1)) β6 (γ6-(v+1)) = - k91G pp pq qq qr rr 0 1 0 (-(u+1)) β6 (γ6-(v+1)) := by
    rw [← ipc _ _ 1 0 0 (-(u+1)) β6 (γ6-(v+1)) e_a e_apb, ← ipc _ _ 0 1 0 (-(u+1)) β6 (γ6-(v+1)) e_b e_apb]
    exact hlamdef
  have hpp' : pp * u = (v + 1) * (-pq) := by linarith [fU1]
  have hqr' : qr * (v + 1) = u * (-pq) := by linarith [fU2]
  have hcore := k91_core (u := u) (v := v) (t := -pq) (x := qq - qr) (b6 := β6) (g6 := γ6) (nu := ν)
    (pp := pp) (pq := pq) (qq := qq) (qr := qr) (rr := rr) hu hv ht hx (by linarith) (by linarith) _ rfl hW
    hpp' (by ring) hqr' (by ring) hrel' hnu
  have hR1 : ∀ x : ℝ³, ∀ x1 x2 x3 : ℝ, x = x1 • (a - d) + x2 • (b - d) + x3 • (c - d) →
      ⟪x, (c - d) + (ν / (v + 1)) • (a - d)⟫ = k91G pp pq qq qr rr x1 x2 x3 (ν / (v + 1)) 0 1 :=
    fun x x1 x2 x3 hx => ipc _ _ x1 x2 x3 _ 0 1 hx (by module)
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hcore
  refine ⟨by linarith, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hh := ipc (c' - a') (b' - c) (u+1) (v+1-β6) (-γ6) (u+1) 0 v (by rw [hc', ha']; module) (by rw [hb']; module)
    rw [hh] at hH
    have := c2 hH
    linarith
  · have h := hR1 (b' - a) u 0 (v+1) (by rw [hb']; module)
    rw [inner_sub_left] at h; linarith
  · have h := hR1 (b' - c) (u+1) 0 v (by rw [hb']; module)
    rw [inner_sub_left] at h; linarith
  · intro hg
    have h := hR1 (c - a') 0 (-β6) (1-γ6) (by rw [ha']; module)
    rw [inner_sub_left] at h; linarith [c5 (by linarith)]
  · have h := hR1 (c' - a) u (v+1) 0 (by rw [hc']; module)
    rw [inner_sub_left] at h; linarith
  · intro hg0 hcb
    have := k91_q2 (u := u) (v := v) (t := -pq) (x := qq - qr) (b6 := β6) (g6 := γ6) (lam := lam)
      (pp := pp) (pq := pq) (qq := qq) (qr := qr) (rr := rr) hu hv ht hx (by linarith) (by linarith) _ rfl hW
      hpp' (by ring) hqr' (by ring) hrel' (by linarith) (by linarith) hlam
    rw [← ipc _ _ (-(u+1)) β6 (γ6-(v+1)) 0 0 1 e_apb e_c] at this
    exact this
end Minimality.Type08Sp.C2
