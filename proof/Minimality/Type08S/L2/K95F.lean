module

public import Minimality.Type08S.L2.K71B
public import Minimality.Type08S.L2.K92B
public import Minimality.Type08S.L2.K92D
public import Minimality.Type08S.L2.K95B
public import Minimality.Type08S.L2.K95C

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace
namespace Minimality.Type08Sp.C2

theorem k92_pos_of {G Ri Ac : ℝ} (hR : Ri < 0) (hA : Ac < 0) (h : G * Ac = Ri) : 0 < G := by
  by_contra hn; push Not at hn
  have := mul_nonneg_of_nonpos_of_nonpos hn hA.le
  linarith

theorem k92_nn1 {s a q b D : ℝ} (hs : 0 < s) (ha : 0 < a) (hb : 0 < b) (hD : 0 < D)
    (h : 0 ≤ s * (a * q * b / D)) : 0 ≤ q := by
  by_contra hq; push Not at hq
  have : s * (a * q * b / D) < 0 :=
    mul_neg_of_pos_of_neg hs (div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg ha hq) hb) hD)
  linarith

theorem k92_nn2 {s a q D : ℝ} (hs : 0 < s) (ha : 0 < a) (hD : 0 < D)
    (h : 0 ≤ s * (a * q / D)) : 0 ≤ q := by
  by_contra hq; push Not at hq
  have : s * (a * q / D) < 0 :=
    mul_neg_of_pos_of_neg hs (div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg ha hq) hD)
  linarith

set_option maxHeartbeats 25600000 in
theorem k95_gwb {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6) (hM : K6sM a a' b b' c c' d)
    (hrel : K16Rel a b c d α1 β1) (hα1 : 1 < α1) (hβ1 : 1 < β1) (hb6 : 1 < β6) (hg6 : 1 < γ6)
    (hσ : β1 < β6 + γ6) (hX3 : ⟪a - c', a - b'⟫ ≤ 0) (hX4 : 0 ≤ ⟪c' - a, b' - c⟫)
    (hH : 0 ≤ ⟪c' - a', b' - c⟫)
    (hz1 : ⟪a - a', k28l2aU0 a b c d α1 β1⟫ = 0)
    (hz2 : ⟪a', k28l2aU0 a b c d α1 β1⟫ = ⟪c, k28l2aU0 a b c d α1 β1⟫)
    (hgWb : β6 * (α1 - 1) = β1 * (γ6 - 1)) (hU0 : k28l2aU0 a b c d α1 β1 ≠ 0) :
    HasLexCell (V8 a a' b b' c c' d) ∨
      (⟪a - b', k61_R a a' b b' d⟫ = 0 ∧ ⟪a' - b, k61_R a a' b b' d⟫ = 0 ∧
        0 < 1 - α1 + β1 * k61_lam a a' b b' d ∧ 0 < α1 - (β1 - 1) * k61_lam a a' b b' d) := by
  obtain ⟨fAv, fF3⟩ := k71_facts hC hM hrel hα1 hβ1 hz1 hz2 hgWb
  obtain ⟨pp, s, qq, qr, rr, m, hpp_d, hs_d, hpr_d, hqq_d, hqr_d, hrr_d, hb6m, hg6m, hs, hpp, hm, hqx, hqy,
    hrel', hppE, hW, hD, hdet, hD2⟩ := k71_gram hC hM hrel hα1 hβ1 hz1 hz2 hgWb
  have hC' := hC
  obtain ⟨-, hc', hb', ha', -⟩ := hC'
  obtain ⟨hPR, -, -, -⟩ := k32e_facts hC hM
  obtain ⟨u, v, x, y, hu_d, hv_d, hx, hy, hqr_c, hqq_c, hrr_c, hpp_c, hWn⟩ :=
    k92_chart hs hα1 hβ1 hqx hqy hrel' hppE hW
  have hα : α1 = u + 1 := by linarith
  have hβ : β1 = v + 1 := by linarith
  have hu : 0 < u := by linarith
  have hv : 0 < v := by linarith
  have hAA : ⟪a - d, a - d⟫ = s * k92pp u v x y := by rw [← hpp_d]; exact hpp_c
  have hAB : ⟪a - d, b - d⟫ = -s := by linarith
  have hBB : ⟪b - d, b - d⟫ = s * (k92qr u v x y + x) := by rw [← hqq_d]; exact hqq_c
  have hBC : ⟪b - d, c - d⟫ = s * k92qr u v x y := by rw [← hqr_d]; exact hqr_c
  have hCC : ⟪c - d, c - d⟫ = s * (k92qr u v x y + y) := by rw [← hrr_d]; exact hrr_c
  have ipc : ∀ (p q : ℝ³) (x1 x2 x3 y1 y2 y3 : ℝ),
      p = x1 • (a - d) + x2 • (b - d) + x3 • (c - d) → q = y1 • (a - d) + y2 • (b - d) + y3 • (c - d) →
      ⟪p, q⟫ = s * k92G u v x y x1 x2 x3 y1 y2 y3 := by
    intro p q x1 x2 x3 y1 y2 y3 hp hq
    rw [hp, hq, k32e_ip _ _ _ hPR, hAA, hAB, hBB, hBC, hCC]
    exact k92_scale s _ _ _ _ x1 x2 x3 y1 y2 y3
  have eA : a - d = (1:ℝ) • (a - d) + (0:ℝ) • (b - d) + (0:ℝ) • (c - d) := by module
  have eB : b - d = (0:ℝ) • (a - d) + (1:ℝ) • (b - d) + (0:ℝ) • (c - d) := by module
  have eC : c - d = (0:ℝ) • (a - d) + (0:ℝ) • (b - d) + (1:ℝ) • (c - d) := by module
  have e_apb : a' - b' = (-(u+1)) • (a - d) + ((v+1)*m) • (b - d) + (1+u*m-(v+1)) • (c - d) := by
    rw [ha', hb', hb6m, hg6m, hα, hβ]; module
  -- signs from the atoms
  have hsig : 0 < m*(u+v+1) - v := by
    rw [hb6m, hg6m, hα, hβ] at hσ; nlinarith [hσ]
  have hPm : 0 < k92Pm u v m x y := by
    unfold k92Pm
    have h1 := mul_pos hm hWn
    have h2 : 0 < v*y*(v*x+x+y) := by positivity
    linarith
  have hW0 := hWn.ne'
  have hP0 := hPm.ne'
  have hxy : 0 < x + y := by linarith
  have hD1 : 0 < (x+y) * k92Wn u v x y := by positivity
  -- atoms
  have hl : 0 ≤ k92l u v x y := by
    have h := hH
    rw [ipc (c' - a') (b' - c) (u+1) (v+1-(v+1)*m) (-(1+u*m)) (u+1) 0 v
      (by rw [hc', ha', hb6m, hg6m, hα, hβ]; module) (by rw [hb', hα, hβ]; module),
      k92_H u v m x y hv hx hy hW0 hP0] at h
    exact k92_nn1 hs (by positivity) hPm hD1 h
  have hlK : 0 ≤ k92l u v x y * k92K u v x y := by
    have h := hX4
    rw [ipc (c' - a) (b' - c) u (v+1) 0 (u+1) 0 v
      (by rw [hc', hα, hβ]; module) (by rw [hb', hα, hβ]; module),
      k92_X4 u v m x y hv hx hy hW0 hP0] at h
    have e : v*y*k92l u v x y*k92K u v x y = (v*y)*(k92l u v x y*k92K u v x y) := by ring
    rw [e] at h
    exact k92_nn2 hs (by positivity) hD1 h
  have hX3' : k92K u v x y * k92M3 u v x y ≤ 0 := by
    have h := hX3
    rw [ipc (a - c') (a - b') (-u) (-(v+1)) 0 (-u) 0 (-(v+1))
      (by rw [hc', hα, hβ]; module) (by rw [hb', hα, hβ]; module),
      k92_X3 u v m x y hv hx hy hW0 hP0] at h
    by_contra hn; push Not at hn
    have : 0 < s * (k92K u v x y * k92M3 u v x y / (v*(x+y)*k92Wn u v x y)) :=
      mul_pos hs (div_pos hn (by positivity))
    linarith
  have hK : k92K u v x y ≠ 0 := by
    intro hK0
    apply hU0
    have hUv : k28l2aU0 a b c d α1 β1 = ((1 - α1) * ⟪a - d, b - d⟫ - β1 * ⟪b - d, c - d⟫) • (a - d) + (0:ℝ) • (b - d) +
        (-((1 - α1) * ⟪a - d, a - d⟫ - β1 * ⟪a - d, b - d⟫)) • (c - d) := by
      unfold k28l2aU0; module
    have c1 : (1 - α1) * ⟪a - d, b - d⟫ - β1 * ⟪b - d, c - d⟫ = 0 := by
      rw [hAB, hBC, hα, hβ]
      have : u - (v+1)*k92qr u v x y = k92K u v x y / (v*(x+y)) := by
        unfold k92qr k92K; field_simp; ring
      have h2 : u - (v+1)*k92qr u v x y = 0 := by rw [this, hK0]; simp
      linear_combination s * h2
    have c3 : -((1 - α1) * ⟪a - d, a - d⟫ - β1 * ⟪a - d, b - d⟫) = 0 := by
      rw [hAA, hAB, hα, hβ]
      have : u * k92pp u v x y - (v+1) = (u+v+1) * k92K u v x y / k92Wn u v x y := by
        unfold k92pp k92K; field_simp; unfold k92Wn; ring
      have h2 : u * k92pp u v x y - (v+1) = 0 := by rw [this, hK0]; simp
      linear_combination s * h2
    rw [hUv, c1, c3]; simp
  obtain ⟨hAc, hBc, hF1, hF2, hzA, hzB, hDP, hQ1, hQ2, hAC⟩ :=
    k92_signs u v m x y hu hv hm hx hy hWn hl hlK hX3' hK hsig
  obtain ⟨lam, hlamd⟩ : ∃ l, l = k61_lam a a' b b' d := ⟨_, rfl⟩
  have hAv_c : ⟪a - d, a' - b'⟫ = s * k92Ac u v m x y := by
    rw [ipc _ _ 1 0 0 _ _ _ eA e_apb, k92_Av u v m x y hv hx hy hW0 hP0]
  have hBv_c : ⟪b - d, a' - b'⟫ = s * k92Bc u v m x y := by
    rw [ipc _ _ 0 1 0 _ _ _ eB e_apb, k92_Bv u v m x y hv hx hy hW0 hP0]
  have hlamc : lam * k92Ac u v m x y = - k92Bc u v m x y := by
    have h1 : lam * ⟪a - d, a' - b'⟫ = -⟪b - d, a' - b'⟫ := by
      rw [hlamd]; unfold k61_lam; field_simp [fAv.ne]
    rw [hAv_c, hBv_c] at h1
    have : s * (lam * k92Ac u v m x y + k92Bc u v m x y) = 0 := by linear_combination h1
    have := (mul_eq_zero.1 this).resolve_left hs.ne'
    linarith
  have hRv : k61_R a a' b b' d = lam • (a - d) + (1:ℝ) • (b - d) + (0:ℝ) • (c - d) := by
    unfold k61_R; rw [← hlamd]; module
  have hR : ∀ (X : ℝ³) (x1 x2 x3 : ℝ), X = x1 • (a - d) + x2 • (b - d) + x3 • (c - d) →
      ⟪X, k61_R a a' b b' d⟫ = s * k92G u v x y x1 x2 x3 lam 1 0 :=
    fun X x1 x2 x3 hX => ipc X _ x1 x2 x3 lam 1 0 hX hRv
  have hRin : ∀ x1 x2 x3 : ℝ, k92G u v x y x1 x2 x3 lam 1 0 * k92Ac u v m x y = k92Rin u v m x y x1 x2 x3 := by
    intro x1 x2 x3
    unfold k92Rin
    rw [k92_lin u v x y x1 x2 x3 lam 1 0, k92_lin u v x y x1 x2 x3 (-k92Bc u v m x y) (k92Ac u v m x y) 0]
    linear_combination (k92G u v x y x1 x2 x3 1 0 0) * hlamc
  have fL : 0 < ⟪b - d, a' - b'⟫ := by rw [hBv_c]; exact mul_pos hs hBc
  have fF1 : 0 < ⟪c' - a, k61_R a a' b b' d⟫ := by
    rw [hR (c' - a) u (v+1) 0 (by rw [hc', hα, hβ]; module)]
    exact mul_pos hs (k92_pos_of hF1 hAc (hRin u (v+1) 0))
  have fF2 : 0 < ⟪c' - b, k61_R a a' b b' d⟫ := by
    rw [hR (c' - b) (u+1) v 0 (by rw [hc', hα, hβ]; module)]
    exact mul_pos hs (k92_pos_of hF2 hAc (hRin (u+1) v 0))
  have fzA : 0 < ⟪a - d, k61_R a a' b b' d⟫ := by
    rw [hR (a - d) 1 0 0 eA]
    exact mul_pos hs (k92_pos_of hzA hAc (hRin 1 0 0))
  have fzB : 0 < ⟪b - d, k61_R a a' b b' d⟫ := by
    rw [hR (b - d) 0 1 0 eB]
    exact mul_pos hs (k92_pos_of hzB hAc (hRin 0 1 0))
  have eab : a - b' = (-u) • (a - d) + (0:ℝ) • (b - d) + (-(v+1)) • (c - d) := by
    rw [hb', hα, hβ]; module
  have fDP : ⟪a - b', k61_R a a' b b' d⟫ = 0 → 0 < ⟪b' - a, a - d⟫ := by
    intro h0
    rw [hR (a - b') (-u) 0 (-(v+1)) eab] at h0
    have hG := (mul_eq_zero.1 h0).resolve_left hs.ne'
    have h1 := hDP (by rw [← hRin, hG]; ring)
    rw [ipc (b' - a) (a - d) u 0 (v+1) 1 0 0 (by rw [hb', hα, hβ]; module) eA]
    exact mul_pos hs h1
  have fQ1 : β1 * k61_lam a a' b b' d + 1 < α1 → 0 < ⟪b' - a', c - d⟫ := by
    intro h
    rw [← hlamd, hα, hβ] at h
    have hPB : 0 < -u*k92Ac u v m x y - (v+1)*k92Bc u v m x y := by
      nlinarith [mul_pos (sub_pos.2 (by linarith : (v+1)*lam < u)) (neg_pos.2 hAc), hlamc]
    have hq := hQ1 hPB
    rw [ipc (b' - a') (c - d) (u+1) (-((v+1)*m)) (v+1-(1+u*m)) 0 0 1
      (by rw [hb', ha', hb6m, hg6m, hα, hβ]; module) eC]
    exact mul_pos hs hq
  have fQ2 : α1 ≤ (β1 - 1) * k61_lam a a' b b' d → 0 < ⟪a' - b', c - d⟫ := by
    intro h
    rw [← hlamd, hα, hβ] at h
    have h' : 0 ≤ v*lam - (u+1) := by linarith
    have hPC : 0 ≤ (u+1)*k92Ac u v m x y + v*k92Bc u v m x y := by
      nlinarith [mul_nonneg h' (neg_nonneg.2 hAc.le), hlamc]
    have hq := hQ2 hPC
    rw [ipc (a' - b') (c - d) (-(u+1)) ((v+1)*m) (1+u*m-(v+1)) 0 0 1 e_apb eC]
    have e : k92G u v x y (-(u+1)) ((v+1)*m) (1+u*m-(v+1)) 0 0 1 =
        - k92G u v x y (u+1) (-((v+1)*m)) (v+1-(1+u*m)) 0 0 1 := by
      simp only [k92G, k91G]; ring
    rw [e]
    have := mul_pos hs (neg_pos.2 hq)
    linarith
  have fAC0 : α1 = β1 * k61_lam a a' b b' d + 1 → 0 ≤ ⟪a - b', k61_R a a' b b' d⟫ := by
    intro h
    rw [← hlamd, hα, hβ] at h
    have h' : u = (v+1)*lam := by linarith
    have hPB0 : -u*k92Ac u v m x y - (v+1)*k92Bc u v m x y = 0 := by
      linear_combination (-(k92Ac u v m x y)) * h' + (-(v+1)) * hlamc
    have hle := hAC hPB0
    rw [hR (a - b') (-u) 0 (-(v+1)) eab]
    refine mul_nonneg hs.le ?_
    by_contra hn; push Not at hn
    have := mul_pos_of_neg_of_neg hn hAc
    rw [hRin] at this
    linarith
  have fQT : α1 = β1 * k61_lam a a' b b' d + 1 → 0 < ⟪b' - a', c - d⟫ := by
    intro h
    rw [← hlamd, hα, hβ] at h
    have h' : u = (v+1)*lam := by linarith
    have hPB0 : -u*k92Ac u v m x y - (v+1)*k92Bc u v m x y = 0 := by
      linear_combination (-(k92Ac u v m x y)) * h' + (-(v+1)) * hlamc
    have hq := k95_fQT u v m x y hu hv hm hx hy hWn hl hlK hPB0.ge
    rw [ipc (b' - a') (c - d) (u+1) (-((v+1)*m)) (v+1-(1+u*m)) 0 0 1
      (by rw [hb', ha', hb6m, hg6m, hα, hβ]; module) eC]
    exact mul_pos hs hq
  have fQ2T : α1 = β1 * k61_lam a a' b b' d + 1 → ⟪a - b', k61_R a a' b b' d⟫ = 0 → 0 < ⟪a' - b, c - d⟫ := by
    intro _ h0
    rw [hR (a - b') (-u) 0 (-(v+1)) eab] at h0
    have hG := (mul_eq_zero.1 h0).resolve_left hs.ne'
    have hz : k92Rin u v m x y (-u) 0 (-(v+1)) = 0 := by rw [← hRin, hG]; ring
    rw [k92_zab u v m x y hv hx hy hW0 hP0] at hz
    have h1 : (u+v+1)*(m*k92l u v x y - y)*k92K u v x y = 0 := by
      rcases div_eq_zero_iff.1 hz with h | h
      · exact h
      · exact absurd h hW0
    have h2 : m*k92l u v x y - y = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · rcases mul_eq_zero.1 h with h | h
        · exfalso; linarith
        · exact h
      · exact absurd h hK
    have hq := k95_fQ2T u v m x y hu hv hm hx hy hWn hl (by linarith)
    have eab' : a' - b = (0:ℝ) • (a - d) + ((v+1)*m-1) • (b - d) + (1+u*m) • (c - d) := by
      rw [ha', hb6m, hg6m, hα, hβ]; module
    rw [ipc (a' - b) (c - d) 0 ((v+1)*m-1) (1+u*m) 0 0 1 eab' eC]
    exact mul_pos hs hq
  have fN1 : 0 < ⟪b - a', a - d⟫ := by
    rw [ipc (b - a') (a - d) 0 (1-(v+1)*m) (-(1+u*m)) 1 0 0
      (by rw [ha', hb6m, hg6m, hα, hβ]; module) eA]
    have e : k92G u v x y 0 (1-(v+1)*m) (-(1+u*m)) 1 0 0 = m*(u+v+1) := by
      simp only [k92G, k91G]; ring
    rw [e]
    exact mul_pos hs (by positivity)
  exact k95_comb hC hM hrel hα1 hβ1 hb6 hg6 hσ hX4 hz1 hz2 fAv fL fF1 fF2 fF3 fzA fzB fDP fQ1 fQ2 fAC0 fN1 fQT fQ2T
end Minimality.Type08Sp.C2
