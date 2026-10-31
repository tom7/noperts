module

public import Minimality.CycSeq

@[expose] public section

/-!
Lemma V(a) of nopert229/out/bottleneck/virial/draft.md §4 (angle-free proof): the screen virial of a balanced outward load is PSD.
-/

namespace Minimality
open scoped RealInnerProductSpace


/-- Core, in terms of coefficients. -/
theorem orient_core (a1 a2 b1 b2 c1 c2 x1 x2 y1 y2 g d al be g' d' : ℝ)
    (hP : 0 < a1*b2 - a2*b1) (hQ : 0 < b1*c2 - b2*c1)
    (hg : 0 ≤ g) (hd : 0 ≤ d) (hal : 0 ≤ al) (hbe : 0 ≤ be) (hg' : 0 ≤ g') (hd' : 0 ≤ d')
    (hx1 : x1 = -g*a2 - d*b2) (hx2 : x2 = g*a1 + d*b1)
    (hy1 : y1 = -al*b2 - be*c2) (hy2 : y2 = al*b1 + be*c1)
    (hz1 : -(x1+y1) = -g'*c2 - d'*a2) (hz2 : -(x2+y2) = g'*c1 + d'*a1) :
    0 ≤ x1*y2 - x2*y1 := by
  have hT : x1*y2 - x2*y1 = g*al*(a1*b2-a2*b1) + g*be*(a1*c2-a2*c1) + d*be*(b1*c2-b2*c1) := by
    subst hx1 hx2 hy1 hy2; ring
  have E1 : (g+d')*a2 + (d+al)*b2 + (be+g')*c2 = 0 := by linarith
  have E2 : (g+d')*a1 + (d+al)*b1 + (be+g')*c1 = 0 := by linarith
  rcases le_or_gt 0 (a1*c2-a2*c1) with hR | hR
  · rw [hT]
    have := mul_nonneg (mul_nonneg hg hal) hP.le
    have := mul_nonneg (mul_nonneg hg hbe) hR
    have := mul_nonneg (mul_nonneg hd hbe) hQ.le
    linarith
  · -- hard case
    have hS : 0 < c1*a2 - c2*a1 := by linarith
    -- A*P = C*Q, A*R = -B*Q  (crossing)
    have k1 : (g+d')*(a1*b2-a2*b1) = (be+g')*(b1*c2-b2*c1) := by
      linear_combination b2 * E2 - b1 * E1
    have k2 : (g+d')*(a1*c2-a2*c1) = -(d+al)*(b1*c2-b2*c1) := by
      linear_combination c2 * E2 - c1 * E1
    have hAT : (g+d')*(x1*y2 - x2*y1) = (b1*c2-b2*c1)*(g*al*g' + d*be*d') := by
      rw [hT]
      linear_combination (g*al) * k1 + (g*be) * k2 + 0
    have hQT : 0 ≤ (g+d')*(x1*y2 - x2*y1) := by
      rw [hAT]; exact mul_nonneg hQ.le (by positivity)
    rcases (add_nonneg hg hd').eq_or_lt with h0 | h0
    · have hg0 : g = 0 := by linarith
      have hd0' : d' = 0 := by linarith
      have hB : (d+al)*(b1*c2-b2*c1) = 0 := by rw [hg0, hd0'] at k2; linarith
      have hd0 : d = 0 := by
        rcases mul_eq_zero.mp hB with h | h
        · linarith
        · linarith
      rw [hT, hg0, hd0]; simp
    · exact nonneg_of_mul_nonneg_right hQT h0 |> fun h => by simpa using h

theorem virial_pair1 (u1 u2 v1 v2 d1 d2 : ℝ) (hP : u1*v2 - u2*v1 ≠ 0) :
    d1 = -((v1*d1+v2*d2)/(u1*v2-u2*v1))*u2 - (-(u1*d1+u2*d2)/(u1*v2-u2*v1))*v2 := by
  generalize hP' : u1*v2-u2*v1 = P at *
  field_simp
  rw [← hP']; ring

theorem virial_pair2 (u1 u2 v1 v2 d1 d2 : ℝ) (hP : u1*v2 - u2*v1 ≠ 0) :
    d2 = ((v1*d1+v2*d2)/(u1*v2-u2*v1))*u1 + (-(u1*d1+u2*d2)/(u1*v2-u2*v1))*v1 := by
  generalize hP' : u1*v2-u2*v1 = P at *
  field_simp
  rw [← hP']; ring

theorem orient_real (a1 a2 b1 b2 c1 c2 x1 x2 y1 y2 : ℝ)
    (h1 : 0 < a1*b2 - a2*b1) (h2 : 0 < b1*c2 - b2*c1)
    (hra : a1*x1 + a2*x2 ≤ 0) (har : 0 ≤ b1*x1 + b2*x2)
    (hab : b1*y1 + b2*y2 ≤ 0) (hba : 0 ≤ c1*y1 + c2*y2)
    (hrb : a1*(x1+y1) + a2*(x2+y2) ≤ 0) (hbr : 0 ≤ c1*(x1+y1) + c2*(x2+y2)) :
    0 ≤ x1*y2 - x2*y1 := by
  have hP := h1.ne'
  have hQ := h2.ne'
  have gx := virial_pair1 a1 a2 b1 b2 x1 x2 hP
  have gx' := virial_pair2 a1 a2 b1 b2 x1 x2 hP
  have gy := virial_pair1 b1 b2 c1 c2 y1 y2 hQ
  have gy' := virial_pair2 b1 b2 c1 c2 y1 y2 hQ
  have hg : 0 ≤ (b1*x1+b2*x2)/(a1*b2-a2*b1) := div_nonneg har h1.le
  have hd : 0 ≤ -(a1*x1+a2*x2)/(a1*b2-a2*b1) := div_nonneg (by linarith) h1.le
  have hal : 0 ≤ (c1*y1+c2*y2)/(b1*c2-b2*c1) := div_nonneg hba h2.le
  have hbe : 0 ≤ -(b1*y1+b2*y2)/(b1*c2-b2*c1) := div_nonneg (by linarith) h2.le
  rcases le_or_gt 0 (a1*c2-a2*c1) with hR | hR
  · generalize (b1*x1+b2*x2)/(a1*b2-a2*b1) = g at *
    generalize -(a1*x1+a2*x2)/(a1*b2-a2*b1) = d at *
    generalize (c1*y1+c2*y2)/(b1*c2-b2*c1) = al at *
    generalize -(b1*y1+b2*y2)/(b1*c2-b2*c1) = be at *
    have hT : x1*y2 - x2*y1 = g*al*(a1*b2-a2*b1) + g*be*(a1*c2-a2*c1) + d*be*(b1*c2-b2*c1) := by
      rw [gx, gx', gy, gy']; ring
    rw [hT]
    have := mul_nonneg (mul_nonneg hg hal) h1.le
    have := mul_nonneg (mul_nonneg hg hbe) hR
    have := mul_nonneg (mul_nonneg hd hbe) h2.le
    linarith
  · have hS : 0 < c1*a2 - c2*a1 := by linarith
    have hS' := hS.ne'
    have gz := virial_pair1 c1 c2 a1 a2 (-(x1+y1)) (-(x2+y2)) hS'
    have gz' := virial_pair2 c1 c2 a1 a2 (-(x1+y1)) (-(x2+y2)) hS'
    have hg' : 0 ≤ (a1*(-(x1+y1))+a2*(-(x2+y2)))/(c1*a2-c2*a1) :=
      div_nonneg (by linarith) hS.le
    have hd' : 0 ≤ -(c1*(-(x1+y1))+c2*(-(x2+y2)))/(c1*a2-c2*a1) :=
      div_nonneg (by linarith) hS.le
    exact orient_core a1 a2 b1 b2 c1 c2 x1 x2 y1 y2 _ _ _ _ _ _ h1 h2 hg hd hal hbe hg' hd'
      (by rw [← gx]) (by rw [← gx']) (by rw [← gy]) (by rw [← gy']) (by rw [← gz]) (by rw [← gz'])

/-- Orientation lemma (O). -/
theorem orient3 (pr pa pb fr fa fb : ℝ²)
    (h1 : 0 < cross2 fr fa) (h2 : 0 < cross2 fa fb)
    (hra : ⟪fr, pa - pr⟫ ≤ 0) (hrb : ⟪fr, pb - pr⟫ ≤ 0)
    (har : ⟪fa, pr - pa⟫ ≤ 0) (hab : ⟪fa, pb - pa⟫ ≤ 0)
    (hbr : ⟪fb, pr - pb⟫ ≤ 0) (hba : ⟪fb, pa - pb⟫ ≤ 0) :
    0 ≤ cross2 (pa - pr) (pb - pr) := by
  simp only [cross2, PiLp.inner_apply, Fin.sum_univ_two, PiLp.sub_apply,
    RCLike.inner_apply, conj_trivial] at *
  have := orient_real (fr 0) (fr 1) (fa 0) (fa 1) (fb 0) (fb 1)
    (pa 0 - pr 0) (pa 1 - pr 1) (pb 0 - pa 0) (pb 1 - pa 1) h1 h2
    (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
  nlinarith


lemma virial_psd2 (m00 m01 m11 a0 a1 : ℝ) (htr : 0 ≤ m00 + m11)
    (hdet : 0 ≤ m00 * m11 - m01 ^ 2) :
    0 ≤ a0 ^ 2 * m00 + 2 * a0 * a1 * m01 + a1 ^ 2 * m11 := by
  have h00 : 0 ≤ m00 := by
    by_contra h
    have h' : m00 < 0 := lt_of_not_ge h
    nlinarith [sq_nonneg m01, mul_pos (neg_pos.2 h') (show 0 < m11 by linarith)]
  have h11 : 0 ≤ m11 := by
    by_contra h
    have h' : m11 < 0 := lt_of_not_ge h
    nlinarith [sq_nonneg m01, mul_pos (neg_pos.2 h') (show 0 < m00 by linarith)]
  rcases h00.eq_or_lt with h | h
  · have : m01 = 0 := by
      rw [← h] at hdet
      nlinarith [sq_nonneg m01]
    rw [this, ← h]
    nlinarith [sq_nonneg a1]
  · have : 0 ≤ m00 * (a0 ^ 2 * m00 + 2 * a0 * a1 * m01 + a1 ^ 2 * m11) := by
      nlinarith [sq_nonneg (a0 * m00 + a1 * m01), mul_nonneg (sq_nonneg a1) hdet]
    exact nonneg_of_mul_nonneg_right this h

lemma virial_term_nonneg (pr pa pb fr fa fb : ℝ²) (c : ℝ) (hc : 0 ≤ c)
    (hy : 0 < c → 0 < cross2 fr fa ∧ 0 < cross2 fa fb)
    (hra : ⟪fr, pa - pr⟫ ≤ 0) (hrb : ⟪fr, pb - pr⟫ ≤ 0)
    (har : ⟪fa, pr - pa⟫ ≤ 0) (hab : ⟪fa, pb - pa⟫ ≤ 0)
    (hbr : ⟪fb, pr - pb⟫ ≤ 0) (hba : ⟪fb, pa - pb⟫ ≤ 0) :
    0 ≤ cross2 (pa - pr) (pb - pr) * c := by
  rcases hc.eq_or_lt with h | h
  · rw [← h]; simp
  · obtain ⟨h1, h2⟩ := hy h
    exact mul_nonneg (orient3 pr pa pb fr fa fb h1 h2 hra hrb har hab hbr hba) h.le

theorem virial_good (p f : Fin 4 → ℝ²)
    (hout : ∀ j k, ⟪f j, p k - p j⟫ ≤ 0)
    (hF : ∑ j, f j = 0) (hT : ∑ j, cross2 (p j) (f j) = 0)
    (h12 : 0 ≤ cross2 (f 1) (f 2)) (h23 : 0 ≤ cross2 (f 2) (f 3))
    (h13 : 0 ≤ cross2 (f 1) (f 3)) (a : ℝ²) :
    0 ≤ ∑ j, ⟪a, p j⟫ * ⟪a, f j⟫ := by
  have hF' : f 0 = -(f 1 + f 2 + f 3) := by
    rw [Fin.sum_univ_four] at hF
    rw [eq_neg_iff_add_eq_zero, ← hF]; abel
  have F0 : f 0 0 = -(f 1 0 + f 2 0 + f 3 0) := by rw [hF']; simp
  have F1 : f 0 1 = -(f 1 1 + f 2 1 + f 3 1) := by rw [hF']; simp
  have hs1 : cross2 (f 0) (f 1) = cross2 (f 1) (f 2) + cross2 (f 1) (f 3) := by
    unfold cross2; rw [F0, F1]; ring
  have hs3 : cross2 (f 3) (f 0) = cross2 (f 1) (f 3) + cross2 (f 2) (f 3) := by
    unfold cross2; rw [F0, F1]; ring
  have t1 := virial_term_nonneg (p 0) (p 1) (p 2) (f 0) (f 1) (f 2) _ h12
    (fun h => ⟨by linarith, h⟩) (hout 0 1) (hout 0 2) (hout 1 0) (hout 1 2) (hout 2 0) (hout 2 1)
  have t2 := virial_term_nonneg (p 0) (p 1) (p 3) (f 0) (f 1) (f 3) _ h13
    (fun h => ⟨by linarith, h⟩) (hout 0 1) (hout 0 3) (hout 1 0) (hout 1 3) (hout 3 0) (hout 3 1)
  have t3 := virial_term_nonneg (p 2) (p 3) (p 0) (f 2) (f 3) (f 0) _ h23
    (fun h => ⟨h, by linarith⟩) (hout 2 3) (hout 2 0) (hout 3 2) (hout 3 0) (hout 0 2) (hout 0 3)
  have e3 : cross2 (p 3 - p 2) (p 0 - p 2) = cross2 (p 2 - p 0) (p 3 - p 0) := by
    simp only [cross2, PiLp.sub_apply]; ring
  rw [e3] at t3
  have hdet : 0 ≤ (∑ j, p j 0 * f j 0) * (∑ j, p j 1 * f j 1)
      - (∑ j, p j 1 * f j 0) * (∑ j, p j 0 * f j 1) := by
    have : (∑ j, p j 0 * f j 0) * (∑ j, p j 1 * f j 1)
      - (∑ j, p j 1 * f j 0) * (∑ j, p j 0 * f j 1) =
      cross2 (p 1 - p 0) (p 2 - p 0) * cross2 (f 1) (f 2)
      + cross2 (p 1 - p 0) (p 3 - p 0) * cross2 (f 1) (f 3)
      + cross2 (p 2 - p 0) (p 3 - p 0) * cross2 (f 2) (f 3) := by
      simp only [Fin.sum_univ_four, cross2, PiLp.sub_apply]
      rw [F0, F1]; ring
    rw [this]; linarith
  have hsym : ∑ j, p j 1 * f j 0 = ∑ j, p j 0 * f j 1 := by
    have h := hT
    simp only [Fin.sum_univ_four, cross2] at h
    simp only [Fin.sum_univ_four]
    linarith
  rw [hsym, ← sq] at hdet
  have hF0 : ∑ j, f j 0 = 0 := by
    have := congrArg (fun v : ℝ² => v 0) hF
    simpa [PiLp.add_apply, Finset.sum_apply] using this
  have hF1 : ∑ j, f j 1 = 0 := by
    have := congrArg (fun v : ℝ² => v 1) hF
    simpa [PiLp.add_apply, Finset.sum_apply] using this
  have htr : 0 ≤ (∑ j, p j 0 * f j 0) + (∑ j, p j 1 * f j 1) := by
    have o0 := hout 0 0
    have o1 := hout 1 0
    have o2 := hout 2 0
    have o3 := hout 3 0
    simp only [PiLp.inner_apply, Fin.sum_univ_two, PiLp.sub_apply, RCLike.inner_apply,
      conj_trivial] at o0 o1 o2 o3
    simp only [Fin.sum_univ_four] at hF0 hF1 ⊢
    have e0 : (p 0).ofLp 0 * ((f 0).ofLp 0 + (f 1).ofLp 0 + (f 2).ofLp 0 + (f 3).ofLp 0) = 0 := by
      rw [hF0]; ring
    have e1 : (p 0).ofLp 1 * ((f 0).ofLp 1 + (f 1).ofLp 1 + (f 2).ofLp 1 + (f 3).ofLp 1) = 0 := by
      rw [hF1]; ring
    linarith
  have key := virial_psd2 _ _ _ (a 0) (a 1) htr hdet
  have e : ∑ j, ⟪a, p j⟫ * ⟪a, f j⟫ = a 0 ^ 2 * (∑ j, p j 0 * f j 0)
      + 2 * a 0 * a 1 * (∑ j, p j 0 * f j 1) + a 1 ^ 2 * (∑ j, p j 1 * f j 1) := by
    simp only [PiLp.inner_apply, Fin.sum_univ_two, Fin.sum_univ_four, RCLike.inner_apply,
      conj_trivial]
    have hs := hsym
    simp only [Fin.sum_univ_four] at hs
    linear_combination (a 0 * a 1) * hs
  rw [e]; exact key

lemma virial_tri (x y z : ℝ²) :
    (0 ≤ cross2 x y ∧ 0 ≤ cross2 y z ∧ 0 ≤ cross2 x z) ∨
    (0 ≤ cross2 x z ∧ 0 ≤ cross2 z y ∧ 0 ≤ cross2 x y) ∨
    (0 ≤ cross2 y x ∧ 0 ≤ cross2 x z ∧ 0 ≤ cross2 y z) ∨
    (0 ≤ cross2 y z ∧ 0 ≤ cross2 z x ∧ 0 ≤ cross2 y x) ∨
    (0 ≤ cross2 z x ∧ 0 ≤ cross2 x y ∧ 0 ≤ cross2 z y) ∨
    (0 ≤ cross2 z y ∧ 0 ≤ cross2 y x ∧ 0 ≤ cross2 z x) ∨
    (0 < cross2 x y ∧ 0 < cross2 y z ∧ 0 < cross2 z x) ∨
    (cross2 x y < 0 ∧ cross2 y z < 0 ∧ cross2 z x < 0) := by
  have e1 : cross2 y x = - cross2 x y := by unfold cross2; ring
  have e2 : cross2 z y = - cross2 y z := by unfold cross2; ring
  have e3 : cross2 z x = - cross2 x z := by unfold cross2; ring
  rcases lt_trichotomy (cross2 x y) 0 with a | a | a <;>
  rcases lt_trichotomy (cross2 y z) 0 with b | b | b <;>
  rcases lt_trichotomy (cross2 z x) 0 with c | c | c <;>
  first
  | (refine Or.inl ⟨?_, ?_, ?_⟩ <;> linarith)
  | (refine Or.inr (Or.inl ⟨?_, ?_, ?_⟩) <;> linarith)
  | (refine Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_⟩)) <;> linarith)
  | (refine Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_⟩))) <;> linarith)
  | (refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_⟩)))) <;> linarith)
  | (refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_⟩))))) <;> linarith)
  | (refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_⟩)))))) <;> linarith)
  | (refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩)))))) <;> linarith)

/-- (G): some ordering a, b, c of three distinct indices has all pairwise crosses nonnegative. -/
def GoodTriple (f : Fin 4 → ℝ²) : Prop :=
  ∃ a b c : Fin 4, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
    0 ≤ cross2 (f a) (f b) ∧ 0 ≤ cross2 (f b) (f c) ∧ 0 ≤ cross2 (f a) (f c)

lemma virial_tri' (f : Fin 4 → ℝ²) (i j k : Fin 4) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    GoodTriple f ∨ (0 < cross2 (f i) (f j) ∧ 0 < cross2 (f j) (f k) ∧ 0 < cross2 (f k) (f i)) ∨
    (cross2 (f i) (f j) < 0 ∧ cross2 (f j) (f k) < 0 ∧ cross2 (f k) (f i) < 0) := by
  rcases virial_tri (f i) (f j) (f k) with h | h | h | h | h | h | h | h
  · exact Or.inl ⟨i, j, k, hij, hjk, hik, h⟩
  · exact Or.inl ⟨i, k, j, hik, hjk.symm, hij, h⟩
  · exact Or.inl ⟨j, i, k, hij.symm, hik, hjk, h⟩
  · exact Or.inl ⟨j, k, i, hjk, hik.symm, hij.symm, h⟩
  · exact Or.inl ⟨k, i, j, hik.symm, hij, hjk.symm, h⟩
  · exact Or.inl ⟨k, j, i, hjk.symm, hij.symm, hik.symm, h⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem good_triple (f : Fin 4 → ℝ²) : GoodTriple f := by
  have anti : ∀ x y : ℝ², cross2 y x = - cross2 x y := by intro x y; unfold cross2; ring
  have a1 := anti (f 0) (f 1)
  have a2 := anti (f 0) (f 2)
  have a3 := anti (f 0) (f 3)
  have a4 := anti (f 1) (f 2)
  have a5 := anti (f 1) (f 3)
  have a6 := anti (f 2) (f 3)
  rcases virial_tri' f 0 1 2 (by decide) (by decide) (by decide) with h1 | h1 | h1 <;>
  rcases virial_tri' f 0 1 3 (by decide) (by decide) (by decide) with h2 | h2 | h2 <;>
  rcases virial_tri' f 0 2 3 (by decide) (by decide) (by decide) with h3 | h3 | h3 <;>
  rcases virial_tri' f 1 2 3 (by decide) (by decide) (by decide) with h4 | h4 | h4 <;>
  first
  | assumption
  | (exfalso; obtain ⟨_, _, _⟩ := h1; linarith)
  | (exfalso
     first
     | (obtain ⟨_, _, _⟩ := h1; obtain ⟨_, _, _⟩ := h2; obtain ⟨_, _, _⟩ := h3; linarith)
     | skip)

lemma virial_perm_of (a b c : Fin 4) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ∃ σ : Equiv.Perm (Fin 4), σ 1 = a ∧ σ 2 = b ∧ σ 3 = c := by
  revert a b c; decide +kernel

theorem virial_four (p f : Fin 4 → ℝ²)
    (hout : ∀ j k, ⟪f j, p k - p j⟫ ≤ 0)
    (hF : ∑ j, f j = 0) (hT : ∑ j, cross2 (p j) (f j) = 0) (a : ℝ²) :
    0 ≤ ∑ j, ⟪a, p j⟫ * ⟪a, f j⟫ := by
  obtain ⟨x, y, z, hxy, hyz, hxz, g1, g2, g3⟩ := good_triple f
  obtain ⟨σ, s1, s2, s3⟩ := virial_perm_of x y z hxy hyz hxz
  have := virial_good (p ∘ σ) (f ∘ σ) (fun j k => hout (σ j) (σ k))
    (by show ∑ j, f (σ j) = 0; rw [Equiv.sum_comp σ f]; exact hF)
    (by show ∑ j, cross2 (p (σ j)) (f (σ j)) = 0; rw [Equiv.sum_comp σ (fun j => cross2 (p j) (f j))]; exact hT)
    (by simp only [Function.comp, s1, s2]; exact g1)
    (by simp only [Function.comp, s2, s3]; exact g2)
    (by simp only [Function.comp, s1, s3]; exact g3) a
  simpa only [Function.comp, Equiv.sum_comp σ (fun j => ⟪a, p j⟫ * ⟪a, f j⟫)] using this

section Reduce
open Finset
section
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup E] [Module ℝ E]

lemma virial_shrink (lam ν : ι → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hz : ∀ j, lam j = 0 → ν j = 0) (hneg : ∃ j, ν j < 0) :
    ∃ t : ℝ, 0 < t ∧ (∀ i, 0 ≤ lam i + t * ν i) ∧
      (univ.filter (fun i => lam i + t * ν i ≠ 0)).card
        < (univ.filter (fun i => lam i ≠ 0)).card := by
  obtain ⟨j0, hj0⟩ := hneg
  have hne : (univ.filter (fun j => ν j < 0)).Nonempty := ⟨j0, by simpa using hj0⟩
  obtain ⟨j1, hj1, hmin⟩ := Finset.exists_min_image _ (fun j => lam j / -ν j) hne
  have hj1' : ν j1 < 0 := by simpa using hj1
  have hl1 : lam j1 ≠ 0 := fun h => by have := hz _ h; linarith
  have hl1p : 0 < lam j1 := lt_of_le_of_ne (hlam _) (Ne.symm hl1)
  have hnn : 0 < -ν j1 := by linarith
  refine ⟨lam j1 / -ν j1, div_pos hl1p hnn, ?_, ?_⟩
  · intro i
    by_cases hi : ν i < 0
    · have h := hmin i (by simpa using hi)
      have hni : 0 < -ν i := by linarith
      have : lam j1 / -ν j1 * -ν i ≤ lam i := by
        have := (le_div_iff₀ hni).mp h
        linarith
      nlinarith
    · have : 0 ≤ ν i := not_lt.mp hi
      have : 0 ≤ lam j1 / -ν j1 * ν i := mul_nonneg (div_pos hl1p hnn).le this
      linarith [hlam i]
  · apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨j1, by simpa using hl1, ?_⟩
      have : lam j1 / -ν j1 * ν j1 = - lam j1 := by
        have : ν j1 ≠ 0 := hj1'.ne
        field_simp
      simp [this]
    · intro i hi
      simp only [mem_filter, mem_univ, true_and] at hi ⊢
      intro h0
      apply hi
      simp [h0, hz i h0]
end

section
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup E] [Module ℝ E]

lemma virial_comb_sum (A : ι → E) (c lam ν : ι → ℝ) (t : ℝ) :
    ∑ i, (lam i + t * ν i) • A i = ∑ i, lam i • A i + t • ∑ i, ν i • A i ∧
    ∑ i, (lam i + t * ν i) * c i = ∑ i, lam i * c i + t * ∑ i, ν i * c i := by
  constructor
  · simp [add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]
  · simp [add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]

lemma virial_step_main (A : ι → E) (c lam ν : ι → ℝ) (j₀ : ι)
    (IH : ∀ f : ι → ℝ, (∀ i, 0 ≤ f i) → ∑ i, f i • A i = 0 →
      (univ.filter (fun i => f i ≠ 0)).card < (univ.filter (fun i => lam i ≠ 0)).card →
      0 ≤ ∑ i, f i * c i)
    (hlam : ∀ i, 0 ≤ lam i) (hA : ∑ i, lam i • A i = 0)
    (hν : ∑ i, ν i • A i = 0) (hz : ∀ j, lam j = 0 → ν j = 0)
    (hj0 : lam j₀ ≠ 0) (hνj0 : ν j₀ = 0) (hne : ∃ j, ν j ≠ 0) :
    0 ≤ ∑ i, lam i * c i := by
  -- case B: ν ≤ 0 with a negative entry
  have caseB : ∀ ν : ι → ℝ, ∑ i, ν i • A i = 0 → (∀ j, lam j = 0 → ν j = 0) →
      ν j₀ = 0 → (∃ j, ν j < 0) → (∀ j, ν j ≤ 0) → 0 ≤ ∑ i, lam i * c i := by
    intro ν hν hz hνj0 hneg hle
    obtain ⟨t, ht, hnn, hlt⟩ := virial_shrink lam ν hlam hz hneg
    obtain ⟨h1, h2⟩ := virial_comb_sum A c lam ν t
    have hP := IH (fun i => lam i + t * ν i) hnn (by rw [h1, hA, hν]; simp) hlt
    have hM := IH (fun i => -ν i) (fun i => by simpa using hle i)
      (by simp [Finset.sum_neg_distrib, hν]) (by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨j₀, by simpa using hj0, by simp [hνj0]⟩
        · intro i hi
          simp only [mem_filter, mem_univ, true_and, neg_ne_zero] at hi ⊢
          intro h0
          exact hi (hz i h0))
    simp only [neg_mul, Finset.sum_neg_distrib] at hM
    rw [h2] at hP
    nlinarith [mul_nonneg ht.le hM]
  by_cases hneg : ∃ j, ν j < 0
  · by_cases hpos : ∃ j, 0 < ν j
    · obtain ⟨t, ht, hnn, hlt⟩ := virial_shrink lam ν hlam hz hneg
      obtain ⟨t', ht', hnn', hlt'⟩ := virial_shrink lam (fun i => -ν i) hlam
        (fun j h => by simpa using hz j h) (by
          obtain ⟨j, hj⟩ := hpos; exact ⟨j, by simpa using hj⟩)
      obtain ⟨h1, h2⟩ := virial_comb_sum A c lam ν t
      obtain ⟨h1', h2'⟩ := virial_comb_sum A c lam (fun i => -ν i) t'
      have hP := IH _ hnn (by rw [h1, hA, hν]; simp) hlt
      have hM := IH _ hnn' (by rw [h1', hA]; simp [Finset.sum_neg_distrib, hν]) hlt'
      rw [h2] at hP
      rw [h2'] at hM
      simp only [neg_mul, Finset.sum_neg_distrib] at hM
      have : 0 ≤ (t + t') * ∑ i, lam i * c i := by nlinarith [mul_nonneg ht'.le hP, mul_nonneg ht.le hM]
      exact (mul_nonneg_iff_of_pos_left (by positivity)).mp this
    · exact caseB ν hν hz hνj0 hneg (fun j => not_lt.mp (fun h => hpos ⟨j, h⟩))
  · obtain ⟨j, hj⟩ := hne
    have hpos : 0 < ν j := lt_of_le_of_ne (not_lt.mp (fun h => hneg ⟨j, h⟩)) (Ne.symm hj)
    exact caseB (fun i => -ν i) (by simp [Finset.sum_neg_distrib, hν])
      (fun j h => by simpa using hz j h) (by simp [hνj0]) ⟨j, by simpa using hpos⟩
      (fun j => by simpa using not_lt.mp (fun h => hneg ⟨j, h⟩))

end

theorem nonneg_of_small_support {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (A : ι → E) (c : ι → ℝ)
    (h : ∀ μ : ι → ℝ, (∀ i, 0 ≤ μ i) → ∑ i, μ i • A i = 0 →
      (Finset.univ.filter (fun i => μ i ≠ 0)).card ≤ Module.finrank ℝ E + 1 → 0 ≤ ∑ i, μ i * c i)
    (lam : ι → ℝ) (hlam : ∀ i, 0 ≤ lam i) (hA : ∑ i, lam i • A i = 0) :
    0 ≤ ∑ i, lam i * c i := by
  suffices H : ∀ n : ℕ, ∀ lam : ι → ℝ, (∀ i, 0 ≤ lam i) → ∑ i, lam i • A i = 0 →
      (univ.filter (fun i => lam i ≠ 0)).card ≤ n → 0 ≤ ∑ i, lam i * c i from
    H _ lam hlam hA le_rfl
  intro n
  induction n with
  | zero =>
    intro lam hlam hA hn
    exact h lam hlam hA (by omega)
  | succ n ih =>
    intro lam hlam hA hn
    by_cases hs : (univ.filter (fun i => lam i ≠ 0)).card ≤ Module.finrank ℝ E + 1
    · exact h lam hlam hA hs
    rw [not_le] at hs
    have hpos : 0 < (univ.filter (fun i => lam i ≠ 0)).card := by omega
    obtain ⟨j₀, hj₀⟩ := Finset.card_pos.mp hpos
    have hj₀' : lam j₀ ≠ 0 := by simpa using hj₀
    set S := (univ.filter (fun i => lam i ≠ 0)).erase j₀ with hS
    have hcard : S.card = (univ.filter (fun i => lam i ≠ 0)).card - 1 :=
      Finset.card_erase_of_mem hj₀
    have hnli : ¬ LinearIndependent ℝ (fun j : S => A j) := by
      intro hli
      have := hli.fintype_card_le_finrank
      simp only [Fintype.card_coe] at this
      omega
    rw [Fintype.not_linearIndependent_iff] at hnli
    obtain ⟨g, hg, i0, hi0⟩ := hnli
    classical
    let ν : ι → ℝ := fun j => if hj : j ∈ S then g ⟨j, hj⟩ else 0
    have hνsum : ∑ i, ν i • A i = 0 := by
      rw [← Finset.sum_subset (Finset.subset_univ S)]
      · rw [← hg, ← Finset.sum_coe_sort S]
        apply Finset.sum_congr rfl
        intro x _
        simp [ν]
      · intro x _ hx
        simp [ν, hx]
    have hνS : ∀ j, j ∉ S → ν j = 0 := fun j hj => by simp [ν, hj]
    have hz : ∀ j, lam j = 0 → ν j = 0 := by
      intro j hj
      apply hνS
      simp [hS, hj]
    have hνj0 : ν j₀ = 0 := hνS _ (by simp [hS])
    have hne : ∃ j, ν j ≠ 0 := ⟨i0, by simpa [ν] using hi0⟩
    exact virial_step_main A c lam ν j₀
      (fun f hf hfA hlt => ih f hf hfA (by omega)) hlam hA hνsum hz hj₀' hνj0 hne

end Reduce

section Final
open Finset

lemma virial_exists_reindex {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : ι → ℝ)
    (hne : (univ.filter (fun i => μ i ≠ 0)).Nonempty)
    (hc : (univ.filter (fun i => μ i ≠ 0)).card ≤ 4) :
    ∃ (e : Fin 4 → ι) (w : Fin 4 → ℝ), (∀ k, w k = 0 ∨ w k = μ (e k)) ∧
      ∀ (M : Type) [AddCommMonoid M] [Module ℝ M] (g : ι → M),
        ∑ j, μ j • g j = ∑ k, w k • g (e k) := by
  set s := univ.filter (fun i => μ i ≠ 0) with hs
  obtain ⟨j₀, hj₀⟩ := hne
  set m := s.card with hm
  let σ : Fin m ≃ s := (s.equivFin).symm
  let e : Fin 4 → ι := fun k => if h : k.val < m then (σ ⟨k.val, h⟩ : ι) else j₀
  let w : Fin 4 → ℝ := fun k => if k.val < m then μ (e k) else 0
  refine ⟨e, w, fun k => ?_, ?_⟩
  · by_cases h : k.val < m <;> simp [w, h]
  intro M _ _ g
  have h1 : ∑ j, μ j • g j = ∑ j ∈ s, μ j • g j := by
    symm
    apply Finset.sum_subset (Finset.subset_univ s)
    intro x _ hx
    have : μ x = 0 := by simpa [hs] using hx
    simp [this]
  have h2 : ∑ k, w k • g (e k) = ∑ k ∈ univ.filter (fun k : Fin 4 => k.val < m), μ (e k) • g (e k) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    by_cases h : k.val < m <;> simp [w, h]
  rw [h1, h2]
  symm
  apply Finset.sum_nbij e
  · intro k hk
    simp only [mem_filter, mem_univ, true_and] at hk
    simp only [e, hk, dite_true]
    exact (σ ⟨k.val, hk⟩).2
  · intro a ha b hb hab
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
    simp only [e, ha, hb, dite_true] at hab
    have := σ.injective (Subtype.ext hab)
    exact Fin.ext (by simpa using this)
  · intro x hx
    have hx' : x ∈ s := hx
    refine ⟨⟨(σ.symm ⟨x, hx'⟩).val, by have := (σ.symm ⟨x, hx'⟩).isLt; omega⟩, ?_, ?_⟩
    · simp [(σ.symm ⟨x, hx'⟩).isLt]
    · have hlt := (σ.symm ⟨x, hx'⟩).isLt
      simp [e, hlt]
  · intro k _; rfl

/-- Lemma V(a), finite form. -/
theorem virial_psd {ι : Type*} [Fintype ι] (p n : ι → ℝ²) (lam : ι → ℝ) (hlam : ∀ j, 0 ≤ lam j)
    (hout : ∀ j k, ⟪n j, p k - p j⟫ ≤ 0)
    (hF : ∑ j, lam j • n j = 0) (hT : ∑ j, lam j * cross2 (p j) (n j) = 0) (a : ℝ²) :
    0 ≤ ∑ j, lam j * (⟪a, p j⟫ * ⟪a, n j⟫) := by
  classical
  have hfin : Module.finrank ℝ (ℝ² × ℝ) + 1 = 4 := by
    simp [Module.finrank_prod]
  refine nonneg_of_small_support (fun j => (n j, cross2 (p j) (n j)))
    (fun j => ⟪a, p j⟫ * ⟪a, n j⟫) ?_ lam hlam ?_
  · intro μ hμ hA hcard
    rw [hfin] at hcard
    by_cases hne : (univ.filter (fun i => μ i ≠ 0)).Nonempty
    · obtain ⟨e, w, hw, hsum⟩ := virial_exists_reindex μ hne hcard
      have hA1 : ∑ j, μ j • n j = 0 := by
        have := congrArg Prod.fst hA
        simpa [Prod.fst_sum] using this
      have hA2 : ∑ j, μ j * cross2 (p j) (n j) = 0 := by
        have := congrArg Prod.snd hA
        simpa [Prod.snd_sum] using this
      have hw0 : ∀ k, 0 ≤ w k := fun k => by rcases hw k with h | h <;> simp [h, hμ]
      have s1 := hsum ℝ² n
      have s2 := hsum ℝ (fun j => cross2 (p j) (n j))
      have s3 := hsum ℝ (fun j => ⟪a, p j⟫ * ⟪a, n j⟫)
      simp only [smul_eq_mul] at s2 s3
      have := virial_four (fun k => p (e k)) (fun k => w k • n (e k))
        (fun j k => by
          simp only [inner_smul_left, conj_trivial]
          exact mul_nonpos_of_nonneg_of_nonpos (hw0 j) (hout _ _))
        (by rw [← s1]; exact hA1)
        (by simp only [cross2_smul_right]; rw [← s2]; exact hA2) a
      simp only [inner_smul_right] at this
      rw [s3]
      refine le_of_le_of_eq this (Finset.sum_congr rfl fun k _ => by ring)
    · rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hne
      apply le_of_eq
      symm
      apply Finset.sum_eq_zero
      intro i _
      have := hne (Finset.mem_univ i)
      simp at this
      simp [this]
  · apply Prod.ext
    · simpa [Prod.fst_sum] using hF
    · simpa [Prod.snd_sum] using hT

/-- Lemma V(a) for a convex set: each n j is an outward normal of S at p j ∈ S. -/
theorem virial_psd_convex {ι : Type*} [Fintype ι] (S : Set ℝ²) (p n : ι → ℝ²) (lam : ι → ℝ)
    (hlam : ∀ j, 0 ≤ lam j) (hp : ∀ j, p j ∈ S) (hn : ∀ j, ∀ y ∈ S, ⟪n j, y - p j⟫ ≤ 0)
    (hF : ∑ j, lam j • n j = 0) (hT : ∑ j, lam j * cross2 (p j) (n j) = 0) (a : ℝ²) :
    0 ≤ ∑ j, lam j * (⟪a, p j⟫ * ⟪a, n j⟫) :=
  virial_psd p n lam hlam (fun j k => hn j _ (hp k)) hF hT a

end Final

end Minimality
