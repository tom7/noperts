module

public import Minimality.CaseC20Sp

@[expose] public section

/-!
# Type 20: the pentagon test `pent1` (sp20d, Theorem F20)
View `u_tA`, sector tilt `w = (0, θ, -1)`, rim `(v, m1-, m2-, xb, m1+)` (labels `(5,3,4,6,0)`),
`σ = -1`, hidden `xa`, `m2+`.  Hypotheses `A1 ≤ 0`, `0 < θ`, `θ h+ < 1 - t+`, `θ k- < s-`.
-/

namespace Minimality.CaseC20
open Finset Filter Minimality.CaseC09 Minimality.CaseC18
open scoped RealInnerProductSpace Topology

namespace Shape20
/-- the tilt of `pent1` -/
def w_T1 (_ : Shape20) (θ : ℝ) : C3 := ⟨0, θ, -1⟩
end Shape20

theorem pent1_cyc (S : Shape20) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ * S.hp < 1 - S.tp) (hθ2 : θ * S.km < S.sm)
    (hA : S.hm*S.tp - S.hm + S.hp*S.tm ≤ 0) :
    Cyc5 (-1) S.u_tA (S.w_T1 θ) (⟨0, 0, 0⟩ : C3) ⟨S.tm, 0, -S.hm⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ ⟨S.tp, 0, S.hp⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  have hw : 0 < S.tm * (S.sm - θ * S.km) := mul_pos htm (by linarith)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tA, Shape20.w_T1]
    rcases hA.lt_or_eq with h | h
    · left; linarith [mul_pos hsm (neg_pos.2 h)]
    · right; refine ⟨by linear_combination (S.sm) * h, ?_⟩; linarith [hw]
  · simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tA, Shape20.w_T1]
    rcases hA.lt_or_eq with h | h
    · left; linarith
    · right; refine ⟨by linear_combination h, ?_⟩; linarith [htm]
  · simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tA, Shape20.w_T1]
    right; refine ⟨by ring, ?_⟩; linarith [mul_pos hθ0 (mul_pos hhm htp), mul_pos hθ0 (mul_pos hhp htm)]
  · simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tA, Shape20.w_T1]
    left; linarith [mul_pos htp1 rm, mul_pos (mul_pos htp1 htm) hkm, mul_pos (mul_pos htm hsm1) hhp]
  · simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tA, Shape20.w_T1]
    left; linarith [mul_pos (mul_pos hsm hhp) htm1, mul_pos (mul_pos hsm hhm) htp1]
  · simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tA, Shape20.w_T1]
    rcases hA.lt_or_eq with h | h
    · left; linarith [mul_pos hsm (neg_pos.2 h)]
    · right; refine ⟨by linear_combination (S.sm) * h, ?_⟩; linarith [hw]
  · simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tA, Shape20.w_T1]
    left; linarith [mul_pos htp1 hkm, mul_pos hsm1 hhp]
  · simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tA, Shape20.w_T1]
    left; linarith [mul_pos htp1 hkm]
  · simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tA, Shape20.w_T1]
    left; linarith [mul_pos htp1 rm, mul_pos (mul_pos htp1 htm) hkm, mul_pos (mul_pos hsm1 htm) hhp]
  · simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tA, Shape20.w_T1]
    left; linarith [hhp]
  · simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tA, Shape20.w_T1]
    left; linarith [mul_pos hhm htp1, mul_pos hhp htm1]
  · simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tA, Shape20.w_T1]
    left; linarith [mul_pos htp1 hkm, mul_pos hhp hsm1]
  · simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tA, Shape20.w_T1]
    right; refine ⟨by ring, ?_⟩; linarith [mul_pos hθ0 (mul_pos hhm htp), mul_pos hθ0 (mul_pos hhp htm)]
  · simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tA, Shape20.w_T1]
    left; linarith [mul_pos hsm hhp]
  · simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tA, Shape20.w_T1]
    left; linarith [hhp]

theorem pent1_rest1 (S : Shape20) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ * S.hp < 1 - S.tp) (hθ2 : θ * S.km < S.sm) :
    Rest5 (-1) S.u_tA (S.w_T1 θ) (⟨0, 0, 0⟩ : C3) ⟨S.tm, 0, -S.hm⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ ⟨S.tp, 0, S.hp⟩
      ⟨1, 0, 0⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tA, Shape20.w_T1]
    right; refine ⟨by ring, ?_⟩; linarith [mul_pos hθ0 hhm]
  · simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tA, Shape20.w_T1]
    left; linarith [mul_pos (mul_pos htp1 hsm) hhm, mul_pos (mul_pos hsm htm1) hhp]
  · simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tA, Shape20.w_T1]
    left; linarith [mul_pos htp1 hkm, mul_pos hsm1 hhp]
  · simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tA, Shape20.w_T1]
    right; refine ⟨by ring, ?_⟩; linarith [hθ1]
  · simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tA, Shape20.w_T1]
    right; refine ⟨by ring, ?_⟩; linarith [mul_pos hθ0 hhp]

theorem pent1_rest2 (S : Shape20) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ * S.hp < 1 - S.tp) (hθ2 : θ * S.km < S.sm)
    (hA : S.hm*S.tp - S.hm + S.hp*S.tm ≤ 0) :
    Rest5 (-1) S.u_tA (S.w_T1 θ) (⟨0, 0, 0⟩ : C3) ⟨S.tm, 0, -S.hm⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ ⟨S.tp, 0, S.hp⟩
      ⟨0, S.sp, S.kp⟩ := by
  have htp := S.tp_pos; have htm := S.tm_pos; have hsp := S.sp_pos; have hsm := S.sm_pos
  have hhp := S.hp_pos; have hhm := S.hm_pos; have hkp := S.kp_pos; have hkm := S.km_pos
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have htm1 : 0 < 1 - S.tm := sub_pos.2 S.tm_lt
  have hsp1 : 0 < 1 - S.sp := sub_pos.2 S.sp_lt
  have hsm1 : 0 < 1 - S.sm := sub_pos.2 S.sm_lt
  have rp : 0 < S.hp * (1 - S.sp) - S.kp * (1 - S.tp) := sub_pos.2 S.roof_p'
  have rm : 0 < S.km * (1 - S.tm) - S.hm * (1 - S.sm) := sub_pos.2 S.roof_m'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tA, Shape20.w_T1]
    rcases hA.lt_or_eq with h | h
    · left; linarith [mul_pos hsp (neg_pos.2 h)]
    · right; refine ⟨by linear_combination (S.sp) * h, ?_⟩
      linarith [mul_pos htm hsp, mul_pos (mul_pos htm hkp) hθ0]
  · simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tA, Shape20.w_T1]
    rcases le_total S.sp S.sm with hs | hs
    · have := mul_nonneg (neg_nonneg.2 hA) (sub_nonneg.2 hs)
      left; linarith [mul_pos (mul_pos htp1 hsm) hkp, mul_pos (mul_pos htp1 hsp) hkm]
    · left; linarith [mul_pos (mul_pos htp1 hsm) hkp, mul_pos (mul_pos htp1 hsp) rm,
        mul_pos (mul_pos (mul_pos htp1 hsp) htm) hkm, mul_pos (mul_pos (mul_pos htp1 hsm) hhm) hsp1,
        mul_nonneg (mul_nonneg htm.le hhp.le) (sub_nonneg.2 hs)]
  · simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tA, Shape20.w_T1]
    left; linarith [mul_pos (mul_pos htp1 hsm1) hkp, mul_pos (mul_pos htp1 hkm) hsp1]
  · simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tA, Shape20.w_T1]
    left; linarith [rp]
  · simp only [CaseC09.ST, Dc, C3.sub, Shape20.u_tA, Shape20.w_T1]
    left; linarith [mul_pos hhp hsp]

/-- The pentagon test at the sector `(0, θ, -1)` of the view `u_tA`. -/
theorem Frame20.pent1 {x : Fin 7 → ℝ³} (F : Frame20 x) (θ : ℝ) (hθ0 : 0 < θ)
    (hθ1 : θ * F.S.hp < 1 - F.S.tp) (hθ2 : θ * F.S.km < F.S.sm)
    (hA : F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm ≤ 0)
    (hD1 : F.dep F.S.u_tA 3 < F.dep F.S.u_tA 5) (hD2 : F.dep F.S.u_tA 6 < F.dep F.S.u_tA 0)
    (hD3 : F.dep F.S.u_tA 4 < F.dep F.S.u_tA 6 ∨ F.dep F.S.u_tA 4 < F.dep F.S.u_tA 3) :
    IsRupert (Finset.univ.image x) := by
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have h0 : F.dep F.S.u_tA 5 < F.dep F.S.u_tA 0 ∨ F.dep F.S.u_tA 5 < F.dep F.S.u_tA 3 ∨
      F.dep F.S.u_tA 4 < F.dep F.S.u_tA 3 ∨ F.dep F.S.u_tA 4 < F.dep F.S.u_tA 6 := by
    rcases hD3 with h | h
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))
  have h1 : F.dep F.S.u_tA 3 < F.dep F.S.u_tA 5 ∨ F.dep F.S.u_tA 3 < F.dep F.S.u_tA 4 ∨
      F.dep F.S.u_tA 6 < F.dep F.S.u_tA 4 ∨ F.dep F.S.u_tA 6 < F.dep F.S.u_tA 0 := Or.inl hD1
  have h2 : F.dep F.S.u_tA 4 < F.dep F.S.u_tA 3 ∨ F.dep F.S.u_tA 4 < F.dep F.S.u_tA 6 ∨
      F.dep F.S.u_tA 0 < F.dep F.S.u_tA 6 ∨ F.dep F.S.u_tA 0 < F.dep F.S.u_tA 5 := by
    rcases hD3 with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
  have h3 : F.dep F.S.u_tA 6 < F.dep F.S.u_tA 4 ∨ F.dep F.S.u_tA 6 < F.dep F.S.u_tA 0 ∨
      F.dep F.S.u_tA 5 < F.dep F.S.u_tA 0 ∨ F.dep F.S.u_tA 5 < F.dep F.S.u_tA 3 :=
    Or.inr (Or.inl hD2)
  have h4 : F.dep F.S.u_tA 0 < F.dep F.S.u_tA 6 ∨ F.dep F.S.u_tA 0 < F.dep F.S.u_tA 5 ∨
      F.dep F.S.u_tA 3 < F.dep F.S.u_tA 5 ∨ F.dep F.S.u_tA 3 < F.dep F.S.u_tA 4 :=
    Or.inr (Or.inr (Or.inl hD1))
  refine F.toFrame7.rim5p 5 3 4 6 0 _ _ _ _ _ (F.ptC_5) (F.ptC_3) (F.ptC_4) (F.ptC_6) (F.ptC_0) (-1) (Or.inr rfl)
    F.S.u_tA (F.S.w_T1 θ) (Or.inl (by simp only [Shape20.u_tA]; intro h; linarith [htp1, h]))
    (pent1_cyc F.S θ hθ0 hθ1 hθ2 hA) ?_ ?_ ?_ ?_ ?_ ?_
  · intro j' h0 h1 h2 h3 h4
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h4
    · rw [F.ptC_1]; exact pent1_rest1 F.S θ hθ0 hθ1 hθ2
    · rw [F.ptC_2]; exact pent1_rest2 F.S θ hθ0 hθ1 hθ2 hA
    · exact absurd rfl h1
    · exact absurd rfl h2
    · exact absurd rfl h0
    · exact absurd rfl h3
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using h0
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using h1
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using h2
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using h3
  · simpa only [Frame20.dep, F.ptC_0, F.ptC_1, F.ptC_2, F.ptC_3, F.ptC_4, F.ptC_5, F.ptC_6] using h4

theorem exists_theta (S : Shape20) : ∃ θ : ℝ, 0 < θ ∧ θ * S.hp < 1 - S.tp ∧ θ * S.km < S.sm := by
  have htp1 : 0 < 1 - S.tp := sub_pos.2 S.tp_lt
  have hD : 0 < S.hp * S.sm + (1 - S.tp) * S.km :=
    add_pos (mul_pos S.hp_pos S.sm_pos) (mul_pos htp1 S.km_pos)
  refine ⟨(1 - S.tp) * S.sm / (S.hp * S.sm + (1 - S.tp) * S.km), div_pos (mul_pos htp1 S.sm_pos) hD, ?_, ?_⟩
  · rw [div_mul_eq_mul_div, div_lt_iff₀ hD]
    nlinarith [mul_pos (mul_pos htp1 htp1) S.km_pos]
  · rw [div_mul_eq_mul_div, div_lt_iff₀ hD]
    nlinarith [mul_pos (mul_pos S.hp_pos S.sm_pos) S.sm_pos]

/-- **Theorem F20** (face `A12 = A11`): Rupert, except on `m1' = {A1 = 0, 0 < p ≤ q}`. -/
theorem Frame20.faceA11 {x : Fin 7 → ℝ³} (F : Frame20 x) (h : F.a12 = F.a11)
    (hn : ¬ (F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm = 0 ∧
      0 < (1 - F.S.tp)*(1 - F.S.tm)*F.a12 - F.gg*F.S.hp*F.S.hm ∧
      (1 - F.S.tp)*(1 - F.S.tm)*F.a12 - F.gg*F.S.hp*F.S.hm ≤
        (1 - F.S.tp)*(1 - F.S.sm)*F.a12 - F.gg*F.S.hp*F.S.km)) :
    IsRupert (Finset.univ.image x) := by
  have hga : 0 < F.a12 := F.A12_pos; have hde : 0 < F.gg := F.g_pos
  have htp := F.S.tp_pos; have htm := F.S.tm_pos; have hsp := F.S.sp_pos; have hsm := F.S.sm_pos
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have htp1 : 0 < 1 - F.S.tp := sub_pos.2 F.S.tp_lt
  have htm1 : 0 < 1 - F.S.tm := sub_pos.2 F.S.tm_lt
  have hsm1 : 0 < 1 - F.S.sm := sub_pos.2 F.S.sm_lt
  have rm : 0 < F.S.km * (1 - F.S.tm) - F.S.hm * (1 - F.S.sm) := sub_pos.2 F.S.roof_m'
  have d0 : F.dep F.S.u_tA 0 = -(1 - F.S.tp)*F.a12*F.S.tp + F.gg*F.S.hp*F.S.hp := by
    simp only [Frame20.dep, Frame20.GG_eq, F.ptC_0, Shape20.u_tA, ← h]; ring
  have d1 : F.dep F.S.u_tA 1 = -(1 - F.S.tp)*F.a12 := by
    simp only [Frame20.dep, Frame20.GG_eq, F.ptC_1, Shape20.u_tA, ← h]; ring
  have d3 : F.dep F.S.u_tA 3 = -(1 - F.S.tp)*F.a12*F.S.tm - F.gg*F.S.hp*F.S.hm := by
    simp only [Frame20.dep, Frame20.GG_eq, F.ptC_3, Shape20.u_tA, ← h]; ring
  have d4 : F.dep F.S.u_tA 4 = -(1 - F.S.tp)*F.a12*F.S.sm - F.gg*F.S.hp*F.S.km := by
    simp only [Frame20.dep, Frame20.GG_eq, F.ptC_4, Shape20.u_tA, ← h]; ring
  have d5 : F.dep F.S.u_tA 5 = 0 := by
    simp only [Frame20.dep, Frame20.GG_eq, F.ptC_5, Shape20.u_tA]; ring
  have d6 : F.dep F.S.u_tA 6 = -(1 - F.S.tp)*F.a12 := by
    simp only [Frame20.dep, Frame20.GG_eq, F.ptC_6, Shape20.u_tA, ← h]; ring
  have p1 := mul_pos (mul_pos htp1 hga) hsm
  have p2 := mul_pos (mul_pos hde hhp) hkm
  have p3 := mul_pos (mul_pos htp1 hga) htm
  have p4 := mul_pos (mul_pos hde hhp) hhm
  have F3a : F.dep F.S.u_tA 4 < F.dep F.S.u_tA 5 := by rw [d4, d5]; linarith
  have F3b : F.dep F.S.u_tA 3 < F.dep F.S.u_tA 5 := by rw [d3, d5]; linarith
  have F1 : F.dep F.S.u_tA 6 < F.dep F.S.u_tA 0 := by
    rw [d0, d6]; nlinarith [mul_pos (mul_pos htp1 htp1) hga, mul_pos (mul_pos hde hhp) hhp]
  rcases lt_or_ge 0 (F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm) with hA | hA
  · exact F.tA hA (Or.inr (Or.inr (Or.inr F3a))) (Or.inl F1)
  · obtain ⟨θ, hθ0, hθ1, hθ2⟩ := exists_theta F.S
    have hF2 : (F.dep F.S.u_tA 3 - F.dep F.S.u_tA 6 ≤ 0) → (0 ≤ F.dep F.S.u_tA 4 - F.dep F.S.u_tA 6) → False := by
      intro hP hQ
      rw [d3, d6] at hP; rw [d4, d6] at hQ
      have e1 := mul_nonneg (neg_nonneg.2 hP) hsm1.le
      have e2 := mul_nonneg hQ htm1.le
      have e3 := mul_pos (mul_pos hde hhp) rm
      nlinarith
    by_cases hq : F.dep F.S.u_tA 4 - F.dep F.S.u_tA 6 < 0
    · exact F.pent1 θ hθ0 hθ1 hθ2 hA F3b F1 (Or.inl (by linarith))
    · have hq' : 0 ≤ F.dep F.S.u_tA 4 - F.dep F.S.u_tA 6 := not_lt.1 hq
      have hp0 : 0 < F.dep F.S.u_tA 3 - F.dep F.S.u_tA 6 := by
        by_contra hc; exact hF2 (not_lt.1 hc) hq'
      by_cases hqp : F.dep F.S.u_tA 4 - F.dep F.S.u_tA 6 < F.dep F.S.u_tA 3 - F.dep F.S.u_tA 6
      · exact F.pent1 θ hθ0 hθ1 hθ2 hA F3b F1 (Or.inr (by linarith))
      · have hqp' : F.dep F.S.u_tA 3 - F.dep F.S.u_tA 6 ≤ F.dep F.S.u_tA 4 - F.dep F.S.u_tA 6 := not_lt.1 hqp
        rcases hA.lt_or_eq with hlt | heq
        · have eP : F.S.u_tP = F.S.u_tA := rfl
          refine F.tP (by linarith) (Or.inl ?_) (Or.inr (Or.inr (Or.inr ?_))) <;> rw [eP]
          · rw [d1]; linarith
          · linarith
        · exfalso
          refine hn ⟨heq, ?_, ?_⟩
          · rw [d3, d6] at hp0; linarith
          · rw [d3, d6, d4] at hqp'; linarith

/-- The R-image of `m1'`, written out: `a12 = a22 ∧ A1R = 0 ∧ 0 < pR ≤ qR`. -/
theorem Frame20.faceA22 {x : Fin 7 → ℝ³} (F : Frame20 x) (h : F.a12 = F.a22)
    (hn : ¬ (F.S.kp*F.S.sm - F.S.kp + F.S.km*F.S.sp = 0 ∧
      0 < (1 - F.S.sm)*(1 - F.S.sp)*F.a12 - F.gg*F.S.km*F.S.kp ∧
      (1 - F.S.sm)*(1 - F.S.sp)*F.a12 - F.gg*F.S.km*F.S.kp ≤
        (1 - F.S.sm)*(1 - F.S.tp)*F.a12 - F.gg*F.S.km*F.S.hp)) :
    IsRupert (Finset.univ.image x) := by
  have h12 : F.rFrame.a12 = F.a12 := by
    show ⟪x (rperm 1) - x (rperm 5), x (rperm 6) - x (rperm 5)⟫ = _
    show ⟪x 6 - x 5, x 1 - x 5⟫ = _
    exact real_inner_comm _ _
  have hg : F.rFrame.gg = F.gg := by
    show ⟪-F.e, -F.e⟫ = ⟪F.e, F.e⟫
    simp
  refine rupert_of_r (F.rFrame.faceA11 (by rw [h12]; exact h) ?_)
  simp only [rFrame_S, Shape20.swap, h12, hg]
  exact hn

/-- `CaseC20Special'` with the face disjuncts `m1`, `m2` replaced by the codimension-2 items
`m1'` (`a12 = a11 ∧ A1 = 0 ∧ 0 < p ≤ q`) and its `R`-image `m2'`. -/
def CaseC20Special'' (x : Fin 7 → ℝ³) : Prop :=
  ∃ F : Frame20 x,
    (F.a12 = F.a11 ∧ F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm = 0 ∧
      0 < (1 - F.S.tp)*(1 - F.S.tm)*F.a12 - F.gg*F.S.hp*F.S.hm ∧
      (1 - F.S.tp)*(1 - F.S.tm)*F.a12 - F.gg*F.S.hp*F.S.hm ≤
        (1 - F.S.tp)*(1 - F.S.sm)*F.a12 - F.gg*F.S.hp*F.S.km) ∨
    (F.a12 = F.a22 ∧ F.S.kp*F.S.sm - F.S.kp + F.S.km*F.S.sp = 0 ∧
      0 < (1 - F.S.sm)*(1 - F.S.sp)*F.a12 - F.gg*F.S.km*F.S.kp ∧
      (1 - F.S.sm)*(1 - F.S.sp)*F.a12 - F.gg*F.S.km*F.S.kp ≤
        (1 - F.S.sm)*(1 - F.S.tp)*F.a12 - F.gg*F.S.km*F.S.hp) ∨
    (-F.S.hm*F.S.sp*F.S.tp + F.S.hm*F.S.tp - F.S.hp*F.S.sp*F.S.tm + F.S.hp*F.S.tm - F.S.kp*F.S.tm = 0) ∨
    (-F.S.hm*F.S.sp - F.S.km*F.S.sp*F.S.tm + F.S.km*F.S.sp - F.S.kp*F.S.sm*F.S.tm + F.S.kp*F.S.sm = 0) ∨
    (F.S.hm*F.S.tp - F.S.hm + F.S.hp*F.S.tm = 0) ∨
    (F.S.km*F.S.sp + F.S.kp*F.S.sm - F.S.kp = 0) ∨
    ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.km*F.S.tm) * (F.a11 - F.a12) + (-F.S.hm*F.S.sm + F.S.hm + F.S.km*F.S.tm - F.S.km) * F.a12 = 0) ∨
    ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.hp*F.S.sp) * (F.a22 - F.a12) + (F.S.hp*F.S.sp - F.S.hp - F.S.kp*F.S.tp + F.S.kp) * F.a12 = 0) ∨
    ((-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * (F.a11 - F.a12) + (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * F.a12 + (-F.S.hm*F.S.hp) * F.gg = 0) ∨
    ((-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * (F.a11 - F.a12) + (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * F.a12 + (-F.S.hm*F.S.hp) * F.gg = 0) ∨
    ((-F.S.sm*F.S.sp*F.S.tp + F.S.sm*F.S.tp + F.S.sp*F.S.tp - F.S.tp) * F.a12 + (F.S.hp*F.S.km*F.S.sp - F.S.hp*F.S.km + F.S.km*F.S.kp) * F.gg = 0 ∧ (F.S.sm*F.S.sp - F.S.sm - F.S.sp + 1) * (F.a22 - F.a12) + (F.S.sm*F.S.sp - F.S.sm - F.S.sp + 1) * F.a12 + (-F.S.km*F.S.kp) * F.gg = 0) ∨
    ((-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * (F.a11 - F.a12) + (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * F.a12 + (-F.S.hm*F.S.hp) * F.gg = 0) ∨
    ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.hp*F.S.sp) * (F.a22 - F.a12) + (F.S.hp*F.S.sp - F.S.hp - F.S.kp*F.S.tp + F.S.kp) * F.a12 = 0) ∨
    ((-F.S.sm*F.S.tm*F.S.tp + F.S.sm*F.S.tm + F.S.sm*F.S.tp - F.S.sm) * F.a12 + (F.S.hm*F.S.hp + F.S.hp*F.S.km*F.S.tm - F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * (F.a11 - F.a12) + (F.S.tm*F.S.tp - F.S.tm - F.S.tp + 1) * F.a12 + (-F.S.hm*F.S.hp) * F.gg = 0) ∨
    (F.S.hm*F.S.sp - F.S.hm + F.S.km*F.S.sp*F.S.tm - F.S.km*F.S.sp - F.S.km*F.S.tm + F.S.km + F.S.kp*F.S.sm*F.S.tm - F.S.kp*F.S.sm = 0) ∨
    ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.hp*F.S.sp) * (F.a22 - F.a12) + (F.S.hp*F.S.sp - F.S.hp - F.S.kp*F.S.tp + F.S.kp) * F.a12 = 0) ∨
    ((-F.S.sm*F.S.sp*F.S.tp + F.S.sm*F.S.tp + F.S.sp*F.S.tp - F.S.tp) * F.a12 + (F.S.hp*F.S.km*F.S.sp - F.S.hp*F.S.km + F.S.km*F.S.kp) * F.gg = 0 ∧ (F.S.sm*F.S.sp - F.S.sm - F.S.sp + 1) * (F.a22 - F.a12) + (F.S.sm*F.S.sp - F.S.sm - F.S.sp + 1) * F.a12 + (-F.S.km*F.S.kp) * F.gg = 0) ∨
    (F.S.hm*F.S.sp*F.S.tp - F.S.hm*F.S.tp + F.S.hp*F.S.sp*F.S.tm - F.S.hp*F.S.sp - F.S.hp*F.S.tm + F.S.hp + F.S.kp*F.S.tm - F.S.kp = 0) ∨
    ((F.S.sm*F.S.tp - F.S.sm - F.S.tp + 1) * F.a12 + (-F.S.hp*F.S.km) * F.gg = 0 ∧ (F.S.km*F.S.tm) * (F.a11 - F.a12) + (-F.S.hm*F.S.sm + F.S.hm + F.S.km*F.S.tm - F.S.km) * F.a12 = 0)

theorem Frame20.isRupert_of_not_special'' {x : Fin 7 → ℝ³} (F : Frame20 x)
    (hx : Function.Injective x) (h : ¬ CaseC20Special'' x) :
    IsRupert (Finset.univ.image x) := by
  by_cases h1 : F.a12 = F.a11
  · refine F.faceA11 h1 fun hm => h ⟨F, Or.inl ⟨h1, hm⟩⟩
  by_cases h2 : F.a12 = F.a22
  · refine F.faceA22 h2 fun hm => h ⟨F, Or.inr (Or.inl ⟨h2, hm⟩)⟩
  refine F.isRupert_of_not_special' hx fun hs => h ?_
  obtain ⟨F', hF'⟩ := hs
  refine ⟨F', ?_⟩
  rcases hF' with m1 | m2 | hr
  · exact absurd m1 h1
  · exact absurd m2 h2
  · exact Or.inr (Or.inr hr)

end Minimality.CaseC20

end

