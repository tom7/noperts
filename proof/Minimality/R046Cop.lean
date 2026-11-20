module

public import Minimality.R012
public import Minimality.Q45Leaf
public import Minimality.CornerU
public import Minimality.DiagCross
public import Minimality.FaceChordFac
public import Minimality.SplitTie
public import Minimality.FiveRim
public import Minimality.Q45J0
public import Minimality.Q45Signs
public import Minimality.Q45Orient
public import Minimality.RimFromSigns
public import Minimality.Type24SAT.K24.Wire24

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace Topology
open Filter Finset
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT Minimality.RimFromSigns
open Minimality.T24.Q45

namespace Minimality.T24.R046
variable {x : Fin 7 → ℝ³}

theorem ev_inner_neg (n b d : ℝ³) (h : ⟪n, b⟫ < 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪n, b + ε • d⟫ < 0 := by
  have := eventually_pos_affine (A := -⟪n, b⟫) (B := -⟪n, d⟫) (Or.inl (by linarith))
  filter_upwards [this] with ε hε
  rw [inner_add_right, real_inner_smul_right]; linarith

theorem ev_inner_pos (n b d : ℝ³) (h : 0 < ⟪n, b⟫) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪n, b + ε • d⟫ := by
  have := eventually_pos_affine (A := ⟪n, b⟫) (B := ⟪n, d⟫) (Or.inl h)
  filter_upwards [this] with ε hε
  rw [inner_add_right, real_inner_smul_right]; linarith

theorem rim4_assemble (A B C D u : ℝ³) (s0 s1 s2 s3 : ℝ)
    (a0 : 0 < s0 * det3 (B - A) (C - A) u) (a0' : 0 < s0 * det3 (B - A) (D - A) u)
    (a1 : 0 < s1 * det3 (C - B) (D - B) u) (a1' : 0 < s1 * det3 (C - B) (A - B) u)
    (a2 : 0 < s2 * det3 (D - C) (A - C) u) (a2' : 0 < s2 * det3 (D - C) (B - C) u)
    (a3 : 0 < s3 * det3 (A - D) (B - D) u) (a3' : 0 < s3 * det3 (A - D) (C - D) u) :
    (0 < s0 * s1 ∧ 0 < s0 * s2 ∧ 0 < s0 * s3) ∧
    ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      0 < s0 * det3 (quad A B C D (i + 1) - quad A B C D i) (quad A B C D j - quad A B C D i) u := by
  have c01 : det3 (B - A) (C - A) u = det3 (C - B) (A - B) u := Minimality.det3_cycle_triangle A B C u
  have c12 : det3 (C - B) (D - B) u = det3 (D - C) (B - C) u := Minimality.det3_cycle_triangle B C D u
  have c23 : det3 (D - C) (A - C) u = det3 (A - D) (C - D) u := Minimality.det3_cycle_triangle C D A u
  have c30 : det3 (A - D) (B - D) u = det3 (B - A) (D - A) u := Minimality.det3_cycle_triangle D A B u
  have h01 : 0 < s0 * s1 := sign_prod a0 (by rw [c01]; exact a1')
  have h12 : 0 < s1 * s2 := sign_prod a1 (by rw [c12]; exact a2')
  have h23 : 0 < s2 * s3 := sign_prod a2 (by rw [c23]; exact a3')
  have h30 : 0 < s3 * s0 := sign_prod a3 (by rw [c30]; exact a0')
  have h02 : 0 < s0 * s2 := sign_transfer h01 h12
  have h03 : 0 < s0 * s3 := by rw [mul_comm]; exact h30
  refine ⟨⟨h01, h02, h03⟩, ?_⟩
  intro i j hj1 hj2
  fin_cases i <;> fin_cases j
  all_goals first
    | exact False.elim (hj1 rfl)
    | exact False.elim (hj2 rfl)
    | exact a0
    | exact a0'
    | exact sign_transfer h01 a1
    | exact sign_transfer h01 a1'
    | exact sign_transfer h02 a2
    | exact sign_transfer h02 a2'
    | exact sign_transfer h03 a3
    | exact sign_transfer h03 a3'

lemma quad_eq046 : ∀ i : ZMod 4, x (quad (4 : Fin 7) 0 5 3 i) = quad (x 4) (x 0) (x 5) (x 3) i := by
  intro i; fin_cases i <;> rfl

lemma ext_vertices046 (q : Fin 7) (hqS : q ∉ s0x_S24 4) (hqr : ∀ j : ZMod 4, q ≠ quad (4 : Fin 7) 0 5 3 j) :
    q = 1 ∨ q = 2 := by
  revert q; decide

lemma mid_vertices046 (q : Fin 7) (hqS : q ∈ s0x_S24 4) (hqr : ∀ j : ZMod 4, q ≠ quad (4 : Fin 7) 0 5 3 j) :
    q = 6 := by
  revert q; decide

lemma far_cand046 (m : ZMod 4) (hmS : quad (4 : Fin 7) 0 5 3 m ∉ s0x_S24 4) : m = 2 ∨ m = 3 := by
  revert m; decide

/-- Rim of the facet 0345 seen from outside on the circle of 046: signs to the rim of `(4,0,5,3)`. -/
theorem rim046 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hN4 : ⟪F.N 4, u⟫ = 0) (hN2 : ⟪F.N 2, u⟫ < 0)
    (hN3 : 0 < ⟪F.N 3, u⟫) (hN6 : ⟪F.N 6, u⟫ < 0) (hN8 : ⟪F.N 8, u⟫ < 0) :
    ∃ ρ : ℝ, ρ ≠ 0 ∧
      (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
        0 < ρ * det3 (quad (x 4) (x 0) (x 5) (x 3) (i + 1) - quad (x 4) (x 0) (x 5) (x 3) i)
          (quad (x 4) (x 0) (x 5) (x 3) j - quad (x 4) (x 0) (x 5) (x 3) i) u) ∧
      (∀ q : Fin 7, (q = 1 ∨ q = 2) → ∀ i : ZMod 4,
        0 < ρ * det3 (quad (x 4) (x 0) (x 5) (x 3) (i + 1) - quad (x 4) (x 0) (x 5) (x 3) i)
          (x q - quad (x 4) (x 0) (x 5) (x 3) i) u) := by
  have cr0 := cross_ne_zero_of_facet_sign F 3 4 0 (by decide) (by decide) hN3.ne' 8 (by decide) (by decide)
  have cr1 := cross_ne_zero_of_facet_sign F 2 0 5 (by decide) (by decide) hN2.ne 4 (by decide) (by decide)
  have cr2 := cross_ne_zero_of_facet_sign F 6 5 3 (by decide) (by decide) hN6.ne 2 (by decide) (by decide)
  have cr3 := cross_ne_zero_of_facet_sign F 8 3 4 (by decide) (by decide) hN8.ne 6 (by decide) (by decide)
  obtain ⟨σ0, hσ0n, hσ0⟩ := det3_sign_edgeOn F 4 4 0 (by decide) (by decide) u hN4 cr0
  obtain ⟨σ1, hσ1n, hσ1⟩ := det3_sign_ridge F 2 3 0 5 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u ⟨hN2, hN3⟩ cr1
  obtain ⟨σ2, hσ2n, hσ2⟩ := det3_sign_ridge F 6 3 5 3 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u ⟨hN6, hN3⟩ cr2
  obtain ⟨σ3, hσ3n, hσ3⟩ := det3_sign_ridge F 8 3 3 4 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u ⟨hN8, hN3⟩ cr3
  obtain ⟨⟨h01, h02, h03⟩, hconv⟩ := rim4_assemble (x 4) (x 0) (x 5) (x 3) u σ0 σ1 σ2 σ3
    (hσ0 5 (by decide)) (hσ0 3 (by decide))
    (hσ1 3 (Or.inl (by decide))) (hσ1 4 (Or.inl (by decide)))
    (hσ2 4 (Or.inl (by decide))) (hσ2 0 (Or.inl (by decide)))
    (hσ3 0 (Or.inl (by decide))) (hσ3 5 (Or.inl (by decide)))
  refine ⟨σ0, hσ0n, hconv, ?_⟩
  intro q hq i
  rcases hq with rfl | rfl
  · fin_cases i
    · exact hσ0 1 (by decide)
    · exact sign_transfer h01 (hσ1 1 (Or.inl (by decide)))
    · exact sign_transfer h02 (hσ2 1 (Or.inl (by decide)))
    · exact sign_transfer h03 (hσ3 1 (Or.inl (by decide)))
  · fin_cases i
    · exact hσ0 2 (by decide)
    · exact sign_transfer h01 (hσ1 2 (Or.inr (by decide)))
    · exact sign_transfer h02 (hσ2 2 (Or.inr (by decide)))
    · exact sign_transfer h03 (hσ3 2 (Or.inl (by decide)))

/-- **Leaf U4 (Carbon `q046_m6_coplanar`)**: on the circle of `046`, views `u4(1 + ε)`:
rim the coplanar quadrilateral `(4, 0, 5, 3)`, middle `6` over the chord `4 -> 0`.  Case
conditions: facets `2, 6` negative on the edge direction `x 4 - x 6` (`s2 > 1`,
`<N6, x4 - x6> < 0`; facet 0 (`c4 > 1`) is not needed: vertices 1, 2 are hidden by the ridge signs); loci: `hfar`, `hoff`, `hgen`. -/
theorem q046_coplanar (F : S0xFac 9 s0x_S24 x)
    (h2 : ⟪F.N 2, x 4 - x 6⟫ < 0) (h6 : ⟪F.N 6, x 4 - x 6⟫ < 0)
    (hfar : F.f 4 (x 3) ≠ F.f 4 (x 5))
    (hoff : ⟪F.N 4, cross (x 0 - x 4) (x (if F.f 4 (x 3) < F.f 4 (x 5) then 3 else 5) - x 4)⟫ ≠ 0 ∨
      ⟪x (if F.f 4 (x 3) < F.f 4 (x 5) then 3 else 5) - x 4, x 0 - x 4⟫ < 0 ∨
      ⟪x (if F.f 4 (x 3) < F.f 4 (x 5) then 3 else 5) - x 0, x 4 - x 0⟫ < 0)
    (hgen : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 4) (x 0) (x 5) (x 3) i - quad (x 4) (x 0) (x 5) (x 3) j, x 4 - x 6⟫ ≠ 0 ∨
      ⟪quad (x 4) (x 0) (x 5) (x 3) i - quad (x 4) (x 0) (x 5) (x 3) j, x 0 - x 6⟫ ≠ 0) :
    FaceChordView F 4 := by
  set b : ℝ³ := x 4 - x 6 with hb
  set d : ℝ³ := x 0 - x 6 with hd
  set p : ZMod 4 → ℝ³ := quad (x 4) (x 0) (x 5) (x 3) with hp
  have ev0 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have e2 := ev_inner_neg (F.N 2) b d h2
  have e6 := ev_inner_neg (F.N 6) b d h6
  have einj := eventually_injective_quad p b d hgen
  obtain ⟨ε, hε, hN2, hN6, hinj⟩ := (ev0.and (e2.and (e6.and einj))).exists
  have hε' : 0 < ε := hε
  set u := b + ε • d with hu
  have lin : ∀ t : Fin 9, ⟪F.N t, u⟫ = (F.f t (x 4) - F.f t (x 6)) + ε * (F.f t (x 0) - F.f t (x 6)) := by
    intro t
    rw [hu, inner_add_right, real_inner_smul_right, hb, hd, F.inner_sub, F.inner_sub]
  have hN4 : ⟪F.N 4, u⟫ = 0 := by
    rw [lin, F.zero 4 4 (by decide), F.zero 4 6 (by decide), F.zero 4 0 (by decide)]; ring
  have hN8 : ⟪F.N 8, u⟫ < 0 := by
    rw [lin, F.zero 8 6 (by decide), F.zero 8 4 (by decide)]
    have := F.neg 8 0 (by decide); nlinarith
  have hN3 : 0 < ⟪F.N 3, u⟫ := by
    rw [lin, F.zero 3 4 (by decide), F.zero 3 0 (by decide)]
    have := F.neg 3 6 (by decide); nlinarith
  obtain ⟨ρ, hρ, hcyc, hin⟩ := rim046 F hN4 hN2 hN3 hN6 hN8
  have h_triD : ∀ i : ZMod 4, 0 < ρ * triD p u i := by
    intro i
    have hne1 : (i + 2 : ZMod 4) ≠ i := by
      intro h
      have : (2 : ZMod 4) = 0 := by
        calc (2 : ZMod 4) = (i + 2) - i := by ring
        _ = i - i := by rw [h]
        _ = 0 := sub_self i
      revert this; decide
    have hne2 : (i + 2 : ZMod 4) ≠ i + 1 := by
      intro h
      have : (1 : ZMod 4) = 0 := by
        calc (1 : ZMod 4) = (i + 2) - (i + 1) := by ring
        _ = (i + 1) - (i + 1) := by rw [h]
        _ = 0 := sub_self _
      revert this; decide
    exact hcyc i (i + 2) hne1 hne2
  have hN3ne : F.N 3 ≠ 0 := by
    intro h
    have h1 := F.neg 3 1 (by decide)
    have h2 := F.hN 3 (x 1) (x 0)
    rw [h, inner_zero_left, F.zero 3 0 (by decide)] at h2
    linarith
  have hk0 : det3 (p 2 - p 0) (p 3 - p 1) (p 0 - p 1) = 0 := by
    show det3 (x 5 - x 4) (x 3 - x 0) (x 4 - x 0) = 0
    refine Minimality.T24.det3_zero_of_inner (F.N 3) _ _ _ hN3ne ?_ ?_ ?_
    · rw [F.inner_sub, F.zero 3 5 (by decide), F.zero 3 4 (by decide)]; ring
    · rw [F.inner_sub, F.zero 3 3 (by decide), F.zero 3 0 (by decide)]; ring
    · rw [F.inner_sub, F.zero 3 4 (by decide), F.zero 3 0 (by decide)]; ring
  have h_uni := unimodal_quad_K0 p u ρ hinj h_triD hk0
  set r : ZMod 4 → Fin 7 := quad (4 : Fin 7) 0 5 3 with hr
  have hrx : ∀ i, x (r i) = p i := quad_eq046
  set w : ZMod 4 := if F.f 4 (x 3) < F.f 4 (x 5) then 3 else 2 with hw
  refine ⟨u, 4, inferInstance, r, 0, w, ρ, hN4, by decide, ?_, ?_, hρ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show quad (4 : Fin 7) 0 5 3 0 ∈ s0x_S24 4; decide
  · show quad (4 : Fin 7) 0 5 3 (0 + 1) ∈ s0x_S24 4; decide
  · intro i j hj1 hj2
    simp_rw [hrx]
    exact hcyc i j hj1 hj2
  · intro q hqS hqr i
    simp_rw [hrx]
    exact hin q (ext_vertices046 q hqS hqr) i
  · intro q hqS hqr
    have hq6 := mid_vertices046 q hqS hqr
    subst hq6
    have hra : x (r 0) = x 4 := rfl
    have hra1 : x (r (0 + 1)) = x 0 := rfl
    rw [hra, hra1]
    have h1e : (1 + ε) ≠ 0 := by linarith
    refine ⟨ε / (1 + ε), -1 / (1 + ε), by positivity, ?_, ?_, ?_⟩
    · rw [div_lt_one (by linarith)]; linarith
    · have : (0 : ℝ) < 1 / (1 + ε) := by positivity
      intro h; rw [neg_div] at h; linarith
    · rw [hu, hb, hd]
      ext j
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      field_simp
      ring
  · simp_rw [hrx]; exact hinj
  · simp_rw [hrx]; exact Or.inl h_uni
  · dsimp [w, r, quad]
    split_ifs <;> decide
  · intro m hmw hmS
    have hc := far_cand046 m hmS
    dsimp [w] at hmw ⊢
    split_ifs at hmw ⊢ with h35
    · rcases hc with rfl | rfl
      · show F.f 4 (x 3) < F.f 4 (x 5); exact h35
      · exact False.elim (hmw rfl)
    · rcases hc with rfl | rfl
      · exact False.elim (hmw rfl)
      · show F.f 4 (x 5) < F.f 4 (x 3)
        exact lt_of_le_of_ne (not_lt.mp h35) (Ne.symm hfar)
  · have hra : x (r 0) = x 4 := rfl
    have hra1 : x (r (0 + 1)) = x 0 := rfl
    rw [hra, hra1]
    dsimp [w]
    split_ifs with h35
    · have hrw : r 3 = 3 := rfl
      rw [hrw]
      have hs := hoff
      simp only [h35, ite_true] at hs
      exact hs
    · have hrw : r 2 = 5 := rfl
      rw [hrw]
      have hs := hoff
      simp only [h35, ite_false] at hs
      exact hs


end Minimality.T24.R046
