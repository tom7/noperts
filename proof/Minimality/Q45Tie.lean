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

namespace Minimality.T24.Q45
variable {x : Fin 7 → ℝ³}

private theorem ev_inner_pos (n b d : ℝ³) (h : 0 < ⟪n, b⟫) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪n, b + ε • d⟫ := by
  have := eventually_pos_affine (A := ⟪n, b⟫) (B := ⟪n, d⟫) (Or.inl h)
  filter_upwards [this] with ε hε
  rw [inner_add_right, real_inner_smul_right]; linarith

/-! ### Leaf 2: J0 tie view on the 0345 circle -/

theorem rim5_assemble (A B C D E u : ℝ³) (s0 s1 s2 s3 s4 : ℝ)
    (e0c : 0 < s0 * det3 (B - A) (C - A) u) (e0d : 0 < s0 * det3 (B - A) (D - A) u)
    (e0e : 0 < s0 * det3 (B - A) (E - A) u)
    (e1d : 0 < s1 * det3 (C - B) (D - B) u) (e1e : 0 < s1 * det3 (C - B) (E - B) u)
    (e1a : 0 < s1 * det3 (C - B) (A - B) u)
    (e2e : 0 < s2 * det3 (D - C) (E - C) u) (e2a : 0 < s2 * det3 (D - C) (A - C) u)
    (e2b : 0 < s2 * det3 (D - C) (B - C) u)
    (e3a : 0 < s3 * det3 (E - D) (A - D) u) (e3b : 0 < s3 * det3 (E - D) (B - D) u)
    (e3c : 0 < s3 * det3 (E - D) (C - D) u)
    (e4b : 0 < s4 * det3 (A - E) (B - E) u) (e4c : 0 < s4 * det3 (A - E) (C - E) u)
    (e4d : 0 < s4 * det3 (A - E) (D - E) u) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      0 < s0 * det3 (quint A B C D E (i + 1) - quint A B C D E i)
        (quint A B C D E j - quint A B C D E i) u := by
  have t01 : det3 (B - A) (C - A) u = det3 (C - B) (A - B) u := Minimality.det3_cycle_triangle A B C u
  have t12 : det3 (C - B) (D - B) u = det3 (D - C) (B - C) u := Minimality.det3_cycle_triangle B C D u
  have t23 : det3 (D - C) (E - C) u = det3 (E - D) (C - D) u := Minimality.det3_cycle_triangle C D E u
  have t34 : det3 (E - D) (A - D) u = det3 (A - E) (D - E) u := Minimality.det3_cycle_triangle D E A u
  have h01 : 0 < s0 * s1 := sign_prod e0c (by rw [t01]; exact e1a)
  have h12 : 0 < s1 * s2 := sign_prod e1d (by rw [t12]; exact e2b)
  have h23 : 0 < s2 * s3 := sign_prod e2e (by rw [t23]; exact e3c)
  have h34 : 0 < s3 * s4 := sign_prod e3a (by rw [t34]; exact e4d)
  have h02 : 0 < s0 * s2 := sign_transfer h01 h12
  have h03 : 0 < s0 * s3 := sign_transfer h02 h23
  have h04 : 0 < s0 * s4 := sign_transfer h03 h34
  intro i j hj1 hj2
  fin_cases i <;> fin_cases j
  all_goals first
    | exact False.elim (hj1 rfl)
    | exact False.elim (hj2 rfl)
    | exact e0c | exact e0d | exact e0e
    | exact sign_transfer h01 e1d | exact sign_transfer h01 e1e | exact sign_transfer h01 e1a
    | exact sign_transfer h02 e2e | exact sign_transfer h02 e2a | exact sign_transfer h02 e2b
    | exact sign_transfer h03 e3a | exact sign_transfer h03 e3b | exact sign_transfer h03 e3c
    | exact sign_transfer h04 e4b | exact sign_transfer h04 e4c | exact sign_transfer h04 e4d

/-- The 5-rim `(4, 5, 2, 1, 6)` of the 0345 circle when vertex 1 is exposed (`N5 u > 0`). -/
theorem rim5J0 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hN3 : ⟪F.N 3, u⟫ = 0) (hN0 : ⟪F.N 0, u⟫ < 0) (hN1 : ⟪F.N 1, u⟫ < 0) (hN2 : ⟪F.N 2, u⟫ < 0)
    (hN4 : ⟪F.N 4, u⟫ < 0) (hN5 : 0 < ⟪F.N 5, u⟫) (hN6 : 0 < ⟪F.N 6, u⟫) (hN8 : 0 < ⟪F.N 8, u⟫) :
    ∃ ρ : ℝ, ρ ≠ 0 ∧ ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      0 < ρ * det3 (quint (x 4) (x 5) (x 2) (x 1) (x 6) (i + 1) - quint (x 4) (x 5) (x 2) (x 1) (x 6) i)
        (quint (x 4) (x 5) (x 2) (x 1) (x 6) j - quint (x 4) (x 5) (x 2) (x 1) (x 6) i) u := by
  have cr0 := cross_ne_zero_of_opp_endpoints F 8 6 4 5 (by decide) (by decide) (by decide) (by decide) hN8 hN6
  have cr1 := cross_ne_zero_of_facet_sign F 2 5 2 (by decide) (by decide) hN2.ne 3 (by decide) (by decide)
  have cr2 := cross_ne_zero_of_facet_sign F 0 2 1 (by decide) (by decide) hN0.ne 6 (by decide) (by decide)
  have cr3 := cross_ne_zero_of_facet_sign F 1 1 6 (by decide) (by decide) hN1.ne 0 (by decide) (by decide)
  have cr4 := cross_ne_zero_of_facet_sign F 4 6 4 (by decide) (by decide) hN4.ne 7 (by decide) (by decide)
  obtain ⟨σ0, hσ0n, hσ0⟩ := det3_sign_edgeOn F 3 4 5 (by decide) (by decide) u hN3 cr0
  obtain ⟨σ1, -, hσ1⟩ := det3_sign_ridge F 2 6 5 2 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u ⟨hN2, hN6⟩ cr1
  obtain ⟨σ2, -, hσ2⟩ := det3_sign_ridge F 0 5 2 1 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u ⟨hN0, hN5⟩ cr2
  obtain ⟨σ3, -, hσ3⟩ := det3_sign_ridge F 1 5 1 6 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u ⟨hN1, hN5⟩ cr3
  obtain ⟨σ4, -, hσ4⟩ := det3_sign_ridge F 4 8 6 4 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u ⟨hN4, hN8⟩ cr4
  exact ⟨σ0, hσ0n, rim5_assemble (x 4) (x 5) (x 2) (x 1) (x 6) u σ0 σ1 σ2 σ3 σ4
    (hσ0 2 (by decide)) (hσ0 1 (by decide)) (hσ0 6 (by decide))
    (hσ1 1 (by decide)) (hσ1 6 (by decide)) (hσ1 4 (by decide))
    (hσ2 6 (by decide)) (hσ2 4 (by decide)) (hσ2 5 (by decide))
    (hσ3 4 (by decide)) (hσ3 5 (by decide)) (hσ3 2 (by decide))
    (hσ4 5 (by decide)) (hσ4 2 (by decide)) (hσ4 1 (by decide))⟩

theorem exists_coords (a b c u : ℝ³) (h : det3 a b c ≠ 0) :
    ∃ p q r : ℝ, u = p • a + q • b + r • c := by
  have hv : vol3 a b c ≠ 0 := by
    have : vol3 a b c = det3 a b c := by simp only [det3_expand, vol3]; ring
    rwa [this]
  refine ⟨vol3 u b c / vol3 a b c, vol3 a u c / vol3 a b c, vol3 a b u / vol3 a b c, ?_⟩
  have e : ∀ t : ℝ, vol3 a b c * (t / vol3 a b c) = t := fun t => by field_simp
  refine smul_right_injective _ hv ?_
  simp only
  rw [vol3_smul_cramer, smul_add, smul_add, smul_smul, smul_smul, smul_smul, e, e, e]

/-- Sign of `kappa` of the merged quadrilateral `(5, 2, 1, 6)`. -/
theorem kappa5216 (F : S0xFac 9 s0x_S24 x) {u : ℝ³} {ρ : ℝ}
    (hρ : 0 < ρ * det3 (x 1 - x 2) (x 6 - x 2) u) (hN5 : 0 < ⟪F.N 5, u⟫) :
    ρ * det3 (x 1 - x 5) (x 6 - x 2) (x 5 - x 2) < 0 := by
  have hΩ := omega_ne_zero F
  have hsw : det3 (x 6 - x 2) (x 1 - x 2) u = - det3 (x 1 - x 2) (x 6 - x 2) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have hor := rimOrient F u (-ρ) (by rw [hsw]; linarith)
  have hρΩ : 0 < ρ * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) := by
    by_contra hn; push Not at hn
    nlinarith [mul_nonneg (neg_nonneg.mpr hn) hN5.le]
  obtain ⟨p, q, r, h⟩ := exists_coords (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) (x 5 - x 1) hΩ
  have h5 : x 5 = x 1 + (p • (x 0 - x 1) + q • (x 2 - x 1) + r • (x 6 - x 1)) := by
    rw [← h]; abel
  have hid : det3 (x 1 - x 5) (x 6 - x 2) (x 5 - x 2) =
      - p * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) := by
    rw [h5]
    simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hp : 0 < p := by
    have e1 : ⟪F.N 5, x 5 - x 1⟫ = F.f 5 (x 5) - F.f 5 (x 1) := (F.hN 5 _ _).symm
    have e2 : ⟪F.N 5, x 5 - x 1⟫ = p * (F.f 5 (x 0) - F.f 5 (x 1)) + q * (F.f 5 (x 2) - F.f 5 (x 1)) +
        r * (F.f 5 (x 6) - F.f 5 (x 1)) := by
      rw [h, inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
        real_inner_smul_right, F.inner_sub, F.inner_sub, F.inner_sub]
    rw [F.zero 5 1 (by decide), F.zero 5 2 (by decide), F.zero 5 6 (by decide)] at e2
    rw [F.zero 5 1 (by decide)] at e1
    have hf5 := F.neg 5 5 (by decide); have hf0 := F.neg 5 0 (by decide)
    by_contra hn; push Not at hn
    nlinarith [mul_nonneg (neg_nonneg.mpr hn) (neg_nonneg.mpr hf0.le)]
  rw [hid]
  nlinarith [mul_pos hp hρΩ]

lemma merged_inj (z : ZMod 5 → ℝ)
    (h : ∀ i j, z i = z j → i = j ∨ (i = 0 ∧ j = 0 + 1) ∨ (i = 0 + 1 ∧ j = 0)) :
    Function.Injective (mergedDepths z 0) := by
  have k1 : ∀ i j : ZMod 4, (0 : ZMod 5) + 1 + (i.val : ZMod 5) = 0 + 1 + (j.val : ZMod 5) → i = j := by
    decide
  have k2 : ∀ i : ZMod 4, (0 : ZMod 5) + 1 + (i.val : ZMod 5) ≠ 0 := by decide
  have k3 : ∀ i : ZMod 4, (0 : ZMod 5) + 1 + (i.val : ZMod 5) ≠ 0 + 1 ∨ i = 0 := by decide
  intro i j hij
  have h' : z (0 + 1 + (i.val : ZMod 5)) = z (0 + 1 + (j.val : ZMod 5)) := hij
  rcases h _ _ h' with h1 | ⟨h1, _⟩ | ⟨_, h1⟩
  · exact k1 i j h1
  · exact absurd h1 (k2 i)
  · exact absurd h1 (k2 j)

theorem signs_pos (F : S0xFac 9 s0x_S24 x) (s t α β : ℝ) (hs0 : 0 < s) (ht : 0 < t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hα : 0 < α) (hβ : 0 < β) (h8 : 0 < α * (1 - s) + β * t) (h6 : 0 < α * s + β * (1 - t)) :
    ⟪F.N 3, u_Pi x α β⟫ = 0 ∧ ⟪F.N 0, u_Pi x α β⟫ < 0 ∧ ⟪F.N 1, u_Pi x α β⟫ < 0 ∧
    ⟪F.N 2, u_Pi x α β⟫ < 0 ∧ ⟪F.N 4, u_Pi x α β⟫ < 0 ∧ 0 < ⟪F.N 6, u_Pi x α β⟫ ∧
    0 < ⟪F.N 8, u_Pi x α β⟫ := by
  refine ⟨inner_N3_u_Pi F α β, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [inner_N0_u_Pi F α β]
    have := mul_neg_of_pos_of_neg hα (inner_N0_e5_neg F)
    have := mul_neg_of_pos_of_neg hβ (inner_N0_e4_neg F)
    linarith
  · rw [inner_N1_u_Pi F α β]
    have := mul_neg_of_pos_of_neg hα (inner_N1_e5_neg F)
    have := mul_neg_of_pos_of_neg hβ (inner_N1_e4_neg F)
    linarith
  · rw [inner_N2_u_Pi F α β]
    exact mul_neg_of_pos_of_neg hβ (inner_N2_e4_neg F)
  · rw [inner_N4_u_Pi F α β]
    exact mul_neg_of_pos_of_neg hα (inner_N4_e5_neg F)
  · have hrel := inner_N6_u_Pi F s t α β hdecomp
    have hpos : 0 < (α * s + β * (1 - t)) * ⟪F.N 6, e5 x⟫ := mul_pos h6 (inner_N6_e5_pos F)
    rw [← hrel] at hpos
    exact pos_of_mul_pos_right hpos hs0.le
  · have hrel := inner_N8_u_Pi F s t α β hdecomp
    have hpos : 0 < (α * (1 - s) + β * t) * ⟪F.N 8, e4 x⟫ := mul_pos h8 (inner_N8_e4_pos F)
    rw [← hrel] at hpos
    exact pos_of_mul_pos_right hpos ht.le

lemma mid_vertices_J0t (q : Fin 7) (hqS : q ∈ s0x_S24 3) (hqr : ∀ j : ZMod 5, q ≠ quint (4 : Fin 7) 5 2 1 6 j) :
    q = 0 ∨ q = 3 := by
  revert q; decide

lemma ext_vertices_J0t (q : Fin 7) (hqS : q ∉ s0x_S24 3) (hqr : ∀ j : ZMod 5, q ≠ quint (4 : Fin 7) 5 2 1 6 j) :
    False := by
  revert q; decide

lemma far_cand_J0t (m : ZMod 5) (hmS : quint (4 : Fin 7) 5 2 1 6 m ∉ s0x_S24 3) :
    quint (4 : Fin 7) 5 2 1 6 m = 1 ∨ quint (4 : Fin 7) 5 2 1 6 m = 2 ∨ quint (4 : Fin 7) 5 2 1 6 m = 6 := by
  revert m; decide

lemma rinj_J0t : ∀ a b : ZMod 5, quint (4 : Fin 7) 5 2 1 6 a = quint (4 : Fin 7) 5 2 1 6 b → a = b := by
  decide

lemma quint_eq_J0t : ∀ i : ZMod 5, x (quint (4 : Fin 7) 5 2 1 6 i) = quint (x 4) (x 5) (x 2) (x 1) (x 6) i := by
  intro i; fin_cases i <;> rfl

/-- **Leaf J0-Tie45 (Carbon A22 Rank 1)**: on the 0345 circle, `u45 = alpha e5 + beta e4` in `J0` with
`<N5, u45> > 0` (vertex 1 exposed), tie `z4 = z5` at `u45` (`SingleAdjacentTie`), and the merged
4-cycle `(5, 2, 1, 6)` not in the failing position `min(z6, z2) >= max(zeta, z1)`:
then `u45 ± eps (x4 - x5)` is a face-circle view with the 5-rim `(4, 5, 2, 1, 6)`. -/
theorem q45_J0_tie45 (F : S0xFac 9 s0x_S24 x) (s t : ℝ) (hs0 : 0 < s) (ht : 0 < t) (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (h8 : 0 < α * (1 - s) + β * t) (h6 : 0 < α * s + β * (1 - t))
    (hN5 : 0 < ⟪F.N 5, u_Pi x α β⟫)
    (htie : SingleAdjacentTie (quint (x 4) (x 5) (x 2) (x 1) (x 6)) (u_Pi x α β) 0)
    (hnot : min ⟪x 6, u_Pi x α β⟫ ⟪x 2, u_Pi x α β⟫ < max ⟪x 4, u_Pi x α β⟫ ⟪x 1, u_Pi x α β⟫)
    (w : Fin 7) (hw : w = 1 ∨ w = 2 ∨ w = 6)
    (hmin : ∀ m : Fin 7, m ≠ w → (m = 1 ∨ m = 2 ∨ m = 6) → F.f 3 (x w) < F.f 3 (x m))
    (hoff : ⟪F.N 3, cross (x 5 - x 4) (x w - x 4)⟫ ≠ 0 ∨ ⟪x w - x 4, x 5 - x 4⟫ < 0 ∨
      ⟪x w - x 5, x 4 - x 5⟫ < 0) :
    FaceChordView F 3 := by
  set b : ℝ³ := u_Pi x α β with hb
  set d : ℝ³ := x 4 - x 5 with hd
  set P : ZMod 5 → ℝ³ := quint (x 4) (x 5) (x 2) (x 1) (x 6) with hP
  obtain ⟨_, bN0, bN1, bN2, bN4, bN6, bN8⟩ :=
    signs_pos F s t α β hs0 ht hdecomp hα hβ h8 h6
  obtain ⟨ρ0, -, hconv0⟩ := rim5J0 F (inner_N3_u_Pi F α β) bN0 bN1 bN2 bN4 hN5 bN6 bN8
  have hρΩ : 0 < ρ0 * det3 (x 1 - x 2) (x 6 - x 2) b := hconv0 2 4 (by decide) (by decide)
  have hκ := kappa5216 F hρΩ hN5
  set q : ZMod 4 → ℝ³ := quad (x 5) (x 2) (x 1) (x 6) with hq
  have hmq : mergedDepths (fun i => ⟪P i, b⟫) 0 = fun j => ⟪q j, b⟫ := by
    funext j; fin_cases j <;> rfl
  have hcyc4 : ∀ i, 0 < ρ0 * triD q b i := by
    intro i
    have e : subquad P 0 = q := by funext j; fin_cases j <;> rfl
    have := subquad_strictConvex P b ρ0 hconv0 0 i
    rw [e] at this; exact this
  have hinjq : Function.Injective (fun i => ⟪q i, b⟫) := by
    rw [← hmq]; exact merged_inj _ htie.2
  have huni : IsCyclicUnimodal (mergedDepths (fun i => ⟪P i, b⟫) 0) := by
    rw [hmq]
    have hnh := diagCross_not_high q b hcyc4 hκ
    have hmin_lt := min_lt_max_of_not_le hnh
    have h2lo : min ⟪q 1, b⟫ ⟪q 3, b⟫ < max ⟪q 0, b⟫ ⟪q 2, b⟫ := by
      show min ⟪x 2, b⟫ ⟪x 6, b⟫ < max ⟪x 5, b⟫ ⟪x 1, b⟫
      have h45 : ⟪x 4, b⟫ = ⟪x 5, b⟫ := htie.1
      rw [min_comm, ← h45]; exact hnot
    have hn := hn_of_min_lt_max (z := fun i => ⟪q i, b⟫) hmin_lt
    have hp := hp_of_min_lt_max (z := fun i => ⟪q i, b⟫) h2lo
    exact Minimality.RimCell.isCyclicUnimodal_four _ hinjq hn hp
  have hdir : ⟪P 0 - P (0 + 1), d⟫ ≠ 0 := by
    show ⟪x 4 - x 5, x 4 - x 5⟫ ≠ 0
    have hne : x 4 - x 5 ≠ 0 := by
      intro h
      have h1 := F.zero 2 5 (by decide); have h2 := F.neg 2 4 (by decide)
      rw [sub_eq_zero.mp h] at h2; linarith
    exact (real_inner_self_pos.mpr hne).ne'
  obtain ⟨σ, hσ, hev⟩ := splitUnimodal_exists_sign_5 P b d 0 htie hdir huni
  have ev0 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have eα : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < α + ε * (-σ) :=
    eventually_pos_affine (A := α) (B := -σ) (Or.inl hα)
  have eβ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < β + ε * σ :=
    eventually_pos_affine (A := β) (B := σ) (Or.inl hβ)
  have e8 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < (α * (1 - s) + β * t) + ε * (σ * (s + t - 1)) :=
    eventually_pos_affine (A := α * (1 - s) + β * t) (B := σ * (s + t - 1)) (Or.inl h8)
  have e6 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < (α * s + β * (1 - t)) + ε * (σ * (1 - s - t)) :=
    eventually_pos_affine (A := α * s + β * (1 - t)) (B := σ * (1 - s - t)) (Or.inl h6)
  have ev5 := ev_inner_pos (F.N 5) b (σ • d) hN5
  obtain ⟨ε, hε, hα', hβ', h8', h6', hN5', ⟨hinj, hcu⟩⟩ :=
    (ev0.and (eα.and (eβ.and (e8.and (e6.and (ev5.and hev)))))).exists
  have hε0 : 0 < ε := hε
  set a' : ℝ := α - σ * ε with ha'
  set b' : ℝ := β + σ * ε with hb'
  have hu : b + (σ * ε) • d = u_Pi x a' b' := by
    ext j; simp only [hb, hd, u_Pi, e4, e5, ha', hb', PiLp.add_apply, PiLp.smul_apply,
      PiLp.sub_apply, smul_eq_mul]; ring
  have hα2 : 0 < a' := by rw [ha']; linarith
  have hβ2 : 0 < b' := by rw [hb']; linarith
  have h82 : 0 < a' * (1 - s) + b' * t := by rw [ha', hb']; nlinarith
  have h62 : 0 < a' * s + b' * (1 - t) := by rw [ha', hb']; nlinarith
  have hN52 : 0 < ⟪F.N 5, u_Pi x a' b'⟫ := by
    rw [← hu]
    have : b + ε • (σ • d) = b + (σ * ε) • d := by rw [smul_smul, mul_comm]
    rw [← this]; exact hN5'
  obtain ⟨hN3', cN0, cN1, cN2, cN4, cN6, cN8⟩ :=
    signs_pos F s t a' b' hs0 ht hdecomp hα2 hβ2 h82 h62
  obtain ⟨ρ, hρ, hconv⟩ := rim5J0 F hN3' cN0 cN1 cN2 cN4 hN52 cN6 cN8
  set r : ZMod 5 → Fin 7 := quint (4 : Fin 7) 5 2 1 6 with hr
  have hrx : ∀ i, x (r i) = P i := quint_eq_J0t
  obtain ⟨wi, hrw⟩ : ∃ wi : ZMod 5, r wi = w := by
    rcases hw with rfl | rfl | rfl
    exacts [⟨3, rfl⟩, ⟨2, rfl⟩, ⟨4, rfl⟩]
  have hsum : a' + b' ≠ 0 := by linarith
  have hmb := middle_bounds_J0 s t a' b' hst hα2 hβ2 h82 h62
  rw [hu] at hinj hcu
  refine ⟨u_Pi x a' b', 5, inferInstance, r, 0, wi, ρ, hN3', by decide, ?_, ?_, hρ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show quint (4 : Fin 7) 5 2 1 6 0 ∈ s0x_S24 3; decide
  · show quint (4 : Fin 7) 5 2 1 6 (0 + 1) ∈ s0x_S24 3; decide
  · intro i j hj1 hj2
    simp_rw [hrx]
    exact hconv i j hj1 hj2
  · intro q' hqS hqr i
    exact (ext_vertices_J0t q' hqS hqr).elim
  · intro q' hqS hqr
    have hra : x (r 0) = x 4 := rfl
    have hra1 : x (r (0 + 1)) = x 5 := rfl
    rw [hra, hra1]
    rcases mid_vertices_J0t q' hqS hqr with rfl | rfl
    · exact ⟨a' / (a' + b'), -(1 / (a' + b')), hmb.1.1, hmb.1.2.1, hmb.1.2.2,
        middle_quad_x0 x a' b' hsum⟩
    · exact ⟨((1 - s) * a' + t * b') / (a' + b'), (s + t - 1) / (a' + b'), hmb.2.1, hmb.2.2.1,
        hmb.2.2.2, middle_quad_x3 x s t a' b' hdecomp hsum⟩
  · simp_rw [hrx]; exact hinj
  · simp_rw [hrx]; exact Or.inl (Minimality.strictUnimodal_of_cyclic (by decide) hcu)
  · rw [hrw]
    rcases hw with rfl | rfl | rfl <;> decide
  · intro m hmw hmS
    rw [hrw]
    exact hmin (r m) (fun h => hmw (rinj_J0t _ _ (h.trans hrw.symm))) (far_cand_J0t m hmS)
  · have hra : x (r 0) = x 4 := rfl
    have hra1 : x (r (0 + 1)) = x 5 := rfl
    rw [hra, hra1, hrw]
    exact hoff


end Minimality.T24.Q45
