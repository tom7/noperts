module

public import Minimality.Type24HiddenCone
public import Minimality.RimCellClosed
public import Minimality.RDispatch24
public import Minimality.Type24SAT.Geo.Top
public import Minimality.FaceChordFac
public import Minimality.Type24NxSign

/-!
# Type 24: the cone `J_54 = cone(U_5, U_4)` of facet `0345` in the hidden-cap cone

Formalizes `regionJ_left`, `regionJ_right`, `regionJ_mid`, `regionJ`, and `isRupert_J54_rob5`
in `Minimality.T24.EJ`.
-/

@[expose] public section

set_option autoImplicit false
open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.EJ

open Minimality Minimality.H21 Minimality.T24.SAT Minimality.RimCell Minimality.T24.HC Minimality.FaceChord

variable {x : Fin 7 → ℝ³}

/-! ## Cells and cycles -/

/-- Up facets of the `+N_3` cell (rim `0 4 6 2 5`): `0345, 235, 236, 346`. -/
def UP : Finset (Fin 9) := {3, 6, 7, 8}
/-- Down facets of the `+N_3` cell: `012, 016, 025, 046, 126`. -/
def DnP : Finset (Fin 9) := {0, 1, 2, 4, 5}
/-- Rim cycle `0 4 6 2 5`. -/
def cP : ZMod 5 → Fin 7 := ![0, 4, 6, 2, 5]

/-- Up facets of the `-N_3` cell (rim `2 5 3 4 6`): `235, 236, 346`. -/
def UM : Finset (Fin 9) := {6, 7, 8}
/-- Down facets of the `-N_3` cell: `012, 016, 025, 0345, 046, 126`. -/
def DnM : Finset (Fin 9) := {0, 1, 2, 3, 4, 5}
/-- Rim cycle `2 5 3 4 6`. -/
def cM : ZMod 5 → Fin 7 := ![2, 5, 3, 4, 6]

/-- The 4-rim of the cone `J_54^+` (a face-chord rim, not a cell rim): `2 5 4 6`, diagonals `{2,4}` and `{5,6}`. -/
def cJ : ZMod 4 → Fin 7 := ![2, 5, 4, 6]

theorem cycP : S0xCycUD s0x_S24 cP UP DnP := by decide
theorem cycM : S0xCycUD s0x_S24 cM UM DnM := by decide

theorem injP : Function.Injective cP := by
  intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)
theorem injM : Function.Injective cM := by
  intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)

/-! ## The shape-only ends -/

/-- `σ` of `X_3 - X_0 = σ (X_4 - X_0) + τ (X_5 - X_0)` (Cramer in the `(b, c)` coordinates). -/
noncomputable def sigJ (x : Fin 7 → ℝ³) : ℝ :=
  (oblX2 x 3 * oblX6 x 5 - oblX6 x 3 * oblX2 x 5) / (oblX2 x 4 * oblX6 x 5 - oblX6 x 4 * oblX2 x 5)
/-- `τ` of the same decomposition. -/
noncomputable def tauJ (x : Fin 7 → ℝ³) : ℝ :=
  (oblX2 x 4 * oblX6 x 3 - oblX6 x 4 * oblX2 x 3) / (oblX2 x 4 * oblX6 x 5 - oblX6 x 4 * oblX2 x 5)
/-- `n_B = c_5 (a_4 - 1) - c_4 (a_5 - 1)`. -/
noncomputable def nBJ (x : Fin 7 → ℝ³) : ℝ :=
  oblX6 x 5 * (oblX0 x 4 - 1) - oblX6 x 4 * (oblX0 x 5 - 1)
/-- `n_C = b_4 (a_5 - 1) - b_5 (a_4 - 1)`. -/
noncomputable def nCJ (x : Fin 7 → ℝ³) : ℝ :=
  oblX2 x 4 * (oblX0 x 5 - 1) - oblX2 x 5 * (oblX0 x 4 - 1)

/-- Shape-only left end `V_L` of `J_54`: `U_5 = x 5 - x 0` if `σ ≤ 1`, else `U_34 = x 3 - x 4`. -/
noncomputable def VL (x : Fin 7 → ℝ³) : ℝ³ := if sigJ x ≤ 1 then x 5 - x 0 else x 3 - x 4
/-- Shape-only right end `V_R` of `J_54`: `U_4 = x 4 - x 0` if `τ ≤ 1`, else `U_35 = x 3 - x 5`. -/
noncomputable def VR (x : Fin 7 → ℝ³) : ℝ³ := if tauJ x ≤ 1 then x 4 - x 0 else x 3 - x 5
/-- The `c_a`-coordinate of `V_L`. -/
noncomputable def caL (x : Fin 7 → ℝ³) : ℝ := if sigJ x ≤ 1 then oblX0 x 5 - 1 else oblX0 x 3 - oblX0 x 4
/-- The `c_a`-coordinate of `V_R`. -/
noncomputable def caR (x : Fin 7 → ℝ³) : ℝ := if tauJ x ≤ 1 then oblX0 x 4 - 1 else oblX0 x 3 - oblX0 x 5
/-- The ray `V_a = sgn(a_4 - a_5) (0, -n_C, n_B)` where `J_54` meets the wall `c_a = 0` (facet `126`). -/
noncomputable def Va (x : Fin 7 → ℝ³) : ℝ³ :=
  (if oblX0 x 5 < oblX0 x 4 then (1 : ℝ) else -1) • capView x 0 (-(nCJ x)) (nBJ x)

/-- Left end of `J_54^+`: `V_L`, or `V_a` when `c_a(V_L) < 0`. -/
noncomputable def WL (x : Fin 7 → ℝ³) : ℝ³ := if caL x < 0 then Va x else VL x
/-- Right end of `J_54^+`: `V_R`, or `V_a` when `c_a(V_R) < 0`. -/
noncomputable def WR (x : Fin 7 → ℝ³) : ℝ³ := if caR x < 0 then Va x else VR x

/-- The facet-sign data at a point of the closed cells (facet `0345` edge-on, the other eight in the cell pattern). -/
def JCore (F : S0xFac 9 s0x_S24 x) (u : ℝ³) : Prop :=
  ⟪F.N 3, u⟫ = 0 ∧ (∀ t ∈ ({6, 7, 8} : Finset (Fin 9)), 0 ≤ ⟪F.N t, u⟫) ∧
    ∀ t ∈ ({0, 1, 2, 4, 5} : Finset (Fin 9)), ⟪F.N t, u⟫ ≤ 0

/-! ## Private Lemma-M & coordinate helpers -/

private theorem rep_sub0 (F : S0xFac 9 s0x_S24 x) (v : Fin 7) :
    x v - x 0 = (oblX0 x v - 1) • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) +
      oblX6 x v • (x 6 - x 1) := by
  have h := (M4.type24OfFac F).rep v
  rw [show x v - x 0 = (x v - x 1) - (x 0 - x 1) by abel,
    show x v - x 1 = oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) +
      oblX6 x v • (x 6 - x 1) from by rw [sub_eq_iff_eq_add, h]; abel]
  module

private theorem sig_tau_spec (F : S0xFac 9 s0x_S24 x) :
    0 < sigJ x ∧ 0 < tauJ x ∧ 1 < sigJ x + tauJ x ∧
    x 3 - x 0 = sigJ x • (x 4 - x 0) + tauJ x • (x 5 - x 0) ∧
    oblX0 x 3 - 1 = sigJ x * (oblX0 x 4 - 1) + tauJ x * (oblX0 x 5 - 1) ∧
    oblX2 x 3 = sigJ x * oblX2 x 4 + tauJ x * oblX2 x 5 ∧
    oblX6 x 3 = sigJ x * oblX6 x 4 + tauJ x * oblX6 x 5 := by
  obtain ⟨s, t, hs, ht, hst, hq⟩ := Minimality.T24.RimFromSigns.lemmaM_quad_decomp F
  have hD : oblX2 x 4 * oblX6 x 5 - oblX6 x 4 * oblX2 x 5 < 0 := Minimality.T24.A20.nx_neg F
  have hli := li24 F
  have h3 := rep_sub0 F 3
  have h4 := rep_sub0 F 4
  have h5 := rep_sub0 F 5
  have hzero : ((oblX0 x 3 - 1) - (s * (oblX0 x 4 - 1) + t * (oblX0 x 5 - 1))) • (x 0 - x 1) +
      (oblX2 x 3 - (s * oblX2 x 4 + t * oblX2 x 5)) • (x 2 - x 1) +
      (oblX6 x 3 - (s * oblX6 x 4 + t * oblX6 x 5)) • (x 6 - x 1) = 0 := by
    have heq : x 3 - x 0 - (s • (x 4 - x 0) + t • (x 5 - x 0)) = 0 := sub_eq_zero.mpr hq
    rw [h3, h4, h5] at heq
    rw [← heq]; module
  have hcomb := Fintype.linearIndependent_iff.1 hli
    ![(oblX0 x 3 - 1) - (s * (oblX0 x 4 - 1) + t * (oblX0 x 5 - 1)),
      oblX2 x 3 - (s * oblX2 x 4 + t * oblX2 x 5),
      oblX6 x 3 - (s * oblX6 x 4 + t * oblX6 x 5)]
    (by simpa [Fin.sum_univ_three] using hzero)
  have ha : oblX0 x 3 - 1 = s * (oblX0 x 4 - 1) + t * (oblX0 x 5 - 1) := by
    have := hcomb 0; simp at this; linarith
  have hb : oblX2 x 3 = s * oblX2 x 4 + t * oblX2 x 5 := by
    have := hcomb 1; simp at this; linarith
  have hc : oblX6 x 3 = s * oblX6 x 4 + t * oblX6 x 5 := by
    have := hcomb 2; simp at this; linarith
  have hs_eq : s = sigJ x := by
    dsimp [sigJ]
    rw [eq_div_iff hD.ne, hb, hc]; ring
  have ht_eq : t = tauJ x := by
    dsimp [tauJ]
    rw [eq_div_iff hD.ne, hb, hc]; ring
  subst hs_eq; subst ht_eq
  exact ⟨hs, ht, hst, hq, ha, hb, hc⟩

private theorem va_eq (F : S0xFac 9 s0x_S24 x) :
    Va x = (if oblX0 x 5 < oblX0 x 4 then (1 : ℝ) else -1) •
      ((oblX0 x 4 - 1) • (x 5 - x 0) - (oblX0 x 5 - 1) • (x 4 - x 0)) := by
  have h4 := rep_sub0 F 4
  have h5 := rep_sub0 F 5
  dsimp [Va, capView, nCJ, nBJ]
  congr 1
  rw [h4, h5]; module


private def JCoreOff5 (F : S0xFac 9 s0x_S24 x) (u : ℝ³) : Prop :=
  ⟪F.N 3, u⟫ = 0 ∧ (∀ t ∈ ({6, 7, 8} : Finset (Fin 9)), 0 ≤ ⟪F.N t, u⟫) ∧
    ∀ t ∈ ({0, 1, 2, 4} : Finset (Fin 9)), ⟪F.N t, u⟫ ≤ 0

private theorem jcoreOff5_pos_comb (F : S0xFac 9 s0x_S24 x) {g g' : ℝ³}
    (hg : JCoreOff5 F g) (hg' : JCoreOff5 F g') {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    JCoreOff5 F (α • g + β • g') := by
  have e : ∀ N : ℝ³, ⟪N, α • g + β • g'⟫ = α * ⟪N, g⟫ + β * ⟪N, g'⟫ := by
    intro N; rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  refine ⟨?_, fun t ht => ?_, fun t ht => ?_⟩
  · rw [e, hg.1, hg'.1]; ring
  · rw [e]; have := hg.2.1 t ht; have := hg'.2.1 t ht; positivity
  · rw [e]; have := hg.2.2 t ht; have := hg'.2.2 t ht; nlinarith

private theorem inner_0_capView (F : S0xFac 9 s0x_S24 x) (ca cb cc : ℝ) :
    ⟪F.N 0, capView x ca cb cc⟫ = cc * F.f 0 (x 6) := by
  obtain ⟨⟨a0, b0, _⟩, _, _⟩ := facet_back_vals F
  simp only [capView, inner_add_right, real_inner_smul_right, a0, b0]
  rw [F.inner_sub, F.zero 0 1 (by decide)]; ring

private theorem inner_1_capView (F : S0xFac 9 s0x_S24 x) (ca cb cc : ℝ) :
    ⟪F.N 1, capView x ca cb cc⟫ = cb * F.f 1 (x 2) := by
  obtain ⟨_, ⟨a1, c1, _⟩, _⟩ := facet_back_vals F
  simp only [capView, inner_add_right, real_inner_smul_right, a1, c1]
  rw [F.inner_sub, F.zero 1 1 (by decide)]; ring

private theorem inner_5_capView (F : S0xFac 9 s0x_S24 x) (ca cb cc : ℝ) :
    ⟪F.N 5, capView x ca cb cc⟫ = ca * F.f 5 (x 0) := by
  obtain ⟨_, _, ⟨b5, c5, _⟩⟩ := facet_back_vals F
  simp only [capView, inner_add_right, real_inner_smul_right, b5, c5]
  rw [F.inner_sub, F.zero 5 1 (by decide)]; ring


private theorem jcoreOff5_VL_and_strict (F : S0xFac 9 s0x_S24 x) :
    JCoreOff5 F (VL x) ∧ ⟪F.N 0, VL x⟫ < 0 ∧ ⟪F.N 1, VL x⟫ < 0 ∧
    ⟪F.N 4, VL x⟫ < 0 ∧ 0 < ⟪F.N 6, VL x⟫ ∧ 0 < ⟪F.N 7, VL x⟫ := by
  have T := M4.type24OfFac F
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have hc4 : 0 < oblX6 x 4 := T.X6_pos (v := 4) (by decide)
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  obtain ⟨hsig, htau, _, hq, ha, hb, hc⟩ := sig_tau_spec F
  have h06 : F.f 0 (x 6) < 0 := F.neg 0 6 (by decide)
  have h12 : F.f 1 (x 2) < 0 := F.neg 1 2 (by decide)
  dsimp [VL]; split_ifs with hσ
  · have hn0 : ⟪F.N 0, x 5 - x 0⟫ < 0 := by
      rw [F.inner_sub, F.zero 0 0 (by decide), sub_zero]; exact F.neg 0 5 (by decide)
    have hn1 : ⟪F.N 1, x 5 - x 0⟫ < 0 := by
      rw [F.inner_sub, F.zero 1 0 (by decide), sub_zero]; exact F.neg 1 5 (by decide)
    have hn4 : ⟪F.N 4, x 5 - x 0⟫ < 0 := by
      rw [F.inner_sub, F.zero 4 0 (by decide), sub_zero]; exact F.neg 4 5 (by decide)
    have hn6 : 0 < ⟪F.N 6, x 5 - x 0⟫ := by
      rw [F.inner_sub, F.zero 6 5 (by decide), zero_sub, neg_pos]; exact F.neg 6 0 (by decide)
    have hn7 : 0 < ⟪F.N 7, x 5 - x 0⟫ := by
      have hev : ⟪F.N 7, x 3 - x 0⟫ = sigJ x * ⟪F.N 7, x 4 - x 0⟫ + tauJ x * ⟪F.N 7, x 5 - x 0⟫ := by
        rw [hq, inner_add_right, real_inner_smul_right, real_inner_smul_right]
      rw [F.inner_sub, F.inner_sub, F.zero 7 3 (by decide)] at hev
      have h70 : 0 < -F.f 7 (x 0) := by linarith [F.neg 7 0 (by decide)]
      have h74 : 0 < -F.f 7 (x 4) := by linarith [F.neg 7 4 (by decide)]
      have hmul : 0 < tauJ x * ⟪F.N 7, x 5 - x 0⟫ := by nlinarith
      exact pos_of_mul_pos_right hmul htau.le
    refine ⟨⟨?_, fun t ht => ?_, fun t ht => ?_⟩, hn0, hn1, hn4, hn6, hn7⟩
    · rw [F.inner_sub, F.zero 3 5 (by decide), F.zero 3 0 (by decide), sub_self]
    · simp only [mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · exact hn6.le
      · exact hn7.le
      · have hev : ⟪F.N 8, x 3 - x 0⟫ = sigJ x * ⟪F.N 8, x 4 - x 0⟫ + tauJ x * ⟪F.N 8, x 5 - x 0⟫ := by
          rw [hq, inner_add_right, real_inner_smul_right, real_inner_smul_right]
        rw [F.inner_sub, F.inner_sub, F.zero 8 3 (by decide), F.zero 8 4 (by decide)] at hev
        have h80 : 0 < -F.f 8 (x 0) := by linarith [F.neg 8 0 (by decide)]
        have hmul : 0 ≤ tauJ x * ⟪F.N 8, x 5 - x 0⟫ := by nlinarith
        exact nonneg_of_mul_nonneg_right hmul htau
    · simp only [mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · exact hn0.le
      · exact hn1.le
      · rw [F.inner_sub, F.zero 2 5 (by decide), F.zero 2 0 (by decide), sub_self]
      · exact hn4.le
  · have hσ_gt : 1 < sigJ x := lt_of_not_ge hσ
    have h34_rep : x 3 - x 4 = (oblX0 x 3 - oblX0 x 4) • (x 0 - x 1) +
        (oblX2 x 3 - oblX2 x 4) • (x 2 - x 1) + (oblX6 x 3 - oblX6 x 4) • (x 6 - x 1) := by
      rw [show x 3 - x 4 = (x 3 - x 0) - (x 4 - x 0) by abel, rep_sub0 F 3, rep_sub0 F 4]; module
    have hn0 : ⟪F.N 0, x 3 - x 4⟫ < 0 := by
      rw [h34_rep, ← capView, inner_0_capView]
      have : 0 < oblX6 x 3 - oblX6 x 4 := by nlinarith
      nlinarith
    have hn1 : ⟪F.N 1, x 3 - x 4⟫ < 0 := by
      rw [h34_rep, ← capView, inner_1_capView]
      have : 0 < oblX2 x 3 - oblX2 x 4 := by nlinarith
      nlinarith
    have hn4 : ⟪F.N 4, x 3 - x 4⟫ < 0 := by
      rw [F.inner_sub, F.zero 4 4 (by decide), sub_zero]; exact F.neg 4 3 (by decide)
    have hn6 : 0 < ⟪F.N 6, x 3 - x 4⟫ := by
      rw [F.inner_sub, F.zero 6 3 (by decide), zero_sub, neg_pos]; exact F.neg 6 4 (by decide)
    have hn7 : 0 < ⟪F.N 7, x 3 - x 4⟫ := by
      rw [F.inner_sub, F.zero 7 3 (by decide), zero_sub, neg_pos]; exact F.neg 7 4 (by decide)
    refine ⟨⟨?_, fun t ht => ?_, fun t ht => ?_⟩, hn0, hn1, hn4, hn6, hn7⟩
    · rw [F.inner_sub, F.zero 3 3 (by decide), F.zero 3 4 (by decide), sub_self]
    · simp only [mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · exact hn6.le
      · exact hn7.le
      · rw [F.inner_sub, F.zero 8 3 (by decide), F.zero 8 4 (by decide), sub_self]
    · simp only [mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · exact hn0.le
      · exact hn1.le
      · have hev : ⟪F.N 2, x 3 - x 0⟫ = sigJ x * ⟪F.N 2, x 4 - x 0⟫ + tauJ x * ⟪F.N 2, x 5 - x 0⟫ := by
          rw [hq, inner_add_right, real_inner_smul_right, real_inner_smul_right]
        rw [F.inner_sub, F.inner_sub, F.inner_sub, F.zero 2 0 (by decide), F.zero 2 5 (by decide)] at hev
        have h24 : F.f 2 (x 4) < 0 := F.neg 2 4 (by decide)
        rw [F.inner_sub]; nlinarith
      · exact hn4.le

private theorem jcoreOff5_VR_and_strict (F : S0xFac 9 s0x_S24 x) :
    JCoreOff5 F (VR x) ∧ ⟪F.N 0, VR x⟫ < 0 ∧ ⟪F.N 1, VR x⟫ < 0 ∧
    ⟪F.N 2, VR x⟫ < 0 ∧ 0 < ⟪F.N 7, VR x⟫ ∧ 0 < ⟪F.N 8, VR x⟫ := by
  have T := M4.type24OfFac F
  have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
  have hc4 : 0 < oblX6 x 4 := T.X6_pos (v := 4) (by decide)
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  obtain ⟨hsig, htau, _, hq, ha, hb, hc⟩ := sig_tau_spec F
  have h06 : F.f 0 (x 6) < 0 := F.neg 0 6 (by decide)
  have h12 : F.f 1 (x 2) < 0 := F.neg 1 2 (by decide)
  dsimp [VR]; split_ifs with hτ
  · have hn0 : ⟪F.N 0, x 4 - x 0⟫ < 0 := by
      rw [F.inner_sub, F.zero 0 0 (by decide), sub_zero]; exact F.neg 0 4 (by decide)
    have hn1 : ⟪F.N 1, x 4 - x 0⟫ < 0 := by
      rw [F.inner_sub, F.zero 1 0 (by decide), sub_zero]; exact F.neg 1 4 (by decide)
    have hn2 : ⟪F.N 2, x 4 - x 0⟫ < 0 := by
      rw [F.inner_sub, F.zero 2 0 (by decide), sub_zero]; exact F.neg 2 4 (by decide)
    have hn7 : 0 < ⟪F.N 7, x 4 - x 0⟫ := by
      have hev : ⟪F.N 7, x 3 - x 0⟫ = sigJ x * ⟪F.N 7, x 4 - x 0⟫ + tauJ x * ⟪F.N 7, x 5 - x 0⟫ := by
        rw [hq, inner_add_right, real_inner_smul_right, real_inner_smul_right]
      rw [F.inner_sub, F.inner_sub, F.inner_sub, F.zero 7 3 (by decide)] at hev
      have h70 : 0 < -F.f 7 (x 0) := by linarith [F.neg 7 0 (by decide)]
      have h75 : 0 < -F.f 7 (x 5) := by linarith [F.neg 7 5 (by decide)]
      have hmul : 0 < sigJ x * (F.f 7 (x 4) - F.f 7 (x 0)) := by nlinarith
      rw [F.inner_sub]; exact pos_of_mul_pos_right hmul hsig.le
    have hn8 : 0 < ⟪F.N 8, x 4 - x 0⟫ := by
      rw [F.inner_sub, F.zero 8 4 (by decide), zero_sub, neg_pos]; exact F.neg 8 0 (by decide)
    refine ⟨⟨?_, fun t ht => ?_, fun t ht => ?_⟩, hn0, hn1, hn2, hn7, hn8⟩
    · rw [F.inner_sub, F.zero 3 4 (by decide), F.zero 3 0 (by decide), sub_self]
    · simp only [mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · have hev : ⟪F.N 6, x 3 - x 0⟫ = sigJ x * ⟪F.N 6, x 4 - x 0⟫ + tauJ x * ⟪F.N 6, x 5 - x 0⟫ := by
          rw [hq, inner_add_right, real_inner_smul_right, real_inner_smul_right]
        rw [F.inner_sub, F.inner_sub, F.inner_sub, F.zero 6 3 (by decide), F.zero 6 5 (by decide)] at hev
        have h60 : 0 < -F.f 6 (x 0) := by linarith [F.neg 6 0 (by decide)]
        have hmul : 0 ≤ sigJ x * (F.f 6 (x 4) - F.f 6 (x 0)) := by nlinarith
        rw [F.inner_sub]; exact nonneg_of_mul_nonneg_right hmul hsig
      · exact hn7.le
      · exact hn8.le
    · simp only [mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · exact hn0.le
      · exact hn1.le
      · exact hn2.le
      · rw [F.inner_sub, F.zero 4 4 (by decide), F.zero 4 0 (by decide), sub_self]
  · have hτ_gt : 1 < tauJ x := lt_of_not_ge hτ
    have h35_rep : x 3 - x 5 = (oblX0 x 3 - oblX0 x 5) • (x 0 - x 1) +
        (oblX2 x 3 - oblX2 x 5) • (x 2 - x 1) + (oblX6 x 3 - oblX6 x 5) • (x 6 - x 1) := by
      rw [show x 3 - x 5 = (x 3 - x 0) - (x 5 - x 0) by abel, rep_sub0 F 3, rep_sub0 F 5]; module
    have hn0 : ⟪F.N 0, x 3 - x 5⟫ < 0 := by
      rw [h35_rep, ← capView, inner_0_capView]
      have : 0 < oblX6 x 3 - oblX6 x 5 := by nlinarith
      nlinarith
    have hn1 : ⟪F.N 1, x 3 - x 5⟫ < 0 := by
      rw [h35_rep, ← capView, inner_1_capView]
      have : 0 < oblX2 x 3 - oblX2 x 5 := by nlinarith
      nlinarith
    have hn2 : ⟪F.N 2, x 3 - x 5⟫ < 0 := by
      rw [F.inner_sub, F.zero 2 5 (by decide), sub_zero]; exact F.neg 2 3 (by decide)
    have hn7 : 0 < ⟪F.N 7, x 3 - x 5⟫ := by
      rw [F.inner_sub, F.zero 7 3 (by decide), zero_sub, neg_pos]; exact F.neg 7 5 (by decide)
    have hn8 : 0 < ⟪F.N 8, x 3 - x 5⟫ := by
      rw [F.inner_sub, F.zero 8 3 (by decide), zero_sub, neg_pos]; exact F.neg 8 5 (by decide)
    refine ⟨⟨?_, fun t ht => ?_, fun t ht => ?_⟩, hn0, hn1, hn2, hn7, hn8⟩
    · rw [F.inner_sub, F.zero 3 3 (by decide), F.zero 3 5 (by decide), sub_self]
    · simp only [mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · rw [F.inner_sub, F.zero 6 3 (by decide), F.zero 6 5 (by decide), sub_self]
      · exact hn7.le
      · exact hn8.le
    · simp only [mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · exact hn0.le
      · exact hn1.le
      · exact hn2.le
      · have hev : ⟪F.N 4, x 3 - x 0⟫ = sigJ x * ⟪F.N 4, x 4 - x 0⟫ + tauJ x * ⟪F.N 4, x 5 - x 0⟫ := by
          rw [hq, inner_add_right, real_inner_smul_right, real_inner_smul_right]
        rw [F.inner_sub, F.inner_sub, F.inner_sub, F.zero 4 0 (by decide), F.zero 4 4 (by decide)] at hev
        have h45 : F.f 4 (x 5) < 0 := F.neg 4 5 (by decide)
        rw [F.inner_sub]; nlinarith

private theorem va_comb (F : S0xFac 9 s0x_S24 x)
    (h : (caL x < 0 ∧ 0 < caR x) ∨ (caR x < 0 ∧ 0 < caL x)) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ Va x = α • VL x + β • VR x := by
  obtain ⟨hsig, htau, hst, hq, ha, _, _⟩ := sig_tau_spec F
  have hva := va_eq F
  dsimp [VL, VR, caL, caR] at h ⊢
  by_cases hσ : sigJ x ≤ 1 <;> by_cases hτ : tauJ x ≤ 1 <;>
    simp only [hσ, hτ, ↓reduceIte] at h ⊢
  · rcases h with ⟨hL, hR⟩ | ⟨hR, hL⟩
    · have h45 : oblX0 x 5 < oblX0 x 4 := by linarith
      refine ⟨oblX0 x 4 - 1, 1 - oblX0 x 5, by linarith, by linarith, ?_⟩
      rw [hva]; simp only [h45, ↓reduceIte, one_smul]; module
    · have h45 : ¬ oblX0 x 5 < oblX0 x 4 := by linarith
      refine ⟨1 - oblX0 x 4, oblX0 x 5 - 1, by linarith, by linarith, ?_⟩
      rw [hva]; simp only [h45, ↓reduceIte]; module
  · have hτ_gt : 1 < tauJ x := lt_of_not_ge hτ
    rcases h with ⟨hL, hR⟩ | ⟨hR, hL⟩
    · have h54 : oblX0 x 5 < oblX0 x 4 := by nlinarith
      refine ⟨(oblX0 x 3 - oblX0 x 5) / sigJ x, (1 - oblX0 x 5) / sigJ x,
        div_pos (by linarith) hsig, div_pos (by linarith) hsig, ?_⟩
      rw [hva]; simp only [h54, ↓reduceIte, one_smul]
      apply smul_right_injective ℝ³ hsig.ne'; dsimp only
      simp only [smul_add, smul_smul, mul_div_cancel₀ _ hsig.ne']
      rw [show x 3 - x 5 = (x 3 - x 0) - (x 5 - x 0) by abel, hq,
        show oblX0 x 3 = 1 + sigJ x * (oblX0 x 4 - 1) + tauJ x * (oblX0 x 5 - 1) by linarith]
      module
    · have h54 : ¬ oblX0 x 5 < oblX0 x 4 := by nlinarith
      refine ⟨(oblX0 x 5 - oblX0 x 3) / sigJ x, (oblX0 x 5 - 1) / sigJ x,
        div_pos (by linarith) hsig, div_pos (by linarith) hsig, ?_⟩
      rw [hva]; simp only [h54, ↓reduceIte]
      apply smul_right_injective ℝ³ hsig.ne'; dsimp only
      simp only [smul_add, smul_smul, mul_div_cancel₀ _ hsig.ne']
      rw [show x 3 - x 5 = (x 3 - x 0) - (x 5 - x 0) by abel, hq,
        show oblX0 x 3 = 1 + sigJ x * (oblX0 x 4 - 1) + tauJ x * (oblX0 x 5 - 1) by linarith]
      module
  · have hσ_gt : 1 < sigJ x := lt_of_not_ge hσ
    rcases h with ⟨hL, hR⟩ | ⟨hR, hL⟩
    · have h54 : oblX0 x 5 < oblX0 x 4 := by nlinarith
      refine ⟨(oblX0 x 4 - 1) / tauJ x, (oblX0 x 4 - oblX0 x 3) / tauJ x,
        div_pos (by linarith) htau, div_pos (by linarith) htau, ?_⟩
      rw [hva]; simp only [h54, ↓reduceIte, one_smul]
      apply smul_right_injective ℝ³ htau.ne'; dsimp only
      simp only [smul_add, smul_smul, mul_div_cancel₀ _ htau.ne']
      rw [show x 3 - x 4 = (x 3 - x 0) - (x 4 - x 0) by abel, hq,
        show oblX0 x 3 = 1 + sigJ x * (oblX0 x 4 - 1) + tauJ x * (oblX0 x 5 - 1) by linarith]
      module
    · have h54 : ¬ oblX0 x 5 < oblX0 x 4 := by nlinarith
      refine ⟨(1 - oblX0 x 4) / tauJ x, (oblX0 x 3 - oblX0 x 4) / tauJ x,
        div_pos (by linarith) htau, div_pos (by linarith) htau, ?_⟩
      rw [hva]; simp only [h54, ↓reduceIte]
      apply smul_right_injective ℝ³ htau.ne'; dsimp only
      simp only [smul_add, smul_smul, mul_div_cancel₀ _ htau.ne']
      rw [show x 3 - x 4 = (x 3 - x 0) - (x 4 - x 0) by abel, hq,
        show oblX0 x 3 = 1 + sigJ x * (oblX0 x 4 - 1) + tauJ x * (oblX0 x 5 - 1) by linarith]
      module
  · have hden : 0 < sigJ x + tauJ x - 1 := by linarith
    rcases h with ⟨hL, hR⟩ | ⟨hR, hL⟩
    · have h54 : oblX0 x 5 < oblX0 x 4 := by linarith
      refine ⟨(oblX0 x 3 - oblX0 x 5) / (sigJ x + tauJ x - 1),
        (oblX0 x 4 - oblX0 x 3) / (sigJ x + tauJ x - 1),
        div_pos (by linarith) hden, div_pos (by linarith) hden, ?_⟩
      rw [hva]; simp only [h54, ↓reduceIte, one_smul]
      apply smul_right_injective ℝ³ hden.ne'; dsimp only
      simp only [smul_add, smul_smul, mul_div_cancel₀ _ hden.ne']
      rw [show x 3 - x 4 = (x 3 - x 0) - (x 4 - x 0) by abel,
        show x 3 - x 5 = (x 3 - x 0) - (x 5 - x 0) by abel, hq,
        show oblX0 x 3 = 1 + sigJ x * (oblX0 x 4 - 1) + tauJ x * (oblX0 x 5 - 1) by linarith]
      module
    · have h54 : ¬ oblX0 x 5 < oblX0 x 4 := by linarith
      refine ⟨(oblX0 x 5 - oblX0 x 3) / (sigJ x + tauJ x - 1),
        (oblX0 x 3 - oblX0 x 4) / (sigJ x + tauJ x - 1),
        div_pos (by linarith) hden, div_pos (by linarith) hden, ?_⟩
      rw [hva]; simp only [h54, ↓reduceIte]
      apply smul_right_injective ℝ³ hden.ne'; dsimp only
      simp only [smul_add, smul_smul, mul_div_cancel₀ _ hden.ne']
      rw [show x 3 - x 4 = (x 3 - x 0) - (x 4 - x 0) by abel,
        show x 3 - x 5 = (x 3 - x 0) - (x 5 - x 0) by abel, hq,
        show oblX0 x 3 = 1 + sigJ x * (oblX0 x 4 - 1) + tauJ x * (oblX0 x 5 - 1) by linarith]
      module

private theorem inner_5_VL (F : S0xFac 9 s0x_S24 x) :
    ⟪F.N 5, VL x⟫ = caL x * F.f 5 (x 0) := by
  dsimp [VL, caL]; split_ifs
  · rw [rep_sub0 F 5, ← capView, inner_5_capView]
  · rw [show x 3 - x 4 = (x 3 - x 0) - (x 4 - x 0) by abel, rep_sub0 F 3, rep_sub0 F 4]
    have hrep : (oblX0 x 3 - 1) • (x 0 - x 1) + oblX2 x 3 • (x 2 - x 1) + oblX6 x 3 • (x 6 - x 1) -
        ((oblX0 x 4 - 1) • (x 0 - x 1) + oblX2 x 4 • (x 2 - x 1) + oblX6 x 4 • (x 6 - x 1)) =
        capView x (oblX0 x 3 - oblX0 x 4) (oblX2 x 3 - oblX2 x 4) (oblX6 x 3 - oblX6 x 4) := by
      dsimp [capView]; module
    rw [hrep, inner_5_capView]

private theorem inner_5_VR (F : S0xFac 9 s0x_S24 x) :
    ⟪F.N 5, VR x⟫ = caR x * F.f 5 (x 0) := by
  dsimp [VR, caR]; split_ifs
  · rw [rep_sub0 F 4, ← capView, inner_5_capView]
  · rw [show x 3 - x 5 = (x 3 - x 0) - (x 5 - x 0) by abel, rep_sub0 F 3, rep_sub0 F 5]
    have hrep : (oblX0 x 3 - 1) • (x 0 - x 1) + oblX2 x 3 • (x 2 - x 1) + oblX6 x 3 • (x 6 - x 1) -
        ((oblX0 x 5 - 1) • (x 0 - x 1) + oblX2 x 5 • (x 2 - x 1) + oblX6 x 5 • (x 6 - x 1)) =
        capView x (oblX0 x 3 - oblX0 x 5) (oblX2 x 3 - oblX2 x 5) (oblX6 x 3 - oblX6 x 5) := by
      dsimp [capView]; module
    rw [hrep, inner_5_capView]

private theorem inner_5_Va (F : S0xFac 9 s0x_S24 x) : ⟪F.N 5, Va x⟫ = 0 := by
  dsimp [Va]
  rw [real_inner_smul_right, inner_5_capView, zero_mul, mul_zero]

private theorem jcore_of_off5 {u : ℝ³} (F : S0xFac 9 s0x_S24 x) (h : JCoreOff5 F u)
    (h5 : ⟪F.N 5, u⟫ ≤ 0) : JCore F u := by
  refine ⟨h.1, h.2.1, fun t ht => ?_⟩
  simp only [mem_insert, mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact h.2.2 0 (by decide)
  · exact h.2.2 1 (by decide)
  · exact h.2.2 2 (by decide)
  · exact h.2.2 4 (by decide)
  · exact h5

/-! ## (i) Region lemmas -/

/-- **EJ(i), left end.** `W_L` is a closed-cell point of both 5-rim cells (facet `0345` edge-on). -/
theorem regionJ_left (F : S0xFac 9 s0x_S24 x) (hne : 0 < caL x ∨ 0 < caR x) : JCore F (WL x) := by
  have hL := (jcoreOff5_VL_and_strict F).1
  have hR := (jcoreOff5_VR_and_strict F).1
  dsimp [WL]; split_ifs with hca
  · have hcaR : 0 < caR x := by rcases hne with h | h <;> linarith
    obtain ⟨α, β, hα, hβ, hVa⟩ := va_comb F (Or.inl ⟨hca, hcaR⟩)
    exact jcore_of_off5 F (hVa ▸ jcoreOff5_pos_comb F hL hR hα.le hβ.le) (by rw [inner_5_Va])
  · have h50 : F.f 5 (x 0) < 0 := F.neg 5 0 (by decide)
    exact jcore_of_off5 F hL (by rw [inner_5_VL]; nlinarith [not_lt.mp hca])

/-- **EJ(i), right end.** `W_R` is a closed-cell point of both 5-rim cells (facet `0345` edge-on). -/
theorem regionJ_right (F : S0xFac 9 s0x_S24 x) (hne : 0 < caL x ∨ 0 < caR x) : JCore F (WR x) := by
  have hL := (jcoreOff5_VL_and_strict F).1
  have hR := (jcoreOff5_VR_and_strict F).1
  dsimp [WR]; split_ifs with hca
  · have hcaL : 0 < caL x := by rcases hne with h | h <;> linarith
    obtain ⟨α, β, hα, hβ, hVa⟩ := va_comb F (Or.inr ⟨hca, hcaL⟩)
    exact jcore_of_off5 F (hVa ▸ jcoreOff5_pos_comb F hL hR hα.le hβ.le) (by rw [inner_5_Va])
  · have h50 : F.f 5 (x 0) < 0 := F.neg 5 0 (by decide)
    exact jcore_of_off5 F hR (by rw [inner_5_VR]; nlinarith [not_lt.mp hca])

/-- **EJ(i), interior.** At the sum of the two ends every facet except `0345` is strict in the cell pattern (and `0345` is edge-on). -/
theorem regionJ_mid (F : S0xFac 9 s0x_S24 x) (hne : 0 < caL x ∨ 0 < caR x) :
    ⟪F.N 3, WL x + WR x⟫ = 0 ∧ (∀ t ∈ ({6, 7, 8} : Finset (Fin 9)), 0 < ⟪F.N t, WL x + WR x⟫) ∧
      ∀ t ∈ ({0, 1, 2, 4, 5} : Finset (Fin 9)), ⟪F.N t, WL x + WR x⟫ < 0 := by
  have hWL := regionJ_left F hne
  have hWR := regionJ_right F hne
  obtain ⟨hL0, hL_0, hL_1, hL_4, hL_6, hL_7⟩ := jcoreOff5_VL_and_strict F
  obtain ⟨hR0, hR_0, hR_1, hR_2, hR_7, hR_8⟩ := jcoreOff5_VR_and_strict F
  have hL_4' : ⟪F.N 4, WL x⟫ < 0 := by
    dsimp [WL]; split_ifs with hca
    · have hcaR : 0 < caR x := by rcases hne with h | h <;> linarith
      obtain ⟨α, β, hα, hβ, hVa⟩ := va_comb F (Or.inl ⟨hca, hcaR⟩)
      rw [hVa, inner_add_right, real_inner_smul_right, real_inner_smul_right]
      have := hR0.2.2 4 (by decide); nlinarith
    · exact hL_4
  have hL_6' : 0 < ⟪F.N 6, WL x⟫ := by
    dsimp [WL]; split_ifs with hca
    · have hcaR : 0 < caR x := by rcases hne with h | h <;> linarith
      obtain ⟨α, β, hα, hβ, hVa⟩ := va_comb F (Or.inl ⟨hca, hcaR⟩)
      rw [hVa, inner_add_right, real_inner_smul_right, real_inner_smul_right]
      have := hR0.2.1 6 (by decide); nlinarith
    · exact hL_6
  have hR_2' : ⟪F.N 2, WR x⟫ < 0 := by
    dsimp [WR]; split_ifs with hca
    · have hcaL : 0 < caL x := by rcases hne with h | h <;> linarith
      obtain ⟨α, β, hα, hβ, hVa⟩ := va_comb F (Or.inr ⟨hca, hcaL⟩)
      rw [hVa, inner_add_right, real_inner_smul_right, real_inner_smul_right]
      have := hL0.2.2 2 (by decide); nlinarith
    · exact hR_2
  have hR_8' : 0 < ⟪F.N 8, WR x⟫ := by
    dsimp [WR]; split_ifs with hca
    · have hcaL : 0 < caL x := by rcases hne with h | h <;> linarith
      obtain ⟨α, β, hα, hβ, hVa⟩ := va_comb F (Or.inr ⟨hca, hcaL⟩)
      rw [hVa, inner_add_right, real_inner_smul_right, real_inner_smul_right]
      have := hL0.2.1 8 (by decide); nlinarith
    · exact hR_8
  have hL_0' : ⟪F.N 0, WL x⟫ < 0 := by
    dsimp [WL]; split_ifs with hca
    · have hcaR : 0 < caR x := by rcases hne with h | h <;> linarith
      obtain ⟨α, β, hα, hβ, hVa⟩ := va_comb F (Or.inl ⟨hca, hcaR⟩)
      rw [hVa, inner_add_right, real_inner_smul_right, real_inner_smul_right]; nlinarith
    · exact hL_0
  have hL_1' : ⟪F.N 1, WL x⟫ < 0 := by
    dsimp [WL]; split_ifs with hca
    · have hcaR : 0 < caR x := by rcases hne with h | h <;> linarith
      obtain ⟨α, β, hα, hβ, hVa⟩ := va_comb F (Or.inl ⟨hca, hcaR⟩)
      rw [hVa, inner_add_right, real_inner_smul_right, real_inner_smul_right]; nlinarith
    · exact hL_1
  have hL_7' : 0 < ⟪F.N 7, WL x⟫ := by
    dsimp [WL]; split_ifs with hca
    · have hcaR : 0 < caR x := by rcases hne with h | h <;> linarith
      obtain ⟨α, β, hα, hβ, hVa⟩ := va_comb F (Or.inl ⟨hca, hcaR⟩)
      rw [hVa, inner_add_right, real_inner_smul_right, real_inner_smul_right]; nlinarith
    · exact hL_7
  refine ⟨by rw [inner_add_right, hWL.1, hWR.1, add_zero], fun t ht => ?_, fun t ht => ?_⟩
  · rw [inner_add_right]
    simp only [mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact add_pos_of_pos_of_nonneg hL_6' (hWR.2.1 6 (by decide))
    · exact add_pos_of_pos_of_nonneg hL_7' (hWR.2.1 7 (by decide))
    · exact add_pos_of_nonneg_of_pos (hWL.2.1 8 (by decide)) hR_8'
  · rw [inner_add_right]
    simp only [mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact add_lt_of_neg_of_le hL_0' (hWR.2.2 0 (by decide))
    · exact add_lt_of_neg_of_le hL_1' (hWR.2.2 1 (by decide))
    · exact add_lt_of_le_of_neg (hWL.2.2 2 (by decide)) hR_2'
    · exact add_lt_of_neg_of_le hL_4' (hWR.2.2 4 (by decide))
    · have h50 : F.f 5 (x 0) < 0 := F.neg 5 0 (by decide)
      rcases hne with hcaL | hcaR
      · have hL5 : ⟪F.N 5, WL x⟫ < 0 := by
          simp only [WL, not_lt.mpr hcaL.le, ↓reduceIte, inner_5_VL]; nlinarith
        exact add_lt_of_neg_of_le hL5 (hWR.2.2 5 (by decide))
      · have hR5 : ⟪F.N 5, WR x⟫ < 0 := by
          simp only [WR, not_lt.mpr hcaR.le, ↓reduceIte, inner_5_VR]; nlinarith
        exact add_lt_of_le_of_neg (hWL.2.2 5 (by decide)) hR5

/-! ## (i) assembled (proved from the region lemmas) -/

theorem n3_pos (F : S0xFac 9 s0x_S24 x) : 0 < ⟪F.N 3, x 0 - x 2⟫ := by
  rw [F.inner_sub, F.zero 3 0 (by decide)]
  have := F.neg 3 2 (by decide)
  linarith

theorem jcore_comb (F : S0xFac 9 s0x_S24 x) {g g' : ℝ³} (hg : JCore F g) (hg' : JCore F g') {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : JCore F ((1 - s) • g + s • g') := by
  have e : ∀ N : ℝ³, ⟪N, (1 - s) • g + s • g'⟫ = (1 - s) * ⟪N, g⟫ + s * ⟪N, g'⟫ := by
    intro N; rw [inner_add_right, inner_smul_right, inner_smul_right]
  have h1 : 0 ≤ 1 - s := by linarith
  refine ⟨?_, fun t ht => ?_, fun t ht => ?_⟩
  · rw [e, hg.1, hg'.1]; ring
  · rw [e]; have := hg.2.1 t ht; have := hg'.2.1 t ht; positivity
  · rw [e]; have := hg.2.2 t ht; have := hg'.2.2 t ht; nlinarith

theorem cellLe_P_of_core (F : S0xFac 9 s0x_S24 x) {u : ℝ³} (h : JCore F u) : CellLe F UP DnP u := by
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · have : t = 3 ∨ t = 6 ∨ t = 7 ∨ t = 8 := by simpa [UP] using ht
    rcases this with rfl | rfl | rfl | rfl
    · exact h.1.ge
    all_goals exact h.2.1 _ (by decide)
  · exact h.2.2 t (by simpa [DnP] using ht)

theorem cellLe_M_of_core (F : S0xFac 9 s0x_S24 x) {u : ℝ³} (h : JCore F u) : CellLe F UM DnM u := by
  refine ⟨fun t ht => h.2.1 t (by simpa [UM] using ht), fun t ht => ?_⟩
  by_cases h3 : t = 3
  · subst h3; exact h.1.le
  · exact h.2.2 t (by simp [DnM] at ht; simp; omega)

/-- A cell point of the `+N_3` cell from a midpoint strict off `0345` (tilt along `x 0 - x 2`). -/
theorem cellAt_P_of_mid (F : S0xFac 9 s0x_S24 x) {u : ℝ³} (h3 : ⟪F.N 3, u⟫ = 0)
    (hU : ∀ t ∈ ({6, 7, 8} : Finset (Fin 9)), 0 < ⟪F.N t, u⟫)
    (hD : ∀ t ∈ ({0, 1, 2, 4, 5} : Finset (Fin 9)), ⟪F.N t, u⟫ < 0) : ∃ a, CellAt F UP DnP a := by
  refine exists_cellAt_of_lex (u₀ := u) (v := x 0 - x 2) (fun t ht => ?_) (fun t ht => ?_)
  · by_cases h : t = 3
    · subst h; exact Or.inr ⟨h3, n3_pos F⟩
    · exact Or.inl (hU t (by simp [UP] at ht; simp; omega))
  · exact Or.inl (by linarith [hD t (by simpa [DnP] using ht)])

/-- A cell point of the `-N_3` cell from a midpoint strict off `0345` (tilt along `x 0 - x 2`, toward `-F.N 3` is `x 2 - x 0`). -/
theorem cellAt_M_of_mid (F : S0xFac 9 s0x_S24 x) {u : ℝ³} (h3 : ⟪F.N 3, u⟫ = 0)
    (hU : ∀ t ∈ ({6, 7, 8} : Finset (Fin 9)), 0 < ⟪F.N t, u⟫)
    (hD : ∀ t ∈ ({0, 1, 2, 4, 5} : Finset (Fin 9)), ⟪F.N t, u⟫ < 0) : ∃ a, CellAt F UM DnM a := by
  refine exists_cellAt_of_lex (u₀ := u) (v := x 2 - x 0) (fun t ht => ?_) (fun t ht => ?_)
  · exact Or.inl (hU t (by simpa [UM] using ht))
  · by_cases h : t = 3
    · subst h; exact Or.inr ⟨by linarith, by linarith [n3_pos F, (by rw [← neg_sub, inner_neg_right] : ⟪F.N 3, x 2 - x 0⟫ = -⟪F.N 3, x 0 - x 2⟫)]⟩
    · exact Or.inl (by linarith [hD t (by simp [DnM] at ht; simp; omega)])

/-- **EJ(i).** Both ends are closed-cell points of both 5-rim cells and both cells are nonempty. -/
theorem regionJ (F : S0xFac 9 s0x_S24 x) (hne : 0 < caL x ∨ 0 < caR x) :
    JCore F (WL x) ∧ JCore F (WR x) ∧ (∃ a, CellAt F UP DnP a) ∧ ∃ a, CellAt F UM DnM a := by
  obtain ⟨h3, hU, hD⟩ := regionJ_mid F hne
  exact ⟨regionJ_left F hne, regionJ_right F hne, cellAt_P_of_mid F h3 hU hD, cellAt_M_of_mid F h3 hU hD⟩

/-! ## (ii) The leaves -/

/-- **EJ(ii-a), closed-cell leaf.**  A robustly unimodal 5-rim point of the segment `[W_L, W_R]` (for either adjacent
5-rim cell) gives Rupert (`isRupert_of_closedCell`, `k = 5`). -/
theorem isRupert_J54_rob5 (F : S0xFac 9 s0x_S24 x) (hne : 0 < caL x ∨ 0 < caR x) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hr : RobUni (fun i : ZMod 5 => ⟪x (cM i), (1 - s) • WL x + s • WR x⟫) ∨
      RobUni (fun i : ZMod 5 => ⟪x (cP i), (1 - s) • WL x + s • WR x⟫)) :
    IsRupert (univ.image x) := by
  obtain ⟨hL, hR, ⟨aP, haP⟩, ⟨aM, haM⟩⟩ := regionJ F hne
  have hx := Minimality.H24.SAT.inj_of_fac F
  have hc := jcore_comb F hL hR hs0 hs1
  rcases hr with hr | hr
  · exact isRupert_of_closedCell (by norm_num) F hx injM cycM haM (cellLe_M_of_core F hc) hr
  · exact isRupert_of_closedCell (by norm_num) F hx injP cycP haP (cellLe_P_of_core F hc) hr

private theorem inner3_expand (a b : ℝ³) :
    ⟪a, b⟫ = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three]
  ring

private theorem det3_expand' (a b c : ℝ³) :
    det3 a b c = a 0 * (b 1 * c 2 - b 2 * c 1) + a 1 * (b 2 * c 0 - b 0 * c 2) +
      a 2 * (b 0 * c 1 - b 1 * c 0) := by
  simp only [det3, inner3, cross_apply_zero, cross_apply_one, cross_apply_two]; ring

private theorem det3_cross_eq (a b c d : ℝ³) :
    det3 (cross a b) c d = ⟪a, c⟫ * ⟪b, d⟫ - ⟪b, c⟫ * ⟪a, d⟫ := by
  simp only [det3_expand', inner3, cross_apply_zero, cross_apply_one, cross_apply_two]; ring

private theorem det3_perp_plane {N3 Nt a c u : ℝ³} (hN3 : N3 ≠ 0) (ha : a ≠ 0)
    (h3a : ⟪N3, a⟫ = 0) (h3c : ⟪N3, c⟫ = 0) (h3u : ⟪N3, u⟫ = 0) (hta : ⟪Nt, a⟫ = 0) :
    det3 a c N3 * ⟪Nt, u⟫ = det3 a u N3 * ⟪Nt, c⟫ := by
  have hbasis_gen : ∀ v : ℝ³, (⟪a, a⟫ * ⟪N3, N3⟫) • v =
      (⟪N3, N3⟫ * ⟪a, v⟫) • a + (⟪a, a⟫ * ⟪N3, v⟫) • N3 +
        ⟪cross N3 a, v⟫ • cross N3 a +
        ⟪N3, a⟫ • (⟪N3, a⟫ • v - ⟪a, v⟫ • N3 - ⟪N3, v⟫ • a) := by
    intro v; ext i
    simp only [PiLp.smul_apply, PiLp.add_apply, PiLp.sub_apply, smul_eq_mul, inner3,
      cross_apply_zero, cross_apply_one, cross_apply_two]
    fin_cases i <;> simp <;> ring
  have hbasis : ∀ v : ℝ³, (⟪a, a⟫ * ⟪N3, N3⟫) • v =
      (⟪N3, N3⟫ * ⟪a, v⟫) • a + (⟪a, a⟫ * ⟪N3, v⟫) • N3 +
        ⟪cross N3 a, v⟫ • cross N3 a := by
    intro v; have h := hbasis_gen v; rw [h3a, zero_smul, add_zero] at h; exact h
  have hdet_eq : ∀ w : ℝ³, ⟪cross N3 a, w⟫ = det3 a w N3 := by
    intro w; simp only [det3_expand', inner3, cross_apply_zero, cross_apply_one, cross_apply_two]; ring
  let v : ℝ³ := det3 a c N3 • u - det3 a u N3 • c
  have hv3 : ⟪N3, v⟫ = 0 := by
    simp only [v, inner_sub_right, real_inner_smul_right, h3u, h3c, mul_zero, sub_self]
  have hvc : ⟪cross N3 a, v⟫ = 0 := by
    rw [hdet_eq]; simp only [v, det3_expand', PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have hvb := congrArg (fun w => ⟪Nt, w⟫) (hbasis v)
  simp only [real_inner_smul_right, inner_add_right, hta, hv3, hvc, mul_zero, zero_mul, add_zero] at hvb
  have ha_pos : 0 < ⟪a, a⟫ := real_inner_self_pos.mpr ha
  have hN3_pos : 0 < ⟪N3, N3⟫ := real_inner_self_pos.mpr hN3
  have hna : ⟪a, a⟫ * ⟪N3, N3⟫ ≠ 0 := mul_ne_zero ha_pos.ne' hN3_pos.ne'
  have hntv : ⟪Nt, v⟫ = 0 := (mul_eq_zero.mp hvb).resolve_left hna
  simp only [v, inner_sub_right, real_inner_smul_right] at hntv
  linarith

private theorem cross_cross_eq (a b c : ℝ³) :
    cross a (cross b c) = ⟪a, c⟫ • b - ⟪a, b⟫ • c := by
  ext i
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, inner3,
    cross_apply_zero, cross_apply_one, cross_apply_two]
  fin_cases i <;> simp [cross_apply_zero, cross_apply_one, cross_apply_two] <;> ring

private theorem det3_smul1 (s : ℝ) (a b c : ℝ³) : det3 (s • a) b c = s * det3 a b c := by
  simp only [det3_expand', PiLp.smul_apply, smul_eq_mul]; ring

private theorem edge_det3_same_sign (F : S0xFac 9 s0x_S24 x) {t1 t2 : Fin 9} {A B p q v : Fin 7}
    {u : ℝ³} (hAB1 : A ∈ s0x_S24 t1 ∧ B ∈ s0x_S24 t1) (hAB2 : A ∈ s0x_S24 t2 ∧ B ∈ s0x_S24 t2)
    (hp : p ∈ s0x_S24 t1 ∧ p ∉ s0x_S24 t2) (hq : q ∈ s0x_S24 t2 ∧ q ∉ s0x_S24 t1)
    (hu1 : ⟪F.N t1, u⟫ < 0) (hu2 : 0 < ⟪F.N t2, u⟫)
    (hv : v ∉ s0x_S24 t1 ∩ s0x_S24 t2) (hAB : A ≠ B) :
    ∃ α : ℝ, α ≠ 0 ∧ x B - x A = α • cross (F.N t1) (F.N t2) ∧
      0 < (-(1 / α)) * det3 (x B - x A) (x v - x A) u := by
  have hx := Minimality.H24.SAT.inj_of_fac F
  have he : x B - x A ≠ 0 := sub_ne_zero.mpr (fun h => hAB (hx h).symm)
  have h1e : ⟪F.N t1, x B - x A⟫ = 0 := by
    rw [F.inner_sub, F.zero t1 B hAB1.2, F.zero t1 A hAB1.1, sub_self]
  have h2e : ⟪F.N t2, x B - x A⟫ = 0 := by
    rw [F.inner_sub, F.zero t2 B hAB2.2, F.zero t2 A hAB2.1, sub_self]
  have hcross_ne : cross (F.N t1) (F.N t2) ≠ 0 := by
    intro h0
    have h1p : ⟪F.N t1, x p - x A⟫ = 0 := by
      rw [F.inner_sub, F.zero t1 p hp.1, F.zero t1 A hAB1.1, sub_self]
    have h2p : ⟪F.N t2, x p - x A⟫ < 0 := by
      rw [F.inner_sub, F.zero t2 A hAB2.1, sub_zero]; exact F.neg t2 p hp.2
    have h1q : ⟪F.N t1, x q - x A⟫ < 0 := by
      rw [F.inner_sub, F.zero t1 A hAB1.1, sub_zero]; exact F.neg t1 q hq.2
    have h2q : ⟪F.N t2, x q - x A⟫ = 0 := by
      rw [F.inner_sub, F.zero t2 q hq.1, F.zero t2 A hAB2.1, sub_self]
    have hd := det3_cross_eq (F.N t1) (F.N t2) (x p - x A) (x q - x A)
    rw [h0, det3_expand'] at hd
    simp only [PiLp.zero_apply, zero_mul, sub_self, mul_zero, add_zero] at hd
    rw [h1p, h2q, zero_mul, zero_sub] at hd
    have hmul : ⟪F.N t2, x p - x A⟫ * ⟪F.N t1, x q - x A⟫ > 0 := mul_pos_of_neg_of_neg h2p h1q
    linarith
  set c := cross (F.N t1) (F.N t2)
  have hc2 : ⟪c, c⟫ ≠ 0 := (real_inner_self_pos.mpr hcross_ne).ne'
  have hcol_gen : ⟪c, c⟫ • (x B - x A) - ⟪x B - x A, c⟫ • c =
      ⟪F.N t2, x B - x A⟫ • cross c (F.N t1) - ⟪F.N t1, x B - x A⟫ • cross c (F.N t2) := by
    have hcc : cross c (cross (x B - x A) c) = ⟪c, c⟫ • (x B - x A) - ⟪x B - x A, c⟫ • c := by
      rw [cross_cross_eq, real_inner_comm (x B - x A) c]
    have hce : cross (x B - x A) c = ⟪x B - x A, F.N t2⟫ • F.N t1 - ⟪x B - x A, F.N t1⟫ • F.N t2 := by
      dsimp [c]; rw [cross_cross_eq]
    have hlin : cross c (⟪x B - x A, F.N t2⟫ • F.N t1 - ⟪x B - x A, F.N t1⟫ • F.N t2) =
        ⟪F.N t2, x B - x A⟫ • cross c (F.N t1) - ⟪F.N t1, x B - x A⟫ • cross c (F.N t2) := by
      have hc1 : ⟪x B - x A, F.N t2⟫ = ⟪F.N t2, x B - x A⟫ := real_inner_comm _ _
      have hc2' : ⟪x B - x A, F.N t1⟫ = ⟪F.N t1, x B - x A⟫ := real_inner_comm _ _
      rw [hc1, hc2']
      ext i
      simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, cross_apply_zero,
        cross_apply_one, cross_apply_two]
      fin_cases i <;> simp <;> ring
    rw [← hcc, hce, hlin]
  have hcol : ⟪c, c⟫ • (x B - x A) = ⟪x B - x A, c⟫ • c := by
    rw [h1e, h2e, zero_smul, zero_smul, sub_self] at hcol_gen
    exact sub_eq_zero.mp hcol_gen
  set α := ⟪x B - x A, c⟫ / ⟪c, c⟫
  have hα_eq : x B - x A = α • c := by
    apply smul_right_injective ℝ³ hc2
    dsimp only
    rw [hcol, smul_smul, mul_div_cancel₀ _ hc2]
  have hα_ne : α ≠ 0 := by
    intro h0; rw [h0, zero_smul] at hα_eq; exact he hα_eq
  refine ⟨α, hα_ne, hα_eq, ?_⟩
  rw [hα_eq, det3_smul1, det3_cross_eq]
  have hcancel : -(1 / α) * (α * (⟪F.N t1, x v - x A⟫ * ⟪F.N t2, u⟫ - ⟪F.N t2, x v - x A⟫ * ⟪F.N t1, u⟫)) =
      -(⟪F.N t1, x v - x A⟫ * ⟪F.N t2, u⟫ - ⟪F.N t2, x v - x A⟫ * ⟪F.N t1, u⟫) := by
    field_simp [hα_ne]
  rw [hcancel]
  have hv1 : ⟪F.N t1, x v - x A⟫ ≤ 0 := by
    rw [F.inner_sub, F.zero t1 A hAB1.1, sub_zero]
    by_cases h : v ∈ s0x_S24 t1
    · rw [F.zero t1 v h]
    · exact (F.neg t1 v h).le
  have hv2 : ⟪F.N t2, x v - x A⟫ ≤ 0 := by
    rw [F.inner_sub, F.zero t2 A hAB2.1, sub_zero]
    by_cases h : v ∈ s0x_S24 t2
    · rw [F.zero t2 v h]
    · exact (F.neg t2 v h).le
  simp only [Finset.mem_inter, not_and] at hv
  by_cases h : v ∈ s0x_S24 t1
  · have hv2' : ⟪F.N t2, x v - x A⟫ < 0 := by
      rw [F.inner_sub, F.zero t2 A hAB2.1, sub_zero]; exact F.neg t2 v (hv h)
    have hmul1 : ⟪F.N t1, x v - x A⟫ * ⟪F.N t2, u⟫ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hv1 hu2.le
    have hmul2 : 0 < ⟪F.N t2, x v - x A⟫ * ⟪F.N t1, u⟫ := mul_pos_of_neg_of_neg hv2' hu1
    linarith
  · have hv1' : ⟪F.N t1, x v - x A⟫ < 0 := by
      rw [F.inner_sub, F.zero t1 A hAB1.1, sub_zero]; exact F.neg t1 v h
    have hmul1 : ⟪F.N t1, x v - x A⟫ * ⟪F.N t2, u⟫ < 0 := mul_neg_of_neg_of_pos hv1' hu2
    have hmul2 : 0 ≤ ⟪F.N t2, x v - x A⟫ * ⟪F.N t1, u⟫ := mul_nonneg_of_nonpos_of_nonpos hv2 hu1.le
    linarith

private theorem u_seg_strict (F : S0xFac 9 s0x_S24 x) (hne : 0 < caL x ∨ 0 < caR x)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    let u := (1 - s) • WL x + s • WR x
    ⟪F.N 3, u⟫ = 0 ∧ (∀ t ∈ ({6, 7, 8} : Finset (Fin 9)), 0 < ⟪F.N t, u⟫) ∧
      ∀ t ∈ ({0, 1, 2, 4, 5} : Finset (Fin 9)), ⟪F.N t, u⟫ < 0 := by
  intro u
  have hL := regionJ_left F hne
  have hR := regionJ_right F hne
  obtain ⟨_, hUm, hDm⟩ := regionJ_mid F hne
  have h1s : 0 < 1 - s := by linarith
  refine ⟨?_, fun t ht => ?_, fun t ht => ?_⟩
  · simp only [u, inner_add_right, real_inner_smul_right, hL.1, hR.1, mul_zero, add_zero]
  · have h1 := hL.2.1 t ht
    have h2 := hR.2.1 t ht
    have hm := hUm t ht
    simp only [inner_add_right, real_inner_smul_right] at hm
    have hor : 0 < ⟪F.N t, WL x⟫ ∨ 0 < ⟪F.N t, WR x⟫ := by
      by_contra h; push Not at h; linarith
    simp only [u, inner_add_right, real_inner_smul_right]
    rcases hor with h | h <;> nlinarith
  · have h1 := hL.2.2 t ht
    have h2 := hR.2.2 t ht
    have hm := hDm t ht
    simp only [inner_add_right, real_inner_smul_right] at hm
    have hor : ⟪F.N t, WL x⟫ < 0 ∨ ⟪F.N t, WR x⟫ < 0 := by
      by_contra h; push Not at h; linarith
    simp only [u, inner_add_right, real_inner_smul_right]
    rcases hor with h | h <;> nlinarith

private theorem edge_54_det3 (F : S0xFac 9 s0x_S24 x) {u : ℝ³} (h3u : ⟪F.N 3, u⟫ = 0)
    (v : Fin 7) :
    ⟪F.N 3, F.N 3⟫ * det3 (x 4 - x 5) (x v - x 5) u =
      F.f 3 (x v) * det3 (x 4 - x 5) (F.N 3) u := by
  have h345 : ⟪F.N 3, x 4 - x 5⟫ = 0 := by
    rw [F.inner_sub, F.zero 3 4 (by decide), F.zero 3 5 (by decide), sub_self]
  have h3v : ⟪F.N 3, x v - x 5⟫ = F.f 3 (x v) := by
    rw [F.inner_sub, F.zero 3 5 (by decide), sub_zero]
  have hid : ⟪F.N 3, F.N 3⟫ * det3 (x 4 - x 5) (x v - x 5) u -
      ⟪F.N 3, x v - x 5⟫ * det3 (x 4 - x 5) (F.N 3) u =
      ⟪F.N 3, x 4 - x 5⟫ * det3 (F.N 3) (x v - x 5) u +
      ⟪F.N 3, u⟫ * det3 (x 4 - x 5) (x v - x 5) (F.N 3) := by
    simp only [det3_expand', inner3]; ring
  rw [h345, h3u, h3v, zero_mul, zero_mul, add_zero] at hid
  exact sub_eq_zero.mp hid

private theorem cJ_hcyc_hin (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (h3 : ⟪F.N 3, u⟫ = 0) (hU : ∀ t ∈ ({6, 7, 8} : Finset (Fin 9)), 0 < ⟪F.N t, u⟫)
    (hD : ∀ t ∈ ({0, 1, 2, 4, 5} : Finset (Fin 9)), ⟪F.N t, u⟫ < 0) :
    let ρ := det3 (x 5 - x 2) (x 4 - x 2) u
    ρ ≠ 0 ∧
    (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      0 < ρ * det3 (x (cJ (i + 1)) - x (cJ i)) (x (cJ j) - x (cJ i)) u) ∧
    (∀ i : ZMod 4, 0 < ρ * det3 (x (cJ (i + 1)) - x (cJ i)) (x 1 - x (cJ i)) u) := by
  intro ρ
  have hu2 : ⟪F.N 2, u⟫ < 0 := hD 2 (by decide)
  have hu4 : ⟪F.N 4, u⟫ < 0 := hD 4 (by decide)
  have hu5 : ⟪F.N 5, u⟫ < 0 := hD 5 (by decide)
  have hu6 : 0 < ⟪F.N 6, u⟫ := hU 6 (by decide)
  have hu7 : 0 < ⟪F.N 7, u⟫ := hU 7 (by decide)
  have hu8 : 0 < ⟪F.N 8, u⟫ := hU 8 (by decide)
  have e0 : ∀ v ∈ ({4, 6, 1} : Finset (Fin 7)),
      ∃ α : ℝ, α ≠ 0 ∧ x 5 - x 2 = α • cross (F.N 2) (F.N 6) ∧
        0 < (-(1 / α)) * det3 (x 5 - x 2) (x v - x 2) u := by
    intro v hv
    refine edge_det3_same_sign F (t1 := 2) (t2 := 6) (A := 2) (B := 5) (p := 0) (q := 3)
      ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
      hu2 hu6 ?_ (by decide)
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl | rfl <;> decide
  obtain ⟨α0, hα0, he0, h04⟩ := e0 4 (by decide)
  obtain ⟨α0', _, he0', h06⟩ := e0 6 (by decide)
  obtain ⟨α0'', _, he0'', h01⟩ := e0 1 (by decide)
  have hρ_ne : ρ ≠ 0 := by
    intro h0; dsimp [ρ] at h0; rw [h0, mul_zero] at h04; exact lt_irrefl 0 h04
  have h0_6 : 0 < ρ * det3 (x 5 - x 2) (x 6 - x 2) u := by
    have hmul := mul_pos h04 h06
    have heq : α0' = α0 := by
      have := he0'.symm.trans he0
      have hne : cross (F.N 2) (F.N 6) ≠ 0 := by
        intro hz; rw [hz, smul_zero] at he0
        exact sub_ne_zero.mpr (fun h => absurd ((Minimality.H24.SAT.inj_of_fac F) h) (by decide)) he0
      exact smul_left_injective ℝ hne this
    rw [heq] at hmul
    have hsq : (-(1 / α0)) * (-(1 / α0)) > 0 := mul_self_pos.mpr (neg_ne_zero.mpr (one_div_ne_zero hα0))
    have hid : (-(1 / α0) * det3 (x 5 - x 2) (x 4 - x 2) u) * (-(1 / α0) * det3 (x 5 - x 2) (x 6 - x 2) u) =
        (-(1 / α0) * -(1 / α0)) * (ρ * det3 (x 5 - x 2) (x 6 - x 2) u) := by dsimp [ρ]; ring
    rw [hid] at hmul
    exact pos_of_mul_pos_right hmul hsq.le
  have h0_1 : 0 < ρ * det3 (x 5 - x 2) (x 1 - x 2) u := by
    have hmul := mul_pos h04 h01
    have heq : α0'' = α0 := by
      have := he0''.symm.trans he0
      have hne : cross (F.N 2) (F.N 6) ≠ 0 := by
        intro hz; rw [hz, smul_zero] at he0
        exact sub_ne_zero.mpr (fun h => absurd ((Minimality.H24.SAT.inj_of_fac F) h) (by decide)) he0
      exact smul_left_injective ℝ hne this
    rw [heq] at hmul
    have hsq : (-(1 / α0)) * (-(1 / α0)) > 0 := mul_self_pos.mpr (neg_ne_zero.mpr (one_div_ne_zero hα0))
    have hid : (-(1 / α0) * det3 (x 5 - x 2) (x 4 - x 2) u) * (-(1 / α0) * det3 (x 5 - x 2) (x 1 - x 2) u) =
        (-(1 / α0) * -(1 / α0)) * (ρ * det3 (x 5 - x 2) (x 1 - x 2) u) := by dsimp [ρ]; ring
    rw [hid] at hmul
    exact pos_of_mul_pos_right hmul hsq.le
  have hcyc01 : det3 (x 5 - x 2) (x 4 - x 2) u = det3 (x 4 - x 5) (x 2 - x 5) u := by
    simp only [det3_expand', PiLp.sub_apply]; ring
  have h1_2 : 0 < ρ * det3 (x 4 - x 5) (x 2 - x 5) u := by
    dsimp [ρ]; rw [← hcyc01]; exact mul_self_pos.mpr hρ_ne
  have h1_same : ∀ v : Fin 7, v ∉ s0x_S24 3 →
      0 < ρ * det3 (x 4 - x 5) (x v - x 5) u := by
    intro v hv
    have hn2 := F.neg 3 2 (by decide)
    have hnv := F.neg 3 v hv
    have e2 := edge_54_det3 F h3 2
    have ev := edge_54_det3 F h3 v
    have hN3_pos : 0 < ⟪F.N 3, F.N 3⟫ := by
      have hN3 : F.N 3 ≠ 0 := fun h0 => by
        have hf := F.inner_sub 3 2 4
        rw [h0, inner_zero_left, F.zero 3 4 (by decide), sub_zero] at hf
        have := F.neg 3 2 (by decide); linarith
      exact real_inner_self_pos.mpr hN3
    have hdet2_ne : det3 (x 4 - x 5) (x 2 - x 5) u ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at h1_2; exact lt_irrefl 0 h1_2
    have hN3_det : det3 (x 4 - x 5) (F.N 3) u ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at e2; exact absurd ((mul_eq_zero.mp e2).resolve_left hN3_pos.ne') hdet2_ne
    have hmul_pos : 0 < (F.f 3 (x 2) * F.f 3 (x v)) ^ 2 * (ρ * det3 (x 4 - x 5) (F.N 3) u) ^ 2 :=
      mul_pos (sq_pos_of_ne_zero (mul_ne_zero hn2.ne hnv.ne)) (sq_pos_of_ne_zero (mul_ne_zero hρ_ne hN3_det))
    have hfac : (F.f 3 (x 2) * F.f 3 (x v)) ^ 2 * (ρ * det3 (x 4 - x 5) (F.N 3) u) ^ 2 =
        (F.f 3 (x 2) * F.f 3 (x v)) * ⟪F.N 3, F.N 3⟫ ^ 2 *
          (ρ * det3 (x 4 - x 5) (x 2 - x 5) u) * (ρ * det3 (x 4 - x 5) (x v - x 5) u) := by
      have h1 : ⟪F.N 3, F.N 3⟫ * det3 (x 4 - x 5) (x 2 - x 5) u = F.f 3 (x 2) * det3 (x 4 - x 5) (F.N 3) u := e2
      have h2 : ⟪F.N 3, F.N 3⟫ * det3 (x 4 - x 5) (x v - x 5) u = F.f 3 (x v) * det3 (x 4 - x 5) (F.N 3) u := ev
      calc (F.f 3 (x 2) * F.f 3 (x v)) ^ 2 * (ρ * det3 (x 4 - x 5) (F.N 3) u) ^ 2
        _ = (F.f 3 (x 2) * F.f 3 (x v)) * (ρ * (F.f 3 (x 2) * det3 (x 4 - x 5) (F.N 3) u)) *
            (ρ * (F.f 3 (x v) * det3 (x 4 - x 5) (F.N 3) u)) := by ring
        _ = (F.f 3 (x 2) * F.f 3 (x v)) * (ρ * (⟪F.N 3, F.N 3⟫ * det3 (x 4 - x 5) (x 2 - x 5) u)) *
            (ρ * (⟪F.N 3, F.N 3⟫ * det3 (x 4 - x 5) (x v - x 5) u)) := by rw [← h1, ← h2]
        _ = _ := by ring
    rw [hfac] at hmul_pos
    have hcoeff : 0 < (F.f 3 (x 2) * F.f 3 (x v)) * ⟪F.N 3, F.N 3⟫ ^ 2 *
        (ρ * det3 (x 4 - x 5) (x 2 - x 5) u) :=
      mul_pos (mul_pos (mul_pos_of_neg_of_neg hn2 hnv) (sq_pos_of_ne_zero hN3_pos.ne')) h1_2
    exact pos_of_mul_pos_right hmul_pos hcoeff.le
  have h1_6 : 0 < ρ * det3 (x 4 - x 5) (x 6 - x 5) u := h1_same 6 (by decide)
  have h1_1 : 0 < ρ * det3 (x 4 - x 5) (x 1 - x 5) u := h1_same 1 (by decide)
  have hcyc12 : det3 (x 4 - x 5) (x 6 - x 5) u = det3 (x 6 - x 4) (x 5 - x 4) u := by
    simp only [det3_expand', PiLp.sub_apply]; ring
  have e2 : ∀ v ∈ ({5, 2, 1} : Finset (Fin 7)),
      ∃ α : ℝ, α ≠ 0 ∧ x 6 - x 4 = α • cross (F.N 4) (F.N 8) ∧
        0 < (-(1 / α)) * det3 (x 6 - x 4) (x v - x 4) u := by
    intro v hv
    refine edge_det3_same_sign F (t1 := 4) (t2 := 8) (A := 4) (B := 6) (p := 0) (q := 3)
      ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
      hu4 hu8 ?_ (by decide)
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl | rfl <;> decide
  obtain ⟨α2, hα2, he2, h25⟩ := e2 5 (by decide)
  obtain ⟨α2', _, he2', h22⟩ := e2 2 (by decide)
  obtain ⟨α2'', _, he2'', h21⟩ := e2 1 (by decide)
  have h2_5 : 0 < ρ * det3 (x 6 - x 4) (x 5 - x 4) u := by rwa [← hcyc12]
  have h2_same : ∀ {v : Fin 7} {α' : ℝ},
      x 6 - x 4 = α' • cross (F.N 4) (F.N 8) →
      0 < (-(1 / α')) * det3 (x 6 - x 4) (x v - x 4) u →
      0 < ρ * det3 (x 6 - x 4) (x v - x 4) u := by
    intro v α' he' hv'
    have heq : α' = α2 := by
      have := he'.symm.trans he2
      have hne : cross (F.N 4) (F.N 8) ≠ 0 := by
        intro hz; rw [hz, smul_zero] at he2
        exact sub_ne_zero.mpr (fun h => absurd ((Minimality.H24.SAT.inj_of_fac F) h) (by decide)) he2
      exact smul_left_injective ℝ hne this
    rw [heq] at hv'
    have hmul := mul_pos h25 hv'
    have hsq : (-(1 / α2)) * (-(1 / α2)) > 0 := mul_self_pos.mpr (neg_ne_zero.mpr (one_div_ne_zero hα2))
    have hpos_det : 0 < det3 (x 6 - x 4) (x 5 - x 4) u * det3 (x 6 - x 4) (x v - x 4) u := by
      have hid : (-(1 / α2) * det3 (x 6 - x 4) (x 5 - x 4) u) * (-(1 / α2) * det3 (x 6 - x 4) (x v - x 4) u) =
          (-(1 / α2) * -(1 / α2)) * (det3 (x 6 - x 4) (x 5 - x 4) u * det3 (x 6 - x 4) (x v - x 4) u) := by ring
      rw [hid] at hmul; exact pos_of_mul_pos_right hmul hsq.le
    have := mul_pos h2_5 hpos_det
    nlinarith [mul_self_pos.mpr (show det3 (x 6 - x 4) (x 5 - x 4) u ≠ 0 from fun h0 => by rw [h0, mul_zero] at h2_5; exact lt_irrefl 0 h2_5)]
  have h2_2 : 0 < ρ * det3 (x 6 - x 4) (x 2 - x 4) u := h2_same he2' h22
  have h2_1 : 0 < ρ * det3 (x 6 - x 4) (x 1 - x 4) u := h2_same he2'' h21
  have hcyc23 : det3 (x 6 - x 4) (x 2 - x 4) u = det3 (x 2 - x 6) (x 4 - x 6) u := by
    simp only [det3_expand', PiLp.sub_apply]; ring
  have e3 : ∀ v ∈ ({4, 5, 1} : Finset (Fin 7)),
      ∃ α : ℝ, α ≠ 0 ∧ x 2 - x 6 = α • cross (F.N 5) (F.N 7) ∧
        0 < (-(1 / α)) * det3 (x 2 - x 6) (x v - x 6) u := by
    intro v hv
    refine edge_det3_same_sign F (t1 := 5) (t2 := 7) (A := 6) (B := 2) (p := 1) (q := 3)
      ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
      hu5 hu7 ?_ (by decide)
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl | rfl <;> decide
  obtain ⟨α3, hα3, he3, h34⟩ := e3 4 (by decide)
  obtain ⟨α3', _, he3', h35⟩ := e3 5 (by decide)
  obtain ⟨α3'', _, he3'', h31⟩ := e3 1 (by decide)
  have h3_4 : 0 < ρ * det3 (x 2 - x 6) (x 4 - x 6) u := by rwa [← hcyc23]
  have h3_same : ∀ {v : Fin 7} {α' : ℝ},
      x 2 - x 6 = α' • cross (F.N 5) (F.N 7) →
      0 < (-(1 / α')) * det3 (x 2 - x 6) (x v - x 6) u →
      0 < ρ * det3 (x 2 - x 6) (x v - x 6) u := by
    intro v α' he' hv'
    have heq : α' = α3 := by
      have := he'.symm.trans he3
      have hne : cross (F.N 5) (F.N 7) ≠ 0 := by
        intro hz; rw [hz, smul_zero] at he3
        exact sub_ne_zero.mpr (fun h => absurd ((Minimality.H24.SAT.inj_of_fac F) h) (by decide)) he3
      exact smul_left_injective ℝ hne this
    rw [heq] at hv'
    have hmul := mul_pos h34 hv'
    have hsq : (-(1 / α3)) * (-(1 / α3)) > 0 := mul_self_pos.mpr (neg_ne_zero.mpr (one_div_ne_zero hα3))
    have hpos_det : 0 < det3 (x 2 - x 6) (x 4 - x 6) u * det3 (x 2 - x 6) (x v - x 6) u := by
      have hid : (-(1 / α3) * det3 (x 2 - x 6) (x 4 - x 6) u) * (-(1 / α3) * det3 (x 2 - x 6) (x v - x 6) u) =
          (-(1 / α3) * -(1 / α3)) * (det3 (x 2 - x 6) (x 4 - x 6) u * det3 (x 2 - x 6) (x v - x 6) u) := by ring
      rw [hid] at hmul; exact pos_of_mul_pos_right hmul hsq.le
    have := mul_pos h3_4 hpos_det
    nlinarith [mul_self_pos.mpr (show det3 (x 2 - x 6) (x 4 - x 6) u ≠ 0 from fun h0 => by rw [h0, mul_zero] at h3_4; exact lt_irrefl 0 h3_4)]
  have h3_5 : 0 < ρ * det3 (x 2 - x 6) (x 5 - x 6) u := h3_same he3' h35
  have h3_1 : 0 < ρ * det3 (x 2 - x 6) (x 1 - x 6) u := h3_same he3'' h31
  refine ⟨hρ_ne, fun i j hji hji1 => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;>
      first
      | exact absurd rfl hji
      | exact absurd rfl hji1
      | exact mul_self_pos.mpr hρ_ne
      | exact h0_6
      | exact h1_2
      | exact h1_6
      | exact h2_5
      | exact h2_2
      | exact h3_5
      | exact h3_4
  · fin_cases i
    · exact h0_1
    · exact h1_1
    · exact h2_1
    · exact h3_1

private theorem det3_perp_ne {N3 Nt a c : ℝ³} (hN3 : N3 ≠ 0) (ha : a ≠ 0)
    (h3a : ⟪N3, a⟫ = 0) (h3c : ⟪N3, c⟫ = 0) (hta : ⟪Nt, a⟫ = 0) (htc : ⟪Nt, c⟫ ≠ 0) :
    det3 a c N3 ≠ 0 := by
  intro h0
  have hN3_2 : ⟪N3, N3⟫ ≠ 0 := (real_inner_self_pos.mpr hN3).ne'
  have ha_2 : ⟪a, a⟫ ≠ 0 := (real_inner_self_pos.mpr ha).ne'
  have hcross : cross a c = 0 := by
    have hid : ⟪N3, N3⟫ • cross a c =
        det3 a c N3 • N3 + ⟪N3, a⟫ • cross N3 c - ⟪N3, c⟫ • cross N3 a := by
      ext i
      simp only [det3_expand', PiLp.smul_apply, PiLp.add_apply, PiLp.sub_apply, smul_eq_mul, inner3,
        cross_apply_zero, cross_apply_one, cross_apply_two]
      fin_cases i <;> simp <;> ring
    rw [h0, h3a, h3c, zero_smul, zero_smul, zero_smul, add_zero, sub_zero] at hid
    exact (smul_eq_zero.mp hid).resolve_left hN3_2
  have hcol : ⟪a, a⟫ • c = ⟪a, c⟫ • a := by
    have hid : ⟪a, a⟫ • c - ⟪a, c⟫ • a = -cross a (cross a c) := by
      rw [cross_cross_eq]; module
    have hcz : cross a (0 : ℝ³) = 0 := by
      ext i; fin_cases i <;> simp [cross_apply_zero, cross_apply_one, cross_apply_two]
    rw [hcross, hcz, neg_zero] at hid
    exact sub_eq_zero.mp hid
  have hnt := congrArg (fun w => ⟪Nt, w⟫) hcol
  simp only [real_inner_smul_right, hta, mul_zero] at hnt
  exact htc ((mul_eq_zero.mp hnt).resolve_left ha_2)

private theorem cJ_hmid (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (h3 : ⟪F.N 3, u⟫ = 0) (hU : ∀ t ∈ ({6, 7, 8} : Finset (Fin 9)), 0 < ⟪F.N t, u⟫)
    (hD : ∀ t ∈ ({0, 1, 2, 4, 5} : Finset (Fin 9)), ⟪F.N t, u⟫ < 0)
    (hdu : det3 (x 4 - x 5) (F.N 3) u ≠ 0) :
    ∀ q ∈ s0x_S24 3, (∀ j : ZMod 4, q ≠ cJ j) →
      ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
        x q = x (cJ 1) + s • (x (cJ 2) - x (cJ 1)) + δ • u := by
  have hx := Minimality.H24.SAT.inj_of_fac F
  have hN3 : F.N 3 ≠ 0 := fun h0 => by
    have hf := F.inner_sub 3 2 4
    rw [h0, inner_zero_left, F.zero 3 4 (by decide), sub_zero] at hf
    have := F.neg 3 2 (by decide); linarith
  have h345 : ⟪F.N 3, x 4 - x 5⟫ = 0 := by
    rw [F.inner_sub, F.zero 3 4 (by decide), F.zero 3 5 (by decide), sub_self]
  have h354 : ⟪F.N 3, x 5 - x 4⟫ = 0 := by
    rw [F.inner_sub, F.zero 3 5 (by decide), F.zero 3 4 (by decide), sub_self]
  set D := det3 (x 4 - x 5) u (F.N 3)
  have hD_ne : D ≠ 0 := by
    have hswap : D = -det3 (x 4 - x 5) (F.N 3) u := by
      simp only [D, det3_expand']; ring
    rw [hswap, neg_ne_zero]; exact hdu
  have solve_cramer : ∀ (q : Fin 7), q ∈ s0x_S24 3 →
      let s := det3 (x q - x 5) u (F.N 3) / D
      let δ := det3 (x 4 - x 5) (x q - x 5) (F.N 3) / D
      x q = x 5 + s • (x 4 - x 5) + δ • u := by
    intro q hq s δ
    have h3q : ⟪F.N 3, x q - x 5⟫ = 0 := by
      rw [F.inner_sub, F.zero 3 q hq, F.zero 3 5 (by decide), sub_self]
    have hsub : x q - x 5 = s • (x 4 - x 5) + δ • u := by
      apply smul_right_injective ℝ³ hD_ne
      dsimp only
      rw [smul_add, smul_smul, mul_div_cancel₀ _ hD_ne, smul_smul, mul_div_cancel₀ _ hD_ne]
      have hid : D • (x q - x 5) - (det3 (x q - x 5) u (F.N 3) • (x 4 - x 5) +
          det3 (x 4 - x 5) (x q - x 5) (F.N 3) • u) =
          ⟪F.N 3, x q - x 5⟫ • cross (x 4 - x 5) u + ⟪F.N 3, x 4 - x 5⟫ • cross u (x q - x 5) +
          ⟪F.N 3, u⟫ • cross (x q - x 5) (x 4 - x 5) := by
        ext i
        simp only [D, det3_expand', PiLp.smul_apply, PiLp.add_apply, PiLp.sub_apply, smul_eq_mul, inner3,
          cross_apply_zero, cross_apply_one, cross_apply_two]
        fin_cases i <;> simp <;> ring
      rw [h3q, h345, h3, zero_smul, zero_smul, zero_smul, add_zero, add_zero] at hid
      exact sub_eq_zero.mp hid
    rw [add_assoc, ← hsub]; abel
  have mid_of_signs : ∀ (q : Fin 7) (hq : q ∈ s0x_S24 3),
      (0 < det3 (x q - x 5) u (F.N 3) ∧ 0 < det3 (x 4 - x q) u (F.N 3) ∨
       det3 (x q - x 5) u (F.N 3) < 0 ∧ det3 (x 4 - x q) u (F.N 3) < 0) →
      det3 (x 4 - x 5) (x q - x 5) (F.N 3) ≠ 0 →
      ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧ x q = x (cJ 1) + s • (x (cJ 2) - x (cJ 1)) + δ • u := by
    intro q hq hsign hdel
    have hc1 : cJ 1 = 5 := by decide
    have hc2 : cJ 2 = 4 := by decide
    rw [hc1, hc2]
    refine ⟨det3 (x q - x 5) u (F.N 3) / D, det3 (x 4 - x 5) (x q - x 5) (F.N 3) / D,
      ?_, ?_, div_ne_zero hdel hD_ne, solve_cramer q hq⟩
    · have hsum : det3 (x q - x 5) u (F.N 3) + det3 (x 4 - x q) u (F.N 3) = D := by
        simp only [D, det3_expand', PiLp.sub_apply]; ring
      rcases hsign with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact div_pos h1 (by linarith)
      · exact div_pos_of_neg_of_neg h1 (by linarith)
    · have hsum : det3 (x q - x 5) u (F.N 3) + det3 (x 4 - x q) u (F.N 3) = D := by
        simp only [D, det3_expand', PiLp.sub_apply]; ring
      rcases hsign with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [div_lt_one (by linarith)]; linarith
      · rw [div_lt_iff_of_neg (by linarith)]; linarith
  intro q hq hqn
  have hq03 : q = 0 ∨ q = 3 := by
    fin_cases q
    · exact Or.inl rfl
    · exact absurd (by decide : (1 : Fin 7) ∉ s0x_S24 3) (fun h => h hq)
    · exact absurd (by decide : (2 : Fin 7) ∉ s0x_S24 3) (fun h => h hq)
    · exact Or.inr rfl
    · exact absurd (by decide : (4 : Fin 7) = cJ 2) (hqn 2)
    · exact absurd (by decide : (5 : Fin 7) = cJ 1) (hqn 1)
    · exact absurd (by decide : (6 : Fin 7) ∉ s0x_S24 3) (fun h => h hq)
  rcases hq03 with rfl | rfl
  · have h30 : ⟪F.N 3, x 0 - x 5⟫ = 0 := by
      rw [F.inner_sub, F.zero 3 0 (by decide), F.zero 3 5 (by decide), sub_self]
    have h340 : ⟪F.N 3, x 4 - x 0⟫ = 0 := by
      rw [F.inner_sub, F.zero 3 4 (by decide), F.zero 3 0 (by decide), sub_self]
    have h205 : ⟪F.N 2, x 0 - x 5⟫ = 0 := by
      rw [F.inner_sub, F.zero 2 0 (by decide), F.zero 2 5 (by decide), sub_self]
    have h440 : ⟪F.N 4, x 4 - x 0⟫ = 0 := by
      rw [F.inner_sub, F.zero 4 4 (by decide), F.zero 4 0 (by decide), sub_self]
    have h24 : ⟪F.N 2, x 4 - x 5⟫ < 0 := by
      rw [F.inner_sub, F.zero 2 5 (by decide), sub_zero]; exact F.neg 2 4 (by decide)
    have h45 : ⟪F.N 4, x 5 - x 4⟫ < 0 := by
      rw [F.inner_sub, F.zero 4 4 (by decide), sub_zero]; exact F.neg 4 5 (by decide)
    have h05_ne : x 0 - x 5 ≠ 0 := sub_ne_zero.mpr (fun h => absurd (hx h) (by decide))
    have h40_ne : x 4 - x 0 ≠ 0 := sub_ne_zero.mpr (fun h => absurd (hx h) (by decide))
    have eA := det3_perp_plane hN3 h05_ne h30 h345 h3 h205
    have eB := det3_perp_plane hN3 h40_ne h340 h354 h3 h440
    have hd_eq : det3 (x 0 - x 5) (x 4 - x 5) (F.N 3) = det3 (x 4 - x 0) (x 5 - x 4) (F.N 3) := by
      simp only [det3_expand', PiLp.sub_apply]; ring
    have hd_eq2 : det3 (x 4 - x 5) (x 0 - x 5) (F.N 3) = -det3 (x 0 - x 5) (x 4 - x 5) (F.N 3) := by
      simp only [det3_expand']; ring
    have hΔ_ne : det3 (x 0 - x 5) (x 4 - x 5) (F.N 3) ≠ 0 :=
      det3_perp_ne hN3 h05_ne h30 h345 h205 h24.ne
    have hu2 := hD 2 (by decide)
    have hu4 := hD 4 (by decide)
    refine mid_of_signs 0 hq ?_ (by rw [hd_eq2, neg_ne_zero]; exact hΔ_ne)
    rcases lt_or_gt_of_ne hΔ_ne with hΔ | hΔ
    · right; constructor
      · have hmul : 0 < det3 (x 0 - x 5) (x 4 - x 5) (F.N 3) * ⟪F.N 2, u⟫ := mul_pos_of_neg_of_neg hΔ hu2
        rw [eA] at hmul; exact neg_of_mul_pos_left hmul h24.le
      · have hmul : 0 < det3 (x 4 - x 0) (x 5 - x 4) (F.N 3) * ⟪F.N 4, u⟫ := by
          rw [← hd_eq]; exact mul_pos_of_neg_of_neg hΔ hu4
        rw [eB] at hmul; exact neg_of_mul_pos_left hmul h45.le
    · left; constructor
      · have hmul : det3 (x 0 - x 5) (x 4 - x 5) (F.N 3) * ⟪F.N 2, u⟫ < 0 := mul_neg_of_pos_of_neg hΔ hu2
        rw [eA] at hmul; exact pos_of_mul_neg_left hmul h24.le
      · have hmul : det3 (x 4 - x 0) (x 5 - x 4) (F.N 3) * ⟪F.N 4, u⟫ < 0 := by
          rw [← hd_eq]; exact mul_neg_of_pos_of_neg hΔ hu4
        rw [eB] at hmul; exact pos_of_mul_neg_left hmul h45.le
  · have h33 : ⟪F.N 3, x 3 - x 5⟫ = 0 := by
      rw [F.inner_sub, F.zero 3 3 (by decide), F.zero 3 5 (by decide), sub_self]
    have h343 : ⟪F.N 3, x 4 - x 3⟫ = 0 := by
      rw [F.inner_sub, F.zero 3 4 (by decide), F.zero 3 3 (by decide), sub_self]
    have h635 : ⟪F.N 6, x 3 - x 5⟫ = 0 := by
      rw [F.inner_sub, F.zero 6 3 (by decide), F.zero 6 5 (by decide), sub_self]
    have h843 : ⟪F.N 8, x 4 - x 3⟫ = 0 := by
      rw [F.inner_sub, F.zero 8 4 (by decide), F.zero 8 3 (by decide), sub_self]
    have h64 : ⟪F.N 6, x 4 - x 5⟫ < 0 := by
      rw [F.inner_sub, F.zero 6 5 (by decide), sub_zero]; exact F.neg 6 4 (by decide)
    have h85 : ⟪F.N 8, x 5 - x 4⟫ < 0 := by
      rw [F.inner_sub, F.zero 8 4 (by decide), sub_zero]; exact F.neg 8 5 (by decide)
    have h35_ne : x 3 - x 5 ≠ 0 := sub_ne_zero.mpr (fun h => absurd (hx h) (by decide))
    have h43_ne : x 4 - x 3 ≠ 0 := sub_ne_zero.mpr (fun h => absurd (hx h) (by decide))
    have eA := det3_perp_plane hN3 h35_ne h33 h345 h3 h635
    have eB := det3_perp_plane hN3 h43_ne h343 h354 h3 h843
    have hd_eq : det3 (x 3 - x 5) (x 4 - x 5) (F.N 3) = det3 (x 4 - x 3) (x 5 - x 4) (F.N 3) := by
      simp only [det3_expand', PiLp.sub_apply]; ring
    have hd_eq2 : det3 (x 4 - x 5) (x 3 - x 5) (F.N 3) = -det3 (x 3 - x 5) (x 4 - x 5) (F.N 3) := by
      simp only [det3_expand']; ring
    have hΔ_ne : det3 (x 3 - x 5) (x 4 - x 5) (F.N 3) ≠ 0 :=
      det3_perp_ne hN3 h35_ne h33 h345 h635 h64.ne
    have hu6 := hU 6 (by decide)
    have hu8 := hU 8 (by decide)
    refine mid_of_signs 3 hq ?_ (by rw [hd_eq2, neg_ne_zero]; exact hΔ_ne)
    rcases lt_or_gt_of_ne hΔ_ne with hΔ | hΔ
    · left; constructor
      · have hmul : det3 (x 3 - x 5) (x 4 - x 5) (F.N 3) * ⟪F.N 6, u⟫ < 0 := mul_neg_of_neg_of_pos hΔ hu6
        rw [eA] at hmul; exact pos_of_mul_neg_left hmul h64.le
      · have hmul : det3 (x 4 - x 3) (x 5 - x 4) (F.N 3) * ⟪F.N 8, u⟫ < 0 := by
          rw [← hd_eq]; exact mul_neg_of_neg_of_pos hΔ hu8
        rw [eB] at hmul; exact pos_of_mul_neg_left hmul h85.le
    · right; constructor
      · have hmul : 0 < det3 (x 3 - x 5) (x 4 - x 5) (F.N 3) * ⟪F.N 6, u⟫ := mul_pos hΔ hu6
        rw [eA] at hmul; exact neg_of_mul_pos_left hmul h64.le
      · have hmul : 0 < det3 (x 4 - x 3) (x 5 - x 4) (F.N 3) * ⟪F.N 8, u⟫ := by
          rw [← hd_eq]; exact mul_pos hΔ hu8
        rw [eB] at hmul; exact neg_of_mul_pos_left hmul h85.le

private theorem strictUnimodal_four_of_robUni {z : ZMod 4 → ℝ}
    (hinj : Function.Injective z) (hrob : RobUni z) : StrictUnimodal z := by
  refine ⟨fun i => hinj.ne (by intro h; exact absurd (by linear_combination h.symm : (1 : ZMod 4) = 0) (by decide)), ?_⟩
  let S := univ.filter fun i : ZMod 4 => z (i - 1) < z i ∧ z (i + 1) < z i
  have hS_nonempty : S.Nonempty := by
    obtain ⟨M, _, hM⟩ := Finset.exists_max_image univ z ⟨0, mem_univ 0⟩
    refine ⟨M, mem_filter.mpr ⟨mem_univ M, ?_, ?_⟩⟩
    · exact lt_of_le_of_ne (hM _ (mem_univ _)) (hinj.ne (by intro h; exact absurd (by linear_combination -h : (1 : ZMod 4) = 0) (by decide)))
    · exact lt_of_le_of_ne (hM _ (mem_univ _)) (hinj.ne (by intro h; exact absurd (by linear_combination h : (1 : ZMod 4) = 0) (by decide)))
  have hS_le : S.card ≤ 1 := by
    by_contra hgt
    push Not at hgt
    obtain ⟨B, hB, C, hC, hBC⟩ := Finset.one_lt_card.mp hgt
    simp only [S, mem_filter, mem_univ, true_and] at hB hC
    have hrel : C = B + 1 ∨ C = B + 2 ∨ C = B + 3 := by
      have hCB : C - B = 0 ∨ C - B = 1 ∨ C - B = 2 ∨ C - B = 3 := by
        fin_cases C <;> fin_cases B <;> decide
      rcases hCB with h | h | h | h
      · exact absurd (sub_eq_zero.mp h).symm hBC
      · left; linear_combination h
      · right; left; linear_combination h
      · right; right; linear_combination h
    rcases hrel with rfl | rfl | rfl
    · have : (B + 1 : ZMod 4) - 1 = B := by ring
      rw [this] at hC; exact lt_asymm hB.2 hC.1
    · have hB3 : B + (3 : ZMod 4) = B - 1 := by rw [sub_eq_add_neg, show (-1 : ZMod 4) = 3 by decide]
      have hB21 : (B + 2 : ZMod 4) - 1 = B + 1 := by ring
      have hB23 : (B + 2 : ZMod 4) + 1 = B + 3 := by ring
      rw [hB21, hB23] at hC
      exact hrob B 1 2 3 (by decide) (by decide) (by decide) (by decide)
        ⟨hB.2.le, hC.1.le, (by simpa [Nat.cast_ofNat, hB3] using hB.1.le), hC.2.le⟩
    · have hB3 : B + (3 : ZMod 4) = B - 1 := by rw [sub_eq_add_neg, show (-1 : ZMod 4) = 3 by decide]
      have : (B + 3 : ZMod 4) + 1 = B := by rw [add_assoc, show (3 : ZMod 4) + 1 = 0 by decide, add_zero]
      rw [this, hB3] at hC; exact lt_asymm hB.1 hC.2
  have hS_ge : 1 ≤ S.card := Finset.card_pos.mpr hS_nonempty
  exact le_antisymm hS_le hS_ge

private theorem det3_ortho_sq {u w n : ℝ³}
    (hwu : ⟪w, u⟫ = 0) (hwn : ⟪w, n⟫ = 0) (hnu : ⟪n, u⟫ = 0) :
    (det3 w n u) ^ 2 = ⟪w, w⟫ * ⟪n, n⟫ * ⟪u, u⟫ := by
  have hid : (det3 w n u) ^ 2 + ⟪w, n⟫ ^ 2 * ⟪u, u⟫ + ⟪w, u⟫ ^ 2 * ⟪n, n⟫ + ⟪n, u⟫ ^ 2 * ⟪w, w⟫ -
      2 * ⟪w, n⟫ * ⟪n, u⟫ * ⟪w, u⟫ = ⟪w, w⟫ * ⟪n, n⟫ * ⟪u, u⟫ := by
    simp only [det3_expand', inner3]; ring
  rw [hwu, hwn, hnu] at hid; linarith

private theorem det3_ortho_frame {u w n a b : ℝ³} (hu : u ≠ 0)
    (hau : ⟪a, u⟫ = 0) (hbu : ⟪b, u⟫ = 0) (hwu : ⟪w, u⟫ = 0)
    (hwn : ⟪w, n⟫ = 0) (hnu : ⟪n, u⟫ = 0) :
    ⟪w, w⟫ * ⟪n, n⟫ * det3 a b u =
      (⟪a, w⟫ * ⟪b, n⟫ - ⟪b, w⟫ * ⟪a, n⟫) * det3 w n u := by
  have hu2 : ⟪u, u⟫ ≠ 0 := (real_inner_self_pos.mpr hu).ne'
  have h1 : det3 w n u * det3 a b u = ⟪u, u⟫ * (⟪a, w⟫ * ⟪b, n⟫ - ⟪b, w⟫ * ⟪a, n⟫) := by
    have hid : det3 w n u * det3 a b u =
        ⟪u, u⟫ * (⟪w, a⟫ * ⟪n, b⟫ - ⟪w, b⟫ * ⟪n, a⟫) +
        ⟪w, u⟫ * (⟪n, a⟫ * ⟪u, b⟫ - ⟪n, b⟫ * ⟪u, a⟫) +
        ⟪n, u⟫ * (⟪w, b⟫ * ⟪u, a⟫ - ⟪w, a⟫ * ⟪u, b⟫) := by
      simp only [det3_expand', inner3]; ring
    have hwa : ⟪w, a⟫ = ⟪a, w⟫ := real_inner_comm _ _
    have hwb : ⟪w, b⟫ = ⟪b, w⟫ := real_inner_comm _ _
    have hna : ⟪n, a⟫ = ⟪a, n⟫ := real_inner_comm _ _
    have hnb : ⟪n, b⟫ = ⟪b, n⟫ := real_inner_comm _ _
    rw [hwu, hnu, zero_mul, zero_mul, add_zero, add_zero, hwa, hwb, hna, hnb] at hid
    exact hid
  have hsq := det3_ortho_sq hwu hwn hnu
  apply mul_left_cancel₀ hu2
  calc ⟪u, u⟫ * (⟪w, w⟫ * ⟪n, n⟫ * det3 a b u)
      = (⟪w, w⟫ * ⟪n, n⟫ * ⟪u, u⟫) * det3 a b u := by ring
    _ = det3 w n u * (det3 w n u * det3 a b u) := by rw [← hsq]; ring
    _ = det3 w n u * (⟪u, u⟫ * (⟪a, w⟫ * ⟪b, n⟫ - ⟪b, w⟫ * ⟪a, n⟫)) := by rw [h1]
    _ = ⟪u, u⟫ * ((⟪a, w⟫ * ⟪b, n⟫ - ⟪b, w⟫ * ⟪a, n⟫) * det3 w n u) := by ring

private theorem quad_robUni_of_signs {v0 v2 v3 z2 z6 : ℝ} (hz2 : z2 < 0) (hz6 : z6 < 0)
    (hv2 : v2 ≠ 0)
    (hq12 : 0 < (v2 * z2) * ((v3 - v2) * z2 - (v0 - v2) * z6))
    (hq13 : 0 < (v2 * z2) * ((v0 - v3) * (-z6) - (-v3) * (z2 - z6)))
    {B : ZMod 4} (hB : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3)
    (h01 : (if B = 0 then v0 else if B = 1 then 0 else if B = 2 then v2 else v3) ≥
           (if B + 1 = 0 then v0 else if B + 1 = 1 then 0 else if B + 1 = 2 then v2 else v3))
    (h21 : (if B + 2 = 0 then v0 else if B + 2 = 1 then 0 else if B + 2 = 2 then v2 else v3) ≥
           (if B + 1 = 0 then v0 else if B + 1 = 1 then 0 else if B + 1 = 2 then v2 else v3))
    (h03 : (if B = 0 then v0 else if B = 1 then 0 else if B = 2 then v2 else v3) ≥
           (if B + 3 = 0 then v0 else if B + 3 = 1 then 0 else if B + 3 = 2 then v2 else v3))
    (h23 : (if B + 2 = 0 then v0 else if B + 2 = 1 then 0 else if B + 2 = 2 then v2 else v3) ≥
           (if B + 3 = 0 then v0 else if B + 3 = 1 then 0 else if B + 3 = 2 then v2 else v3)) :
    False := by
  have hq12' : 0 < v2 * z2 * ((v2 - v3) * (-z2) - (v2 - v0) * (-z6)) := by linarith
  have hq13' : 0 < v2 * z2 * (v0 * (-z6) - v3 * (-z2)) := by linarith
  have e01 : (0 : ZMod 4) + 1 = 1 := by decide
  have e02 : (0 : ZMod 4) + 2 = 2 := by decide
  have e03 : (0 : ZMod 4) + 3 = 3 := by decide
  have e11 : (1 : ZMod 4) + 1 = 2 := by decide
  have e12 : (1 : ZMod 4) + 2 = 3 := by decide
  have e13 : (1 : ZMod 4) + 3 = 0 := by decide
  have e21 : (2 : ZMod 4) + 1 = 3 := by decide
  have e22 : (2 : ZMod 4) + 2 = 0 := by decide
  have e23 : (2 : ZMod 4) + 3 = 1 := by decide
  have e31 : (3 : ZMod 4) + 1 = 0 := by decide
  have e32 : (3 : ZMod 4) + 2 = 1 := by decide
  have e33 : (3 : ZMod 4) + 3 = 2 := by decide
  have n10 : (1 : ZMod 4) ≠ 0 := by decide
  have n20 : (2 : ZMod 4) ≠ 0 := by decide
  have n21 : (2 : ZMod 4) ≠ 1 := by decide
  have n30 : (3 : ZMod 4) ≠ 0 := by decide
  have n31 : (3 : ZMod 4) ≠ 1 := by decide
  have n32 : (3 : ZMod 4) ≠ 2 := by decide
  rcases lt_or_gt_of_ne hv2 with hv2_neg | hv2_pos
  · have hpos : 0 < v2 * z2 := mul_pos_of_neg_of_neg hv2_neg hz2
    have h1 : 0 < (v2 - v3) * (-z2) - (v2 - v0) * (-z6) := pos_of_mul_pos_right hq12' hpos.le
    have h2 : 0 < v0 * (-z6) - v3 * (-z2) := pos_of_mul_pos_right hq13' hpos.le
    rcases hB with rfl | rfl | rfl | rfl
    · simp only [e01, e02, e03, n10, n20, n21, n30, n31, n32, ↓reduceIte] at h01 h21 h03 h23; linarith
    · simp only [e11, e12, e13, n10, n20, n21, n30, n31, n32, ↓reduceIte] at h01 h21 h03 h23
      by_cases hv20 : v2 ≤ v0
      · have hmul_l : v0 * ((v2 - v3) * (-z2) - (v2 - v0) * (-z6)) + (v2 - v0) * (v0 * (-z6) - v3 * (-z2)) < 0 := by
          have ha : v0 * ((v2 - v3) * (-z2) - (v2 - v0) * (-z6)) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h03 h1.le
          have hb : (v2 - v0) * (v0 * (-z6) - v3 * (-z2)) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) h2.le
          rcases lt_or_eq_of_le h03 with h03' | h03'
          · have : v0 * ((v2 - v3) * (-z2) - (v2 - v0) * (-z6)) < 0 := mul_neg_of_neg_of_pos h03' h1
            linarith
          · have : (v2 - v0) * (v0 * (-z6) - v3 * (-z2)) < 0 := mul_neg_of_neg_of_pos (by linarith) h2
            linarith
        have hmul_r : 0 ≤ v2 * (v0 - v3) * (-z2) :=
          mul_nonneg (mul_nonneg_of_nonpos_of_nonpos hv2_neg.le (by linarith)) (by linarith)
        have hid : v0 * ((v2 - v3) * (-z2) - (v2 - v0) * (-z6)) + (v2 - v0) * (v0 * (-z6) - v3 * (-z2)) =
            v2 * (v0 - v3) * (-z2) := by ring
        linarith
      · push Not at hv20
        have hm1 : (v2 - v3) * (-z2) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
        have hm2 : 0 < (v2 - v0) * (-z6) := mul_pos (by linarith) (by linarith)
        linarith
    · simp only [e21, e22, e23, n10, n20, n21, n30, n31, n32, ↓reduceIte] at h01 h21 h03 h23; linarith
    · simp only [e31, e32, e33, n10, n20, n21, n30, n31, n32, ↓reduceIte] at h01 h21 h03 h23
      by_cases hv20 : v2 ≤ v0
      · have hmul_l : v0 * ((v2 - v3) * (-z2) - (v2 - v0) * (-z6)) + (v2 - v0) * (v0 * (-z6) - v3 * (-z2)) < 0 := by
          have ha : v0 * ((v2 - v3) * (-z2) - (v2 - v0) * (-z6)) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h21 h1.le
          have hb : (v2 - v0) * (v0 * (-z6) - v3 * (-z2)) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) h2.le
          rcases lt_or_eq_of_le h21 with h21' | h21'
          · have : v0 * ((v2 - v3) * (-z2) - (v2 - v0) * (-z6)) < 0 := mul_neg_of_neg_of_pos h21' h1
            linarith
          · have : (v2 - v0) * (v0 * (-z6) - v3 * (-z2)) < 0 := mul_neg_of_neg_of_pos (by linarith) h2
            linarith
        have hmul_r : 0 ≤ v2 * (v0 - v3) * (-z2) :=
          mul_nonneg (mul_nonneg_of_nonpos_of_nonpos hv2_neg.le (by linarith)) (by linarith)
        have hid : v0 * ((v2 - v3) * (-z2) - (v2 - v0) * (-z6)) + (v2 - v0) * (v0 * (-z6) - v3 * (-z2)) =
            v2 * (v0 - v3) * (-z2) := by ring
        linarith
      · push Not at hv20
        have hm1 : (v2 - v3) * (-z2) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
        have hm2 : 0 < (v2 - v0) * (-z6) := mul_pos (by linarith) (by linarith)
        linarith
  · have hneg : v2 * z2 < 0 := mul_neg_of_pos_of_neg hv2_pos hz2
    have h1 : (v2 - v3) * (-z2) - (v2 - v0) * (-z6) < 0 := neg_of_mul_pos_right hq12' hneg.le
    have h2 : v0 * (-z6) - v3 * (-z2) < 0 := neg_of_mul_pos_right hq13' hneg.le
    rcases hB with rfl | rfl | rfl | rfl
    · simp only [e01, e02, e03, n10, n20, n21, n30, n31, n32, ↓reduceIte] at h01 h21 h03 h23
      by_cases hv20 : v2 ≤ v0
      · have hm1 : 0 ≤ (v2 - v3) * (-z2) := mul_nonneg (by linarith) (by linarith)
        have hm2 : (v2 - v0) * (-z6) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
        linarith
      · push Not at hv20
        have hmul_l : v0 * ((v2 - v3) * (-z2) - (v2 - v0) * (-z6)) + (v2 - v0) * (v0 * (-z6) - v3 * (-z2)) < 0 := by
          have ha : v0 * ((v2 - v3) * (-z2) - (v2 - v0) * (-z6)) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h01 h1.le
          have hb : (v2 - v0) * (v0 * (-z6) - v3 * (-z2)) < 0 := mul_neg_of_pos_of_neg (by linarith) h2
          linarith
        have hmul_r : 0 ≤ v2 * (v0 - v3) * (-z2) :=
          mul_nonneg (mul_nonneg hv2_pos.le (by linarith)) (by linarith)
        have hid : v0 * ((v2 - v3) * (-z2) - (v2 - v0) * (-z6)) + (v2 - v0) * (v0 * (-z6) - v3 * (-z2)) =
            v2 * (v0 - v3) * (-z2) := by ring
        linarith
    · simp only [e11, e12, e13, n10, n20, n21, n30, n31, n32, ↓reduceIte] at h01 h21 h03 h23; linarith
    · simp only [e21, e22, e23, n10, n20, n21, n30, n31, n32, ↓reduceIte] at h01 h21 h03 h23
      by_cases hv20 : v2 ≤ v0
      · have hm1 : 0 ≤ (v2 - v3) * (-z2) := mul_nonneg (by linarith) (by linarith)
        have hm2 : (v2 - v0) * (-z6) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
        linarith
      · push Not at hv20
        have hmul_l : v0 * ((v2 - v3) * (-z2) - (v2 - v0) * (-z6)) + (v2 - v0) * (v0 * (-z6) - v3 * (-z2)) < 0 := by
          have ha : v0 * ((v2 - v3) * (-z2) - (v2 - v0) * (-z6)) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h23 h1.le
          have hb : (v2 - v0) * (v0 * (-z6) - v3 * (-z2)) < 0 := mul_neg_of_pos_of_neg (by linarith) h2
          linarith
        have hmul_r : 0 ≤ v2 * (v0 - v3) * (-z2) :=
          mul_nonneg (mul_nonneg hv2_pos.le (by linarith)) (by linarith)
        have hid : v0 * ((v2 - v3) * (-z2) - (v2 - v0) * (-z6)) + (v2 - v0) * (v0 * (-z6) - v3 * (-z2)) =
            v2 * (v0 - v3) * (-z2) := by ring
        linarith
    · simp only [e31, e32, e33, n10, n20, n21, n30, n31, n32, ↓reduceIte] at h01 h21 h03 h23; linarith

/-- **EJ(ii-b), bridge lemma.**  Under `hf3`, `hoff`, and `hinj_J` (no pair of `cJ` vertices aligned along
`F.N 3`), the segment `(WL, WR)` contains a `FaceChordView F 3` on the 4-rim `cJ = ![2, 5, 4, 6]`. -/
theorem faceChordView_J54 (F : S0xFac 9 s0x_S24 x) (hne : 0 < caL x ∨ 0 < caR x)
    (hn : (∃ p ∈ diagPairs, ⟪x (cJ p.1) - x (cJ p.2), WL x⟫ < 0) ∨
      ∃ p ∈ diagPairs, ⟪x (cJ p.1) - x (cJ p.2), WR x⟫ < 0)
    (hp : (∃ p ∈ diagPairs, 0 < ⟪x (cJ p.1) - x (cJ p.2), WL x⟫) ∨
      ∃ p ∈ diagPairs, 0 < ⟪x (cJ p.1) - x (cJ p.2), WR x⟫)
    (hf3 : F.f 3 (x 2) ≠ F.f 3 (x 6))
    (hoff : ⟪F.N 3, cross (x 4 - x 5) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 5)⟫ ≠ 0 ∨
      ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 5, x 4 - x 5⟫ < 0 ∨
      ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4, x 5 - x 4⟫ < 0)
    (hinj_J : ∀ i j : ZMod 4, i ≠ j →
      ⟪x (cJ i) - x (cJ j), WL x⟫ ≠ 0 ∨ ⟪x (cJ i) - x (cJ j), WR x⟫ ≠ 0) :
    FaceChordView F 3 := by
  have exists_s : ∃ s : ℝ, 0 < s ∧ s < 1 ∧
      (∀ i j : ZMod 4, i ≠ j → ⟪x (cJ i) - x (cJ j), (1 - s) • WL x + s • WR x⟫ ≠ 0) ∧
      RobUni (fun i => ⟪x (cJ i), (1 - s) • WL x + s • WR x⟫) := by
    let g : ℝ → ℝ³ := fun s => (1 - s) • WL x + s • WR x
    have hg_cont : Continuous g :=
      ((continuous_const.sub continuous_id).smul continuous_const).add (continuous_id.smul continuous_const)
    let A : Set ℝ³ := {u | ∃ s : ℝ, 0 < s ∧ s < 1 ∧ u = g s}
    have hAc : Convex ℝ A := by
      rintro _ ⟨s₁, hs10, hs11, rfl⟩ _ ⟨s₂, hs20, hs21, rfl⟩ a b ha hb hab
      refine ⟨a * s₁ + b * s₂, ?_, ?_, ?_⟩
      · rcases ha.lt_or_eq with ha' | rfl
        · nlinarith
        · simp at hab; subst hab; simpa using hs20
      · rcases ha.lt_or_eq with ha' | rfl
        · nlinarith
        · simp at hab; subst hab; simpa using hs21
      · dsimp [g]; rw [show 1 - (a * s₁ + b * s₂) = a * (1 - s₁) + b * (1 - s₂) by linarith]
        module
    have hWL_cl : WL x ∈ closure A := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      have htend : Filter.Tendsto g (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (WL x)) := by
        have h0 : g 0 = WL x := by simp [g]
        rw [← h0]
        exact hg_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have h_ne : (nhdsWithin (0 : ℝ) (Set.Ioi 0)).NeBot := nhdsWithin_Ioi_neBot (le_refl (0 : ℝ))
      have h_lt1 : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0), s < 1 :=
        nhdsWithin_le_nhds (eventually_lt_nhds (by norm_num))
      have h_ball : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0), g s ∈ Metric.ball (WL x) ε :=
        htend.eventually (Metric.ball_mem_nhds _ hε)
      obtain ⟨s, hs0, hs1, hball⟩ := @Filter.Eventually.exists _ _ _ h_ne (Filter.Eventually.and self_mem_nhdsWithin (h_lt1.and h_ball))
      exact ⟨g s, ⟨s, hs0, hs1, rfl⟩, by simpa [dist_comm] using hball⟩
    have hWR_cl : WR x ∈ closure A := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      have htend : Filter.Tendsto (fun t : ℝ => g (1 - t)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (WR x)) := by
        have h1 : g (1 - 0) = WR x := by simp [g]
        rw [← h1]
        exact (hg_cont.comp (continuous_const.sub continuous_id)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have h_ne : (nhdsWithin (0 : ℝ) (Set.Ioi 0)).NeBot := nhdsWithin_Ioi_neBot (le_refl (0 : ℝ))
      have h_lt1 : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t < 1 :=
        nhdsWithin_le_nhds (eventually_lt_nhds (by norm_num))
      have h_ball : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), g (1 - t) ∈ Metric.ball (WR x) ε :=
        htend.eventually (Metric.ball_mem_nhds _ hε)
      obtain ⟨t, ht0, ht1, hball⟩ := @Filter.Eventually.exists _ _ _ h_ne (Filter.Eventually.and self_mem_nhdsWithin (h_lt1.and h_ball))
      exact ⟨g (1 - t), ⟨1 - t, by linarith, by linarith, rfl⟩, by simpa [dist_comm] using hball⟩
    let f : {p // p ∈ diagPairs} → ℝ³ →ₗ[ℝ] ℝ := fun p =>
      (innerSL ℝ (x (cJ p.1.1) - x (cJ p.1.2))).toLinearMap
    have hfc : ∀ p, Continuous (f p) := fun p => (innerSL ℝ _).continuous
    have h_inj_near : ∀ s₀ : ℝ, ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ∀ i j : ZMod 4, i ≠ j → ⟪x (cJ i) - x (cJ j), g (s₀ + t)⟫ ≠ 0 := by
      intro s₀
      refine Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => ?_
      by_cases hij : i = j
      · exact Filter.Eventually.of_forall fun _ h => absurd hij h
      · have hne_ij := hinj_J i j hij
        have heq : ∀ t : ℝ, ⟪x (cJ i) - x (cJ j), g (s₀ + t)⟫ =
            ⟪x (cJ i) - x (cJ j), g s₀⟫ + t * (⟪x (cJ i) - x (cJ j), WR x⟫ - ⟪x (cJ i) - x (cJ j), WL x⟫) := by
          intro t; dsimp [g]; simp only [inner_add_right, real_inner_smul_right]; ring
        have hdiff_ne : ⟪x (cJ i) - x (cJ j), g s₀⟫ ≠ 0 ∨
            ⟪x (cJ i) - x (cJ j), WR x⟫ - ⟪x (cJ i) - x (cJ j), WL x⟫ ≠ 0 := by
          by_contra hboth; push Not at hboth
          rcases hboth with ⟨h1, h2⟩
          have hW : ⟪x (cJ i) - x (cJ j), WR x⟫ = ⟪x (cJ i) - x (cJ j), WL x⟫ := sub_eq_zero.mp h2
          dsimp [g] at h1
          simp only [inner_add_right, real_inner_smul_right, hW] at h1
          have hL0 : ⟪x (cJ i) - x (cJ j), WL x⟫ = 0 := by linarith
          rw [hL0] at hW
          rcases hne_ij with h | h <;> exact h (by assumption)
        rcases lt_trichotomy ⟪x (cJ i) - x (cJ j), g s₀⟫ 0 with h0 | h0 | h0
        · filter_upwards [Minimality.eventually_pos_affine
            (A := -⟪x (cJ i) - x (cJ j), g s₀⟫)
            (B := -(⟪x (cJ i) - x (cJ j), WR x⟫ - ⟪x (cJ i) - x (cJ j), WL x⟫))
            (Or.inl (by linarith))] with t ht _
          rw [heq t]; linarith
        · have hB : ⟪x (cJ i) - x (cJ j), WR x⟫ - ⟪x (cJ i) - x (cJ j), WL x⟫ ≠ 0 :=
            hdiff_ne.resolve_left (not_not.mpr h0)
          filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t) _
          rw [heq t, h0, zero_add]; exact mul_ne_zero ht.ne' hB
        · filter_upwards [Minimality.eventually_pos_affine
            (A := ⟪x (cJ i) - x (cJ j), g s₀⟫)
            (B := ⟪x (cJ i) - x (cJ j), WR x⟫ - ⟪x (cJ i) - x (cJ j), WL x⟫)
            (Or.inl h0)] with t ht _
          rw [heq t]; linarith
    by_cases hmix : ∃ u ∈ A, (∃ p, f p u < 0) ∧ ∃ p, 0 < f p u
    · obtain ⟨_, ⟨s₀, hs00, hs01, rfl⟩, ⟨p, hpn⟩, ⟨q, hqp⟩⟩ := hmix
      have h_ne : (nhdsWithin (0 : ℝ) (Set.Ioi 0)).NeBot := nhdsWithin_Ioi_neBot (le_refl (0 : ℝ))
      have h_lt1 : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), s₀ + t < 1 := by
        have : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t < 1 - s₀ :=
          nhdsWithin_le_nhds (eventually_lt_nhds (by linarith))
        exact this.mono fun t ht => by linarith
      have hp_ev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          ⟪x (cJ p.1.1) - x (cJ p.1.2), g (s₀ + t)⟫ < 0 := by
        have heq : ∀ t : ℝ, ⟪x (cJ p.1.1) - x (cJ p.1.2), g (s₀ + t)⟫ =
            f p (g s₀) + t * (⟪x (cJ p.1.1) - x (cJ p.1.2), WR x⟫ - ⟪x (cJ p.1.1) - x (cJ p.1.2), WL x⟫) := by
          intro t; dsimp [f, g]; simp only [inner_add_right, real_inner_smul_right]; ring
        filter_upwards [Minimality.eventually_pos_affine
          (A := -f p (g s₀))
          (B := -(⟪x (cJ p.1.1) - x (cJ p.1.2), WR x⟫ - ⟪x (cJ p.1.1) - x (cJ p.1.2), WL x⟫))
          (Or.inl (by linarith))] with t ht
        rw [heq t]; linarith
      have hq_ev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          0 < ⟪x (cJ q.1.1) - x (cJ q.1.2), g (s₀ + t)⟫ := by
        have heq : ∀ t : ℝ, ⟪x (cJ q.1.1) - x (cJ q.1.2), g (s₀ + t)⟫ =
            f q (g s₀) + t * (⟪x (cJ q.1.1) - x (cJ q.1.2), WR x⟫ - ⟪x (cJ q.1.1) - x (cJ q.1.2), WL x⟫) := by
          intro t; dsimp [f, g]; simp only [inner_add_right, real_inner_smul_right]; ring
        filter_upwards [Minimality.eventually_pos_affine
          (A := f q (g s₀))
          (B := ⟪x (cJ q.1.1) - x (cJ q.1.2), WR x⟫ - ⟪x (cJ q.1.1) - x (cJ q.1.2), WL x⟫)
          (Or.inl hqp)] with t ht
        rw [heq t]; linarith
      obtain ⟨t, ht0, ht1, hinj_t, hp_t, hq_t⟩ :=
        @Filter.Eventually.exists _ _ _ h_ne (Filter.Eventually.and self_mem_nhdsWithin (h_lt1.and ((h_inj_near s₀).and (hp_ev.and hq_ev))))
      refine ⟨s₀ + t, by linarith, ht1, hinj_t, robUni_four_of_mixed ⟨p.1, p.2, ?_⟩ ⟨q.1, q.2, ?_⟩⟩
      · rw [← inner_sub_left]; exact hp_t
      · rw [← inner_sub_left]; exact hq_t
    · have hz_u0 : ∃ u₀ ∈ A, ∀ p, f p u₀ = 0 := by
        by_contra hnz; push Not at hnz
        rcases hn with ⟨pn, hpnm, hpnv⟩ | ⟨pn, hpnm, hpnv⟩ <;>
        rcases hp with ⟨pp, hppm, hppv⟩ | ⟨pp, hppm, hppv⟩
        · exact hmix (exists_mixed_sign_of_closure f hfc hAc hnz hWL_cl hWL_cl ⟨⟨pn, hpnm⟩, hpnv⟩ ⟨⟨pp, hppm⟩, hppv⟩)
        · exact hmix (exists_mixed_sign_of_closure f hfc hAc hnz hWL_cl hWR_cl ⟨⟨pn, hpnm⟩, hpnv⟩ ⟨⟨pp, hppm⟩, hppv⟩)
        · exact hmix (exists_mixed_sign_of_closure f hfc hAc hnz hWR_cl hWL_cl ⟨⟨pn, hpnm⟩, hpnv⟩ ⟨⟨pp, hppm⟩, hppv⟩)
        · exact hmix (exists_mixed_sign_of_closure f hfc hAc hnz hWR_cl hWR_cl ⟨⟨pn, hpnm⟩, hpnv⟩ ⟨⟨pp, hppm⟩, hppv⟩)
      obtain ⟨_, ⟨s₀, hs00, hs01, rfl⟩, hall0⟩ := hz_u0
      set u₀ := g s₀
      have h25 : ⟪x 2 - x 5, u₀⟫ = 0 := hall0 ⟨(0, 1), by decide⟩
      have h45 : ⟪x 4 - x 5, u₀⟫ = 0 := hall0 ⟨(2, 1), by decide⟩
      have h65 : ⟪x 6 - x 5, u₀⟫ = 0 := by
        have e1 := hall0 ⟨(0, 1), by decide⟩
        have e2 := hall0 ⟨(0, 3), by decide⟩
        dsimp [f, cJ] at e1 e2
        rw [show x 6 - x 5 = (x 2 - x 5) - (x 2 - x 6) by abel, inner_sub_left, e1, e2, sub_self]
      obtain ⟨h3u0, hUu0, hDu0⟩ := u_seg_strict F hne hs00 hs01
      obtain ⟨hρ0, hcyc0, _⟩ := cJ_hcyc_hin F h3u0 hUu0 hDu0
      have hrob_WL : RobUni (fun i => ⟪x (cJ i), WL x⟫) := by
        have h45_ne : x 4 - x 5 ≠ 0 := sub_ne_zero.mpr (fun h => absurd ((Minimality.H24.SAT.inj_of_fac F) h) (by decide))
        have hu0_ne : u₀ ≠ 0 := fun h0 => by
          have := hUu0 6 (by decide); change 0 < ⟪F.N 6, u₀⟫ at this; rw [h0, inner_zero_right] at this; exact lt_irrefl 0 this
        have hN3_ne : F.N 3 ≠ 0 := fun h0 => by
          have hf := F.inner_sub 3 2 4
          rw [h0, inner_zero_left, F.zero 3 4 (by decide), sub_zero] at hf
          have := F.neg 3 2 (by decide); linarith
        set w : ℝ³ := WL x - (⟪WL x, u₀⟫ / ⟪u₀, u₀⟫) • u₀
        have hwu0 : ⟪w, u₀⟫ = 0 := by
          dsimp [w]; rw [inner_sub_left, real_inner_smul_left, div_mul_cancel₀ _ (real_inner_self_pos.mpr hu0_ne).ne', sub_self]
        have hwN3 : ⟪w, F.N 3⟫ = 0 := by
          dsimp [w]; change ⟪F.N 3, u₀⟫ = 0 at h3u0
          rw [inner_sub_left, real_inner_smul_left, real_inner_comm (F.N 3) (WL x),
            (regionJ_left F hne).1, real_inner_comm (F.N 3) u₀, h3u0, mul_zero, sub_zero]
        have hw_ne : w ≠ 0 := by
          intro h0
          have hWL_par : WL x = (⟪WL x, u₀⟫ / ⟪u₀, u₀⟫) • u₀ := sub_eq_zero.mp h0
          have hv2 : ⟪x 4 - x 5, WL x⟫ = 0 := by rw [hWL_par, real_inner_smul_right, h45, mul_zero]
          have hWR_eq : ∀ y : ℝ³, ⟪y, u₀⟫ = 0 → ⟪y, WL x⟫ = 0 → ⟪y, WR x⟫ = 0 := by
            intro y hy0 hyL
            dsimp [u₀, g] at hy0
            rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, hyL, mul_zero, zero_add] at hy0
            exact (mul_eq_zero.mp hy0).resolve_left hs00.ne'
          exact (hinj_J 2 1 (by decide)).elim (fun h => h hv2) (fun h => h (hWR_eq _ h45 hv2))
        have hw_eq : ∀ y : ℝ³, ⟪y, u₀⟫ = 0 → ⟪y, w⟫ = ⟪y, WL x⟫ := by
          intro y hy; dsimp [w]; rw [inner_sub_right, real_inner_smul_right, hy, mul_zero, sub_zero]
        have hdet_u0 : ∀ a b : ℝ³, ⟪a, u₀⟫ = 0 → ⟪b, u₀⟫ = 0 →
            ⟪w, w⟫ * ⟪F.N 3, F.N 3⟫ * det3 a b u₀ =
              (⟪a, w⟫ * ⟪b, F.N 3⟫ - ⟪b, w⟫ * ⟪a, F.N 3⟫) * det3 w (F.N 3) u₀ :=
          fun a b hau hbu => det3_ortho_frame hu0_ne hau hbu hwu0 hwN3 h3u0
        have hK_ne : det3 w (F.N 3) u₀ ≠ 0 := by
          intro h0
          have hsq := det3_ortho_sq hwu0 hwN3 h3u0
          rw [h0, zero_pow (by decide)] at hsq
          have hpos : 0 < ⟪w, w⟫ * ⟪F.N 3, F.N 3⟫ * ⟪u₀, u₀⟫ :=
            mul_pos (mul_pos (real_inner_self_pos.mpr hw_ne) (real_inner_self_pos.mpr hN3_ne))
              (real_inner_self_pos.mpr hu0_ne)
          linarith
        set v0 := ⟪x 2 - x 5, WL x⟫
        set v2 := ⟪x 4 - x 5, WL x⟫
        set v3 := ⟪x 6 - x 5, WL x⟫
        have hv2_ne : v2 ≠ 0 := by
          intro h0
          have := hdet_u0 (x 4 - x 5) (x 2 - x 5) h45 h25
          dsimp only [v2] at h0
          rw [hw_eq _ h45, h0, zero_mul, zero_sub, real_inner_comm (F.N 3) (x 4 - x 5),
            F.inner_sub, F.zero 3 4 (by decide), F.zero 3 5 (by decide), sub_self, mul_zero, neg_zero, zero_mul] at this
          have hc12 := hcyc0 1 0 (by decide) (by decide)
          have hid : det3 (x (cJ (1 + 1)) - x (cJ 1)) (x (cJ 0) - x (cJ 1)) u₀ =
              det3 (x 4 - x 5) (x 2 - x 5) u₀ := rfl
          rw [hid] at hc12
          have hdet0 : det3 (x 4 - x 5) (x 2 - x 5) u₀ = 0 := by
            have hp : ⟪w, w⟫ * ⟪F.N 3, F.N 3⟫ ≠ 0 :=
              mul_ne_zero (real_inner_self_pos.mpr hw_ne).ne' (real_inner_self_pos.mpr hN3_ne).ne'
            exact (mul_eq_zero.mp this).resolve_left hp
          rw [hdet0, mul_zero] at hc12; exact lt_irrefl 0 hc12
        set z2 := F.f 3 (x 2)
        set z6 := F.f 3 (x 6)
        have hz2 : z2 < 0 := F.neg 3 2 (by decide)
        have hz6 : z6 < 0 := F.neg 3 6 (by decide)
        have hd10 := hcyc0 1 0 (by decide) (by decide)
        have hd20 := hcyc0 2 0 (by decide) (by decide)
        have hd31 := hcyc0 3 1 (by decide) (by decide)
        have he10 : det3 (x (cJ (1 + 1)) - x (cJ 1)) (x (cJ 0) - x (cJ 1)) u₀ =
            det3 (x 4 - x 5) (x 2 - x 5) u₀ := rfl
        have he20 : det3 (x (cJ (2 + 1)) - x (cJ 2)) (x (cJ 0) - x (cJ 2)) u₀ =
            det3 (x 6 - x 4) (x 2 - x 4) u₀ := rfl
        have he31 : det3 (x (cJ (3 + 1)) - x (cJ 3)) (x (cJ 1) - x (cJ 3)) u₀ =
            det3 (x 2 - x 6) (x 5 - x 6) u₀ := rfl
        rw [he10] at hd10; rw [he20] at hd20; rw [he31] at hd31
        have hp12 : 0 < det3 (x 4 - x 5) (x 2 - x 5) u₀ * det3 (x 6 - x 4) (x 2 - x 4) u₀ :=
          pos_of_mul_pos_right (by have := mul_pos hd10 hd20; linarith [sq_nonneg (det3 (x 5 - x 2) (x 4 - x 2) u₀)])
            (sq_nonneg (det3 (x 5 - x 2) (x 4 - x 2) u₀))
        have hp13 : 0 < det3 (x 4 - x 5) (x 2 - x 5) u₀ * det3 (x 2 - x 6) (x 5 - x 6) u₀ :=
          pos_of_mul_pos_right (by have := mul_pos hd10 hd31; linarith [sq_nonneg (det3 (x 5 - x 2) (x 4 - x 2) u₀)])
            (sq_nonneg (det3 (x 5 - x 2) (x 4 - x 2) u₀))
        have h64_u0 : ⟪x 6 - x 4, u₀⟫ = 0 := by rw [show x 6 - x 4 = (x 6 - x 5) - (x 4 - x 5) by abel, inner_sub_left, h65, h45, sub_self]
        have h24_u0 : ⟪x 2 - x 4, u₀⟫ = 0 := by rw [show x 2 - x 4 = (x 2 - x 5) - (x 4 - x 5) by abel, inner_sub_left, h25, h45, sub_self]
        have h26_u0 : ⟪x 2 - x 6, u₀⟫ = 0 := by rw [show x 2 - x 6 = (x 2 - x 5) - (x 6 - x 5) by abel, inner_sub_left, h25, h65, sub_self]
        have h56_u0 : ⟪x 5 - x 6, u₀⟫ = 0 := by rw [← neg_sub, inner_neg_left, h65, neg_zero]
        have e_10 := hdet_u0 (x 4 - x 5) (x 2 - x 5) h45 h25
        have e_20 := hdet_u0 (x 6 - x 4) (x 2 - x 4) h64_u0 h24_u0
        have e_31 := hdet_u0 (x 2 - x 6) (x 5 - x 6) h26_u0 h56_u0
        rw [hw_eq _ h45, hw_eq _ h25,
          real_inner_comm (F.N 3) (x 4 - x 5), real_inner_comm (F.N 3) (x 2 - x 5),
          F.inner_sub, F.inner_sub, F.zero 3 4 (by decide), F.zero 3 5 (by decide), sub_self,
          mul_zero, sub_zero, sub_zero] at e_10
        rw [hw_eq _ h64_u0, hw_eq _ h24_u0,
          show ⟪x 6 - x 4, WL x⟫ = v3 - v2 by rw [show x 6 - x 4 = (x 6 - x 5) - (x 4 - x 5) by abel, inner_sub_left],
          show ⟪x 2 - x 4, WL x⟫ = v0 - v2 by rw [show x 2 - x 4 = (x 2 - x 5) - (x 4 - x 5) by abel, inner_sub_left],
          real_inner_comm (F.N 3) (x 2 - x 4), real_inner_comm (F.N 3) (x 6 - x 4),
          F.inner_sub, F.inner_sub, F.zero 3 4 (by decide), sub_zero, sub_zero] at e_20
        rw [hw_eq _ h26_u0, hw_eq _ h56_u0,
          show ⟪x 2 - x 6, WL x⟫ = v0 - v3 by rw [show x 2 - x 6 = (x 2 - x 5) - (x 6 - x 5) by abel, inner_sub_left],
          show ⟪x 5 - x 6, WL x⟫ = -v3 by rw [← neg_sub, inner_neg_left],
          real_inner_comm (F.N 3) (x 5 - x 6), real_inner_comm (F.N 3) (x 2 - x 6),
          F.inner_sub, F.inner_sub, F.zero 3 5 (by decide), zero_sub] at e_31
        have hC_pos : 0 < ⟪w, w⟫ * ⟪F.N 3, F.N 3⟫ :=
          mul_pos (real_inner_self_pos.mpr hw_ne) (real_inner_self_pos.mpr hN3_ne)
        have hK2 : 0 < (det3 w (F.N 3) u₀) ^ 2 := sq_pos_of_ne_zero hK_ne
        have hq12 : 0 < (v2 * z2) * ((v3 - v2) * z2 - (v0 - v2) * z6) := by
          have hp12' := mul_pos (sq_pos_of_ne_zero hC_pos.ne') hp12
          have hid : (⟪w, w⟫ * ⟪F.N 3, F.N 3⟫) ^ 2 * (det3 (x 4 - x 5) (x 2 - x 5) u₀ * det3 (x 6 - x 4) (x 2 - x 4) u₀) =
              (det3 w (F.N 3) u₀) ^ 2 * ((v2 * z2) * ((v3 - v2) * z2 - (v0 - v2) * z6)) := by
            calc _ = (⟪w, w⟫ * ⟪F.N 3, F.N 3⟫ * det3 (x 4 - x 5) (x 2 - x 5) u₀) *
                    (⟪w, w⟫ * ⟪F.N 3, F.N 3⟫ * det3 (x 6 - x 4) (x 2 - x 4) u₀) := by ring
              _ = (v2 * z2 * det3 w (F.N 3) u₀) * (((v3 - v2) * z2 - (v0 - v2) * z6) * det3 w (F.N 3) u₀) := by
                    rw [e_10, e_20]
              _ = _ := by ring
          rw [hid] at hp12'
          exact pos_of_mul_pos_right hp12' hK2.le
        have hq13 : 0 < (v2 * z2) * ((v0 - v3) * (-z6) - (-v3) * (z2 - z6)) := by
          have hp13' := mul_pos (sq_pos_of_ne_zero hC_pos.ne') hp13
          have hid : (⟪w, w⟫ * ⟪F.N 3, F.N 3⟫) ^ 2 * (det3 (x 4 - x 5) (x 2 - x 5) u₀ * det3 (x 2 - x 6) (x 5 - x 6) u₀) =
              (det3 w (F.N 3) u₀) ^ 2 * ((v2 * z2) * ((v0 - v3) * (-z6) - (-v3) * (z2 - z6))) := by
            calc _ = (⟪w, w⟫ * ⟪F.N 3, F.N 3⟫ * det3 (x 4 - x 5) (x 2 - x 5) u₀) *
                    (⟪w, w⟫ * ⟪F.N 3, F.N 3⟫ * det3 (x 2 - x 6) (x 5 - x 6) u₀) := by ring
              _ = (v2 * z2 * det3 w (F.N 3) u₀) * (((v0 - v3) * (-z6) - (-v3) * (z2 - z6)) * det3 w (F.N 3) u₀) := by
                    rw [e_10, e_31]
              _ = _ := by ring
          rw [hid] at hp13'
          exact pos_of_mul_pos_right hp13' hK2.le
        intro B b c d hb hbc hcd hd ⟨h1, h2, h3, h4⟩
        have hb1 : b = 1 := by omega
        have hc2 : c = 2 := by omega
        have hd3 : d = 3 := by omega
        subst hb1 hc2 hd3
        have zmod4_cases : ∀ k : ZMod 4, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := fun k => by
          fin_cases k
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr rfl))
        have hB : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 := zmod4_cases B
        have hval : ∀ i : ZMod 4, ⟪x (cJ i), WL x⟫ - ⟪x 5, WL x⟫ =
            if i = 0 then v0 else if i = 1 then 0 else if i = 2 then v2 else v3 := by
          intro i
          rcases zmod4_cases i with rfl | rfl | rfl | rfl
          · simp [cJ, inner_sub_left, v0]
          · simp [cJ, show (1 : ZMod 4) ≠ 0 by decide]
          · simp [cJ, inner_sub_left, v2, show (2 : ZMod 4) ≠ 0 by decide, show (2 : ZMod 4) ≠ 1 by decide]
          · simp [cJ, inner_sub_left, v3, show (3 : ZMod 4) ≠ 0 by decide, show (3 : ZMod 4) ≠ 1 by decide, show (3 : ZMod 4) ≠ 2 by decide]
        have h1' : (if B = 0 then v0 else if B = 1 then 0 else if B = 2 then v2 else v3) ≥
            (if B + 1 = 0 then v0 else if B + 1 = 1 then 0 else if B + 1 = 2 then v2 else v3) := by
          rw [← hval B, ← hval (B + 1)]; simpa using h1
        have h2' : (if B + 2 = 0 then v0 else if B + 2 = 1 then 0 else if B + 2 = 2 then v2 else v3) ≥
            (if B + 1 = 0 then v0 else if B + 1 = 1 then 0 else if B + 1 = 2 then v2 else v3) := by
          rw [← hval (B + 2), ← hval (B + 1)]; simpa using h2
        have h03' : (if B = 0 then v0 else if B = 1 then 0 else if B = 2 then v2 else v3) ≥
            (if B + 3 = 0 then v0 else if B + 3 = 1 then 0 else if B + 3 = 2 then v2 else v3) := by
          rw [← hval B, ← hval (B + 3)]; simpa using h3
        have h23' : (if B + 2 = 0 then v0 else if B + 2 = 1 then 0 else if B + 2 = 2 then v2 else v3) ≥
            (if B + 3 = 0 then v0 else if B + 3 = 1 then 0 else if B + 3 = 2 then v2 else v3) := by
          rw [← hval (B + 2), ← hval (B + 3)]; simpa using h4
        exact quad_robUni_of_signs hz2 hz6 hv2_ne hq12 hq13 hB h1' h2' h03' h23'
      have h_ne : (nhdsWithin (0 : ℝ) (Set.Ioi 0)).NeBot := nhdsWithin_Ioi_neBot (le_refl (0 : ℝ))
      have h_lt_s0 : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t < s₀ :=
        nhdsWithin_le_nhds (eventually_lt_nhds hs00)
      obtain ⟨t, ht0, ht_s0, hinj_t⟩ :=
        @Filter.Eventually.exists _ _ _ h_ne (Filter.Eventually.and self_mem_nhdsWithin (h_lt_s0.and (h_inj_near 0)))
      have ht_pos : 0 < 1 - t / s₀ := by
        rw [sub_pos, div_lt_one hs00]; exact ht_s0
      have hscale : ∀ i : ZMod 4, ⟪x (cJ i), g (0 + t)⟫ - ⟪x 5, g (0 + t)⟫ =
          (1 - t / s₀) * (⟪x (cJ i), WL x⟫ - ⟪x 5, WL x⟫) := by
        intro i
        have hi0 : ⟪x (cJ i) - x 5, u₀⟫ = 0 := by
          fin_cases i
          · exact h25
          · simp [cJ]
          · exact h45
          · exact h65
        have hWR : ⟪x (cJ i) - x 5, WR x⟫ = -((1 - s₀) / s₀) * ⟪x (cJ i) - x 5, WL x⟫ := by
          dsimp [u₀, g] at hi0
          rw [inner_add_right, real_inner_smul_right, real_inner_smul_right] at hi0
          field_simp [hs00.ne']; linarith
        rw [← inner_sub_left, ← inner_sub_left]
        dsimp [g]; rw [zero_add, inner_add_right, real_inner_smul_right, real_inner_smul_right, hWR]
        field_simp [hs00.ne']; ring
      refine ⟨0 + t, by linarith, by linarith, hinj_t, ?_⟩
      intro B b c d hb hbc hcd hd ⟨h1, h2, h3, h4⟩
      have hle : ∀ i j : ZMod 4, ⟪x (cJ i), g (0 + t)⟫ ≤ ⟪x (cJ j), g (0 + t)⟫ →
          ⟪x (cJ i), WL x⟫ ≤ ⟪x (cJ j), WL x⟫ := fun i j h => by
        have h1 := hscale i; have h2 := hscale j
        nlinarith only [h, h1, h2, ht_pos]
      exact hrob_WL B b c d hb hbc hcd hd
        ⟨hle (B + b) B h1, hle (B + b) (B + c) h2, hle (B + d) B h3, hle (B + d) (B + c) h4⟩
  obtain ⟨s, hs0, hs1, hinj_s, hrob⟩ := exists_s
  set u := (1 - s) • WL x + s • WR x
  obtain ⟨h3u, hUu, hDu⟩ := u_seg_strict F hne hs0 hs1
  obtain ⟨hρ_ne, hcyc, hin⟩ := cJ_hcyc_hin F h3u hUu hDu
  have hdu : det3 (x 4 - x 5) (F.N 3) u ≠ 0 := by
    intro h0
    have e2 := edge_54_det3 F h3u 2
    rw [h0, mul_zero] at e2
    have hc := hcyc 1 0 (by decide) (by decide)
    have hc1 : cJ (1 + 1) = 4 := by decide
    have hc1' : cJ 1 = 5 := by decide
    have hc0 : cJ 0 = 2 := by decide
    rw [hc1, hc1', hc0] at hc
    have hN3_2 : ⟪F.N 3, F.N 3⟫ ≠ 0 := by
      have hN3 : F.N 3 ≠ 0 := fun h0 => by
        have hlt := F.neg 3 2 (by decide)
        have hsub : ⟪F.N 3, x 2 - x 5⟫ = F.f 3 (x 2) := by
          rw [F.inner_sub, F.zero 3 5 (by decide), sub_zero]
        rw [h0, inner_zero_left] at hsub; linarith
      exact (real_inner_self_pos.mpr hN3).ne'
    have hdet0 : det3 (x 4 - x 5) (x 2 - x 5) u = 0 := (mul_eq_zero.mp e2).resolve_left hN3_2
    rw [hdet0, mul_zero] at hc
    exact lt_irrefl 0 hc
  have hmid := cJ_hmid F h3u hUu hDu hdu
  have hinj_u : Function.Injective (fun i => ⟪x (cJ i), u⟫) := by
    intro i j hij
    by_contra hne_ij
    exact hinj_s i j hne_ij (by rw [inner_sub_left]; exact sub_eq_zero.mpr hij)
  have hz : UniOrSep (fun i => x (cJ i)) u := Or.inl (strictUnimodal_four_of_robUni hinj_u hrob)
  let w : ZMod 4 := if F.f 3 (x 2) < F.f 3 (x 6) then 0 else 3
  have hw_eq : cJ w = if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6 := by
    dsimp [w]; split_ifs <;> decide
  have hwS : cJ w ∉ s0x_S24 3 := by rw [hw_eq]; split_ifs <;> decide
  have hfar : ∀ m : ZMod 4, m ≠ w → cJ m ∉ s0x_S24 3 → F.f 3 (x (cJ w)) < F.f 3 (x (cJ m)) := by
    intro m hmw hmS
    have hm03 : m = 0 ∨ m = 3 := by
      fin_cases m
      · exact Or.inl rfl
      · exact absurd (by decide : cJ 1 ∈ s0x_S24 3) hmS
      · exact absurd (by decide : cJ 2 ∈ s0x_S24 3) hmS
      · exact Or.inr rfl
    dsimp [w] at hmw ⊢
    split_ifs at hmw ⊢ with hlt
    · rcases hm03 with rfl | rfl
      · exact absurd rfl hmw
      · simpa [cJ] using hlt
    · rcases hm03 with rfl | rfl
      · have hgt : F.f 3 (x 6) < F.f 3 (x 2) := lt_of_le_of_ne (not_lt.mp hlt) hf3.symm
        simpa [cJ] using hgt
      · exact absurd rfl hmw
  have hin_all : ∀ q, q ∉ s0x_S24 3 → (∀ j : ZMod 4, q ≠ cJ j) → ∀ i : ZMod 4,
      0 < det3 (x 5 - x 2) (x 4 - x 2) u * det3 (x (cJ (i + 1)) - x (cJ i)) (x q - x (cJ i)) u := by
    intro q hqS hqj i
    have hq1 : q = 1 := by
      fin_cases q
      · exact absurd (by decide : (0 : Fin 7) ∈ s0x_S24 3) hqS
      · rfl
      · exact absurd (by decide : (2 : Fin 7) = cJ 0) (hqj 0)
      · exact absurd (by decide : (3 : Fin 7) ∈ s0x_S24 3) hqS
      · exact absurd (by decide : (4 : Fin 7) = cJ 2) (hqj 2)
      · exact absurd (by decide : (5 : Fin 7) = cJ 1) (hqj 1)
      · exact absurd (by decide : (6 : Fin 7) = cJ 3) (hqj 3)
    subst hq1; exact hin i
  have hoff' : ⟪F.N 3, cross (x (cJ (1 + 1)) - x (cJ 1)) (x (cJ w) - x (cJ 1))⟫ ≠ 0 ∨
      ⟪x (cJ w) - x (cJ 1), x (cJ (1 + 1)) - x (cJ 1)⟫ < 0 ∨
      ⟪x (cJ w) - x (cJ (1 + 1)), x (cJ 1) - x (cJ (1 + 1))⟫ < 0 := by
    have hc1 : cJ 1 = 5 := by decide
    have hc2 : cJ (1 + 1) = 4 := by decide
    rw [hc1, hc2, hw_eq]
    exact hoff
  exact ⟨u, 4, ⟨by decide⟩, cJ, 1, w, det3 (x 5 - x 2) (x 4 - x 2) u, h3u, by decide,
    by decide, by decide, hρ_ne, hcyc, hin_all, hmid, hinj_u, hz, hwS, hfar, hoff'⟩

/-- **EJ(ii-b), the Carbon criterion (Q64.1(1)).**  Proved from `faceChordView_J54` and `isRupert_of_faceChordView`. -/
theorem isRupert_J54 (F : S0xFac 9 s0x_S24 x) (hne : 0 < caL x ∨ 0 < caR x)
    (hn : (∃ p ∈ diagPairs, ⟪x (cJ p.1) - x (cJ p.2), WL x⟫ < 0) ∨
      ∃ p ∈ diagPairs, ⟪x (cJ p.1) - x (cJ p.2), WR x⟫ < 0)
    (hp : (∃ p ∈ diagPairs, 0 < ⟪x (cJ p.1) - x (cJ p.2), WL x⟫) ∨
      ∃ p ∈ diagPairs, 0 < ⟪x (cJ p.1) - x (cJ p.2), WR x⟫)
    (hf3 : F.f 3 (x 2) ≠ F.f 3 (x 6))
    (hoff : ⟪F.N 3, cross (x 4 - x 5) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 5)⟫ ≠ 0 ∨
      ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 5, x 4 - x 5⟫ < 0 ∨
      ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4, x 5 - x 4⟫ < 0)
    (hinj_J : ∀ i j : ZMod 4, i ≠ j →
      ⟪x (cJ i) - x (cJ j), WL x⟫ ≠ 0 ∨ ⟪x (cJ i) - x (cJ j), WR x⟫ ≠ 0) :
    IsRupert (univ.image x) :=
  isRupert_of_faceChordView F (faceChordView_J54 F hne hn hp hf3 hoff hinj_J)

end Minimality.T24.EJ
