module

public import Minimality.Type24HiddenCone
public import Minimality.RimCellClosed
public import Minimality.RDispatch24
public import Minimality.Type24SAT.Geo.Top

/-!
# EL: the ray `c0125 = (1, 1, -M)` in the cone `N_c` of the type-24 hidden-cap analysis (4-rim `0.1.2.5`)

Proves `regionC_gen` (`EL(i)`) and wires `regionC`, `isRupert_c0125_robUni`, `isRupert_c0125`.
-/

@[expose] public section

set_option autoImplicit false
open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.EL

open Minimality Minimality.H21 Minimality.T24.SAT Minimality.RimCell Minimality.T24.HC

variable {x : Fin 7 → ℝ³}

/-! ## The cell and the rim -/

/-- Up facets of the cell: `012, 025`. -/
def UC : Finset (Fin 9) := {0, 2}
/-- Down facets of the cell: all others. -/
def DnC : Finset (Fin 9) := {1, 3, 4, 5, 6, 7, 8}
/-- Rim cycle `0 1 2 5`. -/
def cC : ZMod 4 → Fin 7 := ![0, 1, 2, 5]

theorem cycC : S0xCycUD s0x_S24 cC UC DnC := by decide

theorem injC : Function.Injective cC := by
  intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)

/-! ## The view -/

/-- `r_t = (N_{t,a} + N_{t,b}) / N_{t,c}`, a scale-free ratio of the corner coordinates of the facet covector. -/
noncomputable def rEL (F : S0xFac 9 s0x_S24 x) (t : Fin 9) : ℝ :=
  (⟪F.N t, x 0 - x 1⟫ + ⟪F.N t, x 2 - x 1⟫) / ⟪F.N t, x 6 - x 1⟫

/-- `M_0 = max(0, 1 - ω4, 1 - ω3, r_3, r_6, r_8)`. -/
noncomputable def M0EL (F : S0xFac 9 s0x_S24 x) : ℝ :=
  max 0 (max (1 - omega4 x) (max (1 - omega3 x) (max (rEL F 3) (max (rEL F 6) (rEL F 8)))))

/-- Carbon's ray `c_* = (1, 1, -(M_0 + 1))`. -/
noncomputable def viewC (F : S0xFac 9 s0x_S24 x) : ℝ³ := capView x 1 1 (-(M0EL F + 1))

/-! ## (i) The region lemma -/

private theorem fac_edge1 (F : S0xFac 9 s0x_S24 x) {t : Fin 9} {v : Fin 7}
    (hv : v ∈ s0x_S24 t) :
    ⟪F.N t, x v - x 1⟫ = -F.f t (x 1) := by
  rw [F.inner_sub, F.zero t v hv, zero_sub]

/-- **EL(i).**  For every `M > M_0`, the view `(1, 1, -M)` is a point of the open cell `+ - + - - - - - -`
(facets `0, 2` strictly up, the other seven strictly down), under `n_C > 0`, `N_{6,c} > 0`, `N_{8,c} > 0`
and `0 ≤ ω5` (implied by `CbarIn`; `CbarIn` itself and OB1 are not needed, see GATE.md). -/
theorem regionC_gen (F : S0xFac 9 s0x_S24 x) (h5 : 0 ≤ omega5 x)
    (h3 : 0 < ⟪F.N 3, x 6 - x 1⟫) (h6 : 0 < ⟪F.N 6, x 6 - x 1⟫) (h8 : 0 < ⟪F.N 8, x 6 - x 1⟫)
    {M : ℝ} (hM : M0EL F < M) : CellAt F UC DnC (capView x 1 1 (-M)) := by
  have hm0 : 0 < M := lt_of_le_of_lt (le_max_left _ _) hM
  have hM' : max (1 - omega4 x) (max (1 - omega3 x) (max (rEL F 3) (max (rEL F 6) (rEL F 8)))) < M :=
    lt_of_le_of_lt (le_max_right _ _) hM
  have hm4 : 1 - omega4 x < M := lt_of_le_of_lt (le_max_left _ _) hM'
  have hM'' : max (1 - omega3 x) (max (rEL F 3) (max (rEL F 6) (rEL F 8))) < M :=
    lt_of_le_of_lt (le_max_right _ _) hM'
  have hm3 : 1 - omega3 x < M := lt_of_le_of_lt (le_max_left _ _) hM''
  have hMr : max (rEL F 3) (max (rEL F 6) (rEL F 8)) < M :=
    lt_of_le_of_lt (le_max_right _ _) hM''
  have hmr3 : rEL F 3 < M := lt_of_le_of_lt (le_max_left _ _) hMr
  have hMr' : max (rEL F 6) (rEL F 8) < M := lt_of_le_of_lt (le_max_right _ _) hMr
  have hmr6 : rEL F 6 < M := lt_of_le_of_lt (le_max_left _ _) hMr'
  have hmr8 : rEL F 8 < M := lt_of_le_of_lt (le_max_right _ _) hMr'
  obtain ⟨⟨a0, b0, c0⟩, ⟨a1, c1, b1⟩, ⟨b5, c5, a5⟩⟩ := facet_back_vals F
  have T := M4.type24OfFac F
  have hlin : ∀ t : Fin 9, ⟪F.N t, capView x 1 1 (-M)⟫ =
      ⟪F.N t, x 0 - x 1⟫ + ⟪F.N t, x 2 - x 1⟫ - M * ⟪F.N t, x 6 - x 1⟫ := by
    intro t
    simp only [capView, inner_add_right, real_inner_smul_right, one_smul]
    ring
  have hrep : ∀ t : Fin 9, ∀ v : Fin 7, ⟪F.N t, x v - x 1⟫ =
      oblX0 x v * ⟪F.N t, x 0 - x 1⟫ + oblX2 x v * ⟪F.N t, x 2 - x 1⟫ +
        oblX6 x v * ⟪F.N t, x 6 - x 1⟫ := by
    intro t v
    have hv := T.rep v
    rw [show x v - x 1 = oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) +
        oblX6 x v • (x 6 - x 1) from by rw [sub_eq_iff_eq_add, hv]; abel]
    simp only [inner_add_right, real_inner_smul_right]
  have hlt_r : ∀ t : Fin 9, 0 < ⟪F.N t, x 6 - x 1⟫ → rEL F t < M →
      ⟪F.N t, capView x 1 1 (-M)⟫ < 0 := by
    intro t ht hr
    rw [hlin]
    have hmul : ⟪F.N t, x 0 - x 1⟫ + ⟪F.N t, x 2 - x 1⟫ < M * ⟪F.N t, x 6 - x 1⟫ := by
      rwa [rEL, div_lt_iff₀ ht] at hr
    linarith
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · simp only [UC, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl
    · rw [hlin, a0, b0]; nlinarith
    · have hk : 0 < -F.f 2 (x 1) := by linarith [F.neg 2 1 (by decide)]
      have e0 : ⟪F.N 2, x 0 - x 1⟫ = -F.f 2 (x 1) := fac_edge1 F (by decide)
      have e2 : ⟪F.N 2, x 2 - x 1⟫ = -F.f 2 (x 1) := fac_edge1 F (by decide)
      have e5 : ⟪F.N 2, x 5 - x 1⟫ = -F.f 2 (x 1) := fac_edge1 F (by decide)
      have h5r := hrep 2 5
      rw [e0, e2, e5] at h5r
      have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
      have h6_val : ⟪F.N 2, x 6 - x 1⟫ = -(omega5 x) * (-F.f 2 (x 1)) := by
        have ho5 : oblX6 x 5 * omega5 x = oblX0 x 5 + oblX2 x 5 - 1 := by
          dsimp [omega5]; exact mul_div_cancel₀ _ hc5.ne'
        apply mul_left_cancel₀ hc5.ne'
        linarith only [h5r, show oblX6 x 5 * (-(omega5 x) * (-F.f 2 (x 1))) =
            -(oblX0 x 5 + oblX2 x 5 - 1) * (-F.f 2 (x 1)) by rw [← ho5]; ring]
      rw [hlin, e0, e2, h6_val]
      have hmul : 0 ≤ M * omega5 x := mul_nonneg hm0.le h5
      have hpos : 0 < (2 + M * omega5 x) * (-F.f 2 (x 1)) := mul_pos (by linarith) hk
      linarith only [hpos, show (2 + M * omega5 x) * (-F.f 2 (x 1)) =
          -F.f 2 (x 1) + -F.f 2 (x 1) - M * (-(omega5 x) * -F.f 2 (x 1)) by ring]
  · simp only [DnC, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hlin, a1, c1]; linarith
    · exact hlt_r 3 h3 hmr3
    · have hk : 0 < -F.f 4 (x 1) := by linarith [F.neg 4 1 (by decide)]
      have e0 : ⟪F.N 4, x 0 - x 1⟫ = -F.f 4 (x 1) := fac_edge1 F (by decide)
      have e6 : ⟪F.N 4, x 6 - x 1⟫ = -F.f 4 (x 1) := fac_edge1 F (by decide)
      have e4 : ⟪F.N 4, x 4 - x 1⟫ = -F.f 4 (x 1) := fac_edge1 F (by decide)
      have h4r := hrep 4 4
      rw [e0, e6, e4] at h4r
      have hb4 : 0 < oblX2 x 4 := T.X2_pos (v := 4) (by decide)
      have h2_val : ⟪F.N 4, x 2 - x 1⟫ = -(omega4 x) * (-F.f 4 (x 1)) := by
        have ho4 : oblX2 x 4 * omega4 x = oblX0 x 4 + oblX6 x 4 - 1 := by
          dsimp [omega4]; exact mul_div_cancel₀ _ hb4.ne'
        apply mul_left_cancel₀ hb4.ne'
        linarith only [h4r, show oblX2 x 4 * (-(omega4 x) * (-F.f 4 (x 1))) =
            -(oblX0 x 4 + oblX6 x 4 - 1) * (-F.f 4 (x 1)) by rw [← ho4]; ring]
      rw [hlin, e0, e6, h2_val]
      have hneg : (1 - omega4 x - M) * (-F.f 4 (x 1)) < 0 := mul_neg_of_neg_of_pos (by linarith [hm4]) hk
      linarith only [hneg, show (1 - omega4 x - M) * (-F.f 4 (x 1)) =
          -F.f 4 (x 1) + -(omega4 x) * -F.f 4 (x 1) - M * -F.f 4 (x 1) by ring]
    · rw [hlin, b5, c5]; linarith
    · exact hlt_r 6 h6 hmr6
    · have hk : 0 < -F.f 7 (x 1) := by linarith [F.neg 7 1 (by decide)]
      have e2 : ⟪F.N 7, x 2 - x 1⟫ = -F.f 7 (x 1) := fac_edge1 F (by decide)
      have e6 : ⟪F.N 7, x 6 - x 1⟫ = -F.f 7 (x 1) := fac_edge1 F (by decide)
      have e3 : ⟪F.N 7, x 3 - x 1⟫ = -F.f 7 (x 1) := fac_edge1 F (by decide)
      have h3r := hrep 7 3
      rw [e2, e6, e3] at h3r
      have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
      have h0_val : ⟪F.N 7, x 0 - x 1⟫ = -(omega3 x) * (-F.f 7 (x 1)) := by
        have ho3 : oblX0 x 3 * omega3 x = oblX2 x 3 + oblX6 x 3 - 1 := by
          dsimp [omega3]; exact mul_div_cancel₀ _ ha3.ne'
        apply mul_left_cancel₀ ha3.ne'
        linarith only [h3r, show oblX0 x 3 * (-(omega3 x) * (-F.f 7 (x 1))) =
            -(oblX2 x 3 + oblX6 x 3 - 1) * (-F.f 7 (x 1)) by rw [← ho3]; ring]
      rw [hlin, e2, e6, h0_val]
      have hneg : (-omega3 x + 1 - M) * (-F.f 7 (x 1)) < 0 := mul_neg_of_neg_of_pos (by linarith [hm3]) hk
      linarith only [hneg, show (-omega3 x + 1 - M) * (-F.f 7 (x 1)) =
          -(omega3 x) * -F.f 7 (x 1) + -F.f 7 (x 1) - M * -F.f 7 (x 1) by ring]
    · exact hlt_r 8 h8 hmr8

/-- **EL(i), Carbon's ray.** `c_* = (1, 1, -(M_0 + 1))` is a point of the open cell. -/
theorem regionC (F : S0xFac 9 s0x_S24 x) (h5 : 0 ≤ omega5 x)
    (h3 : 0 < ⟪F.N 3, x 6 - x 1⟫) (h6 : 0 < ⟪F.N 6, x 6 - x 1⟫) (h8 : 0 < ⟪F.N 8, x 6 - x 1⟫) :
    CellAt F UC DnC (viewC F) :=
  regionC_gen F h5 h3 h6 h8 (by linarith)

/-! ## (ii) The leaves (proved from (i) and `isRupert_of_closedCell`) -/

/-- **EL(ii), RobUni form.** At `c_*` the four rim depths are robustly unimodal: Rupert. -/
theorem isRupert_c0125_robUni (F : S0xFac 9 s0x_S24 x) (h5 : 0 ≤ omega5 x)
    (h3 : 0 < ⟪F.N 3, x 6 - x 1⟫) (h6 : 0 < ⟪F.N 6, x 6 - x 1⟫) (h8 : 0 < ⟪F.N 8, x 6 - x 1⟫)
    (hR : RobUni (fun i => ⟪x (cC i), viewC F⟫)) : IsRupert (univ.image x) := by
  have ha := regionC F h5 h3 h6 h8
  exact isRupert_of_closedCell le_rfl F (Minimality.H24.SAT.inj_of_fac F) injC cycC ha ha.cellLe hR

/-- **EL(ii), criterion form.**  `D_A(u) = ∀ p ∈ diagPairs, 0 ≤ ⟪x (cC p.1) - x (cC p.2), u⟫`
(`min(z_0, z_2) ≥ max(z_1, z_5)`), `D_B(u)` the same with `≤ 0`.  `NOT D_A` and `NOT D_B` at `c_*`: Rupert. -/
theorem isRupert_c0125 (F : S0xFac 9 s0x_S24 x) (h5 : 0 ≤ omega5 x)
    (h3 : 0 < ⟪F.N 3, x 6 - x 1⟫) (h6 : 0 < ⟪F.N 6, x 6 - x 1⟫) (h8 : 0 < ⟪F.N 8, x 6 - x 1⟫)
    (hnA : ¬ ∀ p ∈ diagPairs, 0 ≤ ⟪x (cC p.1) - x (cC p.2), viewC F⟫)
    (hnB : ¬ ∀ p ∈ diagPairs, ⟪x (cC p.1) - x (cC p.2), viewC F⟫ ≤ 0) : IsRupert (univ.image x) := by
  refine isRupert_c0125_robUni F h5 h3 h6 h8 (robUni_four_of_mixed ?_ ?_)
  · push Not at hnA
    obtain ⟨p, hp, h⟩ := hnA
    exact ⟨p, hp, by rw [← inner_sub_left]; exact h⟩
  · push Not at hnB
    obtain ⟨p, hp, h⟩ := hnB
    exact ⟨p, hp, by rw [← inner_sub_left]; exact h⟩

end Minimality.T24.EL
