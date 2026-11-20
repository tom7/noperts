module

public import Minimality.R012
public import Minimality.R012F
public import Minimality.R012M
public import Minimality.R012W
public import Minimality.Q45Tie

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true

open scoped RealInnerProductSpace Topology
open Filter Finset
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT Minimality.RimFromSigns
open Minimality.T24.Q45 Minimality.T24.R012

namespace Minimality.T24.R012

variable {x : Fin 7 → ℝ³}

/-- The root of facet 346 on the circle of 012: `t* = -(f8 x0 - f8 x1)/(f8 x2 - f8 x1)`,
`⟪N8, u0 x t*⟫ = 0`. -/
noncomputable def tstar (F : S0xFac 9 s0x_S24 x) : ℝ :=
  -(F.f 8 (x 0) - F.f 8 (x 1)) / (F.f 8 (x 2) - F.f 8 (x 1))

theorem inner_N8_tstar (F : S0xFac 9 s0x_S24 x) (hP : F.f 8 (x 2) - F.f 8 (x 1) ≠ 0) :
    ⟪F.N 8, u0 x (tstar F)⟫ = 0 := by
  rw [inner_N8_u0, tstar]
  field_simp
  ring

theorem inner_N8_d (F : S0xFac 9 s0x_S24 x) :
    ⟪F.N 8, x 2 - x 1⟫ = F.f 8 (x 2) - F.f 8 (x 1) := (F.hN 8 (x 2) (x 1)).symm

/-- **Leaf (b): the 4-rim `(0,4,6,2)` at the 346-root with `t* > 0`** (mirror of `s:f235+`; `t:f346+` on
the circle of 012). The root `t* > 0` of facet 346 (`f8 x0 < f8 x1 < f8 x2`), the view `u0 t* + ε (x2 - x1)`
(`N8 > 0`), rim `(0,4,6,2)` with chord `2 → 0`, middle `1`, interior `3, 5` (`N4 < 0 < N3`, `N4 < 0 < N8`,
`N5 < 0 < N7`). Case conditions: `N3 > 0`, `N4 < 0`, `N7 > 0` at the root (lexicographic ties),
the depth condition at the base view, genericity and the Lemma H data at the farther of `4`, `6`. -/
theorem q012_f346_pos_4w (F : S0xFac 9 s0x_S24 x)
    (hlo : F.f 8 (x 0) < F.f 8 (x 1)) (hhi : F.f 8 (x 1) < F.f 8 (x 2))
    (h3 : 0 < ⟪F.N 3, u0 x (tstar F)⟫ ∨ (⟪F.N 3, u0 x (tstar F)⟫ = 0 ∧ 0 < ⟪F.N 3, x 2 - x 1⟫))
    (h4 : ⟪F.N 4, u0 x (tstar F)⟫ < 0 ∨ (⟪F.N 4, u0 x (tstar F)⟫ = 0 ∧ ⟪F.N 4, x 2 - x 1⟫ < 0))
    (h7 : 0 < ⟪F.N 7, u0 x (tstar F)⟫ ∨ (⟪F.N 7, u0 x (tstar F)⟫ = 0 ∧ 0 < ⟪F.N 7, x 2 - x 1⟫))
    (hbase : min ⟪x 4, u0 x (tstar F)⟫ ⟪x 2, u0 x (tstar F)⟫ <
      max ⟪x 0, u0 x (tstar F)⟫ ⟪x 6, u0 x (tstar F)⟫)
    (hgen : Gen4 (quad (x 0) (x 4) (x 6) (x 2)) (u0 x (tstar F)) (x 2 - x 1))
    (hfar : F.f 0 (x 4) ≠ F.f 0 (x 6))
    (hoff4 : F.f 0 (x 4) < F.f 0 (x 6) → Off012 F 4)
    (hoff6 : F.f 0 (x 6) < F.f 0 (x 4) → Off012 F 6) :
    FaceChordView F 0 := by
  have hP : 0 < F.f 8 (x 2) - F.f 8 (x 1) := by linarith
  have ht0 : 0 < tstar F := div_pos (by linarith) hP
  have h8 := inner_N8_tstar F hP.ne'
  refine leaf_core012 F (tstar F) 1 (Or.inl rfl) ht0 4 6 3 5 4 3 4 8 5 7 (by decide)
    (Or.inr (Or.inl rfl)) ?_ (Or.inl ⟨kap1 F, hbase⟩) hgen (hw_of_ne F 4 6 hfar hoff4 hoff6)
  filter_upwards [ev_neg_u0 (F.N 4) _ 1 (by simpa using h4), ev_pos_u0 (F.N 3) _ 1 (by simpa using h3),
    ev_pos_u0 (F.N 8) _ 1 (Or.inr ⟨h8, by rw [one_mul, inner_N8_d]; exact hP⟩),
    ev_neg_u0 (F.N 5) _ 1 (Or.inl (inner_N5_u0_neg F _)), ev_pos_u0 (F.N 7) _ 1 (by simpa using h7)]
    with ε e4 e3 e8 e5 e7
  exact ⟨⟨e4, e3⟩, ⟨e4, e8⟩, ⟨e5, e7⟩⟩

/-- The 5-rim `(0, 5, 3, 6, 1)`; the chord `1 → 0` of facet 012 is the edge from index `4` to index `0`
(vertex `2` is the middle over it, vertex `4` is inside). -/
def rimC5 : ZMod 5 → Fin 7
  | 0 => 0
  | 1 => 5
  | 2 => 3
  | 3 => 6
  | 4 => 1

/-- Rim data for `(0,5,3,6,1)` from the facet signs `N1, N3, N8 > 0`, `N2, N5, N6, N7 < 0` at a view in
the plane of 012. -/
theorem rimC5_data (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hN0 : ⟪F.N 0, u⟫ = 0) (h1 : 0 < ⟪F.N 1, u⟫) (h2 : ⟪F.N 2, u⟫ < 0) (h3 : 0 < ⟪F.N 3, u⟫)
    (h5 : ⟪F.N 5, u⟫ < 0) (h6 : ⟪F.N 6, u⟫ < 0) (h7 : ⟪F.N 7, u⟫ < 0) (h8 : 0 < ⟪F.N 8, u⟫) :
    ∃ ρ : ℝ, ρ ≠ 0 ∧ StrictConvex5 (fun i => x (rimC5 i)) u ρ ∧
      (∀ i : ZMod 5, 0 < ρ * det3 (x (rimC5 (i + 1)) - x (rimC5 i)) (x 4 - x (rimC5 i)) u) := by
  have hne_01 : cross u (x 5 - x 0) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 2 0 5 (by decide) (by decide) h2.ne 4 (by decide) (by decide)
  have hne_12 : cross u (x 3 - x 5) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 3 5 3 (by decide) (by decide) h3.ne' 2 (by decide) (by decide)
  have hne_23 : cross u (x 6 - x 3) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 8 3 6 (by decide) (by decide) h8.ne' 3 (by decide) (by decide)
  have hne_34 : cross u (x 1 - x 6) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 1 6 1 (by decide) (by decide) h1.ne' 4 (by decide) (by decide)
  have hne_40 : cross u (x 0 - x 1) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 1 1 0 (by decide) (by decide) h1.ne' 5 (by decide) (by decide)
  exact fiveRim_of_signs F (u := u) rimC5 4 2 3 6 3 7 8 5 1 0
    (by decide) (by decide) hN0
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨h2, h3⟩
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨h6, h3⟩
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨h7, h8⟩
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ⟨h5, h1⟩
    hne_01 hne_12 hne_23 hne_34 hne_40
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

theorem view_neg (x : Fin 7 → ℝ³) (t0 ε : ℝ) :
    u0 x t0 + ε • (x 1 - x 2) = u0 x (t0 - ε) := by
  have := u0_add x t0 (-ε)
  rw [← sub_eq_add_neg] at this
  rw [this, neg_smul, ← smul_neg, neg_sub]

theorem det3_x01_x61_u0 (x : Fin 7 → ℝ³) (t : ℝ) :
    det3 (x 0 - x 1) (x 6 - x 1) (u0 x t) = -t * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) := by
  simp only [u0, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring

/-- **Leaf (c): `t:f346-` on the circle of 012, 5-rim `(0,5,3,6,1)`** (root `t* < -1` of facet 346,
`f8 x0 < f8 x2 < f8 x1`). The view `u0 t* - ε (x2 - x1)` has `N8 > 0`, `N1, N3 > 0`, `N2, N5, N6, N7 < 0`;
the rim is `(0,5,3,6,1)` with chord `1 → 0`, middle `2`, interior vertex `4`. Case conditions:
`N3 > 0`, `N6, N7 < 0` at the root (ties broken by the tilt `x1 - x2`), a lexicographic top of the rim depths,
genericity and the Lemma H data. -/
theorem q012_f346_neg_5w (F : S0xFac 9 s0x_S24 x)
    (hlo : F.f 8 (x 0) < F.f 8 (x 2)) (hhi : F.f 8 (x 2) < F.f 8 (x 1))
    (h3 : 0 < ⟪F.N 3, u0 x (tstar F)⟫ ∨ (⟪F.N 3, u0 x (tstar F)⟫ = 0 ∧ 0 < ⟪F.N 3, x 1 - x 2⟫))
    (h6 : ⟪F.N 6, u0 x (tstar F)⟫ < 0 ∨ (⟪F.N 6, u0 x (tstar F)⟫ = 0 ∧ ⟪F.N 6, x 1 - x 2⟫ < 0))
    (h7 : ⟪F.N 7, u0 x (tstar F)⟫ < 0 ∨ (⟪F.N 7, u0 x (tstar F)⟫ = 0 ∧ ⟪F.N 7, x 1 - x 2⟫ < 0))
    (hU : ∃ t : ZMod 5, LexTop (fun i => x (rimC5 i)) (u0 x (tstar F)) (x 1 - x 2) t)
    (hgen : ∀ i j : ZMod 5, i ≠ j →
      ⟪x (rimC5 i) - x (rimC5 j), u0 x (tstar F)⟫ ≠ 0 ∨ ⟪x (rimC5 i) - x (rimC5 j), x 1 - x 2⟫ ≠ 0)
    (w : ZMod 5) (hw : w = 1 ∨ w = 2 ∨ w = 3)
    (hfar : ∀ m : ZMod 5, m ≠ w → rimC5 m ∉ s0x_S24 0 → F.f 0 (x (rimC5 w)) < F.f 0 (x (rimC5 m)))
    (hoff : ⟪F.N 0, cross (x 0 - x 1) (x (rimC5 w) - x 1)⟫ ≠ 0 ∨
      ⟪x (rimC5 w) - x 1, x 0 - x 1⟫ < 0 ∨ ⟪x (rimC5 w) - x 0, x 1 - x 0⟫ < 0) :
    FaceChordView F 0 := by
  set b : ℝ³ := u0 x (tstar F) with hb
  set c : ℝ³ := x 1 - x 2 with hc
  set p : ZMod 5 → ℝ³ := fun i => x (rimC5 i) with hp
  have hP : F.f 8 (x 2) - F.f 8 (x 1) < 0 := by linarith
  have ht0 : tstar F < -1 := by
    rw [tstar, div_lt_iff_of_neg hP]; linarith
  have h8 := inner_N8_tstar F hP.ne
  have ev0 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have evs : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪F.N 3, b + ε • c⟫ ∧ ⟪F.N 6, b + ε • c⟫ < 0 ∧
      ⟪F.N 7, b + ε • c⟫ < 0 := by
    filter_upwards [evp' _ _ _ h3, evn' _ _ _ h6, evn' _ _ _ h7] with ε e3 e6 e7
    exact ⟨e3, e6, e7⟩
  obtain ⟨t, ht⟩ := hU
  have hinj := ev_injective_k b c p hgen
  have hZ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Function.Injective (fun i => ⟪p i, b + ε • c⟫) ∧
      UniOrSep p (b + ε • c) := by
    filter_upwards [ev_lexTop p b c t ht, hinj] with ε h hi
    exact ⟨hi, Or.inl (strictUnimodal_of_cyclic (by decide)
      (isCyclicUnimodal_of_top (by norm_num) hi t h))⟩
  obtain ⟨ε, ⟨e3, e6, e7⟩, hε, hinj', hz⟩ := (evs.and (ev0.and hZ)).exists
  have hε' : (0 : ℝ) < ε := hε
  have hv : b + ε • c = u0 x (tstar F - ε) := view_neg x _ _
  have hN0 : ⟪F.N 0, b + ε • c⟫ = 0 := by rw [hv]; exact inner_N0_u0 F _
  have e1 : 0 < ⟪F.N 1, b + ε • c⟫ := by
    rw [hv, inner_N1_u0]; nlinarith [lambda1_pos F]
  have e2 : ⟪F.N 2, b + ε • c⟫ < 0 := by
    rw [hv, inner_N2_u0]; nlinarith [lambda2_pos F]
  have e5 : ⟪F.N 5, b + ε • c⟫ < 0 := by rw [hv]; exact inner_N5_u0_neg F _
  have e8 : 0 < ⟪F.N 8, b + ε • c⟫ := by
    rw [hv, sub_eq_add_neg, inner_u0_add, h8, zero_add, inner_N8_d]; nlinarith
  obtain ⟨ρ, hρ, hcv, hin4⟩ := rimC5_data F hN0 e1 e2 e3 e5 e6 e7 e8
  have hw' : rimC5 w ∉ s0x_S24 0 := by rcases hw with rfl | rfl | rfl <;> decide
  refine ⟨b + ε • c, 5, inferInstance, rimC5, 4, w, ρ, hN0, by decide, by decide, by decide, hρ,
    hcv, ?_, ?_, hinj', hz, hw', hfar, hoff⟩
  · intro q hq0 hqr i
    have hq4 : q = 4 := by
      fin_cases q <;> first | rfl | (exfalso; revert hq0; decide) | (exfalso; exact hqr 1 rfl) |
        (exfalso; exact hqr 2 rfl) | (exfalso; exact hqr 3 rfl)
    subst hq4
    exact hin4 i
  · intro q hq0 hqr
    have hq2 : q = 2 := by
      fin_cases q <;> first | rfl | (exfalso; revert hq0; decide) | (exfalso; exact hqr 0 rfl) | (exfalso; exact hqr 4 rfl)
    subst hq2
    have ht1 : tstar F - ε + 1 < 0 := by linarith
    have htn : tstar F - ε ≠ 0 := by intro h; linarith
    refine ⟨-1 / (tstar F - ε), 1 / (tstar F - ε), ?_, ?_, by simpa using htn, ?_⟩
    · exact div_pos_of_neg_of_neg (by norm_num) (by linarith)
    · rw [div_lt_one_of_neg (by linarith)]; linarith
    · change x 2 = x 1 + (-1 / (tstar F - ε)) • (x 0 - x 1) + (1 / (tstar F - ε)) • (b + ε • c)
      rw [hv]
      simp only [u0]
      ext j
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      field_simp
      ring

/-- The 6-rim `(2, 0, 4, 6, 3, 5)`; the chord `2 → 0` of facet 012 is the edge from index `0` to index `1`
(vertex `1` is the middle over it). -/
def rimA6 : ZMod 6 → Fin 7
  | 0 => 2
  | 1 => 0
  | 2 => 4
  | 3 => 6
  | 4 => 3
  | 5 => 5

/-- Rim data for `(2,0,4,6,3,5)` from the facet signs `N2, N3, N8 > 0`, `N4, N6, N7 < 0` at a view in the
plane of 012. -/
theorem rimA6_data (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (hN0 : ⟪F.N 0, u⟫ = 0) (h2 : 0 < ⟪F.N 2, u⟫) (h3 : 0 < ⟪F.N 3, u⟫) (h4 : ⟪F.N 4, u⟫ < 0)
    (h6 : ⟪F.N 6, u⟫ < 0) (h7 : ⟪F.N 7, u⟫ < 0) (h8 : 0 < ⟪F.N 8, u⟫) :
    ∃ ρ : ℝ, ρ ≠ 0 ∧ StrictConvexK (fun i => x (rimA6 i)) u ρ := by
  have n01 : cross u (x 0 - x 2) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 2 2 0 (by decide) (by decide) h2.ne' 5 (by decide) (by decide)
  have n12 : cross u (x 4 - x 0) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 4 0 4 (by decide) (by decide) h4.ne 1 (by decide) (by decide)
  have n23 : cross u (x 6 - x 4) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 4 4 6 (by decide) (by decide) h4.ne 3 (by decide) (by decide)
  have n34 : cross u (x 3 - x 6) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 8 6 3 (by decide) (by decide) h8.ne' 1 (by decide) (by decide)
  have n45 : cross u (x 5 - x 3) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 3 3 5 (by decide) (by decide) h3.ne' 8 (by decide) (by decide)
  have n50 : cross u (x 2 - x 5) ≠ 0 :=
    cross_ne_zero_of_facet_sign F 2 5 2 (by decide) (by decide) h2.ne' 3 (by decide) (by decide)
  obtain ⟨σ0, hσ0n, hσ0⟩ := det3_sign_edgeOn F 0 2 0 (by decide) (by decide) u hN0 n01
  obtain ⟨σ1, -, hσ1⟩ := det3_sign_ridge F 4 3 0 4 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u ⟨h4, h3⟩ n12
  obtain ⟨σ2, -, hσ2⟩ := det3_sign_ridge F 4 8 4 6 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u ⟨h4, h8⟩ n23
  obtain ⟨σ3, -, hσ3⟩ := det3_sign_ridge F 7 8 6 3 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u ⟨h7, h8⟩ n34
  obtain ⟨σ4, -, hσ4⟩ := det3_sign_ridge F 6 3 3 5 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u ⟨h6, h3⟩ n45
  obtain ⟨σ5, -, hσ5⟩ := det3_sign_ridge F 6 2 5 2 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ u ⟨h6, h2⟩ n50
  have c0 := Minimality.det3_cycle_triangle (x 2) (x 0) (x 4) u
  have c1 := Minimality.det3_cycle_triangle (x 0) (x 4) (x 6) u
  have c2 := Minimality.det3_cycle_triangle (x 4) (x 6) (x 3) u
  have c3 := Minimality.det3_cycle_triangle (x 6) (x 3) (x 5) u
  have c4 := Minimality.det3_cycle_triangle (x 3) (x 5) (x 2) u
  have p01 : 0 < σ0 * σ1 := sign_prod (hσ0 4 (by decide)) (by rw [c0]; exact hσ1 2 (by decide))
  have p12 : 0 < σ1 * σ2 := sign_prod (hσ1 6 (by decide)) (by rw [c1]; exact hσ2 0 (by decide))
  have p23 : 0 < σ2 * σ3 := sign_prod (hσ2 3 (by decide)) (by rw [c2]; exact hσ3 4 (by decide))
  have p34 : 0 < σ3 * σ4 := sign_prod (hσ3 5 (by decide)) (by rw [c3]; exact hσ4 6 (by decide))
  have p45 : 0 < σ4 * σ5 := sign_prod (hσ4 2 (by decide)) (by rw [c4]; exact hσ5 3 (by decide))
  have s01 := p01
  have s02 := sign_transfer s01 p12
  have s03 := sign_transfer s02 p23
  have s04 := sign_transfer s03 p34
  have s05 := sign_transfer s04 p45
  refine ⟨σ0, hσ0n, ?_⟩
  intro i j hj1 hj2
  rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases zmod6_cases j with rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim (hj1 rfl)
  · exact False.elim (hj2 rfl)
  · exact hσ0 4 (by decide)
  · exact hσ0 6 (by decide)
  · exact hσ0 3 (by decide)
  · exact hσ0 5 (by decide)
  · exact sign_transfer s01 (hσ1 2 (by decide))
  · exact False.elim (hj1 rfl)
  · exact False.elim (hj2 rfl)
  · exact sign_transfer s01 (hσ1 6 (by decide))
  · exact sign_transfer s01 (hσ1 3 (by decide))
  · exact sign_transfer s01 (hσ1 5 (by decide))
  · exact sign_transfer s02 (hσ2 2 (by decide))
  · exact sign_transfer s02 (hσ2 0 (by decide))
  · exact False.elim (hj1 rfl)
  · exact False.elim (hj2 rfl)
  · exact sign_transfer s02 (hσ2 3 (by decide))
  · exact sign_transfer s02 (hσ2 5 (by decide))
  · exact sign_transfer s03 (hσ3 2 (by decide))
  · exact sign_transfer s03 (hσ3 0 (by decide))
  · exact sign_transfer s03 (hσ3 4 (by decide))
  · exact False.elim (hj1 rfl)
  · exact False.elim (hj2 rfl)
  · exact sign_transfer s03 (hσ3 5 (by decide))
  · exact sign_transfer s04 (hσ4 2 (by decide))
  · exact sign_transfer s04 (hσ4 0 (by decide))
  · exact sign_transfer s04 (hσ4 4 (by decide))
  · exact sign_transfer s04 (hσ4 6 (by decide))
  · exact False.elim (hj1 rfl)
  · exact False.elim (hj2 rfl)
  · exact False.elim (hj2 rfl)
  · exact sign_transfer s05 (hσ5 0 (by decide))
  · exact sign_transfer s05 (hσ5 4 (by decide))
  · exact sign_transfer s05 (hσ5 6 (by decide))
  · exact sign_transfer s05 (hσ5 3 (by decide))
  · exact False.elim (hj1 rfl)

theorem det3_x02_x62_u0 (x : Fin 7 → ℝ³) (t : ℝ) :
    det3 (x 0 - x 2) (x 6 - x 2) (u0 x t) = -(1 + t) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) := by
  simp only [u0, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring

/-- **Leaf (a): the 6-rim `(2,0,4,6,3,5)` at the 346-root with `t* > 0`** (mirror of `s:f235+`; `t:f346+` on
the circle of 012). The root `t* > 0` of facet 346 (`f8 x0 < f8 x1 < f8 x2`), the view `u0 t* + ε (x2 - x1)`
(`N8 > 0`, `N2, N3 > 0`, `N4, N6, N7 < 0`), rim `(0,4,6,3,5,2)` with chord `2 → 0` and middle `1`. Case
conditions: `N3 > 0`, `N4, N6, N7 < 0` at the root (ties broken by the tilt `x2 - x1`), a lexicographic top
of the rim depths, genericity and the Lemma H data. -/
theorem q012_f346_pos_6w (F : S0xFac 9 s0x_S24 x)
    (hlo : F.f 8 (x 0) < F.f 8 (x 1)) (hhi : F.f 8 (x 1) < F.f 8 (x 2))
    (h3 : 0 < ⟪F.N 3, u0 x (tstar F)⟫ ∨ (⟪F.N 3, u0 x (tstar F)⟫ = 0 ∧ 0 < ⟪F.N 3, x 2 - x 1⟫))
    (h4 : ⟪F.N 4, u0 x (tstar F)⟫ < 0 ∨ (⟪F.N 4, u0 x (tstar F)⟫ = 0 ∧ ⟪F.N 4, x 2 - x 1⟫ < 0))
    (h6 : ⟪F.N 6, u0 x (tstar F)⟫ < 0 ∨ (⟪F.N 6, u0 x (tstar F)⟫ = 0 ∧ ⟪F.N 6, x 2 - x 1⟫ < 0))
    (h7 : ⟪F.N 7, u0 x (tstar F)⟫ < 0 ∨ (⟪F.N 7, u0 x (tstar F)⟫ = 0 ∧ ⟪F.N 7, x 2 - x 1⟫ < 0))
    (hU : ∃ t : ZMod 6, LexTop (fun i => x (rimA6 i)) (u0 x (tstar F)) (x 2 - x 1) t)
    (hgen : ∀ i j : ZMod 6, i ≠ j →
      ⟪x (rimA6 i) - x (rimA6 j), u0 x (tstar F)⟫ ≠ 0 ∨ ⟪x (rimA6 i) - x (rimA6 j), x 2 - x 1⟫ ≠ 0)
    (w : ZMod 6) (hw : w = 2 ∨ w = 3 ∨ w = 4 ∨ w = 5)
    (hfar : ∀ m : ZMod 6, m ≠ w → rimA6 m ∉ s0x_S24 0 → F.f 0 (x (rimA6 w)) < F.f 0 (x (rimA6 m)))
    (hoff : Off012 F (rimA6 w)) :
    FaceChordView F 0 := by
  set b : ℝ³ := u0 x (tstar F) with hb
  set c : ℝ³ := x 2 - x 1 with hc
  set Ω := det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) with hΩ
  set p : ZMod 6 → ℝ³ := fun i => x (rimA6 i) with hp
  have hP : 0 < F.f 8 (x 2) - F.f 8 (x 1) := by linarith
  have ht0 : 0 < tstar F := div_pos (by linarith) hP
  have h8 := inner_N8_tstar F hP.ne'
  have ev0 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have evs : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ⟪F.N 3, b + ε • c⟫ ∧ ⟪F.N 4, b + ε • c⟫ < 0 ∧
      ⟪F.N 6, b + ε • c⟫ < 0 ∧ ⟪F.N 7, b + ε • c⟫ < 0 := by
    filter_upwards [evp' _ _ _ h3, evn' _ _ _ h4, evn' _ _ _ h6, evn' _ _ _ h7] with ε e3 e4 e6 e7
    exact ⟨e3, e4, e6, e7⟩
  obtain ⟨t, ht⟩ := hU
  have hinj := ev_injective_k b c p hgen
  have hZ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Function.Injective (fun i => ⟪p i, b + ε • c⟫) ∧
      UniOrSep p (b + ε • c) := by
    filter_upwards [ev_lexTop p b c t ht, hinj] with ε h hi
    exact ⟨hi, Or.inl (strictUnimodal_of_cyclic (by decide)
      (isCyclicUnimodal_of_top (by norm_num) hi t h))⟩
  obtain ⟨ε, ⟨e3, e4, e6, e7⟩, hε, hinj', hz⟩ := (evs.and (ev0.and hZ)).exists
  have hε' : (0 : ℝ) < ε := hε
  have hv : b + ε • c = u0 x (tstar F + ε) := (u0_add x _ _).symm
  have hN0 : ⟪F.N 0, b + ε • c⟫ = 0 := by rw [hv]; exact inner_N0_u0 F _
  have e2 : 0 < ⟪F.N 2, b + ε • c⟫ := by
    rw [hv, inner_N2_u0]; exact mul_pos (lambda2_pos F) (by linarith)
  have e8 : 0 < ⟪F.N 8, b + ε • c⟫ := by
    rw [hv, inner_u0_add, h8, zero_add, inner_N8_d]; exact mul_pos hε' hP
  obtain ⟨ρ, hρ, hcv⟩ := rimA6_data F hN0 e2 e3 e4 e6 e7 e8
  have hρΩ : ρ * Ω < 0 := by
    have h := hcv 0 3 (by decide) (by decide)
    have e : det3 (x (rimA6 (0 + 1)) - x (rimA6 0)) (x (rimA6 3) - x (rimA6 0)) (b + ε • c) =
        -(1 + (tstar F + ε)) * Ω := by
      rw [hv]; exact det3_x02_x62_u0 x _
    rw [e] at h
    have h1 : 0 < ρ * (-(1 + (tstar F + ε)) * Ω) := h
    have h2 : 0 < 1 + (tstar F + ε) := by linarith
    by_contra hn; push Not at hn
    nlinarith [mul_nonneg h2.le hn]
  have hcv' := strictConvexK_of_rho hρΩ hcv
  have hw' : rimA6 w ∉ s0x_S24 0 := by rcases hw with rfl | rfl | rfl | rfl <;> decide
  refine ⟨b + ε • c, 6, inferInstance, rimA6, 0, w, -Ω, hN0, by decide, by decide, by decide,
    neg_ne_zero.mpr (omega_ne_zero F), hcv', ?_, ?_, hinj', hz, hw', hfar, hoff⟩
  · intro q hq0 hqr i
    exfalso
    fin_cases q
    · exact hq0 (by decide)
    · exact hq0 (by decide)
    · exact hq0 (by decide)
    · exact hqr 4 rfl
    · exact hqr 2 rfl
    · exact hqr 5 rfl
    · exact hqr 3 rfl
  · intro q hq0 hqr
    have hq1 : q = 1 := by
      fin_cases q <;> first | rfl | (exfalso; revert hq0; decide) | (exfalso; exact hqr 1 rfl) |
        (exfalso; exact hqr 0 rfl)
    subst hq1
    have h2 : 0 < 1 + (tstar F + ε) := by linarith
    refine ⟨1 / (1 + (tstar F + ε)), -1 / (1 + (tstar F + ε)), by positivity, ?_,
      div_ne_zero (by norm_num) h2.ne', ?_⟩
    · rw [div_lt_one h2]; linarith
    · change x 1 = x 2 + (1 / (1 + (tstar F + ε))) • (x 0 - x 2) +
        (-1 / (1 + (tstar F + ε))) • (b + ε • c)
      rw [hv]
      simp only [u0]
      ext j
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      field_simp
      ring

end Minimality.T24.R012
