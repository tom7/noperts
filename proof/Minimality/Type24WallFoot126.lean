module

public import Minimality.Type24Cell

/-!
# Type 24: the wall line of facet `126` (generic wall lemmas and the pentagon `cellP`)

Formalizes (and referees) L2-L4 of nopert229 notes/TRISTAR-PLAN.md section 4 (background: FABLE-TRI-REPLY.md
section 1).  Corner frame at vertex `1`: `e_a = x 0 - x 1`, `e_b = x 2 - x 1`, `e_c = x 6 - x 1`,
`capView x ca cb cc = ca e_a + cb e_b + cc e_c`, depths `z_v = ⟪x v - x 1, w⟫`.

* Facet values on every cone view (`cap_f0`, `cap_f1`, `cap_f2`, `cap_f4`, `cap_f5`, `cap_f7`).
* **Wall `126`** (facet `5`): the views `capView x η 1 cc`, `η → 0+`.  `wall126_cellAt_eventually` (strict facet
  signs at `v0 = capView x 0 1 cc` except `126`, which vanishes there, give the open cell for small `η > 0`),
  `wall126_lt_eventually` (strict depth comparisons persist), `wall126_q4_lexAny` (generic 4-rim leaf).
  On the line `126` vanishes, `012`, `016` are back, `236` is front, `025` is front iff `cc < 1/ω5`, `046` is front
  iff `cc > ω4`; `0345`, `235`, `346` are hypotheses.  The foot is `r26 = (g_b - G_bc) / (g_c - G_bc)`
  (`wall126_z2_sub_z6`: `z2 - z6 = (g_c - G_bc) (r26 - cc)`).
* **Pentagon `cellP`** (rim `0.4.6.2.5`, the generic part of WF2): `robUni_window5` (a 5-rim with an
  axis pair `1, 2` / `3, 2` ordered and a low vertex `0` below one rim neighbour is `RobUni`), `cellAtP_lexAny`
  (open-cell certificate), `wallP_lexAny` (on the wall line at any `cc` in the window).
* Pruned 11-27 pass 3 (see TOOLBOX-LEAN): L2 = CW2 (`cellAt0264_lexAny`, `cellW2_0526_lexAny`, `cellW2_0264_lexAny`,
  `wallFoot126_above/below`), the window-foot lemmas WF2 / WF0 (`windowFoot126_lexAny(_of_tie)`, `cellAtC_lexAny`,
  `wallC_lexAny`, `windowFoot016_lexAny(_of_tie)`, `windowFoot012_lexAny`), the region Props `CW2Above`, `CW2Below`,
  `WF2At`, `WF0At` with their `_twin` versions and `HoleLeaf` forms.  Kept: the facet-value lemmas, `wall126_*`,
  `robUni_window5`, `robUni_of_rotate`, `cellAtP_lexAny`, `wallP_lexAny`.
* Generic: `robUni_window5`, `robUni_of_rotate` (`RobUni` is rotation invariant).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace Topology
open Finset Filter
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.RimCell Minimality.T24.HC

namespace Minimality.T24.WallFoot126

variable {x : Fin 7 → ℝ³}

/-! ## Facet values on the cone views -/

theorem cap_f0 (F : S0xFac 9 s0x_S24 x) (ca cb cc : ℝ) :
    ⟪F.N 0, capView x ca cb cc⟫ = cc * F.f 0 (x 6) := by
  rw [Belt.inner_cap, F.zero 0 0 (by decide), F.zero 0 1 (by decide), F.zero 0 2 (by decide)]; ring

theorem cap_f1 (F : S0xFac 9 s0x_S24 x) (ca cb cc : ℝ) :
    ⟪F.N 1, capView x ca cb cc⟫ = cb * F.f 1 (x 2) := by
  rw [Belt.inner_cap, F.zero 1 0 (by decide), F.zero 1 1 (by decide), F.zero 1 6 (by decide)]; ring

theorem cap_f5 (F : S0xFac 9 s0x_S24 x) (ca cb cc : ℝ) :
    ⟪F.N 5, capView x ca cb cc⟫ = ca * F.f 5 (x 0) := by
  rw [Belt.inner_cap, F.zero 5 1 (by decide), F.zero 5 2 (by decide), F.zero 5 6 (by decide)]; ring

theorem cap_f7 (F : S0xFac 9 s0x_S24 x) (ca cb cc : ℝ) :
    ⟪F.N 7, capView x ca cb cc⟫ = -F.f 7 (x 1) * (cb + cc - omega3 x * ca) := by
  rw [Belt.inner_cap, Belt.f7_rel F, F.zero 7 2 (by decide), F.zero 7 6 (by decide)]; ring

/-- `f4 x2 - f4 x1 = ω4 f4 x1` (facet `046` through `x 4`). -/
theorem f4_rel (F : S0xFac 9 s0x_S24 x) : F.f 4 (x 2) - F.f 4 (x 1) = omega4 x * F.f 4 (x 1) := by
  have hb4 : 0 < oblX2 x 4 := (M4.type24OfFac F).X2_pos (v := 4) (by decide)
  have ev := M4.fac_eval F 4 4
  rw [F.zero 4 4 (by decide), F.zero 4 0 (by decide), F.zero 4 6 (by decide)] at ev
  have e4 := M4.eq4 F
  have h : oblX2 x 4 * ((F.f 4 (x 2) - F.f 4 (x 1)) - omega4 x * F.f 4 (x 1)) = 0 := by
    linear_combination -ev + F.f 4 (x 1) * e4
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hb4.ne')

/-- `f2 x6 - f2 x1 = ω5 f2 x1` (facet `025` through `x 5`). -/
theorem f2_rel (F : S0xFac 9 s0x_S24 x) : F.f 2 (x 6) - F.f 2 (x 1) = omega5 x * F.f 2 (x 1) := by
  have hc5 : 0 < oblX6 x 5 := (M4.type24OfFac F).X6_pos (v := 5) (by decide)
  have ev := M4.fac_eval F 2 5
  rw [F.zero 2 5 (by decide), F.zero 2 0 (by decide), F.zero 2 2 (by decide)] at ev
  have e5 := M4.eq5 F
  have h : oblX6 x 5 * ((F.f 2 (x 6) - F.f 2 (x 1)) - omega5 x * F.f 2 (x 1)) = 0 := by
    linear_combination -ev + F.f 2 (x 1) * e5
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hc5.ne')

theorem cap_f4 (F : S0xFac 9 s0x_S24 x) (ca cb cc : ℝ) :
    ⟪F.N 4, capView x ca cb cc⟫ = -F.f 4 (x 1) * (ca + cc - omega4 x * cb) := by
  rw [Belt.inner_cap, f4_rel F, F.zero 4 0 (by decide), F.zero 4 6 (by decide)]; ring

theorem cap_f2 (F : S0xFac 9 s0x_S24 x) (ca cb cc : ℝ) :
    ⟪F.N 2, capView x ca cb cc⟫ = -F.f 2 (x 1) * (ca + cb - omega5 x * cc) := by
  rw [Belt.inner_cap, f2_rel F, F.zero 2 0 (by decide), F.zero 2 2 (by decide)]; ring

theorem omega45_gt_one (hC : CbarIn x) : 1 < omega4 x * omega5 x := by
  refine omega_prod_gt_one hC.2.1 hC.2.2.1 hC.1 ?_
  have h := hC.2.2.2
  unfold Delta24 at h
  linarith [show omega4 x * omega5 x * omega3 x = omega3 x * omega4 x * omega5 x by ring]

/-! ## The wall line of facet `126` -/

/-- Every linear form along the wall line of `126` is affine in `η`. -/
theorem inner_wall126 (y : ℝ³) (η cc : ℝ) :
    ⟪y, capView x η 1 cc⟫ = ⟪y, capView x 0 1 cc⟫ + η * ⟪y, x 0 - x 1⟫ := by
  simp only [capView, inner_add_right, real_inner_smul_right]; ring

/-- The base view `v0 = e_b + cc e_c` of the wall line, as an affine function of `cc`. -/
theorem inner_v0 (y : ℝ³) (cc : ℝ) :
    ⟪y, capView x 0 1 cc⟫ = ⟪y, x 2 - x 1⟫ + cc * ⟪y, x 6 - x 1⟫ := by
  simp only [capView, inner_add_right, real_inner_smul_right]; ring

private theorem ev_lin {A B : ℝ} (h : 0 < A) : ∀ᶠ η : ℝ in 𝓝[>] 0, 0 < A + η * B := by
  have hc : Continuous (fun η : ℝ => A + η * B) := by fun_prop
  have ht : Tendsto (fun η : ℝ => A + η * B) (𝓝 0) (𝓝 A) := by simpa using hc.tendsto 0
  exact nhdsWithin_le_nhds (ht.eventually (lt_mem_nhds h))

/-- **Wall `126`, cell.** Strict facet signs at `v0 = capView x 0 1 cc` for the up facets `U` and for the down
facets `Dn` other than `126` (which vanishes at `v0`) give the open cell at `capView x η 1 cc`, small `η > 0`. -/
theorem wall126_cellAt_eventually (F : S0xFac 9 s0x_S24 x) {U Dn : Finset (Fin 9)} {cc : ℝ}
    (hU : ∀ t ∈ U, 0 < ⟪F.N t, capView x 0 1 cc⟫)
    (hD : ∀ t ∈ Dn, t ≠ 5 → ⟪F.N t, capView x 0 1 cc⟫ < 0) :
    ∀ᶠ η : ℝ in 𝓝[>] 0, CellAt F U Dn (capView x η 1 cc) := by
  refine (Filter.eventually_all_finset U |>.2 fun t ht => ?_).and
    (Filter.eventually_all_finset Dn |>.2 fun t ht => ?_)
  · exact (ev_lin (B := ⟪F.N t, x 0 - x 1⟫) (hU t ht)).mono fun η h => by rw [inner_wall126]; exact h
  · by_cases h : t = 5
    · subst h
      filter_upwards [self_mem_nhdsWithin] with η (hη : 0 < η)
      rw [cap_f5]; exact mul_neg_of_pos_of_neg hη (F.neg 5 0 (by decide))
    · exact (ev_lin (B := -⟪F.N t, x 0 - x 1⟫) (neg_pos.2 (hD t ht h))).mono fun η hη => by
        rw [inner_wall126]; linarith

/-- **Wall `126`, depths.** A strict depth comparison at `v0` persists at `capView x η 1 cc`, small `η > 0`. -/
theorem wall126_lt_eventually {u v : Fin 7} {cc : ℝ}
    (h : ⟪x u - x 1, capView x 0 1 cc⟫ < ⟪x v - x 1, capView x 0 1 cc⟫) :
    ∀ᶠ η : ℝ in 𝓝[>] 0, ⟪x u, capView x η 1 cc⟫ < ⟪x v, capView x η 1 cc⟫ := by
  have h' : 0 < ⟪x v - x u, capView x 0 1 cc⟫ := by
    have e : x v - x u = (x v - x 1) - (x u - x 1) := by abel
    rw [e, inner_sub_left]; linarith
  refine (ev_lin (B := ⟪x v - x u, x 0 - x 1⟫) h').mono fun η hη => ?_
  rw [← inner_wall126, inner_sub_left] at hη; linarith

/-- **Generic wall-`126` Q4 leaf.** A 4-rim cell `(U, Dn)` on the wall line (facet signs at `v0` as in
`wall126_cellAt_eventually`) whose diagonal forms take a strictly negative and a strictly positive value at `v0`
gives `Gen.LexAny F`. -/
theorem wall126_q4_lexAny (F : S0xFac 9 s0x_S24 x) {c : ZMod 4 → Fin 7} (hc : Function.Injective c)
    {U Dn : Finset (Fin 9)} (hcyc : S0xCycUD s0x_S24 c U Dn) {cc : ℝ}
    (hU : ∀ t ∈ U, 0 < ⟪F.N t, capView x 0 1 cc⟫)
    (hD : ∀ t ∈ Dn, t ≠ 5 → ⟪F.N t, capView x 0 1 cc⟫ < 0)
    (hn : ∃ p ∈ diagPairs, ⟪x (c p.1) - x (c p.2), capView x 0 1 cc⟫ < 0)
    (hp : ∃ p ∈ diagPairs, 0 < ⟪x (c p.1) - x (c p.2), capView x 0 1 cc⟫) :
    Gen.LexAny F := by
  obtain ⟨p, hpm, hpv⟩ := hn
  obtain ⟨q, hqm, hqv⟩ := hp
  have en := ev_lin (B := -⟪x (c p.1) - x (c p.2), x 0 - x 1⟫) (neg_pos.2 hpv)
  have ep := ev_lin (B := ⟪x (c q.1) - x (c q.2), x 0 - x 1⟫) hqv
  obtain ⟨η, hcell, h1, h2⟩ := ((wall126_cellAt_eventually F hU hD).and (en.and ep)).exists
  refine WC.lexAny_of_cellAt_robUni le_rfl F hc hcyc hcell (robUni_four_of_mixed ?_ ?_)
  · exact ⟨p, hpm, by rw [← inner_sub_left, inner_wall126]; linarith⟩
  · exact ⟨q, hqm, by rw [← inner_sub_left, inner_wall126]; linarith⟩

/-! ## The foot `r26` -/

/-- The foot of the tie `z2 = z6` on the wall line of `126`: `r26 = (g_b - G_bc) / (g_c - G_bc)`. -/
noncomputable def r26 (x : Fin 7 → ℝ³) : ℝ :=
  (⟪x 2 - x 1, x 2 - x 1⟫ - ⟪x 2 - x 1, x 6 - x 1⟫) /
    (⟪x 6 - x 1, x 6 - x 1⟫ - ⟪x 2 - x 1, x 6 - x 1⟫)

/-- `z2 - z6 = (g_c - G_bc) (r26 - cc)` on the wall line of `126`, and `g_c - G_bc > 0` when `G_bc ≤ 0`. -/
theorem wall126_z2_sub_z6 (F : S0xFac 9 s0x_S24 x) (hbc : ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0) (cc : ℝ) :
    0 < ⟪x 6 - x 1, x 6 - x 1⟫ - ⟪x 2 - x 1, x 6 - x 1⟫ ∧
    ⟪x 2 - x 1, capView x 0 1 cc⟫ - ⟪x 6 - x 1, capView x 0 1 cc⟫ =
      (⟪x 6 - x 1, x 6 - x 1⟫ - ⟪x 2 - x 1, x 6 - x 1⟫) * (r26 x - cc) := by
  have h61 : x 6 - x 1 ≠ 0 := sub_ne_zero.mpr fun h => by
    exact absurd (EdgeViewLink.inj_of_fac24 F h) (by decide)
  have hgc : 0 < ⟪x 6 - x 1, x 6 - x 1⟫ := real_inner_self_pos.mpr h61
  have hD : 0 < ⟪x 6 - x 1, x 6 - x 1⟫ - ⟪x 2 - x 1, x 6 - x 1⟫ := by linarith
  refine ⟨hD, ?_⟩
  unfold r26
  rw [mul_sub, mul_div_cancel₀ _ hD.ne', inner_v0, inner_v0, real_inner_comm (x 2 - x 1) (x 6 - x 1)]
  ring

/-- `r26 > 0` when `G_bc ≤ 0`. -/
theorem r26_pos (F : S0xFac 9 s0x_S24 x) (hbc : ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0) : 0 < r26 x := by
  have h21 : x 2 - x 1 ≠ 0 := sub_ne_zero.mpr fun h => by
    exact absurd (EdgeViewLink.inj_of_fac24 F h) (by decide)
  have hgb : 0 < ⟪x 2 - x 1, x 2 - x 1⟫ := real_inner_self_pos.mpr h21
  exact div_pos (by linarith) (wall126_z2_sub_z6 F hbc 0).1

/-! ## L2 = CW2: Lemma F4 on wall `126` (cells `0.5.2.6` above the window, `0.2.6.4` below it) -/

/-- Rim `0.2.6.4` (vertices `1, 3, 5` hidden; the `π_24` twin of `0.5.2.6`). -/
def c0264 : ZMod 4 → Fin 7 := ![0, 2, 6, 4]
def U0264 : Finset (Fin 9) := {2, 3, 6, 7, 8}
def Dn0264 : Finset (Fin 9) := {0, 1, 4, 5}

theorem c0264_inj : Function.Injective c0264 := by
  intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)

theorem cyc0264 : S0xCycUD s0x_S24 c0264 U0264 Dn0264 := by decide

/-! ## L3 = WF2: the window foot on wall `126` (pentagon `0.4.6.2.5`) -/

private theorem zmod5_cases (B : ZMod 5) : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := by
  revert B; decide

/-- **Window 5-rim.** A 5-cycle `z` with the axis pair `(2, 3)` ordered away from the rim neighbour `1` of `2`
(`z1 < z2 < z3`) or away from the rim neighbour `4` of `3` (`z4 < z3 < z2`), and the low position `0` below one of
its rim neighbours (`z0 < z1` or `z0 < z4`), is `RobUni`. -/
theorem robUni_window5 {z : ZMod 5 → ℝ} (hax : (z 1 < z 2 ∧ z 2 < z 3) ∨ (z 4 < z 3 ∧ z 3 < z 2))
    (hlow : z 0 < z 1 ∨ z 0 < z 4) : RobUni z := by
  intro B b c d hb hbc hcd hdk
  have hb5 : b < 5 := by omega
  have hc5 : c < 5 := by omega
  have hd5 : d < 5 := by omega
  have hZ5 :
      ((0 : ZMod 5) + 1 = 1 ∧ (0 : ZMod 5) + 2 = 2 ∧ (0 : ZMod 5) + 3 = 3 ∧ (0 : ZMod 5) + 4 = 4) ∧
      ((1 : ZMod 5) + 1 = 2 ∧ (1 : ZMod 5) + 2 = 3 ∧ (1 : ZMod 5) + 3 = 4 ∧ (1 : ZMod 5) + 4 = 0) ∧
      ((2 : ZMod 5) + 1 = 3 ∧ (2 : ZMod 5) + 2 = 4 ∧ (2 : ZMod 5) + 3 = 0 ∧ (2 : ZMod 5) + 4 = 1) ∧
      ((3 : ZMod 5) + 1 = 4 ∧ (3 : ZMod 5) + 2 = 0 ∧ (3 : ZMod 5) + 3 = 1 ∧ (3 : ZMod 5) + 4 = 2) ∧
      ((4 : ZMod 5) + 1 = 0 ∧ (4 : ZMod 5) + 2 = 1 ∧ (4 : ZMod 5) + 3 = 2 ∧ (4 : ZMod 5) + 4 = 3) := by
    decide
  rcases zmod5_cases B with rfl | rfl | rfl | rfl | rfl <;>
  · interval_cases b <;> interval_cases c <;> interval_cases d <;>
    · simp only [Nat.cast_one, Nat.cast_ofNat, hZ5]
      rintro ⟨h1, h2, h3, h4⟩
      rcases hax with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases hlow with l | l <;> linarith

/-- `RobUni` is invariant under rotating the cycle. -/
theorem robUni_of_rotate {k : ℕ} {z : ZMod k → ℝ} (s : ZMod k) (h : RobUni (fun i => z (i + s))) :
    RobUni z := by
  intro B b c d hb hbc hcd hdk
  have e : ∀ m : ZMod k, B - s + m + s = B + m := fun m => by ring
  have := h (B - s) b c d hb hbc hcd hdk
  simpa only [e, sub_add_cancel] using this

/-- **Pentagon certificate** (`cellP`, rim `0.4.6.2.5`; any open-cell view `w`, `z = ⟪x ·, w⟫`): the axis pair
`6, 2` ordered away from the lower axis vertex's other rim neighbour (`z4 < z6 < z2` or `z5 < z2 < z6`) and the low
vertex `0` below `z4` or `z5` => `Gen.LexAny`. -/
theorem cellAtP_lexAny (F : S0xFac 9 s0x_S24 x) {w : ℝ³} (hw : CellAt F Cell.cellP.U (univ \ Cell.cellP.U) w)
    (hax : (⟪x 4, w⟫ < ⟪x 6, w⟫ ∧ ⟪x 6, w⟫ < ⟪x 2, w⟫) ∨ (⟪x 5, w⟫ < ⟪x 2, w⟫ ∧ ⟪x 2, w⟫ < ⟪x 6, w⟫))
    (hlow : ⟪x 0, w⟫ < ⟪x 4, w⟫ ∨ ⟪x 0, w⟫ < ⟪x 5, w⟫) :
    Gen.LexAny F :=
  Cell.lexAny_of_cellRob F Cell.cellP hw (robUni_window5 (z := fun i => ⟪x (Cell.rP i), w⟫) hax hlow)

/-- **Wall `126`, pentagon** (window `1/ω5 < cc < ω4`, `0345`, `235`, `346` front at `v0`; only `ω5 > 0` of
`CbarIn`): the conditions of `cellAtP_lexAny`, strict at `v0`, give `Gen.LexAny`. -/
theorem wallP_lexAny (F : S0xFac 9 s0x_S24 x) (h5 : 0 < omega5 x) {cc : ℝ} (hw5 : 1 / omega5 x < cc)
    (hw4 : cc < omega4 x)
    (h3 : 0 < ⟪F.N 3, capView x 0 1 cc⟫) (h6 : 0 < ⟪F.N 6, capView x 0 1 cc⟫)
    (h8 : 0 < ⟪F.N 8, capView x 0 1 cc⟫)
    (hax : (⟪x 4 - x 1, capView x 0 1 cc⟫ < ⟪x 6 - x 1, capView x 0 1 cc⟫ ∧
        ⟪x 6 - x 1, capView x 0 1 cc⟫ < ⟪x 2 - x 1, capView x 0 1 cc⟫) ∨
      (⟪x 5 - x 1, capView x 0 1 cc⟫ < ⟪x 2 - x 1, capView x 0 1 cc⟫ ∧
        ⟪x 2 - x 1, capView x 0 1 cc⟫ < ⟪x 6 - x 1, capView x 0 1 cc⟫))
    (hlow : ⟪x 0 - x 1, capView x 0 1 cc⟫ < ⟪x 4 - x 1, capView x 0 1 cc⟫ ∨
      ⟪x 0 - x 1, capView x 0 1 cc⟫ < ⟪x 5 - x 1, capView x 0 1 cc⟫) :
    Gen.LexAny F := by
  have hcc : 0 < cc := lt_trans (one_div_pos.mpr h5) hw5
  have hw5' : 1 < omega5 x * cc := by
    have := mul_lt_mul_of_pos_left hw5 h5
    rwa [mul_one_div_cancel h5.ne'] at this
  have hcell := wall126_cellAt_eventually F (U := {3, 6, 7, 8}) (Dn := {0, 1, 2, 4, 5}) (cc := cc)
    (fun t ht => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · exact h3
      · exact h6
      · rw [cap_f7]; nlinarith [F.neg 7 1 (by decide)]
      · exact h8)
    (fun t ht h5' => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl
      · rw [cap_f0]; exact mul_neg_of_pos_of_neg hcc (F.neg 0 6 (by decide))
      · rw [cap_f1]; linarith [F.neg 1 2 (by decide)]
      · rw [cap_f2]; nlinarith [F.neg 2 1 (by decide)]
      · rw [cap_f4]; nlinarith [F.neg 4 1 (by decide)]
      · exact absurd rfl h5')
  have hax' : ∀ᶠ η : ℝ in 𝓝[>] 0,
      (⟪x 4, capView x η 1 cc⟫ < ⟪x 6, capView x η 1 cc⟫ ∧ ⟪x 6, capView x η 1 cc⟫ < ⟪x 2, capView x η 1 cc⟫) ∨
      (⟪x 5, capView x η 1 cc⟫ < ⟪x 2, capView x η 1 cc⟫ ∧ ⟪x 2, capView x η 1 cc⟫ < ⟪x 6, capView x η 1 cc⟫) := by
    rcases hax with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · exact ((wall126_lt_eventually a1).and (wall126_lt_eventually a2)).mono fun _ h => Or.inl h
    · exact ((wall126_lt_eventually a1).and (wall126_lt_eventually a2)).mono fun _ h => Or.inr h
  have hlow' : ∀ᶠ η : ℝ in 𝓝[>] 0,
      ⟪x 0, capView x η 1 cc⟫ < ⟪x 4, capView x η 1 cc⟫ ∨ ⟪x 0, capView x η 1 cc⟫ < ⟪x 5, capView x η 1 cc⟫ := by
    rcases hlow with l | l
    · exact (wall126_lt_eventually l).mono fun _ h => Or.inl h
    · exact (wall126_lt_eventually l).mono fun _ h => Or.inr h
  obtain ⟨η, hc, ha, hl⟩ := (hcell.and (hax'.and hlow')).exists
  have e : (univ \ Cell.cellP.U : Finset (Fin 9)) = {0, 1, 2, 4, 5} := by decide
  exact cellAtP_lexAny F (by rw [e]; exact hc) ha hl

end Minimality.T24.WallFoot126
