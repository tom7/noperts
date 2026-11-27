module

public import Minimality.Type24Cell

/-!
# Type 24: the wall line of facet `126` (CW2 = Lemma F4 there) and the window-foot lemmas WF2, WF0

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
* **L2 = CW2** (Lemma F4 on wall `126`): `cellW2_0526_lexAny` (cell `0.5.2.6` = `C'`, `cc > ω4`),
  `cellW2_0264_lexAny` (new cell `0.2.6.4`, `0 < cc < 1/ω5`; the `π_24` twin of `0.5.2.6`), each with the general
  not-a-crown condition; F4 forms `wallFoot126_above` (`ω4 < cc < r26`, `z0 < z6`) and `wallFoot126_below`
  (`r26 < cc < 1/ω5`, `z0 < z2`); open-cell certificate `cellAt0264_lexAny`.
* **L3 = WF2** (window foot on wall `126`, pentagon `cellP` = rim `0.4.6.2.5`): `robUni_window5` (a 5-rim with an
  axis pair `1, 2` / `3, 2` ordered and a low vertex `0` below one rim neighbour is `RobUni`), `cellAtP_lexAny`
  (open-cell certificate), `wallP_lexAny` (on the wall line at any `cc` in the window), `windowFoot126_lexAny_of_tie`
  (at any tie `z2 = z6` in the window; no metric hypothesis), `windowFoot126_lexAny` (at `r26`, `G_bc ≤ 0`).
* **L4 = WF0** (window foot on walls `016` / `012`, cell `C` = `w_C`, rim `0.5.2.3.6`): `cellAtC_lexAny`,
  `wallC_lexAny`, `windowFoot016_lexAny_of_tie`, `windowFoot016_lexAny` (at `r60`, `G_ac ≤ 0`), the `012` wall
  `windowFoot012_lexAny` (= the `016` wall of `x ∘ π_24`).
* Region forms (named Props, cc-free or `∃ cc`): `CW2Above`, `CW2Below` (L2), `WF2At` (L3), `WF0At` (L4; on
  `x ∘ π_24` = the `012` wall), with `lexAny_of_*`, `_twin` versions (the same Prop on `x ∘ π_24`, `sym24 F`) and
  `HoleLeaf` forms `holeLeaf_not_cw2Above(_twin)`, `holeLeaf_not_cw2Below(_twin)`, `holeLeaf_not_wf2At(_twin)`,
  `holeLeaf_not_wf0At(_twin)`.
* Generic: `robUni_window5`, `robUni_of_rotate` (`RobUni` is rotation invariant).

Referee notes: (1) F4 on `0.5.2.6` (`ω4 < cc < r26`) needs `z0 < z6` at the chosen `cc` (Fable's `z6 > 0`); the plan's
"`z0 ≤ 0` from OB1" alone does not exclude the crown `{z0, z2} ≥ {z5, z6}` (exact: 63 side-instances of the
pool + occensus have a `cc ∈ (ω4, r26)` with the facet signs and `z6 < z0`).  (2) The window-foot lemmas hold with
`max` read literally (`z0 < max(z4, z5)`, no assumption that `0` is the lowest rim vertex), need no `OB1` and no
`k > 0`, and in the tie form no metric hypothesis at all (the tie slope `g_c - G_bc` cannot vanish at a tie:
`x 2 ≠ x 6`); only `ω5 > 0` of `CbarIn` is used.  (3) CW2 needs only `CbarIn` (for `ω4 ω5 > 1`), and the F4 forms
only `G_bc ≤ 0` of `OB1`.
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

/-- **Cell `0.2.6.4` certificate** (any open-cell view `w`): one comparison breaking `{z0, z6} ≥ {z2, z4}` and one
breaking `{z2, z4} ≥ {z0, z6}` (`z = ⟪x ·, w⟫`) => `Gen.LexAny`. -/
theorem cellAt0264_lexAny (F : S0xFac 9 s0x_S24 x) {w : ℝ³} (hw : CellAt F U0264 Dn0264 w)
    (hn : ⟪x 0, w⟫ < ⟪x 2, w⟫ ∨ ⟪x 0, w⟫ < ⟪x 4, w⟫ ∨ ⟪x 6, w⟫ < ⟪x 2, w⟫ ∨ ⟪x 6, w⟫ < ⟪x 4, w⟫)
    (hp : ⟪x 2, w⟫ < ⟪x 0, w⟫ ∨ ⟪x 4, w⟫ < ⟪x 0, w⟫ ∨ ⟪x 2, w⟫ < ⟪x 6, w⟫ ∨ ⟪x 4, w⟫ < ⟪x 6, w⟫) :
    Gen.LexAny F := by
  refine WC.lexAny_of_cellAt_robUni le_rfl F c0264_inj cyc0264 hw (robUni_four_of_mixed ?_ ?_)
  · rcases hn with h | h | h | h
    · exact ⟨(0, 1), by decide, by simp only [c0264, Matrix.cons_val]; linarith⟩
    · exact ⟨(0, 3), by decide, by simp only [c0264, Matrix.cons_val]; linarith⟩
    · exact ⟨(2, 1), by decide, by simp only [c0264, Matrix.cons_val]; linarith⟩
    · exact ⟨(2, 3), by decide, by simp only [c0264, Matrix.cons_val]; linarith⟩
  · rcases hp with h | h | h | h
    · exact ⟨(0, 1), by decide, by simp only [c0264, Matrix.cons_val]; linarith⟩
    · exact ⟨(0, 3), by decide, by simp only [c0264, Matrix.cons_val]; linarith⟩
    · exact ⟨(2, 1), by decide, by simp only [c0264, Matrix.cons_val]; linarith⟩
    · exact ⟨(2, 3), by decide, by simp only [c0264, Matrix.cons_val]; linarith⟩

/-- **CW2, cell `0.5.2.6`** (wall `126`, `ω4 < cc`, `0345`, `235`, `346` front at `v0`): the rim depths at `v0` are
not a crown (one comparison breaking `{z0, z2} ≥ {z5, z6}`, one breaking `{z5, z6} ≥ {z0, z2}`) => `Gen.LexAny`. -/
theorem cellW2_0526_lexAny (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) {cc : ℝ} (hw4 : omega4 x < cc)
    (h3 : 0 < ⟪F.N 3, capView x 0 1 cc⟫) (h6 : 0 < ⟪F.N 6, capView x 0 1 cc⟫)
    (h8 : 0 < ⟪F.N 8, capView x 0 1 cc⟫)
    (hn : ⟪x 0 - x 1, capView x 0 1 cc⟫ < ⟪x 5 - x 1, capView x 0 1 cc⟫ ∨
      ⟪x 0 - x 1, capView x 0 1 cc⟫ < ⟪x 6 - x 1, capView x 0 1 cc⟫ ∨
      ⟪x 2 - x 1, capView x 0 1 cc⟫ < ⟪x 5 - x 1, capView x 0 1 cc⟫ ∨
      ⟪x 2 - x 1, capView x 0 1 cc⟫ < ⟪x 6 - x 1, capView x 0 1 cc⟫)
    (hp : ⟪x 5 - x 1, capView x 0 1 cc⟫ < ⟪x 0 - x 1, capView x 0 1 cc⟫ ∨
      ⟪x 6 - x 1, capView x 0 1 cc⟫ < ⟪x 0 - x 1, capView x 0 1 cc⟫ ∨
      ⟪x 5 - x 1, capView x 0 1 cc⟫ < ⟪x 2 - x 1, capView x 0 1 cc⟫ ∨
      ⟪x 6 - x 1, capView x 0 1 cc⟫ < ⟪x 2 - x 1, capView x 0 1 cc⟫) :
    Gen.LexAny F := by
  have hcc : 0 < cc := lt_trans hC.2.1 hw4
  have h45 := omega45_gt_one hC
  have hw5 : 1 < omega5 x * cc := by nlinarith [hC.2.2.1]
  refine wall126_q4_lexAny F WallFoot.c0526_inj WallFoot.cyc0526 (cc := cc) ?_ ?_ ?_ ?_
  · intro t ht
    simp only [WallFoot.U0526, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact h3
    · rw [cap_f4]; nlinarith [F.neg 4 1 (by decide)]
    · exact h6
    · rw [cap_f7]; nlinarith [F.neg 7 1 (by decide)]
    · exact h8
  · intro t ht h5
    simp only [WallFoot.Dn0526, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · rw [cap_f0]; exact mul_neg_of_pos_of_neg hcc (F.neg 0 6 (by decide))
    · rw [cap_f1]; linarith [F.neg 1 2 (by decide)]
    · rw [cap_f2]; nlinarith [F.neg 2 1 (by decide)]
    · exact absurd rfl h5
  · simp only [inner_sub_left] at hn
    rcases hn with h | h | h | h
    · exact ⟨(0, 1), by decide, by simp only [WallFoot.c0526, Matrix.cons_val, inner_sub_left]; linarith⟩
    · exact ⟨(0, 3), by decide, by simp only [WallFoot.c0526, Matrix.cons_val, inner_sub_left]; linarith⟩
    · exact ⟨(2, 1), by decide, by simp only [WallFoot.c0526, Matrix.cons_val, inner_sub_left]; linarith⟩
    · exact ⟨(2, 3), by decide, by simp only [WallFoot.c0526, Matrix.cons_val, inner_sub_left]; linarith⟩
  · simp only [inner_sub_left] at hp
    rcases hp with h | h | h | h
    · exact ⟨(0, 1), by decide, by simp only [WallFoot.c0526, Matrix.cons_val, inner_sub_left]; linarith⟩
    · exact ⟨(0, 3), by decide, by simp only [WallFoot.c0526, Matrix.cons_val, inner_sub_left]; linarith⟩
    · exact ⟨(2, 1), by decide, by simp only [WallFoot.c0526, Matrix.cons_val, inner_sub_left]; linarith⟩
    · exact ⟨(2, 3), by decide, by simp only [WallFoot.c0526, Matrix.cons_val, inner_sub_left]; linarith⟩

/-- **CW2, cell `0.2.6.4`** (wall `126`, `0 < cc < 1/ω5`, `0345`, `235`, `346` front at `v0`): the rim depths at
`v0` are not a crown (one comparison breaking `{z0, z6} ≥ {z2, z4}`, one breaking `{z2, z4} ≥ {z0, z6}`) =>
`Gen.LexAny`. -/
theorem cellW2_0264_lexAny (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) {cc : ℝ} (hcc : 0 < cc)
    (hw5 : cc < 1 / omega5 x)
    (h3 : 0 < ⟪F.N 3, capView x 0 1 cc⟫) (h6 : 0 < ⟪F.N 6, capView x 0 1 cc⟫)
    (h8 : 0 < ⟪F.N 8, capView x 0 1 cc⟫)
    (hn : ⟪x 0 - x 1, capView x 0 1 cc⟫ < ⟪x 2 - x 1, capView x 0 1 cc⟫ ∨
      ⟪x 0 - x 1, capView x 0 1 cc⟫ < ⟪x 4 - x 1, capView x 0 1 cc⟫ ∨
      ⟪x 6 - x 1, capView x 0 1 cc⟫ < ⟪x 2 - x 1, capView x 0 1 cc⟫ ∨
      ⟪x 6 - x 1, capView x 0 1 cc⟫ < ⟪x 4 - x 1, capView x 0 1 cc⟫)
    (hp : ⟪x 2 - x 1, capView x 0 1 cc⟫ < ⟪x 0 - x 1, capView x 0 1 cc⟫ ∨
      ⟪x 4 - x 1, capView x 0 1 cc⟫ < ⟪x 0 - x 1, capView x 0 1 cc⟫ ∨
      ⟪x 2 - x 1, capView x 0 1 cc⟫ < ⟪x 6 - x 1, capView x 0 1 cc⟫ ∨
      ⟪x 4 - x 1, capView x 0 1 cc⟫ < ⟪x 6 - x 1, capView x 0 1 cc⟫) :
    Gen.LexAny F := by
  have h5 := hC.2.2.1
  have h45 := omega45_gt_one hC
  have hw5' : omega5 x * cc < 1 := by
    have := mul_lt_mul_of_pos_left hw5 h5
    rwa [mul_one_div_cancel h5.ne'] at this
  have hw4 : cc < omega4 x := by nlinarith [hC.2.1]
  refine wall126_q4_lexAny F c0264_inj cyc0264 (cc := cc) ?_ ?_ ?_ ?_
  · intro t ht
    simp only [U0264, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · rw [cap_f2]; nlinarith [F.neg 2 1 (by decide)]
    · exact h3
    · exact h6
    · rw [cap_f7]; nlinarith [F.neg 7 1 (by decide)]
    · exact h8
  · intro t ht h5'
    simp only [Dn0264, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · rw [cap_f0]; exact mul_neg_of_pos_of_neg hcc (F.neg 0 6 (by decide))
    · rw [cap_f1]; linarith [F.neg 1 2 (by decide)]
    · rw [cap_f4]; nlinarith [F.neg 4 1 (by decide)]
    · exact absurd rfl h5'
  · simp only [inner_sub_left] at hn
    rcases hn with h | h | h | h
    · exact ⟨(0, 1), by decide, by simp only [c0264, Matrix.cons_val, inner_sub_left]; linarith⟩
    · exact ⟨(0, 3), by decide, by simp only [c0264, Matrix.cons_val, inner_sub_left]; linarith⟩
    · exact ⟨(2, 1), by decide, by simp only [c0264, Matrix.cons_val, inner_sub_left]; linarith⟩
    · exact ⟨(2, 3), by decide, by simp only [c0264, Matrix.cons_val, inner_sub_left]; linarith⟩
  · simp only [inner_sub_left] at hp
    rcases hp with h | h | h | h
    · exact ⟨(0, 1), by decide, by simp only [c0264, Matrix.cons_val, inner_sub_left]; linarith⟩
    · exact ⟨(0, 3), by decide, by simp only [c0264, Matrix.cons_val, inner_sub_left]; linarith⟩
    · exact ⟨(2, 1), by decide, by simp only [c0264, Matrix.cons_val, inner_sub_left]; linarith⟩
    · exact ⟨(2, 3), by decide, by simp only [c0264, Matrix.cons_val, inner_sub_left]; linarith⟩

/-- **Lemma F4 on wall `126`, above the window** (cell `0.5.2.6`): `ω4 < cc < r26`, `z0 < z6`, `0345`, `235`, `346`
front at `v0` => `Gen.LexAny` (`z0 < z6` breaks `{z0, z2} ≥ {z5, z6}`, `z6 < z2` (`cc < r26`) the other crown).
Referee: `z0 < z6` is needed (it is not implied by `z0 ≤ 0`; Fable's form: `z6 > 0`). -/
theorem wallFoot126_above (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hbc : ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0)
    {cc : ℝ} (hw4 : omega4 x < cc) (hr : cc < r26 x)
    (h3 : 0 < ⟪F.N 3, capView x 0 1 cc⟫) (h6 : 0 < ⟪F.N 6, capView x 0 1 cc⟫)
    (h8 : 0 < ⟪F.N 8, capView x 0 1 cc⟫)
    (hz : ⟪x 0 - x 1, capView x 0 1 cc⟫ < ⟪x 6 - x 1, capView x 0 1 cc⟫) :
    Gen.LexAny F := by
  obtain ⟨hD, he⟩ := wall126_z2_sub_z6 F hbc cc
  refine cellW2_0526_lexAny F hC hw4 h3 h6 h8 (Or.inr (Or.inl hz)) (Or.inr (Or.inr (Or.inr ?_)))
  nlinarith [mul_pos hD (sub_pos.2 hr)]

/-- **Lemma F4 on wall `126`, below the window** (cell `0.2.6.4`): `r26 < cc < 1/ω5`, `z0 < z2`, `0345`, `235`,
`346` front at `v0` => `Gen.LexAny` (`z0 < z2` breaks `{z0, z6} ≥ {z2, z4}`, `z2 < z6` (`cc > r26`) the other). -/
theorem wallFoot126_below (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hbc : ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0)
    {cc : ℝ} (hr : r26 x < cc) (hw5 : cc < 1 / omega5 x)
    (h3 : 0 < ⟪F.N 3, capView x 0 1 cc⟫) (h6 : 0 < ⟪F.N 6, capView x 0 1 cc⟫)
    (h8 : 0 < ⟪F.N 8, capView x 0 1 cc⟫)
    (hz : ⟪x 0 - x 1, capView x 0 1 cc⟫ < ⟪x 2 - x 1, capView x 0 1 cc⟫) :
    Gen.LexAny F := by
  obtain ⟨hD, he⟩ := wall126_z2_sub_z6 F hbc cc
  refine cellW2_0264_lexAny F hC (lt_trans (r26_pos F hbc) hr) hw5 h3 h6 h8 (Or.inl hz)
    (Or.inr (Or.inr (Or.inl ?_)))
  nlinarith [mul_neg_of_pos_of_neg hD (sub_neg.2 hr)]

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

/-- Eventually in `𝓝 cc0` from a strict inequality at `cc0` along the base views of the `126` wall. -/
private theorem ev_cc {y z : ℝ³} {cc0 : ℝ} (h : ⟪y, capView x 0 1 cc0⟫ < ⟪z, capView x 0 1 cc0⟫) :
    ∀ᶠ cc : ℝ in 𝓝 cc0, ⟪y, capView x 0 1 cc⟫ < ⟪z, capView x 0 1 cc⟫ := by
  have hc : Continuous fun cc : ℝ => ⟪z, capView x 0 1 cc⟫ - ⟪y, capView x 0 1 cc⟫ := by
    simp only [inner_v0]; fun_prop
  exact ((hc.tendsto cc0).eventually (lt_mem_nhds (sub_pos.2 h))).mono fun _ h => sub_pos.1 h

private theorem ev_cc_pos {y : ℝ³} {cc0 : ℝ} (h : 0 < ⟪y, capView x 0 1 cc0⟫) :
    ∀ᶠ cc : ℝ in 𝓝 cc0, 0 < ⟪y, capView x 0 1 cc⟫ := by
  have hc : Continuous fun cc : ℝ => ⟪y, capView x 0 1 cc⟫ := by simp only [inner_v0]; fun_prop
  exact (hc.tendsto cc0).eventually (lt_mem_nhds h)

/-- A side of `cc0` on which `(cc - cc0) s > 0`, for `s ≠ 0`. -/
private theorem exists_side {P : ℝ → Prop} {cc0 s : ℝ} (hP : ∀ᶠ cc : ℝ in 𝓝 cc0, P cc) (hs : s ≠ 0) :
    ∃ cc, P cc ∧ 0 < (cc - cc0) * s := by
  rcases lt_or_gt_of_ne hs with hs | hs
  · obtain ⟨cc, h1, h2⟩ := ((hP.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : ∀ᶠ cc in 𝓝[<] cc0, cc ∈ Set.Iio cc0)).exists
    exact ⟨cc, h1, mul_pos_of_neg_of_neg (sub_neg.2 h2) hs⟩
  · obtain ⟨cc, h1, h2⟩ := ((hP.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : ∀ᶠ cc in 𝓝[>] cc0, cc ∈ Set.Ioi cc0)).exists
    exact ⟨cc, h1, mul_pos (sub_pos.2 h2) hs⟩

/-- **WF2, tie form** (window foot on wall `126`; no metric hypothesis, only `ω5 > 0`): at a view
`v0 = capView x 0 1 cc0` in the window `1/ω5 < cc0 < ω4` with `0345`, `235`, `346` front and the axis tie
`z2 = z6 (= k)`, if `z4 < k` or `z5 < k`, and `z0 < z4` or `z0 < z5`, then `Gen.LexAny`.  (Move `cc` to the side of
the tie where the axis vertex next to the low rim neighbour is the lower one, then `wallP_lexAny`.) -/
theorem windowFoot126_lexAny_of_tie (F : S0xFac 9 s0x_S24 x) (h5 : 0 < omega5 x) {cc0 : ℝ}
    (hw5 : 1 / omega5 x < cc0) (hw4 : cc0 < omega4 x)
    (h3 : 0 < ⟪F.N 3, capView x 0 1 cc0⟫) (h6 : 0 < ⟪F.N 6, capView x 0 1 cc0⟫)
    (h8 : 0 < ⟪F.N 8, capView x 0 1 cc0⟫)
    (htie : ⟪x 2 - x 1, capView x 0 1 cc0⟫ = ⟪x 6 - x 1, capView x 0 1 cc0⟫)
    (hk : ⟪x 4 - x 1, capView x 0 1 cc0⟫ < ⟪x 6 - x 1, capView x 0 1 cc0⟫ ∨
      ⟪x 5 - x 1, capView x 0 1 cc0⟫ < ⟪x 2 - x 1, capView x 0 1 cc0⟫)
    (hlow : ⟪x 0 - x 1, capView x 0 1 cc0⟫ < ⟪x 4 - x 1, capView x 0 1 cc0⟫ ∨
      ⟪x 0 - x 1, capView x 0 1 cc0⟫ < ⟪x 5 - x 1, capView x 0 1 cc0⟫) :
    Gen.LexAny F := by
  set D : ℝ := ⟪x 6 - x 2, x 6 - x 1⟫ with hDdef
  -- `z6 - z2 = (cc - cc0) D` along the base line
  have hlin : ∀ cc : ℝ, ⟪x 6 - x 1, capView x 0 1 cc⟫ - ⟪x 2 - x 1, capView x 0 1 cc⟫ = (cc - cc0) * D := by
    intro cc
    have e : ∀ c : ℝ, ⟪x 6 - x 1, capView x 0 1 c⟫ - ⟪x 2 - x 1, capView x 0 1 c⟫ =
        ⟪x 6 - x 2, x 2 - x 1⟫ + c * D := fun c => by
      rw [← inner_sub_left, show x 6 - x 1 - (x 2 - x 1) = x 6 - x 2 by abel, inner_v0]
    have h0 := e cc0
    rw [htie, sub_self] at h0
    rw [e cc]; linear_combination -h0
  -- the slope cannot vanish: otherwise `x 6 - x 2` is orthogonal to `e_b` and `e_c`, so `x 6 = x 2`
  have hD : D ≠ 0 := by
    intro hD0
    have h0 : ⟪x 6 - x 2, x 2 - x 1⟫ = 0 := by
      have := hlin cc0
      rw [sub_self, zero_mul, ← inner_sub_left, show x 6 - x 1 - (x 2 - x 1) = x 6 - x 2 by abel, inner_v0,
        ← hDdef, hD0, mul_zero, add_zero] at this
      exact this
    have hself : ⟪x 6 - x 2, x 6 - x 2⟫ = 0 := by
      have hs : ⟪x 6 - x 2, (x 6 - x 1) - (x 2 - x 1)⟫ = D - ⟪x 6 - x 2, x 2 - x 1⟫ := by
        rw [inner_sub_right]
      rw [show (x 6 - x 1) - (x 2 - x 1) = x 6 - x 2 by abel] at hs
      rw [hs, hD0, h0, sub_zero]
    have h62 : x 6 - x 2 = 0 := inner_self_eq_zero.mp hself
    exact absurd (EdgeViewLink.inj_of_fac24 F (sub_eq_zero.mp h62)) (by decide)
  have hwin : ∀ᶠ cc : ℝ in 𝓝 cc0, 1 / omega5 x < cc ∧ cc < omega4 x ∧
      0 < ⟪F.N 3, capView x 0 1 cc⟫ ∧ 0 < ⟪F.N 6, capView x 0 1 cc⟫ ∧ 0 < ⟪F.N 8, capView x 0 1 cc⟫ ∧
      (⟪x 0 - x 1, capView x 0 1 cc⟫ < ⟪x 4 - x 1, capView x 0 1 cc⟫ ∨
        ⟪x 0 - x 1, capView x 0 1 cc⟫ < ⟪x 5 - x 1, capView x 0 1 cc⟫) := by
    refine (eventually_gt_nhds hw5).and ((eventually_lt_nhds hw4).and ((ev_cc_pos h3).and
      ((ev_cc_pos h6).and ((ev_cc_pos h8).and ?_))))
    rcases hlow with l | l
    · exact (ev_cc l).mono fun _ h => Or.inl h
    · exact (ev_cc l).mono fun _ h => Or.inr h
  rcases hk with hk | hk
  · -- below the foot: `z6 < z2`, then `z4 < z6 < z2`
    obtain ⟨cc, ⟨⟨hw5', hw4', h3', h6', h8', hl'⟩, h4'⟩, hs⟩ :=
      exists_side ((hwin.and (ev_cc hk))) (neg_ne_zero.2 hD)
    refine wallP_lexAny F h5 hw5' hw4' h3' h6' h8' (Or.inl ⟨h4', ?_⟩) hl'
    have := hlin cc; nlinarith
  · -- above the foot: `z2 < z6`, then `z5 < z2 < z6`
    obtain ⟨cc, ⟨⟨hw5', hw4', h3', h6', h8', hl'⟩, h5'⟩, hs⟩ := exists_side ((hwin.and (ev_cc hk))) hD
    refine wallP_lexAny F h5 hw5' hw4' h3' h6' h8' (Or.inr ⟨h5', ?_⟩) hl'
    have := hlin cc; nlinarith

/-- **WF2** (TRISTAR-PLAN L3; at the foot `w26 = capView x 0 1 r26`, `G_bc ≤ 0`, `ω5 > 0`): `1/ω5 < r26 < ω4`,
`0345`, `235`, `346` front at `w26`, `z4 < k` or `z5 < k` (`k = z2 = z6` there), and `z0 < max(z4, z5)` =>
`Gen.LexAny`. -/
theorem windowFoot126_lexAny (F : S0xFac 9 s0x_S24 x) (h5 : 0 < omega5 x)
    (hbc : ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0) (hw5 : 1 / omega5 x < r26 x) (hw4 : r26 x < omega4 x)
    (h3 : 0 < ⟪F.N 3, capView x 0 1 (r26 x)⟫) (h6 : 0 < ⟪F.N 6, capView x 0 1 (r26 x)⟫)
    (h8 : 0 < ⟪F.N 8, capView x 0 1 (r26 x)⟫)
    (hk : ⟪x 4 - x 1, capView x 0 1 (r26 x)⟫ < ⟪x 6 - x 1, capView x 0 1 (r26 x)⟫ ∨
      ⟪x 5 - x 1, capView x 0 1 (r26 x)⟫ < ⟪x 2 - x 1, capView x 0 1 (r26 x)⟫)
    (hlow : ⟪x 0 - x 1, capView x 0 1 (r26 x)⟫ < ⟪x 4 - x 1, capView x 0 1 (r26 x)⟫ ∨
      ⟪x 0 - x 1, capView x 0 1 (r26 x)⟫ < ⟪x 5 - x 1, capView x 0 1 (r26 x)⟫) :
    Gen.LexAny F := by
  have htie : ⟪x 2 - x 1, capView x 0 1 (r26 x)⟫ = ⟪x 6 - x 1, capView x 0 1 (r26 x)⟫ := by
    have := (wall126_z2_sub_z6 F hbc (r26 x)).2; rw [sub_self, mul_zero] at this; linarith
  exact windowFoot126_lexAny_of_tie F h5 hw5 hw4 h3 h6 h8 htie hk hlow

/-! ## L4 = WF0: the window foot on walls `016` / `012` (cell `C` = `w_C`, rim `0.5.2.3.6`) -/

/-- **`w_C` certificate** (`cellC`, rim `0.5.2.3.6`; any open-cell view `w`, `z = ⟪x ·, w⟫`): the axis pair `6, 0`
ordered away from the lower axis vertex's other rim neighbour (`z3 < z6 < z0` or `z5 < z0 < z6`) and the low vertex
`2` below `z3` or `z5` => `Gen.LexAny`. -/
theorem cellAtC_lexAny (F : S0xFac 9 s0x_S24 x) {w : ℝ³} (hw : CellAt F Cell.cellC.U (univ \ Cell.cellC.U) w)
    (hax : (⟪x 3, w⟫ < ⟪x 6, w⟫ ∧ ⟪x 6, w⟫ < ⟪x 0, w⟫) ∨ (⟪x 5, w⟫ < ⟪x 0, w⟫ ∧ ⟪x 0, w⟫ < ⟪x 6, w⟫))
    (hlow : ⟪x 2, w⟫ < ⟪x 3, w⟫ ∨ ⟪x 2, w⟫ < ⟪x 5, w⟫) :
    Gen.LexAny F :=
  Cell.lexAny_of_cellRob F Cell.cellC hw
    (robUni_of_rotate (z := fun i => ⟪x (TwoCone.wcRim i), w⟫) 2 (robUni_window5 hax hlow))

/-- **Wall `016`, `w_C`** (window `1/ω5 < cc < ω3`, `0345`, `235`, `346` front at `w0 = capView x 1 0 cc`; only
`ω5 > 0` of `CbarIn`): the conditions of `cellAtC_lexAny`, strict at `w0`, give `Gen.LexAny`. -/
theorem wallC_lexAny (F : S0xFac 9 s0x_S24 x) (h5 : 0 < omega5 x) {cc : ℝ} (hw5 : 1 / omega5 x < cc)
    (hw3 : cc < omega3 x)
    (h3 : 0 < ⟪F.N 3, capView x 1 0 cc⟫) (h6 : 0 < ⟪F.N 6, capView x 1 0 cc⟫)
    (h8 : 0 < ⟪F.N 8, capView x 1 0 cc⟫)
    (hax : (⟪x 3 - x 1, capView x 1 0 cc⟫ < ⟪x 6 - x 1, capView x 1 0 cc⟫ ∧
        ⟪x 6 - x 1, capView x 1 0 cc⟫ < ⟪x 0 - x 1, capView x 1 0 cc⟫) ∨
      (⟪x 5 - x 1, capView x 1 0 cc⟫ < ⟪x 0 - x 1, capView x 1 0 cc⟫ ∧
        ⟪x 0 - x 1, capView x 1 0 cc⟫ < ⟪x 6 - x 1, capView x 1 0 cc⟫))
    (hlow : ⟪x 2 - x 1, capView x 1 0 cc⟫ < ⟪x 3 - x 1, capView x 1 0 cc⟫ ∨
      ⟪x 2 - x 1, capView x 1 0 cc⟫ < ⟪x 5 - x 1, capView x 1 0 cc⟫) :
    Gen.LexAny F := by
  have hcc : 0 < cc := lt_trans (one_div_pos.mpr h5) hw5
  have hw5' : 1 < cc * omega5 x := by
    have := mul_lt_mul_of_pos_right hw5 h5
    rwa [one_div_mul_cancel h5.ne'] at this
  have hcell := WallFoot.wall_cellAt_eventually F (U := {3, 4, 6, 8}) (Dn := {0, 1, 2, 5, 7}) (cc := cc)
    (fun t ht => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · exact h3
      · rw [WallFoot.wall_f4]; nlinarith [F.neg 4 1 (by decide)]
      · exact h6
      · exact h8)
    (fun t ht h1 => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl
      · rw [WallFoot.wall_f0]; exact mul_neg_of_pos_of_neg hcc (F.neg 0 6 (by decide))
      · exact absurd rfl h1
      · rw [WallFoot.wall_f2]; nlinarith [F.neg 2 1 (by decide)]
      · rw [WallFoot.wall_f5]; exact F.neg 5 0 (by decide)
      · rw [WallFoot.wall_f7]; nlinarith [F.neg 7 1 (by decide)])
  have ev : ∀ {u v : Fin 7}, ⟪x u - x 1, capView x 1 0 cc⟫ < ⟪x v - x 1, capView x 1 0 cc⟫ →
      ∀ᶠ η : ℝ in 𝓝[>] 0, ⟪x u, capView x 1 η cc⟫ < ⟪x v, capView x 1 η cc⟫ := by
    intro u v h
    have h' : 0 < ⟪x v - x u, capView x 1 0 cc⟫ := by
      have e : x v - x u = (x v - x 1) - (x u - x 1) := by abel
      rw [e, inner_sub_left]; linarith
    refine (ev_lin (B := ⟪x v - x u, x 2 - x 1⟫) h').mono fun η hη => ?_
    rw [← WallFoot.inner_wall, inner_sub_left] at hη; linarith
  have hax' : ∀ᶠ η : ℝ in 𝓝[>] 0,
      (⟪x 3, capView x 1 η cc⟫ < ⟪x 6, capView x 1 η cc⟫ ∧ ⟪x 6, capView x 1 η cc⟫ < ⟪x 0, capView x 1 η cc⟫) ∨
      (⟪x 5, capView x 1 η cc⟫ < ⟪x 0, capView x 1 η cc⟫ ∧ ⟪x 0, capView x 1 η cc⟫ < ⟪x 6, capView x 1 η cc⟫) := by
    rcases hax with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · exact ((ev a1).and (ev a2)).mono fun _ h => Or.inl h
    · exact ((ev a1).and (ev a2)).mono fun _ h => Or.inr h
  have hlow' : ∀ᶠ η : ℝ in 𝓝[>] 0,
      ⟪x 2, capView x 1 η cc⟫ < ⟪x 3, capView x 1 η cc⟫ ∨ ⟪x 2, capView x 1 η cc⟫ < ⟪x 5, capView x 1 η cc⟫ := by
    rcases hlow with l | l
    · exact (ev l).mono fun _ h => Or.inl h
    · exact (ev l).mono fun _ h => Or.inr h
  obtain ⟨η, hc, ha, hl⟩ := (hcell.and (hax'.and hlow')).exists
  have e : (univ \ Cell.cellC.U : Finset (Fin 9)) = {0, 1, 2, 5, 7} := by decide
  exact cellAtC_lexAny F (by rw [e]; exact hc) ha hl

private theorem ev_cc016 {y z : ℝ³} {cc0 : ℝ} (h : ⟪y, capView x 1 0 cc0⟫ < ⟪z, capView x 1 0 cc0⟫) :
    ∀ᶠ cc : ℝ in 𝓝 cc0, ⟪y, capView x 1 0 cc⟫ < ⟪z, capView x 1 0 cc⟫ := by
  have hc : Continuous fun cc : ℝ => ⟪z, capView x 1 0 cc⟫ - ⟪y, capView x 1 0 cc⟫ := by
    unfold capView; fun_prop
  exact ((hc.tendsto cc0).eventually (lt_mem_nhds (sub_pos.2 h))).mono fun _ h => sub_pos.1 h

private theorem ev_cc016_pos {y : ℝ³} {cc0 : ℝ} (h : 0 < ⟪y, capView x 1 0 cc0⟫) :
    ∀ᶠ cc : ℝ in 𝓝 cc0, 0 < ⟪y, capView x 1 0 cc⟫ := by
  have hc : Continuous fun cc : ℝ => ⟪y, capView x 1 0 cc⟫ := by unfold capView; fun_prop
  exact (hc.tendsto cc0).eventually (lt_mem_nhds h)

/-- **WF0, tie form** (window foot on wall `016`; no metric hypothesis, only `ω5 > 0`): at `w0 = capView x 1 0 cc0`
in the window `1/ω5 < cc0 < ω3` with `0345`, `235`, `346` front and the axis tie `z0 = z6 (= k)`, if `z3 < k` or
`z5 < k`, and `z2 < z3` or `z2 < z5`, then `Gen.LexAny`.  Generalizes `WC.wc_r60_lexAny` (FN1: `z2 < z5 < k < z3`). -/
theorem windowFoot016_lexAny_of_tie (F : S0xFac 9 s0x_S24 x) (h5 : 0 < omega5 x) {cc0 : ℝ}
    (hw5 : 1 / omega5 x < cc0) (hw3 : cc0 < omega3 x)
    (h3 : 0 < ⟪F.N 3, capView x 1 0 cc0⟫) (h6 : 0 < ⟪F.N 6, capView x 1 0 cc0⟫)
    (h8 : 0 < ⟪F.N 8, capView x 1 0 cc0⟫)
    (htie : ⟪x 0 - x 1, capView x 1 0 cc0⟫ = ⟪x 6 - x 1, capView x 1 0 cc0⟫)
    (hk : ⟪x 3 - x 1, capView x 1 0 cc0⟫ < ⟪x 6 - x 1, capView x 1 0 cc0⟫ ∨
      ⟪x 5 - x 1, capView x 1 0 cc0⟫ < ⟪x 0 - x 1, capView x 1 0 cc0⟫)
    (hlow : ⟪x 2 - x 1, capView x 1 0 cc0⟫ < ⟪x 3 - x 1, capView x 1 0 cc0⟫ ∨
      ⟪x 2 - x 1, capView x 1 0 cc0⟫ < ⟪x 5 - x 1, capView x 1 0 cc0⟫) :
    Gen.LexAny F := by
  set D : ℝ := ⟪x 6 - x 0, x 6 - x 1⟫ with hDdef
  have e : ∀ c : ℝ, ⟪x 6 - x 1, capView x 1 0 c⟫ - ⟪x 0 - x 1, capView x 1 0 c⟫ =
      ⟪x 6 - x 0, x 0 - x 1⟫ + c * D := fun c => by
    rw [← inner_sub_left, show x 6 - x 1 - (x 0 - x 1) = x 6 - x 0 by abel]
    simp only [capView, inner_add_right, real_inner_smul_right, zero_smul, add_zero, one_smul]; ring
  have h0 : ⟪x 6 - x 0, x 0 - x 1⟫ + cc0 * D = 0 := by rw [← e cc0, htie, sub_self]
  have hlin : ∀ cc : ℝ, ⟪x 6 - x 1, capView x 1 0 cc⟫ - ⟪x 0 - x 1, capView x 1 0 cc⟫ = (cc - cc0) * D := by
    intro cc; rw [e cc]; linear_combination h0
  have hD : D ≠ 0 := by
    intro hD0
    have h0' : ⟪x 6 - x 0, x 0 - x 1⟫ = 0 := by rw [hD0, mul_zero, add_zero] at h0; exact h0
    have hself : ⟪x 6 - x 0, x 6 - x 0⟫ = 0 := by
      have hs : ⟪x 6 - x 0, (x 6 - x 1) - (x 0 - x 1)⟫ = D - ⟪x 6 - x 0, x 0 - x 1⟫ := by
        rw [inner_sub_right]
      rw [show (x 6 - x 1) - (x 0 - x 1) = x 6 - x 0 by abel] at hs
      rw [hs, hD0, h0', sub_zero]
    have h60 : x 6 - x 0 = 0 := inner_self_eq_zero.mp hself
    exact absurd (EdgeViewLink.inj_of_fac24 F (sub_eq_zero.mp h60)) (by decide)
  have hwin : ∀ᶠ cc : ℝ in 𝓝 cc0, 1 / omega5 x < cc ∧ cc < omega3 x ∧
      0 < ⟪F.N 3, capView x 1 0 cc⟫ ∧ 0 < ⟪F.N 6, capView x 1 0 cc⟫ ∧ 0 < ⟪F.N 8, capView x 1 0 cc⟫ ∧
      (⟪x 2 - x 1, capView x 1 0 cc⟫ < ⟪x 3 - x 1, capView x 1 0 cc⟫ ∨
        ⟪x 2 - x 1, capView x 1 0 cc⟫ < ⟪x 5 - x 1, capView x 1 0 cc⟫) := by
    refine (eventually_gt_nhds hw5).and ((eventually_lt_nhds hw3).and ((ev_cc016_pos h3).and
      ((ev_cc016_pos h6).and ((ev_cc016_pos h8).and ?_))))
    rcases hlow with l | l
    · exact (ev_cc016 l).mono fun _ h => Or.inl h
    · exact (ev_cc016 l).mono fun _ h => Or.inr h
  rcases hk with hk | hk
  · -- below the foot: `z6 < z0`, then `z3 < z6 < z0`
    obtain ⟨cc, ⟨⟨hw5', hw3', h3', h6', h8', hl'⟩, h4'⟩, hs⟩ :=
      exists_side ((hwin.and (ev_cc016 hk))) (neg_ne_zero.2 hD)
    refine wallC_lexAny F h5 hw5' hw3' h3' h6' h8' (Or.inl ⟨h4', ?_⟩) hl'
    have := hlin cc; nlinarith
  · -- above the foot: `z0 < z6`, then `z5 < z0 < z6`
    obtain ⟨cc, ⟨⟨hw5', hw3', h3', h6', h8', hl'⟩, h5'⟩, hs⟩ := exists_side ((hwin.and (ev_cc016 hk))) hD
    refine wallC_lexAny F h5 hw5' hw3' h3' h6' h8' (Or.inr ⟨h5', ?_⟩) hl'
    have := hlin cc; nlinarith

/-- **WF0** (TRISTAR-PLAN L4; at the foot `w60 = capView x 1 0 r60`, `G_ac ≤ 0`, `ω5 > 0`): `1/ω5 < r60 < ω3`,
`0345`, `235`, `346` front at `w60`, `z3 < k` or `z5 < k` (`k = z0 = z6` there), and `z2 < max(z3, z5)` =>
`Gen.LexAny`. -/
theorem windowFoot016_lexAny (F : S0xFac 9 s0x_S24 x) (h5 : 0 < omega5 x)
    (hac : ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0) (hw5 : 1 / omega5 x < WallFoot.r60 x) (hw3 : WallFoot.r60 x < omega3 x)
    (h3 : 0 < ⟪F.N 3, capView x 1 0 (WallFoot.r60 x)⟫) (h6 : 0 < ⟪F.N 6, capView x 1 0 (WallFoot.r60 x)⟫)
    (h8 : 0 < ⟪F.N 8, capView x 1 0 (WallFoot.r60 x)⟫)
    (hk : ⟪x 3 - x 1, capView x 1 0 (WallFoot.r60 x)⟫ < ⟪x 6 - x 1, capView x 1 0 (WallFoot.r60 x)⟫ ∨
      ⟪x 5 - x 1, capView x 1 0 (WallFoot.r60 x)⟫ < ⟪x 0 - x 1, capView x 1 0 (WallFoot.r60 x)⟫)
    (hlow : ⟪x 2 - x 1, capView x 1 0 (WallFoot.r60 x)⟫ < ⟪x 3 - x 1, capView x 1 0 (WallFoot.r60 x)⟫ ∨
      ⟪x 2 - x 1, capView x 1 0 (WallFoot.r60 x)⟫ < ⟪x 5 - x 1, capView x 1 0 (WallFoot.r60 x)⟫) :
    Gen.LexAny F := by
  have htie : ⟪x 0 - x 1, capView x 1 0 (WallFoot.r60 x)⟫ = ⟪x 6 - x 1, capView x 1 0 (WallFoot.r60 x)⟫ := by
    have := (WallFoot.wall_z0_sub_z6 F hac (WallFoot.r60 x)).2; rw [sub_self, mul_zero] at this; linarith
  exact windowFoot016_lexAny_of_tie F h5 hw5 hw3 h3 h6 h8 htie hk hlow

/-! ## Region forms (named Props), twins and `HoleLeaf` forms -/

/-- **CW2 above the window** (TRISTAR-PLAN L2, cell `0.5.2.6`): some `cc > ω4` with `0345`, `235`, `346` front at
`v0 = capView x 0 1 cc` and the rim depths there not a crown. -/
def CW2Above (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ cc : ℝ, omega4 x < cc ∧ 0 < ⟪F.N 3, capView x 0 1 cc⟫ ∧ 0 < ⟪F.N 6, capView x 0 1 cc⟫ ∧ 0 < ⟪F.N 8, capView x 0 1 cc⟫ ∧
    (⟪x 0 - x 1, capView x 0 1 cc⟫ < ⟪x 5 - x 1, capView x 0 1 cc⟫ ∨
      ⟪x 0 - x 1, capView x 0 1 cc⟫ < ⟪x 6 - x 1, capView x 0 1 cc⟫ ∨
      ⟪x 2 - x 1, capView x 0 1 cc⟫ < ⟪x 5 - x 1, capView x 0 1 cc⟫ ∨
      ⟪x 2 - x 1, capView x 0 1 cc⟫ < ⟪x 6 - x 1, capView x 0 1 cc⟫) ∧
    (⟪x 5 - x 1, capView x 0 1 cc⟫ < ⟪x 0 - x 1, capView x 0 1 cc⟫ ∨
      ⟪x 6 - x 1, capView x 0 1 cc⟫ < ⟪x 0 - x 1, capView x 0 1 cc⟫ ∨
      ⟪x 5 - x 1, capView x 0 1 cc⟫ < ⟪x 2 - x 1, capView x 0 1 cc⟫ ∨
      ⟪x 6 - x 1, capView x 0 1 cc⟫ < ⟪x 2 - x 1, capView x 0 1 cc⟫)

/-- **CW2 below the window** (TRISTAR-PLAN L2, cell `0.2.6.4`): some `0 < cc < 1/ω5` with `0345`, `235`, `346`
front at `v0` and the rim depths there not a crown. -/
def CW2Below (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ cc : ℝ, 0 < cc ∧ cc < 1 / omega5 x ∧ 0 < ⟪F.N 3, capView x 0 1 cc⟫ ∧ 0 < ⟪F.N 6, capView x 0 1 cc⟫ ∧
    0 < ⟪F.N 8, capView x 0 1 cc⟫ ∧
    (⟪x 0 - x 1, capView x 0 1 cc⟫ < ⟪x 2 - x 1, capView x 0 1 cc⟫ ∨
      ⟪x 0 - x 1, capView x 0 1 cc⟫ < ⟪x 4 - x 1, capView x 0 1 cc⟫ ∨
      ⟪x 6 - x 1, capView x 0 1 cc⟫ < ⟪x 2 - x 1, capView x 0 1 cc⟫ ∨
      ⟪x 6 - x 1, capView x 0 1 cc⟫ < ⟪x 4 - x 1, capView x 0 1 cc⟫) ∧
    (⟪x 2 - x 1, capView x 0 1 cc⟫ < ⟪x 0 - x 1, capView x 0 1 cc⟫ ∨
      ⟪x 4 - x 1, capView x 0 1 cc⟫ < ⟪x 0 - x 1, capView x 0 1 cc⟫ ∨
      ⟪x 2 - x 1, capView x 0 1 cc⟫ < ⟪x 6 - x 1, capView x 0 1 cc⟫ ∨
      ⟪x 4 - x 1, capView x 0 1 cc⟫ < ⟪x 6 - x 1, capView x 0 1 cc⟫)

/-- **WF2** (TRISTAR-PLAN L3) at the foot `w26 = capView x 0 1 r26`: window `1/ω5 < r26 < ω4`, `0345`, `235`, `346`
front, `z4 < k` or `z5 < k` (`k = z2 = z6`), `z0 < max(z4, z5)`. -/
def WF2At (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  1 / omega5 x < r26 x ∧ r26 x < omega4 x ∧ 0 < ⟪F.N 3, capView x 0 1 (r26 x)⟫ ∧
    0 < ⟪F.N 6, capView x 0 1 (r26 x)⟫ ∧ 0 < ⟪F.N 8, capView x 0 1 (r26 x)⟫ ∧
    (⟪x 4 - x 1, capView x 0 1 (r26 x)⟫ < ⟪x 6 - x 1, capView x 0 1 (r26 x)⟫ ∨
      ⟪x 5 - x 1, capView x 0 1 (r26 x)⟫ < ⟪x 2 - x 1, capView x 0 1 (r26 x)⟫) ∧
    (⟪x 0 - x 1, capView x 0 1 (r26 x)⟫ < ⟪x 4 - x 1, capView x 0 1 (r26 x)⟫ ∨
      ⟪x 0 - x 1, capView x 0 1 (r26 x)⟫ < ⟪x 5 - x 1, capView x 0 1 (r26 x)⟫)

/-- **WF0** (TRISTAR-PLAN L4) at the foot `w60 = capView x 1 0 r60` of the `016` wall: window `1/ω5 < r60 < ω3`,
`0345`, `235`, `346` front, `z3 < k` or `z5 < k` (`k = z0 = z6`), `z2 < max(z3, z5)`.  On `x ∘ π_24` it is the
window foot of the `012` wall. -/
def WF0At (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  1 / omega5 x < WallFoot.r60 x ∧ WallFoot.r60 x < omega3 x ∧ 0 < ⟪F.N 3, capView x 1 0 (WallFoot.r60 x)⟫ ∧
    0 < ⟪F.N 6, capView x 1 0 (WallFoot.r60 x)⟫ ∧ 0 < ⟪F.N 8, capView x 1 0 (WallFoot.r60 x)⟫ ∧
    (⟪x 3 - x 1, capView x 1 0 (WallFoot.r60 x)⟫ < ⟪x 6 - x 1, capView x 1 0 (WallFoot.r60 x)⟫ ∨
      ⟪x 5 - x 1, capView x 1 0 (WallFoot.r60 x)⟫ < ⟪x 0 - x 1, capView x 1 0 (WallFoot.r60 x)⟫) ∧
    (⟪x 2 - x 1, capView x 1 0 (WallFoot.r60 x)⟫ < ⟪x 3 - x 1, capView x 1 0 (WallFoot.r60 x)⟫ ∨
      ⟪x 2 - x 1, capView x 1 0 (WallFoot.r60 x)⟫ < ⟪x 5 - x 1, capView x 1 0 (WallFoot.r60 x)⟫)

theorem lexAny_of_cw2Above (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (h : CW2Above x F) : Gen.LexAny F := by
  obtain ⟨cc, hw4, h3, h6, h8, hn, hp⟩ := h
  exact cellW2_0526_lexAny F hC hw4 h3 h6 h8 hn hp

theorem lexAny_of_cw2Below (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (h : CW2Below x F) : Gen.LexAny F := by
  obtain ⟨cc, hcc, hw5, h3, h6, h8, hn, hp⟩ := h
  exact cellW2_0264_lexAny F hC hcc hw5 h3 h6 h8 hn hp

theorem lexAny_of_wf2At (F : S0xFac 9 s0x_S24 x) (h5 : 0 < omega5 x) (hbc : ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0)
    (h : WF2At x F) : Gen.LexAny F := by
  obtain ⟨hw5, hw4, h3, h6, h8, hk, hlow⟩ := h
  exact windowFoot126_lexAny F h5 hbc hw5 hw4 h3 h6 h8 hk hlow

theorem lexAny_of_wf0At (F : S0xFac 9 s0x_S24 x) (h5 : 0 < omega5 x) (hac : ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0)
    (h : WF0At x F) : Gen.LexAny F := by
  obtain ⟨hw5, hw3, h3, h6, h8, hk, hlow⟩ := h
  exact windowFoot016_lexAny F h5 hac hw5 hw3 h3 h6 h8 hk hlow

theorem lexAny_of_cw2Above_twin (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (h : CW2Above (x ∘ Sym.pi24) (Sym.sym24 F)) : Gen.LexAny F :=
  Sym.lexAny_sym F (lexAny_of_cw2Above (Sym.sym24 F) ((Sym.cbarIn_comp_pi24 x).2 hC) h)

theorem lexAny_of_cw2Below_twin (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (h : CW2Below (x ∘ Sym.pi24) (Sym.sym24 F)) : Gen.LexAny F :=
  Sym.lexAny_sym F (lexAny_of_cw2Below (Sym.sym24 F) ((Sym.cbarIn_comp_pi24 x).2 hC) h)

theorem lexAny_of_wf2At_twin (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hO : H24K.SAT.OB1 x)
    (h : WF2At (x ∘ Sym.pi24) (Sym.sym24 F)) : Gen.LexAny F :=
  Sym.lexAny_sym F (lexAny_of_wf2At (Sym.sym24 F) ((Sym.cbarIn_comp_pi24 x).2 hC).2.2.1
    ((A19.ob1_comp_pi24 x).2 hO).2.2 h)

/-- **WF0 on the wall `012`** = WF0 on the `π_24` twin `x ∘ π_24` (whose `016` wall is the `012` wall of `x`). -/
theorem windowFoot012_lexAny (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hO : H24K.SAT.OB1 x)
    (h : WF0At (x ∘ Sym.pi24) (Sym.sym24 F)) : Gen.LexAny F :=
  Sym.lexAny_sym F (lexAny_of_wf0At (Sym.sym24 F) ((Sym.cbarIn_comp_pi24 x).2 hC).2.2.1
    ((A19.ob1_comp_pi24 x).2 hO).2.1 h)

theorem holeLeaf_not_cw2Above {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : ¬ CW2Above x F :=
  fun h => hF.2.2.2.1 (lexAny_of_cw2Above F hF.1 h)

theorem holeLeaf_not_cw2Above_twin {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) :
    ¬ CW2Above (x ∘ Sym.pi24) (Sym.sym24 F) :=
  fun h => hF.2.2.2.1 (lexAny_of_cw2Above_twin F hF.1 h)

theorem holeLeaf_not_cw2Below {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : ¬ CW2Below x F :=
  fun h => hF.2.2.2.1 (lexAny_of_cw2Below F hF.1 h)

theorem holeLeaf_not_cw2Below_twin {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) :
    ¬ CW2Below (x ∘ Sym.pi24) (Sym.sym24 F) :=
  fun h => hF.2.2.2.1 (lexAny_of_cw2Below_twin F hF.1 h)

theorem holeLeaf_not_wf2At {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) (hO : H24K.SAT.OB1 x) :
    ¬ WF2At x F :=
  fun h => hF.2.2.2.1 (lexAny_of_wf2At F hF.1.2.2.1 hO.2.2 h)

theorem holeLeaf_not_wf2At_twin {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) (hO : H24K.SAT.OB1 x) :
    ¬ WF2At (x ∘ Sym.pi24) (Sym.sym24 F) :=
  fun h => hF.2.2.2.1 (lexAny_of_wf2At_twin F hF.1 hO h)

theorem holeLeaf_not_wf0At {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) (hO : H24K.SAT.OB1 x) :
    ¬ WF0At x F :=
  fun h => hF.2.2.2.1 (lexAny_of_wf0At F hF.1.2.2.1 hO.2.1 h)

theorem holeLeaf_not_wf0At_twin {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) (hO : H24K.SAT.OB1 x) :
    ¬ WF0At (x ∘ Sym.pi24) (Sym.sym24 F) :=
  fun h => hF.2.2.2.1 (windowFoot012_lexAny F hF.1 hO h)

end Minimality.T24.WallFoot126
