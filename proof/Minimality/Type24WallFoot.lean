module

public import Minimality.Type24WCOrder
public import Minimality.FrontDiag
public import Minimality.EdgeViewLink
public import Minimality.Type24SAT.K24.CornerOB1

/-!
# Type 24: Lex leaves on the wall line of facet `016` (Lemma F4 and the Seesaw corollary)

Formalizes (and referees) Lemma F4 and Corollary (S1)-(S3) of nopert229 notes/FABLE-TRI-REPLY.md section 1.
Wall line of facet `016`: `capView x 1 η cc = e_a + η e_b + cc e_c` (`e_a = x 0 - x 1`, `e_b = x 2 - x 1`,
`e_c = x 6 - x 1`), `η → 0+`.  Facet `016` vanishes at `η = 0` and is back for `η > 0`; every other facet sign
and every depth comparison that is strict at `η = 0` persists for small `η > 0`.  Depths `z_v = ⟪x v - x 1, w⟫`.

* `wall_cellAt_eventually`: strict facet signs at `w0 = capView x 1 0 cc` (all facets of the cell except `016`)
  give the open cell at `capView x 1 η cc` for all small `η > 0`.
* `wall_q4_lexAny` (generic): any 4-rim cell on the wall line with one strictly negative and one strictly positive
  diagonal form at `w0` ("not a crown") gives `Gen.LexAny`.
* Open-cell certificate `cellAt0526_lexAny` (any view `w` with `CellAt`, depths `⟪x v, w⟫` not a crown).
* The foot `r60 = (g_a - G_ac) / (g_c - G_ac)` of the tie `z0 = z6` on the wall line (`wall_z0_sub_z6`).
* Pruned 11-27 pass 3 (see TOOLBOX-LEAN; the cell framework `Type24Cell.lean` / the wall covers keep the statements):
  `cellAt0236_lexAny`, `cellAt0536_lexAny`, `cell0526_lexAny`, `cell0236_lexAny`, `cell0536_lexAny`,
  Lemma F4 `wallFoot_a` / `_b` / `_c`, the Seesaw `seesaw_S1` / `S2` / `S3` and their `HoleLeaf` forms.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset Filter
open scoped Topology
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.RimCell Minimality.T24.HC

namespace Minimality.T24.WallFoot

variable {x : Fin 7 → ℝ³}

/-! ## The wall line -/

/-- Every linear form along the wall line is affine in `η`. -/
theorem inner_wall (y : ℝ³) (η cc : ℝ) :
    ⟪y, capView x 1 η cc⟫ = ⟪y, capView x 1 0 cc⟫ + η * ⟪y, x 2 - x 1⟫ := by
  simp only [capView, inner_add_right, real_inner_smul_right]; ring

private theorem ev_wall {A B : ℝ} (h : 0 < A) : ∀ᶠ η : ℝ in 𝓝[>] 0, 0 < A + η * B := by
  have hc : Continuous (fun η : ℝ => A + η * B) := by fun_prop
  have ht : Tendsto (fun η : ℝ => A + η * B) (𝓝 0) (𝓝 A) := by
    simpa using hc.tendsto 0
  exact nhdsWithin_le_nhds (ht.eventually (lt_mem_nhds h))

/-- **Wall cell.** Strict facet signs at `w0 = capView x 1 0 cc` for the up facets `U` and for the down facets
`Dn` other than `016` (which vanishes at `w0`) give the open cell `CellAt F U Dn` at `capView x 1 η cc` for all
small `η > 0`. -/
theorem wall_cellAt_eventually (F : S0xFac 9 s0x_S24 x) {U Dn : Finset (Fin 9)} {cc : ℝ}
    (hU : ∀ t ∈ U, 0 < ⟪F.N t, capView x 1 0 cc⟫)
    (hD : ∀ t ∈ Dn, t ≠ 1 → ⟪F.N t, capView x 1 0 cc⟫ < 0) :
    ∀ᶠ η : ℝ in 𝓝[>] 0, CellAt F U Dn (capView x 1 η cc) := by
  have h1 : ∀ η : ℝ, ⟪F.N 1, capView x 1 η cc⟫ = η * F.f 1 (x 2) := by
    intro η
    simp only [capView, inner_add_right, real_inner_smul_right, F.inner_sub,
      F.zero 1 0 (by decide), F.zero 1 1 (by decide), F.zero 1 6 (by decide)]
    ring
  refine (Filter.eventually_all_finset U |>.2 fun t ht => ?_).and
    (Filter.eventually_all_finset Dn |>.2 fun t ht => ?_)
  · exact (ev_wall (B := ⟪F.N t, x 2 - x 1⟫) (hU t ht)).mono fun η h => by rw [inner_wall]; exact h
  · by_cases h : t = 1
    · subst h
      filter_upwards [self_mem_nhdsWithin] with η (hη : 0 < η)
      rw [h1]; exact mul_neg_of_pos_of_neg hη (F.neg 1 2 (by decide))
    · exact (ev_wall (B := -⟪F.N t, x 2 - x 1⟫) (neg_pos.2 (hD t ht h))).mono fun η hη => by
        rw [inner_wall]; linarith

/-- **Generic wall Q4 leaf.** A 4-rim `c` of a cell `(U, Dn)` on the wall line (facet signs at `w0` as in
`wall_cellAt_eventually`) whose diagonal forms take a strictly negative and a strictly positive value at `w0`
(the rim depths are not a crown) gives `Gen.LexAny F`. -/
theorem wall_q4_lexAny (F : S0xFac 9 s0x_S24 x) {c : ZMod 4 → Fin 7} (hc : Function.Injective c)
    {U Dn : Finset (Fin 9)} (hcyc : S0xCycUD s0x_S24 c U Dn) {cc : ℝ}
    (hU : ∀ t ∈ U, 0 < ⟪F.N t, capView x 1 0 cc⟫)
    (hD : ∀ t ∈ Dn, t ≠ 1 → ⟪F.N t, capView x 1 0 cc⟫ < 0)
    (hn : ∃ p ∈ diagPairs, ⟪x (c p.1) - x (c p.2), capView x 1 0 cc⟫ < 0)
    (hp : ∃ p ∈ diagPairs, 0 < ⟪x (c p.1) - x (c p.2), capView x 1 0 cc⟫) :
    Gen.LexAny F := by
  obtain ⟨p, hpm, hpv⟩ := hn
  obtain ⟨q, hqm, hqv⟩ := hp
  have en := ev_wall (B := -⟪x (c p.1) - x (c p.2), x 2 - x 1⟫) (neg_pos.2 hpv)
  have ep := ev_wall (B := ⟪x (c q.1) - x (c q.2), x 2 - x 1⟫) hqv
  obtain ⟨η, hcell, h1, h2⟩ := ((wall_cellAt_eventually F hU hD).and (en.and ep)).exists
  refine WC.lexAny_of_cellAt_robUni le_rfl F hc hcyc hcell (robUni_four_of_mixed ?_ ?_)
  · exact ⟨p, hpm, by rw [← inner_sub_left, inner_wall]; linarith⟩
  · exact ⟨q, hqm, by rw [← inner_sub_left, inner_wall]; linarith⟩

/-! ## Facet values at `w0` -/

theorem wall_f0 (F : S0xFac 9 s0x_S24 x) (cc : ℝ) : ⟪F.N 0, capView x 1 0 cc⟫ = cc * F.f 0 (x 6) := by
  rw [Belt.inner_cap, F.zero 0 0 (by decide), F.zero 0 1 (by decide), F.zero 0 2 (by decide)]; ring

theorem wall_f4 (F : S0xFac 9 s0x_S24 x) (cc : ℝ) :
    ⟪F.N 4, capView x 1 0 cc⟫ = -((1 + cc) * F.f 4 (x 1)) := by
  rw [Belt.inner_cap, F.zero 4 0 (by decide), F.zero 4 6 (by decide)]; ring

theorem wall_f5 (F : S0xFac 9 s0x_S24 x) (cc : ℝ) : ⟪F.N 5, capView x 1 0 cc⟫ = F.f 5 (x 0) := by
  rw [Belt.inner_cap, F.zero 5 1 (by decide), F.zero 5 2 (by decide), F.zero 5 6 (by decide)]; ring

theorem wall_f2 (F : S0xFac 9 s0x_S24 x) (cc : ℝ) :
    ⟪F.N 2, capView x 1 0 cc⟫ = F.f 2 (x 1) * (cc * omega5 x - 1) := by
  have T := M4.type24OfFac F
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have ev := M4.fac_eval F 2 5
  rw [F.zero 2 5 (by decide), F.zero 2 0 (by decide), F.zero 2 2 (by decide)] at ev
  have hw : omega5 x * oblX6 x 5 = oblX0 x 5 + oblX2 x 5 - 1 := by
    unfold omega5; field_simp
  have f2_rel : F.f 2 (x 6) - F.f 2 (x 1) = omega5 x * F.f 2 (x 1) := by
    have : oblX6 x 5 * ((F.f 2 (x 6) - F.f 2 (x 1)) - omega5 x * F.f 2 (x 1)) = 0 := by
      linear_combination -ev - F.f 2 (x 1) * hw
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hc5.ne')
  rw [Belt.inner_cap, F.zero 2 0 (by decide), f2_rel]; ring

theorem wall_f7 (F : S0xFac 9 s0x_S24 x) (cc : ℝ) :
    ⟪F.N 7, capView x 1 0 cc⟫ = F.f 7 (x 1) * (omega3 x - cc) := by
  rw [Belt.inner_cap, Belt.f7_rel F, F.zero 7 2 (by decide), F.zero 7 6 (by decide)]; ring

theorem omega35_gt_one (hC : CbarIn x) : 1 < omega3 x * omega5 x := by
  refine omega_prod_gt_one hC.1 hC.2.2.1 hC.2.1 ?_
  have h := hC.2.2.2
  unfold Delta24 at h
  linarith [show omega3 x * omega5 x * omega4 x = omega3 x * omega4 x * omega5 x by ring]

/-! ## The three 4-rim cells on the wall line -/

/-- Rim `0.5.2.6` (vertices `1, 3, 4` hidden). -/
def c0526 : ZMod 4 → Fin 7 := ![0, 5, 2, 6]
def U0526 : Finset (Fin 9) := {3, 4, 6, 7, 8}
def Dn0526 : Finset (Fin 9) := {0, 1, 2, 5}

theorem c0526_inj : Function.Injective c0526 := by
  intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)

theorem cyc0526 : S0xCycUD s0x_S24 c0526 U0526 Dn0526 := by decide

/-- Rim `0.2.3.6` (vertices `1, 4, 5` hidden). -/
def c0236 : ZMod 4 → Fin 7 := ![0, 2, 3, 6]
def U0236 : Finset (Fin 9) := {2, 3, 4, 6, 8}
def Dn0236 : Finset (Fin 9) := {0, 1, 5, 7}

theorem c0236_inj : Function.Injective c0236 := by
  intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)

theorem cyc0236 : S0xCycUD s0x_S24 c0236 U0236 Dn0236 := by decide

private theorem c0536_inj' : Function.Injective Cell0234.c0536 := by
  intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)

/-! ## Open-cell certificates (any view of the open cell, not only the wall line)

For use as cell certificates: a view `w` in the open cell (`CellAt`) whose rim depths are not a crown gives
`Gen.LexAny`.  No hidden-vertex condition is needed (the Lex leaf only uses the rim cycle `S0xCycUD`). -/

/-- **Cell `0.5.2.6` certificate** (vertices `1, 3, 4` hidden): an open-cell view `w` with one comparison
breaking `{z0, z2} ≥ {z5, z6}` and one breaking `{z5, z6} ≥ {z0, z2}` (`z = ⟪x ·, w⟫`) => `Gen.LexAny`. -/
theorem cellAt0526_lexAny (F : S0xFac 9 s0x_S24 x) {w : ℝ³} (hw : CellAt F U0526 Dn0526 w)
    (hn : ⟪x 0, w⟫ < ⟪x 5, w⟫ ∨ ⟪x 0, w⟫ < ⟪x 6, w⟫ ∨ ⟪x 2, w⟫ < ⟪x 5, w⟫ ∨ ⟪x 2, w⟫ < ⟪x 6, w⟫)
    (hp : ⟪x 5, w⟫ < ⟪x 0, w⟫ ∨ ⟪x 6, w⟫ < ⟪x 0, w⟫ ∨ ⟪x 5, w⟫ < ⟪x 2, w⟫ ∨ ⟪x 6, w⟫ < ⟪x 2, w⟫) :
    Gen.LexAny F := by
  refine WC.lexAny_of_cellAt_robUni le_rfl F c0526_inj cyc0526 hw (robUni_four_of_mixed ?_ ?_)
  · rcases hn with h | h | h | h
    · exact ⟨(0, 1), by decide, by simp only [c0526, Matrix.cons_val]; linarith⟩
    · exact ⟨(0, 3), by decide, by simp only [c0526, Matrix.cons_val]; linarith⟩
    · exact ⟨(2, 1), by decide, by simp only [c0526, Matrix.cons_val]; linarith⟩
    · exact ⟨(2, 3), by decide, by simp only [c0526, Matrix.cons_val]; linarith⟩
  · rcases hp with h | h | h | h
    · exact ⟨(0, 1), by decide, by simp only [c0526, Matrix.cons_val]; linarith⟩
    · exact ⟨(0, 3), by decide, by simp only [c0526, Matrix.cons_val]; linarith⟩
    · exact ⟨(2, 1), by decide, by simp only [c0526, Matrix.cons_val]; linarith⟩
    · exact ⟨(2, 3), by decide, by simp only [c0526, Matrix.cons_val]; linarith⟩

/-! ## Lemma F4 in Fable's form: the foot `r60` -/

/-- The foot of the tie `z0 = z6` on the wall line: `r60 = (g_a - G_ac) / (g_c - G_ac)`. -/
noncomputable def r60 (x : Fin 7 → ℝ³) : ℝ :=
  (⟪x 0 - x 1, x 0 - x 1⟫ - ⟪x 0 - x 1, x 6 - x 1⟫) /
    (⟪x 6 - x 1, x 6 - x 1⟫ - ⟪x 0 - x 1, x 6 - x 1⟫)

/-- `z0 - z6 = (g_c - G_ac) (r60 - cc)` on the wall line, and `g_c - G_ac > 0` when `G_ac ≤ 0`. -/
theorem wall_z0_sub_z6 (F : S0xFac 9 s0x_S24 x) (hac : ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0) (cc : ℝ) :
    0 < ⟪x 6 - x 1, x 6 - x 1⟫ - ⟪x 0 - x 1, x 6 - x 1⟫ ∧
    ⟪x 0 - x 1, capView x 1 0 cc⟫ - ⟪x 6 - x 1, capView x 1 0 cc⟫ =
      (⟪x 6 - x 1, x 6 - x 1⟫ - ⟪x 0 - x 1, x 6 - x 1⟫) * (r60 x - cc) := by
  have h61 : x 6 - x 1 ≠ 0 := sub_ne_zero.mpr fun h => by
    exact absurd (EdgeViewLink.inj_of_fac24 F h) (by decide)
  have hgc : 0 < ⟪x 6 - x 1, x 6 - x 1⟫ := real_inner_self_pos.mpr h61
  have hD : 0 < ⟪x 6 - x 1, x 6 - x 1⟫ - ⟪x 0 - x 1, x 6 - x 1⟫ := by linarith
  refine ⟨hD, ?_⟩
  unfold r60
  rw [mul_sub, mul_div_cancel₀ _ hD.ne']
  simp only [capView, inner_add_right, real_inner_smul_right, zero_smul, add_zero, one_smul,
    real_inner_comm (x 0 - x 1) (x 6 - x 1)]
  ring

/-- On `OB1`, `z2 ≤ 0` at `w0` for `cc ≥ 0`. -/
theorem wall_z2_nonpos (hO : H24K.SAT.OB1 x) {cc : ℝ} (hcc : 0 ≤ cc) :
    ⟪x 2 - x 1, capView x 1 0 cc⟫ ≤ 0 := by
  obtain ⟨hab, -, hbc⟩ := hO
  simp only [capView, inner_add_right, real_inner_smul_right, zero_smul, add_zero, one_smul,
    real_inner_comm (x 0 - x 1) (x 2 - x 1)]
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hcc hbc]

end Minimality.T24.WallFoot
