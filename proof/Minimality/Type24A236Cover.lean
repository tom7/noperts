module

public import Minimality.Type24A236S2
public import Minimality.Type24T2Peak0
public import Minimality.SegmentHelly

/-!
# A236Cover: the `236` wall of `A2` carries a certificate unless the letter condition `A236E` holds

nopert229 notes/A236-MECHANISM.md (failure condition E, Lean sketches L1, L2), notes/FABLE-A236-REPLY.md (S2; S1 is
false, so the `{5,6}` crown is NOT excluded here: it is simply not one of the certified pieces).

The wall: the `236` face of the `T_2` cell `A2` (rim `cA2 = 0.5.3.6.1`), points `p (x₃ - x₂) + q (x₆ - x₂)` with
`p, q > 0` (`a236Pt`; `t2e236 x s = a236Pt x 1 s`).  `z_v = ⟪x v, ·⟫`.  The facets `016, 0345, 046, 346` must be
in front; `012, 025, 126, 235` are automatically behind and `236 = 0` is pushed behind by `x₁ - x₂`.

* `cA2_view_uT2`: every view of the open cell `A2` is a positive multiple of a `T_2` view `uT2 x β γ` (`β, γ > 0`),
  so Facts 1 and 2 hold on the whole open cell, not only on the `uT2` chart.
* (L1, `RobUni`) `cA2_robUni_of_cell`: on the open cell, under `OB1`, the strict letters `A236Rob`
  (`z₀ < z₁`; `z₀ < z₅, z₆`; `z₀ < z₅, z₃`; `z₆ < z₃ < z₅`; `z₃ < z₆ < z₁`: Lemma Z, rule T2C, Lemma P0) give
  `RobUni` on `cA2`.  Wall form `a236_lexAny_of_wallRob`.
* (L2, apex) `cA2_apexCert_of_QD0`: on the open cell, `det24 x · Q > 0` (`Q = det(x₅ - x₃, x₁ - x₆, w)`) and
  `z₀, z₁, z₅ < min(z₃, z₆)`, `z₃ ≠ z₆` give `ApexCert` (`A+6-1^3`: base `6-1`, apex `3`, if `z₃ < z₆`; `A-5-3^6`:
  base `5-3`, apex `6`, if `z₆ < z₃`); the two `h₀` letters come from S2 (`a236_S2`).  No `OB1`, no `CbarIn`.
  With `OB1`, `A236QD0` (`det24 x · Q > 0`, `z₀ < z₃`, `z₀ < z₆`) alone suffices (`a236_cert_of_cellQD0`: if
  `z₀ < z₁` or `z₀ < z₅` then T2C; a tie `z₃ = z₆` is moved off along `x₃ - x₆`).
* `a236_cert_of_wall`: a wall point with the four facet letters and `A236Rob ∨ A236QD0` gives
  `Gen.LexAny F ∨ Gen.SplitAny F`.
* `SegLet` (the 1-D Helly letters of `SegmentHelly.exists_on_segment_iff` on the segment `[x₃ - x₂, x₆ - x₂]`) and
  `A236E x F`: for each of the six pieces (facet forms `016, 0345, 046, 346` + the piece forms) the letters fail.
  Each `¬ SegLet` is a statement about the signs of the forms at the two face corners `x₃ - x₂`, `x₆ - x₂` and of
  the crossing determinants `a_i b_j - b_i a_j` (= the piece is empty on the open face).
* **`a236_cert_or_E`**: under `OB1 x`, `Gen.LexAny F ∨ Gen.SplitAny F ∨ A236E x F`; hole facts
  `holeLeaf_a236E` and `holeLeaf_a236E_twin`.  Deciding test (nopert229 tools/genleaves/runs/a236lean/, 73688
  sides of the A236MECH data): 0 sides where the A2.236 wall fails and `A236E` fails; `A236E` holds at 6 sides
  where the wall passes (other apex systems); Helly letters = exact midpoint enumeration at every side.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace Topology
open Finset Filter
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.HC Minimality.T24.SF Minimality.T24.Stmt
  Minimality.T24.TwoCone

namespace Minimality.T24.Cell

variable {x : Fin 7 → ℝ³}

/-! ## Generic helpers -/

/-- `RobUni` is invariant under a positive scaling of the depths. -/
theorem robUni_mul_pos {k : ℕ} {z : ZMod k → ℝ} {a : ℝ} (ha : 0 < a) (h : RobUni z) :
    RobUni (fun i => a * z i) := by
  intro B b c d hb hbc hcd hd ⟨h1, h2, h3, h4⟩
  exact h B b c d hb hbc hcd hd ⟨le_of_mul_le_mul_left h1 ha, le_of_mul_le_mul_left h2 ha,
    le_of_mul_le_mul_left h3 ha, le_of_mul_le_mul_left h4 ha⟩

/-- A strict linear letter persists along `r + η v` for small `η > 0`. -/
theorem ev_inner_pos {n r v : ℝ³} (h : 0 < ⟪n, r⟫) : ∀ᶠ η : ℝ in 𝓝[>] 0, 0 < ⟪n, r + η • v⟫ := by
  filter_upwards [Minimality.T24.Belt.ev_pos _ ⟪n, v⟫ h] with η hη
  rwa [inner_add_right, real_inner_smul_right, mul_comm]

/-- `det3` is linear in the view. -/
theorem det3_add_smul_view (a b r v : ℝ³) (η : ℝ) :
    Split.det3 a b (r + η • v) = Split.det3 a b r + η * Split.det3 a b v := by
  simp only [Split.det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

theorem cellA2_D : univ \ U_A2 = D_A2 := by decide

/-! ## Open-cell views of `A2` are `T_2` views -/

/-- **Every view of the open cell `A2` is a positive multiple of a `T_2` view** `uT2 x β γ`, `β, γ > 0`
(coordinates in `x₀ - x₁, x₂ - x₁, x₆ - x₁`: `126` behind gives the first `> 0`, `016` in front the second `< 0`,
`012` behind the third `> 0`). -/
theorem cA2_view_uT2 (F : S0xFac 9 s0x_S24 x) {w : ℝ³} (hcell : CellAt F U_A2 D_A2 w) :
    ∃ a beta gamma : ℝ, 0 < a ∧ 0 < beta ∧ 0 < gamma ∧ w = a • uT2 x beta gamma := by
  have hli := li_of_det3 _ _ _ (det3_e026_ne F)
  have hspan : Submodule.span ℝ (Set.range ![x 0 - x 1, x 2 - x 1, x 6 - x 1]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp)
  have hw : w ∈ Submodule.span ℝ (Set.range ![x 0 - x 1, x 2 - x 1, x 6 - x 1]) := by
    rw [hspan]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hw
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hc
  have hN : ∀ t : Fin 9, ⟪F.N t, w⟫ = c 0 * (F.f t (x 0) - F.f t (x 1)) +
      c 1 * (F.f t (x 2) - F.f t (x 1)) + c 2 * (F.f t (x 6) - F.f t (x 1)) := by
    intro t
    rw [← hc, inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_right, F.inner_sub, F.inner_sub, F.inner_sub]
  have ha : 0 < c 0 := by
    have h5 := hcell.2 5 (by decide)
    rw [hN, F.zero 5 1 (by decide), F.zero 5 2 (by decide), F.zero 5 6 (by decide)] at h5
    have hf := F.neg 5 0 (by decide)
    nlinarith
  have hb : c 1 < 0 := by
    have h1 := hcell.1 1 (by decide)
    rw [hN, F.zero 1 0 (by decide), F.zero 1 1 (by decide), F.zero 1 6 (by decide)] at h1
    have hf := F.neg 1 2 (by decide)
    nlinarith
  have hcc : 0 < c 2 := by
    have h0 := hcell.2 0 (by decide)
    rw [hN, F.zero 0 0 (by decide), F.zero 0 1 (by decide), F.zero 0 2 (by decide)] at h0
    have hf := F.neg 0 6 (by decide)
    nlinarith
  refine ⟨c 0, -c 1 / c 0, c 2 / c 0, ha, div_pos (by linarith) ha, div_pos hcc ha, ?_⟩
  have e1 : c 0 * -(-c 1 / c 0) = c 1 := by field_simp
  have e2 : c 0 * (c 2 / c 0) = c 2 := by field_simp
  rw [← hc, uT2, capView]
  simp only [smul_add, smul_smul, e1, e2, mul_one]

/-! ## L1: `RobUni` letters on the open cell -/

/-- **Strict `RobUni` letters** of `cA2` at `w` (linear forms `> 0`): `z₀ < z₁` (Lemma Z); `z₀ < z₅, z₆` or
`z₀ < z₅, z₃` (rule T2C); `z₆ < z₃ < z₅` or `z₃ < z₆ < z₁` (Lemma P0). -/
def A236Rob (x : Fin 7 → ℝ³) (w : ℝ³) : Prop :=
  0 < ⟪x 1 - x 0, w⟫ ∨ (0 < ⟪x 5 - x 0, w⟫ ∧ 0 < ⟪x 6 - x 0, w⟫) ∨
    (0 < ⟪x 5 - x 0, w⟫ ∧ 0 < ⟪x 3 - x 0, w⟫) ∨ (0 < ⟪x 3 - x 6, w⟫ ∧ 0 < ⟪x 5 - x 3, w⟫) ∨
    (0 < ⟪x 6 - x 3, w⟫ ∧ 0 < ⟪x 1 - x 6, w⟫)

/-- `A236Rob` is open along `r + η v`. -/
theorem ev_a236Rob {r : ℝ³} (v : ℝ³) (h : A236Rob x r) : ∀ᶠ η : ℝ in 𝓝[>] 0, A236Rob x (r + η • v) := by
  rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact (ev_inner_pos h).mono fun _ h => Or.inl h
  · exact ((ev_inner_pos h1).and (ev_inner_pos h2)).mono fun _ h => Or.inr (Or.inl h)
  · exact ((ev_inner_pos h1).and (ev_inner_pos h2)).mono fun _ h => Or.inr (Or.inr (Or.inl h))
  · exact ((ev_inner_pos h1).and (ev_inner_pos h2)).mono fun _ h => Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact ((ev_inner_pos h1).and (ev_inner_pos h2)).mono fun _ h => Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- **L1 (open cell):** under `OB1 x`, every view of the open cell `A2` with a strict `A236Rob` letter has `RobUni`
depths on `cA2` (Facts 1 and 2 on the whole open cell via `cA2_view_uT2`; then `cA2_robUni_of_t2c`,
`cA2_robUni_of_p0`). -/
theorem cA2_robUni_of_cell (F : S0xFac 9 s0x_S24 x) (hO : H24K.SAT.OB1 x) {w : ℝ³}
    (hcell : CellAt F U_A2 D_A2 w) (hlet : A236Rob x w) :
    RobUni (fun i => ⟪x (cA2 i), w⟫) := by
  obtain ⟨a, β, γ, ha, hβ, hγ, rfl⟩ := cA2_view_uT2 F hcell
  have hz : ∀ v : ℝ³, ⟪v, a • uT2 x β γ⟫ = a * ⟪v, uT2 x β γ⟫ := fun v => real_inner_smul_right _ _ _
  have hcell' : CellAt F U_A2 D_A2 (uT2 x β γ) := by
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · have h := hcell.1 t ht; rw [hz] at h; exact pos_of_mul_pos_right h ha.le
    · have h := hcell.2 t ht; rw [hz] at h; nlinarith
  have hp : ∀ p q : Fin 7, 0 < ⟪x q - x p, a • uT2 x β γ⟫ → ⟪x p, uT2 x β γ⟫ < ⟪x q, uT2 x β γ⟫ := by
    intro p q h
    rw [hz, inner_sub_left] at h
    have := pos_of_mul_pos_right h ha.le
    linarith
  have hR : RobUni (fun i => ⟪x (cA2 i), uT2 x β γ⟫) := by
    rcases hlet with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact cA2_robUni_of_t2c F hO hβ hγ hcell' (Or.inl (hp 0 1 h))
    · exact cA2_robUni_of_t2c F hO hβ hγ hcell' (Or.inr ⟨hp 0 5 h1, Or.inl (hp 0 6 h2).le⟩)
    · exact cA2_robUni_of_t2c F hO hβ hγ hcell' (Or.inr ⟨hp 0 5 h1, Or.inr (hp 0 3 h2).le⟩)
    · exact cA2_robUni_of_p0 F hO hβ hγ (Or.inl ⟨hp 6 3 h1, hp 3 5 h2⟩)
    · exact cA2_robUni_of_p0 F hO hβ hγ (Or.inr ⟨hp 3 6 h1, hp 6 1 h2⟩)
  simpa only [hz] using robUni_mul_pos ha hR

/-! ## L2: the apex certificates `A+6-1^3` and `A-5-3^6` on the open cell -/

/-- **L2 (open cell, apex):** at a view of the open cell `A2` with `det24 x · Q > 0` (`Q = det(x₅ - x₃, x₁ - x₆, w)`,
`h₅` of `A+6-1^3` = `h₁` of `A-5-3^6`), `z₀, z₁, z₅ < min(z₃, z₆)` and `z₃ ≠ z₆`, the rim `cA2` carries a strict
apex certificate: base `6-1` apex `3` if `z₃ < z₆`, base `5-3` apex `6` if `z₆ < z₃`.  The `h₀` letters
(`g63`, `g36`) come from S2.  No `OB1`, no `CbarIn`, no peak condition on vertex `0`. -/
theorem cA2_apexCert_of_QD0 (F : S0xFac 9 s0x_S24 x) {w : ℝ³} (hcell : CellAt F U_A2 D_A2 w)
    (hQ : 0 < det24 x * Split.det3 (x 5 - x 3) (x 1 - x 6) w)
    (h0 : ⟪x 0, w⟫ < min ⟪x 3, w⟫ ⟪x 6, w⟫) (h1 : ⟪x 1, w⟫ < min ⟪x 3, w⟫ ⟪x 6, w⟫)
    (h5 : ⟪x 5, w⟫ < min ⟪x 3, w⟫ ⟪x 6, w⟫) (h36 : ⟪x 3, w⟫ ≠ ⟪x 6, w⟫) :
    ApexCert (fun i => x (cA2 i)) w := by
  have hcell' : CellAt F cellA2.U (univ \ cellA2.U) w := by
    show CellAt F U_A2 (univ \ U_A2) w; rw [cellA2_D]; exact hcell
  obtain ⟨ρ, hρ, hρd, hrim⟩ := cellA2_rimSign F hcell'
  obtain ⟨-, -, hg63, hg36⟩ := a236_S2 F hcell' hQ.le
  -- `ρ`-weighted forms of the three shape letters
  have hρ' : ∀ D : ℝ, 0 < det24 x * D → 0 < ρ * D := by
    intro D hD
    rcases hρ with rfl | rfl
    · have : 0 < det24 x := by linarith
      have := pos_of_mul_pos_right hD this.le; linarith
    · have : det24 x < 0 := by linarith
      nlinarith
  have qρ := hρ' _ hQ
  have g63ρ := hρ' _ hg63
  have g36ρ := hρ' _ hg36
  have habs : ∀ D : ℝ, 0 < ρ * D → |D| = ρ * D := by
    intro D hD
    rcases hρ with rfl | rfl
    · rw [one_mul] at hD ⊢; exact abs_of_pos hD
    · have : D < 0 := by linarith
      rw [abs_of_neg this]; ring
  have hall : ∀ j : ZMod 5, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by decide
  have hev : cA2 0 = 0 ∧ cA2 1 = 5 ∧ cA2 2 = 3 ∧ cA2 3 = 6 ∧ cA2 4 = 1 ∧ (3 : ZMod 5) + 1 = 4 ∧
      (1 : ZMod 5) + 1 = 2 := by decide
  obtain ⟨e0, e1, e2, e3, e4, e34, e12⟩ := hev
  have m3 := min_le_left ⟪x 3, w⟫ ⟪x 6, w⟫
  have m6 := min_le_right ⟪x 3, w⟫ ⟪x 6, w⟫
  rcases lt_or_gt_of_ne h36 with h36 | h63
  · -- `A+6-1^3`: base `6 → 1` (positions `3, 4`), apex `3` (position `2`); `1, 0, 5 < 3 < 6`
    have r0 : 0 < ρ * Split.det3 (x 1 - x 6) (x 0 - x 6) w := by
      simpa only [e34, e3, e4, e0] using hrim 3 0 (by decide) (by decide)
    have r5 : 0 < ρ * Split.det3 (x 1 - x 6) (x 5 - x 6) w := by
      simpa only [e34, e3, e4, e1] using hrim 3 1 (by decide) (by decide)
    have r3 : 0 < ρ * Split.det3 (x 1 - x 6) (x 3 - x 6) w := by
      simpa only [e34, e3, e4, e2] using hrim 3 2 (by decide) (by decide)
    have hsw : ∀ p : Fin 7, Split.det3 (x p - x 6) (x 1 - x 6) w = -Split.det3 (x 1 - x 6) (x p - x 6) w := by
      intro p; simp only [Split.det3, PiLp.sub_apply]; ring
    have d0 : Split.det3 (x 1 - x 6) (x 3 - x 6) w - Split.det3 (x 1 - x 6) (x 0 - x 6) w =
        Split.det3 (x 0 - x 3) (x 1 - x 6) w := by
      simp only [Split.det3, PiLp.sub_apply]; ring
    have d5 : Split.det3 (x 1 - x 6) (x 3 - x 6) w - Split.det3 (x 1 - x 6) (x 5 - x 6) w =
        Split.det3 (x 5 - x 3) (x 1 - x 6) w := by
      simp only [Split.det3, PiLp.sub_apply]; ring
    refine ⟨3, 2, by decide, by decide, ?_, 1, Or.inl rfl, ?_, ?_⟩
    · intro j hj1 hj2 hj3
      simp only [e34, e3, e4, e2]
      rw [hsw, hsw, abs_neg, abs_neg, habs _ r3]
      rcases hall j with rfl | rfl | rfl | rfl | rfl
      · rw [e0, habs _ r0]
        have k := congrArg (fun t => ρ * t) d0; simp only [mul_sub] at k; linarith
      · rw [e1, habs _ r5]
        have k := congrArg (fun t => ρ * t) d5; simp only [mul_sub] at k; linarith
      · exact absurd rfl hj3
      · exact absurd rfl hj1
      · exact absurd (by decide) hj2
    · intro j hj
      rcases hall j with rfl | rfl | rfl | rfl | rfl
      · simp only [e0, e2, one_mul]; linarith
      · simp only [e1, e2, one_mul]; linarith
      · exact absurd hj (by decide)
      · exact absurd hj (by decide)
      · simp only [e4, e2, one_mul]; linarith
    · intro j hj
      rcases hall j with rfl | rfl | rfl | rfl | rfl
      · exact absurd hj (by decide)
      · exact absurd hj (by decide)
      · exact absurd hj (by decide)
      · simp only [e3, e2, one_mul]; linarith
      · exact absurd hj (by decide)
  · -- `A-5-3^6`: base `5 → 3` (positions `1, 2`), apex `6` (position `3`); `3 > 6 > 1, 0, 5`
    have r1 : 0 < ρ * Split.det3 (x 3 - x 5) (x 1 - x 5) w := by
      simpa only [e12, e1, e2, e4] using hrim 1 4 (by decide) (by decide)
    have r0 : 0 < ρ * Split.det3 (x 3 - x 5) (x 0 - x 5) w := by
      simpa only [e12, e1, e2, e0] using hrim 1 0 (by decide) (by decide)
    have r6 : 0 < ρ * Split.det3 (x 3 - x 5) (x 6 - x 5) w := by
      simpa only [e12, e1, e2, e3] using hrim 1 3 (by decide) (by decide)
    have hsw : ∀ p : Fin 7, Split.det3 (x p - x 5) (x 3 - x 5) w = -Split.det3 (x 3 - x 5) (x p - x 5) w := by
      intro p; simp only [Split.det3, PiLp.sub_apply]; ring
    have d1 : Split.det3 (x 3 - x 5) (x 6 - x 5) w - Split.det3 (x 3 - x 5) (x 1 - x 5) w =
        Split.det3 (x 5 - x 3) (x 1 - x 6) w := by
      simp only [Split.det3, PiLp.sub_apply]; ring
    have d0 : Split.det3 (x 3 - x 5) (x 6 - x 5) w - Split.det3 (x 3 - x 5) (x 0 - x 5) w =
        Split.det3 (x 0 - x 6) (x 3 - x 5) w := by
      simp only [Split.det3, PiLp.sub_apply]; ring
    refine ⟨1, 3, by decide, by decide, ?_, -1, Or.inr rfl, ?_, ?_⟩
    · intro j hj1 hj2 hj3
      simp only [e12, e1, e2, e3]
      rw [hsw, hsw, abs_neg, abs_neg, habs _ r6]
      rcases hall j with rfl | rfl | rfl | rfl | rfl
      · rw [e0, habs _ r0]
        have k := congrArg (fun t => ρ * t) d0; simp only [mul_sub] at k; linarith
      · exact absurd rfl hj1
      · exact absurd (by decide) hj2
      · exact absurd rfl hj3
      · rw [e4, habs _ r1]
        have k := congrArg (fun t => ρ * t) d1; simp only [mul_sub] at k; linarith
    · intro j hj
      rcases hall j with rfl | rfl | rfl | rfl | rfl
      · exact absurd hj (by decide)
      · exact absurd hj (by decide)
      · simp only [e2, e3]; linarith
      · exact absurd hj (by decide)
      · exact absurd hj (by decide)
    · intro j hj
      rcases hall j with rfl | rfl | rfl | rfl | rfl
      · simp only [e0, e3]; linarith
      · simp only [e1, e3]; linarith
      · exact absurd hj (by decide)
      · exact absurd hj (by decide)
      · simp only [e4, e3]; linarith

/-- **The `QD0` letters** at `w`: `det24 x · Q > 0`, `z₀ < z₃`, `z₀ < z₆`. -/
def A236QD0 (x : Fin 7 → ℝ³) (w : ℝ³) : Prop :=
  0 < det24 x * Split.det3 (x 5 - x 3) (x 1 - x 6) w ∧ 0 < ⟪x 3 - x 0, w⟫ ∧ 0 < ⟪x 6 - x 0, w⟫

/-- `A236QD0` is open along `r + η v`. -/
theorem ev_a236QD0 {r : ℝ³} (v : ℝ³) (h : A236QD0 x r) : ∀ᶠ η : ℝ in 𝓝[>] 0, A236QD0 x (r + η • v) := by
  obtain ⟨hQ, h3, h6⟩ := h
  have hQ' : ∀ᶠ η : ℝ in 𝓝[>] 0, 0 < det24 x * Split.det3 (x 5 - x 3) (x 1 - x 6) (r + η • v) := by
    filter_upwards [Minimality.T24.Belt.ev_pos _ (det24 x * Split.det3 (x 5 - x 3) (x 1 - x 6) v) hQ]
      with η hη
    rw [det3_add_smul_view]; linarith
  exact (hQ'.and ((ev_inner_pos h3).and (ev_inner_pos h6))).mono fun _ h => ⟨h.1, h.2.1, h.2.2⟩

/-- **`QD0` with no tie:** under `OB1`, a view of the open cell `A2` with `A236QD0` and `z₃ ≠ z₆` carries `RobUni`
(T2C, if `z₀ < z₁` or `z₀ < z₅`) or `ApexCert` (`cA2_apexCert_of_QD0`, otherwise). -/
theorem cA2_cert_of_QD0 (F : S0xFac 9 s0x_S24 x) (hO : H24K.SAT.OB1 x) {w : ℝ³}
    (hcell : CellAt F U_A2 D_A2 w) (h : A236QD0 x w) (h36 : ⟪x 3, w⟫ ≠ ⟪x 6, w⟫) :
    RobUni (fun i => ⟪x (cA2 i), w⟫) ∨ ApexCert (fun i => x (cA2 i)) w := by
  obtain ⟨hQ, h3, h6⟩ := h
  by_cases h01 : 0 < ⟪x 1 - x 0, w⟫
  · exact Or.inl (cA2_robUni_of_cell F hO hcell (Or.inl h01))
  by_cases h05 : 0 < ⟪x 5 - x 0, w⟫
  · exact Or.inl (cA2_robUni_of_cell F hO hcell (Or.inr (Or.inl ⟨h05, h6⟩)))
  push Not at h01 h05
  rw [inner_sub_left] at h01 h05 h3 h6
  right
  exact cA2_apexCert_of_QD0 F hcell hQ (lt_min (by linarith) (by linarith))
    (lt_min (by linarith) (by linarith)) (lt_min (by linarith) (by linarith)) h36

/-- **Open cell to a leaf:** under `OB1`, a view of the open cell `A2` with `A236Rob ∨ A236QD0` gives
`Gen.LexAny F ∨ Gen.SplitAny F` (a tie `z₃ = z₆` in the `QD0` case is moved off along `x₃ - x₆`). -/
theorem a236_cert_of_cell (F : S0xFac 9 s0x_S24 x) (hO : H24K.SAT.OB1 x) {w : ℝ³}
    (hcell : CellAt F U_A2 D_A2 w) (h : A236Rob x w ∨ A236QD0 x w) : Gen.LexAny F ∨ Gen.SplitAny F := by
  have leaf : ∀ u : ℝ³, CellAt F U_A2 D_A2 u →
      (RobUni (fun i => ⟪x (cA2 i), u⟫) ∨ ApexCert (fun i => x (cA2 i)) u) → Gen.LexAny F ∨ Gen.SplitAny F := by
    intro u hu hc
    have hu' : CellAt F cellA2.U (univ \ cellA2.U) u := by
      show CellAt F U_A2 (univ \ U_A2) u; rw [cellA2_D]; exact hu
    rcases hc with hR | hA
    · exact Or.inl (lexAny_of_cellRob F cellA2 hu' hR)
    · exact Or.inr (splitAny_of_cellApex F cellA2 hu' hA)
  rcases h with hR | hQ
  · exact leaf w hcell (Or.inl (cA2_robUni_of_cell F hO hcell hR))
  by_cases h36 : ⟪x 3, w⟫ = ⟪x 6, w⟫
  · -- move along `x₃ - x₆`: the open cell and `QD0` persist, and `z₃ - z₆` becomes `η |x₃ - x₆|² > 0`
    have hne : x 3 - x 6 ≠ 0 := by
      intro e
      have hf := F.hN 3 (x 3) (x 6)
      rw [e, inner_zero_right, F.zero 3 3 (by decide)] at hf
      linarith [F.neg 3 6 (by decide)]
    have hpos : 0 < ⟪x 3 - x 6, x 3 - x 6⟫ := real_inner_self_pos.mpr hne
    have evC : ∀ᶠ η : ℝ in 𝓝[>] 0, CellAt F U_A2 D_A2 (w + η • (x 3 - x 6)) := by
      have := cellAt_eventually_of_wall F U_A2 (v := x 3 - x 6) (w0 := w)
        (fun t ht => Or.inl (hcell.1 t ht)) (fun t ht => Or.inl (hcell.2 t (by rw [← cellA2_D]; simpa using ht)))
      rwa [cellA2_D] at this
    obtain ⟨η, hc, hq, hη⟩ := (evC.and ((ev_a236QD0 (x 3 - x 6) hQ).and Minimality.T24.Belt.ev_gt0)).exists
    refine leaf _ hc (cA2_cert_of_QD0 F hO hc hq ?_)
    intro e
    have : ⟪x 3 - x 6, w + η • (x 3 - x 6)⟫ = η * ⟪x 3 - x 6, x 3 - x 6⟫ := by
      rw [inner_add_right, real_inner_smul_right, inner_sub_left, h36, sub_self, zero_add]
    rw [inner_sub_left, e, sub_self] at this
    nlinarith
  · exact leaf w hcell (cA2_cert_of_QD0 F hO hcell hQ h36)

/-! ## The wall -/

/-- A point `p (x₃ - x₂) + q (x₆ - x₂)` of the `236` face (`p, q > 0`: the open face; `t2e236 x s = a236Pt x 1 s`). -/
noncomputable def a236Pt (x : Fin 7 → ℝ³) (p q : ℝ) : ℝ³ := p • (x 3 - x 2) + q • (x 6 - x 2)

theorem t2e236_eq_a236Pt (s : ℝ) : t2e236 x s = a236Pt x 1 s := by
  rw [t2e236, a236Pt, one_smul]

/-- **Wall to open cell:** at a point of the open `236` face with `016, 0345, 046, 346` in front, the views
`r + η (x₁ - x₂)` are in the open cell `A2` for small `η > 0`. -/
theorem a236_cellAt_eventually (F : S0xFac 9 s0x_S24 x) {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (h1 : 0 < ⟪F.N 1, a236Pt x p q⟫) (h3 : 0 < ⟪F.N 3, a236Pt x p q⟫) (h4 : 0 < ⟪F.N 4, a236Pt x p q⟫)
    (h8 : 0 < ⟪F.N 8, a236Pt x p q⟫) :
    ∀ᶠ η : ℝ in 𝓝[>] 0, CellAt F U_A2 D_A2 (a236Pt x p q + η • (x 1 - x 2)) := by
  have hNr : ∀ t : Fin 9, ⟪F.N t, a236Pt x p q⟫ =
      p * (F.f t (x 3) - F.f t (x 2)) + q * (F.f t (x 6) - F.f t (x 2)) := by
    intro t
    rw [a236Pt, inner_add_right, real_inner_smul_right, real_inner_smul_right, F.inner_sub, F.inner_sub]
  rw [← cellA2_D]
  refine cellAt_eventually_of_wall F U_A2 (fun t ht => ?_) (fun t ht => ?_)
  · have ht' : t ∈ ({1, 3, 4, 8} : Finset (Fin 9)) := ht
    simp only [mem_insert, mem_singleton] at ht'
    left
    rcases ht' with rfl | rfl | rfl | rfl
    · exact h1
    · exact h3
    · exact h4
    · exact h8
  · have ht' : t ∉ ({1, 3, 4, 8} : Finset (Fin 9)) := ht
    have ht'' : t = 0 ∨ t = 2 ∨ t = 5 ∨ t = 6 ∨ t = 7 := by revert t; decide
    rcases ht'' with rfl | rfl | rfl | rfl | rfl
    · left
      rw [hNr, F.zero 0 2 (by decide)]
      have h3' := F.neg 0 3 (by decide)
      have h6' := F.neg 0 6 (by decide)
      nlinarith
    · left
      rw [hNr, F.zero 2 2 (by decide)]
      have h3' := F.neg 2 3 (by decide)
      have h6' := F.neg 2 6 (by decide)
      nlinarith
    · left
      rw [hNr, F.zero 5 2 (by decide), F.zero 5 6 (by decide)]
      have h3' := F.neg 5 3 (by decide)
      nlinarith
    · left
      rw [hNr, F.zero 6 2 (by decide), F.zero 6 3 (by decide)]
      have h6' := F.neg 6 6 (by decide)
      nlinarith
    · right
      rw [hNr, F.inner_sub, F.zero 7 2 (by decide), F.zero 7 3 (by decide), F.zero 7 6 (by decide)]
      exact ⟨by ring, by linarith [F.neg 7 1 (by decide)]⟩

/-- **The wall certificate:** a point of the open `236` face with the four facet letters and `A236Rob ∨ A236QD0`
gives `Gen.LexAny F ∨ Gen.SplitAny F` (push into the open cell, then `a236_cert_of_cell`). -/
theorem a236_cert_of_wall (F : S0xFac 9 s0x_S24 x) (hO : H24K.SAT.OB1 x) {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (h1 : 0 < ⟪F.N 1, a236Pt x p q⟫) (h3 : 0 < ⟪F.N 3, a236Pt x p q⟫) (h4 : 0 < ⟪F.N 4, a236Pt x p q⟫)
    (h8 : 0 < ⟪F.N 8, a236Pt x p q⟫) (h : A236Rob x (a236Pt x p q) ∨ A236QD0 x (a236Pt x p q)) :
    Gen.LexAny F ∨ Gen.SplitAny F := by
  have evC := a236_cellAt_eventually F hp hq h1 h3 h4 h8
  have evL : ∀ᶠ η : ℝ in 𝓝[>] 0, A236Rob x (a236Pt x p q + η • (x 1 - x 2)) ∨
      A236QD0 x (a236Pt x p q + η • (x 1 - x 2)) := by
    rcases h with h | h
    · exact (ev_a236Rob _ h).mono fun _ h => Or.inl h
    · exact (ev_a236QD0 _ h).mono fun _ h => Or.inr h
  obtain ⟨η, hc, hl⟩ := (evC.and evL).exists
  exact a236_cert_of_cell F hO hc hl

/-- **L1 on the wall** (`LexAny`): a point of the open `236` face with the four facet letters and a strict
`A236Rob` letter gives `Gen.LexAny F`. -/
theorem a236_lexAny_of_wallRob (F : S0xFac 9 s0x_S24 x) (hO : H24K.SAT.OB1 x) {p q : ℝ} (hp : 0 < p)
    (hq : 0 < q) (h1 : 0 < ⟪F.N 1, a236Pt x p q⟫) (h3 : 0 < ⟪F.N 3, a236Pt x p q⟫)
    (h4 : 0 < ⟪F.N 4, a236Pt x p q⟫) (h8 : 0 < ⟪F.N 8, a236Pt x p q⟫) (h : A236Rob x (a236Pt x p q)) :
    Gen.LexAny F := by
  obtain ⟨η, hc, hl⟩ := ((a236_cellAt_eventually F hp hq h1 h3 h4 h8).and (ev_a236Rob (x 1 - x 2) h)).exists
  have hc' : CellAt F cellA2.U (univ \ cellA2.U) (a236Pt x p q + η • (x 1 - x 2)) := by
    show CellAt F U_A2 (univ \ U_A2) _; rw [cellA2_D]; exact hc
  exact lexAny_of_cellRob F cellA2 hc' (cA2_robUni_of_cell F hO hc hl)

/-! ## The letter condition `A236E` (1-D Helly on the face) -/

/-- **1-D Helly letters** of finitely many forms `⟪n i, ·⟫` on the segment `[E0, E1]` (`exists_on_segment_iff`):
each form is positive at an end, and every rising form `i` and falling form `j` cross in the right order. -/
def SegLet {ι : Type*} [Fintype ι] (n : ι → ℝ³) (E0 E1 : ℝ³) : Prop :=
  (∀ i, 0 < ⟪n i, E0⟫ ∨ 0 < ⟪n i, E1⟫) ∧
    ∀ i j, ⟪n i, E0⟫ ≤ 0 → ⟪n j, E1⟫ ≤ 0 → 0 < ⟪n i, E1⟫ → 0 < ⟪n j, E0⟫ →
      ⟪n i, E0⟫ * ⟪n j, E1⟫ - ⟪n i, E1⟫ * ⟪n j, E0⟫ < 0

/-- `SegLet` is exactly "all forms are positive at a common interior point of the segment". -/
theorem segLet_iff {ι : Type*} [Fintype ι] (n : ι → ℝ³) (E0 E1 : ℝ³) :
    SegLet n E0 E1 ↔ ∃ l : ℝ, 0 < l ∧ l < 1 ∧ ∀ i, 0 < ⟪n i, (1 - l) • E0 + l • E1⟫ := by
  have e : ∀ (l : ℝ) i, ⟪n i, (1 - l) • E0 + l • E1⟫ = (1 - l) * ⟪n i, E0⟫ + l * ⟪n i, E1⟫ := fun l i => by
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  simp only [e]
  exact (exists_on_segment_iff (fun i => ⟪n i, E0⟫) (fun i => ⟪n i, E1⟫)).symm

/-- The four facet forms of the `236` wall of `A2`: `016, 0345, 046, 346` in front. -/
def a236Fac (F : S0xFac 9 s0x_S24 x) : Fin 4 → ℝ³ := ![F.N 1, F.N 3, F.N 4, F.N 8]

/-- The shape form `det24 x · det(x₅ - x₃, x₁ - x₆, ·)` as a vector. -/
noncomputable def a236Q (x : Fin 7 → ℝ³) : ℝ³ := det24 x • cross (x 5 - x 3) (x 1 - x 6)

theorem inner_a236Q (w : ℝ³) : ⟪a236Q x, w⟫ = det24 x * Split.det3 (x 5 - x 3) (x 1 - x 6) w := by
  rw [a236Q, real_inner_smul_left]
  congr 1
  simp only [Split.inner3, Split.cross_0, Split.cross_1, Split.cross_2, Split.det3]

/-- A piece on the wall: the facet forms and the piece forms `P` (all `> 0`), Helly letters on `[x₃ - x₂, x₆ - x₂]`. -/
def A236Piece {k : ℕ} (F : S0xFac 9 s0x_S24 x) (P : Fin k → ℝ³) : Prop :=
  SegLet (Sum.elim (a236Fac F) P) (x 3 - x 2) (x 6 - x 2)

/-- **The letter condition `E`** (A236-MECHANISM section 2, with the S1 repair: the `{5,6}` crown is not excluded,
it is simply not a certified piece): every certified piece of the `236` face is empty, i.e. its Helly letters fail.
Pieces: `z₀ < z₁`; `z₀ < z₅, z₆`; `z₀ < z₅, z₃`; `z₆ < z₃ < z₅`; `z₃ < z₆ < z₁`; `QD0` (`det24 x · Q > 0`,
`z₀ < z₃, z₆`). -/
def A236E (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  ¬ A236Piece F ![x 1 - x 0] ∧ ¬ A236Piece F ![x 5 - x 0, x 6 - x 0] ∧ ¬ A236Piece F ![x 5 - x 0, x 3 - x 0] ∧
    ¬ A236Piece F ![x 3 - x 6, x 5 - x 3] ∧ ¬ A236Piece F ![x 6 - x 3, x 1 - x 6] ∧
    ¬ A236Piece F ![a236Q x, x 3 - x 0, x 6 - x 0]

/-- A non-empty piece gives a point of the open face with the four facet letters and the piece letters. -/
theorem a236_point_of_piece {k : ℕ} (F : S0xFac 9 s0x_S24 x) {P : Fin k → ℝ³} (h : A236Piece F P) :
    ∃ l : ℝ, 0 < l ∧ l < 1 ∧ 0 < ⟪F.N 1, a236Pt x (1 - l) l⟫ ∧ 0 < ⟪F.N 3, a236Pt x (1 - l) l⟫ ∧
      0 < ⟪F.N 4, a236Pt x (1 - l) l⟫ ∧ 0 < ⟪F.N 8, a236Pt x (1 - l) l⟫ ∧
      ∀ j, 0 < ⟪P j, a236Pt x (1 - l) l⟫ := by
  obtain ⟨l, hl0, hl1, hall⟩ := (segLet_iff _ _ _).1 h
  exact ⟨l, hl0, hl1, hall (Sum.inl 0), hall (Sum.inl 1), hall (Sum.inl 2), hall (Sum.inl 3),
    fun j => hall (Sum.inr j)⟩

/-- **`a236_cert_or_E`:** under `OB1 x`, either a view next to the `236` wall of `A2` carries `RobUni` or a strict
apex certificate on `cA2` (hence `Gen.LexAny F ∨ Gen.SplitAny F`), or the letter condition `A236E x F` holds. -/
theorem a236_cert_or_E (F : S0xFac 9 s0x_S24 x) (hO : H24K.SAT.OB1 x) :
    Gen.LexAny F ∨ Gen.SplitAny F ∨ A236E x F := by
  have wall : ∀ {k : ℕ} (P : Fin k → ℝ³), A236Piece F P →
      (∀ w : ℝ³, (∀ j, 0 < ⟪P j, w⟫) → A236Rob x w ∨ A236QD0 x w) → Gen.LexAny F ∨ Gen.SplitAny F := by
    intro k P hP hl
    obtain ⟨l, hl0, hl1, h1, h3, h4, h8, hj⟩ := a236_point_of_piece F hP
    exact a236_cert_of_wall F hO (by linarith) hl0 h1 h3 h4 h8 (hl _ hj)
  by_cases e1 : A236Piece F ![x 1 - x 0]
  · exact (wall _ e1 fun w h => Or.inl (Or.inl (by simpa using h 0))).elim (Or.inl) (fun h => Or.inr (Or.inl h))
  by_cases e2 : A236Piece F ![x 5 - x 0, x 6 - x 0]
  · refine (wall _ e2 fun w h => Or.inl (Or.inr (Or.inl ⟨by simpa using h 0, by simpa using h 1⟩))).elim
      Or.inl (fun h => Or.inr (Or.inl h))
  by_cases e3 : A236Piece F ![x 5 - x 0, x 3 - x 0]
  · refine (wall _ e3 fun w h => Or.inl (Or.inr (Or.inr (Or.inl ⟨by simpa using h 0, by simpa using h 1⟩)))).elim
      Or.inl (fun h => Or.inr (Or.inl h))
  by_cases e4 : A236Piece F ![x 3 - x 6, x 5 - x 3]
  · refine (wall _ e4 fun w h => Or.inl (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨by simpa using h 0, by simpa using h 1⟩))))).elim Or.inl (fun h => Or.inr (Or.inl h))
  by_cases e5 : A236Piece F ![x 6 - x 3, x 1 - x 6]
  · refine (wall _ e5 fun w h => Or.inl (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨by simpa using h 0, by simpa using h 1⟩))))).elim Or.inl (fun h => Or.inr (Or.inl h))
  by_cases e6 : A236Piece F ![a236Q x, x 3 - x 0, x 6 - x 0]
  · refine (wall _ e6 fun w h => Or.inr ⟨?_, by simpa using h 1, by simpa using h 2⟩).elim
      Or.inl (fun h => Or.inr (Or.inl h))
    have := h 0
    simpa [inner_a236Q] using this
  exact Or.inr (Or.inr ⟨e1, e2, e3, e4, e5, e6⟩)

/-- **Hole fact:** at a hole point with `OB1 x`, the letter condition `A236E x F` holds. -/
theorem holeLeaf_a236E {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) (hO : H24K.SAT.OB1 x) : A236E x F :=
  ((a236_cert_or_E F hO).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1

/-- **Twin hole fact:** at a hole point with `OB1 x`, the `π_24` twin satisfies `A236E` too. -/
theorem holeLeaf_a236E_twin {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) (hO : H24K.SAT.OB1 x) :
    A236E (x ∘ Sym.pi24) (Sym.sym24 F) := by
  have hO' : H24K.SAT.OB1 (x ∘ Sym.pi24) := (Minimality.T24.A19.ob1_comp_pi24 x).2 hO
  rcases a236_cert_or_E (Sym.sym24 F) hO' with hL | hS | hE
  · exact absurd (Sym.lexAny_sym F hL) hF.2.2.2.1
  · exact absurd (Sym.splitAny24_sym F hS) hF.2.2.2.2.1
  · exact hE

end Minimality.T24.Cell
