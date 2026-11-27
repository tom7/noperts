module

public import Minimality.Type24TwoCone

/-!
# The `r_60` Lex transition and unimodality on rim `0.5.2.3.6` (`FN1`–`FN2`)

* `lexAny_of_cellAt_robUni`: an open cell `CellAt F U Dn w` with `4 ≤ k`, `S0xCycUD s0x_S24 c U Dn`,
  and `RobUni (fun i => ⟪x (c i), w⟫)` yields `Gen.LexAny F` (taking `b = d1 = d2 = w`).
* `FN2` (`wc_unimodal_lexAny`, `holeLeaf_not_wc_unimodal`, `hole24_not_wc_unimodal`):
  any `cc` in the `wcCell_eventually` window at which the rim `[0, 5, 2, 3, 6]` depths
  `⟪x (wcRim i), capView x 1 0 cc⟫` are pairwise distinct and `RobUni` yields `Gen.LexAny F`.
* `FN1` (`wc_r60_lexAny`, `holeLeaf_not_wc_r60`, `hole24_not_wc_r60`, Carbon A82 addendum
  Prop 1.2(a)): if `cc0` is in the `wcCell_eventually` window, `z_6(cc0) = z_0(cc0)`, and
  `z_2(cc0) < z_5(cc0) < z_0(cc0) < z_3(cc0)`, then perturbing `cc0` gives `Gen.LexAny F`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset Filter
open scoped Topology
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.M4
open Minimality.T24.HC Minimality.T24.TwoCone

namespace Minimality.T24.WC

/-- An open cell `CellAt F U Dn w` (`4 ≤ k`) with `RobUni` depths at `w` gives `Gen.LexAny F`
via `b = d1 = d2 = w`. -/
theorem lexAny_of_cellAt_robUni {k : ℕ} [NeZero k] (hk : 4 ≤ k) {x : Fin 7 → ℝ³}
    (F : S0xFac 9 s0x_S24 x) {c : ZMod k → Fin 7} (hc : Function.Injective c)
    {U Dn : Finset (Fin 9)} (hcyc : S0xCycUD s0x_S24 c U Dn) {w : ℝ³}
    (hcell : CellAt F U Dn w) (hrob : H21.RobUni (fun i => ⟪x (c i), w⟫)) :
    Gen.LexAny F := by
  refine ⟨k, inferInstance, c, U, Dn, w, w, w, hk, hc, hcyc, ?_, ?_, ?_⟩
  · intro t ht
    exact Or.inl (hcell.1 t ht)
  · intro t ht
    exact Or.inl (neg_pos.mpr (hcell.2 t ht))
  · intro B b c' d hb hbc hcd hdk
    have hnot := hrob B b c' d hb hbc hcd hdk
    rw [not_and_or, not_and_or, not_and_or, not_le, not_le, not_le, not_le] at hnot
    rcases hnot with h | h | h | h
    · exact Or.inl (Or.inl (sub_pos.mpr h))
    · exact Or.inr (Or.inl (Or.inl (sub_pos.mpr h)))
    · exact Or.inr (Or.inr (Or.inl (Or.inl (sub_pos.mpr h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (sub_pos.mpr h))))

/-- **FN2 (general Lex side on `0.5.2.3.6`):** if `cc` is in the `wcCell_eventually` window and the
rim depths `⟪x (wcRim i), capView x 1 0 cc⟫` are pairwise distinct and `RobUni`, then `Gen.LexAny F`. -/
theorem wc_unimodal_lexAny {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (cc : ℝ)
    (hw5 : 1 / omega5 x < cc) (hw3 : cc < omega3 x)
    (h368_pos : ∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
      0 < ⟪F.N t, x 6 - x 1⟫ → -⟪F.N t, x 0 - x 1⟫ / ⟪F.N t, x 6 - x 1⟫ < cc)
    (h368_neg : ∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
      ⟪F.N t, x 6 - x 1⟫ < 0 → cc < -⟪F.N t, x 0 - x 1⟫ / ⟪F.N t, x 6 - x 1⟫)
    (h368_zero : ∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
      ⟪F.N t, x 6 - x 1⟫ = 0 → 0 < ⟪F.N t, x 0 - x 1⟫)
    (_hdist : ∀ i j : ZMod 5, i ≠ j →
      ⟪x (wcRim i), capView x 1 0 cc⟫ ≠ ⟪x (wcRim j), capView x 1 0 cc⟫)
    (hrob : H21.RobUni (fun i => ⟪x (wcRim i), capView x 1 0 cc⟫)) :
    Gen.LexAny F := by
  have hcell := wcCell_eventually F hC cc hw5 hw3 h368_pos h368_neg h368_zero
  have hord : ∀ᶠ η : ℝ in 𝓝[>] 0, ∀ i j : ZMod 5,
      ⟪x (wcRim i), capView x 1 0 cc⟫ < ⟪x (wcRim j), capView x 1 0 cc⟫ →
      ⟪x (wcRim i), capView x 1 η cc⟫ < ⟪x (wcRim j), capView x 1 η cc⟫ := by
    rw [eventually_all]; intro i; rw [eventually_all]; intro j
    by_cases hlt : ⟪x (wcRim i), capView x 1 0 cc⟫ < ⟪x (wcRim j), capView x 1 0 cc⟫
    · have hcont : Continuous (fun η : ℝ =>
          ⟪x (wcRim j), capView x 1 η cc⟫ - ⟪x (wcRim i), capView x 1 η cc⟫) := by
        unfold capView; fun_prop
      have hev := SF.ev_pos hcont (sub_pos.mpr hlt)
      exact hev.mono fun _ h _ => sub_pos.mp h
    · exact Filter.Eventually.of_forall fun _ h => absurd h hlt
  obtain ⟨η, hcell_η, hord_η⟩ := (hcell.and hord).exists
  have hrob_η : H21.RobUni (fun i => ⟪x (wcRim i), capView x 1 η cc⟫) := by
    intro B b c d hb hbc hcd hdk ⟨h1, h2, h3, h4⟩
    have hle : ∀ u v : ZMod 5,
        ⟪x (wcRim u), capView x 1 η cc⟫ ≤ ⟪x (wcRim v), capView x 1 η cc⟫ →
        ⟪x (wcRim u), capView x 1 0 cc⟫ ≤ ⟪x (wcRim v), capView x 1 0 cc⟫ := fun u v huv =>
      not_lt.mp fun hlt => not_lt_of_ge huv (hord_η v u hlt)
    exact hrob B b c d hb hbc hcd hdk ⟨hle _ _ h1, hle _ _ h2, hle _ _ h3, hle _ _ h4⟩
  exact lexAny_of_cellAt_robUni (by omega) F wcRim_inj wcRim_cyc hcell_η hrob_η

/-- **FN1 (Prop 1.2(a), `r_60` transition on `0.5.2.3.6`):** if `cc0` is in the
`wcCell_eventually` window, `z_6(cc0) = z_0(cc0)`, and `z_2(cc0) < z_5(cc0) < z_0(cc0) < z_3(cc0)`
(where `z_v(cc) = ⟪x v - x 1, capView x 1 0 cc⟫`), then `Gen.LexAny F`. -/
theorem wc_r60_lexAny {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (cc0 : ℝ)
    (hw5 : 1 / omega5 x < cc0) (hw3 : cc0 < omega3 x)
    (h368_pos : ∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
      0 < ⟪F.N t, x 6 - x 1⟫ → -⟪F.N t, x 0 - x 1⟫ / ⟪F.N t, x 6 - x 1⟫ < cc0)
    (h368_neg : ∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
      ⟪F.N t, x 6 - x 1⟫ < 0 → cc0 < -⟪F.N t, x 0 - x 1⟫ / ⟪F.N t, x 6 - x 1⟫)
    (h368_zero : ∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
      ⟪F.N t, x 6 - x 1⟫ = 0 → 0 < ⟪F.N t, x 0 - x 1⟫)
    (h60 : ⟪x 6 - x 1, capView x 1 0 cc0⟫ = ⟪x 0 - x 1, capView x 1 0 cc0⟫)
    (h25 : ⟪x 2 - x 1, capView x 1 0 cc0⟫ < ⟪x 5 - x 1, capView x 1 0 cc0⟫)
    (h50 : ⟪x 5 - x 1, capView x 1 0 cc0⟫ < ⟪x 0 - x 1, capView x 1 0 cc0⟫)
    (h03 : ⟪x 0 - x 1, capView x 1 0 cc0⟫ < ⟪x 3 - x 1, capView x 1 0 cc0⟫) :
    Gen.LexAny F := by
  let s60 : ℝ := ⟪x 6 - x 0, x 6 - x 1⟫
  have hs60_ne : s60 ≠ 0 := by
    intro h0
    have h60' : ⟪x 6 - x 0, capView x 1 0 cc0⟫ = 0 := by
      have : x 6 - x 0 = (x 6 - x 1) - (x 0 - x 1) := by abel
      rw [this, inner_sub_left, h60, sub_self]
    have h0' : ⟪x 6 - x 0, x 0 - x 1⟫ = 0 := by
      dsimp only [capView] at h60'
      rw [one_smul, zero_smul, add_zero, inner_add_right, real_inner_smul_right] at h60'
      change ⟪x 6 - x 0, x 0 - x 1⟫ + cc0 * s60 = 0 at h60'
      rw [h0, mul_zero, add_zero] at h60'
      exact h60'
    have hnorm : ⟪x 6 - x 0, x 6 - x 0⟫ = 0 := by
      have : x 6 - x 0 = (x 6 - x 1) - (x 0 - x 1) := by abel
      conv_lhs => rhs; rw [this]
      rw [inner_sub_right]
      change s60 - ⟪x 6 - x 0, x 0 - x 1⟫ = 0
      rw [h0, h0', sub_self]
    have hx60 : x 6 = x 0 := sub_eq_zero.mp (inner_self_eq_zero.mp hnorm)
    have hneg := F.neg 0 6 (by decide)
    rw [hx60, F.zero 0 0 (by decide)] at hneg
    exact lt_irrefl 0 hneg
  let sg : ℝ := if 0 < s60 then 1 else -1
  have hsg_pos : 0 < sg * s60 := by
    dsimp only [sg]; split_ifs with h
    · linarith
    · have := lt_of_le_of_ne (not_lt.mp h) hs60_ne; linarith
  -- Perturb `cc(ε) = cc0 + sg * ε` for `ε ∈ 𝓝[>] 0`
  let cc : ℝ → ℝ := fun ε => cc0 + sg * ε
  have hcc_cont : Continuous cc := by unfold cc; fun_prop
  have hev_w5 : ∀ᶠ ε : ℝ in 𝓝[>] 0, 1 / omega5 x < cc ε :=
    (SF.ev_pos (continuous_iff_continuousAt.mpr fun _ => (hcc_cont.continuousAt.sub continuousAt_const))
      (by simpa [cc] using sub_pos.mpr hw5)).mono fun _ h => sub_pos.mp h
  have hev_w3 : ∀ᶠ ε : ℝ in 𝓝[>] 0, cc ε < omega3 x :=
    (SF.ev_pos (continuous_iff_continuousAt.mpr fun _ => (continuousAt_const.sub hcc_cont.continuousAt))
      (by simpa [cc] using sub_pos.mpr hw3)).mono fun _ h => sub_pos.mp h
  have hev_368p : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
      0 < ⟪F.N t, x 6 - x 1⟫ → -⟪F.N t, x 0 - x 1⟫ / ⟪F.N t, x 6 - x 1⟫ < cc ε := by
    rw [eventually_all]; intro t
    by_cases ht : t ∈ ({3, 6, 8} : Finset (Fin 9))
    · by_cases hpos : 0 < ⟪F.N t, x 6 - x 1⟫
      · have hev := SF.ev_pos (continuous_iff_continuousAt.mpr fun _ =>
            hcc_cont.continuousAt.sub continuousAt_const)
          (by simpa [cc] using sub_pos.mpr (h368_pos t ht hpos))
        exact hev.mono fun _ h _ _ => sub_pos.mp h
      · exact Filter.Eventually.of_forall fun _ _ hp => absurd hp hpos
    · exact Filter.Eventually.of_forall fun _ h => absurd h ht
  have hev_368n : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
      ⟪F.N t, x 6 - x 1⟫ < 0 → cc ε < -⟪F.N t, x 0 - x 1⟫ / ⟪F.N t, x 6 - x 1⟫ := by
    rw [eventually_all]; intro t
    by_cases ht : t ∈ ({3, 6, 8} : Finset (Fin 9))
    · by_cases hneg : ⟪F.N t, x 6 - x 1⟫ < 0
      · have hev := SF.ev_pos (continuous_iff_continuousAt.mpr fun _ =>
            continuousAt_const.sub hcc_cont.continuousAt)
          (by simpa [cc] using sub_pos.mpr (h368_neg t ht hneg))
        exact hev.mono fun _ h _ _ => sub_pos.mp h
      · exact Filter.Eventually.of_forall fun _ _ hn => absurd hn hneg
    · exact Filter.Eventually.of_forall fun _ h => absurd h ht
  have hev_ord : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ⟪x 2 - x 1, capView x 1 0 (cc ε)⟫ < ⟪x 5 - x 1, capView x 1 0 (cc ε)⟫ ∧
      ⟪x 5 - x 1, capView x 1 0 (cc ε)⟫ < ⟪x 0 - x 1, capView x 1 0 (cc ε)⟫ ∧
      ⟪x 0 - x 1, capView x 1 0 (cc ε)⟫ < ⟪x 6 - x 1, capView x 1 0 (cc ε)⟫ ∧
      ⟪x 6 - x 1, capView x 1 0 (cc ε)⟫ < ⟪x 3 - x 1, capView x 1 0 (cc ε)⟫ := by
    have e25 : ∀ᶠ ε : ℝ in 𝓝[>] 0,
        ⟪x 2 - x 1, capView x 1 0 (cc ε)⟫ < ⟪x 5 - x 1, capView x 1 0 (cc ε)⟫ := by
      have hcont : Continuous (fun ε : ℝ =>
          ⟪x 5 - x 1, capView x 1 0 (cc ε)⟫ - ⟪x 2 - x 1, capView x 1 0 (cc ε)⟫) := by
        unfold capView cc; fun_prop
      exact (SF.ev_pos hcont (by simpa [cc] using sub_pos.mpr h25)).mono fun _ h => sub_pos.mp h
    have e50 : ∀ᶠ ε : ℝ in 𝓝[>] 0,
        ⟪x 5 - x 1, capView x 1 0 (cc ε)⟫ < ⟪x 0 - x 1, capView x 1 0 (cc ε)⟫ := by
      have hcont : Continuous (fun ε : ℝ =>
          ⟪x 0 - x 1, capView x 1 0 (cc ε)⟫ - ⟪x 5 - x 1, capView x 1 0 (cc ε)⟫) := by
        unfold capView cc; fun_prop
      exact (SF.ev_pos hcont (by simpa [cc] using sub_pos.mpr h50)).mono fun _ h => sub_pos.mp h
    have e63 : ∀ᶠ ε : ℝ in 𝓝[>] 0,
        ⟪x 6 - x 1, capView x 1 0 (cc ε)⟫ < ⟪x 3 - x 1, capView x 1 0 (cc ε)⟫ := by
      have hcont : Continuous (fun ε : ℝ =>
          ⟪x 3 - x 1, capView x 1 0 (cc ε)⟫ - ⟪x 6 - x 1, capView x 1 0 (cc ε)⟫) := by
        unfold capView cc; fun_prop
      exact (SF.ev_pos hcont (by simpa [cc, h60] using sub_pos.mpr h03)).mono fun _ h => sub_pos.mp h
    have e06 : ∀ᶠ ε : ℝ in 𝓝[>] 0,
        ⟪x 0 - x 1, capView x 1 0 (cc ε)⟫ < ⟪x 6 - x 1, capView x 1 0 (cc ε)⟫ := by
      filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      have hdiff : ⟪x 6 - x 1, capView x 1 0 (cc ε)⟫ - ⟪x 0 - x 1, capView x 1 0 (cc ε)⟫ =
          ε * (sg * s60) := by
        have h1 : ⟪x 6 - x 1, capView x 1 0 (cc ε)⟫ - ⟪x 0 - x 1, capView x 1 0 (cc ε)⟫ =
            ⟪x 6 - x 0, capView x 1 0 (cc0 + sg * ε)⟫ := by
          have : x 6 - x 0 = (x 6 - x 1) - (x 0 - x 1) := by abel
          dsimp only [cc]
          rw [this, inner_sub_left (x 6 - x 1) (x 0 - x 1)]
        rw [h1]
        have h2 : capView x 1 0 (cc0 + sg * ε) =
            capView x 1 0 cc0 + (sg * ε) • (x 6 - x 1) := by
          dsimp only [capView]; module
        have h60' : ⟪x 6 - x 0, capView x 1 0 cc0⟫ = 0 := by
          have : x 6 - x 0 = (x 6 - x 1) - (x 0 - x 1) := by abel
          rw [this, inner_sub_left, h60, sub_self]
        rw [h2, inner_add_right, h60', zero_add, real_inner_smul_right]
        change (sg * ε) * s60 = ε * (sg * s60)
        ring
      linarith [mul_pos hε hsg_pos]
    exact e25.and (e50.and (e06.and e63))
  obtain ⟨ε, hw5_ε, hw3_ε, h368p_ε, h368n_ε, h25_ε, h50_ε, h06_ε, h63_ε⟩ :=
    (hev_w5.and (hev_w3.and (hev_368p.and (hev_368n.and hev_ord)))).exists
  let w := capView x 1 0 (cc ε)
  have hshift : ∀ i j : ZMod 5,
      ⟪x (wcRim i) - x 1, w⟫ < ⟪x (wcRim j) - x 1, w⟫ →
      ⟪x (wcRim i), w⟫ < ⟪x (wcRim j), w⟫ := by
    intro i j hij
    rw [inner_sub_left, inner_sub_left] at hij
    linarith
  have hz25 : ⟪x 2, w⟫ < ⟪x 5, w⟫ := hshift 2 1 h25_ε
  have hz50 : ⟪x 5, w⟫ < ⟪x 0, w⟫ := hshift 1 0 h50_ε
  have hz06 : ⟪x 0, w⟫ < ⟪x 6, w⟫ := hshift 0 4 h06_ε
  have hz63 : ⟪x 6, w⟫ < ⟪x 3, w⟫ := hshift 4 3 h63_ε
  have hdist : ∀ i j : ZMod 5, i ≠ j → ⟪x (wcRim i), w⟫ ≠ ⟪x (wcRim j), w⟫ := by
    intro i j hij h_eq
    fin_cases i <;> fin_cases j <;> first
      | exact absurd rfl hij
      | (dsimp [wcRim] at h_eq; linarith only [h_eq, hz25, hz50, hz06, hz63])
  have hrob : H21.RobUni (fun i => ⟪x (wcRim i), w⟫) := by
    let ord : ZMod 5 → ℕ := ![2, 1, 0, 4, 3]
    have hord_mono : ∀ i j : ZMod 5, ⟪x (wcRim i), w⟫ ≤ ⟪x (wcRim j), w⟫ → ord i ≤ ord j := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> dsimp [ord, wcRim] at hij ⊢ <;> first
        | omega
        | linarith only [hij, hz25, hz50, hz06, hz63]
    have hord_dec : ∀ (B b c d : Fin 5),
        0 < b.val → b.val < c.val → c.val < d.val →
        ¬ (ord (B + b) ≤ ord B ∧ ord (B + b) ≤ ord (B + c) ∧
           ord (B + d) ≤ ord B ∧ ord (B + d) ≤ ord (B + c)) := by
      decide
    intro B b c d hb hbc hcd hdk ⟨h1, h2, h3, h4⟩
    have hb5 : b < 5 := by omega
    have hc5 : c < 5 := by omega
    have hb_eq : (b : ZMod 5) = ⟨b, hb5⟩ := Fin.ext (Nat.mod_eq_of_lt hb5)
    have hc_eq : (c : ZMod 5) = ⟨c, hc5⟩ := Fin.ext (Nat.mod_eq_of_lt hc5)
    have hd_eq : (d : ZMod 5) = ⟨d, hdk⟩ := Fin.ext (Nat.mod_eq_of_lt hdk)
    refine hord_dec B ⟨b, hb5⟩ ⟨c, hc5⟩ ⟨d, hdk⟩ hb hbc hcd ⟨?_, ?_, ?_, ?_⟩
    · rw [← hb_eq]; exact hord_mono _ _ h1
    · rw [← hb_eq, ← hc_eq]; exact hord_mono _ _ h2
    · rw [← hd_eq]; exact hord_mono _ _ h3
    · rw [← hd_eq, ← hc_eq]; exact hord_mono _ _ h4
  exact wc_unimodal_lexAny F hC (cc ε) hw5_ε hw3_ε h368p_ε h368n_ε h368_zero hdist hrob

/-- **FN2 (`HoleLeaf` form).** -/
theorem holeLeaf_not_wc_unimodal {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F)
    (cc : ℝ) (hw5 : 1 / omega5 x < cc) (hw3 : cc < omega3 x)
    (h368_pos : ∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
      0 < ⟪F.N t, x 6 - x 1⟫ → -⟪F.N t, x 0 - x 1⟫ / ⟪F.N t, x 6 - x 1⟫ < cc)
    (h368_neg : ∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
      ⟪F.N t, x 6 - x 1⟫ < 0 → cc < -⟪F.N t, x 0 - x 1⟫ / ⟪F.N t, x 6 - x 1⟫)
    (h368_zero : ∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
      ⟪F.N t, x 6 - x 1⟫ = 0 → 0 < ⟪F.N t, x 0 - x 1⟫)
    (hdist : ∀ i j : ZMod 5, i ≠ j →
      ⟪x (wcRim i), capView x 1 0 cc⟫ ≠ ⟪x (wcRim j), capView x 1 0 cc⟫)
    (hrob : H21.RobUni (fun i => ⟪x (wcRim i), capView x 1 0 cc⟫)) :
    False :=
  hF.2.2.2.1 (wc_unimodal_lexAny F hF.1 cc hw5 hw3 h368_pos h368_neg h368_zero hdist hrob)

/-- **FN2 (`Hole24` form).** -/
theorem hole24_not_wc_unimodal {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : Hole24 x F)
    (cc : ℝ) (hw5 : 1 / omega5 x < cc) (hw3 : cc < omega3 x)
    (h368_pos : ∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
      0 < ⟪F.N t, x 6 - x 1⟫ → -⟪F.N t, x 0 - x 1⟫ / ⟪F.N t, x 6 - x 1⟫ < cc)
    (h368_neg : ∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
      ⟪F.N t, x 6 - x 1⟫ < 0 → cc < -⟪F.N t, x 0 - x 1⟫ / ⟪F.N t, x 6 - x 1⟫)
    (h368_zero : ∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
      ⟪F.N t, x 6 - x 1⟫ = 0 → 0 < ⟪F.N t, x 0 - x 1⟫)
    (hdist : ∀ i j : ZMod 5, i ≠ j →
      ⟪x (wcRim i), capView x 1 0 cc⟫ ≠ ⟪x (wcRim j), capView x 1 0 cc⟫)
    (hrob : H21.RobUni (fun i => ⟪x (wcRim i), capView x 1 0 cc⟫)) :
    False :=
  holeLeaf_not_wc_unimodal hF.1 cc hw5 hw3 h368_pos h368_neg h368_zero hdist hrob

/-- **FN1 (`HoleLeaf` form):** on a `HoleLeaf`, at `cc0` in the window with `z_6(cc0) = z_0(cc0)`,
the ordering `z_2 < z_5 < z_0 < z_3` fails. -/
theorem holeLeaf_not_wc_r60 {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F)
    (cc0 : ℝ) (hw5 : 1 / omega5 x < cc0) (hw3 : cc0 < omega3 x)
    (h368_pos : ∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
      0 < ⟪F.N t, x 6 - x 1⟫ → -⟪F.N t, x 0 - x 1⟫ / ⟪F.N t, x 6 - x 1⟫ < cc0)
    (h368_neg : ∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
      ⟪F.N t, x 6 - x 1⟫ < 0 → cc0 < -⟪F.N t, x 0 - x 1⟫ / ⟪F.N t, x 6 - x 1⟫)
    (h368_zero : ∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
      ⟪F.N t, x 6 - x 1⟫ = 0 → 0 < ⟪F.N t, x 0 - x 1⟫)
    (h60 : ⟪x 6 - x 1, capView x 1 0 cc0⟫ = ⟪x 0 - x 1, capView x 1 0 cc0⟫)
    (h25 : ⟪x 2 - x 1, capView x 1 0 cc0⟫ < ⟪x 5 - x 1, capView x 1 0 cc0⟫)
    (h50 : ⟪x 5 - x 1, capView x 1 0 cc0⟫ < ⟪x 0 - x 1, capView x 1 0 cc0⟫)
    (h03 : ⟪x 0 - x 1, capView x 1 0 cc0⟫ < ⟪x 3 - x 1, capView x 1 0 cc0⟫) :
    False :=
  hF.2.2.2.1 (wc_r60_lexAny F hF.1 cc0 hw5 hw3 h368_pos h368_neg h368_zero h60 h25 h50 h03)

/-- **FN1 (`Hole24` form).** -/
theorem hole24_not_wc_r60 {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : Hole24 x F)
    (cc0 : ℝ) (hw5 : 1 / omega5 x < cc0) (hw3 : cc0 < omega3 x)
    (h368_pos : ∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
      0 < ⟪F.N t, x 6 - x 1⟫ → -⟪F.N t, x 0 - x 1⟫ / ⟪F.N t, x 6 - x 1⟫ < cc0)
    (h368_neg : ∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
      ⟪F.N t, x 6 - x 1⟫ < 0 → cc0 < -⟪F.N t, x 0 - x 1⟫ / ⟪F.N t, x 6 - x 1⟫)
    (h368_zero : ∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
      ⟪F.N t, x 6 - x 1⟫ = 0 → 0 < ⟪F.N t, x 0 - x 1⟫)
    (h60 : ⟪x 6 - x 1, capView x 1 0 cc0⟫ = ⟪x 0 - x 1, capView x 1 0 cc0⟫)
    (h25 : ⟪x 2 - x 1, capView x 1 0 cc0⟫ < ⟪x 5 - x 1, capView x 1 0 cc0⟫)
    (h50 : ⟪x 5 - x 1, capView x 1 0 cc0⟫ < ⟪x 0 - x 1, capView x 1 0 cc0⟫)
    (h03 : ⟪x 0 - x 1, capView x 1 0 cc0⟫ < ⟪x 3 - x 1, capView x 1 0 cc0⟫) :
    False :=
  holeLeaf_not_wc_r60 hF.1 cc0 hw5 hw3 h368_pos h368_neg h368_zero h60 h25 h50 h03

end Minimality.T24.WC
