module

public import Minimality.Type24RayCT
public import Minimality.MonoCorner

/-!
# GAP14: two `T_0` edge-view region lemmas for the last type-24 lemma-gap points

The 14 points of nopert229 `data/hard/holekit/lemmagap_p0.lines` (no Lean region lemma after `P0Edge025`, no `cA2`
RobUni view) carry their certificates on two edges of the `T_0` cone (nopert229 FACENORM24.md "== GAP14 =="):

* `T0Edge012` (12 of the 14, the w1_7_3 pocket): Lemma CT (`apexCert_chordTop`, chord `6 → 1` of the `A0` rim
  `1.2.5.3.6`) at an edge view `r p = x₂ - x₀ + p (x₂ - x₁)`, `-1 < p ≤ 0`, on the `T_0` cone edge `γ = 0` where
  facet `012` is edge-on.  `RayCT02` is the corner `p = 0` of this edge; at the gap points facet `346` cuts the edge
  before `p = 0`, so the corner `x₂ - x₀` lies in `B0`, not `A0`, and the certificate lives on the open edge.  The
  antipodal letter `A*` does not depend on `p` (`det3 (x₆ - x₃) (x₂ - x₁) (r p) = (1 - c₃) det24`).
* `T0Edge126B0` (the 2 w5_25_2 points): `RobUni` on the `B0` rim `1.2.5.3.4.6` at an edge view
  `r s = x₂ - x₁ + s (x₆ - x₁)`, `s > 0` (facet `126` edge-on: the face of `T_0` at infinity), from three strictly
  monotone rim corners (`robUni_of_monoCorners`; at the gap points `z₁ < z₂ < z₅ < z₃ > z₄ > z₆`).

* `T2Edge012B2` (the cB2-twin RobUni views of 5 of the 14): three strictly monotone corners of the `B2` rim
  `0.5.3.4.6.1` at `x₀ - x₁ - β (x₂ - x₁)`, `β > 1`, on the `T_2` cone edge `γ = 0` (facet `012` edge-on).

All push the edge view into the open cell (`cellAt_eventually_of_wall`); the generic step for `RobUni` is
`lexAny_of_wall_monoCorners` (any cell, any wall view, `k - 3` strictly monotone corners).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace Topology
open Finset Filter
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.HC Minimality.T24.SF Minimality.T24.Stmt
  Minimality.T24.M4

namespace Minimality.T24.Cell

variable {x : Fin 7 → ℝ³}

/-! ## Generic: monotone corners at a wall view -/

/-- **Wall view with monotone corners**: a view `r` on the closed face of a cell `c` (every facet strictly of its
side, or `= 0` with `v` pointing to its side) at which at least `k - 3` rim corners are strictly monotone gives
`Gen.LexAny F` (the views `r + η v` are in the open cell and keep the monotone corners). -/
theorem lexAny_of_wall_monoCorners (F : S0xFac 9 s0x_S24 x) (c : Cell24) {r v : ℝ³}
    (hU : ∀ t ∈ c.U, 0 < ⟪F.N t, r⟫ ∨ (⟪F.N t, r⟫ = 0 ∧ 0 < ⟪F.N t, v⟫))
    (hD : ∀ t ∉ c.U, ⟪F.N t, r⟫ < 0 ∨ (⟪F.N t, r⟫ = 0 ∧ ⟪F.N t, v⟫ < 0))
    (S : Finset (ZMod c.k)) (hS : c.k - 3 ≤ S.card)
    (hm : ∀ i ∈ S, 0 < (⟪x (c.r i), r⟫ - ⟪x (c.r (i - 1)), r⟫) * (⟪x (c.r (i + 1)), r⟫ - ⟪x (c.r i), r⟫)) :
    Gen.LexAny F := by
  have evC := cellAt_eventually_of_wall F c.U hU hD
  have ez : ∀ (q : Fin 7) (η : ℝ), ⟪x q, r + η • v⟫ = ⟪x q, r⟫ + η * ⟪x q, v⟫ := fun q η => by
    rw [inner_add_right, real_inner_smul_right]
  have evM : ∀ᶠ η : ℝ in 𝓝[>] 0, ∀ i ∈ S,
      0 < (⟪x (c.r i), r + η • v⟫ - ⟪x (c.r (i - 1)), r + η • v⟫) *
        (⟪x (c.r (i + 1)), r + η • v⟫ - ⟪x (c.r i), r + η • v⟫) := by
    refine (Filter.eventually_all_finset _).2 fun i hi => ?_
    simp only [ez]
    have hc : Continuous fun η : ℝ =>
        (⟪x (c.r i), r⟫ + η * ⟪x (c.r i), v⟫ - (⟪x (c.r (i - 1)), r⟫ + η * ⟪x (c.r (i - 1)), v⟫)) *
          (⟪x (c.r (i + 1)), r⟫ + η * ⟪x (c.r (i + 1)), v⟫ - (⟪x (c.r i), r⟫ + η * ⟪x (c.r i), v⟫)) := by
      fun_prop
    exact Split.AcuteEdge.ev_pos hc (by simpa using hm i hi)
  obtain ⟨η, hcell, hmη⟩ := (evC.and evM).exists
  exact lexAny_of_cellRob F c hcell (GenPlus.robUni_of_monoCorners c.hk S hS hmη)

/-! ## `T0Edge012`: Lemma CT on the `012` edge of `T_0` (cell `A0`) -/

/-- The `012` edge view of `T_0`: `x₂ - x₀ + p (x₂ - x₁)` (`= capView x (-1) (1 + p) 0`). -/
noncomputable def t0e012 (x : Fin 7 → ℝ³) (p : ℝ) : ℝ³ := x 2 - x 0 + p • (x 2 - x 1)

/-- **T0Edge012:** `c₃ < 1` (the chord `6 → 1` is antipodal) and some `p ∈ (-1, 0]` such that at the edge view
`r = x₂ - x₀ + p (x₂ - x₁)` (facet `012` edge-on) the `A0` facets `235, 236` are in front and `0345, 046, 346`
behind (`016`, `025`, `126` are automatic), the chord ends `1, 6` are strictly below `2, 5, 3`, and `z₁ ≠ z₆`.
At `p = 0` this is `RayCT02` (`rayCT02_t0Edge012`). -/
def T0Edge012 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  oblX6 x 3 < 1 ∧ ∃ p : ℝ, -1 < p ∧ p ≤ 0 ∧
    0 < ⟪F.N 6, t0e012 x p⟫ ∧ 0 < ⟪F.N 7, t0e012 x p⟫ ∧
    ⟪F.N 3, t0e012 x p⟫ < 0 ∧ ⟪F.N 4, t0e012 x p⟫ < 0 ∧ ⟪F.N 8, t0e012 x p⟫ < 0 ∧
    max ⟪x 1, t0e012 x p⟫ ⟪x 6, t0e012 x p⟫ < ⟪x 2, t0e012 x p⟫ ∧
    max ⟪x 1, t0e012 x p⟫ ⟪x 6, t0e012 x p⟫ < ⟪x 5, t0e012 x p⟫ ∧
    max ⟪x 1, t0e012 x p⟫ ⟪x 6, t0e012 x p⟫ < ⟪x 3, t0e012 x p⟫ ∧
    ⟪x 1, t0e012 x p⟫ ≠ ⟪x 6, t0e012 x p⟫

/-- **T0Edge012 certificate:** some view `r + η (x₆ - x₀)` (small `η > 0`) lies in the open cell `A0` and carries
a strict-apex certificate (Lemma CT, `apexCert_chordTop`). -/
theorem t0Edge012_exists_apex {F : S0xFac 9 s0x_S24 x} (h : T0Edge012 x F) :
    ∃ w : ℝ³, CellAt F cellA0.U (univ \ cellA0.U) w ∧ ApexCert (fun i => x (cellA0.r i)) w := by
  obtain ⟨hc3, p, hp1, hp0, h6, h7, h3, h4, h8, h2, h5, h3z, hne⟩ := h
  rw [max_lt_iff] at h2 h5 h3z
  set r := t0e012 x p with hr
  have hNr : ∀ t : Fin 9, ⟪F.N t, r⟫ = (F.f t (x 2) - F.f t (x 0)) + p * (F.f t (x 2) - F.f t (x 1)) := by
    intro t
    rw [hr, t0e012, inner_add_right, real_inner_smul_right, F.inner_sub, F.inner_sub]
  have hU : ∀ t ∈ cellA0.U, 0 < ⟪F.N t, r⟫ ∨ (⟪F.N t, r⟫ = 0 ∧ 0 < ⟪F.N t, x 6 - x 0⟫) := by
    intro t ht
    have ht' : t ∈ ({5, 6, 7} : Finset (Fin 9)) := ht
    simp only [mem_insert, mem_singleton] at ht'
    left
    rcases ht' with rfl | rfl | rfl
    · rw [hNr, F.zero 5 2 (by decide), F.zero 5 1 (by decide)]
      linarith [F.neg 5 0 (by decide)]
    · exact h6
    · exact h7
  have hD : ∀ t ∉ cellA0.U, ⟪F.N t, r⟫ < 0 ∨ (⟪F.N t, r⟫ = 0 ∧ ⟪F.N t, x 6 - x 0⟫ < 0) := by
    intro t ht
    have ht' : t ∉ ({5, 6, 7} : Finset (Fin 9)) := ht
    have ht'' : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 8 := by revert t; decide
    rcases ht'' with rfl | rfl | rfl | rfl | rfl | rfl
    · right
      rw [hNr, F.inner_sub, F.zero 0 2 (by decide), F.zero 0 0 (by decide), F.zero 0 1 (by decide)]
      exact ⟨by ring, by linarith [F.neg 0 6 (by decide)]⟩
    · left
      rw [hNr, F.zero 1 0 (by decide), F.zero 1 1 (by decide)]
      have hf := F.neg 1 2 (by decide)
      nlinarith
    · rw [hNr, F.zero 2 2 (by decide), F.zero 2 0 (by decide)]
      have hf := F.neg 2 1 (by decide)
      rcases hp0.lt_or_eq with hp | hp
      · left; nlinarith
      · right
        rw [F.inner_sub, F.zero 2 0 (by decide), hp]
        exact ⟨by ring, by linarith [F.neg 2 6 (by decide)]⟩
    · exact Or.inl h3
    · exact Or.inl h4
    · exact Or.inl h8
  have evC := cellAt_eventually_of_wall F cellA0.U hU hD
  have ez : ∀ v : Fin 7, ∀ η : ℝ, ⟪x v, r + η • (x 6 - x 0)⟫ = ⟪x v, r⟫ + η * ⟪x v, x 6 - x 0⟫ :=
    fun v η => by rw [inner_add_right, real_inner_smul_right]
  have ed : ∀ a b : ℝ³, ∀ η : ℝ, Split.det3 a b (r + η • (x 6 - x 0)) =
      Split.det3 a b r + η * Split.det3 a b (x 6 - x 0) := fun a b η => by
    simp only [Split.det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  -- `A*` and the orientation on the edge do not depend on `p`
  have edr : ∀ a b : ℝ³, Split.det3 a b r = Split.det3 a b (x 2 - x 0) + p * Split.det3 a b (x 2 - x 1) :=
    fun a b => by
      rw [hr, t0e012]
      simp only [Split.det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have d0 : Split.det3 (x 6 - x 3) (x 2 - x 1) (x 2 - x 1) = 0 := by simp only [Split.det3]; ring
  have d1 : Split.det3 (x 2 - x 1) (x 6 - x 1) (x 2 - x 1) = 0 := by simp only [Split.det3]; ring
  obtain ⟨fA, fO⟩ := rayCT02_frame F
  have hdet : det24 x ≠ 0 := (type24OfFac F).det_ne
  have hAO0 : 0 < -(Split.det3 (x 6 - x 3) (x 2 - x 1) r * Split.det3 (x 2 - x 1) (x 6 - x 1) r) := by
    rw [edr, edr, d0, d1, fA, fO]
    have := mul_pos (sub_pos.mpr hc3) (sq_pos_of_ne_zero hdet)
    nlinarith
  have evAO : ∀ᶠ η : ℝ in 𝓝[>] 0, 0 < -((Split.det3 (x 6 - x 3) (x 2 - x 1) r +
      η * Split.det3 (x 6 - x 3) (x 2 - x 1) (x 6 - x 0)) *
      (Split.det3 (x 2 - x 1) (x 6 - x 1) r + η * Split.det3 (x 2 - x 1) (x 6 - x 1) (x 6 - x 0))) := by
    have hc : Continuous fun η : ℝ => -((Split.det3 (x 6 - x 3) (x 2 - x 1) r +
        η * Split.det3 (x 6 - x 3) (x 2 - x 1) (x 6 - x 0)) *
        (Split.det3 (x 2 - x 1) (x 6 - x 1) r + η * Split.det3 (x 2 - x 1) (x 6 - x 1) (x 6 - x 0))) := by
      fun_prop
    exact Split.AcuteEdge.ev_pos hc (by simpa using hAO0)
  obtain ⟨η, hcell, hAO, l12, l62, l15, l65, l13, l63, ln⟩ := (evC.and (evAO.and
    ((rayCT_ev_lt _ ⟪x 1, x 6 - x 0⟫ _ ⟪x 2, x 6 - x 0⟫ h2.1).and
    ((rayCT_ev_lt _ ⟪x 6, x 6 - x 0⟫ _ ⟪x 2, x 6 - x 0⟫ h2.2).and
    ((rayCT_ev_lt _ ⟪x 1, x 6 - x 0⟫ _ ⟪x 5, x 6 - x 0⟫ h5.1).and
    ((rayCT_ev_lt _ ⟪x 6, x 6 - x 0⟫ _ ⟪x 5, x 6 - x 0⟫ h5.2).and
    ((rayCT_ev_lt _ ⟪x 1, x 6 - x 0⟫ _ ⟪x 3, x 6 - x 0⟫ h3z.1).and
    ((rayCT_ev_lt _ ⟪x 6, x 6 - x 0⟫ _ ⟪x 3, x 6 - x 0⟫ h3z.2).and
    (rayCT_ev_ne _ ⟪x 1, x 6 - x 0⟫ _ ⟪x 6, x 6 - x 0⟫ hne))))))))).exists
  rw [← ed, ← ed] at hAO
  simp only [← ez] at l12 l62 l15 l65 l13 l63 ln
  set w := r + η • (x 6 - x 0) with hw
  refine ⟨w, hcell, ?_⟩
  obtain ⟨ρ, hρ, hrim⟩ := rimSign_of_cell F cellA0 hcell
  have hrim5 : ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      0 < ρ * Split.det3 (x (cA (i + 1)) - x (cA i)) (x (cA j) - x (cA i)) w := hrim
  have ev : cA 0 = 1 ∧ cA (0 + 1) = 2 ∧ cA 4 = 6 ∧ cA (4 - 1) = 3 ∧ cA (4 + 2) = 2 ∧ cA (4 + 1) = 1 ∧
      cA 1 = 2 ∧ cA 2 = 5 ∧ cA 3 = 3 := by decide
  have hO := hrim5 0 4 (by decide) (by decide)
  simp only [ev] at hO
  have hρ2 : ρ * ρ = 1 := by rcases hρ with rfl | rfl <;> norm_num
  refine apexCert_chordTop (k := 5) (by norm_num) (fun i => x (cA i)) w hρ hrim5 4 ?_ ?_ ?_
  · simp only [ev]
    have hm : (ρ * Split.det3 (x 6 - x 3) (x 2 - x 1) w) * (ρ * Split.det3 (x 2 - x 1) (x 6 - x 1) w) < 0 := by
      have e : (ρ * Split.det3 (x 6 - x 3) (x 2 - x 1) w) * (ρ * Split.det3 (x 2 - x 1) (x 6 - x 1) w) =
          Split.det3 (x 6 - x 3) (x 2 - x 1) w * Split.det3 (x 2 - x 1) (x 6 - x 1) w := by
        linear_combination (Split.det3 (x 6 - x 3) (x 2 - x 1) w * Split.det3 (x 2 - x 1) (x 6 - x 1) w) * hρ2
      rw [e]; linarith
    exact neg_of_mul_neg_left hm hO.le
  · intro j hj4 hj0
    have hj : j = 1 ∨ j = 2 ∨ j = 3 := by revert j; decide
    rcases hj with rfl | rfl | rfl
    · simp only [ev]; exact max_lt l62 l12
    · simp only [ev]; exact max_lt l65 l15
    · simp only [ev]; exact max_lt l63 l13
  · simp only [ev]; exact fun e => ln e.symm

/-- **T0Edge012 (Split leaf):** `T0Edge012 x F` gives `Gen.SplitAny F`. -/
theorem splitAny_of_t0Edge012 {F : S0xFac 9 s0x_S24 x} (h : T0Edge012 x F) : Gen.SplitAny F := by
  obtain ⟨w, hcell, hA⟩ := t0Edge012_exists_apex h
  exact splitAny_of_cellApex F cellA0 hcell hA

/-- **T0Edge012, `π_24` twin:** `T0Edge012 (x ∘ Sym.pi24) (Sym.sym24 F)` gives `Gen.SplitAny F`. -/
theorem splitAny_of_t0Edge012_twin {F : S0xFac 9 s0x_S24 x}
    (h : T0Edge012 (x ∘ Sym.pi24) (Sym.sym24 F)) : Gen.SplitAny F :=
  Sym.splitAny24_sym F (splitAny_of_t0Edge012 h)

/-- **T0Edge012 hole fact.** -/
theorem holeLeaf_not_t0Edge012 {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : ¬ T0Edge012 x F :=
  fun h => hF.2.2.2.2.1 (splitAny_of_t0Edge012 h)

/-- **T0Edge012 twin hole fact.** -/
theorem holeLeaf_not_t0Edge012_twin {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) :
    ¬ T0Edge012 (x ∘ Sym.pi24) (Sym.sym24 F) :=
  fun h => hF.2.2.2.2.1 (splitAny_of_t0Edge012_twin h)

/-- **`RayCT02` is the corner `p = 0` of `T0Edge012`** (the `A0` facets `235, 236, 0345, 046` are automatic at
`x₂ - x₀`). -/
theorem rayCT02_t0Edge012 {F : S0xFac 9 s0x_S24 x} (h : RayCT02 x F) : T0Edge012 x F := by
  obtain ⟨h8, hc3, h2, h5, h3, hne⟩ := h
  have e : t0e012 x 0 = x 2 - x 0 := by rw [t0e012, zero_smul, add_zero]
  refine ⟨hc3, 0, by norm_num, le_rfl, ?_⟩
  rw [e, F.inner_sub, F.inner_sub, F.inner_sub, F.inner_sub, F.inner_sub]
  refine ⟨?_, ?_, ?_, ?_, ?_, h2, h5, h3, hne⟩
  · rw [F.zero 6 2 (by decide)]; linarith [F.neg 6 0 (by decide)]
  · rw [F.zero 7 2 (by decide)]; linarith [F.neg 7 0 (by decide)]
  · rw [F.zero 3 0 (by decide)]; linarith [F.neg 3 2 (by decide)]
  · rw [F.zero 4 0 (by decide)]; linarith [F.neg 4 2 (by decide)]
  · linarith

/-! ## `T0Edge126B0`: monotone corners on the `126` edge of `T_0` (cell `B0`) -/

/-- The `126` edge view of `T_0` (the face at infinity): `x₂ - x₁ + s (x₆ - x₁)` (`= capView x 0 1 s`). -/
noncomputable def t0e126 (x : Fin 7 → ℝ³) (s : ℝ) : ℝ³ := x 2 - x 1 + s • (x 6 - x 1)

/-- **T0Edge126B0:** some `s > 0` such that at the edge view `r = x₂ - x₁ + s (x₆ - x₁)` (facet `126` edge-on) the
`B0` facets `235, 346` are in front and `025, 0345, 046` behind (`012`, `016`, `236` are automatic), and at least
three corners of the `B0` rim `cB = 1.2.5.3.4.6` are strictly monotone (e.g. `z₁ < z₂ < z₅ < z₃ > z₄ > z₆`). -/
def T0Edge126B0 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ s : ℝ, 0 < s ∧ 0 < ⟪F.N 6, t0e126 x s⟫ ∧ 0 < ⟪F.N 8, t0e126 x s⟫ ∧
    ⟪F.N 2, t0e126 x s⟫ < 0 ∧ ⟪F.N 3, t0e126 x s⟫ < 0 ∧ ⟪F.N 4, t0e126 x s⟫ < 0 ∧
    ∃ S : Finset (ZMod 6), 3 ≤ S.card ∧ ∀ i ∈ S,
      0 < (⟪x (cB i), t0e126 x s⟫ - ⟪x (cB (i - 1)), t0e126 x s⟫) *
        (⟪x (cB (i + 1)), t0e126 x s⟫ - ⟪x (cB i), t0e126 x s⟫)

/-- **T0Edge126B0 (Lex leaf):** `T0Edge126B0 x F` gives `Gen.LexAny F` (push `x₁ - x₀` into the open `B0`). -/
theorem lexAny_of_t0Edge126B0 {F : S0xFac 9 s0x_S24 x} (h : T0Edge126B0 x F) : Gen.LexAny F := by
  obtain ⟨s, hs, h6, h8, h2, h3, h4, S, hS, hm⟩ := h
  have hNr : ∀ t : Fin 9, ⟪F.N t, t0e126 x s⟫ =
      (F.f t (x 2) - F.f t (x 1)) + s * (F.f t (x 6) - F.f t (x 1)) := by
    intro t
    rw [t0e126, inner_add_right, real_inner_smul_right, F.inner_sub, F.inner_sub]
  refine lexAny_of_wall_monoCorners F cellB0 (v := x 1 - x 0) ?_ ?_ S hS hm
  · intro t ht
    have ht' : t ∈ ({5, 6, 7, 8} : Finset (Fin 9)) := ht
    simp only [mem_insert, mem_singleton] at ht'
    rcases ht' with rfl | rfl | rfl | rfl
    · right
      rw [hNr, F.inner_sub, F.zero 5 2 (by decide), F.zero 5 1 (by decide), F.zero 5 6 (by decide)]
      exact ⟨by ring, by linarith [F.neg 5 0 (by decide)]⟩
    · exact Or.inl h6
    · left
      rw [hNr, F.zero 7 2 (by decide), F.zero 7 6 (by decide)]
      have hf := F.neg 7 1 (by decide)
      nlinarith
    · exact Or.inl h8
  · intro t ht
    have ht' : t ∉ ({5, 6, 7, 8} : Finset (Fin 9)) := ht
    have ht'' : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 := by revert t; decide
    left
    rcases ht'' with rfl | rfl | rfl | rfl | rfl
    · rw [hNr, F.zero 0 2 (by decide), F.zero 0 1 (by decide)]
      have hf := F.neg 0 6 (by decide)
      nlinarith
    · rw [hNr, F.zero 1 1 (by decide), F.zero 1 6 (by decide)]
      linarith [F.neg 1 2 (by decide)]
    · exact h2
    · exact h3
    · exact h4

/-- **T0Edge126B0, `π_24` twin.** -/
theorem lexAny_of_t0Edge126B0_twin {F : S0xFac 9 s0x_S24 x}
    (h : T0Edge126B0 (x ∘ Sym.pi24) (Sym.sym24 F)) : Gen.LexAny F :=
  Sym.lexAny_sym F (lexAny_of_t0Edge126B0 h)

/-- **T0Edge126B0 hole fact.** -/
theorem holeLeaf_not_t0Edge126B0 {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : ¬ T0Edge126B0 x F :=
  fun h => hF.2.2.2.1 (lexAny_of_t0Edge126B0 h)

/-- **T0Edge126B0 twin hole fact.** -/
theorem holeLeaf_not_t0Edge126B0_twin {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) :
    ¬ T0Edge126B0 (x ∘ Sym.pi24) (Sym.sym24 F) :=
  fun h => hF.2.2.2.1 (lexAny_of_t0Edge126B0_twin h)

/-! ## `T2Edge012B2`: monotone corners on the `012` edge of `T_2` (cell `B2`) -/

/-- The `012` edge view of `T_2`: `x₀ - x₁ - β (x₂ - x₁)` (`= uT2 x β 0`). -/
noncomputable def t2e012 (x : Fin 7 → ℝ³) (beta : ℝ) : ℝ³ := x 0 - x 1 - beta • (x 2 - x 1)

/-- **T2Edge012B2:** some `β > 1` such that at the edge view `r = x₀ - x₁ - β (x₂ - x₁)` (facet `012` edge-on) the
`B2` facets `0345, 046` are in front and `235, 236, 346` behind (`016`, `025`, `126` are automatic from `β > 1`), and
at least three corners of the `B2` rim `cB2 = 0.5.3.4.6.1` are strictly monotone (e.g. `z₅ < z₃ < z₄ < z₆ < z₁ < z₀`,
the cB2-twin views of the GAP14 points). -/
def T2Edge012B2 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ beta : ℝ, 1 < beta ∧ 0 < ⟪F.N 3, t2e012 x beta⟫ ∧ 0 < ⟪F.N 4, t2e012 x beta⟫ ∧
    ⟪F.N 6, t2e012 x beta⟫ < 0 ∧ ⟪F.N 7, t2e012 x beta⟫ < 0 ∧ ⟪F.N 8, t2e012 x beta⟫ < 0 ∧
    ∃ S : Finset (ZMod 6), 3 ≤ S.card ∧ ∀ i ∈ S,
      0 < (⟪x (TwoCone.cB2 i), t2e012 x beta⟫ - ⟪x (TwoCone.cB2 (i - 1)), t2e012 x beta⟫) *
        (⟪x (TwoCone.cB2 (i + 1)), t2e012 x beta⟫ - ⟪x (TwoCone.cB2 i), t2e012 x beta⟫)

/-- **T2Edge012B2 (Lex leaf):** `T2Edge012B2 x F` gives `Gen.LexAny F` (push `x₆ - x₁` into the open `B2`). -/
theorem lexAny_of_t2Edge012B2 {F : S0xFac 9 s0x_S24 x} (h : T2Edge012B2 x F) : Gen.LexAny F := by
  obtain ⟨beta, hb, h3, h4, h6, h7, h8, S, hS, hm⟩ := h
  have hNr : ∀ t : Fin 9, ⟪F.N t, t2e012 x beta⟫ =
      (F.f t (x 0) - F.f t (x 1)) - beta * (F.f t (x 2) - F.f t (x 1)) := by
    intro t
    rw [t2e012, inner_sub_right, real_inner_smul_right, F.inner_sub, F.inner_sub]
  refine lexAny_of_wall_monoCorners F cellB2 (v := x 6 - x 1) ?_ ?_ S hS hm
  · intro t ht
    have ht' : t ∈ ({1, 3, 4} : Finset (Fin 9)) := ht
    simp only [mem_insert, mem_singleton] at ht'
    left
    rcases ht' with rfl | rfl | rfl
    · rw [hNr, F.zero 1 0 (by decide), F.zero 1 1 (by decide)]
      have hf := F.neg 1 2 (by decide)
      nlinarith
    · exact h3
    · exact h4
  · intro t ht
    have ht' : t ∉ ({1, 3, 4} : Finset (Fin 9)) := ht
    have ht'' : t = 0 ∨ t = 2 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 := by revert t; decide
    rcases ht'' with rfl | rfl | rfl | rfl | rfl | rfl
    · right
      rw [hNr, F.inner_sub, F.zero 0 0 (by decide), F.zero 0 1 (by decide), F.zero 0 2 (by decide)]
      exact ⟨by ring, by linarith [F.neg 0 6 (by decide)]⟩
    · left
      rw [hNr, F.zero 2 0 (by decide), F.zero 2 2 (by decide)]
      have hf := F.neg 2 1 (by decide)
      nlinarith
    · left
      rw [hNr, F.zero 5 1 (by decide), F.zero 5 2 (by decide)]
      linarith [F.neg 5 0 (by decide)]
    · exact Or.inl h6
    · exact Or.inl h7
    · exact Or.inl h8

/-- **T2Edge012B2, `π_24` twin.** -/
theorem lexAny_of_t2Edge012B2_twin {F : S0xFac 9 s0x_S24 x}
    (h : T2Edge012B2 (x ∘ Sym.pi24) (Sym.sym24 F)) : Gen.LexAny F :=
  Sym.lexAny_sym F (lexAny_of_t2Edge012B2 h)

/-- **T2Edge012B2 hole fact.** -/
theorem holeLeaf_not_t2Edge012B2 {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : ¬ T2Edge012B2 x F :=
  fun h => hF.2.2.2.1 (lexAny_of_t2Edge012B2 h)

/-- **T2Edge012B2 twin hole fact.** -/
theorem holeLeaf_not_t2Edge012B2_twin {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) :
    ¬ T2Edge012B2 (x ∘ Sym.pi24) (Sym.sym24 F) :=
  fun h => hF.2.2.2.1 (lexAny_of_t2Edge012B2_twin h)

end Minimality.T24.Cell
