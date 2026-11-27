module

public import Minimality.Type24Cell
public import Minimality.Type24OffOB1Res

/-!
# Type 24: wall persistence and the named cover as a sub-cover of `cells24` (task CELL24B, 2026-11-27)

Design: nopert229 notes/GENREV-NAMEDCOVER.md item 6.

* Generic: `cellAt_eventually_of_wall` (closed face of a cell + inward direction `v` => open cell along
  `w0 + η v`, small `η > 0`), `epCert_eventually` (Edge-Plane rows are finitely many strict inequalities,
  continuous where the base edge is not level), `cellCert_of_line`, **`cellCert_of_wall`** (a strict Edge-Plane
  certificate on a cell wall is a cell certificate of the adjacent open cell, given `Hid`).
* Instances: `wcCert_cellCert` (`w_C`, facet-`016` wall of `C`), `famACert_cellCert` / `famBCert_cellCert`
  (`FamA` / `FamB`, facet-`025` wall of `A0` / `B0`; the `hhid4` conjunct of `FamACertAt` is not used), and the
  `T_2` charts `cA2Cert_cellCert` / `cB2Cert_cellCert` (with `cellA2_hid` / `cellB2_hid`).
* `namedCoverResidue_of_cellCoverResidue`, **`cellCoverEmpty_of_namedCoverEmpty : NamedCoverEmpty →
  CellCoverEmpty cells24`** (the cell form is the weaker open Prop).
* Headline chain with the branch-tagged special piece: **`not_hole24_of_cellCoverEmpty_R`**,
  `open24_of_cellCoverEmpty_R` (`OSpec.OpenSpecialR`, Type24OffOB1Res.lean).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace Topology
open Finset Filter
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.HC Minimality.T24.SF Minimality.T24.Stmt

namespace Minimality.T24.Cell

section Generic
variable {n m : ℕ} {S : Fin m → Finset (Fin n)} {y : Fin n → ℝ³}

/-- **Wall to open cell**: on the closed face of a cell (every facet strictly of its side at `w0`, or `= 0` with
the direction `v` pointing to its side), the views `w0 + η v` are in the open cell for small `η > 0`. -/
theorem cellAt_eventually_of_wall (F : S0xFac m S y) (U : Finset (Fin m)) {w0 v : ℝ³}
    (hU : ∀ t ∈ U, 0 < ⟪F.N t, w0⟫ ∨ (⟪F.N t, w0⟫ = 0 ∧ 0 < ⟪F.N t, v⟫))
    (hD : ∀ t ∉ U, ⟪F.N t, w0⟫ < 0 ∨ (⟪F.N t, w0⟫ = 0 ∧ ⟪F.N t, v⟫ < 0)) :
    ∀ᶠ η : ℝ in 𝓝[>] 0, CellAt F U (univ \ U) (w0 + η • v) := by
  have e : ∀ t η, ⟪F.N t, w0 + η • v⟫ = ⟪F.N t, w0⟫ + η * ⟪F.N t, v⟫ := fun t η => by
    rw [inner_add_right, inner_smul_right]
  have hcont : ∀ t, Continuous fun η : ℝ => ⟪F.N t, w0⟫ + η * ⟪F.N t, v⟫ := fun t => by fun_prop
  have hall : ∀ᶠ η : ℝ in 𝓝[>] 0, ∀ t : Fin m,
      (t ∈ U → 0 < ⟪F.N t, w0 + η • v⟫) ∧ (t ∉ U → ⟪F.N t, w0 + η • v⟫ < 0) := by
    rw [eventually_all]; intro t
    by_cases ht : t ∈ U
    · rcases hU t ht with h | ⟨h0, hv⟩
      · exact (ev_pos (hcont t) (by simpa using h)).mono fun η h' => ⟨fun _ => by rw [e]; exact h', fun h => absurd ht h⟩
      · filter_upwards [self_mem_nhdsWithin] with η (hη : 0 < η)
        exact ⟨fun _ => by rw [e, h0, zero_add]; exact mul_pos hη hv, fun h => absurd ht h⟩
    · rcases hD t ht with h | ⟨h0, hv⟩
      · have hc : Continuous fun η : ℝ => -(⟪F.N t, w0⟫ + η * ⟪F.N t, v⟫) := (hcont t).neg
        exact (ev_pos hc (by simpa using h)).mono fun η h' =>
          ⟨fun h => absurd h ht, fun _ => by rw [e]; linarith⟩
      · filter_upwards [self_mem_nhdsWithin] with η (hη : 0 < η)
        exact ⟨fun h => absurd h ht, fun _ => by rw [e, h0, zero_add]; exact mul_neg_of_pos_of_neg hη hv⟩
  filter_upwards [hall] with η h
  exact ⟨fun t ht => (h t).1 ht, fun t ht => (h t).2 (mem_sdiff.mp ht).2⟩

end Generic

/-- **Edge-Plane rows persist**: an `EPCert` at `w0` holds at `w0 + η v` for small `η > 0` (finitely many strict
inequalities, continuous where the base edge is not level). -/
theorem epCert_eventually {k : ℕ} [NeZero k] (X : ZMod k → ℝ³) {w0 : ℝ³} (v : ℝ³) (h : EPCert X w0) :
    ∀ᶠ η : ℝ in 𝓝[>] 0, EPCert X (w0 + η • v) := by
  obtain ⟨a, s, α, μ, hD, hrows⟩ := h
  have hDc : Continuous fun η : ℝ => ⟪X (a + 1) - X a, w0 + η • v⟫ := by fun_prop
  have hD0 : ⟪X (a + 1) - X a, w0 + (0 : ℝ) • v⟫ ≠ 0 := by simpa using hD
  have evD : ∀ᶠ η : ℝ in 𝓝[>] 0, ⟪X (a + 1) - X a, w0 + η • v⟫ ≠ 0 :=
    (hDc.continuousAt.eventually (isOpen_ne.mem_nhds hD0)).filter_mono nhdsWithin_le_nhds
  have evR : ∀ᶠ η : ℝ in 𝓝[>] 0, Split.EV.EPRows X (w0 + η • v) a s α μ := by
    simp only [Split.EV.EPRows]
    rw [eventually_all]; intro i; rw [eventually_all]; intro j
    by_cases hij : i ≠ a ∧ (j = i ∨ j = i + 1)
    · have hcont : ContinuousAt (fun η : ℝ =>
          (α + μ * ⟪X j - X a, w0 + η • v⟫) * Split.det3 (X (i + 1) - X i) (X (a + 1) - X a) (w0 + η • v) +
            s * Split.edgePlaneSpin X (w0 + η • v) a i j) 0 := by
        unfold Split.edgePlaneSpin
        refine ContinuousAt.add (by simp only [Split.det3]; fun_prop)
          (ContinuousAt.mul continuousAt_const (ContinuousAt.add
            (by simp only [Split.det3, Split.cross_0, Split.cross_1, Split.cross_2]; fun_prop)
            (ContinuousAt.mul (ContinuousAt.div (by fun_prop) (by fun_prop) hD0)
              (by simp only [Split.det3, Split.cross_0, Split.cross_1, Split.cross_2]; fun_prop))))
      have h0 := hrows i j hij.1 hij.2
      have h0' : 0 < (α + μ * ⟪X j - X a, w0 + (0 : ℝ) • v⟫) *
          Split.det3 (X (i + 1) - X i) (X (a + 1) - X a) (w0 + (0 : ℝ) • v) +
            s * Split.edgePlaneSpin X (w0 + (0 : ℝ) • v) a i j := by simpa using h0
      exact ((hcont.eventually (lt_mem_nhds h0')).filter_mono nhdsWithin_le_nhds).mono
        fun η hη _ _ => hη
    · exact Eventually.of_forall fun η hi hj => absurd ⟨hi, hj⟩ hij
  filter_upwards [evD, evR] with η h1 h2
  exact ⟨a, s, α, μ, h1, h2⟩

variable {x : Fin 7 → ℝ³}

/-- **Wall persistence along a line** (`GENREV-NAMEDCOVER` item 6): Edge-Plane rows at `w0` and the open cell
along `w0 + η v` (small `η > 0`) give a cell certificate, on a cell with `Hid`. -/
theorem cellCert_of_line (F : S0xFac 9 s0x_S24 x) (c : Cell24) (hH : c.Hid) {w0 v : ℝ³}
    (hcell : ∀ᶠ η : ℝ in 𝓝[>] 0, CellAt F c.U (univ \ c.U) (w0 + η • v))
    (hE : EPCert (fun i => x (c.r i)) w0) : ∃ w, CellCert F c w := by
  obtain ⟨η, h1, h2⟩ := (hcell.and (epCert_eventually _ v hE)).exists
  exact ⟨_, cellCert_of_ep F hH h1 h2⟩

/-- **Wall persistence** (`cellCert_of_wall`): a strict Edge-Plane certificate at a view `w0` on the closed face
of a cell with `Hid` (facets of the wall are `0` at `w0`, and `v` points into the cell) is a cell certificate
nearby. -/
theorem cellCert_of_wall (F : S0xFac 9 s0x_S24 x) (c : Cell24) (hH : c.Hid) {w0 v : ℝ³}
    (hU : ∀ t ∈ c.U, 0 < ⟪F.N t, w0⟫ ∨ (⟪F.N t, w0⟫ = 0 ∧ 0 < ⟪F.N t, v⟫))
    (hD : ∀ t ∉ c.U, ⟪F.N t, w0⟫ < 0 ∨ (⟪F.N t, w0⟫ = 0 ∧ ⟪F.N t, v⟫ < 0))
    (hE : EPCert (fun i => x (c.r i)) w0) : ∃ w, CellCert F c w :=
  cellCert_of_line F c hH (cellAt_eventually_of_wall F c.U hU hD) hE

/-! ## Named wall and `T_2` certificates as cell certificates -/

/-- `w_C` (facet-`016` wall of `C`): `WCCertAt x F cc` gives a cell certificate of `C` near `capView x 1 0 cc`. -/
theorem wcCert_cellCert (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) {cc : ℝ} (h : TwoCone.WCCertAt x F cc) :
    ∃ w, CellCert F cellC w := by
  rcases h with ⟨hw5, hw3, hp, hn, hz, hD0, hcn, sh, α', μ', hsh, hB, hO⟩
  have hline : ∀ η : ℝ, capView x 1 η cc = capView x 1 0 cc + η • (x 2 - x 1) := fun η => by
    simp only [capView, zero_smul, add_zero]; abel
  have e : (univ \ cellC.U : Finset (Fin 9)) = {0, 1, 2, 5, 7} := by decide
  have hcell : ∀ᶠ η : ℝ in 𝓝[>] 0, CellAt F cellC.U (univ \ cellC.U) (capView x 1 0 cc + η • (x 2 - x 1)) := by
    filter_upwards [WC.wcCell_eventually F hC cc hw5 hw3 hp hn hz] with η hη
    rw [e, ← hline]; exact hη
  obtain ⟨s, α, μ, hrows⟩ := Split.Slope.epRows_of_lineSep (fun t => x (TwoCone.wcRim t)) (capView x 1 0 cc) 4
    hD0 hcn sh hsh α' μ' hB hO
  exact cellCert_of_line F cellC cellC_hid hcell ⟨4, s, α, μ, hD0, hrows⟩

/-- The `u_F` line: `uF x x0 δ = uB x x0 + δ • ((1 / ω5) • (x 6 - x 1))`. -/
theorem uF_line (x0 δ : ℝ) : uF x x0 δ = uB x x0 + δ • ((1 / omega5 x) • (x 6 - x 1)) := by
  simp only [uF, uB, capView, smul_smul]
  rw [show (1 - x0 + δ) / omega5 x = (1 - x0) / omega5 x + δ * (1 / omega5 x) by ring, add_smul]; abel

/-- At `uB x x0` facet `2` (`025`) is the wall: `= 0`, and the `u_F` direction is down. -/
theorem facet2_wall (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (x0 : ℝ) :
    ⟪F.N 2, uB x x0⟫ = 0 ∧ ⟪F.N 2, (1 / omega5 x) • (x 6 - x 1)⟫ < 0 := by
  have h0 := facet2_eq F hC x0 0
  have h1 := facet2_eq F hC x0 1
  rw [show capView x (-x0) 1 ((1 - x0 + 0) / omega5 x) = uB x x0 by simp [uB], zero_mul] at h0
  rw [show capView x (-x0) 1 ((1 - x0 + 1) / omega5 x) = uF x x0 1 from rfl, uF_line, inner_add_right,
    one_smul, h0, zero_add, one_mul] at h1
  exact ⟨h0, by rw [h1]; exact F.neg 2 1 (by decide)⟩

/-- `FamA` (facet-`025` wall of `A0`): `FamACertAt x F x0` gives a cell certificate of `A0` near `uB x x0`
(the `hhid4` conjunct is not needed: `cellA0_hid`). -/
theorem famACert_cellCert (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) {x0 : ℝ} (h : TwoCone.FamACertAt x F x0) :
    ∃ w, CellCert F cellA0 w := by
  rcases h with ⟨hI, h6, h8, -, a, hD0, hcn, sh, α', μ', hsh, hB, hO⟩
  have hb := facets_base F hC hI
  obtain ⟨hw2, hv2⟩ := facet2_wall F hC x0
  obtain ⟨s, α, μ, hrows⟩ := Split.Slope.epRows_of_lineSep (fun t => x (cA t)) (uB x x0) a hD0 hcn sh hsh α' μ' hB hO
  refine cellCert_of_wall (v := (1 / omega5 x) • (x 6 - x 1)) F cellA0 cellA0_hid (fun t ht => Or.inl ?_) (fun t ht => ?_) ⟨a, s, α, μ, hD0, hrows⟩
  · fin_cases t <;> simp [cellA0, TwoCone.U_A0] at ht
    · exact (hb 5 (by decide)).2.2.2.2.1 rfl
    · exact h6
    · exact (hb 7 (by decide)).2.2.2.2.2 rfl
  · fin_cases t <;> simp [cellA0, TwoCone.U_A0] at ht
    · exact Or.inl ((hb 0 (by decide)).1 rfl)
    · exact Or.inl ((hb 1 (by decide)).2.1 rfl)
    · exact Or.inr ⟨hw2, hv2⟩
    · exact Or.inl ((hb 3 (by decide)).2.2.1 rfl)
    · exact Or.inl ((hb 4 (by decide)).2.2.2.1 rfl)
    · exact Or.inl h8

/-- `FamB` (facet-`025` wall of `B0`): `FamBCertAt x F x0` gives a cell certificate of `B0` near `uB x x0`. -/
theorem famBCert_cellCert (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) {x0 : ℝ} (h : TwoCone.FamBCertAt x F x0) :
    ∃ w, CellCert F cellB0 w := by
  rcases h with ⟨hI, h6, h8, a, hD0, hcn, sh, α', μ', hsh, hB, hO⟩
  have hb := facets_base F hC hI
  obtain ⟨hw2, hv2⟩ := facet2_wall F hC x0
  obtain ⟨s, α, μ, hrows⟩ := Split.Slope.epRows_of_lineSep (fun t => x (cB t)) (uB x x0) a hD0 hcn sh hsh α' μ' hB hO
  refine cellCert_of_wall (v := (1 / omega5 x) • (x 6 - x 1)) F cellB0 cellB0_hid (fun t ht => Or.inl ?_) (fun t ht => ?_) ⟨a, s, α, μ, hD0, hrows⟩
  · fin_cases t <;> simp [cellB0, TwoCone.U_B0] at ht
    · exact (hb 5 (by decide)).2.2.2.2.1 rfl
    · exact h6
    · exact (hb 7 (by decide)).2.2.2.2.2 rfl
    · exact h8
  · fin_cases t <;> simp [cellB0, TwoCone.U_B0] at ht
    · exact Or.inl ((hb 0 (by decide)).1 rfl)
    · exact Or.inl ((hb 1 (by decide)).2.1 rfl)
    · exact Or.inr ⟨hw2, hv2⟩
    · exact Or.inl ((hb 3 (by decide)).2.2.1 rfl)
    · exact Or.inl ((hb 4 (by decide)).2.2.2.1 rfl)

/-- `T_2` chart: `CA2CertAt x F β γ` is a cell certificate of `A2` at `uT2 x β γ` (`cellA2_hid`). -/
theorem cA2Cert_cellCert (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) {beta gamma : ℝ}
    (h : TwoCone.CA2CertAt x F beta gamma) : CellCert F cellA2 (TwoCone.uT2 x beta gamma) := by
  rcases h with ⟨hb, hg, h2, h3, h6, h7, h8, a, hD0, hcn, sh, α', μ', hsh, hB, hO⟩
  obtain ⟨h1, h4, h0, h5⟩ := TwoCone.uT2_four_facets F hC hb hg
  obtain ⟨s, α, μ, hrows⟩ := Split.Slope.epRows_of_lineSep (fun t => x (TwoCone.cA2 t)) (TwoCone.uT2 x beta gamma)
    a hD0 hcn sh hsh α' μ' hB hO
  refine cellCert_of_ep F cellA2_hid ⟨fun t ht => ?_, fun t ht => ?_⟩ ⟨a, s, α, μ, hD0, hrows⟩
  · fin_cases t <;> simp [cellA2, TwoCone.U_A2] at ht <;> assumption
  · fin_cases t <;> simp [cellA2, TwoCone.U_A2] at ht <;> assumption

/-- `T_2` chart: `CB2CertAt x F β γ` is a cell certificate of `B2` at `uT2 x β γ` (`cellB2_hid`). -/
theorem cB2Cert_cellCert (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) {beta gamma : ℝ}
    (h : TwoCone.CB2CertAt x F beta gamma) : CellCert F cellB2 (TwoCone.uT2 x beta gamma) := by
  rcases h with ⟨hb, hg, h2, h3, h6, h7, h8, a, hD0, hcn, sh, α', μ', hsh, hB, hO⟩
  obtain ⟨h1, h4, h0, h5⟩ := TwoCone.uT2_four_facets F hC hb hg
  obtain ⟨s, α, μ, hrows⟩ := Split.Slope.epRows_of_lineSep (fun t => x (TwoCone.cB2 t)) (TwoCone.uT2 x beta gamma)
    a hD0 hcn sh hsh α' μ' hB hO
  refine cellCert_of_ep F cellB2_hid ⟨fun t ht => ?_, fun t ht => ?_⟩ ⟨a, s, α, μ, hD0, hrows⟩
  · fin_cases t <;> simp [cellB2, TwoCone.U_B2] at ht <;> assumption
  · fin_cases t <;> simp [cellB2, TwoCone.U_B2] at ht <;> assumption

/-! ## The named cover is a sub-cover of `cells24` -/

/-- **Every named certificate is a cell certificate of `cells24`, on the same side**: the cell-cover residue of
`cells24` lies in the named-cover residue. -/
theorem namedCoverResidue_of_cellCoverResidue {F : S0xFac 9 s0x_S24 x} (h : CellCoverResidue cells24 x F) :
    TwoCone.NamedCoverResidue x F := by
  obtain ⟨hC, hSF, hSFt, hc⟩ := h
  have hC' : CbarIn (x ∘ Sym.pi24) := (Sym.cbarIn_comp_pi24 x).2 hC
  have p : ∀ c ∈ cells24, ∀ w, ¬ CellCert F c w := fun c hc' w => (hc c hc' w).1
  have q : ∀ c ∈ cells24, ∀ w, ¬ CellCert (Sym.sym24 F) c w := fun c hc' w => (hc c hc' w).2
  have mC : cellC ∈ cells24 := by simp [cells24]
  have mD : cellD ∈ cells24 := by simp [cells24]
  have mD6 : cellD6 ∈ cells24 := by simp [cells24]
  have mA2 : cellA2 ∈ cells24 := by simp [cells24]
  have mB2 : cellB2 ∈ cells24 := by simp [cells24]
  have mA0 : cellA0 ∈ cells24 := by simp [cells24]
  have mB0 : cellB0 ∈ cells24 := by simp [cells24]
  refine ⟨hC, hSF, hSFt, fun cc hw => ?_, fun cb hw => ?_, fun x0 hw => ?_, fun x0 hw => ?_, fun x0 hw => ?_,
    fun x0 hw => ?_, fun b g hw => ?_, fun b g hw => ?_, fun b g hw => ?_, fun b g hw => ?_, fun b g hw => ?_,
    fun b g hw => ?_, fun b g hw => ?_, fun b g hw => ?_, fun b g hw => ?_, fun b g hw => ?_, fun b g hw => ?_,
    fun b g hw => ?_⟩
  · obtain ⟨w, h⟩ := wcCert_cellCert F hC hw; exact p _ mC w h
  · obtain ⟨w, h⟩ := wcCert_cellCert (Sym.sym24 F) hC' hw; exact q _ mC w h
  · obtain ⟨w, h⟩ := famACert_cellCert F hC hw; exact p _ mA0 w h
  · obtain ⟨w, h⟩ := famBCert_cellCert F hC hw; exact p _ mB0 w h
  · obtain ⟨w, h⟩ := famACert_cellCert (Sym.sym24 F) hC' hw; exact q _ mA0 w h
  · obtain ⟨w, h⟩ := famBCert_cellCert (Sym.sym24 F) hC' hw; exact q _ mB0 w h
  · exact p _ mD _ (wdCert_cellCert hC hw)
  · exact q _ mD _ (wdCert_cellCert hC' hw)
  · exact p _ mD6 _ (wd6Cert_cellCert hC hw)
  · exact q _ mD6 _ (wd6Cert_cellCert hC' hw)
  · exact p _ mA2 _ (cA2Cert_cellCert F hC hw)
  · exact p _ mB2 _ (cB2Cert_cellCert F hC hw)
  · exact q _ mA2 _ (cA2Cert_cellCert (Sym.sym24 F) hC' hw)
  · exact q _ mB2 _ (cB2Cert_cellCert (Sym.sym24 F) hC' hw)
  · exact p _ mA0 _ (cA0Cert_cellCert F hC hw)
  · exact p _ mB0 _ (cB0Cert_cellCert F hC hw)
  · exact q _ mA0 _ (cA0Cert_cellCert (Sym.sym24 F) hC' hw)
  · exact q _ mB0 _ (cB0Cert_cellCert (Sym.sym24 F) hC' hw)

/-- **`NamedCoverEmpty → CellCoverEmpty cells24`**: the cell form is the weaker open Prop, so earlier work on the
named cover stays connected (`cellCoverEmpty_mono` then covers every larger cell list). -/
theorem cellCoverEmpty_of_namedCoverEmpty (hN : TwoCone.NamedCoverEmpty) : CellCoverEmpty cells24 :=
  fun x F hC hO hres => hN x F hC hO (namedCoverResidue_of_cellCoverResidue hres)

/-! ## The chain with the branch-tagged special piece `OSpec.OpenSpecialR` -/

/-- **Chain (headline)**: `CellCoverEmpty L` and `OSpec.OpenSpecialR` rule out every `Hole24` point. -/
theorem not_hole24_of_cellCoverEmpty_R {L : List Cell24} (hN : CellCoverEmpty L) (hS : OSpec.OpenSpecialR) :
    ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), ¬ Hole24 x F := by
  intro x F hH
  by_cases hO : H24K.SAT.OB1 x
  · exact hN x F hH.1.1 hO (hole24_cellCoverResidue L hH)
  · exact OSpec.hole24_offOB1_R hH hO hS

/-- `CellCoverEmpty L` and `OSpec.OpenSpecialR` give `Stmt.Open24`. -/
theorem open24_of_cellCoverEmpty_R {L : List Cell24} (hN : CellCoverEmpty L) (hS : OSpec.OpenSpecialR) : Open24 :=
  OSpec.open24_of_split_R (openOB1_of_cellCoverEmpty hN) hS

end Minimality.T24.Cell
