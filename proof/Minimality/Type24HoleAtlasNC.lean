module

public import Minimality.Type24NamedCover
public import Minimality.Type24HoleAtlasEP
public import Minimality.Type24HoleAtlasEPRev
public import Minimality.Type24WCOrder
public import Minimality.Type24WCLemmas

/-!
# Type 24: atlas of the named-view certificates (2026-11-27, task LEANATLAS)

No new mathematics: thin wrappers and an index.  Companion of nopert229 notes/TYPE24-HOLE-ATLAS.md
sections 2 and 3.11.

## Section A: lattice arrows of the named certificates (named certificate => generic leaf)

Proved here (each needs `CbarIn x` only; the twin forms are on `(x ∘ Sym.pi24, Sym.sym24 F)`):
`wcCert_edgePlaneAny`, `wcCertTwin_edgePlaneAny` (w_C), `famACert_edgePlaneAny`, `famACertTwin_edgePlaneAny`,
`famBCert_edgePlaneAny`, `famBCertTwin_edgePlaneAny` (T_0 floor families, limit form), `wdCert_edgePlaneAny`,
`wdCertTwin_edgePlaneAny`, `wd6Cert_edgePlaneAny`, `wd6CertTwin_edgePlaneAny` (w_D, w_D6 cells), `cA2Cert_edgePlaneAny`,
`cB2Cert_edgePlaneAny` (T_2 cells), `cA0Cert_edgePlaneAny`, `cB0Cert_edgePlaneAny` (interior T_0 cells), and the
disjunction `NamedEPCert` with `namedEPCert_edgePlaneAny`.

Arrows proved elsewhere (cited, not restated):
* Split family => `Gen.SplitAny`: `SF.splitFamily_splitAny`, `SF.splitFamilyTwin_splitAny` (needs `InI5`).
* Twins of the T_2 / T_0 cells => `EdgePlaneAny`: `TwoCone.cA2_edgePlaneAny_twin`, `cB2_edgePlaneAny_twin`,
  `cA0_edgePlaneAny_twin`, `cB0_edgePlaneAny_twin`.
* Order certificate (OC) => slope-window certificate (line separation): `Split.Slope.lineSep_of_depthOrder`,
  `lineSep_of_depthOrder_ties`, `lineSep_of_depthOrder_dir`; per cell `TwoCone.wdCertAt_of_oc`, `wd6CertAt_of_oc`,
  `cA2CertAt_of_oc`, `cB2CertAt_of_oc`, `cA0CertAt_of_oc`, `cB0CertAt_of_oc`; any open cell
  `TwoCone.cell_oc_edgePlaneAny`, `TwoCone.cell_lineSep_edgePlaneAny`.
* Strict-apex OC in an open cell => `Gen.SplitAny`: `SF.oc_splitAny_of_cell` (FW1).  NOT stated: "the named
  `*OCCertAt` => `Gen.SplitAny`" (the `OrderCertAt` form allows ties and has no strict apex; translating it is new
  work, listed in the atlas note).
* RobUni at an open- or closed-cell view => `Gen.LexAny`: `Atlas.closedCell_lexAny`, `Stmt.lexAny_of_openCellRob`,
  `WC.lexAny_of_cellAt_robUni`, `WC.wc_unimodal_lexAny`, `WC.wc_r60_lexAny`.
* 5-rim classification: `Atlas.rim5_classification` is a tautology (`AltCrown5` is defined as "neither RobUni nor
  SemiUnimodal5"); the content is `Atlas.holeLeaf_rim5_classification` (open-cell 5-rim views of a hole point are
  alternating crowns or semi-unimodal with the wrong apex).
* Generic leaves: `Gen.splitAny_edgePlaneAny`, `T24.LexEP.lexAny_edgePlaneAny`, `facetCellF_lexAny_or_edgePlane`,
  `T24.EPF.edgePlaneAny_of_triCell`, `T24.EPQP.quadFacetEP_all`, the Edge-Plane arrows of `Type24HoleAtlasEP`, and the
  equivalences `holeLeaf_iff_min`, `holeLeaf_iff_core3`, `holeLeaf_iff_core2`, `Stmt.holeChamber_iff_holeLeaf`.

## Section B: the named facts on the hole, under one roof

* `holeLeaf_namedCoverResidue : HoleLeaf x F → NamedCoverResidue x F` (the `HoleLeaf` form of
  `TwoCone.hole24_namedCoverResidue`; every named exclusion uses only `HoleLeaf`).
* `namedCoverResidue_noOC`: the residue also excludes every named order certificate (x and twin).
* `not_holeLeaf_of_namedCoverEmpty`, `openOB1_of_namedCoverEmpty`, `open24_of_namedCoverEmpty`:
  `NamedCoverEmpty` already gives the generic statement `Stmt.OpenOB1` (it rules out `HoleLeaf`, not only `Hole24`,
  on `OB1`), and with `Stmt.OpenSpecial` it gives `Stmt.Open24`.
* Other named hole facts (cited): `TwoCone.holeLeaf_not_T0_family` (T_0 family base EP, eventually in delta),
  `WC.holeLeaf_not_wc_unimodal`, `WC.holeLeaf_not_wc_r60`, `WC.wc_r60_z1_z3_nonneg`, `SF.holeLeaf_not_oc_cell`,
  `SF.holeLeaf_not_splitFamS6m` / `S6p` / `S4p`, the `holeLeaf_not_*_oc` forms of the six cells.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.RimCell Minimality.T24.HC Minimality.T24.SF
  Minimality.T24.TwoCone

namespace Minimality.T24.Atlas

variable {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x}

/-! ## Section A: named certificate => `Gen.EdgePlaneAny` -/

/-- `w_C` certificate => Edge-Plane view (`TwoCone.wc_edgePlaneAny`). -/
theorem wcCert_edgePlaneAny (hC : CbarIn x) {cc : ℝ} (h : WCCertAt x F cc) : Gen.EdgePlaneAny x := by
  rcases h with ⟨hw5, hw3, hp, hn, hz, hD0, hcn, sh, α', μ', hsh, hB, hO⟩
  exact wc_edgePlaneAny F hC cc hw5 hw3 hp hn hz hD0 hcn sh hsh α' μ' hB hO

/-- `π_24` twin `w_C` certificate => Edge-Plane view of `x` (`TwoCone.wc_edgePlaneAny_twin`). -/
theorem wcCertTwin_edgePlaneAny (hC : CbarIn x) {cb : ℝ} (h : WCCertAt (x ∘ Sym.pi24) (Sym.sym24 F) cb) :
    Gen.EdgePlaneAny x := by
  rcases h with ⟨hw5, hw3, hp, hn, hz, hD0, hcn, sh, α', μ', hsh, hB, hO⟩
  exact wc_edgePlaneAny_twin F hC cb hw5 hw3 hp hn hz hD0 hcn sh hsh α' μ' hB hO

/-- T_0 floor family A certificate => Edge-Plane view (`TwoCone.famA_edgePlaneAny`). -/
theorem famACert_edgePlaneAny (hC : CbarIn x) {x0 : ℝ} (h : FamACertAt x F x0) : Gen.EdgePlaneAny x := by
  rcases h with ⟨hI, h6, h8, hhid4, a, hD0, hcn, sh, α', μ', hsh, hB, hO⟩
  exact famA_edgePlaneAny F hC hI h6 h8 hhid4 a hD0 hcn sh hsh α' μ' hB hO

/-- Twin of `famACert_edgePlaneAny` (`TwoCone.famA_edgePlaneAny_twin`). -/
theorem famACertTwin_edgePlaneAny (hC : CbarIn x) {x0 : ℝ}
    (h : FamACertAt (x ∘ Sym.pi24) (Sym.sym24 F) x0) : Gen.EdgePlaneAny x := by
  rcases h with ⟨hI, h6, h8, hhid4, a, hD0, hcn, sh, α', μ', hsh, hB, hO⟩
  exact famA_edgePlaneAny_twin F hC hI h6 h8 hhid4 a hD0 hcn sh hsh α' μ' hB hO

/-- T_0 floor family B certificate => Edge-Plane view (`TwoCone.famB_edgePlaneAny`). -/
theorem famBCert_edgePlaneAny (hC : CbarIn x) {x0 : ℝ} (h : FamBCertAt x F x0) : Gen.EdgePlaneAny x := by
  rcases h with ⟨hI, h6, h8, a, hD0, hcn, sh, α', μ', hsh, hB, hO⟩
  exact famB_edgePlaneAny F hC hI h6 h8 a hD0 hcn sh hsh α' μ' hB hO

/-- Twin of `famBCert_edgePlaneAny` (`TwoCone.famB_edgePlaneAny_twin`). -/
theorem famBCertTwin_edgePlaneAny (hC : CbarIn x) {x0 : ℝ}
    (h : FamBCertAt (x ∘ Sym.pi24) (Sym.sym24 F) x0) : Gen.EdgePlaneAny x := by
  rcases h with ⟨hI, h6, h8, a, hD0, hcn, sh, α', μ', hsh, hB, hO⟩
  exact famB_edgePlaneAny_twin F hC hI h6 h8 a hD0 hcn sh hsh α' μ' hB hO

/-- `w_D` cell certificate => Edge-Plane view (`TwoCone.wd_edgePlaneAny`). -/
theorem wdCert_edgePlaneAny (hC : CbarIn x) {beta gamma : ℝ} (h : WDCertAt x F beta gamma) :
    Gen.EdgePlaneAny x := by
  rcases h with ⟨hb, hg, hr, h6, h8, a, hD0, hcn, sh, α', μ', hsh, hB, hO⟩
  exact wd_edgePlaneAny F hC hb hg hr h6 h8 a hD0 hcn sh hsh α' μ' hB hO

/-- Twin of `wdCert_edgePlaneAny` (`TwoCone.wd_edgePlaneAny_twin`). -/
theorem wdCertTwin_edgePlaneAny (hC : CbarIn x) {beta gamma : ℝ}
    (h : WDCertAt (x ∘ Sym.pi24) (Sym.sym24 F) beta gamma) : Gen.EdgePlaneAny x := by
  rcases h with ⟨hb, hg, hr, h6, h8, a, hD0, hcn, sh, α', μ', hsh, hB, hO⟩
  exact wd_edgePlaneAny_twin F hC hb hg hr h6 h8 a hD0 hcn sh hsh α' μ' hB hO

/-- `w_D6` cell certificate => Edge-Plane view (`TwoCone.wd6_edgePlaneAny`). -/
theorem wd6Cert_edgePlaneAny (hC : CbarIn x) {beta gamma : ℝ} (h : WD6CertAt x F beta gamma) :
    Gen.EdgePlaneAny x := by
  rcases h with ⟨hb, hg, hr, h6, h8, a, hD0, hcn, sh, α', μ', hsh, hB, hO⟩
  exact wd6_edgePlaneAny F hC hb hg hr h6 h8 a hD0 hcn sh hsh α' μ' hB hO

/-- Twin of `wd6Cert_edgePlaneAny` (`TwoCone.wd6_edgePlaneAny_twin`). -/
theorem wd6CertTwin_edgePlaneAny (hC : CbarIn x) {beta gamma : ℝ}
    (h : WD6CertAt (x ∘ Sym.pi24) (Sym.sym24 F) beta gamma) : Gen.EdgePlaneAny x := by
  rcases h with ⟨hb, hg, hr, h6, h8, a, hD0, hcn, sh, α', μ', hsh, hB, hO⟩
  exact wd6_edgePlaneAny_twin F hC hb hg hr h6 h8 a hD0 hcn sh hsh α' μ' hB hO

/-- T_2 cell `cA2` certificate => Edge-Plane view (`TwoCone.cA2_edgePlaneAny`). -/
theorem cA2Cert_edgePlaneAny (hC : CbarIn x) {beta gamma : ℝ} (h : CA2CertAt x F beta gamma) :
    Gen.EdgePlaneAny x := by
  rcases h with ⟨hb, hg, h2, h3, h6, h7, h8, a, hD0, hcn, sh, α', μ', hsh, hB, hO⟩
  exact cA2_edgePlaneAny F hC hb hg h2 h3 h6 h7 h8 a hD0 hcn sh hsh α' μ' hB hO

/-- T_2 cell `cB2` certificate => Edge-Plane view (`TwoCone.cB2_edgePlaneAny`). -/
theorem cB2Cert_edgePlaneAny (hC : CbarIn x) {beta gamma : ℝ} (h : CB2CertAt x F beta gamma) :
    Gen.EdgePlaneAny x := by
  rcases h with ⟨hb, hg, h2, h3, h6, h7, h8, a, hD0, hcn, sh, α', μ', hsh, hB, hO⟩
  exact cB2_edgePlaneAny F hC hb hg h2 h3 h6 h7 h8 a hD0 hcn sh hsh α' μ' hB hO

/-- Interior T_0 cell `cA0` certificate => Edge-Plane view (`TwoCone.cA0_edgePlaneAny`). -/
theorem cA0Cert_edgePlaneAny (hC : CbarIn x) {b gamma : ℝ} (h : CA0CertAt x F b gamma) :
    Gen.EdgePlaneAny x := by
  rcases h with ⟨hb, hg, hlo, hhi, hnC, hs6, a, hD0, hcn, sh, α', μ', hsh, hB, hO⟩
  exact cA0_edgePlaneAny F hC hb hg ⟨hlo, hhi, hnC, hs6⟩ a hD0 hcn sh hsh α' μ' hB hO

/-- Interior T_0 cell `cB0` certificate => Edge-Plane view (`TwoCone.cB0_edgePlaneAny`). -/
theorem cB0Cert_edgePlaneAny (hC : CbarIn x) {b gamma : ℝ} (h : CB0CertAt x F b gamma) :
    Gen.EdgePlaneAny x := by
  rcases h with ⟨hb, hg, hlo, hhi, hnC, hs6, a, hD0, hcn, sh, α', μ', hsh, hB, hO⟩
  exact cB0_edgePlaneAny F hC hb hg ⟨hlo, hhi, hnC, hs6⟩ a hD0 hcn sh hsh α' μ' hB hO

/-- Some named Edge-Plane certificate holds at `(x, F)` or at its `π_24` twin: the 18 slope-window certificates of
`NamedCoverResidue` (everything except the Split family, which is a `Gen.SplitAny` certificate). -/
def NamedEPCert (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  (∃ cc, WCCertAt x F cc) ∨ (∃ cb, WCCertAt (x ∘ Sym.pi24) (Sym.sym24 F) cb) ∨
  (∃ x0, FamACertAt x F x0) ∨ (∃ x0, FamBCertAt x F x0) ∨
  (∃ x0, FamACertAt (x ∘ Sym.pi24) (Sym.sym24 F) x0) ∨ (∃ x0, FamBCertAt (x ∘ Sym.pi24) (Sym.sym24 F) x0) ∨
  (∃ β γ, WDCertAt x F β γ) ∨ (∃ β γ, WDCertAt (x ∘ Sym.pi24) (Sym.sym24 F) β γ) ∨
  (∃ β γ, WD6CertAt x F β γ) ∨ (∃ β γ, WD6CertAt (x ∘ Sym.pi24) (Sym.sym24 F) β γ) ∨
  (∃ β γ, CA2CertAt x F β γ) ∨ (∃ β γ, CB2CertAt x F β γ) ∨
  (∃ β γ, CA2CertAt (x ∘ Sym.pi24) (Sym.sym24 F) β γ) ∨ (∃ β γ, CB2CertAt (x ∘ Sym.pi24) (Sym.sym24 F) β γ) ∨
  (∃ b γ, CA0CertAt x F b γ) ∨ (∃ b γ, CB0CertAt x F b γ) ∨
  (∃ b γ, CA0CertAt (x ∘ Sym.pi24) (Sym.sym24 F) b γ) ∨ (∃ b γ, CB0CertAt (x ∘ Sym.pi24) (Sym.sym24 F) b γ)

/-- Every named Edge-Plane certificate gives `Gen.EdgePlaneAny x` (on `CbarIn`). -/
theorem namedEPCert_edgePlaneAny (hC : CbarIn x) (h : NamedEPCert x F) : Gen.EdgePlaneAny x := by
  rcases h with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ |
    ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩
  · exact wcCert_edgePlaneAny hC h
  · exact wcCertTwin_edgePlaneAny hC h
  · exact famACert_edgePlaneAny hC h
  · exact famBCert_edgePlaneAny hC h
  · exact famACertTwin_edgePlaneAny hC h
  · exact famBCertTwin_edgePlaneAny hC h
  · exact wdCert_edgePlaneAny hC h
  · exact wdCertTwin_edgePlaneAny hC h
  · exact wd6Cert_edgePlaneAny hC h
  · exact wd6CertTwin_edgePlaneAny hC h
  · exact cA2Cert_edgePlaneAny hC h
  · exact cB2Cert_edgePlaneAny hC h
  · exact cA2_edgePlaneAny_twin F hC h
  · exact cB2_edgePlaneAny_twin F hC h
  · exact cA0Cert_edgePlaneAny hC h
  · exact cB0Cert_edgePlaneAny hC h
  · exact cA0_edgePlaneAny_twin F hC h
  · exact cB0_edgePlaneAny_twin F hC h

/-! ## Section B: the named facts on `HoleLeaf` -/

/-- **`HoleLeaf` form of `hole24_namedCoverResidue`**: a point of the generic hole has no named certificate.
Every named exclusion only uses `HoleLeaf`. -/
theorem holeLeaf_namedCoverResidue (h : HoleLeaf x F) : NamedCoverResidue x F := by
  have hC : CbarIn x := h.1
  refine ⟨hC, fun _ hI => holeLeaf_not_splitFamily F h hI, fun _ hI => holeLeaf_not_splitFamilyTwin F h hI,
    fun _ hc => holeLeaf_not_edgePlaneAny h (wcCert_edgePlaneAny hC hc),
    fun _ hc => holeLeaf_not_edgePlaneAny h (wcCertTwin_edgePlaneAny hC hc),
    fun _ hc => holeLeaf_not_famA h hc, fun _ hc => holeLeaf_not_famB h hc,
    fun _ hc => holeLeaf_not_famA_twin h hc, fun _ hc => holeLeaf_not_famB_twin h hc,
    fun _ _ hc => holeLeaf_not_wd h hc, fun _ _ hc => holeLeaf_not_wd_twin h hc,
    fun _ _ hc => holeLeaf_not_wd6 h hc, fun _ _ hc => holeLeaf_not_wd6_twin h hc,
    fun _ _ hc => holeLeaf_not_cA2 h hc, fun _ _ hc => holeLeaf_not_cB2 h hc,
    fun _ _ hc => holeLeaf_not_cA2_twin h hc, fun _ _ hc => holeLeaf_not_cB2_twin h hc,
    fun _ _ hc => holeLeaf_not_cA0 h hc, fun _ _ hc => holeLeaf_not_cB0 h hc,
    fun _ _ hc => holeLeaf_not_cA0_twin h hc, fun _ _ hc => holeLeaf_not_cB0_twin h hc⟩

/-- On `HoleLeaf` no named Edge-Plane certificate holds. -/
theorem holeLeaf_not_namedEPCert (h : HoleLeaf x F) : ¬ NamedEPCert x F := fun hc =>
  holeLeaf_not_edgePlaneAny h (namedEPCert_edgePlaneAny h.1 hc)

/-- The residue excludes every named ORDER certificate, on `x` and on the `π_24` twin (through the `*CertAt_of_oc`
arrows). -/
theorem namedCoverResidue_noOC (h : NamedCoverResidue x F) :
    (∀ β γ, ¬ WDOCCertAt x F β γ) ∧ (∀ β γ, ¬ WDOCCertAt (x ∘ Sym.pi24) (Sym.sym24 F) β γ) ∧
    (∀ β γ, ¬ WD6OCCertAt x F β γ) ∧ (∀ β γ, ¬ WD6OCCertAt (x ∘ Sym.pi24) (Sym.sym24 F) β γ) ∧
    (∀ β γ, ¬ CA2OCCertAt x F β γ) ∧ (∀ β γ, ¬ CB2OCCertAt x F β γ) ∧
    (∀ β γ, ¬ CA2OCCertAt (x ∘ Sym.pi24) (Sym.sym24 F) β γ) ∧
    (∀ β γ, ¬ CB2OCCertAt (x ∘ Sym.pi24) (Sym.sym24 F) β γ) ∧
    (∀ b γ, ¬ CA0OCCertAt x F b γ) ∧ (∀ b γ, ¬ CB0OCCertAt x F b γ) ∧
    (∀ b γ, ¬ CA0OCCertAt (x ∘ Sym.pi24) (Sym.sym24 F) b γ) ∧
    (∀ b γ, ¬ CB0OCCertAt (x ∘ Sym.pi24) (Sym.sym24 F) b γ) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hWD, hWDt, hWD6, hWD6t, hA2, hB2, hA2t, hB2t, hA0, hB0, hA0t, hB0t⟩ := h
  exact ⟨fun β γ hc => hWD β γ (wdCertAt_of_oc hc), fun β γ hc => hWDt β γ (wdCertAt_of_oc hc),
    fun β γ hc => hWD6 β γ (wd6CertAt_of_oc hc), fun β γ hc => hWD6t β γ (wd6CertAt_of_oc hc),
    fun β γ hc => hA2 β γ (cA2CertAt_of_oc hc), fun β γ hc => hB2 β γ (cB2CertAt_of_oc hc),
    fun β γ hc => hA2t β γ (cA2CertAt_of_oc hc), fun β γ hc => hB2t β γ (cB2CertAt_of_oc hc),
    fun b γ hc => hA0 b γ (cA0CertAt_of_oc hc), fun b γ hc => hB0 b γ (cB0CertAt_of_oc hc),
    fun b γ hc => hA0t b γ (cA0CertAt_of_oc hc), fun b γ hc => hB0t b γ (cB0CertAt_of_oc hc)⟩

/-- `NamedCoverEmpty` rules out the generic hole `HoleLeaf` on `OB1` (not only `Hole24`). -/
theorem not_holeLeaf_of_namedCoverEmpty (hN : NamedCoverEmpty) (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x)
    (hO : H24K.SAT.OB1 x) : ¬ HoleLeaf x F := fun h =>
  hN x F h.1 hO (holeLeaf_namedCoverResidue h)

/-- **`NamedCoverEmpty → OpenOB1`**: the open Prop of `Type24NamedCover` is at least as strong as the generic
statement `Stmt.OpenOB1` of `Type24HoleStatement`. -/
theorem openOB1_of_namedCoverEmpty (hN : NamedCoverEmpty) : Stmt.OpenOB1 := fun x F hO hF =>
  not_holeLeaf_of_namedCoverEmpty hN x F hO (Stmt.holeLeaf_of_holeFull hF)

/-- `NamedCoverEmpty` and `OpenSpecial` give `Stmt.Open24` (via `Stmt.open24_of_split`). -/
theorem open24_of_namedCoverEmpty (hN : NamedCoverEmpty) (hS : Stmt.OpenSpecial) : Stmt.Open24 :=
  Stmt.open24_of_split (openOB1_of_namedCoverEmpty hN) hS

end Minimality.T24.Atlas
