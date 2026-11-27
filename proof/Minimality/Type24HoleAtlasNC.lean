module

public import Minimality.Type24NamedCoverRes
public import Minimality.Type24HoleAtlasEP
public import Minimality.Type24HoleAtlasEPRev
public import Minimality.Type24WCOrder
public import Minimality.Type24WCLemmas

/-!
# Type 24: atlas of the named-view certificates (2026-11-27, task LEANATLAS)

No new mathematics: thin wrappers and an index.  Companion of nopert229 notes/TYPE24-HOLE-ATLAS.md
sections 2 and 3.11.

## Section A: lattice arrows of the named certificates (named certificate => generic leaf)

Every named certificate is a cell certificate of `Cell.cells24`: `Cell.wcCert_cellCert`, `famACert_cellCert`,
`famBCert_cellCert`, `wdCert_cellCert`, `wd6Cert_cellCert`, `cA2Cert_cellCert`, `cB2Cert_cellCert`, `cA0Cert_cellCert`,
`cB0Cert_cellCert` (twin forms on `(x ∘ Sym.pi24, Sym.sym24 F)`), and a cell certificate is a generic leaf
(`Cell.cellCert_leaf`, `cellCert_twin_leaf`: `Gen.LexAny`, `Gen.SplitAny` or `Gen.EdgePlaneAny`).  The per-certificate
arrows `wcCert_edgePlaneAny`, ..., `cB0Cert_edgePlaneAny` and `namedEPCert_edgePlaneAny` of the first version of this
file were deleted (PRUNE24, nopert229 notes/TOOLBOX-LEAN.md): the target of a named certificate is now `LexAny`,
`SplitAny` or `EdgePlaneAny` by cell, not always `EdgePlaneAny`.  `NamedEPCert` (the 18 slope-window certificates) stays,
with `holeLeaf_not_namedEPCert`.

Arrows proved elsewhere (cited, not restated):
* Split family => `Gen.SplitAny`: `SF.splitFamily_splitAny`, `SF.splitFamilyTwin_splitAny` (needs `InI5`).
* Twins of the T_2 / T_0 cells => `EdgePlaneAny`: `TwoCone.cA2_edgePlaneAny_twin`, `cB2_edgePlaneAny_twin`
  (the interior T_0 twins are covered by `Cell.cA0Cert_cellCert` / `cB0Cert_cellCert` on the twin).
* Order certificate (OC) => slope-window certificate (line separation): `Split.Slope.lineSep_of_depthOrder`,
  `lineSep_of_depthOrder_ties`, `lineSep_of_depthOrder_dir`; per cell `TwoCone.wdCertAt_of_oc`, `wd6CertAt_of_oc`,
  `cA2CertAt_of_oc`, `cB2CertAt_of_oc`, `cA0CertAt_of_oc`, `cB0CertAt_of_oc`; any open cell
  `TwoCone.cell_lineSep_edgePlaneAny`, `Cell.epCert_of_orderCert`.
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
  `SF.holeLeaf_not_splitFamS6m` / `S6p` / `S4p`, `TwoCone.holeLeaf_not_cA2_oc` / `holeLeaf_not_cB2_oc`.
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

/-! ## Section B: the named facts on `HoleLeaf` -/

/-- **`HoleLeaf` form of `hole24_namedCoverResidue`**: a point of the generic hole has no named certificate.
Every named exclusion only uses `HoleLeaf`. -/
theorem holeLeaf_namedCoverResidue (h : HoleLeaf x F) : NamedCoverResidue x F :=
  Cell.namedCoverResidue_of_cellCoverResidue (Cell.holeLeaf_cellCoverResidue Cell.cells24 h)

/-- On `HoleLeaf` no named Edge-Plane certificate holds. -/
theorem holeLeaf_not_namedEPCert (h : HoleLeaf x F) : ¬ NamedEPCert x F := by
  obtain ⟨_, _, _, hWC, hWCt, hFA, hFB, hFAt, hFBt, hWD, hWDt, hWD6, hWD6t, hA2, hB2, hA2t, hB2t, hA0, hB0, hA0t,
    hB0t⟩ := holeLeaf_namedCoverResidue h
  rintro (⟨_, c⟩ | ⟨_, c⟩ | ⟨_, c⟩ | ⟨_, c⟩ | ⟨_, c⟩ | ⟨_, c⟩ | ⟨_, _, c⟩ | ⟨_, _, c⟩ | ⟨_, _, c⟩ | ⟨_, _, c⟩ |
    ⟨_, _, c⟩ | ⟨_, _, c⟩ | ⟨_, _, c⟩ | ⟨_, _, c⟩ | ⟨_, _, c⟩ | ⟨_, _, c⟩ | ⟨_, _, c⟩ | ⟨_, _, c⟩)
  exacts [hWC _ c, hWCt _ c, hFA _ c, hFB _ c, hFAt _ c, hFBt _ c, hWD _ _ c, hWDt _ _ c, hWD6 _ _ c, hWD6t _ _ c,
    hA2 _ _ c, hB2 _ _ c, hA2t _ _ c, hB2t _ _ c, hA0 _ _ c, hB0 _ _ c, hA0t _ _ c, hB0t _ _ c]

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
