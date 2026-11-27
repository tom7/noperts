module

public import Minimality.Type24T0Interior
public import Minimality.Type24HoleStatement

/-!
# Combined Named-Cover Residue (`FT2`)

Packages all named-cover hole exclusions (`SplitFamily`, `WCCertAt`, `FamACertAt`, `FamBCertAt`,
`WDCertAt`, `WD6CertAt`, `CA2CertAt`, `CB2CertAt`, `CA0CertAt`, `CB0CertAt`, on both `(x, F)`
and `(x ∘ Sym.pi24, Sym.sym24 F)`) into a single `Prop` `NamedCoverResidue x F`, proved by
`hole24_namedCoverResidue : Hole24 x F → NamedCoverResidue x F`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.M4 Minimality.T24.HC Minimality.T24.SF Minimality.T24.DeepC Minimality.T24.Stmt

namespace Minimality.T24.TwoCone

/-- **FT2:** Unified named-cover residue on `Hole24 x F` (both `(x, F)` and its `π_24` twin). -/
def NamedCoverResidue (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  CbarIn x ∧
  (∀ x0 : ℝ, InI5 x x0 → ¬ SplitFamily F x0) ∧
  (∀ x0 : ℝ, InI5 (x ∘ Sym.pi24) x0 → ¬ SplitFamilyTwin F x0) ∧
  (∀ cc : ℝ, ¬ WCCertAt x F cc) ∧
  (∀ cb : ℝ, ¬ WCCertAt (x ∘ Sym.pi24) (Sym.sym24 F) cb) ∧
  (∀ x0 : ℝ, ¬ FamACertAt x F x0) ∧
  (∀ x0 : ℝ, ¬ FamBCertAt x F x0) ∧
  (∀ x0 : ℝ, ¬ FamACertAt (x ∘ Sym.pi24) (Sym.sym24 F) x0) ∧
  (∀ x0 : ℝ, ¬ FamBCertAt (x ∘ Sym.pi24) (Sym.sym24 F) x0) ∧
  (∀ beta gamma : ℝ, ¬ WDCertAt x F beta gamma) ∧
  (∀ beta gamma : ℝ, ¬ WDCertAt (x ∘ Sym.pi24) (Sym.sym24 F) beta gamma) ∧
  (∀ beta gamma : ℝ, ¬ WD6CertAt x F beta gamma) ∧
  (∀ beta gamma : ℝ, ¬ WD6CertAt (x ∘ Sym.pi24) (Sym.sym24 F) beta gamma) ∧
  (∀ beta gamma : ℝ, ¬ CA2CertAt x F beta gamma) ∧
  (∀ beta gamma : ℝ, ¬ CB2CertAt x F beta gamma) ∧
  (∀ beta gamma : ℝ, ¬ CA2CertAt (x ∘ Sym.pi24) (Sym.sym24 F) beta gamma) ∧
  (∀ beta gamma : ℝ, ¬ CB2CertAt (x ∘ Sym.pi24) (Sym.sym24 F) beta gamma) ∧
  (∀ b gamma : ℝ, ¬ CA0CertAt x F b gamma) ∧
  (∀ b gamma : ℝ, ¬ CB0CertAt x F b gamma) ∧
  (∀ b gamma : ℝ, ¬ CA0CertAt (x ∘ Sym.pi24) (Sym.sym24 F) b gamma) ∧
  (∀ b gamma : ℝ, ¬ CB0CertAt (x ∘ Sym.pi24) (Sym.sym24 F) b gamma)

/-! ## FU1: Top-level reduction to `NamedCoverEmpty` and `OpenSpecial` -/

/-- **FU1 (`[OPEN]`):** The generic open part of P3: on `CbarIn` and `OB1`, the named-cover
residue is empty (no `Hole24` point can survive all named cover exclusions).  It implies `Stmt.OpenOB1`
(`Atlas.openOB1_of_namedCoverEmpty`, Type24HoleAtlasNC.lean).  Refuted sub-covers (EXACT, witnesses in nopert229
data/hard/holekit/): T_2 alone (`t2uni_p1_cube.lines`), `{w_C, T_2}` (`t2adv_union_fail15.lines`), one cone
`C(x1)` (`wcadv_noEPinC43.lines`); see notes/TYPE24-HOLE-ATLAS.md section 0. -/
def NamedCoverEmpty : Prop :=
  ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x),
    CbarIn x → H24K.SAT.OB1 x → ¬ NamedCoverResidue x F

/-! ## FU2–FU3: Carbon's revised 4-leaf tree (`A86 addendum to Q86 addendum`, §1)

Bookkeeping only.  The tree is judged a fitted cover (nopert229 notes/NAMED-COVER-STRATEGY.md), not the proof plan;
`Leaf4` was never used on 12097 hard points (Q86BREF). -/

/-- **Leaf 1 (`w_C` on `x` or `π_24` twin):** existence of a `WCCertAt` certificate on `(x, F)`
or its `π_24` twin.

Real-point satisfiability (FU3):
* Primary `WCCertAt`: `u54261` (Task FL, `cc = 0.47989`, `sh = -1`, `μ' = 24.75838442`,
  `α' = 3.5`, `max_blue = 3.463998133 < α' < 3.544454931 = min_orange`).
* `π_24` twin `WCCertAt`: `u16` in `noC566.lines` (Task FM, `cb = 0.410458356`, `sh = -1`,
  `μ' = -8.709161325`, `α' = -0.2095635485`, `max_blue = -0.2225411772 < α' < -0.1965859197 = min_orange`). -/
def Leaf1 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  (∃ cc : ℝ, WCCertAt x F cc) ∨ (∃ cb : ℝ, WCCertAt (x ∘ Sym.pi24) (Sym.sym24 F) cb)

/-- **Leaf 2 (`u_F` on `x` or `π_24` twin):** existence of a `FamACertAt` or `FamBCertAt`
certificate on `(x, F)` or its `π_24` twin.

Real-point satisfiability (FU3, `δ = 0` limit hypotheses):
* Primary `FamACertAt`: `w22_270_1` in `wcadv_noEPinC43.lines` (Task FP, `x₀ = 0.6195167181`,
  `a = 3`, `sh = 1`, `α = -1.141990304`, `μ = -22.40452558`, `margin = 0.01011575354`) and
  `w14_27_1` (Task FQ addendum, `x₀ = 0.00689484`, `a = 3`, `sh = -1`, `α = -2.04486`,
  `μ = -23.2513`, `margin = 0.000767033`).
* `FamBCertAt`: `u16` in `noC566.lines` on the `π_24` twin (Task FQ, `x₀ = 0.04086592484`,
  `a = 0`, `sh = 1`, `α = 28.09033783`, `μ = -94.21166332`, `margin = 0.2473152999`; primary
  `FamBCertAt` also hits 293/566 points in `noC566.lines`, Task FQ addendum). -/
def Leaf2 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  (∃ x0 : ℝ, FamACertAt x F x0 ∨ FamBCertAt x F x0) ∨
  (∃ x0 : ℝ, FamACertAt (x ∘ Sym.pi24) (Sym.sym24 F) x0 ∨
    FamBCertAt (x ∘ Sym.pi24) (Sym.sym24 F) x0)

/-- **Leaf 3 (`T_2` ungated on `x` or `π_24` twin):** existence of a `CA2CertAt` or `CB2CertAt`
certificate on `(x, F)` or its `π_24` twin.

Real-point satisfiability (FU3):
* `CA2CertAt`: `F~mrad_41002_8594` (line 7 of `q84ref_pool_miss39.lines`, Task FS,
  `(β, γ) = (0.8, 0.07)`, `a = 1`, `sh = -1`, `μ = 3.053421221`, `α = 1.158907471`,
  `margin = 0.04217616374`).
* `CB2CertAt`: complementary `γ < γ_8` branch (`(U_B2, D_B2)` cell) in the same `T_2` cone;
  satisfiable on a real point (Task FW0: `namedcov_gap31.lines`, lines 1 and 6, with `CB0CertAt`). -/
def Leaf3 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  (∃ beta gamma : ℝ, CA2CertAt x F beta gamma ∨ CB2CertAt x F beta gamma) ∨
  (∃ beta gamma : ℝ, CA2CertAt (x ∘ Sym.pi24) (Sym.sym24 F) beta gamma ∨
    CB2CertAt (x ∘ Sym.pi24) (Sym.sym24 F) beta gamma)

/-- **Leaf 4 (`u_R` at `b = 3/10`, cells `A0` / `B0`, `x` or `π_24` twin):** existence of a
`CA0CertAt` or `CB0CertAt` certificate at `b = 3/10` on `(x, F)` or its `π_24` twin.

Real-point satisfiability (FU3):
* `CA0CertAt`: `w54_161` in `twoadv_gap234.lines` (Task FT, `(b, γ) = (3/10, 16/25)`,
  `a = 2`, `sh = 1`, `μ = 9.413244071`, `α = -2.902317691`, `margin = 0.1983535724`, and
  `a = 4`, `sh = -1`, `μ = -4.676488455`, `α = -1.419789395`, `margin = 0.2956894851`).
* `CB0CertAt`: complementary `γ < γ_8` branch (`(U_B0, D_B0)` cell); satisfiable on a real point
  (Task FW0: `namedcov_gap31.lines`, lines 1 and 6, with `CB2CertAt`). -/
def Leaf4 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  (∃ gamma : ℝ, CA0CertAt x F (3 / 10) gamma ∨ CB0CertAt x F (3 / 10) gamma) ∨
  (∃ gamma : ℝ, CA0CertAt (x ∘ Sym.pi24) (Sym.sym24 F) (3 / 10) gamma ∨
    CB0CertAt (x ∘ Sym.pi24) (Sym.sym24 F) (3 / 10) gamma)

/-- **FU2:** Covering `CbarIn x ∧ OB1 x` by `Leaf1 ∨ Leaf2 ∨ Leaf3 ∨ Leaf4` implies
`NamedCoverEmpty`. -/
theorem namedCoverEmpty_of_leaves
    (h : ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x),
      CbarIn x → H24K.SAT.OB1 x → Leaf1 x F ∨ Leaf2 x F ∨ Leaf3 x F ∨ Leaf4 x F) :
    NamedCoverEmpty := by
  intro x F hC hO hres
  rcases hres with ⟨_, _, _, hWC, hWCt, hFA, hFB, hFAt, hFBt, _, _, _, _,
    hA2, hB2, hA2t, hB2t, hA0, hB0, hA0t, hB0t⟩
  rcases h x F hC hO with h1 | h2 | h3 | h4
  · rcases h1 with ⟨cc, hcc⟩ | ⟨cb, hcb⟩
    · exact hWC cc hcc
    · exact hWCt cb hcb
  · rcases h2 with ⟨x0, hx0 | hx0⟩ | ⟨x0, hx0 | hx0⟩
    · exact hFA x0 hx0
    · exact hFB x0 hx0
    · exact hFAt x0 hx0
    · exact hFBt x0 hx0
  · rcases h3 with ⟨β, γ, hγ | hγ⟩ | ⟨β, γ, hγ | hγ⟩
    · exact hA2 β γ hγ
    · exact hB2 β γ hγ
    · exact hA2t β γ hγ
    · exact hB2t β γ hγ
  · rcases h4 with ⟨γ, hγ | hγ⟩ | ⟨γ, hγ | hγ⟩
    · exact hA0 (3 / 10) γ hγ
    · exact hB0 (3 / 10) γ hγ
    · exact hA0t (3 / 10) γ hγ
    · exact hB0t (3 / 10) γ hγ

end Minimality.T24.TwoCone
