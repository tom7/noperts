module

public import Minimality.Type24T0Interior

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

open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.M4 Minimality.T24.HC Minimality.T24.SF Minimality.T24.DeepC

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

/-- **FT2:** `Hole24 x F` implies `NamedCoverResidue x F`. -/
theorem hole24_namedCoverResidue {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : Hole24 x F) :
    NamedCoverResidue x F := by
  have hres := hole24_twoConeResidue_FS2 hF
  rcases hres with ⟨⟨⟨⟨⟨⟨hC, hSF, hSFt, hWC, hWCt, _⟩, hFA, hFB⟩, hFAt, hFBt⟩, hWD, hWDt⟩,
    hWD6, hWD6t⟩, hA2, hB2, hA2t, hB2t⟩
  exact ⟨hC, hSF, hSFt, hWC, hWCt, hFA, hFB, hFAt, hFBt, hWD, hWDt, hWD6, hWD6t,
    hA2, hB2, hA2t, hB2t,
    fun _ _ h => hole24_not_cA0 hF h,
    fun _ _ h => hole24_not_cB0 hF h,
    fun _ _ h => hole24_not_cA0_twin hF h,
    fun _ _ h => hole24_not_cB0_twin hF h⟩

end Minimality.T24.TwoCone
