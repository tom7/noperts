module

public import Minimality.Type29Cert
public import Minimality.Type29Cover

@[expose] public section

/-!
# Type 29: the tests as certificates (`FEWER-FACES-PROOFS.md` §28, §18.2)

For each of the 32 named tests, `NF29.cert_<test>` is `NF29.rimThen_<test>` (Type29K3 / K4 /
Cover) with its rim certificate packaged as a `Cert29` (`Type29Cert.lean`): the labelled rim
at `c • view29 x v`, with the closed region facts (`Ex29`) where the limit needs them.  The tests
that need no tie hypothesis beyond a robustly unimodal rim keep `IsRobustUnimodal` (or the weak
non-equality) as hypothesis; the pairs and the cover glue supply it from `OneTie29`
(`Type29CertPairs.lean`, `Type29CertCover.lean`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Minimality

open scoped RealInnerProductSpace
open Finset

variable {x : Fin 7 → ℝ³}

/-- Certificate of `NF29.rimThen_k4_V` as a `Cert29` (`FEWER-FACES-PROOFS.md` §28, §18.2). -/
theorem NF29.cert_k4_V (N : NF29 x)
    (he0 : 0 < N.b0 + N.h0 - 1)
    (hh01 : 0 < -N.h0 + 1)
    (hc : 0 < N.a0 * N.b2 - N.a2 * N.b0 - N.a2 * N.h0 + N.a2)
    (hz : IsRobustUnimodal (quad ⟪x 5, N.vV⟫ ⟪x 1, N.vV⟫ ⟪x 2, N.vV⟫ ⟪x 3, N.vV⟫)) :
    Cert29 x := by
  obtain ⟨σ, hσ, h, -⟩ :=
    NF29.rimThen_k4_V N he0 hh01 hc hz
  exact Cert29.ofQuad 5 1 2 3 .none (by decide) trivial (N.namedAt_vV hσ) h

/-- Certificate of `NF29.rimThen_k4_Y` as a `Cert29` (`FEWER-FACES-PROOFS.md` §28, §18.2). -/
theorem NF29.cert_k4_Y (N : NF29 x)
    (ha2 : 0 < N.a2)
    (he0 : 0 < N.b0 + N.h0 - 1)
    (hs1 : 0 < -N.s + 1)
    (hbh2 : 0 < N.b2 + N.h2)
    (hz : IsRobustUnimodal (quint ⟪x 5, (x 5 - x 3)⟫ ⟪x 0, (x 5 - x 3)⟫ ⟪x 1, (x 5 - x 3)⟫ ⟪x 4,
            (x 5 - x 3)⟫ ⟪x 6, (x 5 - x 3)⟫)) :
    Cert29 x := by
  obtain ⟨σ, hσ, h, -⟩ :=
    NF29.rimThen_k4_Y N ha2 he0 hs1 hbh2 hz
  exact Cert29.ofQuint 5 0 1 4 6 (by decide) (namedAt_seg 3 5 hσ) h

/-- Certificate of `NF29.rimThen_k4_W` as a `Cert29` (`FEWER-FACES-PROOFS.md` §28, §18.2). -/
theorem NF29.cert_k4_W (N : NF29 x)
    (ha2 : 0 < N.a2)
    (hb0 : 0 < N.b0)
    (he0 : 0 < N.b0 + N.h0 - 1)
    (he2 : 0 < N.a2 + N.h2 - 1)
    (hs1 : 0 < -N.s + 1)
    (ht1 : 0 < -N.t + 1)
    (hbh2 : 0 < N.b2 + N.h2)
    (hh0g : 0 < N.h0 - 1)
    (hAh : 0 < -N.a0 - N.h0)
    (hh21 : 0 < -N.h2 + 1)
    (hc2 : 0 < -N.a0 * N.b2 - N.a0 * N.h2 + N.a2 * N.b0 + N.a2 * N.h0 - N.a2 - N.b0 - N.h0 + 1)
    (hz : IsRobustUnimodal
          (quad ⟪x 3, (x 3 - x 0)⟫ ⟪x 5, (x 3 - x 0)⟫ ⟪x 1, (x 3 - x 0)⟫ ⟪x 2, (x 3 - x 0)⟫)) :
    Cert29 x := by
  obtain ⟨σ, hσ, h, -⟩ :=
    NF29.rimThen_k4_W N ha2 hb0 he0 he2 hs1 ht1 hbh2 hh0g hAh hh21 hc2 hz
  exact Cert29.ofQuad 3 5 1 2 .none (by decide) trivial (namedAt_seg 0 3 hσ) h

/-- Certificate of `NF29.rimThen_k4_Z` as a `Cert29` (`FEWER-FACES-PROOFS.md` §28, §18.2). -/
theorem NF29.cert_k4_Z (N : NF29 x)
    (ha2 : 0 < N.a2)
    (hb0 : 0 < N.b0)
    (he0 : 0 < N.b0 + N.h0 - 1)
    (he2 : 0 < N.a2 + N.h2 - 1)
    (hs1 : 0 < -N.s + 1)
    (ht1 : 0 < -N.t + 1)
    (hbh2 : 0 < N.b2 + N.h2)
    (hh0g : 0 < N.h0 - 1)
    (hAh : 0 < -N.a0 - N.h0)
    (hh21 : 0 < -N.h2 + 1)
    (hc2 : 0 < -N.a0 * N.b2 - N.a0 * N.h2 + N.a2 * N.b0 + N.a2 * N.h0 - N.a2 - N.b0 - N.h0 + 1)
    (hz : IsRobustUnimodal (quad ⟪x 3, N.vZ⟫ ⟪x 0, N.vZ⟫ ⟪x 1, N.vZ⟫ ⟪x 4, N.vZ⟫)) :
    Cert29 x := by
  obtain ⟨σ, hσ, h, -⟩ :=
    NF29.rimThen_k4_Z N ha2 hb0 he0 he2 hs1 ht1 hbh2 hh0g hAh hh21 hc2 hz
  exact Cert29.ofQuad 3 0 1 4 .none (by decide) trivial (N.namedAt_vZ hσ) h

/-- Certificate of `NF29.rimThen_k3_T1` as a `Cert29` (`FEWER-FACES-PROOFS.md` §28, §18.2). -/
theorem NF29.cert_k3_T1 (N : NF29 x)
    (hb0 : 0 < N.b0)
    (hG5n : 0 < -N.a0 * N.h2 + N.a2 * N.h0 + N.a0 - N.a2)
    (hF45 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0)
    (hh20 : 0 < -N.h0 + N.h2)
    (hf : 0 < -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s - N.b0
          * N.h2 + N.b2 * N.h0)
    (hh21 : 0 < -N.h2 + 1)
    (hz : IsRobustUnimodal (quad ⟪x 1, N.vT1⟫ ⟪x 2, N.vT1⟫ ⟪x 3, N.vT1⟫ ⟪x 6, N.vT1⟫))
    (hx : Ex29.facts x .t1) :
    Cert29 x := by
  obtain ⟨σ, hσ, h, -⟩ :=
    NF29.rimThen_k3_T1 N hb0 hG5n hF45 hh20 hf hh21 hz
  exact Cert29.ofQuad 1 2 3 6 .t1 (by decide) hx (N.namedAt_vT1 hσ) h

/-- Certificate of `NF29.rimThen_k3_T2a` as a `Cert29` (`FEWER-FACES-PROOFS.md` §28, §18.2). -/
theorem NF29.cert_k3_T2a (N : NF29 x)
    (hA2 : 0 < -N.a2)
    (hh21 : 0 < -N.h2 + 1)
    (hsg : 0 < N.a2 * N.t - N.b2 * N.s + N.h2 * N.t - N.a2 - N.h2 - N.t + 1)
    (hc0 : 0 < N.a0 * N.b2 - N.a2 * N.b0 - N.a2 * N.h0 - N.b0 * N.h2 - N.h0 * N.h2 + N.a2 + N.b0 +
          N.h0 + N.h2 - 1)
    (hz : IsRobustUnimodal (quad ⟪x 4, N.vT2⟫ ⟪x 3, N.vT2⟫ ⟪x 0, N.vT2⟫ ⟪x 5, N.vT2⟫))
    (hx : Ex29.facts x .t2) :
    Cert29 x := by
  obtain ⟨σ, hσ, h, -⟩ :=
    NF29.rimThen_k3_T2a N hA2 hh21 hsg hc0 hz
  exact Cert29.ofQuad 4 3 0 5 .t2 (by decide) hx (N.namedAt_vT2 hσ) h

/-- Certificate of `NF29.rimThen_k3_T2b` as a `Cert29` (`FEWER-FACES-PROOFS.md` §28, §18.2). -/
theorem NF29.cert_k3_T2b (N : NF29 x)
    (hA2 : 0 < -N.a2)
    (hh21 : 0 < -N.h2 + 1)
    (hsg : 0 < N.a2 * N.t - N.b2 * N.s + N.h2 * N.t - N.a2 - N.h2 - N.t + 1)
    (hc0 : 0 < -N.a0 * N.b2 + N.a2 * N.b0 + N.a2 * N.h0 + N.b0 * N.h2 + N.h0 * N.h2 - N.a2 - N.b0 -
          N.h0 - N.h2 + 1)
    (hz : ¬ (⟪x 4, N.vT2⟫ = ⟪x 3, N.vT2⟫ ∧ ⟪x 3, N.vT2⟫ = ⟪x 5, N.vT2⟫))
    (hx : Ex29.facts x .t2) :
    Cert29 x := by
  obtain ⟨σ, hσ, h, -⟩ :=
    NF29.rimThen_k3_T2b N hA2 hh21 hsg hc0 hz
  exact Cert29.ofTri 4 3 5 .t2 (by decide) hx (N.namedAt_vT2 hσ) h

/-- Certificate of `NF29.rimThen_k3_T2c` as a `Cert29` (`FEWER-FACES-PROOFS.md` §28, §18.2). -/
theorem NF29.cert_k3_T2c (N : NF29 x)
    (hA2 : 0 < -N.a2)
    (hh01 : 0 < -N.h0 + 1)
    (hh21 : 0 < -N.h2 + 1)
    (hsg : 0 < -N.a2 * N.t + N.b2 * N.s - N.h2 * N.t + N.a2 + N.h2 + N.t - 1)
    (hx0 : 0 < -N.a0 * N.b2 + N.a2 * N.b0 + N.a2 * N.h0 + N.b0 * N.h2 + N.h0 * N.h2 - N.a2 - N.b0 -
          N.h0 - N.h2 + 1)
    (hz : ¬ (⟪x 4, N.vT2⟫ = ⟪x 3, N.vT2⟫ ∧ ⟪x 3, N.vT2⟫ = ⟪x 6, N.vT2⟫))
    (hx : Ex29.facts x .t2) :
    Cert29 x := by
  obtain ⟨σ, hσ, h, -⟩ :=
    NF29.rimThen_k3_T2c N hA2 hh01 hh21 hsg hx0 hz
  exact Cert29.ofTri 4 3 6 .t2 (by decide) hx (N.namedAt_vT2 hσ) h

/-- Certificate of `NF29.rimThen_k3_T1o` as a `Cert29` (`FEWER-FACES-PROOFS.md` §28, §18.2). -/
theorem NF29.cert_k3_T1o (N : NF29 x)
    (hh01 : 0 < -N.h0 + 1)
    (hF45 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0)
    (hh20 : 0 < -N.h0 + N.h2)
    (hth : 0 < -N.a2 * N.t + N.b2 * N.s)
    (hf : 0 < -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s - N.b0
          * N.h2 + N.b2 * N.h0)
    (hh2g : 0 < N.h2 - 1)
    (hz : IsRobustUnimodal (quad ⟪x 1, N.vT1⟫ ⟪x 2, N.vT1⟫ ⟪x 3, N.vT1⟫ ⟪x 6, N.vT1⟫))
    (hx : Ex29.facts x .t1o) :
    Cert29 x := by
  obtain ⟨σ, hσ, h, -⟩ :=
    NF29.rimThen_k3_T1o N hh01 hF45 hh20 hth hf hh2g hz
  exact Cert29.ofQuad 1 2 3 6 .t1o (by decide) hx (N.namedAt_vT1 hσ) h

/-- Certificate of `NF29.rimThen_k3_T3o` as a `Cert29` (`FEWER-FACES-PROOFS.md` §28, §18.2). -/
theorem NF29.cert_k3_T3o (N : NF29 x)
    (hh01 : 0 < -N.h0 + 1)
    (hh20 : 0 < -N.h0 + N.h2)
    (hth : 0 < -N.a2 * N.t + N.b2 * N.s)
    (hh2g : 0 < N.h2 - 1)
    (hh0F5 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.h0)
    (hF4h2 : 0 < N.b0 * N.h2 - N.b2 * N.h0 - N.h2)
    (hN : 0 < N.a0 * N.b2 - N.a2 * N.b0 - N.a2 * N.h0 + N.a2)
    (hal : 0 < -N.a0 * N.b0 * N.h2 + N.a0 * N.b2 * N.h0 - N.a0 * N.h0 * N.h2 - N.b0 * N.h0 * N.h2 -
          N.h0 ^ 2 * N.h2 + N.a0 * N.h2 + N.h0 * N.h2)
    (hhF5 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.h0 * N.h2)
    (hz : IsRobustUnimodal (quad ⟪x 1, N.vT3⟫ ⟪x 4, N.vT3⟫ ⟪x 3, N.vT3⟫ ⟪x 0, N.vT3⟫)) :
    Cert29 x := by
  obtain ⟨σ, hσ, h, -⟩ :=
    NF29.rimThen_k3_T3o N hh01 hh20 hth hh2g hh0F5 hF4h2 hN hal hhF5 hz
  exact Cert29.ofQuad 1 4 3 0 .none (by decide) trivial (N.namedAt_vT3 hσ) h

/-- Certificate of `NF29.rimThen_k3_T3p` as a `Cert29` (`FEWER-FACES-PROOFS.md` §28, §18.2). -/
theorem NF29.cert_k3_T3p (N : NF29 x)
    (hh2g : 0 < N.h2 - 1)
    (hh0F5 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.h0)
    (hh2F4 : 0 < -N.b0 * N.h2 + N.b2 * N.h0 + N.h2)
    (hq46 : 0 < N.a0 * N.h2 * N.t - N.b2 * N.h0 * N.s + N.h0 * N.h2 * N.t + N.b2 * N.h0)
    (hq65 : 0 < -N.a0 * N.h2 * N.t + N.b2 * N.h0 * N.s + N.h0 * N.h2 * N.s + N.a0 * N.h2)
    (hz : IsRobustUnimodal (quad ⟪x 1, N.vT3⟫ ⟪x 4, N.vT3⟫ ⟪x 6, N.vT3⟫ ⟪x 5, N.vT3⟫)) :
    Cert29 x := by
  obtain ⟨σ, hσ, h, -⟩ :=
    NF29.rimThen_k3_T3p N hh2g hh0F5 hh2F4 hq46 hq65 hz
  exact Cert29.ofQuad 1 4 6 5 .none (by decide) trivial (N.namedAt_vT3 hσ) h

/-- Certificate of `NF29.rimThen_k3_Xa` as a `Cert29` (`FEWER-FACES-PROOFS.md` §28, §18.2). -/
theorem NF29.cert_k3_Xa (N : NF29 x)
    (hh2F4 : 0 < -N.b0 * N.h2 + N.b2 * N.h0 + N.h2)
    (hXf : 0 < -N.a0 * N.t + N.b0 * N.s - N.h0 * N.t - N.b0 - N.s + 1)
    (hb01 : 0 < -N.b0 + 1)
    (hXa2 : 0 < -N.a0 * N.b2 + N.a2 * N.b0 + N.b0 * N.h2 - N.b2 * N.h0 - N.a2 - N.b0 - N.h2 + 1)
    (hz : IsRobustUnimodal
          (quad ⟪x 5, (x 5 - x 0)⟫ ⟪x 1, (x 5 - x 0)⟫ ⟪x 4, (x 5 - x 0)⟫ ⟪x 3, (x 5 - x 0)⟫)) :
    Cert29 x := by
  obtain ⟨σ, hσ, h, -⟩ :=
    NF29.rimThen_k3_Xa N hh2F4 hXf hb01 hXa2 hz
  exact Cert29.ofQuad 5 1 4 3 .none (by decide) trivial (namedAt_seg 0 5 hσ) h

/-- Certificate of `NF29.rimThen_k3_T2o` as a `Cert29` (`FEWER-FACES-PROOFS.md` §28, §18.2). -/
theorem NF29.cert_k3_T2o (N : NF29 x)
    (hV3 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2)
    (hh2g : 0 < N.h2 - 1)
    (hkap : 0 < -N.a2 - N.h2 + 1)
    (hsg : 0 < N.a2 * N.t - N.b2 * N.s + N.h2 * N.t - N.a2 - N.h2 - N.t + 1)
    (hz : IsRobustUnimodal (quad ⟪x 4, N.vT2⟫ ⟪x 2, N.vT2⟫ ⟪x 0, N.vT2⟫ ⟪x 5, N.vT2⟫))
    (hx : Ex29.facts x .t2o) :
    Cert29 x := by
  obtain ⟨σ, hσ, h, -⟩ :=
    NF29.rimThen_k3_T2o N hV3 hh2g hkap hsg hz
  exact Cert29.ofQuad 4 2 0 5 .t2o (by decide) hx (N.namedAt_vT2 hσ) h

/-- Certificate of `NF29.rimThen_k3_Y1p` as a `Cert29` (`FEWER-FACES-PROOFS.md` §28, §18.2). -/
theorem NF29.cert_k3_Y1p (N : NF29 x)
    (hb0 : 0 < N.b0)
    (hYs : 0 < N.h0 * N.s + N.a0)
    (hp56 : 0 < N.a2 * N.t - N.b2 * N.s - N.h2 * N.s - N.a2 + N.s)
    (hL36 : 0 < -N.a0 * N.h2 * N.t + N.b2 * N.h0 * N.s + N.h0 * N.h2 * N.s + N.a0 * N.h2)
    (hz : IsRobustUnimodal (quad ⟪x 1, N.vY1⟫ ⟪x 4, N.vY1⟫ ⟪x 6, N.vY1⟫ ⟪x 5, N.vY1⟫)) :
    Cert29 x := by
  obtain ⟨σ, hσ, h, -⟩ :=
    NF29.rimThen_k3_Y1p N hb0 hYs hp56 hL36 hz
  exact Cert29.ofQuad 1 4 6 5 .none (by decide) trivial (N.namedAt_vY1 hσ) h

/-- Certificate of `NF29.rimThen_k3_T3s` as a `Cert29` (`FEWER-FACES-PROOFS.md` §28, §18.2). -/
theorem NF29.cert_k3_T3s (N : NF29 x)
    (hh2g : 0 < N.h2 - 1)
    (hh0F5 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.h0)
    (hh2F4 : 0 < -N.b0 * N.h2 + N.b2 * N.h0 + N.h2)
    (hL36n : 0 < N.a0 * N.h2 * N.t - N.b2 * N.h0 * N.s - N.h0 * N.h2 * N.s - N.a0 * N.h2)
    (hW43 : 0 < -N.a0 * N.h2 * N.t + N.b2 * N.h0 * N.s - N.h0 * N.h2 * N.t - N.b2 * N.h0)
    (hAh0 : 0 < -N.a0 - N.h0)
    (hs1g : 0 < N.s - 1)
    (hz : IsRobustUnimodal (quad ⟪x 1, N.vT3⟫ ⟪x 4, N.vT3⟫ ⟪x 3, N.vT3⟫ ⟪x 5, N.vT3⟫)) :
    Cert29 x := by
  obtain ⟨σ, hσ, h, -⟩ :=
    NF29.rimThen_k3_T3s N hh2g hh0F5 hh2F4 hL36n hW43 hAh0 hs1g hz
  exact Cert29.ofQuad 1 4 3 5 .none (by decide) trivial (N.namedAt_vT3 hσ) h

/-- Certificate of `NF29.rimThen_k3_Y1q` as a `Cert29` (`FEWER-FACES-PROOFS.md` §28, §18.2). -/
theorem NF29.cert_k3_Y1q (N : NF29 x)
    (hb0 : 0 < N.b0)
    (hV3 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2)
    (hh01 : 0 < -N.h0 + 1)
    (hh2g : 0 < N.h2 - 1)
    (hkap : 0 < -N.a2 - N.h2 + 1)
    (hh0F5 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.h0)
    (hb01 : 0 < -N.b0 + 1)
    (hAs : 0 < -N.h0 * N.s - N.a0)
    (hL36 : 0 < -N.a0 * N.h2 * N.t + N.b2 * N.h0 * N.s + N.h0 * N.h2 * N.s + N.a0 * N.h2)
    (hAh0 : 0 < -N.a0 - N.h0)
    (hs1g : 0 < N.s - 1)
    (hz : IsRobustUnimodal (quad ⟪x 5, N.vY1⟫ ⟪x 1, N.vY1⟫ ⟪x 4, N.vY1⟫ ⟪x 3, N.vY1⟫)) :
    Cert29 x := by
  obtain ⟨σ, hσ, h, -⟩ :=
    NF29.rimThen_k3_Y1q N hb0 hV3 hh01 hh2g hkap hh0F5 hb01 hAs hL36 hAh0 hs1g hz
  exact Cert29.ofQuad 5 1 4 3 .none (by decide) trivial (N.namedAt_vY1 hσ) h

/-- Certificate of `NF29.rimThen_k3_Y2` as a `Cert29` (`FEWER-FACES-PROOFS.md` §28, §18.2). -/
theorem NF29.cert_k3_Y2 (N : NF29 x)
    (hb0 : 0 < N.b0)
    (hV3 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2)
    (hh01 : 0 < -N.h0 + 1)
    (hh20 : 0 < -N.h0 + N.h2)
    (hh2g : 0 < N.h2 - 1)
    (hb01 : 0 < -N.b0 + 1)
    (hW43 : 0 < -N.a0 * N.h2 * N.t + N.b2 * N.h0 * N.s - N.h0 * N.h2 * N.t - N.b2 * N.h0)
    (hs1g : 0 < N.s - 1)
    (hz : IsRobustUnimodal (quint ⟪x 6, (x 6 - x 4)⟫ ⟪x 3, (x 6 - x 4)⟫ ⟪x 2, (x 6 - x 4)⟫ ⟪x 0,
            (x 6 - x 4)⟫ ⟪x 5, (x 6 - x 4)⟫)) :
    Cert29 x := by
  obtain ⟨σ, hσ, h, -⟩ :=
    NF29.rimThen_k3_Y2 N hb0 hV3 hh01 hh20 hh2g hb01 hW43 hs1g hz
  exact Cert29.ofQuint 6 3 2 0 5 (by decide) (namedAt_seg 4 6 hσ) h

/-- Certificate of `NF29.rimThen_k3_C56`: the edge pair of Lemma E at `65` as a `Cert29`
(`FEWER-FACES-PROOFS.md` §28, §21.13). -/
theorem NF29.cert_k3_C56 (N : NF29 x)
    (hA2 : 0 < -N.a2)
    (hV3 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2)
    (hthn : 0 < N.a2 * N.t - N.b2 * N.s)
    (ht1 : 0 < -N.t + 1)
    (hfF5 : 0 < -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s +
          N.a0 * N.h2 - N.a2 * N.h0)
    (hgG5 : 0 < N.a0 * N.h2 * N.t - N.a2 * N.h0 * N.t - N.b0 * N.h2 * N.s + N.b2 * N.h0 * N.s - N.a0
          * N.h2 - N.a0 * N.t + N.a2 * N.h0 + N.a2 * N.t + N.b0 * N.s - N.b2 * N.s + N.a0 - N.a2)
    (hz : ¬ (⟪x 3, x 5 - x 6⟫ = ⟪x 2, x 5 - x 6⟫ ∧
      ⟪x 2, x 5 - x 6⟫ = ⟪x 1, x 5 - x 6⟫)) :
    Cert29 x := by
  obtain ⟨σ, hE, -⟩ :=
    NF29.rimThen_k3_C56 N hA2 hV3 hthn ht1 hfF5 hgG5 hz
  exact Cert29.ofEPair 6 5 3 1 2 (by decide) hE

/-- Certificate of `NF29.rimThen_k3_C14`: the edge pair of Lemma E at `41` as a `Cert29`
(`FEWER-FACES-PROOFS.md` §28, §21.13). -/
theorem NF29.cert_k3_C14 (N : NF29 x)
    (hb0 : 0 < N.b0)
    (hG4 : 0 < -N.b0 * N.h2 + N.b2 * N.h0 + N.b0 - N.b2)
    (hthn : 0 < N.a2 * N.t - N.b2 * N.s)
    (ht1g : 0 < N.t - 1)
    (he0n : 0 < -N.b0 - N.h0 + 1)
    (hz : ¬ (⟪x 6, x 1 - x 4⟫ = ⟪x 3, x 1 - x 4⟫ ∧
      ⟪x 3, x 1 - x 4⟫ = ⟪x 2, x 1 - x 4⟫)) :
    Cert29 x := by
  obtain ⟨σ, hE, -⟩ :=
    NF29.rimThen_k3_C14 N hb0 hG4 hthn ht1g he0n hz
  exact Cert29.ofEPair 4 1 6 2 3 (by decide) hE

/-- Certificate of `NF29.rimThen_k3_C46`: the edge pair of Lemma E at `46` as a `Cert29`
(`FEWER-FACES-PROOFS.md` §28, §21.13). -/
theorem NF29.cert_k3_C46 (N : NF29 x)
    (hb0 : 0 < N.b0)
    (hG4 : 0 < -N.b0 * N.h2 + N.b2 * N.h0 + N.b0 - N.b2)
    (hG5n : 0 < -N.a0 * N.h2 + N.a2 * N.h0 + N.a0 - N.a2)
    (hth : 0 < -N.a2 * N.t + N.b2 * N.s)
    (hfn : 0 < N.a0 * N.h2 * N.t - N.a2 * N.h0 * N.t - N.b0 * N.h2 * N.s + N.b2 * N.h0 * N.s + N.b0
          * N.h2 - N.b2 * N.h0)
    (hs1 : 0 < -N.s + 1)
    (hz : ¬ (⟪x 3, x 6 - x 4⟫ = ⟪x 2, x 6 - x 4⟫ ∧
      ⟪x 2, x 6 - x 4⟫ = ⟪x 1, x 6 - x 4⟫)) :
    Cert29 x := by
  obtain ⟨σ, hE, -⟩ :=
    NF29.rimThen_k3_C46 N hb0 hG4 hG5n hth hfn hs1 hz
  exact Cert29.ofEPair 4 6 3 1 2 (by decide) hE

/-- Certificate of `NF29.rimThen_k4_E05`: the edge pair of Lemma E at `05` as a `Cert29`
(`FEWER-FACES-PROOFS.md` §28, §21.13). -/
theorem NF29.cert_k4_E05 (N : NF29 x)
    (ha2 : 0 < N.a2)
    (hVn : 0 < -N.a0 * N.h2 + N.a2 * N.h0 - N.b0 * N.h2 + N.b2 * N.h0 - N.h0 + N.h2)
    (hq1 : 0 < N.b0 * N.h2 - N.b2 * N.h0 - N.h2)
    (hq2 : 0 < N.a0 * N.b2 - N.a2 * N.b0 - N.b0 * N.h2 + N.b2 * N.h0 + N.a2 + N.b0 + N.h2 - 1)
    (hz : ¬ (⟪x 1, x 5 - x 0⟫ = ⟪x 2, x 5 - x 0⟫ ∧
      ⟪x 2, x 5 - x 0⟫ = ⟪x 3, x 5 - x 0⟫)) :
    Cert29 x := by
  obtain ⟨σ, hE, -⟩ :=
    NF29.rimThen_k4_E05 N ha2 hVn hq1 hq2 hz
  exact Cert29.ofEPair 0 5 1 3 2 (by decide) hE

/-- Certificate of `NF29.rimThen_k4_E24`: the edge pair of Lemma E at `24` as a `Cert29`
(`FEWER-FACES-PROOFS.md` §28, §21.13). -/
theorem NF29.cert_k4_E24 (N : NF29 x)
    (hb0 : 0 < N.b0)
    (hq1 : 0 < -N.a0 * N.h2 + N.a2 * N.h0 - N.h0)
    (hq2 : 0 < N.a0 * N.b2 + N.a0 * N.h2 - N.a2 * N.b0 - N.a2 * N.h0 + N.a2 + N.b0 + N.h0 - 1)
    (hz : ¬ (⟪x 3, x 4 - x 2⟫ = ⟪x 0, x 4 - x 2⟫ ∧
      ⟪x 0, x 4 - x 2⟫ = ⟪x 1, x 4 - x 2⟫)) :
    Cert29 x := by
  obtain ⟨σ, hE, -⟩ :=
    NF29.rimThen_k4_E24 N hb0 hq1 hq2 hz
  exact Cert29.ofEPair 2 4 3 1 0 (by decide) hE

/-- Certificate of `NF29.rimThen_k4_E41s`: the edge pair of Lemma E at `41` as a `Cert29`
(`FEWER-FACES-PROOFS.md` §28, §21.13). -/
theorem NF29.cert_k4_E41s (N : NF29 x)
    (ha2 : 0 < N.a2)
    (hq1 : 0 < -N.b0 * N.h2 + N.b2 * N.h0 + N.b0 - N.b2)
    (hq2 : 0 < -N.b0 - N.h0 + 1)
    (ht1 : 0 < -N.t + 1)
    (hz : ¬ (⟪x 5, x 1 - x 4⟫ = ⟪x 3, x 1 - x 4⟫ ∧
      ⟪x 3, x 1 - x 4⟫ = ⟪x 2, x 1 - x 4⟫)) :
    Cert29 x := by
  obtain ⟨σ, hE, -⟩ :=
    NF29.rimThen_k4_E41s N ha2 hq1 hq2 ht1 hz
  exact Cert29.ofEPair 4 1 5 2 3 (by decide) hE

/-- Certificate of `NF29.rimThen_k4_E41l`: the edge pair of Lemma E at `41` as a `Cert29`
(`FEWER-FACES-PROOFS.md` §28, §21.13). -/
theorem NF29.cert_k4_E41l (N : NF29 x)
    (ha2 : 0 < N.a2)
    (hb0 : 0 < N.b0)
    (hq1 : 0 < -N.b0 * N.h2 + N.b2 * N.h0 + N.b0 - N.b2)
    (hq2 : 0 < -N.b0 - N.h0 + 1)
    (ht1g : 0 < N.t - 1)
    (hz : ¬ (⟪x 6, x 1 - x 4⟫ = ⟪x 3, x 1 - x 4⟫ ∧
      ⟪x 3, x 1 - x 4⟫ = ⟪x 2, x 1 - x 4⟫)) :
    Cert29 x := by
  obtain ⟨σ, hE, -⟩ :=
    NF29.rimThen_k4_E41l N ha2 hb0 hq1 hq2 ht1g hz
  exact Cert29.ofEPair 4 1 6 2 3 (by decide) hE

/-- Certificate of `NF29.rimThen_k4_E15`: the edge pair of Lemma E at `15` as a `Cert29`
(`FEWER-FACES-PROOFS.md` §28, §21.13). -/
theorem NF29.cert_k4_E15 (N : NF29 x)
    (hVn : 0 < -N.a0 * N.h2 + N.a2 * N.h0 - N.b0 * N.h2 + N.b2 * N.h0 - N.h0 + N.h2)
    (hq1 : 0 < -N.a0 * N.h2 + N.a2 * N.h0 + N.a0 - N.a2)
    (hq2 : 0 < N.a2 + N.h2 - 1)
    (hz : ¬ (⟪x 4, x 5 - x 1⟫ = ⟪x 2, x 5 - x 1⟫ ∧
      ⟪x 2, x 5 - x 1⟫ = ⟪x 0, x 5 - x 1⟫)) :
    Cert29 x := by
  obtain ⟨σ, hE, -⟩ :=
    NF29.rimThen_k4_E15 N hVn hq1 hq2 hz
  exact Cert29.ofEPair 1 5 4 0 2 (by decide) hE

/-- Certificate of `NF29.rimThen_k4_E51s`: the edge pair of Lemma E at `51` as a `Cert29`
(`FEWER-FACES-PROOFS.md` §28, §21.13). -/
theorem NF29.cert_k4_E51s (N : NF29 x)
    (hb0 : 0 < N.b0)
    (hq1 : 0 < N.a0 * N.h2 - N.a2 * N.h0 - N.a0 + N.a2)
    (hq2 : 0 < -N.a2 - N.h2 + 1)
    (hs1 : 0 < -N.s + 1)
    (hz : ¬ (⟪x 0, x 1 - x 5⟫ = ⟪x 3, x 1 - x 5⟫ ∧
      ⟪x 3, x 1 - x 5⟫ = ⟪x 4, x 1 - x 5⟫)) :
    Cert29 x := by
  obtain ⟨σ, hE, -⟩ :=
    NF29.rimThen_k4_E51s N hb0 hq1 hq2 hs1 hz
  exact Cert29.ofEPair 5 1 0 4 3 (by decide) hE

/-- Certificate of `NF29.rimThen_k4_E51l`: the edge pair of Lemma E at `51` as a `Cert29`
(`FEWER-FACES-PROOFS.md` §28, §21.13). -/
theorem NF29.cert_k4_E51l (N : NF29 x)
    (ha2 : 0 < N.a2)
    (hb0 : 0 < N.b0)
    (hq1 : 0 < N.a0 * N.h2 - N.a2 * N.h0 - N.a0 + N.a2)
    (hq2 : 0 < -N.a2 - N.h2 + 1)
    (hs1g : 0 < N.s - 1)
    (hz : ¬ (⟪x 0, x 1 - x 5⟫ = ⟪x 3, x 1 - x 5⟫ ∧
      ⟪x 3, x 1 - x 5⟫ = ⟪x 6, x 1 - x 5⟫)) :
    Cert29 x := by
  obtain ⟨σ, hE, -⟩ :=
    NF29.rimThen_k4_E51l N ha2 hb0 hq1 hq2 hs1g hz
  exact Cert29.ofEPair 5 1 0 6 3 (by decide) hE

/-- Certificate of `NF29.rimThen_k3_E03`: the edge pair of Lemma E at `03` as a `Cert29`
(`FEWER-FACES-PROOFS.md` §28, §21.13). -/
theorem NF29.cert_k3_E03 (N : NF29 x)
    (hA2 : 0 < -N.a2)
    (hq1 : 0 < N.b0 * N.h2 - N.b2 * N.h0 + N.b2)
    (hq2 : 0 < N.h0 - 1)
    (hz : ¬ (⟪x 5, x 3 - x 0⟫ = ⟪x 1, x 3 - x 0⟫ ∧
      ⟪x 1, x 3 - x 0⟫ = ⟪x 2, x 3 - x 0⟫)) :
    Cert29 x := by
  obtain ⟨σ, hE, -⟩ :=
    NF29.rimThen_k3_E03 N hA2 hq1 hq2 hz
  exact Cert29.ofEPair 0 3 5 2 1 (by decide) hE

/-- Certificate of `NF29.rimThen_k3_E24`: the edge pair of Lemma E at `24` as a `Cert29`
(`FEWER-FACES-PROOFS.md` §28, §21.13). -/
theorem NF29.cert_k3_E24 (N : NF29 x)
    (hb0 : 0 < N.b0)
    (hV3 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2)
    (hq1 : 0 < -N.a0 * N.h2 + N.a2 * N.h0 - N.h0)
    (hq2 : 0 < N.a0 * N.b2 + N.a0 * N.h2 - N.a2 * N.b0 - N.a2 * N.h0 + N.a2 + N.b0 + N.h0 - 1)
    (hz : ¬ (⟪x 3, x 4 - x 2⟫ = ⟪x 0, x 4 - x 2⟫ ∧
      ⟪x 0, x 4 - x 2⟫ = ⟪x 1, x 4 - x 2⟫)) :
    Cert29 x := by
  obtain ⟨σ, hE, -⟩ :=
    NF29.rimThen_k3_E24 N hb0 hV3 hq1 hq2 hz
  exact Cert29.ofEPair 2 4 3 1 0 (by decide) hE

/-- Certificate of `NF29.rimThen_k3_E14`: the edge pair of Lemma E at `14` as a `Cert29`
(`FEWER-FACES-PROOFS.md` §28, §21.13). -/
theorem NF29.cert_k3_E14 (N : NF29 x)
    (hV3 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2)
    (hq1 : 0 < N.b0 * N.h2 - N.b2 * N.h0 - N.b0 + N.b2)
    (hq2 : 0 < N.b0 + N.h0 - 1)
    (hz : ¬ (⟪x 2, x 4 - x 1⟫ = ⟪x 0, x 4 - x 1⟫ ∧
      ⟪x 0, x 4 - x 1⟫ = ⟪x 5, x 4 - x 1⟫)) :
    Cert29 x := by
  obtain ⟨σ, hE, -⟩ :=
    NF29.rimThen_k3_E14 N hV3 hq1 hq2 hz
  exact Cert29.ofEPair 1 4 2 5 0 (by decide) hE

/-- Certificate of `NF29.rimThen_k3_E51s`: the edge pair of Lemma E at `51` as a `Cert29`
(`FEWER-FACES-PROOFS.md` §28, §21.13). -/
theorem NF29.cert_k3_E51s (N : NF29 x)
    (hb0 : 0 < N.b0)
    (hq1 : 0 < N.a0 * N.h2 - N.a2 * N.h0 - N.a0 + N.a2)
    (hq2 : 0 < -N.a2 - N.h2 + 1)
    (hs1 : 0 < -N.s + 1)
    (hz : ¬ (⟪x 0, x 1 - x 5⟫ = ⟪x 3, x 1 - x 5⟫ ∧
      ⟪x 3, x 1 - x 5⟫ = ⟪x 4, x 1 - x 5⟫)) :
    Cert29 x := by
  obtain ⟨σ, hE, -⟩ :=
    NF29.rimThen_k3_E51s N hb0 hq1 hq2 hs1 hz
  exact Cert29.ofEPair 5 1 0 4 3 (by decide) hE

/-- Certificate of `NF29.rimThen_k3_E51l`: the edge pair of Lemma E at `51` as a `Cert29`
(`FEWER-FACES-PROOFS.md` §28, §21.13). -/
theorem NF29.cert_k3_E51l (N : NF29 x)
    (hA2 : 0 < -N.a2)
    (hb0 : 0 < N.b0)
    (hq1 : 0 < N.a0 * N.h2 - N.a2 * N.h0 - N.a0 + N.a2)
    (hs1g : 0 < N.s - 1)
    (hz : ¬ (⟪x 0, x 1 - x 5⟫ = ⟪x 3, x 1 - x 5⟫ ∧
      ⟪x 3, x 1 - x 5⟫ = ⟪x 6, x 1 - x 5⟫)) :
    Cert29 x := by
  obtain ⟨σ, hE, -⟩ :=
    NF29.rimThen_k3_E51l N hA2 hb0 hq1 hs1g hz
  exact Cert29.ofEPair 5 1 0 6 3 (by decide) hE

end Minimality

end
