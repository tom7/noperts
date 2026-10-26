module

public import Minimality.Type29K3

@[expose] public section

/-!
# Type 29, classes K3 and K4 with Theorem P (`FEWER-FACES-PROOFS.md` §21)

Off `R_G` some E-good `G` edge `x → y` of `O` is a quad edge; there Lemma E holds for `K` at the
edge `xy` (clause C1 of Theorem P, §12, here in normal coordinates: the closings of `K`, the cap
hidden or a middle, `[a b c v] [a b c w] ≤ 0` from the class): `NF29.isRupert_k4_E24`, `_E41s`,
`_E41l`, `_E51s`, `_E51l`, `_E15` (K4a) and `NF29.isRupert_k3_E03`, `_E24`, `_E14`, `_E51s`,
`_E51l` (K3a); `NF29.isRupert_k4_E05` is not needed.  With Theorems 21.11 and 21.22 on `R_G`,
every shape whose `O` is of class K4 or K3 is Rupert, off the special positions and with the
genericity of the named tests: `NF29.isRupert_K4a_all`, `NF29.isRupert_K4b_all`,
`NF29.isRupert_K3a_all`, `NF29.isRupert_K3b_all` (`K4C1Gen`, `K3C1Gen`: the edge tiers'
genericity).
-/

set_option linter.unusedVariables false

namespace Minimality

open scoped RealInnerProductSpace
open Finset

variable {x : Fin 7 → ℝ³}

/-- Certificate form of `NF29.isRupert_k4_E05`
(`FEWER-FACES-PROOFS.md` §18.2, §21): the rim at its named view as `RimCertPts`
(or `RimCert`), without the `NoHDNAt` hypotheses, which only enter the corollary. -/
theorem NF29.rimThen_k4_E05 (N : NF29 x)
    (ha2 : 0 < N.a2)
    (hVn : 0 < -N.a0 * N.h2 + N.a2 * N.h0 - N.b0 * N.h2 + N.b2 * N.h0 - N.h0 + N.h2)
    (hq1 : 0 < N.b0 * N.h2 - N.b2 * N.h0 - N.h2)
    (hq2 : 0 < N.a0 * N.b2 - N.a2 * N.b0 - N.b0 * N.h2 + N.b2 * N.h0 + N.a2 + N.b0 + N.h2 - 1)
    (hz₁ : [⟪x 0, (x 5 - x 0)⟫, ⟪x 1, (x 5 - x 0)⟫, ⟪x 2, (x 5 - x 0)⟫, ⟪x 3, (x 5 - x 0)⟫].Nodup)
    (hz₂ : [⟪x 5, (x 5 - x 0)⟫, ⟪x 1, (x 5 - x 0)⟫, ⟪x 2, (x 5 - x 0)⟫, ⟪x 3, (x 5 - x 0)⟫].Nodup) :
    RimCertThen (univ.image x) (x 5 - x 0)
      (NoHDNAt ((univ.image x).erase (x 5)) (x 5 - x 0) ∧
        NoHDNAt ((univ.image x).erase (x 0)) (x 5 - x 0)) := by
  have hA0 : 0 < -N.a0 := by linarith [N.ha0]
  have h345_0 : 0 < 1 - N.a0 - N.b0 - N.h0 := by linarith [N.t345_0]
  have hst : 0 < N.s + N.t - 1 := by linarith [N.hst]
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  refine edgePairσ_both (univ.image x) hσ (img29 0) (img29 5) (img29 1) (img29 3) (img29 2)
    ?_ ?_ ?_ ?_ ?_ hz₁ hz₂ ?_
  · nf29_test N hσD N.hF5
  · nf29_test N hσD (by show 0 < N.a0 * N.b2 - N.a2 * N.b0 + N.a2; linarith [ha2, N.hDD])
  · nf29_test N hσD N.hDG5
  · nf29_test N hσD hA0
  · nf29_simp N
    refine nf_E_le rfl rfl ?_
    have hE1 : 0 ≤ N.a0 * N.b2 - N.a2 * N.b0 := by
      linarith [N.hDD]
    have hE2 : -N.a2 ≤ 0 := by
      linarith [ha2]
    simp only [det3c]
    linarith [mul_nonpos_of_nonneg_of_nonpos hE1 hE2]
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr <| Or.inr <| Or.inl rfl
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
    · refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨?_, ?_, ?_, ?_⟩
      · nf29_test N hσD N.hh0
      · nf29_test N hσD hq1
      · nf29_test N hσD hq2
      · nf29_test N hσD h345_0
    · exact Or.inr <| Or.inl rfl
    · refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨?_, ?_, ?_, ?_⟩
      · nf29_test N hσD (by show 0 < N.h0 * N.s; linarith [mul_pos (N.hh0) N.hs])
      · nf29_test N hσD (by
              show 0 < -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 *
                N.s - N.h2 * N.s
              linarith [mul_pos (N.hs) hq1, mul_pos (N.hF5) N.ht])
      · nf29_test N hσD (pos_of_mul_pos_r N.hh2
              (by
                show 0 < (N.a0 * N.h2 * N.t - N.a2 * N.h0 * N.t - N.b0 * N.h2 * N.s + N.b2 * N.h0 *
                    N.s + N.a0 * N.b2 - N.a0 * N.t - N.a2 * N.b0 + N.b0 * N.s + N.h2 * N.s + N.a2 -
                    N.s) * (N.h2)
                linarith [mul_pos (N.hF5) N.d234, mul_pos (mul_pos (hst) ha2) hq1, mul_pos
                    (mul_pos (N.ht) ha2) hVn, mul_pos (mul_pos (N.hh2) N.hs) hq2]))
      · nf29_test N hσD N.d035

/-- **C1 tier** (Theorem P, Lemma E at the quad edge `0 → 5` of `O`). -/
theorem NF29.isRupert_k4_E05 (N : NF29 x)
    (ha2 : 0 < N.a2)
    (hVn : 0 < -N.a0 * N.h2 + N.a2 * N.h0 - N.b0 * N.h2 + N.b2 * N.h0 - N.h0 + N.h2)
    (hq1 : 0 < N.b0 * N.h2 - N.b2 * N.h0 - N.h2)
    (hq2 : 0 < N.a0 * N.b2 - N.a2 * N.b0 - N.b0 * N.h2 + N.b2 * N.h0 + N.a2 + N.b0 + N.h2 - 1)
    (hz₁ : [⟪x 0, (x 5 - x 0)⟫, ⟪x 1, (x 5 - x 0)⟫, ⟪x 2, (x 5 - x 0)⟫, ⟪x 3, (x 5 - x 0)⟫].Nodup)
    (hz₂ : [⟪x 5, (x 5 - x 0)⟫, ⟪x 1, (x 5 - x 0)⟫, ⟪x 2, (x 5 - x 0)⟫, ⟪x 3, (x 5 - x 0)⟫].Nodup)
    (hnd₁ : NoHDNAt ((univ.image x).erase (x 5)) (x 5 - x 0))
    (hnd₂ : NoHDNAt ((univ.image x).erase (x 0)) (x 5 - x 0)) : IsRupert (univ.image x) := by
  exact (NF29.rimThen_k4_E05 N ha2 hVn hq1 hq2 hz₁ hz₂).2 ⟨hnd₁, hnd₂⟩

/-- Certificate form of `NF29.isRupert_k4_E24`
(`FEWER-FACES-PROOFS.md` §18.2, §21): the rim at its named view as `RimCertPts`
(or `RimCert`), without the `NoHDNAt` hypotheses, which only enter the corollary. -/
theorem NF29.rimThen_k4_E24 (N : NF29 x)
    (hb0 : 0 < N.b0)
    (hq1 : 0 < -N.a0 * N.h2 + N.a2 * N.h0 - N.h0)
    (hq2 : 0 < N.a0 * N.b2 + N.a0 * N.h2 - N.a2 * N.b0 - N.a2 * N.h0 + N.a2 + N.b0 + N.h0 - 1)
    (hz₁ : [⟪x 2, (x 4 - x 2)⟫, ⟪x 3, (x 4 - x 2)⟫, ⟪x 0, (x 4 - x 2)⟫, ⟪x 1, (x 4 - x 2)⟫].Nodup)
    (hz₂ : [⟪x 4, (x 4 - x 2)⟫, ⟪x 3, (x 4 - x 2)⟫, ⟪x 0, (x 4 - x 2)⟫, ⟪x 1, (x 4 - x 2)⟫].Nodup) :
    RimCertThen (univ.image x) (x 4 - x 2)
      (NoHDNAt ((univ.image x).erase (x 4)) (x 4 - x 2) ∧
        NoHDNAt ((univ.image x).erase (x 2)) (x 4 - x 2)) := by
  have hA0 : 0 < -N.a0 := by linarith [N.ha0]
  have hB2 : 0 < -N.b2 := by linarith [N.hb2]
  have h345_2 : 0 < 1 - N.a2 - N.b2 - N.h2 := by linarith [N.t345_2]
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  refine edgePairσ_both (univ.image x) hσ (img29 2) (img29 4) (img29 3) (img29 1) (img29 0)
    ?_ ?_ ?_ ?_ ?_ hz₁ hz₂ ?_
  · nf29_test N hσD N.hDG4
  · nf29_test N hσD (by show 0 < N.a0 * N.b2 - N.a2 * N.b0 + N.b0; linarith [hb0, N.hDD])
  · nf29_test N hσD N.hF4
  · nf29_test N hσD hB2
  · nf29_simp N
    refine nf_E_le rfl rfl ?_
    have hE1 : 0 ≤ N.a0 * N.b2 - N.a2 * N.b0 := by
      linarith [N.hDD]
    have hE2 : -N.b0 ≤ 0 := by
      linarith [hb0]
    simp only [det3c]
    linarith [mul_nonpos_of_nonneg_of_nonpos hE1 hE2]
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    fin_cases i
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr <| Or.inr <| Or.inl rfl
    · exact Or.inr <| Or.inl rfl
    · refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨?_, ?_, ?_, ?_⟩
      · nf29_test N hσD h345_2
      · nf29_test N hσD hq2
      · nf29_test N hσD hq1
      · nf29_test N hσD N.hh2
    · refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨?_, ?_, ?_, ?_⟩
      · nf29_test N hσD N.d234
      · nf29_test N hσD (pos_of_mul_pos_r hA0
              (by
                show 0 < (N.a0 * N.h2 * N.t - N.a2 * N.h0 * N.t - N.b0 * N.h2 * N.s + N.b2 * N.h0 *
                    N.s + N.a0 * N.b2 - N.a2 * N.b0 + N.a2 * N.t - N.b2 * N.s + N.h0 * N.t + N.b0 -
                    N.t) * (-N.a0)
                linarith [mul_pos (N.d035) hb0, mul_pos (N.hDD) N.d035, mul_pos (mul_pos (hA0) N.ht)
                    hq2, mul_pos (mul_pos (N.hs) hb0) hq2]))
      · nf29_test N hσD (by
              show 0 < -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 *
                N.s - N.h0 * N.t
              linarith [mul_pos (N.ht) hq1, mul_pos (N.hF4) N.hs])
      · nf29_test N hσD (by show 0 < N.h2 * N.t; linarith [mul_pos (N.hh2) N.ht])

/-- **C1 tier** (Theorem P, Lemma E at the quad edge `2 → 4` of `O`). -/
theorem NF29.isRupert_k4_E24 (N : NF29 x)
    (hb0 : 0 < N.b0)
    (hq1 : 0 < -N.a0 * N.h2 + N.a2 * N.h0 - N.h0)
    (hq2 : 0 < N.a0 * N.b2 + N.a0 * N.h2 - N.a2 * N.b0 - N.a2 * N.h0 + N.a2 + N.b0 + N.h0 - 1)
    (hz₁ : [⟪x 2, (x 4 - x 2)⟫, ⟪x 3, (x 4 - x 2)⟫, ⟪x 0, (x 4 - x 2)⟫, ⟪x 1, (x 4 - x 2)⟫].Nodup)
    (hz₂ : [⟪x 4, (x 4 - x 2)⟫, ⟪x 3, (x 4 - x 2)⟫, ⟪x 0, (x 4 - x 2)⟫, ⟪x 1, (x 4 - x 2)⟫].Nodup)
    (hnd₁ : NoHDNAt ((univ.image x).erase (x 4)) (x 4 - x 2))
    (hnd₂ : NoHDNAt ((univ.image x).erase (x 2)) (x 4 - x 2)) : IsRupert (univ.image x) := by
  exact (NF29.rimThen_k4_E24 N hb0 hq1 hq2 hz₁ hz₂).2 ⟨hnd₁, hnd₂⟩

/-- Certificate form of `NF29.isRupert_k4_E41s`
(`FEWER-FACES-PROOFS.md` §18.2, §21): the rim at its named view as `RimCertPts`
(or `RimCert`), without the `NoHDNAt` hypotheses, which only enter the corollary. -/
theorem NF29.rimThen_k4_E41s (N : NF29 x)
    (ha2 : 0 < N.a2)
    (hq1 : 0 < -N.b0 * N.h2 + N.b2 * N.h0 + N.b0 - N.b2)
    (hq2 : 0 < -N.b0 - N.h0 + 1)
    (ht1 : 0 < -N.t + 1)
    (hz₁ : [⟪x 4, (x 1 - x 4)⟫, ⟪x 5, (x 1 - x 4)⟫, ⟪x 3, (x 1 - x 4)⟫, ⟪x 2, (x 1 - x 4)⟫].Nodup)
    (hz₂ : [⟪x 1, (x 1 - x 4)⟫, ⟪x 5, (x 1 - x 4)⟫, ⟪x 3, (x 1 - x 4)⟫, ⟪x 2, (x 1 - x 4)⟫].Nodup) :
    RimCertThen (univ.image x) (x 1 - x 4)
      (NoHDNAt ((univ.image x).erase (x 1)) (x 1 - x 4) ∧
        NoHDNAt ((univ.image x).erase (x 4)) (x 1 - x 4)) := by
  have hB2 : 0 < -N.b2 := by linarith [N.hb2]
  have h345_2 : 0 < 1 - N.a2 - N.b2 - N.h2 := by linarith [N.t345_2]
  have hst : 0 < N.s + N.t - 1 := by linarith [N.hst]
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  refine edgePairσ_both (univ.image x) hσ (img29 4) (img29 1) (img29 5) (img29 2) (img29 3)
    ?_ ?_ ?_ ?_ ?_ hz₁ hz₂ ?_
  · nf29_test N hσD (by norm_num : (0 : ℝ) < 1)
  · nf29_test N hσD (by show 0 < -N.b2 - N.h2 + 1; linarith [ha2, h345_2])
  · nf29_test N hσD hB2
  · nf29_test N hσD N.hh2
  · nf29_simp N
    refine nf_E_le rfl rfl ?_
    have hE1 : 0 ≤ -N.a2 - N.b2 - N.h2 + 1 := by
      linarith [h345_2]
    have hE2 : -N.a2 ≤ 0 := by
      linarith [ha2]
    simp only [det3c]
    linarith [mul_nonpos_of_nonneg_of_nonpos hE1 hE2]
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    fin_cases i
    · refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨?_, ?_, ?_, ?_⟩
      · nf29_test N hσD N.hh0
      · nf29_test N hσD hq2
      · nf29_test N hσD hq1
      · nf29_test N hσD N.hF4
    · exact Or.inr <| Or.inl rfl
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr <| Or.inr <| Or.inl rfl
    · obtain ⟨s, δ, h1, h2, h3, h4⟩ := mid_comb' (m := x 6) (X := x 4) (Y := x 5) (U := x 4 - x 1)
        (D₀ := 1) (α := N.t) (β := N.s + N.t - 1)
        (by norm_num) (by linarith [N.ht]) (by linarith [ht1]) (by linarith [hst]) (by nf29_vec N)
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
          ⟨s, δ, h1, h2, h3, Or.inl (h4.trans (by module))⟩

/-- **C1 tier** (Theorem P, Lemma E at the quad edge `4 → 1` of `O`). -/
theorem NF29.isRupert_k4_E41s (N : NF29 x)
    (ha2 : 0 < N.a2)
    (hq1 : 0 < -N.b0 * N.h2 + N.b2 * N.h0 + N.b0 - N.b2)
    (hq2 : 0 < -N.b0 - N.h0 + 1)
    (ht1 : 0 < -N.t + 1)
    (hz₁ : [⟪x 4, (x 1 - x 4)⟫, ⟪x 5, (x 1 - x 4)⟫, ⟪x 3, (x 1 - x 4)⟫, ⟪x 2, (x 1 - x 4)⟫].Nodup)
    (hz₂ : [⟪x 1, (x 1 - x 4)⟫, ⟪x 5, (x 1 - x 4)⟫, ⟪x 3, (x 1 - x 4)⟫, ⟪x 2, (x 1 - x 4)⟫].Nodup)
    (hnd₁ : NoHDNAt ((univ.image x).erase (x 1)) (x 1 - x 4))
    (hnd₂ : NoHDNAt ((univ.image x).erase (x 4)) (x 1 - x 4)) : IsRupert (univ.image x) := by
  exact (NF29.rimThen_k4_E41s N ha2 hq1 hq2 ht1 hz₁ hz₂).2 ⟨hnd₁, hnd₂⟩

/-- Certificate form of `NF29.isRupert_k4_E41l`
(`FEWER-FACES-PROOFS.md` §18.2, §21): the rim at its named view as `RimCertPts`
(or `RimCert`), without the `NoHDNAt` hypotheses, which only enter the corollary. -/
theorem NF29.rimThen_k4_E41l (N : NF29 x)
    (ha2 : 0 < N.a2)
    (hb0 : 0 < N.b0)
    (hq1 : 0 < -N.b0 * N.h2 + N.b2 * N.h0 + N.b0 - N.b2)
    (hq2 : 0 < -N.b0 - N.h0 + 1)
    (ht1g : 0 < N.t - 1)
    (hz₁ : [⟪x 4, (x 1 - x 4)⟫, ⟪x 6, (x 1 - x 4)⟫, ⟪x 3, (x 1 - x 4)⟫, ⟪x 2, (x 1 - x 4)⟫].Nodup)
    (hz₂ : [⟪x 1, (x 1 - x 4)⟫, ⟪x 6, (x 1 - x 4)⟫, ⟪x 3, (x 1 - x 4)⟫, ⟪x 2, (x 1 - x 4)⟫].Nodup) :
    RimCertThen (univ.image x) (x 1 - x 4)
      (NoHDNAt ((univ.image x).erase (x 1)) (x 1 - x 4) ∧
        NoHDNAt ((univ.image x).erase (x 4)) (x 1 - x 4)) := by
  have hB2 : 0 < -N.b2 := by linarith [N.hb2]
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  refine edgePairσ_both (univ.image x) hσ (img29 4) (img29 1) (img29 6) (img29 2) (img29 3)
    ?_ ?_ ?_ ?_ ?_ hz₁ hz₂ ?_
  · nf29_test N hσD N.ht
  · nf29_test N hσD (by
          show 0 < -N.h2 * N.t - N.b2 + N.t
          linarith [N.d234, mul_pos (N.ht) ha2, mul_pos (hB2) N.hs])
  · nf29_test N hσD hB2
  · nf29_test N hσD (by show 0 < N.h2 * N.t; linarith [mul_pos (N.hh2) N.ht])
  · nf29_simp N
    refine nf_E_le rfl rfl ?_
    have hE1 : 0 ≤ -N.a2 * N.t + N.b2 * N.s - N.h2 * N.t - N.b2 + N.t := by
      linarith [N.d234]
    have hE2 : -N.a2 * N.t + N.b2 * N.s ≤ 0 := by
      linarith
          [(by show 0 < N.a2 * N.t - N.b2 * N.s; linarith [mul_pos (N.ht) ha2, mul_pos (hB2) N.hs])]
    simp only [det3c]
    linarith [mul_nonpos_of_nonneg_of_nonpos hE1 hE2]
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    fin_cases i
    · refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨?_, ?_, ?_, ?_⟩
      · nf29_test N hσD (by show 0 < N.h0 * N.t; linarith [mul_pos (N.hh0) N.ht])
      · nf29_test N hσD (by
              show 0 < -N.h0 * N.t - N.b0 + N.t
              linarith [mul_pos (N.ht) hq2, mul_pos (hb0) ht1g])
      · nf29_test N hσD hq1
      · nf29_test N hσD N.hF4
    · exact Or.inr <| Or.inl rfl
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
    · exact Or.inl rfl
    · obtain ⟨s, δ, h1, h2, h3, h4⟩ := mid_comb' (m := x 5) (X := x 1) (Y := x 6) (U := x 1 - x 4)
        (D₀ := N.t) (α := 1) (β := N.s)
        (by linarith [N.ht]) (by norm_num) (by linarith [ht1g]) (by linarith [N.hs]) (by nf29_vec N)
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
          ⟨s, δ, h1, h2, h3, Or.inr <| Or.inr <| Or.inl (h4.trans (by module))⟩
    · exact Or.inr <| Or.inr <| Or.inl rfl

/-- **C1 tier** (Theorem P, Lemma E at the quad edge `4 → 1` of `O`). -/
theorem NF29.isRupert_k4_E41l (N : NF29 x)
    (ha2 : 0 < N.a2)
    (hb0 : 0 < N.b0)
    (hq1 : 0 < -N.b0 * N.h2 + N.b2 * N.h0 + N.b0 - N.b2)
    (hq2 : 0 < -N.b0 - N.h0 + 1)
    (ht1g : 0 < N.t - 1)
    (hz₁ : [⟪x 4, (x 1 - x 4)⟫, ⟪x 6, (x 1 - x 4)⟫, ⟪x 3, (x 1 - x 4)⟫, ⟪x 2, (x 1 - x 4)⟫].Nodup)
    (hz₂ : [⟪x 1, (x 1 - x 4)⟫, ⟪x 6, (x 1 - x 4)⟫, ⟪x 3, (x 1 - x 4)⟫, ⟪x 2, (x 1 - x 4)⟫].Nodup)
    (hnd₁ : NoHDNAt ((univ.image x).erase (x 1)) (x 1 - x 4))
    (hnd₂ : NoHDNAt ((univ.image x).erase (x 4)) (x 1 - x 4)) : IsRupert (univ.image x) := by
  exact (NF29.rimThen_k4_E41l N ha2 hb0 hq1 hq2 ht1g hz₁ hz₂).2 ⟨hnd₁, hnd₂⟩

/-- Certificate form of `NF29.isRupert_k4_E15`
(`FEWER-FACES-PROOFS.md` §18.2, §21): the rim at its named view as `RimCertPts`
(or `RimCert`), without the `NoHDNAt` hypotheses, which only enter the corollary. -/
theorem NF29.rimThen_k4_E15 (N : NF29 x)
    (hVn : 0 < -N.a0 * N.h2 + N.a2 * N.h0 - N.b0 * N.h2 + N.b2 * N.h0 - N.h0 + N.h2)
    (hq1 : 0 < -N.a0 * N.h2 + N.a2 * N.h0 + N.a0 - N.a2)
    (hq2 : 0 < N.a2 + N.h2 - 1)
    (hz₁ : [⟪x 1, (x 5 - x 1)⟫, ⟪x 4, (x 5 - x 1)⟫, ⟪x 2, (x 5 - x 1)⟫, ⟪x 0, (x 5 - x 1)⟫].Nodup)
    (hz₂ : [⟪x 5, (x 5 - x 1)⟫, ⟪x 4, (x 5 - x 1)⟫, ⟪x 2, (x 5 - x 1)⟫, ⟪x 0, (x 5 - x 1)⟫].Nodup) :
    RimCertThen (univ.image x) (x 5 - x 1)
      (NoHDNAt ((univ.image x).erase (x 5)) (x 5 - x 1) ∧
        NoHDNAt ((univ.image x).erase (x 1)) (x 5 - x 1)) := by
  have hA0 : 0 < -N.a0 := by linarith [N.ha0]
  have hB2 : 0 < -N.b2 := by linarith [N.hb2]
  have hst : 0 < N.s + N.t - 1 := by linarith [N.hst]
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  refine edgePairσ_both (univ.image x) hσ (img29 1) (img29 5) (img29 4) (img29 0) (img29 2)
    ?_ ?_ ?_ ?_ ?_ hz₁ hz₂ ?_
  · nf29_test N hσD N.hh2
  · nf29_test N hσD (by show 0 < -N.a0 * N.h2 + N.a2 * N.h0 - N.h0 + N.h2; linarith [hVn, N.hF4])
  · nf29_test N hσD N.hF5
  · nf29_test N hσD N.hh0
  · nf29_simp N
    refine nf_E_le rfl rfl ?_
    have hE1 : 0 ≤ N.b0 * N.h2 - N.b2 * N.h0 := by
      linarith [N.hF4]
    have hE2 : N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2 ≤ 0 := by
      linarith [hVn]
    simp only [det3c]
    linarith [mul_nonpos_of_nonneg_of_nonpos hE1 hE2]
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    fin_cases i
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
    · refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨?_, ?_, ?_, ?_⟩
      · nf29_test N hσD (by norm_num : (0 : ℝ) < 1)
      · nf29_test N hσD hq2
      · nf29_test N hσD hq1
      · nf29_test N hσD hA0
    · exact Or.inr <| Or.inr <| Or.inl rfl
    · exact Or.inr <| Or.inl rfl
    · obtain ⟨s, δ, h1, h2, h3, h4⟩ := mid_comb' (m := x 6) (X := x 5) (Y := x 4) (U := x 5 - x 1)
        (D₀ := 1) (α := N.s) (β := N.s + N.t - 1)
        (by norm_num) (by linarith [N.hs]) (by
              linarith [(pos_of_mul_pos_r hB2
                    (by show 0 < (-N.s + 1) * (-N.b2); linarith [N.d234, mul_pos (N.ht) hq2]))])
            (by linarith [hst]) (by nf29_vec N)
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
          ⟨s, δ, h1, h2, h3, Or.inr <| Or.inr <| Or.inl (h4.trans (by module))⟩

/-- **C1 tier** (Theorem P, Lemma E at the quad edge `1 → 5` of `O`). -/
theorem NF29.isRupert_k4_E15 (N : NF29 x)
    (hVn : 0 < -N.a0 * N.h2 + N.a2 * N.h0 - N.b0 * N.h2 + N.b2 * N.h0 - N.h0 + N.h2)
    (hq1 : 0 < -N.a0 * N.h2 + N.a2 * N.h0 + N.a0 - N.a2)
    (hq2 : 0 < N.a2 + N.h2 - 1)
    (hz₁ : [⟪x 1, (x 5 - x 1)⟫, ⟪x 4, (x 5 - x 1)⟫, ⟪x 2, (x 5 - x 1)⟫, ⟪x 0, (x 5 - x 1)⟫].Nodup)
    (hz₂ : [⟪x 5, (x 5 - x 1)⟫, ⟪x 4, (x 5 - x 1)⟫, ⟪x 2, (x 5 - x 1)⟫, ⟪x 0, (x 5 - x 1)⟫].Nodup)
    (hnd₁ : NoHDNAt ((univ.image x).erase (x 5)) (x 5 - x 1))
    (hnd₂ : NoHDNAt ((univ.image x).erase (x 1)) (x 5 - x 1)) : IsRupert (univ.image x) := by
  exact (NF29.rimThen_k4_E15 N hVn hq1 hq2 hz₁ hz₂).2 ⟨hnd₁, hnd₂⟩

/-- Certificate form of `NF29.isRupert_k4_E51s`
(`FEWER-FACES-PROOFS.md` §18.2, §21): the rim at its named view as `RimCertPts`
(or `RimCert`), without the `NoHDNAt` hypotheses, which only enter the corollary. -/
theorem NF29.rimThen_k4_E51s (N : NF29 x)
    (hb0 : 0 < N.b0)
    (hq1 : 0 < N.a0 * N.h2 - N.a2 * N.h0 - N.a0 + N.a2)
    (hq2 : 0 < -N.a2 - N.h2 + 1)
    (hs1 : 0 < -N.s + 1)
    (hz₁ : [⟪x 5, (x 1 - x 5)⟫, ⟪x 0, (x 1 - x 5)⟫, ⟪x 3, (x 1 - x 5)⟫, ⟪x 4, (x 1 - x 5)⟫].Nodup)
    (hz₂ : [⟪x 1, (x 1 - x 5)⟫, ⟪x 0, (x 1 - x 5)⟫, ⟪x 3, (x 1 - x 5)⟫, ⟪x 4, (x 1 - x 5)⟫].Nodup) :
    RimCertThen (univ.image x) (x 1 - x 5)
      (NoHDNAt ((univ.image x).erase (x 1)) (x 1 - x 5) ∧
        NoHDNAt ((univ.image x).erase (x 5)) (x 1 - x 5)) := by
  have hA0 : 0 < -N.a0 := by linarith [N.ha0]
  have h345_0 : 0 < 1 - N.a0 - N.b0 - N.h0 := by linarith [N.t345_0]
  have hst : 0 < N.s + N.t - 1 := by linarith [N.hst]
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  refine edgePairσ_both (univ.image x) hσ (img29 5) (img29 1) (img29 0) (img29 4) (img29 3)
    ?_ ?_ ?_ ?_ ?_ hz₁ hz₂ ?_
  · nf29_test N hσD hA0
  · nf29_test N hσD (by show 0 < -N.a0 - N.h0 + 1; linarith [hb0, h345_0])
  · nf29_test N hσD (by norm_num : (0 : ℝ) < 1)
  · nf29_test N hσD N.hh0
  · nf29_simp N
    refine nf_E_le rfl rfl ?_
    have hE1 : 0 ≤ -N.a0 - N.b0 - N.h0 + 1 := by
      linarith [h345_0]
    have hE2 : -N.b0 ≤ 0 := by
      linarith [hb0]
    simp only [det3c]
    linarith [mul_nonpos_of_nonneg_of_nonpos hE1 hE2]
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    fin_cases i
    · exact Or.inr <| Or.inr <| Or.inl rfl
    · exact Or.inr <| Or.inl rfl
    · refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨?_, ?_, ?_, ?_⟩
      · nf29_test N hσD N.hF5
      · nf29_test N hσD hq1
      · nf29_test N hσD hq2
      · nf29_test N hσD N.hh2
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
    · exact Or.inl rfl
    · obtain ⟨s, δ, h1, h2, h3, h4⟩ := mid_comb' (m := x 6) (X := x 4) (Y := x 5) (U := x 5 - x 1)
        (D₀ := 1) (α := -N.s + 1) (β := N.s + N.t - 1)
        (by norm_num) (by linarith [hs1]) (by linarith [N.hs]) (by linarith [hst]) (by nf29_vec N)
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
          ⟨s, δ, h1, h2, h3, Or.inr <| Or.inl (h4.trans (by module))⟩

/-- **C1 tier** (Theorem P, Lemma E at the quad edge `5 → 1` of `O`). -/
theorem NF29.isRupert_k4_E51s (N : NF29 x)
    (hb0 : 0 < N.b0)
    (hq1 : 0 < N.a0 * N.h2 - N.a2 * N.h0 - N.a0 + N.a2)
    (hq2 : 0 < -N.a2 - N.h2 + 1)
    (hs1 : 0 < -N.s + 1)
    (hz₁ : [⟪x 5, (x 1 - x 5)⟫, ⟪x 0, (x 1 - x 5)⟫, ⟪x 3, (x 1 - x 5)⟫, ⟪x 4, (x 1 - x 5)⟫].Nodup)
    (hz₂ : [⟪x 1, (x 1 - x 5)⟫, ⟪x 0, (x 1 - x 5)⟫, ⟪x 3, (x 1 - x 5)⟫, ⟪x 4, (x 1 - x 5)⟫].Nodup)
    (hnd₁ : NoHDNAt ((univ.image x).erase (x 1)) (x 1 - x 5))
    (hnd₂ : NoHDNAt ((univ.image x).erase (x 5)) (x 1 - x 5)) : IsRupert (univ.image x) := by
  exact (NF29.rimThen_k4_E51s N hb0 hq1 hq2 hs1 hz₁ hz₂).2 ⟨hnd₁, hnd₂⟩

/-- Certificate form of `NF29.isRupert_k4_E51l`
(`FEWER-FACES-PROOFS.md` §18.2, §21): the rim at its named view as `RimCertPts`
(or `RimCert`), without the `NoHDNAt` hypotheses, which only enter the corollary. -/
theorem NF29.rimThen_k4_E51l (N : NF29 x)
    (ha2 : 0 < N.a2)
    (hb0 : 0 < N.b0)
    (hq1 : 0 < N.a0 * N.h2 - N.a2 * N.h0 - N.a0 + N.a2)
    (hq2 : 0 < -N.a2 - N.h2 + 1)
    (hs1g : 0 < N.s - 1)
    (hz₁ : [⟪x 5, (x 1 - x 5)⟫, ⟪x 0, (x 1 - x 5)⟫, ⟪x 3, (x 1 - x 5)⟫, ⟪x 6, (x 1 - x 5)⟫].Nodup)
    (hz₂ : [⟪x 1, (x 1 - x 5)⟫, ⟪x 0, (x 1 - x 5)⟫, ⟪x 3, (x 1 - x 5)⟫, ⟪x 6, (x 1 - x 5)⟫].Nodup) :
    RimCertThen (univ.image x) (x 1 - x 5)
      (NoHDNAt ((univ.image x).erase (x 1)) (x 1 - x 5) ∧
        NoHDNAt ((univ.image x).erase (x 5)) (x 1 - x 5)) := by
  have hA0 : 0 < -N.a0 := by linarith [N.ha0]
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  refine edgePairσ_both (univ.image x) hσ (img29 5) (img29 1) (img29 0) (img29 6) (img29 3)
    ?_ ?_ ?_ ?_ ?_ hz₁ hz₂ ?_
  · nf29_test N hσD hA0
  · nf29_test N hσD (by
          show 0 < -N.h0 * N.s - N.a0 + N.s
          linarith [hb0, N.d035, mul_pos (hA0) N.ht, mul_pos (hb0) hs1g])
  · nf29_test N hσD N.hs
  · nf29_test N hσD (by show 0 < N.h0 * N.s; linarith [mul_pos (N.hh0) N.hs])
  · nf29_simp N
    refine nf_E_le rfl rfl ?_
    have hE1 : 0 ≤ N.a0 * N.t - N.b0 * N.s - N.h0 * N.s - N.a0 + N.s := by
      linarith [N.d035]
    have hE2 : N.a0 * N.t - N.b0 * N.s ≤ 0 := by
      linarith [(by
              show 0 < -N.a0 * N.t + N.b0 * N.s
              linarith [mul_pos (N.hs) hb0, mul_pos (hA0) N.ht])]
    simp only [det3c]
    linarith [mul_nonpos_of_nonneg_of_nonpos hE1 hE2]
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    fin_cases i
    · exact Or.inr <| Or.inr <| Or.inl rfl
    · exact Or.inr <| Or.inl rfl
    · refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨?_, ?_, ?_, ?_⟩
      · nf29_test N hσD N.hF5
      · nf29_test N hσD hq1
      · nf29_test N hσD (by
              show 0 < -N.h2 * N.s - N.a2 + N.s
              linarith [mul_pos (ha2) hs1g, mul_pos (N.hs) hq2])
      · nf29_test N hσD (by show 0 < N.h2 * N.s; linarith [mul_pos (N.hh2) N.hs])
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
    · obtain ⟨s, δ, h1, h2, h3, h4⟩ := mid_comb' (m := x 4) (X := x 6) (Y := x 1) (U := x 1 - x 5)
        (D₀ := N.s) (α := N.s - 1) (β := N.t)
        (by linarith [N.hs]) (by linarith [hs1g]) (by norm_num) (by linarith [N.ht]) (by nf29_vec N)
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
          ⟨s, δ, h1, h2, h3, Or.inr <| Or.inr <| Or.inr (h4.trans (by module))⟩
    · exact Or.inl rfl
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inl rfl

/-- **C1 tier** (Theorem P, Lemma E at the quad edge `5 → 1` of `O`). -/
theorem NF29.isRupert_k4_E51l (N : NF29 x)
    (ha2 : 0 < N.a2)
    (hb0 : 0 < N.b0)
    (hq1 : 0 < N.a0 * N.h2 - N.a2 * N.h0 - N.a0 + N.a2)
    (hq2 : 0 < -N.a2 - N.h2 + 1)
    (hs1g : 0 < N.s - 1)
    (hz₁ : [⟪x 5, (x 1 - x 5)⟫, ⟪x 0, (x 1 - x 5)⟫, ⟪x 3, (x 1 - x 5)⟫, ⟪x 6, (x 1 - x 5)⟫].Nodup)
    (hz₂ : [⟪x 1, (x 1 - x 5)⟫, ⟪x 0, (x 1 - x 5)⟫, ⟪x 3, (x 1 - x 5)⟫, ⟪x 6, (x 1 - x 5)⟫].Nodup)
    (hnd₁ : NoHDNAt ((univ.image x).erase (x 1)) (x 1 - x 5))
    (hnd₂ : NoHDNAt ((univ.image x).erase (x 5)) (x 1 - x 5)) : IsRupert (univ.image x) := by
  exact (NF29.rimThen_k4_E51l N ha2 hb0 hq1 hq2 hs1g hz₁ hz₂).2 ⟨hnd₁, hnd₂⟩

/-- Certificate form of `NF29.isRupert_k3_E03`
(`FEWER-FACES-PROOFS.md` §18.2, §21): the rim at its named view as `RimCertPts`
(or `RimCert`), without the `NoHDNAt` hypotheses, which only enter the corollary. -/
theorem NF29.rimThen_k3_E03 (N : NF29 x)
    (hA2 : 0 < -N.a2)
    (hq1 : 0 < N.b0 * N.h2 - N.b2 * N.h0 + N.b2)
    (hq2 : 0 < N.h0 - 1)
    (hz₁ : [⟪x 0, (x 3 - x 0)⟫, ⟪x 5, (x 3 - x 0)⟫, ⟪x 1, (x 3 - x 0)⟫, ⟪x 2, (x 3 - x 0)⟫].Nodup)
    (hz₂ : [⟪x 3, (x 3 - x 0)⟫, ⟪x 5, (x 3 - x 0)⟫, ⟪x 1, (x 3 - x 0)⟫, ⟪x 2, (x 3 - x 0)⟫].Nodup) :
    RimCertThen (univ.image x) (x 3 - x 0)
      (NoHDNAt ((univ.image x).erase (x 3)) (x 3 - x 0) ∧
        NoHDNAt ((univ.image x).erase (x 0)) (x 3 - x 0)) := by
  have hA0 : 0 < -N.a0 := by linarith [N.ha0]
  have h345_0 : 0 < 1 - N.a0 - N.b0 - N.h0 := by linarith [N.t345_0]
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  refine edgePairσ_both (univ.image x) hσ (img29 0) (img29 3) (img29 5) (img29 2) (img29 1)
    ?_ ?_ ?_ ?_ ?_ hz₁ hz₂ ?_
  · nf29_test N hσD hA0
  · nf29_test N hσD (by show 0 < -N.a0 * N.h2 + N.a2 * N.h0 - N.a2; linarith [hA2, N.hF5])
  · nf29_test N hσD N.hDD
  · nf29_test N hσD N.hDG5
  · nf29_simp N
    refine nf_E_le rfl rfl ?_
    have hE1 : 0 ≤ -N.a0 * N.h2 + N.a2 * N.h0 := by
      linarith [N.hF5]
    have hE2 : N.a2 ≤ 0 := by
      linarith [hA2]
    simp only [det3c]
    linarith [mul_nonpos_of_nonneg_of_nonpos hE1 hE2]
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
    · exact Or.inr <| Or.inl rfl
    · refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨?_, ?_, ?_, ?_⟩
      · nf29_test N hσD h345_0
      · nf29_test N hσD hq2
      · nf29_test N hσD hq1
      · nf29_test N hσD N.hDG4
    · exact Or.inr <| Or.inr <| Or.inl rfl
    · refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨?_, ?_, ?_, ?_⟩
      · nf29_test N hσD N.d035
      · nf29_test N hσD (by show 0 < N.h0 * N.s - N.s; linarith [mul_pos (N.hs) hq2])
      · nf29_test N hσD (by
              show 0 < -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 *
                N.s - N.a2 * N.t + N.b2 * N.s
              linarith [mul_pos (N.ht) hA2, mul_pos (N.hs) hq1, mul_pos (N.hF5) N.ht])
      · nf29_test N hσD N.d023

/-- **C1 tier** (Theorem P, Lemma E at the quad edge `0 → 3` of `O`). -/
theorem NF29.isRupert_k3_E03 (N : NF29 x)
    (hA2 : 0 < -N.a2)
    (hq1 : 0 < N.b0 * N.h2 - N.b2 * N.h0 + N.b2)
    (hq2 : 0 < N.h0 - 1)
    (hz₁ : [⟪x 0, (x 3 - x 0)⟫, ⟪x 5, (x 3 - x 0)⟫, ⟪x 1, (x 3 - x 0)⟫, ⟪x 2, (x 3 - x 0)⟫].Nodup)
    (hz₂ : [⟪x 3, (x 3 - x 0)⟫, ⟪x 5, (x 3 - x 0)⟫, ⟪x 1, (x 3 - x 0)⟫, ⟪x 2, (x 3 - x 0)⟫].Nodup)
    (hnd₁ : NoHDNAt ((univ.image x).erase (x 3)) (x 3 - x 0))
    (hnd₂ : NoHDNAt ((univ.image x).erase (x 0)) (x 3 - x 0)) : IsRupert (univ.image x) := by
  exact (NF29.rimThen_k3_E03 N hA2 hq1 hq2 hz₁ hz₂).2 ⟨hnd₁, hnd₂⟩

/-- Certificate form of `NF29.isRupert_k3_E24`
(`FEWER-FACES-PROOFS.md` §18.2, §21): the rim at its named view as `RimCertPts`
(or `RimCert`), without the `NoHDNAt` hypotheses, which only enter the corollary. -/
theorem NF29.rimThen_k3_E24 (N : NF29 x)
    (hb0 : 0 < N.b0)
    (hV3 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2)
    (hq1 : 0 < -N.a0 * N.h2 + N.a2 * N.h0 - N.h0)
    (hq2 : 0 < N.a0 * N.b2 + N.a0 * N.h2 - N.a2 * N.b0 - N.a2 * N.h0 + N.a2 + N.b0 + N.h0 - 1)
    (hz₁ : [⟪x 2, (x 4 - x 2)⟫, ⟪x 3, (x 4 - x 2)⟫, ⟪x 0, (x 4 - x 2)⟫, ⟪x 1, (x 4 - x 2)⟫].Nodup)
    (hz₂ : [⟪x 4, (x 4 - x 2)⟫, ⟪x 3, (x 4 - x 2)⟫, ⟪x 0, (x 4 - x 2)⟫, ⟪x 1, (x 4 - x 2)⟫].Nodup) :
    RimCertThen (univ.image x) (x 4 - x 2)
      (NoHDNAt ((univ.image x).erase (x 4)) (x 4 - x 2) ∧
        NoHDNAt ((univ.image x).erase (x 2)) (x 4 - x 2)) := by
  have hB2 : 0 < -N.b2 := by linarith [N.hb2]
  have h345_2 : 0 < 1 - N.a2 - N.b2 - N.h2 := by linarith [N.t345_2]
  have hst : 0 < N.s + N.t - 1 := by linarith [N.hst]
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  refine edgePairσ_both (univ.image x) hσ (img29 2) (img29 4) (img29 3) (img29 1) (img29 0)
    ?_ ?_ ?_ ?_ ?_ hz₁ hz₂ ?_
  · nf29_test N hσD N.hDG4
  · nf29_test N hσD (by show 0 < N.a0 * N.b2 - N.a2 * N.b0 + N.b0; linarith [hb0, N.hDD])
  · nf29_test N hσD N.hF4
  · nf29_test N hσD hB2
  · nf29_simp N
    refine nf_E_le rfl rfl ?_
    have hE1 : 0 ≤ N.a0 * N.b2 - N.a2 * N.b0 := by
      linarith [N.hDD]
    have hE2 : -N.b0 ≤ 0 := by
      linarith [hb0]
    simp only [det3c]
    linarith [mul_nonpos_of_nonneg_of_nonpos hE1 hE2]
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    fin_cases i
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr <| Or.inr <| Or.inl rfl
    · exact Or.inr <| Or.inl rfl
    · refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨?_, ?_, ?_, ?_⟩
      · nf29_test N hσD h345_2
      · nf29_test N hσD hq2
      · nf29_test N hσD hq1
      · nf29_test N hσD N.hh2
    · refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨?_, ?_, ?_, ?_⟩
      · nf29_test N hσD N.d234
      · nf29_test N hσD (pos_of_mul_pos_r N.hh0
              (by
                show 0 < (N.a0 * N.h2 * N.t - N.a2 * N.h0 * N.t - N.b0 * N.h2 * N.s + N.b2 * N.h0 *
                    N.s + N.a0 * N.b2 - N.a2 * N.b0 + N.a2 * N.t - N.b2 * N.s + N.h0 * N.t + N.b0 -
                    N.t) * (N.h0)
                linarith [mul_pos (N.d035) hV3, mul_pos (N.d035) hq1, mul_pos (N.hh2) N.d035,
                    mul_pos (mul_pos (hst) hb0) hq1, mul_pos (mul_pos (N.hs) hb0) hV3, mul_pos
                    (mul_pos (N.hh0) N.ht) hq2]))
      · nf29_test N hσD (by
              show 0 < -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 *
                N.s - N.h0 * N.t
              linarith [mul_pos (N.ht) hq1, mul_pos (N.hF4) N.hs])
      · nf29_test N hσD (by show 0 < N.h2 * N.t; linarith [mul_pos (N.hh2) N.ht])

/-- **C1 tier** (Theorem P, Lemma E at the quad edge `2 → 4` of `O`). -/
theorem NF29.isRupert_k3_E24 (N : NF29 x)
    (hb0 : 0 < N.b0)
    (hV3 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2)
    (hq1 : 0 < -N.a0 * N.h2 + N.a2 * N.h0 - N.h0)
    (hq2 : 0 < N.a0 * N.b2 + N.a0 * N.h2 - N.a2 * N.b0 - N.a2 * N.h0 + N.a2 + N.b0 + N.h0 - 1)
    (hz₁ : [⟪x 2, (x 4 - x 2)⟫, ⟪x 3, (x 4 - x 2)⟫, ⟪x 0, (x 4 - x 2)⟫, ⟪x 1, (x 4 - x 2)⟫].Nodup)
    (hz₂ : [⟪x 4, (x 4 - x 2)⟫, ⟪x 3, (x 4 - x 2)⟫, ⟪x 0, (x 4 - x 2)⟫, ⟪x 1, (x 4 - x 2)⟫].Nodup)
    (hnd₁ : NoHDNAt ((univ.image x).erase (x 4)) (x 4 - x 2))
    (hnd₂ : NoHDNAt ((univ.image x).erase (x 2)) (x 4 - x 2)) : IsRupert (univ.image x) := by
  exact (NF29.rimThen_k3_E24 N hb0 hV3 hq1 hq2 hz₁ hz₂).2 ⟨hnd₁, hnd₂⟩

/-- Certificate form of `NF29.isRupert_k3_E14`
(`FEWER-FACES-PROOFS.md` §18.2, §21): the rim at its named view as `RimCertPts`
(or `RimCert`), without the `NoHDNAt` hypotheses, which only enter the corollary. -/
theorem NF29.rimThen_k3_E14 (N : NF29 x)
    (hV3 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2)
    (hq1 : 0 < N.b0 * N.h2 - N.b2 * N.h0 - N.b0 + N.b2)
    (hq2 : 0 < N.b0 + N.h0 - 1)
    (hz₁ : [⟪x 1, (x 4 - x 1)⟫, ⟪x 2, (x 4 - x 1)⟫, ⟪x 0, (x 4 - x 1)⟫, ⟪x 5, (x 4 - x 1)⟫].Nodup)
    (hz₂ : [⟪x 4, (x 4 - x 1)⟫, ⟪x 2, (x 4 - x 1)⟫, ⟪x 0, (x 4 - x 1)⟫, ⟪x 5, (x 4 - x 1)⟫].Nodup) :
    RimCertThen (univ.image x) (x 4 - x 1)
      (NoHDNAt ((univ.image x).erase (x 4)) (x 4 - x 1) ∧
        NoHDNAt ((univ.image x).erase (x 1)) (x 4 - x 1)) := by
  have hA0 : 0 < -N.a0 := by linarith [N.ha0]
  have hB2 : 0 < -N.b2 := by linarith [N.hb2]
  have hst : 0 < N.s + N.t - 1 := by linarith [N.hst]
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  refine edgePairσ_both (univ.image x) hσ (img29 1) (img29 4) (img29 2) (img29 5) (img29 0)
    ?_ ?_ ?_ ?_ ?_ hz₁ hz₂ ?_
  · nf29_test N hσD N.hF4
  · nf29_test N hσD (by show 0 < N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2; linarith [hV3, N.hF5])
  · nf29_test N hσD N.hh0
  · nf29_test N hσD N.hh2
  · nf29_simp N
    refine nf_E_le rfl rfl ?_
    have hE1 : 0 ≤ -N.a0 * N.h2 + N.a2 * N.h0 := by
      linarith [N.hF5]
    have hE2 : -N.a0 * N.h2 + N.a2 * N.h0 - N.b0 * N.h2 + N.b2 * N.h0 - N.h0 + N.h2 ≤ 0 := by
      linarith [hV3]
    simp only [det3c]
    linarith [mul_nonpos_of_nonneg_of_nonpos hE1 hE2]
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    fin_cases i
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr <| Or.inr <| Or.inl rfl
    · refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨?_, ?_, ?_, ?_⟩
      · nf29_test N hσD hB2
      · nf29_test N hσD hq1
      · nf29_test N hσD hq2
      · nf29_test N hσD (by norm_num : (0 : ℝ) < 1)
    · exact Or.inr <| Or.inl rfl
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
    · obtain ⟨s, δ, h1, h2, h3, h4⟩ := mid_comb' (m := x 6) (X := x 5) (Y := x 4) (U := x 4 - x 1)
        (D₀ := 1) (α := -N.t + 1) (β := N.s + N.t - 1)
        (by norm_num) (by
              linarith [(pos_of_mul_pos_r hA0
                    (by show 0 < (-N.t + 1) * (-N.a0); linarith [N.d035, mul_pos (N.hs) hq2]))])
            (by linarith [N.ht]) (by linarith [hst]) (by nf29_vec N)
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
          ⟨s, δ, h1, h2, h3, Or.inr <| Or.inr <| Or.inr (h4.trans (by module))⟩

/-- **C1 tier** (Theorem P, Lemma E at the quad edge `1 → 4` of `O`). -/
theorem NF29.isRupert_k3_E14 (N : NF29 x)
    (hV3 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2)
    (hq1 : 0 < N.b0 * N.h2 - N.b2 * N.h0 - N.b0 + N.b2)
    (hq2 : 0 < N.b0 + N.h0 - 1)
    (hz₁ : [⟪x 1, (x 4 - x 1)⟫, ⟪x 2, (x 4 - x 1)⟫, ⟪x 0, (x 4 - x 1)⟫, ⟪x 5, (x 4 - x 1)⟫].Nodup)
    (hz₂ : [⟪x 4, (x 4 - x 1)⟫, ⟪x 2, (x 4 - x 1)⟫, ⟪x 0, (x 4 - x 1)⟫, ⟪x 5, (x 4 - x 1)⟫].Nodup)
    (hnd₁ : NoHDNAt ((univ.image x).erase (x 4)) (x 4 - x 1))
    (hnd₂ : NoHDNAt ((univ.image x).erase (x 1)) (x 4 - x 1)) : IsRupert (univ.image x) := by
  exact (NF29.rimThen_k3_E14 N hV3 hq1 hq2 hz₁ hz₂).2 ⟨hnd₁, hnd₂⟩

/-- Certificate form of `NF29.isRupert_k3_E51s`
(`FEWER-FACES-PROOFS.md` §18.2, §21): the rim at its named view as `RimCertPts`
(or `RimCert`), without the `NoHDNAt` hypotheses, which only enter the corollary. -/
theorem NF29.rimThen_k3_E51s (N : NF29 x)
    (hb0 : 0 < N.b0)
    (hq1 : 0 < N.a0 * N.h2 - N.a2 * N.h0 - N.a0 + N.a2)
    (hq2 : 0 < -N.a2 - N.h2 + 1)
    (hs1 : 0 < -N.s + 1)
    (hz₁ : [⟪x 5, (x 1 - x 5)⟫, ⟪x 0, (x 1 - x 5)⟫, ⟪x 3, (x 1 - x 5)⟫, ⟪x 4, (x 1 - x 5)⟫].Nodup)
    (hz₂ : [⟪x 1, (x 1 - x 5)⟫, ⟪x 0, (x 1 - x 5)⟫, ⟪x 3, (x 1 - x 5)⟫, ⟪x 4, (x 1 - x 5)⟫].Nodup) :
    RimCertThen (univ.image x) (x 1 - x 5)
      (NoHDNAt ((univ.image x).erase (x 1)) (x 1 - x 5) ∧
        NoHDNAt ((univ.image x).erase (x 5)) (x 1 - x 5)) := by
  have hA0 : 0 < -N.a0 := by linarith [N.ha0]
  have h345_0 : 0 < 1 - N.a0 - N.b0 - N.h0 := by linarith [N.t345_0]
  have hst : 0 < N.s + N.t - 1 := by linarith [N.hst]
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  refine edgePairσ_both (univ.image x) hσ (img29 5) (img29 1) (img29 0) (img29 4) (img29 3)
    ?_ ?_ ?_ ?_ ?_ hz₁ hz₂ ?_
  · nf29_test N hσD hA0
  · nf29_test N hσD (by show 0 < -N.a0 - N.h0 + 1; linarith [hb0, h345_0])
  · nf29_test N hσD (by norm_num : (0 : ℝ) < 1)
  · nf29_test N hσD N.hh0
  · nf29_simp N
    refine nf_E_le rfl rfl ?_
    have hE1 : 0 ≤ -N.a0 - N.b0 - N.h0 + 1 := by
      linarith [h345_0]
    have hE2 : -N.b0 ≤ 0 := by
      linarith [hb0]
    simp only [det3c]
    linarith [mul_nonpos_of_nonneg_of_nonpos hE1 hE2]
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    fin_cases i
    · exact Or.inr <| Or.inr <| Or.inl rfl
    · exact Or.inr <| Or.inl rfl
    · refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨?_, ?_, ?_, ?_⟩
      · nf29_test N hσD N.hF5
      · nf29_test N hσD hq1
      · nf29_test N hσD hq2
      · nf29_test N hσD N.hh2
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
    · exact Or.inl rfl
    · obtain ⟨s, δ, h1, h2, h3, h4⟩ := mid_comb' (m := x 6) (X := x 4) (Y := x 5) (U := x 5 - x 1)
        (D₀ := 1) (α := -N.s + 1) (β := N.s + N.t - 1)
        (by norm_num) (by linarith [hs1]) (by linarith [N.hs]) (by linarith [hst]) (by nf29_vec N)
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
          ⟨s, δ, h1, h2, h3, Or.inr <| Or.inl (h4.trans (by module))⟩

/-- **C1 tier** (Theorem P, Lemma E at the quad edge `5 → 1` of `O`). -/
theorem NF29.isRupert_k3_E51s (N : NF29 x)
    (hb0 : 0 < N.b0)
    (hq1 : 0 < N.a0 * N.h2 - N.a2 * N.h0 - N.a0 + N.a2)
    (hq2 : 0 < -N.a2 - N.h2 + 1)
    (hs1 : 0 < -N.s + 1)
    (hz₁ : [⟪x 5, (x 1 - x 5)⟫, ⟪x 0, (x 1 - x 5)⟫, ⟪x 3, (x 1 - x 5)⟫, ⟪x 4, (x 1 - x 5)⟫].Nodup)
    (hz₂ : [⟪x 1, (x 1 - x 5)⟫, ⟪x 0, (x 1 - x 5)⟫, ⟪x 3, (x 1 - x 5)⟫, ⟪x 4, (x 1 - x 5)⟫].Nodup)
    (hnd₁ : NoHDNAt ((univ.image x).erase (x 1)) (x 1 - x 5))
    (hnd₂ : NoHDNAt ((univ.image x).erase (x 5)) (x 1 - x 5)) : IsRupert (univ.image x) := by
  exact (NF29.rimThen_k3_E51s N hb0 hq1 hq2 hs1 hz₁ hz₂).2 ⟨hnd₁, hnd₂⟩

/-- Certificate form of `NF29.isRupert_k3_E51l`
(`FEWER-FACES-PROOFS.md` §18.2, §21): the rim at its named view as `RimCertPts`
(or `RimCert`), without the `NoHDNAt` hypotheses, which only enter the corollary. -/
theorem NF29.rimThen_k3_E51l (N : NF29 x)
    (hA2 : 0 < -N.a2)
    (hb0 : 0 < N.b0)
    (hq1 : 0 < N.a0 * N.h2 - N.a2 * N.h0 - N.a0 + N.a2)
    (hs1g : 0 < N.s - 1)
    (hz₁ : [⟪x 5, (x 1 - x 5)⟫, ⟪x 0, (x 1 - x 5)⟫, ⟪x 3, (x 1 - x 5)⟫, ⟪x 6, (x 1 - x 5)⟫].Nodup)
    (hz₂ : [⟪x 1, (x 1 - x 5)⟫, ⟪x 0, (x 1 - x 5)⟫, ⟪x 3, (x 1 - x 5)⟫, ⟪x 6, (x 1 - x 5)⟫].Nodup) :
    RimCertThen (univ.image x) (x 1 - x 5)
      (NoHDNAt ((univ.image x).erase (x 1)) (x 1 - x 5) ∧
        NoHDNAt ((univ.image x).erase (x 5)) (x 1 - x 5)) := by
  have hA0 : 0 < -N.a0 := by linarith [N.ha0]
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  refine edgePairσ_both (univ.image x) hσ (img29 5) (img29 1) (img29 0) (img29 6) (img29 3)
    ?_ ?_ ?_ ?_ ?_ hz₁ hz₂ ?_
  · nf29_test N hσD hA0
  · nf29_test N hσD (by
          show 0 < -N.h0 * N.s - N.a0 + N.s
          linarith [hb0, N.d035, mul_pos (hA0) N.ht, mul_pos (hb0) hs1g])
  · nf29_test N hσD N.hs
  · nf29_test N hσD (by show 0 < N.h0 * N.s; linarith [mul_pos (N.hh0) N.hs])
  · nf29_simp N
    refine nf_E_le rfl rfl ?_
    have hE1 : 0 ≤ N.a0 * N.t - N.b0 * N.s - N.h0 * N.s - N.a0 + N.s := by
      linarith [N.d035]
    have hE2 : N.a0 * N.t - N.b0 * N.s ≤ 0 := by
      linarith [(by
              show 0 < -N.a0 * N.t + N.b0 * N.s
              linarith [mul_pos (N.hs) hb0, mul_pos (hA0) N.ht])]
    simp only [det3c]
    linarith [mul_nonpos_of_nonneg_of_nonpos hE1 hE2]
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    fin_cases i
    · exact Or.inr <| Or.inr <| Or.inl rfl
    · exact Or.inr <| Or.inl rfl
    · refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨?_, ?_, ?_, ?_⟩
      · nf29_test N hσD N.hF5
      · nf29_test N hσD hq1
      · nf29_test N hσD (pos_of_mul_pos_r hA0
              (by
                show 0 < (-N.h2 * N.s - N.a2 + N.s) * (-N.a0)
                linarith [mul_pos (hA2) hb0, mul_pos (N.hs) hq1, mul_pos (N.d035) hA2, mul_pos
                    (mul_pos (hA0) N.ht) hA2, mul_pos (mul_pos (hA2) hb0) hs1g]))
      · nf29_test N hσD (by show 0 < N.h2 * N.s; linarith [mul_pos (N.hh2) N.hs])
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
    · obtain ⟨s, δ, h1, h2, h3, h4⟩ := mid_comb' (m := x 4) (X := x 6) (Y := x 1) (U := x 1 - x 5)
        (D₀ := N.s) (α := N.s - 1) (β := N.t)
        (by linarith [N.hs]) (by linarith [hs1g]) (by norm_num) (by linarith [N.ht]) (by nf29_vec N)
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
          ⟨s, δ, h1, h2, h3, Or.inr <| Or.inr <| Or.inr (h4.trans (by module))⟩
    · exact Or.inl rfl
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inl rfl

/-- **C1 tier** (Theorem P, Lemma E at the quad edge `5 → 1` of `O`). -/
theorem NF29.isRupert_k3_E51l (N : NF29 x)
    (hA2 : 0 < -N.a2)
    (hb0 : 0 < N.b0)
    (hq1 : 0 < N.a0 * N.h2 - N.a2 * N.h0 - N.a0 + N.a2)
    (hs1g : 0 < N.s - 1)
    (hz₁ : [⟪x 5, (x 1 - x 5)⟫, ⟪x 0, (x 1 - x 5)⟫, ⟪x 3, (x 1 - x 5)⟫, ⟪x 6, (x 1 - x 5)⟫].Nodup)
    (hz₂ : [⟪x 1, (x 1 - x 5)⟫, ⟪x 0, (x 1 - x 5)⟫, ⟪x 3, (x 1 - x 5)⟫, ⟪x 6, (x 1 - x 5)⟫].Nodup)
    (hnd₁ : NoHDNAt ((univ.image x).erase (x 1)) (x 1 - x 5))
    (hnd₂ : NoHDNAt ((univ.image x).erase (x 5)) (x 1 - x 5)) : IsRupert (univ.image x) := by
  exact (NF29.rimThen_k3_E51l N hA2 hb0 hq1 hs1g hz₁ hz₂).2 ⟨hnd₁, hnd₂⟩

/-- The genericity of the C1 tiers of class K4a (Theorem P, Lemma E at the quad edges `2 → 4`, `4 →
1`, `5 → 1`, `1 → 5` of `O`): `s, t ≠ 1`, distinct depths on the closings, no horizontal double
normal at the edge views. -/
structure K4C1Gen (N : NF29 x) : Prop where
  t1 : N.t ≠ 1
  s1 : N.s ≠ 1
  z24a : [⟪x 2, (x 4 - x 2)⟫, ⟪x 3, (x 4 - x 2)⟫, ⟪x 0, (x 4 - x 2)⟫, ⟪x 1, (x 4 - x 2)⟫].Nodup
  z24b : [⟪x 4, (x 4 - x 2)⟫, ⟪x 3, (x 4 - x 2)⟫, ⟪x 0, (x 4 - x 2)⟫, ⟪x 1, (x 4 - x 2)⟫].Nodup
  n24a : NoHDNAt ((univ.image x).erase (x 4)) (x 4 - x 2)
  n24b : NoHDNAt ((univ.image x).erase (x 2)) (x 4 - x 2)
  z41sa : [⟪x 4, (x 1 - x 4)⟫, ⟪x 5, (x 1 - x 4)⟫, ⟪x 3, (x 1 - x 4)⟫, ⟪x 2, (x 1 - x 4)⟫].Nodup
  z41sb : [⟪x 1, (x 1 - x 4)⟫, ⟪x 5, (x 1 - x 4)⟫, ⟪x 3, (x 1 - x 4)⟫, ⟪x 2, (x 1 - x 4)⟫].Nodup
  n41sa : NoHDNAt ((univ.image x).erase (x 1)) (x 1 - x 4)
  n41sb : NoHDNAt ((univ.image x).erase (x 4)) (x 1 - x 4)
  z41la : [⟪x 4, (x 1 - x 4)⟫, ⟪x 6, (x 1 - x 4)⟫, ⟪x 3, (x 1 - x 4)⟫, ⟪x 2, (x 1 - x 4)⟫].Nodup
  z41lb : [⟪x 1, (x 1 - x 4)⟫, ⟪x 6, (x 1 - x 4)⟫, ⟪x 3, (x 1 - x 4)⟫, ⟪x 2, (x 1 - x 4)⟫].Nodup
  n41la : NoHDNAt ((univ.image x).erase (x 1)) (x 1 - x 4)
  n41lb : NoHDNAt ((univ.image x).erase (x 4)) (x 1 - x 4)
  z51sa : [⟪x 5, (x 1 - x 5)⟫, ⟪x 0, (x 1 - x 5)⟫, ⟪x 3, (x 1 - x 5)⟫, ⟪x 4, (x 1 - x 5)⟫].Nodup
  z51sb : [⟪x 1, (x 1 - x 5)⟫, ⟪x 0, (x 1 - x 5)⟫, ⟪x 3, (x 1 - x 5)⟫, ⟪x 4, (x 1 - x 5)⟫].Nodup
  n51sa : NoHDNAt ((univ.image x).erase (x 1)) (x 1 - x 5)
  n51sb : NoHDNAt ((univ.image x).erase (x 5)) (x 1 - x 5)
  z51la : [⟪x 5, (x 1 - x 5)⟫, ⟪x 0, (x 1 - x 5)⟫, ⟪x 3, (x 1 - x 5)⟫, ⟪x 6, (x 1 - x 5)⟫].Nodup
  z51lb : [⟪x 1, (x 1 - x 5)⟫, ⟪x 0, (x 1 - x 5)⟫, ⟪x 3, (x 1 - x 5)⟫, ⟪x 6, (x 1 - x 5)⟫].Nodup
  n51la : NoHDNAt ((univ.image x).erase (x 1)) (x 1 - x 5)
  n51lb : NoHDNAt ((univ.image x).erase (x 5)) (x 1 - x 5)
  z15a : [⟪x 1, (x 5 - x 1)⟫, ⟪x 4, (x 5 - x 1)⟫, ⟪x 2, (x 5 - x 1)⟫, ⟪x 0, (x 5 - x 1)⟫].Nodup
  z15b : [⟪x 5, (x 5 - x 1)⟫, ⟪x 4, (x 5 - x 1)⟫, ⟪x 2, (x 5 - x 1)⟫, ⟪x 0, (x 5 - x 1)⟫].Nodup
  n15a : NoHDNAt ((univ.image x).erase (x 5)) (x 5 - x 1)
  n15b : NoHDNAt ((univ.image x).erase (x 1)) (x 5 - x 1)

/-- The genericity of the C1 tiers of class K3a (Theorem P, Lemma E at the quad edges `0 → 3`, `2 →
4`, `1 → 4`, `5 → 1` of `O`): `s ≠ 1`, distinct depths on the closings, no horizontal double normal
at the edge views. -/
structure K3C1Gen (N : NF29 x) : Prop where
  s1 : N.s ≠ 1
  z03a : [⟪x 0, (x 3 - x 0)⟫, ⟪x 5, (x 3 - x 0)⟫, ⟪x 1, (x 3 - x 0)⟫, ⟪x 2, (x 3 - x 0)⟫].Nodup
  z03b : [⟪x 3, (x 3 - x 0)⟫, ⟪x 5, (x 3 - x 0)⟫, ⟪x 1, (x 3 - x 0)⟫, ⟪x 2, (x 3 - x 0)⟫].Nodup
  n03a : NoHDNAt ((univ.image x).erase (x 3)) (x 3 - x 0)
  n03b : NoHDNAt ((univ.image x).erase (x 0)) (x 3 - x 0)
  z24a : [⟪x 2, (x 4 - x 2)⟫, ⟪x 3, (x 4 - x 2)⟫, ⟪x 0, (x 4 - x 2)⟫, ⟪x 1, (x 4 - x 2)⟫].Nodup
  z24b : [⟪x 4, (x 4 - x 2)⟫, ⟪x 3, (x 4 - x 2)⟫, ⟪x 0, (x 4 - x 2)⟫, ⟪x 1, (x 4 - x 2)⟫].Nodup
  n24a : NoHDNAt ((univ.image x).erase (x 4)) (x 4 - x 2)
  n24b : NoHDNAt ((univ.image x).erase (x 2)) (x 4 - x 2)
  z14a : [⟪x 1, (x 4 - x 1)⟫, ⟪x 2, (x 4 - x 1)⟫, ⟪x 0, (x 4 - x 1)⟫, ⟪x 5, (x 4 - x 1)⟫].Nodup
  z14b : [⟪x 4, (x 4 - x 1)⟫, ⟪x 2, (x 4 - x 1)⟫, ⟪x 0, (x 4 - x 1)⟫, ⟪x 5, (x 4 - x 1)⟫].Nodup
  n14a : NoHDNAt ((univ.image x).erase (x 4)) (x 4 - x 1)
  n14b : NoHDNAt ((univ.image x).erase (x 1)) (x 4 - x 1)
  z51sa : [⟪x 5, (x 1 - x 5)⟫, ⟪x 0, (x 1 - x 5)⟫, ⟪x 3, (x 1 - x 5)⟫, ⟪x 4, (x 1 - x 5)⟫].Nodup
  z51sb : [⟪x 1, (x 1 - x 5)⟫, ⟪x 0, (x 1 - x 5)⟫, ⟪x 3, (x 1 - x 5)⟫, ⟪x 4, (x 1 - x 5)⟫].Nodup
  n51sa : NoHDNAt ((univ.image x).erase (x 1)) (x 1 - x 5)
  n51sb : NoHDNAt ((univ.image x).erase (x 5)) (x 1 - x 5)
  z51la : [⟪x 5, (x 1 - x 5)⟫, ⟪x 0, (x 1 - x 5)⟫, ⟪x 3, (x 1 - x 5)⟫, ⟪x 6, (x 1 - x 5)⟫].Nodup
  z51lb : [⟪x 1, (x 1 - x 5)⟫, ⟪x 0, (x 1 - x 5)⟫, ⟪x 3, (x 1 - x 5)⟫, ⟪x 6, (x 1 - x 5)⟫].Nodup
  n51la : NoHDNAt ((univ.image x).erase (x 1)) (x 1 - x 5)
  n51lb : NoHDNAt ((univ.image x).erase (x 5)) (x 1 - x 5)


/-- **Theorem 21.11 with Theorem P: class K4a.**  Let `K` be of type 29 in normal coordinates
with `O` of class K4a (`a2, b0 > 0`, `V < 0`).  If one of the E-good `G` edges `2 → 4`, `4 → 1`,
`5 → 1`, `1 → 5` is a quad edge of `O`, Lemma E holds at it for `K` (clause C1 of Theorem P,
in coordinates); otherwise `O ∈ R_G` and Theorem 21.11 applies.  Off the special positions and
with the genericity of the named tests (`K4Gen`, `K4C1Gen`), `K` is Rupert. -/
theorem NF29.isRupert_K4a_all (N : NF29 x) (ha2 : 0 < N.a2) (hb0 : 0 < N.b0)
    (hV : N.h0 * (1 - N.a2 - N.b2) - N.h2 * (1 - N.a0 - N.b0) < 0) (G : K4Gen N)
    (G1 : K4C1Gen N) : IsRupert (univ.image x) := by
  by_cases q24 : N.h0 < N.h0 * N.a2 - N.h2 * N.a0 ∧
      1 - N.a0 - N.b0 - N.h0 < -((N.b0 - 1 + N.h0) * N.a2 - N.a0 * N.b2 + N.a0 * (1 - N.h2))
  · have q := q24
    exact N.isRupert_k4_E24 hb0 (by linarith [q.1] : 0 < -N.a0 * N.h2 + N.a2 * N.h0 - N.h0)
        (by
          linarith [q.2] : 0 < N.a0 * N.b2 + N.a0 * N.h2 - N.a2 * N.b0 - N.a2 * N.h0 + N.a2 + N.b0 +
            N.h0 - 1) G1.z24a G1.z24b G1.n24a G1.n24b
  by_cases q41 : 0 < N.b0 * (1 - N.h2) - N.b2 * (1 - N.h0) ∧ N.b0 + N.h0 < 1
  · have q := q41
    rcases lt_or_gt_of_ne G1.t1 with ht0 | ht0
    · have ht : 0 < -N.t + 1 := by linarith
      exact N.isRupert_k4_E41s ha2
          (by linarith [q.1] : 0 < -N.b0 * N.h2 + N.b2 * N.h0 + N.b0 - N.b2)
          (by linarith [q.2] : 0 < -N.b0 - N.h0 + 1) ht G1.z41sa G1.z41sb G1.n41sa G1.n41sb
    · have ht : 0 < N.t - 1 := by linarith
      exact N.isRupert_k4_E41l ha2 hb0
          (by linarith [q.1] : 0 < -N.b0 * N.h2 + N.b2 * N.h0 + N.b0 - N.b2)
          (by linarith [q.2] : 0 < -N.b0 - N.h0 + 1) ht G1.z41la G1.z41lb G1.n41la G1.n41lb
  by_cases q51 : 0 < N.a2 * (1 - N.h0) - N.a0 * (1 - N.h2) ∧ N.a2 + N.h2 < 1
  · have q := q51
    rcases lt_or_gt_of_ne G1.s1 with hs0 | hs0
    · have hs : 0 < -N.s + 1 := by linarith
      exact N.isRupert_k4_E51s hb0 (by linarith [q.1] : 0 < N.a0 * N.h2 - N.a2 * N.h0 - N.a0 + N.a2)
          (by linarith [q.2] : 0 < -N.a2 - N.h2 + 1) hs G1.z51sa G1.z51sb G1.n51sa G1.n51sb
    · have hs : 0 < N.s - 1 := by linarith
      exact N.isRupert_k4_E51l ha2 hb0
          (by linarith [q.1] : 0 < N.a0 * N.h2 - N.a2 * N.h0 - N.a0 + N.a2)
          (by linarith [q.2] : 0 < -N.a2 - N.h2 + 1) hs G1.z51la G1.z51lb G1.n51la G1.n51lb
  by_cases q15 : N.a2 * (1 - N.h0) - N.a0 * (1 - N.h2) < 0 ∧ 1 < N.a2 + N.h2
  · have q := q15
    exact N.isRupert_k4_E15
        (by linarith : 0 < -N.a0 * N.h2 + N.a2 * N.h0 - N.b0 * N.h2 + N.b2 * N.h0 - N.h0 + N.h2)
        (by linarith [q.1] : 0 < -N.a0 * N.h2 + N.a2 * N.h0 + N.a0 - N.a2)
        (by linarith [q.2] : 0 < N.a2 + N.h2 - 1) G1.z15a G1.z15b G1.n15a G1.n15b
  exact N.isRupert_K4a ha2 hb0 hV q24 q41 q51 q15 G

/-- **Class K4b** (`σ` of K4a): `a2, b0 > 0`, `V > 0`; with the genericity of the `σ`-image, `K`
is Rupert. -/
theorem NF29.isRupert_K4b_all (N : NF29 x) (ha2 : 0 < N.a2) (hb0 : 0 < N.b0)
    (hV : 0 < N.h0 * (1 - N.a2 - N.b2) - N.h2 * (1 - N.a0 - N.b0)) (G : K4Gen N.sigma)
    (G1 : K4C1Gen N.sigma) : IsRupert (univ.image x) := by
  have h := NF29.isRupert_K4a_all N.sigma hb0 ha2 (by simp only [NF29.sigma]; linarith) G G1
  rwa [image_sigma29] at h

/-- **Theorem 21.22 with Theorem P: class K3a.**  Let `K` be of type 29 in normal coordinates
with `O` of class K3a (`a2 < 0 < b0`, `V > 0`).  If one of the E-good `G` edges `0 → 3`, `2 → 4`,
`1 → 4`, `5 → 1` is a quad edge of `O`, Lemma E holds at it for `K` (clause C1 of Theorem P, in
coordinates); otherwise `O ∈ R_G` and Theorem 21.22 applies.  Off the special positions and with
the genericity of the named tests (`K3Gen`, `K3C1Gen`), `K` is Rupert. -/
theorem NF29.isRupert_K3a_all (N : NF29 x) (ha2 : N.a2 < 0) (hb0 : 0 < N.b0)
    (hV : 0 < N.h0 * (1 - N.a2 - N.b2) - N.h2 * (1 - N.a0 - N.b0)) (G : K3Gen N)
    (G1 : K3C1Gen N) : IsRupert (univ.image x) := by
  by_cases q03 : -N.b2 < N.h2 * N.b0 - N.h0 * N.b2 ∧ 1 < N.h0
  · have q := q03
    exact N.isRupert_k3_E03 (by linarith : 0 < -N.a2)
        (by linarith [q.1] : 0 < N.b0 * N.h2 - N.b2 * N.h0 + N.b2)
        (by linarith [q.2] : 0 < N.h0 - 1) G1.z03a G1.z03b G1.n03a G1.n03b
  by_cases q24 : N.h0 < N.h0 * N.a2 - N.h2 * N.a0 ∧
      1 - N.a0 - N.b0 - N.h0 < -((N.b0 - 1 + N.h0) * N.a2 - N.a0 * N.b2 + N.a0 * (1 - N.h2))
  · have q := q24
    exact N.isRupert_k3_E24 hb0
        (by linarith : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2)
        (by linarith [q.1] : 0 < -N.a0 * N.h2 + N.a2 * N.h0 - N.h0)
        (by
          linarith [q.2] : 0 < N.a0 * N.b2 + N.a0 * N.h2 - N.a2 * N.b0 - N.a2 * N.h0 + N.a2 + N.b0 +
            N.h0 - 1) G1.z24a G1.z24b G1.n24a G1.n24b
  by_cases q14 : N.b0 * (1 - N.h2) - N.b2 * (1 - N.h0) < 0 ∧ 1 < N.b0 + N.h0
  · have q := q14
    exact N.isRupert_k3_E14
        (by linarith : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2)
        (by linarith [q.1] : 0 < N.b0 * N.h2 - N.b2 * N.h0 - N.b0 + N.b2)
        (by linarith [q.2] : 0 < N.b0 + N.h0 - 1) G1.z14a G1.z14b G1.n14a G1.n14b
  by_cases q51 : 0 < N.a2 * (1 - N.h0) - N.a0 * (1 - N.h2) ∧ N.a2 + N.h2 < 1
  · have q := q51
    rcases lt_or_gt_of_ne G1.s1 with hs0 | hs0
    · have hs : 0 < -N.s + 1 := by linarith
      exact N.isRupert_k3_E51s hb0 (by linarith [q.1] : 0 < N.a0 * N.h2 - N.a2 * N.h0 - N.a0 + N.a2)
          (by linarith [q.2] : 0 < -N.a2 - N.h2 + 1) hs G1.z51sa G1.z51sb G1.n51sa G1.n51sb
    · have hs : 0 < N.s - 1 := by linarith
      exact N.isRupert_k3_E51l (by linarith : 0 < -N.a2) hb0
          (by linarith [q.1] : 0 < N.a0 * N.h2 - N.a2 * N.h0 - N.a0 + N.a2) hs G1.z51la G1.z51lb
          G1.n51la G1.n51lb
  exact N.isRupert_K3a ha2 hb0 hV q03 q24 q14 q51 G

/-- **Class K3b** (`σ` of K3a): `a2 > 0 > b0`, `V < 0`; with the genericity of the `σ`-image, `K`
is Rupert. -/
theorem NF29.isRupert_K3b_all (N : NF29 x) (ha2 : 0 < N.a2) (hb0 : N.b0 < 0)
    (hV : N.h0 * (1 - N.a2 - N.b2) - N.h2 * (1 - N.a0 - N.b0) < 0) (G : K3Gen N.sigma)
    (G1 : K3C1Gen N.sigma) : IsRupert (univ.image x) := by
  have h := NF29.isRupert_K3a_all N.sigma hb0 ha2 (by simp only [NF29.sigma]; linarith) G G1
  rwa [image_sigma29] at h

end Minimality

end
