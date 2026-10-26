module

public import Minimality.Type29CertK3
public import Minimality.Type29CertK4

@[expose] public section

/-!
# Type 29: the K3a / K4a covers as certificates (`FEWER-FACES-PROOFS.md` §28, §21.2, §21.11)

The covers of Theorems 21.11 and 21.22 with Theorem P (C1 tier), stated as "there is a
certificate": `NF29.cert29_K3a_all` and `NF29.cert29_K4a_all` conclude `Cert29 x` (`Type29Cert`:
a labelled rim certificate at a named view with its closed region facts, or an edge pair of Lemma
E).  Hypotheses: the class (`a2 < 0 < b0`, `V > 0`, resp. `a2, b0 > 0`, `V < 0`), the polynomial
genericity (`K3Poly`, `K4Poly`, `K3C1Poly`, `K4C1Poly`: avoided by the approximants of §22), and
the ties allowed (`Tie29`: at most one tied pair at each named view, none at one view of each
combined pair).  Depth ties and horizontal double normals no longer appear: they are checked at
the limit (`Cert29`).  `K3b`, `K4b` are the `σ`-images (`x ∘ σ29`, `NF29.sigma`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Minimality

open scoped RealInnerProductSpace
open Finset

variable {x : Fin 7 → ℝ³}

/-- The polynomial genericity of class K3a (Theorem 21.22): the nonvanishing of the fields of
`K3Gen` that are not depth ties or horizontal double normals.  (Each is a polynomial
condition on the shape, avoided by the approximants of §22.) -/
structure K3Poly (N : NF29 x) : Prop where
  h0 : N.h0 ≠ 1
  G4 : N.b0 * (1 - N.h2) - N.b2 * (1 - N.h0) ≠ 0
  G5 : N.a2 * (1 - N.h0) - N.a0 * (1 - N.h2) ≠ 0
  F : N.h2 * N.b0 - N.h0 * N.b2 ≠ N.h0 * N.a2 - N.h2 * N.a0
  th : -N.a2 * N.t + N.b2 * N.s ≠ 0
  f : -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s - N.b0 * N.h2 +
      N.b2 * N.h0 ≠ 0
  t1 : N.t ≠ 1
  h21 : N.h2 ≠ 1
  kap : -N.a2 - N.h2 + 1 ≠ 0
  F5h0 : N.h0 * N.a2 - N.h2 * N.a0 ≠ N.h0
  F4h2 : N.h2 * N.b0 - N.h0 * N.b2 ≠ N.h2
  sg : N.a2 * N.t - N.b2 * N.s + N.h2 * N.t - N.a2 - N.h2 - N.t + 1 ≠ 0
  c0 : N.a0 * N.b2 - N.a2 * N.b0 - N.a2 * N.h0 - N.b0 * N.h2 - N.h0 * N.h2 + N.a2 + N.b0 + N.h0 +
      N.h2 - 1 ≠ 0
  Xf : -N.a0 * N.t + N.b0 * N.s - N.h0 * N.t - N.b0 - N.s + 1 ≠ 0
  hs : N.h0 * N.s + N.a0 ≠ 0
  L36 : -N.a0 * N.h2 * N.t + N.b2 * N.h0 * N.s + N.h0 * N.h2 * N.s + N.a0 * N.h2 ≠ 0

/-- The polynomial genericity of class K4a (Theorem 21.11). -/
structure K4Poly (N : NF29 x) : Prop where
  e0 : N.b0 + N.h0 ≠ 1
  e2 : N.a2 + N.h2 ≠ 1
  h0 : N.h0 ≠ 1
  ah : N.a0 + N.h0 ≠ 0
  c2 : -((N.b0 - 1 + N.h0) * N.a2 - N.a0 * N.b2 + N.a0 * (1 - N.h2)) ≠ 1 - N.a0 - N.b0 - N.h0

/-- The polynomial genericity of the C1 tiers of K3a (`s ≠ 1`). -/
structure K3C1Poly (N : NF29 x) : Prop where
  s1 : N.s ≠ 1

/-- The polynomial genericity of the C1 tiers of K4a (`s, t ≠ 1`). -/
structure K4C1Poly (N : NF29 x) : Prop where
  t1 : N.t ≠ 1
  s1 : N.s ≠ 1

/-- **Theorem 21.13** (`6 ∉ R`), certificate form. -/
theorem NF29.cert_k3_notR (N : NF29 x)
    (hA2 : 0 < -N.a2)
    (hb0 : 0 < N.b0)
    (hV3 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2)
    (hh01 : 0 < -N.h0 + 1)
    (hG4 : 0 < -N.b0 * N.h2 + N.b2 * N.h0 + N.b0 - N.b2)
    (hG5n : 0 < -N.a0 * N.h2 + N.a2 * N.h0 + N.a0 - N.a2)
    (hF45 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0)
    (hh20 : 0 < -N.h0 + N.h2)
    (hnR : ¬ (0 < -N.a2 * N.t + N.b2 * N.s ∧ 0 < -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 *
            N.h2 * N.s - N.b2 * N.h0 * N.s - N.b0 * N.h2 + N.b2 * N.h0)) (G : K3Poly N) (htie :
                Tie29 x) : Cert29 x := by
  have oT1 : OneTieAt (univ.image x) N.vT1 :=
    (htie.one _ N.view_T1_ne).of_eq_smul N.vT1_eq N.hDi
  have oT2 : OneTieAt (univ.image x) N.vT2 :=
    (htie.one _ N.view_T2_ne).of_eq_smul N.vT2_eq N.hDni
  have oT3 : OneTieAt (univ.image x) N.vT3 :=
    (htie.one _ N.view_T3_ne).of_eq_smul N.vT3_eq N.hDi
  have oY1 : OneTieAt (univ.image x) N.vY1 :=
    (htie.one _ N.view_Y1_ne).of_eq_smul N.vY1_eq N.hDni
  have hA0 : 0 < -N.a0 := by linarith [N.ha0]
  have hB2 : 0 < -N.b2 := by linarith [N.hb2]
  have h345_0 : 0 < 1 - N.a0 - N.b0 - N.h0 := by linarith [N.t345_0]
  have h345_2 : 0 < 1 - N.a2 - N.b2 - N.h2 := by linarith [N.t345_2]
  have hE35 : 0 < -((N.b0 - 1 + N.h0) * N.a2 - N.a0 * N.b2 + N.a0 * (1 - N.h2)) :=
      by linarith [N.hE35]
  have hst : 0 < N.s + N.t - 1 := by linarith [N.hst]
  rcases lt_or_gt_of_ne G.th with hth0 | hth0
  · have hthn : 0 < N.a2 * N.t - N.b2 * N.s := by linarith
    rcases lt_or_gt_of_ne G.t1 with ht0 | ht0
    · have ht1 : 0 < -N.t + 1 := by linarith
      have hfF5 : 0 < -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s
          + N.a0 * N.h2 - N.a2 * N.h0 := by
        linarith [mul_pos (N.hF5) hst, mul_pos (N.hs) hF45]
      have hgG5 : 0 < N.a0 * N.h2 * N.t - N.a2 * N.h0 * N.t - N.b0 * N.h2 * N.s + N.b2 * N.h0 * N.s
          - N.a0 * N.h2 - N.a0 * N.t + N.a2 * N.h0 + N.a2 * N.t + N.b0 * N.s - N.b2 * N.s + N.a0 -
          N.a2 := by
        linarith [mul_pos (hG5n) ht1, mul_pos (N.hs) hG4]
      exact N.cert_k3_C56 hA2 hV3 hthn ht1 hfF5 hgG5
                (N.edgeW htie (i := 6) (j := 5) (by decide) (by decide) (by decide) (by decide))
    · have ht1g : 0 < N.t - 1 := by linarith
      have he0n : 0 < -N.b0 - N.h0 + 1 := by
        by_contra hc; push Not at hc
        have hneg : 0 ≤ N.b0 + N.h0 - 1 := by linarith
        linarith [N.d035, mul_pos (hA0) ht1g, mul_nonneg (N.hs).le hneg]
      exact N.cert_k3_C14 hb0 hG4 hthn ht1g he0n
                (N.edgeW htie (i := 4) (j := 1) (by decide) (by decide) (by decide) (by decide))
  · have hth : 0 < -N.a2 * N.t + N.b2 * N.s := by linarith
    have hfn : 0 < N.a0 * N.h2 * N.t - N.a2 * N.h0 * N.t - N.b0 * N.h2 * N.s + N.b2 * N.h0 * N.s +
        N.b0 * N.h2 - N.b2 * N.h0 := by
      rcases lt_or_gt_of_ne G.f with h | h
      · linarith
      · exact absurd ⟨hth, h⟩ hnR
    have hs1 : 0 < -N.s + 1 := by
      by_contra hc; push Not at hc
      have hneg : 0 ≤ N.s - 1 := by linarith
      linarith [hfn, mul_pos (N.hF5) hst, mul_nonneg (hV3).le hneg, mul_nonneg (hh20).le hneg]
    exact N.cert_k3_C46 hb0 hG4 hG5n hth hfn hs1
                (N.edgeW htie (i := 4) (j := 6) (by decide) (by decide) (by decide) (by decide))

/-- **Theorem 21.15 (i)**, certificate form. -/
theorem NF29.cert_k3_i (N : NF29 x)
    (hA2 : 0 < -N.a2)
    (hb0 : 0 < N.b0)
    (hV3 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2)
    (hh01 : 0 < -N.h0 + 1)
    (hG4 : 0 < -N.b0 * N.h2 + N.b2 * N.h0 + N.b0 - N.b2)
    (hG5n : 0 < -N.a0 * N.h2 + N.a2 * N.h0 + N.a0 - N.a2)
    (hF45 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0)
    (hh20 : 0 < -N.h0 + N.h2)
    (hth : 0 < -N.a2 * N.t + N.b2 * N.s)
        (hf : 0 < -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s -
          N.b0 * N.h2 + N.b2 * N.h0)
    (hh21 : 0 < -N.h2 + 1) (G : K3Poly N) (htie : Tie29 x) : Cert29 x := by
  have oT1 : OneTieAt (univ.image x) N.vT1 :=
    (htie.one _ N.view_T1_ne).of_eq_smul N.vT1_eq N.hDi
  have oT2 : OneTieAt (univ.image x) N.vT2 :=
    (htie.one _ N.view_T2_ne).of_eq_smul N.vT2_eq N.hDni
  have oT3 : OneTieAt (univ.image x) N.vT3 :=
    (htie.one _ N.view_T3_ne).of_eq_smul N.vT3_eq N.hDi
  have oY1 : OneTieAt (univ.image x) N.vY1 :=
    (htie.one _ N.view_Y1_ne).of_eq_smul N.vY1_eq N.hDni
  have hA0 : 0 < -N.a0 := by linarith [N.ha0]
  have hB2 : 0 < -N.b2 := by linarith [N.hb2]
  have h345_0 : 0 < 1 - N.a0 - N.b0 - N.h0 := by linarith [N.t345_0]
  have h345_2 : 0 < 1 - N.a2 - N.b2 - N.h2 := by linarith [N.t345_2]
  have hE35 : 0 < -((N.b0 - 1 + N.h0) * N.a2 - N.a0 * N.b2 + N.a0 * (1 - N.h2)) :=
      by linarith [N.hE35]
  have hst : 0 < N.s + N.t - 1 := by linarith [N.hst]
  rcases lt_or_gt_of_ne G.sg with hs0 | hs0
  · have hsg : 0 < -N.a2 * N.t + N.b2 * N.s - N.h2 * N.t + N.a2 + N.h2 + N.t - 1 := by linarith
    have hx0 : 0 < -N.a0 * N.b2 + N.a2 * N.b0 + N.a2 * N.h0 + N.b0 * N.h2 + N.h0 * N.h2 - N.a2 -
        N.b0 - N.h0 - N.h2 + 1 := by
      by_contra hc; push Not at hc
      have hneg : 0 ≤ N.a0 * N.b2 - N.a2 * N.b0 - N.a2 * N.h0 - N.b0 * N.h2 - N.h0 * N.h2 + N.a2 +
          N.b0 + N.h0 + N.h2 - 1 := by linarith
      linarith [mul_pos (N.d035) hA2, mul_pos (hB2) N.d035, mul_pos (N.d035) hh21, mul_pos (h345_0)
            hsg, mul_nonneg (hst).le hneg]
    exact N.cert_k3_T2c hA2 hh01 hh21 hsg hx0
                (N.edge_weak oT2 (by decide) (by decide) (by decide))
          ⟨N, by linarith [hh20], by linarith [hh21]⟩
  · have hsg : 0 < N.a2 * N.t - N.b2 * N.s + N.h2 * N.t - N.a2 - N.h2 - N.t + 1 := by linarith
    rcases lt_or_gt_of_ne G.c0 with hc | hc
    · have hc0 : 0 < -N.a0 * N.b2 + N.a2 * N.b0 + N.a2 * N.h0 + N.b0 * N.h2 + N.h0 * N.h2 - N.a2 -
          N.b0 - N.h0 - N.h2 + 1 := by linarith
      exact N.cert_k3_T2b hA2 hh21 hsg hc0
                (N.edge_weak oT2 (by decide) (by decide) (by decide))
          ⟨N, by linarith [hh20], by linarith [hh21]⟩
    · have hc0 : 0 < N.a0 * N.b2 - N.a2 * N.b0 - N.a2 * N.h0 - N.b0 * N.h2 - N.h0 * N.h2 + N.a2 +
          N.b0 + N.h0 + N.h2 - 1 := by linarith
      exact N.cert_k3_P14 hA2 hb0 hh01 hG5n hF45 hh20 hth hf hh21 hsg hc0
                (htie.one _ N.view_T1_ne) (htie.one _ N.view_T2_ne)
                (htie.pair (.inr 0, .inr 1) (by decide) N.view_T1_ne N.view_T2_ne)

theorem NF29.cert_k3_open (N : NF29 x)
    (hA2 : 0 < -N.a2)
    (hb0 : 0 < N.b0)
    (hV3 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2)
    (hh01 : 0 < -N.h0 + 1)
    (hG4 : 0 < -N.b0 * N.h2 + N.b2 * N.h0 + N.b0 - N.b2)
    (hG5n : 0 < -N.a0 * N.h2 + N.a2 * N.h0 + N.a0 - N.a2)
    (hF45 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0)
    (hh20 : 0 < -N.h0 + N.h2)
    (hth : 0 < -N.a2 * N.t + N.b2 * N.s)
        (hf : 0 < -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s -
          N.b0 * N.h2 + N.b2 * N.h0)
    (hh2g : 0 < N.h2 - 1) (hkap : 0 < -N.a2 - N.h2 + 1)
    (n24 : ¬ (N.h0 < N.h0 * N.a2 - N.h2 * N.a0 ∧
      1 - N.a0 - N.b0 - N.h0 < -((N.b0 - 1 + N.h0) * N.a2 - N.a0 * N.b2 + N.a0 * (1 - N.h2))))
    (G : K3Poly N) (htie : Tie29 x) : Cert29 x := by
  have oT1 : OneTieAt (univ.image x) N.vT1 :=
    (htie.one _ N.view_T1_ne).of_eq_smul N.vT1_eq N.hDi
  have oT2 : OneTieAt (univ.image x) N.vT2 :=
    (htie.one _ N.view_T2_ne).of_eq_smul N.vT2_eq N.hDni
  have oT3 : OneTieAt (univ.image x) N.vT3 :=
    (htie.one _ N.view_T3_ne).of_eq_smul N.vT3_eq N.hDi
  have oY1 : OneTieAt (univ.image x) N.vY1 :=
    (htie.one _ N.view_Y1_ne).of_eq_smul N.vY1_eq N.hDni
  have hA0 : 0 < -N.a0 := by linarith [N.ha0]
  have hB2 : 0 < -N.b2 := by linarith [N.hb2]
  have h345_0 : 0 < 1 - N.a0 - N.b0 - N.h0 := by linarith [N.t345_0]
  have h345_2 : 0 < 1 - N.a2 - N.b2 - N.h2 := by linarith [N.t345_2]
  have hE35 : 0 < -((N.b0 - 1 + N.h0) * N.a2 - N.a0 * N.b2 + N.a0 * (1 - N.h2)) :=
      by linarith [N.hE35]
  have hst : 0 < N.s + N.t - 1 := by linarith [N.hst]
  -- Theorem 21.15 (iii): `h0 > F5`
  have hh0F5 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.h0 := by
    by_contra hc; push Not at hc
    have hlt : N.h0 < N.h0 * N.a2 - N.h2 * N.a0 := lt_of_le_of_ne (by linarith) (Ne.symm G.F5h0)
    rcases le_or_gt (N.h2 * N.b0 - N.h0 * N.b2) N.h2 with hle | hgt
    · linarith
    · have h := not_lt.mp fun h' => n24 ⟨hlt, h'⟩
      have hneg : 0 < -N.a0 * N.h2 + N.a2 * N.h0 - N.h0 := by linarith
      have hF4h2 : 0 < N.b0 * N.h2 - N.b2 * N.h0 - N.h2 := by linarith
      have hc2n : 0 ≤ -N.a0 * N.b2 - N.a0 * N.h2 + N.a2 * N.b0 + N.a2 * N.h0 - N.a2 - N.b0 - N.h0 +
          1 := by linarith
      linarith [mul_pos (hA2) hV3, mul_pos (hb0) hV3, mul_pos (hB2) hneg, mul_pos (hkap) hneg,
            mul_pos (N.hh0) hV3, mul_pos (h345_0) hV3, mul_pos (h345_0) hneg, mul_nonneg (N.hh2).le
            hc2n, mul_nonneg (N.hh0).le hc2n]
  rcases lt_or_gt_of_ne G.F4h2 with hF | hF
  · have hh2F4 : 0 < -N.b0 * N.h2 + N.b2 * N.h0 + N.h2 := by linarith
    have hb01 : 0 < -N.b0 + 1 := pos_of_mul_pos_r N.hh2 (by
      linarith [hh2F4, mul_pos (N.hh0) hB2])
    by_cases hQ : 0 < N.a0 * N.h2 * N.t - N.b2 * N.h0 * N.s + N.h0 * N.h2 * N.t + N.b2 * N.h0 ∧ 0 <
        -N.a0 * N.h2 * N.t + N.b2 * N.h0 * N.s + N.h0 * N.h2 * N.s + N.a0 * N.h2
    · obtain ⟨hq46, hq65⟩ := hQ
      exact N.cert_k3_T3p hh2g hh0F5 hh2F4 hq46 hq65 (N.planar_robust oT3)
    rcases lt_or_gt_of_ne G.Xf with hX | hX
    · have hXfn : 0 < N.a0 * N.t - N.b0 * N.s + N.h0 * N.t + N.b0 + N.s - 1 := by linarith
      rcases lt_or_gt_of_ne G.hs with hY | hY
      · have hAs : 0 < -N.h0 * N.s - N.a0 := by linarith
        have hAh0 : 0 < -N.a0 - N.h0 := by
          by_contra hc; push Not at hc
          have hneg : 0 ≤ N.a0 + N.h0 := by linarith
          linarith [mul_pos (hA0) hXfn, mul_pos (h345_0) hAs, mul_nonneg (N.d035).le hneg]
        have hs1g : 0 < N.s - 1 := pos_of_mul_pos_r hb01 (by
          linarith [hXfn, mul_pos (N.ht) hAh0])
        have hW43 : 0 < -N.a0 * N.h2 * N.t + N.b2 * N.h0 * N.s - N.h0 * N.h2 * N.t - N.b2 * N.h0 :=
            pos_of_mul_pos_r hA0 (by
              linarith [mul_pos (mul_pos (N.hh0) hB2) hAs, mul_pos (mul_pos (N.hh0) hth) hAh0,
                  mul_pos (mul_pos (N.hF5) N.ht) hAh0])
        have hsg : 0 < N.a2 * N.t - N.b2 * N.s + N.h2 * N.t - N.a2 - N.h2 - N.t + 1 :=
            pos_of_mul_pos_r hA0 (by
              linarith
                [mul_pos (N.hDG5) N.hs, mul_pos (N.d035) hkap,
                    mul_pos (mul_pos (h345_0) N.hs) hh2g])
        rcases lt_or_gt_of_ne G.L36 with hL | hL
        · have hL36n : 0 < N.a0 * N.h2 * N.t - N.b2 * N.h0 * N.s - N.h0 * N.h2 * N.s - N.a0 * N.h2
              := by linarith
          exact N.cert_k3_P13 hV3 hh01 hh2g hkap hh0F5 hh2F4 hsg hL36n hW43 hAh0 hs1g
                (htie.one _ N.view_T3_ne) (htie.one _ N.view_T2_ne)
                (htie.pair (.inr 3, .inr 1) (by decide) N.view_T3_ne N.view_T2_ne)
        · have hL36 : 0 < -N.a0 * N.h2 * N.t + N.b2 * N.h0 * N.s + N.h0 * N.h2 * N.s + N.a0 * N.h2
              := by linarith
          have hc4 : 0 < N.a0 * N.b2 - N.a2 * N.b0 - N.b0 * N.h2 + N.b2 * N.h0 - N.a0 + N.a2 - N.h0
              + N.h2 := pos_of_mul_pos_r hA0
              (by linarith [mul_pos (N.hDG5) hAh0, mul_pos (h345_0) N.hF5])
          exact N.cert_k3_Yp hb0 hV3 hh01 hG5n hh20 hh2g hkap hh0F5 hXfn hb01 hAs hL36 hW43 hAh0
              hs1g hc4
                (htie.one _ N.view_Y1_ne)
                (htie.one _ (N.seg_ne (i := 4) (j := 6) (by decide)))
      · have hYs : 0 < N.h0 * N.s + N.a0 := by linarith
        have hp56 : 0 < N.a2 * N.t - N.b2 * N.s - N.h2 * N.s - N.a2 + N.s := pos_of_mul_pos_r hA0
            (by linarith [mul_pos (N.d035) hA2, mul_pos (N.hDG5) N.hs])
        have hL36 : 0 < -N.a0 * N.h2 * N.t + N.b2 * N.h0 * N.s + N.h0 * N.h2 * N.s + N.a0 * N.h2 :=
            by
          linarith [mul_pos (hb0) hYs, mul_pos (hb01) hYs, mul_pos (hh2g) hYs, mul_pos (N.hh0) hth,
                mul_pos (N.hF5) N.ht]
        exact N.cert_k3_Y1p hb0 hYs hp56 hL36 (N.planar_robust oY1)
    · have hXf : 0 < -N.a0 * N.t + N.b0 * N.s - N.h0 * N.t - N.b0 - N.s + 1 := by linarith
      have hsg : 0 < N.a2 * N.t - N.b2 * N.s + N.h2 * N.t - N.a2 - N.h2 - N.t + 1 :=
          pos_of_mul_pos_r hA0 (by
            linarith [mul_pos (N.d035) hA2, mul_pos (N.hDG5) N.hs,
                mul_pos (mul_pos (hA0) hst) hh2g])
      have hXa2 : 0 < -N.a0 * N.b2 + N.a2 * N.b0 + N.b0 * N.h2 - N.b2 * N.h0 - N.a2 - N.b0 - N.h2 +
          1 := pos_of_mul_pos_r N.hh0 (by linarith [mul_pos (hV3) hb01, mul_pos (h345_0) hh2F4])
      exact N.cert_k3_X hA2 hb0 hV3 hh01 hG4 hG5n hh20 hh2g hkap hh2F4 hXf hb01 hsg hXa2
                (htie.one _ (N.seg_ne (i := 0) (j := 5) (by decide))) (htie.one _ N.view_T2_ne)
                (htie.pair (.inl (0, 5),
                    .inr 1) (by decide) (N.seg_ne (i := 0) (j := 5) (by decide)) N.view_T2_ne)
  · have hF4h2 : 0 < N.b0 * N.h2 - N.b2 * N.h0 - N.h2 := by linarith
    have hN : 0 < N.a0 * N.b2 - N.a2 * N.b0 - N.a2 * N.h0 + N.a2 := by
      linarith [N.hDG5, mul_pos (hA0) hh2g]
    have hal : 0 < -N.a0 * N.b0 * N.h2 + N.a0 * N.b2 * N.h0 - N.a0 * N.h0 * N.h2 - N.b0 * N.h0 *
        N.h2 - N.h0 ^ 2 * N.h2 + N.a0 * N.h2 + N.h0 * N.h2 := by
      linarith [mul_pos (hA0) hF4h2, mul_pos (N.hh0) h345_0, mul_pos (mul_pos (N.hh0) h345_0) hh2g]
    have hhF5 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.h0 * N.h2 := by
      linarith [hh0F5, mul_pos (N.hh0) hh2g]
    exact N.cert_k3_P11 hA2 hb0 hh01 hG5n hF45 hh20 hth hf hh2g hkap hh0F5 hF4h2 hN hal hhF5
       
                (htie.one _ N.view_T1_ne) (htie.one _ N.view_T3_ne)
                (htie.pair (.inr 0, .inr 3) (by decide) N.view_T1_ne N.view_T3_ne)

theorem NF29.cert_K3a (N : NF29 x) (ha2 : N.a2 < 0) (hb0 : 0 < N.b0)
    (hV : 0 < N.h0 * (1 - N.a2 - N.b2) - N.h2 * (1 - N.a0 - N.b0))
    (n03 : ¬ (-N.b2 < N.h2 * N.b0 - N.h0 * N.b2 ∧ 1 < N.h0))
    (n24 : ¬ (N.h0 < N.h0 * N.a2 - N.h2 * N.a0 ∧
      1 - N.a0 - N.b0 - N.h0 < -((N.b0 - 1 + N.h0) * N.a2 - N.a0 * N.b2 + N.a0 * (1 - N.h2))))
    (n14 : ¬ (N.b0 * (1 - N.h2) - N.b2 * (1 - N.h0) < 0 ∧ 1 < N.b0 + N.h0))
    (n51 : ¬ (0 < N.a2 * (1 - N.h0) - N.a0 * (1 - N.h2) ∧ N.a2 + N.h2 < 1))
    (G : K3Poly N) (htie : Tie29 x) : Cert29 x := by
  obtain ⟨h0, hG4', hG5', hF', h20'⟩ := N.k3_facts ha2 hb0 hV n03 n14 n51 G.h0 G.G4 G.G5 G.F
  have hA2 : 0 < -N.a2 := by linarith
  have hb0 : 0 < N.b0 := by linarith
  have hV3 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2 := by linarith
  have hh01 : 0 < -N.h0 + 1 := by linarith
  have hG4 : 0 < -N.b0 * N.h2 + N.b2 * N.h0 + N.b0 - N.b2 := by linarith
  have hG5n : 0 < -N.a0 * N.h2 + N.a2 * N.h0 + N.a0 - N.a2 := by linarith
  have hF45 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 := by linarith
  have hh20 : 0 < -N.h0 + N.h2 := by linarith
  by_cases hR : 0 < -N.a2 * N.t + N.b2 * N.s ∧ 0 < -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 *
      N.h2 * N.s - N.b2 * N.h0 * N.s - N.b0 * N.h2 + N.b2 * N.h0
  · obtain ⟨hth, hf⟩ := hR
    rcases lt_or_gt_of_ne G.h21 with h2 | h2
    · exact N.cert_k3_i hA2 hb0 hV3 hh01 hG4 hG5n hF45 hh20 hth hf (by linarith) G htie
    · rcases lt_or_gt_of_ne G.kap with hk | hk
      · exact (N.k3_R_empty hA2 hb0 hV3 hh01 hG4 hG5n hF45 hh20 hth hf
          (by linarith) (by linarith)).elim
      · exact N.cert_k3_open hA2 hb0 hV3 hh01 hG4 hG5n hF45 hh20 hth hf (by linarith) hk n24 G htie
  · exact N.cert_k3_notR hA2 hb0 hV3 hh01 hG4 hG5n hF45 hh20 hR G htie

/-- **Theorem 21.11 (K4 is covered), class K4a**, certificate form. -/
theorem NF29.cert_K4a (N : NF29 x) (ha2 : 0 < N.a2) (hb0 : 0 < N.b0)
    (hV : N.h0 * (1 - N.a2 - N.b2) - N.h2 * (1 - N.a0 - N.b0) < 0)
    (n24 : ¬ (N.h0 < N.h0 * N.a2 - N.h2 * N.a0 ∧
      1 - N.a0 - N.b0 - N.h0 < -((N.b0 - 1 + N.h0) * N.a2 - N.a0 * N.b2 + N.a0 * (1 - N.h2))))
    (n41 : ¬ (0 < N.b0 * (1 - N.h2) - N.b2 * (1 - N.h0) ∧ N.b0 + N.h0 < 1))
    (n51 : ¬ (0 < N.a2 * (1 - N.h0) - N.a0 * (1 - N.h2) ∧ N.a2 + N.h2 < 1))
    (n15 : ¬ (N.a2 * (1 - N.h0) - N.a0 * (1 - N.h2) < 0 ∧ 1 < N.a2 + N.h2))
    (G : K4Poly N) (htie : Tie29 x) : Cert29 x := by
  obtain ⟨he0, he2, hs1, ht1, hbh2, hG5⟩ := N.k4_facts ha2 hb0 hV n24 n41 n51 n15 G.e0 G.e2
  have hA0 : 0 < -N.a0 := by linarith [N.ha0]
  rcases lt_or_gt_of_ne G.h0 with h0 | h0
  · -- (A)
    have hc : 0 < N.a0 * N.b2 - N.a2 * N.b0 - N.a2 * N.h0 + N.a2 := by
      nlinarith [N.hDD, mul_pos ha2 (show 0 < 1 - N.h0 by linarith)]
    rcases N.cert_k4_A ha2 he0 hbh2 hs1 ht1 (by linarith) hc
      (htie.one _ N.view_V_ne) (htie.one _ (N.seg_ne (i := 3) (j := 5) (by decide)))
      (htie.pair (.inr 2, .inl (3, 5)) (by decide) N.view_V_ne
        (N.seg_ne (i := 3) (j := 5) (by decide))) with h | h
    · exact Cert29.ofV h
    · exact Cert29.ofY h
  · have hh21 : 0 < -N.h2 + 1 := by
      by_contra hc; push Not at hc
      nlinarith [mul_nonneg hA0.le (show 0 ≤ N.h2 - 1 by linarith),
        mul_pos ha2 (show 0 < N.h0 - 1 by linarith)]
    rcases lt_or_gt_of_ne G.ah with hah | hah
    · -- (B2): `c1` holds, so `c2 < 0`
      have hc1 : N.h0 < N.h0 * N.a2 - N.h2 * N.a0 := by
        nlinarith [mul_pos N.hh2 (show 0 < -N.a0 - N.h0 by linarith), mul_pos N.hh0 he2]
      have hc2 : 0 < -N.a0 * N.b2 - N.a0 * N.h2 + N.a2 * N.b0 + N.a2 * N.h0 - N.a2 - N.b0 -
          N.h0 + 1 := by
        have h : -((N.b0 - 1 + N.h0) * N.a2 - N.a0 * N.b2 + N.a0 * (1 - N.h2)) ≤
            1 - N.a0 - N.b0 - N.h0 := not_lt.mp fun h' => n24 ⟨hc1, h'⟩
        have := lt_of_le_of_ne h G.c2
        linarith
      exact N.cert_k4_B2 ha2 hb0 he0 he2 hs1 ht1 hbh2 (by linarith) (by linarith) hh21 hc2
        (htie.one _ (N.seg_ne (i := 0) (j := 3) (by decide))) (htie.one _ N.view_Z_ne)
        (htie.pair (.inl (0, 3), .inr 6) (by decide) (N.seg_ne (i := 0) (j := 3) (by decide))
          N.view_Z_ne)
    · -- (B1): `σ` of (A)
      have hc' : 0 < N.b2 * N.a0 - N.b0 * N.a2 - N.b0 * N.h2 + N.b0 := by
        nlinarith [N.hDD, mul_pos hb0 hh21]
      have oV : OneTieAt (univ.image (x ∘ sigma29)) (view29 (x ∘ sigma29) (.inr 2)) := by
        rw [image_sigma29, view29_sigma_inr2]; exact (htie.one _ N.view_T2_ne).neg
      have oY : OneTieAt (univ.image (x ∘ sigma29)) (view29 (x ∘ sigma29) (.inl (3, 5))) := by
        rw [image_sigma29]; exact htie.one (.inl (3, 4)) (N.seg_ne (by decide))
      have hno : NoTieAt (univ.image (x ∘ sigma29)) (view29 (x ∘ sigma29) (.inr 2)) ∨
          NoTieAt (univ.image (x ∘ sigma29)) (view29 (x ∘ sigma29) (.inl (3, 5))) := by
        rw [image_sigma29, view29_sigma_inr2]
        rcases htie.pair (.inr 1, .inl (3, 4)) (by decide) N.view_T2_ne (N.seg_ne (by decide))
          with h | h
        · exact Or.inl h.neg
        · exact Or.inr h
      exact Cert29.ofSigmaA (N.sigma.cert_k4_A hb0 he2 (by show 0 < N.a0 + N.h0; linarith) ht1
        hs1 hh21 hc' oV oY hno)

/-- **Theorem 21.22 with Theorem P: class K3a**, as a certificate. -/
theorem NF29.cert29_K3a_all (N : NF29 x) (ha2 : N.a2 < 0) (hb0 : 0 < N.b0)
    (hV : 0 < N.h0 * (1 - N.a2 - N.b2) - N.h2 * (1 - N.a0 - N.b0)) (G : K3Poly N)
    (G1 : K3C1Poly N) (htie : Tie29 x) : Cert29 x := by
  by_cases q03 : -N.b2 < N.h2 * N.b0 - N.h0 * N.b2 ∧ 1 < N.h0
  · have q := q03
    exact N.cert_k3_E03 (by linarith : 0 < -N.a2)
        (by linarith [q.1] : 0 < N.b0 * N.h2 - N.b2 * N.h0 + N.b2)
        (by linarith [q.2] : 0 < N.h0 - 1)
                (N.edgeW htie (i := 0) (j := 3) (by decide) (by decide) (by decide) (by decide))
  by_cases q24 : N.h0 < N.h0 * N.a2 - N.h2 * N.a0 ∧
      1 - N.a0 - N.b0 - N.h0 < -((N.b0 - 1 + N.h0) * N.a2 - N.a0 * N.b2 + N.a0 * (1 - N.h2))
  · have q := q24
    exact N.cert_k3_E24 hb0
        (by linarith : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2)
        (by linarith [q.1] : 0 < -N.a0 * N.h2 + N.a2 * N.h0 - N.h0)
        (by
          linarith [q.2] : 0 < N.a0 * N.b2 + N.a0 * N.h2 - N.a2 * N.b0 - N.a2 * N.h0 + N.a2 + N.b0 +
            N.h0 - 1)
                (N.edgeW htie (i := 2) (j := 4) (by decide) (by decide) (by decide) (by decide))
  by_cases q14 : N.b0 * (1 - N.h2) - N.b2 * (1 - N.h0) < 0 ∧ 1 < N.b0 + N.h0
  · have q := q14
    exact N.cert_k3_E14 (by linarith : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 +
        N.h0 - N.h2)
        (by linarith [q.1] : 0 < N.b0 * N.h2 - N.b2 * N.h0 - N.b0 + N.b2)
        (by linarith [q.2] : 0 < N.b0 + N.h0 - 1)
                (N.edgeW htie (i := 1) (j := 4) (by decide) (by decide) (by decide) (by decide))
  by_cases q51 : 0 < N.a2 * (1 - N.h0) - N.a0 * (1 - N.h2) ∧ N.a2 + N.h2 < 1
  · have q := q51
    rcases lt_or_gt_of_ne G1.s1 with hs0 | hs0
    · have hs : 0 < -N.s + 1 := by linarith
      exact N.cert_k3_E51s hb0 (by linarith [q.1] : 0 < N.a0 * N.h2 - N.a2 * N.h0 - N.a0 + N.a2)
          (by linarith [q.2] : 0 < -N.a2 - N.h2 + 1) hs
                (N.edgeW htie (i := 5) (j := 1) (by decide) (by decide) (by decide) (by decide))
    · have hs : 0 < N.s - 1 := by linarith
      exact N.cert_k3_E51l (by linarith : 0 < -N.a2) hb0
          (by linarith [q.1] : 0 < N.a0 * N.h2 - N.a2 * N.h0 - N.a0 + N.a2) hs
                (N.edgeW htie (i := 5) (j := 1) (by decide) (by decide) (by decide) (by decide))
  exact N.cert_K3a ha2 hb0 hV q03 q24 q14 q51 G htie

/-- **Theorem 21.11 with Theorem P: class K4a**, as a certificate. -/
theorem NF29.cert29_K4a_all (N : NF29 x) (ha2 : 0 < N.a2) (hb0 : 0 < N.b0)
    (hV : N.h0 * (1 - N.a2 - N.b2) - N.h2 * (1 - N.a0 - N.b0) < 0) (G : K4Poly N)
    (G1 : K4C1Poly N) (htie : Tie29 x) : Cert29 x := by
  by_cases q24 : N.h0 < N.h0 * N.a2 - N.h2 * N.a0 ∧
      1 - N.a0 - N.b0 - N.h0 < -((N.b0 - 1 + N.h0) * N.a2 - N.a0 * N.b2 + N.a0 * (1 - N.h2))
  · have q := q24
    exact N.cert_k4_E24 hb0 (by linarith [q.1] : 0 < -N.a0 * N.h2 + N.a2 * N.h0 - N.h0)
        (by
          linarith [q.2] : 0 < N.a0 * N.b2 + N.a0 * N.h2 - N.a2 * N.b0 - N.a2 * N.h0 + N.a2 + N.b0 +
            N.h0 - 1)
                (N.edgeW htie (i := 2) (j := 4) (by decide) (by decide) (by decide) (by decide))
  by_cases q41 : 0 < N.b0 * (1 - N.h2) - N.b2 * (1 - N.h0) ∧ N.b0 + N.h0 < 1
  · have q := q41
    rcases lt_or_gt_of_ne G1.t1 with ht0 | ht0
    · have ht : 0 < -N.t + 1 := by linarith
      exact N.cert_k4_E41s ha2
          (by linarith [q.1] : 0 < -N.b0 * N.h2 + N.b2 * N.h0 + N.b0 - N.b2)
          (by linarith [q.2] : 0 < -N.b0 - N.h0 + 1) ht
                (N.edgeW htie (i := 4) (j := 1) (by decide) (by decide) (by decide) (by decide))
    · have ht : 0 < N.t - 1 := by linarith
      exact N.cert_k4_E41l ha2 hb0
          (by linarith [q.1] : 0 < -N.b0 * N.h2 + N.b2 * N.h0 + N.b0 - N.b2)
          (by linarith [q.2] : 0 < -N.b0 - N.h0 + 1) ht
                (N.edgeW htie (i := 4) (j := 1) (by decide) (by decide) (by decide) (by decide))
  by_cases q51 : 0 < N.a2 * (1 - N.h0) - N.a0 * (1 - N.h2) ∧ N.a2 + N.h2 < 1
  · have q := q51
    rcases lt_or_gt_of_ne G1.s1 with hs0 | hs0
    · have hs : 0 < -N.s + 1 := by linarith
      exact N.cert_k4_E51s hb0 (by linarith [q.1] : 0 < N.a0 * N.h2 - N.a2 * N.h0 - N.a0 + N.a2)
          (by linarith [q.2] : 0 < -N.a2 - N.h2 + 1) hs
                (N.edgeW htie (i := 5) (j := 1) (by decide) (by decide) (by decide) (by decide))
    · have hs : 0 < N.s - 1 := by linarith
      exact N.cert_k4_E51l ha2 hb0
          (by linarith [q.1] : 0 < N.a0 * N.h2 - N.a2 * N.h0 - N.a0 + N.a2)
          (by linarith [q.2] : 0 < -N.a2 - N.h2 + 1) hs
                (N.edgeW htie (i := 5) (j := 1) (by decide) (by decide) (by decide) (by decide))
  by_cases q15 : N.a2 * (1 - N.h0) - N.a0 * (1 - N.h2) < 0 ∧ 1 < N.a2 + N.h2
  · have q := q15
    exact N.cert_k4_E15 (by linarith : 0 < -N.a0 * N.h2 + N.a2 * N.h0 - N.b0 * N.h2 + N.b2 * N.h0 -
        N.h0 + N.h2)
        (by linarith [q.1] : 0 < -N.a0 * N.h2 + N.a2 * N.h0 + N.a0 - N.a2)
        (by linarith [q.2] : 0 < N.a2 + N.h2 - 1)
                (N.edgeW htie (i := 1) (j := 5) (by decide) (by decide) (by decide) (by decide))
  exact N.cert_K4a ha2 hb0 hV q24 q41 q51 q15 G htie

end Minimality

end
