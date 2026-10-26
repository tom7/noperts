module

public import Minimality.Type29CertPairs

@[expose] public section

/-!
# Type 29, class K3a: the pair `{Y1, Y2}` and the cover glue as certificates
(`FEWER-FACES-PROOFS.md` §28, §18.4, §21.17–21.22)

* `NF29.cert_k3_Yp` (Lemma 21.20 (Y') with Proposition 21.21): `Y1 = 015/356` (rim `(5, 1, 4, 3)`)
  or `Y2 = 1456/346-4` (rim `(6, 3, 2, 0, 5)`) as a `Cert29`, with at most one tie at each of the
  two views.  `Y1` failing means `{5, 4}` weakly above `{1, 3}` (the crossing has `λ < 0`), so
  `⟪vY1, 6 − 4⟫ ≥ 0`, strictly because `1, 4, 5` are not at one depth (two ties); then the pattern
  argument `k3_Y2_core` holds for all views near `6 − 4` and `Y2` is robustly unimodal
  (`robust_of_view_nhds`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

variable {x : Fin 7 → ℝ³}

theorem NF29.cert_k3_Yp (N : NF29 x)
    (hb0 : 0 < N.b0)
    (hV3 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2)
    (hh01 : 0 < -N.h0 + 1)
    (hG5n : 0 < -N.a0 * N.h2 + N.a2 * N.h0 + N.a0 - N.a2)
    (hh20 : 0 < -N.h0 + N.h2)
    (hh2g : 0 < N.h2 - 1)
    (hkap : 0 < -N.a2 - N.h2 + 1)
    (hh0F5 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.h0)
    (hXfn : 0 < N.a0 * N.t - N.b0 * N.s + N.h0 * N.t + N.b0 + N.s - 1)
    (hb01 : 0 < -N.b0 + 1)
    (hAs : 0 < -N.h0 * N.s - N.a0)
    (hL36 : 0 < -N.a0 * N.h2 * N.t + N.b2 * N.h0 * N.s + N.h0 * N.h2 * N.s + N.a0 * N.h2)
    (hW43 : 0 < -N.a0 * N.h2 * N.t + N.b2 * N.h0 * N.s - N.h0 * N.h2 * N.t - N.b2 * N.h0)
    (hAh0 : 0 < -N.a0 - N.h0)
    (hs1g : 0 < N.s - 1)
    (hc4 : 0 < N.a0 * N.b2 - N.a2 * N.b0 - N.b0 * N.h2 + N.b2 * N.h0 - N.a0 + N.a2 - N.h0 + N.h2)
    (o1 : OneTieAt (univ.image x) (view29 x (.inr 4)))
    (o2 : OneTieAt (univ.image x) (view29 x (.inl (4, 6)))) : Cert29 x := by
  have hA0 : 0 < -N.a0 := by linarith [N.ha0]
  have hB2 : 0 < -N.b2 := by linarith [N.hb2]
  have h345_0 : 0 < 1 - N.a0 - N.b0 - N.h0 := by linarith [N.t345_0]
  have h345_2 : 0 < 1 - N.a2 - N.b2 - N.h2 := by linarith [N.t345_2]
  have hE35 : 0 < -((N.b0 - 1 + N.h0) * N.a2 - N.a0 * N.b2 + N.a0 * (1 - N.h2)) :=
      by linarith [N.hE35]
  have hst : 0 < N.s + N.t - 1 := by linarith [N.hst]
  have vY21 : (N.a0 * N.h2 * N.t - N.a2 * N.h0 * N.t - N.b0 * N.h2 * N.s + N.b2 * N.h0 * N.s + N.a0
        * N.b2 - N.a2 * N.b0 - N.h0 * N.s + N.h2 * N.s - N.a0 + N.a2) • (x 6 - x 4) +
      (-N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s - N.b0 * N.h2
        + N.b2 * N.h0 + N.h0 * N.s - N.h2 * N.s - N.h0 + N.h2) • (x 6 - x 3) +
      (N.a0 * N.t - N.b0 * N.s + N.h0 * N.t + N.b0 + N.s - 1) • (x 0 - x 2) +
      (-N.a0 * N.t + N.a2 * N.t + N.b0 * N.s - N.b2 * N.s - N.h0 * N.t + N.h2 * N.t - N.b0 + N.b2) •
      (x 0 - x 5) = 0 := by
    nf29_vec N
  have cY210 : 0 < N.a0 * N.h2 * N.t - N.a2 * N.h0 * N.t - N.b0 * N.h2 * N.s + N.b2 * N.h0 * N.s +
      N.a0 * N.b2 - N.a2 * N.b0 - N.h0 * N.s + N.h2 * N.s - N.a0 + N.a2 :=
      (by
        linarith [(pos_of_mul_pos_r hA0 (by
                show 0 < (N.a0 * N.h2 * N.t - N.a2 * N.h0 * N.t - N.b0 * N.h2 * N.s + N.b2 * N.h0 *
                    N.s + N.a0 * N.b2 - N.a2 * N.b0 - N.h0 * N.s + N.h2 * N.s - N.a0 + N.a2) *
                  (-N.a0)
                linarith [mul_pos (hAs) hc4, mul_pos (hV3) hAs, mul_pos (N.hF5) N.d035]))])
  have cY211 : 0 < -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s -
      N.b0 * N.h2 + N.b2 * N.h0 + N.h0 * N.s - N.h2 * N.s - N.h0 + N.h2 :=
      (by linarith [mul_pos (hV3) hs1g, mul_pos (N.hF5) hst])
  have cY212 : 0 < N.a0 * N.t - N.b0 * N.s + N.h0 * N.t + N.b0 + N.s - 1 := (by linarith [hXfn])
  have cY213 : 0 < -N.a0 * N.t + N.a2 * N.t + N.b0 * N.s - N.b2 * N.s - N.h0 * N.t + N.h2 * N.t -
      N.b0 + N.b2 := (by
        linarith [(pos_of_mul_pos_r hb01 (by
                show 0 < (-N.a0 * N.t + N.a2 * N.t + N.b0 * N.s - N.b2 * N.s - N.h0 * N.t + N.h2 *
                    N.t - N.b0 + N.b2) * (-N.b0 + 1)
                linarith [mul_pos (N.ht) hc4, mul_pos (hb0) hXfn, mul_pos (hB2) hXfn]))])
  have vY22 : (N.a0 * N.h2 * N.t - N.a2 * N.h0 * N.t - N.b0 * N.h2 * N.s + N.b2 * N.h0 * N.s + N.a0
        * N.b2 - N.a0 * N.t - N.a2 * N.b0 + N.a2 * N.t + N.b0 * N.s - N.b2 * N.s) • (x 6 - x 4) +
      (-N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s + N.a0 * N.t -
        N.a2 * N.t - N.b0 * N.h2 - N.b0 * N.s + N.b2 * N.h0 + N.b2 * N.s + N.b0 - N.b2) •
      (x 6 - x 3) +
      (-N.a0 * N.t + N.a2 * N.t + N.b0 * N.s - N.b2 * N.s - N.h0 * N.t + N.h2 * N.t - N.b0 + N.b2) •
      (x 2 - x 3) + (-N.a2 * N.t + N.b2 * N.s - N.h2 * N.t - N.b2 + N.t) • (x 2 - x 0) = 0 := by
    nf29_vec N
  have cY220 : 0 < N.a0 * N.h2 * N.t - N.a2 * N.h0 * N.t - N.b0 * N.h2 * N.s + N.b2 * N.h0 * N.s +
      N.a0 * N.b2 - N.a0 * N.t - N.a2 * N.b0 + N.a2 * N.t + N.b0 * N.s - N.b2 * N.s :=
      (by linarith [N.d023])
  have cY221 : 0 < -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s +
      N.a0 * N.t - N.a2 * N.t - N.b0 * N.h2 - N.b0 * N.s + N.b2 * N.h0 + N.b2 * N.s + N.b0 - N.b2 :=
      (by
        linarith [mul_pos (N.d234) hh01, mul_pos (mul_pos (hst) hb0) hh2g, mul_pos
            (mul_pos (h345_0) N.ht) hh2g])
  have cY222 : 0 < -N.a0 * N.t + N.a2 * N.t + N.b0 * N.s - N.b2 * N.s - N.h0 * N.t + N.h2 * N.t -
      N.b0 + N.b2 := (by
        linarith [(pos_of_mul_pos_r hb01 (by
                show 0 < (-N.a0 * N.t + N.a2 * N.t + N.b0 * N.s - N.b2 * N.s - N.h0 * N.t + N.h2 *
                    N.t - N.b0 + N.b2) * (-N.b0 + 1)
                linarith [mul_pos (N.ht) hc4, mul_pos (hb0) hXfn, mul_pos (hB2) hXfn]))])
  have cY223 : 0 < -N.a2 * N.t + N.b2 * N.s - N.h2 * N.t - N.b2 + N.t := (by linarith [N.d234])
  have vY5c : (N.a0 * N.a2 * N.h0 * N.t + N.a0 * N.b0 * N.h2 * N.s + N.a0 * N.h0 * N.h2 * N.s - N.a0
        ^ 2 * N.h2 * N.t - N.a2 * N.b0 * N.h0 * N.s - N.a2 * N.h0 ^ 2 * N.s - N.a0 * N.a2 * N.h0 -
        N.a0 * N.h2 * N.s + N.a0 ^ 2 * N.h2 + N.a2 * N.h0 * N.s) • (x 3 - x 2) +
      (-N.a0 * N.a2 * N.h0 * N.t - N.a0 * N.b0 * N.h2 * N.s - N.a0 * N.h0 * N.h2 * N.s + N.a0 ^ 2 *
        N.h2 * N.t + N.a2 * N.b0 * N.h0 * N.s + N.a2 * N.h0 ^ 2 * N.s + N.a0 * N.a2 * N.h0 + N.a0 *
        N.b0 * N.s + N.a0 * N.h0 * N.s + N.a0 * N.h2 * N.s - N.a0 ^ 2 * N.h2 - N.a0 ^ 2 * N.t - N.a2
        * N.h0 * N.s - N.a0 * N.s + N.a0 ^ 2) • (x 0 - x 2) +
      (N.a0 * N.a2 * N.h0 * N.t + N.a0 * N.b0 * N.h2 * N.s + N.a0 * N.h0 * N.h2 * N.s - N.a0 ^ 2 *
        N.h2 * N.t - N.a2 * N.b0 * N.h0 * N.s - N.a2 * N.h0 ^ 2 * N.s - N.a0 * N.a2 * N.h0 - N.a0 *
        N.a2 * N.t - N.a0 * N.b0 * N.s + N.a0 * N.b2 * N.s - N.a0 * N.h0 * N.s + N.a0 ^ 2 * N.h2 +
        N.a0 ^ 2 * N.t + N.a2 * N.h0 * N.s + N.a0 * N.a2 - N.a0 ^ 2) • (x 0 - x 5) +
      (N.a0 * N.b2 + N.a0 * N.h2 - N.a2 * N.b0 - N.a2 * N.h0 - N.a0 + N.a2) • N.vY1 = 0 := by
    simp only [NF29.vY1]; nf29_vec N
  have cY5c0 : 0 < N.a0 * N.a2 * N.h0 * N.t + N.a0 * N.b0 * N.h2 * N.s + N.a0 * N.h0 * N.h2 * N.s -
      N.a0 ^ 2 * N.h2 * N.t - N.a2 * N.b0 * N.h0 * N.s - N.a2 * N.h0 ^ 2 * N.s - N.a0 * N.a2 * N.h0
      - N.a0 * N.h2 * N.s + N.a0 ^ 2 * N.h2 + N.a2 * N.h0 * N.s :=
      (by linarith [mul_pos (N.hF5) N.d035])
  have cY5c1 : 0 < -N.a0 * N.a2 * N.h0 * N.t - N.a0 * N.b0 * N.h2 * N.s - N.a0 * N.h0 * N.h2 * N.s +
      N.a0 ^ 2 * N.h2 * N.t + N.a2 * N.b0 * N.h0 * N.s + N.a2 * N.h0 ^ 2 * N.s + N.a0 * N.a2 * N.h0
      + N.a0 * N.b0 * N.s + N.a0 * N.h0 * N.s + N.a0 * N.h2 * N.s - N.a0 ^ 2 * N.h2 - N.a0 ^ 2 * N.t
      - N.a2 * N.h0 * N.s - N.a0 * N.s + N.a0 ^ 2 :=
      (by
        linarith [mul_pos (hXfn) hAh0, mul_pos (N.hF5) hXfn, mul_pos (hh0F5) hXfn, mul_pos (h345_0)
            hAs, mul_pos (N.d035) hh0F5])
  have cY5c2 : 0 < N.a0 * N.a2 * N.h0 * N.t + N.a0 * N.b0 * N.h2 * N.s + N.a0 * N.h0 * N.h2 * N.s -
      N.a0 ^ 2 * N.h2 * N.t - N.a2 * N.b0 * N.h0 * N.s - N.a2 * N.h0 ^ 2 * N.s - N.a0 * N.a2 * N.h0
      - N.a0 * N.a2 * N.t - N.a0 * N.b0 * N.s + N.a0 * N.b2 * N.s - N.a0 * N.h0 * N.s + N.a0 ^ 2 *
      N.h2 + N.a0 ^ 2 * N.t + N.a2 * N.h0 * N.s + N.a0 * N.a2 - N.a0 ^ 2 :=
      (by
        linarith [hc4, mul_pos (N.hs) hV3, mul_pos (N.hh0) hV3, mul_pos (hG5n) hXfn, mul_pos
            (N.d035) hh20, mul_pos (N.hDG5) hs1g, mul_pos (N.d035) hG5n, mul_pos (N.hF5) N.d035,
            mul_pos (mul_pos (hA0) N.hs) hV3, mul_pos (mul_pos (hh01) hs1g) hc4, mul_pos
            (mul_pos (N.hF5) hst) hb0, mul_pos (mul_pos (N.hh0) N.hs) hc4, mul_pos
            (mul_pos (h345_2) hh01) hAs, mul_pos (mul_pos (h345_0) hh2g) hAs, mul_pos
            (mul_pos (h345_0) N.hF5) hst, mul_pos (mul_pos (N.hDG5) N.hs) hh01])
  have cY5c3 : 0 < N.a0 * N.b2 + N.a0 * N.h2 - N.a2 * N.b0 - N.a2 * N.h0 - N.a0 + N.a2 :=
      (by linarith [N.hDG5])
  have huni : ∀ w : ℝ³, 0 < ⟪x 6 - x 4, w⟫ → 0 < ⟪N.vY1, w⟫ →
      Function.Injective (quint ⟪x 6, w⟫ ⟪x 3, w⟫ ⟪x 2, w⟫ ⟪x 0, w⟫ ⟪x 5, w⟫) →
      IsCyclicUnimodal (quint ⟪x 6, w⟫ ⟪x 3, w⟫ ⟪x 2, w⟫ ⟪x 0, w⟫ ⟪x 5, w⟫) := by
    intro w hq hW hinj
    have vc : N.vY1 = (N.h0 * N.s) • (x 6 - x 3) + (-N.a0 - N.h0 * N.s) • (x 6 - x 5) := by
      simp only [NF29.vY1]; nf29_vec N
    have ic : ⟪N.vY1, w⟫ = N.h0 * N.s * (⟪x 6, w⟫ - ⟪x 3, w⟫) +
        (-N.a0 - N.h0 * N.s) * (⟪x 6, w⟫ - ⟪x 5, w⟫) := by
      rw [vc]; simp only [inner_add_left, real_inner_smul_left, inner_sub_left]
    have hu : 0 < ⟪x 6, w⟫ - ⟪x 4, w⟫ := by rw [← inner_sub_left]; exact hq
    have i21 := congrArg (fun v => ⟪v, w⟫) vY21
    have i22 := congrArg (fun v => ⟪v, w⟫) vY22
    have i5c := congrArg (fun v => ⟪v, w⟫) vY5c
    simp only [inner_add_left, real_inner_smul_left, inner_zero_left, inner_sub_left] at i21 i22 i5c
    exact k3_Y2_core hinj hu hW cY210 cY211 cY212 cY213
      cY220 cY221 cY222 cY223 cY5c0 cY5c1 cY5c2 cY5c3 (mul_pos N.hh0 N.hs) hAs
      (by linear_combination i21) (by linear_combination i22) (by linear_combination i5c)
      (by rw [ic]; ring)
  have o1' : OneTieAt (univ.image x) N.vY1 := o1.of_eq_smul N.vY1_eq N.hDni
  have o2' : OneTieAt (univ.image x) (x 6 - x 4) := o2
  have hne : ∀ {i j : Fin 7}, i ≠ j → x i ≠ x j := fun h => N.inj.ne h
  by_cases hR1 : IsRobustUnimodal (quad ⟪x 5, N.vY1⟫ ⟪x 1, N.vY1⟫ ⟪x 4, N.vY1⟫ ⟪x 3, N.vY1⟫)
  · exact N.cert_k3_Y1q hb0 hV3 hh01 hh2g hkap hh0F5 hb01 hAs hL36 hAh0 hs1g hR1
  -- `Y1` fails: `{5, 4}` weakly above `{1, 3}`
  have W := weakSep_of_not_robust (o1'.oneTie4 (img29 5) (img29 1) (img29 4) (img29 3)
    (List.nodup4_img N.inj (by decide : [(5 : Fin 7), 1, 4, 3].Nodup))) hR1
  have hK : 0 < -N.a0 * N.s - N.a0 * N.t + N.h0 * N.s + N.a0 := by
    linarith [mul_pos hA0 hst, mul_pos N.hh0 N.hs]
  have hm := meet_of_smul (d₀ := x 5) (d₁ := x 4) (e₀ := x 1) (e₁ := x 3) (v := N.vY1)
    (K := -N.a0 * N.s - N.a0 * N.t + N.h0 * N.s + N.a0) (s := -N.a0 * N.s) (t := N.h0 * N.s)
    (l := -1) hK.ne' (by simp only [NF29.vY1]; nf29_vec N)
  have hbd1 : 0 ≤ -N.a0 * N.s / (-N.a0 * N.s - N.a0 * N.t + N.h0 * N.s + N.a0) :=
    (div_pos (by linarith [hA0, mul_pos hA0 hs1g]) hK).le
  have h41 : ⟪x 1, N.vY1⟫ ≤ ⟪x 4, N.vY1⟫ ∧ ⟪x 1, N.vY1⟫ ≤ ⟪x 5, N.vY1⟫ := by
    rcases W with h | h
    · exact ⟨le_trans (le_max_left _ _) (le_trans h (min_le_right _ _)),
        le_trans (le_max_left _ _) (le_trans h (min_le_left _ _))⟩
    · exfalso
      refine not_weakSep_of_meet (div_pos (by linarith [hA0, mul_pos hA0 hs1g]) hK).le
        ((div_le_one hK).mpr (by
          have : 0 < (-N.a0 * N.t + N.h0 * N.s + N.a0) * N.h2 := by
            linarith [hL36, mul_pos (mul_pos N.hh0 hB2) N.hs]
          nlinarith [N.hh2]))
        (div_pos (mul_pos N.hh0 N.hs) hK).le
        ((div_le_one hK).mpr (by linarith [mul_pos hA0 hst])) hm
        (div_neg_of_neg_of_pos (by norm_num) hK)
        (nfV_ne_zero N.hD (Or.inr (Or.inr (ne_of_gt (mul_pos N.hh0 N.hs)))))
        (le_trans (le_max_left _ _) (le_trans h (min_le_left _ _)))
        (le_trans (le_max_left _ _) (le_trans h (min_le_right _ _)))
        (le_trans (le_max_right _ _) (le_trans h (min_le_left _ _)))
        (le_trans (le_max_right _ _) (le_trans h (min_le_right _ _)))
  have v64 : x 6 - x 4 = (N.s - 1) • (x 4 - x 1) + N.t • (x 5 - x 1) := by nf29_vec N
  have hpos : 0 < ⟪N.vY1, x 6 - x 4⟫ := by
    rw [real_inner_comm, v64]
    simp only [inner_add_left, inner_sub_left, real_inner_smul_left]
    have n4 : ⟪x 1, N.vY1⟫ ≠ ⟪x 4, N.vY1⟫ ∨ ⟪x 1, N.vY1⟫ ≠ ⟪x 5, N.vY1⟫ := by
      by_contra hc
      push Not at hc
      exact o1'.not_three (img29 4) (img29 1) (img29 5) (hne (by decide)) (hne (by decide))
        (hne (by decide)) ⟨hc.1.symm, hc.2⟩
    rcases n4 with n | n
    · linarith only [mul_pos hs1g (sub_pos.mpr (lt_of_le_of_ne h41.1 n)),
        mul_nonneg N.ht.le (sub_nonneg.mpr h41.2)]
    · linarith only [mul_nonneg hs1g.le (sub_nonneg.mpr h41.1),
        mul_pos N.ht (sub_pos.mpr (lt_of_le_of_ne h41.2 n))]
  have hu : 0 < ⟪x 6 - x 4, x 6 - x 4⟫ :=
    real_inner_self_pos.mpr (sub_ne_zero.mpr (N.inj.ne (by decide)))
  have hpts : ∀ i, (quint (x 6) (x 3) (x 2) (x 0) (x 5)) i ∈ univ.image x := by
    intro i; rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;> exact img29 _
  have hinjp : Function.Injective (quint (x 6) (x 3) (x 2) (x 0) (x 5)) :=
    quint_injective (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide))
      (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide))
      (hne (by decide))
  have hY2 : IsRobustUnimodal
      (quint ⟪x 6, x 6 - x 4⟫ ⟪x 3, x 6 - x 4⟫ ⟪x 2, x 6 - x 4⟫ ⟪x 0, x 6 - x 4⟫
        ⟪x 5, x 6 - x 4⟫) := by
    have := robust_of_view_nhds (K := univ.image x) hpts hinjp (u := x 6 - x 4) o2'
      (fun w => 0 < ⟪x 6 - x 4, w⟫ ∧ 0 < ⟪N.vY1, w⟫) ?_ ?_
    · rwa [quint_inner] at this
    · have c1 : Continuous fun w : ℝ³ => ⟪x 6 - x 4, w⟫ := continuous_const.inner continuous_id
      have c2 : Continuous fun w : ℝ³ => ⟪N.vY1, w⟫ := continuous_const.inner continuous_id
      exact ((c1.tendsto _).eventually_const_lt hu).and ((c2.tendsto _).eventually_const_lt hpos)
    · intro w hw hinj
      rw [quint_inner] at hinj ⊢
      exact huni w hw.1 hw.2 hinj
  exact N.cert_k3_Y2 hb0 hV3 hh01 hh20 hh2g hb01 hW43 hs1g hY2

end Minimality

end
