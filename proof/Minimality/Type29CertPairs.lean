module

public import Minimality.Type29CertTests
public import Minimality.Type29CertTie

@[expose] public section

/-!
# Type 29: the pairs as certificates (`FEWER-FACES-PROOFS.md` §28, §18.4, §21.15–21.19)

`NF29.cert_k3_P14`, `_P11`, `_X`, `_P13`: the pairs `{T1, T2}`, `{T1o, T3o}`, `{Xa, T2o}`,
`{T3s, T2o}` of class K3a as certificates (`Cert29`).  Corollary 13.3 is used with ties
(`pair_core`): at most one tie at each of the two views (`OneTieAt`) and none at one of them.
The partner (`T2`, `T3`) is preferred; the first test is issued only when the partner is not
robustly unimodal, and then `T1`'s certificate carries `⟪vT1, partner⟫ ≤ 0` (`Ex29.t1`,
`Ex29.t1o`), as type 21's `VQuadCone`.  The partner `T2` carries its closed region facts.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Minimality

open scoped RealInnerProductSpace
open Finset

variable {x : Fin 7 → ℝ³}

theorem NF29.cert_k3_P14 (N : NF29 x)
    (hA2 : 0 < -N.a2)
    (hb0 : 0 < N.b0)
    (hh01 : 0 < -N.h0 + 1)
    (hG5n : 0 < -N.a0 * N.h2 + N.a2 * N.h0 + N.a0 - N.a2)
    (hF45 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0)
    (hh20 : 0 < -N.h0 + N.h2)
    (hth : 0 < -N.a2 * N.t + N.b2 * N.s)
    (hf : 0 < -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s - N.b0
          * N.h2 + N.b2 * N.h0)
    (hh21 : 0 < -N.h2 + 1)
    (hsg : 0 < N.a2 * N.t - N.b2 * N.s + N.h2 * N.t - N.a2 - N.h2 - N.t + 1)
    (hc0 : 0 < N.a0 * N.b2 - N.a2 * N.b0 - N.a2 * N.h0 - N.b0 * N.h2 - N.h0 * N.h2 + N.a2 + N.b0 +
          N.h0 + N.h2 - 1)
    (o1 : OneTieAt (univ.image x) (view29 x (.inr 0)))
    (o2 : OneTieAt (univ.image x) (view29 x (.inr 1)))
    (hno : NoTieAt (univ.image x) (view29 x (.inr 0)) ∨
        NoTieAt (univ.image x) (view29 x (.inr 1))) :
    Cert29 x := by
  have hA0 : 0 < -N.a0 := by linarith [N.ha0]
  have hB2 : 0 < -N.b2 := by linarith [N.hb2]
  have h345_0 : 0 < 1 - N.a0 - N.b0 - N.h0 := by linarith [N.t345_0]
  have h345_2 : 0 < 1 - N.a2 - N.b2 - N.h2 := by linarith [N.t345_2]
  have m11 : SegMeet (x 1) (x 3) (x 2) (x 6) (N.vT1) := segMeet_of_smul'
      (K := N.a0 * N.b2 * N.h2 - N.a0 * N.h2 * N.t - N.a2 * N.b0 * N.h2 + N.a2 * N.h0 * N.t + N.b0 *
        N.h2 * N.s - N.b2 * N.h0 * N.s)
    (s := -N.a0 * N.h2 ^ 2 * N.t + N.a2 * N.h0 * N.h2 * N.t + N.b0 * N.h2 ^ 2 * N.s - N.b2 * N.h0 *
          N.h2 * N.s)
    (t := N.a0 * N.b2 * N.h2 - N.a2 * N.b0 * N.h2)
    (l := N.a2 * N.t - N.b2 * N.s)
    (by linarith [hf, N.hF4, mul_pos (N.hh2) N.hDD])
    (by linarith [mul_pos (N.hh2) hf, mul_pos (N.hh2) N.hF4])
    (by
          linarith [mul_pos (hf) hh21, mul_pos (hF45) hh21, mul_pos (N.hDD) hh20, mul_pos (N.hF5)
              hh21, mul_pos (mul_pos (N.hh0) hA2) hb0, mul_pos (mul_pos (N.hh2) hA0) hB2, mul_pos
              (mul_pos (N.hh2) hb0) hG5n, mul_pos (mul_pos (hA0) N.hF4) hh21, mul_pos
              (mul_pos (N.hh0) N.hh2) N.hDD])
    (by linarith [mul_pos (N.hh2) N.hDD])
    (by linarith [hf, N.hF4])
    (by simp only [NF29.vT1]; nf29_vec N)
  have m12 : SegMeet (x 1) (x 3) (x 2) (x 6) (N.vT2) := segMeet_of_smul'
      (K := -N.a2 * N.t + N.b2 * N.h2 + N.b2 * N.s - N.h2 * N.t - N.b2 + N.t)
    (s := -N.a2 * N.h2 * N.t + N.b2 * N.h2 * N.s - N.h2 ^ 2 * N.t + N.h2 * N.t)
    (t := N.b2 * N.h2 - N.b2)
    (l := N.a2 * N.t - N.b2 * N.s)
    (by linarith [hth, mul_pos (hB2) hh21, mul_pos (N.ht) hh21])
    (by linarith [mul_pos (N.hh2) hth, mul_pos (mul_pos (N.hh2) N.ht) hh21])
    (by linarith [mul_pos (N.d234) hh21])
    (by linarith [mul_pos (hB2) hh21])
    (by linarith [hth, mul_pos (N.ht) hh21])
    (by simp only [NF29.vT2]; nf29_vec N)
  have m21 : SegMeet (x 4) (x 0) (x 3) (x 5) (N.vT1) := segMeet_of_smul'
      (K := N.a0 * N.b2 * N.h0 + N.a0 * N.h0 * N.h2 - N.a2 * N.b0 * N.h0 - N.a2 * N.h0 ^ 2 + N.b0 *
        N.h2 - N.b2 * N.h0)
    (s := N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0)
    (t := N.a0 * N.b2 * N.h0 - N.a2 * N.b0 * N.h0 - N.b0 * N.h0 * N.h2 + N.b2 * N.h0 ^ 2 + N.b0 *
          N.h2 - N.b2 * N.h0)
    (l := N.a0 + N.b0 + N.h0 - 1)
    (by linarith [mul_pos (hb0) hh20, mul_pos (N.hh0) hF45, mul_pos (N.hh0) N.hDG4])
    (by linarith [hF45])
    (by linarith [mul_pos (hA0) hh20, mul_pos (N.hh0) N.hDG5])
    (by
          linarith [mul_pos (hA0) hh20, mul_pos (N.hh0) hc0, mul_pos (hh01) hF45, mul_pos
              (mul_pos (N.hh0) h345_0) hh21])
    (by linarith [mul_pos (N.hh0) hF45])
    (by simp only [NF29.vT1]; nf29_vec N)
  have m22 : SegMeet (x 4) (x 0) (x 3) (x 5) (N.vT2) := segMeet_of_smul'
      (K := N.a0 * N.b2 - N.a2 * N.b0 - N.a2 * N.h0 - N.b0 * N.h2 - N.h0 * N.h2 + N.b0 - N.b2
          + N.h0)
    (s := -N.a2 - N.b2 - N.h2 + 1)
    (t := N.a0 * N.b2 - N.a2 * N.b0 - N.b0 * N.h2 + N.b2 * N.h0 + N.b0 - N.b2)
    (l := -N.a0 - N.b0 - N.h0 + 1)
    (by linarith [hc0, h345_2])
    (by linarith [h345_2])
    (by linarith [hc0])
    (by linarith [N.hDG4])
    (by linarith [mul_pos (N.hh0) h345_2])
    (by simp only [NF29.vT2]; nf29_vec N)
  have eq11 : det3 (N.vT1) (x 3 - x 1) (x 6 - x 2) =
      (N.a0 * N.b2 * N.h2 - N.a0 * N.h2 * N.t - N.a2 * N.b0 * N.h2 + N.a2 * N.h0 * N.t + N.b0 * N.h2
        * N.s - N.b2 * N.h0 * N.s) * det3 N.E₁ N.E₂ N.E₃ := by
    simp only [NF29.vT1]; nf29_simp N; simp only [det3c]; ring
  have pq11 : 0 < N.a0 * N.b2 * N.h2 - N.a0 * N.h2 * N.t - N.a2 * N.b0 * N.h2 + N.a2 * N.h0 * N.t +
      N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s := (by linarith [hf, N.hF4, mul_pos (N.hh2) N.hDD])
  have eq12 : det3 (N.vT2) (x 3 - x 1) (x 6 - x 2) =
      (-N.a2 * N.t + N.b2 * N.h2 + N.b2 * N.s - N.h2 * N.t - N.b2 + N.t) * det3 N.E₁ N.E₂ N.E₃ := by
    simp only [NF29.vT2]; nf29_simp N; simp only [det3c]; ring
  have pq12 : 0 < -N.a2 * N.t + N.b2 * N.h2 + N.b2 * N.s - N.h2 * N.t - N.b2 + N.t :=
      (by linarith [hth, mul_pos (hB2) hh21, mul_pos (N.ht) hh21])
  have eq21 : det3 (N.vT1) (x 0 - x 4) (x 5 - x 3) =
      (-N.a0 * N.b2 * N.h0 - N.a0 * N.h0 * N.h2 + N.a2 * N.b0 * N.h0 + N.a2 * N.h0 ^ 2 - N.b0 * N.h2
        + N.b2 * N.h0) * det3 N.E₁ N.E₂ N.E₃ := by
    simp only [NF29.vT1]; nf29_simp N; simp only [det3c]; ring
  have pq21 : -N.a0 * N.b2 * N.h0 - N.a0 * N.h0 * N.h2 + N.a2 * N.b0 * N.h0 + N.a2 * N.h0 ^ 2 - N.b0
      * N.h2 + N.b2 * N.h0 < 0 :=
      (by linarith [mul_pos (hb0) hh20, mul_pos (N.hh0) hF45, mul_pos (N.hh0) N.hDG4])
  have eq22 : det3 (N.vT2) (x 0 - x 4) (x 5 - x 3) =
      (N.a0 * N.b2 - N.a2 * N.b0 - N.a2 * N.h0 - N.b0 * N.h2 - N.h0 * N.h2 + N.b0 - N.b2 + N.h0) *
      det3 N.E₁ N.E₂ N.E₃ := by
    simp only [NF29.vT2]; nf29_simp N; simp only [det3c]; ring
  have pq22 : 0 < N.a0 * N.b2 - N.a2 * N.b0 - N.a2 * N.h0 - N.b0 * N.h2 - N.h0 * N.h2 + N.b0 - N.b2
      + N.h0 := (by linarith [hc0, h345_2])
  have hS1 : det3 (x 2 - x 1) (x 3 - x 1) (x 6 - x 2) ≠ 0 :=
    segMeet_hS_of_smul' (v := N.vT1)
    (K := N.a0 * N.b2 * N.h2 - N.a0 * N.h2 * N.t - N.a2 * N.b0 * N.h2 + N.a2 * N.h0 * N.t + N.b0 *
        N.h2 * N.s - N.b2 * N.h0 * N.s)
    (s := -N.a0 * N.h2 ^ 2 * N.t + N.a2 * N.h0 * N.h2 * N.t + N.b0 * N.h2 ^ 2 * N.s - N.b2 * N.h0 *
          N.h2 * N.s)
    (t := N.a0 * N.b2 * N.h2 - N.a2 * N.b0 * N.h2)
    (l := N.a2 * N.t - N.b2 * N.s)
    (by linarith [hf, N.hF4, mul_pos (N.hh2) N.hDD])
    (by linarith [mul_pos (N.hh2) hf, mul_pos (N.hh2) N.hF4])
    (by
          linarith [mul_pos (hf) hh21, mul_pos (hF45) hh21, mul_pos (N.hDD) hh20, mul_pos (N.hF5)
              hh21, mul_pos (mul_pos (N.hh0) hA2) hb0, mul_pos (mul_pos (N.hh2) hA0) hB2, mul_pos
              (mul_pos (N.hh2) hb0) hG5n, mul_pos (mul_pos (hA0) N.hF4) hh21, mul_pos
              (mul_pos (N.hh0) N.hh2) N.hDD])
    (by linarith [mul_pos (N.hh2) N.hDD])
    (by linarith [hf, N.hF4])
    (by simp only [NF29.vT1]; nf29_vec N)
    (ne_of_lt (by linarith [hth]))
    (by rw [eq11]; exact mul_ne_zero pq11.ne' N.hD)
  have hS2 : det3 (x 3 - x 4) (x 0 - x 4) (x 5 - x 3) ≠ 0 :=
    segMeet_hS_of_smul' (v := N.vT2)
    (K := N.a0 * N.b2 - N.a2 * N.b0 - N.a2 * N.h0 - N.b0 * N.h2 - N.h0 * N.h2 + N.b0 - N.b2
          + N.h0)
    (s := -N.a2 - N.b2 - N.h2 + 1)
    (t := N.a0 * N.b2 - N.a2 * N.b0 - N.b0 * N.h2 + N.b2 * N.h0 + N.b0 - N.b2)
    (l := -N.a0 - N.b0 - N.h0 + 1)
    (by linarith [hc0, h345_2])
    (by linarith [h345_2])
    (by linarith [hc0])
    (by linarith [N.hDG4])
    (by linarith [mul_pos (N.hh0) h345_2])
    (by simp only [NF29.vT2]; nf29_vec N)
    (ne_of_gt (by linarith [h345_0]))
    (by rw [eq22]; exact mul_ne_zero pq22.ne' N.hD)
  have o1' : OneTieAt (univ.image x) N.vT1 := o1.of_eq_smul N.vT1_eq N.hDi
  have o2' : OneTieAt (univ.image x) N.vT2 := o2.of_eq_smul N.vT2_eq N.hDni
  have hno' : NoTieAt (univ.image x) N.vT1 ∨ NoTieAt (univ.image x) N.vT2 := by
    rcases hno with hnu | hnv
    · exact Or.inl (hnu.of_eq_smul N.vT1_eq N.hDi)
    · exact Or.inr (hnv.of_eq_smul N.vT2_eq N.hDni)
  have hp1 := prod_pos_of_eq N.hD eq11 eq12 pq11 pq12
  have hn2 := prod_neg_of_eq N.hD eq21 eq22 pq21 pq22
  rcases pair_core (img29 1) (img29 3) (img29 2) (img29 6) (img29 4) (img29 0) (img29 3) (img29 5)
    (List.nodup4_img N.inj (by decide : [(1 : Fin 7), 2, 3, 6].Nodup))
    (List.nodup4_img N.inj (by decide : [(4 : Fin 7), 3, 0, 5].Nodup))
    m11 m12 m21 m22 hS1 hS2 hp1 hn2 o1' o2' hno' with hR2 | ⟨hR1, hdot⟩
  · exact NF29.cert_k3_T2a N hA2 hh21 hsg hc0 hR2 ⟨N, by linarith [hh20], by linarith [hh21]⟩
  · exact NF29.cert_k3_T1 N hb0 hG5n hF45 hh20 hf hh21 hR1 ⟨⟨N, by linarith [hth],
      by linarith [hh21]⟩, N.dot_T1T2 hdot⟩


theorem NF29.cert_k3_P11 (N : NF29 x)
    (hA2 : 0 < -N.a2)
    (hb0 : 0 < N.b0)
    (hh01 : 0 < -N.h0 + 1)
    (hG5n : 0 < -N.a0 * N.h2 + N.a2 * N.h0 + N.a0 - N.a2)
    (hF45 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0)
    (hh20 : 0 < -N.h0 + N.h2)
    (hth : 0 < -N.a2 * N.t + N.b2 * N.s)
    (hf : 0 < -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s - N.b0
          * N.h2 + N.b2 * N.h0)
    (hh2g : 0 < N.h2 - 1)
    (hkap : 0 < -N.a2 - N.h2 + 1)
    (hh0F5 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.h0)
    (hF4h2 : 0 < N.b0 * N.h2 - N.b2 * N.h0 - N.h2)
    (hN : 0 < N.a0 * N.b2 - N.a2 * N.b0 - N.a2 * N.h0 + N.a2)
    (hal : 0 < -N.a0 * N.b0 * N.h2 + N.a0 * N.b2 * N.h0 - N.a0 * N.h0 * N.h2 - N.b0 * N.h0 * N.h2 -
          N.h0 ^ 2 * N.h2 + N.a0 * N.h2 + N.h0 * N.h2)
    (hhF5 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.h0 * N.h2)
    (o1 : OneTieAt (univ.image x) (view29 x (.inr 0)))
    (o2 : OneTieAt (univ.image x) (view29 x (.inr 3)))
    (hno : NoTieAt (univ.image x) (view29 x (.inr 0)) ∨
        NoTieAt (univ.image x) (view29 x (.inr 3))) :
    Cert29 x := by
  have hA0 : 0 < -N.a0 := by linarith [N.ha0]
  have hB2 : 0 < -N.b2 := by linarith [N.hb2]
  have h345_0 : 0 < 1 - N.a0 - N.b0 - N.h0 := by linarith [N.t345_0]
  have h345_2 : 0 < 1 - N.a2 - N.b2 - N.h2 := by linarith [N.t345_2]
  have m11 : SegMeet (x 1) (x 3) (x 2) (x 6) (N.vT1) := segMeet_of_smul'
      (K := N.a0 * N.b2 * N.h2 - N.a0 * N.h2 * N.t - N.a2 * N.b0 * N.h2 + N.a2 * N.h0 * N.t + N.b0 *
        N.h2 * N.s - N.b2 * N.h0 * N.s)
    (s := -N.a0 * N.h2 ^ 2 * N.t + N.a2 * N.h0 * N.h2 * N.t + N.b0 * N.h2 ^ 2 * N.s - N.b2 * N.h0 *
          N.h2 * N.s)
    (t := N.a0 * N.b2 * N.h2 - N.a2 * N.b0 * N.h2)
    (l := N.a2 * N.t - N.b2 * N.s)
    (by
          linarith [hf, hA0, hG5n, hhF5, hh20, hF4h2, N.hF4, mul_pos (hA2) hh20, mul_pos (N.hh2) hN,
              mul_pos (hA2) hF4h2, mul_pos (hB2) N.hF5, mul_pos (N.hh0) hkap, mul_pos
              (mul_pos (hA2) hh01) hh2g])
    (by linarith [mul_pos (N.hh2) hf, mul_pos (N.hh2) N.hF4])
    (by linarith [N.d023, mul_pos (hh20) hth, mul_pos (N.d023) hh2g])
    (by linarith [mul_pos (N.hh2) N.hDD])
    (by linarith [hf, N.hF4])
    (by simp only [NF29.vT1]; nf29_vec N)
  have m12 : SegMeet (x 1) (x 3) (x 2) (x 6) (N.vT3) := segMeet_of_smul'
      (K := N.a0 * N.b2 * N.h2 - N.a0 * N.h2 * N.t - N.a2 * N.b2 * N.h0 + N.b2 * N.h0 * N.s)
    (s := -N.a0 * N.h2 ^ 2 * N.t + N.a2 * N.h0 * N.h2 * N.t)
    (t := N.a0 * N.b2 * N.h2 - N.a2 * N.b2 * N.h0)
    (l := N.a2 * N.t - N.b2 * N.s)
    (by linarith [mul_pos (N.hh0) hth, mul_pos (hB2) N.hF5, mul_pos (N.hF5) N.ht])
    (by linarith [mul_pos (mul_pos (N.hh2) N.hF5) N.ht])
    (by linarith [mul_pos (hth) hh0F5, mul_pos (N.hF5) N.d234])
    (by linarith [mul_pos (hB2) N.hF5])
    (by linarith [mul_pos (N.hh0) hth, mul_pos (N.hF5) N.ht])
    (by simp only [NF29.vT3]; nf29_vec N)
  have m21 : SegMeet (x 1) (x 3) (x 4) (x 0) (N.vT1) := segMeet_of_smul'
      (K := N.a0 * N.b2 * N.h0 - N.a2 * N.b0 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0)
    (s := N.b0 * N.h0 * N.h2 - N.b2 * N.h0 ^ 2)
    (t := N.b0 * N.h2 - N.b2 * N.h0)
    (l := -N.b0)
    (by
          linarith [hhF5, hh20, hF4h2, N.hF5, mul_pos (hb0) hh20, mul_pos (hb0) hh0F5, mul_pos (hA0)
              hF4h2, mul_pos (N.hh0) N.hDD, mul_pos (N.hh0) h345_2])
    (by linarith [mul_pos (N.hh0) N.hF4])
    (by
          linarith [mul_pos (hb0) hh2g, mul_pos (N.hh0) N.hDG4, mul_pos (mul_pos (hb0) hh01) hh01,
              mul_pos (mul_pos (N.hh0) hb0) hh20, mul_pos (mul_pos (N.hh2) hb0) hh01])
    (by linarith [N.hF4])
    (by linarith [mul_pos (N.hh0) N.hDD])
    (by simp only [NF29.vT1]; nf29_vec N)
  have m22 : SegMeet (x 1) (x 3) (x 4) (x 0) (N.vT3) := segMeet_of_smul'
      (K := -N.a0 * N.b0 * N.h2 + N.a0 * N.b2 * N.h0 - N.b2 * N.h0)
    (s := N.b0 * N.h0 * N.h2 - N.b2 * N.h0 ^ 2)
    (t := -N.b2 * N.h0)
    (l := N.b0)
    (by linarith [hF4h2, h345_0, mul_pos (hA0) hF4h2, mul_pos (N.hh0) N.hh2, mul_pos (h345_0) hh2g])
    (by linarith [mul_pos (N.hh0) N.hF4])
    (by
          linarith [hal, h345_0, mul_pos (hA0) hF4h2, mul_pos (hh01) hF4h2, mul_pos (h345_0) hh20,
              mul_pos (mul_pos (h345_0) hh01) hh2g])
    (by linarith [mul_pos (N.hh0) hB2])
    (by
          linarith [hA0, mul_pos (hA0) hh20, mul_pos (hA0) hF4h2, mul_pos (mul_pos (hA0) hh01) hh2g,
              mul_pos (mul_pos (N.hh0) N.hh2) hA0])
    (by simp only [NF29.vT3]; nf29_vec N)
  have eq11 : det3 (N.vT1) (x 3 - x 1) (x 6 - x 2) =
      (N.a0 * N.b2 * N.h2 - N.a0 * N.h2 * N.t - N.a2 * N.b0 * N.h2 + N.a2 * N.h0 * N.t + N.b0 * N.h2
        * N.s - N.b2 * N.h0 * N.s) * det3 N.E₁ N.E₂ N.E₃ := by
    simp only [NF29.vT1]; nf29_simp N; simp only [det3c]; ring
  have pq11 : 0 < N.a0 * N.b2 * N.h2 - N.a0 * N.h2 * N.t - N.a2 * N.b0 * N.h2 + N.a2 * N.h0 * N.t +
      N.b0 * N.h2 * N.s - N.b2 * N.h0 * N.s :=
      (by
        linarith [hf, hA0, hG5n, hhF5, hh20, hF4h2, N.hF4, mul_pos (hA2) hh20, mul_pos (N.hh2) hN,
            mul_pos (hA2) hF4h2, mul_pos (hB2) N.hF5, mul_pos (N.hh0) hkap, mul_pos
            (mul_pos (hA2) hh01) hh2g])
  have eq12 : det3 (N.vT3) (x 3 - x 1) (x 6 - x 2) =
      (N.a0 * N.b2 * N.h2 - N.a0 * N.h2 * N.t - N.a2 * N.b2 * N.h0 + N.b2 * N.h0 * N.s) * det3 N.E₁
      N.E₂ N.E₃ := by
    simp only [NF29.vT3]; nf29_simp N; simp only [det3c]; ring
  have pq12 : 0 < N.a0 * N.b2 * N.h2 - N.a0 * N.h2 * N.t - N.a2 * N.b2 * N.h0 + N.b2 * N.h0 * N.s :=
      (by linarith [mul_pos (N.hh0) hth, mul_pos (hB2) N.hF5, mul_pos (N.hF5) N.ht])
  have eq21 : det3 (N.vT1) (x 3 - x 1) (x 0 - x 4) =
      (-N.a0 * N.b2 * N.h0 + N.a2 * N.b0 * N.h0 - N.b0 * N.h2 + N.b2 * N.h0) * det3 N.E₁ N.E₂ N.E₃
      := by
    simp only [NF29.vT1]; nf29_simp N; simp only [det3c]; ring
  have pq21 : -N.a0 * N.b2 * N.h0 + N.a2 * N.b0 * N.h0 - N.b0 * N.h2 + N.b2 * N.h0 < 0 :=
      (by
        linarith [hhF5, hh20, hF4h2, N.hF5, mul_pos (hb0) hh20, mul_pos (hb0) hh0F5, mul_pos (hA0)
            hF4h2, mul_pos (N.hh0) N.hDD, mul_pos (N.hh0) h345_2])
  have eq22 : det3 (N.vT3) (x 3 - x 1) (x 0 - x 4) =
      (-N.a0 * N.b0 * N.h2 + N.a0 * N.b2 * N.h0 - N.b2 * N.h0) * det3 N.E₁ N.E₂ N.E₃ := by
    simp only [NF29.vT3]; nf29_simp N; simp only [det3c]; ring
  have pq22 : 0 < -N.a0 * N.b0 * N.h2 + N.a0 * N.b2 * N.h0 - N.b2 * N.h0 :=
      (by
        linarith [hF4h2, h345_0, mul_pos (hA0) hF4h2, mul_pos (N.hh0) N.hh2, mul_pos (h345_0) hh2g])
  have hS1 : det3 (x 2 - x 1) (x 3 - x 1) (x 6 - x 2) ≠ 0 :=
    segMeet_hS_of_smul' (v := N.vT1)
    (K := N.a0 * N.b2 * N.h2 - N.a0 * N.h2 * N.t - N.a2 * N.b0 * N.h2 + N.a2 * N.h0 * N.t + N.b0 *
        N.h2 * N.s - N.b2 * N.h0 * N.s)
    (s := -N.a0 * N.h2 ^ 2 * N.t + N.a2 * N.h0 * N.h2 * N.t + N.b0 * N.h2 ^ 2 * N.s - N.b2 * N.h0 *
          N.h2 * N.s)
    (t := N.a0 * N.b2 * N.h2 - N.a2 * N.b0 * N.h2)
    (l := N.a2 * N.t - N.b2 * N.s)
    (by
          linarith [hf, hA0, hG5n, hhF5, hh20, hF4h2, N.hF4, mul_pos (hA2) hh20, mul_pos (N.hh2) hN,
              mul_pos (hA2) hF4h2, mul_pos (hB2) N.hF5, mul_pos (N.hh0) hkap, mul_pos
              (mul_pos (hA2) hh01) hh2g])
    (by linarith [mul_pos (N.hh2) hf, mul_pos (N.hh2) N.hF4])
    (by linarith [N.d023, mul_pos (hh20) hth, mul_pos (N.d023) hh2g])
    (by linarith [mul_pos (N.hh2) N.hDD])
    (by linarith [hf, N.hF4])
    (by simp only [NF29.vT1]; nf29_vec N)
    (ne_of_lt (by linarith [hth]))
    (by rw [eq11]; exact mul_ne_zero pq11.ne' N.hD)
  have hS2 : det3 (x 4 - x 1) (x 3 - x 1) (x 0 - x 4) ≠ 0 :=
    segMeet_hS_of_smul' (v := N.vT3)
    (K := -N.a0 * N.b0 * N.h2 + N.a0 * N.b2 * N.h0 - N.b2 * N.h0)
    (s := N.b0 * N.h0 * N.h2 - N.b2 * N.h0 ^ 2)
    (t := -N.b2 * N.h0)
    (l := N.b0)
    (by linarith [hF4h2, h345_0, mul_pos (hA0) hF4h2, mul_pos (N.hh0) N.hh2, mul_pos (h345_0) hh2g])
    (by linarith [mul_pos (N.hh0) N.hF4])
    (by
          linarith [hal, h345_0, mul_pos (hA0) hF4h2, mul_pos (hh01) hF4h2, mul_pos (h345_0) hh20,
              mul_pos (mul_pos (h345_0) hh01) hh2g])
    (by linarith [mul_pos (N.hh0) hB2])
    (by
          linarith [hA0, mul_pos (hA0) hh20, mul_pos (hA0) hF4h2, mul_pos (mul_pos (hA0) hh01) hh2g,
              mul_pos (mul_pos (N.hh0) N.hh2) hA0])
    (by simp only [NF29.vT3]; nf29_vec N)
    (ne_of_gt hb0)
    (by rw [eq22]; exact mul_ne_zero pq22.ne' N.hD)
  have o1' : OneTieAt (univ.image x) N.vT1 := o1.of_eq_smul N.vT1_eq N.hDi
  have o2' : OneTieAt (univ.image x) N.vT3 := o2.of_eq_smul N.vT3_eq N.hDi
  have hno' : NoTieAt (univ.image x) N.vT1 ∨ NoTieAt (univ.image x) N.vT3 := by
    rcases hno with hnu | hnv
    · exact Or.inl (hnu.of_eq_smul N.vT1_eq N.hDi)
    · exact Or.inr (hnv.of_eq_smul N.vT3_eq N.hDi)
  have hp1 := prod_pos_of_eq N.hD eq11 eq12 pq11 pq12
  have hn2 := prod_neg_of_eq N.hD eq21 eq22 pq21 pq22
  rcases pair_core (img29 1) (img29 3) (img29 2) (img29 6) (img29 1) (img29 3) (img29 4) (img29 0)
    (List.nodup4_img N.inj (by decide : [(1 : Fin 7), 2, 3, 6].Nodup))
    (List.nodup4_img N.inj (by decide : [(1 : Fin 7), 4, 3, 0].Nodup))
    m11 m12 m21 m22 hS1 hS2 hp1 hn2 o1' o2' hno' with hR2 | ⟨hR1, hdot⟩
  · exact NF29.cert_k3_T3o N hh01 hh20 hth hh2g hh0F5 hF4h2 hN hal hhF5 hR2
  · exact NF29.cert_k3_T1o N hh01 hF45 hh20 hth hf hh2g hR1 ⟨⟨N, by linarith [hth],
      by linarith [hh2g]⟩, N.dot_T1T3 hdot⟩


theorem NF29.cert_k3_X (N : NF29 x)
    (hA2 : 0 < -N.a2)
    (hb0 : 0 < N.b0)
    (hV3 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2)
    (hh01 : 0 < -N.h0 + 1)
    (hG4 : 0 < -N.b0 * N.h2 + N.b2 * N.h0 + N.b0 - N.b2)
    (hG5n : 0 < -N.a0 * N.h2 + N.a2 * N.h0 + N.a0 - N.a2)
    (hh20 : 0 < -N.h0 + N.h2)
    (hh2g : 0 < N.h2 - 1)
    (hkap : 0 < -N.a2 - N.h2 + 1)
    (hh2F4 : 0 < -N.b0 * N.h2 + N.b2 * N.h0 + N.h2)
    (hXf : 0 < -N.a0 * N.t + N.b0 * N.s - N.h0 * N.t - N.b0 - N.s + 1)
    (hb01 : 0 < -N.b0 + 1)
    (hsg : 0 < N.a2 * N.t - N.b2 * N.s + N.h2 * N.t - N.a2 - N.h2 - N.t + 1)
    (hXa2 : 0 < -N.a0 * N.b2 + N.a2 * N.b0 + N.b0 * N.h2 - N.b2 * N.h0 - N.a2 - N.b0 - N.h2 + 1)
    (o1 : OneTieAt (univ.image x) (view29 x (.inl (0, 5))))
    (o2 : OneTieAt (univ.image x) (view29 x (.inr 1)))
    (hno : NoTieAt (univ.image x) (view29 x (.inl (0,
        5))) ∨ NoTieAt (univ.image x) (view29 x (.inr 1))) :
    Cert29 x := by
  have hA0 : 0 < -N.a0 := by linarith [N.ha0]
  have hB2 : 0 < -N.b2 := by linarith [N.hb2]
  have h345_0 : 0 < 1 - N.a0 - N.b0 - N.h0 := by linarith [N.t345_0]
  have h345_2 : 0 < 1 - N.a2 - N.b2 - N.h2 := by linarith [N.t345_2]
  have m11 : SegMeet (x 5) (x 4) (x 1) (x 3) (x 5 - x 0) := segMeet_of_smul' (K := -N.a0 - N.b0 + 1)
    (s := -N.a0)
    (t := N.h0)
    (l := -1)
    (by linarith [hA0, hb01])
    (by linarith [hA0])
    (by linarith [hb01])
    (by linarith [N.hh0])
    (by linarith [h345_0])
    (by nf29_vec N)
  have m12 : SegMeet (x 5) (x 4) (x 1) (x 3) (N.vT2) := segMeet_of_smul'
      (K := -N.a2 - N.b2 - N.h2 + 1)
    (s := -N.a2 - N.h2 + 1)
    (t := 0)
    (l := -1)
    (by linarith [h345_2])
    (by linarith [hkap])
    (by linarith [hB2])
    (le_of_eq (by ring))
    (by linarith [h345_2])
    (by simp only [NF29.vT2]; nf29_vec N)
  have m21 : SegMeet (x 4) (x 0) (x 2) (x 5) (x 5 - x 0) := segMeet_of_smul'
      (K := N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2)
    (s := N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2)
    (t := N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2)
    (l := N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2)
    (by linarith [hV3])
    (by linarith [hV3])
    (le_of_eq (by ring))
    (by linarith [hV3])
    (le_of_eq (by ring))
    (by nf29_vec N)
  have m22 : SegMeet (x 4) (x 0) (x 2) (x 5) (N.vT2) := segMeet_of_smul'
      (K := N.a0 * N.b2 * N.h2 - N.a2 * N.b0 * N.h2 - N.b0 * N.h2 ^ 2 + N.b2 * N.h0 * N.h2 - N.a2 *
        N.h0 + N.b0 * N.h2 - N.b2 * N.h0 - N.b2 * N.h2 - N.h0 * N.h2 + N.h0)
    (s := -N.a2 * N.h2 - N.b2 * N.h2 - N.h2 ^ 2 + N.h2)
    (t := N.a0 * N.b2 * N.h2 - N.a2 * N.b0 * N.h2 - N.b0 * N.h2 ^ 2 + N.b2 * N.h0 * N.h2 + N.b0 *
          N.h2 - N.b2 * N.h2)
    (l := -N.a0 * N.h2 + N.a2 * N.h0 - N.b0 * N.h2 + N.b2 * N.h0 - N.h0 + N.h2)
    (by
          linarith [hB2, hV3, h345_2, N.hDG4, mul_pos (hA2) hh01, mul_pos (hb0) hG5n, mul_pos
              (N.hh2) hG4, mul_pos (N.hDD) hh2g, mul_pos (N.hF5) hh2g, mul_pos (N.hh2) N.hDG5,
              mul_pos (mul_pos (N.hh0) hA2) hb0, mul_pos (mul_pos (hb0) hh01) hkap, mul_pos
              (mul_pos (hb0) hh2g) hkap, mul_pos (mul_pos (hA0) hh2g) hb01, mul_pos
              (mul_pos (hh20) hkap) hb01, mul_pos (mul_pos (hh01) hh2g) hh2g, mul_pos
              (mul_pos (hh2g) hh2g) hb01, mul_pos (mul_pos (N.hh0) hA2) hh2g, mul_pos
              (mul_pos (N.hh0) hkap) hb01, mul_pos (mul_pos (h345_2) hh01) hh2g, mul_pos
              (mul_pos (h345_0) hh2g) hh2g, mul_pos (mul_pos (N.hh2) N.hh2) h345_0])
    (by linarith [h345_2, mul_pos (h345_2) hh2g])
    (by linarith [mul_pos (hV3) hkap, mul_pos (h345_2) N.hF5])
    (by linarith [mul_pos (N.hh2) N.hDG4])
    (by linarith [mul_pos (N.hh0) h345_2])
    (by simp only [NF29.vT2]; nf29_vec N)
  have eq11 : det3 (x 5 - x 0) (x 4 - x 5) (x 3 - x 1) = (-N.a0 - N.b0 + 1) * det3 N.E₁ N.E₂ N.E₃ :=
      by
    nf29_simp N; simp only [det3c]; ring
  have pq11 : 0 < -N.a0 - N.b0 + 1 := (by linarith [hA0, hb01])
  have eq12 : det3 (N.vT2) (x 4 - x 5) (x 3 - x 1) = (-N.a2 - N.b2 - N.h2 + 1) * det3 N.E₁ N.E₂ N.E₃
      := by
    simp only [NF29.vT2]; nf29_simp N; simp only [det3c]; ring
  have pq12 : 0 < -N.a2 - N.b2 - N.h2 + 1 := (by linarith [h345_2])
  have eq21 : det3 (x 5 - x 0) (x 0 - x 4) (x 5 - x 2) =
      (-N.a0 * N.h2 + N.a2 * N.h0 - N.b0 * N.h2 + N.b2 * N.h0 - N.h0 + N.h2) * det3 N.E₁ N.E₂ N.E₃
      := by
    nf29_simp N; simp only [det3c]; ring
  have pq21 : -N.a0 * N.h2 + N.a2 * N.h0 - N.b0 * N.h2 + N.b2 * N.h0 - N.h0 + N.h2 < 0 :=
      (by linarith [hV3])
  have eq22 : det3 (N.vT2) (x 0 - x 4) (x 5 - x 2) =
      (N.a0 * N.b2 * N.h2 - N.a2 * N.b0 * N.h2 - N.b0 * N.h2 ^ 2 + N.b2 * N.h0 * N.h2 - N.a2 * N.h0
        + N.b0 * N.h2 - N.b2 * N.h0 - N.b2 * N.h2 - N.h0 * N.h2 + N.h0) * det3 N.E₁ N.E₂ N.E₃ := by
    simp only [NF29.vT2]; nf29_simp N; simp only [det3c]; ring
  have pq22 : 0 < N.a0 * N.b2 * N.h2 - N.a2 * N.b0 * N.h2 - N.b0 * N.h2 ^ 2 + N.b2 * N.h0 * N.h2 -
      N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 - N.b2 * N.h2 - N.h0 * N.h2 + N.h0 :=
      (by
        linarith [hB2, hV3, h345_2, N.hDG4, mul_pos (hA2) hh01, mul_pos (hb0) hG5n, mul_pos (N.hh2)
            hG4, mul_pos (N.hDD) hh2g, mul_pos (N.hF5) hh2g, mul_pos (N.hh2) N.hDG5, mul_pos
            (mul_pos (N.hh0) hA2) hb0, mul_pos (mul_pos (hb0) hh01) hkap, mul_pos
            (mul_pos (hb0) hh2g) hkap, mul_pos (mul_pos (hA0) hh2g) hb01, mul_pos
            (mul_pos (hh20) hkap) hb01, mul_pos (mul_pos (hh01) hh2g) hh2g, mul_pos
            (mul_pos (hh2g) hh2g) hb01, mul_pos (mul_pos (N.hh0) hA2) hh2g, mul_pos
            (mul_pos (N.hh0) hkap) hb01, mul_pos (mul_pos (h345_2) hh01) hh2g, mul_pos
            (mul_pos (h345_0) hh2g) hh2g, mul_pos (mul_pos (N.hh2) N.hh2) h345_0])
  have hS1 : det3 (x 1 - x 5) (x 4 - x 5) (x 3 - x 1) ≠ 0 :=
    segMeet_hS_of_smul' (v := (x 5 - x 0))
    (K := -N.a0 - N.b0 + 1)
    (s := -N.a0)
    (t := N.h0)
    (l := -1)
    (by linarith [hA0, hb01])
    (by linarith [hA0])
    (by linarith [hb01])
    (by linarith [N.hh0])
    (by linarith [h345_0])
    (by nf29_vec N)
    (by norm_num)
    (by rw [eq11]; exact mul_ne_zero pq11.ne' N.hD)
  have hS2 : det3 (x 2 - x 4) (x 0 - x 4) (x 5 - x 2) ≠ 0 :=
    segMeet_hS_of_smul' (v := N.vT2)
    (K := N.a0 * N.b2 * N.h2 - N.a2 * N.b0 * N.h2 - N.b0 * N.h2 ^ 2 + N.b2 * N.h0 * N.h2 - N.a2 *
        N.h0 + N.b0 * N.h2 - N.b2 * N.h0 - N.b2 * N.h2 - N.h0 * N.h2 + N.h0)
    (s := -N.a2 * N.h2 - N.b2 * N.h2 - N.h2 ^ 2 + N.h2)
    (t := N.a0 * N.b2 * N.h2 - N.a2 * N.b0 * N.h2 - N.b0 * N.h2 ^ 2 + N.b2 * N.h0 * N.h2 + N.b0 *
          N.h2 - N.b2 * N.h2)
    (l := -N.a0 * N.h2 + N.a2 * N.h0 - N.b0 * N.h2 + N.b2 * N.h0 - N.h0 + N.h2)
    (by
          linarith [hB2, hV3, h345_2, N.hDG4, mul_pos (hA2) hh01, mul_pos (hb0) hG5n, mul_pos
              (N.hh2) hG4, mul_pos (N.hDD) hh2g, mul_pos (N.hF5) hh2g, mul_pos (N.hh2) N.hDG5,
              mul_pos (mul_pos (N.hh0) hA2) hb0, mul_pos (mul_pos (hb0) hh01) hkap, mul_pos
              (mul_pos (hb0) hh2g) hkap, mul_pos (mul_pos (hA0) hh2g) hb01, mul_pos
              (mul_pos (hh20) hkap) hb01, mul_pos (mul_pos (hh01) hh2g) hh2g, mul_pos
              (mul_pos (hh2g) hh2g) hb01, mul_pos (mul_pos (N.hh0) hA2) hh2g, mul_pos
              (mul_pos (N.hh0) hkap) hb01, mul_pos (mul_pos (h345_2) hh01) hh2g, mul_pos
              (mul_pos (h345_0) hh2g) hh2g, mul_pos (mul_pos (N.hh2) N.hh2) h345_0])
    (by linarith [h345_2, mul_pos (h345_2) hh2g])
    (by linarith [mul_pos (hV3) hkap, mul_pos (h345_2) N.hF5])
    (by linarith [mul_pos (N.hh2) N.hDG4])
    (by linarith [mul_pos (N.hh0) h345_2])
    (by simp only [NF29.vT2]; nf29_vec N)
    (ne_of_lt (by linarith [hV3]))
    (by rw [eq22]; exact mul_ne_zero pq22.ne' N.hD)
  have o1' : OneTieAt (univ.image x) (x 5 - x 0) := o1
  have o2' : OneTieAt (univ.image x) N.vT2 := o2.of_eq_smul N.vT2_eq N.hDni
  have hno' : NoTieAt (univ.image x) (x 5 - x 0) ∨ NoTieAt (univ.image x) N.vT2 := by
    rcases hno with hnu | hnv
    · exact Or.inl (hnu)
    · exact Or.inr (hnv.of_eq_smul N.vT2_eq N.hDni)
  have hp1 := prod_pos_of_eq N.hD eq11 eq12 pq11 pq12
  have hn2 := prod_neg_of_eq N.hD eq21 eq22 pq21 pq22
  rcases pair_core (img29 5) (img29 4) (img29 1) (img29 3) (img29 4) (img29 0) (img29 2) (img29 5)
    (List.nodup4_img N.inj (by decide : [(5 : Fin 7), 1, 4, 3].Nodup))
    (List.nodup4_img N.inj (by decide : [(4 : Fin 7), 2, 0, 5].Nodup))
    m11 m12 m21 m22 hS1 hS2 hp1 hn2 o1' o2' hno' with hR2 | ⟨hR1, hdot⟩
  · exact NF29.cert_k3_T2o N hV3 hh2g hkap hsg hR2 ⟨N, by linarith [hh01], by linarith [hh2g]⟩
  · exact NF29.cert_k3_Xa N hh2F4 hXf hb01 hXa2 hR1


theorem NF29.cert_k3_P13 (N : NF29 x)
    (hV3 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2)
    (hh01 : 0 < -N.h0 + 1)
    (hh2g : 0 < N.h2 - 1)
    (hkap : 0 < -N.a2 - N.h2 + 1)
    (hh0F5 : 0 < N.a0 * N.h2 - N.a2 * N.h0 + N.h0)
    (hh2F4 : 0 < -N.b0 * N.h2 + N.b2 * N.h0 + N.h2)
    (hsg : 0 < N.a2 * N.t - N.b2 * N.s + N.h2 * N.t - N.a2 - N.h2 - N.t + 1)
    (hL36n : 0 < N.a0 * N.h2 * N.t - N.b2 * N.h0 * N.s - N.h0 * N.h2 * N.s - N.a0 * N.h2)
    (hW43 : 0 < -N.a0 * N.h2 * N.t + N.b2 * N.h0 * N.s - N.h0 * N.h2 * N.t - N.b2 * N.h0)
    (hAh0 : 0 < -N.a0 - N.h0)
    (hs1g : 0 < N.s - 1)
    (o1 : OneTieAt (univ.image x) (view29 x (.inr 3)))
    (o2 : OneTieAt (univ.image x) (view29 x (.inr 1)))
    (hno : NoTieAt (univ.image x) (view29 x (.inr 3)) ∨
        NoTieAt (univ.image x) (view29 x (.inr 1))) :
    Cert29 x := by
  have hA0 : 0 < -N.a0 := by linarith [N.ha0]
  have hB2 : 0 < -N.b2 := by linarith [N.hb2]
  have h345_0 : 0 < 1 - N.a0 - N.b0 - N.h0 := by linarith [N.t345_0]
  have h345_2 : 0 < 1 - N.a2 - N.b2 - N.h2 := by linarith [N.t345_2]
  have m11 : SegMeet (x 1) (x 3) (x 4) (x 5) (N.vT3) := segMeet_of_smul'
      (K := -N.a0 * N.h2 - N.b2 * N.h0)
    (s := N.h0 * N.h2)
    (t := -N.b2 * N.h0)
    (l := 1)
    (by linarith [hA0, mul_pos (hA0) hh2g, mul_pos (N.hh0) hB2])
    (by linarith [mul_pos (N.hh0) N.hh2])
    (by linarith [hAh0, mul_pos (hh2g) hAh0, mul_pos (N.hh0) hB2])
    (by linarith [mul_pos (N.hh0) hB2])
    (by linarith [hA0, mul_pos (hA0) hh2g])
    (by simp only [NF29.vT3]; nf29_vec N)
  have m12 : SegMeet (x 1) (x 3) (x 4) (x 5) (N.vT2) := segMeet_of_smul'
      (K := -N.a2 - N.b2 - N.h2 + 1)
    (s := 0)
    (t := -N.b2)
    (l := 1)
    (by linarith [h345_2])
    (le_of_eq (by ring))
    (by linarith [h345_2])
    (by linarith [hB2])
    (by linarith [hkap])
    (by simp only [NF29.vT2]; nf29_vec N)
  have m21 : SegMeet (x 4) (x 0) (x 2) (x 5) (N.vT3) := segMeet_of_smul'
      (K := N.a0 * N.b0 * N.h2 ^ 2 - N.a0 * N.b2 * N.h0 * N.h2 - N.a2 * N.b0 * N.h0 * N.h2 + N.a2 *
        N.b2 * N.h0 ^ 2 + N.h0 * N.h2)
    (s := N.a0 * N.h2 ^ 2 - N.a2 * N.h0 * N.h2 + N.h0 * N.h2)
    (t := N.a0 * N.b0 * N.h2 ^ 2 - N.a0 * N.b2 * N.h0 * N.h2 - N.a2 * N.b0 * N.h0 * N.h2 + N.a2 *
          N.b2 * N.h0 ^ 2 + N.b0 * N.h0 * N.h2 - N.b2 * N.h0 ^ 2)
    (l := N.a0 * N.h2 - N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 + N.h0 - N.h2)
    (by
          linarith [hh2F4, mul_pos (hV3) hh01, mul_pos (N.hF5) hh2F4, mul_pos (N.hF4) hh0F5, mul_pos
              (mul_pos (N.hh0) N.hh2) hV3, mul_pos (mul_pos (hh01) hh2g) hh0F5, mul_pos
              (mul_pos (N.hh0) N.hh2) hh2F4])
    (by linarith [mul_pos (N.hh2) hh0F5])
    (by linarith [mul_pos (N.hF5) hh2F4])
    (by linarith [mul_pos (N.hF4) hh0F5])
    (by linarith [mul_pos (N.hh0) hh2F4])
    (by simp only [NF29.vT3]; nf29_vec N)
  have m22 : SegMeet (x 4) (x 0) (x 2) (x 5) (N.vT2) := segMeet_of_smul'
      (K := N.a0 * N.b2 * N.h2 - N.a2 * N.b0 * N.h2 - N.b0 * N.h2 ^ 2 + N.b2 * N.h0 * N.h2 - N.a2 *
        N.h0 + N.b0 * N.h2 - N.b2 * N.h0 - N.b2 * N.h2 - N.h0 * N.h2 + N.h0)
    (s := -N.a2 * N.h2 - N.b2 * N.h2 - N.h2 ^ 2 + N.h2)
    (t := N.a0 * N.b2 * N.h2 - N.a2 * N.b0 * N.h2 - N.b0 * N.h2 ^ 2 + N.b2 * N.h0 * N.h2 + N.b0 *
          N.h2 - N.b2 * N.h2)
    (l := -N.a0 * N.h2 + N.a2 * N.h0 - N.b0 * N.h2 + N.b2 * N.h0 - N.h0 + N.h2)
    (by
          linarith [hV3, h345_2, mul_pos (N.hh2) N.hDG5, mul_pos (N.hh2) N.hDG4, mul_pos
              (mul_pos (h345_2) hh01) hh2g, mul_pos (mul_pos (N.hh2) N.hh2) h345_0])
    (by linarith [h345_2, mul_pos (h345_2) hh2g])
    (by linarith [mul_pos (hV3) hkap, mul_pos (hB2) N.hF5, mul_pos (N.hF5) hkap])
    (by linarith [mul_pos (N.hh2) N.hDG4])
    (by linarith [mul_pos (N.hh0) h345_2])
    (by simp only [NF29.vT2]; nf29_vec N)
  have eq11 : det3 (N.vT3) (x 3 - x 1) (x 5 - x 4) = (-N.a0 * N.h2 - N.b2 * N.h0) * det3 N.E₁ N.E₂
      N.E₃ := by
    simp only [NF29.vT3]; nf29_simp N; simp only [det3c]; ring
  have pq11 : 0 < -N.a0 * N.h2 - N.b2 * N.h0 :=
      (by linarith [hA0, mul_pos (hA0) hh2g, mul_pos (N.hh0) hB2])
  have eq12 : det3 (N.vT2) (x 3 - x 1) (x 5 - x 4) = (-N.a2 - N.b2 - N.h2 + 1) * det3 N.E₁ N.E₂ N.E₃
      := by
    simp only [NF29.vT2]; nf29_simp N; simp only [det3c]; ring
  have pq12 : 0 < -N.a2 - N.b2 - N.h2 + 1 := (by linarith [h345_2])
  have eq21 : det3 (N.vT3) (x 0 - x 4) (x 5 - x 2) =
      (-N.a0 * N.b0 * N.h2 ^ 2 + N.a0 * N.b2 * N.h0 * N.h2 + N.a2 * N.b0 * N.h0 * N.h2 - N.a2 * N.b2
        * N.h0 ^ 2 - N.h0 * N.h2) * det3 N.E₁ N.E₂ N.E₃ := by
    simp only [NF29.vT3]; nf29_simp N; simp only [det3c]; ring
  have pq21 : -N.a0 * N.b0 * N.h2 ^ 2 + N.a0 * N.b2 * N.h0 * N.h2 + N.a2 * N.b0 * N.h0 * N.h2 - N.a2
      * N.b2 * N.h0 ^ 2 - N.h0 * N.h2 < 0 :=
      (by
        linarith [hh2F4, mul_pos (hV3) hh01, mul_pos (N.hF5) hh2F4, mul_pos (N.hF4) hh0F5, mul_pos
            (mul_pos (N.hh0) N.hh2) hV3, mul_pos (mul_pos (hh01) hh2g) hh0F5, mul_pos
            (mul_pos (N.hh0) N.hh2) hh2F4])
  have eq22 : det3 (N.vT2) (x 0 - x 4) (x 5 - x 2) =
      (N.a0 * N.b2 * N.h2 - N.a2 * N.b0 * N.h2 - N.b0 * N.h2 ^ 2 + N.b2 * N.h0 * N.h2 - N.a2 * N.h0
        + N.b0 * N.h2 - N.b2 * N.h0 - N.b2 * N.h2 - N.h0 * N.h2 + N.h0) * det3 N.E₁ N.E₂ N.E₃ := by
    simp only [NF29.vT2]; nf29_simp N; simp only [det3c]; ring
  have pq22 : 0 < N.a0 * N.b2 * N.h2 - N.a2 * N.b0 * N.h2 - N.b0 * N.h2 ^ 2 + N.b2 * N.h0 * N.h2 -
      N.a2 * N.h0 + N.b0 * N.h2 - N.b2 * N.h0 - N.b2 * N.h2 - N.h0 * N.h2 + N.h0 :=
      (by
        linarith [hV3, h345_2, mul_pos (N.hh2) N.hDG5, mul_pos (N.hh2) N.hDG4, mul_pos
            (mul_pos (h345_2) hh01) hh2g, mul_pos (mul_pos (N.hh2) N.hh2) h345_0])
  have hS1 : det3 (x 4 - x 1) (x 3 - x 1) (x 5 - x 4) ≠ 0 :=
    segMeet_hS_of_smul' (v := N.vT3)
    (K := -N.a0 * N.h2 - N.b2 * N.h0)
    (s := N.h0 * N.h2)
    (t := -N.b2 * N.h0)
    (l := 1)
    (by linarith [hA0, mul_pos (hA0) hh2g, mul_pos (N.hh0) hB2])
    (by linarith [mul_pos (N.hh0) N.hh2])
    (by linarith [hAh0, mul_pos (hh2g) hAh0, mul_pos (N.hh0) hB2])
    (by linarith [mul_pos (N.hh0) hB2])
    (by linarith [hA0, mul_pos (hA0) hh2g])
    (by simp only [NF29.vT3]; nf29_vec N)
    (by norm_num)
    (by rw [eq11]; exact mul_ne_zero pq11.ne' N.hD)
  have hS2 : det3 (x 2 - x 4) (x 0 - x 4) (x 5 - x 2) ≠ 0 :=
    segMeet_hS_of_smul' (v := N.vT2)
    (K := N.a0 * N.b2 * N.h2 - N.a2 * N.b0 * N.h2 - N.b0 * N.h2 ^ 2 + N.b2 * N.h0 * N.h2 - N.a2 *
        N.h0 + N.b0 * N.h2 - N.b2 * N.h0 - N.b2 * N.h2 - N.h0 * N.h2 + N.h0)
    (s := -N.a2 * N.h2 - N.b2 * N.h2 - N.h2 ^ 2 + N.h2)
    (t := N.a0 * N.b2 * N.h2 - N.a2 * N.b0 * N.h2 - N.b0 * N.h2 ^ 2 + N.b2 * N.h0 * N.h2 + N.b0 *
          N.h2 - N.b2 * N.h2)
    (l := -N.a0 * N.h2 + N.a2 * N.h0 - N.b0 * N.h2 + N.b2 * N.h0 - N.h0 + N.h2)
    (by
          linarith [hV3, h345_2, mul_pos (N.hh2) N.hDG5, mul_pos (N.hh2) N.hDG4, mul_pos
              (mul_pos (h345_2) hh01) hh2g, mul_pos (mul_pos (N.hh2) N.hh2) h345_0])
    (by linarith [h345_2, mul_pos (h345_2) hh2g])
    (by linarith [mul_pos (hV3) hkap, mul_pos (hB2) N.hF5, mul_pos (N.hF5) hkap])
    (by linarith [mul_pos (N.hh2) N.hDG4])
    (by linarith [mul_pos (N.hh0) h345_2])
    (by simp only [NF29.vT2]; nf29_vec N)
    (ne_of_lt (by linarith [hV3]))
    (by rw [eq22]; exact mul_ne_zero pq22.ne' N.hD)
  have o1' : OneTieAt (univ.image x) N.vT3 := o1.of_eq_smul N.vT3_eq N.hDi
  have o2' : OneTieAt (univ.image x) N.vT2 := o2.of_eq_smul N.vT2_eq N.hDni
  have hno' : NoTieAt (univ.image x) N.vT3 ∨ NoTieAt (univ.image x) N.vT2 := by
    rcases hno with hnu | hnv
    · exact Or.inl (hnu.of_eq_smul N.vT3_eq N.hDi)
    · exact Or.inr (hnv.of_eq_smul N.vT2_eq N.hDni)
  have hp1 := prod_pos_of_eq N.hD eq11 eq12 pq11 pq12
  have hn2 := prod_neg_of_eq N.hD eq21 eq22 pq21 pq22
  rcases pair_core (img29 1) (img29 3) (img29 4) (img29 5) (img29 4) (img29 0) (img29 2) (img29 5)
    (List.nodup4_img N.inj (by decide : [(1 : Fin 7), 4, 3, 5].Nodup))
    (List.nodup4_img N.inj (by decide : [(4 : Fin 7), 2, 0, 5].Nodup))
    m11 m12 m21 m22 hS1 hS2 hp1 hn2 o1' o2' hno' with hR2 | ⟨hR1, hdot⟩
  · exact NF29.cert_k3_T2o N hV3 hh2g hkap hsg hR2 ⟨N, by linarith [hh01], by linarith [hh2g]⟩
  · exact NF29.cert_k3_T3s N hh2g hh0F5 hh2F4 hL36n hW43 hAh0 hs1g hR1


end Minimality

end
