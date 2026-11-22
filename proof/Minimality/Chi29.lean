module

public import Minimality.Type29Leaves
public import Minimality.GenQuad

@[expose] public section

/-!
# Type 29: the 4-point volumes (chirotope) in normal-form coordinates

`chi(ijkl) = Split.det3 (x j - x i) (x k - x i) (x l - x i)` for the 35 four-subsets `i < j < k < l` of the seven
vertices of a type-29 normal form.  For each subset:
* `chi_ijkl_eq`: `chi = N.D * P`, `P` a polynomial in the eight parameters (`N.D = det3 E1 E2 E3`);
* `chi_ijkl_sign`: `0 < N.D * chi` (or `< 0`), i.e. the sign of `P`, from the `NF29` fields.
Extra named hypotheses (cell facts, not NF29 fields), only where the census needs them:
`hb0 : 0 < b0` (0134, 0136), `ha2 : a2 < 0` (1235), `hq : h0 * del2 < h2 * del0` (0245, 0246).
Two entries vary on the dominant cell and have identities only (`chi_1236_eq`, `chi_0256_eq`); `chi_1456 = 0`.
`chi_pos_of_D_pos`, `chi_neg_of_D_pos`: with `0 < N.D` the sign statements are those of `chi` itself.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality

namespace Minimality.NF29

variable {x : Fin 7 → ℝ³}

theorem split_det3_eq (a b c : ℝ³) : Split.det3 a b c = det3 a b c := by
  simp only [Split.det3, det3, cross, PiLp.inner_apply, Fin.sum_univ_three]
  simp
  ring

theorem chi_pos_of_D_pos {N : NF29 x} {c : ℝ} (hD : 0 < N.D) (h : 0 < N.D * c) : 0 < c :=
  pos_of_mul_pos_right h hD.le

theorem chi_neg_of_D_pos {N : NF29 x} {c : ℝ} (hD : 0 < N.D) (h : N.D * c < 0) : c < 0 :=
  neg_of_mul_neg_right h hD.le

theorem D_sq_pos (N : NF29 x) : 0 < N.D ^ 2 :=
  lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 N.hD))

macro "chi_eq_tac " N:term:max : tactic =>
  `(tactic| (rw [split_det3_eq]; nf29_simp $N; simp only [det3c, NF29.D]; ring))

theorem chi_0123_eq (N : NF29 x) :
    Split.det3 (x 1 - x 0) (x 2 - x 0) (x 3 - x 0) = N.D * (((-1 : ℝ)) * N.b0 * N.a2 + ((1 : ℝ)) * N.a0 * N.b2) := by
  chi_eq_tac N

theorem chi_0123_sign (N : NF29 x)  :
    0 < N.D * Split.det3 (x 1 - x 0) (x 2 - x 0) (x 3 - x 0) := by
  rw [chi_0123_eq N]
  have hP : 0 < ((-1 : ℝ)) * N.b0 * N.a2 + ((1 : ℝ)) * N.a0 * N.b2 := by
    nlinarith [mul_pos N.hh0 N.hs, mul_pos N.hh0 N.ht, mul_pos N.hh2 N.hs, mul_pos N.hh2 N.ht, mul_pos N.hs N.ht, mul_pos_of_neg_of_neg N.ha0 N.hb2, N.hh0, N.hh2, N.ha0, N.hb2, N.t345_0, N.t345_2, N.hF4, N.hF5, N.hDD, N.hDG4, N.hDG5, N.hE35, N.hE24, N.hs, N.ht, N.hst, N.d023, N.d035, N.d234]
  have e : N.D * (N.D * (((-1 : ℝ)) * N.b0 * N.a2 + ((1 : ℝ)) * N.a0 * N.b2)) = N.D ^ 2 * (((-1 : ℝ)) * N.b0 * N.a2 + ((1 : ℝ)) * N.a0 * N.b2) := by ring
  rw [e]; exact mul_pos (D_sq_pos N) hP

theorem chi_0124_eq (N : NF29 x) :
    Split.det3 (x 1 - x 0) (x 2 - x 0) (x 4 - x 0) = N.D * (((-1 : ℝ)) * N.h0 * N.b2 + ((1 : ℝ)) * N.b0 * N.h2) := by
  chi_eq_tac N

theorem chi_0124_sign (N : NF29 x)  :
    0 < N.D * Split.det3 (x 1 - x 0) (x 2 - x 0) (x 4 - x 0) := by
  rw [chi_0124_eq N]
  have hP : 0 < ((-1 : ℝ)) * N.h0 * N.b2 + ((1 : ℝ)) * N.b0 * N.h2 := by
    nlinarith [mul_pos N.hh0 N.hs, mul_pos N.hh0 N.ht, mul_pos N.hh2 N.hs, mul_pos N.hh2 N.ht, mul_pos N.hs N.ht, mul_pos_of_neg_of_neg N.ha0 N.hb2, N.hh0, N.hh2, N.ha0, N.hb2, N.t345_0, N.t345_2, N.hF4, N.hF5, N.hDD, N.hDG4, N.hDG5, N.hE35, N.hE24, N.hs, N.ht, N.hst, N.d023, N.d035, N.d234]
  have e : N.D * (N.D * (((-1 : ℝ)) * N.h0 * N.b2 + ((1 : ℝ)) * N.b0 * N.h2)) = N.D ^ 2 * (((-1 : ℝ)) * N.h0 * N.b2 + ((1 : ℝ)) * N.b0 * N.h2) := by ring
  rw [e]; exact mul_pos (D_sq_pos N) hP

theorem chi_0125_eq (N : NF29 x) :
    Split.det3 (x 1 - x 0) (x 2 - x 0) (x 5 - x 0) = N.D * (((1 : ℝ)) * N.h0 * N.a2 + ((-1 : ℝ)) * N.a0 * N.h2) := by
  chi_eq_tac N

theorem chi_0125_sign (N : NF29 x)  :
    0 < N.D * Split.det3 (x 1 - x 0) (x 2 - x 0) (x 5 - x 0) := by
  rw [chi_0125_eq N]
  have hP : 0 < ((1 : ℝ)) * N.h0 * N.a2 + ((-1 : ℝ)) * N.a0 * N.h2 := by
    nlinarith [mul_pos N.hh0 N.hs, mul_pos N.hh0 N.ht, mul_pos N.hh2 N.hs, mul_pos N.hh2 N.ht, mul_pos N.hs N.ht, mul_pos_of_neg_of_neg N.ha0 N.hb2, N.hh0, N.hh2, N.ha0, N.hb2, N.t345_0, N.t345_2, N.hF4, N.hF5, N.hDD, N.hDG4, N.hDG5, N.hE35, N.hE24, N.hs, N.ht, N.hst, N.d023, N.d035, N.d234]
  have e : N.D * (N.D * (((1 : ℝ)) * N.h0 * N.a2 + ((-1 : ℝ)) * N.a0 * N.h2)) = N.D ^ 2 * (((1 : ℝ)) * N.h0 * N.a2 + ((-1 : ℝ)) * N.a0 * N.h2) := by ring
  rw [e]; exact mul_pos (D_sq_pos N) hP

theorem chi_0126_eq (N : NF29 x) :
    Split.det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) = N.D * (((-1 : ℝ)) * N.h0 * N.b2 * N.s + ((1 : ℝ)) * N.h0 * N.a2 * N.t + ((1 : ℝ)) * N.b0 * N.h2 * N.s + ((-1 : ℝ)) * N.a0 * N.h2 * N.t) := by
  chi_eq_tac N

theorem chi_0126_sign (N : NF29 x)  :
    0 < N.D * Split.det3 (x 1 - x 0) (x 2 - x 0) (x 6 - x 0) := by
  rw [chi_0126_eq N]
  have hP : 0 < ((-1 : ℝ)) * N.h0 * N.b2 * N.s + ((1 : ℝ)) * N.h0 * N.a2 * N.t + ((1 : ℝ)) * N.b0 * N.h2 * N.s + ((-1 : ℝ)) * N.a0 * N.h2 * N.t := by
    nlinarith [mul_pos N.hh0 N.hs, mul_pos N.hh0 N.ht, mul_pos N.hh2 N.hs, mul_pos N.hh2 N.ht, mul_pos N.hs N.ht, mul_pos_of_neg_of_neg N.ha0 N.hb2, N.hh0, N.hh2, N.ha0, N.hb2, N.t345_0, N.t345_2, N.hF4, N.hF5, N.hDD, N.hDG4, N.hDG5, N.hE35, N.hE24, N.hs, N.ht, N.hst, N.d023, N.d035, N.d234]
  have e : N.D * (N.D * (((-1 : ℝ)) * N.h0 * N.b2 * N.s + ((1 : ℝ)) * N.h0 * N.a2 * N.t + ((1 : ℝ)) * N.b0 * N.h2 * N.s + ((-1 : ℝ)) * N.a0 * N.h2 * N.t)) = N.D ^ 2 * (((-1 : ℝ)) * N.h0 * N.b2 * N.s + ((1 : ℝ)) * N.h0 * N.a2 * N.t + ((1 : ℝ)) * N.b0 * N.h2 * N.s + ((-1 : ℝ)) * N.a0 * N.h2 * N.t) := by ring
  rw [e]; exact mul_pos (D_sq_pos N) hP

theorem chi_0134_eq (N : NF29 x) :
    Split.det3 (x 1 - x 0) (x 3 - x 0) (x 4 - x 0) = N.D * (((1 : ℝ)) * N.b0) := by
  chi_eq_tac N

theorem chi_0134_sign (N : NF29 x) (hb0 : 0 < N.b0) :
    0 < N.D * Split.det3 (x 1 - x 0) (x 3 - x 0) (x 4 - x 0) := by
  rw [chi_0134_eq N]
  have hP : 0 < ((1 : ℝ)) * N.b0 := by
    nlinarith [mul_pos N.hh0 N.hs, mul_pos N.hh0 N.ht, mul_pos N.hh2 N.hs, mul_pos N.hh2 N.ht, mul_pos N.hs N.ht, mul_pos_of_neg_of_neg N.ha0 N.hb2, mul_pos hb0 N.hs, mul_pos hb0 N.ht, N.hh0, N.hh2, N.ha0, N.hb2, N.t345_0, N.t345_2, N.hF4, N.hF5, N.hDD, N.hDG4, N.hDG5, N.hE35, N.hE24, N.hs, N.ht, N.hst, N.d023, N.d035, N.d234]
  have e : N.D * (N.D * (((1 : ℝ)) * N.b0)) = N.D ^ 2 * (((1 : ℝ)) * N.b0) := by ring
  rw [e]; exact mul_pos (D_sq_pos N) hP

theorem chi_0135_eq (N : NF29 x) :
    Split.det3 (x 1 - x 0) (x 3 - x 0) (x 5 - x 0) = N.D * (((-1 : ℝ)) * N.a0) := by
  chi_eq_tac N

theorem chi_0135_sign (N : NF29 x)  :
    0 < N.D * Split.det3 (x 1 - x 0) (x 3 - x 0) (x 5 - x 0) := by
  rw [chi_0135_eq N]
  have hP : 0 < ((-1 : ℝ)) * N.a0 := by
    nlinarith [mul_pos N.hh0 N.hs, mul_pos N.hh0 N.ht, mul_pos N.hh2 N.hs, mul_pos N.hh2 N.ht, mul_pos N.hs N.ht, mul_pos_of_neg_of_neg N.ha0 N.hb2, N.hh0, N.hh2, N.ha0, N.hb2, N.t345_0, N.t345_2, N.hF4, N.hF5, N.hDD, N.hDG4, N.hDG5, N.hE35, N.hE24, N.hs, N.ht, N.hst, N.d023, N.d035, N.d234]
  have e : N.D * (N.D * (((-1 : ℝ)) * N.a0)) = N.D ^ 2 * (((-1 : ℝ)) * N.a0) := by ring
  rw [e]; exact mul_pos (D_sq_pos N) hP

theorem chi_0136_eq (N : NF29 x) :
    Split.det3 (x 1 - x 0) (x 3 - x 0) (x 6 - x 0) = N.D * (((1 : ℝ)) * N.b0 * N.s + ((-1 : ℝ)) * N.a0 * N.t) := by
  chi_eq_tac N

theorem chi_0136_sign (N : NF29 x) (hb0 : 0 < N.b0) :
    0 < N.D * Split.det3 (x 1 - x 0) (x 3 - x 0) (x 6 - x 0) := by
  rw [chi_0136_eq N]
  have hP : 0 < ((1 : ℝ)) * N.b0 * N.s + ((-1 : ℝ)) * N.a0 * N.t := by
    nlinarith [mul_pos N.hh0 N.hs, mul_pos N.hh0 N.ht, mul_pos N.hh2 N.hs, mul_pos N.hh2 N.ht, mul_pos N.hs N.ht, mul_pos_of_neg_of_neg N.ha0 N.hb2, mul_pos hb0 N.hs, mul_pos hb0 N.ht, N.hh0, N.hh2, N.ha0, N.hb2, N.t345_0, N.t345_2, N.hF4, N.hF5, N.hDD, N.hDG4, N.hDG5, N.hE35, N.hE24, N.hs, N.ht, N.hst, N.d023, N.d035, N.d234]
  have e : N.D * (N.D * (((1 : ℝ)) * N.b0 * N.s + ((-1 : ℝ)) * N.a0 * N.t)) = N.D ^ 2 * (((1 : ℝ)) * N.b0 * N.s + ((-1 : ℝ)) * N.a0 * N.t) := by ring
  rw [e]; exact mul_pos (D_sq_pos N) hP

theorem chi_0145_eq (N : NF29 x) :
    Split.det3 (x 1 - x 0) (x 4 - x 0) (x 5 - x 0) = N.D * (((1 : ℝ)) * N.h0) := by
  chi_eq_tac N

theorem chi_0145_sign (N : NF29 x)  :
    0 < N.D * Split.det3 (x 1 - x 0) (x 4 - x 0) (x 5 - x 0) := by
  rw [chi_0145_eq N]
  have hP : 0 < ((1 : ℝ)) * N.h0 := by
    nlinarith [mul_pos N.hh0 N.hs, mul_pos N.hh0 N.ht, mul_pos N.hh2 N.hs, mul_pos N.hh2 N.ht, mul_pos N.hs N.ht, mul_pos_of_neg_of_neg N.ha0 N.hb2, N.hh0, N.hh2, N.ha0, N.hb2, N.t345_0, N.t345_2, N.hF4, N.hF5, N.hDD, N.hDG4, N.hDG5, N.hE35, N.hE24, N.hs, N.ht, N.hst, N.d023, N.d035, N.d234]
  have e : N.D * (N.D * (((1 : ℝ)) * N.h0)) = N.D ^ 2 * (((1 : ℝ)) * N.h0) := by ring
  rw [e]; exact mul_pos (D_sq_pos N) hP

theorem chi_0146_eq (N : NF29 x) :
    Split.det3 (x 1 - x 0) (x 4 - x 0) (x 6 - x 0) = N.D * (((1 : ℝ)) * N.h0 * N.t) := by
  chi_eq_tac N

theorem chi_0146_sign (N : NF29 x)  :
    0 < N.D * Split.det3 (x 1 - x 0) (x 4 - x 0) (x 6 - x 0) := by
  rw [chi_0146_eq N]
  have hP : 0 < ((1 : ℝ)) * N.h0 * N.t := by
    nlinarith [mul_pos N.hh0 N.hs, mul_pos N.hh0 N.ht, mul_pos N.hh2 N.hs, mul_pos N.hh2 N.ht, mul_pos N.hs N.ht, mul_pos_of_neg_of_neg N.ha0 N.hb2, N.hh0, N.hh2, N.ha0, N.hb2, N.t345_0, N.t345_2, N.hF4, N.hF5, N.hDD, N.hDG4, N.hDG5, N.hE35, N.hE24, N.hs, N.ht, N.hst, N.d023, N.d035, N.d234]
  have e : N.D * (N.D * (((1 : ℝ)) * N.h0 * N.t)) = N.D ^ 2 * (((1 : ℝ)) * N.h0 * N.t) := by ring
  rw [e]; exact mul_pos (D_sq_pos N) hP

theorem chi_0156_eq (N : NF29 x) :
    Split.det3 (x 1 - x 0) (x 5 - x 0) (x 6 - x 0) = N.D * (((-1 : ℝ)) * N.h0 * N.s) := by
  chi_eq_tac N

theorem chi_0156_sign (N : NF29 x)  :
    N.D * Split.det3 (x 1 - x 0) (x 5 - x 0) (x 6 - x 0) < 0 := by
  rw [chi_0156_eq N]
  have hP : ((-1 : ℝ)) * N.h0 * N.s < 0 := by
    nlinarith [mul_pos N.hh0 N.hs, mul_pos N.hh0 N.ht, mul_pos N.hh2 N.hs, mul_pos N.hh2 N.ht, mul_pos N.hs N.ht, mul_pos_of_neg_of_neg N.ha0 N.hb2, N.hh0, N.hh2, N.ha0, N.hb2, N.t345_0, N.t345_2, N.hF4, N.hF5, N.hDD, N.hDG4, N.hDG5, N.hE35, N.hE24, N.hs, N.ht, N.hst, N.d023, N.d035, N.d234]
  have e : N.D * (N.D * (((-1 : ℝ)) * N.h0 * N.s)) = N.D ^ 2 * (((-1 : ℝ)) * N.h0 * N.s) := by ring
  rw [e]; exact mul_neg_of_pos_of_neg (D_sq_pos N) hP

theorem chi_0234_eq (N : NF29 x) :
    Split.det3 (x 2 - x 0) (x 3 - x 0) (x 4 - x 0) = N.D * (((-1 : ℝ)) * N.b2 + ((1 : ℝ)) * N.h0 * N.b2 + ((1 : ℝ)) * N.b0 + ((-1 : ℝ)) * N.b0 * N.h2 + ((-1 : ℝ)) * N.b0 * N.a2 + ((1 : ℝ)) * N.a0 * N.b2) := by
  chi_eq_tac N

theorem chi_0234_sign (N : NF29 x)  :
    0 < N.D * Split.det3 (x 2 - x 0) (x 3 - x 0) (x 4 - x 0) := by
  rw [chi_0234_eq N]
  have hP : 0 < ((-1 : ℝ)) * N.b2 + ((1 : ℝ)) * N.h0 * N.b2 + ((1 : ℝ)) * N.b0 + ((-1 : ℝ)) * N.b0 * N.h2 + ((-1 : ℝ)) * N.b0 * N.a2 + ((1 : ℝ)) * N.a0 * N.b2 := by
    nlinarith [mul_pos N.hh0 N.hs, mul_pos N.hh0 N.ht, mul_pos N.hh2 N.hs, mul_pos N.hh2 N.ht, mul_pos N.hs N.ht, mul_pos_of_neg_of_neg N.ha0 N.hb2, N.hh0, N.hh2, N.ha0, N.hb2, N.t345_0, N.t345_2, N.hF4, N.hF5, N.hDD, N.hDG4, N.hDG5, N.hE35, N.hE24, N.hs, N.ht, N.hst, N.d023, N.d035, N.d234]
  have e : N.D * (N.D * (((-1 : ℝ)) * N.b2 + ((1 : ℝ)) * N.h0 * N.b2 + ((1 : ℝ)) * N.b0 + ((-1 : ℝ)) * N.b0 * N.h2 + ((-1 : ℝ)) * N.b0 * N.a2 + ((1 : ℝ)) * N.a0 * N.b2)) = N.D ^ 2 * (((-1 : ℝ)) * N.b2 + ((1 : ℝ)) * N.h0 * N.b2 + ((1 : ℝ)) * N.b0 + ((-1 : ℝ)) * N.b0 * N.h2 + ((-1 : ℝ)) * N.b0 * N.a2 + ((1 : ℝ)) * N.a0 * N.b2) := by ring
  rw [e]; exact mul_pos (D_sq_pos N) hP

theorem chi_0235_eq (N : NF29 x) :
    Split.det3 (x 2 - x 0) (x 3 - x 0) (x 5 - x 0) = N.D * (((1 : ℝ)) * N.a2 + ((-1 : ℝ)) * N.h0 * N.a2 + ((-1 : ℝ)) * N.b0 * N.a2 + ((-1 : ℝ)) * N.a0 + ((1 : ℝ)) * N.a0 * N.h2 + ((1 : ℝ)) * N.a0 * N.b2) := by
  chi_eq_tac N

theorem chi_0235_sign (N : NF29 x)  :
    0 < N.D * Split.det3 (x 2 - x 0) (x 3 - x 0) (x 5 - x 0) := by
  rw [chi_0235_eq N]
  have hP : 0 < ((1 : ℝ)) * N.a2 + ((-1 : ℝ)) * N.h0 * N.a2 + ((-1 : ℝ)) * N.b0 * N.a2 + ((-1 : ℝ)) * N.a0 + ((1 : ℝ)) * N.a0 * N.h2 + ((1 : ℝ)) * N.a0 * N.b2 := by
    nlinarith [mul_pos N.hh0 N.hs, mul_pos N.hh0 N.ht, mul_pos N.hh2 N.hs, mul_pos N.hh2 N.ht, mul_pos N.hs N.ht, mul_pos_of_neg_of_neg N.ha0 N.hb2, N.hh0, N.hh2, N.ha0, N.hb2, N.t345_0, N.t345_2, N.hF4, N.hF5, N.hDD, N.hDG4, N.hDG5, N.hE35, N.hE24, N.hs, N.ht, N.hst, N.d023, N.d035, N.d234]
  have e : N.D * (N.D * (((1 : ℝ)) * N.a2 + ((-1 : ℝ)) * N.h0 * N.a2 + ((-1 : ℝ)) * N.b0 * N.a2 + ((-1 : ℝ)) * N.a0 + ((1 : ℝ)) * N.a0 * N.h2 + ((1 : ℝ)) * N.a0 * N.b2)) = N.D ^ 2 * (((1 : ℝ)) * N.a2 + ((-1 : ℝ)) * N.h0 * N.a2 + ((-1 : ℝ)) * N.b0 * N.a2 + ((-1 : ℝ)) * N.a0 + ((1 : ℝ)) * N.a0 * N.h2 + ((1 : ℝ)) * N.a0 * N.b2) := by ring
  rw [e]; exact mul_pos (D_sq_pos N) hP

theorem chi_0236_eq (N : NF29 x) :
    Split.det3 (x 2 - x 0) (x 3 - x 0) (x 6 - x 0) = N.D * (((-1 : ℝ)) * N.b2 * N.s + ((1 : ℝ)) * N.a2 * N.t + ((1 : ℝ)) * N.h0 * N.b2 * N.s + ((-1 : ℝ)) * N.h0 * N.a2 * N.t + ((1 : ℝ)) * N.b0 * N.s + ((-1 : ℝ)) * N.b0 * N.h2 * N.s + ((-1 : ℝ)) * N.b0 * N.a2 + ((-1 : ℝ)) * N.a0 * N.t + ((1 : ℝ)) * N.a0 * N.h2 * N.t + ((1 : ℝ)) * N.a0 * N.b2) := by
  chi_eq_tac N

theorem chi_0236_sign (N : NF29 x)  :
    0 < N.D * Split.det3 (x 2 - x 0) (x 3 - x 0) (x 6 - x 0) := by
  rw [chi_0236_eq N]
  have hP : 0 < ((-1 : ℝ)) * N.b2 * N.s + ((1 : ℝ)) * N.a2 * N.t + ((1 : ℝ)) * N.h0 * N.b2 * N.s + ((-1 : ℝ)) * N.h0 * N.a2 * N.t + ((1 : ℝ)) * N.b0 * N.s + ((-1 : ℝ)) * N.b0 * N.h2 * N.s + ((-1 : ℝ)) * N.b0 * N.a2 + ((-1 : ℝ)) * N.a0 * N.t + ((1 : ℝ)) * N.a0 * N.h2 * N.t + ((1 : ℝ)) * N.a0 * N.b2 := by
    nlinarith [mul_pos N.hh0 N.hs, mul_pos N.hh0 N.ht, mul_pos N.hh2 N.hs, mul_pos N.hh2 N.ht, mul_pos N.hs N.ht, mul_pos_of_neg_of_neg N.ha0 N.hb2, N.hh0, N.hh2, N.ha0, N.hb2, N.t345_0, N.t345_2, N.hF4, N.hF5, N.hDD, N.hDG4, N.hDG5, N.hE35, N.hE24, N.hs, N.ht, N.hst, N.d023, N.d035, N.d234]
  have e : N.D * (N.D * (((-1 : ℝ)) * N.b2 * N.s + ((1 : ℝ)) * N.a2 * N.t + ((1 : ℝ)) * N.h0 * N.b2 * N.s + ((-1 : ℝ)) * N.h0 * N.a2 * N.t + ((1 : ℝ)) * N.b0 * N.s + ((-1 : ℝ)) * N.b0 * N.h2 * N.s + ((-1 : ℝ)) * N.b0 * N.a2 + ((-1 : ℝ)) * N.a0 * N.t + ((1 : ℝ)) * N.a0 * N.h2 * N.t + ((1 : ℝ)) * N.a0 * N.b2)) = N.D ^ 2 * (((-1 : ℝ)) * N.b2 * N.s + ((1 : ℝ)) * N.a2 * N.t + ((1 : ℝ)) * N.h0 * N.b2 * N.s + ((-1 : ℝ)) * N.h0 * N.a2 * N.t + ((1 : ℝ)) * N.b0 * N.s + ((-1 : ℝ)) * N.b0 * N.h2 * N.s + ((-1 : ℝ)) * N.b0 * N.a2 + ((-1 : ℝ)) * N.a0 * N.t + ((1 : ℝ)) * N.a0 * N.h2 * N.t + ((1 : ℝ)) * N.a0 * N.b2) := by ring
  rw [e]; exact mul_pos (D_sq_pos N) hP

theorem chi_0245_eq (N : NF29 x) :
    Split.det3 (x 2 - x 0) (x 4 - x 0) (x 5 - x 0) = N.D * (((-1 : ℝ)) * N.h2 + ((1 : ℝ)) * N.h0 + ((-1 : ℝ)) * N.h0 * N.b2 + ((-1 : ℝ)) * N.h0 * N.a2 + ((1 : ℝ)) * N.b0 * N.h2 + ((1 : ℝ)) * N.a0 * N.h2) := by
  chi_eq_tac N

theorem chi_0245_sign (N : NF29 x) (hq : N.h0 * N.del2 < N.h2 * N.del0) :
    N.D * Split.det3 (x 2 - x 0) (x 4 - x 0) (x 5 - x 0) < 0 := by
  rw [chi_0245_eq N]
  have hP : ((-1 : ℝ)) * N.h2 + ((1 : ℝ)) * N.h0 + ((-1 : ℝ)) * N.h0 * N.b2 + ((-1 : ℝ)) * N.h0 * N.a2 + ((1 : ℝ)) * N.b0 * N.h2 + ((1 : ℝ)) * N.a0 * N.h2 < 0 := by
    have hq' := hq
    unfold del0 del2 at hq'
    linarith
  have e : N.D * (N.D * (((-1 : ℝ)) * N.h2 + ((1 : ℝ)) * N.h0 + ((-1 : ℝ)) * N.h0 * N.b2 + ((-1 : ℝ)) * N.h0 * N.a2 + ((1 : ℝ)) * N.b0 * N.h2 + ((1 : ℝ)) * N.a0 * N.h2)) = N.D ^ 2 * (((-1 : ℝ)) * N.h2 + ((1 : ℝ)) * N.h0 + ((-1 : ℝ)) * N.h0 * N.b2 + ((-1 : ℝ)) * N.h0 * N.a2 + ((1 : ℝ)) * N.b0 * N.h2 + ((1 : ℝ)) * N.a0 * N.h2) := by ring
  rw [e]; exact mul_neg_of_pos_of_neg (D_sq_pos N) hP

theorem chi_0246_eq (N : NF29 x) :
    Split.det3 (x 2 - x 0) (x 4 - x 0) (x 6 - x 0) = N.D * (((-1 : ℝ)) * N.h2 * N.t + ((1 : ℝ)) * N.h0 * N.t + ((-1 : ℝ)) * N.h0 * N.b2 + ((1 : ℝ)) * N.h0 * N.b2 * N.s + ((-1 : ℝ)) * N.h0 * N.a2 * N.t + ((1 : ℝ)) * N.b0 * N.h2 + ((-1 : ℝ)) * N.b0 * N.h2 * N.s + ((1 : ℝ)) * N.a0 * N.h2 * N.t) := by
  chi_eq_tac N

theorem chi_0246_sign (N : NF29 x) (hq : N.h0 * N.del2 < N.h2 * N.del0) :
    N.D * Split.det3 (x 2 - x 0) (x 4 - x 0) (x 6 - x 0) < 0 := by
  rw [chi_0246_eq N]
  have hP : ((-1 : ℝ)) * N.h2 * N.t + ((1 : ℝ)) * N.h0 * N.t + ((-1 : ℝ)) * N.h0 * N.b2 + ((1 : ℝ)) * N.h0 * N.b2 * N.s + ((-1 : ℝ)) * N.h0 * N.a2 * N.t + ((1 : ℝ)) * N.b0 * N.h2 + ((-1 : ℝ)) * N.b0 * N.h2 * N.s + ((1 : ℝ)) * N.a0 * N.h2 * N.t < 0 := by
    have hq' := hq
    unfold del0 del2 at hq'
    nlinarith [mul_pos N.ht (sub_pos.2 hq'), mul_pos (sub_pos.2 N.hst) N.hF4]
  have e : N.D * (N.D * (((-1 : ℝ)) * N.h2 * N.t + ((1 : ℝ)) * N.h0 * N.t + ((-1 : ℝ)) * N.h0 * N.b2 + ((1 : ℝ)) * N.h0 * N.b2 * N.s + ((-1 : ℝ)) * N.h0 * N.a2 * N.t + ((1 : ℝ)) * N.b0 * N.h2 + ((-1 : ℝ)) * N.b0 * N.h2 * N.s + ((1 : ℝ)) * N.a0 * N.h2 * N.t)) = N.D ^ 2 * (((-1 : ℝ)) * N.h2 * N.t + ((1 : ℝ)) * N.h0 * N.t + ((-1 : ℝ)) * N.h0 * N.b2 + ((1 : ℝ)) * N.h0 * N.b2 * N.s + ((-1 : ℝ)) * N.h0 * N.a2 * N.t + ((1 : ℝ)) * N.b0 * N.h2 + ((-1 : ℝ)) * N.b0 * N.h2 * N.s + ((1 : ℝ)) * N.a0 * N.h2 * N.t) := by ring
  rw [e]; exact mul_neg_of_pos_of_neg (D_sq_pos N) hP

theorem chi_0345_eq (N : NF29 x) :
    Split.det3 (x 3 - x 0) (x 4 - x 0) (x 5 - x 0) = N.D * (((-1 : ℝ)) + ((1 : ℝ)) * N.h0 + ((1 : ℝ)) * N.b0 + ((1 : ℝ)) * N.a0) := by
  chi_eq_tac N

theorem chi_0345_sign (N : NF29 x)  :
    N.D * Split.det3 (x 3 - x 0) (x 4 - x 0) (x 5 - x 0) < 0 := by
  rw [chi_0345_eq N]
  have hP : ((-1 : ℝ)) + ((1 : ℝ)) * N.h0 + ((1 : ℝ)) * N.b0 + ((1 : ℝ)) * N.a0 < 0 := by
    nlinarith [mul_pos N.hh0 N.hs, mul_pos N.hh0 N.ht, mul_pos N.hh2 N.hs, mul_pos N.hh2 N.ht, mul_pos N.hs N.ht, mul_pos_of_neg_of_neg N.ha0 N.hb2, N.hh0, N.hh2, N.ha0, N.hb2, N.t345_0, N.t345_2, N.hF4, N.hF5, N.hDD, N.hDG4, N.hDG5, N.hE35, N.hE24, N.hs, N.ht, N.hst, N.d023, N.d035, N.d234]
  have e : N.D * (N.D * (((-1 : ℝ)) + ((1 : ℝ)) * N.h0 + ((1 : ℝ)) * N.b0 + ((1 : ℝ)) * N.a0)) = N.D ^ 2 * (((-1 : ℝ)) + ((1 : ℝ)) * N.h0 + ((1 : ℝ)) * N.b0 + ((1 : ℝ)) * N.a0) := by ring
  rw [e]; exact mul_neg_of_pos_of_neg (D_sq_pos N) hP

theorem chi_0346_eq (N : NF29 x) :
    Split.det3 (x 3 - x 0) (x 4 - x 0) (x 6 - x 0) = N.D * (((-1 : ℝ)) * N.t + ((1 : ℝ)) * N.h0 * N.t + ((1 : ℝ)) * N.b0 + ((-1 : ℝ)) * N.b0 * N.s + ((1 : ℝ)) * N.a0 * N.t) := by
  chi_eq_tac N

theorem chi_0346_sign (N : NF29 x)  :
    N.D * Split.det3 (x 3 - x 0) (x 4 - x 0) (x 6 - x 0) < 0 := by
  rw [chi_0346_eq N]
  have hP : ((-1 : ℝ)) * N.t + ((1 : ℝ)) * N.h0 * N.t + ((1 : ℝ)) * N.b0 + ((-1 : ℝ)) * N.b0 * N.s + ((1 : ℝ)) * N.a0 * N.t < 0 := by
    nlinarith [mul_pos N.hh0 N.hs, mul_pos N.hh0 N.ht, mul_pos N.hh2 N.hs, mul_pos N.hh2 N.ht, mul_pos N.hs N.ht, mul_pos_of_neg_of_neg N.ha0 N.hb2, N.hh0, N.hh2, N.ha0, N.hb2, N.t345_0, N.t345_2, N.hF4, N.hF5, N.hDD, N.hDG4, N.hDG5, N.hE35, N.hE24, N.hs, N.ht, N.hst, N.d023, N.d035, N.d234]
  have e : N.D * (N.D * (((-1 : ℝ)) * N.t + ((1 : ℝ)) * N.h0 * N.t + ((1 : ℝ)) * N.b0 + ((-1 : ℝ)) * N.b0 * N.s + ((1 : ℝ)) * N.a0 * N.t)) = N.D ^ 2 * (((-1 : ℝ)) * N.t + ((1 : ℝ)) * N.h0 * N.t + ((1 : ℝ)) * N.b0 + ((-1 : ℝ)) * N.b0 * N.s + ((1 : ℝ)) * N.a0 * N.t) := by ring
  rw [e]; exact mul_neg_of_pos_of_neg (D_sq_pos N) hP

theorem chi_0356_eq (N : NF29 x) :
    Split.det3 (x 3 - x 0) (x 5 - x 0) (x 6 - x 0) = N.D * (((1 : ℝ)) * N.s + ((-1 : ℝ)) * N.h0 * N.s + ((-1 : ℝ)) * N.b0 * N.s + ((-1 : ℝ)) * N.a0 + ((1 : ℝ)) * N.a0 * N.t) := by
  chi_eq_tac N

theorem chi_0356_sign (N : NF29 x)  :
    0 < N.D * Split.det3 (x 3 - x 0) (x 5 - x 0) (x 6 - x 0) := by
  rw [chi_0356_eq N]
  have hP : 0 < ((1 : ℝ)) * N.s + ((-1 : ℝ)) * N.h0 * N.s + ((-1 : ℝ)) * N.b0 * N.s + ((-1 : ℝ)) * N.a0 + ((1 : ℝ)) * N.a0 * N.t := by
    nlinarith [mul_pos N.hh0 N.hs, mul_pos N.hh0 N.ht, mul_pos N.hh2 N.hs, mul_pos N.hh2 N.ht, mul_pos N.hs N.ht, mul_pos_of_neg_of_neg N.ha0 N.hb2, N.hh0, N.hh2, N.ha0, N.hb2, N.t345_0, N.t345_2, N.hF4, N.hF5, N.hDD, N.hDG4, N.hDG5, N.hE35, N.hE24, N.hs, N.ht, N.hst, N.d023, N.d035, N.d234]
  have e : N.D * (N.D * (((1 : ℝ)) * N.s + ((-1 : ℝ)) * N.h0 * N.s + ((-1 : ℝ)) * N.b0 * N.s + ((-1 : ℝ)) * N.a0 + ((1 : ℝ)) * N.a0 * N.t)) = N.D ^ 2 * (((1 : ℝ)) * N.s + ((-1 : ℝ)) * N.h0 * N.s + ((-1 : ℝ)) * N.b0 * N.s + ((-1 : ℝ)) * N.a0 + ((1 : ℝ)) * N.a0 * N.t) := by ring
  rw [e]; exact mul_pos (D_sq_pos N) hP

theorem chi_0456_eq (N : NF29 x) :
    Split.det3 (x 4 - x 0) (x 5 - x 0) (x 6 - x 0) = N.D * (((1 : ℝ)) * N.h0 + ((-1 : ℝ)) * N.h0 * N.t + ((-1 : ℝ)) * N.h0 * N.s) := by
  chi_eq_tac N

theorem chi_0456_sign (N : NF29 x)  :
    N.D * Split.det3 (x 4 - x 0) (x 5 - x 0) (x 6 - x 0) < 0 := by
  rw [chi_0456_eq N]
  have hP : ((1 : ℝ)) * N.h0 + ((-1 : ℝ)) * N.h0 * N.t + ((-1 : ℝ)) * N.h0 * N.s < 0 := by
    nlinarith [mul_pos N.hh0 N.hs, mul_pos N.hh0 N.ht, mul_pos N.hh2 N.hs, mul_pos N.hh2 N.ht, mul_pos N.hs N.ht, mul_pos_of_neg_of_neg N.ha0 N.hb2, N.hh0, N.hh2, N.ha0, N.hb2, N.t345_0, N.t345_2, N.hF4, N.hF5, N.hDD, N.hDG4, N.hDG5, N.hE35, N.hE24, N.hs, N.ht, N.hst, N.d023, N.d035, N.d234]
  have e : N.D * (N.D * (((1 : ℝ)) * N.h0 + ((-1 : ℝ)) * N.h0 * N.t + ((-1 : ℝ)) * N.h0 * N.s)) = N.D ^ 2 * (((1 : ℝ)) * N.h0 + ((-1 : ℝ)) * N.h0 * N.t + ((-1 : ℝ)) * N.h0 * N.s) := by ring
  rw [e]; exact mul_neg_of_pos_of_neg (D_sq_pos N) hP

theorem chi_1234_eq (N : NF29 x) :
    Split.det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) = N.D * (((-1 : ℝ)) * N.b2) := by
  chi_eq_tac N

theorem chi_1234_sign (N : NF29 x)  :
    0 < N.D * Split.det3 (x 2 - x 1) (x 3 - x 1) (x 4 - x 1) := by
  rw [chi_1234_eq N]
  have hP : 0 < ((-1 : ℝ)) * N.b2 := by
    nlinarith [mul_pos N.hh0 N.hs, mul_pos N.hh0 N.ht, mul_pos N.hh2 N.hs, mul_pos N.hh2 N.ht, mul_pos N.hs N.ht, mul_pos_of_neg_of_neg N.ha0 N.hb2, N.hh0, N.hh2, N.ha0, N.hb2, N.t345_0, N.t345_2, N.hF4, N.hF5, N.hDD, N.hDG4, N.hDG5, N.hE35, N.hE24, N.hs, N.ht, N.hst, N.d023, N.d035, N.d234]
  have e : N.D * (N.D * (((-1 : ℝ)) * N.b2)) = N.D ^ 2 * (((-1 : ℝ)) * N.b2) := by ring
  rw [e]; exact mul_pos (D_sq_pos N) hP

theorem chi_1235_eq (N : NF29 x) :
    Split.det3 (x 2 - x 1) (x 3 - x 1) (x 5 - x 1) = N.D * (((1 : ℝ)) * N.a2) := by
  chi_eq_tac N

theorem chi_1235_sign (N : NF29 x) (ha2 : N.a2 < 0) :
    N.D * Split.det3 (x 2 - x 1) (x 3 - x 1) (x 5 - x 1) < 0 := by
  rw [chi_1235_eq N]
  have hP : ((1 : ℝ)) * N.a2 < 0 := by
    nlinarith [mul_pos N.hh0 N.hs, mul_pos N.hh0 N.ht, mul_pos N.hh2 N.hs, mul_pos N.hh2 N.ht, mul_pos N.hs N.ht, mul_pos_of_neg_of_neg N.ha0 N.hb2, N.hh0, N.hh2, N.ha0, N.hb2, N.t345_0, N.t345_2, N.hF4, N.hF5, N.hDD, N.hDG4, N.hDG5, N.hE35, N.hE24, N.hs, N.ht, N.hst, N.d023, N.d035, N.d234]
  have e : N.D * (N.D * (((1 : ℝ)) * N.a2)) = N.D ^ 2 * (((1 : ℝ)) * N.a2) := by ring
  rw [e]; exact mul_neg_of_pos_of_neg (D_sq_pos N) hP

theorem chi_1245_eq (N : NF29 x) :
    Split.det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1) = N.D * (((-1 : ℝ)) * N.h2) := by
  chi_eq_tac N

theorem chi_1245_sign (N : NF29 x)  :
    N.D * Split.det3 (x 2 - x 1) (x 4 - x 1) (x 5 - x 1) < 0 := by
  rw [chi_1245_eq N]
  have hP : ((-1 : ℝ)) * N.h2 < 0 := by
    nlinarith [mul_pos N.hh0 N.hs, mul_pos N.hh0 N.ht, mul_pos N.hh2 N.hs, mul_pos N.hh2 N.ht, mul_pos N.hs N.ht, mul_pos_of_neg_of_neg N.ha0 N.hb2, N.hh0, N.hh2, N.ha0, N.hb2, N.t345_0, N.t345_2, N.hF4, N.hF5, N.hDD, N.hDG4, N.hDG5, N.hE35, N.hE24, N.hs, N.ht, N.hst, N.d023, N.d035, N.d234]
  have e : N.D * (N.D * (((-1 : ℝ)) * N.h2)) = N.D ^ 2 * (((-1 : ℝ)) * N.h2) := by ring
  rw [e]; exact mul_neg_of_pos_of_neg (D_sq_pos N) hP

theorem chi_1246_eq (N : NF29 x) :
    Split.det3 (x 2 - x 1) (x 4 - x 1) (x 6 - x 1) = N.D * (((-1 : ℝ)) * N.h2 * N.t) := by
  chi_eq_tac N

theorem chi_1246_sign (N : NF29 x)  :
    N.D * Split.det3 (x 2 - x 1) (x 4 - x 1) (x 6 - x 1) < 0 := by
  rw [chi_1246_eq N]
  have hP : ((-1 : ℝ)) * N.h2 * N.t < 0 := by
    nlinarith [mul_pos N.hh0 N.hs, mul_pos N.hh0 N.ht, mul_pos N.hh2 N.hs, mul_pos N.hh2 N.ht, mul_pos N.hs N.ht, mul_pos_of_neg_of_neg N.ha0 N.hb2, N.hh0, N.hh2, N.ha0, N.hb2, N.t345_0, N.t345_2, N.hF4, N.hF5, N.hDD, N.hDG4, N.hDG5, N.hE35, N.hE24, N.hs, N.ht, N.hst, N.d023, N.d035, N.d234]
  have e : N.D * (N.D * (((-1 : ℝ)) * N.h2 * N.t)) = N.D ^ 2 * (((-1 : ℝ)) * N.h2 * N.t) := by ring
  rw [e]; exact mul_neg_of_pos_of_neg (D_sq_pos N) hP

theorem chi_1256_eq (N : NF29 x) :
    Split.det3 (x 2 - x 1) (x 5 - x 1) (x 6 - x 1) = N.D * (((1 : ℝ)) * N.h2 * N.s) := by
  chi_eq_tac N

theorem chi_1256_sign (N : NF29 x)  :
    0 < N.D * Split.det3 (x 2 - x 1) (x 5 - x 1) (x 6 - x 1) := by
  rw [chi_1256_eq N]
  have hP : 0 < ((1 : ℝ)) * N.h2 * N.s := by
    nlinarith [mul_pos N.hh0 N.hs, mul_pos N.hh0 N.ht, mul_pos N.hh2 N.hs, mul_pos N.hh2 N.ht, mul_pos N.hs N.ht, mul_pos_of_neg_of_neg N.ha0 N.hb2, N.hh0, N.hh2, N.ha0, N.hb2, N.t345_0, N.t345_2, N.hF4, N.hF5, N.hDD, N.hDG4, N.hDG5, N.hE35, N.hE24, N.hs, N.ht, N.hst, N.d023, N.d035, N.d234]
  have e : N.D * (N.D * (((1 : ℝ)) * N.h2 * N.s)) = N.D ^ 2 * (((1 : ℝ)) * N.h2 * N.s) := by ring
  rw [e]; exact mul_pos (D_sq_pos N) hP

theorem chi_1345_eq (N : NF29 x) :
    Split.det3 (x 3 - x 1) (x 4 - x 1) (x 5 - x 1) = N.D * (((-1 : ℝ))) := by
  chi_eq_tac N

theorem chi_1345_sign (N : NF29 x)  :
    N.D * Split.det3 (x 3 - x 1) (x 4 - x 1) (x 5 - x 1) < 0 := by
  rw [chi_1345_eq N]
  have hP : ((-1 : ℝ)) < 0 := by
    nlinarith [mul_pos N.hh0 N.hs, mul_pos N.hh0 N.ht, mul_pos N.hh2 N.hs, mul_pos N.hh2 N.ht, mul_pos N.hs N.ht, mul_pos_of_neg_of_neg N.ha0 N.hb2, N.hh0, N.hh2, N.ha0, N.hb2, N.t345_0, N.t345_2, N.hF4, N.hF5, N.hDD, N.hDG4, N.hDG5, N.hE35, N.hE24, N.hs, N.ht, N.hst, N.d023, N.d035, N.d234]
  have e : N.D * (N.D * (((-1 : ℝ)))) = N.D ^ 2 * (((-1 : ℝ))) := by ring
  rw [e]; exact mul_neg_of_pos_of_neg (D_sq_pos N) hP

theorem chi_1346_eq (N : NF29 x) :
    Split.det3 (x 3 - x 1) (x 4 - x 1) (x 6 - x 1) = N.D * (((-1 : ℝ)) * N.t) := by
  chi_eq_tac N

theorem chi_1346_sign (N : NF29 x)  :
    N.D * Split.det3 (x 3 - x 1) (x 4 - x 1) (x 6 - x 1) < 0 := by
  rw [chi_1346_eq N]
  have hP : ((-1 : ℝ)) * N.t < 0 := by
    nlinarith [mul_pos N.hh0 N.hs, mul_pos N.hh0 N.ht, mul_pos N.hh2 N.hs, mul_pos N.hh2 N.ht, mul_pos N.hs N.ht, mul_pos_of_neg_of_neg N.ha0 N.hb2, N.hh0, N.hh2, N.ha0, N.hb2, N.t345_0, N.t345_2, N.hF4, N.hF5, N.hDD, N.hDG4, N.hDG5, N.hE35, N.hE24, N.hs, N.ht, N.hst, N.d023, N.d035, N.d234]
  have e : N.D * (N.D * (((-1 : ℝ)) * N.t)) = N.D ^ 2 * (((-1 : ℝ)) * N.t) := by ring
  rw [e]; exact mul_neg_of_pos_of_neg (D_sq_pos N) hP

theorem chi_1356_eq (N : NF29 x) :
    Split.det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) = N.D * (((1 : ℝ)) * N.s) := by
  chi_eq_tac N

theorem chi_1356_sign (N : NF29 x)  :
    0 < N.D * Split.det3 (x 3 - x 1) (x 5 - x 1) (x 6 - x 1) := by
  rw [chi_1356_eq N]
  have hP : 0 < ((1 : ℝ)) * N.s := by
    nlinarith [mul_pos N.hh0 N.hs, mul_pos N.hh0 N.ht, mul_pos N.hh2 N.hs, mul_pos N.hh2 N.ht, mul_pos N.hs N.ht, mul_pos_of_neg_of_neg N.ha0 N.hb2, N.hh0, N.hh2, N.ha0, N.hb2, N.t345_0, N.t345_2, N.hF4, N.hF5, N.hDD, N.hDG4, N.hDG5, N.hE35, N.hE24, N.hs, N.ht, N.hst, N.d023, N.d035, N.d234]
  have e : N.D * (N.D * (((1 : ℝ)) * N.s)) = N.D ^ 2 * (((1 : ℝ)) * N.s) := by ring
  rw [e]; exact mul_pos (D_sq_pos N) hP

theorem chi_2345_eq (N : NF29 x) :
    Split.det3 (x 3 - x 2) (x 4 - x 2) (x 5 - x 2) = N.D * (((-1 : ℝ)) + ((1 : ℝ)) * N.h2 + ((1 : ℝ)) * N.b2 + ((1 : ℝ)) * N.a2) := by
  chi_eq_tac N

theorem chi_2345_sign (N : NF29 x)  :
    N.D * Split.det3 (x 3 - x 2) (x 4 - x 2) (x 5 - x 2) < 0 := by
  rw [chi_2345_eq N]
  have hP : ((-1 : ℝ)) + ((1 : ℝ)) * N.h2 + ((1 : ℝ)) * N.b2 + ((1 : ℝ)) * N.a2 < 0 := by
    nlinarith [mul_pos N.hh0 N.hs, mul_pos N.hh0 N.ht, mul_pos N.hh2 N.hs, mul_pos N.hh2 N.ht, mul_pos N.hs N.ht, mul_pos_of_neg_of_neg N.ha0 N.hb2, N.hh0, N.hh2, N.ha0, N.hb2, N.t345_0, N.t345_2, N.hF4, N.hF5, N.hDD, N.hDG4, N.hDG5, N.hE35, N.hE24, N.hs, N.ht, N.hst, N.d023, N.d035, N.d234]
  have e : N.D * (N.D * (((-1 : ℝ)) + ((1 : ℝ)) * N.h2 + ((1 : ℝ)) * N.b2 + ((1 : ℝ)) * N.a2)) = N.D ^ 2 * (((-1 : ℝ)) + ((1 : ℝ)) * N.h2 + ((1 : ℝ)) * N.b2 + ((1 : ℝ)) * N.a2) := by ring
  rw [e]; exact mul_neg_of_pos_of_neg (D_sq_pos N) hP

theorem chi_2346_eq (N : NF29 x) :
    Split.det3 (x 3 - x 2) (x 4 - x 2) (x 6 - x 2) = N.D * (((-1 : ℝ)) * N.t + ((1 : ℝ)) * N.h2 * N.t + ((1 : ℝ)) * N.b2 + ((-1 : ℝ)) * N.b2 * N.s + ((1 : ℝ)) * N.a2 * N.t) := by
  chi_eq_tac N

theorem chi_2346_sign (N : NF29 x)  :
    N.D * Split.det3 (x 3 - x 2) (x 4 - x 2) (x 6 - x 2) < 0 := by
  rw [chi_2346_eq N]
  have hP : ((-1 : ℝ)) * N.t + ((1 : ℝ)) * N.h2 * N.t + ((1 : ℝ)) * N.b2 + ((-1 : ℝ)) * N.b2 * N.s + ((1 : ℝ)) * N.a2 * N.t < 0 := by
    nlinarith [mul_pos N.hh0 N.hs, mul_pos N.hh0 N.ht, mul_pos N.hh2 N.hs, mul_pos N.hh2 N.ht, mul_pos N.hs N.ht, mul_pos_of_neg_of_neg N.ha0 N.hb2, N.hh0, N.hh2, N.ha0, N.hb2, N.t345_0, N.t345_2, N.hF4, N.hF5, N.hDD, N.hDG4, N.hDG5, N.hE35, N.hE24, N.hs, N.ht, N.hst, N.d023, N.d035, N.d234]
  have e : N.D * (N.D * (((-1 : ℝ)) * N.t + ((1 : ℝ)) * N.h2 * N.t + ((1 : ℝ)) * N.b2 + ((-1 : ℝ)) * N.b2 * N.s + ((1 : ℝ)) * N.a2 * N.t)) = N.D ^ 2 * (((-1 : ℝ)) * N.t + ((1 : ℝ)) * N.h2 * N.t + ((1 : ℝ)) * N.b2 + ((-1 : ℝ)) * N.b2 * N.s + ((1 : ℝ)) * N.a2 * N.t) := by ring
  rw [e]; exact mul_neg_of_pos_of_neg (D_sq_pos N) hP

theorem chi_2356_eq (N : NF29 x) :
    Split.det3 (x 3 - x 2) (x 5 - x 2) (x 6 - x 2) = N.D * (((1 : ℝ)) * N.s + ((-1 : ℝ)) * N.h2 * N.s + ((-1 : ℝ)) * N.b2 * N.s + ((-1 : ℝ)) * N.a2 + ((1 : ℝ)) * N.a2 * N.t) := by
  chi_eq_tac N

theorem chi_2356_sign (N : NF29 x)  :
    0 < N.D * Split.det3 (x 3 - x 2) (x 5 - x 2) (x 6 - x 2) := by
  rw [chi_2356_eq N]
  have hP : 0 < ((1 : ℝ)) * N.s + ((-1 : ℝ)) * N.h2 * N.s + ((-1 : ℝ)) * N.b2 * N.s + ((-1 : ℝ)) * N.a2 + ((1 : ℝ)) * N.a2 * N.t := by
    nlinarith [mul_pos N.hh0 N.hs, mul_pos N.hh0 N.ht, mul_pos N.hh2 N.hs, mul_pos N.hh2 N.ht, mul_pos N.hs N.ht, mul_pos_of_neg_of_neg N.ha0 N.hb2, N.hh0, N.hh2, N.ha0, N.hb2, N.t345_0, N.t345_2, N.hF4, N.hF5, N.hDD, N.hDG4, N.hDG5, N.hE35, N.hE24, N.hs, N.ht, N.hst, N.d023, N.d035, N.d234]
  have e : N.D * (N.D * (((1 : ℝ)) * N.s + ((-1 : ℝ)) * N.h2 * N.s + ((-1 : ℝ)) * N.b2 * N.s + ((-1 : ℝ)) * N.a2 + ((1 : ℝ)) * N.a2 * N.t)) = N.D ^ 2 * (((1 : ℝ)) * N.s + ((-1 : ℝ)) * N.h2 * N.s + ((-1 : ℝ)) * N.b2 * N.s + ((-1 : ℝ)) * N.a2 + ((1 : ℝ)) * N.a2 * N.t) := by ring
  rw [e]; exact mul_pos (D_sq_pos N) hP

theorem chi_2456_eq (N : NF29 x) :
    Split.det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2) = N.D * (((1 : ℝ)) * N.h2 + ((-1 : ℝ)) * N.h2 * N.t + ((-1 : ℝ)) * N.h2 * N.s) := by
  chi_eq_tac N

theorem chi_2456_sign (N : NF29 x)  :
    N.D * Split.det3 (x 4 - x 2) (x 5 - x 2) (x 6 - x 2) < 0 := by
  rw [chi_2456_eq N]
  have hP : ((1 : ℝ)) * N.h2 + ((-1 : ℝ)) * N.h2 * N.t + ((-1 : ℝ)) * N.h2 * N.s < 0 := by
    nlinarith [mul_pos N.hh0 N.hs, mul_pos N.hh0 N.ht, mul_pos N.hh2 N.hs, mul_pos N.hh2 N.ht, mul_pos N.hs N.ht, mul_pos_of_neg_of_neg N.ha0 N.hb2, N.hh0, N.hh2, N.ha0, N.hb2, N.t345_0, N.t345_2, N.hF4, N.hF5, N.hDD, N.hDG4, N.hDG5, N.hE35, N.hE24, N.hs, N.ht, N.hst, N.d023, N.d035, N.d234]
  have e : N.D * (N.D * (((1 : ℝ)) * N.h2 + ((-1 : ℝ)) * N.h2 * N.t + ((-1 : ℝ)) * N.h2 * N.s)) = N.D ^ 2 * (((1 : ℝ)) * N.h2 + ((-1 : ℝ)) * N.h2 * N.t + ((-1 : ℝ)) * N.h2 * N.s) := by ring
  rw [e]; exact mul_neg_of_pos_of_neg (D_sq_pos N) hP

theorem chi_3456_eq (N : NF29 x) :
    Split.det3 (x 4 - x 3) (x 5 - x 3) (x 6 - x 3) = N.D * (((1 : ℝ)) + ((-1 : ℝ)) * N.t + ((-1 : ℝ)) * N.s) := by
  chi_eq_tac N

theorem chi_3456_sign (N : NF29 x)  :
    N.D * Split.det3 (x 4 - x 3) (x 5 - x 3) (x 6 - x 3) < 0 := by
  rw [chi_3456_eq N]
  have hP : ((1 : ℝ)) + ((-1 : ℝ)) * N.t + ((-1 : ℝ)) * N.s < 0 := by
    nlinarith [mul_pos N.hh0 N.hs, mul_pos N.hh0 N.ht, mul_pos N.hh2 N.hs, mul_pos N.hh2 N.ht, mul_pos N.hs N.ht, mul_pos_of_neg_of_neg N.ha0 N.hb2, N.hh0, N.hh2, N.ha0, N.hb2, N.t345_0, N.t345_2, N.hF4, N.hF5, N.hDD, N.hDG4, N.hDG5, N.hE35, N.hE24, N.hs, N.ht, N.hst, N.d023, N.d035, N.d234]
  have e : N.D * (N.D * (((1 : ℝ)) + ((-1 : ℝ)) * N.t + ((-1 : ℝ)) * N.s)) = N.D ^ 2 * (((1 : ℝ)) + ((-1 : ℝ)) * N.t + ((-1 : ℝ)) * N.s) := by ring
  rw [e]; exact mul_neg_of_pos_of_neg (D_sq_pos N) hP

theorem chi_1456 (N : NF29 x) : Split.det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1) = 0 := by
  have : Split.det3 (x 4 - x 1) (x 5 - x 1) (x 6 - x 1) = N.D * 0 := by chi_eq_tac N
  rw [this, mul_zero]

/-- The only sign-varying entry among the rim quadruples `1235, 1236, 1256, 1356, 2356`:
`chi(1236) = D * (a2 t - b2 s)`. -/
theorem chi_1236_eq (N : NF29 x) :
    Split.det3 (x 2 - x 1) (x 3 - x 1) (x 6 - x 1) = N.D * (N.a2 * N.t - N.b2 * N.s) := by
  chi_eq_tac N

theorem chi_0256_eq (N : NF29 x) :
    Split.det3 (x 2 - x 0) (x 5 - x 0) (x 6 - x 0) = N.D * (((1 : ℝ)) * N.h2 * N.s + ((-1 : ℝ)) * N.h0 * N.s + ((1 : ℝ)) * N.h0 * N.b2 * N.s + ((1 : ℝ)) * N.h0 * N.a2 + ((-1 : ℝ)) * N.h0 * N.a2 * N.t + ((-1 : ℝ)) * N.b0 * N.h2 * N.s + ((-1 : ℝ)) * N.a0 * N.h2 + ((1 : ℝ)) * N.a0 * N.h2 * N.t) := by
  chi_eq_tac N

/-- The hand expansion of the `0256` polynomial. -/
theorem chi_0256_expand (N : NF29 x) :
    ((1 : ℝ)) * N.h2 * N.s + ((-1 : ℝ)) * N.h0 * N.s + ((1 : ℝ)) * N.h0 * N.b2 * N.s + ((1 : ℝ)) * N.h0 * N.a2 + ((-1 : ℝ)) * N.h0 * N.a2 * N.t + ((-1 : ℝ)) * N.b0 * N.h2 * N.s + ((-1 : ℝ)) * N.a0 * N.h2 + ((1 : ℝ)) * N.a0 * N.h2 * N.t =
      (N.a2 - N.a0) * N.h0 * (1 - N.t) + (N.b2 - N.b0) * N.h0 * N.s +
        (N.h0 - N.h2) * (N.a0 * (1 - N.t) - N.s * (1 - N.b0)) := by
  ring

end Minimality.NF29
