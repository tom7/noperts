module

public import Minimality.Type16Cover
public import Minimality.Type16Rims

@[expose] public section

/-!
# Type 16: the pairs and the triple on `Ω` (`FEWER-FACES-PROOFS.md` §19.3–19.5)

On the residual `Ω` of Theorem 19.2 no edge certificate of the named edges applies; each part of
`Ω` is certified by two or three tests whose failures force opposite signs of an inner product
of their views (Lemma V, in the form of the angle lemma 13.2: a failing quadrilateral rim has
its diagonals depth-separated, and the direction of the separation is fixed by the crossing of
the diagonals, `depthSep_of_meet`).

* **Lemma 19.3** (`isRupert_F3`): `Ω ∩ {d > 1}`: the closing `K_3` at `35` (rim `(3, x, 4, 1)`)
  and the vertex crossing `046/145` at `4` (view `vT2`, rim `(4, 5, 3, 6)`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Minimality

open scoped RealInnerProductSpace
open Finset

/-- **The direction of a depth separation** (the four-corner rule, §13.1): if the diagonals
`[d₀, d₁]`, `[e₀, e₁]` of a 4-corner rim cross along `w` with `e − d = l w`, `l ≤ 0`, and are
depth-separated at `w`, then `{d₀, d₁}` lies above `{e₀, e₁}`. -/
theorem depthSep_of_meet {d₀ d₁ e₀ e₁ w : ℝ³} {s t l : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hm : (e₀ + t • (e₁ - e₀)) - (d₀ + s • (d₁ - d₀)) = l • w)
    (hl : l ≤ 0) (h : DepthSep d₀ d₁ e₀ e₁ w) : max ⟪e₀, w⟫ ⟪e₁, w⟫ < min ⟪d₀, w⟫ ⟪d₁, w⟫ := by
  have i1 := congrArg (fun z => ⟪z, w⟫) hm
  simp only [inner_sub_left, inner_seg, real_inner_smul_left] at i1
  obtain ⟨e1, e2⟩ := seg_bounds (x := ⟪e₀, w⟫) (y := ⟪e₁, w⟫) ht0 ht1
  obtain ⟨d1, d2⟩ := seg_bounds (x := ⟪d₀, w⟫) (y := ⟪d₁, w⟫) hs0 hs1
  have hww := real_inner_self_nonneg (x := w)
  rcases h with h | h
  · exfalso; nlinarith [mul_nonpos_of_nonpos_of_nonneg hl hww]
  · exact h

namespace NF16

variable {x : Fin 7 → ℝ³}

/-! ### Lemma 19.3 -/

/-- `f15 = f046(1) − f046(5)`: `046` faces toward `5` at the view along `15` iff `f15 > 0`. -/
def f15 (N : NF16 x) : ℝ := (N.g - 1) * (N.p + N.r - 1) - N.d * N.q

/-- `[0146] = f046(1)`. -/
def t0146v (N : NF16 x) : ℝ := N.g * (N.p + N.r - 1) - N.q * (N.d - 1)

/-- **The view of `T2`** (§19.3 (ii)): `v = (−f15)(4 − 1) + f046(1)(5 − 1)`, parallel to the
planes of `046` and `145`. -/
noncomputable def vT2 (N : NF16 x) : ℝ³ :=
  nfV N.E₁ N.E₂ N.E₃ (-N.f15 * N.p) (-N.f15 * (N.q - N.g) + N.t0146v * (1 - N.g))
    (-N.f15 * (N.r - N.d) + N.t0146v * (-N.d))

theorem vT2_eq (N : NF16 x) : N.vT2 = (-N.f15) • (x 4 - x 1) + N.t0146v • (x 5 - x 1) := by
  rw [N.x4, N.x1, N.x5, nfP_sub, nfP_sub]
  simp only [vT2, nfV]
  module

/-- **Lemma 19.3, `T1` for `a > 1`**: the closing `K_3` at `35`, rim `(3, 2, 4, 1)`. -/
theorem isRupert_F3_T1a (N : NF16 x) (hR1 : 0 < (N.g - 1) * (N.p + N.r) - N.d * (N.q - 1))
    (hR2 : 0 < N.a * (N.q - 1) - (N.b - 1) * (N.p + N.r)) (hD : 0 < N.q * N.d - N.r * N.g)
    (hqg : 0 < N.q - N.g) (hg1 : 0 < N.g - 1) (hqb : 0 < N.q - N.b)
    (hc : 0 < N.q * (N.a - 1) - N.b * (N.p - 1)) (hd1 : 0 < N.d - 1)
    (hf15 : 0 < N.d * N.q - (N.g - 1) * (N.p + N.r - 1)) (ha1 : 0 < N.a - 1)
    (hz : IsCyclicUnimodal
          (quad ⟪x 3, (x 5 - x 3)⟫ ⟪x 1, (x 5 - x 3)⟫ ⟪x 4, (x 5 - x 3)⟫ ⟪x 2, (x 5 - x 3)⟫))
    (hnd : NoHDNAt ((univ.image x).erase (x 5)) (x 5 - x 3)) : IsRupert (univ.image x) := by
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  refine isRupert_equadσ (univ.image x) ({x 0, x 6} : Finset ℝ³) (u := (x 5 - x 3))
      (sub_ne_zero.mpr (N.inj.ne (by decide))) hσ (h := (-1 : ℝ)) (by norm_num) (by module)
      (mem_image 5)
    (mem_image 3) (mem_image 1) (mem_image 4) (mem_image 2)
    (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff])
        (by simp [N.inj.eq_iff]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hz hnd ?_
  · nf_test N hσD (by show 0 < N.d * N.p; linarith [mul_pos (N.hd) N.hp])
  · nf_test N hσD (by show 0 < N.a * N.d; linarith [mul_pos (N.ha) N.hd])
  · nf_test N hσD (pos_of_mul_pos_r
          (by show 0 < (1 / 2 : ℝ) * N.d + (1 / 2 : ℝ) * N.g - (1 / 2 : ℝ); linarith [hR1, hf15])
          (by
            show 0 < (-N.a * N.d + N.a * N.r + N.d * N.p) *
              ((1 / 2 : ℝ) * N.d + (1 / 2 : ℝ) * N.g - (1 / 2 : ℝ))
            linarith [mul_pos (N.t146_2) (N.hd), mul_pos (N.tB125) (hd1)]))
  · nf_test N hσD (by show 0 < N.d * N.p; linarith [mul_pos (N.hd) N.hp])
  · nf_test N hσD (by show 0 < N.a * N.r; linarith [mul_pos (N.ha) N.hr])
  · nf_test N hσD (pos_of_mul_pos_r
          (by show 0 < (1 / 2 : ℝ) * N.d + (1 / 2 : ℝ) * N.g - (1 / 2 : ℝ); linarith [hR1, hf15])
          (by
            show 0 < (-N.a * N.d + N.a * N.r + N.d * N.p) *
              ((1 / 2 : ℝ) * N.d + (1 / 2 : ℝ) * N.g - (1 / 2 : ℝ))
            linarith [mul_pos (N.t146_2) (N.hd), mul_pos (N.tB125) (hd1)]))
  · nf_test N hσD (by show 0 < N.a * N.d; linarith [mul_pos (N.ha) N.hd])
  · nf_test N hσD (by show 0 < N.a * N.r; linarith [mul_pos (N.ha) N.hr])
  · intro z hz hzM hn0 hn1 hn2 hn3 hn4
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    fin_cases i
    · exact absurd (by simp) hzM
    · exact absurd rfl hn2
    · exact absurd rfl hn4
    · exact absurd rfl hn1
    · exact absurd rfl hn3
    · exact absurd rfl hn0
    · exact absurd (by simp) hzM
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · refine ⟨x 3, (N.a - 1) / (N.a), (-N.b) / (N.a), Or.inl rfl, div_pos
            (by show 0 < N.a - 1; linarith [ha1]) (by show 0 < N.a; linarith [N.ha]),
            (div_lt_one (by show 0 < N.a; linarith [N.ha])).mpr
            (by have := (by norm_num : (0 : ℝ) < 1); linarith),
            (div_neg_of_neg_of_pos (by have := (by show 0 < N.b; linarith [N.hb]); linarith)
              (by show 0 < N.a; linarith [N.ha])).ne, Or.inr ?_⟩
      refine eq_comb_div (ne_of_gt (by show 0 < N.a; linarith [N.ha])) ?_
      nf_simp N
      ext k
      simp only
          [nfP, nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
      ring
    · refine ⟨x 3, (1) / (N.d), (-N.g) / (N.d), Or.inl rfl, div_pos (by norm_num : (0 : ℝ) < 1)
            (by show 0 < N.d; linarith [N.hd]), (div_lt_one (by show 0 < N.d; linarith [N.hd])).mpr
            (by have := (by show 0 < N.d - 1; linarith [hd1]); linarith),
            (div_neg_of_neg_of_pos (by have := (by show 0 < N.g; linarith [N.hg]); linarith)
              (by show 0 < N.d; linarith [N.hd])).ne, Or.inl ?_⟩
      refine eq_comb_div (ne_of_gt (by show 0 < N.d; linarith [N.hd])) ?_
      nf_simp N
      ext k
      simp only
          [nfP, nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
      ring
-- order: [3, 1, 4, 2]


/-- **Lemma 19.3, `T1` for `a < 1`**: the closing `K_3` at `35`, rim `(3, 0, 4, 1)`. -/
theorem isRupert_F3_T1b (N : NF16 x) (hR1 : 0 < (N.g - 1) * (N.p + N.r) - N.d * (N.q - 1))
    (hR2 : 0 < N.a * (N.q - 1) - (N.b - 1) * (N.p + N.r)) (hD : 0 < N.q * N.d - N.r * N.g)
    (hqg : 0 < N.q - N.g) (hg1 : 0 < N.g - 1) (hqb : 0 < N.q - N.b)
    (hc : 0 < N.q * (N.a - 1) - N.b * (N.p - 1)) (hd1 : 0 < N.d - 1)
    (hf15 : 0 < N.d * N.q - (N.g - 1) * (N.p + N.r - 1)) (ha1 : 0 < 1 - N.a)
    (hz : IsCyclicUnimodal
          (quad ⟪x 3, (x 5 - x 3)⟫ ⟪x 1, (x 5 - x 3)⟫ ⟪x 4, (x 5 - x 3)⟫ ⟪x 0, (x 5 - x 3)⟫))
    (hnd : NoHDNAt ((univ.image x).erase (x 5)) (x 5 - x 3)) : IsRupert (univ.image x) := by
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  refine isRupert_equadσ (univ.image x) ({x 2, x 6} : Finset ℝ³) (u := (x 5 - x 3))
      (sub_ne_zero.mpr (N.inj.ne (by decide))) hσ (h := (-1 : ℝ)) (by norm_num) (by module)
      (mem_image 5)
    (mem_image 3) (mem_image 1) (mem_image 4) (mem_image 0)
    (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff])
        (by simp [N.inj.eq_iff]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hz hnd ?_
  · nf_test N hσD (by show 0 < N.d * N.p; linarith [mul_pos (N.hd) N.hp])
  · nf_test N hσD (by show 0 < N.d; linarith [N.hd])
  · nf_test N hσD (pos_of_mul_pos_r (by
            show 0 < -(1 / 4 : ℝ) * N.d * N.q + (1 / 4 : ℝ) * N.g * N.p + (1 / 4 : ℝ) * N.g * N.r +
              (1 / 4 : ℝ) * N.d + (1 / 4 : ℝ) * N.q - (1 / 4 : ℝ)
            linarith [hR1, N.t0246, N.hab, hR2])
          (by
            show 0 < (N.d * N.p - N.d + N.r) *
              (-(1 / 4 : ℝ) * N.d * N.q + (1 / 4 : ℝ) * N.g * N.p + (1 / 4 : ℝ) * N.g * N.r +
                (1 / 4 : ℝ) * N.d + (1 / 4 : ℝ) * N.q - (1 / 4 : ℝ))
            linarith [mul_pos (N.t0146) (mul_pos (N.hd) N.hp), mul_pos (N.t0146)
                (mul_pos (N.ha) N.hr), mul_pos (mul_pos (N.t0146) (ha1)) (N.hr), mul_pos (N.t145_0)
                (hd1)]))
  · nf_test N hσD (by show 0 < N.d * N.p; linarith [mul_pos (N.hd) N.hp])
  · nf_test N hσD (by show 0 < N.r; linarith [N.hr])
  · nf_test N hσD (pos_of_mul_pos_r (by
            show 0 < -(1 / 4 : ℝ) * N.d * N.q + (1 / 4 : ℝ) * N.g * N.p + (1 / 4 : ℝ) * N.g * N.r +
              (1 / 4 : ℝ) * N.d + (1 / 4 : ℝ) * N.q - (1 / 4 : ℝ)
            linarith [hR1, N.t0246, N.hab, hR2])
          (by
            show 0 < (N.d * N.p - N.d + N.r) *
              (-(1 / 4 : ℝ) * N.d * N.q + (1 / 4 : ℝ) * N.g * N.p + (1 / 4 : ℝ) * N.g * N.r +
                (1 / 4 : ℝ) * N.d + (1 / 4 : ℝ) * N.q - (1 / 4 : ℝ))
            linarith [mul_pos (N.t0146) (mul_pos (N.hd) N.hp), mul_pos (N.t0146)
                (mul_pos (N.ha) N.hr), mul_pos (mul_pos (N.t0146) (ha1)) (N.hr), mul_pos (N.t145_0)
                (hd1)]))
  · nf_test N hσD (by show 0 < N.d; linarith [N.hd])
  · nf_test N hσD (by show 0 < N.r; linarith [N.hr])
  · intro z hz hzM hn0 hn1 hn2 hn3 hn4
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    fin_cases i
    · exact absurd rfl hn4
    · exact absurd rfl hn2
    · exact absurd (by simp) hzM
    · exact absurd rfl hn1
    · exact absurd rfl hn3
    · exact absurd rfl hn0
    · exact absurd (by simp) hzM
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · refine ⟨x 5, (-N.a + 1) / (1), (N.a + N.b - 1) / (1), Or.inr
            ⟨rfl, by have := div_pos (by show 0 < N.a + N.b - 1; linarith [N.hab]) (by norm_num : (0 : ℝ) < 1); linarith⟩,
            div_pos (by show 0 < -N.a + 1; linarith [ha1]) (by norm_num : (0 : ℝ) < 1),
            (div_lt_one (by norm_num : (0 : ℝ) < 1)).mpr
            (by have := (by show 0 < N.a; linarith [N.ha]); linarith),
            (div_pos (by show 0 < N.a + N.b - 1; linarith [N.hab]) (by norm_num : (0 : ℝ) < 1)).ne',
            Or.inr ?_⟩
      refine eq_comb_div (ne_of_gt (by norm_num : (0 : ℝ) < 1)) ?_
      nf_simp N
      ext k
      simp only
          [nfP, nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
      ring
    · refine ⟨x 3, (1) / (N.d), (-N.g) / (N.d), Or.inl rfl, div_pos (by norm_num : (0 : ℝ) < 1)
            (by show 0 < N.d; linarith [N.hd]), (div_lt_one (by show 0 < N.d; linarith [N.hd])).mpr
            (by have := (by show 0 < N.d - 1; linarith [hd1]); linarith),
            (div_neg_of_neg_of_pos (by have := (by show 0 < N.g; linarith [N.hg]); linarith)
              (by show 0 < N.d; linarith [N.hd])).ne, Or.inl ?_⟩
      refine eq_comb_div (ne_of_gt (by show 0 < N.d; linarith [N.hd])) ?_
      nf_simp N
      ext k
      simp only
          [nfP, nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
      ring
-- order: [3, 1, 4, 0]


/-- The view `vT2` is not zero (its first coefficient is `−f15 p`). -/
theorem vT2_ne (N : NF16 x) (hf15 : 0 < N.d * N.q - (N.g - 1) * (N.p + N.r - 1)) : N.vT2 ≠ 0 := by
  refine nfV_ne_zero N.hD (Or.inl (ne_of_gt ?_))
  simp only [f15]; nlinarith [mul_pos hf15 N.hp]

/-- **Lemma 19.3, `T2`**: the vertex crossing `046/145` at `4`, rim `(4, 5, 3, 6)`. -/
theorem isRupert_F3_T2 (N : NF16 x) (hR1 : 0 < (N.g - 1) * (N.p + N.r) - N.d * (N.q - 1))
    (hR2 : 0 < N.a * (N.q - 1) - (N.b - 1) * (N.p + N.r)) (hD : 0 < N.q * N.d - N.r * N.g)
    (hqg : 0 < N.q - N.g) (hg1 : 0 < N.g - 1) (hqb : 0 < N.q - N.b)
    (hc : 0 < N.q * (N.a - 1) - N.b * (N.p - 1)) (hd1 : 0 < N.d - 1)
    (hf15 : 0 < N.d * N.q - (N.g - 1) * (N.p + N.r - 1))
    (hz : IsCyclicUnimodal (quad ⟪x 4, N.vT2⟫ ⟪x 6, N.vT2⟫ ⟪x 3, N.vT2⟫ ⟪x 5, N.vT2⟫))
    (hnd : NoHDNAt (univ.image x) N.vT2) : IsRupert (univ.image x) := by
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  refine isRupert_vquadσ (univ.image x) ({x 0, x 1} : Finset ℝ³) (u := N.vT2) (N.vT2_ne hf15) hσ
    (mem_image 4) (mem_image 6) (mem_image 3) (mem_image 5)
    (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff])
        (by simp [N.inj.eq_iff]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hz hnd ?_
  · simp only [NF16.vT2, NF16.f15, NF16.t0146v]; nf_test N hσD
        (by
          show 0 < N.d * N.p * N.q + N.g * N.p * N.q - N.p * N.q
          linarith [mul_pos (N.hgd) (mul_pos (N.hp) N.hq)])
  · simp only [NF16.vT2, NF16.f15, NF16.t0146v]; nf_test N hσD
        (by
          show 0 < N.d * N.p * N.q + N.d * N.p * N.r + N.d * N.p ^ 2 + N.g * N.p * N.q + N.g * N.p *
            N.r + N.g * N.p ^ 2 - N.d * N.p - N.g * N.p - N.p * N.q - N.p * N.r - N.p ^ 2 + N.p
          linarith [N.hp, mul_pos (hd1) (mul_pos (N.hp) N.hr), mul_pos (N.t0146) (N.hp), mul_pos
              (hg1) (mul_pos (N.hd) N.hp), mul_pos (hd1) (mul_pos (N.hp) N.hp), mul_pos (hd1)
              (mul_pos (N.hp) N.hq), mul_pos (hqg) (mul_pos (N.hd) N.hp), mul_pos (hg1)
              (mul_pos (N.hp) N.hq)])
  · simp only [NF16.vT2, NF16.f15, NF16.t0146v]; nf_test N hσD
        (by
          show 0 < N.d * N.p * N.q - N.g * N.p * N.r - N.g * N.p ^ 2 + N.g * N.p + N.p * N.r + N.p ^
            2 - N.p
          linarith [mul_pos (hf15) (N.hp)])
  · simp only [NF16.vT2, NF16.f15, NF16.t0146v]; nf_test N hσD
        (by
          show 0 < N.d * N.p * N.q + N.g * N.p * N.q - N.p * N.q
          linarith [mul_pos (N.hgd) (mul_pos (N.hp) N.hq)])
  · simp only [NF16.vT2, NF16.f15, NF16.t0146v]; nf_test N hσD
        (by
          show 0 < N.d * N.p * N.q + N.d * N.p * N.r + N.d * N.p ^ 2 - N.d * N.p
          linarith [mul_pos (N.t046_5) (mul_pos (N.hd) N.hp)])
  · simp only [NF16.vT2, NF16.f15, NF16.t0146v]; nf_test N hσD
        (by
          show 0 < N.d * N.p * N.q - N.g * N.p * N.r - N.g * N.p ^ 2 + N.g * N.p + N.p * N.r + N.p ^
            2 - N.p
          linarith [mul_pos (hf15) (N.hp)])
  · simp only [NF16.vT2, NF16.f15, NF16.t0146v]; nf_test N hσD
        (by
          show 0 < N.d * N.p * N.q + N.d * N.p * N.r + N.d * N.p ^ 2 + N.g * N.p * N.q + N.g * N.p *
            N.r + N.g * N.p ^ 2 - N.d * N.p - N.g * N.p - N.p * N.q - N.p * N.r - N.p ^ 2 + N.p
          linarith [N.hp, mul_pos (hd1) (mul_pos (N.hp) N.hr), mul_pos (N.t0146) (N.hp), mul_pos
              (hg1) (mul_pos (N.hd) N.hp), mul_pos (hd1) (mul_pos (N.hp) N.hp), mul_pos (hd1)
              (mul_pos (N.hp) N.hq), mul_pos (hqg) (mul_pos (N.hd) N.hp), mul_pos (hg1)
              (mul_pos (N.hp) N.hq)])
  · simp only [NF16.vT2, NF16.f15, NF16.t0146v]; nf_test N hσD
        (by
          show 0 < N.d * N.p * N.q + N.d * N.p * N.r + N.d * N.p ^ 2 - N.d * N.p
          linarith [mul_pos (N.t046_5) (mul_pos (N.hd) N.hp)])
  · intro z hz hzM hn0 hn1 hn2 hn3
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    fin_cases i
    · exact absurd (by simp) hzM
    · exact absurd (by simp) hzM
    · refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [NF16.vT2, NF16.f15, NF16.t0146v]; nf_test N hσD
            (by
              show 0 < -N.a * N.d * N.p * N.q - N.a * N.g * N.p * N.q + N.b * N.d * N.p * N.r + N.b
                * N.d * N.p ^ 2 + N.b * N.g * N.p * N.r + N.b * N.g * N.p ^ 2 + N.a * N.p * N.q -
                N.b * N.d * N.p - N.b * N.g * N.p - N.b * N.p * N.r - N.b * N.p ^ 2 + N.d * N.p *
                N.q + N.g * N.p * N.q + N.b * N.p - N.p * N.q
              linarith [mul_pos (mul_pos (N.hgd) (N.t0246)) (N.hp)])
      · simp only [NF16.vT2, NF16.f15, NF16.t0146v]; nf_test N hσD
            (by
              show 0 < -N.a * N.d * N.q ^ 2 + N.a * N.g * N.p * N.q + N.a * N.g * N.q * N.r + N.b *
                N.d * N.p * N.q - N.b * N.g * N.p * N.r - N.b * N.g * N.p ^ 2 + N.a * N.d * N.q -
                N.a * N.p * N.q - N.a * N.q * N.r + N.b * N.g * N.p + N.b * N.p * N.r + N.b * N.p ^
                2 - N.b * N.p
              linarith [mul_pos (hf15) (mul_pos (N.hb) N.hp), mul_pos (hR1) (mul_pos (N.ha) N.hq)])
      · simp only [NF16.vT2, NF16.f15, NF16.t0146v]; nf_test N hσD
            (by
              show 0 < -N.a * N.d * N.q * N.r + N.a * N.g * N.p * N.r + N.a * N.g * N.r ^ 2 + N.a *
                N.d * N.p + N.a * N.d * N.q + N.a * N.d * N.r - N.a * N.g * N.r - N.a * N.p * N.r -
                N.a * N.r ^ 2 - N.a * N.d + N.a * N.r
              linarith [mul_pos (N.t145_0) (N.ha), mul_pos (hR1) (mul_pos (N.ha) N.hr)])
      · simp only [NF16.vT2, NF16.f15, NF16.t0146v]; nf_test N hσD
            (by
              show 0 < N.a * N.d * N.p * N.q + N.a * N.d * N.q * N.r + N.a * N.d * N.q ^ 2 - N.a *
                N.g * N.p * N.r - N.a * N.g * N.q * N.r - N.a * N.g * N.r ^ 2 - N.b * N.d * N.p *
                N.q - N.b * N.d * N.p * N.r - N.b * N.d * N.p ^ 2 - N.a * N.d * N.p - 2 * N.a * N.d
                * N.q - N.a * N.d * N.r + N.a * N.g * N.r + N.a * N.p * N.r + N.a * N.q * N.r + N.a
                * N.r ^ 2 + N.b * N.d * N.p + N.d * N.p * N.q + N.d * N.p * N.r + N.d * N.p ^ 2 +
                N.a * N.d - N.a * N.r - N.d * N.p
              linarith [mul_pos (N.t046_5) (N.tB125)])
    · exact absurd rfl hn2
    · exact absurd rfl hn0
    · exact absurd rfl hn3
    · exact absurd rfl hn1
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · refine ⟨(N.d * N.p * N.q + N.d * N.q ^ 2 - N.g * N.q * N.r - N.d * N.q + N.q * N.r) /
            (N.d * N.p * N.q + N.g * N.p * N.q - N.p * N.q), (N.q) /
            (N.d * N.p * N.q + N.g * N.p * N.q - N.p * N.q), div_pos
            (by
              show 0 < N.d * N.p * N.q + N.d * N.q ^ 2 - N.g * N.q * N.r - N.d * N.q + N.q * N.r
              linarith [mul_pos (N.t145_0) (N.hq)])
            (by
              show 0 < N.d * N.p * N.q + N.g * N.p * N.q - N.p * N.q
              linarith [mul_pos (N.hgd) (mul_pos (N.hp) N.hq)]),
            (div_lt_one (by
                show 0 < N.d * N.p * N.q + N.g * N.p * N.q - N.p * N.q
                linarith [mul_pos (N.hgd) (mul_pos (N.hp) N.hq)])).mpr
            (by
              have := (by
                  show 0 < -N.d * N.q ^ 2 + N.g * N.p * N.q + N.g * N.q * N.r + N.d * N.q - N.p *
                    N.q - N.q * N.r
                  linarith [mul_pos (hR1) (N.hq)])
              linarith), (div_pos (by show 0 < N.q; linarith [N.hq])
              (by
                show 0 < N.d * N.p * N.q + N.g * N.p * N.q - N.p * N.q
                linarith [mul_pos (N.hgd) (mul_pos (N.hp) N.hq)])).ne', Or.inl ?_⟩
      refine eq_comb_div (ne_of_gt (by
              show 0 < N.d * N.p * N.q + N.g * N.p * N.q - N.p * N.q
              linarith [mul_pos (N.hgd) (mul_pos (N.hp) N.hq)])) ?_
      simp only [NF16.vT2, NF16.f15, NF16.t0146v]; nf_simp N
      ext k
      simp only
          [nfP, nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
      ring
    · refine ⟨(N.d * N.g * N.p * N.q - N.g ^ 2 * N.p * N.r - N.g ^ 2 * N.p ^ 2 - N.d * N.p * N.q + 2
              * N.g * N.p * N.r + 2 * N.g * N.p ^ 2 + N.g ^ 2 * N.p - 2 * N.g * N.p - N.p * N.r -
              N.p ^ 2 + N.p) / (N.g * N.p * N.q + N.g * N.p * N.r + N.g * N.p ^ 2 - N.g * N.p - N.p
              * N.q - N.p * N.r - N.p ^ 2 + N.p), (-N.g * N.p + N.p) /
            (N.g * N.p * N.q + N.g * N.p * N.r + N.g * N.p ^ 2 - N.g * N.p - N.p * N.q - N.p * N.r -
              N.p ^ 2 + N.p), div_pos (by
              show 0 < N.d * N.g * N.p * N.q - N.g ^ 2 * N.p * N.r - N.g ^ 2 * N.p ^ 2 - N.d * N.p *
                N.q + 2 * N.g * N.p * N.r + 2 * N.g * N.p ^ 2 + N.g ^ 2 * N.p - 2 * N.g * N.p - N.p
                * N.r - N.p ^ 2 + N.p
              linarith [mul_pos (mul_pos (hg1) (hf15)) (N.hp)])
            (by
              show 0 < N.g * N.p * N.q + N.g * N.p * N.r + N.g * N.p ^ 2 - N.g * N.p - N.p * N.q -
                N.p * N.r - N.p ^ 2 + N.p
              linarith [mul_pos (mul_pos (N.hgd) (hg1)) (N.hp), mul_pos (mul_pos (N.hgd) (hqg))
                  (N.hp), mul_pos (hR1) (N.hp)]),
            (div_lt_one (by
                show 0 < N.g * N.p * N.q + N.g * N.p * N.r + N.g * N.p ^ 2 - N.g * N.p - N.p * N.q -
                  N.p * N.r - N.p ^ 2 + N.p
                linarith [mul_pos (mul_pos (N.hgd) (hg1)) (N.hp), mul_pos (mul_pos (N.hgd) (hqg))
                    (N.hp), mul_pos (hR1) (N.hp)])).mpr
            (by
              have := (by
                  show 0 < -N.d * N.g * N.p * N.q + N.g ^ 2 * N.p * N.r + N.g ^ 2 * N.p ^ 2 + N.d *
                    N.p * N.q + N.g * N.p * N.q - N.g * N.p * N.r - N.g * N.p ^ 2 - N.g ^ 2 * N.p +
                    N.g * N.p - N.p * N.q
                  linarith
                    [mul_pos (mul_pos (hqg) (hf15)) (N.hp), mul_pos (hR1) (mul_pos (N.hp) N.hq)])
              linarith), (div_neg_of_neg_of_pos
              (by have := (by show 0 < N.g * N.p - N.p; linarith [mul_pos (hg1) (N.hp)]); linarith)
              (by
                show 0 < N.g * N.p * N.q + N.g * N.p * N.r + N.g * N.p ^ 2 - N.g * N.p - N.p * N.q -
                  N.p * N.r - N.p ^ 2 + N.p
                linarith [mul_pos (mul_pos (N.hgd) (hg1)) (N.hp), mul_pos (mul_pos (N.hgd) (hqg))
                    (N.hp), mul_pos (hR1) (N.hp)])).ne, Or.inr (Or.inr (Or.inr ?_))⟩
      refine eq_comb_div (ne_of_gt (by
              show 0 < N.g * N.p * N.q + N.g * N.p * N.r + N.g * N.p ^ 2 - N.g * N.p - N.p * N.q -
                N.p * N.r - N.p ^ 2 + N.p
              linarith [mul_pos (mul_pos (N.hgd) (hg1)) (N.hp), mul_pos (mul_pos (N.hgd) (hqg))
                  (N.hp), mul_pos (hR1) (N.hp)])) ?_
      simp only [NF16.vT2, NF16.f15, NF16.t0146v]; nf_simp N
      ext k
      simp only
          [nfP, nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
      ring
-- order: [4, 6, 3, 5]



/-- **Lemma 19.3** (`Ω ∩ {d > 1}`): the closing `T1 = K_3` at `35` (rim `(3, x, 4, 1)`,
`x = 2` iff `a > 1`) or the vertex crossing `T2 = 046/145` at `4` (view `vT2`, rim
`(4, 6, 3, 5)`) is unimodal.  `T1` fails only with `{3, 4}` above `{x, 1}` (its diagonals cross
along `5 − 3` with `l ≤ 0`, as `E35` fails), and then `⟪vT2, 5 − 3⟫ > 0`; `T2` fails only with
`{4, 3}` above `{5, 6}` (crossing with `λ = −1/K < 0`), and then `⟪5 − 3, vT2⟫ < 0`. -/
theorem isRupert_F3 (N : NF16 x) (O : Omega N) (hd1 : 0 < N.d - 1) (ha1 : N.a ≠ 1)
    (hf15 : 0 < N.d * N.q - (N.g - 1) * (N.p + N.r - 1))
    (hg : GenPos (univ.image x)) (hnd : NoHDNEdges16 x)
    (hv : [⟪x 4, N.vT2⟫, ⟪x 6, N.vT2⟫, ⟪x 3, N.vT2⟫, ⟪x 5, N.vT2⟫].Nodup)
    (hndv : NoHDNAt (univ.image x) N.vT2) : IsRupert (univ.image x) := by
  obtain ⟨hR1, hR2, hD, hqg, hg1, hqb, hc, nD2, -, -, -, -⟩ := O
  have huu : 0 < ⟪(x 5 - x 3), (x 5 - x 3)⟫ := real_inner_self_pos.mpr
      (sub_ne_zero.mpr (N.inj.ne (by decide)))
  -- `T2` fails only one way, giving `⟪5 − 3, vT2⟫ < 0`
  have hT2 : DepthSep (x 4) (x 3) (x 6) (x 5) N.vT2 → ⟪x 5, N.vT2⟫ < ⟪x 3, N.vT2⟫ := by
    intro h
    set K := N.q * (N.g + N.d - 1) + N.d * (N.p + N.q + N.r - 1) with hK
    have hK0 : 0 < K := by nlinarith [mul_pos N.hq N.hgd, mul_pos N.hd N.t046_5]
    have hs := depthSep_of_meet (d₀ := x 4) (d₁ := x 3) (e₀ := x 6) (e₁ := x 5) (w := N.vT2)
      (s := (N.g + N.d - 1) * (N.p + N.q + N.r - 1) / K)
      (t := (N.q * (N.g + N.d - 1) + N.d * (N.p + N.q + N.r - 1) - N.d * (N.p + N.q + N.r - 1)) / K)
      (l := -1 / K) (div_pos (mul_pos N.hgd N.t046_5) hK0).le
      ((div_le_one hK0).mpr (by nlinarith [hf15]))
      (div_pos (by nlinarith [mul_pos N.hq N.hgd]) hK0).le
      ((div_le_one hK0).mpr (by nlinarith [mul_pos N.hd N.t046_5])) ?_
      (div_nonpos_of_nonpos_of_nonneg (by norm_num) hK0.le) h
    · have := max_lt_iff.mp hs; have := lt_min_iff.mp this.2; linarith
    · have hK0' := hK0.ne'
      simp only [vT2, f15, t0146v]
      nf_simp N
      ext k
      simp only [nfP, nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply,
        smul_eq_mul]
      field_simp
      ring
  -- the two tests at `35`
  have hz35 := fun X (hX : [3, 5, 1, X, 4].Nodup) =>
    depth_nodup4 (v := 3) (w := 5) (a := 1) (b := X) (c := 4) N.inj hg hX
  have key : ∀ X : Fin 7, ∀ {s t l : ℝ}, 0 ≤ s → s ≤ 1 → 0 ≤ t → t ≤ 1 → l ≤ 0 →
      (x 1 + t • (x X - x 1)) - (x 3 + s • (x 4 - x 3)) = l • (x 5 - x 3) →
      DepthSep (x 3) (x 4) (x 1) (x X) (x 5 - x 3) →
      ¬ DepthSep (x 4) (x 3) (x 6) (x 5) N.vT2 := by
    intro X s t l hs0 hs1 ht0 ht1 hl hm h1 h2
    have hs := depthSep_of_meet hs0 hs1 ht0 ht1 hm hl h1
    have k1 := max_lt_iff.mp hs
    have k2 := lt_min_iff.mp k1.1
    have k3 := lt_min_iff.mp k1.2
    have h5 := hT2 h2
    have e1 : ⟪x 5, N.vT2⟫ - ⟪x 3, N.vT2⟫ = ⟪N.vT2, (x 5 - x 3)⟫ := by
      rw [inner_sub_right, real_inner_comm, real_inner_comm (x 3)]
    have e2 : ⟪N.vT2, (x 5 - x 3)⟫ = -N.f15 * (⟪x 4, (x 5 - x 3)⟫ - ⟪x 1, (x 5 - x 3)⟫) +
        N.t0146v *
            ((⟪x 5, (x 5 - x 3)⟫ - ⟪x 3, (x 5 - x 3)⟫) + (⟪x 3, (x 5 - x 3)⟫ - ⟪x 1, (x 5 - x 3)⟫))
            := by
      rw [vT2_eq]; simp only [inner_add_left, real_inner_smul_left, inner_sub_left]; ring
    have e3 : ⟪x 5, (x 5 - x 3)⟫ - ⟪x 3, (x 5 - x 3)⟫ = ⟪(x 5 - x 3), (x 5 - x 3)⟫ :=
        by rw [inner_sub_left]
    have hf : 0 < -N.f15 := by simp only [f15]; linarith
    have ht : 0 < N.t0146v := N.t0146
    nlinarith [mul_pos hf (show 0 < ⟪x 4, (x 5 - x 3)⟫ - ⟪x 1, (x 5 - x 3)⟫ by linarith),
      mul_pos ht (show 0 < ⟪(x 5 - x 3), (x 5 - x 3)⟫ + (⟪x 3, (x 5 - x 3)⟫ - ⟪x 1, (x 5 - x 3)⟫)
            by linarith)]
  have T2ok : ¬ DepthSep (x 4) (x 3) (x 6) (x 5) N.vT2 → IsRupert (univ.image x) := fun h =>
    isRupert_F3_T2 N hR1 hR2 hD hqg hg1 hqb hc hd1 hf15 (quad_unimodal h hv) hndv
  rcases lt_or_gt_of_ne ha1 with ha | ha
  · have hz := hz35 0 (by decide)
    have ha' : 0 < 1 - N.a := by linarith
    by_cases h1 : DepthSep (x 3) (x 4) (x 1) (x 0) (x 5 - x 3)
    · have hc4 : 0 < N.d * N.p - N.d + N.r :=
          (pos_of_mul_pos_r (by
              show 0 < -(1 / 4 : ℝ) * N.d * N.q + (1 / 4 : ℝ) * N.g * N.p + (1 / 4 : ℝ) * N.g * N.r
                + (1 / 4 : ℝ) * N.d + (1 / 4 : ℝ) * N.q - (1 / 4 : ℝ)
              linarith [hR1, N.t0246, N.hab, hR2])
            (by
              show 0 < (N.d * N.p - N.d + N.r) *
                (-(1 / 4 : ℝ) * N.d * N.q + (1 / 4 : ℝ) * N.g * N.p + (1 / 4 : ℝ) * N.g * N.r +
                  (1 / 4 : ℝ) * N.d + (1 / 4 : ℝ) * N.q - (1 / 4 : ℝ))
              linarith [mul_pos (N.t0146) (mul_pos (N.hd) N.hp), mul_pos (N.t0146)
                  (mul_pos (N.ha) N.hr), mul_pos (mul_pos (N.t0146) (ha')) (N.hr), mul_pos
                  (N.t145_0) (hd1)]))
      have hK : 0 < N.d * N.p + N.r := by nlinarith [mul_pos N.hd N.hp, N.hr]
      refine T2ok (key 0 (s := N.d / (N.d * N.p + N.r)) (t := N.d * N.p / (N.d * N.p + N.r))
        (l := (N.g * N.r - N.d * N.q) / (N.d * N.p + N.r)) (div_pos N.hd hK).le
        ((div_le_one hK).mpr (by linarith)) (div_pos (mul_pos N.hd N.hp) hK).le
        ((div_le_one hK).mpr (by linarith [N.hr]))
        (div_nonpos_of_nonpos_of_nonneg (by linarith) hK.le) ?_ h1)
      have hK' := hK.ne'
      nf_simp N
      ext k
      simp only [nfP, nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply,
        smul_eq_mul]
      field_simp
      ring
    · exact isRupert_F3_T1b N hR1 hR2 hD hqg hg1 hqb hc hd1 hf15 ha'
        (quad_unimodal h1 hz.1) (hnd.fwd N (by decide))
  · have hz := hz35 2 (by decide)
    have ha' : 0 < N.a - 1 := by linarith
    by_cases h1 : DepthSep (x 3) (x 4) (x 1) (x 2) (x 5 - x 3)
    · have hc4 : 0 < -N.a * N.d + N.a * N.r + N.d * N.p :=
          (pos_of_mul_pos_r
            (by show 0 < (1 / 2 : ℝ) * N.d + (1 / 2 : ℝ) * N.g - (1 / 2 : ℝ); linarith [hR1, hf15])
            (by
              show 0 < (-N.a * N.d + N.a * N.r + N.d * N.p) *
                ((1 / 2 : ℝ) * N.d + (1 / 2 : ℝ) * N.g - (1 / 2 : ℝ))
              linarith [mul_pos (N.t146_2) (N.hd), mul_pos (N.tB125) (hd1)]))
      have hK : 0 < N.a * N.r + N.d * N.p := by nlinarith [mul_pos N.hd N.hp, mul_pos N.ha N.hr]
      refine T2ok (key 2 (s := N.a * N.d / (N.a * N.r + N.d * N.p))
        (t := N.d * N.p / (N.a * N.r + N.d * N.p))
        (l := (N.p * N.b * N.d + N.r * N.g * N.a - N.q * N.a * N.d) / (N.a * N.r + N.d * N.p))
        (div_pos (mul_pos N.ha N.hd) hK).le ((div_le_one hK).mpr (by linarith))
        (div_pos (mul_pos N.hd N.hp) hK).le
        ((div_le_one hK).mpr (by linarith [mul_pos N.ha N.hr]))
        (div_nonpos_of_nonpos_of_nonneg (nD2 ha' hd1) hK.le) ?_ h1)
      have hK' := hK.ne'
      nf_simp N
      ext k
      simp only [nfP, nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply,
        smul_eq_mul]
      field_simp
      ring
    · exact isRupert_F3_T1a N hR1 hR2 hD hqg hg1 hqb hc hd1 hf15 ha'
        (quad_unimodal h1 hz.1) (hnd.fwd N (by decide))


/-! ### Lemma 19.4 and Lemma 19.5: the views -/

/-- `c36`: `024` faces toward `6` at the view along `36` iff `c36 > 0`. -/
def c36v (N : NF16 x) : ℝ := N.q * (N.a - 1) - N.b * (N.p - 1)

/-- `[0246]`. -/
def t0246v (N : NF16 x) : ℝ := N.b * (N.p + N.r - 1) - N.q * (N.a - 1)

/-- `f03`: `146` faces toward `3` at the view along `03` iff `f03 > 0`. -/
def f03 (N : NF16 x) : ℝ := N.q * (1 - N.d) + N.g * (N.r - 1)

/-- **The view of `A`** (§19.4 (i)): `v_A = (g p, 0, f03) = g p (0 − 6) + [0146] (6 − 3)`, along the
line of the planes `036` and `146`. -/
noncomputable def vA (N : NF16 x) : ℝ³ := nfV N.E₁ N.E₂ N.E₃ (N.g * N.p) 0 N.f03

/-- **The view of `T_a`** (§19.5): `u_a = (p + r − 1, q, 0) = (4 − 0) + r (0 − 6)`, along the
line of the planes `0235` and `046`. -/
noncomputable def uA (N : NF16 x) : ℝ³ := nfV N.E₁ N.E₂ N.E₃ (N.p + N.r - 1) N.q 0

theorem vA_eq (N : NF16 x) :
    N.vA = (N.g * N.p) • (x 0 - x 6) + N.t0146v • (x 6 - x 3) := by
  rw [N.x0, N.x6, N.x3, nfP_sub, nfP_sub]
  simp only [vA, f03, t0146v, nfV]
  module

/-- `q (1 − p*) = −v_A` with `p* = 6 + (g/q)(4 − 6)`. -/
theorem vA_eq' (N : NF16 x) :
    N.vA = -(N.q • (x 1 - x 6) - N.g • (x 4 - x 6)) := by
  rw [N.x1, N.x4, N.x6, nfP_sub, nfP_sub]
  simp only [vA, f03, nfV]
  module

theorem uA_eq (N : NF16 x) : N.uA = (x 4 - x 0) + N.r • (x 0 - x 6) := by
  rw [N.x4, N.x0, N.x6, nfP_sub, nfP_sub]
  simp only [uA, nfV]
  module

/-- **Lemma 19.4, `A`**: the vertex crossing `036/146` at `6` (view `vA`), rim `(6, 4, 5, 3)`
(`H_A < 0`: `2` hidden). -/
theorem isRupert_F1s_A (N : NF16 x) (hR1 : 0 < (N.g - 1) * (N.p + N.r) - N.d * (N.q - 1))
    (hR2 : 0 < N.a * (N.q - 1) - (N.b - 1) * (N.p + N.r)) (hD : 0 < N.q * N.d - N.r * N.g)
    (hqg : 0 < N.q - N.g) (hg1 : 0 < N.g - 1) (hqb : 0 < N.q - N.b)
    (hc : 0 < N.q * (N.a - 1) - N.b * (N.p - 1)) (hd1 : 0 < 1 - N.d)
    (hf03 : 0 < -(N.q * (1 - N.d) + N.g * (N.r - 1)))
    (hHA : 0 < -((N.b - 1) * N.g * N.p * N.r + (N.q * (1 - N.d) + N.g * (N.r - 1)) *
        (N.a * (N.q - 1) - (N.b - 1) * N.p)))
    (hz : IsCyclicUnimodal (quad ⟪x 6, N.vA⟫ ⟪x 3, N.vA⟫ ⟪x 5, N.vA⟫ ⟪x 4, N.vA⟫))
    (hnd : NoHDNAt (univ.image x) N.vA) : IsRupert (univ.image x) := by
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  refine isRupert_vquadσ (univ.image x) ({x 0, x 1} : Finset ℝ³) (u := N.vA)
      (by
        simp only [NF16.vA, NF16.f03]
        exact nfV_ne_zero N.hD (Or.inl (ne_of_gt
              (by have := (by show 0 < N.g * N.p; linarith [mul_pos (N.hg) N.hp]); linarith)))) hσ
    (mem_image 6) (mem_image 3) (mem_image 5) (mem_image 4)
    (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff])
        (by simp [N.inj.eq_iff]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hz hnd ?_
  · simp only [NF16.vA, NF16.f03]; nf_test N hσD
        (by show 0 < N.g * N.p; linarith [mul_pos (N.hg) N.hp])
  · simp only [NF16.vA, NF16.f03]; nf_test N hσD
        (by show 0 < N.g * N.p * N.q; linarith [mul_pos (mul_pos (N.hg) N.hp) N.hq])
  · simp only [NF16.vA, NF16.f03]; nf_test N hσD
        (by
          show 0 < N.d * N.p * N.q + N.g * N.p - N.p * N.q
          linarith [mul_pos (hf03) (N.hp), mul_pos (hg1) (mul_pos (N.hp) N.hr), mul_pos (N.hp) N.hr])
  · simp only [NF16.vA, NF16.f03]; nf_test N hσD
        (by show 0 < N.g * N.p; linarith [mul_pos (N.hg) N.hp])
  · simp only [NF16.vA, NF16.f03]; nf_test N hσD
        (by
          show 0 < N.d * N.p * N.q + N.g * N.p * N.q - N.p * N.q
          linarith [mul_pos (N.hgd) (mul_pos (N.hp) N.hq)])
  · simp only [NF16.vA, NF16.f03]; nf_test N hσD
        (by
          show 0 < N.d * N.p * N.q + N.g * N.p - N.p * N.q
          linarith [mul_pos (hf03) (N.hp), mul_pos (hg1) (mul_pos (N.hp) N.hr), mul_pos (N.hp) N.hr])
  · simp only [NF16.vA, NF16.f03]; nf_test N hσD
        (by show 0 < N.g * N.p * N.q; linarith [mul_pos (mul_pos (N.hg) N.hp) N.hq])
  · simp only [NF16.vA, NF16.f03]; nf_test N hσD
        (by
          show 0 < N.d * N.p * N.q + N.g * N.p * N.q - N.p * N.q
          linarith [mul_pos (N.hgd) (mul_pos (N.hp) N.hq)])
  · intro z hz hzM hn0 hn1 hn2 hn3
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    fin_cases i
    · exact absurd (by simp) hzM
    · exact absurd (by simp) hzM
    · refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [NF16.vA, NF16.f03]; nf_test N hσD
            (by show 0 < N.b * N.g * N.p; linarith [mul_pos (mul_pos (N.hb) N.hg) N.hp])
      · simp only [NF16.vA, NF16.f03]; nf_test N hσD
            (by
              show 0 < N.a * N.d * N.q - N.a * N.g * N.r + N.a * N.g - N.a * N.q
              linarith [mul_pos (hf03) (N.ha)])
      · simp only [NF16.vA, NF16.f03]; nf_test N hσD
            (by
              show 0 < N.a * N.d * N.q ^ 2 - N.a * N.g * N.q * N.r - N.b * N.d * N.p * N.q - N.a *
                N.d * N.q + N.a * N.g * N.q + N.a * N.g * N.r - N.a * N.q ^ 2 - N.b * N.g * N.p +
                N.b * N.p * N.q + N.d * N.p * N.q - N.a * N.g + N.a * N.q + N.g * N.p - N.p * N.q
              linarith [hHA])
      · simp only [NF16.vA, NF16.f03]; nf_test N hσD
            (by
              show 0 < -N.a * N.d * N.q ^ 2 + N.a * N.g * N.q * N.r + N.b * N.d * N.p * N.q - N.a *
                N.g * N.q + N.a * N.q ^ 2 - N.b * N.p * N.q + N.g * N.p * N.q
              linarith [mul_pos (N.t146_2) (N.hq)])
    · exact absurd rfl hn1
    · exact absurd rfl hn3
    · exact absurd rfl hn2
    · exact absurd rfl hn0
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · refine ⟨(-N.d * N.q + N.g * N.p + N.g * N.r - N.g + N.q) / (N.g * N.p), (1) / (N.g * N.p),
            div_pos (by show 0 < -N.d * N.q + N.g * N.p + N.g * N.r - N.g + N.q; linarith [N.t0146])
            (by show 0 < N.g * N.p; linarith [mul_pos (N.hg) N.hp]),
            (div_lt_one (by show 0 < N.g * N.p; linarith [mul_pos (N.hg) N.hp])).mpr
            (by have := (by show 0 < N.d * N.q - N.g * N.r + N.g - N.q; linarith [hf03]); linarith),
            (div_pos (by norm_num : (0 : ℝ) < 1)
              (by show 0 < N.g * N.p; linarith [mul_pos (N.hg) N.hp])).ne', Or.inl ?_⟩
      refine eq_comb_div (ne_of_gt (by show 0 < N.g * N.p; linarith [mul_pos (N.hg) N.hp])) ?_
      simp only [NF16.vA, NF16.f03]; nf_simp N
      ext k
      simp only
          [nfP, nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
      ring
    · refine ⟨(N.g * N.p * N.q - N.g ^ 2 * N.p) / (N.g * N.p * N.q), (-N.g * N.p) /
            (N.g * N.p * N.q), div_pos (by
              show 0 < N.g * N.p * N.q - N.g ^ 2 * N.p
              linarith [mul_pos (hqg) (mul_pos (N.hg) N.hp)])
            (by show 0 < N.g * N.p * N.q; linarith [mul_pos (mul_pos (N.hg) N.hp) N.hq]),
            (div_lt_one (by show 0 < N.g * N.p * N.q; linarith [mul_pos (mul_pos (N.hg) N.hp) N.hq])).mpr
            (by
              have := (by show 0 < N.g ^ 2 * N.p; linarith [mul_pos (mul_pos (N.hg) N.hg) N.hp])
              linarith), (div_neg_of_neg_of_pos
              (by have := (by show 0 < N.g * N.p; linarith [mul_pos (N.hg) N.hp]); linarith)
              (by show 0 < N.g * N.p * N.q; linarith [mul_pos (mul_pos (N.hg) N.hp) N.hq])).ne,
            Or.inr (Or.inr (Or.inr ?_))⟩
      refine eq_comb_div
          (ne_of_gt (by show 0 < N.g * N.p * N.q; linarith [mul_pos (mul_pos (N.hg) N.hp) N.hq])) ?_
      simp only [NF16.vA, NF16.f03]; nf_simp N
      ext k
      simp only
          [nfP, nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
      ring
-- order: [6, 3, 5, 4]


/-- **Lemma 19.5, `T_c`, `T5 < 0`**: the closing `K_1` at `15`, rim `(1, 4, 0, 6)`. -/
theorem isRupert_T6_Tc4 (N : NF16 x) (hR1 : 0 < (N.g - 1) * (N.p + N.r) - N.d * (N.q - 1))
    (hR2 : 0 < N.a * (N.q - 1) - (N.b - 1) * (N.p + N.r)) (hD : 0 < N.q * N.d - N.r * N.g)
    (hqg : 0 < N.q - N.g) (hg1 : 0 < N.g - 1) (hqb : 0 < N.q - N.b)
    (hc : 0 < N.q * (N.a - 1) - N.b * (N.p - 1)) (hd1 : 0 < 1 - N.d)
    (hf03 : 0 < -(N.q * (1 - N.d) + N.g * (N.r - 1))) (hb1 : 0 < N.b - 1)
    (hHA : 0 < (N.b - 1) * N.g * N.p * N.r + (N.q * (1 - N.d) + N.g * (N.r - 1)) *
      (N.a * (N.q - 1) - (N.b - 1) * N.p)) (hf15 : 0 < N.d * N.q - (N.g - 1) * (N.p + N.r - 1))
    (hpr : 0 < N.p + N.r - 1)
    (hT5 : 0 < (N.g - 1) * (N.a - 1) * N.r - N.d * (N.q * (N.a - 1) - N.b * (N.p - 1)))
    (hz : IsCyclicUnimodal
          (quad ⟪x 1, (x 5 - x 1)⟫ ⟪x 4, (x 5 - x 1)⟫ ⟪x 0, (x 5 - x 1)⟫ ⟪x 6, (x 5 - x 1)⟫))
    (hnd : NoHDNAt ((univ.image x).erase (x 5)) (x 5 - x 1)) : IsRupert (univ.image x) := by
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  refine isRupert_equadσ (univ.image x) ({x 3} : Finset ℝ³) (u := (x 5 - x 1))
      (sub_ne_zero.mpr (N.inj.ne (by decide))) hσ (h := (-1 : ℝ)) (by norm_num) (by module)
      (mem_image 5)
    (mem_image 1) (mem_image 4) (mem_image 0) (mem_image 6)
    (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff])
        (by simp [N.inj.eq_iff]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hz hnd ?_
  · nf_test N hσD (by show 0 < N.d * N.p + N.d * N.q - N.g * N.r - N.d + N.r; linarith [N.t145_0])
  · nf_test N hσD (by show 0 < N.d * N.p + N.g * N.p - N.p; linarith [mul_pos (N.hgd) (N.hp)])
  · nf_test N hσD
        (by show 0 < N.d * N.q - N.g * N.p - N.g * N.r + N.g + N.p + N.r - 1; linarith [hf15])
  · nf_test N hσD (by show 0 < N.d * N.p + N.d * N.q - N.g * N.r - N.d + N.r; linarith [N.t145_0])
  · nf_test N hσD (by show 0 < N.d + N.g - 1; linarith [N.hgd])
  · nf_test N hσD
        (by show 0 < N.d * N.q - N.g * N.p - N.g * N.r + N.g + N.p + N.r - 1; linarith [hf15])
  · nf_test N hσD (by show 0 < N.d * N.p + N.g * N.p - N.p; linarith [mul_pos (N.hgd) (N.hp)])
  · nf_test N hσD (by show 0 < N.d + N.g - 1; linarith [N.hgd])
  · intro z hz hzM hn0 hn1 hn2 hn3 hn4
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    fin_cases i
    · exact absurd rfl hn3
    · exact absurd rfl hn1
    · refine ⟨?_, ?_, ?_, ?_⟩
      · nf_test N hσD (by
              show 0 < N.a * N.d * N.q - N.a * N.g * N.r - N.b * N.d * N.p - N.a * N.d + N.a * N.r +
                N.d * N.p
              linarith [N.tB125])
      · nf_test N hσD (by
              show 0 < -N.a * N.d * N.q + N.a * N.g * N.r + N.b * N.d * N.p - N.a * N.r - N.b * N.d
                + N.d * N.q - N.g * N.r + N.r
              linarith [hT5])
      · nf_test N hσD (pos_of_mul_pos_r (by
                show 0 < (2 / 7 : ℝ) * N.p + (2 / 7 : ℝ) * N.q + (2 / 7 : ℝ) * N.r - (2 / 7 : ℝ)
                linarith [hpr, N.hb, hR2, N.ha, hg1, N.t0246, hqg])
              (by
                show 0 < (-N.a * N.g + N.b * N.d + N.a + N.g - 1) *
                  ((2 / 7 : ℝ) * N.p + (2 / 7 : ℝ) * N.q + (2 / 7 : ℝ) * N.r - (2 / 7 : ℝ))
                linarith [mul_pos (N.hab) (hf15), mul_pos (N.hgd) (N.t0246)]))
      · nf_test N hσD (by show 0 < N.a * N.d + N.a * N.g - N.a; linarith [mul_pos (N.hgd) (N.ha)])
    · exact absurd (by simp) hzM
    · exact absurd rfl hn2
    · exact absurd rfl hn0
    · exact absurd rfl hn4
  · intro m hm
    rw [Finset.mem_singleton] at hm; subst hm
    · refine ⟨x 5, (N.g - 1) / (N.d + N.g - 1), (1) / (N.d + N.g - 1), Or.inr
            ⟨rfl, by have := div_pos (by norm_num : (0 : ℝ) < 1) (by show 0 < N.d + N.g - 1; linarith [N.hgd]); linarith⟩,
            div_pos (by show 0 < N.g - 1; linarith [hg1])
            (by show 0 < N.d + N.g - 1; linarith [N.hgd]),
            (div_lt_one (by show 0 < N.d + N.g - 1; linarith [N.hgd])).mpr
            (by have := (by show 0 < N.d; linarith [N.hd]); linarith),
            (div_pos (by norm_num : (0 : ℝ) < 1) (by show 0 < N.d + N.g - 1; linarith [N.hgd])).ne',
            Or.inr ?_⟩
      refine eq_comb_div (ne_of_gt (by show 0 < N.d + N.g - 1; linarith [N.hgd])) ?_
      nf_simp N
      ext k
      simp only
          [nfP, nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
      ring
-- order: [1, 4, 0, 6]


/-- **Lemma 19.4, `B`**: the closing `K_6` at `36`, rim `(6, 0, 2, 4, 1)`. -/
theorem isRupert_F1s_B (N : NF16 x) (hR1 : 0 < (N.g - 1) * (N.p + N.r) - N.d * (N.q - 1))
    (hR2 : 0 < N.a * (N.q - 1) - (N.b - 1) * (N.p + N.r)) (hD : 0 < N.q * N.d - N.r * N.g)
    (hqg : 0 < N.q - N.g) (hg1 : 0 < N.g - 1) (hqb : 0 < N.q - N.b)
    (hc : 0 < N.q * (N.a - 1) - N.b * (N.p - 1)) (hd1 : 0 < 1 - N.d)
    (hf03 : 0 < -(N.q * (1 - N.d) + N.g * (N.r - 1)))
    (hHA : 0 < -((N.b - 1) * N.g * N.p * N.r + (N.q * (1 - N.d) + N.g * (N.r - 1)) *
        (N.a * (N.q - 1) - (N.b - 1) * N.p)))
    (hz : IsCyclicUnimodal (quint ⟪x 6, (x 6 - x 3)⟫ ⟪x 0, (x 6 - x 3)⟫ ⟪x 2, (x 6 - x 3)⟫ ⟪x 4,
            (x 6 - x 3)⟫ ⟪x 1, (x 6 - x 3)⟫))
    (hnd : NoHDNAt ((univ.image x).erase (x 3)) (x 6 - x 3)) : IsRupert (univ.image x) := by
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  have h02 : 0 < N.a * N.g + N.b - N.g := by
    rcases le_or_gt N.a 1 with h | h
    · linarith [hc, mul_nonneg hqg.le (sub_nonneg.mpr h), mul_pos N.hb N.hp]
    · linarith [mul_pos N.hg (sub_pos.mpr h), N.hb]
  refine isRupert_equintσ (univ.image x) ({x 5} : Finset ℝ³) (u := (x 6 - x 3))
      (sub_ne_zero.mpr (N.inj.ne (by decide))) hσ (h := (1 : ℝ)) (by norm_num) (by module)
      (mem_image 3)
    (mem_image 6) (mem_image 0) (mem_image 2) (mem_image 4) (mem_image 1)
    (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff])
        (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff]) ?_ ?_ hz hnd ?_
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · nf_test N hσD (by show 0 < N.b; linarith [N.hb])
    · nf_test N hσD (by show 0 < N.q; linarith [N.hq])
    · nf_test N hσD (by show 0 < N.g; linarith [N.hg])
    · nf_test N hσD (by show 0 < N.a * N.q - N.b * N.p + N.b - N.q; linarith [hc])
    · nf_test N hσD (by show 0 < N.a * N.g + N.b - N.g; linarith [h02])
    · nf_test N hσD (by show 0 < N.b; linarith [N.hb])
    · nf_test N hσD (pos_of_mul_pos_r (by show 0 < (1 / 3 : ℝ) * N.q; linarith [hg1, hqg])
            (by
              show 0 < (-N.a * N.g + N.a * N.q - N.b * N.p + N.g * N.p) * ((1 / 3 : ℝ) * N.q)
              linarith [mul_pos (hqg) (hqb), mul_pos (hqb) (hf03), mul_pos (hqg) (hc), mul_pos
                  (N.t0146) (hqb)]))
    · nf_test N hσD (by show 0 < N.a * N.q - N.b * N.p; linarith [hc, hqb])
    · nf_test N hσD (by show 0 < N.a * N.q - N.b * N.p + N.b - N.q; linarith [hc])
    · nf_test N hσD (by show 0 < N.g * N.p; linarith [mul_pos (N.hg) N.hp])
    · nf_test N hσD (by show 0 < N.g * N.p - N.g + N.q; linarith [N.t0146, hD])
    · nf_test N hσD (pos_of_mul_pos_r (by show 0 < (1 / 3 : ℝ) * N.q; linarith [hg1, hqg])
            (by
              show 0 < (-N.a * N.g + N.a * N.q - N.b * N.p + N.g * N.p) * ((1 / 3 : ℝ) * N.q)
              linarith [mul_pos (hqg) (hqb), mul_pos (hqb) (hf03), mul_pos (hqg) (hc), mul_pos
                  (N.t0146) (hqb)]))
    · nf_test N hσD (by show 0 < N.g; linarith [N.hg])
    · nf_test N hσD (by show 0 < N.a * N.g; linarith [mul_pos (N.ha) N.hg])
    · nf_test N hσD (by show 0 < N.g * N.p; linarith [mul_pos (N.hg) N.hp])
  · intro z hz hzM hn0 hn1 hn2 hn3 hn4 hn5
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    fin_cases i
    · exact absurd rfl hn2
    · exact absurd rfl hn5
    · exact absurd rfl hn3
    · exact absurd rfl hn0
    · exact absurd rfl hn4
    · exact absurd (by simp) hzM
    · exact absurd rfl hn1
  · intro m hm
    rw [Finset.mem_singleton] at hm; subst hm
    · refine ⟨x 3, (N.g - 1) / (N.g), (-N.d) / (N.g), Or.inr
            ⟨rfl, by have := div_neg_of_neg_of_pos (show -N.d < 0 by have := (by show 0 < N.d; linarith [N.hd]); linarith) (by show 0 < N.g; linarith [N.hg]); linarith⟩,
            div_pos (by show 0 < N.g - 1; linarith [hg1]) (by show 0 < N.g; linarith [N.hg]),
            (div_lt_one (by show 0 < N.g; linarith [N.hg])).mpr
            (by have := (by norm_num : (0 : ℝ) < 1); linarith),
            (div_neg_of_neg_of_pos
              (show -N.d < 0 by have := (by show 0 < N.d; linarith [N.hd]); linarith)
              (by show 0 < N.g; linarith [N.hg])).ne, Or.inr ?_⟩
      refine eq_comb_div (ne_of_gt (by show 0 < N.g; linarith [N.hg])) ?_
      nf_simp N
      ext k
      simp only
          [nfP, nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
      ring
-- order: [6, 0, 2, 4, 1]


/-- The depth pattern of `B` (§19.4 (iii), (iv)): the pentagon `(6, 0, 2, 4, 1)` is unimodal if
`z0 < z6`, `1` is not a strict local minimum, and not `z2 > z0, z4` (the identity
`c36 (z6 − z0) + (q − b)(z2 − z0) + b (z2 − z4) < 0` excludes it when `z6 > z0`). -/
theorem quint_B_unimodal {z6 z0 z2 z4 z1 : ℝ} (hinj : Function.Injective (quint z6 z0 z2 z4 z1))
    (h60 : z0 < z6) (h1 : ¬ (z1 < z4 ∧ z1 < z6)) (P : z0 < z2 → z4 < z2 → False) :
    IsCyclicUnimodal (quint z6 z0 z2 z4 z1) := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := zmod5_add_one
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_sub_one
  refine unimodal5_tac hinj fun i j hi hj => ?_
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
  simp only [a0, a1, a2, a3, a4, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3,
    quint_4] at hi hj <;>
  first
  | rfl
  | (exfalso; linarith [hi.1, hi.2, hj.1, hj.2])
  | (exfalso; exact P (by linarith [hi.1, hi.2, hj.1, hj.2]) (by linarith [hi.1, hi.2, hj.1, hj.2]))
  | (exfalso; exact h1 ⟨by linarith [hi.1, hi.2, hj.1, hj.2], by linarith [hi.1, hi.2, hj.1, hj.2]⟩)

/-- **Lemma 19.4** (`Ω ∩ {d < 1}` with `H_A < 0`): the vertex crossing `A = 036/146` at `6`
(view `v_A`, rim `(6, 3, 5, 4)`) or the closing `B = K_6` at `36` (rim `(6, 0, 2, 4, 1)`) is
unimodal.  `A` fails only with `{4, 3}` above `{6, 5}` (crossing with `λ_A < 0`), so then
`⟪v_A, 6 − 3⟫ < 0`; if `⟪v_A, 6 − 3⟫ ≤ 0`, then `z0 < z6`, `1` is not a strict local minimum, and
the identity of (iii) leaves no two-peaked pattern for `B`. -/
theorem isRupert_F1s (N : NF16 x) (O : Omega N) (hd1 : 0 < 1 - N.d)
    (hf03 : 0 < -(N.q * (1 - N.d) + N.g * (N.r - 1)))
    (hHA : 0 < -((N.b - 1) * N.g * N.p * N.r + (N.q * (1 - N.d) + N.g * (N.r - 1)) *
      (N.a * (N.q - 1) - (N.b - 1) * N.p)))
    (hg : GenPos (univ.image x)) (hnd : NoHDNEdges16 x)
    (hv : [⟪x 6, N.vA⟫, ⟪x 3, N.vA⟫, ⟪x 5, N.vA⟫, ⟪x 4, N.vA⟫].Nodup)
    (hndv : NoHDNAt (univ.image x) N.vA) : IsRupert (univ.image x) := by
  obtain ⟨hR1, hR2, hD, hqg, hg1, hqb, hc, -, -, -, -, -⟩ := O
  have he3 : 0 < ⟪x 6 - x 3, x 6 - x 3⟫ :=
    real_inner_self_pos.mpr (sub_ne_zero.mpr (N.inj.ne (by decide)))
  have he3' : 0 < ⟪x 6, x 6 - x 3⟫ - ⟪x 3, x 6 - x 3⟫ := by rw [← inner_sub_left]; exact he3
  by_cases hs : ⟪x 6 - x 3, N.vA⟫ ≤ 0
  · -- `B` is unimodal
    have e1 := congrArg (fun w => ⟪w, x 6 - x 3⟫) N.vA_eq
    have e2 := congrArg (fun w => ⟪w, x 6 - x 3⟫) N.vA_eq'
    have iden : N.c36v • (x 6 - x 0) + (N.q - N.b) • (x 2 - x 0) + N.b • (x 2 - x 4) =
        (-N.t0246v) • (x 6 - x 3) := by
      simp only [c36v, t0246v]
      nf_simp N
      ext k
      simp only [nfP, nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply,
        smul_eq_mul]
      ring
    have e3 := congrArg (fun w => ⟪w, x 6 - x 3⟫) iden
    simp only [inner_add_left, inner_sub_left, real_inner_smul_left, inner_neg_left] at e1 e2 e3
    rw [real_inner_comm] at hs
    have hgp : 0 < N.g * N.p := mul_pos N.hg N.hp
    have ht := N.t0146
    have ht2 := N.t0246
    simp only [t0146v, t0246v, c36v] at e1 e2 e3
    have hz := fun i j (hij : i ≠ j) (hh : (j ≠ 3 ∧ j ≠ 6) ∨ (i ≠ 6 ∧ j ≠ 6)) =>
      depth_ne (v := 3) (w := 6) N.inj hg hij (by decide) hh
    refine isRupert_F1s_B N hR1 hR2 hD hqg hg1 hqb hc hd1 hf03 hHA
      (quint_B_unimodal (quint_injective (hz 6 0 (by decide) (by decide))
        (hz 6 2 (by decide) (by decide)) (hz 6 4 (by decide) (by decide))
        (hz 6 1 (by decide) (by decide)) (hz 0 2 (by decide) (by decide))
        (hz 0 4 (by decide) (by decide)) (hz 0 1 (by decide) (by decide))
        (hz 2 4 (by decide) (by decide)) (hz 2 1 (by decide) (by decide))
        (hz 4 1 (by decide) (by decide))) ?_ ?_ ?_) (hnd.bwd N (by decide))
    · nlinarith [mul_pos ht he3']
    · rintro ⟨h14, h16⟩
      nlinarith [mul_pos hqg (sub_pos.mpr h16), mul_pos N.hg (sub_pos.mpr h14)]
    · intro h02 h42
      have h60 : ⟪x 0, x 6 - x 3⟫ < ⟪x 6, x 6 - x 3⟫ := by nlinarith [mul_pos ht he3']
      nlinarith [mul_pos hc (sub_pos.mpr h60), mul_pos hqb (sub_pos.mpr h02),
        mul_pos N.hb (sub_pos.mpr h42), mul_pos ht2 he3']
  · -- `A` is unimodal
    push Not at hs
    have K0 : 0 < N.q * (N.g + N.d - 1) + N.g := by nlinarith [mul_pos N.hq N.hgd]
    refine isRupert_F1s_A N hR1 hR2 hD hqg hg1 hqb hc hd1 hf03 hHA (quad_unimodal ?_ hv) hndv
    intro hA
    have hA' : DepthSep (x 4) (x 3) (x 6) (x 5) N.vA := by
      simp only [DepthSep, max_comm, min_comm] at hA ⊢; tauto
    have hs2 := depthSep_of_meet (d₀ := x 4) (d₁ := x 3) (e₀ := x 6) (e₁ := x 5) (w := N.vA)
      (s := N.q * (N.g + N.d - 1) / (N.q * (N.g + N.d - 1) + N.g))
      (t := N.g * N.q / (N.q * (N.g + N.d - 1) + N.g))
      (l := -1 / (N.q * (N.g + N.d - 1) + N.g))
      (div_pos (mul_pos N.hq N.hgd) K0).le ((div_le_one K0).mpr (by linarith [N.hg]))
      (div_pos (mul_pos N.hg N.hq) K0).le
          ((div_le_one K0).mpr (by nlinarith [hf03, mul_pos N.hg N.hr]))
      ?_ (div_nonpos_of_nonpos_of_nonneg (by norm_num) K0.le) hA'
    · have k1 := max_lt_iff.mp hs2
      have k2 := lt_min_iff.mp k1.1
      rw [inner_sub_left] at hs
      linarith [k2.2]
    · have K0' := K0.ne'
      simp only [vA, f03]
      nf_simp N
      ext k
      simp only [nfP, nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply,
        smul_eq_mul]
      field_simp
      ring


/-- **Lemma 19.5, `T_a`**: the vertex crossing `0235/046` at `0` (view `uA`), rim `(0, 6, 1, 5)`. -/
theorem isRupert_T6_Ta (N : NF16 x) (hR1 : 0 < (N.g - 1) * (N.p + N.r) - N.d * (N.q - 1))
    (hR2 : 0 < N.a * (N.q - 1) - (N.b - 1) * (N.p + N.r)) (hD : 0 < N.q * N.d - N.r * N.g)
    (hqg : 0 < N.q - N.g) (hg1 : 0 < N.g - 1) (hqb : 0 < N.q - N.b)
    (hc : 0 < N.q * (N.a - 1) - N.b * (N.p - 1)) (hd1 : 0 < 1 - N.d)
    (hf03 : 0 < -(N.q * (1 - N.d) + N.g * (N.r - 1))) (hb1 : 0 < N.b - 1)
    (hHA : 0 < (N.b - 1) * N.g * N.p * N.r + (N.q * (1 - N.d) + N.g * (N.r - 1)) *
      (N.a * (N.q - 1) - (N.b - 1) * N.p)) (hf15 : 0 < N.d * N.q - (N.g - 1) * (N.p + N.r - 1))
    (hpr : 0 < N.p + N.r - 1)
    (hz : IsCyclicUnimodal (quad ⟪x 0, N.uA⟫ ⟪x 5, N.uA⟫ ⟪x 1, N.uA⟫ ⟪x 6, N.uA⟫))
    (hnd : NoHDNAt (univ.image x) N.uA) : IsRupert (univ.image x) := by
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  have hr1 : 0 < -N.r + 1 := by
    by_contra hc; push Not at hc
    nlinarith [mul_pos N.hq hd1, mul_nonpos_of_nonneg_of_nonpos N.hg.le hc]
  refine isRupert_vquadσ (univ.image x) ({x 2, x 3, x 4} : Finset ℝ³) (u := N.uA)
      (by
        simp only [NF16.uA]
        exact nfV_ne_zero N.hD
          (Or.inl (ne_of_gt (by have := (by show 0 < N.p + N.r - 1; linarith [hpr]); linarith)))) hσ
    (mem_image 0) (mem_image 5) (mem_image 1) (mem_image 6)
    (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff])
        (by simp [N.inj.eq_iff]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hz hnd ?_
  · simp only [NF16.uA]; nf_test N hσD
        (by show 0 < N.d * N.p + N.d * N.q + N.d * N.r - N.d; linarith [mul_pos (N.t046_5) (N.hd)])
  · simp only [NF16.uA]; nf_test N hσD (by show 0 < N.p + N.q + N.r - 1; linarith [N.t046_5])
  · simp only [NF16.uA]; nf_test N hσD (by
          show 0 < N.d * N.p + N.d * N.r + N.g * N.p + N.g * N.r - N.d - N.g - N.p - N.r + 1
          linarith [mul_pos (N.hgd) (hpr)])
  · simp only [NF16.uA]; nf_test N hσD
        (by show 0 < N.d * N.p + N.d * N.q + N.d * N.r - N.d; linarith [mul_pos (N.t046_5) (N.hd)])
  · simp only [NF16.uA]; nf_test N hσD
        (by show 0 < -N.d * N.q + N.g * N.p + N.g * N.r - N.g + N.q; linarith [N.t0146])
  · simp only [NF16.uA]; nf_test N hσD (by
          show 0 < N.d * N.p + N.d * N.r + N.g * N.p + N.g * N.r - N.d - N.g - N.p - N.r + 1
          linarith [mul_pos (N.hgd) (hpr)])
  · simp only [NF16.uA]; nf_test N hσD (by show 0 < N.p + N.q + N.r - 1; linarith [N.t046_5])
  · simp only [NF16.uA]; nf_test N hσD
        (by show 0 < -N.d * N.q + N.g * N.p + N.g * N.r - N.g + N.q; linarith [N.t0146])
  · intro z hz hzM hn0 hn1 hn2 hn3
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    fin_cases i
    · exact absurd rfl hn0
    · exact absurd rfl hn2
    · exact absurd (by simp) hzM
    · exact absurd (by simp) hzM
    · exact absurd (by simp) hzM
    · exact absurd rfl hn1
    · exact absurd rfl hn3
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl
    · refine ⟨(-N.a * N.q + N.b * N.p + N.b * N.r - N.b + N.q) / (N.p + N.q + N.r - 1),
            (N.a + N.b - 1) / (N.p + N.q + N.r - 1), div_pos
            (by show 0 < -N.a * N.q + N.b * N.p + N.b * N.r - N.b + N.q; linarith [N.t0246])
            (by show 0 < N.p + N.q + N.r - 1; linarith [N.t046_5]),
            (div_lt_one (by show 0 < N.p + N.q + N.r - 1; linarith [N.t046_5])).mpr
            (by
              have := (by
                  show 0 < N.a * N.q - N.b * N.p - N.b * N.r + N.b + N.p + N.r - 1
                  linarith [hc, hqg, hpr, mul_pos (hr1) (N.hb), hg1, hR2, N.ha])
              linarith), (div_pos (by show 0 < N.a + N.b - 1; linarith [N.hab])
              (by show 0 < N.p + N.q + N.r - 1; linarith [N.t046_5])).ne', Or.inl ?_⟩
      refine eq_comb_div (ne_of_gt (by show 0 < N.p + N.q + N.r - 1; linarith [N.t046_5])) ?_
      simp only [NF16.uA]; nf_simp N
      ext k
      simp only
          [nfP, nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
      ring
    · refine ⟨(N.q) / (N.p + N.q + N.r - 1), (-1) / (N.p + N.q + N.r - 1), div_pos
            (by show 0 < N.q; linarith [N.hq])
            (by show 0 < N.p + N.q + N.r - 1; linarith [N.t046_5]),
            (div_lt_one (by show 0 < N.p + N.q + N.r - 1; linarith [N.t046_5])).mpr
            (by have := (by show 0 < N.p + N.r - 1; linarith [hpr]); linarith),
            (div_neg_of_neg_of_pos (by have := (by norm_num : (0 : ℝ) < 1); linarith)
              (by show 0 < N.p + N.q + N.r - 1; linarith [N.t046_5])).ne, Or.inl ?_⟩
      refine eq_comb_div (ne_of_gt (by show 0 < N.p + N.q + N.r - 1; linarith [N.t046_5])) ?_
      simp only [NF16.uA]; nf_simp N
      ext k
      simp only
          [nfP, nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
      ring
    · refine ⟨(-N.q * N.r + N.q) / (N.q), (N.q) / (N.q), div_pos
            (by show 0 < -N.q * N.r + N.q; linarith [mul_pos (hr1) (N.hq)])
            (by show 0 < N.q; linarith [N.hq]), (div_lt_one (by show 0 < N.q; linarith [N.hq])).mpr
            (by have := (by show 0 < N.q * N.r; linarith [mul_pos (N.hq) N.hr]); linarith),
            (div_pos (by show 0 < N.q; linarith [N.hq]) (by show 0 < N.q; linarith [N.hq])).ne',
            Or.inr (Or.inr (Or.inr ?_))⟩
      refine eq_comb_div (ne_of_gt (by show 0 < N.q; linarith [N.hq])) ?_
      simp only [NF16.uA]; nf_simp N
      ext k
      simp only
          [nfP, nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
      ring
-- order: [0, 5, 1, 6]


/-- **Lemma 19.5, `A`**: the vertex crossing `036/146` at `6` (view `vA`), rim `(6, 4, 2, 5, 3)`
(`H_A > 0`). -/
theorem isRupert_T6_A (N : NF16 x) (hR1 : 0 < (N.g - 1) * (N.p + N.r) - N.d * (N.q - 1))
    (hR2 : 0 < N.a * (N.q - 1) - (N.b - 1) * (N.p + N.r)) (hD : 0 < N.q * N.d - N.r * N.g)
    (hqg : 0 < N.q - N.g) (hg1 : 0 < N.g - 1) (hqb : 0 < N.q - N.b)
    (hc : 0 < N.q * (N.a - 1) - N.b * (N.p - 1)) (hd1 : 0 < 1 - N.d)
    (hf03 : 0 < -(N.q * (1 - N.d) + N.g * (N.r - 1))) (hb1 : 0 < N.b - 1)
    (hHA : 0 < (N.b - 1) * N.g * N.p * N.r + (N.q * (1 - N.d) + N.g * (N.r - 1)) *
      (N.a * (N.q - 1) - (N.b - 1) * N.p)) (hf15 : 0 < N.d * N.q - (N.g - 1) * (N.p + N.r - 1))
    (hpr : 0 < N.p + N.r - 1)
    (hz : IsCyclicUnimodal (quint ⟪x 6, N.vA⟫ ⟪x 3, N.vA⟫ ⟪x 5, N.vA⟫ ⟪x 2, N.vA⟫ ⟪x 4, N.vA⟫))
    (hnd : NoHDNAt (univ.image x) N.vA) : IsRupert (univ.image x) := by
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  have hga : 0 < -N.a * N.d * N.q ^ 2 + N.a * N.g * N.q * N.r + N.b * N.d * N.p * N.q - N.a * N.g *
      N.q + N.a * N.q ^ 2 - N.b * N.d * N.q + N.b * N.g * N.p + N.b * N.g * N.r - N.b * N.p * N.q +
      N.d * N.q ^ 2 - N.g * N.q * N.r - N.b * N.g + N.b * N.q + N.g * N.q - N.q ^ 2 :=
      by linarith [mul_pos (mul_pos N.hg N.hp) N.t0246, mul_pos N.t0146 hc]
  have h243 : 0 < -N.a * N.d * N.q ^ 2 + N.a * N.g * N.q * N.r + N.b * N.d * N.p * N.q - N.a * N.g *
      N.q + N.a * N.q ^ 2 + N.b * N.g * N.p - N.b * N.p * N.q := pos_of_mul_pos_r N.hab
      (by linarith [mul_pos N.hb hHA, mul_pos N.ha hga])
  refine isRupert_vquintσ (univ.image x) ({x 0, x 1} : Finset ℝ³) (u := N.vA)
      (by
        simp only [NF16.vA, NF16.f03]
        exact nfV_ne_zero N.hD (Or.inl (ne_of_gt
              (by have := (by show 0 < N.g * N.p; linarith [mul_pos (N.hg) N.hp]); linarith)))) hσ
    (mem_image 6) (mem_image 3) (mem_image 5) (mem_image 2) (mem_image 4)
    (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff])
        (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff]) ?_ ?_ hz hnd ?_
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [NF16.vA, NF16.f03]; nf_test N hσD
          (by show 0 < N.g * N.p; linarith [mul_pos (N.hg) N.hp])
    · simp only [NF16.vA, NF16.f03]; nf_test N hσD
          (by show 0 < N.b * N.g * N.p; linarith [mul_pos (mul_pos (N.hb) N.hg) N.hp])
    · simp only [NF16.vA, NF16.f03]; nf_test N hσD
          (by show 0 < N.g * N.p * N.q; linarith [mul_pos (mul_pos (N.hg) N.hp) N.hq])
    · simp only [NF16.vA, NF16.f03]; nf_test N hσD
          (by
            show 0 < N.a * N.d * N.q - N.a * N.g * N.r + N.a * N.g - N.a * N.q
            linarith [mul_pos (hf03) (N.ha)])
    · simp only [NF16.vA, NF16.f03]; nf_test N hσD
          (by
            show 0 < N.d * N.p * N.q + N.g * N.p - N.p * N.q
            linarith [mul_pos (hd1) (N.hr), mul_pos (hf03) (N.hp), mul_pos (hpr) (N.hr), mul_pos
                (hR1) (N.hr), mul_pos (hD) (N.hr)])
    · simp only [NF16.vA, NF16.f03]; nf_test N hσD
          (by show 0 < N.g * N.p; linarith [mul_pos (N.hg) N.hp])
    · simp only [NF16.vA, NF16.f03]; nf_test N hσD
          (by
            show 0 < -N.a * N.d * N.q ^ 2 + N.a * N.g * N.q * N.r + N.b * N.d * N.p * N.q + N.a *
              N.d * N.q - N.a * N.g * N.q - N.a * N.g * N.r + N.a * N.q ^ 2 + N.b * N.g * N.p - N.b
              * N.p * N.q - N.d * N.p * N.q + N.a * N.g - N.a * N.q - N.g * N.p + N.p * N.q
            linarith [hHA])
    · simp only [NF16.vA, NF16.f03]; nf_test N hσD
          (by
            show 0 < N.a * N.d * N.q - N.a * N.g * N.r + N.b * N.g * N.p + N.a * N.g - N.a * N.q -
              N.g * N.p
            linarith [mul_pos (hb1) (mul_pos (N.hg) N.hp), mul_pos (hf03) (N.ha)])
    · simp only [NF16.vA, NF16.f03]; nf_test N hσD
          (by
            show 0 < N.a * N.d * N.q - N.a * N.g * N.r + N.a * N.g - N.a * N.q
            linarith [mul_pos (hf03) (N.ha)])
    · simp only [NF16.vA, NF16.f03]; nf_test N hσD
          (by
            show 0 < -N.a * N.d * N.q ^ 2 + N.a * N.g * N.q * N.r + N.b * N.d * N.p * N.q - N.a *
              N.g * N.q + N.a * N.q ^ 2 - N.b * N.p * N.q + N.g * N.p * N.q
            linarith [mul_pos (N.t146_2) (N.hq)])
    · simp only [NF16.vA, NF16.f03]; nf_test N hσD
          (by
            show 0 < -N.a * N.d * N.q ^ 2 + N.a * N.g * N.q * N.r + N.b * N.d * N.p * N.q - N.a *
              N.g * N.q + N.a * N.q ^ 2 + N.b * N.g * N.p - N.b * N.p * N.q
            linarith [h243])
    · simp only [NF16.vA, NF16.f03]; nf_test N hσD
          (by
            show 0 < -N.a * N.d * N.q ^ 2 + N.a * N.g * N.q * N.r + N.b * N.d * N.p * N.q + N.a *
              N.d * N.q - N.a * N.g * N.q - N.a * N.g * N.r + N.a * N.q ^ 2 + N.b * N.g * N.p - N.b
              * N.p * N.q - N.d * N.p * N.q + N.a * N.g - N.a * N.q - N.g * N.p + N.p * N.q
            linarith [hHA])
    · simp only [NF16.vA, NF16.f03]; nf_test N hσD
          (by show 0 < N.g * N.p * N.q; linarith [mul_pos (mul_pos (N.hg) N.hp) N.hq])
    · simp only [NF16.vA, NF16.f03]; nf_test N hσD
          (by
            show 0 < N.d * N.p * N.q + N.g * N.p * N.q - N.p * N.q
            linarith [mul_pos (N.hgd) (mul_pos (N.hp) N.hq)])
    · simp only [NF16.vA, NF16.f03]; nf_test N hσD
          (by
            show 0 < -N.a * N.d * N.q ^ 2 + N.a * N.g * N.q * N.r + N.b * N.d * N.p * N.q - N.a *
              N.g * N.q + N.a * N.q ^ 2 - N.b * N.p * N.q + N.g * N.p * N.q
            linarith [mul_pos (N.t146_2) (N.hq)])
  · intro z hz hzM hn0 hn1 hn2 hn3 hn4
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    fin_cases i
    · exact absurd (by simp) hzM
    · exact absurd (by simp) hzM
    · exact absurd rfl hn3
    · exact absurd rfl hn1
    · exact absurd rfl hn4
    · exact absurd rfl hn2
    · exact absurd rfl hn0
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · refine ⟨(-N.d * N.q + N.g * N.p + N.g * N.r - N.g + N.q) / (N.g * N.p), (1) / (N.g * N.p),
            div_pos (by show 0 < -N.d * N.q + N.g * N.p + N.g * N.r - N.g + N.q; linarith [N.t0146])
            (by show 0 < N.g * N.p; linarith [mul_pos (N.hg) N.hp]),
            (div_lt_one (by show 0 < N.g * N.p; linarith [mul_pos (N.hg) N.hp])).mpr
            (by have := (by show 0 < N.d * N.q - N.g * N.r + N.g - N.q; linarith [hf03]); linarith),
            (div_pos (by norm_num : (0 : ℝ) < 1)
              (by show 0 < N.g * N.p; linarith [mul_pos (N.hg) N.hp])).ne', Or.inl ?_⟩
      refine eq_comb_div (ne_of_gt (by show 0 < N.g * N.p; linarith [mul_pos (N.hg) N.hp])) ?_
      simp only [NF16.vA, NF16.f03]; nf_simp N
      ext k
      simp only
          [nfP, nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
      ring
    · refine ⟨(N.g * N.p * N.q - N.g ^ 2 * N.p) / (N.g * N.p * N.q), (-N.g * N.p) /
            (N.g * N.p * N.q), div_pos (by
              show 0 < N.g * N.p * N.q - N.g ^ 2 * N.p
              linarith [mul_pos (hqg) (mul_pos (N.hg) N.hp)])
            (by show 0 < N.g * N.p * N.q; linarith [mul_pos (mul_pos (N.hg) N.hp) N.hq]),
            (div_lt_one (by show 0 < N.g * N.p * N.q; linarith [mul_pos (mul_pos (N.hg) N.hp) N.hq])).mpr
            (by
              have := (by show 0 < N.g ^ 2 * N.p; linarith [mul_pos (mul_pos (N.hg) N.hg) N.hp])
              linarith), (div_neg_of_neg_of_pos
              (show -N.g * N.p < 0
                by have := (by show 0 < N.g * N.p; linarith [mul_pos (N.hg) N.hp]); linarith)
              (by show 0 < N.g * N.p * N.q; linarith [mul_pos (mul_pos (N.hg) N.hp) N.hq])).ne,
            Or.inr (Or.inr (Or.inr (Or.inr ?_)))⟩
      refine eq_comb_div
          (ne_of_gt (by show 0 < N.g * N.p * N.q; linarith [mul_pos (mul_pos (N.hg) N.hp) N.hq])) ?_
      simp only [NF16.vA, NF16.f03]; nf_simp N
      ext k
      simp only
          [nfP, nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
      ring
-- order: [6, 3, 5, 2, 4]


/-- **Lemma 19.5, `T_c`, `T5 > 0`**: the closing `K_1` at `15`, rim `(1, 4, 2, 0, 6)`. -/
theorem isRupert_T6_Tc5 (N : NF16 x) (hR1 : 0 < (N.g - 1) * (N.p + N.r) - N.d * (N.q - 1))
    (hR2 : 0 < N.a * (N.q - 1) - (N.b - 1) * (N.p + N.r)) (hD : 0 < N.q * N.d - N.r * N.g)
    (hqg : 0 < N.q - N.g) (hg1 : 0 < N.g - 1) (hqb : 0 < N.q - N.b)
    (hc : 0 < N.q * (N.a - 1) - N.b * (N.p - 1)) (hd1 : 0 < 1 - N.d)
    (hf03 : 0 < -(N.q * (1 - N.d) + N.g * (N.r - 1))) (hb1 : 0 < N.b - 1)
    (hHA : 0 < (N.b - 1) * N.g * N.p * N.r + (N.q * (1 - N.d) + N.g * (N.r - 1)) *
      (N.a * (N.q - 1) - (N.b - 1) * N.p)) (hf15 : 0 < N.d * N.q - (N.g - 1) * (N.p + N.r - 1))
    (hpr : 0 < N.p + N.r - 1)
    (hT5 : 0 < N.d * (N.q * (N.a - 1) - N.b * (N.p - 1)) - (N.g - 1) * (N.a - 1) * N.r)
    (hz : IsCyclicUnimodal (quint ⟪x 1, (x 5 - x 1)⟫ ⟪x 4, (x 5 - x 1)⟫ ⟪x 2, (x 5 - x 1)⟫ ⟪x 0,
            (x 5 - x 1)⟫ ⟪x 6, (x 5 - x 1)⟫))
    (hnd : NoHDNAt ((univ.image x).erase (x 5)) (x 5 - x 1)) : IsRupert (univ.image x) := by
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  have h426 : 0 < N.a * N.d * N.q - N.a * N.g * N.r - N.b * N.d * N.p + N.a * N.g + N.a * N.r - N.g
      * N.p - N.a + N.p := pos_of_mul_pos_r (mul_pos N.hr N.hab)
      (by linarith [mul_pos N.tB125 N.t0246, mul_pos hT5 N.t245_6])
  refine isRupert_equintσ (univ.image x) ({x 3} : Finset ℝ³) (u := (x 5 - x 1))
      (sub_ne_zero.mpr (N.inj.ne (by decide))) hσ (h := (-1 : ℝ)) (by norm_num) (by module)
      (mem_image 5)
    (mem_image 1) (mem_image 4) (mem_image 2) (mem_image 0) (mem_image 6)
    (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff])
        (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff]) ?_ ?_ hz hnd ?_
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · nf_test N hσD (by
            show 0 < N.a * N.d * N.q - N.a * N.g * N.r - N.b * N.d * N.p - N.a * N.d + N.a * N.r +
              N.d * N.p
            linarith [N.tB125])
    · nf_test N hσD (by show 0 < N.d * N.p + N.d * N.q - N.g * N.r - N.d + N.r; linarith [N.t145_0])
    · nf_test N hσD (by show 0 < N.d * N.p + N.g * N.p - N.p; linarith [mul_pos (N.hgd) (N.hp)])
    · nf_test N hσD (by
            show 0 < N.a * N.d * N.q - N.a * N.g * N.r - N.b * N.d * N.p + N.a * N.r + N.b * N.d -
              N.d * N.q + N.g * N.r - N.r
            linarith [hT5])
    · nf_test N hσD (by
            show 0 < N.a * N.d * N.q - N.a * N.g * N.r - N.b * N.d * N.p + N.a * N.g + N.a * N.r -
              N.g * N.p - N.a + N.p
            linarith [h426])
    · nf_test N hσD (by
            show 0 < N.a * N.d * N.q - N.a * N.g * N.r - N.b * N.d * N.p - N.a * N.d + N.a * N.r +
              N.d * N.p
            linarith [N.tB125])
    · nf_test N hσD (pos_of_mul_pos_r (by
              show 0 < (1 / 6 : ℝ) * N.b * N.r + (1 / 6 : ℝ) * N.q
              linarith [hR1, hc, hd1, hqg, N.t0246, hf15])
            (by
              show 0 < (-N.a * N.g + N.b * N.d + N.a + N.g - 1) *
                ((1 / 6 : ℝ) * N.b * N.r + (1 / 6 : ℝ) * N.q)
              linarith [mul_pos (N.t0246) (hR1), mul_pos (hf15) (N.hb), mul_pos (hT5) (N.hb),
                  mul_pos (mul_pos (N.t0246) (hb1)) (N.hd), mul_pos (N.t0246) (hf15)]))
    · nf_test N hσD (by show 0 < N.a * N.d + N.b * N.d - N.d; linarith [mul_pos (N.hab) (N.hd)])
    · nf_test N hσD (by
            show 0 < N.a * N.d * N.q - N.a * N.g * N.r - N.b * N.d * N.p + N.a * N.r + N.b * N.d -
              N.d * N.q + N.g * N.r - N.r
            linarith [hT5])
    · nf_test N hσD (by show 0 < N.d + N.g - 1; linarith [N.hgd])
    · nf_test N hσD
          (by show 0 < N.d * N.q - N.g * N.p - N.g * N.r + N.g + N.p + N.r - 1; linarith [hf15])
    · nf_test N hσD (pos_of_mul_pos_r (by
              show 0 < (1 / 6 : ℝ) * N.b * N.r + (1 / 6 : ℝ) * N.q
              linarith [hR1, hc, hd1, hqg, N.t0246, hf15])
            (by
              show 0 < (-N.a * N.g + N.b * N.d + N.a + N.g - 1) *
                ((1 / 6 : ℝ) * N.b * N.r + (1 / 6 : ℝ) * N.q)
              linarith [mul_pos (N.t0246) (hR1), mul_pos (hf15) (N.hb), mul_pos (hT5) (N.hb),
                  mul_pos (mul_pos (N.t0246) (hb1)) (N.hd), mul_pos (N.t0246) (hf15)]))
    · nf_test N hσD (by show 0 < N.d * N.p + N.g * N.p - N.p; linarith [mul_pos (N.hgd) (N.hp)])
    · nf_test N hσD (by show 0 < N.a * N.d + N.a * N.g - N.a; linarith [mul_pos (N.hgd) (N.ha)])
    · nf_test N hσD (by show 0 < N.d + N.g - 1; linarith [N.hgd])
  · intro z hz hzM hn0 hn1 hn2 hn3 hn4 hn5
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    fin_cases i
    · exact absurd rfl hn4
    · exact absurd rfl hn1
    · exact absurd rfl hn3
    · exact absurd (by simp) hzM
    · exact absurd rfl hn2
    · exact absurd rfl hn0
    · exact absurd rfl hn5
  · intro m hm
    rw [Finset.mem_singleton] at hm; subst hm
    · refine ⟨x 5, (N.g - 1) / (N.d + N.g - 1), (1) / (N.d + N.g - 1), Or.inr
            ⟨rfl, by have := div_pos (by norm_num : (0 : ℝ) < 1) (by show 0 < N.d + N.g - 1; linarith [N.hgd]); linarith⟩,
            div_pos (by show 0 < N.g - 1; linarith [hg1])
            (by show 0 < N.d + N.g - 1; linarith [N.hgd]),
            (div_lt_one (by show 0 < N.d + N.g - 1; linarith [N.hgd])).mpr
            (by have := (by show 0 < N.d; linarith [N.hd]); linarith),
            (div_pos (by norm_num : (0 : ℝ) < 1) (by show 0 < N.d + N.g - 1; linarith [N.hgd])).ne',
            Or.inr ?_⟩
      refine eq_comb_div (ne_of_gt (by show 0 < N.d + N.g - 1; linarith [N.hgd])) ?_
      nf_simp N
      ext k
      simp only
          [nfP, nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
      ring
-- order: [1, 4, 2, 0, 6]



/-! ### Lemma 19.5: the triple `T6` on `Ω_open` -/

theorem depthSep_sign {d₀ d₁ e₀ e₁ w v : ℝ³} {s t l : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hm : (e₀ + t • (e₁ - e₀)) - (d₀ + s • (d₁ - d₀)) = l • v)
    (h : max ⟪e₀, w⟫ ⟪e₁, w⟫ < min ⟪d₀, w⟫ ⟪d₁, w⟫) : l * ⟪v, w⟫ < 0 := by
  have i1 := congrArg (fun z => ⟪z, w⟫) hm
  simp only [inner_sub_left, inner_seg, real_inner_smul_left] at i1
  obtain ⟨e1, e2⟩ := seg_bounds (x := ⟪e₀, w⟫) (y := ⟪e₁, w⟫) ht0 ht1
  obtain ⟨d1, d2⟩ := seg_bounds (x := ⟪d₀, w⟫) (y := ⟪d₁, w⟫) hs0 hs1
  linarith

theorem cone_inner3 {T v₁ v₂ v₃ w : ℝ³} {D n₁ n₂ n₃ : ℝ}
    (h : D • T = n₁ • v₁ + n₂ • v₂ + n₃ • v₃) :
    D * ⟪T, w⟫ = n₁ * ⟪v₁, w⟫ + n₂ * ⟪v₂, w⟫ + n₃ * ⟪v₃, w⟫ := by
  have := congrArg (fun z => ⟪z, w⟫) h
  simpa only [inner_add_left, real_inner_smul_left] using this

theorem quint_inj_of_nodup {z₀ z₁ z₂ z₃ z₄ : ℝ} (h : [z₀, z₁, z₂, z₃, z₄].Nodup) :
    Function.Injective (quint z₀ z₁ z₂ z₃ z₄) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at h
  obtain ⟨⟨h1, h2, h3, h4⟩, ⟨h5, h6, h7⟩, ⟨h8, h9⟩, h10, -⟩ := h
  exact quint_injective h1 h2 h3 h4 h5 h6 h7 h8 h9 h10

/-- The depth pattern of `T_c` with five corners (§19.5): the pentagon `(1, 4, 2, 0, 6)` is
unimodal if `1` is not a maximum over `4, 6` (C1), `0` not a minimum under `2, 6` (C2), and not
`4 > 1, 2` with `0 > 2` (C3). -/
theorem quint_Tc_unimodal {z1 z4 z2 z0 z6 : ℝ} (hinj : Function.Injective (quint z1 z4 z2 z0 z6))
    (F1 : ¬ (z4 < z1 ∧ z6 < z1)) (F2 : ¬ (z0 < z2 ∧ z0 < z6))
    (F3 : ¬ (z1 < z4 ∧ z2 < z4 ∧ z2 < z0)) : IsCyclicUnimodal (quint z1 z4 z2 z0 z6) := by
  have h02 : z0 ≠ z2 := fun h => absurd (hinj (show quint z1 z4 z2 z0 z6 3 = quint z1 z4 z2 z0 z6 2
    from h)) (by decide)
  obtain ⟨a0, a1, a2, a3, a4⟩ := zmod5_add_one
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_sub_one
  refine unimodal5_tac hinj fun i j hi hj => ?_
  rcases lt_or_gt_of_ne h02 with h | h <;>
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
  simp only [a0, a1, a2, a3, a4, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3,
    quint_4] at hi hj <;>
  first
  | rfl
  | (exfalso; linarith [hi.1, hi.2, hj.1, hj.2])
  | (exfalso; exact F1 ⟨by linarith [hi.1, hi.2, hj.1, hj.2], by linarith [hi.1, hi.2, hj.1, hj.2]⟩)
  | (exfalso; exact F2 ⟨by linarith [hi.1, hi.2, hj.1, hj.2], by linarith [hi.1, hi.2, hj.1, hj.2]⟩)
  | (exfalso; exact F3 ⟨by linarith [hi.1, hi.2, hj.1, hj.2], by linarith [hi.1, hi.2, hj.1, hj.2],
      by linarith [hi.1, hi.2, hj.1, hj.2]⟩)

/-- The depth pattern of `A` with five corners (§19.5): the pentagon `(6, 3, 5, 2, 4)` is
unimodal if `3` is not a maximum (A1), `4` not a minimum under `6, 2` (A3), and `2` not a minimum
under `4, 5` (A2′). -/
theorem quint_A_unimodal {z6 z3 z5 z2 z4 : ℝ} (hinj : Function.Injective (quint z6 z3 z5 z2 z4))
    (G1 : ¬ (z5 < z3 ∧ z6 < z3)) (G2 : ¬ (z2 < z4 ∧ z2 < z5)) (G3 : ¬ (z4 < z6 ∧ z4 < z2)) :
    IsCyclicUnimodal (quint z6 z3 z5 z2 z4) := by
  have h42 : z4 ≠ z2 := fun h => absurd (hinj (show quint z6 z3 z5 z2 z4 4 = quint z6 z3 z5 z2 z4 3
    from h)) (by decide)
  obtain ⟨a0, a1, a2, a3, a4⟩ := zmod5_add_one
  obtain ⟨b0, b1, b2, b3, b4⟩ := zmod5_sub_one
  refine unimodal5_tac hinj fun i j hi hj => ?_
  rcases lt_or_gt_of_ne h42 with h | h <;>
  rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
  rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
  simp only [a0, a1, a2, a3, a4, b0, b1, b2, b3, b4, quint_0, quint_1, quint_2, quint_3,
    quint_4] at hi hj <;>
  first
  | rfl
  | (exfalso; linarith [hi.1, hi.2, hj.1, hj.2])
  | (exfalso; exact G1 ⟨by linarith [hi.1, hi.2, hj.1, hj.2], by linarith [hi.1, hi.2, hj.1, hj.2]⟩)
  | (exfalso; exact G2 ⟨by linarith [hi.1, hi.2, hj.1, hj.2], by linarith [hi.1, hi.2, hj.1, hj.2]⟩)
  | (exfalso; exact G3 ⟨by linarith [hi.1, hi.2, hj.1, hj.2], by linarith [hi.1, hi.2, hj.1, hj.2]⟩)

set_option maxHeartbeats 4000000 in
/-- **Lemma 19.5 (the triple `T6`)** on `Ω_open` (`Ω ∩ {d < 1, b > 1, H_A > 0}`): one of
`T_a = 0235/046` at `0` (view `u_a`), `A = 036/146` at `6` (view `v_A`) and `T_c = K_1` at `15`
(view `u_c = 5 − 1`) is unimodal.  If `T_a` fails, `⟪u_a, v_A⟫ > 0`; if `T_c` fails,
`⟪u_c, v_A⟫ < 0`; if `A` fails, `⟪v_A, u_c⟫ > 0` or `⟪v_A, u_a⟫ < 0`. -/
theorem isRupert_T6 (N : NF16 x) (O : Omega N) (hd1 : 0 < 1 - N.d) (hb1 : 0 < N.b - 1)
    (ha1 : N.a ≠ 1)
    (hf03 : 0 < -(N.q * (1 - N.d) + N.g * (N.r - 1)))
    (hHA : 0 < (N.b - 1) * N.g * N.p * N.r + (N.q * (1 - N.d) + N.g * (N.r - 1)) *
      (N.a * (N.q - 1) - (N.b - 1) * N.p))
    (hf15 : 0 < N.d * N.q - (N.g - 1) * (N.p + N.r - 1)) (hpr : 0 < N.p + N.r - 1)
    (hT5 : N.d * (N.q * (N.a - 1) - N.b * (N.p - 1)) - (N.g - 1) * (N.a - 1) * N.r ≠ 0)
    (hg : GenPos (univ.image x)) (hnd : NoHDNEdges16 x)
    (huA : [⟪x 0, N.uA⟫, ⟪x 5, N.uA⟫, ⟪x 1, N.uA⟫, ⟪x 6, N.uA⟫].Nodup)
    (hnduA : NoHDNAt (univ.image x) N.uA)
    (hvA : [⟪x 6, N.vA⟫, ⟪x 3, N.vA⟫, ⟪x 5, N.vA⟫, ⟪x 2, N.vA⟫, ⟪x 4, N.vA⟫].Nodup)
    (hndvA : NoHDNAt (univ.image x) N.vA) : IsRupert (univ.image x) := by
  obtain ⟨hR1, hR2, hD, hqg, hg1, hqb, hc, -, -, -, -, -⟩ := O
  have hr1 : 0 < 1 - N.r := by
    by_contra hc'; push Not at hc'
    nlinarith [mul_pos N.hq hd1, mul_nonpos_of_nonneg_of_nonpos N.hg.le hc']
  have ht := N.t0146
  have ht2 := N.t0246
  have hgp : 0 < N.g * N.p := mul_pos N.hg N.hp
  -- (S2) and `c3 > 0`
  have hS2 : (N.a - 1) * (N.g - 1) < N.b * N.d := by
    rcases lt_or_gt_of_ne ha1 with ha | ha
    · nlinarith [mul_pos (sub_pos.mpr ha) hg1, mul_pos N.hb N.hd]
    · have k1 : (N.a - 1) * N.q < N.b * (N.p + N.r - 1) := by linarith
      have k2 : (N.g - 1) * (N.p + N.r - 1) < N.d * N.q := by linarith
      have := mul_lt_mul'' k1 k2 (mul_pos (sub_pos.mpr ha) N.hq).le (mul_pos hg1 hpr).le
      nlinarith [mul_pos N.hq hpr]
  have hc3 : 0 < (N.a - 1) * (N.r * (N.g - 1) - N.d * (N.q - 1)) + N.d * N.b * N.p := by
    rcases lt_or_gt_of_ne ha1 with ha | ha
    · refine pos_of_mul_pos_r N.ha ?_
      linarith [mul_pos (sub_pos.mpr ha) N.tB125, mul_pos (mul_pos N.hd N.hp) N.hab]
    · linarith [mul_pos (sub_pos.mpr ha) (mul_pos N.hp hg1), mul_pos N.hp (sub_pos.mpr hS2),
        mul_pos (sub_pos.mpr ha) hR1]
  -- the cone facts as vector identities
  have iC1 := N.vA_eq'
  have iA1 : x 5 - x 1 = (N.g - 1) • (x 3 - x 5) + N.d • (x 3 - x 6) := by nf_vec N
  have iTc4 : N.t0146v • (x 5 - x 1) = ((N.g - 1) * (N.p + N.r) - N.d * (N.q - 1)) • (x 0 - x 4) +
      (N.d * (N.p + N.q - 1) - (N.g - 1) * N.r) • (x 0 - x 6) +
      (N.d * N.q - (N.g - 1) * (N.p + N.r - 1)) • (x 1 - x 4) := by
    simp only [t0146v]; nf_vec N
  have iC2 : ((N.a - 1) * (N.g - 1) - N.b * N.d) • (-N.vA) =
      (-(N.g - 1) * N.t0146v) • (x 2 - x 0) +
      ((N.a - 1) * (N.g - 1) * (-N.f03) - N.b * N.d * N.g * N.p) • (x 6 - x 0) +
      (-N.b * N.t0146v) • (x 5 - x 1) := by
    simp only [t0146v]; (try simp only [vA, uA, f03]); nf_vec N
  have iC3 : (N.b * N.r + (N.a - 1) * N.r * N.g - N.d * ((N.a - 1) * N.q - N.b * (N.p - 1))) •
      (-(x 5 - x 1)) =
      (N.d * (N.q * (N.a - 1) - N.b * (N.p - 1)) - (N.g - 1) * (N.a - 1) * N.r) • (x 4 - x 1) +
      ((N.a - 1) * (N.r * (N.g - 1) - N.d * (N.q - 1)) + N.d * N.b * N.p) • (x 4 - x 2) +
      (N.a * N.d * (N.q - 1) - N.d * N.p * (N.b - 1) - N.a * N.r * (N.g - 1)) • (x 0 - x 2) := by
    nf_vec N
  have iA3 : (-(N.g * N.p * N.t0246v + N.t0146v * (N.a * N.q - N.b * N.p))) • (-N.uA) =
      (-N.q * (1 - N.r) * N.t0146v) • (x 2 - x 4) +
      (-(N.g * N.p * N.t0246v + N.t0146v * N.c36v + N.r * N.t0146v * (N.q - N.b))) • (x 6 - x 4) +
      (-(1 - N.r) * N.t0246v) • N.vA := by
    simp only [t0146v, t0246v, c36v]; (try simp only [vA, uA, f03]); nf_vec N
  have iA2 : ((N.b - 1) * N.g * N.p * N.r + (N.q * (1 - N.d) + N.g * (N.r - 1)) *
      (N.a * (N.q - 1) - (N.b - 1) * N.p)) • (-N.uA) =
      (-(N.a * N.q - (N.b - 1) * (N.p + N.r - 1)) * N.f03) • (x 4 - x 2) +
      (N.g * N.p * N.t0246v + N.t0146v * N.c36v + N.r * N.t0146v * (N.q - N.b)) • (x 5 - x 2) +
      (N.r * (N.a + N.b - 1 + (N.a * (N.q - 1) - (N.b - 1) * (N.p + N.r)))) • N.vA := by
    simp only [t0146v, t0246v, c36v]; (try simp only [vA, uA, f03]); nf_vec N
  -- positivity of the named quantities
  have ht' : 0 < N.t0146v := N.t0146
  have ht2' : 0 < N.t0246v := N.t0246
  have hc' : 0 < N.c36v := hc
  have hfv : 0 < -N.f03 := hf03
  have hvA0 : N.vA ≠ 0 := by simp only [vA]; exact nfV_ne_zero N.hD (Or.inl (ne_of_gt hgp))
  have hvv : 0 < ⟪N.vA, N.vA⟫ := real_inner_self_pos.mpr hvA0
  have huc : 0 < ⟪x 5 - x 1, x 5 - x 1⟫ :=
    real_inner_self_pos.mpr (sub_ne_zero.mpr (N.inj.ne (by decide)))
  have huc' : 0 < ⟪x 5, x 5 - x 1⟫ - ⟪x 1, x 5 - x 1⟫ := by rw [← inner_sub_left]; exact huc
  have hX1 : 0 < N.g * N.p * N.t0246v + N.t0146v * N.c36v + N.r * N.t0146v * (N.q - N.b) := by
    linarith [mul_pos hgp ht2', mul_pos ht' hc', mul_pos (mul_pos N.hr ht') hqb]
  -- (C1): `1` above `4` and `6` along `u_c` forces `⟪u_c, v_A⟫ < 0`
  have C1 : ⟪x 4, x 5 - x 1⟫ < ⟪x 1, x 5 - x 1⟫ → ⟪x 6, x 5 - x 1⟫ < ⟪x 1, x 5 - x 1⟫ →
      ⟪x 5 - x 1, N.vA⟫ < 0 := by
    intro h4 h6
    rw [real_inner_comm, iC1]
    simp only [inner_neg_left, inner_sub_left, real_inner_smul_left]
    linarith [mul_pos hqg (sub_pos.mpr h6), mul_pos N.hg (sub_pos.mpr h4)]
  by_cases h1 : ⟪N.uA, N.vA⟫ ≤ 0
  · -- `T_a` is unimodal
    refine isRupert_T6_Ta N hR1 hR2 hD hqg hg1 hqb hc hd1 hf03 hb1 hHA hf15 hpr
      (quad_unimodal ?_ huA) hnduA
    intro hsep
    have hsep' : DepthSep (x 0) (x 1) (x 6) (x 5) N.uA := by
      simp only [DepthSep, max_comm, min_comm] at hsep ⊢; tauto
    have hKa : 0 < (N.g + N.d) * (N.p + N.r - 1) + N.q :=
        by linarith [mul_pos (add_pos N.hg N.hd) hpr, N.hq]
    have hKv : 0 < N.g * N.p * (N.g + N.d - 1) + N.t0146v := by linarith [mul_pos hgp N.hgd, ht']
    have hs := depthSep_of_meet (d₀ := x 0) (d₁ := x 1) (e₀ := x 6) (e₁ := x 5) (w := N.uA)
      (s := (N.p + N.q + N.r - 1) / ((N.g + N.d) * (N.p + N.r - 1) + N.q))
      (t := N.t0146v / ((N.g + N.d) * (N.p + N.r - 1) + N.q))
      (l := -(N.g + N.d - 1) / ((N.g + N.d) * (N.p + N.r - 1) + N.q))
      (div_pos N.t046_5 hKa).le ((div_le_one hKa).mpr (by linarith [mul_pos N.hgd hpr]))
      (div_pos ht' hKa).le
      ((div_le_one hKa).mpr (by simp only [t0146v]; linarith [mul_pos N.hd N.t046_5]))
      ?_ (div_nonpos_of_nonpos_of_nonneg (by linarith [N.hgd]) hKa.le) hsep'
    · have hl := depthSep_sign (d₀ := x 0) (d₁ := x 1) (e₀ := x 6) (e₁ := x 5) (v := N.vA)
        (s := N.t0146v / (N.g * N.p * (N.g + N.d - 1) + N.t0146v))
        (t := N.g * N.t0146v / (N.g * N.p * (N.g + N.d - 1) + N.t0146v))
        (l := -(N.g + N.d - 1) / (N.g * N.p * (N.g + N.d - 1) + N.t0146v))
        (div_pos ht' hKv).le ((div_le_one hKv).mpr (by linarith [mul_pos hgp N.hgd]))
        (div_pos (mul_pos N.hg ht') hKv).le
        ((div_le_one hKv).mpr (by
          have e : N.t0146v = N.g * N.p + N.f03 := by simp only [t0146v, f03]; ring
          rw [e]; linarith [mul_pos (mul_pos N.hg N.hp) N.hd, mul_pos hg1 hfv]))
        ?_ hs
      · have hl' : -(N.g + N.d - 1) / (N.g * N.p * (N.g + N.d - 1) + N.t0146v) < 0 :=
          div_neg_of_neg_of_pos (by linarith [N.hgd]) hKv
        rw [real_inner_comm] at h1
        nlinarith [mul_neg_of_neg_of_pos hl' (show 0 < ⟪N.vA, N.uA⟫ by
          by_contra hc0; push Not at hc0
          nlinarith [mul_nonneg_of_nonpos_of_nonpos hl'.le hc0])]
      · refine meet_of_smul hKv.ne' ?_
        simp only [t0146v, vA, f03]
        nf_vec N
    · refine meet_of_smul hKa.ne' ?_
      simp only [t0146v, uA]
      nf_vec N
  push Not at h1
  have hzc := fun i j (hij : i ≠ j) (hh : (j ≠ 1 ∧ j ≠ 5) ∨ (i ≠ 5 ∧ j ≠ 5)) =>
    depth_ne (v := 1) (w := 5) N.inj hg hij (by decide) hh
  by_cases h2 : 0 ≤ ⟪x 5 - x 1, N.vA⟫
  · -- `T_c` is unimodal
    rcases lt_or_gt_of_ne hT5 with h5 | h5
    · have hz4 := depth_nodup4 (v := 1) (w := 5) (a := 4) (b := 6) (c := 0) N.inj hg (by decide)
      refine isRupert_T6_Tc4 N hR1 hR2 hD hqg hg1 hqb hc hd1 hf03 hb1 hHA hf15 hpr (by linarith)
        (quad_unimodal ?_ hz4.1) (hnd.fwd N (by decide))
      intro hsep
      rcases hsep with h | h
      · have k1 := max_lt_iff.mp h
        have k2 := lt_min_iff.mp k1.1
        have k3 := lt_min_iff.mp k1.2
        have e := cone_inner3 (w := x 5 - x 1) iTc4
        simp only [inner_sub_left] at e
        linarith [mul_pos ht' huc', mul_pos hR1 (sub_pos.mpr k3.1), mul_pos N.t145_0
              (sub_pos.mpr k3.2), mul_pos hf15 (sub_pos.mpr k2.1)]
      · have k1 := max_lt_iff.mp h
        have k2 := lt_min_iff.mp k1.1
        have k3 := lt_min_iff.mp k1.2
        linarith [C1 k2.1 k3.1]
    · refine isRupert_T6_Tc5 N hR1 hR2 hD hqg hg1 hqb hc hd1 hf03 hb1 hHA hf15 hpr h5
        (quint_Tc_unimodal (quint_injective (hzc 1 4 (by decide) (by decide))
          (hzc 1 2 (by decide) (by decide)) (hzc 1 0 (by decide) (by decide))
          (hzc 1 6 (by decide) (by decide)) (hzc 4 2 (by decide) (by decide))
          (hzc 4 0 (by decide) (by decide)) (hzc 4 6 (by decide) (by decide))
          (hzc 2 0 (by decide) (by decide)) (hzc 2 6 (by decide) (by decide))
          (hzc 0 6 (by decide) (by decide))) ?_ ?_ ?_) (hnd.fwd N (by decide))
      · rintro ⟨h4, h6⟩; linarith [C1 h4 h6]
      · rintro ⟨h02, h06⟩
        have e := cone_inner3 (w := x 5 - x 1) iC2
        simp only [inner_sub_left, inner_neg_left] at e
        have hn2 : 0 < N.b * N.d * N.g * N.p - (N.a - 1) * (N.g - 1) * (-N.f03) := by
          rcases lt_or_gt_of_ne ha1 with ha | ha
          · linarith [mul_pos (mul_pos (sub_pos.mpr ha) hg1) hfv, mul_pos (mul_pos N.hb N.hd) hgp]
          · have hf' : -N.f03 < N.g * N.p := by
              have : N.t0146v = N.g * N.p + N.f03 := by simp only [t0146v, f03]; ring
              linarith
            nlinarith [mul_lt_mul'' hS2 hf' (mul_pos (sub_pos.mpr ha) hg1).le hfv.le]
        rw [real_inner_comm] at h2
        linarith [mul_nonneg (sub_pos.mpr hS2).le h2, mul_pos (mul_pos hg1 ht') (sub_pos.mpr h02),
          mul_pos hn2 (sub_pos.mpr h06), mul_pos (mul_pos N.hb ht') huc']
      · rintro ⟨h14, h24, h20⟩
        have e := cone_inner3 (w := x 5 - x 1) iC3
        simp only [inner_sub_left, inner_neg_left] at e
        linarith [mul_pos N.t024_1 huc', mul_pos h5 (sub_pos.mpr h14), mul_pos hc3
              (sub_pos.mpr h24), mul_pos N.tB125 (sub_pos.mpr h20)]
  · -- `A` is unimodal
    push Not at h2
    refine isRupert_T6_A N hR1 hR2 hD hqg hg1 hqb hc hd1 hf03 hb1 hHA hf15 hpr
      (quint_A_unimodal (quint_inj_of_nodup hvA) ?_ ?_ ?_) hndvA
    · rintro ⟨h53, h63⟩
      have e := congrArg (fun w => ⟪w, N.vA⟫) iA1
      simp only [inner_add_left, inner_sub_left, real_inner_smul_left] at e
      rw [inner_sub_left] at h2
      linarith [mul_pos hg1 (sub_pos.mpr h53), mul_pos N.hd (sub_pos.mpr h63)]
    · rintro ⟨h24, h25⟩
      have e := cone_inner3 (w := N.vA) iA2
      simp only [inner_sub_left, inner_neg_left] at e
      have hM : 0 < N.a * N.q - (N.b - 1) * (N.p + N.r - 1) := by linarith [N.hab]
      linarith [mul_pos hHA h1, mul_pos (mul_pos hM hfv) (sub_pos.mpr h24),
        mul_pos hX1 (sub_pos.mpr h25), mul_pos (mul_pos N.hr (show 0 < N.a + N.b - 1 +
          (N.a * (N.q - 1) - (N.b - 1) * (N.p + N.r)) by linarith [N.hab])) hvv]
    · rintro ⟨h46, h42⟩
      have e := cone_inner3 (w := N.vA) iA3
      simp only [inner_sub_left, inner_neg_left] at e
      have hZ : 0 < N.g * N.p * N.t0246v + N.t0146v * (N.a * N.q - N.b * N.p) := by
        have : N.a * N.q - N.b * N.p = N.c36v + (N.q - N.b) := by simp only [c36v]; ring
        rw [this]; linarith [mul_pos hgp ht2', mul_pos ht' hc', mul_pos ht' hqb]
      linarith [mul_pos hZ h1, mul_pos (mul_pos (mul_pos N.hq hr1) ht') (sub_pos.mpr h42),
        mul_pos hX1 (sub_pos.mpr h46), mul_pos (mul_pos hr1 ht2') hvv]

end NF16

end Minimality

end
