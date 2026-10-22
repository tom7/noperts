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

* **Lemma 19.3** (`cert_F3`): `Ω ∩ {d > 1}`: the closing `K_3` at `35` (rim `(3, x, 4, 1)`)
  and the vertex crossing `046/145` at `4` (view `vT2`, rim `(4, 5, 3, 6)`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

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

/-- **The four-corner rule with ties, strict crossing**: if the diagonals `[d₀, d₁]`, `[e₀, e₁]`
of a 4-corner rim cross along `w ≠ 0` with `e − d = l w`, `l < 0`, then `{e₀, e₁}` is not
weakly above `{d₀, d₁}`. -/
theorem not_weakSep_of_meet {d₀ d₁ e₀ e₁ w : ℝ³} {s t l : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hm : (e₀ + t • (e₁ - e₀)) - (d₀ + s • (d₁ - d₀)) = l • w)
    (hl : l < 0) (hw : w ≠ 0) (h1 : ⟪d₀, w⟫ ≤ ⟪e₀, w⟫) (h2 : ⟪d₀, w⟫ ≤ ⟪e₁, w⟫)
    (h3 : ⟪d₁, w⟫ ≤ ⟪e₀, w⟫) (h4 : ⟪d₁, w⟫ ≤ ⟪e₁, w⟫) : False := by
  have i1 := congrArg (fun z => ⟪z, w⟫) hm
  simp only [inner_sub_left, inner_seg, real_inner_smul_left] at i1
  have hww : 0 < ⟪w, w⟫ := real_inner_self_pos.mpr hw
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hs1))
      (sub_nonneg.mpr h1), mul_nonneg (mul_nonneg (sub_nonneg.mpr ht1) hs0) (sub_nonneg.mpr h3),
    mul_nonneg (mul_nonneg ht0 (sub_nonneg.mpr hs1)) (sub_nonneg.mpr h2),
    mul_nonneg (mul_nonneg ht0 hs0) (sub_nonneg.mpr h4), mul_pos_of_neg_of_neg hl (neg_neg_of_pos hww)]

/-- **The four-corner rule with ties, interior crossing**: if the diagonals cross at interior
points (`0 < s, t < 1`) along `w` with `e − d = l w`, `l ≤ 0`, and `{e₀, e₁}` is weakly above
`{d₀, d₁}`, all four depths are equal. -/
theorem eq_of_weakSep_meet {d₀ d₁ e₀ e₁ w : ℝ³} {s t l : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ht0 : 0 < t) (ht1 : t < 1) (hm : (e₀ + t • (e₁ - e₀)) - (d₀ + s • (d₁ - d₀)) = l • w)
    (hl : l ≤ 0) (h1 : ⟪d₀, w⟫ ≤ ⟪e₀, w⟫) (h2 : ⟪d₀, w⟫ ≤ ⟪e₁, w⟫)
    (h3 : ⟪d₁, w⟫ ≤ ⟪e₀, w⟫) (h4 : ⟪d₁, w⟫ ≤ ⟪e₁, w⟫) :
    ⟪d₀, w⟫ = ⟪e₀, w⟫ ∧ ⟪d₁, w⟫ = ⟪e₀, w⟫ ∧ ⟪e₁, w⟫ = ⟪e₀, w⟫ := by
  have i1 := congrArg (fun z => ⟪z, w⟫) hm
  simp only [inner_sub_left, inner_seg, real_inner_smul_left] at i1
  have hww := real_inner_self_nonneg (x := w)
  have p1 := mul_nonneg (mul_nonneg (sub_nonneg.mpr ht1.le) (sub_nonneg.mpr hs1.le))
    (sub_nonneg.mpr h1)
  have p2 := mul_nonneg (mul_nonneg (sub_nonneg.mpr ht1.le) hs0.le) (sub_nonneg.mpr h3)
  have p3 := mul_nonneg (mul_nonneg ht0.le (sub_nonneg.mpr hs1.le)) (sub_nonneg.mpr h2)
  have p4 := mul_nonneg (mul_nonneg ht0.le hs0.le) (sub_nonneg.mpr h4)
  have p5 := mul_nonpos_of_nonpos_of_nonneg hl hww
  have k1 : (1 - t) * (1 - s) * (⟪e₀, w⟫ - ⟪d₀, w⟫) = 0 := by nlinarith
  have k2 : (1 - t) * s * (⟪e₀, w⟫ - ⟪d₁, w⟫) = 0 := by nlinarith
  have k3 : t * (1 - s) * (⟪e₁, w⟫ - ⟪d₀, w⟫) = 0 := by nlinarith
  have c1 : (1 - t) * (1 - s) ≠ 0 := mul_ne_zero (by linarith) (by linarith)
  have c2 : (1 - t) * s ≠ 0 := mul_ne_zero (by linarith) hs0.ne'
  have c3 : t * (1 - s) ≠ 0 := mul_ne_zero ht0.ne' (by linarith)
  have e1 := (mul_eq_zero.mp k1).resolve_left c1
  have e2 := (mul_eq_zero.mp k2).resolve_left c2
  have e3 := (mul_eq_zero.mp k3).resolve_left c3
  refine ⟨by linarith, by linarith, by linarith⟩

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

/-- `vT2` is the named view along the vertex crossing `046/145` (`vtxView16 x 0 = −D vT2`). -/
theorem vtxView16_vT2 (N : NF16 x) : vtxView16 x 0 = (-N.D) • N.vT2 := by
  show planeLine (x 0) (x 4) (x 6) (x 1) (x 4) (x 5) = _
  simp only [planeLine, vT2, f15, t0146v, D]
  nf_simp N
  ext k
  simp only [nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul,
    det3c]
  ring

theorem named_vT2 (N : NF16 x) : Named16 x N.vT2 := by
  have hD : -N.D ≠ 0 := neg_ne_zero.mpr N.hD
  refine ⟨.inr 0, (-N.D)⁻¹, inv_ne_zero hD, ?_⟩
  show N.vT2 = (-N.D)⁻¹ • vtxView16 x 0
  rw [vtxView16_vT2, smul_smul, inv_mul_cancel₀ hD, one_smul]

theorem namedAt_vT2 (N : NF16 x) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    ∃ c : ℝ, c ≠ 0 ∧ σ • N.vT2 = c • view16 x (.inr 0) := by
  have hD : -N.D ≠ 0 := neg_ne_zero.mpr N.hD
  refine ⟨σ * (-N.D)⁻¹, mul_ne_zero (sigma_ne_zero hσ) (inv_ne_zero hD), ?_⟩
  show σ • N.vT2 = (σ * (-N.D)⁻¹) • vtxView16 x 0
  rw [vtxView16_vT2, smul_smul, mul_assoc, inv_mul_cancel₀ hD, mul_one]

/-- **Lemma 19.3, `T1` for `a > 1`**: the closing `K_3` at `35`, rim `(3, 2, 4, 1)`. -/
theorem cert_F3_T1a (N : NF16 x) (hR1 : 0 < (N.g - 1) * (N.p + N.r) - N.d * (N.q - 1))
    (hR2 : 0 < N.a * (N.q - 1) - (N.b - 1) * (N.p + N.r)) (hD : 0 < N.q * N.d - N.r * N.g)
    (hqg : 0 < N.q - N.g) (hg1 : 0 < N.g - 1) (hqb : 0 < N.q - N.b)
    (hc : 0 < N.q * (N.a - 1) - N.b * (N.p - 1)) (hd1 : 0 < N.d - 1)
    (hf15 : 0 < N.d * N.q - (N.g - 1) * (N.p + N.r - 1)) (ha1 : 0 < N.a - 1)
    (hz : IsRobustUnimodal
          (quad ⟪x 3, (x 5 - x 3)⟫ ⟪x 1, (x 5 - x 3)⟫ ⟪x 4, (x 5 - x 3)⟫ ⟪x 2, (x 5 - x 3)⟫)) : Cert16 x := by
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  refine Cert16.mkPQ (.inl (3, 5)) 3 1 4 2 (by decide) (namedAt16_seg 3 5 hσ) (rimCertPts_equadσ (univ.image x) ({x 0, x 6} : Finset ℝ³) (u := (x 5 - x 3))
      (sub_ne_zero.mpr (N.inj.ne (by decide))) hσ (h := (-1 : ℝ)) (by norm_num) (by module)
      (mem_image 5)
    (mem_image 3) (mem_image 1) (mem_image 4) (mem_image 2)
    (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff])
        (by simp [N.inj.eq_iff]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hz ?_)
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
theorem cert_F3_T1b (N : NF16 x) (hR1 : 0 < (N.g - 1) * (N.p + N.r) - N.d * (N.q - 1))
    (hR2 : 0 < N.a * (N.q - 1) - (N.b - 1) * (N.p + N.r)) (hD : 0 < N.q * N.d - N.r * N.g)
    (hqg : 0 < N.q - N.g) (hg1 : 0 < N.g - 1) (hqb : 0 < N.q - N.b)
    (hc : 0 < N.q * (N.a - 1) - N.b * (N.p - 1)) (hd1 : 0 < N.d - 1)
    (hf15 : 0 < N.d * N.q - (N.g - 1) * (N.p + N.r - 1)) (ha1 : 0 < 1 - N.a)
    (hz : IsRobustUnimodal
          (quad ⟪x 3, (x 5 - x 3)⟫ ⟪x 1, (x 5 - x 3)⟫ ⟪x 4, (x 5 - x 3)⟫ ⟪x 0, (x 5 - x 3)⟫)) : Cert16 x := by
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  refine Cert16.mkPQ (.inl (3, 5)) 3 1 4 0 (by decide) (namedAt16_seg 3 5 hσ) (rimCertPts_equadσ (univ.image x) ({x 2, x 6} : Finset ℝ³) (u := (x 5 - x 3))
      (sub_ne_zero.mpr (N.inj.ne (by decide))) hσ (h := (-1 : ℝ)) (by norm_num) (by module)
      (mem_image 5)
    (mem_image 3) (mem_image 1) (mem_image 4) (mem_image 0)
    (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff])
        (by simp [N.inj.eq_iff]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hz ?_)
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
theorem cert_F3_T2 (N : NF16 x) (hR1 : 0 < (N.g - 1) * (N.p + N.r) - N.d * (N.q - 1))
    (hR2 : 0 < N.a * (N.q - 1) - (N.b - 1) * (N.p + N.r)) (hD : 0 < N.q * N.d - N.r * N.g)
    (hqg : 0 < N.q - N.g) (hg1 : 0 < N.g - 1) (hqb : 0 < N.q - N.b)
    (hc : 0 < N.q * (N.a - 1) - N.b * (N.p - 1)) (hd1 : 0 < N.d - 1)
    (hf15 : 0 < N.d * N.q - (N.g - 1) * (N.p + N.r - 1))
    (hz : IsRobustUnimodal (quad ⟪x 4, N.vT2⟫ ⟪x 6, N.vT2⟫ ⟪x 3, N.vT2⟫ ⟪x 5, N.vT2⟫)) : Cert16 x := by
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  refine Cert16.mkPQ (.inr 0) 4 6 3 5 (by decide) (N.namedAt_vT2 hσ) (rimCertPts_vquadσ (univ.image x) ({x 0, x 1} : Finset ℝ³) (u := N.vT2) (N.vT2_ne hf15) hσ
    (mem_image 4) (mem_image 6) (mem_image 3) (mem_image 5)
    (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff])
        (by simp [N.inj.eq_iff]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hz ?_)
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



/-- **Lemma 19.3** (`Ω ∩ {d > 1}`), with ties: the closing `T1 = K_3` at `35` (rim
`(3, 1, 4, x)`, `x = 2` iff `a > 1`) or the vertex crossing `T2 = 046/145` at `4` (view `vT2`,
rim `(4, 6, 3, 5)`) has diagonals that are not weakly separated, hence is robustly unimodal.
`T2` can fail only with `{4, 3}` weakly above `{6, 5}` (its diagonals cross with
`λ = −1/K < 0`, `not_weakSep_of_meet`), and then `⟪5 − 3, vT2⟫ ≤ 0`.  `T1` can fail only with
`{3, 4}` weakly above `{1, x}` (the other way the crossing along `5 − 3` with `l ≤ 0` at interior
points would put `1, x, 3, 4` at one depth, two ties at the edge view `35`, against `TieSeg`),
and then `⟪vT2, 5 − 3⟫ > 0`. -/
theorem cert_F3 (N : NF16 x) (O : Omega N) (hd1 : 0 < N.d - 1) (ha1 : N.a ≠ 1)
    (hf15 : 0 < N.d * N.q - (N.g - 1) * (N.p + N.r - 1))
    (hg : TieSeg (univ.image x)) : Cert16 x := by
  obtain ⟨hR1, hR2, hD, hqg, hg1, hqb, hc, nD2, -, -, -, -⟩ := O
  have huu : 0 < ⟪(x 5 - x 3), (x 5 - x 3)⟫ := real_inner_self_pos.mpr
      (sub_ne_zero.mpr (N.inj.ne (by decide)))
  -- `T2` is `NWS4`, or `⟪5 − 3, vT2⟫ ≤ 0`
  by_cases hN2 : NWS4 (quad ⟪x 4, N.vT2⟫ ⟪x 6, N.vT2⟫ ⟪x 3, N.vT2⟫ ⟪x 5, N.vT2⟫)
  · exact cert_F3_T2 N hR1 hR2 hD hqg hg1 hqb hc hd1 hf15 hN2.isRobustUnimodal
  have h53 : ⟪x 5, N.vT2⟫ ≤ ⟪x 3, N.vT2⟫ := by
    simp only [NWS4, quad_0, quad_1, quad_2, quad_3, not_and_or, not_or, not_lt] at hN2
    rcases hN2 with ⟨k1, k2, k3, k4⟩ | ⟨k1, k2, k3, k4⟩
    · exact k4
    · exfalso
      set K := N.q * (N.g + N.d - 1) + N.d * (N.p + N.q + N.r - 1) with hK
      have hK0 : 0 < K := by nlinarith [mul_pos N.hq N.hgd, mul_pos N.hd N.t046_5]
      refine not_weakSep_of_meet (d₀ := x 4) (d₁ := x 3) (e₀ := x 6) (e₁ := x 5) (w := N.vT2)
        (s := (N.g + N.d - 1) * (N.p + N.q + N.r - 1) / K)
        (t := (N.q * (N.g + N.d - 1) + N.d * (N.p + N.q + N.r - 1) - N.d * (N.p + N.q + N.r - 1)) / K)
        (l := -1 / K) (div_pos (mul_pos N.hgd N.t046_5) hK0).le
        ((div_le_one hK0).mpr (by nlinarith [hf15]))
        (div_pos (by nlinarith [mul_pos N.hq N.hgd]) hK0).le
        ((div_le_one hK0).mpr (by nlinarith [mul_pos N.hd N.t046_5])) ?_
        (div_neg_of_neg_of_pos (by norm_num) hK0) (N.vT2_ne hf15) k1 k2 k3 k4
      have hK0' := hK0.ne'
      simp only [vT2, f15, t0146v]
      nf_simp N
      ext k
      simp only [nfP, nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply,
        smul_eq_mul]
      field_simp
      ring
  -- `{3, 4}` weakly above `{1, X}` contradicts `h53`
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
  have up : ⟪x 1, (x 5 - x 3)⟫ ≤ ⟪x 4, (x 5 - x 3)⟫ → ⟪x 1, (x 5 - x 3)⟫ ≤ ⟪x 3, (x 5 - x 3)⟫ →
      False := fun h4 h3 => by
    nlinarith [mul_nonneg hf.le (show 0 ≤ ⟪x 4, (x 5 - x 3)⟫ - ⟪x 1, (x 5 - x 3)⟫ by linarith),
      mul_pos ht (show 0 < ⟪(x 5 - x 3), (x 5 - x 3)⟫ + (⟪x 3, (x 5 - x 3)⟫ - ⟪x 1, (x 5 - x 3)⟫)
            by linarith)]
  -- no three of the points at one depth along `35`
  have hm : ∀ i, x i ∈ univ.image x := fun i => mem_image_of_mem x (mem_univ i)
  have nt := fun {i j k : Fin 7} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) =>
    hg.noTriple (hm 3) (hm 5) (hm i) (hm j) (hm k) (N.inj.ne (by decide)) (N.inj.ne hij)
      (N.inj.ne hjk) (N.inj.ne hik)
  rcases lt_or_gt_of_ne ha1 with ha | ha
  · have ha' : 0 < 1 - N.a := by linarith
    by_cases hN1 : NWS4 (quad ⟪x 3, (x 5 - x 3)⟫ ⟪x 1, (x 5 - x 3)⟫ ⟪x 4, (x 5 - x 3)⟫
        ⟪x 0, (x 5 - x 3)⟫)
    · exact cert_F3_T1b N hR1 hR2 hD hqg hg1 hqb hc hd1 hf15 ha' hN1.isRobustUnimodal
    exfalso
    have hc4 : 0 < N.d * N.p - N.d + N.r :=
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
    have hmeet : (x 1 + (N.d * N.p / (N.d * N.p + N.r)) • (x 0 - x 1)) -
        (x 3 + (N.d / (N.d * N.p + N.r)) • (x 4 - x 3)) =
        ((N.g * N.r - N.d * N.q) / (N.d * N.p + N.r)) • (x 5 - x 3) := by
      have hK' := hK.ne'
      nf_simp N
      ext k
      simp only [nfP, nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply,
        smul_eq_mul]
      field_simp
      ring
    simp only [NWS4, quad_0, quad_1, quad_2, quad_3, not_and_or, not_or, not_lt] at hN1
    rcases hN1 with ⟨k1, k2, k3, k4⟩ | ⟨k1, k2, k3, k4⟩
    · exact up k3 k1
    · obtain ⟨q1, q2, q3⟩ := eq_of_weakSep_meet (div_pos N.hd hK) ((div_lt_one hK).mpr (by linarith))
        (div_pos (mul_pos N.hd N.hp) hK) ((div_lt_one hK).mpr (by linarith [N.hr])) hmeet
        (div_nonpos_of_nonpos_of_nonneg (by linarith) hK.le) k1 k2 k3 k4
      exact nt (i := 3) (j := 1) (k := 4) (by decide) (by decide) (by decide)
        ⟨q1, q2.symm⟩
  · have ha' : 0 < N.a - 1 := by linarith
    by_cases hN1 : NWS4 (quad ⟪x 3, (x 5 - x 3)⟫ ⟪x 1, (x 5 - x 3)⟫ ⟪x 4, (x 5 - x 3)⟫
        ⟪x 2, (x 5 - x 3)⟫)
    · exact cert_F3_T1a N hR1 hR2 hD hqg hg1 hqb hc hd1 hf15 ha' hN1.isRobustUnimodal
    exfalso
    have hc4 : 0 < -N.a * N.d + N.a * N.r + N.d * N.p :=
        (pos_of_mul_pos_r
          (by show 0 < (1 / 2 : ℝ) * N.d + (1 / 2 : ℝ) * N.g - (1 / 2 : ℝ); linarith [hR1, hf15])
          (by
            show 0 < (-N.a * N.d + N.a * N.r + N.d * N.p) *
              ((1 / 2 : ℝ) * N.d + (1 / 2 : ℝ) * N.g - (1 / 2 : ℝ))
            linarith [mul_pos (N.t146_2) (N.hd), mul_pos (N.tB125) (hd1)]))
    have hK : 0 < N.a * N.r + N.d * N.p := by nlinarith [mul_pos N.hd N.hp, mul_pos N.ha N.hr]
    have hmeet : (x 1 + (N.d * N.p / (N.a * N.r + N.d * N.p)) • (x 2 - x 1)) -
        (x 3 + (N.a * N.d / (N.a * N.r + N.d * N.p)) • (x 4 - x 3)) =
        ((N.p * N.b * N.d + N.r * N.g * N.a - N.q * N.a * N.d) / (N.a * N.r + N.d * N.p)) •
          (x 5 - x 3) := by
      have hK' := hK.ne'
      nf_simp N
      ext k
      simp only [nfP, nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply,
        smul_eq_mul]
      field_simp
      ring
    simp only [NWS4, quad_0, quad_1, quad_2, quad_3, not_and_or, not_or, not_lt] at hN1
    rcases hN1 with ⟨k1, k2, k3, k4⟩ | ⟨k1, k2, k3, k4⟩
    · exact up k3 k1
    · obtain ⟨q1, q2, q3⟩ := eq_of_weakSep_meet (div_pos (mul_pos N.ha N.hd) hK)
        ((div_lt_one hK).mpr (by linarith)) (div_pos (mul_pos N.hd N.hp) hK)
        ((div_lt_one hK).mpr (by linarith [mul_pos N.ha N.hr])) hmeet
        (div_nonpos_of_nonpos_of_nonneg (nD2 ha' hd1) hK.le) k1 k2 k3 k4
      exact nt (i := 3) (j := 1) (k := 4) (by decide) (by decide) (by decide)
        ⟨q1, q2.symm⟩


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

/-- `vA` is the named view along the vertex crossing `036/146` (`vtxView16 x 1 = −D vA`). -/
theorem vtxView16_vA (N : NF16 x) : vtxView16 x 1 = (-N.D) • N.vA := by
  show planeLine (x 0) (x 3) (x 6) (x 1) (x 4) (x 6) = _
  simp only [planeLine, vA, f03, D]
  nf_simp N
  ext k
  simp only [nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul,
    det3c]
  ring

/-- `uA` is the named view along the vertex crossing `0235/046` (`vtxView16 x 2 = −D uA`). -/
theorem vtxView16_uA (N : NF16 x) : vtxView16 x 2 = (-N.D) • N.uA := by
  show planeLine (x 0) (x 3) (x 5) (x 0) (x 4) (x 6) = _
  simp only [planeLine, uA, D]
  nf_simp N
  ext k
  simp only [nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul,
    det3c]
  ring

theorem named_vA (N : NF16 x) : Named16 x N.vA := by
  have hD : -N.D ≠ 0 := neg_ne_zero.mpr N.hD
  refine ⟨.inr 1, (-N.D)⁻¹, inv_ne_zero hD, ?_⟩
  show N.vA = (-N.D)⁻¹ • vtxView16 x 1
  rw [vtxView16_vA, smul_smul, inv_mul_cancel₀ hD, one_smul]

theorem named_uA (N : NF16 x) : Named16 x N.uA := by
  have hD : -N.D ≠ 0 := neg_ne_zero.mpr N.hD
  refine ⟨.inr 2, (-N.D)⁻¹, inv_ne_zero hD, ?_⟩
  show N.uA = (-N.D)⁻¹ • vtxView16 x 2
  rw [vtxView16_uA, smul_smul, inv_mul_cancel₀ hD, one_smul]

theorem namedAt_vA (N : NF16 x) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    ∃ c : ℝ, c ≠ 0 ∧ σ • N.vA = c • view16 x (.inr 1) := by
  have hD : -N.D ≠ 0 := neg_ne_zero.mpr N.hD
  refine ⟨σ * (-N.D)⁻¹, mul_ne_zero (sigma_ne_zero hσ) (inv_ne_zero hD), ?_⟩
  show σ • N.vA = (σ * (-N.D)⁻¹) • vtxView16 x 1
  rw [vtxView16_vA, smul_smul, mul_assoc, inv_mul_cancel₀ hD, mul_one]

theorem namedAt_uA (N : NF16 x) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    ∃ c : ℝ, c ≠ 0 ∧ σ • N.uA = c • view16 x (.inr 2) := by
  have hD : -N.D ≠ 0 := neg_ne_zero.mpr N.hD
  refine ⟨σ * (-N.D)⁻¹, mul_ne_zero (sigma_ne_zero hσ) (inv_ne_zero hD), ?_⟩
  show σ • N.uA = (σ * (-N.D)⁻¹) • vtxView16 x 2
  rw [vtxView16_uA, smul_smul, mul_assoc, inv_mul_cancel₀ hD, mul_one]

/-- **Lemma 19.4, `A`**: the vertex crossing `036/146` at `6` (view `vA`), rim `(6, 4, 5, 3)`
(`H_A < 0`: `2` hidden). -/
theorem cert_F1s_A (N : NF16 x) (hR1 : 0 < (N.g - 1) * (N.p + N.r) - N.d * (N.q - 1))
    (hR2 : 0 < N.a * (N.q - 1) - (N.b - 1) * (N.p + N.r)) (hD : 0 < N.q * N.d - N.r * N.g)
    (hqg : 0 < N.q - N.g) (hg1 : 0 < N.g - 1) (hqb : 0 < N.q - N.b)
    (hc : 0 < N.q * (N.a - 1) - N.b * (N.p - 1)) (hd1 : 0 < 1 - N.d)
    (hf03 : 0 < -(N.q * (1 - N.d) + N.g * (N.r - 1)))
    (hHA : 0 < -((N.b - 1) * N.g * N.p * N.r + (N.q * (1 - N.d) + N.g * (N.r - 1)) *
        (N.a * (N.q - 1) - (N.b - 1) * N.p)))
    (hz : IsRobustUnimodal (quad ⟪x 6, N.vA⟫ ⟪x 3, N.vA⟫ ⟪x 5, N.vA⟫ ⟪x 4, N.vA⟫)) : Cert16 x := by
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  refine Cert16.mkPQ (.inr 1) 6 3 5 4 (by decide) (N.namedAt_vA hσ) (rimCertPts_vquadσ (univ.image x) ({x 0, x 1} : Finset ℝ³) (u := N.vA)
      (by
        simp only [NF16.vA, NF16.f03]
        exact nfV_ne_zero N.hD (Or.inl (ne_of_gt
              (by have := (by show 0 < N.g * N.p; linarith [mul_pos (N.hg) N.hp]); linarith)))) hσ
    (mem_image 6) (mem_image 3) (mem_image 5) (mem_image 4)
    (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff])
        (by simp [N.inj.eq_iff]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hz ?_)
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
theorem cert_T6_Tc4 (N : NF16 x) (hR1 : 0 < (N.g - 1) * (N.p + N.r) - N.d * (N.q - 1))
    (hR2 : 0 < N.a * (N.q - 1) - (N.b - 1) * (N.p + N.r)) (hD : 0 < N.q * N.d - N.r * N.g)
    (hqg : 0 < N.q - N.g) (hg1 : 0 < N.g - 1) (hqb : 0 < N.q - N.b)
    (hc : 0 < N.q * (N.a - 1) - N.b * (N.p - 1)) (hd1 : 0 < 1 - N.d)
    (hf03 : 0 < -(N.q * (1 - N.d) + N.g * (N.r - 1))) (hb1 : 0 < N.b - 1)
    (hHA : 0 < (N.b - 1) * N.g * N.p * N.r + (N.q * (1 - N.d) + N.g * (N.r - 1)) *
      (N.a * (N.q - 1) - (N.b - 1) * N.p)) (hf15 : 0 < N.d * N.q - (N.g - 1) * (N.p + N.r - 1))
    (hpr : 0 < N.p + N.r - 1)
    (hT5 : 0 < (N.g - 1) * (N.a - 1) * N.r - N.d * (N.q * (N.a - 1) - N.b * (N.p - 1)))
    (hz : IsRobustUnimodal
          (quad ⟪x 1, (x 5 - x 1)⟫ ⟪x 4, (x 5 - x 1)⟫ ⟪x 0, (x 5 - x 1)⟫ ⟪x 6, (x 5 - x 1)⟫)) : Cert16 x := by
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  refine Cert16.mkPQ (.inl (1, 5)) 1 4 0 6 (by decide) (namedAt16_seg 1 5 hσ) (rimCertPts_equadσ (univ.image x) ({x 3} : Finset ℝ³) (u := (x 5 - x 1))
      (sub_ne_zero.mpr (N.inj.ne (by decide))) hσ (h := (-1 : ℝ)) (by norm_num) (by module)
      (mem_image 5)
    (mem_image 1) (mem_image 4) (mem_image 0) (mem_image 6)
    (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff])
        (by simp [N.inj.eq_iff]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hz ?_)
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
theorem cert_F1s_B (N : NF16 x) (hR1 : 0 < (N.g - 1) * (N.p + N.r) - N.d * (N.q - 1))
    (hR2 : 0 < N.a * (N.q - 1) - (N.b - 1) * (N.p + N.r)) (hD : 0 < N.q * N.d - N.r * N.g)
    (hqg : 0 < N.q - N.g) (hg1 : 0 < N.g - 1) (hqb : 0 < N.q - N.b)
    (hc : 0 < N.q * (N.a - 1) - N.b * (N.p - 1)) (hd1 : 0 < 1 - N.d)
    (hf03 : 0 < -(N.q * (1 - N.d) + N.g * (N.r - 1)))
    (hHA : 0 < -((N.b - 1) * N.g * N.p * N.r + (N.q * (1 - N.d) + N.g * (N.r - 1)) *
        (N.a * (N.q - 1) - (N.b - 1) * N.p)))
    (hz : IsRobustUnimodal (quint ⟪x 6, (x 6 - x 3)⟫ ⟪x 0, (x 6 - x 3)⟫ ⟪x 2, (x 6 - x 3)⟫ ⟪x 4,
            (x 6 - x 3)⟫ ⟪x 1, (x 6 - x 3)⟫)) : Cert16 x := by
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  have h02 : 0 < N.a * N.g + N.b - N.g := by
    rcases le_or_gt N.a 1 with h | h
    · linarith [hc, mul_nonneg hqg.le (sub_nonneg.mpr h), mul_pos N.hb N.hp]
    · linarith [mul_pos N.hg (sub_pos.mpr h), N.hb]
  refine Cert16.mkPQ5 (.inl (3, 6)) 6 0 2 4 1 (by decide) (namedAt16_seg 3 6 hσ) (rimCertPts_equintσ (univ.image x) ({x 5} : Finset ℝ³) (u := (x 6 - x 3))
      (sub_ne_zero.mpr (N.inj.ne (by decide))) hσ (h := (1 : ℝ)) (by norm_num) (by module)
      (mem_image 3)
    (mem_image 6) (mem_image 0) (mem_image 2) (mem_image 4) (mem_image 1)
    (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff])
        (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff]) ?_ ?_ hz ?_)
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

/-- **The pentagon `B` with one tie**: the criterion of `quint_B_unimodal` in its open form
(`z₁` above `z₄` or `z₆`, `z₂` below `z₀` or `z₄`) with at most one tied pair gives a robustly
unimodal rim. -/
theorem quint_B_robust {z6 z0 z2 z4 z1 : ℝ}
    (hone : ∀ a b a' b', a ≠ b → a' ≠ b' → quint z6 z0 z2 z4 z1 a = quint z6 z0 z2 z4 z1 b →
      quint z6 z0 z2 z4 z1 a' = quint z6 z0 z2 z4 z1 b' → (a = a' ∧ b = b') ∨ (a = b' ∧ b = a'))
    (h60 : z0 < z6) (h1 : z4 < z1 ∨ z6 < z1) (P : z2 < z0 ∨ z2 < z4) :
    IsRobustUnimodal (quint z6 z0 z2 z4 z1) := by
  refine isRobustUnimodal_of_nhds hone
    (fun y => y 1 < y 0 ∧ (y 3 < y 4 ∨ y 0 < y 4) ∧ (y 2 < y 1 ∨ y 2 < y 3)) ?_ ?_
  · refine (eventually_entry_lt (i := 1) (j := 0) h60).and ((?_ : ∀ᶠ y in 𝓝 _, _).and ?_)
    · rcases h1 with h | h
      · exact (eventually_entry_lt (i := 3) (j := 4) h).mono fun y hy => Or.inl hy
      · exact (eventually_entry_lt (i := 0) (j := 4) h).mono fun y hy => Or.inr hy
    · rcases P with h | h
      · exact (eventually_entry_lt (i := 2) (j := 1) h).mono fun y hy => Or.inl hy
      · exact (eventually_entry_lt (i := 2) (j := 3) h).mono fun y hy => Or.inr hy
  · intro y hy hinj
    have e : y = quint (y 0) (y 1) (y 2) (y 3) (y 4) := by
      funext i; rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;> rfl
    rw [e] at hinj ⊢
    obtain ⟨k1, k2, k3⟩ := hy
    refine quint_B_unimodal hinj k1 (fun ⟨c1, c2⟩ => ?_) (fun c1 c2 => ?_)
    · rcases k2 with k | k <;> linarith
    · rcases k3 with k | k <;> linarith

set_option maxHeartbeats 800000 in
/-- **Lemma 19.4** (`Ω ∩ {d < 1}` with `H_A < 0`), with ties: the vertex crossing
`A = 036/146` at `6` (view `v_A`, rim `(6, 3, 5, 4)`) or the closing `B = K_6` at `36` (rim
`(6, 0, 2, 4, 1)`) is robustly unimodal.  If `⟪v_A, 6 − 3⟫ > 0`, `A`'s diagonals are not
weakly separated: `{6, 5}` weakly above `{4, 3}` contradicts the crossing with `λ_A < 0`
(`not_weakSep_of_meet`), and `{4, 3}` weakly above `{6, 5}` gives `⟪v_A, 6 − 3⟫ ≤ 0`.  If
`⟪v_A, 6 − 3⟫ ≤ 0`, then `z0 < z6`, `1` is not a weak local minimum and the identity of (iii)
leaves `2` no weak local maximum over `0, 4`, so `B` is robustly unimodal with at most one tie
(`quint_B_robust`, `TieSeg` at the edge view `36`). -/
theorem cert_F1s (N : NF16 x) (O : Omega N) (hd1 : 0 < 1 - N.d)
    (hf03 : 0 < -(N.q * (1 - N.d) + N.g * (N.r - 1)))
    (hHA : 0 < -((N.b - 1) * N.g * N.p * N.r + (N.q * (1 - N.d) + N.g * (N.r - 1)) *
      (N.a * (N.q - 1) - (N.b - 1) * N.p)))
    (hg : TieSeg (univ.image x)) : Cert16 x := by
  obtain ⟨hR1, hR2, hD, hqg, hg1, hqb, hc, -, -, -, -, -⟩ := O
  have he3 : 0 < ⟪x 6 - x 3, x 6 - x 3⟫ :=
    real_inner_self_pos.mpr (sub_ne_zero.mpr (N.inj.ne (by decide)))
  have he3' : 0 < ⟪x 6, x 6 - x 3⟫ - ⟪x 3, x 6 - x 3⟫ := by rw [← inner_sub_left]; exact he3
  by_cases hs : ⟪x 6 - x 3, N.vA⟫ ≤ 0
  · -- `B` is robustly unimodal
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
    have hm : ∀ i, x i ∈ univ.image x := fun i => mem_image_of_mem x (mem_univ i)
    have hone := (hg.tie (x 3) (hm 3) (x 6) (hm 6) (N.inj.ne (by decide))).rim5 (hm 6) (hm 0)
      (hm 2) (hm 4) (hm 1) (quint_injective (N.inj.ne (by decide)) (N.inj.ne (by decide))
        (N.inj.ne (by decide)) (N.inj.ne (by decide)) (N.inj.ne (by decide))
        (N.inj.ne (by decide)) (N.inj.ne (by decide)) (N.inj.ne (by decide))
        (N.inj.ne (by decide)) (N.inj.ne (by decide)))
    have h60 : ⟪x 0, x 6 - x 3⟫ < ⟪x 6, x 6 - x 3⟫ := by nlinarith [mul_pos ht he3']
    refine cert_F1s_B N hR1 hR2 hD hqg hg1 hqb hc hd1 hf03 hHA
      (quint_B_robust hone h60 ?_ ?_)
    · by_contra hc'
      simp only [not_or, not_lt] at hc'
      obtain ⟨h14, h16⟩ := hc'
      -- `q (z₆ − z₁) + g (z₄ − z₆) ≤ 0` with both parts `≥ 0` puts `1, 4, 6` at one depth
      have k1 : (N.q - N.g) * (⟪x 6, x 6 - x 3⟫ - ⟪x 1, x 6 - x 3⟫) = 0 := by
        nlinarith [mul_nonneg hqg.le (sub_nonneg.mpr h16), mul_nonneg N.hg.le (sub_nonneg.mpr h14)]
      have k2 : N.g * (⟪x 4, x 6 - x 3⟫ - ⟪x 1, x 6 - x 3⟫) = 0 := by
        nlinarith [mul_nonneg hqg.le (sub_nonneg.mpr h16), mul_nonneg N.hg.le (sub_nonneg.mpr h14)]
      have q1 := (mul_eq_zero.mp k1).resolve_left hqg.ne'
      have q2 := (mul_eq_zero.mp k2).resolve_left N.hg.ne'
      exact hg.noTriple (hm 3) (hm 6) (hm 1) (hm 4) (hm 6) (N.inj.ne (by decide))
        (N.inj.ne (by decide)) (N.inj.ne (by decide)) (N.inj.ne (by decide))
        ⟨by linarith, by linarith⟩
    · by_contra hc'
      simp only [not_or, not_lt] at hc'
      obtain ⟨h02, h42⟩ := hc'
      have ht2' : 0 < N.b * (N.p + N.r - 1) - N.q * (N.a - 1) := ht2
      linarith [mul_pos hc (sub_pos.mpr h60), mul_nonneg hqb.le (sub_nonneg.mpr h02),
        mul_nonneg N.hb.le (sub_nonneg.mpr h42), mul_pos ht2' he3']
  · -- `A` is robustly unimodal
    push Not at hs
    have K0 : 0 < N.q * (N.g + N.d - 1) + N.g := by nlinarith [mul_pos N.hq N.hgd]
    by_cases hN : NWS4 (quad ⟪x 6, N.vA⟫ ⟪x 3, N.vA⟫ ⟪x 5, N.vA⟫ ⟪x 4, N.vA⟫)
    · exact cert_F1s_A N hR1 hR2 hD hqg hg1 hqb hc hd1 hf03 hHA hN.isRobustUnimodal
    exfalso
    have hmeet : (x 6 + (N.g * N.q / (N.q * (N.g + N.d - 1) + N.g)) • (x 5 - x 6)) -
        (x 4 + (N.q * (N.g + N.d - 1) / (N.q * (N.g + N.d - 1) + N.g)) • (x 3 - x 4)) =
        (-1 / (N.q * (N.g + N.d - 1) + N.g)) • N.vA := by
      have K0' := K0.ne'
      simp only [vA, f03]
      nf_simp N
      ext k
      simp only [nfP, nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply,
        smul_eq_mul]
      field_simp
      ring
    simp only [NWS4, quad_0, quad_1, quad_2, quad_3, not_and_or, not_or, not_lt] at hN
    rw [inner_sub_left] at hs
    rcases hN with ⟨k1, k2, k3, k4⟩ | ⟨k1, k2, k3, k4⟩
    · -- `{6, 5}` weakly above `{3, 4}`
      exact not_weakSep_of_meet (d₀ := x 4) (d₁ := x 3) (e₀ := x 6) (e₁ := x 5) (w := N.vA)
        (div_pos (mul_pos N.hq N.hgd) K0).le ((div_le_one K0).mpr (by linarith [N.hg]))
        (div_pos (mul_pos N.hg N.hq) K0).le
        ((div_le_one K0).mpr (by nlinarith [hf03, mul_pos N.hg N.hr])) hmeet
        (div_neg_of_neg_of_pos (by norm_num) K0)
        (by simp only [vA]; exact nfV_ne_zero N.hD (Or.inl (ne_of_gt (mul_pos N.hg N.hp))))
        k2 k4 k1 k3
    · -- `{3, 4}` weakly above `{6, 5}`: `z6 ≤ z3`
      linarith

/-- **Lemma 19.5, `T_a`**: the vertex crossing `0235/046` at `0` (view `uA`), rim `(0, 6, 1, 5)`. -/
theorem cert_T6_Ta (N : NF16 x) (hR1 : 0 < (N.g - 1) * (N.p + N.r) - N.d * (N.q - 1))
    (hR2 : 0 < N.a * (N.q - 1) - (N.b - 1) * (N.p + N.r)) (hD : 0 < N.q * N.d - N.r * N.g)
    (hqg : 0 < N.q - N.g) (hg1 : 0 < N.g - 1) (hqb : 0 < N.q - N.b)
    (hc : 0 < N.q * (N.a - 1) - N.b * (N.p - 1)) (hd1 : 0 < 1 - N.d)
    (hf03 : 0 < -(N.q * (1 - N.d) + N.g * (N.r - 1))) (hb1 : 0 < N.b - 1)
    (hHA : 0 < (N.b - 1) * N.g * N.p * N.r + (N.q * (1 - N.d) + N.g * (N.r - 1)) *
      (N.a * (N.q - 1) - (N.b - 1) * N.p)) (hf15 : 0 < N.d * N.q - (N.g - 1) * (N.p + N.r - 1))
    (hpr : 0 < N.p + N.r - 1)
    (hz : IsRobustUnimodal (quad ⟪x 0, N.uA⟫ ⟪x 5, N.uA⟫ ⟪x 1, N.uA⟫ ⟪x 6, N.uA⟫)) : Cert16 x := by
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  have hr1 : 0 < -N.r + 1 := by
    by_contra hc; push Not at hc
    nlinarith [mul_pos N.hq hd1, mul_nonpos_of_nonneg_of_nonpos N.hg.le hc]
  refine Cert16.mkPQ (.inr 2) 0 5 1 6 (by decide) (N.namedAt_uA hσ) (rimCertPts_vquadσ (univ.image x) ({x 2, x 3, x 4} : Finset ℝ³) (u := N.uA)
      (by
        simp only [NF16.uA]
        exact nfV_ne_zero N.hD
          (Or.inl (ne_of_gt (by have := (by show 0 < N.p + N.r - 1; linarith [hpr]); linarith)))) hσ
    (mem_image 0) (mem_image 5) (mem_image 1) (mem_image 6)
    (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff])
        (by simp [N.inj.eq_iff]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hz ?_)
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
theorem cert_T6_A (N : NF16 x) (hR1 : 0 < (N.g - 1) * (N.p + N.r) - N.d * (N.q - 1))
    (hR2 : 0 < N.a * (N.q - 1) - (N.b - 1) * (N.p + N.r)) (hD : 0 < N.q * N.d - N.r * N.g)
    (hqg : 0 < N.q - N.g) (hg1 : 0 < N.g - 1) (hqb : 0 < N.q - N.b)
    (hc : 0 < N.q * (N.a - 1) - N.b * (N.p - 1)) (hd1 : 0 < 1 - N.d)
    (hf03 : 0 < -(N.q * (1 - N.d) + N.g * (N.r - 1))) (hb1 : 0 < N.b - 1)
    (hHA : 0 < (N.b - 1) * N.g * N.p * N.r + (N.q * (1 - N.d) + N.g * (N.r - 1)) *
      (N.a * (N.q - 1) - (N.b - 1) * N.p)) (hf15 : 0 < N.d * N.q - (N.g - 1) * (N.p + N.r - 1))
    (hpr : 0 < N.p + N.r - 1)
    (hz : IsRobustUnimodal (quint ⟪x 6, N.vA⟫ ⟪x 3, N.vA⟫ ⟪x 5, N.vA⟫ ⟪x 2, N.vA⟫ ⟪x 4, N.vA⟫)) : Cert16 x := by
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  have hga : 0 < -N.a * N.d * N.q ^ 2 + N.a * N.g * N.q * N.r + N.b * N.d * N.p * N.q - N.a * N.g *
      N.q + N.a * N.q ^ 2 - N.b * N.d * N.q + N.b * N.g * N.p + N.b * N.g * N.r - N.b * N.p * N.q +
      N.d * N.q ^ 2 - N.g * N.q * N.r - N.b * N.g + N.b * N.q + N.g * N.q - N.q ^ 2 :=
      by linarith [mul_pos (mul_pos N.hg N.hp) N.t0246, mul_pos N.t0146 hc]
  have h243 : 0 < -N.a * N.d * N.q ^ 2 + N.a * N.g * N.q * N.r + N.b * N.d * N.p * N.q - N.a * N.g *
      N.q + N.a * N.q ^ 2 + N.b * N.g * N.p - N.b * N.p * N.q := pos_of_mul_pos_r N.hab
      (by linarith [mul_pos N.hb hHA, mul_pos N.ha hga])
  refine Cert16.mkPQ5 (.inr 1) 6 3 5 2 4 (by decide) (N.namedAt_vA hσ) (rimCertPts_vquintσ (univ.image x) ({x 0, x 1} : Finset ℝ³) (u := N.vA)
      (by
        simp only [NF16.vA, NF16.f03]
        exact nfV_ne_zero N.hD (Or.inl (ne_of_gt
              (by have := (by show 0 < N.g * N.p; linarith [mul_pos (N.hg) N.hp]); linarith)))) hσ
    (mem_image 6) (mem_image 3) (mem_image 5) (mem_image 2) (mem_image 4)
    (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff])
        (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff]) ?_ ?_ hz ?_)
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
theorem cert_T6_Tc5 (N : NF16 x) (hR1 : 0 < (N.g - 1) * (N.p + N.r) - N.d * (N.q - 1))
    (hR2 : 0 < N.a * (N.q - 1) - (N.b - 1) * (N.p + N.r)) (hD : 0 < N.q * N.d - N.r * N.g)
    (hqg : 0 < N.q - N.g) (hg1 : 0 < N.g - 1) (hqb : 0 < N.q - N.b)
    (hc : 0 < N.q * (N.a - 1) - N.b * (N.p - 1)) (hd1 : 0 < 1 - N.d)
    (hf03 : 0 < -(N.q * (1 - N.d) + N.g * (N.r - 1))) (hb1 : 0 < N.b - 1)
    (hHA : 0 < (N.b - 1) * N.g * N.p * N.r + (N.q * (1 - N.d) + N.g * (N.r - 1)) *
      (N.a * (N.q - 1) - (N.b - 1) * N.p)) (hf15 : 0 < N.d * N.q - (N.g - 1) * (N.p + N.r - 1))
    (hpr : 0 < N.p + N.r - 1)
    (hT5 : 0 < N.d * (N.q * (N.a - 1) - N.b * (N.p - 1)) - (N.g - 1) * (N.a - 1) * N.r)
    (hz : IsRobustUnimodal (quint ⟪x 1, (x 5 - x 1)⟫ ⟪x 4, (x 5 - x 1)⟫ ⟪x 2, (x 5 - x 1)⟫ ⟪x 0,
            (x 5 - x 1)⟫ ⟪x 6, (x 5 - x 1)⟫)) : Cert16 x := by
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  have h426 : 0 < N.a * N.d * N.q - N.a * N.g * N.r - N.b * N.d * N.p + N.a * N.g + N.a * N.r - N.g
      * N.p - N.a + N.p := pos_of_mul_pos_r (mul_pos N.hr N.hab)
      (by linarith [mul_pos N.tB125 N.t0246, mul_pos hT5 N.t245_6])
  refine Cert16.mkPQ5 (.inl (1, 5)) 1 4 2 0 6 (by decide) (namedAt16_seg 1 5 hσ) (rimCertPts_equintσ (univ.image x) ({x 3} : Finset ℝ³) (u := (x 5 - x 1))
      (sub_ne_zero.mpr (N.inj.ne (by decide))) hσ (h := (-1 : ℝ)) (by norm_num) (by module)
      (mem_image 5)
    (mem_image 1) (mem_image 4) (mem_image 2) (mem_image 0) (mem_image 6)
    (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff])
        (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff]) ?_ ?_ hz ?_)
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

/-- `depthSep_sign` with weak separation: `l ⟪v, w⟫ ≤ 0`. -/
theorem weakSep_sign {d₀ d₁ e₀ e₁ w v : ℝ³} {s t l : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hm : (e₀ + t • (e₁ - e₀)) - (d₀ + s • (d₁ - d₀)) = l • v)
    (h : max ⟪e₀, w⟫ ⟪e₁, w⟫ ≤ min ⟪d₀, w⟫ ⟪d₁, w⟫) : l * ⟪v, w⟫ ≤ 0 := by
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

/-- **The pentagon `T_c` with one tie**: the open forms of (C1)–(C3) with at most one tied pair. -/
theorem quint_Tc_robust {z1 z4 z2 z0 z6 : ℝ}
    (hone : ∀ a b a' b', a ≠ b → a' ≠ b' → quint z1 z4 z2 z0 z6 a = quint z1 z4 z2 z0 z6 b →
      quint z1 z4 z2 z0 z6 a' = quint z1 z4 z2 z0 z6 b' → (a = a' ∧ b = b') ∨ (a = b' ∧ b = a'))
    (F1 : z1 < z4 ∨ z1 < z6) (F2 : z2 < z0 ∨ z6 < z0) (F3 : z4 < z1 ∨ z4 < z2 ∨ z0 < z2) :
    IsRobustUnimodal (quint z1 z4 z2 z0 z6) := by
  refine isRobustUnimodal_of_nhds hone
    (fun y => (y 0 < y 1 ∨ y 0 < y 4) ∧ (y 2 < y 3 ∨ y 4 < y 3) ∧
      (y 1 < y 0 ∨ y 1 < y 2 ∨ y 3 < y 2)) ?_ ?_
  · refine (?_ : ∀ᶠ y in 𝓝 _, _).and ((?_ : ∀ᶠ y in 𝓝 _, _).and ?_)
    · rcases F1 with h | h
      · exact (eventually_entry_lt (i := 0) (j := 1) h).mono fun y hy => Or.inl hy
      · exact (eventually_entry_lt (i := 0) (j := 4) h).mono fun y hy => Or.inr hy
    · rcases F2 with h | h
      · exact (eventually_entry_lt (i := 2) (j := 3) h).mono fun y hy => Or.inl hy
      · exact (eventually_entry_lt (i := 4) (j := 3) h).mono fun y hy => Or.inr hy
    · rcases F3 with h | h | h
      · exact (eventually_entry_lt (i := 1) (j := 0) h).mono fun y hy => Or.inl hy
      · exact (eventually_entry_lt (i := 1) (j := 2) h).mono fun y hy => Or.inr (Or.inl hy)
      · exact (eventually_entry_lt (i := 3) (j := 2) h).mono fun y hy => Or.inr (Or.inr hy)
  · intro y hy hinj
    have e : y = quint (y 0) (y 1) (y 2) (y 3) (y 4) := by
      funext i; rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;> rfl
    rw [e] at hinj ⊢
    obtain ⟨k1, k2, k3⟩ := hy
    refine quint_Tc_unimodal hinj (fun ⟨c1, c2⟩ => ?_) (fun ⟨c1, c2⟩ => ?_)
      (fun ⟨c1, c2, c3⟩ => ?_)
    · rcases k1 with k | k <;> linarith
    · rcases k2 with k | k <;> linarith
    · rcases k3 with k | k | k <;> linarith

/-- **The pentagon `A` with one tie**: the open forms of (A1), (A2′), (A3) with at most one tied
pair. -/
theorem quint_A_robust {z6 z3 z5 z2 z4 : ℝ}
    (hone : ∀ a b a' b', a ≠ b → a' ≠ b' → quint z6 z3 z5 z2 z4 a = quint z6 z3 z5 z2 z4 b →
      quint z6 z3 z5 z2 z4 a' = quint z6 z3 z5 z2 z4 b' → (a = a' ∧ b = b') ∨ (a = b' ∧ b = a'))
    (G1 : z3 < z5 ∨ z3 < z6) (G2 : z4 < z2 ∨ z5 < z2) (G3 : z6 < z4 ∨ z2 < z4) :
    IsRobustUnimodal (quint z6 z3 z5 z2 z4) := by
  refine isRobustUnimodal_of_nhds hone
    (fun y => (y 1 < y 2 ∨ y 1 < y 0) ∧ (y 4 < y 3 ∨ y 2 < y 3) ∧ (y 0 < y 4 ∨ y 3 < y 4)) ?_ ?_
  · refine (?_ : ∀ᶠ y in 𝓝 _, _).and ((?_ : ∀ᶠ y in 𝓝 _, _).and ?_)
    · rcases G1 with h | h
      · exact (eventually_entry_lt (i := 1) (j := 2) h).mono fun y hy => Or.inl hy
      · exact (eventually_entry_lt (i := 1) (j := 0) h).mono fun y hy => Or.inr hy
    · rcases G2 with h | h
      · exact (eventually_entry_lt (i := 4) (j := 3) h).mono fun y hy => Or.inl hy
      · exact (eventually_entry_lt (i := 2) (j := 3) h).mono fun y hy => Or.inr hy
    · rcases G3 with h | h
      · exact (eventually_entry_lt (i := 0) (j := 4) h).mono fun y hy => Or.inl hy
      · exact (eventually_entry_lt (i := 3) (j := 4) h).mono fun y hy => Or.inr hy
  · intro y hy hinj
    have e : y = quint (y 0) (y 1) (y 2) (y 3) (y 4) := by
      funext i; rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;> rfl
    rw [e] at hinj ⊢
    obtain ⟨k1, k2, k3⟩ := hy
    refine quint_A_unimodal hinj (fun ⟨c1, c2⟩ => ?_) (fun ⟨c1, c2⟩ => ?_) (fun ⟨c1, c2⟩ => ?_)
    · rcases k1 with k | k <;> linarith
    · rcases k2 with k | k <;> linarith
    · rcases k3 with k | k <;> linarith

set_option maxHeartbeats 4000000 in
/-- **Lemma 19.5 (the triple `T6`)** on `Ω_open` (`Ω ∩ {d < 1, b > 1, H_A > 0}`), with ties: one
of `T_a = 0235/046` at `0` (view `u_a`), `A = 036/146` at `6` (view `v_A`) and `T_c = K_1` at
`15` (view `u_c = 5 − 1`) is robustly unimodal.  If `⟪u_a, v_A⟫ < 0`, `T_a`'s diagonals are not
weakly separated (the two weak separations give `⟪u_a, v_A⟫ ≥ 0` or contradict the crossing,
`weakSep_sign`, `not_weakSep_of_meet`).  Otherwise, if `⟪u_c, v_A⟫ ≥ 0`, the open forms of
(C1)–(C3) hold (a weak (C1) would put `1, 4, 6` at one depth along `15`, against `TieSeg`)
and `T_c` is robustly unimodal with at most one tie; if `⟪u_c, v_A⟫ < 0`, the open forms of
(A1), (A2′), (A3) hold and `A` is robustly unimodal with at most one tie at `v_A`. -/
theorem cert_T6 (N : NF16 x) (O : Omega N) (hd1 : 0 < 1 - N.d) (hb1 : 0 < N.b - 1)
    (ha1 : N.a ≠ 1)
    (hf03 : 0 < -(N.q * (1 - N.d) + N.g * (N.r - 1)))
    (hHA : 0 < (N.b - 1) * N.g * N.p * N.r + (N.q * (1 - N.d) + N.g * (N.r - 1)) *
      (N.a * (N.q - 1) - (N.b - 1) * N.p))
    (hf15 : 0 < N.d * N.q - (N.g - 1) * (N.p + N.r - 1)) (hpr : 0 < N.p + N.r - 1)
    (hT5 : N.d * (N.q * (N.a - 1) - N.b * (N.p - 1)) - (N.g - 1) * (N.a - 1) * N.r ≠ 0)
    (hg : TieSeg (univ.image x))
    (hvA : OneTieAt (univ.image x) N.vA) : Cert16 x := by
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
  have hm : ∀ i, x i ∈ univ.image x := fun i => mem_image_of_mem x (mem_univ i)
  -- weak (C1): `1` weakly above `4` and `6` along `u_c` with `⟪u_c, v_A⟫ ≥ 0` puts `1, 4, 6` at
  -- one depth
  have C1w : ⟪x 4, x 5 - x 1⟫ ≤ ⟪x 1, x 5 - x 1⟫ → ⟪x 6, x 5 - x 1⟫ ≤ ⟪x 1, x 5 - x 1⟫ →
      0 ≤ ⟪x 5 - x 1, N.vA⟫ → False := by
    intro h4 h6 h0
    rw [real_inner_comm, iC1] at h0
    simp only [inner_neg_left, inner_sub_left, real_inner_smul_left] at h0
    have k1 : (N.q - N.g) * (⟪x 1, x 5 - x 1⟫ - ⟪x 6, x 5 - x 1⟫) = 0 := by
      nlinarith [mul_nonneg hqg.le (sub_nonneg.mpr h6), mul_nonneg N.hg.le (sub_nonneg.mpr h4)]
    have k2 : N.g * (⟪x 1, x 5 - x 1⟫ - ⟪x 4, x 5 - x 1⟫) = 0 := by
      nlinarith [mul_nonneg hqg.le (sub_nonneg.mpr h6), mul_nonneg N.hg.le (sub_nonneg.mpr h4)]
    have q1 := (mul_eq_zero.mp k1).resolve_left hqg.ne'
    have q2 := (mul_eq_zero.mp k2).resolve_left N.hg.ne'
    exact hg.noTriple (hm 1) (hm 5) (hm 1) (hm 4) (hm 6) (N.inj.ne (by decide))
      (N.inj.ne (by decide)) (N.inj.ne (by decide)) (N.inj.ne (by decide))
      ⟨by linarith, by linarith⟩
  by_cases h1 : ⟪N.uA, N.vA⟫ < 0
  · -- `T_a` is robustly unimodal
    by_cases hN : NWS4 (quad ⟪x 0, N.uA⟫ ⟪x 5, N.uA⟫ ⟪x 1, N.uA⟫ ⟪x 6, N.uA⟫)
    · exact cert_T6_Ta N hR1 hR2 hD hqg hg1 hqb hc hd1 hf03 hb1 hHA hf15 hpr hN.isRobustUnimodal
    exfalso
    have hKa : 0 < (N.g + N.d) * (N.p + N.r - 1) + N.q :=
        by linarith [mul_pos (add_pos N.hg N.hd) hpr, N.hq]
    have hKv : 0 < N.g * N.p * (N.g + N.d - 1) + N.t0146v := by linarith [mul_pos hgp N.hgd, ht']
    have hmA : (x 6 + (N.t0146v / ((N.g + N.d) * (N.p + N.r - 1) + N.q)) • (x 5 - x 6)) -
        (x 0 + ((N.p + N.q + N.r - 1) / ((N.g + N.d) * (N.p + N.r - 1) + N.q)) • (x 1 - x 0)) =
        (-(N.g + N.d - 1) / ((N.g + N.d) * (N.p + N.r - 1) + N.q)) • N.uA := by
      refine meet_of_smul hKa.ne' ?_
      simp only [t0146v, uA]
      nf_vec N
    have hmV : (x 6 + (N.g * N.t0146v / (N.g * N.p * (N.g + N.d - 1) + N.t0146v)) • (x 5 - x 6)) -
        (x 0 + (N.t0146v / (N.g * N.p * (N.g + N.d - 1) + N.t0146v)) • (x 1 - x 0)) =
        (-(N.g + N.d - 1) / (N.g * N.p * (N.g + N.d - 1) + N.t0146v)) • N.vA := by
      refine meet_of_smul hKv.ne' ?_
      simp only [t0146v, vA, f03]
      nf_vec N
    have huA0 : N.uA ≠ 0 := by
      simp only [uA]; exact nfV_ne_zero N.hD (Or.inl (ne_of_gt hpr))
    simp only [NWS4, quad_0, quad_1, quad_2, quad_3, not_and_or, not_or, not_lt] at hN
    rcases hN with ⟨k1, k2, k3, k4⟩ | ⟨k1, k2, k3, k4⟩
    · -- `{0, 1}` weakly above `{5, 6}`: `⟪v_A, u_a⟫ ≥ 0`
      have hl := weakSep_sign (d₀ := x 0) (d₁ := x 1) (e₀ := x 6) (e₁ := x 5) (v := N.vA)
        (w := N.uA) (div_pos ht' hKv).le ((div_le_one hKv).mpr (by linarith [mul_pos hgp N.hgd]))
        (div_pos (mul_pos N.hg ht') hKv).le
        ((div_le_one hKv).mpr (by
          have e : N.t0146v = N.g * N.p + N.f03 := by simp only [t0146v, f03]; ring
          rw [e]; linarith [mul_pos (mul_pos N.hg N.hp) N.hd, mul_pos hg1 hfv]))
        hmV (max_le (le_min k2 k4) (le_min k1 k3))
      have hl' : -(N.g + N.d - 1) / (N.g * N.p * (N.g + N.d - 1) + N.t0146v) < 0 :=
        div_neg_of_neg_of_pos (by linarith [N.hgd]) hKv
      rw [real_inner_comm] at h1
      nlinarith [mul_pos_of_neg_of_neg hl' h1]
    · -- `{5, 6}` weakly above `{0, 1}`: against the crossing
      exact not_weakSep_of_meet (d₀ := x 0) (d₁ := x 1) (e₀ := x 6) (e₁ := x 5) (w := N.uA)
        (div_pos N.t046_5 hKa).le ((div_le_one hKa).mpr (by linarith [mul_pos N.hgd hpr]))
        (div_pos ht' hKa).le
        ((div_le_one hKa).mpr (by simp only [t0146v]; linarith [mul_pos N.hd N.t046_5]))
        hmA (div_neg_of_neg_of_pos (by linarith [N.hgd]) hKa) huA0 k2 k1 k4 k3
  push Not at h1
  by_cases h2 : 0 ≤ ⟪x 5 - x 1, N.vA⟫
  · -- `T_c` is robustly unimodal
    rcases lt_or_gt_of_ne hT5 with h5 | h5
    · by_cases hN : NWS4 (quad ⟪x 1, (x 5 - x 1)⟫ ⟪x 4, (x 5 - x 1)⟫ ⟪x 0, (x 5 - x 1)⟫
          ⟪x 6, (x 5 - x 1)⟫)
      · exact cert_T6_Tc4 N hR1 hR2 hD hqg hg1 hqb hc hd1 hf03 hb1 hHA hf15 hpr
          (by linarith) hN.isRobustUnimodal
      exfalso
      simp only [NWS4, quad_0, quad_1, quad_2, quad_3, not_and_or, not_or, not_lt] at hN
      rcases hN with ⟨k1, k2, k3, k4⟩ | ⟨k1, k2, k3, k4⟩
      · exact C1w k1 k2 h2
      · have e := cone_inner3 (w := x 5 - x 1) iTc4
        simp only [inner_sub_left] at e
        linarith [mul_pos ht' huc', mul_nonneg hR1.le (sub_nonneg.mpr k3), mul_nonneg N.t145_0.le
              (sub_nonneg.mpr k4), mul_nonneg hf15.le (sub_nonneg.mpr k1)]
    · have hone := (hg.tie (x 1) (hm 1) (x 5) (hm 5) (N.inj.ne (by decide))).rim5 (hm 1) (hm 4)
        (hm 2) (hm 0) (hm 6) (quint_injective (N.inj.ne (by decide)) (N.inj.ne (by decide))
          (N.inj.ne (by decide)) (N.inj.ne (by decide)) (N.inj.ne (by decide))
          (N.inj.ne (by decide)) (N.inj.ne (by decide)) (N.inj.ne (by decide))
          (N.inj.ne (by decide)) (N.inj.ne (by decide)))
      refine cert_T6_Tc5 N hR1 hR2 hD hqg hg1 hqb hc hd1 hf03 hb1 hHA hf15 hpr h5
        (quint_Tc_robust hone ?_ ?_ ?_)
      · by_contra hc0
        simp only [not_or, not_lt] at hc0
        exact C1w hc0.1 hc0.2 h2
      · by_contra hc0
        simp only [not_or, not_lt] at hc0
        obtain ⟨h02, h06⟩ := hc0
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
        linarith [mul_nonneg (sub_pos.mpr hS2).le h2,
          mul_nonneg (mul_pos hg1 ht').le (sub_nonneg.mpr h02),
          mul_nonneg hn2.le (sub_nonneg.mpr h06), mul_pos (mul_pos N.hb ht') huc']
      · by_contra hc0
        simp only [not_or, not_lt] at hc0
        obtain ⟨h14, h24, h20⟩ := hc0
        have e := cone_inner3 (w := x 5 - x 1) iC3
        simp only [inner_sub_left, inner_neg_left] at e
        linarith [mul_pos N.t024_1 huc', mul_nonneg h5.le (sub_nonneg.mpr h14),
          mul_nonneg hc3.le (sub_nonneg.mpr h24), mul_nonneg N.tB125.le (sub_nonneg.mpr h20)]
  · -- `A` is robustly unimodal
    push Not at h2
    have hone := hvA.rim5 (hm 6) (hm 3) (hm 5) (hm 2) (hm 4)
      (quint_injective (N.inj.ne (by decide)) (N.inj.ne (by decide)) (N.inj.ne (by decide))
        (N.inj.ne (by decide)) (N.inj.ne (by decide)) (N.inj.ne (by decide))
        (N.inj.ne (by decide)) (N.inj.ne (by decide)) (N.inj.ne (by decide))
        (N.inj.ne (by decide)))
    refine cert_T6_A N hR1 hR2 hD hqg hg1 hqb hc hd1 hf03 hb1 hHA hf15 hpr
      (quint_A_robust hone ?_ ?_ ?_)
    · by_contra hc0
      simp only [not_or, not_lt] at hc0
      obtain ⟨h53, h63⟩ := hc0
      have e := congrArg (fun w => ⟪w, N.vA⟫) iA1
      simp only [inner_add_left, inner_sub_left, real_inner_smul_left] at e
      rw [inner_sub_left] at h2
      linarith [mul_nonneg hg1.le (sub_nonneg.mpr h53), mul_nonneg N.hd.le (sub_nonneg.mpr h63)]
    · by_contra hc0
      simp only [not_or, not_lt] at hc0
      obtain ⟨h24, h25⟩ := hc0
      have e := cone_inner3 (w := N.vA) iA2
      simp only [inner_sub_left, inner_neg_left] at e
      have hM : 0 < N.a * N.q - (N.b - 1) * (N.p + N.r - 1) := by linarith [N.hab]
      linarith [mul_nonneg hHA.le h1, mul_nonneg (mul_pos hM hfv).le (sub_nonneg.mpr h24),
        mul_nonneg hX1.le (sub_nonneg.mpr h25), mul_pos (mul_pos N.hr (show 0 < N.a + N.b - 1 +
          (N.a * (N.q - 1) - (N.b - 1) * (N.p + N.r)) by linarith [N.hab])) hvv]
    · by_contra hc0
      simp only [not_or, not_lt] at hc0
      obtain ⟨h46, h42⟩ := hc0
      have e := cone_inner3 (w := N.vA) iA3
      simp only [inner_sub_left, inner_neg_left] at e
      have hZ : 0 < N.g * N.p * N.t0246v + N.t0146v * (N.a * N.q - N.b * N.p) := by
        have : N.a * N.q - N.b * N.p = N.c36v + (N.q - N.b) := by simp only [c36v]; ring
        rw [this]; linarith [mul_pos hgp ht2', mul_pos ht' hc', mul_pos ht' hqb]
      linarith [mul_nonneg hZ.le h1,
        mul_nonneg (mul_pos (mul_pos N.hq hr1) ht').le (sub_nonneg.mpr h42),
        mul_nonneg hX1.le (sub_nonneg.mpr h46), mul_pos (mul_pos hr1 ht2') hvv]

end NF16

end Minimality

end
