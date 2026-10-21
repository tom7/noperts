module

public import Minimality.Type16NF

@[expose] public section

/-!
# Type 16: the Lemma E cover (`FEWER-FACES-PROOFS.md` §19.0–19.2)

In the normal form `NF16` (§19.0), each step of Theorem 19.2 names an edge crossing whose
two closings satisfy Lemma E (`isRupert_edgePairσ`), or a triangle closing
(`isRupert_edgeTriσ`).  Every orientation test is a polynomial in `(a, b, g, d, p, q, r)`
times the frame determinant `D` (`nf_test`); the sign of each polynomial on its region is
a type inequality, a defining inequality of the region, or a short identity (given in the
proofs, found with an exact LP over products of the hypotheses).

* `NF16.isRupert_E06`: off `R1 ∪ R2`, the pair at `06` (Proposition 14.3; `5` is always a
  corner, `1` hidden iff not `R1`, `2` hidden iff not `R2`).
* Theorem 19.2 in `R1`: step 1 (A, the planar closing `1356` at `14`, `isRupert_stepA`), step 2
  (U, `d > 1`: E35, `isRupert_stepU1a`, `_U1b`), step 3 (U, `d < 1`: E35, E02, E25, E03,
  `isRupert_stepU2`–`_U5`), step 4 (D, `c36 < 0`: E36, `isRupert_stepD1`), step 5 (D2–D4:
  E35, E25, E03; D5, D6: triangle closings at `16`, `15`; D7: `4` hidden at `35`;
  `isRupert_stepD2`–`_D7`).
* Lemma 19.1 (b), (c) (`g_gt_one`, `q_gt_b`), the special positions of the route (`Gen`), the
  residual `Omega` and the dispatch `isRupert_R1_or_omega`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Minimality

open scoped RealInnerProductSpace
open Finset

namespace NF16

variable {x : Fin 7 → ℝ³}

theorem mem_image (i : Fin 7) : x i ∈ univ.image x := Finset.mem_image_of_mem x (mem_univ i)

/-- No horizontal double normal at the view along any segment (`hnd` of the entry point). -/
def NoHDNEdges16 (x : Fin 7 → ℝ³) : Prop :=
  ∀ v ∈ univ.image x, ∀ w ∈ univ.image x, v ≠ w → NoHDNAt ((univ.image x).erase w) (w - v)

theorem NoHDNEdges16.fwd (N : NF16 x) (h : NoHDNEdges16 x) {v w : Fin 7} (hvw : v ≠ w) :
    NoHDNAt ((univ.image x).erase (x w)) (x w - x v) :=
  h _ (mem_image v) _ (mem_image w) (N.inj.ne hvw)

theorem NoHDNEdges16.bwd (N : NF16 x) (h : NoHDNEdges16 x) {v w : Fin 7} (hvw : v ≠ w) :
    NoHDNAt ((univ.image x).erase (x v)) (x w - x v) := by
  have := (h _ (mem_image w) _ (mem_image v) (N.inj.ne (Ne.symm hvw))).neg
  rwa [neg_sub] at this

/-- **Proposition 14.3 off `R1 ∪ R2`** (§19.0): at the view along `06` the far path is
`4, 5, 3` with `1`, `2` hidden, and `0`, `6` lie on opposite sides of the plane `345`. -/
theorem isRupert_E06 (N : NF16 x) (hR1 : N.R1 < 0) (hR2 : N.R2 < 0)
    (hg : GenPos (univ.image x))
    (hnd : NoHDNEdges16 x) : IsRupert (univ.image x) := by
  have hx := N.inj
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  have hz := depth_nodup4 (v := 0) (w := 6) (a := 4) (b := 3) (c := 5) hx hg (by decide)
  have N1 : 0 < -N.R1 := by linarith
  have N2 : 0 < -N.R2 := by linarith
  simp only [R1, R2] at N1 N2
  refine isRupert_edgePairσ (v := x 0) (w := x 6) (a := x 4) (b := x 3) (c := x 5) _ hσ
    (mem_image 0) (mem_image 6) (mem_image 4) (mem_image 3) (mem_image 5) ?_ ?_ ?_ ?_ ?_
    hz.1 hz.2 ?_ (hnd.fwd N (by decide)) (hnd.bwd N (by decide))
  · nf_test N hσD N.t046_5
  · nf_test N hσD (add_pos N.hp N.hr)
  · nf_test N hσD one_pos
  · nf_test N hσD N.hq
  · nf_simp N
    exact nf_E_le (P₁ := N.r) (P₂ := -N.p) (by simp only [det3c]; ring)
      (by simp only [det3c]; ring) (by nlinarith [N.hp, N.hr])
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    fin_cases i
    · exact Or.inl rfl
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_, ?_⟩)))))
      · nf_test N hσD N.t0146
      · nf_test N hσD N1
      · nf_test N hσD N.hd
      · nf_test N hσD N.hg
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_, ?_⟩)))))
      · nf_test N hσD N.t0246
      · nf_test N hσD N2
      · nf_test N hσD N.ha
      · nf_test N hσD N.hb
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact Or.inr (Or.inl rfl)

/-- step 1 (A) -/
theorem isRupert_stepA (N : NF16 x) (hR1 : 0 < (N.g - 1) * (N.p + N.r) - N.d * (N.q - 1))
    (hqg : 0 < N.g - N.q) (hrd : 0 < N.d - N.r)
    (hg : GenPos (univ.image x)) (hnd : NoHDNEdges16 x) : IsRupert (univ.image x) := by
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  have hz := depth_nodup4 (v := 1) (w := 4) (a := 6) (b := 5) (c := 3) N.inj hg (by decide)
  refine isRupert_edgePairσ (v := x 1) (w := x 4) (a := x 6) (b := x 5) (c := x 3) _ hσ
    (mem_image 1) (mem_image 4) (mem_image 6) (mem_image 5) (mem_image 3) ?_ ?_ ?_ ?_ ?_
    hz.1 hz.2 ?_ (hnd.fwd N (by decide)) (hnd.bwd N (by decide))
  · nf_test N hσD (by show 0 < N.g * N.p; linarith [mul_pos (N.hg) N.hp])
  · nf_test N hσD N.hp
  · nf_test N hσD (by show 0 < N.d * N.p; linarith [mul_pos (N.hd) N.hp])
  · nf_test N hσD (by show 0 < N.d * N.p + N.g * N.p - N.p; linarith [hR1, N.t145_0])
  · nf_simp N
    refine nf_E_le (P₁ := 0) (P₂ := -N.p) (by simp only [det3c]; ring) (by simp only [det3c]; ring)
        ?_
    simp
  intro z hz
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
  fin_cases i
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_, ?_⟩)))))
    · nf_test N hσD N.t0146
    · nf_test N hσD hqg
    · nf_test N hσD hrd
    · nf_test N hσD N.t145_0
  · exact Or.inl rfl
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_, ?_⟩)))))
    · nf_test N hσD N.t146_2
    · nf_test N hσD (by
            show 0 < N.a * N.g - N.a * N.q + N.b * N.p
            linarith [mul_pos (N.ha) hqg, mul_pos (N.hb) N.hp])
    · nf_test N hσD (by show 0 < N.a * N.d - N.a * N.r; linarith [mul_pos (N.ha) hrd])
    · nf_test N hσD N.tB125
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inl rfl))


/-- **Step 2, `a > 1`**: E35 with far path `2, 4, 1`. -/
theorem isRupert_stepU1a (N : NF16 x) (hR1 : 0 < (N.g - 1) * (N.p + N.r) - N.d * (N.q - 1))
    (hR2 : 0 < N.a * (N.q - 1) - (N.b - 1) * (N.p + N.r)) (hU : 0 < N.r * N.g - N.q * N.d)
    (hrd : 0 < N.r - N.d) (hd1 : 0 < N.d - 1) (ha1 : 0 < N.a - 1)
    (hg : GenPos (univ.image x)) (hnd : NoHDNEdges16 x) : IsRupert (univ.image x) := by
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  have hz := depth_nodup4 (v := 3) (w := 5) (a := 1) (b := 2) (c := 4) N.inj hg (by decide)
  refine isRupert_edgePairσ (v := x 3) (w := x 5) (a := x 1) (b := x 2) (c := x 4) _ hσ
    (mem_image 3) (mem_image 5) (mem_image 1) (mem_image 2) (mem_image 4) ?_ ?_ ?_ ?_ ?_
    hz.1 hz.2 ?_ (hnd.fwd N (by decide)) (hnd.bwd N (by decide))
  · nf_test N hσD (by show 0 < N.d * N.p; linarith [mul_pos (N.hd) N.hp])
  · nf_test N hσD (by
          show 0 < -N.a * N.d + N.a * N.r + N.d * N.p
          linarith [mul_pos (N.hd) N.hp, mul_pos (hrd) (N.ha)])
  · nf_test N hσD (by show 0 < N.a * N.r; linarith [mul_pos (N.ha) N.hr])
  · nf_test N hσD (by show 0 < N.a * N.d; linarith [mul_pos (N.ha) N.hd])
  · nf_simp N
    refine nf_E_le (P₁ := -N.a * N.d * N.q + N.a * N.g * N.r + N.b * N.d * N.p)
        (P₂ := -N.a * N.d * N.q + N.a * N.g * N.r + N.b * N.d * N.p + N.a * N.d - N.a * N.r - N.d *
          N.p) (by simp only [det3c]; ring) (by simp only [det3c]; ring) ?_
    exact mul_nonpos_of_nonneg_of_nonpos
        (le_of_lt (by
            show 0 < -N.a * N.d * N.q + N.a * N.g * N.r + N.b * N.d * N.p
            linarith [mul_pos (mul_pos (N.hb) N.hd) N.hp, mul_pos (hU) (N.ha)]))
        (by
          have := (by
              show 0 < N.a * N.d * N.q - N.a * N.g * N.r - N.b * N.d * N.p - N.a * N.d + N.a * N.r +
                N.d * N.p
              linarith [N.tB125])
          linarith)
  intro z hz
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
  fin_cases i
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inl ⟨(N.a - 1) / (N.a), (N.b) / (N.a), div_pos
                    (by show 0 < N.a - 1; linarith [ha1]) (by show 0 < N.a; linarith [N.ha]),
                    (div_lt_one (by show 0 < N.a; linarith [N.ha])).mpr
                    (by have := (by norm_num : (0 : ℝ) < 1); linarith), div_pos
                    (by show 0 < N.b; linarith [N.hb]) (by show 0 < N.a; linarith [N.ha]), Or.inr
                    (Or.inl ?_)⟩)))))
    have hden := (by show 0 < N.a; linarith [N.ha])
    nf_simp N
    ext k
    simp only
        [nfP, nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
    field_simp
    ring
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inl rfl)
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inl ⟨(1) / (N.d), (N.g) / (N.d), div_pos (by norm_num : (0 : ℝ) < 1)
                    (by show 0 < N.d; linarith [N.hd]),
                    (div_lt_one (by show 0 < N.d; linarith [N.hd])).mpr
                    (by have := (by show 0 < N.d - 1; linarith [hd1]); linarith), div_pos
                    (by show 0 < N.g; linarith [N.hg]) (by show 0 < N.d; linarith [N.hd]), Or.inl ?_⟩)))))
    have hden := (by show 0 < N.d; linarith [N.hd])
    nf_simp N
    ext k
    simp only
        [nfP, nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
    field_simp
    ring

/-- **Step 2, `a < 1`**: E35 with far path `0, 4, 1`. -/
theorem isRupert_stepU1b (N : NF16 x) (hR1 : 0 < (N.g - 1) * (N.p + N.r) - N.d * (N.q - 1))
    (hR2 : 0 < N.a * (N.q - 1) - (N.b - 1) * (N.p + N.r)) (hU : 0 < N.r * N.g - N.q * N.d)
    (hrd : 0 < N.r - N.d) (hd1 : 0 < N.d - 1) (ha1 : 0 < 1 - N.a)
    (hg : GenPos (univ.image x)) (hnd : NoHDNEdges16 x) : IsRupert (univ.image x) := by
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  have hz := depth_nodup4 (v := 3) (w := 5) (a := 1) (b := 0) (c := 4) N.inj hg (by decide)
  refine isRupert_edgePairσ (v := x 3) (w := x 5) (a := x 1) (b := x 0) (c := x 4) _ hσ
    (mem_image 3) (mem_image 5) (mem_image 1) (mem_image 0) (mem_image 4) ?_ ?_ ?_ ?_ ?_
    hz.1 hz.2 ?_ (hnd.fwd N (by decide)) (hnd.bwd N (by decide))
  · nf_test N hσD (by show 0 < N.d * N.p; linarith [mul_pos (N.hd) N.hp])
  · nf_test N hσD (by show 0 < N.d * N.p - N.d + N.r; linarith [N.t145_0, hU])
  · nf_test N hσD (by show 0 < N.r; linarith [N.hr])
  · nf_test N hσD (by show 0 < N.d; linarith [N.hd])
  · nf_simp N
    refine nf_E_le (P₁ := -N.d * N.q + N.g * N.r)
        (P₂ := -N.d * N.p - N.d * N.q + N.g * N.r + N.d - N.r) (by simp only [det3c]; ring)
        (by simp only [det3c]; ring) ?_
    exact mul_nonpos_of_nonneg_of_nonpos
        (le_of_lt (by show 0 < -N.d * N.q + N.g * N.r; linarith [hU]))
        (by
          have := (by show 0 < N.d * N.p + N.d * N.q - N.g * N.r - N.d + N.r; linarith [N.t145_0])
          linarith)
  intro z hz
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
  fin_cases i
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inl rfl))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inl ⟨(-N.a + 1) / (1), (N.a + N.b - 1) / (1), div_pos
                    (by show 0 < -N.a + 1; linarith [ha1]) (by norm_num : (0 : ℝ) < 1),
                    (div_lt_one (by norm_num : (0 : ℝ) < 1)).mpr
                    (by have := (by show 0 < N.a; linarith [N.ha]); linarith), div_pos
                    (by show 0 < N.a + N.b - 1; linarith [N.hab]) (by norm_num : (0 : ℝ) < 1),
                    Or.inr (Or.inr (Or.inr ?_))⟩)))))
    have hden := (by norm_num : (0 : ℝ) < 1)
    nf_simp N
    ext k
    simp only
        [nfP, nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
    field_simp
    ring
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inl rfl)
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inl ⟨(1) / (N.d), (N.g) / (N.d), div_pos (by norm_num : (0 : ℝ) < 1)
                    (by show 0 < N.d; linarith [N.hd]),
                    (div_lt_one (by show 0 < N.d; linarith [N.hd])).mpr
                    (by have := (by show 0 < N.d - 1; linarith [hd1]); linarith), div_pos
                    (by show 0 < N.g; linarith [N.hg]) (by show 0 < N.d; linarith [N.hd]), Or.inl ?_⟩)))))
    have hden := (by show 0 < N.d; linarith [N.hd])
    nf_simp N
    ext k
    simp only
        [nfP, nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
    field_simp
    ring

/-- **Step 3, `Z2 < 0`, `a > 1`**: E35 with far path `2, 4, 6`. -/
theorem isRupert_stepU2 (N : NF16 x) (hR1 : 0 < (N.g - 1) * (N.p + N.r) - N.d * (N.q - 1))
    (hR2 : 0 < N.a * (N.q - 1) - (N.b - 1) * (N.p + N.r)) (hU : 0 < N.r * N.g - N.q * N.d)
    (hrd : 0 < N.r - N.d) (hd1 : 0 < 1 - N.d) (hZ : 0 < N.b * N.p - N.a * N.q) (ha1 : 0 < N.a - 1)
    (hg : GenPos (univ.image x)) (hnd : NoHDNEdges16 x) : IsRupert (univ.image x) := by
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  have hz := depth_nodup4 (v := 3) (w := 5) (a := 6) (b := 2) (c := 4) N.inj hg (by decide)
  refine isRupert_edgePairσ (v := x 3) (w := x 5) (a := x 6) (b := x 2) (c := x 4) _ hσ
    (mem_image 3) (mem_image 5) (mem_image 6) (mem_image 2) (mem_image 4) ?_ ?_ ?_ ?_ ?_
    hz.1 hz.2 ?_ (hnd.fwd N (by decide)) (hnd.bwd N (by decide))
  · nf_test N hσD (by show 0 < N.p; linarith [N.hp])
  · nf_test N hσD (by show 0 < N.a * N.r - N.a + N.p; linarith [hZ, N.t245_6])
  · nf_test N hσD (by show 0 < N.a * N.r; linarith [mul_pos (N.ha) N.hr])
  · nf_test N hσD (by show 0 < N.a; linarith [N.ha])
  · nf_simp N
    refine nf_E_le (P₁ := -N.a * N.q + N.b * N.p)
        (P₂ := -N.a * N.q - N.a * N.r + N.b * N.p + N.a - N.p) (by simp only [det3c]; ring)
        (by simp only [det3c]; ring) ?_
    exact mul_nonpos_of_nonneg_of_nonpos
        (le_of_lt (by show 0 < -N.a * N.q + N.b * N.p; linarith [hZ]))
        (by
          have := (by show 0 < N.a * N.q + N.a * N.r - N.b * N.p - N.a + N.p; linarith [N.t245_6])
          linarith)
  intro z hz
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
  fin_cases i
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inl ⟨(N.a - 1) / (N.a), (N.b) / (N.a), div_pos
                    (by show 0 < N.a - 1; linarith [ha1]) (by show 0 < N.a; linarith [N.ha]),
                    (div_lt_one (by show 0 < N.a; linarith [N.ha])).mpr
                    (by have := (by norm_num : (0 : ℝ) < 1); linarith), div_pos
                    (by show 0 < N.b; linarith [N.hb]) (by show 0 < N.a; linarith [N.ha]), Or.inr
                    (Or.inl ?_)⟩)))))
    have hden := (by show 0 < N.a; linarith [N.ha])
    nf_simp N
    ext k
    simp only
        [nfP, nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
    field_simp
    ring
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inl ⟨(N.d) / (1), (N.d + N.g - 1) / (1), div_pos
                    (by show 0 < N.d; linarith [N.hd]) (by norm_num : (0 : ℝ) < 1),
                    (div_lt_one (by norm_num : (0 : ℝ) < 1)).mpr
                    (by have := (by show 0 < -N.d + 1; linarith [hd1]); linarith), div_pos
                    (by show 0 < N.d + N.g - 1; linarith [N.hgd]) (by norm_num : (0 : ℝ) < 1),
                    Or.inr (Or.inr (Or.inl ?_))⟩)))))
    have hden := (by norm_num : (0 : ℝ) < 1)
    nf_simp N
    ext k
    simp only
        [nfP, nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
    field_simp
    ring
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))

/-- **Step 3, `Z2 < 0`, `a < 1`**: E02 with far path `4, 6, 3`. -/
theorem isRupert_stepU3 (N : NF16 x) (hR1 : 0 < (N.g - 1) * (N.p + N.r) - N.d * (N.q - 1))
    (hR2 : 0 < N.a * (N.q - 1) - (N.b - 1) * (N.p + N.r)) (hU : 0 < N.r * N.g - N.q * N.d)
    (hrd : 0 < N.r - N.d) (hd1 : 0 < 1 - N.d) (hZ : 0 < N.b * N.p - N.a * N.q) (ha1 : 0 < 1 - N.a)
    (hg : GenPos (univ.image x)) (hnd : NoHDNEdges16 x) : IsRupert (univ.image x) := by
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  have hD02 : 0 < N.a * N.d * N.q - N.a * N.g * N.r - N.b * N.d * N.p + N.a * N.g - N.a * N.q + N.b
      * N.p - N.d * N.q + N.g * N.r - N.g + N.q := pos_of_mul_pos_r N.hd
      (by
        linarith [mul_pos (mul_pos ha1 N.hgd) hrd, mul_pos (mul_pos ha1 hd1) N.t145_0, mul_pos
            (mul_pos (mul_pos N.hd hd1) N.hab) N.hp])
  have hz := depth_nodup4 (v := 0) (w := 2) (a := 3) (b := 4) (c := 6) N.inj hg (by decide)
  refine isRupert_edgePairσ (v := x 0) (w := x 2) (a := x 3) (b := x 4) (c := x 6) _ hσ
    (mem_image 0) (mem_image 2) (mem_image 3) (mem_image 4) (mem_image 6) ?_ ?_ ?_ ?_ ?_
    hz.1 hz.2 ?_ (hnd.fwd N (by decide)) (hnd.bwd N (by decide))
  · nf_test N hσD (by show 0 < N.b; linarith [N.hb])
  · nf_test N hσD (by show 0 < -N.a * N.q + N.b * N.p + N.q; linarith [N.hq, hZ])
  · nf_test N hσD (by show 0 < -N.a * N.q + N.b * N.p + N.b * N.r - N.b + N.q; linarith [N.t0246])
  · nf_test N hσD (by show 0 < N.b * N.r; linarith [mul_pos (N.hb) N.hr])
  · nf_simp N
    refine nf_E_le (P₁ := N.q) (P₂ := N.a * N.q - N.b * N.p) (by simp only [det3c]; ring)
        (by simp only [det3c]; ring) ?_
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (by show 0 < N.q; linarith [N.hq]))
        (by have := (by show 0 < -N.a * N.q + N.b * N.p; linarith [hZ]); linarith)
  intro z hz
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
  fin_cases i
  · exact Or.inl rfl
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_, ?_⟩)))))
    · nf_test N hσD (by show 0 < N.b * N.d; linarith [mul_pos (N.hb) N.hd])
    · nf_test N hσD (by show 0 < -N.a * N.g + N.g; linarith [mul_pos (ha1) (N.hg)])
    · nf_test N hσD (by
            show 0 < N.a * N.d * N.q - N.a * N.g * N.r - N.b * N.d * N.p + N.a * N.g - N.a * N.q +
              N.b * N.p - N.d * N.q + N.g * N.r - N.g + N.q
            linarith [hD02])
    · nf_test N hσD (by
            show 0 < -N.a * N.d * N.q + N.a * N.g * N.r + N.b * N.d * N.p - N.b * N.d + N.b * N.r +
              N.d * N.q - N.g * N.r
            linarith [N.t024_1])
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inl ⟨(N.a + N.b - 1) / (N.b), (N.a) / (N.b), div_pos
                    (by show 0 < N.a + N.b - 1; linarith [N.hab])
                    (by show 0 < N.b; linarith [N.hb]),
                    (div_lt_one (by show 0 < N.b; linarith [N.hb])).mpr
                    (by have := (by show 0 < -N.a + 1; linarith [ha1]); linarith), div_pos
                    (by show 0 < N.a; linarith [N.ha]) (by show 0 < N.b; linarith [N.hb]), Or.inr
                    (Or.inr (Or.inl ?_))⟩)))))
    have hden := (by show 0 < N.b; linarith [N.hb])
    nf_simp N
    ext k
    simp only
        [nfP, nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
    field_simp
    ring
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

/-- **Step 3, `Z2 > 0`, `b < 1`**: E25 with far path `4, 6, 3`. -/
theorem isRupert_stepU4 (N : NF16 x) (hR1 : 0 < (N.g - 1) * (N.p + N.r) - N.d * (N.q - 1))
    (hR2 : 0 < N.a * (N.q - 1) - (N.b - 1) * (N.p + N.r)) (hU : 0 < N.r * N.g - N.q * N.d)
    (hrd : 0 < N.r - N.d) (hd1 : 0 < 1 - N.d) (hZ : 0 < N.a * N.q - N.b * N.p) (hb1 : 0 < 1 - N.b)
    (hg : GenPos (univ.image x)) (hnd : NoHDNEdges16 x) : IsRupert (univ.image x) := by
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  have hf25 : 0 < -N.a * N.d * N.q + N.a * N.g * N.r + N.b * N.d * N.p - N.a * N.g + N.a * N.q - N.b
      * N.p - N.d * N.p + N.p := pos_of_mul_pos_r N.hd
      (by linarith [mul_pos hd1 N.tB125, mul_pos (mul_pos N.ha N.hgd) hrd])
  have hz := depth_nodup4 (v := 2) (w := 5) (a := 3) (b := 4) (c := 6) N.inj hg (by decide)
  refine isRupert_edgePairσ (v := x 2) (w := x 5) (a := x 3) (b := x 4) (c := x 6) _ hσ
    (mem_image 2) (mem_image 5) (mem_image 3) (mem_image 4) (mem_image 6) ?_ ?_ ?_ ?_ ?_
    hz.1 hz.2 ?_ (hnd.fwd N (by decide)) (hnd.bwd N (by decide))
  · nf_test N hσD (by show 0 < N.a; linarith [N.ha])
  · nf_test N hσD (by show 0 < N.a * N.q - N.b * N.p + N.p; linarith [N.hp, hZ])
  · nf_test N hσD (by show 0 < N.a * N.q + N.a * N.r - N.b * N.p - N.a + N.p; linarith [N.t245_6])
  · nf_test N hσD (by show 0 < N.a * N.r; linarith [mul_pos (N.ha) N.hr])
  · nf_simp N
    refine nf_E_le (P₁ := N.a * N.q - N.b * N.p) (P₂ := -N.p) (by simp only [det3c]; ring)
        (by simp only [det3c]; ring) ?_
    exact mul_nonpos_of_nonneg_of_nonpos
        (le_of_lt (by show 0 < N.a * N.q - N.b * N.p; linarith [hZ]))
        (by have := (by show 0 < N.p; linarith [N.hp]); linarith)
  intro z hz
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
  fin_cases i
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inl ⟨(N.a + N.b - 1) / (N.a), (N.b) / (N.a), div_pos
                    (by show 0 < N.a + N.b - 1; linarith [N.hab])
                    (by show 0 < N.a; linarith [N.ha]),
                    (div_lt_one (by show 0 < N.a; linarith [N.ha])).mpr
                    (by have := (by show 0 < -N.b + 1; linarith [hb1]); linarith), div_pos
                    (by show 0 < N.b; linarith [N.hb]) (by show 0 < N.a; linarith [N.ha]), Or.inl ?_⟩)))))
    have hden := (by show 0 < N.a; linarith [N.ha])
    nf_simp N
    ext k
    simp only
        [nfP, nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
    field_simp
    ring
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_, ?_⟩)))))
    · nf_test N hσD (by show 0 < N.a * N.d; linarith [mul_pos (N.ha) N.hd])
    · nf_test N hσD (by show 0 < N.a * N.g; linarith [mul_pos (N.ha) N.hg])
    · nf_test N hσD (by
            show 0 < -N.a * N.d * N.q + N.a * N.g * N.r + N.b * N.d * N.p - N.a * N.g + N.a * N.q -
              N.b * N.p - N.d * N.p + N.p
            linarith [hf25])
    · nf_test N hσD (by
            show 0 < N.a * N.d * N.q - N.a * N.g * N.r - N.b * N.d * N.p - N.a * N.d + N.a * N.r +
              N.d * N.p
            linarith [N.tB125])
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))


/-- **Step 3, `Z2 > 0`, `b > 1`**: E03 with far path `2, 4, 6`. -/
theorem isRupert_stepU5 (N : NF16 x) (hR1 : 0 < (N.g - 1) * (N.p + N.r) - N.d * (N.q - 1))
    (hR2 : 0 < N.a * (N.q - 1) - (N.b - 1) * (N.p + N.r)) (hU : 0 < N.r * N.g - N.q * N.d)
    (hrd : 0 < N.r - N.d) (hd1 : 0 < 1 - N.d) (hZ : 0 < N.a * N.q - N.b * N.p) (hb1 : 0 < N.b - 1)
    (hg : GenPos (univ.image x)) (hnd : NoHDNEdges16 x) : IsRupert (univ.image x) := by
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  have hqg : 0 < -N.g + N.q := by
    have hqb : 0 < N.q - N.b := by
      by_contra hc; push Not at hc
      have e : N.b * (1 - N.b) * (N.b * (N.p + N.r - 1) - N.q * (N.a - 1)) - N.b ^ 2 *
          (N.a * (N.q - 1) - (N.b - 1) * (N.p + N.r)) = N.b * (N.a + N.b - 1) * (N.b - N.q) :=
          by ring
      have := mul_nonneg (mul_pos N.hb N.hab).le (show 0 ≤ N.b - N.q by linarith)
      nlinarith [mul_pos (mul_pos N.hb hb1) N.t0246, mul_pos (mul_pos N.hb N.hb) hR2]
    rcases le_or_gt N.g 1 with hg1 | hg1
    · linarith
    · exact pos_of_mul_pos_r (mul_pos N.ha N.hd)
          (by
            linarith [N.tB125, mul_pos (mul_pos N.hd N.hp) hb1, mul_pos
                (mul_pos N.ha (sub_pos.mpr hg1)) hrd])
  have hf03 : 0 < -N.d * N.q + N.g * N.r - N.g + N.q := by linarith [hqg, hU]
  have hz := depth_nodup4 (v := 0) (w := 3) (a := 6) (b := 2) (c := 4) N.inj hg (by decide)
  refine isRupert_edgePairσ (v := x 0) (w := x 3) (a := x 6) (b := x 2) (c := x 4) _ hσ
    (mem_image 0) (mem_image 3) (mem_image 6) (mem_image 2) (mem_image 4) ?_ ?_ ?_ ?_ ?_
    hz.1 hz.2 ?_ (hnd.fwd N (by decide)) (hnd.bwd N (by decide))
  · nf_test N hσD (by show 0 < N.q; linarith [N.hq])
  · nf_test N hσD (by show 0 < N.b * N.r - N.b + N.q; linarith [N.t0246, hZ])
  · nf_test N hσD (by show 0 < N.b * N.r; linarith [mul_pos (N.hb) N.hr])
  · nf_test N hσD (by show 0 < N.b; linarith [N.hb])
  · nf_simp N
    refine nf_E_le (P₁ := -N.a * N.q + N.b * N.p + N.b * N.r - N.b + N.q)
        (P₂ := -N.a * N.q + N.b * N.p) (by simp only [det3c]; ring) (by simp only [det3c]; ring) ?_
    exact mul_nonpos_of_nonneg_of_nonpos
        (le_of_lt (by show 0 < -N.a * N.q + N.b * N.p + N.b * N.r - N.b + N.q; linarith [N.t0246]))
        (by have := (by show 0 < N.a * N.q - N.b * N.p; linarith [hZ]); linarith)
  intro z hz
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
  fin_cases i
  · exact Or.inl rfl
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_, ?_⟩)))))
    · nf_test N hσD (by show 0 < N.g; linarith [N.hg])
    · nf_test N hσD (by show 0 < -N.d * N.q + N.g * N.r - N.g + N.q; linarith [hf03])
    · nf_test N hσD (pos_of_mul_pos_r (N.ha)
            (by
              show 0 < (-N.b * N.d + N.b * N.r + N.d * N.q - N.g * N.r) * (N.a)
              linarith
                [N.tB125, mul_pos (mul_pos (hrd) (hb1)) (N.ha), mul_pos (hb1) (mul_pos (N.hd) N.hp)]))
    · nf_test N hσD (by show 0 < N.b * N.d; linarith [mul_pos (N.hb) N.hd])
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inl ⟨(N.b - 1) / (N.b), (N.a) / (N.b), div_pos
                    (by show 0 < N.b - 1; linarith [hb1]) (by show 0 < N.b; linarith [N.hb]),
                    (div_lt_one (by show 0 < N.b; linarith [N.hb])).mpr
                    (by have := (by norm_num : (0 : ℝ) < 1); linarith), div_pos
                    (by show 0 < N.a; linarith [N.ha]) (by show 0 < N.b; linarith [N.hb]), Or.inr
                    (Or.inr (Or.inr ?_))⟩)))))
    have hden := (by show 0 < N.b; linarith [N.hb])
    nf_simp N
    ext k
    simp only
        [nfP, nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
    field_simp
    ring
  · exact Or.inr (Or.inr (Or.inl rfl))

/-- **Step 5, D2**: E35 with far path `2, 4, 1`. -/
theorem isRupert_stepD2 (N : NF16 x) (hR1 : 0 < (N.g - 1) * (N.p + N.r) - N.d * (N.q - 1))
    (hR2 : 0 < N.a * (N.q - 1) - (N.b - 1) * (N.p + N.r)) (hD : 0 < N.q * N.d - N.r * N.g)
    (hqg : 0 < N.q - N.g) (hg1 : 0 < N.g - 1) (hqb : 0 < N.q - N.b)
    (hc : 0 < N.q * (N.a - 1) - N.b * (N.p - 1)) (ha1 : 0 < N.a - 1) (hd1 : 0 < N.d - 1)
    (hpl : 0 < N.p * N.b * N.d + N.r * N.g * N.a - N.q * N.a * N.d)
    (hg : GenPos (univ.image x)) (hnd : NoHDNEdges16 x) : IsRupert (univ.image x) := by
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  have hz := depth_nodup4 (v := 3) (w := 5) (a := 1) (b := 2) (c := 4) N.inj hg (by decide)
  refine isRupert_edgePairσ (v := x 3) (w := x 5) (a := x 1) (b := x 2) (c := x 4) _ hσ
    (mem_image 3) (mem_image 5) (mem_image 1) (mem_image 2) (mem_image 4) ?_ ?_ ?_ ?_ ?_
    hz.1 hz.2 ?_ (hnd.fwd N (by decide)) (hnd.bwd N (by decide))
  · nf_test N hσD (by show 0 < N.d * N.p; linarith [mul_pos (N.hd) N.hp])
  · nf_test N hσD (pos_of_mul_pos_r (N.hq)
          (by
            show 0 < (-N.a * N.d + N.a * N.r + N.d * N.p) * (N.q)
            linarith [mul_pos (hqg) (mul_pos (N.ha) N.hr), hpl, mul_pos (hqb) (mul_pos (N.hd) N.hp)]))
  · nf_test N hσD (by show 0 < N.a * N.r; linarith [mul_pos (N.ha) N.hr])
  · nf_test N hσD (by show 0 < N.a * N.d; linarith [mul_pos (N.ha) N.hd])
  · nf_simp N
    refine nf_E_le (P₁ := -N.a * N.d * N.q + N.a * N.g * N.r + N.b * N.d * N.p)
        (P₂ := -N.a * N.d * N.q + N.a * N.g * N.r + N.b * N.d * N.p + N.a * N.d - N.a * N.r - N.d *
          N.p) (by simp only [det3c]; ring) (by simp only [det3c]; ring) ?_
    exact mul_nonpos_of_nonneg_of_nonpos
        (le_of_lt (by show 0 < -N.a * N.d * N.q + N.a * N.g * N.r + N.b * N.d * N.p; linarith [hpl]))
        (by
          have := (by
              show 0 < N.a * N.d * N.q - N.a * N.g * N.r - N.b * N.d * N.p - N.a * N.d + N.a * N.r +
                N.d * N.p
              linarith [N.tB125])
          linarith)
  intro z hz
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
  fin_cases i
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inl ⟨(N.a - 1) / (N.a), (N.b) / (N.a), div_pos
                    (by show 0 < N.a - 1; linarith [ha1]) (by show 0 < N.a; linarith [N.ha]),
                    (div_lt_one (by show 0 < N.a; linarith [N.ha])).mpr
                    (by have := (by norm_num : (0 : ℝ) < 1); linarith), div_pos
                    (by show 0 < N.b; linarith [N.hb]) (by show 0 < N.a; linarith [N.ha]), Or.inr
                    (Or.inl ?_)⟩)))))
    have hden := (by show 0 < N.a; linarith [N.ha])
    nf_simp N
    ext k
    simp only
        [nfP, nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
    field_simp
    ring
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inl rfl)
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inl ⟨(1) / (N.d), (N.g) / (N.d), div_pos (by norm_num : (0 : ℝ) < 1)
                    (by show 0 < N.d; linarith [N.hd]),
                    (div_lt_one (by show 0 < N.d; linarith [N.hd])).mpr
                    (by have := (by show 0 < N.d - 1; linarith [hd1]); linarith), div_pos
                    (by show 0 < N.g; linarith [N.hg]) (by show 0 < N.d; linarith [N.hd]), Or.inl ?_⟩)))))
    have hden := (by show 0 < N.d; linarith [N.hd])
    nf_simp N
    ext k
    simp only
        [nfP, nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
    field_simp
    ring

/-- **Step 5, D3**: E25 with far path `4, 6, 3`. -/
theorem isRupert_stepD3 (N : NF16 x) (hR1 : 0 < (N.g - 1) * (N.p + N.r) - N.d * (N.q - 1))
    (hR2 : 0 < N.a * (N.q - 1) - (N.b - 1) * (N.p + N.r)) (hD : 0 < N.q * N.d - N.r * N.g)
    (hqg : 0 < N.q - N.g) (hg1 : 0 < N.g - 1) (hqb : 0 < N.q - N.b)
    (hc : 0 < N.q * (N.a - 1) - N.b * (N.p - 1)) (hb1 : 0 < 1 - N.b)
    (hf : 0 < (1 - N.d) * (N.a * N.q + (1 - N.b) * N.p) + N.a * N.g * (N.r - 1))
    (hg : GenPos (univ.image x)) (hnd : NoHDNEdges16 x) : IsRupert (univ.image x) := by
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  have hz := depth_nodup4 (v := 2) (w := 5) (a := 3) (b := 4) (c := 6) N.inj hg (by decide)
  refine isRupert_edgePairσ (v := x 2) (w := x 5) (a := x 3) (b := x 4) (c := x 6) _ hσ
    (mem_image 2) (mem_image 5) (mem_image 3) (mem_image 4) (mem_image 6) ?_ ?_ ?_ ?_ ?_
    hz.1 hz.2 ?_ (hnd.fwd N (by decide)) (hnd.bwd N (by decide))
  · nf_test N hσD (by show 0 < N.a; linarith [N.ha])
  · nf_test N hσD (by
          show 0 < N.a * N.q - N.b * N.p + N.p
          linarith [hc, N.hp, mul_pos (hqb) (N.hb), mul_pos (hqb) (N.ha), mul_pos (hb1) (N.hp),
              mul_pos (N.hab) (N.hb), mul_pos (hb1) (N.hq)])
  · nf_test N hσD (by show 0 < N.a * N.q + N.a * N.r - N.b * N.p - N.a + N.p; linarith [N.t245_6])
  · nf_test N hσD (by show 0 < N.a * N.r; linarith [mul_pos (N.ha) N.hr])
  · nf_simp N
    refine nf_E_le (P₁ := N.a * N.q - N.b * N.p) (P₂ := -N.p) (by simp only [det3c]; ring)
        (by simp only [det3c]; ring) ?_
    exact mul_nonpos_of_nonneg_of_nonpos
        (le_of_lt (by show 0 < N.a * N.q - N.b * N.p; linarith [hb1, hqg, hc, hg1]))
        (by have := (by show 0 < N.p; linarith [N.hp]); linarith)
  intro z hz
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
  fin_cases i
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inl ⟨(N.a + N.b - 1) / (N.a), (N.b) / (N.a), div_pos
                    (by show 0 < N.a + N.b - 1; linarith [N.hab])
                    (by show 0 < N.a; linarith [N.ha]),
                    (div_lt_one (by show 0 < N.a; linarith [N.ha])).mpr
                    (by have := (by show 0 < -N.b + 1; linarith [hb1]); linarith), div_pos
                    (by show 0 < N.b; linarith [N.hb]) (by show 0 < N.a; linarith [N.ha]), Or.inl ?_⟩)))))
    have hden := (by show 0 < N.a; linarith [N.ha])
    nf_simp N
    ext k
    simp only
        [nfP, nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
    field_simp
    ring
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_, ?_⟩)))))
    · nf_test N hσD (by show 0 < N.a * N.d; linarith [mul_pos (N.ha) N.hd])
    · nf_test N hσD (by show 0 < N.a * N.g; linarith [mul_pos (N.ha) N.hg])
    · nf_test N hσD (by
            show 0 < -N.a * N.d * N.q + N.a * N.g * N.r + N.b * N.d * N.p - N.a * N.g + N.a * N.q -
              N.b * N.p - N.d * N.p + N.p
            linarith [hf])
    · nf_test N hσD (by
            show 0 < N.a * N.d * N.q - N.a * N.g * N.r - N.b * N.d * N.p - N.a * N.d + N.a * N.r +
              N.d * N.p
            linarith [N.tB125])
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))


/-- **Step 5, D5**: the triangle `1, 4, 5` at `16`. -/
theorem isRupert_stepD5 (N : NF16 x) (hR1 : 0 < (N.g - 1) * (N.p + N.r) - N.d * (N.q - 1))
    (hR2 : 0 < N.a * (N.q - 1) - (N.b - 1) * (N.p + N.r)) (hD : 0 < N.q * N.d - N.r * N.g)
    (hqg : 0 < N.q - N.g) (hg1 : 0 < N.g - 1) (hqb : 0 < N.q - N.b)
    (hc : 0 < N.q * (N.a - 1) - N.b * (N.p - 1)) (hd1 : 0 < N.d - 1)
    (hf : 0 < N.a * N.d * N.q - N.a * N.g * N.r - N.b * N.d * N.p - N.a * N.d - N.a * N.q + N.b *
      N.p + N.d * N.p + N.a - N.p)
    (hg : GenPos (univ.image x)) (hnd : NoHDNEdges16 x) : IsRupert (univ.image x) := by
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  have hz := depth_nodup3 (v := 1) (w := 6) (a := 5) (b := 4) N.inj hg (by decide)
  refine isRupert_edgeTriσ (v := x 1) (w := x 6) (a := x 5) (b := x 4) _ hσ
    (mem_image 1) (mem_image 6) (mem_image 5) (mem_image 4) ?_ hz ?_ (hnd.fwd N (by decide))
  · nf_test N hσD (by show 0 < N.d * N.p + N.g * N.p - N.p; linarith [mul_pos (N.hgd) (N.hp)])
  intro z hz
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
  fin_cases i
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩))))
    · nf_test N hσD (by show 0 < N.d + N.g - 1; linarith [N.hgd])
    · nf_test N hσD (pos_of_mul_pos_r (N.ha)
            (by
              show 0 < (N.d * N.p + N.d * N.q - N.g * N.r - N.d - N.p - N.q + 1) * (N.a)
              linarith [hf, mul_pos (mul_pos (N.hab) (hd1)) (N.hp)]))
    · nf_test N hσD (by show 0 < -N.d * N.q + N.g * N.p + N.g * N.r - N.g + N.q; linarith [N.t0146])
  · exact Or.inl rfl
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩))))
    · nf_test N hσD (by show 0 < N.a * N.d + N.a * N.g - N.a; linarith [mul_pos (N.hgd) (N.ha)])
    · nf_test N hσD (by
            show 0 < N.a * N.d * N.q - N.a * N.g * N.r - N.b * N.d * N.p - N.a * N.d - N.a * N.q +
              N.b * N.p + N.d * N.p + N.a - N.p
            linarith [hf])
    · nf_test N hσD (by
            show 0 < -N.a * N.d * N.q + N.a * N.g * N.r + N.b * N.d * N.p - N.a * N.g + N.a * N.q -
              N.b * N.p + N.g * N.p
            linarith [N.t146_2])
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(N.g) / (N.d + N.g - 1), (1) / (N.d + N.g - 1), div_pos
                  (by show 0 < N.g; linarith [N.hg]) (by show 0 < N.d + N.g - 1; linarith [N.hgd]),
                  (div_lt_one (by show 0 < N.d + N.g - 1; linarith [N.hgd])).mpr
                  (by have := (by show 0 < N.d - 1; linarith [hd1]); linarith), div_pos
                  (by norm_num : (0 : ℝ) < 1) (by show 0 < N.d + N.g - 1; linarith [N.hgd]), Or.inr
                  (Or.inr (Or.inl ?_))⟩))))
    have hden := (by show 0 < N.d + N.g - 1; linarith [N.hgd])
    nf_simp N
    ext k
    simp only
        [nfP, nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
    field_simp
    ring
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inl rfl)

/-- **Step 5, D7**: `4` hidden at `35`, the triangle `3, 0, 6`. -/
theorem isRupert_stepD7 (N : NF16 x) (hR1 : 0 < (N.g - 1) * (N.p + N.r) - N.d * (N.q - 1))
    (hR2 : 0 < N.a * (N.q - 1) - (N.b - 1) * (N.p + N.r)) (hD : 0 < N.q * N.d - N.r * N.g)
    (hqg : 0 < N.q - N.g) (hg1 : 0 < N.g - 1) (hqb : 0 < N.q - N.b)
    (hc : 0 < N.q * (N.a - 1) - N.b * (N.p - 1)) (ha1 : 0 < 1 - N.a) (hd1 : 0 < 1 - N.d)
    (hpr : 0 < 1 - N.p - N.r)
    (hg : GenPos (univ.image x)) (hnd : NoHDNEdges16 x) : IsRupert (univ.image x) := by
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  have hz := depth_nodup3 (v := 3) (w := 5) (a := 6) (b := 0) N.inj hg (by decide)
  refine isRupert_edgeTriσ (v := x 3) (w := x 5) (a := x 6) (b := x 0) _ hσ
    (mem_image 3) (mem_image 5) (mem_image 6) (mem_image 0) ?_ hz ?_ (hnd.fwd N (by decide))
  · nf_test N hσD (by norm_num : (0 : ℝ) < 1)
  intro z hz
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
  fin_cases i
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(N.d) / (1), (N.d + N.g - 1) / (1), div_pos (by show 0 < N.d; linarith [N.hd])
                  (by norm_num : (0 : ℝ) < 1), (div_lt_one (by norm_num : (0 : ℝ) < 1)).mpr
                  (by have := (by show 0 < -N.d + 1; linarith [hd1]); linarith), div_pos
                  (by show 0 < N.d + N.g - 1; linarith [N.hgd]) (by norm_num : (0 : ℝ) < 1), Or.inr
                  (Or.inr (Or.inl ?_))⟩))))
    have hden := (by norm_num : (0 : ℝ) < 1)
    nf_simp N
    ext k
    simp only
        [nfP, nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
    field_simp
    ring
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(-N.a + 1) / (1), (N.a + N.b - 1) / (1), div_pos
                  (by show 0 < -N.a + 1; linarith [ha1]) (by norm_num : (0 : ℝ) < 1),
                  (div_lt_one (by norm_num : (0 : ℝ) < 1)).mpr
                  (by have := (by show 0 < N.a; linarith [N.ha]); linarith), div_pos
                  (by show 0 < N.a + N.b - 1; linarith [N.hab]) (by norm_num : (0 : ℝ) < 1), Or.inr
                  (Or.inr (Or.inr ?_))⟩))))
    have hden := (by norm_num : (0 : ℝ) < 1)
    nf_simp N
    ext k
    simp only
        [nfP, nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
    field_simp
    ring
  · exact Or.inl rfl
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩))))
    · nf_test N hσD (by show 0 < N.p; linarith [N.hp])
    · nf_test N hσD (by show 0 < -N.p - N.r + 1; linarith [hpr])
    · nf_test N hσD (by show 0 < N.r; linarith [N.hr])
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))


/-- **Step 4, `c36 < 0`**: E36 with far path `0, 4, 1`. -/
theorem isRupert_stepD1 (N : NF16 x) (hR1 : 0 < (N.g - 1) * (N.p + N.r) - N.d * (N.q - 1))
    (hR2 : 0 < N.a * (N.q - 1) - (N.b - 1) * (N.p + N.r)) (hD : 0 < N.q * N.d - N.r * N.g)
    (hqg : 0 < N.q - N.g) (hg1 : 0 < N.g - 1) (hqb : 0 < N.q - N.b)
    (hc : 0 < N.b * (N.p - 1) - N.q * (N.a - 1))
    (hg : GenPos (univ.image x)) (hnd : NoHDNEdges16 x) : IsRupert (univ.image x) := by
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  have hz := depth_nodup4 (v := 3) (w := 6) (a := 0) (b := 1) (c := 4) N.inj hg (by decide)
  refine isRupert_edgePairσ (v := x 3) (w := x 6) (a := x 0) (b := x 1) (c := x 4) _ hσ
    (mem_image 3) (mem_image 6) (mem_image 0) (mem_image 1) (mem_image 4) ?_ ?_ ?_ ?_ ?_
    hz.1 hz.2 ?_ (hnd.fwd N (by decide)) (hnd.bwd N (by decide))
  · nf_test N hσD (by show 0 < N.q; linarith [N.hq])
  · nf_test N hσD (by show 0 < N.g * N.p - N.g + N.q; linarith [N.t0146, hD])
  · nf_test N hσD (by show 0 < N.g * N.p; linarith [mul_pos (N.hg) N.hp])
  · nf_test N hσD (by show 0 < N.g; linarith [N.hg])
  · nf_simp N
    refine nf_E_le (P₁ := N.d * N.q - N.g * N.r)
        (P₂ := N.d * N.q - N.g * N.p - N.g * N.r + N.g - N.q) (by simp only [det3c]; ring)
        (by simp only [det3c]; ring) ?_
    exact mul_nonpos_of_nonneg_of_nonpos
        (le_of_lt (by show 0 < N.d * N.q - N.g * N.r; linarith [hD]))
        (by
          have := (by show 0 < -N.d * N.q + N.g * N.p + N.g * N.r - N.g + N.q; linarith [N.t0146])
          linarith)
  intro z hz
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
  fin_cases i
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_, ?_⟩)))))
    · nf_test N hσD (by show 0 < N.b; linarith [N.hb])
    · nf_test N hσD (by show 0 < -N.a * N.q + N.b * N.p - N.b + N.q; linarith [hc])
    · nf_test N hσD (pos_of_mul_pos_r (by
              show 0 < (1 / 3 : ℝ) * N.p + (1 / 3 : ℝ) * N.q + (1 / 3 : ℝ) * N.r - (1 / 3 : ℝ)
              linarith [N.t0246, hR2, N.hab])
            (by
              show 0 < (-N.a * N.g + N.a * N.q - N.b * N.p + N.g * N.p) *
                ((1 / 3 : ℝ) * N.p + (1 / 3 : ℝ) * N.q + (1 / 3 : ℝ) * N.r - (1 / 3 : ℝ))
              linarith [mul_pos (N.t024_1) (hqg), mul_pos (hR2) (hD), mul_pos (N.t024_1) (hg1),
                  mul_pos (hR1) (hc), mul_pos (N.t0146) (hR2)]))
    · nf_test N hσD (by show 0 < N.a * N.g; linarith [mul_pos (N.ha) N.hg])
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inl ⟨(N.g - 1) / (N.g), (N.d) / (N.g), div_pos
                    (by show 0 < N.g - 1; linarith [hg1]) (by show 0 < N.g; linarith [N.hg]),
                    (div_lt_one (by show 0 < N.g; linarith [N.hg])).mpr
                    (by have := (by norm_num : (0 : ℝ) < 1); linarith), div_pos
                    (by show 0 < N.d; linarith [N.hd]) (by show 0 < N.g; linarith [N.hg]), Or.inr
                    (Or.inl ?_)⟩)))))
    have hden := (by show 0 < N.g; linarith [N.hg])
    nf_simp N
    ext k
    simp only
        [nfP, nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
    field_simp
    ring
  · exact Or.inr (Or.inl rfl)

/-- **Step 5, D4**: E03 with far path `2, 4, 6`. -/
theorem isRupert_stepD4 (N : NF16 x) (hR1 : 0 < (N.g - 1) * (N.p + N.r) - N.d * (N.q - 1))
    (hR2 : 0 < N.a * (N.q - 1) - (N.b - 1) * (N.p + N.r)) (hD : 0 < N.q * N.d - N.r * N.g)
    (hqg : 0 < N.q - N.g) (hg1 : 0 < N.g - 1) (hqb : 0 < N.q - N.b)
    (hc : 0 < N.q * (N.a - 1) - N.b * (N.p - 1)) (hb1 : 0 < N.b - 1)
    (hf : 0 < N.q * (1 - N.d) + N.g * (N.r - 1))
    (hg : GenPos (univ.image x)) (hnd : NoHDNEdges16 x) : IsRupert (univ.image x) := by
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  have hz := depth_nodup4 (v := 0) (w := 3) (a := 6) (b := 2) (c := 4) N.inj hg (by decide)
  refine isRupert_edgePairσ (v := x 0) (w := x 3) (a := x 6) (b := x 2) (c := x 4) _ hσ
    (mem_image 0) (mem_image 3) (mem_image 6) (mem_image 2) (mem_image 4) ?_ ?_ ?_ ?_ ?_
    hz.1 hz.2 ?_ (hnd.fwd N (by decide)) (hnd.bwd N (by decide))
  · nf_test N hσD (by show 0 < N.q; linarith [N.hq])
  · nf_test N hσD (by show 0 < N.b * N.r - N.b + N.q; linarith [hqb, mul_pos (N.hb) N.hr])
  · nf_test N hσD (by show 0 < N.b * N.r; linarith [mul_pos (N.hb) N.hr])
  · nf_test N hσD (by show 0 < N.b; linarith [N.hb])
  · nf_simp N
    refine nf_E_le (P₁ := -N.a * N.q + N.b * N.p + N.b * N.r - N.b + N.q)
        (P₂ := -N.a * N.q + N.b * N.p) (by simp only [det3c]; ring) (by simp only [det3c]; ring) ?_
    exact mul_nonpos_of_nonneg_of_nonpos
        (le_of_lt (by show 0 < -N.a * N.q + N.b * N.p + N.b * N.r - N.b + N.q; linarith [N.t0246]))
        (by have := (by show 0 < N.a * N.q - N.b * N.p; linarith [hc, hqb]); linarith)
  intro z hz
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
  fin_cases i
  · exact Or.inl rfl
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_, ?_⟩)))))
    · nf_test N hσD (by show 0 < N.g; linarith [N.hg])
    · nf_test N hσD (by show 0 < -N.d * N.q + N.g * N.r - N.g + N.q; linarith [hf])
    · nf_test N hσD (pos_of_mul_pos_r (by show 0 < (1 / 4 : ℝ) * N.q; linarith [hg1, hf, hD])
            (by
              show 0 < (-N.b * N.d + N.b * N.r + N.d * N.q - N.g * N.r) * ((1 / 4 : ℝ) * N.q)
              linarith [mul_pos (hqg) (hc), mul_pos (hD) (hqb), mul_pos (N.t0246) (hqg)]))
    · nf_test N hσD (by show 0 < N.b * N.d; linarith [mul_pos (N.hb) N.hd])
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inl ⟨(N.b - 1) / (N.b), (N.a) / (N.b), div_pos
                    (by show 0 < N.b - 1; linarith [hb1]) (by show 0 < N.b; linarith [N.hb]),
                    (div_lt_one (by show 0 < N.b; linarith [N.hb])).mpr
                    (by have := (by norm_num : (0 : ℝ) < 1); linarith), div_pos
                    (by show 0 < N.a; linarith [N.ha]) (by show 0 < N.b; linarith [N.hb]), Or.inr
                    (Or.inr (Or.inr ?_))⟩)))))
    have hden := (by show 0 < N.b; linarith [N.hb])
    nf_simp N
    ext k
    simp only
        [nfP, nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
    field_simp
    ring
  · exact Or.inr (Or.inr (Or.inl rfl))

/-- **Step 5, D6**: the triangle `1, 6, 4` at `15`. -/
theorem isRupert_stepD6 (N : NF16 x) (hR1 : 0 < (N.g - 1) * (N.p + N.r) - N.d * (N.q - 1))
    (hR2 : 0 < N.a * (N.q - 1) - (N.b - 1) * (N.p + N.r)) (hD : 0 < N.q * N.d - N.r * N.g)
    (hqg : 0 < N.q - N.g) (hg1 : 0 < N.g - 1) (hqb : 0 < N.q - N.b)
    (hc : 0 < N.q * (N.a - 1) - N.b * (N.p - 1)) (hf : 0 < (N.g - 1) * (N.p + N.r - 1) - N.d * N.q)
    (hg : GenPos (univ.image x)) (hnd : NoHDNEdges16 x) : IsRupert (univ.image x) := by
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  have h46 : 0 < -N.a * N.d * N.q + N.a * N.g * N.r + N.b * N.d * N.p - N.a * N.g - N.a * N.r + N.g
      * N.p + N.a - N.p := pos_of_mul_pos_r N.t0146
      (by linarith [mul_pos (mul_pos N.hp N.hgd) N.t0246, mul_pos hf N.t146_2])
  have hz := depth_nodup3 (v := 1) (w := 5) (a := 4) (b := 6) N.inj hg (by decide)
  refine isRupert_edgeTriσ (v := x 1) (w := x 5) (a := x 4) (b := x 6) _ hσ
    (mem_image 1) (mem_image 5) (mem_image 4) (mem_image 6) ?_ hz ?_ (hnd.fwd N (by decide))
  · nf_test N hσD (by show 0 < N.d * N.p + N.g * N.p - N.p; linarith [mul_pos (N.hgd) (N.hp)])
  intro z hz
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
  fin_cases i
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩))))
    · nf_test N hσD (by show 0 < N.d * N.p + N.d * N.q - N.g * N.r - N.d + N.r; linarith [N.t145_0])
    · nf_test N hσD
          (by show 0 < -N.d * N.q + N.g * N.p + N.g * N.r - N.g - N.p - N.r + 1; linarith [hf])
    · nf_test N hσD (by show 0 < N.d + N.g - 1; linarith [N.hgd])
  · exact Or.inl rfl
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩))))
    · nf_test N hσD (by
            show 0 < N.a * N.d * N.q - N.a * N.g * N.r - N.b * N.d * N.p - N.a * N.d + N.a * N.r +
              N.d * N.p
            linarith [N.tB125])
    · nf_test N hσD (by
            show 0 < -N.a * N.d * N.q + N.a * N.g * N.r + N.b * N.d * N.p - N.a * N.g - N.a * N.r +
              N.g * N.p + N.a - N.p
            linarith [h46])
    · nf_test N hσD (by show 0 < N.a * N.d + N.a * N.g - N.a; linarith [mul_pos (N.hgd) (N.ha)])
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨(N.g - 1) / (N.d + N.g - 1), (1) / (N.d + N.g - 1), div_pos
                  (by show 0 < N.g - 1; linarith [hg1])
                  (by show 0 < N.d + N.g - 1; linarith [N.hgd]),
                  (div_lt_one (by show 0 < N.d + N.g - 1; linarith [N.hgd])).mpr
                  (by have := (by show 0 < N.d; linarith [N.hd]); linarith), div_pos
                  (by norm_num : (0 : ℝ) < 1) (by show 0 < N.d + N.g - 1; linarith [N.hgd]), Or.inr
                  (Or.inr (Or.inr ?_))⟩))))
    have hden := (by show 0 < N.d + N.g - 1; linarith [N.hgd])
    nf_simp N
    ext k
    simp only
        [nfP, nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
    field_simp
    ring
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))



/-! ### Lemma 19.1 and the dispatch of Theorem 19.2 -/

/-- **Lemma 19.1 (b)**: in `R1` with `q > g`, `g > 1` (off `g = 1`):
`(1 − g) [0146] + g R1 = −(q − g)(g + d − 1)`. -/
theorem g_gt_one (N : NF16 x) (hR1 : 0 < (N.g - 1) * (N.p + N.r) - N.d * (N.q - 1))
    (hqg : 0 < N.q - N.g) (hg1 : N.g ≠ 1) : 0 < N.g - 1 := by
  rcases lt_or_gt_of_ne hg1 with h | h
  · exfalso
    have e : (1 - N.g) * (N.g * (N.p + N.r - 1) - N.q * (N.d - 1)) +
        N.g * ((N.g - 1) * (N.p + N.r) - N.d * (N.q - 1)) = -((N.q - N.g) * (N.g + N.d - 1)) := by
      ring
    nlinarith [mul_pos (sub_pos.mpr h) N.t0146, mul_pos N.hg hR1, mul_pos hqg N.hgd]
  · linarith

/-- **Lemma 19.1 (c)**: not `R2` with `b > 1` gives `q > b`:
`b (1 − b) [0246] − b² [¬R2] = b (a + b − 1)(b − q)`. -/
theorem q_gt_b (N : NF16 x) (hR2 : 0 < N.a * (N.q - 1) - (N.b - 1) * (N.p + N.r))
    (hb1 : 0 < N.b - 1) : 0 < N.q - N.b := by
  by_contra hc; push Not at hc
  have e : N.b * (1 - N.b) * (N.b * (N.p + N.r - 1) - N.q * (N.a - 1)) -
      N.b ^ 2 * (N.a * (N.q - 1) - (N.b - 1) * (N.p + N.r)) =
      N.b * (N.a + N.b - 1) * (N.b - N.q) := by ring
  have := mul_nonneg (mul_pos N.hb N.hab).le (show 0 ≤ N.b - N.q by linarith)
  nlinarith [mul_pos (mul_pos N.hb hb1) N.t0246, mul_pos (mul_pos N.hb N.hb) hR2]

/-- The nondegeneracy conditions of the cover (§19.7.1, "equality in a sign condition of the
route" and the far-end ties), as polynomials of the normal form. -/
structure Gen (N : NF16 x) : Prop where
  qg : N.q ≠ N.g
  rd : N.r ≠ N.d
  p013 : N.r * N.g ≠ N.q * N.d
  a1 : N.a ≠ 1
  b1 : N.b ≠ 1
  g1 : N.g ≠ 1
  d1 : N.d ≠ 1
  Z2 : N.a * N.q ≠ N.b * N.p
  c36 : N.q * (N.a - 1) ≠ N.b * (N.p - 1)
  f15 : (N.g - 1) * (N.p + N.r - 1) ≠ N.d * N.q
  f03 : N.q * (1 - N.d) + N.g * (N.r - 1) ≠ 0
  pr : N.p + N.r ≠ 1
  HA : (N.b - 1) * N.g * N.p * N.r + (N.q * (1 - N.d) + N.g * (N.r - 1)) *
    (N.a * (N.q - 1) - (N.b - 1) * N.p) ≠ 0
  T5 : N.d * (N.q * (N.a - 1) - N.b * (N.p - 1)) - (N.g - 1) * (N.a - 1) * N.r ≠ 0

/-- **The residual `Ω` of Theorem 19.2** (in `R1`, region D, `2` a corner at `36`, and no step
D2–D7 applies), with the consequences of Lemma 19.1. -/
structure Omega (N : NF16 x) : Prop where
  R1 : 0 < (N.g - 1) * (N.p + N.r) - N.d * (N.q - 1)
  R2 : 0 < N.a * (N.q - 1) - (N.b - 1) * (N.p + N.r)
  D : 0 < N.q * N.d - N.r * N.g
  qg : 0 < N.q - N.g
  g1 : 0 < N.g - 1
  qb : 0 < N.q - N.b
  c36 : 0 < N.q * (N.a - 1) - N.b * (N.p - 1)
  nD2 : 0 < N.a - 1 → 0 < N.d - 1 → N.p * N.b * N.d + N.r * N.g * N.a - N.q * N.a * N.d ≤ 0
  nD3 : 0 < 1 - N.b → (1 - N.d) * (N.a * N.q + (1 - N.b) * N.p) + N.a * N.g * (N.r - 1) ≤ 0
  nD4 : 0 < N.b - 1 → N.q * (1 - N.d) + N.g * (N.r - 1) ≤ 0
  nD6 : (N.g - 1) * (N.p + N.r - 1) - N.d * N.q ≤ 0
  nD7 : 0 < 1 - N.a → 0 < 1 - N.d → 0 ≤ N.p + N.r - 1

/-- **Theorem 19.2 (the Lemma E cover)**: in `R1`, off the special positions `Gen`, `K` is Rupert
by one of the steps A, U (E35, E02, E25, E03), D1 (E36), D2–D7, or it lies in `Ω`. -/
theorem isRupert_R1_or_omega (N : NF16 x) (hR1 : 0 < N.R1) (G : Gen N)
    (hg : GenPos (univ.image x)) (hnd : NoHDNEdges16 x)
    (hΩ : Omega N → IsRupert (univ.image x)) : IsRupert (univ.image x) := by
  have hR2 : 0 < N.a * (N.q - 1) - (N.b - 1) * (N.p + N.r) := by
    have := N.R2_neg_of_R1 hR1.le; simp only [R2] at this; linarith
  simp only [R1] at hR1
  have sgn : ∀ {t : ℝ}, t ≠ 0 → t < 0 ∨ 0 < t := fun h => lt_or_gt_of_ne h
  by_cases hA : N.q < N.g ∧ N.r < N.d
  · exact isRupert_stepA N hR1 (by linarith [hA.1]) (by linarith [hA.2]) hg hnd
  rcases lt_or_gt_of_ne G.p013 with hD | hU
  · -- region D
    have hqg : 0 < N.q - N.g := by
      rcases lt_or_gt_of_ne G.qg with h | h
      · exfalso
        have hrd : N.d ≤ N.r := by by_contra h'; exact hA ⟨h, lt_of_not_ge h'⟩
        nlinarith [mul_le_mul_of_nonneg_left hrd N.hg.le, mul_lt_mul_of_pos_left h N.hd]
      · linarith
    have hg1 := g_gt_one N hR1 hqg G.g1
    have hqb : 0 < N.q - N.b := by
      rcases lt_or_gt_of_ne G.b1 with h | h
      · linarith
      · exact q_gt_b N hR2 (by linarith)
    have hDp : 0 < N.q * N.d - N.r * N.g := by linarith
    rcases lt_or_gt_of_ne G.c36 with hc | hc
    · exact isRupert_stepD1 N hR1 hR2 hDp hqg hg1 hqb (by linarith) hg hnd
    have hc' : 0 < N.q * (N.a - 1) - N.b * (N.p - 1) := by linarith
    by_cases hD2 : 0 < N.a - 1 ∧ 0 < N.d - 1 ∧
        0 < N.p * N.b * N.d + N.r * N.g * N.a - N.q * N.a * N.d
    · exact isRupert_stepD2 N hR1 hR2 hDp hqg hg1 hqb hc' hD2.1 hD2.2.1 hD2.2.2 hg hnd
    by_cases hD3 : 0 < 1 - N.b ∧
        0 < (1 - N.d) * (N.a * N.q + (1 - N.b) * N.p) + N.a * N.g * (N.r - 1)
    · exact isRupert_stepD3 N hR1 hR2 hDp hqg hg1 hqb hc' hD3.1 hD3.2 hg hnd
    by_cases hD4 : 0 < N.b - 1 ∧ 0 < N.q * (1 - N.d) + N.g * (N.r - 1)
    · exact isRupert_stepD4 N hR1 hR2 hDp hqg hg1 hqb hc' hD4.1 hD4.2 hg hnd
    by_cases hD5 : 0 < N.d - 1 ∧ 0 < N.a * N.d * N.q - N.a * N.g * N.r - N.b * N.d * N.p -
        N.a * N.d - N.a * N.q + N.b * N.p + N.d * N.p + N.a - N.p
    · exact isRupert_stepD5 N hR1 hR2 hDp hqg hg1 hqb hc' hD5.1 hD5.2 hg hnd
    by_cases hD6 : 0 < (N.g - 1) * (N.p + N.r - 1) - N.d * N.q
    · exact isRupert_stepD6 N hR1 hR2 hDp hqg hg1 hqb hc' hD6 hg hnd
    by_cases hD7 : 0 < 1 - N.a ∧ 0 < 1 - N.d ∧ 0 < 1 - N.p - N.r
    · exact isRupert_stepD7 N hR1 hR2 hDp hqg hg1 hqb hc' hD7.1 hD7.2.1 hD7.2.2 hg hnd
    refine hΩ ⟨hR1, hR2, hDp, hqg, hg1, hqb, hc', fun h1 h2 => ?_, fun h1 => ?_, fun h1 => ?_,
      not_lt.mp hD6, fun h1 h2 => ?_⟩
    · exact not_lt.mp fun h3 => hD2 ⟨h1, h2, h3⟩
    · exact not_lt.mp fun h3 => hD3 ⟨h1, h3⟩
    · exact not_lt.mp fun h3 => hD4 ⟨h1, h3⟩
    · by_contra h3; push Not at h3; exact hD7 ⟨h1, h2, by linarith⟩
  · -- region U
    have hUp : 0 < N.r * N.g - N.q * N.d := by linarith
    have hrd : 0 < N.r - N.d := by
      rcases lt_or_gt_of_ne G.rd with h | h
      · exfalso
        rcases lt_or_gt_of_ne G.qg with h' | h'
        · exact hA ⟨h', h⟩
        · nlinarith [mul_lt_mul_of_pos_left h N.hg, mul_lt_mul_of_pos_left h' N.hd]
      · linarith
    rcases lt_or_gt_of_ne G.d1 with hd1 | hd1
    · rcases lt_or_gt_of_ne G.Z2 with hZ | hZ
      · rcases lt_or_gt_of_ne G.a1 with ha1 | ha1
        · exact isRupert_stepU3 N hR1 hR2 hUp hrd (by linarith) (by linarith) (by linarith) hg hnd
        · exact isRupert_stepU2 N hR1 hR2 hUp hrd (by linarith) (by linarith) (by linarith) hg hnd
      · rcases lt_or_gt_of_ne G.b1 with hb1 | hb1
        · exact isRupert_stepU4 N hR1 hR2 hUp hrd (by linarith) (by linarith) (by linarith) hg hnd
        · exact isRupert_stepU5 N hR1 hR2 hUp hrd (by linarith) (by linarith) (by linarith) hg hnd
    · rcases lt_or_gt_of_ne G.a1 with ha1 | ha1
      · exact isRupert_stepU1b N hR1 hR2 hUp hrd (by linarith) (by linarith) hg hnd
      · exact isRupert_stepU1a N hR1 hR2 hUp hrd (by linarith) (by linarith) hg hnd

end NF16

end Minimality

end
