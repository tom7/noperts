module

public import Minimality.Type29NF

@[expose] public section

/-!
# Type 29, class K4 (`FEWER-FACES-PROOFS.md` §21.1)

In the normal coordinates of `NF29` (`Type29NF.lean`) class K4a is `a2 > 0`, `b0 > 0`, `V < 0`
(K4b is its `σ`-image).  On `R_G` (none of the class's E-good `G` edges is a quad edge of `O`,
Lemma 21.3) every shape has a metric-free certificate (Theorem 21.11):

* Lemmas 21.7, 21.8 (`NF29.k4_facts`): `e0, e2 > 0`, `s, t < 1`, `b2 + h2 > 0`, `G5 ≥ 0`.
* Tier (A), `h0 < 1`, Lemma 21.9 (F35): the vertex crossing `V = 035/1456`
  (`NF29.isRupert_k4_V`, view `NF29.vV`) or the edge crossing `Y = 035/356-3`
  (`NF29.isRupert_k4_Y`) is unimodal (`NF29.isRupert_k4_A`; the pentagon argument in reals,
  `k4_Y_core`, with `quint_unimodal_of`).
* Tier (B1), `h0 > 1 > h0 + a0`: tier (A) for `x ∘ σ` (`NF29.sigma`).
* Tier (B2), `h0 + a0 < 0`, Lemma 21.10 (F35′): the edge crossing `W = 023/035-0` and the vertex
  crossing `Z = 035/234` (`NF29.isRupert_k4_W`, `NF29.isRupert_k4_Z`, view `NF29.vZ`) are not
  both depth-separated (Corollary 13.3 with the shared diagonal `[1, 3]`,
  `NF29.isRupert_k4_B2`).
* Theorem 21.11: `NF29.isRupert_K4a` (special positions and genericity in `K4Gen`) and
  `NF29.isRupert_K4b`.

Every rim test is a polynomial in the eight coordinates times the frame determinant, proved
positive from the class, region and type inequalities by explicit products (`linarith` with
product hints); middles are explicit combinations (`mid_comb`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Minimality

open scoped RealInnerProductSpace
open Finset

theorem img29 {x : Fin 7 → ℝ³} (i : Fin 7) : x i ∈ univ.image x :=
  Finset.mem_image_of_mem x (mem_univ i)

/-- A middle from a combination with a common positive denominator. -/
theorem mid_comb {m X Y U : ℝ³} {D₀ α β : ℝ} (hD : 0 < D₀) (hα : 0 < α) (hα' : 0 < D₀ - α)
    (hβ : β ≠ 0) (h : D₀ • (m - X) = α • (Y - X) + β • U) :
    ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧ m = X + s • (Y - X) + δ • U :=
  ⟨α / D₀, β / D₀, div_pos hα hD, (div_lt_one hD).mpr (by linarith), div_ne_zero hβ hD.ne',
    eq_comb_div hD.ne' h⟩

variable {x : Fin 7 → ℝ³}

/-- The view of `V = 035/1456`: `d = (A0, −e0, 0)`, along `aff 035 ∩ H`. -/
noncomputable def NF29.vV (N : NF29 x) : ℝ³ :=
  nfV N.E₁ N.E₂ N.E₃ (-N.a0) (-(N.b0 + N.h0 - 1)) 0

/-- The view of `Z = 035/234`: `u_Z = (A0 (B2 − e2), B2 (A0 − e0), A0 B2 − e0 e2)`, along
`aff 035 ∩ aff 234`. -/
noncomputable def NF29.vZ (N : NF29 x) : ℝ³ :=
  nfV N.E₁ N.E₂ N.E₃ (-N.a0 * (-N.b2 - (N.a2 + N.h2 - 1)))
    (-N.b2 * (-N.a0 - (N.b0 + N.h0 - 1))) (N.a0 * N.b2 - (N.b0 + N.h0 - 1) * (N.a2 + N.h2 - 1))

/-- **Test `V = 035/1456`** (§21.11 (A)): the vertex crossing at `5`, view `d = (A0, −e0, 0)` along
`aff 035 ∩ H`, rim `(5, 1, 2, 3)`; `0` a middle over `3–5`, `4` and `6` middles over `5–1`. -/
theorem NF29.isRupert_k4_V (N : NF29 x)
    (he0 : 0 < N.b0 + N.h0 - 1)
    (hh01 : 0 < -N.h0 + 1)
    (hc : 0 < N.a0 * N.b2 - N.a2 * N.b0 - N.a2 * N.h0 + N.a2)
    (hz : IsRobustUnimodal (quad ⟪x 5, N.vV⟫ ⟪x 1, N.vV⟫ ⟪x 2, N.vV⟫ ⟪x 3, N.vV⟫))
    (hnd : NoHDNAt (univ.image x) (N.vV)) : IsRupert (univ.image x) := by
  have hA0 : 0 < -N.a0 := by linarith [N.ha0]
  have h345_0 : 0 < 1 - N.a0 - N.b0 - N.h0 := by linarith [N.t345_0]
  have hst : 0 < N.s + N.t - 1 := by linarith [N.hst]
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  refine isRupert_vquadσ (univ.image x) ({x 0, x 4, x 6} : Finset ℝ³) (u := N.vV) ?_ hσ
    (img29 5) (img29 1) (img29 2) (img29 3)
    (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff])
        (by simp [N.inj.eq_iff]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hz hnd ?_
  · exact nfV_ne_zero N.hD (Or.inl (neg_pos.mpr N.ha0).ne')
  · simp only [NF29.vV]; nf29_test N hσD (by show 0 < -N.a0 * N.h2; linarith [mul_pos (N.hh2) hA0])
  · simp only [NF29.vV]; nf29_test N hσD hA0
  · simp only [NF29.vV]; nf29_test N hσD hc
  · simp only [NF29.vV]; nf29_test N hσD (by show 0 < -N.a0 * N.h2; linarith [mul_pos (N.hh2) hA0])
  · simp only [NF29.vV]; nf29_test N hσD N.hDG5
  · simp only [NF29.vV]; nf29_test N hσD hc
  · simp only [NF29.vV]; nf29_test N hσD hA0
  · simp only [NF29.vV]; nf29_test N hσD N.hDG5
  · intro z hz hzM hn0 hn1 hn2 hn3
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    fin_cases i
    · exact absurd (by simp) hzM
    · exact absurd rfl hn1
    · exact absurd rfl hn2
    · exact absurd rfl hn3
    · exact absurd (by simp) hzM
    · exact absurd rfl hn0
    · exact absurd (by simp) hzM
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl
    · have hmid := mid_comb (m := x 0) (X := x 3) (Y := x 5) (U := N.vV)
        (D₀ := -N.a0) (α := N.a0 * N.h0 - N.a0) (β := N.a0)
        (by linarith [hA0]) (by linarith [mul_pos (hA0) hh01])
        (by linarith [mul_pos (N.hh0) hA0])
        (ne_of_lt (by linarith [hA0]))
        (by simp only [NF29.vV]; nf29_vec N)
      obtain ⟨s, δ, h1, h2, h3, h4⟩ := hmid
      exact ⟨s, δ, h1, h2, h3, Or.inr <| Or.inr <| Or.inr <| h4⟩
    · have hmid := mid_comb (m := x 4) (X := x 5) (Y := x 1) (U := N.vV)
        (D₀ := -N.a0) (α := -N.a0 - N.b0 - N.h0 + 1) (β := 1)
        (by linarith [hA0]) (by linarith [h345_0])
        (by linarith [he0])
        (ne_of_gt (by norm_num))
        (by simp only [NF29.vV]; nf29_vec N)
      obtain ⟨s, δ, h1, h2, h3, h4⟩ := hmid
      exact ⟨s, δ, h1, h2, h3, Or.inl <| h4⟩
    · have hmid := mid_comb (m := x 6) (X := x 5) (Y := x 1) (U := N.vV)
        (D₀ := -N.a0) (α := N.a0 * N.t - N.b0 * N.s - N.h0 * N.s - N.a0 + N.s) (β := N.s)
        (by linarith [hA0]) (by linarith [N.d035])
        (by linarith [he0, mul_pos (hst) he0, mul_pos (h345_0) N.ht])
        (ne_of_gt (by linarith [N.hs]))
        (by simp only [NF29.vV]; nf29_vec N)
      obtain ⟨s, δ, h1, h2, h3, h4⟩ := hmid
      exact ⟨s, δ, h1, h2, h3, Or.inl <| h4⟩

/-- **Test `Y = 035/356-3`** (§21.11 (A)): the edge crossing along `35` (apex `5`, view `5 − 3`),
rim `(5, 0, 1, 4, 6)`; `2` hidden. -/
theorem NF29.isRupert_k4_Y (N : NF29 x)
    (ha2 : 0 < N.a2)
    (he0 : 0 < N.b0 + N.h0 - 1)
    (hs1 : 0 < -N.s + 1)
    (hbh2 : 0 < N.b2 + N.h2)
    (hz : IsRobustUnimodal (quint ⟪x 5, (x 5 - x 3)⟫ ⟪x 0, (x 5 - x 3)⟫ ⟪x 1, (x 5 - x 3)⟫ ⟪x 4,
            (x 5 - x 3)⟫ ⟪x 6, (x 5 - x 3)⟫))
    (hnd : NoHDNAt ((univ.image x).erase (x 3)) ((x 5 - x 3))) : IsRupert (univ.image x) := by
  have hA0 : 0 < -N.a0 := by linarith [N.ha0]
  have h345_0 : 0 < 1 - N.a0 - N.b0 - N.h0 := by linarith [N.t345_0]
  have h345_2 : 0 < 1 - N.a2 - N.b2 - N.h2 := by linarith [N.t345_2]
  have hst : 0 < N.s + N.t - 1 := by linarith [N.hst]
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  refine isRupert_equintσ (univ.image x) (∅ : Finset ℝ³) (u := (x 5 - x 3)) ?_ hσ (h := 1)
      one_ne_zero
    (by module) (img29 3)
    (img29 5) (img29 0) (img29 1) (img29 4) (img29 6)
    (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff])
        (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff]) ?_ ?_ hz hnd ?_
  · exact sub_ne_zero.mpr (N.inj.ne (by decide))
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · nf29_test N hσD hA0
    · nf29_test N hσD h345_0
    · nf29_test N hσD N.d035
    · nf29_test N hσD (by show 0 < N.b0 + N.h0; linarith [he0])
    · nf29_test N hσD (by
            show 0 < -N.a0 * N.t + N.b0 * N.s + N.h0 * N.s
            linarith [he0, N.hs, mul_pos (hA0) hst, mul_pos (h345_0) hs1])
    · nf29_test N hσD hA0
    · nf29_test N hσD N.ht
    · nf29_test N hσD (by norm_num : (0 : ℝ) < 1)
    · nf29_test N hσD (by show 0 < N.b0 + N.h0; linarith [he0])
    · nf29_test N hσD hst
    · nf29_test N hσD (by
            show 0 < -N.a0 * N.t + N.b0 * N.s + N.h0 * N.s - N.b0 - N.h0 + N.t
            linarith [hst, mul_pos (hst) he0, mul_pos (h345_0) N.ht])
    · nf29_test N hσD N.ht
    · nf29_test N hσD N.d035
    · nf29_test N hσD N.hs
    · nf29_test N hσD hst
  · intro z hz hzM hzw hn0 hn1 hn2 hn3 hn4
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    fin_cases i
    · exact absurd rfl hn1
    · exact absurd rfl hn2
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · nf29_test N hσD N.hDG5
      · nf29_test N hσD (by
              show 0 < -N.a0 * N.b2 - N.a0 * N.h2 + N.a2 * N.b0 + N.a2 * N.h0
              linarith [ha2, mul_pos (ha2) he0, mul_pos (hA0) hbh2])
      · nf29_test N hσD hbh2
      · nf29_test N hσD (by
              show 0 < -N.a2 * N.t + N.b2 * N.s + N.h2 * N.s - N.b2 - N.h2 + N.t
              linarith [mul_pos (hst) hbh2, mul_pos (h345_2) N.ht])
      · nf29_test N hσD (by
              show 0 < N.a2 * N.t - N.b2 * N.s - N.h2 * N.s - N.a2 + N.s
              linarith [mul_pos (hst) ha2, mul_pos (h345_2) N.hs])
    · exact absurd rfl hzw
    · exact absurd rfl hn3
    · exact absurd rfl hn0
    · exact absurd rfl hn4
  · intro m hm
    simp at hm

/-- A 5-cycle with distinct values is unimodal if no two non-adjacent positions are both peaks. -/
theorem quint_unimodal_of {y0 y1 y2 y3 y4 : ℝ} (hinj : Function.Injective (quint y0 y1 y2 y3 y4))
    (P02 : y4 < y0 → y1 < y0 → y1 < y2 → y3 < y2 → False)
    (P03 : y4 < y0 → y1 < y0 → y2 < y3 → y4 < y3 → False)
    (P13 : y0 < y1 → y2 < y1 → y2 < y3 → y4 < y3 → False)
    (P14 : y0 < y1 → y2 < y1 → y3 < y4 → y0 < y4 → False)
    (P24 : y1 < y2 → y3 < y2 → y3 < y4 → y0 < y4 → False) :
    IsCyclicUnimodal (quint y0 y1 y2 y3 y4) := by
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
  | (exfalso; exact P02 hi.1 hi.2 hj.1 hj.2)
  | (exfalso; exact P02 hj.1 hj.2 hi.1 hi.2)
  | (exfalso; exact P03 hi.1 hi.2 hj.1 hj.2)
  | (exfalso; exact P03 hj.1 hj.2 hi.1 hi.2)
  | (exfalso; exact P13 hi.1 hi.2 hj.1 hj.2)
  | (exfalso; exact P13 hj.1 hj.2 hi.1 hi.2)
  | (exfalso; exact P14 hi.1 hi.2 hj.1 hj.2)
  | (exfalso; exact P14 hj.1 hj.2 hi.1 hi.2)
  | (exfalso; exact P24 hi.1 hi.2 hj.1 hj.2)
  | (exfalso; exact P24 hj.1 hj.2 hi.1 hi.2)

/-- **Lemma 21.9 (2), (3)** in reals: the depths of `Y`'s rim `(5, 0, 1, 4, 6)` along `u = 5 − 3`
are `z4 = z1 + p1`, `z5 = z1 + p2`, `z6 = z1 + s p1 + t p2` (the cap on `H`) and
`z0 = z1 − A0 p1 + (e0 + 1) p2 − h0 ⟪u, u⟫` (`0 + h0 u ∈ H`); if `ψ(d) = A0 p1 − e0 p2 > 0`, no two
of the five non-adjacent pairs are both peaks. -/
theorem k4_Y_core {A0 e0 h0 s t p1 p2 q z0 z1 z4 z5 z6 : ℝ} (hA0 : 0 < A0) (he0 : 0 < e0)
    (hs : 0 < s) (ht : 0 < t) (hst : 0 < s + t - 1) (ht1 : 0 < 1 - t) (hs1 : 0 < 1 - s)
    (hd035 : 0 < A0 * (1 - t) - e0 * s) (hh0 : 0 < h0) (hq : 0 < q) (h345_0 : 0 < A0 - e0)
    (hpsi : 0 < A0 * p1 - e0 * p2) (e4 : z4 = z1 + p1) (e5 : z5 = z1 + p2)
    (e6 : z6 = z1 + s * p1 + t * p2) (e0' : z0 = z1 - A0 * p1 + (e0 + 1) * p2 - h0 * q)
    (hinj : Function.Injective (quint z5 z0 z1 z4 z6)) :
    IsCyclicUnimodal (quint z5 z0 z1 z4 z6) := by
  subst e4 e5 e6 e0'
  refine quint_unimodal_of hinj ?_ ?_ ?_ ?_ ?_
  · intro i1 i2 i3 i4; linarith [mul_pos (mul_pos (he0) hs) (sub_pos.mpr i1), mul_pos
          (mul_pos (hs) hd035) (sub_pos.mpr i4), mul_pos (mul_pos (hst) ht1) hpsi, mul_pos
          (mul_pos (ht1) ht1) hpsi]
  · intro i1 i2 i3 i4; linarith [mul_pos (hd035) (sub_pos.mpr i4), mul_pos (mul_pos (hA0) hs1)
          (sub_pos.mpr i1), mul_pos (mul_pos (he0) hst) (sub_pos.mpr i1), mul_pos
          (mul_pos (he0) hst) (sub_pos.mpr i3), mul_pos (mul_pos (he0) ht1) (sub_pos.mpr i4),
          mul_pos (mul_pos (hst) h345_0) (sub_pos.mpr i1), mul_pos (mul_pos (hst) hpsi) hs1, mul_pos
          (mul_pos (hst) hst) hpsi, mul_pos (mul_pos (hst) ht1) hpsi]
  · intro i1 i2 i3 i4; linarith [mul_pos (mul_pos (hA0) hst) (sub_pos.mpr i3), mul_pos
          (mul_pos (hd035) hs1) (sub_pos.mpr i3), mul_pos (mul_pos (he0) hst) (sub_pos.mpr i4),
          mul_pos (mul_pos (he0) ht1) (sub_pos.mpr i4), mul_pos (mul_pos (hpsi) hs1) hs1, mul_pos
          (mul_pos (hs) hs1) (sub_pos.mpr i1), mul_pos (mul_pos (hs) ht) (sub_pos.mpr i1), mul_pos
          (mul_pos (hs1) hs1) (sub_pos.mpr i1), mul_pos (mul_pos (hst) hpsi) hs1, mul_pos
          (mul_pos (hst) ht1) (sub_pos.mpr i1), mul_pos (mul_pos (ht) hh0) hq, mul_pos
          (mul_pos (ht) ht) (sub_pos.mpr i1)]
  · intro i1 i2 i3 i4; linarith [mul_pos (hd035) (sub_pos.mpr i1), mul_pos (hd035) hpsi, mul_pos
          (mul_pos (h345_0) hs1) (sub_pos.mpr i1), mul_pos (mul_pos (hA0) hst) hpsi, mul_pos
          (mul_pos (he0) hst) (sub_pos.mpr i1), mul_pos (mul_pos (hh0) hq) h345_0, mul_pos
          (mul_pos (hpsi) h345_0) hs1, mul_pos (mul_pos (hst) h345_0) (sub_pos.mpr i1)]
  · intro i1 i2 i3 i4; linarith [mul_pos (mul_pos (h345_0) hs1) (sub_pos.mpr i2), mul_pos
          (mul_pos (h345_0) hs1) (sub_pos.mpr i4), mul_pos (mul_pos (hA0) ht1) (sub_pos.mpr i3),
          mul_pos (mul_pos (he0) hs1) (sub_pos.mpr i3), mul_pos (mul_pos (he0) hs1)
          (sub_pos.mpr i4), mul_pos (mul_pos (he0) hst) (sub_pos.mpr i2), mul_pos
          (mul_pos (he0) hst) (sub_pos.mpr i3), mul_pos (mul_pos (hs) ht) hpsi, mul_pos
          (mul_pos (hst) h345_0) (sub_pos.mpr i2), mul_pos (mul_pos (hst) h345_0) (sub_pos.mpr i4),
          mul_pos (mul_pos (hst) ht1) hpsi, mul_pos (mul_pos (ht) ht) hpsi]

/-- **Lemma 21.9 (F35)** and **Theorem 21.11 (A)**: for `a2 > 0`, `e0 > 0`, `h0 < 1`, `s, t < 1`,
`b2 + h2 > 0` and `e0 a2 < A0 B2`, the vertex crossing `V = 035/1456` (rim `(5, 1, 2, 3)`)
or the edge crossing `Y = 035/356-3` (rim `(5, 0, 1, 4, 6)`) is unimodal, and `K` is Rupert.
`V`'s diagonals `[5, 2]`, `[1, 3]` cross along `d` with `λ = −a2 / K < 0`, so `V` fails only with
`{5, 2}` above `{1, 3}`, hence `⟪d, 5 − 3⟫ > 0`; then `k4_Y_core`. -/
theorem NF29.isRupert_k4_A (N : NF29 x) (ha2 : 0 < N.a2) (he0 : 0 < N.b0 + N.h0 - 1)
    (hbh2 : 0 < N.b2 + N.h2)
    (hs1 : 0 < -N.s + 1) (ht1 : 0 < -N.t + 1) (hh01 : 0 < -N.h0 + 1)
    (hc : 0 < N.a0 * N.b2 - N.a2 * N.b0 - N.a2 * N.h0 + N.a2)
    (hzV : [⟪x 5, N.vV⟫, ⟪x 1, N.vV⟫, ⟪x 2, N.vV⟫, ⟪x 3, N.vV⟫].Nodup)
    (hzY : [⟪x 5, x 5 - x 3⟫, ⟪x 0, x 5 - x 3⟫, ⟪x 1, x 5 - x 3⟫, ⟪x 4, x 5 - x 3⟫,
      ⟪x 6, x 5 - x 3⟫].Nodup)
    (hndV : NoHDNAt (univ.image x) N.vV)
    (hndY : NoHDNAt ((univ.image x).erase (x 3)) (x 5 - x 3)) : IsRupert (univ.image x) := by
  by_cases hsep : DepthSep (x 5) (x 2) (x 1) (x 3) N.vV
  · have hA0 : 0 < -N.a0 := by linarith [N.ha0]
    have hK : 0 < -N.a0 + N.a0 * N.b2 - N.a2 * (N.b0 + N.h0 - 1) := by linarith
    have hm := meet_of_smul (d₀ := x 5) (d₁ := x 2) (e₀ := x 1) (e₁ := x 3) (v := N.vV)
      (K := -N.a0 + N.a0 * N.b2 - N.a2 * (N.b0 + N.h0 - 1)) (s := -N.a0) (t := -N.a0 * N.h2)
      (l := -N.a2) hK.ne' (by simp only [NF29.vV]; nf29_vec N)
    have hA0h2 : 0 < -N.a0 * N.h2 := by nlinarith [mul_pos N.hh2 he0, mul_pos N.hh0 (show
      0 < 1 - N.a2 - N.b2 - N.h2 by linarith [N.t345_2])]
    have hsep' := depthSep_of_meet (div_pos hA0 hK).le ((div_le_one hK).mpr (by linarith))
      (div_pos hA0h2 hK).le ((div_le_one hK).mpr (by linarith [N.hDG5])) hm
      (div_nonpos_of_nonpos_of_nonneg (by linarith) hK.le) hsep
    have h35 : ⟪x 3, N.vV⟫ < ⟪x 5, N.vV⟫ :=
      lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hsep' (min_le_left _ _))
    -- the depths along `u = 5 − 3`
    have v6 : x 6 - x 1 = N.s • (x 4 - x 1) + N.t • (x 5 - x 1) := by nf29_vec N
    have v0 : x 0 - x 1 = N.a0 • (x 4 - x 1) + (N.b0 + N.h0) • (x 5 - x 1) - N.h0 • (x 5 - x 3) :=
        by
      nf29_vec N
    have vd : N.vV = (-N.a0) • (x 4 - x 1) + (-(N.b0 + N.h0 - 1)) • (x 5 - x 1) := by
      simp only [NF29.vV]; nf29_vec N
    have i6 := congrArg (fun w => ⟪w, x 5 - x 3⟫) v6
    have i0 := congrArg (fun w => ⟪w, x 5 - x 3⟫) v0
    simp only [inner_sub_left, inner_add_left, real_inner_smul_left] at i6 i0
    have hq : 0 < ⟪x 5 - x 3, x 5 - x 3⟫ :=
      real_inner_self_pos.mpr (sub_ne_zero.mpr (N.inj.ne (by decide)))
    have hq' : ⟪x 5 - x 3, x 5 - x 3⟫ = ⟪x 5, x 5 - x 3⟫ - ⟪x 3, x 5 - x 3⟫ := inner_sub_left _ _ _
    have ed : ⟪N.vV, x 5 - x 3⟫ = -N.a0 * (⟪x 4, x 5 - x 3⟫ - ⟪x 1, x 5 - x 3⟫) -
        (N.b0 + N.h0 - 1) * (⟪x 5, x 5 - x 3⟫ - ⟪x 1, x 5 - x 3⟫) := by
      rw [vd]; simp only [inner_add_left, real_inner_smul_left, inner_sub_left]; ring
    have hpsi : 0 < -N.a0 * (⟪x 4, x 5 - x 3⟫ - ⟪x 1, x 5 - x 3⟫) -
        (N.b0 + N.h0 - 1) * (⟪x 5, x 5 - x 3⟫ - ⟪x 1, x 5 - x 3⟫) := by
      rw [← ed, inner_sub_right, real_inner_comm (x 5) N.vV, real_inner_comm (x 3) N.vV]
      linarith
    have hY := k4_Y_core (A0 := -N.a0) (e0 := N.b0 + N.h0 - 1) (h0 := N.h0) (s := N.s) (t := N.t)
      (p1 := ⟪x 4, x 5 - x 3⟫ - ⟪x 1, x 5 - x 3⟫) (p2 := ⟪x 5, x 5 - x 3⟫ - ⟪x 1, x 5 - x 3⟫)
      (q := ⟪x 5 - x 3, x 5 - x 3⟫) (z1 := ⟪x 1, x 5 - x 3⟫) (z0 := ⟪x 0, x 5 - x 3⟫)
      (z4 := ⟪x 4, x 5 - x 3⟫) (z5 := ⟪x 5, x 5 - x 3⟫) (z6 := ⟪x 6, x 5 - x 3⟫) hA0 he0 N.hs N.ht
      (by linarith [N.hst]) (by linarith) (by linarith) (by linarith [N.d035]) N.hh0 hq
      (by linarith [N.t345_0]) hpsi (by ring) (by ring) (by linarith) (by rw [hq']; linarith)
      (NF16.quint_inj_of_nodup hzY)
    exact NF29.isRupert_k4_Y N ha2 he0 hs1 hbh2 hY.isRobustUnimodal hndY
  · exact NF29.isRupert_k4_V N he0 hh01 hc (quad_unimodal hsep hzV).isRobustUnimodal hndV
/-- **Test `W = 023/035-0`** (§21.11 (B2)): the edge crossing along `03` (apex `3`, view `3 − 0`),
rim `(3, 5, 1, 2)`; `4` and `6` hidden. -/
theorem NF29.isRupert_k4_W (N : NF29 x)
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
          (quad ⟪x 3, (x 3 - x 0)⟫ ⟪x 5, (x 3 - x 0)⟫ ⟪x 1, (x 3 - x 0)⟫ ⟪x 2, (x 3 - x 0)⟫))
    (hnd : NoHDNAt ((univ.image x).erase (x 0)) ((x 3 - x 0))) : IsRupert (univ.image x) := by
  have hA0 : 0 < -N.a0 := by linarith [N.ha0]
  have hB2 : 0 < -N.b2 := by linarith [N.hb2]
  have h345_0 : 0 < 1 - N.a0 - N.b0 - N.h0 := by linarith [N.t345_0]
  have h345_2 : 0 < 1 - N.a2 - N.b2 - N.h2 := by linarith [N.t345_2]
  have hst : 0 < N.s + N.t - 1 := by linarith [N.hst]
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  refine isRupert_equadσ (univ.image x) (∅ : Finset ℝ³) (u := (x 3 - x 0)) ?_ hσ (h := 1)
      one_ne_zero
    (by module) (img29 0)
    (img29 3) (img29 5) (img29 1) (img29 2)
    (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff])
        (by simp [N.inj.eq_iff]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hz hnd ?_
  · exact sub_ne_zero.mpr (N.inj.ne (by decide))
  · nf29_test N hσD hA0
  · nf29_test N hσD N.hDG5
  · nf29_test N hσD (by show 0 < -N.a0 * N.h2 + N.a2 * N.h0 - N.a2; linarith [he0, hc2, N.hDD])
  · nf29_test N hσD hA0
  · nf29_test N hσD N.hDD
  · nf29_test N hσD (by show 0 < -N.a0 * N.h2 + N.a2 * N.h0 - N.a2; linarith [he0, hc2, N.hDD])
  · nf29_test N hσD N.hDG5
  · nf29_test N hσD N.hDD
  · intro z hz hzM hzw hn0 hn1 hn2 hn3
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    fin_cases i
    · exact absurd rfl hzw
    · exact absurd rfl hn2
    · exact absurd rfl hn3
    · exact absurd rfl hn0
    · refine ⟨?_, ?_, ?_, ?_⟩
      · nf29_test N hσD h345_0
      · nf29_test N hσD hh0g
      · nf29_test N hσD (by
              show 0 < N.b0 * N.h2 - N.b2 * N.h0 + N.b2
              linarith [mul_pos (hB2) hh0g, mul_pos (N.hh2) hb0])
      · nf29_test N hσD N.hDG4
    · exact absurd rfl hn1
    · refine ⟨?_, ?_, ?_, ?_⟩
      · nf29_test N hσD N.d035
      · nf29_test N hσD (by show 0 < N.h0 * N.s - N.s; linarith [mul_pos (N.hs) hh0g])
      · nf29_test N hσD (by
              show 0 < -N.a0 * N.h2 * N.t + N.a2 * N.h0 * N.t + N.b0 * N.h2 * N.s - N.b2 * N.h0 *
                N.s - N.a2 * N.t + N.b2 * N.s
              linarith [mul_pos (hs1) hc2, mul_pos (he2) hh0g, mul_pos (hs1) hh0g, mul_pos (N.hF4)
                  hst, mul_pos (N.hDD) hs1, mul_pos (N.hDD) hst, mul_pos (hB2) N.d234, mul_pos
                  (N.d234) hAh, mul_pos (N.d234) hb0, mul_pos (N.hh2) N.d234, mul_pos
                  (mul_pos (ha2) he2) hs1, mul_pos (mul_pos (ha2) hb0) he2, mul_pos
                  (mul_pos (hst) ha2) he0, mul_pos (mul_pos (ha2) he0) he2, mul_pos
                  (mul_pos (hst) hb0) ht1, mul_pos (mul_pos (hst) he2) he2, mul_pos
                  (mul_pos (hB2) ht1) hh0g, mul_pos (mul_pos (hB2) hb0) hh21, mul_pos
                  (mul_pos (hB2) hs1) hh21, mul_pos (mul_pos (hst) ht1) hbh2, mul_pos
                  (mul_pos (hB2) hB2) hh0g, mul_pos (mul_pos (ha2) hb0) hbh2, mul_pos
                  (mul_pos (N.ht) he2) hAh, mul_pos (mul_pos (hB2) he0) hbh2, mul_pos
                  (mul_pos (hB2) hh0g) hh21, mul_pos (mul_pos (hb0) hbh2) hbh2, mul_pos
                  (mul_pos (N.hh2) he2) hs1, mul_pos (mul_pos (N.ht) ha2) hh0g, mul_pos
                  (mul_pos (N.ht) ha2) hbh2, mul_pos (mul_pos (N.hh2) hA0) hs1, mul_pos
                  (mul_pos (N.ht) he0) hbh2, mul_pos (mul_pos (hB2) N.ht) hbh2, mul_pos
                  (mul_pos (N.ht) N.ht) hb0, mul_pos (mul_pos (N.hh2) he0) he2, mul_pos
                  (mul_pos (hst) hbh2) hbh2, mul_pos (mul_pos (N.hs) N.ht) hb0, mul_pos
                  (mul_pos (hb0) hbh2) hh21, mul_pos (mul_pos (N.hh0) hs1) hbh2, mul_pos
                  (mul_pos (N.hh2) hst) hh0g, mul_pos (mul_pos (N.hh2) N.hs) hb0, mul_pos
                  (mul_pos (h345_2) hb0) hs1, mul_pos (mul_pos (h345_2) he0) ht1, mul_pos
                  (mul_pos (N.hh2) N.ht) hAh, mul_pos (mul_pos (N.ht) N.ht) hbh2, mul_pos
                  (mul_pos (h345_2) he0) he2, mul_pos (mul_pos (N.hs) N.ht) hbh2, mul_pos
                  (mul_pos (N.hh2) N.ht) hh0g, mul_pos (mul_pos (N.hh2) N.hh2) hs1, mul_pos
                  (mul_pos (h345_0) hst) hbh2, mul_pos (mul_pos (h345_2) hst) hh0g, mul_pos
                  (mul_pos (h345_2) N.ht) he2, mul_pos (mul_pos (N.hh0) h345_2) hs1, mul_pos
                  (mul_pos (N.hh2) h345_2) hb0, mul_pos (mul_pos (N.hh2) h345_0) N.ht, mul_pos
                  (mul_pos (h345_2) h345_2) hh0g])
      · nf29_test N hσD N.d023
  · intro m hm
    simp at hm

/-- **Test `Z = 035/234`** (§21.11 (B2)): the vertex crossing at `3`, view `u_Z = (A0 (B2 − e2), B2
(A0 − e0), A0 B2 − e0 e2)` (`n035 × n234`), rim `(3, 0, 1, 4)`; `5` a middle over `3–0`, `2` over
`4–3`, `6` hidden. -/
theorem NF29.isRupert_k4_Z (N : NF29 x)
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
    (hz : IsRobustUnimodal (quad ⟪x 3, N.vZ⟫ ⟪x 0, N.vZ⟫ ⟪x 1, N.vZ⟫ ⟪x 4, N.vZ⟫))
    (hnd : NoHDNAt (univ.image x) (N.vZ)) : IsRupert (univ.image x) := by
  have hA0 : 0 < -N.a0 := by linarith [N.ha0]
  have hB2 : 0 < -N.b2 := by linarith [N.hb2]
  have h345_0 : 0 < 1 - N.a0 - N.b0 - N.h0 := by linarith [N.t345_0]
  have h345_2 : 0 < 1 - N.a2 - N.b2 - N.h2 := by linarith [N.t345_2]
  have hst : 0 < N.s + N.t - 1 := by linarith [N.hst]
  obtain ⟨σ, hσ, hσD⟩ := exists_sign N.hD
  refine isRupert_vquadσ (univ.image x) ({x 2, x 5} : Finset ℝ³) (u := N.vZ) ?_ hσ
    (img29 3) (img29 0) (img29 1) (img29 4)
    (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff]) (by simp [N.inj.eq_iff])
        (by simp [N.inj.eq_iff]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hz hnd ?_
  · exact nfV_ne_zero N.hD (Or.inl (ne_of_gt
            (by
              nlinarith [mul_pos (neg_pos.mpr N.ha0)
                  (show 0 < -N.b2 - (N.a2 + N.h2 - 1) by linarith [N.t345_2])])))
  · simp only [NF29.vZ]; nf29_test N hσD
        (by
          show 0 < N.a0 * N.a2 * N.b0 + N.a0 * N.b0 * N.h2 - N.a0 * N.b2 * N.h0 - N.a0 ^ 2 * N.b2 -
            N.a0 * N.b0 + N.a0 * N.b2
          linarith [mul_pos (he2) hc2, mul_pos (N.d234) ha2, mul_pos (N.d234) hb0, mul_pos (N.hDG4)
              hAh, mul_pos (N.hDG4) ht1, mul_pos (N.hDG4) ha2, mul_pos (N.hDG4) hh0g, mul_pos
              (N.hDG4) hbh2, mul_pos (h345_2) N.hF4, mul_pos (N.hh0) N.d234, mul_pos (N.hh2) N.d234,
              mul_pos (h345_2) N.d035, mul_pos (h345_0) N.d234, mul_pos (mul_pos (hB2) hB2) hst,
              mul_pos (mul_pos (hB2) hst) hs1, mul_pos (mul_pos (hA0) hB2) hst, mul_pos
              (mul_pos (hB2) hst) ht1, mul_pos (mul_pos (hst) hst) he2, mul_pos
              (mul_pos (h345_2) he0) hAh, mul_pos (mul_pos (h345_2) hb0) hb0, mul_pos
              (mul_pos (hA0) h345_2) he2, mul_pos (mul_pos (hB2) h345_2) ht1, mul_pos
              (mul_pos (hB2) hB2) h345_0, mul_pos (mul_pos (hB2) h345_2) hs1, mul_pos
              (mul_pos (hA0) hB2) h345_0, mul_pos (mul_pos (h345_2) hs1) ht1, mul_pos
              (mul_pos (h345_2) N.ht) hAh, mul_pos (mul_pos (h345_2) N.hs) he2, mul_pos
              (mul_pos (h345_0) he2) hh21, mul_pos (mul_pos (hA0) h345_2) N.hs, mul_pos
              (mul_pos (hB2) h345_0) N.ht, mul_pos (mul_pos (h345_2) N.ht) he0, mul_pos
              (mul_pos (h345_2) N.hs) hst, mul_pos (mul_pos (h345_2) ha2) hh0g, mul_pos
              (mul_pos (N.hh2) h345_2) hAh, mul_pos (mul_pos (N.hh0) h345_2) hb0, mul_pos
              (mul_pos (h345_2) N.ht) N.ht, mul_pos (mul_pos (N.hh0) h345_0) he2, mul_pos
              (mul_pos (N.hh2) h345_2) hh0g, mul_pos (mul_pos (h345_2) h345_2) ha2, mul_pos
              (mul_pos (h345_2) h345_2) hst, mul_pos (mul_pos (h345_0) h345_2) he0, mul_pos
              (mul_pos (h345_0) h345_2) hs1, mul_pos (mul_pos (N.hh0) h345_2) hbh2, mul_pos
              (mul_pos (hA0) h345_2) h345_2, mul_pos (mul_pos (h345_2) h345_2) hbh2, mul_pos
              (mul_pos (h345_0) h345_2) hbh2, mul_pos (mul_pos (h345_2) h345_2) h345_2])
  · simp only [NF29.vZ]; nf29_test N hσD
        (by
          show 0 < N.a0 * N.a2 * N.b0 - N.a0 * N.b0 * N.b2 + N.a0 * N.b0 * N.h2 - 2 * N.a0 * N.b2 *
            N.h0 - N.a0 ^ 2 * N.b2 + N.a2 * N.b0 * N.h0 + N.a2 * N.b0 ^ 2 - N.b0 * N.b2 * N.h0 +
            N.b0 * N.h0 * N.h2 + N.b0 ^ 2 * N.h2 - N.b2 * N.h0 ^ 2 - N.a0 * N.b0 + 2 * N.a0 * N.b2 -
            N.a2 * N.b0 + N.b0 * N.b2 - N.b0 * N.h0 - N.b0 * N.h2 - N.b0 ^ 2 + 2 * N.b2 * N.h0 +
            N.b0 - N.b2
          linarith [mul_pos (h345_0) N.hDG4])
  · simp only [NF29.vZ]; nf29_test N hσD
        (by
          show 0 < N.a0 * N.b0 * N.b2 + N.a0 * N.b2 * N.h0 - N.a2 * N.b0 * N.h0 - N.a2 * N.b0 ^ 2 +
            N.b0 * N.b2 * N.h0 - N.b0 * N.h0 * N.h2 - N.b0 ^ 2 * N.h2 + N.b2 * N.h0 ^ 2 + N.a2 *
            N.b0 + N.b0 * N.h0 + N.b0 * N.h2 + N.b0 ^ 2 - N.b2 * N.h0 - N.b0
          linarith [mul_pos (he2) hc2, mul_pos (h345_2) hc2, mul_pos (N.hDG4) he0, mul_pos (N.hDG4)
              hb0, mul_pos (h345_2) N.hDD, mul_pos (mul_pos (hB2) h345_2) hAh, mul_pos
              (mul_pos (h345_2) ha2) hAh, mul_pos (mul_pos (hB2) hB2) h345_2, mul_pos
              (mul_pos (h345_2) ha2) ha2, mul_pos (mul_pos (h345_2) ha2) he0, mul_pos
              (mul_pos (hB2) h345_0) ha2, mul_pos (mul_pos (h345_2) hh0g) hAh, mul_pos
              (mul_pos (h345_2) he2) hbh2, mul_pos (mul_pos (N.hh0) h345_0) he2, mul_pos
              (mul_pos (N.hh2) h345_2) hh21, mul_pos (mul_pos (N.hh2) h345_2) hh0g, mul_pos
              (mul_pos (h345_2) h345_2) ha2, mul_pos (mul_pos (h345_2) h345_2) hbh2, mul_pos
              (mul_pos (h345_0) h345_2) hbh2, mul_pos (mul_pos (h345_2) h345_2) hh0g, mul_pos
              (mul_pos (h345_0) h345_2) h345_2])
  · simp only [NF29.vZ]; nf29_test N hσD
        (by
          show 0 < N.a0 * N.a2 * N.b0 + N.a0 * N.b0 * N.h2 - N.a0 * N.b2 * N.h0 - N.a0 ^ 2 * N.b2 -
            N.a0 * N.b0 + N.a0 * N.b2
          linarith [mul_pos (he2) hc2, mul_pos (N.d234) ha2, mul_pos (N.d234) hb0, mul_pos (N.hDG4)
              hAh, mul_pos (N.hDG4) ht1, mul_pos (N.hDG4) ha2, mul_pos (N.hDG4) hh0g, mul_pos
              (N.hDG4) hbh2, mul_pos (h345_2) N.hF4, mul_pos (N.hh0) N.d234, mul_pos (N.hh2) N.d234,
              mul_pos (h345_2) N.d035, mul_pos (h345_0) N.d234, mul_pos (mul_pos (hB2) hB2) hst,
              mul_pos (mul_pos (hB2) hst) hs1, mul_pos (mul_pos (hA0) hB2) hst, mul_pos
              (mul_pos (hB2) hst) ht1, mul_pos (mul_pos (hst) hst) he2, mul_pos
              (mul_pos (h345_2) he0) hAh, mul_pos (mul_pos (h345_2) hb0) hb0, mul_pos
              (mul_pos (hA0) h345_2) he2, mul_pos (mul_pos (hB2) h345_2) ht1, mul_pos
              (mul_pos (hB2) hB2) h345_0, mul_pos (mul_pos (hB2) h345_2) hs1, mul_pos
              (mul_pos (hA0) hB2) h345_0, mul_pos (mul_pos (h345_2) hs1) ht1, mul_pos
              (mul_pos (h345_2) N.ht) hAh, mul_pos (mul_pos (h345_2) N.hs) he2, mul_pos
              (mul_pos (h345_0) he2) hh21, mul_pos (mul_pos (hA0) h345_2) N.hs, mul_pos
              (mul_pos (hB2) h345_0) N.ht, mul_pos (mul_pos (h345_2) N.ht) he0, mul_pos
              (mul_pos (h345_2) N.hs) hst, mul_pos (mul_pos (h345_2) ha2) hh0g, mul_pos
              (mul_pos (N.hh2) h345_2) hAh, mul_pos (mul_pos (N.hh0) h345_2) hb0, mul_pos
              (mul_pos (h345_2) N.ht) N.ht, mul_pos (mul_pos (N.hh0) h345_0) he2, mul_pos
              (mul_pos (N.hh2) h345_2) hh0g, mul_pos (mul_pos (h345_2) h345_2) ha2, mul_pos
              (mul_pos (h345_2) h345_2) hst, mul_pos (mul_pos (h345_0) h345_2) he0, mul_pos
              (mul_pos (h345_0) h345_2) hs1, mul_pos (mul_pos (N.hh0) h345_2) hbh2, mul_pos
              (mul_pos (hA0) h345_2) h345_2, mul_pos (mul_pos (h345_2) h345_2) hbh2, mul_pos
              (mul_pos (h345_0) h345_2) hbh2, mul_pos (mul_pos (h345_2) h345_2) h345_2])
  · simp only [NF29.vZ]; nf29_test N hσD
        (by
          show 0 < N.a0 * N.b2 + N.b0 * N.b2 + N.b2 * N.h0 - N.b2
          linarith [mul_pos (hB2) h345_0])
  · simp only [NF29.vZ]; nf29_test N hσD
        (by
          show 0 < N.a0 * N.b0 * N.b2 + N.a0 * N.b2 * N.h0 - N.a2 * N.b0 * N.h0 - N.a2 * N.b0 ^ 2 +
            N.b0 * N.b2 * N.h0 - N.b0 * N.h0 * N.h2 - N.b0 ^ 2 * N.h2 + N.b2 * N.h0 ^ 2 + N.a2 *
            N.b0 + N.b0 * N.h0 + N.b0 * N.h2 + N.b0 ^ 2 - N.b2 * N.h0 - N.b0
          linarith [mul_pos (he2) hc2, mul_pos (h345_2) hc2, mul_pos (N.hDG4) he0, mul_pos (N.hDG4)
              hb0, mul_pos (h345_2) N.hDD, mul_pos (mul_pos (hB2) h345_2) hAh, mul_pos
              (mul_pos (h345_2) ha2) hAh, mul_pos (mul_pos (hB2) hB2) h345_2, mul_pos
              (mul_pos (h345_2) ha2) ha2, mul_pos (mul_pos (h345_2) ha2) he0, mul_pos
              (mul_pos (hB2) h345_0) ha2, mul_pos (mul_pos (h345_2) hh0g) hAh, mul_pos
              (mul_pos (h345_2) he2) hbh2, mul_pos (mul_pos (N.hh0) h345_0) he2, mul_pos
              (mul_pos (N.hh2) h345_2) hh21, mul_pos (mul_pos (N.hh2) h345_2) hh0g, mul_pos
              (mul_pos (h345_2) h345_2) ha2, mul_pos (mul_pos (h345_2) h345_2) hbh2, mul_pos
              (mul_pos (h345_0) h345_2) hbh2, mul_pos (mul_pos (h345_2) h345_2) hh0g, mul_pos
              (mul_pos (h345_0) h345_2) h345_2])
  · simp only [NF29.vZ]; nf29_test N hσD
        (by
          show 0 < N.a0 * N.a2 * N.b0 - N.a0 * N.b0 * N.b2 + N.a0 * N.b0 * N.h2 - 2 * N.a0 * N.b2 *
            N.h0 - N.a0 ^ 2 * N.b2 + N.a2 * N.b0 * N.h0 + N.a2 * N.b0 ^ 2 - N.b0 * N.b2 * N.h0 +
            N.b0 * N.h0 * N.h2 + N.b0 ^ 2 * N.h2 - N.b2 * N.h0 ^ 2 - N.a0 * N.b0 + 2 * N.a0 * N.b2 -
            N.a2 * N.b0 + N.b0 * N.b2 - N.b0 * N.h0 - N.b0 * N.h2 - N.b0 ^ 2 + 2 * N.b2 * N.h0 +
            N.b0 - N.b2
          linarith [mul_pos (h345_0) N.hDG4])
  · simp only [NF29.vZ]; nf29_test N hσD
        (by
          show 0 < N.a0 * N.b2 + N.b0 * N.b2 + N.b2 * N.h0 - N.b2
          linarith [mul_pos (hB2) h345_0])
  · intro z hz hzM hn0 hn1 hn2 hn3
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    fin_cases i
    · exact absurd rfl hn1
    · exact absurd rfl hn2
    · exact absurd (by simp) hzM
    · exact absurd rfl hn0
    · exact absurd rfl hn3
    · exact absurd (by simp) hzM
    · refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [NF29.vZ]; nf29_test N hσD
            (by
              show 0 < -N.a0 * N.a2 * N.b0 * N.t - N.a0 * N.b0 * N.b2 * N.s - N.a0 * N.b0 * N.h2 *
                N.t - N.a0 * N.b2 * N.h0 * N.s + N.a0 * N.b2 * N.h0 * N.t + N.a0 ^ 2 * N.b2 * N.t +
                N.a2 * N.b0 * N.h0 * N.s + N.a2 * N.b0 ^ 2 * N.s - N.b0 * N.b2 * N.h0 * N.s + N.b0 *
                N.h0 * N.h2 * N.s + N.b0 ^ 2 * N.h2 * N.s - N.b2 * N.h0 ^ 2 * N.s + N.a0 * N.a2 *
                N.b0 + N.a0 * N.b0 * N.h2 + N.a0 * N.b0 * N.t - N.a0 * N.b2 * N.h0 + N.a0 * N.b2 *
                N.s - N.a0 * N.b2 * N.t - N.a0 ^ 2 * N.b2 - N.a2 * N.b0 * N.s + N.b0 * N.b2 * N.s -
                N.b0 * N.h0 * N.s - N.b0 * N.h2 * N.s - N.b0 ^ 2 * N.s + 2 * N.b2 * N.h0 * N.s -
                N.a0 * N.b0 + N.a0 * N.b2 + N.b0 * N.s - N.b2 * N.s
              linarith [mul_pos (N.hDG4) N.d035])
      · simp only [NF29.vZ]; nf29_test N hσD
            (by
              show 0 < N.a0 * N.a2 * N.b0 * N.t + N.a0 * N.b0 * N.b2 * N.s + N.a0 * N.b0 * N.h2 *
                N.t + N.a0 * N.b2 * N.h0 * N.s - N.a0 * N.b2 * N.h0 * N.t - N.a0 ^ 2 * N.b2 * N.t -
                N.a2 * N.b0 * N.h0 * N.s - N.a2 * N.b0 ^ 2 * N.s + N.b0 * N.b2 * N.h0 * N.s - N.b0 *
                N.h0 * N.h2 * N.s - N.b0 ^ 2 * N.h2 * N.s + N.b2 * N.h0 ^ 2 * N.s - N.a0 * N.a2 *
                N.t - N.a0 * N.b0 * N.t - N.a0 * N.h2 * N.t + N.a2 * N.b0 * N.s + N.b0 * N.h0 * N.s
                + N.b0 * N.h2 * N.s + N.b0 ^ 2 * N.s - N.b2 * N.h0 * N.s + N.a0 * N.t - N.b0 * N.s
              linarith [mul_pos (N.d023) he2, mul_pos (mul_pos (hA0) hst) he2, mul_pos
                  (mul_pos (he2) hh0g) hc2, mul_pos (mul_pos (hB2) N.hDD) hst, mul_pos
                  (mul_pos (N.hh0) he2) hc2, mul_pos (mul_pos (N.hDG5) hst) hb0, mul_pos
                  (mul_pos (N.hDG4) hb0) ht1, mul_pos (mul_pos (hB2) N.d035) hs1, mul_pos
                  (mul_pos (hst) N.d035) he2, mul_pos (mul_pos (hB2) N.d035) ht1, mul_pos
                  (mul_pos (N.hDG4) hst) he0, mul_pos (mul_pos (N.hDG4) he2) hs1, mul_pos
                  (mul_pos (N.hDG5) he2) hs1, mul_pos (mul_pos (h345_2) ht1) hc2, mul_pos
                  (mul_pos (N.hDG4) hs1) hAh, mul_pos (mul_pos (N.hDG4) ha2) ht1, mul_pos
                  (mul_pos (h345_2) hst) hc2, mul_pos (mul_pos (h345_2) he2) hh0g, mul_pos
                  (mul_pos (h345_2) hh0g) hAh, mul_pos (mul_pos (N.hDG5) he2) hh0g, mul_pos
                  (mul_pos (h345_0) he2) hh21, mul_pos (mul_pos (h345_2) ht1) hh0g, mul_pos
                  (mul_pos (h345_0) N.ht) he2, mul_pos (mul_pos (h345_0) N.hs) he2, mul_pos
                  (mul_pos (h345_2) hst) hh0g, mul_pos (mul_pos (N.hDG4) N.hs) hb0, mul_pos
                  (mul_pos (N.hDG4) N.hs) ha2, mul_pos (mul_pos (N.hDG4) N.ht) hAh, mul_pos
                  (mul_pos (h345_0) N.hDD) hst, mul_pos (mul_pos (h345_2) N.hDD) ht1, mul_pos
                  (mul_pos (h345_0) h345_2) hst, mul_pos (mul_pos (h345_2) N.hs) N.d035, mul_pos
                  (mul_pos (h345_2) N.ht) N.d035])
      · simp only [NF29.vZ]; nf29_test N hσD
            (by
              show 0 < N.a0 * N.b2 * N.t - N.a2 * N.b0 * N.t - N.a2 * N.h0 * N.t - N.b0 * N.h2 * N.t
                - N.h0 * N.h2 * N.t + N.a2 * N.t + N.b0 * N.t + N.h0 * N.t + N.h2 * N.t - N.t
              linarith [mul_pos (N.hDG4) hst, mul_pos (N.d234) he0, mul_pos (mul_pos (hA0) hst) he2,
                  mul_pos (mul_pos (hB2) hst) he0, mul_pos (mul_pos (h345_0) he2) hs1, mul_pos
                  (mul_pos (h345_2) hst) hh0g, mul_pos (mul_pos (h345_0) h345_2) hs1, mul_pos
                  (mul_pos (h345_0) h345_2) hst])
      · simp only [NF29.vZ]; nf29_test N hσD
            (by
              show 0 < N.a0 * N.a2 * N.t - N.a0 * N.b2 * N.s + N.a0 * N.h2 * N.t + N.a2 * N.b0 * N.t
                + N.a2 * N.h0 * N.t - N.b0 * N.b2 * N.s + N.b0 * N.h2 * N.t - N.b2 * N.h0 * N.s +
                N.h0 * N.h2 * N.t + N.a0 * N.b2 - N.a0 * N.t - N.a2 * N.t + N.b0 * N.b2 - N.b0 * N.t
                + N.b2 * N.h0 + N.b2 * N.s - N.h0 * N.t - N.h2 * N.t - N.b2 + N.t
              linarith [mul_pos (h345_0) N.d234])
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · have hmid := mid_comb (m := x 2) (X := x 4) (Y := x 3) (U := N.vZ)
        (D₀ := N.a0 * N.b2 + N.b0 * N.b2 + N.b2 * N.h0 - N.b2)
            (α := N.a0 * N.b2 * N.h2 + N.a0 * N.b2 ^ 2 - N.a2 * N.b0 * N.b2 - N.a2 * N.b2 * N.h0 +
              N.a2 * N.b2 + N.b0 * N.b2 + N.b2 * N.h0 - N.b2) (β := N.b2)
        (by linarith [mul_pos (hB2) h345_0]) (by linarith [mul_pos (hB2) hc2])
        (by linarith [mul_pos (hB2) N.hDG5])
        (ne_of_lt (by linarith [hB2]))
        (by simp only [NF29.vZ]; nf29_vec N)
      obtain ⟨s, δ, h1, h2, h3, h4⟩ := hmid
      exact ⟨s, δ, h1, h2, h3, Or.inr <| Or.inr <| Or.inr <| h4⟩
    · have hmid := mid_comb (m := x 5) (X := x 3) (Y := x 0) (U := N.vZ)
        (D₀ := N.a0 * N.a2 * N.b0 + N.a0 * N.b0 * N.h2 - N.a0 * N.b2 * N.h0 - N.a0 ^ 2 * N.b2 - N.a0
              * N.b0 + N.a0 * N.b2) (α := N.a0 * N.a2 + N.a0 * N.b2 + N.a0 * N.h2 - N.a0)
            (β := -N.a0)
        (by
              linarith [mul_pos (he2) hc2, mul_pos (N.d234) ha2, mul_pos (N.d234) hb0, mul_pos
                  (N.hDG4) hAh, mul_pos (N.hDG4) ht1, mul_pos (N.hDG4) ha2, mul_pos (N.hDG4) hh0g,
                  mul_pos (N.hDG4) hbh2, mul_pos (h345_2) N.hF4, mul_pos (N.hh0) N.d234, mul_pos
                  (N.hh2) N.d234, mul_pos (h345_2) N.d035, mul_pos (h345_0) N.d234, mul_pos
                  (mul_pos (hB2) hB2) hst, mul_pos (mul_pos (hB2) hst) hs1, mul_pos
                  (mul_pos (hA0) hB2) hst, mul_pos (mul_pos (hB2) hst) ht1, mul_pos
                  (mul_pos (hst) hst) he2, mul_pos (mul_pos (h345_2) he0) hAh, mul_pos
                  (mul_pos (h345_2) hb0) hb0, mul_pos (mul_pos (hA0) h345_2) he2, mul_pos
                  (mul_pos (hB2) h345_2) ht1, mul_pos (mul_pos (hB2) hB2) h345_0, mul_pos
                  (mul_pos (hB2) h345_2) hs1, mul_pos (mul_pos (hA0) hB2) h345_0, mul_pos
                  (mul_pos (h345_2) hs1) ht1, mul_pos (mul_pos (h345_2) N.ht) hAh, mul_pos
                  (mul_pos (h345_2) N.hs) he2, mul_pos (mul_pos (h345_0) he2) hh21, mul_pos
                  (mul_pos (hA0) h345_2) N.hs, mul_pos (mul_pos (hB2) h345_0) N.ht, mul_pos
                  (mul_pos (h345_2) N.ht) he0, mul_pos (mul_pos (h345_2) N.hs) hst, mul_pos
                  (mul_pos (h345_2) ha2) hh0g, mul_pos (mul_pos (N.hh2) h345_2) hAh, mul_pos
                  (mul_pos (N.hh0) h345_2) hb0, mul_pos (mul_pos (h345_2) N.ht) N.ht, mul_pos
                  (mul_pos (N.hh0) h345_0) he2, mul_pos (mul_pos (N.hh2) h345_2) hh0g, mul_pos
                  (mul_pos (h345_2) h345_2) ha2, mul_pos (mul_pos (h345_2) h345_2) hst, mul_pos
                  (mul_pos (h345_0) h345_2) he0, mul_pos (mul_pos (h345_0) h345_2) hs1, mul_pos
                  (mul_pos (N.hh0) h345_2) hbh2, mul_pos (mul_pos (hA0) h345_2) h345_2, mul_pos
                  (mul_pos (h345_2) h345_2) hbh2, mul_pos (mul_pos (h345_0) h345_2) hbh2, mul_pos
                  (mul_pos (h345_2) h345_2) h345_2]) (by linarith [mul_pos (hA0) h345_2])
        (by
              linarith [mul_pos (he2) hc2, mul_pos (N.d234) he2, mul_pos (mul_pos (hst) he2) he2,
                  mul_pos (mul_pos (h345_2) hst) he2, mul_pos (mul_pos (h345_2) he0) hAh, mul_pos
                  (mul_pos (h345_2) ha2) hAh, mul_pos (mul_pos (hB2) h345_2) hAh, mul_pos
                  (mul_pos (hB2) h345_0) hAh, mul_pos (mul_pos (h345_2) he2) ht1, mul_pos
                  (mul_pos (h345_2) hAh) hAh, mul_pos (mul_pos (h345_0) he2) he2, mul_pos
                  (mul_pos (hA0) h345_0) he2, mul_pos (mul_pos (h345_2) he2) hh0g, mul_pos
                  (mul_pos (h345_2) hh0g) hAh, mul_pos (mul_pos (h345_0) he2) hh0g, mul_pos
                  (mul_pos (h345_0) he2) hh21, mul_pos (mul_pos (h345_2) hbh2) hAh])
        (ne_of_gt (by linarith [hA0]))
        (by simp only [NF29.vZ]; nf29_vec N)
      obtain ⟨s, δ, h1, h2, h3, h4⟩ := hmid
      exact ⟨s, δ, h1, h2, h3, Or.inl <| h4⟩

/-- `SegMeet` from a combination with a common positive denominator. -/
theorem segMeet_of_smul {d₀ d₁ e₀ e₁ v : ℝ³} {K s t l : ℝ} (hK : 0 < K) (hs : 0 < s)
    (hs' : 0 < K - s) (ht : 0 < t) (ht' : 0 < K - t)
    (h : K • (e₀ - d₀) + t • (e₁ - e₀) - s • (d₁ - d₀) = l • v) : SegMeet d₀ d₁ e₀ e₁ v :=
  ⟨s / K, t / K, l / K, (div_pos hs hK).le, (div_le_one hK).mpr (by linarith), (div_pos ht hK).le,
    (div_le_one hK).mpr (by linarith), meet_of_smul hK.ne' h⟩

/-- The sign of a product of four frame determinants. -/
theorem det4_neg {D X1 X2 X3 X4 P1 P2 P3 P4 : ℝ} (hD : D ≠ 0) (e1 : X1 = P1 * D)
    (e2 : X2 = P2 * D) (e3 : X3 = P3 * D) (e4 : X4 = P4 * D) (h : P1 * P2 * (P3 * P4) < 0) :
    X1 * X2 * (X3 * X4) < 0 := by
  subst e1 e2 e3 e4
  have hDD : 0 < D * D := mul_self_pos.mpr hD
  rw [show P1 * D * (P2 * D) * (P3 * D * (P4 * D)) = P1 * P2 * (P3 * P4) * ((D * D) * (D * D)) by
    ring]
  exact mul_neg_of_neg_of_pos h (mul_pos hDD hDD)

theorem depthSep_swap₂ {d₀ d₁ e₀ e₁ u : ℝ³} (h : DepthSep d₀ d₁ e₀ e₁ u) :
    DepthSep d₀ d₁ e₁ e₀ u := by
  simp only [DepthSep, max_comm ⟪e₁, u⟫, min_comm ⟪e₁, u⟫] at h ⊢
  exact h

/-- **Lemma 21.10 (F35′)** and **Theorem 21.11 (B2)**: for `a2, b0 > 0`, the edge crossing
`W = 023/035-0` (rim `(3, 5, 1, 2)`) and the vertex crossing `Z = 035/234` (rim `(3, 0, 1, 4)`)
share the diagonal `[1, 3]`; their other diagonals `[5, 2]`, `[4, 0]` meet `[1, 3]` along both views
(`0` and `3` coincide along `3 − 0`), and the four determinants have a negative product, so the two
rims are not both depth-separated (Corollary 13.3, `not_both_depthSep`): one test is unimodal. -/
theorem NF29.isRupert_k4_B2 (N : NF29 x)
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
    (hzW : [⟪x 3, x 3 - x 0⟫, ⟪x 5, x 3 - x 0⟫, ⟪x 1, x 3 - x 0⟫, ⟪x 2, x 3 - x 0⟫].Nodup)
    (hzZ : [⟪x 3, N.vZ⟫, ⟪x 0, N.vZ⟫, ⟪x 1, N.vZ⟫, ⟪x 4, N.vZ⟫].Nodup)
    (hndW : NoHDNAt ((univ.image x).erase (x 0)) (x 3 - x 0))
    (hndZ : NoHDNAt (univ.image x) N.vZ) : IsRupert (univ.image x) := by
  have hA0 : 0 < -N.a0 := by linarith [N.ha0]
  have hB2 : 0 < -N.b2 := by linarith [N.hb2]
  have h345_0 : 0 < 1 - N.a0 - N.b0 - N.h0 := by linarith [N.t345_0]
  have h345_2 : 0 < 1 - N.a2 - N.b2 - N.h2 := by linarith [N.t345_2]
  have hst : 0 < N.s + N.t - 1 := by linarith [N.hst]
  have m1u : SegMeet (x 3) (x 1) (x 5) (x 2) (x 3 - x 0) := segMeet_of_smul
    (K := N.a0 * N.b2 - N.a2 * N.b0 - N.a0)
    (s := N.a0 * N.b2 + N.a0 * N.h2 - N.a2 * N.b0 - N.a2 * N.h0 - N.a0 + N.a2)
    (t := -N.a0)
    (l := N.a2)
    (by linarith [N.hDG5, mul_pos (ha2) hh0g, mul_pos (N.hh2) hA0])
    (by linarith [N.hDG5])
    (by linarith [he0, hc2, N.hDD])
    (by linarith [hA0])
    (by linarith [N.hDD])
    (by nf29_vec N)
  have m1v : SegMeet (x 3) (x 1) (x 5) (x 2) N.vZ := segMeet_of_smul
    (K := -N.a0 * N.b2 * N.h2 - N.a0 * N.b2 ^ 2 + N.a2 * N.b0 * N.b2 + N.a2 * N.b2 * N.h0 + N.a0 *
          N.a2 + 2 * N.a0 * N.b2 + N.a0 * N.h2 - N.a2 * N.b2 - N.a0)
    (s := -N.a0 * N.a2 * N.b2 - N.a0 * N.a2 * N.h2 - 2 * N.a0 * N.b2 * N.h2 - N.a0 * N.b2 ^ 2 - N.a0
          * N.h2 ^ 2 + N.a2 * N.b0 * N.b2 + N.a2 * N.b0 * N.h2 + N.a2 * N.b2 * N.h0 + N.a2 * N.h0 *
          N.h2 + N.a2 ^ 2 * N.b0 + N.a2 ^ 2 * N.h0 + N.a0 * N.a2 + 2 * N.a0 * N.b2 + 2 * N.a0 * N.h2
          - N.a2 * N.b0 - N.a2 * N.b2 - N.a2 * N.h0 - N.a2 * N.h2 - N.a2 ^ 2 - N.a0 + N.a2)
    (t := N.a0 * N.a2 + N.a0 * N.b2 + N.a0 * N.h2 - N.a0)
    (l := N.a2)
    (by
          linarith [mul_pos (hB2) N.hDG5, mul_pos (hB2) h345_2, mul_pos (N.d234) hb0, mul_pos
              (N.hDG4) hh21, mul_pos (N.hh0) N.d234, mul_pos (h345_2) N.d035, mul_pos
              (mul_pos (hB2) hst) hs1, mul_pos (mul_pos (hB2) hst) hst, mul_pos (mul_pos (hB2) hst)
              he0, mul_pos (mul_pos (hB2) hst) ht1, mul_pos (mul_pos (h345_0) he2) he2, mul_pos
              (mul_pos (h345_2) ha2) hAh, mul_pos (mul_pos (h345_2) he0) ht1, mul_pos
              (mul_pos (hB2) hB2) h345_0, mul_pos (mul_pos (h345_2) N.hs) hAh, mul_pos
              (mul_pos (h345_2) ha2) hh0g, mul_pos (mul_pos (hA0) h345_2) N.ht, mul_pos
              (mul_pos (N.hh2) h345_2) he0, mul_pos (mul_pos (N.hh2) h345_2) hAh, mul_pos
              (mul_pos (N.hh0) h345_2) ht1, mul_pos (mul_pos (h345_2) N.ht) hh0g, mul_pos
              (mul_pos (h345_0) h345_2) ha2, mul_pos (mul_pos (N.hh0) h345_2) N.hs, mul_pos
              (mul_pos (h345_2) h345_2) hAh, mul_pos (mul_pos (h345_0) h345_2) hs1, mul_pos
              (mul_pos (h345_0) h345_2) hbh2, mul_pos (mul_pos (h345_2) h345_2) hh0g])
    (by linarith [mul_pos (h345_2) N.hDG5])
    (by
          linarith [mul_pos (N.d234) ha2, mul_pos (h345_2) hc2, mul_pos (N.d234) hAh, mul_pos
              (N.hDG5) he2, mul_pos (h345_2) hh21, mul_pos (N.hDG4) hh21, mul_pos (N.d234) hh0g,
              mul_pos (N.d234) hbh2, mul_pos (N.hh2) N.d234, mul_pos (mul_pos (hA0) hst) he2,
              mul_pos (mul_pos (hst) he2) he2, mul_pos (mul_pos (h345_0) he2) he2, mul_pos
              (mul_pos (hA0) h345_2) ht1, mul_pos (mul_pos (h345_2) ha2) hAh, mul_pos
              (mul_pos (hB2) h345_2) ht1, mul_pos (mul_pos (hB2) hB2) h345_0, mul_pos
              (mul_pos (h345_2) hst) hb0, mul_pos (mul_pos (h345_2) ha2) hh0g, mul_pos
              (mul_pos (N.hh0) h345_2) he2, mul_pos (mul_pos (h345_2) N.hs) hh0g, mul_pos
              (mul_pos (N.hh2) h345_2) hb0, mul_pos (mul_pos (N.hh2) hA0) h345_2, mul_pos
              (mul_pos (h345_2) N.ht) hh0g, mul_pos (mul_pos (h345_2) h345_2) hs1, mul_pos
              (mul_pos (h345_2) h345_2) hAh, mul_pos (mul_pos (h345_0) h345_2) hst, mul_pos
              (mul_pos (h345_2) h345_2) N.ht, mul_pos (mul_pos (h345_0) h345_2) hbh2, mul_pos
              (mul_pos (h345_2) h345_2) hh0g])
    (by linarith [mul_pos (hA0) h345_2])
    (by linarith [mul_pos (hB2) N.hDG5])
    (by simp only [NF29.vZ]; nf29_vec N)
  have m2v : SegMeet (x 3) (x 1) (x 4) (x 0) N.vZ := segMeet_of_smul
    (K := N.a0 * N.a2 * N.b0 + N.a0 * N.b0 * N.h2 - N.a0 * N.b2 * N.h0 - N.a0 ^ 2 * N.b2 - N.a0 *
          N.b0 + 2 * N.a0 * N.b2 + N.b0 * N.b2 + N.b2 * N.h0 - N.b2)
    (s := N.a0 * N.a2 * N.b0 - N.a0 * N.b0 * N.b2 + N.a0 * N.b0 * N.h2 - 2 * N.a0 * N.b2 * N.h0 -
          N.a0 ^ 2 * N.b2 + N.a2 * N.b0 * N.h0 + N.a2 * N.b0 ^ 2 - N.b0 * N.b2 * N.h0 + N.b0 * N.h0
          * N.h2 + N.b0 ^ 2 * N.h2 - N.b2 * N.h0 ^ 2 - N.a0 * N.b0 + 2 * N.a0 * N.b2 - N.a2 * N.b0 +
          N.b0 * N.b2 - N.b0 * N.h0 - N.b0 * N.h2 - N.b0 ^ 2 + 2 * N.b2 * N.h0 + N.b0 - N.b2)
    (t := N.a0 * N.b2 + N.b0 * N.b2 + N.b2 * N.h0 - N.b2)
    (l := N.b0)
    (by
          linarith [mul_pos (he2) hc2, mul_pos (N.hDD) hst, mul_pos (h345_2) he2, mul_pos (N.d234)
              he2, mul_pos (N.d234) hAh, mul_pos (N.hDG4) hb0, mul_pos (N.hDG4) hh21, mul_pos
              (N.d234) hh0g, mul_pos (N.d234) hh21, mul_pos (N.d234) hbh2, mul_pos (h345_2) N.hDD,
              mul_pos (N.hh0) N.hDG4, mul_pos (h345_0) h345_2, mul_pos (h345_2) N.d035, mul_pos
              (mul_pos (hB2) hst) he0, mul_pos (mul_pos (hst) hb0) hh21, mul_pos
              (mul_pos (h345_2) he0) hAh, mul_pos (mul_pos (h345_0) he0) he2, mul_pos
              (mul_pos (h345_2) hb0) ht1, mul_pos (mul_pos (hB2) h345_0) hb0, mul_pos
              (mul_pos (h345_2) ha2) hAh, mul_pos (mul_pos (h345_2) hAh) hAh, mul_pos
              (mul_pos (hB2) hB2) h345_0, mul_pos (mul_pos (hA0) h345_2) hs1, mul_pos
              (mul_pos (hB2) h345_0) ha2, mul_pos (mul_pos (h345_2) N.hs) hAh, mul_pos
              (mul_pos (hA0) h345_2) hbh2, mul_pos (mul_pos (h345_2) hbh2) hAh, mul_pos
              (mul_pos (h345_2) hst) hbh2, mul_pos (mul_pos (hB2) h345_0) hbh2, mul_pos
              (mul_pos (h345_2) N.hs) hh21, mul_pos (mul_pos (N.hh2) h345_2) hAh, mul_pos
              (mul_pos (h345_2) N.hs) hh0g, mul_pos (mul_pos (N.hh0) h345_2) ht1, mul_pos
              (mul_pos (N.hh0) h345_2) ha2, mul_pos (mul_pos (h345_2) hh0g) hh21, mul_pos
              (mul_pos (h345_2) N.ht) hh21, mul_pos (mul_pos (h345_0) h345_0) he2, mul_pos
              (mul_pos (hB2) h345_0) h345_0, mul_pos (mul_pos (h345_2) h345_2) hs1, mul_pos
              (mul_pos (h345_2) h345_2) hAh, mul_pos (mul_pos (h345_2) h345_2) hst, mul_pos
              (mul_pos (h345_0) h345_2) h345_2])
    (by linarith [mul_pos (h345_0) N.hDG4])
    (by
          linarith [mul_pos (he2) hc2, mul_pos (h345_2) hc2, mul_pos (N.hDG4) he0, mul_pos (N.hDG4)
              hb0, mul_pos (h345_2) N.hDD, mul_pos (mul_pos (hB2) h345_2) hAh, mul_pos
              (mul_pos (h345_2) ha2) hAh, mul_pos (mul_pos (hB2) hB2) h345_2, mul_pos
              (mul_pos (h345_2) ha2) ha2, mul_pos (mul_pos (h345_2) ha2) he0, mul_pos
              (mul_pos (hB2) h345_0) ha2, mul_pos (mul_pos (h345_2) hh0g) hAh, mul_pos
              (mul_pos (h345_2) he2) hbh2, mul_pos (mul_pos (N.hh0) h345_0) he2, mul_pos
              (mul_pos (N.hh2) h345_2) hh21, mul_pos (mul_pos (N.hh2) h345_2) hh0g, mul_pos
              (mul_pos (h345_2) h345_2) ha2, mul_pos (mul_pos (h345_2) h345_2) hbh2, mul_pos
              (mul_pos (h345_0) h345_2) hbh2, mul_pos (mul_pos (h345_2) h345_2) hh0g, mul_pos
              (mul_pos (h345_0) h345_2) h345_2])
    (by linarith [mul_pos (hB2) h345_0])
    (by
          linarith [mul_pos (he2) hc2, mul_pos (N.d234) ha2, mul_pos (N.d234) hb0, mul_pos (N.hDG4)
              hAh, mul_pos (N.hDG4) ht1, mul_pos (N.hDG4) ha2, mul_pos (N.hDG4) hh0g, mul_pos
              (N.hDG4) hbh2, mul_pos (h345_2) N.hF4, mul_pos (N.hh0) N.d234, mul_pos (N.hh2) N.d234,
              mul_pos (h345_2) N.d035, mul_pos (h345_0) N.d234, mul_pos (mul_pos (hB2) hB2) hst,
              mul_pos (mul_pos (hB2) hst) hs1, mul_pos (mul_pos (hA0) hB2) hst, mul_pos
              (mul_pos (hB2) hst) ht1, mul_pos (mul_pos (hst) hst) he2, mul_pos
              (mul_pos (h345_2) he0) hAh, mul_pos (mul_pos (h345_2) hb0) hb0, mul_pos
              (mul_pos (hA0) h345_2) he2, mul_pos (mul_pos (hB2) h345_2) ht1, mul_pos
              (mul_pos (hB2) hB2) h345_0, mul_pos (mul_pos (hB2) h345_2) hs1, mul_pos
              (mul_pos (hA0) hB2) h345_0, mul_pos (mul_pos (h345_2) hs1) ht1, mul_pos
              (mul_pos (h345_2) N.ht) hAh, mul_pos (mul_pos (h345_2) N.hs) he2, mul_pos
              (mul_pos (h345_0) he2) hh21, mul_pos (mul_pos (hA0) h345_2) N.hs, mul_pos
              (mul_pos (hB2) h345_0) N.ht, mul_pos (mul_pos (h345_2) N.ht) he0, mul_pos
              (mul_pos (h345_2) N.hs) hst, mul_pos (mul_pos (h345_2) ha2) hh0g, mul_pos
              (mul_pos (N.hh2) h345_2) hAh, mul_pos (mul_pos (N.hh0) h345_2) hb0, mul_pos
              (mul_pos (h345_2) N.ht) N.ht, mul_pos (mul_pos (N.hh0) h345_0) he2, mul_pos
              (mul_pos (N.hh2) h345_2) hh0g, mul_pos (mul_pos (h345_2) h345_2) ha2, mul_pos
              (mul_pos (h345_2) h345_2) hst, mul_pos (mul_pos (h345_0) h345_2) he0, mul_pos
              (mul_pos (h345_0) h345_2) hs1, mul_pos (mul_pos (N.hh0) h345_2) hbh2, mul_pos
              (mul_pos (hA0) h345_2) h345_2, mul_pos (mul_pos (h345_2) h345_2) hbh2, mul_pos
              (mul_pos (h345_0) h345_2) hbh2, mul_pos (mul_pos (h345_2) h345_2) h345_2])
    (by simp only [NF29.vZ]; nf29_vec N)
  have eW1 : det3 (x 3 - x 0) (x 1 - x 3) (x 2 - x 5) = (N.a0 * N.b2 - N.a2 * N.b0 - N.a0) * det3
      N.E₁ N.E₂ N.E₃ := by
    nf29_simp N; simp only [det3c]; ring
  have pW1 : 0 < N.a0 * N.b2 - N.a2 * N.b0 - N.a0 :=
      (by linarith [N.hDG5, mul_pos (ha2) hh0g, mul_pos (N.hh2) hA0])
  have eZ1 : det3 N.vZ (x 1 - x 3) (x 2 - x 5) =
      (-N.a0 * N.b2 * N.h2 - N.a0 * N.b2 ^ 2 + N.a2 * N.b0 * N.b2 + N.a2 * N.b2 * N.h0 + N.a0 * N.a2
        + 2 * N.a0 * N.b2 + N.a0 * N.h2 - N.a2 * N.b2 - N.a0) * det3 N.E₁ N.E₂ N.E₃ := by
    simp only [NF29.vZ]; nf29_simp N; simp only [det3c]; ring
  have pZ1 : 0 < -N.a0 * N.b2 * N.h2 - N.a0 * N.b2 ^ 2 + N.a2 * N.b0 * N.b2 + N.a2 * N.b2 * N.h0 +
      N.a0 * N.a2 + 2 * N.a0 * N.b2 + N.a0 * N.h2 - N.a2 * N.b2 - N.a0 :=
      (by
        linarith [mul_pos (hB2) N.hDG5, mul_pos (hB2) h345_2, mul_pos (N.d234) hb0, mul_pos (N.hDG4)
            hh21, mul_pos (N.hh0) N.d234, mul_pos (h345_2) N.d035, mul_pos (mul_pos (hB2) hst) hs1,
            mul_pos (mul_pos (hB2) hst) hst, mul_pos (mul_pos (hB2) hst) he0, mul_pos
            (mul_pos (hB2) hst) ht1, mul_pos (mul_pos (h345_0) he2) he2, mul_pos
            (mul_pos (h345_2) ha2) hAh, mul_pos (mul_pos (h345_2) he0) ht1, mul_pos
            (mul_pos (hB2) hB2) h345_0, mul_pos (mul_pos (h345_2) N.hs) hAh, mul_pos
            (mul_pos (h345_2) ha2) hh0g, mul_pos (mul_pos (hA0) h345_2) N.ht, mul_pos
            (mul_pos (N.hh2) h345_2) he0, mul_pos (mul_pos (N.hh2) h345_2) hAh, mul_pos
            (mul_pos (N.hh0) h345_2) ht1, mul_pos (mul_pos (h345_2) N.ht) hh0g, mul_pos
            (mul_pos (h345_0) h345_2) ha2, mul_pos (mul_pos (N.hh0) h345_2) N.hs, mul_pos
            (mul_pos (h345_2) h345_2) hAh, mul_pos (mul_pos (h345_0) h345_2) hs1, mul_pos
            (mul_pos (h345_0) h345_2) hbh2, mul_pos (mul_pos (h345_2) h345_2) hh0g])
  have eW2 : det3 (x 3 - x 0) (x 1 - x 3) (x 0 - x 4) = (N.b0) * det3 N.E₁ N.E₂ N.E₃ := by
    nf29_simp N; simp only [det3c]; ring
  have pW2 : 0 < N.b0 := (by linarith [hb0])
  have eZ2 : det3 N.vZ (x 1 - x 3) (x 0 - x 4) =
      (-N.a0 * N.a2 * N.b0 - N.a0 * N.b0 * N.h2 + N.a0 * N.b2 * N.h0 + N.a0 ^ 2 * N.b2 + N.a0 * N.b0
        - 2 * N.a0 * N.b2 - N.b0 * N.b2 - N.b2 * N.h0 + N.b2) * det3 N.E₁ N.E₂ N.E₃ := by
    simp only [NF29.vZ]; nf29_simp N; simp only [det3c]; ring
  have pZ2 : -N.a0 * N.a2 * N.b0 - N.a0 * N.b0 * N.h2 + N.a0 * N.b2 * N.h0 + N.a0 ^ 2 * N.b2 + N.a0
      * N.b0 - 2 * N.a0 * N.b2 - N.b0 * N.b2 - N.b2 * N.h0 + N.b2 < 0 :=
      (by
        linarith [mul_pos (he2) hc2, mul_pos (N.hDD) hst, mul_pos (h345_2) he2, mul_pos (N.d234)
            he2, mul_pos (N.d234) hAh, mul_pos (N.hDG4) hb0, mul_pos (N.hDG4) hh21, mul_pos (N.d234)
            hh0g, mul_pos (N.d234) hh21, mul_pos (N.d234) hbh2, mul_pos (h345_2) N.hDD, mul_pos
            (N.hh0) N.hDG4, mul_pos (h345_0) h345_2, mul_pos (h345_2) N.d035, mul_pos
            (mul_pos (hB2) hst) he0, mul_pos (mul_pos (hst) hb0) hh21, mul_pos
            (mul_pos (h345_2) he0) hAh, mul_pos (mul_pos (h345_0) he0) he2, mul_pos
            (mul_pos (h345_2) hb0) ht1, mul_pos (mul_pos (hB2) h345_0) hb0, mul_pos
            (mul_pos (h345_2) ha2) hAh, mul_pos (mul_pos (h345_2) hAh) hAh, mul_pos
            (mul_pos (hB2) hB2) h345_0, mul_pos (mul_pos (hA0) h345_2) hs1, mul_pos
            (mul_pos (hB2) h345_0) ha2, mul_pos (mul_pos (h345_2) N.hs) hAh, mul_pos
            (mul_pos (hA0) h345_2) hbh2, mul_pos (mul_pos (h345_2) hbh2) hAh, mul_pos
            (mul_pos (h345_2) hst) hbh2, mul_pos (mul_pos (hB2) h345_0) hbh2, mul_pos
            (mul_pos (h345_2) N.hs) hh21, mul_pos (mul_pos (N.hh2) h345_2) hAh, mul_pos
            (mul_pos (h345_2) N.hs) hh0g, mul_pos (mul_pos (N.hh0) h345_2) ht1, mul_pos
            (mul_pos (N.hh0) h345_2) ha2, mul_pos (mul_pos (h345_2) hh0g) hh21, mul_pos
            (mul_pos (h345_2) N.ht) hh21, mul_pos (mul_pos (h345_0) h345_0) he2, mul_pos
            (mul_pos (hB2) h345_0) h345_0, mul_pos (mul_pos (h345_2) h345_2) hs1, mul_pos
            (mul_pos (h345_2) h345_2) hAh, mul_pos (mul_pos (h345_2) h345_2) hst, mul_pos
            (mul_pos (h345_0) h345_2) h345_2])
  have m2u : SegMeet (x 3) (x 1) (x 4) (x 0) (x 3 - x 0) :=
    ⟨0, 1, -1, le_rfl, zero_le_one, zero_le_one, le_rfl, by module⟩
  by_cases hW : DepthSep (x 3) (x 1) (x 5) (x 2) (x 3 - x 0)
  · by_cases hZ : DepthSep (x 3) (x 1) (x 0) (x 4) N.vZ
    · exfalso
      exact not_both_depthSep hW (depthSep_swap₂ hZ) m1u m1v m2v m2u
        (det4_neg N.hD eW1 eZ1 eW2 eZ2
          (mul_neg_of_pos_of_neg (mul_pos pW1 pZ1) (mul_neg_of_pos_of_neg pW2 pZ2)))
    · exact NF29.isRupert_k4_Z N ha2 hb0 he0 he2 hs1 ht1 hbh2 hh0g hAh hh21 hc2
          (quad_unimodal hZ hzZ).isRobustUnimodal hndZ
  · exact NF29.isRupert_k4_W N ha2 hb0 he0 he2 hs1 ht1 hbh2 hh0g hAh hh21 hc2
        (quad_unimodal hW hzW).isRobustUnimodal hndW

/-- **Lemmas 21.7 and 21.8 (K4.1, K4.2)** on `K4a ∩ R_G`: if `O` is of class K4a (`a2, b0 > 0`,
`V < 0`) and none of its E-good `G` edges `2 → 4`, `4 → 1`, `5 → 1`, `1 → 5` is a quad edge
(Lemma 21.3), then, off `e0 = 0` and `e2 = 0`: `e0, e2 > 0`, `s, t < 1`, `b2 + h2 > 0` and
`G5 ≥ 0`. -/
theorem NF29.k4_facts (N : NF29 x) (ha2 : 0 < N.a2) (hb0 : 0 < N.b0)
    (hV : N.h0 * (1 - N.a2 - N.b2) - N.h2 * (1 - N.a0 - N.b0) < 0)
    (n24 : ¬ (N.h0 < N.h0 * N.a2 - N.h2 * N.a0 ∧
      1 - N.a0 - N.b0 - N.h0 < -((N.b0 - 1 + N.h0) * N.a2 - N.a0 * N.b2 + N.a0 * (1 - N.h2))))
    (n41 : ¬ (0 < N.b0 * (1 - N.h2) - N.b2 * (1 - N.h0) ∧ N.b0 + N.h0 < 1))
    (n51 : ¬ (0 < N.a2 * (1 - N.h0) - N.a0 * (1 - N.h2) ∧ N.a2 + N.h2 < 1))
    (n15 : ¬ (N.a2 * (1 - N.h0) - N.a0 * (1 - N.h2) < 0 ∧ 1 < N.a2 + N.h2))
    (sp0 : N.b0 + N.h0 ≠ 1) (sp2 : N.a2 + N.h2 ≠ 1) :
    0 < N.b0 + N.h0 - 1 ∧ 0 < N.a2 + N.h2 - 1 ∧ 0 < -N.s + 1 ∧ 0 < -N.t + 1 ∧
      0 < N.b2 + N.h2 ∧ 0 ≤ N.a2 * (1 - N.h0) - N.a0 * (1 - N.h2) := by
  have hA0 : 0 < -N.a0 := by linarith [N.ha0]
  have hB2 : 0 < -N.b2 := by linarith [N.hb2]
  have h345_0 : 0 < 1 - N.a0 - N.b0 - N.h0 := by linarith [N.t345_0]
  have h345_2 : 0 < 1 - N.a2 - N.b2 - N.h2 := by linarith [N.t345_2]
  -- `e2 > 0`: else `5 → 1` is a quad edge
  have he2 : 0 < N.a2 + N.h2 - 1 := by
    rcases lt_or_gt_of_ne sp2 with h | h
    · exfalso
      refine n51 ⟨?_, h⟩
      nlinarith [mul_pos ha2 (show 0 < 1 - N.a0 - N.h0 by linarith),
        mul_pos hA0 (show 0 < 1 - N.h2 - N.a2 by linarith)]
    · linarith
  -- `e0 > 0`: else `4 → 1` is a quad edge
  have he0 : 0 < N.b0 + N.h0 - 1 := by
    rcases lt_or_gt_of_ne sp0 with h | h
    · exfalso
      refine n41 ⟨?_, h⟩
      nlinarith [mul_pos hb0 (show 0 < 1 - N.b2 - N.h2 by linarith),
        mul_pos hB2 (show 0 < 1 - N.h0 - N.b0 by linarith)]
    · linarith
  refine ⟨he0, he2, ?_, ?_, ?_, ?_⟩
  · by_contra hc; push Not at hc
    nlinarith [N.d234, mul_pos he2 N.ht, mul_nonneg hB2.le (show 0 ≤ N.s - 1 by linarith)]
  · by_contra hc; push Not at hc
    nlinarith [N.d035, mul_pos he0 N.hs, mul_nonneg hA0.le (show 0 ≤ N.t - 1 by linarith)]
  · -- Lemma 21.8 (a)
    by_contra hc; push Not at hc
    have hBh : 0 ≤ -N.b2 - N.h2 := by linarith
    rcases lt_trichotomy N.a2 1 with ha1 | ha1 | ha1
    · refine n24 ⟨?_, ?_⟩
      · by_contra hc1; push Not at hc1
        nlinarith [mul_pos N.hh2 he0, mul_nonneg N.hh0.le hBh]
      · nlinarith [mul_pos he0 (show 0 < 1 - N.a2 by linarith), mul_nonneg hA0.le hBh]
    · refine n24 ⟨?_, ?_⟩
      · rw [ha1]; nlinarith [mul_pos N.hh2 hA0]
      · rw [ha1]; nlinarith [mul_pos hA0 (show 0 < -N.b2 - N.h2 by linarith)]
    · refine n24 ⟨?_, ?_⟩
      · nlinarith [mul_pos N.hh0 (show 0 < N.a2 - 1 by linarith), mul_pos N.hh2 hA0]
      · nlinarith [mul_pos hA0 (show 0 < -N.b2 - N.h2 - (N.a2 - 1) by linarith),
          mul_pos (show 0 < N.a2 - 1 by linarith) h345_0]
  · -- Lemma 21.8 (b)
    by_contra hc; push Not at hc
    exact n15 ⟨hc, by linarith⟩

/-- The special positions of class K4a used by Theorem 21.11 (§21.5) and the genericity of its
named tests: distinct depths on the rims and no horizontal double normal at the views (`V`, `Y`
of tier (A); their `σ`-images `V′ = 1456/234`, `Y′ = 234/346-3` of tier (B1); `W`, `Z` of (B2)). -/
structure K4Gen (N : NF29 x) : Prop where
  e0 : N.b0 + N.h0 ≠ 1
  e2 : N.a2 + N.h2 ≠ 1
  h0 : N.h0 ≠ 1
  ah : N.a0 + N.h0 ≠ 0
  c2 : -((N.b0 - 1 + N.h0) * N.a2 - N.a0 * N.b2 + N.a0 * (1 - N.h2)) ≠ 1 - N.a0 - N.b0 - N.h0
  zV : [⟪x 5, N.vV⟫, ⟪x 1, N.vV⟫, ⟪x 2, N.vV⟫, ⟪x 3, N.vV⟫].Nodup
  zY : [⟪x 5, x 5 - x 3⟫, ⟪x 0, x 5 - x 3⟫, ⟪x 1, x 5 - x 3⟫, ⟪x 4, x 5 - x 3⟫,
    ⟪x 6, x 5 - x 3⟫].Nodup
  zV' : [⟪x 4, N.sigma.vV⟫, ⟪x 1, N.sigma.vV⟫, ⟪x 0, N.sigma.vV⟫, ⟪x 3, N.sigma.vV⟫].Nodup
  zY' : [⟪x 4, x 4 - x 3⟫, ⟪x 2, x 4 - x 3⟫, ⟪x 1, x 4 - x 3⟫, ⟪x 5, x 4 - x 3⟫,
    ⟪x 6, x 4 - x 3⟫].Nodup
  zW : [⟪x 3, x 3 - x 0⟫, ⟪x 5, x 3 - x 0⟫, ⟪x 1, x 3 - x 0⟫, ⟪x 2, x 3 - x 0⟫].Nodup
  zZ : [⟪x 3, N.vZ⟫, ⟪x 0, N.vZ⟫, ⟪x 1, N.vZ⟫, ⟪x 4, N.vZ⟫].Nodup
  ndV : NoHDNAt (univ.image x) N.vV
  ndY : NoHDNAt ((univ.image x).erase (x 3)) (x 5 - x 3)
  ndV' : NoHDNAt (univ.image x) N.sigma.vV
  ndY' : NoHDNAt ((univ.image x).erase (x 3)) (x 4 - x 3)
  ndW : NoHDNAt ((univ.image x).erase (x 0)) (x 3 - x 0)
  ndZ : NoHDNAt (univ.image x) N.vZ

/-- **Theorem 21.11 (K4 is covered), class K4a.**  Let `K` be of type 29 in normal coordinates
(`NF29`) with `O = K − 6` of class K4a (`a2 > 0`, `b0 > 0`, `V < 0`) in `R_G`: none of the
E-good `G` edges `2 → 4`, `4 → 1`, `5 → 1`, `1 → 5` is a quad edge (Lemma 21.3; `0 → 5` is not
needed).  Off the special positions and with the genericity of the named tests (`K4Gen`), `K` is
Rupert: (A) `h0 < 1`, F35 (`V`, `Y`); (B1) `h0 > 1 > h0 + a0`, F234 (`σ` of (A)); (B2) `h0 > 1`,
`h0 + a0 < 0`, F35′ (`W`, `Z`). -/
theorem NF29.isRupert_K4a (N : NF29 x) (ha2 : 0 < N.a2) (hb0 : 0 < N.b0)
    (hV : N.h0 * (1 - N.a2 - N.b2) - N.h2 * (1 - N.a0 - N.b0) < 0)
    (n24 : ¬ (N.h0 < N.h0 * N.a2 - N.h2 * N.a0 ∧
      1 - N.a0 - N.b0 - N.h0 < -((N.b0 - 1 + N.h0) * N.a2 - N.a0 * N.b2 + N.a0 * (1 - N.h2))))
    (n41 : ¬ (0 < N.b0 * (1 - N.h2) - N.b2 * (1 - N.h0) ∧ N.b0 + N.h0 < 1))
    (n51 : ¬ (0 < N.a2 * (1 - N.h0) - N.a0 * (1 - N.h2) ∧ N.a2 + N.h2 < 1))
    (n15 : ¬ (N.a2 * (1 - N.h0) - N.a0 * (1 - N.h2) < 0 ∧ 1 < N.a2 + N.h2))
    (G : K4Gen N) : IsRupert (univ.image x) := by
  obtain ⟨he0, he2, hs1, ht1, hbh2, hG5⟩ := N.k4_facts ha2 hb0 hV n24 n41 n51 n15 G.e0 G.e2
  have hA0 : 0 < -N.a0 := by linarith [N.ha0]
  rcases lt_or_gt_of_ne G.h0 with h0 | h0
  · -- (A)
    have hc : 0 < N.a0 * N.b2 - N.a2 * N.b0 - N.a2 * N.h0 + N.a2 := by
      nlinarith [N.hDD, mul_pos ha2 (show 0 < 1 - N.h0 by linarith)]
    exact N.isRupert_k4_A ha2 he0 hbh2 hs1 ht1 (by linarith) hc G.zV G.zY G.ndV G.ndY
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
      exact N.isRupert_k4_B2 ha2 hb0 he0 he2 hs1 ht1 hbh2 (by linarith) (by linarith) hh21 hc2
        G.zW G.zZ G.ndW G.ndZ
    · -- (B1): `σ` of (A)
      have hc' : 0 < N.b2 * N.a0 - N.b0 * N.a2 - N.b0 * N.h2 + N.b0 := by
        nlinarith [N.hDD, mul_pos hb0 hh21]
      have h := NF29.isRupert_k4_A N.sigma hb0 he2 (by show 0 < N.a0 + N.h0; linarith) ht1 hs1
        hh21 hc' G.zV' G.zY' (by rw [image_sigma29]; exact G.ndV')
        (by rw [image_sigma29]; exact G.ndY')
      rwa [image_sigma29] at h

/-- **Theorem 21.11, class K4b** (`σ` of K4a): `a2 > 0`, `b0 > 0`, `V > 0`, and none of the E-good
`G` edges `0 → 5`, `5 → 1`, `4 → 1`, `1 → 4` is a quad edge (Lemma 21.3).  With the special
positions and genericity of the `σ`-image (`K4Gen N.sigma`), `K` is Rupert. -/
theorem NF29.isRupert_K4b (N : NF29 x) (ha2 : 0 < N.a2) (hb0 : 0 < N.b0)
    (hV : 0 < N.h0 * (1 - N.a2 - N.b2) - N.h2 * (1 - N.a0 - N.b0))
    (n05 : ¬ (N.h2 < N.h2 * N.b0 - N.h0 * N.b2 ∧
      1 - N.h2 - N.a2 - N.b2 < N.a0 * N.b2 + (1 - N.h2 - N.a2) * N.b0 - N.b2 * (1 - N.h0)))
    (n41 : ¬ (0 < N.b0 * (1 - N.h2) - N.b2 * (1 - N.h0) ∧ N.b0 + N.h0 < 1))
    (n51 : ¬ (0 < N.a2 * (1 - N.h0) - N.a0 * (1 - N.h2) ∧ N.a2 + N.h2 < 1))
    (n14 : ¬ (N.b0 * (1 - N.h2) - N.b2 * (1 - N.h0) < 0 ∧ 1 < N.b0 + N.h0))
    (G : K4Gen N.sigma) : IsRupert (univ.image x) := by
  have h := NF29.isRupert_K4a N.sigma hb0 ha2 (by simp only [NF29.sigma]; linarith)
    (by intro h; simp only [NF29.sigma] at h; exact n05 ⟨by linarith [h.1], by linarith [h.2]⟩)
    (by intro h; simp only [NF29.sigma] at h; exact n51 ⟨by linarith [h.1], by linarith [h.2]⟩)
    (by intro h; simp only [NF29.sigma] at h; exact n41 ⟨by linarith [h.1], by linarith [h.2]⟩)
    (by intro h; simp only [NF29.sigma] at h; exact n14 ⟨by linarith [h.1], by linarith [h.2]⟩) G
  rwa [image_sigma29] at h

end Minimality

end
