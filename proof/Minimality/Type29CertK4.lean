module

public import Minimality.Type29CertTests
public import Minimality.Type29CertTie

@[expose] public section

/-!
# Type 29, class K4a: the pairs as certificates (`FEWER-FACES-PROOFS.md` §28, §18.4, §21.9–21.11)

* `k4_Y_core_weak`, `NF29.k4_Y_view`: Lemma 21.9 (2), (3) for `Y` (`k4_Y_core`) with the weak
  `ψ(d) ≥ 0`, for the depths along an arbitrary view `w` near `5 − 3` (the cone facts are linear
  identities of the depths).
* `NF29.cert_k4_A` (tier (A), `F35`): `V = 035/1456` (rim `(5, 1, 2, 3)`) or `Y = 035/356-3` (rim
  `(5, 0, 1, 4, 6)`) as a `Cert29`, with at most one tie at each view and none at one of them.
  `V` failing means `{5, 2}` weakly above `{1, 3}` (`not_weakSep_of_meet`, the crossing has
  `λ < 0`), so `ψ ≥ 0`; `ψ > 0` makes `Y` robustly unimodal by perturbing the view
  (`robust_of_view_nhds`), `ψ = 0` is a tie of `V`, so `Y` has none.
* `NF29.cert_k4_B2` (tier (B2), `F35'`): `W` or `Z` (`shared_core`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

variable {x : Fin 7 → ℝ³}

/-- `k4_Y_core` with the weak `ψ ≥ 0`. -/
theorem k4_Y_core_weak {A0 e0 h0 s t p1 p2 q z0 z1 z4 z5 z6 : ℝ} (hA0 : 0 < A0) (he0 : 0 < e0)
    (hs : 0 < s) (ht : 0 < t) (hst : 0 < s + t - 1) (ht1 : 0 < 1 - t) (hs1 : 0 < 1 - s)
    (hd035 : 0 < A0 * (1 - t) - e0 * s) (hh0 : 0 < h0) (hq : 0 < q) (h345_0 : 0 < A0 - e0)
    (hpsi : 0 ≤ A0 * p1 - e0 * p2) (e4 : z4 = z1 + p1) (e5 : z5 = z1 + p2)
    (e6 : z6 = z1 + s * p1 + t * p2) (e0' : z0 = z1 - A0 * p1 + (e0 + 1) * p2 - h0 * q)
    (hinj : Function.Injective (quint z5 z0 z1 z4 z6)) :
    IsCyclicUnimodal (quint z5 z0 z1 z4 z6) := by
  subst e4 e5 e6 e0'
  refine quint_unimodal_of hinj ?_ ?_ ?_ ?_ ?_
  · intro i1 i2 i3 i4; linarith [mul_pos (mul_pos (he0) hs) (sub_pos.mpr i1), mul_pos
          (mul_pos (hs) hd035) (sub_pos.mpr i4), mul_nonneg ((mul_pos (hst) ht1)).le hpsi,
              mul_nonneg ((mul_pos (ht1) ht1)).le hpsi]
  · intro i1 i2 i3 i4; linarith [mul_pos (hd035) (sub_pos.mpr i4), mul_pos (mul_pos (hA0) hs1)
          (sub_pos.mpr i1), mul_pos (mul_pos (he0) hst) (sub_pos.mpr i1), mul_pos
          (mul_pos (he0) hst) (sub_pos.mpr i3), mul_pos (mul_pos (he0) ht1) (sub_pos.mpr i4),
          mul_pos (mul_pos (hst) h345_0) (sub_pos.mpr i1),
              mul_nonneg (mul_nonneg ((hst)).le hpsi) (hs1).le,
                  mul_nonneg ((mul_pos (hst) hst)).le hpsi,
                      mul_nonneg ((mul_pos (hst) ht1)).le hpsi]
  · intro i1 i2 i3 i4; linarith [mul_pos (mul_pos (hA0) hst) (sub_pos.mpr i3), mul_pos
          (mul_pos (hd035) hs1) (sub_pos.mpr i3), mul_pos (mul_pos (he0) hst) (sub_pos.mpr i4),
          mul_pos (mul_pos (he0) ht1) (sub_pos.mpr i4),
              mul_nonneg (mul_nonneg (hpsi) (hs1).le) (hs1).le, mul_pos
          (mul_pos (hs) hs1) (sub_pos.mpr i1), mul_pos (mul_pos (hs) ht) (sub_pos.mpr i1), mul_pos
          (mul_pos (hs1) hs1) (sub_pos.mpr i1), mul_nonneg (mul_nonneg ((hst)).le hpsi) (hs1).le,
              mul_pos
          (mul_pos (hst) ht1) (sub_pos.mpr i1), mul_pos (mul_pos (ht) hh0) hq, mul_pos
          (mul_pos (ht) ht) (sub_pos.mpr i1)]
  · intro i1 i2 i3 i4; linarith [mul_pos (hd035) (sub_pos.mpr i1), mul_nonneg ((hd035)).le hpsi,
      mul_pos
          (mul_pos (h345_0) hs1) (sub_pos.mpr i1), mul_nonneg ((mul_pos (hA0) hst)).le hpsi, mul_pos
          (mul_pos (he0) hst) (sub_pos.mpr i1), mul_pos (mul_pos (hh0) hq) h345_0,
              mul_nonneg (mul_nonneg (hpsi) (h345_0).le) (hs1).le,
                  mul_pos (mul_pos (hst) h345_0) (sub_pos.mpr i1)]
  · intro i1 i2 i3 i4; linarith [mul_pos (mul_pos (h345_0) hs1) (sub_pos.mpr i2), mul_pos
          (mul_pos (h345_0) hs1) (sub_pos.mpr i4), mul_pos (mul_pos (hA0) ht1) (sub_pos.mpr i3),
          mul_pos (mul_pos (he0) hs1) (sub_pos.mpr i3), mul_pos (mul_pos (he0) hs1)
          (sub_pos.mpr i4), mul_pos (mul_pos (he0) hst) (sub_pos.mpr i2), mul_pos
          (mul_pos (he0) hst) (sub_pos.mpr i3), mul_nonneg ((mul_pos (hs) ht)).le hpsi, mul_pos
          (mul_pos (hst) h345_0) (sub_pos.mpr i2), mul_pos (mul_pos (hst) h345_0) (sub_pos.mpr i4),
          mul_nonneg ((mul_pos (hst) ht1)).le hpsi, mul_nonneg ((mul_pos (ht) ht)).le hpsi]


/-- **Lemma 21.9 (2), (3) for the depths along any view `w`**: if `⟪5 − 3, w⟫ > 0` and
`ψ = ⟪vV, w⟫ ≥ 0`, an injective depth sequence of `Y`'s rim `(5, 0, 1, 4, 6)` is unimodal. -/
theorem NF29.k4_Y_view (N : NF29 x) (he0 : 0 < N.b0 + N.h0 - 1) (hs1 : 0 < -N.s + 1)
    (ht1 : 0 < -N.t + 1) (w : ℝ³) (hq : 0 < ⟪x 5 - x 3, w⟫) (hψ : 0 ≤ ⟪N.vV, w⟫)
    (hinj : Function.Injective (quint ⟪x 5, w⟫ ⟪x 0, w⟫ ⟪x 1, w⟫ ⟪x 4, w⟫ ⟪x 6, w⟫)) :
    IsCyclicUnimodal (quint ⟪x 5, w⟫ ⟪x 0, w⟫ ⟪x 1, w⟫ ⟪x 4, w⟫ ⟪x 6, w⟫) := by
  have hA0 : 0 < -N.a0 := by linarith [N.ha0]
  have v6 : x 6 - x 1 = N.s • (x 4 - x 1) + N.t • (x 5 - x 1) := by nf29_vec N
  have v0 : x 0 - x 1 = N.a0 • (x 4 - x 1) + (N.b0 + N.h0) • (x 5 - x 1) - N.h0 • (x 5 - x 3) := by
    nf29_vec N
  have vd : N.vV = (-N.a0) • (x 4 - x 1) + (-(N.b0 + N.h0 - 1)) • (x 5 - x 1) := by
    simp only [NF29.vV]; nf29_vec N
  have i6 := congrArg (fun v => ⟪v, w⟫) v6
  have i0 := congrArg (fun v => ⟪v, w⟫) v0
  simp only [inner_sub_left, inner_add_left, real_inner_smul_left] at i6 i0
  have hq' : ⟪x 5 - x 3, w⟫ = ⟪x 5, w⟫ - ⟪x 3, w⟫ := inner_sub_left _ _ _
  have ed : ⟪N.vV, w⟫ = -N.a0 * (⟪x 4, w⟫ - ⟪x 1, w⟫) -
      (N.b0 + N.h0 - 1) * (⟪x 5, w⟫ - ⟪x 1, w⟫) := by
    rw [vd]; simp only [inner_add_left, real_inner_smul_left, inner_sub_left]; ring
  exact (k4_Y_core_weak (A0 := -N.a0) (e0 := N.b0 + N.h0 - 1) (h0 := N.h0) (s := N.s) (t := N.t)
      (p1 := ⟪x 4, w⟫ - ⟪x 1, w⟫) (p2 := ⟪x 5, w⟫ - ⟪x 1, w⟫) (q := ⟪x 5 - x 3, w⟫)
      (z1 := ⟪x 1, w⟫) (z0 := ⟪x 0, w⟫) (z4 := ⟪x 4, w⟫) (z5 := ⟪x 5, w⟫) (z6 := ⟪x 6, w⟫)
      hA0 he0 N.hs N.ht (by linarith [N.hst]) (by linarith) (by linarith) (by linarith [N.d035])
          N.hh0 hq
      (by linarith [N.t345_0]) (by rw [← ed]; exact hψ) (by ring) (by ring) (by linarith)
      (by rw [hq']; linarith) hinj)

theorem NF29.certV29 (N : NF29 x) (he0 : 0 < N.b0 + N.h0 - 1) (hh01 : 0 < -N.h0 + 1)
    (hc : 0 < N.a0 * N.b2 - N.a2 * N.b0 - N.a2 * N.h0 + N.a2)
    (hz : IsRobustUnimodal (quad ⟪x 5, N.vV⟫ ⟪x 1, N.vV⟫ ⟪x 2, N.vV⟫ ⟪x 3, N.vV⟫)) :
    CertV29 x := by
  obtain ⟨σ, hσ, h, -⟩ := N.rimThen_k4_V he0 hh01 hc hz
  obtain ⟨c, hc', e⟩ := N.namedAt_vV hσ
  exact ⟨c, hc', by rw [← e]; exact h⟩

theorem NF29.certY29 (N : NF29 x) (ha2 : 0 < N.a2) (he0 : 0 < N.b0 + N.h0 - 1)
    (hs1 : 0 < -N.s + 1) (hbh2 : 0 < N.b2 + N.h2)
    (hz : IsRobustUnimodal (quint ⟪x 5, (x 5 - x 3)⟫ ⟪x 0, (x 5 - x 3)⟫ ⟪x 1, (x 5 - x 3)⟫
      ⟪x 4, (x 5 - x 3)⟫ ⟪x 6, (x 5 - x 3)⟫)) : CertY29 x := by
  obtain ⟨σ, hσ, h, -⟩ := N.rimThen_k4_Y ha2 he0 hs1 hbh2 hz
  obtain ⟨c, hc', e⟩ := namedAt_seg (x := x) 3 5 hσ
  exact ⟨c, hc', by rw [← e]; exact h⟩

/-- **Lemma 21.9 and Theorem 21.11 (A), certificate form** (`F35`,
tier (A)); the conclusion is `CertV29 x ∨ CertY29 x`, so that
`Cert29.ofSigmaA` applies to `x ∘ σ`.  `V` fails only with
`{5, 2}` weakly above `{1, 3}`, hence `ψ = ⟪vV, 5 − 3⟫ ≥ 0`; then `Y` is robustly unimodal:
for `ψ > 0` by perturbing the view, for `ψ = 0` (a tie of `V`) because `Y` has no tie. -/
theorem NF29.cert_k4_A (N : NF29 x) (ha2 : 0 < N.a2) (he0 : 0 < N.b0 + N.h0 - 1)
    (hbh2 : 0 < N.b2 + N.h2)
    (hs1 : 0 < -N.s + 1) (ht1 : 0 < -N.t + 1) (hh01 : 0 < -N.h0 + 1)
    (hc : 0 < N.a0 * N.b2 - N.a2 * N.b0 - N.a2 * N.h0 + N.a2)
    (oV : OneTieAt (univ.image x) (view29 x (.inr 2)))
    (oY : OneTieAt (univ.image x) (view29 x (.inl (3, 5))))
    (hno : NoTieAt (univ.image x) (view29 x (.inr 2)) ∨
      NoTieAt (univ.image x) (view29 x (.inl (3, 5)))) : CertV29 x ∨ CertY29 x := by
  have oV' : OneTieAt (univ.image x) N.vV := oV.of_eq_smul N.vV_eq N.hDni
  by_cases hRV : IsRobustUnimodal (quad ⟪x 5, N.vV⟫ ⟪x 1, N.vV⟫ ⟪x 2, N.vV⟫ ⟪x 3, N.vV⟫)
  · exact Or.inl (N.certV29 he0 hh01 hc hRV)
  have W := weakSep_of_not_robust (oV'.oneTie4 (img29 5) (img29 1) (img29 2) (img29 3)
    (List.nodup4_img N.inj (by decide : [(5 : Fin 7), 1, 2, 3].Nodup))) hRV
  have hA0 : 0 < -N.a0 := by linarith [N.ha0]
  have hK : 0 < -N.a0 + N.a0 * N.b2 - N.a2 * (N.b0 + N.h0 - 1) := by linarith
  have hm := meet_of_smul (d₀ := x 5) (d₁ := x 2) (e₀ := x 1) (e₁ := x 3) (v := N.vV)
    (K := -N.a0 + N.a0 * N.b2 - N.a2 * (N.b0 + N.h0 - 1)) (s := -N.a0) (t := -N.a0 * N.h2)
    (l := -N.a2) hK.ne' (by simp only [NF29.vV]; nf29_vec N)
  have hA0h2 : 0 < -N.a0 * N.h2 := by
    nlinarith [mul_pos N.hh2 he0, mul_pos N.hh0 (show
      0 < 1 - N.a2 - N.b2 - N.h2 by linarith [N.t345_2])]
  have h35 : ⟪x 3, N.vV⟫ ≤ ⟪x 5, N.vV⟫ := by
    rcases W with h | h
    · exact le_trans (le_max_right _ _) (le_trans h (min_le_left _ _))
    · exfalso
      exact not_weakSep_of_meet (div_pos hA0 hK).le ((div_le_one hK).mpr (by linarith))
        (div_pos hA0h2 hK).le ((div_le_one hK).mpr (by linarith [N.hDG5])) hm
        (div_neg_of_neg_of_pos (by linarith) hK)
        (nfV_ne_zero N.hD (Or.inl (neg_pos.mpr N.ha0).ne'))
        (le_trans (le_max_left _ _) (le_trans h (min_le_left _ _)))
        (le_trans (le_max_left _ _) (le_trans h (min_le_right _ _)))
        (le_trans (le_max_right _ _) (le_trans h (min_le_left _ _)))
        (le_trans (le_max_right _ _) (le_trans h (min_le_right _ _)))
  have hψ : 0 ≤ ⟪N.vV, x 5 - x 3⟫ := by
    rw [inner_sub_right, real_inner_comm (x 5) N.vV, real_inner_comm (x 3) N.vV]
    linarith
  have hu : 0 < ⟪x 5 - x 3, x 5 - x 3⟫ :=
    real_inner_self_pos.mpr (sub_ne_zero.mpr (N.inj.ne (by decide)))
  have hne : ∀ {i j : Fin 7}, i ≠ j → x i ≠ x j := fun h => N.inj.ne h
  have hpts : ∀ i, (quint (x 5) (x 0) (x 1) (x 4) (x 6)) i ∈ univ.image x := by
    intro i; rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;> exact img29 _
  have hinjp : Function.Injective (quint (x 5) (x 0) (x 1) (x 4) (x 6)) :=
    quint_injective (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide))
      (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide))
      (hne (by decide))
  have hY : IsRobustUnimodal
      (quint ⟪x 5, x 5 - x 3⟫ ⟪x 0, x 5 - x 3⟫ ⟪x 1, x 5 - x 3⟫ ⟪x 4, x 5 - x 3⟫
        ⟪x 6, x 5 - x 3⟫) := by
    rcases hψ.lt_or_eq with hpos | hzero
    · have := robust_of_view_nhds (K := univ.image x) hpts hinjp (u := x 5 - x 3) oY
        (fun w => 0 < ⟪x 5 - x 3, w⟫ ∧ 0 < ⟪N.vV, w⟫) ?_ ?_
      · rwa [quint_inner] at this
      · have c1 : Continuous fun w : ℝ³ => ⟪x 5 - x 3, w⟫ := continuous_const.inner continuous_id
        have c2 : Continuous fun w : ℝ³ => ⟪N.vV, w⟫ := continuous_const.inner continuous_id
        exact ((c1.tendsto _).eventually_const_lt hu).and ((c2.tendsto _).eventually_const_lt hpos)
      · intro w hw hinj
        rw [quint_inner] at hinj ⊢
        exact N.k4_Y_view he0 hs1 ht1 w hw.1 hw.2.le hinj
    · -- `ψ = 0`: a tie of `V`, so no tie at `Y`
      have tie : ⟪x 5, N.vV⟫ = ⟪x 3, N.vV⟫ := by
        rw [inner_sub_right, real_inner_comm (x 5) N.vV, real_inner_comm (x 3) N.vV] at hzero
        linarith
      rcases hno with hnV | hnY
      · exact absurd tie (hnV.of_eq_smul N.vV_eq N.hDni _ (img29 5) _ (img29 3)
          (hne (by decide)))
      · have hnY' : NoTieAt (univ.image x) (x 5 - x 3) := hnY
        have d : ∀ {i j : Fin 7}, i ≠ j → ⟪x i, x 5 - x 3⟫ ≠ ⟪x j, x 5 - x 3⟫ :=
          fun h => hnY' _ (img29 _) _ (img29 _) (hne h)
        exact (N.k4_Y_view he0 hs1 ht1 (x 5 - x 3) hu hψ
          (quint_injective (d (by decide)) (d (by decide)) (d (by decide)) (d (by decide))
            (d (by decide)) (d (by decide)) (d (by decide)) (d (by decide)) (d (by decide))
            (d (by decide)))).isRobustUnimodal
  exact Or.inr (N.certY29 ha2 he0 hs1 hbh2 hY)


/-- **Lemma 21.10 (F35') and Theorem 21.11 (B2), certificate form**: `W = 023/035-0` or
`Z = 035/234` has a robustly unimodal rim (`shared_core`: the tests share the diagonal `[1, 3]`). -/
theorem NF29.cert_k4_B2 (N : NF29 x)
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
    (o1 : OneTieAt (univ.image x) (view29 x (.inl (0, 3))))
    (o2 : OneTieAt (univ.image x) (view29 x (.inr 6)))
    (hno : NoTieAt (univ.image x) (view29 x (.inl (0, 3))) ∨
      NoTieAt (univ.image x) (view29 x (.inr 6))) : Cert29 x := by
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
  have hS1 : det3 (x 5 - x 3) (x 1 - x 3) (x 2 - x 5) ≠ 0 :=
    segMeet_hS_of_smul (v := (x 3 - x 0))
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
    (ne_of_gt ha2)
    (by rw [eW1]; exact mul_ne_zero pW1.ne' N.hD)
  have hS2 : det3 (x 4 - x 3) (x 1 - x 3) (x 0 - x 4) ≠ 0 :=
    segMeet_hS_of_smul (v := N.vZ)
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
    (ne_of_gt hb0)
    (by rw [eZ2]; exact mul_ne_zero pZ2.ne N.hD)
  have o1' : OneTieAt (univ.image x) (x 3 - x 0) := o1
  have o2' : OneTieAt (univ.image x) N.vZ := o2.of_eq_smul N.vZ_eq N.hDi
  have hno' : NoTieAt (univ.image x) (x 3 - x 0) ∨ NoTieAt (univ.image x) N.vZ := by
    rcases hno with hnu | hnv
    · exact Or.inl hnu
    · exact Or.inr (hnv.of_eq_smul N.vZ_eq N.hDi)
  have hdet := det4_neg N.hD eW1 eZ1 eW2 eZ2
    (mul_neg_of_pos_of_neg (mul_pos pW1 pZ1) (mul_neg_of_pos_of_neg pW2 pZ2))
  rcases shared_core (img29 3) (img29 1) (img29 5) (img29 2) (img29 4) (img29 0)
    (List.nodup4_img N.inj (by decide : [(3 : Fin 7), 5, 1, 2].Nodup))
    (List.nodup4_img N.inj (by decide : [(3 : Fin 7), 0, 1, 4].Nodup))
    m1u m1v m2u m2v hS1 hS2 hdet o1' o2' hno' with hRW | hRZ
  · exact NF29.cert_k4_W N ha2 hb0 he0 he2 hs1 ht1 hbh2 hh0g hAh hh21 hc2 hRW
  · exact NF29.cert_k4_Z N ha2 hb0 he0 he2 hs1 ht1 hbh2 hh0g hAh hh21 hc2 hRZ

end Minimality

end
