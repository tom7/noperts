module

public import Minimality.CornerSlide
public import Minimality.Oct9Par
public import Minimality.BadViews
public import Minimality.SilS0XC
public import Minimality.EdgeViewLink
public import Minimality.Type24SAT.Facets24

@[expose] public section

/-!
# Corner Slide Lemma at a G-orthogonal degree-3 corner, any facet list

`csl_corner`: generic form of `csl29` (Type29KSAT/K1Corner) with the corner vertex as a parameter, built on the
Corner Slide Lemma; helpers `par_id`, `fac_zero`, `fac_neg`, `fac_le`, `edge_par`, `sign_tr` generalized.
`csl24`: type 24, corner 5 (edges to 2, 0, 3 pairwise orthogonal): the residual W of the A1 tie cover
(nopert229 out/bottleneck/p4/sat/WCORNER.md, TIECERT.md).
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21

/-!
# The Corner Slide Lemma at a G-orthogonal degree-3 corner, over any facet list

Generic form of `csl29` (Type29KSAT/K1Corner): corner vertex `v`, three pairwise orthogonal edges `v J`, `v M`,
`v K`, facets `tg ∋ v, J, M` (exactly), `te ∋ v, M, K` missing `J`, `tf ∋ v, J, K` missing `M`.  `csl24` is the
type-24 instance at corner 5 (Lemma W of `WCORNER.md`).
-/

namespace Minimality.CSLCorner

variable {n m : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}

theorem cross_ne_zero_of_orth {a b : ℝ³} (ha : a ≠ 0) (hb : b ≠ 0) (hab : ⟪a, b⟫ = 0) :
    cross a b ≠ 0 := by
  intro h
  have hb' := eq_smul_of_cross_eq_zero ha h
  have hba : ⟪b, a⟫ = 0 := by rw [real_inner_comm]; exact hab
  rw [hba, zero_div, zero_smul] at hb'
  exact hb hb'

theorem par_id {a b e N : ℝ³} (hc : cross a b ≠ 0) (he1 : ⟪e, a⟫ = 0) (he2 : ⟪e, b⟫ = 0)
    (hN1 : ⟪N, a⟫ = 0) (hN2 : ⟪N, b⟫ = 0) (y : ℝ³) :
    ⟪y, e⟫ * ⟪e, N⟫ = ⟪e, e⟫ * ⟪y, N⟫ := by
  obtain ⟨s, rfl⟩ := eq_smul_cross_of_perp hc he1 he2
  obtain ⟨t, rfl⟩ := eq_smul_cross_of_perp hc hN1 hN2
  simp only [real_inner_smul_left, real_inner_smul_right]; ring

theorem fac_zero (F : S0xFac m S x) {t : Fin m} {i j : Fin n} (hi : i ∈ S t)
    (hj : j ∈ S t) : ⟪F.N t, x i - x j⟫ = 0 := by
  rw [F.inner_sub, F.zero t i hi, F.zero t j hj]; ring

theorem fac_neg (F : S0xFac m S x) {t : Fin m} {i j : Fin n} (hi : i ∉ S t)
    (hj : j ∈ S t) : ⟪F.N t, x i - x j⟫ < 0 := by
  rw [F.inner_sub, F.zero t j hj]; have := F.neg t i hi; linarith

theorem fac_le (F : S0xFac m S x) {t : Fin m} (i : Fin n) {j : Fin n}
    (hj : j ∈ S t) : ⟪F.N t, x i - x j⟫ ≤ 0 := by
  rw [F.inner_sub, F.zero t j hj]; have := F.le t i; linarith

theorem sub_ne_of_ne (hx : Function.Injective x) {i j : Fin n} (h : i ≠ j) : x i - x j ≠ 0 :=
  sub_ne_zero.2 (fun e => h (hx e))

/-- Edge `x J - x v` parallel to the normal of a facet `t` through `v, M, K` missing `J`: signs transfer. -/
theorem edge_par (F : S0xFac m S x) (hx : Function.Injective x) (v J M K : Fin n) (t : Fin m)
    (hMv : M ≠ v) (hKv : K ≠ v)
    (hJK : ⟪x J - x v, x K - x v⟫ = 0) (hJM : ⟪x J - x v, x M - x v⟫ = 0)
    (hMK : ⟪x M - x v, x K - x v⟫ = 0)
    (hM : M ∈ S t) (hK : K ∈ S t) (hv : v ∈ S t) (hJ : J ∉ S t) :
    ⟪x J - x v, F.N t⟫ < 0 ∧
      ∀ y : ℝ³, ⟪y, x J - x v⟫ * ⟪x J - x v, F.N t⟫ = ⟪x J - x v, x J - x v⟫ * ⟪y, F.N t⟫ := by
  have hc := cross_ne_zero_of_orth (sub_ne_of_ne hx hMv) (sub_ne_of_ne hx hKv) hMK
  have hlt : ⟪x J - x v, F.N t⟫ < 0 := by rw [real_inner_comm]; exact fac_neg F hJ hv
  refine ⟨hlt, par_id hc hJM hJK ?_ ?_⟩
  · exact fac_zero F hM hv
  · exact fac_zero F hK hv

theorem sign_tr {a b c d : ℝ} (h : a * b = c * d) (hb : b < 0) (hc : 0 < c) :
    (d ≤ 0 → 0 ≤ a) ∧ (d < 0 → 0 < a) ∧ (d = 0 → a = 0) := by
  refine ⟨fun hd => ?_, fun hd => ?_, fun hd => ?_⟩
  · by_contra ha; rw [not_le] at ha; nlinarith [mul_pos_of_neg_of_neg ha hb, mul_nonpos_of_nonneg_of_nonpos hc.le hd]
  · by_contra ha; rw [not_lt] at ha; nlinarith [mul_nonneg_of_nonpos_of_nonpos ha hb.le, mul_neg_of_pos_of_neg hc hd]
  · rw [hd, mul_zero] at h; rcases mul_eq_zero.1 h with h | h
    · exact h
    · exact absurd h hb.ne

/-- **CSL at a `G`-orthogonal degree-3 corner `v`, over any facet list.**  `J, M, K` the corner neighbours (pairwise
orthogonal edges), `tg` the triangular facet `v J M`, `te` a facet through `v, M, K` missing `J`, `tf` a facet
through `v, J, K` missing `M`.  Every vertex off `te` other than `J` is strictly short of `J` along `v → J`, and some
vertex `q` is beyond `M` along `v → M`: the polytope is Rupert. -/
theorem csl_corner (F : S0xFac m S x) (hx : Function.Injective x) (v J M K : Fin n) (tg te tf : Fin m)
    (hJv : J ≠ v) (hMv : M ≠ v) (hKv : K ≠ v)
    (hJM : ⟪x J - x v, x M - x v⟫ = 0) (hJK : ⟪x J - x v, x K - x v⟫ = 0)
    (hMK : ⟪x M - x v, x K - x v⟫ = 0)
    (hg : ∀ i, i ∈ S tg ↔ i = J ∨ i = M ∨ i = v) (hKg : K ∉ S tg)
    (hte : M ∈ S te ∧ K ∈ S te ∧ v ∈ S te ∧ J ∉ S te)
    (htf : J ∈ S tf ∧ K ∈ S tf ∧ v ∈ S tf ∧ M ∉ S tf)
    (hNj : ∀ i : Fin n, i ∉ S te → i ≠ J → ⟪x i - x J, x J - x v⟫ < 0)
    (q : Fin n) (hOm : 0 < ⟪x q - x M, x M - x v⟫) :
    IsRupert (univ.image x) := by
  obtain ⟨heN, hepar⟩ := edge_par F hx v J M K te hMv hKv hJK hJM hMK hte.1 hte.2.1 hte.2.2.1 hte.2.2.2
  have hMJ : ⟪x M - x v, x J - x v⟫ = 0 := by rw [real_inner_comm]; exact hJM
  obtain ⟨hfN, hfpar⟩ := edge_par F hx v M J K tf hJv hKv hMK hMJ hJK htf.1 htf.2.1 htf.2.2.1 htf.2.2.2
  have hee : 0 < ⟪x J - x v, x J - x v⟫ := real_inner_self_pos.2 (sub_ne_of_ne hx hJv)
  have hff : 0 < ⟪x M - x v, x M - x v⟫ := real_inner_self_pos.2 (sub_ne_of_ne hx hMv)
  have hgJ : J ∈ S tg := (hg J).2 (Or.inl rfl)
  have hgM : M ∈ S tg := (hg M).2 (Or.inr (Or.inl rfl))
  have hgv : v ∈ S tg := (hg v).2 (Or.inr (Or.inr rfl))
  refine Minimality.Split.Corner.corner_euclid x v J M (x J - x v) (x M - x v) (-F.N tg) rfl rfl
    (sub_ne_of_ne hx hJv) (sub_ne_of_ne hx hMv) ?_ hJM ?_ ?_ ?_ ?_ ?_ ⟨q, ?_⟩
  · intro h
    have := fac_neg F hKg hgv
    rw [neg_eq_zero.1 h, inner_zero_left] at this
    exact lt_irrefl 0 this
  · rw [inner_neg_right, real_inner_comm, fac_zero F hgJ hgv, neg_zero]
  · rw [inner_neg_right, real_inner_comm, fac_zero F hgM hgv, neg_zero]
  · intro i h1 h2 h3
    have hi : i ∉ S tg := by
      rw [hg]; rintro (h | h | h)
      exacts [h2 h, h3 h, h1 h]
    rw [inner_neg_right, real_inner_comm]; linarith [fac_neg F hi hgv]
  · intro i
    refine ⟨(sign_tr (hepar _) heN hee).1 ?_, (sign_tr (hfpar _) hfN hff).1 ?_⟩
    · rw [real_inner_comm]; exact fac_le F i hte.2.2.1
    · rw [real_inner_comm]; exact fac_le F i htf.2.2.1
  · intro i hiJ
    have key : ⟪x i - x v, x J - x v⟫ - ⟪x J - x v, x J - x v⟫ = ⟪x i - x J, x J - x v⟫ := by
      rw [← inner_sub_left]; congr 1; abel
    by_cases hi : i ∈ S te
    · have : ⟪x i - x v, x J - x v⟫ = 0 := (sign_tr (hepar _) heN hee).2.2 (by
        rw [real_inner_comm]; exact fac_zero F hi hte.2.2.1)
      linarith
    · linarith [hNj i hi hiJ]
  · have key : ⟪x q - x v, x M - x v⟫ - ⟪x M - x v, x M - x v⟫ = ⟪x q - x M, x M - x v⟫ := by
      rw [← inner_sub_left]; congr 1; abel
    linarith

open Minimality.T24.SAT in
/-- **Lemma W (type 24)**: the sub-tie `E12 = E13 = E23 = 0` (vertex 5 trirectangular), as the instance of
`csl_corner` at corner `5`, `J = 2`, `M = 3`, `K = 0`, `tg = 6 = {2,3,5}`, `te = 3 = {0,3,4,5}`, `tf = 2 = {0,2,5}`. -/
theorem csl24 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (h20 : ⟪x 2 - x 5, x 0 - x 5⟫ = 0) (h23 : ⟪x 2 - x 5, x 3 - x 5⟫ = 0)
    (h03 : ⟪x 0 - x 5, x 3 - x 5⟫ = 0)
    (h1 : ⟪x 1 - x 2, x 2 - x 5⟫ < 0) (h6 : ⟪x 6 - x 2, x 2 - x 5⟫ < 0)
    (hq : 0 < ⟪x 6 - x 3, x 3 - x 5⟫ ∨ 0 < ⟪x 4 - x 3, x 3 - x 5⟫) :
    IsRupert (univ.image x) := by
  have hx := Minimality.EdgeViewLink.inj_of_fac24 F
  have hMK : ⟪x 3 - x 5, x 0 - x 5⟫ = 0 := by rw [real_inner_comm]; exact h03
  have hg : ∀ i : Fin 7, i ∈ s0x_S24 6 ↔ i = 2 ∨ i = 3 ∨ i = 5 := by decide
  have hNj : ∀ i : Fin 7, i ∉ s0x_S24 3 → i ≠ 2 → ⟪x i - x 2, x 2 - x 5⟫ < 0 := by
    intro i hi h2
    have : i = 1 ∨ i = 6 := by revert hi h2; revert i; decide
    rcases this with rfl | rfl
    exacts [h1, h6]
  rcases hq with hq | hq
  · exact csl_corner F hx 5 2 3 0 6 3 2 (by decide) (by decide) (by decide) h23 h20 hMK hg (by decide)
      (by decide) (by decide) hNj 6 hq
  · exact csl_corner F hx 5 2 3 0 6 3 2 (by decide) (by decide) (by decide) h23 h20 hMK hg (by decide)
      (by decide) (by decide) hNj 4 hq

end Minimality.CSLCorner
