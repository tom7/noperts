module

public import Minimality.SVCTieBreak
public import Minimality.SVCCells
public import Minimality.Type24

@[expose] public section

/-!
# SVCTieGeo: the tilt2 configuration at a view with two edge-on facets (Task TB24B)

Two facets `tA`, `tB` are edge-on at `w` (`⟪N,w⟫ = 0`), `o` lies on both, `vA` only on `tA`, `vB`
only on `tB`, and `eA = x vA - x o`, `eB = x vB - x o` are orthogonal to `w` (tied depths).  The
tilts `d = lA • eA + lB • eB` realise every sign pattern on the two zero facets, the data are the
Gram numbers `EA = |eA|²`, `EB = |eB|²`, `h = ⟪eA,eB⟫` (`h² < EA EB`), and any difference of two
points orthogonal to `w` is `a • eA + b • eB` (completeness).  A tied pair `p ∈ tA \ tB`,
`q ∈ tB \ tA` has `x q - x p = -α • eA + β • eB` with `α, β > 0` (incidence).
-/

set_option autoImplicit false

open scoped RealInnerProductSpace
open Minimality Minimality.H21

namespace Minimality.SVC.Geo

variable {m n : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}

theorem tbg_cross_par {p q w : ℝ³} (hw : w ≠ 0) (hp : ⟪p, w⟫ = 0) (hq : ⟪q, w⟫ = 0) :
    ∃ κ : ℝ, cross p q = κ • w := by
  have hww : ⟪w, w⟫ ≠ 0 := (real_inner_self_pos.mpr hw).ne'
  refine ⟨⟪cross p q, w⟫ / ⟪w, w⟫, ?_⟩
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial] at hp hq hww ⊢
  ext i
  fin_cases i <;>
  · simp only [cross_apply_zero, cross_apply_one, cross_apply_two, PiLp.smul_apply, smul_eq_mul,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    rw [div_mul_eq_mul_div, eq_div_iff hww]
    first
    | linear_combination (w 1 * q 2 - w 2 * q 1) * hp - (w 1 * p 2 - w 2 * p 1) * hq
    | linear_combination (w 2 * q 0 - w 0 * q 2) * hp - (w 2 * p 0 - w 0 * p 2) * hq
    | linear_combination (w 0 * q 1 - w 1 * q 0) * hp - (w 0 * p 1 - w 1 * p 0) * hq

theorem tbg_vol3_eq (a b c : ℝ³) : vol3 a b c = ⟪cross a b, c⟫ := by
  simp only [vol3, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial,
    cross_apply_zero, cross_apply_one, cross_apply_two]
  ring

/-- Vectors `a, b ⟂ g` with `vol3 a b g ≠ 0` span the plane `⟂ g`. -/
theorem tbg_span_perp {a b g v : ℝ³} (hD : vol3 a b g ≠ 0) (hg : g ≠ 0) (hv : ⟪v, g⟫ = 0)
    (ha : ⟪a, g⟫ = 0) (hb : ⟪b, g⟫ = 0) : ∃ l m : ℝ, v = l • a + m • b := by
  have h := vol3_smul_cramer a b g v
  have hgg : 0 < ⟪g, g⟫ := real_inner_self_pos.2 hg
  have h1 := congrArg (fun y => ⟪y, g⟫) h
  simp only [inner_add_left, real_inner_smul_left, hv, ha, hb] at h1
  have hz : vol3 a b v = 0 := by
    have : vol3 a b v * ⟪g, g⟫ = 0 := by linarith
    rcases mul_eq_zero.1 this with h0 | h0
    · exact h0
    · exact absurd h0 hgg.ne'
  rw [hz, zero_smul, add_zero] at h
  refine ⟨vol3 v b g / vol3 a b g, vol3 a v g / vol3 a b g, ?_⟩
  have h2 : v = (vol3 a b g)⁻¹ • (vol3 a b g • v) := by rw [smul_smul, inv_mul_cancel₀ hD, one_smul]
  rw [h, smul_add, smul_smul, smul_smul] at h2
  rw [div_eq_inv_mul, div_eq_inv_mul]
  exact h2

/-- The tilt2 configuration. -/
structure Tilt2 (F : S0xFac m S x) (tA tB : Fin m) (o vA vB : Fin n) (w : ℝ³) : Prop where
  ho1 : o ∈ S tA
  ho2 : o ∈ S tB
  hA1 : vA ∈ S tA
  hA2 : vA ∉ S tB
  hB1 : vB ∈ S tB
  hB2 : vB ∉ S tA
  wA : ⟪F.N tA, w⟫ = 0
  wB : ⟪F.N tB, w⟫ = 0
  eAw : ⟪x vA - x o, w⟫ = 0
  eBw : ⟪x vB - x o, w⟫ = 0
  w0 : w ≠ 0

namespace Tilt2

variable {F : S0xFac m S x} {tA tB : Fin m} {o vA vB : Fin n} {w : ℝ³}

theorem nAA (T : Tilt2 F tA tB o vA vB w) : ⟪F.N tA, x vA - x o⟫ = 0 := by
  rw [F.inner_sub, F.zero tA vA T.hA1, F.zero tA o T.ho1]; ring

theorem nBB (T : Tilt2 F tA tB o vA vB w) : ⟪F.N tB, x vB - x o⟫ = 0 := by
  rw [F.inner_sub, F.zero tB vB T.hB1, F.zero tB o T.ho2]; ring

theorem nBA (T : Tilt2 F tA tB o vA vB w) : ⟪F.N tB, x vA - x o⟫ = F.f tB (x vA) := by
  rw [F.inner_sub, F.zero tB o T.ho2]; ring

theorem nAB (T : Tilt2 F tA tB o vA vB w) : ⟪F.N tA, x vB - x o⟫ = F.f tA (x vB) := by
  rw [F.inner_sub, F.zero tA o T.ho1]; ring

theorem fBA_neg (T : Tilt2 F tA tB o vA vB w) : F.f tB (x vA) < 0 := F.neg tB vA T.hA2
theorem fAB_neg (T : Tilt2 F tA tB o vA vB w) : F.f tA (x vB) < 0 := F.neg tA vB T.hB2

theorem cross_ne (T : Tilt2 F tA tB o vA vB w) :
    ∃ κ : ℝ, κ ≠ 0 ∧ cross (x vA - x o) (x vB - x o) = κ • w := by
  obtain ⟨κ, hκ⟩ := tbg_cross_par T.w0 T.eAw T.eBw
  refine ⟨κ, ?_, hκ⟩
  intro h0
  rw [h0, zero_smul] at hκ
  have hb := h21_binet (F.N tA) (F.N tB) (x vA - x o) (x vB - x o)
  rw [hκ, inner_zero_right, T.nAA, T.nBB, T.nBA, T.nAB] at hb
  nlinarith [mul_pos_of_neg_of_neg T.fAB_neg T.fBA_neg]

theorem vol3_ne (T : Tilt2 F tA tB o vA vB w) : vol3 (x vA - x o) (x vB - x o) w ≠ 0 := by
  obtain ⟨κ, hκ, hc⟩ := T.cross_ne
  rw [tbg_vol3_eq, hc, real_inner_smul_left]
  exact mul_ne_zero hκ (real_inner_self_pos.mpr T.w0).ne'

/-- Completeness: every vector orthogonal to `w` is a combination of `eA`, `eB`. -/
theorem span (T : Tilt2 F tA tB o vA vB w) {e : ℝ³} (he : ⟪e, w⟫ = 0) :
    ∃ a b : ℝ, e = a • (x vA - x o) + b • (x vB - x o) :=
  tbg_span_perp T.vol3_ne T.w0 he T.eAw T.eBw

/-- Strict Cauchy-Schwarz for `eA`, `eB`. -/
theorem gram_pos (T : Tilt2 F tA tB o vA vB w) :
    ⟪x vA - x o, x vB - x o⟫ ^ 2 < ⟪x vA - x o, x vA - x o⟫ * ⟪x vB - x o, x vB - x o⟫ := by
  obtain ⟨κ, hκ, hc⟩ := T.cross_ne
  have hb := h21_binet (x vA - x o) (x vB - x o) (x vA - x o) (x vB - x o)
  rw [hc, real_inner_smul_left, real_inner_smul_right] at hb
  have h1 : 0 < κ * (κ * ⟪w, w⟫) := by
    have := real_inner_self_pos.mpr T.w0
    have hk := sq_pos_of_ne_zero hκ
    nlinarith
  rw [real_inner_comm (x vA - x o) (x vB - x o)] at hb
  nlinarith

theorem EA_pos (T : Tilt2 F tA tB o vA vB w) : 0 < ⟪x vA - x o, x vA - x o⟫ := by
  apply real_inner_self_pos.mpr
  intro h0
  have := T.nBA
  rw [h0, inner_zero_right] at this
  linarith [T.fBA_neg]

theorem EB_pos (T : Tilt2 F tA tB o vA vB w) : 0 < ⟪x vB - x o, x vB - x o⟫ := by
  apply real_inner_self_pos.mpr
  intro h0
  have := T.nAB
  rw [h0, inner_zero_right] at this
  linarith [T.fAB_neg]

/-- A tied pair `p ∈ tA \ tB`, `q ∈ tB \ tA`: `x q - x p = -α eA + β eB` with `α, β > 0`. -/
theorem pair (T : Tilt2 F tA tB o vA vB w) {p q : Fin n} (hp1 : p ∈ S tA) (hp2 : p ∉ S tB)
    (hq1 : q ∈ S tB) (hq2 : q ∉ S tA) (hpq : ⟪x q, w⟫ = ⟪x p, w⟫) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ x q - x p = (-α) • (x vA - x o) + β • (x vB - x o) := by
  have he : ⟪x q - x p, w⟫ = 0 := by rw [inner_sub_left, hpq]; ring
  obtain ⟨a, b, hab⟩ := T.span he
  have hNB := congrArg (fun y => ⟪F.N tB, y⟫) hab
  have hNA := congrArg (fun y => ⟪F.N tA, y⟫) hab
  simp only [inner_add_right, real_inner_smul_right, T.nBA, T.nBB, T.nAA, T.nAB, F.inner_sub,
    F.zero tB q hq1, F.zero tA p hp1] at hNB hNA
  have h1 := F.neg tB p hp2
  have h2 := F.neg tA q hq2
  have ha : a < 0 := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg hh (neg_nonneg.mpr T.fBA_neg.le)]
  have hb : 0 < b := by
    by_contra hh; push Not at hh
    nlinarith [mul_nonneg_of_nonpos_of_nonpos hh T.fAB_neg.le]
  exact ⟨-a, b, by linarith, hb, by rw [neg_neg]; exact hab⟩

/-- Inner products of `eA`, `eB` with a tilt `d = lA eA + lB eB` and the facet functionals. -/
theorem tilt_nA (T : Tilt2 F tA tB o vA vB w) (lA lB : ℝ) :
    ⟪F.N tA, lA • (x vA - x o) + lB • (x vB - x o)⟫ = lB * F.f tA (x vB) := by
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, T.nAA, T.nAB]; ring

theorem tilt_nB (T : Tilt2 F tA tB o vA vB w) (lA lB : ℝ) :
    ⟪F.N tB, lA • (x vA - x o) + lB • (x vB - x o)⟫ = lA * F.f tB (x vA) := by
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, T.nBA, T.nBB]; ring

theorem tilt_inner (a b lA lB : ℝ) (e1 e2 : ℝ³) :
    ⟪a • e1 + b • e2, lA • e1 + lB • e2⟫ =
      a * (lA * ⟪e1, e1⟫ + lB * ⟪e1, e2⟫) + b * (lA * ⟪e2, e1⟫ + lB * ⟪e2, e2⟫) := by
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]; ring

theorem sign_pos_of_neg_mul {a f : ℝ} (ha : a < 0) (hf : f < 0) : SignType.sign (a * f) = 1 :=
  sign_pos (mul_pos_of_neg_of_neg ha hf)

theorem sign_neg_of_pos_mul {a f : ℝ} (ha : 0 < a) (hf : f < 0) : SignType.sign (a * f) = -1 :=
  sign_neg (mul_neg_of_pos_of_neg ha hf)

end Tilt2

theorem tb_depth_sub (a b e1 e2 : ℝ³) (lA lB α β : ℝ) (h : a - b = α • e1 + β • e2) :
    ⟪a, lA • e1 + lB • e2⟫ = ⟪b, lA • e1 + lB • e2⟫ +
      (α * (lA * ⟪e1, e1⟫ + lB * ⟪e1, e2⟫) + β * (lA * ⟪e1, e2⟫ + lB * ⟪e2, e2⟫)) := by
  have h1 : ⟪a - b, lA • e1 + lB • e2⟫ = ⟪a, lA • e1 + lB • e2⟫ - ⟪b, lA • e1 + lB • e2⟫ :=
    inner_sub_left _ _ _
  have h2 : ⟪a - b, lA • e1 + lB • e2⟫ =
      α * (lA * ⟪e1, e1⟫ + lB * ⟪e1, e2⟫) + β * (lA * ⟪e1, e2⟫ + lB * ⟪e2, e2⟫) := by
    rw [h]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_comm e1 e2]
    ring
  linarith

theorem tb_same_block {p : ℕ} (z : Fin p → ℝ) (W : List (List (Fin p)))
    (hpw : W.Pairwise (fun B₁ B₂ => ∀ i ∈ B₁, ∀ j ∈ B₂, z i < z j))
    (hcov : ∀ i, ∃ B ∈ W, i ∈ B) {i j : Fin p} (h : z i = z j) : ∃ B ∈ W, i ∈ B ∧ j ∈ B := by
  obtain ⟨Bi, hBi, hi⟩ := hcov i
  obtain ⟨Bj, hBj, hj⟩ := hcov j
  obtain ⟨a, ha, rfl⟩ := List.mem_iff_getElem.mp hBi
  obtain ⟨b, hb, rfl⟩ := List.mem_iff_getElem.mp hBj
  by_cases hab : a = b
  · subst hab; exact ⟨_, hBi, hi, hj⟩
  · exfalso
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · have := (List.pairwise_iff_getElem.mp hpw) a b ha hb hlt i hi j hj
      linarith
    · have := (List.pairwise_iff_getElem.mp hpw) b a hb ha hgt j hj i hi
      linarith

theorem tb_htie_of_pairs {p : ℕ} (z pos : Fin p → ℝ) (W : List (List (Fin p))) (hW : TBLevel z W)
    (L : List (Fin p)) (pairs : List (Fin p × Fin p))
    (hcov : ∀ B ∈ W, ∀ i ∈ B, ∀ j ∈ B, rk L i < rk L j → (i, j) ∈ pairs)
    (hpairs : ∀ pr ∈ pairs, pos pr.1 < pos pr.2) :
    ∀ i j, z i = z j → rk L i < rk L j → pos i < pos j := by
  intro i j hij hr
  obtain ⟨B, hB, hi, hj⟩ := tb_same_block z W hW.2.1 hW.2.2 hij
  exact hpairs _ (hcov B hB i hi j hj hr)

theorem tbReal_of_tilt2 {p : ℕ} {F : S0xFac m S x} (P : Fin p → Fin n) {w : ℝ³}
    (sw : Fin m → SignType) (R : List (Rim m p)) (c : TBCert p) {tA tB : Fin m}
    {o vA vB : Fin n} (T : Tilt2 F tA tB o vA vB w) (hz : ∀ t, sw t = 0 → t = tA ∨ t = tB)
    (t0 : Fin m) (ht0 : ⟪F.N t0, w⟫ ≠ 0) (ρ : Rim m p) (hρ : R[c.ri]? = some ρ)
    (lA lB : ℝ) (hlB : lB ≠ 0) (hsA : SignType.sign (lB * F.f tA (x vB)) = ρ.sd tA)
    (hsB : SignType.sign (lA * F.f tB (x vA)) = ρ.sd tB)
    (htie : ∀ i j, ⟪x (P i), w⟫ = ⟪x (P j), w⟫ → rk c.L i < rk c.L j →
      ⟪x (P i), lA • (x vA - x o) + lB • (x vB - x o)⟫ <
        ⟪x (P j), lA • (x vA - x o) + lB • (x vB - x o)⟫) :
    TBReal F P w sw R c := by
  have hne : ⟪F.N tA, lA • (x vA - x o) + lB • (x vB - x o)⟫ ≠ 0 := by
    rw [T.tilt_nA]; exact mul_ne_zero hlB T.fAB_neg.ne
  obtain ⟨d2, hd2⟩ := exists_det3_ne_zero ht0 T.wA hne
  refine ⟨ρ, hρ, lA • (x vA - x o) + lB • (x vB - x o), d2, ?_, hd2, htie⟩
  intro t ht
  rcases hz t ht with rfl | rfl
  · rw [T.tilt_nA]; exact hsA
  · rw [T.tilt_nB]; exact hsB

end Minimality.SVC.Geo
