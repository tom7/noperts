module

public import Minimality.Type24Circle

@[expose] public section

/-!
# Type 24 link edges 06: rim determinants and transversality (nopert229 report LINKRIM24).
-/

set_option autoImplicit true
set_option relaxedAutoImplicit true
open scoped RealInnerProductSpace

namespace Minimality
namespace Link24R

open Finset

/-- The determinant part of `EdgeRim` (everything but depth injectivity and `NoHDNAt`). -/
def EdgeRimDet (x : Fin 7 → ℝ³) (u : ℝ³) (d : Fin 7) (h : ℝ) (k : ℕ) [NeZero k]
    (r : ZMod k → Fin 7) : Prop :=
  3 ≤ k ∧ h ≠ 0 ∧ x d = x (r 0) - h • u ∧
    (∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (x (r (i + 1)) - x (r i)) (x (r j) - x (r i)) u) ∧
    (∀ v, v ≠ d → (∀ j, v ≠ r j) → ∀ i,
      0 < det3 (x (r (i + 1)) - x (r i)) (x v - x (r i)) u)

/-- Vectors orthogonal to `w ≠ 0` have a cross product parallel to `w`. -/
theorem cross_par_of_orth (p q w : ℝ³) (hw : w ≠ 0) (hp : ⟪p, w⟫ = 0) (hq : ⟪q, w⟫ = 0) :
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

/-- The edge identity: `κ det3 (b-a) (y-a) u = ⟪NF,y-a⟫⟪NG,u⟫ - ⟪NF,u⟫⟪NG,y-a⟫`. -/
theorem edge_ident (NF NG w z u : ℝ³) (κ : ℝ) (hκ : cross NF NG = κ • w) :
    κ * det3 w z u = ⟪NF, z⟫ * ⟪NG, u⟫ - ⟪NF, u⟫ * ⟪NG, z⟫ := by
  have h0 := congrFun (congrArg (fun v : ℝ³ => (v : Fin 3 → ℝ)) hκ) 0
  have h1 := congrFun (congrArg (fun v : ℝ³ => (v : Fin 3 → ℝ)) hκ) 1
  have h2 := congrFun (congrArg (fun v : ℝ³ => (v : Fin 3 → ℝ)) hκ) 2
  simp only [cross_apply_zero, cross_apply_one, cross_apply_two, PiLp.smul_apply,
    smul_eq_mul] at h0 h1 h2
  simp only [det3_expand, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
  linear_combination -(z 1 * u 2 - z 2 * u 1) * h0 - (z 2 * u 0 - z 0 * u 2) * h1 -
    (z 0 * u 1 - z 1 * u 0) * h2

theorem Rpos {fF fG sF sG : ℝ} (hF : fF ≤ 0) (hG : fG ≤ 0) (hsF : 0 < sF) (hsG : sG ≤ 0)
    (h : fG < 0 ∨ (fF < 0 ∧ sG < 0)) : 0 < fF * sG - sF * fG := by
  rcases h with h | ⟨h1, h2⟩
  · nlinarith [mul_nonneg (neg_nonneg.mpr hF) (neg_nonneg.mpr hsG), mul_pos hsF (neg_pos.mpr h)]
  · nlinarith [mul_pos (neg_pos.mpr h1) (neg_pos.mpr h2), mul_nonneg hsF.le (neg_nonneg.mpr hG)]

/-- **Edge step.** A common edge `a b` of the facets `F` (facing away, `⟪NF,u⟫ > 0`) and `G`
(`⟪NG,u⟫ ≤ 0`); if the triple `(a,b,w)` is positive at the view `u` and `w`, `v` are strictly
beneath `G` (or beneath `F` with `G` strictly facing), then `(a,b,v)` is positive. -/
theorem edgeStep {x : Fin 7 → ℝ³} {S1 S2 : Finset (Fin 7)} (F : Face16 x S1) (G : Face16 x S2)
    (u : ℝ³) {a b w v : Fin 7} (ha1 : a ∈ S1) (hb1 : b ∈ S1) (ha2 : a ∈ S2) (hb2 : b ∈ S2)
    (hab : x a ≠ x b) (sF : 0 < ⟪F.N, u⟫) (sG : ⟪G.N, u⟫ ≤ 0)
    (hw : 0 < det3 (x b - x a) (x w - x a) u)
    (hGw : w ∉ S2 ∨ (w ∉ S1 ∧ ⟪G.N, u⟫ < 0)) (hGv : v ∉ S2 ∨ (v ∉ S1 ∧ ⟪G.N, u⟫ < 0)) :
    0 < det3 (x b - x a) (x v - x a) u := by
  have hFw : ⟪F.N, x b - x a⟫ = 0 := by
    rw [Type24.f_eq_inner F, F.zero b hb1, F.zero a ha1]; simp
  have hGw' : ⟪G.N, x b - x a⟫ = 0 := by
    rw [Type24.f_eq_inner G, G.zero b hb2, G.zero a ha2]; simp
  obtain ⟨κ, hκ⟩ := cross_par_of_orth F.N G.N (x b - x a) (sub_ne_zero.mpr hab.symm) hFw hGw'
  have key : ∀ y, κ * det3 (x b - x a) (y - x a) u =
      ⟪F.N, y - x a⟫ * ⟪G.N, u⟫ - ⟪F.N, u⟫ * ⟪G.N, y - x a⟫ := fun y =>
    edge_ident F.N G.N _ _ u κ hκ
  have R : ∀ y : Fin 7, (y ∉ S2 ∨ (y ∉ S1 ∧ ⟪G.N, u⟫ < 0)) →
      0 < κ * det3 (x b - x a) (x y - x a) u := by
    intro y hy
    rw [key, Type24.f_eq_inner F, Type24.f_eq_inner G, F.zero a ha1, G.zero a ha2]
    simp only [sub_zero]
    refine Rpos (Type24.f_le F y) (Type24.f_le G y) sF sG ?_
    rcases hy with h | ⟨h1, h2⟩
    · exact Or.inl (G.neg y h)
    · exact Or.inr ⟨F.neg y h1, h2⟩
  have hκ0 : 0 < κ := by
    have := R w hGw
    by_contra hc; push Not at hc
    nlinarith
  have := R v hGv
  by_contra hc; push Not at hc
  nlinarith

/-- The rim `(X, 4, 3, 2, 1)` of the link edge `06`. -/
def rim06 (X : Fin 7) : ZMod 5 → Fin 7 := ![X, 4, 3, 2, 1]

/-- The rim `(X, 4, 3, 5, 2, 1)` of the link edge `06`. -/
def rim06s (X : Fin 7) : ZMod 6 → Fin 7 := ![X, 4, 3, 5, 2, 1]

theorem tcyc (x : Fin 7 → ℝ³) (u : ℝ³) (a b c : Fin 7) :
    det3 (x b - x a) (x c - x a) u = det3 (x c - x b) (x a - x b) u := by
  simp only [det3_expand, PiLp.sub_apply]; ring

theorem det3_shift (a b c u : ℝ³) (s1 s2 s3 : ℝ) :
    det3 ((a + s1 • u) - (b + s2 • u)) ((c + s3 • u) - (b + s2 • u)) u = det3 (a - b) (c - b) u := by
  simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring

theorem inner_in0 {x : Fin 7 → ℝ³} {S : Finset (Fin 7)} (F : Face16 x S) (h0 : 0 ∈ S)
    (h6 : 6 ∉ S) : ⟪F.N, x 6 - x 0⟫ < 0 := by
  rw [Type24.f_eq_inner F 6 0, F.zero 0 h0]; have := F.neg 6 h6; linarith

theorem inner_in6 {x : Fin 7 → ℝ³} {S : Finset (Fin 7)} (F : Face16 x S) (h0 : 0 ∉ S)
    (h6 : 6 ∈ S) : 0 < ⟪F.N, x 6 - x 0⟫ := by
  rw [Type24.f_eq_inner F 6 0, F.zero 6 h6]; have := F.neg 0 h0; linarith

theorem inner_both {x : Fin 7 → ℝ³} {S : Finset (Fin 7)} (F : Face16 x S) (h0 : 0 ∈ S)
    (h6 : 6 ∈ S) : ⟪F.N, x 6 - x 0⟫ = 0 := by
  rw [Type24.f_eq_inner F 6 0, F.zero 6 h6, F.zero 0 h0]; simp

/-- The tilt-free screen test `(6, 4, 1)` is positive (`det24 > 0`). -/
theorem ref641 {x : Fin 7 → ℝ³} (T : Type24 x) (hM : 0 < det24 x) :
    0 < det3 (x 4 - x 6) (x 1 - x 6) (x 6 - x 0) := by
  have e1 : x 4 - x 6 = oblX0 x 4 • (x 0 - x 1) + oblX2 x 4 • (x 2 - x 1) +
      (oblX6 x 4 - 1) • (x 6 - x 1) := by
    linear_combination (norm := module) (T.rep 4)
  have e2 : x 1 - x 6 = (0:ℝ) • (x 0 - x 1) + (0:ℝ) • (x 2 - x 1) + (-1:ℝ) • (x 6 - x 1) := by
    module
  have e3 : x 6 - x 0 = (-1:ℝ) • (x 0 - x 1) + (0:ℝ) • (x 2 - x 1) + (1:ℝ) • (x 6 - x 1) := by
    module
  rw [e1, e2, e3, det3_comb]
  have h2 := T.X2_pos (v := 4) (by decide)
  have : det24 x = vol3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) := rfl
  rw [← this]
  nlinarith

/-- The cyclic-chain facts at `u = x 6 - x 0`, chain `4, 3, 2` (`235` facing, `⟪N235,u⟫ < 0`). -/
theorem det06A {x : Fin 7 → ℝ³} (T : Type24 x) (F0345 : Face16 x {0, 3, 4, 5})
    (F235 : Face16 x {2, 3, 5}) (F346 : Face16 x {3, 4, 6}) (hM : 0 < det24 x)
    (hs : ⟪F235.N, x 6 - x 0⟫ < 0) : EdgeRimDet x (x 6 - x 0) 0 1 5 (rim06 6) := by
  have inj := T.inj
  have hne : ∀ a b : Fin 7, a ≠ b → x a ≠ x b := fun a b h e => h (inj e)
  have s126 := inner_in6 T.t126 (by decide) (by decide)
  have s016 := inner_both T.t016 (by decide) (by decide)
  have s012 := inner_in0 T.t012 (by decide) (by decide)
  have s046 := inner_both T.t046 (by decide) (by decide)
  have s236 := inner_in6 T.t236 (by decide) (by decide)
  have s346 := inner_in6 F346 (by decide) (by decide)
  have s0345 := inner_in0 F0345 (by decide) (by decide)
  have s025 := inner_in0 T.t025 (by decide) (by decide)
  have s235 := hs
  have s0345lt := s0345
  have s235lt := s235
  have ref641 := ref641 T hM
  have t643 : 0 < det3 (x 4 - x 6) (x 3 - x 6) (x 6 - x 0) :=
    edgeStep F346 T.t046 _ (a := 6) (b := 4) (w := 1) (v := 3) (by decide) (by decide) (by decide) (by decide)
      (hne 6 4 (by decide)) s346 s046.le ref641 (Or.inl (by decide)) (Or.inl (by decide))
  have t642 : 0 < det3 (x 4 - x 6) (x 2 - x 6) (x 6 - x 0) :=
    edgeStep F346 T.t046 _ (a := 6) (b := 4) (w := 1) (v := 2) (by decide) (by decide) (by decide) (by decide)
      (hne 6 4 (by decide)) s346 s046.le ref641 (Or.inl (by decide)) (Or.inl (by decide))
  have t641 : 0 < det3 (x 4 - x 6) (x 1 - x 6) (x 6 - x 0) :=
    edgeStep F346 T.t046 _ (a := 6) (b := 4) (w := 1) (v := 1) (by decide) (by decide) (by decide) (by decide)
      (hne 6 4 (by decide)) s346 s046.le ref641 (Or.inl (by decide)) (Or.inl (by decide))
  have t645 : 0 < det3 (x 4 - x 6) (x 5 - x 6) (x 6 - x 0) :=
    edgeStep F346 T.t046 _ (a := 6) (b := 4) (w := 1) (v := 5) (by decide) (by decide) (by decide) (by decide)
      (hne 6 4 (by decide)) s346 s046.le ref641 (Or.inl (by decide)) (Or.inl (by decide))
  have t436 : 0 < det3 (x 3 - x 4) (x 6 - x 4) (x 6 - x 0) :=
    edgeStep F346 F0345 _ (a := 4) (b := 3) (w := 6) (v := 6) (by decide) (by decide) (by decide) (by decide)
      (hne 4 3 (by decide)) s346 s0345.le (by rw [← tcyc x _ 6 4 3]; exact t643) (Or.inl (by decide)) (Or.inl (by decide))
  have t432 : 0 < det3 (x 3 - x 4) (x 2 - x 4) (x 6 - x 0) :=
    edgeStep F346 F0345 _ (a := 4) (b := 3) (w := 6) (v := 2) (by decide) (by decide) (by decide) (by decide)
      (hne 4 3 (by decide)) s346 s0345.le (by rw [← tcyc x _ 6 4 3]; exact t643) (Or.inl (by decide)) (Or.inl (by decide))
  have t431 : 0 < det3 (x 3 - x 4) (x 1 - x 4) (x 6 - x 0) :=
    edgeStep F346 F0345 _ (a := 4) (b := 3) (w := 6) (v := 1) (by decide) (by decide) (by decide) (by decide)
      (hne 4 3 (by decide)) s346 s0345.le (by rw [← tcyc x _ 6 4 3]; exact t643) (Or.inl (by decide)) (Or.inl (by decide))
  have t435 : 0 < det3 (x 3 - x 4) (x 5 - x 4) (x 6 - x 0) :=
    edgeStep F346 F0345 _ (a := 4) (b := 3) (w := 6) (v := 5) (by decide) (by decide) (by decide) (by decide)
      (hne 4 3 (by decide)) s346 s0345.le (by rw [← tcyc x _ 6 4 3]; exact t643) (Or.inl (by decide)) (Or.inr ⟨by decide, s0345lt⟩)
  have t324 : 0 < det3 (x 2 - x 3) (x 4 - x 3) (x 6 - x 0) :=
    edgeStep T.t236 F235 _ (a := 3) (b := 2) (w := 4) (v := 4) (by decide) (by decide) (by decide) (by decide)
      (hne 3 2 (by decide)) s236 s235.le (by rw [← tcyc x _ 4 3 2]; exact t432) (Or.inl (by decide)) (Or.inl (by decide))
  have t321 : 0 < det3 (x 2 - x 3) (x 1 - x 3) (x 6 - x 0) :=
    edgeStep T.t236 F235 _ (a := 3) (b := 2) (w := 4) (v := 1) (by decide) (by decide) (by decide) (by decide)
      (hne 3 2 (by decide)) s236 s235.le (by rw [← tcyc x _ 4 3 2]; exact t432) (Or.inl (by decide)) (Or.inl (by decide))
  have t326 : 0 < det3 (x 2 - x 3) (x 6 - x 3) (x 6 - x 0) :=
    edgeStep T.t236 F235 _ (a := 3) (b := 2) (w := 4) (v := 6) (by decide) (by decide) (by decide) (by decide)
      (hne 3 2 (by decide)) s236 s235.le (by rw [← tcyc x _ 4 3 2]; exact t432) (Or.inl (by decide)) (Or.inl (by decide))
  have t325 : 0 < det3 (x 2 - x 3) (x 5 - x 3) (x 6 - x 0) :=
    edgeStep T.t236 F235 _ (a := 3) (b := 2) (w := 4) (v := 5) (by decide) (by decide) (by decide) (by decide)
      (hne 3 2 (by decide)) s236 s235.le (by rw [← tcyc x _ 4 3 2]; exact t432) (Or.inl (by decide)) (Or.inr ⟨by decide, s235lt⟩)
  have t213 : 0 < det3 (x 1 - x 2) (x 3 - x 2) (x 6 - x 0) :=
    edgeStep T.t126 T.t012 _ (a := 2) (b := 1) (w := 3) (v := 3) (by decide) (by decide) (by decide) (by decide)
      (hne 2 1 (by decide)) s126 s012.le (by rw [← tcyc x _ 3 2 1]; exact t321) (Or.inl (by decide)) (Or.inl (by decide))
  have t214 : 0 < det3 (x 1 - x 2) (x 4 - x 2) (x 6 - x 0) :=
    edgeStep T.t126 T.t012 _ (a := 2) (b := 1) (w := 3) (v := 4) (by decide) (by decide) (by decide) (by decide)
      (hne 2 1 (by decide)) s126 s012.le (by rw [← tcyc x _ 3 2 1]; exact t321) (Or.inl (by decide)) (Or.inl (by decide))
  have t216 : 0 < det3 (x 1 - x 2) (x 6 - x 2) (x 6 - x 0) :=
    edgeStep T.t126 T.t012 _ (a := 2) (b := 1) (w := 3) (v := 6) (by decide) (by decide) (by decide) (by decide)
      (hne 2 1 (by decide)) s126 s012.le (by rw [← tcyc x _ 3 2 1]; exact t321) (Or.inl (by decide)) (Or.inl (by decide))
  have t215 : 0 < det3 (x 1 - x 2) (x 5 - x 2) (x 6 - x 0) :=
    edgeStep T.t126 T.t012 _ (a := 2) (b := 1) (w := 3) (v := 5) (by decide) (by decide) (by decide) (by decide)
      (hne 2 1 (by decide)) s126 s012.le (by rw [← tcyc x _ 3 2 1]; exact t321) (Or.inl (by decide)) (Or.inl (by decide))
  have t162 : 0 < det3 (x 6 - x 1) (x 2 - x 1) (x 6 - x 0) :=
    edgeStep T.t126 T.t016 _ (a := 1) (b := 6) (w := 2) (v := 2) (by decide) (by decide) (by decide) (by decide)
      (hne 1 6 (by decide)) s126 s016.le (by rw [← tcyc x _ 2 1 6]; exact t216) (Or.inl (by decide)) (Or.inl (by decide))
  have t163 : 0 < det3 (x 6 - x 1) (x 3 - x 1) (x 6 - x 0) :=
    edgeStep T.t126 T.t016 _ (a := 1) (b := 6) (w := 2) (v := 3) (by decide) (by decide) (by decide) (by decide)
      (hne 1 6 (by decide)) s126 s016.le (by rw [← tcyc x _ 2 1 6]; exact t216) (Or.inl (by decide)) (Or.inl (by decide))
  have t164 : 0 < det3 (x 6 - x 1) (x 4 - x 1) (x 6 - x 0) :=
    edgeStep T.t126 T.t016 _ (a := 1) (b := 6) (w := 2) (v := 4) (by decide) (by decide) (by decide) (by decide)
      (hne 1 6 (by decide)) s126 s016.le (by rw [← tcyc x _ 2 1 6]; exact t216) (Or.inl (by decide)) (Or.inl (by decide))
  have t165 : 0 < det3 (x 6 - x 1) (x 5 - x 1) (x 6 - x 0) :=
    edgeStep T.t126 T.t016 _ (a := 1) (b := 6) (w := 2) (v := 5) (by decide) (by decide) (by decide) (by decide)
      (hne 1 6 (by decide)) s126 s016.le (by rw [← tcyc x _ 2 1 6]; exact t216) (Or.inl (by decide)) (Or.inl (by decide))
  refine ⟨by norm_num, one_ne_zero, ?_, ?_, ?_⟩
  · show x 0 = x 6 - (1 : ℝ) • (x 6 - x 0)
    rw [one_smul]; abel
  · obtain ⟨a0, a1, a2, a3, a4⟩ := zmod5_add_one
    have r0 : rim06 6 0 = 6 := rfl
    have r1 : rim06 6 1 = 4 := rfl
    have r2 : rim06 6 2 = 3 := rfl
    have r3 : rim06 6 3 = 2 := rfl
    have r4 : rim06 6 4 = 1 := rfl
    intro i j hj1 hj2
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [a0, a1, a2, a3, a4, r0, r1, r2, r3, r4] at hj1 hj2 ⊢ <;>
    first | exact absurd rfl hj1 | exact absurd rfl hj2 | assumption
  · obtain ⟨a0, a1, a2, a3, a4⟩ := zmod5_add_one
    have r0 : rim06 6 0 = 6 := rfl
    have r1 : rim06 6 1 = 4 := rfl
    have r2 : rim06 6 2 = 3 := rfl
    have r3 : rim06 6 3 = 2 := rfl
    have r4 : rim06 6 4 = 1 := rfl
    intro v hv hvr i
    have h0 := hvr 0; have h1 := hvr 1; have h2 := hvr 2; have h3 := hvr 3; have h4 := hvr 4
    rw [r0] at h0; rw [r1] at h1; rw [r2] at h2; rw [r3] at h3; rw [r4] at h4
    have hv5 : v = 5 := by
      clear hvr; fin_cases v <;> simp_all
    subst hv5
    rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    simp only [a0, a1, a2, a3, a4, r0, r1, r2, r3, r4] <;> assumption

/-- Chain `4, 3, 5, 2` (`⟪N235,u⟫ > 0`). -/
theorem det06B {x : Fin 7 → ℝ³} (T : Type24 x) (F0345 : Face16 x {0, 3, 4, 5})
    (F235 : Face16 x {2, 3, 5}) (F346 : Face16 x {3, 4, 6}) (hM : 0 < det24 x)
    (hs : 0 < ⟪F235.N, x 6 - x 0⟫) : EdgeRimDet x (x 6 - x 0) 0 1 6 (rim06s 6) := by
  have inj := T.inj
  have hne : ∀ a b : Fin 7, a ≠ b → x a ≠ x b := fun a b h e => h (inj e)
  have s126 := inner_in6 T.t126 (by decide) (by decide)
  have s016 := inner_both T.t016 (by decide) (by decide)
  have s012 := inner_in0 T.t012 (by decide) (by decide)
  have s046 := inner_both T.t046 (by decide) (by decide)
  have s236 := inner_in6 T.t236 (by decide) (by decide)
  have s346 := inner_in6 F346 (by decide) (by decide)
  have s0345 := inner_in0 F0345 (by decide) (by decide)
  have s025 := inner_in0 T.t025 (by decide) (by decide)
  have s235 := hs
  have s0345lt := s0345
  have s235lt := s235
  have ref641 := ref641 T hM
  have t643 : 0 < det3 (x 4 - x 6) (x 3 - x 6) (x 6 - x 0) :=
    edgeStep F346 T.t046 _ (a := 6) (b := 4) (w := 1) (v := 3) (by decide) (by decide) (by decide) (by decide)
      (hne 6 4 (by decide)) s346 s046.le ref641 (Or.inl (by decide)) (Or.inl (by decide))
  have t642 : 0 < det3 (x 4 - x 6) (x 2 - x 6) (x 6 - x 0) :=
    edgeStep F346 T.t046 _ (a := 6) (b := 4) (w := 1) (v := 2) (by decide) (by decide) (by decide) (by decide)
      (hne 6 4 (by decide)) s346 s046.le ref641 (Or.inl (by decide)) (Or.inl (by decide))
  have t641 : 0 < det3 (x 4 - x 6) (x 1 - x 6) (x 6 - x 0) :=
    edgeStep F346 T.t046 _ (a := 6) (b := 4) (w := 1) (v := 1) (by decide) (by decide) (by decide) (by decide)
      (hne 6 4 (by decide)) s346 s046.le ref641 (Or.inl (by decide)) (Or.inl (by decide))
  have t645 : 0 < det3 (x 4 - x 6) (x 5 - x 6) (x 6 - x 0) :=
    edgeStep F346 T.t046 _ (a := 6) (b := 4) (w := 1) (v := 5) (by decide) (by decide) (by decide) (by decide)
      (hne 6 4 (by decide)) s346 s046.le ref641 (Or.inl (by decide)) (Or.inl (by decide))
  have t436 : 0 < det3 (x 3 - x 4) (x 6 - x 4) (x 6 - x 0) :=
    edgeStep F346 F0345 _ (a := 4) (b := 3) (w := 6) (v := 6) (by decide) (by decide) (by decide) (by decide)
      (hne 4 3 (by decide)) s346 s0345.le (by rw [← tcyc x _ 6 4 3]; exact t643) (Or.inl (by decide)) (Or.inl (by decide))
  have t432 : 0 < det3 (x 3 - x 4) (x 2 - x 4) (x 6 - x 0) :=
    edgeStep F346 F0345 _ (a := 4) (b := 3) (w := 6) (v := 2) (by decide) (by decide) (by decide) (by decide)
      (hne 4 3 (by decide)) s346 s0345.le (by rw [← tcyc x _ 6 4 3]; exact t643) (Or.inl (by decide)) (Or.inl (by decide))
  have t431 : 0 < det3 (x 3 - x 4) (x 1 - x 4) (x 6 - x 0) :=
    edgeStep F346 F0345 _ (a := 4) (b := 3) (w := 6) (v := 1) (by decide) (by decide) (by decide) (by decide)
      (hne 4 3 (by decide)) s346 s0345.le (by rw [← tcyc x _ 6 4 3]; exact t643) (Or.inl (by decide)) (Or.inl (by decide))
  have t435 : 0 < det3 (x 3 - x 4) (x 5 - x 4) (x 6 - x 0) :=
    edgeStep F346 F0345 _ (a := 4) (b := 3) (w := 6) (v := 5) (by decide) (by decide) (by decide) (by decide)
      (hne 4 3 (by decide)) s346 s0345.le (by rw [← tcyc x _ 6 4 3]; exact t643) (Or.inl (by decide)) (Or.inr ⟨by decide, s0345lt⟩)
  have t354 : 0 < det3 (x 5 - x 3) (x 4 - x 3) (x 6 - x 0) :=
    edgeStep F235 F0345 _ (a := 3) (b := 5) (w := 4) (v := 4) (by decide) (by decide) (by decide) (by decide)
      (hne 3 5 (by decide)) s235 s0345.le (by rw [← tcyc x _ 4 3 5]; exact t435) (Or.inr ⟨by decide, s0345lt⟩) (Or.inr ⟨by decide, s0345lt⟩)
  have t352 : 0 < det3 (x 5 - x 3) (x 2 - x 3) (x 6 - x 0) :=
    edgeStep F235 F0345 _ (a := 3) (b := 5) (w := 4) (v := 2) (by decide) (by decide) (by decide) (by decide)
      (hne 3 5 (by decide)) s235 s0345.le (by rw [← tcyc x _ 4 3 5]; exact t435) (Or.inr ⟨by decide, s0345lt⟩) (Or.inl (by decide))
  have t351 : 0 < det3 (x 5 - x 3) (x 1 - x 3) (x 6 - x 0) :=
    edgeStep F235 F0345 _ (a := 3) (b := 5) (w := 4) (v := 1) (by decide) (by decide) (by decide) (by decide)
      (hne 3 5 (by decide)) s235 s0345.le (by rw [← tcyc x _ 4 3 5]; exact t435) (Or.inr ⟨by decide, s0345lt⟩) (Or.inl (by decide))
  have t356 : 0 < det3 (x 5 - x 3) (x 6 - x 3) (x 6 - x 0) :=
    edgeStep F235 F0345 _ (a := 3) (b := 5) (w := 4) (v := 6) (by decide) (by decide) (by decide) (by decide)
      (hne 3 5 (by decide)) s235 s0345.le (by rw [← tcyc x _ 4 3 5]; exact t435) (Or.inr ⟨by decide, s0345lt⟩) (Or.inl (by decide))
  have t523 : 0 < det3 (x 2 - x 5) (x 3 - x 5) (x 6 - x 0) :=
    edgeStep F235 T.t025 _ (a := 5) (b := 2) (w := 3) (v := 3) (by decide) (by decide) (by decide) (by decide)
      (hne 5 2 (by decide)) s235 s025.le (by rw [← tcyc x _ 3 5 2]; exact t352) (Or.inl (by decide)) (Or.inl (by decide))
  have t521 : 0 < det3 (x 2 - x 5) (x 1 - x 5) (x 6 - x 0) :=
    edgeStep F235 T.t025 _ (a := 5) (b := 2) (w := 3) (v := 1) (by decide) (by decide) (by decide) (by decide)
      (hne 5 2 (by decide)) s235 s025.le (by rw [← tcyc x _ 3 5 2]; exact t352) (Or.inl (by decide)) (Or.inl (by decide))
  have t526 : 0 < det3 (x 2 - x 5) (x 6 - x 5) (x 6 - x 0) :=
    edgeStep F235 T.t025 _ (a := 5) (b := 2) (w := 3) (v := 6) (by decide) (by decide) (by decide) (by decide)
      (hne 5 2 (by decide)) s235 s025.le (by rw [← tcyc x _ 3 5 2]; exact t352) (Or.inl (by decide)) (Or.inl (by decide))
  have t524 : 0 < det3 (x 2 - x 5) (x 4 - x 5) (x 6 - x 0) :=
    edgeStep F235 T.t025 _ (a := 5) (b := 2) (w := 3) (v := 4) (by decide) (by decide) (by decide) (by decide)
      (hne 5 2 (by decide)) s235 s025.le (by rw [← tcyc x _ 3 5 2]; exact t352) (Or.inl (by decide)) (Or.inl (by decide))
  have t215 : 0 < det3 (x 1 - x 2) (x 5 - x 2) (x 6 - x 0) :=
    edgeStep T.t126 T.t012 _ (a := 2) (b := 1) (w := 5) (v := 5) (by decide) (by decide) (by decide) (by decide)
      (hne 2 1 (by decide)) s126 s012.le (by rw [← tcyc x _ 5 2 1]; exact t521) (Or.inl (by decide)) (Or.inl (by decide))
  have t213 : 0 < det3 (x 1 - x 2) (x 3 - x 2) (x 6 - x 0) :=
    edgeStep T.t126 T.t012 _ (a := 2) (b := 1) (w := 5) (v := 3) (by decide) (by decide) (by decide) (by decide)
      (hne 2 1 (by decide)) s126 s012.le (by rw [← tcyc x _ 5 2 1]; exact t521) (Or.inl (by decide)) (Or.inl (by decide))
  have t214 : 0 < det3 (x 1 - x 2) (x 4 - x 2) (x 6 - x 0) :=
    edgeStep T.t126 T.t012 _ (a := 2) (b := 1) (w := 5) (v := 4) (by decide) (by decide) (by decide) (by decide)
      (hne 2 1 (by decide)) s126 s012.le (by rw [← tcyc x _ 5 2 1]; exact t521) (Or.inl (by decide)) (Or.inl (by decide))
  have t216 : 0 < det3 (x 1 - x 2) (x 6 - x 2) (x 6 - x 0) :=
    edgeStep T.t126 T.t012 _ (a := 2) (b := 1) (w := 5) (v := 6) (by decide) (by decide) (by decide) (by decide)
      (hne 2 1 (by decide)) s126 s012.le (by rw [← tcyc x _ 5 2 1]; exact t521) (Or.inl (by decide)) (Or.inl (by decide))
  have t162 : 0 < det3 (x 6 - x 1) (x 2 - x 1) (x 6 - x 0) :=
    edgeStep T.t126 T.t016 _ (a := 1) (b := 6) (w := 2) (v := 2) (by decide) (by decide) (by decide) (by decide)
      (hne 1 6 (by decide)) s126 s016.le (by rw [← tcyc x _ 2 1 6]; exact t216) (Or.inl (by decide)) (Or.inl (by decide))
  have t163 : 0 < det3 (x 6 - x 1) (x 3 - x 1) (x 6 - x 0) :=
    edgeStep T.t126 T.t016 _ (a := 1) (b := 6) (w := 2) (v := 3) (by decide) (by decide) (by decide) (by decide)
      (hne 1 6 (by decide)) s126 s016.le (by rw [← tcyc x _ 2 1 6]; exact t216) (Or.inl (by decide)) (Or.inl (by decide))
  have t164 : 0 < det3 (x 6 - x 1) (x 4 - x 1) (x 6 - x 0) :=
    edgeStep T.t126 T.t016 _ (a := 1) (b := 6) (w := 2) (v := 4) (by decide) (by decide) (by decide) (by decide)
      (hne 1 6 (by decide)) s126 s016.le (by rw [← tcyc x _ 2 1 6]; exact t216) (Or.inl (by decide)) (Or.inl (by decide))
  have t165 : 0 < det3 (x 6 - x 1) (x 5 - x 1) (x 6 - x 0) :=
    edgeStep T.t126 T.t016 _ (a := 1) (b := 6) (w := 2) (v := 5) (by decide) (by decide) (by decide) (by decide)
      (hne 1 6 (by decide)) s126 s016.le (by rw [← tcyc x _ 2 1 6]; exact t216) (Or.inl (by decide)) (Or.inl (by decide))
  refine ⟨by norm_num, one_ne_zero, ?_, ?_, ?_⟩
  · show x 0 = x 6 - (1 : ℝ) • (x 6 - x 0)
    rw [one_smul]; abel
  · obtain ⟨a0, a1, a2, a3, a4, a5⟩ := zmod6_add_one
    have r0 : rim06s 6 0 = 6 := rfl
    have r1 : rim06s 6 1 = 4 := rfl
    have r2 : rim06s 6 2 = 3 := rfl
    have r3 : rim06s 6 3 = 5 := rfl
    have r4 : rim06s 6 4 = 2 := rfl
    have r5 : rim06s 6 5 = 1 := rfl
    intro i j hj1 hj2
    rcases zmod6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases zmod6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [a0, a1, a2, a3, a4, a5, r0, r1, r2, r3, r4, r5] at hj1 hj2 ⊢ <;>
    first | exact absurd rfl hj1 | exact absurd rfl hj2 | assumption
  · intro v hv hvr i
    have h0 := hvr 0; have h1 := hvr 1; have h2 := hvr 2; have h3 := hvr 3; have h4 := hvr 4
    have h5 := hvr 5
    exfalso
    have r0 : rim06s 6 0 = 6 := rfl
    have r1 : rim06s 6 1 = 4 := rfl
    have r2 : rim06s 6 2 = 3 := rfl
    have r3 : rim06s 6 3 = 5 := rfl
    have r4 : rim06s 6 4 = 2 := rfl
    have r5 : rim06s 6 5 = 1 := rfl
    rw [r0] at h0; rw [r1] at h1; rw [r2] at h2; rw [r3] at h3; rw [r4] at h4; rw [r5] at h5
    clear hvr; fin_cases v <;> simp_all

/-- Transfer from the end `q` to the end `p` of the link edge: `x p = x q - u`. -/
theorem EdgeRimDet.transfer {k : ℕ} [NeZero k] {x : Fin 7 → ℝ³} {p q : Fin 7}
    {r6 r0 : ZMod k → Fin 7}
    (hr : ∀ i, i ≠ 0 → r0 i = r6 i) (h0 : r0 0 = p) (h6 : r6 0 = q)
    (h : EdgeRimDet x (x q - x p) p 1 k r6) : EdgeRimDet x (x q - x p) q (-1) k r0 := by
  obtain ⟨hk, -, -, hc, hrest⟩ := h
  have hs : ∀ i, ∃ s : ℝ, x (r0 i) = x (r6 i) + s • (x q - x p) := by
    intro i
    by_cases hi : i = 0
    · subst hi; rw [h0, h6]; exact ⟨-1, by module⟩
    · exact ⟨0, by rw [hr i hi]; simp⟩
  refine ⟨hk, by norm_num, ?_, ?_, ?_⟩
  · rw [h0]; module
  · intro i j hj1 hj2
    obtain ⟨s1, e1⟩ := hs (i + 1)
    obtain ⟨s2, e2⟩ := hs i
    obtain ⟨s3, e3⟩ := hs j
    rw [e1, e2, e3, det3_shift]
    exact hc i j hj1 hj2
  · intro v hv hvr i
    have hv0 : v ≠ p := by have := hvr 0; rwa [h0] at this
    have hv6 : ∀ j, v ≠ r6 j := by
      intro j
      by_cases hj : j = 0
      · subst hj; rw [h6]; exact hv
      · rw [← hr j hj]; exact hvr j
    obtain ⟨s1, e1⟩ := hs (i + 1)
    obtain ⟨s2, e2⟩ := hs i
    have : det3 (x (r0 (i + 1)) - x (r0 i)) (x v - x (r0 i)) (x q - x p) =
        det3 ((x (r6 (i + 1)) + s1 • (x q - x p)) - (x (r6 i) + s2 • (x q - x p)))
          ((x v + (0:ℝ) • (x q - x p)) - (x (r6 i) + s2 • (x q - x p))) (x q - x p) := by
      rw [e1, e2]; simp
    rw [this, det3_shift]
    exact hrest v hv0 hv6 i


/-- **Link edge `06`, determinant part of `EdgeRim` at the exact edge view.**  For the corner
`1` with positive frame (`det24 > 0`), the facets `0345`, `235`, `346` beyond those of `Type24`,
and outside the special position `235 ∥ 06`, one of the chains `(4,3,2)`, `(4,3,5,2)` gives both
closings `X = 6` and `X = 0`. -/
theorem edgeRimDet06 {x : Fin 7 → ℝ³} (T : Type24 x) (F0345 : Face16 x {0, 3, 4, 5})
    (F235 : Face16 x {2, 3, 5}) (F346 : Face16 x {3, 4, 6}) (hM : 0 < det24 x)
    (hsp : det3 (x 3 - x 2) (x 5 - x 2) (x 6 - x 0) ≠ 0) :
    (EdgeRimDet x (x 6 - x 0) 0 1 5 (rim06 6) ∧ EdgeRimDet x (x 6 - x 0) 6 (-1) 5 (rim06 0)) ∨
    (EdgeRimDet x (x 6 - x 0) 0 1 6 (rim06s 6) ∧ EdgeRimDet x (x 6 - x 0) 6 (-1) 6 (rim06s 0)) := by
  have hN : F235.N ≠ 0 := by
    intro h
    have e := Type24.f_eq_inner F235 1 2
    rw [h, F235.zero 2 (by decide)] at e
    have := F235.neg 1 (by decide)
    simp at e; linarith
  have hp : ⟪F235.N, x 3 - x 2⟫ = 0 := by
    rw [Type24.f_eq_inner F235 3 2, F235.zero 3 (by decide), F235.zero 2 (by decide)]; simp
  have hq : ⟪F235.N, x 5 - x 2⟫ = 0 := by
    rw [Type24.f_eq_inner F235 5 2, F235.zero 5 (by decide), F235.zero 2 (by decide)]; simp
  obtain ⟨κ, hκ⟩ := cross_par_of_orth (x 3 - x 2) (x 5 - x 2) F235.N hN
    (by rw [real_inner_comm]; exact hp) (by rw [real_inner_comm]; exact hq)
  have hd : det3 (x 3 - x 2) (x 5 - x 2) (x 6 - x 0) = κ * ⟪F235.N, x 6 - x 0⟫ := by
    rw [det3, hκ, real_inner_smul_left]
  have hs0 : ⟪F235.N, x 6 - x 0⟫ ≠ 0 := fun h => hsp (by rw [hd, h, mul_zero])
  rcases lt_or_gt_of_ne hs0 with hs | hs
  · left
    have hA := det06A T F0345 F235 F346 hM hs
    exact ⟨hA, EdgeRimDet.transfer (by decide) rfl rfl hA⟩
  · right
    have hB := det06B T F0345 F235 F346 hM hs
    exact ⟨hB, EdgeRimDet.transfer (by decide) rfl rfl hB⟩



/-! ### The covering triangle `026` (Lemma T for the link triangle) -/

/-- `C06 = X0(4) + X6(4) - 1` in the corner coordinates. -/
noncomputable def C06 (x : Fin 7 → ℝ³) : ℝ := oblX0 x 4 + oblX6 x 4 - 1

/-- `C26 = X2(3) + X6(3) - 1`. -/
noncomputable def C26 (x : Fin 7 → ℝ³) : ℝ := oblX2 x 3 + oblX6 x 3 - 1

/-- **Triangle cover** of the link triangle `026`: a direction `u` transversal to the plane
`026`, along which every other vertex projects into the open triangle. -/
def TCov (x : Fin 7 → ℝ³) : Prop :=
  ∃ u : ℝ³, det3 (x 2 - x 0) (x 6 - x 0) u ≠ 0 ∧
    ∀ v : Fin 7, v ≠ 0 → v ≠ 2 → v ≠ 6 →
      ∃ t α β γ : ℝ, 0 < α ∧ 0 < β ∧ 0 < γ ∧ α + β + γ = 1 ∧
        x v + t • u = α • x 0 + β • x 2 + γ • x 6

theorem tri_pt {x : Fin 7 → ℝ³} {v : Fin 7} {c0 c2 c6 d0 d2 d6 t : ℝ}
    (hx : x v = x 1 + c0 • (x 0 - x 1) + c2 • (x 2 - x 1) + c6 • (x 6 - x 1))
    (h0 : 0 < c0 + t * d0) (h2 : 0 < c2 + t * d2) (h6 : 0 < c6 + t * d6)
    (hs : (c0 + t * d0) + (c2 + t * d2) + (c6 + t * d6) = 1) :
    ∃ t α β γ : ℝ, 0 < α ∧ 0 < β ∧ 0 < γ ∧ α + β + γ = 1 ∧
      x v + t • (d0 • (x 0 - x 1) + d2 • (x 2 - x 1) + d6 • (x 6 - x 1)) =
        α • x 0 + β • x 2 + γ • x 6 := by
  refine ⟨t, c0 + t * d0, c2 + t * d2, c6 + t * d6, h0, h2, h6, hs, ?_⟩
  have key : x 1 = ((c0 + t * d0) + (c2 + t * d2) + (c6 + t * d6)) • x 1 := by
    rw [hs, one_smul]
  rw [hx]
  linear_combination (norm := module) key

theorem core_real {a b c δ : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hδ : 0 < δ)
    (hab : a + b ≤ 1) (h1 : δ * (a + b + c) ≤ a) (h2 : δ * (a + b + c) ≤ b) :
    0 < a + (1 - (a + b + c)) / (1 + 2 * δ) * δ ∧ 0 < b + (1 - (a + b + c)) / (1 + 2 * δ) * δ ∧
      0 < c + (1 - (a + b + c)) / (1 + 2 * δ) := by
  have hD : 0 < 1 + 2 * δ := by linarith
  have e : ∀ y : ℝ, y + (1 - (a + b + c)) / (1 + 2 * δ) * δ =
      (y * (1 + 2 * δ) + δ * (1 - (a + b + c))) / (1 + 2 * δ) := by
    intro y; field_simp
  refine ⟨?_, ?_, ?_⟩
  · rw [e]; apply div_pos _ hD; nlinarith
  · rw [e]; apply div_pos _ hD; nlinarith
  · have : c + (1 - (a + b + c)) / (1 + 2 * δ) =
        (2 * δ * c + (1 - a - b)) / (1 + 2 * δ) := by field_simp; ring
    rw [this]; apply div_pos _ hD; nlinarith

theorem transv {x : Fin 7 → ℝ³} (T : Type24 x) {d0 d2 d6 : ℝ} (h : d0 + d2 + d6 ≠ 0) :
    det3 (x 2 - x 0) (x 6 - x 0) (d0 • (x 0 - x 1) + d2 • (x 2 - x 1) + d6 • (x 6 - x 1)) ≠ 0 := by
  have e1 : x 2 - x 0 = (-1:ℝ) • (x 0 - x 1) + (1:ℝ) • (x 2 - x 1) + (0:ℝ) • (x 6 - x 1) := by
    module
  have e2 : x 6 - x 0 = (-1:ℝ) • (x 0 - x 1) + (0:ℝ) • (x 2 - x 1) + (1:ℝ) • (x 6 - x 1) := by
    module
  rw [e1, e2, det3_comb]
  have : det24 x = vol3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) := rfl
  rw [← this]
  have hd := T.det_ne
  intro hz
  rcases mul_eq_zero.mp hz with hz | hz
  · apply h; linarith
  · exact hd hz

theorem aux345 : ∀ v : Fin 7, v ∈ ({3, 4, 5} : Finset (Fin 7)) →
    v ∉ ({1, 2, 6} : Finset (Fin 7)) ∧ v ∉ ({0, 1, 6} : Finset (Fin 7)) ∧
      v ∉ ({0, 1, 2} : Finset (Fin 7)) := by decide

theorem aux34 : ∀ v : Fin 7, v ∈ ({3, 4, 5} : Finset (Fin 7)) → v ≠ 4 →
    v ∉ ({0, 4, 6} : Finset (Fin 7)) := by decide

theorem aux1 : ∀ v : Fin 7, v ≠ 0 → v ≠ 2 → v ≠ 6 → v = 1 ∨ v = 3 ∨ v = 4 ∨ v = 5 := by decide

theorem tcov026_of_C06 {x : Fin 7 → ℝ³} (T : Type24 x) (h : C06 x ≤ 0) : TCov x := by
  have X0p : ∀ v : Fin 7, v ∉ ({1, 2, 6} : Finset (Fin 7)) → 0 < oblX0 x v := fun v hv => T.X0_pos hv
  have X2p : ∀ v : Fin 7, v ∉ ({0, 1, 6} : Finset (Fin 7)) → 0 < oblX2 x v := fun v hv => T.X2_pos hv
  have X6p : ∀ v : Fin 7, v ∉ ({0, 1, 2} : Finset (Fin 7)) → 0 < oblX6 x v := fun v hv => T.X6_pos hv
  have w4 : 0 < oblX2 x 4 := X2p 4 (by decide)
  have om : omega4 x ≤ 0 := div_nonpos_of_nonpos_of_nonneg h w4.le
  have sg : ∀ v : Fin 7, v ∈ ({3, 4, 5} : Finset (Fin 7)) → oblX0 x v + oblX6 x v ≤ 1 := by
    intro v hv
    by_cases h4 : v = 4
    · subst h4; unfold C06 at h; linarith
    · have l := T.lt046 (v := v) (aux34 v hv h4)
      have := X2p v (aux345 v hv).2.1
      nlinarith [mul_nonneg (neg_nonneg.mpr om) this.le]
  -- small δ
  set S3 := oblX0 x 3 + oblX2 x 3 + oblX6 x 3 with hS3
  set S4 := oblX0 x 4 + oblX2 x 4 + oblX6 x 4 with hS4
  set S5 := oblX0 x 5 + oblX2 x 5 + oblX6 x 5 with hS5
  have p30 := X0p 3 (by decide); have p32 := X2p 3 (by decide); have p36 := X6p 3 (by decide)
  have p40 := X0p 4 (by decide); have p42 := X2p 4 (by decide); have p46 := X6p 4 (by decide)
  have p50 := X0p 5 (by decide); have p52 := X2p 5 (by decide); have p56 := X6p 5 (by decide)
  set m := min (min (min (oblX0 x 3) (oblX6 x 3)) (min (oblX0 x 4) (oblX6 x 4)))
    (min (oblX0 x 5) (oblX6 x 5)) with hm
  have hmpos : 0 < m := by
    rw [hm]; exact lt_min (lt_min (lt_min p30 p36) (lt_min p40 p46)) (lt_min p50 p56)
  have m30 : m ≤ oblX0 x 3 := by rw [hm]; exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have m36 : m ≤ oblX6 x 3 := by rw [hm]; exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have m40 : m ≤ oblX0 x 4 := by rw [hm]; exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have m46 : m ≤ oblX6 x 4 := by rw [hm]; exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have m50 : m ≤ oblX0 x 5 := by rw [hm]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have m56 : m ≤ oblX6 x 5 := by rw [hm]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hSpos : 0 < 1 + S3 + S4 + S5 := by
    have : 0 < S3 := by rw [hS3]; linarith
    have : 0 < S4 := by rw [hS4]; linarith
    have : 0 < S5 := by rw [hS5]; linarith
    linarith
  set δ := m / (1 + S3 + S4 + S5) with hδ
  have hδp : 0 < δ := div_pos hmpos hSpos
  have hδS : ∀ S : ℝ, 0 < S → S ≤ 1 + S3 + S4 + S5 → δ * S ≤ m := by
    intro S hS hle
    rw [hδ, div_mul_eq_mul_div, div_le_iff₀ hSpos]
    nlinarith
  refine ⟨(δ : ℝ) • (x 0 - x 1) + (1 : ℝ) • (x 2 - x 1) + δ • (x 6 - x 1), ?_, ?_⟩
  · have := transv T (d0 := δ) (d2 := 1) (d6 := δ) (by linarith)
    simpa using this
  · intro v h0 h2 h6
    have hv : v = 1 ∨ v = 3 ∨ v = 4 ∨ v = 5 := aux1 v h0 h2 h6
    have gen : ∀ w : Fin 7, w ∈ ({3, 4, 5} : Finset (Fin 7)) →
        δ * (oblX0 x w + oblX6 x w + oblX2 x w) ≤ oblX0 x w →
        δ * (oblX0 x w + oblX6 x w + oblX2 x w) ≤ oblX6 x w →
        ∃ t α β γ : ℝ, 0 < α ∧ 0 < β ∧ 0 < γ ∧ α + β + γ = 1 ∧
          x w + t • ((δ : ℝ) • (x 0 - x 1) + (1 : ℝ) • (x 2 - x 1) + δ • (x 6 - x 1)) =
            α • x 0 + β • x 2 + γ • x 6 := by
      intro w hw k1 k2
      have a0 := X0p w (aux345 w hw).1
      have a2 := X2p w (aux345 w hw).2.1
      have a6 := X6p w (aux345 w hw).2.2
      obtain ⟨c1, c2, c3⟩ := core_real a0 a6 a2 hδp (sg w hw) k1 k2
      refine tri_pt (T.rep w) (t := (1 - (oblX0 x w + oblX6 x w + oblX2 x w)) / (1 + 2 * δ))
        (d0 := δ) (d2 := 1) (d6 := δ) c1 (by simpa using c3) c2 ?_
      field_simp; ring
    rcases hv with rfl | rfl | rfl | rfl
    · refine tri_pt (c0 := 0) (c2 := 0) (c6 := 0) (t := 1 / (1 + 2 * δ)) (d0 := δ) (d2 := 1)
        (d6 := δ) (by simp) (by positivity) (by positivity) (by positivity) ?_
      field_simp; ring
    · exact gen 3 (by decide) (by nlinarith [hδS (oblX0 x 3 + oblX6 x 3 + oblX2 x 3) (by linarith) (by linarith [hS3]), m30]) (by nlinarith [hδS (oblX0 x 3 + oblX6 x 3 + oblX2 x 3) (by linarith) (by linarith [hS3]), m36])
    · exact gen 4 (by decide) (by nlinarith [hδS (oblX0 x 4 + oblX6 x 4 + oblX2 x 4) (by linarith) (by linarith [hS4]), m40]) (by nlinarith [hδS (oblX0 x 4 + oblX6 x 4 + oblX2 x 4) (by linarith) (by linarith [hS4]), m46])
    · exact gen 5 (by decide) (by nlinarith [hδS (oblX0 x 5 + oblX6 x 5 + oblX2 x 5) (by linarith) (by linarith [hS5]), m50]) (by nlinarith [hδS (oblX0 x 5 + oblX6 x 5 + oblX2 x 5) (by linarith) (by linarith [hS5]), m56])

theorem aux33 : ∀ v : Fin 7, v ∈ ({3, 4, 5} : Finset (Fin 7)) → v ≠ 3 →
    v ∉ ({2, 3, 6} : Finset (Fin 7)) := by decide

theorem tcov026_of_C26 {x : Fin 7 → ℝ³} (T : Type24 x) (h : C26 x ≤ 0) : TCov x := by
  have X0p : ∀ v : Fin 7, v ∉ ({1, 2, 6} : Finset (Fin 7)) → 0 < oblX0 x v := fun v hv => T.X0_pos hv
  have X2p : ∀ v : Fin 7, v ∉ ({0, 1, 6} : Finset (Fin 7)) → 0 < oblX2 x v := fun v hv => T.X2_pos hv
  have X6p : ∀ v : Fin 7, v ∉ ({0, 1, 2} : Finset (Fin 7)) → 0 < oblX6 x v := fun v hv => T.X6_pos hv
  have w4 : 0 < oblX0 x 3 := X0p 3 (by decide)
  have om : omega3 x ≤ 0 := div_nonpos_of_nonpos_of_nonneg h w4.le
  have sg : ∀ v : Fin 7, v ∈ ({3, 4, 5} : Finset (Fin 7)) → oblX2 x v + oblX6 x v ≤ 1 := by
    intro v hv
    by_cases h4 : v = 3
    · subst h4; unfold C26 at h; linarith
    · have l := T.lt236 (v := v) (aux33 v hv h4)
      have := X0p v (aux345 v hv).1
      nlinarith [mul_nonneg (neg_nonneg.mpr om) this.le]
  -- small δ
  set S3 := oblX0 x 3 + oblX2 x 3 + oblX6 x 3 with hS3
  set S4 := oblX0 x 4 + oblX2 x 4 + oblX6 x 4 with hS4
  set S5 := oblX0 x 5 + oblX2 x 5 + oblX6 x 5 with hS5
  have p30 := X0p 3 (by decide); have p32 := X2p 3 (by decide); have p36 := X6p 3 (by decide)
  have p40 := X0p 4 (by decide); have p42 := X2p 4 (by decide); have p46 := X6p 4 (by decide)
  have p50 := X0p 5 (by decide); have p52 := X2p 5 (by decide); have p56 := X6p 5 (by decide)
  set m := min (min (min (oblX2 x 3) (oblX6 x 3)) (min (oblX2 x 4) (oblX6 x 4)))
    (min (oblX2 x 5) (oblX6 x 5)) with hm
  have hmpos : 0 < m := by
    rw [hm]; exact lt_min (lt_min (lt_min p32 p36) (lt_min p42 p46)) (lt_min p52 p56)
  have m32 : m ≤ oblX2 x 3 := by rw [hm]; exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have m36 : m ≤ oblX6 x 3 := by rw [hm]; exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have m42 : m ≤ oblX2 x 4 := by rw [hm]; exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have m46 : m ≤ oblX6 x 4 := by rw [hm]; exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have m52 : m ≤ oblX2 x 5 := by rw [hm]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have m56 : m ≤ oblX6 x 5 := by rw [hm]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hSpos : 0 < 1 + S3 + S4 + S5 := by
    have : 0 < S3 := by rw [hS3]; linarith
    have : 0 < S4 := by rw [hS4]; linarith
    have : 0 < S5 := by rw [hS5]; linarith
    linarith
  set δ := m / (1 + S3 + S4 + S5) with hδ
  have hδp : 0 < δ := div_pos hmpos hSpos
  have hδS : ∀ S : ℝ, 0 < S → S ≤ 1 + S3 + S4 + S5 → δ * S ≤ m := by
    intro S hS hle
    rw [hδ, div_mul_eq_mul_div, div_le_iff₀ hSpos]
    nlinarith
  refine ⟨(1 : ℝ) • (x 0 - x 1) + (δ : ℝ) • (x 2 - x 1) + δ • (x 6 - x 1), ?_, ?_⟩
  · have := transv T (d0 := 1) (d2 := δ) (d6 := δ) (by linarith)
    simpa using this
  · intro v h0 h2 h6
    have hv : v = 1 ∨ v = 3 ∨ v = 4 ∨ v = 5 := aux1 v h0 h2 h6
    have gen : ∀ w : Fin 7, w ∈ ({3, 4, 5} : Finset (Fin 7)) →
        δ * (oblX2 x w + oblX6 x w + oblX0 x w) ≤ oblX2 x w →
        δ * (oblX2 x w + oblX6 x w + oblX0 x w) ≤ oblX6 x w →
        ∃ t α β γ : ℝ, 0 < α ∧ 0 < β ∧ 0 < γ ∧ α + β + γ = 1 ∧
          x w + t • ((1 : ℝ) • (x 0 - x 1) + (δ : ℝ) • (x 2 - x 1) + δ • (x 6 - x 1)) =
            α • x 0 + β • x 2 + γ • x 6 := by
      intro w hw k1 k2
      have a0 := X0p w (aux345 w hw).1
      have a2 := X2p w (aux345 w hw).2.1
      have a6 := X6p w (aux345 w hw).2.2
      obtain ⟨c1, c2, c3⟩ := core_real a2 a6 a0 hδp (sg w hw) k1 k2
      refine tri_pt (T.rep w) (t := (1 - (oblX2 x w + oblX6 x w + oblX0 x w)) / (1 + 2 * δ))
        (d0 := 1) (d2 := δ) (d6 := δ) (by simpa using c3) c1 c2 ?_
      field_simp; ring
    rcases hv with rfl | rfl | rfl | rfl
    · refine tri_pt (c0 := 0) (c2 := 0) (c6 := 0) (t := 1 / (1 + 2 * δ)) (d0 := 1) (d2 := δ)
        (d6 := δ) (by simp) (by positivity) (by positivity) (by positivity) ?_
      field_simp; ring
    · exact gen 3 (by decide) (by nlinarith [hδS (oblX0 x 3 + oblX6 x 3 + oblX2 x 3) (by linarith) (by linarith [hS3]), m32]) (by nlinarith [hδS (oblX0 x 3 + oblX6 x 3 + oblX2 x 3) (by linarith) (by linarith [hS3]), m36])
    · exact gen 4 (by decide) (by nlinarith [hδS (oblX0 x 4 + oblX6 x 4 + oblX2 x 4) (by linarith) (by linarith [hS4]), m42]) (by nlinarith [hδS (oblX0 x 4 + oblX6 x 4 + oblX2 x 4) (by linarith) (by linarith [hS4]), m46])
    · exact gen 5 (by decide) (by nlinarith [hδS (oblX0 x 5 + oblX6 x 5 + oblX2 x 5) (by linarith) (by linarith [hS5]), m52]) (by nlinarith [hδS (oblX0 x 5 + oblX6 x 5 + oblX2 x 5) (by linarith) (by linarith [hS5]), m56])


end Link24R
end Minimality
