module

public import Minimality.TripleTieAdjacent
public import Minimality.ParDichotomy

@[expose] public section

/-!
# No rectangle of two vertical far edges at two quadrilaterals of types 07 and 14

(`FEWER-FACES-PROOFS.md` Proposition 24.12 and Theorem 24.5 (a).)  The residual position
`Minimality.QuadTripleRect` of two quadrilaterals `Q1 = {v, P, a1, a2}`, `Q2 = {v, Q, b1, b2}`
(`P`, `Q` opposite `v`): a rectangle of two vertical far edges `a a'` (of `Q1`) and `b b'` (of `Q2`)
with `a`, `b` at the depth of `v` and every vertex on one side of it.  In the frame `(a - v, b - v,
e)` (`Minimality.TieFrame`) the points of `Q1` are `v + x (a - v) + t e`, those of `Q2` are
`v + y (b - v) + t e`, and:

* `sideF`: the other far corner `a'` is the opposite vertex `P` (the facets through `v` and its
  neighbours, and the edge facets at `P`), so `a` is a neighbour of `v`; likewise `b' = Q`;
* `coreF`: for each of the four choices of the neighbours `a`, `b` one facet (`KillP`) refutes the
  rectangle: a facet through three corners of the parallelogram `a a' b' b` (`par_frame`), or a
  facet through `v`, `b` and the remaining point of `Q1` (`vb_frame`), or the symmetric one.
* `quadTripleRect_false`: assembles these for a general quadrilateral pair; the types 07 and 14
  are instances (`Minimality.not_quadTripleRect_type07`, `…type14`).
-/

namespace Minimality

open Finset
open scoped RealInnerProductSpace

theorem bad1_real {x c t A1 D1 A2 D2 σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hc : 0 < σ * c)
    (ht : 0 ≤ σ * t) (hx : 0 < x) (h1a : A1 + c * D1 = 0) (hA1 : A1 < 0)
    (h1m : x * A1 + t * D1 < 0) (h2m : x * A2 + t * D2 = 0) (hA2 : A2 < 0)
    (h2a : A2 + c * D2 < 0) : False := by
  have hs : 0 ≤ t * c := by
    have : t * c = (σ * t) * (σ * c) := by rcases hσ with rfl | rfl <;> ring
    rw [this]; exact mul_nonneg ht hc.le
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc
  have hgD : 0 < c * D1 := by linarith
  have k1 : t * c < x * c ^ 2 := by
    have e1 : x * A1 + t * D1 = D1 * (t - x * c) := by
      have : A1 = -(c * D1) := by linarith
      rw [this]; ring
    rw [e1] at h1m
    have : (c * D1) * ((t - x * c) * c) < 0 := by
      have e : (c * D1) * ((t - x * c) * c) = (D1 * (t - x * c)) * c ^ 2 := by ring
      rw [e]; exact mul_neg_of_neg_of_pos h1m (by positivity)
    have hh : (t - x * c) * c < 0 := by
      by_contra hn; push Not at hn; nlinarith [mul_nonneg hgD.le hn]
    nlinarith
  have htD : 0 < t * D2 := by nlinarith
  have ht0 : t ≠ 0 := by rintro rfl; simp at htD
  have hs0 : 0 < t * c := lt_of_le_of_ne hs (fun h => by
    rcases mul_eq_zero.mp h.symm with h | h <;> contradiction)
  have k2 : (A2 + c * D2) * (t * c) < 0 := mul_neg_of_neg_of_pos h2a hs0
  have e2 : (A2 + c * D2) * (t * c) = A2 * (t * c - c ^ 2 * x) := by
    have : t * D2 = -(x * A2) := by linarith
    calc (A2 + c * D2) * (t * c) = A2 * (t * c) + c ^ 2 * (t * D2) := by ring
      _ = _ := by rw [this]; ring
  rw [e2] at k2
  have : 0 < t * c - c ^ 2 * x := by
    by_contra hn; push Not at hn; nlinarith [mul_nonneg_of_nonpos_of_nonpos hA2.le hn]
  nlinarith

theorem bad2_real {x c t A D φ0 σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hc : 0 < σ * c)
    (ht : 0 ≤ σ * t) (hx : x ≤ 1) (hφ0 : φ0 < 0) (ha : φ0 + A = 0)
    (ha' : φ0 + A + c * D < 0) (hm : φ0 + x * A + t * D = 0) : x = 1 ∧ t = 0 := by
  have hs : 0 ≤ t * c := by
    have : t * c = (σ * t) * (σ * c) := by rcases hσ with rfl | rfl <;> ring
    rw [this]; exact mul_nonneg ht hc.le
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc
  have hA : 0 < A := by linarith
  have hcD : c * D < 0 := by linarith
  have hD : D ≠ 0 := by rintro rfl; simp at hcD
  have htD : t * D = (1 - x) * A := by linarith
  have h1 : 0 ≤ t * D := by rw [htD]; exact mul_nonneg (by linarith) hA.le
  have h2 : (t * D) * (c * D) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h1 hcD.le
  have h3 : (t * c) * D ^ 2 ≤ 0 := by nlinarith
  have hD2 : 0 < D ^ 2 := by positivity
  have h4 : t * c = 0 := by nlinarith
  have ht0 : t = 0 := by
    rcases mul_eq_zero.mp h4 with h | h
    · exact h
    · exact absurd h hc0
  refine ⟨?_, ht0⟩
  rw [ht0, zero_mul] at htD
  have : (1 - x) * A = 0 := htD.symm
  rcases mul_eq_zero.mp this with h | h
  · linarith
  · linarith

theorem vb_real {x c t A D σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hc : 0 < σ * c)
    (ht : 0 ≤ σ * t) (hx : 0 < x) (hA : A < 0) (hm : x * A + t * D = 0) (hb : c * D < 0) :
    False := by
  have hs : 0 ≤ t * c := by
    have : t * c = (σ * t) * (σ * c) := by rcases hσ with rfl | rfl <;> ring
    rw [this]; exact mul_nonneg ht hc.le
  have h1 : 0 < t * D := by nlinarith
  have h2 : (t * D) * (c * D) < 0 := mul_neg_of_pos_of_neg h1 hb
  nlinarith [sq_nonneg D, mul_nonneg hs (sq_nonneg D)]

theorem sig_pos {σ d ee : ℝ} (hee : 0 < ee) (hd : 0 < σ * d) :
    0 < σ * (d / ee) := by
  rw [← mul_div_assoc]; exact div_pos hd hee

theorem sig_nonneg {σ d ee : ℝ} (hee : 0 < ee) (hd : 0 ≤ σ * d) : 0 ≤ σ * (d / ee) := by
  rw [← mul_div_assoc]; exact div_nonneg hd hee.le

theorem sig_pos_of_ne {σ d : ℝ} (hσ : σ = 1 ∨ σ = -1) (h0 : 0 ≤ σ * d) (hne : d ≠ 0) :
    0 < σ * d := by
  rcases lt_or_eq_of_le h0 with h | h
  · exact h
  · exfalso; apply hne
    have : σ * d = 0 := h.symm
    rcases mul_eq_zero.mp this with h | h
    · rcases hσ with rfl | rfl <;> norm_num at h
    · exact h

/-- Coordinates of a point of the plane `f1 = 0` in the frame, for a functional vanishing at
`v`. -/
theorem TieFrame.on1 {f1 f2 : ℝ³ →ᵃ[ℝ] ℝ} {v a b e : ℝ³} (F : TieFrame f1 f2 v a b e) {y : ℝ³}
    (hy : f1 y = 0) (φ : ℝ³ →ᵃ[ℝ] ℝ) :
    φ y = φ v + f2 y / f2 a * (φ a - φ v) +
      (⟪y, e⟫ - ⟪v, e⟫) / ⟪e, e⟫ * (φ (v + e) - φ v) := by
  have := F.aff φ y
  rw [hy, zero_div, zero_mul, add_zero] at this
  exact this

theorem TieFrame.on2 {f1 f2 : ℝ³ →ᵃ[ℝ] ℝ} {v a b e : ℝ³} (F : TieFrame f1 f2 v a b e) {y : ℝ³}
    (hy : f2 y = 0) (φ : ℝ³ →ᵃ[ℝ] ℝ) :
    φ y = φ v + f1 y / f1 b * (φ b - φ v) +
      (⟪y, e⟫ - ⟪v, e⟫) / ⟪e, e⟫ * (φ (v + e) - φ v) := by
  have := F.aff φ y
  rw [hy, zero_div, zero_mul, add_zero] at this
  exact this

theorem TieFrame.shiftA {f1 f2 : ℝ³ →ᵃ[ℝ] ℝ} {v a b e : ℝ³} (F : TieFrame f1 f2 v a b e)
    {y : ℝ³} (h1 : f1 y = 0) (h2 : f2 y = f2 a) :
    y = a + ((⟪y, e⟫ - ⟪v, e⟫) / ⟪e, e⟫) • e := by
  have hd := F.decomp y
  have hne : f2 a ≠ 0 := F.hp2.ne
  rw [h1, h2, zero_div, div_self hne, zero_smul, one_smul] at hd
  conv_lhs => rw [hd]
  abel

theorem TieFrame.shiftB {f1 f2 : ℝ³ →ᵃ[ℝ] ℝ} {v a b e : ℝ³} (F : TieFrame f1 f2 v a b e)
    {y : ℝ³} (h2 : f2 y = 0) (h1 : f1 y = f1 b) :
    y = b + ((⟪y, e⟫ - ⟪v, e⟫) / ⟪e, e⟫) • e := by
  have hd := F.decomp y
  have hne : f1 b ≠ 0 := F.hq1.ne
  rw [h1, h2, zero_div, div_self hne, zero_smul, one_smul] at hd
  conv_lhs => rw [hd]
  abel

/-- Frame: a facet through `v`, `b` and a point `m` of `f1 = 0` (negative at `a` and at a point
`b'` of `f2 = 0` tied with the far depth `b`) is impossible when `m` is on the near side. -/
theorem vb_frame {f1 f2 : ℝ³ →ᵃ[ℝ] ℝ} {v a b e : ℝ³} (F : TieFrame f1 f2 v a b e)
    {m b' : ℝ³} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hm1 : f1 m = 0) (hmn : f2 m < 0)
    (sm : 0 ≤ σ * (⟪m, e⟫ - ⟪v, e⟫)) (hb'2 : f2 b' = 0) (hfb' : f1 b' = f1 b)
    (sb : 0 < σ * (⟪b', e⟫ - ⟪v, e⟫)) {φ : ℝ³ →ᵃ[ℝ] ℝ} (hv : φ v = 0) (hb : φ b = 0)
    (hmφ : φ m = 0) (ha : φ a < 0) (hb'φ : φ b' < 0) : False := by
  have hee : 0 < ⟪e, e⟫ := real_inner_self_pos.mpr F.he
  have M := F.on1 hm1 φ
  have B := F.on2 hb'2 φ
  rw [hmφ, hv] at M
  rw [hfb', div_self F.hq1.ne, hv, hb] at B
  exact vb_real (D := φ (v + e)) hσ (sig_pos hee sb) (sig_nonneg hee sm)
    (div_pos_of_neg_of_neg hmn F.hp2) ha (by linarith) (by linarith)

/-- Frame: parallelogram `a, a', b, b'` (both far edges vertical, tied crosswise) lies in no
facet through three of its corners. -/
theorem par_frame {f1 f2 : ℝ³ →ᵃ[ℝ] ℝ} {v a b e : ℝ³} (F : TieFrame f1 f2 v a b e)
    {a' b' : ℝ³} (ha'1 : f1 a' = 0) (hfa' : f2 a' = f2 a) (hb'2 : f2 b' = 0)
    (hfb' : f1 b' = f1 b) (htie : ⟪a', e⟫ = ⟪b', e⟫) {φ : ℝ³ →ᵃ[ℝ] ℝ} (h1 : φ a = 0)
    (h2 : φ b = 0) (h3 : φ b' = 0) (h4 : φ a' < 0) : False := by
  have sA := F.shiftA ha'1 hfa'
  have sB := F.shiftB hb'2 hfb'
  rw [← htie] at sB
  obtain ⟨n, hn⟩ := aff_grad φ
  have hd : a' - a = b' - b := by
    rw [sA, sB]; abel_nf
  have := hn a a'
  have := hn b b'
  rw [hd] at *
  linarith

theorem bad1_frame {f1 f2 : ℝ³ →ᵃ[ℝ] ℝ} {v a b e : ℝ³} (F : TieFrame f1 f2 v a b e)
    {a' m : ℝ³} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (ha'1 : f1 a' = 0) (hfa' : f2 a' = f2 a)
    (hm1 : f1 m = 0) (hmn : f2 m < 0) (sa : 0 < σ * (⟪a', e⟫ - ⟪v, e⟫))
    (sm : 0 ≤ σ * (⟪m, e⟫ - ⟪v, e⟫)) {φ1 φ2 : ℝ³ →ᵃ[ℝ] ℝ} (h1v : φ1 v = 0) (h1a' : φ1 a' = 0)
    (h1a : φ1 a < 0) (h1m : φ1 m < 0) (h2v : φ2 v = 0) (h2m : φ2 m = 0) (h2a : φ2 a < 0)
    (h2a' : φ2 a' < 0) : False := by
  have hee : 0 < ⟪e, e⟫ := real_inner_self_pos.mpr F.he
  have A1 := F.on1 ha'1 φ1
  have M1 := F.on1 hm1 φ1
  have M2 := F.on1 hm1 φ2
  have A2 := F.on1 ha'1 φ2
  rw [hfa', div_self F.hp2.ne, h1v, h1a'] at A1
  rw [h1v] at M1
  rw [h2v, h2m] at M2
  rw [hfa', div_self F.hp2.ne, h2v] at A2
  exact bad1_real (D1 := φ1 (v + e)) (D2 := φ2 (v + e)) hσ (sig_pos hee sa) (sig_nonneg hee sm)
    (div_pos_of_neg_of_neg hmn F.hp2) (by linarith) h1a (by linarith) (by linarith) h2a
    (by linarith)

theorem bad2_frame {f1 f2 : ℝ³ →ᵃ[ℝ] ℝ} {v a b e : ℝ³} (F : TieFrame f1 f2 v a b e)
    {a' m : ℝ³} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (ha'1 : f1 a' = 0) (hfa' : f2 a' = f2 a)
    (hm1 : f1 m = 0) (hmx : f2 a ≤ f2 m) (sa : 0 < σ * (⟪a', e⟫ - ⟪v, e⟫))
    (sm : 0 ≤ σ * (⟪m, e⟫ - ⟪v, e⟫)) {φ : ℝ³ →ᵃ[ℝ] ℝ} (hv : φ v < 0) (ha : φ a = 0)
    (hm : φ m = 0) (ha' : φ a' < 0) : m = a := by
  have hee : 0 < ⟪e, e⟫ := real_inner_self_pos.mpr F.he
  have A := F.on1 ha'1 φ
  have M := F.on1 hm1 φ
  rw [hfa', div_self F.hp2.ne] at A
  obtain ⟨h1, h2⟩ := bad2_real (x := f2 m / f2 a) (t := (⟪m, e⟫ - ⟪v, e⟫) / ⟪e, e⟫)
    (A := φ a - φ v) (D := φ (v + e) - φ v) (φ0 := φ v) hσ (sig_pos hee sa) (sig_nonneg hee sm)
    ((div_le_one_of_neg F.hp2).mpr hmx) hv (by linarith) (by linarith) (by linarith)
  have hd := F.decomp m
  rw [h1, hm1, zero_div, h2, zero_smul, zero_smul] at hd
  simp at hd
  exact hd

/-- **The far pair of a quadrilateral contains the opposite vertex.**  `Q1 = {v, P, a1, a2}` has
`P` opposite `v`; two minimizers `a`, `a'` of `f2` on `Q1` at different depths, `a` at the depth of
`v`, with `Q1` one-sided, are such that `a'` is `P` (and `a` a neighbour of `v`). -/
theorem sideF {f1 f2 : ℝ³ →ᵃ[ℝ] ℝ} {v a b e : ℝ³} (F : TieFrame f1 f2 v a b e)
    {P a1 a2 a' : ℝ³} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hP1 : f1 P = 0) (ha11 : f1 a1 = 0) (ha21 : f1 a2 = 0)
    (hPn : f2 P < 0) (ha1n : f2 a1 < 0) (ha2n : f2 a2 < 0)
    (ha : a = P ∨ a = a1 ∨ a = a2) (ha' : a' = P ∨ a' = a1 ∨ a' = a2)
    (hmP : f2 a ≤ f2 P) (hm1 : f2 a ≤ f2 a1) (hm2 : f2 a ≤ f2 a2) (hfa' : f2 a' = f2 a)
    (hne : ⟪a', e⟫ ≠ ⟪v, e⟫) (sa' : 0 ≤ σ * (⟪a', e⟫ - ⟪v, e⟫))
    (sP : 0 ≤ σ * (⟪P, e⟫ - ⟪v, e⟫)) (s1 : 0 ≤ σ * (⟪a1, e⟫ - ⟪v, e⟫))
    (s2 : 0 ≤ σ * (⟪a2, e⟫ - ⟪v, e⟫)) (hPa1 : P ≠ a1) (hPa2 : P ≠ a2)
    (Ta1 : ∃ φ : ℝ³ →ᵃ[ℝ] ℝ, φ v = 0 ∧ φ a1 = 0 ∧ φ P < 0 ∧ φ a2 < 0)
    (Ta2 : ∃ φ : ℝ³ →ᵃ[ℝ] ℝ, φ v = 0 ∧ φ a2 = 0 ∧ φ P < 0 ∧ φ a1 < 0)
    (E1 : ∃ φ : ℝ³ →ᵃ[ℝ] ℝ, φ P = 0 ∧ φ a1 = 0 ∧ φ v < 0 ∧ φ a2 < 0)
    (E2 : ∃ φ : ℝ³ →ᵃ[ℝ] ℝ, φ P = 0 ∧ φ a2 = 0 ∧ φ v < 0 ∧ φ a1 < 0) :
    a' = P ∧ (a = a1 ∨ a = a2) := by
  have hee : 0 < ⟪e, e⟫ := real_inner_self_pos.mpr F.he
  have spos : 0 < σ * (⟪a', e⟫ - ⟪v, e⟫) :=
    sig_pos_of_ne hσ sa' (fun h => hne (by linarith))
  have notsame : ∀ y, a' = y → a = y → False := fun y h1 h2 => hne (by
    rw [h1, ← h2]; exact F.tp)
  obtain ⟨φ1, h1v, h1a1, h1P, h1a2⟩ := Ta1
  obtain ⟨φ2, h2v, h2a2, h2P, h2a1⟩ := Ta2
  obtain ⟨ψ1, k1P, k1a1, k1v, k1a2⟩ := E1
  obtain ⟨ψ2, k2P, k2a2, k2v, k2a1⟩ := E2
  rcases ha with rfl | rfl | rfl <;> rcases ha' with rfl | rfl | rfl
  · exact (notsame _ rfl rfl).elim
  · exact (bad1_frame F hσ ha11 hfa' ha21 ha2n spos s2 h1v h1a1 h1P h1a2 h2v h2a2 h2P h2a1).elim
  · exact (bad1_frame F hσ ha21 hfa' ha11 ha1n spos s1 h2v h2a2 h2P h2a1 h1v h1a1 h1P h1a2).elim
  · exact ⟨rfl, Or.inl rfl⟩
  · exact (notsame _ rfl rfl).elim
  · exact (hPa1 (bad2_frame F hσ ha21 hfa' hP1 hmP spos sP k1v k1a1 k1P k1a2)).elim
  · exact ⟨rfl, Or.inr rfl⟩
  · exact (hPa2 (bad2_frame F hσ ha11 hfa' hP1 hmP spos sP k2v k2a2 k2P k2a1)).elim
  · exact (notsame _ rfl rfl).elim

/-- The four kinds of facet that refute a rectangle with far corners `a, a'` (of `Q1`) and
`b, b'` (of `Q2`) and the other points `m1`, `m2` of the two faces. -/
def KillP (v a a' m1 b b' m2 : ℝ³) : Prop :=
  (∃ φ : ℝ³ →ᵃ[ℝ] ℝ, φ a = 0 ∧ φ b = 0 ∧ φ b' = 0 ∧ φ a' < 0) ∨
  (∃ φ : ℝ³ →ᵃ[ℝ] ℝ, φ a = 0 ∧ φ a' = 0 ∧ φ b = 0 ∧ φ b' < 0) ∨
  (∃ φ : ℝ³ →ᵃ[ℝ] ℝ, φ v = 0 ∧ φ b = 0 ∧ φ m1 = 0 ∧ φ a < 0 ∧ φ b' < 0) ∨
  (∃ φ : ℝ³ →ᵃ[ℝ] ℝ, φ v = 0 ∧ φ a = 0 ∧ φ m2 = 0 ∧ φ b < 0 ∧ φ a' < 0)

theorem coreF {f1 f2 : ℝ³ →ᵃ[ℝ] ℝ} {v a b e : ℝ³} (F : TieFrame f1 f2 v a b e)
    {a' b' m1 m2 : ℝ³} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (ha'1 : f1 a' = 0) (hfa' : f2 a' = f2 a) (hb'2 : f2 b' = 0) (hfb' : f1 b' = f1 b)
    (hm11 : f1 m1 = 0) (hm1n : f2 m1 < 0) (hm22 : f2 m2 = 0) (hm2n : f1 m2 < 0)
    (htie : ⟪a', e⟫ = ⟪b', e⟫) (sa : 0 < σ * (⟪a', e⟫ - ⟪v, e⟫))
    (sm1 : 0 ≤ σ * (⟪m1, e⟫ - ⟪v, e⟫)) (sm2 : 0 ≤ σ * (⟪m2, e⟫ - ⟪v, e⟫))
    (K : KillP v a a' m1 b b' m2) : False := by
  have sb : 0 < σ * (⟪b', e⟫ - ⟪v, e⟫) := by rw [← htie]; exact sa
  rcases K with ⟨φ, h1, h2, h3, h4⟩ | ⟨φ, h1, h2, h3, h4⟩ | ⟨φ, h1, h2, h3, h4, h5⟩ |
      ⟨φ, h1, h2, h3, h4, h5⟩
  · exact par_frame F ha'1 hfa' hb'2 hfb' htie h1 h2 h3 h4
  · exact par_frame F.swap hb'2 hfb' ha'1 hfa' htie.symm h3 h1 h2 h4
  · exact vb_frame F hσ hm11 hm1n sm1 hb'2 hfb' sb h1 h2 h3 h4 h5
  · exact vb_frame F.swap hσ hm22 hm2n sm2 ha'1 hfa' sa h1 h2 h3 h4 h5

/-- Gradients of two facet functionals that are independent. -/
theorem exists_grads (f1 f2 : ℝ³ →ᵃ[ℝ] ℝ) {v X Y : ℝ³} (hv1 : f1 v = 0) (hv2 : f2 v = 0)
    (hX2 : f2 X < 0) (hY2 : f2 Y = 0) (hY1 : f1 Y < 0) :
    ∃ n1 n2 : ℝ³, (∀ x x', f1 x' - f1 x = ⟪n1, x' - x⟫) ∧ (∀ x x', f2 x' - f2 x = ⟪n2, x' - x⟫) ∧
      cross n1 n2 ≠ 0 := by
  obtain ⟨n1, h1⟩ := aff_grad f1
  obtain ⟨n2, h2⟩ := aff_grad f2
  refine ⟨n1, n2, h1, h2, ?_⟩
  have g1Y : ⟪n1, Y - v⟫ = f1 Y := by rw [← h1, hv1, sub_zero]
  have g2Y : ⟪n2, Y - v⟫ = 0 := by rw [← h2, hY2, hv2, sub_zero]
  have g2X : ⟪n2, X - v⟫ = f2 X := by rw [← h2, hv2, sub_zero]
  have hn1 : n1 ≠ 0 := by
    intro h0; rw [h0, inner_zero_left] at g1Y; exact hY1.ne g1Y.symm
  intro h0
  have hs := eq_smul_of_cross_eq_zero hn1 h0
  set k := ⟪n2, n1⟫ / ⟪n1, n1⟫
  have hk0 : k * f1 Y = 0 := by rw [← g1Y, ← real_inner_smul_left, ← hs, g2Y]
  have hk1 : k = 0 := (mul_eq_zero.mp hk0).resolve_right hY1.ne
  rw [hk1, zero_smul] at hs
  rw [hs, inner_zero_left] at g2X
  exact hX2.ne g2X.symm

/-- Three minimizers of `f2` on the plane `f1 = 0` are collinear. -/
theorem collin_of_min {f1 f2 : ℝ³ →ᵃ[ℝ] ℝ} {n1 n2 : ℝ³}
    (h1 : ∀ x x', f1 x' - f1 x = ⟪n1, x' - x⟫) (h2 : ∀ x x', f2 x' - f2 x = ⟪n2, x' - x⟫)
    (hk : cross n1 n2 ≠ 0) {x y z : ℝ³} (hxy : x ≠ y) (a1 : f1 y = f1 x) (a2 : f1 z = f1 x)
    (b1 : f2 y = f2 x) (b2 : f2 z = f2 x) : ∃ c : ℝ, z - x = c • (y - x) := by
  refine exists_smul_of_perp2 (n := n1) (e := n2) hk (sub_ne_zero.mpr hxy.symm) ?_ ?_ ?_ ?_
  · rw [← h1, a1, sub_self]
  · rw [← h2, b1, sub_self]
  · rw [← h1, a2, sub_self]
  · rw [← h2, b2, sub_self]

/-- Sidedness as a sign. -/
theorem oneSided_sign {v e : ℝ³} {S : Finset ℝ³}
    (h : (∀ x ∈ S, ⟪v, e⟫ ≤ ⟪x, e⟫) ∨ (∀ x ∈ S, ⟪x, e⟫ ≤ ⟪v, e⟫)) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ x ∈ S, 0 ≤ σ * (⟪x, e⟫ - ⟪v, e⟫) := by
  rcases h with h | h
  · exact ⟨1, Or.inl rfl, fun x hx => by linarith [h x hx]⟩
  · exact ⟨-1, Or.inr rfl, fun x hx => by linarith [h x hx]⟩

/-- **No rectangle of two vertical far edges at the shared vertex of two quadrilaterals**
(`QuadTripleRect`), from the facets of the faces around them. -/
theorem quadTripleRect_false {V Q1 Q2 : Finset ℝ³} {v P a1 a2 Q b1 b2 : ℝ³}
    (hgen : NoThreeCollinear V)
    (hQ1 : ∀ y, y ∈ Q1 ↔ y = v ∨ y = P ∨ y = a1 ∨ y = a2)
    (hQ2 : ∀ y, y ∈ Q2 ↔ y = v ∨ y = Q ∨ y = b1 ∨ y = b2)
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hint : Q1 ∩ Q2 = {v})
    (hPv : P ≠ v) (ha1v : a1 ≠ v) (ha2v : a2 ≠ v) (hQv : Q ≠ v) (hb1v : b1 ≠ v) (hb2v : b2 ≠ v)
    (hPa1 : P ≠ a1) (hPa2 : P ≠ a2) (hQb1 : Q ≠ b1) (hQb2 : Q ≠ b2)
    (Ta1 : ∃ φ : ℝ³ →ᵃ[ℝ] ℝ, φ v = 0 ∧ φ a1 = 0 ∧ φ P < 0 ∧ φ a2 < 0)
    (Ta2 : ∃ φ : ℝ³ →ᵃ[ℝ] ℝ, φ v = 0 ∧ φ a2 = 0 ∧ φ P < 0 ∧ φ a1 < 0)
    (E1 : ∃ φ : ℝ³ →ᵃ[ℝ] ℝ, φ P = 0 ∧ φ a1 = 0 ∧ φ v < 0 ∧ φ a2 < 0)
    (E2 : ∃ φ : ℝ³ →ᵃ[ℝ] ℝ, φ P = 0 ∧ φ a2 = 0 ∧ φ v < 0 ∧ φ a1 < 0)
    (Tb1 : ∃ φ : ℝ³ →ᵃ[ℝ] ℝ, φ v = 0 ∧ φ b1 = 0 ∧ φ Q < 0 ∧ φ b2 < 0)
    (Tb2 : ∃ φ : ℝ³ →ᵃ[ℝ] ℝ, φ v = 0 ∧ φ b2 = 0 ∧ φ Q < 0 ∧ φ b1 < 0)
    (G1 : ∃ φ : ℝ³ →ᵃ[ℝ] ℝ, φ Q = 0 ∧ φ b1 = 0 ∧ φ v < 0 ∧ φ b2 < 0)
    (G2 : ∃ φ : ℝ³ →ᵃ[ℝ] ℝ, φ Q = 0 ∧ φ b2 = 0 ∧ φ v < 0 ∧ φ b1 < 0)
    (K11 : KillP v a1 P a2 b1 Q b2) (K12 : KillP v a1 P a2 b2 Q b1)
    (K21 : KillP v a2 P a1 b1 Q b2) (K22 : KillP v a2 P a1 b2 Q b1) :
    ¬ QuadTripleRect V Q1 Q2 v := by
  classical
  rintro ⟨f1, f2, z1, n1, z2, n2, e, he, e1, e2, p, hp, p', hp', q, hq, q', hq', mp, mp', mq, mq',
    tpq, tp'q', hne, hw, hone⟩
  have only : ∀ y ∈ Q1, y ∈ Q2 → y = v := fun y h1 h2 => by
    have : y ∈ Q1 ∩ Q2 := mem_inter.mpr ⟨h1, h2⟩
    rwa [hint, mem_singleton] at this
  have mv1 : v ∈ Q1 := (hQ1 v).mpr (Or.inl rfl)
  have mv2 : v ∈ Q2 := (hQ2 v).mpr (Or.inl rfl)
  have mP : P ∈ Q1 := (hQ1 P).mpr (Or.inr (Or.inl rfl))
  have ma1 : a1 ∈ Q1 := (hQ1 a1).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have ma2 : a2 ∈ Q1 := (hQ1 a2).mpr (Or.inr (Or.inr (Or.inr rfl)))
  have mQ : Q ∈ Q2 := (hQ2 Q).mpr (Or.inr (Or.inl rfl))
  have mb1 : b1 ∈ Q2 := (hQ2 b1).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have mb2 : b2 ∈ Q2 := (hQ2 b2).mpr (Or.inr (Or.inr (Or.inr rfl)))
  have f1v : f1 v = 0 := z1 v mv1
  have f2v : f2 v = 0 := z2 v mv2
  have neg2 : ∀ y ∈ Q1, y ≠ v → f2 y < 0 := fun y hy hyv =>
    n2 y (h1V hy) (fun h => hyv (only y hy h))
  have neg1 : ∀ y ∈ Q2, y ≠ v → f1 y < 0 := fun y hy hyv =>
    n1 y (h2V hy) (fun h => hyv (only y h hy))
  obtain ⟨g1, g2, hg1, hg2, hk⟩ := exists_grads f1 f2 (X := P) (Y := b1) f1v f2v (neg2 P mP hPv)
    (z2 b1 mb1) (neg1 b1 mb1 hb1v)
  obtain ⟨σ, hσ, hs⟩ := oneSided_sign hone
  have s1 : ∀ x ∈ Q1, 0 ≤ σ * (⟪x, e⟫ - ⟪v, e⟫) := fun x hx => hs x (mem_union.mpr (Or.inl hx))
  have s2 : ∀ x ∈ Q2, 0 ≤ σ * (⟪x, e⟫ - ⟪v, e⟫) := fun x hx => hs x (mem_union.mpr (Or.inr hx))
  -- the two far corners at the depth of `v`
  have key : ∃ a a' b b' : ℝ³, a ∈ Q1 ∧ a' ∈ Q1 ∧ b ∈ Q2 ∧ b' ∈ Q2 ∧ (∀ x ∈ Q1, f2 a ≤ f2 x) ∧
      (∀ x ∈ Q1, f2 a' ≤ f2 x) ∧ (∀ x ∈ Q2, f1 b ≤ f1 x) ∧ (∀ x ∈ Q2, f1 b' ≤ f1 x) ∧
      ⟪a, e⟫ = ⟪v, e⟫ ∧ ⟪b, e⟫ = ⟪v, e⟫ ∧ ⟪a', e⟫ = ⟪b', e⟫ ∧ ⟪a', e⟫ ≠ ⟪v, e⟫ := by
    rcases hw with ⟨w, hwQ, hwm, hwe⟩ | ⟨w, hwQ, hwm, hwe⟩
    · by_cases hpv : ⟪p, e⟫ = ⟪v, e⟫
      · exact ⟨p, p', q, q', hp, hp', hq, hq', mp, mp', mq, mq', hpv, tpq.symm.trans hpv, tp'q',
          fun h => hne (hpv.trans h.symm)⟩
      · by_cases hp'v : ⟪p', e⟫ = ⟪v, e⟫
        · exact ⟨p', p, q', q, hp', hp, hq', hq, mp', mp, mq', mq, hp'v,
            tp'q'.symm.trans hp'v, tpq, hpv⟩
        · exfalso
          have hpp' : p ≠ p' := fun h => hne (by rw [h])
          have hpw : p ≠ w := fun h => hpv (by rw [h]; exact hwe)
          have hp'w : p' ≠ w := fun h => hp'v (by rw [h]; exact hwe)
          have c1 : f2 p' = f2 p := le_antisymm (mp' p hp) (mp p' hp')
          have c2 : f2 w = f2 p := le_antisymm (hwm p hp) (mp w hwQ)
          obtain ⟨c, hc⟩ := collin_of_min hg1 hg2 hk hpp' (by rw [z1 p hp, z1 p' hp'])
            (by rw [z1 p hp, z1 w hwQ]) c1 c2
          exact hgen p (h1V hp) p' (h1V hp') w (h1V hwQ) hpp' hpw hp'w c hc
    · by_cases hqv : ⟪q, e⟫ = ⟪v, e⟫
      · exact ⟨p, p', q, q', hp, hp', hq, hq', mp, mp', mq, mq', tpq.trans hqv, hqv, tp'q',
          fun h => hne ((tpq.trans hqv).trans h.symm)⟩
      · by_cases hq'v : ⟪q', e⟫ = ⟪v, e⟫
        · exact ⟨p', p, q', q, hp', hp, hq', hq, mp', mp, mq', mq, tp'q'.trans hq'v, hq'v, tpq,
            fun h => hqv (tpq.symm.trans h)⟩
        · exfalso
          have hqq' : q ≠ q' := fun h => hne (by rw [tpq, tp'q', h])
          have hqw : q ≠ w := fun h => hqv (by rw [h]; exact hwe)
          have hq'w : q' ≠ w := fun h => hq'v (by rw [h]; exact hwe)
          have c1 : f1 q' = f1 q := le_antisymm (mq' q hq) (mq q' hq')
          have c2 : f1 w = f1 q := le_antisymm (hwm q hq) (mq w hwQ)
          obtain ⟨c, hc⟩ := collin_of_min hg1 hg2 hk hqq' c1 c2
            (by rw [z2 q hq, z2 q' hq']) (by rw [z2 q hq, z2 w hwQ])
          exact hgen q (h2V hq) q' (h2V hq') w (h2V hwQ) hqq' hqw hq'w c hc
  obtain ⟨a, a', b, b', ha, ha', hb, hb', ma, ma', mb, mb', hta, htb, htie, hne'⟩ := key
  have hfa : f2 a < 0 := lt_of_le_of_lt (ma P mP) (neg2 P mP hPv)
  have hfb : f1 b < 0 := lt_of_le_of_lt (mb Q mQ) (neg1 Q mQ hQv)
  have F : TieFrame f1 f2 v a b e := ⟨he, f1v, f2v, z1 a ha, z2 b hb, e1, e2, hfa, hfb, hta, htb⟩
  have hfa' : f2 a' = f2 a := le_antisymm (ma' a ha) (ma a' ha')
  have hfb' : f1 b' = f1 b := le_antisymm (mb' b hb) (mb b' hb')
  have spos : 0 < σ * (⟪a', e⟫ - ⟪v, e⟫) :=
    sig_pos_of_ne hσ (s1 a' ha') (fun h => hne' (by linarith))
  have hbne : ⟪b', e⟫ ≠ ⟪v, e⟫ := by rw [← htie]; exact hne'
  have mem1 : ∀ y ∈ Q1, f2 y < 0 → y = P ∨ y = a1 ∨ y = a2 := fun y hy hmin => by
    rcases (hQ1 y).mp hy with h | h | h | h
    · exfalso; rw [h, f2v] at hmin; exact lt_irrefl _ hmin
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have mem2 : ∀ y ∈ Q2, f1 y < 0 → y = Q ∨ y = b1 ∨ y = b2 := fun y hy hmin => by
    rcases (hQ2 y).mp hy with h | h | h | h
    · exfalso; rw [h, f1v] at hmin; exact lt_irrefl _ hmin
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  obtain ⟨hP, haa⟩ := sideF F hσ (z1 P mP) (z1 a1 ma1) (z1 a2 ma2) (neg2 P mP hPv)
    (neg2 a1 ma1 ha1v) (neg2 a2 ma2 ha2v) (mem1 a ha hfa) (mem1 a' ha' (by rw [hfa']; exact hfa))
    (ma P mP) (ma a1 ma1) (ma a2 ma2) hfa' hne' (s1 a' ha') (s1 P mP) (s1 a1 ma1) (s1 a2 ma2)
    hPa1 hPa2 Ta1 Ta2 E1 E2
  have hfb'n : f1 b' < 0 := by rw [hfb']; exact hfb
  obtain ⟨hQ', hbb⟩ := sideF F.swap hσ (z2 Q mQ) (z2 b1 mb1) (z2 b2 mb2) (neg1 Q mQ hQv)
    (neg1 b1 mb1 hb1v) (neg1 b2 mb2 hb2v) (mem2 b hb hfb) (mem2 b' hb' hfb'n)
    (mb Q mQ) (mb b1 mb1) (mb b2 mb2) hfb' hbne (s2 b' hb') (s2 Q mQ) (s2 b1 mb1) (s2 b2 mb2)
    hQb1 hQb2 Tb1 Tb2 G1 G2
  subst hP hQ'
  have u1 := neg2 a1 ma1 ha1v
  have u2 := neg2 a2 ma2 ha2v
  have w1 := neg1 b1 mb1 hb1v
  have w2 := neg1 b2 mb2 hb2v
  rcases haa with rfl | rfl <;> rcases hbb with rfl | rfl
  · exact coreF F hσ (z1 _ ha') hfa' (z2 _ hb') hfb' (z1 a2 ma2) u2 (z2 b2 mb2) w2 htie spos
      (s1 a2 ma2) (s2 b2 mb2) K11
  · exact coreF F hσ (z1 _ ha') hfa' (z2 _ hb') hfb' (z1 a2 ma2) u2 (z2 b1 mb1) w1 htie spos
      (s1 a2 ma2) (s2 b1 mb1) K12
  · exact coreF F hσ (z1 _ ha') hfa' (z2 _ hb') hfb' (z1 a1 ma1) u1 (z2 b2 mb2) w2 htie spos
      (s1 a1 ma1) (s2 b2 mb2) K21
  · exact coreF F hσ (z1 _ ha') hfa' (z2 _ hb') hfb' (z1 a1 ma1) u1 (z2 b1 mb1) w1 htie spos
      (s1 a1 ma1) (s2 b1 mb1) K22

/-- `KillP` for labelled points: the four kinds of facet are faces of `fs`. -/
def KillL (fs : List (Finset (Fin 7))) (v a a' m1 b b' m2 : Fin 7) : Prop :=
  (∃ F ∈ fs, a ∈ F ∧ b ∈ F ∧ b' ∈ F ∧ a' ∉ F) ∨
  (∃ F ∈ fs, a ∈ F ∧ a' ∈ F ∧ b ∈ F ∧ b' ∉ F) ∨
  (∃ F ∈ fs, v ∈ F ∧ b ∈ F ∧ m1 ∈ F ∧ a ∉ F ∧ b' ∉ F) ∨
  (∃ F ∈ fs, v ∈ F ∧ a ∈ F ∧ m2 ∈ F ∧ b ∉ F ∧ a' ∉ F)

instance (fs : List (Finset (Fin 7))) (v a a' m1 b b' m2 : Fin 7) :
    Decidable (KillL fs v a a' m1 b b' m2) := by
  unfold KillL; infer_instance

theorem KillL.killP {x : Fin 7 → ℝ³} {fs : List (Finset (Fin 7))} (hR : RealizesFaces x fs)
    {v a a' m1 b b' m2 : Fin 7} (K : KillL fs v a a' m1 b b' m2) :
    KillP (x v) (x a) (x a') (x m1) (x b) (x b') (x m2) := by
  rcases K with ⟨F, hF, h1, h2, h3, h4⟩ | ⟨F, hF, h1, h2, h3, h4⟩ |
      ⟨F, hF, h1, h2, h3, h4, h5⟩ | ⟨F, hF, h1, h2, h3, h4, h5⟩ <;>
    obtain ⟨φ, hφ⟩ := hR F hF
  · exact Or.inl ⟨φ, (hφ _).1 h1, (hφ _).1 h2, (hφ _).1 h3, (hφ _).2 h4⟩
  · exact Or.inr (Or.inl ⟨φ, (hφ _).1 h1, (hφ _).1 h2, (hφ _).1 h3, (hφ _).2 h4⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨φ, (hφ _).1 h1, (hφ _).1 h2, (hφ _).1 h3, (hφ _).2 h4,
      (hφ _).2 h5⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨φ, (hφ _).1 h1, (hφ _).1 h2, (hφ _).1 h3, (hφ _).2 h4,
      (hφ _).2 h5⟩))

/-- **`quadTripleRect_false` for the labelled points of a realized type**: the quadrilaterals
`q1 = {v, P, a1, a2}`, `q2 = {v, Q, b1, b2}` (`P`, `Q` opposite `v`) and the facets used are faces
of `fs`. -/
theorem quadTripleRect_false_of_realizes {x : Fin 7 → ℝ³} (hx : Function.Injective x)
    (hgen : NoThreeCollinear (Finset.univ.image x)) {fs : List (Finset (Fin 7))}
    (hR : RealizesFaces x fs) (q1 q2 : Finset (Fin 7)) (v P a1 a2 Q b1 b2 : Fin 7)
    (hq1 : q1 = {v, P, a1, a2}) (hq2 : q2 = {v, Q, b1, b2}) (hint : q1 ∩ q2 = {v})
    (hne : P ≠ v ∧ a1 ≠ v ∧ a2 ≠ v ∧ Q ≠ v ∧ b1 ≠ v ∧ b2 ≠ v ∧ P ≠ a1 ∧ P ≠ a2 ∧ Q ≠ b1 ∧
      Q ≠ b2)
    (Ta1 : ∃ F ∈ fs, v ∈ F ∧ a1 ∈ F ∧ P ∉ F ∧ a2 ∉ F)
    (Ta2 : ∃ F ∈ fs, v ∈ F ∧ a2 ∈ F ∧ P ∉ F ∧ a1 ∉ F)
    (E1 : ∃ F ∈ fs, P ∈ F ∧ a1 ∈ F ∧ v ∉ F ∧ a2 ∉ F)
    (E2 : ∃ F ∈ fs, P ∈ F ∧ a2 ∈ F ∧ v ∉ F ∧ a1 ∉ F)
    (Tb1 : ∃ F ∈ fs, v ∈ F ∧ b1 ∈ F ∧ Q ∉ F ∧ b2 ∉ F)
    (Tb2 : ∃ F ∈ fs, v ∈ F ∧ b2 ∈ F ∧ Q ∉ F ∧ b1 ∉ F)
    (G1 : ∃ F ∈ fs, Q ∈ F ∧ b1 ∈ F ∧ v ∉ F ∧ b2 ∉ F)
    (G2 : ∃ F ∈ fs, Q ∈ F ∧ b2 ∈ F ∧ v ∉ F ∧ b1 ∉ F)
    (K11 : KillL fs v a1 P a2 b1 Q b2) (K12 : KillL fs v a1 P a2 b2 Q b1)
    (K21 : KillL fs v a2 P a1 b1 Q b2) (K22 : KillL fs v a2 P a1 b2 Q b1) :
    ¬ QuadTripleRect (Finset.univ.image x) (q1.image x) (q2.image x) (x v) := by
  classical
  obtain ⟨hPv, ha1v, ha2v, hQv, hb1v, hb2v, hPa1, hPa2, hQb1, hQb2⟩ := hne
  have mem : ∀ (q : Finset (Fin 7)) (i j k l : Fin 7), q = {i, j, k, l} →
      ∀ y, y ∈ q.image x ↔ y = x i ∨ y = x j ∨ y = x k ∨ y = x l := by
    intro q i j k l hq y
    subst hq
    simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨m, (rfl | rfl | rfl | rfl), rfl⟩ <;> simp
    · rintro (rfl | rfl | rfl | rfl) <;> exact ⟨_, by simp, rfl⟩
  have tri : ∀ {F : Finset (Fin 7)}, F ∈ fs → ∀ i j k l : Fin 7, i ∈ F → j ∈ F → k ∉ F → l ∉ F →
      ∃ φ : ℝ³ →ᵃ[ℝ] ℝ, φ (x i) = 0 ∧ φ (x j) = 0 ∧ φ (x k) < 0 ∧ φ (x l) < 0 := by
    intro F hF i j k l hi hj hk hl
    obtain ⟨φ, hφ⟩ := hR F hF
    exact ⟨φ, (hφ i).1 hi, (hφ j).1 hj, (hφ k).2 hk, (hφ l).2 hl⟩
  refine quadTripleRect_false (P := x P) (a1 := x a1) (a2 := x a2) (Q := x Q) (b1 := x b1)
    (b2 := x b2) hgen (mem q1 v P a1 a2 hq1) (mem q2 v Q b1 b2 hq2)
    (Finset.image_subset_image (Finset.subset_univ _))
    (Finset.image_subset_image (Finset.subset_univ _)) ?_
    (hx.ne hPv) (hx.ne ha1v) (hx.ne ha2v) (hx.ne hQv) (hx.ne hb1v) (hx.ne hb2v) (hx.ne hPa1)
    (hx.ne hPa2) (hx.ne hQb1) (hx.ne hQb2) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (K11.killP hR) (K12.killP hR)
    (K21.killP hR) (K22.killP hR)
  · rw [← Finset.image_inter _ _ hx, hint, Finset.image_singleton]
  · obtain ⟨F, hF, h1, h2, h3, h4⟩ := Ta1; exact tri hF v a1 P a2 h1 h2 h3 h4
  · obtain ⟨F, hF, h1, h2, h3, h4⟩ := Ta2; exact tri hF v a2 P a1 h1 h2 h3 h4
  · obtain ⟨F, hF, h1, h2, h3, h4⟩ := E1; exact tri hF P a1 v a2 h1 h2 h3 h4
  · obtain ⟨F, hF, h1, h2, h3, h4⟩ := E2; exact tri hF P a2 v a1 h1 h2 h3 h4
  · obtain ⟨F, hF, h1, h2, h3, h4⟩ := Tb1; exact tri hF v b1 Q b2 h1 h2 h3 h4
  · obtain ⟨F, hF, h1, h2, h3, h4⟩ := Tb2; exact tri hF v b2 Q b1 h1 h2 h3 h4
  · obtain ⟨F, hF, h1, h2, h3, h4⟩ := G1; exact tri hF Q b1 v b2 h1 h2 h3 h4
  · obtain ⟨F, hF, h1, h2, h3, h4⟩ := G2; exact tri hF Q b2 v b1 h1 h2 h3 h4

/-- **Type 07** (`0256`, `1234` at vertex `2`): the residual position `QuadTripleRect` does not
occur.  The far corner `a'` is the vertex `6` opposite `2`, `a` is `0` or `5`, `b' = 3`, and
`b` is `1` or `4`: `(0, 1)` is refuted by the facet `013`, `(5, 4)` by `456`, and `(0, 4)`,
`(5, 1)` by `245` (the triangle `{2, 0, 4}` or `{2, 5, 1}` of the triple tie is no face). -/
theorem not_quadTripleRect_type07 {x : Fin 7 → ℝ³} (hx : Function.Injective x)
    (hgen : NoThreeCollinear (Finset.univ.image x))
    (hR : RealizesFaces x (sevenTypeFaces 6)) :
    ¬ QuadTripleRect (Finset.univ.image x) (({0, 2, 5, 6} : Finset (Fin 7)).image x)
      (({1, 2, 3, 4} : Finset (Fin 7)).image x) (x 2) :=
  quadTripleRect_false_of_realizes hx hgen hR {0, 2, 5, 6} {1, 2, 3, 4} 2 6 0 5 3 1 4
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

/-- **Type 14** (`0235`, `1456` at vertex `5`): the residual position does not occur; the
far corners are `3` and `1` opposite `5`, `a` is `0` or `2`, `b` is `4` or `6`. -/
theorem not_quadTripleRect_type14 {x : Fin 7 → ℝ³} (hx : Function.Injective x)
    (hgen : NoThreeCollinear (Finset.univ.image x))
    (hR : RealizesFaces x (sevenTypeFaces 13)) :
    ¬ QuadTripleRect (Finset.univ.image x) (({0, 2, 3, 5} : Finset (Fin 7)).image x)
      (({1, 4, 5, 6} : Finset (Fin 7)).image x) (x 5) :=
  quadTripleRect_false_of_realizes hx hgen hR {0, 2, 3, 5} {1, 4, 5, 6} 5 3 0 2 1 4 6
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

end Minimality

end
