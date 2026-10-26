module

public import Minimality.TripleTieObtuse
public import Minimality.SevenTypes

@[expose] public section

/-!
# Case (c) of the triple tie does not occur in types 07 and 14

(`FEWER-FACES-PROOFS.md` §23, Lemma 23.0 and Theorem 24.5.)  Two quadrilateral faces `Q1`,
`Q2` meeting in `v`, seen along the line `v + ℝ e` of their planes, with far ends `p`, `q` at
the depth of `v` (the triple tie).  In the frame `(p - v, q - v, e)` every point of `Q1` is
`v + λ (p - v) + t e` and every point of `Q2` is `v + μ (q - v) + s e`, with `0 < λ, μ < 1`
for the middles.  A face of the type through `v` and `p` (a triangle) makes `Q1` one-sided
(`TieFrame.oneSided_left`).  If `p` and `q` are both opposite to `v`, then a facet through a
middle of `Q1` and a middle of `Q2` (not through `v`) forces their depths to have one sign
(`TieFrame.cross_pos`): the segment between them would cross the depth of `v` inside the
shadow triangle, at an interior point of the triangle `v p q` of the hull.  Two such facets
through one middle of `Q1` make `Q2` one-sided.  This is the statement of Lemma 23.0 that the
far ends are joined by an edge (the opposite vertices `6, 3` resp. `3, 1` of types 07, 14 are
not adjacent), in the form used.

* `triGenTieO_of_quads`: `TriGenPar` gives `TriGenTieO` for two quadrilaterals with these
  facets.
* `triGenTieO_type07`, `triGenTieO_type14`: the realized types.
-/

namespace Minimality

open Finset
open scoped RealInnerProductSpace

/-- The gradient of an affine functional. -/
theorem aff_grad (f : ℝ³ →ᵃ[ℝ] ℝ) : ∃ n : ℝ³, ∀ x x', f x' - f x = ⟪n, x' - x⟫ := by
  obtain ⟨K, α, β, γ, hf⟩ := affine_xyz f
  refine ⟨!₂[α, β, γ], fun x x' => ?_⟩
  rw [hf, hf]
  simp [PiLp.inner_apply, Fin.sum_univ_three]; ring

/-- Three vectors orthogonal to three independent ones are zero (`cross n1 n2 ≠ 0`, `e ≠ 0`). -/
theorem eq_zero_of_perp3 {n1 n2 e w : ℝ³} (hk : cross n1 n2 ≠ 0) (he : e ≠ 0)
    (h1 : ⟪n1, e⟫ = 0) (h2 : ⟪n2, e⟫ = 0) (h3 : ⟪n1, w⟫ = 0) (h4 : ⟪n2, w⟫ = 0)
    (h5 : ⟪e, w⟫ = 0) : w = 0 := by
  obtain ⟨c, hc⟩ := exists_smul_of_perp2 hk he h1 h2 h3 h4
  have hee : ⟪e, e⟫ ≠ 0 := inner_self_ne_zero.mpr he
  have : c = 0 := by
    rw [hc, inner_smul_right] at h5
    exact (mul_eq_zero.mp h5).resolve_right hee
  rw [hc, this, zero_smul]

/-- The data of the tie frame: two face functionals `f1` (zero on `Q1 ∋ v, p`, negative at `q`)
and `f2` (zero on `Q2 ∋ v, q`, negative at `p`), both vanishing on the line `v + ℝ e`, and the
far ends `p`, `q` at the depth of `v` along `e`. -/
structure TieFrame (f1 f2 : ℝ³ →ᵃ[ℝ] ℝ) (v p q e : ℝ³) : Prop where
  he : e ≠ 0
  hv1 : f1 v = 0
  hv2 : f2 v = 0
  hp1 : f1 p = 0
  hq2 : f2 q = 0
  he1 : f1 (v + e) = 0
  he2 : f2 (v + e) = 0
  hp2 : f2 p < 0
  hq1 : f1 q < 0
  tp : ⟪p, e⟫ = ⟪v, e⟫
  tq : ⟪q, e⟫ = ⟪v, e⟫

theorem TieFrame.swap {f1 f2 : ℝ³ →ᵃ[ℝ] ℝ} {v p q e : ℝ³} (F : TieFrame f1 f2 v p q e) :
    TieFrame f2 f1 v q p e :=
  ⟨F.he, F.hv2, F.hv1, F.hq2, F.hp1, F.he2, F.he1, F.hq1, F.hp2, F.tq, F.tp⟩

/-- Every point is `v + λ (p - v) + μ (q - v) + t e`, with `λ = f2 y / f2 p`,
`μ = f1 y / f1 q`, `t = (⟪y, e⟫ - ⟪v, e⟫) / ⟪e, e⟫`. -/
theorem TieFrame.decomp {f1 f2 : ℝ³ →ᵃ[ℝ] ℝ} {v p q e : ℝ³} (F : TieFrame f1 f2 v p q e)
    (y : ℝ³) : y = v + (f2 y / f2 p) • (p - v) + (f1 y / f1 q) • (q - v) +
      ((⟪y, e⟫ - ⟪v, e⟫) / ⟪e, e⟫) • e := by
  obtain ⟨n1, h1⟩ := aff_grad f1
  obtain ⟨n2, h2⟩ := aff_grad f2
  have hee : ⟪e, e⟫ ≠ 0 := inner_self_ne_zero.mpr F.he
  have hp2 := F.hp2.ne
  have hq1 := F.hq1.ne
  have hn1e : ⟪n1, e⟫ = 0 := by
    have := h1 v (v + e); rw [F.he1, F.hv1, add_sub_cancel_left] at this; linarith
  have hn2e : ⟪n2, e⟫ = 0 := by
    have := h2 v (v + e); rw [F.he2, F.hv2, add_sub_cancel_left] at this; linarith
  have g1p : ⟪n1, p - v⟫ = 0 := by rw [← h1, F.hp1, F.hv1, sub_zero]
  have g1q : ⟪n1, q - v⟫ = f1 q := by rw [← h1, F.hv1, sub_zero]
  have g2p : ⟪n2, p - v⟫ = f2 p := by rw [← h2, F.hv2, sub_zero]
  have g2q : ⟪n2, q - v⟫ = 0 := by rw [← h2, F.hq2, F.hv2, sub_zero]
  have g1y : ⟪n1, y - v⟫ = f1 y := by rw [← h1, F.hv1, sub_zero]
  have g2y : ⟪n2, y - v⟫ = f2 y := by rw [← h2, F.hv2, sub_zero]
  have hn1 : n1 ≠ 0 := by
    intro h0; rw [h0, inner_zero_left] at g1q; exact hq1 g1q.symm
  have hk : cross n1 n2 ≠ 0 := by
    intro h0
    have hs := eq_smul_of_cross_eq_zero hn1 h0
    set k := ⟪n2, n1⟫ / ⟪n1, n1⟫
    have hk0 : k * f1 q = 0 := by rw [← g1q, ← real_inner_smul_left, ← hs, g2q]
    have hk1 : k = 0 := (mul_eq_zero.mp hk0).resolve_right hq1
    rw [hk1, zero_smul] at hs
    rw [hs, inner_zero_left] at g2p
    exact hp2 g2p.symm
  set l := f2 y / f2 p with hl
  set m := f1 y / f1 q with hm
  set t := (⟪y, e⟫ - ⟪v, e⟫) / ⟪e, e⟫ with ht
  have hlp : l * f2 p = f2 y := by rw [hl]; field_simp
  have hmq : m * f1 q = f1 y := by rw [hm]; field_simp
  have hte : t * ⟪e, e⟫ = ⟪y, e⟫ - ⟪v, e⟫ := by rw [ht]; field_simp
  have hw : y - (v + l • (p - v) + m • (q - v) + t • e) =
      (y - v) - l • (p - v) - m • (q - v) - t • e := by module
  have hz : y - (v + l • (p - v) + m • (q - v) + t • e) = 0 := by
    rw [hw]
    refine eq_zero_of_perp3 hk F.he hn1e hn2e ?_ ?_ ?_
    · simp only [inner_sub_right, real_inner_smul_right, g1y, g1p, g1q, hn1e]
      linarith
    · simp only [inner_sub_right, real_inner_smul_right, g2y, g2p, g2q, hn2e]
      linarith
    · simp only [inner_sub_right, real_inner_smul_right, real_inner_comm y e, real_inner_comm v e,
        real_inner_comm p e, real_inner_comm q e, F.tp, F.tq]
      linarith
  exact (sub_eq_zero.mp hz)

/-- Any affine functional in the frame: `φ y = φ v + λ (φ p - φ v) + μ (φ q - φ v) + t d`. -/
theorem TieFrame.aff {f1 f2 : ℝ³ →ᵃ[ℝ] ℝ} {v p q e : ℝ³} (F : TieFrame f1 f2 v p q e)
    (φ : ℝ³ →ᵃ[ℝ] ℝ) (y : ℝ³) :
    φ y = φ v + (f2 y / f2 p) * (φ p - φ v) + (f1 y / f1 q) * (φ q - φ v) +
      ((⟪y, e⟫ - ⟪v, e⟫) / ⟪e, e⟫) * (φ (v + e) - φ v) := by
  obtain ⟨n, hn⟩ := aff_grad φ
  have hy : y - v = (f2 y / f2 p) • (p - v) + (f1 y / f1 q) • (q - v) +
      ((⟪y, e⟫ - ⟪v, e⟫) / ⟪e, e⟫) • e := by
    conv_lhs => rw [F.decomp y]
    abel
  have h1 : φ y - φ v = ⟪n, y - v⟫ := hn v y
  rw [hy] at h1
  simp only [inner_add_right, real_inner_smul_right] at h1
  have hp : ⟪n, p - v⟫ = φ p - φ v := (hn v p).symm
  have hq : ⟪n, q - v⟫ = φ q - φ v := (hn v q).symm
  have he : ⟪n, e⟫ = φ (v + e) - φ v := by rw [hn v (v + e), add_sub_cancel_left]
  rw [hp, hq, he] at h1
  linarith

/-- **Two middles at the depth of `v` crossing** (Lemma 23.0, case (c)): a facet through a middle
`a` of `Q1` and a middle `b` of `Q2`, not through `v`, forces the depths of `a` and `b`
relative to `v` to have the same sign.  Otherwise the segment `a b` crosses the depth of `v`
at an interior point of the triangle `v p q` of the hull. -/
theorem TieFrame.cross_pos {f1 f2 : ℝ³ →ᵃ[ℝ] ℝ} {v p q e : ℝ³} (F : TieFrame f1 f2 v p q e)
    {a b : ℝ³} (ha1 : f1 a = 0) (hb2 : f2 b = 0) (ha : f2 p ≤ f2 a) (ha0 : f2 a < 0)
    (hb : f1 q ≤ f1 b) (hb0 : f1 b < 0) (hna : ∀ c : ℝ, a - p ≠ c • e)
    (hnb : ∀ c : ℝ, b - q ≠ c • e) {φ : ℝ³ →ᵃ[ℝ] ℝ} (hφa : φ a = 0) (hφb : φ b = 0)
    (hφv : φ v < 0) (hφp : φ p ≤ 0) (hφq : φ q ≤ 0) :
    0 < (⟪a, e⟫ - ⟪v, e⟫) * (⟪b, e⟫ - ⟪v, e⟫) := by
  have hee : 0 < ⟪e, e⟫ := real_inner_self_pos.mpr F.he
  have hp2 := F.hp2
  have hq1 := F.hq1
  have hl1 : f2 a / f2 p ≠ 1 := by
    intro h
    have hd := F.decomp a
    rw [h, ha1, zero_div, zero_smul, add_zero, one_smul] at hd
    refine hna ((⟪a, e⟫ - ⟪v, e⟫) / ⟪e, e⟫) ?_
    conv_lhs => rw [hd]
    abel
  have hm1 : f1 b / f1 q ≠ 1 := by
    intro h
    have hd := F.decomp b
    simp only [h, hb2, zero_div, zero_smul, add_zero, one_smul] at hd
    refine hnb ((⟪b, e⟫ - ⟪v, e⟫) / ⟪e, e⟫) ?_
    conv_lhs => rw [hd]
    abel
  have hl0 : 0 < f2 a / f2 p := div_pos_of_neg_of_neg ha0 hp2
  have hm0 : 0 < f1 b / f1 q := div_pos_of_neg_of_neg hb0 hq1
  have hl2 : f2 a / f2 p < 1 := lt_of_le_of_ne ((div_le_one_of_neg hp2).mpr ha) hl1
  have hm2 : f1 b / f1 q < 1 := lt_of_le_of_ne ((div_le_one_of_neg hq1).mpr hb) hm1
  have A := F.aff φ a
  have B := F.aff φ b
  rw [ha1, zero_div, zero_mul, add_zero, hφa] at A
  rw [hb2, zero_div, zero_mul, hφb] at B
  set l := f2 a / f2 p
  set m := f1 b / f1 q
  set ta := (⟪a, e⟫ - ⟪v, e⟫) / ⟪e, e⟫
  set sb := (⟪b, e⟫ - ⟪v, e⟫) / ⟪e, e⟫
  set d := φ (v + e) - φ v
  have h1 : 0 < ta * d := by nlinarith [mul_pos hl0 (neg_pos.mpr hφv)]
  have h2 : 0 < sb * d := by nlinarith [mul_pos hm0 (neg_pos.mpr hφv)]
  have h3 : 0 < ta * sb := by
    by_contra hc
    push Not at hc
    nlinarith [mul_pos h1 h2, sq_nonneg d]
  have : (⟪a, e⟫ - ⟪v, e⟫) * (⟪b, e⟫ - ⟪v, e⟫) = (ta * sb) * ⟪e, e⟫ ^ 2 := by
    simp only [ta, sb]; field_simp
  rw [this]; positivity

/-- A face through `v` and the far end `p` (a triangle of the type) makes `Q1` one-sided: its
other two points `a1`, `a2` are strictly on one side of the depth of `v`. -/
theorem TieFrame.oneSided_left {f1 f2 : ℝ³ →ᵃ[ℝ] ℝ} {v p q e : ℝ³} (F : TieFrame f1 f2 v p q e)
    {a1 a2 : ℝ³} (ha1 : f1 a1 = 0) (ha2 : f1 a2 = 0) {φ : ℝ³ →ᵃ[ℝ] ℝ} (hv : φ v = 0)
    (hp : φ p = 0) (h1 : φ a1 < 0) (h2 : φ a2 < 0) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ σ * ⟪a1, e⟫ < σ * ⟪v, e⟫ ∧ σ * ⟪a2, e⟫ < σ * ⟪v, e⟫ := by
  have hee : 0 < ⟪e, e⟫ := real_inner_self_pos.mpr F.he
  have A := F.aff φ a1
  have B := F.aff φ a2
  rw [ha1, zero_div, zero_mul, add_zero, hv, hp] at A
  rw [ha2, zero_div, zero_mul, add_zero, hv, hp] at B
  have u1 : ⟪a1, e⟫ - ⟪v, e⟫ = ((⟪a1, e⟫ - ⟪v, e⟫) / ⟪e, e⟫) * ⟪e, e⟫ := by field_simp
  have u2 : ⟪a2, e⟫ - ⟪v, e⟫ = ((⟪a2, e⟫ - ⟪v, e⟫) / ⟪e, e⟫) * ⟪e, e⟫ := by field_simp
  set t1 := (⟪a1, e⟫ - ⟪v, e⟫) / ⟪e, e⟫
  set t2 := (⟪a2, e⟫ - ⟪v, e⟫) / ⟪e, e⟫
  set d := φ (v + e) - 0
  have A' : φ a1 = t1 * d := by rw [A]; ring
  have B' : φ a2 = t2 * d := by rw [B]; ring
  rcases lt_trichotomy d 0 with hd | hd | hd
  · refine ⟨-1, Or.inr rfl, ?_, ?_⟩
    · have : 0 < t1 := by by_contra hc; push Not at hc; nlinarith
      nlinarith
    · have : 0 < t2 := by by_contra hc; push Not at hc; nlinarith
      nlinarith
  · rw [hd] at A'; linarith
  · refine ⟨1, Or.inl rfl, ?_, ?_⟩
    · have : t1 < 0 := by by_contra hc; push Not at hc; nlinarith
      nlinarith
    · have : t2 < 0 := by by_contra hc; push Not at hc; nlinarith
      nlinarith

/-- **No case (c) at two quadrilaterals with the facets of types 07 and 14** (Lemma 23.0 and
Theorem 24.5): `Q1 = {v, P, a1, a2}` and `Q2 = {v, Q, b1, b2}` meet only in `v`, `P` is opposite
`v` in `Q1` (so `a1`, `a2` are its neighbours) and `Q` is opposite `v` in `Q2`.  Given the
triangle facets through `v` and each neighbour (`Ta1`, `Ta2`, `Tb1`, `Tb2`: zero at both, negative
at the other two points of the quadrilateral) and two facets avoiding `v` through `a1` and
`b1`, resp. `a1` and `b2` (`C1`, `C2`), `TriGenPar` gives `TriGenTieO`: at the triple tie of any
far ends, `Q1` or `Q2` is one-sided (`TieHT`).  The opposite far ends `P`, `Q` are excluded by
the two facets `C1`, `C2` (`TieFrame.cross_pos`), a far end next to `v` by the triangle. -/
theorem triGenTieO_of_quads {V Q1 Q2 : Finset ℝ³} {v P a1 a2 Q b1 b2 : ℝ³}
    (hQ1 : ∀ y, y ∈ Q1 ↔ y = v ∨ y = P ∨ y = a1 ∨ y = a2)
    (hQ2 : ∀ y, y ∈ Q2 ↔ y = v ∨ y = Q ∨ y = b1 ∨ y = b2)
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hint : Q1 ∩ Q2 = {v})
    (hPv : P ≠ v) (ha1v : a1 ≠ v) (ha2v : a2 ≠ v) (hQv : Q ≠ v) (hb1v : b1 ≠ v) (hb2v : b2 ≠ v)
    (ha1P : a1 ≠ P) (hb1Q : b1 ≠ Q) (hb2Q : b2 ≠ Q)
    (Ta1 : ∃ φ : ℝ³ →ᵃ[ℝ] ℝ, φ v = 0 ∧ φ a1 = 0 ∧ φ P < 0 ∧ φ a2 < 0)
    (Ta2 : ∃ φ : ℝ³ →ᵃ[ℝ] ℝ, φ v = 0 ∧ φ a2 = 0 ∧ φ P < 0 ∧ φ a1 < 0)
    (Tb1 : ∃ φ : ℝ³ →ᵃ[ℝ] ℝ, φ v = 0 ∧ φ b1 = 0 ∧ φ Q < 0 ∧ φ b2 < 0)
    (Tb2 : ∃ φ : ℝ³ →ᵃ[ℝ] ℝ, φ v = 0 ∧ φ b2 = 0 ∧ φ Q < 0 ∧ φ b1 < 0)
    (C1 : ∃ φ : ℝ³ →ᵃ[ℝ] ℝ, φ v < 0 ∧ φ a1 = 0 ∧ φ b1 = 0 ∧ φ P ≤ 0 ∧ φ Q ≤ 0)
    (C2 : ∃ φ : ℝ³ →ᵃ[ℝ] ℝ, φ v < 0 ∧ φ a1 = 0 ∧ φ b2 = 0 ∧ φ P ≤ 0 ∧ φ Q ≤ 0) :
    TriGenPar V Q1 Q2 v → TriGenTieO V Q1 Q2 v := by
  intro hpar f1 f2 z1 n1 z2 n2 e he e1 e2
  refine ⟨hpar f1 f2 z1 n1 z2 n2 e he e1 e2, ?_⟩
  intro p hp q hq _ hpmin hqmin
  have only : ∀ y ∈ Q1, y ∈ Q2 → y = v := fun y h1 h2 => by
    have : y ∈ Q1 ∩ Q2 := mem_inter.mpr ⟨h1, h2⟩
    rwa [hint, mem_singleton] at this
  have mP : P ∈ Q1 := (hQ1 P).mpr (Or.inr (Or.inl rfl))
  have ma1 : a1 ∈ Q1 := (hQ1 a1).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have ma2 : a2 ∈ Q1 := (hQ1 a2).mpr (Or.inr (Or.inr (Or.inr rfl)))
  have mQ : Q ∈ Q2 := (hQ2 Q).mpr (Or.inr (Or.inl rfl))
  have mb1 : b1 ∈ Q2 := (hQ2 b1).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have mb2 : b2 ∈ Q2 := (hQ2 b2).mpr (Or.inr (Or.inr (Or.inr rfl)))
  have mv1 : v ∈ Q1 := (hQ1 v).mpr (Or.inl rfl)
  have mv2 : v ∈ Q2 := (hQ2 v).mpr (Or.inl rfl)
  have f1v : f1 v = 0 := z1 v mv1
  have f2v : f2 v = 0 := z2 v mv2
  have neg2 : ∀ y ∈ Q1, y ≠ v → f2 y < 0 := fun y hy hyv =>
    n2 y (h1V hy) (fun h => hyv (only y hy h))
  have neg1 : ∀ y ∈ Q2, y ≠ v → f1 y < 0 := fun y hy hyv =>
    n1 y (h2V hy) (fun h => hyv (only y h hy))
  have hpv : p ≠ v := by
    intro h
    have := hpmin P mP
    rw [h, f2v] at this
    linarith [neg2 P mP hPv]
  have hqv : q ≠ v := by
    intro h
    have := hqmin Q mQ
    rw [h, f1v] at this
    linarith [neg1 Q mQ hQv]
  refine Or.inl ?_
  by_cases h1 : ⟪p, e⟫ = ⟪q, e⟫
  swap
  · exact Or.inl (Or.inl (Or.inl h1))
  by_cases h2 : ⟪v, e⟫ = ⟪p, e⟫
  swap
  · exact Or.inl (Or.inr ⟨h1, h2⟩)
  refine Or.inr ⟨h1, h2, ?_⟩
  have F : TieFrame f1 f2 v p q e :=
    ⟨he, f1v, f2v, z1 p hp, z2 q hq, e1, e2, neg2 p hp hpv, neg1 q hq hqv, h2.symm,
      h1.symm.trans h2.symm⟩
  -- one-sidedness of `Q1` from a triangle through `v` and a neighbour `a` of `v`
  have side1 : ∀ a a' : ℝ³, p = a → (a = a1 ∧ a' = a2 ∨ a = a2 ∧ a' = a1) →
      OneSided Q1 v p (fun x => ⟪x, e⟫) := by
    intro a a' hpa hcase
    obtain ⟨φ, hv, ha, hP, ha'⟩ : ∃ φ : ℝ³ →ᵃ[ℝ] ℝ, φ v = 0 ∧ φ a = 0 ∧ φ P < 0 ∧ φ a' < 0 := by
      rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Ta1
      · exact Ta2
    obtain ⟨σ, hσ, s1, s2⟩ := F.oneSided_left (a1 := P) (a2 := a') (z1 P mP)
      (z1 a' (by rcases hcase with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption)) hv (by rw [hpa]; exact ha)
      hP ha'
    refine ⟨σ, hσ, fun x hx hxv hxp => ?_⟩
    show σ * ⟪x, e⟫ < σ * ⟪v, e⟫
    rcases (hQ1 x).mp hx with h | h | h | h
    · exact absurd h hxv
    · rw [h]; exact s1
    · rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd (h.trans hpa.symm) hxp
      · rw [h]; exact s2
    · rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [h]; exact s2
      · exact absurd (h.trans hpa.symm) hxp
  have side2 : ∀ b b' : ℝ³, q = b → (b = b1 ∧ b' = b2 ∨ b = b2 ∧ b' = b1) →
      OneSided Q2 v q (fun x => ⟪x, e⟫) := by
    intro b b' hqb hcase
    obtain ⟨φ, hv, hb, hQ, hb'⟩ : ∃ φ : ℝ³ →ᵃ[ℝ] ℝ, φ v = 0 ∧ φ b = 0 ∧ φ Q < 0 ∧ φ b' < 0 := by
      rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Tb1
      · exact Tb2
    obtain ⟨σ, hσ, s1, s2⟩ := F.swap.oneSided_left (a1 := Q) (a2 := b') (z2 Q mQ)
      (z2 b' (by rcases hcase with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption)) hv (by rw [hqb]; exact hb)
      hQ hb'
    refine ⟨σ, hσ, fun x hx hxv hxq => ?_⟩
    show σ * ⟪x, e⟫ < σ * ⟪v, e⟫
    rcases (hQ2 x).mp hx with h | h | h | h
    · exact absurd h hxv
    · rw [h]; exact s1
    · rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd (h.trans hqb.symm) hxq
      · rw [h]; exact s2
    · rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [h]; exact s2
      · exact absurd (h.trans hqb.symm) hxq
  rcases (hQ1 p).mp hp with hpv' | hpP | hpa1 | hpa2
  · exact absurd hpv' hpv
  · rcases (hQ2 q).mp hq with hqv' | hqQ | hqb1 | hqb2
    · exact absurd hqv' hqv
    · -- both far ends opposite `v`: the two facets `C1`, `C2` through `a1`
      obtain ⟨φ1, hv1, ha1', hb1', hP1, hQ1'⟩ := C1
      obtain ⟨φ2, hv2, ha2', hb2', hP2, hQ2'⟩ := C2
      have npa : ∀ c : ℝ, a1 - p ≠ c • e := fun c =>
        hpar f1 f2 z1 n1 z2 n2 e he e1 e2 p (h1V hp) a1 (h1V ma1)
          (by rw [hpP]; exact ha1P.symm) c
      have nq : ∀ b, b ∈ Q2 → b ≠ Q → ∀ c : ℝ, b - q ≠ c • e := fun b hb hbQ c =>
        hpar f1 f2 z1 n1 z2 n2 e he e1 e2 q (h2V hq) b (h2V hb) (by rw [hqQ]; exact hbQ.symm) c
      have u1 := F.cross_pos (z1 a1 ma1) (z2 b1 mb1) (hpmin a1 ma1) (neg2 a1 ma1 ha1v)
        (hqmin b1 mb1) (neg1 b1 mb1 hb1v) npa (nq b1 mb1 hb1Q) ha1' hb1' hv1
        (by rw [hpP]; exact hP1) (by rw [hqQ]; exact hQ1')
      have u2 := F.cross_pos (z1 a1 ma1) (z2 b2 mb2) (hpmin a1 ma1) (neg2 a1 ma1 ha1v)
        (hqmin b2 mb2) (neg1 b2 mb2 hb2v) npa (nq b2 mb2 hb2Q) ha2' hb2' hv2
        (by rw [hpP]; exact hP2) (by rw [hqQ]; exact hQ2')
      refine Or.inr (Or.inl ?_)
      set ua := ⟪a1, e⟫ - ⟪v, e⟫
      set ub1 := ⟪b1, e⟫ - ⟪v, e⟫
      set ub2 := ⟪b2, e⟫ - ⟪v, e⟫
      have key : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ σ * ub1 < 0 ∧ σ * ub2 < 0 := by
        rcases lt_trichotomy ua 0 with hu | hu | hu
        · exact ⟨1, Or.inl rfl, by nlinarith, by nlinarith⟩
        · rw [hu] at u1; simp at u1
        · exact ⟨-1, Or.inr rfl, by nlinarith, by nlinarith⟩
      obtain ⟨σ, hσ, k1, k2⟩ := key
      refine ⟨σ, hσ, fun x hx hxv hxq => ?_⟩
      show σ * ⟪x, e⟫ < σ * ⟪v, e⟫
      rcases (hQ2 x).mp hx with h | h | h | h
      · exact absurd h hxv
      · exact absurd (h.trans hqQ.symm) hxq
      · rw [h]; simp only [ub1] at k1; linarith
      · rw [h]; simp only [ub2] at k2; linarith
    · exact Or.inr (Or.inl (side2 b1 b2 hqb1 (Or.inl ⟨rfl, rfl⟩)))
    · exact Or.inr (Or.inl (side2 b2 b1 hqb2 (Or.inr ⟨rfl, rfl⟩)))
  · exact Or.inl (side1 a1 a2 hpa1 (Or.inl ⟨rfl, rfl⟩))
  · exact Or.inl (side1 a2 a1 hpa2 (Or.inr ⟨rfl, rfl⟩))

/-- `triGenTieO_of_quads` for the labelled points of a realized type: the quadrilaterals
`q1 = {v, P, a1, a2}`, `q2 = {v, Q, b1, b2}` and the facets `Ta1, …, C2` are faces of `fs`. -/
theorem triGenTieO_of_realizes {x : Fin 7 → ℝ³} (hx : Function.Injective x)
    {fs : List (Finset (Fin 7))} (hR : RealizesFaces x fs) (q1 q2 : Finset (Fin 7))
    (v P a1 a2 Q b1 b2 : Fin 7) (hq1 : q1 = {v, P, a1, a2}) (hq2 : q2 = {v, Q, b1, b2})
    (hint : q1 ∩ q2 = {v})
    (hne : P ≠ v ∧ a1 ≠ v ∧ a2 ≠ v ∧ Q ≠ v ∧ b1 ≠ v ∧ b2 ≠ v ∧ a1 ≠ P ∧ b1 ≠ Q ∧ b2 ≠ Q)
    (Ta1 : ∃ F ∈ fs, v ∈ F ∧ a1 ∈ F ∧ P ∉ F ∧ a2 ∉ F)
    (Ta2 : ∃ F ∈ fs, v ∈ F ∧ a2 ∈ F ∧ P ∉ F ∧ a1 ∉ F)
    (Tb1 : ∃ F ∈ fs, v ∈ F ∧ b1 ∈ F ∧ Q ∉ F ∧ b2 ∉ F)
    (Tb2 : ∃ F ∈ fs, v ∈ F ∧ b2 ∈ F ∧ Q ∉ F ∧ b1 ∉ F)
    (C1 : ∃ F ∈ fs, v ∉ F ∧ a1 ∈ F ∧ b1 ∈ F) (C2 : ∃ F ∈ fs, v ∉ F ∧ a1 ∈ F ∧ b2 ∈ F) :
    TriGenPar (Finset.univ.image x) (q1.image x) (q2.image x) (x v) →
      TriGenTieO (Finset.univ.image x) (q1.image x) (q2.image x) (x v) := by
  classical
  obtain ⟨hPv, ha1v, ha2v, hQv, hb1v, hb2v, ha1P, hb1Q, hb2Q⟩ := hne
  have mem : ∀ (q : Finset (Fin 7)) (i j k l : Fin 7), q = {i, j, k, l} →
      ∀ y, y ∈ q.image x ↔ y = x i ∨ y = x j ∨ y = x k ∨ y = x l := by
    intro q i j k l hq y
    subst hq
    simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨m, (rfl | rfl | rfl | rfl), rfl⟩ <;> simp
    · rintro (rfl | rfl | rfl | rfl) <;> exact ⟨_, by simp, rfl⟩
  have tri : ∀ F ∈ fs, ∀ i j k l : Fin 7, i ∈ F → j ∈ F → k ∉ F → l ∉ F →
      ∃ φ : ℝ³ →ᵃ[ℝ] ℝ, φ (x i) = 0 ∧ φ (x j) = 0 ∧ φ (x k) < 0 ∧ φ (x l) < 0 := by
    intro F hF i j k l hi hj hk hl
    obtain ⟨φ, hφ⟩ := hR F hF
    exact ⟨φ, (hφ i).1 hi, (hφ j).1 hj, (hφ k).2 hk, (hφ l).2 hl⟩
  have crs : ∀ F ∈ fs, ∀ i j k l m : Fin 7, i ∉ F → j ∈ F → k ∈ F →
      ∃ φ : ℝ³ →ᵃ[ℝ] ℝ, φ (x i) < 0 ∧ φ (x j) = 0 ∧ φ (x k) = 0 ∧ φ (x l) ≤ 0 ∧ φ (x m) ≤ 0 := by
    intro F hF i j k l m hi hj hk
    obtain ⟨φ, hφ⟩ := hR F hF
    refine ⟨φ, (hφ i).2 hi, (hφ j).1 hj, (hφ k).1 hk, ?_, ?_⟩
    · by_cases hl : l ∈ F
      · exact ((hφ l).1 hl).le
      · exact ((hφ l).2 hl).le
    · by_cases hm : m ∈ F
      · exact ((hφ m).1 hm).le
      · exact ((hφ m).2 hm).le
  refine triGenTieO_of_quads (P := x P) (a1 := x a1) (a2 := x a2) (Q := x Q) (b1 := x b1)
    (b2 := x b2) (mem q1 v P a1 a2 hq1)
    (mem q2 v Q b1 b2 hq2)
    (Finset.image_subset_image (Finset.subset_univ _))
    (Finset.image_subset_image (Finset.subset_univ _)) ?_
    (hx.ne hPv) (hx.ne ha1v) (hx.ne ha2v) (hx.ne hQv) (hx.ne hb1v) (hx.ne hb2v) (hx.ne ha1P)
    (hx.ne hb1Q) (hx.ne hb2Q) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← Finset.image_inter _ _ hx, hint, Finset.image_singleton]
  · obtain ⟨F, hF, h1, h2, h3, h4⟩ := Ta1; exact tri F hF v a1 P a2 h1 h2 h3 h4
  · obtain ⟨F, hF, h1, h2, h3, h4⟩ := Ta2; exact tri F hF v a2 P a1 h1 h2 h3 h4
  · obtain ⟨F, hF, h1, h2, h3, h4⟩ := Tb1; exact tri F hF v b1 Q b2 h1 h2 h3 h4
  · obtain ⟨F, hF, h1, h2, h3, h4⟩ := Tb2; exact tri F hF v b2 Q b1 h1 h2 h3 h4
  · obtain ⟨F, hF, h1, h2, h3⟩ := C1; exact crs F hF v a1 b1 P Q h1 h2 h3
  · obtain ⟨F, hF, h1, h2, h3⟩ := C2; exact crs F hF v a1 b2 P Q h1 h2 h3

/-- **Type 07** (`0256`, `1234` at vertex `2`; `6`, `3` opposite `2`, `0`, `5` and `1`, `4` its
neighbours): `TriGenPar` gives `TriGenTieO`.  Case (c) of the triple tie does not occur (Lemma 23.0
(a): the opposite vertices `6`, `3` are not adjacent): the facets `013` and `0346` through `0` and
`1`, resp. `4`, make `1234` one-sided at the triple tie of `6`, `3`. -/
theorem triGenTieO_type07 {x : Fin 7 → ℝ³} (hx : Function.Injective x)
    (hR : RealizesFaces x (sevenTypeFaces 6)) :
    TriGenPar (Finset.univ.image x) (({0, 2, 5, 6} : Finset (Fin 7)).image x)
      (({1, 2, 3, 4} : Finset (Fin 7)).image x) (x 2) →
    TriGenTieO (Finset.univ.image x) (({0, 2, 5, 6} : Finset (Fin 7)).image x)
      (({1, 2, 3, 4} : Finset (Fin 7)).image x) (x 2) :=
  triGenTieO_of_realizes hx hR _ _ 2 6 0 5 3 1 4 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Type 14** (`0235`, `1456` at vertex `5`; `3`, `1` opposite `5`, `0`, `2` and `4`, `6` its
neighbours): `TriGenPar` gives `TriGenTieO`.  Case (c) of the triple tie does not occur (Lemma 23.0
(a): the opposite vertices `3`, `1` are not adjacent): the facets `014` and `016` through `0` and
`4`, resp. `6`, make `1456` one-sided at the triple tie of `3`, `1`. -/
theorem triGenTieO_type14 {x : Fin 7 → ℝ³} (hx : Function.Injective x)
    (hR : RealizesFaces x (sevenTypeFaces 13)) :
    TriGenPar (Finset.univ.image x) (({0, 2, 3, 5} : Finset (Fin 7)).image x)
      (({1, 4, 5, 6} : Finset (Fin 7)).image x) (x 5) →
    TriGenTieO (Finset.univ.image x) (({0, 2, 3, 5} : Finset (Fin 7)).image x)
      (({1, 4, 5, 6} : Finset (Fin 7)).image x) (x 5) :=
  triGenTieO_of_realizes hx hR _ _ 5 3 0 2 1 4 6 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end Minimality

end
