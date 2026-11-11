module

public import Mathlib
public import Minimality.Type21Lemmas

@[expose] public section

/-!
# The Hidden-Cap reduction (Lemma HC, parts (i)-(iii))

Let `v` be a vertex of `K = conv (insert v O)` with three edge vectors `e_a, e_b, e_c`
(independent) to points `a, b, c ∈ O`.

* (i)   a positive combination `u` of three facet normals at `v` has `⟪u, e_k⟫ < 0`
        (`inner_neg_of_normals`);
* (ii)  if the edges are pairwise non-acute, `-u` is a positive combination of `e_a, e_b, e_c`
        whenever `⟪u, e_k⟫ < 0` for all `k` (`exists_pos_comb_of_inner_neg`); the core algebra
        is `pos_of_gram_solve`;
* (iii) at every view `u` in the open cone of `e_a, e_b, e_c`, the point `v` is hidden by `O`
        (`hiddenAt_of_cone`, and `hiddenAt_of_cone_neg` for the opposite orientation); here
        `HiddenAt` is the tree's notion (the image of `v` lies strictly inside every supporting
        line of the shadow of `O`).  No obtuseness is needed for (iii).
-/

set_option autoImplicit false

namespace Minimality

open scoped RealInnerProductSpace
open Finset

/-! ### (i) -/

/-- (i): `u = α n₁ + β n₂ + γ n₃` with `α, β, γ > 0` makes a negative inner product with each
edge `e k`, when every facet normal `n i` is non-positive on every edge and each edge is strictly
negative for some normal. -/
theorem inner_neg_of_normals (n : Fin 3 → ℝ³) (e : Fin 3 → ℝ³) (α : Fin 3 → ℝ)
    (hα : ∀ i, 0 < α i) (hle : ∀ i k, ⟪n i, e k⟫ ≤ 0) (hlt : ∀ k, ∃ i, ⟪n i, e k⟫ < 0)
    (k : Fin 3) : ⟪∑ i, α i • n i, e k⟫ < 0 := by
  rw [sum_inner]
  simp only [real_inner_smul_left]
  obtain ⟨i, hi⟩ := hlt k
  have h1 : ∀ j ∈ (univ : Finset (Fin 3)), α j * ⟪n j, e k⟫ ≤ 0 :=
    fun j _ => mul_nonpos_of_nonneg_of_nonpos (hα j).le (hle j k)
  have h2 : α i * ⟪n i, e k⟫ < 0 := mul_neg_of_pos_of_neg (hα i) hi
  calc ∑ j, α j * ⟪n j, e k⟫ < 0 :=
        lt_of_lt_of_le (Finset.sum_lt_sum h1 ⟨i, mem_univ _, by simpa using h2⟩) (by simp)

/-! ### (ii) -/

/-- Core algebra of (ii): `G c = w` with `w > 0`, `G` symmetric with non-positive off-diagonal
entries and positive definite (as the quadratic form `Q`), then `c > 0`. -/
theorem pos_of_gram_solve (g11 g12 g13 g22 g23 g33 c1 c2 c3 w1 w2 w3 : ℝ)
    (h12 : g12 ≤ 0) (h13 : g13 ≤ 0) (h23 : g23 ≤ 0)
    (hQ : ∀ x y z : ℝ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) →
      0 < g11 * x ^ 2 + g22 * y ^ 2 + g33 * z ^ 2 + 2 * (g12 * x * y + g13 * x * z + g23 * y * z))
    (hw1 : 0 < w1) (hw2 : 0 < w2) (hw3 : 0 < w3)
    (e1 : g11 * c1 + g12 * c2 + g13 * c3 = w1)
    (e2 : g12 * c1 + g22 * c2 + g23 * c3 = w2)
    (e3 : g13 * c1 + g23 * c2 + g33 * c3 = w3) :
    0 < c1 ∧ 0 < c2 ∧ 0 < c3 := by
  have p11 : 0 < g11 := by simpa using hQ 1 0 0 (Or.inl one_ne_zero)
  have p22 : 0 < g22 := by simpa using hQ 0 1 0 (Or.inr (Or.inl one_ne_zero))
  have p33 : 0 < g33 := by simpa using hQ 0 0 1 (Or.inr (Or.inr one_ne_zero))
  -- positive 2x2 minors
  have m23 : 0 < g22 * g33 - g23 ^ 2 := by
    have := hQ 0 g23 (-g22) (Or.inr (Or.inr (by simpa using p22.ne')))
    have h2 : 0 < g22 * (g22 * g33 - g23 ^ 2) := by nlinarith
    exact pos_of_mul_pos_right h2 p22.le
  have m13 : 0 < g11 * g33 - g13 ^ 2 := by
    have := hQ g13 0 (-g11) (Or.inr (Or.inr (by simpa using p11.ne')))
    have h2 : 0 < g11 * (g11 * g33 - g13 ^ 2) := by nlinarith
    exact pos_of_mul_pos_right h2 p11.le
  have m12 : 0 < g11 * g22 - g12 ^ 2 := by
    have := hQ g12 (-g11) 0 (Or.inr (Or.inl (by simpa using p11.ne')))
    have h2 : 0 < g11 * (g11 * g22 - g12 ^ 2) := by nlinarith
    exact pos_of_mul_pos_right h2 p11.le
  -- the determinant
  set D := g11 * (g22 * g33 - g23 ^ 2) - g12 * (g12 * g33 - g13 * g23)
    + g13 * (g12 * g23 - g13 * g22) with hD
  have hDpos : 0 < D := by
    have := hQ (g22 * g33 - g23 ^ 2) (g13 * g23 - g12 * g33) (g12 * g23 - g13 * g22)
      (Or.inl m23.ne')
    have h2 : 0 < D * (g22 * g33 - g23 ^ 2) := by rw [hD]; nlinarith
    exact pos_of_mul_pos_left h2 m23.le
  have a1 : D * c1 = (g22 * g33 - g23 ^ 2) * w1 + (g13 * g23 - g12 * g33) * w2
      + (g12 * g23 - g13 * g22) * w3 := by
    rw [hD, ← e1, ← e2, ← e3]; ring
  have a2 : D * c2 = (g13 * g23 - g12 * g33) * w1 + (g11 * g33 - g13 ^ 2) * w2
      + (g12 * g13 - g11 * g23) * w3 := by
    rw [hD, ← e1, ← e2, ← e3]; ring
  have a3 : D * c3 = (g12 * g23 - g13 * g22) * w1 + (g12 * g13 - g11 * g23) * w2
      + (g11 * g22 - g12 ^ 2) * w3 := by
    rw [hD, ← e1, ← e2, ← e3]; ring
  have o12 : 0 ≤ g13 * g23 - g12 * g33 := by
    nlinarith [mul_nonneg (neg_nonneg.2 h13) (neg_nonneg.2 h23),
      mul_nonneg (neg_nonneg.2 h12) p33.le]
  have o13 : 0 ≤ g12 * g23 - g13 * g22 := by
    nlinarith [mul_nonneg (neg_nonneg.2 h12) (neg_nonneg.2 h23),
      mul_nonneg (neg_nonneg.2 h13) p22.le]
  have o23 : 0 ≤ g12 * g13 - g11 * g23 := by
    nlinarith [mul_nonneg (neg_nonneg.2 h12) (neg_nonneg.2 h13),
      mul_nonneg (neg_nonneg.2 h23) p11.le]
  have t1 := mul_pos m23 hw1
  have t2 := mul_pos m13 hw2
  have t3 := mul_pos m12 hw3
  have u12 := mul_nonneg o12 hw1.le
  have u13 := mul_nonneg o13 hw1.le
  have u21 := mul_nonneg o12 hw2.le
  have u23 := mul_nonneg o23 hw2.le
  have u31 := mul_nonneg o13 hw3.le
  have u32 := mul_nonneg o23 hw3.le
  refine ⟨?_, ?_, ?_⟩
  · refine pos_of_mul_pos_right (a := D) ?_ hDpos.le
    rw [a1]; linarith
  · refine pos_of_mul_pos_right (a := D) ?_ hDpos.le
    rw [a2]; linarith
  · refine pos_of_mul_pos_right (a := D) ?_ hDpos.le
    rw [a3]; linarith

/-- Three independent vectors of `ℝ³` span it. -/
theorem span_of_indep3 {ea eb ec : ℝ³} (hli : LinearIndependent ℝ ![ea, eb, ec]) (y : ℝ³) :
    ∃ x₁ x₂ x₃ : ℝ, y = x₁ • ea + x₂ • eb + x₃ • ec := by
  have hs := hli.span_eq_top_of_card_eq_finrank (by simp)
  have hy : y ∈ Submodule.span ℝ (Set.range ![ea, eb, ec]) := by
    rw [hs]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hy
  refine ⟨c 0, c 1, c 2, ?_⟩
  rw [← hc]; simp [Fin.sum_univ_three]

/-- (ii): if the edges `ea, eb, ec` are independent and pairwise non-acute and `⟪u, e_k⟫ < 0`
for all `k`, then `-u` is a positive combination of the three edges. -/
theorem exists_pos_comb_of_inner_neg {ea eb ec u : ℝ³}
    (hli : LinearIndependent ℝ ![ea, eb, ec])
    (hab : ⟪ea, eb⟫ ≤ 0) (hac : ⟪ea, ec⟫ ≤ 0) (hbc : ⟪eb, ec⟫ ≤ 0)
    (ha : ⟪u, ea⟫ < 0) (hb : ⟪u, eb⟫ < 0) (hc : ⟪u, ec⟫ < 0) :
    ∃ ca cb cc : ℝ, 0 < ca ∧ 0 < cb ∧ 0 < cc ∧ -u = ca • ea + cb • eb + cc • ec := by
  obtain ⟨x₁, x₂, x₃, hx⟩ := span_of_indep3 hli (-u)
  have hQ : ∀ x y z : ℝ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) →
      0 < ⟪ea, ea⟫ * x ^ 2 + ⟪eb, eb⟫ * y ^ 2 + ⟪ec, ec⟫ * z ^ 2 +
        2 * (⟪ea, eb⟫ * x * y + ⟪ea, ec⟫ * x * z + ⟪eb, ec⟫ * y * z) := by
    intro x y z hxyz
    have hne : x • ea + y • eb + z • ec ≠ 0 := by
      intro h0
      have := Fintype.linearIndependent_iff.1 hli ![x, y, z] (by
        simpa [Fin.sum_univ_three] using h0)
      rcases hxyz with h | h | h
      · exact h (by simpa using this 0)
      · exact h (by simpa using this 1)
      · exact h (by simpa using this 2)
    have hpos := real_inner_self_pos.2 hne
    have hexp : ⟪x • ea + y • eb + z • ec, x • ea + y • eb + z • ec⟫ =
        ⟪ea, ea⟫ * x ^ 2 + ⟪eb, eb⟫ * y ^ 2 + ⟪ec, ec⟫ * z ^ 2 +
        2 * (⟪ea, eb⟫ * x * y + ⟪ea, ec⟫ * x * z + ⟪eb, ec⟫ * y * z) := by
      simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
        real_inner_comm ea eb, real_inner_comm ea ec, real_inner_comm eb ec]
      ring
    linarith
  have hu : ∀ e : ℝ³, ⟪-u, e⟫ = -⟪u, e⟫ := fun e => by simp
  have hs : ∀ e : ℝ³, ⟪-u, e⟫ = ⟪x₁ • ea + x₂ • eb + x₃ • ec, e⟫ := fun e => by rw [hx]
  have E : ∀ e : ℝ³, -⟪u, e⟫ = x₁ * ⟪ea, e⟫ + x₂ * ⟪eb, e⟫ + x₃ * ⟪ec, e⟫ := fun e => by
    rw [← hu, hs]; simp only [inner_add_left, real_inner_smul_left]
  obtain ⟨p1, p2, p3⟩ := pos_of_gram_solve ⟪ea, ea⟫ ⟪ea, eb⟫ ⟪ea, ec⟫ ⟪eb, eb⟫ ⟪eb, ec⟫ ⟪ec, ec⟫
    x₁ x₂ x₃ (-⟪u, ea⟫) (-⟪u, eb⟫) (-⟪u, ec⟫) hab hac hbc hQ (by linarith) (by linarith)
    (by linarith)
    (by rw [E ea, real_inner_comm ea eb, real_inner_comm ea ec]; ring)
    (by rw [E eb, real_inner_comm eb ec]; ring)
    (by rw [E ec]; ring)
  exact ⟨x₁, x₂, x₃, p1, p2, p3, hx⟩

/-! ### (iii) -/

/-- Linearity of `det3` in the middle slot over three vectors. -/
theorem det3_comb_mid (P : ℝ³) (x y z : ℝ) (a b c u : ℝ³) :
    det3 P (x • a + y • b + z • c) u = x * det3 P a u + y * det3 P b u + z * det3 P c u := by
  simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

/-- (iii): at a view `u = c_a e_a + c_b e_b + c_c e_c` (`c > 0`), the vertex `v` is hidden by `O`:
its image lies strictly inside every supporting line of the shadow of `O`.  Needs neither
convexity nor obtuseness. -/
theorem hiddenAt_of_cone (O : Finset ℝ³) (v a b c : ℝ³) (ha : a ∈ O) (hb : b ∈ O) (hc : c ∈ O)
    (hli : LinearIndependent ℝ ![a - v, b - v, c - v]) (ca cb cc : ℝ)
    (hca : 0 < ca) (hcb : 0 < cb) (hcc : 0 < cc) :
    HiddenAt O (ca • (a - v) + cb • (b - v) + cc • (c - v)) v := by
  intro A hA B hB h1 h2
  obtain ⟨z0, hz0, hz0pos⟩ := h2
  set u := ca • (a - v) + cb • (b - v) + cc • (c - v) with hu
  by_contra hneg
  rw [not_lt] at hneg
  -- f z = det3 (B - A) (z - A) u ; l y = det3 (B - A) y u
  have split : ∀ z : ℝ³, det3 (B - A) (z - A) u =
      det3 (B - A) (v - A) u + det3 (B - A) (z - v) u := by
    intro z; simp only [det3_expand, PiLp.sub_apply]; ring
  have lk : ∀ z ∈ O, 0 ≤ det3 (B - A) (z - v) u := by
    intro z hz
    have := h1 z hz
    rw [split] at this
    linarith
  have hLu : det3 (B - A) u u = 0 := by
    simp only [det3_expand]; ring
  have hexp : det3 (B - A) u u =
      ca * det3 (B - A) (a - v) u + cb * det3 (B - A) (b - v) u
        + cc * det3 (B - A) (c - v) u := det3_comb_mid _ _ _ _ _ _ _ _
  have la := lk a ha
  have lb := lk b hb
  have lc := lk c hc
  have la0 : det3 (B - A) (a - v) u = 0 := by
    nlinarith [mul_nonneg hca.le la, mul_nonneg hcb.le lb, mul_nonneg hcc.le lc]
  have lb0 : det3 (B - A) (b - v) u = 0 := by
    nlinarith [mul_nonneg hca.le la, mul_nonneg hcb.le lb, mul_nonneg hcc.le lc]
  have lc0 : det3 (B - A) (c - v) u = 0 := by
    nlinarith [mul_nonneg hca.le la, mul_nonneg hcb.le lb, mul_nonneg hcc.le lc]
  obtain ⟨x₁, x₂, x₃, hx⟩ := span_of_indep3 hli (z0 - v)
  have : det3 (B - A) (z0 - v) u = 0 := by
    rw [hx, det3_comb_mid, la0, lb0, lc0]; ring
  rw [split, this] at hz0pos
  linarith

/-- (iii) for the opposite orientation of the view. -/
theorem hiddenAt_of_cone_neg (O : Finset ℝ³) (v a b c : ℝ³) (ha : a ∈ O) (hb : b ∈ O)
    (hc : c ∈ O) (hli : LinearIndependent ℝ ![a - v, b - v, c - v]) (ca cb cc : ℝ)
    (hca : 0 < ca) (hcb : 0 < cb) (hcc : 0 < cc) :
    HiddenAt O (-(ca • (a - v) + cb • (b - v) + cc • (c - v))) v :=
  (hiddenAt_of_cone O v a b c ha hb hc hli ca cb cc hca hcb hcc).neg

/-- Hidden-Cap reduction, assembled: facet normals `n i` at `v` (non-positive on the edges,
each edge strictly negative on one), `u` a positive combination of them, `O ∋ a, b, c` with
independent pairwise non-acute edges `a - v, b - v, c - v`: the vertex `v` is hidden by `O`
at the view `u`. -/
theorem hiddenAt_of_normals (O : Finset ℝ³) (v a b c : ℝ³) (ha : a ∈ O) (hb : b ∈ O) (hc : c ∈ O)
    (hli : LinearIndependent ℝ ![a - v, b - v, c - v])
    (hab : ⟪a - v, b - v⟫ ≤ 0) (hac : ⟪a - v, c - v⟫ ≤ 0) (hbc : ⟪b - v, c - v⟫ ≤ 0)
    (n : Fin 3 → ℝ³) (α : Fin 3 → ℝ) (hα : ∀ i, 0 < α i)
    (hle : ∀ i k, ⟪n i, ![a - v, b - v, c - v] k⟫ ≤ 0)
    (hlt : ∀ k, ∃ i, ⟪n i, ![a - v, b - v, c - v] k⟫ < 0) :
    HiddenAt O (∑ i, α i • n i) v := by
  have h0 := inner_neg_of_normals n ![a - v, b - v, c - v] α hα hle hlt
  obtain ⟨ca, cb, cc, pa, pb, pc, hx⟩ := exists_pos_comb_of_inner_neg hli hab hac hbc
    (by simpa using h0 0) (by simpa using h0 1) (by simpa using h0 2)
  have := hiddenAt_of_cone_neg O v a b c ha hb hc hli ca cb cc pa pb pc
  rwa [← hx, neg_neg] at this

end Minimality

