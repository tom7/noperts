module

public import Minimality.Type24SAT.Facets24

@[expose] public section

/-!
# Front facets of a type-24 solid: the isolated front triangle (FRONTCONN24.md)

The two facing patterns of `RimClass24` that local vertex convexity does not refute, front set
exactly `{046, 235}` (facets `{4, 6}`) and exactly `{025, 346}` (`{2, 8}`), are disconnected.
Instead of the topological "front facets form a disk" we use a planar fact about the shadow.

* `vs`: for a front facet `a` and a back facet `b` (at the view `u`) the affine functional
  `-⟪N b, u⟫ f_a + ⟪N a, u⟫ f_b` is constant along `u` (`vsM_perp`), `≤ 0` on all points, `0` on
  `S a ∩ S b` and `< 0` off it: the vertical plane through a silhouette edge supports the solid.
* `front_triangle_isolated` (generic `S0xFac`): if a front facet has three points `A B C` whose three
  edges are silhouette edges (each with a back neighbour through exactly that edge), then no point
  `P` off that facet lies on any silhouette edge.  In the shadow, the three supporting lines put
  every other point strictly inside the triangle `A B C`, and a point strictly inside cannot lie on
  a supporting line.  The proof is one linear dependency of `P - C, A - C, B - C, u` in `ℝ³`
  (`exists_dep4`) and sign bookkeeping (`tri_scalar`); no H-representation or completeness of the
  facet list is needed.
* Type 24: `not_front46`, `not_front28` (the two patterns, from five facing signs each) and
  `not_front68` (`235` and `346` front with `025, 0345, 046, 236` back: the case of the hand proof
  of Theorem FQ).
* Minkowski relation (`kap_sum`, `kap_sign`): `∑ κ t * ⟪N t, w⟫ = 0` with all `κ t` of one strict
  sign, from the closed oriented surface and the orientation chain of `Facets24` (both
  chiralities).  Hence `exists_front` / `exists_back`: at every view with some facet not edge-on,
  some facet is front and some is back.  This is what `RimClass24.nonempty_front_of_FQ` needs.
* `fq_trichotomy`: with `012, 016, 126, 025, 046, 236` back (no facet edge-on), `0345` is front or
  the front set is exactly `{235}` or exactly `{346}`.  The hand Theorem FQ (QUANT-IDEAS-GEMINI 3.2)
  carves out exactly these 3-rim cells; the unconditional `RimClass24.TheoremFQ F u*` is stronger
  and is not proved here (it fails wherever `u*` lies in `T_235` or `T_346`).
-/

set_option autoImplicit false
open scoped RealInnerProductSpace

namespace Minimality.T24.FrontConn
open Minimality Minimality.H21 Minimality.T24.SAT

/-- Four vectors in `ℝ³` are linearly dependent. -/
theorem exists_dep4 (v : Fin 4 → ℝ³) : ∃ c : Fin 4 → ℝ, ∑ i, c i • v i = 0 ∧ ∃ i, c i ≠ 0 := by
  have h : ¬ LinearIndependent ℝ v := by
    intro hli
    have := hli.fintype_card_le_finrank
    simp at this
  exact Fintype.not_linearIndependent_iff.mp h

/-- The sign bookkeeping of `tri_core` for `c0 > 0`. -/
theorem tri_scalar {c0 c1 c2 : ℝ} {a1 p1 b2 p2 p3 q3 a4 b4 q4 : ℝ} (hc0 : 0 < c0)
    (ha1 : a1 < 0) (hp1 : p1 < 0) (hb2 : b2 < 0) (hp2 : p2 < 0) (hp3 : p3 < 0) (hq3 : q3 < 0)
    (ha4 : a4 < 0) (hb4 : b4 < 0) (hq4 : q4 < 0)
    (E1 : c0 * p1 + c1 * a1 = 0) (E2 : c0 * p2 + c2 * b2 = 0)
    (E3 : c0 * (p3 - q3) + c1 * (0 - q3) + c2 * (0 - q3) = 0)
    (E4 : c0 * (0 - q4) + c1 * (a4 - q4) + c2 * (b4 - q4) = 0) : False := by
  have hc1 : c1 < 0 := by
    by_contra h; replace h := not_lt.mp h; nlinarith [mul_nonpos_of_nonneg_of_nonpos h ha1.le, mul_neg_of_pos_of_neg hc0 hp1]
  have hc2 : c2 < 0 := by
    by_contra h; replace h := not_lt.mp h; nlinarith [mul_nonpos_of_nonneg_of_nonpos h hb2.le, mul_neg_of_pos_of_neg hc0 hp2]
  have hs : 0 < c0 + c1 + c2 := by
    by_contra h; replace h := not_lt.mp h
    nlinarith [mul_nonneg_of_nonpos_of_nonpos h hq3.le, mul_neg_of_pos_of_neg hc0 hp3]
  nlinarith [mul_pos hs (neg_pos.mpr hq4), mul_pos_of_neg_of_neg hc1 ha4, mul_pos_of_neg_of_neg hc2 hb4]

/-- **The planar core.**  Four affine functionals constant along `u ≠ 0`: `g1, g2, g3` support the
triangle `A B C` along its edges `BC, AC, AB` and are negative at `P` and at the opposite vertex;
`g4` vanishes at `P` and is negative at `A, B, C`.  Impossible. -/
theorem tri_core {P A B C u : ℝ³} (hu : u ≠ 0) (g1 g2 g3 g4 : ℝ³ → ℝ) (M1 M2 M3 M4 : ℝ³)
    (hg1 : ∀ y z, g1 y - g1 z = ⟪M1, y - z⟫) (hg2 : ∀ y z, g2 y - g2 z = ⟪M2, y - z⟫)
    (hg3 : ∀ y z, g3 y - g3 z = ⟪M3, y - z⟫) (hg4 : ∀ y z, g4 y - g4 z = ⟪M4, y - z⟫)
    (hM1 : ⟪M1, u⟫ = 0) (hM2 : ⟪M2, u⟫ = 0) (hM3 : ⟪M3, u⟫ = 0) (hM4 : ⟪M4, u⟫ = 0)
    (h1B : g1 B = 0) (h1C : g1 C = 0) (h1A : g1 A < 0) (h1P : g1 P < 0)
    (h2A : g2 A = 0) (h2C : g2 C = 0) (h2B : g2 B < 0) (h2P : g2 P < 0)
    (h3A : g3 A = 0) (h3B : g3 B = 0) (h3C : g3 C < 0) (h3P : g3 P < 0)
    (h4P : g4 P = 0) (h4A : g4 A < 0) (h4B : g4 B < 0) (h4C : g4 C < 0) : False := by
  obtain ⟨c, hc, i, hi⟩ := exists_dep4 ![P - C, A - C, B - C, u]
  -- apply a functional constant along `u` to the dependency
  have key : ∀ (g : ℝ³ → ℝ) (M : ℝ³), (∀ y z, g y - g z = ⟪M, y - z⟫) → ⟪M, u⟫ = 0 →
      c 0 * (g P - g C) + c 1 * (g A - g C) + c 2 * (g B - g C) = 0 := by
    intro g M hg hM
    have h := congrArg (fun w => ⟪M, w⟫) hc
    simp only [Fin.sum_univ_four, inner_add_right, real_inner_smul_right, inner_zero_right,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons] at h
    rw [← hg, ← hg, ← hg, hM] at h
    linarith
  have E1 := key g1 M1 hg1 hM1
  have E2 := key g2 M2 hg2 hM2
  have E3 := key g3 M3 hg3 hM3
  have E4 := key g4 M4 hg4 hM4
  rw [h1B, h1C] at E1; rw [h2A, h2C] at E2; rw [h3A, h3B] at E3; rw [h4P] at E4
  rcases lt_trichotomy (c 0) 0 with h0 | h0 | h0
  · exact tri_scalar (c0 := -c 0) (c1 := -c 1) (c2 := -c 2) (neg_pos.mpr h0) h1A h1P h2B h2P h3P h3C
      h4A h4B h4C (by linear_combination -E1) (by linear_combination -E2) (by linear_combination -E3)
      (by linear_combination -E4)
  · rw [h0] at E1 E2
    have hc1 : c 1 = 0 := by
      rcases mul_eq_zero.mp (show c 1 * g1 A = 0 by linarith) with h | h
      · exact h
      · exact absurd h h1A.ne
    have hc2 : c 2 = 0 := by
      rcases mul_eq_zero.mp (show c 2 * g2 B = 0 by linarith) with h | h
      · exact h
      · exact absurd h h2B.ne
    have hc3 : c 3 ≠ 0 := by
      intro h3; apply hi; fin_cases i <;> simp_all
    simp only [Fin.sum_univ_four, h0, hc1, hc2, zero_smul, zero_add, Matrix.cons_val_three,
      Matrix.tail_cons, Matrix.head_cons] at hc
    exact hu ((smul_eq_zero.mp hc).resolve_left hc3)
  · exact tri_scalar (c1 := c 1) (c2 := c 2) h0 h1A h1P h2B h2P h3P h3C h4A h4B h4C (by linear_combination E1)
      (by linear_combination E2) (by linear_combination E3) (by linear_combination E4)

section Generic
variable {n m : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}

/-- The vertical support functional of the edge between the facets `a` and `b` at the view `u`. -/
noncomputable def vs (F : S0xFac m S x) (u : ℝ³) (a b : Fin m) (y : ℝ³) : ℝ :=
  (-⟪F.N b, u⟫) * F.f a y + ⟪F.N a, u⟫ * F.f b y

/-- Its gradient. -/
noncomputable def vsM (F : S0xFac m S x) (u : ℝ³) (a b : Fin m) : ℝ³ :=
  (-⟪F.N b, u⟫) • F.N a + ⟪F.N a, u⟫ • F.N b

theorem vs_sub (F : S0xFac m S x) (u : ℝ³) (a b : Fin m) (y z : ℝ³) :
    vs F u a b y - vs F u a b z = ⟪vsM F u a b, y - z⟫ := by
  simp only [vs, vsM, inner_add_left, real_inner_smul_left, ← F.hN]; ring

theorem vsM_perp (F : S0xFac m S x) (u : ℝ³) (a b : Fin m) : ⟪vsM F u a b, u⟫ = 0 := by
  simp only [vsM, inner_add_left, real_inner_smul_left]; ring

theorem vs_zero (F : S0xFac m S x) (u : ℝ³) {a b : Fin m} {k : Fin n} (ha : k ∈ S a) (hb : k ∈ S b) :
    vs F u a b (x k) = 0 := by
  simp only [vs, F.zero a k ha, F.zero b k hb]; ring

theorem vs_neg (F : S0xFac m S x) {u : ℝ³} {a b : Fin m} (hA : 0 < ⟪F.N a, u⟫) (hB : ⟪F.N b, u⟫ < 0)
    {k : Fin n} (hk : k ∉ S a ∨ k ∉ S b) : vs F u a b (x k) < 0 := by
  have la := F.le a k
  have lb := F.le b k
  unfold vs
  rcases hk with h | h
  · nlinarith [mul_neg_of_pos_of_neg (neg_pos.mpr hB) (F.neg a k h), mul_nonpos_of_nonneg_of_nonpos hA.le lb]
  · nlinarith [mul_neg_of_pos_of_neg hA (F.neg b k h),
      mul_nonpos_of_nonneg_of_nonpos (neg_pos.mpr hB).le la]

/-- **Isolated front triangle.**  `T` is front at `u`; its points `i j k` span three silhouette
edges: `e1` (back) meets `T` along `jk` only, `e2` along `ik`, `e3` along `ij`.  Then no point `p`
off `T` lies on a silhouette edge `P ∩ Q` (`P` front, `Q` back) that misses `i, j, k`. -/
theorem front_triangle_isolated (F : S0xFac m S x) {u : ℝ³} {T e1 e2 e3 P Q : Fin m} {i j k p : Fin n}
    (hT : 0 < ⟪F.N T, u⟫) (h1 : ⟪F.N e1, u⟫ < 0) (h2 : ⟪F.N e2, u⟫ < 0) (h3 : ⟪F.N e3, u⟫ < 0)
    (hP : 0 < ⟪F.N P, u⟫) (hQ : ⟪F.N Q, u⟫ < 0)
    (hiT : i ∈ S T) (hjT : j ∈ S T) (hkT : k ∈ S T) (hpT : p ∉ S T)
    (hj1 : j ∈ S e1) (hk1 : k ∈ S e1) (hi1 : i ∉ S e1)
    (hi2 : i ∈ S e2) (hk2 : k ∈ S e2) (hj2 : j ∉ S e2)
    (hi3 : i ∈ S e3) (hj3 : j ∈ S e3) (hk3 : k ∉ S e3)
    (hpP : p ∈ S P) (hpQ : p ∈ S Q)
    (hiPQ : i ∉ S P ∨ i ∉ S Q) (hjPQ : j ∉ S P ∨ j ∉ S Q) (hkPQ : k ∉ S P ∨ k ∉ S Q) : False := by
  have hu : u ≠ 0 := by rintro rfl; simp at hT
  exact tri_core (P := x p) (A := x i) (B := x j) (C := x k) hu
    (vs F u T e1) (vs F u T e2) (vs F u T e3) (vs F u P Q)
    (vsM F u T e1) (vsM F u T e2) (vsM F u T e3) (vsM F u P Q)
    (vs_sub F u T e1) (vs_sub F u T e2) (vs_sub F u T e3) (vs_sub F u P Q)
    (vsM_perp F u T e1) (vsM_perp F u T e2) (vsM_perp F u T e3) (vsM_perp F u P Q)
    (vs_zero F u hjT hj1) (vs_zero F u hkT hk1) (vs_neg F hT h1 (Or.inr hi1)) (vs_neg F hT h1 (Or.inl hpT))
    (vs_zero F u hiT hi2) (vs_zero F u hkT hk2) (vs_neg F hT h2 (Or.inr hj2)) (vs_neg F hT h2 (Or.inl hpT))
    (vs_zero F u hiT hi3) (vs_zero F u hjT hj3) (vs_neg F hT h3 (Or.inr hk3)) (vs_neg F hT h3 (Or.inl hpT))
    (vs_zero F u hpP hpQ) (vs_neg F hP hQ hiPQ) (vs_neg F hP hQ hjPQ) (vs_neg F hP hQ hkPQ)

end Generic

section Type24
variable {x : Fin 7 → ℝ³}

/-- Front set `{046, 235}` is impossible: `235` is an isolated front triangle (neighbours `0345`,
`025`, `236` back) and `0` lies on the silhouette edge `04` (`046` front, `0345` back). -/
theorem not_front46 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (h4 : 0 < ⟪F.N 4, u⟫) (h6 : 0 < ⟪F.N 6, u⟫)
    (h2 : ⟪F.N 2, u⟫ < 0) (h3 : ⟪F.N 3, u⟫ < 0) (h7 : ⟪F.N 7, u⟫ < 0) : False :=
  front_triangle_isolated F (T := 6) (e1 := 3) (e2 := 2) (e3 := 7) (P := 4) (Q := 3)
    (i := 2) (j := 3) (k := 5) (p := 0) h6 h3 h2 h7 h4 h3
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

/-- Front set `{025, 346}` is impossible: `025` is an isolated front triangle (neighbours `235`,
`0345`, `012` back) and `3` lies on the silhouette edge `34` (`346` front, `0345` back). -/
theorem not_front28 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (h2 : 0 < ⟪F.N 2, u⟫) (h8 : 0 < ⟪F.N 8, u⟫)
    (h0 : ⟪F.N 0, u⟫ < 0) (h3 : ⟪F.N 3, u⟫ < 0) (h6 : ⟪F.N 6, u⟫ < 0) : False :=
  front_triangle_isolated F (T := 2) (e1 := 6) (e2 := 3) (e3 := 0) (P := 8) (Q := 3)
    (i := 0) (j := 2) (k := 5) (p := 3) h2 h6 h3 h0 h8 h3
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

/-- `235` and `346` cannot both be front while `025, 0345, 236, 046` are back: `235` is an isolated
front triangle and `4` lies on the silhouette edge `46` (`346` front, `046` back). -/
theorem not_front68 (F : S0xFac 9 s0x_S24 x) {u : ℝ³}
    (h6 : 0 < ⟪F.N 6, u⟫) (h8 : 0 < ⟪F.N 8, u⟫)
    (h2 : ⟪F.N 2, u⟫ < 0) (h3 : ⟪F.N 3, u⟫ < 0) (h4 : ⟪F.N 4, u⟫ < 0) (h7 : ⟪F.N 7, u⟫ < 0) :
    False :=
  front_triangle_isolated F (T := 6) (e1 := 3) (e2 := 2) (e3 := 7) (P := 8) (Q := 4)
    (i := 2) (j := 3) (k := 5) (p := 4) h6 h3 h2 h7 h8 h4
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

end Type24

/-! ## Some facet is front: the Minkowski relation of type 24

The oriented boundary of the nine facets is a closed surface, so the sum of their oriented area
vectors vanishes (`mink_id`, a polynomial identity).  Each area vector is a multiple of the facet
normal (`det_perp'`), with a coefficient whose sign is the orientation of the facet; the orientation
chain of `Facets24` (`ori24_aux`, and its mirror `ori24_auxN` below for the other chirality) makes
all nine coefficients of one strict sign.  Hence `∑ κ t * ⟪N t, u⟫ = 0` with all `κ t > 0`, and from
every view with a facet not edge-on some facet is front (`exists_front`) and some is back. -/

section Minkowski
variable {y : Fin 7 → ℝ³}

theorem ip3 (a b : ℝ³) : ⟪a, b⟫ = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]; ring

/-- `det A * det B = det (B Aᵀ)` for rows `a b c` and `p q r`. -/
theorem det_gram (a b c p q r : ℝ³) :
    det3 a b c * det3 p q r =
      ⟪p, a⟫ * (⟪q, b⟫ * ⟪r, c⟫ - ⟪q, c⟫ * ⟪r, b⟫) - ⟪p, b⟫ * (⟪q, a⟫ * ⟪r, c⟫ - ⟪q, c⟫ * ⟪r, a⟫) +
        ⟪p, c⟫ * (⟪q, a⟫ * ⟪r, b⟫ - ⟪q, b⟫ * ⟪r, a⟫) := by
  simp only [det3_expand, ip3]; ring

/-- The chirality bracket `[0126]` is never zero (facets `012`, `016`, `046`). -/
theorem chir_ne (F : S0xFac 9 s0x_S24 y) : det3 (y 1 - y 0) (y 2 - y 0) (y 6 - y 0) ≠ 0 := by
  intro h
  have g := det_gram (y 1 - y 0) (y 2 - y 0) (y 6 - y 0) (F.N 0) (F.N 1) (F.N 4)
  simp only [F.inner_sub] at g
  rw [F.zero 0 0 (by decide), F.zero 0 1 (by decide), F.zero 0 2 (by decide), F.zero 1 0 (by decide),
    F.zero 1 1 (by decide), F.zero 1 6 (by decide), F.zero 4 0 (by decide), F.zero 4 6 (by decide),
    h, zero_mul] at g
  have a := F.neg 0 6 (by decide)
  have b := F.neg 1 2 (by decide)
  have c := F.neg 4 1 (by decide)
  have : 0 < F.f 0 (y 6) * F.f 1 (y 2) * F.f 4 (y 1) * -1 := by
    have := mul_pos (mul_pos_of_neg_of_neg a b) (neg_pos.mpr c); linarith
  nlinarith

/-- The orientation chain for the other chirality `[0126] > 0` (`ori24_aux` with all signs flipped). -/
theorem ori24_auxN (F : S0xFac 9 s0x_S24 y) (h : 0 < det3 (y 1 - y 0) (y 2 - y 0) (y 6 - y 0)) :
    0 < (-1:ℝ) * Ar F 0 0 1 2 ∧ 0 < (1:ℝ) * Ar F 1 0 1 6 ∧ 0 < (-1:ℝ) * Ar F 2 0 2 5 ∧
    0 < (-1:ℝ) * Ar F 3 0 3 4 ∧ 0 < (-1:ℝ) * Ar F 4 0 4 6 ∧ 0 < (1:ℝ) * Ar F 5 1 2 6 ∧
    0 < (-1:ℝ) * Ar F 6 2 3 5 ∧ 0 < (1:ℝ) * Ar F 7 2 3 6 ∧ 0 < (1:ℝ) * Ar F 8 3 4 6 := by
  have c0 : 0 < (-1:ℝ) * Ar F 0 0 1 2 := by
    have i := brk_id24 F 0 0 1 2 6 (by decide) (by decide) (by decide)
    have f := off24 F 0 0 6 (by decide) (by decide)
    have n := nn24 F 0
    have : 0 < (-Ar F 0 0 1 2) * ⟪F.N 0, y 0 - y 6⟫ := by
      rw [neg_mul, i]; nlinarith
    rw [neg_one_mul]; exact pos_of_mul_pos_left this f.le
  have c1 : 0 < (1:ℝ) * Ar F 1 0 1 6 :=
    step24 F 0 1 0 1 2 6 0 1 2 0 1 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (-1) (1) (1) (1) (-1) c0 (by ar_eq) (by ar_eq) (by norm_num) (by norm_num)
  have c2 : 0 < (-1:ℝ) * Ar F 2 0 2 5 :=
    step24 F 0 2 0 2 1 5 0 1 2 0 2 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (-1) (-1) (-1) (1) (1) c0 (by ar_eq) (by ar_eq) (by norm_num) (by norm_num)
  have c5 : 0 < (1:ℝ) * Ar F 5 1 2 6 :=
    step24 F 0 5 1 2 0 6 0 1 2 1 2 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (-1) (1) (1) (1) (-1) c0 (by ar_eq) (by ar_eq) (by norm_num) (by norm_num)
  have c4 : 0 < (-1:ℝ) * Ar F 4 0 4 6 :=
    step24 F 1 4 0 6 1 4 0 1 6 0 4 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (1) (-1) (-1) (-1) (-1) c1 (by ar_eq) (by ar_eq) (by norm_num) (by norm_num)
  have c3 : 0 < (-1:ℝ) * Ar F 3 0 3 4 :=
    step24 F 4 3 0 4 6 3 0 4 6 0 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (-1) (-1) (1) (-1) (-1) c4 (by ar_eq) (by ar_eq) (by norm_num) (by norm_num)
  have c8 : 0 < (1:ℝ) * Ar F 8 3 4 6 :=
    step24 F 3 8 3 4 0 6 0 3 4 3 4 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (-1) (1) (1) (1) (-1) c3 (by ar_eq) (by ar_eq) (by norm_num) (by norm_num)
  have c6 : 0 < (-1:ℝ) * Ar F 6 2 3 5 :=
    step24 F 2 6 2 5 0 3 0 2 5 2 3 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (-1) (-1) (1) (-1) (-1) c2 (by ar_eq) (by ar_eq) (by norm_num) (by norm_num)
  have c7 : 0 < (1:ℝ) * Ar F 7 2 3 6 :=
    step24 F 6 7 2 3 5 6 2 3 5 2 3 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (-1) (1) (1) (1) (-1) c6 (by ar_eq) (by ar_eq) (by norm_num) (by norm_num)
  exact ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8⟩

/-- The second triangle `0 3 5` of the quad `0345` is oppositely oriented to `0 3 4` (step from
`235` across the edge `35`), for either chirality. -/
theorem quad_step (F : S0xFac 9 s0x_S24 y) (σ : ℝ) (h6 : 0 < σ * Ar F 6 2 3 5) :
    0 < (-σ) * Ar F 3 0 3 5 :=
  step24 F 6 3 3 5 2 0 2 3 5 0 3 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) σ (-σ) 1 1 σ h6 (by ar_eq) (by ar_eq) (by ring) (by ring)

/-- The closed oriented surface of type 24: the oriented area vectors (against `w`) sum to zero. -/
theorem mink_id (w : ℝ³) :
    det3 (y 1 - y 0) (y 2 - y 0) w - det3 (y 1 - y 0) (y 6 - y 0) w + det3 (y 2 - y 0) (y 5 - y 0) w +
      (det3 (y 3 - y 0) (y 4 - y 0) w - det3 (y 3 - y 0) (y 5 - y 0) w) + det3 (y 4 - y 0) (y 6 - y 0) w -
      det3 (y 2 - y 1) (y 6 - y 1) w + det3 (y 3 - y 2) (y 5 - y 2) w - det3 (y 3 - y 2) (y 6 - y 2) w -
      det3 (y 4 - y 3) (y 6 - y 3) w = 0 := by
  simp only [det3_expand, PiLp.sub_apply]; ring

/-- A facet triple's area against `w`: `[b - a, c - a, w] |N|² = Ar * ⟪N, w⟫`. -/
theorem area_normal (F : S0xFac 9 s0x_S24 y) (t : Fin 9) (a b c : Fin 7) (ha : a ∈ s0x_S24 t)
    (hb : b ∈ s0x_S24 t) (hc : c ∈ s0x_S24 t) (w : ℝ³) :
    det3 (y b - y a) (y c - y a) w = Ar F t a b c / ⟪F.N t, F.N t⟫ * ⟪F.N t, w⟫ := by
  have e := det_perp' (y b - y a) (y c - y a) w (F.N t) (perp24 F t b a hb ha) (perp24 F t c a hc ha)
  have n := (nn24 F t).ne'
  unfold Ar; field_simp; linarith

/-- The Minkowski coefficients (facet area over `|N|²`, oriented by the reference chirality). -/
noncomputable def kap (F : S0xFac 9 s0x_S24 y) : Fin 9 → ℝ :=
  ![Ar F 0 0 1 2 / ⟪F.N 0, F.N 0⟫, -(Ar F 1 0 1 6 / ⟪F.N 1, F.N 1⟫), Ar F 2 0 2 5 / ⟪F.N 2, F.N 2⟫,
    Ar F 3 0 3 4 / ⟪F.N 3, F.N 3⟫ - Ar F 3 0 3 5 / ⟪F.N 3, F.N 3⟫, Ar F 4 0 4 6 / ⟪F.N 4, F.N 4⟫,
    -(Ar F 5 1 2 6 / ⟪F.N 5, F.N 5⟫), Ar F 6 2 3 5 / ⟪F.N 6, F.N 6⟫, -(Ar F 7 2 3 6 / ⟪F.N 7, F.N 7⟫),
    -(Ar F 8 3 4 6 / ⟪F.N 8, F.N 8⟫)]

/-- **Minkowski relation**: `∑ κ t * ⟪N t, w⟫ = 0` for every `w`. -/
theorem kap_sum (F : S0xFac 9 s0x_S24 y) (w : ℝ³) : ∑ t, kap F t * ⟪F.N t, w⟫ = 0 := by
  have m := mink_id (y := y) w
  rw [area_normal F 0 0 1 2 (by decide) (by decide) (by decide), area_normal F 1 0 1 6 (by decide) (by decide) (by decide),
    area_normal F 2 0 2 5 (by decide) (by decide) (by decide), area_normal F 3 0 3 4 (by decide) (by decide) (by decide),
    area_normal F 3 0 3 5 (by decide) (by decide) (by decide), area_normal F 4 0 4 6 (by decide) (by decide) (by decide),
    area_normal F 5 1 2 6 (by decide) (by decide) (by decide), area_normal F 6 2 3 5 (by decide) (by decide) (by decide),
    area_normal F 7 2 3 6 (by decide) (by decide) (by decide), area_normal F 8 3 4 6 (by decide) (by decide) (by decide)] at m
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, kap, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two, add_zero]
  have e3 : (Fin.succ 2 : Fin 9) = 3 := rfl
  have e4 : ((Fin.succ 2).succ : Fin 9) = 4 := rfl
  have e5 : ((Fin.succ 2).succ.succ : Fin 9) = 5 := rfl
  have e6 : ((Fin.succ 2).succ.succ.succ : Fin 9) = 6 := rfl
  have e7 : ((Fin.succ 2).succ.succ.succ.succ : Fin 9) = 7 := rfl
  have e8 : ((Fin.succ 2).succ.succ.succ.succ.succ : Fin 9) = 8 := rfl
  rw [e3, e4, e5, e6, e7, e8]
  linear_combination m

/-- All nine Minkowski coefficients have one strict sign (the chirality). -/
theorem kap_sign (F : S0xFac 9 s0x_S24 y) : (∀ t, 0 < kap F t) ∨ (∀ t, kap F t < 0) := by
  have n : ∀ t, 0 < ⟪F.N t, F.N t⟫ := nn24 F
  rcases lt_or_gt_of_ne (chir_ne F) with h | h
  · obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8⟩ := ori24_aux F h
    have q := quad_step F 1 c6
    simp only [one_mul, neg_one_mul] at c0 c1 c2 c3 c4 c5 c6 c7 c8 q
    left; intro t
    match t with
    | 0 => exact div_pos c0 (n 0)
    | 1 => exact neg_pos.mpr (div_neg_of_neg_of_pos (by linarith) (n 1))
    | 2 => exact div_pos c2 (n 2)
    | 3 => exact sub_pos.mpr ((div_neg_of_neg_of_pos (by linarith) (n 3)).trans (div_pos c3 (n 3)))
    | 4 => exact div_pos c4 (n 4)
    | 5 => exact neg_pos.mpr (div_neg_of_neg_of_pos (by linarith) (n 5))
    | 6 => exact div_pos c6 (n 6)
    | 7 => exact neg_pos.mpr (div_neg_of_neg_of_pos (by linarith) (n 7))
    | 8 => exact neg_pos.mpr (div_neg_of_neg_of_pos (by linarith) (n 8))
  · obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8⟩ := ori24_auxN F h
    have q := quad_step F (-1) c6
    simp only [one_mul, neg_one_mul, neg_neg] at c0 c1 c2 c3 c4 c5 c6 c7 c8 q
    right; intro t
    match t with
    | 0 => exact div_neg_of_neg_of_pos (by linarith) (n 0)
    | 1 => exact neg_neg_iff_pos.mpr (div_pos c1 (n 1))
    | 2 => exact div_neg_of_neg_of_pos (by linarith) (n 2)
    | 3 => exact sub_neg.mpr ((div_neg_of_neg_of_pos (by linarith) (n 3)).trans (div_pos q (n 3)))
    | 4 => exact div_neg_of_neg_of_pos (by linarith) (n 4)
    | 5 => exact neg_neg_iff_pos.mpr (div_pos c5 (n 5))
    | 6 => exact div_neg_of_neg_of_pos (by linarith) (n 6)
    | 7 => exact neg_neg_iff_pos.mpr (div_pos c7 (n 7))
    | 8 => exact neg_neg_iff_pos.mpr (div_pos c8 (n 8))

/-- **Some facet is front** at every view at which some facet is not edge-on (no completeness of
the facet list, no view-specific facts: replaces `TheoremFQ` in `RimClass24.nonempty_front_of_FQ`). -/
theorem exists_front (F : S0xFac 9 s0x_S24 y) (u : ℝ³) (hne : ∃ s, ⟪F.N s, u⟫ ≠ 0) :
    ∃ t, 0 < ⟪F.N t, u⟫ := by
  by_contra hc
  simp only [not_exists, not_lt] at hc
  obtain ⟨s, hs⟩ := hne
  have hsum := kap_sum F u
  rcases kap_sign F with hk | hk
  · have hle : ∀ t ∈ Finset.univ, kap F t * ⟪F.N t, u⟫ ≤ 0 :=
      fun t _ => mul_nonpos_of_nonneg_of_nonpos (hk t).le (hc t)
    rcases mul_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonpos hle).mp hsum s (Finset.mem_univ s)) with h | h
    · exact (hk s).ne' h
    · exact hs h
  · have hge : ∀ t ∈ Finset.univ, 0 ≤ kap F t * ⟪F.N t, u⟫ :=
      fun t _ => mul_nonneg_of_nonpos_of_nonpos (hk t).le (hc t)
    rcases mul_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg hge).mp hsum s (Finset.mem_univ s)) with h | h
    · exact (hk s).ne h
    · exact hs h

/-- Some facet is back (`exists_front` at `-u`). -/
theorem exists_back (F : S0xFac 9 s0x_S24 y) (u : ℝ³) (hne : ∃ s, ⟪F.N s, u⟫ ≠ 0) :
    ∃ t, ⟪F.N t, u⟫ < 0 := by
  obtain ⟨s, hs⟩ := hne
  obtain ⟨t, ht⟩ := exists_front F (-u) ⟨s, by rw [inner_neg_right]; exact neg_ne_zero.mpr hs⟩
  exact ⟨t, by rw [inner_neg_right] at ht; linarith⟩

/-- **What the hand proof of Theorem FQ gives.**  With the corner facets `012, 016, 126` and
`025, 046, 236` back and no facet edge-on, either `0345` is front or the front set is a single
triangle, `{235}` or `{346}` (the 3-rim cells `T_235`, `T_346`, excluded by hand in QUANT-IDEAS-GEMINI
3.2, not refuted). -/
theorem fq_trichotomy (F : S0xFac 9 s0x_S24 y) (u : ℝ³) (hno : ∀ t, ⟪F.N t, u⟫ ≠ 0)
    (h0 : ⟪F.N 0, u⟫ < 0) (h1 : ⟪F.N 1, u⟫ < 0) (h5 : ⟪F.N 5, u⟫ < 0)
    (h2 : ⟪F.N 2, u⟫ < 0) (h4 : ⟪F.N 4, u⟫ < 0) (h7 : ⟪F.N 7, u⟫ < 0) :
    0 < ⟪F.N 3, u⟫ ∨ (0 < ⟪F.N 6, u⟫ ∧ ⟪F.N 3, u⟫ < 0 ∧ ⟪F.N 8, u⟫ < 0) ∨
      (0 < ⟪F.N 8, u⟫ ∧ ⟪F.N 3, u⟫ < 0 ∧ ⟪F.N 6, u⟫ < 0) := by
  rcases lt_or_gt_of_ne (hno 3) with h3 | h3
  · right
    have h68 : ¬ (0 < ⟪F.N 6, u⟫ ∧ 0 < ⟪F.N 8, u⟫) := fun h => not_front68 F h.1 h.2 h2 h3 h4 h7
    obtain ⟨t, ht⟩ := exists_front F u ⟨0, hno 0⟩
    match t with
    | 0 => exact absurd h0 (not_lt.mpr ht.le)
    | 1 => exact absurd h1 (not_lt.mpr ht.le)
    | 2 => exact absurd h2 (not_lt.mpr ht.le)
    | 3 => exact absurd h3 (not_lt.mpr ht.le)
    | 4 => exact absurd h4 (not_lt.mpr ht.le)
    | 5 => exact absurd h5 (not_lt.mpr ht.le)
    | 6 =>
      left
      exact ⟨ht, h3, (lt_or_gt_of_ne (hno 8)).resolve_right fun h8 => h68 ⟨ht, h8⟩⟩
    | 7 => exact absurd h7 (not_lt.mpr ht.le)
    | 8 =>
      right
      exact ⟨ht, h3, (lt_or_gt_of_ne (hno 6)).resolve_right fun h6 => h68 ⟨h6, ht⟩⟩
  · exact Or.inl h3

end Minkowski

end Minimality.T24.FrontConn
