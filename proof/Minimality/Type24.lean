module

public import Minimality.EdgePair
public import Minimality.Type10
public import Minimality.FewVertices

@[expose] public section

/-!
# Type 24 outside `C̄ ∪ Σ_B` (§15)

`FEWER-FACES-PROOFS.md` §15.  Type 24 has the faces `012, 016, 126` (the cap `1`, of degree
3, with neighbours `0, 2, 6`), the side faces `236, 046, 025`, the quadrilateral `0345`, and
`235, 346`.  The proofs here use only the three cap faces and the three side faces
(`Type24`).

**Oblique coordinates at `1`** (`oblX0`, `oblX2`, `oblX6`, by Cramer's rule): `x v = x 1 +
X0 (x 0 − x 1) + X2 (x 2 − x 1) + X6 (x 6 − x 1)` (`Type24.rep`; the frame determinant
`det24` is nonzero, `Type24.det_ne`).  The cap faces make `X0, X2, X6 > 0` at `3, 4, 5`.
The side face `G_xc` through the axis vertices `x, c`, with apex `g` and third axis vertex
`y`, is the plane `X_x + X_c − ω_xc X_y = 1`, `ω_xc = (X_x(g) + X_c(g) − 1) / X_y(g)`, as in
§15.0: `omega3` (`236`), `omega4` (`046`), `omega5` (`025`); every point satisfies
`X_x + X_c − ω_xc X_y ≤ 1`, strictly off the face (`Type24.side236` and relatives: the face
functional is `f(x 1) (1 − (X_x + X_c − ω X_y))`).  `Δ = ω3 ω4 ω5 − ω3 − ω4 − ω5 − 2`
(`Delta24`); the identity `(ω_g ω_h − 1)(ω_g ω_k − 1) − (1 + ω_g)² = ω_g Δ`
(`omega_identity`), so all `ω > 0` with `Δ ≥ 0` force every product above 1
(`omega_prod_gt_one`).

* **Theorem 15.4, the window triangle** (`isRupert_type24_window`): if some `ω ≤ 0` or some
  `ω_g ω_h < 1` (region W), `K` is Rupert, with no exclusion.  The view
  `e_a + t e_b + ε e_c` (oblique, inside the tangent cone at `1`) sees the silhouette
  `a b c` with `1, 3, 4, 5` strictly inside; Theorem 5 (the coplanar-silhouette theorem,
  `isRupert_of_crossing`) applies to the plane of `0, 2, 6`.  The frame form is
  `isRupert_window_frame`; `ε` is explicit (`1 / (1 + |ω_ab|)`, using the third side face),
  so no limit is needed.
* **Lemma 15.5 and Theorem 15.7, case B** (`isRupert_type24_S6`, `_S2`, `_S0`,
  `isRupert_type24_B`): in region B (all `ω > 0`, all products `≥ 1`, `Δ < 0`), the side
  crossing `S_6 = 046/236` at the view `d⁽⁶⁾ = (1 + ω4, 1 + ω3, ω3 ω4 − 1)` (`view6`) has
  the triangle `(0, 2, 6)` as reduced polygon, `4` and `3` middles over its sides `6 0` and
  `2 6`, and `1, 5` strictly inside (`L(5) = −c₅ Δ`); likewise `S_2 = 025/236` and
  `S_0 = 025/046`.  A triangle with distinct depths is unimodal, so with no horizontal
  double normal Proposition 8.8 with Theorem 7.3 gives a passage (`isRupert_vertexTri`).
  The exclusions are explicit: `S6Free` (product `> 1`, distinct depths of `0, 2, 6` at the
  view, `NoHDNAt` for the triangle) and its relatives.  The frame form is
  `isRupert_sideCrossing_frame`.
* **Corollary 15.8** (`isRupert_type24_outside_Cbar`): a type-24 point set outside
  `C̄ = {ω3, ω4, ω5 > 0, Δ ≥ 0}` is Rupert, unless it is in region B and no side crossing
  is free (the set `Σ_B`).

Not formalized: Lemma 15.2 at ties (an obtuse tie is free; here distinct depths are
assumed), the codimension count of `Σ_B` (Lemma 15.6, 15.7′), §§15.4–15.5 (crossing
certificates near the corner, region `C̄`).
-/

namespace Minimality

open Finset
open scoped RealInnerProductSpace

/-! ### Frames: Cramer's rule, determinants in oblique coordinates -/

/-- Cramer's rule as a vector identity. -/
theorem vol3_smul_cramer (e1 e2 e3 v : ℝ³) :
    vol3 e1 e2 e3 • v = vol3 v e2 e3 • e1 + vol3 e1 v e3 • e2 + vol3 e1 e2 v • e3 := by
  ext i
  fin_cases i <;> simp [vol3] <;> ring

/-- **Oblique coordinates** of `w` in the frame `o; a, b, c` (Cramer's rule). -/
theorem cramer_vec (o a b c w : ℝ³) (hD : vol3 (a - o) (b - o) (c - o) ≠ 0) :
    w = o + (vol3 (w - o) (b - o) (c - o) / vol3 (a - o) (b - o) (c - o)) • (a - o) +
      (vol3 (a - o) (w - o) (c - o) / vol3 (a - o) (b - o) (c - o)) • (b - o) +
      (vol3 (a - o) (b - o) (w - o) / vol3 (a - o) (b - o) (c - o)) • (c - o) := by
  have h := vol3_smul_cramer (a - o) (b - o) (c - o) (w - o)
  set D := vol3 (a - o) (b - o) (c - o)
  have h2 : w - o = D⁻¹ • (D • (w - o)) := by rw [smul_smul, inv_mul_cancel₀ hD, one_smul]
  rw [h, smul_add, smul_add, smul_smul, smul_smul, smul_smul] at h2
  rw [div_eq_inv_mul, div_eq_inv_mul, div_eq_inv_mul]
  conv_lhs => rw [← sub_add_cancel w o, h2]
  abel

/-- The triple product of three combinations of a frame. -/
theorem det3_comb (ea eb ec : ℝ³) (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℝ) :
    det3 (a0 • ea + a1 • eb + a2 • ec) (b0 • ea + b1 • eb + b2 • ec)
        (c0 • ea + c1 • eb + c2 • ec) =
      (a0 * (b1 * c2 - b2 * c1) - a1 * (b0 * c2 - b2 * c0) + a2 * (b0 * c1 - b1 * c0)) *
        vol3 ea eb ec := by
  simp only [det3_expand, vol3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

/-- Cauchy–Binet for `3 × 3`: the determinant of the matrix `⟪N_i, e_j⟫`. -/
theorem vol3_mul_inner (N1 N2 N3 e1 e2 e3 : ℝ³) :
    vol3 N1 N2 N3 * vol3 e1 e2 e3 =
      ⟪N1, e1⟫ * (⟪N2, e2⟫ * ⟪N3, e3⟫ - ⟪N2, e3⟫ * ⟪N3, e2⟫) -
        ⟪N1, e2⟫ * (⟪N2, e1⟫ * ⟪N3, e3⟫ - ⟪N2, e3⟫ * ⟪N3, e1⟫) +
        ⟪N1, e3⟫ * (⟪N2, e1⟫ * ⟪N3, e2⟫ - ⟪N2, e2⟫ * ⟪N3, e1⟫) := by
  simp only [vol3, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
  ring

/-- Screen tests at a view given in oblique coordinates, scaled by the frame determinant:
`det3 (Y − X) (Z − X) u = vol² · (the coordinate determinant)`. -/
theorem det3_frame_view (o ea eb ec X Y Z u : ℝ³) (x0 x1 x2 y0 y1 y2 z0 z1 z2 d0 d1 d2 : ℝ)
    (hX : X = o + x0 • ea + x1 • eb + x2 • ec) (hY : Y = o + y0 • ea + y1 • eb + y2 • ec)
    (hZ : Z = o + z0 • ea + z1 • eb + z2 • ec)
    (hu : u = vol3 ea eb ec • (d0 • ea + d1 • eb + d2 • ec)) :
    det3 (Y - X) (Z - X) u =
      vol3 ea eb ec ^ 2 * ((y0 - x0) * ((z1 - x1) * d2 - (z2 - x2) * d1) -
        (y1 - x1) * ((z0 - x0) * d2 - (z2 - x2) * d0) +
        (y2 - x2) * ((z0 - x0) * d1 - (z1 - x1) * d0)) := by
  have e1 : Y - X = (y0 - x0) • ea + (y1 - x1) • eb + (y2 - x2) • ec := by rw [hX, hY]; module
  have e2 : Z - X = (z0 - x0) • ea + (z1 - x1) • eb + (z2 - x2) • ec := by rw [hX, hZ]; module
  have e3 : det3 (Y - X) (Z - X) u =
      vol3 ea eb ec * det3 (Y - X) (Z - X) (d0 • ea + d1 • eb + d2 • ec) := by
    rw [hu]; simp only [det3, real_inner_smul_right]
  rw [e3, e1, e2, det3_comb]; ring

theorem nodup3 {a b c : ℝ} : [a, b, c].Nodup ↔ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  simp [List.nodup_cons, and_assoc]

/-- No horizontal double normal at `u` means none at `c u` (`c ≠ 0`). -/
theorem NoHDNAt.smul {V : Finset ℝ³} {u : ℝ³} (h : NoHDNAt V u) {c : ℝ} (hc : c ≠ 0) :
    NoHDNAt V (c • u) := by
  intro R hR r hr hRu
  refine h R hR (c⁻¹ * r) (mul_ne_zero (inv_ne_zero hc) hr) ?_
  rw [map_smul] at hRu
  rw [mul_smul, ← hRu, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-! ### A vertex crossing whose reduced polygon is a triangle -/

/-- **A triangle test** (Proposition 8.8 with Theorem 7.3): at the view `u`, the shadow is
the counterclockwise triangle `(p, q, r)`, every point of `V` outside `M` other than the
corners is strictly inside, and every point of `M` is a middle over an open side (at a
different depth).  A triangle with distinct depths is unimodal, so without a horizontal
double normal of the triangle, `V` is Rupert.  (`isRupert_of_vertexView` with the
double-normal exclusion for the triangle only.) -/
theorem isRupert_vertexTri {p q r : ℝ³} (V M : Finset ℝ³) (u : ℝ³)
    (hpV : p ∈ V) (hqV : q ∈ V) (hrV : r ∈ V) (hpM : p ∉ M) (hqM : q ∉ M) (hrM : r ∉ M)
    (hT : 0 < det3 (q - p) (r - p) u)
    (hz : [⟪p, u⟫, ⟪q, u⟫, ⟪r, u⟫].Nodup)
    (hrest : ∀ y ∈ V, y ∉ M → y ≠ p → y ≠ q → y ≠ r → TriHidden u p q r y)
    (hM : ∀ m ∈ M, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      (m = p + s • (q - p) + δ • u ∨ m = q + s • (r - q) + δ • u ∨
        m = r + s • (p - r) + δ • u))
    (hnd : NoHDNAt {p, q, r} u) : IsRupert V := by
  have hu : u ≠ 0 := by
    intro h0; rw [h0] at hT; simp only [det3, inner_zero_right, lt_irrefl] at hT
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hz
  obtain ⟨⟨z1, z2⟩, z3, -⟩ := hz
  obtain ⟨b0, b1, b2⟩ := zmod3_add_one
  have i1 : det3 (r - q) (p - q) u = det3 (q - p) (r - p) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i2 : det3 (p - r) (q - r) u = det3 (q - p) (r - p) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  obtain ⟨R, hR, ρ, hρ, hRu⟩ := exists_rotation_to_ez_pos u hu
  have hxV : ∀ i, tri p q r i ∈ V := by
    intro i; rcases zmod3_cases i with rfl | rfl | rfl
    exacts [hpV, hqV, hrV]
  have hxW : ∀ i, tri p q r i ∈ ({p, q, r} : Finset ℝ³) := by
    intro i; rcases zmod3_cases i with rfl | rfl | rfl <;> simp [tri_0, tri_1, tri_2]
  have hxM : ∀ i, tri p q r i ∉ M := by
    intro i; rcases zmod3_cases i with rfl | rfl | rfl
    exacts [hpM, hqM, hrM]
  have hcyc : ∀ i j : ZMod 3, j ≠ i → j ≠ i + 1 →
      0 < det3 (tri p q r (i + 1) - tri p q r i) (tri p q r j - tri p q r i) u := by
    intro i j hi hj
    rcases zmod3_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [b0, b1, b2, tri_0, tri_1, tri_2, i1, i2]
    exacts [hT, hT, hT]
  have hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (tri p q r i))) := by
    refine ⟨le_rfl, fun i j hi hj => ?_⟩
    simp only [proj_rot_sub]
    exact cross2_proj_rot_pos hR hρ hRu (hcyc i j hi hj)
  have hdepth : ∀ y, (R.toEuclideanLin y) 2 = ρ⁻¹ * ⟪y, u⟫ := by
    intro y
    have : ρ * (R.toEuclideanLin y) 2 = ⟪y, u⟫ := by
      rw [← inner_ez, ← real_inner_smul_right, ← hRu, inner_toEuclideanLin_SO3 hR]
    rw [← this]; field_simp
  refine isRupert_of_chords_unimodal V M R hR hρ hRu (tri p q r) hxV hxM hp ?_ ?_ ?_ ?_
  · intro y hy hyM hyx
    refine hp.mem_interior_of_left fun i => ?_
    simp only [proj_rot_sub]
    refine cross2_proj_rot_pos hR hρ hRu ?_
    have h0 := hyx 0; have h1 := hyx 1; have h2 := hyx 2
    simp only [tri_0, tri_1, tri_2] at h0 h1 h2
    obtain ⟨r1, r2, r3⟩ := hrest y hy hyM h0 h1 h2
    rcases zmod3_cases i with rfl | rfl | rfl <;> simp only [b0, b1, b2, tri_0, tri_1, tri_2]
    exacts [r1, r2, r3]
  · simp only [hdepth]
    have hz3 : IsCyclicUnimodal (fun i => ⟪tri p q r i, u⟫) := by
      rw [tri_inner]; exact isCyclicUnimodal_three (tri_injective z1 z2 z3)
    exact hz3.smul (inv_pos.mpr hρ)
  · exact hnd R hR ρ hρ.ne' hRu 3 (tri p q r) hxW hp
  · intro m hm
    obtain ⟨s, δ, hs0, hs1, hδ, h | h | h⟩ := hM m hm
    · exact ⟨0, s, δ, hs0, hs1, hδ, by simp only [b0, tri_0, tri_1]; exact h⟩
    · exact ⟨1, s, δ, hs0, hs1, hδ, by simp only [b1, tri_1, tri_2]; exact h⟩
    · exact ⟨2, s, δ, hs0, hs1, hδ, by simp only [b2, tri_2, tri_0]; exact h⟩

/-! ### The window triangle in a frame (Theorem 15.4) -/

/-- The window interval: some `t > max (0, ω_bc)` with `t ω_ac < 1`. -/
theorem exists_window_t {wac wbc : ℝ} (h : wac * wbc < 1 ∨ wac ≤ 0 ∨ wbc ≤ 0) :
    ∃ t : ℝ, 0 < t ∧ wbc < t ∧ t * wac < 1 := by
  have m0 := le_max_left 0 wbc
  have m1 := le_max_right 0 wbc
  rcases le_or_gt wac 0 with hac | hac
  · refine ⟨max 0 wbc + 1, by linarith, by linarith, ?_⟩
    nlinarith
  · have hbc : wbc < 1 / wac := by
      rcases h with h | h | h
      · rw [lt_div_iff₀ hac]; linarith [mul_comm wac wbc]
      · linarith
      · have : 0 < 1 / wac := by positivity
        linarith
    have hm : max 0 wbc < 1 / wac := max_lt (by positivity) hbc
    refine ⟨(max 0 wbc + 1 / wac) / 2, by linarith, by linarith, ?_⟩
    rw [← lt_div_iff₀ hac]; linarith

/-- **Theorem 15.4 in a frame** (the window triangle).  In the frame `o; pa, pb, pc` (the
apex `o` with its three neighbours), every other point of `V` is `o` or has oblique
coordinates `A, B, C > 0` beneath the three side planes `B + C − ω_bc A ≤ 1`,
`A + C − ω_ac B ≤ 1`, `A + B − ω_ab C ≤ 1`.  If `ω_ac ω_bc < 1` or `ω_ac ≤ 0` or `ω_bc ≤ 0`,
then at the view `(pa − o) + t (pb − o) + ε (pc − o)` (`ω_bc < t`, `t ω_ac < 1`,
`ε = 1 / (1 + |ω_ab|)`) every other point projects into the interior of the triangle
`pa pb pc`, and `V` is Rupert (Theorem 5). -/
theorem isRupert_window_frame (V : Finset ℝ³) (o pa pb pc : ℝ³)
    (ha : pa ∈ V) (hb : pb ∈ V) (hc : pc ∈ V)
    (hD : vol3 (pa - o) (pb - o) (pc - o) ≠ 0) {wac wbc wab : ℝ}
    (hω : wac * wbc < 1 ∨ wac ≤ 0 ∨ wbc ≤ 0)
    (hV : ∀ v ∈ V, v ≠ pa → v ≠ pb → v ≠ pc → v = o ∨ ∃ A B C : ℝ,
      v = o + A • (pa - o) + B • (pb - o) + C • (pc - o) ∧ 0 < A ∧ 0 < B ∧ 0 < C ∧
      B + C - wbc * A ≤ 1 ∧ A + C - wac * B ≤ 1 ∧ A + B - wab * C ≤ 1) :
    IsRupert V := by
  classical
  obtain ⟨t, ht0, htb, hta⟩ := exists_window_t hω
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = 1 / (1 + |wab|) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hεw : ε * wab < 1 := by
    have h1 : ε * (1 + |wab|) = 1 := by rw [hε]; field_simp
    nlinarith [le_abs_self wab, abs_nonneg wab]
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = 1 + t + ε := ⟨_, rfl⟩
  have hS0 : 0 < S := by rw [hS]; linarith
  obtain ⟨u, hu⟩ : ∃ u : ℝ³, u = (pa - o) + t • (pb - o) + ε • (pc - o) := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℝ³, N = cross (pb - pa) (pc - pa) := ⟨_, rfl⟩
  have hNu : ⟪N, u⟫ = S * vol3 (pa - o) (pb - o) (pc - o) := by
    rw [hN, hu, hS]
    change det3 _ _ _ = _
    simp only [det3_expand, vol3, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hNu0 : ⟪N, u⟫ ≠ 0 := by rw [hNu]; exact mul_ne_zero hS0.ne' hD
  have hN0 : N ≠ 0 := by intro h0; apply hNu0; rw [h0, inner_zero_left]
  have hind : AffineIndependent ℝ ![pa, pb, pc] := by
    rw [hN] at hN0; exact affineIndependent_of_cross_ne_zero hN0
  have hinj := hind.injective
  have hab : pa ≠ pb := fun h => by
    have := @hinj 0 1 (by simp [h]); exact absurd this (by decide)
  have hac : pa ≠ pc := fun h => by
    have := @hinj 0 2 (by simp [h]); exact absurd this (by decide)
  have hbc : pb ≠ pc := fun h => by
    have := @hinj 1 2 (by simp [h]); exact absurd this (by decide)
  have hNb : ⟪N, pb⟫ = ⟪N, pa⟫ := by
    have := inner_cross_left (pb - pa) (pc - pa); rw [← hN, inner_sub_right] at this; linarith
  have hNc : ⟪N, pc⟫ = ⟪N, pa⟫ := by
    have := inner_cross_right (pb - pa) (pc - pa); rw [← hN, inner_sub_right] at this; linarith
  have hWN : ∀ w ∈ ({pa, pb, pc} : Finset ℝ³), ⟪N, w⟫ = ⟪N, pa⟫ := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · rfl
    · exact hNb
    · exact hNc
  have hpa_b : pa ∉ ({pb, pc} : Finset ℝ³) := by simp [hab, hac]
  have hpb_c : pb ∉ ({pc} : Finset ℝ³) := by simp [hbc]
  have hsum : ∀ g : ℝ³ → ℝ, ∑ w ∈ ({pa, pb, pc} : Finset ℝ³), g w = g pa + g pb + g pc := by
    intro g; rw [Finset.sum_insert hpa_b, Finset.sum_insert hpb_c, Finset.sum_singleton,
      add_assoc]
  have hsumv : ∀ g : ℝ³ → ℝ, ∑ w ∈ ({pa, pb, pc} : Finset ℝ³), g w • w =
      g pa • pa + g pb • pb + g pc • pc := by
    intro g; rw [Finset.sum_insert hpa_b, Finset.sum_insert hpb_c, Finset.sum_singleton,
      add_assoc]
  -- the crossing of the line through a point with oblique coordinates `A, B, C`
  have key : ∀ A B C : ℝ, 0 < A * (t + ε) + 1 - B - C → 0 < B * (1 + ε) + t * (1 - A - C) →
      0 < C * (1 + t) + ε * (1 - A - B) →
      ∃ τ : ℝ, ∃ μ : ℝ³ → ℝ, (∀ w ∈ ({pa, pb, pc} : Finset ℝ³), 0 < μ w) ∧
        ∑ w ∈ ({pa, pb, pc} : Finset ℝ³), μ w = 1 ∧
        (o + A • (pa - o) + B • (pb - o) + C • (pc - o)) + τ • u =
          ∑ w ∈ ({pa, pb, pc} : Finset ℝ³), μ w • w := by
    intro A B C h1 h2 h3
    obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = (1 - A - B - C) / S := ⟨_, rfl⟩
    obtain ⟨ma, hma⟩ : ∃ m : ℝ, m = A + τ := ⟨_, rfl⟩
    obtain ⟨mb, hmb⟩ : ∃ m : ℝ, m = B + τ * t := ⟨_, rfl⟩
    obtain ⟨mc, hmc⟩ : ∃ m : ℝ, m = C + τ * ε := ⟨_, rfl⟩
    have pa' : 0 < ma := by
      have e : ma = (A * (t + ε) + 1 - B - C) / S := by
        rw [hma, hτ, hS]; field_simp; ring
      rw [e]; exact div_pos h1 hS0
    have pb' : 0 < mb := by
      have e : mb = (B * (1 + ε) + t * (1 - A - C)) / S := by
        rw [hmb, hτ, hS]; field_simp; ring
      rw [e]; exact div_pos h2 hS0
    have pc' : 0 < mc := by
      have e : mc = (C * (1 + t) + ε * (1 - A - B)) / S := by
        rw [hmc, hτ, hS]; field_simp; ring
      rw [e]; exact div_pos h3 hS0
    have hm1 : 1 = ma + mb + mc := by
      rw [hma, hmb, hmc, hτ, hS]; field_simp; ring
    refine ⟨τ, fun w => if w = pa then ma else if w = pb then mb else mc, ?_, ?_, ?_⟩
    · intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · simp only [ite_true]; exact pa'
      · simp only [Ne.symm hab, ite_true, ite_false]; exact pb'
      · simp only [Ne.symm hac, Ne.symm hbc, ite_false]; exact pc'
    · rw [hsum]
      simp only [ite_true, Ne.symm hab, Ne.symm hac, Ne.symm hbc, ite_false]
      linarith
    · rw [hsumv]
      simp only [ite_true, Ne.symm hab, Ne.symm hac, Ne.symm hbc, ite_false]
      rw [hu, hma, hmb, hmc]
      rw [hma, hmb, hmc] at hm1
      linear_combination (norm := module) hm1 • o
  refine isRupert_of_crossing V {pa, pb, pc}
    (fun w hw => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl <;> assumption)
    N ⟪N, pa⟫ hWN (by simp) (by simp) (by simp) hind u hNu0 ?_
  intro v hv hvW
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hvW
  obtain ⟨h1, h2, h3⟩ := hvW
  rcases hV v hv h1 h2 h3 with rfl | ⟨A, B, C, rfl, hA, hB, hC, s1, s2, s3⟩
  · have e : v = v + (0 : ℝ) • (pa - v) + (0 : ℝ) • (pb - v) + (0 : ℝ) • (pc - v) := by simp
    obtain ⟨τ, μ, hμ, hμ1, hx⟩ := key 0 0 0 (by linarith) (by linarith) (by linarith)
    exact ⟨τ, μ, hμ, hμ1, by rw [← hx, ← e]⟩
  · obtain ⟨τ, μ, hμ, hμ1, hx⟩ := key A B C
      (by nlinarith [mul_pos hA (show 0 < t + ε - wbc by linarith)])
      (by nlinarith [mul_nonneg ht0.le (show 0 ≤ 1 - A - C + wac * B by linarith),
        mul_pos hB (show 0 < 1 + ε - t * wac by linarith)])
      (by nlinarith [mul_nonneg hε0.le (show 0 ≤ 1 - A - B + wab * C by linarith),
        mul_pos hC (show 0 < 1 + t - ε * wab by linarith)])
    exact ⟨τ, μ, hμ, hμ1, hx⟩

/-! ### The side crossings in a frame (Lemma 15.5, Theorem 15.7) -/

/-- The view of the side crossing at the axis vertex `pc` between the side faces
`G_ac` (coefficient `ω_ac`) and `G_bc` (`ω_bc`): oblique direction
`(1 + ω_ac, 1 + ω_bc, ω_ac ω_bc − 1)` in the frame `o; pa, pb, pc`. -/
def sideView (o pa pb pc : ℝ³) (wac wbc : ℝ) : ℝ³ :=
  (1 + wac) • (pa - o) + (1 + wbc) • (pb - o) + (wac * wbc - 1) • (pc - o)

/-- **Lemma 15.5 with Theorem 15.7, in a frame.**  The frame `o; pa, pb, pc`; the side faces
`G_ac` (apex `ga`: `A + C − ω_ac B = 1`), `G_bc` (apex `gb`: `B + C − ω_bc A = 1`) and
`G_ab` (apex `gc`: `A + B − ω_ab C = 1`), each apex strictly beneath the other two side
planes; all `ω > 0`, `ω_ac ω_bc > 1` and `Δ < 0`.  At the view `sideView` (the side
crossing `G_ac / G_bc` at `pc`), the shadow is the triangle `(pa, pb, pc)`, `ga` and `gb`
are middles over its sides `pc pa` and `pb pc`, and `o`, `gc` are strictly inside
(`L(gc) = −C Δ`).  With distinct depths of the corners and no horizontal double normal of
the triangle at the view, `V` is Rupert. -/
theorem isRupert_sideCrossing_frame (V : Finset ℝ³) {o pa pb pc ga gb gc : ℝ³}
    (hV : ∀ y ∈ V, y = o ∨ y = pa ∨ y = pb ∨ y = pc ∨ y = ga ∨ y = gb ∨ y = gc)
    (hpa : pa ∈ V) (hpb : pb ∈ V) (hpc : pc ∈ V)
    (hga : ga ≠ pa ∧ ga ≠ pb ∧ ga ≠ pc) (hgb : gb ≠ pa ∧ gb ≠ pb ∧ gb ≠ pc)
    (hD : vol3 (pa - o) (pb - o) (pc - o) ≠ 0)
    {wac wbc wab : ℝ} (hac : 0 < wac) (hbc : 0 < wbc) (hab : 0 < wab)
    (hprod : 1 < wac * wbc) (hΔ : wac * wbc * wab - wac - wbc - wab - 2 < 0)
    {Aa Ba Ca Ab Bb Cb Ac Bc Cc : ℝ}
    (ea : ga = o + Aa • (pa - o) + Ba • (pb - o) + Ca • (pc - o)) (aB : 0 < Ba)
    (aF : Aa + Ca - wac * Ba = 1) (aS1 : Ba + Ca - wbc * Aa < 1)
    (aS2 : Aa + Ba - wab * Ca < 1)
    (eb : gb = o + Ab • (pa - o) + Bb • (pb - o) + Cb • (pc - o)) (bA : 0 < Ab)
    (bF : Bb + Cb - wbc * Ab = 1) (bS1 : Ab + Cb - wac * Bb < 1)
    (bS2 : Ab + Bb - wab * Cb < 1)
    (ec : gc = o + Ac • (pa - o) + Bc • (pb - o) + Cc • (pc - o)) (cC : 0 < Cc)
    (cF : Ac + Bc - wab * Cc = 1) (cS1 : Bc + Cc - wbc * Ac < 1)
    (cS2 : Ac + Cc - wac * Bc < 1)
    (hz : [⟪pa, sideView o pa pb pc wac wbc⟫, ⟪pb, sideView o pa pb pc wac wbc⟫,
      ⟪pc, sideView o pa pb pc wac wbc⟫].Nodup)
    (hnd : NoHDNAt {pa, pb, pc} (sideView o pa pb pc wac wbc)) : IsRupert V := by
  classical
  obtain ⟨D, hDd⟩ : ∃ D : ℝ, D = vol3 (pa - o) (pb - o) (pc - o) := ⟨_, rfl⟩
  rw [← hDd] at hD
  obtain ⟨w, hw⟩ : ∃ w : ℝ³, w = sideView o pa pb pc wac wbc := ⟨_, rfl⟩
  rw [← hw] at hz hnd
  obtain ⟨u, hu⟩ : ∃ u : ℝ³, u = D • w := ⟨_, rfl⟩
  have hu' : u = vol3 (pa - o) (pb - o) (pc - o) •
      ((1 + wac) • (pa - o) + (1 + wbc) • (pb - o) + (wac * wbc - 1) • (pc - o)) := by
    rw [hu, hDd, hw]; rfl
  have hDD : 0 < vol3 (pa - o) (pb - o) (pc - o) ^ 2 := by rw [← hDd]; positivity
  have dt := fun (X Y Z : ℝ³) (x0 x1 x2 y0 y1 y2 z0 z1 z2 : ℝ) hX hY hZ =>
    det3_frame_view o (pa - o) (pb - o) (pc - o) X Y Z u x0 x1 x2 y0 y1 y2 z0 z1 z2
      (1 + wac) (1 + wbc) (wac * wbc - 1) hX hY hZ hu'
  have rpa : pa = o + (1 : ℝ) • (pa - o) + (0 : ℝ) • (pb - o) + (0 : ℝ) • (pc - o) := by
    module
  have rpb : pb = o + (0 : ℝ) • (pa - o) + (1 : ℝ) • (pb - o) + (0 : ℝ) • (pc - o) := by
    module
  have rpc : pc = o + (0 : ℝ) • (pa - o) + (0 : ℝ) • (pb - o) + (1 : ℝ) • (pc - o) := by
    module
  have ro : o = o + (0 : ℝ) • (pa - o) + (0 : ℝ) • (pb - o) + (0 : ℝ) • (pc - o) := by
    module
  have h1ac : 0 < 1 + wac := by linarith
  have h1bc : 0 < 1 + wbc := by linarith
  have h1ab : 0 < 1 + wab := by linarith
  have hnΔ : 0 < -(wac * wbc * wab - wac - wbc - wab - 2) := by linarith
  -- the triangle and the hidden points
  have hT : 0 < det3 (pb - pa) (pc - pa) u := by
    rw [dt pa pb pc 1 0 0 0 1 0 0 0 1 rpa rpb rpc]
    apply mul_pos hDD; linarith
  have hid : ∀ y A B C, y = o + A • (pa - o) + B • (pb - o) + C • (pc - o) →
      0 < C * (2 + wac + wbc) - (A + B - 1) * (wac * wbc - 1) →
      B + C - wbc * A < 1 → A + C - wac * B < 1 → TriHidden u pa pb pc y := by
    intro y A B C hy t1 t2 t3
    refine ⟨?_, ?_, ?_⟩
    · rw [dt pa pb y 1 0 0 0 1 0 A B C rpa rpb hy]
      apply mul_pos hDD; linarith
    · rw [dt pb pc y 0 1 0 0 0 1 A B C rpb rpc hy]
      apply mul_pos hDD; linarith [mul_pos h1ac (show 0 < 1 - (B + C - wbc * A) by linarith)]
    · rw [dt pc pa y 0 0 1 1 0 0 A B C rpc rpa hy]
      apply mul_pos hDD; linarith [mul_pos h1bc (show 0 < 1 - (A + C - wac * B) by linarith)]
  have hido : TriHidden u pa pb pc o :=
    hid o 0 0 0 ro (by linarith) (by linarith) (by linarith)
  have hidc : TriHidden u pa pb pc gc := by
    refine hid gc Ac Bc Cc ec ?_ cS1 cS2
    have e : Cc * (2 + wac + wbc) - (Ac + Bc - 1) * (wac * wbc - 1) =
        Cc * -(wac * wbc * wab - wac - wbc - wab - 2) := by
      linear_combination (-(wac * wbc - 1)) * cF
    rw [e]; exact mul_pos cC hnΔ
  -- the middles
  set M := V.filter (fun y => y = ga ∨ y = gb) with hM
  have hpaM : pa ∉ M := by
    intro h; rcases (mem_filter.mp h).2 with e | e
    exacts [hga.1 e.symm, hgb.1 e.symm]
  have hpbM : pb ∉ M := by
    intro h; rcases (mem_filter.mp h).2 with e | e
    exacts [hga.2.1 e.symm, hgb.2.1 e.symm]
  have hpcM : pc ∉ M := by
    intro h; rcases (mem_filter.mp h).2 with e | e
    exacts [hga.2.2 e.symm, hgb.2.2 e.symm]
  have hDu : ∀ δ' : ℝ, (δ' / D) • u = δ' • w := by
    intro δ'; rw [hu, smul_smul, div_mul_cancel₀ _ hD]
  have hmid : ∀ m ∈ M, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      (m = pa + s • (pb - pa) + δ • u ∨ m = pb + s • (pc - pb) + δ • u ∨
        m = pc + s • (pa - pc) + δ • u) := by
    intro m hm
    rcases (mem_filter.mp hm).2 with rfl | rfl
    · -- `ga`, over the side `pc pa`
      have hCa : Ca = 1 - Aa + wac * Ba := by linarith
      subst hCa
      have k1 : Ba * (1 + wac) < Aa * (1 + wbc) := by linarith
      have k2 : (Aa - 1) * (1 + wab) + Ba * (1 - wab * wac) < 0 := by linarith
      have k3 : (1 + wab) * ((1 + wbc) * (Aa - 1) - Ba * (1 + wac)) < 0 := by
        linarith [mul_lt_mul_of_pos_left k2 h1bc, mul_pos aB hnΔ]
      have k4 : (1 + wbc) * (Aa - 1) - Ba * (1 + wac) < 0 := by
        by_contra hk; push Not at hk; linarith [mul_nonneg h1ab.le hk]
      refine ⟨(Aa * (1 + wbc) - Ba * (1 + wac)) / (1 + wbc), (Ba / (1 + wbc)) / D,
        div_pos (by linarith) h1bc, ?_, div_ne_zero (div_pos aB h1bc).ne' hD,
        Or.inr (Or.inr ?_)⟩
      · rw [div_lt_one h1bc]; linarith
      · rw [hDu, hw, ea, sideView]
        have h1 : Aa = (Aa * (1 + wbc) - Ba * (1 + wac)) / (1 + wbc) +
            Ba / (1 + wbc) * (1 + wac) := by field_simp; ring
        have h2 : Ba = Ba / (1 + wbc) * (1 + wbc) := by field_simp
        have h3 : 1 - Aa + wac * Ba = 1 - (Aa * (1 + wbc) - Ba * (1 + wac)) / (1 + wbc) +
            Ba / (1 + wbc) * (wac * wbc - 1) := by field_simp; ring
        linear_combination (norm := module) h1 • (pa - o) + h2 • (pb - o) + h3 • (pc - o)
    · -- `gb`, over the side `pb pc`
      have hCb : Cb = 1 - Bb + wbc * Ab := by linarith
      subst hCb
      have k1 : Ab * (1 + wbc) < Bb * (1 + wac) := by linarith
      have k2 : (Bb - 1) * (1 + wab) + Ab * (1 - wab * wbc) < 0 := by linarith
      have k3 : (1 + wab) * ((1 + wac) * (Bb - 1) - Ab * (1 + wbc)) < 0 := by
        linarith [mul_lt_mul_of_pos_left k2 h1ac, mul_pos bA hnΔ]
      have k4 : (1 + wac) * (Bb - 1) - Ab * (1 + wbc) < 0 := by
        by_contra hk; push Not at hk; linarith [mul_nonneg h1ab.le hk]
      refine ⟨((1 - Bb) * (1 + wac) + Ab * (1 + wbc)) / (1 + wac), (Ab / (1 + wac)) / D,
        div_pos (by linarith) h1ac, ?_, div_ne_zero (div_pos bA h1ac).ne' hD,
        Or.inr (Or.inl ?_)⟩
      · rw [div_lt_one h1ac]; linarith
      · rw [hDu, hw, eb, sideView]
        have h1 : Ab = Ab / (1 + wac) * (1 + wac) := by field_simp
        have h2 : Bb = 1 - ((1 - Bb) * (1 + wac) + Ab * (1 + wbc)) / (1 + wac) +
            Ab / (1 + wac) * (1 + wbc) := by field_simp; ring
        have h3 : 1 - Bb + wbc * Ab = ((1 - Bb) * (1 + wac) + Ab * (1 + wbc)) / (1 + wac) +
            Ab / (1 + wac) * (wac * wbc - 1) := by field_simp; ring
        linear_combination (norm := module) h1 • (pa - o) + h2 • (pb - o) + h3 • (pc - o)
  -- depths and double normals at `u = D w`
  have hz' : [⟪pa, u⟫, ⟪pb, u⟫, ⟪pc, u⟫].Nodup := by
    rw [nodup3] at hz ⊢
    obtain ⟨z1, z2, z3⟩ := hz
    simp only [hu, real_inner_smul_right]
    exact ⟨fun h => z1 (mul_left_cancel₀ hD h), fun h => z2 (mul_left_cancel₀ hD h),
      fun h => z3 (mul_left_cancel₀ hD h)⟩
  have hnd' : NoHDNAt {pa, pb, pc} u := by rw [hu]; exact hnd.smul hD
  refine isRupert_vertexTri V M u hpa hpb hpc hpaM hpbM hpcM hT hz' ?_ hmid hnd'
  intro y hy hyM h1 h2 h3
  rcases hV y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hido
  · exact absurd rfl h1
  · exact absurd rfl h2
  · exact absurd rfl h3
  · exact absurd (mem_filter.mpr ⟨hy, Or.inl rfl⟩) hyM
  · exact absurd (mem_filter.mpr ⟨hy, Or.inr rfl⟩) hyM
  · exact hidc

/-! ### Type 24 -/

/-- A face of `x` from a set of labels (`Face16`): two labels on different sides of it give
different points. -/
theorem Face16.mem_iff {x : Fin 7 → ℝ³} {S : Finset (Fin 7)} (F : Face16 x S) {i j : Fin 7}
    (h : x i = x j) : i ∈ S ↔ j ∈ S := by
  constructor
  · intro hi; by_contra hj
    have := F.neg j hj; rw [← h, F.zero i hi] at this; exact lt_irrefl _ this
  · intro hj; by_contra hi
    have := F.neg i hi; rw [h, F.zero j hj] at this; exact lt_irrefl _ this

/-- **Type 24**, the faces used in §15: the cap faces `012`, `016`, `126` at the vertex `1`
and the side faces `236`, `046`, `025` (the quadrilateral `0345` and the faces `235`, `346`
are not needed), each given by an affine function vanishing on it and negative at the
other points. -/
structure Type24 (x : Fin 7 → ℝ³) where
  t012 : Face16 x {0, 1, 2}
  t016 : Face16 x {0, 1, 6}
  t126 : Face16 x {1, 2, 6}
  t236 : Face16 x {2, 3, 6}
  t046 : Face16 x {0, 4, 6}
  t025 : Face16 x {0, 2, 5}

/-- Type 24 from affine functionals. -/
noncomputable def Type24.ofAffine (x : Fin 7 → ℝ³) (fA fB fC fD fE fF : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 1, 2} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 1, 2} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({0, 1, 6} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({0, 1, 6} : Finset (Fin 7)) → fB (x i) < 0))
    (hC : ∀ i, (i ∈ ({1, 2, 6} : Finset (Fin 7)) → fC (x i) = 0) ∧
      (i ∉ ({1, 2, 6} : Finset (Fin 7)) → fC (x i) < 0))
    (hD : ∀ i, (i ∈ ({2, 3, 6} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({2, 3, 6} : Finset (Fin 7)) → fD (x i) < 0))
    (hE : ∀ i, (i ∈ ({0, 4, 6} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({0, 4, 6} : Finset (Fin 7)) → fE (x i) < 0))
    (hF : ∀ i, (i ∈ ({0, 2, 5} : Finset (Fin 7)) → fF (x i) = 0) ∧
      (i ∉ ({0, 2, 5} : Finset (Fin 7)) → fF (x i) < 0)) : Type24 x :=
  ⟨Face16.ofAffine fA hA, Face16.ofAffine fB hB, Face16.ofAffine fC hC, Face16.ofAffine fD hD,
    Face16.ofAffine fE hE, Face16.ofAffine fF hF⟩

/-- The six faces separate the seven points. -/
theorem Type24.inj {x : Fin 7 → ℝ³} (T : Type24 x) : Function.Injective x := by
  intro i j h
  have key : ∀ i j : Fin 7,
      (i ∈ ({0, 1, 2} : Finset (Fin 7)) ↔ j ∈ ({0, 1, 2} : Finset (Fin 7))) →
      (i ∈ ({0, 1, 6} : Finset (Fin 7)) ↔ j ∈ ({0, 1, 6} : Finset (Fin 7))) →
      (i ∈ ({1, 2, 6} : Finset (Fin 7)) ↔ j ∈ ({1, 2, 6} : Finset (Fin 7))) →
      (i ∈ ({2, 3, 6} : Finset (Fin 7)) ↔ j ∈ ({2, 3, 6} : Finset (Fin 7))) →
      (i ∈ ({0, 4, 6} : Finset (Fin 7)) ↔ j ∈ ({0, 4, 6} : Finset (Fin 7))) →
      (i ∈ ({0, 2, 5} : Finset (Fin 7)) ↔ j ∈ ({0, 2, 5} : Finset (Fin 7))) → i = j := by
    decide
  exact key i j (T.t012.mem_iff h) (T.t016.mem_iff h) (T.t126.mem_iff h) (T.t236.mem_iff h)
    (T.t046.mem_iff h) (T.t025.mem_iff h)

/-- The frame determinant at `1`: `[x 0 − x 1, x 2 − x 1, x 6 − x 1]`. -/
noncomputable def det24 (x : Fin 7 → ℝ³) : ℝ := vol3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)

/-- The oblique coordinate along `x 0 − x 1` (axis `a`), by Cramer's rule. -/
noncomputable def oblX0 (x : Fin 7 → ℝ³) (v : Fin 7) : ℝ :=
  vol3 (x v - x 1) (x 2 - x 1) (x 6 - x 1) / det24 x

/-- The oblique coordinate along `x 2 − x 1` (axis `b`). -/
noncomputable def oblX2 (x : Fin 7 → ℝ³) (v : Fin 7) : ℝ :=
  vol3 (x 0 - x 1) (x v - x 1) (x 6 - x 1) / det24 x

/-- The oblique coordinate along `x 6 − x 1` (axis `c`). -/
noncomputable def oblX6 (x : Fin 7 → ℝ³) (v : Fin 7) : ℝ :=
  vol3 (x 0 - x 1) (x 2 - x 1) (x v - x 1) / det24 x

/-- `ω3 = ω_26` of the side face `236` (apex `3`): `(X2(3) + X6(3) − 1) / X0(3)`. -/
noncomputable def omega3 (x : Fin 7 → ℝ³) : ℝ := (oblX2 x 3 + oblX6 x 3 - 1) / oblX0 x 3

/-- `ω4 = ω_06` of the side face `046` (apex `4`): `(X0(4) + X6(4) − 1) / X2(4)`. -/
noncomputable def omega4 (x : Fin 7 → ℝ³) : ℝ := (oblX0 x 4 + oblX6 x 4 - 1) / oblX2 x 4

/-- `ω5 = ω_02` of the side face `025` (apex `5`): `(X0(5) + X2(5) − 1) / X6(5)`. -/
noncomputable def omega5 (x : Fin 7 → ℝ³) : ℝ := (oblX0 x 5 + oblX2 x 5 - 1) / oblX6 x 5

/-- `Δ = ω3 ω4 ω5 − ω3 − ω4 − ω5 − 2`. -/
noncomputable def Delta24 (x : Fin 7 → ℝ³) : ℝ :=
  omega3 x * omega4 x * omega5 x - omega3 x - omega4 x - omega5 x - 2

/-- **The identity of §15.0**: `(ω_g ω_h − 1)(ω_g ω_k − 1) − (1 + ω_g)² = ω_g Δ`. -/
theorem omega_identity (a b c : ℝ) :
    (a * b - 1) * (a * c - 1) - (1 + a) ^ 2 = a * (a * b * c - a - b - c - 2) := by
  ring

/-- If all `ω > 0` and `Δ ≥ 0`, every product `ω_g ω_h` exceeds 1. -/
theorem omega_prod_gt_one {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hΔ : 0 ≤ a * b * c - a - b - c - 2) : 1 < a * b := by
  by_contra h; push Not at h
  nlinarith [mul_nonneg hc.le (show 0 ≤ 1 - a * b by linarith)]

namespace Type24

theorem f_eq_inner {x : Fin 7 → ℝ³} {S : Finset (Fin 7)} (F : Face16 x S) (i j : Fin 7) :
    ⟪F.N, x i - x j⟫ = F.f (x i) - F.f (x j) := (F.hN (x i) (x j)).symm

theorem f_le {x : Fin 7 → ℝ³} {S : Finset (Fin 7)} (F : Face16 x S) (v : Fin 7) :
    F.f (x v) ≤ 0 := by
  by_cases h : v ∈ S
  · exact (F.zero v h).le
  · exact (F.neg v h).le

theorem mem {x : Fin 7 → ℝ³} (i : Fin 7) : x i ∈ univ.image x := mem_image_of_mem x (mem_univ i)

variable {x : Fin 7 → ℝ³} (T : Type24 x)
include T

/-- The frame at `1` is nondegenerate: the cap faces give the matrix `⟪N_i, e_j⟫` a
nonzero diagonal and zeros elsewhere (Cauchy–Binet). -/
theorem det_ne : det24 x ≠ 0 := by
  have e := vol3_mul_inner T.t126.N T.t016.N T.t012.N (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)
  simp only [f_eq_inner] at e
  have z := fun {S : Finset (Fin 7)} (F : Face16 x S) (i : Fin 7) (h : i ∈ S) => F.zero i h
  rw [z T.t126 1 (by decide), z T.t126 2 (by decide), z T.t126 6 (by decide),
    z T.t016 0 (by decide), z T.t016 1 (by decide), z T.t016 6 (by decide),
    z T.t012 0 (by decide), z T.t012 1 (by decide), z T.t012 2 (by decide)] at e
  have h1 := T.t126.neg 0 (by decide)
  have h2 := T.t016.neg 2 (by decide)
  have h3 := T.t012.neg 6 (by decide)
  intro h0
  rw [det24] at h0
  rw [h0, mul_zero] at e
  have : T.t126.f (x 0) * (T.t016.f (x 2) * T.t012.f (x 6)) = 0 := by linear_combination -e
  rcases mul_eq_zero.mp this with h | h
  · linarith
  rcases mul_eq_zero.mp h with h | h <;> linarith

/-- The oblique coordinates at `1`. -/
theorem rep (v : Fin 7) : x v = x 1 + oblX0 x v • (x 0 - x 1) + oblX2 x v • (x 2 - x 1) +
    oblX6 x v • (x 6 - x 1) :=
  cramer_vec (x 1) (x 0) (x 2) (x 6) (x v) T.det_ne

/-- A face functional in oblique coordinates. -/
theorem eval {S : Finset (Fin 7)} (F : Face16 x S) (v : Fin 7) :
    F.f (x v) = F.f (x 1) + oblX0 x v * (F.f (x 0) - F.f (x 1)) +
      oblX2 x v * (F.f (x 2) - F.f (x 1)) + oblX6 x v * (F.f (x 6) - F.f (x 1)) := by
  conv_lhs => rw [T.rep v]
  exact affine_frame3 F.hN _ _ _ _ _ _ _

/-- Off the cap face `126`, `X0 > 0`. -/
theorem X0_pos {v : Fin 7} (hv : v ∉ ({1, 2, 6} : Finset (Fin 7))) : 0 < oblX0 x v := by
  have e := T.eval T.t126 v
  rw [T.t126.zero 1 (by decide), T.t126.zero 2 (by decide), T.t126.zero 6 (by decide)] at e
  have h0 := T.t126.neg 0 (by decide)
  have hv' := T.t126.neg v hv
  nlinarith

/-- Off the cap face `016`, `X2 > 0`. -/
theorem X2_pos {v : Fin 7} (hv : v ∉ ({0, 1, 6} : Finset (Fin 7))) : 0 < oblX2 x v := by
  have e := T.eval T.t016 v
  rw [T.t016.zero 0 (by decide), T.t016.zero 1 (by decide), T.t016.zero 6 (by decide)] at e
  have h0 := T.t016.neg 2 (by decide)
  have hv' := T.t016.neg v hv
  nlinarith

/-- Off the cap face `012`, `X6 > 0`. -/
theorem X6_pos {v : Fin 7} (hv : v ∉ ({0, 1, 2} : Finset (Fin 7))) : 0 < oblX6 x v := by
  have e := T.eval T.t012 v
  rw [T.t012.zero 0 (by decide), T.t012.zero 1 (by decide), T.t012.zero 2 (by decide)] at e
  have h0 := T.t012.neg 6 (by decide)
  have hv' := T.t012.neg v hv
  nlinarith

/-- The apex `3` lies on `X2 + X6 − ω3 X0 = 1`. -/
theorem eq3 : oblX2 x 3 + oblX6 x 3 - omega3 x * oblX0 x 3 = 1 := by
  have h := T.X0_pos (v := 3) (by decide)
  rw [omega3, div_mul_cancel₀ _ h.ne']; ring

/-- The apex `4` lies on `X0 + X6 − ω4 X2 = 1`. -/
theorem eq4 : oblX0 x 4 + oblX6 x 4 - omega4 x * oblX2 x 4 = 1 := by
  have h := T.X2_pos (v := 4) (by decide)
  rw [omega4, div_mul_cancel₀ _ h.ne']; ring

/-- The apex `5` lies on `X0 + X2 − ω5 X6 = 1`. -/
theorem eq5 : oblX0 x 5 + oblX2 x 5 - omega5 x * oblX6 x 5 = 1 := by
  have h := T.X6_pos (v := 5) (by decide)
  rw [omega5, div_mul_cancel₀ _ h.ne']; ring

/-- **The side face `236` in oblique coordinates**: its functional is
`f(x 1) (1 − (X2 + X6 − ω3 X0))`. -/
theorem side236 (v : Fin 7) :
    T.t236.f (x v) = T.t236.f (x 1) * (1 - (oblX2 x v + oblX6 x v - omega3 x * oblX0 x v)) := by
  have e := T.eval T.t236 v
  have e3 := T.eval T.t236 3
  rw [T.t236.zero 2 (by decide), T.t236.zero 6 (by decide)] at e e3
  rw [T.t236.zero 3 (by decide)] at e3
  have h3 := T.eq3
  have hX := T.X0_pos (v := 3) (by decide)
  have k : (T.t236.f (x 0) - T.t236.f (x 1) - omega3 x * T.t236.f (x 1)) * oblX0 x 3 = 0 := by
    linear_combination -e3 + T.t236.f (x 1) * h3
  have k' : T.t236.f (x 0) - T.t236.f (x 1) - omega3 x * T.t236.f (x 1) = 0 := by
    rcases mul_eq_zero.mp k with h | h
    · exact h
    · exact absurd h hX.ne'
  rw [e]; linear_combination oblX0 x v * k'

/-- The side face `046`: `f(x 1) (1 − (X0 + X6 − ω4 X2))`. -/
theorem side046 (v : Fin 7) :
    T.t046.f (x v) = T.t046.f (x 1) * (1 - (oblX0 x v + oblX6 x v - omega4 x * oblX2 x v)) := by
  have e := T.eval T.t046 v
  have e4 := T.eval T.t046 4
  rw [T.t046.zero 0 (by decide), T.t046.zero 6 (by decide)] at e e4
  rw [T.t046.zero 4 (by decide)] at e4
  have h4 := T.eq4
  have hX := T.X2_pos (v := 4) (by decide)
  have k : (T.t046.f (x 2) - T.t046.f (x 1) - omega4 x * T.t046.f (x 1)) * oblX2 x 4 = 0 := by
    linear_combination -e4 + T.t046.f (x 1) * h4
  have k' : T.t046.f (x 2) - T.t046.f (x 1) - omega4 x * T.t046.f (x 1) = 0 := by
    rcases mul_eq_zero.mp k with h | h
    · exact h
    · exact absurd h hX.ne'
  rw [e]; linear_combination oblX2 x v * k'

/-- The side face `025`: `f(x 1) (1 − (X0 + X2 − ω5 X6))`. -/
theorem side025 (v : Fin 7) :
    T.t025.f (x v) = T.t025.f (x 1) * (1 - (oblX0 x v + oblX2 x v - omega5 x * oblX6 x v)) := by
  have e := T.eval T.t025 v
  have e5 := T.eval T.t025 5
  rw [T.t025.zero 0 (by decide), T.t025.zero 2 (by decide)] at e e5
  rw [T.t025.zero 5 (by decide)] at e5
  have h5 := T.eq5
  have hX := T.X6_pos (v := 5) (by decide)
  have k : (T.t025.f (x 6) - T.t025.f (x 1) - omega5 x * T.t025.f (x 1)) * oblX6 x 5 = 0 := by
    linear_combination -e5 + T.t025.f (x 1) * h5
  have k' : T.t025.f (x 6) - T.t025.f (x 1) - omega5 x * T.t025.f (x 1) = 0 := by
    rcases mul_eq_zero.mp k with h | h
    · exact h
    · exact absurd h hX.ne'
  rw [e]; linear_combination oblX6 x v * k'

/-- Every point is beneath the plane of `236`. -/
theorem le236 (v : Fin 7) : oblX2 x v + oblX6 x v - omega3 x * oblX0 x v ≤ 1 := by
  have e := T.side236 v
  have h1 := T.t236.neg 1 (by decide)
  have h := f_le T.t236 v
  nlinarith

theorem lt236 {v : Fin 7} (hv : v ∉ ({2, 3, 6} : Finset (Fin 7))) :
    oblX2 x v + oblX6 x v - omega3 x * oblX0 x v < 1 := by
  have e := T.side236 v
  have h1 := T.t236.neg 1 (by decide)
  have h := T.t236.neg v hv
  nlinarith

theorem le046 (v : Fin 7) : oblX0 x v + oblX6 x v - omega4 x * oblX2 x v ≤ 1 := by
  have e := T.side046 v
  have h1 := T.t046.neg 1 (by decide)
  have h := f_le T.t046 v
  nlinarith

theorem lt046 {v : Fin 7} (hv : v ∉ ({0, 4, 6} : Finset (Fin 7))) :
    oblX0 x v + oblX6 x v - omega4 x * oblX2 x v < 1 := by
  have e := T.side046 v
  have h1 := T.t046.neg 1 (by decide)
  have h := T.t046.neg v hv
  nlinarith

theorem le025 (v : Fin 7) : oblX0 x v + oblX2 x v - omega5 x * oblX6 x v ≤ 1 := by
  have e := T.side025 v
  have h1 := T.t025.neg 1 (by decide)
  have h := f_le T.t025 v
  nlinarith

theorem lt025 {v : Fin 7} (hv : v ∉ ({0, 2, 5} : Finset (Fin 7))) :
    oblX0 x v + oblX2 x v - omega5 x * oblX6 x v < 1 := by
  have e := T.side025 v
  have h1 := T.t025.neg 1 (by decide)
  have h := T.t025.neg v hv
  nlinarith

/-- The oblique coordinates in the frame `x 1; x 0, x 6, x 2`. -/
theorem rep062 (v : Fin 7) : x v = x 1 + oblX0 x v • (x 0 - x 1) + oblX6 x v • (x 6 - x 1) +
    oblX2 x v • (x 2 - x 1) := by
  conv_lhs => rw [T.rep v]
  abel

/-- The oblique coordinates in the frame `x 1; x 2, x 6, x 0`. -/
theorem rep260 (v : Fin 7) : x v = x 1 + oblX2 x v • (x 2 - x 1) + oblX6 x v • (x 6 - x 1) +
    oblX0 x v • (x 0 - x 1) := by
  conv_lhs => rw [T.rep v]
  abel

theorem det062 : vol3 (x 0 - x 1) (x 6 - x 1) (x 2 - x 1) ≠ 0 := by
  have e : vol3 (x 0 - x 1) (x 6 - x 1) (x 2 - x 1) = -det24 x := by
    simp only [det24, vol3]; ring
  rw [e, neg_ne_zero]; exact T.det_ne

theorem det260 : vol3 (x 2 - x 1) (x 6 - x 1) (x 0 - x 1) ≠ 0 := by
  have e : vol3 (x 2 - x 1) (x 6 - x 1) (x 0 - x 1) = det24 x := by
    simp only [det24, vol3]; ring
  rw [e]; exact T.det_ne

end Type24

/-! ### Theorem 15.4: the window triangle -/

theorem fin7_cases (i : Fin 7) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by
  fin_cases i <;> simp

/-- The window at the axis vertex `6` (`a = 0`, `b = 2`). -/
theorem isRupert_type24_window6 {x : Fin 7 → ℝ³} (T : Type24 x)
    (h : omega4 x * omega3 x < 1 ∨ omega4 x ≤ 0 ∨ omega3 x ≤ 0) :
    IsRupert (univ.image x) := by
  have gen : ∀ v : Fin 7, v ≠ 0 → v ≠ 1 → v ≠ 2 → v ≠ 6 → ∃ A B C : ℝ,
      x v = x 1 + A • (x 0 - x 1) + B • (x 2 - x 1) + C • (x 6 - x 1) ∧ 0 < A ∧ 0 < B ∧
        0 < C ∧ B + C - omega3 x * A ≤ 1 ∧ A + C - omega4 x * B ≤ 1 ∧
        A + B - omega5 x * C ≤ 1 := by
    intro v h0 h1 h2 h6
    exact ⟨_, _, _, T.rep v, T.X0_pos (by simp [h1, h2, h6]), T.X2_pos (by simp [h0, h1, h6]),
      T.X6_pos (by simp [h0, h1, h2]), T.le236 v, T.le046 v, T.le025 v⟩
  refine isRupert_window_frame (univ.image x) (x 1) (x 0) (x 2) (x 6) (Type24.mem 0) (Type24.mem 2)
    (Type24.mem 6) T.det_ne (wab := omega5 x) h ?_
  intro v hv h0 h2 h6
  obtain ⟨i, -, rfl⟩ := mem_image.mp hv
  rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl h0
  · exact Or.inl rfl
  · exact absurd rfl h2
  · exact Or.inr (gen 3 (by decide) (by decide) (by decide) (by decide))
  · exact Or.inr (gen 4 (by decide) (by decide) (by decide) (by decide))
  · exact Or.inr (gen 5 (by decide) (by decide) (by decide) (by decide))
  · exact absurd rfl h6

/-- The window at the axis vertex `2` (`a = 0`, `b = 6`). -/
theorem isRupert_type24_window2 {x : Fin 7 → ℝ³} (T : Type24 x)
    (h : omega5 x * omega3 x < 1 ∨ omega5 x ≤ 0 ∨ omega3 x ≤ 0) :
    IsRupert (univ.image x) := by
  have gen : ∀ v : Fin 7, v ≠ 0 → v ≠ 1 → v ≠ 2 → v ≠ 6 → ∃ A B C : ℝ,
      x v = x 1 + A • (x 0 - x 1) + B • (x 6 - x 1) + C • (x 2 - x 1) ∧ 0 < A ∧ 0 < B ∧
        0 < C ∧ B + C - omega3 x * A ≤ 1 ∧ A + C - omega5 x * B ≤ 1 ∧
        A + B - omega4 x * C ≤ 1 := by
    intro v h0 h1 h2 h6
    exact ⟨_, _, _, T.rep062 v, T.X0_pos (by simp [h1, h2, h6]),
      T.X6_pos (by simp [h0, h1, h2]), T.X2_pos (by simp [h0, h1, h6]),
      by linarith [T.le236 v], T.le025 v, T.le046 v⟩
  refine isRupert_window_frame (univ.image x) (x 1) (x 0) (x 6) (x 2) (Type24.mem 0) (Type24.mem 6)
    (Type24.mem 2) T.det062 (wab := omega4 x) h ?_
  intro v hv h0 h6 h2
  obtain ⟨i, -, rfl⟩ := mem_image.mp hv
  rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl h0
  · exact Or.inl rfl
  · exact absurd rfl h2
  · exact Or.inr (gen 3 (by decide) (by decide) (by decide) (by decide))
  · exact Or.inr (gen 4 (by decide) (by decide) (by decide) (by decide))
  · exact Or.inr (gen 5 (by decide) (by decide) (by decide) (by decide))
  · exact absurd rfl h6

/-- The window at the axis vertex `0` (`a = 2`, `b = 6`). -/
theorem isRupert_type24_window0 {x : Fin 7 → ℝ³} (T : Type24 x)
    (h : omega5 x * omega4 x < 1 ∨ omega5 x ≤ 0 ∨ omega4 x ≤ 0) :
    IsRupert (univ.image x) := by
  have gen : ∀ v : Fin 7, v ≠ 0 → v ≠ 1 → v ≠ 2 → v ≠ 6 → ∃ A B C : ℝ,
      x v = x 1 + A • (x 2 - x 1) + B • (x 6 - x 1) + C • (x 0 - x 1) ∧ 0 < A ∧ 0 < B ∧
        0 < C ∧ B + C - omega4 x * A ≤ 1 ∧ A + C - omega5 x * B ≤ 1 ∧
        A + B - omega3 x * C ≤ 1 := by
    intro v h0 h1 h2 h6
    exact ⟨_, _, _, T.rep260 v, T.X2_pos (by simp [h0, h1, h6]),
      T.X6_pos (by simp [h0, h1, h2]), T.X0_pos (by simp [h1, h2, h6]),
      by linarith [T.le046 v], by linarith [T.le025 v], T.le236 v⟩
  refine isRupert_window_frame (univ.image x) (x 1) (x 2) (x 6) (x 0) (Type24.mem 2) (Type24.mem 6)
    (Type24.mem 0) T.det260 (wab := omega3 x) h ?_
  intro v hv h2 h6 h0
  obtain ⟨i, -, rfl⟩ := mem_image.mp hv
  rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl h0
  · exact Or.inl rfl
  · exact absurd rfl h2
  · exact Or.inr (gen 3 (by decide) (by decide) (by decide) (by decide))
  · exact Or.inr (gen 4 (by decide) (by decide) (by decide) (by decide))
  · exact Or.inr (gen 5 (by decide) (by decide) (by decide) (by decide))
  · exact absurd rfl h6

/-- **Theorem 15.4 (the window triangle).**  A type-24 point set in region W (some
`ω ≤ 0`, or some product `ω_g ω_h < 1`) is Rupert, with no exclusion: at a view in the open
tangent cone at `1`, the silhouette is the triangle of the axis vertices `0, 2, 6` and
`1, 3, 4, 5` project strictly inside it (Theorem 5). -/
theorem isRupert_type24_window {x : Fin 7 → ℝ³} (T : Type24 x)
    (hW : omega3 x ≤ 0 ∨ omega4 x ≤ 0 ∨ omega5 x ≤ 0 ∨ omega3 x * omega4 x < 1 ∨
      omega3 x * omega5 x < 1 ∨ omega4 x * omega5 x < 1) :
    IsRupert (univ.image x) := by
  rcases hW with h | h | h | h | h | h
  · exact isRupert_type24_window6 T (Or.inr (Or.inr h))
  · exact isRupert_type24_window6 T (Or.inr (Or.inl h))
  · exact isRupert_type24_window2 T (Or.inr (Or.inl h))
  · exact isRupert_type24_window6 T (Or.inl (by linarith [mul_comm (omega3 x) (omega4 x)]))
  · exact isRupert_type24_window2 T (Or.inl (by linarith [mul_comm (omega3 x) (omega5 x)]))
  · exact isRupert_type24_window0 T (Or.inl (by linarith [mul_comm (omega4 x) (omega5 x)]))

/-! ### Theorem 15.7, case B: the three side crossings -/

/-- The view of `S_6 = 046/236`: oblique `(1 + ω4, 1 + ω3, ω3 ω4 − 1)`. -/
noncomputable def view6 (x : Fin 7 → ℝ³) : ℝ³ :=
  sideView (x 1) (x 0) (x 2) (x 6) (omega4 x) (omega3 x)

/-- The view of `S_2 = 025/236`: oblique `(1 + ω5, ω3 ω5 − 1, 1 + ω3)`. -/
noncomputable def view2 (x : Fin 7 → ℝ³) : ℝ³ :=
  sideView (x 1) (x 0) (x 6) (x 2) (omega5 x) (omega3 x)

/-- The view of `S_0 = 025/046`: oblique `(ω4 ω5 − 1, 1 + ω5, 1 + ω4)`. -/
noncomputable def view0 (x : Fin 7 → ℝ³) : ℝ³ :=
  sideView (x 1) (x 2) (x 6) (x 0) (omega5 x) (omega4 x)

/-- `S_6` is available and free: `ω3 ω4 > 1`, the axis vertices `0, 2, 6` at distinct depths
along `view6`, and no horizontal double normal of their triangle there. -/
def S6Free (x : Fin 7 → ℝ³) : Prop :=
  1 < omega3 x * omega4 x ∧ [⟪x 0, view6 x⟫, ⟪x 2, view6 x⟫, ⟪x 6, view6 x⟫].Nodup ∧
    NoHDNAt {x 0, x 2, x 6} (view6 x)

/-- `S_2` is available and free (`ω3 ω5 > 1`). -/
def S2Free (x : Fin 7 → ℝ³) : Prop :=
  1 < omega3 x * omega5 x ∧ [⟪x 0, view2 x⟫, ⟪x 2, view2 x⟫, ⟪x 6, view2 x⟫].Nodup ∧
    NoHDNAt {x 0, x 2, x 6} (view2 x)

/-- `S_0` is available and free (`ω4 ω5 > 1`). -/
def S0Free (x : Fin 7 → ℝ³) : Prop :=
  1 < omega4 x * omega5 x ∧ [⟪x 0, view0 x⟫, ⟪x 2, view0 x⟫, ⟪x 6, view0 x⟫].Nodup ∧
    NoHDNAt {x 0, x 2, x 6} (view0 x)

/-- Region B: all `ω > 0`, all products `≥ 1`, `Δ < 0`. -/
def RegionB24 (x : Fin 7 → ℝ³) : Prop :=
  0 < omega3 x ∧ 0 < omega4 x ∧ 0 < omega5 x ∧ 1 ≤ omega3 x * omega4 x ∧
    1 ≤ omega3 x * omega5 x ∧ 1 ≤ omega4 x * omega5 x ∧ Delta24 x < 0

theorem univ_image_cases (x : Fin 7 → ℝ³) {o pa pb pc ga gb gc : ℝ³}
    (h : ∀ i : Fin 7, x i = o ∨ x i = pa ∨ x i = pb ∨ x i = pc ∨ x i = ga ∨ x i = gb ∨
      x i = gc) :
    ∀ y ∈ univ.image x, y = o ∨ y = pa ∨ y = pb ∨ y = pc ∨ y = ga ∨ y = gb ∨ y = gc := by
  intro y hy
  obtain ⟨i, -, rfl⟩ := mem_image.mp hy
  exact h i

/-- **Lemma 15.5 for `S_6` (with Theorem 15.7).**  If all `ω > 0`, `Δ < 0` and `S_6` is
free, a type-24 point set is Rupert. -/
theorem isRupert_type24_S6 {x : Fin 7 → ℝ³} (T : Type24 x) (h3 : 0 < omega3 x)
    (h4 : 0 < omega4 x) (h5 : 0 < omega5 x) (hΔ : Delta24 x < 0) (hf : S6Free x) :
    IsRupert (univ.image x) := by
  obtain ⟨hp, hz, hnd⟩ := hf
  have ne : ∀ i j : Fin 7, i ≠ j → x i ≠ x j := fun i j h e => h (T.inj e)
  refine isRupert_sideCrossing_frame (univ.image x) (o := x 1) (pa := x 0) (pb := x 2)
    (pc := x 6) (ga := x 4) (gb := x 3) (gc := x 5) ?_ (Type24.mem 0) (Type24.mem 2) (Type24.mem 6)
    ⟨ne 4 0 (by decide), ne 4 2 (by decide), ne 4 6 (by decide)⟩
    ⟨ne 3 0 (by decide), ne 3 2 (by decide), ne 3 6 (by decide)⟩ T.det_ne h4 h3 h5
    (by linarith [mul_comm (omega3 x) (omega4 x)])
    (by have : omega4 x * omega3 x * omega5 x - omega4 x - omega3 x - omega5 x - 2 =
          Delta24 x := by unfold Delta24; ring
        linarith)
    (T.rep 4) (T.X2_pos (by decide)) T.eq4 (T.lt236 (by decide)) (T.lt025 (by decide))
    (T.rep 3) (T.X0_pos (by decide)) T.eq3 (T.lt046 (by decide)) (T.lt025 (by decide))
    (T.rep 5) (T.X6_pos (by decide)) T.eq5 (T.lt236 (by decide)) (T.lt046 (by decide))
    hz hnd
  refine univ_image_cases x fun i => ?_
  rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- **Lemma 15.5 for `S_2` (with Theorem 15.7).** -/
theorem isRupert_type24_S2 {x : Fin 7 → ℝ³} (T : Type24 x) (h3 : 0 < omega3 x)
    (h4 : 0 < omega4 x) (h5 : 0 < omega5 x) (hΔ : Delta24 x < 0) (hf : S2Free x) :
    IsRupert (univ.image x) := by
  obtain ⟨hp, hz, hnd⟩ := hf
  have ne : ∀ i j : Fin 7, i ≠ j → x i ≠ x j := fun i j h e => h (T.inj e)
  have hW : ({x 0, x 6, x 2} : Finset ℝ³) = {x 0, x 2, x 6} := by
    ext y; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  refine isRupert_sideCrossing_frame (univ.image x) (o := x 1) (pa := x 0) (pb := x 6)
    (pc := x 2) (ga := x 5) (gb := x 3) (gc := x 4) ?_ (Type24.mem 0) (Type24.mem 6) (Type24.mem 2)
    ⟨ne 5 0 (by decide), ne 5 6 (by decide), ne 5 2 (by decide)⟩
    ⟨ne 3 0 (by decide), ne 3 6 (by decide), ne 3 2 (by decide)⟩ T.det062 h5 h3 h4
    (by linarith [mul_comm (omega3 x) (omega5 x)])
    (by have : omega5 x * omega3 x * omega4 x - omega5 x - omega3 x - omega4 x - 2 =
          Delta24 x := by unfold Delta24; ring
        linarith)
    (T.rep062 5) (T.X6_pos (by decide)) (by linarith [T.eq5])
      (by linarith [T.lt236 (v := 5) (by decide)]) (T.lt046 (by decide))
    (T.rep062 3) (T.X0_pos (by decide)) (by linarith [T.eq3]) (T.lt025 (by decide))
      (T.lt046 (by decide))
    (T.rep062 4) (T.X2_pos (by decide)) T.eq4 (by linarith [T.lt236 (v := 4) (by decide)])
      (T.lt025 (by decide))
    ?_ (by rw [hW]; exact hnd)
  · refine univ_image_cases x fun i => ?_
    rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · rw [nodup3] at hz ⊢
    exact ⟨hz.2.1, hz.1, fun h => hz.2.2 h.symm⟩

/-- **Lemma 15.5 for `S_0` (with Theorem 15.7).** -/
theorem isRupert_type24_S0 {x : Fin 7 → ℝ³} (T : Type24 x) (h3 : 0 < omega3 x)
    (h4 : 0 < omega4 x) (h5 : 0 < omega5 x) (hΔ : Delta24 x < 0) (hf : S0Free x) :
    IsRupert (univ.image x) := by
  obtain ⟨hp, hz, hnd⟩ := hf
  have ne : ∀ i j : Fin 7, i ≠ j → x i ≠ x j := fun i j h e => h (T.inj e)
  have hW : ({x 2, x 6, x 0} : Finset ℝ³) = {x 0, x 2, x 6} := by
    ext y; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  refine isRupert_sideCrossing_frame (univ.image x) (o := x 1) (pa := x 2) (pb := x 6)
    (pc := x 0) (ga := x 5) (gb := x 4) (gc := x 3) ?_ (Type24.mem 2) (Type24.mem 6) (Type24.mem 0)
    ⟨ne 5 2 (by decide), ne 5 6 (by decide), ne 5 0 (by decide)⟩
    ⟨ne 4 2 (by decide), ne 4 6 (by decide), ne 4 0 (by decide)⟩ T.det260 h5 h4 h3
    (by linarith [mul_comm (omega4 x) (omega5 x)])
    (by have : omega5 x * omega4 x * omega3 x - omega5 x - omega4 x - omega3 x - 2 =
          Delta24 x := by unfold Delta24; ring
        linarith)
    (T.rep260 5) (T.X6_pos (by decide)) (by linarith [T.eq5])
      (by linarith [T.lt046 (v := 5) (by decide)]) (T.lt236 (by decide))
    (T.rep260 4) (T.X2_pos (by decide)) (by linarith [T.eq4])
      (by linarith [T.lt025 (v := 4) (by decide)]) (T.lt236 (by decide))
    (T.rep260 3) (T.X0_pos (by decide)) T.eq3 (by linarith [T.lt046 (v := 3) (by decide)])
      (by linarith [T.lt025 (v := 3) (by decide)])
    ?_ (by rw [hW]; exact hnd)
  · refine univ_image_cases x fun i => ?_
    rcases fin7_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · rw [nodup3] at hz ⊢
    exact ⟨hz.2.2, fun h => hz.1 h.symm, fun h => hz.2.1 h.symm⟩

/-- **Theorem 15.7 (region B).**  In region B, a type-24 point set is Rupert as soon as one
side crossing whose product exceeds 1 is free (distinct depths of `0, 2, 6`, no horizontal
double normal of their triangle at its view). -/
theorem isRupert_type24_B {x : Fin 7 → ℝ³} (T : Type24 x) (hB : RegionB24 x)
    (hf : S6Free x ∨ S2Free x ∨ S0Free x) : IsRupert (univ.image x) := by
  obtain ⟨h3, h4, h5, -, -, -, hΔ⟩ := hB
  rcases hf with hf | hf | hf
  · exact isRupert_type24_S6 T h3 h4 h5 hΔ hf
  · exact isRupert_type24_S2 T h3 h4 h5 hΔ hf
  · exact isRupert_type24_S0 T h3 h4 h5 hΔ hf

/-- **Corollary 15.8.**  A type-24 point set outside `C̄ = {ω3, ω4, ω5 > 0, Δ ≥ 0}` is
Rupert, unless it lies in `Σ_B`: region B with no free side crossing (the hypothesis `hB`
is "not in `Σ_B`").  Region W needs no exclusion (Theorem 15.4). -/
theorem isRupert_type24_outside_Cbar {x : Fin 7 → ℝ³} (T : Type24 x)
    (hC : ¬ (0 < omega3 x ∧ 0 < omega4 x ∧ 0 < omega5 x ∧ 0 ≤ Delta24 x))
    (hB : RegionB24 x → S6Free x ∨ S2Free x ∨ S0Free x) : IsRupert (univ.image x) := by
  by_cases hW : omega3 x ≤ 0 ∨ omega4 x ≤ 0 ∨ omega5 x ≤ 0 ∨ omega3 x * omega4 x < 1 ∨
      omega3 x * omega5 x < 1 ∨ omega4 x * omega5 x < 1
  · exact isRupert_type24_window T hW
  · push Not at hW
    obtain ⟨h3, h4, h5, p34, p35, p45⟩ := hW
    have hΔ : Delta24 x < 0 := by
      by_contra h; push Not at h; exact hC ⟨h3, h4, h5, h⟩
    have hR : RegionB24 x := ⟨h3, h4, h5, p34, p35, p45, hΔ⟩
    exact isRupert_type24_B T hR (hB hR)

end Minimality

end
