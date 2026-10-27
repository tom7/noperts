module

public import Minimality.RobustEdge

@[expose] public section

/-!
# Edge crossings with doubles over the rim corners (Lemma 16.27′ at an edge view)

`isRupert_edgePair_robust` (`RobustEdge.lean`) allows besides the rim only points hidden inside
it and middles over its sides.  Lemma 16.27′ (`isRupert_of_uniform_doubles`, `UniformTilt.lean`)
says that any finite set `D` of *doubles* `y = x i − h u₀` over corners `x i` of the shadow costs
nothing at the uniform tilt (the axle `w` is one of them).  So a point of `V` lying exactly over a
rim corner `a`, `b` or `c` at the view `u = w − v` (a vertical far edge: a face edge parallel to
`u`) can be allowed in `hV`, with no change of the rim, of the depth conditions or of
`NoHDNAt (V.erase w) u` (the corners of the rim lie in `V.erase w`; polygons in the
definition of `NoHDNAt` are strictly convex, so they never contain a point and its double).

* `isRupert_of_edgeView_robustD`: the determinant-test form of Theorem 8.9/18.1 with doubles;
* `isRupert_quad_rim_int_robustD`, `isRupert_edgePair_closing_nwsD`: the chain below;
* `isRupert_edgePair_robustD`: Corollary 14.1 with ties and doubles over `a`, `b`, `c`.

Middles are taken as chords from the corner of the closing (`EdgeMid.chord_v`, `chord_w`): in
the uniform tilt a middle chord from the axle is not available, but every `EdgeMid` is also a
chord from the corner, with another offset.
-/

namespace Minimality

open scoped RealInnerProductSpace
open Finset

/-- **Theorem 8.9 with ties and doubles, at an edge view given by determinant tests**
(`isRupert_of_edgeView_robust` with `isRupert_of_uniform_doubles_robustUnimodal`): besides the
middles `M`, any finite set `D` of doubles `y = x i − h u₀` over corners may lie in `V`.  The
middles are chords from the corner `x i₀`. -/
theorem isRupert_of_edgeView_robustD (V M D : Finset ℝ³) (u₀ : ℝ³) (hu₀ : u₀ ≠ 0) {k : ℕ}
    [NeZero k] (hk : 3 ≤ k) (x : ZMod k → ℝ³) (i₀ : ZMod k) (w : ℝ³) (h : ℝ) (hwV : w ∈ V)
    (hw : w = x i₀ - h • u₀) (hh : h ≠ 0) (hxV : ∀ i, x i ∈ V) (hxM : ∀ i, x i ∉ M)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (x (i + 1) - x i) (x j - x i) u₀)
    (hrest : ∀ y ∈ V, y ∉ M → y ∉ D → y ≠ w → (∀ j, y ≠ x j) → ∀ i,
      0 < det3 (x (i + 1) - x i) (y - x i) u₀)
    (hz : IsRobustUnimodal (fun i => ⟪x i, u₀⟫)) (hnd : NoHDNAt (V.erase w) u₀)
    (hM : ∀ m ∈ M, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      (m = x i₀ + s • (x (i₀ + 1) - x i₀) + δ • u₀ ∨
        m = x (i₀ - 1) + s • (x i₀ - x (i₀ - 1)) + δ • u₀))
    (hD : ∀ y ∈ D, ∃ i : ZMod k, ∃ h : ℝ, h ≠ 0 ∧ y = x i - h • u₀) : IsRupert V := by
  classical
  obtain ⟨R, hR, r, hr, hRu⟩ := exists_rotation_to_ez_pos u₀ hu₀
  have hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))) := by
    refine ⟨hk, fun i j hi hj => ?_⟩
    simp only [proj_rot_sub]
    exact cross2_proj_rot_pos hR hr hRu (hcyc i j hi hj)
  have hdepth : ∀ y, (R.toEuclideanLin y) 2 = r⁻¹ * ⟪y, u₀⟫ := by
    intro y
    have : r * (R.toEuclideanLin y) 2 = ⟪y, u₀⟫ := by
      rw [← inner_ez, ← real_inner_smul_right, ← hRu, inner_toEuclideanLin_SO3 hR]
    rw [← this]; field_simp
  refine isRupert_of_uniform_doubles_robustUnimodal V M (insert w D) R hR hr hRu x hxV hxM hp
    ?_ ?_ ?_ ?_ ?_
  · intro y hy hyM hyD hyx
    rw [mem_insert, not_or] at hyD
    refine hp.mem_interior_of_left fun i => ?_
    simp only [proj_rot_sub]
    exact cross2_proj_rot_pos hR hr hRu (hrest y hy hyM hyD.2 hyD.1 hyx i)
  · simp only [hdepth]; exact hz.smul (inv_pos.mpr hr)
  · exact hnd R hR r hr.ne' hRu k x
      (fun i => mem_erase.mpr ⟨corner_ne_axle hr hRu hp hw hh i, hxV i⟩) hp
  · intro m hm
    obtain ⟨s, δ, hs0, hs1, hδ, hmm | hmm⟩ := hM m hm
    · exact ⟨i₀, s, δ, hs0, hs1, hδ, hmm⟩
    · exact ⟨i₀ - 1, s, δ, hs0, hs1, hδ, by rwa [sub_add_cancel]⟩
  · intro y hy
    rcases mem_insert.mp hy with rfl | hyD
    · exact ⟨i₀, h, hh, hw⟩
    · exact hD y hyD

/-- A middle of the edge crossing is a chord from `v`, with another offset. -/
theorem EdgeMid.chord_v {v w a b m : ℝ³} (h : EdgeMid v w a b m) :
    ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      (m = v + s • (a - v) + δ • (w - v) ∨ m = b + s • (v - b) + δ • (w - v)) := by
  obtain ⟨s, δ, hs0, hs1, hδ, h | h | h | h⟩ := h
  · exact ⟨s, -δ, hs0, hs1, neg_ne_zero.mpr hδ.ne', Or.inl (by rw [h]; module)⟩
  · exact ⟨s, -δ, hs0, hs1, neg_ne_zero.mpr hδ.ne', Or.inr (by rw [h]; module)⟩
  · exact ⟨s, 1 - s + δ, hs0, hs1, by linarith, Or.inl (by rw [h]; module)⟩
  · exact ⟨s, s + δ, hs0, hs1, by linarith, Or.inr (by rw [h]; module)⟩

/-- A middle of the edge crossing is a chord from `w`, with another offset. -/
theorem EdgeMid.chord_w {v w a b m : ℝ³} (h : EdgeMid v w a b m) :
    ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      (m = w + s • (a - w) + δ • (w - v) ∨ m = b + s • (w - b) + δ • (w - v)) := by
  obtain ⟨s, δ, hs0, hs1, hδ, h | h | h | h⟩ := h
  · exact ⟨s, -δ - (1 - s), hs0, hs1, by linarith, Or.inl (by rw [h]; module)⟩
  · exact ⟨s, -δ - s, hs0, hs1, by linarith, Or.inr (by rw [h]; module)⟩
  · exact ⟨s, δ, hs0, hs1, hδ.ne', Or.inl h⟩
  · exact ⟨s, δ, hs0, hs1, hδ.ne', Or.inr h⟩

/-- **A 4-corner edge-view rim with ties and doubles** (`isRupert_quad_rim_int_robust` with
doubles `D` over the rim corners). -/
theorem isRupert_quad_rim_int_robustD (V M D : Finset ℝ³) (u : ℝ³) (hu : u ≠ 0)
    {w y y' A B : ℝ³}
    (h : ℝ) (hh : h ≠ 0) (hw : w = y - h • u) (hwV : w ∈ V) (hyV : y ∈ V) (hy'V : y' ∈ V)
    (hAV : A ∈ V) (hBV : B ∈ V) (hyM : y ∉ M) (hAM : A ∉ M) (hy'M : y' ∉ M) (hBM : B ∉ M)
    (t1 : 0 < det3 (A - y) (y' - y) u) (t2 : 0 < det3 (A - y) (B - y) u)
    (t3 : 0 < det3 (y' - A) (B - A) u) (t4 : 0 < det3 (y' - A) (y - A) u)
    (t5 : 0 < det3 (B - y') (y - y') u) (t6 : 0 < det3 (B - y') (A - y') u)
    (t7 : 0 < det3 (y - B) (A - B) u) (t8 : 0 < det3 (y - B) (y' - B) u)
    (hrest : ∀ z ∈ V, z ∉ M → z ∉ D → z ≠ w → z ≠ y → z ≠ A → z ≠ y' → z ≠ B →
      0 < det3 (A - y) (z - y) u ∧ 0 < det3 (y' - A) (z - A) u ∧
      0 < det3 (B - y') (z - y') u ∧ 0 < det3 (y - B) (z - B) u)
    (hz : IsRobustUnimodal (quad ⟪y, u⟫ ⟪A, u⟫ ⟪y', u⟫ ⟪B, u⟫))
    (hM : ∀ m ∈ M, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      (m = y + s • (A - y) + δ • u ∨ m = B + s • (y - B) + δ • u))
    (hD : ∀ z ∈ D, ∃ p, (p = y ∨ p = A ∨ p = y' ∨ p = B) ∧ ∃ k : ℝ, k ≠ 0 ∧ z = p - k • u)
    (hnd : NoHDNAt (V.erase w) u) : IsRupert V := by
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  refine isRupert_of_edgeView_robustD V M D u hu (k := 4) (by norm_num) (quad y A y' B) 0 w h hwV
    (by simp only [quad_0]; exact hw) hh ?_ ?_ ?_ ?_ ?_ hnd ?_ ?_
  · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
    exacts [hyV, hAV, hy'V, hBV]
  · intro i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
    exacts [hyM, hAM, hy'M, hBM]
  · intro i j hi hj
    rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
    exacts [t1, t2, t3, t4, t5, t6, t7, t8]
  · intro z hz hzM hzD hzw hzx i
    obtain ⟨r1, r2, r3, r4⟩ := hrest z hz hzM hzD hzw (hzx 0) (hzx 1) (hzx 2) (hzx 3)
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3]
    exacts [r1, r2, r3, r4]
  · rw [quad_inner]; exact hz
  · rw [zmod4_zero_add_one, zmod4_zero_sub_one]
    simpa only [quad_0, quad_1, quad_3] using hM
  · intro z hzD
    obtain ⟨p, hp, k, hk, rfl⟩ := hD z hzD
    rcases hp with rfl | rfl | rfl | rfl
    exacts [⟨0, k, hk, by simp only [quad_0]⟩, ⟨1, k, hk, by simp only [quad_1]⟩,
      ⟨2, k, hk, by simp only [quad_2]⟩, ⟨3, k, hk, by simp only [quad_3]⟩]

/-- **One closing with ties and doubles** (`isRupert_edgePair_closing_nws` with doubles `D`
over `a`, `c`, `b`). -/
theorem isRupert_edgePair_closing_nwsD (V M D : Finset ℝ³) {u y o a b c : ℝ³} {h : ℝ}
    (hh : h ≠ 0) (ho : o = y - h • u) (hu : u ≠ 0) (hoV : o ∈ V) (hyV : y ∈ V) (haV : a ∈ V)
    (hbV : b ∈ V) (hcV : c ∈ V) (hyM : y ∉ M) (haM : a ∉ M) (hbM : b ∉ M) (hcM : c ∉ M)
    (q₁ : 0 < det3 (a - y) (c - y) u) (q₂ : 0 < det3 (c - a) (b - a) u)
    (q₃ : 0 < det3 (b - c) (y - c) u) (q₄ : 0 < det3 (y - b) (a - b) u)
    (hrest : ∀ z ∈ V, z ∉ M → z ∉ D → z ≠ o → z ≠ y → z ≠ a → z ≠ c → z ≠ b →
      EdgeHidden u y a c b z)
    (hN : NWS4 (quad ⟪y, u⟫ ⟪a, u⟫ ⟪c, u⟫ ⟪b, u⟫))
    (hM : ∀ m ∈ M, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      (m = y + s • (a - y) + δ • u ∨ m = b + s • (y - b) + δ • u))
    (hD : ∀ z ∈ D, ∃ k : ℝ, k ≠ 0 ∧ (z = a - k • u ∨ z = c - k • u ∨ z = b - k • u))
    (hnd : NoHDNAt (V.erase o) u) : IsRupert V := by
  have i2 : det3 (a - y) (b - y) u = det3 (y - b) (a - b) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i4 : det3 (c - a) (y - a) u = det3 (a - y) (c - y) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i6 : det3 (b - c) (a - c) u = det3 (c - a) (b - a) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have i8 : det3 (y - b) (c - b) u = det3 (b - c) (y - c) u := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  refine isRupert_quad_rim_int_robustD V M D u hu h hh ho hoV hyV hcV haV hbV hyM haM hcM hbM q₁
    (by rw [i2]; exact q₄) q₂ (by rw [i4]; exact q₁) q₃ (by rw [i6]; exact q₂) q₄
    (by rw [i8]; exact q₃) hrest hN.isRobustUnimodal hM ?_ hnd
  intro z hz
  obtain ⟨k, hk, hz | hz | hz⟩ := hD z hz
  exacts [⟨a, by tauto, k, hk, hz⟩, ⟨c, by tauto, k, hk, hz⟩, ⟨b, by tauto, k, hk, hz⟩]

/-- A point lying exactly over one of the rim corners `a`, `b`, `c` of the shadow at the view
`u` (a double, in the sense of Lemma 16.27′): `z = p + k u` with `k ≠ 0`. -/
def EdgeDoubleOver (u a b c z : ℝ³) : Prop :=
  ∃ k : ℝ, k ≠ 0 ∧ (z = a + k • u ∨ z = b + k • u ∨ z = c + k • u)

/-- **Corollary 14.1 with ties and doubles** (`isRupert_edgePair_robust` with Lemma 16.27′):
as there, with `hV` also allowing points over the rim corners `a`, `b`, `c` at the view
`w − v` (for instance an edge of a face parallel to the edge `v w`, with `a` and the other end
of the edge in the same position in the shadow). -/
theorem isRupert_edgePair_robustD {v w a b c : ℝ³} (V : Finset ℝ³)
    (hvV : v ∈ V) (hwV : w ∈ V) (haV : a ∈ V) (hbV : b ∈ V) (hcV : c ∈ V)
    (q₁ : 0 < det3 (a - v) (c - v) (w - v)) (q₂ : 0 < det3 (c - a) (b - a) (w - v))
    (q₃ : 0 < det3 (b - c) (v - c) (w - v)) (q₄ : 0 < det3 (v - b) (a - b) (w - v))
    (hE : det3 (b - a) (c - a) (v - a) * det3 (b - a) (c - a) (w - a) ≤ 0)
    (h3 : ¬ (⟪a, w - v⟫ = ⟪c, w - v⟫ ∧ ⟪c, w - v⟫ = ⟪b, w - v⟫))
    (hV : ∀ z ∈ V, z = v ∨ z = w ∨ z = a ∨ z = b ∨ z = c ∨ EdgeMid v w a b z ∨
      EdgeHidden (w - v) v a c b z ∨ EdgeDoubleOver (w - v) a b c z)
    (hnd₁ : NoHDNAt (V.erase w) (w - v)) (hnd₂ : NoHDNAt (V.erase v) (w - v)) :
    IsRupert V := by
  classical
  set M := V.filter (fun z => EdgeMid v w a b z ∧ z ≠ v ∧ z ≠ w ∧ z ≠ a ∧ z ≠ b ∧ z ≠ c)
    with hM
  set D := V.filter (fun z => EdgeDoubleOver (w - v) a b c z ∧ z ≠ v ∧ z ≠ w ∧ z ≠ a ∧ z ≠ b ∧
    z ≠ c) with hDdef
  have hu : w - v ≠ 0 := by
    intro h0; rw [h0] at q₁; simp only [det3, inner_zero_right, lt_irrefl] at q₁
  have nM : ∀ z, z = v ∨ z = w ∨ z = a ∨ z = b ∨ z = c → z ∉ M := by
    intro z hz hzM
    obtain ⟨-, -, h1, h2, h3, h4, h5⟩ := mem_filter.mp hzM
    rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp_all
  have rest : ∀ z ∈ V, z ∉ M → z ∉ D → z ≠ v → z ≠ w → z ≠ a → z ≠ c → z ≠ b →
      EdgeHidden (w - v) v a c b z := by
    intro z hz hzM hzD h1 h2 h3 h4 h5
    rcases hV z hz with e | e | e | e | e | hmid | hid | hdb
    · exact absurd e h1
    · exact absurd e h2
    · exact absurd e h3
    · exact absurd e h5
    · exact absurd e h4
    · exact absurd (mem_filter.mpr ⟨hz, hmid, h1, h2, h3, h5, h4⟩) hzM
    · exact hid
    · exact absurd (mem_filter.mpr ⟨hz, hdb, h1, h2, h3, h5, h4⟩) hzD
  have hDw : ∀ z ∈ D, ∃ k : ℝ, k ≠ 0 ∧ (z = a - k • (w - v) ∨ z = c - k • (w - v) ∨
      z = b - k • (w - v)) := by
    intro z hz
    obtain ⟨k, hk, e | e | e⟩ := (mem_filter.mp hz).2.1
    exacts [⟨-k, neg_ne_zero.mpr hk, Or.inl (by rw [e]; module)⟩,
      ⟨-k, neg_ne_zero.mpr hk, Or.inr (Or.inr (by rw [e]; module))⟩,
      ⟨-k, neg_ne_zero.mpr hk, Or.inr (Or.inl (by rw [e]; module))⟩]
  rcases edgePair_nws q₁ q₂ q₃ q₄ hE h3 with hN | hN
  · -- `K_v`
    refine isRupert_edgePair_closing_nwsD V M D (y := v) (o := w) (h := -1) (by norm_num)
      (by rw [neg_one_smul, sub_neg_eq_add]; abel) hu hwV hvV haV hbV hcV (nM v (by tauto))
      (nM a (by tauto)) (nM b (by tauto)) (nM c (by tauto)) q₁ q₂ q₃ q₄ ?_ hN ?_ hDw hnd₁
    · intro z hz hzM hzD h1 h2 h3 h4 h5
      exact rest z hz hzM hzD h2 h1 h3 h4 h5
    · intro m hm
      exact (mem_filter.mp hm).2.1.chord_v
  · -- `K_w`
    refine isRupert_edgePair_closing_nwsD V M D (y := w) (o := v) (h := 1) one_ne_zero
      (by rw [one_smul]; abel) hu hvV hwV haV hbV hcV (nM w (by tauto)) (nM a (by tauto))
      (nM b (by tauto)) (nM c (by tauto)) (by rw [det3_vw_both]; exact q₁) q₂
      (by rw [det3_vw_right]; exact q₃) (by rw [det3_vw_left]; exact q₄) ?_ hN ?_ hDw hnd₂
    · intro z hz hzM hzD h1 h2 h3 h4 h5
      exact (rest z hz hzM hzD h1 h2 h3 h4 h5).shift
    · intro m hm
      exact (mem_filter.mp hm).2.1.chord_w

end Minimality

end
