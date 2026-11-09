module

public import Minimality.RobustUnimodal
public import Minimality.UniformTilt

@[expose] public section

/-!
# Theorem 18.3 in the certificate forms: rims with ties

Every consumer of Theorem 7.3 in `UnimodalCert.lean`, `UniformTilt.lean`, `Type08Cases.lean` and
`OctAxis.lean` with `IsCyclicUnimodal` (distinct unimodal corner depths) replaced by
`IsRobustUnimodal` (ties allowed: weakly unimodal, no three equal, no level edge inside a run).
The proofs are those of the distinct-depth forms with Theorem 18.3
(`exists_firstOrderInward_of_robustUnimodal`) in place of Theorem 7.3.

* `exists_tiltCert_of_robustUnimodal`: the certificate form;
* `isRupert_of_chords_robustUnimodal`, `isRupert_of_edgeChords_robustUnimodal`: Propositions
  8.8 and 8.9 with ties;
* `isRupert_of_edgeChords_uniform_robustUnimodal` (Lemma 16.27) and
  **`isRupert_of_uniform_doubles_robustUnimodal`** (Theorem 18.1 in its tie form, §18.3:
  "Theorem 18.1 holds with robustly unimodal in place of distinct and unimodal");
* the determinant-test forms `isRupert_of_edgeView_robust`, `isRupert_of_vertexView_robust`,
  `isRupert_of_edgeView_uniform_robust`.

Sources of robust unimodality: `IsCyclicUnimodal.isRobustUnimodal`, `isRobustUnimodal_three`
(triangle rims), `IsCcwPolygon.isRobustUnimodal_affine` (planar rims), and the limit forms
`isRobustUnimodal_of_tendsto`, `isRobustUnimodal_of_tendsto_single_tie`, and the limit lemma
(`LimitCert.lean`).
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

theorem IsRobustUnimodal.smul {k : ℕ} {z : ZMod k → ℝ} (hz : IsRobustUnimodal z) {c : ℝ}
    (hc : 0 < c) : IsRobustUnimodal (fun i => c * z i) where
  noPeaks B a b c' d hab hbc hcd hdk h := hz.noPeaks B a b c' d hab hbc hcd hdk (by
    simp only [mul_lt_mul_iff_right₀ hc] at h; exact h)
  noTriple i j l hij hjl hil e1 e2 := hz.noTriple i j l hij hjl hil
    (mul_left_cancel₀ hc.ne' e1) (mul_left_cancel₀ hc.ne' e2)
  noLevelRun B a b c' d hab hbc hcd hdk e := by
    have := hz.noLevelRun B a b c' d hab hbc hcd hdk (mul_left_cancel₀ hc.ne' e)
    simp only [mul_lt_mul_iff_right₀ hc]; exact this

/-- **Theorem 18.3 at a rotated view.**  The rotated form of
`exists_firstOrderInward_of_robustUnimodal`: the points are given before rotating. -/
theorem exists_firstOrderInward_image_of_robustUnimodal (V : Finset ℝ³)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V)
    (hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))))
    (hin : ∀ v ∈ V, (∀ i, v ≠ x i) → proj_xy (R.toEuclideanLin v) ∈
      interior (convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (x i)))))
    (hz : IsRobustUnimodal (fun i => (R.toEuclideanLin (x i)) 2))
    (hnd : ¬ HasHorizontalDoubleNormal (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2)) :
    ∃ ω τ : ℝ³, FirstOrderInward (V.image R.toEuclideanLin) ω τ := by
  classical
  exact exists_firstOrderInward_of_robustUnimodal (V.image R.toEuclideanLin)
    (fun i => R.toEuclideanLin (x i)) (fun i => mem_image_of_mem _ (hxV i)) hp
    (by
      intro w hw hc
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hw
      exact hin v hv fun i h => hc i (by rw [h]))
    hz hnd

/-- **Theorem 18.3, certificate form.**  At a view `u₀` (`R u₀ = r e_z`,
`r > 0`) where the silhouette of `V` is the strictly convex counterclockwise
polygon `x`, every other point projecting strictly inside, with robustly
unimodal depths and no horizontal double normal, some first-order motion
`(ω, τ)` has a local certificate at every point of `V`, and moves each corner
strictly to the inner side of both of its edges. -/
theorem exists_tiltCert_of_robustUnimodal (V : Finset ℝ³) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : R ∈ SO3) {u₀ : ℝ³} {r : ℝ} (hr : 0 < r) (hRu : R.toEuclideanLin u₀ = r • ez)
    {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V)
    (hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))))
    (hin : ∀ v ∈ V, (∀ i, v ≠ x i) → proj_xy (R.toEuclideanLin v) ∈
      interior (convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (x i)))))
    (hz : IsRobustUnimodal (fun i => (R.toEuclideanLin (x i)) 2))
    (hnd : ¬ HasHorizontalDoubleNormal (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2)) :
    ∃ ω τ : ℝ³, (∀ y ∈ V, TiltCert V u₀ ω τ y) ∧
      ∀ i, 0 < det3 (x (i + 1) - x i) (cross ω (x i) + τ) u₀ ∧
        0 < det3 (x (i + 1) - x i) (cross ω (x (i + 1)) + τ) u₀ :=
  exists_tiltCert_of_firstOrderInward V R hR hr hRu x hxV hp hin
    (exists_firstOrderInward_image_of_robustUnimodal V R x hxV hp hin hz hnd)

/-- **Proposition 8.8 with a robustly unimodal `K′`.**  As
`isRupert_of_chords_of_firstOrderInward`, with `K′` robustly unimodal at `u₀` and
without horizontal double normal (Theorem 18.3). -/
theorem isRupert_of_chords_robustUnimodal (V M : Finset ℝ³) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : R ∈ SO3) {u₀ : ℝ³} {r : ℝ} (hr : 0 < r) (hRu : R.toEuclideanLin u₀ = r • ez)
    {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V) (hxM : ∀ i, x i ∉ M)
    (hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))))
    (hin : ∀ v ∈ V, v ∉ M → (∀ i, v ≠ x i) → proj_xy (R.toEuclideanLin v) ∈
      interior (convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (x i)))))
    (hz : IsRobustUnimodal (fun i => (R.toEuclideanLin (x i)) 2))
    (hnd : ¬ HasHorizontalDoubleNormal (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2))
    (hM : ∀ m ∈ M, ∃ i : ZMod k, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = x i + s • (x (i + 1) - x i) + δ • u₀) : IsRupert V := by
  classical
  exact isRupert_of_chords_of_firstOrderInward V M R hR hr hRu x hxV hxM hp hin
    (exists_firstOrderInward_image_of_robustUnimodal (V \ M) R x
      (fun i => mem_sdiff.mpr ⟨hxV i, hxM i⟩) hp
      (fun v hv hvx => hin v (mem_sdiff.mp hv).1 (mem_sdiff.mp hv).2 hvx) hz hnd) hM

/-- **Theorem 8.9 with a robustly unimodal `K_v`.**  As
`isRupert_of_edgeChords_of_firstOrderInward`, with `K_v` robustly unimodal at `u₀` and
without horizontal double normal (Theorem 18.3). -/
theorem isRupert_of_edgeChords_robustUnimodal (V M : Finset ℝ³) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : R ∈ SO3) {u₀ : ℝ³} {r : ℝ} (hr : 0 < r) (hRu : R.toEuclideanLin u₀ = r • ez)
    {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) (i₀ : ZMod k) (w : ℝ³) (h : ℝ) (hwV : w ∈ V)
    (hw : w = x i₀ - h • u₀) (hh : h ≠ 0) (hxV : ∀ i, x i ∈ V) (hxM : ∀ i, x i ∉ M)
    (hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))))
    (hin : ∀ v ∈ V, v ∉ M → v ≠ w → (∀ i, v ≠ x i) → proj_xy (R.toEuclideanLin v) ∈
      interior (convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (x i)))))
    (hz : IsRobustUnimodal (fun i => (R.toEuclideanLin (x i)) 2))
    (hnd : ¬ HasHorizontalDoubleNormal (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2))
    (hM : ∀ m ∈ M, EdgeMiddle u₀ (x i₀) w (x (i₀ + 1)) (x (i₀ - 1)) h m) : IsRupert V := by
  classical
  exact isRupert_of_edgeChords_of_firstOrderInward V M R hR hr hRu x i₀ w h hwV hw hh hxV hxM hp
    hin (exists_firstOrderInward_image_of_robustUnimodal ((V \ M).erase w) R x
      (fun i => mem_erase.mpr ⟨corner_ne_axle hr hRu hp hw hh i, mem_sdiff.mpr ⟨hxV i, hxM i⟩⟩) hp
      (fun v hv hvx => by
        obtain ⟨hvw, hv'⟩ := mem_erase.mp hv
        exact hin v (mem_sdiff.mp hv').1 (mem_sdiff.mp hv').2 hvw hvx) hz hnd) hM

/-- **Lemma 16.27 with a robustly unimodal `K_v` (Theorem 18.3).** The view `u₀`
(`R u₀ = r e_z`, `r > 0`) runs along the edge `vw`, `v = x i₀`, `w = v − h u₀`. The silhouette
of `K_v` (the hull without the middles and `w`) is the strictly convex counterclockwise polygon
`x` (every other point of `K_v` strictly inside), with robustly unimodal depths and no
horizontal double normal. Each middle lies over a side `[x i, x (i + 1)]` of that polygon,
at a depth offset `δ ≠ 0`: the sides at `v` carry the middles of the two faces at `vw`
(chords from `v`), the other sides those of further faces seen edge-on. Then `V` is
Rupert. -/
theorem isRupert_of_edgeChords_uniform_robustUnimodal (V M : Finset ℝ³)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : R ∈ SO3) {u₀ : ℝ³} {r : ℝ} (hr : 0 < r) (hRu : R.toEuclideanLin u₀ = r • ez)
    {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) (i₀ : ZMod k) (w : ℝ³) (h : ℝ)
    (hw : w = x i₀ - h • u₀) (hh : h ≠ 0) (hxV : ∀ i, x i ∈ V) (hxM : ∀ i, x i ∉ M)
    (hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))))
    (hin : ∀ v ∈ V, v ∉ M → v ≠ w → (∀ i, v ≠ x i) → proj_xy (R.toEuclideanLin v) ∈
      interior (convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (x i)))))
    (hz : IsRobustUnimodal (fun i => (R.toEuclideanLin (x i)) 2))
    (hnd : ¬ HasHorizontalDoubleNormal (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2))
    (hM : ∀ m ∈ M, ∃ i : ZMod k, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = x i + s • (x (i + 1) - x i) + δ • u₀) : IsRupert V := by
  classical
  have hu₀ := ne_zero_of_rot_eq hr hRu
  have hxw : ∀ i, x i ≠ w := corner_ne_axle hr hRu hp hw hh
  obtain ⟨ω, τ, hcert, hedge⟩ := exists_tiltCert_of_robustUnimodal ((V \ M).erase w) R hR hr hRu x
    (fun i => mem_erase.mpr ⟨hxw i, mem_sdiff.mpr ⟨hxV i, hxM i⟩⟩) hp
    (fun v hv hvx => by
      obtain ⟨hvw, hv'⟩ := mem_erase.mp hv
      exact hin v (mem_sdiff.mp hv').1 (mem_sdiff.mp hv').2 hvw hvx) hz hnd
  have hB := hedge (i₀ - 1)
  rw [sub_add_cancel] at hB
  refine isRupert_of_edgeChords_uniform V M u₀ ω τ (x i₀) w (x (i₀ + 1)) (x (i₀ - 1)) h hu₀
    (hxV _) (hxV _) (hxV _) hw hh (det3_corner_pos hR hr hRu hp i₀) (hedge i₀).1 hB.2
    (fun y hy hyM _ hyw => (hcert y (mem_erase.mpr ⟨hyw, mem_sdiff.mpr ⟨hy, hyM⟩⟩)).mono
      ((erase_subset _ _).trans sdiff_subset)) fun m hm => ?_
  obtain ⟨i, s, δ, hs0, hs1, hδ, rfl⟩ := hM m hm
  exact ⟨x i, hxV i, x (i + 1), hxV _, x (i - 1), hxV _, s, δ, hs0, hs1, hδ, rfl,
    det3_corner_pos hR hr hRu hp i, (hedge i).1, (hedge i).2⟩

/-- **Theorem 18.1, tie form** (Lemma 16.27′ with Theorem 18.3; §18.3 after the proof of
Theorem 18.3).  One vertex `x i` over each corner of the shadow; the silhouette of
`V ∖ (M ∪ D)` at `u₀` is the strictly convex counterclockwise polygon `x` with robustly
unimodal depths and no horizontal double normal; each middle lies over a side of `x`, and
each double lies over a corner of `x` (the axle of an edge crossing is one of them). -/
theorem isRupert_of_uniform_doubles_robustUnimodal (V M D : Finset ℝ³)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : R ∈ SO3) {u₀ : ℝ³} {r : ℝ} (hr : 0 < r) (hRu : R.toEuclideanLin u₀ = r • ez)
    {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V) (hxM : ∀ i, x i ∉ M)
    (hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))))
    (hin : ∀ v ∈ V, v ∉ M → v ∉ D → (∀ i, v ≠ x i) → proj_xy (R.toEuclideanLin v) ∈
      interior (convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (x i)))))
    (hz : IsRobustUnimodal (fun i => (R.toEuclideanLin (x i)) 2))
    (hnd : ¬ HasHorizontalDoubleNormal (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2))
    (hM : ∀ m ∈ M, ∃ i : ZMod k, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = x i + s • (x (i + 1) - x i) + δ • u₀)
    (hD : ∀ y ∈ D, ∃ i : ZMod k, ∃ h : ℝ, h ≠ 0 ∧ y = x i - h • u₀) : IsRupert V := by
  classical
  have hu₀ := ne_zero_of_rot_eq hr hRu
  have hxD : ∀ i, x i ∉ D := by
    intro i hiD
    obtain ⟨j, h, hh, hy⟩ := hD (x i) hiD
    exact corner_ne_axle hr hRu hp hy hh i rfl
  obtain ⟨ω, τ, hcert, hedge⟩ := exists_tiltCert_of_robustUnimodal ((V \ M) \ D) R hR hr hRu x
    (fun i => mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hxV i, hxM i⟩, hxD i⟩) hp
    (fun v hv hvx => by
      obtain ⟨hv1, hvD⟩ := mem_sdiff.mp hv
      exact hin v (mem_sdiff.mp hv1).1 (mem_sdiff.mp hv1).2 hvD hvx) hz hnd
  refine isRupert_of_uniform_doubles V M D u₀ ω τ hu₀ ?_
    (fun y hy hyM hyD => (hcert y (mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hy, hyM⟩, hyD⟩)).mono
      (sdiff_subset.trans sdiff_subset)) ?_
  · intro y hyD
    obtain ⟨i, h, hh, rfl⟩ := hD y hyD
    have hB := hedge (i - 1)
    rw [sub_add_cancel] at hB
    exact ⟨x i, hxV i, x (i + 1), hxV _, x (i - 1), hxV _, h, hh, rfl,
      det3_corner_pos hR hr hRu hp i, (hedge i).1, hB.2⟩
  · intro m hm
    obtain ⟨i, s, δ, hs0, hs1, hδ, rfl⟩ := hM m hm
    exact ⟨x i, hxV i, x (i + 1), hxV _, x (i - 1), hxV _, s, δ, hs0, hs1, hδ, rfl,
      det3_corner_pos hR hr hRu hp i, (hedge i).1, (hedge i).2⟩

/-- **Theorem 8.9 with a robustly unimodal `K_v`, at an edge view given by determinant
tests.**  Two faces share the edge `v w` (`v = x i₀`, `w = v − h u₀`); the cycle `x`
passes all determinant tests at `u₀` (strictly convex, counterclockwise), every
other point except the middles `M` and `w` is strictly inside, the depths
`⟪x i, u₀⟫` are robustly unimodal, and there is no horizontal double normal.
Then `V` is Rupert. -/
theorem isRupert_of_edgeView_robust (V M : Finset ℝ³) (u₀ : ℝ³) (hu₀ : u₀ ≠ 0) {k : ℕ} [NeZero k]
    (hk : 3 ≤ k) (x : ZMod k → ℝ³) (i₀ : ZMod k) (w : ℝ³) (h : ℝ) (hwV : w ∈ V)
    (hw : w = x i₀ - h • u₀) (hh : h ≠ 0) (hxV : ∀ i, x i ∈ V) (hxM : ∀ i, x i ∉ M)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (x (i + 1) - x i) (x j - x i) u₀)
    (hrest : ∀ y ∈ V, y ∉ M → y ≠ w → (∀ j, y ≠ x j) → ∀ i,
      0 < det3 (x (i + 1) - x i) (y - x i) u₀)
    (hz : IsRobustUnimodal (fun i => ⟪x i, u₀⟫)) (hnd : NoHDNAt (V.erase w) u₀)
    (hM : ∀ m ∈ M, EdgeMiddle u₀ (x i₀) w (x (i₀ + 1)) (x (i₀ - 1)) h m) : IsRupert V := by
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
  refine isRupert_of_edgeChords_robustUnimodal V M R hR hr hRu x i₀ w h hwV hw hh hxV hxM hp
    ?_ ?_ ?_ hM
  · intro y hy hyM hyw hyx
    refine hp.mem_interior_of_left fun i => ?_
    simp only [proj_rot_sub]
    exact cross2_proj_rot_pos hR hr hRu (hrest y hy hyM hyw hyx i)
  · simp only [hdepth]; exact hz.smul (inv_pos.mpr hr)
  · exact hnd R hR r hr.ne' hRu k x
      (fun i => mem_erase.mpr ⟨corner_ne_axle hr hRu hp hw hh i, hxV i⟩) hp

/-- **Proposition 8.8 with Theorem 18.3, at a view given by determinant tests** (no rotation
in the statement; the vertex-crossing analogue of `isRupert_of_edgeView_robust`).  The cycle `x`
passes all determinant tests at `u₀` (strictly convex, counterclockwise), every point of `V`
other than the corners and the middles `M` is strictly inside, the depths `⟪x i, u₀⟫` are
robustly unimodal, there is no horizontal double normal, and each middle lies over a side:
`m = x i + s (x (i + 1) − x i) + δ u₀`, `0 < s < 1`, `δ ≠ 0`.  Then `V` is Rupert. -/
theorem isRupert_of_vertexView_robust (V M : Finset ℝ³) (u₀ : ℝ³) (hu₀ : u₀ ≠ 0) {k : ℕ} [NeZero k]
    (hk : 3 ≤ k) (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V) (hxM : ∀ i, x i ∉ M)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (x (i + 1) - x i) (x j - x i) u₀)
    (hrest : ∀ y ∈ V, y ∉ M → (∀ j, y ≠ x j) → ∀ i,
      0 < det3 (x (i + 1) - x i) (y - x i) u₀)
    (hz : IsRobustUnimodal (fun i => ⟪x i, u₀⟫)) (hnd : NoHDNAt V u₀)
    (hM : ∀ m ∈ M, ∃ i : ZMod k, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = x i + s • (x (i + 1) - x i) + δ • u₀) : IsRupert V := by
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
  refine isRupert_of_chords_robustUnimodal V M R hR hr hRu x hxV hxM hp ?_ ?_ ?_ hM
  · intro y hy hyM hyx
    refine hp.mem_interior_of_left fun i => ?_
    simp only [proj_rot_sub]
    exact cross2_proj_rot_pos hR hr hRu (hrest y hy hyM hyx i)
  · simp only [hdepth]; exact hz.smul (inv_pos.mpr hr)
  · exact hnd R hR r hr.ne' hRu k x hxV hp

/-- **Lemma 16.27′ at an edge view given by determinant tests.**  The cycle `x` passes all
triple tests at `u₀` (strictly convex, counterclockwise), every other point except the middles
`M` and the doubles `D` is strictly inside, the depths `⟪x i, u₀⟫` are robustly unimodal and
there is no horizontal double normal (`NoHDNAt W u₀` for a set `W` containing the rim).  Each
middle lies over a side of `x` at a depth offset `δ ≠ 0`, each double over a corner.  Then `V`
is Rupert. -/
theorem isRupert_of_edgeView_uniform_robust (V M D W : Finset ℝ³) (u₀ : ℝ³) (hu₀ : u₀ ≠ 0)
    {k : ℕ} [NeZero k] (hk : 3 ≤ k) (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V)
    (hxM : ∀ i, x i ∉ M)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (x (i + 1) - x i) (x j - x i) u₀)
    (hrest : ∀ y ∈ V, y ∉ M → y ∉ D → (∀ j, y ≠ x j) → ∀ i,
      0 < det3 (x (i + 1) - x i) (y - x i) u₀)
    (hz : IsRobustUnimodal (fun i => ⟪x i, u₀⟫)) (hnd : NoHDNAt W u₀) (hxW : ∀ i, x i ∈ W)
    (hM : ∀ m ∈ M, ∃ i : ZMod k, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = x i + s • (x (i + 1) - x i) + δ • u₀)
    (hD : ∀ y ∈ D, ∃ i : ZMod k, ∃ h : ℝ, h ≠ 0 ∧ y = x i - h • u₀) : IsRupert V := by
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
  refine isRupert_of_uniform_doubles_robustUnimodal V M D R hR hr hRu x hxV hxM hp ?_ ?_ ?_ hM hD
  · intro y hy hyM hyD hyx
    refine hp.mem_interior_of_left fun i => ?_
    simp only [proj_rot_sub]
    exact cross2_proj_rot_pos hR hr hRu (hrest y hy hyM hyD hyx i)
  · simp only [hdepth]; exact hz.smul (inv_pos.mpr hr)
  · exact hnd R hR r hr.ne' hRu k x hxW hp

end Minimality

end
