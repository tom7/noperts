module

public import Minimality.EdgeChords
public import Minimality.Unimodal

@[expose] public section

/-!
# Unimodal silhouettes give local certificates (Theorem 7.3 → Propositions 8.8, 8.9)

Theorem 7.3 (`exists_firstOrderInward_of_unimodal`) gives, at a view whose
silhouette is a strictly convex counterclockwise polygon `x` with cyclically
unimodal depths and no horizontal double normal (every other point strictly
inside), a strictly inward first-order motion.  Propositions 8.8 and 8.9
(`isRupert_of_chords`, `isRupert_of_edgeChords`) ask instead for *local
certificates* `TiltCert` at the view, plus strict inward motion of the
polygon's corners across their edges.  This file bridges the two
(`exists_tiltCert_of_unimodal`), frame-free at the view `u₀` with
`R u₀ = r e_z`, `r > 0`:

* a corner `x i` gets the certificate with neighbours `x (i − 1)`, `x (i + 1)`:
  `x i + ε ν` is interior, hence strictly left of both edges at `x i`
  (`IsCcwPolygon.left_of_mem_interior`);
* an interior point `q` cannot always be put strictly inside a triangle of
  points (the centre of a square lies on both diagonals), so it also gets a
  *corner* certificate: its velocity `ν` points strictly into the angle
  `x l, q, x (l + 1)` for a consecutive pair with `cross2 (x l − q) ν > 0 >
  cross2 (x (l + 1) − q) ν` (`exists_pos_succ_neg`), which exists once
  `ν` is parallel to no `x j − q`.  The translation `τ` is perturbed along a
  direction `t` that achieves this (`exists_inner_ne_zero`); the corners' tests
  are strict and survive.

Corollaries: `isRupert_of_chords_unimodal` (Proposition 8.8 with "`K′` is
first-order free" replaced by "`K′` has a unimodal silhouette at `u₀` without
horizontal double normal", the middles lying over silhouette edges of `K′`)
and `isRupert_of_edgeChords_unimodal` (Theorem 8.9 likewise, for `K_v` with
`v` a silhouette corner and `A`, `B` its neighbours).
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

section Algebra

variable (a b c t u y ω τ : ℝ³) (η : ℝ)

theorem det3_eq_inner_cross : det3 a b u = ⟪cross u a, b⟫ := by
  simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem det3_sub_comm_left : det3 (y - c) b u = -det3 (c - y) b u := by
  simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

/-- The velocity under the translation `τ + η t`. -/
theorem det3_vel_perturb :
    det3 a (cross ω y + (τ + η • t)) u = det3 a (cross ω y + τ) u + η * det3 a t u := by
  simp [det3, cross, PiLp.inner_apply, Fin.sum_univ_three]; ring

end Algebra

theorem cross2_sub_sub (a b q : ℝ²) : cross2 (a - q) (b - q) = cross2 (b - a) (q - a) := by
  simp [cross2]; ring

theorem eventually_ne_affine {A B : ℝ} (hB : B ≠ 0) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), A + η * B ≠ 0 := by
  rcases eq_or_ne A 0 with rfl | hA
  · filter_upwards [self_mem_nhdsWithin] with η hη
    rw [zero_add]; exact mul_ne_zero (show (0 : ℝ) < η from hη).ne' hB
  · have hc : Continuous fun η : ℝ => A + η * B := by fun_prop
    exact (hc.continuousAt.eventually_ne (by simpa using hA)).filter_mono nhdsWithin_le_nhds

/-- A cyclic sequence of nonzero reals taking both signs changes from positive
to negative somewhere. -/
theorem exists_pos_succ_neg {k : ℕ} [NeZero k] (f : ZMod k → ℝ) (h0 : ∀ j, f j ≠ 0)
    {i j : ZMod k} (hi : 0 < f i) (hj : f j < 0) : ∃ l, 0 < f l ∧ f (l + 1) < 0 := by
  by_contra H
  push Not at H
  have hall : ∀ n : ℕ, 0 < f (i + n) := by
    intro n
    induction n with
    | zero => simpa using hi
    | succ n ih =>
      rw [Nat.cast_succ, ← add_assoc]
      exact lt_of_le_of_ne (H _ ih) (h0 _).symm
  have := hall (j - i).val
  rw [ZMod.natCast_zmod_val, show i + (j - i) = j by ring] at this
  linarith

/-- The corners of a polygon around an interior point `q` lie strictly on
both sides of every line through `q`. -/
theorem exists_cross2_pos_of_mem_interior {k : ℕ} {p : ZMod k → ℝ²} {q d : ℝ²} (hd : d ≠ 0)
    (hq : q ∈ interior (convexHull ℝ (Set.range p))) : ∃ j, 0 < cross2 (p j - q) d := by
  set n : ℝ² := !₂[d 1, -(d 0)] with hn
  have hnw : ∀ w : ℝ², ⟪n, w⟫ = cross2 w d := fun w => by
    simp [hn, cross2, PiLp.inner_apply, Fin.sum_univ_two]; ring
  have hn0 : n ≠ 0 := by
    intro h0
    apply hd
    have e0 := congrArg (fun z : ℝ² => z 0) h0
    have e1 := congrArg (fun z : ℝ² => z 1) h0
    simp [hn] at e0 e1
    ext i; fin_cases i <;> simp [e0, e1]
  by_contra H
  push Not at H
  have hconv : Convex ℝ {c : ℝ² | ⟪n, c⟫ ≤ ⟪n, q⟫} :=
    convex_halfSpace_le (innerₛₗ ℝ n).isLinear _
  have hsub : convexHull ℝ (Set.range p) ⊆ {c : ℝ² | ⟪n, c⟫ ≤ ⟪n, q⟫} := by
    refine convexHull_min ?_ hconv
    rintro _ ⟨j, rfl⟩
    have h1 := H j
    rw [← hnw, inner_sub_right] at h1
    show ⟪n, p j⟫ ≤ ⟪n, q⟫
    linarith
  have := inner_neg_of_mem_interior hn0 (fun c hc => by
    have h1 : ⟪n, c⟫ ≤ ⟪n, q⟫ := hsub hc
    rw [inner_sub_right]; linarith) hq
  simp at this

/-- `TiltCert` is monotone in the point set. -/
theorem TiltCert.mono {V W : Finset ℝ³} {w ω τ x : ℝ³} (hVW : V ⊆ W) (h : TiltCert V w ω τ x) :
    TiltCert W w ω τ x := by
  rcases h with ⟨y₀, hy₀, y₁, hy₁, h⟩ | ⟨a, ha, b, hb, c, hc, h⟩
  · exact Or.inl ⟨y₀, hVW hy₀, y₁, hVW hy₁, h⟩
  · exact Or.inr ⟨a, hVW ha, b, hVW hb, c, hVW hc, h⟩

section Polygon

variable {R : Matrix (Fin 3) (Fin 3) ℝ} {u₀ : ℝ³} {r : ℝ} {k : ℕ} {x : ZMod k → ℝ³}

theorem zmod_sub_one_ne {k : ℕ} (hk : 3 ≤ k) (i : ZMod k) : i - 1 ≠ i := by
  have := zmod_ne_add_one (by omega) (i - 1)
  rwa [sub_add_cancel] at this

/-- A silhouette corner turns strictly left (determinant form). -/
theorem det3_corner_pos (hR : R ∈ SO3) (hr : 0 < r) (hRu : R.toEuclideanLin u₀ = r • ez)
    (hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i)))) (i : ZMod k) :
    0 < det3 (x (i + 1) - x i) (x (i - 1) - x i) u₀ := by
  rw [← cross2_proj_rot hR hRu, ← proj_rot_sub, ← proj_rot_sub]
  exact mul_pos hr (hp.2 i (i - 1) (zmod_sub_one_ne hp.1 i) (zmod_sub_one_ne_add_one hp.1 i))

theorem ne_zero_of_rot_eq (hr : 0 < r) (hRu : R.toEuclideanLin u₀ = r • ez) : u₀ ≠ 0 := by
  rintro rfl
  have := congrArg (fun z : ℝ³ => z 2) hRu
  simp [ez] at this
  exact hr.ne' this.symm

end Polygon

/-- **Theorem 7.3, certificate form.**  At a view `u₀` (`R u₀ = r e_z`,
`r > 0`) where the silhouette of `V` is the strictly convex counterclockwise
polygon `x`, every other point projecting strictly inside, with cyclically
unimodal depths and no horizontal double normal, some first-order motion
`(ω, τ)` has a local certificate at every point of `V`, and moves each corner
strictly to the inner side of both of its edges. -/
theorem exists_tiltCert_of_unimodal (V : Finset ℝ³) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : R ∈ SO3) {u₀ : ℝ³} {r : ℝ} (hr : 0 < r) (hRu : R.toEuclideanLin u₀ = r • ez)
    {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V)
    (hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))))
    (hin : ∀ v ∈ V, (∀ i, v ≠ x i) → proj_xy (R.toEuclideanLin v) ∈
      interior (convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (x i)))))
    (hz : IsCyclicUnimodal (fun i => (R.toEuclideanLin (x i)) 2))
    (hnd : ¬ HasHorizontalDoubleNormal (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2)) :
    ∃ ω τ : ℝ³, (∀ y ∈ V, TiltCert V u₀ ω τ y) ∧
      ∀ i, 0 < det3 (x (i + 1) - x i) (cross ω (x i) + τ) u₀ ∧
        0 < det3 (x (i + 1) - x i) (cross ω (x (i + 1)) + τ) u₀ := by
  classical
  have hk := hp.1
  set P : ℝ³ → ℝ² := fun y => proj_xy (R.toEuclideanLin y) with hP
  have hdet : ∀ a b : ℝ³, det3 a b u₀ = r * cross2 (P a) (P b) := fun a b =>
    (cross2_proj_rot hR hRu a b).symm
  have hsub : ∀ a b : ℝ³, P (a - b) = P a - P b := fun a b => (proj_rot_sub R a b).symm
  -- Theorem 7.3: a strictly inward first-order motion
  obtain ⟨ω', τ', hFO⟩ := exists_firstOrderInward_of_unimodal (V.image R.toEuclideanLin)
    (fun i => R.toEuclideanLin (x i)) (fun i => mem_image_of_mem _ (hxV i)) hp
    (by
      intro w hw hc
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hw
      exact hin v hv fun i h => hc i (by rw [h]))
    hz hnd
  obtain ⟨ω, rfl⟩ := (so3Isometry hR).surjective ω'
  obtain ⟨τ₀, rfl⟩ := (so3Isometry hR).surjective τ'
  rw [so3Isometry_apply, so3Isometry_apply] at hFO
  have hvel : ∀ y, screenVel (R.toEuclideanLin ω) (R.toEuclideanLin τ₀) (R.toEuclideanLin y) =
      P (cross ω y + τ₀) := fun y => by
    simp only [screenVel, crossMatrix_apply, hP, map_add, cross_toEuclideanLin hR]
  -- the shadow is the polygon
  have hS : proj_xy '' convexHull ℝ ((V.image R.toEuclideanLin : Finset ℝ³) : Set ℝ³) ⊆
      convexHull ℝ (Set.range fun i => P (x i)) := by
    rw [show (proj_xy : ℝ³ → ℝ²) = projL from rfl, LinearMap.image_convexHull]
    apply convexHull_min _ (convex_convexHull ℝ _)
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hw
    by_cases hc : ∃ i, v = x i
    · obtain ⟨i, rfl⟩ := hc; exact subset_convexHull ℝ _ ⟨i, rfl⟩
    · push Not at hc; exact interior_subset (hin v hv hc)
  -- corners move strictly into both adjacent edges
  have hcorner : ∀ i, 0 < cross2 (P (x (i + 1)) - P (x i)) (P (cross ω (x i) + τ₀)) ∧
      0 < cross2 (P (x i) - P (x (i - 1))) (P (cross ω (x i) + τ₀)) := by
    intro i
    obtain ⟨ε, hε, hεin⟩ := hFO _ (mem_image_of_mem _ (hxV i))
    rw [hvel] at hεin
    have hq := interior_mono hS hεin
    have h1 : 0 < cross2 (P (x (i + 1)) - P (x i))
        ((P (x i) + ε • P (cross ω (x i) + τ₀)) - P (x i)) := hp.left_of_mem_interior i hq
    have h2 : 0 < cross2 (P (x (i - 1 + 1)) - P (x (i - 1)))
        ((P (x i) + ε • P (cross ω (x i) + τ₀)) - P (x (i - 1))) :=
      hp.left_of_mem_interior (i - 1) hq
    rw [add_sub_cancel_left, cross2_smul_right] at h1
    rw [sub_add_cancel, show P (x i) + ε • P (cross ω (x i) + τ₀) - P (x (i - 1)) =
      (P (x i) - P (x (i - 1))) + ε • P (cross ω (x i) + τ₀) by abel, cross2_add_right,
      cross2_smul_right, cross2_self, zero_add] at h2
    exact ⟨pos_of_mul_pos_right h1 hε.le, pos_of_mul_pos_right h2 hε.le⟩
  have C1 : ∀ i, 0 < det3 (x (i + 1) - x i) (cross ω (x i) + τ₀) u₀ := fun i => by
    rw [hdet, hsub]; exact mul_pos hr (hcorner i).1
  have C2 : ∀ i, 0 < det3 (x (i + 1) - x i) (cross ω (x (i + 1)) + τ₀) u₀ := fun i => by
    have := (hcorner (i + 1)).2
    rw [add_sub_cancel_right] at this
    rw [hdet, hsub]; exact mul_pos hr this
  -- interior points see consecutive corners counterclockwise
  have hint : ∀ y ∈ V, (∀ i, y ≠ x i) → ∀ j, 0 < det3 (x j - y) (x (j + 1) - y) u₀ := by
    intro y hy hyx j
    rw [hdet, hsub, hsub, cross2_sub_sub]
    exact mul_pos hr (hp.left_of_mem_interior j (hin y hy hyx))
  -- a perturbation direction for the translation
  set I := (univ : Finset (ZMod k)) ×ˢ V.filter (fun y => ∀ i, y ≠ x i) with hI
  have hn : ∀ jy ∈ I, cross u₀ (x jy.1 - jy.2) ≠ 0 := by
    intro jy hjy h0
    simp only [hI, mem_product, mem_filter] at hjy
    have := hint jy.2 hjy.2.1 hjy.2.2 jy.1
    rw [det3_eq_inner_cross, h0, inner_zero_left] at this
    exact lt_irrefl _ this
  obtain ⟨t, ht⟩ := exists_inner_ne_zero I (fun jy => cross u₀ (x jy.1 - jy.2)) hn
  have E1 : ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ i,
      0 < det3 (x (i + 1) - x i) (cross ω (x i) + (τ₀ + η • t)) u₀ :=
    eventually_all.2 fun i => by
      simp only [det3_vel_perturb]; exact eventually_pos_affine (Or.inl (C1 i))
  have E2 : ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ i,
      0 < det3 (x (i + 1) - x i) (cross ω (x (i + 1)) + (τ₀ + η • t)) u₀ :=
    eventually_all.2 fun i => by
      simp only [det3_vel_perturb]; exact eventually_pos_affine (Or.inl (C2 i))
  have E3 : ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ y ∈ V, (∀ i, y ≠ x i) → ∀ j,
      det3 (x j - y) (cross ω y + (τ₀ + η • t)) u₀ ≠ 0 := by
    refine (eventually_all_finset V).2 fun y hy => ?_
    by_cases hyx : ∀ i, y ≠ x i
    · refine (eventually_all.2 fun j => ?_).mono fun _ h _ => h
      simp only [det3_vel_perturb]
      refine eventually_ne_affine ?_
      rw [det3_eq_inner_cross]
      exact ht (j, y) (by simp only [hI, mem_product, mem_filter, mem_univ, true_and]; exact ⟨hy, hyx⟩)
    · exact Eventually.of_forall fun _ h => absurd h hyx
  obtain ⟨η, h1, h2, h3⟩ := (E1.and (E2.and E3)).exists
  refine ⟨ω, τ₀ + η • t, fun y hy => ?_, fun i => ⟨h1 i, h2 i⟩⟩
  by_cases hc : ∃ i, y = x i
  · -- a corner, between its neighbours
    obtain ⟨i, rfl⟩ := hc
    have h2' := h2 (i - 1)
    rw [sub_add_cancel] at h2'
    exact Or.inl ⟨x (i - 1), hxV _, x (i + 1), hxV _, det3_corner_pos hR hr hRu hp i, h1 i, h2'⟩
  · -- an interior point: a corner certificate from a sign change of its velocity
    push Not at hc
    set d := P (cross ω y + (τ₀ + η • t)) with hd
    have hf : ∀ j, det3 (x j - y) (cross ω y + (τ₀ + η • t)) u₀ =
        r * cross2 (P (x j) - P y) d := fun j => by rw [hdet, hsub]
    have hq := hin y hy hc
    have hd0 : d ≠ 0 := by
      intro h0
      apply h3 y hy hc 0
      rw [hf, h0]; simp [cross2]
    obtain ⟨i, hi⟩ := exists_cross2_pos_of_mem_interior hd0 hq
    obtain ⟨j, hj⟩ := exists_cross2_pos_of_mem_interior (neg_ne_zero.mpr hd0) hq
    have hneg : ∀ a : ℝ², cross2 a (-d) = -cross2 a d := fun a => by simp [cross2]; ring
    rw [hneg] at hj
    obtain ⟨l, hl1, hl2⟩ := exists_pos_succ_neg
      (fun j => det3 (x j - y) (cross ω y + (τ₀ + η • t)) u₀) (h3 y hy hc)
      (i := i) (j := j) (by rw [hf]; exact mul_pos hr hi)
      (by rw [hf]; exact mul_neg_of_pos_of_neg hr (by linarith))
    refine Or.inl ⟨x (l + 1), hxV _, x l, hxV _, hint y hy hc l, hl1, ?_⟩
    rw [det3_sub_comm_left]; linarith

/-- **Proposition 8.8 with a unimodal `K′`.**  Let `M ⊆ V` be the middles at
the view `u₀` (`R u₀ = r e_z`, `r > 0`), each over a silhouette edge
`[x i, x (i + 1)]` of the rest `K′`: `m = x i + s (x (i + 1) − x i) + δ u₀`,
`0 < s < 1`, `δ ≠ 0`.  If the silhouette of `K′` at `u₀` is the strictly
convex counterclockwise polygon `x` (every other point of `K′` strictly inside),
with cyclically unimodal depths and no horizontal double normal, then `V` is
Rupert. -/
theorem isRupert_of_chords_unimodal (V M : Finset ℝ³) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : R ∈ SO3) {u₀ : ℝ³} {r : ℝ} (hr : 0 < r) (hRu : R.toEuclideanLin u₀ = r • ez)
    {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V) (hxM : ∀ i, x i ∉ M)
    (hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))))
    (hin : ∀ v ∈ V, v ∉ M → (∀ i, v ≠ x i) → proj_xy (R.toEuclideanLin v) ∈
      interior (convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (x i)))))
    (hz : IsCyclicUnimodal (fun i => (R.toEuclideanLin (x i)) 2))
    (hnd : ¬ HasHorizontalDoubleNormal (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2))
    (hM : ∀ m ∈ M, ∃ i : ZMod k, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = x i + s • (x (i + 1) - x i) + δ • u₀) : IsRupert V := by
  classical
  obtain ⟨ω, τ, hcert, hedge⟩ := exists_tiltCert_of_unimodal (V \ M) R hR hr hRu x
    (fun i => mem_sdiff.mpr ⟨hxV i, hxM i⟩) hp
    (fun v hv hvx => hin v (mem_sdiff.mp hv).1 (mem_sdiff.mp hv).2 hvx) hz hnd
  refine isRupert_of_chords V M u₀ ω τ (ne_zero_of_rot_eq hr hRu)
    (fun y hy hyM => (hcert y (mem_sdiff.mpr ⟨hy, hyM⟩)).mono sdiff_subset) fun m hm => ?_
  obtain ⟨i, s, δ, hs0, hs1, hδ, rfl⟩ := hM m hm
  exact ⟨x i, hxV i, x (i + 1), hxV _, x (i - 1), hxV _, s, δ, hs0, hs1, hδ, rfl,
    det3_corner_pos hR hr hRu hp i, (hedge i).1, (hedge i).2⟩

/-- **Theorem 8.9 with a unimodal `K_v`.**  Two faces share the edge `vw`,
`w = v − h u₀` (`h ≠ 0`), at the view `u₀` (`R u₀ = r e_z`, `r > 0`), with
middles `M` (`EdgeMiddle`).  If the silhouette of `K_v` (the hull without the
middles and `w`) at `u₀` is the strictly convex counterclockwise polygon `x`
(every other point of `K_v` strictly inside), with cyclically unimodal depths
and no horizontal double normal, `v = x i₀`, and the far ends are its
neighbours `A = x (i₀ + 1)`, `B = x (i₀ − 1)`, then `V` is Rupert. -/
theorem isRupert_of_edgeChords_unimodal (V M : Finset ℝ³) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : R ∈ SO3) {u₀ : ℝ³} {r : ℝ} (hr : 0 < r) (hRu : R.toEuclideanLin u₀ = r • ez)
    {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) (i₀ : ZMod k) (w : ℝ³) (h : ℝ) (hwV : w ∈ V)
    (hw : w = x i₀ - h • u₀) (hh : h ≠ 0) (hxV : ∀ i, x i ∈ V) (hxM : ∀ i, x i ∉ M)
    (hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))))
    (hin : ∀ v ∈ V, v ∉ M → v ≠ w → (∀ i, v ≠ x i) → proj_xy (R.toEuclideanLin v) ∈
      interior (convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (x i)))))
    (hz : IsCyclicUnimodal (fun i => (R.toEuclideanLin (x i)) 2))
    (hnd : ¬ HasHorizontalDoubleNormal (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2))
    (hM : ∀ m ∈ M, EdgeMiddle u₀ (x i₀) w (x (i₀ + 1)) (x (i₀ - 1)) h m) : IsRupert V := by
  classical
  have hu₀ := ne_zero_of_rot_eq hr hRu
  -- `w` is not a corner: it projects onto `v`, and `v ≠ w`
  have hxw : ∀ i, x i ≠ w := by
    intro i hi
    have hPw : proj_xy (R.toEuclideanLin w) = proj_xy (R.toEuclideanLin (x i₀)) := by
      rw [hw, map_sub, map_smul, hRu, proj_xy_sub', proj_xy_smul', proj_xy_smul']
      have : proj_xy ez = 0 := by ext j; fin_cases j <;> simp [proj_xy, ez]
      rw [this]; simp
    have hii : i = i₀ := hp.injective (by simp only [hi, hPw])
    subst hii
    have : h • u₀ = 0 := by
      have := congrArg (fun z => x i - z) hi
      simp only [sub_self, hw, sub_sub_cancel] at this
      exact this.symm
    rcases smul_eq_zero.mp this with h0 | h0
    exacts [hh h0, hu₀ h0]
  obtain ⟨ω, τ, hcert, hedge⟩ := exists_tiltCert_of_unimodal ((V \ M).erase w) R hR hr hRu x
    (fun i => mem_erase.mpr ⟨hxw i, mem_sdiff.mpr ⟨hxV i, hxM i⟩⟩) hp
    (fun v hv hvx => by
      obtain ⟨hvw, hv'⟩ := mem_erase.mp hv
      exact hin v (mem_sdiff.mp hv').1 (mem_sdiff.mp hv').2 hvw hvx) hz hnd
  have hB := hedge (i₀ - 1)
  rw [sub_add_cancel] at hB
  refine isRupert_of_edgeChords V M u₀ ω τ (x i₀) w (x (i₀ + 1)) (x (i₀ - 1)) h hu₀ (hxV _) hwV
    (hxV _) (hxV _) hw hh (det3_corner_pos hR hr hRu hp i₀) (hedge i₀).1 hB.2 (hedge i₀).2 hB.1
    (fun y hy hyM _ hyw => (hcert y (mem_erase.mpr ⟨hyw, mem_sdiff.mpr ⟨hy, hyM⟩⟩)).mono
      ((erase_subset _ _).trans sdiff_subset)) hM

end Minimality

end
