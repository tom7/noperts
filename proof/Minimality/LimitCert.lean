module

public import Minimality.RobustCert

@[expose] public section

/-!
# The limit lemma (`FEWER-FACES-PROOFS.md` §18.2, §18.4, §19.7), in the shape's own metric

Lemma 18.2 passes a labelled certificate to limits of shapes: if every `K_n` is certified by
a crossing test with the same labelled rim `X` (strictly convex, counterclockwise, unimodal at
`K_n`), then at the limit `K` the rim only loses corners, and the corner rim stays unimodal.
Here the shapes enter only through their projected rims `ps n : ZMod k → ℝ²` and rim depths
`zs n : ZMod k → ℝ` (in any frames converging to `K`'s frame); the corner rim of `K` is given
by a choice `σ : ZMod k' → ZMod k` of one label over each corner of `K`'s shadow, and is
assumed strictly convex counterclockwise at `K` (`IsCcwPolygon`), which is what "the corners of
the shadow" means.

* `cycBetween_of_tendsto` (18.2 (a), the cyclic order): the chosen labels are a cyclic
  subsequence of `X` — three corners in counterclockwise order at `K` have a positive
  determinant, hence also at `K_n` for large `n`, so their labels are in `X`'s cyclic order.
* `isRobustUnimodal_cornerRim_of_tendsto` (18.2 (b) at `K`'s own metric): if the corner rim has
  distinct depths at `K`, it is robustly unimodal (unimodality passes to cyclic subsequences,
  `IsRobustUnimodal.comp`, and survives the limit, `isRobustUnimodal_of_tendsto`).
* `isRobustUnimodal_cornerRim_of_tendsto_single_tie` (18.4 (α)): with exactly one tied pair at
  `K`, certified shapes on both sides of the tie make the corner rim robustly unimodal.
* `isRobustUnimodal_cornerRim_or_of_tendsto` (pairs, 19.7 (a)): if each `K_n` has one of two
  certified tests, one of the two corner rims is robustly unimodal at `K`.
* **`isRupert_of_limitCertificate`** (18.2 with Theorems 18.1 and 18.3): `K` is Rupert if its
  corner rim has distinct depths, no horizontal double normal, and every other vertex lies
  inside, over an open side (a chord middle) or over a corner (a double).
  `isRupert_of_limitCertificate_tie`: the same with one tie, approached from both sides.
* `tendsto_proj_rot`, `tendsto_depth_rot`: the rims of converging shapes in converging frames
  converge.

Not formalized: the existence of limit certificates for a combinatorial type (the density of
the generic shapes and the finitely many labelled certificates of the tier proofs, 18.6 step 2),
metric-freeness across metrics (18.2 (b) at other metrics; here the conclusion is used only at
`K`'s metric, or on both sides of a single tie), and the count of codimension (18.6 step 4).
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

theorem cross2_zero_left (a : ℝ²) : cross2 0 a = 0 := by simp [cross2]

theorem continuous_cross2 : Continuous fun q : ℝ² × ℝ² => cross2 q.1 q.2 := by
  unfold cross2
  have h0 : Continuous fun v : ℝ² => v 0 := PiLp.continuous_apply 2 _ 0
  have h1 : Continuous fun v : ℝ² => v 1 := PiLp.continuous_apply 2 _ 1
  exact ((h0.comp continuous_fst).mul (h1.comp continuous_snd)).sub
    ((h1.comp continuous_fst).mul (h0.comp continuous_snd))

/-- **Lemma 18.2 (a), cyclic order.**  If the chosen labels `σ` of the corners of `K` form a
strictly convex counterclockwise polygon `p` at `K`, and the labelled rims `ps n` of shapes
converging to `K` are frequently strictly convex counterclockwise, then `σ` keeps the cyclic
order: the corner rim is a cyclic subsequence of the labelled rim. -/
theorem cycBetween_of_tendsto {k k' : ℕ} [NeZero k] {ι : Type*} {l : Filter ι}
    {ps : ι → ZMod k → ℝ²} (σ : ZMod k' → ZMod k) {p : ZMod k' → ℝ²}
    (hp : ∀ i, Tendsto (fun n => ps n (σ i)) l (𝓝 (p i)))
    (hcert : ∃ᶠ n in l, IsCcwPolygon (ps n)) (hcorner : IsCcwPolygon p) [NeZero k']
    {i j m : ZMod k'} (h : CycBetween i j m) : CycBetween (σ i) (σ j) (σ m) := by
  have hpos := hcorner.cross2_pos_of_cycBetween h
  have hlim : Tendsto (fun n => cross2 (ps n (σ j) - ps n (σ i)) (ps n (σ m) - ps n (σ i))) l
      (𝓝 (cross2 (p j - p i) (p m - p i))) :=
    (continuous_cross2.tendsto _).comp (((hp j).sub (hp i)).prodMk_nhds ((hp m).sub (hp i)))
  obtain ⟨n, hn, hpos'⟩ := (hcert.and_eventually (hlim.eventually (lt_mem_nhds hpos))).exists
  refine hn.cycBetween_of_cross2_pos (fun e => ?_) (fun e => ?_) (fun e => ?_) hpos'
  · rw [e, sub_self, cross2_zero_left] at hpos'; exact lt_irrefl _ hpos'
  · rw [e, cross2_self] at hpos'; exact lt_irrefl _ hpos'
  · rw [e, sub_self, cross2_comm, cross2_zero_left, neg_zero] at hpos'; exact lt_irrefl _ hpos'

/-- **Lemma 18.2 (b) at `K`'s own metric.**  Shapes `K_n → K` are frequently certified by a
labelled rim (`ps n` strictly convex counterclockwise, depths `zs n` robustly unimodal, e.g.
unimodal).  If the chosen corner labels `σ` of `K` form a strictly convex counterclockwise
polygon `p` with distinct depths `z`, the corner rim is robustly unimodal. -/
theorem isRobustUnimodal_cornerRim_of_tendsto {k k' : ℕ} [NeZero k] [NeZero k'] {ι : Type*}
    {l : Filter ι} {ps : ι → ZMod k → ℝ²} {zs : ι → ZMod k → ℝ} (σ : ZMod k' → ZMod k)
    {p : ZMod k' → ℝ²} {z : ZMod k' → ℝ}
    (hp : ∀ i, Tendsto (fun n => ps n (σ i)) l (𝓝 (p i)))
    (hz : ∀ i, Tendsto (fun n => zs n (σ i)) l (𝓝 (z i)))
    (hcert : ∃ᶠ n in l, IsCcwPolygon (ps n) ∧ IsRobustUnimodal (zs n))
    (hcorner : IsCcwPolygon p) (hinj : Function.Injective z) : IsRobustUnimodal z := by
  have hσ : ∀ i j m, CycBetween i j m → CycBetween (σ i) (σ j) (σ m) := fun i j m h =>
    cycBetween_of_tendsto σ hp (hcert.mono fun _ h => h.1) hcorner h
  exact isRobustUnimodal_of_tendsto (zs := fun n => zs n ∘ σ) hz
    (hcert.mono fun n h => h.2.comp σ hσ) hinj

/-- **Lemma 18.4 (α) for a limit certificate.**  As `isRobustUnimodal_cornerRim_of_tendsto`, but
the corner depths at `K` have exactly one tied pair `i, j`; certified shapes converge to `K`
from both sides of the tie (`zs n (σ j) < zs n (σ i)` along `l`, the reverse along `l'`). -/
theorem isRobustUnimodal_cornerRim_of_tendsto_single_tie {k k' : ℕ} [NeZero k] [NeZero k']
    {ι κ : Type*} {l : Filter ι} {l' : Filter κ} {ps : ι → ZMod k → ℝ²} {zs : ι → ZMod k → ℝ}
    {zs' : κ → ZMod k → ℝ} (σ : ZMod k' → ZMod k)
    {p : ZMod k' → ℝ²} {z : ZMod k' → ℝ} {i j : ZMod k'}
    (hp : ∀ i, Tendsto (fun n => ps n (σ i)) l (𝓝 (p i)))
    (hz : ∀ i, Tendsto (fun n => zs n (σ i)) l (𝓝 (z i)))
    (hz' : ∀ i, Tendsto (fun n => zs' n (σ i)) l' (𝓝 (z i)))
    (hcert : ∃ᶠ n in l, IsCcwPolygon (ps n) ∧ IsRobustUnimodal (zs n) ∧ zs n (σ j) < zs n (σ i))
    (hcert' : ∃ᶠ n in l', IsRobustUnimodal (zs' n) ∧ zs' n (σ i) < zs' n (σ j))
    (hcorner : IsCcwPolygon p)
    (hone : ∀ a b, a ≠ b → z a = z b → (a = i ∧ b = j) ∨ (a = j ∧ b = i)) :
    IsRobustUnimodal z := by
  have hσ : ∀ i j m, CycBetween i j m → CycBetween (σ i) (σ j) (σ m) := fun i j m h =>
    cycBetween_of_tendsto σ hp (hcert.mono fun _ h => h.1) hcorner h
  exact isRobustUnimodal_of_tendsto_single_tie (zs := fun n => zs n ∘ σ)
    (zs' := fun n => zs' n ∘ σ) hone hz hz'
    (hcert.mono fun n h => ⟨h.2.1.comp σ hσ, h.2.2⟩)
    (hcert'.mono fun n h => ⟨h.1.comp σ hσ, h.2⟩)

/-- **Lemma 18.2 (b) for a pair of tests** (and 19.7 (a)): every `K_n` has one of two certified
tests (rims `ps, zs` and `qs, ws`, corner labels `σ`, `τ`).  If both corner rims have distinct
depths at `K`, one of them is robustly unimodal. -/
theorem isRobustUnimodal_cornerRim_or_of_tendsto {k k' m m' : ℕ} [NeZero k] [NeZero k']
    [NeZero m] [NeZero m'] {ι : Type*} {l : Filter ι} {ps : ι → ZMod k → ℝ²}
    {zs : ι → ZMod k → ℝ} {qs : ι → ZMod m → ℝ²} {ws : ι → ZMod m → ℝ}
    (σ : ZMod k' → ZMod k) (τ : ZMod m' → ZMod m) {p : ZMod k' → ℝ²} {z : ZMod k' → ℝ}
    {q : ZMod m' → ℝ²} {w : ZMod m' → ℝ}
    (hp : ∀ i, Tendsto (fun n => ps n (σ i)) l (𝓝 (p i)))
    (hz : ∀ i, Tendsto (fun n => zs n (σ i)) l (𝓝 (z i)))
    (hq : ∀ i, Tendsto (fun n => qs n (τ i)) l (𝓝 (q i)))
    (hw : ∀ i, Tendsto (fun n => ws n (τ i)) l (𝓝 (w i)))
    (hcert : ∃ᶠ n in l, (IsCcwPolygon (ps n) ∧ IsRobustUnimodal (zs n)) ∨
      (IsCcwPolygon (qs n) ∧ IsRobustUnimodal (ws n)))
    (hp0 : IsCcwPolygon p) (hq0 : IsCcwPolygon q) (hzi : Function.Injective z)
    (hwi : Function.Injective w) : IsRobustUnimodal z ∨ IsRobustUnimodal w := by
  rcases frequently_or_distrib.mp hcert with h | h
  · exact Or.inl (isRobustUnimodal_cornerRim_of_tendsto σ hp hz h hp0 hzi)
  · exact Or.inr (isRobustUnimodal_cornerRim_of_tendsto τ hq hw h hq0 hwi)

/-! ### Converging shapes in converging frames -/

theorem tendsto_rot {ι : Type*} {l : Filter ι} {Rs : ι → Matrix (Fin 3) (Fin 3) ℝ}
    {R : Matrix (Fin 3) (Fin 3) ℝ} {ys : ι → ℝ³} {y : ℝ³} (hR : Tendsto Rs l (𝓝 R))
    (hy : Tendsto ys l (𝓝 y)) :
    Tendsto (fun n => (Rs n).toEuclideanLin (ys n)) l (𝓝 (R.toEuclideanLin y)) := by
  simp only [Matrix.toLpLin_apply]
  have h1 : Tendsto (fun n => WithLp.ofLp (ys n)) l (𝓝 (WithLp.ofLp y)) :=
    ((PiLp.continuous_ofLp 2 _).tendsto y).comp hy
  have h2 : Tendsto (fun n => (Rs n).mulVec (WithLp.ofLp (ys n))) l
      (𝓝 (R.mulVec (WithLp.ofLp y))) := by
    have hc : Continuous fun q : Matrix (Fin 3) (Fin 3) ℝ × (Fin 3 → ℝ) => q.1.mulVec q.2 :=
      continuous_fst.matrix_mulVec continuous_snd
    exact (hc.tendsto (R, WithLp.ofLp y)).comp (hR.prodMk_nhds h1)
  exact ((PiLp.continuous_toLp 2 _).tendsto _).comp h2

/-- The projected rims of converging shapes in converging frames converge. -/
theorem tendsto_proj_rot {ι : Type*} {l : Filter ι} {Rs : ι → Matrix (Fin 3) (Fin 3) ℝ}
    {R : Matrix (Fin 3) (Fin 3) ℝ} {ys : ι → ℝ³} {y : ℝ³} (hR : Tendsto Rs l (𝓝 R))
    (hy : Tendsto ys l (𝓝 y)) :
    Tendsto (fun n => proj_xy ((Rs n).toEuclideanLin (ys n))) l
      (𝓝 (proj_xy (R.toEuclideanLin y))) :=
  (continuous_proj_xy.tendsto _).comp (tendsto_rot hR hy)

/-- The depths of converging shapes in converging frames converge. -/
theorem tendsto_depth_rot {ι : Type*} {l : Filter ι} {Rs : ι → Matrix (Fin 3) (Fin 3) ℝ}
    {R : Matrix (Fin 3) (Fin 3) ℝ} {ys : ι → ℝ³} {y : ℝ³} (hR : Tendsto Rs l (𝓝 R))
    (hy : Tendsto ys l (𝓝 y)) :
    Tendsto (fun n => ((Rs n).toEuclideanLin (ys n)) 2) l (𝓝 ((R.toEuclideanLin y) 2)) :=
  ((PiLp.continuous_apply 2 _ 2).tendsto _).comp (tendsto_rot hR hy)

/-! ### Rupertness of the limit -/

/-- **The limit lemma, Rupert form** (Lemma 18.2 with Theorems 18.1 and 18.3, at `K`'s own
metric).  Let `V` be the vertices of `K`, viewed along `u₀` (`R u₀ = r e_z`, `r > 0`).  Shapes
`K_n → K`, in frames `Rs n → R`, are frequently certified by a labelled test: its rim
`ys n : ZMod k → ℝ³` projects to a strictly convex counterclockwise polygon with robustly
unimodal (e.g. distinct unimodal) depths.  At `K`, one label `σ i` is chosen over each corner of
the shadow (`ys n (σ i) → x i`), the corners `x` form a strictly convex counterclockwise
polygon with distinct depths and no horizontal double normal, and every other vertex lies
inside, over an open side (`M`, a chord middle, `δ ≠ 0`) or over a corner (`D`, a double,
`h ≠ 0`).  Then `K` is Rupert.  Nothing is assumed of `K` beyond this: neither (G1) for `K`
nor the hypotheses of the tier that certified the `K_n`. -/
theorem isRupert_of_limitCertificate (V M D : Finset ℝ³) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : R ∈ SO3) {u₀ : ℝ³} {r : ℝ} (hr : 0 < r) (hRu : R.toEuclideanLin u₀ = r • ez)
    {k k' : ℕ} [NeZero k] [NeZero k'] (x : ZMod k' → ℝ³) (hxV : ∀ i, x i ∈ V)
    (hxM : ∀ i, x i ∉ M)
    (hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))))
    (hin : ∀ v ∈ V, v ∉ M → v ∉ D → (∀ i, v ≠ x i) → proj_xy (R.toEuclideanLin v) ∈
      interior (convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (x i)))))
    (hdist : Function.Injective fun i => (R.toEuclideanLin (x i)) 2)
    (hnd : ¬ HasHorizontalDoubleNormal (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2))
    (hM : ∀ m ∈ M, ∃ i : ZMod k', ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = x i + s • (x (i + 1) - x i) + δ • u₀)
    (hD : ∀ y ∈ D, ∃ i : ZMod k', ∃ h : ℝ, h ≠ 0 ∧ y = x i - h • u₀)
    {ι : Type*} {l : Filter ι} (Rs : ι → Matrix (Fin 3) (Fin 3) ℝ) (ys : ι → ZMod k → ℝ³)
    (σ : ZMod k' → ZMod k) (hRs : Tendsto Rs l (𝓝 R))
    (hys : ∀ i, Tendsto (fun n => ys n (σ i)) l (𝓝 (x i)))
    (hcert : ∃ᶠ n in l, IsCcwPolygon (fun i => proj_xy ((Rs n).toEuclideanLin (ys n i))) ∧
      IsRobustUnimodal (fun i => ((Rs n).toEuclideanLin (ys n i)) 2)) : IsRupert V :=
  isRupert_of_uniform_doubles_robustUnimodal V M D R hR hr hRu x hxV hxM hp hin
    (isRobustUnimodal_cornerRim_of_tendsto σ (fun i => tendsto_proj_rot hRs (hys i))
      (fun i => tendsto_depth_rot hRs (hys i)) hcert hp hdist) hnd hM hD

/-- **The limit lemma with one tie** (Corollary 18.5 for a single test): as
`isRupert_of_limitCertificate`, but the corner depths at `K` have exactly one tied pair `i, j`,
and certified shapes approach `K` from both sides of the tie. -/
theorem isRupert_of_limitCertificate_tie (V M D : Finset ℝ³) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : R ∈ SO3) {u₀ : ℝ³} {r : ℝ} (hr : 0 < r) (hRu : R.toEuclideanLin u₀ = r • ez)
    {k k' : ℕ} [NeZero k] [NeZero k'] (x : ZMod k' → ℝ³) (hxV : ∀ i, x i ∈ V)
    (hxM : ∀ i, x i ∉ M)
    (hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))))
    (hin : ∀ v ∈ V, v ∉ M → v ∉ D → (∀ i, v ≠ x i) → proj_xy (R.toEuclideanLin v) ∈
      interior (convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (x i)))))
    {i j : ZMod k'}
    (hone : ∀ a b, a ≠ b → (R.toEuclideanLin (x a)) 2 = (R.toEuclideanLin (x b)) 2 →
      (a = i ∧ b = j) ∨ (a = j ∧ b = i))
    (hnd : ¬ HasHorizontalDoubleNormal (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2))
    (hM : ∀ m ∈ M, ∃ i : ZMod k', ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = x i + s • (x (i + 1) - x i) + δ • u₀)
    (hD : ∀ y ∈ D, ∃ i : ZMod k', ∃ h : ℝ, h ≠ 0 ∧ y = x i - h • u₀)
    {ι κ : Type*} {l : Filter ι} {l' : Filter κ} (Rs : ι → Matrix (Fin 3) (Fin 3) ℝ)
    (ys : ι → ZMod k → ℝ³) (Rs' : κ → Matrix (Fin 3) (Fin 3) ℝ) (ys' : κ → ZMod k → ℝ³)
    (σ : ZMod k' → ZMod k) (hRs : Tendsto Rs l (𝓝 R)) (hRs' : Tendsto Rs' l' (𝓝 R))
    (hys : ∀ i, Tendsto (fun n => ys n (σ i)) l (𝓝 (x i)))
    (hys' : ∀ i, Tendsto (fun n => ys' n (σ i)) l' (𝓝 (x i)))
    (hcert : ∃ᶠ n in l, IsCcwPolygon (fun i => proj_xy ((Rs n).toEuclideanLin (ys n i))) ∧
      IsRobustUnimodal (fun i => ((Rs n).toEuclideanLin (ys n i)) 2) ∧
      ((Rs n).toEuclideanLin (ys n (σ j))) 2 < ((Rs n).toEuclideanLin (ys n (σ i))) 2)
    (hcert' : ∃ᶠ n in l', IsCcwPolygon (fun i => proj_xy ((Rs' n).toEuclideanLin (ys' n i))) ∧
      IsRobustUnimodal (fun i => ((Rs' n).toEuclideanLin (ys' n i)) 2) ∧
      ((Rs' n).toEuclideanLin (ys' n (σ i))) 2 < ((Rs' n).toEuclideanLin (ys' n (σ j))) 2) :
    IsRupert V :=
  isRupert_of_uniform_doubles_robustUnimodal V M D R hR hr hRu x hxV hxM hp hin
    (isRobustUnimodal_cornerRim_of_tendsto_single_tie σ
      (fun i => tendsto_proj_rot hRs (hys i)) (fun i => tendsto_depth_rot hRs (hys i))
      (fun i => tendsto_depth_rot hRs' (hys' i)) hcert (hcert'.mono fun _ h => h.2) hp hone)
    hnd hM hD

end Minimality

end
