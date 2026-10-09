module

public import SmallRupert.SixVertices
public import Mathlib.Analysis.Convex.Caratheodory

@[expose] public section

/-!
# L7: unimodal silhouettes

LEMMAS.md L7, in the standard view (`proj_xy`, depth = coordinate 2).

* `exists_forces_of_not_firstOrderInward` (Lemma 7.1, the direction used):
  if no first-order motion is strictly inward, there are horizontal *corner
  forces* `f v` in the normal cones of the shadow at the points of `V`, not all
  zero, with zero sum (E1), zero depth moment (E2) and zero torque (E3).  It is
  stated with normal cones (`normalConeAt`), so it needs neither (G1) nor
  edge normals.
* `hasHorizontalDoubleNormal_of_forces` (Theorem 7.3 (⇒), pure polygon form):
  forces in the normal cones of a strictly convex counterclockwise polygon,
  balanced as in (E1)–(E3), with cyclically unimodal distinct depths, force a
  horizontal double normal of the silhouette cycle.
* `exists_firstOrderInward_of_unimodal`, `isRupert_of_unimodalView` (Theorem
  7.3 at an explicit view): a generic unimodal silhouette without horizontal
  double normal gives a passage.
* `exists_badPlanes` (Lemma 7.4) and `isRupert_of_genericUnimodalView`
  (Theorem 7.5): a generic unimodal view suffices.
* `isRupert_translationPrism` (Theorem 7.7) and
  `isRupert_octahedron_conditionA` (Corollary 7.8).

The silhouette at an explicit view is given by a cyclic list of points
`x : ZMod k → ℝ³` of `V`: (G1) is `IsCcwPolygon (proj_xy ∘ x)` (strictly convex,
counterclockwise) together with "every other point of `V` projects into the
interior", and (G2) is injectivity of the depths, part of `IsCyclicUnimodal`.
-/

namespace SmallRupert

open scoped RealInnerProductSpace

/-- The normal cone of `S` at `p`. -/
def normalConeAt (S : Set ℝ²) (p : ℝ²) : Set ℝ² := {n | ∀ q ∈ S, ⟪n, q - p⟫ ≤ 0}

/-- The 2D cross product `a × b = a₀ b₁ - a₁ b₀`. -/
def cross2 (a b : ℝ²) : ℝ := a 0 * b 1 - a 1 * b 0

/-- The convex hull of a compact set in a finite-dimensional normed space is
compact (Carathéodory). -/
theorem isCompact_convexHull_of_isCompact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {A : Set E} (hA : IsCompact A) : IsCompact (convexHull ℝ A) := by
  classical
  set n := Module.finrank ℝ E + 1
  let Φ : (Fin n → ℝ) × (Fin n → E) → E := fun wz => ∑ j, wz.1 j • wz.2 j
  have hΦ : Continuous Φ := by fun_prop
  have hD : IsCompact (stdSimplex ℝ (Fin n) ×ˢ Set.univ.pi (fun _ : Fin n => A)) :=
    IsCompact.prod (isCompact_stdSimplex ℝ (Fin n)) (isCompact_univ_pi fun _ => hA)
  suffices h : convexHull ℝ A = Φ '' (stdSimplex ℝ (Fin n) ×ˢ Set.univ.pi (fun _ => A)) by
    rw [h]; exact hD.image hΦ
  apply le_antisymm
  · intro x hx
    obtain ⟨ι, _, z, w, hzA, hind, hw0, hw1, hx⟩ := eq_pos_convex_span_of_mem_convexHull hx
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
      (show Fintype.card ι ≤ Fintype.card (Fin n) by
        rw [Fintype.card_fin]
        exact hind.card_le_finrank_succ.trans
          (Nat.add_le_add_right (Submodule.finrank_le _) 1))
    have hne : Nonempty ι := by
      by_contra h; rw [not_nonempty_iff] at h; simp at hw1
    obtain ⟨i₀⟩ := hne
    let w' : Fin n → ℝ := fun j => ∑ i ∈ Finset.univ.filter (fun i => e i = j), w i
    let z' : Fin n → E := fun j => if h : ∃ i, e i = j then z h.choose else z i₀
    have hz' : ∀ i, z' (e i) = z i := fun i => by
      have h : ∃ i', e i' = e i := ⟨i, rfl⟩
      simp only [z', dif_pos h]
      rw [e.injective h.choose_spec]
    refine ⟨(w', z'), ⟨⟨fun j => Finset.sum_nonneg fun i _ => (hw0 i).le, ?_⟩, fun j _ => ?_⟩, ?_⟩
    · rw [← hw1]; exact Finset.sum_fiberwise_of_maps_to (fun i _ => Finset.mem_univ (e i)) w
    · simp only [z']
      split_ifs with h
      · exact hzA ⟨_, rfl⟩
      · exact hzA ⟨_, rfl⟩
    · simp only [Φ, w', Finset.sum_smul]
      rw [← hx, ← Finset.sum_fiberwise_of_maps_to (g := e) (fun i _ => Finset.mem_univ (e i))]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i hi => ?_
      rw [← (Finset.mem_filter.mp hi).2, hz']
  · rintro _ ⟨⟨w, z⟩, ⟨⟨hw0, hw1⟩, hz⟩, rfl⟩
    exact (convex_convexHull ℝ A).sum_mem (fun j _ => hw0 j) hw1
      (fun j _ => subset_convexHull ℝ A (hz j (Set.mem_univ j)))

/-- The horizontal lift `n ↦ (n, 0)`. -/
noncomputable def liftH (n : ℝ²) : ℝ³ := !₂[n 0, n 1, 0]

theorem inner_screenVel (ω τ v : ℝ³) (n : ℝ²) :
    ⟪n, screenVel ω τ v⟫ = ⟪ω, cross v (liftH n)⟫ + ⟪τ, liftH n⟫ := by
  simp [screenVel, proj_xy, crossMatrix, cross, liftH, Matrix.toLpLin_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_three, PiLp.inner_apply, Fin.sum_univ_two]
  ring

theorem normalConeAt_isClosed (S : Set ℝ²) (p : ℝ²) : IsClosed (normalConeAt S p) := by
  have : normalConeAt S p = ⋂ q ∈ S, {n | ⟪n, q - p⟫ ≤ 0} := by ext; simp [normalConeAt]
  rw [this]
  exact isClosed_biInter fun q _ => isClosed_le (continuous_id.inner continuous_const)
    continuous_const

/-- **Lemma 7.1 (corner forces), the direction used.**  If no first-order
motion is strictly inward, there are forces `f v ∈ N_S(P v)` (`v ∈ V`), not all
zero, with `Σ f = 0`, `Σ z f = 0`, `Σ P v × f = 0`.  (Points projecting into
the interior of the shadow get `f v = 0`, their normal cone being `{0}`.) -/
theorem exists_forces_of_not_firstOrderInward (V : Finset ℝ³)
    (hint : (interior (proj_xy '' convexHull ℝ (V : Set ℝ³))).Nonempty)
    (h : ∀ ω τ : ℝ³, ¬ FirstOrderInward V ω τ) :
    ∃ f : ℝ³ → ℝ², (∀ v ∈ V, f v ∈ normalConeAt (proj_xy '' convexHull ℝ (V : Set ℝ³))
        (proj_xy v)) ∧ (∃ v ∈ V, f v ≠ 0) ∧ ∑ v ∈ V, f v = 0 ∧ ∑ v ∈ V, v 2 • f v = 0 ∧
      ∑ v ∈ V, cross2 (proj_xy v) (f v) = 0 := by
  classical
  set S := proj_xy '' convexHull ℝ (V : Set ℝ³) with hSdef
  have hS : Convex ℝ S := by
    rw [hSdef, show (proj_xy : ℝ³ → ℝ²) = projL from rfl]
    exact (convex_convexHull ℝ _).linear_image projL
  obtain ⟨c, hc⟩ := hint
  have hPv : ∀ v ∈ V, proj_xy v ∈ S := fun v hv => ⟨v, subset_convexHull ℝ _ hv, rfl⟩
  -- unit normals are strictly negative on the direction to the interior point `c`
  have hneg : ∀ v ∈ V, ∀ n ∈ normalConeAt S (proj_xy v), n ≠ 0 → ⟪n, c - proj_xy v⟫ < 0 := by
    intro v hv n hn hn0
    have hin : IsInwardAt S (proj_xy v) (c - proj_xy v) :=
      ⟨1, one_pos, by rw [one_smul, add_sub_cancel]; exact hc⟩
    exact hin.inner_neg hn0 hn
  let K : ℝ³ → Set ℝ² := fun v => normalConeAt S (proj_xy v) ∩ Metric.sphere 0 1
  have hK : ∀ v, IsCompact (K v) := fun v =>
    (isCompact_sphere (0 : ℝ²) 1).inter_left (normalConeAt_isClosed _ _)
  let a : ℝ³ → ℝ² → ℝ³ × ℝ³ := fun v n => (cross v (liftH n), liftH n)
  have ha : ∀ v, Continuous (a v) := fun v => by
    simp only [a, cross, liftH]; fun_prop
  set A := ⋃ v ∈ V, a v '' K v with hAdef
  have hA : IsCompact A := V.isCompact_biUnion fun v _ => (hK v).image (ha v)
  have hC := isCompact_convexHull_of_isCompact hA
  by_cases h0 : (0 : ℝ³ × ℝ³) ∈ convexHull ℝ A
  · rw [convexHull_eq] at h0
    obtain ⟨ι, t, w, z, hw0, hw1, hzA, hsum⟩ := h0
    rw [Finset.centerMass_eq_of_sum_1 _ _ hw1] at hsum
    have hz' : ∀ i ∈ t, ∃ v ∈ V, ∃ n ∈ K v, a v n = z i := by
      intro i hi
      have := hzA i hi
      simp only [hAdef, Set.mem_iUnion, Set.mem_image] at this
      obtain ⟨v, hv, n, hn, h⟩ := this
      exact ⟨v, hv, n, hn, h⟩
    choose! vv hvV nn hnK hza using hz'
    have hsum' : ∑ i ∈ t, w i • a (vv i) (nn i) = 0 := by
      rw [← hsum]; exact Finset.sum_congr rfl fun i hi => by rw [hza i hi]
    have hfst := congrArg Prod.fst hsum'
    have hsnd := congrArg Prod.snd hsum'
    simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, Prod.fst_zero,
      Prod.snd_zero, a] at hfst hsnd
    let f : ℝ³ → ℝ² := fun v => ∑ i ∈ t.filter (fun i => vv i = v), w i • nn i
    have hmaps : ∀ i ∈ t, vv i ∈ V := fun i hi => hvV i hi
    have hn0 : ∀ i ∈ t, nn i ≠ 0 := fun i hi h0 => by
      have := (hnK i hi).2; simp [h0] at this
    refine ⟨f, fun v hv q hq => ?_, ?_, ?_, ?_, ?_⟩
    · simp only [f, sum_inner, real_inner_smul_left]
      refine Finset.sum_nonpos fun i hi => ?_
      obtain ⟨hit, hiv⟩ := Finset.mem_filter.mp hi
      have := (hnK i hit).1 q hq
      rw [hiv] at this
      exact mul_nonpos_of_nonneg_of_nonpos (hw0 i hit) this
    · obtain ⟨i, hit, hwi⟩ : ∃ i ∈ t, 0 < w i := by
        by_contra hcon; push Not at hcon
        have : ∑ i ∈ t, w i ≤ 0 := Finset.sum_nonpos hcon
        linarith
      refine ⟨vv i, hvV i hit, fun h => ?_⟩
      have hlt : ⟪f (vv i), c - proj_xy (vv i)⟫ < 0 := by
        simp only [f, sum_inner, real_inner_smul_left]
        have hi' : i ∈ t.filter (fun j => vv j = vv i) := Finset.mem_filter.mpr ⟨hit, rfl⟩
        rw [← Finset.add_sum_erase _ _ hi']
        have hstrict : w i * ⟪nn i, c - proj_xy (vv i)⟫ < 0 :=
          mul_neg_of_pos_of_neg hwi (hneg (vv i) (hvV i hit) (nn i) (hnK i hit).1 (hn0 i hit))
        have hrest : ∑ j ∈ (t.filter (fun j => vv j = vv i)).erase i,
            w j * ⟪nn j, c - proj_xy (vv i)⟫ ≤ 0 := by
          refine Finset.sum_nonpos fun j hj => ?_
          obtain ⟨hjt, hjv⟩ := Finset.mem_filter.mp (Finset.mem_of_mem_erase hj)
          have := hneg (vv j) (hvV j hjt) (nn j) (hnK j hjt).1 (hn0 j hjt)
          rw [hjv] at this
          exact mul_nonpos_of_nonneg_of_nonpos (hw0 j hjt) this.le
        linarith
      rw [h, inner_zero_left] at hlt
      exact lt_irrefl _ hlt
    · rw [show ∑ v ∈ V, f v = ∑ i ∈ t, w i • nn i from
        Finset.sum_fiberwise_of_maps_to hmaps _]
      ext j; fin_cases j
      · have := congrArg (fun x : ℝ³ => x 0) hsnd
        simpa [liftH] using this
      · have := congrArg (fun x : ℝ³ => x 1) hsnd
        simpa [liftH] using this
    · have hE2 : ∑ v ∈ V, v 2 • f v = ∑ i ∈ t, (vv i 2 * w i) • nn i := by
        rw [← Finset.sum_fiberwise_of_maps_to hmaps]
        refine Finset.sum_congr rfl fun v _ => ?_
        simp only [f, Finset.smul_sum, smul_smul]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [(Finset.mem_filter.mp hi).2, mul_comm]
      rw [hE2]
      ext j; fin_cases j
      · have := congrArg (fun x : ℝ³ => x 1) hfst
        simp [cross, liftH] at this
        simp
        exact (Finset.sum_congr rfl fun i _ => by ring).trans this
      · have := congrArg (fun x : ℝ³ => x 0) hfst
        simp [cross, liftH] at this
        simp
        exact (Finset.sum_congr rfl fun i _ => by ring).trans this
    · have hE3 : ∑ v ∈ V, cross2 (proj_xy v) (f v) =
          ∑ i ∈ t, w i * (vv i 0 * nn i 1 - vv i 1 * nn i 0) := by
        rw [← Finset.sum_fiberwise_of_maps_to hmaps]
        refine Finset.sum_congr rfl fun v _ => ?_
        simp only [f, cross2, proj_xy]
        simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,
          Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [(Finset.mem_filter.mp hi).2]
        simp
        ring
      rw [hE3]
      have := congrArg (fun x : ℝ³ => x 2) hfst
      simp [cross, liftH] at this
      linear_combination this
  · -- separate `0` from the compact convex hull
    exfalso
    obtain ⟨φ, u, u', hφ, huu', hφ0⟩ := geometric_hahn_banach_compact_closed
      (convex_convexHull ℝ A) hC (convex_singleton 0) isClosed_singleton
      (Set.disjoint_singleton_right.mpr h0)
    have hφneg : ∀ x ∈ A, φ x < 0 := fun x hx => by
      have h1 := hφ x (subset_convexHull ℝ A hx)
      have h2 := hφ0 0 rfl
      rw [map_zero] at h2
      linarith
    set ω := (InnerProductSpace.toDual ℝ ℝ³).symm (φ.comp (ContinuousLinearMap.inl ℝ ℝ³ ℝ³))
    set τ := (InnerProductSpace.toDual ℝ ℝ³).symm (φ.comp (ContinuousLinearMap.inr ℝ ℝ³ ℝ³))
    have hφa : ∀ v n, φ (a v n) = ⟪n, screenVel ω τ v⟫ := by
      intro v n
      rw [inner_screenVel, InnerProductSpace.toDual_symm_apply,
        InnerProductSpace.toDual_symm_apply]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
        ContinuousLinearMap.inr_apply, a]
      rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
    apply h ω τ
    intro v hv
    refine isInwardAt_of_forall_normal hS ⟨c, hc⟩ (subset_closure (hPv v hv)) _
      (fun n hn0 hn => ?_)
    have hnpos : 0 < ‖n‖ := norm_pos_iff.mpr hn0
    have hmem : (1 / ‖n‖) • n ∈ K v := by
      refine ⟨fun q hq => ?_, by simp [norm_smul, hnpos.ne']⟩
      rw [real_inner_smul_left]
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (hn q hq)
    have := hφneg _ (Set.mem_biUnion hv ⟨_, hmem, rfl⟩)
    rw [hφa, real_inner_smul_left] at this
    by_contra hcon; push Not at hcon
    have := mul_nonneg (show 0 ≤ 1 / ‖n‖ by positivity) hcon
    linarith

/-- `p` lists the corners of a strictly convex polygon counterclockwise: every
corner lies strictly to the left of every directed edge not containing it. -/
def IsCcwPolygon {k : ℕ} (p : ZMod k → ℝ²) : Prop :=
  3 ≤ k ∧ ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 → 0 < cross2 (p (i + 1) - p i) (p j - p i)

/-- A cyclic sequence of distinct reals with exactly one local maximum (hence
exactly one local minimum). -/
def IsCyclicUnimodal {k : ℕ} [NeZero k] (z : ZMod k → ℝ) : Prop :=
  Function.Injective z ∧
    (Finset.univ.filter (fun i : ZMod k => z (i - 1) < z i ∧ z (i + 1) < z i)).card = 1

/-- The corner `(p i, z i)` of the silhouette cycle in `ℝ³`. -/
noncomputable def liftPt (q : ℝ²) (t : ℝ) : ℝ³ := !₂[q 0, q 1, t]

/-- The silhouette cycle `C = x₀x₁⋯x_{k-1}x₀` has a *horizontal double normal*:
two points of `C` at the same depth whose projections span a double normal of
the shadow `conv p`. -/
def HasHorizontalDoubleNormal {k : ℕ} (p : ZMod k → ℝ²) (z : ZMod k → ℝ) : Prop :=
  ∃ y y' : ℝ³, (∃ i, y ∈ segment ℝ (liftPt (p i) (z i)) (liftPt (p (i + 1)) (z (i + 1)))) ∧
    (∃ j, y' ∈ segment ℝ (liftPt (p j) (z j)) (liftPt (p (j + 1)) (z (j + 1)))) ∧
    y 2 = y' 2 ∧ proj_xy y ≠ proj_xy y' ∧
    proj_xy y' - proj_xy y ∈ normalConeAt (convexHull ℝ (Set.range p)) (proj_xy y') ∧
    proj_xy y - proj_xy y' ∈ normalConeAt (convexHull ℝ (Set.range p)) (proj_xy y)

/-- **Theorem 7.3 (⇒), polygon form.**  Forces in the normal cones of a
strictly convex counterclockwise polygon, not all zero, with zero sum, zero
depth moment and zero torque, at cyclically unimodal distinct depths, force a
horizontal double normal. -/
theorem hasHorizontalDoubleNormal_of_forces {k : ℕ} [NeZero k] (p : ZMod k → ℝ²)
    (z : ZMod k → ℝ) (hp : IsCcwPolygon p) (hz : IsCyclicUnimodal z) (f : ZMod k → ℝ²)
    (hf : ∀ i, f i ∈ normalConeAt (convexHull ℝ (Set.range p)) (p i)) (hne : ∃ i, f i ≠ 0)
    (h1 : ∑ i, f i = 0) (h2 : ∑ i, z i • f i = 0) (h3 : ∑ i, cross2 (p i) (f i) = 0) :
    HasHorizontalDoubleNormal p z := by
  sorry

/-- **Theorem 7.3 at an explicit standard view.**  The silhouette is the cycle
`x`, every other point of `V` projects into the interior of the shadow, the
corner depths are cyclically unimodal and distinct, and there is no horizontal
double normal.  Then some first-order motion is strictly inward. -/
theorem exists_firstOrderInward_of_unimodal (V : Finset ℝ³) {k : ℕ} [NeZero k]
    (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V) (hp : IsCcwPolygon (fun i => proj_xy (x i)))
    (hin : ∀ v ∈ V, (∀ i, v ≠ x i) →
      proj_xy v ∈ interior (convexHull ℝ (Set.range fun i => proj_xy (x i))))
    (hz : IsCyclicUnimodal (fun i => x i 2))
    (hnd : ¬ HasHorizontalDoubleNormal (fun i => proj_xy (x i)) (fun i => x i 2)) :
    ∃ ω τ : ℝ³, FirstOrderInward V ω τ := by
  sorry

/-- **Theorem 7.3, Rupert form, at the view of a rotation `R`.** -/
theorem isRupert_of_unimodalView (V : Finset ℝ³) (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : R ∈ SO3)
    {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V)
    (hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))))
    (hin : ∀ v ∈ V, (∀ i, v ≠ x i) → proj_xy (R.toEuclideanLin v) ∈
      interior (convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (x i)))))
    (hz : IsCyclicUnimodal (fun i => (R.toEuclideanLin (x i)) 2))
    (hnd : ¬ HasHorizontalDoubleNormal (fun i => proj_xy (R.toEuclideanLin (x i)))
      (fun i => (R.toEuclideanLin (x i)) 2)) :
    IsRupert V := by
  sorry

/-- **Lemma 7.4 (exceptional views).**  Horizontal double normals at generic
views occur only for views `u = Rᵀ e_z` on finitely many great circles
`l ⟂ u`, determined by `V` alone (cases (a)–(e) of LEMMAS.md). -/
theorem exists_badPlanes (V : Finset ℝ³) :
    ∃ Λ : Finset ℝ³, (∀ l ∈ Λ, l ≠ 0) ∧
      ∀ R ∈ SO3, ∀ (k : ℕ) [NeZero k] (x : ZMod k → ℝ³), (∀ i, x i ∈ V) →
        IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))) →
        IsCyclicUnimodal (fun i => (R.toEuclideanLin (x i)) 2) →
        HasHorizontalDoubleNormal (fun i => proj_xy (R.toEuclideanLin (x i)))
          (fun i => (R.toEuclideanLin (x i)) 2) →
        ∃ l ∈ Λ, (R.toEuclideanLin l) 2 = 0 := by
  sorry

/-- **Theorem 7.5 (unimodal view criterion).**  A generic view (strictly
convex silhouette `x`, all other points inside, distinct corner depths) with a
unimodal silhouette makes `V` Rupert. -/
theorem isRupert_of_genericUnimodalView (V : Finset ℝ³) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : R ∈ SO3) {k : ℕ} [NeZero k] (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V)
    (hp : IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x i))))
    (hin : ∀ v ∈ V, (∀ i, v ≠ x i) → proj_xy (R.toEuclideanLin v) ∈
      interior (convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (x i)))))
    (hz : IsCyclicUnimodal (fun i => (R.toEuclideanLin (x i)) 2)) :
    IsRupert V := by
  sorry

/-- **Theorem 7.7 (translation prisms).**  `K = T + [0, w]` for a triangle
`T = ABC` and `w` not parallel to its plane.  If `w` is not perpendicular to
the plane of `T`, or `T` has an obtuse angle, `K` is Rupert.  (Right prisms over
non-obtuse triangles remain open.) -/
theorem isRupert_translationPrism (A B C w : ℝ³) (hind : AffineIndependent ℝ ![A, B, C, A + w])
    (h : ⟪w, B - A⟫ ≠ 0 ∨ ⟪w, C - A⟫ ≠ 0 ∨ ⟪B - A, C - A⟫ < 0 ∨ ⟪A - B, C - B⟫ < 0 ∨
      ⟪A - C, B - C⟫ < 0) :
    IsRupert {A, B, C, A + w, B + w, C + w} := by
  sorry

/-- An octahedron with opposite vertex pairs `(a, a')`, `(b, b')`, `(c, c')`:
the eight triangles with one vertex from each pair are facets. -/
structure IsOctahedron (a a' b b' c c' : ℝ³) : Prop where
  nodup : [a, a', b, b', c, c'].Nodup
  facet_abc : IsFacetTriangle {a, a', b, b', c, c'} a b c
  facet_abc' : IsFacetTriangle {a, a', b, b', c, c'} a b c'
  facet_ab'c : IsFacetTriangle {a, a', b, b', c, c'} a b' c
  facet_ab'c' : IsFacetTriangle {a, a', b, b', c, c'} a b' c'
  facet_a'bc : IsFacetTriangle {a, a', b, b', c, c'} a' b c
  facet_a'bc' : IsFacetTriangle {a, a', b, b', c, c'} a' b c'
  facet_a'b'c : IsFacetTriangle {a, a', b, b', c, c'} a' b' c
  facet_a'b'c' : IsFacetTriangle {a, a', b, b', c, c'} a' b' c'

/-- **Corollary 7.8 (Condition A).**  With `d = a - a'`, if the projections of
the diagonals `bb'` and `cc'` onto the axis `aa'` overlap in more than a point,
the octahedron is Rupert. -/
theorem isRupert_octahedron_conditionA {a a' b b' c c' : ℝ³} (h : IsOctahedron a a' b b' c c')
    (hA : max (min ⟪a - a', b⟫ ⟪a - a', b'⟫) (min ⟪a - a', c⟫ ⟪a - a', c'⟫) <
      min (max ⟪a - a', b⟫ ⟪a - a', b'⟫) (max ⟪a - a', c⟫ ⟪a - a', c'⟫)) :
    IsRupert {a, a', b, b', c, c'} := by
  sorry

end SmallRupert

end
