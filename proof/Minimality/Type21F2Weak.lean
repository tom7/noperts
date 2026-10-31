module

public import Minimality.Type21F2
public import Minimality.OctAxis
public import Minimality.Type16Rims
public import Minimality.Type16Limit
public import Minimality.Generic.TwoTie

@[expose] public section

/-!
# Type 21: F2 with a tie at both views, the tied pairs independent

The named vertex views `vtx21`, `vtxView21`, `view21` (with their covariance, continuity) and the
weak variant `cert_type21_F2_weak` of `cert_type21_F2`: `F2Tie` is replaced by `OneTieAt` at both
views and independence of the two tied pairs (`TieIndep`).  Equivariance of the F2 certificate
(`b5b_core`, `b5b_MF`), the rim robustness (`b5b_F2_robust`), and the identification of the
axis views with the named views (`b5b_par1`, `b5b_par4`).
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Filter Noperts

/-! ### Linear maps (moved from `Type16Metric`) -/

/-- The determinant of a linear map of `ℝ³`, as the triple product of the images of the
standard basis. -/
noncomputable def detMap (M : ℝ³ →L[ℝ] ℝ³) : ℝ :=
  det3 (M (EuclideanSpace.single 0 1)) (M (EuclideanSpace.single 1 1))
    (M (EuclideanSpace.single 2 1))

theorem map_coord (M : ℝ³ →L[ℝ] ℝ³) (a : ℝ³) (j : Fin 3) :
    (M a) j = a 0 * (M (EuclideanSpace.single 0 1)) j + a 1 * (M (EuclideanSpace.single 1 1)) j +
      a 2 * (M (EuclideanSpace.single 2 1)) j := by
  have ha : a = a 0 • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) +
      a 1 • EuclideanSpace.single (1 : Fin 3) (1 : ℝ) +
      a 2 • EuclideanSpace.single (2 : Fin 3) (1 : ℝ) := by
    ext i; fin_cases i <;> simp
  conv_lhs => rw [ha]
  simp only [map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]

theorem det3_map (M : ℝ³ →L[ℝ] ℝ³) (a b c : ℝ³) :
    det3 (M a) (M b) (M c) = detMap M * det3 a b c := by
  simp only [detMap, det3_expand, map_coord M a, map_coord M b, map_coord M c]
  ring

theorem planeLine_map (M : ℝ³ →L[ℝ] ℝ³) (p₀ p₁ p₂ q₀ q₁ q₂ : ℝ³) :
    planeLine (M p₀) (M p₁) (M p₂) (M q₀) (M q₁) (M q₂) =
      detMap M • M (planeLine p₀ p₁ p₂ q₀ q₁ q₂) := by
  rw [planeLine, planeLine, ← map_sub M p₁ p₀, ← map_sub M p₂ p₀, ← map_sub M q₂ q₀,
    ← map_sub M q₁ q₀, det3_map, det3_map]
  simp only [map_sub, map_smul, smul_sub, smul_smul]

theorem robust_mul_ne_zero {k : ℕ} {z : ZMod k → ℝ} (hz : IsRobustUnimodal z) {c : ℝ}
    (hc : c ≠ 0) : IsRobustUnimodal (fun i => c * z i) := by
  rcases lt_or_gt_of_ne hc with h | h
  · have := (hz.smul (neg_pos.mpr h)).neg
    convert this using 2 with i
    ring
  · exact hz.smul h

/-! ### The named views (moved from `Type21Limit`, `Type21Metric`, `Type21Ties`) -/

/-- **The eight vertex crossings** of the cover: the lines of the facet pairs `014/0256` (at
`0`), `014/2346` (at `4`), `135/0256` (at `5`), `135/2346` (at `3`), `046/134` (at `4`),
`046/015` (at `0`), `235/134` (at `3`), `235/015` (at `5`), each facet by three of its labels,
the common vertex first (as in the vertex tests of F2, `F2ViewsL`). -/
def vtx21 : Fin 8 → (Fin 7 × Fin 7 × Fin 7) × (Fin 7 × Fin 7 × Fin 7) :=
  ![((0, 4, 1), (0, 5, 6)), ((4, 0, 1), (4, 3, 6)), ((5, 3, 1), (5, 0, 2)),
    ((3, 5, 1), (3, 4, 2)), ((4, 0, 6), (4, 3, 1)), ((0, 4, 6), (0, 5, 1)),
    ((3, 5, 2), (3, 4, 1)), ((5, 3, 2), (5, 0, 1))]

/-- The view along the `t`-th vertex crossing. -/
noncomputable def vtxView21 (x : Fin 7 → ℝ³) (t : Fin 8) : ℝ³ :=
  planeLine (x (vtx21 t).1.1) (x (vtx21 t).1.2.1) (x (vtx21 t).1.2.2) (x (vtx21 t).2.1)
    (x (vtx21 t).2.2.1) (x (vtx21 t).2.2.2)

/-- **The named views of type 21**: the segments and the eight vertex crossings. -/
noncomputable def view21 (x : Fin 7 → ℝ³) : (Fin 7 × Fin 7) ⊕ Fin 8 → ℝ³
  | .inl ij => x ij.2 - x ij.1
  | .inr t => vtxView21 x t

theorem tendsto_view21 {ι : Type*} {l : Filter ι} {K : ι → Fin 7 → ℝ³} {x : Fin 7 → ℝ³}
    (hK : ∀ m, Tendsto (fun n => K n m) l (𝓝 (x m))) (v : (Fin 7 × Fin 7) ⊕ Fin 8) :
    Tendsto (fun n => view21 (K n) v) l (𝓝 (view21 x v)) := by
  rcases v with ⟨i, j⟩ | t
  · exact (hK j).sub (hK i)
  · exact tendsto_planeLine (hK _) (hK _) (hK _) (hK _) (hK _) (hK _)

theorem view21_map (M : ℝ³ →L[ℝ] ℝ³) (y : Fin 7 → ℝ³) (v : (Fin 7 × Fin 7) ⊕ Fin 8) :
    ∃ c : ℝ, (c = 1 ∨ c = detMap M) ∧ view21 (fun l => M (y l)) v = c • M (view21 y v) := by
  rcases v with ⟨i, j⟩ | t
  · exact ⟨1, Or.inl rfl, by rw [one_smul]; simp [view21]⟩
  · exact ⟨detMap M, Or.inr rfl, planeLine_map M _ _ _ _ _ _⟩

theorem detMap_eq21 (L : ℝ³ →L[ℝ] ℝ³) : detMap L = LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis, Matrix.det_fin_three]
  simp only [detMap, det3_expand, LinearMap.toMatrix_apply]
  simp [EuclideanSpace.basisFun_apply]
  ring

/-- The named views are covariant. -/
theorem covView_view21 (v : (Fin 7 × Fin 7) ⊕ Fin 8) :
    CovView (fun y : Fin 7 → ℝ³ => view21 y v) := by
  refine ⟨?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun y => ?_
    exact tendsto_view21 (fun m => (continuous_apply m).tendsto y) v
  · intro L y hL
    have hd : detMap L = 1 := by rw [detMap_eq21]; exact hL
    obtain ⟨c, hc, e⟩ := view21_map L y v
    show view21 (fun l => L (y l)) v = L (view21 y v)
    rw [e]
    rcases hc with rfl | rfl
    · rw [one_smul]
    · rw [hd, one_smul]


/-- coordinates of `L u` -/
theorem b5b_apply (L : ℝ³ →L[ℝ] ℝ³) (u : ℝ³) (i : Fin 3) :
    L u i = ∑ j : Fin 3, (L (EuclideanSpace.single j 1)) i * u j := by
  conv_lhs => rw [show u = ∑ j : Fin 3, u j • (EuclideanSpace.single j (1:ℝ) : ℝ³) by
    ext k; simp [Fin.sum_univ_three, Pi.single_apply]; fin_cases k <;> simp]
  simp [map_sum, Finset.sum_apply, mul_comm]

theorem b5b_det_eq (L : ℝ³ →L[ℝ] ℝ³) :
    LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) =
      (fun a : Fin 3 → Fin 3 → ℝ => a 0 0 * a 1 1 * a 2 2 - a 0 0 * a 1 2 * a 2 1 - a 0 1 * a 1 0 * a 2 2 +
        a 0 1 * a 1 2 * a 2 0 + a 0 2 * a 1 0 * a 2 1 - a 0 2 * a 1 1 * a 2 0)
        (fun i j => L (EuclideanSpace.single j 1) i) := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis, Matrix.det_fin_three]
  simp [LinearMap.toMatrix_apply]

/-- `det3` is multiplied by `det L`. -/
theorem b5b_det3_map (L : ℝ³ →L[ℝ] ℝ³) (u v w : ℝ³) :
    det3 (L u) (L v) (L w) = LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) * det3 u v w := by
  rw [b5b_det_eq]
  have hu := b5b_apply L u
  have hv := b5b_apply L v
  have hw := b5b_apply L w
  simp only [det3_expand, hu, hv, hw, Fin.sum_univ_three]
  ring

/-! ### Gale data and axis views are equivariant (transport by precomposition with `L⁻¹`) -/

/-- Precompose a functional with `L⁻¹`. -/
noncomputable def b5b_pre (L : ℝ³ →L[ℝ] ℝ³) (h : LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) ≠ 0)
    (l : ℝ³ → ℝ) : ℝ³ → ℝ := fun y => l ((LinearMap.equivOfDetNeZero _ h).symm y)

theorem b5b_pre_apply (L : ℝ³ →L[ℝ] ℝ³) (h : LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) ≠ 0)
    (l : ℝ³ → ℝ) (s : ℝ³) : b5b_pre L h l (L s) = l s := by
  have : (LinearMap.equivOfDetNeZero _ h).symm (L s) = s :=
    (LinearEquiv.symm_apply_eq _).2 rfl
  simp [b5b_pre, this]

theorem b5b_galeD_map {l m l' m' : ℝ³ → ℝ} (L : ℝ³ →L[ℝ] ℝ³) (hl : ∀ s, l' (L s) = l s)
    (hm : ∀ s, m' (L s) = m s) (s t : ℝ³) : galeD l' m' (L s) (L t) = galeD l m s t := by
  simp only [galeD, hl, hm]

/-- `axisView` is equivariant: the view of the mapped octahedron is the image of the view. -/
theorem b5b_axisView_map {l m l' m' : ℝ³ → ℝ} (L : ℝ³ →L[ℝ] ℝ³) (hl : ∀ s, l' (L s) = l s)
    (hm : ∀ s, m' (L s) = m s) (a a' b c : ℝ³) :
    axisView l' m' (L a) (L a') (L b) (L c) = L (axisView l m a a' b c) := by
  simp only [axisView, b5b_galeD_map L hl hm, map_add, map_smul, map_sub]

/-- Gale data transports to the mapped points. -/
noncomputable def b5b_gale {a a' b b' c c' : ℝ³} (G : GaleData a a' b b' c c') (L : ℝ³ →L[ℝ] ℝ³)
    (h : LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) ≠ 0) : GaleData (L a) (L a') (L b) (L b') (L c) (L c') where
  l := b5b_pre L h G.l
  m := b5b_pre L h G.m
  hl := ⟨by simp only [b5b_pre_apply]; exact G.hl.sum, by
    simp only [b5b_pre_apply, ← map_smul, ← map_add]; rw [G.hl.vsum, map_zero]⟩
  hm := ⟨by simp only [b5b_pre_apply]; exact G.hm.sum, by
    simp only [b5b_pre_apply, ← map_smul, ← map_add]; rw [G.hm.vsum, map_zero]⟩
  indep := by simp only [b5b_pre_apply]; exact G.indep

theorem b5b_segMeet_map {d₀ d₁ e₀ e₁ u : ℝ³} (L : ℝ³ →L[ℝ] ℝ³) (h : SegMeet d₀ d₁ e₀ e₁ u) :
    SegMeet (L d₀) (L d₁) (L e₀) (L e₁) (L u) := by
  obtain ⟨s, t, μ, hs, hs1, ht, ht1, e⟩ := h
  refine ⟨s, t, μ, hs, hs1, ht, ht1, ?_⟩
  have := congrArg L e
  simpa [map_sub, map_add, map_smul] using this

/-- **MF core for the F2 pair.**  Original-shape sign/meeting hypotheses (as in `cert_type21_F2`'s
tail) and a unimodular `L`: at the mapped points with the mapped views `L u`, `L v` (what `CovView`
gives), the two rims are never both depth-separated. -/
theorem b5b_core {b b' c d a a' u v : ℝ³} (L : ℝ³ →L[ℝ] ℝ³)
    (hL : LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) = 1)
    (hdet : det3 u (b' - b) (c - d) * det3 v (b' - b) (c - d) *
      (det3 u (b' - b) (a - a') * det3 v (b' - b) (a - a')) < 0)
    (m1u : SegMeet b b' d c u) (m1v : SegMeet b b' d c v)
    (m2v : SegMeet b b' a' a v) (m2u : SegMeet b b' a' a u) :
    ¬ (DepthSep (L b) (L b') (L d) (L c) (L u) ∧ DepthSep (L b) (L b') (L a') (L a) (L v)) := by
  rintro ⟨h1, h2⟩
  refine not_both_depthSep h1 h2 (b5b_segMeet_map L m1u) (b5b_segMeet_map L m1v)
    (b5b_segMeet_map L m2v) (b5b_segMeet_map L m2u) ?_
  simp only [← map_sub, b5b_det3_map, hL, one_mul]
  exact hdet

theorem b5b_nodup_of_inj {x y z w : ℝ} (h : Function.Injective (quad x y z w)) :
    [x, y, z, w].Nodup := by
  have e := fun i j (hij : (i : ZMod 4) ≠ j) (hxy : quad x y z w i = quad x y z w j) => hij (h hxy)
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
    and_true]
  exact ⟨⟨fun hx => e 0 1 (by decide) (by simpa [quad] using hx), fun hx => e 0 2 (by decide) (by simpa [quad] using hx),
    fun hx => e 0 3 (by decide) (by simpa [quad] using hx)⟩, ⟨fun hx => e 1 2 (by decide) (by simpa [quad] using hx),
    fun hx => e 1 3 (by decide) (by simpa [quad] using hx)⟩, ⟨fun hx => e 2 3 (by decide) (by simpa [quad] using hx), not_false⟩⟩

/-- **The `hMF`-shaped conclusion** for the pair of rims (V at `u`, V' at `v`), mapped by `L`:
injective depths force one of the two rims to be cyclically unimodal. -/
theorem b5b_MF {b b' c d a a' u v : ℝ³} (L : ℝ³ →L[ℝ] ℝ³)
    (hL : LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) = 1)
    (hdet : det3 u (b' - b) (c - d) * det3 v (b' - b) (c - d) *
      (det3 u (b' - b) (a - a') * det3 v (b' - b) (a - a')) < 0)
    (m1u : SegMeet b b' d c u) (m1v : SegMeet b b' d c v)
    (m2v : SegMeet b b' a' a v) (m2u : SegMeet b b' a' a u)
    (i1 : Function.Injective (quad ⟪L b, L u⟫ ⟪L d, L u⟫ ⟪L b', L u⟫ ⟪L c, L u⟫))
    (i2 : Function.Injective (quad ⟪L b, L v⟫ ⟪L a', L v⟫ ⟪L b', L v⟫ ⟪L a, L v⟫)) :
    IsCyclicUnimodal (quad ⟪L b, L u⟫ ⟪L d, L u⟫ ⟪L b', L u⟫ ⟪L c, L u⟫) ∨
    IsCyclicUnimodal (quad ⟪L b, L v⟫ ⟪L a', L v⟫ ⟪L b', L v⟫ ⟪L a, L v⟫) := by
  by_contra hn
  push Not at hn
  have s1 : DepthSep (L b) (L b') (L d) (L c) (L u) := by
    by_contra hc; exact hn.1 (quad_unimodal hc (b5b_nodup_of_inj i1))
  have s2 : DepthSep (L b) (L b') (L a') (L a) (L v) := by
    by_contra hc; exact hn.2 (quad_unimodal hc (b5b_nodup_of_inj i2))
  exact b5b_core L hL hdet m1u m1v m2v m2u ⟨s1, s2⟩

/-- Views of the F2 pair at vertex views `1` (V) and `4` (V'), labelling `id` of `F2ViewsL`
(`b = x4, b' = x5, c = x1, d = x2, a = x0, a' = x3`): the quads are `(4,2,5,1)` and `(4,3,5,0)`. -/
noncomputable def b5b_g : Bool → ViewGroup 7
  | true => .single (LabTest.quad (fun y => view21 y (.inr 1)) 4 2 5 1)
  | false => .single (LabTest.quad (fun y => view21 y (.inr 4)) 4 3 5 0)

theorem b5b_depth_true (L : ℝ³ →L[ℝ] ℝ³) (y : Fin 7 → ℝ³)
    (hL : LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) = 1) :
    (LabTest.quad (fun y => view21 y (.inr 1)) 4 2 5 1).depth (mapShape L y) =
      quad ⟪L (y 4), L (view21 y (.inr 1))⟫ ⟪L (y 2), L (view21 y (.inr 1))⟫
        ⟪L (y 5), L (view21 y (.inr 1))⟫ ⟪L (y 1), L (view21 y (.inr 1))⟫ := by
  rw [← (covView_view21 (.inr 1)).2 L y hL]
  funext i
  fin_cases i <;> rfl

theorem b5b_depth_false (L : ℝ³ →L[ℝ] ℝ³) (y : Fin 7 → ℝ³)
    (hL : LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) = 1) :
    (LabTest.quad (fun y => view21 y (.inr 4)) 4 3 5 0).depth (mapShape L y) =
      quad ⟪L (y 4), L (view21 y (.inr 4))⟫ ⟪L (y 3), L (view21 y (.inr 4))⟫
        ⟪L (y 5), L (view21 y (.inr 4))⟫ ⟪L (y 0), L (view21 y (.inr 4))⟫ := by
  rw [← (covView_view21 (.inr 4)).2 L y hL]
  funext i
  fin_cases i <;> rfl

/-- **Phase A.**  F2 pair `(vtx 1, vtx 4)` at the shape `y`: the sign fact `hdet` and the four
`SegMeet`s (hypotheses, to be derived from Gale data), two ties (one per view) that are
independent and cover the rim coincidences: one of the two rims is robustly unimodal. -/
theorem b5b_F2_robust (y : Fin 7 → ℝ³)
    (hdet : det3 (view21 y (.inr 1)) (y 5 - y 4) (y 1 - y 2) *
        det3 (view21 y (.inr 4)) (y 5 - y 4) (y 1 - y 2) *
      (det3 (view21 y (.inr 1)) (y 5 - y 4) (y 0 - y 3) *
        det3 (view21 y (.inr 4)) (y 5 - y 4) (y 0 - y 3)) < 0)
    (m1u : SegMeet (y 4) (y 5) (y 2) (y 1) (view21 y (.inr 1)))
    (m1v : SegMeet (y 4) (y 5) (y 2) (y 1) (view21 y (.inr 4)))
    (m2v : SegMeet (y 4) (y 5) (y 3) (y 0) (view21 y (.inr 4)))
    (m2u : SegMeet (y 4) (y 5) (y 3) (y 0) (view21 y (.inr 1)))
    (hinj : ∀ a, ∀ T ∈ (b5b_g a).tests, Function.Injective T.lab)
    {q : ℕ} (hq : q ≤ 2) (ties : Fin q → Bool × Fin 7 × Fin 7)
    (hties : ∀ t, ⟪y (ties t).2.1 - y (ties t).2.2, (b5b_g (ties t).1).view y⟫ = 0)
    (hind : TieIndep (fun t => y (ties t).2.1 - y (ties t).2.2)
      (fun t => (b5b_g (ties t).1).view y))
    (hcover : ∀ a, ∀ T ∈ (b5b_g a).tests, ∀ i j : ZMod T.k, T.depth y i = T.depth y j →
      Relation.EqvGen (fun p p' => ∃ t, (ties t).1 = a ∧ (ties t).2 = (p, p')) (T.lab i) (T.lab j)) :
    IsRobustUnimodal (quad ⟪y 4, view21 y (.inr 1)⟫ ⟪y 2, view21 y (.inr 1)⟫
        ⟪y 5, view21 y (.inr 1)⟫ ⟪y 1, view21 y (.inr 1)⟫) ∨
    IsRobustUnimodal (quad ⟪y 4, view21 y (.inr 4)⟫ ⟪y 3, view21 y (.inr 4)⟫
        ⟪y 5, view21 y (.inr 4)⟫ ⟪y 0, view21 y (.inr 4)⟫) := by
  have hcov : ∀ a, CovView (b5b_g a).view := by
    intro a; cases a
    · exact covView_view21 (.inr 4)
    · exact covView_view21 (.inr 1)
  have hMF : ∀ᶠ L : ℝ³ →L[ℝ] ℝ³ in 𝓝 1, LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) = 1 →
      (∀ a, ∀ T ∈ (b5b_g a).tests, Function.Injective (T.depth (mapShape L y))) →
      ∃ a, ∃ T ∈ (b5b_g a).tests, IsCyclicUnimodal (T.depth (mapShape L y)) := by
    refine Filter.Eventually.of_forall fun L hL hi => ?_
    have i1 := hi true (LabTest.quad (fun y => view21 y (.inr 1)) 4 2 5 1) (by simp [b5b_g, ViewGroup.tests])
    have i2 := hi false (LabTest.quad (fun y => view21 y (.inr 4)) 4 3 5 0) (by simp [b5b_g, ViewGroup.tests])
    rw [b5b_depth_true L y hL] at i1
    rw [b5b_depth_false L y hL] at i2
    rcases b5b_MF L hL hdet m1u m1v m2v m2u i1 i2 with h | h
    · exact ⟨true, LabTest.quad (fun y => view21 y (.inr 1)) 4 2 5 1, by simp [b5b_g, ViewGroup.tests], by rw [b5b_depth_true L y hL]; exact h⟩
    · exact ⟨false, LabTest.quad (fun y => view21 y (.inr 4)) 4 3 5 0, by simp [b5b_g, ViewGroup.tests], by rw [b5b_depth_false L y hL]; exact h⟩
  have := robust_corner_rim_of_MF (n := 7) (q := q) (A := Bool) y b5b_g hcov
    (fun a => by cases a <;> simp [b5b_g, ViewGroup.Ordered])
    (fun a T h => by cases a <;> simp [b5b_g] at h <;> subst h <;> simp [LabTest.quad])
    hinj hq ties hties hind hcover hMF
  rcases this with ⟨a, T, hT, hr⟩ | ⟨a, hs⟩
  · cases a
    · simp [b5b_g, ViewGroup.tests] at hT; subst hT; right
      have e : (LabTest.quad (fun y => view21 y (.inr 4)) 4 3 5 0).depth y = quad ⟪y 4, view21 y (.inr 4)⟫ ⟪y 3, view21 y (.inr 4)⟫ ⟪y 5, view21 y (.inr 4)⟫ ⟪y 0, view21 y (.inr 4)⟫ := by
        funext i; fin_cases i <;> rfl
      rwa [e] at hr
    · simp [b5b_g, ViewGroup.tests] at hT; subst hT; left
      have e : (LabTest.quad (fun y => view21 y (.inr 1)) 4 2 5 1).depth y = quad ⟪y 4, view21 y (.inr 1)⟫ ⟪y 2, view21 y (.inr 1)⟫ ⟪y 5, view21 y (.inr 1)⟫ ⟪y 1, view21 y (.inr 1)⟫ := by
        funext i; fin_cases i <;> rfl
      rwa [e] at hr
  · cases a <;> simp [b5b_g, ViewGroup.Straddle] at hs

/-- `SegMeet` is invariant under replacing the view by a nonzero multiple (used to pass from
`axisView = lam * vtxView21` to `vtxView21`). -/
theorem b5b_segMeet_smul {d₀ d₁ e₀ e₁ u : ℝ³} {lam : ℝ} (hl : lam ≠ 0)
    (h : SegMeet d₀ d₁ e₀ e₁ (lam • u)) : SegMeet d₀ d₁ e₀ e₁ u := by
  obtain ⟨s, t, μ, hs, hs1, ht, ht1, e⟩ := h
  exact ⟨s, t, μ * lam, hs, hs1, ht, ht1, by rw [e, mul_smul]⟩

/-- The `hdet` product is invariant under nonzero scalings of the two views. -/
theorem b5b_hdet_smul {u v p q r : ℝ³} {l1 l2 : ℝ} (hl1 : l1 ≠ 0) (hl2 : l2 ≠ 0)
    (h : det3 (l1 • u) p q * det3 (l2 • v) p q * (det3 (l1 • u) p r * det3 (l2 • v) p r) < 0) :
    det3 u p q * det3 v p q * (det3 u p r * det3 v p r) < 0 := by
  have sm : ∀ (l : ℝ) (w x : ℝ³), det3 (l • w) p x = l * det3 w p x := by
    intro l w x; simp only [det3_expand, PiLp.smul_apply, smul_eq_mul]; ring
  have d1 := sm l1 u q
  have d2 := sm l2 v q
  have d3 := sm l1 u r
  have d4 := sm l2 v r
  have e : det3 (l1 • u) p q * det3 (l2 • v) p q * (det3 (l1 • u) p r * det3 (l2 • v) p r) =
      (l1 * l1 * l2 * l2) * (det3 u p q * det3 v p q * (det3 u p r * det3 v p r)) := by
    simp only [d1, d2, d3, d4]; ring
  rw [e] at h
  have : 0 < l1 * l1 * l2 * l2 := by
    have := mul_self_pos.2 hl1
    have := mul_self_pos.2 hl2
    nlinarith [mul_pos (mul_self_pos.2 hl1) (mul_self_pos.2 hl2)]
  exact neg_of_mul_neg_right h this.le

/-- The line of two planes as a cross product of their normals. -/
theorem planeLine_eq_cross (p₀ p₁ p₂ q₀ q₁ q₂ : ℝ³) :
    planeLine p₀ p₁ p₂ q₀ q₁ q₂ =
      cross (cross (p₁ - p₀) (p₂ - p₀)) (cross (q₁ - q₀) (q₂ - q₀)) := by
  ext i; fin_cases i <;>
    simp only [planeLine, det3_expand, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      cross_apply_zero, cross_apply_one, cross_apply_two, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul] <;> ring

/-! ### Step 1: parallelism of the F2 views with the named vertex views -/

/-- A vector in two planes whose normals have nonzero cross product is a multiple of that cross product. -/
theorem b5b_par {A B C D u : ℝ³} (h1 : det3 A B u = 0) (h2 : det3 C D u = 0)
    (hw : cross (cross A B) (cross C D) ≠ 0) :
    ∃ lam : ℝ, u = lam • cross (cross A B) (cross C D) := by
  refine ⟨_, eq_smul_of_cross_eq_zero hw ?_⟩
  rw [cross_cross_eq]
  have e1 : ⟪cross A B, u⟫ = 0 := h1
  have e2 : ⟪cross C D, u⟫ = 0 := h2
  rw [e1, e2, zero_smul, zero_smul, sub_zero]

theorem b5b_vtx1 (y : Fin 7 → ℝ³) : view21 y (.inr 1) =
    cross (cross (y 0 - y 4) (y 1 - y 4)) (cross (y 3 - y 4) (y 6 - y 4)) := by
  show planeLine _ _ _ _ _ _ = _
  rw [planeLine_eq_cross]; rfl

theorem b5b_vtx4 (y : Fin 7 → ℝ³) : view21 y (.inr 4) =
    cross (cross (y 0 - y 4) (y 6 - y 4)) (cross (y 3 - y 4) (y 1 - y 4)) := by
  show planeLine _ _ _ _ _ _ = _
  rw [planeLine_eq_cross]; rfl

/-- `axisView = lam * vtxView21 y 1` (nonzero `lam`), given the plane memberships and `vtxView21 ≠ 0`. -/
theorem b5b_par1 {y : Fin 7 → ℝ³} {u : ℝ³} (hu : u ≠ 0)
    (h1 : det3 (y 0 - y 4) (y 1 - y 4) u = 0) (h2 : det3 (y 3 - y 4) (y 6 - y 4) u = 0)
    (hw : view21 y (.inr 1) ≠ 0) : ∃ lam : ℝ, lam ≠ 0 ∧ u = lam • view21 y (.inr 1) := by
  rw [b5b_vtx1] at hw ⊢
  obtain ⟨lam, h⟩ := b5b_par h1 h2 hw
  exact ⟨lam, fun e => hu (by rw [h, e, zero_smul]), h⟩

theorem b5b_par4 {y : Fin 7 → ℝ³} {u : ℝ³} (hu : u ≠ 0)
    (h1 : det3 (y 0 - y 4) (y 6 - y 4) u = 0) (h2 : det3 (y 3 - y 4) (y 1 - y 4) u = 0)
    (hw : view21 y (.inr 4) ≠ 0) : ∃ lam : ℝ, lam ≠ 0 ∧ u = lam • view21 y (.inr 4) := by
  rw [b5b_vtx4] at hw ⊢
  obtain ⟨lam, h⟩ := b5b_par h1 h2 hw
  exact ⟨lam, fun e => hu (by rw [h, e, zero_smul]), h⟩

/-! ### Step 2a: `hcover` from `OneTieAt` -/

theorem b5b_indep_ne {q : ℕ} {d u : Fin q → ℝ³} (h : TieIndep d u) (t : Fin q) : d t ≠ 0 := by
  intro h0
  have := h (Pi.single t 1) (fun G => by
    rw [Finset.sum_eq_single t]
    · simp [h0]
    · intro t' _ ht'; simp [Pi.single_apply, ht']
    · simp)
  have := congrFun this t
  simp at this

theorem b5b_hcover (y : Fin 7 → ℝ³) (hyinj : Function.Injective y)
    (o : ∀ a, OneTieAt (Finset.univ.image y) ((b5b_g a).view y))
    {q : ℕ} (ties : Fin q → Bool × Fin 7 × Fin 7)
    (hties : ∀ t, ⟪y (ties t).2.1 - y (ties t).2.2, (b5b_g (ties t).1).view y⟫ = 0)
    (hind : TieIndep (fun t => y (ties t).2.1 - y (ties t).2.2)
      (fun t => (b5b_g (ties t).1).view y))
    (hex : ∀ a, (∃ i j : Fin 7, i ≠ j ∧ ⟪y i, (b5b_g a).view y⟫ = ⟪y j, (b5b_g a).view y⟫) →
      ∃ t, (ties t).1 = a)
    (hlab : ∀ a, ∀ T ∈ (b5b_g a).tests, Function.Injective T.lab) :
    ∀ a, ∀ T ∈ (b5b_g a).tests, ∀ i j : ZMod T.k, T.depth y i = T.depth y j →
      Relation.EqvGen (fun p p' => ∃ t, (ties t).1 = a ∧ (ties t).2 = (p, p')) (T.lab i) (T.lab j) := by
  intro a T hT i j hij
  by_cases hl : T.lab i = T.lab j
  · rw [hl]; exact Relation.EqvGen.refl _
  have hTv : T.view = (b5b_g a).view := by
    cases a <;> simp [b5b_g, ViewGroup.tests] at hT <;> subst hT <;> rfl
  have hd : ⟪y (T.lab i), (b5b_g a).view y⟫ = ⟪y (T.lab j), (b5b_g a).view y⟫ := by
    have := hij; simp only [LabTest.depth, hTv] at this; exact this
  obtain ⟨t, ht⟩ := hex a ⟨_, _, hl, hd⟩
  have hne : y (ties t).2.1 - y (ties t).2.2 ≠ 0 := b5b_indep_ne hind t
  have hrr : (ties t).2.1 ≠ (ties t).2.2 := fun e => hne (by rw [e, sub_self])
  have hv := hties t
  rw [ht] at hv
  have hv' : ⟪y (ties t).2.1, (b5b_g a).view y⟫ = ⟪y (ties t).2.2, (b5b_g a).view y⟫ := by
    rwa [inner_sub_left, sub_eq_zero] at hv
  have mem : ∀ k, y k ∈ Finset.univ.image y := fun k => Finset.mem_image_of_mem y (Finset.mem_univ k)
  rcases o a _ (mem _) _ (mem _) _ (mem _) _ (mem _) (fun e => hl (hyinj e)) (fun e => hrr (hyinj e))
    hd hv' with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · have := hyinj e1; have := hyinj e2
    refine Relation.EqvGen.rel _ _ ⟨t, ht, ?_⟩
    ext <;> simp [*]
  · have h1 := hyinj e1; have h2 := hyinj e2
    refine Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨t, ht, ?_⟩)
    ext <;> simp [*]


/-! ### Step 2: the weak/weak F2 certificate -/

theorem b5b_quad_smul (l a b c d : ℝ) :
    quad (l * a) (l * b) (l * c) (l * d) = fun i => l * quad a b c d i := by
  funext i; fin_cases i <;> rfl

theorem b5b_K_eq (y : Fin 7 → ℝ³) {a a' b b' c c' d : ℝ³} (ha : y 0 = a) (ha' : y 3 = a')
    (hb : y 4 = b) (hb' : y 5 = b') (hc : y 1 = c) (hc' : y 6 = c') (hd : y 2 = d) :
    (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) = Finset.univ.image y := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    exacts [⟨2, hd⟩, ⟨0, ha⟩, ⟨3, ha'⟩, ⟨4, hb⟩, ⟨5, hb'⟩, ⟨1, hc⟩, ⟨6, hc'⟩]
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [ha, ha', hb, hb', hc, hc', hd]

theorem b5b_lab_inj : ∀ a, ∀ T ∈ (b5b_g a).tests, Function.Injective T.lab := by
  intro a T hT
  cases a <;> simp [b5b_g, ViewGroup.tests] at hT <;> subst hT <;> simp only [LabTest.quad] <;> decide

variable {L : ℝ³ → Prop}

/-- **The weak/weak variant of `cert_type21_F2`, at a shape `y`** (core of `cert_type21_F2_weak`) (labels `a = y 0, a' = y 3, b = y 4,
b' = y 5, c = y 1, c' = y 6, d = y 2`): `F2Tie` is replaced by `OneTieAt` at both views, the
non-coplanarity `hS2` of the `V'` diagonals, and two listed independent ties (`q ≤ 2`) that list every
tie of the two vertex views (`hex`); the plane memberships `hN1..hN4` and `vtxView21 ≠ 0` identify
the axis views with the named views. -/
theorem cert_type21_F2_weak_core {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c') {σ₁ σ₂ s₁ δ₁ s₁' δ₁' s₂ δ₂ s₂' δ₂' : ℝ}
    (hσ₁ : σ₁ = 1 ∨ σ₁ = -1)
    (hT₁ : 0 < σ₁ * det3 (d - b) (c - b) (axisView G.l G.m b' b a c))
    (hΓ₁ : 0 < σ₁ * det3 (d - b) (b' - b) (axisView G.l G.m b' b a c))
    (hB₁ : 0 < σ₁ * det3 (b' - b) (c - b) (axisView G.l G.m b' b a c))
    (hP₁ : det3 (c - d) (b' - d) (axisView G.l G.m b' b a c) ≠ 0)
    (hm₁ : 0 < s₁ ∧ s₁ < 1 ∧ δ₁ ≠ 0 ∧ a' = b + s₁ • (d - b) + δ₁ • axisView G.l G.m b' b a c)
    (hm₁' : 0 < s₁' ∧ s₁' < 1 ∧ δ₁' ≠ 0 ∧ a = b + s₁' • (c - b) + δ₁' • axisView G.l G.m b' b a c)
    (hX₁ : AxisExtra b' b d c (axisView G.l G.m b' b a c) c')

    (hσ₂ : σ₂ = 1 ∨ σ₂ = -1)
    (hT₂ : 0 < σ₂ * det3 (a' - b) (a - b) (axisView G.l G.m b' b a c'))
    (hΓ₂ : 0 < σ₂ * det3 (a' - b) (b' - b) (axisView G.l G.m b' b a c'))
    (hB₂ : 0 < σ₂ * det3 (b' - b) (a - b) (axisView G.l G.m b' b a c'))
    (hP₂ : det3 (a - a') (b' - a') (axisView G.l G.m b' b a c') ≠ 0)
    (hm₂ : 0 < s₂ ∧ s₂ < 1 ∧ δ₂ ≠ 0 ∧ c = b + s₂ • (a' - b) + δ₂ • axisView G.l G.m b' b a c')
    (hm₂' : 0 < s₂' ∧ s₂' < 1 ∧ δ₂' ≠ 0 ∧ c' = b + s₂' • (a - b) + δ₂' • axisView G.l G.m b' b a c')
    (hX₂ : AxisExtra b' b a' a (axisView G.l G.m b' b a c') d)

    (hmeet : SegMeet b b' d c (axisView G.l G.m b' b a c'))
    (hsign : 0 < det3 (axisView G.l G.m b' b a c) (b' - b) (c - d) *
      det3 (axisView G.l G.m b' b a c') (b' - b) (c - d))
    (hc'u : ∃ s δ : ℝ, δ < 0 ∧ c' = b + s • (d - b) + δ • axisView G.l G.m b' b a c)
    (hcone : ∃ α β γ : ℝ, 0 < α ∧ 0 < β ∧ 0 < γ ∧
      -axisView G.l G.m b' b a c' = α • (c - b) + β • (b - d) + γ • (c' - b))
    (hΔ : VDelta b b' c c' d)
    (hL₁ : VRim (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) a a' b b' c c' d
      (σ₁ • axisView G.l G.m b' b a c) → L (σ₁ • axisView G.l G.m b' b a c))
    (hL₂ : L (σ₂ • axisView G.l G.m b' b a c'))
    -- the shape and its labels
    (y : Fin 7 → ℝ³) (ha : y 0 = a) (ha' : y 3 = a') (hb : y 4 = b) (hb' : y 5 = b')
    (hc : y 1 = c) (hc' : y 6 = c') (hd : y 2 = d) (hyinj : Function.Injective y)
    -- the axis views lie on the vertex-crossing lines, which are nonzero
    (hN1 : det3 (a - b) (c - b) (axisView G.l G.m b' b a c) = 0)
    (hN2 : det3 (a' - b) (c' - b) (axisView G.l G.m b' b a c) = 0)
    (hN3 : det3 (a - b) (c' - b) (axisView G.l G.m b' b a c') = 0)
    (hN4 : det3 (a' - b) (c - b) (axisView G.l G.m b' b a c') = 0)
    (hw1 : view21 y (.inr 1) ≠ 0) (hw4 : view21 y (.inr 4) ≠ 0)
    -- the weak ties: `OneTieAt` at both views, `V'` diagonals not coplanar
    (o1 : OneTieAt (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) (axisView G.l G.m b' b a c))
    (o2 : OneTieAt (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) (axisView G.l G.m b' b a c'))
    (hS2 : det3 (a' - b) (b' - b) (a - a') ≠ 0)
    -- the listed independent ties
    {q : ℕ} (hq : q ≤ 2) (ties : Fin q → Bool × Fin 7 × Fin 7)
    (hties : ∀ t, ⟪y (ties t).2.1 - y (ties t).2.2, (b5b_g (ties t).1).view y⟫ = 0)
    (hind : TieIndep (fun t => y (ties t).2.1 - y (ties t).2.2)
      (fun t => (b5b_g (ties t).1).view y))
    (hex : ∀ a, (∃ i j : Fin 7, i ≠ j ∧ ⟪y i, (b5b_g a).view y⟫ = ⟪y j, (b5b_g a).view y⟫) →
      ∃ t, (ties t).1 = a) :
    CertV (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L
      (SegOK21 (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) a a' b b' c c' d) := by
  set u := axisView G.l G.m b' b a c with hu
  set v := axisView G.l G.m b' b a c' with hv
  set K := insert d ({a, a', b, b', c, c'} : Finset ℝ³) with hK
  obtain ⟨hs₁0, hs₁1, hδ₁, hm₁⟩ := hm₁
  obtain ⟨hs₁0', hs₁1', hδ₁', hm₁'⟩ := hm₁'
  obtain ⟨hs₂0, hs₂1, hδ₂, hm₂⟩ := hm₂
  obtain ⟨hs₂0', hs₂1', hδ₂', hm₂'⟩ := hm₂'
  have hKa : a ∈ K := by simp [hK]
  have hKa' : a' ∈ K := by simp [hK]
  have hKb : b ∈ K := by simp [hK]
  have hKb' : b' ∈ K := by simp [hK]
  have hKc : c ∈ K := by simp [hK]
  have hKd : d ∈ K := by simp [hK]
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  have hbd : b ≠ d := by
    intro e
    have h0 : det3 (d - b) (c - b) u = 0 := by
      rw [← e, sub_self]; simp only [det3_expand, PiLp.zero_apply]; ring
    rw [h0, mul_zero] at hT₁; exact lt_irrefl _ hT₁
  have hdb' : d ≠ b' := by
    intro e
    have h0 : det3 (d - b) (b' - b) u = 0 := by
      rw [e]; simp only [det3_expand, PiLp.sub_apply]; ring
    rw [h0, mul_zero] at hΓ₁; exact lt_irrefl _ hΓ₁
  have hdc : d ≠ c := by
    intro e
    have h0 : det3 (d - b) (c - b) u = 0 := by
      rw [e]; simp only [det3_expand, PiLp.sub_apply]; ring
    rw [h0, mul_zero] at hT₁; exact lt_irrefl _ hT₁
  have htri₁ : ¬ (⟪b, u⟫ = ⟪d, u⟫ ∧ ⟪d, u⟫ = ⟪c, u⟫) := by
    rintro ⟨e1, e2⟩
    rcases o1 b hKb d hKd d hKd c hKc hbd hdc e1 e2 with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hbd h1
    · exact hbc h1
  have htri₂ : ¬ (⟪b, v⟫ = ⟪a', v⟫ ∧ ⟪a', v⟫ = ⟪a, v⟫) := by
    rintro ⟨e1, e2⟩
    rcases o2 b hKb a' hKa' a' hKa' a hKa (Ne.symm ha'b) (Ne.symm haa') e1 e2 with
      ⟨h1, -⟩ | ⟨h1, -⟩
    · exact ha'b h1.symm
    · exact hab h1.symm
  -- the test `V` at `u` (core labels `(b', b, d, c)`)
  obtain ⟨K1, K2⟩ := rimCertPts_axisTest_core_gen hσ₁ hT₁ hΓ₁ hB₁ htri₁ K (by simp [hK])
    (by simp [hK]) (by simp [hK]) (by simp [hK]) (fun x hx => by
      simp only [hK, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨s₁', δ₁', hs₁0', hs₁1', hδ₁', hm₁'⟩)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s₁, δ₁, hs₁0, hs₁1, hδ₁, hm₁⟩)))))
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr hX₁))))
  -- the test `V'` at `v` (core labels `(b', b, a', a)`)
  obtain ⟨L1, L2⟩ := rimCert_axisTest_core_gen hσ₂ hT₂ hΓ₂ hB₂ htri₂ K (by simp [hK])
    (by simp [hK]) (by simp [hK]) (by simp [hK]) (fun x hx => by
      simp only [hK, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inr hX₂)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s₂, δ₂, hs₂0, hs₂1, hδ₂, hm₂⟩)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨s₂', δ₂', hs₂0', hs₂1', hδ₂',
          hm₂'⟩))))))
  have hσσ₁ : σ₁ ≠ 0 := by rcases hσ₁ with rfl | rfl <;> norm_num
  have hσσ₂ : σ₂ ≠ 0 := by rcases hσ₂ with rfl | rfl <;> norm_num
  have nd1 : [b, d, b', c].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true]
    exact ⟨⟨hbd, hbb', hbc⟩, ⟨hdb', hdc⟩, hb'c, not_false⟩
  have nd2 : [b, a', b', a].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true]
    exact ⟨⟨Ne.symm ha'b, hbb', Ne.symm hab⟩, ⟨ha'b', Ne.symm haa'⟩, Ne.symm hab', not_false⟩
  -- `V′` first: its certificate needs no data (two triangles)
  rcases lt_or_gt_of_ne (mul_ne_zero hσσ₂ hP₂) with hα₂ | hα₂
  swap; · exact CertV.line hL₂ (L1 hα₂)
  by_cases hR2 : IsRobustUnimodal (quad ⟪b, v⟫ ⟪a', v⟫ ⟪b', v⟫ ⟪a, v⟫)
  · exact CertV.line hL₂ (L2 hα₂ hR2)
  -- `V`, with `V′` failing
  rcases lt_or_gt_of_ne (mul_ne_zero hσσ₁ hP₁) with hα₁ | hα₁
  swap; · exact CertV.line (hL₁ (Or.inr (K1 hα₁))) (K1 hα₁).rimCert3
  obtain ⟨m1u, m2u⟩ := axisTest_meets hσ₁ hs₁0 hs₁1 hm₁ hs₁0' hs₁1' hm₁' hT₁ hΓ₁ hB₁ hα₁
  obtain ⟨m2v, -⟩ := axisTest_meets hσ₂ hs₂0 hs₂1 hm₂ hs₂0' hs₂1' hm₂' hT₂ hΓ₂ hB₂ hα₂
  have h08 : det3 u (b' - b) (a - a') * det3 v (b' - b) (a - a') < 0 :=
    vertex_sep F.swap₁.swap₂.swap₃ G.swap₁.swap₂.swap₃
  -- Lemma 22.14 (ii): `V′` fails, so `⟪u_V′, u_V⟫ ≤ 0`
  have huv : ⟪v, u⟫ ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have B := (show 0 ≤ ⟪v, u⟫ * (det3 v (b' - b) (a - a') * det3 u (b' - b) (a - a')) by
      have W2 := weakSep_of_not_robust (o2.oneTie4 hKb hKa' hKb' hKa nd2) hR2
      exact weakSep_det_sign W2.symm m2v m2u hpos.ne' hS2)
    have hprod : det3 v (b' - b) (a - a') * det3 u (b' - b) (a - a') < 0 := by
      linarith [mul_comm (det3 v (b' - b) (a - a')) (det3 u (b' - b) (a - a'))]
    linarith [mul_pos hpos (neg_pos.mpr hprod)]
  by_cases hR1 : IsRobustUnimodal (quad ⟪b, u⟫ ⟪d, u⟫ ⟪b', u⟫ ⟪c, u⟫)
  · -- `V`'s quadrilateral, with the data of Lemmas 22.13 and 22.14
    refine CertV.line (hL₁ (Or.inl ⟨K2 hα₁ hR1, ?_, hΔ⟩)) (K2 hα₁ hR1).rimCert4
    obtain ⟨s, δ, hδ, hc'⟩ := hc'u
    obtain ⟨α, β, γ, hα, hβ, hγ, hy⟩ := hcone
    have hv0 : v ≠ 0 := by
      intro h0
      have : det3 (a' - b) (a - b) v = 0 := by
        rw [h0]; simp only [det3_expand, PiLp.zero_apply]; ring
      rw [this, mul_zero] at hT₂; exact lt_irrefl _ hT₂
    refine ⟨-v, neg_ne_zero.mpr hv0, ?_, ?_, ?_⟩
    · rw [hm₂']; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
        PiLp.neg_apply, smul_eq_mul]; ring
    · rw [hm₂]; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
        PiLp.neg_apply, smul_eq_mul]; ring
    · set Dg := det3 (c - b) (b - d) (c' - b) with hDg
      have e1 : det3 (-v) (b - d) (c' - b) = α * Dg := by
        rw [hy, hDg]; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
          smul_eq_mul]; ring
      have e2 : det3 (c - b) (-v) (c' - b) = β * Dg := by
        rw [hy, hDg]; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
          smul_eq_mul]; ring
      have e3 : det3 (c - b) (b - d) (-v) = γ * Dg := by
        rw [hy, hDg]; simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
          smul_eq_mul]; ring
      have ec : cross (d - b) (c' - b) = δ • cross (d - b) u := by
        rw [hc']; ext j; fin_cases j <;> simp [cross] <;> ring
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [e1, mul_assoc]; exact mul_nonneg hα.le (mul_self_nonneg Dg)
      · rw [e2, mul_assoc]; exact mul_nonneg hβ.le (mul_self_nonneg Dg)
      · rw [e3, mul_assoc]; exact mul_nonneg hγ.le (mul_self_nonneg Dg)
      · rw [ec, cross_smul_right', real_inner_smul_left, real_inner_smul_right,
          real_inner_smul_right, inner_neg_left]
        have hσσ : σ₁ * σ₁ = 1 := by rcases hσ₁ with rfl | rfl <;> norm_num
        have hCC := real_inner_self_nonneg (x := cross (d - b) u)
        have : δ * (σ₁ * ⟪cross (d - b) u, cross (d - b) u⟫) * (σ₁ * -⟪v, u⟫) =
            δ * (⟪cross (d - b) u, cross (d - b) u⟫ * -⟪v, u⟫) := by
          linear_combination (δ * ⟪cross (d - b) u, cross (d - b) u⟫ * -⟪v, u⟫) * hσσ
        rw [this]
        exact mul_nonpos_of_nonpos_of_nonneg hδ.le (mul_nonneg hCC (by linarith))
  exfalso
  have hdet := mul_neg_of_pos_of_neg hsign h08
  have hu0 : u ≠ 0 := by
    intro h0
    have : det3 (d - b) (c - b) u = 0 := by
      rw [h0]; simp only [det3_expand, PiLp.zero_apply]; ring
    rw [this, mul_zero] at hT₁; exact lt_irrefl _ hT₁
  have hv0 : v ≠ 0 := by
    intro h0
    have : det3 (a' - b) (a - b) v = 0 := by
      rw [h0]; simp only [det3_expand, PiLp.zero_apply]; ring
    rw [this, mul_zero] at hT₂; exact lt_irrefl _ hT₂
  obtain ⟨l1, hl1, hu1⟩ := b5b_par1 (y := y) hu0 (by rw [ha, hb, hc]; exact hN1)
    (by rw [ha', hb, hc']; exact hN2) hw1
  obtain ⟨l2, hl2, hv1⟩ := b5b_par4 (y := y) hv0 (by rw [ha, hb, hc']; exact hN3)
    (by rw [ha', hb, hc]; exact hN4) hw4
  have hdet' := b5b_hdet_smul hl1 hl2 (by rw [← hu1, ← hv1]; exact hdet)
  have m1u' := b5b_segMeet_smul hl1 (by rw [← hu1]; exact m1u)
  have m1v' := b5b_segMeet_smul hl2 (by rw [← hv1]; exact hmeet)
  have m2v' := b5b_segMeet_smul hl2 (by rw [← hv1]; exact m2v)
  have m2u' := b5b_segMeet_smul hl1 (by rw [← hu1]; exact m2u)
  simp only [← ha, ← ha', ← hb, ← hb', ← hc, ← hc', ← hd] at hdet' m1u' m1v' m2v' m2u'
  have oo : ∀ x : Bool, OneTieAt (Finset.univ.image y) ((b5b_g x).view y) := by
    rw [← b5b_K_eq y ha ha' hb hb' hc hc' hd]
    intro x; cases x
    · have := o2.smul (inv_ne_zero hl2)
      rw [hv1, smul_smul, inv_mul_cancel₀ hl2, one_smul] at this
      exact this
    · have := o1.smul (inv_ne_zero hl1)
      rw [hu1, smul_smul, inv_mul_cancel₀ hl1, one_smul] at this
      exact this
  have hcov := b5b_hcover y hyinj oo ties hties hind hex b5b_lab_inj
  have R := b5b_F2_robust y hdet' m1u' m1v' m2v' m2u' b5b_lab_inj hq ties hties hind hcov
  rcases R with R | R
  · apply hR1
    have e : quad ⟪b, u⟫ ⟪d, u⟫ ⟪b', u⟫ ⟪c, u⟫ = fun i => l1 *
        quad ⟪y 4, view21 y (.inr 1)⟫ ⟪y 2, view21 y (.inr 1)⟫ ⟪y 5, view21 y (.inr 1)⟫
          ⟪y 1, view21 y (.inr 1)⟫ i := by
      rw [← b5b_quad_smul, hu1, hb, hd, hb', hc]
      simp only [real_inner_smul_right]
    rw [e]; exact robust_mul_ne_zero R hl1
  · apply hR2
    have e : quad ⟪b, v⟫ ⟪a', v⟫ ⟪b', v⟫ ⟪a, v⟫ = fun i => l2 *
        quad ⟪y 4, view21 y (.inr 4)⟫ ⟪y 3, view21 y (.inr 4)⟫ ⟪y 5, view21 y (.inr 4)⟫
          ⟪y 0, view21 y (.inr 4)⟫ i := by
      rw [← b5b_quad_smul, hv1, hb, ha', hb', ha]
      simp only [real_inner_smul_right]
    rw [e]; exact robust_mul_ne_zero R hl2


/-! ### Phase B2: the tie hypothesis in terms of points -/

theorem b5b_tieIndep_smul {q : ℕ} {d u : Fin q → ℝ³} (h : TieIndep d u) {c : Fin q → ℝ}
    (hc : ∀ t, c t ≠ 0) : TieIndep d (fun t => c t • u t) := by
  intro lam hl
  have h0 := h (fun t => lam t * c t) (fun G => by
    rw [← hl G]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [map_smul, real_inner_smul_right, real_inner_smul_left]
    ring)
  funext t
  have := congrFun h0 t
  exact (mul_eq_zero.mp this).resolve_right (hc t)

/-- **Independence of the tied pairs at two views** (vacuous if either view has no tie). -/
def IndepF (K : Finset ℝ³) (u v : ℝ³) : Prop :=
  ∀ p ∈ K, ∀ p' ∈ K, p ≠ p' → ⟪p, u⟫ = ⟪p', u⟫ →
    ∀ r ∈ K, ∀ r' ∈ K, r ≠ r' → ⟪r, v⟫ = ⟪r', v⟫ → TieIndep ![p - p', r - r'] ![u, v]

theorem IndepF.smul {K : Finset ℝ³} {u v : ℝ³} (h : IndepF K u v) {c c' : ℝ} (hc : c ≠ 0)
    (hc' : c' ≠ 0) : IndepF K (c • u) (c' • v) := by
  intro p hp p' hp' hpp e r hr r' hr' hrr e'
  simp only [real_inner_smul_right] at e e'
  have := b5b_tieIndep_smul (h p hp p' hp' hpp (mul_left_cancel₀ hc e) r hr r' hr' hrr
    (mul_left_cancel₀ hc' e')) (c := ![c, c']) (by
      intro t; fin_cases t
      · exact hc
      · exact hc')
  convert this using 1
  funext t; fin_cases t <;> rfl

/-- No tie at one of the views: nothing to be independent. -/
theorem IndepF.of_noTie {K : Finset ℝ³} {u v : ℝ³} (h : NoTieAt K u ∨ NoTieAt K v) :
    IndepF K u v := by
  intro p hp p' hp' hpp e r hr r' hr' hrr e'
  rcases h with h | h
  · exact absurd e (h p hp p' hp' hpp)
  · exact absurd e' (h r hr r' hr' hrr)

/-- **The weak tie hypothesis of F2** (labels as in `F2ViewsL`): one tie at each view, the two
diagonals non-coplanar, the tied pairs independent, and the seven points distinct. -/
def F2TieW (K : Finset ℝ³) (a a' b b' c c' d u v : ℝ³) : Prop :=
  OneTieAt K u ∧ OneTieAt K v ∧ det3 (d - b) (b' - b) (c - d) ≠ 0 ∧
    det3 (a' - b) (b' - b) (a - a') ≠ 0 ∧ IndepF K u v ∧
    Function.Injective ![a, c, d, a', b, b', c']

theorem b5b_cross_cross_ne {f : ℝ³ → ℝ} {N P A C A' C' : ℝ³}
    (hf : ∀ y z, f y - f z = ⟪N, y - z⟫) (fP : f P = 0) (fA : f A = 0) (fC : f C = 0)
    (fA' : f A' < 0) (n1 : cross (A - P) (C - P) ≠ 0) (n2 : cross (A' - P) (C' - P) ≠ 0) :
    cross (cross (A - P) (C - P)) (cross (A' - P) (C' - P)) ≠ 0 := by
  intro h0
  have e := eq_smul_of_cross_eq_zero n1 h0
  set κ := ⟪cross (A' - P) (C' - P), cross (A - P) (C - P)⟫ / ⟪cross (A - P) (C - P),
    cross (A - P) (C - P)⟫ with hκ
  have hκ0 : κ ≠ 0 := fun h => n2 (by rw [e, h, zero_smul])
  have h2 : ⟪cross (A' - P) (C' - P), A' - P⟫ = 0 := by
    show det3 (A' - P) (C' - P) (A' - P) = 0
    simp only [det3_expand]; ring
  rw [e, real_inner_smul_left] at h2
  have h3 : det3 (A - P) (C - P) (A' - P) = 0 := (mul_eq_zero.mp h2).resolve_left hκ0
  exact absurd (affine_zero_of_coplanar hf fP fA fC n1 h3) fA'.ne

/-- **`cert_type21_F2` with the tie hypothesis `F2Tie` replaced by `F2TieW`**: `OneTieAt` at both
views and independent tied pairs.  If a view has no tie, `F2Tie` applies; otherwise the shape
`y = ![a, c, d, a', b, b', c']` and `cert_type21_F2_weak_core`. -/
theorem cert_type21_F2_weak {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c') {σ₁ σ₂ s₁ δ₁ s₁' δ₁' s₂ δ₂ s₂' δ₂' : ℝ}
    (hσ₁ : σ₁ = 1 ∨ σ₁ = -1)
    (hT₁ : 0 < σ₁ * det3 (d - b) (c - b) (axisView G.l G.m b' b a c))
    (hΓ₁ : 0 < σ₁ * det3 (d - b) (b' - b) (axisView G.l G.m b' b a c))
    (hB₁ : 0 < σ₁ * det3 (b' - b) (c - b) (axisView G.l G.m b' b a c))
    (hP₁ : det3 (c - d) (b' - d) (axisView G.l G.m b' b a c) ≠ 0)
    (hm₁ : 0 < s₁ ∧ s₁ < 1 ∧ δ₁ ≠ 0 ∧ a' = b + s₁ • (d - b) + δ₁ • axisView G.l G.m b' b a c)
    (hm₁' : 0 < s₁' ∧ s₁' < 1 ∧ δ₁' ≠ 0 ∧ a = b + s₁' • (c - b) + δ₁' • axisView G.l G.m b' b a c)
    (hX₁ : AxisExtra b' b d c (axisView G.l G.m b' b a c) c')

    (hσ₂ : σ₂ = 1 ∨ σ₂ = -1)
    (hT₂ : 0 < σ₂ * det3 (a' - b) (a - b) (axisView G.l G.m b' b a c'))
    (hΓ₂ : 0 < σ₂ * det3 (a' - b) (b' - b) (axisView G.l G.m b' b a c'))
    (hB₂ : 0 < σ₂ * det3 (b' - b) (a - b) (axisView G.l G.m b' b a c'))
    (hP₂ : det3 (a - a') (b' - a') (axisView G.l G.m b' b a c') ≠ 0)
    (hm₂ : 0 < s₂ ∧ s₂ < 1 ∧ δ₂ ≠ 0 ∧ c = b + s₂ • (a' - b) + δ₂ • axisView G.l G.m b' b a c')
    (hm₂' : 0 < s₂' ∧ s₂' < 1 ∧ δ₂' ≠ 0 ∧ c' = b + s₂' • (a - b) + δ₂' • axisView G.l G.m b' b a c')
    (hX₂ : AxisExtra b' b a' a (axisView G.l G.m b' b a c') d)

    (hmeet : SegMeet b b' d c (axisView G.l G.m b' b a c'))
    (hsign : 0 < det3 (axisView G.l G.m b' b a c) (b' - b) (c - d) *
      det3 (axisView G.l G.m b' b a c') (b' - b) (c - d))
    (hties : F2Tie (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) b b' d c a' a
        (axisView G.l G.m b' b a c) (axisView G.l G.m b' b a c') ∨
      F2TieW (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) a a' b b' c c' d
        (axisView G.l G.m b' b a c) (axisView G.l G.m b' b a c'))
    (hc'u : ∃ s δ : ℝ, δ < 0 ∧ c' = b + s • (d - b) + δ • axisView G.l G.m b' b a c)
    (hcone : ∃ α β γ : ℝ, 0 < α ∧ 0 < β ∧ 0 < γ ∧
      -axisView G.l G.m b' b a c' = α • (c - b) + β • (b - d) + γ • (c' - b))
    (hΔ : VDelta b b' c c' d)
    (hL₁ : VRim (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) a a' b b' c c' d
      (σ₁ • axisView G.l G.m b' b a c) → L (σ₁ • axisView G.l G.m b' b a c))
    (hL₂ : L (σ₂ • axisView G.l G.m b' b a c'))
    -- the axis views lie on the vertex-crossing lines
    (hN1 : det3 (a - b) (c - b) (axisView G.l G.m b' b a c) = 0)
    (hN2 : det3 (a' - b) (c' - b) (axisView G.l G.m b' b a c) = 0)
    (hN3 : det3 (a - b) (c' - b) (axisView G.l G.m b' b a c') = 0)
    (hN4 : det3 (a' - b) (c - b) (axisView G.l G.m b' b a c') = 0)
    :
    CertV (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L
      (SegOK21 (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) a a' b b' c c' d) := by
  rcases hties with hties | hW
  · exact cert_type21_F2 F G hσ₁ hT₁ hΓ₁ hB₁ hP₁ hm₁ hm₁' hX₁ hσ₂ hT₂ hΓ₂ hB₂ hP₂ hm₂ hm₂' hX₂
      hmeet hsign hties hc'u hcone hΔ hL₁ hL₂
  obtain ⟨o1, o2, hS1, hS2, hind, hyinj⟩ := hW
  set u := axisView G.l G.m b' b a c with hu
  set v := axisView G.l G.m b' b a c' with hv
  set K := insert d ({a, a', b, b', c, c'} : Finset ℝ³) with hK
  by_cases hno : NoTieAt K u ∨ NoTieAt K v
  · exact cert_type21_F2 F G hσ₁ hT₁ hΓ₁ hB₁ hP₁ hm₁ hm₁' hX₁ hσ₂ hT₂ hΓ₂ hB₂ hP₂ hm₂ hm₂' hX₂
      hmeet hsign (Or.inr ⟨o1, o2, hno, hS1, hS2⟩) hc'u hcone hΔ hL₁ hL₂
  rw [not_or] at hno
  obtain ⟨hn1, hn2⟩ := hno
  simp only [NoTieAt, not_forall] at hn1 hn2
  obtain ⟨p, hp, p', hp', hpp, hpe⟩ := hn1
  obtain ⟨r, hr, r', hr', hrr, hre⟩ := hn2
  have hpe : ⟪p, u⟫ = ⟪p', u⟫ := not_not.mp hpe
  have hre : ⟪r, v⟫ = ⟪r', v⟫ := not_not.mp hre
  set y : Fin 7 → ℝ³ := ![a, c, d, a', b, b', c'] with hy
  have hKy : K = Finset.univ.image y :=
    b5b_K_eq y (a := a) (a' := a') (b := b) (b' := b') (c := c) (c' := c') (d := d) rfl rfl rfl rfl rfl rfl rfl
  have hind' := hind p hp p' hp' hpp hpe r hr r' hr' hrr hre
  rw [hKy] at hp hp' hr hr'
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hp'
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hr'
  -- nonzero named views, and the axis views are multiples
  have hnd := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  have n_abc' : cross (a - b) (c - b) ≠ 0 :=
    cross_ne_zero_of_affine F.abc'.hN (Ne.symm hab) F.abc'.hQ F.abc'.hP
      (F.abc'.neg c (by simp) (Ne.symm hac) (Ne.symm hbc) hcc')
  have n_a'bc : cross (a' - b) (c' - b) ≠ 0 :=
    cross_ne_zero_of_affine F.a'bc.hN (Ne.symm ha'b) F.a'bc.hQ F.a'bc.hP
      (F.a'bc.neg c' (by simp) (Ne.symm ha'c') (Ne.symm hbc') (Ne.symm hcc'))
  have n_abc : cross (a - b) (c' - b) ≠ 0 :=
    cross_ne_zero_of_affine F.abc.hN (Ne.symm hab) F.abc.hQ F.abc.hP
      (F.abc.neg c' (by simp) (Ne.symm hac') (Ne.symm hbc') (Ne.symm hcc'))
  have n_a'bc' : cross (a' - b) (c - b) ≠ 0 :=
    cross_ne_zero_of_affine F.a'bc'.hN (Ne.symm ha'b) F.a'bc'.hQ F.a'bc'.hP
      (F.a'bc'.neg c (by simp) (Ne.symm ha'c) (Ne.symm hbc) hcc')
  have hw1 : view21 y (.inr 1) ≠ 0 := by
    rw [b5b_vtx1]
    exact b5b_cross_cross_ne F.abc.hN F.abc.hQ F.abc.hP F.abc.hR
      (F.abc.neg a' (by simp) (Ne.symm haa') ha'b ha'c) n_abc' n_a'bc
  have hw4 : view21 y (.inr 4) ≠ 0 := by
    rw [b5b_vtx4]
    exact b5b_cross_cross_ne F.abc'.hN F.abc'.hQ F.abc'.hP F.abc'.hR
      (F.abc'.neg a' (by simp) (Ne.symm haa') ha'b ha'c') n_abc n_a'bc'
  have hu0 : u ≠ 0 := by
    intro h0
    have : det3 (d - b) (b' - b) u = 0 := by
      rw [h0]; simp only [det3_expand, PiLp.zero_apply]; ring
    rw [this, mul_zero] at hΓ₁; exact lt_irrefl _ hΓ₁
  have hv0 : v ≠ 0 := by
    intro h0
    have : det3 (a' - b) (b' - b) v = 0 := by
      rw [h0]; simp only [det3_expand, PiLp.zero_apply]; ring
    rw [this, mul_zero] at hΓ₂; exact lt_irrefl _ hΓ₂
  obtain ⟨lam, hl, e1⟩ := b5b_par1 (y := y) hu0 hN1 hN2 hw1
  obtain ⟨mu, hm, e2⟩ := b5b_par4 (y := y) hv0 hN3 hN4 hw4
  let ties : Fin 2 → Bool × Fin 7 × Fin 7 := ![(true, i, j), (false, k, l)]
  have hties : ∀ t, ⟪y (ties t).2.1 - y (ties t).2.2, (b5b_g (ties t).1).view y⟫ = 0 := by
    intro t
    fin_cases t
    · show ⟪y i - y j, view21 y (.inr 1)⟫ = 0
      have h0 : ⟪y i - y j, u⟫ = 0 := by rw [inner_sub_left, hpe, sub_self]
      rw [e1, real_inner_smul_right] at h0
      exact (mul_eq_zero.mp h0).resolve_left hl
    · show ⟪y k - y l, view21 y (.inr 4)⟫ = 0
      have h0 : ⟪y k - y l, v⟫ = 0 := by rw [inner_sub_left, hre, sub_self]
      rw [e2, real_inner_smul_right] at h0
      exact (mul_eq_zero.mp h0).resolve_left hm
  have hind2 : TieIndep (fun t => y (ties t).2.1 - y (ties t).2.2)
      (fun t => (b5b_g (ties t).1).view y) := by
    have := b5b_tieIndep_smul hind' (c := ![lam⁻¹, mu⁻¹]) (by
      intro t; fin_cases t
      · exact inv_ne_zero hl
      · exact inv_ne_zero hm)
    have k1 : (fun t => y (ties t).2.1 - y (ties t).2.2) = ![y i - y j, y k - y l] := by
      funext t; fin_cases t <;> rfl
    have k2 : (fun t => (b5b_g (ties t).1).view y) =
        fun t => (![lam⁻¹, mu⁻¹] : Fin 2 → ℝ) t • (![u, v] : Fin 2 → ℝ³) t := by
      funext t; fin_cases t
      · show view21 y (.inr 1) = lam⁻¹ • u
        rw [e1, smul_smul, inv_mul_cancel₀ hl, one_smul]
      · show view21 y (.inr 4) = mu⁻¹ • v
        rw [e2, smul_smul, inv_mul_cancel₀ hm, one_smul]
    rw [k1, k2]; exact this
  have hex : ∀ g, (∃ i j : Fin 7, i ≠ j ∧ ⟪y i, (b5b_g g).view y⟫ = ⟪y j, (b5b_g g).view y⟫) →
      ∃ t, (ties t).1 = g := by
    intro g _
    cases g
    · exact ⟨1, rfl⟩
    · exact ⟨0, rfl⟩
  exact cert_type21_F2_weak_core F G hσ₁ hT₁ hΓ₁ hB₁ hP₁ hm₁ hm₁' hX₁ hσ₂ hT₂ hΓ₂ hB₂ hP₂ hm₂ hm₂'
    hX₂ hmeet hsign hc'u hcone hΔ hL₁ hL₂ y rfl rfl rfl rfl rfl rfl rfl hyinj hN1 hN2 hN3 hN4 hw1 hw4
    o1 o2 hS2 (q := 2) le_rfl ties hties hind2 hex

end Minimality
