module

public import Mathlib
public import MinimalityExtra

/-!
# Coplanar silhouettes (Proposition 27.14, (i) ⇔ (ii))

Theorem 5's hypotheses for some `W` and `u` hold iff, on a nonempty open set of views, the
vertices over the shadow's corners are coplanar and every other vertex projects into the open
shadow.
-/

@[expose] public section

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

namespace MinimalityExtra

namespace CoplanarIff

lemma exists_ker {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (D : Submodule ℝ ℝ³) (h : Module.finrank ℝ D + Module.finrank ℝ E = 3) :
    ∃ g : ℝ³ →ₗ[ℝ] E, LinearMap.ker g = D := by
  have h1 := Submodule.finrank_quotient_add_finrank D
  rw [finrank_euclideanSpace_fin] at h1
  have h2 : Module.finrank ℝ (ℝ³ ⧸ D) = Module.finrank ℝ E := by omega
  let e : (ℝ³ ⧸ D) ≃ₗ[ℝ] E := LinearEquiv.ofFinrankEq _ _ h2
  refine ⟨(e : (ℝ³ ⧸ D) →ₗ[ℝ] E) ∘ₗ D.mkQ, ?_⟩
  rw [LinearEquiv.ker_comp, Submodule.ker_mkQ]

lemma exists_homeo (C : Set ℝ³) (hne : C.Nonempty) (π : ℝ³ →ₗ[ℝ] ℝ²) (u : ℝ³)
    (hker : LinearMap.ker π = Submodule.span ℝ {u})
    (hD : Module.finrank ℝ (affineSpan ℝ C).direction = 2)
    (hu : u ∉ (affineSpan ℝ C).direction) :
    ∃ e : affineSpan ℝ C ≃ₜ ℝ², ∀ x, e x = π x := by
  set A := affineSpan ℝ C with hA
  have : Nonempty A := by
    obtain ⟨c, hc⟩ := hne
    exact ⟨⟨c, subset_affineSpan ℝ C hc⟩⟩
  let L : A.direction →ₗ[ℝ] ℝ² := π ∘ₗ A.direction.subtype
  have hLinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro d hd
    have : (d : ℝ³) ∈ LinearMap.ker π := hd
    rw [hker, Submodule.mem_span_singleton] at this
    obtain ⟨c, hc⟩ := this
    by_cases hc0 : c = 0
    · subst hc0; ext1; simpa using hc.symm
    · exfalso; apply hu
      have : u = c⁻¹ • (d : ℝ³) := by rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      rw [this]; exact A.direction.smul_mem _ d.2
  have hLsurj : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [hD, finrank_euclideanSpace_fin])).1 hLinj
  let g : A →ᵃ[ℝ] ℝ² := π.toAffineMap.comp A.subtype
  have hg : ∀ x : A, g x = π x := fun x => rfl
  have hgb : Function.Bijective g := by
    constructor
    · intro x y hxy
      have h1 : L ⟨(x : ℝ³) - y, A.vsub_mem_direction x.2 y.2⟩ = 0 := by
        simp only [L, LinearMap.comp_apply, Submodule.subtype_apply, map_sub]
        rw [hg, hg] at hxy; rw [hxy, sub_self]
      have := hLinj (h1.trans (map_zero L).symm)
      ext1
      have := congrArg Subtype.val this
      simpa [sub_eq_zero] using this
    · intro y
      obtain ⟨a⟩ := ‹Nonempty A›
      obtain ⟨d, hd⟩ := hLsurj (y - g a)
      refine ⟨d +ᵥ a, ?_⟩
      show π (((d +ᵥ a : A)) : ℝ³) = y
      have : L d = π d := rfl
      have h2 : (((d +ᵥ a : A)) : ℝ³) = (d : ℝ³) + a := rfl
      rw [h2, map_add, ← this, hd]
      show _ + g a = _
      simp
  let ge : A ≃ᵃ[ℝ] ℝ² := AffineEquiv.ofBijective hgb
  exact ⟨ge.toContinuousAffineEquiv.toHomeomorph, fun x => rfl⟩


lemma mem_intrinsicInterior_iff (C : Set ℝ³) (hne : C.Nonempty) (π : ℝ³ →ₗ[ℝ] ℝ²) (u : ℝ³)
    (hker : LinearMap.ker π = Submodule.span ℝ {u})
    (hD : Module.finrank ℝ (affineSpan ℝ C).direction = 2)
    (hu : u ∉ (affineSpan ℝ C).direction) (q : ℝ³) (hq : q ∈ affineSpan ℝ C) :
    q ∈ intrinsicInterior ℝ C ↔ π q ∈ interior (π '' C) := by
  obtain ⟨e, he⟩ := exists_homeo C hne π u hker hD hu
  have himg : e '' (((↑) : affineSpan ℝ C → ℝ³) ⁻¹' C) = π '' C := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, (he y).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, subset_affineSpan ℝ C hx⟩, hx, he _⟩
  have key := e.image_interior (((↑) : affineSpan ℝ C → ℝ³) ⁻¹' C)
  rw [himg] at key
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← key, ← he]
    exact ⟨y, hy, rfl⟩
  · intro h
    rw [← key] at h
    obtain ⟨y, hy, hyq⟩ := h
    refine ⟨y, hy, ?_⟩
    have : y = ⟨q, hq⟩ := e.injective (by rw [hyq, he ⟨q, hq⟩])
    rw [this]


lemma nonempty_of_not_collinear {W : Set ℝ³} (hnc : ¬ Collinear ℝ W) : W.Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  exact hnc (h ▸ collinear_empty ℝ ℝ³)

lemma finrank_two (W : Set ℝ³) (hnc : ¬ Collinear ℝ W) (hcp : Coplanar ℝ W) :
    Module.finrank ℝ (affineSpan ℝ W).direction = 2 := by
  rw [direction_affineSpan]
  have h1 := hcp.finrank_le_two
  have h2 : ¬ Module.finrank ℝ (vectorSpan ℝ W) ≤ 1 :=
    fun h => hnc (collinear_iff_finrank_le_one.2 h)
  omega

lemma mem_intrinsicInterior_iff' (W : Set ℝ³) (hnc : ¬ Collinear ℝ W) (hcp : Coplanar ℝ W)
    (π : ℝ³ →ₗ[ℝ] ℝ²) (u : ℝ³) (hker : LinearMap.ker π = Submodule.span ℝ {u})
    (hu : u ∉ (affineSpan ℝ W).direction) (q : ℝ³) (hq : q ∈ affineSpan ℝ W) :
    q ∈ intrinsicInterior ℝ (convexHull ℝ W) ↔ π q ∈ interior (π '' convexHull ℝ W) := by
  have := affineSpan_convexHull (𝕜 := ℝ) W
  refine mem_intrinsicInterior_iff _ (nonempty_of_not_collinear hnc).convexHull
    π u hker ?_ ?_ q ?_
  · rw [this]; exact finrank_two W hnc hcp
  · rw [this]; exact hu
  · rw [this]; exact hq

lemma exists_point (W : Set ℝ³) (hnc : ¬ Collinear ℝ W) (hcp : Coplanar ℝ W)
    (π : ℝ³ →ₗ[ℝ] ℝ²) (u : ℝ³) (hker : LinearMap.ker π = Submodule.span ℝ {u})
    (hu : u ∉ (affineSpan ℝ W).direction) (y : ℝ²) :
    ∃ x ∈ affineSpan ℝ W, π x = y := by
  have := affineSpan_convexHull (𝕜 := ℝ) W
  obtain ⟨e, he⟩ := exists_homeo (convexHull ℝ W)
    (nonempty_of_not_collinear hnc).convexHull π u hker
    (by rw [this]; exact finrank_two W hnc hcp) (by rw [this]; exact hu)
  refine ⟨(e.symm y : ℝ³), ?_, ?_⟩
  · rw [← this]; exact (e.symm y).2
  · rw [← he, e.apply_symm_apply]

lemma injOn_plane (A : AffineSubspace ℝ ℝ³) (π : ℝ³ →ₗ[ℝ] ℝ²) (u : ℝ³)
    (hker : LinearMap.ker π = Submodule.span ℝ {u}) (hu : u ∉ A.direction) :
    Set.InjOn π (A : Set ℝ³) := by
  intro x hx y hy hxy
  have h1 : x - y ∈ LinearMap.ker π := by simp [map_sub, hxy]
  rw [hker, Submodule.mem_span_singleton] at h1
  obtain ⟨c, hc⟩ := h1
  by_cases hc0 : c = 0
  · subst hc0; simpa [sub_eq_zero] using hc.symm
  · exfalso; apply hu
    have h2 : u = c⁻¹ • (x - y) := by rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [h2]
    exact A.direction.smul_mem _ (A.vsub_mem_direction hx hy)

lemma image_extreme (C : Set ℝ³) (hC : Convex ℝ C) (π : ℝ³ →ₗ[ℝ] ℝ²) (hinj : Set.InjOn π C)
    (x : ℝ³) (hx : x ∈ Set.extremePoints ℝ C) : π x ∈ Set.extremePoints ℝ (π '' C) := by
  refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ ⟨s, t, hs, ht, hst, hseg⟩
  have hmem : s • a + t • b ∈ C := hC ha hb hs.le ht.le hst
  have heq : s • a + t • b = x := hinj hmem hx.1 (by rw [map_add, map_smul, map_smul]; exact hseg)
  have h1 := hx.2 ha hb ⟨s, t, hs, ht, hst, heq⟩
  have h2 := hx.2 hb ha ⟨t, s, ht, hs, by linarith, by rw [add_comm]; exact heq⟩
  rw [h1]

lemma not_collinear_of_top (X : Set ℝ²) (h : affineSpan ℝ X = ⊤) : ¬ Collinear ℝ X := by
  intro hc
  have h1 := hc.finrank_le_one
  rw [← direction_affineSpan, h, AffineSubspace.direction_top, finrank_top,
    finrank_euclideanSpace_fin] at h1
  omega

lemma finrank_map_lt (D : Submodule ℝ ℝ³) (π : ℝ³ →ₗ[ℝ] ℝ²) (u : ℝ³) (hu0 : u ≠ 0) (hu : u ∈ D)
    (hπu : π u = 0) : Module.finrank ℝ (D.map π) + 1 ≤ Module.finrank ℝ D := by
  have h := (π.domRestrict D).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict] at h
  have : 0 < Module.finrank ℝ (LinearMap.ker (π.domRestrict D)) := by
    apply Module.finrank_pos_iff_exists_ne_zero.2
    refine ⟨⟨⟨u, hu⟩, by simpa using hπu⟩, ?_⟩
    intro h0
    apply hu0
    simpa using congrArg (fun z => ((z : D) : ℝ³)) (congrArg Subtype.val h0)
  omega


theorem hyp_to_shadow (V : Finset ℝ³)
    (hconv : ∀ v ∈ V, v ∈ Set.extremePoints ℝ (convexHull ℝ (V : Set ℝ³)))
    (W : Finset ℝ³) (u0 : ℝ³) (h : CoplanarSilhouetteHyp V W u0) : CoplanarShadowCorners V := by
  classical
  obtain ⟨hWV, hnc, hcp, hu0, hin⟩ := h
  set Ws : Set ℝ³ := (W : Set ℝ³) with hWs
  have hD : Module.finrank ℝ (affineSpan ℝ Ws).direction = 2 := finrank_two Ws hnc hcp
  obtain ⟨f, hf⟩ := exists_ker (E := ℝ) (affineSpan ℝ Ws).direction (by rw [hD]; simp)
  have hfD : ∀ x, f x = 0 ↔ x ∈ (affineSpan ℝ Ws).direction := fun x => by
    rw [← hf]; simp
  obtain ⟨a, ha⟩ := nonempty_of_not_collinear hnc
  have haA : a ∈ affineSpan ℝ Ws := subset_affineSpan ℝ _ ha
  have hAmem : ∀ x, x ∈ affineSpan ℝ Ws ↔ f x = f a := fun x => by
    rw [← sub_eq_zero, ← map_sub, hfD]
    exact ⟨fun hx => AffineSubspace.vsub_mem_direction hx haA, fun hx => by
      have := AffineSubspace.vadd_mem_of_mem_direction hx haA
      simpa [vadd_eq_add] using this⟩
  have hspan := affineSpan_convexHull (𝕜 := ℝ) Ws
  obtain ⟨O, hO, hOeq⟩ : ∃ O : Set ℝ³, IsOpen O ∧
      (Subtype.val ⁻¹' O : Set (affineSpan ℝ (convexHull ℝ Ws))) =
        interior (Subtype.val ⁻¹' convexHull ℝ Ws) :=
    isOpen_induced_iff.1 isOpen_interior
  have hIO : ∀ x, x ∈ intrinsicInterior ℝ (convexHull ℝ Ws) ↔ x ∈ affineSpan ℝ Ws ∧ x ∈ O := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [← hOeq] at hy
      exact ⟨hspan ▸ y.2, hy⟩
    · rintro ⟨hx, hxO⟩
      have hx' : x ∈ affineSpan ℝ (convexHull ℝ Ws) := hspan ▸ hx
      refine ⟨⟨x, hx'⟩, ?_, rfl⟩
      rw [← hOeq]; exact hxO
  have hfc : Continuous f := LinearMap.continuous_of_finiteDimensional f
  let q : ℝ³ → ℝ³ → ℝ³ := fun v u => v + ((f a - f v) / f u) • u
  have hqf : ∀ v u, f u ≠ 0 → f (q v u) = f a := by
    intro v u hu
    simp only [q, map_add, map_smul, smul_eq_mul]
    field_simp; ring
  have hqπ : ∀ (π : ℝ³ →ₗ[ℝ] ℝ²) v u, π u = 0 → π (q v u) = π v := by
    intro π v u hπ
    simp [q, hπ]
  have hcont : ∀ v, ContinuousOn (q v) {u | f u ≠ 0} := by
    intro v
    have h1 : ContinuousOn (fun u => (f a - f v) / f u) {u | f u ≠ 0} :=
      continuousOn_const.div hfc.continuousOn (fun u hu => hu)
    exact continuousOn_const.add (h1.fun_smul continuousOn_id)
  have hopen0 : IsOpen {u : ℝ³ | f u ≠ 0} := isOpen_ne_fun hfc continuous_const
  let U : Set ℝ³ := {u | f u ≠ 0 ∧ ∀ v ∈ V, v ∉ W → q v u ∈ O}
  have hUopen : IsOpen U := by
    have : U = {u | f u ≠ 0} ∩ ⋂ v ∈ V.filter (· ∉ W), ({u | f u ≠ 0} ∩ q v ⁻¹' O) := by
      ext u
      simp only [U, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
        Finset.mem_filter]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun v hv => ⟨h1, h2 v hv.1 hv.2⟩⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun v hv hvW => (h2 v ⟨hv, hvW⟩).2⟩
    rw [this]
    refine hopen0.inter (isOpen_biInter_finset fun v _ => ?_)
    exact (hcont v).isOpen_inter_preimage hopen0 hO
  have hu0f : f u0 ≠ 0 := fun h0 => hu0 ((hfD u0).1 h0)
  have hu0U : u0 ∈ U := by
    refine ⟨hu0f, fun v hv hvW => ?_⟩
    obtain ⟨t, ht⟩ := hin v hv hvW
    obtain ⟨hA1, hO1⟩ := (hIO _).1 ht
    have h1 := (hAmem _).1 hA1
    have h2 : t = (f a - f v) / f u0 := by
      simp only [map_add, map_smul, smul_eq_mul] at h1
      field_simp; linarith
    have : q v u0 = v + t • u0 := by simp only [q, h2]
    rw [this]; exact hO1
  refine ⟨U, hUopen, ⟨u0, hu0U⟩, fun h0 => h0.1 (map_zero f), ?_⟩
  rintro u ⟨hfu, hUu⟩ π hker
  have hudir : u ∉ (affineSpan ℝ Ws).direction := fun h' => hfu ((hfD u).2 h')
  have hπu : π u = 0 := by
    have : u ∈ LinearMap.ker π := by rw [hker]; exact Submodule.mem_span_singleton_self u
    exact this
  have hL2 := mem_intrinsicInterior_iff' Ws hnc hcp π u hker hudir
  have key1 : ∀ v ∈ V, v ∉ W → π v ∈ interior (π '' convexHull ℝ Ws) := by
    intro v hv hvW
    have hxO := hUu v hv hvW
    have hxA : q v u ∈ affineSpan ℝ Ws := (hAmem _).2 (hqf v u hfu)
    have := (hL2 _ hxA).1 ((hIO _).2 ⟨hxA, hxO⟩)
    rwa [hqπ π v u hπu] at this
  have hinjC : Set.InjOn π (convexHull ℝ Ws) :=
    (injOn_plane (affineSpan ℝ Ws) π u hker hudir).mono (convexHull_subset_affineSpan Ws)
  have hextW : ∀ v ∈ W, π v ∈ Set.extremePoints ℝ (π '' convexHull ℝ Ws) := by
    intro v hv
    have h1 : v ∈ convexHull ℝ Ws ∩ Set.extremePoints ℝ (convexHull ℝ (V : Set ℝ³)) :=
      ⟨subset_convexHull ℝ _ hv, hconv v (hWV hv)⟩
    have h2 := inter_extremePoints_subset_extremePoints_of_subset
      (convexHull_mono (by exact_mod_cast hWV : Ws ⊆ (V : Set ℝ³))) h1
    exact image_extreme _ (convex_convexHull ℝ _) π hinjC v h2
  have hSeq : π '' convexHull ℝ (V : Set ℝ³) = π '' convexHull ℝ Ws := by
    apply Set.Subset.antisymm
    · rw [LinearMap.image_convexHull]
      apply convexHull_min _ ((convex_convexHull ℝ _).linear_image π)
      rintro _ ⟨v, hv, rfl⟩
      by_cases hvW : v ∈ W
      · exact ⟨v, subset_convexHull ℝ _ hvW, rfl⟩
      · exact interior_subset (key1 v hv hvW)
    · exact Set.image_mono (convexHull_mono (by exact_mod_cast hWV))
  rw [hSeq]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := Set.Nonempty.intrinsicInterior (convex_convexHull ℝ Ws)
      (nonempty_of_not_collinear hnc).convexHull
    have hxA := ((hIO x).1 hx).1
    exact ⟨π x, (hL2 x hxA).1 hx⟩
  · refine hcp.subset ?_
    rintro v ⟨hv, hext⟩
    by_contra hvW
    rw [hSeq] at hext
    exact Set.disjoint_left.1 (disjoint_interior_extremePoints _) (key1 v hv hvW) hext
  · intro v hv hext
    apply key1 v hv
    intro hvW
    exact hext (hextW v hvW)


lemma vs_image (π : ℝ³ →ₗ[ℝ] ℝ²) (X : Set ℝ³) :
    vectorSpan ℝ (π '' X) = (vectorSpan ℝ X).map π := by
  simpa using (AffineMap.map_vectorSpan (f := π.toAffineMap) (s := X)).symm

theorem shadow_to_hyp (V : Finset ℝ³) (h : CoplanarShadowCorners V) :
    ∃ (W : Finset ℝ³) (u : ℝ³), CoplanarSilhouetteHyp V W u := by
  classical
  obtain ⟨U, hUo, ⟨u, huU⟩, h0, H⟩ := h
  have hu0 : u ≠ 0 := fun h => h0 (h ▸ huU)
  obtain ⟨π, hker⟩ := exists_ker (E := ℝ²) (Submodule.span ℝ {u})
    (by rw [finrank_span_singleton hu0, finrank_euclideanSpace_fin])
  obtain ⟨h1, h2, h3⟩ := H u huU π hker
  have hπu : π u = 0 := by
    have : u ∈ LinearMap.ker π := by rw [hker]; exact Submodule.mem_span_singleton_self u
    exact this
  have hπc : Continuous π := LinearMap.continuous_of_finiteDimensional π
  set S := π '' convexHull ℝ (V : Set ℝ³) with hS
  have hSimg : S = convexHull ℝ (π '' (V : Set ℝ³)) := LinearMap.image_convexHull π _
  have hSconv : Convex ℝ S := (convex_convexHull ℝ _).linear_image π
  have hScomp : IsCompact S := (V.finite_toSet.isCompact_convexHull ℝ).image hπc
  let W : Finset ℝ³ := V.filter (fun v => π v ∈ Set.extremePoints ℝ S)
  have hWmem : ∀ v, v ∈ W ↔ v ∈ V ∧ π v ∈ Set.extremePoints ℝ S := fun v => Finset.mem_filter
  have hWs : (W : Set ℝ³) = ShadowCorners V π := by
    ext v; simp only [Finset.mem_coe, hWmem, ShadowCorners, Set.mem_ofPred_eq]; exact Iff.rfl
  have hextsub : Set.extremePoints ℝ S ⊆ π '' (V : Set ℝ³) := by
    rw [hSimg]; exact extremePoints_convexHull_subset
  have hextW : Set.extremePoints ℝ S = π '' (W : Set ℝ³) := by
    ext e
    constructor
    · intro he
      obtain ⟨v, hv, rfl⟩ := hextsub he
      exact ⟨v, (hWmem v).2 ⟨hv, he⟩, rfl⟩
    · rintro ⟨v, hv, rfl⟩; exact ((hWmem v).1 hv).2
  have hSW : S = π '' convexHull ℝ (W : Set ℝ³) := by
    have hfin : (Set.extremePoints ℝ S).Finite := (V.finite_toSet.image π).subset hextsub
    have hcl := closure_convexHull_extremePoints hScomp hSconv
    rw [(hfin.isCompact_convexHull ℝ).isClosed.closure_eq, hextW, ← LinearMap.image_convexHull] at hcl
    exact hcl.symm
  have hspanTop : affineSpan ℝ (π '' (W : Set ℝ³)) = ⊤ := by
    have := (hSconv.interior_nonempty_iff_affineSpan_eq_top).1 h1
    rwa [hSW, LinearMap.image_convexHull, affineSpan_convexHull] at this
  have hncπ := not_collinear_of_top _ hspanTop
  have hcp : Coplanar ℝ (W : Set ℝ³) := by rw [hWs]; exact h2
  have hnc : ¬ Collinear ℝ (W : Set ℝ³) := by
    intro hc
    apply hncπ
    rw [collinear_iff_finrank_le_one] at hc ⊢
    rw [vs_image]
    exact (Submodule.finrank_map_le π _).trans hc
  have hudir : u ∉ (affineSpan ℝ (W : Set ℝ³)).direction := by
    intro hmem
    rw [direction_affineSpan] at hmem
    apply hncπ
    rw [collinear_iff_finrank_le_one, vs_image]
    have := finrank_map_lt (vectorSpan ℝ (W : Set ℝ³)) π u hu0 hmem hπu
    have := hcp.finrank_le_two
    omega
  refine ⟨W, u, Finset.filter_subset _ _, hnc, hcp, hudir, ?_⟩
  intro v hv hvW
  have hint : π v ∈ interior S := h3 v hv (fun he => hvW ((hWmem v).2 ⟨hv, he⟩))
  obtain ⟨x, hxA, hxπ⟩ := exists_point (W : Set ℝ³) hnc hcp π u hker hudir (π v)
  have hxI : x ∈ intrinsicInterior ℝ (convexHull ℝ (W : Set ℝ³)) :=
    (mem_intrinsicInterior_iff' _ hnc hcp π u hker hudir x hxA).2 (by rw [hxπ, ← hSW]; exact hint)
  have hker2 : x - v ∈ LinearMap.ker π := by simp [map_sub, hxπ]
  rw [hker, Submodule.mem_span_singleton] at hker2
  obtain ⟨t, ht⟩ := hker2
  exact ⟨t, by rw [ht]; simpa using hxI⟩

end CoplanarIff

theorem coplanarSilhouetteIff : CoplanarSilhouetteIff := by
  intro V hconv
  constructor
  · rintro ⟨W, u, h⟩
    exact CoplanarIff.hyp_to_shadow V hconv W u h
  · exact CoplanarIff.shadow_to_hyp V

end MinimalityExtra
