module

public import Mathlib
public import MinimalityExtra

/-!
# Theorem F, the Anchor Lemma's core, and spin of inward motions
-/

@[expose] public section

open Matrix

namespace MinimalityExtra

/-- projection onto `annV v` along `l` -/
noncomputable def projAnn (v l x : Fin 3 → ℝ) : Fin 3 → ℝ := x - ((x ⬝ᵥ v) / (l ⬝ᵥ v)) • l

theorem projAnn_mem (v l x : Fin 3 → ℝ) (hs : l ⬝ᵥ v ≠ 0) : projAnn v l x ⬝ᵥ v = 0 := by
  simp only [projAnn, sub_dotProduct, smul_dotProduct, smul_eq_mul]
  field_simp; ring

theorem decomp (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : Mᵀ = M) (v l : Fin 3 → ℝ) (hl : M *ᵥ l = v)
    (hs : l ⬝ᵥ v ≠ 0) (x y : Fin 3 → ℝ) :
    x ⬝ᵥ (M *ᵥ y) = projAnn v l x ⬝ᵥ (M *ᵥ projAnn v l y) + (x ⬝ᵥ v) * (y ⬝ᵥ v) / (l ⬝ᵥ v) := by
  have hx : x = projAnn v l x + ((x ⬝ᵥ v) / (l ⬝ᵥ v)) • l := by simp [projAnn]
  have hy : y = projAnn v l y + ((y ⬝ᵥ v) / (l ⬝ᵥ v)) • l := by simp [projAnn]
  have h1 : projAnn v l x ⬝ᵥ (M *ᵥ l) = 0 := by rw [hl]; exact projAnn_mem v l x hs
  have h2 : l ⬝ᵥ (M *ᵥ projAnn v l y) = 0 := by
    rw [sym_dot M hM, hl]; exact projAnn_mem v l y hs
  have h3 : l ⬝ᵥ (M *ᵥ l) = l ⬝ᵥ v := by rw [hl]
  conv_lhs => rw [hx, hy]
  simp only [add_dotProduct, dotProduct_add, mulVec_add, mulVec_smul, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, h1, h2, h3]
  field_simp
  ring

theorem metricSplit_injective (v : Fin 3 → ℝ) (hv : v ≠ 0) : Function.Injective (metricSplit v hv) := by
  intro G1 G2 h
  have hl : G1.1 *ᵥ v = G2.1 *ᵥ v := congrArg (fun p => p.1.1) h
  have hH : ∀ a b : annV v, (a : Fin 3 → ℝ) ⬝ᵥ (G1.1⁻¹ *ᵥ (b : Fin 3 → ℝ)) =
      (a : Fin 3 → ℝ) ⬝ᵥ (G2.1⁻¹ *ᵥ (b : Fin 3 → ℝ)) := by
    intro a b
    have := congrArg (fun p => p.2.1 a b) h
    simpa [metricSplit, restrictForm] using this
  have hs : (G1.1 *ᵥ v) ⬝ᵥ v ≠ 0 := (pos_dot _ G1.2 v hv).ne'
  have hM : ∀ G : {G : Matrix (Fin 3) (Fin 3) ℝ // G.PosDef}, G.1⁻¹ *ᵥ (G.1 *ᵥ v) = v := by
    intro G
    rw [mulVec_mulVec, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp G.2.isUnit), one_mulVec]
  have hMl : G1.1⁻¹ *ᵥ (G1.1 *ᵥ v) = v := hM G1
  have hMl2 : G2.1⁻¹ *ᵥ (G1.1 *ᵥ v) = v := by rw [hl]; exact hM G2
  have heq : G1.1⁻¹ = G2.1⁻¹ := by
    have key : ∀ x y : Fin 3 → ℝ, x ⬝ᵥ (G1.1⁻¹ *ᵥ y) = x ⬝ᵥ (G2.1⁻¹ *ᵥ y) := by
      intro x y
      rw [decomp _ (pd_symm _ G1.2.inv) v _ hMl hs, decomp _ (pd_symm _ G2.2.inv) v _ hMl2 hs]
      congr 1
      exact hH ⟨_, projAnn_mem v _ x hs⟩ ⟨_, projAnn_mem v _ y hs⟩
    ext i j
    have := key (Pi.single i 1) (Pi.single j 1)
    simpa [Matrix.mulVec_single_one] using this
  apply Subtype.ext
  rw [← Matrix.nonsing_inv_nonsing_inv G1.1 ((Matrix.isUnit_iff_isUnit_det _).mp G1.2.isUnit),
    ← Matrix.nonsing_inv_nonsing_inv G2.1 ((Matrix.isUnit_iff_isUnit_det _).mp G2.2.isUnit), heq]


theorem metricSplit_surjective (v : Fin 3 → ℝ) (hv : v ≠ 0) : Function.Surjective (metricSplit v hv) := by
  rintro ⟨⟨l, hl⟩, ⟨H, hsym, hpos⟩⟩
  have hs : l ⬝ᵥ v ≠ 0 := hl.ne'
  -- the projection onto the plane, as a linear map
  let Pm : Matrix (Fin 3) (Fin 3) ℝ := 1 - (1 / (l ⬝ᵥ v)) • vecMulVec l v
  have hPm : ∀ x, Pm *ᵥ x = projAnn v l x := by
    intro x
    simp only [Pm, projAnn, sub_mulVec, smul_mulVec, vecMulVec_mulVec, one_mulVec]
    ext i; simp [dotProduct_comm x v]; ring
  let πL : (Fin 3 → ℝ) →ₗ[ℝ] annV v :=
    LinearMap.codRestrict (annV v) (Matrix.toLin' Pm) (fun x => by
      show (Pm *ᵥ x) ⬝ᵥ v = 0
      rw [hPm]; exact projAnn_mem v l x hs)
  have hπ : ∀ x, (πL x : Fin 3 → ℝ) = projAnn v l x := fun x => by
    simp [πL, hPm]
  let B : LinearMap.BilinForm ℝ (Fin 3 → ℝ) :=
    H.compl₁₂ πL πL + Matrix.toBilin' ((1 / (l ⬝ᵥ v)) • vecMulVec v v)
  have hB : ∀ x y, B x y = H (πL x) (πL y) + (x ⬝ᵥ v) * (y ⬝ᵥ v) / (l ⬝ᵥ v) := by
    intro x y
    simp only [B, LinearMap.add_apply, LinearMap.compl₁₂_apply, Matrix.toBilin'_apply',
      smul_mulVec, vecMulVec_mulVec, dotProduct_smul]
    simp [dotProduct_comm v y]; ring
  let M := LinearMap.BilinForm.toMatrix' B
  have hM : ∀ x y, x ⬝ᵥ (M *ᵥ y) = B x y := by
    intro x y
    rw [← Matrix.toBilin'_apply' M x y]
    exact congrArg (fun f => f x y) (Matrix.toBilin'_toMatrix' B)
  have hBs : ∀ x y, B x y = B y x := by
    intro x y; rw [hB, hB, hsym, mul_comm (x ⬝ᵥ v)]
  have hMt : Mᵀ = M := by
    ext i j
    have h1 := hM (Pi.single i 1) (Pi.single j 1)
    have h2 := hM (Pi.single j 1) (Pi.single i 1)
    simp [Matrix.mulVec_single_one] at h1 h2
    simp only [Matrix.transpose_apply]
    rw [h1, h2, hBs]
  have hMpd : M.PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
    · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]; exact hMt
    · intro x hx
      simp only [star_trivial]
      rw [hM, hB]
      have h2 : 0 ≤ (x ⬝ᵥ v) * (x ⬝ᵥ v) / (l ⬝ᵥ v) := div_nonneg (mul_self_nonneg _) hl.le
      by_cases hp : πL x = 0
      · have hx0 : x ⬝ᵥ v ≠ 0 := by
          intro h0; apply hx
          have := hπ x
          rw [hp] at this
          simp only [projAnn, h0, zero_div, zero_smul, sub_zero] at this
          simpa using this.symm
        rw [hp]; simp only [map_zero, LinearMap.zero_apply, zero_add]
        exact div_pos (mul_self_pos.mpr hx0) hl
      · have := hpos _ hp
        linarith
  have hMl : M *ᵥ l = v := by
    have : ∀ y, y ⬝ᵥ (M *ᵥ l) = y ⬝ᵥ v := by
      intro y
      have hπl : πL l = 0 := Subtype.ext (by rw [hπ]; simp [projAnn, div_self hs])
      rw [hM, hB, hπl]
      simp only [map_zero, LinearMap.zero_apply, zero_add]
      field_simp
    funext i
    simpa using this (Pi.single i 1)
  have hMu : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det _).mp hMpd.isUnit
  refine ⟨⟨M⁻¹, hMpd.inv⟩, ?_⟩
  have hinv : (M⁻¹)⁻¹ = M := Matrix.nonsing_inv_nonsing_inv M hMu
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · show M⁻¹ *ᵥ v = l
    rw [← hMl, mulVec_mulVec, Matrix.nonsing_inv_mul _ hMu, one_mulVec]
  · show restrictForm v (M⁻¹)⁻¹ = H
    rw [hinv]
    apply LinearMap.ext₂
    intro a b
    show (a : Fin 3 → ℝ) ⬝ᵥ (M *ᵥ (b : Fin 3 → ℝ)) = H a b
    have ha : πL (a : Fin 3 → ℝ) = a := Subtype.ext (by
      rw [hπ]; simp [projAnn, show (a : Fin 3 → ℝ) ⬝ᵥ v = 0 from a.2])
    have hb : πL (b : Fin 3 → ℝ) = b := Subtype.ext (by
      rw [hπ]; simp [projAnn, show (b : Fin 3 → ℝ) ⬝ᵥ v = 0 from b.2])
    rw [hM, hB, ha, hb, show (a : Fin 3 → ℝ) ⬝ᵥ v = 0 from a.2]
    simp

theorem thmFBijection : ThmFBijection := fun v hv =>
  ⟨metricSplit_injective v hv, metricSplit_surjective v hv⟩

theorem anchorCore : AnchorCore := by
  intro V ν c v hν hvV hmax hF hmin l p
  have hnn : 0 < ν ⬝ᵥ ν := lt_of_le_of_ne (dotProduct_self_star_nonneg ν)
    (Ne.symm ((dotProduct_self_eq_zero).not.mpr hν))
  obtain ⟨f, hfV, hf⟩ := hF
  have hcv : ν ⬝ᵥ v ≤ c := hf ▸ hmin f hfV
  have hl0 : 0 ≤ l := div_nonneg (by linarith) hnn.le
  have hp : ν ⬝ᵥ p = c := by
    simp only [p, l, dotProduct_add, dotProduct_smul, smul_eq_mul]; field_simp; ring
  refine ⟨hl0, hp, ?_, ?_⟩
  · intro y hy
    have : p - v = l • ν := by simp [p]
    rw [this, smul_dotProduct, dotProduct_sub, hy, hp]; simp
  · intro u hu huν
    have hu2 : 0 < u ⬝ᵥ u := lt_of_le_of_ne (dotProduct_self_star_nonneg u)
      (Ne.symm ((dotProduct_self_eq_zero).not.mpr hu))
    have hpr : ∀ y, ν ⬝ᵥ (y - ((u ⬝ᵥ y) / (u ⬝ᵥ u)) • u) = ν ⬝ᵥ y := by
      intro y
      rw [dotProduct_sub, dotProduct_smul, dotProduct_comm ν u, huν]; simp
    refine ⟨?_, hpr, ?_, ?_, ?_⟩
    · simp only [p, dotProduct_add, dotProduct_smul, smul_eq_mul, huν]; ring
    · intro x hx; rw [hpr, hpr]; exact hmin x hx
    · intro x hx; rw [hpr]; exact hmax x hx
    · exact ⟨f, hfV, by rw [hpr]; exact hf⟩

theorem ev_lt (ν x y : Fin 3 → ℝ) (h : ν ⬝ᵥ x < ν ⬝ᵥ y) :
    ∀ᶠ δ in nhds (0 : Fin 3 → ℝ), (ν + δ) ⬝ᵥ x < (ν + δ) ⬝ᵥ y := by
  have c1 : Continuous (fun δ : Fin 3 → ℝ => (ν + δ) ⬝ᵥ x) := by simp only [add_dotProduct]; fun_prop
  have c2 : Continuous (fun δ : Fin 3 → ℝ => (ν + δ) ⬝ᵥ y) := by simp only [add_dotProduct]; fun_prop
  have := c1.continuousAt.eventually_lt c2.continuousAt (by rw [add_zero]; exact h)
  exact this

theorem anchorWidth : AnchorWidth := by
  intro V hV ν c v hvV hmax huniq hF
  obtain ⟨f0, hf0m⟩ := id hF
  have hf0 := Finset.mem_filter.mp hf0m
  -- eventually, strict comparisons persist
  have hev : ∀ᶠ δ in nhds (0 : Fin 3 → ℝ),
      (∀ x ∈ V, ν ⬝ᵥ x ≠ c → (ν + δ) ⬝ᵥ x < (ν + δ) ⬝ᵥ f0) ∧
      (∀ x ∈ V, x ≠ v → (ν + δ) ⬝ᵥ v < (ν + δ) ⬝ᵥ x) := by
    rw [Filter.eventually_and]
    constructor
    · rw [Filter.eventually_all_finset]; intro x hx
      by_cases hxc : ν ⬝ᵥ x = c
      · exact Filter.Eventually.of_forall fun _ h => absurd hxc h
      · have hlt : ν ⬝ᵥ x < ν ⬝ᵥ f0 := by
          have := hmax x hx; rw [hf0.2]; exact lt_of_le_of_ne this hxc
        exact (ev_lt ν x f0 hlt).mono fun δ h _ => h
    · rw [Filter.eventually_all_finset]; intro x hx
      by_cases hxv : x = v
      · exact Filter.Eventually.of_forall fun _ h => absurd hxv h
      · exact (ev_lt ν v x (huniq x hx hxv)).mono fun δ h _ => h
  filter_upwards [hev] with δ ⟨h1, h2⟩
  have hv : V.inf' hV (fun x => (ν + δ) ⬝ᵥ x) = (ν + δ) ⬝ᵥ v := by
    apply le_antisymm (Finset.inf'_le _ hvV)
    apply Finset.le_inf'
    intro x hx
    by_cases hxv : x = v
    · rw [hxv]
    · exact (h2 x hx hxv).le
  have hs : V.sup' hV (fun x => (ν + δ) ⬝ᵥ x) =
      (V.filter (fun x => ν ⬝ᵥ x = c)).sup' hF (fun x => (ν + δ) ⬝ᵥ x) := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro x hx
      by_cases hxc : ν ⬝ᵥ x = c
      · exact Finset.le_sup' (fun x => (ν + δ) ⬝ᵥ x) (Finset.mem_filter.mpr ⟨hx, hxc⟩)
      · exact (h1 x hx hxc).le.trans (Finset.le_sup' (fun x => (ν + δ) ⬝ᵥ x) (hf0m))
    · exact Finset.sup'_mono _ (Finset.filter_subset _ _) _
  have hs2 : (V.filter (fun x => ν ⬝ᵥ x = c)).sup' hF (fun x => (ν + δ) ⬝ᵥ x) =
      (V.filter (fun x => ν ⬝ᵥ x = c)).sup' hF (fun x => c + δ ⬝ᵥ x) := by
    apply Finset.sup'_congr _ rfl
    intro x hx
    rw [add_dotProduct, (Finset.mem_filter.mp hx).2]
  have hs3 : (V.filter (fun x => ν ⬝ᵥ x = c)).sup' hF (fun x => c + δ ⬝ᵥ x) =
      c + (V.filter (fun x => ν ⬝ᵥ x = c)).sup' hF (fun x => δ ⬝ᵥ x) := by
    exact (Finset.add_sup' _ _ _ hF).symm
  have hs4 : (V.filter (fun x => ν ⬝ᵥ x = c)).sup' hF (fun x => (x - v) ⬝ᵥ δ) =
      -(δ ⬝ᵥ v) + (V.filter (fun x => ν ⬝ᵥ x = c)).sup' hF (fun x => δ ⬝ᵥ x) := by
    rw [Finset.add_sup' _ _ _ hF]
    apply Finset.sup'_congr _ rfl
    intro x hx
    rw [sub_dotProduct, dotProduct_comm x δ, dotProduct_comm v δ]; ring
  rw [hv, hs, hs2, hs3, hs4, add_dotProduct ν δ v]
  ring

theorem inwardMotionHasSpin : InwardMotionHasSpin := by
  intro ι _ _ x z t g θ h hθ
  subst hθ
  -- a direction n ≠ 0 with n ⬝ g = 0
  obtain ⟨n, hn0, hng⟩ : ∃ n : Fin 2 → ℝ, n ≠ 0 ∧ n ⬝ᵥ g = 0 := by
    by_cases hg : g = 0
    · exact ⟨![1, 0], by intro h; have := congrFun h 0; simp at this, by simp [hg]⟩
    · refine ⟨![-(g 1), g 0], ?_, by simp [dotProduct, Fin.sum_univ_two]; ring⟩
      intro h; apply hg; ext i; fin_cases i
      · have := congrFun h 1; simpa using this
      · have := congrFun h 0; simpa using this
  have hnn : 0 < n ⬝ᵥ n := lt_of_le_of_ne (dotProduct_self_star_nonneg n)
    (Ne.symm ((dotProduct_self_eq_zero).not.mpr hn0))
  have hinw : ∀ i, ∃ ε : ℝ, 0 < ε ∧ x i + ε • (t + z i • g) ∈ interior (convexHull ℝ (Set.range x)) := by
    intro i
    obtain ⟨ε, hε, hpos⟩ := (h i |>.and self_mem_nhdsWithin).exists
    exact ⟨ε, hpos, by simpa using hε⟩
  have key : ∀ (s : ℝ) (i : ι), (∀ j, s * (n ⬝ᵥ x j) ≤ s * (n ⬝ᵥ x i)) → s ≠ 0 →
      s * (n ⬝ᵥ t) < 0 := by
    intro s i hmax hs
    have hsub : convexHull ℝ (Set.range x) ⊆ {y | s * (n ⬝ᵥ y) ≤ s * (n ⬝ᵥ x i)} := by
      apply convexHull_min
      · rintro _ ⟨j, rfl⟩; exact hmax j
      · intro a ha b hb p q hp hq hpq
        simp only [Set.mem_setOf_eq, dotProduct_add, dotProduct_smul, smul_eq_mul] at *
        have e : s * (p * (n ⬝ᵥ a) + q * (n ⬝ᵥ b)) = p * (s * (n ⬝ᵥ a)) + q * (s * (n ⬝ᵥ b)) := by ring
        have e2 : s * (n ⬝ᵥ x i) = (p + q) * (s * (n ⬝ᵥ x i)) := by rw [hpq]; ring
        rw [e]
        nlinarith [mul_le_mul_of_nonneg_left ha hp, mul_le_mul_of_nonneg_left hb hq]
    have hI : ∀ y ∈ interior (convexHull ℝ (Set.range x)), s * (n ⬝ᵥ y) < s * (n ⬝ᵥ x i) := by
      intro y hy
      have hnh : interior (convexHull ℝ (Set.range x)) ∈ nhds y := isOpen_interior.mem_nhds hy
      have hc : Filter.Tendsto (fun δ : ℝ => y + δ • (s • n)) (nhdsWithin 0 (Set.Ioi 0)) (nhds y) := by
        have : Continuous (fun δ : ℝ => y + δ • (s • n)) := by fun_prop
        simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
      obtain ⟨δ, hδ, hδpos⟩ := ((hc.eventually hnh).and self_mem_nhdsWithin).exists
      have := hsub (interior_subset hδ)
      simp only [Set.mem_setOf_eq, dotProduct_add, dotProduct_smul, smul_eq_mul] at this
      have hδ0 : 0 < δ := hδpos
      have hss : 0 < s * s := mul_self_pos.mpr hs
      have : 0 < δ * (s * s * (n ⬝ᵥ n)) := by positivity
      nlinarith
    obtain ⟨ε, hε, hin⟩ := hinw i
    have := hI _ hin
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul] at this
    have e : n ⬝ᵥ (t + z i • g) = n ⬝ᵥ t := by simp [dotProduct_add, dotProduct_smul, hng]
    rw [hng, mul_zero, add_zero] at this
    nlinarith
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => n ⬝ᵥ x j) Finset.univ_nonempty
  obtain ⟨j, -, hj⟩ := Finset.exists_min_image Finset.univ (fun j => n ⬝ᵥ x j) Finset.univ_nonempty
  have k1 := key 1 i (fun l => by simpa using hi l (Finset.mem_univ _)) one_ne_zero
  have k2 := key (-1) j (fun l => by have := hj l (Finset.mem_univ _); linarith) (by norm_num)
  linarith

#print axioms thmFBijection
#print axioms anchorCore
#print axioms anchorWidth
#print axioms inwardMotionHasSpin

end MinimalityExtra
