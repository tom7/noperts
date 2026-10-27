module

public import Minimality.Type16Limit
public import Minimality.MetricBridge
public import Minimality.Type29HDN

@[expose] public section

/-!
# Type 16 with several ties: linear images and the metric bridge (`FEWER-FACES-PROOFS.md` §24.3)

The cover of type 16 (`NF16.cert_nf`) certifies every normal-form shape off the special positions
`genPoly16` and with at most one tie at each segment view and at the two vertex views used by the
route.  A linear image `M ∘ y` of a normal-form shape is a normal-form shape with the same
parameters and the frame `M o, M E_i`, so it is certified as soon as it has no ties at the named
views; and ties are broken by a generic small perturbation of `M`.

* `detMap`, `det3_map`, `planeLine_map`, `view16_map`: the named views are equivariant.
* `NoTies16`, `cert16_nfShape`: a normal-form shape with no ties at the named views is certified.
* `exists_perturb`: a small perturbation of an invertible `M` that breaks finitely many ties.
* `exists_certSeq16_map`: for every `M` with `det ≠ 0`, `M ∘ x` is a pointwise limit of certified
  shapes (**the cover is affine-invariant**).
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### Named views under linear maps -/

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

theorem view16_map_inl (M : ℝ³ →L[ℝ] ℝ³) (y : Fin 7 → ℝ³) (i j : Fin 7) :
    view16 (fun l => M (y l)) (.inl (i, j)) = M (view16 y (.inl (i, j))) := by
  simp [view16]

theorem view16_map_inr (M : ℝ³ →L[ℝ] ℝ³) (y : Fin 7 → ℝ³) (t : Fin 6) :
    view16 (fun l => M (y l)) (.inr t) = detMap M • M (view16 y (.inr t)) :=
  planeLine_map M _ _ _ _ _ _

/-- The named views of a linear image: a multiple `c` of the image of the view, with `c = 1` for
segments and `c = det M` for vertex crossings. -/
theorem view16_map (M : ℝ³ →L[ℝ] ℝ³) (y : Fin 7 → ℝ³) (v : (Fin 7 × Fin 7) ⊕ Fin 6) :
    ∃ c : ℝ, (c = 1 ∨ c = detMap M) ∧ view16 (fun l => M (y l)) v = c • M (view16 y v) := by
  rcases v with ⟨i, j⟩ | t
  · exact ⟨1, Or.inl rfl, by rw [one_smul]; exact view16_map_inl M y i j⟩
  · exact ⟨detMap M, Or.inr rfl, view16_map_inr M y t⟩

/-! ### Shapes without ties are certified -/

/-- No two points of `y` have equal depth along a nonzero named view. -/
def NoTies16 (y : Fin 7 → ℝ³) : Prop :=
  ∀ v a b, a ≠ b → view16 y v ≠ 0 → ⟪y a - y b, view16 y v⟫ ≠ 0

theorem oneTieAt_of_noTies {y : Fin 7 → ℝ³} (h : NoTies16 y) (v : (Fin 7 × Fin 7) ⊕ Fin 6)
    (hv : view16 y v ≠ 0) : OneTieAt (univ.image y) (view16 y v) := by
  intro s hs t ht s' hs' t' ht' hst hst' e1 e2
  obtain ⟨a, -, rfl⟩ := mem_image.mp hs
  obtain ⟨b, -, rfl⟩ := mem_image.mp ht
  have hab : a ≠ b := fun h => hst (by rw [h])
  exact absurd (by rw [inner_sub_left, e1, sub_self]) (h v a b hab hv)

/-- **A normal-form shape without ties at the named views is certified** (`NF16.cert_nf`, whose
tie hypotheses hold vacuously). -/
theorem cert16_nfShape (o E₁ E₂ E₃ : ℝ³) (θ : Fin 7 → ℝ) (hD : det3 E₁ E₂ E₃ ≠ 0)
    (hn : ∀ k, 0 < ineq16 θ k) (hg : MvPolynomial.eval θ genPoly16 ≠ 0)
    (hnt : NoTies16 (nfShape o E₁ E₂ E₃ θ)) : Cert16 (nfShape o E₁ E₂ E₃ θ) := by
  set Nn := NF16.ofParams o E₁ E₂ E₃ θ hD hn with hNn
  rw [eval_genPoly16, mul_ne_zero_iff, mul_ne_zero_iff] at hg
  obtain ⟨⟨g1, g2⟩, g3⟩ := hg
  have G : NF16.Gen Nn := NF16.Gen.ofFactors Nn g1
  have Gσ : NF16.Gen Nn.sigma := NF16.Gen.ofFactors Nn.sigma g2
  have hR : Nn.R1 ≠ 0 ∧ Nn.R2 ≠ 0 := by
    simp only [rFactors, mul_ne_zero_iff] at g3; exact g3
  have hgt : TieSeg (univ.image (nfShape o E₁ E₂ E₃ θ)) := by
    refine ⟨fun v hv w hw hvw => ?_⟩
    obtain ⟨i, -, rfl⟩ := mem_image.mp hv
    obtain ⟨j, -, rfl⟩ := mem_image.mp hw
    exact oneTieAt_of_noTies hnt (.inl (i, j)) (sub_ne_zero.mpr (Ne.symm hvw))
  have W : NF16.Views Nn := by
    refine ⟨fun hne => ?_⟩
    have e := NF16.vtxView16_vA Nn
    have hD' : -Nn.D ≠ 0 := neg_ne_zero.mpr Nn.hD
    have hv1 : view16 (nfShape o E₁ E₂ E₃ θ) (.inr 1) ≠ 0 := by
      show vtxView16 _ 1 ≠ 0
      rw [e]; exact smul_ne_zero hD' hne
    have e2 : Nn.vA = (-Nn.D)⁻¹ • view16 (nfShape o E₁ E₂ E₃ θ) (.inr 1) := by
      show _ = _ • vtxView16 _ 1
      rw [e, smul_smul, inv_mul_cancel₀ hD', one_smul]
    rw [e2]
    exact (oneTieAt_of_noTies hnt (.inr 1) hv1).smul (inv_ne_zero hD')
  have Wσ : NF16.Views Nn.sigma := by
    refine ⟨fun hne => ?_⟩
    have e := NF16.vtxView16_vA Nn.sigma
    rw [vtxView16_sigma] at e
    have hD' : -Nn.sigma.D ≠ 0 := neg_ne_zero.mpr Nn.sigma.hD
    have hv4 : view16 (nfShape o E₁ E₂ E₃ θ) (.inr 4) ≠ 0 := by
      show vtxView16 _ 4 ≠ 0
      rw [show (4 : Fin 6) = 1 + 3 from rfl, e]; exact smul_ne_zero hD' hne
    have e2 : Nn.sigma.vA = (-Nn.sigma.D)⁻¹ • view16 (nfShape o E₁ E₂ E₃ θ) (.inr 4) := by
      show _ = _ • vtxView16 _ 4
      rw [show (4 : Fin 6) = 1 + 3 from rfl, e, smul_smul, inv_mul_cancel₀ hD', one_smul]
    rw [e2, image_sigma16]
    exact (oneTieAt_of_noTies hnt (.inr 4) hv4).smul (inv_ne_zero hD')
  exact NF16.cert_nf Nn G Gσ W Wσ hR.1 hR.2 hgt

/-! ### Breaking ties by a small linear perturbation -/

/-- **A direction that breaks finitely many ties**: for finitely many pairs of nonzero vectors
`a i, b i` there is a linear map `S` such that `(1 + tS) a i` and `(1 + tS) b i` are not
orthogonal, for all small `t > 0`.  (The derivative of `⟪(1+tS)a, (1+tS)b⟫` at `t = 0` is
`⟪S a, b⟫ + ⟪a, S b⟫`, nonzero for `S x = ⟪a, x⟫ b + ⟪b, x⟫ a`, and a common `S` for finitely many
pairs avoids finitely many hyperplanes.) -/
theorem exists_noTie_dir {ι : Type} [Finite ι] (a b : ι → ℝ³) (ha : ∀ i, a i ≠ 0)
    (hb : ∀ i, b i ≠ 0) :
    ∃ S : ℝ³ →L[ℝ] ℝ³, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, ⟪a i + t • S (a i), b i + t • S (b i)⟫ ≠ 0 := by
  let ℓ : ι → (ℝ³ →L[ℝ] ℝ³) →ₗ[ℝ] ℝ := fun i =>
    { toFun := fun S => ⟪S (a i), b i⟫ + ⟪a i, S (b i)⟫
      map_add' := fun S T => by
        simp only [add_apply, inner_add_left, inner_add_right]; ring
      map_smul' := fun c S => by
        simp only [smul_apply, real_inner_smul_left, real_inner_smul_right,
          RingHom.id_apply, smul_eq_mul]; ring }
  have hℓ : ∀ i, ℓ i ≠ 0 := by
    intro i h0
    let S : ℝ³ →L[ℝ] ℝ³ := (innerSL ℝ (a i)).smulRight (b i) + (innerSL ℝ (b i)).smulRight (a i)
    have h1 := LinearMap.congr_fun h0 S
    have hS : ∀ x, S x = ⟪a i, x⟫ • b i + ⟪b i, x⟫ • a i := by
      intro x
      simp [S]
    simp only [ℓ, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply, hS, inner_add_left,
      inner_add_right, real_inner_smul_left, real_inner_smul_right] at h1
    have e1 := real_inner_self_nonneg (x := a i)
    have e2 := real_inner_self_nonneg (x := b i)
    have p1 : 0 < ⟪a i, a i⟫ := real_inner_self_pos.mpr (ha i)
    have p2 : 0 < ⟪b i, b i⟫ := real_inner_self_pos.mpr (hb i)
    rw [real_inner_comm (b i) (a i)] at h1
    nlinarith [mul_pos p1 p2, sq_nonneg ⟪a i, b i⟫]
  obtain ⟨S, -, hS⟩ := exists_avoid_kernels ℓ hℓ (O := Set.univ) isOpen_univ ⟨0, trivial⟩
  refine ⟨S, ?_⟩
  refine eventually_all.2 fun i => ?_
  have hq := eventually_pos_mul_quad (A := ⟪a i, b i⟫) (B := ℓ i S) (C := ⟪S (a i), S (b i)⟫)
    (fun _ => hS i)
  filter_upwards [hq] with t ht h0
  have e : ⟪a i + t • S (a i), b i + t • S (b i)⟫ =
      ⟪a i, b i⟫ + t * ℓ i S + t ^ 2 * ⟪S (a i), S (b i)⟫ := by
    simp only [ℓ, LinearMap.coe_mk, AddHom.coe_mk, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right]
    ring
  rw [e] at h0
  rw [h0, zero_mul] at ht
  exact lt_irrefl _ ht

theorem map_nfP (M : ℝ³ →L[ℝ] ℝ³) (o E₁ E₂ E₃ : ℝ³) (α β γ : ℝ) :
    M (nfP o E₁ E₂ E₃ α β γ) = nfP (M o) (M E₁) (M E₂) (M E₃) α β γ := by
  simp only [nfP, map_add, map_smul]

theorem map_nfShape (M : ℝ³ →L[ℝ] ℝ³) (o E₁ E₂ E₃ : ℝ³) (θ : Fin 7 → ℝ) :
    (fun i => M (nfShape o E₁ E₂ E₃ θ i)) = nfShape (M o) (M E₁) (M E₂) (M E₃) θ := by
  funext i; fin_cases i <;> exact map_nfP M o E₁ E₂ E₃ _ _ _

/-- **The cover is affine-invariant** (bridge input for type 16): for an invertible linear map
`M`, the shape `M ∘ x` of a normal form `N` is a pointwise limit of certified shapes.  The shapes
are `((1 + t S) M) ∘ y_s`, where `y_s` are normal-form shapes off the special positions of the
cover with parameters `θ_s → θ₀`, and `t S` is a small generic perturbation of the metric that
leaves no tie at the named views. -/
theorem exists_certSeq16_map {x : Fin 7 → ℝ³} (N : NF16 x) (M : ℝ³ →L[ℝ] ℝ³)
    (hMinj : ∀ a, M a = 0 → a = 0) (hD : det3 (M N.E₁) (M N.E₂) (M N.E₃) ≠ 0) :
    ∃ Y : ℕ → Fin 7 → ℝ³, (∀ i, Tendsto (fun s => Y s i) atTop (𝓝 (M (x i)))) ∧
      ∀ᶠ s in atTop, Cert16 (Y s) := by
  classical
  set θ₀ : Fin 7 → ℝ := ![N.a, N.b, N.g, N.d, N.p, N.q, N.r] with hθ₀
  have hx : x = nfShape N.o N.E₁ N.E₂ N.E₃ θ₀ := N.eq_nfShape
  obtain ⟨θs, hθs, hgen⟩ := exists_seq_eval_ne_zero genPoly16_ne_zero θ₀
  set Y0 : ℕ → Fin 7 → ℝ³ := fun s => nfShape N.o N.E₁ N.E₂ N.E₃ (θs s) with hY0
  have hY0t : ∀ i, Tendsto (fun s => Y0 s i) atTop (𝓝 (x i)) := by
    intro m
    have := tendsto_nfShape (o := fun _ : ℕ => N.o) (E₁ := fun _ => N.E₁) (E₂ := fun _ => N.E₂)
      (E₃ := fun _ => N.E₃) tendsto_const_nhds tendsto_const_nhds tendsto_const_nhds
      tendsto_const_nhds hθs m
    rw [hx]; exact this
  have hineq : ∀ᶠ s in atTop, ∀ k, 0 < ineq16 (θs s) k :=
    eventually_all.mpr fun k =>
      (((continuous_ineq16 k).tendsto θ₀).comp hθs).eventually (lt_mem_nhds (N.ineq k))
  -- the perturbations
  have key : ∀ s : ℕ, ∃ (S : ℝ³ →L[ℝ] ℝ³) (t : ℝ), 0 < t ∧ t * ‖S‖ < 1 / ((s : ℝ) + 1) ∧
      ((∀ k, 0 < ineq16 (θs s) k) →
        Cert16 (fun i => ((ContinuousLinearMap.id ℝ ℝ³ + t • S).comp M) (Y0 s i))) := by
    intro s
    have hs0 : (0 : ℝ) < 1 / ((s : ℝ) + 1) := by positivity
    by_cases hn : ∀ k, 0 < ineq16 (θs s) k
    · have hinj : Function.Injective (Y0 s) := (NF16.ofParams N.o N.E₁ N.E₂ N.E₃ (θs s) N.hD hn).inj
      let ι := {p : ((Fin 7 × Fin 7) ⊕ Fin 6) × Fin 7 × Fin 7 //
        p.2.1 ≠ p.2.2 ∧ view16 (Y0 s) p.1 ≠ 0}
      have ha : ∀ p : ι, M (Y0 s p.1.2.1 - Y0 s p.1.2.2) ≠ 0 := fun p h =>
        sub_ne_zero.mpr (hinj.ne p.2.1) (hMinj _ h)
      have hb : ∀ p : ι, M (view16 (Y0 s) p.1.1) ≠ 0 := fun p h => p.2.2 (hMinj _ h)
      obtain ⟨S, hS⟩ := exists_noTie_dir (fun p : ι => M (Y0 s p.1.2.1 - Y0 s p.1.2.2))
        (fun p : ι => M (view16 (Y0 s) p.1.1)) ha hb
      -- the determinant condition and the size of the perturbation for small `t`
      have hdet : ∀ᶠ t in 𝓝[>] (0 : ℝ),
          det3 (((ContinuousLinearMap.id ℝ ℝ³ + t • S).comp M) N.E₁)
            (((ContinuousLinearMap.id ℝ ℝ³ + t • S).comp M) N.E₂)
            (((ContinuousLinearMap.id ℝ ℝ³ + t • S).comp M) N.E₃) ≠ 0 := by
        have hT : ∀ v : ℝ³, Tendsto (fun t : ℝ => M v + t • S (M v)) (𝓝 0) (𝓝 (M v)) := by
          intro v
          have : Continuous fun t : ℝ => M v + t • S (M v) := by fun_prop
          simpa using this.tendsto 0
        have := Tendsto.det3' (hT N.E₁) (hT N.E₂) (hT N.E₃)
        exact ((this.eventually_ne hD).filter_mono nhdsWithin_le_nhds).mono fun t ht => by
          simpa using ht
      have hsz : ∀ᶠ t in 𝓝[>] (0 : ℝ), t * ‖S‖ < 1 / ((s : ℝ) + 1) := by
        have hc : Continuous fun t : ℝ => t * ‖S‖ := by fun_prop
        exact (hc.continuousAt.eventually (gt_mem_nhds (by simpa using hs0))).filter_mono
          nhdsWithin_le_nhds
      have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), (0 : ℝ) < t := self_mem_nhdsWithin
      obtain ⟨t, ht0, htd, hts, htS⟩ := (hpos.and (hdet.and (hsz.and hS))).exists
      refine ⟨S, t, ht0, hts, fun _ => ?_⟩
      set Nt : ℝ³ →L[ℝ] ℝ³ := (ContinuousLinearMap.id ℝ ℝ³ + t • S).comp M with hNt
      have hNtv : ∀ v, Nt v = M v + t • S (M v) := fun v => by simp [hNt]
      rw [show (fun i => Nt (Y0 s i)) = nfShape (Nt N.o) (Nt N.E₁) (Nt N.E₂) (Nt N.E₃) (θs s) from
        map_nfShape Nt N.o N.E₁ N.E₂ N.E₃ (θs s)]
      refine cert16_nfShape _ _ _ _ _ htd hn (hgen s) ?_
      rw [← map_nfShape Nt N.o N.E₁ N.E₂ N.E₃ (θs s)]
      intro v a b hab hv
      obtain ⟨c, -, hc⟩ := view16_map Nt (Y0 s) v
      rw [hc] at hv ⊢
      have hc0 : c ≠ 0 := left_ne_zero_of_smul hv
      have hv0 : view16 (Y0 s) v ≠ 0 := fun h => hv (by rw [h, map_zero, smul_zero])
      have := htS ⟨(v, a, b), hab, hv0⟩
      have e1 : Nt (Y0 s a) - Nt (Y0 s b) =
          M (Y0 s a - Y0 s b) + t • S (M (Y0 s a - Y0 s b)) := by
        rw [← map_sub, hNtv]
      rw [real_inner_smul_right, e1, hNtv (view16 (Y0 s) v)]
      exact mul_ne_zero hc0 this
    · exact ⟨0, 1, one_pos, by simpa using hs0, fun h => absurd h hn⟩
  choose S t ht0 hts hcert using key
  refine ⟨fun s i => ((ContinuousLinearMap.id ℝ ℝ³ + t s • S s).comp M) (Y0 s i), fun i => ?_,
    hineq.mono fun s hs => hcert s hs⟩
  have h1 : Tendsto (fun s => M (Y0 s i)) atTop (𝓝 (M (x i))) :=
    (M.continuous.tendsto _).comp (hY0t i)
  have h2 : Tendsto (fun s => t s • S s (M (Y0 s i))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hb : Tendsto (fun s : ℕ => 1 / ((s : ℝ) + 1) * ‖M (Y0 s i)‖) atTop (𝓝 (0 * ‖M (x i)‖)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.mul (h1.norm)
    rw [zero_mul] at hb
    refine squeeze_zero (fun s => norm_nonneg _) (fun s => ?_) hb
    calc ‖t s • S s (M (Y0 s i))‖ = t s * ‖S s (M (Y0 s i))‖ := by
          rw [norm_smul, Real.norm_of_nonneg (ht0 s).le]
      _ ≤ t s * (‖S s‖ * ‖M (Y0 s i)‖) :=
          mul_le_mul_of_nonneg_left ((S s).le_opNorm _) (ht0 s).le
      _ = (t s * ‖S s‖) * ‖M (Y0 s i)‖ := by ring
      _ ≤ 1 / ((s : ℝ) + 1) * ‖M (Y0 s i)‖ :=
          mul_le_mul_of_nonneg_right (hts s).le (norm_nonneg _)
  have := h1.add h2
  rw [add_zero] at this
  simpa using this

/-! ### The certificates of type 16 as a finite family -/

/-- The labelled rims of the cover: three, four or five corners. -/
abbrev Rim16 : Type := (ZMod 3 → Fin 7) ⊕ (ZMod 4 → Fin 7) ⊕ (ZMod 5 → Fin 7)

/-- A labelled certificate index: a named view, a sign, and a labelled rim (`CertL16`). -/
abbrev Q16 : Type := ((Fin 7 × Fin 7) ⊕ Fin 6) × Bool × Rim16

/-- The corner count and labels of a rim. -/
def Lab16 : Rim16 → (k : ℕ) × (ZMod k → Fin 7)
  | .inl l => ⟨3, l⟩
  | .inr (.inl l) => ⟨4, l⟩
  | .inr (.inr l) => ⟨5, l⟩

/-- The number of corners of the rim of `q`. -/
def Q16.K (q : Q16) : ℕ := (Lab16 q.2.2).1

/-- The labels of the rim of `q`. -/
def Q16.lab (q : Q16) : ZMod q.K → Fin 7 := (Lab16 q.2.2).2

/-- The view of `q` as a function of the shape. -/
noncomputable def Q16.vw (q : Q16) (y : Fin 7 → ℝ³) : ℝ³ := sgnB q.2.1 • view16 y q.1

theorem Q16.K_three (q : Q16) : 3 ≤ q.K := by
  rcases q with ⟨v, e, L | L | L⟩ <;> simp [Q16.K, Lab16]

instance (q : Q16) : NeZero q.K :=
  ⟨by have := q.K_three; omega⟩

theorem certL16_iff (y : Fin 7 → ℝ³) (q : Q16) :
    CertL16 y q.1 q.2.1 q.2.2 ↔ RimCertAt y (q.vw y) q.lab := by
  rcases q with ⟨v, e, L | L | L⟩ <;> exact Iff.rfl

theorem Q16.vw_eq_zero {x : Fin 7 → ℝ³} (T : Type16 x) (q : Q16) (h : q.vw x = 0) (y : Fin 7 → ℝ³) :
    q.vw y = 0 := by
  rcases q with ⟨v, e, L⟩
  have hs := sgnB_ne_zero e
  simp only [Q16.vw] at h ⊢
  have h0 : view16 x v = 0 := by
    rcases smul_eq_zero.mp h with h1 | h1
    · exact absurd h1 hs
    · exact h1
  rcases v with ⟨i, j⟩ | t
  · by_cases hij : i = j
    · subst hij; simp [view16]
    · exact absurd h0 (T.view16_ne_zero (.inl (i, j)) (fun l e' => hij (by
        simp only [Sum.inl.injEq, Prod.mk.injEq] at e'; rw [e'.1, e'.2])))
  · exact absurd h0 (T.view16_ne_zero (.inr t) (fun l e' => by cases e'))

/-! ### Rotations and reflections of a rim -/

/-- Robust unimodality of the rotated or reflected sequence gives that of the original. -/
theorem robust_of_equiv {k : ℕ} [NeZero k] (a b : ZMod k → ℝ) (r : ℤ)
    (h : (∀ n : ℤ, a (n : ZMod k) = b ((n + r : ℤ) : ZMod k)) ∨
      (∀ n : ℤ, a (n : ZMod k) = b ((r - n : ℤ) : ZMod k)))
    (hb : IsRobustUnimodal a) : IsRobustUnimodal b := by
  have key : ∀ i : ZMod k, ((ZMod.cast i : ℤ) : ZMod k) = i := fun i => ZMod.intCast_zmod_cast i
  rcases h with h | h
  · have hr := hb.rot (((-r : ℤ)) : ZMod k)
    convert hr using 1
    funext i
    have h1 := h (ZMod.cast (i + ((-r : ℤ) : ZMod k)) : ℤ)
    rw [key] at h1
    push_cast at h1 ⊢
    rw [h1]
    congr 1
    ring
  · have hr := hb.reflect.rot (((-r : ℤ)) : ZMod k)
    convert hr using 1
    funext i
    have h1 := h (ZMod.cast (-(i + ((-r : ℤ) : ZMod k))) : ℤ)
    rw [key] at h1
    push_cast at h1 ⊢
    rw [h1]
    congr 1
    ring

theorem robust_mul_ne_zero {k : ℕ} {z : ZMod k → ℝ} (hz : IsRobustUnimodal z) {c : ℝ}
    (hc : c ≠ 0) : IsRobustUnimodal (fun i => c * z i) := by
  rcases lt_or_gt_of_ne hc with h | h
  · have := (hz.smul (neg_pos.mpr h)).neg
    convert this using 2 with i
    ring
  · exact hz.smul h

/-- The relation between a labelled rim and a rotation or reflection of another, on depths. -/
theorem equiv_aux {k : ℕ} [NeZero k] (a b : ZMod k → ℝ) (r : ℤ) (lam : ℝ) (hlam : lam ≠ 0)
    (h : (∀ n : ℤ, a (n : ZMod k) = lam * b ((n + r : ℤ) : ZMod k)) ∨
      (∀ n : ℤ, a (n : ZMod k) = lam * b ((r - n : ℤ) : ZMod k))) :
    (Function.Injective b → Function.Injective a) ∧
      (IsRobustUnimodal a → IsRobustUnimodal b) := by
  have key : ∀ i : ZMod k, ((ZMod.cast i : ℤ) : ZMod k) = i := fun i => ZMod.intCast_zmod_cast i
  have hshift : ∀ i : ZMod k, ∃ n : ℤ, (n : ZMod k) = i := fun i => ⟨ZMod.cast i, key i⟩
  constructor
  · intro hb i j hij
    obtain ⟨n, rfl⟩ := hshift i
    obtain ⟨m, rfl⟩ := hshift j
    rcases h with h | h
    · rw [h, h] at hij
      have := hb (mul_left_cancel₀ hlam hij)
      push_cast at this
      have : (n : ZMod k) = m := by simpa using this
      exact this
    · rw [h, h] at hij
      have := hb (mul_left_cancel₀ hlam hij)
      push_cast at this
      have : (n : ZMod k) = m := by simpa using this
      exact this
  · intro ha
    have ha' : IsRobustUnimodal (fun i => lam⁻¹ * a i) := robust_mul_ne_zero ha (inv_ne_zero hlam)
    refine robust_of_equiv (fun i => lam⁻¹ * a i) b r ?_ ha'
    rcases h with h | h
    · left; intro n; simp only [h, ← mul_assoc, inv_mul_cancel₀ hlam, one_mul]
    · right; intro n; simp only [h, ← mul_assoc, inv_mul_cancel₀ hlam, one_mul]

/-- The certificate `q` has a rim that is a rotation or reflection of the rim `lab₁`, at a
multiple of the view `u₁`. -/
def RimMatch16 (x : Fin 7 → ℝ³) (u₁ : ℝ³) {k₁ : ℕ} (lab₁ : ZMod k₁ → Fin 7) (q : Q16) : Prop :=
  (∃ lam : ℝ, lam ≠ 0 ∧ q.vw x = lam • u₁) ∧ q.K = k₁ ∧ ∃ r : ℤ,
    (∀ n : ℤ, q.lab (n : ZMod q.K) = lab₁ ((n + r : ℤ) : ZMod k₁)) ∨
    (∀ n : ℤ, q.lab (n : ZMod q.K) = lab₁ ((r - n : ℤ) : ZMod k₁))

theorem RimMatch16.pair {x : Fin 7 → ℝ³} {u₁ : ℝ³} {k₁ : ℕ} [NeZero k₁] {lab₁ : ZMod k₁ → Fin 7}
    {q : Q16} (h : RimMatch16 x u₁ lab₁ q) :
    ∃ lam : ℝ, q.vw x = lam • u₁ ∧ ∀ w : ℝ³,
      (Function.Injective (fun i => ⟪x (lab₁ i), w⟫) →
        Function.Injective (fun i => ⟪x (q.lab i), lam • w⟫)) ∧
      (IsRobustUnimodal (fun i => ⟪x (q.lab i), lam • w⟫) →
        IsRobustUnimodal (fun i => ⟪x (lab₁ i), w⟫)) := by
  obtain ⟨⟨lam, hlam, hv⟩, hk, r, hr⟩ := h
  refine ⟨lam, hv, ?_⟩
  subst hk
  intro w
  refine equiv_aux (fun i => ⟪x (q.lab i), lam • w⟫) (fun i => ⟪x (lab₁ i), w⟫) r lam hlam ?_
  rcases hr with h | h
  · left; intro n; simp only [h, real_inner_smul_right]
  · right; intro n; simp only [h, real_inner_smul_right]

/-! ### Two views with ties -/

/-- **Two tilt tests at certificates of the cover** (Theorem 24.3 for type 16).  `q₁, q₂` are
labelled certificate indices (a named view, a sign, a labelled rim of 3, 4 or 5 corners) whose
rims `x ∘ q.lab` at the views `q.vw x` are tilt tests (`TiltTest`: the silhouette at the tilted
views is a cyclic subsequence of the rim, for a nonempty open cone `Θ` of tilts), the views are
not proportional, and the cones are compatible (`compat_of_signs`) if the views are orthogonal.
Every other certificate of the cover that survives in the limit (`WeakRim`: distinct labels, all
points weakly left of its polygon, labels weakly counterclockwise) has no horizontal double normal
at its limit view and distinct depths of its labels.  Rotations and reflections of the two rims at
the same views belong to the tests. -/
def TwoView16 (x : Fin 7 → ℝ³) : Prop :=
  ∃ (q₁ q₂ : Q16) (Θ₁ Θ₂ : Set ℝ³) (k₁ k₂ : ℕ) (_ : NeZero k₁) (_ : NeZero k₂)
    (σ₁ : ZMod k₁ → ZMod q₁.K) (σ₂ : ZMod k₂ → ZMod q₂.K),
    TiltTest (univ.image x) (q₁.vw x) (fun i => x (q₁.lab i)) σ₁ Θ₁ ∧
    TiltTest (univ.image x) (q₂.vw x) (fun i => x (q₂.lab i)) σ₂ Θ₂ ∧
    (∀ t : ℝ, q₂.vw x ≠ t • q₁.vw x) ∧
    (⟪q₁.vw x, q₂.vw x⟫ = 0 → ∃ d ∈ Θ₁, ∃ d' ∈ Θ₂, ⟪q₂.vw x, d⟫ = ⟪q₁.vw x, d'⟫) ∧
    ∀ q : Q16, ¬ RimMatch16 x (q₁.vw x) q₁.lab q → ¬ RimMatch16 x (q₂.vw x) q₂.lab q →
      q.vw x ≠ 0 → Function.Injective q.lab → WeakRim x (q.vw x) q.lab →
        NoHDNAt (univ.image x) (q.vw x) ∧
          ∀ i j, q.lab i ≠ q.lab j → ⟪x (q.lab i) - x (q.lab j), q.vw x⟫ ≠ 0

/-- The curve of linear maps `M ε = I + (ε/2) H` and its metric `Gm ε = M ε ∘ M ε`. -/
theorem curve_inner (H : ℝ³ →L[ℝ] ℝ³) (hH : (H : ℝ³ →ₗ[ℝ] ℝ³).IsSymmetric) (ε : ℝ)
    (a b : ℝ³) :
    ⟪a + (ε / 2) • H a, b + (ε / 2) • H b⟫ =
      ⟪a, (b + (ε / 2) • H b) + (ε / 2) • H (b + (ε / 2) • H b)⟫ := by
  have h1 : ⟪H a, b⟫ = ⟪a, H b⟫ := hH a b
  have h2 : ⟪H a, H b⟫ = ⟪a, H (H b)⟫ := hH a (H b)
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, map_add,
    map_smul, h1, h2]
  ring

theorem detMap_one : detMap (ContinuousLinearMap.id ℝ ℝ³) = 1 := by
  simp [detMap, det3_expand]

/-- **Type 16 with two ties at two certificates** (Theorem 24.3 with the cover, the bridge
`metricFree_of_cover`).  A type-16 shape with `TwoView16` is Rupert: the two tilt tests are
metric-free along the curve `I + (ε/2) H` because the cover is affine-invariant
(`exists_certSeq16_map`), or else the limit lemma makes the shape Rupert directly. -/
theorem isRupert_type16_twoView {x : Fin 7 → ℝ³} (T : Type16 x) (P : TwoView16 x) :
    IsRupert (univ.image x) := by
  classical
  obtain ⟨q₁, q₂, Θ, Θ', k₁, k₂, i₁, i₂, σ, σ', T1, T2, hind, hcompat, hO⟩ := P
  set u : ℝ³ := q₁.vw x with hu
  set u' : ℝ³ := q₂.vw x with hu'
  set X : ZMod q₁.K → ℝ³ := fun i => x (q₁.lab i) with hX
  set X' : ZMod q₂.K → ℝ³ := fun i => x (q₂.lab i) with hX'
  obtain ⟨d, hdΘ, d', hdΘ', hcoup, hg, hg'⟩ := exists_good_pair T1 T2 hcompat
  set c : ℝ := (⟪u, d'⟫ - ⟪u', d⟫) / ⟪u, u'⟫ with hc
  have hrel : ⟪d, u'⟫ + c * ⟪u, u'⟫ = ⟪u, d'⟫ := by
    by_cases ho : ⟪u, u'⟫ = 0
    · rw [real_inner_comm, hcoup ho, ho]; ring
    · rw [hc]; field_simp; rw [real_inner_comm]; ring
  have hgood : GoodTilt X u (d + c • u) := by
    intro i j hij hti
    have := hg i j hij hti
    simp only [inner_add_right, real_inner_smul_right, hti, mul_zero, add_zero]
    exact this
  obtain ⟨H, hsymm, hHu, hHu'⟩ := exists_symm_clm (A := d + c • u) (B := d') T1.ne_zero hind (by
    simp only [inner_add_right, real_inner_smul_right]
    rw [← real_inner_comm d u'] at hrel
    rw [real_inner_comm u u']
    linarith)
  -- the curve of metrics
  set M : ℝ → ℝ³ →L[ℝ] ℝ³ := fun ε => ContinuousLinearMap.id ℝ ℝ³ + (ε / 2) • H with hM
  set Gm : ℝ → ℝ³ →L[ℝ] ℝ³ := fun ε => (M ε).comp (M ε) with hGm
  have hMv : ∀ ε v, M ε v = v + (ε / 2) • H v := fun ε v => by simp [hM]
  have hGv : ∀ ε v, Gm ε v = M ε (M ε v) := fun ε v => rfl
  have hMG : ∀ ε a b, ⟪M ε a, M ε b⟫ = ⟪a, Gm ε b⟫ := by
    intro ε a b
    rw [hMv, hMv, hGv, hMv, hMv]
    exact curve_inner H hsymm ε a b
  have hMt : ∀ v : ℝ³, Tendsto (fun ε => M ε v) (𝓝[>] (0 : ℝ)) (𝓝 v) := by
    intro v
    have hc' : Continuous fun ε : ℝ => v + (ε / 2) • H v := by fun_prop
    simpa [hMv] using hc'.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)))
  have hdetpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < detMap (M ε) := by
    have h := Tendsto.det3' (hMt (EuclideanSpace.single 0 1)) (hMt (EuclideanSpace.single 1 1))
      (hMt (EuclideanSpace.single 2 1))
    have h1 : det3 (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))
        (EuclideanSpace.single (1 : Fin 3) (1 : ℝ)) (EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
        = 1 := detMap_one
    rw [h1] at h
    exact h.eventually (lt_mem_nhds one_pos)
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε / 2 * ‖H‖ < 1 := by
    have hc' : Continuous fun ε : ℝ => ε / 2 * ‖H‖ := by fun_prop
    exact (hc'.continuousAt.eventually (gt_mem_nhds (by simp))).filter_mono nhdsWithin_le_nhds
  have hMinj : ∀ ε, ε / 2 * ‖H‖ < 1 → 0 < ε → ∀ a, M ε a = 0 → a = 0 := by
    intro ε hε hε0 a ha
    rw [hMv] at ha
    have e : a = -((ε / 2) • H a) := eq_neg_of_add_eq_zero_left ha
    have h1 : ‖a‖ ≤ ε / 2 * ‖H‖ * ‖a‖ := by
      calc ‖a‖ = ‖(ε / 2) • H a‖ := by
            have := congrArg norm e
            rwa [norm_neg] at this
        _ = ε / 2 * ‖H a‖ := by rw [norm_smul, Real.norm_of_nonneg (by positivity)]
        _ ≤ ε / 2 * (‖H‖ * ‖a‖) := mul_le_mul_of_nonneg_left (H.le_opNorm a) (by positivity)
        _ = ε / 2 * ‖H‖ * ‖a‖ := by ring
    have : ‖a‖ = 0 := by nlinarith [norm_nonneg a]
    exact norm_eq_zero.mp this
  -- the generic bridge
  have hmain := metricFree_of_cover x T.noSeg ⟨3, 0, 5, 6, T.det_ne⟩ (Q := Q16) Q16.K Q16.lab
    Q16.vw (fun q h y => Q16.vw_eq_zero T q h y)
    (fun q z ι l xs h => (tendsto_view16 h q.1).const_smul _) M Gm hMG (fun i => hMt (x i))
    (by
      have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (0 : ℝ) < ε := self_mem_nhdsWithin
      filter_upwards [hdetpos, hsmall, hpos] with ε hd hs hε0
      obtain ⟨Y, hY, hc'⟩ := exists_certSeq16_map T.toNF (M ε) (hMinj ε hs hε0) (by
        rw [det3_map]; exact mul_ne_zero hd.ne' T.toNF.hD)
      refine ⟨Y, hY, (hc'.frequently).mono fun s hs' => ?_⟩
      obtain ⟨v, e, L, hL⟩ := hs'.exists_certL
      exact ⟨(v, e, L), (certL16_iff (Y s) (v, e, L)).1 hL⟩)
    (by
      filter_upwards [hdetpos] with ε hd q
      obtain ⟨c0, hc0, hv⟩ := view16_map (M ε) x q.1
      have hc0' : 0 < c0 := by
        rcases hc0 with rfl | rfl
        · exact one_pos
        · exact hd
      refine ⟨c0, hc0', ?_⟩
      simp only [Q16.vw, hv, map_smul, smul_comm (sgnB q.2.1) c0])
    (k₁ := q₁.K) (k₂ := q₂.K) q₁.K_three q₂.K_three X X' u u' (fun ε => u + ε • (d + c • u))
    (fun ε => u' + ε • d') (RimMatch16 x u q₁.lab) (RimMatch16 x u' q₂.lab)
    (fun q h => h.pair) (fun q h => h.pair)
    (by
      have hGu : ∀ ε, Gm ε u = u + ε • (d + c • u) + ε ^ 2 • ((1 / 4 : ℝ) • H (d + c • u)) := by
        intro ε
        rw [hGv, hMv, hMv, map_add, map_smul, hHu]
        module
      simp only [hGu]
      exact eventually_order_tilt X u (d + c • u) ((1 / 4 : ℝ) • H (d + c • u)) hgood)
    (by
      have hGu : ∀ ε, Gm ε u' = u' + ε • d' + ε ^ 2 • ((1 / 4 : ℝ) • H d') := by
        intro ε
        rw [hGv, hMv, hMv, map_add, map_smul, hHu']
        module
      simp only [hGu]
      exact eventually_order_tilt X' u' d' ((1 / 4 : ℝ) • H d') hg')
    hO
  rcases hmain with hR | hMF
  · exact hR
  have hall := hMF.and ((eventually_injective_depth hgood).and (eventually_injective_depth hg'))
  have hall' : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      IsCyclicUnimodal (fun i => ⟪X i, u + ε • (d + c • u)⟫) ∨
        IsCyclicUnimodal (fun i => ⟪X' i, u' + ε • d'⟫) :=
    hall.mono fun _ ⟨h1, h2, h3⟩ => h1 h2 h3
  rcases frequently_or_distrib.mp hall'.frequently with h | h
  · exact T1.isRupert_of_freq hdΘ (frequently_unimodal_tilt X u d c h)
  · exact T2.isRupert_of_freq hdΘ' h

/-- **Theorem 24.3 for type 16 from the facets**: seven points labelled so that `0235`, `1356`
(quadrilaterals), `024`, `036`, `046`, `145`, `146`, `245` are facets (functionals negative off
them) with `TwoView16` are Rupert. -/
theorem isRupert_type16_twoView_facets (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (fA fB fC fD fE fF fG fH : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 2, 3, 5} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 2, 3, 5} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({1, 3, 5, 6} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({1, 3, 5, 6} : Finset (Fin 7)) → fB (x i) < 0))
    (hC : ∀ i, (i ∈ ({0, 2, 4} : Finset (Fin 7)) → fC (x i) = 0) ∧
      (i ∉ ({0, 2, 4} : Finset (Fin 7)) → fC (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 3, 6} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 3, 6} : Finset (Fin 7)) → fD (x i) < 0))
    (hE : ∀ i, (i ∈ ({0, 4, 6} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({0, 4, 6} : Finset (Fin 7)) → fE (x i) < 0))
    (hF : ∀ i, (i ∈ ({1, 4, 5} : Finset (Fin 7)) → fF (x i) = 0) ∧
      (i ∉ ({1, 4, 5} : Finset (Fin 7)) → fF (x i) < 0))
    (hG : ∀ i, (i ∈ ({1, 4, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({1, 4, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hH : ∀ i, (i ∈ ({2, 4, 5} : Finset (Fin 7)) → fH (x i) = 0) ∧
      (i ∉ ({2, 4, 5} : Finset (Fin 7)) → fH (x i) < 0))
    (P : TwoView16 x) : IsRupert (univ.image x) :=
  isRupert_type16_twoView ⟨hx, Face16.ofAffine fA hA, Face16.ofAffine fB hB,
    Face16.ofAffine fC hC, Face16.ofAffine fD hD, Face16.ofAffine fE hE, Face16.ofAffine fF hF,
    Face16.ofAffine fG hG, Face16.ofAffine fH hH⟩ P

end Minimality

end
