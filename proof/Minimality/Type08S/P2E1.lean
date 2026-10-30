module

public import Minimality.Generic.TwoTie
public import Minimality.ManyTies
public import Minimality.Type16Metric
public import Minimality.Slide

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# E1 (generic): Lemma R2T* — the lexicographic two-closing lemma, any ties (`tt3/draft.md` §1)

An edge pair `(v, w, f1, r, f2)` at a covariant view `u` with `z_w < z_v` (`z = ⟪·, u y⟫`) whose two
closings `X_v = (v,f1,r,f2)`, `X_w = (w,f1,r,f2)` satisfy MF at every unimodular metric
(`mapShape L y`, `det L = 1`): then `X_v` or `X_w` is robustly unimodal at `y`, or
`z f1 = z r = z f2 =: c` with `z_w ≤ c ≤ z_v`.  No tie count, no independence.

* `exists_sep_segment`: a point off a segment is strictly separated from it (Hahn–Banach).
* `exists_lex_metric`: for `d ⊥ u` the shear `x ↦ x + ε⟪u,x⟫d` (det 1) realizes the lexicographic
  order `(z, ⟪·, d⟫)` on finitely many points.
* `r2t_kill_c`: case (c) of the draft (`f1, f2` weakly below `w` and `r`, not all four at one level) is
  incompatible with MF.  Case (b) is case (c) for `(-u, w, v)`.
* `r2t_star`: the lemma.
-/

set_option autoImplicit true
set_option linter.unusedVariables false

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### Separation of a point from a segment -/

theorem exists_sep_segment {x a b : ℝ³} (h : x ∉ segment ℝ a b) :
    ∃ d : ℝ³, 0 < ⟪x - a, d⟫ ∧ 0 < ⟪x - b, d⟫ := by
  have hc : IsClosed (segment ℝ a b) := by
    have := (Set.toFinite ({a, b} : Set ℝ³)).isCompact_convexHull (𝕜 := ℝ)
    rw [convexHull_pair] at this
    exact this.isClosed
  obtain ⟨f, c, hfx, hf⟩ := geometric_hahn_banach_point_closed (convex_segment a b) hc h
  have key : ∀ z : ℝ³, ⟪z, -(InnerProductSpace.toDual ℝ ℝ³).symm f⟫ = - f z := by
    intro z
    rw [inner_neg_right, real_inner_comm, InnerProductSpace.toDual_symm_apply]
  refine ⟨-(InnerProductSpace.toDual ℝ ℝ³).symm f, ?_, ?_⟩
  · rw [key, map_sub]
    have := hf a (left_mem_segment ℝ a b); linarith
  · rw [key, map_sub]
    have := hf b (right_mem_segment ℝ a b); linarith

theorem not_mem_segment_of_noSeg {x a b : ℝ³} (hxa : x ≠ a) (hxb : x ≠ b)
    (h : ∀ s : ℝ, 0 < s → s < 1 → x ≠ a + s • (b - a)) : x ∉ segment ℝ a b := by
  rintro ⟨p, q, hp, hq, hpq, hx⟩
  have hp' : p = 1 - q := by linarith
  subst hp'
  rcases hq.lt_or_eq with hq | rfl
  · rcases (show q ≤ 1 by linarith).lt_or_eq with hq1 | rfl
    · apply h q hq hq1
      rw [← hx, smul_sub, sub_smul, one_smul]; abel
    · apply hxb; rw [← hx]; simp
  · apply hxa; rw [← hx]; simp

/-! ### The lexicographic metric -/

theorem detMap_eq_det (L : ℝ³ →L[ℝ] ℝ³) : detMap L = LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis, Matrix.det_fin_three]
  simp only [detMap, det3_expand, LinearMap.toMatrix_apply]
  simp [EuclideanSpace.basisFun_apply]
  ring

/-- The shear `x ↦ x + ε ⟪u, x⟫ d`. -/
noncomputable def lexShear (u d : ℝ³) (ε : ℝ) : ℝ³ →L[ℝ] ℝ³ :=
  1 + ε • (innerSL ℝ u).smulRight d

theorem lexShear_apply (u d : ℝ³) (ε : ℝ) (x : ℝ³) :
    lexShear u d ε x = x + (ε * ⟪u, x⟫) • d := by
  simp [lexShear, mul_smul]

theorem lexShear_det (u d : ℝ³) (ε : ℝ) (hdu : ⟪d, u⟫ = 0) :
    LinearMap.det (lexShear u d ε : ℝ³ →ₗ[ℝ] ℝ³) = 1 := by
  rw [← detMap_eq_det]
  simp only [detMap, lexShear_apply, det3_expand]
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial] at hdu ⊢
  simp
  linear_combination ε * hdu

theorem lexShear_inner (u d : ℝ³) (ε : ℝ) (hdu : ⟪d, u⟫ = 0) (y : ℝ³) :
    ⟪lexShear u d ε y, lexShear u d ε u⟫ =
      (1 + ε ^ 2 * ⟪u, u⟫ * ⟪d, d⟫) * ⟪y, u⟫ + (ε * ⟪u, u⟫) * ⟪y, d⟫ := by
  rw [lexShear_apply, lexShear_apply]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm u y, hdu]
  ring

/-- **Lexicographic metric.**  For `d ⊥ u`, a unimodular `L` orders finitely many points by `z = ⟪·, u⟫`,
and within a level by `⟪·, d⟫` (exactly: the depth difference is `B ⟪· - ·, d⟫`, `B > 0`). -/
theorem exists_lex_metric {u d : ℝ³} (hu : u ≠ 0) (hdu : ⟪d, u⟫ = 0) {ι : Type*} [Finite ι]
    (Y : ι → ℝ³) :
    ∃ L : ℝ³ →L[ℝ] ℝ³, LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) = 1 ∧ ∃ B : ℝ, 0 < B ∧ ∀ p q : ι,
      (⟪Y p, u⟫ < ⟪Y q, u⟫ → ⟪L (Y p), L u⟫ < ⟪L (Y q), L u⟫) ∧
      (⟪Y p, u⟫ = ⟪Y q, u⟫ → ⟪L (Y p), L u⟫ - ⟪L (Y q), L u⟫ = B * ⟪Y p - Y q, d⟫) := by
  have huu : 0 < ⟪u, u⟫ := real_inner_self_pos.mpr hu
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ∀ p q : ι, ⟪Y p, u⟫ < ⟪Y q, u⟫ →
      ε * (⟪u, u⟫ * |⟪Y p - Y q, d⟫|) < ⟪Y q, u⟫ - ⟪Y p, u⟫ := by
    have h0 : ∀ᶠ ε in 𝓝[>] (0:ℝ), 0 < ε := eventually_mem_nhdsWithin
    refine h0.and ?_
    refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
    rw [Filter.eventually_all]; intro p
    rw [Filter.eventually_all]; intro q
    by_cases h : ⟪Y p, u⟫ < ⟪Y q, u⟫
    · have hc : Continuous fun ε : ℝ => ε * (⟪u, u⟫ * |⟪Y p - Y q, d⟫|) := by fun_prop
      have := hc.continuousAt.eventually_lt (continuousAt_const (y := ⟪Y q, u⟫ - ⟪Y p, u⟫) (x := (0:ℝ)))
        (by simp only [zero_mul]; linarith)
      exact this.mono fun ε hε _ => hε
    · exact Filter.Eventually.of_forall fun ε h' => absurd h' h
  obtain ⟨ε, hε0, hε⟩ := hev.exists
  refine ⟨lexShear u d ε, lexShear_det u d ε hdu, ε * ⟪u, u⟫, mul_pos hε0 huu, fun p q => ⟨?_, ?_⟩⟩
  · intro hpq
    rw [lexShear_inner u d ε hdu, lexShear_inner u d ε hdu]
    have h1 := hε p q hpq
    have h2 : ε * ⟪u, u⟫ * (⟪Y p, d⟫ - ⟪Y q, d⟫) ≤ ε * (⟪u, u⟫ * |⟪Y p - Y q, d⟫|) := by
      rw [inner_sub_left, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left (le_abs_self _) (mul_pos hε0 huu).le
    have h3 : 0 ≤ ε ^ 2 * ⟪u, u⟫ * ⟪d, d⟫ := by
      have := real_inner_self_nonneg (x := d); positivity
    nlinarith
  · intro hpq
    rw [lexShear_inner u d ε hdu, lexShear_inner u d ε hdu, hpq, inner_sub_left]
    ring

/-! ### Case (c): MF kills `f1, f2` weakly below `w` and `r` -/

theorem isOpen_imp_pos (P : Prop) (c : ℝ³) : IsOpen {d : ℝ³ | P → 0 < ⟪c, d⟫} := by
  by_cases hP : P
  · simp only [hP, true_implies]
    exact isOpen_lt continuous_const (continuous_const.inner continuous_id)
  · simp only [hP, false_implies, Set.ofPred_true]
    exact isOpen_univ

theorem quad_depth_eq {n : ℕ} (u : (Fin n → ℝ³) → ℝ³) (y : Fin n → ℝ³) (a b c d : Fin n) :
    (LabTest.quad u a b c d).depth y = quad ⟪y a, u y⟫ ⟪y b, u y⟫ ⟪y c, u y⟫ ⟪y d, u y⟫ := by
  funext i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rfl

set_option maxHeartbeats 1000000 in
/-- **Case (c).**  `f1, f2` weakly below `w` and `r` (then also strictly below `v`), not the level
configuration `w ~ f1 ~ r ~ f2`: some unimodular metric makes both closings two-peaked, against MF. -/
theorem r2t_kill_c {n : ℕ} (y : Fin n → ℝ³) (u : (Fin n → ℝ³) → ℝ³) (hcov : CovView u)
    (v w f1 r f2 : Fin n) (hy : Function.Injective y) (hlab : [v, w, f1, r, f2].Nodup)
    (hseg : ∀ i j m : Fin n, y m ≠ y i → y m ≠ y j → ∀ s : ℝ, 0 < s → s < 1 →
      y m ≠ y i + s • (y j - y i))
    (hord : ⟪y w, u y⟫ < ⟪y v, u y⟫)
    (hMF : ∀ L : ℝ³ →L[ℝ] ℝ³, LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) = 1 →
      Function.Injective ((LabTest.quad u v f1 r f2).depth (mapShape L y)) →
      Function.Injective ((LabTest.quad u w f1 r f2).depth (mapShape L y)) →
      IsCyclicUnimodal ((LabTest.quad u v f1 r f2).depth (mapShape L y)) ∨
        IsCyclicUnimodal ((LabTest.quad u w f1 r f2).depth (mapShape L y)))
    (hc : ⟪y f1, u y⟫ ≤ ⟪y w, u y⟫ ∧ ⟪y f2, u y⟫ ≤ ⟪y w, u y⟫ ∧
      ⟪y f1, u y⟫ ≤ ⟪y r, u y⟫ ∧ ⟪y f2, u y⟫ ≤ ⟪y r, u y⟫)
    (hnex : ¬ (⟪y w, u y⟫ = ⟪y f1, u y⟫ ∧ ⟪y w, u y⟫ = ⟪y f2, u y⟫ ∧ ⟪y w, u y⟫ = ⟪y r, u y⟫)) :
    False := by
  classical
  set u0 := u y with hu0def
  set z : Fin n → ℝ := fun x => ⟪y x, u0⟫ with hzdef
  have hu0 : u0 ≠ 0 := by
    intro h; rw [h, inner_zero_right, inner_zero_right] at hord; exact lt_irrefl _ hord
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hlab
  obtain ⟨⟨hvw, hvf1, hvr, hvf2⟩, ⟨hwf1, hwr, hwf2⟩, ⟨hf1r, hf1f2⟩, hrf2, -⟩ := hlab
  have yne : ∀ {p q : Fin n}, p ≠ q → y p ≠ y q := fun h e => h (hy e)
  -- the point-segment separations
  have sep : ∀ {x a b : Fin n}, x ≠ a → x ≠ b → ∃ d : ℝ³, 0 < ⟪y x - y a, d⟫ ∧ 0 < ⟪y x - y b, d⟫ :=
    fun {x a b} hxa hxb => exists_sep_segment (not_mem_segment_of_noSeg (yne hxa) (yne hxb)
      (fun s hs0 hs1 => hseg a b x (yne hxa) (yne hxb) s hs0 hs1))
  -- Step 1: a direction putting `w, r` above `f1, f2` within each level
  set Pd : ℝ³ → Prop := fun d =>
    (z w = z f1 → 0 < ⟪y w - y f1, d⟫) ∧ (z w = z f2 → 0 < ⟪y w - y f2, d⟫) ∧
    (z r = z f1 → 0 < ⟪y r - y f1, d⟫) ∧ (z r = z f2 → 0 < ⟪y r - y f2, d⟫) with hPd
  have hd0 : ∃ d, Pd d := by
    by_cases hw : z w = z f1 ∨ z w = z f2
    · by_cases hr : z r = z f1 ∨ z r = z f2
      · -- both at the top level of the `f`'s; it is one `f` only (else `hnex`)
        have hc1 := hc.1; have hc2 := hc.2.1; have hc3 := hc.2.2.1; have hc4 := hc.2.2.2
        by_cases h12 : z f1 = z f2
        · exfalso; apply hnex
          rcases hw with hw | hw <;> rcases hr with hr | hr <;>
            exact ⟨by simp only [hzdef] at *; linarith, by simp only [hzdef] at *; linarith,
              by simp only [hzdef] at *; linarith⟩
        rcases lt_or_gt_of_ne h12 with h12 | h12
        · -- `z f1 < z f2`: `w, r` at the level of `f2`
          have ew : z w = z f2 := by
            rcases hw with hw | hw
            · simp only [hzdef] at *; linarith
            · exact hw
          have er : z r = z f2 := by
            rcases hr with hr | hr
            · simp only [hzdef] at *; linarith
            · exact hr
          obtain ⟨d, h1, h2⟩ := sep (x := f2) (a := w) (b := r) (Ne.symm hwf2) (Ne.symm hrf2)
          refine ⟨-d, fun h => ?_, fun _ => ?_, fun h => ?_, fun _ => ?_⟩
          · exfalso; rw [ew] at h; exact lt_irrefl _ (h ▸ h12)
          · rw [inner_neg_right, ← neg_sub, inner_neg_left, neg_neg]; exact h1
          · exfalso; rw [er] at h; exact lt_irrefl _ (h ▸ h12)
          · rw [inner_neg_right, ← neg_sub, inner_neg_left, neg_neg]; exact h2
        · -- `z f2 < z f1`
          have ew : z w = z f1 := by
            rcases hw with hw | hw
            · exact hw
            · simp only [hzdef] at *; linarith
          have er : z r = z f1 := by
            rcases hr with hr | hr
            · exact hr
            · simp only [hzdef] at *; linarith
          obtain ⟨d, h1, h2⟩ := sep (x := f1) (a := w) (b := r) (Ne.symm hwf1) (Ne.symm hf1r).symm
          refine ⟨-d, fun _ => ?_, fun h => ?_, fun _ => ?_, fun h => ?_⟩
          · rw [inner_neg_right, ← neg_sub, inner_neg_left, neg_neg]; exact h1
          · exfalso; rw [ew] at h; exact lt_irrefl _ (h ▸ h12)
          · rw [inner_neg_right, ← neg_sub, inner_neg_left, neg_neg]; exact h2
          · exfalso; rw [er] at h; exact lt_irrefl _ (h ▸ h12)
      · obtain ⟨d, h1, h2⟩ := sep (x := w) (a := f1) (b := f2) hwf1 hwf2
        push Not at hr
        exact ⟨d, fun _ => h1, fun _ => h2, fun h => absurd h hr.1, fun h => absurd h hr.2⟩
    · push Not at hw
      by_cases hr : z r = z f1 ∨ z r = z f2
      · obtain ⟨d, h1, h2⟩ := sep (x := r) (a := f1) (b := f2) (Ne.symm hf1r) hrf2
        exact ⟨d, fun h => absurd h hw.1, fun h => absurd h hw.2, fun _ => h1, fun _ => h2⟩
      · push Not at hr
        exact ⟨0, fun h => absurd h hw.1, fun h => absurd h hw.2, fun h => absurd h hr.1,
          fun h => absurd h hr.2⟩
  -- Step 2: perturb off the kernels of all label differences
  set plab : Fin 5 → Fin n := ![v, w, f1, r, f2] with hplab
  have plab_inj : Function.Injective plab := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [plab]
  let ι := {k : Fin 5 × Fin 5 // k.1 ≠ k.2}
  let ℓ : ι → ℝ³ →ₗ[ℝ] ℝ := fun k => innerₛₗ ℝ (y (plab k.1.1) - y (plab k.1.2))
  have hℓ : ∀ k, ℓ k ≠ 0 := by
    intro k h0
    have := LinearMap.congr_fun h0 (y (plab k.1.1) - y (plab k.1.2))
    simp only [ℓ, innerₛₗ_apply_apply, LinearMap.zero_apply] at this
    exact yne (fun e => k.2 (plab_inj e)) (sub_eq_zero.mp (inner_self_eq_zero.mp this))
  have hO : IsOpen {d : ℝ³ | Pd d} := by
    simp only [hPd, Set.ofPred_and]
    exact (isOpen_imp_pos _ _).inter ((isOpen_imp_pos _ _).inter ((isOpen_imp_pos _ _).inter
      (isOpen_imp_pos _ _)))
  obtain ⟨d1, hd1P, hd1ℓ⟩ := exists_avoid_kernels ℓ hℓ hO hd0
  -- project to `u0^⊥`
  set d := d1 - (⟪d1, u0⟫ / ⟪u0, u0⟫) • u0 with hddef
  have hu0u0 : ⟪u0, u0⟫ ≠ 0 := (real_inner_self_pos.mpr hu0).ne'
  have hdu : ⟪d, u0⟫ = 0 := by
    rw [hddef, inner_sub_left, real_inner_smul_left, div_mul_cancel₀ _ hu0u0, sub_self]
  have hperp : ∀ a : ℝ³, ⟪a, u0⟫ = 0 → ⟪a, d⟫ = ⟪a, d1⟫ := by
    intro a ha
    rw [hddef, inner_sub_right, real_inner_smul_right, ha, mul_zero, sub_zero]
  -- Step 3: the lexicographic metric
  obtain ⟨L, hdet, B, hB, hlex⟩ := exists_lex_metric hu0 hdu (fun i : Fin 5 => y (plab i))
  set D : Fin n → ℝ := fun x => ⟪L (y x), L u0⟫ with hDdef
  have tied : ∀ i j : Fin 5, z (plab i) = z (plab j) → D (plab i) - D (plab j) =
      B * ⟪y (plab i) - y (plab j), d1⟫ := by
    intro i j h
    rw [← hperp _ (by rw [inner_sub_left]; exact sub_eq_zero.mpr h)]
    exact (hlex i j).2 h
  have strict : ∀ i j : Fin 5, z (plab i) < z (plab j) → D (plab i) < D (plab j) :=
    fun i j h => (hlex i j).1 h
  have Dinj : ∀ i j : Fin 5, i ≠ j → D (plab i) ≠ D (plab j) := by
    intro i j hij e
    rcases lt_trichotomy (z (plab i)) (z (plab j)) with h | h | h
    · exact (strict i j h).ne e
    · have := tied i j h
      rw [e, sub_self] at this
      have h2 := hd1ℓ ⟨(i, j), hij⟩
      simp only [ℓ, innerₛₗ_apply_apply] at h2
      exact h2 ((mul_eq_zero.mp this.symm).resolve_left hB.ne')
    · exact (strict j i h).ne' e
  have below : ∀ i j : Fin 5, z (plab j) ≤ z (plab i) →
      (z (plab j) = z (plab i) → 0 < ⟪y (plab i) - y (plab j), d1⟫) → D (plab j) < D (plab i) := by
    intro i j hle hpos
    rcases hle.lt_or_eq with h | h
    · exact strict j i h
    · have := tied i j h.symm
      have := mul_pos hB (hpos h)
      linarith
  have hc1 := hc.1; have hc2 := hc.2.1; have hc3 := hc.2.2.1; have hc4 := hc.2.2.2
  have hvf1' : z f1 < z v := lt_of_le_of_lt hc1 hord
  have hvf2' : z f2 < z v := lt_of_le_of_lt hc2 hord
  obtain ⟨P1, P2, P3, P4⟩ := hd1P
  have b_v1 : D f1 < D v := below 0 2 hvf1'.le (fun h => absurd h hvf1'.ne)
  have b_v2 : D f2 < D v := below 0 4 hvf2'.le (fun h => absurd h hvf2'.ne)
  have b_w1 : D f1 < D w := below 1 2 hc1 (fun h => P1 h.symm)
  have b_w2 : D f2 < D w := below 1 4 hc2 (fun h => P2 h.symm)
  have b_r1 : D f1 < D r := below 3 2 hc3 (fun h => P3 h.symm)
  have b_r2 : D f2 < D r := below 3 4 hc4 (fun h => P4 h.symm)
  -- Step 4: MF at `L`
  have hdepth : ∀ a b c e : Fin n, (LabTest.quad u a b c e).depth (mapShape L y) =
      quad (D a) (D b) (D c) (D e) := by
    intro a b c e
    rw [quad_depth_eq, hcov.2 L y hdet]
    rfl
  have i_r1 : D r ≠ D f1 := (Dinj 3 2 (by decide))
  have i_r2 : D r ≠ D f2 := (Dinj 3 4 (by decide))
  have i_12 : D f1 ≠ D f2 := (Dinj 2 4 (by decide))
  have qinj : ∀ {a b c e : ℝ}, a ≠ b → a ≠ c → a ≠ e → b ≠ c → b ≠ e → c ≠ e →
      Function.Injective (quad a b c e) := by
    intro a b c e h1 h2 h3 h4 h5 h6 i j hij
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
      first | rfl | (simp only [quad_0, quad_1, quad_2, quad_3] at hij; simp_all)
  have hiv : Function.Injective ((LabTest.quad u v f1 r f2).depth (mapShape L y)) := by
    rw [hdepth]
    exact qinj b_v1.ne' (Dinj 0 3 (by decide)) b_v2.ne' i_r1.symm i_12 i_r2
  have hiw : Function.Injective ((LabTest.quad u w f1 r f2).depth (mapShape L y)) := by
    rw [hdepth]
    exact qinj b_w1.ne' (Dinj 1 3 (by decide)) b_w2.ne' i_r1.symm i_12 i_r2
  rcases hMF L hdet hiv hiw with h | h
  · rw [hdepth] at h
    have := (nws_of_unimodal4 h).1
    simp only [quad, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at this
    rcases this with h' | h' | h' | h' <;> linarith
  · rw [hdepth] at h
    have := (nws_of_unimodal4 h).1
    simp only [quad, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at this
    rcases this with h' | h' | h' | h' <;> linarith

theorem covView_neg {n : ℕ} {u : (Fin n → ℝ³) → ℝ³} (h : CovView u) : CovView (fun y => -u y) :=
  ⟨h.1.neg, fun L y hL => by simp [h.2 L y hL]⟩

theorem quad_depth_neg {n : ℕ} (u : (Fin n → ℝ³) → ℝ³) (Y : Fin n → ℝ³) (a b c e : Fin n) :
    (LabTest.quad (fun y => -u y) a b c e).depth Y = fun i => -(LabTest.quad u a b c e).depth Y i := by
  funext i; simp [LabTest.depth, LabTest.quad, inner_neg_right]

/-- **Lemma R2T\*** (`tt3/draft.md` §1): MF at every unimodular metric for the two closings of an edge
pair gives a robust closing, or the weak far triple `z f1 = z r = z f2 ∈ [z_w, z_v]`. Any ties. -/
theorem r2t_star {n : ℕ} (y : Fin n → ℝ³) (u : (Fin n → ℝ³) → ℝ³) (hcov : CovView u)
    (v w f1 r f2 : Fin n) (hy : Function.Injective y) (hlab : [v, w, f1, r, f2].Nodup)
    (hseg : ∀ i j m : Fin n, y m ≠ y i → y m ≠ y j → ∀ s : ℝ, 0 < s → s < 1 →
      y m ≠ y i + s • (y j - y i))
    (hord : ⟪y w, u y⟫ < ⟪y v, u y⟫)
    (hMF : ∀ L : ℝ³ →L[ℝ] ℝ³, LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) = 1 →
      Function.Injective ((LabTest.quad u v f1 r f2).depth (mapShape L y)) →
      Function.Injective ((LabTest.quad u w f1 r f2).depth (mapShape L y)) →
      IsCyclicUnimodal ((LabTest.quad u v f1 r f2).depth (mapShape L y)) ∨
        IsCyclicUnimodal ((LabTest.quad u w f1 r f2).depth (mapShape L y))) :
    IsRobustUnimodal ((LabTest.quad u v f1 r f2).depth y) ∨
      IsRobustUnimodal ((LabTest.quad u w f1 r f2).depth y) ∨
      (⟪y f1, u y⟫ = ⟪y r, u y⟫ ∧ ⟪y r, u y⟫ = ⟪y f2, u y⟫ ∧ ⟪y w, u y⟫ ≤ ⟪y r, u y⟫ ∧
        ⟪y r, u y⟫ ≤ ⟪y v, u y⟫) := by
  rw [quad_depth_eq, quad_depth_eq]
  by_cases hv : (⟪y v, u y⟫ < ⟪y f1, u y⟫ ∨ ⟪y v, u y⟫ < ⟪y f2, u y⟫ ∨ ⟪y r, u y⟫ < ⟪y f1, u y⟫ ∨
      ⟪y r, u y⟫ < ⟪y f2, u y⟫) ∧ (⟪y f1, u y⟫ < ⟪y v, u y⟫ ∨ ⟪y f2, u y⟫ < ⟪y v, u y⟫ ∨
      ⟪y f1, u y⟫ < ⟪y r, u y⟫ ∨ ⟪y f2, u y⟫ < ⟪y r, u y⟫)
  · exact Or.inl (CaseC18.robust_quad_of_nws hv.1 hv.2)
  by_cases hw : (⟪y w, u y⟫ < ⟪y f1, u y⟫ ∨ ⟪y w, u y⟫ < ⟪y f2, u y⟫ ∨ ⟪y r, u y⟫ < ⟪y f1, u y⟫ ∨
      ⟪y r, u y⟫ < ⟪y f2, u y⟫) ∧ (⟪y f1, u y⟫ < ⟪y w, u y⟫ ∨ ⟪y f2, u y⟫ < ⟪y w, u y⟫ ∨
      ⟪y f1, u y⟫ < ⟪y r, u y⟫ ∨ ⟪y f2, u y⟫ < ⟪y r, u y⟫)
  · exact Or.inr (Or.inl (CaseC18.robust_quad_of_nws hw.1 hw.2))
  right; right
  rw [not_and_or] at hv hw
  rcases hw with hw | hw
  · -- (c): `f1, f2` weakly below `w` and `r`
    push Not at hw
    obtain ⟨c1, c2, c3, c4⟩ := hw
    by_cases hnex : ⟪y w, u y⟫ = ⟪y f1, u y⟫ ∧ ⟪y w, u y⟫ = ⟪y f2, u y⟫ ∧ ⟪y w, u y⟫ = ⟪y r, u y⟫
    · obtain ⟨e1, e2, e3⟩ := hnex
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    · exact (r2t_kill_c y u hcov v w f1 r f2 hy hlab hseg hord hMF ⟨c1, c2, c3, c4⟩ hnex).elim
  · -- (d): `w` and `r` weakly below `f1, f2`
    push Not at hw
    obtain ⟨d1, d2, d3, d4⟩ := hw
    rcases hv with hv | hv
    · push Not at hv
      obtain ⟨a1, a2, a3, a4⟩ := hv
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    · -- (b): the mirror of (c) at `-u`, with `v, w` swapped
      push Not at hv
      obtain ⟨b1, b2, b3, b4⟩ := hv
      by_cases hnex : ⟪y v, u y⟫ = ⟪y f1, u y⟫ ∧ ⟪y v, u y⟫ = ⟪y f2, u y⟫ ∧ ⟪y v, u y⟫ = ⟪y r, u y⟫
      · obtain ⟨e1, e2, e3⟩ := hnex
        exact ⟨by linarith, by linarith, by linarith, by linarith⟩
      · exfalso
        have hlab' : [w, v, f1, r, f2].Nodup := by
          simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
            List.nodup_nil, and_true] at hlab ⊢
          obtain ⟨⟨hvw, hvf1, hvr, hvf2⟩, ⟨hwf1, hwr, hwf2⟩, ⟨hf1r, hf1f2⟩, hrf2, -⟩ := hlab
          exact ⟨⟨Ne.symm hvw, hwf1, hwr, hwf2⟩, ⟨hvf1, hvr, hvf2⟩, ⟨hf1r, hf1f2⟩, hrf2, by simp⟩
        refine r2t_kill_c y (fun y => -u y) (covView_neg hcov) w v f1 r f2 hy hlab' hseg
          (by simp only [inner_neg_right]; linarith) ?_
          ⟨by simp only [inner_neg_right]; linarith, by simp only [inner_neg_right]; linarith,
            by simp only [inner_neg_right]; linarith, by simp only [inner_neg_right]; linarith⟩
          (by simp only [inner_neg_right, neg_inj]; exact hnex)
        intro L hL hi1 hi2
        rw [quad_depth_neg] at hi1 hi2 ⊢
        rw [quad_depth_neg]
        have j1 : Function.Injective ((LabTest.quad u w f1 r f2).depth (mapShape L y)) :=
          fun a b h => hi1 (by simp only [h])
        have j2 : Function.Injective ((LabTest.quad u v f1 r f2).depth (mapShape L y)) :=
          fun a b h => hi2 (by simp only [h])
        rcases hMF L hL j2 j1 with h | h
        · exact Or.inr (IsCyclicUnimodal.neg' (show 2 ≤ 4 by norm_num) h)
        · exact Or.inl (IsCyclicUnimodal.neg' (show 2 ≤ 4 by norm_num) h)

end Minimality

#print axioms Minimality.r2t_kill_c
#print axioms Minimality.r2t_star
