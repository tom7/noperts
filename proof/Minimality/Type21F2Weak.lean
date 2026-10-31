module

public import Minimality.Type21F2
public import Minimality.OctAxis
public import Minimality.Type16Rims
public import Minimality.Type16Limit
public import Minimality.Generic.TwoTie
public import Minimality.Generic.PairR2T
public import Minimality.Generic.NamedViews

@[expose] public section

/-!
# Type 21: F2 with a tie at both views, the tied pairs independent

The named vertex views `vtx21`, `vtxView21`, `view21` (with their covariance, continuity) and the
weak variant `cert_type21_F2_weak` of `cert_type21_F2`: `F2Tie` is replaced by `OneTieAt` at both
views and independence of the two tied pairs (`TieIndep`).  The equivariance and the robust rim
of the F2 pair come from `Generic/PairR2T` (`robust_rim_of_pair_signs`, `f2Group`); here the
identification of the axis views with the named views (`eq_smul_view21_one`,
`eq_smul_view21_four`) and the shared body `cert_type21_F2_gen` of `Type21F2`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Filter Noperts

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

theorem view21_eq_namedView : view21 = namedView vtx21 := by
  funext x v; rcases v with _ | _ <;> rfl

theorem tendsto_view21 {ι : Type*} {l : Filter ι} {K : ι → Fin 7 → ℝ³} {x : Fin 7 → ℝ³}
    (hK : ∀ m, Tendsto (fun n => K n m) l (𝓝 (x m))) (v : (Fin 7 × Fin 7) ⊕ Fin 8) :
    Tendsto (fun n => view21 (K n) v) l (𝓝 (view21 x v)) :=
  by rw [view21_eq_namedView]; exact tendsto_namedView vtx21 hK v

theorem view21_map (M : ℝ³ →L[ℝ] ℝ³) (y : Fin 7 → ℝ³) (v : (Fin 7 × Fin 7) ⊕ Fin 8) :
    ∃ c : ℝ, (c = 1 ∨ c = detMap M) ∧ view21 (fun l => M (y l)) v = c • M (view21 y v) := by
  rcases v with ⟨i, j⟩ | t
  · exact ⟨1, Or.inl rfl, by rw [one_smul]; simp [view21]⟩
  · exact ⟨detMap M, Or.inr rfl, planeLine_map M _ _ _ _ _ _⟩

/-- The named views are covariant. -/
theorem covView_view21 (v : (Fin 7 × Fin 7) ⊕ Fin 8) :
    CovView (fun y : Fin 7 → ℝ³ => view21 y v) :=
  by rw [view21_eq_namedView]; exact covView_namedView vtx21 v

/-- Views of the F2 pair at vertex views `1` (V) and `4` (V'), labelling `id` of `F2ViewsL`
(`b = x4, b' = x5, c = x1, d = x2, a = x0, a' = x3`): the quads are `(4,2,5,1)` and `(4,3,5,0)`. -/
noncomputable abbrev f2Group : Bool → ViewGroup 7 :=
  pairGroup (fun y => view21 y (.inr 1)) (fun y => view21 y (.inr 4)) 4 5 2 1 4 5 3 0

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
theorem eq_smul_cross_cross {A B C D u : ℝ³} (h1 : det3 A B u = 0) (h2 : det3 C D u = 0)
    (hw : cross (cross A B) (cross C D) ≠ 0) :
    ∃ lam : ℝ, u = lam • cross (cross A B) (cross C D) := by
  refine ⟨_, eq_smul_of_cross_eq_zero hw ?_⟩
  rw [cross_cross_eq]
  have e1 : ⟪cross A B, u⟫ = 0 := h1
  have e2 : ⟪cross C D, u⟫ = 0 := h2
  rw [e1, e2, zero_smul, zero_smul, sub_zero]

theorem view21_one_eq_cross (y : Fin 7 → ℝ³) : view21 y (.inr 1) =
    cross (cross (y 0 - y 4) (y 1 - y 4)) (cross (y 3 - y 4) (y 6 - y 4)) := by
  show planeLine _ _ _ _ _ _ = _
  rw [planeLine_eq_cross]; rfl

theorem view21_four_eq_cross (y : Fin 7 → ℝ³) : view21 y (.inr 4) =
    cross (cross (y 0 - y 4) (y 6 - y 4)) (cross (y 3 - y 4) (y 1 - y 4)) := by
  show planeLine _ _ _ _ _ _ = _
  rw [planeLine_eq_cross]; rfl

/-- `axisView = lam * vtxView21 y 1` (nonzero `lam`), given the plane memberships and `vtxView21 ≠ 0`. -/
theorem eq_smul_view21_one {y : Fin 7 → ℝ³} {u : ℝ³} (hu : u ≠ 0)
    (h1 : det3 (y 0 - y 4) (y 1 - y 4) u = 0) (h2 : det3 (y 3 - y 4) (y 6 - y 4) u = 0)
    (hw : view21 y (.inr 1) ≠ 0) : ∃ lam : ℝ, lam ≠ 0 ∧ u = lam • view21 y (.inr 1) := by
  rw [view21_one_eq_cross] at hw ⊢
  obtain ⟨lam, h⟩ := eq_smul_cross_cross h1 h2 hw
  exact ⟨lam, fun e => hu (by rw [h, e, zero_smul]), h⟩

theorem eq_smul_view21_four {y : Fin 7 → ℝ³} {u : ℝ³} (hu : u ≠ 0)
    (h1 : det3 (y 0 - y 4) (y 6 - y 4) u = 0) (h2 : det3 (y 3 - y 4) (y 1 - y 4) u = 0)
    (hw : view21 y (.inr 4) ≠ 0) : ∃ lam : ℝ, lam ≠ 0 ∧ u = lam • view21 y (.inr 4) := by
  rw [view21_four_eq_cross] at hw ⊢
  obtain ⟨lam, h⟩ := eq_smul_cross_cross h1 h2 hw
  exact ⟨lam, fun e => hu (by rw [h, e, zero_smul]), h⟩


/-! ### Step 2: the weak/weak F2 certificate -/

theorem image_eq_insert_21 (y : Fin 7 → ℝ³) {a a' b b' c c' d : ℝ³} (ha : y 0 = a) (ha' : y 3 = a')
    (hb : y 4 = b) (hb' : y 5 = b') (hc : y 1 = c) (hc' : y 6 = c') (hd : y 2 = d) :
    (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) = Finset.univ.image y := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    exacts [⟨2, hd⟩, ⟨0, ha⟩, ⟨3, ha'⟩, ⟨4, hb⟩, ⟨5, hb'⟩, ⟨1, hc⟩, ⟨6, hc'⟩]
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [ha, ha', hb, hb', hc, hc', hd]

theorem f2Group_lab_inj : ∀ a, ∀ T ∈ (f2Group a).tests, Function.Injective T.lab :=
  pairGroup_lab_inj _ _ (by decide) (by decide)

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
    (hties : ∀ t, ⟪y (ties t).2.1 - y (ties t).2.2, (f2Group (ties t).1).view y⟫ = 0)
    (hind : TieIndep (fun t => y (ties t).2.1 - y (ties t).2.2)
      (fun t => (f2Group (ties t).1).view y))
    (hex : ∀ a, (∃ i j : Fin 7, i ≠ j ∧ ⟪y i, (f2Group a).view y⟫ = ⟪y j, (f2Group a).view y⟫) →
      ∃ t, (ties t).1 = a) :
    CertV (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L
      (SegOK21 (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) a a' b b' c c' d) := by
  set u := axisView G.l G.m b' b a c with hu
  set v := axisView G.l G.m b' b a c' with hv
  set K := insert d ({a, a', b, b', c, c'} : Finset ℝ³) with hK
  have hKa : a ∈ K := by simp [hK]
  have hKa' : a' ∈ K := by simp [hK]
  have hKb : b ∈ K := by simp [hK]
  have hKb' : b' ∈ K := by simp [hK]
  have hKc : c ∈ K := by simp [hK]
  have hKd : d ∈ K := by simp [hK]
  refine cert_type21_F2_gen F G hσ₁ hT₁ hΓ₁ hB₁ hP₁ hm₁ hm₁' hX₁ hσ₂ hT₂ hΓ₂ hB₂ hP₂ hm₂ hm₂' hX₂
    hmeet hsign hc'u hcone hΔ hL₁ hL₂ ?_ ?_ ?_ ?_
  · intro hbd hdc hbc
    rintro ⟨e1, e2⟩
    rcases o1 b hKb d hKd d hKd c hKc hbd hdc e1 e2 with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hbd h1
    · exact hbc h1
  · intro ha'b haa' hab
    rintro ⟨e1, e2⟩
    rcases o2 b hKb a' hKa' a' hKa' a hKa (Ne.symm ha'b) (Ne.symm haa') e1 e2 with
      ⟨h1, -⟩ | ⟨h1, -⟩
    · exact ha'b h1.symm
    · exact hab h1.symm
  · intro nd2 hR2 m2v m2u hne
    have W2 := weakSep_of_not_robust (o2.oneTie4 hKb hKa' hKb' hKa nd2) hR2
    exact weakSep_det_sign W2.symm m2v m2u hne hS2
  · intro nd1 nd2 hR1 hR2 hdet m1u m2v m2u
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
    obtain ⟨l1, hl1, hu1⟩ := eq_smul_view21_one (y := y) hu0 (by rw [ha, hb, hc]; exact hN1)
      (by rw [ha', hb, hc']; exact hN2) hw1
    obtain ⟨l2, hl2, hv1⟩ := eq_smul_view21_four (y := y) hv0 (by rw [ha, hb, hc']; exact hN3)
      (by rw [ha', hb, hc]; exact hN4) hw4
    have hdet' := hdet_smul hl1 hl2 (by rw [← hu1, ← hv1]; exact hdet)
    have m1u' := segMeet_smul hl1 (by rw [← hu1]; exact m1u)
    have m1v' := segMeet_smul hl2 (by rw [← hv1]; exact hmeet)
    have m2v' := segMeet_smul hl2 (by rw [← hv1]; exact m2v)
    have m2u' := segMeet_smul hl1 (by rw [← hu1]; exact m2u)
    simp only [← ha, ← ha', ← hb, ← hb', ← hc, ← hc', ← hd] at hdet' m1u' m1v' m2v' m2u'
    have oo : ∀ x : Bool, OneTieAt (Finset.univ.image y) ((f2Group x).view y) := by
      rw [← image_eq_insert_21 y ha ha' hb hb' hc hc' hd]
      intro x; cases x
      · have := o2.smul (inv_ne_zero hl2)
        rw [hv1, smul_smul, inv_mul_cancel₀ hl2, one_smul] at this
        exact this
      · have := o1.smul (inv_ne_zero hl1)
        rw [hu1, smul_smul, inv_mul_cancel₀ hl1, one_smul] at this
        exact this
    have hcov := hcover_of_oneTieAt f2Group (pairGroup_hTv _ _ _ _ _ _ _ _ _ _) y hyinj oo ties hties hind
      hex f2Group_lab_inj
    have R : IsRobustUnimodal (quad ⟪y 4, view21 y (.inr 1)⟫ ⟪y 2, view21 y (.inr 1)⟫
          ⟪y 5, view21 y (.inr 1)⟫ ⟪y 1, view21 y (.inr 1)⟫) ∨
        IsRobustUnimodal (quad ⟪y 4, view21 y (.inr 4)⟫ ⟪y 3, view21 y (.inr 4)⟫
          ⟪y 5, view21 y (.inr 4)⟫ ⟪y 0, view21 y (.inr 4)⟫) :=
      robust_rim_of_pair_signs _ _ (covView_view21 _) (covView_view21 _) 4 5 2 1 4 5 3 0 y hdet'
        m1u' m1v' m2v' m2u' f2Group_lab_inj hq ties hties hind hcov
    rcases R with R | R
    · apply hR1
      have e : quad ⟪b, u⟫ ⟪d, u⟫ ⟪b', u⟫ ⟪c, u⟫ = fun i => l1 *
          quad ⟪y 4, view21 y (.inr 1)⟫ ⟪y 2, view21 y (.inr 1)⟫ ⟪y 5, view21 y (.inr 1)⟫
            ⟪y 1, view21 y (.inr 1)⟫ i := by
        rw [← quad_smul, hu1, hb, hd, hb', hc]
        simp only [real_inner_smul_right]
      rw [e]; exact robust_mul_ne_zero R hl1
    · apply hR2
      have e : quad ⟪b, v⟫ ⟪a', v⟫ ⟪b', v⟫ ⟪a, v⟫ = fun i => l2 *
          quad ⟪y 4, view21 y (.inr 4)⟫ ⟪y 3, view21 y (.inr 4)⟫ ⟪y 5, view21 y (.inr 4)⟫
            ⟪y 0, view21 y (.inr 4)⟫ i := by
        rw [← quad_smul, hv1, hb, ha', hb', ha]
        simp only [real_inner_smul_right]
      rw [e]; exact robust_mul_ne_zero R hl2



/-- **The weak tie hypothesis of F2** (labels as in `F2ViewsL`): one tie at each view, the two
diagonals non-coplanar, the tied pairs independent, and the seven points distinct. -/
def F2TieW (K : Finset ℝ³) (a a' b b' c c' d u v : ℝ³) : Prop :=
  OneTieAt K u ∧ OneTieAt K v ∧ det3 (d - b) (b' - b) (c - d) ≠ 0 ∧
    det3 (a' - b) (b' - b) (a - a') ≠ 0 ∧ IndepF K u v ∧
    Function.Injective ![a, c, d, a', b, b', c']

theorem cross_cross_ne_zero {f : ℝ³ → ℝ} {N P A C A' C' : ℝ³}
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
  set y : Fin 7 → ℝ³ := ![a, c, d, a', b, b', c'] with hy
  have hKy : K = Finset.univ.image y :=
    image_eq_insert_21 y (a := a) (a' := a') (b := b) (b' := b') (c := c) (c' := c') (d := d) rfl rfl rfl rfl rfl rfl rfl
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
    rw [view21_one_eq_cross]
    exact cross_cross_ne_zero F.abc.hN F.abc.hQ F.abc.hP F.abc.hR
      (F.abc.neg a' (by simp) (Ne.symm haa') ha'b ha'c) n_abc' n_a'bc
  have hw4 : view21 y (.inr 4) ≠ 0 := by
    rw [view21_four_eq_cross]
    exact cross_cross_ne_zero F.abc'.hN F.abc'.hQ F.abc'.hP F.abc'.hR
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
  obtain ⟨lam, hl, e1⟩ := eq_smul_view21_one (y := y) hu0 hN1 hN2 hw1
  obtain ⟨mu, hm, e2⟩ := eq_smul_view21_four (y := y) hv0 hN3 hN4 hw4
  have hvu : lam⁻¹ • u = view21 y (.inr 1) := by
    rw [e1, smul_smul, inv_mul_cancel₀ hl, one_smul]
  have hvv : mu⁻¹ • v = view21 y (.inr 4) := by
    rw [e2, smul_smul, inv_mul_cancel₀ hm, one_smul]
  have hI : IndepF (Finset.univ.image y) (view21 y (.inr 1)) (view21 y (.inr 4)) := by
    rw [← hKy, ← hvu, ← hvv]; exact hind.smul (inv_ne_zero hl) (inv_ne_zero hm)
  have hnt : ∀ {V : Finset ℝ³} {w : ℝ³} {c : ℝ}, c ≠ 0 → NoTieAt V w → NoTieAt V (c • w) := by
    intro V w c hc h s hs t ht hst e
    simp only [real_inner_smul_right] at e
    exact h s hs t ht hst (mul_left_cancel₀ hc e)
  have hno' : ¬ (NoTieAt (Finset.univ.image y) (view21 y (.inr 1)) ∨
      NoTieAt (Finset.univ.image y) (view21 y (.inr 4))) := fun h =>
    hno (by rw [hKy]; exact h.imp (fun h => by rw [e1]; exact hnt hl h) (fun h => by rw [e2]; exact hnt hm h))
  obtain ⟨i, j, k, l, e1', e2', hind'⟩ := exists_ties_of_indepF hI hno'
  obtain ⟨ties, hties, hind2, hex⟩ := exists_listed_ties (fu := fun y => view21 y (.inr 1))
    (fv := fun y => view21 y (.inr 4)) f2Group rfl rfl e1' e2' hind'
  exact cert_type21_F2_weak_core F G hσ₁ hT₁ hΓ₁ hB₁ hP₁ hm₁ hm₁' hX₁ hσ₂ hT₂ hΓ₂ hB₂ hP₂ hm₂ hm₂'
    hX₂ hmeet hsign hc'u hcone hΔ hL₁ hL₂ y rfl rfl rfl rfl rfl rfl rfl hyinj hN1 hN2 hN3 hN4 hw1 hw4
    o1 o2 hS2 (q := 2) le_rfl ties hties hind2 (fun g _ => hex g)

end Minimality
