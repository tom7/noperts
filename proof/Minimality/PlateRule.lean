module

public import Minimality.BoxLemma

@[expose] public section

/-! # The plate rule (glob rule P, Lemma F) in Lean

A type-free sufficient condition for a polytope to be Rupert, on top of the box lemma. -/

namespace Minimality

open scoped RealInnerProductSpace

/-- A point with positive barycentric weights on three vertices (whose projections are `q₁ q₂ q₃`)
is a positive combination of all the projected vertices. -/
theorem posComb_of_bary (V : Finset ℝ³) (R₂ : Matrix (Fin 3) (Fin 3) ℝ)
    (p₁ p₂ p₃ : ℝ³) (h₁ : p₁ ∈ V) (h₂ : p₂ ∈ V) (h₃ : p₃ ∈ V)
    (l₁ l₂ l₃ : ℝ² → ℝ) (hsum : ∀ z, l₁ z + l₂ z + l₃ z = 1)
    (hrec : ∀ z, l₁ z • proj_xy (R₂.toEuclideanLin p₁) + l₂ z • proj_xy (R₂.toEuclideanLin p₂)
      + l₃ z • proj_xy (R₂.toEuclideanLin p₃) = z)
    (x : ℝ²) (hx₁ : 0 < l₁ x) (hx₂ : 0 < l₂ x) (hx₃ : 0 < l₃ x) :
    PosComb V R₂ x := by
  classical
  set φ : ℝ³ → ℝ² := fun w => proj_xy (R₂.toEuclideanLin w) with hφ
  have hne : V.Nonempty := ⟨p₁, h₁⟩
  set n : ℝ := (V.card : ℝ) with hn
  have hnpos : 0 < n := by rw [hn]; exact_mod_cast hne.card_pos
  set c : ℝ² := ∑ w ∈ V, (1 / n) • φ w with hc
  set m : ℝ := min (l₁ x) (min (l₂ x) (l₃ x)) with hm
  have hmpos : 0 < m := lt_min hx₁ (lt_min hx₂ hx₃)
  set K : ℝ := |l₁ c| + |l₂ c| + |l₃ c| with hK
  have hK0 : 0 ≤ K := by positivity
  set ε : ℝ := m / (1 + K) with hε
  have hεpos : 0 < ε := by positivity
  have hεK : ε * K < m := by
    rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]; nlinarith
  have hbd : ∀ t : ℝ, |t| ≤ K → ε * t < m := by
    intro t ht
    have := neg_abs_le t
    have := le_abs_self t
    nlinarith
  have ha₁ : 0 < l₁ x - ε * l₁ c := by
    have := hbd (l₁ c) (by simp only [hK]; linarith [abs_nonneg (l₂ c), abs_nonneg (l₃ c)])
    have := min_le_left (l₁ x) (min (l₂ x) (l₃ x))
    linarith
  have ha₂ : 0 < l₂ x - ε * l₂ c := by
    have := hbd (l₂ c) (by simp only [hK]; linarith [abs_nonneg (l₁ c), abs_nonneg (l₃ c)])
    have := (min_le_right (l₁ x) (min (l₂ x) (l₃ x))).trans (min_le_left _ (l₃ x))
    linarith
  have ha₃ : 0 < l₃ x - ε * l₃ c := by
    have := hbd (l₃ c) (by simp only [hK]; linarith [abs_nonneg (l₂ c), abs_nonneg (l₁ c)])
    have := (min_le_right (l₁ x) (min (l₂ x) (l₃ x))).trans (min_le_right _ (l₃ x))
    linarith
  refine ⟨fun w => ε / n + (if w = p₁ then l₁ x - ε * l₁ c else 0)
      + (if w = p₂ then l₂ x - ε * l₂ c else 0) + (if w = p₃ then l₃ x - ε * l₃ c else 0),
    ?_, ?_, ?_⟩
  · intro w _
    have : 0 < ε / n := by positivity
    have t1 : 0 ≤ (if w = p₁ then l₁ x - ε * l₁ c else 0) := by split_ifs <;> linarith
    have t2 : 0 ≤ (if w = p₂ then l₂ x - ε * l₂ c else 0) := by split_ifs <;> linarith
    have t3 : 0 ≤ (if w = p₃ then l₃ x - ε * l₃ c else 0) := by split_ifs <;> linarith
    linarith
  · simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.sum_ite_eq', h₁, h₂,
      h₃, ite_true]
    rw [← hn]
    have := hsum c
    have : n ≠ 0 := hnpos.ne'
    field_simp
    nlinarith [hsum x, hsum c]
  · have hcsum : ε • c = ∑ w ∈ V, (ε / n) • φ w := by
      rw [hc, Finset.smul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [smul_smul]; congr 1; field_simp
    simp only [add_smul, Finset.sum_add_distrib, ite_smul, zero_smul, Finset.sum_ite_eq', h₁, h₂,
      h₃, ite_true]
    rw [← hcsum]
    have e1 := hrec x
    have e2 := hrec c
    rw [sub_smul, sub_smul, sub_smul, mul_smul, mul_smul, mul_smul]
    have : ε • c = ε • (l₁ c • proj_xy (R₂.toEuclideanLin p₁) + l₂ c • proj_xy (R₂.toEuclideanLin p₂)
      + l₃ c • proj_xy (R₂.toEuclideanLin p₃)) := by rw [e2]
    rw [smul_add, smul_add] at this
    rw [this]
    conv_lhs => rw [← e1]
    abel

theorem proj_frameMat (u u' v : ℝ³) :
    proj_xy ((frameMat u u').toEuclideanLin v) = !₂[⟪u, v⟫, ⟪u', v⟫] := by
  have h0 : (Matrix.toEuclideanLin (frameMat u u') v) 0 = ⟪u, v⟫ := by
    simp [frameMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three, PiLp.inner_apply]; ring
  have h1 : (Matrix.toEuclideanLin (frameMat u u') v) 1 = ⟪u', v⟫ := by
    simp [frameMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three, PiLp.inner_apply]; ring
  ext i
  fin_cases i
  · simpa [proj_xy] using h0
  · simpa [proj_xy] using h1

/-- **Plate rule (glob rule P, Lemma F), triangle form.**  Inner view: all vertices lie in the box
`⟪e,v⟫ ∈ [a,a+μ]`, `⟪n,v⟫ ∈ [b,b+w]`.  Outer view: orthonormal `u, u'`; three vertices project
to `(x₀,y₀)`, `(x₀+D,y₀)` (base of length `D`) and `(x₃,y₀+h)` (apex at height `h`, foot
`x₃ ∈ [x₀, x₀+D]`).  If `μ/D + w/h < 1`, a `μ × w` rectangle fits strictly inside the triangle. -/
theorem boxApplies_of_plate_triangle (V : Finset ℝ³)
    (e n u u' : ℝ³) (hee : ⟪e, e⟫ = 1) (hnn : ⟪n, n⟫ = 1) (hen : ⟪e, n⟫ = 0)
    (huu : ⟪u, u⟫ = 1) (hu'u' : ⟪u', u'⟫ = 1) (huu' : ⟪u, u'⟫ = 0)
    (a b μ w D h x₀ y₀ x₃ : ℝ) (hμ : 0 < μ) (hw : 0 < w) (hD : 0 < D) (hh : 0 < h)
    (hbox : ∀ v ∈ V, a ≤ ⟪e, v⟫ ∧ ⟪e, v⟫ ≤ a + μ ∧ b ≤ ⟪n, v⟫ ∧ ⟪n, v⟫ ≤ b + w)
    (p₁ p₂ p₃ : ℝ³) (h₁ : p₁ ∈ V) (h₂ : p₂ ∈ V) (h₃ : p₃ ∈ V)
    (hp₁ : ⟪u, p₁⟫ = x₀ ∧ ⟪u', p₁⟫ = y₀)
    (hp₂ : ⟪u, p₂⟫ = x₀ + D ∧ ⟪u', p₂⟫ = y₀)
    (hp₃ : ⟪u, p₃⟫ = x₃ ∧ ⟪u', p₃⟫ = y₀ + h)
    (hx₃ : x₀ ≤ x₃ ∧ x₃ ≤ x₀ + D)
    (hsmall : μ / D + w / h < 1) :
    BoxApplies V := by
  have hR₂ := frameMat_mem_SO3 u u' huu hu'u' huu'
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = μ / D := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = w / h := ⟨_, rfl⟩
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = (x₃ - x₀) / D := ⟨_, rfl⟩
  have hμ' : μ = ρ * D := by rw [hρ]; field_simp
  have hw' : w = r * h := by rw [hr]; field_simp
  have hx' : x₃ = x₀ + θ * D := by rw [hθ]; field_simp; ring
  have hρ0 : 0 < ρ := by rw [hρ]; positivity
  have hr0 : 0 < r := by rw [hr]; positivity
  have hθ0 : 0 ≤ θ := by rw [hθ]; exact div_nonneg (by linarith [hx₃.1]) hD.le
  have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one hD]; linarith [hx₃.2]
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = 1 - ρ - r := ⟨_, rfl⟩
  have hσ0 : 0 < σ := by rw [hσ, hρ, hr]; linarith
  let l₃ : ℝ² → ℝ := fun z => (z 1 - y₀) / h
  let l₂ : ℝ² → ℝ := fun z => (z 0 - x₀ - l₃ z * (x₃ - x₀)) / D
  let l₁ : ℝ² → ℝ := fun z => 1 - l₂ z - l₃ z
  refine ⟨e, n, hee, hnn, hen, frameMat u u', hR₂, a, b, μ, w,
    x₀ + (σ / 2 + r) * (θ * D) + D * σ / 4, y₀ + σ * h / 2, μ, w, hμ, hw, le_rfl, le_rfl, hbox, ?_⟩
  intro s t hs ht
  have hs' : 0 ≤ s ∧ s ≤ 1 := by rcases hs with rfl | rfl <;> norm_num
  have ht' : 0 ≤ t ∧ t ≤ 1 := by rcases ht with rfl | rfl <;> norm_num
  have e3 : l₃ !₂[x₀ + (σ / 2 + r) * (θ * D) + D * σ / 4 + s * μ, y₀ + σ * h / 2 + t * w]
      = σ / 2 + t * r := by
    simp only [l₃]; simp; rw [hw']; field_simp; ring
  have e2 : l₂ !₂[x₀ + (σ / 2 + r) * (θ * D) + D * σ / 4 + s * μ, y₀ + σ * h / 2 + t * w]
      = (1 - t) * r * θ + σ / 4 + s * ρ := by
    simp only [l₂]; rw [e3]; simp; rw [hμ', hx']; field_simp; ring
  refine posComb_of_bary V (frameMat u u') p₁ p₂ p₃ h₁ h₂ h₃ l₁ l₂ l₃ ?_ ?_ _ ?_ ?_ ?_
  · intro z; simp only [l₁]; ring
  · intro z
    rw [proj_frameMat, proj_frameMat, proj_frameMat, hp₁.1, hp₁.2, hp₂.1, hp₂.2, hp₃.1, hp₃.2]
    ext i
    fin_cases i
    · simp only [l₁, l₂, l₃]
      simp
      field_simp
      ring
    · simp only [l₁, l₂, l₃]
      simp
      field_simp
      ring
  · simp only [l₁]; rw [e2, e3]
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 ht'.2) hr0.le) hθ0,
      mul_nonneg (sub_nonneg.2 ht'.2) hr0.le, mul_nonneg ht'.1 hr0.le,
      mul_nonneg (sub_nonneg.2 hθ1) (mul_nonneg (sub_nonneg.2 ht'.2) hr0.le),
      mul_nonneg (sub_nonneg.2 hs'.2) hρ0.le]
  · rw [e2]
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 ht'.2) hr0.le) hθ0, mul_nonneg hs'.1 hρ0.le]
  · rw [e3]
    nlinarith [mul_nonneg ht'.1 hr0.le]

/-- **Plate rule, triangle form** (see `boxApplies_of_plate_triangle`): `V` is Rupert. -/
theorem isRupert_of_plate_triangle (V : Finset ℝ³)
    (hsol : (interior (convexHull ℝ (V : Set ℝ³))).Nonempty)
    (e n u u' : ℝ³) (hee : ⟪e, e⟫ = 1) (hnn : ⟪n, n⟫ = 1) (hen : ⟪e, n⟫ = 0)
    (huu : ⟪u, u⟫ = 1) (hu'u' : ⟪u', u'⟫ = 1) (huu' : ⟪u, u'⟫ = 0)
    (a b μ w D h x₀ y₀ x₃ : ℝ) (hμ : 0 < μ) (hw : 0 < w) (hD : 0 < D) (hh : 0 < h)
    (hbox : ∀ v ∈ V, a ≤ ⟪e, v⟫ ∧ ⟪e, v⟫ ≤ a + μ ∧ b ≤ ⟪n, v⟫ ∧ ⟪n, v⟫ ≤ b + w)
    (p₁ p₂ p₃ : ℝ³) (h₁ : p₁ ∈ V) (h₂ : p₂ ∈ V) (h₃ : p₃ ∈ V)
    (hp₁ : ⟪u, p₁⟫ = x₀ ∧ ⟪u', p₁⟫ = y₀)
    (hp₂ : ⟪u, p₂⟫ = x₀ + D ∧ ⟪u', p₂⟫ = y₀)
    (hp₃ : ⟪u, p₃⟫ = x₃ ∧ ⟪u', p₃⟫ = y₀ + h)
    (hx₃ : x₀ ≤ x₃ ∧ x₃ ≤ x₀ + D)
    (hsmall : μ / D + w / h < 1) :
    IsRupert V :=
  isRupert_of_boxApplies V hsol
    (boxApplies_of_plate_triangle V e n u u' hee hnn hen huu hu'u' huu' a b μ w D h x₀ y₀ x₃ hμ hw
      hD hh hbox p₁ p₂ p₃ h₁ h₂ h₃ hp₁ hp₂ hp₃ hx₃ hsmall)

/-- The plate rule applies to `V`: all the data and hypotheses of `isRupert_of_plate_triangle`
other than the interior hypothesis. -/
def PlateApplies (V : Finset ℝ³) : Prop :=
  ∃ (e n u u' : ℝ³), ⟪e, e⟫ = 1 ∧ ⟪n, n⟫ = 1 ∧ ⟪e, n⟫ = 0 ∧
    ⟪u, u⟫ = 1 ∧ ⟪u', u'⟫ = 1 ∧ ⟪u, u'⟫ = 0 ∧
    ∃ (a b μ w D h x₀ y₀ x₃ : ℝ), 0 < μ ∧ 0 < w ∧ 0 < D ∧ 0 < h ∧
      (∀ v ∈ V, a ≤ ⟪e, v⟫ ∧ ⟪e, v⟫ ≤ a + μ ∧ b ≤ ⟪n, v⟫ ∧ ⟪n, v⟫ ≤ b + w) ∧
      ∃ p₁ p₂ p₃ : ℝ³, p₁ ∈ V ∧ p₂ ∈ V ∧ p₃ ∈ V ∧
        (⟪u, p₁⟫ = x₀ ∧ ⟪u', p₁⟫ = y₀) ∧
        (⟪u, p₂⟫ = x₀ + D ∧ ⟪u', p₂⟫ = y₀) ∧
        (⟪u, p₃⟫ = x₃ ∧ ⟪u', p₃⟫ = y₀ + h) ∧
        (x₀ ≤ x₃ ∧ x₃ ≤ x₀ + D) ∧ μ / D + w / h < 1

/-- The plate rule is an instance of the box lemma. -/
theorem plateApplies_boxApplies {V : Finset ℝ³} (h : PlateApplies V) : BoxApplies V := by
  obtain ⟨e, n, u, u', hee, hnn, hen, huu, hu'u', huu', a, b, μ, w, D, h, x₀, y₀, x₃, hμ, hw, hD,
    hh, hbox, p₁, p₂, p₃, h₁, h₂, h₃, hp₁, hp₂, hp₃, hx₃, hsmall⟩ := h
  exact boxApplies_of_plate_triangle V e n u u' hee hnn hen huu hu'u' huu' a b μ w D h x₀ y₀ x₃
    hμ hw hD hh hbox p₁ p₂ p₃ h₁ h₂ h₃ hp₁ hp₂ hp₃ hx₃ hsmall

/-- If the plate rule applies to `V` (and `V` is solid), `V` is Rupert. -/
theorem isRupert_of_plateApplies (V : Finset ℝ³)
    (hsol : (interior (convexHull ℝ (V : Set ℝ³))).Nonempty) (h : PlateApplies V) :
    IsRupert V := by
  obtain ⟨e, n, u, u', hee, hnn, hen, huu, hu'u', huu', a, b, μ, w, D, h, x₀, y₀, x₃, hμ, hw, hD,
    hh, hbox, p₁, p₂, p₃, h₁, h₂, h₃, hp₁, hp₂, hp₃, hx₃, hsmall⟩ := h
  exact isRupert_of_plate_triangle V hsol e n u u' hee hnn hen huu hu'u' huu' a b μ w D h x₀ y₀ x₃
    hμ hw hD hh hbox p₁ p₂ p₃ h₁ h₂ h₃ hp₁ hp₂ hp₃ hx₃ hsmall

/-- **Plate rule, P0 form.**  If the apex height satisfies `μ ≤ 2h` (as when `μ` is the minimum
width and `h` is at least half of it), then `2w/μ + μ/D < 1` suffices.  (`μ ≤ 2h` is the only use of
the minimal-width property.) -/
theorem isRupert_of_plate_P0 (V : Finset ℝ³)
    (hsol : (interior (convexHull ℝ (V : Set ℝ³))).Nonempty)
    (e n u u' : ℝ³) (hee : ⟪e, e⟫ = 1) (hnn : ⟪n, n⟫ = 1) (hen : ⟪e, n⟫ = 0)
    (huu : ⟪u, u⟫ = 1) (hu'u' : ⟪u', u'⟫ = 1) (huu' : ⟪u, u'⟫ = 0)
    (a b μ w D h x₀ y₀ x₃ : ℝ) (hμ : 0 < μ) (hw : 0 < w) (hD : 0 < D) (hh : 0 < h)
    (hbox : ∀ v ∈ V, a ≤ ⟪e, v⟫ ∧ ⟪e, v⟫ ≤ a + μ ∧ b ≤ ⟪n, v⟫ ∧ ⟪n, v⟫ ≤ b + w)
    (p₁ p₂ p₃ : ℝ³) (h₁ : p₁ ∈ V) (h₂ : p₂ ∈ V) (h₃ : p₃ ∈ V)
    (hp₁ : ⟪u, p₁⟫ = x₀ ∧ ⟪u', p₁⟫ = y₀)
    (hp₂ : ⟪u, p₂⟫ = x₀ + D ∧ ⟪u', p₂⟫ = y₀)
    (hp₃ : ⟪u, p₃⟫ = x₃ ∧ ⟪u', p₃⟫ = y₀ + h)
    (hx₃ : x₀ ≤ x₃ ∧ x₃ ≤ x₀ + D)
    (hhμ : μ ≤ 2 * h) (hsmall : 2 * w / μ + μ / D < 1) :
    IsRupert V := by
  refine isRupert_of_plate_triangle V hsol e n u u' hee hnn hen huu hu'u' huu' a b μ w D h x₀ y₀ x₃
    hμ hw hD hh hbox p₁ p₂ p₃ h₁ h₂ h₃ hp₁ hp₂ hp₃ hx₃ ?_
  have : w / h ≤ 2 * w / μ := by
    rw [div_le_div_iff₀ hh hμ]; nlinarith
  linarith

/-- Satisfiability check: the thin triangular prism with vertices `(0|1, 0, 0)`, `(0|1, 4, 0)`,
`(0|1, 2, 16)` meets every hypothesis of the triangle form (`e = E₀`, `n = u = E₁`, `u' = E₂`,
`μ = 1`, `w = 4`, `D = 4`, `h = 16`, `x₃ = 2`, `μ/D + w/h = 1/2`), apart from the interior
hypothesis `hsol`, which holds because the prism has positive volume. -/
example (hsol : (interior (convexHull ℝ
      ((({!₂[0,0,0], !₂[0,4,0], !₂[0,2,16], !₂[1,0,0], !₂[1,4,0], !₂[1,2,16]} : Finset ℝ³)) :
        Set ℝ³))).Nonempty) :
    IsRupert ({!₂[0,0,0], !₂[0,4,0], !₂[0,2,16], !₂[1,0,0], !₂[1,4,0], !₂[1,2,16]} : Finset ℝ³) := by
  refine isRupert_of_plate_triangle _ hsol !₂[1,0,0] !₂[0,1,0] !₂[0,1,0] !₂[0,0,1]
    ?_ ?_ ?_ ?_ ?_ ?_ 0 0 1 4 4 16 0 0 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ?hbox !₂[0,0,0] !₂[0,4,0] !₂[0,2,16] ?_ ?_ ?_ ?_ ?_ ?_ (by norm_num) (by norm_num)
  case hbox =>
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial] <;>
      norm_num
  all_goals
    first
      | (simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
         norm_num)
      | simp

end Minimality

end
