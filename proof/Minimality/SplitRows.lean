module

public import Mathlib
public import Minimality.DepthSeparated
public import Minimality.Tilt

/-!
# Split rows give free views (Theorem 8.10, row form), on the Minimality side

The frame-free freedom machinery of `MinimalityExtra/DepthSeparated.lean`, moved here so that the
minimality proof (the SAT-route split leaf, `Minimality.SplitLeaf`) can use it without importing
`MinimalityExtra`. The definitions in `Minimality.Split` repeat the bodies of the
`MinimalityExtra` ones (`det3`, `TiltCert`, `FreeAt`, `StrictRimN`, `HiddenInTriangles`,
`levelPoint`, `IsDepthSeparatedAt`), so the two agree by `rfl`; `cross` is `Minimality.cross`,
which equals `MinimalityExtra.cross` by `rfl`. `MinimalityExtra/DepthSeparated.lean` restates every
lemma here under its old name.

* `freeAt_of_splitRows`: `SplitRows` (a product of two linear forms in the view per rim row) at a
  strict rim with hidden points in triangles gives `FreeAt` (Propeller Lemma, row form).
* `splitRows_of_isDepthSeparatedAt`: a split antipodal level pair gives split rows.
* `freeAt_of_pivot`: rotation about a line through a corner keeping both of its edges.
* `FreeAt.isRupert`: a free nonzero view gives `IsRupert` (via `Minimality.isRupert_of_tiltCert`).
-/

@[expose] public section

namespace Minimality.Split
open scoped RealInnerProductSpace
open Finset

/-- The determinant of `a`, `b`, `c`, in coordinates (body of `MinimalityExtra.det3`). -/
noncomputable def det3 (a b c : ℝ³) : ℝ :=
  (a 1 * b 2 - a 2 * b 1) * c 0 + (a 2 * b 0 - a 0 * b 2) * c 1 +
    (a 0 * b 1 - a 1 * b 0) * c 2

/-- `MinimalityExtra.TiltCert`, with the coordinate `det3`. -/
def TiltCert (V : Finset ℝ³) (w ω τ x : ℝ³) : Prop :=
  (∃ y₀ ∈ V, ∃ y₁ ∈ V, 0 < det3 (y₁ - x) (y₀ - x) w ∧
      0 < det3 (y₁ - x) (cross ω x + τ) w ∧ 0 < det3 (x - y₀) (cross ω x + τ) w) ∨
  (∃ a ∈ V, ∃ b ∈ V, ∃ c ∈ V, 0 < det3 (b - a) (c - a) w ∧ 0 < det3 (b - a) (x - a) w ∧
      0 < det3 (c - b) (x - b) w ∧ 0 < det3 (a - c) (x - c) w)

/-- The view `w` of `V` is *free* (`MinimalityExtra.FreeAt`). -/
def FreeAt (V : Finset ℝ³) (w : ℝ³) : Prop :=
  ∃ ω τ : ℝ³, ∀ y ∈ V, TiltCert V w ω τ y

/-- `MinimalityExtra.StrictRimN`: `lab` is the strict rim of the view `u`. -/
def StrictRimN {n k : ℕ} [NeZero k] (x : Fin n → ℝ³) (u : ℝ³) (lab : ZMod k → Fin n) : Prop :=
  ∀ (m : Fin n) (i : ZMod k), m ≠ lab i → m ≠ lab (i + 1) →
    0 < det3 (x (lab (i + 1)) - x (lab i)) (x m - x (lab i)) u

/-- `MinimalityExtra.levelPoint`. -/
noncomputable def levelPoint {k : ℕ} (X : ZMod k → ℝ³) (w : ℝ³) (a c : ZMod k) : ℝ³ :=
  X a + (⟪X c - X a, w⟫ / ⟪X (a + 1) - X a, w⟫) • (X (a + 1) - X a)

/-- `MinimalityExtra.HiddenInTriangles`: every point off the rim is strictly inside a projected
triangle of points. -/
def HiddenInTriangles {n k : ℕ} (x : Fin n → ℝ³) (w : ℝ³) (lab : ZMod k → Fin n) : Prop :=
  ∀ m, (∀ i, m ≠ lab i) → ∃ p ∈ Finset.univ.image x, ∃ q ∈ Finset.univ.image x, ∃ r ∈ Finset.univ.image x,
    0 < det3 (q - p) (r - p) w ∧ 0 < det3 (q - p) (x m - p) w ∧
    0 < det3 (r - q) (x m - q) w ∧ 0 < det3 (p - r) (x m - r) w

/-- `MinimalityExtra.IsDepthSeparatedAt`: a split antipodal level pair. -/
def IsDepthSeparatedAt {k : ℕ} (X : ZMod k → ℝ³) (w : ℝ³) (a c : ZMod k) : Prop :=
  (∀ i, i ≠ c → det3 (X (a + 1) - X a) w (X c) < det3 (X (a + 1) - X a) w (X i)) ∧
    (((∀ s : ℕ, 0 < s → s ≤ (a - c).val → ⟪X c, w⟫ < ⟪X (c + s), w⟫) ∧
        ∀ s : ℕ, (a - c).val < s → s < k → ⟪X (c + s), w⟫ < ⟪X c, w⟫) ∨
      ((∀ s : ℕ, 0 < s → s ≤ (a - c).val → ⟪X (c + s), w⟫ < ⟪X c, w⟫) ∧
        ∀ s : ℕ, (a - c).val < s → s < k → ⟪X c, w⟫ < ⟪X (c + s), w⟫))

theorem inner3 (a b : ℝ³) : ⟪a, b⟫ = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three]; ring

@[simp] theorem cross_0 (a b : ℝ³) : cross a b 0 = a 1 * b 2 - a 2 * b 1 := by simp [cross]
@[simp] theorem cross_1 (a b : ℝ³) : cross a b 1 = a 2 * b 0 - a 0 * b 2 := by simp [cross]
@[simp] theorem cross_2 (a b : ℝ³) : cross a b 2 = a 0 * b 1 - a 1 * b 0 := by simp [cross]

/-- Row form of a split antipodal level pair `(edge a, corner c)` of the cycle `X` at the view
`w`, with orientation `σ`.  For every rim edge `i` other than `a` and every end `j ≠ c` of it,
the depth `⟪X j - X c, w⟫` and the rise `det3 (X (i+1) - X i) d w` of the height
`det3 d w ·` (`d` the edge `a`) along edge `i` have the sign product `σ`. -/
def SplitRows {k : ℕ} (X : ZMod k → ℝ³) (w : ℝ³) (a c : ZMod k) (σ : ℝ) : Prop :=
  ∀ i j : ZMod k, i ≠ a → (j = i ∨ j = i + 1) → j ≠ c →
    0 < σ * (⟪X j - X c, w⟫ * det3 (X (i + 1) - X i) (X (a + 1) - X a) w)

/-- Motion 1: turning about the horizontal axis through `X c` normal to the support planes. -/
theorem col_turn (E d w y C : ℝ³) :
    det3 E (cross (cross w d) y + (-⟪C, w⟫) • d) w = ⟪y - C, w⟫ * det3 E d w := by
  simp only [det3, inner3, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, cross_0, cross_1,
    cross_2, smul_eq_mul]
  ring

/-- Motion 2 in general: constant `T` at `C`, spin `θ`, normal shear `β`. -/
theorem col_fix (E d w y C T : ℝ³) (θ β : ℝ) :
    det3 E (cross (θ • w + β • cross w (cross d w)) y +
        (T - θ • cross w C - (β * ⟪C, w⟫) • cross d w)) w =
      det3 E T w + θ * det3 E (cross w (y - C)) w + β * ⟪y - C, w⟫ * det3 E (cross d w) w := by
  simp only [det3, inner3, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, cross_0, cross_1,
    cross_2, smul_eq_mul]
  ring

theorem det3_sum_motion (E w y ω₁ τ₁ ω₂ τ₂ : ℝ³) (L : ℝ) :
    det3 E (cross (L • ω₁ + ω₂) y + (L • τ₁ + τ₂)) w =
      L * det3 E (cross ω₁ y + τ₁) w + det3 E (cross ω₂ y + τ₂) w := by
  simp only [det3, PiLp.add_apply, PiLp.smul_apply, cross_0, cross_1, cross_2, smul_eq_mul]
  ring

/-- Motion 2 on the edge line: the value is constant. -/
theorem col_edge (d w u T : ℝ³) (D ρ s : ℝ) (hD : D ≠ 0) (hDw : ⟪d, w⟫ = D)
    (hρ : ⟪u, d⟫ - s * ⟪d, d⟫ = ρ) (hs : ⟪u, w⟫ = s * D) (θ : ℝ) :
    det3 d T w + θ * det3 d (cross w u) w + (θ / D) * ⟪u, w⟫ * det3 d (cross d w) w =
      det3 d T w + θ * (⟪w, w⟫ * ρ) := by
  have e1 : det3 d (cross w u) w = ⟪w, w⟫ * ⟪u, d⟫ - ⟪u, w⟫ * ⟪d, w⟫ := by
    simp only [det3, inner3, cross_0, cross_1, cross_2]; ring
  have e2 : det3 d (cross d w) w = ⟪d, w⟫ * ⟪d, w⟫ - ⟪w, w⟫ * ⟪d, d⟫ := by
    simp only [det3, inner3, cross_0, cross_1, cross_2]; ring
  rw [e1, e2, hs, hDw, ← hρ]
  field_simp
  ring

/-- Large multiples win. -/
theorem exists_large {ι : Type*} [Finite ι] (p q : ι → ℝ)
    (h : ∀ t, 0 < p t ∨ (p t = 0 ∧ 0 < q t)) : ∃ L : ℝ, ∀ t, 0 < L * p t + q t := by
  have : ∀ᶠ L : ℝ in Filter.atTop, ∀ t, 0 < L * p t + q t := by
    rw [Filter.eventually_all]
    intro t
    rcases h t with hp | ⟨hp, hq⟩
    · filter_upwards [Filter.eventually_gt_atTop (-q t / p t)] with L hL
      have := (div_lt_iff₀ hp).1 hL
      linarith
    · exact Filter.Eventually.of_forall fun L => by simpa [hp] using hq
  exact this.exists

theorem zmod_pred_ne_succ {k : ℕ} [NeZero k] (hk : 3 ≤ k) (i : ZMod k) : i - 1 ≠ i + 1 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod k) = 0 := by
    have : (i + 1) - (i - 1) = 0 := by rw [← h]; ring
    have e : (i + 1) - (i - 1) = ((2 : ℕ) : ZMod k) := by push_cast; ring
    rw [← e, this]
  rw [ZMod.natCast_eq_zero_iff] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  omega

/-- **Propeller Lemma, row form, with an explicit motion on the rim.** -/
theorem exists_motion_of_splitRows {n k : ℕ} [NeZero k] (hk : 3 ≤ k) (x : Fin n → ℝ³) (w : ℝ³)
    (lab : ZMod k → Fin n) (hinj : Function.Injective lab) (hrim : StrictRimN x w lab)
    (a c : ZMod k) (σ : ℝ)
    (hrows : SplitRows (fun i => x (lab i)) w a c σ)
    (hD : ⟪x (lab (a + 1)) - x (lab a), w⟫ ≠ 0)
    (hnd : ⟪levelPoint (fun i => x (lab i)) w a c - x (lab c),
      x (lab (a + 1)) - x (lab a)⟫ ≠ 0) :
    ∃ ω τ : ℝ³, ∀ i : ZMod k,
      0 < det3 (x (lab (i + 1)) - x (lab i)) (cross ω (x (lab i)) + τ) w ∧
      0 < det3 (x (lab (i + 1)) - x (lab i)) (cross ω (x (lab (i + 1))) + τ) w := by
  set X : ZMod k → ℝ³ := fun i => x (lab i) with hX
  set d := X (a + 1) - X a with hd
  set D := ⟪d, w⟫ with hDdef
  set C := X c with hC
  set A := X (c + 1) - C with hA
  set B := X (c - 1) - C with hB
  set q := levelPoint X w a c with hq
  set ρ := ⟪q - C, d⟫ with hρ
  have hne : ∀ i, lab (i - 1) ≠ lab (i + 1) ∧ lab (i - 1) ≠ lab i := fun i =>
    ⟨fun h => zmod_pred_ne_succ hk i (hinj h), fun h => by
      have := hinj h
      have h1 : (1 : ZMod k) = 0 := by
        have : i - (i - 1) = 0 := by rw [this]; ring
        simpa using this
      have hf : Fact (1 < k) := ⟨by omega⟩
      exact one_ne_zero h1⟩
  have hP : 0 < det3 A B w := hrim (lab (c - 1)) c (hne c).2 (hne c).1
  have hw : ⟪w, w⟫ ≠ 0 := by
    intro h0
    have : w = 0 := inner_self_eq_zero.1 h0
    rw [this] at hP
    simp [det3] at hP
  -- the two motions
  set T := A + B with hT
  set G := det3 d T w with hG
  set θ := (1 - G) / (⟪w, w⟫ * ρ) with hθ
  set β := θ / D with hβ
  set ω₁ := cross w d with hω₁
  set τ₁ := (-⟪C, w⟫) • d with hτ₁
  set ω₂ := θ • w + β • cross w (cross d w) with hω₂
  set τ₂ := T - θ • cross w C - (β * ⟪C, w⟫) • cross d w with hτ₂
  have hsum : ∀ (L : ℝ) (E y : ℝ³),
      det3 E (cross ((L * σ) • ω₁ + ω₂) y + ((L * σ) • τ₁ + τ₂)) w =
        L * (σ * (⟪y - C, w⟫ * det3 E d w)) + det3 E (cross ω₂ y + τ₂) w := by
    intro L E y
    rw [det3_sum_motion, hω₁, hτ₁, col_turn]
    ring
  have hfix : ∀ E y : ℝ³, det3 E (cross ω₂ y + τ₂) w =
      det3 E T w + θ * det3 E (cross w (y - C)) w + β * ⟪y - C, w⟫ * det3 E (cross d w) w :=
    fun E y => col_fix E d w y C T θ β
  have hρ0 : ρ ≠ 0 := hnd
  -- the two end points of the edge
  have hedge : ∀ (y : ℝ³) (s : ℝ), y - C - s • d = q - C → ⟪y - C, w⟫ = s * D →
      det3 d (cross ω₂ y + τ₂) w = 1 := by
    intro y s h1 h2
    have hρ' : ⟪y - C, d⟫ - s * ⟪d, d⟫ = ρ := by
      rw [hρ, ← h1, inner_sub_left (𝕜 := ℝ) (y - C) (s • d) d, real_inner_smul_left]
    rw [hfix, col_edge d w (y - C) T D ρ s hD rfl hρ' h2 θ, hθ]
    field_simp
    ring
  have hqdef : q = X a + (⟪C - X a, w⟫ / D) • d := rfl
  have hzs : ⟪C - X a, w⟫ / D = -(⟪X a - C, w⟫ / D) := by
    rw [← neg_div, ← inner_neg_left, neg_sub]
  have hXa : det3 d (cross ω₂ (X a) + τ₂) w = 1 := by
    refine hedge (X a) (⟪X a - C, w⟫ / D) ?_ ?_
    · rw [hqdef, hzs]; module
    · field_simp
  have hXa1 : det3 d (cross ω₂ (X (a + 1)) + τ₂) w = 1 := by
    refine hedge (X (a + 1)) (⟪X a - C, w⟫ / D + 1) ?_ ?_
    · have : X (a + 1) = X a + d := by rw [hd]; abel
      rw [hqdef, hzs, this]; module
    · have : X (a + 1) - C = (X a - C) + d := by rw [hd]; abel
      rw [this, inner_add_left, add_mul, one_mul, div_mul_cancel₀ _ hD]
  have hCcol : ∀ E : ℝ³, det3 E (cross ω₂ C + τ₂) w = det3 E T w := by
    intro E
    rw [hfix]
    simp only [sub_self, inner_zero_left, mul_zero, zero_mul, add_zero]
    simp [det3, cross]
  have hAT : det3 A T w = det3 A B w := by
    simp only [hT, det3, PiLp.add_apply]; ring
  have hBT : det3 (C - X (c - 1)) T w = det3 A B w := by
    have : C - X (c - 1) = -B := by rw [hB]; abel
    rw [this]
    simp only [hT, det3, PiLp.add_apply, PiLp.neg_apply]; ring
  -- the choice of the large multiple
  let J : ZMod k × Bool → ZMod k := fun t => if t.2 then t.1 + 1 else t.1
  let Ed : ZMod k × Bool → ℝ³ := fun t => X (t.1 + 1) - X t.1
  obtain ⟨L, hL⟩ := exists_large (ι := ZMod k × Bool)
    (fun t => σ * (⟪X (J t) - C, w⟫ * det3 (Ed t) d w))
    (fun t => det3 (Ed t) (cross ω₂ (X (J t)) + τ₂) w) (by
      rintro ⟨i, b⟩
      by_cases hi : i = a
      · subst hi
        right
        refine ⟨by simp only [Ed, ← hd]; simp [det3]; ring_nf; simp, ?_⟩
        cases b
        · simp only [J, Ed, ← hd]; simp only [Bool.false_eq_true, ite_false]; rw [hXa]; norm_num
        · simp only [J, Ed, ← hd]; simp only [ite_true]; rw [hXa1]; norm_num
      · by_cases hj : J (i, b) = c
        · right
          refine ⟨by rw [hj]; simp [hC], ?_⟩
          rw [hj, hCcol]
          cases b
          · have : i = c := hj
            subst this
            simp only [Ed]
            rw [show X (i + 1) - X i = A from rfl, hAT]; exact hP
          · have : i + 1 = c := hj
            have hi' : i = c - 1 := by rw [← this]; ring
            subst hi'
            simp only [Ed]
            rw [show c - 1 + 1 = c by ring, hBT]; exact hP
        · left
          refine hrows i (J (i, b)) hi ?_ hj
          cases b
          · exact Or.inl rfl
          · exact Or.inr rfl)
  refine ⟨(L * σ) • ω₁ + ω₂, (L * σ) • τ₁ + τ₂, fun i => ⟨?_, ?_⟩⟩
  · have := hL (i, false)
    rw [hsum]; exact this
  · have := hL (i, true)
    rw [hsum]; exact this

/-- A motion strictly inward at both ends of every rim edge gives `FreeAt`. -/
theorem freeAt_of_rimMotion {n k : ℕ} [NeZero k] (hk : 3 ≤ k) (x : Fin n → ℝ³) (w : ℝ³)
    (lab : ZMod k → Fin n) (hinj : Function.Injective lab) (hrim : StrictRimN x w lab)
    (hhid : HiddenInTriangles x w lab)
    (hm : ∃ ω τ : ℝ³, ∀ i : ZMod k,
      0 < det3 (x (lab (i + 1)) - x (lab i)) (cross ω (x (lab i)) + τ) w ∧
      0 < det3 (x (lab (i + 1)) - x (lab i)) (cross ω (x (lab (i + 1))) + τ) w) :
    FreeAt (univ.image x) w := by
  obtain ⟨ω, τ, h⟩ := hm
  refine ⟨ω, τ, fun y hy => ?_⟩
  obtain ⟨m, -, rfl⟩ := mem_image.1 hy
  by_cases hm : ∃ i, m = lab i
  · obtain ⟨i, rfl⟩ := hm
    left
    have hp : lab (i - 1) ≠ lab i ∧ lab (i - 1) ≠ lab (i + 1) := by
      refine ⟨fun e => ?_, fun e => zmod_pred_ne_succ hk i (hinj e)⟩
      have h1 : i - (i - 1) = 0 := by rw [hinj e]; ring
      have : (1 : ZMod k) = 0 := by simpa using h1
      have hf : Fact (1 < k) := ⟨by omega⟩
      exact one_ne_zero this
    refine ⟨x (lab (i - 1)), mem_image_of_mem x (mem_univ _), x (lab (i + 1)),
      mem_image_of_mem x (mem_univ _), hrim _ i hp.1 hp.2, (h i).1, ?_⟩
    have := (h (i - 1)).2
    rwa [show i - 1 + 1 = i by ring] at this
  · push Not at hm
    right
    exact hhid m hm

/-- **Propeller Lemma, row form.** -/
theorem freeAt_of_splitRows {n k : ℕ} [NeZero k] (hk : 3 ≤ k) (x : Fin n → ℝ³) (w : ℝ³)
    (lab : ZMod k → Fin n) (hinj : Function.Injective lab) (hrim : StrictRimN x w lab)
    (hhid : HiddenInTriangles x w lab) (a c : ZMod k) (σ : ℝ)
    (hrows : SplitRows (fun i => x (lab i)) w a c σ)
    (hD : ⟪x (lab (a + 1)) - x (lab a), w⟫ ≠ 0)
    (hnd : ⟪levelPoint (fun i => x (lab i)) w a c - x (lab c),
      x (lab (a + 1)) - x (lab a)⟫ ≠ 0) :
    FreeAt (univ.image x) w :=
  freeAt_of_rimMotion hk x w lab hinj hrim hhid
    (exists_motion_of_splitRows hk x w lab hinj hrim a c σ hrows hD hnd)


/-- The planar projection used for the monotonicity facts. -/
noncomputable def projP (N w : ℝ³) (e : ℝ³) : ℝ² := !₂[⟪e, N⟫, ⟪e, cross w N⟫]

theorem projP_sub (N w e f : ℝ³) : projP N w e - projP N w f = projP N w (e - f) := by
  ext i; fin_cases i <;> simp [projP, inner_sub_left]

theorem cross2_projP (d w e f : ℝ³) :
    Minimality.cross2 (projP (cross d w) w e) (projP (cross d w) w f) =
      ⟪cross d w, cross d w⟫ * det3 e f w := by
  simp only [Minimality.cross2, projP, inner3, cross_0, cross_1, cross_2, det3]
  simp
  ring

theorem det3_eq_inner (d w x : ℝ³) : det3 d w x = ⟪cross d w, x⟫ := by
  simp only [det3, inner3, cross_0, cross_1, cross_2]

theorem det3_rot (D d w : ℝ³) : det3 D d w = det3 d w D := by
  simp only [det3]; ring

theorem val_succ_sub {k : ℕ} [NeZero k] (hk : 3 ≤ k) (i c : ZMod k) (h : i + 1 ≠ c) :
    (i + 1 - c).val = (i - c).val + 1 ∧ (i - c).val + 1 < k := by
  haveI : Fact (1 < k) := ⟨by omega⟩
  have e : i + 1 - c = (i - c) + 1 := by ring
  have hne : (i + 1 - c).val ≠ 0 := fun h0 => h (by
    have := (ZMod.val_eq_zero _).1 h0; exact sub_eq_zero.1 this)
  have hlt := ZMod.val_lt (i - c)
  rw [e, ZMod.val_add, ZMod.val_one] at hne ⊢
  by_cases hc : (i - c).val + 1 < k
  · rw [Nat.mod_eq_of_lt hc]; exact ⟨rfl, hc⟩
  · exfalso; apply hne
    have : (i - c).val + 1 = k := by omega
    rw [this, Nat.mod_self]

/-- Arcs give rows. -/
theorem splitRows_of_isDepthSeparatedAt {n k : ℕ} [NeZero k] (hk : 3 ≤ k) (x : Fin n → ℝ³) (w : ℝ³)
    (lab : ZMod k → Fin n) (hinj : Function.Injective lab) (hrim : StrictRimN x w lab)
    (a c : ZMod k) (hs : IsDepthSeparatedAt (fun i => x (lab i)) w a c) :
    (∃ σ : ℝ, SplitRows (fun i => x (lab i)) w a c σ) ∧
      ⟪x (lab (a + 1)) - x (lab a), w⟫ ≠ 0 := by
  obtain ⟨hmin, harcs⟩ := hs
  set X : ZMod k → ℝ³ := fun i => x (lab i) with hX
  set d : ℝ³ := X (a + 1) - X a with hd
  set N : ℝ³ := cross d w with hN
  set nn : ℝ := ⟪N, N⟫ with hnn
  set p : ZMod k → ℝ² := fun i => projP N w (X i) with hp
  have hk1 : (c + 1 : ZMod k) ≠ c := by
    intro h; exact Minimality.zmod_ne_add_one (by omega) c (by rw [add_comm] at h; simpa using h)
  have hmin' : ∀ i, i ≠ c → ⟪N, X c⟫ < ⟪N, X i⟫ := fun i hi => by
    have := hmin i hi; rwa [det3_eq_inner, det3_eq_inner] at this
  have hnn0 : 0 < nn := by
    rcases (real_inner_self_nonneg (x := N)).lt_or_eq with h | h
    · exact h
    · exfalso
      have : N = 0 := inner_self_eq_zero.1 h.symm
      have := hmin' (c + 1) hk1
      rw [‹N = 0›] at this; simp at this
  have hh : ∀ i, p i 0 = ⟪X i, N⟫ := fun i => by simp [hp, projP]
  have hh' : ∀ i, ⟪N, X i⟫ = p i 0 := fun i => by rw [hh, real_inner_comm]
  have hpoly : ∀ e f : ℝ³, Minimality.cross2 (projP N w e) (projP N w f) = nn * det3 e f w :=
    fun e f => cross2_projP d w e f
  have hccw : Minimality.IsCcwPolygon p := by
    refine ⟨hk, fun i j hji hj1 => ?_⟩
    have hr := hrim (lab j) i (fun e => hji (hinj e)) (fun e => hj1 (hinj e))
    rw [hp]; simp only []
    rw [projP_sub, projP_sub, hpoly]
    exact mul_pos hnn0 hr
  -- the edge a
  have hd0 : ⟪d, N⟫ = 0 := by
    simp only [hN, hd, inner3, cross_0, cross_1, cross_2]; ring
  have hd1 : ⟪d, cross w N⟫ = nn := by
    simp only [hnn, hN, hd, inner3, cross_0, cross_1, cross_2]; ring
  have hΔ : p (a + 1) - p a = !₂[0, nn] := by
    rw [hp]; simp only []
    rw [projP_sub]
    ext i; fin_cases i <;> simp [projP] <;> first | exact hd0 | exact hd1
  have hflat : p (a + 1) 0 = p a 0 := by
    have := congrArg (fun v => v 0) hΔ; simp at this; linarith
  have hon : Minimality.outNormal (p a) (p (a + 1)) = !₂[nn, 0] := by
    rw [Minimality.outNormal, hΔ]; ext i; fin_cases i <;> simp
  have hcone : -Minimality.outNormal (p a) (p (a + 1)) ∈
      Minimality.normalConeAt (convexHull ℝ (Set.range p)) (p c) := by
    intro q hq
    have hS : convexHull ℝ (Set.range p) ⊆ {q : ℝ² | p c 0 ≤ q 0} := by
      apply convexHull_min
      · rintro _ ⟨i, rfl⟩
        show p c 0 ≤ p i 0
        rw [← hh', ← hh']
        by_cases hi : i = c
        · rw [hi]
        · exact (hmin' i hi).le
      · intro q1 hq1 q2 hq2 s t hs ht hst
        simp only [Set.mem_ofPred_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at *
        have e : s * p c 0 + t * p c 0 = p c 0 := by rw [← add_mul, hst, one_mul]
        nlinarith [mul_le_mul_of_nonneg_left hq1 hs, mul_le_mul_of_nonneg_left hq2 ht]
    have := hS hq
    simp only [Set.mem_ofPred_eq] at this
    rw [hon]
    simp [PiLp.inner_apply, Fin.sum_univ_two]
    nlinarith
  obtain ⟨hup, hdown⟩ := hccw.incr_outNormal hcone
  set m : ℕ := (a - c).val with hm
  have hmk : m < k := ZMod.val_lt _
  have hcm : c + (m : ZMod k) = a := Minimality.zmod_add_val_sub c a
  have hha : ∀ j, p j 0 ≤ p a 0 := fun j => by
    have := hccw.inner_outNormal_le a j
    rw [hon] at this
    simp [PiLp.inner_apply, Fin.sum_univ_two] at this
    nlinarith
  -- strictness off the edge a
  have hstrict : ∀ i, i ≠ a → p (i + 1) 0 ≠ p i 0 := by
    intro i hia hfl
    have hΔi : p (i + 1) - p i = !₂[0, p (i + 1) 1 - p i 1] := by
      ext l; fin_cases l <;> simp [hfl]
    have hu : p (i + 1) 1 - p i 1 ≠ 0 := by
      intro h0
      have := hccw.cross2_edge_pos i
      rw [hΔi, h0] at this
      simp [Minimality.cross2] at this
    rcases lt_or_gt_of_ne hu with hneg | hpos
    · have hge : ∀ j, j ≠ i → j ≠ i + 1 → p i 0 < p j 0 := fun j h1 h2 => by
        have := hccw.2 i j h1 h2
        rw [hΔi] at this
        simp [Minimality.cross2] at this
        nlinarith
      have hmn : ∀ j, p i 0 ≤ p j 0 := fun j => by
        by_cases h1 : j = i
        · rw [h1]
        by_cases h2 : j = i + 1
        · rw [h2, hfl]
        exact (hge j h1 h2).le
      by_cases hic : i = c
      · have := hmin' (i + 1) (by rw [hic]; exact hk1)
        rw [hh', hh', hfl, ← hic] at this
        exact lt_irrefl _ this
      · have := hmin' i hic
        rw [hh', hh'] at this
        linarith [hmn c]
    · have hle : ∀ j, j ≠ i → j ≠ i + 1 → p j 0 < p i 0 := fun j h1 h2 => by
        have := hccw.2 i j h1 h2
        rw [hΔi] at this
        simp [Minimality.cross2] at this
        nlinarith
      by_cases hai : a = i + 1
      · have := hccw.cross2_edge_pos a
        have e1 : a - 1 = i := by rw [hai]; ring
        have hΔi' : p a - p i = !₂[0, p (i + 1) 1 - p i 1] := by rw [hai]; exact hΔi
        rw [e1, hΔi', hΔ] at this
        simp [Minimality.cross2] at this
      · have := hle a (Ne.symm hia) hai
        linarith [hha i]
  -- signs of the rises
  have hrise_eq : ∀ i, p (i + 1) 0 - p i 0 = ⟪N, X (i + 1) - X i⟫ := fun i => by
    rw [inner_sub_right, hh', hh']
  have hsign : ∀ i, i ≠ a →
      (0 < p (i + 1) 0 - p i 0 ∧ (i - c).val < m) ∨ (p (i + 1) 0 - p i 0 < 0 ∧ m < (i - c).val) := by
    intro i hia
    set n := (i - c).val with hn
    have hnk : n < k := ZMod.val_lt _
    have hin : c + (n : ZMod k) = i := Minimality.zmod_add_val_sub c i
    have hnm : n ≠ m := fun e => hia (by rw [← hin, e, hcm])
    have hne := hstrict i hia
    rcases lt_or_gt_of_ne hnm with h | h
    · left
      refine ⟨?_, h⟩
      have := hup n h
      have e1 : c + ((n + 1 : ℕ) : ZMod k) = i + 1 := by rw [← hin]; push_cast; ring
      rw [e1, hin, hon] at this
      simp [PiLp.inner_apply, Fin.sum_univ_two] at this
      have h2 : 0 ≤ p (i + 1) 0 - p i 0 := by nlinarith
      exact lt_of_le_of_ne h2 (fun e => hne (by linarith))
    · right
      refine ⟨?_, h⟩
      have := hdown n h.le hnk
      have e1 : c + ((n + 1 : ℕ) : ZMod k) = i + 1 := by rw [← hin]; push_cast; ring
      rw [e1, hin, hon] at this
      simp [PiLp.inner_apply, Fin.sum_univ_two] at this
      have h2 : p (i + 1) 0 - p i 0 ≤ 0 := by nlinarith
      exact lt_of_le_of_ne h2 (fun e => hne (by linarith))
  -- ends of edges and arcs
  have hends : ∀ i j, i ≠ a → (j = i ∨ j = i + 1) → j ≠ c →
      (0 < p (i + 1) 0 - p i 0 ∧ ∃ s : ℕ, 0 < s ∧ s ≤ m ∧ c + (s : ZMod k) = j) ∨
      (p (i + 1) 0 - p i 0 < 0 ∧ ∃ s : ℕ, m < s ∧ s < k ∧ c + (s : ZMod k) = j) := by
    intro i j hia hj hjc
    have hjv : (j - c).val ≠ 0 := fun h0 => hjc (sub_eq_zero.1 ((ZMod.val_eq_zero _).1 h0))
    have hjk : (j - c).val < k := ZMod.val_lt _
    have hjj : c + ((j - c).val : ZMod k) = j := Minimality.zmod_add_val_sub c j
    rcases hsign i hia with ⟨hr, hn⟩ | ⟨hr, hn⟩
    · left
      refine ⟨hr, (j - c).val, Nat.pos_of_ne_zero hjv, ?_, hjj⟩
      rcases hj with rfl | rfl
      · omega
      · obtain ⟨e, -⟩ := val_succ_sub hk i c hjc
        omega
    · right
      refine ⟨hr, (j - c).val, ?_, hjk, hjj⟩
      rcases hj with rfl | rfl
      · exact hn
      · obtain ⟨e, -⟩ := val_succ_sub hk i c hjc
        omega
  have hdet : ∀ i, det3 (X (i + 1) - X i) d w = p (i + 1) 0 - p i 0 := fun i => by
    rw [det3_rot, det3_eq_inner]; exact (hrise_eq i).symm
  refine ⟨?_, ?_⟩
  · rcases harcs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨1, fun i j hia hj hjc => ?_⟩
      show 0 < 1 * (⟪X j - X c, w⟫ * det3 (X (i + 1) - X i) d w)
      rw [hdet, inner_sub_left]
      rcases hends i j hia hj hjc with ⟨hr, s, hs0, hsm, hsj⟩ | ⟨hr, s, hs0, hsk, hsj⟩
      · have := h1 s hs0 hsm
        rw [hsj] at this
        nlinarith
      · have := h2 s hs0 hsk
        rw [hsj] at this
        nlinarith
    · refine ⟨-1, fun i j hia hj hjc => ?_⟩
      show 0 < -1 * (⟪X j - X c, w⟫ * det3 (X (i + 1) - X i) d w)
      rw [hdet, inner_sub_left]
      rcases hends i j hia hj hjc with ⟨hr, s, hs0, hsm, hsj⟩ | ⟨hr, s, hs0, hsk, hsj⟩
      · have := h1 s hs0 hsm
        rw [hsj] at this
        nlinarith
      · have := h2 s hs0 hsk
        rw [hsj] at this
        nlinarith
  · have hac : a ≠ c := by
      intro h
      have := hmin' (a + 1) (by rw [h]; exact hk1)
      rw [hh', hh', hflat, h] at this
      exact lt_irrefl _ this
    have ha1c : a + 1 ≠ c := by
      intro h
      have := hmin' a hac
      rw [hh', hh'] at this
      rw [← h, hflat] at this
      exact lt_irrefl _ this
    have hm0 : 0 < m := Nat.pos_of_ne_zero (fun h0 => hac (sub_eq_zero.1 ((ZMod.val_eq_zero _).1 h0)))
    obtain ⟨e, hk'⟩ := val_succ_sub hk a c ha1c
    have hcm1 : c + ((m + 1 : ℕ) : ZMod k) = a + 1 := by
      have := Minimality.zmod_add_val_sub c (a + 1)
      rwa [e] at this
    have hdw : ⟪x (lab (a + 1)) - x (lab a), w⟫ = ⟪X (a + 1), w⟫ - ⟪X a, w⟫ := inner_sub_left _ _ _
    rw [hdw]
    rcases harcs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have u1 := h1 m hm0 le_rfl
      have u2 := h2 (m + 1) (by omega) hk'
      rw [hcm] at u1
      rw [hcm1] at u2
      linarith
    · have u1 := h1 m hm0 le_rfl
      have u2 := h2 (m + 1) (by omega) hk'
      rw [hcm] at u1
      rw [hcm1] at u2
      linarith

/-! ## Secondary: the pivot lemma (for rims that are not split) -/

/-- The covector of the condition "the line of the edge `D` stays in its silhouette plane". -/
noncomputable def edgeRow (D w : ℝ³) : ℝ³ := ⟪D, D⟫ • w - ⟪D, w⟫ • D

/-- The axis direction of the pivot at the corner `c`: rotating about the line through `X c` with
this direction keeps the screen lines of both edges at `c`. -/
noncomputable def pivotAxis {k : ℕ} (X : ZMod k → ℝ³) (w : ℝ³) (c : ZMod k) : ℝ³ :=
  cross (edgeRow (X (c + 1) - X c) w) (edgeRow (X c - X (c - 1)) w)

theorem det3_pivot_self (D w ν : ℝ³) (h : ⟪ν, edgeRow D w⟫ = 0) : det3 D (cross ν D) w = 0 := by
  have e : det3 D (cross ν D) w = ⟪ν, edgeRow D w⟫ := by
    simp only [det3, inner3, edgeRow, PiLp.sub_apply, PiLp.smul_apply, cross_0, cross_1, cross_2,
      smul_eq_mul]
    ring
  rw [e, h]

theorem inner_cross_left (A B : ℝ³) : ⟪cross A B, A⟫ = 0 := by
  simp only [inner3, cross_0, cross_1, cross_2]; ring

theorem inner_cross_right (A B : ℝ³) : ⟪cross A B, B⟫ = 0 := by
  simp only [inner3, cross_0, cross_1, cross_2]; ring

theorem cross_sub_right (ν y C : ℝ³) : cross ν (y - C) = cross ν y + -cross ν C := by
  ext i; fin_cases i <;> simp <;> ring

/-- **Pivot Lemma.**  If rotating about the pivot axis at `c` (with sign `σ`) moves both ends of
every rim edge not at `c` strictly inward, the view is free.  On a two-peaked 4-corner rim, with
`c` the sharp corner, the four numbers are the torques of the two level tripods at the ends of
their private edges. -/
theorem freeAt_of_pivot {n k : ℕ} [NeZero k] (hk : 3 ≤ k) (x : Fin n → ℝ³) (w : ℝ³)
    (lab : ZMod k → Fin n) (hinj : Function.Injective lab) (hrim : StrictRimN x w lab)
    (hhid : HiddenInTriangles x w lab) (c : ZMod k) (σ : ℝ)
    (hrows : ∀ i j : ZMod k, i ≠ c → i + 1 ≠ c → (j = i ∨ j = i + 1) →
      0 < σ * det3 (x (lab (i + 1)) - x (lab i))
        (cross (pivotAxis (fun i => x (lab i)) w c) (x (lab j) - x (lab c))) w) :
    FreeAt (univ.image x) w := by
  refine freeAt_of_rimMotion hk x w lab hinj hrim hhid ?_
  set X : ZMod k → ℝ³ := fun i => x (lab i) with hX
  set ν := pivotAxis X w c with hν
  set C := X c with hC
  set A := X (c + 1) - C with hA
  set B := X (c - 1) - C with hB
  have hne : lab (c - 1) ≠ lab (c + 1) ∧ lab (c - 1) ≠ lab c := by
    refine ⟨fun h => zmod_pred_ne_succ hk c (hinj h), fun e => ?_⟩
    have h1 : c - (c - 1) = 0 := by rw [hinj e]; ring
    have : (1 : ZMod k) = 0 := by simpa using h1
    have hf : Fact (1 < k) := ⟨by omega⟩
    exact one_ne_zero this
  have hP : 0 < det3 A B w := hrim (lab (c - 1)) c hne.2 hne.1
  have hA0 : det3 A (cross ν A) w = 0 := det3_pivot_self A w ν (inner_cross_left _ _ |> fun h => by
    rw [real_inner_comm]; simpa [hν, pivotAxis, real_inner_comm] using h)
  have hB0 : det3 (C - X (c - 1)) (cross ν (C - X (c - 1))) w = 0 :=
    det3_pivot_self _ w ν (inner_cross_right _ _ |> fun h => by
      rw [real_inner_comm]; simpa [hν, pivotAxis, real_inner_comm] using h)
  set T := A + B with hT
  have hAT : det3 A T w = det3 A B w := by
    simp only [hT, det3, PiLp.add_apply]; ring
  have hBT : det3 (C - X (c - 1)) T w = det3 A B w := by
    have : C - X (c - 1) = -B := by rw [hB]; abel
    rw [this]
    simp only [hT, det3, PiLp.add_apply, PiLp.neg_apply]; ring
  have hval : ∀ (L : ℝ) (E y : ℝ³),
      det3 E (cross ((L * σ) • ν) y + ((L * σ) • (-cross ν C) + T)) w =
        L * (σ * det3 E (cross ν (y - C)) w) + det3 E T w := by
    intro L E y
    simp only [det3, cross_sub_right, PiLp.add_apply, PiLp.smul_apply, PiLp.neg_apply, cross_0,
      cross_1, cross_2, smul_eq_mul]
    ring
  let J : ZMod k × Bool → ZMod k := fun t => if t.2 then t.1 + 1 else t.1
  let Ed : ZMod k × Bool → ℝ³ := fun t => X (t.1 + 1) - X t.1
  obtain ⟨L, hL⟩ := exists_large (ι := ZMod k × Bool)
    (fun t => σ * det3 (Ed t) (cross ν (X (J t) - C)) w) (fun t => det3 (Ed t) T w) (by
      rintro ⟨i, b⟩
      by_cases h1 : i = c
      · subst h1
        right
        refine ⟨?_, by simp only [Ed]; rw [show X (i + 1) - X i = A from rfl, hAT]; exact hP⟩
        cases b
        · simp [J, Ed, hC, det3, cross]
        · simp only [J, Ed, ite_true]
          rw [hA0, mul_zero]
      · by_cases h2 : i + 1 = c
        · have hi' : i = c - 1 := by rw [← h2]; ring
          subst hi'
          right
          have e1 : X (c - 1 + 1) = C := by rw [show c - 1 + 1 = c by ring]
          refine ⟨?_, by simp only [Ed]; rw [e1, hBT]; exact hP⟩
          cases b
          · simp only [J, Ed, Bool.false_eq_true, ite_false]
            rw [e1]
            have e2 : X (c - 1) - C = -(C - X (c - 1)) := by abel
            have e3 : det3 (C - X (c - 1)) (cross ν (-(C - X (c - 1)))) w =
                -det3 (C - X (c - 1)) (cross ν (C - X (c - 1))) w := by
              simp only [det3, PiLp.neg_apply, cross_0, cross_1, cross_2]; ring
            rw [e2, e3, hB0]; simp
          · simp only [J, Ed, ite_true]
            rw [e1]
            simp [det3, cross]
        · left
          refine hrows i (J (i, b)) h1 h2 ?_
          cases b
          · exact Or.inl rfl
          · exact Or.inr rfl)
  refine ⟨(L * σ) • ν, (L * σ) • (-cross ν C) + T, fun i => ⟨?_, ?_⟩⟩
  · have := hL (i, false)
    rw [hval]; exact this
  · have := hL (i, true)
    rw [hval]; exact this

/-! ## Free views pass -/

theorem det3_eq_minimality (a b c : ℝ³) : det3 a b c = Minimality.det3 a b c := by
  rw [Minimality.det3, inner3]
  simp only [det3, cross]
  simp

theorem tiltCert_iff (V : Finset ℝ³) (w ω τ y : ℝ³) :
    TiltCert V w ω τ y ↔ Minimality.TiltCert V w ω τ y := by
  simp only [TiltCert, Minimality.TiltCert, det3_eq_minimality]

/-- A free nonzero view gives a Rupert passage (`MinimalityExtra.FreeAt.isRupert`). -/
theorem FreeAt.isRupert {V : Finset ℝ³} {w : ℝ³} (hw : w ≠ 0) (h : FreeAt V w) : IsRupert V := by
  obtain ⟨ω, τ, hc⟩ := h
  exact Minimality.isRupert_of_tiltCert V w hw ω τ fun y hy => (tiltCert_iff V w ω τ y).1 (hc y hy)

end Minimality.Split

#print axioms Minimality.Split.freeAt_of_splitRows
#print axioms Minimality.Split.freeAt_of_pivot
#print axioms Minimality.Split.FreeAt.isRupert
