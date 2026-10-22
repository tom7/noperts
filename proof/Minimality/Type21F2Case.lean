module

public import Minimality.Type21Other

@[expose] public section

/-!
# Type 21: F2 on the rest of class (c) (`FEWER-FACES-PROOFS.md` Lemma 16.24)

Labels as in `Type21Lemmas.lean`: `a, a', b, b', c, c', d = 0, 3, 4, 5, 1, 6, 2`.  In the normal
form (c) (`K − 2` in the pattern `(+, −, +)`, `2` beyond `013` but not beyond `145`), with `Q`
and `H` failing for `K − 2` and `Q` failing for `K − 6`, and `|[3 1]| < |[3 4]|`, the two
vertex tests at `4`, `V = 014/2346` and `V′ = 046/134`, satisfy the hypotheses of F2
(`cert_type21_F2`).

* `cert_type21_F2_frame` — the geometry of steps 2–4 of 16.24 in the frame
  `4; 3, 5, 6` (`D = det(3 − 4, 5 − 4, 6 − 4)`): the coordinates of `0, 1, 2` and of the views
  `u_V = [5 0](0 − 4) + [5 1](1 − 4)`, `u_V′ = [5 0](0 − 4) + [5 6](6 − 4)` come from the
  dependencies `[1 ·]`, `[5 ·]` and the cap `2 − 4 = τ [1 3](3 − 4) + r (6 − 4)`; every
  determinant of F2 is a bracket polynomial times `D` (`det3_scaled_combo`).  The bracket
  values enter as real parameters with the facts of step 1.
* `cert_type21_F2case` — step 1 (the Gale facts) and the reduction: each failing Gale
  comparison is a tier (`Q` at `05` of `K − 2`, `H` at `13`, `Q` at `50` of `K − 6`, `Q` at `23`
  of `K − 6` by `cert_type21_step5` when H2 holds); otherwise F2.

**Certificate form** (§18.2, §18.6 step 2): every theorem of the tier cover concludes a rim
certificate at a named view (`CertV`: a segment view or a view satisfying `L`, the named vertex
crossings) instead of Rupertness; no horizontal double normal is assumed.  The old statement
`isRupert_type21_facets` and the limit theorem are in `Type21Limit.lean`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

variable {L : ℝ³ → Prop}

theorem type21_id_F2B1 {a a' b b' c c' : ℝ³} {l m : ℝ³ → ℝ}
    (hl : IsDep a a' b b' c c' l) (hm : IsDep a a' b b' c c' m) :
    galeD l m c a' * galeD l m b' c' - galeD l m c' c * galeD l m a' b' =
      galeD l m b' c * galeD l m c' a' := by
  type21_ring hl hm

theorem type21_id_F2al {a a' b b' c c' : ℝ³} {l m : ℝ³ → ℝ}
    (_hl : IsDep a a' b b' c c' l) (_hm : IsDep a a' b b' c c' m) :
    galeD l m a b' * galeD l m c a' =
      galeD l m a' a * galeD l m b' c + galeD l m c a * galeD l m a' b' := by
  simp only [galeD]; ring

theorem type21_id_F2h1 {a a' b b' c c' : ℝ³} {l m : ℝ³ → ℝ}
    (hl : IsDep a a' b b' c c' l) (hm : IsDep a a' b b' c c' m) :
    (galeD l m a' b - galeD l m c a') * galeD l m b' c' +
      (galeD l m a b' - galeD l m b' c') * galeD l m c' a' +
      (galeD l m b' c' - galeD l m c' a) * galeD l m a' b' = 0 := by
  type21_ring hl hm

theorem type21_id_F2P5 {a a' b b' c c' : ℝ³} {l m : ℝ³ → ℝ}
    (hl : IsDep a a' b b' c c' l) (hm : IsDep a a' b b' c c' m) :
    galeD l m a' b' * galeD l m c' a - galeD l m a' b' * galeD l m b' c' +
      galeD l m c a' * galeD l m b' c' = galeD l m a' b' * galeD l m b c' +
      galeD l m c' a' * galeD l m b' c - galeD l m c' a' * galeD l m a' b' := by
  type21_ring hl hm

theorem type21_id_F2c1 {a a' b b' c c' : ℝ³} {l m : ℝ³ → ℝ}
    (hl : IsDep a a' b b' c c' l) (hm : IsDep a a' b b' c c' m) :
    galeD l m a' b' * galeD l m b c' - galeD l m a' b * galeD l m b' c' =
      -(galeD l m c' a' * galeD l m b b') := by
  type21_ring hl hm

theorem type21_id_F2c2 {a a' b b' c c' : ℝ³} {l m : ℝ³ → ℝ}
    (hl : IsDep a a' b b' c c' l) (hm : IsDep a a' b b' c c' m) :
    galeD l m b' c * galeD l m b c' =
      galeD l m c' c * galeD l m b b' + galeD l m b c * galeD l m b' c' := by
  type21_ring hl hm

/-- A determinant of three vectors given (up to scalars) in a frame `e, f, g`. -/
theorem det3_scaled_combo {X Y Z e f g : ℝ³} {k₁ k₂ k₃ x₁ y₁ z₁ x₂ y₂ z₂ x₃ y₃ z₃ : ℝ}
    (h₁ : k₁ • X = x₁ • e + y₁ • f + z₁ • g) (h₂ : k₂ • Y = x₂ • e + y₂ • f + z₂ • g)
    (h₃ : k₃ • Z = x₃ • e + y₃ • f + z₃ • g) :
    k₁ * k₂ * k₃ * det3 X Y Z = (x₁ * (y₂ * z₃ - z₂ * y₃) - y₁ * (x₂ * z₃ - z₂ * x₃) +
      z₁ * (x₂ * y₃ - y₂ * x₃)) * det3 e f g := by
  have : k₁ * k₂ * k₃ * det3 X Y Z = det3 (k₁ • X) (k₂ • Y) (k₃ • Z) := by
    simp only [det3_expand, PiLp.smul_apply, smul_eq_mul]; ring
  rw [this, h₁, h₂, h₃]
  simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

theorem pos_of_scaled {k x M D σ : ℝ} (hk : 0 < k) (h : k * x = M * D) (hM : 0 < σ * M * D) :
    0 < σ * x := by
  have e : k * (σ * x) = σ * M * D := by rw [← mul_assoc, mul_comm k σ, mul_assoc, h]; ring
  rw [← e] at hM
  exact pos_of_mul_pos_right hM hk.le

theorem mul_pos_of_scaled {k₁ k₂ x₁ x₂ M₁ M₂ D : ℝ} (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (h₁ : k₁ * x₁ = M₁ * D) (h₂ : k₂ * x₂ = M₂ * D) (hM : 0 < M₁ * M₂) (hD : D ≠ 0) :
    0 < x₁ * x₂ := by
  have e : (k₁ * k₂) * (x₁ * x₂) = (M₁ * M₂) * (D * D) := by
    linear_combination (k₂ * x₂) * h₁ + (M₁ * D) * h₂
  have h := mul_pos hM (mul_self_pos.mpr hD)
  rw [← e] at h
  exact pos_of_mul_pos_right h (mul_pos hk₁ hk₂).le

theorem mul_neg_of_scaled {k₁ k₂ x₁ x₂ M₁ M₂ D : ℝ} (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (h₁ : k₁ * x₁ = M₁ * D) (h₂ : k₂ * x₂ = M₂ * D) (hM : M₁ * M₂ < 0) (hD : D ≠ 0) :
    x₁ * x₂ < 0 := by
  have e : (k₁ * k₂) * (x₁ * x₂) = (M₁ * M₂) * (D * D) := by
    linear_combination (k₂ * x₂) * h₁ + (M₁ * D) * h₂
  have h := mul_neg_of_neg_of_pos hM (mul_self_pos.mpr hD)
  rw [← e] at h
  exact neg_of_mul_neg_right h (mul_pos hk₁ hk₂).le

theorem combo_div {k p q : ℝ} {X Y Z : ℝ³} (hk : k ≠ 0) (h : k • X = p • Y + q • Z) :
    X = (p / k) • Y + (q / k) • Z := by
  rw [div_eq_inv_mul, div_eq_inv_mul, mul_smul, mul_smul, ← smul_add, ← h, smul_smul,
    inv_mul_cancel₀ hk, one_smul]

theorem combo_div3 {k p q s : ℝ} {X Y Z W : ℝ³} (hk : k ≠ 0)
    (h : k • X = p • Y + q • Z + s • W) : X = (p / k) • Y + (q / k) • Z + (s / k) • W := by
  rw [div_eq_inv_mul, div_eq_inv_mul, div_eq_inv_mul, mul_smul, mul_smul, mul_smul, ← smul_add,
    ← smul_add, ← h, smul_smul, inv_mul_cancel₀ hk, one_smul]

/-- **A hidden point from a degenerate combination** (Lemma 13.8 (i)): if
`m = P' + p (Q' − P') + q (P − P') + γ u` with `p, q > 0`, `p + q < 1` (no weight at `Q`), a small
multiple of any relation `Q − P' = x (P − P') + y u + z (Q' − P')` moves weight onto `Q`. -/
theorem axisHidden_of_rel {P P' Q Q' u m : ℝ³} {p q γ x y z : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hpq : p + q < 1) (hm : m = P' + p • (Q' - P') + q • (P - P') + γ • u)
    (hrel : Q - P' = x • (P - P') + y • u + z • (Q' - P')) : AxisHidden P P' Q Q' u m := by
  set s := min p (min q (1 - p - q)) with hs
  have hs0 : 0 < s := lt_min hp (lt_min hq (by linarith))
  have hsp : s ≤ p := min_le_left _ _
  have hsq : s ≤ q := (min_le_right _ _).trans (min_le_left _ _)
  have hsr : s ≤ 1 - p - q := (min_le_right _ _).trans (min_le_right _ _)
  have hxa : 0 ≤ |x| := abs_nonneg x
  have hza : 0 ≤ |z| := abs_nonneg z
  set K := 1 + |x| + |z| with hK
  have hK0 : 0 < K := by positivity
  set ε := s / (2 * K) with hε
  have hε0 : 0 < ε := by positivity
  have hεK : ε * K = s / 2 := by rw [hε]; field_simp
  have ex1 : ε * x ≤ ε * |x| := mul_le_mul_of_nonneg_left (le_abs_self x) hε0.le
  have ex2 : ε * -|x| ≤ ε * x := mul_le_mul_of_nonneg_left (neg_abs_le x) hε0.le
  have ez1 : ε * z ≤ ε * |z| := mul_le_mul_of_nonneg_left (le_abs_self z) hε0.le
  have ez2 : ε * -|z| ≤ ε * z := mul_le_mul_of_nonneg_left (neg_abs_le z) hε0.le
  have eK : ε * K = ε + ε * |x| + ε * |z| := by rw [hK]; ring
  have exK : ε * |x| ≤ ε * K := mul_le_mul_of_nonneg_left (by linarith) hε0.le
  have ezK : ε * |z| ≤ ε * K := mul_le_mul_of_nonneg_left (by linarith) hε0.le
  refine ⟨q - ε * x, 1 - p - q - ε + ε * x + ε * z, ε, p - ε * z, γ - ε * y, ?_, ?_, hε0, ?_,
    ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · ring
  · rw [hm]
    linear_combination (norm := module) (-ε) • hrel

/-- **The special positions of the two vertex tests of F2** in one labelling (vertex `b`): at
every direction `u ≠ 0` of the line `abc ∩ a'bc'` (`V`, rim `b, d, b', c`) and every direction
`v ≠ 0` of `abc' ∩ a'bc` (`V′`, rim `b, a', b', a`), the far side off the antipode
(`[c − d, b' − d, u] ≠ 0`, `[a − a', b' − a', v] ≠ 0`), the views satisfy `L`, and the ties of
the two rims are allowed ones (`F2Tie`). -/
def F2ViewsL (K : Finset ℝ³) (L : ℝ³ → Prop) (a a' b b' c c' d : ℝ³) : Prop :=
  (∀ u : ℝ³, u ≠ 0 → det3 (a - b) (c - b) u = 0 → det3 (a' - b) (c' - b) u = 0 →
    det3 (c - d) (b' - d) u ≠ 0 ∧ (VRim K a a' b b' c c' d u → L u)) ∧
  (∀ v : ℝ³, v ≠ 0 → det3 (a - b) (c' - b) v = 0 → det3 (a' - b) (c - b) v = 0 →
    det3 (a - a') (b' - a') v ≠ 0 ∧ L v) ∧
  (∀ u v : ℝ³, u ≠ 0 → det3 (a - b) (c - b) u = 0 → det3 (a' - b) (c' - b) u = 0 →
    v ≠ 0 → det3 (a - b) (c' - b) v = 0 → det3 (a' - b) (c - b) v = 0 →
    F2Tie K b b' d c a' a u v)

/-- **Lemma 16.24, steps 2–4, in the frame `4; 3, 5, 6`.**  The bracket values are parameters
(`g05 = [0 5]`, `g10 = [1 0]`, …, all positive in the pattern `(+, −, +)`); `VA`, `VC` are the
dependencies `[1 ·]`, `[5 ·]` at `4`, `VD` the cap, `hu`, `hu'` the views.  The facts of step 1
enter as `h35 : [3 5] < [5 1]`, `h51 : [5 1] < [0 5]`, `h05 : [0 5] < [5 6]` (h1),
`hΛ : δ_014(2) > δ_014(3)` (in the form `[5 6] < τ [1 3][5 6] + r [3 5]`), `hP : α > 0` (the
weight of `0` in `P(2)`), `hab : 1 − α − β > 0` and `hP5` (the side of `P(5)`).  Then F2
holds: `V`'s rim is `(4, 2, 5, 1)` (`3` a middle over `4 → 2`, `0` over `4 → 1`, `6` a middle
over `4 → 2`), `V′`'s rim is `(4, 3, 5, 0)` (`1` over `4 → 3`, `6` over `4 → 0`, `2` hidden),
`[2, 1]` meets `[4, 5]` along `u_V′`, and the sign condition holds. -/
theorem cert_type21_F2_frame {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (G : GaleData a a' b b' c c') {g05 g10 g13 g35 g51 g56 g60 g61 g63 τ r : ℝ}
    (p05 : 0 < g05) (p10 : 0 < g10) (p13 : 0 < g13) (p35 : 0 < g35) (p51 : 0 < g51)
    (p56 : 0 < g56) (p60 : 0 < g60) (p63 : 0 < g63) (pτ : 0 < τ) (pr : 0 < r)
    (VA : g10 • (a - b) = (-g13) • (a' - b) + g51 • (b' - b) + g61 • (c' - b))
    (VC : g51 • (c - b) = g05 • (a - b) + g35 • (a' - b) - g56 • (c' - b))
    (VD : d - b = (τ * g13) • (a' - b) + r • (c' - b))
    (hu : axisView G.l G.m b' b a c = (-g05) • (a - b) + g51 • (c - b))
    (hu' : axisView G.l G.m b' b a c' = (-g05) • (a - b) + g56 • (c' - b))
    (P1 : g61 * g05 = g56 * g10 - g60 * g51)
    (B1 : g13 * g56 - g61 * g35 = g51 * g63)
    (hΛ : g56 < τ * g13 * g56 + r * g35)
    (h35 : g35 < g51) (h51 : g51 < g05) (h05 : g05 < g56)
    (hP : 0 < r * g05 - τ * g51 * g60)
    (hab : 0 < g56 - τ * g51 * g56 - (r * g05 - τ * g51 * g60))
    (hP5 : 0 < g35 * g60 - g35 * g56 + g13 * g56) {g30 : ℝ}
    (hC1 : g10 * g35 - g05 * g13 = -(g51 * g30)) (h145 : τ * g13 * g60 < r * g30)
    (hDD : 0 < (1 - r) * g30 + τ * g13 * g60)
    (hF2 : F2ViewsL (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L a a' b b' c c' d) :
    CertV (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L
      (SegOK21 (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) a a' b b' c c' d) := by
  have hnd' := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨haa', hab', hab'', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd'
  -- the frame `4; 3, 5, 6`
  set D := det3 (a' - b) (b' - b) (c' - b) with hDdef
  have hD : D ≠ 0 := by
    intro h0
    have hc := cross_ne_zero_of_affine F.a'bc.hN ha'b F.a'bc.hP F.a'bc.hQ
      (F.a'bc.neg c' (by simp) (Ne.symm ha'c') (Ne.symm hbc') (Ne.symm hcc'))
    have := affine_zero_of_coplanar F.a'bc'.hN F.a'bc'.hP F.a'bc'.hQ F.a'bc'.hR hc (w := b') (by
      have e : det3 (b - a') (c' - a') (b' - a') = D := by
        simp only [hDdef, det3_expand, PiLp.sub_apply]; ring
      rw [e, h0])
    linarith [F.a'bc'.neg b' (by simp) (Ne.symm ha'b') (Ne.symm hbb') hb'c']
  obtain ⟨σ, hσ, hσD⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ 0 < σ * D := by
    rcases lt_or_gt_of_ne hD with h | h
    · exact ⟨-1, Or.inr rfl, by linarith⟩
    · exact ⟨1, Or.inl rfl, by linarith⟩
  set u := axisView G.l G.m b' b a c with hudef
  set v := axisView G.l G.m b' b a c' with hvdef
  have hu2 : u = g35 • (a' - b) - g56 • (c' - b) := by
    rw [hu]; linear_combination (norm := module) VC
  have hv2 : v = g35 • (a' - b) - g51 • (c - b) := by
    rw [hu']; linear_combination (norm := module) VC
  -- coordinates in the frame
  have c3 : (1 : ℝ) • (a' - b) = (1 : ℝ) • (a' - b) + (0 : ℝ) • (b' - b) + (0 : ℝ) • (c' - b) := by
    module
  have c5 : (1 : ℝ) • (b' - b) = (0 : ℝ) • (a' - b) + (1 : ℝ) • (b' - b) + (0 : ℝ) • (c' - b) := by
    module
  have cD : (1 : ℝ) • (d - b) = (τ * g13) • (a' - b) + (0 : ℝ) • (b' - b) + r • (c' - b) := by
    rw [VD]; module
  have cC : (g10 * g51) • (c - b) = (g10 * g35 - g05 * g13) • (a' - b) + (g05 * g51) • (b' - b) +
      (g05 * g61 - g10 * g56) • (c' - b) := by
    linear_combination (norm := module) g10 • VC + g05 • VA
  have cU : (1 : ℝ) • u = g35 • (a' - b) + (0 : ℝ) • (b' - b) + (-g56) • (c' - b) := by
    rw [hu2]; module
  have cV : g10 • v = (g05 * g13) • (a' - b) + (-(g05 * g51)) • (b' - b) +
      (g10 * g56 - g05 * g61) • (c' - b) := by
    rw [hu']; linear_combination (norm := module) (-g05) • VA
  have cCD : (g10 * g51) • (c - d) = (g10 * g35 - g05 * g13 - g10 * g51 * (τ * g13)) • (a' - b) +
      (g05 * g51) • (b' - b) + (g05 * g61 - g10 * g56 - g10 * g51 * r) • (c' - b) := by
    linear_combination (norm := module) g10 • VC + g05 • VA - (g10 * g51) • VD
  -- the determinants of `V` (sign `−D`)
  have dT1 : 1 * (g10 * g51) * 1 * det3 (d - b) (c - b) u =
      (-(g05 * g51 * (τ * g13 * g56 + r * g35))) * D := by
    rw [det3_scaled_combo cD cC cU]; ring
  have dG1 : 1 * 1 * 1 * det3 (d - b) (b' - b) u = (-(τ * g13 * g56 + r * g35)) * D := by
    rw [det3_scaled_combo cD c5 cU]; ring
  have dB1 : 1 * (g10 * g51) * 1 * det3 (b' - b) (c - b) u = (-(g05 * g51 * g63)) * D := by
    rw [det3_scaled_combo c5 cC cU]; linear_combination (-D * g05) * B1
  -- the determinants of `V′` (sign `D`)
  have dT2 : 1 * g10 * g10 * det3 (a' - b) (a - b) v = (g51 * g10 * g56) * D := by
    rw [det3_scaled_combo c3 VA cV]; ring
  have dG2 : 1 * 1 * g10 * det3 (a' - b) (b' - b) v = (g60 * g51) * D := by
    rw [det3_scaled_combo c3 c5 cV]; linear_combination (-D) * P1
  have dB2 : 1 * g10 * g10 * det3 (b' - b) (a - b) v = (g13 * g10 * g56) * D := by
    rw [det3_scaled_combo c5 VA cV]; ring
  -- the sign condition
  have dS1 : 1 * 1 * (g10 * g51) * det3 u (b' - b) (c - d) =
      (-(g51 * (g05 * g63 + g10 * (τ * g13 * g56 + r * g35)))) * D := by
    rw [det3_scaled_combo cU c5 cCD]; linear_combination (-D * g05) * B1
  have dS2 : g10 * 1 * (g10 * g51) * det3 v (b' - b) (c - d) =
      (-(g10 * g51 * (g13 * (r * g05 - τ * g51 * g60) + g35 * g60))) * D := by
    rw [det3_scaled_combo cV c5 cCD]
    linear_combination (D * g10 * (g35 - τ * g13 * g51)) * P1
  have hΛ0 : 0 < τ * g13 * g56 + r * g35 := by linarith
  have hsign : 0 < det3 u (b' - b) (c - d) * det3 v (b' - b) (c - d) :=
    mul_pos_of_scaled (by positivity) (by positivity) dS1 dS2
      (mul_pos_of_neg_of_neg (by
        have : 0 < g51 * (g05 * g63 + g10 * (τ * g13 * g56 + r * g35)) := by positivity
        linarith) (by
        have : 0 < g10 * g51 * (g13 * (r * g05 - τ * g51 * g60) + g35 * g60) := by positivity
        linarith)) hD
  -- the views are nonzero and lie in the face planes
  have hu0 : u ≠ 0 := by
    intro h0
    have e : det3 (d - b) (b' - b) u = 0 := by
      rw [h0]; simp only [det3_expand, PiLp.zero_apply]; ring
    rw [e] at dG1
    have : (τ * g13 * g56 + r * g35) * D = 0 := by linarith
    exact mul_ne_zero hΛ0.ne' hD this
  have hv0 : v ≠ 0 := by
    intro h0
    have e : det3 (a' - b) (b' - b) v = 0 := by
      rw [h0]; simp only [det3_expand, PiLp.zero_apply]; ring
    rw [e] at dG2
    have : (g60 * g51) * D = 0 := by linarith
    exact mul_ne_zero (by positivity) hD this
  have hN1 : det3 (a - b) (c - b) u = 0 := by
    rw [hu]; simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
      smul_eq_mul]; ring
  have hN2 : det3 (a' - b) (c' - b) u = 0 := by
    rw [hu2]; simp only [det3_expand, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have hN3 : det3 (a - b) (c' - b) v = 0 := by
    rw [hu']; simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
      smul_eq_mul]; ring
  have hN4 : det3 (a' - b) (c - b) v = 0 := by
    rw [hv2]; simp only [det3_expand, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
  obtain ⟨hP₁, -⟩ := hF2.1 u hu0 hN1 hN2
  obtain ⟨hP₂, -⟩ := hF2.2.1 v hv0 hN3 hN4
  have hties := hF2.2.2 u v hu0 hN1 hN2 hv0 hN3 hN4
  -- `V`: the middles `3` (over `4 → 2`), `0` (over `4 → 1`) and `6` (over `4 → 2`)
  have hm₁ : 0 < g56 / (τ * g13 * g56 + r * g35) ∧ g56 / (τ * g13 * g56 + r * g35) < 1 ∧
      r / (τ * g13 * g56 + r * g35) ≠ 0 ∧ a' = b + (g56 / (τ * g13 * g56 + r * g35)) • (d - b) +
        (r / (τ * g13 * g56 + r * g35)) • u := by
    refine ⟨by positivity, (div_lt_one hΛ0).mpr hΛ, by positivity, ?_⟩
    have k : (τ * g13 * g56 + r * g35) • (a' - b) = g56 • (d - b) + r • u := by
      linear_combination (norm := module) (-g56) • VD - r • hu2
    have := combo_div hΛ0.ne' k
    linear_combination (norm := module) this
  have hm₁' : 0 < g51 / g05 ∧ g51 / g05 < 1 ∧ (-1) / g05 ≠ 0 ∧
      a = b + (g51 / g05) • (c - b) + ((-1) / g05) • u := by
    refine ⟨by positivity, (div_lt_one p05).mpr h51, div_ne_zero (by norm_num) p05.ne', ?_⟩
    have k : g05 • (a - b) = g51 • (c - b) + (-1 : ℝ) • u := by
      linear_combination (norm := module) hu
    have := combo_div p05.ne' k
    linear_combination (norm := module) this
  have hX₁ : AxisExtra b' b d c u c' := by
    refine Or.inr (Or.inl ⟨g35 / (τ * g13 * g56 + r * g35), (-(τ * g13)) / (τ * g13 * g56 + r * g35),
      by positivity, (div_lt_one hΛ0).mpr (by linarith), div_ne_zero (by
        have : 0 < τ * g13 := by positivity
        linarith) hΛ0.ne', ?_⟩)
    have k : (τ * g13 * g56 + r * g35) • (c' - b) = g35 • (d - b) + (-(τ * g13)) • u := by
      linear_combination (norm := module) (-g35) • VD + (τ * g13) • hu2
    have := combo_div hΛ0.ne' k
    linear_combination (norm := module) this
  -- `V′`: the middles `1` (over `4 → 3`), `6` (over `4 → 0`), and `2` hidden
  have hm₂ : 0 < g35 / g51 ∧ g35 / g51 < 1 ∧ (-1) / g51 ≠ 0 ∧
      c = b + (g35 / g51) • (a' - b) + ((-1) / g51) • v := by
    refine ⟨by positivity, (div_lt_one p51).mpr h35, div_ne_zero (by norm_num) p51.ne', ?_⟩
    have k : g51 • (c - b) = g35 • (a' - b) + (-1 : ℝ) • v := by
      linear_combination (norm := module) VC + hu'
    have := combo_div p51.ne' k
    linear_combination (norm := module) this
  have hm₂' : 0 < g05 / g56 ∧ g05 / g56 < 1 ∧ 1 / g56 ≠ 0 ∧
      c' = b + (g05 / g56) • (a - b) + (1 / g56) • v := by
    refine ⟨by positivity, (div_lt_one p56).mpr h05, by positivity, ?_⟩
    have k : g56 • (c' - b) = g05 • (a - b) + (1 : ℝ) • v := by
      linear_combination (norm := module) -hu'
    have := combo_div p56.ne' k
    linear_combination (norm := module) this
  -- the frame `4; 0, 5, u_V′` for the hidden point and the meeting
  have fD : g56 • (d - b) = (r * g05 + τ * (g61 * g05 - g10 * g56)) • (a - b) +
      (τ * g51 * g56) • (b' - b) + (r + τ * g61) • v := by
    linear_combination (norm := module) g56 • VD + (τ * g56) • VA - (r + τ * g61) • hu'
  have fR : (g13 * g56) • (a' - b) = (g51 * g56) • (b' - b) + g61 • v +
      (g61 * g05 - g10 * g56) • (a - b) := by
    linear_combination (norm := module) g56 • VA - g61 • hu'
  have hPe : r * g05 + τ * (g61 * g05 - g10 * g56) = r * g05 - τ * g51 * g60 := by
    linear_combination τ * P1
  have hX₂ : AxisExtra b' b a' a v d := by
    left
    have k := combo_div3 p56.ne' fD
    have hq : (τ * g51 * g56) / g56 = τ * g51 := by field_simp
    rw [hq, hPe] at k
    refine axisHidden_of_rel (p := (r * g05 - τ * g51 * g60) / g56) (q := τ * g51)
      (γ := (r + τ * g61) / g56) (by positivity) (by positivity) ?_ (by
        linear_combination (norm := module) k) (combo_div3 (mul_pos p13 p56).ne' fR)
    rw [div_add' _ _ _ p56.ne', div_lt_one p56]
    linarith
  -- the meeting of `[2, 1]` and `[4, 5]` along `u_V′`
  set D' := det3 (a - b) (b' - b) v with hD'def
  have hD' : D' ≠ 0 := by
    intro h0
    have e : det3 (b' - b) (a - b) v = -D' := by
      simp only [hD'def, det3_expand, PiLp.sub_apply]; ring
    rw [e, h0, neg_zero, mul_zero] at dB2
    exact mul_ne_zero (by positivity) hD dB2.symm
  have f5 : (1 : ℝ) • (b' - b) = (0 : ℝ) • (a - b) + (1 : ℝ) • (b' - b) + (0 : ℝ) • v := by module
  have fV : (1 : ℝ) • v = (0 : ℝ) • (a - b) + (0 : ℝ) • (b' - b) + (1 : ℝ) • v := by module
  have fC : (g13 * g56 * g51) • (c - b) = (g35 * (g61 * g05 - g10 * g56)) • (a - b) +
      (g35 * g51 * g56) • (b' - b) + (g35 * g61 - g13 * g56) • v := by
    linear_combination (norm := module) (g13 * g56) • VC + (g13 * g56 - g35 * g61) • hu' +
      (g35 * g56) • VA
  set P := r * g05 + τ * (g61 * g05 - g10 * g56) with hPdef
  set W := g61 * g05 - g10 * g56 with hWdef
  have fCD : (g13 * g56 * g51) • (c - d) = (g35 * W - g13 * g51 * P) • (a - b) +
      (g35 * g51 * g56 - τ * g13 * g51 * g51 * g56) • (b' - b) +
      (g35 * g61 - g13 * g56 - g13 * g51 * (r + τ * g61)) • v := by
    linear_combination (norm := module) fC - (g13 * g51) • fD
  have fBD : (g13 * g56 * g51) • (b - d) = (-(g13 * g51 * P)) • (a - b) +
      (-(τ * g13 * g51 * g51 * g56)) • (b' - b) + (-(g13 * g51 * (r + τ * g61))) • v := by
    linear_combination (norm := module) (-(g13 * g51)) • fD
  have fB'D : (g13 * g56 * g51) • (b' - d) = (-(g13 * g51 * P)) • (a - b) +
      (g13 * g56 * g51 - τ * g13 * g51 * g51 * g56) • (b' - b) +
      (-(g13 * g51 * (r + τ * g61))) • v := by
    linear_combination (norm := module) (-(g13 * g51)) • fD
  have mD1 : 1 * g56 * 1 * det3 (b' - b) (d - b) v = (-P) * D' := by
    rw [det3_scaled_combo f5 fD fV]; ring
  have mD2 : 1 * (g13 * g56 * g51) * 1 * det3 (b' - b) (c - b) v = (-(g35 * W)) * D' := by
    rw [det3_scaled_combo f5 fC fV]; ring
  have mE1 : (g13 * g56 * g51) * (g13 * g56 * g51) * 1 * det3 (c - d) (b - d) v =
      (g13 * g51 * g51 * g56 * g35 * (r * g05)) * D' := by
    rw [det3_scaled_combo fCD fBD fV]; ring
  have mE2 : (g13 * g56 * g51) * (g13 * g56 * g51) * 1 * det3 (c - d) (b' - d) v =
      (g13 * g51 * g56 * (g35 * W * (1 - τ * g51) + g51 * P * (g35 - g13))) * D' := by
    rw [det3_scaled_combo fCD fB'D fV]; ring
  have hW : W = -(g60 * g51) := by rw [hWdef]; linarith
  have hPp : P = r * g05 - τ * g51 * g60 := by rw [hPdef]; linarith
  have hQ : g35 * W * (1 - τ * g51) + g51 * P * (g35 - g13) < 0 := by
    have key : g56 * (g35 * W * (1 - τ * g51) + g51 * P * (g35 - g13)) =
        -g51 * (g35 * g60 * (g56 - τ * g51 * g56 - (r * g05 - τ * g51 * g60)) +
          (r * g05 - τ * g51 * g60) * (g35 * g60 - g35 * g56 + g13 * g56)) := by
      rw [hW, hPp]; ring
    have : 0 < g51 * (g35 * g60 * (g56 - τ * g51 * g56 - (r * g05 - τ * g51 * g60)) +
        (r * g05 - τ * g51 * g60) * (g35 * g60 - g35 * g56 + g13 * g56)) := by positivity
    have h2 : g56 * (g35 * W * (1 - τ * g51) + g51 * P * (g35 - g13)) < 0 := by
      rw [key]; linarith
    exact neg_of_mul_neg_right h2 p56.le
  have hmeet : SegMeet b b' d c v := by
    refine segMeet_of_sides ?_ ?_
    · refine mul_neg_of_scaled (by positivity) (by positivity) mD1 mD2 ?_ hD'
      rw [hW, hPp]
      have := mul_pos hP (show 0 < g35 * g60 * g51 by positivity)
      linarith
    · refine (mul_neg_of_scaled (by positivity) (by positivity) mE1 mE2 ?_ hD').le
      exact mul_neg_of_pos_of_neg (by positivity) (mul_neg_of_pos_of_neg (by positivity) hQ)
  -- the data of §22: `6` below the chord `4 2` along `u_V`, the cone of Lemma 22.14 (iii) and the
  -- fact of Lemma 22.13 (`ρ ∈ (0, 1)`)
  have kc' : (τ * g13 * g56 + r * g35) • (c' - b) = g35 • (d - b) + (-(τ * g13)) • u := by
    linear_combination (norm := module) (-g35) • VD + (τ * g13) • hu2
  have hc'u : ∃ s δ : ℝ, δ < 0 ∧ c' = b + s • (d - b) + δ • u := by
    refine ⟨g35 / (τ * g13 * g56 + r * g35), (-(τ * g13)) / (τ * g13 * g56 + r * g35),
      div_neg_of_neg_of_pos (neg_neg_of_pos (by positivity)) hΛ0, ?_⟩
    have := combo_div hΛ0.ne' kc'
    linear_combination (norm := module) this
  have kv : (τ * g13) • (-v) = (τ * g13 * g51) • (c - b) + g35 • (b - d) + (g35 * r) • (c' - b) := by
    linear_combination (norm := module) (-(τ * g13)) • hv2 + g35 • VD
  have hcone : ∃ α β γ : ℝ, 0 < α ∧ 0 < β ∧ 0 < γ ∧
      -v = α • (c - b) + β • (b - d) + γ • (c' - b) :=
    ⟨_, _, _, by positivity, by positivity, by positivity,
      combo_div3 (by positivity : (0 : ℝ) < τ * g13).ne' kv⟩
  have cBC : (g10 * g51) • (b - c) = (-(g10 * g35 - g05 * g13)) • (a' - b) +
      (-(g05 * g51)) • (b' - b) + (-(g05 * g61 - g10 * g56)) • (c' - b) := by
    linear_combination (norm := module) (-1 : ℝ) • cC
  have cB'C : (g10 * g51) • (b' - c) = (-(g10 * g35 - g05 * g13)) • (a' - b) +
      (g10 * g51 - g05 * g51) • (b' - b) + (-(g05 * g61 - g10 * g56)) • (c' - b) := by
    linear_combination (norm := module) (-1 : ℝ) • cC
  have cDC : (g10 * g51) • (d - c) = (g10 * g51 * (τ * g13) - (g10 * g35 - g05 * g13)) • (a' - b) +
      (-(g05 * g51)) • (b' - b) + (g10 * g51 * r - (g05 * g61 - g10 * g56)) • (c' - b) := by
    linear_combination (norm := module) (g10 * g51) • VD - cC
  have c6D : (1 : ℝ) • (c' - d) = (-(τ * g13)) • (a' - b) + (0 : ℝ) • (b' - b) +
      (1 - r) • (c' - b) := by
    linear_combination (norm := module) (-1 : ℝ) • VD
  have dd : (g10 * g51) * (g10 * g51) * (g10 * g51) * det3 (b - c) (b' - c) (d - c) =
      ((g10 * g51) * (g10 * g51) * (g51 * (r * g30 - τ * g13 * g60))) * D := by
    rw [det3_scaled_combo cBC cB'C cDC]
    linear_combination (D * (g10 * g51) * (g10 * g51) * (-r)) * hC1 +
      (D * (g10 * g51) * (g10 * g51) * (τ * g13)) * P1
  have d6 : (g10 * g51) * (g10 * g51) * 1 * det3 (b - c) (b' - c) (c' - d) =
      ((g10 * g51) * (g51 * ((1 - r) * g30 + τ * g13 * g60))) * D := by
    rw [det3_scaled_combo cBC cB'C c6D]
    linear_combination (D * (g10 * g51) * (-(1 - r))) * hC1 +
      (D * (g10 * g51) * (-(τ * g13))) * P1
  have hΔ : VDelta b b' c c' d := by
    unfold VDelta
    rw [show det3 (b - c) (b' - c) (c' - c) - det3 (b - c) (b' - c) (d - c) =
      det3 (b - c) (b' - c) (c' - d) by simp only [det3_expand, PiLp.sub_apply]; ring]
    refine mul_pos_of_scaled (by positivity) (by positivity) dd d6 ?_ hD
    have h1 : 0 < r * g30 - τ * g13 * g60 := by linarith
    have k := mul_pos p10 p51
    exact mul_pos (mul_pos (mul_pos k k) (mul_pos p51 h1)) (mul_pos k (mul_pos p51 hDD))
  -- F2
  have hσ₁ : -σ = 1 ∨ -σ = -1 := by
    rcases hσ with h | h
    · right; rw [h]
    · left; rw [h]; norm_num
  exact cert_type21_F2 F G hσ₁
    (pos_of_scaled (by positivity) dT1 (by
      have := mul_pos (show 0 < g05 * g51 * (τ * g13 * g56 + r * g35) by positivity) hσD
      linarith))
    (pos_of_scaled (by positivity) dG1 (by
      have := mul_pos hΛ0 hσD
      linarith))
    (pos_of_scaled (by positivity) dB1 (by
      have := mul_pos (show 0 < g05 * g51 * g63 by positivity) hσD
      linarith))
    hP₁ hm₁ hm₁' hX₁ hσ
    (pos_of_scaled (by positivity) dT2 (by
      have := mul_pos (show 0 < g51 * g10 * g56 by positivity) hσD
      linarith))
    (pos_of_scaled (by positivity) dG2 (by
      have := mul_pos (show 0 < g60 * g51 by positivity) hσD
      linarith))
    (pos_of_scaled (by positivity) dB2 (by
      have := mul_pos (show 0 < g13 * g10 * g56 by positivity) hσD
      linarith))
    hP₂ hm₂ hm₂' hX₂ hmeet hsign hties hc'u hcone hΔ
    (hF2.1 ((-σ) • u) (smul_ne_zero (by rcases hσ with rfl | rfl <;> norm_num) hu0)
      (by rw [det3_smul_right, hN1, mul_zero]) (by rw [det3_smul_right, hN2, mul_zero])).2
    (hF2.2.1 (σ • v) (smul_ne_zero (by rcases hσ with rfl | rfl <;> norm_num) hv0)
      (by rw [det3_smul_right, hN3, mul_zero]) (by rw [det3_smul_right, hN4, mul_zero])).2

/-- **Lemma 16.24 (F2 on the rest of class (c))**, in `τ`: `K − 2` in the pattern `(+, −, +)`,
`2` beyond `013` (`{5 4} > 0`) but not beyond `145` (`{0 3} < 0`), `1 → 0` a quad edge of
`K − 2` (Lemma 16.16), and `|[3 1]| < |[3 4]|`.  Step 1: `[1 0] > [5 1]` (else `Q` at `05`),
`[5 1] > [3 5]` (else `H` at `13`), `[5 6] > [6 0]` (else `Q` at `50` of `K − 6`), hence
`[5 6] > [0 5]` (h1); and `δ_014(2) > δ_014(3)` (else H2, so H1 by `{5 4} > 0`, and `Q` at `23`
of `K − 6`).  Then F2 (`cert_type21_F2_frame`).  Special positions: the ties
`[1 0] = [5 1]`, `[5 1] = [3 5]`, `[5 6] = [6 0]`, `δ_014(3) = δ_014(2)`, and those of the two
vertex tests (`F2ViewsL` along the lines `014 ∩ 346` and `046 ∩ 134`). -/
theorem cert_type21_F2case {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap21 F d) (G : GaleData a a' b b' c c') (hN : CrossNorm G)
    (h45 : 0 < galeD G.l G.m b b') {α β τ : ℝ} (hβ : 0 < β) (hτ : 0 < τ)
    (hco : d = a + α • (b' - a) + β • (c' - a)) (hα : α = τ * galeD G.l G.m b' c)
    (ht : α + β - 1 = τ * galeD G.l G.m c a)
    (hc013 : 0 < (β + τ * galeD G.l G.m c c') * galeD G.l G.m b' b +
      τ * galeD G.l G.m b c * galeD G.l G.m b' c')
    (hn145 : τ * galeD G.l G.m c a' * galeD G.l G.m c' a <
      (β + τ * galeD G.l G.m c c') * galeD G.l G.m a' a)
    (hq10 : EGoodQuad G.l G.m c c' a b b')
    (h31 : galeD G.l G.m c a' < galeD G.l G.m a' b)
    (t10 : galeD G.l G.m c a ≠ galeD G.l G.m b' c)
    (t51 : galeD G.l G.m b' c ≠ galeD G.l G.m a' b')
    (t56 : galeD G.l G.m b' c' ≠ galeD G.l G.m c' a)
    (t23 : F.abc.f a' ≠ F.abc.f d)
    (hF2 : F2ViewsL (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L a a' b b' c c' d)
    (hgen : GenPosTie (insert d ({a, a', b, b', c, c'} : Finset ℝ³))) :
    CertV (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L
      (SegOK21 (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) a a' b b' c c' d) := by
  obtain ⟨s34, s05, s04, s56, s51, s46, s41, s63, s60, s13, s10⟩ := hN.signs F
  have s35 := hN.h35
  have s30 := hN.h30
  have s61 := hN.h61
  have anti := galeD_anti G.l G.m
  obtain ⟨hr, -, -⟩ := type21_r_pos hd hN hco hα ht
  have P1 := type21_id_P1 G.hl G.hm
  have P3 := type21_id_P3 G.hl G.hm
  have q4 := hq10.2.1
  rw [anti a b'] at q4
  have f05 : galeD G.l G.m b' c < galeD G.l G.m a b' := by
    have := neg_of_mul_neg_right q4 s51.le
    linarith
  -- `Q` at `05` of `K − 2`
  rcases lt_or_gt_of_ne t10 with h10 | h10
  · refine cert_type21_Q F hd G hgen (Or.inl ⟨?_, ?_, mul_pos s30 s35⟩)
    · rw [anti b' c]
      exact mul_neg_of_pos_of_neg s10 (by linarith)
    · rw [anti b' c']
      have e1 := mul_pos s61 s05
      have e2 : galeD G.l G.m b' c' * galeD G.l G.m c a <
          galeD G.l G.m b' c' * galeD G.l G.m b' c := mul_lt_mul_of_pos_left h10 s56
      have h6 : galeD G.l G.m c' a < galeD G.l G.m b' c' := by
        by_contra hc
        push Not at hc
        have e3 : galeD G.l G.m b' c' * galeD G.l G.m b' c ≤
            galeD G.l G.m c' a * galeD G.l G.m b' c := mul_le_mul_of_nonneg_right hc s51.le
        linarith
      exact mul_neg_of_pos_of_neg s60 (by linarith)
  -- `H` at `13`
  rcases lt_or_gt_of_ne t51 with h51 | h51
  · refine cert_type21_H F hd G hgen (Or.inl ⟨?_, ?_, mul_pos s61 s63⟩)
    · rw [anti a' b]
      have h4 : galeD G.l G.m b c < galeD G.l G.m a' b := by
        rw [anti b b'] at P3
        have e1 := mul_pos s13 h45
        have e2 : galeD G.l G.m b' c * galeD G.l G.m a' b <
            galeD G.l G.m a' b' * galeD G.l G.m a' b := mul_lt_mul_of_pos_right h51 s34
        by_contra hc
        push Not at hc
        have e3 : galeD G.l G.m a' b' * galeD G.l G.m a' b ≤
            galeD G.l G.m a' b' * galeD G.l G.m b c := mul_le_mul_of_nonneg_left hc s35.le
        linarith
      exact mul_neg_of_pos_of_neg s41 (by linarith)
    · rw [anti a' b']
      exact mul_neg_of_pos_of_neg s51 (by linarith)
  -- `Q` at `50` of `K − 6`
  rcases lt_or_gt_of_ne t56 with h56 | h56
  · obtain ⟨G2, l5, l4, l3, l0, l1, l2, m5, m4, m3, m0, m1, m2⟩ :=
      type21_galeO2 hd G hco hα ht hr.ne' s10.ne'
    obtain ⟨k1, -, -, -⟩ := type21_galeO2_kappa (F := F) G hN hα ht hr G2 l5 l4 l3 l0 l1 l2 m5
      m4 m3 m0 m1 m2
    obtain ⟨-, ⟨B1, -, B3⟩, -, -⟩ := cluster_signs hd.O2 G2
    have anti2 := galeD_anti G2.l G2.m
    have hbc2 : 0 < galeD G2.l G2.m b c := by
      show 0 < G2.l b * G2.m c - G2.m b * G2.l c
      rw [l4, m1, l1, anti b c, anti c a]
      have := mul_pos (mul_pos hβ s41) (mul_pos hr s10)
      linarith
    have hba'2 : galeD G2.l G2.m b a' < 0 := neg_of_mul_neg_left B3 hbc2.le
    have hba2 : galeD G2.l G2.m b a < 0 := neg_of_mul_pos_right B1 hba'2.le
    have v1 : galeD G2.l G2.m c b' = -((β + τ * galeD G.l G.m c c') *
        (β + τ * galeD G.l G.m c c') * (galeD G.l G.m c a * galeD G.l G.m b' c)) := by
      show G2.l c * G2.m b' - G2.m c * G2.l b' = _
      rw [l1, m5, m1, l5, anti c a, anti b' c]
      ring
    have v2 : galeD G2.l G2.m c a = (β + τ * galeD G.l G.m c c') *
        (β + τ * galeD G.l G.m c c') * (galeD G.l G.m c a * galeD G.l G.m c a) := by
      show G2.l c * G2.m a - G2.m c * G2.l a = _
      rw [l1, m0, m1, l0, anti c a]
      ring
    have v3 : galeD G2.l G2.m d b' = -((β + τ * galeD G.l G.m c c') *
        (galeD G.l G.m c' c * galeD G.l G.m a b' + galeD G.l G.m c' a * galeD G.l G.m b' c)) := by
      show G2.l d * G2.m b' - G2.m d * G2.l b' = _
      rw [l2, m5, m2, l5, anti c' c, anti c' a, anti b' c]
      ring
    have v4 : galeD G2.l G2.m d a = (β + τ * galeD G.l G.m c c') *
        (galeD G.l G.m c' a * galeD G.l G.m c a) := by
      show G2.l d * G2.m a - G2.m d * G2.l a = _
      rw [l2, m0, m2, l0, anti c' a]
      ring
    refine cert_type21_Q2 F hd G2 hgen (Or.inl ⟨?_, ?_, ?_⟩)
    · rw [v1, v2]
      have hrr := mul_pos hr hr
      refine mul_neg_of_neg_of_pos ?_ ?_
      · have := mul_pos hrr (mul_pos s10 s51)
        linarith
      · have := mul_pos hrr (mul_pos s10 (sub_pos.mpr h10))
        linarith
    · rw [v3, v4]
      refine mul_neg_of_neg_of_pos ?_ ?_
      · have := mul_pos hr (add_pos (mul_pos s61 s05) (mul_pos s60 s51))
        linarith
      · have e : -((β + τ * galeD G.l G.m c c') *
            (galeD G.l G.m c' c * galeD G.l G.m a b' + galeD G.l G.m c' a * galeD G.l G.m b' c)) +
            (β + τ * galeD G.l G.m c c') * (galeD G.l G.m c' a * galeD G.l G.m c a) =
            (β + τ * galeD G.l G.m c c') * galeD G.l G.m c a *
              (galeD G.l G.m c' a - galeD G.l G.m b' c') := by
          linear_combination (-(β + τ * galeD G.l G.m c c')) * P1
        rw [e]
        exact mul_pos (mul_pos hr s10) (sub_pos.mpr h56)
    · rw [anti2 b' b]
      have hk : 0 < galeD G2.l G2.m b' b := by rw [k1]; exact mul_pos (mul_pos hr s10) hc013
      exact mul_pos_of_neg_of_neg (by linarith) hba2
  -- `δ_014(2)` against `δ_014(3)`
  have hB1 := type21_id_F2B1 G.hl G.hm
  obtain ⟨e1, e2, e3⟩ := type21_f014 F G hco
  rcases lt_trichotomy (α * galeD G.l G.m c' a' + β * galeD G.l G.m a' b')
    (galeD G.l G.m b' c') with hH2 | hH2 | hH2
  · -- H2, hence H1 (`{5 4} > 0`): `Q` at `23` of `K − 6`
    have c1 := type21_id_F2c1 G.hl G.hm
    have c2 := type21_id_F2c2 G.hl G.hm
    have key : (α * galeD G.l G.m c' a' + β * galeD G.l G.m a' b') * galeD G.l G.m b c' -
        β * galeD G.l G.m a' b * galeD G.l G.m b' c' = galeD G.l G.m c' a' *
        ((β + τ * galeD G.l G.m c c') * galeD G.l G.m b' b +
          τ * galeD G.l G.m b c * galeD G.l G.m b' c') := by
      rw [hα, anti c' c, anti b b']
      linear_combination β * c1 + τ * galeD G.l G.m c' a' * c2
    have hH1 : β * galeD G.l G.m a' b < galeD G.l G.m b c' := by
      have k1 := mul_pos s63 hc013
      have k2 : (α * galeD G.l G.m c' a' + β * galeD G.l G.m a' b') * galeD G.l G.m b c' <
          galeD G.l G.m b' c' * galeD G.l G.m b c' := mul_lt_mul_of_pos_right hH2 s46
      by_contra hc
      push Not at hc
      have k3 : galeD G.l G.m b c' * galeD G.l G.m b' c' ≤
          β * galeD G.l G.m a' b * galeD G.l G.m b' c' := mul_le_mul_of_nonneg_right hc s56.le
      linarith
    exact cert_type21_step5 F hd G hN hco hα ht hH1 hH2 hn145 hgen
  · exfalso
    apply t23
    have k : galeD G.l G.m c' a' * F.abc.f d - galeD G.l G.m c' a' * F.abc.f a' =
        F.abc.f b' * (α * galeD G.l G.m c' a' + β * galeD G.l G.m a' b' -
          galeD G.l G.m b' c') := by
      rw [e3]; linear_combination -e1 - β * e2
    rw [hH2, sub_self, mul_zero] at k
    have : galeD G.l G.m c' a' * (F.abc.f d - F.abc.f a') = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h s63.ne'
    · linarith
  -- F2
  have h1 := type21_id_F2h1 G.hl G.hm
  have f56 : galeD G.l G.m a b' < galeD G.l G.m b' c' := by
    by_contra hc
    push Not at hc
    have k1 := mul_pos (sub_pos.mpr h31) s56
    have k2 := mul_pos (sub_pos.mpr h56) s35
    have k3 : 0 ≤ (galeD G.l G.m a b' - galeD G.l G.m b' c') * galeD G.l G.m c' a' :=
      mul_nonneg (by linarith) s63.le
    linarith
  have hal := type21_id_F2al G.hl G.hm
  have hP5 := type21_id_F2P5 G.hl G.hm
  -- the dependencies `[1 ·]`, `[5 ·]` and the cap, in the frame `4; 3, 5, 6`
  have hsc := galeD_sum G.hl G.hm c
  have hvc := (G.hl.galeD G.hm c).vsum
  rw [galeD_self] at hsc hvc
  have hsb := galeD_sum G.hl G.hm b'
  have hvb := (G.hl.galeD G.hm b').vsum
  rw [galeD_self] at hsb hvb
  have VA : galeD G.l G.m c a • (a - b) = (-galeD G.l G.m c a') • (a' - b) +
      galeD G.l G.m b' c • (b' - b) + galeD G.l G.m c' c • (c' - b) := by
    rw [anti c b', anti c c']
    linear_combination (norm := module) hvc - hsc • b
  have VC : galeD G.l G.m b' c • (c - b) = galeD G.l G.m a b' • (a - b) +
      galeD G.l G.m a' b' • (a' - b) - galeD G.l G.m b' c' • (c' - b) := by
    rw [anti b' a, anti b' a']
    linear_combination (norm := module) hvb - hsb • b
  have S : τ * galeD G.l G.m c a' + τ * galeD G.l G.m c b + (β + τ * galeD G.l G.m c c') = 1 := by
    linear_combination τ * hsc + ht - hα - τ * anti b' c
  have VD : d - b = (τ * galeD G.l G.m c a') • (a' - b) +
      (β + τ * galeD G.l G.m c c') • (c' - b) := by
    linear_combination (norm := module) hd.rep2 G hco hα ht + S • b
  have hu : axisView G.l G.m b' b a c = (-galeD G.l G.m a b') • (a - b) +
      galeD G.l G.m b' c • (c - b) := by
    simp only [axisView]; rw [anti b' a]; module
  have hu' : axisView G.l G.m b' b a c' = (-galeD G.l G.m a b') • (a - b) +
      galeD G.l G.m b' c' • (c' - b) := by
    simp only [axisView]; rw [anti b' a]; module
  -- the inequalities of steps 2–3
  have hΛ : galeD G.l G.m b' c' < τ * galeD G.l G.m c a' * galeD G.l G.m b' c' +
      (β + τ * galeD G.l G.m c c') * galeD G.l G.m a' b' := by
    have : τ * galeD G.l G.m c a' * galeD G.l G.m b' c' +
        (β + τ * galeD G.l G.m c c') * galeD G.l G.m a' b' =
        α * galeD G.l G.m c' a' + β * galeD G.l G.m a' b' := by
      rw [hα, anti c' c]; linear_combination τ * hB1
    linarith
  have hP : 0 < (β + τ * galeD G.l G.m c c') * galeD G.l G.m a b' -
      τ * galeD G.l G.m b' c * galeD G.l G.m c' a := by
    have k : galeD G.l G.m a' a * ((β + τ * galeD G.l G.m c c') * galeD G.l G.m a b' -
        τ * galeD G.l G.m b' c * galeD G.l G.m c' a) = galeD G.l G.m a b' *
        ((β + τ * galeD G.l G.m c c') * galeD G.l G.m a' a -
          τ * galeD G.l G.m c a' * galeD G.l G.m c' a) +
        τ * galeD G.l G.m c a * galeD G.l G.m a' b' * galeD G.l G.m c' a := by
      linear_combination τ * galeD G.l G.m c' a * hal
    have : 0 < galeD G.l G.m a' a * ((β + τ * galeD G.l G.m c c') * galeD G.l G.m a b' -
        τ * galeD G.l G.m b' c * galeD G.l G.m c' a) := by
      rw [k]
      have := mul_pos s05 (sub_pos.mpr hn145)
      have := mul_pos (mul_pos (mul_pos hτ s10) s35) s60
      linarith
    exact pos_of_mul_pos_right this s30.le
  have hab : 0 < galeD G.l G.m b' c' - τ * galeD G.l G.m b' c * galeD G.l G.m b' c' -
      ((β + τ * galeD G.l G.m c c') * galeD G.l G.m a b' -
        τ * galeD G.l G.m b' c * galeD G.l G.m c' a) := by
    have k : galeD G.l G.m b' c' - τ * galeD G.l G.m b' c * galeD G.l G.m b' c' -
        ((β + τ * galeD G.l G.m c c') * galeD G.l G.m a b' -
          τ * galeD G.l G.m b' c * galeD G.l G.m c' a) =
        β * (galeD G.l G.m b' c' - galeD G.l G.m a b') := by
      rw [anti c' c]
      linear_combination τ * P1 + galeD G.l G.m b' c' * hα - galeD G.l G.m b' c' * ht
    rw [k]
    exact mul_pos hβ (sub_pos.mpr f56)
  have hP5' : 0 < galeD G.l G.m a' b' * galeD G.l G.m c' a -
      galeD G.l G.m a' b' * galeD G.l G.m b' c' + galeD G.l G.m c a' * galeD G.l G.m b' c' := by
    rw [hP5]
    have := mul_pos s35 s46
    have := mul_pos s63 (sub_pos.mpr h51)
    linarith
  -- the facts of Lemma 22.13: `[1 0][3 5] − [0 5][1 3] = −[5 1][3 0]` (Plücker), `2` not beyond
  -- `145`, and `D = [1 3]([3 0] + [6 0]) − [4 1][3 0] > 0` (F2's `[1 3] < [3 4]`)
  have hC1 : galeD G.l G.m c a * galeD G.l G.m a' b' - galeD G.l G.m a b' * galeD G.l G.m c a' =
      -(galeD G.l G.m b' c * galeD G.l G.m a' a) := by
    have pl := galeD_plucker G.l G.m c a a' b'
    rw [anti b' c, anti a' a] at pl
    linear_combination pl
  have hDD : 0 < (1 - (β + τ * galeD G.l G.m c c')) * galeD G.l G.m a' a +
      τ * galeD G.l G.m c a' * galeD G.l G.m c' a := by
    have pl := galeD_plucker G.l G.m c a' c' a
    have sc := galeD_sum G.hl G.hm c
    have sa := galeD_sum G.hl G.hm a'
    rw [galeD_self, anti b' c] at sc
    rw [galeD_self, anti c a'] at sa
    have key : (1 - (β + τ * galeD G.l G.m c c')) * galeD G.l G.m a' a +
        τ * galeD G.l G.m c a' * galeD G.l G.m c' a =
        τ * (galeD G.l G.m c a * (galeD G.l G.m a' b - galeD G.l G.m c a' +
          galeD G.l G.m a' b') + galeD G.l G.m a' a * galeD G.l G.m b' c) := by
      linear_combination (-galeD G.l G.m a' a) * S + (τ * galeD G.l G.m a' a) * sc -
        (τ * galeD G.l G.m c a) * sa + τ * pl
    rw [key]
    have := sub_pos.mpr h31
    exact mul_pos hτ (add_pos (mul_pos s10 (by linarith)) (mul_pos s30 s51))
  exact cert_type21_F2_frame F G s05 s10 s13 s35 s51 s56 s60 s63 hτ hr VA VC VD hu hu' P1
    hB1 hΛ h51 f05 f56 hP hab hP5' hC1 hn145 hDD hF2

/-- **Theorem 16.23 (class (c), one crossing)**, in `τ`: `K − 2` in the pattern `(+, −, +)`,
`2` beyond `013` (`{5 4} > 0`) but not beyond `145` (`{0 3} < 0`), `1 → 0` a quad edge of
`K − 2` (Lemma 16.16).  If Q fails for `K − 6`, `0 → 4` is an E-good quad edge of `K − 6`
(Lemma 16.22, so (iii)); near or A1 (Lemma 16.21; A1 with `δ_014(2) > δ_014(5)` is `Q` at `25`);
with near and `|[3 1]| > |[3 4]|`, F1 (16.7); with `|[3 1]| < |[3 4]|`, a tier among Q, H and F2
(Lemma 16.24, `cert_type21_F2case`).  Special positions: `f ≠ 0` for `K − 6` (`hpp2`), the
ties `|[3 1]| = |[3 4]|` and those of 16.24, the switch surface `H⁻_c` (`δ_014(2) = δ_014(5)` with
`|[3 1]| > |[3 4]|`), `T1`, and the two vertex tests of F2. -/
theorem cert_type21_classC {a a' b b' c c' d : ℝ³} (F : OctFacets a a' b b' c c')
    (hd : IsCap21 F d) (G : GaleData a a' b b' c c') (hN : CrossNorm G)
    (h45 : 0 < galeD G.l G.m b b') {α β τ : ℝ} (hβ : 0 < β) (hτ : 0 < τ)
    (hco : d = a + α • (b' - a) + β • (c' - a)) (hα : α = τ * galeD G.l G.m b' c)
    (ht : α + β - 1 = τ * galeD G.l G.m c a)
    (hc013 : 0 < (β + τ * galeD G.l G.m c c') * galeD G.l G.m b' b +
      τ * galeD G.l G.m b c * galeD G.l G.m b' c')
    (hn145 : τ * galeD G.l G.m c a' * galeD G.l G.m c' a <
      (β + τ * galeD G.l G.m c c') * galeD G.l G.m a' a)
    (hq10 : EGoodQuad G.l G.m c c' a b b')
    (hpp2 : det3 (a - b) (c - b) (a' - b') ≠ 0)
    (t34 : galeD G.l G.m a' b ≠ galeD G.l G.m c a')
    (t10 : galeD G.l G.m c a ≠ galeD G.l G.m b' c)
    (t51 : galeD G.l G.m b' c ≠ galeD G.l G.m a' b')
    (t56 : galeD G.l G.m b' c' ≠ galeD G.l G.m c' a)
    (t23 : F.abc.f a' ≠ F.abc.f d)
    (hHc : ¬ (F.abc.f d = F.abc.f b' ∧ galeD G.l G.m a' b < galeD G.l G.m c a'))
    (hT1 : ∀ u : ℝ³, u ≠ 0 → ⟪F.abc.N, u⟫ = 0 → ⟪F.ab'c'.N, u⟫ = 0 →
      T1Gen (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L a a' b b' u)
    (hF2 : F2ViewsL (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L a a' b b' c c' d)
    (hgen : GenPosTie (insert d ({a, a', b, b', c, c'} : Finset ℝ³))) :
    CertV (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L
      (SegOK21 (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) a a' b b' c c' d) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, s10⟩ := hN.signs F
  obtain ⟨hr, -, -⟩ := type21_r_pos hd hN hco hα ht
  obtain ⟨G2, l5, l4, l3, l0, l1, l2, m5, m4, m3, m0, m1, m2⟩ :=
    type21_galeO2 hd G hco hα ht hr.ne' s10.ne'
  by_cases hQ2 : Type21Q G2.l G2.m b' b a' a c d
  · exact cert_type21_Q2 F hd G2 hgen hQ2
  have h04 := type21_O2_quad04 hd G hN hα ht hr G2 l5 l4 l3 l0 l1 l2 m5 m4 m3 m0 m1 m2 hc013
    hn145 hpp2 hQ2
  have hiii : F.a'b'c.f a < F.a'b'c.f b ∧ hd.f235.f a < hd.f235.f b := by
    obtain ⟨t1, t2, -⟩ := h04.tests hd.O2.perm₁₂.swap₁.swap₂.swap₃ G2.perm₁₂.swap₁.swap₂.swap₃
    exact ⟨t2, t1⟩
  have hF2 : galeD G.l G.m c a' < galeD G.l G.m a' b →
      CertV (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) L
        (SegOK21 (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) a a' b b' c c' d) :=
    fun h =>
    cert_type21_F2case F hd G hN h45 hβ hτ hco hα ht hc013 hn145 hq10 h t10 t51 t56 t23 hF2 hgen
  rcases type21_near_or_A1 F hd G hN hco hα ht hn145 with hS | hA1
  · rcases lt_or_gt_of_ne t34 with h | h
    · exact cert_type21_F1' F hd G hN hS hiii h hT1 hgen
    · exact hF2 h
  · rcases lt_trichotomy (F.abc.f d) (F.abc.f b') with h3 | h3 | h3
    · exact cert_type21_Q25 F hd G hN hA1 h3 hgen
    · rcases lt_or_gt_of_ne t34 with h | h
      · exact absurd ⟨h3, h⟩ hHc
      · exact hF2 h
    · rcases lt_or_gt_of_ne t34 with h | h
      · exact cert_type21_F1' F hd G hN h3 hiii h hT1 hgen
      · exact hF2 h

end Minimality

end
