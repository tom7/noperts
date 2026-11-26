module

public import Minimality.SplitEdgePlane

/-!
# Tilting in a rim cell: weak depth separation and an infinitesimal-tilt obstruction

Investigates Task FB (whether a strict `k`-rim at `w₀` with strictly unimodal depths can be
tilted `w₀ + t • v` for small `t > 0` to achieve `IsDepthSeparatedAt` / `SplitRows`).

1. **Persistence under small tilts:** `eventually_strictRimN_add_smul` and
   `eventually_hiddenInTriangles_add_smul` show that `StrictRimN` and `HiddenInTriangles`
   persist on `w₀ + t • v` for `∀ᶠ t in 𝓝[>] (0 : ℝ)`.
2. **Sufficient condition (`edgePlaneAny_of_weakDepthSep_tilt`):** if `(a, c)` is antipodal at
   `w₀` and the depths are *weakly* separated across the two arcs (allowing ties
   `⟪X j - X c, w₀⟫ = 0`), then any tilt `v` that breaks the ties in the matching direction
   yields `IsDepthSeparatedAt X (w₀ + t • v) a c` for `∀ᶠ t in 𝓝[>] (0 : ℝ)`, and hence
   `Gen.EdgePlaneAny x` (under `hD ≠ 0`, `hnd ≠ 0` at `w₀`).
   `example_weak_tilt_edgePlane` exhibits a concrete 6-point, 5-rim with a depth tie at
   `w₀ = (0, 0, 1)` that is resolved by a tilt `v = (0, -1, 0)`.
3. **Parallel-edge obstruction at a fixed view (`skew5_no_splitRows`):**
   the concrete integer 5-rim `skewX5` at `w₀ = (0, 0, 1)` has `StrictRimN`, `HiddenInTriangles`,
   and strictly unimodal distinct depths `0 < 1 < 2 < 3 < 4`, yet `SplitRows` fails for every
   `(a, c, σ)` (`c ≠ a`, `c ≠ a + 1`) at `w₀` (due to `E_2 ∥ -E_4`, where `det3 E_2 E_4 w₀ = 0`).
   Perturbing `y₄ = -73` to `-72` or `-74` (or tilting `w₀`) breaks the parallelism and
   restores `SplitRows`.
-/

@[expose] public section

set_option autoImplicit false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality.Split.LexTilt

private theorem det3_continuous_right (a b : ℝ³) : Continuous (fun w : ℝ³ => det3 a b w) := by
  simp only [det3]
  fun_prop

private theorem eventually_pos_add_smul (f : ℝ³ → ℝ) (hf : Continuous f) (w₀ v : ℝ³)
    (h0 : 0 < f w₀) : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < f (w₀ + t • v) := by
  have hc : Continuous fun t : ℝ => f (w₀ + t • v) := hf.comp (by fun_prop)
  have hmem : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < f (w₀ + t • v) :=
    hc.continuousAt.eventually (lt_mem_nhds (by simpa using h0))
  exact hmem.filter_mono nhdsWithin_le_nhds

/-- `StrictRimN` persists under any sufficiently small tilt `w₀ + t • v` (`t > 0`). -/
theorem eventually_strictRimN_add_smul {n k : ℕ} [NeZero k] (x : Fin n → ℝ³)
    (lab : ZMod k → Fin n) (w₀ v : ℝ³) (hrim : StrictRimN x w₀ lab) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), StrictRimN x (w₀ + t • v) lab := by
  have hall : ∀ p : Fin n × ZMod k,
      ∀ᶠ t in 𝓝[>] (0 : ℝ), p.1 ≠ lab p.2 → p.1 ≠ lab (p.2 + 1) →
        0 < det3 (x (lab (p.2 + 1)) - x (lab p.2)) (x p.1 - x (lab p.2)) (w₀ + t • v) := by
    intro p
    by_cases h1 : p.1 ≠ lab p.2
    · by_cases h2 : p.1 ≠ lab (p.2 + 1)
      · filter_upwards [eventually_pos_add_smul _ (det3_continuous_right _ _) w₀ v
          (hrim p.1 p.2 h1 h2)] with t ht _ _
        exact ht
      · exact Filter.Eventually.of_forall fun _ _ hm2 => absurd hm2 h2
    · exact Filter.Eventually.of_forall fun _ hm1 => absurd hm1 h1
  rw [← eventually_all] at hall
  filter_upwards [hall] with t ht m i hm1 hm2
  exact ht (m, i) hm1 hm2

/-- `HiddenInTriangles` persists under any sufficiently small tilt `w₀ + t • v` (`t > 0`). -/
theorem eventually_hiddenInTriangles_add_smul {n k : ℕ} (x : Fin n → ℝ³)
    (lab : ZMod k → Fin n) (w₀ v : ℝ³) (hhid : HiddenInTriangles x w₀ lab) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), HiddenInTriangles x (w₀ + t • v) lab := by
  have hall : ∀ m : Fin n,
      ∀ᶠ t in 𝓝[>] (0 : ℝ), (∀ i, m ≠ lab i) →
        ∃ p ∈ univ.image x, ∃ q ∈ univ.image x, ∃ r ∈ univ.image x,
          0 < det3 (q - p) (r - p) (w₀ + t • v) ∧
          0 < det3 (q - p) (x m - p) (w₀ + t • v) ∧
          0 < det3 (r - q) (x m - q) (w₀ + t • v) ∧
          0 < det3 (p - r) (x m - r) (w₀ + t • v) := by
    intro m
    by_cases hm : ∀ i, m ≠ lab i
    · obtain ⟨p, hp, q, hq, r, hr, h1, h2, h3, h4⟩ := hhid m hm
      filter_upwards
        [eventually_pos_add_smul _ (det3_continuous_right _ _) w₀ v h1,
         eventually_pos_add_smul _ (det3_continuous_right _ _) w₀ v h2,
         eventually_pos_add_smul _ (det3_continuous_right _ _) w₀ v h3,
         eventually_pos_add_smul _ (det3_continuous_right _ _) w₀ v h4]
        with t ht1 ht2 ht3 ht4 _
      exact ⟨p, hp, q, hq, r, hr, ht1, ht2, ht3, ht4⟩
    · exact Filter.Eventually.of_forall fun _ hm' => absurd hm' hm
  rw [← eventually_all] at hall
  filter_upwards [hall] with t ht m hm
  exact ht m hm

private theorem eventually_pos_inner_tilt (d w₀ v : ℝ³) (ε : ℝ) (h0 : 0 ≤ ε * ⟪d, w₀⟫)
    (h1 : ε * ⟪d, w₀⟫ = 0 → 0 < ε * ⟪d, v⟫) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < ε * ⟪d, w₀ + t • v⟫ := by
  rcases h0.lt_or_eq with hlt | heq
  · exact eventually_pos_add_smul (fun w => ε * ⟪d, w⟫) (by fun_prop) w₀ v hlt
  · have hv : 0 < ε * ⟪d, v⟫ := h1 heq.symm
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : 0 < t := ht
    have e : ε * ⟪d, w₀ + t • v⟫ = ε * ⟪d, w₀⟫ + t * (ε * ⟪d, v⟫) := by
      rw [inner_add_right, real_inner_smul_right]; ring
    rw [e, ← heq, zero_add]
    exact mul_pos ht0 hv

/-- **Weak depth separation + tie-breaking tilt yields `IsDepthSeparatedAt` for small `t > 0`.** -/
theorem isDepthSeparatedAt_add_smul_of_weak {k : ℕ} [NeZero k] (X : ZMod k → ℝ³)
    (w₀ v : ℝ³) (a c : ZMod k)
    (hmin : ∀ i, i ≠ c → det3 (X (a + 1) - X a) w₀ (X c) < det3 (X (a + 1) - X a) w₀ (X i))
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (hZ1 : ∀ s : ℕ, 0 < s → s ≤ (a - c).val → 0 ≤ ε * ⟪X (c + s) - X c, w₀⟫)
    (hZ2 : ∀ s : ℕ, (a - c).val < s → s < k → ε * ⟪X (c + s) - X c, w₀⟫ ≤ 0)
    (hT1 : ∀ s : ℕ, 0 < s → s ≤ (a - c).val →
      ⟪X (c + s) - X c, w₀⟫ = 0 → 0 < ε * ⟪X (c + s) - X c, v⟫)
    (hT2 : ∀ s : ℕ, (a - c).val < s → s < k →
      ⟪X (c + s) - X c, w₀⟫ = 0 → ε * ⟪X (c + s) - X c, v⟫ < 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), IsDepthSeparatedAt X (w₀ + t • v) a c := by
  have hmin_ev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ∀ i, i ≠ c → det3 (X (a + 1) - X a) (w₀ + t • v) (X c) <
        det3 (X (a + 1) - X a) (w₀ + t • v) (X i) := by
    have hall : ∀ i : ZMod k, ∀ᶠ t in 𝓝[>] (0 : ℝ), i ≠ c →
        det3 (X (a + 1) - X a) (w₀ + t • v) (X c) <
          det3 (X (a + 1) - X a) (w₀ + t • v) (X i) := by
      intro i
      by_cases hic : i ≠ c
      · have hc : Continuous fun w : ℝ³ =>
            det3 (X (a + 1) - X a) w (X i) - det3 (X (a + 1) - X a) w (X c) := by
          simp only [det3]; fun_prop
        filter_upwards [eventually_pos_add_smul _ hc w₀ v (sub_pos.2 (hmin i hic))] with t ht _
        linarith
      · exact Filter.Eventually.of_forall fun _ h => absurd h hic
    rw [← eventually_all] at hall
    filter_upwards [hall] with t ht i hi
    exact ht i hi
  have harc1 : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ∀ s : ℕ, 0 < s → s ≤ (a - c).val → 0 < ε * ⟪X (c + s) - X c, w₀ + t • v⟫ := by
    have hall : ∀ s : Fin k, ∀ᶠ t in 𝓝[>] (0 : ℝ),
        0 < (s : ℕ) → (s : ℕ) ≤ (a - c).val → 0 < ε * ⟪X (c + (s : ℕ)) - X c, w₀ + t • v⟫ := by
      intro s
      by_cases hs1 : 0 < (s : ℕ)
      · by_cases hs2 : (s : ℕ) ≤ (a - c).val
        · have hev := eventually_pos_inner_tilt (X (c + (s : ℕ)) - X c) w₀ v ε
            (hZ1 s hs1 hs2) (fun h => hT1 s hs1 hs2 (by
              rcases mul_eq_zero.1 h with hε0 | hz
              · rcases hε with rfl | rfl <;> norm_num at hε0
              · exact hz))
          filter_upwards [hev] with t ht _ _; exact ht
        · exact Filter.Eventually.of_forall fun _ _ h => absurd h hs2
      · exact Filter.Eventually.of_forall fun _ h => absurd h hs1
    rw [← eventually_all] at hall
    filter_upwards [hall] with t ht s hs1 hs2
    have hsk : s < k := lt_of_le_of_lt hs2 (ZMod.val_lt _)
    exact ht ⟨s, hsk⟩ hs1 hs2
  have harc2 : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ∀ s : ℕ, (a - c).val < s → s < k → ε * ⟪X (c + s) - X c, w₀ + t • v⟫ < 0 := by
    have hall : ∀ s : Fin k, ∀ᶠ t in 𝓝[>] (0 : ℝ),
        (a - c).val < (s : ℕ) → (s : ℕ) < k → ε * ⟪X (c + (s : ℕ)) - X c, w₀ + t • v⟫ < 0 := by
      intro s
      by_cases hs1 : (a - c).val < (s : ℕ)
      · have hev := eventually_pos_inner_tilt (X (c + (s : ℕ)) - X c) w₀ v (-ε)
          (by have := hZ2 s hs1 s.isLt; linarith)
          (fun h => by
            have hz : ⟪X (c + (s : ℕ)) - X c, w₀⟫ = 0 := by
              rcases mul_eq_zero.1 h with hε0 | hz
              · rcases hε with rfl | rfl <;> norm_num at hε0
              · exact hz
            have := hT2 s hs1 s.isLt hz
            linarith)
        filter_upwards [hev] with t ht _ _; linarith
      · exact Filter.Eventually.of_forall fun _ h => absurd h hs1
    rw [← eventually_all] at hall
    filter_upwards [hall] with t ht s hs1 hs2
    exact ht ⟨s, hs2⟩ hs1 hs2
  filter_upwards [hmin_ev, harc1, harc2] with t hm h1 h2
  refine ⟨hm, ?_⟩
  rcases hε with rfl | rfl
  · left
    refine ⟨fun s hs1 hs2 => ?_, fun s hs1 hs2 => ?_⟩
    · have := h1 s hs1 hs2; rw [one_mul, inner_sub_left] at this; linarith
    · have := h2 s hs1 hs2; rw [one_mul, inner_sub_left] at this; linarith
  · right
    refine ⟨fun s hs1 hs2 => ?_, fun s hs1 hs2 => ?_⟩
    · have := h1 s hs1 hs2; rw [neg_one_mul, inner_sub_left] at this; linarith
    · have := h2 s hs1 hs2; rw [neg_one_mul, inner_sub_left] at this; linarith

/-- **Sufficient tilt theorem (`k ≥ 3`):** weak depth separation + antipodal corner at `w₀`,
together with a tie-breaking tilt `v`, `hD ≠ 0` and `hnd ≠ 0` at `w₀`, yields `Gen.EdgePlaneAny x`. -/
theorem edgePlaneAny_of_weakDepthSep_tilt {n k : ℕ} [NeZero k] (hk : 3 ≤ k) (x : Fin n → ℝ³)
    (lab : ZMod k → Fin n) (hinj : Function.Injective lab) (w₀ v : ℝ³)
    (hrim : StrictRimN x w₀ lab) (hhid : HiddenInTriangles x w₀ lab) (a c : ZMod k)
    (hca : c ≠ a) (hca1 : c ≠ a + 1)
    (hmin : ∀ i, i ≠ c →
      det3 (x (lab (a + 1)) - x (lab a)) w₀ (x (lab c)) <
        det3 (x (lab (a + 1)) - x (lab a)) w₀ (x (lab i)))
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (hZ1 : ∀ s : ℕ, 0 < s → s ≤ (a - c).val → 0 ≤ ε * ⟪x (lab (c + s)) - x (lab c), w₀⟫)
    (hZ2 : ∀ s : ℕ, (a - c).val < s → s < k → ε * ⟪x (lab (c + s)) - x (lab c), w₀⟫ ≤ 0)
    (hT1 : ∀ s : ℕ, 0 < s → s ≤ (a - c).val →
      ⟪x (lab (c + s)) - x (lab c), w₀⟫ = 0 → 0 < ε * ⟪x (lab (c + s)) - x (lab c), v⟫)
    (hT2 : ∀ s : ℕ, (a - c).val < s → s < k →
      ⟪x (lab (c + s)) - x (lab c), w₀⟫ = 0 → ε * ⟪x (lab (c + s)) - x (lab c), v⟫ < 0)
    (hD : ⟪x (lab (a + 1)) - x (lab a), w₀⟫ ≠ 0)
    (hnd : ⟪levelPoint (fun i => x (lab i)) w₀ a c - x (lab c),
      x (lab (a + 1)) - x (lab a)⟫ ≠ 0) :
    Gen.EdgePlaneAny x := by
  let X : ZMod k → ℝ³ := fun i => x (lab i)
  have hnd_at : ContinuousAt (fun t : ℝ => ⟪levelPoint X (w₀ + t • v) a c - X c,
      X (a + 1) - X a⟫) 0 := by
    unfold levelPoint
    have hD0 : ⟪X (a + 1) - X a, w₀ + (0 : ℝ) • v⟫ ≠ 0 := by simpa using hD
    have hdiv : ContinuousAt (fun t : ℝ =>
        ⟪X c - X a, w₀ + t • v⟫ / ⟪X (a + 1) - X a, w₀ + t • v⟫) 0 :=
      ContinuousAt.div (by fun_prop) (by fun_prop) hD0
    have hpt : ContinuousAt (fun t : ℝ =>
        X a + (⟪X c - X a, w₀ + t • v⟫ / ⟪X (a + 1) - X a, w₀ + t • v⟫) • (X (a + 1) - X a) - X c) 0 :=
      (continuousAt_const.add (hdiv.smul continuousAt_const)).sub continuousAt_const
    exact hpt.inner continuousAt_const
  have hnd_ev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ⟪levelPoint X (w₀ + t • v) a c - X c, X (a + 1) - X a⟫ ≠ 0 :=
    (hnd_at.eventually (isOpen_ne.mem_nhds (by simpa using hnd))).filter_mono nhdsWithin_le_nhds
  have hev :=
    (eventually_strictRimN_add_smul x lab w₀ v hrim).and
    ((eventually_hiddenInTriangles_add_smul x lab w₀ v hhid).and
    ((isDepthSeparatedAt_add_smul_of_weak X w₀ v a c hmin ε hε hZ1 hZ2 hT1 hT2).and hnd_ev))
  obtain ⟨t, ⟨hrim_t, hhid_t, hsep_t, hnd_t⟩, -⟩ := (hev.and self_mem_nhdsWithin).exists
  obtain ⟨⟨σ, hS_t⟩, hD_t⟩ := splitRows_of_isDepthSeparatedAt hk x (w₀ + t • v) lab hinj hrim_t a c hsep_t
  have hcv_t : det3 (X (c + 1) - X c) (X (c - 1) - X c) (w₀ + t • v) ≠ 0 := by
    have h1 : c - 1 ≠ c := fun h => by
      have : (1 : ZMod k) = 0 := by linear_combination -h
      have hf : Fact (1 < k) := ⟨by omega⟩
      exact one_ne_zero this
    have h2 : c - 1 ≠ c + 1 := zmod_pred_ne_succ hk c
    exact (hrim_t (lab (c - 1)) c (fun h => h1 (hinj h)) (fun h => h2 (hinj h))).ne'
  obtain ⟨s, α, μ, hrow⟩ := EV.epRows_of_splitRows hk X (w₀ + t • v) a c σ hca hca1 hS_t hD_t hnd_t hcv_t
  exact ⟨k, inferInstance, lab, w₀ + t • v, a, s, α, μ, hk, hinj, hrim_t, hhid_t, hD_t, hrow⟩

/-! ## Satisfiability example for `edgePlaneAny_of_weakDepthSep_tilt` -/

/-- Six-point configuration in `ℝ³` with a depth tie (`z₁ = z₄ = 1`) at `w₀ = (0, 0, 1)`. -/
noncomputable def weakX5 : Fin 6 → ℝ³
  | 0 => !₂[2, 0, 0]
  | 1 => !₂[1, 2, 1]
  | 2 => !₂[-1, 2, 4]
  | 3 => !₂[-2, -1, 3]
  | 4 => !₂[0, -2, 1]
  | 5 => !₂[0, 0, 0]

def weakLab5 : ZMod 5 → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4

/-- `weakX5` at `w₀ = (0, 0, 1)` has a depth tie `z₁ = z₄`, resolved by tilting along
`v = (0, -1, 0)` via `edgePlaneAny_of_weakDepthSep_tilt`. -/
theorem example_weak_tilt_edgePlane : Gen.EdgePlaneAny weakX5 := by
  let w₀ : ℝ³ := !₂[0, 0, 1]
  let v : ℝ³ := !₂[0, -1, 0]
  have hinj : Function.Injective weakLab5 := by decide
  have hrim : StrictRimN weakX5 w₀ weakLab5 := by
    intro m i hm1 hm2
    have hi : ∀ t : ZMod 5, t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 := by decide
    rcases hi i with rfl | rfl | rfl | rfl | rfl <;>
      (try rw [show (4 + 1 : ZMod 5) = 0 from by decide] at hm2 ⊢) <;>
      (try rw [show (3 + 1 : ZMod 5) = 4 from by decide] at hm2 ⊢) <;>
      (try rw [show (2 + 1 : ZMod 5) = 3 from by decide] at hm2 ⊢) <;>
      (try rw [show (1 + 1 : ZMod 5) = 2 from by decide] at hm2 ⊢) <;>
      (try rw [show (0 + 1 : ZMod 5) = 1 from by decide] at hm2 ⊢) <;>
      fin_cases m <;>
      simp_all [weakLab5, weakX5, w₀, det3, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
      try norm_num
  have hhid : HiddenInTriangles weakX5 w₀ weakLab5 := by
    intro m hm
    have hm5 : m = 5 := by
      fin_cases m
      · exact absurd rfl (hm 0)
      · exact absurd rfl (hm 1)
      · exact absurd rfl (hm 2)
      · exact absurd rfl (hm 3)
      · exact absurd rfl (hm 4)
      · rfl
    subst hm5
    refine ⟨weakX5 0, mem_image_of_mem _ (mem_univ 0),
            weakX5 2, mem_image_of_mem _ (mem_univ 2),
            weakX5 3, mem_image_of_mem _ (mem_univ 3), ?_, ?_, ?_, ?_⟩ <;>
      · simp [weakX5, w₀, det3, Matrix.cons_val_zero, Matrix.cons_val_one]; try norm_num
  refine edgePlaneAny_of_weakDepthSep_tilt (k := 5) (by norm_num) weakX5 weakLab5 hinj w₀ v
    hrim hhid 1 4 (by decide) (by decide) ?_ (-1) (Or.inr rfl) ?_ ?_ ?_ ?_ ?_ ?_
  · intro i hi
    have hi' : ∀ t : ZMod 5, t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 := by decide
    rcases hi' i with rfl | rfl | rfl | rfl | rfl
    · simp [weakLab5, weakX5, w₀, det3, Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num
    · simp [weakLab5, weakX5, w₀, det3, Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num
    · simp [weakLab5, weakX5, w₀, det3, Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num
    · simp [weakLab5, weakX5, w₀, det3, Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num
    · exact absurd rfl hi
  · intro s hs1 hs2
    have hca : ((1 : ZMod 5) - 4).val = 2 := by decide
    rw [hca] at hs2
    have hs : s = 1 ∨ s = 2 := by omega
    rcases hs with rfl | rfl <;>
      · simp [weakLab5, weakX5, w₀, inner3, Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num
  · intro s hs1 hs2
    have hca : ((1 : ZMod 5) - 4).val = 2 := by decide
    rw [hca] at hs1
    have hs : s = 3 ∨ s = 4 := by omega
    rcases hs with rfl | rfl <;>
      · simp [weakLab5, weakX5, w₀, inner3, Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num
  · intro s hs1 hs2 h0
    have hca : ((1 : ZMod 5) - 4).val = 2 := by decide
    rw [hca] at hs2
    have hs : s = 1 ∨ s = 2 := by omega
    rcases hs with rfl | rfl
    · simp [weakLab5, weakX5, w₀, inner3, Matrix.cons_val_zero, Matrix.cons_val_one] at h0; norm_num at h0
    · simp [weakLab5, weakX5, v, inner3, Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num
  · intro s hs1 hs2 h0
    have hca : ((1 : ZMod 5) - 4).val = 2 := by decide
    rw [hca] at hs1
    have hs : s = 3 ∨ s = 4 := by omega
    rcases hs with rfl | rfl <;>
      · simp [weakLab5, weakX5, w₀, inner3, Matrix.cons_val_zero, Matrix.cons_val_one] at h0; norm_num at h0
  · simp [weakLab5, weakX5, w₀, inner3, Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num
  · simp [levelPoint, weakLab5, weakX5, w₀, inner3, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num

/-! ## Obstruction to infinitesimal tilts from an arbitrary unimodal view -/

/-- Skewed integer 5-rim in `ℝ³` with strictly unimodal depths `0, 1, 2, 3, 4` at `w₀ = (0, 0, 1)`
that admits no `SplitRows` pair `(a, c, σ)` at `w₀` (nor on `w₀ + t • v` for small `t > 0`). -/
noncomputable def skewX5 : Fin 5 → ℝ³
  | 0 => !₂[100, 3, 0]
  | 1 => !₂[100, 5, 1]
  | 2 => !₂[68, 74, 2]
  | 3 => !₂[-100, -2, 3]
  | 4 => !₂[-68, -73, 4]

def skewLab5 : ZMod 5 → Fin 5
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4

theorem skew5_strictRim : StrictRimN skewX5 !₂[0, 0, 1] skewLab5 := by
  intro m i hm1 hm2
  have hi : ∀ t : ZMod 5, t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 := by decide
  rcases hi i with rfl | rfl | rfl | rfl | rfl <;>
    (try rw [show (4 + 1 : ZMod 5) = 0 from by decide] at hm2 ⊢) <;>
    (try rw [show (3 + 1 : ZMod 5) = 4 from by decide] at hm2 ⊢) <;>
    (try rw [show (2 + 1 : ZMod 5) = 3 from by decide] at hm2 ⊢) <;>
    (try rw [show (1 + 1 : ZMod 5) = 2 from by decide] at hm2 ⊢) <;>
    (try rw [show (0 + 1 : ZMod 5) = 1 from by decide] at hm2 ⊢) <;>
    fin_cases m <;>
    simp_all [skewLab5, skewX5, det3, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    try norm_num

theorem skew5_hiddenInTriangles : HiddenInTriangles skewX5 !₂[0, 0, 1] skewLab5 := by
  intro m hm
  exfalso
  fin_cases m
  · exact hm 0 rfl
  · exact hm 1 rfl
  · exact hm 2 rfl
  · exact hm 3 rfl
  · exact hm 4 rfl

private def skewPt5 : ZMod 5 → ℤ × ℤ × ℤ
  | 0 => (100, 3, 0)
  | 1 => (100, 5, 1)
  | 2 => (68, 74, 2)
  | 3 => (-100, -2, 3)
  | 4 => (-68, -73, 4)

private def skewDet5 (i a : ZMod 5) : ℤ :=
  let (x1, y1, _) := skewPt5 i
  let (x2, y2, _) := skewPt5 (i + 1)
  let (u1, u2, _) := skewPt5 a
  let (v1, v2, _) := skewPt5 (a + 1)
  (x2 - x1) * (v2 - u2) - (y2 - y1) * (v1 - u1)

private theorem skew5_nonpos_witness_int :
    ∀ (a c : ZMod 5) (b : Bool), c ≠ a → c ≠ a + 1 →
      ∃ i j : ZMod 5, i ≠ a ∧ (j = i ∨ j = i + 1) ∧ j ≠ c ∧
        (if b then (1 : ℤ) else -1) * (((skewPt5 j).2.2 - (skewPt5 c).2.2) * skewDet5 i a) ≤ 0 := by
  decide

private theorem skewX5_z (j : ZMod 5) :
    ⟪skewX5 (skewLab5 j), !₂[0, 0, 1]⟫ = ((skewPt5 j).2.2 : ℝ) := by
  have hz5 : ∀ t : ZMod 5, t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 := by decide
  rcases hz5 j with rfl | rfl | rfl | rfl | rfl <;>
    · simp [skewLab5, skewX5, skewPt5, inner3, Matrix.cons_val_zero, Matrix.cons_val_one]

private theorem skewX5_det (i a : ZMod 5) :
    det3 (skewX5 (skewLab5 (i + 1)) - skewX5 (skewLab5 i))
      (skewX5 (skewLab5 (a + 1)) - skewX5 (skewLab5 a)) !₂[0, 0, 1] = (skewDet5 i a : ℝ) := by
  have hz5 : ∀ t : ZMod 5, t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 := by decide
  rcases hz5 i with rfl | rfl | rfl | rfl | rfl <;>
    rcases hz5 a with rfl | rfl | rfl | rfl | rfl <;>
    (try rw [show (4 + 1 : ZMod 5) = 0 from by decide]) <;>
    (try rw [show (3 + 1 : ZMod 5) = 4 from by decide]) <;>
    (try rw [show (2 + 1 : ZMod 5) = 3 from by decide]) <;>
    (try rw [show (1 + 1 : ZMod 5) = 2 from by decide]) <;>
    (try rw [show (0 + 1 : ZMod 5) = 1 from by decide]) <;>
    · simp [skewLab5, skewX5, skewDet5, skewPt5, det3, Matrix.cons_val_zero, Matrix.cons_val_one]; try norm_num

private theorem skew5_nonpos_witness (a c : ZMod 5) (hca : c ≠ a) (hca1 : c ≠ a + 1)
    (s : ℝ) (hs : s = 1 ∨ s = -1) :
    ∃ i j : ZMod 5, i ≠ a ∧ (j = i ∨ j = i + 1) ∧ j ≠ c ∧
      s * (⟪skewX5 (skewLab5 j) - skewX5 (skewLab5 c), !₂[0, 0, 1]⟫ *
        det3 (skewX5 (skewLab5 (i + 1)) - skewX5 (skewLab5 i))
          (skewX5 (skewLab5 (a + 1)) - skewX5 (skewLab5 a)) !₂[0, 0, 1]) ≤ 0 := by
  rcases hs with rfl | rfl
  · obtain ⟨i, j, hia, hj, hjc, hle⟩ := skew5_nonpos_witness_int a c true hca hca1
    refine ⟨i, j, hia, hj, hjc, ?_⟩
    simp only [↓reduceIte] at hle
    rw [inner_sub_left, skewX5_z, skewX5_z, skewX5_det]
    exact_mod_cast hle
  · obtain ⟨i, j, hia, hj, hjc, hle⟩ := skew5_nonpos_witness_int a c false hca hca1
    refine ⟨i, j, hia, hj, hjc, ?_⟩
    simp only [Bool.false_eq_true, ↓reduceIte] at hle
    rw [inner_sub_left, skewX5_z, skewX5_z, skewX5_det]
    exact_mod_cast hle

/-- `skewX5` has no `SplitRows` pair `(a, c, σ)` (`c ≠ a`, `c ≠ a + 1`) at `w₀ = (0, 0, 1)`. -/
theorem skew5_no_splitRows :
    ¬ ∃ a c : ZMod 5, c ≠ a ∧ c ≠ a + 1 ∧ ∃ σ : ℝ,
      SplitRows (fun i => skewX5 (skewLab5 i)) !₂[0, 0, 1] a c σ := by
  rintro ⟨a, c, hca, hca1, σ, hS⟩
  rcases lt_trichotomy σ 0 with hneg | rfl | hpos
  · obtain ⟨i, j, hia, hj, hjc, hle⟩ := skew5_nonpos_witness a c hca hca1 (-1) (Or.inr rfl)
    have hrow := hS i j hia hj hjc
    have hp : 0 ≤ ⟪skewX5 (skewLab5 j) - skewX5 (skewLab5 c), !₂[0, 0, 1]⟫ *
        det3 (skewX5 (skewLab5 (i + 1)) - skewX5 (skewLab5 i))
          (skewX5 (skewLab5 (a + 1)) - skewX5 (skewLab5 a)) !₂[0, 0, 1] := by linarith
    have hmul : σ * (⟪skewX5 (skewLab5 j) - skewX5 (skewLab5 c), !₂[0, 0, 1]⟫ *
        det3 (skewX5 (skewLab5 (i + 1)) - skewX5 (skewLab5 i))
          (skewX5 (skewLab5 (a + 1)) - skewX5 (skewLab5 a)) !₂[0, 0, 1]) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hneg.le hp
    linarith
  · obtain ⟨i, j, hia, hj, hjc, _⟩ := skew5_nonpos_witness a c hca hca1 1 (Or.inl rfl)
    have hrow := hS i j hia hj hjc
    simp at hrow
  · obtain ⟨i, j, hia, hj, hjc, hle⟩ := skew5_nonpos_witness a c hca hca1 1 (Or.inl rfl)
    have hrow := hS i j hia hj hjc
    nlinarith

end Minimality.Split.LexTilt
