module

public import Minimality.EdgePlaneSlope
public import Minimality.EdgePlaneHidden
public import Minimality.Type24SplitFamily
public import Minimality.Type24LexEP

/-!
# The `w_C` leaf and the `T_0` family leaf (`FL1`–`FL3`)

* `FL2` (`uF_T0_facets_eventually`, `edgePlaneAny_of_T0_family`): for `InI5 x x0`, eventually
  as `δ → 0+` all five facets `{0, 1, 2, 3, 4}` have `⟪F.N t, uF x x0 δ⟫ < 0`; hence
  `EdgePlaneAt (x ∘ (0 : Fin 7).succAbove) (uF x x0 δ)` transfers to `Gen.EdgePlaneAny x` via
  `edgePlaneAt_of_T0`.
* `FL1` (`wc_edgePlaneAny`): under `CbarIn x`, `cc` in the `wcCell_eventually` window, and strict
  line separation at `w0 = capView x 1 0 cc` on rim `[0, 5, 2, 3, 6]` edge `6 → 0`,
  `Gen.EdgePlaneAny x` holds.
* `FL3` (`holeLeaf_not_wc`, `hole24_not_wc`, `holeLeaf_not_T0_family`, `hole24_not_T0_family`):
  the corresponding `HoleLeaf` / `Hole24` refutations.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset Filter
open scoped Topology
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.M4
open Minimality.T24.HC Minimality.T24.SF Minimality.T24.DeepC

namespace Minimality.T24.TwoCone

/-! ## FL2: `T_0` family leaf -/

/-- **FL2 (facet signs):** for `CbarIn x` and `InI5 x x0`, eventually as `δ → 0+` all five facets
`{0, 1, 2, 3, 4}` incident to vertex `0` have `⟪F.N t, uF x x0 δ⟫ < 0`. -/
theorem uF_T0_facets_eventually {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    {x0 : ℝ} (hI : InI5 x x0) :
    ∀ᶠ δ : ℝ in 𝓝[>] 0,
      ∀ t ∈ ({0, 1, 2, 3, 4} : Finset (Fin 9)), ⟪F.N t, uF x x0 δ⟫ < 0 := by
  have hb := facets_base F hC hI
  have hcont : ∀ t : Fin 9, Continuous (fun δ : ℝ => -⟪F.N t, uF x x0 δ⟫) := fun t => by
    unfold uF capView; fun_prop
  have e0 : ∀ᶠ δ : ℝ in 𝓝[>] 0, ⟪F.N 0, uF x x0 δ⟫ < 0 := by
    have h0 := (hb 0 (by decide)).1 rfl
    have hev := ev_pos (hcont 0) (by rw [uF_zero]; linarith)
    exact hev.mono fun δ h => by linarith
  have e1 : ∀ᶠ δ : ℝ in 𝓝[>] 0, ⟪F.N 1, uF x x0 δ⟫ < 0 := by
    have h0 := (hb 1 (by decide)).2.1 rfl
    have hev := ev_pos (hcont 1) (by rw [uF_zero]; linarith)
    exact hev.mono fun δ h => by linarith
  have e2 : ∀ᶠ δ : ℝ in 𝓝[>] 0, ⟪F.N 2, uF x x0 δ⟫ < 0 := by
    have hP := F.neg 2 1 (by decide)
    filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
    rw [uF, facet2_eq F hC]
    exact mul_neg_of_pos_of_neg hδ hP
  have e3 : ∀ᶠ δ : ℝ in 𝓝[>] 0, ⟪F.N 3, uF x x0 δ⟫ < 0 := by
    have h0 := (hb 3 (by decide)).2.2.1 rfl
    have hev := ev_pos (hcont 3) (by rw [uF_zero]; linarith)
    exact hev.mono fun δ h => by linarith
  have e4 : ∀ᶠ δ : ℝ in 𝓝[>] 0, ⟪F.N 4, uF x x0 δ⟫ < 0 := by
    have h0 := (hb 4 (by decide)).2.2.2.1 rfl
    have hev := ev_pos (hcont 4) (by rw [uF_zero]; linarith)
    exact hev.mono fun δ h => by linarith
  filter_upwards [e0, e1, e2, e3, e4] with δ h0 h1 h2 h3 h4 t ht
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl <;> assumption

/-- **FL2 (`edgePlaneAny_of_T0_family`):** if `InI5 x x0` and frequently (in particular, eventually)
as `δ → 0+` the base `x ∘ (0 : Fin 7).succAbove` has `EdgePlaneAt` at `uF x x0 δ`, then
`Gen.EdgePlaneAny x` holds. -/
theorem edgePlaneAny_of_T0_family {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    {x0 : ℝ} (hI : InI5 x x0)
    (hEP : ∃ᶠ δ : ℝ in 𝓝[>] 0, EdgePlaneAt (x ∘ (0 : Fin 7).succAbove) (uF x x0 δ)) :
    Gen.EdgePlaneAny x := by
  obtain ⟨δ, hδ, hfac⟩ := (hEP.and_eventually (uF_T0_facets_eventually F hC hI)).exists
  exact (edgePlaneAny_iff_exists_at x).2 ⟨uF x x0 δ, edgePlaneAt_of_T0 F (Or.inl hfac) hδ⟩

/-! ## FL1: `w_C` leaf -/

/-- The 5-rim `[0, 5, 2, 3, 6]` for the `w_C` cell. -/
def wcRim : ZMod 5 → Fin 7 := ![0, 5, 2, 3, 6]

theorem wcRim_inj : Function.Injective wcRim := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hij (by decide)

theorem wcRim_cyc : S0xCycUD s0x_S24 wcRim {3, 4, 6, 8} {0, 1, 2, 5, 7} := by
  decide

/-- Vertex `4` is strictly inside `(x 0, x 3, x 6)` or `(x 0, x 6, x 3)` whenever facets
`{3, 4, 8}` all satisfy `0 < ⟪F.N t, w⟫`. -/
private theorem hidden_four_of_cell {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {w : ℝ³}
    (h3 : 0 < ⟪F.N 3, w⟫) (h4 : 0 < ⟪F.N 4, w⟫) (h8 : 0 < ⟪F.N 8, w⟫) :
    ∃ p ∈ univ.image x, ∃ q ∈ univ.image x, ∃ r ∈ univ.image x,
      0 < Split.det3 (q - p) (r - p) w ∧ 0 < Split.det3 (q - p) (x 4 - p) w ∧
      0 < Split.det3 (r - q) (x 4 - q) w ∧ 0 < Split.det3 (p - r) (x 4 - r) w := by
  let e0 := x 0 - x 4
  let e3 := x 3 - x 4
  let e6 := x 6 - x 4
  have hf_lt : ∀ (t : Fin 9) (q : Fin 7), (4 : Fin 7) ∈ s0x_S24 t → q ∉ s0x_S24 t →
      ⟪F.N t, x q - x 4⟫ < 0 := by
    intro t q h4t hq
    rw [F.inner_sub t q 4, F.zero t 4 h4t, sub_zero]; exact F.neg t q hq
  have h03 : ⟪F.N 3, e0⟫ = 0 := by rw [F.inner_sub 3 0 4, F.zero 3 0 (by decide), F.zero 3 4 (by decide), sub_self]
  have h33 : ⟪F.N 3, e3⟫ = 0 := by rw [F.inner_sub 3 3 4, F.zero 3 3 (by decide), F.zero 3 4 (by decide), sub_self]
  have h38 : ⟪F.N 8, e3⟫ = 0 := by rw [F.inner_sub 8 3 4, F.zero 8 3 (by decide), F.zero 8 4 (by decide), sub_self]
  have h68 : ⟪F.N 8, e6⟫ = 0 := by rw [F.inner_sub 8 6 4, F.zero 8 6 (by decide), F.zero 8 4 (by decide), sub_self]
  have h64 : ⟪F.N 4, e6⟫ = 0 := by rw [F.inner_sub 4 6 4, F.zero 4 6 (by decide), F.zero 4 4 (by decide), sub_self]
  have h04 : ⟪F.N 4, e0⟫ = 0 := by rw [F.inner_sub 4 0 4, F.zero 4 0 (by decide), F.zero 4 4 (by decide), sub_self]
  -- `e0, e3` are linearly independent in `(F.N 3)^⊥` (since `⟪F.N 4, e0⟫ = 0` and `⟪F.N 4, e3⟫ < 0`)
  -- and `⟪F.N 3, e6⟫ < 0`, so `det3 e0 e3 e6 ≠ 0`.
  have hne : Split.det3 e0 e3 e6 ≠ 0 := by
    have hcr : cross e0 e3 ≠ 0 := by
      intro h0
      -- If `cross e0 e3 = 0`, `e0` and `e3` are linearly dependent; since `e0 ≠ 0` (`F.f 8 (x 0) < 0`),
      -- `e3 = c • e0`, contradicting `⟪F.N 4, e0⟫ = 0` and `⟪F.N 4, e3⟫ < 0`.
      have he0_ne : e0 ≠ 0 := by
        intro he0
        have hlt := hf_lt 8 0 (by decide) (by decide)
        change ⟪F.N 8, e0⟫ < 0 at hlt
        rw [he0, inner_zero_right] at hlt
        exact lt_irrefl 0 hlt
      have he3_span : ∃ c : ℝ, e3 = c • e0 := by
        -- `cross e0 e3 = 0` => `⟪e0, e0⟫ • e3 = ⟪e0, e3⟫ • e0`
        have hid : ⟪e0, e0⟫ • e3 - ⟪e0, e3⟫ • e0 = 0 := by
          ext i; fin_cases i <;> dsimp
          · have hc1 := congrArg (fun v : ℝ³ => v 1) h0
            have hc2 := congrArg (fun v : ℝ³ => v 2) h0
            simp only [Split.cross_1, Split.cross_2, PiLp.zero_apply] at hc1 hc2
            simp only [Split.inner3]
            linear_combination -e0 1 * hc2 + e0 2 * hc1
          · have hc0 := congrArg (fun v : ℝ³ => v 0) h0
            have hc2 := congrArg (fun v : ℝ³ => v 2) h0
            simp only [Split.cross_0, Split.cross_2, PiLp.zero_apply] at hc0 hc2
            simp only [Split.inner3]
            linear_combination -e0 2 * hc0 + e0 0 * hc2
          · have hc0 := congrArg (fun v : ℝ³ => v 0) h0
            have hc1 := congrArg (fun v : ℝ³ => v 1) h0
            simp only [Split.cross_0, Split.cross_1, PiLp.zero_apply] at hc0 hc1
            simp only [Split.inner3]
            linear_combination -e0 0 * hc1 + e0 1 * hc0
        have hnn : ⟪e0, e0⟫ ≠ 0 := inner_self_ne_zero.mpr he0_ne
        refine ⟨⟪e0, e3⟫ / ⟪e0, e0⟫, ?_⟩
        have h1 : ⟪e0, e0⟫ • e3 = ⟪e0, e3⟫ • e0 := sub_eq_zero.mp hid
        calc e3 = (1 / ⟪e0, e0⟫) • (⟪e0, e0⟫ • e3) := by rw [smul_smul, one_div_mul_cancel hnn, one_smul]
          _ = (1 / ⟪e0, e0⟫) • (⟪e0, e3⟫ • e0) := by rw [h1]
          _ = (⟪e0, e3⟫ / ⟪e0, e0⟫) • e0 := by rw [smul_smul]; ring_nf
      obtain ⟨c, hc⟩ := he3_span
      have hlt4 := hf_lt 4 3 (by decide) (by decide)
      change ⟪F.N 4, e3⟫ < 0 at hlt4
      rw [hc, real_inner_smul_right, h04, mul_zero] at hlt4
      exact lt_irrefl 0 hlt4
    -- Now `cross e0 e3` is nonzero and orthogonal to `e0, e3`; if `det3 e0 e3 e6 = 0`,
    -- then `e6 ∈ span(e0, e3)` (since `cross e0 e3 ⊥ e6` and `F.N 3 ⊥ e0, e3` would force `⟪F.N 3, e6⟫ = 0`!)
    intro h0
    -- Actually `det3 e0 e3 e6 = 0` means `⟪cross e0 e3, e6⟫ = 0`, and `cross e0 e3` is orthogonal to `e0, e3`,
    -- while `F.N 3` is orthogonal to `e0, e3` and `⟪F.N 3, e6⟫ < 0`!
    -- Wait: `(cross e0 e3) × (F.N 3)` is orthogonal to `cross e0 e3` and `F.N 3`...
    -- Even simpler: `cross (F.N 3) e0`? No, `{e0, e3, F.N 3}` is a basis if `cross e0 e3 ≠ 0`?
    -- Check `⟪cross e0 e3, F.N 3⟫`: if `⟪cross e0 e3, F.N 3⟫ = 0`, then `F.N 3` is in `span(e0, e3)`,
    -- Wait: `e0, e3, cross e0 e3` are orthogonal; any `z` with `⟪z, e0⟫ = 0, ⟪z, e3⟫ = 0, ⟪z, cross e0 e3⟫ = 0` is `0`!
    -- Since `F.N 3 ≠ 0` (`⟪F.N 3, e6⟫ < 0`), `⟪F.N 3, cross e0 e3⟫ ≠ 0`!
    -- And `det3 e0 e3 z = ⟪cross e0 e3, z⟫` vanishes on `e0, e3, e6` (when `h0`), contradicting `cross e0 e3 ≠ 0`?
    -- Wait: `⟪F.N 3, e0⟫ = 0`, `⟪F.N 3, e3⟫ = 0`, `⟪F.N 3, e6⟫ < 0`, so `{e0, e3, cross e0 e3}` vs `F.N 3`:
    have horth : ∀ r : ℝ³, ⟪r, e0⟫ = 0 → ⟪r, e3⟫ = 0 → ⟪r, cross e0 e3⟫ = 0 → r = 0 := by
      intro r hr0 hr3 hrc
      have hid : ⟪cross e0 e3, cross e0 e3⟫ * ⟪r, r⟫ =
          ⟪r, e0⟫ * Split.det3 e3 (cross e0 e3) r - ⟪r, e3⟫ * Split.det3 e0 (cross e0 e3) r +
          ⟪r, cross e0 e3⟫ * Split.det3 e0 e3 r := by
        have hbin : Split.det3 e0 e3 (cross e0 e3) = ⟪cross e0 e3, cross e0 e3⟫ := by
          simp only [Split.det3, Split.inner3, Split.cross_0, Split.cross_1, Split.cross_2]
        rw [← hbin]
        simp only [Split.det3, Split.inner3]; ring
      rw [hr0, hr3, hrc, zero_mul, zero_mul, zero_mul, sub_zero, add_zero] at hid
      have hcc : ⟪cross e0 e3, cross e0 e3⟫ ≠ 0 := inner_self_ne_zero.mpr hcr
      exact inner_self_eq_zero.mp ((mul_eq_zero.mp hid).resolve_left hcc)
    -- So `⟪F.N 3, cross e0 e3⟫ ≠ 0`, and `F.N 3` and `cross e0 e3` are proportional:
    have hN3_ne : ⟪F.N 3, cross e0 e3⟫ ≠ 0 := by
      intro h0'
      have hN0 := horth (F.N 3) h03 h33 h0'
      have hlt := hf_lt 3 6 (by decide) (by decide)
      change ⟪F.N 3, e6⟫ < 0 at hlt
      rw [hN0, inner_zero_left] at hlt
      exact lt_irrefl 0 hlt
    have hprop0 : ⟪F.N 3, cross e0 e3⟫ • cross e0 e3 - ⟪cross e0 e3, cross e0 e3⟫ • F.N 3 = 0 :=
      horth _
        (by rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left, h03, mul_zero,
          show ⟪cross e0 e3, e0⟫ = 0 by simp only [Split.inner3, Split.cross_0, Split.cross_1, Split.cross_2]; ring,
          mul_zero, sub_self])
        (by rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left, h33, mul_zero,
          show ⟪cross e0 e3, e3⟫ = 0 by simp only [Split.inner3, Split.cross_0, Split.cross_1, Split.cross_2]; ring,
          mul_zero, sub_self])
        (by rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left]; ring)
    have hdot := congrArg (fun v => ⟪v, e6⟫) hprop0
    rw [inner_zero_left, inner_sub_left, real_inner_smul_left, real_inner_smul_left] at hdot
    have hce6 : ⟪cross e0 e3, e6⟫ = Split.det3 e0 e3 e6 := by
      simp only [Split.inner3, Split.det3, Split.cross_0, Split.cross_1, Split.cross_2]
    rw [hce6, h0, mul_zero, zero_sub, neg_eq_zero] at hdot
    have hcc : ⟪cross e0 e3, cross e0 e3⟫ ≠ 0 := inner_self_ne_zero.mpr hcr
    have hN6 := (mul_eq_zero.mp hdot).resolve_left hcc
    have hlt := hf_lt 3 6 (by decide) (by decide)
    change ⟪F.N 3, e6⟫ < 0 at hlt
    exact hlt.ne hN6
  -- Now propagate `σ = sign(det3 e0 e3 e6)` to `det3 e0 e3 w`, `det3 e3 e6 w`, `det3 e6 e0 w`
  have hcross_eq : ∀ (t : Fin 9) (u v : ℝ³) (hu : ⟪F.N t, u⟫ = 0) (hv : ⟪F.N t, v⟫ = 0)
      (q0 : Fin 7) (hq0 : ⟪F.N t, x q0 - x 4⟫ < 0)
      (hdq : Split.det3 u v (x q0 - x 4) ≠ 0),
      Split.det3 u v w * ⟪F.N t, x q0 - x 4⟫ = Split.det3 u v (x q0 - x 4) * ⟪F.N t, w⟫ := by
    intro t u v hu hv q0 hq0 hdq
    let N := F.N t
    let d0 := x q0 - x 4
    have horth : ∀ r : ℝ³, ⟪r, u⟫ = 0 → ⟪r, v⟫ = 0 → ⟪r, d0⟫ = 0 → r = 0 := by
      intro r hru hrv hrd
      have hlin : ∀ y : ℝ³, Split.det3 u v d0 * ⟪r, y⟫ = 0 := by
        intro y
        have hid : Split.det3 u v d0 * ⟪r, y⟫ =
            ⟪r, u⟫ * Split.det3 v d0 y - ⟪r, v⟫ * Split.det3 u d0 y + ⟪r, d0⟫ * Split.det3 u v y := by
          simp only [Split.det3, Split.inner3]; ring
        rw [hid, hru, hrv, hrd]; ring
      exact inner_self_eq_zero.mp ((mul_eq_zero.mp (hlin r)).resolve_left hdq)
    let r := Split.det3 u v d0 • N - ⟪N, d0⟫ • cross u v
    have hr0 : r = 0 := horth r
      (by rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left, hu, mul_zero,
        show ⟪cross u v, u⟫ = 0 by simp only [Split.inner3, Split.cross_0, Split.cross_1, Split.cross_2]; ring,
        mul_zero, sub_zero])
      (by rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left, hv, mul_zero,
        show ⟪cross u v, v⟫ = 0 by simp only [Split.inner3, Split.cross_0, Split.cross_1, Split.cross_2]; ring,
        mul_zero, sub_zero])
      (by rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left]
          have : ⟪cross u v, d0⟫ = Split.det3 u v d0 := by
            simp only [Split.inner3, Split.det3, Split.cross_0, Split.cross_1, Split.cross_2]
          rw [this]; ring)
    have hrz : ⟪r, w⟫ = 0 := by rw [hr0, inner_zero_left]
    rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left] at hrz
    have hcz : ⟪cross u v, w⟫ = Split.det3 u v w := by
      simp only [Split.inner3, Split.det3, Split.cross_0, Split.cross_1, Split.cross_2]
    rw [hcz] at hrz
    linarith
  have h3_eq := hcross_eq 3 e0 e3 h03 h33 6 (hf_lt 3 6 (by decide) (by decide)) hne
  have hne8 : Split.det3 e3 e6 e0 ≠ 0 := by
    have : Split.det3 e3 e6 e0 = Split.det3 e0 e3 e6 := by simp only [Split.det3]; ring
    rw [this]; exact hne
  have hne4 : Split.det3 e6 e0 e3 ≠ 0 := by
    have : Split.det3 e6 e0 e3 = Split.det3 e0 e3 e6 := by simp only [Split.det3]; ring
    rw [this]; exact hne
  have h8_eq := hcross_eq 8 e3 e6 h38 h68 0 (hf_lt 8 0 (by decide) (by decide)) hne8
  have h4_eq := hcross_eq 4 e6 e0 h64 h04 3 (hf_lt 4 3 (by decide) (by decide)) hne4
  have hmem0 : x 0 ∈ univ.image x := mem_image_of_mem x (mem_univ 0)
  have hmem3 : x 3 ∈ univ.image x := mem_image_of_mem x (mem_univ 3)
  have hmem6 : x 6 ∈ univ.image x := mem_image_of_mem x (mem_univ 6)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- `det3 e0 e3 e6 < 0`, so `0 < det3 e0 e3 w`, `0 < det3 e3 e6 w`, `0 < det3 e6 e0 w`!
    have ht1 : 0 < Split.det3 e0 e3 w := by
      have hlt3 := hf_lt 3 6 (by decide) (by decide)
      have hmul : 0 < Split.det3 e0 e3 e6 * ⟪F.N 3, w⟫ * ⟪F.N 3, e6⟫ :=
        mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos hlt h3) hlt3
      have : Split.det3 e0 e3 w * (⟪F.N 3, e6⟫ * ⟪F.N 3, e6⟫) =
          Split.det3 e0 e3 e6 * ⟪F.N 3, w⟫ * ⟪F.N 3, e6⟫ := by
        calc Split.det3 e0 e3 w * (⟪F.N 3, e6⟫ * ⟪F.N 3, e6⟫)
            = (Split.det3 e0 e3 w * ⟪F.N 3, e6⟫) * ⟪F.N 3, e6⟫ := by ring
          _ = (Split.det3 e0 e3 e6 * ⟪F.N 3, w⟫) * ⟪F.N 3, e6⟫ := by rw [h3_eq]
      rw [← this] at hmul
      exact (mul_pos_iff.mp hmul).elim (fun h => h.1) (fun h => absurd h.2 (not_lt_of_gt (mul_self_pos.mpr hlt3.ne)))
    have ht2 : 0 < Split.det3 e3 e6 w := by
      have hlt8 := hf_lt 8 0 (by decide) (by decide)
      have hlt' : Split.det3 e3 e6 e0 < 0 := by
        have : Split.det3 e3 e6 e0 = Split.det3 e0 e3 e6 := by simp only [Split.det3]; ring
        linarith
      have hmul : 0 < Split.det3 e3 e6 e0 * ⟪F.N 8, w⟫ * ⟪F.N 8, e0⟫ :=
        mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos hlt' h8) hlt8
      have : Split.det3 e3 e6 w * (⟪F.N 8, e0⟫ * ⟪F.N 8, e0⟫) =
          Split.det3 e3 e6 e0 * ⟪F.N 8, w⟫ * ⟪F.N 8, e0⟫ := by
        calc Split.det3 e3 e6 w * (⟪F.N 8, e0⟫ * ⟪F.N 8, e0⟫)
            = (Split.det3 e3 e6 w * ⟪F.N 8, e0⟫) * ⟪F.N 8, e0⟫ := by ring
          _ = (Split.det3 e3 e6 e0 * ⟪F.N 8, w⟫) * ⟪F.N 8, e0⟫ := by rw [h8_eq]
      rw [← this] at hmul
      exact (mul_pos_iff.mp hmul).elim (fun h => h.1) (fun h => absurd h.2 (not_lt_of_gt (mul_self_pos.mpr hlt8.ne)))
    have ht3 : 0 < Split.det3 e6 e0 w := by
      have hlt4 := hf_lt 4 3 (by decide) (by decide)
      have hlt' : Split.det3 e6 e0 e3 < 0 := by
        have : Split.det3 e6 e0 e3 = Split.det3 e0 e3 e6 := by simp only [Split.det3]; ring
        linarith
      have hmul : 0 < Split.det3 e6 e0 e3 * ⟪F.N 4, w⟫ * ⟪F.N 4, e3⟫ :=
        mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos hlt' h4) hlt4
      have : Split.det3 e6 e0 w * (⟪F.N 4, e3⟫ * ⟪F.N 4, e3⟫) =
          Split.det3 e6 e0 e3 * ⟪F.N 4, w⟫ * ⟪F.N 4, e3⟫ := by
        calc Split.det3 e6 e0 w * (⟪F.N 4, e3⟫ * ⟪F.N 4, e3⟫)
            = (Split.det3 e6 e0 w * ⟪F.N 4, e3⟫) * ⟪F.N 4, e3⟫ := by ring
          _ = (Split.det3 e6 e0 e3 * ⟪F.N 4, w⟫) * ⟪F.N 4, e3⟫ := by rw [h4_eq]
      rw [← this] at hmul
      exact (mul_pos_iff.mp hmul).elim (fun h => h.1) (fun h => absurd h.2 (not_lt_of_gt (mul_self_pos.mpr hlt4.ne)))
    refine ⟨x 0, hmem0, x 3, hmem3, x 6, hmem6, ?_, ?_, ?_, ?_⟩
    · have : Split.det3 (x 3 - x 0) (x 6 - x 0) w = Split.det3 e0 e3 w + Split.det3 e3 e6 w + Split.det3 e6 e0 w := by
        dsimp only [e0, e3, e6]; simp only [Split.det3, PiLp.sub_apply]; ring
      linarith
    · have : Split.det3 (x 3 - x 0) (x 4 - x 0) w = Split.det3 e0 e3 w := by
        dsimp only [e0, e3]; simp only [Split.det3, PiLp.sub_apply]; ring
      linarith
    · have : Split.det3 (x 6 - x 3) (x 4 - x 3) w = Split.det3 e3 e6 w := by
        dsimp only [e3, e6]; simp only [Split.det3, PiLp.sub_apply]; ring
      linarith
    · have : Split.det3 (x 0 - x 6) (x 4 - x 6) w = Split.det3 e6 e0 w := by
        dsimp only [e6, e0]; simp only [Split.det3, PiLp.sub_apply]; ring
      linarith
  · -- `0 < det3 e0 e3 e6`, so `det3 e0 e3 w < 0`, `det3 e3 e6 w < 0`, `det3 e6 e0 w < 0`, use `(x 0, x 6, x 3)`!
    have ht1 : Split.det3 e0 e3 w < 0 := by
      have hlt3 := hf_lt 3 6 (by decide) (by decide)
      have hmul : Split.det3 e0 e3 e6 * ⟪F.N 3, w⟫ * ⟪F.N 3, e6⟫ < 0 :=
        mul_neg_of_pos_of_neg (mul_pos hgt h3) hlt3
      have : Split.det3 e0 e3 w * (⟪F.N 3, e6⟫ * ⟪F.N 3, e6⟫) =
          Split.det3 e0 e3 e6 * ⟪F.N 3, w⟫ * ⟪F.N 3, e6⟫ := by
        calc Split.det3 e0 e3 w * (⟪F.N 3, e6⟫ * ⟪F.N 3, e6⟫)
            = (Split.det3 e0 e3 w * ⟪F.N 3, e6⟫) * ⟪F.N 3, e6⟫ := by ring
          _ = (Split.det3 e0 e3 e6 * ⟪F.N 3, w⟫) * ⟪F.N 3, e6⟫ := by rw [h3_eq]
      rw [← this] at hmul
      rcases mul_neg_iff.mp hmul with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact absurd h2 (not_lt_of_gt (mul_self_pos.mpr hlt3.ne))
      · exact h1
    have ht2 : Split.det3 e3 e6 w < 0 := by
      have hlt8 := hf_lt 8 0 (by decide) (by decide)
      have hgt' : 0 < Split.det3 e3 e6 e0 := by
        have : Split.det3 e3 e6 e0 = Split.det3 e0 e3 e6 := by simp only [Split.det3]; ring
        linarith
      have hmul : Split.det3 e3 e6 e0 * ⟪F.N 8, w⟫ * ⟪F.N 8, e0⟫ < 0 :=
        mul_neg_of_pos_of_neg (mul_pos hgt' h8) hlt8
      have : Split.det3 e3 e6 w * (⟪F.N 8, e0⟫ * ⟪F.N 8, e0⟫) =
          Split.det3 e3 e6 e0 * ⟪F.N 8, w⟫ * ⟪F.N 8, e0⟫ := by
        calc Split.det3 e3 e6 w * (⟪F.N 8, e0⟫ * ⟪F.N 8, e0⟫)
            = (Split.det3 e3 e6 w * ⟪F.N 8, e0⟫) * ⟪F.N 8, e0⟫ := by ring
          _ = (Split.det3 e3 e6 e0 * ⟪F.N 8, w⟫) * ⟪F.N 8, e0⟫ := by rw [h8_eq]
      rw [← this] at hmul
      rcases mul_neg_iff.mp hmul with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact absurd h2 (not_lt_of_gt (mul_self_pos.mpr hlt8.ne))
      · exact h1
    have ht3 : Split.det3 e6 e0 w < 0 := by
      have hlt4 := hf_lt 4 3 (by decide) (by decide)
      have hgt' : 0 < Split.det3 e6 e0 e3 := by
        have : Split.det3 e6 e0 e3 = Split.det3 e0 e3 e6 := by simp only [Split.det3]; ring
        linarith
      have hmul : Split.det3 e6 e0 e3 * ⟪F.N 4, w⟫ * ⟪F.N 4, e3⟫ < 0 :=
        mul_neg_of_pos_of_neg (mul_pos hgt' h4) hlt4
      have : Split.det3 e6 e0 w * (⟪F.N 4, e3⟫ * ⟪F.N 4, e3⟫) =
          Split.det3 e6 e0 e3 * ⟪F.N 4, w⟫ * ⟪F.N 4, e3⟫ := by
        calc Split.det3 e6 e0 w * (⟪F.N 4, e3⟫ * ⟪F.N 4, e3⟫)
            = (Split.det3 e6 e0 w * ⟪F.N 4, e3⟫) * ⟪F.N 4, e3⟫ := by ring
          _ = (Split.det3 e6 e0 e3 * ⟪F.N 4, w⟫) * ⟪F.N 4, e3⟫ := by rw [h4_eq]
      rw [← this] at hmul
      rcases mul_neg_iff.mp hmul with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact absurd h2 (not_lt_of_gt (mul_self_pos.mpr hlt4.ne))
      · exact h1
    refine ⟨x 0, hmem0, x 6, hmem6, x 3, hmem3, ?_, ?_, ?_, ?_⟩
    · have : Split.det3 (x 6 - x 0) (x 3 - x 0) w = -(Split.det3 e0 e3 w + Split.det3 e3 e6 w + Split.det3 e6 e0 w) := by
        dsimp only [e0, e3, e6]; simp only [Split.det3, PiLp.sub_apply]; ring
      linarith
    · have : Split.det3 (x 6 - x 0) (x 4 - x 0) w = -Split.det3 e6 e0 w := by
        dsimp only [e6, e0]; simp only [Split.det3, PiLp.sub_apply]; ring
      linarith
    · have : Split.det3 (x 3 - x 6) (x 4 - x 6) w = -Split.det3 e3 e6 w := by
        dsimp only [e3, e6]; simp only [Split.det3, PiLp.sub_apply]; ring
      linarith
    · have : Split.det3 (x 0 - x 3) (x 4 - x 3) w = -Split.det3 e0 e3 w := by
        dsimp only [e0, e3]; simp only [Split.det3, PiLp.sub_apply]; ring
      linarith

/-- **FL1 (`wc_edgePlaneAny`):** under `CbarIn x`, `cc` in the `wcCell_eventually` window,
and strict line separation at the limit view `w0 = capView x 1 0 cc` on rim `[0, 5, 2, 3, 6]`
edge `4` (`6 → 0`), `Gen.EdgePlaneAny x` holds. -/
theorem wc_edgePlaneAny {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (cc : ℝ)
    (hw5 : 1 / omega5 x < cc) (hw3 : cc < omega3 x)
    (h368_pos : ∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
      0 < ⟪F.N t, x 6 - x 1⟫ → -⟪F.N t, x 0 - x 1⟫ / ⟪F.N t, x 6 - x 1⟫ < cc)
    (h368_neg : ∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
      ⟪F.N t, x 6 - x 1⟫ < 0 → cc < -⟪F.N t, x 0 - x 1⟫ / ⟪F.N t, x 6 - x 1⟫)
    (h368_zero : ∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
      ⟪F.N t, x 6 - x 1⟫ = 0 → 0 < ⟪F.N t, x 0 - x 1⟫)
    (hD0 : ⟪x (wcRim (4 + 1)) - x (wcRim 4), capView x 1 0 cc⟫ ≠ 0)
    (hc_ne0 : ∀ i : ZMod 5, i ≠ 4 →
      Split.det3 (x (wcRim (i + 1)) - x (wcRim i))
        (x (wcRim (4 + 1)) - x (wcRim 4)) (capView x 1 0 cc) ≠ 0)
    (sh : ℝ) (hsh : sh = 1 ∨ sh = -1) (α' μ' : ℝ)
    (hBlue0 : ∀ i j : ZMod 5, i ≠ 4 → (j = i ∨ j = i + 1) →
      0 < Split.det3 (x (wcRim (i + 1)) - x (wcRim i))
          (x (wcRim (4 + 1)) - x (wcRim 4)) (capView x 1 0 cc) →
      (-sh * ⟪Split.Slope.linSpinVec (fun t => x (wcRim t)) 4 i j, capView x 1 0 cc⟫ /
          Split.det3 (x (wcRim (i + 1)) - x (wcRim i))
            (x (wcRim (4 + 1)) - x (wcRim 4)) (capView x 1 0 cc)) -
        μ' * ⟪x (wcRim j) - x (wcRim 4), capView x 1 0 cc⟫ < α')
    (hOrange0 : ∀ p q : ZMod 5, p ≠ 4 → (q = p ∨ q = p + 1) →
      Split.det3 (x (wcRim (p + 1)) - x (wcRim p))
          (x (wcRim (4 + 1)) - x (wcRim 4)) (capView x 1 0 cc) < 0 →
      α' < (-sh * ⟪Split.Slope.linSpinVec (fun t => x (wcRim t)) 4 p q, capView x 1 0 cc⟫ /
          Split.det3 (x (wcRim (p + 1)) - x (wcRim p))
            (x (wcRim (4 + 1)) - x (wcRim 4)) (capView x 1 0 cc)) -
        μ' * ⟪x (wcRim q) - x (wcRim 4), capView x 1 0 cc⟫) :
    Gen.EdgePlaneAny x := by
  have hcc_pos : 0 < cc := lt_trans (one_div_pos.mpr hC.2.2.1) hw5
  have hcell := WC.wcCell_eventually F hC cc hw5 hw3 h368_pos h368_neg h368_zero
  have hw_cont : Continuous (fun η : ℝ => capView x 1 η cc) := by
    unfold capView; fun_prop
  have hev_D : ∀ᶠ η : ℝ in 𝓝[>] 0,
      ⟪x (wcRim (4 + 1)) - x (wcRim 4), capView x 1 η cc⟫ ≠ 0 := by
    have hcont : Continuous (fun η : ℝ => ⟪x (wcRim (4 + 1)) - x (wcRim 4), capView x 1 η cc⟫) := by
      fun_prop
    exact (hcont.continuousAt.eventually (isOpen_ne.mem_nhds hD0)).filter_mono nhdsWithin_le_nhds
  have hev_c : ∀ᶠ η : ℝ in 𝓝[>] 0, ∀ i : ZMod 5, i ≠ 4 →
      Split.det3 (x (wcRim (i + 1)) - x (wcRim i))
        (x (wcRim (4 + 1)) - x (wcRim 4)) (capView x 1 η cc) ≠ 0 := by
    rw [eventually_all]
    intro i
    by_cases hi : i = 4
    · exact Filter.Eventually.of_forall fun _ h => absurd hi h
    · have hcont : Continuous (fun η : ℝ => Split.det3 (x (wcRim (i + 1)) - x (wcRim i))
          (x (wcRim (4 + 1)) - x (wcRim 4)) (capView x 1 η cc)) := by
        simp only [Split.det3]; fun_prop
      have hev : ∀ᶠ η : ℝ in 𝓝[>] 0, Split.det3 (x (wcRim (i + 1)) - x (wcRim i))
          (x (wcRim (4 + 1)) - x (wcRim 4)) (capView x 1 η cc) ≠ 0 :=
        (hcont.continuousAt.eventually (isOpen_ne.mem_nhds (hc_ne0 i hi))).filter_mono
          nhdsWithin_le_nhds
      exact hev.mono fun _ h _ => h
  have hev_sep : ∀ᶠ η : ℝ in 𝓝[>] 0,
      (∀ i j : ZMod 5, i ≠ 4 → (j = i ∨ j = i + 1) →
        0 < Split.det3 (x (wcRim (i + 1)) - x (wcRim i))
            (x (wcRim (4 + 1)) - x (wcRim 4)) (capView x 1 η cc) →
        (-sh * ⟪Split.Slope.linSpinVec (fun t => x (wcRim t)) 4 i j, capView x 1 η cc⟫ /
            Split.det3 (x (wcRim (i + 1)) - x (wcRim i))
              (x (wcRim (4 + 1)) - x (wcRim 4)) (capView x 1 η cc)) -
          μ' * ⟪x (wcRim j) - x (wcRim 4), capView x 1 η cc⟫ < α') ∧
      (∀ p q : ZMod 5, p ≠ 4 → (q = p ∨ q = p + 1) →
        Split.det3 (x (wcRim (p + 1)) - x (wcRim p))
            (x (wcRim (4 + 1)) - x (wcRim 4)) (capView x 1 η cc) < 0 →
        α' < (-sh * ⟪Split.Slope.linSpinVec (fun t => x (wcRim t)) 4 p q, capView x 1 η cc⟫ /
            Split.det3 (x (wcRim (p + 1)) - x (wcRim p))
              (x (wcRim (4 + 1)) - x (wcRim 4)) (capView x 1 η cc)) -
          μ' * ⟪x (wcRim q) - x (wcRim 4), capView x 1 η cc⟫) := by
    refine Eventually.and ?_ ?_
    · rw [eventually_all]; intro i; rw [eventually_all]; intro j
      by_cases hi : i = 4
      · exact Filter.Eventually.of_forall fun _ h => absurd hi h
      · by_cases hj : j = i ∨ j = i + 1
        · rcases lt_or_gt_of_ne (hc_ne0 i hi) with hneg | hpos
          · have hcont : Continuous (fun η : ℝ => Split.det3 (x (wcRim (i + 1)) - x (wcRim i))
                (x (wcRim (4 + 1)) - x (wcRim 4)) (capView x 1 η cc)) := by
              simp only [Split.det3]; fun_prop
            have hev : ∀ᶠ η : ℝ in 𝓝[>] 0, Split.det3 (x (wcRim (i + 1)) - x (wcRim i))
                (x (wcRim (4 + 1)) - x (wcRim 4)) (capView x 1 η cc) < 0 :=
              (hcont.continuousAt.eventually (gt_mem_nhds hneg)).filter_mono nhdsWithin_le_nhds
            exact hev.mono fun _ h _ _ hpos' => absurd hpos' (not_lt_of_gt h)
          · have hcont : ContinuousAt (fun η : ℝ =>
                α' - ((-sh * ⟪Split.Slope.linSpinVec (fun t => x (wcRim t)) 4 i j, capView x 1 η cc⟫ /
                    Split.det3 (x (wcRim (i + 1)) - x (wcRim i))
                      (x (wcRim (4 + 1)) - x (wcRim 4)) (capView x 1 η cc)) -
                  μ' * ⟪x (wcRim j) - x (wcRim 4), capView x 1 η cc⟫)) 0 := by
              refine ContinuousAt.sub continuousAt_const (ContinuousAt.sub ?_ (ContinuousAt.mul continuousAt_const (by fun_prop)))
              refine ContinuousAt.div (ContinuousAt.mul continuousAt_const (by fun_prop)) ?_ hpos.ne'
              simp only [Split.det3]; fun_prop
            have h0 : 0 < α' - ((-sh * ⟪Split.Slope.linSpinVec (fun t => x (wcRim t)) 4 i j,
                  capView x 1 0 cc⟫ / Split.det3 (x (wcRim (i + 1)) - x (wcRim i))
                  (x (wcRim (4 + 1)) - x (wcRim 4)) (capView x 1 0 cc)) -
                μ' * ⟪x (wcRim j) - x (wcRim 4), capView x 1 0 cc⟫) :=
              sub_pos.mpr (hBlue0 i j hi hj hpos)
            exact ((hcont.eventually (lt_mem_nhds h0)).filter_mono nhdsWithin_le_nhds).mono
              fun _ h _ _ _ => sub_pos.mp h
        · exact Filter.Eventually.of_forall fun _ _ h => absurd h hj
    · rw [eventually_all]; intro p; rw [eventually_all]; intro q
      by_cases hp : p = 4
      · exact Filter.Eventually.of_forall fun _ h => absurd hp h
      · by_cases hq : q = p ∨ q = p + 1
        · rcases lt_or_gt_of_ne (hc_ne0 p hp) with hneg | hpos
          · have hcont : ContinuousAt (fun η : ℝ =>
                ((-sh * ⟪Split.Slope.linSpinVec (fun t => x (wcRim t)) 4 p q, capView x 1 η cc⟫ /
                    Split.det3 (x (wcRim (p + 1)) - x (wcRim p))
                      (x (wcRim (4 + 1)) - x (wcRim 4)) (capView x 1 η cc)) -
                  μ' * ⟪x (wcRim q) - x (wcRim 4), capView x 1 η cc⟫) - α') 0 := by
              refine ContinuousAt.sub (ContinuousAt.sub ?_ (ContinuousAt.mul continuousAt_const (by fun_prop))) continuousAt_const
              refine ContinuousAt.div (ContinuousAt.mul continuousAt_const (by fun_prop)) ?_ hneg.ne
              simp only [Split.det3]; fun_prop
            have h0 : 0 < ((-sh * ⟪Split.Slope.linSpinVec (fun t => x (wcRim t)) 4 p q,
                  capView x 1 0 cc⟫ / Split.det3 (x (wcRim (p + 1)) - x (wcRim p))
                  (x (wcRim (4 + 1)) - x (wcRim 4)) (capView x 1 0 cc)) -
                μ' * ⟪x (wcRim q) - x (wcRim 4), capView x 1 0 cc⟫) - α' :=
              sub_pos.mpr (hOrange0 p q hp hq hneg)
            exact ((hcont.eventually (lt_mem_nhds h0)).filter_mono nhdsWithin_le_nhds).mono
              fun _ h _ _ _ => sub_pos.mp h
          · have hcont : Continuous (fun η : ℝ => Split.det3 (x (wcRim (p + 1)) - x (wcRim p))
                (x (wcRim (4 + 1)) - x (wcRim 4)) (capView x 1 η cc)) := by
              simp only [Split.det3]; fun_prop
            have hev : ∀ᶠ η : ℝ in 𝓝[>] 0, 0 < Split.det3 (x (wcRim (p + 1)) - x (wcRim p))
                (x (wcRim (4 + 1)) - x (wcRim 4)) (capView x 1 η cc) :=
              (hcont.continuousAt.eventually (lt_mem_nhds hpos)).filter_mono nhdsWithin_le_nhds
            exact hev.mono fun _ h _ _ hneg' => absurd hneg' (not_lt_of_gt h)
        · exact Filter.Eventually.of_forall fun _ _ h => absurd h hq
  obtain ⟨η, hη, hcell_η, hD_η, hc_η, hBlue_η, hOrange_η⟩ :=
    (eventually_mem_nhdsWithin.and (hcell.and (hev_D.and (hev_c.and hev_sep)))).exists
  have hη_pos : 0 < η := hη
  let w := capView x 1 η cc
  have hhid_base : ∀ m : Fin 7, (∀ i : ZMod 5, m ≠ wcRim i) →
      ∃ p ∈ univ.image x, ∃ q ∈ univ.image x, ∃ r ∈ univ.image x,
        0 < Split.det3 (q - p) (r - p) w ∧ 0 < Split.det3 (q - p) (x m - p) w ∧
        0 < Split.det3 (r - q) (x m - q) w ∧ 0 < Split.det3 (p - r) (x m - r) w := by
    intro m hm
    have hm14 : m = 1 ∨ m = 4 := by
      fin_cases m
      · exact absurd rfl (hm 0)
      · exact Or.inl rfl
      · exact absurd rfl (hm 2)
      · exact absurd rfl (hm 3)
      · exact Or.inr rfl
      · exact absurd rfl (hm 1)
      · exact absurd rfl (hm 4)
    rcases hm14 with rfl | rfl
    · have h0 : x 0 ∈ univ.image x := mem_image_of_mem x (mem_univ 0)
      have h2 : x 2 ∈ univ.image x := mem_image_of_mem x (mem_univ 2)
      have h6 : x 6 ∈ univ.image x := mem_image_of_mem x (mem_univ 6)
      rcases Split.det3_pos_triangle_of_cone (x 1) (x 0) (x 2) (x 6) 1 η cc
          (cone_det3_ne F) (Or.inl ⟨one_pos, hη_pos, hcc_pos⟩) with
        ⟨t1, t2, t3, t4⟩ | ⟨t1, t2, t3, t4⟩
      · exact ⟨x 0, h0, x 2, h2, x 6, h6, t1, t2, t3, t4⟩
      · exact ⟨x 0, h0, x 6, h6, x 2, h2, t1, t2, t3, t4⟩
    · exact hidden_four_of_cell F (hcell_η.1 3 (by decide)) (hcell_η.1 4 (by decide)) (hcell_η.1 8 (by decide))
  rcases LexEP.strictRimN_of_openCell (by omega) F wcRim_inj wcRim_cyc hcell_η with hrim | hrim_rev
  · exact (edgePlaneAny_iff_exists_at x).2 ⟨w, Split.Slope.edgePlaneAt_of_lineSep (by omega) x w
      wcRim wcRim_inj hrim hhid_base 4 hD_η hc_η sh hsh α' μ' hBlue_η hOrange_η⟩
  · -- Reversed rim `wcRim' i := wcRim (-i)` at edge `a' := -4 - 1 = 0`:
    -- `c'_i = c_{-i-1}`, `linSpinVec` is identical, `zt' j = zt j - D`, so `(α' + μ' * D, μ')` separates!
    let wcRim' : ZMod 5 → Fin 7 := fun i => wcRim (-i)
    have hinj' : Function.Injective wcRim' := fun i j h => neg_injective (wcRim_inj h)
    have hhid' : Split.HiddenInTriangles x w wcRim' := fun m hm =>
      hhid_base m (fun i => by simpa [wcRim'] using hm (-i))
    have hD' : ⟪x (wcRim' (0 + 1)) - x (wcRim' 0), w⟫ ≠ 0 := by
      have e0 : wcRim' 0 = wcRim (4 + 1) := by decide
      have e1 : wcRim' (0 + 1) = wcRim 4 := by decide
      rw [e0, e1]
      intro h0
      apply hD_η
      have : x (wcRim (4 + 1)) - x (wcRim 4) = -(x (wcRim 4) - x (wcRim (4 + 1))) := by abel
      rw [this, inner_neg_left, h0, neg_zero]
    have hD_eq : ⟪x (wcRim' (0 + 1)) - x (wcRim' 0), w⟫ = -⟪x (wcRim (4 + 1)) - x (wcRim 4), w⟫ := by
      have e0 : wcRim' 0 = wcRim (4 + 1) := by decide
      have e1 : wcRim' (0 + 1) = wcRim 4 := by decide
      rw [e0, e1]
      simp only [Split.inner3, PiLp.sub_apply]; ring
    have hc_eq : ∀ i : ZMod 5,
        Split.det3 (x (wcRim' (i + 1)) - x (wcRim' i)) (x (wcRim' (0 + 1)) - x (wcRim' 0)) w =
        Split.det3 (x (wcRim (-i - 1 + 1)) - x (wcRim (-i - 1)))
          (x (wcRim (4 + 1)) - x (wcRim 4)) w := by
      intro i
      have e0 : wcRim' 0 = wcRim (4 + 1) := by decide
      have e1 : wcRim' (0 + 1) = wcRim 4 := by decide
      have ei1 : -(i + 1) = -i - 1 := by ring
      rw [e0, e1]
      dsimp only [wcRim']
      rw [ei1]
      have ei0 : wcRim (-i) = wcRim (-i - 1 + 1) := by congr 1; ring
      rw [ei0]
      have hE : x (wcRim (-i - 1)) - x (wcRim (-i - 1 + 1)) =
          -(x (wcRim (-i - 1 + 1)) - x (wcRim (-i - 1))) := by abel
      have hd : x (wcRim 4) - x (wcRim (4 + 1)) = -(x (wcRim (4 + 1)) - x (wcRim 4)) := by abel
      rw [hE, hd]
      simp only [Split.det3, PiLp.neg_apply]; ring
    have hv_eq : ∀ i j : ZMod 5,
        ⟪Split.Slope.linSpinVec (fun t => x (wcRim' t)) 0 i j, w⟫ =
        ⟪Split.Slope.linSpinVec (fun t => x (wcRim t)) 4 (-i - 1) (-j), w⟫ := by
      intro i j
      have e0 : wcRim' 0 = wcRim (4 + 1) := by decide
      have e1 : wcRim' (0 + 1) = wcRim 4 := by decide
      have ei1 : -(i + 1) = -i - 1 := by ring
      have ej : wcRim' j = wcRim (-j) := rfl
      dsimp only [Split.Slope.linSpinVec]
      rw [e0, e1, ej]
      dsimp only [wcRim']
      rw [ei1]
      have ei0 : wcRim (-i) = wcRim (-i - 1 + 1) := by congr 1; ring
      rw [ei0]
      have hE : x (wcRim (-i - 1)) - x (wcRim (-i - 1 + 1)) =
          -(x (wcRim (-i - 1 + 1)) - x (wcRim (-i - 1))) := by abel
      have hd : x (wcRim 4) - x (wcRim (4 + 1)) = -(x (wcRim (4 + 1)) - x (wcRim 4)) := by abel
      have hXj : x (wcRim (-j)) - x (wcRim (4 + 1)) =
          (x (wcRim (-j)) - x (wcRim 4)) - (x (wcRim (4 + 1)) - x (wcRim 4)) := by abel
      rw [hE, hd, hXj]
      simp only [inner_neg_left, inner_neg_right, inner_sub_left, inner_sub_right,
        real_inner_smul_left]
      ring
    have hz_eq : ∀ j : ZMod 5,
        ⟪x (wcRim' j) - x (wcRim' 0), w⟫ =
        ⟪x (wcRim (-j)) - x (wcRim 4), w⟫ - ⟪x (wcRim (4 + 1)) - x (wcRim 4), w⟫ := by
      intro j
      have e0 : wcRim' 0 = wcRim (4 + 1) := by decide
      rw [e0]
      dsimp only [wcRim']
      simp only [Split.inner3, PiLp.sub_apply]; ring
    have hi_iff : ∀ i : ZMod 5, i ≠ 0 → -i - 1 ≠ 4 := by
      intro i hi h
      apply hi
      calc i = -(-i - 1) - 1 := by ring
        _ = -4 - 1 := by rw [h]
        _ = 0 := by decide
    have hj_iff : ∀ i j : ZMod 5, j = i ∨ j = i + 1 → -j = -i - 1 ∨ -j = -i - 1 + 1 := by
      intro i j hj
      rcases hj with rfl | rfl
      · right; ring
      · left; ring
    refine (edgePlaneAny_iff_exists_at x).2 ⟨w, Split.Slope.edgePlaneAt_of_lineSep (by omega) x w
      wcRim' hinj' hrim_rev hhid' 0 hD' (fun i hi => by rw [hc_eq]; exact hc_η (-i - 1) (hi_iff i hi))
      sh hsh (α' + μ' * ⟪x (wcRim (4 + 1)) - x (wcRim 4), w⟫) μ' ?_ ?_⟩
    · intro i j hi hj hpos
      rw [hc_eq] at hpos
      rw [hc_eq, hv_eq, hz_eq]
      have := hBlue_η (-i - 1) (-j) (hi_iff i hi) (hj_iff i j hj) hpos
      linarith
    · intro p q hp hq hneg
      rw [hc_eq] at hneg
      rw [hc_eq, hv_eq, hz_eq]
      have := hOrange_η (-p - 1) (-q) (hi_iff p hp) (hj_iff p q hq) hneg
      linarith

/-! ## FL3: Hole facts -/

/-- **FL3 (`w_C` hole fact):** on a `HoleLeaf`, no `cc` in the `wcCell_eventually` window can have
strict line separation at `capView x 1 0 cc` on rim `[0, 5, 2, 3, 6]` edge `4` (`6 → 0`). -/
theorem holeLeaf_not_wc {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F)
    (cc : ℝ) (hw5 : 1 / omega5 x < cc) (hw3 : cc < omega3 x)
    (h368_pos : ∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
      0 < ⟪F.N t, x 6 - x 1⟫ → -⟪F.N t, x 0 - x 1⟫ / ⟪F.N t, x 6 - x 1⟫ < cc)
    (h368_neg : ∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
      ⟪F.N t, x 6 - x 1⟫ < 0 → cc < -⟪F.N t, x 0 - x 1⟫ / ⟪F.N t, x 6 - x 1⟫)
    (h368_zero : ∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
      ⟪F.N t, x 6 - x 1⟫ = 0 → 0 < ⟪F.N t, x 0 - x 1⟫)
    (hD0 : ⟪x (wcRim (4 + 1)) - x (wcRim 4), capView x 1 0 cc⟫ ≠ 0)
    (hc_ne0 : ∀ i : ZMod 5, i ≠ 4 →
      Split.det3 (x (wcRim (i + 1)) - x (wcRim i))
        (x (wcRim (4 + 1)) - x (wcRim 4)) (capView x 1 0 cc) ≠ 0)
    (sh : ℝ) (hsh : sh = 1 ∨ sh = -1) (α' μ' : ℝ)
    (hBlue0 : ∀ i j : ZMod 5, i ≠ 4 → (j = i ∨ j = i + 1) →
      0 < Split.det3 (x (wcRim (i + 1)) - x (wcRim i))
          (x (wcRim (4 + 1)) - x (wcRim 4)) (capView x 1 0 cc) →
      (-sh * ⟪Split.Slope.linSpinVec (fun t => x (wcRim t)) 4 i j, capView x 1 0 cc⟫ /
          Split.det3 (x (wcRim (i + 1)) - x (wcRim i))
            (x (wcRim (4 + 1)) - x (wcRim 4)) (capView x 1 0 cc)) -
        μ' * ⟪x (wcRim j) - x (wcRim 4), capView x 1 0 cc⟫ < α')
    (hOrange0 : ∀ p q : ZMod 5, p ≠ 4 → (q = p ∨ q = p + 1) →
      Split.det3 (x (wcRim (p + 1)) - x (wcRim p))
          (x (wcRim (4 + 1)) - x (wcRim 4)) (capView x 1 0 cc) < 0 →
      α' < (-sh * ⟪Split.Slope.linSpinVec (fun t => x (wcRim t)) 4 p q, capView x 1 0 cc⟫ /
          Split.det3 (x (wcRim (p + 1)) - x (wcRim p))
            (x (wcRim (4 + 1)) - x (wcRim 4)) (capView x 1 0 cc)) -
        μ' * ⟪x (wcRim q) - x (wcRim 4), capView x 1 0 cc⟫) :
    False :=
  Atlas.holeLeaf_not_edgePlaneAny hF
    (wc_edgePlaneAny F hF.1 cc hw5 hw3 h368_pos h368_neg h368_zero
      hD0 hc_ne0 sh hsh α' μ' hBlue0 hOrange0)

/-- **FL3 (`Hole24` `w_C` form).** -/
theorem hole24_not_wc {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : Hole24 x F)
    (cc : ℝ) (hw5 : 1 / omega5 x < cc) (hw3 : cc < omega3 x)
    (h368_pos : ∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
      0 < ⟪F.N t, x 6 - x 1⟫ → -⟪F.N t, x 0 - x 1⟫ / ⟪F.N t, x 6 - x 1⟫ < cc)
    (h368_neg : ∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
      ⟪F.N t, x 6 - x 1⟫ < 0 → cc < -⟪F.N t, x 0 - x 1⟫ / ⟪F.N t, x 6 - x 1⟫)
    (h368_zero : ∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
      ⟪F.N t, x 6 - x 1⟫ = 0 → 0 < ⟪F.N t, x 0 - x 1⟫)
    (hD0 : ⟪x (wcRim (4 + 1)) - x (wcRim 4), capView x 1 0 cc⟫ ≠ 0)
    (hc_ne0 : ∀ i : ZMod 5, i ≠ 4 →
      Split.det3 (x (wcRim (i + 1)) - x (wcRim i))
        (x (wcRim (4 + 1)) - x (wcRim 4)) (capView x 1 0 cc) ≠ 0)
    (sh : ℝ) (hsh : sh = 1 ∨ sh = -1) (α' μ' : ℝ)
    (hBlue0 : ∀ i j : ZMod 5, i ≠ 4 → (j = i ∨ j = i + 1) →
      0 < Split.det3 (x (wcRim (i + 1)) - x (wcRim i))
          (x (wcRim (4 + 1)) - x (wcRim 4)) (capView x 1 0 cc) →
      (-sh * ⟪Split.Slope.linSpinVec (fun t => x (wcRim t)) 4 i j, capView x 1 0 cc⟫ /
          Split.det3 (x (wcRim (i + 1)) - x (wcRim i))
            (x (wcRim (4 + 1)) - x (wcRim 4)) (capView x 1 0 cc)) -
        μ' * ⟪x (wcRim j) - x (wcRim 4), capView x 1 0 cc⟫ < α')
    (hOrange0 : ∀ p q : ZMod 5, p ≠ 4 → (q = p ∨ q = p + 1) →
      Split.det3 (x (wcRim (p + 1)) - x (wcRim p))
          (x (wcRim (4 + 1)) - x (wcRim 4)) (capView x 1 0 cc) < 0 →
      α' < (-sh * ⟪Split.Slope.linSpinVec (fun t => x (wcRim t)) 4 p q, capView x 1 0 cc⟫ /
          Split.det3 (x (wcRim (p + 1)) - x (wcRim p))
            (x (wcRim (4 + 1)) - x (wcRim 4)) (capView x 1 0 cc)) -
        μ' * ⟪x (wcRim q) - x (wcRim 4), capView x 1 0 cc⟫) :
    False :=
  holeLeaf_not_wc hF.1 cc hw5 hw3 h368_pos h368_neg h368_zero hD0 hc_ne0 sh hsh α' μ' hBlue0 hOrange0

/-- **FL3 (`T_0` family hole fact):** on a `HoleLeaf`, for every `x0` in `I5`, eventually in
`δ → 0+` there is no base `EdgePlaneAt` at `uF x x0 δ`. -/
theorem holeLeaf_not_T0_family {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F)
    {x0 : ℝ} (hI : InI5 x x0) :
    ∀ᶠ δ : ℝ in 𝓝[>] 0, ¬ EdgePlaneAt (x ∘ (0 : Fin 7).succAbove) (uF x x0 δ) := by
  by_contra h
  simp only [Filter.not_eventually, not_not] at h
  exact Atlas.holeLeaf_not_edgePlaneAny hF (edgePlaneAny_of_T0_family F hF.1 hI h)

/-! ## FM1: `π_24` twin of the `w_C` leaf -/

/-- `Gen.EdgePlaneAny` is preserved under the `Sym.pi24` vertex permutation. -/
theorem edgePlaneAny_of_comp_pi24 (x : Fin 7 → ℝ³)
    (h : Gen.EdgePlaneAny (x ∘ Sym.pi24)) : Gen.EdgePlaneAny x := by
  rcases h with ⟨k, hne, lab, w, a, s, α, μ, hk, hinj, hrim, hhid, hDw, hrows⟩
  let lab' : ZMod k → Fin 7 := fun i => Sym.pi24 (lab i)
  have hinj' : Function.Injective lab' := Sym.pi24.injective.comp hinj
  have hrim' : Split.StrictRimN x w lab' := by
    intro m i hm1 hm2
    let m' : Fin 7 := Sym.pi24.symm m
    have hm' : Sym.pi24 m' = m := Sym.pi24.apply_symm_apply m
    have h1 : m' ≠ lab i := fun h => hm1 (by rw [← hm']; exact congrArg Sym.pi24 h)
    have h2 : m' ≠ lab (i + 1) := fun h => hm2 (by rw [← hm']; exact congrArg Sym.pi24 h)
    simpa only [Function.comp_apply, hm', lab'] using hrim m' i h1 h2
  have hhid' : Split.HiddenInTriangles x w lab' := by
    have himg : univ.image (x ∘ Sym.pi24) = univ.image x := by
      ext y
      simp only [mem_image, mem_univ, true_and, Function.comp_apply]
      exact ⟨fun ⟨i, hi⟩ => ⟨Sym.pi24 i, hi⟩,
        fun ⟨i, hi⟩ => ⟨Sym.pi24.symm i, by simpa using hi⟩⟩
    intro m hm
    let m' : Fin 7 := Sym.pi24.symm m
    have hm' : Sym.pi24 m' = m := Sym.pi24.apply_symm_apply m
    have hmi : ∀ i, m' ≠ lab i := fun i h => hm i (by rw [← hm']; exact congrArg Sym.pi24 h)
    obtain ⟨p, hp, q, hq, r, hr, t1, t2, t3, t4⟩ := hhid m' hmi
    rw [himg] at hp hq hr
    simp only [Function.comp_apply, hm'] at t2 t3 t4
    exact ⟨p, hp, q, hq, r, hr, t1, t2, t3, t4⟩
  exact ⟨k, hne, lab', w, a, s, α, μ, hk, hinj', hrim', hhid', hDw, hrows⟩

/-- **FM1 (`w_C` twin leaf):** `π_24` image of `wc_edgePlaneAny` (view `capView (x ∘ Sym.pi24) 1 η cb`,
rim `wcTwinRim = ![0, 4, 6, 3, 2]`, edge `2 → 0`). -/
theorem wc_edgePlaneAny_twin {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (cb : ℝ)
    (hw5 : 1 / omega5 (x ∘ Sym.pi24) < cb) (hw3 : cb < omega3 (x ∘ Sym.pi24))
    (h368_pos : ∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
      0 < ⟪(Sym.sym24 F).N t, (x ∘ Sym.pi24) 6 - (x ∘ Sym.pi24) 1⟫ →
      -⟪(Sym.sym24 F).N t, (x ∘ Sym.pi24) 0 - (x ∘ Sym.pi24) 1⟫ /
        ⟪(Sym.sym24 F).N t, (x ∘ Sym.pi24) 6 - (x ∘ Sym.pi24) 1⟫ < cb)
    (h368_neg : ∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
      ⟪(Sym.sym24 F).N t, (x ∘ Sym.pi24) 6 - (x ∘ Sym.pi24) 1⟫ < 0 →
      cb < -⟪(Sym.sym24 F).N t, (x ∘ Sym.pi24) 0 - (x ∘ Sym.pi24) 1⟫ /
        ⟪(Sym.sym24 F).N t, (x ∘ Sym.pi24) 6 - (x ∘ Sym.pi24) 1⟫)
    (h368_zero : ∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
      ⟪(Sym.sym24 F).N t, (x ∘ Sym.pi24) 6 - (x ∘ Sym.pi24) 1⟫ = 0 →
      0 < ⟪(Sym.sym24 F).N t, (x ∘ Sym.pi24) 0 - (x ∘ Sym.pi24) 1⟫)
    (hD0 : ⟪(x ∘ Sym.pi24) (wcRim (4 + 1)) - (x ∘ Sym.pi24) (wcRim 4),
      capView (x ∘ Sym.pi24) 1 0 cb⟫ ≠ 0)
    (hc_ne0 : ∀ i : ZMod 5, i ≠ 4 →
      Split.det3 ((x ∘ Sym.pi24) (wcRim (i + 1)) - (x ∘ Sym.pi24) (wcRim i))
        ((x ∘ Sym.pi24) (wcRim (4 + 1)) - (x ∘ Sym.pi24) (wcRim 4))
        (capView (x ∘ Sym.pi24) 1 0 cb) ≠ 0)
    (sh : ℝ) (hsh : sh = 1 ∨ sh = -1) (α' μ' : ℝ)
    (hBlue0 : ∀ i j : ZMod 5, i ≠ 4 → (j = i ∨ j = i + 1) →
      0 < Split.det3 ((x ∘ Sym.pi24) (wcRim (i + 1)) - (x ∘ Sym.pi24) (wcRim i))
          ((x ∘ Sym.pi24) (wcRim (4 + 1)) - (x ∘ Sym.pi24) (wcRim 4))
          (capView (x ∘ Sym.pi24) 1 0 cb) →
      (-sh * ⟪Split.Slope.linSpinVec (fun t => (x ∘ Sym.pi24) (wcRim t)) 4 i j,
            capView (x ∘ Sym.pi24) 1 0 cb⟫ /
          Split.det3 ((x ∘ Sym.pi24) (wcRim (i + 1)) - (x ∘ Sym.pi24) (wcRim i))
            ((x ∘ Sym.pi24) (wcRim (4 + 1)) - (x ∘ Sym.pi24) (wcRim 4))
            (capView (x ∘ Sym.pi24) 1 0 cb)) -
        μ' * ⟪(x ∘ Sym.pi24) (wcRim j) - (x ∘ Sym.pi24) (wcRim 4),
          capView (x ∘ Sym.pi24) 1 0 cb⟫ < α')
    (hOrange0 : ∀ p q : ZMod 5, p ≠ 4 → (q = p ∨ q = p + 1) →
      Split.det3 ((x ∘ Sym.pi24) (wcRim (p + 1)) - (x ∘ Sym.pi24) (wcRim p))
          ((x ∘ Sym.pi24) (wcRim (4 + 1)) - (x ∘ Sym.pi24) (wcRim 4))
          (capView (x ∘ Sym.pi24) 1 0 cb) < 0 →
      α' < (-sh * ⟪Split.Slope.linSpinVec (fun t => (x ∘ Sym.pi24) (wcRim t)) 4 p q,
            capView (x ∘ Sym.pi24) 1 0 cb⟫ /
          Split.det3 ((x ∘ Sym.pi24) (wcRim (p + 1)) - (x ∘ Sym.pi24) (wcRim p))
            ((x ∘ Sym.pi24) (wcRim (4 + 1)) - (x ∘ Sym.pi24) (wcRim 4))
            (capView (x ∘ Sym.pi24) 1 0 cb)) -
        μ' * ⟪(x ∘ Sym.pi24) (wcRim q) - (x ∘ Sym.pi24) (wcRim 4),
          capView (x ∘ Sym.pi24) 1 0 cb⟫) :
    Gen.EdgePlaneAny x :=
  edgePlaneAny_of_comp_pi24 x
    (wc_edgePlaneAny (Sym.sym24 F) ((Sym.cbarIn_comp_pi24 x).2 hC) cb
      hw5 hw3 h368_pos h368_neg h368_zero hD0 hc_ne0 sh hsh α' μ' hBlue0 hOrange0)

/-- **FM1 (`HoleLeaf` `w_C` twin hole fact).** -/
theorem holeLeaf_not_wc_twin {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F)
    (cb : ℝ) (hw5 : 1 / omega5 (x ∘ Sym.pi24) < cb) (hw3 : cb < omega3 (x ∘ Sym.pi24))
    (h368_pos : ∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
      0 < ⟪(Sym.sym24 F).N t, (x ∘ Sym.pi24) 6 - (x ∘ Sym.pi24) 1⟫ →
      -⟪(Sym.sym24 F).N t, (x ∘ Sym.pi24) 0 - (x ∘ Sym.pi24) 1⟫ /
        ⟪(Sym.sym24 F).N t, (x ∘ Sym.pi24) 6 - (x ∘ Sym.pi24) 1⟫ < cb)
    (h368_neg : ∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
      ⟪(Sym.sym24 F).N t, (x ∘ Sym.pi24) 6 - (x ∘ Sym.pi24) 1⟫ < 0 →
      cb < -⟪(Sym.sym24 F).N t, (x ∘ Sym.pi24) 0 - (x ∘ Sym.pi24) 1⟫ /
        ⟪(Sym.sym24 F).N t, (x ∘ Sym.pi24) 6 - (x ∘ Sym.pi24) 1⟫)
    (h368_zero : ∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
      ⟪(Sym.sym24 F).N t, (x ∘ Sym.pi24) 6 - (x ∘ Sym.pi24) 1⟫ = 0 →
      0 < ⟪(Sym.sym24 F).N t, (x ∘ Sym.pi24) 0 - (x ∘ Sym.pi24) 1⟫)
    (hD0 : ⟪(x ∘ Sym.pi24) (wcRim (4 + 1)) - (x ∘ Sym.pi24) (wcRim 4),
      capView (x ∘ Sym.pi24) 1 0 cb⟫ ≠ 0)
    (hc_ne0 : ∀ i : ZMod 5, i ≠ 4 →
      Split.det3 ((x ∘ Sym.pi24) (wcRim (i + 1)) - (x ∘ Sym.pi24) (wcRim i))
        ((x ∘ Sym.pi24) (wcRim (4 + 1)) - (x ∘ Sym.pi24) (wcRim 4))
        (capView (x ∘ Sym.pi24) 1 0 cb) ≠ 0)
    (sh : ℝ) (hsh : sh = 1 ∨ sh = -1) (α' μ' : ℝ)
    (hBlue0 : ∀ i j : ZMod 5, i ≠ 4 → (j = i ∨ j = i + 1) →
      0 < Split.det3 ((x ∘ Sym.pi24) (wcRim (i + 1)) - (x ∘ Sym.pi24) (wcRim i))
          ((x ∘ Sym.pi24) (wcRim (4 + 1)) - (x ∘ Sym.pi24) (wcRim 4))
          (capView (x ∘ Sym.pi24) 1 0 cb) →
      (-sh * ⟪Split.Slope.linSpinVec (fun t => (x ∘ Sym.pi24) (wcRim t)) 4 i j,
            capView (x ∘ Sym.pi24) 1 0 cb⟫ /
          Split.det3 ((x ∘ Sym.pi24) (wcRim (i + 1)) - (x ∘ Sym.pi24) (wcRim i))
            ((x ∘ Sym.pi24) (wcRim (4 + 1)) - (x ∘ Sym.pi24) (wcRim 4))
            (capView (x ∘ Sym.pi24) 1 0 cb)) -
        μ' * ⟪(x ∘ Sym.pi24) (wcRim j) - (x ∘ Sym.pi24) (wcRim 4),
          capView (x ∘ Sym.pi24) 1 0 cb⟫ < α')
    (hOrange0 : ∀ p q : ZMod 5, p ≠ 4 → (q = p ∨ q = p + 1) →
      Split.det3 ((x ∘ Sym.pi24) (wcRim (p + 1)) - (x ∘ Sym.pi24) (wcRim p))
          ((x ∘ Sym.pi24) (wcRim (4 + 1)) - (x ∘ Sym.pi24) (wcRim 4))
          (capView (x ∘ Sym.pi24) 1 0 cb) < 0 →
      α' < (-sh * ⟪Split.Slope.linSpinVec (fun t => (x ∘ Sym.pi24) (wcRim t)) 4 p q,
            capView (x ∘ Sym.pi24) 1 0 cb⟫ /
          Split.det3 ((x ∘ Sym.pi24) (wcRim (p + 1)) - (x ∘ Sym.pi24) (wcRim p))
            ((x ∘ Sym.pi24) (wcRim (4 + 1)) - (x ∘ Sym.pi24) (wcRim 4))
            (capView (x ∘ Sym.pi24) 1 0 cb)) -
        μ' * ⟪(x ∘ Sym.pi24) (wcRim q) - (x ∘ Sym.pi24) (wcRim 4),
          capView (x ∘ Sym.pi24) 1 0 cb⟫) :
    False :=
  Atlas.holeLeaf_not_edgePlaneAny hF
    (wc_edgePlaneAny_twin F hF.1 cb hw5 hw3 h368_pos h368_neg h368_zero
      hD0 hc_ne0 sh hsh α' μ' hBlue0 hOrange0)

/-- **FM1 (`Hole24` `w_C` twin hole fact).** -/
theorem hole24_not_wc_twin {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : Hole24 x F)
    (cb : ℝ) (hw5 : 1 / omega5 (x ∘ Sym.pi24) < cb) (hw3 : cb < omega3 (x ∘ Sym.pi24))
    (h368_pos : ∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
      0 < ⟪(Sym.sym24 F).N t, (x ∘ Sym.pi24) 6 - (x ∘ Sym.pi24) 1⟫ →
      -⟪(Sym.sym24 F).N t, (x ∘ Sym.pi24) 0 - (x ∘ Sym.pi24) 1⟫ /
        ⟪(Sym.sym24 F).N t, (x ∘ Sym.pi24) 6 - (x ∘ Sym.pi24) 1⟫ < cb)
    (h368_neg : ∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
      ⟪(Sym.sym24 F).N t, (x ∘ Sym.pi24) 6 - (x ∘ Sym.pi24) 1⟫ < 0 →
      cb < -⟪(Sym.sym24 F).N t, (x ∘ Sym.pi24) 0 - (x ∘ Sym.pi24) 1⟫ /
        ⟪(Sym.sym24 F).N t, (x ∘ Sym.pi24) 6 - (x ∘ Sym.pi24) 1⟫)
    (h368_zero : ∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
      ⟪(Sym.sym24 F).N t, (x ∘ Sym.pi24) 6 - (x ∘ Sym.pi24) 1⟫ = 0 →
      0 < ⟪(Sym.sym24 F).N t, (x ∘ Sym.pi24) 0 - (x ∘ Sym.pi24) 1⟫)
    (hD0 : ⟪(x ∘ Sym.pi24) (wcRim (4 + 1)) - (x ∘ Sym.pi24) (wcRim 4),
      capView (x ∘ Sym.pi24) 1 0 cb⟫ ≠ 0)
    (hc_ne0 : ∀ i : ZMod 5, i ≠ 4 →
      Split.det3 ((x ∘ Sym.pi24) (wcRim (i + 1)) - (x ∘ Sym.pi24) (wcRim i))
        ((x ∘ Sym.pi24) (wcRim (4 + 1)) - (x ∘ Sym.pi24) (wcRim 4))
        (capView (x ∘ Sym.pi24) 1 0 cb) ≠ 0)
    (sh : ℝ) (hsh : sh = 1 ∨ sh = -1) (α' μ' : ℝ)
    (hBlue0 : ∀ i j : ZMod 5, i ≠ 4 → (j = i ∨ j = i + 1) →
      0 < Split.det3 ((x ∘ Sym.pi24) (wcRim (i + 1)) - (x ∘ Sym.pi24) (wcRim i))
          ((x ∘ Sym.pi24) (wcRim (4 + 1)) - (x ∘ Sym.pi24) (wcRim 4))
          (capView (x ∘ Sym.pi24) 1 0 cb) →
      (-sh * ⟪Split.Slope.linSpinVec (fun t => (x ∘ Sym.pi24) (wcRim t)) 4 i j,
            capView (x ∘ Sym.pi24) 1 0 cb⟫ /
          Split.det3 ((x ∘ Sym.pi24) (wcRim (i + 1)) - (x ∘ Sym.pi24) (wcRim i))
            ((x ∘ Sym.pi24) (wcRim (4 + 1)) - (x ∘ Sym.pi24) (wcRim 4))
            (capView (x ∘ Sym.pi24) 1 0 cb)) -
        μ' * ⟪(x ∘ Sym.pi24) (wcRim j) - (x ∘ Sym.pi24) (wcRim 4),
          capView (x ∘ Sym.pi24) 1 0 cb⟫ < α')
    (hOrange0 : ∀ p q : ZMod 5, p ≠ 4 → (q = p ∨ q = p + 1) →
      Split.det3 ((x ∘ Sym.pi24) (wcRim (p + 1)) - (x ∘ Sym.pi24) (wcRim p))
          ((x ∘ Sym.pi24) (wcRim (4 + 1)) - (x ∘ Sym.pi24) (wcRim 4))
          (capView (x ∘ Sym.pi24) 1 0 cb) < 0 →
      α' < (-sh * ⟪Split.Slope.linSpinVec (fun t => (x ∘ Sym.pi24) (wcRim t)) 4 p q,
            capView (x ∘ Sym.pi24) 1 0 cb⟫ /
          Split.det3 ((x ∘ Sym.pi24) (wcRim (p + 1)) - (x ∘ Sym.pi24) (wcRim p))
            ((x ∘ Sym.pi24) (wcRim (4 + 1)) - (x ∘ Sym.pi24) (wcRim 4))
            (capView (x ∘ Sym.pi24) 1 0 cb)) -
        μ' * ⟪(x ∘ Sym.pi24) (wcRim q) - (x ∘ Sym.pi24) (wcRim 4),
          capView (x ∘ Sym.pi24) 1 0 cb⟫) :
    False :=
  holeLeaf_not_wc_twin hF.1 cb hw5 hw3 h368_pos h368_neg h368_zero hD0 hc_ne0 sh hsh α' μ' hBlue0 hOrange0

/-! ## FM2: Packaged two-cone residue -/

/-- The `w_C` window and strict line-separation hypothesis at `w0 = capView x 1 0 cc`. -/
def WCCertAt (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) (cc : ℝ) : Prop :=
  1 / omega5 x < cc ∧ cc < omega3 x ∧
  (∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
    0 < ⟪F.N t, x 6 - x 1⟫ → -⟪F.N t, x 0 - x 1⟫ / ⟪F.N t, x 6 - x 1⟫ < cc) ∧
  (∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
    ⟪F.N t, x 6 - x 1⟫ < 0 → cc < -⟪F.N t, x 0 - x 1⟫ / ⟪F.N t, x 6 - x 1⟫) ∧
  (∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
    ⟪F.N t, x 6 - x 1⟫ = 0 → 0 < ⟪F.N t, x 0 - x 1⟫) ∧
  ⟪x (wcRim (4 + 1)) - x (wcRim 4), capView x 1 0 cc⟫ ≠ 0 ∧
  (∀ i : ZMod 5, i ≠ 4 →
    Split.det3 (x (wcRim (i + 1)) - x (wcRim i))
      (x (wcRim (4 + 1)) - x (wcRim 4)) (capView x 1 0 cc) ≠ 0) ∧
  ∃ sh α' μ' : ℝ, (sh = 1 ∨ sh = -1) ∧
    (∀ i j : ZMod 5, i ≠ 4 → (j = i ∨ j = i + 1) →
      0 < Split.det3 (x (wcRim (i + 1)) - x (wcRim i))
          (x (wcRim (4 + 1)) - x (wcRim 4)) (capView x 1 0 cc) →
      (-sh * ⟪Split.Slope.linSpinVec (fun t => x (wcRim t)) 4 i j, capView x 1 0 cc⟫ /
          Split.det3 (x (wcRim (i + 1)) - x (wcRim i))
            (x (wcRim (4 + 1)) - x (wcRim 4)) (capView x 1 0 cc)) -
        μ' * ⟪x (wcRim j) - x (wcRim 4), capView x 1 0 cc⟫ < α') ∧
    (∀ p q : ZMod 5, p ≠ 4 → (q = p ∨ q = p + 1) →
      Split.det3 (x (wcRim (p + 1)) - x (wcRim p))
          (x (wcRim (4 + 1)) - x (wcRim 4)) (capView x 1 0 cc) < 0 →
      α' < (-sh * ⟪Split.Slope.linSpinVec (fun t => x (wcRim t)) 4 p q, capView x 1 0 cc⟫ /
          Split.det3 (x (wcRim (p + 1)) - x (wcRim p))
            (x (wcRim (4 + 1)) - x (wcRim 4)) (capView x 1 0 cc)) -
        μ' * ⟪x (wcRim q) - x (wcRim 4), capView x 1 0 cc⟫)

/-- **FM2 (`TwoConeResidue`):** packaged two-cone residue for `Hole24 x F`. -/
def TwoConeResidue (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  CbarIn x ∧
  (∀ x0 : ℝ, InI5 x x0 → ¬ SplitFamily F x0) ∧
  (∀ x0 : ℝ, InI5 (x ∘ Sym.pi24) x0 → ¬ SplitFamilyTwin F x0) ∧
  (∀ cc : ℝ, ¬ WCCertAt x F cc) ∧
  (∀ cb : ℝ, ¬ WCCertAt (x ∘ Sym.pi24) (Sym.sym24 F) cb) ∧
  (∀ x0 : ℝ, InI5 x x0 → ∀ᶠ δ : ℝ in 𝓝[>] 0, ¬ EdgePlaneAt (x ∘ (0 : Fin 7).succAbove) (uF x x0 δ))

/-- **FM2 (`hole24_twoConeResidue`):** `Hole24 x F` implies `TwoConeResidue x F`. -/
theorem hole24_twoConeResidue {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : Hole24 x F) :
    TwoConeResidue x F := by
  refine ⟨hF.1.1,
    fun x0 hI => holeLeaf_not_splitFamily F hF.1 hI,
    fun x0 hI => holeLeaf_not_splitFamilyTwin F hF.1 hI,
    fun cc hcc => ?_,
    fun cb hcb => ?_,
    fun x0 hI => holeLeaf_not_T0_family hF.1 hI⟩
  · rcases hcc with ⟨hw5, hw3, h368p, h368n, h368z, hD0, hcn, sh, α', μ', hsh, hB, hO⟩
    exact hole24_not_wc hF cc hw5 hw3 h368p h368n h368z hD0 hcn sh hsh α' μ' hB hO
  · rcases hcb with ⟨hw5, hw3, h368p, h368n, h368z, hD0, hcn, sh, α', μ', hsh, hB, hO⟩
    exact hole24_not_wc_twin hF cb hw5 hw3 h368p h368n h368z hD0 hcn sh hsh α' μ' hB hO

end Minimality.T24.TwoCone
