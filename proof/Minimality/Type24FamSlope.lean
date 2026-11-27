module

public import Minimality.Type24TwoCone

/-!
# `T_0`-family leaf in line-separation form (`FP1`–`FP2`)

* `FP1` (`fam_edgePlaneAny_core`, `famA_edgePlaneAny`, `famB_edgePlaneAny`):
  for `CbarIn x`, `InI5 x x0`, rim `cA = ![1, 2, 5, 3, 6]` (`patA`, plus `hhid4` for vertex `4`)
  or `cB = ![1, 2, 5, 3, 4, 6]` (`patB`), facet signs `h6, h8` at `uB x x0`, `hD0` and `hc_ne0` at
  `uB x x0` for any edge `a`, and strict line separation at `uB x x0` (`hBlue0`, `hOrange0`),
  `Gen.EdgePlaneAny x` holds.
* `FP2` (`holeLeaf_not_famA`, `hole24_not_famA`, `holeLeaf_not_famB`, `hole24_not_famB`,
  `FamACertAt`, `FamBCertAt`, `TwoConeResidue'`, `hole24_twoConeResidue'`):
  hole facts and extended `TwoConeResidue'`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace Topology
open Finset Filter
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.M4
open Minimality.T24.HC Minimality.T24.SF Minimality.T24.DeepC

namespace Minimality.T24.TwoCone

/-- `Fin 6` rim corresponding to `cA = ![1, 2, 5, 3, 6]` under `(0 : Fin 7).succAbove`. -/
def cA' : ZMod 5 → Fin 6 := ![0, 1, 4, 2, 5]

/-- `Fin 6` rim corresponding to `cB = ![1, 2, 5, 3, 4, 6]` under `(0 : Fin 7).succAbove`. -/
def cB' : ZMod 6 → Fin 6 := ![0, 1, 4, 2, 3, 5]

theorem succAbove_cA' : ∀ i : ZMod 5, (0 : Fin 7).succAbove (cA' i) = cA i := by
  intro i; fin_cases i <;> rfl

theorem succAbove_cB' : ∀ i : ZMod 6, (0 : Fin 7).succAbove (cB' i) = cB i := by
  intro i; fin_cases i <;> rfl

theorem cA'_inj : Function.Injective cA' := by
  intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)

theorem cB'_inj : Function.Injective cB' := by
  intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)

private theorem pat_cycUD {k : ℕ} [NeZero k] {c : ZMod k → Fin 7} {pat : Fin 9 → Bool}
    (hcyc : S0xCycOK s0x_S24 c pat) :
    S0xCycUD s0x_S24 c (Finset.univ.filter fun t => pat t = true)
      (Finset.univ.filter fun t => pat t = false) := by
  intro i
  obtain ⟨a, b, ha, hb, h⟩ := hcyc i
  exact ⟨a, by simpa using ha, b, by simpa using hb, h⟩

private theorem uF_cell_eventually {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    {x0 : ℝ} (_hI : InI5 x x0) {pat : Fin 9 → Bool} (hp2 : pat 2 = false)
    (hfac : ∀ t : Fin 9, t ≠ 2 →
      (pat t = true → 0 < ⟪F.N t, uB x x0⟫) ∧ (pat t = false → ⟪F.N t, uB x x0⟫ < 0)) :
    ∀ᶠ δ : ℝ in 𝓝[>] 0,
      CellAt F (Finset.univ.filter fun t => pat t = true)
        (Finset.univ.filter fun t => pat t = false) (uF x x0 δ) := by
  have hev_up : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      ∀ t ∈ Finset.univ.filter (fun t : Fin 9 => pat t = true), 0 < ⟪F.N t, uF x x0 δ⟫ := by
    rw [eventually_all]; intro t
    by_cases hpt : pat t = true
    · have ht2 : t ≠ 2 := by intro h; subst h; simp [hp2] at hpt
      have hcont : Continuous (fun δ : ℝ => ⟪F.N t, uF x x0 δ⟫) := by unfold uF capView; fun_prop
      have h0 : 0 < ⟪F.N t, uF x x0 0⟫ := by rw [uF_zero]; exact (hfac t ht2).1 hpt
      exact (ev_pos hcont h0).mono fun δ hδ _ => hδ
    · exact Filter.Eventually.of_forall fun δ ht => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
        exact absurd ht hpt
  have hev_dn : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      ∀ t ∈ Finset.univ.filter (fun t : Fin 9 => pat t = false), ⟪F.N t, uF x x0 δ⟫ < 0 := by
    rw [eventually_all]; intro t
    by_cases hpf : pat t = false
    · by_cases ht2 : t = 2
      · subst ht2
        have hP := F.neg 2 1 (by decide)
        filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ) _
        rw [uF, facet2_eq F hC]
        exact mul_neg_of_pos_of_neg hδ hP
      · have hcont : Continuous (fun δ : ℝ => -⟪F.N t, uF x x0 δ⟫) := by unfold uF capView; fun_prop
        have h0 : 0 < -⟪F.N t, uF x x0 0⟫ := by rw [uF_zero]; exact neg_pos.mpr ((hfac t ht2).2 hpf)
        exact (ev_pos hcont h0).mono fun δ hδ _ => neg_pos.mp hδ
    · exact Filter.Eventually.of_forall fun δ ht => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
        exact absurd ht hpf
  filter_upwards [hev_up, hev_dn] with δ hu hd
  exact ⟨hu, hd⟩

/-- **FP1 (core):** for any `k ≥ 3` rim `c` with `Fin 6` counterpart `c'` (`succAbove 0 ∘ c' = c`)
and `S0xCycOK s0x_S24 c pat`, facet signs at `uB x x0`, `HiddenInTriangles` for `(x ∘ succAbove 0)`
eventually in `δ > 0`, and strict line separation at `uB x x0` on edge `a`, `Gen.EdgePlaneAny x`
holds. -/
theorem fam_edgePlaneAny_core {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    {x0 : ℝ} (hI : InI5 x x0)
    {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (c : ZMod k → Fin 7) (hc : Function.Injective c)
    (c' : ZMod k → Fin 6) (hc' : Function.Injective c')
    (hcc' : ∀ i : ZMod k, (0 : Fin 7).succAbove (c' i) = c i)
    (pat : Fin 9 → Bool) (hcyc : S0xCycOK s0x_S24 c pat) (hp2 : pat 2 = false)
    (hfac : ∀ t : Fin 9, t ≠ 2 →
      (pat t = true → 0 < ⟪F.N t, uB x x0⟫) ∧ (pat t = false → ⟪F.N t, uB x x0⟫ < 0))
    (hhid_ev : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      Split.HiddenInTriangles (x ∘ (0 : Fin 7).succAbove) (uF x x0 δ) c')
    (a : ZMod k)
    (hD0 : ⟪x (c (a + 1)) - x (c a), uB x x0⟫ ≠ 0)
    (hc_ne0 : ∀ i : ZMod k, i ≠ a →
      Split.det3 (x (c (i + 1)) - x (c i)) (x (c (a + 1)) - x (c a)) (uB x x0) ≠ 0)
    (sh : ℝ) (hsh : sh = 1 ∨ sh = -1) (α' μ' : ℝ)
    (hBlue0 : ∀ i j : ZMod k, i ≠ a → (j = i ∨ j = i + 1) →
      0 < Split.det3 (x (c (i + 1)) - x (c i)) (x (c (a + 1)) - x (c a)) (uB x x0) →
      (-sh * ⟪Split.Slope.linSpinVec (fun t => x (c t)) a i j, uB x x0⟫ /
          Split.det3 (x (c (i + 1)) - x (c i)) (x (c (a + 1)) - x (c a)) (uB x x0)) -
        μ' * ⟪x (c j) - x (c a), uB x x0⟫ < α')
    (hOrange0 : ∀ p q : ZMod k, p ≠ a → (q = p ∨ q = p + 1) →
      Split.det3 (x (c (p + 1)) - x (c p)) (x (c (a + 1)) - x (c a)) (uB x x0) < 0 →
      α' < (-sh * ⟪Split.Slope.linSpinVec (fun t => x (c t)) a p q, uB x x0⟫ /
          Split.det3 (x (c (p + 1)) - x (c p)) (x (c (a + 1)) - x (c a)) (uB x x0)) -
        μ' * ⟪x (c q) - x (c a), uB x x0⟫) :
    Gen.EdgePlaneAny x := by
  have hcell := uF_cell_eventually F hC hI hp2 hfac
  have hD_ev : ∀ᶠ δ : ℝ in 𝓝[>] 0, ⟪x (c (a + 1)) - x (c a), uF x x0 δ⟫ ≠ 0 := by
    rcases lt_or_gt_of_ne hD0 with hlt | hgt
    · have hcont : Continuous (fun δ : ℝ => -⟪x (c (a + 1)) - x (c a), uF x x0 δ⟫) := by
        unfold uF capView; fun_prop
      exact (ev_pos hcont (by rw [uF_zero]; exact neg_pos.mpr hlt)).mono fun δ h => (neg_pos.mp h).ne
    · have hcont : Continuous (fun δ : ℝ => ⟪x (c (a + 1)) - x (c a), uF x x0 δ⟫) := by
        unfold uF capView; fun_prop
      exact (ev_pos hcont (by rw [uF_zero]; exact hgt)).mono fun δ h => h.ne'
  have hc_ev : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∀ i : ZMod k, i ≠ a →
      Split.det3 (x (c (i + 1)) - x (c i)) (x (c (a + 1)) - x (c a)) (uF x x0 δ) ≠ 0 := by
    rw [eventually_all]; intro i
    by_cases hi : i = a
    · exact Filter.Eventually.of_forall fun _ h => absurd hi h
    · rcases lt_or_gt_of_ne (hc_ne0 i hi) with hlt | hgt
      · have hcont : Continuous (fun δ : ℝ =>
            -Split.det3 (x (c (i + 1)) - x (c i)) (x (c (a + 1)) - x (c a)) (uF x x0 δ)) := by
          unfold uF capView Split.det3; fun_prop
        exact (ev_pos hcont (by rw [uF_zero]; exact neg_pos.mpr hlt)).mono fun δ h _ => (neg_pos.mp h).ne
      · have hcont : Continuous (fun δ : ℝ =>
            Split.det3 (x (c (i + 1)) - x (c i)) (x (c (a + 1)) - x (c a)) (uF x x0 δ)) := by
          unfold uF capView Split.det3; fun_prop
        exact (ev_pos hcont (by rw [uF_zero]; exact hgt)).mono fun δ h _ => h.ne'
  have hBlue_ev : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∀ i j : ZMod k, i ≠ a → (j = i ∨ j = i + 1) →
      0 < Split.det3 (x (c (i + 1)) - x (c i)) (x (c (a + 1)) - x (c a)) (uF x x0 δ) →
      (-sh * ⟪Split.Slope.linSpinVec (fun t => x (c t)) a i j, uF x x0 δ⟫ /
          Split.det3 (x (c (i + 1)) - x (c i)) (x (c (a + 1)) - x (c a)) (uF x x0 δ)) -
        μ' * ⟪x (c j) - x (c a), uF x x0 δ⟫ < α' := by
    rw [eventually_all]; intro i; rw [eventually_all]; intro j
    by_cases hij : i ≠ a ∧ (j = i ∨ j = i + 1)
    · rcases lt_or_gt_of_ne (hc_ne0 i hij.1) with hc_neg | hc_pos
      · have hcont : Continuous (fun δ : ℝ =>
            -Split.det3 (x (c (i + 1)) - x (c i)) (x (c (a + 1)) - x (c a)) (uF x x0 δ)) := by
          unfold uF capView Split.det3; fun_prop
        exact (ev_pos hcont (by rw [uF_zero]; exact neg_pos.mpr hc_neg)).mono fun δ h _ _ hpos =>
          absurd hpos (not_lt.mpr (neg_pos.mp h).le)
      · have h0 := hBlue0 i j hij.1 hij.2 hc_pos
        let num : ℝ → ℝ := fun δ =>
          (α' + μ' * ⟪x (c j) - x (c a), uF x x0 δ⟫) *
            Split.det3 (x (c (i + 1)) - x (c i)) (x (c (a + 1)) - x (c a)) (uF x x0 δ) -
          (-sh * ⟪Split.Slope.linSpinVec (fun t => x (c t)) a i j, uF x x0 δ⟫)
        have hcont : Continuous num := by unfold num uF capView Split.det3; fun_prop
        have hnum0 : 0 < num 0 := by
          dsimp only [num]; rw [uF_zero]
          have h1 : -sh * ⟪Split.Slope.linSpinVec (fun t => x (c t)) a i j, uB x x0⟫ /
              Split.det3 (x (c (i + 1)) - x (c i)) (x (c (a + 1)) - x (c a)) (uB x x0) <
              α' + μ' * ⟪x (c j) - x (c a), uB x x0⟫ := by linarith
          rw [div_lt_iff₀ hc_pos] at h1
          linarith
        exact (ev_pos hcont hnum0).mono fun δ hnum _ _ hpos => by
          dsimp only [num] at hnum
          have h1 : -sh * ⟪Split.Slope.linSpinVec (fun t => x (c t)) a i j, uF x x0 δ⟫ <
              (α' + μ' * ⟪x (c j) - x (c a), uF x x0 δ⟫) *
                Split.det3 (x (c (i + 1)) - x (c i)) (x (c (a + 1)) - x (c a)) (uF x x0 δ) := by
            linarith
          rw [← div_lt_iff₀ hpos] at h1
          linarith
    · exact Filter.Eventually.of_forall fun _ hi hj => absurd ⟨hi, hj⟩ hij
  have hOrange_ev : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∀ p q : ZMod k, p ≠ a → (q = p ∨ q = p + 1) →
      Split.det3 (x (c (p + 1)) - x (c p)) (x (c (a + 1)) - x (c a)) (uF x x0 δ) < 0 →
      α' < (-sh * ⟪Split.Slope.linSpinVec (fun t => x (c t)) a p q, uF x x0 δ⟫ /
          Split.det3 (x (c (p + 1)) - x (c p)) (x (c (a + 1)) - x (c a)) (uF x x0 δ)) -
        μ' * ⟪x (c q) - x (c a), uF x x0 δ⟫ := by
    rw [eventually_all]; intro p; rw [eventually_all]; intro q
    by_cases hpq : p ≠ a ∧ (q = p ∨ q = p + 1)
    · rcases lt_or_gt_of_ne (hc_ne0 p hpq.1) with hc_neg | hc_pos
      · have h0 := hOrange0 p q hpq.1 hpq.2 hc_neg
        let num : ℝ → ℝ := fun δ =>
          (α' + μ' * ⟪x (c q) - x (c a), uF x x0 δ⟫) *
            Split.det3 (x (c (p + 1)) - x (c p)) (x (c (a + 1)) - x (c a)) (uF x x0 δ) -
          (-sh * ⟪Split.Slope.linSpinVec (fun t => x (c t)) a p q, uF x x0 δ⟫)
        have hcont : Continuous num := by unfold num uF capView Split.det3; fun_prop
        have hnum0 : 0 < num 0 := by
          dsimp only [num]; rw [uF_zero]
          have h1 : α' + μ' * ⟪x (c q) - x (c a), uB x x0⟫ <
              -sh * ⟪Split.Slope.linSpinVec (fun t => x (c t)) a p q, uB x x0⟫ /
                Split.det3 (x (c (p + 1)) - x (c p)) (x (c (a + 1)) - x (c a)) (uB x x0) := by
            linarith
          rw [lt_div_iff_of_neg hc_neg] at h1
          linarith
        exact (ev_pos hcont hnum0).mono fun δ hnum _ _ hneg => by
          dsimp only [num] at hnum
          have h1 : -sh * ⟪Split.Slope.linSpinVec (fun t => x (c t)) a p q, uF x x0 δ⟫ <
              (α' + μ' * ⟪x (c q) - x (c a), uF x x0 δ⟫) *
                Split.det3 (x (c (p + 1)) - x (c p)) (x (c (a + 1)) - x (c a)) (uF x x0 δ) := by
            linarith
          rw [← lt_div_iff_of_neg hneg] at h1
          linarith
      · have hcont : Continuous (fun δ : ℝ =>
            Split.det3 (x (c (p + 1)) - x (c p)) (x (c (a + 1)) - x (c a)) (uF x x0 δ)) := by
          unfold uF capView Split.det3; fun_prop
        exact (ev_pos hcont (by rw [uF_zero]; exact hc_pos)).mono fun δ h _ _ hneg =>
          absurd hneg (not_lt.mpr h.le)
    · exact Filter.Eventually.of_forall fun _ hp hq => absurd ⟨hp, hq⟩ hpq
  have hEP_ev : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      EdgePlaneAt (x ∘ (0 : Fin 7).succAbove) (uF x x0 δ) := by
    filter_upwards [hcell, hhid_ev, hD_ev, hc_ev, hBlue_ev, hOrange_ev] with
      δ hcell_δ hhid_δ hD_δ hc_δ hBlue_δ hOrange_δ
    let w := uF x x0 δ
    let x' : Fin 6 → ℝ³ := x ∘ (0 : Fin 7).succAbove
    have hcc'' : ∀ i : ZMod k, (c' i).succ = c i := fun i => by
      simpa [Fin.succAbove_zero] using hcc' i
    have hx'c : ∀ i : ZMod k, x' (c' i) = x (c i) := fun i => by
      dsimp [x']; rw [hcc'' i]
    rcases LexEP.strictRimN_of_openCell hk F hc (pat_cycUD hcyc) hcell_δ with hrim | hrim_rev
    · have hrim' : Split.StrictRimN x' w c' := fun m i hm0 hm1 => by
        have hm := hrim ((0 : Fin 7).succAbove m) i
          (fun h => hm0 (Fin.succAbove_right_injective (by rw [h, hcc'])))
          (fun h => hm1 (Fin.succAbove_right_injective (by rw [h, hcc'])))
        simpa [x', hcc''] using hm
      exact Split.Slope.edgePlaneAt_of_lineSep hk x' w c' hc' hrim' hhid_δ a
        (by simpa [hx'c] using hD_δ)
        (fun i hi => by simpa [hx'c] using hc_δ i hi)
        sh hsh α' μ'
        (fun i j hi hj hpos => by
          have := hBlue_δ i j hi hj (by simpa [hx'c] using hpos)
          simpa [hx'c] using this)
        (fun p q hp hq hneg => by
          have := hOrange_δ p q hp hq (by simpa [hx'c] using hneg)
          simpa [hx'c] using this)
    · let c_rev : ZMod k → Fin 6 := fun i => c' (-i)
      have hc_rev : Function.Injective c_rev := fun i j h => neg_injective (hc' h)
      have hrim' : Split.StrictRimN x' w c_rev := fun m i hm0 hm1 => by
        have hm := hrim_rev ((0 : Fin 7).succAbove m) i
          (fun h => hm0 (Fin.succAbove_right_injective (by rw [h, hcc'])))
          (fun h => hm1 (Fin.succAbove_right_injective (by rw [h, hcc'])))
        simpa [x', c_rev, hcc''] using hm
      have hhid' : Split.HiddenInTriangles x' w c_rev := fun m hm =>
        hhid_δ m fun i => by simpa [c_rev] using hm (-i)
      have hcc_rev : ∀ i : ZMod k, x' (c_rev i) = x (c (-i)) := fun i => hx'c (-i)
      let a' : ZMod k := -a - 1
      have hD' : ⟪x' (c_rev (a' + 1)) - x' (c_rev a'), w⟫ ≠ 0 := by
        have h1 : -(a' + 1) = a := by dsimp [a']; ring
        have h2 : -a' = a + 1 := by dsimp [a']; ring
        rw [hcc_rev, hcc_rev, h1, h2]
        intro h0
        apply hD_δ
        have : x (c (a + 1)) - x (c a) = -(x (c a) - x (c (a + 1))) := by abel
        rw [this, inner_neg_left, h0, neg_zero]
      have hc_eq : ∀ i : ZMod k,
          Split.det3 (x' (c_rev (i + 1)) - x' (c_rev i))
            (x' (c_rev (a' + 1)) - x' (c_rev a')) w =
          Split.det3 (x (c ((-i - 1) + 1)) - x (c (-i - 1)))
            (x (c (a + 1)) - x (c a)) w := by
        intro i
        have hc1 : x' (c_rev (i + 1)) = x (c (-i - 1)) := by
          rw [hcc_rev]; congr 2; ring
        have hc0 : x' (c_rev i) = x (c (-i - 1 + 1)) := by
          rw [hcc_rev]; congr 2; ring
        have ha1 : x' (c_rev (a' + 1)) = x (c a) := by
          rw [hcc_rev]; congr 2; dsimp [a']; ring
        have ha0 : x' (c_rev a') = x (c (a + 1)) := by
          rw [hcc_rev]; congr 2; dsimp [a']; ring
        rw [hc1, hc0, ha1, ha0]
        simp only [Split.det3, PiLp.sub_apply]; ring
      have hv_eq : ∀ i j : ZMod k,
          ⟪Split.Slope.linSpinVec (fun t => x' (c_rev t)) a' i j, w⟫ =
          ⟪Split.Slope.linSpinVec (fun t => x (c t)) a (-i - 1) (-j), w⟫ := by
        intro i j
        have hc1 : x' (c_rev (i + 1)) = x (c (-i - 1)) := by
          rw [hcc_rev]; congr 2; ring
        have hc0 : x' (c_rev i) = x (c (-i - 1 + 1)) := by
          rw [hcc_rev]; congr 2; ring
        have ha1 : x' (c_rev (a' + 1)) = x (c a) := by
          rw [hcc_rev]; congr 2; dsimp [a']; ring
        have ha0 : x' (c_rev a') = x (c (a + 1)) := by
          rw [hcc_rev]; congr 2; dsimp [a']; ring
        dsimp only [Split.Slope.linSpinVec]
        rw [hc1, hc0, ha1, ha0, hcc_rev j]
        have heq_v : (⟪x (c (-i - 1)) - x (c (-i - 1 + 1)), x (c (-j)) - x (c (a + 1))⟫ •
              (x (c a) - x (c (a + 1))) -
            ⟪x (c (-i - 1)) - x (c (-i - 1 + 1)), x (c a) - x (c (a + 1))⟫ •
              (x (c (-j)) - x (c (a + 1)))) =
          (⟪x (c (-i - 1 + 1)) - x (c (-i - 1)), x (c (-j)) - x (c a)⟫ • (x (c (a + 1)) - x (c a)) -
            ⟪x (c (-i - 1 + 1)) - x (c (-i - 1)), x (c (a + 1)) - x (c a)⟫ • (x (c (-j)) - x (c a))) := by
          have hsub : x (c (-j)) - x (c (a + 1)) = (x (c (-j)) - x (c a)) - (x (c (a + 1)) - x (c a)) := by
            abel
          have he1 : x (c (-i - 1)) - x (c (-i - 1 + 1)) = -(x (c (-i - 1 + 1)) - x (c (-i - 1))) := by abel
          have he2 : x (c a) - x (c (a + 1)) = -(x (c (a + 1)) - x (c a)) := by abel
          rw [hsub, he1, he2]
          simp only [inner_sub_right, inner_neg_left, inner_neg_right]
          module
        rw [heq_v]
      have hz_eq : ∀ j : ZMod k,
          ⟪x' (c_rev j) - x' (c_rev a'), w⟫ =
          ⟪x (c (-j)) - x (c a), w⟫ - ⟪x (c (a + 1)) - x (c a), w⟫ := by
        intro j
        have h4 : -a' = a + 1 := by dsimp [a']; ring
        rw [hcc_rev, hcc_rev, h4]
        have : x (c (-j)) - x (c (a + 1)) = (x (c (-j)) - x (c a)) - (x (c (a + 1)) - x (c a)) := by abel
        rw [this, inner_sub_left]
      have hi_iff : ∀ i : ZMod k, i ≠ a' → -i - 1 ≠ a := by
        intro i hi h
        apply hi
        have : i = -a - 1 := by linear_combination -h
        exact this
      have hj_iff : ∀ i j : ZMod k, j = i ∨ j = i + 1 → -j = -i - 1 ∨ -j = -i - 1 + 1 := by
        intro i j hj
        rcases hj with rfl | rfl
        · right; ring
        · left; ring
      refine Split.Slope.edgePlaneAt_of_lineSep hk x' w c_rev hc_rev hrim' hhid' a' hD'
        (fun i hi => by rw [hc_eq]; exact hc_δ (-i - 1) (hi_iff i hi))
        sh hsh (α' + μ' * ⟪x (c (a + 1)) - x (c a), w⟫) μ' ?_ ?_
      · intro i j hi hj hpos
        rw [hc_eq] at hpos
        rw [hc_eq, hv_eq, hz_eq]
        have h0 := hBlue_δ (-i - 1) (-j) (hi_iff i hi) (hj_iff i j hj) hpos
        linarith
      · intro p q hp hq hneg
        rw [hc_eq] at hneg
        rw [hc_eq, hv_eq, hz_eq]
        have h0 := hOrange_δ (-p - 1) (-q) (hi_iff p hp) (hj_iff p q hq) hneg
        linarith
  exact edgePlaneAny_of_T0_family F hC hI hEP_ev.frequently

/-- **FP1 (`cA = ![1, 2, 5, 3, 6]`, `patA`):** strict line separation at `uB x x0` on any edge `a`,
plus `h6 > 0`, `h8 < 0`, and `hhid4` for vertex `4` in `(1, 2, 5, 3, 6)`, yields `Gen.EdgePlaneAny x`. -/
theorem famA_edgePlaneAny {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    {x0 : ℝ} (hI : InI5 x x0)
    (h6 : 0 < ⟪F.N 6, uB x x0⟫) (h8 : ⟪F.N 8, uB x x0⟫ < 0)
    (hhid4 : ∃ p ∈ ({1, 2, 5, 3, 6} : Finset (Fin 7)).image x,
      ∃ q ∈ ({1, 2, 5, 3, 6} : Finset (Fin 7)).image x,
      ∃ r ∈ ({1, 2, 5, 3, 6} : Finset (Fin 7)).image x,
      0 < Split.det3 (q - p) (r - p) (uB x x0) ∧ 0 < Split.det3 (q - p) (x 4 - p) (uB x x0) ∧
      0 < Split.det3 (r - q) (x 4 - q) (uB x x0) ∧ 0 < Split.det3 (p - r) (x 4 - r) (uB x x0))
    (a : ZMod 5)
    (hD0 : ⟪x (cA (a + 1)) - x (cA a), uB x x0⟫ ≠ 0)
    (hc_ne0 : ∀ i : ZMod 5, i ≠ a →
      Split.det3 (x (cA (i + 1)) - x (cA i)) (x (cA (a + 1)) - x (cA a)) (uB x x0) ≠ 0)
    (sh : ℝ) (hsh : sh = 1 ∨ sh = -1) (α' μ' : ℝ)
    (hBlue0 : ∀ i j : ZMod 5, i ≠ a → (j = i ∨ j = i + 1) →
      0 < Split.det3 (x (cA (i + 1)) - x (cA i)) (x (cA (a + 1)) - x (cA a)) (uB x x0) →
      (-sh * ⟪Split.Slope.linSpinVec (fun t => x (cA t)) a i j, uB x x0⟫ /
          Split.det3 (x (cA (i + 1)) - x (cA i)) (x (cA (a + 1)) - x (cA a)) (uB x x0)) -
        μ' * ⟪x (cA j) - x (cA a), uB x x0⟫ < α')
    (hOrange0 : ∀ p q : ZMod 5, p ≠ a → (q = p ∨ q = p + 1) →
      Split.det3 (x (cA (p + 1)) - x (cA p)) (x (cA (a + 1)) - x (cA a)) (uB x x0) < 0 →
      α' < (-sh * ⟪Split.Slope.linSpinVec (fun t => x (cA t)) a p q, uB x x0⟫ /
          Split.det3 (x (cA (p + 1)) - x (cA p)) (x (cA (a + 1)) - x (cA a)) (uB x x0)) -
        μ' * ⟪x (cA q) - x (cA a), uB x x0⟫) :
    Gen.EdgePlaneAny x := by
  have hb := facets_base F hC hI
  have hfac : ∀ t : Fin 9, t ≠ 2 →
      (patA t = true → 0 < ⟪F.N t, uB x x0⟫) ∧ (patA t = false → ⟪F.N t, uB x x0⟫ < 0) := by
    intro t ht
    fin_cases t <;> simp [patA] at *
    · exact (hb 0 (by decide)).1 rfl
    · exact (hb 1 (by decide)).2.1 rfl
    · exact (hb 3 (by decide)).2.2.1 rfl
    · exact (hb 4 (by decide)).2.2.2.1 rfl
    · exact (hb 5 (by decide)).2.2.2.2.1 rfl
    · exact h6
    · exact (hb 7 (by decide)).2.2.2.2.2 rfl
    · exact h8
  obtain ⟨p, hp, q, hq, r, hr, ht1, ht2, ht3, ht4⟩ := hhid4
  have hhid_ev : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      Split.HiddenInTriangles (x ∘ (0 : Fin 7).succAbove) (uF x x0 δ) cA' := by
    have e1 := ev_pos (g := fun δ => Split.det3 (q - p) (r - p) (uF x x0 δ))
      (by unfold uF capView Split.det3; fun_prop) (by rw [uF_zero]; exact ht1)
    have e2 := ev_pos (g := fun δ => Split.det3 (q - p) (x 4 - p) (uF x x0 δ))
      (by unfold uF capView Split.det3; fun_prop) (by rw [uF_zero]; exact ht2)
    have e3 := ev_pos (g := fun δ => Split.det3 (r - q) (x 4 - q) (uF x x0 δ))
      (by unfold uF capView Split.det3; fun_prop) (by rw [uF_zero]; exact ht3)
    have e4 := ev_pos (g := fun δ => Split.det3 (p - r) (x 4 - r) (uF x x0 δ))
      (by unfold uF capView Split.det3; fun_prop) (by rw [uF_zero]; exact ht4)
    have hmem : ∀ v ∈ ({1, 2, 5, 3, 6} : Finset (Fin 7)),
        x v ∈ Finset.univ.image (x ∘ (0 : Fin 7).succAbove) := by
      intro v hv
      simp only [Finset.mem_image, Finset.mem_univ, Function.comp_apply, true_and]
      fin_cases v <;> simp at hv
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨4, rfl⟩
      · exact ⟨5, rfl⟩
    have hp' : p ∈ Finset.univ.image (x ∘ (0 : Fin 7).succAbove) := by
      rcases Finset.mem_image.mp hp with ⟨v, hv, rfl⟩; exact hmem v hv
    have hq' : q ∈ Finset.univ.image (x ∘ (0 : Fin 7).succAbove) := by
      rcases Finset.mem_image.mp hq with ⟨v, hv, rfl⟩; exact hmem v hv
    have hr' : r ∈ Finset.univ.image (x ∘ (0 : Fin 7).succAbove) := by
      rcases Finset.mem_image.mp hr with ⟨v, hv, rfl⟩; exact hmem v hv
    filter_upwards [e1, e2, e3, e4] with δ d1 d2 d3 d4 m hm
    have hm3 : m = 3 := by
      fin_cases m
      · exact absurd rfl (hm 0)
      · exact absurd rfl (hm 1)
      · exact absurd rfl (hm 3)
      · rfl
      · exact absurd rfl (hm 2)
      · exact absurd rfl (hm 4)
    subst hm3
    exact ⟨p, hp', q, hq', r, hr', d1, d2, d3, d4⟩
  exact fam_edgePlaneAny_core F hC hI (by norm_num) cA cA_inj cA' cA'_inj succAbove_cA'
    patA cA_cyc rfl hfac hhid_ev a hD0 hc_ne0 sh hsh α' μ' hBlue0 hOrange0

/-- **FP1 (`cB = ![1, 2, 5, 3, 4, 6]`, `patB`):** strict line separation at `uB x x0` on any edge `a`,
plus `h6 > 0` and `h8 > 0`, yields `Gen.EdgePlaneAny x`. -/
theorem famB_edgePlaneAny {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    {x0 : ℝ} (hI : InI5 x x0)
    (h6 : 0 < ⟪F.N 6, uB x x0⟫) (h8 : 0 < ⟪F.N 8, uB x x0⟫)
    (a : ZMod 6)
    (hD0 : ⟪x (cB (a + 1)) - x (cB a), uB x x0⟫ ≠ 0)
    (hc_ne0 : ∀ i : ZMod 6, i ≠ a →
      Split.det3 (x (cB (i + 1)) - x (cB i)) (x (cB (a + 1)) - x (cB a)) (uB x x0) ≠ 0)
    (sh : ℝ) (hsh : sh = 1 ∨ sh = -1) (α' μ' : ℝ)
    (hBlue0 : ∀ i j : ZMod 6, i ≠ a → (j = i ∨ j = i + 1) →
      0 < Split.det3 (x (cB (i + 1)) - x (cB i)) (x (cB (a + 1)) - x (cB a)) (uB x x0) →
      (-sh * ⟪Split.Slope.linSpinVec (fun t => x (cB t)) a i j, uB x x0⟫ /
          Split.det3 (x (cB (i + 1)) - x (cB i)) (x (cB (a + 1)) - x (cB a)) (uB x x0)) -
        μ' * ⟪x (cB j) - x (cB a), uB x x0⟫ < α')
    (hOrange0 : ∀ p q : ZMod 6, p ≠ a → (q = p ∨ q = p + 1) →
      Split.det3 (x (cB (p + 1)) - x (cB p)) (x (cB (a + 1)) - x (cB a)) (uB x x0) < 0 →
      α' < (-sh * ⟪Split.Slope.linSpinVec (fun t => x (cB t)) a p q, uB x x0⟫ /
          Split.det3 (x (cB (p + 1)) - x (cB p)) (x (cB (a + 1)) - x (cB a)) (uB x x0)) -
        μ' * ⟪x (cB q) - x (cB a), uB x x0⟫) :
    Gen.EdgePlaneAny x := by
  have hb := facets_base F hC hI
  have hfac : ∀ t : Fin 9, t ≠ 2 →
      (patB t = true → 0 < ⟪F.N t, uB x x0⟫) ∧ (patB t = false → ⟪F.N t, uB x x0⟫ < 0) := by
    intro t ht
    fin_cases t <;> simp [patB] at *
    · exact (hb 0 (by decide)).1 rfl
    · exact (hb 1 (by decide)).2.1 rfl
    · exact (hb 3 (by decide)).2.2.1 rfl
    · exact (hb 4 (by decide)).2.2.2.1 rfl
    · exact (hb 5 (by decide)).2.2.2.2.1 rfl
    · exact h6
    · exact (hb 7 (by decide)).2.2.2.2.2 rfl
    · exact h8
  have hhid_ev : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      Split.HiddenInTriangles (x ∘ (0 : Fin 7).succAbove) (uF x x0 δ) cB' := by
    refine Filter.Eventually.of_forall fun _ m hm => False.elim ?_
    fin_cases m
    · exact hm 0 rfl
    · exact hm 1 rfl
    · exact hm 3 rfl
    · exact hm 4 rfl
    · exact hm 2 rfl
    · exact hm 5 rfl
  exact fam_edgePlaneAny_core F hC hI (by norm_num) cB cB_inj cB' cB'_inj succAbove_cB'
    patB cB_cyc rfl hfac hhid_ev a hD0 hc_ne0 sh hsh α' μ' hBlue0 hOrange0

/-! ## FP2: Hole facts and `TwoConeResidue'` -/

/-- `FamACertAt x F x0`: `InI5 x x0`, `patA` (`h6 > 0, h8 < 0`), `hhid4` at `uB x x0`, and
strict line separation at `uB x x0` on some edge `a : ZMod 5` of `cA`. -/
def FamACertAt (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) (x0 : ℝ) : Prop :=
  InI5 x x0 ∧ 0 < ⟪F.N 6, uB x x0⟫ ∧ ⟪F.N 8, uB x x0⟫ < 0 ∧
  (∃ p ∈ ({1, 2, 5, 3, 6} : Finset (Fin 7)).image x,
    ∃ q ∈ ({1, 2, 5, 3, 6} : Finset (Fin 7)).image x,
    ∃ r ∈ ({1, 2, 5, 3, 6} : Finset (Fin 7)).image x,
    0 < Split.det3 (q - p) (r - p) (uB x x0) ∧ 0 < Split.det3 (q - p) (x 4 - p) (uB x x0) ∧
    0 < Split.det3 (r - q) (x 4 - q) (uB x x0) ∧ 0 < Split.det3 (p - r) (x 4 - r) (uB x x0)) ∧
  ∃ a : ZMod 5,
    ⟪x (cA (a + 1)) - x (cA a), uB x x0⟫ ≠ 0 ∧
    (∀ i : ZMod 5, i ≠ a →
      Split.det3 (x (cA (i + 1)) - x (cA i)) (x (cA (a + 1)) - x (cA a)) (uB x x0) ≠ 0) ∧
    ∃ sh α' μ' : ℝ, (sh = 1 ∨ sh = -1) ∧
      (∀ i j : ZMod 5, i ≠ a → (j = i ∨ j = i + 1) →
        0 < Split.det3 (x (cA (i + 1)) - x (cA i)) (x (cA (a + 1)) - x (cA a)) (uB x x0) →
        (-sh * ⟪Split.Slope.linSpinVec (fun t => x (cA t)) a i j, uB x x0⟫ /
            Split.det3 (x (cA (i + 1)) - x (cA i)) (x (cA (a + 1)) - x (cA a)) (uB x x0)) -
          μ' * ⟪x (cA j) - x (cA a), uB x x0⟫ < α') ∧
      (∀ p q : ZMod 5, p ≠ a → (q = p ∨ q = p + 1) →
        Split.det3 (x (cA (p + 1)) - x (cA p)) (x (cA (a + 1)) - x (cA a)) (uB x x0) < 0 →
        α' < (-sh * ⟪Split.Slope.linSpinVec (fun t => x (cA t)) a p q, uB x x0⟫ /
            Split.det3 (x (cA (p + 1)) - x (cA p)) (x (cA (a + 1)) - x (cA a)) (uB x x0)) -
          μ' * ⟪x (cA q) - x (cA a), uB x x0⟫)

/-- `FamBCertAt x F x0`: `InI5 x x0`, `patB` (`h6 > 0, h8 > 0`), and strict line separation at
`uB x x0` on some edge `a : ZMod 6` of `cB`. -/
def FamBCertAt (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) (x0 : ℝ) : Prop :=
  InI5 x x0 ∧ 0 < ⟪F.N 6, uB x x0⟫ ∧ 0 < ⟪F.N 8, uB x x0⟫ ∧
  ∃ a : ZMod 6,
    ⟪x (cB (a + 1)) - x (cB a), uB x x0⟫ ≠ 0 ∧
    (∀ i : ZMod 6, i ≠ a →
      Split.det3 (x (cB (i + 1)) - x (cB i)) (x (cB (a + 1)) - x (cB a)) (uB x x0) ≠ 0) ∧
    ∃ sh α' μ' : ℝ, (sh = 1 ∨ sh = -1) ∧
      (∀ i j : ZMod 6, i ≠ a → (j = i ∨ j = i + 1) →
        0 < Split.det3 (x (cB (i + 1)) - x (cB i)) (x (cB (a + 1)) - x (cB a)) (uB x x0) →
        (-sh * ⟪Split.Slope.linSpinVec (fun t => x (cB t)) a i j, uB x x0⟫ /
            Split.det3 (x (cB (i + 1)) - x (cB i)) (x (cB (a + 1)) - x (cB a)) (uB x x0)) -
          μ' * ⟪x (cB j) - x (cB a), uB x x0⟫ < α') ∧
      (∀ p q : ZMod 6, p ≠ a → (q = p ∨ q = p + 1) →
        Split.det3 (x (cB (p + 1)) - x (cB p)) (x (cB (a + 1)) - x (cB a)) (uB x x0) < 0 →
        α' < (-sh * ⟪Split.Slope.linSpinVec (fun t => x (cB t)) a p q, uB x x0⟫ /
            Split.det3 (x (cB (p + 1)) - x (cB p)) (x (cB (a + 1)) - x (cB a)) (uB x x0)) -
          μ' * ⟪x (cB q) - x (cB a), uB x x0⟫)

theorem holeLeaf_not_famA {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F)
    {x0 : ℝ} (hc : FamACertAt x F x0) : False := by
  rcases hc with ⟨hI, h6, h8, hhid4, a, hD0, hc_ne0, sh, α', μ', hsh, hB, hO⟩
  exact Atlas.holeLeaf_not_edgePlaneAny hF
    (famA_edgePlaneAny F hF.1 hI h6 h8 hhid4 a hD0 hc_ne0 sh hsh α' μ' hB hO)

theorem hole24_not_famA {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : Hole24 x F)
    {x0 : ℝ} (hc : FamACertAt x F x0) : False :=
  holeLeaf_not_famA hF.1 hc

theorem holeLeaf_not_famB {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F)
    {x0 : ℝ} (hc : FamBCertAt x F x0) : False := by
  rcases hc with ⟨hI, h6, h8, a, hD0, hc_ne0, sh, α', μ', hsh, hB, hO⟩
  exact Atlas.holeLeaf_not_edgePlaneAny hF
    (famB_edgePlaneAny F hF.1 hI h6 h8 a hD0 hc_ne0 sh hsh α' μ' hB hO)

theorem hole24_not_famB {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : Hole24 x F)
    {x0 : ℝ} (hc : FamBCertAt x F x0) : False :=
  holeLeaf_not_famB hF.1 hc

/-- Extended two-cone residue adding `¬ FamACertAt` and `¬ FamBCertAt`. -/
def TwoConeResidue' (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  TwoConeResidue x F ∧ (∀ x0 : ℝ, ¬ FamACertAt x F x0) ∧ (∀ x0 : ℝ, ¬ FamBCertAt x F x0)

theorem hole24_twoConeResidue' {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : Hole24 x F) :
    TwoConeResidue' x F :=
  ⟨hole24_twoConeResidue hF, fun _ h => hole24_not_famA hF h, fun _ h => hole24_not_famB hF h⟩

/-! ## FQ1: `π_24` twins of `famA` / `famB` and `TwoConeResidue''` -/

/-- **FQ1 (`cA` `π_24` twin leaf):** `famA_edgePlaneAny` on `(x ∘ Sym.pi24, Sym.sym24 F)`. -/
theorem famA_edgePlaneAny_twin {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    {x0 : ℝ} (hI : InI5 (x ∘ Sym.pi24) x0)
    (h6 : 0 < ⟪(Sym.sym24 F).N 6, uB (x ∘ Sym.pi24) x0⟫)
    (h8 : ⟪(Sym.sym24 F).N 8, uB (x ∘ Sym.pi24) x0⟫ < 0)
    (hhid4 : ∃ p ∈ ({1, 2, 5, 3, 6} : Finset (Fin 7)).image (x ∘ Sym.pi24),
      ∃ q ∈ ({1, 2, 5, 3, 6} : Finset (Fin 7)).image (x ∘ Sym.pi24),
      ∃ r ∈ ({1, 2, 5, 3, 6} : Finset (Fin 7)).image (x ∘ Sym.pi24),
      0 < Split.det3 (q - p) (r - p) (uB (x ∘ Sym.pi24) x0) ∧
      0 < Split.det3 (q - p) ((x ∘ Sym.pi24) 4 - p) (uB (x ∘ Sym.pi24) x0) ∧
      0 < Split.det3 (r - q) ((x ∘ Sym.pi24) 4 - q) (uB (x ∘ Sym.pi24) x0) ∧
      0 < Split.det3 (p - r) ((x ∘ Sym.pi24) 4 - r) (uB (x ∘ Sym.pi24) x0))
    (a : ZMod 5)
    (hD0 : ⟪(x ∘ Sym.pi24) (cA (a + 1)) - (x ∘ Sym.pi24) (cA a), uB (x ∘ Sym.pi24) x0⟫ ≠ 0)
    (hc_ne0 : ∀ i : ZMod 5, i ≠ a →
      Split.det3 ((x ∘ Sym.pi24) (cA (i + 1)) - (x ∘ Sym.pi24) (cA i))
        ((x ∘ Sym.pi24) (cA (a + 1)) - (x ∘ Sym.pi24) (cA a)) (uB (x ∘ Sym.pi24) x0) ≠ 0)
    (sh : ℝ) (hsh : sh = 1 ∨ sh = -1) (α' μ' : ℝ)
    (hBlue0 : ∀ i j : ZMod 5, i ≠ a → (j = i ∨ j = i + 1) →
      0 < Split.det3 ((x ∘ Sym.pi24) (cA (i + 1)) - (x ∘ Sym.pi24) (cA i))
          ((x ∘ Sym.pi24) (cA (a + 1)) - (x ∘ Sym.pi24) (cA a)) (uB (x ∘ Sym.pi24) x0) →
      (-sh * ⟪Split.Slope.linSpinVec (fun t => (x ∘ Sym.pi24) (cA t)) a i j,
            uB (x ∘ Sym.pi24) x0⟫ /
          Split.det3 ((x ∘ Sym.pi24) (cA (i + 1)) - (x ∘ Sym.pi24) (cA i))
            ((x ∘ Sym.pi24) (cA (a + 1)) - (x ∘ Sym.pi24) (cA a)) (uB (x ∘ Sym.pi24) x0)) -
        μ' * ⟪(x ∘ Sym.pi24) (cA j) - (x ∘ Sym.pi24) (cA a), uB (x ∘ Sym.pi24) x0⟫ < α')
    (hOrange0 : ∀ p q : ZMod 5, p ≠ a → (q = p ∨ q = p + 1) →
      Split.det3 ((x ∘ Sym.pi24) (cA (p + 1)) - (x ∘ Sym.pi24) (cA p))
          ((x ∘ Sym.pi24) (cA (a + 1)) - (x ∘ Sym.pi24) (cA a)) (uB (x ∘ Sym.pi24) x0) < 0 →
      α' < (-sh * ⟪Split.Slope.linSpinVec (fun t => (x ∘ Sym.pi24) (cA t)) a p q,
            uB (x ∘ Sym.pi24) x0⟫ /
          Split.det3 ((x ∘ Sym.pi24) (cA (p + 1)) - (x ∘ Sym.pi24) (cA p))
            ((x ∘ Sym.pi24) (cA (a + 1)) - (x ∘ Sym.pi24) (cA a)) (uB (x ∘ Sym.pi24) x0)) -
        μ' * ⟪(x ∘ Sym.pi24) (cA q) - (x ∘ Sym.pi24) (cA a), uB (x ∘ Sym.pi24) x0⟫) :
    Gen.EdgePlaneAny x :=
  edgePlaneAny_of_comp_pi24 x
    (famA_edgePlaneAny (Sym.sym24 F) ((Sym.cbarIn_comp_pi24 x).2 hC) hI h6 h8 hhid4
      a hD0 hc_ne0 sh hsh α' μ' hBlue0 hOrange0)

/-- **FQ1 (`cB` `π_24` twin leaf):** `famB_edgePlaneAny` on `(x ∘ Sym.pi24, Sym.sym24 F)`. -/
theorem famB_edgePlaneAny_twin {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    {x0 : ℝ} (hI : InI5 (x ∘ Sym.pi24) x0)
    (h6 : 0 < ⟪(Sym.sym24 F).N 6, uB (x ∘ Sym.pi24) x0⟫)
    (h8 : 0 < ⟪(Sym.sym24 F).N 8, uB (x ∘ Sym.pi24) x0⟫)
    (a : ZMod 6)
    (hD0 : ⟪(x ∘ Sym.pi24) (cB (a + 1)) - (x ∘ Sym.pi24) (cB a), uB (x ∘ Sym.pi24) x0⟫ ≠ 0)
    (hc_ne0 : ∀ i : ZMod 6, i ≠ a →
      Split.det3 ((x ∘ Sym.pi24) (cB (i + 1)) - (x ∘ Sym.pi24) (cB i))
        ((x ∘ Sym.pi24) (cB (a + 1)) - (x ∘ Sym.pi24) (cB a)) (uB (x ∘ Sym.pi24) x0) ≠ 0)
    (sh : ℝ) (hsh : sh = 1 ∨ sh = -1) (α' μ' : ℝ)
    (hBlue0 : ∀ i j : ZMod 6, i ≠ a → (j = i ∨ j = i + 1) →
      0 < Split.det3 ((x ∘ Sym.pi24) (cB (i + 1)) - (x ∘ Sym.pi24) (cB i))
          ((x ∘ Sym.pi24) (cB (a + 1)) - (x ∘ Sym.pi24) (cB a)) (uB (x ∘ Sym.pi24) x0) →
      (-sh * ⟪Split.Slope.linSpinVec (fun t => (x ∘ Sym.pi24) (cB t)) a i j,
            uB (x ∘ Sym.pi24) x0⟫ /
          Split.det3 ((x ∘ Sym.pi24) (cB (i + 1)) - (x ∘ Sym.pi24) (cB i))
            ((x ∘ Sym.pi24) (cB (a + 1)) - (x ∘ Sym.pi24) (cB a)) (uB (x ∘ Sym.pi24) x0)) -
        μ' * ⟪(x ∘ Sym.pi24) (cB j) - (x ∘ Sym.pi24) (cB a), uB (x ∘ Sym.pi24) x0⟫ < α')
    (hOrange0 : ∀ p q : ZMod 6, p ≠ a → (q = p ∨ q = p + 1) →
      Split.det3 ((x ∘ Sym.pi24) (cB (p + 1)) - (x ∘ Sym.pi24) (cB p))
          ((x ∘ Sym.pi24) (cB (a + 1)) - (x ∘ Sym.pi24) (cB a)) (uB (x ∘ Sym.pi24) x0) < 0 →
      α' < (-sh * ⟪Split.Slope.linSpinVec (fun t => (x ∘ Sym.pi24) (cB t)) a p q,
            uB (x ∘ Sym.pi24) x0⟫ /
          Split.det3 ((x ∘ Sym.pi24) (cB (p + 1)) - (x ∘ Sym.pi24) (cB p))
            ((x ∘ Sym.pi24) (cB (a + 1)) - (x ∘ Sym.pi24) (cB a)) (uB (x ∘ Sym.pi24) x0)) -
        μ' * ⟪(x ∘ Sym.pi24) (cB q) - (x ∘ Sym.pi24) (cB a), uB (x ∘ Sym.pi24) x0⟫) :
    Gen.EdgePlaneAny x :=
  edgePlaneAny_of_comp_pi24 x
    (famB_edgePlaneAny (Sym.sym24 F) ((Sym.cbarIn_comp_pi24 x).2 hC) hI h6 h8
      a hD0 hc_ne0 sh hsh α' μ' hBlue0 hOrange0)

theorem holeLeaf_not_famA_twin {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F)
    {x0 : ℝ} (hc : FamACertAt (x ∘ Sym.pi24) (Sym.sym24 F) x0) : False := by
  rcases hc with ⟨hI, h6, h8, hhid4, a, hD0, hc_ne0, sh, α', μ', hsh, hB, hO⟩
  exact Atlas.holeLeaf_not_edgePlaneAny hF
    (famA_edgePlaneAny_twin F hF.1 hI h6 h8 hhid4 a hD0 hc_ne0 sh hsh α' μ' hB hO)

theorem hole24_not_famA_twin {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : Hole24 x F)
    {x0 : ℝ} (hc : FamACertAt (x ∘ Sym.pi24) (Sym.sym24 F) x0) : False :=
  holeLeaf_not_famA_twin hF.1 hc

theorem holeLeaf_not_famB_twin {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F)
    {x0 : ℝ} (hc : FamBCertAt (x ∘ Sym.pi24) (Sym.sym24 F) x0) : False := by
  rcases hc with ⟨hI, h6, h8, a, hD0, hc_ne0, sh, α', μ', hsh, hB, hO⟩
  exact Atlas.holeLeaf_not_edgePlaneAny hF
    (famB_edgePlaneAny_twin F hF.1 hI h6 h8 a hD0 hc_ne0 sh hsh α' μ' hB hO)

theorem hole24_not_famB_twin {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : Hole24 x F)
    {x0 : ℝ} (hc : FamBCertAt (x ∘ Sym.pi24) (Sym.sym24 F) x0) : False :=
  holeLeaf_not_famB_twin hF.1 hc

/-- Extended two-cone residue adding the `π_24` twins `¬ FamACertAt` and `¬ FamBCertAt`. -/
def TwoConeResidue'' (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  TwoConeResidue' x F ∧
  (∀ x0 : ℝ, ¬ FamACertAt (x ∘ Sym.pi24) (Sym.sym24 F) x0) ∧
  (∀ x0 : ℝ, ¬ FamBCertAt (x ∘ Sym.pi24) (Sym.sym24 F) x0)

theorem hole24_twoConeResidue'' {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (hF : Hole24 x F) :
    TwoConeResidue'' x F :=
  ⟨hole24_twoConeResidue' hF,
    fun _ h => hole24_not_famA_twin hF h,
    fun _ h => hole24_not_famB_twin hF h⟩

/-! ## FQ2: `T_0` rim determinants (`cA = ![1, 2, 5, 3, 6]`, edge `3 → 6`, Lemma T1) -/

/-- `γ_0(x0) := (1 - x0) / ω_5(x)` used in `uB x x0`. -/
noncomputable def gamma0 (x : Fin 7 → ℝ³) (x0 : ℝ) : ℝ := (1 - x0) / omega5 x

/-- `τ_1(x0)` (`2 → 5` determinant factor). -/
noncomputable def tau1 (x : Fin 7 → ℝ³) (x0 : ℝ) : ℝ :=
  -oblX0 x 5 * (1 - oblX6 x 3 + oblX2 x 3 * gamma0 x x0) +
    (oblX2 x 5 - 1) * (Hh x x0 (gamma0 x x0) 3 - x0) -
    oblX6 x 5 * (oblX0 x 3 + oblX2 x 3 * x0)

end Minimality.T24.TwoCone
