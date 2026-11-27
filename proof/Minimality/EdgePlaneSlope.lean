module

public import Minimality.Type24DeepC
public import Minimality.Type24BeltCell
public import Minimality.EdgePlaneLWrap

/-!
# Edge-Plane as a slope window and the closed-form view `w_C` (`FK1`–`FK3`)

* `Minimality.Split.Slope` (`FK1`):
  - `edgePlaneSpin_eq_linSpin` (`FK1(a)`): `edgePlaneSpin X w a i j = (‖w‖^2 / D) * ⟪v i j, w⟫`
    where `v i j = ⟪E_i, X j - X a⟫ • d - ⟪E_i, d⟫ • (X j - X a)`.
  - `epRows_of_lineSep` (`FK1(b)` first-form): separating `y i j - μ' * zt j < α'` (Blue, `0 < c_i`)
    from `α' < y p q - μ' * zt q` (Orange, `c_p < 0`) yields `EPRows X w a s α μ`.
  - `edgePlaneAt_of_lineSep`: corollary giving `DeepC.EdgePlaneAt x w` under `StrictRimN` and
    `HiddenInTriangles`.
  - `epRows_of_slopeWindow` (`FK1` slope-window form): equal-`zt` apex gap plus every lower-slope
    `<` every upper-slope yields `EPRows X w a s α μ`.
* `Minimality.T24.WC` (`FK2`–`FK3`):
  - `wcCell_eventually` (`FK2`): cell membership `CellAt F {3,4,6,8} {0,1,2,5,7} (capView x 1 η c_c)`
    eventually as `η → 0+` under the `c_c` window.
  - `wc_det3_rim` (`FK3`): at `w0 = capView x 1 0 c_c` and rim `[0, 5, 2, 3, 6]`, edge `6 → 0`,
    `det3 E_i (x 0 - x 6) w0` equals `(1 + c_c) * det24 x` times `(-b5, -(1 - b5), 1 - b3, b3)`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset Filter
open scoped Topology
open Minimality

namespace Minimality.Split.Slope

/-- Linearized spin vector `v i j = ⟪E_i, X j - X a⟫ • d - ⟪E_i, d⟫ • (X j - X a)`. -/
noncomputable def linSpinVec {k : ℕ} (X : ZMod k → ℝ³) (a i j : ZMod k) : ℝ³ :=
  ⟪X (i + 1) - X i, X j - X a⟫ • (X (a + 1) - X a) -
    ⟪X (i + 1) - X i, X (a + 1) - X a⟫ • (X j - X a)

/-- **FK1(a):** `edgePlaneSpin X w a i j = (‖w‖^2 / D) * ⟪linSpinVec X a i j, w⟫`. -/
theorem edgePlaneSpin_eq_linSpin {k : ℕ} (X : ZMod k → ℝ³) (w : ℝ³) (a i j : ZMod k)
    (hD : ⟪X (a + 1) - X a, w⟫ ≠ 0) :
    Split.edgePlaneSpin X w a i j =
      (‖w‖ ^ 2 / ⟪X (a + 1) - X a, w⟫) * ⟪linSpinVec X a i j, w⟫ := by
  let E := X (i + 1) - X i
  let d := X (a + 1) - X a
  let D := ⟪d, w⟫
  have hD' : D ≠ 0 := hD
  have e1 : Split.det3 E (cross w (X j - X a)) w =
      ⟪w, w⟫ * ⟪X j - X a, E⟫ - ⟪X j - X a, w⟫ * ⟪E, w⟫ := by
    simp only [Split.det3, Split.inner3, Split.cross_0, Split.cross_1, Split.cross_2]; ring
  have e2 : Split.det3 E (cross d w) w = D * ⟪E, w⟫ - ⟪w, w⟫ * ⟪E, d⟫ := by
    dsimp only [D]
    simp only [Split.det3, Split.inner3, Split.cross_0, Split.cross_1, Split.cross_2]; ring
  have hw2 : ‖w‖ ^ 2 = ⟪w, w⟫ := real_inner_self_eq_norm_sq w |>.symm
  have hv : ⟪linSpinVec X a i j, w⟫ =
      ⟪E, X j - X a⟫ * D - ⟪E, d⟫ * ⟪X j - X a, w⟫ := by
    simp only [linSpinVec, inner_sub_left, real_inner_smul_left]
    dsimp only [E, d, D]
    simp only [inner_sub_left]
  unfold Split.edgePlaneSpin
  change Split.det3 E (cross w (X j - X a)) w +
      (⟪X j - X a, w⟫ / D) * Split.det3 E (cross d w) w =
    (‖w‖ ^ 2 / D) * ⟪linSpinVec X a i j, w⟫
  rw [e1, e2, hw2, hv, real_inner_comm (X j - X a) E]
  field_simp [hD']
  ring

/-- **FK1(b) first-form:** if all `c_i ≠ 0` (`i ≠ a`) and for some `sh ∈ {1, -1}` there exist
`α', μ'` separating `y i j - μ' * zt j < α'` (Blue, `0 < c_i`) from `α' < y p q - μ' * zt q`
(Orange, `c_p < 0`), then `Split.EV.EPRows X w a s α μ` holds. -/
theorem epRows_of_lineSep {k : ℕ} (X : ZMod k → ℝ³) (w : ℝ³) (a : ZMod k)
    (hD : ⟪X (a + 1) - X a, w⟫ ≠ 0)
    (hc_ne : ∀ i : ZMod k, i ≠ a → Split.det3 (X (i + 1) - X i) (X (a + 1) - X a) w ≠ 0)
    (sh : ℝ) (_hsh : sh = 1 ∨ sh = -1) (α' μ' : ℝ)
    (hBlue : ∀ i j : ZMod k, i ≠ a → (j = i ∨ j = i + 1) →
      0 < Split.det3 (X (i + 1) - X i) (X (a + 1) - X a) w →
      (-sh * ⟪linSpinVec X a i j, w⟫ /
          Split.det3 (X (i + 1) - X i) (X (a + 1) - X a) w) -
        μ' * ⟪X j - X a, w⟫ < α')
    (hOrange : ∀ p q : ZMod k, p ≠ a → (q = p ∨ q = p + 1) →
      Split.det3 (X (p + 1) - X p) (X (a + 1) - X a) w < 0 →
      α' < (-sh * ⟪linSpinVec X a p q, w⟫ /
          Split.det3 (X (p + 1) - X p) (X (a + 1) - X a) w) -
        μ' * ⟪X q - X a, w⟫) :
    ∃ s α μ : ℝ, Split.EV.EPRows X w a s α μ := by
  have hw0 : w ≠ 0 := by
    intro h0; rw [h0, inner_zero_right] at hD; exact hD rfl
  have hwn2 : 0 < ‖w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hw0)
  let s : ℝ := sh * ⟪X (a + 1) - X a, w⟫ / ‖w‖ ^ 2
  refine ⟨s, α', μ', fun i j hi hj => ?_⟩
  have hspin := edgePlaneSpin_eq_linSpin X w a i j hD
  have hs_mul : s * Split.edgePlaneSpin X w a i j = sh * ⟪linSpinVec X a i j, w⟫ := by
    rw [hspin]
    dsimp only [s]
    field_simp [hD, hwn2.ne']
  rw [hs_mul]
  set ci := Split.det3 (X (i + 1) - X i) (X (a + 1) - X a) w
  have hci : ci ≠ 0 := hc_ne i hi
  have hid : (α' + μ' * ⟪X j - X a, w⟫) * ci + sh * ⟪linSpinVec X a i j, w⟫ =
      ci * (α' - ((-sh * ⟪linSpinVec X a i j, w⟫ / ci) - μ' * ⟪X j - X a, w⟫)) := by
    field_simp [hci]
    ring
  rw [hid]
  rcases lt_or_gt_of_ne hci with hneg | hpos
  · exact mul_pos_of_neg_of_neg hneg (sub_neg.mpr (hOrange i j hi hj hneg))
  · exact mul_pos hpos (sub_pos.mpr (hBlue i j hi hj hpos))

/-- Corollary of `epRows_of_lineSep`: with `StrictRimN` and `HiddenInTriangles` at `w`,
gives `Minimality.T24.DeepC.EdgePlaneAt x w`. -/
theorem edgePlaneAt_of_lineSep {n k : ℕ} [NeZero k] (hk : 3 ≤ k) (x : Fin n → ℝ³) (w : ℝ³)
    (lab : ZMod k → Fin n) (hinj : Function.Injective lab)
    (hrim : Split.StrictRimN x w lab) (hhid : Split.HiddenInTriangles x w lab) (a : ZMod k)
    (hD : ⟪x (lab (a + 1)) - x (lab a), w⟫ ≠ 0)
    (hc_ne : ∀ i : ZMod k, i ≠ a →
      Split.det3 (x (lab (i + 1)) - x (lab i)) (x (lab (a + 1)) - x (lab a)) w ≠ 0)
    (sh : ℝ) (hsh : sh = 1 ∨ sh = -1) (α' μ' : ℝ)
    (hBlue : ∀ i j : ZMod k, i ≠ a → (j = i ∨ j = i + 1) →
      0 < Split.det3 (x (lab (i + 1)) - x (lab i)) (x (lab (a + 1)) - x (lab a)) w →
      (-sh * ⟪linSpinVec (fun t => x (lab t)) a i j, w⟫ /
          Split.det3 (x (lab (i + 1)) - x (lab i)) (x (lab (a + 1)) - x (lab a)) w) -
        μ' * ⟪x (lab j) - x (lab a), w⟫ < α')
    (hOrange : ∀ p q : ZMod k, p ≠ a → (q = p ∨ q = p + 1) →
      Split.det3 (x (lab (p + 1)) - x (lab p)) (x (lab (a + 1)) - x (lab a)) w < 0 →
      α' < (-sh * ⟪linSpinVec (fun t => x (lab t)) a p q, w⟫ /
          Split.det3 (x (lab (p + 1)) - x (lab p)) (x (lab (a + 1)) - x (lab a)) w) -
        μ' * ⟪x (lab q) - x (lab a), w⟫) :
    Minimality.T24.DeepC.EdgePlaneAt x w := by
  obtain ⟨s, α, μ, hrows⟩ := epRows_of_lineSep (fun t => x (lab t)) w a hD hc_ne sh hsh α' μ' hBlue hOrange
  exact ⟨k, inferInstance, lab, a, s, α, μ, hk, hinj, hrim, hhid, hD, hrows⟩

/-- **FK1 slope-window form:** equal-`zt` apex gap plus every lower-slope `<` every upper-slope
implies existence of `(α', μ')` and hence `Split.EV.EPRows X w a s α μ`. -/
theorem epRows_of_slopeWindow {k : ℕ} [NeZero k] (X : ZMod k → ℝ³) (w : ℝ³) (a : ZMod k)
    (hD : ⟪X (a + 1) - X a, w⟫ ≠ 0)
    (hc_ne : ∀ i : ZMod k, i ≠ a → Split.det3 (X (i + 1) - X i) (X (a + 1) - X a) w ≠ 0)
    (sh : ℝ) (hsh : sh = 1 ∨ sh = -1)
    (hEq : ∀ i j p q : ZMod k, i ≠ a → (j = i ∨ j = i + 1) →
      p ≠ a → (q = p ∨ q = p + 1) →
      0 < Split.det3 (X (i + 1) - X i) (X (a + 1) - X a) w →
      Split.det3 (X (p + 1) - X p) (X (a + 1) - X a) w < 0 →
      ⟪X j - X a, w⟫ = ⟪X q - X a, w⟫ →
      (-sh * ⟪linSpinVec X a i j, w⟫ / Split.det3 (X (i + 1) - X i) (X (a + 1) - X a) w) <
        (-sh * ⟪linSpinVec X a p q, w⟫ / Split.det3 (X (p + 1) - X p) (X (a + 1) - X a) w))
    (hSlope : ∀ i₁ j₁ p₁ q₁ i₂ j₂ p₂ q₂ : ZMod k,
      i₁ ≠ a → (j₁ = i₁ ∨ j₁ = i₁ + 1) → p₁ ≠ a → (q₁ = p₁ ∨ q₁ = p₁ + 1) →
      0 < Split.det3 (X (i₁ + 1) - X i₁) (X (a + 1) - X a) w →
      Split.det3 (X (p₁ + 1) - X p₁) (X (a + 1) - X a) w < 0 →
      ⟪X q₁ - X a, w⟫ < ⟪X j₁ - X a, w⟫ →
      i₂ ≠ a → (j₂ = i₂ ∨ j₂ = i₂ + 1) → p₂ ≠ a → (q₂ = p₂ ∨ q₂ = p₂ + 1) →
      0 < Split.det3 (X (i₂ + 1) - X i₂) (X (a + 1) - X a) w →
      Split.det3 (X (p₂ + 1) - X p₂) (X (a + 1) - X a) w < 0 →
      ⟪X j₂ - X a, w⟫ < ⟪X q₂ - X a, w⟫ →
      ((-sh * ⟪linSpinVec X a i₁ j₁, w⟫ / Split.det3 (X (i₁ + 1) - X i₁) (X (a + 1) - X a) w) -
          (-sh * ⟪linSpinVec X a p₁ q₁, w⟫ / Split.det3 (X (p₁ + 1) - X p₁) (X (a + 1) - X a) w)) /
        (⟪X j₁ - X a, w⟫ - ⟪X q₁ - X a, w⟫) <
      ((-sh * ⟪linSpinVec X a p₂ q₂, w⟫ / Split.det3 (X (p₂ + 1) - X p₂) (X (a + 1) - X a) w) -
          (-sh * ⟪linSpinVec X a i₂ j₂, w⟫ / Split.det3 (X (i₂ + 1) - X i₂) (X (a + 1) - X a) w)) /
        (⟪X q₂ - X a, w⟫ - ⟪X j₂ - X a, w⟫)) :
    ∃ s α μ : ℝ, Split.EV.EPRows X w a s α μ := by
  let y : ZMod k × ZMod k → ℝ := fun ⟨i, j⟩ =>
    -sh * ⟪linSpinVec X a i j, w⟫ / Split.det3 (X (i + 1) - X i) (X (a + 1) - X a) w
  let zt : ZMod k → ℝ := fun j => ⟪X j - X a, w⟫
  let isBlue : ZMod k × ZMod k → Prop := fun ⟨i, j⟩ =>
    i ≠ a ∧ (j = i ∨ j = i + 1) ∧ 0 < Split.det3 (X (i + 1) - X i) (X (a + 1) - X a) w
  let isOrange : ZMod k × ZMod k → Prop := fun ⟨p, q⟩ =>
    p ≠ a ∧ (q = p ∨ q = p + 1) ∧ Split.det3 (X (p + 1) - X p) (X (a + 1) - X a) w < 0
  let P_lo : (ZMod k × ZMod k) × (ZMod k × ZMod k) → Prop := fun ⟨b, o⟩ =>
    isBlue b ∧ isOrange o ∧ zt o.2 < zt b.2
  let P_hi : (ZMod k × ZMod k) × (ZMod k × ZMod k) → Prop := fun ⟨b, o⟩ =>
    isBlue b ∧ isOrange o ∧ zt b.2 < zt o.2
  let f_lo : (ZMod k × ZMod k) × (ZMod k × ZMod k) → ℝ := fun ⟨b, o⟩ =>
    (y b - y o) / (zt b.2 - zt o.2)
  let f_hi : (ZMod k × ZMod k) × (ZMod k × ZMod k) → ℝ := fun ⟨b, o⟩ =>
    (y o - y b) / (zt o.2 - zt b.2)
  -- Pick `μ'` strictly between `max P_lo f_lo` and `min P_hi f_hi`
  have hμ' : ∃ μ' : ℝ,
      (∀ r, P_lo r → f_lo r < μ') ∧ (∀ r, P_hi r → μ' < f_hi r) := by
    classical
    by_cases hne_lo : ∃ r, P_lo r
    · obtain ⟨r_lo, hr_lo, hmax⟩ := Finset.exists_max_image (Finset.univ.filter P_lo) f_lo
        (by obtain ⟨r, hr⟩ := hne_lo; exact ⟨r, by simpa using hr⟩)
      obtain ⟨m_hi, hm_hi_gt, hm_hi_le⟩ := Split.LWrap.exists_lower P_hi f_hi (f_lo r_lo) (by
        rintro ⟨⟨i₂, j₂⟩, ⟨p₂, q₂⟩⟩ ⟨hb₂, ho₂, hlt₂⟩
        rcases r_lo with ⟨⟨i₁, j₁⟩, ⟨p₁, q₁⟩⟩
        have hr_lo' : P_lo ((i₁, j₁), (p₁, q₁)) := by simpa using hr_lo
        exact hSlope i₁ j₁ p₁ q₁ i₂ j₂ p₂ q₂
          hr_lo'.1.1 hr_lo'.1.2.1 hr_lo'.2.1.1 hr_lo'.2.1.2.1 hr_lo'.1.2.2 hr_lo'.2.1.2.2 hr_lo'.2.2
          hb₂.1 hb₂.2.1 ho₂.1 ho₂.2.1 hb₂.2.2 ho₂.2.2 hlt₂)
      refine ⟨(f_lo r_lo + m_hi) / 2, fun r hr => ?_, fun r hr => ?_⟩
      · have := hmax r (by simpa using hr); linarith
      · have := hm_hi_le r hr; linarith
    · by_cases hne_hi : ∃ r, P_hi r
      · obtain ⟨r_hi, hr_hi, hmin⟩ := Finset.exists_min_image (Finset.univ.filter P_hi) f_hi
          (by obtain ⟨r, hp⟩ := hne_hi; exact ⟨r, by simpa using hp⟩)
        refine ⟨f_hi r_hi - 1, fun r hr => absurd ⟨r, hr⟩ hne_lo, fun r hr => ?_⟩
        have := hmin r (by simpa using hr); linarith
      · exact ⟨0, fun r hr => absurd ⟨r, hr⟩ hne_lo, fun r hr => absurd ⟨r, hr⟩ hne_hi⟩
  obtain ⟨μ', hμ_lo, hμ_hi⟩ := hμ'
  let g : ZMod k × ZMod k → ℝ := fun r => y r - μ' * zt r.2
  have hsep : ∀ b o : ZMod k × ZMod k, isBlue b → isOrange o → g b < g o := by
    rintro ⟨i, j⟩ ⟨p, q⟩ hb ho
    dsimp only [g]
    rcases lt_trichotomy (zt j) (zt q) with hlt | heq | hgt
    · have hmu := hμ_hi ((i, j), (p, q)) ⟨hb, ho, hlt⟩
      dsimp only [f_hi] at hmu
      have hdiff : 0 < zt q - zt j := sub_pos.mpr hlt
      have := (lt_div_iff₀ hdiff).mp hmu
      linarith
    · have he := hEq i j p q hb.1 hb.2.1 ho.1 ho.2.1 hb.2.2 ho.2.2 heq
      dsimp only [y, zt] at *
      rw [heq]
      linarith
    · have hmu := hμ_lo ((i, j), (p, q)) ⟨hb, ho, hgt⟩
      dsimp only [f_lo] at hmu
      have hdiff : 0 < zt j - zt q := sub_pos.mpr hgt
      have := (div_lt_iff₀ hdiff).mp hmu
      linarith
  have hα' : ∃ α' : ℝ, (∀ b, isBlue b → g b < α') ∧ (∀ o, isOrange o → α' < g o) := by
    classical
    by_cases hne_b : ∃ b, isBlue b
    · obtain ⟨b0, hb0, hmax⟩ := Finset.exists_max_image (Finset.univ.filter isBlue) g
        (by obtain ⟨b, hb⟩ := hne_b; exact ⟨b, by simpa using hb⟩)
      have hb0' : isBlue b0 := by simpa using hb0
      obtain ⟨m_o, hm_o_gt, hm_o_le⟩ := Split.LWrap.exists_lower isOrange g (g b0)
        (fun o ho => hsep b0 o hb0' ho)
      refine ⟨(g b0 + m_o) / 2, fun b hb => ?_, fun o ho => ?_⟩
      · have := hmax b (by simpa using hb); linarith
      · have := hm_o_le o ho; linarith
    · by_cases hne_o : ∃ o, isOrange o
      · obtain ⟨o0, ho0, hmin⟩ := Finset.exists_min_image (Finset.univ.filter isOrange) g
          (by obtain ⟨o, ho⟩ := hne_o; exact ⟨o, by simpa using ho⟩)
        refine ⟨g o0 - 1, fun b hb => absurd ⟨b, hb⟩ hne_b, fun o ho => ?_⟩
        have := hmin o (by simpa using ho); linarith
      · exact ⟨0, fun b hb => absurd ⟨b, hb⟩ hne_b, fun o ho => absurd ⟨o, ho⟩ hne_o⟩
  obtain ⟨α', hα_b, hα_o⟩ := hα'
  exact epRows_of_lineSep X w a hD hc_ne sh hsh α' μ'
    (fun i j hi hj hpos => hα_b (i, j) ⟨hi, hj, hpos⟩)
    (fun p q hp hq hneg => hα_o (p, q) ⟨hp, hq, hneg⟩)

/-- **FV1 helper:** unified signed-depth order certificate (`σ = 1` for Blue `≤` Orange,
yielding `μ' < 0`; `σ = -1` for Orange `≤` Blue, yielding `0 < μ'`), with shared-apex ties
`zt j = zt q → y b < y o`. -/
theorem lineSep_of_depthOrder_dir {k : ℕ} [NeZero k] (X : ZMod k → ℝ³) (w : ℝ³) (a : ZMod k)
    (sh : ℝ) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hOrd : ∀ i j p q : ZMod k, i ≠ a → (j = i ∨ j = i + 1) →
      p ≠ a → (q = p ∨ q = p + 1) →
      0 < Split.det3 (X (i + 1) - X i) (X (a + 1) - X a) w →
      Split.det3 (X (p + 1) - X p) (X (a + 1) - X a) w < 0 →
      σ * ⟪X j - X a, w⟫ ≤ σ * ⟪X q - X a, w⟫)
    (hEq : ∀ i j p q : ZMod k, i ≠ a → (j = i ∨ j = i + 1) →
      p ≠ a → (q = p ∨ q = p + 1) →
      0 < Split.det3 (X (i + 1) - X i) (X (a + 1) - X a) w →
      Split.det3 (X (p + 1) - X p) (X (a + 1) - X a) w < 0 →
      ⟪X j - X a, w⟫ = ⟪X q - X a, w⟫ →
      (-sh * ⟪linSpinVec X a i j, w⟫ / Split.det3 (X (i + 1) - X i) (X (a + 1) - X a) w) <
        (-sh * ⟪linSpinVec X a p q, w⟫ / Split.det3 (X (p + 1) - X p) (X (a + 1) - X a) w)) :
    ∃ α' μ' : ℝ, σ * μ' < 0 ∧
      (∀ i j : ZMod k, i ≠ a → (j = i ∨ j = i + 1) →
        0 < Split.det3 (X (i + 1) - X i) (X (a + 1) - X a) w →
        (-sh * ⟪linSpinVec X a i j, w⟫ /
            Split.det3 (X (i + 1) - X i) (X (a + 1) - X a) w) -
          μ' * ⟪X j - X a, w⟫ < α') ∧
      (∀ p q : ZMod k, p ≠ a → (q = p ∨ q = p + 1) →
        Split.det3 (X (p + 1) - X p) (X (a + 1) - X a) w < 0 →
        α' < (-sh * ⟪linSpinVec X a p q, w⟫ /
            Split.det3 (X (p + 1) - X p) (X (a + 1) - X a) w) -
          μ' * ⟪X q - X a, w⟫) := by
  classical
  let y : ZMod k × ZMod k → ℝ := fun ⟨i, j⟩ =>
    -sh * ⟪linSpinVec X a i j, w⟫ / Split.det3 (X (i + 1) - X i) (X (a + 1) - X a) w
  let zt : ZMod k → ℝ := fun j => ⟪X j - X a, w⟫
  let isBlue : ZMod k × ZMod k → Prop := fun ⟨i, j⟩ =>
    i ≠ a ∧ (j = i ∨ j = i + 1) ∧ 0 < Split.det3 (X (i + 1) - X i) (X (a + 1) - X a) w
  let isOrange : ZMod k × ZMod k → Prop := fun ⟨p, q⟩ =>
    p ≠ a ∧ (q = p ∨ q = p + 1) ∧ Split.det3 (X (p + 1) - X p) (X (a + 1) - X a) w < 0
  let P_diff : (ZMod k × ZMod k) × (ZMod k × ZMod k) → Prop := fun ⟨b, o⟩ =>
    isBlue b ∧ isOrange o ∧ σ * zt b.2 < σ * zt o.2
  let ratio : (ZMod k × ZMod k) × (ZMod k × ZMod k) → ℝ := fun ⟨b, o⟩ =>
    (y o - y b) / (σ * (zt o.2 - zt b.2))
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hσ_ne : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  have hm : ∃ m : ℝ, m < 0 ∧ ∀ r, P_diff r → m < ratio r := by
    by_cases hne : ∃ r, P_diff r
    · obtain ⟨r0, hr0, hmin⟩ := Finset.exists_min_image (Finset.univ.filter P_diff) ratio
        (by obtain ⟨r, hr⟩ := hne; exact ⟨r, by simpa using hr⟩)
      refine ⟨min (-1) (ratio r0 - 1), lt_of_le_of_lt (min_le_left _ _) (by norm_num),
        fun r hr => ?_⟩
      have h1 := hmin r (by simpa using hr)
      have h2 : min (-1) (ratio r0 - 1) ≤ ratio r0 - 1 := min_le_right _ _
      linarith
    · exact ⟨-1, by norm_num, fun r hr => absurd ⟨r, hr⟩ hne⟩
  obtain ⟨m, hm_neg, hm_lt⟩ := hm
  let μ' : ℝ := σ * m
  have hσμ : σ * μ' < 0 := by dsimp [μ']; rw [← mul_assoc, hσ2, one_mul]; exact hm_neg
  let g : ZMod k × ZMod k → ℝ := fun r => y r - μ' * zt r.2
  have hsep : ∀ b o : ZMod k × ZMod k, isBlue b → isOrange o → g b < g o := by
    rintro ⟨i, j⟩ ⟨p, q⟩ hb ho
    dsimp only [g]
    have hle := hOrd i j p q hb.1 hb.2.1 ho.1 ho.2.1 hb.2.2 ho.2.2
    rcases lt_or_eq_of_le hle with hlt | heq
    · have hrat := hm_lt ((i, j), (p, q)) ⟨hb, ho, hlt⟩
      dsimp only [ratio] at hrat
      have hpos : 0 < σ * (zt q - zt j) := by dsimp [zt] at *; linarith
      have hmul := (lt_div_iff₀ hpos).mp hrat
      have hid : m * (σ * (zt q - zt j)) = μ' * (zt q - zt j) := by dsimp [μ']; ring
      rw [hid] at hmul
      linarith
    · have heqz : zt j = zt q := by
        have := congrArg (σ * ·) heq
        dsimp [zt] at *
        have h1 : σ * (σ * ⟪X j - X a, w⟫) = ⟪X j - X a, w⟫ := by
          calc σ * (σ * ⟪X j - X a, w⟫) = (σ * σ) * ⟪X j - X a, w⟫ := by ring
            _ = ⟪X j - X a, w⟫ := by rw [hσ2, one_mul]
        have h2 : σ * (σ * ⟪X q - X a, w⟫) = ⟪X q - X a, w⟫ := by
          calc σ * (σ * ⟪X q - X a, w⟫) = (σ * σ) * ⟪X q - X a, w⟫ := by ring
            _ = ⟪X q - X a, w⟫ := by rw [hσ2, one_mul]
        linarith
      have hy := hEq i j p q hb.1 hb.2.1 ho.1 ho.2.1 hb.2.2 ho.2.2 heqz
      dsimp only [y, zt] at *
      rw [heqz]
      linarith
  have hα' : ∃ α' : ℝ, (∀ b, isBlue b → g b < α') ∧ (∀ o, isOrange o → α' < g o) := by
    by_cases hne_b : ∃ b, isBlue b
    · obtain ⟨b0, hb0, hmax⟩ := Finset.exists_max_image (Finset.univ.filter isBlue) g
        (by obtain ⟨b, hb⟩ := hne_b; exact ⟨b, by simpa using hb⟩)
      have hb0' : isBlue b0 := by simpa using hb0
      obtain ⟨m_o, _, hm_o_le⟩ := Split.LWrap.exists_lower isOrange g (g b0)
        (fun o ho => hsep b0 o hb0' ho)
      refine ⟨(g b0 + m_o) / 2, fun b hb => ?_, fun o ho => ?_⟩
      · have := hmax b (by simpa using hb); linarith
      · have := hm_o_le o ho; linarith
    · by_cases hne_o : ∃ o, isOrange o
      · obtain ⟨o0, ho0, hmin⟩ := Finset.exists_min_image (Finset.univ.filter isOrange) g
          (by obtain ⟨o, ho⟩ := hne_o; exact ⟨o, by simpa using ho⟩)
        refine ⟨g o0 - 1, fun b hb => absurd ⟨b, hb⟩ hne_b, fun o ho => ?_⟩
        have := hmin o (by simpa using ho); linarith
      · exact ⟨0, fun b hb => absurd ⟨b, hb⟩ hne_b, fun o ho => absurd ⟨o, ho⟩ hne_o⟩
  obtain ⟨α', hα_b, hα_o⟩ := hα'
  exact ⟨α', μ', hσμ, fun i j hi hj hpos => hα_b (i, j) ⟨hi, hj, hpos⟩,
    fun p q hp hq hneg => hα_o (p, q) ⟨hp, hq, hneg⟩⟩

/-- **FV1 (`lineSep_of_depthOrder_ties`):** if every Blue depth `≤` every Orange depth (so
`μ' < 0` separates) OR every Orange depth `≤` every Blue depth (so `0 < μ'` separates), with
shared-apex ties `zt j = zt q → y b < y o`, then strict line separation `(α', μ')` exists. -/
theorem lineSep_of_depthOrder_ties {k : ℕ} [NeZero k] (X : ZMod k → ℝ³) (w : ℝ³) (a : ZMod k)
    (sh : ℝ)
    (hOrd : (∀ i j p q : ZMod k, i ≠ a → (j = i ∨ j = i + 1) →
        p ≠ a → (q = p ∨ q = p + 1) →
        0 < Split.det3 (X (i + 1) - X i) (X (a + 1) - X a) w →
        Split.det3 (X (p + 1) - X p) (X (a + 1) - X a) w < 0 →
        ⟪X j - X a, w⟫ ≤ ⟪X q - X a, w⟫) ∨
      (∀ i j p q : ZMod k, i ≠ a → (j = i ∨ j = i + 1) →
        p ≠ a → (q = p ∨ q = p + 1) →
        0 < Split.det3 (X (i + 1) - X i) (X (a + 1) - X a) w →
        Split.det3 (X (p + 1) - X p) (X (a + 1) - X a) w < 0 →
        ⟪X q - X a, w⟫ ≤ ⟪X j - X a, w⟫))
    (hEq : ∀ i j p q : ZMod k, i ≠ a → (j = i ∨ j = i + 1) →
      p ≠ a → (q = p ∨ q = p + 1) →
      0 < Split.det3 (X (i + 1) - X i) (X (a + 1) - X a) w →
      Split.det3 (X (p + 1) - X p) (X (a + 1) - X a) w < 0 →
      ⟪X j - X a, w⟫ = ⟪X q - X a, w⟫ →
      (-sh * ⟪linSpinVec X a i j, w⟫ / Split.det3 (X (i + 1) - X i) (X (a + 1) - X a) w) <
        (-sh * ⟪linSpinVec X a p q, w⟫ / Split.det3 (X (p + 1) - X p) (X (a + 1) - X a) w)) :
    ∃ α' μ' : ℝ,
      (∀ i j : ZMod k, i ≠ a → (j = i ∨ j = i + 1) →
        0 < Split.det3 (X (i + 1) - X i) (X (a + 1) - X a) w →
        (-sh * ⟪linSpinVec X a i j, w⟫ /
            Split.det3 (X (i + 1) - X i) (X (a + 1) - X a) w) -
          μ' * ⟪X j - X a, w⟫ < α') ∧
      (∀ p q : ZMod k, p ≠ a → (q = p ∨ q = p + 1) →
        Split.det3 (X (p + 1) - X p) (X (a + 1) - X a) w < 0 →
        α' < (-sh * ⟪linSpinVec X a p q, w⟫ /
            Split.det3 (X (p + 1) - X p) (X (a + 1) - X a) w) -
          μ' * ⟪X q - X a, w⟫) := by
  rcases hOrd with hBO | hOB
  · obtain ⟨α', μ', _, hB, hO⟩ := lineSep_of_depthOrder_dir X w a sh 1 (Or.inl rfl)
      (fun i j p q hi hj hp hq hb ho => by simpa using hBO i j p q hi hj hp hq hb ho) hEq
    exact ⟨α', μ', hB, hO⟩
  · obtain ⟨α', μ', _, hB, hO⟩ := lineSep_of_depthOrder_dir X w a sh (-1) (Or.inr rfl)
      (fun i j p q hi hj hp hq hb ho => by simpa using hOB i j p q hi hj hp hq hb ho) hEq
    exact ⟨α', μ', hB, hO⟩

/-- **FV1 (`lineSep_of_depthOrder`):** strict depth separation (`z_b < z_o` for all Blue/Orange,
yielding `μ' < 0`, or `z_o < z_b` for all Blue/Orange, yielding `0 < μ'`) with arbitrary `y`
values yields strict line separation `(α', μ')`. -/
theorem lineSep_of_depthOrder {k : ℕ} [NeZero k] (X : ZMod k → ℝ³) (w : ℝ³) (a : ZMod k)
    (sh : ℝ)
    (hOrd : (∀ i j p q : ZMod k, i ≠ a → (j = i ∨ j = i + 1) →
        p ≠ a → (q = p ∨ q = p + 1) →
        0 < Split.det3 (X (i + 1) - X i) (X (a + 1) - X a) w →
        Split.det3 (X (p + 1) - X p) (X (a + 1) - X a) w < 0 →
        ⟪X j - X a, w⟫ < ⟪X q - X a, w⟫) ∨
      (∀ i j p q : ZMod k, i ≠ a → (j = i ∨ j = i + 1) →
        p ≠ a → (q = p ∨ q = p + 1) →
        0 < Split.det3 (X (i + 1) - X i) (X (a + 1) - X a) w →
        Split.det3 (X (p + 1) - X p) (X (a + 1) - X a) w < 0 →
        ⟪X q - X a, w⟫ < ⟪X j - X a, w⟫)) :
    ∃ α' μ' : ℝ,
      (∀ i j : ZMod k, i ≠ a → (j = i ∨ j = i + 1) →
        0 < Split.det3 (X (i + 1) - X i) (X (a + 1) - X a) w →
        (-sh * ⟪linSpinVec X a i j, w⟫ /
            Split.det3 (X (i + 1) - X i) (X (a + 1) - X a) w) -
          μ' * ⟪X j - X a, w⟫ < α') ∧
      (∀ p q : ZMod k, p ≠ a → (q = p ∨ q = p + 1) →
        Split.det3 (X (p + 1) - X p) (X (a + 1) - X a) w < 0 →
        α' < (-sh * ⟪linSpinVec X a p q, w⟫ /
            Split.det3 (X (p + 1) - X p) (X (a + 1) - X a) w) -
          μ' * ⟪X q - X a, w⟫) := by
  refine lineSep_of_depthOrder_ties X w a sh ?_ ?_
  · rcases hOrd with hBO | hOB
    · exact Or.inl (fun i j p q hi hj hp hq hb ho => le_of_lt (hBO i j p q hi hj hp hq hb ho))
    · exact Or.inr (fun i j p q hi hj hp hq hb ho => le_of_lt (hOB i j p q hi hj hp hq hb ho))
  · intro i j p q hi hj hp hq hb ho heq
    rcases hOrd with hBO | hOB
    · exact absurd heq (ne_of_lt (hBO i j p q hi hj hp hq hb ho))
    · exact absurd heq.symm (ne_of_lt (hOB i j p q hi hj hp hq hb ho))

/-- **FV1:** `epRows_of_depthOrder_ties` (`EPRows` from an order certificate with shared-apex ties). -/
theorem epRows_of_depthOrder_ties {k : ℕ} [NeZero k] (X : ZMod k → ℝ³) (w : ℝ³) (a : ZMod k)
    (hD : ⟪X (a + 1) - X a, w⟫ ≠ 0)
    (hc_ne : ∀ i : ZMod k, i ≠ a → Split.det3 (X (i + 1) - X i) (X (a + 1) - X a) w ≠ 0)
    (sh : ℝ) (hsh : sh = 1 ∨ sh = -1)
    (hOrd : (∀ i j p q : ZMod k, i ≠ a → (j = i ∨ j = i + 1) →
        p ≠ a → (q = p ∨ q = p + 1) →
        0 < Split.det3 (X (i + 1) - X i) (X (a + 1) - X a) w →
        Split.det3 (X (p + 1) - X p) (X (a + 1) - X a) w < 0 →
        ⟪X j - X a, w⟫ ≤ ⟪X q - X a, w⟫) ∨
      (∀ i j p q : ZMod k, i ≠ a → (j = i ∨ j = i + 1) →
        p ≠ a → (q = p ∨ q = p + 1) →
        0 < Split.det3 (X (i + 1) - X i) (X (a + 1) - X a) w →
        Split.det3 (X (p + 1) - X p) (X (a + 1) - X a) w < 0 →
        ⟪X q - X a, w⟫ ≤ ⟪X j - X a, w⟫))
    (hEq : ∀ i j p q : ZMod k, i ≠ a → (j = i ∨ j = i + 1) →
      p ≠ a → (q = p ∨ q = p + 1) →
      0 < Split.det3 (X (i + 1) - X i) (X (a + 1) - X a) w →
      Split.det3 (X (p + 1) - X p) (X (a + 1) - X a) w < 0 →
      ⟪X j - X a, w⟫ = ⟪X q - X a, w⟫ →
      (-sh * ⟪linSpinVec X a i j, w⟫ / Split.det3 (X (i + 1) - X i) (X (a + 1) - X a) w) <
        (-sh * ⟪linSpinVec X a p q, w⟫ / Split.det3 (X (p + 1) - X p) (X (a + 1) - X a) w)) :
    ∃ s α μ : ℝ, Split.EV.EPRows X w a s α μ := by
  obtain ⟨α', μ', hB, hO⟩ := lineSep_of_depthOrder_ties X w a sh hOrd hEq
  exact epRows_of_lineSep X w a hD hc_ne sh hsh α' μ' hB hO

/-- **FV1:** `edgePlaneAt_of_depthOrder_ties` (`EdgePlaneAt` from an order certificate with ties). -/
theorem edgePlaneAt_of_depthOrder_ties {n k : ℕ} [NeZero k] (hk : 3 ≤ k) (x : Fin n → ℝ³)
    (w : ℝ³) (lab : ZMod k → Fin n) (hinj : Function.Injective lab)
    (hrim : Split.StrictRimN x w lab) (hhid : Split.HiddenInTriangles x w lab) (a : ZMod k)
    (hD : ⟪x (lab (a + 1)) - x (lab a), w⟫ ≠ 0)
    (hc_ne : ∀ i : ZMod k, i ≠ a →
      Split.det3 (x (lab (i + 1)) - x (lab i)) (x (lab (a + 1)) - x (lab a)) w ≠ 0)
    (sh : ℝ) (hsh : sh = 1 ∨ sh = -1)
    (hOrd : (∀ i j p q : ZMod k, i ≠ a → (j = i ∨ j = i + 1) →
        p ≠ a → (q = p ∨ q = p + 1) →
        0 < Split.det3 (x (lab (i + 1)) - x (lab i)) (x (lab (a + 1)) - x (lab a)) w →
        Split.det3 (x (lab (p + 1)) - x (lab p)) (x (lab (a + 1)) - x (lab a)) w < 0 →
        ⟪x (lab j) - x (lab a), w⟫ ≤ ⟪x (lab q) - x (lab a), w⟫) ∨
      (∀ i j p q : ZMod k, i ≠ a → (j = i ∨ j = i + 1) →
        p ≠ a → (q = p ∨ q = p + 1) →
        0 < Split.det3 (x (lab (i + 1)) - x (lab i)) (x (lab (a + 1)) - x (lab a)) w →
        Split.det3 (x (lab (p + 1)) - x (lab p)) (x (lab (a + 1)) - x (lab a)) w < 0 →
        ⟪x (lab q) - x (lab a), w⟫ ≤ ⟪x (lab j) - x (lab a), w⟫))
    (hEq : ∀ i j p q : ZMod k, i ≠ a → (j = i ∨ j = i + 1) →
      p ≠ a → (q = p ∨ q = p + 1) →
      0 < Split.det3 (x (lab (i + 1)) - x (lab i)) (x (lab (a + 1)) - x (lab a)) w →
      Split.det3 (x (lab (p + 1)) - x (lab p)) (x (lab (a + 1)) - x (lab a)) w < 0 →
      ⟪x (lab j) - x (lab a), w⟫ = ⟪x (lab q) - x (lab a), w⟫ →
      (-sh * ⟪linSpinVec (fun t => x (lab t)) a i j, w⟫ /
          Split.det3 (x (lab (i + 1)) - x (lab i)) (x (lab (a + 1)) - x (lab a)) w) <
        (-sh * ⟪linSpinVec (fun t => x (lab t)) a p q, w⟫ /
          Split.det3 (x (lab (p + 1)) - x (lab p)) (x (lab (a + 1)) - x (lab a)) w)) :
    Minimality.T24.DeepC.EdgePlaneAt x w := by
  obtain ⟨α', μ', hB, hO⟩ := lineSep_of_depthOrder_ties (fun t => x (lab t)) w a sh hOrd hEq
  exact edgePlaneAt_of_lineSep hk x w lab hinj hrim hhid a hD hc_ne sh hsh α' μ' hB hO

/-- Shared **Order Certificate (`OC`)** at view `w` on rim `X : ZMod k → ℝ³` (with ties). -/
def OrderCertAt {k : ℕ} (X : ZMod k → ℝ³) (w : ℝ³) : Prop :=
  ∃ a : ZMod k,
    ⟪X (a + 1) - X a, w⟫ ≠ 0 ∧
    (∀ i : ZMod k, i ≠ a → Split.det3 (X (i + 1) - X i) (X (a + 1) - X a) w ≠ 0) ∧
    ∃ sh : ℝ, (sh = 1 ∨ sh = -1) ∧
      ((∀ i j p q : ZMod k, i ≠ a → (j = i ∨ j = i + 1) →
          p ≠ a → (q = p ∨ q = p + 1) →
          0 < Split.det3 (X (i + 1) - X i) (X (a + 1) - X a) w →
          Split.det3 (X (p + 1) - X p) (X (a + 1) - X a) w < 0 →
          ⟪X j - X a, w⟫ ≤ ⟪X q - X a, w⟫) ∨
        (∀ i j p q : ZMod k, i ≠ a → (j = i ∨ j = i + 1) →
          p ≠ a → (q = p ∨ q = p + 1) →
          0 < Split.det3 (X (i + 1) - X i) (X (a + 1) - X a) w →
          Split.det3 (X (p + 1) - X p) (X (a + 1) - X a) w < 0 →
          ⟪X q - X a, w⟫ ≤ ⟪X j - X a, w⟫)) ∧
      (∀ i j p q : ZMod k, i ≠ a → (j = i ∨ j = i + 1) →
        p ≠ a → (q = p ∨ q = p + 1) →
        0 < Split.det3 (X (i + 1) - X i) (X (a + 1) - X a) w →
        Split.det3 (X (p + 1) - X p) (X (a + 1) - X a) w < 0 →
        ⟪X j - X a, w⟫ = ⟪X q - X a, w⟫ →
        (-sh * ⟪linSpinVec X a i j, w⟫ / Split.det3 (X (i + 1) - X i) (X (a + 1) - X a) w) <
          (-sh * ⟪linSpinVec X a p q, w⟫ / Split.det3 (X (p + 1) - X p) (X (a + 1) - X a) w))

end Minimality.Split.Slope

namespace Minimality.T24.WC

open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.M4 Minimality.T24.HC Minimality.T24.Belt

/-- **FK2 (`wcCell_eventually`):** for `CbarIn x` and `c_c` in the `(1/ω5, ω3)` & `{3, 6, 8}`
window, `CellAt F {3, 4, 6, 8} {0, 1, 2, 5, 7} (capView x 1 η c_c)` holds eventually for `η → 0+`. -/
theorem wcCell_eventually {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hC : CbarIn x) (cc : ℝ)
    (hw5 : 1 / omega5 x < cc) (hw3 : cc < omega3 x)
    (h368_pos : ∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
      0 < ⟪F.N t, x 6 - x 1⟫ → -⟪F.N t, x 0 - x 1⟫ / ⟪F.N t, x 6 - x 1⟫ < cc)
    (h368_neg : ∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
      ⟪F.N t, x 6 - x 1⟫ < 0 → cc < -⟪F.N t, x 0 - x 1⟫ / ⟪F.N t, x 6 - x 1⟫)
    (h368_zero : ∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
      ⟪F.N t, x 6 - x 1⟫ = 0 → 0 < ⟪F.N t, x 0 - x 1⟫) :
    ∀ᶠ η : ℝ in 𝓝[>] 0,
      CellAt F ({3, 4, 6, 8} : Finset (Fin 9)) ({0, 1, 2, 5, 7} : Finset (Fin 9))
        (capView x 1 η cc) := by
  have hcc_pos : 0 < cc := lt_trans (one_div_pos.mpr hC.2.2.1) hw5
  have h368_val : ∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
      0 < ⟪F.N t, x 0 - x 1⟫ + cc * ⟪F.N t, x 6 - x 1⟫ := by
    intro t ht
    rcases lt_trichotomy ⟪F.N t, x 6 - x 1⟫ 0 with hlt | heq | hgt
    · have hc := h368_neg t ht hlt
      have hne : ⟪F.N t, x 6 - x 1⟫ ≠ 0 := hlt.ne
      have hmul : cc * ⟪F.N t, x 6 - x 1⟫ > (-⟪F.N t, x 0 - x 1⟫ / ⟪F.N t, x 6 - x 1⟫) * ⟪F.N t, x 6 - x 1⟫ :=
        mul_lt_mul_of_neg_right hc hlt
      rw [div_mul_cancel₀ _ hne] at hmul
      linarith
    · rw [heq, mul_zero, add_zero]; exact h368_zero t ht heq
    · have hc := h368_pos t ht hgt
      have hne : ⟪F.N t, x 6 - x 1⟫ ≠ 0 := hgt.ne'
      have hmul : (-⟪F.N t, x 0 - x 1⟫ / ⟪F.N t, x 6 - x 1⟫) * ⟪F.N t, x 6 - x 1⟫ < cc * ⟪F.N t, x 6 - x 1⟫ :=
        mul_lt_mul_of_pos_right hc hgt
      rw [div_mul_cancel₀ _ hne] at hmul
      linarith
  have e3 := ev_pos (⟪F.N 3, x 0 - x 1⟫ + cc * ⟪F.N 3, x 6 - x 1⟫) ⟪F.N 3, x 2 - x 1⟫ (h368_val 3 (by decide))
  have e4 := ev_pos ((1 + cc) * (-F.f 4 (x 1))) (F.f 4 (x 2) - F.f 4 (x 1))
    (mul_pos (by linarith) (neg_pos.mpr (F.neg 4 1 (by decide))))
  have e6 := ev_pos (⟪F.N 6, x 0 - x 1⟫ + cc * ⟪F.N 6, x 6 - x 1⟫) ⟪F.N 6, x 2 - x 1⟫ (h368_val 6 (by decide))
  have e8 := ev_pos (⟪F.N 8, x 0 - x 1⟫ + cc * ⟪F.N 8, x 6 - x 1⟫) ⟪F.N 8, x 2 - x 1⟫ (h368_val 8 (by decide))
  have f2_rel : F.f 2 (x 6) - F.f 2 (x 1) = omega5 x * F.f 2 (x 1) := by
    have T := type24OfFac F
    have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
    have ev := fac_eval F 2 5
    rw [F.zero 2 5 (by decide), F.zero 2 0 (by decide), F.zero 2 2 (by decide)] at ev
    have hw : omega5 x * oblX6 x 5 = oblX0 x 5 + oblX2 x 5 - 1 := by
      unfold omega5; field_simp
    have : oblX6 x 5 * ((F.f 2 (x 6) - F.f 2 (x 1)) - omega5 x * F.f 2 (x 1)) = 0 := by
      linear_combination -ev - F.f 2 (x 1) * hw
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hc5.ne')
  have h2_0 : F.f 2 (x 1) * (cc * omega5 x - 1) < 0 := by
    have hmul : 1 / omega5 x * omega5 x < cc * omega5 x := mul_lt_mul_of_pos_right hw5 hC.2.2.1
    rw [one_div_mul_cancel hC.2.2.1.ne'] at hmul
    exact mul_neg_of_neg_of_pos (F.neg 2 1 (by decide)) (by linarith)
  have e2 := ev_neg (F.f 2 (x 1) * (cc * omega5 x - 1)) (-(F.f 2 (x 1))) h2_0
  have h7_0 : F.f 7 (x 1) * (omega3 x - cc) < 0 :=
    mul_neg_of_neg_of_pos (F.neg 7 1 (by decide)) (by linarith)
  have e7 := ev_neg (F.f 7 (x 1) * (omega3 x - cc)) (-(F.f 7 (x 1))) h7_0
  filter_upwards [e3, e4, e6, e8, e2, e7, ev_gt0] with η h3 h4 h6 h8 h2 h7 hη
  refine ⟨?_, ?_⟩
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · rw [inner_cap, ← F.inner_sub 3 0 1, ← F.inner_sub 3 2 1, ← F.inner_sub 3 6 1]; linarith
    · rw [inner_cap, F.zero 4 0 (by decide), F.zero 4 6 (by decide)]; linarith
    · rw [inner_cap, ← F.inner_sub 6 0 1, ← F.inner_sub 6 2 1, ← F.inner_sub 6 6 1]; linarith
    · rw [inner_cap, ← F.inner_sub 8 0 1, ← F.inner_sub 8 2 1, ← F.inner_sub 8 6 1]; linarith
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · rw [inner_cap, F.zero 0 0 (by decide), F.zero 0 1 (by decide), F.zero 0 2 (by decide)]
      simpa using mul_neg_of_pos_of_neg hcc_pos (F.neg 0 6 (by decide))
    · rw [inner_cap, F.zero 1 0 (by decide), F.zero 1 1 (by decide), F.zero 1 6 (by decide)]
      simpa using mul_neg_of_pos_of_neg hη (F.neg 1 2 (by decide))
    · rw [inner_cap, F.zero 2 0 (by decide), F.zero 2 2 (by decide), f2_rel]; linarith
    · rw [inner_cap, F.zero 5 1 (by decide), F.zero 5 2 (by decide), F.zero 5 6 (by decide)]
      simpa using F.neg 5 0 (by decide)
    · rw [inner_cap, F.zero 7 2 (by decide), F.zero 7 6 (by decide), f7_rel F]; linarith

/-- **FK3 (`wc_det3_rim`):** at `w0 = capView x 1 0 c_c` and rim `[0, 5, 2, 3, 6]`, edge `6 → 0`
(`d = x 0 - x 6`), `det3 E_i d w0` equals `(1 + c_c) * det24 x` times `(-b5, -(1 - b5), 1 - b3, b3)`. -/
theorem wc_det3_rim (x : Fin 7 → ℝ³) (hdet : det24 x ≠ 0) (cc : ℝ) :
    let w0 := capView x 1 0 cc
    let d := x 0 - x 6
    let b3 := oblX2 x 3
    let b5 := oblX2 x 5
    let K := (1 + cc) * det24 x
    Split.det3 (x 5 - x 0) d w0 = K * (-b5) ∧
    Split.det3 (x 2 - x 5) d w0 = K * (-(1 - b5)) ∧
    Split.det3 (x 3 - x 2) d w0 = K * (1 - b3) ∧
    Split.det3 (x 6 - x 3) d w0 = K * b3 := by
  intro w0 d b3 b5 K
  have hgen : ∀ E : ℝ³, Split.det3 E d w0 =
      (1 + cc) * Split.det3 E (x 0 - x 1) (x 6 - x 1) := by
    intro E
    dsimp only [d, w0, capView]
    simp only [Split.det3, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hobl : ∀ v : Fin 7,
      Split.det3 (x v - x 1) (x 0 - x 1) (x 6 - x 1) = -(oblX2 x v * det24 x) := by
    intro v
    have hb : oblX2 x v * det24 x = Split.det3 (x 0 - x 1) (x v - x 1) (x 6 - x 1) := by
      unfold oblX2
      rw [div_mul_cancel₀ _ hdet]
      simp only [vol3, Split.det3, PiLp.sub_apply]; ring
    have hs : Split.det3 (x v - x 1) (x 0 - x 1) (x 6 - x 1) =
        -Split.det3 (x 0 - x 1) (x v - x 1) (x 6 - x 1) := by
      simp only [Split.det3, PiLp.sub_apply]; ring
    linarith
  have h0 : Split.det3 (x 0 - x 1) (x 0 - x 1) (x 6 - x 1) = 0 := by
    simp only [Split.det3, PiLp.sub_apply]; ring
  have h6 : Split.det3 (x 6 - x 1) (x 0 - x 1) (x 6 - x 1) = 0 := by
    simp only [Split.det3, PiLp.sub_apply]; ring
  have h2 : Split.det3 (x 2 - x 1) (x 0 - x 1) (x 6 - x 1) = -det24 x := by
    simp only [det24, vol3, Split.det3, PiLp.sub_apply]; ring
  have hlin : ∀ u v : ℝ³, Split.det3 (u - v) (x 0 - x 1) (x 6 - x 1) =
      Split.det3 (u - x 1) (x 0 - x 1) (x 6 - x 1) -
      Split.det3 (v - x 1) (x 0 - x 1) (x 6 - x 1) := by
    intro u v; simp only [Split.det3, PiLp.sub_apply]; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hgen, hlin, hobl 5, h0]; dsimp only [b5, K]; ring
  · rw [hgen, hlin, h2, hobl 5]; dsimp only [b5, K]; ring
  · rw [hgen, hlin, hobl 3, h2]; dsimp only [b3, K]; ring
  · rw [hgen, hlin, h6, hobl 3]; dsimp only [b3, K]; ring

end Minimality.T24.WC
