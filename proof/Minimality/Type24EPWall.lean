module

public import Minimality.Type24RayQuad
public import Minimality.SplitLeaf
public import Minimality.EdgePlane
public import Minimality.GenericLeaves
public import Minimality.Type24HoleAtlas

/-!
# EU: Edge-Plane at the wall view `w0` of the hidden-cap cone

Merge Hydrogen Task EU.  Credit: Hydrogen Task EU (nopertz branch eu-work 05290fe3); spec nopert229 tools/genleaves/runs/epderive/SPEC.md
(EPDERIVE: fires on 650 of 1034 no-C points).  Uses `Minimality.Split.edgePlaneSpin` and `freeAt_of_edgePlane`.

Rim `0.4.6.2.5` (or its reverse `0.5.2.6.4` when negatively oriented at `w0`), edge `a = {6, 2}`
(index `2` in either orientation).  In the corner frame at vertex `1`:
`w0 := (1 + 2 ω5 + ω4 ω5) e_b + (1 + 2 ω4 + ω4 ω5) e_c`,
tilted to `w_eps := eps • (x 0 - x 1) + w0` for small `eps > 0`.

At `w0`, facet `126` is edge-on (`Split.det3 (x 2 - x 6) (x 1 - x 6) w0 = 0`), and `x 1` lies strictly on
the segment `[x 2, x 6]` in the projection along `w0` because both `e_b` and `e_c` coordinates of
`w0` are positive under `CbarIn x`.  Thus:
- `H0` (strict rim at `w0` for `m ≠ 1`, including `m = 3`) automatically implies strictness of
  vertex `1` on the four non-`a` edges at `w0`;
- `H1` (`0 < Split.det3 d (x 1 - X a) (x 0 - x 1)`) gives strictness of vertex `1` on edge `a` at `w_eps`
  for every `eps > 0`;
- `hidden_of_strictPentagon` gives `HiddenInTriangles` for both `x 1` and `x 3` at `w_eps`;
- `H2` and `H3` (vertex form of Edge-Plane with `(α, μ, s) = σ • (r₁ × r₂)`) persist to `w_eps` by
  continuity, yielding `FreeAt (univ.image x) (eps • (x 0 - x 1) + w0 x)` and `IsRupert (univ.image x)`.
-/

@[expose] public section

set_option autoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.T24.SAT Minimality.Split

namespace Minimality.T24.EU

/-! ## Perturbing a vertex solution of the Edge-Plane rows into a strict one -/

/-- Two tight rows (value `0`, nonzero coefficients `A`, distinct `Z`) and all other rows strictly positive:
a perturbation of `(s, α, μ)` makes every row strictly positive (the construction of
`Split.freeAt_of_edgePlane_vertex`, stated on the abstract row data). -/
theorem rows_of_vertex {k : ℕ} [NeZero k] (A Z : ZMod k → ℝ) (S : ZMod k → ZMod k → ℝ) (a : ZMod k)
    (s α μ : ℝ) (i₁ j₁ i₂ j₂ : ZMod k) (hA₁ : A i₁ ≠ 0) (hA₂ : A i₂ ≠ 0) (hZ : Z j₁ ≠ Z j₂)
    (ht₁ : (α + μ * Z j₁) * A i₁ + s * S i₁ j₁ = 0)
    (ht₂ : (α + μ * Z j₂) * A i₂ + s * S i₂ j₂ = 0)
    (hrows : ∀ i j : ZMod k, i ≠ a → (j = i ∨ j = i + 1) → (i, j) ≠ (i₁, j₁) → (i, j) ≠ (i₂, j₂) →
      0 < (α + μ * Z j) * A i + s * S i j) :
    ∃ s' α' μ' : ℝ, ∀ i j : ZMod k, i ≠ a → (j = i ∨ j = i + 1) →
      0 < (α' + μ' * Z j) * A i + s' * S i j := by
  classical
  have hz : Z j₂ - Z j₁ ≠ 0 := sub_ne_zero.2 fun h => hZ h.symm
  set dm := (1 / A i₂ - 1 / A i₁) / (Z j₂ - Z j₁) with hdm
  set da := 1 / A i₁ - Z j₁ * dm with hda
  have hq₁ : (da + dm * Z j₁) * A i₁ = 1 := by
    rw [hda]; field_simp; ring
  have hq₂ : (da + dm * Z j₂) * A i₂ = 1 := by
    have : da + dm * Z j₂ = 1 / A i₂ := by
      rw [hda, hdm]; field_simp; ring
    rw [this]; field_simp
  let J : ZMod k × Bool → ZMod k := fun t => if t.2 then t.1 + 1 else t.1
  obtain ⟨L, hL⟩ := exists_large (ι := ZMod k × Bool)
    (fun t => if t.1 = a then 1 else (α + μ * Z (J t)) * A t.1 + s * S t.1 (J t))
    (fun t => if t.1 = a then 0 else (da + dm * Z (J t)) * A t.1) (by
      rintro ⟨i, b⟩
      by_cases hi : i = a
      · left; simp [hi]
      · have hj : J (i, b) = i ∨ J (i, b) = i + 1 := by
          cases b
          · exact Or.inl rfl
          · exact Or.inr rfl
        simp only [hi, ite_false]
        by_cases h1 : (i, J (i, b)) = (i₁, j₁)
        · obtain ⟨e1, e2⟩ := Prod.mk.inj h1
          right
          rw [e2, e1]
          exact ⟨ht₁, by rw [hq₁]; norm_num⟩
        · by_cases h2 : (i, J (i, b)) = (i₂, j₂)
          · obtain ⟨e1, e2⟩ := Prod.mk.inj h2
            right
            rw [e2, e1]
            exact ⟨ht₂, by rw [hq₂]; norm_num⟩
          · left
            exact hrows i (J (i, b)) hi hj h1 h2)
  refine ⟨L * s, L * α + da, L * μ + dm, ?_⟩
  intro i j hi hj
  have hb : ∃ b, J (i, b) = j := by
    rcases hj with rfl | rfl
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩
  obtain ⟨b, rfl⟩ := hb
  have := hL (i, b)
  simp only [hi, ite_false] at this
  have e : ((L * α + da) + (L * μ + dm) * Z (J (i, b))) * A i + (L * s) * S i (J (i, b)) =
      L * ((α + μ * Z (J (i, b))) * A i + s * S i (J (i, b))) +
        (da + dm * Z (J (i, b))) * A i := by ring
  exact e ▸ this


/-! ## Pentagon `HiddenInTriangles` lemma (no diagonal non-degeneracy needed) -/

private theorem plucker_det3 (u1 u2 u3 v w : ℝ³) :
    Split.det3 u1 u2 w * Split.det3 u3 v w - Split.det3 u1 u3 w * Split.det3 u2 v w = Split.det3 u1 v w * Split.det3 u3 u2 w := by
  simp only [Split.det3]; ring

private lemma zmod5_add2_ne (i : ZMod 5) : i + 2 ≠ i := by revert i; decide
private lemma zmod5_add2_ne_add1 (i : ZMod 5) : i + 2 ≠ i + 1 := by revert i; decide
private lemma zmod5_ne_add2 (i : ZMod 5) : i ≠ i + 2 := by revert i; decide
private lemma zmod5_ne_add3 (i : ZMod 5) : i ≠ i + 2 + 1 := by revert i; decide

private lemma zmod5_add2_ne_add4 (i : ZMod 5) : i + 2 ≠ i + 4 := by revert i; decide
private lemma zmod5_add2_ne_add5 (i : ZMod 5) : i + 2 ≠ i + 4 + 1 := by revert i; decide
private lemma zmod5_add3_add2 (i : ZMod 5) : i + 3 + 2 = i := by revert i; decide
private lemma zmod5_add4_add1 (i : ZMod 5) : i + 4 + 1 = i := by revert i; decide
private lemma zmod5_add2_add1 (i : ZMod 5) : i + 2 + 1 = i + 3 := by revert i; decide

private theorem hidden_of_strictPentagon {p : ZMod 5 → ℝ³} {w y : ℝ³}
    (hcvx : ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 → 0 < Split.det3 (p (i + 1) - p i) (p j - p i) w)
    (hin : ∀ i : ZMod 5, 0 < Split.det3 (p (i + 1) - p i) (y - p i) w) :
    ∃ a b c : ZMod 5,
      0 < Split.det3 (p b - p a) (p c - p a) w ∧ 0 < Split.det3 (p b - p a) (y - p a) w ∧
      0 < Split.det3 (p c - p b) (y - p b) w ∧ 0 < Split.det3 (p a - p c) (y - p c) w := by
  set d : ZMod 5 → ℝ := fun i => Split.det3 (p (i + 2) - p i) (y - p i) w
  by_cases hneg : ∃ i : ZMod 5, d i < 0
  · obtain ⟨i, hi⟩ := hneg
    have h11 : (i + 1 + 1 : ZMod 5) = i + 2 := by ring
    have hin1 := hin (i + 1)
    rw [h11] at hin1
    refine ⟨i, i + 1, i + 2, hcvx i (i + 2) (zmod5_add2_ne i) (zmod5_add2_ne_add1 i),
      hin i, hin1, ?_⟩
    have hflip : Split.det3 (p i - p (i + 2)) (y - p (i + 2)) w = -d i := by
      dsimp [d]; simp only [Split.det3, PiLp.sub_apply]; ring
    rw [hflip]; linarith
  push Not at hneg
  have hzero_imp : ∀ i : ZMod 5, d i = 0 → 0 < d (i + 2) ∧ 0 < d (i + 3) := by
    intro i hi0
    have h1 := hcvx i (i + 2) (zmod5_add2_ne i) (zmod5_add2_ne_add1 i)
    have h2 : 0 < Split.det3 (p (i + 2) - p i) (p (i + 3) - p i) w := by
      have hcv := hcvx (i + 2) i (zmod5_ne_add2 i) (zmod5_ne_add3 i)
      rw [show Split.det3 (p (i + 2) - p i) (p (i + 3) - p i) w =
          Split.det3 (p (i + 2 + 1) - p (i + 2)) (p i - p (i + 2)) w by
        rw [show i + 2 + 1 = i + 3 by ring]
        simp only [Split.det3, PiLp.sub_apply]; ring]
      exact hcv
    have h3 := hin i
    have hpl := plucker_det3 (p (i + 2) - p i) (p (i + 1) - p i) (y - p i) (p (i + 3) - p i) w
    have hd0 : Split.det3 (p (i + 2) - p i) (y - p i) w = 0 := hi0
    rw [hd0, zero_mul, sub_zero] at hpl
    have hdet_eq : Split.det3 (p (i + 2) - p i) (p (i + 1) - p i) w =
        -Split.det3 (p (i + 1) - p i) (p (i + 2) - p i) w := by
      simp only [Split.det3]; ring
    have hy_eq : Split.det3 (y - p i) (p (i + 3) - p i) w = d (i + 3) := by
      dsimp [d]; rw [zmod5_add3_add2 i]
      simp only [Split.det3, PiLp.sub_apply]; ring
    have hy1_eq : Split.det3 (y - p i) (p (i + 1) - p i) w = -Split.det3 (p (i + 1) - p i) (y - p i) w := by
      simp only [Split.det3]; ring
    rw [hdet_eq, hy_eq, hy1_eq] at hpl
    have hmul : Split.det3 (p (i + 1) - p i) (p (i + 2) - p i) w * d (i + 3) =
        Split.det3 (p (i + 2) - p i) (p (i + 3) - p i) w * Split.det3 (p (i + 1) - p i) (y - p i) w := by
      linarith
    have hd3 : 0 < d (i + 3) := by
      have hrhs : 0 < Split.det3 (p (i + 2) - p i) (p (i + 3) - p i) w *
          Split.det3 (p (i + 1) - p i) (y - p i) w := mul_pos h2 h3
      rw [← hmul] at hrhs
      exact pos_of_mul_pos_right hrhs h1.le
    -- Similarly d (i + 2) > 0 via Plucker at p (i + 2):
    have h1' : 0 < Split.det3 (p (i + 2 + 1) - p (i + 2)) (p i - p (i + 2)) w :=
      hcvx (i + 2) i (zmod5_ne_add2 i) (zmod5_ne_add3 i)
    have h2' : 0 < Split.det3 (p (i + 4) - p (i + 2)) (p i - p (i + 2)) w := by
      have hcv := hcvx (i + 4) (i + 2) (zmod5_add2_ne_add4 i) (zmod5_add2_ne_add5 i)
      rw [zmod5_add4_add1 i] at hcv
      have : Split.det3 (p (i + 4) - p (i + 2)) (p i - p (i + 2)) w =
          Split.det3 (p i - p (i + 4)) (p (i + 2) - p (i + 4)) w := by
        simp only [Split.det3, PiLp.sub_apply]; ring
      rw [this]; exact hcv
    have h3' : 0 < Split.det3 (p (i + 2 + 1) - p (i + 2)) (y - p (i + 2)) w := hin (i + 2)
    have hpl' := plucker_det3 (p i - p (i + 2)) (p (i + 3) - p (i + 2)) (y - p (i + 2))
      (p (i + 4) - p (i + 2)) w
    have hd0' : Split.det3 (p i - p (i + 2)) (y - p (i + 2)) w = 0 := by
      have : Split.det3 (p i - p (i + 2)) (y - p (i + 2)) w = -d i := by
        dsimp [d]; simp only [Split.det3, PiLp.sub_apply]; ring
      rw [this, hi0, neg_zero]
    rw [hd0', zero_mul, sub_zero] at hpl'
    have hdet_eq' : Split.det3 (p i - p (i + 2)) (p (i + 3) - p (i + 2)) w =
        -Split.det3 (p (i + 2 + 1) - p (i + 2)) (p i - p (i + 2)) w := by
      rw [zmod5_add2_add1 i]; simp only [Split.det3]; ring
    have h4_eq : Split.det3 (y - p (i + 2)) (p (i + 4) - p (i + 2)) w = -d (i + 2) := by
      dsimp [d]; rw [show i + 2 + 2 = i + 4 by ring]
      simp only [Split.det3]; ring
    have h5_eq : Split.det3 (y - p (i + 2)) (p (i + 3) - p (i + 2)) w =
        -Split.det3 (p (i + 2 + 1) - p (i + 2)) (y - p (i + 2)) w := by
      rw [zmod5_add2_add1 i]; simp only [Split.det3]; ring
    have h6_eq : Split.det3 (p i - p (i + 2)) (p (i + 4) - p (i + 2)) w =
        -Split.det3 (p (i + 4) - p (i + 2)) (p i - p (i + 2)) w := by
      simp only [Split.det3]; ring
    rw [hdet_eq', h4_eq, h5_eq, h6_eq] at hpl'
    have hmul' : Split.det3 (p (i + 2 + 1) - p (i + 2)) (p i - p (i + 2)) w * d (i + 2) =
        Split.det3 (p (i + 4) - p (i + 2)) (p i - p (i + 2)) w *
          Split.det3 (p (i + 2 + 1) - p (i + 2)) (y - p (i + 2)) w := by
      linarith
    have hd2 : 0 < d (i + 2) := by
      have hrhs : 0 < Split.det3 (p (i + 4) - p (i + 2)) (p i - p (i + 2)) w *
          Split.det3 (p (i + 2 + 1) - p (i + 2)) (y - p (i + 2)) w := mul_pos h2' h3'
      rw [← hmul'] at hrhs
      exact pos_of_mul_pos_right hrhs h1'.le
    exact ⟨hd2, hd3⟩
  have hpair : ∃ i : ZMod 5, 0 < d i ∧ 0 < d (i + 3) := by
    by_cases h0 : d 0 = 0
    · obtain ⟨h2, h3⟩ := hzero_imp 0 h0
      by_cases h4 : d 4 = 0
      · obtain ⟨h1, _⟩ := hzero_imp 4 h4
        rw [show (4 + 2 : ZMod 5) = 1 from rfl] at h1
        exact ⟨3, by simpa using h3, h1⟩
      · exact ⟨4, lt_of_le_of_ne (hneg 4) (Ne.symm h4),
          by rw [show (4 + 3 : ZMod 5) = 0 + 2 from rfl]; exact h2⟩
    · have h0_pos : 0 < d 0 := lt_of_le_of_ne (hneg 0) (Ne.symm h0)
      by_cases h3 : d 3 = 0
      · obtain ⟨h0', h1⟩ := hzero_imp 3 h3
        by_cases h2 : d 2 = 0
        · obtain ⟨h4, _⟩ := hzero_imp 2 h2
          rw [show (3 + 3 : ZMod 5) = 1 from rfl] at h1
          rw [show (2 + 2 : ZMod 5) = 4 from rfl] at h4
          exact ⟨1, h1, h4⟩
        · rw [show (3 + 2 : ZMod 5) = 0 from rfl] at h0'
          exact ⟨2, lt_of_le_of_ne (hneg 2) (Ne.symm h2), h0'⟩
      · exact ⟨0, h0_pos, lt_of_le_of_ne (hneg 3) (Ne.symm h3)⟩
  obtain ⟨i, hi, hi3⟩ := hpair
  have hcv := hcvx (i + 2) i (zmod5_ne_add2 i) (zmod5_ne_add3 i)
  rw [zmod5_add2_add1 i] at hcv
  have hin2 := hin (i + 2)
  rw [zmod5_add2_add1 i] at hin2
  dsimp [d] at hi3
  rw [zmod5_add3_add2 i] at hi3
  refine ⟨i, i + 2, i + 3, ?_, hi, hin2, hi3⟩
  have : Split.det3 (p (i + 2) - p i) (p (i + 3) - p i) w =
      Split.det3 (p (i + 3) - p (i + 2)) (p i - p (i + 2)) w := by
    simp only [Split.det3, PiLp.sub_apply]; ring
  rw [this]; exact hcv

/-! ## Wall view `w0` and `EPWall` predicate -/

/-- The G-free wall view `w0 := (1 + 2 ω5 + ω4 ω5) e_b + (1 + 2 ω4 + ω4 ω5) e_c`. -/
noncomputable def w0 (x : Fin 7 → ℝ³) : ℝ³ :=
  T24.HC.capView x 0 (1 + 2 * omega5 x + omega4 x * omega5 x) (1 + 2 * omega4 x + omega4 x * omega5 x)

/-- Rim cycle `0.4.6.2.5` or its reverse `0.5.2.6.4`. -/
def epLab (rev : Bool) : ZMod 5 → Fin 7 :=
  if rev then ![0, 5, 2, 6, 4] else ![0, 4, 6, 2, 5]

theorem epLab_inj (rev : Bool) : Function.Injective (epLab rev) := by
  cases rev <;> intro i j h <;> fin_cases i <;> fin_cases j <;>
    first | rfl | exact absurd h (by decide)

/-- The 3D row vector `r(i, j) = (A_i, A_i Z_j, edgePlaneSpin ...)` for the Edge-Plane Lemma. -/
noncomputable def epRowVec (x : Fin 7 → ℝ³) (w : ℝ³) (lab : ZMod 5 → Fin 7) (a i j : ZMod 5) : ℝ³ :=
  let X : ZMod 5 → ℝ³ := fun k => x (lab k)
  let d := X (a + 1) - X a
  let A := Split.det3 (X (i + 1) - X i) d w
  let Z := ⟪X j - X a, w⟫
  let S := edgePlaneSpin X w a i j
  !₂[A, A * Z, S]

/-- **EU (`EPWall`).**  There is an orientation `rev : Bool` of the rim `0.4.6.2.5` (with edge `a = 2`,
i.e. `{6, 2}`), two tight rows `(i₁, j₁), (i₂, j₂)`, and a sign `σ ∈ {1, -1}` such that:
- `H0`: `x ∘ lab` is a strict rim at `w0 x` for all vertices `m ≠ 1` (including `m = 3`);
- `H1`: vertex `1` moves strictly inside edge `a` along `x 0 - x 1`;
- `H2`: `⟪d, w0 x⟫ ≠ 0` and the two tight rows are non-degenerate (`A i₁ ≠ 0`, `A i₂ ≠ 0`, `Z j₁ ≠ Z j₂`);
- `H3`: `(α, μ, s) = σ • (r(i₁, j₁) × r(i₂, j₂))` makes all six remaining rows strictly positive. -/
def EPWall {x : Fin 7 → ℝ³} (F : H21.S0xFac 9 s0x_S24 x) : Prop :=
  let _ := F
  ∃ (rev : Bool) (i₁ j₁ i₂ j₂ : ZMod 5) (σ : ℝ),
    (σ = 1 ∨ σ = -1) ∧
    let lab := epLab rev
    let X : ZMod 5 → ℝ³ := fun k => x (lab k)
    let a : ZMod 5 := 2
    let d := X (a + 1) - X a
    let w := w0 x
    -- H0: strict rim at w0 for all vertices m ≠ 1
    (∀ (m : Fin 7) (i : ZMod 5), m ≠ lab i → m ≠ lab (i + 1) → m ≠ 1 →
      0 < Split.det3 (X (i + 1) - X i) (x m - X i) w) ∧
    -- H1: vertex 1 strictly inside edge a for eps > 0
    0 < Split.det3 d (x 1 - X a) (x 0 - x 1) ∧
    -- H2: non-degeneracy
    ⟪d, w⟫ ≠ 0 ∧
    i₁ ≠ a ∧ (j₁ = i₁ ∨ j₁ = i₁ + 1) ∧
    i₂ ≠ a ∧ (j₂ = i₂ ∨ j₂ = i₂ + 1) ∧
    Split.det3 (X (i₁ + 1) - X i₁) d w ≠ 0 ∧
    Split.det3 (X (i₂ + 1) - X i₂) d w ≠ 0 ∧
    ⟪X j₁ - X a, w⟫ ≠ ⟪X j₂ - X a, w⟫ ∧
    -- H3: all six other rows strictly positive for (α, μ, s) = σ • (r₁ × r₂)
    let c := σ • cross (epRowVec x w lab a i₁ j₁) (epRowVec x w lab a i₂ j₂)
    ∀ i j : ZMod 5, i ≠ a → (j = i ∨ j = i + 1) → (i, j) ≠ (i₁, j₁) → (i, j) ≠ (i₂, j₂) →
      0 < (c 0 + c 1 * ⟪X j - X a, w⟫) * Split.det3 (X (i + 1) - X i) d w +
        c 2 * edgePlaneSpin X w a i j

/-! ## Persistence to `w_eps` and main theorems -/

private theorem eventually_pos_of_continuousAt {f : ℝ → ℝ} (hf : ContinuousAt f 0) (h0 : 0 < f 0) :
    ∀ᶠ eps in nhdsWithin 0 (Set.Ioi 0), 0 < f eps :=
  (hf.tendsto.mono_left nhdsWithin_le_nhds).eventually (lt_mem_nhds h0)

private theorem eventually_ne_of_continuousAt {f : ℝ → ℝ} (hf : ContinuousAt f 0) (h0 : f 0 ≠ 0) :
    ∀ᶠ eps in nhdsWithin 0 (Set.Ioi 0), f eps ≠ 0 :=
  (eventually_pos_of_continuousAt hf.abs (abs_pos.2 h0)).mono fun _ h => abs_pos.1 h

private theorem continuous_det3_right (a b : ℝ³) : Continuous (fun w : ℝ³ => Split.det3 a b w) := by
  simp only [Split.det3]
  fun_prop

private theorem continuous_w_eps (x : Fin 7 → ℝ³) :
    Continuous (fun eps : ℝ => eps • (x 0 - x 1) + w0 x) := by
  fun_prop

private theorem continuousAt_edgePlaneSpin {x : Fin 7 → ℝ³} {lab : ZMod 5 → Fin 7} {a i j : ZMod 5}
    {w₀ : ℝ³} (hD : ⟪x (lab (a + 1)) - x (lab a), w₀⟫ ≠ 0) :
    ContinuousAt (fun w : ℝ³ => edgePlaneSpin (fun k => x (lab k)) w a i j) w₀ := by
  unfold edgePlaneSpin
  have hc1 : Continuous (fun w : ℝ³ => Split.det3 (x (lab (i + 1)) - x (lab i))
      (cross w (x (lab j) - x (lab a))) w) := by
    simp only [Split.det3, cross_0, cross_1, cross_2]; fun_prop
  have hc2 : Continuous (fun w : ℝ³ => Split.det3 (x (lab (i + 1)) - x (lab i))
      (cross (x (lab (a + 1)) - x (lab a)) w) w) := by
    simp only [Split.det3, cross_0, cross_1, cross_2]; fun_prop
  exact hc1.continuousAt.add (((continuous_inner.comp (continuous_const.prodMk continuous_id)).continuousAt.div
    (continuous_inner.comp (continuous_const.prodMk continuous_id)).continuousAt hD).mul hc2.continuousAt)

private theorem continuousAt_epRowVec {x : Fin 7 → ℝ³} {lab : ZMod 5 → Fin 7} {a i j : ZMod 5}
    {w₀ : ℝ³} (hD : ⟪x (lab (a + 1)) - x (lab a), w₀⟫ ≠ 0) :
    ContinuousAt (fun w : ℝ³ => epRowVec x w lab a i j) w₀ := by
  unfold epRowVec
  have hA := (continuous_det3_right (x (lab (i + 1)) - x (lab i))
    (x (lab (a + 1)) - x (lab a))).continuousAt (x := w₀)
  have hZ : ContinuousAt (fun w : ℝ³ => ⟪x (lab j) - x (lab a), w⟫) w₀ := by fun_prop
  have hS := continuousAt_edgePlaneSpin (x := x) (lab := lab) (a := a) (i := i) (j := j) hD
  have hvec : Continuous (fun p : ℝ × ℝ × ℝ => !₂[p.1, p.2.1, p.2.2]) := by
    change Continuous (fun p : ℝ × ℝ × ℝ => WithLp.toLp 2 ![p.1, p.2.1, p.2.2])
    refine (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp ?_
    rw [continuous_pi_iff]
    intro k
    fin_cases k <;> simp <;> fun_prop
  exact hvec.continuousAt.comp (hA.prodMk ((hA.mul hZ).prodMk hS))

private theorem inner_epRow_cross_left (r₁ r₂ : ℝ³) (σ : ℝ) :
    (σ • cross r₁ r₂) 0 * r₁ 0 + (σ • cross r₁ r₂) 1 * r₁ 1 + (σ • cross r₁ r₂) 2 * r₁ 2 = 0 := by
  simp only [PiLp.smul_apply, smul_eq_mul, cross_0, cross_1, cross_2]; ring

private theorem inner_epRow_cross_right (r₁ r₂ : ℝ³) (σ : ℝ) :
    (σ • cross r₁ r₂) 0 * r₂ 0 + (σ • cross r₁ r₂) 1 * r₂ 1 + (σ • cross r₁ r₂) 2 * r₂ 2 = 0 := by
  simp only [PiLp.smul_apply, smul_eq_mul, cross_0, cross_1, cross_2]; ring

private lemma ep_h2_or_6 (rev : Bool) (i : ZMod 5) (hia : i ≠ 2) :
    (2 ≠ epLab rev i ∧ 2 ≠ epLab rev (i + 1)) ∨ (6 ≠ epLab rev i ∧ 6 ≠ epLab rev (i + 1)) := by
  revert i hia
  cases rev <;> decide

/-- Core of EU: for all small `eps > 0`, `w_eps = eps • (x 0 - x 1) + w0 x` is first-order free and an
Edge-Plane view (strict rim, hidden points, all rows strictly positive). -/
theorem epWall_core {x : Fin 7 → ℝ³} (F : H21.S0xFac 9 s0x_S24 x) (hC : CbarIn x) (h : EPWall F) :
    ∀ᶠ eps in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      FreeAt (univ.image x) (eps • (x 0 - x 1) + w0 x) ∧ Gen.EdgePlaneAny x := by
  obtain ⟨rev, i₁, j₁, i₂, j₂, σ, _, hH0, hH1, hD, hi1a, hj1, hi2a, hj2, hA1, hA2, hZ12, hH3⟩ := h
  set lab := epLab rev
  set X : ZMod 5 → ℝ³ := fun k => x (lab k)
  set a : ZMod 5 := 2
  set d := X (a + 1) - X a
  set w := w0 x
  set w_eps : ℝ → ℝ³ := fun eps => eps • (x 0 - x 1) + w
  have hw_cont : Continuous w_eps := continuous_w_eps x
  have hcb : 0 < 1 + 2 * omega5 x + omega4 x * omega5 x := by
    have := hC.2.1; have := hC.2.2.1; nlinarith
  have hcc : 0 < 1 + 2 * omega4 x + omega4 x * omega5 x := by
    have := hC.2.1; have := hC.2.2.1; nlinarith
  have hdecomp : (1 + 2 * omega5 x + omega4 x * omega5 x) • (x 2 - x 1) +
      (1 + 2 * omega4 x + omega4 x * omega5 x) • (x 6 - x 1) = w := by
    simp only [w, w0, T24.HC.capView, zero_smul, zero_add]
  have h1_other : ∀ i : ZMod 5, i ≠ a → 0 < Split.det3 (X (i + 1) - X i) (x 1 - X i) w := by
    intro i hia
    have hlin : ∀ A : ℝ³,
        (1 + 2 * omega5 x + omega4 x * omega5 x) * Split.det3 A (x 2 - x 1) w +
        (1 + 2 * omega4 x + omega4 x * omega5 x) * Split.det3 A (x 6 - x 1) w = 0 := by
      intro A
      have hdet0 : Split.det3 A w w = 0 := by simp only [Split.det3]; ring
      nth_rw 1 [← hdecomp] at hdet0
      simp only [Split.det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hdet0 ⊢
      linear_combination hdet0
    have hcomb : ∀ A p : ℝ³,
        ((1 + 2 * omega5 x + omega4 x * omega5 x) + (1 + 2 * omega4 x + omega4 x * omega5 x)) *
          Split.det3 A (x 1 - p) w =
        (1 + 2 * omega5 x + omega4 x * omega5 x) * Split.det3 A (x 2 - p) w +
        (1 + 2 * omega4 x + omega4 x * omega5 x) * Split.det3 A (x 6 - p) w := by
      intro A p
      have hsub := hlin A
      simp only [Split.det3, PiLp.sub_apply] at hsub ⊢
      linear_combination -hsub
    have hsum_pos : 0 < (1 + 2 * omega5 x + omega4 x * omega5 x) +
        (1 + 2 * omega4 x + omega4 x * omega5 x) := by linarith
    have hspec := hcomb (X (i + 1) - X i) (X i)
    have h2_ge : 0 ≤ (1 + 2 * omega5 x + omega4 x * omega5 x) * Split.det3 (X (i + 1) - X i) (x 2 - X i) w := by
      by_cases hm2 : (2 : Fin 7) = lab i ∨ (2 : Fin 7) = lab (i + 1)
      · rcases hm2 with h20 | h21
        · rw [show X i = x 2 by dsimp [X]; rw [← h20], sub_self]
          simp only [Split.det3, PiLp.zero_apply, mul_zero, zero_mul, sub_self, add_zero, le_refl]
        · rw [show X (i + 1) = x 2 by dsimp [X]; rw [← h21]]
          have : Split.det3 (x 2 - X i) (x 2 - X i) w = 0 := by
            simp only [Split.det3]; ring
          rw [this, mul_zero]
      · push Not at hm2
        exact (mul_pos hcb (hH0 2 i hm2.1 hm2.2 (by decide))).le
    have h6_ge : 0 ≤ (1 + 2 * omega4 x + omega4 x * omega5 x) * Split.det3 (X (i + 1) - X i) (x 6 - X i) w := by
      by_cases hm6 : (6 : Fin 7) = lab i ∨ (6 : Fin 7) = lab (i + 1)
      · rcases hm6 with h60 | h61
        · rw [show X i = x 6 by dsimp [X]; rw [← h60], sub_self]
          simp only [Split.det3, PiLp.zero_apply, mul_zero, zero_mul, sub_self, add_zero, le_refl]
        · rw [show X (i + 1) = x 6 by dsimp [X]; rw [← h61]]
          have : Split.det3 (x 6 - X i) (x 6 - X i) w = 0 := by
            simp only [Split.det3]; ring
          rw [this, mul_zero]
      · push Not at hm6
        exact (mul_pos hcc (hH0 6 i hm6.1 hm6.2 (by decide))).le
    have hstrict : 0 < (1 + 2 * omega5 x + omega4 x * omega5 x) * Split.det3 (X (i + 1) - X i) (x 2 - X i) w +
        (1 + 2 * omega4 x + omega4 x * omega5 x) * Split.det3 (X (i + 1) - X i) (x 6 - X i) w := by
      rcases ep_h2_or_6 rev i hia with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · linarith [mul_pos hcb (hH0 2 i h1 h2 (by decide))]
      · linarith [mul_pos hcc (hH0 6 i h1 h2 (by decide))]
    rw [← hspec] at hstrict
    exact pos_of_mul_pos_right hstrict hsum_pos.le
  -- 1. StrictRimN x (w_eps eps) lab eventually for eps > 0:
  have h1_a_w0 : Split.det3 d (x 1 - X a) w = 0 := by
    have hd_26 : (rev = false → d = x 2 - x 6 ∧ X a = x 6) ∧
        (rev = true → d = x 6 - x 2 ∧ X a = x 2) := by
      have h21 : (2 + 1 : ZMod 5) = 3 := rfl
      cases rev <;> simp [d, X, a, lab, epLab, h21]
    rcases Bool.dichotomy rev with rfl | rfl
    · obtain ⟨hd', hXa'⟩ := hd_26.1 rfl
      rw [hd', hXa', ← hdecomp]
      simp only [Split.det3, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]; ring
    · obtain ⟨hd', hXa'⟩ := hd_26.2 rfl
      rw [hd', hXa', ← hdecomp]
      simp only [Split.det3, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]; ring
  have hrim_ev : ∀ᶠ eps in nhdsWithin 0 (Set.Ioi 0), StrictRimN x (w_eps eps) lab := by
    have hother : ∀ᶠ eps in nhdsWithin 0 (Set.Ioi 0),
        ∀ (m : Fin 7) (i : ZMod 5), m ≠ lab i → m ≠ lab (i + 1) → ¬(m = 1 ∧ i = a) →
          0 < Split.det3 (X (i + 1) - X i) (x m - X i) (w_eps eps) := by
      refine Filter.eventually_all.2 fun m => Filter.eventually_all.2 fun i =>
        ev_imp fun hm0 => ev_imp fun hm1 => ev_imp fun hnot => ?_
      refine eventually_pos_of_continuousAt ((continuous_det3_right _ _).comp hw_cont).continuousAt ?_
      simp only [w_eps, zero_smul, zero_add]
      by_cases hm_one : m = 1
      · subst hm_one
        have hia : i ≠ a := fun h => hnot ⟨rfl, h⟩
        exact h1_other i hia
      · exact hH0 m i hm0 hm1 hm_one
    filter_upwards [hother, self_mem_nhdsWithin] with eps heps (heps0 : 0 < eps)
    intro m i hm0 hm1
    by_cases h1a : m = 1 ∧ i = a
    · rcases h1a with ⟨rfl, rfl⟩
      have hdet_eq : Split.det3 d (x 1 - X a) (w_eps eps) =
          eps * Split.det3 d (x 1 - X a) (x 0 - x 1) + Split.det3 d (x 1 - X a) w := by
        dsimp [w_eps]
        simp only [Split.det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
      rw [hdet_eq, h1_a_w0, add_zero]
      exact mul_pos heps0 hH1
    · exact heps m i hm0 hm1 h1a
  -- 2. HiddenInTriangles x (w_eps eps) lab from StrictRimN:
  have hhid_ev : ∀ᶠ eps in nhdsWithin 0 (Set.Ioi 0), HiddenInTriangles x (w_eps eps) lab := by
    filter_upwards [hrim_ev] with eps hrim
    intro m hm
    have hcvx : ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
        0 < Split.det3 (X (i + 1) - X i) (X j - X i) (w_eps eps) := by
      intro i j hji hji1
      exact hrim (lab j) i (fun h => hji (epLab_inj rev h)) (fun h => hji1 (epLab_inj rev h))
    have hin : ∀ i : ZMod 5, 0 < Split.det3 (X (i + 1) - X i) (x m - X i) (w_eps eps) :=
      fun i => hrim m i (hm i) (hm (i + 1))
    obtain ⟨p0, p1, p2, h012, h01y, h12y, h20y⟩ := hidden_of_strictPentagon hcvx hin
    exact ⟨X p0, mem_image_of_mem x (mem_univ _), X p1, mem_image_of_mem x (mem_univ _),
      X p2, mem_image_of_mem x (mem_univ _), h012, h01y, h12y, h20y⟩
  -- 3. Edge-Plane hypotheses H2, H3 persist to w_eps eps by continuity:
  have hD_ev : ∀ᶠ eps in nhdsWithin 0 (Set.Ioi 0), ⟪d, w_eps eps⟫ ≠ 0 :=
    eventually_ne_of_continuousAt (by fun_prop) (by simpa [w_eps] using hD)
  have hA1_ev : ∀ᶠ eps in nhdsWithin 0 (Set.Ioi 0),
      Split.det3 (X (i₁ + 1) - X i₁) d (w_eps eps) ≠ 0 :=
    eventually_ne_of_continuousAt ((continuous_det3_right _ _).comp hw_cont).continuousAt
      (by simpa [w_eps] using hA1)
  have hA2_ev : ∀ᶠ eps in nhdsWithin 0 (Set.Ioi 0),
      Split.det3 (X (i₂ + 1) - X i₂) d (w_eps eps) ≠ 0 :=
    eventually_ne_of_continuousAt ((continuous_det3_right _ _).comp hw_cont).continuousAt
      (by simpa [w_eps] using hA2)
  have hZ12_ev : ∀ᶠ eps in nhdsWithin 0 (Set.Ioi 0),
      ⟪X j₁ - X a, w_eps eps⟫ ≠ ⟪X j₂ - X a, w_eps eps⟫ :=
    (eventually_ne_of_continuousAt
      (f := fun eps : ℝ => ⟪X j₁ - X a, w_eps eps⟫ - ⟪X j₂ - X a, w_eps eps⟫)
      (by fun_prop) (by simpa [w_eps] using sub_ne_zero.2 hZ12)).mono fun _ h =>
      sub_ne_zero.1 h
  let c_eps : ℝ → ℝ³ := fun eps =>
    σ • cross (epRowVec x (w_eps eps) lab a i₁ j₁) (epRowVec x (w_eps eps) lab a i₂ j₂)
  have hw0_eq : w_eps 0 = w := by simp [w_eps]
  have hD0 : ⟪x (lab (a + 1)) - x (lab a), w_eps 0⟫ ≠ 0 := by rw [hw0_eq]; exact hD
  have hc_cont : ∀ i j : ZMod 5, ContinuousAt (fun eps : ℝ =>
      ((c_eps eps) 0 + (c_eps eps) 1 * ⟪X j - X a, w_eps eps⟫) *
          Split.det3 (X (i + 1) - X i) d (w_eps eps) +
        (c_eps eps) 2 * edgePlaneSpin X (w_eps eps) a i j) 0 := by
    intro i j
    have hr1 : ContinuousAt (fun eps : ℝ => epRowVec x (w_eps eps) lab a i₁ j₁) 0 :=
      (continuousAt_epRowVec (x := x) (lab := lab) (a := a) (i := i₁) (j := j₁) hD0).comp
        hw_cont.continuousAt
    have hr2 : ContinuousAt (fun eps : ℝ => epRowVec x (w_eps eps) lab a i₂ j₂) 0 :=
      (continuousAt_epRowVec (x := x) (lab := lab) (a := a) (i := i₂) (j := j₂) hD0).comp
        hw_cont.continuousAt
    have hc_at : ContinuousAt c_eps 0 := by
      dsimp [c_eps]
      refine ContinuousAt.const_smul ?_ σ
      have hcr : Continuous (fun p : ℝ³ × ℝ³ => cross p.1 p.2) := by
        change Continuous (fun p : ℝ³ × ℝ³ => WithLp.toLp 2 (fun k => (cross p.1 p.2) k))
        refine (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp (continuous_pi fun k => ?_)
        fin_cases k <;> fun_prop
      exact hcr.continuousAt.comp (hr1.prodMk hr2)
    have hc0 : ContinuousAt (fun eps => (c_eps eps) 0) 0 :=
      (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 0).continuousAt.comp hc_at
    have hc1 : ContinuousAt (fun eps => (c_eps eps) 1) 0 :=
      (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 1).continuousAt.comp hc_at
    have hc2 : ContinuousAt (fun eps => (c_eps eps) 2) 0 :=
      (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2).continuousAt.comp hc_at
    have hZ_at : ContinuousAt (fun eps => ⟪X j - X a, w_eps eps⟫) 0 := by fun_prop
    have hA_at : ContinuousAt (fun eps => Split.det3 (X (i + 1) - X i) d (w_eps eps)) 0 :=
      ((continuous_det3_right _ _).comp hw_cont).continuousAt
    have hS_at : ContinuousAt (fun eps => edgePlaneSpin X (w_eps eps) a i j) 0 :=
      (continuousAt_edgePlaneSpin (x := x) (lab := lab) (a := a) (i := i) (j := j) hD0).comp
        hw_cont.continuousAt
    exact ((hc0.add (hc1.mul hZ_at)).mul hA_at).add (hc2.mul hS_at)
  have hrows_ev : ∀ᶠ eps in nhdsWithin 0 (Set.Ioi 0),
      ∀ i j : ZMod 5, i ≠ a → (j = i ∨ j = i + 1) → (i, j) ≠ (i₁, j₁) → (i, j) ≠ (i₂, j₂) →
        0 < ((c_eps eps) 0 + (c_eps eps) 1 * ⟪X j - X a, w_eps eps⟫) *
            Split.det3 (X (i + 1) - X i) d (w_eps eps) +
          (c_eps eps) 2 * edgePlaneSpin X (w_eps eps) a i j := by
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      ev_imp fun hia => ev_imp fun hj => ev_imp fun hn1 => ev_imp fun hn2 => ?_
    refine eventually_pos_of_continuousAt (hc_cont i j) ?_
    simpa [c_eps, hw0_eq] using hH3 i j hia hj hn1 hn2
  have hall := hrim_ev.and (hhid_ev.and (hD_ev.and (hA1_ev.and (hA2_ev.and (hZ12_ev.and hrows_ev)))))
  refine hall.mono fun eps ⟨hrim, hhid, hDe, hA1e, hA2e, hZ12e, hrowse⟩ => ?_
  have ht₁ : (c_eps eps 0 + c_eps eps 1 * ⟪X j₁ - X a, w_eps eps⟫) *
        Split.det3 (X (i₁ + 1) - X i₁) (X (a + 1) - X a) (w_eps eps) +
      c_eps eps 2 * edgePlaneSpin X (w_eps eps) a i₁ j₁ = 0 := by
    have h := inner_epRow_cross_left (epRowVec x (w_eps eps) lab a i₁ j₁)
      (epRowVec x (w_eps eps) lab a i₂ j₂) σ
    dsimp [c_eps]
    dsimp [epRowVec] at h ⊢
    linarith
  have ht₂ : (c_eps eps 0 + c_eps eps 1 * ⟪X j₂ - X a, w_eps eps⟫) *
        Split.det3 (X (i₂ + 1) - X i₂) (X (a + 1) - X a) (w_eps eps) +
      c_eps eps 2 * edgePlaneSpin X (w_eps eps) a i₂ j₂ = 0 := by
    have h := inner_epRow_cross_right (epRowVec x (w_eps eps) lab a i₁ j₁)
      (epRowVec x (w_eps eps) lab a i₂ j₂) σ
    dsimp [c_eps]
    dsimp [epRowVec] at h ⊢
    linarith
  obtain ⟨s', α', μ', hr⟩ := rows_of_vertex
    (fun i => Split.det3 (X (i + 1) - X i) (X (a + 1) - X a) (w_eps eps))
    (fun j => ⟪X j - X a, w_eps eps⟫) (fun i j => edgePlaneSpin X (w_eps eps) a i j) a
    (c_eps eps 2) (c_eps eps 0) (c_eps eps 1) i₁ j₁ i₂ j₂ hA1e hA2e hZ12e ht₁ ht₂ hrowse
  have hD' : ⟪x (lab (a + 1)) - x (lab a), w_eps eps⟫ ≠ 0 := hDe
  exact ⟨freeAt_of_edgePlane (by decide) x (w_eps eps) lab (epLab_inj rev) hrim hhid a s' α' μ' hD' hr,
    5, inferInstance, lab, w_eps eps, a, s', α', μ', by norm_num, epLab_inj rev, hrim, hhid, hD', hr⟩

/-- **EU(i), free view on the ray.**  Under `CbarIn x` and `EPWall F`, `w_eps = eps • (x 0 - x 1) + w0 x`
is first-order free for all sufficiently small `eps > 0`. -/
theorem freeAt_of_epWall {x : Fin 7 → ℝ³} (F : H21.S0xFac 9 s0x_S24 x) (hC : CbarIn x) (h : EPWall F) :
    ∀ᶠ eps in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      FreeAt (univ.image x) (eps • (x 0 - x 1) + w0 x) :=
  (epWall_core F hC h).mono fun _ h => h.1

/-- **EU(iii), the Edge-Plane leaf.**  `EPWall F` (with `CbarIn x`) gives `Gen.EdgePlaneAny x`: the same rim,
edge and certificate at some `w_eps`, strictified by `rows_of_vertex`. -/
theorem edgePlaneAny_of_epWall {x : Fin 7 → ℝ³} (F : H21.S0xFac 9 s0x_S24 x) (hC : CbarIn x)
    (h : EPWall F) : Gen.EdgePlaneAny x := by
  obtain ⟨eps, he⟩ := @Filter.Eventually.exists _ _ _ (nhdsWithin_Ioi_neBot (le_refl (0 : ℝ)))
    (epWall_core F hC h)
  exact he.2

/-- Atlas contrapositive: at a hole point the Edge-Plane wall certificate `EPWall` fails. -/
theorem holeLeaf_not_epWall {x : Fin 7 → ℝ³} (F : H21.S0xFac 9 s0x_S24 x) (h : HoleLeaf x F) :
    ¬ EPWall F :=
  fun hE => h.2.2.2.2.2.2 (edgePlaneAny_of_epWall F h.1 hE)

/-- **EU(ii), Rupert from `EPWall`.** -/
theorem isRupert_of_epWall {x : Fin 7 → ℝ³} (F : H21.S0xFac 9 s0x_S24 x) (hC : CbarIn x) (hEP : EPWall F) :
    IsRupert (univ.image x) := by
  have ⟨rev, _, _, _, _, _, _, _, _, hD, _⟩ := hEP
  set d := x (epLab rev (2 + 1)) - x (epLab rev 2)
  have hne_ev : ∀ᶠ eps in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
      eps • (x 0 - x 1) + w0 x ≠ 0 := by
    have hDe := eventually_ne_of_continuousAt
      (f := fun eps : ℝ => ⟪d, eps • (x 0 - x 1) + w0 x⟫) (by fun_prop) (by simpa using hD)
    exact show ∀ᶠ eps in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)), eps • (x 0 - x 1) + w0 x ≠ 0 from
      hDe.mono fun eps hDe' h0 => by rw [h0, inner_zero_right] at hDe'; exact hDe' rfl
  have hand : ∀ᶠ eps in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      FreeAt (univ.image x) (eps • (x 0 - x 1) + w0 x) ∧ eps • (x 0 - x 1) + w0 x ≠ 0 :=
    (freeAt_of_epWall F hC hEP).and hne_ev
  obtain ⟨eps, hfree, hne⟩ :=
    @Filter.Eventually.exists _ _ _ (nhdsWithin_Ioi_neBot (le_refl (0 : ℝ))) hand
  exact hfree.isRupert hne

end Minimality.T24.EU
