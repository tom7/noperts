import Minimality.Type24A1Tie

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.A1

open Minimality Minimality.H21 Minimality.H24.SAT Minimality.T24.SAT Minimality.T24.RCell
  Minimality.LexCell Minimality.Split Minimality.T24.M4 Minimality.T24.A7 Minimality.T24.A8
  Minimality.T24.A10 Minimality.T24.Q24 Minimality.T24 Minimality.GenQuad

/-! ### Coordinates in the vertex-5 frame -/

/-- The six sign conditions of `FrontDet` on the four determinants `A = det3 (p-q) (r-s) b`,
`B = det3 (s-q) (r-s) b`, `C = -det3 (p-q) (s-q) b`, `D = det3 (p-q) (r-s) (s-q)`. -/
def FrontDetR (A B C D : ℝ) : Prop :=
  (0 < A ∧ 0 ≤ B ∧ B ≤ A ∧ 0 ≤ C ∧ C ≤ A ∧ D < 0) ∨
  (A < 0 ∧ B ≤ 0 ∧ A ≤ B ∧ C ≤ 0 ∧ A ≤ C ∧ 0 < D)

theorem FrontDetR.scale {A B C D k l : ℝ} (h : FrontDetR A B C D) (hk : 0 < k) (hl : 0 < l) :
    FrontDetR (k * A) (k * B) (k * C) (l * D) := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩
  · exact Or.inl ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  · exact Or.inr ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- Coordinates `P = (y1, y2, y3)` against the frame `e1 e2 e3`. -/
def phi (e1 e2 e3 : ℝ³) (P : ℝ × ℝ × ℝ) : ℝ³ := P.1 • e1 + P.2.1 • e2 + P.2.2 • e3

/-- The determinant of three coordinate triples. -/
def d3c (a b c : ℝ × ℝ × ℝ) : ℝ :=
  (a.2.1 * b.2.2 - a.2.2 * b.2.1) * c.1 + (a.2.2 * b.1 - a.1 * b.2.2) * c.2.1 +
    (a.1 * b.2.1 - a.2.1 * b.1) * c.2.2

theorem det3_phi (e1 e2 e3 : ℝ³) (a b c : ℝ × ℝ × ℝ) :
    Split.det3 (phi e1 e2 e3 a) (phi e1 e2 e3 b) (phi e1 e2 e3 c) =
      Split.det3 e1 e2 e3 * d3c a b c := by
  simp only [phi, d3c, Split.det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

theorem det3_smul_right (a b c : ℝ³) (μ : ℝ) :
    Split.det3 a b (μ • c) = μ * Split.det3 a b c := by
  simp only [Split.det3, PiLp.smul_apply, smul_eq_mul]; ring

theorem phi_sub (e1 e2 e3 : ℝ³) (a b : ℝ × ℝ × ℝ) :
    phi e1 e2 e3 (a - b) = phi e1 e2 e3 a - phi e1 e2 e3 b := by
  simp only [phi, Prod.fst_sub, Prod.snd_sub, sub_smul]; abel

/-- `FrontDet` from a coordinate certificate in a positively oriented frame at the base point `z`. -/
theorem frontDet_of_coords {z e1 e2 e3 p q r s b : ℝ³} (hΔ : 0 < Split.det3 e1 e2 e3)
    {μ : ℝ} (hμ : 0 < μ) {P Q R S B : ℝ × ℝ × ℝ}
    (hp : p = z + phi e1 e2 e3 P) (hq : q = z + phi e1 e2 e3 Q)
    (hr : r = z + phi e1 e2 e3 R) (hs : s = z + phi e1 e2 e3 S)
    (hb : b = μ • phi e1 e2 e3 B)
    (h : FrontDetR (d3c (P - Q) (R - S) B) (d3c (S - Q) (R - S) B) (-d3c (P - Q) (S - Q) B)
      (d3c (P - Q) (R - S) (S - Q))) : FrontDet p q r s b := by
  have h' := h.scale (mul_pos hμ hΔ) hΔ
  have e1' : p - q = phi e1 e2 e3 (P - Q) := by rw [hp, hq, phi_sub]; abel
  have e2' : r - s = phi e1 e2 e3 (R - S) := by rw [hr, hs, phi_sub]; abel
  have e3' : s - q = phi e1 e2 e3 (S - Q) := by rw [hs, hq, phi_sub]; abel
  have hA : Split.det3 (p - q) (r - s) b =
      μ * Split.det3 e1 e2 e3 * d3c (P - Q) (R - S) B := by
    rw [e1', e2', hb, det3_smul_right, det3_phi]; ring
  have hB : Split.det3 (s - q) (r - s) b =
      μ * Split.det3 e1 e2 e3 * d3c (S - Q) (R - S) B := by
    rw [e3', e2', hb, det3_smul_right, det3_phi]; ring
  have hE : Split.det3 (p - q) (s - q) b =
      μ * Split.det3 e1 e2 e3 * d3c (P - Q) (S - Q) B := by
    rw [e1', e3', hb, det3_smul_right, det3_phi]; ring
  have hD : Split.det3 (p - q) (r - s) (s - q) =
      Split.det3 e1 e2 e3 * d3c (P - Q) (R - S) (S - Q) := by
    rw [e1', e2', e3', det3_phi]
  unfold FrontDet
  rw [hA, hB, hE, hD]
  unfold FrontDetR at h'
  simp only [mul_neg] at h'
  exact h'

/-! ### Frame points and pure-real `FrontDetR` lemmas -/

def V2 : ℝ × ℝ × ℝ := (1, 0, 0)
def V0 : ℝ × ℝ × ℝ := (0, 1, 0)
def V3 : ℝ × ℝ × ℝ := (0, 0, 1)
def V5 : ℝ × ℝ × ℝ := (0, 0, 0)
def V4 (p q : ℝ) : ℝ × ℝ × ℝ := (0, p, q)
def V6 (a b c : ℝ) : ℝ × ℝ × ℝ := (a, b, c)
def V1 (a b c : ℝ) : ℝ × ℝ × ℝ := (a, b, c)
def B26 (a : ℝ) : ℝ × ℝ × ℝ := (a - 1, -a, 0)
def B25 : ℝ × ℝ × ℝ := (-1, 0, 0)

theorem Bnn {t p4 q4 c61 c62 c63 : ℝ} (ht : 0 < t) (hp : 0 < p4) (hq : 1 ≤ q4)
    (h61 : 0 < c61) (f4a : (p4 - 1) * c63 < q4 * (c61 + c62 - 1))
    (hG : t * p4 * (c63 - 1) ≤ (q4 - 1) * ((t + 1) * c61 + t * c62)) :
    t * p4 * c63 ≤ q4 * ((t + 1) * c61 + t * c62) := by
  rcases le_total c63 q4 with h | h
  · nlinarith [mul_lt_mul_of_pos_left f4a ht, mul_pos h61 (by linarith : (0:ℝ) < q4), mul_nonneg ht.le (sub_nonneg.2 h)]
  · rcases eq_or_lt_of_le h with h' | h'
    · nlinarith [mul_lt_mul_of_pos_left f4a ht, mul_pos h61 (by linarith : (0:ℝ) < q4)]
    · have hK : t * p4 ≤ (t + 1) * c61 + t * c62 := by
        by_contra hK
        push Not at hK
        nlinarith [mul_pos ht hp, mul_nonneg (sub_nonneg.2 hq) (sub_nonneg.2 hK.le), mul_pos (mul_pos ht hp) (sub_pos.2 h')]
      nlinarith

theorem fd_f2356_26 {a5 c61 c62 c63 : ℝ} (ha5 : 1 < a5) (h61 : 0 < c61) (h62 : 0 < c62)
    (h63 : 0 < c63) (h13 : 1 < c61 + c63) :
    FrontDetR (d3c (V2 - V3) (V5 - V6 c61 c62 c63) (B26 a5))
      (d3c (V6 c61 c62 c63 - V3) (V5 - V6 c61 c62 c63) (B26 a5))
      (-d3c (V2 - V3) (V6 c61 c62 c63 - V3) (B26 a5))
      (d3c (V2 - V3) (V5 - V6 c61 c62 c63) (V6 c61 c62 c63 - V3)) := by
  unfold FrontDetR
  simp only [d3c, V2, V3, V5, V6, B26, Prod.fst_sub, Prod.snd_sub]
  right
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith [mul_pos h61 (sub_pos.2 ha5), mul_pos h62 (sub_pos.2 ha5), mul_pos h63 (sub_pos.2 ha5)]

theorem fd_t26d {a5 p4 q4 c61 c62 c63 : ℝ} (ha5 : 1 < a5) (hp : 0 < p4) (hq : 1 ≤ q4)
    (h61 : 0 < c61) (h62 : 0 < c62)
    (f4a : (p4 - 1) * c63 < q4 * (c61 + c62 - 1))
    (hG : 0 ≤ (q4 - 1) * (a5 * c61 + (a5 - 1) * c62) - (a5 - 1) * p4 * (c63 - 1)) :
    FrontDetR (d3c (V3 - V6 c61 c62 c63) (V5 - V4 p4 q4) (B26 a5))
      (d3c (V4 p4 q4 - V6 c61 c62 c63) (V5 - V4 p4 q4) (B26 a5))
      (-d3c (V3 - V6 c61 c62 c63) (V4 p4 q4 - V6 c61 c62 c63) (B26 a5))
      (d3c (V3 - V6 c61 c62 c63) (V5 - V4 p4 q4) (V4 p4 q4 - V6 c61 c62 c63)) := by
  unfold FrontDetR
  simp only [d3c, V3, V4, V5, V6, B26, Prod.fst_sub, Prod.snd_sub]
  left
  have hq' : 0 ≤ q4 - 1 := by linarith
  have ht : 0 < a5 - 1 := sub_pos.2 ha5
  have hB := Bnn ht hp hq h61 f4a (by
    have e : a5 - 1 + 1 = a5 := by ring
    rw [e]; linarith)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first | nlinarith [mul_pos hp ht, mul_pos h61 ht, mul_pos h62 ht, mul_pos h61 hp, mul_pos h62 hp, mul_nonneg hq' ht.le, mul_pos ht hp]

theorem fd_t26c {a5 p4 q4 c61 c62 c63 : ℝ} (ha5 : 1 < a5) (hp : 0 < p4) (hq : 1 ≤ q4)
    (h62 : 0 < c62)
    (f4a : (p4 - 1) * c63 < q4 * (c61 + c62 - 1)) (f7c : c62 * (q4 - 1) < p4 * (c61 + c63 - 1))
    (hG : 0 ≤ (q4 - 1) * (a5 * c61 + (a5 - 1) * c62) - (a5 - 1) * p4 * (c63 - 1)) :
    FrontDetR (d3c (V3 - V6 c61 c62 c63) (V2 - V4 p4 q4) (B26 a5))
      (d3c (V4 p4 q4 - V6 c61 c62 c63) (V2 - V4 p4 q4) (B26 a5))
      (-d3c (V3 - V6 c61 c62 c63) (V4 p4 q4 - V6 c61 c62 c63) (B26 a5))
      (d3c (V3 - V6 c61 c62 c63) (V2 - V4 p4 q4) (V4 p4 q4 - V6 c61 c62 c63)) := by
  unfold FrontDetR
  simp only [d3c, V2, V3, V4, V6, B26, Prod.fst_sub, Prod.snd_sub]
  left
  have hq' : 0 ≤ q4 - 1 := by linarith
  have ht : 0 < a5 - 1 := sub_pos.2 ha5
  have h13 : 0 < c61 + c63 - 1 := by nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first | nlinarith [mul_pos hp ht, mul_pos h62 ht, mul_pos h62 hp, mul_nonneg hq' ht.le, mul_pos ht hp, mul_pos (by linarith : (0:ℝ) < a5) h13]

/-! ### Frame facts from the facets -/

theorem eq_of_frame {y z e1 e2 e3 : ℝ³} (P : ℝ × ℝ × ℝ)
    (h : y - z = P.1 • e1 + P.2.1 • e2 + P.2.2 • e3) : y = z + phi e1 e2 e3 P := by
  simp only [phi]; rw [← h]; abel

/-- Affine evaluation of a facet functional in the vertex-5 frame. -/
theorem fval {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : Fin 9) {v : Fin 7} {c1 c2 c3 : ℝ}
    (h : x v - x 5 = c1 • (x 2 - x 5) + c2 • (x 0 - x 5) + c3 • (x 3 - x 5)) :
    F.f t (x v) = F.f t (x 5) + c1 * (F.f t (x 2) - F.f t (x 5)) +
      c2 * (F.f t (x 0) - F.f t (x 5)) + c3 * (F.f t (x 3) - F.f t (x 5)) := by
  have := congrArg (fun w => ⟪F.N t, w⟫) h
  simp only [inner_add_right, inner_smul_right, F.inner_sub] at this
  linarith

/-- Facet facts about `x4`, `x6` in the vertex-5 frame: `7` at `x4` (equivalently `8` at `x2`),
`046` at `x3`, and `046` at `x2`. -/
theorem x46_facts {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {p4 q4 c61 c62 c63 : ℝ}
    (hx4 : x 4 - x 5 = p4 • (x 0 - x 5) + q4 • (x 3 - x 5))
    (hx6 : x 6 - x 5 = c61 • (x 2 - x 5) + c62 • (x 0 - x 5) + c63 • (x 3 - x 5))
    (hc61 : 0 < c61) (hc62 : 0 < c62) (hq4 : 0 < q4) :
    c62 * (q4 - 1) < p4 * (c61 + c63 - 1) ∧ 1 < p4 + q4 ∧
      (p4 - 1) * c63 < q4 * (c61 + c62 - 1) := by
  have hx4' : x 4 - x 5 = (0:ℝ) • (x 2 - x 5) + p4 • (x 0 - x 5) + q4 • (x 3 - x 5) := by
    rw [hx4]; module
  -- facet 7
  have a4 := fval F 7 hx4'
  have a6 := fval F 7 hx6
  rw [F.zero 7 6 (by decide), F.zero 7 2 (by decide), F.zero 7 3 (by decide)] at a6
  rw [F.zero 7 2 (by decide), F.zero 7 3 (by decide)] at a4
  have w7 := F.neg 7 5 (by decide)
  have h7 := F.neg 7 0 (by decide)
  have n7 := F.neg 7 4 (by decide)
  have k7 : c62 * F.f 7 (x 4) = F.f 7 (x 5) * (c62 * (1 - q4) + p4 * (c61 + c63 - 1)) := by
    linear_combination c62 * a4 - p4 * a6
  have f7c : c62 * (q4 - 1) < p4 * (c61 + c63 - 1) := by
    by_contra hK
    push Not at hK
    nlinarith [mul_pos hc62 (neg_pos.2 n7), mul_nonneg (neg_nonneg.2 w7.le) (sub_nonneg.2 hK)]
  -- facet 4
  have b4 := fval F 4 hx4'
  have b6 := fval F 4 hx6
  rw [F.zero 4 0 (by decide)] at b4 b6
  rw [F.zero 4 4 (by decide)] at b4
  rw [F.zero 4 6 (by decide)] at b6
  have w4 := F.neg 4 5 (by decide)
  have g3 := F.neg 4 3 (by decide)
  have g2 := F.neg 4 2 (by decide)
  have f4b : 1 < p4 + q4 := by
    by_contra hK
    push Not at hK
    have : q4 * F.f 4 (x 3) = F.f 4 (x 5) * (p4 + q4 - 1) := by linear_combination -b4
    nlinarith [mul_pos hq4 (neg_pos.2 g3), mul_nonneg (neg_nonneg.2 w4.le) (sub_nonneg.2 hK)]
  have k4 : q4 * c61 * F.f 4 (x 2) =
      F.f 4 (x 5) * (q4 * (c61 + c62 - 1) - (p4 - 1) * c63) := by
    linear_combination (-q4) * b6 + c63 * b4
  have f4a : (p4 - 1) * c63 < q4 * (c61 + c62 - 1) := by
    by_contra hK
    push Not at hK
    nlinarith [mul_pos (mul_pos hq4 hc61) (neg_pos.2 g2), mul_nonneg (neg_nonneg.2 w4.le) (sub_nonneg.2 hK)]
  exact ⟨f7c, f4b, f4a⟩

/-- Lagrange identity: for `N ⊥ a, b`, `det3 a b y * ⟪N, e⟫ = det3 a b e * ⟪N, y⟫`. -/
theorem det3_lagrange (N a b y e : ℝ³) (h1 : ⟪N, a⟫ = 0) (h2 : ⟪N, b⟫ = 0) :
    Split.det3 a b y * ⟪N, e⟫ = Split.det3 a b e * ⟪N, y⟫ := by
  have key : Split.det3 a b y * ⟪N, e⟫ - Split.det3 a b e * ⟪N, y⟫ =
      ⟪N, a⟫ * Split.det3 y e b - ⟪N, b⟫ * Split.det3 y e a := by
    simp only [Split.det3, PiLp.inner_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
    simp; ring
  rw [h1, h2] at key
  linarith

/-- Orientation of the vertex-5 frame: `0 < det3 (x2 - x5) (x0 - x5) (x3 - x5)` when `0 < det24`. -/
theorem delta_pos {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hdet : 0 < det24 x) :
    0 < Split.det3 (x 2 - x 5) (x 0 - x 5) (x 3 - x 5) := by
  have T := type24OfFac F
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hrep : x 5 - x 1 = oblX0 x 5 • (x 0 - x 1) + oblX2 x 5 • (x 2 - x 1) +
      oblX6 x 5 • (x 6 - x 1) := by rw [T.rep 5]; abel
  have e2 : x 2 - x 5 = (-oblX0 x 5) • (x 0 - x 1) + (1 - oblX2 x 5) • (x 2 - x 1) +
      (-oblX6 x 5) • (x 6 - x 1) := by
    linear_combination (norm := module) -hrep
  have e0 : x 0 - x 5 = (1 - oblX0 x 5) • (x 0 - x 1) + (-oblX2 x 5) • (x 2 - x 1) +
      (-oblX6 x 5) • (x 6 - x 1) := by
    linear_combination (norm := module) -hrep
  have e1 : x 1 - x 5 = (-oblX0 x 5) • (x 0 - x 1) + (-oblX2 x 5) • (x 2 - x 1) +
      (-oblX6 x 5) • (x 6 - x 1) := by
    linear_combination (norm := module) -hrep
  have h := M4.det3_frame x (-oblX0 x 5) (1 - oblX2 x 5) (-oblX6 x 5) (1 - oblX0 x 5)
    (-oblX2 x 5) (-oblX6 x 5) (-oblX0 x 5) (-oblX2 x 5) (-oblX6 x 5)
  rw [← e2, ← e0, ← e1] at h
  have D1 : 0 < Split.det3 (x 2 - x 5) (x 0 - x 5) (x 1 - x 5) := by
    rw [Split.det3_eq_minimality, h]
    have : (-oblX0 x 5 * (-oblX2 x 5 * -oblX6 x 5 - -oblX6 x 5 * -oblX2 x 5) -
        (1 - oblX2 x 5) * ((1 - oblX0 x 5) * -oblX6 x 5 - -oblX6 x 5 * -oblX0 x 5) +
        -oblX6 x 5 * ((1 - oblX0 x 5) * -oblX2 x 5 - -oblX2 x 5 * -oblX0 x 5)) = oblX6 x 5 := by ring
    rw [this]; exact mul_pos hc5 hdet
  have hz1 : ⟪F.N 2, x 2 - x 5⟫ = 0 := by
    rw [F.inner_sub, F.zero 2 2 (by decide), F.zero 2 5 (by decide)]; ring
  have hz2 : ⟪F.N 2, x 0 - x 5⟫ = 0 := by
    rw [F.inner_sub, F.zero 2 0 (by decide), F.zero 2 5 (by decide)]; ring
  have lag := det3_lagrange (F.N 2) (x 2 - x 5) (x 0 - x 5) (x 1 - x 5) (x 3 - x 5) hz1 hz2
  rw [F.inner_sub, F.inner_sub, F.zero 2 5 (by decide)] at lag
  have n3 := F.neg 2 3 (by decide)
  have n1 := F.neg 2 1 (by decide)
  by_contra hΔ
  push Not at hΔ
  nlinarith [mul_pos D1 (neg_pos.2 n3), mul_nonneg (neg_nonneg.2 hΔ) (neg_nonneg.2 n1.le)]

/-! ### The three T26 region facts -/

/-- The common frame data of `x4`, `x6` in region `A1`. -/
theorem frame_data {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hA1 : Reg.A1 x F) :
    ∃ p4 q4 c61 c62 c63 : ℝ, x 4 - x 5 = p4 • (x 0 - x 5) + q4 • (x 3 - x 5) ∧
      x 6 - x 5 = c61 • (x 2 - x 5) + c62 • (x 0 - x 5) + c63 • (x 3 - x 5) ∧
      0 < p4 ∧ 1 ≤ q4 ∧ 0 < c61 ∧ 0 < c62 ∧ 0 < c63 ∧
      c62 * (q4 - 1) < p4 * (c61 + c63 - 1) ∧ 1 < p4 + q4 ∧
      (p4 - 1) * c63 < q4 * (c61 + c62 - 1) := by
  obtain ⟨p4, q4, hx4, hp4, hq4pos, hq4le, -⟩ := x4_frame F
  obtain ⟨c61, c62, c63, hx6, h61, h62, h63⟩ := x6_frame F
  obtain ⟨f7c, f4b, f4a⟩ := x46_facts F hx4 hx6 h61 h62 hq4pos
  exact ⟨p4, q4, c61, c62, c63, hx4, hx6, hp4, hq4le hA1.2, h61, h62, h63, f7c, f4b, f4a⟩

/-- `FrontDet (x 2) (x 3) (x 5) (x 6) (bT26 x)` (region fact: `Reg.A1` and `0 < det24` only). -/
theorem f2356_26_of_region {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hA1 : Reg.A1 x F)
    (hdet : 0 < det24 x) : FrontDet (x 2) (x 3) (x 5) (x 6) (bT26 x) := by
  obtain ⟨p4, q4, c61, c62, c63, hx4, hx6, hp4, hq4, h61, h62, h63, f7c, f4b, f4a⟩ :=
    frame_data F hA1
  have hΔ := delta_pos F hdet
  obtain ⟨μ, hμ, hb26⟩ := bT26_frame F hdet
  have h13 : 1 < c61 + c63 := by nlinarith
  exact frontDet_of_coords (z := x 5) (e1 := x 2 - x 5) (e2 := x 0 - x 5) (e3 := x 3 - x 5) hΔ hμ
    (P := V2) (Q := V3) (R := V5) (S := V6 c61 c62 c63) (B := B26 (oblX0 x 5))
    (eq_of_frame V2 (by simp [V2])) (eq_of_frame V3 (by simp [V3]))
    (eq_of_frame V5 (by simp [V5])) (eq_of_frame _ (by simp only [V6]; exact hx6))
    (by rw [hb26]; simp only [phi, B26]; module)
    (fd_f2356_26 hA1.1 h61 h62 h63 h13)

/-- Guard `0 ≤ ⟪N 8, bT26⟫` in the frame (`facet8_T26`). -/
theorem guard26_of_region {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hdet : 0 < det24 x)
    {p4 q4 c61 c62 c63 : ℝ} (hx4 : x 4 - x 5 = p4 • (x 0 - x 5) + q4 • (x 3 - x 5))
    (hx6 : x 6 - x 5 = c61 • (x 2 - x 5) + c62 • (x 0 - x 5) + c63 • (x 3 - x 5))
    (hp4 : 0 < p4) (hc61 : 0 < c61) (h8 : 0 ≤ ⟪F.N 8, bT26 x⟫) :
    0 ≤ (q4 - 1) * (oblX0 x 5 * c61 + (oblX0 x 5 - 1) * c62) -
      (oblX0 x 5 - 1) * p4 * (c63 - 1) := by
  obtain ⟨μ, hμ, hb26⟩ := bT26_frame F hdet
  obtain ⟨κ, hκ, hκ'⟩ := facet8_T26 F hx4 hx6 hb26 hp4 hc61 hμ
  rw [hκ'] at h8
  exact (mul_nonneg_iff_of_pos_left hκ).1 h8

theorem t26d_of_region {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hA1 : Reg.A1 x F)
    (hdet : 0 < det24 x) (h8 : 0 ≤ ⟪F.N 8, bT26 x⟫) :
    FrontDet (x 3) (x 6) (x 5) (x 4) (bT26 x) := by
  obtain ⟨p4, q4, c61, c62, c63, hx4, hx6, hp4, hq4, h61, h62, h63, f7c, f4b, f4a⟩ :=
    frame_data F hA1
  have hΔ := delta_pos F hdet
  obtain ⟨μ, hμ, hb26⟩ := bT26_frame F hdet
  have hG := guard26_of_region F hdet hx4 hx6 hp4 h61 h8
  exact frontDet_of_coords (z := x 5) (e1 := x 2 - x 5) (e2 := x 0 - x 5) (e3 := x 3 - x 5) hΔ hμ
    (P := V3) (Q := V6 c61 c62 c63) (R := V5) (S := V4 p4 q4) (B := B26 (oblX0 x 5))
    (eq_of_frame V3 (by simp [V3])) (eq_of_frame _ (by simp only [V6]; exact hx6))
    (eq_of_frame V5 (by simp [V5])) (eq_of_frame _ (by simp only [V4]; rw [hx4]; module))
    (by rw [hb26]; simp only [phi, B26]; module)
    (fd_t26d hA1.1 hp4 hq4 h61 h62 f4a hG)

theorem t26c_of_region {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hA1 : Reg.A1 x F)
    (hdet : 0 < det24 x) (h8 : 0 ≤ ⟪F.N 8, bT26 x⟫) :
    FrontDet (x 3) (x 6) (x 2) (x 4) (bT26 x) := by
  obtain ⟨p4, q4, c61, c62, c63, hx4, hx6, hp4, hq4, h61, h62, h63, f7c, f4b, f4a⟩ :=
    frame_data F hA1
  have hΔ := delta_pos F hdet
  obtain ⟨μ, hμ, hb26⟩ := bT26_frame F hdet
  have hG := guard26_of_region F hdet hx4 hx6 hp4 h61 h8
  exact frontDet_of_coords (z := x 5) (e1 := x 2 - x 5) (e2 := x 0 - x 5) (e3 := x 3 - x 5) hΔ hμ
    (P := V3) (Q := V6 c61 c62 c63) (R := V2) (S := V4 p4 q4) (B := B26 (oblX0 x 5))
    (eq_of_frame V3 (by simp [V3])) (eq_of_frame _ (by simp only [V6]; exact hx6))
    (eq_of_frame V2 (by simp [V2])) (eq_of_frame _ (by simp only [V4]; rw [hx4]; module))
    (by rw [hb26]; simp only [phi, B26]; module)
    (fd_t26c hA1.1 hp4 hq4 h62 f4a f7c hG)

/-! ### The region facts `c13 ≤ c63` and `0 < c63 c11 - c13 c61` of rim `016435` -/

theorem det3_e12 (e1 e2 e3 : ℝ³) (a b c : ℝ) :
    Split.det3 e1 e2 (a • e1 + b • e2 + c • e3) = c * Split.det3 e1 e2 e3 := by
  simp only [Split.det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

theorem det3_e23 (e1 e2 e3 : ℝ³) (a b c : ℝ) :
    Split.det3 e2 e3 (a • e1 + b • e2 + c • e3) = a * Split.det3 e1 e2 e3 := by
  simp only [Split.det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

/-- The coordinates of `x1` in the vertex-5 frame, from `x5 - x1 = a (x0 - x1) + b (x2 - x1) + c (x6 - x1)`:
`(a + b + c - 1) c11 = b + c c61` and `(a + b + c - 1) c13 = c c63`. -/
theorem x1_coords {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hdet : 0 < det24 x)
    {c11 c12 c13 c61 c62 c63 : ℝ}
    (hx1 : x 1 - x 5 = c11 • (x 2 - x 5) + c12 • (x 0 - x 5) + c13 • (x 3 - x 5))
    (hx6 : x 6 - x 5 = c61 • (x 2 - x 5) + c62 • (x 0 - x 5) + c63 • (x 3 - x 5)) :
    (oblX0 x 5 + oblX2 x 5 + oblX6 x 5 - 1) * c11 = oblX2 x 5 + oblX6 x 5 * c61 ∧
    (oblX0 x 5 + oblX2 x 5 + oblX6 x 5 - 1) * c13 = oblX6 x 5 * c63 := by
  have T := type24OfFac F
  have hΔ := delta_pos F hdet
  have hrep : x 5 - x 1 = oblX0 x 5 • (x 0 - x 1) + oblX2 x 5 • (x 2 - x 1) +
      oblX6 x 5 • (x 6 - x 1) := by rw [T.rep 5]; abel
  have h0 : (oblX0 x 5 + oblX2 x 5 + oblX6 x 5 - 1) • (x 1 - x 5) - oblX0 x 5 • (x 0 - x 5) -
      oblX2 x 5 • (x 2 - x 5) - oblX6 x 5 • (x 6 - x 5) = 0 := by
    linear_combination (norm := module) hrep
  rw [hx1, hx6] at h0
  have vec : ((oblX0 x 5 + oblX2 x 5 + oblX6 x 5 - 1) * c11 - oblX2 x 5 - oblX6 x 5 * c61) •
        (x 2 - x 5) +
      ((oblX0 x 5 + oblX2 x 5 + oblX6 x 5 - 1) * c12 - oblX0 x 5 - oblX6 x 5 * c62) •
        (x 0 - x 5) +
      ((oblX0 x 5 + oblX2 x 5 + oblX6 x 5 - 1) * c13 - oblX6 x 5 * c63) • (x 3 - x 5) = 0 := by
    linear_combination (norm := module) h0
  have d12 := congrArg (Split.det3 (x 2 - x 5) (x 0 - x 5)) vec
  have d23 := congrArg (Split.det3 (x 0 - x 5) (x 3 - x 5)) vec
  have z : ∀ a b : ℝ³, Split.det3 a b 0 = 0 := by intro a b; simp [Split.det3]
  rw [det3_e12, z] at d12
  rw [det3_e23, z] at d23
  have k3 := (mul_eq_zero.1 d12).resolve_right hΔ.ne'
  have k1 := (mul_eq_zero.1 d23).resolve_right hΔ.ne'
  constructor <;> linarith

theorem coords_unique {e1 e2 e3 : ℝ³} (hΔ : 0 < Split.det3 e1 e2 e3) {a1 a2 a3 b1 b2 b3 : ℝ}
    (h : a1 • e1 + a2 • e2 + a3 • e3 = b1 • e1 + b2 • e2 + b3 • e3) : a1 = b1 ∧ a3 = b3 := by
  have h12 := congrArg (Split.det3 e1 e2) h
  have h23 := congrArg (Split.det3 e2 e3) h
  rw [det3_e12, det3_e12] at h12
  rw [det3_e23, det3_e23] at h23
  exact ⟨mul_right_cancel₀ hΔ.ne' h23, mul_right_cancel₀ hΔ.ne' h12⟩

/-- Region facts `c13 ≤ c63` (`c5 (c63 - c13) = (a5 + b5 - 1) c13`) and `0 < c63 c11 - c13 c61`
(`s (c63 c11 - c13 c61) = b5 c63`) of rim `016435`, from `Reg.A1` and `0 < det24` only. -/
theorem c13_c63_pos_of_region {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hA1 : Reg.A1 x F)
    (hdet : 0 < det24 x) {c11 c12 c13 c61 c62 c63 : ℝ}
    (hx1 : x 1 - x 5 = c11 • (x 2 - x 5) + c12 • (x 0 - x 5) + c13 • (x 3 - x 5))
    (hx6 : x 6 - x 5 = c61 • (x 2 - x 5) + c62 • (x 0 - x 5) + c63 • (x 3 - x 5)) :
    c13 ≤ c63 ∧ 0 < c63 * c11 - c13 * c61 := by
  obtain ⟨k1, k3⟩ := x1_coords F hdet hx1 hx6
  have T := type24OfFac F
  have hΔ := delta_pos F hdet
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  obtain ⟨c11', c12', c13', hx1', h11, h12, h13⟩ := x1_frame F
  obtain ⟨c61', c62', c63', hx6', h61, h62, h63⟩ := x6_frame F
  obtain ⟨e11, e13⟩ := coords_unique hΔ (hx1.symm.trans hx1')
  obtain ⟨e61, e63⟩ := coords_unique hΔ (hx6.symm.trans hx6')
  subst e11 e13 e61 e63
  have ha := hA1.1
  have hs : 0 < oblX0 x 5 + oblX2 x 5 + oblX6 x 5 - 1 := by linarith
  constructor
  · by_contra hlt
    push Not at hlt
    nlinarith [mul_pos (by linarith : 0 < oblX0 x 5 + oblX2 x 5 - 1) h13, mul_le_mul_of_nonneg_left hlt.le hc5.le]
  · have hX : (oblX0 x 5 + oblX2 x 5 + oblX6 x 5 - 1) * (c63 * c11 - c13 * c61) =
        oblX2 x 5 * c63 := by linear_combination c63 * k1 - c61 * k3
    have : 0 < (oblX0 x 5 + oblX2 x 5 + oblX6 x 5 - 1) * (c63 * c11 - c13 * c61) := by
      rw [hX]; exact mul_pos hb5 h63
    exact pos_of_mul_pos_right this hs.le

/-! ### The T25 region facts (`t25_01635a`, `t25_01635b`, `t16_04`, `t16_06`, `t16_07`, `t16_13`) -/

private theorem det3_e13 (e1 e2 e3 : ℝ³) (a b c : ℝ) :
    Split.det3 e1 e3 (a • e1 + b • e2 + c • e3) = -b * Split.det3 e1 e2 e3 := by
  simp only [Split.det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

private theorem x1_c12 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hdet : 0 < det24 x)
    {c11 c12 c13 c61 c62 c63 : ℝ}
    (hx1 : x 1 - x 5 = c11 • (x 2 - x 5) + c12 • (x 0 - x 5) + c13 • (x 3 - x 5))
    (hx6 : x 6 - x 5 = c61 • (x 2 - x 5) + c62 • (x 0 - x 5) + c63 • (x 3 - x 5)) :
    (oblX0 x 5 + oblX2 x 5 + oblX6 x 5 - 1) * c12 = oblX0 x 5 + oblX6 x 5 * c62 := by
  have T := type24OfFac F
  have hΔ := delta_pos F hdet
  have hrep : x 5 - x 1 = oblX0 x 5 • (x 0 - x 1) + oblX2 x 5 • (x 2 - x 1) +
      oblX6 x 5 • (x 6 - x 1) := by rw [T.rep 5]; abel
  have h0 : (oblX0 x 5 + oblX2 x 5 + oblX6 x 5 - 1) • (x 1 - x 5) - oblX0 x 5 • (x 0 - x 5) -
      oblX2 x 5 • (x 2 - x 5) - oblX6 x 5 • (x 6 - x 5) = 0 := by
    linear_combination (norm := module) hrep
  rw [hx1, hx6] at h0
  have vec : ((oblX0 x 5 + oblX2 x 5 + oblX6 x 5 - 1) * c11 - oblX2 x 5 - oblX6 x 5 * c61) •
        (x 2 - x 5) +
      ((oblX0 x 5 + oblX2 x 5 + oblX6 x 5 - 1) * c12 - oblX0 x 5 - oblX6 x 5 * c62) •
        (x 0 - x 5) +
      ((oblX0 x 5 + oblX2 x 5 + oblX6 x 5 - 1) * c13 - oblX6 x 5 * c63) • (x 3 - x 5) = 0 := by
    linear_combination (norm := module) h0
  have d13 := congrArg (Split.det3 (x 2 - x 5) (x 3 - x 5)) vec
  have z : ∀ a b : ℝ³, Split.det3 a b 0 = 0 := by intro a b; simp [Split.det3]
  rw [det3_e13, z] at d13
  have k2 := (mul_eq_zero.1 d13).resolve_right hΔ.ne'
  linarith

private theorem fd_0615 {c11 c12 c13 c61 c62 c63 : ℝ}
    (h13 : 0 < c13) (h63 : 0 < c63) (hle : c13 ≤ c63)
    (hpos : 0 < c63 * c11 - c13 * c61)
    (hN1 : -c12 * c63 + c13 * c62 - c13 + c63 < 0) :
    FrontDetR (d3c (V0 - V6 c61 c62 c63) (V1 c11 c12 c13 - V5) B25)
      (d3c (V5 - V6 c61 c62 c63) (V1 c11 c12 c13 - V5) B25)
      (-d3c (V0 - V6 c61 c62 c63) (V5 - V6 c61 c62 c63) B25)
      (d3c (V0 - V6 c61 c62 c63) (V1 c11 c12 c13 - V5) (V5 - V6 c61 c62 c63)) := by
  unfold FrontDetR
  simp only [d3c, V0, V6, V1, V5, B25, Prod.fst_sub, Prod.snd_sub]
  right
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

private theorem fd_0415 {a5 c5 s p4 q4 c11 c12 c13 c62 c63 : ℝ}
    (h11 : 0 < c11) (h13 : 0 < c13) (hq : 1 ≤ q4) (ha5 : 1 < a5) (hc5 : 0 < c5) (hs : 0 < s)
    (hs12 : s * c12 = a5 + c5 * c62) (hs13 : s * c13 = c5 * c63)
    (hB : 0 < c62 * q4 - c63 * p4) (hAC : -c12 * q4 + c13 * p4 - c13 + q4 < 0) :
    FrontDetR (d3c (V0 - V4 p4 q4) (V1 c11 c12 c13 - V5) B25)
      (d3c (V5 - V4 p4 q4) (V1 c11 c12 c13 - V5) B25)
      (-d3c (V0 - V4 p4 q4) (V5 - V4 p4 q4) B25)
      (d3c (V0 - V4 p4 q4) (V1 c11 c12 c13 - V5) (V5 - V4 p4 q4)) := by
  unfold FrontDetR
  simp only [d3c, V0, V4, V1, V5, B25, Prod.fst_sub, Prod.snd_sub]
  right
  have hsB : s * (-c12 * q4 + c13 * p4) = -a5 * q4 - c5 * (c62 * q4 - c63 * p4) := by
    linear_combination -q4 * hs12 + p4 * hs13
  refine ⟨by linarith, ?_, by linarith, by linarith, by linarith, by nlinarith⟩
  nlinarith [mul_pos (by linarith : 0 < a5) (by linarith : 0 < q4), mul_pos hc5 hB]

private theorem fd_0463 {p4 q4 c61 c62 c63 : ℝ}
    (h61 : 0 < c61) (hpq : 1 < p4 + q4)
    (hc6 : 1 - c62 - c63 < 0) (hN8 : 0 < c62 * (q4 - 1) - p4 * (c63 - 1))
    (hAC : -c62 * q4 + c63 * p4 - c63 + q4 < 0) :
    FrontDetR (d3c (V0 - V4 p4 q4) (V6 c61 c62 c63 - V3) B25)
      (d3c (V3 - V4 p4 q4) (V6 c61 c62 c63 - V3) B25)
      (-d3c (V0 - V4 p4 q4) (V3 - V4 p4 q4) B25)
      (d3c (V0 - V4 p4 q4) (V6 c61 c62 c63 - V3) (V3 - V4 p4 q4)) := by
  unfold FrontDetR
  simp only [d3c, V0, V4, V6, V3, B25, Prod.fst_sub, Prod.snd_sub]
  right
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by nlinarith⟩

private theorem fd_0465 {p4 q4 c61 c62 c63 : ℝ}
    (h61 : 0 < c61) (h63 : 0 < c63) (hq : 1 ≤ q4)
    (hB : 0 < c62 * q4 - c63 * p4) (hAC : -c62 * q4 + c63 * p4 - c63 + q4 < 0) :
    FrontDetR (d3c (V0 - V4 p4 q4) (V6 c61 c62 c63 - V5) B25)
      (d3c (V5 - V4 p4 q4) (V6 c61 c62 c63 - V5) B25)
      (-d3c (V0 - V4 p4 q4) (V5 - V4 p4 q4) B25)
      (d3c (V0 - V4 p4 q4) (V6 c61 c62 c63 - V5) (V5 - V4 p4 q4)) := by
  unfold FrontDetR
  simp only [d3c, V0, V4, V6, V5, B25, Prod.fst_sub, Prod.snd_sub]
  right
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by nlinarith⟩

private theorem fd_4563 {p4 q4 c61 c62 c63 : ℝ}
    (hp : 0 < p4) (h61 : 0 < c61) (h62 : 0 < c62)
    (hN8 : 0 < c62 * (q4 - 1) - p4 * (c63 - 1)) (hC : 0 < c62 * q4 - c63 * p4) :
    FrontDetR (d3c (V4 p4 q4 - V5) (V6 c61 c62 c63 - V3) B25)
      (d3c (V3 - V5) (V6 c61 c62 c63 - V3) B25)
      (-d3c (V4 p4 q4 - V5) (V3 - V5) B25)
      (d3c (V4 p4 q4 - V5) (V6 c61 c62 c63 - V3) (V3 - V5)) := by
  unfold FrontDetR
  simp only [d3c, V4, V5, V6, V3, B25, Prod.fst_sub, Prod.snd_sub]
  left
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by nlinarith⟩

private theorem f1_t25_facts {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    {p4 q4 c11 c12 c13 c61 c62 c63 : ℝ}
    (hx4 : x 4 - x 5 = p4 • (x 0 - x 5) + q4 • (x 3 - x 5))
    (hx1 : x 1 - x 5 = c11 • (x 2 - x 5) + c12 • (x 0 - x 5) + c13 • (x 3 - x 5))
    (hx6 : x 6 - x 5 = c61 • (x 2 - x 5) + c62 • (x 0 - x 5) + c63 • (x 3 - x 5))
    (h11 : 0 < c11) (h13 : 0 < c13) (h61 : 0 < c61) (h63 : 0 < c63) (hq4 : 0 < q4)
    (hpos : 0 < c63 * c11 - c13 * c61) (h1 : 0 < ⟪F.N 1, bT25 x⟫) :
    (1 - c62 - c63 < 0) ∧ (1 - c12 - c13 < 0) ∧
      (-c12 * c63 + c13 * c62 - c13 + c63 < 0) ∧
      (0 < c11 * (c62 + c63 - 1) - c61 * (c12 + c13 - 1)) ∧
      (-c12 * q4 + c13 * p4 - c13 + q4 < 0) ∧
      (-c62 * q4 + c63 * p4 - c63 + q4 < 0) := by
  have hx4' : x 4 - x 5 = (0:ℝ) • (x 2 - x 5) + p4 • (x 0 - x 5) + q4 • (x 3 - x 5) := by
    rw [hx4]; module
  have e1 := fval F 1 hx1
  have e6 := fval F 1 hx6
  have e4 := fval F 1 hx4'
  rw [F.zero 1 1 (by decide), F.zero 1 0 (by decide)] at e1
  rw [F.zero 1 6 (by decide), F.zero 1 0 (by decide)] at e6
  rw [F.zero 1 0 (by decide)] at e4
  have hb : F.f 1 (x 2) - F.f 1 (x 5) = -⟪F.N 1, bT25 x⟫ := by
    have hbT : bT25 x = -(x 2 - x 5) := by unfold bT25; abel
    rw [hbT, inner_neg_right, F.inner_sub]; ring
  have w5 := F.neg 1 5 (by decide)
  have w3 := F.neg 1 3 (by decide)
  have w4 := F.neg 1 4 (by decide)
  have k6 : (1 - c62 - c63) * F.f 1 (x 5) = c61 * ⟪F.N 1, bT25 x⟫ + c63 * (-F.f 1 (x 3)) := by
    linear_combination -e6 - c61 * hb
  have hc6 : 1 - c62 - c63 < 0 := by
    by_contra hK; push Not at hK
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hK w5.le, mul_pos h61 h1, mul_pos h63 (neg_pos.2 w3)]
  have k1 : (1 - c12 - c13) * F.f 1 (x 5) = c11 * ⟪F.N 1, bT25 x⟫ + c13 * (-F.f 1 (x 3)) := by
    linear_combination -e1 - c11 * hb
  have hc1 : 1 - c12 - c13 < 0 := by
    by_contra hK; push Not at hK
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hK w5.le, mul_pos h11 h1, mul_pos h13 (neg_pos.2 w3)]
  have kN1 : (-c12 * c63 + c13 * c62 - c13 + c63) * F.f 1 (x 5) =
      (c63 * c11 - c13 * c61) * ⟪F.N 1, bT25 x⟫ := by
    linear_combination c13 * e6 - c63 * e1 - (c63 * c11 - c13 * c61) * hb
  have hN1 : -c12 * c63 + c13 * c62 - c13 + c63 < 0 := by
    by_contra hK; push Not at hK
    have p1 := mul_nonpos_of_nonneg_of_nonpos hK w5.le
    have p2 := mul_pos hpos h1
    linarith
  have kD : (c11 * (c62 + c63 - 1) - c61 * (c12 + c13 - 1)) * (-F.f 1 (x 5)) =
      (c63 * c11 - c13 * c61) * (-F.f 1 (x 3)) := by
    linear_combination -c11 * e6 + c61 * e1
  have hD : 0 < c11 * (c62 + c63 - 1) - c61 * (c12 + c13 - 1) := by
    by_contra hK; push Not at hK
    have p1 := mul_nonpos_of_nonpos_of_nonneg hK (neg_nonneg.2 w5.le)
    have p2 := mul_pos hpos (neg_pos.2 w3)
    linarith
  have k41 : (-c12 * q4 + c13 * p4 - c13 + q4) * (-F.f 1 (x 5)) =
      c13 * F.f 1 (x 4) - q4 * c11 * ⟪F.N 1, bT25 x⟫ := by
    linear_combination -c13 * e4 + q4 * e1 + q4 * c11 * hb
  have h41 : -c12 * q4 + c13 * p4 - c13 + q4 < 0 := by
    by_contra hK; push Not at hK
    have p1 := mul_nonneg hK (neg_nonneg.2 w5.le)
    have p2 := mul_pos h13 (neg_pos.2 w4)
    have p3 := mul_pos (mul_pos hq4 h11) h1
    linarith
  have k46 : (-c62 * q4 + c63 * p4 - c63 + q4) * (-F.f 1 (x 5)) =
      c63 * F.f 1 (x 4) - q4 * c61 * ⟪F.N 1, bT25 x⟫ := by
    linear_combination -c63 * e4 + q4 * e6 + q4 * c61 * hb
  have h46 : -c62 * q4 + c63 * p4 - c63 + q4 < 0 := by
    by_contra hK; push Not at hK
    have p1 := mul_nonneg hK (neg_nonneg.2 w5.le)
    have p2 := mul_pos h63 (neg_pos.2 w4)
    have p3 := mul_pos (mul_pos hq4 h61) h1
    linarith
  exact ⟨hc6, hc1, hN1, hD, h41, h46⟩

private theorem f8_t25_fact {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    {p4 q4 c61 c62 c63 : ℝ}
    (hx4 : x 4 - x 5 = p4 • (x 0 - x 5) + q4 • (x 3 - x 5))
    (hx6 : x 6 - x 5 = c61 • (x 2 - x 5) + c62 • (x 0 - x 5) + c63 • (x 3 - x 5))
    (hp4 : 0 < p4) (h61 : 0 < c61) (h8 : ⟪F.N 8, bT25 x⟫ < 0) :
    0 < c62 * (q4 - 1) - p4 * (c63 - 1) := by
  have hx4' : x 4 - x 5 = (0:ℝ) • (x 2 - x 5) + p4 • (x 0 - x 5) + q4 • (x 3 - x 5) := by
    rw [hx4]; module
  have e4 := fval F 8 hx4'
  have e6 := fval F 8 hx6
  rw [F.zero 8 4 (by decide), F.zero 8 3 (by decide)] at e4
  rw [F.zero 8 6 (by decide), F.zero 8 3 (by decide)] at e6
  have hb : F.f 8 (x 2) - F.f 8 (x 5) = -⟪F.N 8, bT25 x⟫ := by
    have hbT : bT25 x = -(x 2 - x 5) := by unfold bT25; abel
    rw [hbT, inner_neg_right, F.inner_sub]; ring
  have w5 := F.neg 8 5 (by decide)
  have key : (c62 * (q4 - 1) - p4 * (c63 - 1)) * (-F.f 8 (x 5)) = p4 * c61 * (-⟪F.N 8, bT25 x⟫) := by
    linear_combination p4 * e6 - c62 * e4 + p4 * c61 * hb
  by_contra hK; push Not at hK
  have p1 := mul_nonpos_of_nonpos_of_nonneg hK (neg_nonneg.2 w5.le)
  have p2 := mul_pos (mul_pos hp4 h61) (neg_pos.2 h8)
  linarith

private theorem f4_x1_fact {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    {p4 q4 c11 c12 c13 c61 c62 c63 : ℝ}
    (hx4 : x 4 - x 5 = p4 • (x 0 - x 5) + q4 • (x 3 - x 5))
    (hx1 : x 1 - x 5 = c11 • (x 2 - x 5) + c12 • (x 0 - x 5) + c13 • (x 3 - x 5))
    (hx6 : x 6 - x 5 = c61 • (x 2 - x 5) + c62 • (x 0 - x 5) + c63 • (x 3 - x 5))
    (h11 : 0 < c11) (h61 : 0 < c61) (hp4 : 0 < p4) (hq4 : 1 ≤ q4)
    (h41 : -c12 * q4 + c13 * p4 - c13 + q4 < 0)
    (hN8 : 0 < c62 * (q4 - 1) - p4 * (c63 - 1)) :
    0 < c62 * q4 - c63 * p4 := by
  rcases lt_or_ge c63 q4 with hlt | hge
  · have hx4' : x 4 - x 5 = (0:ℝ) • (x 2 - x 5) + p4 • (x 0 - x 5) + q4 • (x 3 - x 5) := by
      rw [hx4]; module
    have e4 := fval F 4 hx4'
    have e6 := fval F 4 hx6
    have e1 := fval F 4 hx1
    rw [F.zero 4 4 (by decide), F.zero 4 0 (by decide)] at e4
    rw [F.zero 4 6 (by decide), F.zero 4 0 (by decide)] at e6
    rw [F.zero 4 0 (by decide)] at e1
    have w5 := F.neg 4 5 (by decide)
    have w1 := F.neg 4 1 (by decide)
    have key : (c11 * (c62 * q4 - c63 * p4 - (q4 - c63)) + c61 * (-c12 * q4 + c13 * p4 - c13 + q4)) *
        F.f 4 (x 5) = q4 * c61 * F.f 4 (x 1) := by
      linear_combination -q4 * c61 * e1 + c11 * q4 * e6 - (c11 * c63 - c13 * c61) * e4
    have hpos1 : 0 < c11 * (c62 * q4 - c63 * p4 - (q4 - c63)) +
        c61 * (-c12 * q4 + c13 * p4 - c13 + q4) := by
      by_contra hK; push Not at hK
      have hrhs : q4 * c61 * F.f 4 (x 1) < 0 := by
        nlinarith [mul_pos (by linarith : 0 < q4) h61, neg_pos.2 w1]
      nlinarith [mul_nonneg_of_nonpos_of_nonpos hK w5.le]
    nlinarith [mul_pos h61 (neg_pos.2 h41)]
  · have hq1 : 0 < q4 - 1 := by
      by_contra hq0; push Not at hq0
      have : q4 = 1 := by linarith
      subst this
      nlinarith [mul_nonneg hp4.le (by linarith : 0 ≤ c63 - 1)]
    have hc62_gt : p4 < c62 := by
      by_contra hle; push Not at hle
      have h1 : (c62 - p4) * (q4 - 1) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hq1.le
      nlinarith [mul_nonneg hp4.le (by linarith : 0 ≤ c63 - q4)]
    have : c62 * q4 - c63 * p4 = (c62 * (q4 - 1) - p4 * (c63 - 1)) + (c62 - p4) := by ring
    linarith

private theorem bT25_eq_phi {x : Fin 7 → ℝ³} :
    bT25 x = (1 : ℝ) • phi (x 2 - x 5) (x 0 - x 5) (x 3 - x 5) B25 := by
  ext i; simp only [bT25, phi, B25, one_smul, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

theorem t25_01635b_of_region {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hA1 : Reg.A1 x F)
    (hdet : 0 < det24 x) (h1 : 0 < ⟪F.N 1, bT25 x⟫) :
    FrontDet (x 0) (x 6) (x 1) (x 5) (bT25 x) := by
  obtain ⟨p4, q4, c61, c62, c63, hx4, hx6, hp4, hq4, h61, h62, h63, -, -, -⟩ := frame_data F hA1
  obtain ⟨c11, c12, c13, hx1, h11, h12, h13⟩ := x1_frame F
  have hΔ := delta_pos F hdet
  obtain ⟨hle, hpos⟩ := c13_c63_pos_of_region F hA1 hdet hx1 hx6
  obtain ⟨-, -, hN1, -, -, -⟩ := f1_t25_facts F hx4 hx1 hx6 h11 h13 h61 h63 (by linarith) hpos h1
  exact frontDet_of_coords (z := x 5) (e1 := x 2 - x 5) (e2 := x 0 - x 5) (e3 := x 3 - x 5) hΔ one_pos
    (P := V0) (Q := V6 c61 c62 c63) (R := V1 c11 c12 c13) (S := V5) (B := B25)
    (eq_of_frame V0 (by simp [V0])) (eq_of_frame _ (by simp only [V6]; exact hx6))
    (eq_of_frame _ (by simp only [V1]; exact hx1)) (eq_of_frame V5 (by simp [V5]))
    bT25_eq_phi (fd_0615 h13 h63 hle hpos hN1)

theorem t16_04_of_region {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hA1 : Reg.A1 x F)
    (hdet : 0 < det24 x) (h1 : 0 < ⟪F.N 1, bT25 x⟫) (h8 : ⟪F.N 8, bT25 x⟫ < 0) :
    FrontDet (x 0) (x 4) (x 1) (x 5) (bT25 x) := by
  obtain ⟨p4, q4, c61, c62, c63, hx4, hx6, hp4, hq4, h61, h62, h63, -, -, -⟩ := frame_data F hA1
  obtain ⟨c11, c12, c13, hx1, h11, h12, h13⟩ := x1_frame F
  have hΔ := delta_pos F hdet
  obtain ⟨-, hpos⟩ := c13_c63_pos_of_region F hA1 hdet hx1 hx6
  obtain ⟨-, -, -, -, h41, -⟩ := f1_t25_facts F hx4 hx1 hx6 h11 h13 h61 h63 (by linarith) hpos h1
  have hN8 := f8_t25_fact F hx4 hx6 hp4 h61 h8
  have hB := f4_x1_fact F hx4 hx1 hx6 h11 h61 hp4 hq4 h41 hN8
  have T := type24OfFac F
  have hs12 := x1_c12 F hdet hx1 hx6
  have hs13 := (x1_coords F hdet hx1 hx6).2
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hs : 0 < oblX0 x 5 + oblX2 x 5 + oblX6 x 5 - 1 := by linarith [hA1.1]
  exact frontDet_of_coords (z := x 5) (e1 := x 2 - x 5) (e2 := x 0 - x 5) (e3 := x 3 - x 5) hΔ one_pos
    (P := V0) (Q := V4 p4 q4) (R := V1 c11 c12 c13) (S := V5) (B := B25)
    (eq_of_frame V0 (by simp [V0])) (eq_of_frame _ (by simp only [V4]; rw [hx4]; module))
    (eq_of_frame _ (by simp only [V1]; exact hx1)) (eq_of_frame V5 (by simp [V5]))
    bT25_eq_phi (fd_0415 h11 h13 hq4 hA1.1 hc5 hs hs12 hs13 hB h41)

theorem t16_06_of_region {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hA1 : Reg.A1 x F)
    (hdet : 0 < det24 x) (h1 : 0 < ⟪F.N 1, bT25 x⟫) (h8 : ⟪F.N 8, bT25 x⟫ < 0) :
    FrontDet (x 0) (x 4) (x 6) (x 3) (bT25 x) := by
  obtain ⟨p4, q4, c61, c62, c63, hx4, hx6, hp4, hq4, h61, h62, h63, -, hpq, -⟩ := frame_data F hA1
  obtain ⟨c11, c12, c13, hx1, h11, h12, h13⟩ := x1_frame F
  have hΔ := delta_pos F hdet
  obtain ⟨-, hpos⟩ := c13_c63_pos_of_region F hA1 hdet hx1 hx6
  obtain ⟨hc6, -, -, -, -, h46⟩ := f1_t25_facts F hx4 hx1 hx6 h11 h13 h61 h63 (by linarith) hpos h1
  have hN8 := f8_t25_fact F hx4 hx6 hp4 h61 h8
  exact frontDet_of_coords (z := x 5) (e1 := x 2 - x 5) (e2 := x 0 - x 5) (e3 := x 3 - x 5) hΔ one_pos
    (P := V0) (Q := V4 p4 q4) (R := V6 c61 c62 c63) (S := V3) (B := B25)
    (eq_of_frame V0 (by simp [V0])) (eq_of_frame _ (by simp only [V4]; rw [hx4]; module))
    (eq_of_frame _ (by simp only [V6]; exact hx6)) (eq_of_frame V3 (by simp [V3]))
    bT25_eq_phi (fd_0463 h61 hpq hc6 hN8 h46)

theorem t16_07_of_region {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hA1 : Reg.A1 x F)
    (hdet : 0 < det24 x) (h1 : 0 < ⟪F.N 1, bT25 x⟫) (h8 : ⟪F.N 8, bT25 x⟫ < 0) :
    FrontDet (x 0) (x 4) (x 6) (x 5) (bT25 x) := by
  obtain ⟨p4, q4, c61, c62, c63, hx4, hx6, hp4, hq4, h61, h62, h63, -, -, -⟩ := frame_data F hA1
  obtain ⟨c11, c12, c13, hx1, h11, h12, h13⟩ := x1_frame F
  have hΔ := delta_pos F hdet
  obtain ⟨-, hpos⟩ := c13_c63_pos_of_region F hA1 hdet hx1 hx6
  obtain ⟨-, -, -, -, h41, h46⟩ := f1_t25_facts F hx4 hx1 hx6 h11 h13 h61 h63 (by linarith) hpos h1
  have hN8 := f8_t25_fact F hx4 hx6 hp4 h61 h8
  have hB := f4_x1_fact F hx4 hx1 hx6 h11 h61 hp4 hq4 h41 hN8
  exact frontDet_of_coords (z := x 5) (e1 := x 2 - x 5) (e2 := x 0 - x 5) (e3 := x 3 - x 5) hΔ one_pos
    (P := V0) (Q := V4 p4 q4) (R := V6 c61 c62 c63) (S := V5) (B := B25)
    (eq_of_frame V0 (by simp [V0])) (eq_of_frame _ (by simp only [V4]; rw [hx4]; module))
    (eq_of_frame _ (by simp only [V6]; exact hx6)) (eq_of_frame V5 (by simp [V5]))
    bT25_eq_phi (fd_0465 h61 h63 hq4 hB h46)

theorem t16_13_of_region {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hA1 : Reg.A1 x F)
    (hdet : 0 < det24 x) (h1 : 0 < ⟪F.N 1, bT25 x⟫) (h8 : ⟪F.N 8, bT25 x⟫ < 0) :
    FrontDet (x 4) (x 5) (x 6) (x 3) (bT25 x) := by
  obtain ⟨p4, q4, c61, c62, c63, hx4, hx6, hp4, hq4, h61, h62, h63, -, -, -⟩ := frame_data F hA1
  obtain ⟨c11, c12, c13, hx1, h11, h12, h13⟩ := x1_frame F
  have hΔ := delta_pos F hdet
  obtain ⟨-, hpos⟩ := c13_c63_pos_of_region F hA1 hdet hx1 hx6
  obtain ⟨-, -, -, -, h41, -⟩ := f1_t25_facts F hx4 hx1 hx6 h11 h13 h61 h63 (by linarith) hpos h1
  have hN8 := f8_t25_fact F hx4 hx6 hp4 h61 h8
  have hC := f4_x1_fact F hx4 hx1 hx6 h11 h61 hp4 hq4 h41 hN8
  exact frontDet_of_coords (z := x 5) (e1 := x 2 - x 5) (e2 := x 0 - x 5) (e3 := x 3 - x 5) hΔ one_pos
    (P := V4 p4 q4) (Q := V5) (R := V6 c61 c62 c63) (S := V3) (B := B25)
    (eq_of_frame _ (by simp only [V4]; rw [hx4]; module)) (eq_of_frame V5 (by simp [V5]))
    (eq_of_frame _ (by simp only [V6]; exact hx6)) (eq_of_frame V3 (by simp [V3]))
    bT25_eq_phi (fd_4563 hp4 h61 h62 hN8 hC)

/-! ### The reduced bundle and the main theorem -/

/-- Reduced sample-fact bundle: `A1TieSample` without the region facts `f2356_26` and the T26 fronts
`2 3 5 4`-complement (`3 6 2 4`, `3 6 5 4`), which are consequences of `Reg.A1` and `0 < det24 x`. -/
structure A1TieSmall (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop where
  hb5_ne : ⟪F.N 1, bT25 x⟫ ≠ 0
  hc63 : F.f 2 (x 6) ≤ F.f 2 (x 3)
  hq_sig1 : F.f 8 (x 0) = F.f 8 (x 5) → ⟪x 2 - x 5, x 3 - x 5⟫ = 0 → ⟪x 0 - x 5, x 3 - x 5⟫ = 0 →
    F.f 2 (x 6) < F.f 2 (x 3)
  h4 : ⟪F.N 1, bT25 x⟫ < 0 ∨ ⟪F.N 8, bT25 x⟫ < 0 → 0 < ⟪F.N 4, bT25 x⟫
  /-- Undecided/sample T26 fronts `2 3 5 4` and `2 4 5 6` (rim `25346`). -/
  t26_fronts_25346 : 0 ≤ ⟪F.N 8, bT26 x⟫ →
    FrontDet (x 2) (x 3) (x 5) (x 4) (bT26 x) ∧ FrontDet (x 2) (x 4) (x 5) (x 6) (bT26 x)
  t25_fronts_0536 : ⟪F.N 1, bT25 x⟫ < 0 → 0 ≤ ⟪F.N 8, bT25 x⟫ →
    FrontDet (x 0) (x 3) (x 5) (x 6) (bT25 x)
  t25_fronts_05346 : ⟪F.N 1, bT25 x⟫ < 0 → ⟪F.N 8, bT25 x⟫ < 0 →
    FrontDet (x 0) (x 3) (x 5) (x 6) (bT25 x) ∧
    FrontDet (x 0) (x 4) (x 5) (x 6) (bT25 x) ∧
    FrontDet (x 0) (x 4) (x 3) (x 6) (bT25 x) ∧
    FrontDet (x 5) (x 4) (x 3) (x 6) (bT25 x)
  t25_fronts_01635 : 0 < ⟪F.N 1, bT25 x⟫ → 0 ≤ ⟪F.N 8, bT25 x⟫ →
    FrontDet (x 0) (x 6) (x 1) (x 3) (bT25 x) ∧
    FrontDet (x 0) (x 3) (x 1) (x 5) (bT25 x) ∧
    FrontDet (x 0) (x 3) (x 6) (x 5) (bT25 x) ∧
    (FrontDet (x 6) (x 5) (x 1) (x 3) (bT25 x) ∨ FrontDet (x 1) (x 3) (x 6) (x 5) (bT25 x))
  t25_016435 : 0 < ⟪F.N 1, bT25 x⟫ → ⟪F.N 8, bT25 x⟫ < 0 →
    (∀ {p4 q4 c11 c12 c13 c61 c62 c63 : ℝ},
      x 4 - x 5 = p4 • (x 0 - x 5) + q4 • (x 3 - x 5) →
      x 1 - x 5 = c11 • (x 2 - x 5) + c12 • (x 0 - x 5) + c13 • (x 3 - x 5) →
      x 6 - x 5 = c61 • (x 2 - x 5) + c62 • (x 0 - x 5) + c63 • (x 3 - x 5) →
      c13 < 1 ∧ q4 ≤ c63) ∧
    FrontDet (x 0) (x 6) (x 1) (x 4) (bT25 x) ∧
    FrontDet (x 0) (x 6) (x 1) (x 3) (bT25 x) ∧
    FrontDet (x 0) (x 4) (x 1) (x 3) (bT25 x) ∧
    FrontDet (x 0) (x 3) (x 1) (x 5) (bT25 x) ∧
    FrontDet (x 0) (x 3) (x 6) (x 5) (bT25 x) ∧
    FrontDet (x 1) (x 4) (x 6) (x 3) (bT25 x) ∧
    FrontDet (x 1) (x 4) (x 6) (x 5) (bT25 x) ∧
    FrontDet (x 6) (x 5) (x 1) (x 3) (bT25 x) ∧
    FrontDet (x 4) (x 5) (x 1) (x 3) (bT25 x)

theorem a1TieSample_of_small {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hA1 : Reg.A1 x F)
    (hdet : 0 < det24 x) (hS : A1TieSmall x F) : A1TieSample x F where
  hb5_ne := hS.hb5_ne
  hc63 := hS.hc63
  hq_sig1 := hS.hq_sig1
  h4 := hS.h4
  f2356_26 := f2356_26_of_region F hA1 hdet
  t26_fronts_25346 := fun h8 =>
    ⟨(hS.t26_fronts_25346 h8).1, (hS.t26_fronts_25346 h8).2, t26c_of_region F hA1 hdet h8,
      t26d_of_region F hA1 hdet h8⟩
  t25_fronts_0536 := hS.t25_fronts_0536
  t25_fronts_05346 := hS.t25_fronts_05346
  t25_fronts_01635 := fun h1 h8 => by
    obtain ⟨a, c, d, e⟩ := hS.t25_fronts_01635 h1 h8
    refine ⟨a, t25_01635b_of_region F hA1 hdet h1, c, d, ?_⟩
    rcases e with e | e
    · exact Or.inl e
    · exact Or.inr ⟨e, fun {_ _ _ _ _ _} hx1 hx6 => c13_c63_pos_of_region F hA1 hdet hx1 hx6⟩
  t25_016435 := fun h1 h8 => by
    obtain ⟨hfr, f00, f01, f03, f05, f08, f09, f10, f11, f12⟩ := hS.t25_016435 h1 h8
    exact ⟨fun {_ _ _ _ _ _ _ _} hx4 hx1 hx6 =>
      ⟨(hfr hx4 hx1 hx6).1,
        (c13_c63_pos_of_region F hA1 hdet hx1 hx6).1,
        (hfr hx4 hx1 hx6).2,
        (c13_c63_pos_of_region F hA1 hdet hx1 hx6).2⟩,
      f00, f01, t25_01635b_of_region F hA1 hdet h1,
      f03, t16_04_of_region F hA1 hdet h1 h8, f05,
      t16_06_of_region F hA1 hdet h1 h8, t16_07_of_region F hA1 hdet h1 h8,
      f08, f09, f10, f11, f12, t16_13_of_region F hA1 hdet h1 h8⟩

private theorem det24_neg' (x : Fin 7 → ℝ³) : det24 (fun i => -x i) = -det24 x := by
  simp only [det24, vol3, PiLp.sub_apply, PiLp.neg_apply]; ring

private theorem oblX0_neg' (x : Fin 7 → ℝ³) (v : Fin 7) :
    oblX0 (fun i => -x i) v = oblX0 x v := by
  simp only [oblX0, det24_neg']
  have hn : vol3 (-x v - -x 1) (-x 2 - -x 1) (-x 6 - -x 1) =
      -vol3 (x v - x 1) (x 2 - x 1) (x 6 - x 1) := by
    simp only [vol3, PiLp.sub_apply, PiLp.neg_apply]; ring
  rw [hn, neg_div_neg_eq]

/-- **Main A1 tie theorem with the reduced bundle** (same shape as `a1_tie_rupert`). -/
theorem a1_tie_rupert_small {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (hR : Hole24R x F) (hA1 : Reg.A1 x F) (htie : ⟪x 2 - x 5, x 5 - x 0⟫ = 0)
    (hS : if 0 < det24 x then A1TieSmall x F else A1TieSmall (fun i => -x i) (facNeg F)) :
    IsRupert (univ.image x) := by
  refine a1_tie_rupert F hR hA1 htie ?_
  by_cases hpos : 0 < det24 x
  · simp only [hpos, ite_true] at hS ⊢
    exact a1TieSample_of_small F hA1 hpos hS
  · simp only [hpos, ite_false] at hS ⊢
    have hne : det24 x ≠ 0 := (type24OfFac F).det_ne
    have hneg : det24 x < 0 := lt_of_le_of_ne (not_lt.1 hpos) hne
    have hpos' : 0 < det24 (fun i => -x i) := by rw [det24_neg']; linarith
    have hA1' : Reg.A1 (fun i => -x i) (facNeg F) := by
      refine ⟨?_, ?_⟩
      · rw [oblX0_neg']; exact hA1.1
      · simpa [facNeg] using hA1.2
    exact a1TieSample_of_small (facNeg F) hA1' hpos' hS

end Minimality.T24.A1
