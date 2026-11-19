module

public import Minimality.LemmaTQChart
public import Minimality.FrontDiag
public import Minimality.LemmaCA

@[expose] public section

/-!
# Lemma TQ (type 24, obtuse corner OB1)

TQPROOF24.md (fourth pass and "Shape facts", 2026-11-19).  For a type-24 solid with the
orthocentre view `c* = H 1` of the corner 1 in the region `04325` (front set `{0345, 235}`), the
3-rim cells `{235}`, `{346}`, `{025}` empty (non-TCOV) and `G_ab, G_bc ≤ 0`, Q4 holds on the cell
`0234` or on `0536` at one point, hence `IsRupert` (Lemma FD supplies the positive form).

The proof is the chart layer `Minimality.LemmaTQChart` (Lemmas A1, A1', A2, B, C, WT, CA and the
assembly `tq_chart`); this file is the bridge from the solid to the chart:
* `v3_3d`: the vertex-figure relation V3 at vertex 3 (Cramer's rule plus the edge signs);
* `mkCh`: the chart data (normalized facet normals, `y3`, `θ`, `θb`, `γ`, V3);
* `lemmaTQ_04325`: the theorem.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace

namespace Minimality.T24.TQ
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.RimCell Minimality.T24.Cell0234
  Minimality.T24.FrontDiag

theorem ip (a b : ℝ³) : ⟪a, b⟫ = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := FrontDiag.ip3 a b

/-- Determinant of three vectors (rows). -/
def dt (a b c : ℝ³) : ℝ :=
  a 0 * (b 1 * c 2 - b 2 * c 1) - a 1 * (b 0 * c 2 - b 2 * c 0) + a 2 * (b 0 * c 1 - b 1 * c 0)

/-- **Lemma V3** (vertex figure at a 4-valent vertex): four facet normals `A B C D` in cyclic order
around the vertex, with edges `e1 = A ∩ B`, `e2 = B ∩ C`, `e3 = C ∩ D` (each strictly beneath the
two other facets; the fourth edge `D ∩ A` is not needed), satisfy `k1 A + k3 C = k2 B + k4 D` with `k > 0`. -/
theorem v3_3d {A B C D e1 e2 e3 : ℝ³} (h1A : ⟪A, e1⟫ = 0) (h1B : ⟪B, e1⟫ = 0)
    (h1C : ⟪C, e1⟫ < 0) (h1D : ⟪D, e1⟫ < 0) (h2B : ⟪B, e2⟫ = 0) (h2C : ⟪C, e2⟫ = 0)
    (h2A : ⟪A, e2⟫ < 0) (h2D : ⟪D, e2⟫ < 0) (h3C : ⟪C, e3⟫ = 0) (h3D : ⟪D, e3⟫ = 0)
    (h3A : ⟪A, e3⟫ < 0) (h3B : ⟪B, e3⟫ < 0) :
    ∃ k1 k2 k3 k4 : ℝ, 0 < k1 ∧ 0 < k2 ∧ 0 < k3 ∧ 0 < k4 ∧
      ∀ w : ℝ³, k1 * ⟪A, w⟫ + k3 * ⟪C, w⟫ = k2 * ⟪B, w⟫ + k4 * ⟪D, w⟫ := by
  set lA := dt B C D
  set lB := -dt A C D
  set lC := dt A B D
  set lD := -dt A B C
  have rel : ∀ w : ℝ³, lA * ⟪A, w⟫ + lB * ⟪B, w⟫ + lC * ⟪C, w⟫ + lD * ⟪D, w⟫ = 0 := by
    intro w; simp only [lA, lB, lC, lD, ip, dt]; ring
  have cb : lA * dt e2 e3 e1 =
      ⟪B, e2⟫ * (⟪C, e3⟫ * ⟪D, e1⟫ - ⟪C, e1⟫ * ⟪D, e3⟫) -
        ⟪B, e3⟫ * (⟪C, e2⟫ * ⟪D, e1⟫ - ⟪C, e1⟫ * ⟪D, e2⟫) +
        ⟪B, e1⟫ * (⟪C, e2⟫ * ⟪D, e3⟫ - ⟪C, e3⟫ * ⟪D, e2⟫) := by
    simp only [lA, ip, dt]; ring
  rw [h2B, h2C, h3C, h3D, h1B] at cb
  have hneg : lA * dt e2 e3 e1 < 0 := by
    rw [cb]; nlinarith [mul_pos (mul_pos_of_neg_of_neg h3B h1C) (neg_pos.2 h2D)]
  have hlA : lA ≠ 0 := by rintro h; rw [h, zero_mul] at hneg; exact lt_irrefl _ hneg
  have r1 := rel e1
  have r2 := rel e2
  have r3 := rel e3
  rw [h1A, h1B] at r1
  rw [h2B, h2C] at r2
  rw [h3C, h3D] at r3
  rcases lt_or_gt_of_ne hlA with h | h
  · have hD : 0 < lD := by nlinarith
    have hB : 0 < lB := by nlinarith
    have hC : lC < 0 := by nlinarith
    refine ⟨-lA, lB, -lC, lD, by linarith, hB, by linarith, hD, fun w => ?_⟩
    linear_combination -(rel w)
  · have hD : lD < 0 := by nlinarith
    have hB : lB < 0 := by nlinarith
    have hC : 0 < lC := by nlinarith
    refine ⟨lA, -lB, lC, -lD, h, by linarith, hC, by linarith, fun w => ?_⟩
    linear_combination rel w

section Bridge
variable {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)

/-- The chart view `a (x0 - x1) + b (x2 - x1) + c (x6 - x1)`. -/
noncomputable def vw (x : Fin 7 → ℝ³) (a b c : ℝ) : ℝ³ := a • (x 0 - x 1) + b • (x 2 - x 1) + c • (x 6 - x 1)

/-- Normalizer `-f_t(x1) > 0` of a facet not through vertex 1. -/
def kap (t : Fin 9) : ℝ := -F.f t (x 1)
/-- Normalized chart normal entry `<N_t, x_i - x_1> / kap t`. -/
noncomputable def nr (t : Fin 9) (i : Fin 7) : ℝ := 1 + F.f t (x i) / kap F t

theorem kap_pos (t : Fin 9) (ht : (1 : Fin 7) ∉ s0x_S24 t) : 0 < kap F t := by
  unfold kap; linarith [F.neg t 1 ht]

theorem inner_nr (t : Fin 9) (ht : (1 : Fin 7) ∉ s0x_S24 t) (i : Fin 7) :
    ⟪F.N t, x i - x 1⟫ = kap F t * nr F t i := by
  rw [F.inner_sub]
  have := (kap_pos F t ht).ne'
  unfold nr; field_simp; unfold kap; ring

theorem nr_on (t : Fin 9) (i : Fin 7) (hi : i ∈ s0x_S24 t) : nr F t i = 1 := by
  simp [nr, F.zero t i hi]

theorem nr_off (t : Fin 9) (ht : (1 : Fin 7) ∉ s0x_S24 t) (i : Fin 7) (hi : i ∉ s0x_S24 t) :
    nr F t i < 1 := by
  have h1 := F.neg t i hi
  have h2 := kap_pos F t ht
  unfold nr
  have : F.f t (x i) / kap F t < 0 := div_neg_of_neg_of_pos h1 h2
  linarith

theorem facet_vw (t : Fin 9) (ht : (1 : Fin 7) ∉ s0x_S24 t) (a b c : ℝ) :
    ⟪F.N t, vw x a b c⟫ = kap F t * L3 (nr F t 0) (nr F t 2) (nr F t 6) a b c := by
  simp only [vw, inner_add_right, real_inner_smul_right, inner_nr F t ht, L3]; ring

theorem facet0_vw (a b c : ℝ) : ⟪F.N 0, vw x a b c⟫ = c * F.f 0 (x 6) := by
  simp only [vw, inner_add_right, real_inner_smul_right, F.inner_sub,
    F.zero 0 0 (by decide), F.zero 0 1 (by decide), F.zero 0 2 (by decide)]; ring
theorem facet1_vw (a b c : ℝ) : ⟪F.N 1, vw x a b c⟫ = b * F.f 1 (x 2) := by
  simp only [vw, inner_add_right, real_inner_smul_right, F.inner_sub,
    F.zero 1 0 (by decide), F.zero 1 1 (by decide), F.zero 1 6 (by decide)]; ring
theorem facet5_vw (a b c : ℝ) : ⟪F.N 5, vw x a b c⟫ = a * F.f 5 (x 0) := by
  simp only [vw, inner_add_right, real_inner_smul_right, F.inner_sub,
    F.zero 5 1 (by decide), F.zero 5 2 (by decide), F.zero 5 6 (by decide)]; ring

theorem inner_vw_left (a b c : ℝ) (w : ℝ³) :
    ⟪vw x a b c, w⟫ = a * ⟪x 0 - x 1, w⟫ + b * ⟪x 2 - x 1, w⟫ + c * ⟪x 6 - x 1, w⟫ := by
  simp only [vw, inner_add_left, real_inner_smul_left]

/-- Incidences: `<n_t, y_i> = nr t i` in the chart. -/
theorem incid {y : Fin 7 → Fin 3 → ℝ} (hxy : ∀ i, x i - x 1 = vw x (y i 0) (y i 1) (y i 2))
    (t : Fin 9) (ht : (1 : Fin 7) ∉ s0x_S24 t) (i : Fin 7) :
    L3 (nr F t 0) (nr F t 2) (nr F t 6) (y i 0) (y i 1) (y i 2) = nr F t i := by
  have h1 := inner_nr F t ht i
  rw [hxy i, facet_vw F t ht] at h1
  exact mul_left_cancel₀ (kap_pos F t ht).ne' h1

theorem y0_pos (F : S0xFac 9 s0x_S24 x) {y : Fin 7 → Fin 3 → ℝ} (hxy : ∀ i, x i - x 1 = vw x (y i 0) (y i 1) (y i 2))
    (i : Fin 7) (hi : i ∉ s0x_S24 5) : 0 < y i 0 := by
  have h := F.inner_sub 5 i 1
  rw [hxy i, facet5_vw, F.zero 5 1 (by decide)] at h
  have h1 := F.neg 5 i hi
  have h0 := F.neg 5 0 (by decide)
  nlinarith
theorem y1_pos (F : S0xFac 9 s0x_S24 x) {y : Fin 7 → Fin 3 → ℝ} (hxy : ∀ i, x i - x 1 = vw x (y i 0) (y i 1) (y i 2))
    (i : Fin 7) (hi : i ∉ s0x_S24 1) : 0 < y i 1 := by
  have h := F.inner_sub 1 i 1
  rw [hxy i, facet1_vw, F.zero 1 1 (by decide)] at h
  have h1 := F.neg 1 i hi
  have h0 := F.neg 1 2 (by decide)
  nlinarith
theorem y2_pos (F : S0xFac 9 s0x_S24 x) {y : Fin 7 → Fin 3 → ℝ} (hxy : ∀ i, x i - x 1 = vw x (y i 0) (y i 1) (y i 2))
    (i : Fin 7) (hi : i ∉ s0x_S24 0) : 0 < y i 2 := by
  have h := F.inner_sub 0 i 1
  rw [hxy i, facet0_vw, F.zero 0 1 (by decide)] at h
  have h1 := F.neg 0 i hi
  have h0 := F.neg 0 6 (by decide)
  nlinarith

/-- The chart data of the solid at the corner 1 (frame `04325`). -/
theorem exists_ch {y : Fin 7 → Fin 3 → ℝ} (hxy : ∀ i, x i - x 1 = vw x (y i 0) (y i 1) (y i 2)) :
    ∃ S : Ch24, S.a3 = y 3 0 ∧ S.b3 = y 3 1 ∧ S.c3 = y 3 2 ∧
      (∀ a b c, ⟪F.N 2, vw x a b c⟫ = kap F 2 * S.f025 a b c) ∧
      (∀ a b c, ⟪F.N 3, vw x a b c⟫ = kap F 3 * S.f4350 a b c) ∧
      (∀ a b c, ⟪F.N 4, vw x a b c⟫ = kap F 4 * S.f046 a b c) ∧
      (∀ a b c, ⟪F.N 6, vw x a b c⟫ = kap F 6 * S.f235 a b c) ∧
      (∀ a b c, ⟪F.N 7, vw x a b c⟫ = kap F 7 * S.f236 a b c) ∧
      (∀ a b c, ⟪F.N 8, vw x a b c⟫ = kap F 8 * S.f346 a b c) := by
  -- V3 at vertex 3
  have z : ∀ t : Fin 9, ∀ i j : Fin 7, i ∈ s0x_S24 t → j ∈ s0x_S24 t → ⟪F.N t, x i - x j⟫ = 0 :=
    fun t i j hi hj => perp24 F t i j hi hj
  have ng : ∀ t : Fin 9, ∀ i : Fin 7, i ∉ s0x_S24 t → (3 : Fin 7) ∈ s0x_S24 t →
      ⟪F.N t, x i - x 3⟫ < 0 := by
    intro t i hi h3; rw [F.inner_sub, F.zero t 3 h3]; linarith [F.neg t i hi]
  obtain ⟨K1, K2, K3, K4, hK1, hK2, hK3, hK4, hrel⟩ := v3_3d (A := F.N 3) (B := F.N 6) (C := F.N 7)
    (D := F.N 8) (e1 := x 5 - x 3) (e2 := x 2 - x 3) (e3 := x 6 - x 3)
    (z 3 5 3 (by decide) (by decide)) (z 6 5 3 (by decide) (by decide)) (ng 7 5 (by decide) (by decide))
    (ng 8 5 (by decide) (by decide)) (z 6 2 3 (by decide) (by decide)) (z 7 2 3 (by decide) (by decide))
    (ng 3 2 (by decide) (by decide)) (ng 8 2 (by decide) (by decide)) (z 7 6 3 (by decide) (by decide))
    (z 8 6 3 (by decide) (by decide)) (ng 3 6 (by decide) (by decide)) (ng 6 6 (by decide) (by decide))
  have k3 := kap_pos F 3 (by decide)
  have k6 := kap_pos F 6 (by decide)
  have k7 := kap_pos F 7 (by decide)
  have k8 := kap_pos F 8 (by decide)
  have rv : ∀ i : Fin 7, K1 * (kap F 3 * nr F 3 i) + K3 * (kap F 7 * nr F 7 i) =
      K2 * (kap F 6 * nr F 6 i) + K4 * (kap F 8 * nr F 8 i) := by
    intro i
    have h := hrel (x i - x 1)
    rwa [inner_nr F 3 (by decide), inner_nr F 6 (by decide), inner_nr F 7 (by decide),
      inner_nr F 8 (by decide)] at h
  have r0 := rv 0
  have r2 := rv 2
  have r6 := rv 6
  rw [nr_on F 3 0 (by decide)] at r0
  rw [nr_on F 6 2 (by decide), nr_on F 7 2 (by decide)] at r2
  rw [nr_on F 7 6 (by decide), nr_on F 8 6 (by decide)] at r6
  -- incidences
  have I6 := incid F hxy 6 (by decide) 3
  rw [nr_on F 6 2 (by decide), nr_on F 6 3 (by decide)] at I6
  have I7 := incid F hxy 7 (by decide) 3
  rw [nr_on F 7 2 (by decide), nr_on F 7 6 (by decide), nr_on F 7 3 (by decide)] at I7
  have I3 := incid F hxy 3 (by decide) 3
  rw [nr_on F 3 0 (by decide), nr_on F 3 3 (by decide)] at I3
  have I8 := incid F hxy 8 (by decide) 3
  rw [nr_on F 8 6 (by decide), nr_on F 8 3 (by decide)] at I8
  have I2 := incid F hxy 2 (by decide) 3
  rw [nr_on F 2 0 (by decide), nr_on F 2 2 (by decide)] at I2
  have O2 := nr_off F 2 (by decide) 3 (by decide)
  have I4 := incid F hxy 4 (by decide) 3
  rw [nr_on F 4 0 (by decide), nr_on F 4 6 (by decide)] at I4
  have O4 := nr_off F 4 (by decide) 3 (by decide)
  have J4 := incid F hxy 4 (by decide) 4
  rw [nr_on F 4 0 (by decide), nr_on F 4 6 (by decide), nr_on F 4 4 (by decide)] at J4
  have J3 := incid F hxy 3 (by decide) 4
  rw [nr_on F 3 0 (by decide), nr_on F 3 4 (by decide)] at J3
  have b4 := y1_pos F hxy 4 (by decide)
  have c4 := y2_pos F hxy 4 (by decide)
  have hp := nr_off F 2 (by decide) 6 (by decide)
  have hq := nr_off F 4 (by decide) 2 (by decide)
  have hr := nr_off F 7 (by decide) 0 (by decide)
  have hm1 := nr_off F 3 (by decide) 2 (by decide)
  have hm2 := nr_off F 3 (by decide) 6 (by decide)
  simp only [L3] at I6 I7 I3 I8 I2 I4 J4 J3
  refine ⟨{
    p := nr F 2 6, q := nr F 4 2, r := nr F 7 0, m1 := nr F 3 2, m2 := nr F 3 6,
    s0 := nr F 6 0, s2 := nr F 6 6, w0 := nr F 8 0, w1 := nr F 8 2,
    a3 := y 3 0, b3 := y 3 1, c3 := y 3 2,
    th := 1 / (1 - nr F 7 0), thb := 1 / (1 - nr F 4 2), ga := 1 / (1 - nr F 2 6),
    k1 := K1 * kap F 3, k2 := K2 * kap F 6, k3 := K3 * kap F 7, k4 := K4 * kap F 8,
    hp := hp, hq := hq, hr := hr, hm1 := hm1, hm2 := hm2,
    hs0 := nr_off F 6 (by decide) 0 (by decide), hs2 := nr_off F 6 (by decide) 6 (by decide),
    hw1 := nr_off F 8 (by decide) 2 (by decide),
    hth := one_div_mul_cancel (by linarith), hthb := one_div_mul_cancel (by linarith),
    hga := one_div_mul_cancel (by linarith),
    ha3 := y0_pos F hxy 3 (by decide), hb3 := y1_pos F hxy 3 (by decide),
    hc3 := y2_pos F hxy 3 (by decide),
    i235 := by linarith, i236 := by linarith, i4350 := by linarith, i346 := by linarith,
    o025 := by linarith, o046 := by linarith,
    hqm := by nlinarith [mul_pos (show 0 < 1 - nr F 3 6 by linarith) c4],
    hk1 := mul_pos hK1 k3, hk2 := mul_pos hK2 k6, hk3 := mul_pos hK3 k7, hk4 := mul_pos hK4 k8,
    v0 := by linear_combination r0, v1 := by linear_combination r2,
    v2 := by linear_combination r6 }, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b c; rw [facet_vw F 2 (by decide), nr_on F 2 0 (by decide), nr_on F 2 2 (by decide)]; rfl
  · intro a b c; rw [facet_vw F 3 (by decide), nr_on F 3 0 (by decide)]; rfl
  · intro a b c; rw [facet_vw F 4 (by decide), nr_on F 4 0 (by decide), nr_on F 4 6 (by decide)]; rfl
  · intro a b c; rw [facet_vw F 6 (by decide), nr_on F 6 2 (by decide)]; rfl
  · intro a b c; rw [facet_vw F 7 (by decide), nr_on F 7 2 (by decide), nr_on F 7 6 (by decide)]; rfl
  · intro a b c; rw [facet_vw F 8 (by decide), nr_on F 8 6 (by decide)]; rfl

/-- Positive facet normalizers (`012`, `016`, `126` use the far vertex). -/
noncomputable def kp (t : Fin 9) : ℝ :=
  ![-F.f 0 (x 6), -F.f 1 (x 2), kap F 2, kap F 3, kap F 4, -F.f 5 (x 0), kap F 6, kap F 7, kap F 8] t

/-- Chart facings of all nine facets (`012`, `016`, `126`: `-g_c`, `-g_b`, `-g_a`). -/
def chf (S : Ch24) (a b c : ℝ) (t : Fin 9) : ℝ :=
  ![-c, -b, S.f025 a b c, S.f4350 a b c, S.f046 a b c, -a, S.f235 a b c, S.f236 a b c,
    S.f346 a b c] t

theorem kp_pos (t : Fin 9) : 0 < kp F t := by
  fin_cases t <;> simp only [kp, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]
  · linarith [F.neg 0 6 (by decide)]
  · linarith [F.neg 1 2 (by decide)]
  · exact kap_pos F 2 (by decide)
  · exact kap_pos F 3 (by decide)
  · exact kap_pos F 4 (by decide)
  · linarith [F.neg 5 0 (by decide)]
  · exact kap_pos F 6 (by decide)
  · exact kap_pos F 7 (by decide)
  · exact kap_pos F 8 (by decide)

theorem facing_vw {S : Ch24}
    (e2 : ∀ a b c, ⟪F.N 2, vw x a b c⟫ = kap F 2 * S.f025 a b c)
    (e3 : ∀ a b c, ⟪F.N 3, vw x a b c⟫ = kap F 3 * S.f4350 a b c)
    (e4 : ∀ a b c, ⟪F.N 4, vw x a b c⟫ = kap F 4 * S.f046 a b c)
    (e6 : ∀ a b c, ⟪F.N 6, vw x a b c⟫ = kap F 6 * S.f235 a b c)
    (e7 : ∀ a b c, ⟪F.N 7, vw x a b c⟫ = kap F 7 * S.f236 a b c)
    (e8 : ∀ a b c, ⟪F.N 8, vw x a b c⟫ = kap F 8 * S.f346 a b c) (a b c : ℝ) (t : Fin 9) :
    ⟪F.N t, vw x a b c⟫ = kp F t * chf S a b c t := by
  fin_cases t <;> simp only [kp, chf, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]
  · rw [facet0_vw]; ring
  · rw [facet1_vw]; ring
  · exact e2 a b c
  · exact e3 a b c
  · exact e4 a b c
  · rw [facet5_vw]; ring
  · exact e6 a b c
  · exact e7 a b c
  · exact e8 a b c

omit F in
theorem gramC (p q s r : ℝ³) :
    ⟪q - p, s - p⟫ = ⟪p - r, p - r⟫ - ⟪p - r, q - r⟫ - ⟪p - r, s - r⟫ + ⟪q - r, s - r⟫ := by
  have e1 : q - p = (q - r) - (p - r) := by abel
  have e2 : s - p = (s - r) - (p - r) := by abel
  rw [e1, e2]
  generalize p - r = a
  generalize q - r = b
  generalize s - r = c
  rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_comm b a]
  ring

/-- Cell membership of a chart view from the chart facings. -/
theorem cellAt_of_chf {S : Ch24} (hfac : ∀ a b c t, ⟪F.N t, vw x a b c⟫ = kp F t * chf S a b c t)
    {U Dn : Finset (Fin 9)} {a b c : ℝ} (hU : ∀ t ∈ U, 0 < chf S a b c t)
    (hD : ∀ t ∈ Dn, chf S a b c t < 0) : CellAt F U Dn (vw x a b c) :=
  ⟨fun t ht => by rw [hfac]; exact mul_pos (kp_pos F t) (hU t ht),
   fun t ht => by rw [hfac]; exact mul_neg_of_pos_of_neg (kp_pos F t) (hD t ht)⟩

theorem cellLe_of_chf {S : Ch24} (hfac : ∀ a b c t, ⟪F.N t, vw x a b c⟫ = kp F t * chf S a b c t)
    {U Dn : Finset (Fin 9)} {a b c : ℝ} (hU : ∀ t ∈ U, 0 ≤ chf S a b c t)
    (hD : ∀ t ∈ Dn, chf S a b c t ≤ 0) : CellLe F U Dn (vw x a b c) :=
  ⟨fun t ht => by rw [hfac]; exact mul_nonneg (kp_pos F t).le (hU t ht),
   fun t ht => by rw [hfac]; exact mul_nonpos_of_nonneg_of_nonpos (kp_pos F t).le (hD t ht)⟩

theorem chf_of_cellAt {S : Ch24} (hfac : ∀ a b c t, ⟪F.N t, vw x a b c⟫ = kp F t * chf S a b c t)
    {U Dn : Finset (Fin 9)} {a b c : ℝ} (h : CellAt F U Dn (vw x a b c)) :
    (∀ t ∈ U, 0 < chf S a b c t) ∧ ∀ t ∈ Dn, chf S a b c t < 0 :=
  ⟨fun t ht => by have := h.1 t ht; rw [hfac] at this; exact pos_of_mul_pos_right this (kp_pos F t).le,
   fun t ht => by have := h.2 t ht; rw [hfac] at this; exact neg_of_mul_neg_right this (kp_pos F t).le⟩

/-- **Lemma TQ, frame `04325`.**  Type-24 solid `x`, corner 1 with linearly independent edges,
`G_ab = <x0 - x1, x2 - x1> ≤ 0`, `G_bc = <x2 - x1, x6 - x1> ≤ 0` (`G_ac` free), orthocentre view `u`
(`<x_e - x1, u> = 1`) in the region `04325` (front facets exactly `0345` and `235`), the 3-rim cells
with front sets `{235}`, `{346}`, `{025}` empty.  Then `IsRupert`: Q4 holds
on the cell `0234` (at one point, `z0 < z2` or `z3 < z2`) or on `0536` (`z0 < z6`). -/
theorem lemmaTQ_04325 (hx : Function.Injective x)
    (hli : LinearIndependent ℝ ![x 0 - x 1, x 2 - x 1, x 6 - x 1])
    (hab : ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0) (hbc : ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0)
    {u : ℝ³} (hu : ∀ e, ⟪![x 0 - x 1, x 2 - x 1, x 6 - x 1] e, u⟫ = 1)
    (hR : CellAt F {3, 6} {0, 1, 2, 4, 5, 7, 8} u)
    (hNo235 : ∀ w, ¬ CellAt F {6} {0, 1, 2, 3, 4, 5, 7, 8} w)
    (hNo346 : ∀ w, ¬ CellAt F {8} {0, 1, 2, 3, 4, 5, 6, 7} w)
    (hNo025 : ∀ w, ¬ CellAt F {2} {0, 1, 3, 4, 5, 6, 7, 8} w) :
    IsRupert (Finset.univ.image x) := by
  -- coordinates along the corner edges
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ ℝ³ := by simp
  set B := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hcoe : ⇑B = ![x 0 - x 1, x 2 - x 1, x 6 - x 1] :=
    coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hrep : ∀ w : ℝ³, w = vw x (B.repr w 0) (B.repr w 1) (B.repr w 2) := by
    intro w
    have h := B.sum_repr w
    rw [hcoe, Fin.sum_univ_three] at h
    simpa [vw] using h.symm
  have hinj : ∀ a b c, vw x a b c = 0 → a = 0 ∧ b = 0 ∧ c = 0 := by
    intro a b c h
    have := Fintype.linearIndependent_iff.mp hli ![a, b, c]
      (by simpa [Fin.sum_univ_three, vw] using h)
    exact ⟨by simpa using this 0, by simpa using this 1, by simpa using this 2⟩
  set y : Fin 7 → Fin 3 → ℝ := fun i e => B.repr (x i - x 1) e
  have hxy : ∀ i, x i - x 1 = vw x (y i 0) (y i 1) (y i 2) := fun i => hrep _
  obtain ⟨S, ha3, hb3, hc3, e2, e3, e4, e6, e7, e8⟩ := exists_ch F hxy
  have hfac := facing_vw F e2 e3 e4 e6 e7 e8
  -- Gram entries and depths
  set G00 := ⟪x 0 - x 1, x 0 - x 1⟫
  set G01 := ⟪x 0 - x 1, x 2 - x 1⟫
  set G02 := ⟪x 0 - x 1, x 6 - x 1⟫
  set G11 := ⟪x 2 - x 1, x 2 - x 1⟫
  set G12 := ⟪x 2 - x 1, x 6 - x 1⟫
  set G22 := ⟪x 6 - x 1, x 6 - x 1⟫
  have d0 : ∀ a b c, ⟪x 0 - x 1, vw x a b c⟫ = G00 * a + G01 * b + G02 * c := by
    intro a b c; simp only [vw, inner_add_right, real_inner_smul_right]; ring
  have d2 : ∀ a b c, ⟪x 2 - x 1, vw x a b c⟫ = G01 * a + G11 * b + G12 * c := by
    intro a b c; simp only [vw, inner_add_right, real_inner_smul_right, G01]
    rw [real_inner_comm (x 0 - x 1)]; ring
  have d6 : ∀ a b c, ⟪x 6 - x 1, vw x a b c⟫ = G02 * a + G12 * b + G22 * c := by
    intro a b c; simp only [vw, inner_add_right, real_inner_smul_right, G02, G12]
    rw [real_inner_comm (x 0 - x 1), real_inner_comm (x 2 - x 1)]; ring
  -- the orthocentre in the chart
  set c0 := B.repr u 0
  set c1 := B.repr u 1
  set c2 := B.repr u 2
  have hu' : u = vw x c0 c1 c2 := hrep u
  have q0 : G00 * c0 + G01 * c1 + G02 * c2 = 1 := by have := hu 0; rw [hu'] at this; simpa [d0] using this
  have q1 : G01 * c0 + G11 * c1 + G12 * c2 = 1 := by have := hu 1; rw [hu'] at this; simpa [d2] using this
  have q2 : G02 * c0 + G12 * c1 + G22 * c2 = 1 := by have := hu 2; rw [hu'] at this; simpa [d6] using this
  rw [hu'] at hR
  obtain ⟨hRU, hRD⟩ := chf_of_cellAt F hfac hR
  have hc2 : 0 < c2 := by have := hRD 0 (by decide); simp [chf] at this; linarith
  have hc1 : 0 < c1 := by have := hRD 1 (by decide); simp [chf] at this; linarith
  have hc0 : 0 < c0 := by have := hRD 5 (by decide); simp [chf] at this; linarith
  have f4 : 0 < S.f4350 c0 c1 c2 := by simpa [chf] using hRU 3 (by decide)
  have f6 : 0 < S.f235 c0 c1 c2 := by simpa [chf] using hRU 6 (by decide)
  have f2 : S.f025 c0 c1 c2 < 0 := by simpa [chf] using hRD 2 (by decide)
  have f4' : S.f046 c0 c1 c2 < 0 := by simpa [chf] using hRD 4 (by decide)
  have f7 : S.f236 c0 c1 c2 < 0 := by simpa [chf] using hRD 7 (by decide)
  have f8 : S.f346 c0 c1 c2 < 0 := by simpa [chf] using hRD 8 (by decide)
  set σ := c0 + c1 + c2
  have hσ : 0 < σ := by positivity
  have sc : ∀ α β γ : ℝ, L3 α β γ (c0 / σ) (c1 / σ) (c2 / σ) = L3 α β γ c0 c1 c2 / σ := by
    intro α β γ; unfold L3; ring
  have hR' : S.InR (c0 / σ) (c1 / σ) (c2 / σ) := by
    refine ⟨div_pos hc0 hσ, div_pos hc1 hσ, div_pos hc2 hσ, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show 0 < L3 _ _ _ _ _ _; rw [sc]; exact div_pos f4 hσ
    · show 0 < L3 _ _ _ _ _ _; rw [sc]; exact div_pos f6 hσ
    · show L3 _ _ _ _ _ _ < 0; rw [sc]; exact div_neg_of_neg_of_pos f2 hσ
    · show L3 _ _ _ _ _ _ < 0; rw [sc]; exact div_neg_of_neg_of_pos f4' hσ
    · show L3 _ _ _ _ _ _ < 0; rw [sc]; exact div_neg_of_neg_of_pos f7 hσ
    · show L3 _ _ _ _ _ _ < 0; rw [sc]; exact div_neg_of_neg_of_pos f8 hσ
  have hts : c0 / σ + c1 / σ + c2 / σ = 1 := by
    rw [show c0 / σ + c1 / σ + c2 / σ = (c0 + c1 + c2) / σ by ring]; exact div_self hσ.ne'
  have r0 : G00 * (c0 / σ) + G01 * (c1 / σ) + G02 * (c2 / σ) = 1 / σ := by
    rw [← q0]; field_simp
  have r1 : G01 * (c0 / σ) + G11 * (c1 / σ) + G12 * (c2 / σ) = 1 / σ := by
    rw [← q1]; field_simp
  have r2 : G02 * (c0 / σ) + G12 * (c1 / σ) + G22 * (c2 / σ) = 1 / σ := by
    rw [← q2]; field_simp
  -- empty cells in the chart
  have No235 : S.No235 := by
    intro a b c ha hb hc h235 h4350 h025 h046 h236 h346
    refine hNo235 (vw x a b c) (cellAt_of_chf F hfac (fun t ht => ?_) (fun t ht => ?_))
    · simp only [Finset.mem_singleton] at ht; subst ht; simpa [chf] using h235
    · simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [chf] <;> linarith
  have No346 : S.No346 := by
    intro a b c ha hb hc h346 h4350 h235 h025 h046 h236
    refine hNo346 (vw x a b c) (cellAt_of_chf F hfac (fun t ht => ?_) (fun t ht => ?_))
    · simp only [Finset.mem_singleton] at ht; subst ht; simpa [chf] using h346
    · simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [chf] <;> linarith
  have No025 : S.No025 := by
    intro a b c ha hb hc h025 h4350 h235 h046 h236 h346
    refine hNo025 (vw x a b c) (cellAt_of_chf F hfac (fun t ht => ?_) (fun t ht => ?_))
    · simp only [Finset.mem_singleton] at ht; subst ht; simpa [chf] using h025
    · simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [chf] <;> linarith
  -- metric: |x2 - x0|², |x6 - x0|², <x2 - x0, x6 - x0>
  have hlin : LinearIndependent ℝ ![x 2 - x 0, x 6 - x 0] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have : vw x (-(s + t)) s t = 0 := by
      rw [← hst]; simp only [vw]; module
    obtain ⟨-, h1, h2⟩ := hinj _ _ _ this
    exact ⟨h1, h2⟩
  have hCS := LemmaCA.inner_sq_lt hlin
  have hA0 : 0 < ⟪x 2 - x 0, x 2 - x 0⟫ := real_inner_self_pos.2 (sub_ne_zero.2 (hx.ne (by decide)))
  have hB0 : 0 < ⟪x 6 - x 0, x 6 - x 0⟫ := real_inner_self_pos.2 (sub_ne_zero.2 (hx.ne (by decide)))
  rw [gramC (x 0) (x 2) (x 6) (x 1), gramC (x 0) (x 2) (x 2) (x 1), gramC (x 0) (x 6) (x 6) (x 1)] at hCS
  rw [gramC (x 0) (x 2) (x 2) (x 1)] at hA0
  rw [gramC (x 0) (x 6) (x 6) (x 1)] at hB0
  have hA : 0 < G00 - 2 * G01 + G11 := by linarith
  have hB : 0 < G00 - 2 * G02 + G22 := by linarith
  have hC : (G00 - G01 - G02 + G12) ^ 2 < (G00 - 2 * G01 + G11) * (G00 - 2 * G02 + G22) := by
    convert hCS using 2 <;> ring
  -- the chart theorem
  rcases tq_chart S hR' hts No235 No346 No025 (by positivity) r0 r1 r2 hab hbc hA hB hC with
    ⟨⟨a, b, c, hop⟩, g0, g1, g2, hcl, hneg⟩ | ⟨⟨a, b, c, hop⟩, g0, g1, g2, hcl, hneg⟩
  · obtain ⟨o0, o1, o2, o025, o4350, o235, o046, o236, o346⟩ := hop
    obtain ⟨l0, l1, l2, l025, l4350, l235, l046, l236, l346⟩ := hcl
    have ha : CellAt F U0234 Dn0234 (vw x a b c) := by
      refine cellAt_of_chf F hfac (fun t ht => ?_) (fun t ht => ?_)
      · simp only [U0234, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl <;> simpa [chf]
      · simp only [Dn0234, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [chf] <;> linarith
    have hg : CellLe F U0234 Dn0234 (vw x g0 g1 g2) := by
      refine cellLe_of_chf F hfac (fun t ht => ?_) (fun t ht => ?_)
      · simp only [U0234, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl <;> simpa [chf]
      · simp only [Dn0234, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [chf] <;> linarith
    refine isRupert_q4_0234_of_neg F hx ha hg ?_
    have z0 : ⟪x 0, vw x g0 g1 g2⟫ = ⟪x 1, vw x g0 g1 g2⟫ + (G00 * g0 + G01 * g1 + G02 * g2) := by
      rw [← d0, inner_sub_left]; ring
    have z2 : ⟪x 2, vw x g0 g1 g2⟫ = ⟪x 1, vw x g0 g1 g2⟫ + (G01 * g0 + G11 * g1 + G12 * g2) := by
      rw [← d2, inner_sub_left]; ring
    have z3 : ⟪x 3, vw x g0 g1 g2⟫ = ⟪x 1, vw x g0 g1 g2⟫ + (S.a3 * (G00 * g0 + G01 * g1 + G02 * g2) +
        S.b3 * (G01 * g0 + G11 * g1 + G12 * g2) + S.c3 * (G02 * g0 + G12 * g1 + G22 * g2)) := by
      have h : ⟪x 3 - x 1, vw x g0 g1 g2⟫ = ⟪vw x (y 3 0) (y 3 1) (y 3 2), vw x g0 g1 g2⟫ := by
        rw [← hxy 3]
      rw [inner_vw_left, d0, d2, d6, inner_sub_left] at h
      rw [ha3, hb3, hc3]
      linarith
    rcases hneg with h | h
    · left; rw [z0, z2]; linarith
    · right; right; left; rw [z3, z2]; linarith
  · obtain ⟨o0, o1, o2, o046, o4350, o346, o025, o235, o236⟩ := hop
    obtain ⟨l0, l1, l2, l046, l4350, l346, l025, l235, l236⟩ := hcl
    have ha : CellAt F U0536 Dn0536 (vw x a b c) := by
      refine cellAt_of_chf F hfac (fun t ht => ?_) (fun t ht => ?_)
      · simp only [U0536, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl <;> simpa [chf]
      · simp only [Dn0536, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [chf] <;> linarith
    have hg : CellLe F U0536 Dn0536 (vw x g0 g1 g2) := by
      refine cellLe_of_chf F hfac (fun t ht => ?_) (fun t ht => ?_)
      · simp only [U0536, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl <;> simpa [chf]
      · simp only [Dn0536, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [chf] <;> linarith
    refine isRupert_q4_0536_of_neg F hx ha hg (Or.inl ?_)
    have z0 : ⟪x 0, vw x g0 g1 g2⟫ = ⟪x 1, vw x g0 g1 g2⟫ + (G00 * g0 + G01 * g1 + G02 * g2) := by
      rw [← d0, inner_sub_left]; ring
    have z6 : ⟪x 6, vw x g0 g1 g2⟫ = ⟪x 1, vw x g0 g1 g2⟫ + (G02 * g0 + G12 * g1 + G22 * g2) := by
      rw [← d6, inner_sub_left]; ring
    rw [z0, z6]; linarith

end Bridge

/-! ## The mirror frame `04635` (relabelling `(2 6)(4 5)`) -/

/-- The vertex relabelling `(2 6)(4 5)`. -/
def sg : Fin 7 → Fin 7 := ![0, 1, 6, 3, 5, 4, 2]
/-- The induced facet relabelling `012 ↔ 016`, `025 ↔ 046`, `235 ↔ 346`. -/
def tg : Fin 9 → Fin 9 := ![1, 0, 4, 3, 2, 5, 8, 7, 6]

theorem sg_mem : ∀ (t : Fin 9) (i : Fin 7), i ∈ s0x_S24 t ↔ sg i ∈ s0x_S24 (tg t) := by decide
theorem tg_tg : ∀ t : Fin 9, tg (tg t) = t := by decide
theorem sg_inj : Function.Injective sg := by decide

/-- The relabelled solid `x ∘ (2 6)(4 5)` is again of type 24. -/
def relab {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : S0xFac 9 s0x_S24 (x ∘ sg) where
  f t := F.f (tg t)
  N t := F.N (tg t)
  hN t := F.hN (tg t)
  zero t i hi := F.zero (tg t) (sg i) ((sg_mem t i).1 hi)
  neg t i hi := F.neg (tg t) (sg i) (fun h => hi ((sg_mem t i).2 h))

theorem cellAt_relab {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {U D U' D' : Finset (Fin 9)} {w : ℝ³}
    (h : CellAt F U' D' w) (hU : ∀ t ∈ U, tg t ∈ U') (hD : ∀ t ∈ D, tg t ∈ D') :
    CellAt (relab F) U D w :=
  ⟨fun t ht => h.1 _ (hU t ht), fun t ht => h.2 _ (hD t ht)⟩

theorem cellAt_unrelab {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {U D U' D' : Finset (Fin 9)}
    {w : ℝ³} (h : CellAt (relab F) U D w) (hU : ∀ t ∈ U', tg t ∈ U) (hD : ∀ t ∈ D', tg t ∈ D) :
    CellAt F U' D' w :=
  ⟨fun t ht => by have := h.1 _ (hU t ht); rwa [show F.N t = F.N (tg (tg t)) by rw [tg_tg]],
   fun t ht => by have := h.2 _ (hD t ht); rwa [show F.N t = F.N (tg (tg t)) by rw [tg_tg]]⟩

/-- **Lemma TQ, frame `04635`** (mirror of `lemmaTQ_04325` under `(2 6)(4 5)`, `b ↔ c`):
orthocentre view in the region `04635` (front facets exactly `0345`, `346`), `G_ac, G_bc ≤ 0`,
the 3-rim cells `{346}`, `{235}`, `{046}` empty.  Q4 holds on `0536` or `0234`. -/
theorem lemmaTQ_04635 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hx : Function.Injective x)
    (hli : LinearIndependent ℝ ![x 0 - x 1, x 2 - x 1, x 6 - x 1])
    (hac : ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0) (hbc : ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0)
    {u : ℝ³} (hu : ∀ e, ⟪![x 0 - x 1, x 2 - x 1, x 6 - x 1] e, u⟫ = 1)
    (hR : CellAt F {3, 8} {0, 1, 2, 4, 5, 6, 7} u)
    (hNo346 : ∀ w, ¬ CellAt F {8} {0, 1, 2, 3, 4, 5, 6, 7} w)
    (hNo235 : ∀ w, ¬ CellAt F {6} {0, 1, 2, 3, 4, 5, 7, 8} w)
    (hNo046 : ∀ w, ¬ CellAt F {4} {0, 1, 2, 3, 5, 6, 7, 8} w) :
    IsRupert (Finset.univ.image x) := by
  have himg : Finset.univ.image (x ∘ sg) = Finset.univ.image x := by
    rw [← Finset.image_image, show Finset.univ.image sg = Finset.univ from
      Finset.image_univ_of_surjective (Finite.surjective_of_injective sg_inj)]
  rw [← himg]
  have hv : ![(x ∘ sg) 0 - (x ∘ sg) 1, (x ∘ sg) 2 - (x ∘ sg) 1, (x ∘ sg) 6 - (x ∘ sg) 1] =
      ![x 0 - x 1, x 2 - x 1, x 6 - x 1] ∘ Equiv.swap 1 2 := by
    funext e; fin_cases e <;> rfl
  refine lemmaTQ_04325 (relab F) (hx.comp sg_inj) (u := u) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hv]; exact hli.comp _ (Equiv.injective _)
  · exact hac
  · rw [real_inner_comm]; exact hbc
  · intro e; rw [hv]; exact hu _
  · exact cellAt_relab F hR (by decide) (by decide)
  · intro w h; exact hNo346 w (cellAt_unrelab F h (by decide) (by decide))
  · intro w h; exact hNo235 w (cellAt_unrelab F h (by decide) (by decide))
  · intro w h; exact hNo046 w (cellAt_unrelab F h (by decide) (by decide))

/-- **Lemma TQ** (type 24, obtuse corner 1): the orthocentre view in `04325` or `04635`. -/
theorem lemmaTQ {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (hx : Function.Injective x)
    (hli : LinearIndependent ℝ ![x 0 - x 1, x 2 - x 1, x 6 - x 1])
    (hab : ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0) (hac : ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0)
    (hbc : ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0)
    {u : ℝ³} (hu : ∀ e, ⟪![x 0 - x 1, x 2 - x 1, x 6 - x 1] e, u⟫ = 1)
    (hR : CellAt F {3, 6} {0, 1, 2, 4, 5, 7, 8} u ∨ CellAt F {3, 8} {0, 1, 2, 4, 5, 6, 7} u)
    (hNo235 : ∀ w, ¬ CellAt F {6} {0, 1, 2, 3, 4, 5, 7, 8} w)
    (hNo346 : ∀ w, ¬ CellAt F {8} {0, 1, 2, 3, 4, 5, 6, 7} w)
    (hNo025 : ∀ w, ¬ CellAt F {2} {0, 1, 3, 4, 5, 6, 7, 8} w)
    (hNo046 : ∀ w, ¬ CellAt F {4} {0, 1, 2, 3, 5, 6, 7, 8} w) :
    IsRupert (Finset.univ.image x) := by
  rcases hR with h | h
  · exact lemmaTQ_04325 F hx hli hab hbc hu h hNo235 hNo346 hNo025
  · exact lemmaTQ_04635 F hx hli hac hbc hu h hNo346 hNo235 hNo046

end Minimality.T24.TQ
