module

public import Minimality.TripleTieObtuse
public import Minimality.SevenTypes
public import Minimality.TriBridge
public import Minimality.CaseC09Alg

@[expose] public section

namespace Minimality.CaseC09

open Finset
open scoped RealInnerProductSpace

/-- What `TriGenPar` and `¬TriGenTieO` give. -/
theorem not_tieO_data {V Q1 Q2 : Finset ℝ³} {v : ℝ³}
    (hP : TriGenPar V Q1 Q2 v) (hT : ¬ TriGenTieO V Q1 Q2 v) :
    ∃ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ, (∀ p ∈ Q1, f1 p = 0) ∧ (∀ p ∈ V, p ∉ Q1 → f1 p < 0) ∧
      (∀ p ∈ Q2, f2 p = 0) ∧ (∀ p ∈ V, p ∉ Q2 → f2 p < 0) ∧
      ∃ e : ℝ³, e ≠ 0 ∧ f1 (v + e) = 0 ∧ f2 (v + e) = 0 ∧
        (∀ p ∈ V, ∀ q ∈ V, p ≠ q → ∀ c : ℝ, q - p = c • e →
          MidPair Q1 Q2 (fun p => ∀ p' ∈ Q1, f2 p ≤ f2 p') (fun q => ∀ q' ∈ Q2, f1 q ≤ f1 q')
            p q) ∧
        ∃ p ∈ Q1, ∃ q ∈ Q2, p ≠ q ∧ (∀ p' ∈ Q1, f2 p ≤ f2 p') ∧ (∀ q' ∈ Q2, f1 q ≤ f1 q') ∧
          ⟪p, e⟫ = ⟪q, e⟫ ∧ ⟪v, e⟫ = ⟪p, e⟫ ∧ 0 < ⟪p - v, q - v⟫ ∧ ⟪q - p, p - v⟫ ≤ 0 ∧
          ⟪p - q, q - v⟫ ≤ 0 ∧
          ¬ OneSided Q1 v p (fun y => ⟪y, e⟫) ∧ ¬ OneSided Q2 v q (fun y => ⟪y, e⟫) := by
  by_contra hcon
  apply hT
  intro f1 f2 z1 n1 z2 n2 e he e1 e2
  refine ⟨hP f1 f2 z1 n1 z2 n2 e he e1 e2, fun p hp q hq hpq h1 h2 => ?_⟩
  by_contra hn
  rw [not_or] at hn
  obtain ⟨hTie, hobt⟩ := hn
  apply hcon
  refine ⟨f1, f2, z1, n1, z2, n2, e, he, e1, e2, hP f1 f2 z1 n1 z2 n2 e he e1 e2, p, hp, q, hq,
    hpq, h1, h2, ?_⟩
  unfold TieHT at hTie
  rw [not_or] at hTie
  obtain ⟨hR, hS⟩ := hTie
  unfold TieHR at hR
  rw [not_or] at hR
  obtain ⟨hH, hK⟩ := hR
  have hpq' : ⟪p, e⟫ = ⟪q, e⟫ := by
    by_contra h
    exact hH (Or.inl h)
  have hvp : ⟪v, e⟫ = ⟪p, e⟫ := by
    by_contra h
    exact hK ⟨hpq', h⟩
  have hS' : ¬ (OneSided Q1 v p (fun y => ⟪y, e⟫) ∨ OneSided Q2 v q (fun y => ⟪y, e⟫) ∨
      0 < ⟪q - p, p - v⟫ ∨ 0 < ⟪p - q, q - v⟫) := fun h => hS ⟨hpq', hvp, h⟩
  simp only [not_or, not_lt] at hS'
  obtain ⟨o1, o2, a1, a2⟩ := hS'
  have hpos : 0 < ⟪p - v, q - v⟫ := by
    by_contra h
    exact hobt ⟨hpq', hvp, not_lt.mp h⟩
  exact ⟨hpq', hvp, hpos, a1, a2, o1, o2⟩

/-! ### The frame: coordinates along `p - v`, `q - v`, `e` -/

theorem frame_indep {f1 f2 : ℝ³ →ᵃ[ℝ] ℝ} {v p q e : ℝ³}
    (he : e ≠ 0) (h1v : f1 v = 0) (h2v : f2 v = 0) (h1p : f1 p = 0) (h2q : f2 q = 0)
    (h1e : f1 (v + e) = 0) (h2e : f2 (v + e) = 0) (h2p : f2 p ≠ 0) (h1q : f1 q ≠ 0)
    (hpe : ⟪p - v, e⟫ = 0) (hqe : ⟪q - v, e⟫ = 0) : LinearIndependent ℝ ![p - v, q - v, e] := by
  have hee : ⟪e, e⟫ ≠ 0 := inner_self_ne_zero.mpr he
  have l1p : f1.linear (p - v) = 0 := by have := aff_sub f1 v p; linarith
  have l1q : f1.linear (q - v) = f1 q := by have := aff_sub f1 v q; linarith
  have l1e : f1.linear e = 0 := by have := aff_add f1 v e; linarith
  have l2p : f2.linear (p - v) = f2 p := by have := aff_sub f2 v p; linarith
  have l2q : f2.linear (q - v) = 0 := by have := aff_sub f2 v q; linarith
  have l2e : f2.linear e = 0 := by have := aff_add f2 v e; linarith
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hg
  have a2 := congrArg f2.linear hg
  have a1 := congrArg f1.linear hg
  have a3 := congrArg (fun y => ⟪y, e⟫) hg
  simp only [map_add, map_smul, l2p, l2q, l2e, smul_eq_mul, map_zero, mul_zero, add_zero] at a2
  simp only [map_add, map_smul, l1p, l1q, l1e, smul_eq_mul, map_zero, mul_zero, zero_add,
    add_zero] at a1
  simp only [inner_add_left, inner_smul_left, hpe, hqe, inner_zero_left, mul_zero, zero_add,
    conj_trivial] at a3
  have g0 : g 0 = 0 := by
    rcases mul_eq_zero.mp a2 with h | h
    · exact h
    · exact absurd h h2p
  have g1 : g 1 = 0 := by
    rcases mul_eq_zero.mp a1 with h | h
    · exact h
    · exact absurd h h1q
  have g2 : g 2 = 0 := by
    rcases mul_eq_zero.mp a3 with h | h
    · exact h
    · exact absurd h hee
  intro i
  fin_cases i <;> assumption

theorem frame_decomp {f1 f2 : ℝ³ →ᵃ[ℝ] ℝ} {v p q e : ℝ³}
    (he : e ≠ 0) (h1v : f1 v = 0) (h2v : f2 v = 0) (h1p : f1 p = 0) (h2q : f2 q = 0)
    (h1e : f1 (v + e) = 0) (h2e : f2 (v + e) = 0) (h2p : f2 p ≠ 0) (h1q : f1 q ≠ 0)
    (hpe : ⟪p - v, e⟫ = 0) (hqe : ⟪q - v, e⟫ = 0) (w : ℝ³) :
    w - v = (f2 w / f2 p) • (p - v) + (f1 w / f1 q) • (q - v) +
      (⟪w - v, e⟫ / ⟪e, e⟫) • e := by
  have hee : ⟪e, e⟫ ≠ 0 := inner_self_ne_zero.mpr he
  have l1p : f1.linear (p - v) = 0 := by have := aff_sub f1 v p; linarith
  have l1q : f1.linear (q - v) = f1 q := by have := aff_sub f1 v q; linarith
  have l1e : f1.linear e = 0 := by have := aff_add f1 v e; linarith
  have l2p : f2.linear (p - v) = f2 p := by have := aff_sub f2 v p; linarith
  have l2q : f2.linear (q - v) = 0 := by have := aff_sub f2 v q; linarith
  have l2e : f2.linear e = 0 := by have := aff_add f2 v e; linarith
  have hli := frame_indep he h1v h2v h1p h2q h1e h2e h2p h1q hpe hqe
  have hspan : Submodule.span ℝ (Set.range ![p - v, q - v, e]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp)
  have hw : w - v ∈ Submodule.span ℝ (Set.range ![p - v, q - v, e]) := by
    rw [hspan]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hw
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hc
  have b2 := congrArg f2.linear hc
  have b1 := congrArg f1.linear hc
  have b3 := congrArg (fun y => ⟪y, e⟫) hc
  have e2 : f2.linear (w - v) = f2 w := by have := aff_sub f2 v w; linarith
  have e1 : f1.linear (w - v) = f1 w := by have := aff_sub f1 v w; linarith
  simp only [map_add, map_smul, l2p, l2q, l2e, smul_eq_mul, mul_zero, add_zero, e2] at b2
  simp only [map_add, map_smul, l1p, l1q, l1e, smul_eq_mul, mul_zero, zero_add, add_zero, e1]
    at b1
  simp only [inner_add_left, inner_smul_left, hpe, hqe, mul_zero, zero_add, conj_trivial] at b3
  have c0 : c 0 = f2 w / f2 p := by field_simp; linarith
  have c1 : c 1 = f1 w / f1 q := by field_simp; linarith
  have c2 : c 2 = ⟪w - v, e⟫ / ⟪e, e⟫ := by field_simp; linarith
  rw [← c0, ← c1, ← c2]
  exact hc.symm

/-! ### The sign and range constraints of `Shape09` from the facets (real algebra) -/

section Alg
variable {t u s r h z4 z2 z6 : ℝ}

/-- Facet `012`: the upper middle `m2+` of `F2` is above the plane `z = 0`. -/
lemma z2_pos {a b c : ℝ} (ht : 0 < t) (hs : 0 < s) (hh : 0 < h) (e1 : a * t + c * h = 0)
    (e2 : b * s + c * z2 = 0) (ha : a < 0) (hb : b < 0) : 0 < z2 := by
  have hc : 0 < c := by
    by_contra hc
    push Not at hc
    nlinarith [mul_pos ht (neg_pos.2 ha), mul_nonneg (neg_nonneg.2 hc) hh.le]
  by_contra hz
  push Not at hz
  nlinarith [mul_pos hs (neg_pos.2 hb), mul_nonneg hc.le (neg_nonneg.2 hz)]

/-- Facets `3456` and `123`: the lower middle `m1-` of `F1` is below the plane `z = 0`. -/
lemma z4_neg {φ0 a c ψ0 a' c' : ℝ} (hu1 : u < 1) (hh : 0 < h)
    (hφ0 : φ0 < 0) (hψ0 : ψ0 < 0)
    (f3 : φ0 + a = 0) (f4 : φ0 + a * u + c * z4 = 0) (f1 : φ0 + a * t + c * h < 0)
    (g3 : ψ0 + a' = 0) (g1 : ψ0 + a' * t + c' * h = 0) (g4 : ψ0 + a' * u + c' * z4 < 0) :
    z4 < 0 := by
  have ha : a = -φ0 := by linarith
  have ha' : a' = -ψ0 := by linarith
  have E1 : c * z4 = (-φ0) * (1 - u) := by rw [ha] at f4; linarith
  have E2 : c * h < (-φ0) * (1 - t) := by rw [ha] at f1; nlinarith
  have E3 : c' * h = (-ψ0) * (1 - t) := by rw [ha'] at g1; linarith
  have E4 : c' * z4 < (-ψ0) * (1 - u) := by rw [ha'] at g4; nlinarith
  have hM : 0 < -φ0 := neg_pos.2 hφ0
  have hN : 0 < -ψ0 := neg_pos.2 hψ0
  have hz : z4 ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at E1
    have : 0 < (-φ0) * (1 - u) := mul_pos hM (by linarith)
    linarith
  by_contra hneg
  push Not at hneg
  have hz4 : 0 < z4 := lt_of_le_of_ne hneg (Ne.symm hz)
  have k1 : (1 - u) * h < (1 - t) * z4 := by
    have : (-φ0) * ((1 - u) * h) < (-φ0) * ((1 - t) * z4) := by
      have := mul_lt_mul_of_pos_right E2 hz4
      nlinarith
    exact lt_of_mul_lt_mul_left this hM.le
  have k2 : (1 - t) * z4 < (1 - u) * h := by
    have : (-ψ0) * ((1 - t) * z4) < (-ψ0) * ((1 - u) * h) := by
      have := mul_lt_mul_of_pos_right E4 hh
      nlinarith
    exact lt_of_mul_lt_mul_left this hN.le
  linarith

/-- Facets `3456` (planarity) and the relation of `z4`, `z6`. -/
lemma z6_rel {φ0 a b c : ℝ} (hu1 : u < 1) (hr1 : r < 1) (hφ0 : φ0 < 0) (hz4 : z4 < 0)
    (f3 : φ0 + a = 0) (f5 : φ0 + b = 0) (f4 : φ0 + a * u + c * z4 = 0)
    (f6 : φ0 + b * r + c * z6 = 0) :
    z6 < 0 ∧ z6 * (1 - u) = (1 - r) * z4 := by
  have ha : a = -φ0 := by linarith
  have hb : b = -φ0 := by linarith
  have E1 : c * z4 = (-φ0) * (1 - u) := by rw [ha] at f4; linarith
  have E2 : c * z6 = (-φ0) * (1 - r) := by rw [hb] at f6; linarith
  have hM : 0 < -φ0 := neg_pos.2 hφ0
  have p1 : 0 < (-φ0) * (1 - u) := mul_pos hM (by linarith)
  have p2 : 0 < (-φ0) * (1 - r) := mul_pos hM (by linarith)
  have hc : c < 0 := by
    by_contra hc
    push Not at hc
    nlinarith [mul_nonneg hc (neg_nonneg.2 hz4.le)]
  refine ⟨?_, ?_⟩
  · by_contra hz
    push Not at hz
    nlinarith [mul_nonneg (neg_nonneg.2 hc.le) hz]
  · have : (-φ0) * (z6 * (1 - u)) = (-φ0) * ((1 - r) * z4) := by
      have h1 : z6 * (c * z4) = z6 * ((-φ0) * (1 - u)) := by rw [E1]
      have h2 : z4 * (c * z6) = z4 * ((-φ0) * (1 - r)) := by rw [E2]
      nlinarith
    exact mul_left_cancel₀ hM.ne' this

/-- Facet `235`: the roof `b+ < d+` of type 09. -/
lemma roof_of {χ0 a b c : ℝ} (hs1 : s < 1) (ht1 : t < 1) (hh : 0 < h) (hz2 : 0 < z2)
    (hχ0 : χ0 < 0) (f3 : χ0 + a = 0) (f5 : χ0 + b = 0) (f2 : χ0 + b * s + c * z2 = 0)
    (f1 : χ0 + a * t + c * h < 0) : h / (1 - t) < z2 / (1 - s) := by
  have ha : a = -χ0 := by linarith
  have hb : b = -χ0 := by linarith
  have E1 : c * z2 = (-χ0) * (1 - s) := by rw [hb] at f2; linarith
  have E2 : c * h < (-χ0) * (1 - t) := by rw [ha] at f1; nlinarith
  have hN : 0 < -χ0 := neg_pos.2 hχ0
  have key : (1 - s) * h < (1 - t) * z2 := by
    have : (-χ0) * ((1 - s) * h) < (-χ0) * ((1 - t) * z2) := by
      have := mul_lt_mul_of_pos_right E2 hz2
      nlinarith
    exact lt_of_mul_lt_mul_left this hN.le
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  linarith

end Alg

/-! ### The frame -/

/-- **The normal-form frame of type 09's case (c)** (FEWER-FACES-PROOFS.md §27, continued (2) §0;
labels `(v, xa, m1+, m1-, xb, m2+, m2-) = (0, 3, 1, 4, 5, 2, 6)`): the basis
`u₁ = x 3 - x 0`, `u₂ = x 5 - x 0`, `e` (the direction of the line of the planes of the faces
`0134`, `0256`) of `ℝ³`, in which the seven points are `x 0 = 0`, `x 3 = (1, 0, 0)`,
`x 5 = (0, 1, 0)`, `x 1 = (t+, 0, h+)`, `x 4 = (t-, 0, -h-)`, `x 2 = (0, s+, k+)`,
`x 6 = (0, s-, -k-)` with `S : Shape09` (the constraints of `Shape09` included, `k-` the
determined one), and the Euclidean metric is the Gram matrix of `(u₁, u₂, e)`:
`G = diag(A, g)`, `A = [[A11, A12], [A12, A22]]` with `0 < A12 ≤ min (A11, A22)`
(`inner_frame`).  The strict `A12 < A11`, `A12 < A22` (acute far angles) is *not* given by
`¬TriGenTieO`: a right far angle is allowed by `TieHT` (the paper's codimension-3 item). -/
structure Frame09 (x : Fin 7 → ℝ³) where
  e : ℝ³
  S : Shape09
  e_ne : e ≠ 0
  indep : LinearIndependent ℝ ![x 3 - x 0, x 5 - x 0, e]
  x1_eq : x 1 = x 0 + S.tp • (x 3 - x 0) + S.hp • e
  x4_eq : x 4 = x 0 + S.tm • (x 3 - x 0) - S.hm • e
  x2_eq : x 2 = x 0 + S.sp • (x 5 - x 0) + S.kp • e
  x6_eq : x 6 = x 0 + S.sm • (x 5 - x 0) - S.km • e
  inner_u1_e : ⟪x 3 - x 0, e⟫ = 0
  inner_u2_e : ⟪x 5 - x 0, e⟫ = 0
  A12_pos : 0 < ⟪x 3 - x 0, x 5 - x 0⟫
  A12_le_A11 : ⟪x 3 - x 0, x 5 - x 0⟫ ≤ ⟪x 3 - x 0, x 3 - x 0⟫
  A12_le_A22 : ⟪x 3 - x 0, x 5 - x 0⟫ ≤ ⟪x 5 - x 0, x 5 - x 0⟫

namespace Frame09

variable {x : Fin 7 → ℝ³} (F : Frame09 x)

/-- The coordinate basis `(x 3 - x 0, x 5 - x 0, e)`. -/
noncomputable def basis : Module.Basis (Fin 3) ℝ ℝ³ :=
  basisOfLinearIndependentOfCardEqFinrank F.indep (by simp)

lemma basis_apply (i : Fin 3) : F.basis i = ![x 3 - x 0, x 5 - x 0, F.e] i := by
  simp [basis]

lemma g_pos : 0 < ⟪F.e, F.e⟫ := real_inner_self_pos.mpr F.e_ne

/-- The Euclidean metric in the frame: `G = diag(A, g)`. -/
lemma inner_frame (a b c a' b' c' : ℝ) :
    ⟪a • (x 3 - x 0) + b • (x 5 - x 0) + c • F.e, a' • (x 3 - x 0) + b' • (x 5 - x 0) + c' • F.e⟫ =
      ⟪x 3 - x 0, x 3 - x 0⟫ * (a * a') + ⟪x 3 - x 0, x 5 - x 0⟫ * (a * b' + a' * b) +
        ⟪x 5 - x 0, x 5 - x 0⟫ * (b * b') + ⟪F.e, F.e⟫ * (c * c') := by
  have h1 := F.inner_u1_e
  have h2 := F.inner_u2_e
  have h1' : ⟪F.e, x 3 - x 0⟫ = 0 := by rw [real_inner_comm]; exact h1
  have h2' : ⟪F.e, x 5 - x 0⟫ = 0 := by rw [real_inner_comm]; exact h2
  have h12 : ⟪x 5 - x 0, x 3 - x 0⟫ = ⟪x 3 - x 0, x 5 - x 0⟫ := real_inner_comm _ _
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, h1, h2, h1', h2',
    h12, conj_trivial]
  ring

include F in
/-- The Gram determinant of `A` is positive (`A` is positive definite). -/
lemma A_det_pos : 0 < ⟪x 3 - x 0, x 3 - x 0⟫ * ⟪x 5 - x 0, x 5 - x 0⟫ -
    ⟪x 3 - x 0, x 5 - x 0⟫ ^ 2 := by
  have h0 := F.A12_pos
  have h1 := F.A12_le_A11
  have h2 := F.A12_le_A22
  set u1 := x 3 - x 0
  set u2 := x 5 - x 0
  have hA22 : 0 < ⟪u2, u2⟫ := h0.trans_le h2
  have hli := Fintype.linearIndependent_iff.mp F.indep
  have hw : ⟪u2, u2⟫ • u1 - ⟪u1, u2⟫ • u2 ≠ 0 := by
    intro hw
    have := hli ![⟪u2, u2⟫, -⟪u1, u2⟫, 0] (by
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, zero_smul, add_zero, neg_smul]
      rw [← sub_eq_add_neg]; exact hw) 0
    simp only [Matrix.cons_val_zero] at this
    exact hA22.ne' this
  have hpos : 0 < ⟪⟪u2, u2⟫ • u1 - ⟪u1, u2⟫ • u2, ⟪u2, u2⟫ • u1 - ⟪u1, u2⟫ • u2⟫ :=
    real_inner_self_pos.mpr hw
  have h12 : ⟪u2, u1⟫ = ⟪u1, u2⟫ := real_inner_comm _ _
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, h12,
    conj_trivial] at hpos
  have : 0 < ⟪u2, u2⟫ * (⟪u1, u1⟫ * ⟪u2, u2⟫ - ⟪u1, u2⟫ ^ 2) := by nlinarith
  exact pos_of_mul_pos_right this hA22.le

end Frame09

theorem eval_dec (φ : ℝ³ →ᵃ[ℝ] ℝ) {v p q w e : ℝ³} {X Y Z : ℝ}
    (hw : w - v = X • (p - v) + Y • (q - v) + Z • e) :
    φ w = φ v + X * (φ p - φ v) + Y * (φ q - φ v) + Z * φ.linear e := by
  have h1 := aff_sub φ v w
  have h2 := aff_sub φ v p
  have h3 := aff_sub φ v q
  rw [hw] at h1
  simp only [map_add, map_smul, smul_eq_mul] at h1
  have e2 : φ.linear (p - v) = φ p - φ v := by linarith
  have e3 : φ.linear (q - v) = φ q - φ v := by linarith
  rw [e2, e3] at h1
  linarith

/-- **The frame from the triple-tie data** (core, after the far ends are identified as
`x 3`, `x 5` and `e` is oriented so that `x 1` is above the plane of `x 0, x 3, x 5`). -/
theorem frame09_core (x : Fin 7 → ℝ³) (f1 f2 : ℝ³ →ᵃ[ℝ] ℝ)
    (hf1 : ∀ i : Fin 7, (i ∈ ({0, 1, 3, 4} : Finset (Fin 7)) → f1 (x i) = 0) ∧
      (i ∉ ({0, 1, 3, 4} : Finset (Fin 7)) → f1 (x i) < 0))
    (hf2 : ∀ i : Fin 7, (i ∈ ({0, 2, 5, 6} : Finset (Fin 7)) → f2 (x i) = 0) ∧
      (i ∉ ({0, 2, 5, 6} : Finset (Fin 7)) → f2 (x i) < 0))
    (m2 : f2 (x 3) ≤ f2 (x 1) ∧ f2 (x 3) ≤ f2 (x 4))
    (m1 : f1 (x 5) ≤ f1 (x 2) ∧ f1 (x 5) ≤ f1 (x 6))
    (e : ℝ³) (he : e ≠ 0) (h1e : f1 (x 0 + e) = 0) (h2e : f2 (x 0 + e) = 0)
    (hu1e : ⟪x 3 - x 0, e⟫ = 0) (hu2e : ⟪x 5 - x 0, e⟫ = 0)
    (par1 : ∀ c : ℝ, x 1 - x 3 ≠ c • e) (par4 : ∀ c : ℝ, x 4 - x 3 ≠ c • e)
    (par2 : ∀ c : ℝ, x 2 - x 5 ≠ c • e) (par6 : ∀ c : ℝ, x 6 - x 5 ≠ c • e)
    (a12 : 0 < ⟪x 3 - x 0, x 5 - x 0⟫) (a11 : ⟪x 5 - x 3, x 3 - x 0⟫ ≤ 0)
    (a22 : ⟪x 3 - x 5, x 5 - x 0⟫ ≤ 0) (hz : 0 < ⟪x 1 - x 0, e⟫)
    (φ012 φ123 φ235 φ3456 : ℝ³ →ᵃ[ℝ] ℝ)
    (h012 : ∀ i : Fin 7, (i ∈ ({0, 1, 2} : Finset (Fin 7)) → φ012 (x i) = 0) ∧
      (i ∉ ({0, 1, 2} : Finset (Fin 7)) → φ012 (x i) < 0))
    (h123 : ∀ i : Fin 7, (i ∈ ({1, 2, 3} : Finset (Fin 7)) → φ123 (x i) = 0) ∧
      (i ∉ ({1, 2, 3} : Finset (Fin 7)) → φ123 (x i) < 0))
    (h235 : ∀ i : Fin 7, (i ∈ ({2, 3, 5} : Finset (Fin 7)) → φ235 (x i) = 0) ∧
      (i ∉ ({2, 3, 5} : Finset (Fin 7)) → φ235 (x i) < 0))
    (h3456 : ∀ i : Fin 7, (i ∈ ({3, 4, 5, 6} : Finset (Fin 7)) → φ3456 (x i) = 0) ∧
      (i ∉ ({3, 4, 5, 6} : Finset (Fin 7)) → φ3456 (x i) < 0)) :
    Nonempty (Frame09 x) := by
  have h1v : f1 (x 0) = 0 := (hf1 0).1 (by decide)
  have h1_1 : f1 (x 1) = 0 := (hf1 1).1 (by decide)
  have h1_3 : f1 (x 3) = 0 := (hf1 3).1 (by decide)
  have h1_4 : f1 (x 4) = 0 := (hf1 4).1 (by decide)
  have n1_2 : f1 (x 2) < 0 := (hf1 2).2 (by decide)
  have n1_5 : f1 (x 5) < 0 := (hf1 5).2 (by decide)
  have n1_6 : f1 (x 6) < 0 := (hf1 6).2 (by decide)
  have h2v : f2 (x 0) = 0 := (hf2 0).1 (by decide)
  have h2_2 : f2 (x 2) = 0 := (hf2 2).1 (by decide)
  have h2_5 : f2 (x 5) = 0 := (hf2 5).1 (by decide)
  have h2_6 : f2 (x 6) = 0 := (hf2 6).1 (by decide)
  have n2_1 : f2 (x 1) < 0 := (hf2 1).2 (by decide)
  have n2_3 : f2 (x 3) < 0 := (hf2 3).2 (by decide)
  have n2_4 : f2 (x 4) < 0 := (hf2 4).2 (by decide)
  have hee : 0 < ⟪e, e⟫ := real_inner_self_pos.mpr he
  have hli := frame_indep he h1v h2v h1_3 h2_5 h1e h2e n2_3.ne n1_5.ne hu1e hu2e
  have dec := fun i => frame_decomp he h1v h2v h1_3 h2_5 h1e h2e n2_3.ne n1_5.ne hu1e hu2e (x i)
  -- the coordinates
  obtain ⟨tp, htp⟩ : ∃ r : ℝ, r = f2 (x 1) / f2 (x 3) := ⟨_, rfl⟩
  obtain ⟨tm, htm⟩ : ∃ r : ℝ, r = f2 (x 4) / f2 (x 3) := ⟨_, rfl⟩
  obtain ⟨sp, hsp⟩ : ∃ r : ℝ, r = f1 (x 2) / f1 (x 5) := ⟨_, rfl⟩
  obtain ⟨sm, hsm⟩ : ∃ r : ℝ, r = f1 (x 6) / f1 (x 5) := ⟨_, rfl⟩
  obtain ⟨hp, hhp⟩ : ∃ r : ℝ, r = ⟪x 1 - x 0, e⟫ / ⟪e, e⟫ := ⟨_, rfl⟩
  obtain ⟨z4, hz4⟩ : ∃ r : ℝ, r = ⟪x 4 - x 0, e⟫ / ⟪e, e⟫ := ⟨_, rfl⟩
  obtain ⟨kp, hkp⟩ : ∃ r : ℝ, r = ⟪x 2 - x 0, e⟫ / ⟪e, e⟫ := ⟨_, rfl⟩
  obtain ⟨z6, hz6⟩ : ∃ r : ℝ, r = ⟪x 6 - x 0, e⟫ / ⟪e, e⟫ := ⟨_, rfl⟩
  have d1 : x 1 - x 0 = tp • (x 3 - x 0) + hp • e := by
    have := dec 1
    rw [h1_1, zero_div, zero_smul, add_zero, ← htp, ← hhp] at this
    exact this
  have d4 : x 4 - x 0 = tm • (x 3 - x 0) + z4 • e := by
    have := dec 4
    rw [h1_4, zero_div, zero_smul, add_zero, ← htm, ← hz4] at this
    exact this
  have d2 : x 2 - x 0 = sp • (x 5 - x 0) + kp • e := by
    have := dec 2
    rw [h2_2, zero_div, zero_smul, zero_add, ← hsp, ← hkp] at this
    exact this
  have d6 : x 6 - x 0 = sm • (x 5 - x 0) + z6 • e := by
    have := dec 6
    rw [h2_6, zero_div, zero_smul, zero_add, ← hsm, ← hz6] at this
    exact this
  -- ranges
  have tp_pos : 0 < tp := by rw [htp]; exact div_pos_of_neg_of_neg n2_1 n2_3
  have tm_pos : 0 < tm := by rw [htm]; exact div_pos_of_neg_of_neg n2_4 n2_3
  have sp_pos : 0 < sp := by rw [hsp]; exact div_pos_of_neg_of_neg n1_2 n1_5
  have sm_pos : 0 < sm := by rw [hsm]; exact div_pos_of_neg_of_neg n1_6 n1_5
  have tp_lt : tp < 1 := by
    refine lt_of_le_of_ne ((div_le_one_of_neg n2_3).mpr m2.1 |> fun h => htp ▸ h) fun h => ?_
    apply par1 hp
    rw [h, one_smul] at d1
    rw [show x 1 - x 3 = (x 1 - x 0) - (x 3 - x 0) by abel, d1]
    abel
  have tm_lt : tm < 1 := by
    refine lt_of_le_of_ne ((div_le_one_of_neg n2_3).mpr m2.2 |> fun h => htm ▸ h) fun h => ?_
    apply par4 z4
    rw [h, one_smul] at d4
    rw [show x 4 - x 3 = (x 4 - x 0) - (x 3 - x 0) by abel, d4]
    abel
  have sp_lt : sp < 1 := by
    refine lt_of_le_of_ne ((div_le_one_of_neg n1_5).mpr m1.1 |> fun h => hsp ▸ h) fun h => ?_
    apply par2 kp
    rw [h, one_smul] at d2
    rw [show x 2 - x 5 = (x 2 - x 0) - (x 5 - x 0) by abel, d2]
    abel
  have sm_lt : sm < 1 := by
    refine lt_of_le_of_ne ((div_le_one_of_neg n1_5).mpr m1.2 |> fun h => hsm ▸ h) fun h => ?_
    apply par6 z6
    rw [h, one_smul] at d6
    rw [show x 6 - x 5 = (x 6 - x 0) - (x 5 - x 0) by abel, d6]
    abel
  have hp_pos : 0 < hp := by rw [hhp]; exact div_pos hz hee
  have sp_pos' := sp_pos
  -- evaluation of an affine functional on the coordinates
  have ev1 : ∀ φ : ℝ³ →ᵃ[ℝ] ℝ,
      φ (x 1) = φ (x 0) + tp * (φ (x 3) - φ (x 0)) + hp * φ.linear e := by
    intro φ
    have := eval_dec φ (dec 1)
    rw [h1_1, zero_div, zero_mul, add_zero, ← htp, ← hhp] at this
    exact this
  have ev4 : ∀ φ : ℝ³ →ᵃ[ℝ] ℝ,
      φ (x 4) = φ (x 0) + tm * (φ (x 3) - φ (x 0)) + z4 * φ.linear e := by
    intro φ
    have := eval_dec φ (dec 4)
    rw [h1_4, zero_div, zero_mul, add_zero, ← htm, ← hz4] at this
    exact this
  have ev2 : ∀ φ : ℝ³ →ᵃ[ℝ] ℝ,
      φ (x 2) = φ (x 0) + sp * (φ (x 5) - φ (x 0)) + kp * φ.linear e := by
    intro φ
    have := eval_dec φ (dec 2)
    rw [h2_2, zero_div, zero_mul, add_zero, ← hsp, ← hkp] at this
    exact this
  have ev6 : ∀ φ : ℝ³ →ᵃ[ℝ] ℝ,
      φ (x 6) = φ (x 0) + sm * (φ (x 5) - φ (x 0)) + z6 * φ.linear e := by
    intro φ
    have := eval_dec φ (dec 6)
    rw [h2_6, zero_div, zero_mul, add_zero, ← hsm, ← hz6] at this
    exact this
  -- facet 012
  have A0 : φ012 (x 0) = 0 := (h012 0).1 (by decide)
  have A1 : φ012 (x 1) = 0 := (h012 1).1 (by decide)
  have A2 : φ012 (x 2) = 0 := (h012 2).1 (by decide)
  have A3 : φ012 (x 3) < 0 := (h012 3).2 (by decide)
  have A5 : φ012 (x 5) < 0 := (h012 5).2 (by decide)
  have kp_pos : 0 < kp :=
    z2_pos (a := φ012 (x 3) - φ012 (x 0)) (b := φ012 (x 5) - φ012 (x 0)) (c := φ012.linear e)
      tp_pos sp_pos hp_pos (by have := ev1 φ012; linarith) (by have := ev2 φ012; linarith)
      (by linarith) (by linarith)
  -- facets 3456, 123
  have B0 : φ3456 (x 0) < 0 := (h3456 0).2 (by decide)
  have B3 : φ3456 (x 3) = 0 := (h3456 3).1 (by decide)
  have B4 : φ3456 (x 4) = 0 := (h3456 4).1 (by decide)
  have B5 : φ3456 (x 5) = 0 := (h3456 5).1 (by decide)
  have B6 : φ3456 (x 6) = 0 := (h3456 6).1 (by decide)
  have B1 : φ3456 (x 1) < 0 := (h3456 1).2 (by decide)
  have C0 : φ123 (x 0) < 0 := (h123 0).2 (by decide)
  have C1 : φ123 (x 1) = 0 := (h123 1).1 (by decide)
  have C3 : φ123 (x 3) = 0 := (h123 3).1 (by decide)
  have C4 : φ123 (x 4) < 0 := (h123 4).2 (by decide)
  have z4_neg' : z4 < 0 :=
    z4_neg (φ0 := φ3456 (x 0)) (a := φ3456 (x 3) - φ3456 (x 0)) (c := φ3456.linear e)
      (ψ0 := φ123 (x 0)) (a' := φ123 (x 3) - φ123 (x 0)) (c' := φ123.linear e)
      (t := tp) tm_lt hp_pos B0 C0 (by linarith) (by have := ev4 φ3456; linarith)
      (by have := ev1 φ3456; linarith) (by linarith) (by have := ev1 φ123; linarith)
      (by have := ev4 φ123; linarith)
  obtain ⟨z6_neg, z6_rel'⟩ :=
    z6_rel (z6 := z6) (φ0 := φ3456 (x 0)) (a := φ3456 (x 3) - φ3456 (x 0))
      (b := φ3456 (x 5) - φ3456 (x 0)) (c := φ3456.linear e) tm_lt sm_lt B0 z4_neg'
      (by linarith) (by linarith) (by have := ev4 φ3456; linarith)
      (by have := ev6 φ3456; linarith)
  -- facet 235 (the roof)
  have D0 : φ235 (x 0) < 0 := (h235 0).2 (by decide)
  have D2 : φ235 (x 2) = 0 := (h235 2).1 (by decide)
  have D3 : φ235 (x 3) = 0 := (h235 3).1 (by decide)
  have D5 : φ235 (x 5) = 0 := (h235 5).1 (by decide)
  have D1 : φ235 (x 1) < 0 := (h235 1).2 (by decide)
  have roof : hp / (1 - tp) < kp / (1 - sp) :=
    roof_of (χ0 := φ235 (x 0)) (a := φ235 (x 3) - φ235 (x 0)) (b := φ235 (x 5) - φ235 (x 0))
      (c := φ235.linear e) sp_lt tp_lt hp_pos kp_pos D0 (by linarith) (by linarith)
      (by have := ev2 φ235; linarith) (by have := ev1 φ235; linarith)
  -- the shape
  let S : Shape09 :=
    { tp := tp, tm := tm, sp := sp, sm := sm, hp := hp, hm := -z4, kp := kp
      tp_pos := tp_pos, tp_lt := tp_lt, tm_pos := tm_pos, tm_lt := tm_lt
      sp_pos := sp_pos, sp_lt := sp_lt, sm_pos := sm_pos, sm_lt := sm_lt
      hp_pos := hp_pos, hm_pos := neg_pos.2 z4_neg', kp_pos := kp_pos, roof := roof }
  have hkm : S.km = -z6 := by
    have h1 : (1 - tm) ≠ 0 := (by linarith : 0 < 1 - tm).ne'
    show (1 - sm) * (-z4) / (1 - tm) = -z6
    rw [div_eq_iff h1]
    linarith
  refine ⟨{ e := e
            S := S
            e_ne := he
            indep := hli
            x1_eq := ?_
            x4_eq := ?_
            x2_eq := ?_
            x6_eq := ?_
            inner_u1_e := hu1e
            inner_u2_e := hu2e
            A12_pos := a12
            A12_le_A11 := ?_
            A12_le_A22 := ?_ }⟩
  · show x 1 = x 0 + tp • (x 3 - x 0) + hp • e
    rw [add_assoc, ← d1]; abel
  · show x 4 = x 0 + tm • (x 3 - x 0) - (-z4) • e
    rw [neg_smul, sub_neg_eq_add, add_assoc, ← d4]; abel
  · show x 2 = x 0 + sp • (x 5 - x 0) + kp • e
    rw [add_assoc, ← d2]; abel
  · show x 6 = x 0 + sm • (x 5 - x 0) - S.km • e
    rw [hkm, neg_smul, sub_neg_eq_add, add_assoc, ← d6]; abel
  · have : ⟪x 5 - x 3, x 3 - x 0⟫ = ⟪x 5 - x 0, x 3 - x 0⟫ - ⟪x 3 - x 0, x 3 - x 0⟫ := by
      rw [← inner_sub_left]; congr 1; abel
    have c : ⟪x 5 - x 0, x 3 - x 0⟫ = ⟪x 3 - x 0, x 5 - x 0⟫ := real_inner_comm _ _
    linarith
  · have : ⟪x 3 - x 5, x 5 - x 0⟫ = ⟪x 3 - x 0, x 5 - x 0⟫ - ⟪x 5 - x 0, x 5 - x 0⟫ := by
      rw [← inner_sub_left]; congr 1; abel
    linarith


/-! ### From `TriGenPar ∧ ¬TriGenTieO` to the frame -/

lemma two_sided_real {Zm Zm' c : ℝ} (h : Zm * c < 0) (h' : Zm' * c < 0)
    (h1 : 0 ≤ Zm ∨ 0 ≤ Zm') (h2 : Zm ≤ 0 ∨ Zm' ≤ 0) : False := by
  rcases lt_trichotomy c 0 with hc | hc | hc
  · have a : 0 < Zm := by
      by_contra ha; push Not at ha; nlinarith [mul_nonneg_of_nonpos_of_nonpos ha hc.le]
    have b : 0 < Zm' := by
      by_contra ha; push Not at ha; nlinarith [mul_nonneg_of_nonpos_of_nonpos ha hc.le]
    rcases h2 with h2 | h2 <;> linarith
  · rw [hc] at h; simp at h
  · have a : Zm < 0 := by
      by_contra ha; push Not at ha; nlinarith [mul_nonneg ha hc.le]
    have b : Zm' < 0 := by
      by_contra ha; push Not at ha; nlinarith [mul_nonneg ha hc.le]
    rcases h1 with h1 | h1 <;> linarith

theorem two_sided_of_not_oneSided {Q : Finset ℝ³} {v p m m' : ℝ³} {g : ℝ³ → ℝ}
    (hQ : ∀ y ∈ Q, y = v ∨ y = p ∨ y = m ∨ y = m')
    (h : ¬ OneSided Q v p g) : (g v ≤ g m ∨ g v ≤ g m') ∧ (g m ≤ g v ∨ g m' ≤ g v) := by
  constructor
  · by_contra hc
    push Not at hc
    apply h
    refine ⟨1, Or.inl rfl, fun y hy hyv hyp => ?_⟩
    rcases hQ y hy with rfl | rfl | rfl | rfl
    · exact absurd rfl hyv
    · exact absurd rfl hyp
    · simpa using hc.1
    · simpa using hc.2
  · by_contra hc
    push Not at hc
    apply h
    refine ⟨-1, Or.inr rfl, fun y hy hyv hyp => ?_⟩
    rcases hQ y hy with rfl | rfl | rfl | rfl
    · exact absurd rfl hyv
    · exact absurd rfl hyp
    · simp only [neg_mul, one_mul, neg_lt_neg_iff]; exact hc.1
    · simp only [neg_mul, one_mul, neg_lt_neg_iff]; exact hc.2

/-- A far end of `F1` that is not the corner opposite `v` is impossible: the two other points `m`,
`m'` of the face lie on one side of the line `v p` in the plane of `F1` (the facet `φ` through `v`,
`p` is negative at both), and their depths have the same sign, against two-sidedness. -/
theorem q1_side_contra {Q1 : Finset ℝ³} {f1 f2 : ℝ³ →ᵃ[ℝ] ℝ} {v p q e m m' : ℝ³}
    (he : e ≠ 0) (h1v : f1 v = 0) (h2v : f2 v = 0) (h1p : f1 p = 0) (h2q : f2 q = 0)
    (h1e : f1 (v + e) = 0) (h2e : f2 (v + e) = 0) (h2p : f2 p ≠ 0) (h1q : f1 q ≠ 0)
    (hpe : ⟪p - v, e⟫ = 0) (hqe : ⟪q - v, e⟫ = 0)
    (hm1 : f1 m = 0) (hm1' : f1 m' = 0)
    (φ : ℝ³ →ᵃ[ℝ] ℝ) (hφv : φ v = 0) (hφp : φ p = 0) (hφm : φ m < 0) (hφm' : φ m' < 0)
    (hQ : ∀ y ∈ Q1, y = v ∨ y = p ∨ y = m ∨ y = m')
    (hos : ¬ OneSided Q1 v p (fun y => ⟪y, e⟫)) : False := by
  have hee : 0 < ⟪e, e⟫ := real_inner_self_pos.mpr he
  have ev : ∀ w, f1 w = 0 → φ w = (⟪w - v, e⟫ / ⟪e, e⟫) * φ.linear e := by
    intro w hw
    have := eval_dec φ (frame_decomp he h1v h2v h1p h2q h1e h2e h2p h1q hpe hqe w)
    rw [hw, zero_div, zero_mul, add_zero, hφv, hφp] at this
    linarith
  obtain ⟨o1, o2⟩ := two_sided_of_not_oneSided hQ hos
  beta_reduce at o1 o2
  have key : ∀ w, ⟪v, e⟫ ≤ ⟪w, e⟫ → 0 ≤ ⟪w - v, e⟫ / ⟪e, e⟫ := fun w hw => by
    rw [inner_sub_left]; exact div_nonneg (by linarith) hee.le
  have key' : ∀ w, ⟪w, e⟫ ≤ ⟪v, e⟫ → ⟪w - v, e⟫ / ⟪e, e⟫ ≤ 0 := fun w hw => by
    rw [inner_sub_left]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) hee.le
  refine two_sided_real (Zm := ⟪m - v, e⟫ / ⟪e, e⟫) (Zm' := ⟪m' - v, e⟫ / ⟪e, e⟫)
    (c := φ.linear e) (by rw [← ev m hm1]; exact hφm) (by rw [← ev m' hm1']; exact hφm') ?_ ?_
  · rcases o1 with h | h
    · exact Or.inl (key m h)
    · exact Or.inr (key m' h)
  · rcases o2 with h | h
    · exact Or.inl (key' m h)
    · exact Or.inr (key' m' h)

theorem q2_side_contra {Q2 : Finset ℝ³} {f1 f2 : ℝ³ →ᵃ[ℝ] ℝ} {v p q e m m' : ℝ³}
    (he : e ≠ 0) (h1v : f1 v = 0) (h2v : f2 v = 0) (h1p : f1 p = 0) (h2q : f2 q = 0)
    (h1e : f1 (v + e) = 0) (h2e : f2 (v + e) = 0) (h2p : f2 p ≠ 0) (h1q : f1 q ≠ 0)
    (hpe : ⟪p - v, e⟫ = 0) (hqe : ⟪q - v, e⟫ = 0)
    (hm2 : f2 m = 0) (hm2' : f2 m' = 0)
    (φ : ℝ³ →ᵃ[ℝ] ℝ) (hφv : φ v = 0) (hφq : φ q = 0) (hφm : φ m < 0) (hφm' : φ m' < 0)
    (hQ : ∀ y ∈ Q2, y = v ∨ y = q ∨ y = m ∨ y = m')
    (hos : ¬ OneSided Q2 v q (fun y => ⟪y, e⟫)) : False := by
  have hee : 0 < ⟪e, e⟫ := real_inner_self_pos.mpr he
  have ev : ∀ w, f2 w = 0 → φ w = (⟪w - v, e⟫ / ⟪e, e⟫) * φ.linear e := by
    intro w hw
    have := eval_dec φ (frame_decomp he h1v h2v h1p h2q h1e h2e h2p h1q hpe hqe w)
    rw [hw, zero_div, zero_mul, add_zero, hφv, hφq] at this
    linarith
  obtain ⟨o1, o2⟩ := two_sided_of_not_oneSided hQ hos
  beta_reduce at o1 o2
  have key : ∀ w, ⟪v, e⟫ ≤ ⟪w, e⟫ → 0 ≤ ⟪w - v, e⟫ / ⟪e, e⟫ := fun w hw => by
    rw [inner_sub_left]; exact div_nonneg (by linarith) hee.le
  have key' : ∀ w, ⟪w, e⟫ ≤ ⟪v, e⟫ → ⟪w - v, e⟫ / ⟪e, e⟫ ≤ 0 := fun w hw => by
    rw [inner_sub_left]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) hee.le
  refine two_sided_real (Zm := ⟪m - v, e⟫ / ⟪e, e⟫) (Zm' := ⟪m' - v, e⟫ / ⟪e, e⟫)
    (c := φ.linear e) (by rw [← ev m hm2]; exact hφm) (by rw [← ev m' hm2']; exact hφm') ?_ ?_
  · rcases o1 with h | h
    · exact Or.inl (key m h)
    · exact Or.inr (key m' h)
  · rcases o2 with h | h
    · exact Or.inl (key' m h)
    · exact Or.inr (key' m' h)

theorem not_midPair_far1 {Q1 Q2 : Finset ℝ³} {far1 far2 : ℝ³ → Prop} {p q : ℝ³}
    (hp1 : p ∈ Q1) (hp2 : p ∉ Q2) (hfar : far1 p) : ¬ MidPair Q1 Q2 far1 far2 p q := by
  rintro (⟨_, _, hn, _⟩ | ⟨h, _⟩ | ⟨h, _⟩)
  · exact hn hfar
  · exact hp2 h
  · exact h hp1

theorem not_midPair_far2 {Q1 Q2 : Finset ℝ³} {far1 far2 : ℝ³ → Prop} {p q : ℝ³}
    (hp2 : p ∈ Q2) (hp1 : p ∉ Q1) (hfar : far2 p) : ¬ MidPair Q1 Q2 far1 far2 p q := by
  rintro (⟨h, _⟩ | ⟨_, _, hn, _⟩ | ⟨_, h, _⟩)
  · exact hp1 h
  · exact hn hfar
  · exact h hp2

/-- **The normal-form frame of type 09's acute case (c).**  `TriGenPar` and `¬TriGenTieO` for the
faces `0134`, `0256` at the vertex `0` of a type-09 realization give the frame `Frame09 x`. -/
theorem frame09 {x : Fin 7 → ℝ³} (hx : Function.Injective x)
    (hgen : NoThreeCollinear (Finset.univ.image x))
    (hR : RealizesFaces x (sevenTypeFaces 8))
    (hP : TriGenPar (Finset.univ.image x) (({0, 1, 3, 4} : Finset (Fin 7)).image x)
      (({0, 2, 5, 6} : Finset (Fin 7)).image x) (x 0))
    (hT : ¬ TriGenTieO (Finset.univ.image x) (({0, 1, 3, 4} : Finset (Fin 7)).image x)
      (({0, 2, 5, 6} : Finset (Fin 7)).image x) (x 0)) : Nonempty (Frame09 x) := by
  classical
  obtain ⟨f1, f2, z1, n1, z2, n2, e, he, e1, e2, hpar, p, hp, q, hq, hpq, hmin1, hmin2, htie,
    hvp, hacute, ha1, ha2, hos1, hos2⟩ := not_tieO_data hP hT
  obtain ⟨φ012, h012⟩ := hR {0, 1, 2} (by decide)
  obtain ⟨φ046, h046⟩ := hR {0, 4, 6} (by decide)
  obtain ⟨φ123, h123⟩ := hR {1, 2, 3} (by decide)
  obtain ⟨φ235, h235⟩ := hR {2, 3, 5} (by decide)
  obtain ⟨φ3456, h3456⟩ := hR {3, 4, 5, 6} (by decide)
  have hf1 : ∀ i : Fin 7, (i ∈ ({0, 1, 3, 4} : Finset (Fin 7)) → f1 (x i) = 0) ∧
      (i ∉ ({0, 1, 3, 4} : Finset (Fin 7)) → f1 (x i) < 0) := fun i =>
    ⟨fun hi => z1 _ (Finset.mem_image_of_mem x hi), fun hi =>
      n1 _ (Finset.mem_image_of_mem x (Finset.mem_univ i))
        (fun h => hi (hx.mem_finset_image.mp h))⟩
  have hf2 : ∀ i : Fin 7, (i ∈ ({0, 2, 5, 6} : Finset (Fin 7)) → f2 (x i) = 0) ∧
      (i ∉ ({0, 2, 5, 6} : Finset (Fin 7)) → f2 (x i) < 0) := fun i =>
    ⟨fun hi => z2 _ (Finset.mem_image_of_mem x hi), fun hi =>
      n2 _ (Finset.mem_image_of_mem x (Finset.mem_univ i))
        (fun h => hi (hx.mem_finset_image.mp h))⟩
  have h1v : f1 (x 0) = 0 := (hf1 0).1 (by decide)
  have h2v : f2 (x 0) = 0 := (hf2 0).1 (by decide)
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
  have hiS : i = 1 ∨ i = 3 ∨ i = 4 := by
    have h0 : i ≠ 0 := by
      rintro rfl
      have := hmin1 (x 1) (Finset.mem_image_of_mem x (by decide))
      have := (hf2 1).2 (by decide)
      linarith
    exact (by decide : ∀ i : Fin 7, i ∈ ({0, 1, 3, 4} : Finset (Fin 7)) → i ≠ 0 →
      (i = 1 ∨ i = 3 ∨ i = 4)) i hi h0
  have hjS : j = 2 ∨ j = 5 ∨ j = 6 := by
    have h0 : j ≠ 0 := by
      rintro rfl
      have := hmin2 (x 2) (Finset.mem_image_of_mem x (by decide))
      have := (hf1 2).2 (by decide)
      linarith
    exact (by decide : ∀ j : Fin 7, j ∈ ({0, 2, 5, 6} : Finset (Fin 7)) → j ≠ 0 →
      (j = 2 ∨ j = 5 ∨ j = 6)) j hj h0
  have h2p : f2 (x i) < 0 := (hf2 i).2 (by rcases hiS with rfl | rfl | rfl <;> decide)
  have h1q : f1 (x j) < 0 := (hf1 j).2 (by rcases hjS with rfl | rfl | rfl <;> decide)
  have h1p : f1 (x i) = 0 := (hf1 i).1 hi
  have h2q : f2 (x j) = 0 := (hf2 j).1 hj
  have hpe : ⟪x i - x 0, e⟫ = 0 := by rw [inner_sub_left]; linarith
  have hqe : ⟪x j - x 0, e⟫ = 0 := by rw [inner_sub_left]; linarith
  have hQ1 : ∀ (a b c d : Fin 7), ({0, 1, 3, 4} : Finset (Fin 7)) = {a, b, c, d} →
      ∀ y ∈ (({0, 1, 3, 4} : Finset (Fin 7)).image x), y = x a ∨ y = x b ∨ y = x c ∨ y = x d := by
    intro a b c d h y hy
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
    rw [h] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> simp
  have hQ2 : ∀ (a b c d : Fin 7), ({0, 2, 5, 6} : Finset (Fin 7)) = {a, b, c, d} →
      ∀ y ∈ (({0, 2, 5, 6} : Finset (Fin 7)).image x), y = x a ∨ y = x b ∨ y = x c ∨ y = x d := by
    intro a b c d h y hy
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
    rw [h] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> simp
  have hi3 : i = 3 := by
    rcases hiS with rfl | h | rfl
    · exact (q1_side_contra (m := x 3) (m' := x 4) he h1v h2v h1p h2q e1 e2 h2p.ne h1q.ne hpe hqe
        ((hf1 3).1 (by decide)) ((hf1 4).1 (by decide)) φ012 ((h012 0).1 (by decide))
        ((h012 1).1 (by decide)) ((h012 3).2 (by decide)) ((h012 4).2 (by decide))
        (hQ1 0 1 3 4 (by decide)) hos1).elim
    · exact h
    · exact (q1_side_contra (m := x 1) (m' := x 3) he h1v h2v h1p h2q e1 e2 h2p.ne h1q.ne hpe hqe
        ((hf1 1).1 (by decide)) ((hf1 3).1 (by decide)) φ046 ((h046 0).1 (by decide))
        ((h046 4).1 (by decide)) ((h046 1).2 (by decide)) ((h046 3).2 (by decide))
        (hQ1 0 4 1 3 (by decide)) hos1).elim
  subst hi3
  have hj5 : j = 5 := by
    rcases hjS with rfl | h | rfl
    · exact (q2_side_contra (m := x 5) (m' := x 6) he h1v h2v h1p h2q e1 e2 h2p.ne h1q.ne hpe hqe
        ((hf2 5).1 (by decide)) ((hf2 6).1 (by decide)) φ012 ((h012 0).1 (by decide))
        ((h012 2).1 (by decide)) ((h012 5).2 (by decide)) ((h012 6).2 (by decide))
        (hQ2 0 2 5 6 (by decide)) hos2).elim
    · exact h
    · exact (q2_side_contra (m := x 2) (m' := x 5) he h1v h2v h1p h2q e1 e2 h2p.ne h1q.ne hpe hqe
        ((hf2 2).1 (by decide)) ((hf2 5).1 (by decide)) φ046 ((h046 0).1 (by decide))
        ((h046 6).1 (by decide)) ((h046 2).2 (by decide)) ((h046 5).2 (by decide))
        (hQ2 0 6 2 5 (by decide)) hos2).elim
  subst hj5
  -- the parallel-segment exclusions
  have fm1 : ∀ y : Fin 7, y ∈ ({1, 4} : Finset (Fin 7)) → ∀ c : ℝ, x y - x 3 ≠ c • e := by
    intro y hy c hc
    have hne : x 3 ≠ x y := hx.ne
      ((by decide : ∀ y : Fin 7, y ∈ ({1, 4} : Finset (Fin 7)) → 3 ≠ y) y hy)
    exact not_midPair_far1 (Finset.mem_image_of_mem x (by decide))
      (fun h => absurd (hx.mem_finset_image.mp h) (by decide)) hmin1
      (hpar (x 3) (Finset.mem_image_of_mem x (Finset.mem_univ _)) (x y)
        (Finset.mem_image_of_mem x (Finset.mem_univ _)) hne c hc)
  have fm2 : ∀ y : Fin 7, y ∈ ({2, 6} : Finset (Fin 7)) → ∀ c : ℝ, x y - x 5 ≠ c • e := by
    intro y hy c hc
    have hne : x 5 ≠ x y := hx.ne
      ((by decide : ∀ y : Fin 7, y ∈ ({2, 6} : Finset (Fin 7)) → 5 ≠ y) y hy)
    exact not_midPair_far2 (Finset.mem_image_of_mem x (by decide))
      (fun h => absurd (hx.mem_finset_image.mp h) (by decide)) hmin2
      (hpar (x 5) (Finset.mem_image_of_mem x (Finset.mem_univ _)) (x y)
        (Finset.mem_image_of_mem x (Finset.mem_univ _)) hne c hc)
  have m2 : f2 (x 3) ≤ f2 (x 1) ∧ f2 (x 3) ≤ f2 (x 4) :=
    ⟨hmin1 _ (Finset.mem_image_of_mem x (by decide)), hmin1 _ (Finset.mem_image_of_mem x (by decide))⟩
  have m1 : f1 (x 5) ≤ f1 (x 2) ∧ f1 (x 5) ≤ f1 (x 6) :=
    ⟨hmin2 _ (Finset.mem_image_of_mem x (by decide)), hmin2 _ (Finset.mem_image_of_mem x (by decide))⟩
  -- the orientation
  have hzne : ⟪x 1 - x 0, e⟫ ≠ 0 := by
    intro h0
    have d := frame_decomp he h1v h2v h1p h2q e1 e2 h2p.ne h1q.ne hpe hqe (x 1)
    rw [(hf1 1).1 (by decide), zero_div, zero_smul, add_zero, h0, zero_div, zero_smul,
      add_zero] at d
    exact hgen (x 0) (Finset.mem_image_of_mem x (Finset.mem_univ _)) (x 3)
      (Finset.mem_image_of_mem x (Finset.mem_univ _)) (x 1)
      (Finset.mem_image_of_mem x (Finset.mem_univ _)) (hx.ne (by decide)) (hx.ne (by decide))
      (hx.ne (by decide)) _ d
  have a11 : ⟪x 5 - x 3, x 3 - x 0⟫ ≤ 0 := ha1
  have a22 : ⟪x 3 - x 5, x 5 - x 0⟫ ≤ 0 := ha2
  have key : ∀ e' : ℝ³, e' ≠ 0 → f1 (x 0 + e') = 0 → f2 (x 0 + e') = 0 →
      ⟪x 3 - x 0, e'⟫ = 0 → ⟪x 5 - x 0, e'⟫ = 0 →
      (∀ c : ℝ, x 1 - x 3 ≠ c • e') → (∀ c : ℝ, x 4 - x 3 ≠ c • e') →
      (∀ c : ℝ, x 2 - x 5 ≠ c • e') → (∀ c : ℝ, x 6 - x 5 ≠ c • e') →
      0 < ⟪x 1 - x 0, e'⟫ → Nonempty (Frame09 x) :=
    fun e' he' a b c d p1 p4 p2 p6 hz' =>
      frame09_core x f1 f2 hf1 hf2 m2 m1 e' he' a b c d p1 p4 p2 p6 hacute a11 a22 hz'
        φ012 φ123 φ235 φ3456 h012 h123 h235 h3456
  rcases lt_or_gt_of_ne hzne with hneg | hpos
  · -- orient with `-e`
    have hl1 : f1 (x 0 + -e) = 0 := by
      have := aff_add f1 (x 0) (-e); have := aff_add f1 (x 0) e
      rw [map_neg] at *; linarith
    have hl2 : f2 (x 0 + -e) = 0 := by
      have := aff_add f2 (x 0) (-e); have := aff_add f2 (x 0) e
      rw [map_neg] at *; linarith
    refine key (-e) (neg_ne_zero.mpr he) hl1 hl2 (by rw [inner_neg_right, hpe, neg_zero])
      (by rw [inner_neg_right, hqe, neg_zero])
      (fun c h => fm1 1 (by decide) (-c) (by rw [h, smul_neg, neg_smul]))
      (fun c h => fm1 4 (by decide) (-c) (by rw [h, smul_neg, neg_smul]))
      (fun c h => fm2 2 (by decide) (-c) (by rw [h, smul_neg, neg_smul]))
      (fun c h => fm2 6 (by decide) (-c) (by rw [h, smul_neg, neg_smul])) ?_
    rw [inner_neg_right]; linarith
  · exact key e he e1 e2 hpe hqe (fm1 1 (by decide)) (fm1 4 (by decide)) (fm2 2 (by decide))
      (fm2 6 (by decide)) hpos

end Minimality.CaseC09
