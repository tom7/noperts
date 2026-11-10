module

public import Minimality.Type29KSAT.NfK2

@[expose] public section

/-!
# Type 29, class K2a on the stratum `Z1`: the atoms of the class in normal form coordinates

On `Z1 = {s = 1, t = 1, a0 + h0 = 0}` the three atoms `KF1456 = det3 (x1 - x4) (x5 - x6) N_F`,
`KF1546 = det3 (x1 - x5) (x4 - x6) N_F` and `B:34 = <N_B, x3 - x4>` vanish (`z1_atoms`).  The case hypothesis of the
case-A core is that the edge direction `x1 - x4` is not orthogonal to the plane of the facet `B = 015`;
this is the nonvanishing of one of the two inner products `<x1 - x4, x0 - x1>`, `<x1 - x4, x0 - x5>`
(`caseA_of_not_parallel`).
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.H29.SAT

namespace Minimality.H29K.SAT

variable {x : Fin 7 → ℝ³}

/-- **The three atoms of the class vanish on `Z1`.** -/
theorem z1_atoms (N : NF29 x) (F : S0xFac 9 s0x_S29 x) (hZ : N.s = 1 ∧ N.t = 1 ∧ N.a0 + N.h0 = 0) :
    det3 (x 1 - x 4) (x 5 - x 6) (F.N 5) = 0 ∧ det3 (x 1 - x 5) (x 4 - x 6) (F.N 5) = 0 ∧
      ⟪F.N 1, x 3 - x 4⟫ = 0 := by
  obtain ⟨hs, ht, hh⟩ := hZ
  refine ⟨?_, ?_, ?_⟩
  · rw [k2_atom1 N, ht]; ring
  · rw [k2_atom2 N, hs]; ring
  · have e51 : x 5 - x 1 = N.E₂ := by rw [N.x5, N.x1]; simp only [nfP]; module
    have e31 : x 3 - x 1 = -N.E₃ := by rw [N.x3, N.x1]; simp only [nfP]; module
    have e01 : x 0 - x 1 = N.a0 • N.E₁ + N.b0 • N.E₂ + (-N.h0) • N.E₃ := by
      rw [N.x0, N.x1]; simp only [nfP]; module
    have e34 : x 3 - x 4 = -N.E₃ - N.E₁ := by rw [N.x3, N.x4]; simp only [nfP]; module
    have g2 : ⟪F.N 1, N.E₂⟫ = 0 := by
      have := F.inner_sub 1 5 1
      rw [e51, F.zero 1 5 (by decide), F.zero 1 1 (by decide)] at this
      simpa using this
    have g0 : N.a0 * ⟪F.N 1, N.E₁⟫ + N.b0 * ⟪F.N 1, N.E₂⟫ + (-N.h0) * ⟪F.N 1, N.E₃⟫ = 0 := by
      have := F.inner_sub 1 0 1
      rw [e01, F.zero 1 0 (by decide), F.zero 1 1 (by decide)] at this
      simpa [inner_add_right, real_inner_smul_right] using this
    rw [g2] at g0
    have ha := N.ha0
    have h1 : ⟪F.N 1, N.E₁⟫ = -⟪F.N 1, N.E₃⟫ := by
      have hh' : N.h0 = -N.a0 := by linarith
      rw [hh'] at g0
      have : N.a0 * (⟪F.N 1, N.E₁⟫ + ⟪F.N 1, N.E₃⟫) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h ha.ne
      · linarith
    rw [e34, inner_sub_right, inner_neg_right]
    linarith

/-- A vector orthogonal to two independent vectors `P1`, `P2` is a multiple of any other such nonzero vector. -/
theorem par_of_perp (P1 P2 W M M' : ℝ³) (hW : det3 P1 P2 W ≠ 0) (hM' : M' ≠ 0)
    (m1 : ⟪M, P1⟫ = 0) (m2 : ⟪M, P2⟫ = 0) (n1 : ⟪M', P1⟫ = 0) (n2 : ⟪M', P2⟫ = 0) :
    ∃ c : ℝ, M = c • M' := by
  rw [inn3] at m1 m2 n1 n2
  set q0 := P1 1 * P2 2 - P1 2 * P2 1 with hq0
  set q1 := P1 2 * P2 0 - P1 0 * P2 2 with hq1
  set q2 := P1 0 * P2 1 - P1 1 * P2 0 with hq2
  have hqq : q0 * q0 + q1 * q1 + q2 * q2 ≠ 0 := by
    intro h
    have h0 : q0 = 0 := by nlinarith [sq_nonneg q0, sq_nonneg q1, sq_nonneg q2]
    have h1 : q1 = 0 := by nlinarith [sq_nonneg q0, sq_nonneg q1, sq_nonneg q2]
    have h2 : q2 = 0 := by nlinarith [sq_nonneg q0, sq_nonneg q1, sq_nonneg q2]
    apply hW
    rw [det3_expand]
    linear_combination (W 0) * h0 + (W 1) * h1 + (W 2) * h2
  have key : ∀ X : ℝ³, X 0 * P1 0 + X 1 * P1 1 + X 2 * P1 2 = 0 → X 0 * P2 0 + X 1 * P2 1 + X 2 * P2 2 = 0 →
      (q0 * q0 + q1 * q1 + q2 * q2) * X 0 = (X 0 * q0 + X 1 * q1 + X 2 * q2) * q0 ∧
      (q0 * q0 + q1 * q1 + q2 * q2) * X 1 = (X 0 * q0 + X 1 * q1 + X 2 * q2) * q1 ∧
      (q0 * q0 + q1 * q1 + q2 * q2) * X 2 = (X 0 * q0 + X 1 * q1 + X 2 * q2) * q2 := by
    intro X a1 a2
    refine ⟨?_, ?_, ?_⟩
    · linear_combination (q1 * P1 2 - q2 * P1 1) * a2 - (q1 * P2 2 - q2 * P2 1) * a1
    · linear_combination (q2 * P1 0 - q0 * P1 2) * a2 - (q2 * P2 0 - q0 * P2 2) * a1
    · linear_combination (q0 * P1 1 - q1 * P1 0) * a2 - (q0 * P2 1 - q1 * P2 0) * a1
  obtain ⟨a0, a1, a2⟩ := key M m1 m2
  obtain ⟨b0, b1, b2⟩ := key M' n1 n2
  set s := M' 0 * q0 + M' 1 * q1 + M' 2 * q2 with hs
  have hsne : s ≠ 0 := by
    intro h0
    apply hM'
    have z0 : M' 0 = 0 := by
      have := b0; rw [h0, zero_mul] at this
      exact (mul_eq_zero.mp this).resolve_left hqq
    have z1 : M' 1 = 0 := by
      have := b1; rw [h0, zero_mul] at this
      exact (mul_eq_zero.mp this).resolve_left hqq
    have z2 : M' 2 = 0 := by
      have := b2; rw [h0, zero_mul] at this
      exact (mul_eq_zero.mp this).resolve_left hqq
    ext i; fin_cases i <;> simp [z0, z1, z2]
  have fin : ∀ (m m' qi : ℝ), (q0 * q0 + q1 * q1 + q2 * q2) * m = (M 0 * q0 + M 1 * q1 + M 2 * q2) * qi →
      (q0 * q0 + q1 * q1 + q2 * q2) * m' = s * qi → m = (M 0 * q0 + M 1 * q1 + M 2 * q2) / s * m' := by
    intro m m' qi ha hb
    rw [div_mul_eq_mul_div, eq_div_iff hsne]
    apply mul_left_cancel₀ hqq
    linear_combination s * ha - (M 0 * q0 + M 1 * q1 + M 2 * q2) * hb
  refine ⟨(M 0 * q0 + M 1 * q1 + M 2 * q2) / s, ?_⟩
  ext i; fin_cases i
  · exact fin _ _ _ a0 b0
  · exact fin _ _ _ a1 b1
  · exact fin _ _ _ a2 b2

/-- **The case hypothesis of case A**: the edge direction `x1 - x4` is not orthogonal to both `x0 - x1` and `x0 - x5`
(on `Z1` these two edges span the plane of the facet `B = 015`). -/
def CaseA (y : Fin 7 → ℝ³) : Prop := ⟪y 1 - y 4, y 0 - y 1⟫ ≠ 0 ∨ ⟪y 1 - y 4, y 0 - y 5⟫ ≠ 0

/-- **Case A in geometric form**: if `x1 - x4` is not parallel to the normal of the facet `B = 015` (that is, not orthogonal
to the plane of `B`), it is not orthogonal to both `x0 - x1` and `x0 - x5`. -/
theorem caseA_of_not_parallel (N : NF29 x) (F : S0xFac 9 s0x_S29 x) (h : ¬ ∃ c : ℝ, x 1 - x 4 = c • F.N 1) :
    CaseA x := by
  by_contra hc
  simp only [CaseA, not_or, not_not] at hc
  obtain ⟨c1, c2⟩ := hc
  have e51 : x 5 - x 1 = N.E₂ := by rw [N.x5, N.x1]; simp only [nfP]; module
  have e31 : x 3 - x 1 = -N.E₃ := by rw [N.x3, N.x1]; simp only [nfP]; module
  have e01 : x 0 - x 1 = N.a0 • N.E₁ + N.b0 • N.E₂ + (-N.h0) • N.E₃ := by
    rw [N.x0, N.x1]; simp only [nfP]; module
  have g3 : 0 < ⟪F.N 1, N.E₃⟫ := by
    have := F.inner_sub 1 3 1
    rw [e31, F.zero 1 1 (by decide), inner_neg_right] at this
    have h := F.neg 1 3 (by decide)
    linarith
  have hM' : F.N 1 ≠ 0 := by
    intro h0; rw [h0, inner_zero_left] at g3; exact lt_irrefl _ g3
  have hW : det3 (x 5 - x 1) (x 0 - x 1) (x 3 - x 1) ≠ 0 := by
    have : det3 (x 5 - x 1) (x 0 - x 1) (x 3 - x 1) = N.a0 * det3 N.E₁ N.E₂ N.E₃ := by
      rw [e51, e01, e31]
      simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
      ring
    rw [this]
    exact mul_ne_zero N.ha0.ne (by simpa [det3] using N.hD)
  have m2 : ⟪x 1 - x 4, x 0 - x 1⟫ = 0 := c1
  have m1 : ⟪x 1 - x 4, x 5 - x 1⟫ = 0 := by
    have : x 5 - x 1 = (x 0 - x 1) - (x 0 - x 5) := by abel
    rw [this, inner_sub_right, c1, c2]; ring
  have n1 : ⟪F.N 1, x 5 - x 1⟫ = 0 := by
    rw [F.inner_sub 1 5 1, F.zero 1 5 (by decide), F.zero 1 1 (by decide)]; ring
  have n2 : ⟪F.N 1, x 0 - x 1⟫ = 0 := by
    rw [F.inner_sub 1 0 1, F.zero 1 0 (by decide), F.zero 1 1 (by decide)]; ring
  exact h (par_of_perp (x 5 - x 1) (x 0 - x 1) (x 3 - x 1) (x 1 - x 4) (F.N 1) hW hM' m1 m2 n1 n2)

end Minimality.H29K.SAT
