module

public import Minimality.Type08S.C2K6TAE

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- The two K5a cells at the view `a - d` in the `β1 = 1` frame (`T`, `γ4 = 1` forced by `κ_a = 0`), as conditions on
`m` with `⟪c - d, a - d⟫ = ⟪b - d, a - d⟫ + m ⟪a - d, a - d⟫` (`m = (C - B)/A`):
cell 1 `(a,d,b,a',b')`: `m > 0`, `1 < m + α4`, `0 < β6 m + α4 (β6 + 1) - β6`;
cell 2 `(a,d,c,a',c')`: `m < 0`, `1 < -m + α1`, `0 < -m + α1 (1 + β6) - β6`. -/
def K6tB11Cell1 (α1 α4 β6 m : ℝ) : Prop :=
  0 < m ∧ 1 < m + α4 ∧ 0 < β6 * m + α4 * (β6 + 1) - β6

def K6tB11Cell2 (α1 α4 β6 m : ℝ) : Prop :=
  m < 0 ∧ 1 < -m + α1 ∧ 0 < -m + α1 * (1 + β6) - β6

/-- **Leftover of the `β1 = 1` frame (tasks 3 and 4a)**: the coordinates and `m` for which neither K5a cell's Gram
conditions hold (includes `m = 0`, i.e. `B = C`). -/
def K6tLeftB11 (a a' b b' c c' d : ℝ³) : Prop :=
  ∃ α1 α4 β6 m : ℝ, 0 < α1 ∧ 0 < α4 ∧ 0 < β6 ∧
    c' = d + α1 • (a - d) + (1 : ℝ) • (b - d) ∧ b' = d + α4 • (a - d) + (1 : ℝ) • (c - d) ∧
    a' = d + β6 • (b - d) + (1 : ℝ) • (c - d) ∧
    ⟪c - d, a - d⟫ = ⟪b - d, a - d⟫ + m * ⟪a - d, a - d⟫ ∧
    ¬ K6tB11Cell1 α1 α4 β6 m ∧ ¬ K6tB11Cell2 α1 α4 β6 m

set_option maxHeartbeats 3200000 in
/-- **`β1 = 1` frame (Touch and Ta `β1 = 1`)**: `T`, `κ_a = 0`, `β1 = 1` (`det3 (a-d) (c'-b) (c-d) = 0`).  Either one of the
two K5a cells at `a - d` (`k5a_core_hasLexCellAt`, conditions `K6tB11Cell1/2` on the Gram quantity `m`) or `K6tLeftB11`. -/
theorem k6t1_B11 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT : IsT a' b c d)
    (hκ : det3 (c - b) (b' - b) (c' - b) = 0) (hβ1 : det3 (a - d) (c' - b) (c - d) = 0) :
    HasLexCell (V8 a a' b b' c c' d) ∨ K6tLeftB11 a a' b b' c c' d := by
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα1, hβ1p, hαβ, hα4, hγ4, hαγ, hβ6, -⟩ :=
    norm08w_coordsT W hT
  have hκ' := (planar_a_iff hdet hc' hb').1 hκ
  rw [det_beta1 hc'] at hβ1
  have hβ1e : β1 = 1 := by
    have : β1 - 1 = 0 := by
      rcases mul_eq_zero.1 hβ1 with h | h
      · exact h
      · exact absurd h hdet
    linarith
  subst hβ1e
  have hγ4e : γ4 = 1 := by
    have : α1 * (1 - γ4) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  subst hγ4e
  set p := b - d with hp
  set q := c - d with hq
  set r := a - d with hr
  have hr0 : r ≠ 0 := by intro h0; rw [h0] at hdet; simp [det3_expand] at hdet
  have hA : 0 < ⟪r, r⟫ := real_inner_self_pos.2 hr0
  obtain ⟨m, hm⟩ : ∃ m : ℝ, ⟪q, r⟫ = ⟪p, r⟫ + m * ⟪r, r⟫ := ⟨(⟪q, r⟫ - ⟪p, r⟫) / ⟪r, r⟫, by field_simp; ring⟩
  have hcyc : ∀ x y z : ℝ³, det3 x y z = det3 z x y := by
    intro x y z; simp only [det3_expand]; ring
  have hΔ : det3 p q r ≠ 0 := by rw [hcyc]; exact hdet
  have hΔ' : det3 q p r ≠ 0 := by
    have : det3 q p r = - det3 p q r := by simp only [det3_expand]; ring
    rw [this]; exact neg_ne_zero.2 hΔ
  have hfp : ∀ (u v : ℝ³) (x y z : ℝ), fpoint u v r d (x, y, z) = d + x • u + y • v + z • r := by
    intro u v x y z; simp only [fpoint, fcomb]; module
  have eA : a = d + r := by rw [hr]; abel
  have eB : b = d + p := by rw [hp]; abel
  have eC : c = d + q := by rw [hq]; abel
  have eC' : c' = d + α1 • r + p := by rw [hc', hr, hp]; module
  have eB' : b' = d + α4 • r + q := by rw [hb', hr, hq]; module
  have eA' : a' = d + β6 • p + (1 : ℝ) • q := by rw [ha', hp, hq]
  have P1a : fpoint p q r d (0, 0, 1) = a := by rw [hfp]; simp only [hr]; module
  have P1d : fpoint p q r d (0, 0, 0) = d := by rw [hfp]; module
  have P1b : fpoint p q r d (1, 0, 0) = b := by rw [hfp]; simp only [hp]; module
  have P1a' : fpoint p q r d (β6, 1, 0) = a' := by rw [hfp, ha']; simp only [hp, hq]; module
  have P1b' : fpoint p q r d (0, 1, α4) = b' := by rw [hfp, hb']; simp only [hr, hq]; module
  have P1c : fpoint p q r d (0, 1, 0) = c := by rw [hfp]; simp only [hq]; module
  have P1c' : fpoint p q r d (1, 0, α1) = c' := by rw [hfp, hc']; simp only [hr, hp]; module
  have P2a : fpoint q p r d (0, 0, 1) = a := by rw [hfp]; simp only [hr]; module
  have P2d : fpoint q p r d (0, 0, 0) = d := by rw [hfp]; module
  have P2c : fpoint q p r d (1, 0, 0) = c := by rw [hfp]; simp only [hq]; module
  have P2a' : fpoint q p r d (1, β6, 0) = a' := by rw [hfp, ha']; simp only [hp, hq]; module
  have P2c' : fpoint q p r d (0, 1, α1) = c' := by rw [hfp, hc']; simp only [hr, hp]; module
  have P2b : fpoint q p r d (0, 1, 0) = b := by rw [hfp]; simp only [hp]; module
  have P2b' : fpoint q p r d (1, 0, α4) = b' := by rw [hfp, hb']; simp only [hr, hq]; module
  by_cases h1 : K6tB11Cell1 α1 α4 β6 m
  · obtain ⟨hm0, hmα, hcond⟩ := h1
    left
    refine ⟨r, hr0, ?_⟩
    refine k5a_core_hasLexCellAt (V8 a a' b b' c c' d) p q r d hΔ (α1 := α1) (α4 := α4) (β6 := β6)
      (γ6 := 1) hα1 hα4 hβ6 one_pos (by linarith) hm0 hmα (by linarith) hm ?_ ?_
    · intro i
      rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
      · simp only [kCyc, pc5_0, P1a]; simp [V8]
      · simp only [kCyc, pc5_1, P1d]; simp [V8]
      · simp only [kCyc, pc5_2, P1b]; simp [V8]
      · simp only [kCyc, pc5_3, P1a']; simp [V8]
      · simp only [kCyc, pc5_4, P1b']; simp [V8]
    · intro y hy
      rw [P1a, P1d, P1b, P1a', P1b', P1c, P1c']
      simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
      tauto
  · by_cases h2 : K6tB11Cell2 α1 α4 β6 m
    · obtain ⟨hm0, hmα, hcond⟩ := h2
      left
      refine ⟨r, hr0, ?_⟩
      have hm' : ⟪p, r⟫ = ⟪q, r⟫ + (-m) * ⟪r, r⟫ := by linarith
      refine k5a_core_hasLexCellAt (V8 a a' b b' c c' d) q p r d hΔ' (α1 := α4) (α4 := α1) (β6 := 1)
        (γ6 := β6) hα4 hα1 one_pos hβ6 (by linarith) (by linarith) (by linarith) (by linarith) hm' ?_ ?_
      · intro i
        rcases z5_cases i with rfl | rfl | rfl | rfl | rfl
        · simp only [kCyc, pc5_0, P2a]; simp [V8]
        · simp only [kCyc, pc5_1, P2d]; simp [V8]
        · simp only [kCyc, pc5_2, P2c]; simp [V8]
        · simp only [kCyc, pc5_3, P2a']; simp [V8]
        · simp only [kCyc, pc5_4, P2c']; simp [V8]
      · intro y hy
        rw [P2a, P2d, P2c, P2a', P2c', P2b, P2b']
        simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
        tauto
    · right
      exact ⟨α1, α4, β6, m, hα1, hα4, hβ6, hc', hb', ha', hm, h1, h2⟩

end C2
end Type08Sp
end Minimality
