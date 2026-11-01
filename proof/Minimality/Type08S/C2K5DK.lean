module

public import Minimality.Type08S.C2K5DJ

@[expose] public section


/-!
# K5d / K: point-form setup for QPa and QTT (frame `(a - d, c - d, d - b)` at `u0 = d - b`)
-/
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

theorem k5dX1_mem (α4 γ4 β1 β6 γ6 : ℝ) : ∀ i, k5dX1 α4 γ4 β1 i ∈ k5dL α4 γ4 β1 β6 γ6 := by
  intro i; rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> simp [k5dX1_0, k5dX1_1, k5dX1_2, k5dX1_3, k5dX1_4, k5dL]
theorem k5dX4_mem (α4 γ4 β1 β6 γ6 : ℝ) : ∀ i, k5dX4 α4 γ4 β1 β6 γ6 i ∈ k5dL α4 γ4 β1 β6 γ6 := by
  intro i; rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> simp [k5dX4_0, k5dX4_1, k5dX4_2, k5dX4_3, k5dX4_4, k5dL]
theorem k5dX5_mem (α4 γ4 β1 β6 γ6 : ℝ) : ∀ i, k5dX5 α4 γ4 β1 β6 γ6 i ∈ k5dL α4 γ4 β1 β6 γ6 := by
  intro i; rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;> simp [k5dX5_0, k5dX5_1, k5dX5_2, k5dX5_3, k5dX5_4, k5dL]
theorem k5dX3_mem (α4 γ4 β1 β6 γ6 : ℝ) : ∀ i, k5dX3 α4 γ4 β1 β6 γ6 i ∈ k5dL α4 γ4 β1 β6 γ6 := by
  intro i; rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [k5dX3_0, k5dX3_1, k5dX3_2, k5dX3_3, k5dX3_4, k5dX3_5, k5dL]
theorem k5dX6_mem (α4 γ4 β1 β6 γ6 : ℝ) : ∀ i, k5dX6 α4 γ4 β1 β6 γ6 i ∈ k5dL α4 γ4 β1 β6 γ6 := by
  intro i; rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [k5dX6_0, k5dX6_1, k5dX6_2, k5dX6_3, k5dX6_4, k5dX6_5, k5dL]

/-- Common setup at `T'`: coordinates, frame points in `V8`, membership. -/
theorem k5d_setup {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT' : IsT' a b c' d) :
    ∃ α4 β1 γ4 β6 γ6 : ℝ, det3 (a - d) (b - d) (c - d) ≠ 0 ∧ det3 (a - d) (c - d) (d - b) ≠ 0 ∧
      0 < β1 ∧ 0 < α4 ∧ 0 < γ4 ∧ 1 < α4 + γ4 ∧ 0 < β6 ∧ 0 < γ6 ∧ 1 < β6 + γ6 ∧
      (W.F.abc'.f c < W.F.abc'.f a' → γ6 < 1) ∧
      c' = d + (1 : ℝ) • (a - d) + β1 • (b - d) ∧ b' = d + α4 • (a - d) + γ4 • (c - d) ∧
      a' = d + β6 • (b - d) + γ6 • (c - d) ∧
      (∀ t ∈ k5dL α4 γ4 β1 β6 γ6, fpoint (a - d) (c - d) (d - b) d t ∈ V8 a a' b b' c c' d) ∧
      (∀ y ∈ V8 a a' b b' c c' d, y = fpoint (a - d) (c - d) (d - b) d (0, 0, 0) ∨
        y = fpoint (a - d) (c - d) (d - b) d (1, 0, 0) ∨
        y = fpoint (a - d) (c - d) (d - b) d (α4, γ4, 0) ∨ y = fpoint (a - d) (c - d) (d - b) d (0, 1, 0) ∨
        y = fpoint (a - d) (c - d) (d - b) d (0, 0, -1) ∨
        y = fpoint (a - d) (c - d) (d - b) d (1, 0, -β1) ∨
        y = fpoint (a - d) (c - d) (d - b) d (0, γ6, -β6)) := by
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hβ1, hα4p, hγ4, hαγ, hβ6, hγ6, hγ6s, hfar⟩ :=
    norm08w_coordsTp W hT'
  have hΔ : det3 (a - d) (c - d) (d - b) ≠ 0 := by
    have e : det3 (a - d) (c - d) (d - b) = det3 (a - d) (b - d) (c - d) := by
      simp only [det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [e]; exact hdet
  have hfp : ∀ x y z : ℝ, fpoint (a - d) (c - d) (d - b) d (x, y, z) =
      d + x • (a - d) + y • (c - d) + z • (d - b) := by
    intro x y z; simp only [fpoint, fcomb]; module
  have eO : fpoint (a - d) (c - d) (d - b) d (0, 0, 0) = d := by rw [hfp]; simp
  have eA : fpoint (a - d) (c - d) (d - b) d (1, 0, 0) = a := by rw [hfp]; module
  have eB' : fpoint (a - d) (c - d) (d - b) d (α4, γ4, 0) = b' := by rw [hfp, hb']; module
  have eC : fpoint (a - d) (c - d) (d - b) d (0, 1, 0) = c := by rw [hfp]; module
  have eB : fpoint (a - d) (c - d) (d - b) d (0, 0, -1) = b := by rw [hfp]; module
  have eC' : fpoint (a - d) (c - d) (d - b) d (1, 0, -β1) = c' := by rw [hfp, hc']; module
  have eA' : fpoint (a - d) (c - d) (d - b) d (0, γ6, -β6) = a' := by rw [hfp, ha']; module
  refine ⟨α4, β1, γ4, β6, γ6, hdet, hΔ, hβ1, hα4p, hγ4, hαγ, hβ6, hγ6, hγ6s, hfar, hc', hb', ha', ?_, ?_⟩
  · intro t ht
    simp only [k5dL, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [eA]; simp [V8]
    · rw [eC]; simp [V8]
    · rw [eO]; simp [V8]
    · rw [eB]; simp [V8]
    · rw [eB']; simp [V8]
    · rw [eC']; simp [V8]
    · rw [eA']; simp [V8]
  · intro y hy
    rw [eO, eA, eB', eC, eB, eC', eA']
    simp only [V8, Finset.mem_insert, Finset.mem_singleton] at hy
    tauto

end C2
end Type08Sp
end Minimality
