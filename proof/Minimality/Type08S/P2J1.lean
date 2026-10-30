module

public import Minimality.Type08S.P2E1
public import Minimality.Type08S.P2Defs
public import Minimality.Type08S.P2I5b

@[expose] public section

set_option relaxedAutoImplicit true

set_option autoImplicit true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- Weak far triple of the T4 group at `ℓ` (R2T*'s exception). -/
def WeakFarTp (b b' c c' d : ℝ³) : Prop :=
  ⟪c', b - d⟫ = ⟪b', b - d⟫ ∧ ⟪b', b - d⟫ = ⟪c, b - d⟫ ∧ ⟪d, b - d⟫ ≤ ⟪b', b - d⟫ ∧ ⟪b', b - d⟫ ≤ ⟪b, b - d⟫

theorem pts08_inj' {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) :
    Function.Injective (pts08 a a' b b' c c' d) := by
  have hnd := N.F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
  obtain ⟨hda, hda', hdb, hdb', hdc, hdc'⟩ := N.hd.ne
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [pts08]

set_option maxHeartbeats 1000000 in
/-- R2T* for the T4 group at a frame shape, no condition on `θ 0`, `θ 5` (only `hθ`). -/
theorem r2t08_T4 {o E₁ E₂ E₃ : ℝ³} (hE : det3 E₁ E₂ E₃ ≠ 0) {θ : Fin 6 → ℝ} (hθ : ∀ k, 0 < ineq08 θ k)
    (hy : Function.Injective (nfShape08 o E₁ E₂ E₃ θ))
    (hseg : ∀ i j m : Fin 7, nfShape08 o E₁ E₂ E₃ θ m ≠ nfShape08 o E₁ E₂ E₃ θ i →
      nfShape08 o E₁ E₂ E₃ θ m ≠ nfShape08 o E₁ E₂ E₃ θ j → ∀ s : ℝ, 0 < s → s < 1 →
      nfShape08 o E₁ E₂ E₃ θ m ≠ nfShape08 o E₁ E₂ E₃ θ i +
        s • (nfShape08 o E₁ E₂ E₃ θ j - nfShape08 o E₁ E₂ E₃ θ i)) :
    IsRobustUnimodal ((test08 1 true true).depth (nfShape08 o E₁ E₂ E₃ θ)) ∨
      IsRobustUnimodal ((test08 1 true false).depth (nfShape08 o E₁ E₂ E₃ θ)) ∨
      (let y := nfShape08 o E₁ E₂ E₃ θ; let u := y 2 - y 6
       ⟪y 5, u⟫ = ⟪y 3, u⟫ ∧ ⟪y 3, u⟫ = ⟪y 4, u⟫ ∧ ⟪y 6, u⟫ ≤ ⟪y 3, u⟫ ∧ ⟪y 3, u⟫ ≤ ⟪y 2, u⟫) := by
  set y := nfShape08 o E₁ E₂ E₃ θ with hydef
  have hord := ord08 (o := o) hE hθ 1
  have e1 : test08 1 true true = LabTest.quad (fun y => y 2 - y 6) 2 5 3 4 := rfl
  have e2 : test08 1 true false = LabTest.quad (fun y => y 2 - y 6) 6 5 3 4 := rfl
  have R := r2t_star y (fun y => y 2 - y 6) (covView_diff08 2 6) 2 6 5 3 4 hy (by decide) hseg
    hord (by
      intro L hL h1 h2
      have hinj : ∀ j, Function.Injective ((test08 1 true j).depth
          (nfShape08 (L o) (L E₁) (L E₂) (L E₃) θ)) := by
        intro j; cases j
        · rw [e2, ← mapShape_nfShape08]; exact h2
        · rw [e1, ← mapShape_nfShape08]; exact h1
      obtain ⟨j, hj⟩ := T4_core o E₁ E₂ E₃ hE θ hθ L hL hinj
      rw [← mapShape_nfShape08] at hj
      cases j
      · right; rw [← e2]; exact hj
      · left; rw [← e1]; exact hj)
  rcases R with h | h | h
  · exact Or.inl (by rw [e1]; exact h)
  · exact Or.inr (Or.inl (by rw [e2]; exact h))
  · exact Or.inr (Or.inr h)

theorem depth_T4_true {a a' b b' c c' d : ℝ³} :
    (test08 1 true true).depth (pts08 a a' b b' c c' d) =
      fun i : ZMod 4 => ⟪quad b c' b' c i, b - d⟫ := by
  show (LabTest.quad (fun y => y 2 - y 6) 2 5 3 4).depth (pts08 a a' b b' c c' d) = _
  funext i
  simp only [LabTest.depth, LabTest.quad]
  congr 1
  fin_cases i <;> rfl

theorem depth_T4_false {a a' b b' c c' d : ℝ³} :
    (test08 1 true false).depth (pts08 a a' b b' c c' d) =
      fun i : ZMod 4 => ⟪quad d c' b' c i, b - d⟫ := by
  show (LabTest.quad (fun y => y 2 - y 6) 6 5 3 4).depth (pts08 a a' b b' c c' d) = _
  funext i
  simp only [LabTest.depth, LabTest.quad]
  congr 1
  fin_cases i <;> rfl

/-- **The order dichotomy at `T'`** (needs no hypothesis beyond `Norm08`: `T4_core` works at `α1 = 1`). -/
theorem Tp_dichotomy {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d) :
    IsRobustUnimodal (fun i : ZMod 4 => ⟪quad d c' b' c i, b - d⟫) ∨
      IsRobustUnimodal (fun i : ZMod 4 => ⟪quad b c' b' c i, b - d⟫) ∨ WeakFarTp b b' c c' d := by
  classical
  obtain ⟨o, E₁, E₂, E₃, θ, hE, hθ, hpts⟩ := exists_nf08 N
  obtain ⟨hseg, hsp⟩ := seg08 N
  simp only [hpts] at hseg hsp
  have hy : Function.Injective (nfShape08 o E₁ E₂ E₃ θ) := by rw [← hpts]; exact pts08_inj' N
  rcases r2t08_T4 hE hθ hy hseg with h | h | h
  · right; left
    rw [← hpts, depth_T4_true] at h; exact h
  · left
    rw [← hpts, depth_T4_false] at h; exact h
  · right; right
    rw [← hpts] at h
    simpa [pts08, WeakFarTp] using h

end Type08Sp
end Minimality
#print axioms Minimality.Type08Sp.Tp_dichotomy
