module

public import Minimality.Type08S.C2K6TBL

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

/-- From the forward-monotone key on a list `L` to the weak depth order on a cycle inside `L`. -/
theorem k6t2_hdep {n : ℕ} {X : ZMod n → ℝ × ℝ × ℝ} {L : List (ℝ × ℝ × ℝ)} {u t A k0 U T B : ℝ}
    (hX : ∀ i, X i ∈ L)
    (hfw : ∀ s ∈ L, ∀ t' ∈ L, s.1 * u + s.2.1 * t + s.2.2 * A < t'.1 * u + t'.2.1 * t + t'.2.2 * A →
      k0 + s.1 * U + s.2.1 * T + s.2.2 * B < k0 + t'.1 * U + t'.2.1 * T + t'.2.2 * B) :
    ∀ i j : ZMod n,
      k0 + (X i).1 * U + (X i).2.1 * T + (X i).2.2 * B < k0 + (X j).1 * U + (X j).2.1 * T + (X j).2.2 * B →
      (X i).1 * u + (X i).2.1 * t + (X i).2.2 * A ≤ (X j).1 * u + (X j).2.1 * t + (X j).2.2 * A := by
  intro i j hij
  by_contra hlt
  push Not at hlt
  have := hfw _ (hX j) _ (hX i) hlt
  linarith

/-- Cell `(c',b',c,d,b)` at `ζ(a,d) = 0 < ζ(c,d)` (frame form). -/
theorem k6t2_c1u0_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {α4 γ4 β1 β6 γ6 : ℝ}
    (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hs : 1 < α4 + γ4) (hβ1 : 0 < β1) (hb6 : 0 < β6) (hγ6 : 0 < γ6)
    (hg6 : γ6 < 1 ∨ γ6 = 1) (hu : ⟪P, R⟫ = 0) (ht : 0 < ⟪Q, R⟫)
    (hmem : ∀ i, fpoint P Q R d (k5dX1 α4 γ4 β1 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, 0) ∨
      y = fpoint P Q R d (α4, γ4, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, -1) ∨
      y = fpoint P Q R d (1, 0, -β1) ∨ y = fpoint P Q R d (0, γ6, -β6)) :
    HasLexCellAt V R := by
  have hA := k5d_hA hΔ
  refine k5d_c1_core V P Q R d hΔ hα4 hγ4 hs hβ1 hb6 hγ6 hg6 hmem hVall ?_
  intro k0 U T B hfw hinj
  have hBd := hfw (0, 0, -1) (by simp [k5dL]) (0, 0, 0) (by simp [k5dL]) (by dsimp only; linarith)
  dsimp only at hBd
  have hB : 0 < B := by linarith
  exact k6t2_c1u0_real (u := ⟪P, R⟫) (t := ⟪Q, R⟫) (A := ⟪R, R⟫) hα4 hγ4 hβ1 hA hB hu ht
    (k6t2_hdep (fun i => by simpa using k5dX1_mem α4 γ4 β1 β6 γ6 i) hfw) hinj

/-- Cell `(b',a',b,d,a)` at `ζ(a,d) = 0 > ζ(c,d)`, `γ4 ≤ 1`, `γ6 = 1` (frame form). -/
theorem k6t2_c5u0_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {α4 γ4 β1 β6 γ6 : ℝ}
    (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hs : 1 < α4 + γ4) (hβ1 : 0 < β1) (hb6 : 0 < β6) (hg6 : γ6 = 1)
    (hγ41 : γ4 ≤ 1) (hu : ⟪P, R⟫ = 0) (ht : ⟪Q, R⟫ < 0)
    (hmem : ∀ i, fpoint P Q R d (k5dX5 α4 γ4 β1 β6 γ6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, 0) ∨
      y = fpoint P Q R d (α4, γ4, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, -1) ∨
      y = fpoint P Q R d (1, 0, -β1) ∨ y = fpoint P Q R d (0, γ6, -β6)) :
    HasLexCellAt V R := by
  have hA := k5d_hA hΔ
  refine k5d_c5_core V P Q R d hΔ hα4 hγ4 hs hβ1 hb6 hg6 hmem hVall ?_
  intro k0 U T B hfw hinj
  have hBd := hfw (0, 0, -1) (by simp [k5dL]) (0, 0, 0) (by simp [k5dL]) (by dsimp only; linarith)
  dsimp only at hBd
  have hB : 0 < B := by linarith
  exact k6t2_c5u0_real (u := ⟪P, R⟫) (t := ⟪Q, R⟫) (A := ⟪R, R⟫) hα4 hγ4 hβ1 hb6 hg6 hγ41 hA hB hu ht
    (k6t2_hdep (fun i => by simpa using k5dX5_mem α4 γ4 β1 β6 γ6 i) hfw) hinj

end C2
end Type08Sp
end Minimality
