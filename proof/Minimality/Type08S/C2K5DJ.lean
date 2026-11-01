module

public import Minimality.Type08S.C2K5DI

@[expose] public section


/-!
# K5d / J: frame lemmas for cells 3, 4, 5, 6, 8
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

theorem k5d_c4_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {α4 γ4 β1 β6 γ6 : ℝ}
    (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hs : 1 < α4 + γ4) (hβ1 : 0 < β1) (hb6 : 0 < β6) (hγ6 : 0 < γ6) (hg61 : γ6 < 1) (hα41 : α4 < 1)
    (hκ : α4 * (1 - β1) = 1 - γ4) (hTU : ⟪Q, R⟫ < ⟪P, R⟫) (hbc : α4 * ⟪P, R⟫ + γ4 * ⟪Q, R⟫ < ⟪Q, R⟫)
    
    (hmem : ∀ i, fpoint P Q R d (k5dX4 α4 γ4 β1 β6 γ6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, 0) ∨
      y = fpoint P Q R d (α4, γ4, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, -1) ∨
      y = fpoint P Q R d (1, 0, -β1) ∨ y = fpoint P Q R d (0, γ6, -β6)) :
    HasLexCellAt V R := by
  have hA := k5d_hA hΔ
  refine k5d_c4_core V P Q R d hΔ hα4 hγ4 hs hβ1 hb6 hγ6 hg61 hα41 hmem hVall ?_
  intro k0 U T B hfw hinj
  have hBd := hfw (0, 0, -1) (by simp [k5dL]) (0, 0, 0) (by simp [k5dL]) (by dsimp only; linarith)
  dsimp only at hBd
  have hB : 0 < B := by linarith
  have h1 := hfw (0, 1, 0) (by simp [k5dL]) (1, 0, 0) (by simp [k5dL]) (by dsimp only; linarith)
  dsimp only at h1
  have h2 := hfw (α4, γ4, 0) (by simp [k5dL]) (0, 1, 0) (by simp [k5dL]) (by dsimp only; linarith)
  dsimp only at h2
  exact k5d_c4_real hα4 hγ4 hs hβ1 hb6 hB hα41 hκ (by linarith) (by linarith) hinj

theorem k5d_c3_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {α4 γ4 β1 β6 γ6 : ℝ}
    (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hs : 1 < α4 + γ4) (hβ1 : 0 < β1) (hb6 : 0 < β6) (hγ6 : 0 < γ6) (hg61 : γ6 < 1) (hbg : 1 < β6 + γ6) (hα41 : α4 < 1)
    (hκ : α4 * (1 - β1) = 1 - γ4) (hTU : ⟪Q, R⟫ < ⟪P, R⟫) (hcb : ⟪Q, R⟫ < α4 * ⟪P, R⟫ + γ4 * ⟪Q, R⟫)
    
    (hmem : ∀ i, fpoint P Q R d (k5dX3 α4 γ4 β1 β6 γ6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, 0) ∨
      y = fpoint P Q R d (α4, γ4, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, -1) ∨
      y = fpoint P Q R d (1, 0, -β1) ∨ y = fpoint P Q R d (0, γ6, -β6)) :
    HasLexCellAt V R := by
  have hA := k5d_hA hΔ
  refine k5d_c3_core V P Q R d hΔ hα4 hγ4 hs hβ1 hb6 hγ6 hg61 hbg hα41 hmem hVall ?_
  intro k0 U T B hfw hinj
  have hBd := hfw (0, 0, -1) (by simp [k5dL]) (0, 0, 0) (by simp [k5dL]) (by dsimp only; linarith)
  dsimp only at hBd
  have hB : 0 < B := by linarith
  have h1 := hfw (0, 1, 0) (by simp [k5dL]) (1, 0, 0) (by simp [k5dL]) (by dsimp only; linarith)
  dsimp only at h1
  have h2 := hfw (0, 1, 0) (by simp [k5dL]) (α4, γ4, 0) (by simp [k5dL]) (by dsimp only; linarith)
  dsimp only at h2
  exact k5d_c3_real hα4 hγ4 hs hβ1 hb6 hγ6 hg61 hbg hB hα41 hκ (by linarith) (by linarith) hinj

theorem k5d_c5_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {α4 γ4 β1 β6 γ6 : ℝ}
    (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hs : 1 < α4 + γ4) (hβ1 : 0 < β1) (hb6 : 0 < β6) (hg6 : γ6 = 1)
    (hab : α4 * ⟪P, R⟫ + γ4 * ⟪Q, R⟫ < ⟪P, R⟫) (hba : ⟪Q, R⟫ - β6 * ⟪R, R⟫ < α4 * ⟪P, R⟫ + γ4 * ⟪Q, R⟫)
    
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
  have h1 := hfw (α4, γ4, 0) (by simp [k5dL]) (1, 0, 0) (by simp [k5dL]) (by dsimp only; linarith)
  dsimp only at h1
  have h2 := hfw (0, γ6, -β6) (by simp [k5dL]) (α4, γ4, 0) (by simp [k5dL]) (by dsimp only; rw [hg6]; linarith)
  dsimp only at h2
  rw [hg6] at h2
  exact k5d_c5_real hα4 hγ4 hs hβ1 hb6 hg6 hB (by linarith) (by linarith) hinj

theorem k5d_c8_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {α4 γ4 β1 β6 γ6 : ℝ}
    (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hs : 1 < α4 + γ4) (hβ1 : 0 < β1) (hb6 : 0 < β6) (hg6 : γ6 = 1)
    (hab : ⟪P, R⟫ < α4 * ⟪P, R⟫ + γ4 * ⟪Q, R⟫) (hU0 : 0 < ⟪P, R⟫)
    
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
  have h1 := hfw (1, 0, 0) (by simp [k5dL]) (α4, γ4, 0) (by simp [k5dL]) (by dsimp only; linarith)
  dsimp only at h1
  have h2 := hfw (0, 0, 0) (by simp [k5dL]) (1, 0, 0) (by simp [k5dL]) (by dsimp only; linarith)
  dsimp only at h2
  exact k5d_c8_real hα4 hγ4 hs hβ1 hb6 hg6 hB (by linarith) (by linarith) hinj

theorem k5d_c6_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {α4 γ4 β1 β6 γ6 : ℝ}
    (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hs : 1 < α4 + γ4) (hβ1 : 0 < β1) (hb6 : 0 < β6) (hg6 : γ6 = 1)
    (hab : α4 * ⟪P, R⟫ + γ4 * ⟪Q, R⟫ < ⟪P, R⟫) (hba : α4 * ⟪P, R⟫ + γ4 * ⟪Q, R⟫ < ⟪Q, R⟫ - β6 * ⟪R, R⟫)
    
    (hmem : ∀ i, fpoint P Q R d (k5dX6 α4 γ4 β1 β6 γ6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, 0) ∨
      y = fpoint P Q R d (α4, γ4, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, -1) ∨
      y = fpoint P Q R d (1, 0, -β1) ∨ y = fpoint P Q R d (0, γ6, -β6)) :
    HasLexCellAt V R := by
  have hA := k5d_hA hΔ
  refine k5d_c6_core V P Q R d hΔ hα4 hγ4 hs hβ1 hb6 hg6 hmem hVall ?_
  intro k0 U T B hfw hinj
  have hBd := hfw (0, 0, -1) (by simp [k5dL]) (0, 0, 0) (by simp [k5dL]) (by dsimp only; linarith)
  dsimp only at hBd
  have hB : 0 < B := by linarith
  have h1 := hfw (α4, γ4, 0) (by simp [k5dL]) (1, 0, 0) (by simp [k5dL]) (by dsimp only; linarith)
  dsimp only at h1
  have h2 := hfw (α4, γ4, 0) (by simp [k5dL]) (0, γ6, -β6) (by simp [k5dL]) (by dsimp only; rw [hg6]; linarith)
  dsimp only at h2
  rw [hg6] at h2
  exact k5d_c6_real hα4 hγ4 hs hβ1 hb6 hg6 hB (by linarith) (by linarith) hinj


end C2
end Type08Sp
end Minimality
