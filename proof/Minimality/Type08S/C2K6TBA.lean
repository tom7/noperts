module

public import Minimality.Type08S.C2K6PZ

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

set_option maxHeartbeats 3200000 in
theorem k6t2_c1_real_pa {α4 γ4 β1 k0 U T B : ℝ} (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hs : 1 < α4 + γ4)
    (hβ1 : 0 < β1) (hκ : α4 * (1 - β1) = 1 - γ4) (hB : 0 < B) (hUT : U - β1 * B < T)
    (hcase : (0 < T ∧ T < α4 * U + γ4 * T ∧ U - β1 * B < α4 * U + γ4 * T) ∨
      (T < 0 ∧ α4 * U + γ4 * T < T ∧ U - β1 * B < 0 ∧ α4 * U + γ4 * T < 0))
    (hinj : ∀ i j, k0 + (k5dX1 α4 γ4 β1 i).1 * U + (k5dX1 α4 γ4 β1 i).2.1 * T + (k5dX1 α4 γ4 β1 i).2.2 * B =
      k0 + (k5dX1 α4 γ4 β1 j).1 * U + (k5dX1 α4 γ4 β1 j).2.1 * T + (k5dX1 α4 γ4 β1 j).2.2 * B → i = j) :
    LexUni (fun _ => (0 : ℝ))
      (fun i => k0 + (k5dX1 α4 γ4 β1 i).1 * U + (k5dX1 α4 γ4 β1 i).2.1 * T + (k5dX1 α4 γ4 β1 i).2.2 * B) := by
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  obtain ⟨s0, s1, s2, s3, s4⟩ := k5d_z5_sub
  refine k5d_uni_of_nopair (by decide) _ hinj ?_
  intro i j h1 h2 h3
  have hg : γ4 = 1 - α4 + α4 * β1 := by linarith
  subst hg
  have p1 := mul_pos hα4 hβ1
  have p2 := mul_pos hα4 hB
  have p3 := mul_pos hβ1 hB
  have p4 := mul_pos (mul_pos hα4 hβ1) hB
  have p5 := mul_pos hγ4 hB
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2 (by decide)).elim
    | exact (h3 (by decide)).elim
    | (simp only [k5dX1_0, k5dX1_1, k5dX1_2, k5dX1_3, k5dX1_4, f0, f1, f2, f3, f4, s0, s1, s2, s3, s4]
       rintro ⟨⟨h5, h6⟩, h7, h8⟩
       rcases hcase with hc | hc <;> nlinarith [hc.1, hc.2.1])


theorem k6t2_c1_pa0_frame (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0) {α4 γ4 β1 β6 γ6 : ℝ}
    (hα4 : 0 < α4) (hγ4 : 0 < γ4) (hs : 1 < α4 + γ4) (hβ1 : 0 < β1) (hb6 : 0 < β6) (hγ6 : 0 < γ6)
    (hg6 : γ6 < 1 ∨ γ6 = 1) (hκ : α4 * (1 - β1) = 1 - γ4) (hζ : ⟪P, R⟫ = ⟪Q, R⟫) (hu0 : ⟪P, R⟫ ≠ 0)
    (hmem : ∀ i, fpoint P Q R d (k5dX1 α4 γ4 β1 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, 0, 0) ∨ y = fpoint P Q R d (1, 0, 0) ∨
      y = fpoint P Q R d (α4, γ4, 0) ∨ y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, -1) ∨
      y = fpoint P Q R d (1, 0, -β1) ∨ y = fpoint P Q R d (0, γ6, -β6)) :
    HasLexCellAt V R := by
  have hA := k5d_hA hΔ
  refine k5d_c1_core V P Q R d hΔ hα4 hγ4 hs hβ1 hb6 hγ6 hg6 hmem hVall ?_
  intro k0 U T B hfw hinj
  have hB : 0 < B := by
    have := hfw (0, 0, -1) (by simp [k5dL]) (0, 0, 0) (by simp [k5dL]) (by dsimp only; linarith)
    dsimp only at this; linarith
  have hUT : U - β1 * B < T := by
    have := hfw (1, 0, -β1) (by simp [k5dL]) (0, 1, 0) (by simp [k5dL])
      (by dsimp only; nlinarith [mul_pos hβ1 hA])
    dsimp only at this; linarith
  have hc : (0 < T ∧ T < α4 * U + γ4 * T ∧ U - β1 * B < α4 * U + γ4 * T) ∨
      (T < 0 ∧ α4 * U + γ4 * T < T ∧ U - β1 * B < 0 ∧ α4 * U + γ4 * T < 0) := by
    rcases lt_or_gt_of_ne hu0 with hu | hu
    · right
      have h1 := hfw (α4, γ4, 0) (by simp [k5dL]) (0, 1, 0) (by simp [k5dL])
        (by dsimp only; nlinarith)
      have h2 := hfw (0, 1, 0) (by simp [k5dL]) (0, 0, 0) (by simp [k5dL])
        (by dsimp only; nlinarith)
      have h3 := hfw (1, 0, -β1) (by simp [k5dL]) (0, 0, 0) (by simp [k5dL])
        (by dsimp only; nlinarith [mul_pos hβ1 hA])
      have h4 := hfw (α4, γ4, 0) (by simp [k5dL]) (0, 0, 0) (by simp [k5dL])
        (by dsimp only; nlinarith)
      dsimp only at h1 h2 h3 h4
      refine ⟨by linarith, by linarith, by linarith, by linarith⟩
    · left
      have h1 := hfw (0, 1, 0) (by simp [k5dL]) (α4, γ4, 0) (by simp [k5dL])
        (by dsimp only; nlinarith)
      have h2 := hfw (0, 0, 0) (by simp [k5dL]) (0, 1, 0) (by simp [k5dL])
        (by dsimp only; nlinarith)
      have h3 := hfw (1, 0, -β1) (by simp [k5dL]) (α4, γ4, 0) (by simp [k5dL])
        (by dsimp only; nlinarith [mul_pos hβ1 hA])
      dsimp only at h1 h2 h3
      refine ⟨by linarith, by linarith, by linarith⟩
  exact k6t2_c1_real_pa hα4 hγ4 hs hβ1 hκ hB hUT hc hinj

end C2
end Type08Sp
end Minimality
