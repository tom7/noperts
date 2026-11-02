module

public import Minimality.Type08S.C2K6TDD

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

set_option maxHeartbeats 1600000 in
/-- Generic cell `(a, d, x, a', x')` at `r = a - d` (as K5a's core), with the lex part supplied by `hLex` on a tilt interval. -/
theorem k6t4_core (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0)
    {α1 α4 β6 γ6 : ℝ} (hα1 : 0 < α1) (hα4 : 0 < α4) (hβ6 : 0 < β6)
    (hγ6 : 0 < γ6) (hs : 1 < β6 + γ6) {lo hi : ℝ} (hlh : lo < hi)
    (hlam : ∀ lam, lo < lam → lam < hi → 0 < lam ∧ 1 - β6 < lam * γ6 ∧ (1 - γ6) * lam + β6 * (-1) < 0)
    (hLex : ∀ lam, lo < lam → lam < hi →
      (∀ i j : ZMod 5, ⟪fpoint p q r d (kCyc β6 γ6 α4 i), r⟫ = ⟪fpoint p q r d (kCyc β6 γ6 α4 j), r⟫ →
        ⟪fpoint p q r d (kCyc β6 γ6 α4 i), fcomb p q r (0 + lam * 1) (-1 + lam * 0) 0⟫ =
          ⟪fpoint p q r d (kCyc β6 γ6 α4 j), fcomb p q r (0 + lam * 1) (-1 + lam * 0) 0⟫ → i = j) →
      LexUni (fun i => ⟪fpoint p q r d (kCyc β6 γ6 α4 i), r⟫)
        (fun i => ⟪fpoint p q r d (kCyc β6 γ6 α4 i), fcomb p q r (0 + lam * 1) (-1 + lam * 0) 0⟫))
    (hmem : ∀ i, fpoint p q r d (kCyc β6 γ6 α4 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint p q r d (0, 0, 1) ∨ y = fpoint p q r d (0, 0, 0) ∨
      y = fpoint p q r d (1, 0, 0) ∨ y = fpoint p q r d (β6, γ6, 0) ∨ y = fpoint p q r d (0, 1, α4) ∨
      y = fpoint p q r d (0, 1, 0) ∨ y = fpoint p q r d (1, 0, α1)) :
    HasLexCellAt V r := by
  set Y := kCyc β6 γ6 α4 with hY
  have hr0 : r ≠ 0 := by intro h; rw [h] at hΔ; simp [det3_expand] at hΔ
  have hA : 0 < ⟪r, r⟫ := real_inner_self_pos.2 hr0
  obtain ⟨lam, hl0, hl1, hsep⟩ := exists_sep_tilt p q r d hΔ Y (kCyc_inj hβ6 hγ6)
    (u1 := 0) (u2 := -1) (t1 := 1) (t2 := 0) (by norm_num) hlh
  obtain ⟨hlam0, hlam1, hlam3⟩ := hlam lam hl0 hl1
  set vv := fcomb p q r (0 + lam * 1) (-1 + lam * 0) 0 with hvv
  have hv1 : 0 < 0 + lam * 1 := by linarith
  have hv2 : -1 + lam * 0 < 0 := by linarith
  have hcone : (1 - γ6) * (0 + lam * 1) + β6 * (-1 + lam * 0) < 0 := by nlinarith
  have hc1 : 0 < γ6 * (0 + lam * 1) + (1 - β6) * (-1 + lam * 0) := by nlinarith
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint p q r d t, r⟫ = ⟪d, r⟫ + t.1 * ⟪p, r⟫ + t.2.1 * ⟪q, r⟫ + t.2.2 * ⟪r, r⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  obtain ⟨f0, f1, f2, f3, f4⟩ := z5_add
  have hinj := hsep
  have hlexY : LexUni (fun i => ⟪fpoint p q r d (Y i), r⟫) (fun i => ⟪fpoint p q r d (Y i), vv⟫) :=
    hLex lam hl0 hl1 hinj
  have n0 : -(0 : ZMod 5) = 0 := by decide
  have n1 : -(1 : ZMod 5) = 4 := by decide
  have n2 : -(2 : ZMod 5) = 3 := by decide
  have n3 : -(3 : ZMod 5) = 2 := by decide
  have n4 : -(4 : ZMod 5) = 1 := by decide
  have hcyc0 := fun D (hD : 0 < D) => k2_cyc (v3 := 0) (α4 := α4) hD hβ6 hγ6 hs hv1 hv2
  have hr0' := fun D (hD : 0 < D) => k5a_rest0 (v3 := 0) (α4 := α4) hD hα4 hβ6 hγ6 hs hv1 hv2 hcone
  have hr1' := fun D (hD : 0 < D) => k5a_rest1 (α4 := α4) (v3 := 0) hD hα1 hβ6 hγ6 hs hv2 hc1
  rcases hΔ.lt_or_gt with hneg | hpos
  · have hD : 0 < -det3 p q r := by linarith
    refine ⟨5, inferInstance, fun i => fpoint p q r d (Y (-i)), vv, ?_⟩
    refine lexCell_coord V p q r d (by norm_num) (fun i => Y (-i)) (0 + lam * 1, -1 + lam * 0, 0)
      (fun i => hmem (-i)) (hcyc_rev (hcyc0 _ hD)) ?_ (lexUni_neg hlexY)
    intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [n0, hY, kCyc, pc5_0])).elim
    · exact (hyx 4 (by simp only [n4, hY, kCyc, pc5_1])).elim
    · exact (hyx 3 (by simp only [n3, hY, kCyc, pc5_2])).elim
    · exact (hyx 2 (by simp only [n2, hY, kCyc, pc5_3])).elim
    · exact (hyx 1 (by simp only [n1, hY, kCyc, pc5_4])).elim
    · exact ⟨_, rfl, hrest_rev (hr0' _ hD)⟩
    · exact ⟨_, rfl, hrest_rev (hr1' _ hD)⟩
  · refine ⟨5, inferInstance, fun i => fpoint p q r d (Y i), vv, ?_⟩
    refine lexCell_coord V p q r d (by norm_num) Y (0 + lam * 1, -1 + lam * 0, 0) hmem
      (hcyc0 _ hpos) ?_ hlexY
    intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [hY, kCyc, pc5_0])).elim
    · exact (hyx 1 (by simp only [hY, kCyc, pc5_1])).elim
    · exact (hyx 2 (by simp only [hY, kCyc, pc5_2])).elim
    · exact (hyx 3 (by simp only [hY, kCyc, pc5_3])).elim
    · exact (hyx 4 (by simp only [hY, kCyc, pc5_4])).elim
    · exact ⟨_, rfl, hr0' _ hpos⟩
    · exact ⟨_, rfl, hr1' _ hpos⟩


end C2
end Type08Sp
end Minimality
