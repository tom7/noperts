module

public import Minimality.Type08S.C2K5BC

@[expose] public section


/-!
# K5b / D: the generic cells `(a,d,b,a',b')` (cell 1) and `(a,d,c,a',c')` (cell 2) at `u0 = r = b - c`.
Frame `p = a-d`, `q = c-d`, `r = b-c` (so `b = d+q+r`, `b' = d+α1 p+β1 q`, `c' = d+α1 p+β1(q+r)`, `a' = d+(β6+γ6) q+β6 r`).
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

theorem k5b_ex5_add (c : ℝ) {z0 z1 z2 z3 z4 : ℝ} (h : k5b_ex5 z0 z1 z2 z3 z4) :
    k5b_ex5 (c + z0) (c + z1) (c + z2) (c + z3) (c + z4) := by
  simpa only [k5b_ex5, add_lt_add_iff_left] using h

/-- Tilt interval `v = (1, lam, 0)`: `β1 - (α1-1) lam > 0` and `(s - β1) + α1 lam > 0`. -/
theorem k5b_interval {α1 β1 s : ℝ} (hα1 : 0 < α1) (hβ1 : 0 < β1) (hs : 0 < s) :
    ∃ lo hi : ℝ, lo < hi ∧ ∀ lam, lo < lam → lam < hi →
      0 < β1 - (α1 - 1) * lam ∧ 0 < (s - β1) + α1 * lam := by
  rcases le_or_gt α1 1 with h1 | h1
  · refine ⟨max ((β1 - s) / α1) 0, max ((β1 - s) / α1) 0 + 1, by linarith, fun lam hl0 hl1 => ?_⟩
    have hlam0 : 0 < lam := lt_of_le_of_lt (le_max_right _ _) hl0
    have hlam1 : (β1 - s) / α1 < lam := lt_of_le_of_lt (le_max_left _ _) hl0
    refine ⟨by nlinarith, ?_⟩
    have := (div_lt_iff₀ hα1).1 hlam1; linarith
  · have hα : 0 < α1 - 1 := by linarith
    have hlt : (β1 - s) / α1 < β1 / (α1 - 1) := by
      rw [div_lt_div_iff₀ hα1 hα]; nlinarith [mul_pos hs hα]
    refine ⟨(β1 - s) / α1, β1 / (α1 - 1), hlt, fun lam hl0 hl1 => ?_⟩
    refine ⟨?_, ?_⟩
    · have := (lt_div_iff₀ hα).1 hl1; nlinarith
    · have := (div_lt_iff₀ hα1).1 hl0; linarith

theorem k5b_cycN_inj {α1 β1 β6 γ6 : ℝ} (hα1 : 0 < α1) (hβ1 : 0 < β1) (hs : 1 < β6 + γ6) :
    (∀ i j, k5b_cyc1 α1 β1 β6 γ6 i = k5b_cyc1 α1 β1 β6 γ6 j → i = j) ∧
    (∀ i j, k5b_cyc2 α1 β1 β6 γ6 i = k5b_cyc2 α1 β1 β6 γ6 j → i = j) := by
  refine ⟨fun i j h => ?_, fun i j h => ?_⟩ <;>
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | rfl
    | (exfalso
       simp only [k5b_cyc1, k5b_cyc2, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4, Prod.mk.injEq] at h
       obtain ⟨e1, e2, e3⟩ := h
       first | linarith | nlinarith)

set_option maxHeartbeats 6400000 in
/-- **Cell 1 `(a, d, b, a', b')` at `r = b - c`** (ccw cycle `(a, b', a', b, d)`, tilt `v1 > 0`). -/
theorem k5b_cell1_hasLexCellAt (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0)
    {α1 β1 β6 γ6 : ℝ} (hα1 : 0 < α1) (hβ1 : 0 < β1) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hs : 1 < β6 + γ6)
    (hab : 1 < α1 + β1) (hcond : 0 < (α1 - 1) * (β6 + γ6) + β1)
    (hex : k5b_ex5 ⟪p, r⟫ (α1 * ⟪p, r⟫ + β1 * ⟪q, r⟫) ((β6 + γ6) * ⟪q, r⟫ + β6 * ⟪r, r⟫) (⟪q, r⟫ + ⟪r, r⟫) 0)
    (hmem : ∀ i, fpoint p q r d (k5b_cyc1 α1 β1 β6 γ6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint p q r d (1, 0, 0) ∨ y = fpoint p q r d (α1, β1, 0) ∨
      y = fpoint p q r d (0, β6 + γ6, β6) ∨ y = fpoint p q r d (0, 1, 1) ∨ y = fpoint p q r d (0, 0, 0) ∨
      y = fpoint p q r d (0, 1, 0) ∨ y = fpoint p q r d (α1, β1, β1)) :
    HasLexCellAt V r := by
  set Y := k5b_cyc1 α1 β1 β6 γ6 with hY
  obtain ⟨lo, hi, hlh, hlam⟩ := k5b_interval hα1 hβ1 (s := β6 + γ6) (by linarith)
  obtain ⟨lam, hl0, hl1, hsep⟩ := exists_sep_tilt p q r d hΔ Y (k5b_cycN_inj hα1 hβ1 hs).1
    (u1 := 1) (u2 := 0) (t1 := 0) (t2 := 1) (by norm_num) hlh
  obtain ⟨hc1, hc2⟩ := hlam lam hl0 hl1
  set vv := fcomb p q r (1 + lam * 0) (0 + lam * 1) 0 with hvv
  have hv1 : 0 < 1 + lam * 0 := by linarith
  have hc1' : 0 < β1 * (1 + lam * 0) - (α1 - 1) * (0 + lam * 1) := by nlinarith
  have hc2' : 0 < (β6 + γ6 - β1) * (1 + lam * 0) + α1 * (0 + lam * 1) := by nlinarith
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint p q r d t, r⟫ = ⟪d, r⟫ + t.1 * ⟪p, r⟫ + t.2.1 * ⟪q, r⟫ + t.2.2 * ⟪r, r⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have hlexY : LexUni (fun i => ⟪fpoint p q r d (Y i), r⟫) (fun i => ⟪fpoint p q r d (Y i), vv⟫) := by
    set zz : ZMod 5 → ℝ := fun i => ⟪fpoint p q r d (Y i), r⟫ with hzz
    refine k5b_lexUni5_excl _ _ hsep (k5b_ex_of zz ?_)
    have z0 : zz 0 = ⟪d, r⟫ + ⟪p, r⟫ := by simp only [hzz, hY, k5b_cyc1, pc5_0, hz]; ring
    have z1 : zz 1 = ⟪d, r⟫ + (α1 * ⟪p, r⟫ + β1 * ⟪q, r⟫) := by simp only [hzz, hY, k5b_cyc1, pc5_1, hz]; ring
    have z2 : zz 2 = ⟪d, r⟫ + ((β6 + γ6) * ⟪q, r⟫ + β6 * ⟪r, r⟫) := by
      simp only [hzz, hY, k5b_cyc1, pc5_2, hz]; ring
    have z3 : zz 3 = ⟪d, r⟫ + (⟪q, r⟫ + ⟪r, r⟫) := by simp only [hzz, hY, k5b_cyc1, pc5_3, hz]; ring
    have z4 : zz 4 = ⟪d, r⟫ + 0 := by simp only [hzz, hY, k5b_cyc1, pc5_4, hz]; ring
    rw [z0, z1, z2, z3, z4]
    exact k5b_ex5_add _ hex
  have n0 : -(0 : ZMod 5) = 0 := by decide
  have n1 : -(1 : ZMod 5) = 4 := by decide
  have n2 : -(2 : ZMod 5) = 3 := by decide
  have n3 : -(3 : ZMod 5) = 2 := by decide
  have n4 : -(4 : ZMod 5) = 1 := by decide
  have hcyc0 := fun D (hD : 0 < D) => k5b_cyc1_tsc (v2 := 0 + lam * 1) hD hα1 hβ1 hβ6 hγ6 hs hab hcond hv1
  have hr0' := fun D (hD : 0 < D) =>
    (k5b_rest1_tsc (v2 := 0 + lam * 1) hD hα1 hβ1 hβ6 hγ6 hs hab hv1 hc1' hc2').1
  have hr1' := fun D (hD : 0 < D) =>
    (k5b_rest1_tsc (v2 := 0 + lam * 1) hD hα1 hβ1 hβ6 hγ6 hs hab hv1 hc1' hc2').2
  rcases hΔ.lt_or_gt with hneg | hpos
  · have hD : 0 < -det3 p q r := by linarith
    refine ⟨5, inferInstance, fun i => fpoint p q r d (Y (-i)), vv, ?_⟩
    refine lexCell_coord V p q r d (by norm_num) (fun i => Y (-i)) (1 + lam * 0, 0 + lam * 1, 0)
      (fun i => hmem (-i)) (hcyc_rev (hcyc0 _ hD)) ?_ (lexUni_neg hlexY)
    intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [n0, hY, k5b_cyc1, pc5_0])).elim
    · exact (hyx 4 (by simp only [n4, hY, k5b_cyc1, pc5_1])).elim
    · exact (hyx 3 (by simp only [n3, hY, k5b_cyc1, pc5_2])).elim
    · exact (hyx 2 (by simp only [n2, hY, k5b_cyc1, pc5_3])).elim
    · exact (hyx 1 (by simp only [n1, hY, k5b_cyc1, pc5_4])).elim
    · exact ⟨_, rfl, hrest_rev (hr0' _ hD)⟩
    · exact ⟨_, rfl, hrest_rev (hr1' _ hD)⟩
  · refine ⟨5, inferInstance, fun i => fpoint p q r d (Y i), vv, ?_⟩
    refine lexCell_coord V p q r d (by norm_num) Y (1 + lam * 0, 0 + lam * 1, 0) hmem
      (hcyc0 _ hpos) ?_ hlexY
    intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [hY, k5b_cyc1, pc5_0])).elim
    · exact (hyx 1 (by simp only [hY, k5b_cyc1, pc5_1])).elim
    · exact (hyx 2 (by simp only [hY, k5b_cyc1, pc5_2])).elim
    · exact (hyx 3 (by simp only [hY, k5b_cyc1, pc5_3])).elim
    · exact (hyx 4 (by simp only [hY, k5b_cyc1, pc5_4])).elim
    · exact ⟨_, rfl, hr0' _ hpos⟩
    · exact ⟨_, rfl, hr1' _ hpos⟩


set_option maxHeartbeats 6400000 in
/-- **Cell 2 `(a, d, c, a', c')` at `r = b - c`** (ccw cycle `(a, c', a', c, d)`, tilt `v1 < 0`). -/
theorem k5b_cell2_hasLexCellAt (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0)
    {α1 β1 β6 γ6 : ℝ} (hα1 : 0 < α1) (hβ1 : 0 < β1) (hβ6 : 0 < β6) (hγ6 : 0 < γ6) (hs : 1 < β6 + γ6)
    (hab : 1 < α1 + β1) (hcond : 0 < (α1 - 1) * (β6 + γ6) + β1)
    (hex : k5b_ex5 ⟪p, r⟫ (α1 * ⟪p, r⟫ + β1 * ⟪q, r⟫ + β1 * ⟪r, r⟫) ((β6 + γ6) * ⟪q, r⟫ + β6 * ⟪r, r⟫) ⟪q, r⟫ 0)
    (hmem : ∀ i, fpoint p q r d (k5b_cyc2 α1 β1 β6 γ6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint p q r d (1, 0, 0) ∨ y = fpoint p q r d (α1, β1, β1) ∨
      y = fpoint p q r d (0, β6 + γ6, β6) ∨ y = fpoint p q r d (0, 1, 0) ∨ y = fpoint p q r d (0, 0, 0) ∨
      y = fpoint p q r d (0, 1, 1) ∨ y = fpoint p q r d (α1, β1, 0)) :
    HasLexCellAt V r := by
  set Y := k5b_cyc2 α1 β1 β6 γ6 with hY
  obtain ⟨lo, hi, hlh, hlam⟩ := k5b_interval hα1 hβ1 (s := β6 + γ6) (by linarith)
  obtain ⟨lam, hl0, hl1, hsep⟩ := exists_sep_tilt p q r d hΔ Y (k5b_cycN_inj hα1 hβ1 hs).2
    (u1 := -1) (u2 := 0) (t1 := 0) (t2 := -1) (by norm_num) hlh
  obtain ⟨hc1, hc2⟩ := hlam lam hl0 hl1
  set vv := fcomb p q r (-1 + lam * 0) (0 + lam * -1) 0 with hvv
  have hv1 : -1 + lam * 0 < 0 := by linarith
  have hc1' : 0 < -β1 * (-1 + lam * 0) + (α1 - 1) * (0 + lam * -1) := by nlinarith
  have hc2' : 0 < -(β6 + γ6 - β1) * (-1 + lam * 0) - α1 * (0 + lam * -1) := by nlinarith
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint p q r d t, r⟫ = ⟪d, r⟫ + t.1 * ⟪p, r⟫ + t.2.1 * ⟪q, r⟫ + t.2.2 * ⟪r, r⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  have hlexY : LexUni (fun i => ⟪fpoint p q r d (Y i), r⟫) (fun i => ⟪fpoint p q r d (Y i), vv⟫) := by
    set zz : ZMod 5 → ℝ := fun i => ⟪fpoint p q r d (Y i), r⟫ with hzz
    refine k5b_lexUni5_excl _ _ hsep (k5b_ex_of zz ?_)
    have z0 : zz 0 = ⟪d, r⟫ + ⟪p, r⟫ := by simp only [hzz, hY, k5b_cyc2, pc5_0, hz]; ring
    have z1 : zz 1 = ⟪d, r⟫ + (α1 * ⟪p, r⟫ + β1 * ⟪q, r⟫ + β1 * ⟪r, r⟫) := by simp only [hzz, hY, k5b_cyc2, pc5_1, hz]; ring
    have z2 : zz 2 = ⟪d, r⟫ + ((β6 + γ6) * ⟪q, r⟫ + β6 * ⟪r, r⟫) := by
      simp only [hzz, hY, k5b_cyc2, pc5_2, hz]; ring
    have z3 : zz 3 = ⟪d, r⟫ + ⟪q, r⟫ := by simp only [hzz, hY, k5b_cyc2, pc5_3, hz]; ring
    have z4 : zz 4 = ⟪d, r⟫ + 0 := by simp only [hzz, hY, k5b_cyc2, pc5_4, hz]; ring
    rw [z0, z1, z2, z3, z4]
    exact k5b_ex5_add _ hex
  have n0 : -(0 : ZMod 5) = 0 := by decide
  have n1 : -(1 : ZMod 5) = 4 := by decide
  have n2 : -(2 : ZMod 5) = 3 := by decide
  have n3 : -(3 : ZMod 5) = 2 := by decide
  have n4 : -(4 : ZMod 5) = 1 := by decide
  have hcyc0 := fun D (hD : 0 < D) => k5b_cyc2_tsc (v2 := 0 + lam * -1) hD hα1 hβ1 hβ6 hγ6 hs hab hcond hv1
  have hr0' := fun D (hD : 0 < D) =>
    (k5b_rest2_tsc (v2 := 0 + lam * -1) hD hα1 hβ1 hβ6 hγ6 hs hab hv1 hc1' hc2').1
  have hr1' := fun D (hD : 0 < D) =>
    (k5b_rest2_tsc (v2 := 0 + lam * -1) hD hα1 hβ1 hβ6 hγ6 hs hab hv1 hc1' hc2').2
  rcases hΔ.lt_or_gt with hneg | hpos
  · have hD : 0 < -det3 p q r := by linarith
    refine ⟨5, inferInstance, fun i => fpoint p q r d (Y (-i)), vv, ?_⟩
    refine lexCell_coord V p q r d (by norm_num) (fun i => Y (-i)) (-1 + lam * 0, 0 + lam * -1, 0)
      (fun i => hmem (-i)) (hcyc_rev (hcyc0 _ hD)) ?_ (lexUni_neg hlexY)
    intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [n0, hY, k5b_cyc2, pc5_0])).elim
    · exact (hyx 4 (by simp only [n4, hY, k5b_cyc2, pc5_1])).elim
    · exact (hyx 3 (by simp only [n3, hY, k5b_cyc2, pc5_2])).elim
    · exact (hyx 2 (by simp only [n2, hY, k5b_cyc2, pc5_3])).elim
    · exact (hyx 1 (by simp only [n1, hY, k5b_cyc2, pc5_4])).elim
    · exact ⟨_, rfl, hrest_rev (hr0' _ hD)⟩
    · exact ⟨_, rfl, hrest_rev (hr1' _ hD)⟩
  · refine ⟨5, inferInstance, fun i => fpoint p q r d (Y i), vv, ?_⟩
    refine lexCell_coord V p q r d (by norm_num) Y (-1 + lam * 0, 0 + lam * -1, 0) hmem
      (hcyc0 _ hpos) ?_ hlexY
    intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [hY, k5b_cyc2, pc5_0])).elim
    · exact (hyx 1 (by simp only [hY, k5b_cyc2, pc5_1])).elim
    · exact (hyx 2 (by simp only [hY, k5b_cyc2, pc5_2])).elim
    · exact (hyx 3 (by simp only [hY, k5b_cyc2, pc5_3])).elim
    · exact (hyx 4 (by simp only [hY, k5b_cyc2, pc5_4])).elim
    · exact ⟨_, rfl, hr0' _ hpos⟩
    · exact ⟨_, rfl, hr1' _ hpos⟩

end C2
end Type08Sp
end Minimality
