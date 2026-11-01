module

public import Minimality.Type08S.C2K8J
public import Minimality.Type08S.C2K9C

@[expose] public section

/-!
# K9D: the two cells at the view `R = b - d` (frame `(P, Q, R) = (c - d, a - d, b - d)`), with caller tilt segment and
caller lex hypotheses.
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

/-- Depth of the frame point `t` at the view `R`. -/
noncomputable def k9z (P Q R d : ℝ³) (t : ℝ × ℝ × ℝ) : ℝ := ⟪fpoint P Q R d t, R⟫
/-- Tilt weight of the frame point `t` for the tilt `v1 P + v2 Q`. -/
noncomputable def k9w (P Q R d : ℝ³) (v1 v2 : ℝ) (t : ℝ × ℝ × ℝ) : ℝ :=
  ⟪fpoint P Q R d t, fcomb P Q R v1 v2 0⟫

theorem k9_wd (P Q R d : ℝ³) (s t : ℝ × ℝ × ℝ) (v1 v2 : ℝ) :
    k9w P Q R d v1 v2 s - k9w P Q R d v1 v2 t =
      (s.1 - t.1) * (v1 * ⟪P, P⟫ + v2 * ⟪P, Q⟫) + (s.2.1 - t.2.1) * (v1 * ⟪P, Q⟫ + v2 * ⟪Q, Q⟫) +
        (s.2.2 - t.2.2) * (v1 * ⟪P, R⟫ + v2 * ⟪Q, R⟫) := by
  unfold k9w
  simp only [fpoint, fcomb, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    inner_zero_right, real_inner_comm P Q, real_inner_comm P R, real_inner_comm Q R]
  ring

theorem k9_zd (P Q R d : ℝ³) (s t : ℝ × ℝ × ℝ) :
    k9z P Q R d s - k9z P Q R d t =
      (s.1 - t.1) * ⟪P, R⟫ + (s.2.1 - t.2.1) * ⟪Q, R⟫ + (s.2.2 - t.2.2) * ⟪R, R⟫ := by
  unfold k9z
  rw [inner_fpoint, inner_fpoint]; ring

set_option maxHeartbeats 6400000 in
/-- **Cell 1** `(b, d, c, b', c')` at `R = b - d`. -/
theorem k9_cell1 (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0)
    {γ4 β1 γ6 β6 : ℝ} (hγ4 : 0 < γ4) (hβ1 : 0 < β1) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) (hβ6 : 0 < β6)
    (u1 u2 t1 t2 : ℝ) (hut : u1 * t2 - u2 * t1 ≠ 0)
    (hcone : ∀ lam : ℝ, 0 < lam → lam < 1 → 0 < u1 + lam * t1 ∧ u2 + lam * t2 < 0)
    (hlex : ∀ lam : ℝ, 0 < lam → lam < 1 →
      (∀ i j, k9z P Q R d (k9Y1 γ4 β1 i) = k9z P Q R d (k9Y1 γ4 β1 j) →
        k9w P Q R d (u1 + lam * t1) (u2 + lam * t2) (k9Y1 γ4 β1 i) =
          k9w P Q R d (u1 + lam * t1) (u2 + lam * t2) (k9Y1 γ4 β1 j) → i = j) →
      LexLt (k9z P Q R d (k9Y1 γ4 β1 1), k9w P Q R d (u1 + lam * t1) (u2 + lam * t2) (k9Y1 γ4 β1 1))
        (k9z P Q R d (k9Y1 γ4 β1 2), k9w P Q R d (u1 + lam * t1) (u2 + lam * t2) (k9Y1 γ4 β1 2)) ∧
      ((LexLt (k9z P Q R d (k9Y1 γ4 β1 0), k9w P Q R d (u1 + lam * t1) (u2 + lam * t2) (k9Y1 γ4 β1 0))
          (k9z P Q R d (k9Y1 γ4 β1 4), k9w P Q R d (u1 + lam * t1) (u2 + lam * t2) (k9Y1 γ4 β1 4)) ∧
        LexLt (k9z P Q R d (k9Y1 γ4 β1 4), k9w P Q R d (u1 + lam * t1) (u2 + lam * t2) (k9Y1 γ4 β1 4))
          (k9z P Q R d (k9Y1 γ4 β1 3), k9w P Q R d (u1 + lam * t1) (u2 + lam * t2) (k9Y1 γ4 β1 3))) ∨
       (LexLt (k9z P Q R d (k9Y1 γ4 β1 2), k9w P Q R d (u1 + lam * t1) (u2 + lam * t2) (k9Y1 γ4 β1 2))
          (k9z P Q R d (k9Y1 γ4 β1 3), k9w P Q R d (u1 + lam * t1) (u2 + lam * t2) (k9Y1 γ4 β1 3)) ∧
        LexLt (k9z P Q R d (k9Y1 γ4 β1 3), k9w P Q R d (u1 + lam * t1) (u2 + lam * t2) (k9Y1 γ4 β1 3))
          (k9z P Q R d (k9Y1 γ4 β1 4), k9w P Q R d (u1 + lam * t1) (u2 + lam * t2) (k9Y1 γ4 β1 4)))))
    (hmem : ∀ i, fpoint P Q R d (k9Y1 γ4 β1 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, 0, 1) ∨ y = fpoint P Q R d (0, 0, 0) ∨
      y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (γ4, 1, 0) ∨ y = fpoint P Q R d (0, 1, β1) ∨
      y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (γ6, 0, β6)) :
    HasLexCellAt V R := by
  set Y := k9Y1 γ4 β1 with hY
  have hr0 : R ≠ 0 := by intro h; rw [h] at hΔ; simp [det3_expand] at hΔ
  have hA : 0 < ⟪R, R⟫ := real_inner_self_pos.2 hr0
  obtain ⟨lam, hl0, hl1, hsep⟩ := exists_sep_tilt P Q R d hΔ Y (k9Y1_inj hγ4 hβ1)
    (u1 := u1) (u2 := u2) (t1 := t1) (t2 := t2) hut (lo := 0) (hi := 1) (by norm_num)
  obtain ⟨hv1, hv2⟩ := hcone lam hl0 hl1
  set v1 := u1 + lam * t1 with hv1def
  set v2 := u2 + lam * t2 with hv2def
  set vv := fcomb P Q R v1 v2 0 with hvv
  obtain ⟨hdc, hPQ⟩ := hlex lam hl0 hl1 hsep
  have hdb : LexLt (k9z P Q R d (Y 1), k9w P Q R d v1 v2 (Y 1)) (k9z P Q R d (Y 0), k9w P Q R d v1 v2 (Y 0)) := by
    left
    have := k9_zd P Q R d (Y 0) (Y 1)
    simp only [hY, k9Y1, pc5_0, pc5_1] at this ⊢
    linarith
  have hlexY : LexUni (fun i => ⟪fpoint P Q R d (Y i), R⟫) (fun i => ⟪fpoint P Q R d (Y i), vv⟫) :=
    lexUni5_k9a _ _ hsep hdb hdc hPQ
  have n0 : -(0 : ZMod 5) = 0 := by decide
  have n1 : -(1 : ZMod 5) = 4 := by decide
  have n2 : -(2 : ZMod 5) = 3 := by decide
  have n3 : -(3 : ZMod 5) = 2 := by decide
  have n4 : -(4 : ZMod 5) = 1 := by decide
  rcases hΔ.lt_or_gt with hneg' | hpos
  · have hD : 0 < -det3 P Q R := by linarith
    have hcyc := k9_cyc1 (v3 := 0) hD hγ4 hβ1 hv1 hv2
    have hra := k9_rest1_a (v3 := 0) hD hγ4 hβ1 hv1 hv2
    have hra' := k9_rest1_a' (v3 := 0) hD hγ4 hβ1 hγ6 hγ61 hβ6 hv1 hv2
    refine ⟨5, inferInstance, fun i => fpoint P Q R d (Y (-i)), vv, ?_⟩
    refine lexCell_coord V P Q R d (by norm_num) (fun i => Y (-i)) (v1, v2, 0)
      (fun i => hmem (-i)) (hcyc_rev hcyc) ?_ (lexUni_neg hlexY)
    intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [n0, hY, k9Y1, pc5_0])).elim
    · exact (hyx 4 (by simp only [n4, hY, k9Y1, pc5_1])).elim
    · exact (hyx 3 (by simp only [n3, hY, k9Y1, pc5_2])).elim
    · exact (hyx 2 (by simp only [n2, hY, k9Y1, pc5_3])).elim
    · exact (hyx 1 (by simp only [n1, hY, k9Y1, pc5_4])).elim
    · exact ⟨_, rfl, hrest_rev hra⟩
    · exact ⟨_, rfl, hrest_rev hra'⟩
  · have hcyc := k9_cyc1 (v3 := 0) hpos hγ4 hβ1 hv1 hv2
    have hra := k9_rest1_a (v3 := 0) hpos hγ4 hβ1 hv1 hv2
    have hra' := k9_rest1_a' (v3 := 0) hpos hγ4 hβ1 hγ6 hγ61 hβ6 hv1 hv2
    refine ⟨5, inferInstance, fun i => fpoint P Q R d (Y i), vv, ?_⟩
    refine lexCell_coord V P Q R d (by norm_num) Y (v1, v2, 0) hmem hcyc ?_ hlexY
    intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [hY, k9Y1, pc5_0])).elim
    · exact (hyx 1 (by simp only [hY, k9Y1, pc5_1])).elim
    · exact (hyx 2 (by simp only [hY, k9Y1, pc5_2])).elim
    · exact (hyx 3 (by simp only [hY, k9Y1, pc5_3])).elim
    · exact (hyx 4 (by simp only [hY, k9Y1, pc5_4])).elim
    · exact ⟨_, rfl, hra⟩
    · exact ⟨_, rfl, hra'⟩

set_option maxHeartbeats 6400000 in
/-- **Cell 2** `(a, d, c, b', c')` at `R = b - d`. -/
theorem k9_cell2 (V : Finset ℝ³) (P Q R d : ℝ³) (hΔ : det3 P Q R ≠ 0)
    {γ4 β1 γ6 β6 : ℝ} (hγ4 : 0 < γ4) (hβ1 : 0 < β1) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) (hβ6 : 0 < β6)
    (u1 u2 t1 t2 : ℝ) (hut : u1 * t2 - u2 * t1 ≠ 0)
    (hcone : ∀ lam : ℝ, 0 < lam → lam < 1 → u1 + lam * t1 < 0 ∧ u2 + lam * t2 < 0)
    (hlex : ∀ lam : ℝ, 0 < lam → lam < 1 →
      LexLt (k9z P Q R d (k9Y2 γ4 β1 1), k9w P Q R d (u1 + lam * t1) (u2 + lam * t2) (k9Y2 γ4 β1 1))
        (k9z P Q R d (k9Y2 γ4 β1 2), k9w P Q R d (u1 + lam * t1) (u2 + lam * t2) (k9Y2 γ4 β1 2)) ∧
      LexLt (k9z P Q R d (k9Y2 γ4 β1 4), k9w P Q R d (u1 + lam * t1) (u2 + lam * t2) (k9Y2 γ4 β1 4))
        (k9z P Q R d (k9Y2 γ4 β1 3), k9w P Q R d (u1 + lam * t1) (u2 + lam * t2) (k9Y2 γ4 β1 3)) ∧
      (LexLt (k9z P Q R d (k9Y2 γ4 β1 0), k9w P Q R d (u1 + lam * t1) (u2 + lam * t2) (k9Y2 γ4 β1 0))
          (k9z P Q R d (k9Y2 γ4 β1 4), k9w P Q R d (u1 + lam * t1) (u2 + lam * t2) (k9Y2 γ4 β1 4)) ∨
        LexLt (k9z P Q R d (k9Y2 γ4 β1 0), k9w P Q R d (u1 + lam * t1) (u2 + lam * t2) (k9Y2 γ4 β1 0))
          (k9z P Q R d (k9Y2 γ4 β1 1), k9w P Q R d (u1 + lam * t1) (u2 + lam * t2) (k9Y2 γ4 β1 1))))
    (hmem : ∀ i, fpoint P Q R d (k9Y2 γ4 β1 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint P Q R d (0, 1, 0) ∨ y = fpoint P Q R d (0, 0, 0) ∨
      y = fpoint P Q R d (1, 0, 0) ∨ y = fpoint P Q R d (γ4, 1, 0) ∨ y = fpoint P Q R d (0, 1, β1) ∨
      y = fpoint P Q R d (0, 0, 1) ∨ y = fpoint P Q R d (γ6, 0, β6)) :
    HasLexCellAt V R := by
  set Y := k9Y2 γ4 β1 with hY
  obtain ⟨lam, hl0, hl1, hsep⟩ := exists_sep_tilt P Q R d hΔ Y (k9Y2_inj hγ4 hβ1)
    (u1 := u1) (u2 := u2) (t1 := t1) (t2 := t2) hut (lo := 0) (hi := 1) (by norm_num)
  obtain ⟨hv1, hv2⟩ := hcone lam hl0 hl1
  set v1 := u1 + lam * t1 with hv1def
  set v2 := u2 + lam * t2 with hv2def
  set vv := fcomb P Q R v1 v2 0 with hvv
  obtain ⟨hdc, hcb, hA⟩ := hlex lam hl0 hl1
  have hlexY : LexUni (fun i => ⟪fpoint P Q R d (Y i), R⟫) (fun i => ⟪fpoint P Q R d (Y i), vv⟫) :=
    lexUni5_k9b _ _ hsep hdc hcb hA
  have n0 : -(0 : ZMod 5) = 0 := by decide
  have n1 : -(1 : ZMod 5) = 4 := by decide
  have n2 : -(2 : ZMod 5) = 3 := by decide
  have n3 : -(3 : ZMod 5) = 2 := by decide
  have n4 : -(4 : ZMod 5) = 1 := by decide
  rcases hΔ.lt_or_gt with hneg' | hpos
  · have hD : 0 < -det3 P Q R := by linarith
    have hcyc := k9_cyc2 (v3 := 0) hD hγ4 hβ1 hv1 hv2
    have hrb := k9_rest2_b (v3 := 0) hD hγ4 hβ1 hv1 hv2
    have hra' := k9_rest2_a' (v3 := 0) hD hγ4 hβ1 hγ6 hγ61 hβ6 hv1 hv2
    refine ⟨5, inferInstance, fun i => fpoint P Q R d (Y (-i)), vv, ?_⟩
    refine lexCell_coord V P Q R d (by norm_num) (fun i => Y (-i)) (v1, v2, 0)
      (fun i => hmem (-i)) (hcyc_rev hcyc) ?_ (lexUni_neg hlexY)
    intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [n0, hY, k9Y2, pc5_0])).elim
    · exact (hyx 4 (by simp only [n4, hY, k9Y2, pc5_1])).elim
    · exact (hyx 3 (by simp only [n3, hY, k9Y2, pc5_2])).elim
    · exact (hyx 2 (by simp only [n2, hY, k9Y2, pc5_3])).elim
    · exact (hyx 1 (by simp only [n1, hY, k9Y2, pc5_4])).elim
    · exact ⟨_, rfl, hrest_rev hrb⟩
    · exact ⟨_, rfl, hrest_rev hra'⟩
  · have hcyc := k9_cyc2 (v3 := 0) hpos hγ4 hβ1 hv1 hv2
    have hrb := k9_rest2_b (v3 := 0) hpos hγ4 hβ1 hv1 hv2
    have hra' := k9_rest2_a' (v3 := 0) hpos hγ4 hβ1 hγ6 hγ61 hβ6 hv1 hv2
    refine ⟨5, inferInstance, fun i => fpoint P Q R d (Y i), vv, ?_⟩
    refine lexCell_coord V P Q R d (by norm_num) Y (v1, v2, 0) hmem hcyc ?_ hlexY
    intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [hY, k9Y2, pc5_0])).elim
    · exact (hyx 1 (by simp only [hY, k9Y2, pc5_1])).elim
    · exact (hyx 2 (by simp only [hY, k9Y2, pc5_2])).elim
    · exact (hyx 3 (by simp only [hY, k9Y2, pc5_3])).elim
    · exact (hyx 4 (by simp only [hY, k9Y2, pc5_4])).elim
    · exact ⟨_, rfl, hrb⟩
    · exact ⟨_, rfl, hra'⟩

end C2
end Type08Sp
end Minimality
