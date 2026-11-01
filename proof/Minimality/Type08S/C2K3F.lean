module

public import Minimality.Type08S.C2K3E

@[expose] public section

/-!
# C2 / K3F: the level-face cells `Q2⁺ = (b', a, c', a', c)` (`β6 > 1`) and `Q2⁻ = (b', a, c', b, a', c)` (`β6 < 1`)

`C = ⟪q, r⟫ = 0`.  Tilt `u = (1,1)`, `t = (1,0)`: `v = (1 + λ, 1)`.  Q2⁺ hides `d, b`, lex `lexUni5_top`
(`a < b'`, `c' < a'` (`s₁ > 0`), `a' < c` (`γ6 < 1`)).  Q2⁻ hides `d`, lex `lexUni6_top2`
(`a < b'`, `c' < b` (`s₂ > 0`), `b < a'`, `a' < c`).
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- The ccw cycle `(b', a, c', a', c)` in the `c - d` frame. -/
def k3q2pCyc (γ4 β1 β6 γ6 : ℝ) : ZMod 5 → ℝ × ℝ × ℝ :=
  pc5 (1, 0, γ4) (1, 0, 0) (1, β1, 0) (0, β6, γ6) (0, 0, 1)

set_option maxHeartbeats 3200000 in
theorem k3q2p_cyc {D γ4 β1 β6 γ6 v1 v2 v3 : ℝ} (hD : 0 < D) (hγ4 : 0 < γ4) (hβ1 : 0 < β1) (hβ6 : 1 < β6)
    (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) (hs : 1 < β6 + γ6) (hv1 : 0 < v1) (hv2 : 0 < v2) :
    ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      TSc D (k3q2pCyc γ4 β1 β6 γ6 (i + 1) - k3q2pCyc γ4 β1 β6 γ6 i)
        (k3q2pCyc γ4 β1 β6 γ6 j - k3q2pCyc γ4 β1 β6 γ6 i) (v1, v2, v3) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have k1 := hD
  have kb1 := mul_pos hD hβ1
  have kb6 := mul_pos hD (lt_trans one_pos hβ6)
  have kb61 := mul_pos hD (sub_pos.2 hβ6)
  have kg6 := mul_pos hD hγ6
  have kg61 := mul_pos hD (sub_pos.2 hγ61)
  have kg4 := mul_pos hD hγ4
  have ks := mul_pos hD (sub_pos.2 hs)
  have kv1 := mul_pos hD hv1
  have kv2 := mul_pos hD hv2
  have kg6v1 := mul_pos (mul_pos hD hγ6) hv1
  have kg61v1 := mul_pos (mul_pos hD (sub_pos.2 hγ61)) hv1
  have kg4v1 := mul_pos (mul_pos hD hγ4) hv1
  have kg4v2 := mul_pos (mul_pos hD hγ4) hv2
  have kb1v1 := mul_pos (mul_pos hD hβ1) hv1
  have kb1v2 := mul_pos (mul_pos hD hβ1) hv2
  have kb61v1 := mul_pos (mul_pos hD (sub_pos.2 hβ6)) hv1
  have ksv1 := mul_pos (mul_pos hD (sub_pos.2 hs)) hv1
  intro i j h1 h2'
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2' (by decide)).elim
    | (simp only [TSc, d3, k3q2pCyc, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 3200000 in
theorem k3q2p_rest {D γ4 β1 β6 γ6 v1 v2 v3 : ℝ} (hD : 0 < D) (hγ4 : 0 < γ4) (hβ1 : 0 < β1) (hβ6 : 1 < β6)
    (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) (hs : 1 < β6 + γ6) (hv1 : 0 < v1) (hv2 : 0 < v2) :
    (∀ i : ZMod 5, TSc D (k3q2pCyc γ4 β1 β6 γ6 (i + 1) - k3q2pCyc γ4 β1 β6 γ6 i)
      ((0, 0, 0) - k3q2pCyc γ4 β1 β6 γ6 i) (v1, v2, v3)) ∧
    (∀ i : ZMod 5, TSc D (k3q2pCyc γ4 β1 β6 γ6 (i + 1) - k3q2pCyc γ4 β1 β6 γ6 i)
      ((0, 1, 0) - k3q2pCyc γ4 β1 β6 γ6 i) (v1, v2, v3)) := by
  obtain ⟨s0, s1, s2, s3, s4⟩ := z5_add
  have k1 := hD
  have kb1 := mul_pos hD hβ1
  have kb6 := mul_pos hD (lt_trans one_pos hβ6)
  have kb61 := mul_pos hD (sub_pos.2 hβ6)
  have kg6 := mul_pos hD hγ6
  have kg61 := mul_pos hD (sub_pos.2 hγ61)
  have kg4 := mul_pos hD hγ4
  have ks := mul_pos hD (sub_pos.2 hs)
  have kv1 := mul_pos hD hv1
  have kv2 := mul_pos hD hv2
  have kg6v1 := mul_pos (mul_pos hD hγ6) hv1
  have kg61v1 := mul_pos (mul_pos hD (sub_pos.2 hγ61)) hv1
  have kg4v1 := mul_pos (mul_pos hD hγ4) hv1
  have kg4v2 := mul_pos (mul_pos hD hγ4) hv2
  have kb1v1 := mul_pos (mul_pos hD hβ1) hv1
  have kb1v2 := mul_pos (mul_pos hD hβ1) hv2
  have kb61v1 := mul_pos (mul_pos hD (sub_pos.2 hβ6)) hv1
  have ksv1 := mul_pos (mul_pos hD (sub_pos.2 hs)) hv1
  refine ⟨?_, ?_⟩ <;> intro i <;>
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [TSc, d3, k3q2pCyc, s0, s1, s2, s3, s4, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
     first
     | (left; nlinarith)
     | (right; refine ⟨by ring, by nlinarith⟩))

theorem k3q2pCyc_inj {γ4 β1 β6 γ6 : ℝ} (hγ4 : 0 < γ4) (hβ1 : 0 < β1) (hβ6 : 1 < β6) (hγ6 : 0 < γ6)
    (hγ61 : γ6 < 1) :
    ∀ i j, k3q2pCyc γ4 β1 β6 γ6 i = k3q2pCyc γ4 β1 β6 γ6 j → i = j := by
  intro i j h
  rcases z5_cases i with rfl | rfl | rfl | rfl | rfl <;>
    rcases z5_cases j with rfl | rfl | rfl | rfl | rfl <;>
    simp only [k3q2pCyc, pc5_0, pc5_1, pc5_2, pc5_3, pc5_4, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith [h.1, h.2.1, h.2.2]) | (exfalso; norm_num at h) |
      (exfalso; obtain ⟨h1, h2, h3⟩ := h; linarith)

set_option maxHeartbeats 3200000 in
/-- **The cell `Q2⁺`** (frame form): `β6 > 1`, `C = ⟪q, r⟫ = 0`, `s₁ = γ6 A - B > 0`. -/
theorem k3q2p_hasLexCellAt (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0)
    {β1 γ4 β6 γ6 : ℝ} (hβ1 : 0 < β1) (hγ4 : 0 < γ4) (hβ6 : 1 < β6) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1)
    (hs : 1 < β6 + γ6)
    (hC : ⟪q, r⟫ = 0) (hs1 : 0 < (β6 - β1) * ⟪q, r⟫ + γ6 * ⟪r, r⟫ - ⟪p, r⟫)
    (hmem : ∀ i, fpoint p q r d (k3q2pCyc γ4 β1 β6 γ6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint p q r d (0, 0, 1) ∨ y = fpoint p q r d (0, 0, 0) ∨
      y = fpoint p q r d (1, 0, 0) ∨ y = fpoint p q r d (1, β1, 0) ∨ y = fpoint p q r d (0, β6, γ6) ∨
      y = fpoint p q r d (0, 1, 0) ∨ y = fpoint p q r d (1, 0, γ4)) :
    HasLexCellAt V r := by
  set Y := k3q2pCyc γ4 β1 β6 γ6 with hY
  have hr0 : r ≠ 0 := by intro h; rw [h] at hΔ; simp [det3_expand] at hΔ
  have hA : 0 < ⟪r, r⟫ := real_inner_self_pos.2 hr0
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint p q r d t, r⟫ = ⟪d, r⟫ + t.1 * ⟪p, r⟫ + t.2.1 * ⟪q, r⟫ + t.2.2 * ⟪r, r⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  refine k3_cell_gen V p q r d hΔ (by norm_num) Y (k3q2pCyc_inj hγ4 hβ1 hβ6 hγ6 hγ61) (u1 := 1) (u2 := 1)
    (t1 := 1) (t2 := 0) (by norm_num) hmem ?_ ?_ ?_
  · intro lam hl0 hl1 D hD
    exact k3q2p_cyc hD hγ4 hβ1 hβ6 hγ6 hγ61 hs (by linarith) (by norm_num)
  · intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 4 (by simp only [hY, k3q2pCyc, pc5_4])).elim
    · exact ⟨_, rfl, fun lam hl0 hl1 D hD =>
        (k3q2p_rest hD hγ4 hβ1 hβ6 hγ6 hγ61 hs (by linarith) (by norm_num)).1⟩
    · exact (hyx 1 (by simp only [hY, k3q2pCyc, pc5_1])).elim
    · exact (hyx 2 (by simp only [hY, k3q2pCyc, pc5_2])).elim
    · exact (hyx 3 (by simp only [hY, k3q2pCyc, pc5_3])).elim
    · exact ⟨_, rfl, fun lam hl0 hl1 D hD =>
        (k3q2p_rest hD hγ4 hβ1 hβ6 hγ6 hγ61 hs (by linarith) (by norm_num)).2⟩
    · exact (hyx 0 (by simp only [hY, k3q2pCyc, pc5_0])).elim
  · intro w hw
    refine lexUni5_top _ _ hw ?_ ?_ ?_
    · left; simp only [hY, k3q2pCyc, pc5_1, pc5_0, hz]; nlinarith [mul_pos hγ4 hA]
    · left; simp only [hY, k3q2pCyc, pc5_2, pc5_3, hz]; nlinarith
    · left; simp only [hY, k3q2pCyc, pc5_3, pc5_4, hz]; nlinarith [mul_pos (sub_pos.2 hγ61) hA]

/-- The ccw cycle `(b', a, c', b, a', c)` in the `c - d` frame. -/
def k3q2mCyc (γ4 β1 β6 γ6 : ℝ) : ZMod 6 → ℝ × ℝ × ℝ :=
  pc6 (1, 0, γ4) (1, 0, 0) (1, β1, 0) (0, 1, 0) (0, β6, γ6) (0, 0, 1)

set_option maxHeartbeats 3200000 in
theorem k3q2m_cyc {D γ4 β1 β6 γ6 v1 v2 v3 : ℝ} (hD : 0 < D) (hγ4 : 0 < γ4) (hβ1 : 0 < β1) (hβ6p : 0 < β6)
    (hβ6 : β6 < 1) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) (hs : 1 < β6 + γ6) (hv1 : 0 < v1) (hv2 : 0 < v2) :
    ∀ i j : ZMod 6, j ≠ i → j ≠ i + 1 →
      TSc D (k3q2mCyc γ4 β1 β6 γ6 (i + 1) - k3q2mCyc γ4 β1 β6 γ6 i)
        (k3q2mCyc γ4 β1 β6 γ6 j - k3q2mCyc γ4 β1 β6 γ6 i) (v1, v2, v3) := by
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := z6_add_one
  have k1 := hD
  have kb1 := mul_pos hD hβ1
  have kb6 := mul_pos hD hβ6p
  have kb61 := mul_pos hD (sub_pos.2 hβ6)
  have kg6 := mul_pos hD hγ6
  have kg61 := mul_pos hD (sub_pos.2 hγ61)
  have kg4 := mul_pos hD hγ4
  have ks := mul_pos hD (sub_pos.2 hs)
  have kv1 := mul_pos hD hv1
  have kv2 := mul_pos hD hv2
  have kg6v1 := mul_pos (mul_pos hD hγ6) hv1
  have kg61v1 := mul_pos (mul_pos hD (sub_pos.2 hγ61)) hv1
  have kg4v1 := mul_pos (mul_pos hD hγ4) hv1
  have kg4v2 := mul_pos (mul_pos hD hγ4) hv2
  have kb1v1 := mul_pos (mul_pos hD hβ1) hv1
  have kb1v2 := mul_pos (mul_pos hD hβ1) hv2
  have kb61v1 := mul_pos (mul_pos hD (sub_pos.2 hβ6)) hv1
  have kb6v1 := mul_pos (mul_pos hD hβ6p) hv1
  have ksv1 := mul_pos (mul_pos hD (sub_pos.2 hs)) hv1
  intro i j h1 h2'
  rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases z6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2' (by decide)).elim
    | (simp only [TSc, d3, k3q2mCyc, s0, s1, s2, s3, s4, s5, pc6_0, pc6_1, pc6_2, pc6_3, pc6_4, pc6_5,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 3200000 in
theorem k3q2m_rest {D γ4 β1 β6 γ6 v1 v2 v3 : ℝ} (hD : 0 < D) (hγ4 : 0 < γ4) (hβ1 : 0 < β1) (hβ6p : 0 < β6)
    (hβ6 : β6 < 1) (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) (hs : 1 < β6 + γ6) (hv1 : 0 < v1) (hv2 : 0 < v2) :
    ∀ i : ZMod 6, TSc D (k3q2mCyc γ4 β1 β6 γ6 (i + 1) - k3q2mCyc γ4 β1 β6 γ6 i)
      ((0, 0, 0) - k3q2mCyc γ4 β1 β6 γ6 i) (v1, v2, v3) := by
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := z6_add_one
  have k1 := hD
  have kb1 := mul_pos hD hβ1
  have kb6 := mul_pos hD hβ6p
  have kb61 := mul_pos hD (sub_pos.2 hβ6)
  have kg6 := mul_pos hD hγ6
  have kg61 := mul_pos hD (sub_pos.2 hγ61)
  have kg4 := mul_pos hD hγ4
  have ks := mul_pos hD (sub_pos.2 hs)
  have kv1 := mul_pos hD hv1
  have kv2 := mul_pos hD hv2
  have kg6v1 := mul_pos (mul_pos hD hγ6) hv1
  have kg61v1 := mul_pos (mul_pos hD (sub_pos.2 hγ61)) hv1
  have kg4v1 := mul_pos (mul_pos hD hγ4) hv1
  have kg4v2 := mul_pos (mul_pos hD hγ4) hv2
  have kb1v1 := mul_pos (mul_pos hD hβ1) hv1
  have kb1v2 := mul_pos (mul_pos hD hβ1) hv2
  have kb61v1 := mul_pos (mul_pos hD (sub_pos.2 hβ6)) hv1
  have kb6v1 := mul_pos (mul_pos hD hβ6p) hv1
  have ksv1 := mul_pos (mul_pos hD (sub_pos.2 hs)) hv1
  intro i
  rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [TSc, d3, k3q2mCyc, s0, s1, s2, s3, s4, s5, pc6_0, pc6_1, pc6_2, pc6_3, pc6_4, pc6_5,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
     first
     | (left; nlinarith)
     | (right; refine ⟨by ring, by nlinarith⟩))

theorem k3q2mCyc_inj {γ4 β1 β6 γ6 : ℝ} (hγ4 : 0 < γ4) (hβ1 : 0 < β1) (hβ6p : 0 < β6) (hβ6 : β6 < 1)
    (hγ6 : 0 < γ6) (hγ61 : γ6 < 1) :
    ∀ i j, k3q2mCyc γ4 β1 β6 γ6 i = k3q2mCyc γ4 β1 β6 γ6 j → i = j := by
  intro i j h
  rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases z6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [k3q2mCyc, pc6_0, pc6_1, pc6_2, pc6_3, pc6_4, pc6_5, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith [h.1, h.2.1, h.2.2]) | (exfalso; norm_num at h) |
      (exfalso; obtain ⟨h1, h2, h3⟩ := h; linarith)

set_option maxHeartbeats 3200000 in
/-- **The cell `Q2⁻`** (frame form): `β6 < 1`, `C = ⟪q, r⟫ = 0`, `s₂ = -B > 0`. -/
theorem k3q2m_hasLexCellAt (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0)
    {β1 γ4 β6 γ6 : ℝ} (hβ1 : 0 < β1) (hγ4 : 0 < γ4) (hβ6p : 0 < β6) (hβ6 : β6 < 1) (hγ6 : 0 < γ6)
    (hγ61 : γ6 < 1) (hs : 1 < β6 + γ6)
    (hC : ⟪q, r⟫ = 0) (hs2 : 0 < (1 - β1) * ⟪q, r⟫ - ⟪p, r⟫)
    (hmem : ∀ i, fpoint p q r d (k3q2mCyc γ4 β1 β6 γ6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint p q r d (0, 0, 1) ∨ y = fpoint p q r d (0, 0, 0) ∨
      y = fpoint p q r d (1, 0, 0) ∨ y = fpoint p q r d (1, β1, 0) ∨ y = fpoint p q r d (0, β6, γ6) ∨
      y = fpoint p q r d (0, 1, 0) ∨ y = fpoint p q r d (1, 0, γ4)) :
    HasLexCellAt V r := by
  set Y := k3q2mCyc γ4 β1 β6 γ6 with hY
  have hr0 : r ≠ 0 := by intro h; rw [h] at hΔ; simp [det3_expand] at hΔ
  have hA : 0 < ⟪r, r⟫ := real_inner_self_pos.2 hr0
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint p q r d t, r⟫ = ⟪d, r⟫ + t.1 * ⟪p, r⟫ + t.2.1 * ⟪q, r⟫ + t.2.2 * ⟪r, r⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  refine k3_cell_gen V p q r d hΔ (by norm_num) Y (k3q2mCyc_inj hγ4 hβ1 hβ6p hβ6 hγ6 hγ61) (u1 := 1) (u2 := 1)
    (t1 := 1) (t2 := 0) (by norm_num) hmem ?_ ?_ ?_
  · intro lam hl0 hl1 D hD
    exact k3q2m_cyc hD hγ4 hβ1 hβ6p hβ6 hγ6 hγ61 hs (by linarith) (by norm_num)
  · intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 5 (by simp only [hY, k3q2mCyc, pc6_5])).elim
    · exact ⟨_, rfl, fun lam hl0 hl1 D hD =>
        k3q2m_rest hD hγ4 hβ1 hβ6p hβ6 hγ6 hγ61 hs (by linarith) (by norm_num)⟩
    · exact (hyx 1 (by simp only [hY, k3q2mCyc, pc6_1])).elim
    · exact (hyx 2 (by simp only [hY, k3q2mCyc, pc6_2])).elim
    · exact (hyx 4 (by simp only [hY, k3q2mCyc, pc6_4])).elim
    · exact (hyx 3 (by simp only [hY, k3q2mCyc, pc6_3])).elim
    · exact (hyx 0 (by simp only [hY, k3q2mCyc, pc6_0])).elim
  · intro w hw
    refine lexUni6_top2 _ w hw ?_ ?_ ?_ ?_
    · left; simp only [hY, k3q2mCyc, pc6_1, pc6_0, hz]; nlinarith [mul_pos hγ4 hA]
    · left; simp only [hY, k3q2mCyc, pc6_2, pc6_3, hz]; nlinarith
    · left; simp only [hY, k3q2mCyc, pc6_3, pc6_4, hz]; nlinarith [mul_pos hγ6 hA]
    · left; left; simp only [hY, k3q2mCyc, pc6_4, pc6_5, hz]; nlinarith [mul_pos (sub_pos.2 hγ61) hA]

end C2
end Type08Sp
end Minimality

