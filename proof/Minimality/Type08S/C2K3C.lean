module

public import Minimality.Type08S.C2K3B

@[expose] public section

/-!
# C2 / K3C: generic cell assembly for package K3, and the cell `Q1⁻ = (c, d, a, c', b, a')` (`β6 < 1`)

`k3_cell_gen`: a cycle `Y` of frame points with a tilt family `(u1 + λ t1, u2 + λ t2, 0)` (`0 < λ < 1`) whose
`TSc` tests hold for every positive orientation constant and every `λ`, and whose depths are lex unimodal for every
injective `w`, gives `HasLexCellAt V r` (both signs of `det3 p q r`, via the reversed cycle).

Q1⁻: tilt `u = (1,-1)`, `t = (1,0)` (as Q1⁺); cycle `(c, d, a, c', b, a')` hides `b'`; depths
`d < c`, `a < c'`, `c' < b` (`s₂ > 0`), `b < a' ∨ c < a'`.
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

set_option maxHeartbeats 1600000 in
theorem k3_cell_gen (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (Y : ZMod k → ℝ × ℝ × ℝ) (hYinj : ∀ i j, Y i = Y j → i = j) {u1 u2 t1 t2 : ℝ} (hut : u1 * t2 - u2 * t1 ≠ 0)
    (hmem : ∀ i, fpoint p q r d (Y i) ∈ V)
    (hcyc : ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ D : ℝ, 0 < D → ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 →
      TSc D (Y (i + 1) - Y i) (Y j - Y i) (u1 + lam * t1, u2 + lam * t2, 0))
    (hrest : ∀ y ∈ V, (∀ j, y ≠ fpoint p q r d (Y j)) → ∃ t, y = fpoint p q r d t ∧
      ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ D : ℝ, 0 < D → ∀ i, TSc D (Y (i + 1) - Y i) (t - Y i)
        (u1 + lam * t1, u2 + lam * t2, 0))
    (hlex : ∀ w : ZMod k → ℝ, (∀ i j, ⟪fpoint p q r d (Y i), r⟫ = ⟪fpoint p q r d (Y j), r⟫ → w i = w j → i = j) →
      LexUni (fun i => ⟪fpoint p q r d (Y i), r⟫) w) :
    HasLexCellAt V r := by
  obtain ⟨lam, hl0, hl1, hsep⟩ := exists_sep_tilt p q r d hΔ Y hYinj hut (lo := 0) (hi := 1) (by norm_num)
  have hlexY := hlex (fun i => ⟪fpoint p q r d (Y i), fcomb p q r (u1 + lam * t1) (u2 + lam * t2) 0⟫)
    (fun i j h1 h2 => hsep i j h1 h2)
  rcases hΔ.lt_or_gt with hneg | hpos
  · have hD : 0 < -det3 p q r := by linarith
    refine ⟨k, inferInstance, fun i => fpoint p q r d (Y (-i)), fcomb p q r (u1 + lam * t1) (u2 + lam * t2) 0, ?_⟩
    refine lexCell_coord V p q r d hk (fun i => Y (-i)) (u1 + lam * t1, u2 + lam * t2, 0)
      (fun i => hmem (-i)) (hcyc_rev (hcyc lam hl0 hl1 _ hD)) ?_ (lexUni_neg hlexY)
    intro y hy hyx
    obtain ⟨t, rfl, ht⟩ := hrest y hy (fun j h => hyx (-j) (by simpa using h))
    exact ⟨t, rfl, hrest_rev (ht lam hl0 hl1 _ hD)⟩
  · refine ⟨k, inferInstance, fun i => fpoint p q r d (Y i), fcomb p q r (u1 + lam * t1) (u2 + lam * t2) 0, ?_⟩
    refine lexCell_coord V p q r d hk Y (u1 + lam * t1, u2 + lam * t2, 0) hmem
      (hcyc lam hl0 hl1 _ hpos) ?_ hlexY
    intro y hy hyx
    obtain ⟨t, rfl, ht⟩ := hrest y hy hyx
    exact ⟨t, rfl, ht lam hl0 hl1 _ hpos⟩

/-- The ccw cycle `(c, d, a, c', b, a')` in the `c - d` frame. -/
def k3q1mCyc (β1 β6 γ6 : ℝ) : ZMod 6 → ℝ × ℝ × ℝ :=
  pc6 (0, 0, 1) (0, 0, 0) (1, 0, 0) (1, β1, 0) (0, 1, 0) (0, β6, γ6)

set_option maxHeartbeats 1600000 in
theorem k3q1m_cyc {D β1 β6 γ6 v1 v2 v3 : ℝ} (hD : 0 < D) (hβ1 : 0 < β1) (hβ6p : 0 < β6) (hβ6 : β6 < 1) (hγ6 : 0 < γ6)
    (hs : 1 < β6 + γ6) (hv1 : 0 < v1) (hv2 : v2 < 0) :
    ∀ i j : ZMod 6, j ≠ i → j ≠ i + 1 →
      TSc D (k3q1mCyc β1 β6 γ6 (i + 1) - k3q1mCyc β1 β6 γ6 i) (k3q1mCyc β1 β6 γ6 j - k3q1mCyc β1 β6 γ6 i)
        (v1, v2, v3) := by
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := z6_add_one
  have k1 := hD
  have kb1 := mul_pos hD hβ1
  have kb6 := mul_pos hD hβ6p
  have kb61 := mul_pos hD (sub_pos.2 hβ6)
  have kg6 := mul_pos hD hγ6
  have ks := mul_pos hD (sub_pos.2 hs)
  have kv1 := mul_pos hD hv1
  have kv2 := mul_pos hD (neg_pos.2 hv2)
  have kgv1 := mul_pos (mul_pos hD hγ6) hv1
  have kgv2 := mul_pos (mul_pos hD hγ6) (neg_pos.2 hv2)
  have kbv1 := mul_pos (mul_pos hD hβ1) hv1
  have kbv2 := mul_pos (mul_pos hD hβ1) (neg_pos.2 hv2)
  have kb6v1 := mul_pos (mul_pos hD hβ6p) hv1
  have kb61v1 := mul_pos (mul_pos hD (sub_pos.2 hβ6)) hv1
  have kb61v2 := mul_pos (mul_pos hD (sub_pos.2 hβ6)) (neg_pos.2 hv2)
  have ksv1 := mul_pos (mul_pos hD (sub_pos.2 hs)) hv1
  intro i j h1 h2'
  rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases z6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact (h2' (by decide)).elim
    | (simp only [TSc, d3, k3q1mCyc, s0, s1, s2, s3, s4, s5, pc6_0, pc6_1, pc6_2, pc6_3, pc6_4, pc6_5,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
       first
       | (left; nlinarith)
       | (right; refine ⟨by ring, by nlinarith⟩))

set_option maxHeartbeats 1600000 in
theorem k3q1m_rest {D β1 γ4 β6 γ6 v1 v2 v3 : ℝ} (hD : 0 < D) (hβ1 : 0 < β1) (hγ4 : 0 < γ4) (hβ6p : 0 < β6) (hβ6 : β6 < 1)
    (hγ6 : 0 < γ6) (hs : 1 < β6 + γ6) (hv1 : 0 < v1) (hv2 : v2 < 0) :
    ∀ i : ZMod 6, TSc D (k3q1mCyc β1 β6 γ6 (i + 1) - k3q1mCyc β1 β6 γ6 i) ((1, 0, γ4) - k3q1mCyc β1 β6 γ6 i)
      (v1, v2, v3) := by
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := z6_add_one
  have k1 := hD
  have kb1 := mul_pos hD hβ1
  have kb6 := mul_pos hD hβ6p
  have kb61 := mul_pos hD (sub_pos.2 hβ6)
  have kg6 := mul_pos hD hγ6
  have kg4 := mul_pos hD hγ4
  have ks := mul_pos hD (sub_pos.2 hs)
  have kv1 := mul_pos hD hv1
  have kv2 := mul_pos hD (neg_pos.2 hv2)
  have kgv1 := mul_pos (mul_pos hD hγ6) hv1
  have kgv2 := mul_pos (mul_pos hD hγ6) (neg_pos.2 hv2)
  have kg4v1 := mul_pos (mul_pos hD hγ4) hv1
  have kg4v2 := mul_pos (mul_pos hD hγ4) (neg_pos.2 hv2)
  have kbv1 := mul_pos (mul_pos hD hβ1) hv1
  have kb6v1 := mul_pos (mul_pos hD hβ6p) hv1
  have kb61v1 := mul_pos (mul_pos hD (sub_pos.2 hβ6)) hv1
  have ksv1 := mul_pos (mul_pos hD (sub_pos.2 hs)) hv1
  intro i
  rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [TSc, d3, k3q1mCyc, s0, s1, s2, s3, s4, s5, pc6_0, pc6_1, pc6_2, pc6_3, pc6_4, pc6_5,
        Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
     first
     | (left; nlinarith)
     | (right; refine ⟨by ring, by nlinarith⟩))

theorem k3q1mCyc_inj {β1 β6 γ6 : ℝ} (hβ1 : 0 < β1) (hβ6 : 0 < β6) (hβ61 : β6 < 1) (hγ6 : 0 < γ6) :
    ∀ i j, k3q1mCyc β1 β6 γ6 i = k3q1mCyc β1 β6 γ6 j → i = j := by
  intro i j h
  rcases z6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases z6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [k3q1mCyc, pc6_0, pc6_1, pc6_2, pc6_3, pc6_4, pc6_5, Prod.mk.injEq] at h <;>
    first | rfl | (exfalso; linarith [h.1, h.2.1, h.2.2]) | (exfalso; norm_num at h)

set_option maxHeartbeats 1600000 in
/-- **The cell `Q1⁻`** (frame form): `β6 < 1`, `C = ⟪q, r⟫ > 0`, `s₂ = (1 - β1) C - B > 0`. -/
theorem k3q1m_hasLexCellAt (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0)
    {β1 γ4 β6 γ6 : ℝ} (hβ1 : 0 < β1) (hγ4 : 0 < γ4) (hβ6p : 0 < β6) (hβ6 : β6 < 1) (hγ6 : 0 < γ6)
    (hs : 1 < β6 + γ6)
    (hC : 0 < ⟪q, r⟫) (hs2 : 0 < (1 - β1) * ⟪q, r⟫ - ⟪p, r⟫)
    (hmem : ∀ i, fpoint p q r d (k3q1mCyc β1 β6 γ6 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint p q r d (0, 0, 1) ∨ y = fpoint p q r d (0, 0, 0) ∨
      y = fpoint p q r d (1, 0, 0) ∨ y = fpoint p q r d (1, β1, 0) ∨ y = fpoint p q r d (0, β6, γ6) ∨
      y = fpoint p q r d (0, 1, 0) ∨ y = fpoint p q r d (1, 0, γ4)) :
    HasLexCellAt V r := by
  set Y := k3q1mCyc β1 β6 γ6 with hY
  have hr0 : r ≠ 0 := by intro h; rw [h] at hΔ; simp [det3_expand] at hΔ
  have hA : 0 < ⟪r, r⟫ := real_inner_self_pos.2 hr0
  have hz : ∀ t : ℝ × ℝ × ℝ, ⟪fpoint p q r d t, r⟫ = ⟪d, r⟫ + t.1 * ⟪p, r⟫ + t.2.1 * ⟪q, r⟫ + t.2.2 * ⟪r, r⟫ :=
    fun t => inner_fpoint _ _ _ _ _ _
  refine k3_cell_gen V p q r d hΔ (by norm_num) Y (k3q1mCyc_inj hβ1 hβ6p hβ6 hγ6) (u1 := 1) (u2 := -1)
    (t1 := 1) (t2 := 0) (by norm_num) hmem ?_ ?_ ?_
  · intro lam hl0 hl1 D hD
    exact k3q1m_cyc hD hβ1 hβ6p hβ6 hγ6 hs (by linarith) (by norm_num)
  · intro y hy hyx
    rcases hVall y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hyx 0 (by simp only [hY, k3q1mCyc, pc6_0])).elim
    · exact (hyx 1 (by simp only [hY, k3q1mCyc, pc6_1])).elim
    · exact (hyx 2 (by simp only [hY, k3q1mCyc, pc6_2])).elim
    · exact (hyx 3 (by simp only [hY, k3q1mCyc, pc6_3])).elim
    · exact (hyx 5 (by simp only [hY, k3q1mCyc, pc6_5])).elim
    · exact (hyx 4 (by simp only [hY, k3q1mCyc, pc6_4])).elim
    · exact ⟨_, rfl, fun lam hl0 hl1 D hD =>
        k3q1m_rest hD hβ1 hγ4 hβ6p hβ6 hγ6 hs (by linarith) (by norm_num)⟩
  · intro w hw
    refine lexUni6_top2 _ w hw ?_ ?_ ?_ ?_
    · left; simp only [hY, k3q1mCyc, pc6_0, pc6_1, hz]; nlinarith
    · left; simp only [hY, k3q1mCyc, pc6_2, pc6_3, hz]; nlinarith [mul_pos hβ1 hC]
    · left; simp only [hY, k3q1mCyc, pc6_3, pc6_4, hz]; nlinarith
    · rcases le_total ⟪q, r⟫ ⟪r, r⟫ with h | h
      · left; left; simp only [hY, k3q1mCyc, pc6_4, pc6_5, hz]
        nlinarith [mul_pos (sub_pos.2 hs) hC, mul_nonneg hγ6.le (sub_nonneg.2 h)]
      · right; left; simp only [hY, k3q1mCyc, pc6_0, pc6_5, hz]
        nlinarith [mul_pos (sub_pos.2 hs) hA, mul_nonneg hβ6p.le (sub_nonneg.2 h)]

end C2
end Type08Sp
end Minimality

