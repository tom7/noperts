module

public import Minimality.Type08S.C2K5ZE

@[expose] public section


set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- Leftover stratum M of the K6P spec: `ρ_a = 0`, `ζ(c',d) > 0 > ζ(b',d)` (view `b - c`). -/
def K6sM (a a' b b' c c' d : ℝ³) : Prop :=
  ⟪a - d, b - c⟫ = 0 ∧ 0 < ⟪c' - d, b - c⟫ ∧ ⟪b' - d, b - c⟫ < 0

/-- M for QN2: `κ_a = 0` and `ParEndN2`. -/
def K6sMN2 (a a' b b' c c' d : ℝ³) : Prop :=
  det3 (c - b) (b' - b) (c' - b) = 0 ∧ ParEndN2 a a' b b' c c' ∧ K6sM a a' b b' c c' d

/-- M for QCEb: `κ_a = 0` and `ParEndKb`. -/
def K6sMKb (a a' b b' c c' d : ℝ³) : Prop :=
  det3 (c - b) (b' - b) (c' - b) = 0 ∧ ParEndKb b b' c c' d ∧ K6sM a a' b b' c c' d

/-- `B = ⟪a-d,b-d⟫ ≠ 0` for `ParEndK2` (Rob4 at `B = 0` forces three equal depths). -/
theorem k6p_B_ne {a b b' c c' d : ℝ³} {α1 α4 l : ℝ} (h : ParEndK2 b b' c c' d)
    (hc' : c' = d + α1 • (a - d) + (1:ℝ) • (b - d)) (hb' : b' = d + α4 • (a - d) + (1:ℝ) • (c - d))
    (heq2 : l * ⟪a - d, b - d⟫ + ⟪b - d, b - d⟫ - ⟪b - d, c - d⟫ = 0) :
    ⟪a - d, b - d⟫ ≠ 0 := by
  intro hB
  obtain ⟨e1, e2, e3, κ, hF, hκ0, hxe, -, -, -, hrob, -⟩ := h
  have hq : b - d = -(κ • e3) := by rw [← hxe]; abel
  have key : ∀ x : ℝ³, ⟪x - b, e3⟫ = ⟪x - d, e3⟫ + κ := by
    intro x
    have : x - b = (x - d) + (d - b) := by abel
    rw [this, inner_add_left, hxe, inner_smul_left, hF.n33]; simp
  have key2 : ∀ x : ℝ³, ⟪x - d, b - d⟫ = -κ * ⟪x - d, e3⟫ := by
    intro x; rw [hq, inner_neg_right, inner_smul_right]; ring
  have hCc : ⟪c - d, b - d⟫ = ⟪b - d, b - d⟫ := by
    have := real_inner_comm (b - d) (c - d); rw [hB] at heq2; linarith
  have e1' : ⟪c' - d, b - d⟫ = ⟪b - d, b - d⟫ := by
    have : c' - d = α1 • (a - d) + (1:ℝ) • (b - d) := by rw [hc']; abel
    rw [this, inner_add_left, inner_smul_left, inner_smul_left]; simp [hB]
  have e2' : ⟪b' - d, b - d⟫ = ⟪b - d, b - d⟫ := by
    have : b' - d = α4 • (a - d) + (1:ℝ) • (c - d) := by rw [hb']; abel
    rw [this, inner_add_left, inner_smul_left, inner_smul_left]; simp [hB, hCc]
  have f1 : ⟪c' - d, e3⟫ = ⟪b' - d, e3⟫ := by
    have h1 := key2 c'; have h2 := key2 b'
    rw [e1'] at h1; rw [e2'] at h2
    have : -κ * (⟪c' - d, e3⟫ - ⟪b' - d, e3⟫) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (by linarith) hκ0
    · linarith
  have f2 : ⟪b' - d, e3⟫ = ⟪c - d, e3⟫ := by
    have h1 := key2 b'; have h2 := key2 c
    rw [e2'] at h1; rw [hCc] at h2
    have : -κ * (⟪b' - d, e3⟫ - ⟪c - d, e3⟫) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (by linarith) hκ0
    · linarith
  exact hrob.t123 ⟨by rw [key c', key b']; linarith, by rw [key b', key c]; linarith⟩

set_option maxHeartbeats 1600000 in
/-- **Generic cell `(a, d, x, a', x')` at `r = a - d`**, `x = (1,0,0)`, `x' = (0,1,α4)`, rest `y = (0,1,0)`,
`y' = (1,0,α1)`, `a' = (β6, γ6, 0)`.  Inner-product hypotheses: `⟪q,r⟫ = ⟪p,r⟫ + m ⟪r,r⟫`, `m > 0`,
`1 < m + α4`, `hcond : 0 < β6 m + α4 (β6+γ6) - (β6+γ6-1)`. -/
theorem k6p_core_hasLexCellAt (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0)
    {α1 α4 β6 γ6 m : ℝ} (hα1 : 0 < α1) (hα4 : 0 < α4) (hβ6 : 0 < β6)
    (hγ6 : 0 < γ6) (hs : 1 < β6 + γ6)
    (hm : 0 ≤ m) (hB0 : 0 < m ∨ ⟪p, r⟫ ≠ 0) (hmα : 1 < m + α4) (hcond : 0 < β6 * m + α4 * (β6 + γ6) - (β6 + γ6 - 1))
    (hC : ⟪q, r⟫ = ⟪p, r⟫ + m * ⟪r, r⟫)
    (hmem : ∀ i, fpoint p q r d (kCyc β6 γ6 α4 i) ∈ V)
    (hVall : ∀ y ∈ V, y = fpoint p q r d (0, 0, 1) ∨ y = fpoint p q r d (0, 0, 0) ∨
      y = fpoint p q r d (1, 0, 0) ∨ y = fpoint p q r d (β6, γ6, 0) ∨ y = fpoint p q r d (0, 1, α4) ∨
      y = fpoint p q r d (0, 1, 0) ∨ y = fpoint p q r d (1, 0, α1)) :
    HasLexCellAt V r := by
  set Y := kCyc β6 γ6 α4 with hY
  have hr0 : r ≠ 0 := by intro h; rw [h] at hΔ; simp [det3_expand] at hΔ
  have hA : 0 < ⟪r, r⟫ := real_inner_self_pos.2 hr0
  obtain ⟨lo, hi, hlh, -, hlam⟩ := k5a_interval hβ6 hγ6 hs
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
  have hlexY : LexUni (fun i => ⟪fpoint p q r d (Y i), r⟫) (fun i => ⟪fpoint p q r d (Y i), vv⟫) := by
    set zz : ZMod 5 → ℝ := fun i => ⟪fpoint p q r d (Y i), r⟫ with hzz
    set ww : ZMod 5 → ℝ := fun i => ⟪fpoint p q r d (Y i), vv⟫ with hww
    have z0 : zz 0 = ⟪d, r⟫ + ⟪r, r⟫ := by simp only [hzz, hY, kCyc, pc5_0, hz]; ring
    have z1 : zz 1 = ⟪d, r⟫ := by simp only [hzz, hY, kCyc, pc5_1, hz]; ring
    have z2 : zz 2 = ⟪d, r⟫ + ⟪p, r⟫ := by simp only [hzz, hY, kCyc, pc5_2, hz]; ring
    have z3 : zz 3 = ⟪d, r⟫ + β6 * ⟪p, r⟫ + γ6 * ⟪q, r⟫ := by simp only [hzz, hY, kCyc, pc5_3, hz]; ring
    have z4 : zz 4 = ⟪d, r⟫ + ⟪q, r⟫ + α4 * ⟪r, r⟫ := by simp only [hzz, hY, kCyc, pc5_4, hz]; ring
    rw [hC] at z3 z4
    have h10 : LexLt (zz 1, ww 1) (zz 0, ww 0) := Or.inl (by rw [z0, z1]; linarith)
    rcases lt_or_ge (⟪p, r⟫) 0 with hB | hB
    · -- B < 0: x < d
      have h21 : LexLt (zz 2, ww 2) (zz 1, ww 1) := Or.inl (by rw [z2, z1]; linarith)
      have hne : ∀ i j : ZMod 5, i ≠ j → (zz i, ww i) ≠ (zz j, ww j) := fun i j hij h =>
        hij (hinj i j (congrArg Prod.fst h) (congrArg Prod.snd h))
      rcases lexLt_total (hne 3 2 (by decide)) with h32 | h23
      · exact lexUni5_adj zz ww hinj h10 h21 (Or.inl h32)
      · rcases lexLt_total (hne 3 4 (by decide)) with h34 | h43
        · exact lexUni5_adj zz ww hinj h10 h21 (Or.inr h34)
        · have h04 : LexLt (zz 0, ww 0) (zz 4, ww 4) := by
            left
            by_contra hcon
            have h43' : zz 4 ≤ zz 3 := by
              rcases h43 with h | ⟨h, -⟩
              · exact h.le
              · exact h.le
            rw [z0, z4] at hcon
            rw [z3, z4] at h43'
            push Not at hcon
            have e1 : 0 ≤ -⟪p, r⟫ - (m + α4 - 1) * ⟪r, r⟫ := by nlinarith
            nlinarith [mul_pos hA hcond, mul_nonneg (by linarith : 0 ≤ β6 + γ6 - 1) e1]
          exact k5a_lexUni5_three zz ww hinj h10 h04 h23 h43
    · -- B ≥ 0: L2
      have hs1 : LexLt (zz 1, ww 1) (zz 0, ww 0) := h10
      apply lexUni_shift_k 1
      refine lexUni5_two _ _ (fun i j h1 h2 => add_right_cancel (hinj _ _ h1 h2)) ?_ ?_ ?_
      · left; simp only [f0, f1, f2, f3, f4, z2, z3]
        rcases hB0 with hm' | hB'
        · nlinarith [mul_nonneg (by linarith : 0 ≤ β6 + γ6 - 1) hB, mul_pos hγ6 (mul_pos hm' hA)]
        · have hBp : 0 < ⟪p, r⟫ := lt_of_le_of_ne hB (Ne.symm hB')
          nlinarith [mul_pos (by linarith : 0 < β6 + γ6 - 1) hBp, mul_nonneg hγ6.le (mul_nonneg hm hA.le)]
      · left; simp only [f0, f1, f2, f3, f4, z0, z4]
        nlinarith [mul_pos (by linarith : 0 < m + α4 - 1) hA]
      · right; simp only [f0, f1, f2, f3, f4]; exact h10
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
