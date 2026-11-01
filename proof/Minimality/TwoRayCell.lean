module

public import Minimality.Type08S.C2K3C
public import Minimality.Type08S.P2RFinalJ

@[expose] public section

/-!
# V1: generic two-ray cell (type-free)

Frame `(p, q, r, d)` with `d = w`, `p = far_P - w`, `q = far_Q - w`, `r = u₀`.  Cycle `Y` of frame points, ccw in the
screen coordinates (first two), with `Y 0 = w = (0,0,0)`, `Y 1 = far_P = (1,0,0)`, `Y (-1) = far_Q = (0,1,0)`.
Depths `⟪·, r⟫` of the corners: distinct and cyclically unimodal.  Every other point of `V` is
* strictly inside the screen polygon, or
* a side point of ray P, `(s, 0, z)`, `0 < s < 1`, `z σP < 0` (inner side of P's plane), or
* a side point of ray Q, `(0, s, z)`, `0 < s < 1`, `z σQ < 0`.
Then `HasLexCellAt V r` (and `IsRupert V`).  The tilt is `v = (σQ (1 + λ/2), σP)` in frame screen coordinates.
-/

set_option autoImplicit true
set_option linter.unusedVariables false
open scoped RealInnerProductSpace
open Finset Filter

namespace Minimality
namespace TwoRay
open Type08Sp Type08Sp.C2

/-- Screen cross product of frame vectors. -/
def cross2 (e f : ℝ × ℝ × ℝ) : ℝ := e.1 * f.2.1 - e.2.1 * f.1

theorem tsc_of_cross {D : ℝ} {e f v : ℝ × ℝ × ℝ} (hD : 0 < D) (h : 0 < cross2 e f) : TSc D e f v := by
  left
  have : d3 e.1 e.2.1 e.2.2 f.1 f.2.1 f.2.2 0 0 1 = cross2 e f := by simp [d3, cross2]
  rw [this]; positivity

theorem lexLt_iff {a b wa wb : ℝ} (h : a ≠ b) : LexLt (a, wa) (b, wb) ↔ a < b := by
  unfold LexLt
  simp only
  constructor
  · rintro (h1 | ⟨h1, _⟩)
    · exact h1
    · exact absurd h1 h
  · exact Or.inl

/-- Distinct depths: the lex unimodality does not depend on the second key. -/
theorem lexUni_any {k : ℕ} [NeZero k] (z w : ZMod k → ℝ) (h : LexUni z (fun _ => 0)) (hk : (1 : ZMod k) ≠ 0) :
    LexUni z w := by
  classical
  have hz : ∀ i j, z i = z j → i = j := fun i j h' => h.1 i j h' rfl
  have hne : ∀ i j : ZMod k, i ≠ j → z i ≠ z j := fun i j hij h' => hij (hz i j h')
  refine ⟨fun i j h1 _ => hz i j h1, ?_⟩
  rw [← h.2]
  congr 1
  apply Finset.filter_congr
  intro i _
  have h1 : i - 1 ≠ i := by intro h'; apply hk; linear_combination -h'
  have h2 : i + 1 ≠ i := by intro h'; apply hk; linear_combination h'
  rw [lexLt_iff (hne _ _ h1), lexLt_iff (hne _ _ h2), lexLt_iff (hne _ _ h1), lexLt_iff (hne _ _ h2)]

section
variable {k : ℕ} [NeZero k]

theorem cross_nonneg (Y : ZMod k → ℝ × ℝ × ℝ)
    (hconv : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < cross2 (Y (i + 1) - Y i) (Y j - Y i)) (i j : ZMod k) :
    0 ≤ cross2 (Y (i + 1) - Y i) (Y j - Y i) := by
  by_cases h1 : j = i
  · subst h1; simp [cross2]
  by_cases h2 : j = i + 1
  · subst h2; simp only [cross2]; ring_nf; exact le_refl _
  exact (hconv i j h1 h2).le

/-- A strict mixture of two corners that are not both on edge `i` is strictly inside edge `i`. -/
theorem mix_inside (Y : ZMod k → ℝ × ℝ × ℝ)
    (hconv : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < cross2 (Y (i + 1) - Y i) (Y j - Y i))
    (a b i : ZMod k) (hab : (a ≠ i ∧ a ≠ i + 1) ∨ (b ≠ i ∧ b ≠ i + 1)) (t : ℝ × ℝ × ℝ) {s : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1)
    (h1 : t.1 = (1 - s) * (Y a).1 + s * (Y b).1) (h2 : t.2.1 = (1 - s) * (Y a).2.1 + s * (Y b).2.1) :
    0 < cross2 (Y (i + 1) - Y i) (t - Y i) := by
  have hid : cross2 (Y (i + 1) - Y i) (t - Y i) =
      (1 - s) * cross2 (Y (i + 1) - Y i) (Y a - Y i) + s * cross2 (Y (i + 1) - Y i) (Y b - Y i) := by
    simp only [cross2, Prod.fst_sub, Prod.snd_sub, h1, h2]; ring
  rw [hid]
  have na := cross_nonneg Y hconv i a
  have nb := cross_nonneg Y hconv i b
  have hs1' : 0 < 1 - s := by linarith
  rcases hab with ⟨ha1, ha2⟩ | ⟨hb1, hb2⟩
  · have := hconv i a ha1 ha2; nlinarith
  · have := hconv i b hb1 hb2; nlinarith

end

theorem two_ne_zero_zmod {k : ℕ} (hk : 3 ≤ k) : (2 : ZMod k) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod k) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  have := Nat.le_of_dvd (by norm_num) this
  omega

theorem one_ne_zero_zmod {k : ℕ} (hk : 3 ≤ k) : (1 : ZMod k) ≠ 0 := by
  intro h
  have : ((1 : ℕ) : ZMod k) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  have := Nat.le_of_dvd (by norm_num) this
  omega

set_option maxHeartbeats 1600000 in
/-- **V1** (frame form).  See the file header. -/
theorem v1_hasLexCellAt (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (Y : ZMod k → ℝ × ℝ × ℝ) (hY0 : Y 0 = (0, 0, 0)) (hY1 : Y 1 = (1, 0, 0)) (hYm : Y (-1) = (0, 1, 0))
    (hmem : ∀ i, fpoint p q r d (Y i) ∈ V)
    (hconv : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < cross2 (Y (i + 1) - Y i) (Y j - Y i))
    (hdep : LexUni (fun i => ⟪fpoint p q r d (Y i), r⟫) (fun _ => 0))
    {σP σQ : ℝ} (hσP : σP ≠ 0) (hσQ : σQ ≠ 0)
    (hV : ∀ y ∈ V, (∀ j, y ≠ fpoint p q r d (Y j)) → ∃ t, y = fpoint p q r d t ∧
      ((∀ i, 0 < cross2 (Y (i + 1) - Y i) (t - Y i)) ∨
       (∃ s z : ℝ, t = (s, 0, z) ∧ 0 < s ∧ s < 1 ∧ z * σP < 0) ∨
       (∃ s z : ℝ, t = (0, s, z) ∧ 0 < s ∧ s < 1 ∧ z * σQ < 0))) :
    HasLexCellAt V r := by
  have h1 := one_ne_zero_zmod hk
  have h2 := two_ne_zero_zmod hk
  have hinj : ∀ i j, Y i = Y j → i = j := by
    intro i j h
    exact hdep.1 i j (by simp [h]) rfl
  have hcyc : ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ D : ℝ, 0 < D → ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 →
      TSc D (Y (i + 1) - Y i) (Y j - Y i) (σQ + lam * (σQ / 2), σP + lam * 0, 0) :=
    fun _ _ _ D hD i j a b => tsc_of_cross hD (hconv i j a b)
  refine k3_cell_gen V p q r d hΔ hk Y hinj (u1 := σQ) (u2 := σP) (t1 := σQ / 2) (t2 := 0)
    (by intro h; apply mul_ne_zero hσP hσQ; linarith) hmem hcyc ?_
    (fun w _ => lexUni_any _ w hdep h1)
  intro y hy hyx
  obtain ⟨t, hyt, ht⟩ := hV y hy hyx
  refine ⟨t, hyt, ?_⟩
  intro lam hl0 hl1 D hD i
  rcases ht with hin | ⟨s, z, rfl, hs0, hs1, hz⟩ | ⟨s, z, rfl, hs0, hs1, hz⟩
  · exact tsc_of_cross hD (hin i)
  · -- side point on ray P
    by_cases hi : i = 0
    · subst hi
      right
      simp only [zero_add, hY1, hY0, d3, Prod.mk_sub_mk, Prod.fst_sub, Prod.snd_sub]
      refine ⟨by ring, ?_⟩
      nlinarith [mul_pos hD (neg_pos.2 hz)]
    · refine tsc_of_cross hD (mix_inside Y hconv 0 1 i ?_ _ hs0 hs1 ?_ ?_)
      · by_cases hi0 : i + 1 = 0
        · right
          exact ⟨fun h => h2 (by linear_combination h + hi0), fun h => hi (by linear_combination -h)⟩
        · left
          exact ⟨fun h => hi h.symm, fun h => hi0 h.symm⟩
      · simp [hY0, hY1]
      · simp [hY0, hY1]
  · -- side point on ray Q
    by_cases hi : i = -1
    · subst hi
      right
      simp only [neg_add_cancel, hYm, hY0, d3, Prod.mk_sub_mk, Prod.fst_sub, Prod.snd_sub]
      refine ⟨by ring, ?_⟩
      have hl : 0 < 1 + lam / 2 := by linarith
      nlinarith [mul_pos (mul_pos hD (neg_pos.2 hz)) hl]
    · refine tsc_of_cross hD (mix_inside Y hconv 0 (-1) i ?_ _ hs0 hs1 ?_ ?_)
      · by_cases hi0 : i = 0
        · right
          exact ⟨fun h => h1 (by subst hi0; linear_combination -h), fun h => h2 (by subst hi0; linear_combination -h)⟩
        · left
          exact ⟨fun h => hi0 h.symm, fun h => hi (by linear_combination -h)⟩
      · simp [hY0, hYm]
      · simp [hY0, hYm]


/-- Three distinct depths on a triangle are automatically cyclically unimodal. -/
theorem lexUni_three (z : ZMod 3 → ℝ) (hinj : ∀ i j, z i = z j → i = j) : LexUni z (fun _ => 0) := by
  classical
  refine ⟨fun i j h _ => hinj i j h, ?_⟩
  have h01 : z 0 ≠ z 1 := fun h => absurd (hinj _ _ h) (by decide)
  have h02 : z 0 ≠ z 2 := fun h => absurd (hinj _ _ h) (by decide)
  have h12 : z 1 ≠ z 2 := fun h => absurd (hinj _ _ h) (by decide)
  rw [Finset.card_filter]
  have hs : ∀ g : ZMod 3 → ℕ, ∑ i, g i = g 0 + g 1 + g 2 := fun g => Fin.sum_univ_three (f := g)
  rw [hs]
  have e0 : (0 : ZMod 3) - 1 = 2 := by decide
  have e1 : (1 : ZMod 3) - 1 = 0 := by decide
  have e2 : (2 : ZMod 3) - 1 = 1 := by decide
  have f0 : (0 : ZMod 3) + 1 = 1 := by decide
  have f1 : (1 : ZMod 3) + 1 = 2 := by decide
  have f2 : (2 : ZMod 3) + 1 = 0 := by decide
  show (if LexLt (z (0 - 1), 0) (z 0, 0) ∧ LexLt (z (0 + 1), 0) (z 0, 0) then 1 else 0) +
    (if LexLt (z (1 - 1), 0) (z 1, 0) ∧ LexLt (z (1 + 1), 0) (z 1, 0) then 1 else 0) +
    (if LexLt (z (2 - 1), 0) (z 2, 0) ∧ LexLt (z (2 + 1), 0) (z 2, 0) then 1 else 0) = 1
  rw [e0, e1, e2, f0, f1, f2]
  simp only [lexLt_iff h01, lexLt_iff h01.symm, lexLt_iff h02, lexLt_iff h02.symm, lexLt_iff h12,
    lexLt_iff h12.symm]
  rcases lt_or_gt_of_ne h01 with a | a <;> rcases lt_or_gt_of_ne h02 with b | b <;>
    rcases lt_or_gt_of_ne h12 with c | c <;>
    simp [a, b, c, a.le, b.le, c.le, not_lt.2 a.le, not_lt.2 b.le, not_lt.2 c.le] <;> linarith

set_option maxHeartbeats 1600000 in
/-- **V1 for `k = 3`** (triangle `w, far_P, far_Q`): no unimodality hypothesis; depths of the three corners distinct. -/
theorem v1_k3 (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0)
    (Y : ZMod 3 → ℝ × ℝ × ℝ) (hY0 : Y 0 = (0, 0, 0)) (hY1 : Y 1 = (1, 0, 0)) (hYm : Y (-1) = (0, 1, 0))
    (hmem : ∀ i, fpoint p q r d (Y i) ∈ V)
    (hdist : ∀ i j, ⟪fpoint p q r d (Y i), r⟫ = ⟪fpoint p q r d (Y j), r⟫ → i = j)
    {σP σQ : ℝ} (hσP : σP ≠ 0) (hσQ : σQ ≠ 0)
    (hV : ∀ y ∈ V, (∀ j, y ≠ fpoint p q r d (Y j)) → ∃ t, y = fpoint p q r d t ∧
      ((∀ i, 0 < cross2 (Y (i + 1) - Y i) (t - Y i)) ∨
       (∃ s z : ℝ, t = (s, 0, z) ∧ 0 < s ∧ s < 1 ∧ z * σP < 0) ∨
       (∃ s z : ℝ, t = (0, s, z) ∧ 0 < s ∧ s < 1 ∧ z * σQ < 0))) :
    HasLexCellAt V r := by
  refine v1_hasLexCellAt V p q r d hΔ (by norm_num) Y hY0 hY1 hYm hmem ?_
    (lexUni_three _ hdist) hσP hσQ hV
  intro i j hji hj
  have hm : (-1 : ZMod 3) = 2 := by decide
  rw [hm] at hYm
  rcases zmod3_cases i with rfl | rfl | rfl <;> rcases zmod3_cases j with rfl | rfl | rfl <;>
    first | exact absurd rfl hji | exact absurd (by decide) hj |
    (simp only [cross2, hY0, hY1, hYm, show (0 : ZMod 3) + 1 = 1 from rfl, show (1 : ZMod 3) + 1 = 2 from rfl,
      show (2 : ZMod 3) + 1 = 0 from rfl, Prod.fst_sub, Prod.snd_sub]; norm_num)

/-- **V1 to Rupert**. -/
theorem v1_isRupert (V : Finset ℝ³) (p q r d : ℝ³) (hΔ : det3 p q r ≠ 0) (h : HasLexCellAt V r) : IsRupert V := by
  have hr0 : r ≠ 0 := by intro h; rw [h] at hΔ; simp [det3_expand] at hΔ
  exact isRupert_of_hasLexCell V ⟨r, hr0, h⟩

end TwoRay
end Minimality

