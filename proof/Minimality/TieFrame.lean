module

public import Minimality.TieRight
public import Minimality.TriTie
public import Minimality.ParallelFar

@[expose] public section

/-!
# Lemma T at the tie, robust form: the oblique frame

The robust tie (`isRupert_of_tilted_tie`) in the oblique frame of
`isRupert_triShadow_gen`: apex `O`, far ends `a = O + A r1`, `b = O + B r2`,
`ρ = cross2 r1 r2 > 0`. Corner generators are positive multiples of `-J r1`
(side 1) or `J r2` (side 2); the test vectors are `m = -(r1 + r2)` and
`p = -r1` (`-r2` mirrored); the far determinant is `λ μ ρ A (r1 · (b - a))`
(mirrored `λ μ ρ B (r2 · (a - b))`), zero exactly at a right angle, where
`isRupert_of_tilted_tie_right` (torques about the other far end) takes over.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### The oblique frame -/

/-- Generators against an oblique test vector `μ1 r1 + μ2 r2`. -/
theorem inner_cross_ez_obl (O r1 r2 : ℝ²) (a b z a' b' z' μ1 μ2 : ℝ) :
    ⟪cross ez (oblPt O r1 r2 a b z - oblPt O r1 r2 a' b' z'), oblPt 0 r1 r2 μ1 μ2 0⟫ =
      ((a - a') * μ2 - (b - b') * μ1) * cross2 r1 r2 := by
  simp [cross, ez, oblPt, cross2, PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem inner_cross_obl_ez (O r1 r2 : ℝ²) (a b z a' b' z' μ1 μ2 : ℝ) :
    ⟪cross (oblPt O r1 r2 a b z - oblPt O r1 r2 a' b' z') ez, oblPt 0 r1 r2 μ1 μ2 0⟫ =
      -(((a - a') * μ2 - (b - b') * μ1) * cross2 r1 r2) := by
  simp [cross, ez, oblPt, cross2, PiLp.inner_apply, Fin.sum_univ_three]; ring

/-- The far determinant in the oblique frame: zero exactly at a right angle at `a`. -/
theorem farDet_obl (O r1 r2 : ℝ²) (A A0 B B1 c z0 z1 : ℝ) :
    farDet (cross ez (oblPt O r1 r2 A0 0 z0 - oblPt O r1 r2 A 0 c))
      (cross (oblPt O r1 r2 0 B c - oblPt O r1 r2 A 0 c) ez)
      (cross (oblPt O r1 r2 0 B1 z1 - oblPt O r1 r2 0 B c) ez)
      (oblPt O r1 r2 A 0 c) (oblPt O r1 r2 0 B c) ez =
      (A - A0) * (B - B1) * cross2 r1 r2 * A *
        (r1 0 * (B * r2 0 - A * r1 0) + r1 1 * (B * r2 1 - A * r1 1)) := by
  simp [farDet, cross, ez, oblPt, cross2, PiLp.inner_apply]; ring

theorem farDet_obl_neg (O r1 r2 : ℝ²) (A A0 B B1 c z0 z1 : ℝ) :
    farDet (cross (oblPt O r1 r2 0 B1 z1 - oblPt O r1 r2 0 B c) ez)
      (cross (oblPt O r1 r2 0 B c - oblPt O r1 r2 A 0 c) ez)
      (cross ez (oblPt O r1 r2 A0 0 z0 - oblPt O r1 r2 A 0 c))
      (oblPt O r1 r2 0 B c) (oblPt O r1 r2 A 0 c) ez =
      (A - A0) * (B - B1) * cross2 r1 r2 * B *
        (r2 0 * (A * r1 0 - B * r2 0) + r2 1 * (A * r1 1 - B * r2 1)) := by
  simp [farDet, cross, ez, oblPt, cross2, PiLp.inner_apply]; ring

/-- The right angle at `a` in the oblique frame. -/
theorem inner_obl_right_a (O r1 r2 : ℝ²) (A B c A0 z0 : ℝ) :
    ⟪oblPt O r1 r2 A 0 c - oblPt O r1 r2 0 B c, oblPt O r1 r2 A0 0 z0 - oblPt O r1 r2 A 0 c⟫ =
      (A - A0) * (r1 0 * (B * r2 0 - A * r1 0) + r1 1 * (B * r2 1 - A * r1 1)) := by
  simp [oblPt, PiLp.inner_apply, Fin.sum_univ_three]; ring

/-- The right angle at `b` in the oblique frame. -/
theorem inner_obl_right_b (O r1 r2 : ℝ²) (A B c B1 z1 : ℝ) :
    ⟪oblPt O r1 r2 A 0 c - oblPt O r1 r2 0 B c, oblPt O r1 r2 0 B1 z1 - oblPt O r1 r2 0 B c⟫ =
      (B1 - B) * (r2 0 * (A * r1 0 - B * r2 0) + r2 1 * (A * r1 1 - B * r2 1)) := by
  simp [oblPt, PiLp.inner_apply, Fin.sum_univ_three]; ring

/-- Torques about a far end of the generators, in the oblique frame. -/
theorem torque_obl_left (O r1 r2 : ℝ²) (a b z a' b' z' a2 b2 z2 a3 b3 z3 : ℝ) :
    ⟪cross (oblPt O r1 r2 a b z - oblPt O r1 r2 a' b' z')
      (cross ez (oblPt O r1 r2 a2 b2 z2 - oblPt O r1 r2 a3 b3 z3)), ez⟫ =
      ((a - a') * r1 0 + (b - b') * r2 0) * ((a2 - a3) * r1 0 + (b2 - b3) * r2 0) +
      ((a - a') * r1 1 + (b - b') * r2 1) * ((a2 - a3) * r1 1 + (b2 - b3) * r2 1) := by
  simp [cross, ez, oblPt, PiLp.inner_apply]; ring

theorem torque_obl_right (O r1 r2 : ℝ²) (a b z a' b' z' a2 b2 z2 a3 b3 z3 : ℝ) :
    ⟪cross (oblPt O r1 r2 a b z - oblPt O r1 r2 a' b' z')
      (cross (oblPt O r1 r2 a2 b2 z2 - oblPt O r1 r2 a3 b3 z3) ez), ez⟫ =
      -(((a - a') * r1 0 + (b - b') * r2 0) * ((a2 - a3) * r1 0 + (b2 - b3) * r2 0) +
      ((a - a') * r1 1 + (b - b') * r2 1) * ((a2 - a3) * r1 1 + (b2 - b3) * r2 1)) := by
  simp [cross, ez, oblPt, PiLp.inner_apply]; ring

/-- The `2 × 2` determinants of `tie_core_right`, in the oblique frame. -/
theorem det2_obl (O r1 r2 : ℝ²) (A B B1 c z1 : ℝ) :
    cross (oblPt O r1 r2 0 B c - oblPt O r1 r2 A 0 c) ez 0 *
        cross (oblPt O r1 r2 0 B1 z1 - oblPt O r1 r2 0 B c) ez 1 -
      cross (oblPt O r1 r2 0 B c - oblPt O r1 r2 A 0 c) ez 1 *
        cross (oblPt O r1 r2 0 B1 z1 - oblPt O r1 r2 0 B c) ez 0 = A * (B - B1) * cross2 r1 r2 := by
  simp [cross, ez, oblPt, cross2]; ring

theorem det2_obl_neg (O r1 r2 : ℝ²) (A A0 B c z0 : ℝ) :
    cross (oblPt O r1 r2 0 B c - oblPt O r1 r2 A 0 c) ez 0 *
        cross ez (oblPt O r1 r2 A0 0 z0 - oblPt O r1 r2 A 0 c) 1 -
      cross (oblPt O r1 r2 0 B c - oblPt O r1 r2 A 0 c) ez 1 *
        cross ez (oblPt O r1 r2 A0 0 z0 - oblPt O r1 r2 A 0 c) 0 = (A0 - A) * B * cross2 r1 r2 := by
  simp [cross, ez, oblPt, cross2]; ring

set_option maxHeartbeats 16000000 in
/-- **Lemma T at the tie, robust form, in the oblique frame.** The setting of
`isRupert_triShadow_gen` in a same-sign sector (`t = -s`), at a tie of the far
depths (`cz m = dz n`), with every other corner strictly on the `s` side of
the tie, and a tilt `(α, β)` with `⟪b - a, α r1 + β r2⟫ ≠ 0`: `V` is Rupert
(first-order free, though not unimodal). If the matching angle (at `a` if
positive, at `b` if negative) is right, the far determinant vanishes and
`isRupert_of_tilted_tie_right` takes over. -/
theorem isRupert_triShadow_robust (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) {m n : ℕ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) (s : ℝ) (hs : s = 1 ∨ s = -1) (t : ℝ) (ht : t = 1 ∨ t = -1) {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (ca cz cb dz : ℕ → ℝ)
    (hca0 : ca 0 = 0) (hcb0 : cb 0 = 0) (hdz0 : dz 0 = cz 0)
    (hca : ∀ l, l < m → ca l < ca (l + 1)) (hcb : ∀ l, l < n → cb l < cb (l + 1))
    (V : Finset ℝ³)
    (hC1V : ∀ l, l ≤ m → oblPt O r1 r2 (ca l) 0 (cz l) ∈ V)
    (hC2V : ∀ l, l ≤ n → oblPt O r1 r2 0 (cb l) (dz l) ∈ V)
    (hVc : ∀ y ∈ V, ∃ a b z, y = oblPt O r1 r2 a b z ∧ 0 ≤ a ∧ 0 ≤ b ∧
      (TiltOK (ca m) 0 (cz m) 0 (cb n) (dz n) a b z (-t * α) (s * β) ∨
        y = oblPt O r1 r2 (ca m) 0 (cz m) ∨ y = oblPt O r1 r2 0 (cb n) (dz n)) ∧
      (b = 0 → ∀ l, l < m → y ≠ oblPt O r1 r2 (ca l) 0 (cz l) →
        y ≠ oblPt O r1 r2 (ca (l + 1)) 0 (cz (l + 1)) →
        s * ((ca (l + 1) - ca l) * (z - cz l) - (cz (l + 1) - cz l) * (a - ca l)) < 0) ∧
      (a = 0 → ∀ l, l < n → y ≠ oblPt O r1 r2 0 (cb (l + 1)) (dz (l + 1)) →
        y ≠ oblPt O r1 r2 0 (cb l) (dz l) →
        t * ((cb l - cb (l + 1)) * (z - dz (l + 1)) - (dz l - dz (l + 1)) * (b - cb (l + 1))) < 0))
    (htS : t = -s) (hsol : (interior (convexHull ℝ (V : Set ℝ³))).Nonempty)
    (htie : cz m = dz n) (hz1 : ∀ l, l < m → 0 < s * (cz l - cz m))
    (hz2 : ∀ k, 0 < k → k < n → 0 < s * (dz k - cz m))
    (hcase : 0 < ⟪oblPt 0 r1 r2 (-ca m) (cb n) 0, oblPt 0 r1 r2 α β 0⟫ ∨
      ⟪oblPt 0 r1 r2 (-ca m) (cb n) 0, oblPt 0 r1 r2 α β 0⟫ < 0) :
    IsRupert V := by
  have hNZ : NeZero (m + n + 1) := ⟨by omega⟩
  have hval : ∀ v : ℕ, v < m + n + 1 → ((v : ZMod (m + n + 1))).val = v := fun v hv => by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hv]
  have hcam : ∀ i j, i < j → j ≤ m → ca i < ca j := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hij with h | h
      · exact lt_trans (ih h (by omega)) (hca j (by omega))
      · subst h; exact hca i (by omega)
  have hcbm : ∀ i j, i < j → j ≤ n → cb i < cb j := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hij with h | h
      · exact lt_trans (ih h (by omega)) (hcb j (by omega))
      · subst h; exact hcb i (by omega)
  set x : ZMod (m + n + 1) → ℝ³ := fun i => triPt O r1 r2 m n ca cz cb dz i.val with hx
  -- positions
  have hxC1 : ∀ v, v ≤ m → x (v : ZMod (m + n + 1)) = oblPt O r1 r2 (ca v) 0 (cz v) := by
    intro v hv; simp only [hx, hval v (by omega), triPt, hv, ite_true]
  have hxC2 : ∀ l, l < n → x ((m + n - l : ℕ) : ZMod (m + n + 1)) =
      oblPt O r1 r2 0 (cb (l + 1)) (dz (l + 1)) := by
    intro l hl
    simp only [hx, hval (m + n - l) (by omega), triPt, show ¬ m + n - l ≤ m by omega, ite_false]
    rw [show m + n + 1 - (m + n - l) = l + 1 by omega]
  have hapex : oblPt O r1 r2 (ca 0) 0 (cz 0) = oblPt O r1 r2 0 (cb 0) (dz 0) := by
    rw [hca0, hcb0, hdz0]
  have hdepth : ∀ i : ZMod (m + n + 1), ⟪x i, ez⟫ = triZ m n cz dz i.val := by
    intro i; simp only [hx, triPt, triZ]; split_ifs <;> exact inner_oblPt_ez _ _ _ _ _ _
  have hxinj : Function.Injective x := by
    have pos : ∀ w, w < m + n + 1 → (w ≤ m ∧ x w = oblPt O r1 r2 (ca w) 0 (cz w)) ∨
        (m < w ∧ x w = oblPt O r1 r2 0 (cb (m + n + 1 - w)) (dz (m + n + 1 - w))) := by
      intro w hw
      by_cases h : w ≤ m
      · exact Or.inl ⟨h, hxC1 w h⟩
      · refine Or.inr ⟨by omega, ?_⟩
        have := hxC2 (m + n - w) (by omega)
        rwa [show m + n - (m + n - w) = w by omega, show m + n - w + 1 = m + n + 1 - w by omega]
          at this
    intro i j h
    obtain ⟨wi, hwi, rfl⟩ : ∃ w, w < m + n + 1 ∧ (w : ZMod (m + n + 1)) = i :=
      ⟨i.val, ZMod.val_lt i, ZMod.natCast_zmod_val i⟩
    obtain ⟨wj, hwj, rfl⟩ : ∃ w, w < m + n + 1 ∧ (w : ZMod (m + n + 1)) = j :=
      ⟨j.val, ZMod.val_lt j, ZMod.natCast_zmod_val j⟩
    suffices wi = wj by rw [this]
    rcases pos wi hwi with ⟨h1, e1⟩ | ⟨h1, e1⟩ <;> rcases pos wj hwj with ⟨h2, e2⟩ | ⟨h2, e2⟩ <;>
      rw [e1, e2] at h <;> have c := oblPt_inj hρ h
    · rcases lt_trichotomy wi wj with l | l | l
      · exact absurd c.1 (hcam _ _ l h2).ne
      · exact l
      · exact absurd c.1 (hcam _ _ l h1).ne'
    · have := hcbm 0 (m + n + 1 - wj) (by omega) (by omega); rw [hcb0] at this; linarith [c.2.1]
    · have := hcbm 0 (m + n + 1 - wi) (by omega) (by omega); rw [hcb0] at this; linarith [c.2.1]
    · rcases lt_trichotomy (m + n + 1 - wi) (m + n + 1 - wj) with l | l | l
      · exact absurd c.2.1 (hcbm _ _ l (by omega)).ne
      · omega
      · exact absurd c.2.1 (hcbm _ _ l (by omega)).ne'
  -- the tilt
  set v : ℝ³ := oblPt 0 r1 r2 (-t * α) (s * β) 0 with hv
  have key : ∀ {ap bp zp aq bq zq ay by' zy : ℝ},
      TiltOK ap bp zp aq bq zq ay by' zy (-t * α) (s * β) →
      TiltSign (oblPt O r1 r2 aq bq zq - oblPt O r1 r2 ap bp zp)
        (oblPt O r1 r2 ay by' zy - oblPt O r1 r2 ap bp zp) ez v :=
    fun h => tiltSign_obl O r1 r2 hρ (-t * α) (s * β) h
  have side1 : ∀ {ap aq zp zq ay zy : ℝ}, s * ((aq - ap) * (zy - zp) - (zq - zp) * (ay - ap)) < 0 →
      TiltOK ap 0 zp aq 0 zq ay 0 zy (-t * α) (s * β) := by
    intro ap aq zp zq ay zy h
    apply tiltOK_side1_on
    rcases hs with rfl | rfl
    · left; exact ⟨by linarith, by linarith⟩
    · right; exact ⟨by linarith, by linarith⟩
  have side2 : ∀ {bp bq zp zq by' zy : ℝ},
      t * ((bq - bp) * (zy - zp) - (zq - zp) * (by' - bp)) < 0 →
      TiltOK 0 bp zp 0 bq zq 0 by' zy (-t * α) (s * β) := by
    intro bp bq zp zq by' zy h
    apply tiltOK_side2_on
    rcases ht with rfl | rfl
    · right; exact ⟨by linarith, by linarith⟩
    · left; exact ⟨by linarith, by linarith⟩
  -- every test of Lemma 8.0
  have tests : ∀ y ∈ V, ∀ i : ZMod (m + n + 1), y ≠ x i → y ≠ x (i + 1) →
      TiltSign (x (i + 1) - x i) (y - x i) ez v := by
    intro y hy i hyi hyi1
    obtain ⟨a, b, z, rfl, ha, hb, hin, hr1, hr2⟩ := hVc y hy
    obtain ⟨w, hwlt, rfl⟩ : ∃ w, w < m + n + 1 ∧ (w : ZMod (m + n + 1)) = i :=
      ⟨i.val, ZMod.val_lt i, ZMod.natCast_zmod_val i⟩
    have hsucc : ((w : ZMod (m + n + 1)) + 1) = ((w + 1 : ℕ) : ZMod (m + n + 1)) := by simp
    rw [hsucc] at hyi1 ⊢
    rcases Nat.lt_or_ge w m with h1 | h1
    · -- a segment of `C1`
      rw [hxC1 w h1.le] at hyi ⊢
      rw [hxC1 (w + 1) h1] at hyi1 ⊢
      apply key
      rcases hb.lt_or_eq with hb | hb
      · exact tiltOK_side1_off (hca _ h1) hb
      · subst hb; exact side1 (hr1 rfl _ h1 hyi hyi1)
    rcases Nat.lt_or_ge w (m + 1) with h2 | h2
    · -- the far edge `A → B`
      have hwm : w = m := by omega
      subst w
      have e1 : x ((m + 1 : ℕ) : ZMod (m + n + 1)) = oblPt O r1 r2 0 (cb n) (dz n) := by
        rw [show m + 1 = m + n - (n - 1) by omega, hxC2 (n - 1) (by omega),
          show n - 1 + 1 = n by omega]
      rw [hxC1 m le_rfl] at hyi ⊢
      rw [e1] at hyi1 ⊢
      apply key
      rcases hin with hin | hin | hin
      · exact hin
      · exact absurd hin hyi
      · exact absurd hin hyi1
    · -- a segment of `C2` (inward), the last one ending at the apex
      obtain ⟨l, hln, rfl⟩ : ∃ l, l < n ∧ m + n - l = w := ⟨m + n - w, by omega, by omega⟩
      have e1 : x ((m + n - l + 1 : ℕ) : ZMod (m + n + 1)) = oblPt O r1 r2 0 (cb l) (dz l) := by
        rcases Nat.eq_zero_or_pos l with hl0 | hl0
        · subst hl0
          rw [show m + n - 0 + 1 = m + n + 1 by omega, ZMod.natCast_self, ← hapex,
            show (0 : ZMod (m + n + 1)) = ((0 : ℕ) : ZMod (m + n + 1)) by simp]
          exact hxC1 0 (Nat.zero_le _)
        · rw [show m + n - l + 1 = m + n - (l - 1) by omega, hxC2 (l - 1) (by omega),
            show l - 1 + 1 = l by omega]
      rw [hxC2 l hln] at hyi ⊢
      rw [e1] at hyi1 ⊢
      apply key
      rcases ha.lt_or_eq with ha | ha
      · exact tiltOK_side2_off (hcb _ hln) ha
      · subst ha; exact side2 (hr2 rfl _ hln hyi hyi1)
  have hcyc : ∀ i j : ZMod (m + n + 1), j ≠ i → j ≠ i + 1 →
      TiltSign (x (i + 1) - x i) (x j - x i) ez v := by
    intro i j h1 h2
    refine tests (x j) ?_ i (fun h => h1 (hxinj h)) (fun h => h2 (hxinj h))
    simp only [hx, triPt]; split_ifs with h
    · exact hC1V _ h
    · exact hC2V _ (by have := ZMod.val_lt j; omega)
  have hrest : ∀ y ∈ V, (∀ j, y ≠ x j) → ∀ i,
      TiltSign (x (i + 1) - x i) (y - x i) ez v :=
    fun y hy hyx i => tests y hy i (hyx i) (hyx (i + 1))
  -- the depths are unimodal
  have hxV : ∀ i, x i ∈ V := by
    intro i; simp only [hx, triPt]; split_ifs with h
    · exact hC1V _ h
    · exact hC2V _ (by have := ZMod.val_lt i; omega)
  -- the robust tie
  have hv0 : v 2 = 0 := by simp [hv, oblPt]
  have hρ' : 0 < cross2 r1 r2 := hρ
  have hcam0 : ∀ j, 0 < j → j ≤ m → 0 < ca j := fun j hj hjm => by
    have := hcam 0 j hj hjm; rwa [hca0] at this
  have hcbm0 : ∀ j, 0 < j → j ≤ n → 0 < cb j := fun j hj hjn => by
    have := hcbm 0 j hj hjn; rwa [hcb0] at this
  -- `C2` positions including the apex (`k = 0`)
  have xC2 : ∀ k, k ≤ n → x ((m + n + 1 - k : ℕ) : ZMod (m + n + 1)) = oblPt O r1 r2 0 (cb k) (dz k) := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [Nat.sub_zero, ZMod.natCast_self, show (0 : ZMod (m + n + 1)) = ((0 : ℕ) : ZMod (m + n + 1)) by simp,
        hxC1 0 (Nat.zero_le _), hapex]
    · rw [show m + n + 1 - k = m + n - (k - 1) by omega, hxC2 (k - 1) (by omega),
        show k - 1 + 1 = k by omega]
  have hcast : ∀ a : ℕ, ((a : ZMod (m + n + 1)) + 1) = ((a + 1 : ℕ) : ZMod (m + n + 1)) := by
    intro a; push_cast; ring
  have hcastsub : ∀ a : ℕ, 1 ≤ a → ((a : ZMod (m + n + 1)) - 1) = ((a - 1 : ℕ) : ZMod (m + n + 1)) := by
    intro a h; rw [Nat.cast_sub h]; simp
  have xa : x (m : ZMod (m + n + 1)) = oblPt O r1 r2 (ca m) 0 (cz m) := hxC1 m le_rfl
  have xb : x ((m : ZMod (m + n + 1)) + 1) = oblPt O r1 r2 0 (cb n) (cz m) := by
    rw [show ((m : ZMod (m + n + 1)) + 1) = ((m + n + 1 - n : ℕ) : ZMod (m + n + 1)) by
      rw [show m + n + 1 - n = m + 1 by omega]; push_cast; ring, xC2 n le_rfl, htie]
  have xa0 : x ((m : ZMod (m + n + 1)) - 1) = oblPt O r1 r2 (ca (m - 1)) 0 (cz (m - 1)) := by
    rw [show ((m : ZMod (m + n + 1)) - 1) = ((m - 1 : ℕ) : ZMod (m + n + 1)) by
      rw [Nat.cast_sub hm]; simp]
    exact hxC1 (m - 1) (by omega)
  have xb1 : x ((m : ZMod (m + n + 1)) + 1 + 1) = oblPt O r1 r2 0 (cb (n - 1)) (dz (n - 1)) := by
    rw [show ((m : ZMod (m + n + 1)) + 1 + 1) = ((m + n + 1 - (n - 1) : ℕ) : ZMod (m + n + 1)) by
      rw [show m + n + 1 - (n - 1) = m + 2 by omega]; push_cast; ring, xC2 (n - 1) (by omega)]
  -- every vertex other than `a`, `b`: a corner of `C1` (`w < m`, the apex at `w = 0`) or of `C2`
  have classify : ∀ i : ZMod (m + n + 1), i ≠ (m : ZMod (m + n + 1)) → i ≠ (m : ZMod (m + n + 1)) + 1 →
      (∃ w, w < m ∧ i = (w : ZMod (m + n + 1))) ∨
        (∃ k, 0 < k ∧ k < n ∧ i = ((m + n + 1 - k : ℕ) : ZMod (m + n + 1))) := by
    intro i h1 h2
    obtain ⟨w, hw, rfl⟩ : ∃ w, w < m + n + 1 ∧ (w : ZMod (m + n + 1)) = i :=
      ⟨i.val, ZMod.val_lt i, ZMod.natCast_zmod_val i⟩
    rcases Nat.lt_or_ge w m with h | h
    · exact Or.inl ⟨w, h, rfl⟩
    · have hwm : w ≠ m := fun e => h1 (by rw [e])
      have hwm1 : w ≠ m + 1 := fun e => h2 (by rw [e]; push_cast; ring)
      exact Or.inr ⟨m + n + 1 - w, by omega, by omega, by rw [show m + n + 1 - (m + n + 1 - w) = w by omega]⟩
  -- neighbours of a `C1` corner `w < m`
  have nbC1 : ∀ w, w < m → x ((w : ZMod (m + n + 1)) + 1) = oblPt O r1 r2 (ca (w + 1)) 0 (cz (w + 1)) := by
    intro w hw; rw [hcast w]; exact hxC1 (w + 1) hw
  have nbC1' : ∀ w, 0 < w → w < m → x ((w : ZMod (m + n + 1)) - 1) = oblPt O r1 r2 (ca (w - 1)) 0 (cz (w - 1)) := by
    intro w hw0 hw; rw [hcastsub w hw0]; exact hxC1 (w - 1) (by omega)
  have nbApex : x (((0 : ℕ) : ZMod (m + n + 1)) - 1) = oblPt O r1 r2 0 (cb 1) (dz 1) := by
    have hself : ((m + n + 1 : ℕ) : ZMod (m + n + 1)) = 0 := ZMod.natCast_self _
    rw [show ((0 : ℕ) : ZMod (m + n + 1)) - 1 = ((m + n + 1 - 1 : ℕ) : ZMod (m + n + 1)) by
      rw [show m + n + 1 - 1 = m + n by omega]; push_cast at hself ⊢; linear_combination -hself]
    exact xC2 1 hn
  -- neighbours of a `C2` corner `k` (index `m + n + 1 - k`)
  have nbC2 : ∀ k, 0 < k → k < n → x (((m + n + 1 - k : ℕ) : ZMod (m + n + 1)) + 1) =
      oblPt O r1 r2 0 (cb (k - 1)) (dz (k - 1)) := by
    intro k hk0 hk
    rw [hcast, show m + n + 1 - k + 1 = m + n + 1 - (k - 1) by omega]; exact xC2 (k - 1) (by omega)
  have nbC2' : ∀ k, 0 < k → k < n → x (((m + n + 1 - k : ℕ) : ZMod (m + n + 1)) - 1) =
      oblPt O r1 r2 0 (cb (k + 1)) (dz (k + 1)) := by
    intro k hk0 hk
    rw [hcastsub _ (by omega), show m + n + 1 - k - 1 = m + n + 1 - (k + 1) by omega]
    exact xC2 (k + 1) (by omega)
  have hC2pos : ∀ k, 0 < k → k < n → x ((m + n + 1 - k : ℕ) : ZMod (m + n + 1)) =
      oblPt O r1 r2 0 (cb k) (dz k) := fun k _ hk => xC2 k hk.le
  set mv : ℝ³ := oblPt 0 r1 r2 (-1) (-1) 0
  have hD' : ∀ σ' : ℝ, σ' = s → s * ⟪x ((m : ZMod (m + n + 1)) + 1) - x (m : ZMod (m + n + 1)), v⟫ =
      ⟪oblPt 0 r1 r2 (-ca m) (cb n) 0, oblPt 0 r1 r2 α β 0⟫ := by
    intro _ _
    rw [xa, xb, hv, htS]
    rcases hs with rfl | rfl <;>
      simp [oblPt, PiLp.inner_apply, Fin.sum_univ_three] <;> ring
  have hXz' : ∀ i, i ≠ (m : ZMod (m + n + 1)) → i ≠ (m : ZMod (m + n + 1)) + 1 →
      0 < s * (x i 2 - x (m : ZMod (m + n + 1)) 2) := by
    intro i h1 h2
    rw [xa]
    rcases classify i h1 h2 with ⟨w, hw, rfl⟩ | ⟨k, hk0, hk, rfl⟩
    · rw [hxC1 w hw.le]; simpa [oblPt] using hz1 w hw
    · rw [hC2pos k hk0 hk]; simpa [oblPt] using hz2 k hk0 hk
  have hmC : ∀ i, i ≠ (m : ZMod (m + n + 1)) → i ≠ (m : ZMod (m + n + 1)) + 1 →
      0 < ⟪cross ez (x (i - 1) - x i), mv⟫ ∧ 0 < ⟪cross (x (i + 1) - x i) ez, mv⟫ := by
    intro i h1 h2
    rcases classify i h1 h2 with ⟨w, hw, rfl⟩ | ⟨k, hk0, hk, rfl⟩
    · rw [hxC1 w hw.le, nbC1 w hw, inner_cross_obl_ez]
      have hinc := hca w hw
      refine ⟨?_, by nlinarith⟩
      rcases Nat.eq_zero_or_pos w with rfl | hw0
      · rw [nbApex, inner_cross_ez_obl, hca0]; have := hcbm0 1 (by omega) hn; nlinarith
      · rw [nbC1' w hw0 hw, inner_cross_ez_obl]
        have := hca (w - 1) (by omega); rw [show w - 1 + 1 = w by omega] at this; nlinarith
    · rw [hC2pos k hk0 hk, nbC2 k hk0 hk, nbC2' k hk0 hk, inner_cross_ez_obl, inner_cross_obl_ez]
      have e1 := hcb k hk
      have e2 := hcb (k - 1) (by omega); rw [show k - 1 + 1 = k by omega] at e2
      exact ⟨by nlinarith, by nlinarith⟩
  have hdetA := farDet_obl O r1 r2 (ca m) (ca (m - 1)) (cb n) (cb (n - 1)) (cz m) (cz (m - 1)) (dz (n - 1))
  have hdetB := farDet_obl_neg O r1 r2 (ca m) (ca (m - 1)) (cb n) (cb (n - 1)) (cz m) (cz (m - 1)) (dz (n - 1))
  have hA0 : 0 < ca m - ca (m - 1) := by have := hca (m - 1) (by omega); rw [show m - 1 + 1 = m by omega] at this; linarith
  have hB0 : 0 < cb n - cb (n - 1) := by have := hcb (n - 1) (by omega); rw [show n - 1 + 1 = n by omega] at this; linarith
  have hAm := hcam0 m hm le_rfl
  have hBn := hcbm0 n hn le_rfl
  rcases hcase with hDp | hDn
  · by_cases hang : r1 0 * (cb n * r2 0 - ca m * r1 0) + r1 1 * (cb n * r2 1 - ca m * r1 1) ≠ 0
    · refine isRupert_of_tilted_tie V hsol v hv0 (by omega) x hxinj hxV hcyc hrest (m : ZMod (m + n + 1))
        mv (oblPt 0 r1 r2 (-1) 0 0) (by rw [xa, xb]; simp [oblPt]) s hs (by rw [hD' s rfl]; exact hDp)
        hXz' hmC ?_ ?_ ?_ ?_
      · intro i h1 h2
        rcases classify i h1 h2 with ⟨w, hw, rfl⟩ | ⟨k, hk0, hk, rfl⟩
        · rw [hxC1 w hw.le, nbC1 w hw, inner_cross_obl_ez]
          refine ⟨?_, by simp⟩
          rcases Nat.eq_zero_or_pos w with rfl | hw0
          · rw [nbApex, inner_cross_ez_obl, hca0]; have := hcbm0 1 (by omega) hn; nlinarith
          · rw [nbC1' w hw0 hw, inner_cross_ez_obl]; simp
        · rw [hC2pos k hk0 hk, nbC2 k hk0 hk, nbC2' k hk0 hk, inner_cross_ez_obl, inner_cross_obl_ez]
          have e1 := hcb k hk
          have e2 := hcb (k - 1) (by omega); rw [show k - 1 + 1 = k by omega] at e2
          exact ⟨by nlinarith, by nlinarith⟩
      · rw [xa0, xa, inner_cross_ez_obl]; simp
      · rw [xb, xa, inner_cross_obl_ez]; nlinarith
      · rw [xa0, xa, xb, xb1, hdetA]
        exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hA0.ne' hB0.ne') hρ'.ne') hAm.ne') hang
    -- a right angle at `a`
    push Not at hang
    refine isRupert_of_tilted_tie_right V hsol v hv0 (by omega) x hxinj hxV hcyc hrest
      (m : ZMod (m + n + 1)) mv (oblPt 0 r1 r2 (-1) 0 0) (by rw [xa, xb]; simp [oblPt]) s hs
      (by rw [hD' s rfl]; exact hDp) hXz' hmC ?_ ?_ ?_ ?_ ?_ ?_
    · intro i h1 h2
      rcases classify i h1 h2 with ⟨w, hw, rfl⟩ | ⟨k, hk0, hk, rfl⟩
      · rw [hxC1 w hw.le, nbC1 w hw, inner_cross_obl_ez]
        refine ⟨?_, by simp⟩
        rcases Nat.eq_zero_or_pos w with rfl | hw0
        · rw [nbApex, inner_cross_ez_obl, hca0]; have := hcbm0 1 (by omega) hn; nlinarith
        · rw [nbC1' w hw0 hw, inner_cross_ez_obl]; simp
      · rw [hC2pos k hk0 hk, nbC2 k hk0 hk, nbC2' k hk0 hk, inner_cross_ez_obl, inner_cross_obl_ez]
        have e1 := hcb k hk
        have e2 := hcb (k - 1) (by omega); rw [show k - 1 + 1 = k by omega] at e2
        exact ⟨by nlinarith, by nlinarith⟩
    · rw [xa0, xa, inner_cross_ez_obl]; simp
    · rw [xb, xa, inner_cross_obl_ez]; nlinarith
    · rw [xa, xb, xa0, inner_obl_right_a, hang, mul_zero]
    · have hr1 : 0 < r1 0 ^ 2 + r1 1 ^ 2 := by
        rcases (show r1 0 ≠ 0 ∨ r1 1 ≠ 0 by
          by_contra h; push Not at h; simp [cross2, h.1, h.2] at hρ') with h | h
        · have := pow_pos (abs_pos.mpr h) 2; rw [sq_abs] at this; nlinarith [sq_nonneg (r1 1)]
        · have := pow_pos (abs_pos.mpr h) 2; rw [sq_abs] at this; nlinarith [sq_nonneg (r1 0)]
      intro i h1 h2
      rcases classify i h1 h2 with ⟨w, hw, rfl⟩ | ⟨k, hk0, hk, rfl⟩
      · have hAw : 0 < ca m - ca w := by have := hcam w m hw le_rfl; linarith
        rw [hxC1 w hw.le, nbC1 w hw, xb]
        refine ⟨?_, Or.inr ?_⟩
        · rcases Nat.eq_zero_or_pos w with rfl | hw0
          · left; rw [nbApex, inner_cross_ez_obl, hca0]; have := hcbm0 1 (by omega) hn; nlinarith
          · right
            rw [nbC1' w hw0 hw, torque_obl_left]
            have hd : 0 < ca w - ca (w - 1) := by
              have := hca (w - 1) (by omega); rw [show w - 1 + 1 = w by omega] at this; linarith
            have hpos := mul_pos (mul_pos hd hAw) hr1
            linear_combination hpos - (ca w - ca (w - 1)) * hang
        · rw [torque_obl_right]
          have hd : 0 < ca (w + 1) - ca w := by have := hca w hw; linarith
          have hpos := mul_pos (mul_pos hd hAw) hr1
          linear_combination hpos - (ca (w + 1) - ca w) * hang
      · rw [hC2pos k hk0 hk, nbC2 k hk0 hk, nbC2' k hk0 hk, inner_cross_ez_obl, inner_cross_obl_ez]
        have e1 := hcb k hk
        have e2 := hcb (k - 1) (by omega); rw [show k - 1 + 1 = k by omega] at e2
        exact ⟨Or.inl (by nlinarith), Or.inl (by nlinarith)⟩
    · rw [xa, xb, xb1, det2_obl]
      exact mul_ne_zero (mul_ne_zero hAm.ne' hB0.ne') hρ'.ne'
  · by_cases hang : r2 0 * (ca m * r1 0 - cb n * r2 0) + r2 1 * (ca m * r1 1 - cb n * r2 1) ≠ 0
    · refine isRupert_of_tilted_tie_neg V hsol v hv0 (by omega) x hxinj hxV hcyc hrest (m : ZMod (m + n + 1))
        mv (oblPt 0 r1 r2 0 (-1) 0) (by rw [xa, xb]; simp [oblPt]) s hs ?_ ?_ hmC ?_ ?_ ?_ ?_
      · have := hD' s rfl
        have e : s * ⟪x (m : ZMod (m + n + 1)) - x ((m : ZMod (m + n + 1)) + 1), v⟫ =
            -(s * ⟪x ((m : ZMod (m + n + 1)) + 1) - x (m : ZMod (m + n + 1)), v⟫) := by
          rw [← neg_sub, inner_neg_left]; ring
        rw [e, this]; linarith
      · intro i h1 h2
        have := hXz' i h1 h2
        rwa [xb, show (oblPt O r1 r2 0 (cb n) (cz m)) 2 = cz m by simp [oblPt], ← show
          (oblPt O r1 r2 (ca m) 0 (cz m)) 2 = cz m by simp [oblPt], ← xa]
      · intro i h1 h2
        rcases classify i h1 h2 with ⟨w, hw, rfl⟩ | ⟨k, hk0, hk, rfl⟩
        · rw [hxC1 w hw.le, nbC1 w hw, inner_cross_obl_ez]
          have hinc := hca w hw
          refine ⟨?_, by nlinarith⟩
          rcases Nat.eq_zero_or_pos w with rfl | hw0
          · rw [nbApex, inner_cross_ez_obl, hca0]; simp
          · rw [nbC1' w hw0 hw, inner_cross_ez_obl]
            have := hca (w - 1) (by omega); rw [show w - 1 + 1 = w by omega] at this; nlinarith
        · rw [hC2pos k hk0 hk, nbC2 k hk0 hk, nbC2' k hk0 hk, inner_cross_ez_obl, inner_cross_obl_ez]
          exact ⟨by simp, by simp⟩
      · rw [xb1, xb, inner_cross_obl_ez]; simp
      · rw [xb, xa, inner_cross_obl_ez]; nlinarith
      · rw [xa0, xa, xb, xb1, hdetB]
        exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hA0.ne' hB0.ne') hρ'.ne') hBn.ne') hang
    -- a right angle at `b`
    push Not at hang
    refine isRupert_of_tilted_tie_right_neg V hsol v hv0 (by omega) x hxinj hxV hcyc hrest
      (m : ZMod (m + n + 1)) mv (oblPt 0 r1 r2 0 (-1) 0) (by rw [xa, xb]; simp [oblPt]) s hs ?_ ?_
      hmC ?_ ?_ ?_ ?_ ?_ ?_
    · have := hD' s rfl
      have e : s * ⟪x (m : ZMod (m + n + 1)) - x ((m : ZMod (m + n + 1)) + 1), v⟫ =
          -(s * ⟪x ((m : ZMod (m + n + 1)) + 1) - x (m : ZMod (m + n + 1)), v⟫) := by
        rw [← neg_sub, inner_neg_left]; ring
      rw [e, this]; linarith
    · intro i h1 h2
      have := hXz' i h1 h2
      rwa [xb, show (oblPt O r1 r2 0 (cb n) (cz m)) 2 = cz m by simp [oblPt], ← show
        (oblPt O r1 r2 (ca m) 0 (cz m)) 2 = cz m by simp [oblPt], ← xa]
    · intro i h1 h2
      rcases classify i h1 h2 with ⟨w, hw, rfl⟩ | ⟨k, hk0, hk, rfl⟩
      · rw [hxC1 w hw.le, nbC1 w hw, inner_cross_obl_ez]
        have hinc := hca w hw
        refine ⟨?_, by nlinarith⟩
        rcases Nat.eq_zero_or_pos w with rfl | hw0
        · rw [nbApex, inner_cross_ez_obl, hca0]; simp
        · rw [nbC1' w hw0 hw, inner_cross_ez_obl]
          have := hca (w - 1) (by omega); rw [show w - 1 + 1 = w by omega] at this; nlinarith
      · rw [hC2pos k hk0 hk, nbC2 k hk0 hk, nbC2' k hk0 hk, inner_cross_ez_obl, inner_cross_obl_ez]
        exact ⟨by simp, by simp⟩
    · rw [xb1, xb, inner_cross_obl_ez]; simp
    · rw [xb, xa, inner_cross_obl_ez]; nlinarith
    · rw [xa, xb, xb1, inner_obl_right_b, hang, mul_zero]
    · have hr2 : 0 < r2 0 ^ 2 + r2 1 ^ 2 := by
        rcases (show r2 0 ≠ 0 ∨ r2 1 ≠ 0 by
          by_contra h; push Not at h; simp [cross2, h.1, h.2] at hρ') with h | h
        · have := pow_pos (abs_pos.mpr h) 2; rw [sq_abs] at this; nlinarith [sq_nonneg (r2 1)]
        · have := pow_pos (abs_pos.mpr h) 2; rw [sq_abs] at this; nlinarith [sq_nonneg (r2 0)]
      intro i h1 h2
      rcases classify i h1 h2 with ⟨w, hw, rfl⟩ | ⟨k, hk0, hk, rfl⟩
      · rw [hxC1 w hw.le, nbC1 w hw, xa]
        have hinc := hca w hw
        refine ⟨?_, Or.inl ?_⟩
        · rcases Nat.eq_zero_or_pos w with rfl | hw0
          · right
            rw [nbApex, torque_obl_left, hca0]
            have hpos := mul_pos (mul_pos (hcbm0 1 (by omega) hn) hBn) hr2
            linear_combination hpos - cb 1 * hang
          · left
            rw [nbC1' w hw0 hw, inner_cross_ez_obl]
            have := hca (w - 1) (by omega); rw [show w - 1 + 1 = w by omega] at this; nlinarith
        · rw [inner_cross_obl_ez]; nlinarith
      · have hBk : 0 < cb n - cb k := by have := hcbm k n hk le_rfl; linarith
        rw [hC2pos k hk0 hk, nbC2 k hk0 hk, nbC2' k hk0 hk, xa]
        refine ⟨Or.inr ?_, Or.inr ?_⟩
        · rw [torque_obl_left]
          have hd : 0 < cb (k + 1) - cb k := by have := hcb k hk; linarith
          have hpos := mul_pos (mul_pos hd hBk) hr2
          linear_combination hpos - (cb (k + 1) - cb k) * hang
        · rw [torque_obl_right]
          have hd : 0 < cb k - cb (k - 1) := by
            have := hcb (k - 1) (by omega); rw [show k - 1 + 1 = k by omega] at this; linarith
          have hpos := mul_pos (mul_pos hd hBk) hr2
          linear_combination hpos - (cb k - cb (k - 1)) * hang
    · rw [xa, xb, xa0, det2_obl_neg]
      exact mul_ne_zero (mul_ne_zero (by linarith) hBn.ne') hρ'.ne'

/-- A finite sequence with no interior local minimum (`ChainOK.conc`) exceeds
the smaller of its end values at every interior index. -/
theorem gt_min_ends_of_conc {f : ℕ → ℝ} {m : ℕ}
    (hc : ∀ l, 1 ≤ l → l < m → min (f (l - 1)) (f (l + 1)) < f l) :
    ∀ l, 0 < l → l < m → min (f 0) (f m) < f l := by
  intro l hl0 hlm
  obtain ⟨g, hg, hgmin⟩ := (range (m + 1)).exists_min_image f ⟨0, by simp⟩
  have hgm : g ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hg)
  -- the minimum is not interior
  have hend : g = 0 ∨ g = m := by
    by_contra h
    push Not at h
    have := hc g (by omega) (by omega)
    have h1 := hgmin (g - 1) (mem_range.mpr (by omega))
    have h2 := hgmin (g + 1) (mem_range.mpr (by omega))
    rw [min_lt_iff] at this
    rcases this with h3 | h3 <;> linarith
  have hfl : f g ≤ f l := hgmin l (mem_range.mpr (by omega))
  have hstrict : f g < f l := by
    rcases hfl.lt_or_eq with h | h
    · exact h
    · -- `l` would be an interior minimum
      have := hc l hl0 hlm
      have h1 := hgmin (l - 1) (mem_range.mpr (by omega))
      have h2 := hgmin (l + 1) (mem_range.mpr (by omega))
      rw [min_lt_iff] at this
      rcases this with h3 | h3 <;> linarith
  rcases hend with rfl | rfl
  · exact lt_of_le_of_lt (min_le_left _ _) hstrict
  · exact lt_of_le_of_lt (min_le_right _ _) hstrict

/-- A tilt `(α, β)` for the robust tie exists unless the far triangle has a
right angle at `a` or at `b`. -/
theorem exists_tie_tilt (O r1 r2 : ℝ²) (A B : ℝ)
    (ha : r1 0 * (B * r2 0 - A * r1 0) + r1 1 * (B * r2 1 - A * r1 1) ≠ 0)
    (hb : r2 0 * (A * r1 0 - B * r2 0) + r2 1 * (A * r1 1 - B * r2 1) ≠ 0) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧
      ((0 < ⟪oblPt 0 r1 r2 (-A) B 0, oblPt 0 r1 r2 α β 0⟫ ∧
        r1 0 * (B * r2 0 - A * r1 0) + r1 1 * (B * r2 1 - A * r1 1) ≠ 0) ∨
      (⟪oblPt 0 r1 r2 (-A) B 0, oblPt 0 r1 r2 α β 0⟫ < 0 ∧
        r2 0 * (A * r1 0 - B * r2 0) + r2 1 * (A * r1 1 - B * r2 1) ≠ 0)) := by
  set p1 := r1 0 * (B * r2 0 - A * r1 0) + r1 1 * (B * r2 1 - A * r1 1)
  set p2 := r2 0 * (B * r2 0 - A * r1 0) + r2 1 * (B * r2 1 - A * r1 1)
  have hp2 : p2 ≠ 0 := by
    intro h; apply hb
    have : r2 0 * (A * r1 0 - B * r2 0) + r2 1 * (A * r1 1 - B * r2 1) = -p2 := by
      simp only [p2]; ring
    rw [this, h, neg_zero]
  have key : ∀ α β, ⟪oblPt 0 r1 r2 (-A) B 0, oblPt 0 r1 r2 α β 0⟫ = α * p1 + β * p2 := by
    intro α β
    simp [oblPt, PiLp.inner_apply, Fin.sum_univ_three, p1, p2]; ring
  -- a tiny `β` keeps the sign of `p1`
  set β := |p1| / (2 * (|p2| + 1))
  have hβ : 0 < β := by
    have := abs_pos.mpr ha; positivity
  have hsmall : |β * p2| < |p1| := by
    rw [abs_mul, abs_of_pos hβ]
    have h1 : 0 < |p1| := abs_pos.mpr ha
    have : |p1| / (2 * (|p2| + 1)) * |p2| ≤ |p1| / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [abs_nonneg p2]
    linarith
  refine ⟨1, β, one_pos, hβ, ?_⟩
  rw [key]
  rcases lt_or_gt_of_ne ha with h | h
  · right
    refine ⟨?_, hb⟩
    have := (abs_lt.mp hsmall).2; rw [abs_of_neg h] at this; linarith
  · left
    refine ⟨?_, ha⟩
    have := (abs_lt.mp hsmall).1; rw [abs_of_pos h] at this; linarith

/-- A tilt `(α, β)` for the robust tie always exists: `⟪b - a, α r1 + β r2⟫ ≠ 0`
for `(1, 1)` or `(1, 2)`, since `b - a` is not orthogonal to both `r1` and `r2`. -/
theorem exists_tie_tilt' (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (A B : ℝ) (hB : 0 < B) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ (0 < ⟪oblPt 0 r1 r2 (-A) B 0, oblPt 0 r1 r2 α β 0⟫ ∨
      ⟪oblPt 0 r1 r2 (-A) B 0, oblPt 0 r1 r2 α β 0⟫ < 0) := by
  set p1 := r1 0 * (B * r2 0 - A * r1 0) + r1 1 * (B * r2 1 - A * r1 1)
  set p2 := r2 0 * (B * r2 0 - A * r1 0) + r2 1 * (B * r2 1 - A * r1 1)
  have key : ∀ α β, ⟪oblPt 0 r1 r2 (-A) B 0, oblPt 0 r1 r2 α β 0⟫ = α * p1 + β * p2 := by
    intro α β
    simp [oblPt, PiLp.inner_apply, Fin.sum_univ_three, p1, p2]; ring
  have hne : ¬ (p1 = 0 ∧ p2 = 0) := by
    rintro ⟨h1, h2⟩
    have hu : (B * r2 0 - A * r1 0) ^ 2 + (B * r2 1 - A * r1 1) ^ 2 = 0 := by
      linear_combination B * h2 - A * h1
    have u0 : B * r2 0 - A * r1 0 = 0 := by
      nlinarith [sq_nonneg (B * r2 0 - A * r1 0), sq_nonneg (B * r2 1 - A * r1 1)]
    have u1 : B * r2 1 - A * r1 1 = 0 := by
      nlinarith [sq_nonneg (B * r2 0 - A * r1 0), sq_nonneg (B * r2 1 - A * r1 1)]
    have : B * cross2 r1 r2 = 0 := by
      simp only [cross2]; linear_combination r1 0 * u1 - r1 1 * u0
    have := mul_pos hB hρ; linarith
  have ne : ∀ d : ℝ, d ≠ 0 → 0 < d ∨ d < 0 := fun d hd => (lt_or_gt_of_ne hd).symm
  by_cases h : p1 + p2 = 0
  · refine ⟨1, 2, one_pos, two_pos, ne _ ?_⟩
    rw [key]; intro h'
    exact hne ⟨by linarith, by linarith⟩
  · exact ⟨1, 1, one_pos, one_pos, ne _ (by rw [key]; intro h'; exact h (by linarith))⟩

set_option maxHeartbeats 8000000 in
/-- **Lemma T at the tie, robust form, from chains.** The setting of
`isRupert_vertex_frame_tie` with the far depths tied and the apex off the tie
depth: `V` (a solid) is Rupert. -/
theorem isRupert_vertex_frame_robust (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (Q1 Q2 : ℝ → ℝ → Prop)
    {z0 : ℝ}
    (hU1 : ∃ m ca cz, ChainOK Q1 z0 1 m ca cz) (hL1 : ∃ m ca cz, ChainOK Q1 z0 (-1) m ca cz)
    (hU2 : ∃ m ca cz, ChainOK Q2 z0 1 m ca cz) (hL2 : ∃ m ca cz, ChainOK Q2 z0 (-1) m ca cz)
    (hap1 : ∀ z, Q1 0 z → z = z0) (hap2 : ∀ z, Q2 0 z → z = z0)
    (hpos1 : ∀ a z, Q1 a z → 0 ≤ a) (hpos2 : ∀ b z, Q2 b z → 0 ≤ b)
    (V : Finset ℝ³)
    (hV1 : ∀ a z, Q1 a z → oblPt O r1 r2 a 0 z ∈ V) (hV2 : ∀ b z, Q2 b z → oblPt O r1 r2 0 b z ∈ V)
    (hVc : ∀ y ∈ V, ∃ a b z, y = oblPt O r1 r2 a b z ∧
      ((b = 0 ∧ Q1 a z) ∨ (a = 0 ∧ Q2 b z) ∨ (0 < a ∧ 0 < b ∧
        ∀ m ca cz n cb dz, ChainOK Q1 z0 1 m ca cz → ChainOK Q2 z0 1 n cb dz →
          a * cb n + b * ca m < ca m * cb n)))
    (hsol : (interior (convexHull ℝ (V : Set ℝ³))).Nonempty)
    (hrob : ∀ m ca cz n cb dz, ChainOK Q1 z0 1 m ca cz → ChainOK Q2 z0 1 n cb dz →
      cz m = dz n ∧ z0 ≠ cz m) :
    IsRupert V := by
  obtain ⟨m0, ca0, cz0, U1⟩ := hU1
  obtain ⟨n0, cb0, dz0, U2⟩ := hU2
  obtain ⟨m1, ca1, cz1, L1⟩ := hL1
  obtain ⟨n1, cb1, dz1, L2⟩ := hL2
  obtain ⟨htie0, hz0⟩ := hrob m0 ca0 cz0 n0 cb0 dz0 U1 U2
  have ch1 : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ∃ m ca cz, ChainOK Q1 z0 σ m ca cz := by
    rintro σ (rfl | rfl)
    exacts [⟨m0, ca0, cz0, U1⟩, ⟨m1, ca1, cz1, L1⟩]
  have ch2 : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ∃ n cb dz, ChainOK Q2 z0 σ n cb dz := by
    rintro σ (rfl | rfl)
    exacts [⟨n0, cb0, dz0, U2⟩, ⟨n1, cb1, dz1, L2⟩]
  -- the side of the tie the apex lies on
  obtain ⟨s, hs, hsz⟩ : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ 0 < s * (z0 - cz0 m0) := by
    rcases lt_or_gt_of_ne hz0 with h | h
    · exact ⟨-1, Or.inr rfl, by linarith⟩
    · exact ⟨1, Or.inl rfl, by linarith⟩
  obtain ⟨m, ca, cz, C1⟩ := ch1 s hs
  obtain ⟨n, cb, dz, C2⟩ := ch2 s hs
  have e1 := C1.far_eq U1
  have e2 := C2.far_eq U2
  set t : ℝ := -s with htdef
  have ht : t = 1 ∨ t = -1 := by
    rw [htdef]; rcases hs with h | h <;> rw [h] <;> norm_num
  replace C2 : ChainOK Q2 z0 (-t) n cb dz := by rw [htdef, neg_neg]; exact C2
  have hA0 := C1.far_pos
  have hB0 := C2.far_pos
  have c10 := C1.start; have c20 := C2.start
  have far1 : ∀ a z, Q1 a z → a * cb n < ca m * cb n ∨ (a = ca m ∧ z = cz m) := by
    intro a z hq
    by_cases h : a = ca m ∧ z = cz m
    · exact Or.inr h
    · left; exact mul_lt_mul_of_pos_right (C1.far a z hq h) hB0
  have far2 : ∀ b z, Q2 b z → b * ca m < cb n * ca m ∨ (b = cb n ∧ z = dz n) := by
    intro b z hq
    by_cases h : b = cb n ∧ z = dz n
    · exact Or.inr h
    · left; exact mul_lt_mul_of_pos_right (C2.far b z hq h) hA0
  have side1 : ∀ a z, Q1 a z → ∀ l, l < m → oblPt O r1 r2 a 0 z ≠ oblPt O r1 r2 (ca l) 0 (cz l) →
      oblPt O r1 r2 a 0 z ≠ oblPt O r1 r2 (ca (l + 1)) 0 (cz (l + 1)) →
      s * ((ca (l + 1) - ca l) * (z - cz l) - (cz (l + 1) - cz l) * (a - ca l)) < 0 := by
    intro a z hq l hl h1 h2
    exact C1.side a z hq l hl (fun ⟨e1, e2⟩ => h1 (by rw [e1, e2]))
      (fun ⟨e1, e2⟩ => h2 (by rw [e1, e2]))
  have side2 : ∀ b z, Q2 b z → ∀ l, l < n →
      oblPt O r1 r2 0 b z ≠ oblPt O r1 r2 0 (cb (l + 1)) (dz (l + 1)) →
      oblPt O r1 r2 0 b z ≠ oblPt O r1 r2 0 (cb l) (dz l) →
      t * ((cb l - cb (l + 1)) * (z - dz (l + 1)) - (dz l - dz (l + 1)) * (b - cb (l + 1))) < 0 := by
    intro b z hq l hl h1 h2
    have := C2.side b z hq l hl (fun ⟨e1, e2⟩ => h2 (by rw [e1, e2]))
      (fun ⟨e1, e2⟩ => h1 (by rw [e1, e2]))
    have e : t * ((cb l - cb (l + 1)) * (z - dz (l + 1)) - (dz l - dz (l + 1)) * (b - cb (l + 1))) =
      -t * ((cb (l + 1) - cb l) * (z - dz l) - (dz (l + 1) - dz l) * (b - cb l)) := by ring
    rw [e]; exact this
  have q20 : Q2 0 z0 := by rw [← c20.2, ← c20.1]; exact C2.mem 0 (Nat.zero_le _)
  have q10 : Q1 0 z0 := by rw [← c10.2, ← c10.1]; exact C1.mem 0 (Nat.zero_le _)

  have htie : cz m = dz n := by rw [e1.2, e2.2]; exact htie0
  have hz1 : ∀ l, l < m → 0 < s * (cz l - cz m) := by
    intro l hl
    rw [e1.2]
    rcases Nat.eq_zero_or_pos l with rfl | hl0
    · rw [c10.2]; exact hsz
    · have hc := gt_min_ends_of_conc (f := fun l => s * cz l) (m := m) C1.conc l hl0 hl
      have h0 : s * cz m < s * cz 0 := by rw [c10.2, e1.2]; linarith
      simp only [min_eq_right h0.le] at hc
      rw [← e1.2]; linarith
  have hz2 : ∀ k, 0 < k → k < n → 0 < s * (dz k - cz m) := by
    intro k hk0 hk
    have C2' : ChainOK Q2 z0 s n cb dz := by rw [htdef, neg_neg] at C2; exact C2
    have hc := gt_min_ends_of_conc (f := fun l => s * dz l) (m := n) C2'.conc k hk0 hk
    have h0 : s * dz n < s * dz 0 := by
      rw [C2'.start.2, ← htie, e1.2]; linarith
    simp only [min_eq_right h0.le] at hc
    rw [htie]; linarith
  obtain ⟨α, β, hα, hβ, hcase⟩ := exists_tie_tilt' O r1 r2 hρ (ca m) (cb n) hB0
  refine isRupert_triShadow_robust O r1 r2 hρ C1.one_le C2.one_le s hs t ht hα hβ ca cz cb dz
    c10.1 c20.1 (by rw [c10.2, c20.2]) C1.inc C2.inc V (fun l hl => hV1 _ _ (C1.mem l hl))
    (fun l hl => hV2 _ _ (C2.mem l hl)) ?_ rfl hsol htie hz1 hz2 hcase
  intro y hy
  obtain ⟨a, b, z, rfl, hc⟩ := hVc y hy
  rcases hc with ⟨rfl, hq⟩ | ⟨rfl, hq⟩ | ⟨ha, hb, hin⟩
  · refine ⟨a, 0, z, rfl, hpos1 a z hq, le_rfl, ?_, fun _ => side1 a z hq, ?_⟩
    · rcases far1 a z hq with h | ⟨e1, e2⟩
      · left; exact far_tiltOK (by linarith)
      · right; left; rw [e1, e2]
    · intro ha; subst ha; rw [hap1 z hq]; exact side2 0 z0 q20
  · refine ⟨0, b, z, rfl, le_rfl, hpos2 b z hq, ?_, ?_, fun _ => side2 b z hq⟩
    · rcases far2 b z hq with h | ⟨e1, e2⟩
      · left; exact far_tiltOK (by linarith)
      · right; right; rw [e1, e2]
    · intro hb; subst hb; rw [hap2 z hq]; exact side1 0 z0 q10
  · refine ⟨a, b, z, rfl, ha.le, hb.le, Or.inl (far_tiltOK ?_), fun h => absurd h hb.ne',
      fun h => absurd h ha.ne'⟩
    rw [e1.1, e2.1]; exact hin m0 ca0 cz0 n0 cb0 dz0 U1 U2

/-- **Lemma T at a vertex from chains, the tie allowed, robust.** As
`isRupert_vertex_frame_tie`, with a third way out at the tie: the apex off the
tie depth (`isRupert_vertex_frame_robust`; `V` a solid). -/
theorem isRupert_vertex_frame_tieR (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (Q1 Q2 : ℝ → ℝ → Prop)
    {z0 : ℝ}
    (hU1 : ∃ m ca cz, ChainOK Q1 z0 1 m ca cz) (hL1 : ∃ m ca cz, ChainOK Q1 z0 (-1) m ca cz)
    (hU2 : ∃ m ca cz, ChainOK Q2 z0 1 m ca cz) (hL2 : ∃ m ca cz, ChainOK Q2 z0 (-1) m ca cz)
    (hap1 : ∀ z, Q1 0 z → z = z0) (hap2 : ∀ z, Q2 0 z → z = z0)
    (hpos1 : ∀ a z, Q1 a z → 0 ≤ a) (hpos2 : ∀ b z, Q2 b z → 0 ≤ b)
    (V : Finset ℝ³)
    (hV1 : ∀ a z, Q1 a z → oblPt O r1 r2 a 0 z ∈ V) (hV2 : ∀ b z, Q2 b z → oblPt O r1 r2 0 b z ∈ V)
    (hVc : ∀ y ∈ V, ∃ a b z, y = oblPt O r1 r2 a b z ∧
      ((b = 0 ∧ Q1 a z) ∨ (a = 0 ∧ Q2 b z) ∨ (0 < a ∧ 0 < b ∧
        ∀ m ca cz n cb dz, ChainOK Q1 z0 1 m ca cz → ChainOK Q2 z0 1 n cb dz →
          a * cb n + b * ca m < ca m * cb n)))
    (hsol : (interior (convexHull ℝ (V : Set ℝ³))).Nonempty)
    (hfarT : ∀ m ca cz n cb dz, ChainOK Q1 z0 1 m ca cz → ChainOK Q2 z0 1 n cb dz →
      cz m ≠ dz n ∨ VTie Q1 Q2 z0 (ca m) (cz m) (cb n) (dz n) ∨
      (cz m = dz n ∧ z0 ≠ cz m)) :
    IsRupert V := by
  obtain ⟨m0, ca0, cz0, U1⟩ := hU1
  obtain ⟨n0, cb0, dz0, U2⟩ := hU2
  rcases hfarT m0 ca0 cz0 n0 cb0 dz0 U1 U2 with h | h | h
  · refine isRupert_vertex_frame_tie O r1 r2 hρ Q1 Q2 ⟨m0, ca0, cz0, U1⟩ hL1 ⟨n0, cb0, dz0, U2⟩ hL2
      hap1 hap2 hpos1 hpos2 V hV1 hV2 hVc fun m ca cz n cb dz C1 C2 => Or.inl ?_
    rw [(C1.far_eq U1).2, (C2.far_eq U2).2]; exact h
  · refine isRupert_vertex_frame_tie O r1 r2 hρ Q1 Q2 ⟨m0, ca0, cz0, U1⟩ hL1 ⟨n0, cb0, dz0, U2⟩ hL2
      hap1 hap2 hpos1 hpos2 V hV1 hV2 hVc fun m ca cz n cb dz C1 C2 => Or.inr ?_
    rw [(C1.far_eq U1).1, (C1.far_eq U1).2, (C2.far_eq U2).1, (C2.far_eq U2).2]; exact h
  · refine isRupert_vertex_frame_robust O r1 r2 hρ Q1 Q2 ⟨m0, ca0, cz0, U1⟩ hL1 ⟨n0, cb0, dz0, U2⟩ hL2
      hap1 hap2 hpos1 hpos2 V hV1 hV2 hVc hsol fun m ca cz n cb dz C1 C2 => ?_
    rw [(C1.far_eq U1).2, (C2.far_eq U2).2]; exact h


/-- The tie condition with the robust way out: `TieH`, or the far ends tied
with the shared vertex off their height (a right angle of the shadow triangle
at a far end is allowed: `isRupert_of_tilted_tie_right`). -/
def TieHR (Q1 Q2 : Finset ℝ³) (v p q : ℝ³) (h : ℝ³ → ℝ) : Prop :=
  TieH Q1 Q2 v p q h ∨ (h p = h q ∧ h v ≠ h p)

/-- **Chains when the far end is the unique point of largest `a`, middles on a vertical
allowed.** As `exists_chainOK` without distinct `a`: `exists_chainOKc` builds the chain on the
top point of each vertical, and `huniq` (the point of largest `a` is unique) turns it into a
`ChainOK`.  The lower points of a vertical lie strictly on the chain's side. -/
theorem exists_chainOK_uniq (S : Finset (ℝ × ℝ)) (z0 : ℝ) (h0 : (0, z0) ∈ S)
    (hpos : ∀ q ∈ S, q ≠ (0, z0) → 0 < q.1) (hne : ∃ q ∈ S, q ≠ (0, z0))
    (hcol : ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → p ≠ r → q ≠ r →
      (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1) ≠ 0)
    (huniq : ∀ q ∈ S, ∀ q' ∈ S, (∀ r ∈ S, r.1 ≤ q.1) → q'.1 = q.1 → q' = q)
    (s : ℝ) (hs : s = 1 ∨ s = -1) :
    ∃ m ca cz, ChainOK (fun a z => (a, z) ∈ S) z0 s m ca cz := by
  obtain ⟨m, ca, cz, C⟩ := exists_chainOKc S z0 h0 hpos hne hcol s hs
  refine ⟨m, ca, cz, C.one_le, C.start, C.inc, C.mem, fun a z hq hn => ?_, C.side⟩
  have hP : (ca m, cz m) ∈ S := C.mem m le_rfl
  have hmax : ∀ r ∈ S, r.1 ≤ ca m := by
    intro r hr
    by_cases e : r.1 = ca m ∧ r.2 = cz m
    · exact e.1.le
    · rcases C.far r.1 r.2 hr e with h | ⟨h, -⟩ <;> exact h.le
  rcases C.far a z hq hn with h | ⟨h, -⟩
  · exact h
  · exfalso
    have := huniq (ca m, cz m) hP (a, z) hq hmax h
    exact hn ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

/-- **Chains over an edge when the far end is the unique point of largest `a`, middles on a
vertical allowed.** As `exists_chainOK_edge`, with the injectivity of `a` off the second apex
point replaced by the uniqueness of the far end (`exists_chainOK_uniq`). -/
theorem exists_chainOK_edge_uniq (S : Finset (ℝ × ℝ)) (zs zo s : ℝ) (hs : s = 1 ∨ s = -1)
    (hso : s * zo < s * zs) (h0 : (0, zs) ∈ S)
    (hpos : ∀ q ∈ S, q ≠ (0, zs) → q ≠ (0, zo) → 0 < q.1) (hne : ∃ q ∈ S, 0 < q.1)
    (hcol : ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → p ≠ r → q ≠ r →
      (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1) ≠ 0)
    (huniq : ∀ q ∈ S.erase (0, zo), ∀ q' ∈ S.erase (0, zo),
      (∀ r ∈ S.erase (0, zo), r.1 ≤ q.1) → q'.1 = q.1 → q' = q) :
    ∃ m ca cz, ChainOK (fun a z => (a, z) ∈ S) zs s m ca cz := by
  classical
  have hzz : zs ≠ zo := fun h => by rw [h] at hso; exact lt_irrefl _ hso
  have hne0 : ((0 : ℝ), zs) ≠ (0, zo) := fun h => hzz (congrArg Prod.snd h)
  obtain ⟨m, ca, cz, C⟩ := exists_chainOK_uniq (S.erase (0, zo)) zs
    (Finset.mem_erase.mpr ⟨hne0, h0⟩)
    (fun q hq hq0 => hpos q (Finset.mem_of_mem_erase hq) hq0 (Finset.ne_of_mem_erase hq))
    (by
      obtain ⟨q, hq, hq0⟩ := hne
      refine ⟨q, Finset.mem_erase.mpr ⟨fun h => ?_, hq⟩, fun h => ?_⟩
      · rw [h] at hq0; exact lt_irrefl _ hq0
      · rw [h] at hq0; exact lt_irrefl _ hq0)
    (fun p hp q hq r hr => hcol p (Finset.mem_of_mem_erase hp) q (Finset.mem_of_mem_erase hq)
      r (Finset.mem_of_mem_erase hr))
    huniq s hs
  refine ⟨m, ca, cz, C.one_le, C.start, C.inc, fun l hl => Finset.mem_of_mem_erase (C.mem l hl),
    fun a z hq hn => ?_, fun a z hq l hl h1' h2' => ?_⟩
  · by_cases e : (a, z) = (0, zo)
    · have := C.far_pos; rw [show a = 0 from congrArg Prod.fst e]; exact this
    · exact C.far a z (Finset.mem_erase.mpr ⟨e, hq⟩) hn
  · by_cases e : (a, z) = (0, zo)
    · have ea : a = 0 := congrArg Prod.fst e
      have ez' : z = zo := congrArg Prod.snd e
      rw [ea, ez']
      have hd := C.inc l hl
      rcases Nat.eq_zero_or_pos l with rfl | hl0
      · rw [C.start.1, C.start.2]
        have : 0 < ca 1 := by have := C.inc 0 (by omega); rw [C.start.1] at this; exact this
        have k : s * ((ca (0 + 1) - 0) * (zo - zs) - (cz (0 + 1) - zs) * (0 - 0)) =
            (ca 1) * (s * zo - s * zs) := by ring
        rw [k]; exact mul_neg_of_pos_of_neg this (by linarith)
      · have hl1 : 0 < ca l := C.pos l hl0 (by omega)
        have hs0 := C.side 0 zs (C.mem 0 (by omega) |> fun h => by
          rw [C.start.1, C.start.2] at h; exact h) l hl
          (fun h => by linarith [h.1]) (fun h => by linarith [h.1, C.pos (l + 1) (by omega) (by omega)])
        have k : s * ((ca (l + 1) - ca l) * (zo - cz l) - (cz (l + 1) - cz l) * (0 - ca l)) =
            s * ((ca (l + 1) - ca l) * (zs - cz l) - (cz (l + 1) - cz l) * (0 - ca l)) +
            (ca (l + 1) - ca l) * (s * zo - s * zs) := by ring
        rw [k]
        have : (ca (l + 1) - ca l) * (s * zo - s * zs) < 0 :=
          mul_neg_of_pos_of_neg (by linarith) (by linarith)
        linarith
    · exact C.side a z (Finset.mem_erase.mpr ⟨e, hq⟩) l hl h1' h2'

theorem inner_obl_angle1 (O r1 r2 : ℝ²) (A B c z0 : ℝ) :
    ⟪oblPt O r1 r2 0 B c - oblPt O r1 r2 A 0 c, oblPt O r1 r2 A 0 c - oblPt O r1 r2 0 0 z0⟫ =
      A * (r1 0 * (B * r2 0 - A * r1 0) + r1 1 * (B * r2 1 - A * r1 1)) := by
  simp [oblPt, PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem inner_obl_angle2 (O r1 r2 : ℝ²) (A B c z0 : ℝ) :
    ⟪oblPt O r1 r2 0 B c - oblPt O r1 r2 A 0 c, oblPt O r1 r2 0 B c - oblPt O r1 r2 0 0 z0⟫ =
      -(B * (r2 0 * (A * r1 0 - B * r2 0) + r2 1 * (A * r1 1 - B * r2 1))) := by
  simp [oblPt, PiLp.inner_apply, Fin.sum_univ_three]; ring

set_option maxHeartbeats 4000000 in
/-- **Lemma T over a vertex at the tie, in frame coordinates.** As
`isRupert_vertex_coords`, with the far depths allowed to tie when a far end or
the shared vertex is a strict top or bottom of its face (`VTie`).  The points of `V` are
`oblPt O r1 r2 (a p) (b p) (p 2)`; `Q1` lies on the ray `b = 0`, `Q2` on `a = 0`,
every other point at `a, b > 0`. -/
theorem isRupert_vertex_coords_tieR (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (V Q1 Q2 : Finset ℝ³)
    (v : ℝ³) (a b : ℝ³ → ℝ) (hy : ∀ p ∈ V, p = oblPt O r1 r2 (a p) (b p) (p 2))
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hint : Q1 ∩ Q2 = {v})
    (hb1 : ∀ p ∈ Q1, b p = 0) (hb1' : ∀ p ∈ V, p ∉ Q1 → 0 < b p)
    (ha2 : ∀ p ∈ Q2, a p = 0) (ha2' : ∀ p ∈ V, p ∉ Q2 → 0 < a p)
    (hne1 : ∃ p ∈ Q1, p ≠ v) (hne2 : ∃ p ∈ Q2, p ≠ v)
    (hcol : ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V, p ≠ q → p ≠ r → q ≠ r → ∀ c : ℝ, r - p ≠ c • (q - p))
    (hmid : ∀ p ∈ V, ∀ q ∈ V, p ≠ q → a p = a q → b p = b q →
      MidPair Q1 Q2 (fun p => ∀ p' ∈ Q1, a p' ≤ a p) (fun q => ∀ q' ∈ Q2, b q' ≤ b q) p q)
    (hfarZ : ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, a p' ≤ a p) → (∀ q' ∈ Q2, b q' ≤ b q) →
      TieHR Q1 Q2 v p q (fun x => x 2))
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ≠ v ∧ xb ≠ v ∧
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → a y / a xa + b y / b xb < 1)
    (hsol : (interior (convexHull ℝ (V : Set ℝ³))).Nonempty) : IsRupert V := by
  classical
  have hv1 : v ∈ Q1 := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).1
  have hv2 : v ∈ Q2 := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).2
  have only : ∀ p ∈ Q1, p ∈ Q2 → p = v := by
    intro p h1 h2
    have : p ∈ Q1 ∩ Q2 := Finset.mem_inter.mpr ⟨h1, h2⟩
    rwa [hint, Finset.mem_singleton] at this
  have hav : a v = 0 := ha2 v hv2
  have hbv : b v = 0 := hb1 v hv1
  have apos : ∀ p ∈ Q1, p ≠ v → 0 < a p := fun p hp hpv =>
    ha2' p (h1V hp) (fun h => hpv (only p hp h))
  have bpos : ∀ p ∈ Q2, p ≠ v → 0 < b p := fun p hp hpv =>
    hb1' p (h2V hp) (fun h => hpv (only p h hp))
  -- the faces in their planes
  set S1 := Q1.image (fun p => (a p, p 2)) with hS1
  set S2 := Q2.image (fun p => (b p, p 2)) with hS2
  have ofS1 : ∀ x z, (x, z) ∈ S1 → ∃ p ∈ Q1, a p = x ∧ p 2 = z := by
    intro x z h; rw [hS1, Finset.mem_image] at h
    obtain ⟨p, hp, e⟩ := h; simp only [Prod.mk.injEq] at e; exact ⟨p, hp, e.1, e.2⟩
  have ofS2 : ∀ x z, (x, z) ∈ S2 → ∃ p ∈ Q2, b p = x ∧ p 2 = z := by
    intro x z h; rw [hS2, Finset.mem_image] at h
    obtain ⟨p, hp, e⟩ := h; simp only [Prod.mk.injEq] at e; exact ⟨p, hp, e.1, e.2⟩
  have pt1 : ∀ p ∈ Q1, p = oblPt O r1 r2 (a p) 0 (p 2) := fun p hp => by
    conv_lhs => rw [hy p (h1V hp), hb1 p hp]
  have pt2 : ∀ p ∈ Q2, p = oblPt O r1 r2 0 (b p) (p 2) := fun p hp => by
    conv_lhs => rw [hy p (h2V hp), ha2 p hp]
  -- chains
  have chains1 : ∀ s : ℝ, (s = 1 ∨ s = -1) → ∃ m ca cz, ChainOK (fun x z => (x, z) ∈ S1) (v 2) s m ca cz := by
    intro s hs
    apply exists_chainOK_uniq S1 (v 2) (by rw [hS1, Finset.mem_image]; exact ⟨v, hv1, by rw [hav]⟩)
    · intro q hq hne
      obtain ⟨p, hp, e1, e2⟩ := ofS1 q.1 q.2 hq
      rw [← e1]; refine apos p hp (fun h => hne ?_)
      exact Prod.ext (by show q.1 = 0; rw [← e1, h, hav]) (by show q.2 = v 2; rw [← e2, h])
    · obtain ⟨p, hp, hpv⟩ := hne1
      refine ⟨(a p, p 2), Finset.mem_image_of_mem _ hp, fun h => ?_⟩
      have := congrArg Prod.fst h; simp only at this; linarith [apos p hp hpv]
    · intro q hq q' hq' q'' hq'' n1 n2 n3
      obtain ⟨p, hp, e1, e2⟩ := ofS1 q.1 q.2 hq
      obtain ⟨p', hp', e1', e2'⟩ := ofS1 q'.1 q'.2 hq'
      obtain ⟨p'', hp'', e1'', e2''⟩ := ofS1 q''.1 q''.2 hq''
      have d : ∀ {r r' : ℝ × ℝ} {u u' : ℝ³}, r ≠ r' → a u = r.1 → u 2 = r.2 → a u' = r'.1 →
          u' 2 = r'.2 → u ≠ u' := by
        intro r r' u u' h h1 h2 h1' h2' hu; apply h
        exact Prod.ext (by rw [← h1, ← h1', hu]) (by rw [← h2, ← h2', hu])
      have hne : (a p, p 2) ≠ (a p', p' 2) := by rw [e1, e2, e1', e2']; exact n1
      have := orient_ne_of_frame1' (O := O) (r1 := r1) (r2 := r2) (zi := p 2) (zj := p' 2) (zk := p'' 2)
        (ak := a p'') hne (by
          intro c; rw [← pt1 p hp, ← pt1 p' hp', ← pt1 p'' hp'']
          exact hcol p (h1V hp) p' (h1V hp') p'' (h1V hp'') (d n1 e1 e2 e1' e2')
            (d n2 e1 e2 e1'' e2'') (d n3 e1' e2' e1'' e2'') c)
      unfold orient2 at this; rwa [e1, e2, e1', e2', e1'', e2''] at this
    · intro q hq q' hq' hmax e
      obtain ⟨p, hp, e1, e2⟩ := ofS1 q.1 q.2 hq
      obtain ⟨p', hp', e1', e2'⟩ := ofS1 q'.1 q'.2 hq'
      have hpmax : ∀ x ∈ Q1, a x ≤ a p := fun x hx => by
        rw [e1]; exact hmax (a x, x 2) (Finset.mem_image_of_mem _ hx)
      by_cases hpp : p' = p
      · exact Prod.ext e (by rw [← e2', ← e2, hpp])
      · exfalso
        rcases hmid p' (h1V hp') p (h1V hp) hpp (by rw [e1', e1]; exact e)
            (by rw [hb1 p' hp', hb1 p hp]) with ⟨-, -, -, nf⟩ | ⟨hp'2, hp2, -, -⟩ | ⟨hp'1, -, -, -⟩
        · exact nf hpmax
        · exact hpp ((only p' hp' hp'2).trans (only p hp hp2).symm)
        · exact absurd hp' hp'1
    · exact hs
  have chains2 : ∀ s : ℝ, (s = 1 ∨ s = -1) → ∃ m ca cz, ChainOK (fun x z => (x, z) ∈ S2) (v 2) s m ca cz := by
    intro s hs
    apply exists_chainOK_uniq S2 (v 2) (by rw [hS2, Finset.mem_image]; exact ⟨v, hv2, by rw [hbv]⟩)
    · intro q hq hne
      obtain ⟨p, hp, e1, e2⟩ := ofS2 q.1 q.2 hq
      rw [← e1]; refine bpos p hp (fun h => hne ?_)
      exact Prod.ext (by show q.1 = 0; rw [← e1, h, hbv]) (by show q.2 = v 2; rw [← e2, h])
    · obtain ⟨p, hp, hpv⟩ := hne2
      refine ⟨(b p, p 2), Finset.mem_image_of_mem _ hp, fun h => ?_⟩
      have := congrArg Prod.fst h; simp only at this; linarith [bpos p hp hpv]
    · intro q hq q' hq' q'' hq'' n1 n2 n3
      obtain ⟨p, hp, e1, e2⟩ := ofS2 q.1 q.2 hq
      obtain ⟨p', hp', e1', e2'⟩ := ofS2 q'.1 q'.2 hq'
      obtain ⟨p'', hp'', e1'', e2''⟩ := ofS2 q''.1 q''.2 hq''
      have d : ∀ {r r' : ℝ × ℝ} {u u' : ℝ³}, r ≠ r' → b u = r.1 → u 2 = r.2 → b u' = r'.1 →
          u' 2 = r'.2 → u ≠ u' := by
        intro r r' u u' h h1 h2 h1' h2' hu; apply h
        exact Prod.ext (by rw [← h1, ← h1', hu]) (by rw [← h2, ← h2', hu])
      have hne : (b p, p 2) ≠ (b p', p' 2) := by rw [e1, e2, e1', e2']; exact n1
      have := orient_ne_of_frame2' (O := O) (r1 := r1) (r2 := r2) (zi := p 2) (zj := p' 2) (zk := p'' 2)
        (bk := b p'') hne (by
          intro c; rw [← pt2 p hp, ← pt2 p' hp', ← pt2 p'' hp'']
          exact hcol p (h2V hp) p' (h2V hp') p'' (h2V hp'') (d n1 e1 e2 e1' e2')
            (d n2 e1 e2 e1'' e2'') (d n3 e1' e2' e1'' e2'') c)
      unfold orient2 at this; rwa [e1, e2, e1', e2', e1'', e2''] at this
    · intro q hq q' hq' hmax e
      obtain ⟨p, hp, e1, e2⟩ := ofS2 q.1 q.2 hq
      obtain ⟨p', hp', e1', e2'⟩ := ofS2 q'.1 q'.2 hq'
      have hpmax : ∀ x ∈ Q2, b x ≤ b p := fun x hx => by
        rw [e1]; exact hmax (b x, x 2) (Finset.mem_image_of_mem _ hx)
      by_cases hpp : p' = p
      · exact Prod.ext e (by rw [← e2', ← e2, hpp])
      · exfalso
        rcases hmid p' (h2V hp') p (h2V hp) hpp (by rw [ha2 p' hp', ha2 p hp])
            (by rw [e1', e1]; exact e) with ⟨hp'1, hp1, -, -⟩ | ⟨-, -, -, nf⟩ | ⟨-, hp'2, -, -⟩
        · exact hpp ((only p' hp'1 hp').trans (only p hp1 hp).symm)
        · exact nf hpmax
        · exact absurd hp' hp'2
    · exact hs
  obtain ⟨xa, hxa, xb, hxb, hxav, hxbv, hin'⟩ := hin
  refine isRupert_vertex_frame_tieR O r1 r2 hρ (fun x z => (x, z) ∈ S1) (fun x z => (x, z) ∈ S2)
    (z0 := v 2) (chains1 1 (Or.inl rfl)) (chains1 (-1) (Or.inr rfl)) (chains2 1 (Or.inl rfl))
    (chains2 (-1) (Or.inr rfl)) ?_ ?_ ?_ ?_ V ?_ ?_ ?_ hsol ?_
  · intro z h
    obtain ⟨p, hp, e1, e2⟩ := ofS1 0 z h
    by_cases hpv : p = v
    · rw [← e2, hpv]
    · linarith [apos p hp hpv]
  · intro z h
    obtain ⟨p, hp, e1, e2⟩ := ofS2 0 z h
    by_cases hpv : p = v
    · rw [← e2, hpv]
    · linarith [bpos p hp hpv]
  · intro x z h
    obtain ⟨p, hp, e1, e2⟩ := ofS1 x z h
    by_cases hpv : p = v
    · rw [← e1, hpv, hav]
    · rw [← e1]; exact (apos p hp hpv).le
  · intro x z h
    obtain ⟨p, hp, e1, e2⟩ := ofS2 x z h
    by_cases hpv : p = v
    · rw [← e1, hpv, hbv]
    · rw [← e1]; exact (bpos p hp hpv).le
  · intro x z h
    obtain ⟨p, hp, e1, e2⟩ := ofS1 x z h
    rw [← e1, ← e2, ← pt1 p hp]; exact h1V hp
  · intro x z h
    obtain ⟨p, hp, e1, e2⟩ := ofS2 x z h
    rw [← e1, ← e2, ← pt2 p hp]; exact h2V hp
  · intro y hy'
    refine ⟨a y, b y, y 2, hy y hy', ?_⟩
    by_cases h1 : y ∈ Q1
    · exact Or.inl ⟨hb1 y h1, Finset.mem_image_of_mem _ h1⟩
    by_cases h2 : y ∈ Q2
    · exact Or.inr (Or.inl ⟨ha2 y h2, Finset.mem_image_of_mem (fun p => (b p, p 2)) h2⟩)
    refine Or.inr (Or.inr ⟨ha2' y hy' h2, hb1' y hy' h1, ?_⟩)
    intro m ca cz n cb dz C1 C2
    have hA := C1.far_pos
    have hB := C2.far_pos
    have hxa0 := apos xa hxa hxav
    have hxb0 := bpos xb hxb hxbv
    have le1 : a xa ≤ ca m := by
      by_cases e : a xa = ca m ∧ xa 2 = cz m
      · exact e.1.le
      · exact (C1.far _ _ (Finset.mem_image_of_mem _ hxa) e).le
    have le2 : b xb ≤ cb n := by
      by_cases e : b xb = cb n ∧ xb 2 = dz n
      · exact e.1.le
      · exact (C2.far _ _ (Finset.mem_image_of_mem (fun p => (b p, p 2)) hxb) e).le
    have k := hin' y hy' h1 h2
    have ha := ha2' y hy' h2
    have hb := hb1' y hy' h1
    have t1 : a y / ca m ≤ a y / a xa := div_le_div_of_nonneg_left ha.le hxa0 le1
    have t2 : b y / cb n ≤ b y / b xb := div_le_div_of_nonneg_left hb.le hxb0 le2
    have : a y / ca m + b y / cb n < 1 := by linarith
    rw [div_add_div _ _ hA.ne' hB.ne', div_lt_one (mul_pos hA hB)] at this
    linarith
  · intro m ca cz n cb dz C1 C2
    obtain ⟨p, hp, e1, e2⟩ := ofS1 _ _ (C1.mem m le_rfl)
    obtain ⟨q, hq, f1, f2⟩ := ofS2 _ _ (C2.mem n le_rfl)
    have hpq : p ≠ q := by
      intro e; subst e
      have := only p hp hq; subst this
      linarith [C1.far_pos]
    have pmax : ∀ p' ∈ Q1, a p' ≤ a p := fun p' hp' => by
      rw [e1]
      by_cases e : a p' = ca m ∧ p' 2 = cz m
      · exact e.1.le
      · exact (C1.far _ _ (Finset.mem_image_of_mem _ hp') e).le
    have qmax : ∀ q' ∈ Q2, b q' ≤ b q := fun q' hq' => by
      rw [f1]
      by_cases e : b q' = cb n ∧ q' 2 = dz n
      · exact e.1.le
      · exact (C2.far _ _ (Finset.mem_image_of_mem (fun p => (b p, p 2)) hq') e).le
    rcases hfarZ p hp q hq hpq pmax qmax with hT | ⟨hpq2, hvp⟩
    · have old : cz m ≠ dz n ∨ VTie (fun x z => (x, z) ∈ S1) (fun x z => (x, z) ∈ S2) (v 2)
          (ca m) (cz m) (cb n) (dz n) := by
        rcases hT with hne | ⟨s, hs, hv | hv | hv | hv⟩
        · left; rw [← e2, ← f2]; exact hne
        · refine Or.inr ⟨s, hs, Or.inl fun x z hxz hn => ?_⟩
          obtain ⟨p', hp', g1, g2⟩ := ofS1 x z hxz
          rw [← g2, ← e2]
          exact hv p' hp' (fun h => hn ⟨by rw [← g1, h, e1], by rw [← g2, h, e2]⟩)
        · refine Or.inr ⟨s, hs, Or.inr (Or.inl fun x z hxz hn => ?_)⟩
          obtain ⟨q', hq', g1, g2⟩ := ofS2 x z hxz
          rw [← g2, ← f2]
          exact hv q' hq' (fun h => hn ⟨by rw [← g1, h, f1], by rw [← g2, h, f2]⟩)
        · refine Or.inr ⟨s, hs, Or.inr (Or.inr (Or.inl fun x z hxz hn => ?_))⟩
          obtain ⟨p', hp', g1, g2⟩ := ofS1 x z hxz
          rw [← g2]
          exact hv p' hp' (fun h => hn ⟨by rw [← g1, h, hav], by rw [← g2, h]⟩)
        · refine Or.inr ⟨s, hs, Or.inr (Or.inr (Or.inr fun x z hxz hn => ?_))⟩
          obtain ⟨q', hq', g1, g2⟩ := ofS2 x z hxz
          rw [← g2]
          exact hv q' hq' (fun h => hn ⟨by rw [← g1, h, hbv], by rw [← g2, h]⟩)
      rcases old with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · right; right
      simp only at hpq2 hvp
      exact ⟨by rw [← e2, ← f2]; exact hpq2, by rw [← e2]; exact hvp⟩


theorem TieHR.swap {Q1 Q2 : Finset ℝ³} {v p q : ℝ³} {h : ℝ³ → ℝ} (H : TieHR Q1 Q2 v p q h) :
    TieHR Q2 Q1 v q p h := by
  rcases H with H | ⟨e, hv⟩
  · exact Or.inl H.swap
  · exact Or.inr ⟨e.symm, by rw [← e]; exact hv⟩

theorem TieHR.map {Q1 Q2 : Finset ℝ³} {v p q : ℝ³} {h h' : ℝ³ → ℝ} (g : ℝ³ → ℝ³)
    (hg : Function.Injective g) {r : ℝ} (hr : 0 < r) (hh : ∀ x, h' (g x) = h x / r)
    (H : TieHR Q1 Q2 v p q h) [DecidableEq ℝ³] (_hlin : ∀ x y, g (x - y) = g x - g y)
    (_hip : ∀ x y, ⟪g x, g y⟫ = ⟪x, y⟫) :
    TieHR (Q1.image g) (Q2.image g) (g v) (g p) (g q) h' := by
  rcases H with H | ⟨e, hv⟩
  · exact Or.inl (H.map g hg hr hh)
  · refine Or.inr ⟨by rw [hh, hh, e], fun e' => hv ?_⟩
    rw [hh, hh] at e'
    have := congrArg (· * r) e'; simp only [div_mul_cancel₀ _ hr.ne'] at this; exact this

theorem interior_convexHull_image_rot {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ SO3) {V : Finset ℝ³}
    (h : (interior (convexHull ℝ (V : Set ℝ³))).Nonempty) :
    (interior (convexHull ℝ ((V.image R.toEuclideanLin : Finset ℝ³) : Set ℝ³))).Nonempty := by
  classical
  obtain ⟨c, hc⟩ := h
  refine ⟨R.toEuclideanLin c, ?_⟩
  have e : convexHull ℝ ((V.image R.toEuclideanLin : Finset ℝ³) : Set ℝ³) =
      (so3Isometry hR).toHomeomorph '' convexHull ℝ (V : Set ℝ³) := by
    rw [Finset.coe_image, ← LinearMap.image_convexHull]; rfl
  rw [e, ← (so3Isometry hR).toHomeomorph.image_interior]
  exact ⟨c, hc, rfl⟩

/-- The former general position `TriGenTieR`, kept for reference: as `TriGenTie`, with `TieHR`
at the far ends (at a tie of the far ends, the shared vertex off their height suffices), and no
segment at all parallel to the line.  `TriGenTieRN.weaken` gives `TriGenTieR`. -/
def TriGenTieRN (V Q1 Q2 : Finset ℝ³) (v : ℝ³) : Prop :=
  ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ, (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
    (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
    ∀ e : ℝ³, e ≠ 0 → f1 (v + e) = 0 → f2 (v + e) = 0 →
      (∀ p ∈ V, ∀ q ∈ V, p ≠ q → ∀ c : ℝ, q - p ≠ c • e) ∧
      ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, f2 p ≤ f2 p') → (∀ q' ∈ Q2, f1 q ≤ f1 q') →
        TieHR Q1 Q2 v p q (fun x => ⟪x, e⟫)

/-- General position for Lemma T at the line of the planes of two facets, with
the robust tie: as `TriGenTie`, with `TieHR` at the far ends (at a tie of the
far ends, the shared vertex off their height suffices), **and segments parallel to the line
allowed between two middles of one face, or between two hidden vertices** (`MidPair`: a middle
is not a far end of its face; a hidden vertex lies off both faces).  By FEWER-FACES-PROOFS.md
Proposition 23.19 (2), (3) such a pair changes no corner and no chain extreme, so the robust
Lemma T at the tie still holds.  A segment parallel to the line with an endpoint at a far end,
or joining a face vertex to a hidden one, is still excluded.  Codimension 2 for any two faces.  The earlier version, with no parallel
segment at all, is `TriGenTieRN`. -/
def TriGenTieR (V Q1 Q2 : Finset ℝ³) (v : ℝ³) : Prop :=
  ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ, (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
    (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
    ∀ e : ℝ³, e ≠ 0 → f1 (v + e) = 0 → f2 (v + e) = 0 →
      (∀ p ∈ V, ∀ q ∈ V, p ≠ q → ∀ c : ℝ, q - p = c • e →
        MidPair Q1 Q2 (fun p => ∀ p' ∈ Q1, f2 p ≤ f2 p') (fun q => ∀ q' ∈ Q2, f1 q ≤ f1 q')
          p q) ∧
      ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, f2 p ≤ f2 p') → (∀ q' ∈ Q2, f1 q ≤ f1 q') →
        TieHR Q1 Q2 v p q (fun x => ⟪x, e⟫)

/-- No parallel segment at all gives `TriGenTieR`. -/
theorem TriGenTieRN.weaken {V Q1 Q2 : Finset ℝ³} {v : ℝ³} (h : TriGenTieRN V Q1 Q2 v) :
    TriGenTieR V Q1 Q2 v := by
  intro f1 f2 z1 n1 z2 n2 e he e1 e2
  obtain ⟨hpar, hfar⟩ := h f1 f2 z1 n1 z2 n2 e he e1 e2
  exact ⟨fun p hp q hq hpq c hc => absurd hc (hpar p hp q hq hpq c), hfar⟩

theorem TriGenTie.toRN {V Q1 Q2 : Finset ℝ³} {v : ℝ³} (h : TriGenTie V Q1 Q2 v) :
    TriGenTieRN V Q1 Q2 v := by
  intro f1 f2 z1 n1 z2 n2 e he e1 e2
  obtain ⟨hpar, hfar⟩ := h f1 f2 z1 n1 z2 n2 e he e1 e2
  exact ⟨hpar, fun p hp q hq hpq h1 h2 => Or.inl (hfar p hp q hq hpq h1 h2)⟩

theorem TriGenTie.toR {V Q1 Q2 : Finset ℝ³} {v : ℝ³} (h : TriGenTie V Q1 Q2 v) :
    TriGenTieR V Q1 Q2 v :=
  h.toRN.weaken

set_option maxHeartbeats 4000000 in
/-- **Lemma T over a vertex at the tie, the planes vertical.**  `Q1`, `Q2` are facets
(functionals `f1`, `f2`) meeting in `v`, both planes containing the vertical line
through `v`. -/
theorem isRupert_facets_vertex_vertical_tieR (V Q1 Q2 : Finset ℝ³) (v : ℝ³)
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hint : Q1 ∩ Q2 = {v}) (f1 f2 : ℝ³ →ᵃ[ℝ] ℝ)
    (z1 : ∀ p ∈ Q1, f1 p = 0) (n1 : ∀ p ∈ V, p ∉ Q1 → f1 p < 0)
    (z2 : ∀ p ∈ Q2, f2 p = 0) (n2 : ∀ p ∈ V, p ∉ Q2 → f2 p < 0)
    (e1 : f1 (v + ez) = 0) (e2 : f2 (v + ez) = 0)
    (hne1 : ∃ p ∈ Q1, p ≠ v) (hne2 : ∃ p ∈ Q2, p ≠ v)
    (hcol : ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V, p ≠ q → p ≠ r → q ≠ r → ∀ c : ℝ, r - p ≠ c • (q - p))
    (hpar : ∀ p ∈ V, ∀ q ∈ V, p ≠ q → p 0 = q 0 → p 1 = q 1 →
      MidPair Q1 Q2 (fun p => ∀ p' ∈ Q1, f2 p ≤ f2 p') (fun q => ∀ q' ∈ Q2, f1 q ≤ f1 q') p q)
    (hfarZ : ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, f2 p ≤ f2 p') → (∀ q' ∈ Q2, f1 q ≤ f1 q') →
      TieHR Q1 Q2 v p q (fun x => x 2))
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ≠ v ∧ xb ≠ v ∧
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → f2 y / f2 xa + f1 y / f1 xb < 1)
    (hsol : (interior (convexHull ℝ (V : Set ℝ³))).Nonempty) : IsRupert V := by
  classical
  have hv1 : v ∈ Q1 := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).1
  have hv2 : v ∈ Q2 := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).2
  have only : ∀ p ∈ Q1, p ∈ Q2 → p = v := by
    intro p h1 h2
    have : p ∈ Q1 ∩ Q2 := Finset.mem_inter.mpr ⟨h1, h2⟩
    rwa [hint, Finset.mem_singleton] at this
  obtain ⟨p1, hp1, hp1v⟩ := hne1
  obtain ⟨p2, hp2, hp2v⟩ := hne2
  have m21 : f2 p1 < 0 := n2 p1 (h1V hp1) (fun h => hp1v (only p1 hp1 h))
  have m12 : f1 p2 < 0 := n1 p2 (h2V hp2) (fun h => hp2v (only p2 h hp2))
  obtain ⟨K1, α1, β1, γ1, h1⟩ := affine_xyz f1
  obtain ⟨K2, α2, β2, γ2, h2⟩ := affine_xyz f2
  have v1 := z1 v hv1; have v2 := z2 v hv2
  have hγ1 : γ1 = 0 := by
    rw [h1] at e1 v1; simp [ez] at e1; linarith
  have hγ2 : γ2 = 0 := by
    rw [h2] at e2 v2; simp [ez] at e2; linarith
  have g1 : ∀ p, f1 p = α1 * (p 0 - v 0) + β1 * (p 1 - v 1) := by
    intro p; have := v1; rw [h1, hγ1] at this ⊢; linarith
  have g2 : ∀ p, f2 p = α2 * (p 0 - v 0) + β2 * (p 1 - v 1) := by
    intro p; have := v2; rw [h2, hγ2] at this ⊢; linarith
  -- the frame
  set O : ℝ² := !₂[v 0, v 1] with hO
  set r1 : ℝ² := !₂[p1 0 - v 0, p1 1 - v 1] with hr1
  set r2 : ℝ² := !₂[p2 0 - v 0, p2 1 - v 1] with hr2
  have q11 : α1 * (p1 0 - v 0) + β1 * (p1 1 - v 1) = 0 := by rw [← g1]; exact z1 p1 hp1
  have q22 : α2 * (p2 0 - v 0) + β2 * (p2 1 - v 1) = 0 := by rw [← g2]; exact z2 p2 hp2
  have hρ : cross2 r1 r2 ≠ 0 := by
    intro hρ0
    simp only [hr1, hr2, cross2] at hρ0
    simp at hρ0
    have k0 : f1 p2 * (p1 0 - v 0) = 0 := by
      rw [g1]; linear_combination (p2 0 - v 0) * q11 + β1 * hρ0
    have k1 : f1 p2 * (p1 1 - v 1) = 0 := by
      rw [g1]; linear_combination (p2 1 - v 1) * q11 - α1 * hρ0
    have r10 := (mul_eq_zero.mp k0).resolve_left m12.ne
    have r11 := (mul_eq_zero.mp k1).resolve_left m12.ne
    have := g2 p1; rw [r10, r11] at this; linarith
  set ρ := cross2 r1 r2 with hρdef
  set a : ℝ³ → ℝ := fun p => cross2 !₂[p 0 - v 0, p 1 - v 1] r2 / ρ with ha
  set b : ℝ³ → ℝ := fun p => cross2 r1 !₂[p 0 - v 0, p 1 - v 1] / ρ with hb
  have hxy : ∀ p : ℝ³, p 0 - v 0 = a p * r1 0 + b p * r2 0 ∧ p 1 - v 1 = a p * r1 1 + b p * r2 1 := by
    intro p
    obtain ⟨c0, c1⟩ := cramer2 !₂[p 0 - v 0, p 1 - v 1] r1 r2 hρ
    simp at c0 c1; exact ⟨c0, c1⟩
  have hy : ∀ p : ℝ³, p = oblPt O r1 r2 (a p) (b p) (p 2) := by
    intro p; obtain ⟨c0, c1⟩ := hxy p
    ext j; fin_cases j
    · simp only [oblPt, hO]; simp; linarith
    · simp only [oblPt, hO]; simp; linarith
    · simp [oblPt]
  have r10 : r1 0 = p1 0 - v 0 := by simp [hr1]
  have r11 : r1 1 = p1 1 - v 1 := by simp [hr1]
  have r20 : r2 0 = p2 0 - v 0 := by simp [hr2]
  have r21 : r2 1 = p2 1 - v 1 := by simp [hr2]
  have G1 : ∀ p, f1 p = b p * f1 p2 := by
    intro p; rw [g1 p, g1 p2, (hxy p).1, (hxy p).2, r10, r11, r20, r21]
    linear_combination a p * q11
  have G2 : ∀ p, f2 p = a p * f2 p1 := by
    intro p; rw [g2 p, g2 p1, (hxy p).1, (hxy p).2, r10, r11, r20, r21]
    linear_combination b p * q22
  have hb1 : ∀ p ∈ Q1, b p = 0 := fun p hp => by
    have := G1 p; rw [z1 p hp] at this
    exact (mul_eq_zero.mp this.symm).resolve_right m12.ne
  have ha2 : ∀ p ∈ Q2, a p = 0 := fun p hp => by
    have := G2 p; rw [z2 p hp] at this
    exact (mul_eq_zero.mp this.symm).resolve_right m21.ne
  have hb1' : ∀ p ∈ V, p ∉ Q1 → 0 < b p := fun p hp hq => by
    have := n1 p hp hq; rw [G1] at this; nlinarith
  have ha2' : ∀ p ∈ V, p ∉ Q2 → 0 < a p := fun p hp hq => by
    have := n2 p hp hq; rw [G2] at this; nlinarith
  have hmid : ∀ p ∈ V, ∀ q ∈ V, p ≠ q → a p = a q → b p = b q →
      MidPair Q1 Q2 (fun p => ∀ p' ∈ Q1, a p' ≤ a p) (fun q => ∀ q' ∈ Q2, b q' ≤ b q) p q := by
    intro p hp q hq hpq ea eb
    obtain ⟨c0, c1⟩ := hxy p; obtain ⟨d0, d1⟩ := hxy q
    rw [ea, eb] at c0 c1
    refine (hpar p hp q hq hpq (by linarith) (by linarith)).mono (fun x _ hx p' hp' => ?_)
      (fun x _ hx q' hq' => ?_)
    · rw [G2 x, G2 p']; exact mul_le_mul_of_nonpos_right (hx p' hp') m21.le
    · rw [G1 x, G1 q']; exact mul_le_mul_of_nonpos_right (hx q' hq') m12.le
  have hfar' : ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, a p' ≤ a p) → (∀ q' ∈ Q2, b q' ≤ b q) →
      TieHR Q1 Q2 v p q (fun x => x 2) := fun p hp q hq hpq h1 h2 =>
    hfarZ p hp q hq hpq (fun p' hp' => by
        rw [G2 p, G2 p']; exact mul_le_mul_of_nonpos_right (h1 p' hp') m21.le)
      (fun q' hq' => by rw [G1 q, G1 q']; exact mul_le_mul_of_nonpos_right (h2 q' hq') m12.le)
  have hin' : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ≠ v ∧ xb ≠ v ∧
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → a y / a xa + b y / b xb < 1 := by
    obtain ⟨xa, hxa, xb, hxb, hxav, hxbv, h⟩ := hin
    refine ⟨xa, hxa, xb, hxb, hxav, hxbv, fun y hy hy1 hy2 => ?_⟩
    have k := h y hy hy1 hy2
    rw [G1 y, G1 xb, G2 y, G2 xa, mul_div_mul_right _ _ m21.ne, mul_div_mul_right _ _ m12.ne] at k
    exact k
  rcases lt_or_gt_of_ne hρ with hneg | hpos
  · -- negative orientation: exchange the two faces
    have hpos' : 0 < cross2 r2 r1 := by
      have : cross2 r2 r1 = -cross2 r1 r2 := by unfold cross2; ring
      rw [this]; linarith
    have swap : ∀ p q z, oblPt O r2 r1 q p z = oblPt O r1 r2 p q z := by
      intro p q z; ext j; fin_cases j <;> simp [oblPt] <;> ring
    refine isRupert_vertex_coords_tieR O r2 r1 hpos' V Q2 Q1 v b a (fun p _ => by rw [swap]; exact hy p)
      h2V h1V (by rw [Finset.inter_comm]; exact hint) ha2 ha2' hb1 hb1' ⟨p2, hp2, hp2v⟩
      ⟨p1, hp1, hp1v⟩ hcol ?_
      (fun p hp q hq hpq h1 h2 => (hfar' q hq p hp (Ne.symm hpq) h2 h1).swap) ?_ hsol
    · intro p hp q hq hpq ea eb
      exact (hmid p hp q hq hpq eb ea).swap
    · obtain ⟨xa, hxa, xb, hxb, hxav, hxbv, h⟩ := hin'
      exact ⟨xb, hxb, xa, hxa, hxbv, hxav, fun y hy hy2 hy1 => by
        rw [add_comm]; exact h y hy hy1 hy2⟩
  · exact isRupert_vertex_coords_tieR O r1 r2 hpos V Q1 Q2 v a b (fun p _ => hy p) h1V h2V hint
      hb1 hb1' ha2 ha2' ⟨p1, hp1, hp1v⟩ ⟨p2, hp2, hp2v⟩ hcol hmid hfar' hin' hsol

set_option maxHeartbeats 4000000 in
/-- **Lemma T over a vertex at the tie** for two facets `Q1`, `Q2` (functionals `f1`, `f2`)
meeting in `v`, viewed along the line `v + ℝ e` of their planes: no three points
collinear, no segment parallel to `e`, distinct depths along `e` at the far ends
(the point of `Q1` where `f2` is least, that of `Q2` where `f1` is least), and
every point off both facets inside the shadow triangle of `v` and some `xa ∈
Q1`, `xb ∈ Q2`. -/
theorem isRupert_facets_vertex_tieR (V Q1 Q2 : Finset ℝ³) (v : ℝ³)
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hint : Q1 ∩ Q2 = {v}) (f1 f2 : ℝ³ →ᵃ[ℝ] ℝ)
    (z1 : ∀ p ∈ Q1, f1 p = 0) (n1 : ∀ p ∈ V, p ∉ Q1 → f1 p < 0)
    (z2 : ∀ p ∈ Q2, f2 p = 0) (n2 : ∀ p ∈ V, p ∉ Q2 → f2 p < 0)
    (e : ℝ³) (he : e ≠ 0) (e1 : f1 (v + e) = 0) (e2 : f2 (v + e) = 0)
    (hne1 : ∃ p ∈ Q1, p ≠ v) (hne2 : ∃ p ∈ Q2, p ≠ v)
    (hcol : ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V, p ≠ q → p ≠ r → q ≠ r → ∀ c : ℝ, r - p ≠ c • (q - p))
    (hpar : ∀ p ∈ V, ∀ q ∈ V, p ≠ q → ∀ c : ℝ, q - p = c • e →
      MidPair Q1 Q2 (fun p => ∀ p' ∈ Q1, f2 p ≤ f2 p') (fun q => ∀ q' ∈ Q2, f1 q ≤ f1 q') p q)
    (hfarZ : ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, f2 p ≤ f2 p') → (∀ q' ∈ Q2, f1 q ≤ f1 q') →
      TieHR Q1 Q2 v p q (fun x => ⟪x, e⟫))
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ≠ v ∧ xb ≠ v ∧
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → f2 y / f2 xa + f1 y / f1 xb < 1)
    (hsol : (interior (convexHull ℝ (V : Set ℝ³))).Nonempty) : IsRupert V := by
  classical
  obtain ⟨R, hR, r, hr, hRe⟩ := exists_rotation_to_ez_pos e he
  apply isRupert_of_isRupert_image_rotation R hR
  set g := R.toEuclideanLin with hg
  set I := so3Isometry hR with hI
  have hgI : ∀ p, g p = I p := fun p => rfl
  have hginj : Function.Injective g := I.injective
  have hgz : ∀ p, g p 2 = ⟪p, e⟫ / r := fun p => by
    have := inner_toEuclideanLin_SO3 hR p e
    rw [hRe, real_inner_smul_right, inner_ez] at this
    field_simp; linarith
  have hIe : I.symm ez = r⁻¹ • e := by
    apply I.injective
    rw [LinearIsometryEquiv.apply_symm_apply, map_smul, ← hgI, hRe, smul_smul,
      inv_mul_cancel₀ hr.ne', one_smul]
  -- functionals transported by the inverse rotation
  set F1 := f1.comp I.symm.toLinearEquiv.toLinearMap.toAffineMap with hF1
  set F2 := f2.comp I.symm.toLinearEquiv.toLinearMap.toAffineMap with hF2
  have tF1 : ∀ p, F1 (g p) = f1 p := fun p => by simp [hF1, hgI]
  have tF2 : ∀ p, F2 (g p) = f2 p := fun p => by simp [hF2, hgI]
  have tz : ∀ f : ℝ³ →ᵃ[ℝ] ℝ, f v = 0 → f (v + e) = 0 →
      (f.comp I.symm.toLinearEquiv.toLinearMap.toAffineMap) (g v + ez) = 0 := by
    intro f h0 h1
    have : (f.comp I.symm.toLinearEquiv.toLinearMap.toAffineMap) (g v + ez) = f (v + r⁻¹ • e) := by
      simp [hgI, map_add, hIe]
    rw [this]; exact affine_zero_line f h0 h1 _
  have hv1 : v ∈ Q1 := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).1
  have hv2 : v ∈ Q2 := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).2
  have memg : ∀ (S : Finset ℝ³) p, g p ∈ S.image g ↔ p ∈ S := fun S p =>
    ⟨fun h => by obtain ⟨q, hq, e⟩ := Finset.mem_image.mp h; rwa [← hginj e], Finset.mem_image_of_mem g⟩
  have allg : ∀ (S : Finset ℝ³) (P : ℝ³ → Prop), (∀ p ∈ S, P (g p)) → ∀ q ∈ S.image g, P q := by
    intro S P h q hq; obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq; exact h p hp
  refine isRupert_facets_vertex_vertical_tieR (V.image g) (Q1.image g) (Q2.image g) (g v)
    (Finset.image_subset_image h1V) (Finset.image_subset_image h2V)
    (by rw [← Finset.image_inter _ _ hginj, hint, Finset.image_singleton]) F1 F2
    (allg Q1 _ (fun p hp => by rw [tF1]; exact z1 p hp))
    (allg V _ (fun p hp hq => by rw [tF1]; exact n1 p hp (fun h => hq ((memg Q1 p).mpr h))))
    (allg Q2 _ (fun p hp => by rw [tF2]; exact z2 p hp))
    (allg V _ (fun p hp hq => by rw [tF2]; exact n2 p hp (fun h => hq ((memg Q2 p).mpr h))))
    (tz f1 (z1 v hv1) e1) (tz f2 (z2 v hv2) e2) ?_ ?_ ?_ ?_ ?_ ?_ (interior_convexHull_image_rot hR hsol)
  · obtain ⟨p, hp, hpv⟩ := hne1
    exact ⟨g p, Finset.mem_image_of_mem g hp, fun h => hpv (hginj h)⟩
  · obtain ⟨p, hp, hpv⟩ := hne2
    exact ⟨g p, Finset.mem_image_of_mem g hp, fun h => hpv (hginj h)⟩
  · refine allg V _ (fun p hp => allg V _ (fun q hq => allg V _ (fun w hw => ?_)))
    intro hpq hpw hqw c h
    apply hcol p hp q hq w hw (fun e => hpq (by rw [e])) (fun e => hpw (by rw [e]))
      (fun e => hqw (by rw [e])) c
    apply hginj
    simp only [map_sub, map_smul] at h ⊢; exact h
  · refine allg V _ (fun p hp => allg V _ (fun q hq => ?_))
    intro hpq h0 h1
    have hc : q - p = ((g (q - p)) 2 / r) • e := by
      apply hginj
      rw [map_smul, hRe]
      ext k; fin_cases k
      · simp [ez, map_sub]; linarith
      · simp [ez, map_sub]; linarith
      · simp [ez]; field_simp
    refine (hpar p hp q hq (fun e => hpq (by rw [e])) _ hc).map g hginj
      (fun x _ hf p' hp' => ?_) (fun x _ hf q' hq' => ?_)
    · have := hf (g p') (Finset.mem_image_of_mem g hp'); rwa [tF2, tF2] at this
    · have := hf (g q') (Finset.mem_image_of_mem g hq'); rwa [tF1, tF1] at this
  · refine allg Q1 _ (fun p hp => allg Q2 _ (fun q hq => ?_))
    intro hpq h1 h2
    refine (hfarZ p hp q hq (fun e => hpq (by rw [e])) (fun p' hp' => ?_) (fun q' hq' => ?_)).map g
      hginj hr (fun x => hgz x) (fun x y => map_sub g x y) (fun x y => inner_toEuclideanLin_SO3 hR x y)
    · have := h1 (g p') (Finset.mem_image_of_mem g hp'); rwa [tF2, tF2] at this
    · have := h2 (g q') (Finset.mem_image_of_mem g hq'); rwa [tF1, tF1] at this
  · obtain ⟨xa, hxa, xb, hxb, hxav, hxbv, h⟩ := hin
    refine ⟨g xa, Finset.mem_image_of_mem g hxa, g xb, Finset.mem_image_of_mem g hxb,
      fun e => hxav (hginj e), fun e => hxbv (hginj e), allg V _ (fun y hy hy1 hy2 => ?_)⟩
    rw [tF1, tF1, tF2, tF2]
    exact h y hy (fun h => hy1 ((memg Q1 y).mpr h)) (fun h => hy2 ((memg Q2 y).mpr h))

set_option maxHeartbeats 4000000 in
/-- **Lemma T over a vertex at the tie, facet form** (`FEWER-FACES-PROOFS.md` §7): two facets
`Q1`, `Q2` of `V` (no three points collinear) meeting in the single vertex `v`,
with `TriGenFar` at the line of their planes, and every point off both facets
inside the shadow triangle of `v`, `xa ∈ Q1`, `xb ∈ Q2` (stated with any facet
functionals `f1`, `f2`): Rupert. -/
theorem isRupert_of_facets_vertex_tieR (V : Finset ℝ³) (hgen : NoThreeCollinear V)
    (Q1 Q2 : Finset ℝ³) (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (h1f : IsFacet V Q1) (h2f : IsFacet V Q2)
    (v : ℝ³) (hint : Q1 ∩ Q2 = {v}) (hne1 : ∃ p ∈ Q1, p ≠ v) (hne2 : ∃ p ∈ Q2, p ≠ v)
    (hT : TriGenTieR V Q1 Q2 v)
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ≠ v ∧ xb ≠ v ∧ ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ,
      (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
      (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → f2 y / f2 xa + f1 y / f1 xb < 1)
    (hsol : (interior (convexHull ℝ (V : Set ℝ³))).Nonempty) : IsRupert V := by
  classical
  have hv1 : v ∈ Q1 := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).1
  have hv2 : v ∈ Q2 := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).2
  have only : ∀ p ∈ Q1, p ∈ Q2 → p = v := by
    intro p h1 h2
    have : p ∈ Q1 ∩ Q2 := Finset.mem_inter.mpr ⟨h1, h2⟩
    rwa [hint, Finset.mem_singleton] at this
  obtain ⟨p1, hp1, hp1v⟩ := hne1
  obtain ⟨p2, hp2, hp2v⟩ := hne2
  obtain ⟨f1, z1, n1⟩ := h1f
  obtain ⟨f2, z2, n2⟩ := h2f
  obtain ⟨K1, α1, β1, γ1, hf1⟩ := affine_xyz f1
  obtain ⟨K2, α2, β2, γ2, hf2⟩ := affine_xyz f2
  set e : ℝ³ := !₂[β1 * γ2 - γ1 * β2, γ1 * α2 - α1 * γ2, α1 * β2 - β1 * α2] with he
  have dif : ∀ (f : ℝ³ →ᵃ[ℝ] ℝ) (K α β γ : ℝ), (∀ p, f p = K + α * p 0 + β * p 1 + γ * p 2) →
      ∀ p q, f q - f p = α * (q 0 - p 0) + β * (q 1 - p 1) + γ * (q 2 - p 2) := by
    intro f K α β γ h p q; rw [h, h]; ring
  have e1 : f1 (v + e) = 0 := by
    have := dif f1 K1 α1 β1 γ1 hf1 v (v + e)
    rw [z1 v hv1] at this; rw [sub_zero] at this; rw [this]; simp [he]; ring
  have e2 : f2 (v + e) = 0 := by
    have := dif f2 K2 α2 β2 γ2 hf2 v (v + e)
    rw [z2 v hv2] at this; rw [sub_zero] at this; rw [this]; simp [he]; ring
  have hn1 : f1 p2 < 0 := n1 p2 (h2V hp2) (fun h => hp2v (only p2 h hp2))
  have hn2 : f2 p1 < 0 := n2 p1 (h1V hp1) (fun h => hp1v (only p1 hp1 h))
  have hne : e ≠ 0 := by
    intro h0
    have c0 := congrArg (fun p : ℝ³ => p 0) h0
    have c1 := congrArg (fun p : ℝ³ => p 1) h0
    have c2 := congrArg (fun p : ℝ³ => p 2) h0
    simp [he] at c0 c1 c2
    have d14 := dif f1 K1 α1 β1 γ1 hf1 v p2
    have d21 := dif f2 K2 α2 β2 γ2 hf2 v p1
    have d11 := dif f1 K1 α1 β1 γ1 hf1 v p1
    rw [z1 v hv1, sub_zero] at d14
    rw [z1 v hv1, z1 p1 hp1, sub_zero] at d11
    rw [z2 v hv2, sub_zero] at d21
    have key : (f1 p2) * (f2 p1) = 0 := by
      rw [d14, d21]
      have := d11
      linear_combination (α2 * (p2 0 - v 0) + β2 * (p2 1 - v 1) + γ2 * (p2 2 - v 2)) * this.symm +
        ((p1 1 - v 1) * (p2 0 - v 0) - (p1 0 - v 0) * (p2 1 - v 1)) * c2 +
        ((p1 2 - v 2) * (p2 1 - v 1) - (p1 1 - v 1) * (p2 2 - v 2)) * c0 +
        ((p1 0 - v 0) * (p2 2 - v 2) - (p1 2 - v 2) * (p2 0 - v 0)) * c1
    nlinarith
  obtain ⟨hpar, hfarZ⟩ := hT f1 f2 z1 n1 z2 n2 e hne e1 e2
  obtain ⟨xa, hxa, xb, hxb, hxav, hxbv, hin'⟩ := hin
  refine isRupert_facets_vertex_tieR V Q1 Q2 v h1V h2V hint f1 f2 z1 n1 z2 n2 e hne e1 e2
    ⟨p1, hp1, hp1v⟩ ⟨p2, hp2, hp2v⟩ ?_ hpar hfarZ
    ⟨xa, hxa, xb, hxb, hxav, hxbv, hin' f1 f2 z1 n1 z2 n2⟩ hsol
  exact hgen


set_option maxHeartbeats 4000000 in
/-- The robust tie over an edge, same-sign sector: both chains start at the apex
vertex `z1s` (strictly beyond the tied far depth in `s z`), the other apex
vertex `z2s` hidden (`isRupert_triShadow_robust`). -/
theorem edge_robust_core (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (Q1 Q2 : ℝ → ℝ → Prop)
    (s : ℝ) (hs : s = 1 ∨ s = -1) {z1s z2s : ℝ} (hap : s * z2s < s * z1s)
    {m n : ℕ} {ca cz cb dz : ℕ → ℝ}
    (C1 : ChainOK Q1 z1s s m ca cz) (C2 : ChainOK Q2 z1s s n cb dz)
    (htie : cz m = dz n) (hz : 0 < s * (z1s - cz m))
    (hap1 : ∀ z, Q1 0 z → z = z1s ∨ z = z2s) (hap2 : ∀ z, Q2 0 z → z = z1s ∨ z = z2s)
    (hQ1z2 : Q1 0 z2s) (hQ2z2 : Q2 0 z2s)
    (hpos1 : ∀ a z, Q1 a z → 0 ≤ a) (hpos2 : ∀ b z, Q2 b z → 0 ≤ b)
    (V : Finset ℝ³)
    (hV1 : ∀ a z, Q1 a z → oblPt O r1 r2 a 0 z ∈ V) (hV2 : ∀ b z, Q2 b z → oblPt O r1 r2 0 b z ∈ V)
    (hVc : ∀ y ∈ V, ∃ a b z, y = oblPt O r1 r2 a b z ∧
      ((b = 0 ∧ Q1 a z) ∨ (a = 0 ∧ Q2 b z) ∨ (0 < a ∧ 0 < b ∧ a * cb n + b * ca m < ca m * cb n)))
    (hsol : (interior (convexHull ℝ (V : Set ℝ³))).Nonempty) :
    IsRupert V := by
  have hA0 := C1.far_pos
  have hB0 := C2.far_pos
  have c10 := C1.start; have c20 := C2.start
  have hns : -s = 1 ∨ -s = -1 := by rcases hs with rfl | rfl <;> norm_num
  have far1 : ∀ a z, Q1 a z → a * cb n < ca m * cb n ∨ (a = ca m ∧ z = cz m) := by
    intro a z hq
    by_cases h : a = ca m ∧ z = cz m
    · exact Or.inr h
    · left; exact mul_lt_mul_of_pos_right (C1.far a z hq h) hB0
  have far2 : ∀ b z, Q2 b z → b * ca m < cb n * ca m ∨ (b = cb n ∧ z = dz n) := by
    intro b z hq
    by_cases h : b = cb n ∧ z = dz n
    · exact Or.inr h
    · left; exact mul_lt_mul_of_pos_right (C2.far b z hq h) hA0
  have side1 : ∀ a z, Q1 a z → ∀ l, l < m → oblPt O r1 r2 a 0 z ≠ oblPt O r1 r2 (ca l) 0 (cz l) →
      oblPt O r1 r2 a 0 z ≠ oblPt O r1 r2 (ca (l + 1)) 0 (cz (l + 1)) →
      s * ((ca (l + 1) - ca l) * (z - cz l) - (cz (l + 1) - cz l) * (a - ca l)) < 0 := by
    intro a z hq l hl h1 h2
    exact C1.side a z hq l hl (fun ⟨e1, e2⟩ => h1 (by rw [e1, e2]))
      (fun ⟨e1, e2⟩ => h2 (by rw [e1, e2]))
  have side2 : ∀ b z, Q2 b z → ∀ l, l < n →
      oblPt O r1 r2 0 b z ≠ oblPt O r1 r2 0 (cb (l + 1)) (dz (l + 1)) →
      oblPt O r1 r2 0 b z ≠ oblPt O r1 r2 0 (cb l) (dz l) →
      -s * ((cb l - cb (l + 1)) * (z - dz (l + 1)) - (dz l - dz (l + 1)) * (b - cb (l + 1))) < 0 := by
    intro b z hq l hl h1 h2
    have := C2.side b z hq l hl (fun ⟨e1, e2⟩ => h2 (by rw [e1, e2]))
      (fun ⟨e1, e2⟩ => h1 (by rw [e1, e2]))
    have e : -s * ((cb l - cb (l + 1)) * (z - dz (l + 1)) - (dz l - dz (l + 1)) * (b - cb (l + 1))) =
      s * ((cb (l + 1) - cb l) * (z - dz l) - (dz (l + 1) - dz l) * (b - cb l)) := by ring
    rw [e]; exact this
  have q10 : Q1 0 z1s := by rw [← c10.2, ← c10.1]; exact C1.mem 0 (Nat.zero_le _)
  have q20 : Q2 0 z1s := by rw [← c20.2, ← c20.1]; exact C2.mem 0 (Nat.zero_le _)
  have q2of : ∀ z, Q1 0 z → Q2 0 z := by
    intro z h; rcases hap1 z h with rfl | rfl
    · exact q20
    · exact hQ2z2
  have q1of : ∀ z, Q2 0 z → Q1 0 z := by
    intro z h; rcases hap2 z h with rfl | rfl
    · exact q10
    · exact hQ1z2
  have hz1 : ∀ l, l < m → 0 < s * (cz l - cz m) := by
    intro l hl
    rcases Nat.eq_zero_or_pos l with rfl | hl0
    · rw [c10.2]; exact hz
    · have hc := gt_min_ends_of_conc (f := fun l => s * cz l) (m := m) C1.conc l hl0 hl
      have h0 : s * cz m < s * cz 0 := by rw [c10.2]; linarith
      simp only [min_eq_right h0.le] at hc
      linarith
  have hz2 : ∀ k, 0 < k → k < n → 0 < s * (dz k - cz m) := by
    intro k hk0 hk
    have hc := gt_min_ends_of_conc (f := fun l => s * dz l) (m := n) C2.conc k hk0 hk
    have h0 : s * dz n < s * dz 0 := by rw [c20.2, ← htie]; linarith
    simp only [min_eq_right h0.le] at hc
    rw [htie]; linarith
  obtain ⟨α, β, hα, hβ, hcase⟩ := exists_tie_tilt' O r1 r2 hρ (ca m) (cb n) C2.far_pos
  refine isRupert_triShadow_robust O r1 r2 hρ C1.one_le C2.one_le s hs (-s) hns hα hβ ca cz
    cb dz c10.1 c20.1 (by rw [c10.2, c20.2]) C1.inc C2.inc V (fun l hl => hV1 _ _ (C1.mem l hl))
    (fun l hl => hV2 _ _ (C2.mem l hl)) ?_ rfl hsol htie hz1 hz2 hcase
  intro y hy
  obtain ⟨a, b, z, rfl, hc⟩ := hVc y hy
  rcases hc with ⟨rfl, hq⟩ | ⟨rfl, hq⟩ | ⟨ha, hb, hin⟩
  · refine ⟨a, 0, z, rfl, hpos1 a z hq, le_rfl, ?_, fun _ => side1 a z hq, ?_⟩
    · rcases far1 a z hq with h | ⟨e1, e2⟩
      · left; exact far_tiltOK (by linarith)
      · right; left; rw [e1, e2]
    · intro ha; subst ha; exact side2 0 z (q2of z hq)
  · refine ⟨0, b, z, rfl, le_rfl, hpos2 b z hq, ?_, ?_, fun _ => side2 b z hq⟩
    · rcases far2 b z hq with h | ⟨e1, e2⟩
      · left; exact far_tiltOK (by linarith)
      · right; right; rw [e1, e2]
    · intro hb; subst hb; exact side1 0 z (q1of z hq)
  · exact ⟨a, b, z, rfl, ha.le, hb.le, Or.inl (far_tiltOK hin), fun h => absurd h hb.ne',
      fun h => absurd h ha.ne'⟩

set_option maxHeartbeats 4000000 in
/-- **Lemma T at the tie over an edge, robust form, from chains.** The setting of
`isRupert_edge_frame_tie` with the far depths tied: the apex vertex strictly
beyond the tied depth (one of the two always is) starts both chains (`edge_robust_core`); `V` a solid. -/
theorem isRupert_edge_frame_robust (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (Q1 Q2 : ℝ → ℝ → Prop)
    {zx zx' : ℝ} (hxx : zx < zx')
    (hU1 : ∃ m ca cz, ChainOK Q1 zx' 1 m ca cz) (hL1 : ∃ m ca cz, ChainOK Q1 zx (-1) m ca cz)
    (hU2 : ∃ m ca cz, ChainOK Q2 zx' 1 m ca cz) (hL2 : ∃ m ca cz, ChainOK Q2 zx (-1) m ca cz)
    (hap1 : ∀ z, Q1 0 z → z = zx ∨ z = zx') (hap2 : ∀ z, Q2 0 z → z = zx ∨ z = zx')
    (hQ1x : Q1 0 zx) (hQ1x' : Q1 0 zx') (hQ2x : Q2 0 zx) (hQ2x' : Q2 0 zx')
    (hpos1 : ∀ a z, Q1 a z → 0 ≤ a) (hpos2 : ∀ b z, Q2 b z → 0 ≤ b)
    (V : Finset ℝ³)
    (hV1 : ∀ a z, Q1 a z → oblPt O r1 r2 a 0 z ∈ V) (hV2 : ∀ b z, Q2 b z → oblPt O r1 r2 0 b z ∈ V)
    (hVc : ∀ y ∈ V, ∃ a b z, y = oblPt O r1 r2 a b z ∧
      ((b = 0 ∧ Q1 a z) ∨ (a = 0 ∧ Q2 b z) ∨ (0 < a ∧ 0 < b ∧
        ∀ m ca cz n cb dz, ChainOK Q1 zx' 1 m ca cz → ChainOK Q2 zx' 1 n cb dz →
          a * cb n + b * ca m < ca m * cb n)))
    (hsol : (interior (convexHull ℝ (V : Set ℝ³))).Nonempty)
    (hrob : ∀ m ca cz n cb dz, ChainOK Q1 zx' 1 m ca cz → ChainOK Q2 zx' 1 n cb dz →
      cz m = dz n) :
    IsRupert V := by
  obtain ⟨m0, ca0, cz0, U1⟩ := hU1
  obtain ⟨n0, cb0, dz0, U2⟩ := hU2
  obtain ⟨m1, ca1, cz1, L1⟩ := hL1
  obtain ⟨n1, cb1, dz1, L2⟩ := hL2
  have conv : ∀ {m n : ℕ} {ca cb : ℕ → ℝ}, ca m = ca0 m0 → cb n = cb0 n0 →
      ∀ y ∈ V, ∃ a b z, y = oblPt O r1 r2 a b z ∧
        ((b = 0 ∧ Q1 a z) ∨ (a = 0 ∧ Q2 b z) ∨ (0 < a ∧ 0 < b ∧ a * cb n + b * ca m < ca m * cb n)) := by
    intro m n ca cb e1 e2 y hy
    obtain ⟨a, b, z, e, hc⟩ := hVc y hy
    refine ⟨a, b, z, e, ?_⟩
    rcases hc with h | h | ⟨ha, hb, hin⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · right; right; refine ⟨ha, hb, ?_⟩
      rw [e1, e2]; exact hin m0 ca0 cz0 n0 cb0 dz0 U1 U2
  have htie := hrob m0 ca0 cz0 n0 cb0 dz0 U1 U2
  have eU1 := L1.far_eq U1
  have eU2 := L2.far_eq U2
  have eU1' := U1.far_eq U1
  have eU2' := U2.far_eq U2
  rcases lt_or_ge (cz0 m0) zx' with hc | hc
  · exact edge_robust_core O r1 r2 hρ Q1 Q2 1 (Or.inl rfl) (z1s := zx') (z2s := zx) (by linarith)
      U1 U2 htie (by linarith) (fun z h => (hap1 z h).symm) (fun z h => (hap2 z h).symm)
      hQ1x hQ2x hpos1 hpos2 V hV1 hV2 (conv eU1'.1 eU2'.1) hsol
  · refine edge_robust_core O r1 r2 hρ Q1 Q2 (-1) (Or.inr rfl) (z1s := zx) (z2s := zx') (by linarith)
      L1 L2 (by rw [eU1.2, eU2.2]; exact htie) (by rw [eU1.2]; linarith) hap1 hap2 hQ1x' hQ2x' hpos1 hpos2 V hV1 hV2
      (conv eU1.1 eU2.1) hsol

/-- **Lemma T over an edge from chains, the tie allowed, robust.** -/
theorem isRupert_edge_frame_tieR (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (Q1 Q2 : ℝ → ℝ → Prop)
    {zx zx' : ℝ} (hxx : zx < zx')
    (hU1 : ∃ m ca cz, ChainOK Q1 zx' 1 m ca cz) (hL1 : ∃ m ca cz, ChainOK Q1 zx (-1) m ca cz)
    (hU2 : ∃ m ca cz, ChainOK Q2 zx' 1 m ca cz) (hL2 : ∃ m ca cz, ChainOK Q2 zx (-1) m ca cz)
    (hap1 : ∀ z, Q1 0 z → z = zx ∨ z = zx') (hap2 : ∀ z, Q2 0 z → z = zx ∨ z = zx')
    (hQ1x : Q1 0 zx) (hQ1x' : Q1 0 zx') (hQ2x : Q2 0 zx) (hQ2x' : Q2 0 zx')
    (hpos1 : ∀ a z, Q1 a z → 0 ≤ a) (hpos2 : ∀ b z, Q2 b z → 0 ≤ b)
    (V : Finset ℝ³)
    (hV1 : ∀ a z, Q1 a z → oblPt O r1 r2 a 0 z ∈ V) (hV2 : ∀ b z, Q2 b z → oblPt O r1 r2 0 b z ∈ V)
    (hVc : ∀ y ∈ V, ∃ a b z, y = oblPt O r1 r2 a b z ∧
      ((b = 0 ∧ Q1 a z) ∨ (a = 0 ∧ Q2 b z) ∨ (0 < a ∧ 0 < b ∧
        ∀ m ca cz n cb dz, ChainOK Q1 zx' 1 m ca cz → ChainOK Q2 zx' 1 n cb dz →
          a * cb n + b * ca m < ca m * cb n)))
    (hsol : (interior (convexHull ℝ (V : Set ℝ³))).Nonempty)
    (hfarT : ∀ m ca cz n cb dz, ChainOK Q1 zx' 1 m ca cz → ChainOK Q2 zx' 1 n cb dz →
      cz m ≠ dz n ∨ ETie Q1 Q2 zx zx' (ca m) (cz m) (cb n) (dz n) ∨
      cz m = dz n) :
    IsRupert V := by
  obtain ⟨m0, ca0, cz0, U1⟩ := hU1
  obtain ⟨n0, cb0, dz0, U2⟩ := hU2
  rcases hfarT m0 ca0 cz0 n0 cb0 dz0 U1 U2 with h | h | h
  · refine isRupert_edge_frame_tie O r1 r2 hρ Q1 Q2 hxx ⟨m0, ca0, cz0, U1⟩ hL1 ⟨n0, cb0, dz0, U2⟩ hL2
      hap1 hap2 hQ1x hQ1x' hQ2x hQ2x' hpos1 hpos2 V hV1 hV2 hVc fun m ca cz n cb dz C1 C2 => Or.inl ?_
    rw [(C1.far_eq U1).2, (C2.far_eq U2).2]; exact h
  · refine isRupert_edge_frame_tie O r1 r2 hρ Q1 Q2 hxx ⟨m0, ca0, cz0, U1⟩ hL1 ⟨n0, cb0, dz0, U2⟩ hL2
      hap1 hap2 hQ1x hQ1x' hQ2x hQ2x' hpos1 hpos2 V hV1 hV2 hVc fun m ca cz n cb dz C1 C2 => Or.inr ?_
    rw [(C1.far_eq U1).1, (C1.far_eq U1).2, (C2.far_eq U2).1, (C2.far_eq U2).2]; exact h
  · refine isRupert_edge_frame_robust O r1 r2 hρ Q1 Q2 hxx ⟨m0, ca0, cz0, U1⟩ hL1 ⟨n0, cb0, dz0, U2⟩ hL2
      hap1 hap2 hQ1x hQ1x' hQ2x hQ2x' hpos1 hpos2 V hV1 hV2 hVc hsol fun m ca cz n cb dz C1 C2 => ?_
    rw [(C1.far_eq U1).2, (C2.far_eq U2).2]; exact h


/-- The edge tie condition with the robust way out: `TieHE`, or the far ends
tied (a right angle at a far end is allowed: `isRupert_of_tilted_tie_right`). -/
def TieHER (Q1 Q2 : Finset ℝ³) (v w p q : ℝ³) (h : ℝ³ → ℝ) : Prop :=
  TieHE Q1 Q2 v w p q h ∨ h p = h q

theorem TieHER.swap {Q1 Q2 : Finset ℝ³} {v w p q : ℝ³} {h : ℝ³ → ℝ} (H : TieHER Q1 Q2 v w p q h) :
    TieHER Q2 Q1 v w q p h := by
  rcases H with H | e
  · exact Or.inl H.swap
  · exact Or.inr e.symm

theorem TieHER.comm {Q1 Q2 : Finset ℝ³} {v w p q : ℝ³} {h : ℝ³ → ℝ} (H : TieHER Q1 Q2 v w p q h) :
    TieHER Q1 Q2 w v p q h := by
  rcases H with H | e
  · exact Or.inl H.comm
  · exact Or.inr e

theorem TieHER.map {Q1 Q2 : Finset ℝ³} {v w p q : ℝ³} {h h' : ℝ³ → ℝ} (g : ℝ³ → ℝ³)
    {r : ℝ} (hr : 0 < r) (hh : ∀ x, h' (g x) = h x / r)
    (H : TieHER Q1 Q2 v w p q h) [DecidableEq ℝ³] (_hlin : ∀ x y, g (x - y) = g x - g y)
    (_hip : ∀ x y, ⟪g x, g y⟫ = ⟪x, y⟫) :
    TieHER (Q1.image g) (Q2.image g) (g v) (g w) (g p) (g q) h' := by
  rcases H with H | e
  · exact Or.inl (H.map g hr hh)
  · exact Or.inr (by rw [hh, hh, e])

/-- The former general position `EdgeTieR`, kept for reference: as `EdgeTie`, with `TieHER` at the
far ends (a tie of the far ends suffices), and no other segment at all parallel to the edge.
`EdgeTieRN.weaken` gives `EdgeTieR`. -/
def EdgeTieRN (V Q1 Q2 : Finset ℝ³) (v w : ℝ³) : Prop :=
  (∀ p ∈ V, ∀ q ∈ V, p ≠ q → ({p, q} : Finset ℝ³) ≠ {v, w} → ∀ c : ℝ, q - p ≠ c • (w - v)) ∧
  ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ, (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
    (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
    ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, f2 p ≤ f2 p') → (∀ q' ∈ Q2, f1 q ≤ f1 q') →
      TieHER Q1 Q2 v w p q (fun x => ⟪x, w - v⟫)

/-- General position for Lemma T along an edge with the robust tie: as
`EdgeTie`, with `TieHER` at the far ends (a tie of the far ends suffices), **and segments
parallel to the edge allowed between two middles of one face, or between two hidden vertices**
(`MidPair`: a middle is not a far end of its face; a hidden vertex lies off both faces; the
edge itself is not counted).  By FEWER-FACES-PROOFS.md Proposition 23.19 (2), (3) such a pair
changes no corner and no chain extreme, so the robust Lemma T at the tie still holds.  A
segment parallel to the edge with an endpoint at a far end, or joining a face vertex to a
hidden one, is still excluded.  Codimension 2 for any two faces.  The earlier version, with no other
parallel segment at all, is `EdgeTieRN`. -/
def EdgeTieR (V Q1 Q2 : Finset ℝ³) (v w : ℝ³) : Prop :=
  ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ, (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
    (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
    (∀ p ∈ V, ∀ q ∈ V, p ≠ q → ({p, q} : Finset ℝ³) ≠ {v, w} → ∀ c : ℝ, q - p = c • (w - v) →
      MidPair Q1 Q2 (fun p => ∀ p' ∈ Q1, f2 p ≤ f2 p') (fun q => ∀ q' ∈ Q2, f1 q ≤ f1 q') p q) ∧
    ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, f2 p ≤ f2 p') → (∀ q' ∈ Q2, f1 q ≤ f1 q') →
      TieHER Q1 Q2 v w p q (fun x => ⟪x, w - v⟫)

/-- No other parallel segment at all gives `EdgeTieR`. -/
theorem EdgeTieRN.weaken {V Q1 Q2 : Finset ℝ³} {v w : ℝ³} (h : EdgeTieRN V Q1 Q2 v w) :
    EdgeTieR V Q1 Q2 v w :=
  fun f1 f2 z1 n1 z2 n2 =>
    ⟨fun p hp q hq hpq hne c hc => absurd hc (h.1 p hp q hq hpq hne c), h.2 f1 f2 z1 n1 z2 n2⟩

theorem EdgeTie.toRN {V Q1 Q2 : Finset ℝ³} {v w : ℝ³} (h : EdgeTie V Q1 Q2 v w) :
    EdgeTieRN V Q1 Q2 v w :=
  ⟨h.1, fun f1 f2 z1 n1 z2 n2 p hp q hq hpq h1 h2 => Or.inl (h.2 f1 f2 z1 n1 z2 n2 p hp q hq hpq h1 h2)⟩

theorem EdgeTie.toR {V Q1 Q2 : Finset ℝ³} {v w : ℝ³} (h : EdgeTie V Q1 Q2 v w) :
    EdgeTieR V Q1 Q2 v w :=
  h.toRN.weaken

set_option maxHeartbeats 4000000 in
/-- **Lemma T over an edge, in frame coordinates.**  The points of `V` are
`oblPt O r1 r2 (a p) (b p) (p 2)`; `Q1` lies on the ray `b = 0`, `Q2` on `a = 0`,
they share the vertical edge `v w`, every other point at `a, b > 0`. -/
theorem isRupert_edge_coords_tieR (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (V Q1 Q2 : Finset ℝ³)
    (v w : ℝ³) (hvw : v 2 < w 2) (a b : ℝ³ → ℝ)
    (hy : ∀ p ∈ V, p = oblPt O r1 r2 (a p) (b p) (p 2))
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hint : Q1 ∩ Q2 = {v, w})
    (hb1 : ∀ p ∈ Q1, b p = 0) (hb1' : ∀ p ∈ V, p ∉ Q1 → 0 < b p)
    (ha2 : ∀ p ∈ Q2, a p = 0) (ha2' : ∀ p ∈ V, p ∉ Q2 → 0 < a p)
    (hne1 : ∃ p ∈ Q1, p ∉ Q2) (hne2 : ∃ p ∈ Q2, p ∉ Q1)
    (hcol : ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V, p ≠ q → p ≠ r → q ≠ r → ∀ c : ℝ, r - p ≠ c • (q - p))
    (hmid : ∀ p ∈ V, ∀ q ∈ V, p ≠ q → ({p, q} : Finset ℝ³) ≠ {v, w} → a p = a q → b p = b q →
      MidPair Q1 Q2 (fun p => ∀ p' ∈ Q1, a p' ≤ a p) (fun q => ∀ q' ∈ Q2, b q' ≤ b q) p q)
    (hfarZ : ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, a p' ≤ a p) → (∀ q' ∈ Q2, b q' ≤ b q) →
      TieHER Q1 Q2 v w p q (fun x => x 2))
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ∉ Q2 ∧ xb ∉ Q1 ∧
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → a y / a xa + b y / b xb < 1)
    (hsol : (interior (convexHull ℝ (V : Set ℝ³))).Nonempty) : IsRupert V := by
  classical
  have mem12 : ∀ p, p ∈ Q1 → p ∈ Q2 → p = v ∨ p = w := by
    intro p h1 h2
    have : p ∈ Q1 ∩ Q2 := Finset.mem_inter.mpr ⟨h1, h2⟩
    rw [hint] at this; simpa using this
  have hvi : v ∈ Q1 ∩ Q2 := by rw [hint]; simp
  have hwi : w ∈ Q1 ∩ Q2 := by rw [hint]; simp
  have hv1 := (Finset.mem_inter.mp hvi).1; have hv2 := (Finset.mem_inter.mp hvi).2
  have hw1 := (Finset.mem_inter.mp hwi).1; have hw2 := (Finset.mem_inter.mp hwi).2
  have hav := ha2 v hv2; have haw := ha2 w hw2
  have hbv := hb1 v hv1; have hbw := hb1 w hw1
  have hvw' : v ≠ w := fun e => by rw [e] at hvw; exact lt_irrefl _ hvw
  -- the faces in their planes
  set S1 := Q1.image (fun p => (a p, p 2)) with hS1
  set S2 := Q2.image (fun p => (b p, p 2)) with hS2
  have ofS1 : ∀ x z, (x, z) ∈ S1 → ∃ p ∈ Q1, a p = x ∧ p 2 = z := by
    intro x z h; rw [hS1, Finset.mem_image] at h
    obtain ⟨p, hp, e⟩ := h; simp only [Prod.mk.injEq] at e; exact ⟨p, hp, e.1, e.2⟩
  have ofS2 : ∀ x z, (x, z) ∈ S2 → ∃ p ∈ Q2, b p = x ∧ p 2 = z := by
    intro x z h; rw [hS2, Finset.mem_image] at h
    obtain ⟨p, hp, e⟩ := h; simp only [Prod.mk.injEq] at e; exact ⟨p, hp, e.1, e.2⟩
  have pt1 : ∀ p ∈ Q1, p = oblPt O r1 r2 (a p) 0 (p 2) := fun p hp => by
    conv_lhs => rw [hy p (h1V hp), hb1 p hp]
  have pt2 : ∀ p ∈ Q2, p = oblPt O r1 r2 0 (b p) (p 2) := fun p hp => by
    conv_lhs => rw [hy p (h2V hp), ha2 p hp]
  have d1 : ∀ {r r' : ℝ × ℝ} {u u' : ℝ³}, r ≠ r' → a u = r.1 → u 2 = r.2 → a u' = r'.1 →
      u' 2 = r'.2 → u ≠ u' := by
    intro r r' u u' h h1 h2 h1' h2' hu; apply h
    exact Prod.ext (by rw [← h1, ← h1', hu]) (by rw [← h2, ← h2', hu])
  have d2 : ∀ {r r' : ℝ × ℝ} {u u' : ℝ³}, r ≠ r' → b u = r.1 → u 2 = r.2 → b u' = r'.1 →
      u' 2 = r'.2 → u ≠ u' := by
    intro r r' u u' h h1 h2 h1' h2' hu; apply h
    exact Prod.ext (by rw [← h1, ← h1', hu]) (by rw [← h2, ← h2', hu])
  -- chains of the first face
  have chains1 : ∀ (s : ℝ) (u u' : ℝ³), (s = 1 ∨ s = -1) → (u = v ∧ u' = w ∨ u = w ∧ u' = v) →
      s * u' 2 < s * u 2 → ∃ m ca cz, ChainOK (fun x z => (x, z) ∈ S1) (u 2) s m ca cz := by
    intro s u u' hs huu hso
    have hu1 : u ∈ Q1 := by rcases huu with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> assumption
    have hau : a u = 0 := by rcases huu with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> assumption
    apply exists_chainOK_edge_uniq S1 (u 2) (u' 2) s hs hso
      (by rw [hS1, Finset.mem_image]; exact ⟨u, hu1, by rw [hau]⟩)
    · intro q hq h0 h1
      obtain ⟨p, hp, e1, e2⟩ := ofS1 q.1 q.2 hq
      by_cases hp2 : p ∈ Q2
      · exfalso
        have hpe : p = u ∨ p = u' := by
          rcases mem12 p hp hp2 with rfl | rfl <;> rcases huu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
        rcases hpe with rfl | rfl
        · exact h0 (Prod.ext (by rw [← e1, hau]) (by rw [← e2]))
        · apply h1; refine Prod.ext ?_ (by rw [← e2])
          show q.1 = 0; rw [← e1]; exact ha2 p hp2
      · rw [← e1]; exact ha2' p (h1V hp) hp2
    · obtain ⟨p, hp, hp2⟩ := hne1
      exact ⟨(a p, p 2), Finset.mem_image_of_mem _ hp, ha2' p (h1V hp) hp2⟩
    · intro q hq q' hq' q'' hq'' n1 n2 n3
      obtain ⟨p, hp, e1, e2⟩ := ofS1 q.1 q.2 hq
      obtain ⟨p', hp', e1', e2'⟩ := ofS1 q'.1 q'.2 hq'
      obtain ⟨p'', hp'', e1'', e2''⟩ := ofS1 q''.1 q''.2 hq''
      have := orient_ne_of_frame1' (O := O) (r1 := r1) (r2 := r2) (ai := a p) (zi := p 2)
        (aj := a p') (zj := p' 2) (zk := p'' 2) (ak := a p'')
        (by rw [e1, e2, e1', e2']; exact n1) (by
          intro c; rw [← pt1 p hp, ← pt1 p' hp', ← pt1 p'' hp'']
          exact hcol p (h1V hp) p' (h1V hp') p'' (h1V hp'') (d1 n1 e1 e2 e1' e2')
            (d1 n2 e1 e2 e1'' e2'') (d1 n3 e1' e2' e1'' e2'') c)
      unfold orient2 at this; rwa [e1, e2, e1', e2', e1'', e2''] at this
    · intro q hq q' hq' hmax e
      obtain ⟨p, hp, e1, e2⟩ := ofS1 q.1 q.2 (Finset.mem_of_mem_erase hq)
      obtain ⟨p', hp', e1', e2'⟩ := ofS1 q'.1 q'.2 (Finset.mem_of_mem_erase hq')
      obtain ⟨x, hx, hx2⟩ := hne1
      have hxpos := ha2' x (h1V hx) hx2
      have hpos : 0 < a p := by
        have := hmax (a x, x 2) (Finset.mem_erase.mpr ⟨fun h => by
          have := congrArg Prod.fst h; simp only at this; linarith, Finset.mem_image_of_mem _ hx⟩)
        rw [e1]; exact lt_of_lt_of_le hxpos this
      have hpmax : ∀ y ∈ Q1, a y ≤ a p := fun y hy => by
        by_cases hy2 : y ∈ Q2
        · rw [ha2 y hy2]; exact hpos.le
        · rw [e1]; exact hmax (a y, y 2) (Finset.mem_erase.mpr ⟨fun h => by
            have := congrArg Prod.fst h; simp only at this
            linarith [ha2' y (h1V hy) hy2], Finset.mem_image_of_mem _ hy⟩)
      by_cases hpp : p' = p
      · exact Prod.ext e (by rw [← e2', ← e2, hpp])
      · exfalso
        have hnot : ({p', p} : Finset ℝ³) ≠ {v, w} := fun h => by
          have hm : p ∈ ({v, w} : Finset ℝ³) := h ▸ (by simp)
          simp only [Finset.mem_insert, Finset.mem_singleton] at hm
          rcases hm with h' | h'
          · rw [h', hav] at hpos; exact lt_irrefl _ hpos
          · rw [h', haw] at hpos; exact lt_irrefl _ hpos
        rcases hmid p' (h1V hp') p (h1V hp) hpp hnot (by rw [e1', e1]; exact e)
            (by rw [hb1 p' hp', hb1 p hp]) with ⟨-, -, -, nf⟩ | ⟨-, hp2, -, -⟩ | ⟨hp'1, -, -, -⟩
        · exact nf hpmax
        · rw [ha2 p hp2] at hpos; exact lt_irrefl _ hpos
        · exact absurd hp' hp'1
  have chains2 : ∀ (s : ℝ) (u u' : ℝ³), (s = 1 ∨ s = -1) → (u = v ∧ u' = w ∨ u = w ∧ u' = v) →
      s * u' 2 < s * u 2 → ∃ m ca cz, ChainOK (fun x z => (x, z) ∈ S2) (u 2) s m ca cz := by
    intro s u u' hs huu hso
    have hu2 : u ∈ Q2 := by rcases huu with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> assumption
    have hbu : b u = 0 := by rcases huu with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> assumption
    apply exists_chainOK_edge_uniq S2 (u 2) (u' 2) s hs hso
      (by rw [hS2, Finset.mem_image]; exact ⟨u, hu2, by rw [hbu]⟩)
    · intro q hq h0 h1
      obtain ⟨p, hp, e1, e2⟩ := ofS2 q.1 q.2 hq
      by_cases hp1 : p ∈ Q1
      · exfalso
        have hpe : p = u ∨ p = u' := by
          rcases mem12 p hp1 hp with rfl | rfl <;> rcases huu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
        rcases hpe with rfl | rfl
        · exact h0 (Prod.ext (by rw [← e1, hbu]) (by rw [← e2]))
        · apply h1; refine Prod.ext ?_ (by rw [← e2])
          show q.1 = 0; rw [← e1]; exact hb1 p hp1
      · rw [← e1]; exact hb1' p (h2V hp) hp1
    · obtain ⟨p, hp, hp1⟩ := hne2
      exact ⟨(b p, p 2), Finset.mem_image_of_mem _ hp, hb1' p (h2V hp) hp1⟩
    · intro q hq q' hq' q'' hq'' n1 n2 n3
      obtain ⟨p, hp, e1, e2⟩ := ofS2 q.1 q.2 hq
      obtain ⟨p', hp', e1', e2'⟩ := ofS2 q'.1 q'.2 hq'
      obtain ⟨p'', hp'', e1'', e2''⟩ := ofS2 q''.1 q''.2 hq''
      have := orient_ne_of_frame2' (O := O) (r1 := r1) (r2 := r2) (bi := b p) (zi := p 2)
        (bj := b p') (zj := p' 2) (zk := p'' 2) (bk := b p'')
        (by rw [e1, e2, e1', e2']; exact n1) (by
          intro c; rw [← pt2 p hp, ← pt2 p' hp', ← pt2 p'' hp'']
          exact hcol p (h2V hp) p' (h2V hp') p'' (h2V hp'') (d2 n1 e1 e2 e1' e2')
            (d2 n2 e1 e2 e1'' e2'') (d2 n3 e1' e2' e1'' e2'') c)
      unfold orient2 at this; rwa [e1, e2, e1', e2', e1'', e2''] at this
    · intro q hq q' hq' hmax e
      obtain ⟨p, hp, e1, e2⟩ := ofS2 q.1 q.2 (Finset.mem_of_mem_erase hq)
      obtain ⟨p', hp', e1', e2'⟩ := ofS2 q'.1 q'.2 (Finset.mem_of_mem_erase hq')
      obtain ⟨x, hx, hx1⟩ := hne2
      have hxpos := hb1' x (h2V hx) hx1
      have hpos : 0 < b p := by
        have := hmax (b x, x 2) (Finset.mem_erase.mpr ⟨fun h => by
          have := congrArg Prod.fst h; simp only at this; linarith, Finset.mem_image_of_mem _ hx⟩)
        rw [e1]; exact lt_of_lt_of_le hxpos this
      have hpmax : ∀ y ∈ Q2, b y ≤ b p := fun y hy => by
        by_cases hy1 : y ∈ Q1
        · rw [hb1 y hy1]; exact hpos.le
        · rw [e1]; exact hmax (b y, y 2) (Finset.mem_erase.mpr ⟨fun h => by
            have := congrArg Prod.fst h; simp only at this
            linarith [hb1' y (h2V hy) hy1], Finset.mem_image_of_mem _ hy⟩)
      by_cases hpp : p' = p
      · exact Prod.ext e (by rw [← e2', ← e2, hpp])
      · exfalso
        have hnot : ({p', p} : Finset ℝ³) ≠ {v, w} := fun h => by
          have hm : p ∈ ({v, w} : Finset ℝ³) := h ▸ (by simp)
          simp only [Finset.mem_insert, Finset.mem_singleton] at hm
          rcases hm with h' | h'
          · rw [h', hbv] at hpos; exact lt_irrefl _ hpos
          · rw [h', hbw] at hpos; exact lt_irrefl _ hpos
        rcases hmid p' (h2V hp') p (h2V hp) hpp hnot (by rw [ha2 p' hp', ha2 p hp])
            (by rw [e1', e1]; exact e) with ⟨hp'1, hp1, -, -⟩ | ⟨-, -, -, nf⟩ | ⟨-, hp'2, -, -⟩
        · rw [hb1 p hp1] at hpos; exact lt_irrefl _ hpos
        · exact nf hpmax
        · exact absurd hp' hp'2
  have up : (1 : ℝ) * v 2 < 1 * w 2 := by linarith
  have lo : (-1 : ℝ) * w 2 < -1 * v 2 := by linarith
  obtain ⟨xa, hxa, xb, hxb, hxa2, hxb1, hin'⟩ := hin
  refine isRupert_edge_frame_tieR O r1 r2 hρ (fun x z => (x, z) ∈ S1) (fun x z => (x, z) ∈ S2)
    (zx := v 2) (zx' := w 2) hvw
    (chains1 1 w v (Or.inl rfl) (Or.inr ⟨rfl, rfl⟩) up)
    (chains1 (-1) v w (Or.inr rfl) (Or.inl ⟨rfl, rfl⟩) lo)
    (chains2 1 w v (Or.inl rfl) (Or.inr ⟨rfl, rfl⟩) up)
    (chains2 (-1) v w (Or.inr rfl) (Or.inl ⟨rfl, rfl⟩) lo) ?_ ?_
    (Finset.mem_image.mpr ⟨v, hv1, by rw [hav]⟩) (Finset.mem_image.mpr ⟨w, hw1, by rw [haw]⟩)
    (Finset.mem_image.mpr ⟨v, hv2, by rw [hbv]⟩) (Finset.mem_image.mpr ⟨w, hw2, by rw [hbw]⟩)
    ?_ ?_ V ?_ ?_ ?_ hsol ?_
  · intro z h
    obtain ⟨p, hp, e1, e2⟩ := ofS1 0 z h
    by_cases hp2 : p ∈ Q2
    · rcases mem12 p hp hp2 with rfl | rfl
      · exact Or.inl e2.symm
      · exact Or.inr e2.symm
    · linarith [ha2' p (h1V hp) hp2]
  · intro z h
    obtain ⟨p, hp, e1, e2⟩ := ofS2 0 z h
    by_cases hp1 : p ∈ Q1
    · rcases mem12 p hp1 hp with rfl | rfl
      · exact Or.inl e2.symm
      · exact Or.inr e2.symm
    · linarith [hb1' p (h2V hp) hp1]
  · intro x z h
    obtain ⟨p, hp, e1, e2⟩ := ofS1 x z h
    by_cases hp2 : p ∈ Q2
    · rw [← e1, ha2 p hp2]
    · rw [← e1]; exact (ha2' p (h1V hp) hp2).le
  · intro x z h
    obtain ⟨p, hp, e1, e2⟩ := ofS2 x z h
    by_cases hp1 : p ∈ Q1
    · rw [← e1, hb1 p hp1]
    · rw [← e1]; exact (hb1' p (h2V hp) hp1).le
  · intro x z h
    obtain ⟨p, hp, e1, e2⟩ := ofS1 x z h
    rw [← e1, ← e2, ← pt1 p hp]; exact h1V hp
  · intro x z h
    obtain ⟨p, hp, e1, e2⟩ := ofS2 x z h
    rw [← e1, ← e2, ← pt2 p hp]; exact h2V hp
  · intro y hy'
    refine ⟨a y, b y, y 2, hy y hy', ?_⟩
    by_cases h1 : y ∈ Q1
    · exact Or.inl ⟨hb1 y h1, Finset.mem_image_of_mem _ h1⟩
    by_cases h2 : y ∈ Q2
    · exact Or.inr (Or.inl ⟨ha2 y h2, Finset.mem_image_of_mem (fun p => (b p, p 2)) h2⟩)
    refine Or.inr (Or.inr ⟨ha2' y hy' h2, hb1' y hy' h1, ?_⟩)
    intro m ca cz n cb dz C1 C2
    have hA := C1.far_pos
    have hB := C2.far_pos
    have hxa0 := ha2' xa (h1V hxa) hxa2
    have hxb0 := hb1' xb (h2V hxb) hxb1
    have le1 : a xa ≤ ca m := by
      by_cases e : a xa = ca m ∧ xa 2 = cz m
      · exact e.1.le
      · exact (C1.far _ _ (Finset.mem_image_of_mem _ hxa) e).le
    have le2 : b xb ≤ cb n := by
      by_cases e : b xb = cb n ∧ xb 2 = dz n
      · exact e.1.le
      · exact (C2.far _ _ (Finset.mem_image_of_mem (fun p => (b p, p 2)) hxb) e).le
    have k := hin' y hy' h1 h2
    have ha := ha2' y hy' h2
    have hb := hb1' y hy' h1
    have t1 : a y / ca m ≤ a y / a xa := div_le_div_of_nonneg_left ha.le hxa0 le1
    have t2 : b y / cb n ≤ b y / b xb := div_le_div_of_nonneg_left hb.le hxb0 le2
    have : a y / ca m + b y / cb n < 1 := by linarith
    rw [div_add_div _ _ hA.ne' hB.ne', div_lt_one (mul_pos hA hB)] at this
    linarith
  · intro m ca cz n cb dz C1 C2
    obtain ⟨p, hp, e1, e2⟩ := ofS1 _ _ (C1.mem m le_rfl)
    obtain ⟨q, hq, f1, f2⟩ := ofS2 _ _ (C2.mem n le_rfl)
    have hpq : p ≠ q := by
      intro e; subst e
      have := C1.far_pos
      rw [← e1, ha2 p hq] at this; exact lt_irrefl _ this
    have pmax : ∀ p' ∈ Q1, a p' ≤ a p := fun p' hp' => by
      rw [e1]
      by_cases e : a p' = ca m ∧ p' 2 = cz m
      · exact e.1.le
      · exact (C1.far _ _ (Finset.mem_image_of_mem _ hp') e).le
    have qmax : ∀ q' ∈ Q2, b q' ≤ b q := fun q' hq' => by
      rw [f1]
      by_cases e : b q' = cb n ∧ q' 2 = dz n
      · exact e.1.le
      · exact (C2.far _ _ (Finset.mem_image_of_mem (fun p => (b p, p 2)) hq') e).le
    rcases hfarZ p hp q hq hpq pmax qmax with hT | hpq2
    · have old : cz m ≠ dz n ∨ ETie (fun x z => (x, z) ∈ S1) (fun x z => (x, z) ∈ S2) (v 2) (w 2)
          (ca m) (cz m) (cb n) (dz n) := by
        rcases hT with hne | ⟨s, hs, hv | hv | ⟨u, hu, hv⟩ | ⟨u, hu, hv⟩⟩
        · left; rw [← e2, ← f2]; exact hne
        · refine Or.inr ⟨s, hs, Or.inl fun x z hxz hn => ?_⟩
          obtain ⟨p', hp', g1, g2⟩ := ofS1 x z hxz
          rw [← g2, ← e2]
          exact hv p' hp' (fun h => hn ⟨by rw [← g1, h, e1], by rw [← g2, h, e2]⟩)
        · refine Or.inr ⟨s, hs, Or.inr (Or.inl fun x z hxz hn => ?_)⟩
          obtain ⟨q', hq', g1, g2⟩ := ofS2 x z hxz
          rw [← g2, ← f2]
          exact hv q' hq' (fun h => hn ⟨by rw [← g1, h, f1], by rw [← g2, h, f2]⟩)
        · have hau : a u = 0 := by rcases hu with rfl | rfl; exacts [hav, haw]
          refine Or.inr ⟨s, hs, Or.inr (Or.inr (Or.inl ⟨u 2, ?_, fun x z hxz hn => ?_⟩))⟩
          · rcases hu with rfl | rfl; exacts [Or.inl rfl, Or.inr rfl]
          obtain ⟨p', hp', g1, g2⟩ := ofS1 x z hxz
          rw [← g2]
          exact hv p' hp' (fun h => hn ⟨by rw [← g1, h, hau], by rw [← g2, h]⟩)
        · have hbu : b u = 0 := by rcases hu with rfl | rfl; exacts [hbv, hbw]
          refine Or.inr ⟨s, hs, Or.inr (Or.inr (Or.inr ⟨u 2, ?_, fun x z hxz hn => ?_⟩))⟩
          · rcases hu with rfl | rfl; exacts [Or.inl rfl, Or.inr rfl]
          obtain ⟨q', hq', g1, g2⟩ := ofS2 x z hxz
          rw [← g2]
          exact hv q' hq' (fun h => hn ⟨by rw [← g1, h, hbu], by rw [← g2, h]⟩)
      rcases old with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · right; right
      simp only at hpq2
      rw [← e2, ← f2]; exact hpq2

set_option maxHeartbeats 4000000 in
/-- **Lemma T over an edge, the edge vertical**, with `v` below `w`. -/
theorem isRupert_facets_edge_vertical_lt_tieR (V Q1 Q2 : Finset ℝ³) (v w : ℝ³) (hvw : v 2 < w 2)
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hint : Q1 ∩ Q2 = {v, w}) (f1 f2 : ℝ³ →ᵃ[ℝ] ℝ)
    (z1 : ∀ p ∈ Q1, f1 p = 0) (n1 : ∀ p ∈ V, p ∉ Q1 → f1 p < 0)
    (z2 : ∀ p ∈ Q2, f2 p = 0) (n2 : ∀ p ∈ V, p ∉ Q2 → f2 p < 0)
    (e1 : f1 (v + ez) = 0) (e2 : f2 (v + ez) = 0)
    (hne1 : ∃ p ∈ Q1, p ∉ Q2) (hne2 : ∃ p ∈ Q2, p ∉ Q1)
    (hcol : ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V, p ≠ q → p ≠ r → q ≠ r → ∀ c : ℝ, r - p ≠ c • (q - p))
    (hpar : ∀ p ∈ V, ∀ q ∈ V, p ≠ q → ({p, q} : Finset ℝ³) ≠ {v, w} → p 0 = q 0 → p 1 = q 1 →
      MidPair Q1 Q2 (fun p => ∀ p' ∈ Q1, f2 p ≤ f2 p') (fun q => ∀ q' ∈ Q2, f1 q ≤ f1 q') p q)
    (hfarZ : ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, f2 p ≤ f2 p') → (∀ q' ∈ Q2, f1 q ≤ f1 q') →
      TieHER Q1 Q2 v w p q (fun x => x 2))
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ∉ Q2 ∧ xb ∉ Q1 ∧
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → f2 y / f2 xa + f1 y / f1 xb < 1)
    (hsol : (interior (convexHull ℝ (V : Set ℝ³))).Nonempty) : IsRupert V := by
  classical
  have hvi : v ∈ Q1 ∩ Q2 := by rw [hint]; simp
  have hv1 := (Finset.mem_inter.mp hvi).1; have hv2 := (Finset.mem_inter.mp hvi).2
  obtain ⟨p1, hp1, hp12⟩ := hne1
  obtain ⟨p2, hp2, hp21⟩ := hne2
  have m21 : f2 p1 < 0 := n2 p1 (h1V hp1) hp12
  have m12 : f1 p2 < 0 := n1 p2 (h2V hp2) hp21
  obtain ⟨K1, α1, β1, γ1, h1⟩ := affine_xyz f1
  obtain ⟨K2, α2, β2, γ2, h2⟩ := affine_xyz f2
  have v1 := z1 v hv1; have v2 := z2 v hv2
  have hγ1 : γ1 = 0 := by
    rw [h1] at e1 v1; simp [ez] at e1; linarith
  have hγ2 : γ2 = 0 := by
    rw [h2] at e2 v2; simp [ez] at e2; linarith
  have g1 : ∀ p, f1 p = α1 * (p 0 - v 0) + β1 * (p 1 - v 1) := by
    intro p; have := v1; rw [h1, hγ1] at this ⊢; linarith
  have g2 : ∀ p, f2 p = α2 * (p 0 - v 0) + β2 * (p 1 - v 1) := by
    intro p; have := v2; rw [h2, hγ2] at this ⊢; linarith
  set O : ℝ² := !₂[v 0, v 1] with hO
  set r1 : ℝ² := !₂[p1 0 - v 0, p1 1 - v 1] with hr1
  set r2 : ℝ² := !₂[p2 0 - v 0, p2 1 - v 1] with hr2
  have q11 : α1 * (p1 0 - v 0) + β1 * (p1 1 - v 1) = 0 := by rw [← g1]; exact z1 p1 hp1
  have q22 : α2 * (p2 0 - v 0) + β2 * (p2 1 - v 1) = 0 := by rw [← g2]; exact z2 p2 hp2
  have hρ : cross2 r1 r2 ≠ 0 := by
    intro hρ0
    simp only [hr1, hr2, cross2] at hρ0
    simp at hρ0
    have k0 : f1 p2 * (p1 0 - v 0) = 0 := by
      rw [g1]; linear_combination (p2 0 - v 0) * q11 + β1 * hρ0
    have k1 : f1 p2 * (p1 1 - v 1) = 0 := by
      rw [g1]; linear_combination (p2 1 - v 1) * q11 - α1 * hρ0
    have r10 := (mul_eq_zero.mp k0).resolve_left m12.ne
    have r11 := (mul_eq_zero.mp k1).resolve_left m12.ne
    have := g2 p1; rw [r10, r11] at this; linarith
  set ρ := cross2 r1 r2 with hρdef
  set a : ℝ³ → ℝ := fun p => cross2 !₂[p 0 - v 0, p 1 - v 1] r2 / ρ with ha
  set b : ℝ³ → ℝ := fun p => cross2 r1 !₂[p 0 - v 0, p 1 - v 1] / ρ with hb
  have hxy : ∀ p : ℝ³, p 0 - v 0 = a p * r1 0 + b p * r2 0 ∧ p 1 - v 1 = a p * r1 1 + b p * r2 1 := by
    intro p
    obtain ⟨c0, c1⟩ := cramer2 !₂[p 0 - v 0, p 1 - v 1] r1 r2 hρ
    simp at c0 c1; exact ⟨c0, c1⟩
  have hy : ∀ p : ℝ³, p = oblPt O r1 r2 (a p) (b p) (p 2) := by
    intro p; obtain ⟨c0, c1⟩ := hxy p
    ext j; fin_cases j
    · simp only [oblPt, hO]; simp; linarith
    · simp only [oblPt, hO]; simp; linarith
    · simp [oblPt]
  have r10 : r1 0 = p1 0 - v 0 := by simp [hr1]
  have r11 : r1 1 = p1 1 - v 1 := by simp [hr1]
  have r20 : r2 0 = p2 0 - v 0 := by simp [hr2]
  have r21 : r2 1 = p2 1 - v 1 := by simp [hr2]
  have G1 : ∀ p, f1 p = b p * f1 p2 := by
    intro p; rw [g1 p, g1 p2, (hxy p).1, (hxy p).2, r10, r11, r20, r21]
    linear_combination a p * q11
  have G2 : ∀ p, f2 p = a p * f2 p1 := by
    intro p; rw [g2 p, g2 p1, (hxy p).1, (hxy p).2, r10, r11, r20, r21]
    linear_combination b p * q22
  have hb1 : ∀ p ∈ Q1, b p = 0 := fun p hp => by
    have := G1 p; rw [z1 p hp] at this
    exact (mul_eq_zero.mp this.symm).resolve_right m12.ne
  have ha2 : ∀ p ∈ Q2, a p = 0 := fun p hp => by
    have := G2 p; rw [z2 p hp] at this
    exact (mul_eq_zero.mp this.symm).resolve_right m21.ne
  have hb1' : ∀ p ∈ V, p ∉ Q1 → 0 < b p := fun p hp hq => by
    have := n1 p hp hq; rw [G1] at this; nlinarith
  have ha2' : ∀ p ∈ V, p ∉ Q2 → 0 < a p := fun p hp hq => by
    have := n2 p hp hq; rw [G2] at this; nlinarith
  have hmid : ∀ p ∈ V, ∀ q ∈ V, p ≠ q → ({p, q} : Finset ℝ³) ≠ {v, w} → a p = a q → b p = b q →
      MidPair Q1 Q2 (fun p => ∀ p' ∈ Q1, a p' ≤ a p) (fun q => ∀ q' ∈ Q2, b q' ≤ b q) p q := by
    intro p hp q hq hpq hne ea eb
    obtain ⟨c0, c1⟩ := hxy p; obtain ⟨d0, d1⟩ := hxy q
    rw [ea, eb] at c0 c1
    refine (hpar p hp q hq hpq hne (by linarith) (by linarith)).mono (fun x _ hx p' hp' => ?_)
      (fun x _ hx q' hq' => ?_)
    · rw [G2 x, G2 p']; exact mul_le_mul_of_nonpos_right (hx p' hp') m21.le
    · rw [G1 x, G1 q']; exact mul_le_mul_of_nonpos_right (hx q' hq') m12.le
  have hfar' : ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, a p' ≤ a p) → (∀ q' ∈ Q2, b q' ≤ b q) →
      TieHER Q1 Q2 v w p q (fun x => x 2) := fun p hp q hq hpq h1 h2 =>
    hfarZ p hp q hq hpq (fun p' hp' => by
        rw [G2 p, G2 p']; exact mul_le_mul_of_nonpos_right (h1 p' hp') m21.le)
      (fun q' hq' => by rw [G1 q, G1 q']; exact mul_le_mul_of_nonpos_right (h2 q' hq') m12.le)
  have hin' : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ∉ Q2 ∧ xb ∉ Q1 ∧
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → a y / a xa + b y / b xb < 1 := by
    obtain ⟨xa, hxa, xb, hxb, hxa2, hxb1, h⟩ := hin
    refine ⟨xa, hxa, xb, hxb, hxa2, hxb1, fun y hy hy1 hy2 => ?_⟩
    have k := h y hy hy1 hy2
    rw [G1 y, G1 xb, G2 y, G2 xa, mul_div_mul_right _ _ m21.ne, mul_div_mul_right _ _ m12.ne] at k
    exact k
  rcases lt_or_gt_of_ne hρ with hneg | hpos
  · have hpos' : 0 < cross2 r2 r1 := by
      have : cross2 r2 r1 = -cross2 r1 r2 := by unfold cross2; ring
      rw [this]; linarith
    have swap : ∀ p q z, oblPt O r2 r1 q p z = oblPt O r1 r2 p q z := by
      intro p q z; ext j; fin_cases j <;> simp [oblPt] <;> ring
    refine isRupert_edge_coords_tieR O r2 r1 hpos' V Q2 Q1 v w hvw b a
      (fun p _ => by rw [swap]; exact hy p) h2V h1V (by rw [Finset.inter_comm]; exact hint)
      ha2 ha2' hb1 hb1' ⟨p2, hp2, hp21⟩ ⟨p1, hp1, hp12⟩ hcol ?_
      (fun p hp q hq hpq h1 h2 => (hfar' q hq p hp (Ne.symm hpq) h2 h1).swap) ?_ hsol
    · intro p hp q hq hpq hne ea eb
      exact (hmid p hp q hq hpq hne eb ea).swap
    · obtain ⟨xa, hxa, xb, hxb, hxa2, hxb1, h⟩ := hin'
      exact ⟨xb, hxb, xa, hxa, hxb1, hxa2, fun y hy hy2 hy1 => by
        rw [add_comm]; exact h y hy hy1 hy2⟩
  · exact isRupert_edge_coords_tieR O r1 r2 hpos V Q1 Q2 v w hvw a b (fun p _ => hy p) h1V h2V hint
      hb1 hb1' ha2 ha2' ⟨p1, hp1, hp12⟩ ⟨p2, hp2, hp21⟩ hcol hmid hfar' hin' hsol

/-- **Lemma T over an edge, the edge vertical.** -/
theorem isRupert_facets_edge_vertical_tieR (V Q1 Q2 : Finset ℝ³) (v w : ℝ³) (hvw : v ≠ w)
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hint : Q1 ∩ Q2 = {v, w}) (f1 f2 : ℝ³ →ᵃ[ℝ] ℝ)
    (z1 : ∀ p ∈ Q1, f1 p = 0) (n1 : ∀ p ∈ V, p ∉ Q1 → f1 p < 0)
    (z2 : ∀ p ∈ Q2, f2 p = 0) (n2 : ∀ p ∈ V, p ∉ Q2 → f2 p < 0)
    (e1 : f1 (v + ez) = 0) (e2 : f2 (v + ez) = 0)
    (hne1 : ∃ p ∈ Q1, p ∉ Q2) (hne2 : ∃ p ∈ Q2, p ∉ Q1)
    (hcol : ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V, p ≠ q → p ≠ r → q ≠ r → ∀ c : ℝ, r - p ≠ c • (q - p))
    (hpar : ∀ p ∈ V, ∀ q ∈ V, p ≠ q → ({p, q} : Finset ℝ³) ≠ {v, w} → p 0 = q 0 → p 1 = q 1 →
      MidPair Q1 Q2 (fun p => ∀ p' ∈ Q1, f2 p ≤ f2 p') (fun q => ∀ q' ∈ Q2, f1 q ≤ f1 q') p q)
    (hvw2 : v 2 ≠ w 2)
    (hfarZ : ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, f2 p ≤ f2 p') → (∀ q' ∈ Q2, f1 q ≤ f1 q') →
      TieHER Q1 Q2 v w p q (fun x => x 2))
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ∉ Q2 ∧ xb ∉ Q1 ∧
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → f2 y / f2 xa + f1 y / f1 xb < 1)
    (hsol : (interior (convexHull ℝ (V : Set ℝ³))).Nonempty) : IsRupert V := by
  have hvi : v ∈ Q1 ∩ Q2 := by rw [hint]; simp
  have hwi : w ∈ Q1 ∩ Q2 := by rw [hint]; simp
  have hvV : v ∈ V := h1V (Finset.mem_inter.mp hvi).1
  have hwV : w ∈ V := h1V (Finset.mem_inter.mp hwi).1
  rcases lt_or_gt_of_ne hvw2 with hlt | hgt
  · exact isRupert_facets_edge_vertical_lt_tieR V Q1 Q2 v w hlt h1V h2V hint f1 f2 z1 n1 z2 n2 e1 e2
      hne1 hne2 hcol hpar hfarZ hin hsol
  · -- the line through `w` is the same vertical line
    have hw : ∀ (f : ℝ³ →ᵃ[ℝ] ℝ), f v = 0 → f (v + ez) = 0 → f w = 0 → f (w + ez) = 0 := by
      intro f h0 h1 hw0
      have k1 : f (v + ez) = f.linear ez + f v := by
        rw [show v + ez = ez +ᵥ v by rw [vadd_eq_add, add_comm]]; exact f.map_vadd v ez
      have k2 : f (w + ez) = f.linear ez + f w := by
        rw [show w + ez = ez +ᵥ w by rw [vadd_eq_add, add_comm]]; exact f.map_vadd w ez
      rw [k2, hw0]; rw [k1, h0] at h1; linarith
    have hv1 := (Finset.mem_inter.mp hvi).1; have hv2 := (Finset.mem_inter.mp hvi).2
    have hw1 := (Finset.mem_inter.mp hwi).1; have hw2 := (Finset.mem_inter.mp hwi).2
    refine isRupert_facets_edge_vertical_lt_tieR V Q1 Q2 w v hgt h1V h2V
      (by rw [Finset.pair_comm]; exact hint) f1 f2 z1 n1 z2 n2
      (hw f1 (z1 v hv1) e1 (z1 w hw1)) (hw f2 (z2 v hv2) e2 (z2 w hw2)) hne1 hne2 hcol
      (fun p hp q hq hpq h e0 e1' => hpar p hp q hq hpq (by rw [Finset.pair_comm v w]; exact h) e0 e1')
      (fun p hp q hq hpq h1 h2 => (hfarZ p hp q hq hpq h1 h2).comm) hin hsol

set_option maxHeartbeats 4000000 in
/-- **Lemma T over an edge** for two facets `Q1`, `Q2` (functionals `f1`, `f2`)
sharing the edge `v w`, viewed along it: no three points collinear, no other
segment parallel to it, distinct far depths along it, and every point off both
facets inside the shadow triangle of the edge and some `xa ∈ Q1 \ Q2`,
`xb ∈ Q2 \ Q1`. -/
theorem isRupert_facets_edge_tieR (V Q1 Q2 : Finset ℝ³) (v w : ℝ³) (hvw : v ≠ w)
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hint : Q1 ∩ Q2 = {v, w}) (f1 f2 : ℝ³ →ᵃ[ℝ] ℝ)
    (z1 : ∀ p ∈ Q1, f1 p = 0) (n1 : ∀ p ∈ V, p ∉ Q1 → f1 p < 0)
    (z2 : ∀ p ∈ Q2, f2 p = 0) (n2 : ∀ p ∈ V, p ∉ Q2 → f2 p < 0)
    (hne1 : ∃ p ∈ Q1, p ∉ Q2) (hne2 : ∃ p ∈ Q2, p ∉ Q1)
    (hcol : ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V, p ≠ q → p ≠ r → q ≠ r → ∀ c : ℝ, r - p ≠ c • (q - p))
    (hpar : ∀ p ∈ V, ∀ q ∈ V, p ≠ q → ({p, q} : Finset ℝ³) ≠ {v, w} → ∀ c : ℝ, q - p = c • (w - v) →
      MidPair Q1 Q2 (fun p => ∀ p' ∈ Q1, f2 p ≤ f2 p') (fun q => ∀ q' ∈ Q2, f1 q ≤ f1 q') p q)
    (hfarZ : ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, f2 p ≤ f2 p') → (∀ q' ∈ Q2, f1 q ≤ f1 q') →
      TieHER Q1 Q2 v w p q (fun x => ⟪x, w - v⟫))
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ∉ Q2 ∧ xb ∉ Q1 ∧
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → f2 y / f2 xa + f1 y / f1 xb < 1)
    (hsol : (interior (convexHull ℝ (V : Set ℝ³))).Nonempty) : IsRupert V := by
  classical
  have he : w - v ≠ 0 := sub_ne_zero.mpr hvw.symm
  obtain ⟨R, hR, r, hr, hRe⟩ := exists_rotation_to_ez_pos (w - v) he
  apply isRupert_of_isRupert_image_rotation R hR
  set g := R.toEuclideanLin with hg
  set I := so3Isometry hR with hI
  have hgI : ∀ p, g p = I p := fun p => rfl
  have hginj : Function.Injective g := I.injective
  have hgz : ∀ p, g p 2 = ⟪p, w - v⟫ / r := fun p => by
    have := inner_toEuclideanLin_SO3 hR p (w - v)
    rw [hRe, real_inner_smul_right, inner_ez] at this
    field_simp; linarith
  have hIe : I.symm ez = r⁻¹ • (w - v) := by
    apply I.injective
    rw [LinearIsometryEquiv.apply_symm_apply, map_smul, ← hgI, hRe, smul_smul,
      inv_mul_cancel₀ hr.ne', one_smul]
  set F1 := f1.comp I.symm.toLinearEquiv.toLinearMap.toAffineMap with hF1
  set F2 := f2.comp I.symm.toLinearEquiv.toLinearMap.toAffineMap with hF2
  have tF1 : ∀ p, F1 (g p) = f1 p := fun p => by simp [hF1, hgI]
  have tF2 : ∀ p, F2 (g p) = f2 p := fun p => by simp [hF2, hgI]
  have tz : ∀ f : ℝ³ →ᵃ[ℝ] ℝ, f v = 0 → f w = 0 →
      (f.comp I.symm.toLinearEquiv.toLinearMap.toAffineMap) (g v + ez) = 0 := by
    intro f h0 h1
    have : (f.comp I.symm.toLinearEquiv.toLinearMap.toAffineMap) (g v + ez) =
        f (v + r⁻¹ • (w - v)) := by
      simp [hgI, map_add, hIe]
    rw [this]; exact affine_zero_line f h0 (by rw [add_sub_cancel]; exact h1) _
  have hvi : v ∈ Q1 ∩ Q2 := by rw [hint]; simp
  have hwi : w ∈ Q1 ∩ Q2 := by rw [hint]; simp
  have hv1 := (Finset.mem_inter.mp hvi).1; have hv2 := (Finset.mem_inter.mp hvi).2
  have hw1 := (Finset.mem_inter.mp hwi).1; have hw2 := (Finset.mem_inter.mp hwi).2
  have memg : ∀ (S : Finset ℝ³) p, g p ∈ S.image g ↔ p ∈ S := fun S p =>
    ⟨fun h => by obtain ⟨q, hq, e⟩ := Finset.mem_image.mp h; rwa [← hginj e], Finset.mem_image_of_mem g⟩
  have allg : ∀ (S : Finset ℝ³) (P : ℝ³ → Prop), (∀ p ∈ S, P (g p)) → ∀ q ∈ S.image g, P q := by
    intro S P h q hq; obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq; exact h p hp
  refine isRupert_facets_edge_vertical_tieR (V.image g) (Q1.image g) (Q2.image g) (g v) (g w)
    (fun h => hvw (hginj h))
    (Finset.image_subset_image h1V) (Finset.image_subset_image h2V)
    (by rw [← Finset.image_inter _ _ hginj, hint, Finset.image_insert, Finset.image_singleton]) F1 F2
    (allg Q1 _ (fun p hp => by rw [tF1]; exact z1 p hp))
    (allg V _ (fun p hp hq => by rw [tF1]; exact n1 p hp (fun h => hq ((memg Q1 p).mpr h))))
    (allg Q2 _ (fun p hp => by rw [tF2]; exact z2 p hp))
    (allg V _ (fun p hp hq => by rw [tF2]; exact n2 p hp (fun h => hq ((memg Q2 p).mpr h))))
    (tz f1 (z1 v hv1) (z1 w hw1)) (tz f2 (z2 v hv2) (z2 w hw2)) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (interior_convexHull_image_rot hR hsol)
  · obtain ⟨p, hp, hp2⟩ := hne1
    exact ⟨g p, Finset.mem_image_of_mem g hp, fun h => hp2 ((memg Q2 p).mp h)⟩
  · obtain ⟨p, hp, hp1⟩ := hne2
    exact ⟨g p, Finset.mem_image_of_mem g hp, fun h => hp1 ((memg Q1 p).mp h)⟩
  · refine allg V _ (fun p hp => allg V _ (fun q hq => allg V _ (fun u hu => ?_)))
    intro hpq hpu hqu c h
    apply hcol p hp q hq u hu (fun e => hpq (by rw [e])) (fun e => hpu (by rw [e]))
      (fun e => hqu (by rw [e])) c
    apply hginj
    simp only [map_sub, map_smul] at h ⊢; exact h
  · refine allg V _ (fun p hp => allg V _ (fun q hq => ?_))
    intro hpq hpair h0 h1
    have hc : q - p = ((g (q - p)) 2 / r) • (w - v) := by
      apply hginj
      rw [map_smul, hRe]
      ext k; fin_cases k
      · simp [ez, map_sub]; linarith
      · simp [ez, map_sub]; linarith
      · simp [ez]; field_simp
    refine (hpar p hp q hq (fun e => hpq (by rw [e])) (fun e => hpair (by
      rw [show ({g p, g q} : Finset ℝ³) = Finset.image g {p, q} by simp,
        show ({g v, g w} : Finset ℝ³) = Finset.image g {v, w} by simp, e])) _ hc).map g hginj
      (fun x _ hf p' hp' => ?_) (fun x _ hf q' hq' => ?_)
    · have := hf (g p') (Finset.mem_image_of_mem g hp'); rwa [tF2, tF2] at this
    · have := hf (g q') (Finset.mem_image_of_mem g hq'); rwa [tF1, tF1] at this
  · rw [hgz, hgz]
    intro h
    have k : ⟪v, w - v⟫ = ⟪w, w - v⟫ := by simpa [hr.ne'] using h
    have : ⟪w - v, w - v⟫ = 0 := by rw [inner_sub_left]; linarith
    exact hvw (sub_eq_zero.mp (inner_self_eq_zero.mp this)).symm
  · refine allg Q1 _ (fun p hp => allg Q2 _ (fun q hq => ?_))
    intro hpq h1 h2
    refine (hfarZ p hp q hq (fun e => hpq (by rw [e])) (fun p' hp' => ?_) (fun q' hq' => ?_)).map g
      hr (fun x => hgz x) (fun x y => map_sub g x y) (fun x y => inner_toEuclideanLin_SO3 hR x y)
    · have := h1 (g p') (Finset.mem_image_of_mem g hp'); rwa [tF2, tF2] at this
    · have := h2 (g q') (Finset.mem_image_of_mem g hq'); rwa [tF1, tF1] at this
  · obtain ⟨xa, hxa, xb, hxb, hxa2, hxb1, h⟩ := hin
    refine ⟨g xa, Finset.mem_image_of_mem g hxa, g xb, Finset.mem_image_of_mem g hxb,
      fun e => hxa2 ((memg Q2 xa).mp e), fun e => hxb1 ((memg Q1 xb).mp e),
      allg V _ (fun y hy hy1 hy2 => ?_)⟩
    rw [tF1, tF1, tF2, tF2]
    exact h y hy (fun h => hy1 ((memg Q1 y).mpr h)) (fun h => hy2 ((memg Q2 y).mpr h))

set_option maxHeartbeats 4000000 in
/-- **Lemma T over an edge at the tie, facet form** (`FEWER-FACES-PROOFS.md` §7): two
facets `Q1`, `Q2` of `V` (no three points collinear) sharing exactly the edge
`v w`, general position along it (`EdgeFar`), and every point off both
facets inside the shadow triangle of the edge and some `xa ∈ Q1 \ Q2`,
`xb ∈ Q2 \ Q1` (stated with any facet functionals `f1`, `f2`): Rupert. -/
theorem isRupert_of_facets_edge_tieR (V : Finset ℝ³) (hgen : NoThreeCollinear V)
    (Q1 Q2 : Finset ℝ³) (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (h1f : IsFacet V Q1) (h2f : IsFacet V Q2)
    (v w : ℝ³) (hvw : v ≠ w) (hint : Q1 ∩ Q2 = {v, w})
    (hne1 : ∃ p ∈ Q1, p ∉ Q2) (hne2 : ∃ p ∈ Q2, p ∉ Q1)
    (hfarZ : EdgeTieR V Q1 Q2 v w)
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ∉ Q2 ∧ xb ∉ Q1 ∧ ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ,
      (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
      (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → f2 y / f2 xa + f1 y / f1 xb < 1)
    (hsol : (interior (convexHull ℝ (V : Set ℝ³))).Nonempty) : IsRupert V := by
  classical
  have hvi : v ∈ Q1 ∩ Q2 := by rw [hint]; simp
  have hwi : w ∈ Q1 ∩ Q2 := by rw [hint]; simp
  have hvV : v ∈ V := h1V (Finset.mem_inter.mp hvi).1
  have hwV : w ∈ V := h1V (Finset.mem_inter.mp hwi).1
  obtain ⟨f1, z1, n1⟩ := h1f
  obtain ⟨f2, z2, n2⟩ := h2f
  obtain ⟨xa, hxa, xb, hxb, hxa2, hxb1, hin'⟩ := hin
  obtain ⟨hpar, hfar⟩ := hfarZ f1 f2 z1 n1 z2 n2
  exact isRupert_facets_edge_tieR V Q1 Q2 v w hvw h1V h2V hint f1 f2 z1 n1 z2 n2 hne1 hne2 hgen
    hpar hfar ⟨xa, hxa, xb, hxb, hxa2, hxb1, hin' f1 f2 z1 n1 z2 n2⟩ hsol

/-- **Lemma T at the tie over an edge with a triangle face, middle and hidden parallels
allowed**: `EdgePar` gives `EdgeTieR` (the triangle settles any tie of the far ends: `TieHE`;
the parallel clause is the same, FEWER-FACES-PROOFS.md Proposition 23.19 (2), (3)). -/
theorem edgeTieR_of_tri {V Q1 Q2 : Finset ℝ³} {v w : ℝ³} (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V)
    (hv1 : v ∈ Q1) (hw1 : w ∈ Q1) (hv2 : v ∈ Q2) (hw2 : w ∈ Q2) (hvw : v ≠ w)
    (h12 : ∃ x ∈ Q1, x ∉ Q2) (h21 : ∃ x ∈ Q2, x ∉ Q1) (hcard : Q1.card = 3 ∨ Q2.card = 3)
    (hpar : EdgePar V Q1 Q2 v w) : EdgeTieR V Q1 Q2 v w :=
  fun f1 f2 z1 n1 z2 n2 =>
    ⟨hpar f1 f2 z1 n1 z2 n2, fun p hp q hq hpq h1 h2 =>
      Or.inl (edgeTieHE_of_tri h1V h2V hv1 hw1 hv2 hw2 hvw h12 h21 hcard f1 f2 z1 n1 z2 n2
        p hp q hq hpq h1 h2)⟩

/-- **Lemma T over an edge with a triangle face, facet form**: as `isRupert_of_facets_edge_tieR`,
with `EdgeTieR` replaced by `EdgePar` (no far-depth condition) when `Q1` or `Q2` is a triangle.
Segments parallel to the edge are allowed between two middles of one face or two hidden
vertices (`MidPair`; FEWER-FACES-PROOFS.md Proposition 23.19 (2), (3)).  The earlier version, with
no other parallel segment at all, is `isRupert_of_facets_edge_triN`. -/
theorem isRupert_of_facets_edge_tri (V : Finset ℝ³) (hgen : NoThreeCollinear V)
    (Q1 Q2 : Finset ℝ³) (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (h1f : IsFacet V Q1) (h2f : IsFacet V Q2)
    (v w : ℝ³) (hvw : v ≠ w) (hint : Q1 ∩ Q2 = {v, w})
    (hne1 : ∃ p ∈ Q1, p ∉ Q2) (hne2 : ∃ p ∈ Q2, p ∉ Q1)
    (hcard : Q1.card = 3 ∨ Q2.card = 3) (hpar : EdgePar V Q1 Q2 v w)
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ∉ Q2 ∧ xb ∉ Q1 ∧ ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ,
      (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
      (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → f2 y / f2 xa + f1 y / f1 xb < 1)
    (hsol : (interior (convexHull ℝ (V : Set ℝ³))).Nonempty) : IsRupert V := by
  have hvi : v ∈ Q1 ∩ Q2 := by rw [hint]; simp
  have hwi : w ∈ Q1 ∩ Q2 := by rw [hint]; simp
  exact isRupert_of_facets_edge_tieR V hgen Q1 Q2 h1V h2V h1f h2f v w hvw hint hne1 hne2
    (edgeTieR_of_tri h1V h2V (Finset.mem_inter.mp hvi).1 (Finset.mem_inter.mp hwi).1
      (Finset.mem_inter.mp hvi).2 (Finset.mem_inter.mp hwi).2 hvw hne1 hne2 hcard hpar) hin hsol

/-- **Lemma T over a vertex with a triangle face, middle and hidden parallels allowed**:
`TriGenTri` gives `TriGenTieR` (`TriGenTri.far`). -/
theorem TriGenTri.tieR {V Q1 Q2 : Finset ℝ³} {v : ℝ³} (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V)
    (hint : Q1 ∩ Q2 = {v}) (hcard : Q1.card = 3 ∨ Q2.card = 3) (h : TriGenTri V Q1 Q2 v) :
    TriGenTieR V Q1 Q2 v := fun f1 f2 z1 n1 z2 n2 e he e1 e2 =>
  ⟨(h f1 f2 z1 n1 z2 n2 e he e1 e2).1, fun p hp q hq hpq h1 h2 =>
    Or.inl (TriGenTri.far h1V h2V hint hcard h f1 f2 z1 n1 z2 n2 e he e1 e2 p hp q hq hpq h1 h2)⟩

end Minimality

end
