module

public import Minimality.TieRobust
public import Minimality.TriTie

@[expose] public section

/-!
# Lemma T at the tie, robust form: the oblique frame

The robust tie (`isRupert_of_tilted_tie`) in the oblique frame of
`isRupert_triShadow_gen`: apex `O`, far ends `a = O + A r1`, `b = O + B r2`,
`ρ = cross2 r1 r2 > 0`. Corner generators are positive multiples of `-J r1`
(side 1) or `J r2` (side 2); the test vectors are `m = -(r1 + r2)` and
`p = -r1` (`-r2` mirrored); the far determinant is `λ μ ρ A (r1 · (b - a))`
(mirrored `λ μ ρ B (r2 · (a - b))`), zero exactly at a right angle.
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
  simp [farDet, cross, ez, oblPt, cross2, PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem farDet_obl_neg (O r1 r2 : ℝ²) (A A0 B B1 c z0 z1 : ℝ) :
    farDet (cross (oblPt O r1 r2 0 B1 z1 - oblPt O r1 r2 0 B c) ez)
      (cross (oblPt O r1 r2 0 B c - oblPt O r1 r2 A 0 c) ez)
      (cross ez (oblPt O r1 r2 A0 0 z0 - oblPt O r1 r2 A 0 c))
      (oblPt O r1 r2 0 B c) (oblPt O r1 r2 A 0 c) ez =
      (A - A0) * (B - B1) * cross2 r1 r2 * B *
        (r2 0 * (A * r1 0 - B * r2 0) + r2 1 * (A * r1 1 - B * r2 1)) := by
  simp [farDet, cross, ez, oblPt, cross2, PiLp.inner_apply, Fin.sum_univ_three]; ring

set_option maxHeartbeats 16000000 in
/-- **Lemma T at the tie, robust form, in the oblique frame.** The setting of
`isRupert_triShadow_gen` in a same-sign sector (`t = -s`), at a tie of the far
depths (`cz m = dz n`), with every other corner strictly on the `s` side of
the tie, and a tilt `(α, β)` with `⟪b - a, α r1 + β r2⟫ ≠ 0` whose matching
angle (at `a` if positive, at `b` if negative) is not right: `V` is Rupert
(first-order free, though not unimodal). -/
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
    (hcase : (0 < ⟪oblPt 0 r1 r2 (-ca m) (cb n) 0, oblPt 0 r1 r2 α β 0⟫ ∧
        r1 0 * (cb n * r2 0 - ca m * r1 0) + r1 1 * (cb n * r2 1 - ca m * r1 1) ≠ 0) ∨
      (⟪oblPt 0 r1 r2 (-ca m) (cb n) 0, oblPt 0 r1 r2 α β 0⟫ < 0 ∧
        r2 0 * (ca m * r1 0 - cb n * r2 0) + r2 1 * (ca m * r1 1 - cb n * r2 1) ≠ 0)) :
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
  rcases hcase with ⟨hDp, hang⟩ | ⟨hDn, hang⟩
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

set_option maxHeartbeats 8000000 in
/-- **Lemma T at the tie, robust form, from chains.** The setting of
`isRupert_vertex_frame_tie` with the far depths tied, the apex off the tie
depth, and no right angle at the far ends: `V` (a solid) is Rupert. -/
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
      cz m = dz n ∧ z0 ≠ cz m ∧
      r1 0 * (cb n * r2 0 - ca m * r1 0) + r1 1 * (cb n * r2 1 - ca m * r1 1) ≠ 0 ∧
      r2 0 * (ca m * r1 0 - cb n * r2 0) + r2 1 * (ca m * r1 1 - cb n * r2 1) ≠ 0) :
    IsRupert V := by
  obtain ⟨m0, ca0, cz0, U1⟩ := hU1
  obtain ⟨n0, cb0, dz0, U2⟩ := hU2
  obtain ⟨m1, ca1, cz1, L1⟩ := hL1
  obtain ⟨n1, cb1, dz1, L2⟩ := hL2
  obtain ⟨htie0, hz0, hangA, hangB⟩ := hrob m0 ca0 cz0 n0 cb0 dz0 U1 U2
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
  obtain ⟨α, β, hα, hβ, hcase⟩ := exists_tie_tilt O r1 r2 (ca m) (cb n)
    (by rw [e1.1, e2.1]; exact hangA) (by rw [e1.1, e2.1]; exact hangB)
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

end Minimality

end
