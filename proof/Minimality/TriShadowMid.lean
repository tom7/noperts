module

public import Minimality.TriShadowChord

@[expose] public section

/-!
# Lemma T with a middle vertex on the far side (both faces with a vertical far edge)

`isRupert_triShadow_tilt` with one extra vertex `M` of `V` inserted in the cycle between the
far end `P = C1 m` of the first chain and the far end `Q = C2 n` of the second:
`C1, M, C2 reversed`.  The far side of the shadow is then the two segments `P M` and `M Q`,
one of which is parallel to the view line: `M` is the other end of the vertical far edge of
the first face (above or below `P`) or of the second face (above or below `Q`).  The tests
of the two new cycle edges are hypotheses (`TiltOK`), discharged by `TiltFarMid.lean`.

With `s z_Q < s z_M < s z_P` the sequence of depths along the cycle has one local maximum of
`s z`, on the first chain (the unimodality criterion of `tri_localMax_unique`).  This is the
sign-vector case analysis of FEWER-FACES-PROOFS.md Proposition 24.12 (the sectors
`(−, −, +)` etc. in which one vertical edge is a cycle edge) in the frame of Lemma T.
-/

namespace Minimality

open Finset Filter Topology
open scoped RealInnerProductSpace

/-- The cycle position `v` of the mixed cycle with a middle vertex `M`: `C1 v` for `v ≤ m`,
`M` at `m + 1`, else `C2 (m + n + 2 - v)`. -/
noncomputable def triPtM (O r1 r2 : ℝ²) (m n : ℕ) (ca cz cb dz : ℕ → ℝ) (M : ℝ³) (v : ℕ) : ℝ³ :=
  if v ≤ m then oblPt O r1 r2 (ca v) 0 (cz v)
  else if v = m + 1 then M
  else oblPt O r1 r2 0 (cb (m + n + 2 - v)) (dz (m + n + 2 - v))

/-- Its depth. -/
noncomputable def triZM (m n : ℕ) (cz dz : ℕ → ℝ) (zM : ℝ) (v : ℕ) : ℝ :=
  if v ≤ m then cz v else if v = m + 1 then zM else dz (m + n + 2 - v)

set_option maxHeartbeats 4000000 in
/-- **Lemma T in the oblique frame, general mixed tilt, with a middle vertex.**  The cycle is
`C1 0, …, C1 m, M, C2 n, …, C2 1` (then back to the apex).  The segments `C1 m → M` and
`M → C2 n` replace the far edge: their tests are the hypotheses `TiltOK` of `hVc`.  The
depths satisfy `s z_Q < s z_M < s z_P`. -/
theorem isRupert_triShadow_mid (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) {m n : ℕ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) (s : ℝ) (hs : s = 1 ∨ s = -1) {α β : ℝ} (hα : 0 < α)
    (hβ : 0 < β) (ca cz cb dz : ℕ → ℝ)
    (hca0 : ca 0 = 0) (hcb0 : cb 0 = 0) (hdz0 : dz 0 = cz 0)
    (hca : ∀ l, l < m → ca l < ca (l + 1)) (hcb : ∀ l, l < n → cb l < cb (l + 1))
    (V : Finset ℝ³) (aM bM zM : ℝ) (hMV : oblPt O r1 r2 aM bM zM ∈ V)
    (hM1 : ∀ l, l ≤ m → oblPt O r1 r2 aM bM zM ≠ oblPt O r1 r2 (ca l) 0 (cz l))
    (hM2 : ∀ l, l ≤ n → oblPt O r1 r2 aM bM zM ≠ oblPt O r1 r2 0 (cb l) (dz l))
    (hC1V : ∀ l, l ≤ m → oblPt O r1 r2 (ca l) 0 (cz l) ∈ V)
    (hC2V : ∀ l, l ≤ n → oblPt O r1 r2 0 (cb l) (dz l) ∈ V)
    (hVc : ∀ y ∈ V, ∃ a b z, y = oblPt O r1 r2 a b z ∧ 0 ≤ a ∧ 0 ≤ b ∧
      (TiltOK (ca m) 0 (cz m) aM bM zM a b z (-s * α) (s * β) ∨
        y = oblPt O r1 r2 (ca m) 0 (cz m) ∨ y = oblPt O r1 r2 aM bM zM) ∧
      (TiltOK aM bM zM 0 (cb n) (dz n) a b z (-s * α) (s * β) ∨
        y = oblPt O r1 r2 aM bM zM ∨ y = oblPt O r1 r2 0 (cb n) (dz n)) ∧
      (b = 0 → ∀ l, l < m → y ≠ oblPt O r1 r2 (ca l) 0 (cz l) →
        y ≠ oblPt O r1 r2 (ca (l + 1)) 0 (cz (l + 1)) →
        s * ((ca (l + 1) - ca l) * (z - cz l) - (cz (l + 1) - cz l) * (a - ca l)) < 0) ∧
      (a = 0 → ∀ l, l < n → y ≠ oblPt O r1 r2 0 (cb (l + 1)) (dz (l + 1)) →
        y ≠ oblPt O r1 r2 0 (cb l) (dz l) →
        s * ((cb l - cb (l + 1)) * (z - dz (l + 1)) - (dz l - dz (l + 1)) * (b - cb (l + 1))) < 0))
    (hPM : s * zM < s * cz m) (hMQ : s * dz n < s * zM) : IsRupert V := by
  have hNZ : NeZero (m + n + 2) := ⟨by omega⟩
  have hval : ∀ v : ℕ, v < m + n + 2 → ((v : ZMod (m + n + 2))).val = v := fun v hv => by
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
  set M : ℝ³ := oblPt O r1 r2 aM bM zM with hMdef
  set x : ZMod (m + n + 2) → ℝ³ := fun i => triPtM O r1 r2 m n ca cz cb dz M i.val with hx
  -- positions
  have hxC1 : ∀ v, v ≤ m → x (v : ZMod (m + n + 2)) = oblPt O r1 r2 (ca v) 0 (cz v) := by
    intro v hv; simp only [hx, hval v (by omega), triPtM, hv, ite_true]
  have hxM : x ((m + 1 : ℕ) : ZMod (m + n + 2)) = M := by
    simp only [hx, hval (m + 1) (by omega), triPtM, show ¬ m + 1 ≤ m by omega, ite_false,
      ite_true]
  have hxC2 : ∀ l, l < n → x ((m + n + 1 - l : ℕ) : ZMod (m + n + 2)) =
      oblPt O r1 r2 0 (cb (l + 1)) (dz (l + 1)) := by
    intro l hl
    simp only [hx, hval (m + n + 1 - l) (by omega), triPtM, show ¬ m + n + 1 - l ≤ m by omega,
      show ¬ m + n + 1 - l = m + 1 by omega, ite_false]
    rw [show m + n + 2 - (m + n + 1 - l) = l + 1 by omega]
  have hapex : oblPt O r1 r2 (ca 0) 0 (cz 0) = oblPt O r1 r2 0 (cb 0) (dz 0) := by
    rw [hca0, hcb0, hdz0]
  have hdepth : ∀ i : ZMod (m + n + 2), ⟪x i, ez⟫ = triZM m n cz dz zM i.val := by
    intro i; simp only [hx, triPtM, triZM]; split_ifs <;> exact inner_oblPt_ez _ _ _ _ _ _
  have hxinj : Function.Injective x := by
    have pos : ∀ w, w < m + n + 2 → (w ≤ m ∧ x w = oblPt O r1 r2 (ca w) 0 (cz w)) ∨
        (w = m + 1 ∧ x w = M) ∨
        (m + 2 ≤ w ∧ x w = oblPt O r1 r2 0 (cb (m + n + 2 - w)) (dz (m + n + 2 - w))) := by
      intro w hw
      by_cases h : w ≤ m
      · exact Or.inl ⟨h, hxC1 w h⟩
      by_cases h' : w = m + 1
      · subst h'; exact Or.inr (Or.inl ⟨rfl, hxM⟩)
      · refine Or.inr (Or.inr ⟨by omega, ?_⟩)
        have := hxC2 (m + n + 1 - w) (by omega)
        rwa [show m + n + 1 - (m + n + 1 - w) = w by omega,
          show m + n + 1 - w + 1 = m + n + 2 - w by omega] at this
    intro i j h
    obtain ⟨wi, hwi, rfl⟩ : ∃ w, w < m + n + 2 ∧ (w : ZMod (m + n + 2)) = i :=
      ⟨i.val, ZMod.val_lt i, ZMod.natCast_zmod_val i⟩
    obtain ⟨wj, hwj, rfl⟩ : ∃ w, w < m + n + 2 ∧ (w : ZMod (m + n + 2)) = j :=
      ⟨j.val, ZMod.val_lt j, ZMod.natCast_zmod_val j⟩
    suffices wi = wj by rw [this]
    rcases pos wi hwi with ⟨h1, e1⟩ | ⟨h1, e1⟩ | ⟨h1, e1⟩ <;>
      rcases pos wj hwj with ⟨h2, e2⟩ | ⟨h2, e2⟩ | ⟨h2, e2⟩ <;> rw [e1, e2] at h
    · have c := oblPt_inj hρ h
      rcases lt_trichotomy wi wj with l | l | l
      · exact absurd c.1 (hcam _ _ l h2).ne
      · exact l
      · exact absurd c.1 (hcam _ _ l h1).ne'
    · exact absurd h.symm (hM1 wi h1)
    · have c := oblPt_inj hρ h
      have := hcbm 0 (m + n + 2 - wj) (by omega) (by omega); rw [hcb0] at this; linarith [c.2.1]
    · exact absurd h (hM1 wj h2)
    · omega
    · exact absurd h (hM2 _ (by omega))
    · have c := oblPt_inj hρ h
      have := hcbm 0 (m + n + 2 - wi) (by omega) (by omega); rw [hcb0] at this; linarith [c.2.1]
    · exact absurd h.symm (hM2 _ (by omega))
    · have c := oblPt_inj hρ h
      rcases lt_trichotomy (m + n + 2 - wi) (m + n + 2 - wj) with l | l | l
      · exact absurd c.2.1 (hcbm _ _ l (by omega)).ne
      · omega
      · exact absurd c.2.1 (hcbm _ _ l (by omega)).ne'
  -- the tilt
  set v : ℝ³ := oblPt 0 r1 r2 (-s * α) (s * β) 0 with hv
  have key : ∀ {ap bp zp aq bq zq ay by' zy : ℝ},
      TiltOK ap bp zp aq bq zq ay by' zy (-s * α) (s * β) →
      TiltSign (oblPt O r1 r2 aq bq zq - oblPt O r1 r2 ap bp zp)
        (oblPt O r1 r2 ay by' zy - oblPt O r1 r2 ap bp zp) ez v :=
    fun h => tiltSign_obl O r1 r2 hρ (-s * α) (s * β) h
  have side1 : ∀ {ap aq zp zq ay zy : ℝ}, s * ((aq - ap) * (zy - zp) - (zq - zp) * (ay - ap)) < 0 →
      TiltOK ap 0 zp aq 0 zq ay 0 zy (-s * α) (s * β) := by
    intro ap aq zp zq ay zy h
    apply tiltOK_side1_on
    rcases hs with rfl | rfl
    · left; exact ⟨by linarith, by linarith⟩
    · right; exact ⟨by linarith, by linarith⟩
  have side2 : ∀ {bp bq zp zq by' zy : ℝ},
      s * ((bq - bp) * (zy - zp) - (zq - zp) * (by' - bp)) < 0 →
      TiltOK 0 bp zp 0 bq zq 0 by' zy (-s * α) (s * β) := by
    intro bp bq zp zq by' zy h
    apply tiltOK_side2_on
    rcases hs with rfl | rfl
    · right; exact ⟨by linarith, by linarith⟩
    · left; exact ⟨by linarith, by linarith⟩
  -- every test of Lemma 8.0
  have tests : ∀ y ∈ V, ∀ i : ZMod (m + n + 2), y ≠ x i → y ≠ x (i + 1) →
      TiltSign (x (i + 1) - x i) (y - x i) ez v := by
    intro y hy i hyi hyi1
    obtain ⟨a, b, z, rfl, ha, hb, hin1, hin2, hr1, hr2⟩ := hVc y hy
    obtain ⟨w, hwlt, rfl⟩ : ∃ w, w < m + n + 2 ∧ (w : ZMod (m + n + 2)) = i :=
      ⟨i.val, ZMod.val_lt i, ZMod.natCast_zmod_val i⟩
    have hsucc : ((w : ZMod (m + n + 2)) + 1) = ((w + 1 : ℕ) : ZMod (m + n + 2)) := by simp
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
    · -- the edge `P → M`
      have hwm : w = m := by omega
      subst w
      rw [hxC1 m le_rfl] at hyi ⊢
      rw [hxM] at hyi1 ⊢
      apply key
      rcases hin1 with hin | hin | hin
      · exact hin
      · exact absurd hin hyi
      · exact absurd hin hyi1
    rcases Nat.lt_or_ge w (m + 2) with h3 | h3
    · -- the edge `M → Q`
      have hwm : w = m + 1 := by omega
      subst w
      have e1 : x ((m + 1 + 1 : ℕ) : ZMod (m + n + 2)) = oblPt O r1 r2 0 (cb n) (dz n) := by
        rw [show m + 1 + 1 = m + n + 1 - (n - 1) by omega, hxC2 (n - 1) (by omega),
          show n - 1 + 1 = n by omega]
      rw [hxM] at hyi ⊢
      rw [e1] at hyi1 ⊢
      apply key
      rcases hin2 with hin | hin | hin
      · exact hin
      · exact absurd hin hyi
      · exact absurd hin hyi1
    · -- a segment of `C2` (inward), the last one ending at the apex
      obtain ⟨l, hln, rfl⟩ : ∃ l, l < n ∧ m + n + 1 - l = w := ⟨m + n + 1 - w, by omega, by omega⟩
      have e1 : x ((m + n + 1 - l + 1 : ℕ) : ZMod (m + n + 2)) = oblPt O r1 r2 0 (cb l) (dz l) := by
        rcases Nat.eq_zero_or_pos l with hl0 | hl0
        · subst hl0
          rw [show m + n + 1 - 0 + 1 = m + n + 2 by omega, ZMod.natCast_self, ← hapex,
            show (0 : ZMod (m + n + 2)) = ((0 : ℕ) : ZMod (m + n + 2)) by simp]
          exact hxC1 0 (Nat.zero_le _)
        · rw [show m + n + 1 - l + 1 = m + n + 1 - (l - 1) by omega, hxC2 (l - 1) (by omega),
            show l - 1 + 1 = l by omega]
      rw [hxC2 l hln] at hyi ⊢
      rw [e1] at hyi1 ⊢
      apply key
      rcases ha.lt_or_eq with ha | ha
      · exact tiltOK_side2_off (hcb _ hln) ha
      · subst ha; exact side2 (hr2 rfl _ hln hyi hyi1)
  have hxV : ∀ i, x i ∈ V := by
    intro i; simp only [hx, triPtM]; split_ifs with h h'
    · exact hC1V _ h
    · exact hMV
    · exact hC2V _ (by have := ZMod.val_lt i; omega)
  have hcyc : ∀ i j : ZMod (m + n + 2), j ≠ i → j ≠ i + 1 →
      TiltSign (x (i + 1) - x i) (x j - x i) ez v := by
    intro i j h1 h2
    exact tests (x j) (hxV j) i (fun h => h1 (hxinj h)) (fun h => h2 (hxinj h))
  have hrest : ∀ y ∈ V, (∀ j, y ≠ x j) → ∀ i,
      TiltSign (x (i + 1) - x i) (y - x i) ez v :=
    fun y hy hyx i => tests y hy i (hyx i) (hyx (i + 1))
  -- the depths are unimodal
  set Z : ZMod (m + n + 2) → ℝ := fun i => triZM m n cz dz zM i.val with hZ
  have hZpos : ∀ l, l < m + n + 2 → Z (l : ZMod (m + n + 2)) = triZM m n cz dz zM l := by
    intro l hl; simp only [hZ, hval l hl]
  have hZ1 : ∀ l, l ≤ m → Z (l : ZMod (m + n + 2)) = cz l := by
    intro l hl; rw [hZpos l (by omega)]; simp [triZM, hl]
  have hZM : Z ((m + 1 : ℕ) : ZMod (m + n + 2)) = zM := by
    rw [hZpos _ (by omega)]; simp [triZM]
  have hZ2 : ∀ l, m + 2 ≤ l → l ≤ m + n + 1 → Z (l : ZMod (m + n + 2)) = dz (m + n + 2 - l) := by
    intro l h1 h2; rw [hZpos l (by omega)]
    simp [triZM, show ¬ l ≤ m by omega, show ¬ l = m + 1 by omega]
  have hZk : Z ((m + n + 2 : ℕ) : ZMod (m + n + 2)) = dz 0 := by
    rw [ZMod.natCast_self, show (0 : ZMod (m + n + 2)) = ((0 : ℕ) : ZMod (m + n + 2)) by simp,
      hZ1 0 (Nat.zero_le _), hdz0]
  -- chain coordinates from `hVc`
  have coords1 : ∀ l, l ≤ m → ∀ j, j < m → oblPt O r1 r2 (ca l) 0 (cz l) ≠
      oblPt O r1 r2 (ca j) 0 (cz j) → oblPt O r1 r2 (ca l) 0 (cz l) ≠
      oblPt O r1 r2 (ca (j + 1)) 0 (cz (j + 1)) →
      s * ((ca (j + 1) - ca j) * (cz l - cz j) - (cz (j + 1) - cz j) * (ca l - ca j)) < 0 := by
    intro l hl j hj h1 h2
    obtain ⟨a, b, z, he, -, -, -, -, hr1, -⟩ := hVc _ (hC1V l hl)
    obtain ⟨ea, eb, ez'⟩ := oblPt_inj hρ he
    subst ea ez'
    exact hr1 eb.symm j hj (he ▸ h1) (he ▸ h2)
  have coords2 : ∀ l, l ≤ n → ∀ j, j < n → oblPt O r1 r2 0 (cb l) (dz l) ≠
      oblPt O r1 r2 0 (cb (j + 1)) (dz (j + 1)) → oblPt O r1 r2 0 (cb l) (dz l) ≠
      oblPt O r1 r2 0 (cb j) (dz j) →
      s * ((cb j - cb (j + 1)) * (dz l - dz (j + 1)) - (dz j - dz (j + 1)) * (cb l - cb (j + 1))) < 0 := by
    intro l hl j hj h1 h2
    obtain ⟨a, b, z, he, -, -, -, -, -, hr2⟩ := hVc _ (hC2V l hl)
    obtain ⟨ea, eb, ez'⟩ := oblPt_inj hρ he
    subst eb ez'
    exact hr2 ea.symm j hj (he ▸ h1) (he ▸ h2)
  have ne1 : ∀ i j, i ≤ m → j ≤ m → i ≠ j →
      oblPt O r1 r2 (ca i) 0 (cz i) ≠ oblPt O r1 r2 (ca j) 0 (cz j) := by
    intro i j hi hj hij he
    have := (oblPt_inj hρ he).1
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact absurd this (hcam i j h hj).ne
    · exact absurd this (hcam j i h hi).ne'
  have ne2 : ∀ i j, i ≤ n → j ≤ n → i ≠ j →
      oblPt O r1 r2 0 (cb i) (dz i) ≠ oblPt O r1 r2 0 (cb j) (dz j) := by
    intro i j hi hj hij he
    have := (oblPt_inj hρ he).2.1
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact absurd this (hcbm i j h hj).ne
    · exact absurd this (hcbm j i h hi).ne'
  -- the sequence lemma's hypotheses for `s Z`
  have hconcZ : ∀ l : ℕ, 1 ≤ l → l < m → min (s * Z ((l - 1 : ℕ) : ZMod (m + n + 2)))
      (s * Z ((l + 1 : ℕ) : ZMod (m + n + 2))) < s * Z (l : ZMod (m + n + 2)) := by
    intro l h1 h2
    rw [hZ1 _ (by omega), hZ1 _ (by omega), hZ1 _ (by omega)]
    have hc := coords1 (l + 1) (by omega) (l - 1) (by omega)
      (ne1 _ _ (by omega) (by omega) (by omega))
      (by rw [show l - 1 + 1 = l by omega]; exact ne1 _ _ (by omega) (by omega) (by omega))
    rw [show l - 1 + 1 = l by omega] at hc
    have d1 := hcam (l - 1) l (by omega) (by omega)
    have d2 := hcam l (l + 1) (by omega) (by omega)
    by_contra hcon
    push Not at hcon
    rw [le_min_iff] at hcon
    nlinarith [mul_nonneg (sub_nonneg.mpr d1.le) (sub_nonneg.mpr (hcon.2)),
      mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hcon.1) (sub_nonpos.mpr d2.le)]
  have hconvZ : ∀ l : ℕ, m + 2 ≤ l → l ≤ m + (n + 1) → s * Z (l : ZMod (m + n + 2)) <
      max (s * Z ((l - 1 : ℕ) : ZMod (m + n + 2))) (s * Z ((l + 1 : ℕ) : ZMod (m + n + 2))) := by
    intro l h1 h2
    rcases Nat.eq_or_lt_of_le h1 with hl | hl
    · -- the far end `Q` of the second chain: below the middle vertex
      subst hl
      rw [hZ2 (m + 2) le_rfl (by omega), show m + n + 2 - (m + 2) = n by omega,
        show m + 2 - 1 = m + 1 by omega, hZM]
      exact lt_max_of_lt_left hMQ
    · set j := m + n + 2 - l with hj
      have hj1 : 1 ≤ j := by omega
      have hjn : j < n := by omega
      rw [hZ2 l (by omega) h2, hZ2 (l - 1) (by omega) (by omega),
        show m + n + 2 - (l - 1) = j + 1 by omega]
      have hnext : Z ((l + 1 : ℕ) : ZMod (m + n + 2)) = dz (j - 1) := by
        rcases Nat.lt_or_ge l (m + n + 1) with hl' | hl'
        · rw [hZ2 (l + 1) (by omega) (by omega), show m + n + 2 - (l + 1) = j - 1 by omega]
        · rw [show l + 1 = m + n + 2 by omega, hZk, show j - 1 = 0 by omega]
      rw [hnext]
      have hc := coords2 (j - 1) (by omega) j hjn
        (ne2 _ _ (by omega) (by omega) (by omega)) (ne2 _ _ (by omega) (by omega) (by omega))
      have e1 := hcbm j (j + 1) (by omega) (by omega)
      have e2 := hcbm (j - 1) j (by omega) (by omega)
      by_contra hcon
      push Not at hcon
      rw [max_le_iff] at hcon
      nlinarith [mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr e1.le) (sub_nonpos.mpr hcon.2),
        mul_nonneg (sub_nonneg.mpr hcon.1) (sub_nonneg.mpr e2.le)]
  have hABZ : s * Z ((m + 1 : ℕ) : ZMod (m + n + 2)) < s * Z (m : ZMod (m + n + 2)) := by
    rw [hZM, hZ1 m le_rfl]; exact hPM
  have hT : TriSeq m (n + 1) s Z := by
    refine ⟨fun l hl => ?_, fun l hl => ?_, hABZ⟩
    · obtain ⟨h1, h2⟩ := Finset.mem_Ioo.mp hl
      exact min_lt_iff.mp (hconcZ l (by omega) h2)
    · obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hl
      exact lt_max_iff.mp (hconvZ l h1 h2)
  have hez : (ez : ℝ³) ≠ 0 := by
    intro h; have := congrArg (fun x : ℝ³ => x 2) h; simp [ez] at this
  exact isRupert_of_tilted_localMax V ez v hez (k := m + n + 2) (by omega) x hxV hcyc hrest s hs
    (TriSeq m (n + 1) s) (isOpen_triSeq m (n + 1) s) (fun z c hc hz => triSeq_smul hc hz)
    (by rw [show (fun i => ⟪x i, ez⟫) = Z from funext hdepth]; exact hT)
    (fun z hz => triSeq_localMax hm (by omega) hz)

end Minimality

end
