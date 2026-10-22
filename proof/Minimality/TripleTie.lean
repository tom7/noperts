module

public import Minimality.TieFrame
public import Minimality.ParallelOr
public import Minimality.BadViews

@[expose] public section

/-!
# The triple tie at a vertex view (`FEWER-FACES-PROOFS.md` §24, Theorem 24.5)

At the view along the line of two face planes `F1`, `F2` meeting in the single
vertex `v`, the shadow is the triangle `(p, a, b)` and the far vertices `xa`,
`xb` may tie with each other and with `v` (the triple tie). Theorem 24.5 decides
first-order passages there through sector tilts, breaking the ties
lexicographically by the tilt:

- if a face is one-sided (its other vertices all strictly on one side of the
  tied depth), a sector tilt hides that face and some tilt is unimodal (cases
  (a) and (b) of 24.5, any angle of the shadow triangle);
- if the shadow triangle has an obtuse angle at a far vertex, the mixed sector
  is unimodal near the corresponding end ray (case (c)).

`isRupert_triShadow_lex` is `isRupert_triShadow_gen` with the run hypotheses
asked only lexicographically (`LexS`: the depth, then the tilt). The frame
theorem `isRupert_vertex_frame_triple` picks the sector and the tilt; the rest
lifts it, as for `TriGenTieR`, to `TriGenTieT` (`TieHT`: the robust tie
condition, or the triple tie with a one-sided face or an obtuse far angle). With
a triangle face the triple tie is always settled (`TriGenPar.tieT`: only no
segment parallel to the view line is needed).
-/

namespace Minimality

open Finset Filter Topology
open scoped RealInnerProductSpace

/-- Lexicographic comparison in `s z`, then `s w`. -/
def LexS (s z w z' w' : ℝ) : Prop := s * z < s * z' ∨ (z = z' ∧ s * w < s * w')

theorem runSeq_add_const {K L c : ℕ} {s : ℝ} {z : ZMod K → ℝ} (k : ℝ)
    (h : RunSeq K L c s z) : RunSeq K L c s (fun i => z i + k) := by
  have m : ∀ a b : ZMod K, s * z a < s * z b → s * (z a + k) < s * (z b + k) := by
    intro a b hab; rw [mul_add, mul_add]; linarith
  exact ⟨fun l hl => (h.1 l hl).imp (m _ _) (m _ _), fun l hl => (h.2 l hl).imp (m _ _) (m _ _)⟩

/-- A small positive parameter keeps a strict sign. -/
theorem exists_small_pos {f0 f1 : ℝ} (h : 0 < f0) : ∃ ε : ℝ, 0 < ε ∧ 0 < f0 + ε * f1 := by
  have hd : 0 < |f1| + 1 := by positivity
  refine ⟨f0 / (|f1| + 1), by positivity, ?_⟩
  have h1 : -(f0 / (|f1| + 1) * |f1|) ≤ f0 / (|f1| + 1) * f1 := by
    have := neg_abs_le f1
    have h0 : 0 ≤ f0 / (|f1| + 1) := by positivity
    nlinarith
  have h2 : f0 / (|f1| + 1) * |f1| < f0 := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hd]; nlinarith [abs_nonneg f1]
  linarith

set_option maxHeartbeats 4000000 in
/-- **Lemma T at the triple tie, lexicographic runs.** As `isRupert_triShadow_gen`
(tilt `(-t α, s β)`, so the tilt values along the rays are `P = ⟪r1, d⟫`,
`Q = ⟪r2, d⟫`), with one of three run modes asked only lexicographically
(`LexS`: the depth, then the tilt value): the run is `C1` and `B` is below `A`
(or, with no `C2` corner, below the apex); or `C1` is a single edge and the run
is `C2` reversed with the apex (`t = -s`), `A` below a neighbour; or `C1` is a
single edge, the run is apex, `A`, `B` (`t = s`), `A` not the lowest. -/
theorem isRupert_triShadow_lex (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) {m n : ℕ}
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
    (P Q : ℝ)
    (hP : P = -t * α * (r1 0 * r1 0 + r1 1 * r1 1) + s * β * (r1 0 * r2 0 + r1 1 * r2 1))
    (hQ : Q = -t * α * (r1 0 * r2 0 + r1 1 * r2 1) + s * β * (r2 0 * r2 0 + r2 1 * r2 1))
    (hmodeL : ((t = s ∨ n = 1) ∧ (LexS s (dz n) (cb n * Q) (cz m) (ca m * P) ∨
        (n = 1 ∧ LexS s (dz n) (cb n * Q) (cz 0) 0))) ∨
      (m = 1 ∧ t = -s ∧ (LexS s (cz m) (ca m * P) (cz 0) 0 ∨ LexS s (cz m) (ca m * P) (dz n) (cb n * Q))) ∨
      (m = 1 ∧ t = s ∧ (LexS s (cz 0) 0 (cz m) (ca m * P) ∨ LexS s (dz n) (cb n * Q) (cz m) (ca m * P)))) :
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
  set Z : ZMod (m + n + 1) → ℝ := fun i => triZ m n cz dz i.val with hZ
  have hZpos : ∀ l, l < m + n + 1 → Z (l : ZMod (m + n + 1)) = triZ m n cz dz l := by
    intro l hl; simp only [hZ, hval l hl]
  have hZ1 : ∀ l, l ≤ m → Z (l : ZMod (m + n + 1)) = cz l := by
    intro l hl; rw [hZpos l (by omega)]; simp [triZ, hl]
  have hZ2 : ∀ l, m + 1 ≤ l → l ≤ m + n → Z (l : ZMod (m + n + 1)) = dz (m + n + 1 - l) := by
    intro l h1 h2; rw [hZpos l (by omega)]; simp [triZ, show ¬ l ≤ m by omega]
  have hZk : Z ((m + n + 1 : ℕ) : ZMod (m + n + 1)) = dz 0 := by
    rw [ZMod.natCast_self, show (0 : ZMod (m + n + 1)) = ((0 : ℕ) : ZMod (m + n + 1)) by simp,
      hZ1 0 (Nat.zero_le _), hdz0]
  -- chain coordinates from `hVc`
  have coords1 : ∀ l, l ≤ m → ∀ j, j < m → oblPt O r1 r2 (ca l) 0 (cz l) ≠
      oblPt O r1 r2 (ca j) 0 (cz j) → oblPt O r1 r2 (ca l) 0 (cz l) ≠
      oblPt O r1 r2 (ca (j + 1)) 0 (cz (j + 1)) →
      s * ((ca (j + 1) - ca j) * (cz l - cz j) - (cz (j + 1) - cz j) * (ca l - ca j)) < 0 := by
    intro l hl j hj h1 h2
    obtain ⟨a, b, z, he, -, -, -, hr1, -⟩ := hVc _ (hC1V l hl)
    obtain ⟨ea, eb, ez'⟩ := oblPt_inj hρ he
    subst ea ez'
    exact hr1 eb.symm j hj (he ▸ h1) (he ▸ h2)
  have coords2 : ∀ l, l ≤ n → ∀ j, j < n → oblPt O r1 r2 0 (cb l) (dz l) ≠
      oblPt O r1 r2 0 (cb (j + 1)) (dz (j + 1)) → oblPt O r1 r2 0 (cb l) (dz l) ≠
      oblPt O r1 r2 0 (cb j) (dz j) →
      t * ((cb j - cb (j + 1)) * (dz l - dz (j + 1)) - (dz j - dz (j + 1)) * (cb l - cb (j + 1))) < 0 := by
    intro l hl j hj h1 h2
    obtain ⟨a, b, z, he, -, -, -, -, hr2⟩ := hVc _ (hC2V l hl)
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
  -- the sequence lemma's hypotheses for `s Z` (strict, so they survive the tilt)
  have hconcZ : ∀ l : ℕ, 1 ≤ l → l < m → min (s * Z ((l - 1 : ℕ) : ZMod (m + n + 1)))
      (s * Z ((l + 1 : ℕ) : ZMod (m + n + 1))) < s * Z (l : ZMod (m + n + 1)) := by
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
  have hconvZ : ∀ l : ℕ, m + 2 ≤ l → l ≤ m + (n) → t * Z (l : ZMod (m + n + 1)) <
      max (t * Z ((l - 1 : ℕ) : ZMod (m + n + 1))) (t * Z ((l + 1 : ℕ) : ZMod (m + n + 1))) := by
    intro l h1 h2
    set j := m + n + 1 - l with hj
    have hj1 : 1 ≤ j := by omega
    have hjn : j < n := by omega
    rw [hZ2 l (by omega) h2, hZ2 (l - 1) (by omega) (by omega),
      show m + n + 1 - (l - 1) = j + 1 by omega]
    have hnext : Z ((l + 1 : ℕ) : ZMod (m + n + 1)) = dz (j - 1) := by
      rcases Nat.lt_or_ge l (m + n) with hl | hl
      · rw [hZ2 (l + 1) (by omega) (by omega), show m + n + 1 - (l + 1) = j - 1 by omega]
      · rw [show l + 1 = m + n + 1 by omega, hZk, show j - 1 = 0 by omega]
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
  have hw : ∀ v : ℕ, ((m + n + 1 + v : ℕ) : ZMod (m + n + 1)) = (v : ZMod (m + n + 1)) := by
    intro v; rw [Nat.cast_add, ZMod.natCast_self, zero_add]
  have hez : (ez : ℝ³) ≠ 0 := by
    intro h; have := congrArg (fun x : ℝ³ => x 2) h; simp [ez] at this
  -- the tilt values
  set W : ZMod (m + n + 1) → ℝ := fun i => triZ m n (fun l => ca l * P) (fun l => cb l * Q) i.val
    with hW
  have hWpos : ∀ l, l < m + n + 1 →
      W (l : ZMod (m + n + 1)) = triZ m n (fun l => ca l * P) (fun l => cb l * Q) l := by
    intro l hl; simp only [hW, hval l hl]
  have hW1 : ∀ l, l ≤ m → W (l : ZMod (m + n + 1)) = ca l * P := by
    intro l hl; rw [hWpos l (by omega)]; simp [triZ, hl]
  have hW2 : ∀ l, m + 1 ≤ l → l ≤ m + n → W (l : ZMod (m + n + 1)) = cb (m + n + 1 - l) * Q := by
    intro l h1 h2; rw [hWpos l (by omega)]; simp [triZ, show ¬ l ≤ m by omega]
  have hWk : W ((m + n + 1 : ℕ) : ZMod (m + n + 1)) = 0 := by
    rw [ZMod.natCast_self, show (0 : ZMod (m + n + 1)) = ((0 : ℕ) : ZMod (m + n + 1)) by simp,
      hW1 0 (Nat.zero_le _), hca0, zero_mul]
  -- lexicographic comparisons hold for all small tilts
  have evLex : ∀ i j : ZMod (m + n + 1), LexS s (Z i) (W i) (Z j) (W j) →
      ∀ᶠ δ in 𝓝[>] (0 : ℝ), s * (Z i + δ * W i) < s * (Z j + δ * W j) := by
    intro i j h
    have := eventually_pos_affine (A := s * Z j - s * Z i) (B := s * W j - s * W i) (by
      rcases h with h | ⟨h1, h2⟩
      · left; linarith
      · right; exact ⟨by rw [h1]; ring, by linarith⟩)
    filter_upwards [this] with δ hδ
    have e : s * (Z j + δ * W j) - s * (Z i + δ * W i) =
      (s * Z j - s * Z i) + δ * (s * W j - s * W i) := by ring
    linarith
  have evStrict : ∀ i j : ZMod (m + n + 1), s * Z i < s * Z j →
      ∀ᶠ δ in 𝓝[>] (0 : ℝ), s * (Z i + δ * W i) < s * (Z j + δ * W j) :=
    fun i j h => evLex i j (Or.inl h)
  -- the run of the sequence lemma, by the mode
  have hrun : ∃ L c : ℕ, L < m + n + 1 ∧
      ∀ᶠ δ in 𝓝[>] (0 : ℝ), RunSeq (m + n + 1) L c s (fun i => Z i + δ * W i) := by
    rcases hmodeL with ⟨hts, hAB⟩ | ⟨hm1, hts, hA⟩ | ⟨hm1, hts, hA⟩
    · -- the run is `C1`; `B` below `A` (or below the apex)
      refine ⟨m, 0, by omega, ?_⟩
      simp only [RunSeq, zero_add, Filter.eventually_and, Filter.eventually_all_finset]
      refine ⟨fun l hl => ?_, fun l hl => ?_⟩
      · obtain ⟨h1, h2⟩ := Finset.mem_Ioo.mp hl
        rcases Nat.lt_or_ge l (m + 2) with h3 | h3
        · have hl : l = m + 1 := by omega
          subst hl
          rcases hAB with hAB | ⟨hn1, hAB⟩
          · refine (evLex _ _ ?_).mono fun δ h => Or.inl h
            rw [show m + 1 - 1 = m by omega, hZ2 (m + 1) (by omega) (by omega), hZ1 m le_rfl,
              hW2 (m + 1) (by omega) (by omega), hW1 m le_rfl, show m + n + 1 - (m + 1) = n by omega]
            exact hAB
          · refine (evLex _ _ ?_).mono fun δ h => Or.inr h
            rw [hZ2 (m + 1) (by omega) (by omega), hW2 (m + 1) (by omega) (by omega),
              show m + 1 + 1 = m + n + 1 by omega, hZk, hWk, hdz0, show m + n + 1 - (m + 1) = n by omega]
            exact hAB
        · have hts' : t = s := by
            rcases hts with h | h
            · exact h
            · omega
          have := hconvZ l h3 (by omega)
          rw [hts', lt_max_iff] at this
          rcases this with h | h
          · exact (evStrict _ _ h).mono fun δ h => Or.inl h
          · exact (evStrict _ _ h).mono fun δ h => Or.inr h
      · obtain ⟨h1, h2⟩ := Finset.mem_Ioo.mp hl
        rcases min_lt_iff.mp (hconcZ l (by omega) h2) with h | h
        · exact (evStrict _ _ h).mono fun δ h => Or.inl h
        · exact (evStrict _ _ h).mono fun δ h => Or.inr h
    · -- `C1` a single edge, the run is `C2` reversed and the apex; `A` below a neighbour
      refine ⟨n, m + 1, by omega, ?_⟩
      simp only [RunSeq, Filter.eventually_and, Filter.eventually_all_finset]
      refine ⟨fun l hl => ?_, fun l hl => ?_⟩
      · obtain ⟨h1, h2⟩ := Finset.mem_Ioo.mp hl
        have hl : l = n + 1 := by omega
        subst hl
        rw [show m + 1 + (n + 1) = m + n + 1 + m by omega,
          show m + n + 1 + m - 1 = m + n + 1 + 0 by omega,
          show m + n + 1 + m + 1 = m + n + 1 + (m + 1) by omega, hw, hw, hw]
        rcases hA with hA | hA
        · refine (evLex _ _ ?_).mono fun δ h => Or.inl h
          rw [hZ1 m le_rfl, hW1 m le_rfl, hZ1 0 (by omega), hW1 0 (by omega), hca0, zero_mul]
          exact hA
        · refine (evLex _ _ ?_).mono fun δ h => Or.inr h
          rw [hZ1 m le_rfl, hW1 m le_rfl, hZ2 (m + 1) (by omega) (by omega),
            hW2 (m + 1) (by omega) (by omega), show m + n + 1 - (m + 1) = n by omega]
          exact hA
      · obtain ⟨h1, h2⟩ := Finset.mem_Ioo.mp hl
        have := hconvZ (m + 1 + l) (by omega) (by omega)
        rw [hts, lt_max_iff] at this
        rcases this with h | h
        · exact (evStrict _ _ (by linarith)).mono fun δ h => Or.inl h
        · exact (evStrict _ _ (by linarith)).mono fun δ h => Or.inr h
    · -- `C1` a single edge, the run is apex, `A`, `B`; `A` not the lowest
      refine ⟨m + 1, 0, by omega, ?_⟩
      simp only [RunSeq, zero_add, Filter.eventually_and, Filter.eventually_all_finset]
      refine ⟨fun l hl => ?_, fun l hl => ?_⟩
      · obtain ⟨h1, h2⟩ := Finset.mem_Ioo.mp hl
        have := hconvZ l (by omega) (by omega)
        rw [hts, lt_max_iff] at this
        rcases this with h | h
        · exact (evStrict _ _ h).mono fun δ h => Or.inl h
        · exact (evStrict _ _ h).mono fun δ h => Or.inr h
      · obtain ⟨h1, h2⟩ := Finset.mem_Ioo.mp hl
        have hl : l = m := by omega
        subst hl
        rcases hA with hA | hA
        · refine (evLex _ _ ?_).mono fun δ h => Or.inl h
          rw [show l - 1 = 0 by omega, hZ1 l le_rfl, hW1 l le_rfl, hZ1 0 (by omega),
            hW1 0 (by omega), hca0, zero_mul]
          exact hA
        · refine (evLex _ _ ?_).mono fun δ h => Or.inr h
          rw [hZ1 l le_rfl, hW1 l le_rfl, hZ2 (l + 1) (by omega) (by omega),
            hW2 (l + 1) (by omega) (by omega), show l + n + 1 - (l + 1) = n by omega]
          exact hA
  obtain ⟨L, c, hLK, hR⟩ := hrun
  -- the depths at the tilted views
  set c0 : ℝ := O 0 * (-t * α * r1 0 + s * β * r2 0) + O 1 * (-t * α * r1 1 + s * β * r2 1)
    with hc0
  have hobl : ∀ a b z : ℝ, ⟪oblPt O r1 r2 a b z, v⟫ = c0 + a * P + b * Q := by
    intro a b z
    simp only [hv, oblPt, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
    simp
    rw [hc0, hP, hQ]; ring
  have hdv : ∀ i : ZMod (m + n + 1), ⟪x i, v⟫ = c0 + W i := by
    intro i
    simp only [hx, hW, triPt, triZ]
    split_ifs with h
    · rw [hobl]; ring
    · rw [hobl]; ring
  have hdepth' : ∀ (ε : ℝ) (i : ZMod (m + n + 1)), ⟪x i, ez + ε • v⟫ = (Z i + ε * W i) + ε * c0 := by
    intro ε i
    rw [inner_add_right, real_inner_smul_right, hdepth, hdv]
    simp only [hZ]; ring
  refine isRupert_of_tilted_unimodal' V ez v hez (k := m + n + 1) (by omega) x hxV hcyc hrest
    (RunSeq (m + n + 1) L c s) (isOpen_runSeq _ _ _ s) (fun z k hk hz => runSeq_smul hk hz) ?_ ?_
  · filter_upwards [hR] with ε hε
    have e : (fun i => ⟪x i, ez + ε • v⟫) = fun i => (Z i + ε * W i) + ε * c0 :=
      funext (hdepth' ε)
    rw [e]
    exact runSeq_add_const (ε * c0) hε
  · intro z hz hP'
    rcases hs with rfl | rfl
    · exact isCyclicUnimodal_of_localMax_unique (by omega) z hz
        (fun a b h1 h2 h3 h4 => runSeq_localMax hLK hP' a b (by linarith) (by linarith)
          (by linarith) (by linarith))
    · exact isCyclicUnimodal_of_localMin_unique (by omega) z hz
        (fun a b h1 h2 h3 h4 => runSeq_localMax hLK hP' a b (by linarith) (by linarith)
          (by linarith) (by linarith))

/-! ### The frame theorem at the triple tie -/

/-- A face (oblique `(t, z)` coordinates, apex `(0, z0)`, far end `(A, z0)` at the
tied depth) is *one-sided*: every other point strictly on one side of the tied depth. -/
def OneSidedF (Q : ℝ → ℝ → Prop) (z0 A : ℝ) : Prop :=
  ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
    ∀ a z, Q a z → ¬ (a = 0 ∧ z = z0) → ¬ (a = A ∧ z = z0) → σ * z < σ * z0

/-- **The settled triple tie** (Theorem 24.5): the far ends `(A, zA)`, `(B, zB)` tie
with the apex depth `z0`, and a face is one-sided (cases (a), (b)) or the shadow
triangle `(O, O + A r1, O + B r2)` is obtuse at a far corner (case (c)). -/
def TripleF (Q1 Q2 : ℝ → ℝ → Prop) (z0 : ℝ) (r1 r2 : ℝ²) (A zA B zB : ℝ) : Prop :=
  zA = z0 ∧ zB = z0 ∧ (OneSidedF Q1 z0 A ∨ OneSidedF Q2 z0 B ∨
    0 < r1 0 * (B * r2 0 - A * r1 0) + r1 1 * (B * r2 1 - A * r1 1) ∨
    0 < r2 0 * (A * r1 0 - B * r2 0) + r2 1 * (A * r1 1 - B * r2 1))

/-- A chain on the empty side of a one-sided face is a single edge. -/
theorem ChainOK.eq_one_of_oneSided {Q : ℝ → ℝ → Prop} {z0 σ : ℝ} {m : ℕ} {ca cz : ℕ → ℝ}
    (C : ChainOK Q z0 σ m ca cz) (hfar : cz m = z0)
    (h : ∀ a z, Q a z → ¬ (a = 0 ∧ z = z0) → ¬ (a = ca m ∧ z = z0) → σ * z < σ * z0) :
    m = 1 := by
  by_contra hm
  have hm2 : 2 ≤ m := by have := C.one_le; omega
  have hc := gt_min_ends_of_conc (f := fun l => σ * cz l) (m := m) C.conc 1 (by omega) (by omega)
  simp only [C.start.2, hfar, min_self] at hc
  have h0 := C.inc 0 (by omega)
  rw [C.start.1] at h0
  have key : ∀ j, 2 ≤ j → j ≤ m → ca 1 < ca j := by
    intro j hj hjm
    induction j, hj using Nat.le_induction with
    | base => exact C.inc 1 (by omega)
    | succ j hj ih => exact lt_trans (ih (by omega)) (C.inc j (by omega))
  have := h (ca 1) (cz 1) (C.mem 1 (by omega)) (fun e => by linarith [e.1])
    (fun e => by linarith [e.1, key m hm2 le_rfl])
  linarith

theorem normSq_pos_of_cross2 {r1 r2 : ℝ²} (h : 0 < cross2 r1 r2) :
    0 < r1 0 * r1 0 + r1 1 * r1 1 ∧ 0 < r2 0 * r2 0 + r2 1 * r2 1 := by
  constructor
  · by_contra hc; push Not at hc
    have a0 : r1 0 = 0 := by nlinarith [mul_self_nonneg (r1 0), mul_self_nonneg (r1 1)]
    have a1 : r1 1 = 0 := by nlinarith [mul_self_nonneg (r1 0), mul_self_nonneg (r1 1)]
    simp [cross2, a0, a1] at h
  · by_contra hc; push Not at hc
    have a0 : r2 0 = 0 := by nlinarith [mul_self_nonneg (r2 0), mul_self_nonneg (r2 1)]
    have a1 : r2 1 = 0 := by nlinarith [mul_self_nonneg (r2 0), mul_self_nonneg (r2 1)]
    simp [cross2, a0, a1] at h

set_option maxHeartbeats 4000000 in
/-- **Theorem 24.5 in the frame** (`FEWER-FACES-PROOFS.md` §24): the setting of
`isRupert_vertex_frame_tie` at the triple tie (both far ends at the apex depth),
with a one-sided face or a far corner of the shadow triangle obtuse
(`TripleF`): `V` is Rupert. A one-sided face is hidden by a sector tilt and the
other face's chain is chosen by the angle at the apex side; an obtuse far
corner makes the mixed sector unimodal near the matching end ray. -/
theorem isRupert_vertex_frame_triple (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2)
    (Q1 Q2 : ℝ → ℝ → Prop) {z0 : ℝ} {m0 n0 : ℕ} {ca0 cz0 cb0 dz0 : ℕ → ℝ}
    (U1 : ChainOK Q1 z0 1 m0 ca0 cz0) (hL1 : ∃ m ca cz, ChainOK Q1 z0 (-1) m ca cz)
    (U2 : ChainOK Q2 z0 1 n0 cb0 dz0) (hL2 : ∃ m ca cz, ChainOK Q2 z0 (-1) m ca cz)
    (hap1 : ∀ z, Q1 0 z → z = z0) (hap2 : ∀ z, Q2 0 z → z = z0)
    (hpos1 : ∀ a z, Q1 a z → 0 ≤ a) (hpos2 : ∀ b z, Q2 b z → 0 ≤ b)
    (V : Finset ℝ³)
    (hV1 : ∀ a z, Q1 a z → oblPt O r1 r2 a 0 z ∈ V) (hV2 : ∀ b z, Q2 b z → oblPt O r1 r2 0 b z ∈ V)
    (hVc : ∀ y ∈ V, ∃ a b z, y = oblPt O r1 r2 a b z ∧
      ((b = 0 ∧ Q1 a z) ∨ (a = 0 ∧ Q2 b z) ∨ (0 < a ∧ 0 < b ∧
        ∀ m ca cz n cb dz, ChainOK Q1 z0 1 m ca cz → ChainOK Q2 z0 1 n cb dz →
          a * cb n + b * ca m < ca m * cb n)))
    (htri : TripleF Q1 Q2 z0 r1 r2 (ca0 m0) (cz0 m0) (cb0 n0) (dz0 n0)) :
    IsRupert V := by
  obtain ⟨m1, ca1, cz1, L1⟩ := hL1
  obtain ⟨n1, cb1, dz1, L2⟩ := hL2
  obtain ⟨hzA, hzB, hok⟩ := htri
  have hA0 := U1.far_pos
  have hB0 := U2.far_pos
  -- the core, for signs `s`, `t`, a tilt `(α, β)` and chains `C1` (sign `s`), `C2` (sign `-t`)
  have core : ∀ (s : ℝ), (s = 1 ∨ s = -1) → ∀ (t : ℝ), (t = 1 ∨ t = -1) → ∀ {α β : ℝ},
      0 < α → 0 < β → ∀ (Pt Qt : ℝ),
      Pt = -t * α * (r1 0 * r1 0 + r1 1 * r1 1) + s * β * (r1 0 * r2 0 + r1 1 * r2 1) →
      Qt = -t * α * (r1 0 * r2 0 + r1 1 * r2 1) + s * β * (r2 0 * r2 0 + r2 1 * r2 1) →
      ∀ {m n : ℕ} {ca cz cb dz : ℕ → ℝ},
      ChainOK Q1 z0 s m ca cz → ChainOK Q2 z0 (-t) n cb dz →
      (((t = s ∨ n = 1) ∧ (LexS s (dz n) (cb n * Qt) (cz m) (ca m * Pt) ∨
          (n = 1 ∧ LexS s (dz n) (cb n * Qt) (cz 0) 0))) ∨
        (m = 1 ∧ t = -s ∧ (LexS s (cz m) (ca m * Pt) (cz 0) 0 ∨
          LexS s (cz m) (ca m * Pt) (dz n) (cb n * Qt))) ∨
        (m = 1 ∧ t = s ∧ (LexS s (cz 0) 0 (cz m) (ca m * Pt) ∨
          LexS s (dz n) (cb n * Qt) (cz m) (ca m * Pt)))) →
      ca m = ca0 m0 → cb n = cb0 n0 → IsRupert V := by
    intro s hs t ht α β hα hβ Pt Qt hPt hQt m n ca cz cb dz C1 C2 hmode ea eb
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
    refine isRupert_triShadow_lex O r1 r2 hρ C1.one_le C2.one_le s hs t ht hα hβ ca cz cb dz
      c10.1 c20.1 (by rw [c10.2, c20.2]) C1.inc C2.inc V (fun l hl => hV1 _ _ (C1.mem l hl))
      (fun l hl => hV2 _ _ (C2.mem l hl)) ?_ Pt Qt hPt hQt hmode
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
      rw [ea, eb]; exact hin m0 ca0 cz0 n0 cb0 dz0 U1 U2
  have ch1 : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ∃ m ca cz, ChainOK Q1 z0 σ m ca cz := by
    rintro σ (rfl | rfl)
    exacts [⟨m0, ca0, cz0, U1⟩, ⟨m1, ca1, cz1, L1⟩]
  have ch2 : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ∃ n cb dz, ChainOK Q2 z0 σ n cb dz := by
    rintro σ (rfl | rfl)
    exacts [⟨n0, cb0, dz0, U2⟩, ⟨n1, cb1, dz1, L2⟩]
  have neg : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → (-σ = 1 ∨ -σ = -1) := by
    rintro σ (rfl | rfl) <;> norm_num
  have hnn : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → -(-σ) = σ := fun σ _ => neg_neg σ
  obtain ⟨hN1, hN2⟩ := normSq_pos_of_cross2 hρ
  rcases hok with ⟨σ, hσ, hmid⟩ | ⟨σ, hσ, hmid⟩ | hobA | hobB
  · -- face 1 one-sided: hide it (`s = σ`, `C1` a single edge)
    obtain ⟨m, ca, cz, C1⟩ := ch1 σ hσ
    have e1 := C1.far_eq U1
    have hm1 : m = 1 := C1.eq_one_of_oneSided (by rw [e1.2, hzA])
      (fun a z hq h0 h1 => hmid a z hq h0 (by rw [← e1.1]; exact h1))
    by_cases hcase : ca0 m0 * (r1 0 * r2 0 + r1 1 * r2 1) < cb0 n0 * (r2 0 * r2 0 + r2 1 * r2 1)
    · -- `C2` the other bump (`t = -σ`), `A` below `B`
      obtain ⟨α, hα, hpos⟩ := exists_small_pos
        (f0 := cb0 n0 * (r2 0 * r2 0 + r2 1 * r2 1) - ca0 m0 * (r1 0 * r2 0 + r1 1 * r2 1))
        (f1 := cb0 n0 * (r1 0 * r2 0 + r1 1 * r2 1) - ca0 m0 * (r1 0 * r1 0 + r1 1 * r1 1))
        (by linarith)
      obtain ⟨n, cb, dz, C2⟩ := ch2 σ hσ
      have e2 := C2.far_eq U2
      refine core σ hσ (-σ) (neg σ hσ) hα one_pos _ _ rfl rfl C1 (by rw [neg_neg]; exact C2)
        (Or.inr (Or.inl ⟨hm1, rfl, Or.inr (Or.inr ⟨by rw [e1.2, e2.2, hzA, hzB], ?_⟩)⟩)) e1.1 e2.1
      rw [e1.1, e2.1]
      rcases hσ with rfl | rfl
      · nlinarith
      · nlinarith
    · -- `C2` the other dip (`t = σ`), `A` above the apex
      push Not at hcase
      have hAg : 0 < ca0 m0 * (r1 0 * r2 0 + r1 1 * r2 1) := lt_of_lt_of_le (mul_pos hB0 hN2) hcase
      obtain ⟨α, hα, hpos⟩ := exists_small_pos
        (f0 := ca0 m0 * (r1 0 * r2 0 + r1 1 * r2 1))
        (f1 := -(ca0 m0 * (r1 0 * r1 0 + r1 1 * r1 1))) hAg
      obtain ⟨n, cb, dz, C2⟩ := ch2 (-σ) (neg σ hσ)
      have e2 := C2.far_eq U2
      refine core σ hσ σ hσ hα one_pos _ _ rfl rfl C1 C2
        (Or.inr (Or.inr ⟨hm1, rfl, Or.inl (Or.inr ⟨by rw [C1.start.2, e1.2, hzA], ?_⟩)⟩)) e1.1 e2.1
      rw [e1.1]
      rcases hσ with rfl | rfl
      · nlinarith
      · nlinarith
  · -- face 2 one-sided: hide it (`t = -σ`, `C2` a single edge)
    obtain ⟨n, cb, dz, C2⟩ := ch2 σ hσ
    have e2 := C2.far_eq U2
    have hn1 : n = 1 := C2.eq_one_of_oneSided (by rw [e2.2, hzB])
      (fun a z hq h0 h1 => hmid a z hq h0 (by rw [← e2.1]; exact h1))
    have C2' : ChainOK Q2 z0 (-(-σ)) n cb dz := by rw [neg_neg]; exact C2
    by_cases hcase : cb0 n0 * (r1 0 * r2 0 + r1 1 * r2 1) < ca0 m0 * (r1 0 * r1 0 + r1 1 * r1 1)
    · -- `s = σ`: `B` below `A`
      obtain ⟨β, hβ, hpos⟩ := exists_small_pos
        (f0 := ca0 m0 * (r1 0 * r1 0 + r1 1 * r1 1) - cb0 n0 * (r1 0 * r2 0 + r1 1 * r2 1))
        (f1 := ca0 m0 * (r1 0 * r2 0 + r1 1 * r2 1) - cb0 n0 * (r2 0 * r2 0 + r2 1 * r2 1))
        (by linarith)
      obtain ⟨m, ca, cz, C1⟩ := ch1 σ hσ
      have e1 := C1.far_eq U1
      refine core σ hσ (-σ) (neg σ hσ) one_pos hβ _ _ rfl rfl C1 C2'
        (Or.inl ⟨Or.inr hn1, Or.inl (Or.inr ⟨by rw [e1.2, e2.2, hzA, hzB], ?_⟩)⟩) e1.1 e2.1
      rw [e1.1, e2.1]
      rcases hσ with rfl | rfl
      · nlinarith
      · nlinarith
    · -- `s = -σ`: `B` below the apex
      push Not at hcase
      have hBg : 0 < cb0 n0 * (r1 0 * r2 0 + r1 1 * r2 1) := lt_of_lt_of_le (mul_pos hA0 hN1) hcase
      obtain ⟨β, hβ, hpos⟩ := exists_small_pos
        (f0 := cb0 n0 * (r1 0 * r2 0 + r1 1 * r2 1))
        (f1 := -(cb0 n0 * (r2 0 * r2 0 + r2 1 * r2 1))) hBg
      obtain ⟨m, ca, cz, C1⟩ := ch1 (-σ) (neg σ hσ)
      have e1 := C1.far_eq U1
      refine core (-σ) (neg σ hσ) (-σ) (neg σ hσ) one_pos hβ _ _ rfl rfl C1 C2'
        (Or.inl ⟨Or.inl rfl, Or.inr ⟨hn1, Or.inr ⟨by rw [C1.start.2, e2.2, hzB], ?_⟩⟩⟩) e1.1 e2.1
      rw [e2.1]
      rcases hσ with rfl | rfl
      · nlinarith
      · nlinarith
  · -- obtuse at `a`: the mixed sector near the end ray `-r1`
    obtain ⟨β, hβ, hpos⟩ := exists_small_pos
      (f1 := ca0 m0 * (r1 0 * r2 0 + r1 1 * r2 1) - cb0 n0 * (r2 0 * r2 0 + r2 1 * r2 1)) hobA
    obtain ⟨n, cb, dz, C2⟩ := ch2 (-1) (Or.inr rfl)
    have e2 := C2.far_eq U2
    refine core 1 (Or.inl rfl) 1 (Or.inl rfl) one_pos hβ _ _ rfl rfl U1 C2
      (Or.inl ⟨Or.inl rfl, Or.inl (Or.inr ⟨by rw [e2.2, hzA, hzB], ?_⟩)⟩) rfl e2.1
    rw [e2.1]
    nlinarith
  · -- obtuse at `b`: the mixed sector near the end ray `r2`
    obtain ⟨α, hα, hpos⟩ := exists_small_pos
      (f1 := cb0 n0 * (r1 0 * r2 0 + r1 1 * r2 1) - ca0 m0 * (r1 0 * r1 0 + r1 1 * r1 1)) hobB
    obtain ⟨n, cb, dz, C2⟩ := ch2 (-1) (Or.inr rfl)
    have e2 := C2.far_eq U2
    refine core 1 (Or.inl rfl) 1 (Or.inl rfl) hα one_pos _ _ rfl rfl U1 C2
      (Or.inl ⟨Or.inl rfl, Or.inl (Or.inr ⟨by rw [e2.2, hzA, hzB], ?_⟩)⟩) rfl e2.1
    rw [e2.1]
    nlinarith

/-- **Lemma T at a vertex from chains, the triple tie allowed.** As
`isRupert_vertex_frame_tieR`, with a fourth way out at the far ends: the settled
triple tie (`TripleF`, Theorem 24.5). The robust way out (the far ends tied, the
apex off their depth) is asked only under a flag `Rb`, which supplies the solid
`V`. -/
theorem isRupert_vertex_frame_tieW {Rb : Prop} (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2)
    (Q1 Q2 : ℝ → ℝ → Prop) {z0 : ℝ}
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
    (hsol : Rb → (interior (convexHull ℝ (V : Set ℝ³))).Nonempty)
    (hfarT : ∀ m ca cz n cb dz, ChainOK Q1 z0 1 m ca cz → ChainOK Q2 z0 1 n cb dz →
      cz m ≠ dz n ∨ VTie Q1 Q2 z0 (ca m) (cz m) (cb n) (dz n) ∨
      (Rb ∧ cz m = dz n ∧ z0 ≠ cz m) ∨ TripleF Q1 Q2 z0 r1 r2 (ca m) (cz m) (cb n) (dz n)) :
    IsRupert V := by
  obtain ⟨m0, ca0, cz0, U1⟩ := hU1
  obtain ⟨n0, cb0, dz0, U2⟩ := hU2
  have far : ∀ m ca cz n cb dz, ChainOK Q1 z0 1 m ca cz → ChainOK Q2 z0 1 n cb dz →
      ca m = ca0 m0 ∧ cz m = cz0 m0 ∧ cb n = cb0 n0 ∧ dz n = dz0 n0 :=
    fun m ca cz n cb dz C1 C2 => ⟨(C1.far_eq U1).1, (C1.far_eq U1).2, (C2.far_eq U2).1,
      (C2.far_eq U2).2⟩
  rcases hfarT m0 ca0 cz0 n0 cb0 dz0 U1 U2 with h | h | ⟨hRb, h⟩ | h
  · refine isRupert_vertex_frame_tie O r1 r2 hρ Q1 Q2 ⟨m0, ca0, cz0, U1⟩ hL1 ⟨n0, cb0, dz0, U2⟩ hL2
      hap1 hap2 hpos1 hpos2 V hV1 hV2 hVc fun m ca cz n cb dz C1 C2 => ?_
    obtain ⟨e1, e2, e3, e4⟩ := far m ca cz n cb dz C1 C2
    rw [e2, e4]; exact Or.inl h
  · refine isRupert_vertex_frame_tie O r1 r2 hρ Q1 Q2 ⟨m0, ca0, cz0, U1⟩ hL1 ⟨n0, cb0, dz0, U2⟩ hL2
      hap1 hap2 hpos1 hpos2 V hV1 hV2 hVc fun m ca cz n cb dz C1 C2 => ?_
    obtain ⟨e1, e2, e3, e4⟩ := far m ca cz n cb dz C1 C2
    rw [e1, e2, e3, e4]; exact Or.inr h
  · refine isRupert_vertex_frame_tieR O r1 r2 hρ Q1 Q2 ⟨m0, ca0, cz0, U1⟩ hL1 ⟨n0, cb0, dz0, U2⟩ hL2
      hap1 hap2 hpos1 hpos2 V hV1 hV2 hVc (hsol hRb) fun m ca cz n cb dz C1 C2 => ?_
    obtain ⟨e1, e2, e3, e4⟩ := far m ca cz n cb dz C1 C2
    rw [e2, e4]; exact Or.inr (Or.inr h)
  · exact isRupert_vertex_frame_triple O r1 r2 hρ Q1 Q2 U1 hL1 U2 hL2 hap1 hap2 hpos1 hpos2 V
      hV1 hV2 hVc h

/-! ### Faces as point sets -/

/-- A face `Q` with shared vertex `v` and far end `p` is *one-sided* in the heights `h`:
every other point strictly on one side of the height of `v`. -/
def OneSided (Q : Finset ℝ³) (v p : ℝ³) (h : ℝ³ → ℝ) : Prop :=
  ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ x ∈ Q, x ≠ v → x ≠ p → σ * h x < σ * h v

/-- **The tie condition with the triple tie settled** (Theorem 24.5): `TieHR`, or the
far ends and the shared vertex at one height with a one-sided face or an obtuse
angle of the triangle `(v, p, q)` at `p` or at `q`. Fails only at the triple tie
with both faces two-sided and both far angles at most right (case (c) of 24.5 with
acute or right far angles). -/
def TieHT (Q1 Q2 : Finset ℝ³) (v p q : ℝ³) (h : ℝ³ → ℝ) : Prop :=
  TieHR Q1 Q2 v p q h ∨ (h p = h q ∧ h v = h p ∧
    (OneSided Q1 v p h ∨ OneSided Q2 v q h ∨ 0 < ⟪q - p, p - v⟫ ∨ 0 < ⟪p - q, q - v⟫))

/-- `TieHT` with the robust way out only under the flag `Rb` (the form the lifting
theorems use; `Rb = False` needs no solid). -/
def TieHW (Rb : Prop) (Q1 Q2 : Finset ℝ³) (v p q : ℝ³) (h : ℝ³ → ℝ) : Prop :=
  TieH Q1 Q2 v p q h ∨ (Rb ∧ h p = h q ∧ h v ≠ h p) ∨ (h p = h q ∧ h v = h p ∧
    (OneSided Q1 v p h ∨ OneSided Q2 v q h ∨ 0 < ⟪q - p, p - v⟫ ∨ 0 < ⟪p - q, q - v⟫))

theorem TieHR.toT {Q1 Q2 : Finset ℝ³} {v p q : ℝ³} {h : ℝ³ → ℝ} (H : TieHR Q1 Q2 v p q h) :
    TieHT Q1 Q2 v p q h := Or.inl H

theorem TieHT.toW {Q1 Q2 : Finset ℝ³} {v p q : ℝ³} {h : ℝ³ → ℝ} (H : TieHT Q1 Q2 v p q h) :
    TieHW True Q1 Q2 v p q h := by
  rcases H with (H | H) | H
  · exact Or.inl H
  · exact Or.inr (Or.inl ⟨trivial, H⟩)
  · exact Or.inr (Or.inr H)

theorem TieHW.swap {Rb : Prop} {Q1 Q2 : Finset ℝ³} {v p q : ℝ³} {h : ℝ³ → ℝ}
    (H : TieHW Rb Q1 Q2 v p q h) : TieHW Rb Q2 Q1 v q p h := by
  rcases H with H | ⟨hRb, e, hv⟩ | ⟨e, ev, hok⟩
  · exact Or.inl H.swap
  · exact Or.inr (Or.inl ⟨hRb, e.symm, by rw [← e]; exact hv⟩)
  · refine Or.inr (Or.inr ⟨e.symm, ev.trans e, ?_⟩)
    rcases hok with h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))

theorem OneSided.map {Q : Finset ℝ³} {v p : ℝ³} {h h' : ℝ³ → ℝ} (g : ℝ³ → ℝ³)
    {r : ℝ} (hr : 0 < r) (hh : ∀ x, h' (g x) = h x / r) (H : OneSided Q v p h) [DecidableEq ℝ³] :
    OneSided (Q.image g) (g v) (g p) h' := by
  obtain ⟨σ, hσ, H⟩ := H
  refine ⟨σ, hσ, fun y hy hyv hyp => ?_⟩
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  rw [hh, hh, show σ * (h x / r) = (σ * h x) / r by ring, show σ * (h v / r) = (σ * h v) / r by ring]
  exact div_lt_div_of_pos_right (H x hx (fun e => hyv (by rw [e])) (fun e => hyp (by rw [e]))) hr

theorem TieHW.map {Rb : Prop} {Q1 Q2 : Finset ℝ³} {v p q : ℝ³} {h h' : ℝ³ → ℝ} (g : ℝ³ → ℝ³)
    (hg : Function.Injective g) {r : ℝ} (hr : 0 < r) (hh : ∀ x, h' (g x) = h x / r)
    (H : TieHW Rb Q1 Q2 v p q h) [DecidableEq ℝ³] (hlin : ∀ x y, g (x - y) = g x - g y)
    (hip : ∀ x y, ⟪g x, g y⟫ = ⟪x, y⟫) :
    TieHW Rb (Q1.image g) (Q2.image g) (g v) (g p) (g q) h' := by
  rcases H with H | ⟨hRb, e, hv⟩ | ⟨e, ev, hok⟩
  · exact Or.inl (H.map g hg hr hh)
  · refine Or.inr (Or.inl ⟨hRb, by rw [hh, hh, e], fun e' => hv ?_⟩)
    rw [hh, hh] at e'
    have := congrArg (· * r) e'; simp only [div_mul_cancel₀ _ hr.ne'] at this; exact this
  · refine Or.inr (Or.inr ⟨by rw [hh, hh, e], by rw [hh, hh, ev], ?_⟩)
    rcases hok with H | H | H | H
    · exact Or.inl (H.map g hr hh)
    · exact Or.inr (Or.inl (H.map g hr hh))
    · exact Or.inr (Or.inr (Or.inl (by rw [← hlin, ← hlin, hip]; exact H)))
    · exact Or.inr (Or.inr (Or.inr (by rw [← hlin, ← hlin, hip]; exact H)))

/-- The angle at the far end `p` of the tied triangle in oblique coordinates. -/
theorem angle_frame1 {O r1 r2 : ℝ²} {p q v : ℝ³} {A B c z0 : ℝ} (hp : p = oblPt O r1 r2 A 0 c)
    (hq : q = oblPt O r1 r2 0 B c) (hv : v = oblPt O r1 r2 0 0 z0) :
    ⟪q - p, p - v⟫ = A * (r1 0 * (B * r2 0 - A * r1 0) + r1 1 * (B * r2 1 - A * r1 1)) := by
  rw [hp, hq, hv]; exact inner_obl_angle1 O r1 r2 A B c z0

/-- The angle at the far end `q`. -/
theorem angle_frame2 {O r1 r2 : ℝ²} {p q v : ℝ³} {A B c z0 : ℝ} (hp : p = oblPt O r1 r2 A 0 c)
    (hq : q = oblPt O r1 r2 0 B c) (hv : v = oblPt O r1 r2 0 0 z0) :
    ⟪p - q, q - v⟫ = B * (r2 0 * (A * r1 0 - B * r2 0) + r2 1 * (A * r1 1 - B * r2 1)) := by
  rw [show p - q = -(q - p) by abel, inner_neg_left, hp, hq, hv, inner_obl_angle2, neg_neg]

set_option maxHeartbeats 4000000 in
/-- **Lemma T over a vertex at the tie, in frame coordinates, the triple tie allowed.** As
`isRupert_vertex_coords`, with the far depths allowed to tie when a far end or
the shared vertex is a strict top or bottom of its face (`VTie`).  The points of `V` are
`oblPt O r1 r2 (a p) (b p) (p 2)`; `Q1` lies on the ray `b = 0`, `Q2` on `a = 0`,
every other point at `a, b > 0`. -/
theorem isRupert_vertex_coords_tieW {Rb : Prop} (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (V Q1 Q2 : Finset ℝ³)
    (v : ℝ³) (a b : ℝ³ → ℝ) (hy : ∀ p ∈ V, p = oblPt O r1 r2 (a p) (b p) (p 2))
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hint : Q1 ∩ Q2 = {v})
    (hb1 : ∀ p ∈ Q1, b p = 0) (hb1' : ∀ p ∈ V, p ∉ Q1 → 0 < b p)
    (ha2 : ∀ p ∈ Q2, a p = 0) (ha2' : ∀ p ∈ V, p ∉ Q2 → 0 < a p)
    (hne1 : ∃ p ∈ Q1, p ≠ v) (hne2 : ∃ p ∈ Q2, p ≠ v)
    (hcol : ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V, p ≠ q → p ≠ r → q ≠ r → ∀ c : ℝ, r - p ≠ c • (q - p))
    (hinj : Set.InjOn (fun p => (a p, b p)) (V : Set ℝ³))
    (hfarZ : ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, a p' ≤ a p) → (∀ q' ∈ Q2, b q' ≤ b q) →
      TieHW Rb Q1 Q2 v p q (fun x => x 2))
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ≠ v ∧ xb ≠ v ∧
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → a y / a xa + b y / b xb < 1)
    (hsol : Rb → (interior (convexHull ℝ (V : Set ℝ³))).Nonempty) : IsRupert V := by
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
    apply exists_chainOK S1 (v 2) (by rw [hS1, Finset.mem_image]; exact ⟨v, hv1, by rw [hav]⟩)
    · intro q hq hne
      obtain ⟨p, hp, e1, e2⟩ := ofS1 q.1 q.2 hq
      rw [← e1]; refine apos p hp (fun h => hne ?_)
      exact Prod.ext (by show q.1 = 0; rw [← e1, h, hav]) (by show q.2 = v 2; rw [← e2, h])
    · obtain ⟨p, hp, hpv⟩ := hne1
      refine ⟨(a p, p 2), Finset.mem_image_of_mem _ hp, fun h => ?_⟩
      have := congrArg Prod.fst h; simp only at this; linarith [apos p hp hpv]
    · intro q hq q' hq' e
      obtain ⟨p, hp, e1, e2⟩ := ofS1 q.1 q.2 hq
      obtain ⟨p', hp', e1', e2'⟩ := ofS1 q'.1 q'.2 hq'
      have : p = p' := hinj (h1V hp) (h1V hp') (by simp only [Prod.mk.injEq]; rw [hb1 p hp, hb1 p' hp']; exact ⟨by rw [e1, e1']; exact e, rfl⟩)
      exact Prod.ext e (by rw [← e2, ← e2', this])
    · intro q hq q' hq' q'' hq'' n1 n2 n3
      obtain ⟨p, hp, e1, e2⟩ := ofS1 q.1 q.2 hq
      obtain ⟨p', hp', e1', e2'⟩ := ofS1 q'.1 q'.2 hq'
      obtain ⟨p'', hp'', e1'', e2''⟩ := ofS1 q''.1 q''.2 hq''
      have d : ∀ {r r' : ℝ × ℝ} {u u' : ℝ³}, r ≠ r' → a u = r.1 → u 2 = r.2 → a u' = r'.1 →
          u' 2 = r'.2 → u ≠ u' := by
        intro r r' u u' h h1 h2 h1' h2' hu; apply h
        exact Prod.ext (by rw [← h1, ← h1', hu]) (by rw [← h2, ← h2', hu])
      have hne : a p ≠ a p' := fun h => d n1 e1 e2 e1' e2'
        (hinj (h1V hp) (h1V hp') (by simp only [Prod.mk.injEq]; rw [hb1 p hp, hb1 p' hp']; exact ⟨h, rfl⟩))
      have := orient_ne_of_frame1 (O := O) (r1 := r1) (r2 := r2) (zi := p 2) (zj := p' 2) (zk := p'' 2)
        (ak := a p'') hne (by
          intro c; rw [← pt1 p hp, ← pt1 p' hp', ← pt1 p'' hp'']
          exact hcol p (h1V hp) p' (h1V hp') p'' (h1V hp'') (d n1 e1 e2 e1' e2')
            (d n2 e1 e2 e1'' e2'') (d n3 e1' e2' e1'' e2'') c)
      unfold orient2 at this; rwa [e1, e2, e1', e2', e1'', e2''] at this
    · exact hs
  have chains2 : ∀ s : ℝ, (s = 1 ∨ s = -1) → ∃ m ca cz, ChainOK (fun x z => (x, z) ∈ S2) (v 2) s m ca cz := by
    intro s hs
    apply exists_chainOK S2 (v 2) (by rw [hS2, Finset.mem_image]; exact ⟨v, hv2, by rw [hbv]⟩)
    · intro q hq hne
      obtain ⟨p, hp, e1, e2⟩ := ofS2 q.1 q.2 hq
      rw [← e1]; refine bpos p hp (fun h => hne ?_)
      exact Prod.ext (by show q.1 = 0; rw [← e1, h, hbv]) (by show q.2 = v 2; rw [← e2, h])
    · obtain ⟨p, hp, hpv⟩ := hne2
      refine ⟨(b p, p 2), Finset.mem_image_of_mem _ hp, fun h => ?_⟩
      have := congrArg Prod.fst h; simp only at this; linarith [bpos p hp hpv]
    · intro q hq q' hq' e
      obtain ⟨p, hp, e1, e2⟩ := ofS2 q.1 q.2 hq
      obtain ⟨p', hp', e1', e2'⟩ := ofS2 q'.1 q'.2 hq'
      have : p = p' := hinj (h2V hp) (h2V hp') (by simp only [Prod.mk.injEq]; rw [ha2 p hp, ha2 p' hp']; exact ⟨rfl, by rw [e1, e1']; exact e⟩)
      exact Prod.ext e (by rw [← e2, ← e2', this])
    · intro q hq q' hq' q'' hq'' n1 n2 n3
      obtain ⟨p, hp, e1, e2⟩ := ofS2 q.1 q.2 hq
      obtain ⟨p', hp', e1', e2'⟩ := ofS2 q'.1 q'.2 hq'
      obtain ⟨p'', hp'', e1'', e2''⟩ := ofS2 q''.1 q''.2 hq''
      have d : ∀ {r r' : ℝ × ℝ} {u u' : ℝ³}, r ≠ r' → b u = r.1 → u 2 = r.2 → b u' = r'.1 →
          u' 2 = r'.2 → u ≠ u' := by
        intro r r' u u' h h1 h2 h1' h2' hu; apply h
        exact Prod.ext (by rw [← h1, ← h1', hu]) (by rw [← h2, ← h2', hu])
      have hne : b p ≠ b p' := fun h => d n1 e1 e2 e1' e2'
        (hinj (h2V hp) (h2V hp') (by simp only [Prod.mk.injEq]; rw [ha2 p hp, ha2 p' hp']; exact ⟨rfl, h⟩))
      have := orient_ne_of_frame2 (O := O) (r1 := r1) (r2 := r2) (zi := p 2) (zj := p' 2) (zk := p'' 2)
        (bk := b p'') hne (by
          intro c; rw [← pt2 p hp, ← pt2 p' hp', ← pt2 p'' hp'']
          exact hcol p (h2V hp) p' (h2V hp') p'' (h2V hp'') (d n1 e1 e2 e1' e2')
            (d n2 e1 e2 e1'' e2'') (d n3 e1' e2' e1'' e2'') c)
      unfold orient2 at this; rwa [e1, e2, e1', e2', e1'', e2''] at this
    · exact hs
  obtain ⟨xa, hxa, xb, hxb, hxav, hxbv, hin'⟩ := hin
  refine isRupert_vertex_frame_tieW O r1 r2 hρ (fun x z => (x, z) ∈ S1) (fun x z => (x, z) ∈ S2)
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
    rcases hfarZ p hp q hq hpq pmax qmax with hT | ⟨hRb, hpq2, hvp⟩ | ⟨hpq2, hvp, hok⟩
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
    · right; right; left
      simp only at hpq2 hvp
      exact ⟨hRb, by rw [← e2, ← f2]; exact hpq2, by rw [← e2]; exact hvp⟩
    · -- the triple tie (Theorem 24.5)
      right; right; right
      simp only at hpq2 hvp
      have hap : 0 < a p := by rw [e1]; exact C1.far_pos
      have hbq : 0 < b q := by rw [f1]; exact C2.far_pos
      have hv' : v = oblPt O r1 r2 0 0 (v 2) := by conv_lhs => rw [pt1 v hv1, hav]
      have hq' : q = oblPt O r1 r2 0 (b q) (p 2) := by rw [hpq2]; exact pt2 q hq
      refine ⟨by rw [← e2, hvp], by rw [← f2, ← hpq2, hvp], ?_⟩
      rcases hok with ⟨σ, hσ, h⟩ | ⟨σ, hσ, h⟩ | h | h
      · refine Or.inl ⟨σ, hσ, fun x z hxz h0 hA => ?_⟩
        obtain ⟨p', hp', g1, g2⟩ := ofS1 x z hxz
        rw [← g2]
        exact h p' hp' (fun e => h0 ⟨by rw [← g1, e, hav], by rw [← g2, e]⟩)
          (fun e => hA ⟨by rw [← g1, e, e1], by rw [← g2, e, ← hvp]⟩)
      · refine Or.inr (Or.inl ⟨σ, hσ, fun x z hxz h0 hB => ?_⟩)
        obtain ⟨q', hq'', g1, g2⟩ := ofS2 x z hxz
        rw [← g2]
        exact h q' hq'' (fun e => h0 ⟨by rw [← g1, e, hbv], by rw [← g2, e]⟩)
          (fun e => hB ⟨by rw [← g1, e, f1], by rw [← g2, e, ← hpq2, ← hvp]⟩)
      · rw [angle_frame1 (pt1 p hp) hq' hv'] at h
        rw [← e1, ← f1]; exact Or.inr (Or.inr (Or.inl (pos_of_mul_pos_right h hap.le)))
      · rw [angle_frame2 (pt1 p hp) hq' hv'] at h
        rw [← e1, ← f1]; exact Or.inr (Or.inr (Or.inr (pos_of_mul_pos_right h hbq.le)))

/-- General position at the line of the planes of two facets with the far
condition `TieHW Rb` (the lifting form). -/
def TriGenTieW (Rb : Prop) (V Q1 Q2 : Finset ℝ³) (v : ℝ³) : Prop :=
  ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ, (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
    (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
    ∀ e : ℝ³, e ≠ 0 → f1 (v + e) = 0 → f2 (v + e) = 0 →
      (∀ p ∈ V, ∀ q ∈ V, p ≠ q → ∀ c : ℝ, q - p ≠ c • e) ∧
      ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, f2 p ≤ f2 p') → (∀ q' ∈ Q2, f1 q ≤ f1 q') →
        TieHW Rb Q1 Q2 v p q (fun x => ⟪x, e⟫)

/-- **General position for Lemma T at the line of the planes of two facets, the
triple tie settled** (Theorem 24.5): as `TriGenTieR`, with `TieHT` at the far
ends. What it excludes beyond a parallel segment: the far ends and the shared
vertex at one depth along the line, both faces two-sided there, and the shadow
triangle neither obtuse at `p` nor at `q` (case (c) of 24.5 with both far
angles acute or right). -/
def TriGenTieT (V Q1 Q2 : Finset ℝ³) (v : ℝ³) : Prop :=
  ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ, (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
    (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
    ∀ e : ℝ³, e ≠ 0 → f1 (v + e) = 0 → f2 (v + e) = 0 →
      (∀ p ∈ V, ∀ q ∈ V, p ≠ q → ∀ c : ℝ, q - p ≠ c • e) ∧
      ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, f2 p ≤ f2 p') → (∀ q' ∈ Q2, f1 q ≤ f1 q') →
        TieHT Q1 Q2 v p q (fun x => ⟪x, e⟫)

theorem TriGenTieR.toT {V Q1 Q2 : Finset ℝ³} {v : ℝ³} (h : TriGenTieR V Q1 Q2 v) :
    TriGenTieT V Q1 Q2 v := by
  intro f1 f2 z1 n1 z2 n2 e he e1 e2
  obtain ⟨hpar, hfar⟩ := h f1 f2 z1 n1 z2 n2 e he e1 e2
  exact ⟨hpar, fun p hp q hq hpq h1 h2 => (hfar p hp q hq hpq h1 h2).toT⟩

theorem TriGenTieT.toW {V Q1 Q2 : Finset ℝ³} {v : ℝ³} (h : TriGenTieT V Q1 Q2 v) :
    TriGenTieW True V Q1 Q2 v := by
  intro f1 f2 z1 n1 z2 n2 e he e1 e2
  obtain ⟨hpar, hfar⟩ := h f1 f2 z1 n1 z2 n2 e he e1 e2
  exact ⟨hpar, fun p hp q hq hpq h1 h2 => (hfar p hp q hq hpq h1 h2).toW⟩

set_option maxHeartbeats 4000000 in
/-- **Lemma T over a vertex at the tie, the planes vertical.**  `Q1`, `Q2` are facets
(functionals `f1`, `f2`) meeting in `v`, both planes containing the vertical line
through `v`. -/
theorem isRupert_facets_vertex_vertical_tieW {Rb : Prop} (V Q1 Q2 : Finset ℝ³) (v : ℝ³)
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hint : Q1 ∩ Q2 = {v}) (f1 f2 : ℝ³ →ᵃ[ℝ] ℝ)
    (z1 : ∀ p ∈ Q1, f1 p = 0) (n1 : ∀ p ∈ V, p ∉ Q1 → f1 p < 0)
    (z2 : ∀ p ∈ Q2, f2 p = 0) (n2 : ∀ p ∈ V, p ∉ Q2 → f2 p < 0)
    (e1 : f1 (v + ez) = 0) (e2 : f2 (v + ez) = 0)
    (hne1 : ∃ p ∈ Q1, p ≠ v) (hne2 : ∃ p ∈ Q2, p ≠ v)
    (hcol : ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V, p ≠ q → p ≠ r → q ≠ r → ∀ c : ℝ, r - p ≠ c • (q - p))
    (hpar : ∀ p ∈ V, ∀ q ∈ V, p ≠ q → p 0 ≠ q 0 ∨ p 1 ≠ q 1)
    (hfarZ : ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, f2 p ≤ f2 p') → (∀ q' ∈ Q2, f1 q ≤ f1 q') →
      TieHW Rb Q1 Q2 v p q (fun x => x 2))
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ≠ v ∧ xb ≠ v ∧
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → f2 y / f2 xa + f1 y / f1 xb < 1)
    (hsol : Rb → (interior (convexHull ℝ (V : Set ℝ³))).Nonempty) : IsRupert V := by
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
  have hinj : Set.InjOn (fun p => (a p, b p)) (V : Set ℝ³) := by
    intro p hp q hq e
    simp only [Prod.mk.injEq] at e
    by_contra hpq
    obtain ⟨c0, c1⟩ := hxy p; obtain ⟨d0, d1⟩ := hxy q
    rw [e.1, e.2] at c0 c1
    rcases hpar p hp q hq hpq with h | h <;> apply h <;> linarith
  have hfar' : ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, a p' ≤ a p) → (∀ q' ∈ Q2, b q' ≤ b q) →
      TieHW Rb Q1 Q2 v p q (fun x => x 2) := fun p hp q hq hpq h1 h2 =>
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
    refine isRupert_vertex_coords_tieW O r2 r1 hpos' V Q2 Q1 v b a (fun p _ => by rw [swap]; exact hy p)
      h2V h1V (by rw [Finset.inter_comm]; exact hint) ha2 ha2' hb1 hb1' ⟨p2, hp2, hp2v⟩
      ⟨p1, hp1, hp1v⟩ hcol ?_
      (fun p hp q hq hpq h1 h2 => (hfar' q hq p hp (Ne.symm hpq) h2 h1).swap) ?_ hsol
    · intro p hp q hq e
      simp only [Prod.mk.injEq] at e
      exact hinj hp hq (by simp only [Prod.mk.injEq]; exact ⟨e.2, e.1⟩)
    · obtain ⟨xa, hxa, xb, hxb, hxav, hxbv, h⟩ := hin'
      exact ⟨xb, hxb, xa, hxa, hxbv, hxav, fun y hy hy2 hy1 => by
        rw [add_comm]; exact h y hy hy1 hy2⟩
  · exact isRupert_vertex_coords_tieW O r1 r2 hpos V Q1 Q2 v a b (fun p _ => hy p) h1V h2V hint
      hb1 hb1' ha2 ha2' ⟨p1, hp1, hp1v⟩ ⟨p2, hp2, hp2v⟩ hcol hinj hfar' hin' hsol

set_option maxHeartbeats 4000000 in
/-- **Lemma T over a vertex at the tie** for two facets `Q1`, `Q2` (functionals `f1`, `f2`)
meeting in `v`, viewed along the line `v + ℝ e` of their planes: no three points
collinear, no segment parallel to `e`, distinct depths along `e` at the far ends
(the point of `Q1` where `f2` is least, that of `Q2` where `f1` is least), and
every point off both facets inside the shadow triangle of `v` and some `xa ∈
Q1`, `xb ∈ Q2`. -/
theorem isRupert_facets_vertex_tieW {Rb : Prop} (V Q1 Q2 : Finset ℝ³) (v : ℝ³)
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hint : Q1 ∩ Q2 = {v}) (f1 f2 : ℝ³ →ᵃ[ℝ] ℝ)
    (z1 : ∀ p ∈ Q1, f1 p = 0) (n1 : ∀ p ∈ V, p ∉ Q1 → f1 p < 0)
    (z2 : ∀ p ∈ Q2, f2 p = 0) (n2 : ∀ p ∈ V, p ∉ Q2 → f2 p < 0)
    (e : ℝ³) (he : e ≠ 0) (e1 : f1 (v + e) = 0) (e2 : f2 (v + e) = 0)
    (hne1 : ∃ p ∈ Q1, p ≠ v) (hne2 : ∃ p ∈ Q2, p ≠ v)
    (hcol : ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V, p ≠ q → p ≠ r → q ≠ r → ∀ c : ℝ, r - p ≠ c • (q - p))
    (hpar : ∀ p ∈ V, ∀ q ∈ V, p ≠ q → ∀ c : ℝ, q - p ≠ c • e)
    (hfarZ : ∀ p ∈ Q1, ∀ q ∈ Q2, p ≠ q → (∀ p' ∈ Q1, f2 p ≤ f2 p') → (∀ q' ∈ Q2, f1 q ≤ f1 q') →
      TieHW Rb Q1 Q2 v p q (fun x => ⟪x, e⟫))
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ≠ v ∧ xb ≠ v ∧
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → f2 y / f2 xa + f1 y / f1 xb < 1)
    (hsol : Rb → (interior (convexHull ℝ (V : Set ℝ³))).Nonempty) : IsRupert V := by
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
  refine isRupert_facets_vertex_vertical_tieW (V.image g) (Q1.image g) (Q2.image g) (g v)
    (Finset.image_subset_image h1V) (Finset.image_subset_image h2V)
    (by rw [← Finset.image_inter _ _ hginj, hint, Finset.image_singleton]) F1 F2
    (allg Q1 _ (fun p hp => by rw [tF1]; exact z1 p hp))
    (allg V _ (fun p hp hq => by rw [tF1]; exact n1 p hp (fun h => hq ((memg Q1 p).mpr h))))
    (allg Q2 _ (fun p hp => by rw [tF2]; exact z2 p hp))
    (allg V _ (fun p hp hq => by rw [tF2]; exact n2 p hp (fun h => hq ((memg Q2 p).mpr h))))
    (tz f1 (z1 v hv1) e1) (tz f2 (z2 v hv2) e2) ?_ ?_ ?_ ?_ ?_ ?_ (fun hb => interior_convexHull_image_rot hR (hsol hb))
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
    intro hpq
    by_contra h; push Not at h
    obtain ⟨h0, h1⟩ := h
    apply hpar p hp q hq (fun e => hpq (by rw [e])) ((g (q - p)) 2 / r)
    apply hginj
    rw [map_smul, hRe]
    ext k; fin_cases k
    · simp [ez, map_sub]; linarith
    · simp [ez, map_sub]; linarith
    · simp [ez]; field_simp
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
theorem isRupert_of_facets_vertex_tieW {Rb : Prop} (V : Finset ℝ³) (hgen : NoThreeCollinear V)
    (Q1 Q2 : Finset ℝ³) (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (h1f : IsFacet V Q1) (h2f : IsFacet V Q2)
    (v : ℝ³) (hint : Q1 ∩ Q2 = {v}) (hne1 : ∃ p ∈ Q1, p ≠ v) (hne2 : ∃ p ∈ Q2, p ≠ v)
    (hT : TriGenTieW Rb V Q1 Q2 v)
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ≠ v ∧ xb ≠ v ∧ ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ,
      (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
      (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → f2 y / f2 xa + f1 y / f1 xb < 1)
    (hsol : Rb → (interior (convexHull ℝ (V : Set ℝ³))).Nonempty) : IsRupert V := by
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
  refine isRupert_facets_vertex_tieW V Q1 Q2 v h1V h2V hint f1 f2 z1 n1 z2 n2 e hne e1 e2
    ⟨p1, hp1, hp1v⟩ ⟨p2, hp2, hp2v⟩ ?_ hpar hfarZ
    ⟨xa, hxa, xb, hxb, hxav, hxbv, hin' f1 f2 z1 n1 z2 n2⟩ hsol
  exact hgen


set_option maxHeartbeats 4000000 in
/-- **Lemma T over a vertex, the triple tie settled, facet form**: as
`isRupert_of_facets_vertex_tieR`, with `TriGenTieT` (Theorem 24.5 at the triple tie). -/
theorem isRupert_of_facets_vertex_tieT (V : Finset ℝ³) (hgen : NoThreeCollinear V)
    (Q1 Q2 : Finset ℝ³) (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (h1f : IsFacet V Q1) (h2f : IsFacet V Q2)
    (v : ℝ³) (hint : Q1 ∩ Q2 = {v}) (hne1 : ∃ p ∈ Q1, p ≠ v) (hne2 : ∃ p ∈ Q2, p ≠ v)
    (hT : TriGenTieT V Q1 Q2 v)
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ≠ v ∧ xb ≠ v ∧ ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ,
      (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
      (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → f2 y / f2 xa + f1 y / f1 xb < 1)
    (hsol : (interior (convexHull ℝ (V : Set ℝ³))).Nonempty) : IsRupert V :=
  isRupert_of_facets_vertex_tieW V hgen Q1 Q2 h1V h2V h1f h2f v hint hne1 hne2 hT.toW hin
    (fun _ => hsol)

/-! ### A triangle face settles the triple tie -/

/-- `k × u = 0` for `k = n × e` and `u` orthogonal to `n` and `e`. -/
theorem cross_cross_perp_zero {n e u : ℝ³} (h1 : ⟪n, u⟫ = 0) (h2 : ⟪e, u⟫ = 0) :
    cross (cross n e) u = 0 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial] at h1 h2
  ext j; fin_cases j
  · simp [cross]; linear_combination e 0 * h1 - n 0 * h2
  · simp [cross]; linear_combination e 1 * h1 - n 1 * h2
  · simp [cross]; linear_combination e 2 * h1 - n 2 * h2

/-- Two vectors orthogonal to two independent vectors are parallel. -/
theorem exists_smul_of_perp2 {n e u w : ℝ³} (hk : cross n e ≠ 0) (hu : u ≠ 0)
    (h1 : ⟪n, u⟫ = 0) (h2 : ⟪e, u⟫ = 0) (h3 : ⟪n, w⟫ = 0) (h4 : ⟪e, w⟫ = 0) :
    ∃ c : ℝ, w = c • u := by
  obtain ⟨l1, hl1⟩ : ∃ l, u = l • cross n e :=
    ⟨_, eq_smul_of_cross_eq_zero hk (cross_cross_perp_zero h1 h2)⟩
  obtain ⟨l2, hl2⟩ : ∃ l, w = l • cross n e :=
    ⟨_, eq_smul_of_cross_eq_zero hk (cross_cross_perp_zero h3 h4)⟩
  have hl : l1 ≠ 0 := fun h0 => hu (by rw [hl1, h0, zero_smul])
  exact ⟨l2 / l1, by rw [hl2, hl1, smul_smul, div_mul_cancel₀ _ hl]⟩

/-- A triangle face `Q ∋ v, p` (no three points collinear) whose plane contains the
line `v + ℝ e`, with `p` at the depth of `v` along `e`: its third vertex is off that
depth, so the face is one-sided. -/
theorem oneSided_tri {V Q : Finset ℝ³} (hgen : NoThreeCollinear V) (hQV : Q ⊆ V)
    (hQ : Q.card = 3) {v p : ℝ³} (hv : v ∈ Q) (hp : p ∈ Q) (hvp : v ≠ p) (f : ℝ³ →ᵃ[ℝ] ℝ)
    (hz : ∀ x ∈ Q, f x = 0) {y : ℝ³} (hy : f y ≠ 0) {e : ℝ³} (he : e ≠ 0)
    (hfe : f (v + e) = 0) (hpv : ⟪p, e⟫ = ⟪v, e⟫) : OneSided Q v p (fun x => ⟪x, e⟫) := by
  classical
  obtain ⟨w, hw⟩ := exists_third_of_card_three hQ hv hp hvp
  obtain ⟨w', hw'Q, hw'v, hw'p⟩ : ∃ x ∈ Q, x ≠ v ∧ x ≠ p := by
    by_contra hc
    push Not at hc
    have hsub : Q ⊆ {v, p} := fun x hx => by
      by_cases h1 : x = v
      · simp [h1]
      · simp [hc x hx h1]
    have := Finset.card_le_card hsub
    rw [Finset.card_pair hvp] at this
    omega
  have only : ∀ x ∈ Q, x ≠ v → x ≠ p → x = w' := by
    intro x hx h1 h2
    rcases hw x hx with h | h | h
    · exact absurd h h1
    · exact absurd h h2
    · rcases hw w' hw'Q with h' | h' | h'
      · exact absurd h' hw'v
      · exact absurd h' hw'p
      · rw [h, h']
  have hne : ⟪w', e⟫ ≠ ⟪v, e⟫ := by
    intro hwe
    obtain ⟨K, α, β, γ, hf⟩ := affine_xyz f
    set n : ℝ³ := !₂[α, β, γ] with hn
    have hdiff : ∀ x x', f x' - f x = ⟪n, x' - x⟫ := by
      intro x x'
      rw [hf, hf]
      simp [hn, PiLp.inner_apply, Fin.sum_univ_three]; ring
    have hfv := hz v hv
    have h1 : ⟪n, p - v⟫ = 0 := by rw [← hdiff, hz p hp, hfv, sub_zero]
    have h3 : ⟪n, w' - v⟫ = 0 := by rw [← hdiff, hz w' hw'Q, hfv, sub_zero]
    have hne' : ⟪n, e⟫ = 0 := by
      have := hdiff v (v + e); rw [hfe, hfv, add_sub_cancel_left] at this; linarith
    have h2 : ⟪e, p - v⟫ = 0 := by
      rw [inner_sub_right, real_inner_comm p e, real_inner_comm v e, hpv, sub_self]
    have h4 : ⟪e, w' - v⟫ = 0 := by
      rw [inner_sub_right, real_inner_comm w' e, real_inner_comm v e, hwe, sub_self]
    have hn0 : n ≠ 0 := by
      intro h0; apply hy
      have := hdiff v y; rw [h0, inner_zero_left, hfv, sub_zero] at this; exact this
    have hk : cross n e ≠ 0 := by
      intro h0
      have := eq_smul_of_cross_eq_zero hn0 h0
      rw [real_inner_comm, hne', zero_div, zero_smul] at this
      exact he this
    obtain ⟨c, hc⟩ := exists_smul_of_perp2 hk (sub_ne_zero.mpr hvp.symm) h1 h2 h3 h4
    exact hgen v (hQV hv) p (hQV hp) w' (hQV hw'Q) hvp (fun h => hw'v h.symm)
      (fun h => hw'p h.symm) c hc
  rcases lt_or_gt_of_ne hne with h | h
  · refine ⟨1, Or.inl rfl, fun x hx h1 h2 => ?_⟩
    rw [only x hx h1 h2]; simp only; linarith
  · refine ⟨-1, Or.inr rfl, fun x hx h1 h2 => ?_⟩
    rw [only x hx h1 h2]; simp only; linarith

/-- General position for Lemma T when one face is a triangle: only no segment
parallel to the line of the two planes (a triangle face settles every tie of the far
ends, the triple tie included: `TriGenPar.tieS`). -/
def TriGenPar (V Q1 Q2 : Finset ℝ³) (v : ℝ³) : Prop :=
  ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ, (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
    (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
    ∀ e : ℝ³, e ≠ 0 → f1 (v + e) = 0 → f2 (v + e) = 0 →
      ∀ p ∈ V, ∀ q ∈ V, p ≠ q → ∀ c : ℝ, q - p ≠ c • e

theorem TriGenTri.par {V Q1 Q2 : Finset ℝ³} {v : ℝ³} (h : TriGenTri V Q1 Q2 v) :
    TriGenPar V Q1 Q2 v := fun f1 f2 z1 n1 z2 n2 e he e1 e2 =>
  (h f1 f2 z1 n1 z2 n2 e he e1 e2).1

set_option maxHeartbeats 4000000 in
/-- **A triangle face settles every tie at the far ends** (Lemma T at the tie, and
Theorem 24.5 (a), (b) at the triple tie): with no three points collinear, `TriGenPar`
gives the far condition `TieHW False` (no robust way out needed, so no solid). -/
theorem TriGenPar.tieS {V Q1 Q2 : Finset ℝ³} {v : ℝ³} (hgen : NoThreeCollinear V)
    (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (hint : Q1 ∩ Q2 = {v}) (hcard : Q1.card = 3 ∨ Q2.card = 3)
    (h : TriGenPar V Q1 Q2 v) : TriGenTieW False V Q1 Q2 v := by
  intro f1 f2 z1 n1 z2 n2 e he e1 e2
  refine ⟨h f1 f2 z1 n1 z2 n2 e he e1 e2, fun p hp q hq hpq hpm hqm => ?_⟩
  have hv1 : v ∈ Q1 := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).1
  have hv2 : v ∈ Q2 := (Finset.mem_inter.mp (hint ▸ Finset.mem_singleton_self v)).2
  have only : ∀ x ∈ Q1, x ∈ Q2 → x = v := by
    intro x h1 h2
    have : x ∈ Q1 ∩ Q2 := Finset.mem_inter.mpr ⟨h1, h2⟩
    rwa [hint, Finset.mem_singleton] at this
  by_cases ht : ⟪p, e⟫ = ⟪q, e⟫
  swap
  · exact Or.inl (Or.inl ht)
  by_cases hvp : ⟪v, e⟫ = ⟪p, e⟫
  · -- the triple tie: the triangle face is one-sided
    refine Or.inr (Or.inr ⟨ht, hvp, ?_⟩)
    rcases hcard with hc | hc
    · have hpv : v ≠ p := by
        intro hvp'
        obtain ⟨x, hx, hxv⟩ := Finset.exists_mem_ne (by omega : 1 < Q1.card) v
        have h1 := hpm x hx
        rw [← hvp', z2 v hv2] at h1
        have h2 := n2 x (h1V hx) (fun h => hxv (only x hx h))
        linarith
      by_cases hQ2 : ∃ x ∈ Q2, x ≠ v
      · obtain ⟨y, hy, hyv⟩ := hQ2
        exact Or.inl (oneSided_tri hgen h1V hc hv1 hp hpv f1 z1
          (n1 y (h2V hy) (fun h => hyv (only y h hy))).ne he e1 hvp.symm)
      · push Not at hQ2
        exact Or.inr (Or.inl ⟨1, Or.inl rfl, fun x hx hxv _ => absurd (hQ2 x hx) hxv⟩)
    · have hqv : v ≠ q := by
        intro hvq
        obtain ⟨x, hx, hxv⟩ := Finset.exists_mem_ne (by omega : 1 < Q2.card) v
        have h1 := hqm x hx
        rw [← hvq, z1 v hv1] at h1
        have h2 := n1 x (h2V hx) (fun h => hxv (only x h hx))
        linarith
      have hqe : ⟪q, e⟫ = ⟪v, e⟫ := by rw [← ht, hvp]
      by_cases hQ1 : ∃ x ∈ Q1, x ≠ v
      · obtain ⟨y, hy, hyv⟩ := hQ1
        exact Or.inr (Or.inl (oneSided_tri hgen h2V hc hv2 hq hqv f2 z2
          (n2 y (h1V hy) (fun h => hyv (only y hy h))).ne he e2 hqe))
      · push Not at hQ1
        exact Or.inl ⟨1, Or.inl rfl, fun x hx hxv _ => absurd (hQ1 x hx) hxv⟩
  -- the far ends tied, `v` off their depth: the triangle's strict top or bottom
  have hpv : ⟪p, e⟫ ≠ ⟪v, e⟫ := fun h' => hvp h'.symm
  left; right
  rcases hcard with hc | hc
  · -- `Q1` is a triangle: `p` or `v` is its strict top or bottom
    have hpv' : v ≠ p := fun e' => hpv (by rw [e'])
    obtain ⟨w, hw⟩ := exists_third_of_card_three hc hv1 hp hpv'
    obtain ⟨s, hs, hst | hst⟩ := three_heights (hv := ⟪v, e⟫) (hp := ⟪p, e⟫) (hw := ⟪w, e⟫)
      (fun e' => hpv e'.symm)
    · refine ⟨s, hs, Or.inl fun x hx hxp => ?_⟩
      rcases hw x hx with rfl | rfl | rfl
      · exact hst.1
      · exact absurd rfl hxp
      · exact hst.2
    · refine ⟨s, hs, Or.inr (Or.inr (Or.inl fun x hx hxv => ?_))⟩
      rcases hw x hx with rfl | rfl | rfl
      · exact absurd rfl hxv
      · exact hst.1
      · exact hst.2
  · -- `Q2` is a triangle: `q` or `v` is its strict top or bottom
    have hqv : ⟪q, e⟫ ≠ ⟪v, e⟫ := by rw [← ht]; exact hpv
    have hvq : v ≠ q := fun e' => hqv (by rw [e'])
    obtain ⟨w, hw⟩ := exists_third_of_card_three hc hv2 hq hvq
    obtain ⟨s, hs, hst | hst⟩ := three_heights (hv := ⟪v, e⟫) (hp := ⟪q, e⟫) (hw := ⟪w, e⟫)
      (fun e' => hqv e'.symm)
    · refine ⟨-s, by rcases hs with rfl | rfl <;> norm_num, Or.inr (Or.inl fun x hx hxq => ?_)⟩
      rcases hw x hx with rfl | rfl | rfl
      · linarith [hst.1]
      · exact absurd rfl hxq
      · linarith [hst.2]
    · refine ⟨s, hs, Or.inr (Or.inr (Or.inr fun x hx hxv => ?_))⟩
      rcases hw x hx with rfl | rfl | rfl
      · exact absurd rfl hxv
      · exact hst.1
      · exact hst.2

/-- **Lemma T over a vertex with a triangle face, either general position** (as
`isRupert_of_facets_vertex_tie_or`, with `TriGenPar.tieS`): `TriGenTieW False` (from
`TriGenPar`) or `TriGenFarP`. No solid is needed. -/
theorem isRupert_of_facets_vertex_tieS_or (V : Finset ℝ³) (hgen : NoThreeCollinear V)
    (Q1 Q2 : Finset ℝ³) (h1V : Q1 ⊆ V) (h2V : Q2 ⊆ V) (h1f : IsFacet V Q1) (h2f : IsFacet V Q2)
    (v : ℝ³) (hint : Q1 ∩ Q2 = {v}) (hne1 : ∃ p ∈ Q1, p ≠ v) (hne2 : ∃ p ∈ Q2, p ≠ v)
    (hT : TriGenTieW False V Q1 Q2 v ∨ TriGenFarP V Q1 Q2 v)
    (hin : ∃ xa ∈ Q1, ∃ xb ∈ Q2, xa ≠ v ∧ xb ≠ v ∧ ∀ f1 f2 : ℝ³ →ᵃ[ℝ] ℝ,
      (∀ p ∈ Q1, f1 p = 0) → (∀ p ∈ V, p ∉ Q1 → f1 p < 0) →
      (∀ p ∈ Q2, f2 p = 0) → (∀ p ∈ V, p ∉ Q2 → f2 p < 0) →
      ∀ y ∈ V, y ∉ Q1 → y ∉ Q2 → f2 y / f2 xa + f1 y / f1 xb < 1) : IsRupert V := by
  rcases hT with hT | hT
  · exact isRupert_of_facets_vertex_tieW V hgen Q1 Q2 h1V h2V h1f h2f v hint hne1 hne2 hT hin
      False.elim
  · exact isRupert_of_facets_vertex_par V hgen Q1 Q2 h1V h2V h1f h2f v hint hne1 hne2 hT hin

end Minimality

end
