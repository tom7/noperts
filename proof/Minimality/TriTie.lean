module

public import Minimality.TriShadowChord

@[expose] public section

/-!
# Lemma T at the tie

"Lemma T at the tie" of `FEWER-FACES-PROOFS.md` §7: at the view along the line
of two face planes, the far ends `xa`, `xb` of the shadow triangle may have the
same depth, and some tilt is still unimodal when (b) the lowest vertex of a
face's chain is the shared vertex or its far end, or (c) the same with the
highest. Every case comes down to one sequence fact
(`localMax_unique_of_run`): if every position of a cyclic sequence outside a
run has a strictly larger neighbour, and the run has no interior local
minimum, the local maximum is unique. These conditions are strict at the
untilted view, so `isRupert_of_tilted_localMax` applies without breaking the
tie by hand.
-/

namespace Minimality

open Finset Filter Topology
open scoped RealInnerProductSpace

/-- **One concave run.** Positions `0, …, L` of a cyclic sequence form a run
with no interior local minimum, and every other position has a strictly larger
neighbour. Then the sequence has at most one strict local maximum. -/
theorem localMax_unique_of_run {K L : ℕ} [NeZero K] (hL : L < K) (w : ZMod K → ℝ)
    (hout : ∀ l : ℕ, L < l → l < K →
      w (l : ZMod K) < w ((l - 1 : ℕ) : ZMod K) ∨ w (l : ZMod K) < w ((l + 1 : ℕ) : ZMod K))
    (hconc : ∀ l : ℕ, 1 ≤ l → l < L →
      min (w ((l - 1 : ℕ) : ZMod K)) (w ((l + 1 : ℕ) : ZMod K)) < w (l : ZMod K)) :
    ∀ a b : ZMod K, w (a - 1) < w a → w (a + 1) < w a →
      w (b - 1) < w b → w (b + 1) < w b → a = b := by
  have hcast : ∀ a : ZMod K, ((a.val : ℕ) : ZMod K) = a := ZMod.natCast_zmod_val
  have hsub : ∀ l : ℕ, 1 ≤ l → ((l : ZMod K) - 1) = ((l - 1 : ℕ) : ZMod K) := by
    intro l hl; rw [Nat.cast_sub hl]; simp
  have hadd : ∀ l : ℕ, ((l : ZMod K) + 1) = ((l + 1 : ℕ) : ZMod K) := by intro l; simp
  -- a local maximum lies in the run
  have inrun' : ∀ l : ℕ, l < K → w ((l : ZMod K) - 1) < w (l : ZMod K) →
      w ((l : ZMod K) + 1) < w (l : ZMod K) → l ≤ L := by
    intro l hlK h1 h2
    by_contra hv; push Not at hv
    rw [hsub l (by omega)] at h1
    rw [hadd] at h2
    rcases hout l hv hlK with h | h <;> linarith
  have inrun : ∀ a : ZMod K, w (a - 1) < w a → w (a + 1) < w a → a.val ≤ L := by
    intro a h1 h2
    have ha := hcast a
    rw [← ha] at h1 h2
    exact inrun' a.val (ZMod.val_lt a) h1 h2
  -- two local maxima in the run would enclose an interior local minimum
  have key : ∀ p q : ℕ, p < q → q ≤ L →
      w ((p + 1 : ℕ) : ZMod K) < w (p : ZMod K) → w ((q - 1 : ℕ) : ZMod K) < w (q : ZMod K) → False := by
    intro p q hpq hqL hp hq
    obtain ⟨c, hc, hcmin⟩ := (Finset.Icc p q).exists_min_image (fun l : ℕ => w (l : ZMod K))
      ⟨p, Finset.mem_Icc.mpr ⟨le_rfl, hpq.le⟩⟩
    obtain ⟨hc1, hc2⟩ := Finset.mem_Icc.mp hc
    have cp : c ≠ p := by
      rintro rfl
      exact absurd (hcmin (c + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)) (not_le.mpr hp)
    have cq : c ≠ q := by
      rintro rfl
      exact absurd (hcmin (c - 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)) (not_le.mpr hq)
    have := hconc c (by omega) (by omega)
    have e1 := hcmin (c - 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    have e2 := hcmin (c + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    rw [min_lt_iff] at this
    rcases this with h | h <;> linarith
  intro a b ha1 ha2 hb1 hb2
  have hav := inrun a ha1 ha2
  have hbv := inrun b hb1 hb2
  have ea := hcast a; have eb := hcast b
  have lmax : ∀ x : ZMod K, w (x - 1) < w x → w (x + 1) < w x →
      w ((x.val + 1 : ℕ) : ZMod K) < w (x.val : ZMod K) ∧
        (1 ≤ x.val → w ((x.val - 1 : ℕ) : ZMod K) < w (x.val : ZMod K)) := by
    intro x h1 h2
    have ex := hcast x
    refine ⟨by rw [← hadd, ex]; exact h2, fun h => by rw [← hsub _ h, ex]; exact h1⟩
  rcases lt_trichotomy a.val b.val with h | h | h
  · exact (key a.val b.val h hbv (lmax a ha1 ha2).1 ((lmax b hb1 hb2).2 (by omega))).elim
  · exact ZMod.val_injective K h
  · exact (key b.val a.val h hav (lmax b hb1 hb2).1 ((lmax a ha1 ha2).2 (by omega))).elim

/-- `localMax_unique_of_run` for a run starting at position `c`. -/
theorem localMax_unique_of_run_shift {K L : ℕ} [NeZero K] (hL : L < K) (c : ℕ) (w : ZMod K → ℝ)
    (hout : ∀ l : ℕ, L < l → l < K →
      w ((c + l : ℕ) : ZMod K) < w ((c + l - 1 : ℕ) : ZMod K) ∨
        w ((c + l : ℕ) : ZMod K) < w ((c + l + 1 : ℕ) : ZMod K))
    (hconc : ∀ l : ℕ, 1 ≤ l → l < L →
      min (w ((c + l - 1 : ℕ) : ZMod K)) (w ((c + l + 1 : ℕ) : ZMod K)) < w ((c + l : ℕ) : ZMod K)) :
    ∀ a b : ZMod K, w (a - 1) < w a → w (a + 1) < w a →
      w (b - 1) < w b → w (b + 1) < w b → a = b := by
  set w' : ZMod K → ℝ := fun i => w (i + (c : ZMod K)) with hw'
  have shift : ∀ l : ℕ, w' (l : ZMod K) = w ((c + l : ℕ) : ZMod K) := by
    intro l; simp only [hw']; push_cast; ring_nf
  have shiftm : ∀ l : ℕ, 1 ≤ l → w' ((l - 1 : ℕ) : ZMod K) = w ((c + l - 1 : ℕ) : ZMod K) := by
    intro l hl; rw [shift]; congr 2; omega
  have shiftp : ∀ l : ℕ, w' ((l + 1 : ℕ) : ZMod K) = w ((c + l + 1 : ℕ) : ZMod K) := by
    intro l; rw [shift]; congr 2
  have h := localMax_unique_of_run hL w'
    (fun l h1 h2 => by rw [shiftm l (by omega), shiftp, shift]; exact hout l h1 h2)
    (fun l h1 h2 => by rw [shiftm l h1, shiftp, shift]; exact hconc l h1 h2)
  intro a b ha1 ha2 hb1 hb2
  have e : ∀ x : ZMod K, w' (x - (c : ZMod K)) = w x := fun x => by simp [hw']
  have := h (a - c) (b - c)
    (by rw [show a - (c : ZMod K) - 1 = (a - 1) - c by ring, e, e]; exact ha1)
    (by rw [show a - (c : ZMod K) + 1 = (a + 1) - c by ring, e, e]; exact ha2)
    (by rw [show b - (c : ZMod K) - 1 = (b - 1) - c by ring, e, e]; exact hb1)
    (by rw [show b - (c : ZMod K) + 1 = (b + 1) - c by ring, e, e]; exact hb2)
  exact sub_left_injective this

/-- The hypotheses of `localMax_unique_of_run_shift` for `s z` (run of length
`L` from position `c`), as an open, scale-invariant condition on `z`. -/
def RunSeq (K L c : ℕ) (s : ℝ) (z : ZMod K → ℝ) : Prop :=
  (∀ l ∈ Finset.Ioo L K, s * z ((c + l : ℕ) : ZMod K) < s * z ((c + l - 1 : ℕ) : ZMod K) ∨
      s * z ((c + l : ℕ) : ZMod K) < s * z ((c + l + 1 : ℕ) : ZMod K)) ∧
    (∀ l ∈ Finset.Ioo 0 L, s * z ((c + l - 1 : ℕ) : ZMod K) < s * z ((c + l : ℕ) : ZMod K) ∨
      s * z ((c + l + 1 : ℕ) : ZMod K) < s * z ((c + l : ℕ) : ZMod K))

theorem isOpen_runSeq (K L c : ℕ) (s : ℝ) : IsOpen {z | RunSeq K L c s z} := by
  have cc : ∀ a : ZMod K, Continuous fun z : ZMod K → ℝ => s * z a :=
    fun a => continuous_const.mul (continuous_apply a)
  have e : {z | RunSeq K L c s z} =
      (⋂ l ∈ Finset.Ioo L K, ({z : ZMod K → ℝ | s * z ((c + l : ℕ) : ZMod K) <
        s * z ((c + l - 1 : ℕ) : ZMod K)} ∪ {z | s * z ((c + l : ℕ) : ZMod K) <
        s * z ((c + l + 1 : ℕ) : ZMod K)})) ∩
      (⋂ l ∈ Finset.Ioo 0 L, ({z : ZMod K → ℝ | s * z ((c + l - 1 : ℕ) : ZMod K) <
        s * z ((c + l : ℕ) : ZMod K)} ∪ {z | s * z ((c + l + 1 : ℕ) : ZMod K) <
        s * z ((c + l : ℕ) : ZMod K)})) := by
    ext z; simp only [RunSeq, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_union]
  rw [e]
  refine (isOpen_biInter_finset fun l _ => ?_).inter (isOpen_biInter_finset fun l _ => ?_)
  · exact (isOpen_lt (cc _) (cc _)).union (isOpen_lt (cc _) (cc _))
  · exact (isOpen_lt (cc _) (cc _)).union (isOpen_lt (cc _) (cc _))

theorem runSeq_smul {K L c : ℕ} {s : ℝ} {z : ZMod K → ℝ} {k : ℝ} (hk : 0 < k)
    (h : RunSeq K L c s z) : RunSeq K L c s (fun i => k * z i) := by
  have m : ∀ a b : ZMod K, s * z a < s * z b → s * (k * z a) < s * (k * z b) := by
    intro a b hab
    rw [show s * (k * z a) = k * (s * z a) by ring, show s * (k * z b) = k * (s * z b) by ring]
    exact mul_lt_mul_of_pos_left hab hk
  exact ⟨fun l hl => (h.1 l hl).imp (m _ _) (m _ _), fun l hl => (h.2 l hl).imp (m _ _) (m _ _)⟩

theorem runSeq_localMax {K L c : ℕ} [NeZero K] (hL : L < K) {s : ℝ} {z : ZMod K → ℝ}
    (h : RunSeq K L c s z) : ∀ a b : ZMod K, s * z (a - 1) < s * z a →
      s * z (a + 1) < s * z a → s * z (b - 1) < s * z b → s * z (b + 1) < s * z b → a = b :=
  localMax_unique_of_run_shift hL c (fun i => s * z i)
    (fun l h1 h2 => h.1 l (Finset.mem_Ioo.mpr ⟨h1, h2⟩))
    (fun l h1 h2 => min_lt_iff.mpr ((h.2 l (Finset.mem_Ioo.mpr ⟨by omega, h2⟩)).imp id id))

set_option maxHeartbeats 4000000 in
/-- **Lemma T, general sectors and the tie.** As `isRupert_triShadow_tilt`, with
the tilt `(-t α, s β)`: `t = s` is a mixed sector (as there), `t = -s` a
same-sign sector (`C2` then lies on the other side of its ray). Instead of
`s z_B < s z_A` it takes one of four modes, each with a run for
`localMax_unique_of_run`: strict (`t = s`, `s z_B < s z_A`); `C1` rises
strictly in `s z` to `A` (`t = s`); `C2` reversed rises strictly from `B`
to the apex (any `t`); `C1` falls strictly from the apex (`t = -s`). The last
three allow `z_A = z_B` ("Lemma T at the tie", cases (b) and (c)). -/
theorem isRupert_triShadow_gen (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) {m n : ℕ}
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
    (hmode : (t = s ∧ s * dz n < s * cz m) ∨ (t = s ∧ ∀ l, l < m → s * cz l < s * cz (l + 1)) ∨
      (∀ j, j < n → s * dz (j + 1) < s * dz j) ∨ (t = -s ∧ ∀ l, l < m → s * cz (l + 1) < s * cz l)) :
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
  -- the run of the sequence lemma, by the mode
  have hrun : ∃ L c : ℕ, L < m + n + 1 ∧ RunSeq (m + n + 1) L c s Z := by
    rcases hmode with ⟨hts, hAB⟩ | ⟨hts, hinc⟩ | hFB | ⟨hts, hdec⟩
    · -- the strict case: the run is `C1`
      refine ⟨m, 0, by omega, fun l hl => ?_, fun l hl => ?_⟩
      · obtain ⟨h1, h2⟩ := Finset.mem_Ioo.mp hl
        simp only [zero_add]
        rcases Nat.lt_or_ge l (m + 2) with h3 | h3
        · left
          obtain rfl : l = m + 1 := by omega
          rw [hZ2 (m + 1) (by omega) (by omega), show m + 1 - 1 = m by omega, hZ1 m le_rfl,
            show m + n + 1 - (m + 1) = n by omega]
          exact hAB
        · have := hconvZ l h3 (by omega); rw [hts] at this; exact lt_max_iff.mp this
      · obtain ⟨h1, h2⟩ := Finset.mem_Ioo.mp hl
        simp only [zero_add]
        exact min_lt_iff.mp (hconcZ l (by omega) h2)
    · -- `C1` rises to `A`: the run is `A, B`
      refine ⟨1, m, by omega, fun l hl => ?_, fun l hl => ?_⟩
      · obtain ⟨h1, h2⟩ := Finset.mem_Ioo.mp hl
        rcases Nat.lt_or_ge (m + l) (m + n + 1) with h3 | h3
        · have := hconvZ (m + l) (by omega) (by omega); rw [hts] at this; exact lt_max_iff.mp this
        · right
          rw [show m + l = m + n + 1 + (m + l - (m + n + 1)) by omega,
            show m + n + 1 + (m + l - (m + n + 1)) + 1 = m + n + 1 + (m + l - (m + n + 1) + 1) by omega,
            hw, hw, hZ1 _ (by omega), hZ1 _ (by omega)]
          exact hinc _ (by omega)
      · obtain ⟨h1, h2⟩ := Finset.mem_Ioo.mp hl; omega
    · -- `C2` reversed rises from `B` to the apex: the run is `C1`
      refine ⟨m, 0, by omega, fun l hl => ?_, fun l hl => ?_⟩
      · obtain ⟨h1, h2⟩ := Finset.mem_Ioo.mp hl
        simp only [zero_add]
        right
        have hl1 : Z ((l + 1 : ℕ) : ZMod (m + n + 1)) = dz (m + n - l) := by
          rcases Nat.lt_or_ge l (m + n) with h | h
          · rw [hZ2 (l + 1) (by omega) (by omega)]; congr 1; omega
          · rw [show l + 1 = m + n + 1 by omega, hZk, show m + n - l = 0 by omega]
        rw [hZ2 l (by omega) (by omega), hl1]
        have := hFB (m + n - l) (by omega)
        rwa [show m + n - l + 1 = m + n + 1 - l by omega] at this
      · obtain ⟨h1, h2⟩ := Finset.mem_Ioo.mp hl
        simp only [zero_add]
        exact min_lt_iff.mp (hconcZ l (by omega) h2)
    · -- same-sign sector, `C1` falls from the apex: the run is `C2` reversed and the apex
      refine ⟨n, m + 1, by omega, fun l hl => ?_, fun l hl => ?_⟩
      · obtain ⟨h1, h2⟩ := Finset.mem_Ioo.mp hl
        left
        rw [show m + 1 + l = m + n + 1 + (l - n) by omega,
          show m + n + 1 + (l - n) - 1 = m + n + 1 + (l - n - 1) by omega,
          hw, hw, hZ1 _ (by omega), hZ1 _ (by omega)]
        have := hdec (l - n - 1) (by omega)
        rwa [show l - n - 1 + 1 = l - n by omega] at this
      · obtain ⟨h1, h2⟩ := Finset.mem_Ioo.mp hl
        have := hconvZ (m + 1 + l) (by omega) (by omega)
        rw [hts, lt_max_iff] at this
        rcases this with h | h
        · left; linarith
        · right; linarith
  obtain ⟨L, c, hLK, hR⟩ := hrun
  exact isRupert_of_tilted_localMax V ez v hez (k := m + n + 1) (by omega) x hxV hcyc hrest s hs
    (RunSeq (m + n + 1) L c s) (isOpen_runSeq _ _ _ s) (fun z k hk hz => runSeq_smul hk hz)
    (by rw [show (fun i => ⟪x i, ez⟫) = Z from funext hdepth]; exact hR)
    (fun z hz => runSeq_localMax hLK hz)

end Minimality

end
