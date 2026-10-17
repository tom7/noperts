module

public import Minimality.EdgeView

@[expose] public section

/-!
# The triangle-shadow lemma (Lemma T)

Lemma T of `FEWER-FACES-PROOFS.md` §7, in the oblique frame of `EdgeView.lean`:
the view is `ez`, the limit shadow is the triangle `O, O + A r1, O + B r2`, a
single vertex (the apex, oblique coordinates `(0, 0)`) lies over `O`, and every
other vertex lies on the two rays or strictly inside the triangle.  The tilt
`v = -s r1 + s r2` (`s = ±1`) shows the chain `C1` of the face on the first ray
(traversed outward) and the chain `C2` of the face on the second ray (traversed
inward); with `s = 1` these are the upper and the lower chain.  If
`s (z_A - z_B) > 0` the cycle `C1, C2 reversed` is unimodal: every local maximum
of `s z` lies on `C1`, which is concave.

This first part is the sequence lemma.
-/

namespace Minimality

open Finset Filter Topology
open scoped RealInnerProductSpace

/-- **The mixed cycle has one local maximum.**  Positions `0, …, m` carry the
concave chain (apex at `0`, the far end `A` at `m`), positions `m + 1, …, m + n`
the convex chain reversed (its far end `B` at `m + 1`, the apex again at
`m + n + 1 = 0`), and `w A > w B`. -/
theorem tri_localMax_unique {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (w : ZMod (m + n + 1) → ℝ)
    (hconc : ∀ l : ℕ, 1 ≤ l → l < m →
      min (w ((l - 1 : ℕ) : ZMod (m + n + 1))) (w ((l + 1 : ℕ) : ZMod (m + n + 1))) <
        w (l : ZMod (m + n + 1)))
    (hconv : ∀ l : ℕ, m + 2 ≤ l → l ≤ m + n →
      w (l : ZMod (m + n + 1)) <
        max (w ((l - 1 : ℕ) : ZMod (m + n + 1))) (w ((l + 1 : ℕ) : ZMod (m + n + 1))))
    (hAB : w ((m + 1 : ℕ) : ZMod (m + n + 1)) < w (m : ZMod (m + n + 1))) :
    ∀ a b : ZMod (m + n + 1), w (a - 1) < w a → w (a + 1) < w a →
      w (b - 1) < w b → w (b + 1) < w b → a = b := by
  have : NeZero (m + n + 1) := ⟨by omega⟩
  -- every element is the cast of its value
  have hcast : ∀ a : ZMod (m + n + 1), ((a.val : ℕ) : ZMod (m + n + 1)) = a := ZMod.natCast_zmod_val
  have hlt : ∀ a : ZMod (m + n + 1), a.val < m + n + 1 := fun a => ZMod.val_lt a
  have hsub : ∀ l : ℕ, 1 ≤ l → ((l : ZMod (m + n + 1)) - 1) = ((l - 1 : ℕ) : ZMod (m + n + 1)) := by
    intro l hl; rw [Nat.cast_sub hl]; simp
  have hadd : ∀ l : ℕ, ((l : ZMod (m + n + 1)) + 1) = ((l + 1 : ℕ) : ZMod (m + n + 1)) := by intro l; simp
  -- a local maximum sits at a position `≤ m`
  have hpos : ∀ a : ZMod (m + n + 1), w (a - 1) < w a → w (a + 1) < w a → a.val ≤ m := by
    intro a h1 h2
    by_contra hv
    push Not at hv
    have ha := hcast a
    have hva := hlt a
    rcases Nat.lt_or_ge a.val (m + 2) with hv2 | hv2
    · -- `a` is `B`, whose predecessor `A` is higher
      have hb : a.val = m + 1 := by omega
      rw [← ha, hb, hsub _ (by omega)] at h1
      simp only [Nat.add_sub_cancel] at h1
      rw [hb] at ha
      exact absurd (lt_trans h1 hAB) (lt_irrefl _)
    · have := hconv a.val hv2 (by omega)
      rw [ha] at this
      have h1' : w ((a.val - 1 : ℕ) : ZMod (m + n + 1)) < w a := by
        rw [← hsub _ (by omega), hcast]; exact h1
      have h2' : w ((a.val + 1 : ℕ) : ZMod (m + n + 1)) < w a := by
        rw [← hadd, hcast]; exact h2
      exact absurd (max_lt h1' h2') (not_lt.mpr this.le)
  intro a b ha1 ha2 hb1 hb2
  have hpa := hpos a ha1 ha2
  have hpb := hpos b hb1 hb2
  -- two local maxima on the concave chain would enclose a local minimum
  wlog hab : a.val ≤ b.val generalizing a b
  · exact (this b a hb1 hb2 ha1 ha2 hpb hpa (by omega)).symm
  rcases Nat.eq_or_lt_of_le hab with he | hlt'
  · exact (ZMod.val_injective (m + n + 1)) he
  exfalso
  obtain ⟨l, hl, hmin⟩ := (Finset.Icc a.val b.val).exists_min_image
    (fun l : ℕ => w (l : ZMod (m + n + 1))) ⟨a.val, by simp [hab]⟩
  simp only [Finset.mem_Icc] at hl
  have hwa : w ((a.val + 1 : ℕ) : ZMod (m + n + 1)) < w ((a.val : ℕ) : ZMod (m + n + 1)) := by
    rw [← hadd, hcast]; exact ha2
  have hwb : w ((b.val - 1 : ℕ) : ZMod (m + n + 1)) < w ((b.val : ℕ) : ZMod (m + n + 1)) := by
    rw [← hsub _ (by omega), hcast]; exact hb1
  have hla : l ≠ a.val := by
    rintro rfl
    have := hmin (a.val + 1) (by simp; omega)
    exact absurd (lt_of_le_of_lt this hwa) (lt_irrefl _)
  have hlb : l ≠ b.val := by
    rintro rfl
    have := hmin (b.val - 1) (by simp; omega)
    exact absurd (lt_of_le_of_lt this hwb) (lt_irrefl _)
  have h1 : 1 ≤ l := by omega
  have h2 : l < m := by omega
  have hc := hconc l h1 h2
  have hle1 := hmin (l - 1) (by simp; omega)
  have hle2 := hmin (l + 1) (by simp; omega)
  rcases min_lt_iff.mp hc with h | h
  · exact absurd (lt_of_le_of_lt hle1 h) (lt_irrefl _)
  · exact absurd (lt_of_le_of_lt hle2 h) (lt_irrefl _)

/-! ### The frame theorem -/

/-- The cycle position `v` of the mixed cycle: `C1 v` for `v ≤ m`, else
`C2 (m + n + 1 - v)`. -/
noncomputable def triPt (O r1 r2 : ℝ²) (m n : ℕ) (ca cz cb dz : ℕ → ℝ) (v : ℕ) : ℝ³ :=
  if v ≤ m then oblPt O r1 r2 (ca v) 0 (cz v)
  else oblPt O r1 r2 0 (cb (m + n + 1 - v)) (dz (m + n + 1 - v))

/-- Its depth. -/
noncomputable def triZ (m n : ℕ) (cz dz : ℕ → ℝ) (v : ℕ) : ℝ :=
  if v ≤ m then cz v else dz (m + n + 1 - v)

theorem inner_oblPt_ez (O r1 r2 : ℝ²) (a b z : ℝ) : ⟪oblPt O r1 r2 a b z, ez⟫ = z := by
  simp [oblPt, inner_ez]

theorem far_tiltOK {A B ay by' zp zq zy α β : ℝ} (h : ay * B + by' * A < A * B) :
    TiltOK A 0 zp 0 B zq ay by' zy α β :=
  Or.inl (by nlinarith)

/-- Oblique coordinates are coordinates. -/
theorem oblPt_inj {O r1 r2 : ℝ²} (hρ : 0 < cross2 r1 r2) {a b z a' b' z' : ℝ}
    (h : oblPt O r1 r2 a b z = oblPt O r1 r2 a' b' z') : a = a' ∧ b = b' ∧ z = z' := by
  have h0 := congrArg (fun p : ℝ³ => p 0) h
  have h1 := congrArg (fun p : ℝ³ => p 1) h
  have h2 := congrArg (fun p : ℝ³ => p 2) h
  simp [oblPt] at h0 h1 h2
  have ea : (a - a') * cross2 r1 r2 = 0 := by unfold cross2; linear_combination r2 1 * h0 - r2 0 * h1
  have eb : (b - b') * cross2 r1 r2 = 0 := by unfold cross2; linear_combination r1 0 * h1 - r1 1 * h0
  refine ⟨?_, ?_, h2⟩
  · have := (mul_eq_zero.mp ea).resolve_right hρ.ne'; linarith
  · have := (mul_eq_zero.mp eb).resolve_right hρ.ne'; linarith

/-- **Lemma T in the oblique frame (a single vertex over the apex).**  The
chain `C1 l = (ca l, 0, cz l)` (`l ≤ m`) runs out along the first ray from the
apex `C1 0` to `A = C1 m`, the chain `C2 l = (0, cb l, dz l)` (`l ≤ n`) along the
second ray from the apex `C2 0 = C1 0` to `B = C2 n`.  Every point of `V` lies in
the triangle (strictly inside the far side unless it is `A` or `B`), and the
points on each ray lie on the `s`-side of each segment of that ray's chain
(`s = 1`: below `C1`, above `C2`).  If the depths along the cycle are distinct
and `s z_A > s z_B`, the tilt `-s r1 + s r2` is unimodal and `V` is Rupert. -/
theorem isRupert_triShadow (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) {m n : ℕ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) (s : ℝ) (hs : s = 1 ∨ s = -1) (ca cz cb dz : ℕ → ℝ)
    (hca0 : ca 0 = 0) (hcb0 : cb 0 = 0) (hdz0 : dz 0 = cz 0)
    (hca : ∀ l, l < m → ca l < ca (l + 1)) (hcb : ∀ l, l < n → cb l < cb (l + 1))
    (V : Finset ℝ³)
    (hC1V : ∀ l, l ≤ m → oblPt O r1 r2 (ca l) 0 (cz l) ∈ V)
    (hC2V : ∀ l, l ≤ n → oblPt O r1 r2 0 (cb l) (dz l) ∈ V)
    (hVc : ∀ y ∈ V, ∃ a b z, y = oblPt O r1 r2 a b z ∧ 0 ≤ a ∧ 0 ≤ b ∧
      (a * cb n + b * ca m < ca m * cb n ∨ y = oblPt O r1 r2 (ca m) 0 (cz m) ∨
        y = oblPt O r1 r2 0 (cb n) (dz n)) ∧
      (b = 0 → ∀ l, l < m → y ≠ oblPt O r1 r2 (ca l) 0 (cz l) →
        y ≠ oblPt O r1 r2 (ca (l + 1)) 0 (cz (l + 1)) →
        s * ((ca (l + 1) - ca l) * (z - cz l) - (cz (l + 1) - cz l) * (a - ca l)) < 0) ∧
      (a = 0 → ∀ l, l < n → y ≠ oblPt O r1 r2 0 (cb (l + 1)) (dz (l + 1)) →
        y ≠ oblPt O r1 r2 0 (cb l) (dz l) →
        s * ((cb l - cb (l + 1)) * (z - dz (l + 1)) - (dz l - dz (l + 1)) * (b - cb (l + 1))) < 0))
    (hinj : Function.Injective fun i : ZMod (m + n + 1) => triZ m n cz dz i.val)
    (hAB : s * dz n < s * cz m) : IsRupert V := by
  have hNZ : NeZero (m + n + 1) := ⟨by omega⟩
  have hval : ∀ v : ℕ, v < m + n + 1 → ((v : ZMod (m + n + 1))).val = v := fun v hv => by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hv]
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
    intro i j h; apply hinj; simp only; rw [← hdepth, ← hdepth, h]
  -- the tilt
  set v : ℝ³ := oblPt 0 r1 r2 (-s) s 0 with hv
  have key : ∀ {ap bp zp aq bq zq ay by' zy : ℝ}, TiltOK ap bp zp aq bq zq ay by' zy (-s) s →
      TiltSign (oblPt O r1 r2 aq bq zq - oblPt O r1 r2 ap bp zp)
        (oblPt O r1 r2 ay by' zy - oblPt O r1 r2 ap bp zp) ez v :=
    fun h => tiltSign_obl O r1 r2 hρ (-s) s h
  have side1 : ∀ {ap aq zp zq ay zy : ℝ}, s * ((aq - ap) * (zy - zp) - (zq - zp) * (ay - ap)) < 0 →
      TiltOK ap 0 zp aq 0 zq ay 0 zy (-s) s := by
    intro ap aq zp zq ay zy h
    apply tiltOK_side1_on
    rcases hs with rfl | rfl
    · left; exact ⟨one_pos, by linarith⟩
    · right; exact ⟨by norm_num, by linarith⟩
  have side2 : ∀ {bp bq zp zq by' zy : ℝ},
      s * ((bq - bp) * (zy - zp) - (zq - zp) * (by' - bp)) < 0 →
      TiltOK 0 bp zp 0 bq zq 0 by' zy (-s) s := by
    intro bp bq zp zq by' zy h
    apply tiltOK_side2_on
    rcases hs with rfl | rfl
    · right; exact ⟨by norm_num, by linarith⟩
    · left; exact ⟨by norm_num, by linarith⟩
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
      · exact far_tiltOK hin
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
      s * ((cb j - cb (j + 1)) * (dz l - dz (j + 1)) - (dz j - dz (j + 1)) * (cb l - cb (j + 1))) < 0 := by
    intro l hl j hj h1 h2
    obtain ⟨a, b, z, he, -, -, -, -, hr2⟩ := hVc _ (hC2V l hl)
    obtain ⟨ea, eb, ez'⟩ := oblPt_inj hρ he
    subst eb ez'
    exact hr2 ea.symm j hj (he ▸ h1) (he ▸ h2)
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
  -- the sequence lemma for `s Z`
  have hmax := tri_localMax_unique hm hn (fun i => s * Z i)
    (by
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
        mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hcon.1) (sub_nonpos.mpr d2.le)])
    (by
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
        mul_nonneg (sub_nonneg.mpr hcon.1) (sub_nonneg.mpr e2.le)])
    (by
      rw [hZ2 (m + 1) (by omega) (by omega), hZ1 m le_rfl, show m + n + 1 - (m + 1) = n by omega]
      exact hAB)
  have hZu : IsCyclicUnimodal Z := by
    rcases hs with rfl | rfl
    · exact isCyclicUnimodal_of_localMax_unique (by omega) Z hinj
        (fun a b h1 h2 h3 h4 => hmax a b (by linarith) (by linarith) (by linarith) (by linarith))
    · exact isCyclicUnimodal_of_localMin_unique (by omega) Z hinj
        (fun a b h1 h2 h3 h4 => hmax a b (by linarith) (by linarith) (by linarith) (by linarith))
  have hu0 : IsCyclicUnimodal fun i => ⟪x i, ez⟫ := by
    have : (fun i => ⟪x i, ez⟫) = Z := funext hdepth
    rw [this]; exact hZu
  have hez : (ez : ℝ³) ≠ 0 := by
    intro h; have := congrArg (fun x : ℝ³ => x 2) h; simp [ez] at this
  exact isRupert_of_tilted_unimodal' V ez v hez (k := m + n + 1) (by omega)
    x hxV hcyc hrest IsCyclicUnimodal isOpen_isCyclicUnimodal
    (fun z c hc hz => isCyclicUnimodal_smul hc hz)
    (eventually_unimodal_tilt x ez v hu0) (fun z _ h => h)

/-- `isRupert_triShadow` with distinct depths on all of `V` in place of distinct
depths along the cycle. -/
theorem isRupert_triShadow_injOn (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) {m n : ℕ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) (s : ℝ) (hs : s = 1 ∨ s = -1) (ca cz cb dz : ℕ → ℝ)
    (hca0 : ca 0 = 0) (hcb0 : cb 0 = 0) (hdz0 : dz 0 = cz 0)
    (hca : ∀ l, l < m → ca l < ca (l + 1)) (hcb : ∀ l, l < n → cb l < cb (l + 1))
    (V : Finset ℝ³)
    (hC1V : ∀ l, l ≤ m → oblPt O r1 r2 (ca l) 0 (cz l) ∈ V)
    (hC2V : ∀ l, l ≤ n → oblPt O r1 r2 0 (cb l) (dz l) ∈ V)
    (hVc : ∀ y ∈ V, ∃ a b z, y = oblPt O r1 r2 a b z ∧ 0 ≤ a ∧ 0 ≤ b ∧
      (a * cb n + b * ca m < ca m * cb n ∨ y = oblPt O r1 r2 (ca m) 0 (cz m) ∨
        y = oblPt O r1 r2 0 (cb n) (dz n)) ∧
      (b = 0 → ∀ l, l < m → y ≠ oblPt O r1 r2 (ca l) 0 (cz l) →
        y ≠ oblPt O r1 r2 (ca (l + 1)) 0 (cz (l + 1)) →
        s * ((ca (l + 1) - ca l) * (z - cz l) - (cz (l + 1) - cz l) * (a - ca l)) < 0) ∧
      (a = 0 → ∀ l, l < n → y ≠ oblPt O r1 r2 0 (cb (l + 1)) (dz (l + 1)) →
        y ≠ oblPt O r1 r2 0 (cb l) (dz l) →
        s * ((cb l - cb (l + 1)) * (z - dz (l + 1)) - (dz l - dz (l + 1)) * (b - cb (l + 1))) < 0))
    (hzV : Set.InjOn (fun y : ℝ³ => ⟪y, ez⟫) (V : Set ℝ³))
    (hAB : s * dz n < s * cz m) : IsRupert V := by
  have hNZ : NeZero (m + n + 1) := ⟨by omega⟩
  have mono : ∀ (f : ℕ → ℝ) (k : ℕ), (∀ l, l < k → f l < f (l + 1)) →
      ∀ i j, i < j → j ≤ k → f i < f j := by
    intro f k hf i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hij with h | h
      · exact lt_trans (ih h (by omega)) (hf j (by omega))
      · subst h; exact hf i (by omega)
  -- distinct positions carry distinct points
  have hpt : ∀ v, v < m + n + 1 → triPt O r1 r2 m n ca cz cb dz v ∈ V := by
    intro v hv; simp only [triPt]; split_ifs with h
    · exact hC1V v h
    · exact hC2V _ (by omega)
  have hdist : ∀ v w, v < m + n + 1 → w < m + n + 1 → v ≠ w →
      triPt O r1 r2 m n ca cz cb dz v ≠ triPt O r1 r2 m n ca cz cb dz w := by
    intro v w hv hw hvw he
    simp only [triPt] at he
    split_ifs at he with h1 h2 h2
    · have := (oblPt_inj hρ he).1
      rcases Nat.lt_or_gt_of_ne hvw with h | h
      · exact absurd this (mono ca m hca v w h h2).ne
      · exact absurd this (mono ca m hca w v h h1).ne'
    · have := (oblPt_inj hρ he).2.1
      have := mono cb n hcb 0 (m + n + 1 - w) (by omega) (by omega)
      rw [hcb0] at this; linarith
    · have := (oblPt_inj hρ he).2.1
      have := mono cb n hcb 0 (m + n + 1 - v) (by omega) (by omega)
      rw [hcb0] at this; linarith
    · have := (oblPt_inj hρ he).2.1
      rcases Nat.lt_or_gt_of_ne hvw with h | h
      · exact absurd this (mono cb n hcb _ _ (by omega) (by omega)).ne'
      · exact absurd this (mono cb n hcb _ _ (by omega) (by omega)).ne
  refine isRupert_triShadow O r1 r2 hρ hm hn s hs ca cz cb dz hca0 hcb0 hdz0 hca hcb V hC1V hC2V
    hVc ?_ hAB
  intro i j hij
  have hdi : ⟪triPt O r1 r2 m n ca cz cb dz i.val, ez⟫ = triZ m n cz dz i.val := by
    simp only [triPt, triZ]; split_ifs <;> exact inner_oblPt_ez _ _ _ _ _ _
  have hdj : ⟪triPt O r1 r2 m n ca cz cb dz j.val, ez⟫ = triZ m n cz dz j.val := by
    simp only [triPt, triZ]; split_ifs <;> exact inner_oblPt_ez _ _ _ _ _ _
  simp only at hij
  by_contra hne
  have hv : i.val ≠ j.val := fun h => hne (ZMod.val_injective _ h)
  exact hdist _ _ (ZMod.val_lt i) (ZMod.val_lt j) hv
    (hzV (hpt _ (ZMod.val_lt i)) (hpt _ (ZMod.val_lt j)) (by simp only; rw [hdi, hdj, hij]))

end Minimality

end
