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

/-- The tilted unimodality criterion with an open condition on the depths that
forces a single strict local maximum of `s z`; the depths along the cycle need
not be distinct. -/
theorem isRupert_of_tilted_localMax (V : Finset ℝ³) (u₀ v : ℝ³) (hu₀ : u₀ ≠ 0) {k : ℕ}
    [NeZero k] (hk : 3 ≤ k) (x : ZMod k → ℝ³) (hxV : ∀ i, x i ∈ V)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 → TiltSign (x (i + 1) - x i) (x j - x i) u₀ v)
    (hrest : ∀ y ∈ V, (∀ j, y ≠ x j) → ∀ i, TiltSign (x (i + 1) - x i) (y - x i) u₀ v)
    (s : ℝ) (hs : s = 1 ∨ s = -1)
    (P : (ZMod k → ℝ) → Prop) (hPo : IsOpen {z | P z})
    (hPs : ∀ z : ZMod k → ℝ, ∀ c : ℝ, 0 < c → P z → P (fun i => c * z i))
    (hP0 : P fun i => ⟪x i, u₀⟫)
    (hPu : ∀ z, P z → ∀ a b : ZMod k, s * z (a - 1) < s * z a → s * z (a + 1) < s * z a →
      s * z (b - 1) < s * z b → s * z (b + 1) < s * z b → a = b) : IsRupert V := by
  refine isRupert_of_tilted_unimodal' V u₀ v hu₀ hk x hxV hcyc hrest P hPo hPs ?_ ?_
  · have hc : Continuous fun ε : ℝ => fun i => ⟪x i, u₀ + ε • v⟫ := by fun_prop
    have := hc.continuousAt (x := 0) |>.preimage_mem_nhds (hPo.mem_nhds (by simpa using hP0))
    exact nhdsWithin_le_nhds this
  · intro z hz hP
    rcases hs with rfl | rfl
    · exact isCyclicUnimodal_of_localMax_unique (by omega) z hz
        (fun a b h1 h2 h3 h4 => hPu z hP a b (by linarith) (by linarith) (by linarith) (by linarith))
    · exact isCyclicUnimodal_of_localMin_unique (by omega) z hz
        (fun a b h1 h2 h3 h4 => hPu z hP a b (by linarith) (by linarith) (by linarith) (by linarith))

/-- The hypotheses of `tri_localMax_unique` for `s z`, as an open, scale-invariant
condition on `z`. -/
def TriSeq (m n : ℕ) (s : ℝ) (z : ZMod (m + n + 1) → ℝ) : Prop :=
  (∀ l ∈ Finset.Ioo 0 m, s * z ((l - 1 : ℕ) : ZMod (m + n + 1)) < s * z (l : ZMod (m + n + 1)) ∨
      s * z ((l + 1 : ℕ) : ZMod (m + n + 1)) < s * z (l : ZMod (m + n + 1))) ∧
    (∀ l ∈ Finset.Icc (m + 2) (m + n),
      s * z (l : ZMod (m + n + 1)) < s * z ((l - 1 : ℕ) : ZMod (m + n + 1)) ∨
      s * z (l : ZMod (m + n + 1)) < s * z ((l + 1 : ℕ) : ZMod (m + n + 1))) ∧
    s * z ((m + 1 : ℕ) : ZMod (m + n + 1)) < s * z (m : ZMod (m + n + 1))

theorem isOpen_triSeq (m n : ℕ) (s : ℝ) : IsOpen {z | TriSeq m n s z} := by
  have c : ∀ a : ZMod (m + n + 1), Continuous fun z : ZMod (m + n + 1) → ℝ => s * z a :=
    fun a => continuous_const.mul (continuous_apply a)
  have e : {z | TriSeq m n s z} =
      (⋂ l ∈ Finset.Ioo 0 m, ({z : ZMod (m + n + 1) → ℝ | s * z ((l - 1 : ℕ) : ZMod (m + n + 1)) <
        s * z (l : ZMod (m + n + 1))} ∪ {z | s * z ((l + 1 : ℕ) : ZMod (m + n + 1)) <
        s * z (l : ZMod (m + n + 1))})) ∩
      ((⋂ l ∈ Finset.Icc (m + 2) (m + n), ({z : ZMod (m + n + 1) → ℝ |
        s * z (l : ZMod (m + n + 1)) < s * z ((l - 1 : ℕ) : ZMod (m + n + 1))} ∪
        {z | s * z (l : ZMod (m + n + 1)) < s * z ((l + 1 : ℕ) : ZMod (m + n + 1))})) ∩
      {z | s * z ((m + 1 : ℕ) : ZMod (m + n + 1)) < s * z (m : ZMod (m + n + 1))}) := by
    ext z; simp only [TriSeq, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_union]
  rw [e]
  refine (isOpen_biInter_finset fun l _ => ?_).inter
    ((isOpen_biInter_finset fun l _ => ?_).inter (isOpen_lt (c _) (c _)))
  · exact (isOpen_lt (c _) (c _)).union (isOpen_lt (c _) (c _))
  · exact (isOpen_lt (c _) (c _)).union (isOpen_lt (c _) (c _))

theorem triSeq_smul {m n : ℕ} {s : ℝ} {z : ZMod (m + n + 1) → ℝ} {c : ℝ} (hc : 0 < c)
    (h : TriSeq m n s z) : TriSeq m n s (fun i => c * z i) := by
  have k : ∀ a b : ZMod (m + n + 1), s * z a < s * z b → s * (c * z a) < s * (c * z b) := by
    intro a b hab
    rw [show s * (c * z a) = c * (s * z a) by ring, show s * (c * z b) = c * (s * z b) by ring]
    exact mul_lt_mul_of_pos_left hab hc
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun l hl => (h1 l hl).imp (k _ _) (k _ _), fun l hl => (h2 l hl).imp (k _ _) (k _ _),
    k _ _ h3⟩

theorem triSeq_localMax {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) {s : ℝ} {z : ZMod (m + n + 1) → ℝ}
    (h : TriSeq m n s z) : ∀ a b : ZMod (m + n + 1), s * z (a - 1) < s * z a →
      s * z (a + 1) < s * z a → s * z (b - 1) < s * z b → s * z (b + 1) < s * z b → a = b :=
  tri_localMax_unique hm hn (fun i => s * z i)
    (fun l h1 h2 => min_lt_iff.mpr (h.1 l (Finset.mem_Ioo.mpr ⟨by omega, h2⟩)))
    (fun l h1 h2 => lt_max_iff.mpr (h.2.1 l (Finset.mem_Icc.mpr ⟨h1, h2⟩))) h.2.2

end Minimality

end
