module

public import Minimality.TriShadowMid

@[expose] public section

/-!
# Lemma T for the two non-mixed tilt arcs (both vertical far edges)

FEWER-FACES-PROOFS.md Proposition 24.12: the two arcs `(−, +, −)` and `(+, −, +)` of Theorem 24.1.
In the oblique frame of Lemma T (view `ez`, shadow triangle `O, O + A r1, O + B r2`) the tilt is
`s (α r1 + β r2)` with `α, β > 0`, `s = ±1`: it points into the shadow (`s = 1`) or out of it
(`s = -1`) across both rays, so both chains have the same sign `s` (upper for `s = 1`, lower for
`s = -1`).  Both vertical far edges, over `A` and over `B`, are cycle edges:

`C1 0, …, C1 m = P, M1, M2, Q = C2 n, …, C2 1`  (then back to the apex),

with `M1` the other end of the vertical over `A` (`s z_{M1} < s z_P`) and `M2` the other end of the
vertical over `B` (`s z_{M2} < s z_Q`).  The far side of the shadow is the three segments
`P M1` (vertical), `M1 M2` (the level edge, a chord), `M2 Q` (vertical).  The depths `s z` along the
cycle have no local minimum except possibly at `M1`, `M2` (at most one of the two, whichever way
a tie between them is broken), provided the apex is strictly above one of its two neighbours
(`s z_apex > s z_{C1 1}` or `> s z_{C2 1}`): `v` is not below both its `s`-neighbours.  The
tests of the three far-side edges do not depend on the ratio `α / β`.
-/

namespace Minimality

open Finset Filter Topology
open scoped RealInnerProductSpace

/-- **The non-mixed cycle has at most one local minimum.**  Positions `0, …, m` carry the concave
chain (apex at `0`, the far end `P` at `m`), positions `m + 1`, `m + 2` the middle vertices
`M1`, `M2`, position `m + 3` the far end `Q` of the second chain, whose reversed chain occupies
`m + 3, …, m + n + 2` (then the apex again).  No position is a local minimum except `m + 1`,
`m + 2`, and these cannot both be. -/
theorem nm_localMin_unique {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (w : ZMod (m + n + 3) → ℝ)
    (hchain1 : ∀ l : ℕ, 1 ≤ l → l < m →
      w ((l - 1 : ℕ) : ZMod (m + n + 3)) < w (l : ZMod (m + n + 3)) ∨
        w ((l + 1 : ℕ) : ZMod (m + n + 3)) < w (l : ZMod (m + n + 3)))
    (hM1 : w ((m + 1 : ℕ) : ZMod (m + n + 3)) < w (m : ZMod (m + n + 3)))
    (hM2 : w ((m + 2 : ℕ) : ZMod (m + n + 3)) < w ((m + 3 : ℕ) : ZMod (m + n + 3)))
    (hchain2 : ∀ l : ℕ, m + 4 ≤ l → l ≤ m + n + 2 →
      w ((l - 1 : ℕ) : ZMod (m + n + 3)) < w (l : ZMod (m + n + 3)) ∨
        w ((l + 1 : ℕ) : ZMod (m + n + 3)) < w (l : ZMod (m + n + 3)))
    (hapex : w (1 : ZMod (m + n + 3)) < w (0 : ZMod (m + n + 3)) ∨
        w ((m + n + 2 : ℕ) : ZMod (m + n + 3)) < w (0 : ZMod (m + n + 3))) :
    ∀ a b : ZMod (m + n + 3), w a < w (a - 1) → w a < w (a + 1) →
      w b < w (b - 1) → w b < w (b + 1) → a = b := by
  have : NeZero (m + n + 3) := ⟨by omega⟩
  have hsub : ∀ l : ℕ, 1 ≤ l → ((l : ZMod (m + n + 3)) - 1) = ((l - 1 : ℕ) : ZMod (m + n + 3)) := by
    intro l hl; rw [Nat.cast_sub hl]; simp
  have hadd : ∀ l : ℕ, ((l : ZMod (m + n + 3)) + 1) = ((l + 1 : ℕ) : ZMod (m + n + 3)) := by
    intro l; simp
  have hzero : ((0 : ZMod (m + n + 3)) - 1) = ((m + n + 2 : ℕ) : ZMod (m + n + 3)) := by
    have h := ZMod.natCast_self (m + n + 3)
    rw [show m + n + 3 = (m + n + 2) + 1 from rfl, Nat.cast_succ] at h
    linear_combination -h
  have cand : ∀ a : ZMod (m + n + 3), w a < w (a - 1) → w a < w (a + 1) →
      a = ((m + 1 : ℕ) : ZMod (m + n + 3)) ∨ a = ((m + 2 : ℕ) : ZMod (m + n + 3)) := by
    intro a h1 h2
    obtain ⟨l, hl, rfl⟩ : ∃ l, l < m + n + 3 ∧ (l : ZMod (m + n + 3)) = a :=
      ⟨a.val, ZMod.val_lt a, ZMod.natCast_zmod_val a⟩
    rw [hadd] at h2
    by_cases h0 : l = 0
    · exfalso
      subst h0
      simp only [Nat.cast_zero, hzero, zero_add] at h1 h2 hapex
      simp only [Nat.cast_one] at h2
      rcases hapex with h | h <;> linarith
    by_cases hA : l < m
    · exfalso
      rw [hsub l (by omega)] at h1
      rcases hchain1 l (by omega) hA with h | h <;> linarith
    by_cases hB : l = m
    · exfalso
      subst hB
      linarith
    by_cases hC : l = m + 1
    · left; rw [hC]
    by_cases hD : l = m + 2
    · right; rw [hD]
    by_cases hE : l = m + 3
    · exfalso
      subst hE
      rw [hsub (m + 3) (by omega), show m + 3 - 1 = m + 2 by omega] at h1
      linarith
    · exfalso
      rw [hsub l (by omega)] at h1
      rcases hchain2 l (by omega) (by omega) with h | h <;> linarith
  intro a b h1 h2 h3 h4
  rcases cand a h1 h2 with rfl | rfl <;> rcases cand b h3 h4 with rfl | rfl
  · rfl
  · exfalso
    rw [hadd (m + 1)] at h2
    rw [hsub (m + 2) (by omega), show m + 2 - 1 = m + 1 by omega] at h3
    linarith
  · exfalso
    rw [hadd (m + 1)] at h4
    rw [hsub (m + 2) (by omega), show m + 2 - 1 = m + 1 by omega] at h1
    linarith
  · rfl


/-- A concave chain has no weak interior local minimum: the three points `x0 < x1 < x2` with
the middle one on the `s`-side of the chord. -/
theorem chain_notmin {s x0 x1 x2 y0 y1 y2 : ℝ} (h01 : x0 < x1) (h12 : x1 < x2)
    (hside : s * ((x1 - x0) * (y2 - y0) - (y1 - y0) * (x2 - x0)) < 0) :
    s * y0 < s * y1 ∨ s * y2 < s * y1 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨c1, c2⟩ := hcon
  nlinarith [mul_nonneg (sub_nonneg.mpr h01.le) (sub_nonneg.mpr c2),
    mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr c1) (sub_nonpos.mpr h12.le)]

/-- The open, scale-invariant condition on the depths along the non-mixed cycle. -/
def NmSeq (m n : ℕ) (s : ℝ) (z : ZMod (m + n + 3) → ℝ) : Prop :=
  (∀ l ∈ Finset.Ioo 0 m, s * z ((l - 1 : ℕ) : ZMod (m + n + 3)) < s * z (l : ZMod (m + n + 3)) ∨
      s * z ((l + 1 : ℕ) : ZMod (m + n + 3)) < s * z (l : ZMod (m + n + 3))) ∧
    s * z ((m + 1 : ℕ) : ZMod (m + n + 3)) < s * z (m : ZMod (m + n + 3)) ∧
    s * z ((m + 2 : ℕ) : ZMod (m + n + 3)) < s * z ((m + 3 : ℕ) : ZMod (m + n + 3)) ∧
    (∀ l ∈ Finset.Icc (m + 4) (m + n + 2),
      s * z ((l - 1 : ℕ) : ZMod (m + n + 3)) < s * z (l : ZMod (m + n + 3)) ∨
      s * z ((l + 1 : ℕ) : ZMod (m + n + 3)) < s * z (l : ZMod (m + n + 3))) ∧
    (s * z (1 : ZMod (m + n + 3)) < s * z (0 : ZMod (m + n + 3)) ∨
      s * z ((m + n + 2 : ℕ) : ZMod (m + n + 3)) < s * z (0 : ZMod (m + n + 3)))

theorem isOpen_nmSeq (m n : ℕ) (s : ℝ) : IsOpen {z | NmSeq m n s z} := by
  have c : ∀ a : ZMod (m + n + 3), Continuous fun z : ZMod (m + n + 3) → ℝ => s * z a :=
    fun a => continuous_const.mul (continuous_apply a)
  have e : {z | NmSeq m n s z} =
      (⋂ l ∈ Finset.Ioo 0 m, ({z : ZMod (m + n + 3) → ℝ | s * z ((l - 1 : ℕ) : ZMod (m + n + 3)) <
        s * z (l : ZMod (m + n + 3))} ∪ {z | s * z ((l + 1 : ℕ) : ZMod (m + n + 3)) <
        s * z (l : ZMod (m + n + 3))})) ∩
      ({z | s * z ((m + 1 : ℕ) : ZMod (m + n + 3)) < s * z (m : ZMod (m + n + 3))} ∩
      ({z | s * z ((m + 2 : ℕ) : ZMod (m + n + 3)) < s * z ((m + 3 : ℕ) : ZMod (m + n + 3))} ∩
      ((⋂ l ∈ Finset.Icc (m + 4) (m + n + 2), ({z : ZMod (m + n + 3) → ℝ |
        s * z ((l - 1 : ℕ) : ZMod (m + n + 3)) < s * z (l : ZMod (m + n + 3))} ∪
        {z | s * z ((l + 1 : ℕ) : ZMod (m + n + 3)) < s * z (l : ZMod (m + n + 3))})) ∩
      ({z : ZMod (m + n + 3) → ℝ | s * z (1 : ZMod (m + n + 3)) < s * z (0 : ZMod (m + n + 3))} ∪
        {z | s * z ((m + n + 2 : ℕ) : ZMod (m + n + 3)) < s * z (0 : ZMod (m + n + 3))})))) := by
    ext z
    simp only [NmSeq, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_union]
  rw [e]
  refine (isOpen_biInter_finset fun l _ => ?_).inter
    ((isOpen_lt (c _) (c _)).inter ((isOpen_lt (c _) (c _)).inter
    ((isOpen_biInter_finset fun l _ => ?_).inter ?_)))
  · exact (isOpen_lt (c _) (c _)).union (isOpen_lt (c _) (c _))
  · exact (isOpen_lt (c _) (c _)).union (isOpen_lt (c _) (c _))
  · exact (isOpen_lt (c _) (c _)).union (isOpen_lt (c _) (c _))

theorem nmSeq_smul {m n : ℕ} {s : ℝ} {z : ZMod (m + n + 3) → ℝ} {c : ℝ} (hc : 0 < c)
    (h : NmSeq m n s z) : NmSeq m n s (fun i => c * z i) := by
  have k : ∀ a b : ZMod (m + n + 3), s * z a < s * z b → s * (c * z a) < s * (c * z b) := by
    intro a b hab
    rw [show s * (c * z a) = c * (s * z a) by ring, show s * (c * z b) = c * (s * z b) by ring]
    exact mul_lt_mul_of_pos_left hab hc
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨fun l hl => (h1 l hl).imp (k _ _) (k _ _), k _ _ h2, k _ _ h3,
    fun l hl => (h4 l hl).imp (k _ _) (k _ _), h5.imp (k _ _) (k _ _)⟩

theorem nmSeq_localMin {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) {s : ℝ}
    {z : ZMod (m + n + 3) → ℝ} (h : NmSeq m n s z) :
    ∀ a b : ZMod (m + n + 3), (-s) * z (a - 1) < (-s) * z a → (-s) * z (a + 1) < (-s) * z a →
      (-s) * z (b - 1) < (-s) * z b → (-s) * z (b + 1) < (-s) * z b → a = b := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  intro a b ha1 ha2 hb1 hb2
  exact nm_localMin_unique hm hn (fun i => s * z i)
    (fun l hl1 hl2 => h1 l (Finset.mem_Ioo.mpr ⟨by omega, hl2⟩)) h2 h3
    (fun l hl1 hl2 => h4 l (Finset.mem_Icc.mpr ⟨hl1, hl2⟩)) h5 a b
    (by linarith) (by linarith) (by linarith) (by linarith)


/-- The cycle position `v` of the non-mixed cycle: `C1 v` for `v ≤ m`, then `M1` over the first
far end, `M2` over the second, then `C2 (m + n + 3 - v)`. -/
noncomputable def triPtN (O r1 r2 : ℝ²) (m n : ℕ) (ca cz cb dz : ℕ → ℝ) (zM1 zM2 : ℝ) (v : ℕ) :
    ℝ³ :=
  if v ≤ m then oblPt O r1 r2 (ca v) 0 (cz v)
  else if v = m + 1 then oblPt O r1 r2 (ca m) 0 zM1
  else if v = m + 2 then oblPt O r1 r2 0 (cb n) zM2
  else oblPt O r1 r2 0 (cb (m + n + 3 - v)) (dz (m + n + 3 - v))

/-- Its depth. -/
noncomputable def triZN (m n : ℕ) (cz dz : ℕ → ℝ) (zM1 zM2 : ℝ) (v : ℕ) : ℝ :=
  if v ≤ m then cz v else if v = m + 1 then zM1 else if v = m + 2 then zM2
  else dz (m + n + 3 - v)

set_option maxHeartbeats 4000000 in
/-- **Lemma T in the oblique frame, the non-mixed tilt arcs** (FEWER-FACES-PROOFS.md
Proposition 24.12, the arcs `(−, +, −)` for `s = 1` and `(+, −, +)` for `s = -1`).  Both chains
carry the sign `s`; the tilt is `s (α r1 + β r2)`.  The cycle is `C1 0, …, C1 m, M1, M2, C2 n,
…, C2 1`, with `M1` over the far end `A` of the first chain below `P = C1 m` (`s z_{M1} < s z_P`)
and `M2` over the far end of the second chain below `Q = C2 n`.  The tests of the three far-side
edges are the hypotheses `TiltOK` of `hVc`.  The depths have at most one local minimum of
`s z` (at `M1` or `M2`) provided the apex is strictly above one of its two neighbours
(`hapex`). -/
theorem isRupert_triShadow_nm (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) {m n : ℕ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) (s : ℝ) (hs : s = 1 ∨ s = -1) {α β : ℝ} (hα : 0 < α)
    (hβ : 0 < β) (ca cz cb dz : ℕ → ℝ)
    (hca0 : ca 0 = 0) (hcb0 : cb 0 = 0) (hdz0 : dz 0 = cz 0)
    (hca : ∀ l, l < m → ca l < ca (l + 1)) (hcb : ∀ l, l < n → cb l < cb (l + 1))
    (V : Finset ℝ³) (zM1 zM2 : ℝ) (hM1V : oblPt O r1 r2 (ca m) 0 zM1 ∈ V)
    (hM2V : oblPt O r1 r2 0 (cb n) zM2 ∈ V)
    (hC1V : ∀ l, l ≤ m → oblPt O r1 r2 (ca l) 0 (cz l) ∈ V)
    (hC2V : ∀ l, l ≤ n → oblPt O r1 r2 0 (cb l) (dz l) ∈ V)
    (hVc : ∀ y ∈ V, ∃ a b z, y = oblPt O r1 r2 a b z ∧ 0 ≤ a ∧ 0 ≤ b ∧
      (TiltOK (ca m) 0 (cz m) (ca m) 0 zM1 a b z (s * α) (s * β) ∨
        y = oblPt O r1 r2 (ca m) 0 (cz m) ∨ y = oblPt O r1 r2 (ca m) 0 zM1) ∧
      (TiltOK (ca m) 0 zM1 0 (cb n) zM2 a b z (s * α) (s * β) ∨
        y = oblPt O r1 r2 (ca m) 0 zM1 ∨ y = oblPt O r1 r2 0 (cb n) zM2) ∧
      (TiltOK 0 (cb n) zM2 0 (cb n) (dz n) a b z (s * α) (s * β) ∨
        y = oblPt O r1 r2 0 (cb n) zM2 ∨ y = oblPt O r1 r2 0 (cb n) (dz n)) ∧
      (b = 0 → ∀ l, l < m → y ≠ oblPt O r1 r2 (ca l) 0 (cz l) →
        y ≠ oblPt O r1 r2 (ca (l + 1)) 0 (cz (l + 1)) →
        s * ((ca (l + 1) - ca l) * (z - cz l) - (cz (l + 1) - cz l) * (a - ca l)) < 0) ∧
      (a = 0 → ∀ l, l < n → y ≠ oblPt O r1 r2 0 (cb (l + 1)) (dz (l + 1)) →
        y ≠ oblPt O r1 r2 0 (cb l) (dz l) →
        s * ((cb (l + 1) - cb l) * (z - dz l) - (dz (l + 1) - dz l) * (b - cb l)) < 0))
    (hPM : s * zM1 < s * cz m) (hQM : s * zM2 < s * dz n)
    (hapex : s * cz 1 < s * cz 0 ∨ s * dz 1 < s * dz 0) : IsRupert V := by
  have hNZ : NeZero (m + n + 3) := ⟨by omega⟩
  have hval : ∀ v : ℕ, v < m + n + 3 → ((v : ZMod (m + n + 3))).val = v := fun v hv => by
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
  have hApos : 0 < ca m := by have := hcam 0 m (by omega) le_rfl; rwa [hca0] at this
  have hBpos : 0 < cb n := by have := hcbm 0 n (by omega) le_rfl; rwa [hcb0] at this
  have hzM1 : zM1 ≠ cz m := fun e => by rw [e] at hPM; exact lt_irrefl _ hPM
  have hzM2 : zM2 ≠ dz n := fun e => by rw [e] at hQM; exact lt_irrefl _ hQM
  set M1 : ℝ³ := oblPt O r1 r2 (ca m) 0 zM1 with hM1def
  set M2 : ℝ³ := oblPt O r1 r2 0 (cb n) zM2 with hM2def
  set x : ZMod (m + n + 3) → ℝ³ := fun i => triPtN O r1 r2 m n ca cz cb dz zM1 zM2 i.val with hx
  -- positions
  have hxC1 : ∀ v, v ≤ m → x (v : ZMod (m + n + 3)) = oblPt O r1 r2 (ca v) 0 (cz v) := by
    intro v hv; simp only [hx, hval v (by omega), triPtN, hv, ite_true]
  have hxM1 : x ((m + 1 : ℕ) : ZMod (m + n + 3)) = M1 := by
    simp only [hx, hval (m + 1) (by omega), triPtN, show ¬ m + 1 ≤ m by omega, ite_false,
      ite_true]
    exact hM1def.symm
  have hxM2 : x ((m + 2 : ℕ) : ZMod (m + n + 3)) = M2 := by
    simp only [hx, hval (m + 2) (by omega), triPtN, show ¬ m + 2 ≤ m by omega,
      show ¬ m + 2 = m + 1 by omega, ite_false, ite_true]
    exact hM2def.symm
  have hxC2 : ∀ l, l < n → x ((m + n + 2 - l : ℕ) : ZMod (m + n + 3)) =
      oblPt O r1 r2 0 (cb (l + 1)) (dz (l + 1)) := by
    intro l hl
    simp only [hx, hval (m + n + 2 - l) (by omega), triPtN, show ¬ m + n + 2 - l ≤ m by omega,
      show ¬ m + n + 2 - l = m + 1 by omega, show ¬ m + n + 2 - l = m + 2 by omega, ite_false]
    rw [show m + n + 3 - (m + n + 2 - l) = l + 1 by omega]
  have hapexpt : oblPt O r1 r2 (ca 0) 0 (cz 0) = oblPt O r1 r2 0 (cb 0) (dz 0) := by
    rw [hca0, hcb0, hdz0]
  have hdepth : ∀ i : ZMod (m + n + 3), ⟪x i, ez⟫ = triZN m n cz dz zM1 zM2 i.val := by
    intro i; simp only [hx, triPtN, triZN]; split_ifs <;> exact inner_oblPt_ez _ _ _ _ _ _
  have hM1ne : ∀ l, l ≤ m → M1 ≠ oblPt O r1 r2 (ca l) 0 (cz l) := by
    intro l hl he
    obtain ⟨e1, -, e3⟩ := oblPt_inj hρ he
    rcases hl.lt_or_eq with h | h
    · linarith [hcam l m h le_rfl]
    · subst h; exact hzM1 e3
  have hM2ne : ∀ l, 1 ≤ l → l ≤ n → M2 ≠ oblPt O r1 r2 0 (cb l) (dz l) := by
    intro l h1 hl he
    obtain ⟨-, e2, e3⟩ := oblPt_inj hρ he
    rcases hl.lt_or_eq with h | h
    · linarith [hcbm l n h le_rfl]
    · subst h; exact hzM2 e3
  have hxinj : Function.Injective x := by
    have pos : ∀ w, w < m + n + 3 → (w ≤ m ∧ x w = oblPt O r1 r2 (ca w) 0 (cz w)) ∨
        (w = m + 1 ∧ x w = M1) ∨ (w = m + 2 ∧ x w = M2) ∨
        (m + 3 ≤ w ∧ x w = oblPt O r1 r2 0 (cb (m + n + 3 - w)) (dz (m + n + 3 - w))) := by
      intro w hw
      by_cases h : w ≤ m
      · exact Or.inl ⟨h, hxC1 w h⟩
      by_cases h' : w = m + 1
      · subst h'; exact Or.inr (Or.inl ⟨rfl, hxM1⟩)
      by_cases h'' : w = m + 2
      · subst h''; exact Or.inr (Or.inr (Or.inl ⟨rfl, hxM2⟩))
      · refine Or.inr (Or.inr (Or.inr ⟨by omega, ?_⟩))
        have := hxC2 (m + n + 2 - w) (by omega)
        rwa [show m + n + 2 - (m + n + 2 - w) = w by omega,
          show m + n + 2 - w + 1 = m + n + 3 - w by omega] at this
    intro i j h
    obtain ⟨wi, hwi, rfl⟩ : ∃ w, w < m + n + 3 ∧ (w : ZMod (m + n + 3)) = i :=
      ⟨i.val, ZMod.val_lt i, ZMod.natCast_zmod_val i⟩
    obtain ⟨wj, hwj, rfl⟩ : ∃ w, w < m + n + 3 ∧ (w : ZMod (m + n + 3)) = j :=
      ⟨j.val, ZMod.val_lt j, ZMod.natCast_zmod_val j⟩
    suffices wi = wj by rw [this]
    rcases pos wi hwi with ⟨h1, e1⟩ | ⟨h1, e1⟩ | ⟨h1, e1⟩ | ⟨h1, e1⟩ <;>
      rcases pos wj hwj with ⟨h2, e2⟩ | ⟨h2, e2⟩ | ⟨h2, e2⟩ | ⟨h2, e2⟩ <;> rw [e1, e2] at h
    · have c := oblPt_inj hρ h
      rcases lt_trichotomy wi wj with l | l | l
      · exact absurd c.1 (hcam _ _ l h2).ne
      · exact l
      · exact absurd c.1 (hcam _ _ l h1).ne'
    · exact absurd h.symm (hM1ne wi h1)
    · have c := oblPt_inj hρ h; linarith [c.2.1]
    · have c := oblPt_inj hρ h
      have := hcbm 0 (m + n + 3 - wj) (by omega) (by omega); rw [hcb0] at this; linarith [c.2.1]
    · exact absurd h (hM1ne wj h2)
    · omega
    · have c := oblPt_inj hρ h; linarith [c.1]
    · have c := oblPt_inj hρ h; linarith [c.1]
    · have c := oblPt_inj hρ h; linarith [c.2.1]
    · have c := oblPt_inj hρ h; linarith [c.1]
    · omega
    · exact absurd h (hM2ne _ (by omega) (by omega))
    · have c := oblPt_inj hρ h
      have := hcbm 0 (m + n + 3 - wi) (by omega) (by omega); rw [hcb0] at this; linarith [c.2.1]
    · have c := oblPt_inj hρ h; linarith [c.1]
    · exact absurd h.symm (hM2ne _ (by omega) (by omega))
    · have c := oblPt_inj hρ h
      rcases lt_trichotomy (m + n + 3 - wi) (m + n + 3 - wj) with l | l | l
      · exact absurd c.2.1 (hcbm _ _ l (by omega)).ne
      · omega
      · exact absurd c.2.1 (hcbm _ _ l (by omega)).ne'
  -- the tilt
  set v : ℝ³ := oblPt 0 r1 r2 (s * α) (s * β) 0 with hv
  have key : ∀ {ap bp zp aq bq zq ay by' zy : ℝ},
      TiltOK ap bp zp aq bq zq ay by' zy (s * α) (s * β) →
      TiltSign (oblPt O r1 r2 aq bq zq - oblPt O r1 r2 ap bp zp)
        (oblPt O r1 r2 ay by' zy - oblPt O r1 r2 ap bp zp) ez v :=
    fun h => tiltSign_obl O r1 r2 hρ (s * α) (s * β) h
  have side1 : ∀ {ap aq zp zq ay zy : ℝ}, s * ((aq - ap) * (zy - zp) - (zq - zp) * (ay - ap)) < 0 →
      TiltOK ap 0 zp aq 0 zq ay 0 zy (s * α) (s * β) := by
    intro ap aq zp zq ay zy h
    apply tiltOK_side1_on
    rcases hs with rfl | rfl
    · left; exact ⟨by linarith, by linarith⟩
    · right; exact ⟨by linarith, by linarith⟩
  have side2 : ∀ {bp bq zp zq by' zy : ℝ},
      s * ((bp - bq) * (zy - zq) - (zp - zq) * (by' - bq)) < 0 →
      TiltOK 0 bp zp 0 bq zq 0 by' zy (s * α) (s * β) := by
    intro bp bq zp zq by' zy h
    apply tiltOK_side2_on
    rcases hs with rfl | rfl
    · left; exact ⟨by linarith, by linarith⟩
    · right; exact ⟨by linarith, by linarith⟩
  -- every test of Lemma 8.0
  have tests : ∀ y ∈ V, ∀ i : ZMod (m + n + 3), y ≠ x i → y ≠ x (i + 1) →
      TiltSign (x (i + 1) - x i) (y - x i) ez v := by
    intro y hy i hyi hyi1
    obtain ⟨a, b, z, rfl, ha, hb, hin1, hin2, hin3, hr1, hr2⟩ := hVc y hy
    obtain ⟨w, hwlt, rfl⟩ : ∃ w, w < m + n + 3 ∧ (w : ZMod (m + n + 3)) = i :=
      ⟨i.val, ZMod.val_lt i, ZMod.natCast_zmod_val i⟩
    have hsucc : ((w : ZMod (m + n + 3)) + 1) = ((w + 1 : ℕ) : ZMod (m + n + 3)) := by simp
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
    · -- the edge `P → M1`
      have hwm : w = m := by omega
      subst w
      rw [hxC1 m le_rfl] at hyi ⊢
      rw [hxM1] at hyi1 ⊢
      apply key
      rcases hin1 with hin | hin | hin
      · exact hin
      · exact absurd hin hyi
      · exact absurd hin hyi1
    rcases Nat.lt_or_ge w (m + 2) with h3 | h3
    · -- the edge `M1 → M2`
      have hwm : w = m + 1 := by omega
      subst w
      rw [hxM1] at hyi ⊢
      rw [hxM2] at hyi1 ⊢
      apply key
      rcases hin2 with hin | hin | hin
      · exact hin
      · exact absurd hin hyi
      · exact absurd hin hyi1
    rcases Nat.lt_or_ge w (m + 3) with h4 | h4
    · -- the edge `M2 → Q`
      have hwm : w = m + 2 := by omega
      subst w
      have e1 : x ((m + 2 + 1 : ℕ) : ZMod (m + n + 3)) = oblPt O r1 r2 0 (cb n) (dz n) := by
        rw [show m + 2 + 1 = m + n + 2 - (n - 1) by omega, hxC2 (n - 1) (by omega),
          show n - 1 + 1 = n by omega]
      rw [hxM2] at hyi ⊢
      rw [e1] at hyi1 ⊢
      apply key
      rcases hin3 with hin | hin | hin
      · exact hin
      · exact absurd hin hyi
      · exact absurd hin hyi1
    · -- a segment of `C2` (inward), the last one ending at the apex
      obtain ⟨l, hln, rfl⟩ : ∃ l, l < n ∧ m + n + 2 - l = w := ⟨m + n + 2 - w, by omega, by omega⟩
      have e1 : x ((m + n + 2 - l + 1 : ℕ) : ZMod (m + n + 3)) = oblPt O r1 r2 0 (cb l) (dz l) := by
        rcases Nat.eq_zero_or_pos l with hl0 | hl0
        · subst hl0
          rw [show m + n + 2 - 0 + 1 = m + n + 3 by omega, ZMod.natCast_self, ← hapexpt,
            show (0 : ZMod (m + n + 3)) = ((0 : ℕ) : ZMod (m + n + 3)) by simp]
          exact hxC1 0 (Nat.zero_le _)
        · rw [show m + n + 2 - l + 1 = m + n + 2 - (l - 1) by omega, hxC2 (l - 1) (by omega),
            show l - 1 + 1 = l by omega]
      rw [hxC2 l hln] at hyi ⊢
      rw [e1] at hyi1 ⊢
      apply key
      rcases ha.lt_or_eq with ha | ha
      · exact tiltOK_side2_off (hcb _ hln) ha
      · subst ha; exact side2 (hr2 rfl _ hln hyi hyi1)
  have hxV : ∀ i, x i ∈ V := by
    intro i; simp only [hx, triPtN]; split_ifs with h h' h''
    · exact hC1V _ h
    · exact hM1V
    · exact hM2V
    · exact hC2V _ (by have := ZMod.val_lt i; omega)
  have hcyc : ∀ i j : ZMod (m + n + 3), j ≠ i → j ≠ i + 1 →
      TiltSign (x (i + 1) - x i) (x j - x i) ez v := by
    intro i j h1 h2
    exact tests (x j) (hxV j) i (fun h => h1 (hxinj h)) (fun h => h2 (hxinj h))
  have hrest : ∀ y ∈ V, (∀ j, y ≠ x j) → ∀ i,
      TiltSign (x (i + 1) - x i) (y - x i) ez v :=
    fun y hy hyx i => tests y hy i (hyx i) (hyx (i + 1))
  -- the depths
  set Z : ZMod (m + n + 3) → ℝ := fun i => triZN m n cz dz zM1 zM2 i.val with hZ
  have hZpos : ∀ l, l < m + n + 3 → Z (l : ZMod (m + n + 3)) = triZN m n cz dz zM1 zM2 l := by
    intro l hl; simp only [hZ, hval l hl]
  have hZ1 : ∀ l, l ≤ m → Z (l : ZMod (m + n + 3)) = cz l := by
    intro l hl; rw [hZpos l (by omega)]; simp [triZN, hl]
  have hZM1 : Z ((m + 1 : ℕ) : ZMod (m + n + 3)) = zM1 := by
    rw [hZpos _ (by omega)]; simp [triZN]
  have hZM2 : Z ((m + 2 : ℕ) : ZMod (m + n + 3)) = zM2 := by
    rw [hZpos _ (by omega)]; simp [triZN]
  have hZQ : Z ((m + 3 : ℕ) : ZMod (m + n + 3)) = dz n := by
    rw [hZpos _ (by omega)]
    simp [triZN, show ¬ m + 3 ≤ m by omega, show ¬ m + 3 = m + 1 by omega,
      show ¬ m + 3 = m + 2 by omega, show m + n + 3 - (m + 3) = n by omega]
  have hZ2 : ∀ l, m + 3 ≤ l → l ≤ m + n + 2 → Z (l : ZMod (m + n + 3)) = dz (m + n + 3 - l) := by
    intro l h1 h2; rw [hZpos l (by omega)]
    simp [triZN, show ¬ l ≤ m by omega, show ¬ l = m + 1 by omega, show ¬ l = m + 2 by omega]
  have hZk : Z ((m + n + 3 : ℕ) : ZMod (m + n + 3)) = dz 0 := by
    rw [ZMod.natCast_self, show (0 : ZMod (m + n + 3)) = ((0 : ℕ) : ZMod (m + n + 3)) by simp,
      hZ1 0 (Nat.zero_le _), hdz0]
  -- chain coordinates from `hVc`
  have coords1 : ∀ l, l ≤ m → ∀ j, j < m → oblPt O r1 r2 (ca l) 0 (cz l) ≠
      oblPt O r1 r2 (ca j) 0 (cz j) → oblPt O r1 r2 (ca l) 0 (cz l) ≠
      oblPt O r1 r2 (ca (j + 1)) 0 (cz (j + 1)) →
      s * ((ca (j + 1) - ca j) * (cz l - cz j) - (cz (j + 1) - cz j) * (ca l - ca j)) < 0 := by
    intro l hl j hj h1 h2
    obtain ⟨a, b, z, he, -, -, -, -, -, hr1, -⟩ := hVc _ (hC1V l hl)
    obtain ⟨ea, eb, ez'⟩ := oblPt_inj hρ he
    subst ea ez'
    exact hr1 eb.symm j hj (he ▸ h1) (he ▸ h2)
  have coords2 : ∀ l, l ≤ n → ∀ j, j < n → oblPt O r1 r2 0 (cb l) (dz l) ≠
      oblPt O r1 r2 0 (cb (j + 1)) (dz (j + 1)) → oblPt O r1 r2 0 (cb l) (dz l) ≠
      oblPt O r1 r2 0 (cb j) (dz j) →
      s * ((cb (j + 1) - cb j) * (dz l - dz j) - (dz (j + 1) - dz j) * (cb l - cb j)) < 0 := by
    intro l hl j hj h1 h2
    obtain ⟨a, b, z, he, -, -, -, -, -, -, hr2⟩ := hVc _ (hC2V l hl)
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
  -- the hypotheses of the sequence lemma for `s Z`
  have hT : NmSeq m n s Z := by
    refine ⟨fun l hl => ?_, ?_, ?_, fun l hl => ?_, ?_⟩
    · obtain ⟨h1, h2⟩ := Finset.mem_Ioo.mp hl
      rw [hZ1 _ (by omega), hZ1 _ (by omega), hZ1 _ (by omega)]
      have hc := coords1 (l + 1) (by omega) (l - 1) (by omega)
        (ne1 _ _ (by omega) (by omega) (by omega))
        (by rw [show l - 1 + 1 = l by omega]; exact ne1 _ _ (by omega) (by omega) (by omega))
      rw [show l - 1 + 1 = l by omega] at hc
      exact chain_notmin (hcam (l - 1) l (by omega) (by omega))
        (hcam l (l + 1) (by omega) (by omega)) (by linarith)
    · rw [hZM1, hZ1 m le_rfl]; exact hPM
    · rw [hZM2, hZQ]; exact hQM
    · obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hl
      set j := m + n + 3 - l with hj
      have hj1 : 1 ≤ j := by omega
      have hjn : j + 1 ≤ n := by omega
      rw [hZ2 l (by omega) (by omega), hZ2 (l - 1) (by omega) (by omega),
        show m + n + 3 - (l - 1) = j + 1 by omega]
      have hnext : Z ((l + 1 : ℕ) : ZMod (m + n + 3)) = dz (j - 1) := by
        rcases Nat.lt_or_ge l (m + n + 2) with hl' | hl'
        · rw [hZ2 (l + 1) (by omega) (by omega), show m + n + 3 - (l + 1) = j - 1 by omega]
        · rw [show l + 1 = m + n + 3 by omega, hZk, show j - 1 = 0 by omega]
      rw [hnext]
      have hc := coords2 (j + 1) (by omega) (j - 1) (by omega)
        (ne2 _ _ (by omega) (by omega) (by omega)) (ne2 _ _ (by omega) (by omega) (by omega))
      rw [show j - 1 + 1 = j by omega] at hc
      have := chain_notmin (s := s) (y0 := dz (j - 1)) (y1 := dz j) (y2 := dz (j + 1))
        (hcbm (j - 1) j (by omega) (by omega)) (hcbm j (j + 1) (by omega) (by omega))
        (by linarith)
      exact this.symm
    · rw [show (1 : ZMod (m + n + 3)) = ((1 : ℕ) : ZMod (m + n + 3)) by simp,
        show (0 : ZMod (m + n + 3)) = ((0 : ℕ) : ZMod (m + n + 3)) by simp,
        hZ1 1 (by omega), hZ1 0 (Nat.zero_le _), hZpos (m + n + 2) (by omega)]
      rw [show triZN m n cz dz zM1 zM2 (m + n + 2) = dz 1 by
        unfold triZN
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
          show m + n + 3 - (m + n + 2) = 1 by omega]]
      rw [hdz0] at hapex
      exact hapex
  have hez : (ez : ℝ³) ≠ 0 := by
    intro h; have := congrArg (fun x : ℝ³ => x 2) h; simp [ez] at this
  have hs' : -s = 1 ∨ -s = -1 := by
    rcases hs with rfl | rfl
    · right; norm_num
    · left; norm_num
  exact isRupert_of_tilted_localMax V ez v hez (k := m + n + 3) (by omega) x hxV hcyc hrest (-s) hs'
    (NmSeq m n s) (isOpen_nmSeq m n s) (fun z c hc hz => nmSeq_smul hc hz)
    (by rw [show (fun i => ⟪x i, ez⟫) = Z from funext hdepth]; exact hT)
    (fun z hz => nmSeq_localMin hm hn hz)

end Minimality

end
