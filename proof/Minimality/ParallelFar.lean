module

public import Minimality.TriShadow2Chord
public import Minimality.HullChain
public import Minimality.TriShadowChord

@[expose] public section

/-!
# A segment parallel to the view line at a far end (codimension-2 tail)

Lemma T's general position includes "no segment of `V` parallel to the view
line". At a far end `(ca m, 0, cz m)` of the first face's chain, a second
vertex `(ca m, 0, z)` of that face on the same vertical (a segment parallel
to the view line) lies on the far edge's line at the untilted view. It is
still strictly inside the tilted shadow when it is on the chain's side
(`s * (z - cz m) < 0`) and the tilt `(-s α, s β)` of
`isRupert_triShadow2_tilt` leans toward the second face (`ca m * β < cb n * α`);
likewise at the second face's far end with the opposite ratio. Both at once
is Corollary T1's rectangle exception (FEWER-FACES-PROOFS.md §7). See
FEWER-FACES.md §11, step (ii).
-/

namespace Minimality

/-- A vertical companion of the first face's far end, on the chain's side. -/
theorem tiltOK_farComp1 {s A B zp zq zy α β : ℝ} (hc : s * (zy - zp) < 0)
    (hr : A * β < B * α) :
    TiltOK A 0 zp 0 B zq A 0 zy (-s * α) (s * β) := by
  right
  refine ⟨by ring, ?_⟩
  have e : (zq - zp) * ((A - A) * (s * β) - (0 - 0) * (-s * α)) -
      (zy - zp) * ((0 - A) * (s * β) - (B - 0) * (-s * α)) =
      (s * (zy - zp)) * (A * β - B * α) := by ring
  rw [e]
  exact mul_pos_of_neg_of_neg hc (by linarith)

/-- A vertical companion of the second face's far end, on that chain's side
(the second chain carries the sign `-s`). -/
theorem tiltOK_farComp2 {s A B zp zq zy α β : ℝ} (hc : 0 < s * (zy - zq))
    (hr : B * α < A * β) :
    TiltOK A 0 zp 0 B zq 0 B zy (-s * α) (s * β) := by
  right
  refine ⟨by ring, ?_⟩
  have e : (zq - zp) * ((0 - A) * (s * β) - (B - 0) * (-s * α)) -
      (zy - zp) * ((0 - A) * (s * β) - (B - 0) * (-s * α)) =
      (s * (zy - zq)) * (A * β - B * α) := by ring
  rw [e]
  exact mul_pos hc (by linarith)

/-- A chain as `ChainOK`, except that the far end need not be the unique
point of largest `a`: points of `Q` on its vertical lie on the chain's
side (`s * (z - cz m) < 0`), its vertical companions. -/
structure ChainOKc (Q : ℝ → ℝ → Prop) (z0 s : ℝ) (m : ℕ) (ca cz : ℕ → ℝ) : Prop where
  one_le : 1 ≤ m
  start : ca 0 = 0 ∧ cz 0 = z0
  inc : ∀ l, l < m → ca l < ca (l + 1)
  mem : ∀ l, l ≤ m → Q (ca l) (cz l)
  far : ∀ a z, Q a z → ¬ (a = ca m ∧ z = cz m) → a < ca m ∨ (a = ca m ∧ s * (z - cz m) < 0)
  side : ∀ a z, Q a z → ∀ l, l < m → ¬ (a = ca l ∧ z = cz l) → ¬ (a = ca (l + 1) ∧ z = cz (l + 1)) →
    s * ((ca (l + 1) - ca l) * (z - cz l) - (cz (l + 1) - cz l) * (a - ca l)) < 0

theorem ChainOK.toC {Q : ℝ → ℝ → Prop} {z0 s : ℝ} {m : ℕ} {ca cz : ℕ → ℝ}
    (C : ChainOK Q z0 s m ca cz) : ChainOKc Q z0 s m ca cz :=
  ⟨C.one_le, C.start, C.inc, C.mem, fun a z hq hn => Or.inl (C.far a z hq hn), C.side⟩

/-- **Chains when several points share a vertical.** As `exists_chainOK`,
without distinct `a`: build the chain on the top point (in the `s` sense) of
each vertical and lift; the lower points of a vertical are strictly on the
chain's side, and those under the far end are its vertical companions. -/
theorem exists_chainOKc (S : Finset (ℝ × ℝ)) (z0 : ℝ) (h0 : (0, z0) ∈ S)
    (hpos : ∀ q ∈ S, q ≠ (0, z0) → 0 < q.1) (hne : ∃ q ∈ S, q ≠ (0, z0))
    (hcol : ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → p ≠ r → q ≠ r →
      (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1) ≠ 0)
    (s : ℝ) (hs : s = 1 ∨ s = -1) :
    ∃ m ca cz, ChainOKc (fun a z => (a, z) ∈ S) z0 s m ca cz := by
  classical
  have hss : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  -- the top point of each vertical
  set T := S.filter (fun q => ∀ r ∈ S, r.1 = q.1 → s * r.2 ≤ s * q.2) with hT
  have hTS : ∀ q ∈ T, q ∈ S := fun q hq => (Finset.mem_filter.mp hq).1
  -- every point has a top on its vertical
  have top : ∀ q ∈ S, ∃ q' ∈ T, q'.1 = q.1 ∧ s * q.2 ≤ s * q'.2 := by
    intro q hq
    obtain ⟨q', hq', hmax⟩ := (S.filter (fun r => r.1 = q.1)).exists_max_image
      (fun r => s * r.2) ⟨q, Finset.mem_filter.mpr ⟨hq, rfl⟩⟩
    obtain ⟨hq'S, hq'1⟩ := Finset.mem_filter.mp hq'
    refine ⟨q', Finset.mem_filter.mpr ⟨hq'S, fun r hr e => ?_⟩, hq'1,
      hmax q (Finset.mem_filter.mpr ⟨hq, rfl⟩)⟩
    exact hmax r (Finset.mem_filter.mpr ⟨hr, by rw [e, hq'1]⟩)
  have hz0T : (0, z0) ∈ T := by
    refine Finset.mem_filter.mpr ⟨h0, fun r hr e => ?_⟩
    by_cases hr0 : r = (0, z0)
    · rw [hr0]
    · have := hpos r hr hr0; simp at e; linarith
  have hinjT : Set.InjOn Prod.fst (T : Set (ℝ × ℝ)) := by
    intro q hq q' hq' e
    have h1 := (Finset.mem_filter.mp hq).2 q' (hTS q' hq') e.symm
    have h2 := (Finset.mem_filter.mp hq').2 q (hTS q hq) e
    have hz : q.2 = q'.2 := by
      have : s * q.2 = s * q'.2 := le_antisymm h2 h1
      have := congrArg (fun t => s * t) this; simp only [← mul_assoc, hss, one_mul] at this
      exact this
    exact Prod.ext e hz
  have hneT : ∃ q ∈ T, q ≠ (0, z0) := by
    obtain ⟨q, hq, hq0⟩ := hne
    obtain ⟨q', hq'T, e, -⟩ := top q hq
    refine ⟨q', hq'T, fun h => ?_⟩
    have := hpos q hq hq0; rw [h] at e; simp at e; linarith
  obtain ⟨m, ca, cz, C⟩ := exists_chainOK T z0 hz0T (fun q hq => hpos q (hTS q hq)) hneT hinjT
    (fun p hp q hq r hr => hcol p (hTS p hp) q (hTS q hq) r (hTS r hr)) s hs
  refine ⟨m, ca, cz, C.one_le, C.start, C.inc, fun l hl => hTS _ (C.mem l hl), ?_, ?_⟩
  · intro a z hq hn
    obtain ⟨q', hq'T, e, hle⟩ := top (a, z) hq
    by_cases hqT : (a, z) ∈ T
    · exact Or.inl (C.far a z hqT hn)
    · have hlt : s * z < s * q'.2 := by
        rcases hle.lt_or_eq with h | h
        · exact h
        · exfalso; apply hqT
          have hz : z = q'.2 := by
            have := congrArg (fun t => s * t) h; simp only [← mul_assoc, hss, one_mul] at this
            exact this
          have : (a, z) = q' := Prod.ext e.symm hz
          rw [this]; exact hq'T
      by_cases hfar : q'.1 = ca m ∧ q'.2 = cz m
      · right; refine ⟨by rw [← hfar.1, e], ?_⟩
        rw [← hfar.2]; linarith [show s * (z - q'.2) = s * z - s * q'.2 by ring]
      · left
        have := C.far q'.1 q'.2 (by simpa using hq'T) hfar
        rw [e] at this; exact this
  · intro a z hq l hl hn1 hn2
    obtain ⟨q', hq'T, e, hle⟩ := top (a, z) hq
    by_cases hqT : (a, z) ∈ T
    · exact C.side a z hqT l hl hn1 hn2
    · have hlt : s * z < s * q'.2 := by
        rcases hle.lt_or_eq with h | h
        · exact h
        · exfalso; apply hqT
          have hz : z = q'.2 := by
            have := congrArg (fun t => s * t) h; simp only [← mul_assoc, hss, one_mul] at this
            exact this
          have : (a, z) = q' := Prod.ext e.symm hz
          rw [this]; exact hq'T
      -- the top's cross product is ≤ 0 (on the chain, or strictly on its side)
      have hq'le : s * ((ca (l + 1) - ca l) * (q'.2 - cz l) - (cz (l + 1) - cz l) * (q'.1 - ca l)) ≤ 0 := by
        by_cases h1 : q'.1 = ca l ∧ q'.2 = cz l
        · rw [h1.1, h1.2]; ring_nf; rfl
        by_cases h2 : q'.1 = ca (l + 1) ∧ q'.2 = cz (l + 1)
        · rw [h2.1, h2.2]; ring_nf; rfl
        exact (C.side q'.1 q'.2 (by simpa using hq'T) l hl h1 h2).le
      have hd : 0 < ca (l + 1) - ca l := sub_pos.mpr (C.inc l hl)
      have e2 : s * ((ca (l + 1) - ca l) * (z - cz l) - (cz (l + 1) - cz l) * (a - ca l)) =
          s * ((ca (l + 1) - ca l) * (q'.2 - cz l) - (cz (l + 1) - cz l) * (q'.1 - ca l)) +
          (ca (l + 1) - ca l) * (s * z - s * q'.2) := by rw [e]; ring
      rw [e2]; nlinarith [mul_pos hd (sub_pos.mpr hlt)]

theorem ChainOKc.far_pos {Q : ℝ → ℝ → Prop} {z0 s : ℝ} {m : ℕ} {ca cz : ℕ → ℝ}
    (h : ChainOKc Q z0 s m ca cz) : 0 < ca m := by
  have : ∀ j, j ≤ m → ca 0 < ca j ∨ j = 0 := by
    intro j hj
    induction j with
    | zero => right; rfl
    | succ j ih =>
      left
      rcases ih (by omega) with h' | h'
      · exact lt_trans h' (h.inc j (by omega))
      · subst h'; exact h.inc 0 (by omega)
  rcases this m le_rfl with h' | h'
  · rw [h.start.1] at h'; exact h'
  · have := h.one_le; omega

set_option maxHeartbeats 4000000 in
/-- **Lemma T over a vertex with vertical companions at the far ends.** As
the core of `isRupert_vertex_frame`, for chains `C1` (sign `s`) and `C2`
(sign `-s`) that may have vertical companions at their far ends, and a tilt
ratio `α / β` leaning toward the face without companions. -/
theorem vertex_core_par (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (Q1 Q2 : ℝ → ℝ → Prop)
    {z0 : ℝ} (s : ℝ) (hs : s = 1 ∨ s = -1) {m n : ℕ} {ca cz cb dz : ℕ → ℝ}
    (C1 : ChainOKc Q1 z0 s m ca cz) (C2 : ChainOKc Q2 z0 (-s) n cb dz)
    (hAB : s * dz n < s * cz m) {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hr1 : ∀ z, Q1 (ca m) z → z ≠ cz m → ca m * β < cb n * α)
    (hr2 : ∀ z, Q2 (cb n) z → z ≠ dz n → cb n * α < ca m * β)
    (hap1 : ∀ z, Q1 0 z → z = z0) (hap2 : ∀ z, Q2 0 z → z = z0)
    (hpos1 : ∀ a z, Q1 a z → 0 ≤ a) (hpos2 : ∀ b z, Q2 b z → 0 ≤ b)
    (V : Finset ℝ³)
    (hV1 : ∀ a z, Q1 a z → oblPt O r1 r2 a 0 z ∈ V) (hV2 : ∀ b z, Q2 b z → oblPt O r1 r2 0 b z ∈ V)
    (hVc : ∀ y ∈ V, ∃ a b z, y = oblPt O r1 r2 a b z ∧
      ((b = 0 ∧ Q1 a z) ∨ (a = 0 ∧ Q2 b z) ∨ (0 < a ∧ 0 < b ∧ a * cb n + b * ca m < ca m * cb n))) :
    IsRupert V := by
  have hA0 := C1.far_pos
  have hB0 := C2.far_pos
  have c10 := C1.start; have c20 := C2.start
  have side1 : ∀ a z, Q1 a z → ∀ l, l < m → oblPt O r1 r2 a 0 z ≠ oblPt O r1 r2 (ca l) 0 (cz l) →
      oblPt O r1 r2 a 0 z ≠ oblPt O r1 r2 (ca (l + 1)) 0 (cz (l + 1)) →
      s * ((ca (l + 1) - ca l) * (z - cz l) - (cz (l + 1) - cz l) * (a - ca l)) < 0 := by
    intro a z hq l hl h1 h2
    exact C1.side a z hq l hl (fun ⟨e1, e2⟩ => h1 (by rw [e1, e2]))
      (fun ⟨e1, e2⟩ => h2 (by rw [e1, e2]))
  have side2 : ∀ b z, Q2 b z → ∀ l, l < n →
      oblPt O r1 r2 0 b z ≠ oblPt O r1 r2 0 (cb (l + 1)) (dz (l + 1)) →
      oblPt O r1 r2 0 b z ≠ oblPt O r1 r2 0 (cb l) (dz l) →
      s * ((cb l - cb (l + 1)) * (z - dz (l + 1)) - (dz l - dz (l + 1)) * (b - cb (l + 1))) < 0 := by
    intro b z hq l hl h1 h2
    have := C2.side b z hq l hl (fun ⟨e1, e2⟩ => h2 (by rw [e1, e2]))
      (fun ⟨e1, e2⟩ => h1 (by rw [e1, e2]))
    have e : s * ((cb l - cb (l + 1)) * (z - dz (l + 1)) - (dz l - dz (l + 1)) * (b - cb (l + 1))) =
      -s * ((cb (l + 1) - cb l) * (z - dz l) - (dz (l + 1) - dz l) * (b - cb l)) := by ring
    rw [e]; exact this
  have q20 : Q2 0 z0 := by rw [← c20.2, ← c20.1]; exact C2.mem 0 (Nat.zero_le _)
  have q10 : Q1 0 z0 := by rw [← c10.2, ← c10.1]; exact C1.mem 0 (Nat.zero_le _)
  -- the far tests, with the companions
  have far1 : ∀ a z, Q1 a z →
      TiltOK (ca m) 0 (cz m) 0 (cb n) (dz n) a 0 z (-s * α) (s * β) ∨
        oblPt O r1 r2 a 0 z = oblPt O r1 r2 (ca m) 0 (cz m) := by
    intro a z hq
    by_cases h : a = ca m ∧ z = cz m
    · right; rw [h.1, h.2]
    rcases C1.far a z hq h with hlt | ⟨ea, hc⟩
    · left; exact far_tiltOK (by nlinarith)
    · left; subst ea
      have hz : z ≠ cz m := fun e => by rw [e] at hc; simp at hc
      exact tiltOK_farComp1 hc (hr1 z hq hz)
  have far2 : ∀ b z, Q2 b z →
      TiltOK (ca m) 0 (cz m) 0 (cb n) (dz n) 0 b z (-s * α) (s * β) ∨
        oblPt O r1 r2 0 b z = oblPt O r1 r2 0 (cb n) (dz n) := by
    intro b z hq
    by_cases h : b = cb n ∧ z = dz n
    · right; rw [h.1, h.2]
    rcases C2.far b z hq h with hlt | ⟨eb, hc⟩
    · left; exact far_tiltOK (by nlinarith)
    · left; subst eb
      have hz : z ≠ dz n := fun e => by rw [e] at hc; simp at hc
      exact tiltOK_farComp2 (by linarith) (hr2 z hq hz)
  refine isRupert_triShadow_tilt O r1 r2 hρ C1.one_le C2.one_le s hs hα hβ ca cz cb dz c10.1 c20.1
    (by rw [c10.2, c20.2]) C1.inc C2.inc V (fun l hl => hV1 _ _ (C1.mem l hl))
    (fun l hl => hV2 _ _ (C2.mem l hl)) ?_ hAB
  intro y hy
  obtain ⟨a, b, z, rfl, hc⟩ := hVc y hy
  rcases hc with ⟨rfl, hq⟩ | ⟨rfl, hq⟩ | ⟨ha, hb, hin⟩
  · refine ⟨a, 0, z, rfl, hpos1 a z hq, le_rfl, ?_, fun _ => side1 a z hq, ?_⟩
    · rcases far1 a z hq with h | h
      · exact Or.inl h
      · right; left; exact h
    · intro ha; subst ha; rw [hap1 z hq]; exact side2 0 z0 q20
  · refine ⟨0, b, z, rfl, le_rfl, hpos2 b z hq, ?_, ?_, fun _ => side2 b z hq⟩
    · rcases far2 b z hq with h | h
      · exact Or.inl h
      · right; right; exact h
    · intro hb; subst hb; rw [hap2 z hq]; exact side1 0 z0 q10
  · exact ⟨a, b, z, rfl, ha.le, hb.le, Or.inl (far_tiltOK hin), fun h => absurd h hb.ne',
      fun h => absurd h ha.ne'⟩

/-- All chains of one point set end at the same `a` (the largest). -/
theorem ChainOKc.far_a_eq {Q : ℝ → ℝ → Prop} {z0 z0' s s' : ℝ} {m m' : ℕ} {ca cz ca' cz' : ℕ → ℝ}
    (h : ChainOKc Q z0 s m ca cz) (h' : ChainOKc Q z0' s' m' ca' cz') : ca m = ca' m' := by
  have le1 : ca' m' ≤ ca m := by
    by_cases e : ca' m' = ca m ∧ cz' m' = cz m
    · exact e.1.le
    rcases h.far _ _ (h'.mem m' le_rfl) e with hl | ⟨hl, -⟩
    · exact hl.le
    · exact hl.le
  have le2 : ca m ≤ ca' m' := by
    by_cases e : ca m = ca' m' ∧ cz m = cz' m'
    · exact e.1.le
    rcases h'.far _ _ (h.mem m le_rfl) e with hl | ⟨hl, -⟩
    · exact hl.le
    · exact hl.le
  linarith

/-- If only one point of `Q` has the largest `a`, every chain ends there. -/
theorem ChainOKc.far_z_of_unique {Q : ℝ → ℝ → Prop} {z0 z0' s s' : ℝ} {m m' : ℕ}
    {ca cz ca' cz' : ℕ → ℝ} (h : ChainOKc Q z0 s m ca cz) (h' : ChainOKc Q z0' s' m' ca' cz')
    (hu : ∀ z, Q (ca m) z → z = cz m) : ∀ z, Q (ca' m') z → z = cz' m' := by
  have ea := h.far_a_eq h'
  intro z hz
  rw [← ea] at hz
  have e1 := hu z hz
  have e2 := hu (cz' m') (by rw [ea]; exact h'.mem m' le_rfl)
  rw [e1, e2]

set_option maxHeartbeats 4000000 in
/-- **Lemma T over a vertex, far companions allowed, from chains.** As
`isRupert_vertex_frame`, for chains that may have vertical companions at
their far ends (`ChainOKc`), provided one of the two faces has a single
point of largest `a` (else the rectangle exception) and the far depths are
not all tied (`hfar`: the top of one face's far vertical is above the
bottom of the other's, in one of the two orders). -/
theorem isRupert_vertex_frame_par (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (Q1 Q2 : ℝ → ℝ → Prop)
    {z0 : ℝ}
    (hU1 : ∃ m ca cz, ChainOKc Q1 z0 1 m ca cz) (hL1 : ∃ m ca cz, ChainOKc Q1 z0 (-1) m ca cz)
    (hU2 : ∃ m ca cz, ChainOKc Q2 z0 1 m ca cz) (hL2 : ∃ m ca cz, ChainOKc Q2 z0 (-1) m ca cz)
    (hap1 : ∀ z, Q1 0 z → z = z0) (hap2 : ∀ z, Q2 0 z → z = z0)
    (hpos1 : ∀ a z, Q1 a z → 0 ≤ a) (hpos2 : ∀ b z, Q2 b z → 0 ≤ b)
    (hone : (∀ m ca cz, ChainOKc Q1 z0 1 m ca cz → ∀ z, Q1 (ca m) z → z = cz m) ∨
      (∀ n cb dz, ChainOKc Q2 z0 1 n cb dz → ∀ z, Q2 (cb n) z → z = dz n))
    (hfar : ∀ m ca cz m' ca' cz' n cb dz n' cb' dz', ChainOKc Q1 z0 1 m ca cz →
      ChainOKc Q1 z0 (-1) m' ca' cz' → ChainOKc Q2 z0 1 n cb dz → ChainOKc Q2 z0 (-1) n' cb' dz' →
      dz' n' < cz m ∨ cz' m' < dz n)
    (V : Finset ℝ³)
    (hV1 : ∀ a z, Q1 a z → oblPt O r1 r2 a 0 z ∈ V) (hV2 : ∀ b z, Q2 b z → oblPt O r1 r2 0 b z ∈ V)
    (hVc : ∀ y ∈ V, ∃ a b z, y = oblPt O r1 r2 a b z ∧
      ((b = 0 ∧ Q1 a z) ∨ (a = 0 ∧ Q2 b z) ∨ (0 < a ∧ 0 < b ∧
        ∀ m ca cz n cb dz, ChainOKc Q1 z0 1 m ca cz → ChainOKc Q2 z0 1 n cb dz →
          a * cb n + b * ca m < ca m * cb n))) :
    IsRupert V := by
  obtain ⟨m0, ca0, cz0, U1⟩ := hU1
  obtain ⟨n0, cb0, dz0, U2⟩ := hU2
  obtain ⟨m1, ca1, cz1, L1⟩ := hL1
  obtain ⟨n1, cb1, dz1, L2⟩ := hL2
  -- the core for chains `C1` (sign `s`), `C2` (sign `-s`)
  have core : ∀ (s : ℝ), (s = 1 ∨ s = -1) → ∀ {m n : ℕ} {ca cz cb dz : ℕ → ℝ},
      ChainOKc Q1 z0 s m ca cz → ChainOKc Q2 z0 (-s) n cb dz → s * dz n < s * cz m →
      IsRupert V := by
    intro s hs m n ca cz cb dz C1 C2 hAB
    have ea := C1.far_a_eq U1
    have eb := C2.far_a_eq U2
    have hA0 := C1.far_pos
    have hB0 := C2.far_pos
    -- the tilt ratio: lean toward the face without companions
    obtain ⟨α, β, hα, hβ, hr1, hr2⟩ : ∃ α β : ℝ, 0 < α ∧ 0 < β ∧
        (∀ z, Q1 (ca m) z → z ≠ cz m → ca m * β < cb n * α) ∧
        (∀ z, Q2 (cb n) z → z ≠ dz n → cb n * α < ca m * β) := by
      rcases hone with h1 | h2
      · have hu := U1.far_z_of_unique C1 (h1 m0 ca0 cz0 U1)
        refine ⟨1, 2 * cb n / ca m, one_pos, by positivity, fun z hz hne => absurd (hu z hz) hne,
          fun z _ _ => ?_⟩
        rw [mul_div_assoc', mul_comm (ca m) (2 * cb n), mul_div_assoc, div_self hA0.ne']
        linarith
      · have hu := U2.far_z_of_unique C2 (h2 n0 cb0 dz0 U2)
        refine ⟨2 * ca m / cb n, 1, by positivity, one_pos, fun z _ _ => ?_,
          fun z hz hne => absurd (hu z hz) hne⟩
        rw [mul_div_assoc', mul_comm (cb n) (2 * ca m), mul_div_assoc, div_self hB0.ne']
        linarith
    refine vertex_core_par O r1 r2 hρ Q1 Q2 s hs C1 C2 hAB hα hβ hr1 hr2 hap1 hap2 hpos1 hpos2 V
      hV1 hV2 ?_
    intro y hy
    obtain ⟨a, b, z, rfl, hc⟩ := hVc y hy
    refine ⟨a, b, z, rfl, ?_⟩
    rcases hc with h | h | ⟨ha, hb, hin⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · right; right; refine ⟨ha, hb, ?_⟩
      have := hin m0 ca0 cz0 n0 cb0 dz0 U1 U2
      rw [ea, eb]; exact this
  rcases hfar m0 ca0 cz0 m1 ca1 cz1 n0 cb0 dz0 n1 cb1 dz1 U1 L1 U2 L2 with h | h
  · exact core 1 (Or.inl rfl) U1 (by simpa using L2) (by linarith)
  · exact core (-1) (Or.inr rfl) L1 (by simpa using U2) (by linarith)

set_option maxHeartbeats 4000000 in
/-- **Lemma T over an edge with vertical companions at the far ends**, the
core for given chains and tilt ratio (as `edge_core_chord`). -/
theorem edge_core_par (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (Q1 Q2 : ℝ → ℝ → Prop)
    (s : ℝ) (hs : s = 1 ∨ s = -1) {z1s z2s : ℝ} (hap : s * z2s < s * z1s)
    {m n : ℕ} {ca cz cb dz : ℕ → ℝ}
    (C1 : ChainOKc Q1 z1s s m ca cz) (C2 : ChainOKc Q2 z2s (-s) n cb dz)
    (hAB : s * dz n < s * cz m) {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hr1 : ∀ z, Q1 (ca m) z → z ≠ cz m → ca m * β < cb n * α)
    (hr2 : ∀ z, Q2 (cb n) z → z ≠ dz n → cb n * α < ca m * β)
    (hap1 : ∀ z, Q1 0 z → z = z1s ∨ z = z2s) (hap2 : ∀ z, Q2 0 z → z = z1s ∨ z = z2s)
    (hQ1z2 : Q1 0 z2s) (hQ2z1 : Q2 0 z1s)
    (hpos1 : ∀ a z, Q1 a z → 0 ≤ a) (hpos2 : ∀ b z, Q2 b z → 0 ≤ b)
    (V : Finset ℝ³)
    (hV1 : ∀ a z, Q1 a z → oblPt O r1 r2 a 0 z ∈ V) (hV2 : ∀ b z, Q2 b z → oblPt O r1 r2 0 b z ∈ V)
    (hVc : ∀ y ∈ V, ∃ a b z, y = oblPt O r1 r2 a b z ∧
      ((b = 0 ∧ Q1 a z) ∨ (a = 0 ∧ Q2 b z) ∨ (0 < a ∧ 0 < b ∧ a * cb n + b * ca m < ca m * cb n))) :
    IsRupert V := by
  have hA0 := C1.far_pos
  have hB0 := C2.far_pos
  have c10 := C1.start; have c20 := C2.start
  have side1 : ∀ a z, Q1 a z → ∀ l, l < m → oblPt O r1 r2 a 0 z ≠ oblPt O r1 r2 (ca l) 0 (cz l) →
      oblPt O r1 r2 a 0 z ≠ oblPt O r1 r2 (ca (l + 1)) 0 (cz (l + 1)) →
      s * ((ca (l + 1) - ca l) * (z - cz l) - (cz (l + 1) - cz l) * (a - ca l)) < 0 := by
    intro a z hq l hl h1 h2
    exact C1.side a z hq l hl (fun ⟨e1, e2⟩ => h1 (by rw [e1, e2]))
      (fun ⟨e1, e2⟩ => h2 (by rw [e1, e2]))
  have side2 : ∀ b z, Q2 b z → ∀ l, l < n →
      oblPt O r1 r2 0 b z ≠ oblPt O r1 r2 0 (cb (l + 1)) (dz (l + 1)) →
      oblPt O r1 r2 0 b z ≠ oblPt O r1 r2 0 (cb l) (dz l) →
      s * ((cb l - cb (l + 1)) * (z - dz (l + 1)) - (dz l - dz (l + 1)) * (b - cb (l + 1))) < 0 := by
    intro b z hq l hl h1 h2
    have := C2.side b z hq l hl (fun ⟨e1, e2⟩ => h2 (by rw [e1, e2]))
      (fun ⟨e1, e2⟩ => h1 (by rw [e1, e2]))
    have e : s * ((cb l - cb (l + 1)) * (z - dz (l + 1)) - (dz l - dz (l + 1)) * (b - cb (l + 1))) =
      -s * ((cb (l + 1) - cb l) * (z - dz l) - (dz (l + 1) - dz l) * (b - cb l)) := by ring
    rw [e]; exact this
  have apx : ∀ z, z = z1s ∨ z = z2s → oblPt O r1 r2 0 0 z = oblPt O r1 r2 (ca 0) 0 (cz 0) ∨
      oblPt O r1 r2 0 0 z = oblPt O r1 r2 0 (cb 0) (dz 0) := by
    rintro z (rfl | rfl)
    · left; rw [c10.1, c10.2]
    · right; rw [c20.1, c20.2]
  have q1of : ∀ z, Q2 0 z → Q1 0 z := by
    intro z h; rcases hap2 z h with rfl | rfl
    · exact (by rw [← c10.2, ← c10.1]; exact C1.mem 0 (Nat.zero_le _))
    · exact hQ1z2
  have q2of : ∀ z, Q1 0 z → Q2 0 z := by
    intro z h; rcases hap1 z h with rfl | rfl
    · exact hQ2z1
    · exact (by rw [← c20.2, ← c20.1]; exact C2.mem 0 (Nat.zero_le _))
  have far1 : ∀ a z, Q1 a z →
      TiltOK (ca m) 0 (cz m) 0 (cb n) (dz n) a 0 z (-s * α) (s * β) ∨
        oblPt O r1 r2 a 0 z = oblPt O r1 r2 (ca m) 0 (cz m) := by
    intro a z hq
    by_cases h : a = ca m ∧ z = cz m
    · right; rw [h.1, h.2]
    rcases C1.far a z hq h with hlt | ⟨ea, hc⟩
    · left; exact far_tiltOK (by nlinarith)
    · left; subst ea
      have hz : z ≠ cz m := fun e => by rw [e] at hc; simp at hc
      exact tiltOK_farComp1 hc (hr1 z hq hz)
  have far2 : ∀ b z, Q2 b z →
      TiltOK (ca m) 0 (cz m) 0 (cb n) (dz n) 0 b z (-s * α) (s * β) ∨
        oblPt O r1 r2 0 b z = oblPt O r1 r2 0 (cb n) (dz n) := by
    intro b z hq
    by_cases h : b = cb n ∧ z = dz n
    · right; rw [h.1, h.2]
    rcases C2.far b z hq h with hlt | ⟨eb, hc⟩
    · left; exact far_tiltOK (by nlinarith)
    · left; subst eb
      have hz : z ≠ dz n := fun e => by rw [e] at hc; simp at hc
      exact tiltOK_farComp2 (by linarith) (hr2 z hq hz)
  refine isRupert_triShadow2_tilt O r1 r2 hρ C1.one_le C2.one_le s hs hα hβ ca cz cb dz c10.1 c20.1
    (by rw [c10.2, c20.2]; exact hap) C1.inc C2.inc V (fun l hl => hV1 _ _ (C1.mem l hl))
    (fun l hl => hV2 _ _ (C2.mem l hl)) ?_ hAB
  intro y hy
  obtain ⟨a, b, z, rfl, hc⟩ := hVc y hy
  rcases hc with ⟨rfl, hq⟩ | ⟨rfl, hq⟩ | ⟨ha, hb, hin⟩
  · refine ⟨a, 0, z, rfl, hpos1 a z hq, le_rfl, ?_, ?_, fun _ => side1 a z hq, ?_⟩
    · rcases far1 a z hq with h | h
      · exact Or.inl h
      · right; left; exact h
    · intro ha _; subst ha; exact apx z (hap1 z hq)
    · intro ha; subst ha; exact side2 0 z (q2of z hq)
  · refine ⟨0, b, z, rfl, le_rfl, hpos2 b z hq, ?_, ?_, ?_, fun _ => side2 b z hq⟩
    · rcases far2 b z hq with h | h
      · exact Or.inl h
      · right; right; exact h
    · intro _ hb; subst hb; exact apx z (hap2 z hq)
    · intro hb; subst hb; exact side1 0 z (q1of z hq)
  · exact ⟨a, b, z, rfl, ha.le, hb.le, Or.inl (far_tiltOK hin), fun h => absurd h ha.ne',
      fun h => absurd h hb.ne', fun h => absurd h ha.ne'⟩

set_option maxHeartbeats 4000000 in
/-- **Lemma T over an edge, far companions allowed, from chains** (as
`isRupert_edge_frame`; upper chains start at the top apex vertex, lower
chains at the bottom one). -/
theorem isRupert_edge_frame_par (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (Q1 Q2 : ℝ → ℝ → Prop)
    {zx zx' : ℝ} (hxx : zx < zx')
    (hU1 : ∃ m ca cz, ChainOKc Q1 zx' 1 m ca cz) (hL1 : ∃ m ca cz, ChainOKc Q1 zx (-1) m ca cz)
    (hU2 : ∃ m ca cz, ChainOKc Q2 zx' 1 m ca cz) (hL2 : ∃ m ca cz, ChainOKc Q2 zx (-1) m ca cz)
    (hap1 : ∀ z, Q1 0 z → z = zx ∨ z = zx') (hap2 : ∀ z, Q2 0 z → z = zx ∨ z = zx')
    (hQ1x : Q1 0 zx) (hQ1x' : Q1 0 zx') (hQ2x : Q2 0 zx) (hQ2x' : Q2 0 zx')
    (hpos1 : ∀ a z, Q1 a z → 0 ≤ a) (hpos2 : ∀ b z, Q2 b z → 0 ≤ b)
    (hone : (∀ m ca cz, ChainOKc Q1 zx' 1 m ca cz → ∀ z, Q1 (ca m) z → z = cz m) ∨
      (∀ n cb dz, ChainOKc Q2 zx' 1 n cb dz → ∀ z, Q2 (cb n) z → z = dz n))
    (hfar : ∀ m ca cz m' ca' cz' n cb dz n' cb' dz', ChainOKc Q1 zx' 1 m ca cz →
      ChainOKc Q1 zx (-1) m' ca' cz' → ChainOKc Q2 zx' 1 n cb dz → ChainOKc Q2 zx (-1) n' cb' dz' →
      dz' n' < cz m ∨ cz' m' < dz n)
    (V : Finset ℝ³)
    (hV1 : ∀ a z, Q1 a z → oblPt O r1 r2 a 0 z ∈ V) (hV2 : ∀ b z, Q2 b z → oblPt O r1 r2 0 b z ∈ V)
    (hVc : ∀ y ∈ V, ∃ a b z, y = oblPt O r1 r2 a b z ∧
      ((b = 0 ∧ Q1 a z) ∨ (a = 0 ∧ Q2 b z) ∨ (0 < a ∧ 0 < b ∧
        ∀ m ca cz n cb dz, ChainOKc Q1 zx' 1 m ca cz → ChainOKc Q2 zx' 1 n cb dz →
          a * cb n + b * ca m < ca m * cb n))) :
    IsRupert V := by
  obtain ⟨m0, ca0, cz0, U1⟩ := hU1
  obtain ⟨n0, cb0, dz0, U2⟩ := hU2
  obtain ⟨m1, ca1, cz1, L1⟩ := hL1
  obtain ⟨n1, cb1, dz1, L2⟩ := hL2
  have core : ∀ (s : ℝ), (s = 1 ∨ s = -1) → ∀ {z1s z2s : ℝ}, s * z2s < s * z1s →
      (∀ z, Q1 0 z → z = z1s ∨ z = z2s) → (∀ z, Q2 0 z → z = z1s ∨ z = z2s) →
      Q1 0 z2s → Q2 0 z1s → ∀ {m n : ℕ} {ca cz cb dz : ℕ → ℝ},
      ChainOKc Q1 z1s s m ca cz → ChainOKc Q2 z2s (-s) n cb dz → s * dz n < s * cz m →
      IsRupert V := by
    intro s hs z1s z2s hap h1 h2 q12 q21 m n ca cz cb dz C1 C2 hAB
    have ea := C1.far_a_eq U1
    have eb := C2.far_a_eq U2
    have hA0 := C1.far_pos
    have hB0 := C2.far_pos
    obtain ⟨α, β, hα, hβ, hr1, hr2⟩ : ∃ α β : ℝ, 0 < α ∧ 0 < β ∧
        (∀ z, Q1 (ca m) z → z ≠ cz m → ca m * β < cb n * α) ∧
        (∀ z, Q2 (cb n) z → z ≠ dz n → cb n * α < ca m * β) := by
      rcases hone with hu1 | hu2
      · have hu := U1.far_z_of_unique C1 (hu1 m0 ca0 cz0 U1)
        refine ⟨1, 2 * cb n / ca m, one_pos, by positivity, fun z hz hne => absurd (hu z hz) hne,
          fun z _ _ => ?_⟩
        rw [mul_div_assoc', mul_comm (ca m) (2 * cb n), mul_div_assoc, div_self hA0.ne']
        linarith
      · have hu := U2.far_z_of_unique C2 (hu2 n0 cb0 dz0 U2)
        refine ⟨2 * ca m / cb n, 1, by positivity, one_pos, fun z _ _ => ?_,
          fun z hz hne => absurd (hu z hz) hne⟩
        rw [mul_div_assoc', mul_comm (cb n) (2 * ca m), mul_div_assoc, div_self hB0.ne']
        linarith
    refine edge_core_par O r1 r2 hρ Q1 Q2 s hs hap C1 C2 hAB hα hβ hr1 hr2 h1 h2 q12 q21 hpos1 hpos2
      V hV1 hV2 ?_
    intro y hy
    obtain ⟨a, b, z, rfl, hc⟩ := hVc y hy
    refine ⟨a, b, z, rfl, ?_⟩
    rcases hc with h | h | ⟨ha, hb, hin⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · right; right; refine ⟨ha, hb, ?_⟩
      have := hin m0 ca0 cz0 n0 cb0 dz0 U1 U2
      rw [ea, eb]; exact this
  rcases hfar m0 ca0 cz0 m1 ca1 cz1 n0 cb0 dz0 n1 cb1 dz1 U1 L1 U2 L2 with h | h
  · exact core 1 (Or.inl rfl) (by linarith) (fun z hz => (hap1 z hz).symm.imp id id |>.elim
      (fun e => Or.inl e) (fun e => Or.inr e)) (fun z hz => (hap2 z hz).symm.imp id id |>.elim
      (fun e => Or.inl e) (fun e => Or.inr e)) hQ1x hQ2x' U1 (by simpa using L2) (by linarith)
  · exact core (-1) (Or.inr rfl) (by linarith) (hap1) (hap2) hQ1x' hQ2x L1 (by simpa using U2)
      (by linarith)

theorem ChainOKc.pos {Q : ℝ → ℝ → Prop} {z0 s : ℝ} {m : ℕ} {ca cz : ℕ → ℝ}
    (h : ChainOKc Q z0 s m ca cz) : ∀ l, 1 ≤ l → l ≤ m → 0 < ca l := by
  intro l
  induction l with
  | zero => intro h1; omega
  | succ l ih =>
    intro _ hl
    rcases Nat.eq_zero_or_pos l with rfl | hl0
    · have := h.inc 0 (by omega); rw [h.start.1] at this; exact this
    · exact lt_trans (ih hl0 (by omega)) (h.inc l (by omega))

/-- **Chains over an edge, points sharing verticals allowed** (as
`exists_chainOK_edge` without distinct `a`). -/
theorem exists_chainOKc_edge (S : Finset (ℝ × ℝ)) (zs zo s : ℝ) (hs : s = 1 ∨ s = -1)
    (hso : s * zo < s * zs) (h0 : (0, zs) ∈ S)
    (hpos : ∀ q ∈ S, q ≠ (0, zs) → q ≠ (0, zo) → 0 < q.1) (hne : ∃ q ∈ S, 0 < q.1)
    (hcol : ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, p ≠ q → p ≠ r → q ≠ r →
      (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1) ≠ 0) :
    ∃ m ca cz, ChainOKc (fun a z => (a, z) ∈ S) zs s m ca cz := by
  classical
  have hzz : zs ≠ zo := fun h => by rw [h] at hso; exact lt_irrefl _ hso
  have hne0 : ((0 : ℝ), zs) ≠ (0, zo) := fun h => hzz (congrArg Prod.snd h)
  obtain ⟨m, ca, cz, C⟩ := exists_chainOKc (S.erase (0, zo)) zs
    (Finset.mem_erase.mpr ⟨hne0, h0⟩)
    (fun q hq hq0 => hpos q (Finset.mem_of_mem_erase hq) hq0 (Finset.ne_of_mem_erase hq))
    (by
      obtain ⟨q, hq, hq0⟩ := hne
      refine ⟨q, Finset.mem_erase.mpr ⟨fun h => ?_, hq⟩, fun h => ?_⟩
      · rw [h] at hq0; exact lt_irrefl _ hq0
      · rw [h] at hq0; exact lt_irrefl _ hq0)
    (fun p hp q hq r hr => hcol p (Finset.mem_of_mem_erase hp) q (Finset.mem_of_mem_erase hq)
      r (Finset.mem_of_mem_erase hr))
    s hs
  refine ⟨m, ca, cz, C.one_le, C.start, C.inc, fun l hl => Finset.mem_of_mem_erase (C.mem l hl),
    fun a z hq hn => ?_, fun a z hq l hl h1' h2' => ?_⟩
  · by_cases e : (a, z) = (0, zo)
    · have := C.far_pos; rw [show a = 0 from congrArg Prod.fst e]; exact Or.inl this
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

end Minimality

end
