module

public import Minimality.TriFaces
public import Minimality.TriShadow2Chord

@[expose] public section

/-!
# Lemma T′ frames: one point on the far side

`isRupert_vertex_frame` (and the edge version) with one more kind of point: a
point `(ac, bc, zc)` on the chord of the far side, off the segment `A B` (in the
plane of the far-side face it lies above or below `A B`). The tilt
`(-s α, s β)` hides it behind the edge `A B`, with `α / β` chosen from the side
it lies on (Lemma T′ of `FEWER-FACES-PROOFS.md` §7 when the far-side face is a
triangle).
-/

namespace Minimality

open Finset Filter Topology
open scoped RealInnerProductSpace

set_option maxHeartbeats 4000000 in
/-- **Lemma T′ over a vertex, from chains.** -/
theorem isRupert_vertex_frame_chord (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (Q1 Q2 : ℝ → ℝ → Prop)
    {z0 : ℝ}
    (hU1 : ∃ m ca cz, ChainOK Q1 z0 1 m ca cz) (hL1 : ∃ m ca cz, ChainOK Q1 z0 (-1) m ca cz)
    (hU2 : ∃ m ca cz, ChainOK Q2 z0 1 m ca cz) (hL2 : ∃ m ca cz, ChainOK Q2 z0 (-1) m ca cz)
    (hap1 : ∀ z, Q1 0 z → z = z0) (hap2 : ∀ z, Q2 0 z → z = z0)
    (hpos1 : ∀ a z, Q1 a z → 0 ≤ a) (hpos2 : ∀ b z, Q2 b z → 0 ≤ b)
    (ac bc zc : ℝ) (hac : 0 < ac) (hbc : 0 < bc)
    (hch : ∀ s1 s2 m ca cz n cb dz, ChainOK Q1 z0 s1 m ca cz → ChainOK Q2 z0 s2 n cb dz →
      ac * cb n + bc * ca m = ca m * cb n ∧ cb n * (zc - cz m) - bc * (dz n - cz m) ≠ 0)
    (V : Finset ℝ³)
    (hV1 : ∀ a z, Q1 a z → oblPt O r1 r2 a 0 z ∈ V) (hV2 : ∀ b z, Q2 b z → oblPt O r1 r2 0 b z ∈ V)
    (hVc : ∀ y ∈ V, ∃ a b z, y = oblPt O r1 r2 a b z ∧
      ((b = 0 ∧ Q1 a z) ∨ (a = 0 ∧ Q2 b z) ∨ (0 < a ∧ 0 < b ∧
        ∀ m ca cz n cb dz, ChainOK Q1 z0 1 m ca cz → ChainOK Q2 z0 1 n cb dz →
          a * cb n + b * ca m < ca m * cb n) ∨ (a = ac ∧ b = bc ∧ z = zc)))
    (hzV : Set.InjOn (fun y : ℝ³ => ⟪y, ez⟫) (V : Set ℝ³))
    (hfar : ∀ m ca cz n cb dz, ChainOK Q1 z0 1 m ca cz → ChainOK Q2 z0 1 n cb dz → cz m ≠ dz n) :
    IsRupert V := by
  obtain ⟨m0, ca0, cz0, U1⟩ := hU1
  obtain ⟨n0, cb0, dz0, U2⟩ := hU2
  obtain ⟨m1, ca1, cz1, L1⟩ := hL1
  obtain ⟨n1, cb1, dz1, L2⟩ := hL2
  have hne := hfar m0 ca0 cz0 n0 cb0 dz0 U1 U2
  -- the core, for a sign `s` and chains `C1` (sign `s`) and `C2` (sign `-s`)
  have core : ∀ (s : ℝ), (s = 1 ∨ s = -1) → ∀ {m n : ℕ} {ca cz cb dz : ℕ → ℝ},
      ChainOK Q1 z0 s m ca cz → ChainOK Q2 z0 (-s) n cb dz → s * dz n < s * cz m →
      ca m = ca0 m0 → cb n = cb0 n0 → IsRupert V := by
    intro s hs m n ca cz cb dz C1 C2 hAB ea eb
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
        s * ((cb l - cb (l + 1)) * (z - dz (l + 1)) - (dz l - dz (l + 1)) * (b - cb (l + 1))) < 0 := by
      intro b z hq l hl h1 h2
      have := C2.side b z hq l hl (fun ⟨e1, e2⟩ => h2 (by rw [e1, e2]))
        (fun ⟨e1, e2⟩ => h1 (by rw [e1, e2]))
      have e : s * ((cb l - cb (l + 1)) * (z - dz (l + 1)) - (dz l - dz (l + 1)) * (b - cb (l + 1))) =
        -s * ((cb (l + 1) - cb l) * (z - dz l) - (dz (l + 1) - dz l) * (b - cb l)) := by ring
      rw [e]; exact this
    have q20 : Q2 0 z0 := by rw [← c20.2, ← c20.1]; exact C2.mem 0 (Nat.zero_le _)
    have q10 : Q1 0 z0 := by rw [← c10.2, ← c10.1]; exact C1.mem 0 (Nat.zero_le _)
    -- the tilt ratio, from the side of the chord point
    obtain ⟨hch1, hch2⟩ := hch s (-s) m ca cz n cb dz C1 C2
    obtain ⟨α, β, hα, hβ, hpos⟩ : ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ 0 < s * (ca m * β - cb n * α) *
        (cb n * (zc - cz m) - bc * (dz n - cz m)) := by
      have hsD : s * (cb n * (zc - cz m) - bc * (dz n - cz m)) ≠ 0 := by
        intro h; rcases hs with rfl | rfl
        · exact hch2 (by linarith)
        · exact hch2 (by linarith)
      rcases lt_or_gt_of_ne hsD with hneg | hposD
      · refine ⟨2 * ca m / cb n, 1, by positivity, one_pos, ?_⟩
        have e : s * (ca m * 1 - cb n * (2 * ca m / cb n)) * (cb n * (zc - cz m) - bc * (dz n - cz m)) =
            -(ca m) * (s * (cb n * (zc - cz m) - bc * (dz n - cz m))) := by
          field_simp; ring
        rw [e]; nlinarith
      · refine ⟨1, 2 * cb n / ca m, one_pos, by positivity, ?_⟩
        have e : s * (ca m * (2 * cb n / ca m) - cb n * 1) * (cb n * (zc - cz m) - bc * (dz n - cz m)) =
            cb n * (s * (cb n * (zc - cz m) - bc * (dz n - cz m))) := by
          field_simp; ring
        rw [e]; nlinarith
    refine isRupert_triShadow_injOn_tilt O r1 r2 hρ C1.one_le C2.one_le s hs hα hβ ca cz cb dz c10.1 c20.1
      (by rw [c10.2, c20.2]) C1.inc C2.inc V (fun l hl => hV1 _ _ (C1.mem l hl))
      (fun l hl => hV2 _ _ (C2.mem l hl)) ?_ hzV hAB
    intro y hy
    obtain ⟨a, b, z, rfl, hc⟩ := hVc y hy
    rcases hc with ⟨rfl, hq⟩ | ⟨rfl, hq⟩ | ⟨ha, hb, hin⟩ | ⟨ea', eb', ez'⟩
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
    · refine ⟨a, b, z, rfl, by rw [ea']; exact hac.le, by rw [eb']; exact hbc.le,
        Or.inl (by rw [ea', eb', ez']; exact chord_tiltOK C2.far_pos hch1 hpos),
        fun h => absurd (h ▸ eb'.symm) hbc.ne', fun h => absurd (h ▸ ea'.symm) hac.ne'⟩
  have eU1 := L1.far_eq U1
  have eU2 := L2.far_eq U2
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact core (-1) (Or.inr rfl) L1 (by simpa using U2) (by rw [eU1.2]; linarith) eU1.1 rfl
  · exact core 1 (Or.inl rfl) U1 (by simpa using L2) (by rw [eU2.2]; linarith) rfl eU2.1

end Minimality

end
