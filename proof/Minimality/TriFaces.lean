module

public import Minimality.TriQuad
public import Minimality.TriShadow2

@[expose] public section

/-!
# Lemma T for two faces sharing an edge, with interior points

The frame theorem behind the edge views of Theorems E–L of
`FEWER-FACES-PROOFS.md` §7: two faces `Q1`, `Q2` of `V` share the vertical edge
over the apex (`(0, zx)` below `(0, zx′)`), each given by its chains (upper from
`zx′`, lower from `zx`), and every other point of `V` lies strictly inside the
shadow triangle.  Then `V` is Rupert, by the mixed tilt chosen from the far
depths.
-/

namespace Minimality

open Finset Filter Topology
open scoped RealInnerProductSpace

set_option maxHeartbeats 4000000 in
/-- The core of `isRupert_edge_frame`, for given chains. -/
theorem edge_core (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (Q1 Q2 : ℝ → ℝ → Prop)
    (s : ℝ) (hs : s = 1 ∨ s = -1) {z1s z2s : ℝ} (hap : s * z2s < s * z1s)
    {m n : ℕ} {ca cz cb dz : ℕ → ℝ}
    (C1 : ChainOK Q1 z1s s m ca cz) (C2 : ChainOK Q2 z2s (-s) n cb dz)
    (hAB : s * dz n < s * cz m)
    (hap1 : ∀ z, Q1 0 z → z = z1s ∨ z = z2s) (hap2 : ∀ z, Q2 0 z → z = z1s ∨ z = z2s)
    (hQ1z2 : Q1 0 z2s) (hQ2z1 : Q2 0 z1s)
    (hpos1 : ∀ a z, Q1 a z → 0 ≤ a) (hpos2 : ∀ b z, Q2 b z → 0 ≤ b)
    (V : Finset ℝ³)
    (hV1 : ∀ a z, Q1 a z → oblPt O r1 r2 a 0 z ∈ V) (hV2 : ∀ b z, Q2 b z → oblPt O r1 r2 0 b z ∈ V)
    (hVc : ∀ y ∈ V, ∃ a b z, y = oblPt O r1 r2 a b z ∧
      ((b = 0 ∧ Q1 a z) ∨ (a = 0 ∧ Q2 b z) ∨ (0 < a ∧ 0 < b ∧ a * cb n + b * ca m < ca m * cb n)))
    (hzV : Set.InjOn (fun y : ℝ³ => ⟪y, ez⟫) (V : Set ℝ³)) : IsRupert V := by
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
  -- the apex points
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
  refine isRupert_triShadow2 O r1 r2 hρ C1.one_le C2.one_le s hs ca cz cb dz c10.1 c20.1
    (by rw [c10.2, c20.2]; exact hap) C1.inc C2.inc V (fun l hl => hV1 _ _ (C1.mem l hl))
    (fun l hl => hV2 _ _ (C2.mem l hl)) ?_ hzV hAB
  intro y hy
  obtain ⟨a, b, z, rfl, hc⟩ := hVc y hy
  rcases hc with ⟨rfl, hq⟩ | ⟨rfl, hq⟩ | ⟨ha, hb, hin⟩
  · refine ⟨a, 0, z, rfl, hpos1 a z hq, le_rfl, ?_, ?_, fun _ => side1 a z hq, ?_⟩
    · rcases far1 a z hq with h | ⟨e1, e2⟩
      · left; linarith
      · right; left; rw [e1, e2]
    · intro ha _; subst ha; exact apx z (hap1 z hq)
    · intro ha; subst ha; exact side2 0 z (q2of z hq)
  · refine ⟨0, b, z, rfl, le_rfl, hpos2 b z hq, ?_, ?_, ?_, fun _ => side2 b z hq⟩
    · rcases far2 b z hq with h | ⟨e1, e2⟩
      · left; linarith
      · right; right; rw [e1, e2]
    · intro _ hb; subst hb; exact apx z (hap2 z hq)
    · intro hb; subst hb; exact side1 0 z (q1of z hq)
  · exact ⟨a, b, z, rfl, ha.le, hb.le, Or.inl hin, fun h => absurd h ha.ne',
      fun h => absurd h hb.ne', fun h => absurd h ha.ne'⟩

set_option maxHeartbeats 4000000 in
/-- **Lemma T over an edge, from chains.** -/
theorem isRupert_edge_frame (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (Q1 Q2 : ℝ → ℝ → Prop)
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
    (hzV : Set.InjOn (fun y : ℝ³ => ⟪y, ez⟫) (V : Set ℝ³))
    (hfar : ∀ m ca cz n cb dz, ChainOK Q1 zx' 1 m ca cz → ChainOK Q2 zx' 1 n cb dz → cz m ≠ dz n) :
    IsRupert V := by
  obtain ⟨m0, ca0, cz0, U1⟩ := hU1
  obtain ⟨n0, cb0, dz0, U2⟩ := hU2
  have hne := hfar m0 ca0 cz0 n0 cb0 dz0 U1 U2
  -- choose the tilt by the far depths
  obtain ⟨m1, ca1, cz1, L1⟩ := hL1
  obtain ⟨n1, cb1, dz1, L2⟩ := hL2
  have eU1 := L1.far_eq U1
  have eU2 := L2.far_eq U2
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- far depth of `Q2` larger: the lower chain of `Q1`, the upper chain of `Q2`
    refine edge_core O r1 r2 hρ Q1 Q2 (-1) (Or.inr rfl) (z1s := zx) (z2s := zx') (by linarith)
      L1 (by simpa using U2) (by rw [eU1.2]; linarith) hap1 (fun z h => (hap2 z h)) hQ1x' hQ2x
      hpos1 hpos2 V hV1 hV2 ?_ hzV
    intro y hy
    obtain ⟨a, b, z, e, hc⟩ := hVc y hy
    refine ⟨a, b, z, e, ?_⟩
    rcases hc with h | h | ⟨ha, hb, hin⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · right; right; refine ⟨ha, hb, ?_⟩
      have := hin m0 ca0 cz0 n0 cb0 dz0 U1 U2; rw [eU1.1]; exact this
  · -- far depth of `Q1` larger: the upper chain of `Q1`, the lower chain of `Q2`
    refine edge_core O r1 r2 hρ Q1 Q2 1 (Or.inl rfl) (z1s := zx') (z2s := zx) (by linarith)
      U1 (by simpa using L2) (by rw [eU2.2]; linarith) (fun z h => (hap1 z h).symm)
      (fun z h => (hap2 z h).symm) hQ1x hQ2x' hpos1 hpos2 V hV1 hV2 ?_ hzV
    intro y hy
    obtain ⟨a, b, z, e, hc⟩ := hVc y hy
    refine ⟨a, b, z, e, ?_⟩
    rcases hc with h | h | ⟨ha, hb, hin⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · right; right; refine ⟨ha, hb, ?_⟩
      have := hin m0 ca0 cz0 n0 cb0 dz0 U1 U2; rw [eU2.1]; exact this

set_option maxHeartbeats 4000000 in
/-- **Lemma T over a vertex, from chains**, with interior points: two faces meet
in the apex vertex `(0, 0, z0)`, each given by its upper and lower chains from
it, every other point of `V` strictly inside the shadow triangle, distinct
depths on `V`, distinct far depths: Rupert. -/
theorem isRupert_vertex_frame (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2) (Q1 Q2 : ℝ → ℝ → Prop)
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
    refine isRupert_triShadow_injOn O r1 r2 hρ C1.one_le C2.one_le s hs ca cz cb dz c10.1 c20.1
      (by rw [c10.2, c20.2]) C1.inc C2.inc V (fun l hl => hV1 _ _ (C1.mem l hl))
      (fun l hl => hV2 _ _ (C2.mem l hl)) ?_ hzV hAB
    intro y hy
    obtain ⟨a, b, z, rfl, hc⟩ := hVc y hy
    rcases hc with ⟨rfl, hq⟩ | ⟨rfl, hq⟩ | ⟨ha, hb, hin⟩
    · refine ⟨a, 0, z, rfl, hpos1 a z hq, le_rfl, ?_, fun _ => side1 a z hq, ?_⟩
      · rcases far1 a z hq with h | ⟨e1, e2⟩
        · left; linarith
        · right; left; rw [e1, e2]
      · intro ha; subst ha; rw [hap1 z hq]; exact side2 0 z0 q20
    · refine ⟨0, b, z, rfl, le_rfl, hpos2 b z hq, ?_, ?_, fun _ => side2 b z hq⟩
      · rcases far2 b z hq with h | ⟨e1, e2⟩
        · left; linarith
        · right; right; rw [e1, e2]
      · intro hb; subst hb; rw [hap2 z hq]; exact side1 0 z0 q10
    · refine ⟨a, b, z, rfl, ha.le, hb.le, Or.inl ?_, fun h => absurd h hb.ne',
        fun h => absurd h ha.ne'⟩
      rw [ea, eb]; exact hin m0 ca0 cz0 n0 cb0 dz0 U1 U2
  have eU1 := L1.far_eq U1
  have eU2 := L2.far_eq U2
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact core (-1) (Or.inr rfl) L1 (by simpa using U2) (by rw [eU1.2]; linarith) eU1.1 rfl
  · exact core 1 (Or.inl rfl) U1 (by simpa using L2) (by rw [eU2.2]; linarith) rfl eU2.1

end Minimality

end
