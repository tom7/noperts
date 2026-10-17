module

public import Minimality.TriShadow

@[expose] public section

/-!
# Lemma T for two quadrilaterals sharing a vertex

Corollary T1 of `FEWER-FACES-PROOFS.md` §7 for two quadrilateral facets that
meet in one vertex and contain all seven points (types 02, 07, 09, 14, 18, 20).
This file works in the oblique frame of `TriShadow.lean`: each quadrilateral is
a convex quadrilateral in its `(t, z)`-plane with the apex at `t = 0`, and its
upper and lower chains from the apex to the far vertex feed
`isRupert_triShadow`.
-/

namespace Minimality

open Finset Filter Topology
open scoped RealInnerProductSpace

/-- The four vertices `(0, z0), (a1, z1), (a2, z2), (a3, z3)` of a quadrilateral
in its `(t, z)`-plane. -/
def QuadPt (z0 a1 z1 a2 z2 a3 z3 : ℝ) (a z : ℝ) : Prop :=
  (a = 0 ∧ z = z0) ∨ (a = a1 ∧ z = z1) ∨ (a = a2 ∧ z = z2) ∨ (a = a3 ∧ z = z3)

/-- A chain `(ca l, cz l)`, `l ≤ m`, of the point set `Q` from the apex `(0, z0)`
to the far point: increasing in `t`, through points of `Q`, ending at the unique
point of largest `t`, with every other point of `Q` strictly on the `s`-side of
each segment (`s = 1`: below, the upper chain; `s = -1`: above, the lower one). -/
structure ChainOK (Q : ℝ → ℝ → Prop) (z0 s : ℝ) (m : ℕ) (ca cz : ℕ → ℝ) : Prop where
  one_le : 1 ≤ m
  start : ca 0 = 0 ∧ cz 0 = z0
  inc : ∀ l, l < m → ca l < ca (l + 1)
  mem : ∀ l, l ≤ m → Q (ca l) (cz l)
  far : ∀ a z, Q a z → ¬ (a = ca m ∧ z = cz m) → a < ca m
  side : ∀ a z, Q a z → ∀ l, l < m → ¬ (a = ca l ∧ z = cz l) → ¬ (a = ca (l + 1) ∧ z = cz (l + 1)) →
    s * ((ca (l + 1) - ca l) * (z - cz l) - (cz (l + 1) - cz l) * (a - ca l)) < 0

/-- A chain with one segment. -/
noncomputable def chain1 (x0 x1 : ℝ) : ℕ → ℝ := fun l => if l = 0 then x0 else x1

/-- A chain with two segments. -/
noncomputable def chain2 (x0 x1 x2 : ℝ) : ℕ → ℝ :=
  fun l => if l = 0 then x0 else if l = 1 then x1 else x2

/-- A chain with three segments. -/
noncomputable def chain3 (x0 x1 x2 x3 : ℝ) : ℕ → ℝ :=
  fun l => if l = 0 then x0 else if l = 1 then x1 else if l = 2 then x2 else x3

set_option linter.unnecessarySeqFocus false

set_option maxHeartbeats 2000000 in
/-- Counterclockwise quadrilateral, far vertex `2`, upper chain `0, 3, 2`. -/
theorem chainOK_ccw2_up {z0 a1 z1 a2 z2 a3 z3 : ℝ} (h1 : 0 < a1) (h2 : 0 < a2) (h3 : 0 < a3)
    (hQ : ConvQuad 0 z0 a1 z1 a2 z2 a3 z3) (h12 : a1 < a2) (h32 : a3 < a2) :
    ChainOK (QuadPt z0 a1 z1 a2 z2 a3 z3) z0 1 2 (chain2 0 a3 a2) (chain2 z0 z3 z2) := by
  obtain ⟨⟨q1a, q1b⟩, ⟨q2a, q2b⟩, ⟨q3a, q3b⟩, ⟨q4a, q4b⟩⟩ := hQ
  refine ⟨by norm_num, by simp [chain2], ?_, ?_, ?_, ?_⟩
  · intro l hl; interval_cases l <;> simp [chain2] <;> nlinarith
  · intro l hl; interval_cases l <;> simp [chain2, QuadPt]
  · intro a z hq hne
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [chain2] at hne ⊢ <;>
      nlinarith
  · intro a z hq l hl hn1 hn2
    interval_cases l <;>
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [chain2] at hn1 hn2 ⊢ <;> nlinarith

set_option maxHeartbeats 2000000 in
/-- Counterclockwise quadrilateral, far vertex `2`, lower chain `0, 1, 2`. -/
theorem chainOK_ccw2_lo {z0 a1 z1 a2 z2 a3 z3 : ℝ} (h1 : 0 < a1) (h2 : 0 < a2) (h3 : 0 < a3)
    (hQ : ConvQuad 0 z0 a1 z1 a2 z2 a3 z3) (h12 : a1 < a2) (h32 : a3 < a2) :
    ChainOK (QuadPt z0 a1 z1 a2 z2 a3 z3) z0 (-1) 2 (chain2 0 a1 a2) (chain2 z0 z1 z2) := by
  obtain ⟨⟨q1a, q1b⟩, ⟨q2a, q2b⟩, ⟨q3a, q3b⟩, ⟨q4a, q4b⟩⟩ := hQ
  refine ⟨by norm_num, by simp [chain2], ?_, ?_, ?_, ?_⟩
  · intro l hl; interval_cases l <;> simp [chain2] <;> nlinarith
  · intro l hl; interval_cases l <;> simp [chain2, QuadPt]
  · intro a z hq hne
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [chain2] at hne ⊢ <;>
      nlinarith
  · intro a z hq l hl hn1 hn2
    interval_cases l <;>
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [chain2] at hn1 hn2 ⊢ <;> nlinarith

set_option maxHeartbeats 2000000 in
/-- Counterclockwise quadrilateral, far vertex `1`, upper chain `0, 3, 2, 1`. -/
theorem chainOK_ccw1_up {z0 a1 z1 a2 z2 a3 z3 : ℝ} (h1 : 0 < a1) (h2 : 0 < a2) (h3 : 0 < a3)
    (hQ : ConvQuad 0 z0 a1 z1 a2 z2 a3 z3) (h21 : a2 < a1) (h31 : a3 < a1) :
    ChainOK (QuadPt z0 a1 z1 a2 z2 a3 z3) z0 1 3 (chain3 0 a3 a2 a1) (chain3 z0 z3 z2 z1) := by
  obtain ⟨⟨q1a, q1b⟩, ⟨q2a, q2b⟩, ⟨q3a, q3b⟩, ⟨q4a, q4b⟩⟩ := hQ
  refine ⟨by norm_num, by simp [chain3], ?_, ?_, ?_, ?_⟩
  · intro l hl; interval_cases l <;> simp [chain3] <;> nlinarith
  · intro l hl; interval_cases l <;> simp [chain3, QuadPt]
  · intro a z hq hne
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [chain3] at hne ⊢ <;>
      nlinarith
  · intro a z hq l hl hn1 hn2
    interval_cases l <;>
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [chain3] at hn1 hn2 ⊢ <;> nlinarith

set_option maxHeartbeats 2000000 in
/-- Counterclockwise quadrilateral, far vertex `1`, lower chain `0, 1`. -/
theorem chainOK_ccw1_lo {z0 a1 z1 a2 z2 a3 z3 : ℝ} (h1 : 0 < a1) (h2 : 0 < a2) (h3 : 0 < a3)
    (hQ : ConvQuad 0 z0 a1 z1 a2 z2 a3 z3) (h21 : a2 < a1) (h31 : a3 < a1) :
    ChainOK (QuadPt z0 a1 z1 a2 z2 a3 z3) z0 (-1) 1 (chain1 0 a1) (chain1 z0 z1) := by
  obtain ⟨⟨q1a, q1b⟩, ⟨q2a, q2b⟩, ⟨q3a, q3b⟩, ⟨q4a, q4b⟩⟩ := hQ
  refine ⟨by norm_num, by simp [chain1], ?_, ?_, ?_, ?_⟩
  · intro l hl; interval_cases l <;> simp [chain1] <;> nlinarith
  · intro l hl; interval_cases l <;> simp [chain1, QuadPt]
  · intro a z hq hne
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [chain1] at hne ⊢ <;>
      nlinarith
  · intro a z hq l hl hn1 hn2
    interval_cases l <;>
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [chain1] at hn1 hn2 ⊢ <;> nlinarith

set_option maxHeartbeats 2000000 in
/-- Counterclockwise quadrilateral, far vertex `3`, upper chain `0, 3`. -/
theorem chainOK_ccw3_up {z0 a1 z1 a2 z2 a3 z3 : ℝ} (h1 : 0 < a1) (h2 : 0 < a2) (h3 : 0 < a3)
    (hQ : ConvQuad 0 z0 a1 z1 a2 z2 a3 z3) (h13 : a1 < a3) (h23 : a2 < a3) :
    ChainOK (QuadPt z0 a1 z1 a2 z2 a3 z3) z0 1 1 (chain1 0 a3) (chain1 z0 z3) := by
  obtain ⟨⟨q1a, q1b⟩, ⟨q2a, q2b⟩, ⟨q3a, q3b⟩, ⟨q4a, q4b⟩⟩ := hQ
  refine ⟨by norm_num, by simp [chain1], ?_, ?_, ?_, ?_⟩
  · intro l hl; interval_cases l <;> simp [chain1] <;> nlinarith
  · intro l hl; interval_cases l <;> simp [chain1, QuadPt]
  · intro a z hq hne
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [chain1] at hne ⊢ <;>
      nlinarith
  · intro a z hq l hl hn1 hn2
    interval_cases l <;>
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [chain1] at hn1 hn2 ⊢ <;> nlinarith

set_option maxHeartbeats 2000000 in
/-- Counterclockwise quadrilateral, far vertex `3`, lower chain `0, 1, 2, 3`. -/
theorem chainOK_ccw3_lo {z0 a1 z1 a2 z2 a3 z3 : ℝ} (h1 : 0 < a1) (h2 : 0 < a2) (h3 : 0 < a3)
    (hQ : ConvQuad 0 z0 a1 z1 a2 z2 a3 z3) (h13 : a1 < a3) (h23 : a2 < a3) :
    ChainOK (QuadPt z0 a1 z1 a2 z2 a3 z3) z0 (-1) 3 (chain3 0 a1 a2 a3) (chain3 z0 z1 z2 z3) := by
  obtain ⟨⟨q1a, q1b⟩, ⟨q2a, q2b⟩, ⟨q3a, q3b⟩, ⟨q4a, q4b⟩⟩ := hQ
  refine ⟨by norm_num, by simp [chain3], ?_, ?_, ?_, ?_⟩
  · intro l hl; interval_cases l <;> simp [chain3] <;> nlinarith
  · intro l hl; interval_cases l <;> simp [chain3, QuadPt]
  · intro a z hq hne
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [chain3] at hne ⊢ <;>
      nlinarith
  · intro a z hq l hl hn1 hn2
    interval_cases l <;>
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [chain3] at hn1 hn2 ⊢ <;> nlinarith

theorem quadPt_swap13 (z0 a1 z1 a2 z2 a3 z3 : ℝ) :
    QuadPt z0 a3 z3 a2 z2 a1 z1 = QuadPt z0 a1 z1 a2 z2 a3 z3 := by
  funext a z; simp only [QuadPt, eq_iff_iff]; tauto

/-- The chains of a convex quadrilateral seen from a vertex (the apex at
`t = 0`, the other vertices at `t > 0` with distinct `t`), in either
orientation: for `s = 1` the upper chain, for `s = -1` the lower one. -/
theorem quad_chain {z0 a1 z1 a2 z2 a3 z3 : ℝ} (h1 : 0 < a1) (h2 : 0 < a2) (h3 : 0 < a3)
    (hQ : ConvQuad 0 z0 a1 z1 a2 z2 a3 z3 ∨ ConvQuad 0 z0 a3 z3 a2 z2 a1 z1)
    (h12 : a1 ≠ a2) (h13 : a1 ≠ a3) (h23 : a2 ≠ a3) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    ∃ m ca cz, ChainOK (QuadPt z0 a1 z1 a2 z2 a3 z3) z0 s m ca cz := by
  -- the counterclockwise case, for any labelling
  have ccw : ∀ {b1 w1 b3 w3 : ℝ}, 0 < b1 → 0 < b3 → b1 ≠ a2 → b1 ≠ b3 → a2 ≠ b3 →
      ConvQuad 0 z0 b1 w1 a2 z2 b3 w3 → ∃ m ca cz, ChainOK (QuadPt z0 b1 w1 a2 z2 b3 w3) z0 s m ca cz := by
    intro b1 w1 b3 w3 hb1 hb3 e12 e13 e23 hq
    rcases hs with rfl | rfl
    · rcases lt_or_gt_of_ne e12 with c12 | c12 <;> rcases lt_or_gt_of_ne e13 with c13 | c13 <;>
        rcases lt_or_gt_of_ne e23 with c23 | c23
      all_goals first
        | exact ⟨_, _, _, chainOK_ccw2_up hb1 h2 hb3 hq (by linarith) (by linarith)⟩
        | exact ⟨_, _, _, chainOK_ccw1_up hb1 h2 hb3 hq (by linarith) (by linarith)⟩
        | exact ⟨_, _, _, chainOK_ccw3_up hb1 h2 hb3 hq (by linarith) (by linarith)⟩
    · rcases lt_or_gt_of_ne e12 with c12 | c12 <;> rcases lt_or_gt_of_ne e13 with c13 | c13 <;>
        rcases lt_or_gt_of_ne e23 with c23 | c23
      all_goals first
        | exact ⟨_, _, _, chainOK_ccw2_lo hb1 h2 hb3 hq (by linarith) (by linarith)⟩
        | exact ⟨_, _, _, chainOK_ccw1_lo hb1 h2 hb3 hq (by linarith) (by linarith)⟩
        | exact ⟨_, _, _, chainOK_ccw3_lo hb1 h2 hb3 hq (by linarith) (by linarith)⟩
  rcases hQ with hq | hq
  · exact ccw h1 h3 h12 h13 h23 hq
  · rw [← quadPt_swap13]; exact ccw h3 h1 h23.symm h13.symm h12.symm hq

/-- All chains of one point set end at the same far point. -/
theorem ChainOK.far_eq {Q : ℝ → ℝ → Prop} {z0 s s' : ℝ} {m m' : ℕ} {ca cz ca' cz' : ℕ → ℝ}
    (h : ChainOK Q z0 s m ca cz) (h' : ChainOK Q z0 s' m' ca' cz') :
    ca m = ca' m' ∧ cz m = cz' m' := by
  by_contra hne
  have h1 := h.far _ _ (h'.mem m' le_rfl) (fun e => hne ⟨e.1.symm, e.2.symm⟩)
  have h2 := h'.far _ _ (h.mem m le_rfl) hne
  linarith

theorem ChainOK.far_pos {Q : ℝ → ℝ → Prop} {z0 s : ℝ} {m : ℕ} {ca cz : ℕ → ℝ}
    (h : ChainOK Q z0 s m ca cz) : 0 < ca m := by
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
/-- **Two quadrilaterals sharing the apex, in the oblique frame.**  The apex
`(0, 0, z0)`, the quadrilateral `0, 1, 2, 3` on the first ray (oblique
coordinates `(a_i, 0, z_i)`) and `0, 1′, 2′, 3′` on the second (`(0, b_j, w_j)`),
each convex in its plane (either orientation) with distinct positive `t`, and
seven distinct depths: Rupert (Corollary T1 of `FEWER-FACES-PROOFS.md` §7). -/
theorem isRupert_twoQuads_frame (O r1 r2 : ℝ²) (hρ : 0 < cross2 r1 r2)
    {z0 a1 z1 a2 z2 a3 z3 b1 w1 b2 w2 b3 w3 : ℝ}
    (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3)
    (hQ1 : ConvQuad 0 z0 a1 z1 a2 z2 a3 z3 ∨ ConvQuad 0 z0 a3 z3 a2 z2 a1 z1)
    (hQ2 : ConvQuad 0 z0 b1 w1 b2 w2 b3 w3 ∨ ConvQuad 0 z0 b3 w3 b2 w2 b1 w1)
    (ha12 : a1 ≠ a2) (ha13 : a1 ≠ a3) (ha23 : a2 ≠ a3)
    (hb12 : b1 ≠ b2) (hb13 : b1 ≠ b3) (hb23 : b2 ≠ b3)
    (hz : Function.Injective ![z0, z1, z2, z3, w1, w2, w3]) :
    IsRupert ({oblPt O r1 r2 0 0 z0, oblPt O r1 r2 a1 0 z1, oblPt O r1 r2 a2 0 z2,
      oblPt O r1 r2 a3 0 z3, oblPt O r1 r2 0 b1 w1, oblPt O r1 r2 0 b2 w2,
      oblPt O r1 r2 0 b3 w3} : Finset ℝ³) := by
  set Q1 := QuadPt z0 a1 z1 a2 z2 a3 z3 with hQ1def
  set Q2 := QuadPt z0 b1 w1 b2 w2 b3 w3 with hQ2def
  -- distinct depths, as equalities between entries
  have zne : ∀ i j : Fin 7, i ≠ j → ![z0, z1, z2, z3, w1, w2, w3] i ≠ ![z0, z1, z2, z3, w1, w2, w3] j :=
    fun i j h e => h (hz e)
  -- the far points (from the upper chains)
  obtain ⟨m0, ca0, cz0, C10⟩ := quad_chain ha1 ha2 ha3 hQ1 ha12 ha13 ha23 1 (Or.inl rfl)
  obtain ⟨n0, cb0, dz0, C20⟩ := quad_chain hb1 hb2 hb3 hQ2 hb12 hb13 hb23 1 (Or.inl rfl)
  -- distinct depths between the two rays
  have n14 : z1 ≠ w1 := fun h => absurd (hz (a₁ := 1) (a₂ := 4) (by simp [h])) (by decide)
  have n15 : z1 ≠ w2 := fun h => absurd (hz (a₁ := 1) (a₂ := 5) (by simp [h])) (by decide)
  have n16 : z1 ≠ w3 := fun h => absurd (hz (a₁ := 1) (a₂ := 6) (by simp [h])) (by decide)
  have n24 : z2 ≠ w1 := fun h => absurd (hz (a₁ := 2) (a₂ := 4) (by simp [h])) (by decide)
  have n25 : z2 ≠ w2 := fun h => absurd (hz (a₁ := 2) (a₂ := 5) (by simp [h])) (by decide)
  have n26 : z2 ≠ w3 := fun h => absurd (hz (a₁ := 2) (a₂ := 6) (by simp [h])) (by decide)
  have n34 : z3 ≠ w1 := fun h => absurd (hz (a₁ := 3) (a₂ := 4) (by simp [h])) (by decide)
  have n35 : z3 ≠ w2 := fun h => absurd (hz (a₁ := 3) (a₂ := 5) (by simp [h])) (by decide)
  have n36 : z3 ≠ w3 := fun h => absurd (hz (a₁ := 3) (a₂ := 6) (by simp [h])) (by decide)
  -- the far depths differ
  have hfar : cz0 m0 ≠ dz0 n0 := by
    have hA := C10.mem m0 le_rfl
    have hB := C20.mem n0 le_rfl
    have hA0 := C10.far_pos
    have hB0 := C20.far_pos
    simp only [QuadPt] at hA hB
    rcases hA with ⟨e, -⟩ | ⟨-, e1⟩ | ⟨-, e1⟩ | ⟨-, e1⟩
    · linarith
    all_goals rcases hB with ⟨e, -⟩ | ⟨-, e2⟩ | ⟨-, e2⟩ | ⟨-, e2⟩
    all_goals first
      | linarith
      | (rwa [e1, e2])
  set s : ℝ := if dz0 n0 < cz0 m0 then 1 else -1 with hsdef
  have hs : s = 1 ∨ s = -1 := by rw [hsdef]; split_ifs <;> simp
  have hs' : -s = 1 ∨ -s = -1 := by rcases hs with h | h <;> rw [h] <;> simp
  obtain ⟨m, ca, cz, C1⟩ := quad_chain ha1 ha2 ha3 hQ1 ha12 ha13 ha23 s hs
  obtain ⟨n, cb, dz, C2⟩ := quad_chain hb1 hb2 hb3 hQ2 hb12 hb13 hb23 (-s) hs'
  have eA := C1.far_eq C10
  have eB := C2.far_eq C20
  have hAB : s * dz n < s * cz m := by
    rw [eA.2, eB.2, hsdef]
    split_ifs with h
    · linarith
    · have : cz0 m0 < dz0 n0 := lt_of_le_of_ne (not_lt.mp h) hfar
      linarith
  have hA0 := C1.far_pos
  have hB0 := C2.far_pos
  -- membership of chain points
  have mem1 : ∀ a z, Q1 a z → oblPt O r1 r2 a 0 z ∈ ({oblPt O r1 r2 0 0 z0, oblPt O r1 r2 a1 0 z1,
      oblPt O r1 r2 a2 0 z2, oblPt O r1 r2 a3 0 z3, oblPt O r1 r2 0 b1 w1, oblPt O r1 r2 0 b2 w2,
      oblPt O r1 r2 0 b3 w3} : Finset ℝ³) := by
    intro a z h; simp only [hQ1def, QuadPt] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  have mem2 : ∀ b z, Q2 b z → oblPt O r1 r2 0 b z ∈ ({oblPt O r1 r2 0 0 z0, oblPt O r1 r2 a1 0 z1,
      oblPt O r1 r2 a2 0 z2, oblPt O r1 r2 a3 0 z3, oblPt O r1 r2 0 b1 w1, oblPt O r1 r2 0 b2 w2,
      oblPt O r1 r2 0 b3 w3} : Finset ℝ³) := by
    intro b z h; simp only [hQ2def, QuadPt] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  -- the side conditions on each ray
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
  -- the far conditions
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
  refine isRupert_triShadow_injOn O r1 r2 hρ C1.one_le C2.one_le s hs ca cz cb dz C1.start.1
    C2.start.1 (by rw [C2.start.2, C1.start.2]) C1.inc C2.inc _
    (fun l hl => mem1 _ _ (C1.mem l hl)) (fun l hl => mem2 _ _ (C2.mem l hl)) ?_ ?_ hAB
  · -- every point: coordinates and side conditions
    have q10 : Q1 0 z0 := Or.inl ⟨rfl, rfl⟩
    have q20 : Q2 0 z0 := Or.inl ⟨rfl, rfl⟩
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨0, 0, z0, rfl, le_rfl, le_rfl, Or.inl (by nlinarith), fun _ => side1 0 z0 q10,
        fun _ => side2 0 z0 q20⟩
    · rcases far1 a1 z1 (Or.inr (Or.inl ⟨rfl, rfl⟩)) with h | ⟨e1, e2⟩
      · exact ⟨a1, 0, z1, rfl, ha1.le, le_rfl, Or.inl (by linarith), fun _ => side1 a1 z1
          (Or.inr (Or.inl ⟨rfl, rfl⟩)), fun h => absurd h ha1.ne'⟩
      · exact ⟨a1, 0, z1, rfl, ha1.le, le_rfl, Or.inr (Or.inl (by rw [e1, e2])), fun _ => side1 a1 z1
          (Or.inr (Or.inl ⟨rfl, rfl⟩)), fun h => absurd h ha1.ne'⟩
    · rcases far1 a2 z2 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) with h | ⟨e1, e2⟩
      · exact ⟨a2, 0, z2, rfl, ha2.le, le_rfl, Or.inl (by linarith), fun _ => side1 a2 z2
          (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))), fun h => absurd h ha2.ne'⟩
      · exact ⟨a2, 0, z2, rfl, ha2.le, le_rfl, Or.inr (Or.inl (by rw [e1, e2])), fun _ => side1 a2 z2
          (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))), fun h => absurd h ha2.ne'⟩
    · rcases far1 a3 z3 (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))) with h | ⟨e1, e2⟩
      · exact ⟨a3, 0, z3, rfl, ha3.le, le_rfl, Or.inl (by linarith), fun _ => side1 a3 z3
          (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))), fun h => absurd h ha3.ne'⟩
      · exact ⟨a3, 0, z3, rfl, ha3.le, le_rfl, Or.inr (Or.inl (by rw [e1, e2])), fun _ => side1 a3 z3
          (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))), fun h => absurd h ha3.ne'⟩
    · rcases far2 b1 w1 (Or.inr (Or.inl ⟨rfl, rfl⟩)) with h | ⟨e1, e2⟩
      · exact ⟨0, b1, w1, rfl, le_rfl, hb1.le, Or.inl (by linarith), fun h => absurd h hb1.ne',
          fun _ => side2 b1 w1 (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
      · exact ⟨0, b1, w1, rfl, le_rfl, hb1.le, Or.inr (Or.inr (by rw [e1, e2])),
          fun h => absurd h hb1.ne', fun _ => side2 b1 w1 (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    · rcases far2 b2 w2 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) with h | ⟨e1, e2⟩
      · exact ⟨0, b2, w2, rfl, le_rfl, hb2.le, Or.inl (by linarith), fun h => absurd h hb2.ne',
          fun _ => side2 b2 w2 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩
      · exact ⟨0, b2, w2, rfl, le_rfl, hb2.le, Or.inr (Or.inr (by rw [e1, e2])),
          fun h => absurd h hb2.ne', fun _ => side2 b2 w2 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩
    · rcases far2 b3 w3 (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))) with h | ⟨e1, e2⟩
      · exact ⟨0, b3, w3, rfl, le_rfl, hb3.le, Or.inl (by linarith), fun h => absurd h hb3.ne',
          fun _ => side2 b3 w3 (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))⟩
      · exact ⟨0, b3, w3, rfl, le_rfl, hb3.le, Or.inr (Or.inr (by rw [e1, e2])),
          fun h => absurd h hb3.ne', fun _ => side2 b3 w3 (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))⟩
  · -- distinct depths on `V`
    set p : Fin 7 → ℝ³ := ![oblPt O r1 r2 0 0 z0, oblPt O r1 r2 a1 0 z1, oblPt O r1 r2 a2 0 z2,
      oblPt O r1 r2 a3 0 z3, oblPt O r1 r2 0 b1 w1, oblPt O r1 r2 0 b2 w2,
      oblPt O r1 r2 0 b3 w3] with hp
    have hpz : ∀ k, ⟪p k, ez⟫ = ![z0, z1, z2, z3, w1, w2, w3] k := by
      intro k; fin_cases k <;> simp [hp, inner_oblPt_ez]
    have hpV : ∀ y, y ∈ ({oblPt O r1 r2 0 0 z0, oblPt O r1 r2 a1 0 z1, oblPt O r1 r2 a2 0 z2,
        oblPt O r1 r2 a3 0 z3, oblPt O r1 r2 0 b1 w1, oblPt O r1 r2 0 b2 w2,
        oblPt O r1 r2 0 b3 w3} : Finset ℝ³) → ∃ k, p k = y := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩, ⟨5, rfl⟩, ⟨6, rfl⟩]
    intro y hy y' hy' h
    obtain ⟨i, rfl⟩ := hpV y hy
    obtain ⟨j, rfl⟩ := hpV y' hy'
    simp only [hpz] at h
    rw [hz h]

end Minimality

end
