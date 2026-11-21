module

public import Minimality.SameView

@[expose] public section

/-!
# The snap form: a test good at the exact corner certifies a neighbourhood (17.1, 17.1′)

The depth difference at an oblique view `d` is exactly linear in the three cosines `h_ij` of the
axes at `1` (`depth_sub_viewOf`); at the exact corner (`h = 0`) it is the snap depth
`snapDepth`.  On the obtuse octant with `|h_ij| ≤ δ L_i L_j` the pair radius `SnapAbove`
keeps the order of the snap (`depth_lt_of_snapAbove`).  A certified rim (`RimTestR`, depths left
open) whose failure patterns are all broken at the snap is Rupert for the whole neighbourhood:
for a quad (`isRupert_type24_snap4`) and a triangle (`isRupert_type24_snap3`).
-/

namespace Minimality
open Finset
open scoped RealInnerProductSpace

namespace Type24

/-- **The snap depth** at the oblique view `d`, relative to the cap: the depth at the exact corner
with the same oblique coordinates and axis lengths. -/
noncomputable def snapDepth (x : Fin 7 → ℝ³) (d : Fin 3 → ℝ) (v : Fin 7) : ℝ :=
  d 0 * ‖x 0 - x 1‖ ^ 2 * oblX0 x v + d 1 * ‖x 2 - x 1‖ ^ 2 * oblX2 x v +
    d 2 * ‖x 6 - x 1‖ ^ 2 * oblX6 x v

/-- The coefficient of `h_ab = ⟪e_a, e_b⟫` in `z_v − z_w` at the view `d` (17.1). -/
noncomputable def cosCoefAB (x : Fin 7 → ℝ³) (d : Fin 3 → ℝ) (v w : Fin 7) : ℝ :=
  d 0 * (oblX2 x v - oblX2 x w) + d 1 * (oblX0 x v - oblX0 x w)

/-- The coefficient of `h_ac`. -/
noncomputable def cosCoefAC (x : Fin 7 → ℝ³) (d : Fin 3 → ℝ) (v w : Fin 7) : ℝ :=
  d 0 * (oblX6 x v - oblX6 x w) + d 2 * (oblX0 x v - oblX0 x w)

/-- The coefficient of `h_bc`. -/
noncomputable def cosCoefBC (x : Fin 7 → ℝ³) (d : Fin 3 → ℝ) (v w : Fin 7) : ℝ :=
  d 1 * (oblX6 x v - oblX6 x w) + d 2 * (oblX2 x v - oblX2 x w)

/-- **The obtuse octant at `1` within cosine `δ`**: `h_ij ≤ 0` and `−h_ij ≤ δ L_i L_j`. -/
def ObtuseNear (x : Fin 7 → ℝ³) (δ : ℝ) : Prop :=
  ⟪x 0 - x 1, x 2 - x 1⟫ ≤ 0 ∧ ⟪x 0 - x 1, x 6 - x 1⟫ ≤ 0 ∧ ⟪x 2 - x 1, x 6 - x 1⟫ ≤ 0 ∧
    -⟪x 0 - x 1, x 2 - x 1⟫ ≤ δ * (‖x 0 - x 1‖ * ‖x 2 - x 1‖) ∧
    -⟪x 0 - x 1, x 6 - x 1⟫ ≤ δ * (‖x 0 - x 1‖ * ‖x 6 - x 1‖) ∧
    -⟪x 2 - x 1, x 6 - x 1⟫ ≤ δ * (‖x 2 - x 1‖ * ‖x 6 - x 1‖)

/-- **`v` is above `w` at the snap, with octant margin `δ`** (17.1′ for the form `z_v − z_w`). -/
def SnapAbove (x : Fin 7 → ℝ³) (d : Fin 3 → ℝ) (δ : ℝ) (v w : Fin 7) : Prop :=
  δ * (max 0 (cosCoefAB x d v w) * (‖x 0 - x 1‖ * ‖x 2 - x 1‖) +
      max 0 (cosCoefAC x d v w) * (‖x 0 - x 1‖ * ‖x 6 - x 1‖) +
      max 0 (cosCoefBC x d v w) * (‖x 2 - x 1‖ * ‖x 6 - x 1‖)) <
    snapDepth x d v - snapDepth x d w

variable {x : Fin 7 → ℝ³} (T : Type24 x)
include T



omit T in
/-- **A certified rim at a view**, depth pattern left open (Theorem 7.3 with Lemma 16.27′, any
`k`): `isRupert_of_edgeView_uniform_robust`'s hypotheses without the depths. -/
def RimTestR (V : Finset ℝ³) (u : ℝ³) {k : ℕ} (p : ZMod k → ℝ³) : Prop :=
  ∃ M D W : Finset ℝ³, u ≠ 0 ∧ 3 ≤ k ∧ (∀ i, p i ∈ V) ∧ (∀ i, p i ∉ M) ∧
    (∀ i j, j ≠ i → j ≠ i + 1 → 0 < det3 (p (i + 1) - p i) (p j - p i) u) ∧
    (∀ y ∈ V, y ∉ M → y ∉ D → (∀ j, y ≠ p j) → ∀ i, 0 < det3 (p (i + 1) - p i) (y - p i) u) ∧
    NoHDNAt W u ∧ (∀ i, p i ∈ W) ∧
    (∀ m ∈ M, ∃ i : ZMod k, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      m = p i + s • (p (i + 1) - p i) + δ • u) ∧
    (∀ y ∈ D, ∃ i : ZMod k, ∃ h : ℝ, h ≠ 0 ∧ y = p i - h • u)

omit T in
theorem RimTestR.isRupert {V : Finset ℝ³} {u : ℝ³} {k : ℕ} [NeZero k] {p : ZMod k → ℝ³}
    (h : RimTestR V u p) (hz : IsRobustUnimodal fun i => ⟪p i, u⟫) : IsRupert V := by
  obtain ⟨M, D, W, hu, hk, hV, hM0, hc, hr, hnd, hW, hMm, hD⟩ := h
  exact isRupert_of_edgeView_uniform_robust V M D W u hu hk p hV hM0 hc hr hz hnd hW hMm hD



omit T in
/-- Four reals with three equal are never weakly diagonal-separated either way. -/
theorem four_three_equal {w0 w1 w2 w3 : ℝ}
    (h1 : ¬ max w1 w3 ≤ min w0 w2) (h2 : ¬ max w0 w2 ≤ min w1 w3)
    (h : (w0 = w1 ∧ w1 = w2) ∨ (w0 = w1 ∧ w1 = w3) ∨ (w0 = w2 ∧ w2 = w3) ∨
      (w1 = w2 ∧ w2 = w3)) : False := by
  rcases h with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;>
  rcases le_total w0 w1 with c1 | c1 <;> rcases le_total w0 w2 with c2 | c2 <;>
  rcases le_total w0 w3 with c3 | c3 <;>
  first
  | (refine absurd ?_ h1; simp only [max_le_iff, le_min_iff]
     refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith)
  | (refine absurd ?_ h2; simp only [max_le_iff, le_min_iff]
     refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith)

omit T in
/-- **No closed failure pattern** (§17.0, 17.1′): no two interleaved pairs of positions of the
cyclic sequence are weakly depth-separated, in either orientation.  `B + a, B + b, B + c, B + e`
with `a < b < c < e < k` are four positions in cyclic order. -/
def NoWeakSep {k : ℕ} (z : ZMod k → ℝ) : Prop :=
  ∀ (B : ZMod k) (a b c e : ℕ), a < b → b < c → c < e → e < k →
    ¬ (max (z (B + b)) (z (B + e)) ≤ min (z (B + a)) (z (B + c))) ∧
      ¬ (max (z (B + a)) (z (B + c)) ≤ min (z (B + b)) (z (B + e)))

omit T in
theorem NoWeakSep.key {k : ℕ} {z : ZMod k → ℝ} (h : NoWeakSep z) (i : ZMod k)
    {p q r : ℕ} (hpq : p < q) (hqr : q < r) (hrk : r < k) (hp : 0 < p)
    (u1 u2 u3 : ZMod k) (e1 : i + (p : ZMod k) = u1) (e2 : i + (q : ZMod k) = u2)
    (e3 : i + (r : ZMod k) = u3)
    (hz : (z i = z u1 ∧ z u1 = z u2) ∨ (z i = z u1 ∧ z u1 = z u3) ∨
      (z i = z u2 ∧ z u2 = z u3) ∨ (z u1 = z u2 ∧ z u2 = z u3)) : False := by
  obtain ⟨n1, n2⟩ := h i 0 p q r hp hpq hqr hrk
  simp only [Nat.cast_zero, add_zero, e1, e2, e3] at n1 n2
  exact four_three_equal n1 n2 hz

omit T in
/-- **A rim with no closed failure pattern is robustly unimodal** (`k ≥ 4`; ties allowed). -/
theorem NoWeakSep.isRobustUnimodal {k : ℕ} [NeZero k] (hk : 4 ≤ k) {z : ZMod k → ℝ}
    (h : NoWeakSep z) : IsRobustUnimodal z where
  noPeaks B a b c d hab hbc hcd hdk hh := by
    obtain ⟨n1, -⟩ := h B a b c d hab hbc hcd hdk
    obtain ⟨h1, h2, h3, h4⟩ := hh
    exact n1 (by simp only [max_le_iff, le_min_iff]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith)
  noLevelRun B a b c d hab hbc hcd hdk he := by
    obtain ⟨n1, n2⟩ := h B a b c d hab hbc hcd hdk
    constructor
    · rintro ⟨h1, h2⟩
      exact n2 (by simp only [max_le_iff, le_min_iff]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith)
    · rintro ⟨h1, h2⟩
      exact n1 (by simp only [max_le_iff, le_min_iff]; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith)
  noTriple i j l hij hjl hil h1 h2 := by
    obtain ⟨m, hmi, hmj, hml⟩ : ∃ m : ZMod k, m ≠ i ∧ m ≠ j ∧ m ≠ l := by
      by_contra hcon
      push Not at hcon
      have hsub : (Finset.univ : Finset (ZMod k)) ⊆ {i, j, l} := by
        intro m _
        by_cases a : m = i
        · simp [a]
        by_cases b : m = j
        · simp [b]
        simp [hcon m a b]
      have := (Finset.card_le_card hsub).trans Finset.card_le_three
      simp [ZMod.card] at this
      omega
    have hv : ∀ x : ZMod k, i + (((x - i).val : ℕ) : ZMod k) = x := by
      intro x; rw [ZMod.natCast_zmod_val]; ring
    have hv0 : ∀ x : ZMod k, x ≠ i → 0 < (x - i).val := fun x hx =>
      ZMod.val_pos.mpr (sub_ne_zero.mpr hx)
    have hvne : ∀ x y : ZMod k, x ≠ y → (x - i).val ≠ (y - i).val := by
      intro x y hxy hh
      apply hxy
      have := congrArg (fun n : ℕ => i + (n : ZMod k)) hh
      simpa [hv] using this
    have hlt : ∀ x : ZMod k, (x - i).val < k := fun x => ZMod.val_lt _
    have c := h1.trans h2
    have n1 := hvne j l hjl
    have n2 := hvne j m (Ne.symm hmj)
    have n3 := hvne l m (Ne.symm hml)
    have p1 := hv0 j (Ne.symm hij)
    have p2 := hv0 l (Ne.symm hil)
    have p3 := hv0 m hmi
    have q1 := hlt j
    have q2 := hlt l
    have q3 := hlt m
    rcases lt_or_gt_of_ne n1 with a | a <;> rcases lt_or_gt_of_ne n2 with b | b <;>
      rcases lt_or_gt_of_ne n3 with d | d
    · -- j < l < m
      exact h.key i (by omega) (by omega) q3 p1 j l m (hv j) (hv l) (hv m) (Or.inl ⟨h1, h2⟩)
    · -- j < m < l
      exact h.key i (by omega) (by omega) q2 p1 j m l (hv j) (hv m) (hv l) (Or.inr (Or.inl ⟨h1, h2⟩))
    · omega
    · -- m < j < l
      exact h.key i (by omega) (by omega) q2 p3 m j l (hv m) (hv j) (hv l) (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))
    · -- l < j < m
      exact h.key i (by omega) (by omega) q3 p2 l j m (hv l) (hv j) (hv m) (Or.inl ⟨c, h2.symm⟩)
    · omega
    · -- l < m < j
      exact h.key i (by omega) (by omega) q1 p2 l m j (hv l) (hv m) (hv j) (Or.inr (Or.inl ⟨c, h2.symm⟩))
    · -- m < l < j
      exact h.key i (by omega) (by omega) q1 p3 m l j (hv m) (hv l) (hv j)
        (Or.inr (Or.inr (Or.inl ⟨c, h2.symm⟩)))



end Type24

end Minimality
