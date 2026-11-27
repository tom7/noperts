module

public import Minimality.Type24CellWall
public import Minimality.ChordTop

/-!
# RAY-CT: Lemma CT at the `T_0` edge view `x₂ - x₀` (type 24, cell `A0`)

Fable cover tests (nopert229 notes/FABLE-COVER-REPLY.md Idea 1 / Idea 3, COVTEST in
tools/genleaves/FACENORM24.md): at the `T_0` ray `x₂ - x₀` the open cell next to the ray is `A0` (rim
`cA = 1.2.5.3.6`), the chord `6 → 1` is a rim edge, and Lemma CT (ChordTop.lean,
`isDepthSeparatedPair_chordTop`) gives a depth-separated pair.  Here the same statement in the cell framework,
with a strict apex (Split) certificate.

* `apexCert_chordTop` (any rim, `k ≥ 3`): strictly convex rim at `w` (one sign `ρ` for every rim determinant),
  the chord `a → a + 1` strictly antipodal (`ρ · det3 (X a - X (a-1)) (X (a+2) - X (a+1)) w < 0`), both chord
  ends strictly below every other rim corner, distinct depths ⟹ `ApexCert X w` (base edge `a-1 → a`, apex
  `a+1` if `z a < z (a+1)`; base edge `a+1 → a+2`, apex `a` otherwise).  The strict apex comes from the cone
  identity at the apex (`det3_cone`).
* `RayCT02 x F`: the region form at the ray (shape letters `F.f 8 (x 2) < F.f 8 (x 0)` (cell `A0`, not `B0`) and
  `c₃ < 1` (A* at the ray: `det3 (x₆ - x₃) (x₂ - x₁) (x₂ - x₀) = (1 - c₃) det24`), Gram letters
  `max z₁ z₆ < z₂, z₅, z₃` and `z₁ ≠ z₆` at `x₂ - x₀`).  The views `x₂ - x₀ + η (x₆ - x₀)` (small `η > 0`) are in
  the open cell `A0` and carry the certificate (`rayCT02_exists_cellCert`).
* Leaves: `splitAny_of_rayCT02`, the `π_24` twin (`x₆ - x₀`, chord `1 → 2`, A* ⟺ `b₃ < 1`)
  `splitAny_of_rayCT02_twin`, the cell-cover form `not_cellCoverResidue_of_rayCT02`, hole facts
  `holeLeaf_not_rayCT02(_twin)`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace Topology
open Finset Filter
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.HC Minimality.T24.SF Minimality.T24.Stmt
  Minimality.T24.M4

namespace Minimality.T24.Cell

/-! ## Lemma CT as a strict apex certificate (any rim) -/

section CT

variable {k : ℕ}

theorem rayCT_add_natCast_ne (b : ZMod k) {n : ℕ} (h0 : 0 < n) (hn : n < k) : b + (n : ZMod k) ≠ b := by
  intro h
  have h' : ((n : ℕ) : ZMod k) = 0 := by
    have := congrArg (fun y => y - b) h
    simpa using this
  rw [ZMod.natCast_eq_zero_iff] at h'
  exact absurd (Nat.le_of_dvd h0 h') (by omega)

theorem rayCT_val_neg_one (hk : 1 ≤ k) : (-1 : ZMod k).val = k - 1 := by
  have e : (-1 : ZMod k) = ((k - 1 : ℕ) : ZMod k) := by
    rw [Nat.cast_sub hk, ZMod.natCast_self]; push_cast; ring
  rw [e, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]

/-- The cone identity behind the strict apex: `det3 (·, ·, w)` is a 2-form of rank 2, so Cramer's rule in the
plane `w^⊥` holds for it (`det3 p q w · v ≡ det3 v q w · p + det3 p v w · q` modulo `w`). -/
theorem det3_cone (p q v d w : ℝ³) :
    Split.det3 p q w * Split.det3 d v w =
      Split.det3 v q w * Split.det3 d p w + Split.det3 p v w * Split.det3 d q w := by
  simp only [Split.det3]; ring

/-- **Lemma CT, apex form.**  Rim `X : ZMod k → ℝ³` (`k ≥ 3`) at `w` with every rim determinant of sign `ρ`;
the chord `a → a + 1` strictly antipodal; both chord ends strictly below every other rim corner, with distinct
depths.  Then the rim carries a strict-apex certificate `ApexCert X w`. -/
theorem apexCert_chordTop [NeZero k] (hk : 3 ≤ k) (X : ZMod k → ℝ³) (w : ℝ³) {ρ : ℝ} (hρ : ρ = 1 ∨ ρ = -1)
    (hrim : ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 → 0 < ρ * Split.det3 (X (i + 1) - X i) (X j - X i) w)
    (a : ZMod k) (hA : ρ * Split.det3 (X a - X (a - 1)) (X (a + 2) - X (a + 1)) w < 0)
    (hz : ∀ j, j ≠ a → j ≠ a + 1 → max ⟪X a, w⟫ ⟪X (a + 1), w⟫ < ⟪X j, w⟫)
    (hne : ⟪X a, w⟫ ≠ ⟪X (a + 1), w⟫) : ApexCert X w := by
  have d10 : a + 1 ≠ a := by
    have := rayCT_add_natCast_ne a (n := 1) (by norm_num) (by omega); simpa using this
  have d20 : a + 2 ≠ a := by
    have := rayCT_add_natCast_ne a (n := 2) (by norm_num) (by omega); simpa using this
  have d21 : a + 2 ≠ a + 1 := by
    have := rayCT_add_natCast_ne (a + 1) (n := 1) (by norm_num) (by omega)
    intro h; apply this; push_cast; linear_combination h
  have dm0 : a - 1 ≠ a := by
    have := rayCT_add_natCast_ne (a - 1) (n := 1) (by norm_num) (by omega)
    intro h; apply this; push_cast; linear_combination -h
  have dm1 : a + 1 ≠ a - 1 := by
    have := rayCT_add_natCast_ne (a - 1) (n := 2) (by norm_num) (by omega)
    intro h; apply this; push_cast; linear_combination h
  have e2 : a + 1 + 1 = a + 2 := by ring
  have em : a - 1 + 1 = a := by ring
  have habs : ∀ y : ℝ, 0 < ρ * y → |y| = ρ * y := by
    intro y hy
    rcases hρ with rfl | rfl
    · rw [one_mul] at hy ⊢; exact abs_of_pos hy
    · rw [neg_one_mul] at hy ⊢; exact abs_of_neg (by linarith)
  have sw : ∀ p q : ℝ³, Split.det3 p q w = -Split.det3 q p w := by
    intro p q; simp only [Split.det3]; ring
  have lin : ∀ d y P Q : ℝ³, Split.det3 d (y - Q) w = Split.det3 d (y - P) w - Split.det3 d (Q - P) w := by
    intro d y P Q; simp only [Split.det3, PiLp.sub_apply]; ring
  have rot : ∀ A B J : ℝ³, Split.det3 (J - B) (A - B) w = Split.det3 (B - A) (J - A) w := by
    intro A B J; simp only [Split.det3, PiLp.sub_apply]; ring
  have self0 : ∀ p : ℝ³, Split.det3 p p w = 0 := by intro p; simp only [Split.det3]; ring
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- `z a < z (a + 1)`: base edge `a - 1 → a`, apex `a + 1`
    refine ⟨a - 1, a + 1, dm1, by rw [em]; exact d10, ?_, 1, Or.inl rfl, ?_, ?_⟩
    · intro j hj0 hj1 hj2
      rw [em] at hj1 ⊢
      set e := X a - X (a - 1) with he
      have hD : ∀ m, m ≠ a - 1 → m ≠ a → 0 < ρ * Split.det3 e (X m - X (a - 1)) w := by
        intro m h0 h1
        have := hrim (a - 1) m h0 (by rw [em]; exact h1)
        rwa [em] at this
      have hDj := hD j hj0 hj1
      have hDc := hD (a + 1) dm1 d10
      rw [sw (X j - X (a - 1)), sw (X (a + 1) - X (a - 1)), abs_neg, abs_neg, habs _ hDj, habs _ hDc]
      -- cone at `a + 1` spanned by `p = X (a+2) - X (a+1)` and `q = X a - X (a+1)`
      have hid := det3_cone (X (a + 2) - X (a + 1)) (X a - X (a + 1)) (X j - X (a + 1)) e w
      rw [lin e (X j) (X (a - 1)) (X (a + 1)), lin e (X a) (X (a - 1)) (X (a + 1)), he, self0] at hid
      have hPQ : 0 < ρ * Split.det3 (X (a + 2) - X (a + 1)) (X a - X (a + 1)) w := by
        have := hrim (a + 1) a d10.symm (by rw [e2]; exact d20.symm)
        rwa [e2] at this
      have hVQ : 0 < ρ * Split.det3 (X j - X (a + 1)) (X a - X (a + 1)) w := by
        rw [rot]; exact hrim a j hj1 hj2
      have hPV : 0 ≤ ρ * Split.det3 (X (a + 2) - X (a + 1)) (X j - X (a + 1)) w := by
        by_cases hj3 : j = a + 2
        · rw [hj3, self0, mul_zero]
        · have := hrim (a + 1) j hj2 (by rw [e2]; exact hj3)
          rw [e2] at this; exact this.le
      have key : (ρ * Split.det3 (X (a + 2) - X (a + 1)) (X a - X (a + 1)) w) *
          (ρ * Split.det3 (X a - X (a - 1)) (X j - X (a - 1)) w -
            ρ * Split.det3 (X a - X (a - 1)) (X (a + 1) - X (a - 1)) w) =
          (ρ * Split.det3 (X j - X (a + 1)) (X a - X (a + 1)) w) *
            (ρ * Split.det3 (X a - X (a - 1)) (X (a + 2) - X (a + 1)) w) -
          (ρ * Split.det3 (X (a + 2) - X (a + 1)) (X j - X (a + 1)) w) *
            (ρ * Split.det3 (X a - X (a - 1)) (X (a + 1) - X (a - 1)) w) := by
        linear_combination (ρ * ρ) * hid
      have hR : (ρ * Split.det3 (X j - X (a + 1)) (X a - X (a + 1)) w) *
            (ρ * Split.det3 (X a - X (a - 1)) (X (a + 2) - X (a + 1)) w) -
          (ρ * Split.det3 (X (a + 2) - X (a + 1)) (X j - X (a + 1)) w) *
            (ρ * Split.det3 (X a - X (a - 1)) (X (a + 1) - X (a - 1)) w) < 0 := by
        have h1 := mul_neg_of_pos_of_neg hVQ hA
        have h2 := mul_nonneg hPV hDc.le
        linarith
      rw [← key] at hR
      have := neg_of_mul_neg_right hR hPQ.le
      linarith
    · intro j hj
      rw [show j - (a - 1) - 1 = j - a by ring, show a + 1 - (a - 1) - 1 = a + 1 - a by ring,
        zmod_val_add_one_sub (by omega)] at hj
      have hj0 : j - a = 0 := (ZMod.val_eq_zero _).mp (by omega)
      rw [sub_eq_zero.mp hj0]
      linarith
    · intro j hj
      rw [show j - (a - 1) - 1 = j - a by ring, show a + 1 - (a - 1) - 1 = a + 1 - a by ring,
        zmod_val_add_one_sub (by omega)] at hj
      have hja : j ≠ a := by
        rintro rfl; rw [sub_self, ZMod.val_zero] at hj; omega
      have hja1 : j ≠ a + 1 := by
        rintro rfl; rw [zmod_val_add_one_sub (by omega)] at hj; omega
      have := hz j hja hja1
      have := le_max_right ⟪X a, w⟫ ⟪X (a + 1), w⟫
      linarith
  · -- `z (a + 1) < z a`: base edge `a + 1 → a + 2`, apex `a`
    refine ⟨a + 1, a, d10.symm, by rw [e2]; exact d20.symm, ?_, -1, Or.inr rfl, ?_, ?_⟩
    · intro j hj0 hj1 hj2
      rw [e2] at hj1 ⊢
      set p := X (a + 2) - X (a + 1) with hp
      have hE : ∀ m, m ≠ a + 1 → m ≠ a + 2 → 0 < ρ * Split.det3 p (X m - X (a + 1)) w := by
        intro m h0 h1
        have := hrim (a + 1) m h0 (by rw [e2]; exact h1)
        rwa [e2] at this
      have hEj := hE j hj0 hj1
      have hEc := hE a d10.symm d20.symm
      rw [sw (X j - X (a + 1)), sw (X a - X (a + 1)), abs_neg, abs_neg, habs _ hEj, habs _ hEc]
      -- cone at `a` spanned by `q = X (a+1) - X a` and `r = X (a-1) - X a`
      have hid := det3_cone (X (a + 1) - X a) (X (a - 1) - X a) (X j - X a) p w
      rw [lin p (X j) (X (a + 1)) (X a)] at hid
      have hpq : Split.det3 p (X (a + 1) - X a) w = -Split.det3 p (X a - X (a + 1)) w := by
        simp only [Split.det3, PiLp.sub_apply]; ring
      have hpr : Split.det3 p (X (a - 1) - X a) w =
          Split.det3 (X a - X (a - 1)) (X (a + 2) - X (a + 1)) w := by
        rw [hp]; simp only [Split.det3, PiLp.sub_apply]; ring
      rw [hpq, hpr] at hid
      have hQR : 0 < ρ * Split.det3 (X (a + 1) - X a) (X (a - 1) - X a) w :=
        hrim a (a - 1) dm0 dm1.symm
      have hVR : 0 ≤ ρ * Split.det3 (X j - X a) (X (a - 1) - X a) w := by
        by_cases hj3 : j = a - 1
        · rw [hj3, self0, mul_zero]
        · rw [rot]
          have := hrim (a - 1) j hj3 (by rw [em]; exact hj2)
          rw [em] at this; exact this.le
      have hQV : 0 < ρ * Split.det3 (X (a + 1) - X a) (X j - X a) w :=
        hrim a j hj2 (fun h => hj0 h)
      have key : (ρ * Split.det3 (X (a + 1) - X a) (X (a - 1) - X a) w) *
          (ρ * Split.det3 p (X j - X (a + 1)) w - ρ * Split.det3 p (X a - X (a + 1)) w) =
          (ρ * Split.det3 (X j - X a) (X (a - 1) - X a) w) * (-(ρ * Split.det3 p (X a - X (a + 1)) w)) +
          (ρ * Split.det3 (X (a + 1) - X a) (X j - X a) w) *
            (ρ * Split.det3 (X a - X (a - 1)) (X (a + 2) - X (a + 1)) w) := by
        linear_combination (ρ * ρ) * hid
      have hR : (ρ * Split.det3 (X j - X a) (X (a - 1) - X a) w) * (-(ρ * Split.det3 p (X a - X (a + 1)) w)) +
          (ρ * Split.det3 (X (a + 1) - X a) (X j - X a) w) *
            (ρ * Split.det3 (X a - X (a - 1)) (X (a + 2) - X (a + 1)) w) < 0 := by
        have h1 := mul_nonpos_of_nonneg_of_nonpos hVR (neg_nonpos.mpr hEc.le)
        have h2 := mul_neg_of_pos_of_neg hQV hA
        linarith
      rw [← key] at hR
      have := neg_of_mul_neg_right hR hQR.le
      linarith
    · intro j hj
      rw [show a - (a + 1) - 1 = a - 1 - (a + 1) by ring, zmod_val_sub_two hk] at hj
      have hja : j ≠ a := by
        intro h
        rw [h, show a - (a + 1) - 1 = a - 1 - (a + 1) by ring, zmod_val_sub_two hk] at hj; omega
      have hja1 : j ≠ a + 1 := by
        intro h
        rw [h, show a + 1 - (a + 1) - 1 = -1 by ring, rayCT_val_neg_one (by omega)] at hj; omega
      have := hz j hja hja1
      have := le_max_left ⟪X a, w⟫ ⟪X (a + 1), w⟫
      linarith
    · intro j hj
      rw [show a - (a + 1) - 1 = a - 1 - (a + 1) by ring, zmod_val_sub_two hk] at hj
      have hv : (j - (a + 1) - 1).val = (-1 : ZMod k).val := by
        rw [rayCT_val_neg_one (by omega)]; have := ZMod.val_lt (j - (a + 1) - 1); omega
      have hj1 : j = a + 1 := by
        have := ZMod.val_injective k hv
        linear_combination this
      subst hj1
      linarith

end CT

/-! ## The rim sign of an open cell -/

variable {x : Fin 7 → ℝ³}

/-- On an open cell of `cells24`-type data, every rim determinant has one sign `ρ`. -/
theorem rimSign_of_cell (F : S0xFac 9 s0x_S24 x) (c : Cell24) {w : ℝ³}
    (hcell : CellAt F c.U (univ \ c.U) w) :
    ∃ ρ : ℝ, (ρ = 1 ∨ ρ = -1) ∧ ∀ i j : ZMod c.k, j ≠ i → j ≠ i + 1 →
      0 < ρ * Split.det3 (x (c.r (i + 1)) - x (c.r i)) (x (c.r j) - x (c.r i)) w := by
  rcases LexEP.strictRimN_of_openCell (by have := c.hk; omega) F c.inj c.cyc hcell with h | h
  · exact ⟨1, Or.inl rfl, fun i j h0 h1 => by
      rw [one_mul]; exact h (c.r j) i (fun e => h0 (c.inj e)) (fun e => h1 (c.inj e))⟩
  · refine ⟨-1, Or.inr rfl, fun i j h0 h1 => ?_⟩
    have e1 : -(-i - 1) = i + 1 := by ring
    have e2 : -(-i - 1 + 1) = i := by ring
    have := h (c.r j) (-i - 1) (by simp only [e1]; exact fun e => h1 (c.inj e))
      (by simp only [e2]; exact fun e => h0 (c.inj e))
    simp only [e1, e2] at this
    have e : Split.det3 (x (c.r i) - x (c.r (i + 1))) (x (c.r j) - x (c.r (i + 1))) w =
        -Split.det3 (x (c.r (i + 1)) - x (c.r i)) (x (c.r j) - x (c.r i)) w := by
      simp only [Split.det3, PiLp.sub_apply]; ring
    rw [e] at this; linarith

/-! ## The region at the ray `x₂ - x₀` -/

/-- **RayCT02:** the region form of Lemma CT at the `T_0` edge view `r = x₂ - x₀` (chord `6 → 1` of the
`A0` rim `1.2.5.3.6`).  Shape letters: facet `8 = 346` strictly in front at `r` (`F.f 8 (x 2) < F.f 8 (x 0)`,
the cell next to the ray is `A0`, not `B0`) and `c₃ < 1` (the chord is strictly antipodal at `r`).  Gram letters
at `r` (`z_v = ⟪x v, r⟫`): the chord ends `1, 6` strictly below `2, 5, 3`, and `z₁ ≠ z₆`.  (Under `OB1 x` the
letter `z₁ < z₂` is automatic.) -/
def RayCT02 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  F.f 8 (x 2) < F.f 8 (x 0) ∧ oblX6 x 3 < 1 ∧
    max ⟪x 1, x 2 - x 0⟫ ⟪x 6, x 2 - x 0⟫ < ⟪x 2, x 2 - x 0⟫ ∧
    max ⟪x 1, x 2 - x 0⟫ ⟪x 6, x 2 - x 0⟫ < ⟪x 5, x 2 - x 0⟫ ∧
    max ⟪x 1, x 2 - x 0⟫ ⟪x 6, x 2 - x 0⟫ < ⟪x 3, x 2 - x 0⟫ ∧
    ⟪x 1, x 2 - x 0⟫ ≠ ⟪x 6, x 2 - x 0⟫

theorem rayCT_ev_lt (A B C D : ℝ) (h : A < C) :
    ∀ᶠ η : ℝ in 𝓝[>] 0, A + η * B < C + η * D := by
  have hc : Continuous fun η : ℝ => (C + η * D) - (A + η * B) := by fun_prop
  exact (Split.AcuteEdge.ev_pos hc (by simpa using h)).mono fun η hη => by linarith

theorem rayCT_ev_ne (A B C D : ℝ) (h : A ≠ C) :
    ∀ᶠ η : ℝ in 𝓝[>] 0, A + η * B ≠ C + η * D := by
  have hc : Continuous fun η : ℝ => ((C + η * D) - (A + η * B)) ^ 2 := by fun_prop
  refine (Split.AcuteEdge.ev_pos hc (by simpa using sq_pos_of_ne_zero (sub_ne_zero.mpr h.symm))).mono
    fun η hη e => ?_
  rw [e, sub_self] at hη; simp at hη

/-- **A* and the orientation at the ray** (frame computation): `det3 (x₆ - x₃) (x₂ - x₁) (x₂ - x₀) =
(1 - c₃) det24` and `det3 (x₂ - x₁) (x₆ - x₁) (x₂ - x₀) = - det24`. -/
theorem rayCT02_frame (F : S0xFac 9 s0x_S24 x) :
    Split.det3 (x 6 - x 3) (x 2 - x 1) (x 2 - x 0) = (1 - oblX6 x 3) * det24 x ∧
      Split.det3 (x 2 - x 1) (x 6 - x 1) (x 2 - x 0) = -det24 x := by
  have T := type24OfFac F
  have e63 : x 6 - x 3 = (-oblX0 x 3) • (x 0 - x 1) + (-oblX2 x 3) • (x 2 - x 1) +
      (1 - oblX6 x 3) • (x 6 - x 1) := by
    rw [T.rep 3]; module
  have e21 : x 2 - x 1 = (0 : ℝ) • (x 0 - x 1) + (1 : ℝ) • (x 2 - x 1) + (0 : ℝ) • (x 6 - x 1) := by
    module
  have e61 : x 6 - x 1 = (0 : ℝ) • (x 0 - x 1) + (0 : ℝ) • (x 2 - x 1) + (1 : ℝ) • (x 6 - x 1) := by
    module
  have e20 : x 2 - x 0 = (-1 : ℝ) • (x 0 - x 1) + (1 : ℝ) • (x 2 - x 1) + (0 : ℝ) • (x 6 - x 1) := by
    module
  have f1 := Minimality.T24.M4.det3_frame x (-oblX0 x 3) (-oblX2 x 3) (1 - oblX6 x 3) 0 1 0 (-1) 1 0
  have f2 := Minimality.T24.M4.det3_frame x 0 1 0 0 0 1 (-1) 1 0
  rw [← e63, ← e21, ← e20] at f1
  rw [← e21, ← e61, ← e20] at f2
  rw [Split.det3_eq_minimality, Split.det3_eq_minimality, f1, f2]
  constructor <;> ring

/-- **RAY-CT certificate:** on `RayCT02 x F`, some view `x₂ - x₀ + η (x₆ - x₀)` (small `η > 0`) lies in the
open cell `A0` and carries a strict-apex certificate on its rim (Lemma CT, `apexCert_chordTop`). -/
theorem rayCT02_exists_apex {F : S0xFac 9 s0x_S24 x} (h : RayCT02 x F) :
    ∃ w : ℝ³, CellAt F cellA0.U (univ \ cellA0.U) w ∧ ApexCert (fun i => x (cellA0.r i)) w := by
  obtain ⟨h8, hc3, h2, h5, h3, hne⟩ := h
  rw [max_lt_iff] at h2 h5 h3
  have T := type24OfFac F
  -- the open cell along `x₂ - x₀ + η (x₆ - x₀)`
  have hU : ∀ t ∈ cellA0.U, 0 < ⟪F.N t, x 2 - x 0⟫ ∨
      (⟪F.N t, x 2 - x 0⟫ = 0 ∧ 0 < ⟪F.N t, x 6 - x 0⟫) := by
    intro t ht
    have ht' : t ∈ ({5, 6, 7} : Finset (Fin 9)) := ht
    simp only [mem_insert, mem_singleton] at ht'
    left
    rw [F.inner_sub]
    rcases ht' with rfl | rfl | rfl
    · rw [F.zero 5 2 (by decide)]; linarith [F.neg 5 0 (by decide)]
    · rw [F.zero 6 2 (by decide)]; linarith [F.neg 6 0 (by decide)]
    · rw [F.zero 7 2 (by decide)]; linarith [F.neg 7 0 (by decide)]
  have hD : ∀ t ∉ cellA0.U, ⟪F.N t, x 2 - x 0⟫ < 0 ∨
      (⟪F.N t, x 2 - x 0⟫ = 0 ∧ ⟪F.N t, x 6 - x 0⟫ < 0) := by
    intro t ht
    have ht' : t ∉ ({5, 6, 7} : Finset (Fin 9)) := ht
    rw [F.inner_sub, F.inner_sub]
    have ht'' : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 8 := by revert t; decide
    rcases ht'' with rfl | rfl | rfl | rfl | rfl | rfl
    · right; rw [F.zero 0 2 (by decide), F.zero 0 0 (by decide)]
      exact ⟨by ring, by linarith [F.neg 0 6 (by decide)]⟩
    · left; rw [F.zero 1 0 (by decide)]; linarith [F.neg 1 2 (by decide)]
    · right; rw [F.zero 2 2 (by decide), F.zero 2 0 (by decide)]
      exact ⟨by ring, by linarith [F.neg 2 6 (by decide)]⟩
    · left; rw [F.zero 3 0 (by decide)]; linarith [F.neg 3 2 (by decide)]
    · left; rw [F.zero 4 0 (by decide)]; linarith [F.neg 4 2 (by decide)]
    · left; linarith
  have evC := cellAt_eventually_of_wall F cellA0.U hU hD
  -- depths and determinants along the segment are affine in `η`
  have ez : ∀ v : Fin 7, ∀ η : ℝ, ⟪x v, x 2 - x 0 + η • (x 6 - x 0)⟫ =
      ⟪x v, x 2 - x 0⟫ + η * ⟪x v, x 6 - x 0⟫ := fun v η => by
    rw [inner_add_right, real_inner_smul_right]
  have ed : ∀ p q : ℝ³, ∀ η : ℝ, Split.det3 p q (x 2 - x 0 + η • (x 6 - x 0)) =
      Split.det3 p q (x 2 - x 0) + η * Split.det3 p q (x 6 - x 0) := fun p q η => by
    simp only [Split.det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  obtain ⟨fA, fO⟩ := rayCT02_frame F
  have hdet : det24 x ≠ 0 := T.det_ne
  have hAO0 : 0 < -(Split.det3 (x 6 - x 3) (x 2 - x 1) (x 2 - x 0) *
      Split.det3 (x 2 - x 1) (x 6 - x 1) (x 2 - x 0)) := by
    rw [fA, fO]
    have := mul_pos (sub_pos.mpr hc3) (sq_pos_of_ne_zero hdet)
    nlinarith
  have evAO : ∀ᶠ η : ℝ in 𝓝[>] 0, 0 < -((Split.det3 (x 6 - x 3) (x 2 - x 1) (x 2 - x 0) +
      η * Split.det3 (x 6 - x 3) (x 2 - x 1) (x 6 - x 0)) *
      (Split.det3 (x 2 - x 1) (x 6 - x 1) (x 2 - x 0) + η * Split.det3 (x 2 - x 1) (x 6 - x 1) (x 6 - x 0))) := by
    have hc : Continuous fun η : ℝ => -((Split.det3 (x 6 - x 3) (x 2 - x 1) (x 2 - x 0) +
        η * Split.det3 (x 6 - x 3) (x 2 - x 1) (x 6 - x 0)) *
        (Split.det3 (x 2 - x 1) (x 6 - x 1) (x 2 - x 0) +
          η * Split.det3 (x 2 - x 1) (x 6 - x 1) (x 6 - x 0))) := by fun_prop
    exact Split.AcuteEdge.ev_pos hc (by simpa using hAO0)
  obtain ⟨η, hcell, hAO, l12, l62, l15, l65, l13, l63, ln⟩ := (evC.and (evAO.and
    ((rayCT_ev_lt _ ⟪x 1, x 6 - x 0⟫ _ ⟪x 2, x 6 - x 0⟫ h2.1).and
    ((rayCT_ev_lt _ ⟪x 6, x 6 - x 0⟫ _ ⟪x 2, x 6 - x 0⟫ h2.2).and
    ((rayCT_ev_lt _ ⟪x 1, x 6 - x 0⟫ _ ⟪x 5, x 6 - x 0⟫ h5.1).and
    ((rayCT_ev_lt _ ⟪x 6, x 6 - x 0⟫ _ ⟪x 5, x 6 - x 0⟫ h5.2).and
    ((rayCT_ev_lt _ ⟪x 1, x 6 - x 0⟫ _ ⟪x 3, x 6 - x 0⟫ h3.1).and
    ((rayCT_ev_lt _ ⟪x 6, x 6 - x 0⟫ _ ⟪x 3, x 6 - x 0⟫ h3.2).and
    (rayCT_ev_ne _ ⟪x 1, x 6 - x 0⟫ _ ⟪x 6, x 6 - x 0⟫ hne))))))))).exists
  rw [← ed, ← ed] at hAO
  simp only [← ez] at l12 l62 l15 l65 l13 l63 ln
  set w := x 2 - x 0 + η • (x 6 - x 0) with hw
  refine ⟨w, hcell, ?_⟩
  obtain ⟨ρ, hρ, hrim⟩ := rimSign_of_cell F cellA0 hcell
  have hrim5 : ∀ i j : ZMod 5, j ≠ i → j ≠ i + 1 →
      0 < ρ * Split.det3 (x (cA (i + 1)) - x (cA i)) (x (cA j) - x (cA i)) w := hrim
  have ev : cA 0 = 1 ∧ cA (0 + 1) = 2 ∧ cA 4 = 6 ∧ cA (4 - 1) = 3 ∧ cA (4 + 2) = 2 ∧ cA (4 + 1) = 1 ∧
      cA 1 = 2 ∧ cA 2 = 5 ∧ cA 3 = 3 := by decide
  have hO := hrim5 0 4 (by decide) (by decide)
  simp only [ev] at hO
  have hρ2 : ρ * ρ = 1 := by rcases hρ with rfl | rfl <;> norm_num
  refine apexCert_chordTop (k := 5) (by norm_num) (fun i => x (cA i)) w hρ hrim5 4 ?_ ?_ ?_
  · simp only [ev]
    have hm : (ρ * Split.det3 (x 6 - x 3) (x 2 - x 1) w) * (ρ * Split.det3 (x 2 - x 1) (x 6 - x 1) w) < 0 := by
      have e : (ρ * Split.det3 (x 6 - x 3) (x 2 - x 1) w) * (ρ * Split.det3 (x 2 - x 1) (x 6 - x 1) w) =
          Split.det3 (x 6 - x 3) (x 2 - x 1) w * Split.det3 (x 2 - x 1) (x 6 - x 1) w := by
        linear_combination (Split.det3 (x 6 - x 3) (x 2 - x 1) w * Split.det3 (x 2 - x 1) (x 6 - x 1) w) * hρ2
      rw [e]; linarith
    exact neg_of_mul_neg_left hm hO.le
  · intro j hj4 hj0
    have hj : j = 1 ∨ j = 2 ∨ j = 3 := by revert j; decide
    rcases hj with rfl | rfl | rfl
    · simp only [ev]; exact max_lt l62 l12
    · simp only [ev]; exact max_lt l65 l15
    · simp only [ev]; exact max_lt l63 l13
  · simp only [ev]; exact fun e => ln e.symm

/-- **RAY-CT (cell form):** `RayCT02 x F` gives a cell certificate of `A0`. -/
theorem rayCT02_exists_cellCert {F : S0xFac 9 s0x_S24 x} (h : RayCT02 x F) :
    ∃ w : ℝ³, CellCert F cellA0 w := by
  obtain ⟨w, hcell, hA⟩ := rayCT02_exists_apex h
  exact ⟨w, hcell, Or.inr (Or.inl hA)⟩

/-- **RAY-CT (Split leaf):** `RayCT02 x F` gives `Gen.SplitAny F`. -/
theorem splitAny_of_rayCT02 {F : S0xFac 9 s0x_S24 x} (h : RayCT02 x F) : Gen.SplitAny F := by
  obtain ⟨w, hcell, hA⟩ := rayCT02_exists_apex h
  exact splitAny_of_cellApex F cellA0 hcell hA

/-- **RAY-CT, `π_24` twin** (ray `x₆ - x₀`, chord `1 → 2`, A* ⟺ `b₃ < 1`):
`RayCT02 (x ∘ Sym.pi24) (Sym.sym24 F)` gives `Gen.SplitAny F`. -/
theorem splitAny_of_rayCT02_twin {F : S0xFac 9 s0x_S24 x}
    (h : RayCT02 (x ∘ Sym.pi24) (Sym.sym24 F)) : Gen.SplitAny F :=
  Sym.splitAny24_sym F (splitAny_of_rayCT02 h)

/-- **RAY-CT in the cell cover:** a list containing `A0` has empty cell-cover residue on `RayCT02` (either
side). -/
theorem not_cellCoverResidue_of_rayCT02 {L : List Cell24} (hL : cellA0 ∈ L) {F : S0xFac 9 s0x_S24 x}
    (h : RayCT02 x F ∨ RayCT02 (x ∘ Sym.pi24) (Sym.sym24 F)) : ¬ CellCoverResidue L x F := by
  intro hres
  rcases h with h | h
  · obtain ⟨w, hw⟩ := rayCT02_exists_cellCert h
    exact (hres.2.2.2 cellA0 hL w).1 hw
  · obtain ⟨w, hw⟩ := rayCT02_exists_cellCert h
    exact (hres.2.2.2 cellA0 hL w).2 hw

/-- **RAY-CT hole fact:** `HoleLeaf x F` excludes `RayCT02 x F`. -/
theorem holeLeaf_not_rayCT02 {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : ¬ RayCT02 x F :=
  fun h => hF.2.2.2.2.1 (splitAny_of_rayCT02 h)

/-- **RAY-CT twin hole fact:** `HoleLeaf x F` excludes `RayCT02 (x ∘ Sym.pi24) (Sym.sym24 F)`. -/
theorem holeLeaf_not_rayCT02_twin {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) :
    ¬ RayCT02 (x ∘ Sym.pi24) (Sym.sym24 F) :=
  fun h => hF.2.2.2.2.1 (splitAny_of_rayCT02_twin h)

end Minimality.T24.Cell
