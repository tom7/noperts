module

public import Minimality.Type24CellsE
public import Minimality.Type24GapLemmas2
public import Minimality.Type24RayCT
public import Minimality.MonoCorner

/-!
# P126Cover: the `126` wall of the pentagon `P` carries a certificate unless the letter condition `P126E` holds

nopert229 notes/P126-MECHANISM.md.  Step 2 of the structural cover route (step 1: `Type24A236Cover`, `A236E`).

* Generic part (any `Cell24` `c` and any wall of it, `CellWall`): the strict certificate systems on the rim
  `X = x ∘ c.r` are
  - the `RobUni` sign systems `(i0, L)` (`rForm`: edge `j → j + 1` increasing iff `(j - i0).val < L`;
    `robUni_of_rForm` via `robUni_of_monoCorners`, the `k - 2` corners off `i0, i0 + L` are monotone), and
  - the apex systems `(a, m, σ)`, `m ≠ a, a + 1` (`hForm`: `s · det(X_j - X_m, X_{a+1} - X_a, ·) > 0` for the other
    rim vertices `j`, with `s` a scalar of the sign of the open cell's rim orientation `ρ`; `dForm`: the two arcs
    strictly below / above `z_m`, as in `ApexCert`; `apexCert_of_letters`).
  `WallE F c W s`: every system, together with the wall's facet forms, has failing 1-D Helly letters (`SegLet`) on
  the wall segment, i.e. no system holds strictly anywhere on the open wall.  **`wall_cert_or_E`**:
  `Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE F c W s` (no `OB1`, no `CbarIn`: purely literal).
* The `P.126` instance: `p126Wall` = the segment `[x₂ - x₁, x₆ - x₁]` (facet `126` edge-on), facet forms
  `-N 025, -N 046, N 0345, N 235, N 346` (`012, 016, 236` are automatic, `126` is pushed behind by `x₀ - x₁`);
  `cellP_rho`: on the open cell `P` the rim sign satisfies `ρ · det24 x < 0`, so `s = -det24 x`.
  **`p126_cert_or_E`**, hole facts `holeLeaf_p126E(_twin)`.
* The narrowed open Prop `CellCoverEmptyEP` (`A236E` and `P126E` on `x` and on the `π_24` twin) and its chain.

Deciding test (nopert229 tools/genleaves/runs/p126mech/, PIECES=1, a literal transcription of `P126E`): 73688 sides of
the A236MECH data (36844 points); 0 sides where the wall fails and `P126E` fails, 0 sides where `P126E` holds and the
wall passes, Helly letters = exact midpoint enumeration at every side.  `P126E x ↔ P126E twin` on all 36844 points
(`π_24` fixes `126` and reverses the rim of `P`).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace Topology
open Finset Filter
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.HC Minimality.T24.SF Minimality.T24.Stmt

namespace Minimality.T24.Cell

variable {x : Fin 7 → ℝ³}

/-! ## Generic: certificate systems on a rim -/

/-- The `RobUni` sign system `(i0, L)`: the form of rim edge `j → j + 1`, increasing iff `(j - i0).val < L`. -/
noncomputable def rForm {k : ℕ} (X : ZMod k → ℝ³) (i0 : ZMod k) (L : ℕ) (j : ZMod k) : ℝ³ :=
  if (j - i0).val < L then X (j + 1) - X j else X j - X (j + 1)

/-- **A strict sign system with two changes is `RobUni`:** if all forms `rForm X i0 L` are positive at `w`, the rim
depths are `RobUni` (the corners other than `i0`, `i0 + L` are monotone, at least `k - 2` of them).  No bound on `L`
is needed: for `L = 0` or `L ≥ k` all edges have one direction, so the hypothesis cannot hold, and the corner
argument does not use the bound. -/
theorem robUni_of_rForm {k : ℕ} [NeZero k] (hk : 4 ≤ k) {X : ZMod k → ℝ³} {w : ℝ³} (i0 : ZMod k) {L : ℕ}
    (h : ∀ j, 0 < ⟪rForm X i0 L j, w⟫) : RobUni (fun i => ⟪X i, w⟫) := by
  have : Fact (1 < k) := ⟨by omega⟩
  refine GenPlus.robUni_of_monoCorners hk (univ \ {i0, i0 + (L : ZMod k)}) ?_ ?_
  · have h2 := Finset.card_le_two (a := i0) (b := i0 + (L : ZMod k))
    have hs := Finset.card_sdiff_add_card_inter (univ : Finset (ZMod k)) {i0, i0 + (L : ZMod k)}
    rw [univ_inter, card_univ, ZMod.card] at hs
    omega
  · intro v hv
    rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hv
    obtain ⟨-, hv0, hvL⟩ := hv
    have ht0 : v - i0 ≠ 0 := fun e => hv0 (sub_eq_zero.1 e)
    have htL : (v - i0).val ≠ L := by
      intro e
      apply hvL
      have hc : ((L : ℕ) : ZMod k) = v - i0 := by rw [← e, ZMod.natCast_zmod_val]
      rw [hc]; ring
    have hpos : 1 ≤ (v - i0).val := by
      rcases Nat.eq_zero_or_pos (v - i0).val with e | e
      · exact absurd ((ZMod.val_eq_zero (v - i0)).1 e) ht0
      · exact e
    have hval : (v - 1 - i0).val = (v - i0).val - 1 := by
      have e : v - 1 - i0 = (v - i0) - 1 := by ring
      rw [e, ZMod.val_sub (by rw [ZMod.val_one]; exact hpos), ZMod.val_one]
    have h1 := h (v - 1)
    have h2 := h v
    simp only [rForm, sub_add_cancel] at h1 h2
    rw [hval] at h1
    show 0 < (⟪X v, w⟫ - ⟪X (v - 1), w⟫) * (⟪X (v + 1), w⟫ - ⟪X v, w⟫)
    by_cases hlt : (v - i0).val < L
    · have h1' : (v - i0).val - 1 < L := by omega
      simp only [h1', hlt, ↓reduceIte, inner_sub_left] at h1 h2
      exact mul_pos h1 h2
    · have h1' : ¬ (v - i0).val - 1 < L := by omega
      simp only [h1', hlt, ↓reduceIte, inner_sub_left] at h1 h2
      nlinarith

/-- **Apex letters give `ApexCert`:** with the rim orientation `ρ` (all rim determinants `ρ`-positive), apex `m`
off the base edge `a → a + 1`, the height letters `ρ · det(X_j - X_m, X_{a+1} - X_a, w) > 0` for the other rim
vertices and the two depth arcs (as in `ApexCert`) give `ApexCert X w`. -/
theorem apexCert_of_letters {k : ℕ} {X : ZMod k → ℝ³} {w : ℝ³} {ρ : ℝ} (hρ : ρ = 1 ∨ ρ = -1)
    (hrim : ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 → 0 < ρ * Split.det3 (X (i + 1) - X i) (X j - X i) w)
    {a m : ZMod k} (hma : m ≠ a) (hma1 : m ≠ a + 1)
    (hh : ∀ j, j ≠ a → j ≠ a + 1 → j ≠ m → 0 < ρ * Split.det3 (X j - X m) (X (a + 1) - X a) w)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hlo : ∀ j : ZMod k, (j - a - 1).val < (m - a - 1).val → σ * (⟪X j, w⟫ - ⟪X m, w⟫) < 0)
    (hhi : ∀ j : ZMod k, (m - a - 1).val < (j - a - 1).val → 0 < σ * (⟪X j, w⟫ - ⟪X m, w⟫)) :
    ApexCert X w := by
  have habs : ∀ j, j ≠ a → j ≠ a + 1 →
      |Split.det3 (X j - X a) (X (a + 1) - X a) w| = ρ * Split.det3 (X (a + 1) - X a) (X j - X a) w := by
    intro j h0 h1
    have hc := hrim a j h0 h1
    have e : Split.det3 (X j - X a) (X (a + 1) - X a) w = -Split.det3 (X (a + 1) - X a) (X j - X a) w := by
      simp only [Split.det3, PiLp.sub_apply]; ring
    rw [e, abs_neg]
    rcases hρ with rfl | rfl
    · rw [one_mul] at hc ⊢; exact abs_of_pos hc
    · rw [neg_one_mul] at hc ⊢; exact abs_of_neg (by linarith)
  refine ⟨a, m, hma, hma1, fun j h0 h1 h2 => ?_, σ, hσ, hlo, hhi⟩
  rw [habs j h0 h1, habs m hma hma1]
  have e : Split.det3 (X (a + 1) - X a) (X m - X a) w - Split.det3 (X (a + 1) - X a) (X j - X a) w =
      Split.det3 (X j - X m) (X (a + 1) - X a) w := by
    simp only [Split.det3, PiLp.sub_apply]; ring
  have := hh j h0 h1 h2
  have k := congrArg (fun t => ρ * t) e
  simp only [mul_sub] at k
  linarith

/-- A letter weighted by a scalar `s` of the sign of `ρ` is a `ρ`-weighted letter. -/
theorem pos_rho_of_pos_s {ρ s D : ℝ} (hρ : ρ = 1 ∨ ρ = -1) (hs : 0 < ρ * s) (h : 0 < s * D) : 0 < ρ * D := by
  rcases hρ with rfl | rfl
  · rw [one_mul] at hs ⊢; exact pos_of_mul_pos_right h hs.le
  · have : s < 0 := by linarith
    have : D < 0 := by nlinarith
    linarith

/-- The height forms of the apex system `(a, m)`: `s • (X_j - X_m) × (X_{a+1} - X_a)` for `j ≠ a, a + 1, m`. -/
noncomputable def hForm {k : ℕ} (X : ZMod k → ℝ³) (s : ℝ) (a m : ZMod k)
    (j : {j : ZMod k // j ≠ a ∧ j ≠ a + 1 ∧ j ≠ m}) : ℝ³ :=
  s • cross (X j.1 - X m) (X (a + 1) - X a)

/-- The depth forms of the apex system `(a, m, σ)`: `σ (z_m - z_j)` on the arc before `m`, `σ (z_j - z_m)` after. -/
noncomputable def dForm {k : ℕ} (X : ZMod k → ℝ³) (a m : ZMod k) (σ : ℝ) (j : {j : ZMod k // j ≠ m}) : ℝ³ :=
  if (j.1 - a - 1).val < (m - a - 1).val then σ • (X m - X j.1) else σ • (X j.1 - X m)

/-- **A wall of a cell** `c`: a segment `[E0, E1]`, facet forms `fac` and a push direction `v` such that every point
of the open segment where the facet forms are positive is a closed-face view of `c` with push `v`. -/
structure CellWall (F : S0xFac 9 s0x_S24 x) (c : Cell24) where
  n : ℕ
  E0 : ℝ³
  E1 : ℝ³
  v : ℝ³
  fac : Fin n → ℝ³
  face : ∀ l : ℝ, 0 < l → l < 1 → (∀ i, 0 < ⟪fac i, (1 - l) • E0 + l • E1⟫) →
    (∀ t ∈ c.U, 0 < ⟪F.N t, (1 - l) • E0 + l • E1⟫ ∨
      (⟪F.N t, (1 - l) • E0 + l • E1⟫ = 0 ∧ 0 < ⟪F.N t, v⟫)) ∧
    (∀ t ∉ c.U, ⟪F.N t, (1 - l) • E0 + l • E1⟫ < 0 ∨
      (⟪F.N t, (1 - l) • E0 + l • E1⟫ = 0 ∧ ⟪F.N t, v⟫ < 0))

/-- **The wall letter condition**: no `RobUni` sign system and no apex system (height forms weighted by `s`) holds
strictly anywhere on the open wall (the 1-D Helly letters `SegLet` of each system plus the facet forms fail). -/
def WallE (F : S0xFac 9 s0x_S24 x) (c : Cell24) (W : CellWall F c) (s : ℝ) : Prop :=
  (∀ (i0 : ZMod c.k) (L : ℕ), ¬ SegLet (Sum.elim W.fac (rForm (fun i => x (c.r i)) i0 L)) W.E0 W.E1) ∧
  ∀ (a m : ZMod c.k) (σ : ℝ), m ≠ a → m ≠ a + 1 → (σ = 1 ∨ σ = -1) →
    ¬ SegLet (Sum.elim W.fac (Sum.elim (hForm (fun i => x (c.r i)) s a m) (dForm (fun i => x (c.r i)) a m σ)))
      W.E0 W.E1

/-- **`wall_cert_or_E`** (any cell, any wall): if `s` has the sign of the rim orientation of the open cell, then a
view next to the wall carries `RobUni` or a strict apex certificate (hence `Gen.LexAny F ∨ Gen.SplitAny F`), or the
letter condition `WallE F c W s` holds. -/
theorem wall_cert_or_E (F : S0xFac 9 s0x_S24 x) (c : Cell24) (W : CellWall F c) {s : ℝ}
    (hs : ∀ w : ℝ³, CellAt F c.U (univ \ c.U) w → ∀ ρ : ℝ, (ρ = 1 ∨ ρ = -1) →
      (∀ i j : ZMod c.k, j ≠ i → j ≠ i + 1 →
        0 < ρ * Split.det3 (x (c.r (i + 1)) - x (c.r i)) (x (c.r j) - x (c.r i)) w) → 0 < ρ * s) :
    Gen.LexAny F ∨ Gen.SplitAny F ∨ WallE F c W s := by
  by_cases hR : ∃ (i0 : ZMod c.k) (L : ℕ), SegLet (Sum.elim W.fac (rForm (fun i => x (c.r i)) i0 L)) W.E0 W.E1
  · obtain ⟨i0, L, hseg⟩ := hR
    obtain ⟨l, hl0, hl1, hall⟩ := (segLet_iff _ _ _).1 hseg
    obtain ⟨hU, hD⟩ := W.face l hl0 hl1 (fun i => hall (Sum.inl i))
    exact Or.inl (lexAny_of_wall_robUni F c hU hD
      (robUni_of_rForm c.hk i0 (fun j => hall (Sum.inr j))))
  by_cases hA : ∃ (a m : ZMod c.k) (σ : ℝ), m ≠ a ∧ m ≠ a + 1 ∧ (σ = 1 ∨ σ = -1) ∧
      SegLet (Sum.elim W.fac (Sum.elim (hForm (fun i => x (c.r i)) s a m) (dForm (fun i => x (c.r i)) a m σ)))
        W.E0 W.E1
  · obtain ⟨a, m, σ, hma, hma1, hσ, hseg⟩ := hA
    obtain ⟨l, hl0, hl1, hall⟩ := (segLet_iff _ _ _).1 hseg
    obtain ⟨hU, hD⟩ := W.face l hl0 hl1 (fun i => hall (Sum.inl i))
    have evC := cellAt_eventually_of_wall F c.U hU hD
    have evL : ∀ᶠ η : ℝ in 𝓝[>] 0, ∀ i, 0 < ⟪Sum.elim (hForm (fun i => x (c.r i)) s a m)
        (dForm (fun i => x (c.r i)) a m σ) i, (1 - l) • W.E0 + l • W.E1 + η • W.v⟫ := by
      rw [eventually_all]
      intro i
      exact ev_inner_pos (hall (Sum.inr i))
    obtain ⟨η, hc, hl⟩ := (evC.and evL).exists
    obtain ⟨ρ, hρ, hrim⟩ := rimSign_of_cell F c hc
    have hρs := hs _ hc ρ hρ hrim
    refine Or.inr (Or.inl (splitAny_of_cellApex F c hc (apexCert_of_letters hρ hrim hma hma1 ?_ hσ ?_ ?_)))
    · intro j h0 h1 h2
      have := hl (Sum.inl ⟨j, h0, h1, h2⟩)
      simp only [Sum.elim_inl, hForm, real_inner_smul_left, ← Split.det3_eq_inner] at this
      exact pos_rho_of_pos_s hρ hρs this
    · intro j hj
      have hjm : j ≠ m := by rintro rfl; exact lt_irrefl _ hj
      have := hl (Sum.inr ⟨j, hjm⟩)
      simp only [Sum.elim_inr, dForm, hj, ↓reduceIte, real_inner_smul_left, inner_sub_left] at this
      linarith
    · intro j hj
      have hjm : j ≠ m := by rintro rfl; exact lt_irrefl _ hj
      have hn : ¬ (j - a - 1).val < (m - a - 1).val := by omega
      have := hl (Sum.inr ⟨j, hjm⟩)
      simp only [Sum.elim_inr, dForm, hn, ↓reduceIte, real_inner_smul_left, inner_sub_left] at this
      exact this
  · push Not at hR hA
    exact Or.inr (Or.inr ⟨fun i0 L => hR i0 L, fun a m σ h1 h2 h3 => hA a m σ h1 h2 h3⟩)

/-! ## The `126` wall of the pentagon `P` -/

/-- **The rim orientation of the open cell `P`:** `ρ · det24 x < 0` (coordinates `w = c₀ (x₀ - x₁) + c₁ (x₂ - x₁) +
c₂ (x₆ - x₁)` with `c₀, c₁, c₂ > 0` from `126, 016, 012` behind; the rim determinant at `6 → 2`, vertex `0`, is
`-(c₀ + c₁ + c₂) det24 x`). -/
theorem cellP_rho (F : S0xFac 9 s0x_S24 x) {w : ℝ³} (hcell : CellAt F cellP.U (univ \ cellP.U) w) {ρ : ℝ}
    (hrim : ∀ i j : ZMod cellP.k, j ≠ i → j ≠ i + 1 →
      0 < ρ * Split.det3 (x (cellP.r (i + 1)) - x (cellP.r i)) (x (cellP.r j) - x (cellP.r i)) w) :
    0 < ρ * -det24 x := by
  have hli := li_of_det3 _ _ _ (det3_e026_ne F)
  have hspan : Submodule.span ℝ (Set.range ![x 0 - x 1, x 2 - x 1, x 6 - x 1]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp)
  have hw : w ∈ Submodule.span ℝ (Set.range ![x 0 - x 1, x 2 - x 1, x 6 - x 1]) := by
    rw [hspan]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hw
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hc
  have hN : ∀ t : Fin 9, ⟪F.N t, w⟫ = c 0 * (F.f t (x 0) - F.f t (x 1)) +
      c 1 * (F.f t (x 2) - F.f t (x 1)) + c 2 * (F.f t (x 6) - F.f t (x 1)) := by
    intro t
    rw [← hc, inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_right, F.inner_sub, F.inner_sub, F.inner_sub]
  have ha : 0 < c 0 := by
    have h5 := hcell.2 5 (by decide)
    rw [hN, F.zero 5 1 (by decide), F.zero 5 2 (by decide), F.zero 5 6 (by decide)] at h5
    have hf := F.neg 5 0 (by decide)
    nlinarith
  have hb : 0 < c 1 := by
    have h1 := hcell.2 1 (by decide)
    rw [hN, F.zero 1 0 (by decide), F.zero 1 1 (by decide), F.zero 1 6 (by decide)] at h1
    have hf := F.neg 1 2 (by decide)
    nlinarith
  have hcc : 0 < c 2 := by
    have h0 := hcell.2 0 (by decide)
    rw [hN, F.zero 0 0 (by decide), F.zero 0 1 (by decide), F.zero 0 2 (by decide)] at h0
    have hf := F.neg 0 6 (by decide)
    nlinarith
  have l : 0 < ρ * Split.det3 (x 2 - x 6) (x 0 - x 6) w := hrim 2 0 (by decide) (by decide)
  have e : Split.det3 (x 2 - x 6) (x 0 - x 6) w = (c 0 + c 1 + c 2) * -det24 x := by
    have e1 : x 2 - x 6 = (0 : ℝ) • (x 0 - x 1) + (1 : ℝ) • (x 2 - x 1) + (-1 : ℝ) • (x 6 - x 1) := by module
    have e2 : x 0 - x 6 = (1 : ℝ) • (x 0 - x 1) + (0 : ℝ) • (x 2 - x 1) + (-1 : ℝ) • (x 6 - x 1) := by module
    rw [← hc, e1, e2, Split.det3_eq_minimality, M4.det3_frame]; ring
  rw [e] at l
  have hsum : 0 < c 0 + c 1 + c 2 := by linarith
  have : 0 < (c 0 + c 1 + c 2) * (ρ * -det24 x) := by linarith
  exact pos_of_mul_pos_right this hsum.le

/-- **The `126` wall of `P`:** the segment `[x₂ - x₁, x₆ - x₁]` (facet `126` edge-on), facet forms
`-N 025, -N 046, N 0345, N 235, N 346`; `012, 016` are behind and `236` in front automatically; push `x₀ - x₁`. -/
noncomputable def p126Wall (F : S0xFac 9 s0x_S24 x) : CellWall F cellP where
  n := 5
  E0 := x 2 - x 1
  E1 := x 6 - x 1
  v := x 0 - x 1
  fac := ![-F.N 2, -F.N 4, F.N 3, F.N 6, F.N 8]
  face := by
    intro l hl0 hl1 hf
    have hNr : ∀ t : Fin 9, ⟪F.N t, (1 - l) • (x 2 - x 1) + l • (x 6 - x 1)⟫ =
        (1 - l) * (F.f t (x 2) - F.f t (x 1)) + l * (F.f t (x 6) - F.f t (x 1)) := by
      intro t
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, F.inner_sub, F.inner_sub]
    have f2 : 0 < ⟪-F.N 2, (1 - l) • (x 2 - x 1) + l • (x 6 - x 1)⟫ := hf 0
    have f4 : 0 < ⟪-F.N 4, (1 - l) • (x 2 - x 1) + l • (x 6 - x 1)⟫ := hf 1
    have f3 : 0 < ⟪F.N 3, (1 - l) • (x 2 - x 1) + l • (x 6 - x 1)⟫ := hf 2
    have f6 : 0 < ⟪F.N 6, (1 - l) • (x 2 - x 1) + l • (x 6 - x 1)⟫ := hf 3
    have f8 : 0 < ⟪F.N 8, (1 - l) • (x 2 - x 1) + l • (x 6 - x 1)⟫ := hf 4
    rw [inner_neg_left] at f2 f4
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · have ht' : t ∈ ({3, 6, 7, 8} : Finset (Fin 9)) := ht
      simp only [mem_insert, mem_singleton] at ht'
      rcases ht' with rfl | rfl | rfl | rfl
      · exact Or.inl f3
      · exact Or.inl f6
      · left
        rw [hNr, F.zero 7 2 (by decide), F.zero 7 6 (by decide)]
        have := F.neg 7 1 (by decide)
        nlinarith
      · exact Or.inl f8
    · have ht' : t ∉ ({3, 6, 7, 8} : Finset (Fin 9)) := ht
      have ht'' : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 4 ∨ t = 5 := by revert t; decide
      rcases ht'' with rfl | rfl | rfl | rfl | rfl
      · left
        rw [hNr, F.zero 0 2 (by decide), F.zero 0 1 (by decide)]
        have := F.neg 0 6 (by decide)
        nlinarith
      · left
        rw [hNr, F.zero 1 6 (by decide), F.zero 1 1 (by decide)]
        have := F.neg 1 2 (by decide)
        nlinarith
      · left; linarith
      · left; linarith
      · right
        refine ⟨?_, ?_⟩
        · rw [hNr, F.zero 5 1 (by decide), F.zero 5 2 (by decide), F.zero 5 6 (by decide)]; ring
        · rw [F.inner_sub, F.zero 5 1 (by decide)]; linarith [F.neg 5 0 (by decide)]

/-- **The letter condition `P126E`**: no strict `RobUni` or apex system of the rim `0.4.6.2.5` anywhere on the open
`126` wall of `P` (`WallE` for `p126Wall`, height forms weighted by `-det24 x`). -/
def P126E (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop := WallE F cellP (p126Wall F) (-det24 x)

/-- **`p126_cert_or_E`:** a view next to the `126` wall of `P` carries `RobUni` or a strict apex certificate on the
rim `0.4.6.2.5` (hence `Gen.LexAny F ∨ Gen.SplitAny F`), or `P126E x F` holds.  No `OB1`, no `CbarIn`. -/
theorem p126_cert_or_E (F : S0xFac 9 s0x_S24 x) : Gen.LexAny F ∨ Gen.SplitAny F ∨ P126E x F :=
  wall_cert_or_E F cellP (p126Wall F) (fun _ hc _ _ hrim => cellP_rho F hc hrim)

/-- **Hole fact:** at a hole point, `P126E x F` holds. -/
theorem holeLeaf_p126E {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : P126E x F :=
  ((p126_cert_or_E F).resolve_left hF.2.2.2.1).resolve_left hF.2.2.2.2.1

/-- **Twin hole fact:** at a hole point, the `π_24` twin satisfies `P126E` too. -/
theorem holeLeaf_p126E_twin {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) :
    P126E (x ∘ Sym.pi24) (Sym.sym24 F) := by
  rcases p126_cert_or_E (Sym.sym24 F) with hL | hS | hE
  · exact absurd (Sym.lexAny_sym F hL) hF.2.2.2.1
  · exact absurd (Sym.splitAny24_sym F hS) hF.2.2.2.2.1
  · exact hE

/-! ## The narrowed open Prop -/

/-- **[OPEN] `CellCoverEmptyEP L`**: on `CbarIn`, `OB1`, with `A236E` and `P126E` on `x` and on the twin, the point
is not in the cell-cover residue of `L`. -/
def CellCoverEmptyEP (L : List Cell24) : Prop :=
  ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), CbarIn x → H24K.SAT.OB1 x → A236E x F →
    A236E (x ∘ Sym.pi24) (Sym.sym24 F) → P126E x F → P126E (x ∘ Sym.pi24) (Sym.sym24 F) →
    ¬ CellCoverResidue L x F

/-- The previous open Prop implies the narrower one. -/
theorem cellCoverEmptyEP_of_cellCoverEmptyE {L : List Cell24} (h : CellCoverEmptyE L) : CellCoverEmptyEP L :=
  fun x F hC hO hA hA' _ _ => h x F hC hO hA hA'

/-- `CellCoverEmptyEP L` rules out the generic hole `HoleLeaf` on `OB1`. -/
theorem not_holeLeaf_of_cellCoverEmptyEP {L : List Cell24} (hN : CellCoverEmptyEP L) (x : Fin 7 → ℝ³)
    (F : S0xFac 9 s0x_S24 x) (hO : H24K.SAT.OB1 x) : ¬ HoleLeaf x F := fun h =>
  hN x F h.1 hO (holeLeaf_a236E h hO) (holeLeaf_a236E_twin h hO) (holeLeaf_p126E h) (holeLeaf_p126E_twin h)
    (holeLeaf_cellCoverResidue L h)

/-- `CellCoverEmptyEP L → Stmt.OpenOB1`. -/
theorem openOB1_of_cellCoverEmptyEP {L : List Cell24} (hN : CellCoverEmptyEP L) : OpenOB1 := fun x F hO hF =>
  not_holeLeaf_of_cellCoverEmptyEP hN x F hO (holeLeaf_of_holeFull hF)

/-- [PROVED] `CellCoverEmptyEP L` and `OSpec.OpenSpecialO` give `Open24Rupert`. -/
theorem open24Rupert_of_cellCoverEmptyEP_O {L : List Cell24} (hN : CellCoverEmptyEP L)
    (hS : OSpec.OpenSpecialO) : Open24Rupert :=
  OSpec.open24Rupert_of_split_O (openOB1_of_cellCoverEmptyEP hN) hS

/-- [PROVED] Headline chain: `CellCoverEmptyEP cells28` and `OSpec.OpenSpecialO` give `Open24Rupert`. -/
theorem open24Rupert_of_cellCoverEmptyEP28_O (hN : CellCoverEmptyEP cells28) (hS : OSpec.OpenSpecialO) :
    Open24Rupert :=
  open24Rupert_of_cellCoverEmptyEP_O hN hS

end Minimality.T24.Cell
