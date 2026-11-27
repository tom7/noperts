module

public import Minimality.Type24HoleAtlas
public import Minimality.ThinCases

@[expose] public section

/-!
# The type-24 hole as one open problem

Companion of nopert229 notes/TYPE24-HOLE-STATEMENT.md.  This module is NOT imported by the main proof and has no
`sorry`: the open problem is stated as `def ... : Prop` (statements, nothing proved).  `Hole24`, `HoleLeaf`,
`Hole24Lemmas`, `Region24` are defined in Type24HoleReduce.lean.

Markers used in the docstrings:
* [PROVED] kernel-checked here (or a re-export of a tree theorem).
* [OPEN]   the open problem itself or a piece of it: a `def ... : Prop` that nobody can prove yet.
* [CONJECTURE] stronger than what the main theorem needs, supported by data only.

Sections:
1. The open statement as the main theorem needs it (`Open24`, `Open24Rupert`, `Open24RupertS`, `AllRupert24`).
2. Form A, leaf-negation form: `HoleLeaf` (in Type24HoleReduce) and `HoleFull` (adds the four proved-lemma flags).
3. Generic / special split: off `OB1` the hole lives on special-position strata.
4. Form B, chamber form: open chambers of the facet arrangement on the view sphere.
5. Form C, corner-frame form `x = c + E ∘ X` (shape `X`, linear map `E`, metric `G = Eᵀ E`), metric-free depths.
6. Form D, quantitative splits: deep-obtuse / near-right corner / cube-corner stratum; fatness from the box lemma.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.RimCell

namespace Minimality.T24.Stmt

/-! ## 1. The open statement -/

/-- [OPEN] **Emptiness form.** No type-24 configuration (seven points `x`, nine facet functionals `fs` with the
type-24 incidences `hh`) lies in the hole.  This is what `Minimality.lean`'s type-24 `sorry` asks for, up to the
extra hypotheses available there (see `main_sorry_of_open24Rupert`). -/
def Open24 : Prop :=
  ∀ (x : Fin 7 → ℝ³) (fs : Fin 9 → ℝ³ →ᵃ[ℝ] ℝ)
    (hh : ∀ t i, (i ∈ s0x_S24 t → fs t (x i) = 0) ∧ (i ∉ s0x_S24 t → fs t (x i) < 0)),
    ¬ Hole24 x (mkFac24 fs hh)

/-- [OPEN] **Rupert form** (weaker than `Open24`, exactly sufficient): every hole point is Rupert.  It admits
proofs by any Rupert mechanism (free views, second-order motions, ...), not only by the generic leaves that the
hole already negates. -/
def Open24Rupert : Prop :=
  ∀ (x : Fin 7 → ℝ³) (fs : Fin 9 → ℝ³ →ᵃ[ℝ] ℝ)
    (hh : ∀ t i, (i ∈ s0x_S24 t → fs t (x i) = 0) ∧ (i ∉ s0x_S24 t → fs t (x i) < 0)),
    Hole24 x (mkFac24 fs hh) → IsRupert (univ.image x)

/-- [PROVED] Emptiness implies the Rupert form. -/
theorem open24Rupert_of_open24 (h : Open24) : Open24Rupert := fun x fs hh hH => (h x fs hh hH).elim

/-- [PROVED] What the main theorem's type-24 `sorry` needs: from the Rupert form, a hole point is not a nopert.
(In `Minimality.lean` the `sorry` also has "no face has an admissible view" (`byThm5Faces`) and injectivity of
`x` as hypotheses; an attempt may use them, this statement does not need them.) -/
theorem main_sorry_of_open24Rupert (h : Open24Rupert) {x : Fin 7 → ℝ³} {fs : Fin 9 → ℝ³ →ᵃ[ℝ] ℝ}
    {hh : ∀ t i, (i ∈ s0x_S24 t → fs t (x i) = 0) ∧ (i ∉ s0x_S24 t → fs t (x i) < 0)}
    (hN : IsNopert (univ.image x)) (hH : Hole24 x (mkFac24 fs hh)) : False :=
  ((isNopert_iff _).1 hN).2 (h x fs hh hH)

/-- [OPEN] **Rupert form with a solid hull** (the weakest form; exactly what the main theorem uses, since a
nopert has a solid hull). -/
def Open24RupertS : Prop :=
  ∀ (x : Fin 7 → ℝ³), (interior (convexHull ℝ ((univ.image x : Finset ℝ³) : Set ℝ³))).Nonempty →
    ∀ (fs : Fin 9 → ℝ³ →ᵃ[ℝ] ℝ)
    (hh : ∀ t i, (i ∈ s0x_S24 t → fs t (x i) = 0) ∧ (i ∉ s0x_S24 t → fs t (x i) < 0)),
    Hole24 x (mkFac24 fs hh) → IsRupert (univ.image x)

/-- [OPEN] **The plain mathematical statement**: every solid with seven vertices and the type-24 facets (eight
triangles 012 016 025 046 126 235 236 346 and the planar quadrilateral 0345) is Rupert. -/
def AllRupert24 : Prop :=
  ∀ (x : Fin 7 → ℝ³), (interior (convexHull ℝ ((univ.image x : Finset ℝ³) : Set ℝ³))).Nonempty →
    ∀ (fs : Fin 9 → ℝ³ →ᵃ[ℝ] ℝ),
    (∀ t i, (i ∈ s0x_S24 t → fs t (x i) = 0) ∧ (i ∉ s0x_S24 t → fs t (x i) < 0)) →
    IsRupert (univ.image x)

/-- [PROVED] **All Rupert forms are one statement**: `Open24RupertS ↔ AllRupert24`, by the proved reduction
`type24_rupert_or_hole` (every type-24 solid is Rupert or in `Hole24`). -/
theorem open24RupertS_iff_allRupert24 : Open24RupertS ↔ AllRupert24 := by
  constructor
  · intro h x hsol fs hh
    rcases type24_rupert_or_hole hsol (fs 0) (fs 1) (fs 5) (fs 7) (fs 4) (fs 2) (fs 3) (fs 6) (fs 8)
      (hh 0) (hh 1) (hh 5) (hh 7) (hh 4) (hh 2) (hh 3) (hh 6) (hh 8) with hR | ⟨hh', hH⟩
    · exact hR
    · exact h x hsol _ hh' hH
  · intro h x hsol fs hh _
    exact h x hsol fs hh

/-- [PROVED] `Open24Rupert → Open24RupertS`. -/
theorem open24RupertS_of_open24Rupert (h : Open24Rupert) : Open24RupertS :=
  fun x _ fs hh hH => h x fs hh hH

/-- [PROVED] The main theorem's type-24 `sorry` from the weakest form. -/
theorem main_sorry_of_open24RupertS (h : Open24RupertS) {x : Fin 7 → ℝ³} {fs : Fin 9 → ℝ³ →ᵃ[ℝ] ℝ}
    {hh : ∀ t i, (i ∈ s0x_S24 t → fs t (x i) = 0) ∧ (i ∉ s0x_S24 t → fs t (x i) < 0)}
    (hN : IsNopert (univ.image x)) (hH : Hole24 x (mkFac24 fs hh)) : False :=
  ((isNopert_iff _).1 hN).2 (h x hN.interior_nonempty fs hh hH)

/-! ## 2. Form A: leaf-negation form -/

/-- **`HoleFull`**: `HoleLeaf` plus the four other free flags of the hole (Root T0, Lemma NC, Adjacency, Lemma E2
face pair), the proved-lemma flags `Hole24Lemmas`. -/
def HoleFull (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  HoleLeaf x F ∧ Hole24Lemmas x

/-- [PROVED] `Hole24 → HoleFull` (the two leading conjuncts of `Hole24`). -/
theorem holeFull_of_hole24 {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (h : Hole24 x F) : HoleFull x F :=
  ⟨h.1, h.2.1⟩

/-- [PROVED] `HoleFull → HoleLeaf`. -/
theorem holeLeaf_of_holeFull {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (h : HoleFull x F) : HoleLeaf x F := h.1

/-- [CONJECTURE] **Leaf form of the open statement**: `HoleLeaf` is empty.  Strictly stronger than `Open24` as a
statement (it drops `Resid24`, the `Q45` / `R1` region bookkeeping and four flags).  Evidence: every point ever
evaluated exactly (about 0.3 M, adversarial sets included, off `OB1` too: MIRROR24) satisfies a leaf. -/
def OpenLeaf : Prop := ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), ¬ HoleLeaf x F

/-- [CONJECTURE] The same with the four extra flags (between `OpenLeaf` and `Open24`). -/
def OpenFull : Prop := ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), ¬ HoleFull x F

/-- [PROVED] `OpenLeaf → OpenFull → Open24`. -/
theorem openFull_of_openLeaf (h : OpenLeaf) : OpenFull := fun x F hF => h x F hF.1

theorem open24_of_openFull (h : OpenFull) : Open24 := fun x fs hh hH => h x _ (holeFull_of_hole24 hH)

/-! ## 3. Generic / special split -/

/-- [PROVED] **Off `OB1` the hole is special position.**  Every hole point has the obtuse corner `OB1` at vertex
1, or lies on a wall `a₄ = 1` / `a₅ = 1` (outside `OB1`), or on the `Q45` special locus `Q45Special'` (a finite
union of tie / collinearity strata).  So the positive-measure part of the hole is inside `OB1`. -/
theorem hole24_ob1_or_special {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x}
    (h : Hole24 x F) :
    H24K.SAT.OB1 x ∨ (¬ H24K.SAT.OB1 x ∧ (oblX0 x 4 = 1 ∨ oblX0 x 5 = 1)) ∨ Q45.Q45Special' F := by
  rcases h.2.2.2 with ⟨-, hS⟩ | ⟨hQ, hR⟩
  · exact Or.inr (Or.inr hS)
  · rcases hR with h | h | h | h | h | h | h | h | h | h | h | h
    · obtain ⟨hO, h4, h5⟩ := h
      refine Or.inr (Or.inl ⟨hO, ?_⟩)
      by_contra hne
      push Not at hne
      exact hQ (Reg.q45HalfPred_of_gt F (lt_of_le_of_ne h4 (Ne.symm hne.1))
        (lt_of_le_of_ne h5 (Ne.symm hne.2)))
    · exact Or.inl h.1
    · exact Or.inl h.1
    · exact Or.inl h.1
    · exact Or.inl h.1
    · exact Or.inl h.1
    · exact Or.inl h.1
    · exact Or.inl h.1
    · exact Or.inl ((A19.ob1_comp_pi24 x).1 h.1)
    · exact Or.inl ((A19.ob1_comp_pi24 x).1 h.1)
    · exact Or.inl ((A19.ob1_comp_pi24 x).1 h.1)
    · exact Or.inl ((A19.ob1_comp_pi24 x).1 h.1)

/-- [OPEN] The generic piece: `HoleFull` on `OB1`.  Implied by `TwoCone.NamedCoverEmpty`
(`Atlas.openOB1_of_namedCoverEmpty`, Type24HoleAtlasNC.lean), the current open form of this piece. -/
def OpenOB1 : Prop := ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), H24K.SAT.OB1 x → ¬ HoleFull x F

/-- [OPEN] The special piece off `OB1` (walls and `Q45` strata). -/
def OpenSpecial : Prop := ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), ¬ H24K.SAT.OB1 x →
  ((oblX0 x 4 = 1 ∨ oblX0 x 5 = 1) ∨ Q45.Q45Special' F) → ¬ HoleFull x F

/-- [PROVED] Generic + special assemble to `Open24` (`Q45Special'` points on `OB1` are covered by `OpenOB1`).
`OpenOB1` and `Open24` are incomparable as far as we know: neither hole is known to contain the other. -/
theorem open24_of_split (h1 : OpenOB1) (h2 : OpenSpecial) : Open24 := by
  intro x fs hh hH
  have hF := holeFull_of_hole24 hH
  rcases hole24_ob1_or_special hH with hO | ⟨hO, hw⟩ | hq
  · exact h1 x _ hO hF
  · exact h2 x _ hO (Or.inl hw) hF
  · by_cases hO : H24K.SAT.OB1 x
    · exact h1 x _ hO hF
    · exact h2 x _ hO (Or.inr hq) hF

/-! ## 4. `Hole24` = generic leaf negations + proved lemmas + `Resid24` + region tag -/

/-- [PROVED] `Hole24 = HoleFull ∧ Resid24 ∧ Region24` (reassociation of the definition).  `Resid24` and `Region24`
are pure bookkeeping: they say which proved lemmas were already spent.  Dropping them gives `OpenFull`, a stronger
statement. -/
theorem hole24_iff_full_tag {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} :
    Hole24 x F ↔ HoleFull x F ∧ Resid24 x ∧ Region24 x F :=
  ⟨fun ⟨a, b, c, d⟩ => ⟨⟨a, b⟩, c, d⟩, fun ⟨⟨a, b⟩, c, d⟩ => ⟨a, b, c, d⟩⟩

/-! ## 4b. Form B: chamber form (open cells of the facet arrangement on the view sphere) -/

/-- Some `k ≥ 4` silhouette cycle `c` (up facets `U`, down facets `Dn`) has a view `u` in its OPEN cell at which
the rim depths are robustly unimodal. -/
def OpenCellRob {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ (k : ℕ) (_ : NeZero k) (c : ZMod k → Fin 7) (U Dn : Finset (Fin 9)) (u : ℝ³),
    4 ≤ k ∧ Function.Injective c ∧ S0xCycUD s0x_S24 c U Dn ∧ CellAt F U Dn u ∧
    RobUni (fun i => ⟪x (c i), u⟫)

/-- Some `k ≥ 3` silhouette cycle has a view `u` with STRICT facings (pattern `pat`) carrying split rows. -/
def OpenCellSplit {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  ∃ (k : ℕ) (_ : NeZero k) (c : ZMod k → Fin 7) (pat : Fin 9 → Bool) (u : ℝ³) (a cc : ZMod k) (σ : ℝ),
    3 ≤ k ∧ Function.Injective c ∧ S0xCycOK s0x_S24 c pat ∧
    (∀ t, (pat t = true → 0 < ⟪F.N t, u⟫) ∧ (pat t = false → ⟪F.N t, u⟫ < 0)) ∧
    cc ≠ a ∧ cc ≠ a + 1 ∧ Split.SplitRows (fun i => x (c i)) u a cc σ

/-- [PROVED] Open-cell robust unimodality is a lex cell. -/
theorem lexAny_of_openCellRob {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (h : OpenCellRob F) :
    Gen.LexAny F := by
  obtain ⟨k, hk0, c, U, Dn, u, hk, hc, hcyc, ha, hR⟩ := h
  exact Atlas.closedCell_lexAny hk F hc hcyc ha ha.cellLe hR

/-- [PROVED] An open-cell split view is a split cell. -/
theorem splitAny_of_openCellSplit {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (h : OpenCellSplit F) :
    Gen.SplitAny F := by
  obtain ⟨k, hk0, c, pat, u, a, cc, σ, hk, hc, hcyc, hfac, hca, hca1, hrows⟩ := h
  refine ⟨k, hk0, c, pat, u, u, a, cc, σ, hk, hc, hcyc, fun t => ⟨fun ht => Or.inl ((hfac t).1 ht),
    fun ht => Or.inl (neg_pos.2 ((hfac t).2 ht))⟩, hca, hca1, hrows⟩

section Perturb
open Filter Topology

theorem ev_pos_cont {g : ℝ → ℝ} (hg : Continuous g) (h : 0 < g 0) : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < g s :=
  Filter.Eventually.filter_mono nhdsWithin_le_nhds ((hg.tendsto 0).eventually (lt_mem_nhds h))

theorem ev_lp {a b : ℝ} (h : h21b_LP a b) : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < a + s * b := by
  rcases h with h | ⟨rfl, h⟩
  · exact ev_pos_cont (g := fun s => a + s * b) (by fun_prop) (by simpa using h)
  · filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
    simpa using mul_pos hs h

theorem ev_lex3 {a b c : ℝ} (h : LexCell.LexPos3 a b c) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < a + s * b + s ^ 2 * c := by
  rcases h with h | ⟨rfl, h | ⟨rfl, h⟩⟩
  · exact ev_pos_cont (g := fun s => a + s * b + s ^ 2 * c) (by fun_prop) (by simpa using h)
  · filter_upwards [self_mem_nhdsWithin,
      ev_pos_cont (g := fun s => b + s * c) (by fun_prop) (by simpa using h)] with s (hs : 0 < s) hb
    have := mul_pos hs hb
    nlinarith
  · filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
    have := mul_pos (pow_pos hs 2) h
    nlinarith

theorem ev_lexLt {p q : ℝ × ℝ × ℝ} (h : LexCell.LexLt3 p q) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), p.1 + s * p.2.1 + s ^ 2 * p.2.2 < q.1 + s * q.2.1 + s ^ 2 * q.2.2 :=
  (ev_lex3 h).mono fun s hs => by nlinarith

theorem ev_robUni {k : ℕ} [NeZero k] {z : ZMod k → ℝ × ℝ × ℝ} (h : LexCell.RobUniLex z) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), RobUni (fun i => (z i).1 + s * (z i).2.1 + s ^ 2 * (z i).2.2) := by
  set w : ℝ → ZMod k → ℝ := fun s i => (z i).1 + s * (z i).2.1 + s ^ 2 * (z i).2.2 with hw
  have key : ∀ (B : ZMod k) (b c d : Fin k), ∀ᶠ s in 𝓝[>] (0:ℝ),
      0 < (b : ℕ) → (b : ℕ) < c → (c : ℕ) < d →
      ¬ (w s (B + (b : ℕ)) ≤ w s B ∧ w s (B + (b : ℕ)) ≤ w s (B + (c : ℕ)) ∧
        w s (B + (d : ℕ)) ≤ w s B ∧ w s (B + (d : ℕ)) ≤ w s (B + (c : ℕ))) := by
    intro B b c d
    by_cases hh : 0 < (b : ℕ) ∧ (b : ℕ) < c ∧ (c : ℕ) < d
    · rcases h B b c d hh.1 hh.2.1 hh.2.2 d.isLt with h1 | h1 | h1 | h1
      · filter_upwards [ev_lexLt h1] with s hs
        intro _ _ _ ⟨e1, _, _, _⟩; exact absurd e1 (not_le.2 hs)
      · filter_upwards [ev_lexLt h1] with s hs
        intro _ _ _ ⟨_, e2, _, _⟩; exact absurd e2 (not_le.2 hs)
      · filter_upwards [ev_lexLt h1] with s hs
        intro _ _ _ ⟨_, _, e3, _⟩; exact absurd e3 (not_le.2 hs)
      · filter_upwards [ev_lexLt h1] with s hs
        intro _ _ _ ⟨_, _, _, e4⟩; exact absurd e4 (not_le.2 hs)
    · exact Filter.Eventually.of_forall fun _ h0 h1 h2 => absurd ⟨h0, h1, h2⟩ hh
  have hall : ∀ᶠ s in 𝓝[>] (0:ℝ), ∀ (B : ZMod k) (b c d : Fin k),
      0 < (b : ℕ) → (b : ℕ) < c → (c : ℕ) < d →
      ¬ (w s (B + (b : ℕ)) ≤ w s B ∧ w s (B + (b : ℕ)) ≤ w s (B + (c : ℕ)) ∧
        w s (B + (d : ℕ)) ≤ w s B ∧ w s (B + (d : ℕ)) ≤ w s (B + (c : ℕ))) :=
    Filter.eventually_all.2 fun B => Filter.eventually_all.2 fun b => Filter.eventually_all.2 fun c =>
      Filter.eventually_all.2 fun d => key B b c d
  filter_upwards [hall] with s hs
  intro B b c d h0 h1 h2 h3
  exact hs B ⟨b, by omega⟩ ⟨c, by omega⟩ ⟨d, h3⟩ h0 h1 h2

/-- [PROVED] Converse: a lex cell `(b, d₁, d₂)` gives an open-cell view `b + s d₁ + s² d₂` (small `s > 0`) with
robustly unimodal depths (every strict lex comparison becomes strict for small `s`). -/
theorem openCellRob_of_lexAny {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (h : Gen.LexAny F) :
    OpenCellRob F := by
  obtain ⟨k, hk0, c, U, Dn, b, d1, d2, hk, hc, hcyc, hU, hD, hR⟩ := h
  have e : ∀ (y : ℝ³) (s : ℝ), ⟪y, b + s • d1 + s ^ 2 • d2⟫ = ⟪y, b⟫ + s * ⟪y, d1⟫ + s ^ 2 * ⟪y, d2⟫ := by
    intro y s; simp only [inner_add_right, inner_smul_right]
  have hU' : ∀ᶠ s in 𝓝[>] (0:ℝ), ∀ t ∈ U, 0 < ⟪F.N t, b + s • d1 + s ^ 2 • d2⟫ :=
    (Filter.eventually_all_finset U).2 fun t ht => (ev_lex3 (hU t ht)).mono fun s hs => by rw [e]; exact hs
  have hD' : ∀ᶠ s in 𝓝[>] (0:ℝ), ∀ t ∈ Dn, ⟪F.N t, b + s • d1 + s ^ 2 • d2⟫ < 0 :=
    (Filter.eventually_all_finset Dn).2 fun t ht => (ev_lex3 (hD t ht)).mono fun s hs => by
      rw [e]; linarith
  obtain ⟨s, hu, hd, hr⟩ := (hU'.and (hD'.and (ev_robUni hR))).exists
  refine ⟨k, hk0, c, U, Dn, b + s • d1 + s ^ 2 • d2, hk, hc, hcyc, ⟨hu, hd⟩, ?_⟩
  have : (fun i => ⟪x (c i), b + s • d1 + s ^ 2 • d2⟫) =
      (fun i => ((⟪x (c i), b⟫, ⟪x (c i), d1⟫, ⟪x (c i), d2⟫) : ℝ × ℝ × ℝ).1 +
        s * ((⟪x (c i), b⟫, ⟪x (c i), d1⟫, ⟪x (c i), d2⟫) : ℝ × ℝ × ℝ).2.1 +
        s ^ 2 * ((⟪x (c i), b⟫, ⟪x (c i), d1⟫, ⟪x (c i), d2⟫) : ℝ × ℝ × ℝ).2.2) := by
    funext i; exact e _ _
  rw [this]; exact hr

/-- [PROVED] Converse: a split cell at `(u, v)` (lex facings) gives one at `u + s v` (strict facings; split rows
are strict, hence open in the view). -/
theorem openCellSplit_of_splitAny {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (h : Gen.SplitAny F) :
    OpenCellSplit F := by
  obtain ⟨k, hk0, c, pat, u, v, a, cc, σ, hk, hc, hcyc, hfac, hca, hca1, hrows⟩ := h
  have e : ∀ (y : ℝ³) (s : ℝ), ⟪y, u + s • v⟫ = ⟪y, u⟫ + s * ⟪y, v⟫ := by
    intro y s; simp only [inner_add_right, inner_smul_right]
  have ed : ∀ (p q : ℝ³) (s : ℝ), Split.det3 p q (u + s • v) = Split.det3 p q u + s * Split.det3 p q v := by
    intro p q s; simp only [Split.det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have hF : ∀ᶠ s in 𝓝[>] (0:ℝ), ∀ t, (pat t = true → 0 < ⟪F.N t, u + s • v⟫) ∧
      (pat t = false → ⟪F.N t, u + s • v⟫ < 0) := by
    refine Filter.eventually_all.2 fun t => ?_
    cases hp : pat t
    · filter_upwards [ev_lp ((hfac t).2 hp)] with s hs
      exact ⟨fun h => absurd h (by simp), fun _ => by rw [e]; linarith⟩
    · filter_upwards [ev_lp ((hfac t).1 hp)] with s hs
      exact ⟨fun _ => by rw [e]; linarith, fun h => absurd h (by simp)⟩
  have hS : ∀ᶠ s in 𝓝[>] (0:ℝ), ∀ i j : ZMod k, i ≠ a → (j = i ∨ j = i + 1) → j ≠ cc →
      0 < σ * (⟪x (c j) - x (c cc), u + s • v⟫ *
        Split.det3 (x (c (i + 1)) - x (c i)) (x (c (a + 1)) - x (c a)) (u + s • v)) := by
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
    by_cases hh : i ≠ a ∧ (j = i ∨ j = i + 1) ∧ j ≠ cc
    · have h0 := hrows i j hh.1 hh.2.1 hh.2.2
      set A := ⟪x (c j) - x (c cc), u⟫
      set B := ⟪x (c j) - x (c cc), v⟫
      set C := Split.det3 (x (c (i + 1)) - x (c i)) (x (c (a + 1)) - x (c a)) u
      set D := Split.det3 (x (c (i + 1)) - x (c i)) (x (c (a + 1)) - x (c a)) v
      filter_upwards [ev_pos_cont (g := fun s => σ * ((A + s * B) * (C + s * D))) (by fun_prop)
        (by simpa using h0)] with s hs
      intro _ _ _
      rw [e, ed]; exact hs
    · exact Filter.Eventually.of_forall fun _ h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hh
  obtain ⟨s, hf, hs⟩ := (hF.and hS).exists
  exact ⟨k, hk0, c, pat, u + s • v, a, cc, σ, hk, hc, hcyc, hf, hca, hca1, fun i j h1 h2 h3 => hs i j h1 h2 h3⟩

end Perturb

/-- **`HoleChamber`**: the hole as a statement about the open chambers of the arrangement of the nine facet great
circles: at every view `u` off the facet circles, the silhouette's depths are not robustly unimodal and carry no
split rows; on the facet circles there is no face-chord view. -/
def HoleChamber (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  CbarIn x ∧ ¬ Z0.FacetCellF F ∧ ¬ Gen.AnyFaceChord F ∧ ¬ OpenCellRob F ∧ ¬ OpenCellSplit F ∧
    ¬ BoxApplies (univ.image x) ∧ ¬ Gen.EdgePlaneAny x

/-- [PROVED] `HoleLeaf → HoleChamber`. -/
theorem holeChamber_of_holeLeaf {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (h : HoleLeaf x F) :
    HoleChamber x F :=
  ⟨h.1, h.2.1, h.2.2.1, fun hr => h.2.2.2.1 (lexAny_of_openCellRob hr),
    fun hs => h.2.2.2.2.1 (splitAny_of_openCellSplit hs), h.2.2.2.2.2⟩

/-- [PROVED] `HoleChamber ↔ HoleLeaf`. -/
theorem holeChamber_iff_holeLeaf {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} :
    HoleChamber x F ↔ HoleLeaf x F :=
  ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, fun hl => h.2.2.2.1 (openCellRob_of_lexAny hl),
    fun hs => h.2.2.2.2.1 (openCellSplit_of_splitAny hs), h.2.2.2.2.2⟩, holeChamber_of_holeLeaf⟩

/-- [PROVED] **Crowned 4-rims.**  On `HoleLeaf`, at every view `u` in the CLOSED cell of a 4-rim whose open cell
is nonempty, the rim is crowned: all four diagonal forms `≥ 0` (`D_A`) or all `≤ 0` (`D_B`). -/
theorem crowned_of_holeLeaf {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (h : HoleLeaf x F)
    {c : ZMod 4 → Fin 7} (hc : Function.Injective c) {U Dn : Finset (Fin 9)}
    (hcyc : S0xCycUD s0x_S24 c U Dn) {a u : ℝ³} (ha : CellAt F U Dn a) (hu : CellLe F U Dn u) :
    (∀ p ∈ diagPairs, 0 ≤ ⟪x (c p.1) - x (c p.2), u⟫) ∨ (∀ p ∈ diagPairs, ⟪x (c p.1) - x (c p.2), u⟫ ≤ 0) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨p, hp, hpn⟩, ⟨q, hq, hqp⟩⟩ := hcon
  have hR : RobUni (fun i => ⟪x (c i), u⟫) := robUni_four_of_mixed
    ⟨p, hp, by rw [← inner_sub_left]; exact hpn⟩ ⟨q, hq, by rw [← inner_sub_left]; exact hqp⟩
  exact h.2.2.2.1 (Atlas.closedCell_lexAny le_rfl F hc hcyc ha hu hR)

/-- [PROVED] On `HoleLeaf`, no closed-cell view of a `k ≥ 4` rim with a nonempty open cell has robustly unimodal
depths (the `k`-rim analogue of "crowned"; for `k = 5` Lemma A5 then forbids any strict row at an apex edge). -/
theorem noRobUni_of_holeLeaf {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (h : HoleLeaf x F)
    {k : ℕ} [NeZero k] (hk : 4 ≤ k) {c : ZMod k → Fin 7} (hc : Function.Injective c) {U Dn : Finset (Fin 9)}
    (hcyc : S0xCycUD s0x_S24 c U Dn) {a u : ℝ³} (ha : CellAt F U Dn a) (hu : CellLe F U Dn u) :
    ¬ RobUni (fun i => ⟪x (c i), u⟫) := fun hR =>
  h.2.2.2.1 (Atlas.closedCell_lexAny hk F hc hcyc ha hu hR)


/-! ## 5. Form C: corner frame `x = c + E ∘ X` -/

/-- The linear map `w ↦ w₀ a + w₁ b + w₂ c` (columns `a`, `b`, `c`). -/
noncomputable def frameMap (a b c : ℝ³) : ℝ³ →ₗ[ℝ] ℝ³ where
  toFun w := w 0 • a + w 1 • b + w 2 • c
  map_add' w w' := by simp only [PiLp.add_apply, add_smul]; abel
  map_smul' r w := by simp only [PiLp.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, smul_add]

/-- The shape `X` is in the corner frame at vertex 1: `X₁ = 0`, `X₀ = e_a`, `X₂ = e_b`, `X₆ = e_c`. -/
def FrameNormal (X : Fin 7 → ℝ³) : Prop :=
  X 1 = !₂[0, 0, 0] ∧ X 0 = !₂[1, 0, 0] ∧ X 2 = !₂[0, 1, 0] ∧ X 6 = !₂[0, 0, 1]

/-- The corner-frame (oblique) coordinates of `x`: `(a_v, b_v, c_v) = (oblX0, oblX2, oblX6)`. -/
noncomputable def frameCoords (x : Fin 7 → ℝ³) (v : Fin 7) : ℝ³ := !₂[oblX0 x v, oblX2 x v, oblX6 x v]

/-- [OPEN] **Frame form**: for every corner-frame shape `X`, every translation `c` and every linear map `E` (the
metric is `G = Eᵀ E`), the point `c + E ∘ X` is not in the hole.  This is the engine's input format
(genleaves24: "x0..x6 in the y-frame, G"); `frameOpen24_iff` shows it is `Open24`. -/
def FrameOpen24 : Prop :=
  ∀ (X : Fin 7 → ℝ³), FrameNormal X → ∀ (c : ℝ³) (E : ℝ³ →ₗ[ℝ] ℝ³) (fs : Fin 9 → ℝ³ →ᵃ[ℝ] ℝ)
    (hh : ∀ t i, (i ∈ s0x_S24 t → fs t (c + E (X i)) = 0) ∧ (i ∉ s0x_S24 t → fs t (c + E (X i)) < 0)),
    ¬ Hole24 (fun v => c + E (X v)) (mkFac24 fs hh)

theorem hole24_congr {x y : Fin 7 → ℝ³} (e : x = y) (fs : Fin 9 → ℝ³ →ᵃ[ℝ] ℝ)
    (hh : ∀ t i, (i ∈ s0x_S24 t → fs t (x i) = 0) ∧ (i ∉ s0x_S24 t → fs t (x i) < 0))
    (h : Hole24 x (mkFac24 fs hh)) : Hole24 y (mkFac24 fs (e ▸ hh)) := by
  subst e; exact h

/-- [PROVED] Every type-24 configuration is `c + E ∘ X` with `c = x₁`, `E` = the corner edges, `X` = the
oblique coordinates, and `X` is in the corner frame. -/
theorem frame_decomp {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    FrameNormal (frameCoords x) ∧
      x = fun v => x 1 + frameMap (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) (frameCoords x v) := by
  have T := M4.type24OfFac F
  have hd := T.det_ne
  have a0 : oblX0 x 0 = 1 := by unfold oblX0; exact div_self hd
  have b2 : oblX2 x 2 = 1 := by unfold oblX2; exact div_self hd
  have c6 : oblX6 x 6 = 1 := by unfold oblX6; exact div_self hd
  have z : ∀ r : ℝ, (0 : ℝ) / r = 0 := fun r => zero_div r
  have a1 : oblX0 x 1 = 0 := by simp only [oblX0, sub_self, vol3]; simp
  have b1 : oblX2 x 1 = 0 := by simp only [oblX2, sub_self, vol3]; simp
  have c1 : oblX6 x 1 = 0 := by simp only [oblX6, sub_self, vol3]; simp
  have a2 : oblX0 x 2 = 0 := by simp only [oblX0, vol3]; ring_nf
  have a6 : oblX0 x 6 = 0 := by simp only [oblX0, vol3]; ring_nf
  have b0 : oblX2 x 0 = 0 := by simp only [oblX2, vol3]; ring_nf
  have b6 : oblX2 x 6 = 0 := by simp only [oblX2, vol3]; ring_nf
  have c0 : oblX6 x 0 = 0 := by simp only [oblX6, vol3]; ring_nf
  have c2 : oblX6 x 2 = 0 := by simp only [oblX6, vol3]; ring_nf
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [frameCoords, a1, b1, c1]
  · simp only [frameCoords, a0, b0, c0]
  · simp only [frameCoords, a2, b2, c2]
  · simp only [frameCoords, a6, b6, c6]
  · funext v
    rw [T.rep v]
    simp [frameMap, frameCoords, add_assoc]

/-- [PROVED] **`FrameOpen24 ↔ Open24`.** -/
theorem frameOpen24_iff : FrameOpen24 ↔ Open24 := by
  constructor
  · intro hF x fs hh hH
    obtain ⟨hX, e⟩ := frame_decomp (mkFac24 fs hh)
    have hh' : ∀ t i, (i ∈ s0x_S24 t →
          fs t (x 1 + frameMap (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) (frameCoords x i)) = 0) ∧
        (i ∉ s0x_S24 t →
          fs t (x 1 + frameMap (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) (frameCoords x i)) < 0) := by
      intro t i
      have ei : x i = x 1 + frameMap (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) (frameCoords x i) := congrFun e i
      rw [← ei]; exact hh t i
    exact hF (frameCoords x) hX (x 1) _ fs hh' (hole24_congr e fs hh hH)
  · intro hO X _ c E fs hh
    exact hO (fun v => c + E (X v)) fs hh

/-- [PROVED] **Depths are metric-free in `ζ = Eᵀ u`**: `z_v - z_w = ⟪X_v - X_w, ζ⟫`. -/
theorem frame_depth (X : Fin 7 → ℝ³) (c : ℝ³) (E : ℝ³ →ₗ[ℝ] ℝ³) (u : ℝ³) (v w : Fin 7) :
    ⟪c + E (X v), u⟫ - ⟪c + E (X w), u⟫ = ⟪X v - X w, LinearMap.adjoint E u⟫ := by
  rw [← inner_sub_left, add_sub_add_left_eq_sub, ← map_sub, LinearMap.adjoint_inner_right]

/-- [PROVED] **Facet signs are metric-free in `w = E⁻¹ u`**: `⟪N_t, E w⟫ = g_t(w) - g_t(0)` with
`g_t = f_t ∘ (c + E ·)` the facet functional pulled back to the shape frame (it vanishes on `X_i`, `i ∈ S_t`). -/
theorem frame_facet {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : Fin 9) (c : ℝ³) (E : ℝ³ →ₗ[ℝ] ℝ³)
    (w : ℝ³) : ⟪F.N t, E w⟫ = F.f t (c + E w) - F.f t c := by
  rw [F.hN]; simp

/-- [PROVED] The metric: `⟪E a, E b⟫ = ⟪a, (Eᵀ E) b⟫`. -/
theorem frame_gram (E : ℝ³ →ₗ[ℝ] ℝ³) (a b : ℝ³) :
    ⟪E a, E b⟫ = ⟪a, (LinearMap.adjoint E ∘ₗ E) b⟫ := by
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right]

/-- [PROVED] The hidden-cap cone `C` (facets 012, 016, 126 back; vertex 1 hidden) is `E` of the open positive
octant: `capView x ca cb cc = E (ca, cb, cc)`. -/
theorem capView_eq_frame (x : Fin 7 → ℝ³) (ca cb cc : ℝ) :
    HC.capView x ca cb cc = frameMap (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) !₂[ca, cb, cc] := by
  simp [HC.capView, frameMap]

/-! ## 6. Form D: quantitative splits (hypotheses for different proof styles) -/

/-- The three corner Gram entries at vertex 1 (`G_ab, G_ac, G_bc`). -/
noncomputable def gab (x : Fin 7 → ℝ³) : ℝ := ⟪x 0 - x 1, x 2 - x 1⟫
noncomputable def gac (x : Fin 7 → ℝ³) : ℝ := ⟪x 0 - x 1, x 6 - x 1⟫
noncomputable def gbc (x : Fin 7 → ℝ³) : ℝ := ⟪x 2 - x 1, x 6 - x 1⟫

/-- The cube-corner stratum: all three face angles at vertex 1 are right angles (`G` diagonal; the corner of M7). -/
def CubeCorner (x : Fin 7 → ℝ³) : Prop := gab x = 0 ∧ gac x = 0 ∧ gbc x = 0

/-- Deep obtuse corner: all three corner cosines `≤ -δ`. -/
def DeepObtuse (δ : ℝ) (x : Fin 7 → ℝ³) : Prop :=
  gab x ≤ -δ * (‖x 0 - x 1‖ * ‖x 2 - x 1‖) ∧ gac x ≤ -δ * (‖x 0 - x 1‖ * ‖x 6 - x 1‖) ∧
    gbc x ≤ -δ * (‖x 2 - x 1‖ * ‖x 6 - x 1‖)

/-- Near-right corner: `OB1`, and some corner cosine in `(-δ, 0]`. -/
def NearRight (δ : ℝ) (x : Fin 7 → ℝ³) : Prop := H24K.SAT.OB1 x ∧ ¬ DeepObtuse δ x

/-- [PROVED] For `δ ≥ 0`, a deep-obtuse corner is `OB1`. -/
theorem ob1_of_deepObtuse {δ : ℝ} (hδ : 0 ≤ δ) {x : Fin 7 → ℝ³} (h : DeepObtuse δ x) : H24K.SAT.OB1 x := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [gab, gac, gbc] at h1 h2 h3
  have p1 := mul_nonneg hδ (mul_nonneg (norm_nonneg (x 0 - x 1)) (norm_nonneg (x 2 - x 1)))
  have p2 := mul_nonneg hδ (mul_nonneg (norm_nonneg (x 0 - x 1)) (norm_nonneg (x 6 - x 1)))
  have p3 := mul_nonneg hδ (mul_nonneg (norm_nonneg (x 2 - x 1)) (norm_nonneg (x 6 - x 1)))
  exact ⟨by linarith, by linarith, by linarith⟩

/-- [OPEN] deep-obtuse piece. -/
def OpenDeep (δ : ℝ) : Prop := ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), DeepObtuse δ x → ¬ HoleFull x F

/-- [OPEN] near-right piece (contains the hardest known points: `G` nearly diagonal, cond 2.6-16). -/
def OpenNearRight (δ : ℝ) : Prop := ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), NearRight δ x → ¬ HoleFull x F

/-- [OPEN] the cube-corner stratum alone (codimension 3; a natural first exercise, M7's corner with a planar
quad). -/
def OpenCube : Prop := ∀ (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x), CubeCorner x → ¬ HoleFull x F

/-- [PROVED] The split assembles: for any `δ`, deep + near-right + special give `Open24`. -/
theorem open24_of_quant (δ : ℝ) (h1 : OpenDeep δ) (h2 : OpenNearRight δ) (h3 : OpenSpecial) : Open24 := by
  refine open24_of_split (fun x F hO hF => ?_) h3
  by_cases hD : DeepObtuse δ x
  · exact h1 x F hD hF
  · exact h2 x F ⟨hO, hD⟩ hF

/-- [PROVED] The cube corner is near-right for every `δ > 0` (so `OpenNearRight δ → OpenCube`). -/
theorem openCube_of_nearRight {δ : ℝ} (hδ : 0 < δ) (h : OpenNearRight δ) : OpenCube := by
  intro x F hc hF
  have hO : H24K.SAT.OB1 x := ⟨hc.1.le, hc.2.1.le, hc.2.2.le⟩
  refine h x F ⟨hO, fun hD => ?_⟩ hF
  have hpos : 0 < ‖x 0 - x 1‖ * ‖x 2 - x 1‖ := by
    have T := M4.type24OfFac F
    have hx := Minimality.H24.SAT.inj_of_fac F
    refine mul_pos (norm_pos_iff.2 (sub_ne_zero.2 fun e => ?_)) (norm_pos_iff.2 (sub_ne_zero.2 fun e => ?_))
    · exact absurd (hx e) (by decide)
    · exact absurd (hx e) (by decide)
  have := hD.1
  rw [hc.1] at this
  nlinarith

/-- [PROVED] **Fatness on the hole** (box lemma, `ThinCases.boxApplies_of_thin_fin`): a hole point is not within a
slab of width `w < thinAlpha 7 · ‖x_i - x_j‖`.  A compactness input. -/
theorem holeLeaf_fat {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} (h : HoleLeaf x F)
    (hsol : (interior (convexHull ℝ ((univ.image x : Finset ℝ³) : Set ℝ³))).Nonempty)
    (n : ℝ³) (hnn : ⟪n, n⟫ = 1) (w : ℝ) (hpair : ∀ i j, |⟪n, x i - x j⟫| ≤ w) (i j : Fin 7) :
    thinAlpha 7 * ‖x i - x j‖ ≤ w :=
  le_of_not_gt fun hlt => h.2.2.2.2.2.1 (boxApplies_of_thin_fin x hsol n hnn w hpair i j hlt)

end Minimality.T24.Stmt
