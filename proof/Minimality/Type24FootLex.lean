module

public import Minimality.Type24WallFoot126
public import Minimality.TieMerge
public import Minimality.RobustUnimodal

/-!
# Type 24: FOOT (the level chord in Lex / cell form) and RAY-R (lex cells at edge views)

Fable's schemas FOOT and RAY-R (nopert229 notes/FABLE-COVER-REPLY.md Idea 3, COVTEST in
tools/genleaves/FACENORM24.md), in `HoleLeaf`-excluded form (conclusion `Gen.LexAny`).

* **FOOT, generic** (`exists_cellAt_cu_of_tie`, any facet family, any rim length `m + 1 ≥ 3`): a view `w0` on a
  closed face of a cell (every facet strict at `w0`, or vanishing at `w0` and along the wall direction `d` with
  the sign of the tilt `v`), an adjacent rim tie `z (r i) = z (r (i + 1))` at `w0` that `d` breaks
  (`⟪x (r (i+1)) - x (r i), d⟫ ≠ 0`), and the merged cycle `skipAt z i` strictly unimodal.  Then the views
  `w0 + s • (±d) + s² • v` (small `s > 0`, the sign continuing the step through the chord) are in the open cell and
  have strictly unimodal rim depths.  This is Lemma LC / TA (`isRupert_levelChord`, `isCyclicUnimodal_of_tieMerge`)
  in cell form: `lexAny_of_tie` (`m ≥ 3`), `cellCert_of_tie` (a `CellCert` of the cell built from the data).
* Region form `LevelChordAt x F w0 d v` (some rim / up-set / tie position with the hypotheses above), `lexAny_of_levelChordAt`,
  and the three wall feet: `FootW0` (wall `016`, `w60 = capView x 1 0 r60`, `d = x 6 - x 1`, tilt `±(x 2 - x 1)`),
  `FootW2` (wall `126`, `w26 = capView x 0 1 r26`, `d = x 6 - x 1`, tilt `±(x 0 - x 1)`), and the wall `012` as
  `FootW0` of the twin `x ∘ π_24`.  Leaves `lexAny_of_footW0(_twin)`, `lexAny_of_footW2(_twin)`, hole facts
  `holeLeaf_not_footW0(_twin)`, `holeLeaf_not_footW2(_twin)`.  No metric, `CbarIn` or `OB1` hypothesis.
* **RAY-R**: `RayRLex x F u v` = a lex cell at the edge view `x v - x u` (facet signs and `RobUniLex` in the
  lexicographic order of `(x v - x u, d1, d2)`, any `d1, d2`, any rim and cell), `lexAny_of_rayRLex(_twin)`,
  `holeLeaf_not_rayRLex(_twin)`; the closed-cell form `rayRLex_of_closedFace` (facets strict or vanishing at the
  ray with the sign of one direction `v`, rim depths `RobUni` strictly at the ray itself).

Relation to the earlier wall lemmas (Type24WallFoot126): WF2 (`WF2At`) and WF0 (`WF0At`) are FOOT in the cells
`0.4.6.2.5` / `0.5.2.3.6` with a sufficient condition for the merged 4-cycle to be no crown, so `FootW2` / `FootW0`
contain them wherever the rim depths at the foot are distinct apart from the chord (ties among the other corners
are allowed by WF0 / WF2, not by FOOT).  CW2 and the WallFoot cell lemmas (`∃ cc` on the wall line, 4-rims) are
not feet: FOOT at a foot in `0.5.2.6` is the case `cc = r26 ∓ ε` of CW2, and conversely CW2 also holds away
from the foot (neither contains the other).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace Topology
open Finset Filter
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.RimCell Minimality.T24.HC

namespace Minimality.T24.FootLex

/-! ## Lexicographic signs along `w0 + s d + s² v` -/

/-- A lexicographically positive triple is the sign of `A + s B + s² C` for small `s > 0`. -/
theorem ev_lexPos3 {A B C : ℝ} (h : LexCell.LexPos3 A B C) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < A + s * B + s * s * C := by
  rcases h with hA | ⟨rfl, hB | ⟨rfl, hC⟩⟩
  · have hc : Continuous fun s : ℝ => A + s * B + s * s * C := by fun_prop
    exact (hc.continuousAt.eventually (lt_mem_nhds (by simpa using hA))).filter_mono nhdsWithin_le_nhds
  · have hc : Continuous fun s : ℝ => B + s * C := by fun_prop
    have h1 : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < B + s * C :=
      (hc.continuousAt.eventually (lt_mem_nhds (by simpa using hB))).filter_mono nhdsWithin_le_nhds
    filter_upwards [h1, self_mem_nhdsWithin] with s h1 (h2 : 0 < s)
    have := mul_pos h2 h1
    linarith [show (0 : ℝ) + s * B + s * s * C = s * (B + s * C) by ring]
  · filter_upwards [self_mem_nhdsWithin] with s (h2 : 0 < s)
    have := mul_pos (mul_pos h2 h2) hC
    linarith [show (0 : ℝ) + s * 0 + s * s * C = s * s * C by ring]

theorem inner_curve (p w0 D v : ℝ³) (s : ℝ) :
    ⟪p, w0 + s • D + (s * s) • v⟫ = ⟪p, w0⟫ + s * ⟪p, D⟫ + s * s * ⟪p, v⟫ := by
  rw [inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right]

section Generic

variable {n nf : ℕ} {S : Fin nf → Finset (Fin n)} {y : Fin n → ℝ³}

/-- In a cycle whose merged cycle `skipAt z i` is injective, a tie `z p = z q` (`p ≠ q`) is the tie of the pair
`i, i + 1`. -/
theorem tie_pair_of_merged {m : ℕ} [NeZero m] {z : ZMod (m + 1) → ℝ} {i : ZMod (m + 1)}
    (hinj : Function.Injective (skipAt z i)) (htie : z i = z (i + 1)) {p q : ZMod (m + 1)} (hpq : p ≠ q)
    (he : z p = z q) : (p = i ∧ q = i + 1) ∨ (p = i + 1 ∧ q = i) := by
  have hsk : ∀ j, skipAt z i j = z (phi i j) := fun j => rfl
  have h0 : skipAt z i 0 = z (i + 1) := by rw [hsk, phi_zero]
  by_cases hp : p = i
  · subst hp
    obtain ⟨jq, hjq⟩ := phi_surj p q (Ne.symm hpq)
    have : skipAt z p jq = skipAt z p 0 := by rw [hsk, hjq, h0, ← he, htie]
    have hj := hinj this
    left; refine ⟨rfl, ?_⟩; rw [← hjq, hj, phi_zero]
  · by_cases hq : q = i
    · subst hq
      obtain ⟨jp, hjp⟩ := phi_surj q p hp
      have : skipAt z q jp = skipAt z q 0 := by rw [hsk, hjp, h0, he, htie]
      have hj := hinj this
      right; refine ⟨?_, rfl⟩; rw [← hjp, hj, phi_zero]
    · obtain ⟨jp, hjp⟩ := phi_surj i p hp
      obtain ⟨jq, hjq⟩ := phi_surj i q hq
      have : skipAt z i jp = skipAt z i jq := by rw [hsk, hsk, hjp, hjq, he]
      exact absurd (by rw [← hjp, ← hjq, hinj this]) hpq

/-- **FOOT / Lemma LC in cell form (generic).**  Facets strict at `w0`, or vanishing at `w0` and along `d` with
the sign of the tilt `v`; an adjacent rim tie at `w0` broken by `d`; the merged cycle strictly unimodal.  Then some
view of the open cell has strictly unimodal rim depths. -/
theorem exists_cellAt_cu_of_tie {m : ℕ} [NeZero m] (hm : 2 ≤ m) (F : S0xFac nf S y)
    {r : ZMod (m + 1) → Fin n} {U Dn : Finset (Fin nf)} {w0 d v : ℝ³} (i : ZMod (m + 1))
    (hU : ∀ t ∈ U, 0 < ⟪F.N t, w0⟫ ∨ (⟪F.N t, w0⟫ = 0 ∧ ⟪F.N t, d⟫ = 0 ∧ 0 < ⟪F.N t, v⟫))
    (hD : ∀ t ∈ Dn, ⟪F.N t, w0⟫ < 0 ∨ (⟪F.N t, w0⟫ = 0 ∧ ⟪F.N t, d⟫ = 0 ∧ ⟪F.N t, v⟫ < 0))
    (htie : ⟪y (r i), w0⟫ = ⟪y (r (i + 1)), w0⟫)
    (hd : ⟪y (r (i + 1)) - y (r i), d⟫ ≠ 0)
    (hmerge : IsCyclicUnimodal (skipAt (fun j => ⟪y (r j), w0⟫) i)) :
    ∃ w, CellAt F U Dn w ∧ IsCyclicUnimodal (fun j => ⟪y (r j), w⟫) := by
  set z0 : ZMod (m + 1) → ℝ := fun j => ⟪y (r j), w0⟫ with hz0
  set Δ : ℝ³ := y (r (i + 1)) - y (r i) with hΔ
  have hne : z0 (i - 1) ≠ z0 i := by
    have := skipAt_ne_ends hm (z := z0) hmerge.1
    rw [show z0 i = z0 (i + 1) from htie]; exact this.symm
  -- the direction along the wall continuing the step through the chord
  obtain ⟨D, hDd, hDs⟩ : ∃ D : ℝ³, (∀ N : ℝ³, ⟪N, d⟫ = 0 → ⟪N, D⟫ = 0) ∧
      ((z0 (i - 1) < z0 i ∧ 0 < ⟪Δ, D⟫) ∨ (z0 i < z0 (i - 1) ∧ ⟪Δ, D⟫ < 0)) := by
    have hneg : ∀ N : ℝ³, ⟪N, d⟫ = 0 → ⟪N, -d⟫ = 0 := fun N h => by rw [inner_neg_right, h, neg_zero]
    rcases lt_or_gt_of_ne hne with h1 | h1 <;> rcases lt_or_gt_of_ne hd with h2 | h2
    · exact ⟨-d, hneg, Or.inl ⟨h1, by rw [inner_neg_right]; linarith⟩⟩
    · exact ⟨d, fun N h => h, Or.inl ⟨h1, h2⟩⟩
    · exact ⟨d, fun N h => h, Or.inr ⟨h1, h2⟩⟩
    · exact ⟨-d, hneg, Or.inr ⟨h1, by rw [inner_neg_right]; linarith⟩⟩
  set w : ℝ → ℝ³ := fun s => w0 + s • D + (s * s) • v with hw
  have e : ∀ (p : ℝ³) (s : ℝ), ⟪p, w s⟫ = ⟪p, w0⟫ + s * ⟪p, D⟫ + s * s * ⟪p, v⟫ :=
    fun p s => inner_curve p w0 D v s
  -- the open cell
  have evC : ∀ᶠ s : ℝ in 𝓝[>] 0, CellAt F U Dn (w s) := by
    refine (Filter.eventually_all_finset U |>.2 fun t ht => ?_).and
      (Filter.eventually_all_finset Dn |>.2 fun t ht => ?_)
    · have hl : LexCell.LexPos3 ⟪F.N t, w0⟫ ⟪F.N t, D⟫ ⟪F.N t, v⟫ := by
        rcases hU t ht with h | ⟨h0, h1, h2⟩
        · exact Or.inl h
        · exact Or.inr ⟨h0, Or.inr ⟨hDd _ h1, h2⟩⟩
      exact (ev_lexPos3 hl).mono fun s hs => by rw [e]; exact hs
    · have hl : LexCell.LexPos3 (-⟪F.N t, w0⟫) (-⟪F.N t, D⟫) (-⟪F.N t, v⟫) := by
        rcases hD t ht with h | ⟨h0, h1, h2⟩
        · exact Or.inl (neg_pos.2 h)
        · exact Or.inr ⟨by rw [h0, neg_zero], Or.inr ⟨by rw [hDd _ h1, neg_zero], neg_pos.2 h2⟩⟩
      exact (ev_lexPos3 hl).mono fun s hs => by rw [e]; linarith
  -- strict comparisons persist
  have evO : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ p q : ZMod (m + 1), z0 p < z0 q →
      ⟪y (r p), w s⟫ < ⟪y (r q), w s⟫ := by
    refine eventually_all.2 fun p => eventually_all.2 fun q => ?_
    by_cases h : z0 p < z0 q
    · have hl : LexCell.LexPos3 (⟪y (r q) - y (r p), w0⟫) (⟪y (r q) - y (r p), D⟫) (⟪y (r q) - y (r p), v⟫) :=
        Or.inl (by rw [inner_sub_left]; exact sub_pos.2 h)
      exact (ev_lexPos3 hl).mono fun s hs _ => by
        rw [← e, inner_sub_left] at hs; linarith
    · exact Eventually.of_forall fun _ h' => absurd h' h
  -- the tie is broken in the step direction
  have hΔ0 : ⟪Δ, w0⟫ = 0 := by rw [hΔ, inner_sub_left, ← htie, sub_self]
  have evT : ∀ᶠ s : ℝ in 𝓝[>] 0,
      (z0 (i - 1) < z0 i ∧ 0 < ⟪Δ, w s⟫) ∨ (z0 i < z0 (i - 1) ∧ ⟪Δ, w s⟫ < 0) := by
    rcases hDs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact (ev_lexPos3 (A := ⟪Δ, w0⟫) (C := ⟪Δ, v⟫) (Or.inr ⟨hΔ0, Or.inl h2⟩)).mono fun s hs =>
        Or.inl ⟨h1, by rw [e]; exact hs⟩
    · exact (ev_lexPos3 (A := -⟪Δ, w0⟫) (B := -⟪Δ, D⟫) (C := -⟪Δ, v⟫)
        (Or.inr ⟨by rw [hΔ0, neg_zero], Or.inl (neg_pos.2 h2)⟩)).mono fun s hs =>
        Or.inr ⟨h1, by rw [e]; linarith⟩
  obtain ⟨s, hC, hO, hT⟩ := (evC.and (evO.and evT)).exists
  refine ⟨w s, hC, ?_⟩
  set z' : ZMod (m + 1) → ℝ := fun j => ⟪y (r j), w s⟫ with hz'
  have hT' : (z0 (i - 1) < z0 i ∧ z' i < z' (i + 1)) ∨ (z0 i < z0 (i - 1) ∧ z' (i + 1) < z' i) := by
    have eΔ : ⟪Δ, w s⟫ = z' (i + 1) - z' i := by rw [hΔ, inner_sub_left]
    rcases hT with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, by linarith⟩
    · exact Or.inr ⟨h1, by linarith⟩
  have hinj : Function.Injective z' := by
    intro p q hpq
    by_contra hne'
    rcases lt_trichotomy (z0 p) (z0 q) with h | h | h
    · exact absurd hpq (hO p q h).ne
    · have hpair := tie_pair_of_merged hmerge.1 htie hne' h
      rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hT' with ⟨_, h2⟩ | ⟨_, h2⟩
      · exact absurd hpq h2.ne
      · exact absurd hpq h2.ne'
      · exact absurd hpq h2.ne'
      · exact absurd hpq h2.ne
    · exact absurd hpq (hO q p h).ne'
  exact isCyclicUnimodal_of_tieMerge hm hmerge hinj hO hT'

/-- **FOOT, Lex form (generic, rim length `m + 1 ≥ 4`).** -/
theorem lexAny_of_tie {m : ℕ} [NeZero m] (hm : 3 ≤ m) (F : S0xFac nf S y)
    {r : ZMod (m + 1) → Fin n} (hr : Function.Injective r) {U Dn : Finset (Fin nf)}
    (hcyc : S0xCycUD S r U Dn) {w0 d v : ℝ³} (i : ZMod (m + 1))
    (hU : ∀ t ∈ U, 0 < ⟪F.N t, w0⟫ ∨ (⟪F.N t, w0⟫ = 0 ∧ ⟪F.N t, d⟫ = 0 ∧ 0 < ⟪F.N t, v⟫))
    (hD : ∀ t ∈ Dn, ⟪F.N t, w0⟫ < 0 ∨ (⟪F.N t, w0⟫ = 0 ∧ ⟪F.N t, d⟫ = 0 ∧ ⟪F.N t, v⟫ < 0))
    (htie : ⟪y (r i), w0⟫ = ⟪y (r (i + 1)), w0⟫)
    (hd : ⟪y (r (i + 1)) - y (r i), d⟫ ≠ 0)
    (hmerge : IsCyclicUnimodal (skipAt (fun j => ⟪y (r j), w0⟫) i)) : Gen.LexAny F := by
  obtain ⟨w, hC, hcu⟩ := exists_cellAt_cu_of_tie (by omega) F i hU hD htie hd hmerge
  exact lexAny_of_cellAt_robUni (by omega) F hr hcyc hC
    (s0x_robUni_of_isRobustUnimodal hcu.isRobustUnimodal)

end Generic

/-! ## Type 24 -/

variable {x : Fin 7 → ℝ³}

/-- **FOOT, cell certificate**: the level-chord hypotheses on a rim `r` of length `m + 1 ≥ 4` with up-set `U`
give a `CellCert` of the cell built from `(r, U)`. -/
theorem cellCert_of_tie {m : ℕ} [NeZero m] (hm : 3 ≤ m) (F : S0xFac 9 s0x_S24 x)
    {r : ZMod (m + 1) → Fin 7} (hr : Function.Injective r) {U : Finset (Fin 9)}
    (hcyc : S0xCycUD s0x_S24 r U (univ \ U)) {w0 d v : ℝ³} (i : ZMod (m + 1))
    (hU : ∀ t ∈ U, 0 < ⟪F.N t, w0⟫ ∨ (⟪F.N t, w0⟫ = 0 ∧ ⟪F.N t, d⟫ = 0 ∧ 0 < ⟪F.N t, v⟫))
    (hD : ∀ t ∈ univ \ U, ⟪F.N t, w0⟫ < 0 ∨ (⟪F.N t, w0⟫ = 0 ∧ ⟪F.N t, d⟫ = 0 ∧ ⟪F.N t, v⟫ < 0))
    (htie : ⟪x (r i), w0⟫ = ⟪x (r (i + 1)), w0⟫)
    (hd : ⟪x (r (i + 1)) - x (r i), d⟫ ≠ 0)
    (hmerge : IsCyclicUnimodal (skipAt (fun j => ⟪x (r j), w0⟫) i)) :
    ∃ w, Cell.CellCert F ⟨m + 1, by omega, r, U, hr, hcyc⟩ w := by
  obtain ⟨w, hC, hcu⟩ := exists_cellAt_cu_of_tie (by omega) F i hU hD htie hd hmerge
  exact ⟨w, hC, Or.inl (s0x_robUni_of_isRobustUnimodal hcu.isRobustUnimodal)⟩

/-- **FOOT region form at a view `w0`** (wall direction `d`, tilt `v`): some rim `r` of length `m + 1 ≥ 4` with
up-set `U` (a silhouette, `S0xCycUD`) and position `i` such that the facets are strict at `w0` or vanish at `w0`
and along `d` with the sign of `v`, the chord `r i → r (i + 1)` is level at `w0` and broken by `d`, and the merged
cycle is strictly unimodal. -/
def LevelChordAt (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) (w0 d v : ℝ³) : Prop :=
  ∃ (m : ℕ) (_ : NeZero m) (r : ZMod (m + 1) → Fin 7) (U : Finset (Fin 9)) (i : ZMod (m + 1)),
    3 ≤ m ∧ Function.Injective r ∧ S0xCycUD s0x_S24 r U (univ \ U) ∧
    (∀ t ∈ U, 0 < ⟪F.N t, w0⟫ ∨ (⟪F.N t, w0⟫ = 0 ∧ ⟪F.N t, d⟫ = 0 ∧ 0 < ⟪F.N t, v⟫)) ∧
    (∀ t ∈ univ \ U, ⟪F.N t, w0⟫ < 0 ∨ (⟪F.N t, w0⟫ = 0 ∧ ⟪F.N t, d⟫ = 0 ∧ ⟪F.N t, v⟫ < 0)) ∧
    ⟪x (r i), w0⟫ = ⟪x (r (i + 1)), w0⟫ ∧ ⟪x (r (i + 1)) - x (r i), d⟫ ≠ 0 ∧
    IsCyclicUnimodal (skipAt (fun j => ⟪x (r j), w0⟫) i)

theorem lexAny_of_levelChordAt {F : S0xFac 9 s0x_S24 x} {w0 d v : ℝ³} (h : LevelChordAt x F w0 d v) :
    Gen.LexAny F := by
  obtain ⟨m, _, r, U, i, hm, hr, hcyc, hU, hD, htie, hd, hmerge⟩ := h
  exact lexAny_of_tie hm F hr hcyc i hU hD htie hd hmerge

/-- **FOOT at the foot of wall `016`** (`w60 = capView x 1 0 r60`, the tie `z0 = z6`; wall direction
`x 6 - x 1`, tilt `±(x 2 - x 1)`). -/
def FootW0 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  LevelChordAt x F (capView x 1 0 (WallFoot.r60 x)) (x 6 - x 1) (x 2 - x 1) ∨
    LevelChordAt x F (capView x 1 0 (WallFoot.r60 x)) (x 6 - x 1) (-(x 2 - x 1))

/-- **FOOT at the foot of wall `126`** (`w26 = capView x 0 1 r26`, the tie `z2 = z6`; wall direction
`x 6 - x 1`, tilt `±(x 0 - x 1)`). -/
def FootW2 (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) : Prop :=
  LevelChordAt x F (capView x 0 1 (WallFoot126.r26 x)) (x 6 - x 1) (x 0 - x 1) ∨
    LevelChordAt x F (capView x 0 1 (WallFoot126.r26 x)) (x 6 - x 1) (-(x 0 - x 1))

theorem lexAny_of_footW0 {F : S0xFac 9 s0x_S24 x} (h : FootW0 x F) : Gen.LexAny F :=
  h.elim lexAny_of_levelChordAt lexAny_of_levelChordAt

theorem lexAny_of_footW2 {F : S0xFac 9 s0x_S24 x} (h : FootW2 x F) : Gen.LexAny F :=
  h.elim lexAny_of_levelChordAt lexAny_of_levelChordAt

/-- FOOT at the foot of wall `012` = `FootW0` of the twin `x ∘ π_24`. -/
theorem lexAny_of_footW0_twin {F : S0xFac 9 s0x_S24 x} (h : FootW0 (x ∘ Sym.pi24) (Sym.sym24 F)) :
    Gen.LexAny F :=
  Sym.lexAny_sym F (lexAny_of_footW0 h)

theorem lexAny_of_footW2_twin {F : S0xFac 9 s0x_S24 x} (h : FootW2 (x ∘ Sym.pi24) (Sym.sym24 F)) :
    Gen.LexAny F :=
  Sym.lexAny_sym F (lexAny_of_footW2 h)

theorem holeLeaf_not_levelChordAt {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) (w0 d v : ℝ³) :
    ¬ LevelChordAt x F w0 d v :=
  fun h => hF.2.2.2.1 (lexAny_of_levelChordAt h)

theorem holeLeaf_not_levelChordAt_twin {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) (w0 d v : ℝ³) :
    ¬ LevelChordAt (x ∘ Sym.pi24) (Sym.sym24 F) w0 d v :=
  fun h => hF.2.2.2.1 (Sym.lexAny_sym F (lexAny_of_levelChordAt h))

theorem holeLeaf_not_footW0 {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : ¬ FootW0 x F :=
  fun h => hF.2.2.2.1 (lexAny_of_footW0 h)

theorem holeLeaf_not_footW0_twin {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) :
    ¬ FootW0 (x ∘ Sym.pi24) (Sym.sym24 F) :=
  fun h => hF.2.2.2.1 (lexAny_of_footW0_twin h)

theorem holeLeaf_not_footW2 {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) : ¬ FootW2 x F :=
  fun h => hF.2.2.2.1 (lexAny_of_footW2 h)

theorem holeLeaf_not_footW2_twin {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) :
    ¬ FootW2 (x ∘ Sym.pi24) (Sym.sym24 F) :=
  fun h => hF.2.2.2.1 (lexAny_of_footW2_twin h)

/-! ## RAY-R: lex cells at edge views -/

/-- **RAY-R region form at the edge view `x v - x u`**: a rim `r` (length `k ≥ 4`, a silhouette of the up-set `U`)
whose facet signs and rim depths are lexicographically strict / robustly unimodal in the order of
`(x v - x u, d1, d2)` for some `d1, d2`.  (At an edge view the two facets of the edge vanish; `d1` pushes them to
their side of the cell, `d2` breaks the remaining ties.) -/
def RayRLex (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) (u v : Fin 7) : Prop :=
  ∃ (k : ℕ) (_ : NeZero k) (r : ZMod k → Fin 7) (U : Finset (Fin 9)) (d1 d2 : ℝ³),
    4 ≤ k ∧ Function.Injective r ∧ S0xCycUD s0x_S24 r U (univ \ U) ∧
    (∀ t ∈ U, LexCell.LexPos3 ⟪F.N t, x v - x u⟫ ⟪F.N t, d1⟫ ⟪F.N t, d2⟫) ∧
    (∀ t ∈ univ \ U, LexCell.LexPos3 (-⟪F.N t, x v - x u⟫) (-⟪F.N t, d1⟫) (-⟪F.N t, d2⟫)) ∧
    LexCell.RobUniLex (fun i => (⟪x (r i), x v - x u⟫, ⟪x (r i), d1⟫, ⟪x (r i), d2⟫))

theorem lexAny_of_rayRLex {F : S0xFac 9 s0x_S24 x} {u v : Fin 7} (h : RayRLex x F u v) : Gen.LexAny F := by
  obtain ⟨k, hk0, r, U, d1, d2, hk, hr, hcyc, hU, hD, hR⟩ := h
  exact ⟨k, hk0, r, U, univ \ U, x v - x u, d1, d2, hk, hr, hcyc, hU, hD, hR⟩

theorem lexAny_of_rayRLex_twin {F : S0xFac 9 s0x_S24 x} {u v : Fin 7}
    (h : RayRLex (x ∘ Sym.pi24) (Sym.sym24 F) u v) : Gen.LexAny F :=
  Sym.lexAny_sym F (lexAny_of_rayRLex h)

theorem holeLeaf_not_rayRLex {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) (u v : Fin 7) :
    ¬ RayRLex x F u v :=
  fun h => hF.2.2.2.1 (lexAny_of_rayRLex h)

theorem holeLeaf_not_rayRLex_twin {F : S0xFac 9 s0x_S24 x} (hF : HoleLeaf x F) (u v : Fin 7) :
    ¬ RayRLex (x ∘ Sym.pi24) (Sym.sym24 F) u v :=
  fun h => hF.2.2.2.1 (lexAny_of_rayRLex_twin h)

/-- **RAY-R, closed-cell form**: facets strict at the ray or vanishing there with the sign of one direction `dl`,
and the rim depths robustly unimodal strictly at the ray itself, give `RayRLex`. -/
theorem rayRLex_of_closedFace {F : S0xFac 9 s0x_S24 x} {u v : Fin 7} {k : ℕ} [NeZero k] (hk : 4 ≤ k)
    {r : ZMod k → Fin 7} (hr : Function.Injective r) {U : Finset (Fin 9)}
    (hcyc : S0xCycUD s0x_S24 r U (univ \ U)) {dl : ℝ³}
    (hU : ∀ t ∈ U, 0 < ⟪F.N t, x v - x u⟫ ∨ (⟪F.N t, x v - x u⟫ = 0 ∧ 0 < ⟪F.N t, dl⟫))
    (hD : ∀ t ∈ univ \ U, ⟪F.N t, x v - x u⟫ < 0 ∨ (⟪F.N t, x v - x u⟫ = 0 ∧ ⟪F.N t, dl⟫ < 0))
    (hR : RobUni (fun i => ⟪x (r i), x v - x u⟫)) : RayRLex x F u v := by
  refine ⟨k, inferInstance, r, U, dl, 0, hk, hr, hcyc, fun t ht => ?_, fun t ht => ?_, ?_⟩
  · rcases hU t ht with h | ⟨h0, h1⟩
    · exact Or.inl h
    · exact Or.inr ⟨h0, Or.inl h1⟩
  · rcases hD t ht with h | ⟨h0, h1⟩
    · exact Or.inl (neg_pos.2 h)
    · exact Or.inr ⟨by rw [h0, neg_zero], Or.inl (neg_pos.2 h1)⟩
  · intro B b c d hb hbc hcd hdk
    have h := hR B b c d hb hbc hcd hdk
    simp only [LexCell.LexLt3, LexCell.LexPos3]
    by_contra hn
    simp only [not_or] at hn
    exact h ⟨not_lt.mp (fun h' => hn.1.1 (sub_pos.2 h')), not_lt.mp (fun h' => hn.2.1.1 (sub_pos.2 h')),
      not_lt.mp (fun h' => hn.2.2.1.1 (sub_pos.2 h')), not_lt.mp (fun h' => hn.2.2.2.1 (sub_pos.2 h'))⟩

end Minimality.T24.FootLex
