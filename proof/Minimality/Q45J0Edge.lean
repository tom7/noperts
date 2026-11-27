module

public import Minimality.Q45
public import Minimality.FaceChordEdge
public import Minimality.FaceChordDS

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped RealInnerProductSpace Topology
open Filter Finset
open Minimality Minimality.H21 Minimality.FaceChord Minimality.T24.SAT Minimality.T24.RimFromSigns

/-!
# The J0 face chords with a far EDGE (job OSPEC3, nopert229 notes/OPENSPECIAL-STRATEGY.md)

The four codim-1 face-chord leaves of the Q45 dispatcher (`q45_Kplus_s_le_one` .. `q45_Kminus_t_gt_one`, Q45J0.lean:
view on the face circle of 0345, rim 6 4 5 2, chord 4 → 5, middles 0, 3) use their far-vertex hypotheses `hS3`
(`f3(x2) ≠ f3(x6)`) and `hS4` (foot of the farther vertex off the chord) only for Lemma H.  Here:

* `J0Chord F u ρ`: the rest of the face-chord data at `u` (everything except the far vertex);
* `q45_*_j0w` (OSPEC4): the four cores with only the ADJACENT rim pairs off the S2 locus (`hS2a`; opposite corners
  may tie, `unimodal_quad_Kplus_adj`, `strictUnimodal_four_of_adj`), concluding `⟪N3, u⟫ = 0`, `J0Extra`, `u = B + ε D`
  and the lex order at `(B, D)` read at `u`, and, under the full `hS2`, `J0Chord`; `s2_opp_of` (an S2 pair off the adjacent ones is `4 2` or `6 5`);
* `q45_*_j0`: the four leaves without `hS3`, `hS4`, concluding `J0Chord` and `J0Extra` (OSPEC4: the facet signs
  `J0Signs`, strictly unimodal rim depths, middle `0` below `max z4 z5` and `3` above `min z4 z5`, used by the tilt
  of Q45J0Tilt.lean) (the proofs are those of Q45J0.lean up to the far-vertex goals; DEDUP TODO: at the next rebuild
  of Q45J0 make `q45_*` corollaries of these);
* `isRupert_of_j0Chord`: `J0Chord` and `J0PairOff` (the far pair 2, 6 off the chord 4 5 in the segment sense of
  `noPersistHDN_of_farPair_offChord`) give Rupert, with no tie hypothesis: on S3 (edge 26 parallel to 0345) the far
  feature is the edge 26, elsewhere the farther vertex.
-/

namespace Minimality.T24.Q45

/-- The J0 face-chord data at the view `u` without the far vertex (rim `6 4 5 2`, chord `4 → 5` = rim edge `1 → 2`):
`u` on the face circle of facet `3`, the rim tests, the middles `0`, `3`, distinct rim depths, unimodal or split. -/
def J0Chord {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (u : ℝ³) (ρ : ℝ) : Prop :=
  ⟪F.N 3, u⟫ = 0 ∧ ρ ≠ 0 ∧
  (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
    0 < ρ * det3 (x (quad 6 4 5 2 (i + 1)) - x (quad 6 4 5 2 i)) (x (quad 6 4 5 2 j) - x (quad 6 4 5 2 i)) u) ∧
  (∀ q, q ∉ s0x_S24 3 → (∀ j : ZMod 4, q ≠ quad 6 4 5 2 j) → ∀ i : ZMod 4,
    0 < ρ * det3 (x (quad 6 4 5 2 (i + 1)) - x (quad 6 4 5 2 i)) (x q - x (quad 6 4 5 2 i)) u) ∧
  (∀ q ∈ s0x_S24 3, (∀ j : ZMod 4, q ≠ quad 6 4 5 2 j) → ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
    x q = x (quad 6 4 5 2 1) + s • (x (quad 6 4 5 2 (1 + 1)) - x (quad 6 4 5 2 1)) + δ • u) ∧
  Function.Injective (fun i : ZMod 4 => ⟪x (quad 6 4 5 2 i), u⟫) ∧
  UniOrSep (fun i : ZMod 4 => x (quad 6 4 5 2 i)) u

/-- The rim tests of the J0 face chord at `u` (`J0Chord` without the rim-depth conditions): `u` on the face circle
of facet `3`, the rim tests of `6 4 5 2`, the middles `0`, `3` over the chord `4 5` (job OSPEC7). -/
def J0Tests {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (u : ℝ³) (ρ : ℝ) : Prop :=
  ⟪F.N 3, u⟫ = 0 ∧ ρ ≠ 0 ∧
  (∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
    0 < ρ * det3 (x (quad 6 4 5 2 (i + 1)) - x (quad 6 4 5 2 i)) (x (quad 6 4 5 2 j) - x (quad 6 4 5 2 i)) u) ∧
  (∀ q, q ∉ s0x_S24 3 → (∀ j : ZMod 4, q ≠ quad 6 4 5 2 j) → ∀ i : ZMod 4,
    0 < ρ * det3 (x (quad 6 4 5 2 (i + 1)) - x (quad 6 4 5 2 i)) (x q - x (quad 6 4 5 2 i)) u) ∧
  (∀ q ∈ s0x_S24 3, (∀ j : ZMod 4, q ≠ quad 6 4 5 2 j) → ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
    x q = x (quad 6 4 5 2 1) + s • (x (quad 6 4 5 2 (1 + 1)) - x (quad 6 4 5 2 1)) + δ • u)

theorem J0Chord.of_tests {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x} {u : ℝ³} {ρ : ℝ} (h : J0Tests F u ρ)
    (hinj : Function.Injective (fun i : ZMod 4 => ⟪x (quad 6 4 5 2 i), u⟫))
    (hz : UniOrSep (fun i : ZMod 4 => x (quad 6 4 5 2 i)) u) : J0Chord F u ρ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, hinj, hz⟩

/-- The J0 facet signs at the view `u` (the `lemma_signs_J0` pattern, facets `025 046 126` down, `235 236 346` up). -/
def J0Signs {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (u : ℝ³) : Prop :=
  ⟪F.N 2, u⟫ < 0 ∧ ⟪F.N 4, u⟫ < 0 ∧ ⟪F.N 5, u⟫ < 0 ∧ 0 < ⟪F.N 6, u⟫ ∧ 0 < ⟪F.N 7, u⟫ ∧ 0 < ⟪F.N 8, u⟫

/-- What the J0 cores know at their view besides `J0Chord` (job OSPEC4): the facet signs, strictly unimodal rim
depths, and the depth sides of the middles (`0` has offset `δ < 0`, `3` has `δ > 0`). -/
def J0Extra {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (u : ℝ³) : Prop :=
  J0Signs F u ∧ StrictUnimodal (fun i => ⟪quad (x 6) (x 4) (x 5) (x 2) i, u⟫) ∧
    ⟪x 0, u⟫ < max ⟪x 4, u⟫ ⟪x 5, u⟫ ∧ min ⟪x 4, u⟫ ⟪x 5, u⟫ < ⟪x 3, u⟫

/-- `J0Extra` with the strict unimodality only under adjacent-distinct rim depths (job OSPEC5: the cores
`q45_*_j0ww` have no S2 hypothesis, so an adjacent rim pair may tie at the view). -/
def J0ExtraW {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (u : ℝ³) : Prop :=
  J0Signs F u ∧ ((∀ i : ZMod 4, ⟪quad (x 6) (x 4) (x 5) (x 2) i, u⟫ ≠ ⟪quad (x 6) (x 4) (x 5) (x 2) (i + 1), u⟫) →
      StrictUnimodal (fun i => ⟪quad (x 6) (x 4) (x 5) (x 2) i, u⟫)) ∧
    ⟪x 0, u⟫ < max ⟪x 4, u⟫ ⟪x 5, u⟫ ∧ min ⟪x 4, u⟫ ⟪x 5, u⟫ < ⟪x 3, u⟫

/-- A view that reads the lex order at `(B, D)` separates every pair that is not orthogonal to both `B` and `D`. -/
theorem ne_of_lexOr {x : Fin 7 → ℝ³} {B D u : ℝ³}
    (hlex : ∀ a c : Fin 7, (0 < ⟪x a - x c, B⟫ ∨ (⟪x a - x c, B⟫ = 0 ∧ 0 < ⟪x a - x c, D⟫)) →
      ⟪x c, u⟫ < ⟪x a, u⟫) {a c : Fin 7} (h : ⟪x a - x c, B⟫ ≠ 0 ∨ ⟪x a - x c, D⟫ ≠ 0) :
    ⟪x a, u⟫ ≠ ⟪x c, u⟫ := by
  have nB : ⟪x c - x a, B⟫ = -⟪x a - x c, B⟫ := by rw [← inner_neg_left, neg_sub]
  have nD : ⟪x c - x a, D⟫ = -⟪x a - x c, D⟫ := by rw [← inner_neg_left, neg_sub]
  intro heq
  rcases lt_trichotomy ⟪x a - x c, B⟫ 0 with hb | hb | hb
  · have := hlex c a (Or.inl (by rw [nB]; linarith)); linarith
  · have hd : ⟪x a - x c, D⟫ ≠ 0 := h.resolve_left (not_not.mpr hb)
    rcases lt_or_gt_of_ne hd with hd | hd
    · have := hlex c a (Or.inr ⟨by rw [nB, hb, neg_zero], by rw [nD]; linarith⟩); linarith
    · have := hlex a c (Or.inr ⟨hb, hd⟩); linarith
  · have := hlex a c (Or.inl hb); linarith

/-- With the adjacent rim pairs off the S2 locus, a lex-reading view has adjacent-distinct rim depths. -/
theorem adj_of_lex {x : Fin 7 → ℝ³} {B D u : ℝ³}
    (hlex : ∀ a c : Fin 7, (0 < ⟪x a - x c, B⟫ ∨ (⟪x a - x c, B⟫ = 0 ∧ 0 < ⟪x a - x c, D⟫)) →
      ⟪x c, u⟫ < ⟪x a, u⟫)
    (h : ∀ i : ZMod 4, ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) (i + 1), B⟫ ≠ 0 ∨
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) (i + 1), D⟫ ≠ 0) :
    ∀ i : ZMod 4, ⟪quad (x 6) (x 4) (x 5) (x 2) i, u⟫ ≠ ⟪quad (x 6) (x 4) (x 5) (x 2) (i + 1), u⟫ := by
  have hq : ∀ j : ZMod 4, quad (x 6) (x 4) (x 5) (x 2) j = x (quad 6 4 5 2 j) := by
    intro j; fin_cases j <;> rfl
  intro i
  have hi := h i
  rw [hq, hq] at hi
  rw [hq, hq]
  exact ne_of_lexOr hlex hi

theorem depth_lt_max_of_mid {A B q u : ℝ³} {s δ : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hδ : δ < 0) (hu : u ≠ 0)
    (h : q = A + s • (B - A) + δ • u) : ⟪q, u⟫ < max ⟪A, u⟫ ⟪B, u⟫ := by
  have hq : ⟪q, u⟫ = (1 - s) * ⟪A, u⟫ + s * ⟪B, u⟫ + δ * ⟪u, u⟫ := by
    rw [h, inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_sub_left]; ring
  have huu : 0 < ⟪u, u⟫ := real_inner_self_pos.mpr hu
  rw [hq]
  rcases le_total ⟪A, u⟫ ⟪B, u⟫ with hAB | hAB
  · rw [max_eq_right hAB]; nlinarith
  · rw [max_eq_left hAB]; nlinarith

theorem min_lt_depth_of_mid {A B q u : ℝ³} {s δ : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hδ : 0 < δ) (hu : u ≠ 0)
    (h : q = A + s • (B - A) + δ • u) : min ⟪A, u⟫ ⟪B, u⟫ < ⟪q, u⟫ := by
  have hq : ⟪q, u⟫ = (1 - s) * ⟪A, u⟫ + s * ⟪B, u⟫ + δ * ⟪u, u⟫ := by
    rw [h, inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_sub_left]; ring
  have huu : 0 < ⟪u, u⟫ := real_inner_self_pos.mpr hu
  rw [hq]
  rcases le_total ⟪A, u⟫ ⟪B, u⟫ with hAB | hAB
  · rw [min_eq_left hAB]; nlinarith
  · rw [min_eq_right hAB]; nlinarith

/-- A 4-cycle with adjacent values distinct and no double peak (`hn`, `hp` as in `isCyclicUnimodal_four`) is strictly
unimodal; opposite values may tie (OSPEC4). -/
theorem strictUnimodal_four_of_adj (z : ZMod 4 → ℝ) (hadj : ∀ i, z i ≠ z (i + 1))
    (hn : z 0 < z 1 ∨ z 0 < z 3 ∨ z 2 < z 1 ∨ z 2 < z 3)
    (hp : z 1 < z 0 ∨ z 3 < z 0 ∨ z 1 < z 2 ∨ z 3 < z 2) : StrictUnimodal z := by
  refine ⟨hadj, ?_⟩
  have d01 : z 0 ≠ z 1 := hadj 0
  have d12 : z 1 ≠ z 2 := hadj 1
  have d23 : z 2 ≠ z 3 := hadj 2
  have d30 : z 3 ≠ z 0 := hadj 3
  rw [Finset.card_filter]
  have hu : (Finset.univ : Finset (ZMod 4)) = {0, 1, 2, 3} := by decide
  rw [hu]
  have e1 : (0 : ZMod 4) - 1 = 3 := by decide
  have e2 : (1 : ZMod 4) - 1 = 0 := by decide
  have e3 : (2 : ZMod 4) - 1 = 1 := by decide
  have e4 : (3 : ZMod 4) - 1 = 2 := by decide
  have f1 : (0 : ZMod 4) + 1 = 1 := by decide
  have f2 : (1 : ZMod 4) + 1 = 2 := by decide
  have f3 : (2 : ZMod 4) + 1 = 3 := by decide
  have f4 : (3 : ZMod 4) + 1 = 0 := by decide
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, e1, e2, e3, e4, f1, f2, f3, f4]
  rcases lt_or_gt_of_ne d01 with a | a <;> rcases lt_or_gt_of_ne d12 with b | b <;>
    rcases lt_or_gt_of_ne d23 with c | c <;> rcases lt_or_gt_of_ne d30 with d | d <;>
    simp [*, not_lt_of_gt] <;> (exfalso; rcases hn with h | h | h | h <;> rcases hp with h' | h' | h' | h' <;> linarith)

/-- `unimodal_quad_Kplus` with adjacent-distinct depths only (opposite corners may tie). -/
theorem unimodal_quad_Kplus_adj (p : ZMod 4 → ℝ³) (u : ℝ³) (ρ : ℝ)
    (hadj : ∀ i, ⟪p i, u⟫ ≠ ⟪p (i + 1), u⟫)
    (hcyc : ∀ i, 0 < ρ * triD p u i)
    (hk : 0 < ρ * det3 (p 2 - p 0) (p 3 - p 1) (p 0 - p 1))
    (h6lo : min ⟪p 0, u⟫ ⟪p 2, u⟫ < max ⟪p 1, u⟫ ⟪p 3, u⟫) :
    Minimality.StrictUnimodal (fun i => ⟪p i, u⟫) := by
  have hnot_low := diagCross_not_low p u hcyc hk
  have hmin_lt := min_lt_max_of_not_le hnot_low
  have hn := hn_of_min_lt_max (z := fun i => ⟪p i, u⟫) h6lo
  have hp := hp_of_min_lt_max (z := fun i => ⟪p i, u⟫) hmin_lt
  exact strictUnimodal_four_of_adj (fun i => ⟪p i, u⟫) hadj hn hp

/-- `unimodal_quad_Kminus` with adjacent-distinct depths only. -/
theorem unimodal_quad_Kminus_adj (p : ZMod 4 → ℝ³) (u : ℝ³) (ρ : ℝ)
    (hadj : ∀ i, ⟪p i, u⟫ ≠ ⟪p (i + 1), u⟫)
    (hcyc : ∀ i, 0 < ρ * triD p u i)
    (hk : ρ * det3 (p 2 - p 0) (p 3 - p 1) (p 0 - p 1) < 0)
    (h2lo : min ⟪p 1, u⟫ ⟪p 3, u⟫ < max ⟪p 0, u⟫ ⟪p 2, u⟫) :
    Minimality.StrictUnimodal (fun i => ⟪p i, u⟫) := by
  have hnot_high := diagCross_not_high p u hcyc hk
  have hmin_lt := min_lt_max_of_not_le hnot_high
  have hn := hn_of_min_lt_max (z := fun i => ⟪p i, u⟫) hmin_lt
  have hp := hp_of_min_lt_max (z := fun i => ⟪p i, u⟫) h2lo
  exact strictUnimodal_four_of_adj (fun i => ⟪p i, u⟫) hadj hn hp

theorem zmod4_ne_succ (i : ZMod 4) : i ≠ i + 1 := by revert i; decide

/-- With the adjacent rim pairs off the S2 locus (`hS2a`), an S2 pair is an opposite pair `4 2` or `6 5`. -/
theorem s2_opp_of (p : ZMod 4 → ℝ³) (b d : ℝ³)
    (hS2a : ∀ i : ZMod 4, ⟪p i - p (i + 1), b⟫ ≠ 0 ∨ ⟪p i - p (i + 1), d⟫ ≠ 0)
    (hS2 : ¬ ∀ i j : ZMod 4, i ≠ j → ⟪p i - p j, b⟫ ≠ 0 ∨ ⟪p i - p j, d⟫ ≠ 0) :
    (⟪p 1 - p 3, b⟫ = 0 ∧ ⟪p 1 - p 3, d⟫ = 0) ∨ (⟪p 0 - p 2, b⟫ = 0 ∧ ⟪p 0 - p 2, d⟫ = 0) := by
  have neg : ∀ i j : ZMod 4, ∀ v : ℝ³, ⟪p i - p j, v⟫ = -⟪p j - p i, v⟫ := by
    intro i j v; rw [← inner_neg_left, neg_sub]
  by_contra hc
  apply hS2
  intro i j hij
  simp only [not_or, not_and_or] at hc
  obtain ⟨c13, c02⟩ := hc
  have shape : ∀ i j : ZMod 4, i ≠ j → j = i + 1 ∨ i = j + 1 ∨ j = i + 2 := by decide
  have four : ∀ i : ZMod 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide
  rcases shape i j hij with rfl | rfl | rfl
  · exact hS2a i
  · rw [neg (j + 1) j b, neg (j + 1) j d, neg_ne_zero, neg_ne_zero]; exact hS2a j
  · rcases four i with rfl | rfl | rfl | rfl
    · exact c02
    · exact c13
    · rw [show (2 : ZMod 4) + 2 = 0 from rfl, neg 2 0 b, neg 2 0 d, neg_ne_zero, neg_ne_zero]; exact c02
    · rw [show (3 : ZMod 4) + 2 = 1 from rfl, neg 3 1 b, neg 3 1 d, neg_ne_zero, neg_ne_zero]; exact c13

theorem eventually_adj_quad (p : ZMod 4 → ℝ³) (b d : ℝ³)
    (h : ∀ i : ZMod 4, ⟪p i - p (i + 1), b⟫ ≠ 0 ∨ ⟪p i - p (i + 1), d⟫ ≠ 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i : ZMod 4, ⟪p i, b + ε • d⟫ ≠ ⟪p (i + 1), b + ε • d⟫ := by
  refine eventually_all.mpr fun i => ?_
  filter_upwards [eventually_ne_affine_or (h i)] with ε hε heq
  apply hε
  rw [← sub_eq_zero.mpr heq, ← inner_sub_left, inner_add_right, real_inner_smul_right]

/-- Core of `q45_Kplus_s_le_one` (no far-vertex hypotheses `hS3`, `hS4`): the J0 chord data.  The branch sign may
also vanish on the wall `a5 = 1` if `⟪N5, x 4 - x 0⟫ < 0` (the views `e5 + ε e4` still have `⟪N5, ·⟫ < 0`).
 **Leaf K+ (Subcase s ≤ 1, E5 = e5)**:
When `ρ0 * kJ > 0` and weak 6-high fails strictly at base `e5 = x 5 - x 0`.
- Views: `u_ε = e5 + ε • e4` in `J0` for small `ε > 0`.
- Rim: 6 4 5 2, chord 4 -> 5, middles 0, 3, farther w ∈ {2, 6}.
- Lemma K rules out 2-high everywhere on `J0`.
- Open condition `h6lo` rules out 6-high near `e5`. -/
theorem q45_Kplus_s_le_one_j0ww {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha5 : ⟪F.N 5, x 5 - x 0⟫ < 0 ∨ (⟪F.N 5, x 5 - x 0⟫ = 0 ∧ ⟪F.N 5, x 4 - x 0⟫ < 0))
    (s t : ℝ)
    (hs0 : 0 < s)
    (ht : 0 < t)
    (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hk : det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) < 0)
    (hs : s ≤ 1)
    (h6lo : min ⟪x 6, x 5 - x 0⟫ ⟪x 5, x 5 - x 0⟫ < max ⟪x 4, x 5 - x 0⟫ ⟪x 2, x 5 - x 0⟫)
    (P : ℝ³ → Prop) (hP : ∀ᶠ ε in 𝓝[>] (0 : ℝ), P ((x 5 - x 0) + ε • (x 4 - x 0))) :
    ∃ (u : ℝ³) (ρ : ℝ), ⟪F.N 3, u⟫ = 0 ∧ J0ExtraW F u ∧ (∃ ε : ℝ, u = (x 5 - x 0) + ε • (x 4 - x 0)) ∧
      (∀ a c : Fin 7, (0 < ⟪x a - x c, x 5 - x 0⟫ ∨ (⟪x a - x c, x 5 - x 0⟫ = 0 ∧ 0 < ⟪x a - x c, x 4 - x 0⟫)) →
        ⟪x c, u⟫ < ⟪x a, u⟫) ∧
      ((∀ i j : ZMod 4, i ≠ j →
        ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 5 - x 0⟫ ≠ 0 ∨
        ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 4 - x 0⟫ ≠ 0) → J0Chord F u ρ) ∧
      J0Tests F u ρ ∧ P u := by
  set p_quad := quad (x 6) (x 4) (x 5) (x 2)
  set r : ZMod 4 → Fin 7 := quad 6 4 5 2
  have hr : ∀ i : ZMod 4, x (r i) = p_quad i := by
    intro i; fin_cases i <;> rfl
  set b := x 5 - x 0
  set d := x 4 - x 0
  have hu_Pi : ∀ ε : ℝ, b + ε • d = u_Pi x 1 ε := by
    intro ε; ext j; simp [b, d, u_Pi, e4, e5]
  have ev_eps : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have ev_6 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < 1 * s + ε * (1 - t) := by
    have : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < s + ε * (1 - t) :=
      eventually_pos_affine (A := s) (B := 1 - t) (Or.inl hs0)
    filter_upwards [this] with ε hε
    linarith
  have ev_N5 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪F.N 5, b + ε • d⟫ < 0 := by
    have hlin : ∀ ε : ℝ, ⟪F.N 5, b + ε • d⟫ = ⟪F.N 5, b⟫ + ε * ⟪F.N 5, d⟫ := by
      intro ε; rw [inner_add_right, real_inner_smul_right]
    have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < - ⟪F.N 5, b⟫ + ε * (- ⟪F.N 5, d⟫) :=
      eventually_pos_affine (A := - ⟪F.N 5, b⟫) (B := - ⟪F.N 5, d⟫)
        (by rcases ha5 with h | ⟨h1, h2⟩
            · exact Or.inl (by linarith)
            · exact Or.inr ⟨by linarith, by linarith⟩)
    filter_upwards [hpos] with ε hε
    rw [hlin]; linarith
  have ev_6lo : ∀ᶠ ε in 𝓝[>] (0 : ℝ), min ⟪p_quad 0, b + ε • d⟫ ⟪p_quad 2, b + ε • d⟫ < max ⟪p_quad 1, b + ε • d⟫ ⟪p_quad 3, b + ε • d⟫ :=
    eventually_min02_lt_max13 p_quad b d h6lo
  have ev_inj : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (∀ i j : ZMod 4, i ≠ j → ⟪p_quad i - p_quad j, b⟫ ≠ 0 ∨
      ⟪p_quad i - p_quad j, d⟫ ≠ 0) → Function.Injective (fun i => ⟪p_quad i, b + ε • d⟫) := by
    by_cases hS2 : ∀ i j : ZMod 4, i ≠ j → ⟪p_quad i - p_quad j, b⟫ ≠ 0 ∨ ⟪p_quad i - p_quad j, d⟫ ≠ 0
    · filter_upwards [eventually_injective_quad p_quad b d hS2] with ε hε _ using hε
    · exact Eventually.of_forall fun ε h => absurd h hS2
  have ev_lex : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ a c : Fin 7,
      (0 < ⟪x a - x c, b⟫ ∨ (⟪x a - x c, b⟫ = 0 ∧ 0 < ⟪x a - x c, d⟫)) → ⟪x c, b + ε • d⟫ < ⟪x a, b + ε • d⟫ := by
    refine eventually_all.mpr fun a => eventually_all.mpr fun c => ?_
    by_cases hlx : 0 < ⟪x a - x c, b⟫ ∨ (⟪x a - x c, b⟫ = 0 ∧ 0 < ⟪x a - x c, d⟫)
    · filter_upwards [eventually_pos_affine hlx] with ε hε _
      have hl : ⟪x a, b + ε • d⟫ - ⟪x c, b + ε • d⟫ = ⟪x a - x c, b⟫ + ε * ⟪x a - x c, d⟫ := by
        rw [← inner_sub_left, inner_add_right, real_inner_smul_right]
      linarith
    · exact Eventually.of_forall fun ε h' => absurd h' hlx
  have ev_all := ev_eps.and (ev_6.and (ev_N5.and (ev_6lo.and (ev_inj.and (ev_lex.and hP)))))
  obtain ⟨ε, hε, h6, hN5_u, h6lo_u, hinj_u, hlex_u, hP_u⟩ := ev_all.exists
  set u := b + ε • d
  have hu_Pi_eq : u = u_Pi x 1 ε := hu_Pi ε
  have h8 : 0 < 1 * (1 - s) + ε * t := by nlinarith [hs, ht, hε]
  have hN5_Pi : ⟪F.N 5, u_Pi x 1 ε⟫ < 0 := by rw [← hu_Pi_eq]; exact hN5_u
  have hsigns := lemma_signs_J0 F s t 1 ε hs0 ht hst hdecomp one_pos hε h8 h6 hN5_Pi
  rw [← hu_Pi_eq] at hsigns
  have hN3 : ⟪F.N 3, u⟫ = 0 := hsigns.1
  have hN2 : ⟪F.N 2, u⟫ < 0 := hsigns.2.1
  have hN4 : ⟪F.N 4, u⟫ < 0 := hsigns.2.2.1
  have hN5 : ⟪F.N 5, u⟫ < 0 := hsigns.2.2.2.1
  have hN6 : 0 < ⟪F.N 6, u⟫ := hsigns.2.2.2.2.1
  have hN7 : 0 < ⟪F.N 7, u⟫ := hsigns.2.2.2.2.2.1
  have hN8 : 0 < ⟪F.N 8, u⟫ := hsigns.2.2.2.2.2.2
  obtain ⟨ρ, hρ_ne, hcyc, hin⟩ := lemmaR_quad_signs F hN3 hN2 hN4 hN5 hN6 hN7 hN8
  have hin3 := hin 3
  have h3_eq : quad (x 6) (x 4) (x 5) (x 2) (3 + 1) - quad (x 6) (x 4) (x 5) (x 2) 3 = x 6 - x 2 := by
    show quad (x 6) (x 4) (x 5) (x 2) 0 - quad (x 6) (x 4) (x 5) (x 2) 3 = x 6 - x 2
    rfl
  have h3_1 : x 1 - quad (x 6) (x 4) (x 5) (x 2) 3 = x 1 - x 2 := by
    show x 1 - quad (x 6) (x 4) (x 5) (x 2) 3 = x 1 - x 2
    rfl
  rw [h3_eq, h3_1] at hin3
  have h_rho_om := rho_mul_omega_pos_of_inner_neg F u ρ hin3 hN5
  set Ω := det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)
  have h_om_ne := omega_ne_zero F
  have h_om_sq : 0 < Ω ^ 2 := sq_pos_of_ne_zero h_om_ne
  have hkap := kappa_rim6452 x
  have h_om_kap : 0 < Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1) := by
    dsimp [p_quad]
    rw [hkap]
    linarith [hk]
  have hk_pos : 0 < ρ * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1) := by
    have hprod : 0 < (ρ * Ω) * (Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) :=
      mul_pos h_rho_om h_om_kap
    have : (ρ * Ω) * (Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) =
        Ω ^ 2 * (ρ * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) := by ring
    rw [this] at hprod
    exact pos_of_mul_pos_right hprod h_om_sq.le
  have h_triD (i : ZMod 4) : 0 < ρ * triD p_quad u i := by
    have hneq1 : (i + 2 : ZMod 4) ≠ i := by
      intro h
      have : (2 : ZMod 4) = 0 := by
        calc (2 : ZMod 4) = (i + 2) - i := by ring
        _ = i - i := by rw [h]
        _ = 0 := sub_self i
      revert this; decide
    have hneq2 : (i + 2 : ZMod 4) ≠ i + 1 := by
      intro h
      have : (1 : ZMod 4) = 0 := by
        calc (1 : ZMod 4) = (i + 2) - (i + 1) := by ring
        _ = (i + 1) - (i + 1) := by rw [h]
        _ = 0 := sub_self _
      revert this; decide
    exact hcyc i (i + 2) hneq1 hneq2
  have h_uni := fun hadj => unimodal_quad_Kplus_adj p_quad u ρ hadj h_triD hk_pos h6lo_u
  have h_mb := middle_bounds_J0 s t 1 ε hst one_pos hε h8 h6
  set a : ZMod 4 := 1
  have hr' : ∀ i : ZMod 4, x (quad 6 4 5 2 i) = p_quad i := hr
  have hu0 : u ≠ 0 := fun h0 => by rw [h0, inner_zero_right] at hN2; exact lt_irrefl _ hN2
  have htests : J0Tests F u ρ := by
    refine ⟨hN3, hρ_ne, ?_, ?_, ?_⟩
    · intro i j hj1 hj2
      simp_rw [hr']
      exact hcyc i j hj1 hj2
    · intro q hqS hqr i
      have hq1 := exterior_vertices_J0 q hqS hqr
      subst hq1
      simp_rw [hr']
      exact hin i
    · intro q hqS hqr
      have hq03 := middle_vertices_J0 q hqS hqr
      have hra : x (r a) = x 4 := rfl
      have hra1 : x (r (a + 1)) = x 5 := rfl
      rw [hra, hra1]
      rcases hq03 with rfl | rfl
      · refine ⟨1 / (1 + ε), - (1 / (1 + ε)), h_mb.1.1, h_mb.1.2.1, h_mb.1.2.2, ?_⟩
        rw [hu_Pi_eq]
        exact middle_quad_x0 x 1 ε (by linarith [hε])
      · refine ⟨((1 - s) * 1 + t * ε) / (1 + ε), (s + t - 1) / (1 + ε), h_mb.2.1, h_mb.2.2.1, h_mb.2.2.2, ?_⟩
        rw [hu_Pi_eq]
        exact middle_quad_x3 x s t 1 ε hdecomp (by linarith [hε])
  refine ⟨u, ρ, hN3, ⟨⟨hN2, hN4, hN5, hN6, hN7, hN8⟩, h_uni, ?_, ?_⟩, ⟨ε, rfl⟩, hlex_u,
    fun hS2 => J0Chord.of_tests htests ?_ ?_, htests, hP_u⟩
  · have e0 := middle_quad_x0 x 1 ε (by linarith)
    rw [← hu_Pi_eq] at e0
    exact depth_lt_max_of_mid h_mb.1.1 h_mb.1.2.1 (neg_neg_of_pos (one_div_pos.mpr (by linarith))) hu0 e0
  · have e3 := middle_quad_x3 x s t 1 ε hdecomp (by linarith)
    rw [← hu_Pi_eq] at e3
    exact min_lt_depth_of_mid h_mb.2.1 h_mb.2.2.1 (div_pos (by linarith) (by linarith)) hu0 e3
  · simp_rw [hr']
    exact hinj_u hS2
  · simp_rw [hr']
    exact Or.inl (h_uni fun i h => zmod4_ne_succ i (hinj_u hS2 h))

/-- The weak core with the adjacent rim pairs off the S2 locus (`hS2a`): strictly unimodal rim depths. -/
theorem q45_Kplus_s_le_one_j0w {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha5 : ⟪F.N 5, x 5 - x 0⟫ < 0 ∨ (⟪F.N 5, x 5 - x 0⟫ = 0 ∧ ⟪F.N 5, x 4 - x 0⟫ < 0))
    (s t : ℝ)
    (hs0 : 0 < s)
    (ht : 0 < t)
    (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hk : det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) < 0)
    (hs : s ≤ 1)
    (h6lo : min ⟪x 6, x 5 - x 0⟫ ⟪x 5, x 5 - x 0⟫ < max ⟪x 4, x 5 - x 0⟫ ⟪x 2, x 5 - x 0⟫)
    (hS2a : ∀ i : ZMod 4,
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) (i + 1), x 5 - x 0⟫ ≠ 0 ∨
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) (i + 1), x 4 - x 0⟫ ≠ 0) :
    ∃ (u : ℝ³) (ρ : ℝ), ⟪F.N 3, u⟫ = 0 ∧ J0Extra F u ∧ (∃ ε : ℝ, u = (x 5 - x 0) + ε • (x 4 - x 0)) ∧
      (∀ a c : Fin 7, (0 < ⟪x a - x c, x 5 - x 0⟫ ∨ (⟪x a - x c, x 5 - x 0⟫ = 0 ∧ 0 < ⟪x a - x c, x 4 - x 0⟫)) →
        ⟪x c, u⟫ < ⟪x a, u⟫) ∧
      ((∀ i j : ZMod 4, i ≠ j →
        ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 5 - x 0⟫ ≠ 0 ∨
        ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 4 - x 0⟫ ≠ 0) → J0Chord F u ρ) := by
  obtain ⟨u, ρ, h3, ⟨hs, hU, h0, h3'⟩, hu, hlex, hc, -⟩ := q45_Kplus_s_le_one_j0ww F
    ha5 s t hs0 ht hst hdecomp hk hs h6lo (fun _ => True) (Eventually.of_forall fun _ => trivial)
  exact ⟨u, ρ, h3, ⟨hs, hU (adj_of_lex hlex hS2a), h0, h3'⟩, hu, hlex, hc⟩

/-- The old form (full `hS2`): `J0Chord` and `J0Extra`. -/
theorem q45_Kplus_s_le_one_j0 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha5 : ⟪F.N 5, x 5 - x 0⟫ < 0 ∨ (⟪F.N 5, x 5 - x 0⟫ = 0 ∧ ⟪F.N 5, x 4 - x 0⟫ < 0))
    (s t : ℝ)
    (hs0 : 0 < s)
    (ht : 0 < t)
    (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hk : det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) < 0)
    (hs : s ≤ 1)
    (h6lo : min ⟪x 6, x 5 - x 0⟫ ⟪x 5, x 5 - x 0⟫ < max ⟪x 4, x 5 - x 0⟫ ⟪x 2, x 5 - x 0⟫)
    (hS2 : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 5 - x 0⟫ ≠ 0 ∨
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 4 - x 0⟫ ≠ 0) :
    ∃ (u : ℝ³) (ρ : ℝ), J0Chord F u ρ ∧ J0Extra F u := by
  obtain ⟨u, ρ, -, hx, -, -, hc⟩ := q45_Kplus_s_le_one_j0w F ha5 s t hs0 ht hst hdecomp hk hs h6lo
    (fun i => hS2 i (i + 1) (zmod4_ne_succ i))
  exact ⟨u, ρ, hc hS2, hx⟩

/-- Core of `q45_Kplus_s_gt_one` (no far-vertex hypotheses `hS3`, `hS4`): the J0 chord data.
 **Leaf K+ (Subcase 1 < s, E5 = e34)**:
When `ρ0 * kJ > 0` and weak 6-high fails strictly at base `e34 = x 3 - x 4`.
- Views: `u_ε = (x 3 - x 4) + ε • (x 4 - x 0)` in `J0` for small `ε > 0`.
- Rim: 6 4 5 2, chord 4 -> 5, middles 0, 3, farther w ∈ {2, 6}.
- Lemma K rules out 2-high everywhere on `J0`.
- Open condition `h6lo` rules out 6-high near `e34`. -/
theorem q45_Kplus_s_gt_one_j0ww {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha34 : ⟪F.N 5, x 3 - x 4⟫ < 0)
    (s t : ℝ)
    (hs0 : 0 < s)
    (ht : 0 < t)
    (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hk : det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) < 0)
    (hs : 1 < s)
    (h6lo : min ⟪x 6, x 3 - x 4⟫ ⟪x 5, x 3 - x 4⟫ < max ⟪x 4, x 3 - x 4⟫ ⟪x 2, x 3 - x 4⟫)
    (P : ℝ³ → Prop) (hP : ∀ᶠ ε in 𝓝[>] (0 : ℝ), P ((x 3 - x 4) + ε • (x 4 - x 0))) :
    ∃ (u : ℝ³) (ρ : ℝ), ⟪F.N 3, u⟫ = 0 ∧ J0ExtraW F u ∧ (∃ ε : ℝ, u = (x 3 - x 4) + ε • (x 4 - x 0)) ∧
      (∀ a c : Fin 7, (0 < ⟪x a - x c, x 3 - x 4⟫ ∨ (⟪x a - x c, x 3 - x 4⟫ = 0 ∧ 0 < ⟪x a - x c, x 4 - x 0⟫)) →
        ⟪x c, u⟫ < ⟪x a, u⟫) ∧
      ((∀ i j : ZMod 4, i ≠ j →
        ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 3 - x 4⟫ ≠ 0 ∨
        ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 4 - x 0⟫ ≠ 0) → J0Chord F u ρ) ∧
      J0Tests F u ρ ∧ P u := by
  set p_quad := quad (x 6) (x 4) (x 5) (x 2)
  set r : ZMod 4 → Fin 7 := quad 6 4 5 2
  have hr : ∀ i : ZMod 4, x (r i) = p_quad i := by
    intro i; fin_cases i <;> rfl
  set b := x 3 - x 4
  set d := x 4 - x 0
  have hu_Pi : ∀ ε : ℝ, b + ε • d = u_Pi x t (s - 1 + ε) := by
    intro ε; ext j
    have hdj := congr_arg (fun (v : ℝ³) => v j) hdecomp
    dsimp [b, d, u_Pi, e4, e5, e34] at hdj ⊢
    linear_combination hdj
  have ev_eps : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have ev_beta : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < s - 1 + ε := by
    have := eventually_pos_affine (A := s - 1) (B := 1) (Or.inl (by linarith [hs]))
    filter_upwards [this] with ε hε; linarith
  have ev_6 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < t * s + (s - 1 + ε) * (1 - t) := by
    have hA : 0 < t * s + (s - 1) * (1 - t) := by linarith [hst]
    have := eventually_pos_affine (A := t * s + (s - 1) * (1 - t)) (B := 1 - t) (Or.inl hA)
    filter_upwards [this] with ε hε
    have : t * s + (s - 1 + ε) * (1 - t) = t * s + (s - 1) * (1 - t) + ε * (1 - t) := by ring
    rw [this]; exact hε
  have ev_N5 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪F.N 5, b + ε • d⟫ < 0 := by
    have hlin : ∀ ε : ℝ, ⟪F.N 5, b + ε • d⟫ = ⟪F.N 5, b⟫ + ε * ⟪F.N 5, d⟫ := by
      intro ε; rw [inner_add_right, real_inner_smul_right]
    have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < - ⟪F.N 5, b⟫ + ε * (- ⟪F.N 5, d⟫) :=
      eventually_pos_affine (A := - ⟪F.N 5, b⟫) (B := - ⟪F.N 5, d⟫) (Or.inl (by linarith [ha34]))
    filter_upwards [hpos] with ε hε
    rw [hlin]; linarith
  have ev_6lo : ∀ᶠ ε in 𝓝[>] (0 : ℝ), min ⟪p_quad 0, b + ε • d⟫ ⟪p_quad 2, b + ε • d⟫ < max ⟪p_quad 1, b + ε • d⟫ ⟪p_quad 3, b + ε • d⟫ :=
    eventually_min02_lt_max13 p_quad b d h6lo
  have ev_inj : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (∀ i j : ZMod 4, i ≠ j → ⟪p_quad i - p_quad j, b⟫ ≠ 0 ∨
      ⟪p_quad i - p_quad j, d⟫ ≠ 0) → Function.Injective (fun i => ⟪p_quad i, b + ε • d⟫) := by
    by_cases hS2 : ∀ i j : ZMod 4, i ≠ j → ⟪p_quad i - p_quad j, b⟫ ≠ 0 ∨ ⟪p_quad i - p_quad j, d⟫ ≠ 0
    · filter_upwards [eventually_injective_quad p_quad b d hS2] with ε hε _ using hε
    · exact Eventually.of_forall fun ε h => absurd h hS2
  have ev_lex : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ a c : Fin 7,
      (0 < ⟪x a - x c, b⟫ ∨ (⟪x a - x c, b⟫ = 0 ∧ 0 < ⟪x a - x c, d⟫)) → ⟪x c, b + ε • d⟫ < ⟪x a, b + ε • d⟫ := by
    refine eventually_all.mpr fun a => eventually_all.mpr fun c => ?_
    by_cases hlx : 0 < ⟪x a - x c, b⟫ ∨ (⟪x a - x c, b⟫ = 0 ∧ 0 < ⟪x a - x c, d⟫)
    · filter_upwards [eventually_pos_affine hlx] with ε hε _
      have hl : ⟪x a, b + ε • d⟫ - ⟪x c, b + ε • d⟫ = ⟪x a - x c, b⟫ + ε * ⟪x a - x c, d⟫ := by
        rw [← inner_sub_left, inner_add_right, real_inner_smul_right]
      linarith
    · exact Eventually.of_forall fun ε h' => absurd h' hlx
  have ev_all := ev_eps.and (ev_beta.and (ev_6.and (ev_N5.and (ev_6lo.and (ev_inj.and (ev_lex.and hP))))))
  obtain ⟨ε, hε, hβ, h6, hN5_u, h6lo_u, hinj_u, hlex_u, hP_u⟩ := ev_all.exists
  set u := b + ε • d
  have hu_Pi_eq : u = u_Pi x t (s - 1 + ε) := hu_Pi ε
  have h8 : 0 < t * (1 - s) + (s - 1 + ε) * t := by
    have : t * (1 - s) + (s - 1 + ε) * t = ε * t := by ring
    rw [this]; exact mul_pos hε ht
  have hN5_Pi : ⟪F.N 5, u_Pi x t (s - 1 + ε)⟫ < 0 := by rw [← hu_Pi_eq]; exact hN5_u
  have hsigns := lemma_signs_J0 F s t t (s - 1 + ε) hs0 ht hst hdecomp ht hβ h8 h6 hN5_Pi
  rw [← hu_Pi_eq] at hsigns
  have hN3 : ⟪F.N 3, u⟫ = 0 := hsigns.1
  have hN2 : ⟪F.N 2, u⟫ < 0 := hsigns.2.1
  have hN4 : ⟪F.N 4, u⟫ < 0 := hsigns.2.2.1
  have hN5 : ⟪F.N 5, u⟫ < 0 := hsigns.2.2.2.1
  have hN6 : 0 < ⟪F.N 6, u⟫ := hsigns.2.2.2.2.1
  have hN7 : 0 < ⟪F.N 7, u⟫ := hsigns.2.2.2.2.2.1
  have hN8 : 0 < ⟪F.N 8, u⟫ := hsigns.2.2.2.2.2.2
  obtain ⟨ρ, hρ_ne, hcyc, hin⟩ := lemmaR_quad_signs F hN3 hN2 hN4 hN5 hN6 hN7 hN8
  have hin3 := hin 3
  have h3_eq : quad (x 6) (x 4) (x 5) (x 2) (3 + 1) - quad (x 6) (x 4) (x 5) (x 2) 3 = x 6 - x 2 := by
    show quad (x 6) (x 4) (x 5) (x 2) 0 - quad (x 6) (x 4) (x 5) (x 2) 3 = x 6 - x 2
    rfl
  have h3_1 : x 1 - quad (x 6) (x 4) (x 5) (x 2) 3 = x 1 - x 2 := by
    show x 1 - quad (x 6) (x 4) (x 5) (x 2) 3 = x 1 - x 2
    rfl
  rw [h3_eq, h3_1] at hin3
  have h_rho_om := rho_mul_omega_pos_of_inner_neg F u ρ hin3 hN5
  set Ω := det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)
  have h_om_ne := omega_ne_zero F
  have h_om_sq : 0 < Ω ^ 2 := sq_pos_of_ne_zero h_om_ne
  have hkap := kappa_rim6452 x
  have h_om_kap : 0 < Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1) := by
    dsimp [p_quad]
    rw [hkap]
    linarith [hk]
  have hk_pos : 0 < ρ * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1) := by
    have hprod : 0 < (ρ * Ω) * (Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) :=
      mul_pos h_rho_om h_om_kap
    have : (ρ * Ω) * (Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) =
        Ω ^ 2 * (ρ * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) := by ring
    rw [this] at hprod
    exact pos_of_mul_pos_right hprod h_om_sq.le
  have h_triD (i : ZMod 4) : 0 < ρ * triD p_quad u i := by
    have hneq1 : (i + 2 : ZMod 4) ≠ i := by
      intro h
      have : (2 : ZMod 4) = 0 := by
        calc (2 : ZMod 4) = (i + 2) - i := by ring
        _ = i - i := by rw [h]
        _ = 0 := sub_self i
      revert this; decide
    have hneq2 : (i + 2 : ZMod 4) ≠ i + 1 := by
      intro h
      have : (1 : ZMod 4) = 0 := by
        calc (1 : ZMod 4) = (i + 2) - (i + 1) := by ring
        _ = (i + 1) - (i + 1) := by rw [h]
        _ = 0 := sub_self _
      revert this; decide
    exact hcyc i (i + 2) hneq1 hneq2
  have h_uni := fun hadj => unimodal_quad_Kplus_adj p_quad u ρ hadj h_triD hk_pos h6lo_u
  have h_mb := middle_bounds_J0 s t t (s - 1 + ε) hst ht hβ h8 h6
  set a : ZMod 4 := 1
  have hr' : ∀ i : ZMod 4, x (quad 6 4 5 2 i) = p_quad i := hr
  have hu0 : u ≠ 0 := fun h0 => by rw [h0, inner_zero_right] at hN2; exact lt_irrefl _ hN2
  have htests : J0Tests F u ρ := by
    refine ⟨hN3, hρ_ne, ?_, ?_, ?_⟩
    · intro i j hj1 hj2
      simp_rw [hr']
      exact hcyc i j hj1 hj2
    · intro q hqS hqr i
      have hq1 := exterior_vertices_J0 q hqS hqr
      subst hq1
      simp_rw [hr']
      exact hin i
    · intro q hqS hqr
      have hq03 := middle_vertices_J0 q hqS hqr
      have hra : x (r a) = x 4 := rfl
      have hra1 : x (r (a + 1)) = x 5 := rfl
      rw [hra, hra1]
      rcases hq03 with rfl | rfl
      · refine ⟨t / (t + (s - 1 + ε)), - (1 / (t + (s - 1 + ε))), h_mb.1.1, h_mb.1.2.1, h_mb.1.2.2, ?_⟩
        rw [hu_Pi_eq]
        exact middle_quad_x0 x t (s - 1 + ε) (by linarith [ht, hβ])
      · refine ⟨((1 - s) * t + t * (s - 1 + ε)) / (t + (s - 1 + ε)), (s + t - 1) / (t + (s - 1 + ε)), h_mb.2.1, h_mb.2.2.1, h_mb.2.2.2, ?_⟩
        rw [hu_Pi_eq]
        exact middle_quad_x3 x s t t (s - 1 + ε) hdecomp (by linarith [ht, hβ])
  refine ⟨u, ρ, hN3, ⟨⟨hN2, hN4, hN5, hN6, hN7, hN8⟩, h_uni, ?_, ?_⟩, ⟨ε, rfl⟩, hlex_u,
    fun hS2 => J0Chord.of_tests htests ?_ ?_, htests, hP_u⟩
  · have e0 := middle_quad_x0 x t (s - 1 + ε) (by linarith)
    rw [← hu_Pi_eq] at e0
    exact depth_lt_max_of_mid h_mb.1.1 h_mb.1.2.1 (neg_neg_of_pos (one_div_pos.mpr (by linarith))) hu0 e0
  · have e3 := middle_quad_x3 x s t t (s - 1 + ε) hdecomp (by linarith)
    rw [← hu_Pi_eq] at e3
    exact min_lt_depth_of_mid h_mb.2.1 h_mb.2.2.1 (div_pos (by linarith) (by linarith)) hu0 e3
  · simp_rw [hr']
    exact hinj_u hS2
  · simp_rw [hr']
    exact Or.inl (h_uni fun i h => zmod4_ne_succ i (hinj_u hS2 h))

/-- The weak core with the adjacent rim pairs off the S2 locus (`hS2a`): strictly unimodal rim depths. -/
theorem q45_Kplus_s_gt_one_j0w {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha34 : ⟪F.N 5, x 3 - x 4⟫ < 0)
    (s t : ℝ)
    (hs0 : 0 < s)
    (ht : 0 < t)
    (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hk : det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) < 0)
    (hs : 1 < s)
    (h6lo : min ⟪x 6, x 3 - x 4⟫ ⟪x 5, x 3 - x 4⟫ < max ⟪x 4, x 3 - x 4⟫ ⟪x 2, x 3 - x 4⟫)
    (hS2a : ∀ i : ZMod 4,
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) (i + 1), x 3 - x 4⟫ ≠ 0 ∨
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) (i + 1), x 4 - x 0⟫ ≠ 0) :
    ∃ (u : ℝ³) (ρ : ℝ), ⟪F.N 3, u⟫ = 0 ∧ J0Extra F u ∧ (∃ ε : ℝ, u = (x 3 - x 4) + ε • (x 4 - x 0)) ∧
      (∀ a c : Fin 7, (0 < ⟪x a - x c, x 3 - x 4⟫ ∨ (⟪x a - x c, x 3 - x 4⟫ = 0 ∧ 0 < ⟪x a - x c, x 4 - x 0⟫)) →
        ⟪x c, u⟫ < ⟪x a, u⟫) ∧
      ((∀ i j : ZMod 4, i ≠ j →
        ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 3 - x 4⟫ ≠ 0 ∨
        ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 4 - x 0⟫ ≠ 0) → J0Chord F u ρ) := by
  obtain ⟨u, ρ, h3, ⟨hs, hU, h0, h3'⟩, hu, hlex, hc, -⟩ := q45_Kplus_s_gt_one_j0ww F
    ha34 s t hs0 ht hst hdecomp hk hs h6lo (fun _ => True) (Eventually.of_forall fun _ => trivial)
  exact ⟨u, ρ, h3, ⟨hs, hU (adj_of_lex hlex hS2a), h0, h3'⟩, hu, hlex, hc⟩

/-- The old form (full `hS2`): `J0Chord` and `J0Extra`. -/
theorem q45_Kplus_s_gt_one_j0 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha34 : ⟪F.N 5, x 3 - x 4⟫ < 0)
    (s t : ℝ)
    (hs0 : 0 < s)
    (ht : 0 < t)
    (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hk : det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1) < 0)
    (hs : 1 < s)
    (h6lo : min ⟪x 6, x 3 - x 4⟫ ⟪x 5, x 3 - x 4⟫ < max ⟪x 4, x 3 - x 4⟫ ⟪x 2, x 3 - x 4⟫)
    (hS2 : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 3 - x 4⟫ ≠ 0 ∨
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 4 - x 0⟫ ≠ 0) :
    ∃ (u : ℝ³) (ρ : ℝ), J0Chord F u ρ ∧ J0Extra F u := by
  obtain ⟨u, ρ, -, hx, -, -, hc⟩ := q45_Kplus_s_gt_one_j0w F ha34 s t hs0 ht hst hdecomp hk hs h6lo
    (fun i => hS2 i (i + 1) (zmod4_ne_succ i))
  exact ⟨u, ρ, hc hS2, hx⟩

/-- Core of `q45_Kminus_t_le_one` (no far-vertex hypotheses `hS3`, `hS4`): the J0 chord data.  The branch sign may
also vanish on the wall `a4 = 1` if `⟪N5, x 5 - x 0⟫ < 0`.
 **Leaf K- (Subcase t ≤ 1, E4 = e4)**:
When `0 < ρ0 * kJ` (i.e. `0 < det3(256-plane) * Ω`) and weak 2-high fails strictly at base `e4 = x 4 - x 0`.
- Views: `u_ε = e4 + ε • e5` in `J0` for small `ε > 0`.
- Rim: 6 4 5 2, chord 4 -> 5, middles 0, 3, farther w ∈ {2, 6}.
- Lemma K rules out 6-high everywhere on `J0`.
- Open condition `h2lo` rules out 2-high near `e4`. -/
theorem q45_Kminus_t_le_one_j0ww {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha4 : ⟪F.N 5, x 4 - x 0⟫ < 0 ∨ (⟪F.N 5, x 4 - x 0⟫ = 0 ∧ ⟪F.N 5, x 5 - x 0⟫ < 0))
    (s t : ℝ)
    (hs0 : 0 < s)
    (ht : 0 < t)
    (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hk : 0 < det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1))
    (ht1 : t ≤ 1)
    (h2lo : min ⟪x 4, x 4 - x 0⟫ ⟪x 2, x 4 - x 0⟫ < max ⟪x 6, x 4 - x 0⟫ ⟪x 5, x 4 - x 0⟫)
    (P : ℝ³ → Prop) (hP : ∀ᶠ ε in 𝓝[>] (0 : ℝ), P ((x 4 - x 0) + ε • (x 5 - x 0))) :
    ∃ (u : ℝ³) (ρ : ℝ), ⟪F.N 3, u⟫ = 0 ∧ J0ExtraW F u ∧ (∃ ε : ℝ, u = (x 4 - x 0) + ε • (x 5 - x 0)) ∧
      (∀ a c : Fin 7, (0 < ⟪x a - x c, x 4 - x 0⟫ ∨ (⟪x a - x c, x 4 - x 0⟫ = 0 ∧ 0 < ⟪x a - x c, x 5 - x 0⟫)) →
        ⟪x c, u⟫ < ⟪x a, u⟫) ∧
      ((∀ i j : ZMod 4, i ≠ j →
        ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 4 - x 0⟫ ≠ 0 ∨
        ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 5 - x 0⟫ ≠ 0) → J0Chord F u ρ) ∧
      J0Tests F u ρ ∧ P u := by
  set p_quad := quad (x 6) (x 4) (x 5) (x 2)
  set r : ZMod 4 → Fin 7 := quad 6 4 5 2
  have hr : ∀ i : ZMod 4, x (r i) = p_quad i := by
    intro i; fin_cases i <;> rfl
  set b := x 4 - x 0
  set d := x 5 - x 0
  have hu_Pi : ∀ ε : ℝ, b + ε • d = u_Pi x ε 1 := by
    intro ε; ext j; simp [b, d, u_Pi, e4, e5]; ring
  have ev_eps : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have ev_8 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε * (1 - s) + 1 * t := by
    have : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < t + ε * (1 - s) :=
      eventually_pos_affine (A := t) (B := 1 - s) (Or.inl ht)
    filter_upwards [this] with ε hε
    linarith
  have ev_N5 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪F.N 5, b + ε • d⟫ < 0 := by
    have hlin : ∀ ε : ℝ, ⟪F.N 5, b + ε • d⟫ = ⟪F.N 5, b⟫ + ε * ⟪F.N 5, d⟫ := by
      intro ε; rw [inner_add_right, real_inner_smul_right]
    have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < - ⟪F.N 5, b⟫ + ε * (- ⟪F.N 5, d⟫) :=
      eventually_pos_affine (A := - ⟪F.N 5, b⟫) (B := - ⟪F.N 5, d⟫)
        (by rcases ha4 with h | ⟨h1, h2⟩
            · exact Or.inl (by linarith)
            · exact Or.inr ⟨by linarith, by linarith⟩)
    filter_upwards [hpos] with ε hε
    rw [hlin]; linarith
  have ev_2lo : ∀ᶠ ε in 𝓝[>] (0 : ℝ), min ⟪p_quad 1, b + ε • d⟫ ⟪p_quad 3, b + ε • d⟫ < max ⟪p_quad 0, b + ε • d⟫ ⟪p_quad 2, b + ε • d⟫ :=
    eventually_min13_lt_max02 p_quad b d h2lo
  have ev_inj : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (∀ i j : ZMod 4, i ≠ j → ⟪p_quad i - p_quad j, b⟫ ≠ 0 ∨
      ⟪p_quad i - p_quad j, d⟫ ≠ 0) → Function.Injective (fun i => ⟪p_quad i, b + ε • d⟫) := by
    by_cases hS2 : ∀ i j : ZMod 4, i ≠ j → ⟪p_quad i - p_quad j, b⟫ ≠ 0 ∨ ⟪p_quad i - p_quad j, d⟫ ≠ 0
    · filter_upwards [eventually_injective_quad p_quad b d hS2] with ε hε _ using hε
    · exact Eventually.of_forall fun ε h => absurd h hS2
  have ev_lex : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ a c : Fin 7,
      (0 < ⟪x a - x c, b⟫ ∨ (⟪x a - x c, b⟫ = 0 ∧ 0 < ⟪x a - x c, d⟫)) → ⟪x c, b + ε • d⟫ < ⟪x a, b + ε • d⟫ := by
    refine eventually_all.mpr fun a => eventually_all.mpr fun c => ?_
    by_cases hlx : 0 < ⟪x a - x c, b⟫ ∨ (⟪x a - x c, b⟫ = 0 ∧ 0 < ⟪x a - x c, d⟫)
    · filter_upwards [eventually_pos_affine hlx] with ε hε _
      have hl : ⟪x a, b + ε • d⟫ - ⟪x c, b + ε • d⟫ = ⟪x a - x c, b⟫ + ε * ⟪x a - x c, d⟫ := by
        rw [← inner_sub_left, inner_add_right, real_inner_smul_right]
      linarith
    · exact Eventually.of_forall fun ε h' => absurd h' hlx
  have ev_all := ev_eps.and (ev_8.and (ev_N5.and (ev_2lo.and (ev_inj.and (ev_lex.and hP)))))
  obtain ⟨ε, hε, h8, hN5_u, h2lo_u, hinj_u, hlex_u, hP_u⟩ := ev_all.exists
  set u := b + ε • d
  have hu_Pi_eq : u = u_Pi x ε 1 := hu_Pi ε
  have h6 : 0 < ε * s + 1 * (1 - t) := by nlinarith [ht1, hs0, hε]
  have hN5_Pi : ⟪F.N 5, u_Pi x ε 1⟫ < 0 := by rw [← hu_Pi_eq]; exact hN5_u
  have hsigns := lemma_signs_J0 F s t ε 1 hs0 ht hst hdecomp hε one_pos h8 h6 hN5_Pi
  rw [← hu_Pi_eq] at hsigns
  have hN3 : ⟪F.N 3, u⟫ = 0 := hsigns.1
  have hN2 : ⟪F.N 2, u⟫ < 0 := hsigns.2.1
  have hN4 : ⟪F.N 4, u⟫ < 0 := hsigns.2.2.1
  have hN5 : ⟪F.N 5, u⟫ < 0 := hsigns.2.2.2.1
  have hN6 : 0 < ⟪F.N 6, u⟫ := hsigns.2.2.2.2.1
  have hN7 : 0 < ⟪F.N 7, u⟫ := hsigns.2.2.2.2.2.1
  have hN8 : 0 < ⟪F.N 8, u⟫ := hsigns.2.2.2.2.2.2
  obtain ⟨ρ, hρ_ne, hcyc, hin⟩ := lemmaR_quad_signs F hN3 hN2 hN4 hN5 hN6 hN7 hN8
  have hin3 := hin 3
  have h3_eq : quad (x 6) (x 4) (x 5) (x 2) (3 + 1) - quad (x 6) (x 4) (x 5) (x 2) 3 = x 6 - x 2 := by
    show quad (x 6) (x 4) (x 5) (x 2) 0 - quad (x 6) (x 4) (x 5) (x 2) 3 = x 6 - x 2
    rfl
  have h3_1 : x 1 - quad (x 6) (x 4) (x 5) (x 2) 3 = x 1 - x 2 := by
    show x 1 - quad (x 6) (x 4) (x 5) (x 2) 3 = x 1 - x 2
    rfl
  rw [h3_eq, h3_1] at hin3
  have h_rho_om := rho_mul_omega_pos_of_inner_neg F u ρ hin3 hN5
  set Ω := det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)
  have h_om_ne := omega_ne_zero F
  have h_om_sq : 0 < Ω ^ 2 := sq_pos_of_ne_zero h_om_ne
  have hkap := kappa_rim6452 x
  have h_om_kap : Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1) < 0 := by
    dsimp [p_quad]
    rw [hkap]
    linarith [hk]
  have hk_neg : ρ * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1) < 0 := by
    have hprod : (ρ * Ω) * (Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) < 0 :=
      mul_neg_of_pos_of_neg h_rho_om h_om_kap
    have : (ρ * Ω) * (Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) =
        Ω ^ 2 * (ρ * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) := by ring
    rw [this] at hprod
    exact neg_of_mul_neg_right hprod h_om_sq.le
  have h_triD (i : ZMod 4) : 0 < ρ * triD p_quad u i := by
    have hneq1 : (i + 2 : ZMod 4) ≠ i := by
      intro h
      have : (2 : ZMod 4) = 0 := by
        calc (2 : ZMod 4) = (i + 2) - i := by ring
        _ = i - i := by rw [h]
        _ = 0 := sub_self i
      revert this; decide
    have hneq2 : (i + 2 : ZMod 4) ≠ i + 1 := by
      intro h
      have : (1 : ZMod 4) = 0 := by
        calc (1 : ZMod 4) = (i + 2) - (i + 1) := by ring
        _ = (i + 1) - (i + 1) := by rw [h]
        _ = 0 := sub_self _
      revert this; decide
    exact hcyc i (i + 2) hneq1 hneq2
  have h_uni := fun hadj => unimodal_quad_Kminus_adj p_quad u ρ hadj h_triD hk_neg h2lo_u
  have h_mb := middle_bounds_J0 s t ε 1 hst hε one_pos h8 h6
  set a : ZMod 4 := 1
  have hr' : ∀ i : ZMod 4, x (quad 6 4 5 2 i) = p_quad i := hr
  have hu0 : u ≠ 0 := fun h0 => by rw [h0, inner_zero_right] at hN2; exact lt_irrefl _ hN2
  have htests : J0Tests F u ρ := by
    refine ⟨hN3, hρ_ne, ?_, ?_, ?_⟩
    · intro i j hj1 hj2
      simp_rw [hr']
      exact hcyc i j hj1 hj2
    · intro q hqS hqr i
      have hq1 := exterior_vertices_J0 q hqS hqr
      subst hq1
      simp_rw [hr']
      exact hin i
    · intro q hqS hqr
      have hq03 := middle_vertices_J0 q hqS hqr
      have hra : x (r a) = x 4 := rfl
      have hra1 : x (r (a + 1)) = x 5 := rfl
      rw [hra, hra1]
      rcases hq03 with rfl | rfl
      · refine ⟨ε / (ε + 1), - (1 / (ε + 1)), h_mb.1.1, h_mb.1.2.1, h_mb.1.2.2, ?_⟩
        rw [hu_Pi_eq]
        exact middle_quad_x0 x ε 1 (by linarith [hε])
      · refine ⟨((1 - s) * ε + t * 1) / (ε + 1), (s + t - 1) / (ε + 1), h_mb.2.1, h_mb.2.2.1, h_mb.2.2.2, ?_⟩
        rw [hu_Pi_eq]
        exact middle_quad_x3 x s t ε 1 hdecomp (by linarith [hε])
  refine ⟨u, ρ, hN3, ⟨⟨hN2, hN4, hN5, hN6, hN7, hN8⟩, h_uni, ?_, ?_⟩, ⟨ε, rfl⟩, hlex_u,
    fun hS2 => J0Chord.of_tests htests ?_ ?_, htests, hP_u⟩
  · have e0 := middle_quad_x0 x ε 1 (by linarith)
    rw [← hu_Pi_eq] at e0
    exact depth_lt_max_of_mid h_mb.1.1 h_mb.1.2.1 (neg_neg_of_pos (one_div_pos.mpr (by linarith))) hu0 e0
  · have e3 := middle_quad_x3 x s t ε 1 hdecomp (by linarith)
    rw [← hu_Pi_eq] at e3
    exact min_lt_depth_of_mid h_mb.2.1 h_mb.2.2.1 (div_pos (by linarith) (by linarith)) hu0 e3
  · simp_rw [hr']
    exact hinj_u hS2
  · simp_rw [hr']
    exact Or.inl (h_uni fun i h => zmod4_ne_succ i (hinj_u hS2 h))

/-- The weak core with the adjacent rim pairs off the S2 locus (`hS2a`): strictly unimodal rim depths. -/
theorem q45_Kminus_t_le_one_j0w {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha4 : ⟪F.N 5, x 4 - x 0⟫ < 0 ∨ (⟪F.N 5, x 4 - x 0⟫ = 0 ∧ ⟪F.N 5, x 5 - x 0⟫ < 0))
    (s t : ℝ)
    (hs0 : 0 < s)
    (ht : 0 < t)
    (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hk : 0 < det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1))
    (ht1 : t ≤ 1)
    (h2lo : min ⟪x 4, x 4 - x 0⟫ ⟪x 2, x 4 - x 0⟫ < max ⟪x 6, x 4 - x 0⟫ ⟪x 5, x 4 - x 0⟫)
    (hS2a : ∀ i : ZMod 4,
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) (i + 1), x 4 - x 0⟫ ≠ 0 ∨
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) (i + 1), x 5 - x 0⟫ ≠ 0) :
    ∃ (u : ℝ³) (ρ : ℝ), ⟪F.N 3, u⟫ = 0 ∧ J0Extra F u ∧ (∃ ε : ℝ, u = (x 4 - x 0) + ε • (x 5 - x 0)) ∧
      (∀ a c : Fin 7, (0 < ⟪x a - x c, x 4 - x 0⟫ ∨ (⟪x a - x c, x 4 - x 0⟫ = 0 ∧ 0 < ⟪x a - x c, x 5 - x 0⟫)) →
        ⟪x c, u⟫ < ⟪x a, u⟫) ∧
      ((∀ i j : ZMod 4, i ≠ j →
        ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 4 - x 0⟫ ≠ 0 ∨
        ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 5 - x 0⟫ ≠ 0) → J0Chord F u ρ) := by
  obtain ⟨u, ρ, h3, ⟨hs, hU, h0, h3'⟩, hu, hlex, hc, -⟩ := q45_Kminus_t_le_one_j0ww F
    ha4 s t hs0 ht hst hdecomp hk ht1 h2lo (fun _ => True) (Eventually.of_forall fun _ => trivial)
  exact ⟨u, ρ, h3, ⟨hs, hU (adj_of_lex hlex hS2a), h0, h3'⟩, hu, hlex, hc⟩

/-- The old form (full `hS2`): `J0Chord` and `J0Extra`. -/
theorem q45_Kminus_t_le_one_j0 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha4 : ⟪F.N 5, x 4 - x 0⟫ < 0 ∨ (⟪F.N 5, x 4 - x 0⟫ = 0 ∧ ⟪F.N 5, x 5 - x 0⟫ < 0))
    (s t : ℝ)
    (hs0 : 0 < s)
    (ht : 0 < t)
    (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hk : 0 < det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1))
    (ht1 : t ≤ 1)
    (h2lo : min ⟪x 4, x 4 - x 0⟫ ⟪x 2, x 4 - x 0⟫ < max ⟪x 6, x 4 - x 0⟫ ⟪x 5, x 4 - x 0⟫)
    (hS2 : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 4 - x 0⟫ ≠ 0 ∨
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 5 - x 0⟫ ≠ 0) :
    ∃ (u : ℝ³) (ρ : ℝ), J0Chord F u ρ ∧ J0Extra F u := by
  obtain ⟨u, ρ, -, hx, -, -, hc⟩ := q45_Kminus_t_le_one_j0w F ha4 s t hs0 ht hst hdecomp hk ht1 h2lo
    (fun i => hS2 i (i + 1) (zmod4_ne_succ i))
  exact ⟨u, ρ, hc hS2, hx⟩

/-- Core of `q45_Kminus_t_gt_one` (no far-vertex hypotheses `hS3`, `hS4`): the J0 chord data.
 **Leaf K- (Subcase 1 < t, E4 = e35)**:
When `0 < ρ0 * kJ` and weak 2-high fails strictly at base `e35 = x 3 - x 5`.
- Views: `u_ε = (x 3 - x 5) + ε • (x 5 - x 0)` in `J0` for small `ε > 0`.
- Rim: 6 4 5 2, chord 4 -> 5, middles 0, 3, farther w ∈ {2, 6}.
- Lemma K rules out 6-high everywhere on `J0`.
- Open condition `h2lo` rules out 2-high near `e35`. -/
theorem q45_Kminus_t_gt_one_j0ww {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha35 : ⟪F.N 5, x 3 - x 5⟫ < 0)
    (s t : ℝ)
    (hs0 : 0 < s)
    (ht : 0 < t)
    (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hk : 0 < det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1))
    (ht1 : 1 < t)
    (h2lo : min ⟪x 4, x 3 - x 5⟫ ⟪x 2, x 3 - x 5⟫ < max ⟪x 6, x 3 - x 5⟫ ⟪x 5, x 3 - x 5⟫)
    (P : ℝ³ → Prop) (hP : ∀ᶠ ε in 𝓝[>] (0 : ℝ), P ((x 3 - x 5) + ε • (x 5 - x 0))) :
    ∃ (u : ℝ³) (ρ : ℝ), ⟪F.N 3, u⟫ = 0 ∧ J0ExtraW F u ∧ (∃ ε : ℝ, u = (x 3 - x 5) + ε • (x 5 - x 0)) ∧
      (∀ a c : Fin 7, (0 < ⟪x a - x c, x 3 - x 5⟫ ∨ (⟪x a - x c, x 3 - x 5⟫ = 0 ∧ 0 < ⟪x a - x c, x 5 - x 0⟫)) →
        ⟪x c, u⟫ < ⟪x a, u⟫) ∧
      ((∀ i j : ZMod 4, i ≠ j →
        ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 3 - x 5⟫ ≠ 0 ∨
        ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 5 - x 0⟫ ≠ 0) → J0Chord F u ρ) ∧
      J0Tests F u ρ ∧ P u := by
  set p_quad := quad (x 6) (x 4) (x 5) (x 2)
  set r : ZMod 4 → Fin 7 := quad 6 4 5 2
  have hr : ∀ i : ZMod 4, x (r i) = p_quad i := by
    intro i; fin_cases i <;> rfl
  set b := x 3 - x 5
  set d := x 5 - x 0
  have hu_Pi : ∀ ε : ℝ, b + ε • d = u_Pi x (t - 1 + ε) s := by
    intro ε; ext j
    have hdj := congr_arg (fun (v : ℝ³) => v j) hdecomp
    dsimp [b, d, u_Pi, e4, e5, e35] at hdj ⊢
    linear_combination hdj
  have ev_eps : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have ev_alpha : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < t - 1 + ε := by
    have := eventually_pos_affine (A := t - 1) (B := 1) (Or.inl (by linarith [ht1]))
    filter_upwards [this] with ε hε; linarith
  have ev_8 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < (t - 1 + ε) * (1 - s) + s * t := by
    have hA : 0 < (t - 1) * (1 - s) + s * t := by linarith [hst]
    have := eventually_pos_affine (A := (t - 1) * (1 - s) + s * t) (B := 1 - s) (Or.inl hA)
    filter_upwards [this] with ε hε
    have : (t - 1 + ε) * (1 - s) + s * t = (t - 1) * (1 - s) + s * t + ε * (1 - s) := by ring
    rw [this]; exact hε
  have ev_N5 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ⟪F.N 5, b + ε • d⟫ < 0 := by
    have hlin : ∀ ε : ℝ, ⟪F.N 5, b + ε • d⟫ = ⟪F.N 5, b⟫ + ε * ⟪F.N 5, d⟫ := by
      intro ε; rw [inner_add_right, real_inner_smul_right]
    have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < - ⟪F.N 5, b⟫ + ε * (- ⟪F.N 5, d⟫) :=
      eventually_pos_affine (A := - ⟪F.N 5, b⟫) (B := - ⟪F.N 5, d⟫) (Or.inl (by linarith [ha35]))
    filter_upwards [hpos] with ε hε
    rw [hlin]; linarith
  have ev_2lo : ∀ᶠ ε in 𝓝[>] (0 : ℝ), min ⟪p_quad 1, b + ε • d⟫ ⟪p_quad 3, b + ε • d⟫ < max ⟪p_quad 0, b + ε • d⟫ ⟪p_quad 2, b + ε • d⟫ :=
    eventually_min13_lt_max02 p_quad b d h2lo
  have ev_inj : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (∀ i j : ZMod 4, i ≠ j → ⟪p_quad i - p_quad j, b⟫ ≠ 0 ∨
      ⟪p_quad i - p_quad j, d⟫ ≠ 0) → Function.Injective (fun i => ⟪p_quad i, b + ε • d⟫) := by
    by_cases hS2 : ∀ i j : ZMod 4, i ≠ j → ⟪p_quad i - p_quad j, b⟫ ≠ 0 ∨ ⟪p_quad i - p_quad j, d⟫ ≠ 0
    · filter_upwards [eventually_injective_quad p_quad b d hS2] with ε hε _ using hε
    · exact Eventually.of_forall fun ε h => absurd h hS2
  have ev_lex : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ a c : Fin 7,
      (0 < ⟪x a - x c, b⟫ ∨ (⟪x a - x c, b⟫ = 0 ∧ 0 < ⟪x a - x c, d⟫)) → ⟪x c, b + ε • d⟫ < ⟪x a, b + ε • d⟫ := by
    refine eventually_all.mpr fun a => eventually_all.mpr fun c => ?_
    by_cases hlx : 0 < ⟪x a - x c, b⟫ ∨ (⟪x a - x c, b⟫ = 0 ∧ 0 < ⟪x a - x c, d⟫)
    · filter_upwards [eventually_pos_affine hlx] with ε hε _
      have hl : ⟪x a, b + ε • d⟫ - ⟪x c, b + ε • d⟫ = ⟪x a - x c, b⟫ + ε * ⟪x a - x c, d⟫ := by
        rw [← inner_sub_left, inner_add_right, real_inner_smul_right]
      linarith
    · exact Eventually.of_forall fun ε h' => absurd h' hlx
  have ev_all := ev_eps.and (ev_alpha.and (ev_8.and (ev_N5.and (ev_2lo.and (ev_inj.and (ev_lex.and hP))))))
  obtain ⟨ε, hε, hα, h8, hN5_u, h2lo_u, hinj_u, hlex_u, hP_u⟩ := ev_all.exists
  set u := b + ε • d
  have hu_Pi_eq : u = u_Pi x (t - 1 + ε) s := hu_Pi ε
  have h6 : 0 < (t - 1 + ε) * s + s * (1 - t) := by
    have : (t - 1 + ε) * s + s * (1 - t) = ε * s := by ring
    rw [this]; exact mul_pos hε hs0
  have hN5_Pi : ⟪F.N 5, u_Pi x (t - 1 + ε) s⟫ < 0 := by rw [← hu_Pi_eq]; exact hN5_u
  have hsigns := lemma_signs_J0 F s t (t - 1 + ε) s hs0 ht hst hdecomp hα hs0 h8 h6 hN5_Pi
  rw [← hu_Pi_eq] at hsigns
  have hN3 : ⟪F.N 3, u⟫ = 0 := hsigns.1
  have hN2 : ⟪F.N 2, u⟫ < 0 := hsigns.2.1
  have hN4 : ⟪F.N 4, u⟫ < 0 := hsigns.2.2.1
  have hN5 : ⟪F.N 5, u⟫ < 0 := hsigns.2.2.2.1
  have hN6 : 0 < ⟪F.N 6, u⟫ := hsigns.2.2.2.2.1
  have hN7 : 0 < ⟪F.N 7, u⟫ := hsigns.2.2.2.2.2.1
  have hN8 : 0 < ⟪F.N 8, u⟫ := hsigns.2.2.2.2.2.2
  obtain ⟨ρ, hρ_ne, hcyc, hin⟩ := lemmaR_quad_signs F hN3 hN2 hN4 hN5 hN6 hN7 hN8
  have hin3 := hin 3
  have h3_eq : quad (x 6) (x 4) (x 5) (x 2) (3 + 1) - quad (x 6) (x 4) (x 5) (x 2) 3 = x 6 - x 2 := by
    show quad (x 6) (x 4) (x 5) (x 2) 0 - quad (x 6) (x 4) (x 5) (x 2) 3 = x 6 - x 2
    rfl
  have h3_1 : x 1 - quad (x 6) (x 4) (x 5) (x 2) 3 = x 1 - x 2 := by
    show x 1 - quad (x 6) (x 4) (x 5) (x 2) 3 = x 1 - x 2
    rfl
  rw [h3_eq, h3_1] at hin3
  have h_rho_om := rho_mul_omega_pos_of_inner_neg F u ρ hin3 hN5
  set Ω := det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1)
  have h_om_ne := omega_ne_zero F
  have h_om_sq : 0 < Ω ^ 2 := sq_pos_of_ne_zero h_om_ne
  have hkap := kappa_rim6452 x
  have h_om_kap : Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1) < 0 := by
    dsimp [p_quad]
    rw [hkap]
    linarith [hk]
  have hk_neg : ρ * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1) < 0 := by
    have hprod : (ρ * Ω) * (Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) < 0 :=
      mul_neg_of_pos_of_neg h_rho_om h_om_kap
    have : (ρ * Ω) * (Ω * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) =
        Ω ^ 2 * (ρ * det3 (p_quad 2 - p_quad 0) (p_quad 3 - p_quad 1) (p_quad 0 - p_quad 1)) := by ring
    rw [this] at hprod
    exact neg_of_mul_neg_right hprod h_om_sq.le
  have h_triD (i : ZMod 4) : 0 < ρ * triD p_quad u i := by
    have hneq1 : (i + 2 : ZMod 4) ≠ i := by
      intro h
      have : (2 : ZMod 4) = 0 := by
        calc (2 : ZMod 4) = (i + 2) - i := by ring
        _ = i - i := by rw [h]
        _ = 0 := sub_self i
      revert this; decide
    have hneq2 : (i + 2 : ZMod 4) ≠ i + 1 := by
      intro h
      have : (1 : ZMod 4) = 0 := by
        calc (1 : ZMod 4) = (i + 2) - (i + 1) := by ring
        _ = (i + 1) - (i + 1) := by rw [h]
        _ = 0 := sub_self _
      revert this; decide
    exact hcyc i (i + 2) hneq1 hneq2
  have h_uni := fun hadj => unimodal_quad_Kminus_adj p_quad u ρ hadj h_triD hk_neg h2lo_u
  have h_mb := middle_bounds_J0 s t (t - 1 + ε) s hst hα hs0 h8 h6
  set a : ZMod 4 := 1
  have hr' : ∀ i : ZMod 4, x (quad 6 4 5 2 i) = p_quad i := hr
  have hu0 : u ≠ 0 := fun h0 => by rw [h0, inner_zero_right] at hN2; exact lt_irrefl _ hN2
  have htests : J0Tests F u ρ := by
    refine ⟨hN3, hρ_ne, ?_, ?_, ?_⟩
    · intro i j hj1 hj2
      simp_rw [hr']
      exact hcyc i j hj1 hj2
    · intro q hqS hqr i
      have hq1 := exterior_vertices_J0 q hqS hqr
      subst hq1
      simp_rw [hr']
      exact hin i
    · intro q hqS hqr
      have hq03 := middle_vertices_J0 q hqS hqr
      have hra : x (r a) = x 4 := rfl
      have hra1 : x (r (a + 1)) = x 5 := rfl
      rw [hra, hra1]
      rcases hq03 with rfl | rfl
      · refine ⟨(t - 1 + ε) / ((t - 1 + ε) + s), - (1 / ((t - 1 + ε) + s)), h_mb.1.1, h_mb.1.2.1, h_mb.1.2.2, ?_⟩
        rw [hu_Pi_eq]
        exact middle_quad_x0 x (t - 1 + ε) s (by linarith [hα, hs0])
      · refine ⟨((1 - s) * (t - 1 + ε) + t * s) / ((t - 1 + ε) + s), (s + t - 1) / ((t - 1 + ε) + s), h_mb.2.1, h_mb.2.2.1, h_mb.2.2.2, ?_⟩
        rw [hu_Pi_eq]
        exact middle_quad_x3 x s t (t - 1 + ε) s hdecomp (by linarith [hα, hs0])
  refine ⟨u, ρ, hN3, ⟨⟨hN2, hN4, hN5, hN6, hN7, hN8⟩, h_uni, ?_, ?_⟩, ⟨ε, rfl⟩, hlex_u,
    fun hS2 => J0Chord.of_tests htests ?_ ?_, htests, hP_u⟩
  · have e0 := middle_quad_x0 x (t - 1 + ε) s (by linarith)
    rw [← hu_Pi_eq] at e0
    exact depth_lt_max_of_mid h_mb.1.1 h_mb.1.2.1 (neg_neg_of_pos (one_div_pos.mpr (by linarith))) hu0 e0
  · have e3 := middle_quad_x3 x s t (t - 1 + ε) s hdecomp (by linarith)
    rw [← hu_Pi_eq] at e3
    exact min_lt_depth_of_mid h_mb.2.1 h_mb.2.2.1 (div_pos (by linarith) (by linarith)) hu0 e3
  · simp_rw [hr']
    exact hinj_u hS2
  · simp_rw [hr']
    exact Or.inl (h_uni fun i h => zmod4_ne_succ i (hinj_u hS2 h))

/-- The weak core with the adjacent rim pairs off the S2 locus (`hS2a`): strictly unimodal rim depths. -/
theorem q45_Kminus_t_gt_one_j0w {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha35 : ⟪F.N 5, x 3 - x 5⟫ < 0)
    (s t : ℝ)
    (hs0 : 0 < s)
    (ht : 0 < t)
    (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hk : 0 < det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1))
    (ht1 : 1 < t)
    (h2lo : min ⟪x 4, x 3 - x 5⟫ ⟪x 2, x 3 - x 5⟫ < max ⟪x 6, x 3 - x 5⟫ ⟪x 5, x 3 - x 5⟫)
    (hS2a : ∀ i : ZMod 4,
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) (i + 1), x 3 - x 5⟫ ≠ 0 ∨
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) (i + 1), x 5 - x 0⟫ ≠ 0) :
    ∃ (u : ℝ³) (ρ : ℝ), ⟪F.N 3, u⟫ = 0 ∧ J0Extra F u ∧ (∃ ε : ℝ, u = (x 3 - x 5) + ε • (x 5 - x 0)) ∧
      (∀ a c : Fin 7, (0 < ⟪x a - x c, x 3 - x 5⟫ ∨ (⟪x a - x c, x 3 - x 5⟫ = 0 ∧ 0 < ⟪x a - x c, x 5 - x 0⟫)) →
        ⟪x c, u⟫ < ⟪x a, u⟫) ∧
      ((∀ i j : ZMod 4, i ≠ j →
        ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 3 - x 5⟫ ≠ 0 ∨
        ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 5 - x 0⟫ ≠ 0) → J0Chord F u ρ) := by
  obtain ⟨u, ρ, h3, ⟨hs, hU, h0, h3'⟩, hu, hlex, hc, -⟩ := q45_Kminus_t_gt_one_j0ww F
    ha35 s t hs0 ht hst hdecomp hk ht1 h2lo (fun _ => True) (Eventually.of_forall fun _ => trivial)
  exact ⟨u, ρ, h3, ⟨hs, hU (adj_of_lex hlex hS2a), h0, h3'⟩, hu, hlex, hc⟩

/-- The old form (full `hS2`): `J0Chord` and `J0Extra`. -/
theorem q45_Kminus_t_gt_one_j0 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (ha35 : ⟪F.N 5, x 3 - x 5⟫ < 0)
    (s t : ℝ)
    (hs0 : 0 < s)
    (ht : 0 < t)
    (hst : 1 < s + t)
    (hdecomp : x 3 - x 0 = s • (x 4 - x 0) + t • (x 5 - x 0))
    (hk : 0 < det3 (x 5 - x 6) (x 2 - x 6) (x 4 - x 6) * det3 (x 0 - x 1) (x 2 - x 1) (x 6 - x 1))
    (ht1 : 1 < t)
    (h2lo : min ⟪x 4, x 3 - x 5⟫ ⟪x 2, x 3 - x 5⟫ < max ⟪x 6, x 3 - x 5⟫ ⟪x 5, x 3 - x 5⟫)
    (hS2 : ∀ i j : ZMod 4, i ≠ j →
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 3 - x 5⟫ ≠ 0 ∨
      ⟪quad (x 6) (x 4) (x 5) (x 2) i - quad (x 6) (x 4) (x 5) (x 2) j, x 5 - x 0⟫ ≠ 0) :
    ∃ (u : ℝ³) (ρ : ℝ), J0Chord F u ρ ∧ J0Extra F u := by
  obtain ⟨u, ρ, -, hx, -, -, hc⟩ := q45_Kminus_t_gt_one_j0w F ha35 s t hs0 ht hst hdecomp hk ht1 h2lo
    (fun i => hS2 i (i + 1) (zmod4_ne_succ i))
  exact ⟨u, ρ, hc hS2, hx⟩

/-- The far pair `6`, `2` of the J0 rim is off the chord `4 5` in the segment sense: both strictly on one side of
the line `4 5` (in the plane of 0345, along `N3`), or `4`, `5` strictly on one side of the line `6 2`.  Its failure
`¬ J0PairOff F` means that the projection of the segment `[x 6, x 2]` along `N3` meets the chord `[x 4, x 5]`. -/
def J0PairOff {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  0 < ⟪F.N 3, cross (x 5 - x 4) (x 6 - x 4)⟫ * ⟪F.N 3, cross (x 5 - x 4) (x 2 - x 4)⟫ ∨
    0 < ⟪F.N 3, cross (x 2 - x 6) (x 4 - x 6)⟫ * ⟪F.N 3, cross (x 2 - x 6) (x 5 - x 6)⟫

/-- **The J0 chord with a far pair.**  The J0 chord data and the far pair `6`, `2` off the chord give Rupert, with
no hypothesis on `f3(x2)` vs `f3(x6)` (`isRupert_faceChord_fac_pair`, far pair = rim positions `0`, `3`). -/
theorem isRupert_of_j0Chord {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {u : ℝ³} {ρ : ℝ} (h : J0Chord F u ρ)
    (hoff : J0PairOff F) : IsRupert (univ.image x) := by
  obtain ⟨hnu, hρ, hcyc, hin, hmid, hinj, hz⟩ := h
  exact isRupert_faceChord_fac_pair F 3 hnu (k := 4) (by decide) (quad 6 4 5 2) (a := 1) (by decide) (by decide)
    hρ hcyc hin hmid hinj hz (w := 0) (w' := 3) (by decide) (by decide)
    (fun m h1 h2 h3 => absurd h3 (by revert m h1 h2; decide)) hoff

/-- **The J0 chord with the farther vertex** (the end of `q45_*` in Q45J0.lean): `J0Chord`, no tie `f3(x2) ≠ f3(x6)`
and the farther vertex's foot off the chord give the face chord. -/
theorem faceChordView_of_j0Chord {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {u : ℝ³} {ρ : ℝ} (h : J0Chord F u ρ)
    (hS3 : F.f 3 (x 2) ≠ F.f 3 (x 6))
    (hS4 : ⟪F.N 3, cross (x 5 - x 4) (x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4)⟫ ≠ 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 4, x 5 - x 4⟫ < 0 ∨
           ⟪x (if F.f 3 (x 2) < F.f 3 (x 6) then 2 else 6) - x 5, x 4 - x 5⟫ < 0) :
    FaceChordView F 3 := by
  obtain ⟨hnu, hρ, hcyc, hin, hmid, hinj, hz⟩ := h
  refine ⟨u, 4, inferInstance, quad 6 4 5 2, 1, if F.f 3 (x 2) < F.f 3 (x 6) then 3 else 0, ρ, hnu, by decide,
    by decide, by decide, hρ, hcyc, hin, hmid, hinj, hz, ?_, ?_, ?_⟩
  · split_ifs <;> decide
  · intro m hmw hmS
    split_ifs at hmw ⊢ with h26
    · rcases w_candidates_J0 m hmS with rfl | rfl
      · show F.f 3 (x 2) < F.f 3 (x 6); exact h26
      · exact False.elim (hmw rfl)
    · rcases w_candidates_J0 m hmS with rfl | rfl
      · exact False.elim (hmw rfl)
      · show F.f 3 (x 6) < F.f 3 (x 2)
        exact lt_of_le_of_ne (not_lt.mp h26) hS3.symm
  · split_ifs at hS4 ⊢ with h26
    · exact hS4
    · exact hS4

/-- **J0 chord, either far condition**: the farther vertex (no tie, foot off the chord) or the far pair. -/
theorem isRupert_of_j0Chord' {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {u : ℝ³} {ρ : ℝ} (h : J0Chord F u ρ)
    (hoff : ¬ (F.f 3 (x 2) = F.f 3 (x 6) ∨ Q45S4LocusJ0 F) ∨ J0PairOff F) : IsRupert (univ.image x) := by
  rcases hoff with h1 | h2
  · rw [not_or] at h1
    exact Minimality.FaceChord.isRupert_of_faceChordView F
      (faceChordView_of_j0Chord F h h1.1 (not_not.mp h1.2))
  · exact isRupert_of_j0Chord F h h2

/-! ### The J0 chord with a depth-separated pair (job OSPEC7)

On an ADJACENT S2 pair (`5 2` or `6 4` orthogonal to the face plane) the two rim vertices tie at every view of the
face circle near the core base, so `J0Chord` (injective rim depths) fails.  The depth-separated branch of the slide
(`isRupert_faceChord_fac_pair_ds`) tolerates the tie when the pair `[2, 6]`, corner `4` (tie `5 2`) resp. corner `5`
(tie `6 4`) separates the depths: the tied pair then lies on one side of the corner's depth.  The far feature is
handled by `J0FarOff`: the far pair off the chord, or a strictly farther vertex off the line `4 5` (on the tie `5 2`
the projection of `2` along `N3` IS `5`, so only the farther vertex `6` can work, and symmetrically). -/

/-- The far condition of the J0 chord in the `χ` form (`χ(q) = ⟪N3, (x5 - x4) × (xq - x4)⟫`): the far pair `6`, `2`
off the chord (`J0PairOff`), or a strictly farther one of `2`, `6` (smaller `f3`) with `χ ≠ 0`. -/
def J0FarOff {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) : Prop :=
  J0PairOff F ∨ (F.f 3 (x 2) < F.f 3 (x 6) ∧ ⟪F.N 3, cross (x 5 - x 4) (x 2 - x 4)⟫ ≠ 0) ∨
    (F.f 3 (x 6) < F.f 3 (x 2) ∧ ⟪F.N 3, cross (x 5 - x 4) (x 6 - x 4)⟫ ≠ 0)

/-- A depth-separated pair of the J0 rim `6 4 5 2` at every view `B + ε D` with small `ε > 0`. -/
def J0DSEv (x : Fin 7 → ℝ³) (B D : ℝ³) : Prop :=
  ∃ a c : ZMod 4, ∀ᶠ ε in 𝓝[>] (0 : ℝ), DepthSepAt (fun i => x (quad 6 4 5 2 i)) (B + ε • D) a c

theorem J0DSEv.eventually {x : Fin 7 → ℝ³} {B D : ℝ³} (h : J0DSEv x B D) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ a c : ZMod 4, DepthSepAt (fun i => x (quad 6 4 5 2 i)) (B + ε • D) a c := by
  obtain ⟨a, c, h⟩ := h
  exact h.mono fun ε hε => ⟨a, c, hε⟩

/-- **The J0 chord with a depth-separated pair.**  The rim tests of the J0 chord at `u`, a `DepthSepAt` pair of the
rim `6 4 5 2` at `u` (rim depths may tie) and `J0FarOff` give Rupert. -/
theorem isRupert_of_j0Tests_ds {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {u : ℝ³} {ρ : ℝ} (h : J0Tests F u ρ)
    (hds : ∃ a c : ZMod 4, DepthSepAt (fun i => x (quad 6 4 5 2 i)) u a c) (hoff : J0FarOff F) :
    IsRupert (univ.image x) := by
  obtain ⟨hnu, hρ, hcyc, hin, hmid⟩ := h
  rcases hoff with hoff | ⟨h26, hc⟩ | ⟨h62, hc⟩
  · exact isRupert_faceChord_fac_pair_ds F 3 hnu (k := 4) (by decide) (quad 6 4 5 2) (a := 1) (by decide)
      (by decide) hρ hcyc hin hmid hds (w := 0) (w' := 3) (by decide) (by decide)
      (fun m h1 h2 h3 => absurd h3 (by revert m h1 h2; decide)) hoff
  · refine isRupert_faceChord_fac_pair_ds F 3 hnu (k := 4) (by decide) (quad 6 4 5 2) (a := 1) (by decide)
      (by decide) hρ hcyc hin hmid hds (w := 3) (w' := 3) (by decide) (by decide) ?_ (Or.inl (mul_self_pos.mpr hc))
    intro m h1 _ h3
    have hm : m = 0 := by revert m h1 h3; decide
    subst hm
    rw [min_self]
    exact h26
  · refine isRupert_faceChord_fac_pair_ds F 3 hnu (k := 4) (by decide) (quad 6 4 5 2) (a := 1) (by decide)
      (by decide) hρ hcyc hin hmid hds (w := 0) (w' := 0) (by decide) (by decide) ?_ (Or.inl (mul_self_pos.mpr hc))
    intro m h1 _ h3
    have hm : m = 3 := by revert m h1 h3; decide
    subst hm
    rw [min_self]
    exact h62

end Minimality.T24.Q45
