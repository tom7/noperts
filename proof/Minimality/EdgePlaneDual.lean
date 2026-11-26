module

public import Minimality.Type24HoleAtlas
public import Minimality.EdgePlaneRim4Level
public import Minimality.EdgePlaneLevel
public import Minimality.EdgePlaneLWrap
public import Minimality.Type24NoCoplanar
public import Minimality.Unimodal

/-!
# The Gordan (dual) form of the Edge-Plane leaf

Each row `(i, j)` (`i ≠ a`, `j ∈ {i, i + 1}`) of `Gen.EdgePlaneAny` is linear in `(α, μ, s)`:
`⟪epRow x lab w a p, !₂[α, μ, s]⟫`.  By convex separation (`geometric_hahn_banach_compact_closed`)
and Carathéodory (`eq_pos_convex_span_of_mem_convexHull`), a blocked edge (no `(α, μ, s)` makes
every row positive) has a dual Gordan certificate: at most `4` rows with strictly positive weights
whose weighted sum vanishes (`t.Nonempty`, `t.card ≤ 4`, `∀ p ∈ t, 0 < lam p`,
`∑ p ∈ t, lam p • epRow x lab w a p = 0`), so no motion of the Edge-Plane family satisfies them.

Main results (`Minimality.Split.Dual` and `Minimality.T24.Atlas`):
- `gordan_r3` and `not_exists_pos_of_gordan`: finite Gordan alternative in `ℝ³`.
- `epRow` and `inner_epRow`: Edge-Plane row vectors and linearity in `(α, μ, s)`.
- `edgePlaneAny_or_gordan`: every valid `(k, lab, w, a)` yields either `Gen.EdgePlaneAny x` or
  a `≤ 4`-row Gordan certificate.
- `holeLeaf_ep_gordan` and `hole24_ep_gordan`: at a `HoleLeaf` (resp. `Hole24`) point, the
  Gordan certificate exists for every valid `(k, lab, w, a)`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset

namespace Minimality.Split.Dual

/-- **Gordan's theorem in `ℝ³` (forward direction).**  If no `v : ℝ³` makes `0 < ⟪r i, v⟫` for all
`i : ι`, then `0` lies in the convex hull of `range r`, so by Carathéodory at most `4` vectors
`t : Finset ι` have strictly positive weights `lam : ι → ℝ` summing to `0`. -/
theorem gordan_r3 {ι : Type*} [Fintype ι] (r : ι → ℝ³)
    (h : ¬ ∃ v : ℝ³, ∀ i, 0 < ⟪r i, v⟫) :
    ∃ (t : Finset ι) (lam : ι → ℝ),
      t.Nonempty ∧ t.card ≤ 4 ∧ (∀ i ∈ t, 0 < lam i) ∧ ∑ i ∈ t, lam i • r i = 0 := by
  classical
  let A : Set ℝ³ := Set.range r
  have hA : IsCompact A := (Set.finite_range r).isCompact
  have hC : IsCompact (convexHull ℝ A) := isCompact_convexHull_of_isCompact hA
  have h0 : (0 : ℝ³) ∈ convexHull ℝ A := by
    by_contra hnot
    obtain ⟨φ, u, u', hφ, huu', hφ0⟩ := geometric_hahn_banach_compact_closed
      (convex_convexHull ℝ A) hC (convex_singleton 0) isClosed_singleton
      (Set.disjoint_singleton_right.mpr hnot)
    have hφneg : ∀ i : ι, φ (r i) < 0 := fun i => by
      have h1 := hφ (r i) (subset_convexHull ℝ A ⟨i, rfl⟩)
      have h2 := hφ0 0 rfl
      rw [map_zero] at h2
      linarith
    let v : ℝ³ := -((InnerProductSpace.toDual ℝ ℝ³).symm φ)
    apply h
    refine ⟨v, fun i => ?_⟩
    have hv : ⟪r i, v⟫ = -φ (r i) := by
      simp only [v, inner_neg_right]
      rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
    linarith [hφneg i]
  obtain ⟨κ, _, z, w, hzA, hind, hw0, hw1, hsum⟩ := eq_pos_convex_span_of_mem_convexHull h0
  have hne : Nonempty κ := by
    by_contra hemp
    rw [not_nonempty_iff] at hemp
    simp at hw1
  let f : κ → ι := fun j => (hzA ⟨j, rfl⟩).choose
  have hf_spec : ∀ j, r (f j) = z j := fun j => (hzA ⟨j, rfl⟩).choose_spec
  have hf_inj : Function.Injective f := fun j₁ j₂ heq =>
    hind.injective (by rw [← hf_spec j₁, ← hf_spec j₂, heq])
  let t : Finset ι := Finset.univ.image f
  let lam : ι → ℝ := fun i => if hi : ∃ j : κ, f j = i then w hi.choose else 0
  refine ⟨t, lam, ?_, ?_, ?_, ?_⟩
  · obtain ⟨j₀⟩ := hne
    exact ⟨f j₀, Finset.mem_image_of_mem f (Finset.mem_univ j₀)⟩
  · calc t.card ≤ Fintype.card κ := Finset.card_image_le.trans (by simp)
      _ ≤ Module.finrank ℝ ℝ³ + 1 :=
        hind.card_le_finrank_succ.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)
      _ = 4 := by simp
  · intro i hi
    rcases Finset.mem_image.mp hi with ⟨j, -, rfl⟩
    have hex : ∃ j', f j' = f j := ⟨j, rfl⟩
    simp only [lam, dite_eq_left hex]
    exact hw0 hex.choose
  · rw [Finset.sum_image (fun j₁ _ j₂ _ heq => hf_inj heq)]
    have hterm : ∀ j : κ, lam (f j) • r (f j) = w j • z j := fun j => by
      have hex : ∃ j', f j' = f j := ⟨j, rfl⟩
      simp only [lam, dite_eq_left hex, hf_spec j, hf_inj hex.choose_spec]
    simp_rw [hterm]
    exact hsum

/-- **Gordan's theorem in `ℝ³` (converse).**  Any nonempty finite positive-weight linear combination
summing to `0` excludes every `v : ℝ³` with `∀ i, 0 < ⟪r i, v⟫`. -/
theorem not_exists_pos_of_gordan {ι : Type*} (r : ι → ℝ³) (t : Finset ι) (lam : ι → ℝ)
    (ht : t.Nonempty) (hlam : ∀ i ∈ t, 0 < lam i) (hsum : ∑ i ∈ t, lam i • r i = 0) :
    ¬ ∃ v : ℝ³, ∀ i, 0 < ⟪r i, v⟫ := by
  rintro ⟨v, hv⟩
  have h0 : (0 : ℝ) = ∑ i ∈ t, lam i * ⟪r i, v⟫ := by
    have : ⟪∑ i ∈ t, lam i • r i, v⟫ = 0 := by rw [hsum, inner_zero_left]
    simpa [sum_inner, real_inner_smul_left] using this.symm
  have hpos : 0 < ∑ i ∈ t, lam i * ⟪r i, v⟫ :=
    Finset.sum_pos (fun i hi => mul_pos (hlam i hi) (hv i)) ht
  linarith

/-- The Edge-Plane row vector `(c_i, c_i * z_j, S_{i,j}) ∈ ℝ³` for edge `i = p.1.1 ≠ a` and
endpoint `j = if p.1.2 then i + 1 else i`, where `c_i = det3 (X (i+1) - X i) (X (a+1) - X a) w`,
`z_j = ⟪X j - X a, w⟫`, and `S_{i,j} = edgePlaneSpin X w a i j`. -/
noncomputable def epRow {n k : ℕ} (x : Fin n → ℝ³) (lab : ZMod k → Fin n) (w : ℝ³)
    (a : ZMod k) (p : {p : ZMod k × Bool // p.1 ≠ a}) : ℝ³ :=
  let X : ZMod k → ℝ³ := fun t => x (lab t)
  let i : ZMod k := p.1.1
  let j : ZMod k := if p.1.2 then i + 1 else i
  let c : ℝ := Split.det3 (X (i + 1) - X i) (X (a + 1) - X a) w
  let z : ℝ := ⟪X j - X a, w⟫
  let S : ℝ := Split.edgePlaneSpin X w a i j
  !₂[c, c * z, S]

/-- Linearity of the Edge-Plane row expression in `(α, μ, s)`. -/
theorem inner_epRow {n k : ℕ} (x : Fin n → ℝ³) (lab : ZMod k → Fin n) (w : ℝ³) (a : ZMod k)
    (p : {p : ZMod k × Bool // p.1 ≠ a}) (α μ s : ℝ) :
    ⟪epRow x lab w a p, !₂[α, μ, s]⟫ =
      (α + μ * ⟪x (lab (if p.1.2 then p.1.1 + 1 else p.1.1)) - x (lab a), w⟫) *
          Split.det3 (x (lab (p.1.1 + 1)) - x (lab p.1.1)) (x (lab (a + 1)) - x (lab a)) w +
        s * Split.edgePlaneSpin (fun t => x (lab t)) w a p.1.1
          (if p.1.2 then p.1.1 + 1 else p.1.1) := by
  simp only [epRow, Split.inner3]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- **Edge-Plane / Gordan alternative.**  For any valid strict-rim view `(k, lab, w, a)` with
`⟪X (a + 1) - X a, w⟫ ≠ 0`, either `Gen.EdgePlaneAny x` holds, or the edge `a` is blocked by a
Gordan certificate: at most `4` rows of `epRow` with strictly positive weights summing to `0`. -/
theorem edgePlaneAny_or_gordan {n k : ℕ} [NeZero k] (hk : 3 ≤ k) (x : Fin n → ℝ³)
    (lab : ZMod k → Fin n) (hinj : Function.Injective lab) (w : ℝ³)
    (hrim : Split.StrictRimN x w lab) (hhid : Split.HiddenInTriangles x w lab) (a : ZMod k)
    (hD : ⟪x (lab (a + 1)) - x (lab a), w⟫ ≠ 0) :
    Gen.EdgePlaneAny x ∨
      ∃ (t : Finset {p : ZMod k × Bool // p.1 ≠ a})
        (lam : {p : ZMod k × Bool // p.1 ≠ a} → ℝ),
        t.Nonempty ∧ t.card ≤ 4 ∧ (∀ p ∈ t, 0 < lam p) ∧
        ∑ p ∈ t, lam p • epRow x lab w a p = 0 := by
  by_cases hEP : Gen.EdgePlaneAny x
  · exact Or.inl hEP
  · right
    refine gordan_r3 (epRow x lab w a) ?_
    rintro ⟨v, hv⟩
    apply hEP
    refine ⟨k, inferInstance, lab, w, a, v 2, v 0, v 1, hk, hinj, hrim, hhid, hD, ?_⟩
    intro i j hia hj
    have hv' : v = !₂[v 0, v 1, v 2] := by
      ext m; fin_cases m <;> rfl
    rcases hj with hj | hj
    · rw [hj]
      have hrow := hv ⟨(i, false), hia⟩
      rw [hv', inner_epRow] at hrow
      simpa using hrow
    · rw [hj]
      have hrow := hv ⟨(i, true), hia⟩
      rw [hv', inner_epRow] at hrow
      simpa using hrow

end Minimality.Split.Dual

namespace Minimality.T24.Atlas

open Minimality Minimality.H21 Minimality.T24.SAT Minimality.RimCell Minimality.T24.HC

variable {x : Fin 7 → ℝ³} {F : S0xFac 9 s0x_S24 x}

/-- At a `HoleLeaf` point, every valid `(k, lab, w, a)` with `⟪X (a + 1) - X a, w⟫ ≠ 0` is
blocked by at most `4` Edge-Plane rows whose positive combination vanishes. -/
theorem holeLeaf_ep_gordan (h : HoleLeaf x F) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (lab : ZMod k → Fin 7) (hinj : Function.Injective lab) (w : ℝ³)
    (hrim : Split.StrictRimN x w lab) (hhid : Split.HiddenInTriangles x w lab) (a : ZMod k)
    (hD : ⟪x (lab (a + 1)) - x (lab a), w⟫ ≠ 0) :
    ∃ (t : Finset {p : ZMod k × Bool // p.1 ≠ a})
      (lam : {p : ZMod k × Bool // p.1 ≠ a} → ℝ),
      t.Nonempty ∧ t.card ≤ 4 ∧ (∀ p ∈ t, 0 < lam p) ∧
      ∑ p ∈ t, lam p • Split.Dual.epRow x lab w a p = 0 :=
  (Split.Dual.edgePlaneAny_or_gordan hk x lab hinj w hrim hhid a hD).resolve_left
    (holeLeaf_not_edgePlaneAny h)

/-- `Hole24` form of `holeLeaf_ep_gordan`: at a `Hole24` point, every valid `(k, lab, w, a)` with
`⟪X (a + 1) - X a, w⟫ ≠ 0` has a `≤ 4`-row Gordan certificate. -/
theorem hole24_ep_gordan (h : Hole24 x F) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (lab : ZMod k → Fin 7) (hinj : Function.Injective lab) (w : ℝ³)
    (hrim : Split.StrictRimN x w lab) (hhid : Split.HiddenInTriangles x w lab) (a : ZMod k)
    (hD : ⟪x (lab (a + 1)) - x (lab a), w⟫ ≠ 0) :
    ∃ (t : Finset {p : ZMod k × Bool // p.1 ≠ a})
      (lam : {p : ZMod k × Bool // p.1 ≠ a} → ℝ),
      t.Nonempty ∧ t.card ≤ 4 ∧ (∀ p ∈ t, 0 < lam p) ∧
      ∑ p ∈ t, lam p • Split.Dual.epRow x lab w a p = 0 :=
  holeLeaf_ep_gordan h.1 hk lab hinj w hrim hhid a hD

end Minimality.T24.Atlas
