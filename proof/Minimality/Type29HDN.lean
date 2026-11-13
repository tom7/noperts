module

public import Minimality.Type29Faces

@[expose] public section

/-!
# Type 29: the labelled closings and their limit (`FEWER-FACES-PROOFS.md` §22, §28)

The limit lemma of `Type29Limit.lean` makes a type-29 shape of class K3a or K4a Rupert unless the
limit rim has a horizontal double normal (HDN) at its named view.  Theorem 28.10 replaces "no HDN
at every named view" by codimension-2 exceptions, closing by closing.  This file sets up the
finitely many closings and the limit lemma for the two-triangle views.

* `Lab29`, `Lab29.Ok`, `Lab29.view`, `CertAt29`, `cert29_iff`: the closings of the whitelists and
  the certificate of one of them.
* `CertAt29.quad_at`, `quint_at`, `tri_at`, `epair_at`: a labelled rim certificate with a sign.
* `isRupert_of_certL_seq29_or`: Lemma 18.2 with "no HDN, or `Sec29`" (two triangles).
* `RimCertAt.rev4`, `rev3`: a rim read backwards at the opposite view.
* `NF29.params_eq`, `Ex29.lim`, `Ex29.lim_of_freq`: the region facts of a certificate at the
  limit (the normal form of a point set is unique; the inequalities are closed).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

variable {x : Fin 7 → ℝ³}

instance : Fintype Ex29 := ⟨{.none, .t1, .t1o, .t2, .t2o}, by intro e; cases e <;> decide⟩

/-- **A closing of the whitelists**: a four-corner rim (with its region tag), a five-corner rim, a
triangular rim, or an edge pair `(v, w, a, b, c)` of Lemma E. -/
abbrev Lab29 : Type :=
  (View29 × (Fin 7 × Fin 7 × Fin 7 × Fin 7) × Ex29) ⊕
    (View29 × (Fin 7 × Fin 7 × Fin 7 × Fin 7 × Fin 7)) ⊕
    (View29 × (Fin 7 × Fin 7 × Fin 7) × Ex29) ⊕ (Fin 7 × Fin 7 × Fin 7 × Fin 7 × Fin 7)

/-- The closings that occur in the covers (`quadLabels29`, …, `ePairLabels29`). -/
def Lab29.Ok : Lab29 → Prop
  | .inl q => q ∈ quadLabels29
  | .inr (.inl q) => q ∈ quintLabels29
  | .inr (.inr (.inl q)) => q ∈ triLabels29
  | .inr (.inr (.inr q)) => q ∈ ePairLabels29

/-- The named view of a closing (an edge pair lives at the segment `v w`). -/
def Lab29.view : Lab29 → View29
  | .inl q => q.1
  | .inr (.inl q) => q.1
  | .inr (.inr (.inl q)) => q.1
  | .inr (.inr (.inr q)) => .inl (q.1, q.2.1)

/-! ### Labelled rims with a sign -/

/-- **A rim certificate at `c • w`, `c ≠ 0`, is one at `sgnB ε • w`** (positive scaling). -/
theorem RimCertPts.sgn {k : ℕ} {V : Finset ℝ³} {w : ℝ³} {Y : ZMod k → ℝ³} {c : ℝ} (hc : c ≠ 0)
    (h : RimCertPts V (c • w) Y) : ∃ ε : Bool, RimCertPts V (sgnB ε • w) Y := by
  have hpos : 0 < |c|⁻¹ := inv_pos.mpr (abs_pos.mpr hc)
  have hz' := h.smul hpos
  rw [smul_smul] at hz'
  have hsg : |c|⁻¹ * c = sgnB (decide (0 < c)) := by
    rcases lt_or_gt_of_ne hc with h | h
    · rw [abs_of_neg h, sgnB, decide_eq_false (not_lt.mpr h.le)]
      field_simp; simp
    · rw [abs_of_pos h, sgnB, decide_eq_true h, inv_mul_cancel₀ h.ne']; simp
  rw [hsg] at hz'
  exact ⟨_, hz'⟩

/-! ### Lemma 18.2 with a tilt alternative -/

/-! ### Reversing a rim -/

theorem IsRobustUnimodal.reflect {k : ℕ} {z : ZMod k → ℝ} (hz : IsRobustUnimodal z) :
    IsRobustUnimodal (fun i => z (-i)) where
  noPeaks B a b c d hab hbc hcd hdk h := by
    have e : ∀ x : ℕ, x ≤ d →
        -(B + (x : ZMod k)) = (-B - (d : ZMod k)) + ((d - x : ℕ) : ZMod k) := by
      intro x hx; rw [Nat.cast_sub hx]; ring
    have ea := e a (by omega)
    have eb := e b (by omega)
    have ec := e c (by omega)
    have ed := e d le_rfl
    simp only [Nat.sub_self, Nat.cast_zero, add_zero] at ed
    simp only [ea, eb, ec, ed] at h
    refine hz.noPeaks' (-B - (d : ZMod k)) (a := 0) (b := d - c) (c := d - b) (d := d - a)
      (by omega) (by omega) (by omega) (by omega) ?_
    simp only [Nat.cast_zero, add_zero]
    obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨h4, h2, h3, h1⟩
  noTriple i j l hij hjl hil e1 e2 := hz.noTriple (-i) (-j) (-l) (neg_injective.ne hij)
    (neg_injective.ne hjl) (neg_injective.ne hil) e1 e2
  noLevelRun B a b c d hab hbc hcd hdk e := by
    have eq : ∀ x : ℕ, x ≤ d →
        -(B + (x : ZMod k)) = (-B - (d : ZMod k)) + ((d - x : ℕ) : ZMod k) := by
      intro x hx; rw [Nat.cast_sub hx]; ring
    have ea := eq a (by omega)
    have eb := eq b (by omega)
    have ec := eq c (by omega)
    have ed := eq d le_rfl
    simp only [Nat.sub_self, Nat.cast_zero, add_zero] at ed
    simp only [ea, eb, ec, ed] at e ⊢
    have := hz.noLevelRun (-B - (d : ZMod k)) 0 (d - c) (d - b) (d - a) (by omega) (by omega)
      (by omega) (by omega) e.symm
    try simp only [Nat.cast_zero, add_zero] at this
    exact ⟨fun h => this.2 ⟨h.2, h.1⟩, fun h => this.1 ⟨h.2, h.1⟩⟩

/-! ### The region facts at the limit -/

/-- **The closed region facts of a certificate, at the limit** (in the parameters of `x`): the
facts `Ex29.facts` of the approximants `K_n`, in the limit. -/
def Ex29.lim {x : Fin 7 → ℝ³} (N : NF29 x) : Ex29 → Prop
  | .none => True
  | .t1 => (0 ≤ -N.a2 * N.t + N.b2 * N.s ∧ N.h2 ≤ 1) ∧
      0 ≤ ⟪view29 x (.inr 0), view29 x (.inr 1)⟫
  | .t1o => (0 ≤ -N.a2 * N.t + N.b2 * N.s ∧ 1 ≤ N.h2) ∧
      ⟪view29 x (.inr 0), view29 x (.inr 3)⟫ ≤ 0
  | .t2 => N.h0 ≤ N.h2 ∧ N.h2 ≤ 1
  | .t2o => N.h0 ≤ 1 ∧ 1 ≤ N.h2

end Minimality

end
