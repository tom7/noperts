module

public import Minimality.Type29CertTie
public import Minimality.Type29Bridge
public import Minimality.Type16Limit

@[expose] public section

/-!
# Type 29 outside the HDN set and codimension 2 (`FEWER-FACES-PROOFS.md` §28, §18.2, §21)

Every type-29 shape `K` of class K3a or K4a is a limit of shapes `K_n` off the affine special
positions of the cover (the polynomial genericity fields `K3Poly`, `K4Poly`, `K3C1Poly`,
`K4C1Poly`: all polynomials in the eight normal-form parameters), with the same tie as `K` at
the named views.  The cover (`NF29.cert29_K3a_all`, `NF29.cert29_K4a_all`) gives each `K_n` a
certificate `Cert29`; a subsequence carries one labelled certificate, and the limit lemma
(`isRupert_of_tendsto_rimCert`) makes `K` Rupert unless the limit view has a horizontal double
normal.  The route is that of type 16 (`Type16Limit.lean`).

* `nfShape29`, `ineq29`, `NF29.ofParams`: normal-form shapes from parameters.
* `genPoly29`: the product of the polynomial fields, a nonzero polynomial
  (`genPoly29_ne_zero`); `exists_seq_eval_ne_zero_fin`: the shapes off its zero set are dense.
* `restore`-shears (`Type16Limit`) restore one tie.
* `TieInst29`, `SameTie29`, **`OneTieGlobal29`**: ties at the named views; **at most one tie**
  (counting the tie of `s, t` along `ij` and the tie of `i, j` along `st` as one) is the
  codimension-2 condition.  `OneTieGlobal29.oneTie`: it implies the per-view `OneTie29`.
* `exists_certSeq29`, **`isRupert_type29_limit`**: a type-29 shape of class K3a or K4a with at
  most one tie at its named views and no horizontal double normal at them is Rupert.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### Shapes from parameters -/

/-! ### The polynomial genericity of the covers as one polynomial -/

section ofGen

variable {x : Fin 7 → ℝ³} (N : NF29 x)

end ofGen

/-! ### Named views in the limit -/

variable {x : Fin 7 → ℝ³}

/-! ### Ties at the named views -/

/-- Two ties that are one equation for every shape (`SameTieG`). -/
abbrev SameTie29 (v : View29) (s t : Fin 7) (v' : View29) (s' t' : Fin 7) : Prop :=
  SameTieG v s t v' s' t'

/-- One equation holds at every shape where the other does. -/
theorem SameTie29.inner_eq_zero {v : View29} {s t : Fin 7} {v' : View29} {s' t' : Fin 7}
    (h : SameTie29 v s t v' s' t') (y : Fin 7 → ℝ³) (h0 : ⟪y s - y t, view29 y v⟫ = 0) :
    ⟪y s' - y t', view29 y v'⟫ = 0 :=
  SameTieG.inner_eq_zero (fun _ _ _ => rfl) h y h0

/-! ### The limit certificate -/

/-- A labelled certificate at a named view, with 3, 4 or 5 corners. -/
def CertL29 (y : Fin 7 → ℝ³) (v : View29) (ε : Bool) :
    ((ZMod 3 → Fin 7) ⊕ (ZMod 4 → Fin 7) ⊕ (ZMod 5 → Fin 7)) → Prop :=
  Sum.elim (fun lab => RimCertAt y (sgnB ε • view29 y v) lab)
    (Sum.elim (fun lab => RimCertAt y (sgnB ε • view29 y v) lab)
      (fun lab => RimCertAt y (sgnB ε • view29 y v) lab))

/-- **Normalizing a certificate**: labels, a named view and a sign. -/
theorem Cert29.exists_certL {y : Fin 7 → ℝ³} (h : Cert29 y) :
    ∃ v ε L, CertL29 y v ε L := by
  obtain ⟨v, c, hc0, k, hk, z, hz⟩ := h.rimCert
  have hpos : 0 < |c|⁻¹ := inv_pos.mpr (abs_pos.mpr hc0)
  have hz' := hz.smul hpos
  rw [smul_smul] at hz'
  have hsg : |c|⁻¹ * c = sgnB (decide (0 < c)) := by
    rcases lt_or_gt_of_ne hc0 with h | h
    · rw [abs_of_neg h, sgnB, decide_eq_false (not_lt.mpr h.le)]
      field_simp; simp
    · rw [abs_of_pos h, sgnB, decide_eq_true h, inv_mul_cancel₀ h.ne']; simp
  rw [hsg] at hz'
  obtain ⟨lab, -, hat⟩ := hz'.toAt
  refine ⟨v, decide (0 < c), ?_⟩
  rcases hk with rfl | rfl | rfl
  · exact ⟨Sum.inl lab, hat⟩
  · exact ⟨Sum.inr (Sum.inl lab), hat⟩
  · exact ⟨Sum.inr (Sum.inr lab), hat⟩

end Minimality

end
