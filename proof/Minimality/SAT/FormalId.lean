module

public import Minimality.SATFormal

@[expose] public section

/-!
# Formal identities in the generator form: soundness for SAT rows

The generic, type-free half of the Lean bridge for formal identity clauses
(`nopert229/tools/satformal/`).  A *formal identity* is a list of integer weighted terms, each the
product of one or two *atoms* (real functions `Cfg → ℝ`, collected in a list `A`), whose weighted sum
vanishes on the admissible configurations `Adm`.  The generator proves the identity (by
`linear_combination` after expanding the atoms in the generators `bt`, `gm`); this file turns it into
the SAT clauses on the three valued signs (`zn_sound`).

* `FormalId Adm A ts`: the identity.
* `formalId_sound`: if `S i` is the three valued sign of atom `i` at `c`, then all clauses
  `znPos`/`znNeg` of the weighted product signs hold.  Products of two atoms need `GateOK`
  (the product gate of the encoder, `Sg3.mul3`).
* `dE`, `nF`, `bt`, `gm`: the generators the expansion lemmas are written in (differences, facet normals, point brackets `[0 a b e]` and Gram
  entries `Gamma(d_0p, d_0q)`).

`formalId_sound` subsumes `Minimality.SAT.Formal.formalP_sound`: take `Adm c := c.G.IsSymm`, the atom list
`A = ts.map (pval ...)` and every `j = none`; `FormalP` is kept for its users.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace
open Minimality.H29.SAT Minimality.SAT.Formal

namespace Minimality.SAT.FormalId

open Minimality (det3 cross)

/-! ### Generators of type 24 -/

/-- The difference `x_a - x_b`. -/
noncomputable def dE (c : Cfg) (a b : ℕ) : ℝ³ := c.x a - c.x b

/-- The facet normal `s * (x_b - x_a) x (x_e - x_a)` (`s = +-1` fixes the orientation). -/
noncomputable def nF (c : Cfg) (s : ℝ) (a b e : ℕ) : ℝ³ := s • cross (c.x b - c.x a) (c.x e - c.x a)

/-- The point bracket `[0 a b e] = det (x_a - x_0, x_b - x_0, x_e - x_0)`. -/
noncomputable def bt (c : Cfg) (a b e : ℕ) : ℝ := det3 (c.x a - c.x 0) (c.x b - c.x 0) (c.x e - c.x 0)

/-- The Gram entry `Gamma(d_0p, d_0q)`. -/
noncomputable def gm (c : Cfg) (p q : ℕ) : ℝ := ⟪c.x p - c.x 0, Gv c.G (c.x q - c.x 0)⟫

/-! ### The generic soundness theorem -/

/-- A weighted term: `w * A i` or `w * A i * A j`. -/
structure ITerm where
  w : ℤ
  i : ℕ
  j : Option ℕ

/-- The atom value (a missing index is `0`). -/
def aval (A : List (Cfg → ℝ)) (c : Cfg) (i : ℕ) : ℝ := (A.getD i (fun _ => 0)) c

/-- The unweighted product. -/
def ITerm.prod (A : List (Cfg → ℝ)) (c : Cfg) (t : ITerm) : ℝ :=
  match t.j with
  | none => aval A c t.i
  | some j => aval A c t.i * aval A c j

/-- The weighted value. -/
def ITerm.val (A : List (Cfg → ℝ)) (c : Cfg) (t : ITerm) : ℝ := (t.w : ℝ) * t.prod A c

/-- The three valued sign of the unweighted product. -/
def ITerm.sg (S : ℕ → S3) (t : ITerm) : S3 :=
  match t.j with
  | none => S t.i
  | some j => Minimality.H29.SAT.mul3 (S t.i) (S j)

/-- **A formal identity** on the admissible configurations `Adm`: the weighted products add to `0`. -/
def FormalId (Adm : Cfg → Prop) (A : List (Cfg → ℝ)) (ts : List ITerm) : Prop :=
  ∀ c, Adm c → (ts.map (ITerm.val A c)).sum = 0

/-- **Soundness of a formal identity** (subsumes `formalP_sound`): terms that are products of one or
two atoms.  If `S i` is the three valued sign of atom `i`, every clause `znPos`/`znNeg` of the weighted
product signs holds. -/
theorem formalId_sound {ρ : V → Bool} (hP : Proper ρ) (hG : GateOK ρ) {Adm : Cfg → Prop}
    {A : List (Cfg → ℝ)} {ts : List ITerm} (hF : FormalId Adm A ts) (c : Cfg) (hc : Adm c)
    (S : ℕ → S3) (hS : ∀ i, Sg3 ρ (S i) (aval A c i)) (k : Fin ts.length) :
    Holds ρ (znPos (fun m => scaleS (ts.get m).w ((ts.get m).sg S)) k) ∧
    Holds ρ (znNeg (fun m => scaleS (ts.get m).w ((ts.get m).sg S)) k) := by
  refine zn_sound _ (fun m => (ts.get m).val A c) (fun m => ?_) ?_ k
  · have hp : Sg3 ρ ((ts.get m).sg S) ((ts.get m).prod A c) := by
      unfold ITerm.sg ITerm.prod
      cases (ts.get m).j with
      | none => exact hS _
      | some j => exact Sg3.mul3 hP hG (hS _) (hS _)
    exact Sg3_scaleS hP _ hp
  · have := hF c hc
    rw [sum_get]; exact this

end Minimality.SAT.FormalId
