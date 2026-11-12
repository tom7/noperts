module

public import Minimality.Type24SAT.FacLink24
public import Minimality.Type29SAT.Mir

@[expose] public section

/-!
# Type 24, mirror orientation: reflection `mir = diag(1,1,-1)` and the literal signs

For `x' = mir ∘ x` (Type29SAT/Mir.lean):
- `val x' l = - val x l` for `br lv mv fc` (determinants / `⟪nrm, ·⟫`: `nrm x' = - mir (nrm x)`),
- `val x' l = val x l` for `nv kv` (two reflections cancel),
- `cv x' t v = - cv x t v`, and `det3 (…) ` of the chirality bracket flips.
So a mirror-oriented shape (hchir with the opposite sign, all `cv` negative) reflects to a reference-oriented one, and
a core literal `(l, s)` on `x'` reads `(l, epsL l * s)` on `x`, `epsL = -1` for `br lv mv fc`, `+1` for `nv kv`.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
open scoped RealInnerProductSpace

namespace Minimality.T24.SAT
open Minimality Minimality.H21 Minimality.H29.SAT

/-- The sign by which a literal's value changes under reflection. -/
def epsL : Lit24 → Int
  | .nv .. => 1
  | .kv .. => 1
  | _ => -1

theorem mir_smul (c : ℝ) (v : ℝ³) : mir (c • v) = c • mir v := by
  ext i; fin_cases i <;> simp [mir]

theorem det3_neg3 (a b c : ℝ³) : det3 (-a) (-b) (-c) = - det3 a b c := by
  simp only [det3_expand, PiLp.neg_apply]; ring

/-- The reflected configuration. -/
noncomputable def mirx (x : Nat → ℝ³) : Nat → ℝ³ := fun i => mir (x i)

theorem nrm_mir (x : Nat → ℝ³) (t : Nat) : nrm (mirx x) t = - mir (nrm x t) := by
  unfold nrm mirx
  rw [← mir_sub, ← mir_sub, mir_cross, mir_smul, smul_neg]

theorem val_mir (x : Nat → ℝ³) (l : Lit24) : val (mirx x) l = (epsL l : ℝ) * val x l := by
  cases l with
  | br a b c d => simp only [val, mirx, ← mir_sub, mir_det3, epsL]; push_cast; ring
  | lv a b c d e => simp only [val, mirx, ← mir_sub, mir_det3, epsL]; push_cast; ring
  | mv a b c d e f => simp only [val, mirx, ← mir_sub, mir_det3, epsL]; push_cast; ring
  | fc t p q =>
    simp only [val, epsL]
    rw [nrm_mir]; simp only [mirx, ← mir_sub, inner_neg_left, mir_inner]; push_cast; ring
  | nv r s t =>
    simp only [val, epsL]
    rw [nrm_mir, nrm_mir, nrm_mir, det3_neg3, mir_det3]; push_cast; simp
  | kv t a b c d =>
    simp only [val, epsL]
    rw [nrm_mir]; simp only [mirx, ← mir_sub, mir_cross, inner_neg_left, inner_neg_right, mir_inner]; push_cast; ring

theorem cv_mir (x : Nat → ℝ³) (t v : Nat) : cv (mirx x) t v = - cv x t v := by
  unfold cv
  rw [nrm_mir]; simp only [mirx, ← mir_sub, inner_neg_left, mir_inner]

theorem convex_mir (x : Nat → ℝ³) (h : ∀ p ∈ cvList, cv x p.1 p.2 < 0) : Convex24 (mirx x) := by
  intro p hp; rw [cv_mir]; linarith [h p hp]

theorem litHolds_mir (x : Nat → ℝ³) (l : Lit24) (s : Int) :
    LitHolds (mirx x) l s ↔ LitHolds x l (epsL l * s) := by
  unfold LitHolds
  rw [val_mir]; push_cast
  constructor <;> intro h <;> linarith

theorem ext_mir (y : Fin 7 → ℝ³) : ext (fun i => mir (y i)) = mirx (ext y) := by
  funext i; rfl

theorem hchir_mir (y : Fin 7 → ℝ³) (h : 0 < det3 (y 1 - y 0) (y 2 - y 0) (y 6 - y 0)) :
    det3 (mir (y 1) - mir (y 0)) (mir (y 2) - mir (y 0)) (mir (y 6) - mir (y 0)) < 0 := by
  rw [← mir_sub, ← mir_sub, ← mir_sub, mir_det3]; linarith

/-- `S0xFac` is preserved by reflection (`mirFac`); `Facets24`'s `S0xFac 9 s0x_S24 y` becomes one for `mir ∘ y`. -/
theorem mir_core_false (y : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 y)
    (hchir : 0 < det3 (y 1 - y 0) (y 2 - y 0) (y 6 - y 0)) (core : List (Lit24 × Int))
    (hf : ∀ (z : Fin 7 → ℝ³), S0xFac 9 s0x_S24 z → det3 (z 1 - z 0) (z 2 - z 0) (z 6 - z 0) < 0 →
        (∀ p ∈ core, LitHolds (ext z) p.1 p.2) → False)
    (hcore : ∀ p ∈ core, LitHolds (ext y) p.1 (epsL p.1 * p.2)) : False :=
  hf (fun i => mir (y i)) (mirFac F) (hchir_mir y hchir) (fun p hp => by
    rw [ext_mir, litHolds_mir]; exact hcore p hp)

theorem coreFalsePpmmm_mir (y : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 y)
    (hchir : 0 < det3 (y 1 - y 0) (y 2 - y 0) (y 6 - y 0))
    (hcore : ∀ p ∈ corePpmmm, LitHolds (ext y) p.1 (epsL p.1 * p.2)) : False :=
  mir_core_false y F hchir corePpmmm (fun z Fz hz hc => coreFalsePpmmm_fac z Fz hz hc) hcore

theorem coreFalsePpmpm_mir (y : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 y)
    (hchir : 0 < det3 (y 1 - y 0) (y 2 - y 0) (y 6 - y 0))
    (hcore : ∀ p ∈ corePpmpm, LitHolds (ext y) p.1 (epsL p.1 * p.2)) : False :=
  mir_core_false y F hchir corePpmpm (fun z Fz hz hc => coreFalsePpmpm_fac z Fz hz hc) hcore

theorem coreFalseMpmpm_mir (y : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 y)
    (hchir : 0 < det3 (y 1 - y 0) (y 2 - y 0) (y 6 - y 0))
    (hcore : ∀ p ∈ coreMpmpm, LitHolds (ext y) p.1 (epsL p.1 * p.2)) : False :=
  mir_core_false y F hchir coreMpmpm (fun z Fz hz hc => coreFalseMpmpm_fac z Fz hz hc) hcore

theorem coreFalseMpppm_mir (y : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 y)
    (hchir : 0 < det3 (y 1 - y 0) (y 2 - y 0) (y 6 - y 0))
    (hcore : ∀ p ∈ coreMpppm, LitHolds (ext y) p.1 (epsL p.1 * p.2)) : False :=
  mir_core_false y F hchir coreMpppm (fun z Fz hz hc => coreFalseMpppm_fac z Fz hz hc) hcore

theorem coreFalsePpmmm30_mir (y : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 y)
    (hchir : 0 < det3 (y 1 - y 0) (y 2 - y 0) (y 6 - y 0))
    (hcore : ∀ p ∈ corePpmmm30, LitHolds (ext y) p.1 (epsL p.1 * p.2)) : False :=
  mir_core_false y F hchir corePpmmm30 (fun z Fz hz hc => coreFalsePpmmm30_fac z Fz hz hc) hcore

#print axioms val_mir
#print axioms cv_mir
#print axioms coreFalseMpppm_mir
#print axioms coreFalsePpmmm_mir
#print axioms coreFalsePpmpm_mir
#print axioms coreFalseMpmpm_mir
#print axioms coreFalsePpmmm30_mir

end Minimality.T24.SAT
