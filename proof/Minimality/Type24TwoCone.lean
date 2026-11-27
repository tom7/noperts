module

public import Minimality.EdgePlaneSlope
public import Minimality.EdgePlaneHidden
public import Minimality.Type24SplitFamily
public import Minimality.Type24LexEP

/-!
# The `w_C` leaf and the `T_0` family leaf (`FL1`–`FL3`)

* `FL2`, `FL1`, `FL3` (the `T_0` family leaf, `wc_edgePlaneAny`, `holeLeaf_not_wc`, ...): deleted
  (11-27 pass 2); the `w_C` leaf and `T_0` family are now cells of `Type24Cell` (`wcCert_cellCert`).
  What remains are the shared helpers used by the cell translations.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset Filter
open scoped Topology
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.T24.M4
open Minimality.T24.HC Minimality.T24.SF Minimality.T24.DeepC

namespace Minimality.T24.TwoCone

/-! ## FL2: `T_0` family leaf -/

/-! ## FL1: `w_C` leaf -/

/-- The 5-rim `[0, 5, 2, 3, 6]` for the `w_C` cell. -/
def wcRim : ZMod 5 → Fin 7 := ![0, 5, 2, 3, 6]

theorem wcRim_inj : Function.Injective wcRim := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hij (by decide)

theorem wcRim_cyc : S0xCycUD s0x_S24 wcRim {3, 4, 6, 8} {0, 1, 2, 5, 7} := by
  decide

/-! ## FL3: Hole facts -/

/-! ## FM1: `π_24` twin of the `w_C` leaf -/

/-- `Gen.EdgePlaneAny` is preserved under the `Sym.pi24` vertex permutation. -/
theorem edgePlaneAny_of_comp_pi24 (x : Fin 7 → ℝ³)
    (h : Gen.EdgePlaneAny (x ∘ Sym.pi24)) : Gen.EdgePlaneAny x := by
  rcases h with ⟨k, hne, lab, w, a, s, α, μ, hk, hinj, hrim, hhid, hDw, hrows⟩
  let lab' : ZMod k → Fin 7 := fun i => Sym.pi24 (lab i)
  have hinj' : Function.Injective lab' := Sym.pi24.injective.comp hinj
  have hrim' : Split.StrictRimN x w lab' := by
    intro m i hm1 hm2
    let m' : Fin 7 := Sym.pi24.symm m
    have hm' : Sym.pi24 m' = m := Sym.pi24.apply_symm_apply m
    have h1 : m' ≠ lab i := fun h => hm1 (by rw [← hm']; exact congrArg Sym.pi24 h)
    have h2 : m' ≠ lab (i + 1) := fun h => hm2 (by rw [← hm']; exact congrArg Sym.pi24 h)
    simpa only [Function.comp_apply, hm', lab'] using hrim m' i h1 h2
  have hhid' : Split.HiddenInTriangles x w lab' := by
    have himg : univ.image (x ∘ Sym.pi24) = univ.image x := by
      ext y
      simp only [mem_image, mem_univ, true_and, Function.comp_apply]
      exact ⟨fun ⟨i, hi⟩ => ⟨Sym.pi24 i, hi⟩,
        fun ⟨i, hi⟩ => ⟨Sym.pi24.symm i, by simpa using hi⟩⟩
    intro m hm
    let m' : Fin 7 := Sym.pi24.symm m
    have hm' : Sym.pi24 m' = m := Sym.pi24.apply_symm_apply m
    have hmi : ∀ i, m' ≠ lab i := fun i h => hm i (by rw [← hm']; exact congrArg Sym.pi24 h)
    obtain ⟨p, hp, q, hq, r, hr, t1, t2, t3, t4⟩ := hhid m' hmi
    rw [himg] at hp hq hr
    simp only [Function.comp_apply, hm'] at t2 t3 t4
    exact ⟨p, hp, q, hq, r, hr, t1, t2, t3, t4⟩
  exact ⟨k, hne, lab', w, a, s, α, μ, hk, hinj', hrim', hhid', hDw, hrows⟩

/-! ## FM2: Packaged two-cone residue -/

/-- The `w_C` window and strict line-separation hypothesis at `w0 = capView x 1 0 cc`. -/
def WCCertAt (x : Fin 7 → ℝ³) (F : S0xFac 9 s0x_S24 x) (cc : ℝ) : Prop :=
  1 / omega5 x < cc ∧ cc < omega3 x ∧
  (∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
    0 < ⟪F.N t, x 6 - x 1⟫ → -⟪F.N t, x 0 - x 1⟫ / ⟪F.N t, x 6 - x 1⟫ < cc) ∧
  (∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
    ⟪F.N t, x 6 - x 1⟫ < 0 → cc < -⟪F.N t, x 0 - x 1⟫ / ⟪F.N t, x 6 - x 1⟫) ∧
  (∀ t ∈ ({3, 6, 8} : Finset (Fin 9)),
    ⟪F.N t, x 6 - x 1⟫ = 0 → 0 < ⟪F.N t, x 0 - x 1⟫) ∧
  ⟪x (wcRim (4 + 1)) - x (wcRim 4), capView x 1 0 cc⟫ ≠ 0 ∧
  (∀ i : ZMod 5, i ≠ 4 →
    Split.det3 (x (wcRim (i + 1)) - x (wcRim i))
      (x (wcRim (4 + 1)) - x (wcRim 4)) (capView x 1 0 cc) ≠ 0) ∧
  ∃ sh α' μ' : ℝ, (sh = 1 ∨ sh = -1) ∧
    (∀ i j : ZMod 5, i ≠ 4 → (j = i ∨ j = i + 1) →
      0 < Split.det3 (x (wcRim (i + 1)) - x (wcRim i))
          (x (wcRim (4 + 1)) - x (wcRim 4)) (capView x 1 0 cc) →
      (-sh * ⟪Split.Slope.linSpinVec (fun t => x (wcRim t)) 4 i j, capView x 1 0 cc⟫ /
          Split.det3 (x (wcRim (i + 1)) - x (wcRim i))
            (x (wcRim (4 + 1)) - x (wcRim 4)) (capView x 1 0 cc)) -
        μ' * ⟪x (wcRim j) - x (wcRim 4), capView x 1 0 cc⟫ < α') ∧
    (∀ p q : ZMod 5, p ≠ 4 → (q = p ∨ q = p + 1) →
      Split.det3 (x (wcRim (p + 1)) - x (wcRim p))
          (x (wcRim (4 + 1)) - x (wcRim 4)) (capView x 1 0 cc) < 0 →
      α' < (-sh * ⟪Split.Slope.linSpinVec (fun t => x (wcRim t)) 4 p q, capView x 1 0 cc⟫ /
          Split.det3 (x (wcRim (p + 1)) - x (wcRim p))
            (x (wcRim (4 + 1)) - x (wcRim 4)) (capView x 1 0 cc)) -
        μ' * ⟪x (wcRim q) - x (wcRim 4), capView x 1 0 cc⟫)

end Minimality.T24.TwoCone
