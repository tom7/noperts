module

public import Minimality.FaceChordFac
public import Minimality.LexCell
public import Minimality.SplitLeaf

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset

namespace Minimality.Gen

open Minimality Minimality.H21 Minimality.FaceChord Minimality.LexCell Minimality.Split

/-- Generic `FaceChordView` on any facet of an `S0xFac` solid. -/
def AnyFaceChord {N nf : ℕ} {S : Fin nf → Finset (Fin N)} {x : Fin N → ℝ³}
    (F : S0xFac nf S x) : Prop :=
  ∃ t : Fin nf, FaceChordView F t

/-- Every generic `FaceChordView` on any facet of an `S0xFac` solid yields `IsRupert`. -/
theorem anyFaceChord_isRupert {N nf : ℕ} {S : Fin nf → Finset (Fin N)} {x : Fin N → ℝ³}
    (F : S0xFac nf S x) (h : AnyFaceChord F) : IsRupert (univ.image x) := by
  rcases h with ⟨t, ht⟩
  exact isRupert_of_faceChordView F ht

/-- Generic lexicographic closed-cell leaf (`k ≥ 4`) for any `S0xFac` facet family. -/
def LexAny {m n : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) : Prop :=
  ∃ (k : ℕ) (_ : NeZero k) (c : ZMod k → Fin n) (U Dn : Finset (Fin m)) (b d1 d2 : ℝ³),
    4 ≤ k ∧ Function.Injective c ∧ S0xCycUD S c U Dn ∧
    (∀ t ∈ U, LexPos3 ⟪F.N t, b⟫ ⟪F.N t, d1⟫ ⟪F.N t, d2⟫) ∧
    (∀ t ∈ Dn, LexPos3 (-⟪F.N t, b⟫) (-⟪F.N t, d1⟫) (-⟪F.N t, d2⟫)) ∧
    RobUniLex (fun i => (⟪x (c i), b⟫, ⟪x (c i), d1⟫, ⟪x (c i), d2⟫))

/-- Every generic lexicographic closed-cell leaf (`k ≥ 4`) yields `IsRupert`. -/
theorem lexAny_isRupert {m n : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) (hx : Function.Injective x) (h : LexAny F) :
    IsRupert (univ.image x) := by
  rcases h with ⟨k, _, c, U, Dn, b, d1, d2, hk, hc, hcyc, hU, hD, hR⟩
  exact Minimality.LexCell.isRupert_of_lexCell hk F hx hc hcyc b d1 d2 hU hD hR

/-- Generic tope split-pair view (`k ≥ 3`) for any `S0xFac` facet family. -/
def SplitAny {m n : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) : Prop :=
  ∃ (k : ℕ) (_ : NeZero k) (c : ZMod k → Fin n) (pat : Fin m → Bool) (u v : ℝ³)
    (a cc : ZMod k) (σ : ℝ),
    3 ≤ k ∧ Function.Injective c ∧ S0xCycOK S c pat ∧ S0xFacOK F pat u v ∧
    cc ≠ a ∧ cc ≠ a + 1 ∧ SplitRows (fun i => x (c i)) u a cc σ

/-- Every generic tope split-pair view (`k ≥ 3`) yields `IsRupert`, given facet separation. -/
theorem splitAny_isRupert {m n : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}
    (F : S0xFac m S x) (hx : Function.Injective x)
    (hsep : ∀ i j : Fin n, j ≠ i → ∃ t : Fin m, i ∈ S t ∧ j ∉ S t)
    (h : SplitAny F) : IsRupert (univ.image x) := by
  rcases h with ⟨k, hne, c, pat, u, v, a, cc, σ, hk, hc, hcyc, hfac, hca, hca1, hrows⟩
  have := hne
  exact split_tope_rupert F hx (noBetween_of_fac F hsep) v hc hk hcyc hfac a cc σ hca hca1 hrows

end Minimality.Gen
