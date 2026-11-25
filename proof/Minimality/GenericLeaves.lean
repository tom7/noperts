module

public import Minimality.FaceChordFac
public import Minimality.LexCell
public import Minimality.SplitLeaf
public import Minimality.EdgePlane

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

/-- **Generic Edge-Plane view** (`k ≥ 3`) of a point family `x : Fin n → ℝ³` (any solid `univ.image x`; no
facet data is needed, the rim `lab` is a strict rim of the view `w` with every other point hidden in a projected
triangle).  The data are those of the Edge-Plane Lemma (`Minimality.Split.freeAt_of_edgePlane`): a rim edge
`a` with `⟪x (lab (a+1)) - x (lab a), w⟫ ≠ 0` and parameters `(s, α, μ)` such that every row (every other edge `i`
at each of its two ends `j`) is positive.  Such a view is first-order free.

Census (FREECERT 11-25, FACENORM24.md): at points of the hidden-cap cone with no Lex / Split / face-chord leaf,
free views exist and ALL are Edge-Plane views.  Every `SplitRows` view tested was also an Edge-Plane view (1624 of
1624 on a C-covered sample).  CONJECTURE (not proved): `SplitAny F → EdgePlaneAny x`, i.e. this leaf subsumes
`SplitAny`. -/
def EdgePlaneAny {n : ℕ} (x : Fin n → ℝ³) : Prop :=
  ∃ (k : ℕ) (_ : NeZero k) (lab : ZMod k → Fin n) (w : ℝ³) (a : ZMod k) (s α μ : ℝ),
    3 ≤ k ∧ Function.Injective lab ∧ StrictRimN x w lab ∧ HiddenInTriangles x w lab ∧
    ⟪x (lab (a + 1)) - x (lab a), w⟫ ≠ 0 ∧
    ∀ i j : ZMod k, i ≠ a → (j = i ∨ j = i + 1) →
      0 < (α + μ * ⟪x (lab j) - x (lab a), w⟫) *
          Split.det3 (x (lab (i + 1)) - x (lab i)) (x (lab (a + 1)) - x (lab a)) w +
        s * Split.edgePlaneSpin (fun i => x (lab i)) w a i j

/-- Every generic Edge-Plane view yields `IsRupert` (`FreeAt.isRupert`; `w ≠ 0` follows from the edge condition
`hD`).  No injectivity of `x`, no facets. -/
theorem edgePlaneAny_isRupert {n : ℕ} {x : Fin n → ℝ³} (h : EdgePlaneAny x) :
    IsRupert (univ.image x) := by
  rcases h with ⟨k, hne, lab, w, a, s, α, μ, hk, hinj, hrim, hhid, hD, hrows⟩
  have hw : w ≠ 0 := by
    rintro rfl
    simp at hD
  exact FreeAt.isRupert hw (freeAt_of_edgePlane hk x w lab hinj hrim hhid a s α μ hD hrows)

end Minimality.Gen
