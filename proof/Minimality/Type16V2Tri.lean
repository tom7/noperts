module

public import Minimality.Type16V2Core

@[expose] public section

/-!
# V2: triangle cells at the 11 vertex views of type 16 (affine hypotheses)

Facets `A..H` = indices `0..7` (`fIdx`); the 11 vertex views `(P, Q, w)` (`vtxPQW`).  `FreeTT` is the triangle cell:
for chosen far vertices `a ∈ P`, `b ∈ Q` and edge facets `eP ∋ w, a`, `eQ ∋ w, b`, every other vertex `j` is
* inside: `fQ(j) fP(b) + fP(j) fQ(a) < fQ(a) fP(b)` (off both facets), or
* on P (side point of ray P): `fQ(a) < fQ(j)`, and off `eP`; or on Q: `fP(b) < fP(j)`, off `eQ`.
All data are values of facet functions at the seven points (affine).  `DepthOK`: the depths of `w, a, b` along the
view direction are distinct.
-/

set_option autoImplicit true
set_option linter.unusedVariables false
open scoped RealInnerProductSpace
open Finset Filter

namespace Minimality
namespace V2
open Type08Sp Type08Sp.C2

theorem exists_kernel2 (N1 N2 : ℝ³) : ∃ r : ℝ³, r ≠ 0 ∧ ⟪N1, r⟫ = 0 ∧ ⟪N2, r⟫ = 0 := by
  let f : ℝ³ →ₗ[ℝ] ℝ × ℝ := (innerSL ℝ N1).toLinearMap.prod (innerSL ℝ N2).toLinearMap
  have h : Module.finrank ℝ (ℝ × ℝ) < Module.finrank ℝ ℝ³ := by
    simp [Module.finrank_prod]
  have := LinearMap.ker_ne_bot_of_finrank_lt (f := f) h
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot this
  refine ⟨r, hr0, ?_, ?_⟩
  · have := congrArg Prod.fst (LinearMap.mem_ker.1 hr); simpa [f] using this
  · have := congrArg Prod.snd (LinearMap.mem_ker.1 hr); simpa [f] using this

/-- The vertex sets of the facets `A = 0235, B = 1356, C = 024, D = 036, E = 046, F = 145, G = 146, H = 245`. -/
def fIdx : Fin 8 → Finset (Fin 7) :=
  ![{0, 2, 3, 5}, {1, 3, 5, 6}, {0, 2, 4}, {0, 3, 6}, {0, 4, 6}, {1, 4, 5}, {1, 4, 6}, {2, 4, 5}]

/-- The 11 vertex views: facets `P`, `Q` and the common vertex `w`. -/
def vtxPQW : Fin 11 → Fin 8 × Fin 8 × Fin 7 :=
  ![(0, 4, 0), (0, 5, 5), (1, 4, 6), (1, 7, 5), (2, 3, 0), (2, 5, 4), (2, 6, 4), (3, 6, 6), (4, 5, 4), (4, 7, 4),
    (6, 7, 4)]

theorem vtx_inter : ∀ t, fIdx (vtxPQW t).1 ∩ fIdx (vtxPQW t).2.1 = {(vtxPQW t).2.2} := by decide

variable {x : Fin 7 → ℝ³}

def _root_.Minimality.Type16.ff (T : Type16 x) : Fin 8 → ℝ³ → ℝ
  | 0 => T.q0235.f | 1 => T.q1356.f | 2 => T.t024.f | 3 => T.t036.f | 4 => T.t046.f | 5 => T.t145.f
  | 6 => T.t146.f | 7 => T.t245.f

def _root_.Minimality.Type16.fN (T : Type16 x) : Fin 8 → ℝ³
  | 0 => T.q0235.N | 1 => T.q1356.N | 2 => T.t024.N | 3 => T.t036.N | 4 => T.t046.N | 5 => T.t145.N
  | 6 => T.t146.N | 7 => T.t245.N

theorem ff_hN (T : Type16 x) (i : Fin 8) : ∀ y z, T.ff i y - T.ff i z = ⟪T.fN i, y - z⟫ := by
  fin_cases i
  · exact T.q0235.hN
  · exact T.q1356.hN
  · exact T.t024.hN
  · exact T.t036.hN
  · exact T.t046.hN
  · exact T.t145.hN
  · exact T.t146.hN
  · exact T.t245.hN

theorem ff_zero (T : Type16 x) (i : Fin 8) (j : Fin 7) (h : j ∈ fIdx i) : T.ff i (x j) = 0 := by
  fin_cases i
  · exact T.q0235.zero j h
  · exact T.q1356.zero j h
  · exact T.t024.zero j h
  · exact T.t036.zero j h
  · exact T.t046.zero j h
  · exact T.t145.zero j h
  · exact T.t146.zero j h
  · exact T.t245.zero j h

theorem ff_neg (T : Type16 x) (i : Fin 8) (j : Fin 7) (h : j ∉ fIdx i) : T.ff i (x j) < 0 := by
  fin_cases i
  · exact T.q0235.neg j h
  · exact T.q1356.neg j h
  · exact T.t024.neg j h
  · exact T.t036.neg j h
  · exact T.t046.neg j h
  · exact T.t145.neg j h
  · exact T.t146.neg j h
  · exact T.t245.neg j h

/-- **The triangle cell** at the line of the planes of facets `P`, `Q` (common vertex `w`), far vertices `a ∈ P`,
`b ∈ Q`, edge facets `eP ∋ w, a`, `eQ ∋ w, b`. -/
def FreeTT (T : Type16 x) (P Q eP eQ : Fin 8) (w a b : Fin 7) : Prop :=
  w ∈ fIdx P ∧ w ∈ fIdx Q ∧ a ∈ fIdx P ∧ a ∉ fIdx Q ∧ b ∈ fIdx Q ∧ b ∉ fIdx P ∧
  w ∈ fIdx eP ∧ a ∈ fIdx eP ∧ w ∈ fIdx eQ ∧ b ∈ fIdx eQ ∧
  ∀ j, j ≠ w → j ≠ a → j ≠ b →
    (j ∉ fIdx P ∧ j ∉ fIdx Q ∧
      T.ff Q (x j) * T.ff P (x b) + T.ff P (x j) * T.ff Q (x a) < T.ff Q (x a) * T.ff P (x b)) ∨
    (j ∈ fIdx P ∧ j ∉ fIdx Q ∧ T.ff Q (x a) < T.ff Q (x j) ∧ j ∉ fIdx eP) ∨
    (j ∈ fIdx Q ∧ j ∉ fIdx P ∧ T.ff P (x b) < T.ff P (x j) ∧ j ∉ fIdx eQ)

/-- Depths of `w, a, b` along `r` are distinct. -/
def DepthOK (x : Fin 7 → ℝ³) (r : ℝ³) (w a b : Fin 7) : Prop :=
  ⟪x w, r⟫ ≠ ⟪x a, r⟫ ∧ ⟪x w, r⟫ ≠ ⟪x b, r⟫ ∧ ⟪x a, r⟫ ≠ ⟪x b, r⟫

theorem freeTT_cell (T : Type16 x) {P Q eP eQ : Fin 8} {w a b : Fin 7} (h : FreeTT T P Q eP eQ w a b)
    {r : ℝ³} (hr : r ≠ 0) (hPr : ⟪T.fN P, r⟫ = 0) (hQr : ⟪T.fN Q, r⟫ = 0) (hd : DepthOK x r w a b) :
    HasLexCellAt (univ.image x) r := by
  obtain ⟨hwP, hwQ, haP, haQ, hbQ, hbP, hweP, haeP, hweQ, hbeQ, hcls⟩ := h
  refine tt_gen (univ.image x) (T.ff P) (T.ff Q) (T.ff eP) (T.ff eQ) (T.fN P) (T.fN Q) (T.fN eP) (T.fN eQ)
    (ff_hN T P) (ff_hN T Q) (ff_hN T eP) (ff_hN T eQ) (x w) (x a) (x b) r (mem_image_of_mem x (mem_univ _))
    (mem_image_of_mem x (mem_univ _)) (mem_image_of_mem x (mem_univ _)) hr hPr hQr (ff_zero T P w hwP)
    (ff_zero T P a haP) (ff_neg T P b hbP) (ff_zero T Q w hwQ) (ff_zero T Q b hbQ) (ff_neg T Q a haQ)
    (ff_zero T eP w hweP) (ff_zero T eP a haeP) (ff_zero T eQ w hweQ) (ff_zero T eQ b hbeQ) hd.1 hd.2.1 hd.2.2 ?_
  intro y hy hyw hya hyb
  obtain ⟨j, -, rfl⟩ := mem_image.1 hy
  have hjw : j ≠ w := fun e => hyw (by rw [e])
  have hja : j ≠ a := fun e => hya (by rw [e])
  have hjb : j ≠ b := fun e => hyb (by rw [e])
  rcases hcls j hjw hja hjb with ⟨c1, c2, c3⟩ | ⟨c1, c2, c3, c4⟩ | ⟨c1, c2, c3, c4⟩
  · exact Or.inl ⟨ff_neg T Q j c2, ff_neg T P j c1, c3⟩
  · exact Or.inr (Or.inl ⟨ff_zero T P j c1, c3, ff_neg T Q j c2, ff_neg T eP j c4⟩)
  · exact Or.inr (Or.inr ⟨ff_zero T Q j c1, c3, ff_neg T P j c2, ff_neg T eQ j c4⟩)

/-- **`FreeVtx16`**: the triangle cell holds at the `t`-th vertex view for some far vertices and edge facets. -/
def FreeVtx16 (T : Type16 x) (t : Fin 11) : Prop :=
  ∃ eP eQ a b, FreeTT T (vtxPQW t).1 (vtxPQW t).2.1 eP eQ (vtxPQW t).2.2 a b

/-- The depth condition at the view direction, for all directions of the line `P ∩ Q` planes. -/
def FreeVtx16D (T : Type16 x) (t : Fin 11) : Prop :=
  ∃ eP eQ a b, FreeTT T (vtxPQW t).1 (vtxPQW t).2.1 eP eQ (vtxPQW t).2.2 a b ∧
    ∀ r : ℝ³, r ≠ 0 → ⟪T.fN (vtxPQW t).1, r⟫ = 0 → ⟪T.fN (vtxPQW t).2.1, r⟫ = 0 →
      DepthOK x r (vtxPQW t).2.2 a b

theorem freeVtx16_hasLexCell (T : Type16 x) (t : Fin 11) (h : FreeVtx16D T t) : HasLexCell (univ.image x) := by
  obtain ⟨eP, eQ, a, b, hf, hd⟩ := h
  obtain ⟨r, hr, h1, h2⟩ := exists_kernel2 (T.fN (vtxPQW t).1) (T.fN (vtxPQW t).2.1)
  exact ⟨r, hr, freeTT_cell T hf hr h1 h2 (hd r hr h1 h2)⟩

theorem freeVtx16_isRupert (T : Type16 x) (t : Fin 11) (h : FreeVtx16D T t) : IsRupert (univ.image x) :=
  isRupert_of_hasLexCell _ (freeVtx16_hasLexCell T t h)

end V2
end Minimality
