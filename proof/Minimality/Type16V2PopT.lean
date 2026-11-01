module

public import Minimality.Type16V2Tri
public import Minimality.Type16V2Pop

@[expose] public section

/-!
# V2: pop cells at the quadrilateral-triangle vertex views of type 16 (AE, AF, BE, BH)

`P = A = 0235` (cyclic 2,0,3,5, diagonal `05`, ring points `3`, `2`) or `P = B = 1356` (cyclic 3,6,1,5, diagonal
`56`, ring points `3`, `1`).  The diagonal functional is `g = f_Pbar / f_Pbar(v) + f_D / f_D(5) - 1` (`D = 036`),
with `g(3) = -1 < 0 < g(2)` resp. `g(1)` from the quadrilateral coordinates of `Type16.coords0235/1356`.
-/

set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped RealInnerProductSpace
open Finset Filter

namespace Minimality
namespace V2
open Type08Sp Type08Sp.C2

variable {x : Fin 7 → ℝ³}

/-- The diagonal functional of the quadrilateral whose other facet is `Pb` and whose diagonal runs `v – 5`. -/
noncomputable def popG (T : Type16 x) (Pb : Fin 8) (v : Fin 7) (y : ℝ³) : ℝ :=
  T.ff Pb y / T.ff Pb (x v) + T.ff 3 y / T.ff 3 (x 5) - 1

noncomputable def popN (T : Type16 x) (Pb : Fin 8) (v : Fin 7) : ℝ³ :=
  (1 / T.ff Pb (x v)) • T.fN Pb + (1 / T.ff 3 (x 5)) • T.fN 3

theorem popG_hN (T : Type16 x) (Pb : Fin 8) (v : Fin 7) :
    ∀ y z, popG T Pb v y - popG T Pb v z = ⟪popN T Pb v, y - z⟫ := by
  intro y z
  have h1 := ff_hN T Pb y z
  have h2 := ff_hN T 3 y z
  simp only [popG, popN, inner_add_left, real_inner_smul_left, ← h1, ← h2]
  ring

theorem popG_facts (T : Type16 x) (Pb : Fin 8) (v : Fin 7) (hv : v ∉ fIdx Pb) (hv3 : v ∈ fIdx 3)
    (h5 : 5 ∈ fIdx Pb) (h53 : 5 ∉ fIdx 3) (h3 : 3 ∈ fIdx Pb) (h33 : 3 ∈ fIdx 3) :
    popG T Pb v (x v) = 0 ∧ popG T Pb v (x 5) = 0 ∧ popG T Pb v (x 3) = -1 := by
  have a1 := (ff_neg T Pb v hv).ne
  have a2 := (ff_neg T 3 5 h53).ne
  refine ⟨?_, ?_, ?_⟩
  · simp only [popG, ff_zero T 3 v hv3]; field_simp; ring
  · simp only [popG, ff_zero T Pb 5 h5]; field_simp; ring
  · simp only [popG, ff_zero T Pb 3 h3, ff_zero T 3 3 h33]; ring

/-- Pop condition: the quadrilateral `P` with diagonal `w – a` (opposite), ring `m1, m2`; triangle side `Q`. -/
def PopCond (T : Type16 x) (P Q eQ : Fin 8) (w a b m1 m2 : Fin 7) : Prop :=
  w ∈ fIdx P ∧ a ∈ fIdx P ∧ m1 ∈ fIdx P ∧ m2 ∈ fIdx P ∧ w ∈ fIdx Q ∧ a ∉ fIdx Q ∧ m1 ∉ fIdx Q ∧ m2 ∉ fIdx Q ∧
  b ∈ fIdx Q ∧ b ∉ fIdx P ∧ w ∈ fIdx eQ ∧ b ∈ fIdx eQ ∧
  T.ff Q (x a) < T.ff Q (x m1) ∧ T.ff Q (x a) < T.ff Q (x m2) ∧
  ∀ j, j ≠ w → j ≠ a → j ≠ b → j ≠ m1 → j ≠ m2 →
    (j ∉ fIdx P ∧ j ∉ fIdx Q ∧
      T.ff Q (x j) * T.ff P (x b) + T.ff P (x j) * T.ff Q (x a) < T.ff Q (x a) * T.ff P (x b)) ∨
    (j ∈ fIdx Q ∧ j ∉ fIdx P ∧ T.ff P (x b) < T.ff P (x j) ∧ j ∉ fIdx eQ)

/-- Depths of `w, a, b, m1, m2` along `r`: the nine pairs used by the pop cell are distinct. -/
def DepthOK5 (x : Fin 7 → ℝ³) (r : ℝ³) (w a b m1 m2 : Fin 7) : Prop :=
  ⟪x w, r⟫ ≠ ⟪x a, r⟫ ∧ ⟪x w, r⟫ ≠ ⟪x b, r⟫ ∧ ⟪x a, r⟫ ≠ ⟪x b, r⟫ ∧ ⟪x w, r⟫ ≠ ⟪x m1, r⟫ ∧
  ⟪x a, r⟫ ≠ ⟪x m1, r⟫ ∧ ⟪x b, r⟫ ≠ ⟪x m1, r⟫ ∧ ⟪x w, r⟫ ≠ ⟪x m2, r⟫ ∧ ⟪x a, r⟫ ≠ ⟪x m2, r⟫ ∧
  ⟪x b, r⟫ ≠ ⟪x m2, r⟫

/-- The pop cell from a diagonal functional. -/
theorem popCond_cell (T : Type16 x) {P Q eQ : Fin 8} {w a b m1 m2 : Fin 7} (h : PopCond T P Q eQ w a b m1 m2)
    (g : ℝ³ → ℝ) (Ng : ℝ³) (hg : ∀ y z, g y - g z = ⟪Ng, y - z⟫) (hgw : g (x w) = 0) (hga : g (x a) = 0)
    (hg1 : g (x m1) < 0) (hg2 : 0 < g (x m2))
    {r : ℝ³} (hr : r ≠ 0) (hPr : ⟪T.fN P, r⟫ = 0) (hQr : ⟪T.fN Q, r⟫ = 0) (hD : DepthOK5 x r w a b m1 m2) :
    HasLexCellAt (univ.image x) r := by
  obtain ⟨hwP, haP, h1P, h2P, hwQ, haQ, h1Q, h2Q, hbQ, hbP, hweQ, hbeQ, hf1, hf2, hcls⟩ := h
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9⟩ := hD
  have mem : ∀ i, x i ∈ univ.image x := fun i => mem_image_of_mem x (mem_univ i)
  refine pop_gen (univ.image x) (T.ff P) (T.ff Q) (T.ff eQ) g (T.fN P) (T.fN Q) (T.fN eQ) Ng (ff_hN T P)
    (ff_hN T Q) (ff_hN T eQ) hg (x w) (x a) (x b) (x m1) (x m2) r (mem w) (mem a) (mem b) (mem m1) (mem m2) hr hPr hQr
    (ff_zero T P w hwP) (ff_zero T P a haP) (ff_neg T P b hbP) (ff_zero T Q w hwQ) (ff_zero T Q b hbQ)
    (ff_neg T Q a haQ) (ff_zero T eQ w hweQ) (ff_zero T eQ b hbeQ) (ff_zero T P m1 h1P) ⟨hf1, ff_neg T Q m1 h1Q⟩
    (ff_zero T P m2 h2P) ⟨hf2, ff_neg T Q m2 h2Q⟩ hgw hga hg1 hg2 d1 d2 d3 d4 d5 d6 d7 d8 d9 ?_
  intro y hy hyw hya hyb hy1 hy2
  obtain ⟨j, -, rfl⟩ := mem_image.1 hy
  have hjw : j ≠ w := fun e => hyw (by rw [e])
  have hja : j ≠ a := fun e => hya (by rw [e])
  have hjb : j ≠ b := fun e => hyb (by rw [e])
  have hj1 : j ≠ m1 := fun e => hy1 (by rw [e])
  have hj2 : j ≠ m2 := fun e => hy2 (by rw [e])
  rcases hcls j hjw hja hjb hj1 hj2 with ⟨c1, c2, c3⟩ | ⟨c1, c2, c3, c4⟩
  · exact Or.inl ⟨ff_neg T Q j c2, ff_neg T P j c1, c3⟩
  · exact Or.inr ⟨ff_zero T Q j c1, c3, ff_neg T P j c2, ff_neg T eQ j c4⟩

end V2
end Minimality
