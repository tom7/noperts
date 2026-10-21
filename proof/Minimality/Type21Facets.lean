module

public import Minimality.Type21Pattern

@[expose] public section

/-!
# Type 21 from its facets (`FEWER-FACES-PROOFS.md` §16, Theorem 16.26)

Seven points `x 0, …, x 6` whose facets are `014, 015, 0256, 046, 134, 135, 2346, 235`:
`exists_type21_cap` makes `x 2` a type-21 cap over `O = K − 2`, and `isRupert_type21_all`
(Theorem 16.26) applies.  The special positions are stated in the points and the facet
functions.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- **Type 21 from its facets (Theorem 16.26).**  Seven points whose facets are `014, 015, 0256,
046, 134, 135, 2346, 235`.  Off the special positions — `NoPlaneParallel`, `GenPos`, no
horizontal double normal at the edge views, the five planar equators `{4, 5, 1, 6}`,
`{0, 3, 1, 6}`, `{0, 3, 4, 5}` (of `K − 2`), `{0, 3, 1, 2}`, `{4, 5, 1, 2}` (of `K − 6`), the
special positions of `T1` at the four vertex crossings `0: 014/0256`, `4: 014/2346`,
`5: 135/0256`, `3: 135/2346` (`T1View`), and the special positions of the vertex tests of F2 in
the four labellings `id, σ1, σ2, σ2σ1` (`F2Views`: at `4: 014/2346, 046/134`, `0: 014/0256,
046/015`, `3: 135/2346, 235/134`, `5: 135/0256, 235/015`) — the points are Rupert.  The switch
surface (`H⁻`, `H⁻_c`) is no special position: Theorem 16.30. -/
theorem isRupert_type21_facets (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (fA fB fC fD fE fF fG fH : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 1, 4} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 1, 4} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({0, 1, 5} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({0, 1, 5} : Finset (Fin 7)) → fB (x i) < 0))
    (hC : ∀ i, (i ∈ ({0, 2, 5, 6} : Finset (Fin 7)) → fC (x i) = 0) ∧
      (i ∉ ({0, 2, 5, 6} : Finset (Fin 7)) → fC (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 4, 6} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 4, 6} : Finset (Fin 7)) → fD (x i) < 0))
    (hE : ∀ i, (i ∈ ({1, 3, 4} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({1, 3, 4} : Finset (Fin 7)) → fE (x i) < 0))
    (hF : ∀ i, (i ∈ ({1, 3, 5} : Finset (Fin 7)) → fF (x i) = 0) ∧
      (i ∉ ({1, 3, 5} : Finset (Fin 7)) → fF (x i) < 0))
    (hG : ∀ i, (i ∈ ({2, 3, 4, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({2, 3, 4, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hH : ∀ i, (i ∈ ({2, 3, 5} : Finset (Fin 7)) → fH (x i) = 0) ∧
      (i ∉ ({2, 3, 5} : Finset (Fin 7)) → fH (x i) < 0))
    (hpp : NoPlaneParallel (univ.image x)) (hgen : GenPos (univ.image x))
    (hnd : ∀ v ∈ univ.image x, ∀ w ∈ univ.image x, v ≠ w →
      NoHDNAt ((univ.image x).erase w) (w - v))
    (hEq : det3 (x 5 - x 4) (x 1 - x 4) (x 6 - x 4) ≠ 0 ∧
      det3 (x 3 - x 0) (x 1 - x 0) (x 6 - x 0) ≠ 0 ∧
      det3 (x 3 - x 0) (x 4 - x 0) (x 5 - x 0) ≠ 0 ∧
      det3 (x 0 - x 3) (x 1 - x 3) (x 2 - x 3) ≠ 0 ∧
      det3 (x 4 - x 5) (x 1 - x 5) (x 2 - x 5) ≠ 0)
    (hT1 : T1View (univ.image x) fA fC (x 0) (x 3) (x 4) (x 5) ∧
      T1View (univ.image x) fA fG (x 4) (x 5) (x 0) (x 3) ∧
      T1View (univ.image x) fF fC (x 5) (x 4) (x 3) (x 0) ∧
      T1View (univ.image x) fF fG (x 3) (x 0) (x 5) (x 4))
    (hF2 : F2Views (univ.image x) (x 0) (x 3) (x 4) (x 5) (x 1) (x 6) (x 2) ∧
      F2Views (univ.image x) (x 4) (x 5) (x 0) (x 3) (x 1) (x 6) (x 2) ∧
      F2Views (univ.image x) (x 5) (x 4) (x 3) (x 0) (x 1) (x 2) (x 6) ∧
      F2Views (univ.image x) (x 3) (x 0) (x 5) (x 4) (x 1) (x 2) (x 6)) :
    IsRupert (univ.image x) := by
  classical
  obtain ⟨-, eV⟩ := image_seven21 x
  obtain ⟨F, hcap, eA, eD, eB, eC, eE, eG, eF⟩ :=
    exists_type21_cap x hx fA fB fC fD fE fF fG fH hA hB hC hD hE hF hG hH
  rw [eV] at hpp hgen hnd ⊢
  have hnd' : NoHDNEdges (insert (x 2) ({x 0, x 3, x 4, x 5, x 1, x 6} : Finset ℝ³)) := hnd
  have eO2 := type21_set_O2 (x 0) (x 3) (x 4) (x 5) (x 1) (x 6) (x 2)
  have e5 := (type21_set (x 0) (x 3) (x 4) (x 5) (x 1) (x 6) (x 2)).2.2.2.2
  have e21 := type21_set_O21 (x 0) (x 3) (x 4) (x 5) (x 1) (x 6) (x 2)
  obtain ⟨t1, t2, t3, t4⟩ := hT1
  rw [eV] at t1 t2 t3 t4
  obtain ⟨f1, f2, f3, f4⟩ := hF2
  rw [eV] at f1 f2 f3 f4
  refine isRupert_type21_all F hcap hpp hgen hnd' hEq ⟨fun u hu h1 h2 => ?_,
      fun u hu h1 h2 => ?_, fun u hu h1 h2 => ?_, fun u hu h1 h2 => ?_⟩
    ⟨f1, ?_, ?_, ?_⟩
  · exact t1 u hu (by rw [affine_linear_eq fA eA F.abc.hN]; exact h1)
      (by rw [affine_linear_eq fC eC F.ab'c'.hN]; exact h2)
  · rw [e5]
    exact t2 u hu (by rw [affine_linear_eq fA eA F.abc.hN]; exact h1)
      (by rw [affine_linear_eq fG eG F.a'bc'.hN]; exact h2)
  · rw [eO2]
    exact t3 u hu (by rw [affine_linear_eq fF eF F.a'b'c.hN]; exact h1)
      (by rw [affine_linear_eq fC eC F.ab'c'.hN]; exact h2)
  · rw [e21]
    exact t4 u hu (by rw [affine_linear_eq fF eF F.a'b'c.hN]; exact h1)
      (by rw [affine_linear_eq fG eG F.a'bc'.hN]; exact h2)
  · unfold Type21OtherGen; rw [e5]; exact f2
  · unfold Type21OtherGen; rw [eO2]; exact f3
  · unfold Type21OtherGen; rw [e21]; exact f4

end Minimality

end
