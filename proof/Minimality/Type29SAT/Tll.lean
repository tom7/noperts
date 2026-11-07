module

public import Minimality.Type29SAT.Rule

@[expose] public section

/-!
# Type 29: the `T(L, L)` rows (family 22)

For a line view `L` (the cross product of two facet normals `N_a x N_b`) and a facet `t`: if the entry of
`det3 (N a) (N b) (N t)` is nonzero, the view is nonzero, so `<u, u> > 0`: the clause `not x_p or Tp(L, L)`
(and the same for `x_q`).
-/

set_option autoImplicit false
set_option maxRecDepth 100000
open scoped RealInnerProductSpace
open Classical
open Finset
open Minimality Minimality.H21

namespace Minimality.H29.SAT

/-- The clauses of a `T(L,L)` row (parameters `L`, `t`): a nonzero determinant sign implies `tp L L`. -/
def tllS (L t : Nat) : List (List Lit) :=
  [[(nEnt3 (lineOf L).1 (lineOf L).2 t).1.neg, (true, V.tp L L)],
   [(nEnt3 (lineOf L).1 (lineOf L).2 t).2.neg, (true, V.tp L L)]]

/-- Check of a `T(L,L)` row. -/
def tllOK (p : List Nat) (cl : List Lit) : Bool :=
  decide (21 ≤ prm p 0 ∧ prm p 0 < 43 ∧ prm p 1 < 9) && anyCov cl (tllS (prm p 0) (prm p 1))

/-- **A `T(L,L)` row that passes the check is true** of the real data. -/
theorem tllOK_sound {g : Geo} (hG : GeoOK g) {p : List Nat} {cl : List Lit}
    (h : tllOK p cl = true) : Holds (rho g) cl := by
  unfold tllOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2, h3⟩, hc⟩ := h
  set L := prm p 0
  set t := prm p 1
  have hlm : lineOf L ∈ lines := by
    unfold lineOf
    have : L - 21 < lines.length := by simp [lines]; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]
    exact List.getElem_mem this
  have hb := lines_ok _ hlm
  have hv : g.vv L = cross (g.N (lineOf L).1) (g.N (lineOf L).2) := by
    have : ¬ L < 21 := by omega
    simp only [Geo.vv, this, ite_false]; rfl
  have S := nEnt3_sound hG hb.1 hb.2 (show t < 9 from h3)
  have key : det3 (g.N (lineOf L).1) (g.N (lineOf L).2) (g.N t) ≠ 0 → rho g (V.tp L L) = true := by
    intro hd
    have hne : g.vv L ≠ 0 := by
      intro h0
      apply hd
      rw [← inner_cross_det3', ← hv, h0]; simp
    have : 0 < ⟪g.vv L, g.vv L⟫ := real_inner_self_pos.mpr hne
    show decide (0 < ⟪g.vv L, g.vv L⟫) = true
    exact decide_eq_true this
  apply anyCov_holds (rho_proper g) hc
  intro s hs
  simp only [tllS, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · by_cases hx : evalL (rho g) (nEnt3 (lineOf L).1 (lineOf L).2 t).1 = true
    · have hp := S.1.mp hx
      refine ⟨(true, V.tp L L), by simp, ?_⟩
      simp [evalL, key hp.ne']
    · refine ⟨(nEnt3 (lineOf L).1 (lineOf L).2 t).1.neg, by simp, ?_⟩
      rw [evalL_neg]; simp [hx]
  · by_cases hx : evalL (rho g) (nEnt3 (lineOf L).1 (lineOf L).2 t).2 = true
    · have hp := S.2.mp hx
      refine ⟨(true, V.tp L L), by simp, ?_⟩
      simp [evalL, key hp.ne]
    · refine ⟨(nEnt3 (lineOf L).1 (lineOf L).2 t).2.neg, by simp, ?_⟩
      rw [evalL_neg]; simp [hx]

end Minimality.H29.SAT
