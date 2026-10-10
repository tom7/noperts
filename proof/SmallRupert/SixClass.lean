module

public import SmallRupert.SixGale

@[expose] public section

/-!
# Every polyhedron with at most six vertices is Rupert (LEMMAS.md L10)

After a 2+4 split (Lemma 10.1) with positive points `D, E` and the other four
`W = {P, Q, R, S}`:
* if `W` is coplanar, the segment `DE` crosses `relint conv W` (Lemma 10.3,
  `isRupert_split_coplanar`);
* otherwise `D, E` have barycentric coordinates `β = l`, `γ = m` on `W`
  (`NF`), every point of `W` falls in one of the classes
  `I = (+,-)`, `I½ = (+,0)`, `II = (+,+)`, `II½ = (0,+)`, `III = (-,+)`, and the
  case table of Theorem 10.4 gives an octahedron, a bicapped tetrahedron, a
  T4, a T5 or a T3, each with its facets read off from Gale signs.

`isRupert_of_card_le_six` assembles L5–L10.
-/

namespace SmallRupert

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- Normal form after a 2+4 split (LEMMAS.md L10.3): `l`, `m` are the
barycentric dependencies of `D`, `E` on `W = {P, Q, R, S}`, and the split
gives `(H)`. -/
structure NF (V : Finset ℝ³) (D E P Q R S : ℝ³) (l m : ℝ³ → ℝ) : Prop where
  six : Six V
  eq : V = {D, E, P, Q, R, S}
  nodup : [D, E, P, Q, R, S].Nodup
  hl : IsDepOn V l
  hm : IsDepOn V m
  lD : l D = -1
  mD : m D = 0
  lE : l E = 0
  mE : m E = -1
  H : ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ 0 < a * l P + b * m P ∧ 0 < a * l Q + b * m Q ∧
    0 < a * l R + b * m R ∧ 0 < a * l S + b * m S

/-! ### Relabelling -/

theorem NF.swapPQ {V : Finset ℝ³} {D E P Q R S : ℝ³} {l m : ℝ³ → ℝ}
    (h : NF V D E P Q R S l m) : NF V D E Q P R S l m := by
  sorry

theorem NF.swapQR {V : Finset ℝ³} {D E P Q R S : ℝ³} {l m : ℝ³ → ℝ}
    (h : NF V D E P Q R S l m) : NF V D E P R Q S l m := by
  sorry

theorem NF.swapRS {V : Finset ℝ³} {D E P Q R S : ℝ³} {l m : ℝ³ → ℝ}
    (h : NF V D E P Q R S l m) : NF V D E P Q S R l m := by
  sorry

/-- The mirror `D ↔ E`, `l ↔ m` (classes `I ↔ III`, `I½ ↔ II½`). -/
theorem NF.mirror {V : Finset ℝ³} {D E P Q R S : ℝ³} {l m : ℝ³ → ℝ}
    (h : NF V D E P Q R S l m) : NF V E D S R Q P m l := by
  sorry

/-! ### The case table (Theorem 10.4) -/

/-- `(Q, R) = (I, III)`: an octahedron with opposite pairs `PQ`, `DE`, `RS`. -/
theorem NF.case_oct {V : Finset ℝ³} {D E P Q R S : ℝ³} {l m : ℝ³ → ℝ}
    (h : NF V D E P Q R S l m) (hP : 0 < l P ∧ m P < 0) (hQ : 0 < l Q ∧ m Q < 0)
    (hR : l R < 0 ∧ 0 < m R) (hS : l S < 0 ∧ 0 < m S) : IsRupert V := by
  sorry

/-- `(Q, R) = (II, II)`: a bicapped tetrahedron with caps `E`, `D`. -/
theorem NF.case_bicap₁ {V : Finset ℝ³} {D E P Q R S : ℝ³} {l m : ℝ³ → ℝ}
    (h : NF V D E P Q R S l m) (hP : 0 < l P ∧ m P < 0) (hQ : 0 < l Q ∧ 0 < m Q)
    (hR : 0 < l R ∧ 0 < m R) (hS : l S < 0 ∧ 0 < m S) : IsRupert V := by
  sorry

/-- `(Q, R) = (II, III)`: a bicapped tetrahedron with caps `E`, `P`. -/
theorem NF.case_bicap₂ {V : Finset ℝ³} {D E P Q R S : ℝ³} {l m : ℝ³ → ℝ}
    (h : NF V D E P Q R S l m) (hP : 0 < l P ∧ m P < 0) (hQ : 0 < l Q ∧ 0 < m Q)
    (hR : l R < 0 ∧ 0 < m R) (hS : l S < 0 ∧ 0 < m S) : IsRupert V := by
  sorry

/-- `(Q, R) = (I½, III)`: a T4. -/
theorem NF.case_T4 {V : Finset ℝ³} {D E P Q R S : ℝ³} {l m : ℝ³ → ℝ}
    (h : NF V D E P Q R S l m) (hP : 0 < l P ∧ m P < 0) (hQ : 0 < l Q ∧ m Q = 0)
    (hR : l R < 0 ∧ 0 < m R) (hS : l S < 0 ∧ 0 < m S) : IsRupert V := by
  sorry

/-- `(Q, R) = (I½, II)`: a T5 with apex `Q`. -/
theorem NF.case_T5 {V : Finset ℝ³} {D E P Q R S : ℝ³} {l m : ℝ³ → ℝ}
    (h : NF V D E P Q R S l m) (hP : 0 < l P ∧ m P < 0) (hQ : 0 < l Q ∧ m Q = 0)
    (hR : 0 < l R ∧ 0 < m R) (hS : l S < 0 ∧ 0 < m S) : IsRupert V := by
  sorry

/-- `(Q, R) = (I½, II½)`: a T3. -/
theorem NF.case_T3 {V : Finset ℝ³} {D E P Q R S : ℝ³} {l m : ℝ³ → ℝ}
    (h : NF V D E P Q R S l m) (hP : 0 < l P ∧ m P < 0) (hQ : 0 < l Q ∧ m Q = 0)
    (hR : l R = 0 ∧ 0 < m R) (hS : l S < 0 ∧ 0 < m S) : IsRupert V := by
  sorry

/-- **Theorem 10.4.** Every normal form is Rupert. -/
theorem NF.isRupert {V : Finset ℝ³} {D E P Q R S : ℝ³} {l m : ℝ³ → ℝ}
    (h : NF V D E P Q R S l m) : IsRupert V := by
  sorry

/-! ### The split -/

/-- **Lemma 10.3.**  A split with coplanar `W`: the segment `DE` crosses
`relint conv W`. -/
theorem isRupert_split_coplanar {V : Finset ℝ³} (hS : Six V) {D E P Q R S : ℝ³}
    (hV : V = {D, E, P, Q, R, S}) (hnd : [D, E, P, Q, R, S].Nodup) {μ : ℝ³ → ℝ}
    (hμ : IsDepOn V μ) (hD : 0 < μ D) (hE : 0 < μ E) (hP : μ P < 0) (hQ : μ Q < 0)
    (hR : μ R < 0) (hS' : μ S < 0) (hcop : Coplanar ℝ ({P, Q, R, S} : Set ℝ³)) :
    IsRupert V := by
  sorry

/-- A split with independent `W` gives a normal form. -/
theorem exists_NF_of_split {V : Finset ℝ³} (hS : Six V) {D E P Q R S : ℝ³}
    (hV : V = {D, E, P, Q, R, S}) (hnd : [D, E, P, Q, R, S].Nodup) {μ : ℝ³ → ℝ}
    (hμ : IsDepOn V μ) (hD : 0 < μ D) (hE : 0 < μ E) (hP : μ P < 0) (hQ : μ Q < 0)
    (hR : μ R < 0) (hS' : μ S < 0) (hind : ¬ Coplanar ℝ ({P, Q, R, S} : Set ℝ³)) :
    ∃ l m, NF V D E P Q R S l m := by
  sorry

/-- Every 2+4 split gives a passage. -/
theorem isRupert_of_split {V : Finset ℝ³} (hS : Six V) {D E : ℝ³} (hD : D ∈ V) (hE : E ∈ V)
    (hDE : D ≠ E) {μ : ℝ³ → ℝ} (hμ : IsDepOn V μ) (hμD : 0 < μ D) (hμE : 0 < μ E)
    (hμW : ∀ x ∈ V, x ≠ D → x ≠ E → μ x < 0) : IsRupert V := by
  sorry

/-! ### Assembly -/

/-- Setting (S) is Rupert. -/
theorem Six.isRupert {V : Finset ℝ³} (hS : Six V) : IsRupert V := by
  sorry

/-- **Theorem 10.0.** Every convex polyhedron with at most six vertices is
Rupert.  `V` need not consist of vertices only. -/
theorem isRupert_of_card_le_six (V : Finset ℝ³) (hV : V.card ≤ 6)
    (hint : (interior (convexHull ℝ (V : Set ℝ³))).Nonempty) : IsRupert V := by
  sorry

end SmallRupert

end
