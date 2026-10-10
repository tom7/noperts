module

public import Minimality
public import Septopert

/-!
# Seven vertices is the smallest a nopert can be

This file brings together results from the rest of the repository,
proving the main theorem in MainTheorem **assuming that
`CertificatesValid` is true**.

See `BUILDING.md` for more details.

-/

@[expose] public section

open Septopert

/-- Every nontrivial convex polyhedron with fewer than 7 vertices is Rupert. -/
theorem notExistsNonRupertPolyhedronBelowSizeSeven :
    NotExistsNonRupertPolyhedronBelowSizeSeven := by
  rintro ⟨V, hcard, hint, hnR⟩
  exact hnR (isRupert_of_card_le_six V (by omega)
    ((not_coplanar_iff_interior_convexHull_nonempty _).mpr hint))

/-- The Septopert has at most 7 points.

It actually has exactly 7, but this conveniently dodges having to prove uniqueness. -/
theorem card_septopert_le_seven : septopert.card ≤ 7 := by
  rw [septopert_eq_verts, verts]
  calc (Finset.univ.image fun i : Fin 7 => toR3 (vertexQ i)).card
      ≤ (Finset.univ : Finset (Fin 7)).card := Finset.card_image_le
    _ = 7 := by simp

/-- **There is a nontrivial 7-vertex polyhedron that is not Rupert**, given
valid certificate data: the Septopert. -/
theorem existsNonRupertPolyhedronSizeSeven_of_certificatesValid (h : CertificatesValid) :
    ExistsNonRupertPolyhedronSizeSeven :=
  ⟨septopert, card_septopert_le_seven,
    (isNopert_of_certificatesValid h).interior_nonempty,
    not_isRupert_of_certificatesValid h⟩

/-- **Seven vertices is the smallest a nopert can be**, given valid
certificate data. -/
theorem minimalNopert_of_certificatesValid (h : CertificatesValid) : MinimalNopert :=
  ⟨existsNonRupertPolyhedronSizeSeven_of_certificatesValid h,
    notExistsNonRupertPolyhedronBelowSizeSeven⟩

end

/--
info: 'minimalNopert_of_certificatesValid' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms minimalNopert_of_certificatesValid
