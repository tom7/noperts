module

public import SmallRupert.FirstOrder
public import SmallRupert.DoubleNormal

@[expose] public section

/-!
# L2, L4, L5: the coplanar-silhouette theorem

* L2 (`screenVel_of_depth_eq`, `exists_motion_iff`, `exists_motion_iff_faceOn`):
  on a non-vertical plane `z = ⟪g, p⟫ + c` the screen velocity is the affine
  field `M p + b` with `M = ψ J + f gᵀ`; for `g ≠ 0` the realizable `M` are
  exactly those with `⟪J g, M (J g)⟫ = 0` (`J g` spans the iso-depth
  direction `û`), for `g = 0` (face-on) exactly `ℝ J`.
* `admissibleViews V W` is LEMMAS.md's `U_Π` for `Π = affineSpan W`: view
  directions `u` not parallel to `Π` such that every other point of `V`
  projects along `u` into the relative interior of `F₀ = conv W`.
* L4 (`dense_generic_admissibleViews`): views orthogonal to no double normal
  of `F₀` are dense in `U_Π` (the bad set lies on finitely many great circles).
* L5 (`exists_firstOrderInward_of_coplanar`, `isRupert_of_generic_admissibleView`,
  `isRupert_of_admissibleViews_nonempty`): the coplanar-silhouette theorem.

Formulation.  Instead of LEMMAS.md's `W = V ∩ Π` we allow any `W ⊆ V`, with
`Π := affineSpan ℝ W`; points of `V \ W` that happen to lie in `Π` must then
lie in `relint F₀`, which the definition of `admissibleViews` already says.
No vertex or convex-position hypothesis is needed, nor nonempty interior of
`conv V`.  Non-collinearity of `W` is needed (a segment shadow has empty
interior); `Π` being a plane follows from `admissibleViews V W ≠ ∅`.
-/

namespace SmallRupert

open scoped RealInnerProductSpace Matrix Topology
open Filter

/-- The vector `f = (ω₂, -ω₁)` of LEMMAS.md L2 (indices shifted to `0, 1`). -/
noncomputable def tiltVec (ω : ℝ³) : ℝ² := !₂[ω 1, -ω 0]

/-- **L2(a).** On the plane `z = ⟪g, p⟫ + c` the screen velocity is affine in
the screen position `p`: `ν(x) = ψ J p + ⟪g, p⟫ f + (c f + Pτ)`. -/
theorem screenVel_of_depth_eq (ω τ x : ℝ³) (g : ℝ²) (c : ℝ)
    (hx : x 2 = ⟪g, proj_xy x⟫ + c) :
    screenVel ω τ x = ω 2 • rot90 (proj_xy x) + ⟪g, proj_xy x⟫ • tiltVec ω +
      (c • tiltVec ω + proj_xy τ) := by
  sorry

/-- **L2(b,c).** For a non-face-on plane (`g ≠ 0`), an affine screen field
`p ↦ M p + b` is the screen velocity on the plane of some first-order motion
iff `⟪J g, M (J g)⟫ = 0`. -/
theorem exists_motion_iff (g : ℝ²) (hg : g ≠ 0) (c : ℝ) (M : ℝ² →ₗ[ℝ] ℝ²)
    (b : ℝ²) :
    (∃ ω τ : ℝ³, ∀ x : ℝ³, x 2 = ⟪g, proj_xy x⟫ + c →
        screenVel ω τ x = M (proj_xy x) + b) ↔
      ⟪rot90 g, M (rot90 g)⟫ = 0 := by
  sorry

/-- **L2(d), realizability.** Face-on (`g = 0`) only rigid screen motions are
realizable. -/
theorem exists_motion_iff_faceOn (c : ℝ) (M : ℝ² →ₗ[ℝ] ℝ²) (b : ℝ²) :
    (∃ ω τ : ℝ³, ∀ x : ℝ³, x 2 = c → screenVel ω τ x = M (proj_xy x) + b) ↔
      ∃ ψ : ℝ, ∀ p, M p = ψ • rot90 p := by
  sorry

/-- **L2(d), obstruction (optional, not used by the Rupert theorems).** No
rigid screen motion is strictly inward at every point of a polygon (a
diameter is a double normal for every direction field `ψ J`; LEMMAS.md uses
the divergence theorem instead). -/
theorem not_forall_inward_rigid (W : Finset ℝ²)
    (hW : (interior (convexHull ℝ (W : Set ℝ²))).Nonempty) (ψ : ℝ) (b : ℝ²) :
    ¬ ∀ p ∈ W, IsInwardAt (convexHull ℝ (W : Set ℝ²)) p (ψ • rot90 p + b) := by
  sorry

/-- LEMMAS.md's `U_Π` for `Π = affineSpan ℝ W`, `F₀ = conv W`: directions `u`
not parallel to `Π` such that the line `v + ℝ u` meets `relint F₀` for every
`v ∈ V \ W`. -/
def admissibleViews (V W : Finset ℝ³) : Set ℝ³ :=
  { u | u ∉ (affineSpan ℝ (W : Set ℝ³)).direction ∧
    ∀ v ∈ V, v ∉ W → ∃ t : ℝ, v + t • u ∈ intrinsicInterior ℝ (convexHull ℝ (W : Set ℝ³)) }

/-- `U_Π` is open (LEMMAS.md §L4). -/
theorem isOpen_admissibleViews (V W : Finset ℝ³) (hW : ¬ Collinear ℝ (W : Set ℝ³)) :
    IsOpen (admissibleViews V W) := by
  sorry

/-- **Lemma 4 (genericity).** Views orthogonal to no double-normal direction
of `F₀` are dense in `U_Π`.  (The bad set is contained in finitely many
planes `δ^⊥`, `δ ∈ Π₀`, by `isDoubleNormalDir_convexHull_cases`; all of them
contain the normal of `Π`, so in particular face-on views are bad.) -/
theorem dense_generic_admissibleViews (V W : Finset ℝ³) (hW : ¬ Collinear ℝ (W : Set ℝ³)) :
    admissibleViews V W ⊆ closure { u ∈ admissibleViews V W |
      ∀ δ, IsDoubleNormalDir (convexHull ℝ (W : Set ℝ³)) δ → ⟪δ, u⟫ ≠ 0 } := by
  sorry

theorem exists_generic_admissibleView (V W : Finset ℝ³) (hW : ¬ Collinear ℝ (W : Set ℝ³))
    (hU : (admissibleViews V W).Nonempty) :
    ∃ u ∈ admissibleViews V W,
      ∀ δ, IsDoubleNormalDir (convexHull ℝ (W : Set ℝ³)) δ → ⟪δ, u⟫ ≠ 0 := by
  sorry

/-- `U_Π` is a cone: invariant under nonzero scaling. -/
theorem smul_mem_admissibleViews (V W : Finset ℝ³) {u : ℝ³} (hu : u ∈ admissibleViews V W)
    {r : ℝ} (hr : r ≠ 0) : r • u ∈ admissibleViews V W := by
  sorry

/-- Admissible views are carried along by rotations. -/
theorem mem_admissibleViews_image (V W : Finset ℝ³) (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (hQ : Q ∈ SO3) (u : ℝ³) (hu : u ∈ admissibleViews V W) :
    Q.toEuclideanLin u ∈
      admissibleViews (V.image Q.toEuclideanLin) (W.image Q.toEuclideanLin) := by
  sorry

/-- **Theorem 5, first-order form, standard view, explicit plane** (the form
the proofs use).  `W` lies in the non-vertical plane `⟪N, x⟫ = h`; its
shadow `F = conv (proj_xy W)` is solid; every other point of `V` projects
into `interior F`; and no double normal of `conv W` is horizontal.  Then some
first-order motion is strictly inward. -/
theorem exists_firstOrderInward_of_plane (V W : Finset ℝ³) (hWV : W ⊆ V) (N : ℝ³) (h : ℝ)
    (hN : N 2 ≠ 0) (hWN : ∀ w ∈ W, ⟪N, w⟫ = h)
    (hint : (interior (convexHull ℝ ((W.image proj_xy : Finset ℝ²) : Set ℝ²))).Nonempty)
    (hin : ∀ v ∈ V, v ∉ W →
      proj_xy v ∈ interior (convexHull ℝ ((W.image proj_xy : Finset ℝ²) : Set ℝ²)))
    (hgen : ∀ δ : ℝ³, IsDoubleNormalDir (convexHull ℝ (W : Set ℝ³)) δ → δ 2 ≠ 0) :
    ∃ ω τ : ℝ³, FirstOrderInward V ω τ := by
  sorry

/-- **Theorem 5, first-order form, standard view.**  If the standard view
`ez` is admissible for `(V, W)` and orthogonal to no double normal of
`F₀ = conv W` (i.e. every double-normal direction has nonzero depth
component), then some first-order motion is strictly inward.  The view is
then automatically not face-on, since a diameter of `F₀` is a double normal
(`exists_isDoubleNormalDir`).

Proof: L2 (`exists_motion_iff`) realizes the field of L3
(`exists_admissible_inward_field`) for `û = J g / |g|`, which is not a double
normal of the shadow of `F₀` by L4 (`isDoubleNormalDir_proj_iff`); the shadow
of `conv V` equals that of `F₀`, and the points of `V \ W` project into its
interior. -/
theorem exists_firstOrderInward_of_coplanar (V W : Finset ℝ³) (hWV : W ⊆ V)
    (hW : ¬ Collinear ℝ (W : Set ℝ³)) (hview : ez ∈ admissibleViews V W)
    (hgen : ∀ δ : ℝ³, IsDoubleNormalDir (convexHull ℝ (W : Set ℝ³)) δ → δ 2 ≠ 0) :
    ∃ ω τ : ℝ³, FirstOrderInward V ω τ := by
  sorry

/-- **Theorem 5, precise form.**  At every admissible view `u` orthogonal to
no double normal of `F₀` there is a first-order passage; hence `V` is
Rupert. -/
theorem isRupert_of_generic_admissibleView (V W : Finset ℝ³) (hWV : W ⊆ V)
    (hW : ¬ Collinear ℝ (W : Set ℝ³)) (u : ℝ³) (hu : u ∈ admissibleViews V W)
    (hgen : ∀ δ : ℝ³, IsDoubleNormalDir (convexHull ℝ (W : Set ℝ³)) δ → ⟪δ, u⟫ ≠ 0) :
    IsRupert V := by
  sorry

/-- **Theorem 5 (coplanar-silhouette theorem).**  If some subset `W ⊆ V`,
not collinear, has an admissible view (`U_Π ≠ ∅` for `Π = affineSpan W`),
then `V` is Rupert. -/
theorem isRupert_of_admissibleViews_nonempty (V W : Finset ℝ³) (hWV : W ⊆ V)
    (hW : ¬ Collinear ℝ (W : Set ℝ³)) (hU : (admissibleViews V W).Nonempty) :
    IsRupert V := by
  obtain ⟨u, hu, hgen⟩ := exists_generic_admissibleView V W hW hU
  exact isRupert_of_generic_admissibleView V W hWV hW u hu hgen

end SmallRupert

end
