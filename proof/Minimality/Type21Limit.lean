module

public import Minimality.Type21Facets
public import Minimality.Type16Limit

@[expose] public section

/-!
# Type 21 outside the HDN set and codimension 2 (`FEWER-FACES-PROOFS.md` §18.6 step 2)

Every type-21 shape `K` is a limit of shapes `K_n` off the affine special positions of the tier
cover (`NoPlaneParallel`, the parallel clause of `GenPosTie`, the five planar equators, the far
sides of `T1` and of the vertex tests of F2: all polynomials in seven normal-form parameters),
with the same tie as `K` at the named views.  The cover (`cert_type21_facets`) gives each `K_n`
a rim certificate at a named view; a subsequence carries one labelled certificate, and the limit
lemma (`isRupert_of_tendsto_rimCert`) makes `K` Rupert unless the limit view has a horizontal
double normal.

* `Facets21`: the eight facets as `Face16` data; convex position (`Facets21.noSeg`), the frame
  `2; 0, 3, 6` (`Facets21.det_ne`), each facet function a multiple of a determinant
  (`Face16.eq_det`, `Facets21.exists_kappa`).
* `isRupert_of_rimCert`, `isRupert_type21_facets`: a rim certificate at a view without
  horizontal double normal gives Rupertness; Theorem 16.26 with the explicit special positions of
  `not_type21_of_isNopert`, re-derived from the certificate form.
* Normal-form shapes (`co21`, `nfShape21`, `Facets21.eq_nfShape`: `2 = 0`, `0 = e₁`, `3 = e₂`,
  `6 = e₃`, `5 = (p, 0, q)`, `4 = (0, r, s)`, `1 = (t, v, w)`), the special positions as one
  polynomial (`gen21`, `genPoly21`, nonzero by `decide` at an integer point, `genPoly21_ne_zero`).
* The named views (`view21`: the segments and the eight vertex crossings `vtx21`, nonzero for every
  type-21 shape: `Facets21.vtxView21_ne_zero`), ties at them (`TieInst21`, `SameTie21`,
  `OneTie21`); ties across views (`noTieAt_seg_of_tie`, `noTieAt_or`).
* `cert21_of_generic`: the cover at a generic normal-form shape whose ties are those of `K`.
* **`isRupert_type21_limit`**, `isRupert_type21_limit_facets`: a type-21 shape with at most one
  tie at its named views and no horizontal double normal at them is Rupert.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### Type 21 by its facets, indexed -/

/-- **Type 21 by its facets**: seven distinct points with the facets `014`, `015`, `0256`, `046`,
`134`, `135`, `2346`, `235` (functions zero on the facet and negative at the other points). -/
structure Facets21 (x : Fin 7 → ℝ³) where
  inj : Function.Injective x
  f014 : Face16 x {0, 1, 4}
  f015 : Face16 x {0, 1, 5}
  f0256 : Face16 x {0, 2, 5, 6}
  f046 : Face16 x {0, 4, 6}
  f134 : Face16 x {1, 3, 4}
  f135 : Face16 x {1, 3, 5}
  f2346 : Face16 x {2, 3, 4, 6}
  f235 : Face16 x {2, 3, 5}

/-- **Type 21 is in convex position**: each vertex is cut off by its facets. -/
theorem Facets21.noSeg {x : Fin 7 → ℝ³} (T : Facets21 x) :
    ∀ i j m : Fin 7, x m ≠ x i → x m ≠ x j → ∀ s : ℝ, 0 < s → s < 1 →
      x m ≠ x i + s • (x j - x i) := by
  intro i j m hmi hmj s hs0 hs1
  have hmi' : m ≠ i := fun h => hmi (by rw [h])
  have hmj' : m ≠ j := fun h => hmj (by rw [h])
  fin_cases m <;> fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hmi'
    | exact absurd rfl hmj'
    | exact T.f014.ne_seg (by decide) (by decide) s hs0 hs1
    | exact T.f015.ne_seg (by decide) (by decide) s hs0 hs1
    | exact T.f0256.ne_seg (by decide) (by decide) s hs0 hs1
    | exact T.f046.ne_seg (by decide) (by decide) s hs0 hs1
    | exact T.f134.ne_seg (by decide) (by decide) s hs0 hs1
    | exact T.f135.ne_seg (by decide) (by decide) s hs0 hs1
    | exact T.f2346.ne_seg (by decide) (by decide) s hs0 hs1
    | exact T.f235.ne_seg (by decide) (by decide) s hs0 hs1

/-- **The frame `2; 0, 3, 6` of type 21**: the facets `2346`, `0256`, `235` each vanish on three
of the four points. -/
theorem Facets21.det_ne {x : Fin 7 → ℝ³} (T : Facets21 x) :
    det3 (x 0 - x 2) (x 3 - x 2) (x 6 - x 2) ≠ 0 := by
  refine det3_ne_zero_of_affine3 T.f2346.hN T.f0256.hN T.f235.hN (x 2) (x 0) (x 3) (x 6) ?_
  rw [T.f2346.zero 2 (by decide), T.f2346.zero 3 (by decide), T.f2346.zero 6 (by decide),
    T.f0256.zero 0 (by decide), T.f0256.zero 2 (by decide), T.f0256.zero 6 (by decide),
    T.f235.zero 2 (by decide), T.f235.zero 3 (by decide)]
  have := mul_ne_zero (T.f2346.neg 0 (by decide)).ne
    (mul_ne_zero (T.f0256.neg 3 (by decide)).ne (T.f235.neg 6 (by decide)).ne)
  simp only [sub_zero, mul_zero, sub_self, zero_mul, add_zero]
  exact this

/-- The facets from affine functions. -/
noncomputable def Facets21.ofAffine (x : Fin 7 → ℝ³) (hx : Function.Injective x)
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
      (i ∉ ({2, 3, 5} : Finset (Fin 7)) → fH (x i) < 0)) : Facets21 x :=
  ⟨hx, Face16.ofAffine fA hA, Face16.ofAffine fB hB, Face16.ofAffine fC hC,
    Face16.ofAffine fD hD, Face16.ofAffine fE hE, Face16.ofAffine fF hF, Face16.ofAffine fG hG,
    Face16.ofAffine fH hH⟩

/-! ### From a certificate to Rupertness -/

/-- **A rim certificate at a view without horizontal double normal** makes a point set in convex
position, not in a plane, Rupert (Theorem 18.1 with 18.3, at the shape itself). -/
theorem isRupert_of_rimCert {n : ℕ} (x : Fin n → ℝ³)
    (hseg : ∀ i j m : Fin n, x m ≠ x i → x m ≠ x j → ∀ s : ℝ, 0 < s → s < 1 →
      x m ≠ x i + s • (x j - x i))
    (hsp : ∃ i j l m : Fin n, det3 (x j - x i) (x l - x i) (x m - x i) ≠ 0) {u : ℝ³}
    (hnd : NoHDNAt (univ.image x) u) (h : RimCert (univ.image x) u) : IsRupert (univ.image x) := by
  obtain ⟨k, hk, y, hy⟩ := h
  obtain ⟨lab, -, hat⟩ := hy.toAt
  have hk0 : NeZero k := ⟨by rcases hk with rfl | rfl | rfl <;> norm_num⟩
  exact isRupert_of_tendsto_rimCert x hseg hsp lab hat.ne_zero hnd (l := (⊤ : Filter Unit))
    (fun _ => x) (fun _ => u) (fun _ => tendsto_const_nhds) tendsto_const_nhds
    (Filter.frequently_top.mpr ⟨(), hat, fun _ _ h => h⟩)

/-- **Type 21 from its facets (Theorem 16.26)**, with the explicit special positions of
`not_type21_of_isNopert`: `NoPlaneParallel`, `GenPosTie`, no horizontal double normal at the
edge views, the five planar equators `{4, 5, 1, 6}`, `{0, 3, 1, 6}`, `{0, 3, 4, 5}`,
`{0, 3, 1, 2}`, `{4, 5, 1, 2}`, the special positions of `T1` at the four vertex crossings
(`T1View`) and those of the vertex tests of F2 in the four labellings (`F2Views`).  From the
certificate form `cert_type21_facets` (a rim certificate at a named view) with Theorems 18.1 and
18.3 at the shape itself. -/
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
    (hpp : NoPlaneParallel (univ.image x)) (hgen : GenPosTie (univ.image x))
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
  let T := Facets21.ofAffine x hx fA fB fC fD fE fF fG fH hA hB hC hD hE hF hG hH
  obtain ⟨u, hu, hcert⟩ := cert_type21_facets (L := NoHDNAt (univ.image x)) x hx fA fB fC fD fE
    fF fG fH hA hB hC hD hE hF hG hH hpp hgen hEq
    ⟨hT1.1.toL, hT1.2.1.toL, hT1.2.2.1.toL, hT1.2.2.2.toL⟩
    ⟨hF2.1.toL, hF2.2.1.toL, hF2.2.2.1.toL, hF2.2.2.2.toL⟩
  refine isRupert_of_rimCert x T.noSeg ⟨2, 0, 3, 6, T.det_ne⟩ ?_ hcert
  rcases hu with h | ⟨v, hv, w, hw, hvw, rfl⟩
  · exact h
  · exact noHDNAt_of_erase hvw (hnd v hv w hw hvw)
      (by simpa only [neg_sub] using (hnd w hw v hv (Ne.symm hvw)).neg)

/-! ### Normal-form shapes from parameters -/

/-- **The normal-form coordinates of type 21** over a commutative ring, in the frame
`2; 0, 3, 6`: `2 = 0`, `0 = e₁`, `3 = e₂`, `6 = e₃`, `5 = (p, 0, q)` (on `0256`), `4 = (0, r, s)`
(on `2346`), `1 = (t, v, w)`, with the parameters `θ = (p, q, r, s, t, v, w)`. -/
def co21 {R : Type*} [CommRing R] (θ : Fin 7 → R) : Fin 7 → Fin 3 → R :=
  ![![1, 0, 0], ![θ 4, θ 5, θ 6], ![0, 0, 0], ![0, 1, 0], ![0, θ 2, θ 3], ![θ 0, 0, θ 1],
    ![0, 0, 1]]

/-- The normal-form shape with parameters `θ` in the frame `o; E₁, E₂, E₃`. -/
noncomputable def nfShape21 (o E₁ E₂ E₃ : ℝ³) (θ : Fin 7 → ℝ) : Fin 7 → ℝ³ :=
  fun i => nfP o E₁ E₂ E₃ (co21 θ i 0) (co21 θ i 1) (co21 θ i 2)

/-- The determinant of three coordinate vectors over a commutative ring. -/
def dR {R : Type*} [CommRing R] (a b c : Fin 3 → R) : R :=
  a 0 * (b 1 * c 2 - b 2 * c 1) - a 1 * (b 0 * c 2 - b 2 * c 0) + a 2 * (b 0 * c 1 - b 1 * c 0)

/-- The direction of the line of the planes spanned by `a, b` and by `c, d`, in coordinates. -/
def plR {R : Type*} [CommRing R] (a b c d : Fin 3 → R) : Fin 3 → R :=
  fun k => dR a b d * c k - dR a b c * d k

/-- The squared length of the cross product, in coordinates. -/
def crSq {R : Type*} [CommRing R] (a b : Fin 3 → R) : R :=
  (a 1 * b 2 - a 2 * b 1) ^ 2 + (a 2 * b 0 - a 0 * b 2) ^ 2 + (a 0 * b 1 - a 1 * b 0) ^ 2

/-- `[j − i, k − i, m − l]` in normal-form coordinates. -/
def d21 {R : Type*} [CommRing R] (θ : Fin 7 → R) (i j k l m : Fin 7) : R :=
  dR (co21 θ j - co21 θ i) (co21 θ k - co21 θ i) (co21 θ m - co21 θ l)

/-- `|(j − i) × (l − k)|²` in normal-form coordinates. -/
def par21 {R : Type*} [CommRing R] (θ : Fin 7 → R) (i j k l : Fin 7) : R :=
  crSq (co21 θ j - co21 θ i) (co21 θ l - co21 θ k)

/-- **The eight vertex crossings** of the cover: the lines of the facet pairs `014/0256` (at
`0`), `014/2346` (at `4`), `135/0256` (at `5`), `135/2346` (at `3`), `046/134` (at `4`),
`046/015` (at `0`), `235/134` (at `3`), `235/015` (at `5`), each facet by three of its labels,
the common vertex first (as in the vertex tests of F2, `F2ViewsL`). -/
def vtx21 : Fin 8 → (Fin 7 × Fin 7 × Fin 7) × (Fin 7 × Fin 7 × Fin 7) :=
  ![((0, 4, 1), (0, 5, 6)), ((4, 0, 1), (4, 3, 6)), ((5, 3, 1), (5, 0, 2)),
    ((3, 5, 1), (3, 4, 2)), ((4, 0, 6), (4, 3, 1)), ((0, 4, 6), (0, 5, 1)),
    ((3, 5, 2), (3, 4, 1)), ((5, 3, 2), (5, 0, 1))]

/-- The `t`-th vertex crossing in normal-form coordinates. -/
def plv21 {R : Type*} [CommRing R] (θ : Fin 7 → R) (t : Fin 8) : Fin 3 → R :=
  plR (co21 θ (vtx21 t).1.2.1 - co21 θ (vtx21 t).1.1)
    (co21 θ (vtx21 t).1.2.2 - co21 θ (vtx21 t).1.1)
    (co21 θ (vtx21 t).2.2.1 - co21 θ (vtx21 t).2.1)
    (co21 θ (vtx21 t).2.2.2 - co21 θ (vtx21 t).2.1)

/-- The test `[Y − X, Z − X, u_t]` in normal-form coordinates. -/
def vt21 {R : Type*} [CommRing R] (θ : Fin 7 → R) (X Y Z : Fin 7) (t : Fin 8) : R :=
  dR (co21 θ Y - co21 θ X) (co21 θ Z - co21 θ X) (plv21 θ t)

/-- **The twelve far-side tests** of `T1` (four labellings) and of the two vertex tests of F2
(four labellings): `(X, Y, Z, t)` stands for `[Y − X, Z − X, u_t] ≠ 0`. -/
def tests21 : Fin 12 → Fin 7 × Fin 7 × Fin 7 × Fin 8 :=
  ![(5, 4, 3, 0), (3, 0, 5, 1), (0, 3, 4, 2), (4, 5, 0, 3),
    (2, 1, 5, 1), (3, 0, 5, 4), (2, 1, 3, 0), (5, 4, 3, 5),
    (6, 1, 0, 3), (4, 5, 0, 6), (6, 1, 4, 2), (0, 3, 4, 7)]

/-- The five planar equators `{4, 5, 1, 6}`, `{0, 3, 1, 6}`, `{0, 3, 4, 5}` (of `K − 2`),
`{0, 3, 1, 2}`, `{4, 5, 1, 2}` (of `K − 6`): `(i, j, k, m)` stands for `[j − i, k − i, m − i]`. -/
def eq21 : Fin 5 → Fin 7 × Fin 7 × Fin 7 × Fin 7 :=
  ![(4, 5, 1, 6), (0, 3, 1, 6), (0, 3, 4, 5), (3, 0, 1, 2), (5, 4, 1, 2)]

/-- The index condition of `NoPlaneParallel`. -/
def pp21 (τ : Fin 7 × Fin 7 × Fin 7 × Fin 7 × Fin 7) : Prop :=
  [τ.1, τ.2.1, τ.2.2.1, τ.2.2.2.1, τ.2.2.2.2].Nodup

instance (τ : Fin 7 × Fin 7 × Fin 7 × Fin 7 × Fin 7) : Decidable (pp21 τ) := by
  unfold pp21; infer_instance

/-- The index condition of the parallel clause of `GenPosTie`. -/
def pr21 (τ : Fin 7 × Fin 7 × Fin 7 × Fin 7) : Prop :=
  τ.1 ≠ τ.2.1 ∧ τ.2.2.1 ≠ τ.2.2.2 ∧
    ¬ ((τ.1 = τ.2.2.1 ∧ τ.2.1 = τ.2.2.2) ∨ (τ.1 = τ.2.2.2 ∧ τ.2.1 = τ.2.2.1))

instance (τ : Fin 7 × Fin 7 × Fin 7 × Fin 7) : Decidable (pr21 τ) := by
  unfold pr21; infer_instance

/-- **The special positions of the cover** as one product over a commutative ring: no plane of
three labels parallel to the segment of two others, no two segments parallel, the five planar
equators, the twelve far-side tests. -/
def gen21 {R : Type*} [CommRing R] (θ : Fin 7 → R) : R :=
  (∏ τ : Fin 7 × Fin 7 × Fin 7 × Fin 7 × Fin 7,
      if pp21 τ then d21 θ τ.1 τ.2.1 τ.2.2.1 τ.2.2.2.1 τ.2.2.2.2 else 1) *
    (∏ τ : Fin 7 × Fin 7 × Fin 7 × Fin 7,
      if pr21 τ then par21 θ τ.1 τ.2.1 τ.2.2.1 τ.2.2.2 else 1) *
    (∏ e : Fin 5, d21 θ (eq21 e).1 (eq21 e).2.1 (eq21 e).2.2.1 (eq21 e).1 (eq21 e).2.2.2) *
    (∏ e : Fin 12, vt21 θ (tests21 e).1 (tests21 e).2.1 (tests21 e).2.2.1 (tests21 e).2.2.2)

section Map

variable {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (θ : Fin 7 → R)

theorem map_co21 (i : Fin 7) (k : Fin 3) : φ (co21 θ i k) = co21 (φ ∘ θ) i k := by
  fin_cases i <;> fin_cases k <;> simp [co21]

theorem map_co21_sub (i j : Fin 7) : (fun k => φ ((co21 θ j - co21 θ i) k)) =
    co21 (φ ∘ θ) j - co21 (φ ∘ θ) i := by
  funext k; simp only [Pi.sub_apply, map_sub, map_co21]

theorem map_dR (a b c : Fin 3 → R) : φ (dR a b c) = dR (fun k => φ (a k)) (fun k => φ (b k))
    (fun k => φ (c k)) := by
  simp only [dR, map_add, map_sub, map_mul]

theorem map_d21 (i j k l m : Fin 7) : φ (d21 θ i j k l m) = d21 (φ ∘ θ) i j k l m := by
  simp only [d21, map_dR, map_co21_sub]

theorem map_par21 (i j k l : Fin 7) : φ (par21 θ i j k l) = par21 (φ ∘ θ) i j k l := by
  simp only [par21, crSq, map_add, map_sub, map_mul, map_pow]
  simp only [← map_co21_sub]

theorem map_plv21 (t : Fin 8) : (fun k => φ (plv21 θ t k)) = plv21 (φ ∘ θ) t := by
  funext k
  simp only [plv21, plR, map_sub, map_mul, map_dR, map_co21_sub]
  simp only [Pi.sub_apply, map_sub, map_co21]

theorem map_vt21 (X Y Z : Fin 7) (t : Fin 8) : φ (vt21 θ X Y Z t) = vt21 (φ ∘ θ) X Y Z t := by
  simp only [vt21, map_dR, map_co21_sub, map_plv21]

theorem map_gen21 : φ (gen21 θ) = gen21 (φ ∘ θ) := by
  simp only [gen21, map_mul, map_prod, apply_ite φ, map_one, map_d21, map_par21, map_vt21]

end Map

/-- An integer point off the special positions. -/
def thZ21 : Fin 7 → ℤ := ![-7, -9, 6, -1, 8, -2, -3]

theorem gen21_thZ_pp : ∀ i j k l m : Fin 7, [i, j, k, l, m].Nodup → d21 thZ21 i j k l m ≠ 0 := by
  decide +kernel

theorem gen21_thZ_pr : ∀ i j k l : Fin 7, i ≠ j → k ≠ l →
    ¬ ((i = k ∧ j = l) ∨ (i = l ∧ j = k)) → par21 thZ21 i j k l ≠ 0 := by
  decide +kernel

theorem gen21_thZ_eq : ∀ e : Fin 5,
    d21 thZ21 (eq21 e).1 (eq21 e).2.1 (eq21 e).2.2.1 (eq21 e).1 (eq21 e).2.2.2 ≠ 0 := by
  decide +kernel

theorem gen21_thZ_vt : ∀ e : Fin 12,
    vt21 thZ21 (tests21 e).1 (tests21 e).2.1 (tests21 e).2.2.1 (tests21 e).2.2.2 ≠ 0 := by
  decide +kernel

theorem gen21_thZ : gen21 thZ21 ≠ 0 := by
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_
  · refine Finset.prod_ne_zero_iff.mpr fun τ _ => ?_
    split_ifs with h
    · exact gen21_thZ_pp _ _ _ _ _ h
    · exact one_ne_zero
  · refine Finset.prod_ne_zero_iff.mpr fun τ _ => ?_
    split_ifs with h
    · exact gen21_thZ_pr _ _ _ _ h.1 h.2.1 h.2.2
    · exact one_ne_zero
  · exact Finset.prod_ne_zero_iff.mpr fun e _ => gen21_thZ_eq e
  · exact Finset.prod_ne_zero_iff.mpr fun e _ => gen21_thZ_vt e

open MvPolynomial in
/-- **The special positions of the cover as one polynomial** in the seven parameters. -/
noncomputable def genPoly21 : MvPolynomial (Fin 7) ℝ := gen21 (X : Fin 7 → MvPolynomial (Fin 7) ℝ)

theorem eval_genPoly21 (θ : Fin 7 → ℝ) : MvPolynomial.eval θ genPoly21 = gen21 θ := by
  rw [genPoly21, map_gen21]
  congr 1
  funext i
  simp

theorem genPoly21_ne_zero : genPoly21 ≠ 0 := by
  intro h
  have := congrArg (MvPolynomial.eval (fun i => (thZ21 i : ℝ))) h
  rw [eval_genPoly21, map_zero] at this
  have e : gen21 (fun i => (thZ21 i : ℝ)) = ((gen21 thZ21 : ℤ) : ℝ) := by
    rw [show (fun i => (thZ21 i : ℝ)) = (Int.castRingHom ℝ) ∘ thZ21 from rfl, ← map_gen21]
    rfl
  rw [e] at this
  exact gen21_thZ (by exact_mod_cast this)

/-! ### Shapes in the frame -/

theorem nfShape21_sub (o E₁ E₂ E₃ : ℝ³) (θ : Fin 7 → ℝ) (i j : Fin 7) :
    nfShape21 o E₁ E₂ E₃ θ j - nfShape21 o E₁ E₂ E₃ θ i =
      nfV E₁ E₂ E₃ (co21 θ j 0 - co21 θ i 0) (co21 θ j 1 - co21 θ i 1)
        (co21 θ j 2 - co21 θ i 2) :=
  nfP_sub _ _ _ _ _ _ _ _ _ _

theorem det3_nfShape21 (o E₁ E₂ E₃ : ℝ³) (θ : Fin 7 → ℝ) (i j k l m : Fin 7) :
    det3 (nfShape21 o E₁ E₂ E₃ θ j - nfShape21 o E₁ E₂ E₃ θ i)
      (nfShape21 o E₁ E₂ E₃ θ k - nfShape21 o E₁ E₂ E₃ θ i)
      (nfShape21 o E₁ E₂ E₃ θ m - nfShape21 o E₁ E₂ E₃ θ l) =
      d21 θ i j k l m * det3 E₁ E₂ E₃ := by
  rw [nfShape21_sub, nfShape21_sub, nfShape21_sub, det3_nfV]
  simp only [d21, dR, det3c, Pi.sub_apply]

/-- The view along the `t`-th vertex crossing. -/
noncomputable def vtxView21 (x : Fin 7 → ℝ³) (t : Fin 8) : ℝ³ :=
  planeLine (x (vtx21 t).1.1) (x (vtx21 t).1.2.1) (x (vtx21 t).1.2.2) (x (vtx21 t).2.1)
    (x (vtx21 t).2.2.1) (x (vtx21 t).2.2.2)

/-- **The named views of type 21**: the segments and the eight vertex crossings. -/
noncomputable def view21 (x : Fin 7 → ℝ³) : (Fin 7 × Fin 7) ⊕ Fin 8 → ℝ³
  | .inl ij => x ij.2 - x ij.1
  | .inr t => vtxView21 x t

theorem vtxView21_nfShape (o E₁ E₂ E₃ : ℝ³) (θ : Fin 7 → ℝ) (t : Fin 8) :
    vtxView21 (nfShape21 o E₁ E₂ E₃ θ) t =
      det3 E₁ E₂ E₃ • nfV E₁ E₂ E₃ (plv21 θ t 0) (plv21 θ t 1) (plv21 θ t 2) := by
  simp only [vtxView21, planeLine]
  rw [det3_nfShape21, det3_nfShape21, nfShape21_sub, nfShape21_sub]
  simp only [nfV, plv21, plR, d21, Pi.sub_apply]
  ext k
  simp only [PiLp.sub_apply, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
  ring

theorem det3_vtx_nfShape21 (o E₁ E₂ E₃ : ℝ³) (θ : Fin 7 → ℝ) (X Y Z : Fin 7) (t : Fin 8) :
    det3 (nfShape21 o E₁ E₂ E₃ θ Y - nfShape21 o E₁ E₂ E₃ θ X)
      (nfShape21 o E₁ E₂ E₃ θ Z - nfShape21 o E₁ E₂ E₃ θ X)
      (vtxView21 (nfShape21 o E₁ E₂ E₃ θ) t) =
      det3 E₁ E₂ E₃ * (vt21 θ X Y Z t * det3 E₁ E₂ E₃) := by
  rw [vtxView21_nfShape, det3_smul_right, nfShape21_sub, nfShape21_sub, det3_nfV]
  simp only [vt21, dR, det3c, Pi.sub_apply]

/-- The line of two planes as a cross product of their normals. -/
theorem planeLine_eq_cross (p₀ p₁ p₂ q₀ q₁ q₂ : ℝ³) :
    planeLine p₀ p₁ p₂ q₀ q₁ q₂ =
      cross (cross (p₁ - p₀) (p₂ - p₀)) (cross (q₁ - q₀) (q₂ - q₀)) := by
  ext i; fin_cases i <;>
    simp only [planeLine, det3_expand, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      cross_apply_zero, cross_apply_one, cross_apply_two, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul] <;> ring

/-- **A direction of a vertex crossing is a multiple of its named view**, and a test that is
nonzero at the named view is nonzero at it. -/
theorem vtxView21_of_perp (y : Fin 7 → ℝ³) (t : Fin 8) {X Y Z : Fin 7} {u : ℝ³} (hu : u ≠ 0)
    (h₁ : det3 (y (vtx21 t).1.2.1 - y (vtx21 t).1.1) (y (vtx21 t).1.2.2 - y (vtx21 t).1.1) u = 0)
    (h₂ : det3 (y (vtx21 t).2.2.1 - y (vtx21 t).2.1) (y (vtx21 t).2.2.2 - y (vtx21 t).2.1) u = 0)
    (hT : det3 (y Y - y X) (y Z - y X) (vtxView21 y t) ≠ 0) :
    (∃ c : ℝ, c ≠ 0 ∧ u = c • vtxView21 y t) ∧ det3 (y Y - y X) (y Z - y X) u ≠ 0 := by
  have e := planeLine_eq_cross (y (vtx21 t).1.1) (y (vtx21 t).1.2.1) (y (vtx21 t).1.2.2)
    (y (vtx21 t).2.1) (y (vtx21 t).2.2.1) (y (vtx21 t).2.2.2)
  have hv : vtxView21 y t ≠ 0 := by
    intro h0; rw [h0] at hT; simp [det3] at hT
  rw [show vtxView21 y t = _ from e] at hv hT ⊢
  obtain ⟨c, rfl⟩ := eq_smul_cross_of_perp hv (by rw [real_inner_comm]; exact h₁)
    (by rw [real_inner_comm]; exact h₂)
  have hc : c ≠ 0 := by rintro rfl; exact hu (zero_smul _ _)
  exact ⟨⟨c, hc, rfl⟩, by rw [det3_smul_right]; exact mul_ne_zero hc hT⟩

/-! ### The normal form of a type-21 shape -/

/-- A facet's normal is nonzero, so three vectors along the facet are dependent. -/
theorem Face16.det_eq_zero {x : Fin 7 → ℝ³} {S : Finset (Fin 7)} (F : Face16 x S) {m : Fin 7}
    (hm : m ∉ S) {a b c d e f : Fin 7} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S)
    (he : e ∈ S) (hf : f ∈ S) : det3 (x b - x a) (x d - x c) (x f - x e) = 0 := by
  have hN : F.N ≠ 0 := by
    intro h
    have := F.hN (x m) (x a)
    rw [h, inner_zero_left, F.zero a ha, sub_zero] at this
    linarith [F.neg m hm]
  refine det3_eq_zero_of_perp hN ?_ ?_ ?_
  · rw [real_inner_comm]; exact F.inner_sub hb ha
  · rw [real_inner_comm]; exact F.inner_sub hd hc
  · rw [real_inner_comm]; exact F.inner_sub hf he

/-- The normal-form parameters of a type-21 shape: Cramer coordinates of `5`, `4`, `1` in the
frame `2; 0, 3, 6`. -/
noncomputable def theta21 (x : Fin 7 → ℝ³) : Fin 7 → ℝ :=
  ![det3 (x 5 - x 2) (x 3 - x 2) (x 6 - x 2) / det3 (x 0 - x 2) (x 3 - x 2) (x 6 - x 2),
    det3 (x 0 - x 2) (x 3 - x 2) (x 5 - x 2) / det3 (x 0 - x 2) (x 3 - x 2) (x 6 - x 2),
    det3 (x 0 - x 2) (x 4 - x 2) (x 6 - x 2) / det3 (x 0 - x 2) (x 3 - x 2) (x 6 - x 2),
    det3 (x 0 - x 2) (x 3 - x 2) (x 4 - x 2) / det3 (x 0 - x 2) (x 3 - x 2) (x 6 - x 2),
    det3 (x 1 - x 2) (x 3 - x 2) (x 6 - x 2) / det3 (x 0 - x 2) (x 3 - x 2) (x 6 - x 2),
    det3 (x 0 - x 2) (x 1 - x 2) (x 6 - x 2) / det3 (x 0 - x 2) (x 3 - x 2) (x 6 - x 2),
    det3 (x 0 - x 2) (x 3 - x 2) (x 1 - x 2) / det3 (x 0 - x 2) (x 3 - x 2) (x 6 - x 2)]

/-- **Every type-21 shape is a normal-form shape** in the frame `2; 0, 3, 6`: `5` lies on the plane
of `0256`, `4` on the plane of `2346`. -/
theorem Facets21.eq_nfShape {x : Fin 7 → ℝ³} (T : Facets21 x) :
    x = nfShape21 (x 2) (x 0 - x 2) (x 3 - x 2) (x 6 - x 2) (theta21 x) := by
  have hD := T.det_ne
  have h5 : det3 (x 0 - x 2) (x 5 - x 2) (x 6 - x 2) = 0 := by
    rw [det3_swap23]
    rw [T.f0256.det_eq_zero (m := 1) (by decide) (a := 2) (b := 0) (c := 2) (d := 6) (e := 2)
      (f := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), neg_zero]
  have h4 : det3 (x 4 - x 2) (x 3 - x 2) (x 6 - x 2) = 0 := by
    have e : det3 (x 4 - x 2) (x 3 - x 2) (x 6 - x 2) = det3 (x 3 - x 2) (x 6 - x 2) (x 4 - x 2) :=
        by
      simp only [det3_expand, PiLp.sub_apply]; ring
    rw [e, T.f2346.det_eq_zero (m := 0) (by decide) (a := 2) (b := 3) (c := 2) (d := 6) (e := 2)
      (f := 4) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  funext i
  fin_cases i
  · show x 0 = nfP (x 2) (x 0 - x 2) (x 3 - x 2) (x 6 - x 2) 1 0 0
    simp only [nfP, one_smul, zero_smul, add_zero]; abel
  · show x 1 = nfP (x 2) (x 0 - x 2) (x 3 - x 2) (x 6 - x 2) _ _ _
    exact eq_nfP_cramer hD (x 1)
  · show x 2 = nfP (x 2) (x 0 - x 2) (x 3 - x 2) (x 6 - x 2) 0 0 0
    simp only [nfP, zero_smul, add_zero]
  · show x 3 = nfP (x 2) (x 0 - x 2) (x 3 - x 2) (x 6 - x 2) 0 1 0
    simp only [nfP, one_smul, zero_smul, add_zero]; abel
  · have hc := eq_nfP_cramer (o := x 2) hD (x 4)
    rw [h4, zero_div] at hc
    exact hc
  · have hc := eq_nfP_cramer (o := x 2) hD (x 5)
    rw [h5, zero_div] at hc
    exact hc
  · show x 6 = nfP (x 2) (x 0 - x 2) (x 3 - x 2) (x 6 - x 2) 0 0 1
    simp only [nfP, one_smul, zero_smul, add_zero]; abel

theorem tendsto_nfShape21 {ι : Type*} {l : Filter ι} {o E₁ E₂ E₃ : ι → ℝ³} {o₀ F₁ F₂ F₃ : ℝ³}
    {θ : ι → Fin 7 → ℝ} {θ₀ : Fin 7 → ℝ} (ho : Tendsto o l (𝓝 o₀))
    (h₁ : Tendsto E₁ l (𝓝 F₁)) (h₂ : Tendsto E₂ l (𝓝 F₂)) (h₃ : Tendsto E₃ l (𝓝 F₃))
    (hθ : Tendsto θ l (𝓝 θ₀)) (i : Fin 7) :
    Tendsto (fun t => nfShape21 (o t) (E₁ t) (E₂ t) (E₃ t) (θ t) i) l
      (𝓝 (nfShape21 o₀ F₁ F₂ F₃ θ₀ i)) := by
  have cj : ∀ j, Tendsto (fun t => θ t j) l (𝓝 (θ₀ j)) := fun j =>
    ((continuous_apply j).tendsto θ₀).comp hθ
  have c : ∀ k, Tendsto (fun t => co21 (θ t) i k) l (𝓝 (co21 θ₀ i k)) := by
    intro k
    fin_cases i <;> fin_cases k <;> simp only [co21] <;>
      first | exact tendsto_const_nhds | exact cj _
  exact tendsto_nfP ho h₁ h₂ h₃ (c 0) (c 1) (c 2)

theorem restore_nfShape21 (s : ℝ) (e b o E₁ E₂ E₃ : ℝ³) (θ : Fin 7 → ℝ) :
    (fun i => restore s e b (nfShape21 o E₁ E₂ E₃ θ i)) =
      nfShape21 (restore s e b o) (restore s e b E₁) (restore s e b E₂) (restore s e b E₃) θ := by
  funext i; exact restore_nfP s e b o E₁ E₂ E₃ _ _ _

/-! ### Named views and ties -/

theorem view21_restore {s : ℝ} {e b : ℝ³} (h : ⟪e, b⟫ = 0) (y : Fin 7 → ℝ³)
    (v : (Fin 7 × Fin 7) ⊕ Fin 8) :
    view21 (fun i => restore s e b (y i)) v = restore s e b (view21 y v) := by
  rcases v with ⟨i, j⟩ | t
  · exact (restore_sub s e b _ _).symm
  · exact planeLine_restore h _ _ _ _ _ _

theorem tendsto_view21 {ι : Type*} {l : Filter ι} {K : ι → Fin 7 → ℝ³} {x : Fin 7 → ℝ³}
    (hK : ∀ m, Tendsto (fun n => K n m) l (𝓝 (x m))) (v : (Fin 7 × Fin 7) ⊕ Fin 8) :
    Tendsto (fun n => view21 (K n) v) l (𝓝 (view21 x v)) := by
  rcases v with ⟨i, j⟩ | t
  · exact (hK j).sub (hK i)
  · exact tendsto_planeLine (hK _) (hK _) (hK _) (hK _) (hK _) (hK _)

/-- A tie at a named view: two labels `s ≠ t` at equal depth along a nonzero named view. -/
def TieInst21 (x : Fin 7 → ℝ³) (v : (Fin 7 × Fin 7) ⊕ Fin 8) (s t : Fin 7) : Prop :=
  s ≠ t ∧ view21 x v ≠ 0 ∧ ⟪x s - x t, view21 x v⟫ = 0

/-- Two ties that are one equation for every shape: the same view (up to reversing a segment)
and the same pair, or the tie of `s, t` along `i j` and the tie of `i, j` along `s t`. -/
def SameTie21 (v : (Fin 7 × Fin 7) ⊕ Fin 8) (s t : Fin 7) (v' : (Fin 7 × Fin 7) ⊕ Fin 8)
    (s' t' : Fin 7) : Prop :=
  ((v' = v ∨ ∃ i j, v = .inl (i, j) ∧ v' = .inl (j, i)) ∧
      ((s' = s ∧ t' = t) ∨ (s' = t ∧ t' = s))) ∨
    ∃ i j, v = .inl (i, j) ∧ (v' = .inl (s, t) ∨ v' = .inl (t, s)) ∧
      ((s' = i ∧ t' = j) ∨ (s' = j ∧ t' = i))

/-- **At most one tie** at the named views of `x` (18.6, conservatively: over all named
views, not only the rims of one certificate): any two ties are one equation.  Two ties that are
not one equation are two conditions on the shape, so this fails only in codimension 2. -/
def OneTie21 (x : Fin 7 → ℝ³) : Prop :=
  ∀ v s t v' s' t', TieInst21 x v s t → TieInst21 x v' s' t' → SameTie21 v s t v' s' t'

/-- One equation holds at every shape where the other does. -/
theorem SameTie21.inner_eq_zero {v : (Fin 7 × Fin 7) ⊕ Fin 8} {s t : Fin 7}
    {v' : (Fin 7 × Fin 7) ⊕ Fin 8} {s' t' : Fin 7} (h : SameTie21 v s t v' s' t')
    (y : Fin 7 → ℝ³) (h0 : ⟪y s - y t, view21 y v⟫ = 0) : ⟪y s' - y t', view21 y v'⟫ = 0 := by
  rcases h with ⟨hv, hp⟩ | ⟨i, j, rfl, hv', hp⟩
  · have hv'' : view21 y v' = view21 y v ∨ view21 y v' = -view21 y v := by
      rcases hv with rfl | ⟨i, j, rfl, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (by simp only [view21, neg_sub])
    have hp' : y s' - y t' = y s - y t ∨ y s' - y t' = -(y s - y t) := by
      rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (neg_sub _ _).symm
    rcases hv'' with e | e <;> rcases hp' with f | f <;>
      simp only [e, f, inner_neg_left, inner_neg_right, h0, neg_zero]
  · simp only [view21] at h0
    rw [inner_coords] at h0
    rcases hv' with rfl | rfl <;> rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [view21] <;> rw [inner_coords] <;>
      simp only [PiLp.sub_apply] at h0 ⊢ <;>
      first | linear_combination h0 | linear_combination -h0

/-- **At most one tie at a named view** of a shape whose ties are ties of `x`. -/
theorem oneTieAt_of_ties21 {x y : Fin 7 → ℝ³} (htie : OneTie21 x)
    (hsub : ∀ v a b, a ≠ b → view21 y v ≠ 0 → ⟪y a - y b, view21 y v⟫ = 0 → TieInst21 x v a b)
    (v : (Fin 7 × Fin 7) ⊕ Fin 8) (hv : view21 y v ≠ 0) :
    OneTieAt (univ.image y) (view21 y v) := by
  intro s hs t ht s' hs' t' ht' hst hst' e1 e2
  obtain ⟨a, -, rfl⟩ := mem_image.mp hs
  obtain ⟨b, -, rfl⟩ := mem_image.mp ht
  obtain ⟨a', -, rfl⟩ := mem_image.mp hs'
  obtain ⟨b', -, rfl⟩ := mem_image.mp ht'
  have hab : a ≠ b := fun h => hst (by rw [h])
  have hab' : a' ≠ b' := fun h => hst' (by rw [h])
  have t1 := hsub v a b hab hv (by rw [inner_sub_left, e1, sub_self])
  have t2 := hsub v a' b' hab' hv (by rw [inner_sub_left, e2, sub_self])
  rcases htie v a b v a' b' t1 t2 with ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨i, j, rfl, hv', -⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exfalso
    obtain ⟨-, hne, h0⟩ := t1
    have hij : (i = a ∧ j = b) ∨ (i = b ∧ j = a) := by
      rcases hv' with h | h
      · simp only [Sum.inl.injEq, Prod.mk.injEq] at h; exact Or.inl h
      · simp only [Sum.inl.injEq, Prod.mk.injEq] at h; exact Or.inr h
    have hne' : x j - x i ≠ 0 := hne
    have h0' : ⟪x a - x b, x j - x i⟫ = 0 := h0
    rcases hij with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2] at hne' h0'
      rw [← neg_sub, inner_neg_left, neg_eq_zero] at h0'
      exact hne' (inner_self_eq_zero.mp h0')
    · rw [h1, h2] at hne' h0'
      exact hne' (inner_self_eq_zero.mp h0')

/-- **Strict comparisons persist**: eventually every tie of `K_n` at a named view is a tie of the
limit `x`. -/
theorem eventually_ties21 {x : Fin 7 → ℝ³} {K : ℕ → Fin 7 → ℝ³}
    (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m))) :
    ∀ᶠ n in atTop, ∀ v a b, ⟪K n a - K n b, view21 (K n) v⟫ = 0 →
      ⟪x a - x b, view21 x v⟫ = 0 := by
  have h : ∀ q : ((Fin 7 × Fin 7) ⊕ Fin 8) × Fin 7 × Fin 7, ∀ᶠ n in atTop,
      ⟪K n q.2.1 - K n q.2.2, view21 (K n) q.1⟫ = 0 → ⟪x q.2.1 - x q.2.2, view21 x q.1⟫ = 0 := by
    rintro ⟨v, a, b⟩
    by_cases h0 : ⟪x a - x b, view21 x v⟫ = 0
    · exact Eventually.of_forall fun _ _ => h0
    · exact ((((hK a).sub (hK b)).inner (tendsto_view21 hK v)).eventually_ne h0).mono
        fun n hn h => absurd h hn
  filter_upwards [eventually_all.mpr h] with n hn v a b h
  exact hn (v, a, b) h

/-! ### The named views of a type-21 shape are nonzero -/

/-- **Two facets through a common vertex have a nonzero line**: if the normals were parallel,
the facet `P` would vanish on the facet `Q`. -/
theorem planeLine_ne_zero_of_faces {x : Fin 7 → ℝ³} {SP SQ : Finset (Fin 7)} (FP : Face16 x SP)
    (FQ : Face16 x SQ) {p₀ p₁ p₂ q₁ q₂ m n : Fin 7} (h0P : p₀ ∈ SP) (h1 : p₁ ∈ SP) (h2 : p₂ ∈ SP)
    (h0Q : p₀ ∈ SQ) (hq1 : q₁ ∈ SQ) (hq2 : q₂ ∈ SQ) (hmQ : m ∈ SQ) (hmP : m ∉ SP) (hn : n ∉ SQ)
    (hc1 : cross (x p₁ - x p₀) (x p₂ - x p₀) ≠ 0) (hc2 : cross (x q₁ - x p₀) (x q₂ - x p₀) ≠ 0) :
    planeLine (x p₀) (x p₁) (x p₂) (x p₀) (x q₁) (x q₂) ≠ 0 := by
  rw [planeLine_eq_cross]
  set e₁ := cross (x p₁ - x p₀) (x p₂ - x p₀) with he₁
  set e₂ := cross (x q₁ - x p₀) (x q₂ - x p₀) with he₂
  intro h0
  have hNQ : FQ.N = (⟪FQ.N, e₂⟫ / ⟪e₂, e₂⟫) • e₂ := eq_smul_of_cross_eq_zero hc2 (by
    rw [he₂, cross_cross_eq, real_inner_comm, FQ.inner_sub hq1 h0Q, real_inner_comm,
      FQ.inner_sub hq2 h0Q, zero_smul, zero_smul, sub_zero])
  have hNP : FP.N = (⟪FP.N, e₁⟫ / ⟪e₁, e₁⟫) • e₁ := eq_smul_of_cross_eq_zero hc1 (by
    rw [he₁, cross_cross_eq, real_inner_comm, FP.inner_sub h1 h0P, real_inner_comm,
      FP.inner_sub h2 h0P, zero_smul, zero_smul, sub_zero])
  have he : e₂ = (⟪e₂, e₁⟫ / ⟪e₁, e₁⟫) • e₁ := eq_smul_of_cross_eq_zero hc1 h0
  set c := ⟪FQ.N, e₂⟫ / ⟪e₂, e₂⟫ * (⟪e₂, e₁⟫ / ⟪e₁, e₁⟫) with hc
  have hNQ' : FQ.N = c • e₁ := by
    calc FQ.N = (⟪FQ.N, e₂⟫ / ⟪e₂, e₂⟫) • e₂ := hNQ
      _ = (⟪FQ.N, e₂⟫ / ⟪e₂, e₂⟫) • ((⟪e₂, e₁⟫ / ⟪e₁, e₁⟫) • e₁) := by rw [← he]
      _ = c • e₁ := by rw [smul_smul]
  have hc0 : c ≠ 0 := by
    intro h
    have k := FQ.hN (x n) (x p₀)
    rw [hNQ', h, zero_smul, inner_zero_left, FQ.zero p₀ h0Q, sub_zero] at k
    linarith [FQ.neg n hn]
  have k1 := FQ.hN (x m) (x p₀)
  rw [hNQ', real_inner_smul_left, FQ.zero m hmQ, FQ.zero p₀ h0Q, sub_self] at k1
  have k2 : ⟪e₁, x m - x p₀⟫ = 0 := (mul_eq_zero.mp k1.symm).resolve_left hc0
  have k3 := FP.hN (x m) (x p₀)
  rw [hNP, real_inner_smul_left, k2, mul_zero, FP.zero p₀ h0P, sub_zero] at k3
  linarith [FP.neg m hmP]

/-- **The vertex crossings of a type-21 shape are nonzero views.** -/
theorem Facets21.vtxView21_ne_zero {x : Fin 7 → ℝ³} (T : Facets21 x) (t : Fin 8) :
    vtxView21 x t ≠ 0 := by
  have ne : ∀ {i j : Fin 7}, i ≠ j → x i ≠ x j := fun h => T.inj.ne h
  fin_cases t
  · show planeLine (x 0) (x 4) (x 1) (x 0) (x 5) (x 6) ≠ 0
    exact planeLine_ne_zero_of_faces T.f014 T.f0256 (m := 5) (n := 1) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (cross_ne_zero_of_affine T.f046.hN (ne (by decide)) (T.f046.zero 0 (by decide))
        (T.f046.zero 4 (by decide)) (T.f046.neg 1 (by decide)))
      (cross_ne_zero_of_affine T.f015.hN (ne (by decide)) (T.f015.zero 0 (by decide))
        (T.f015.zero 5 (by decide)) (T.f015.neg 6 (by decide)))
  · show planeLine (x 4) (x 0) (x 1) (x 4) (x 3) (x 6) ≠ 0
    exact planeLine_ne_zero_of_faces T.f014 T.f2346 (m := 3) (n := 0) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (cross_ne_zero_of_affine T.f046.hN (ne (by decide)) (T.f046.zero 4 (by decide))
        (T.f046.zero 0 (by decide)) (T.f046.neg 1 (by decide)))
      (cross_ne_zero_of_affine T.f134.hN (ne (by decide)) (T.f134.zero 4 (by decide))
        (T.f134.zero 3 (by decide)) (T.f134.neg 6 (by decide)))
  · show planeLine (x 5) (x 3) (x 1) (x 5) (x 0) (x 2) ≠ 0
    exact planeLine_ne_zero_of_faces T.f135 T.f0256 (m := 0) (n := 1) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (cross_ne_zero_of_affine T.f235.hN (ne (by decide)) (T.f235.zero 5 (by decide))
        (T.f235.zero 3 (by decide)) (T.f235.neg 1 (by decide)))
      (cross_ne_zero_of_affine T.f015.hN (ne (by decide)) (T.f015.zero 5 (by decide))
        (T.f015.zero 0 (by decide)) (T.f015.neg 2 (by decide)))
  · show planeLine (x 3) (x 5) (x 1) (x 3) (x 4) (x 2) ≠ 0
    exact planeLine_ne_zero_of_faces T.f135 T.f2346 (m := 4) (n := 0) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (cross_ne_zero_of_affine T.f235.hN (ne (by decide)) (T.f235.zero 3 (by decide))
        (T.f235.zero 5 (by decide)) (T.f235.neg 1 (by decide)))
      (cross_ne_zero_of_affine T.f134.hN (ne (by decide)) (T.f134.zero 3 (by decide))
        (T.f134.zero 4 (by decide)) (T.f134.neg 2 (by decide)))
  · show planeLine (x 4) (x 0) (x 6) (x 4) (x 3) (x 1) ≠ 0
    exact planeLine_ne_zero_of_faces T.f046 T.f134 (m := 3) (n := 0) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (cross_ne_zero_of_affine T.f014.hN (ne (by decide)) (T.f014.zero 4 (by decide))
        (T.f014.zero 0 (by decide)) (T.f014.neg 6 (by decide)))
      (cross_ne_zero_of_affine T.f2346.hN (ne (by decide)) (T.f2346.zero 4 (by decide))
        (T.f2346.zero 3 (by decide)) (T.f2346.neg 1 (by decide)))
  · show planeLine (x 0) (x 4) (x 6) (x 0) (x 5) (x 1) ≠ 0
    exact planeLine_ne_zero_of_faces T.f046 T.f015 (m := 5) (n := 2) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (cross_ne_zero_of_affine T.f014.hN (ne (by decide)) (T.f014.zero 0 (by decide))
        (T.f014.zero 4 (by decide)) (T.f014.neg 6 (by decide)))
      (cross_ne_zero_of_affine T.f0256.hN (ne (by decide)) (T.f0256.zero 0 (by decide))
        (T.f0256.zero 5 (by decide)) (T.f0256.neg 1 (by decide)))
  · show planeLine (x 3) (x 5) (x 2) (x 3) (x 4) (x 1) ≠ 0
    exact planeLine_ne_zero_of_faces T.f235 T.f134 (m := 4) (n := 0) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (cross_ne_zero_of_affine T.f135.hN (ne (by decide)) (T.f135.zero 3 (by decide))
        (T.f135.zero 5 (by decide)) (T.f135.neg 2 (by decide)))
      (cross_ne_zero_of_affine T.f2346.hN (ne (by decide)) (T.f2346.zero 3 (by decide))
        (T.f2346.zero 4 (by decide)) (T.f2346.neg 1 (by decide)))
  · show planeLine (x 5) (x 3) (x 2) (x 5) (x 0) (x 1) ≠ 0
    exact planeLine_ne_zero_of_faces T.f235 T.f015 (m := 0) (n := 2) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (cross_ne_zero_of_affine T.f135.hN (ne (by decide)) (T.f135.zero 5 (by decide))
        (T.f135.zero 3 (by decide)) (T.f135.neg 2 (by decide)))
      (cross_ne_zero_of_affine T.f0256.hN (ne (by decide)) (T.f0256.zero 5 (by decide))
        (T.f0256.zero 0 (by decide)) (T.f0256.neg 1 (by decide)))

/-- **The named views of a type-21 shape are nonzero** (except the degenerate segments). -/
theorem Facets21.view21_ne_zero {x : Fin 7 → ℝ³} (T : Facets21 x) (v : (Fin 7 × Fin 7) ⊕ Fin 8)
    (hv : ∀ i, v ≠ .inl (i, i)) : view21 x v ≠ 0 := by
  rcases v with ⟨i, j⟩ | t
  · have hij : i ≠ j := fun h => hv i (by rw [h])
    exact sub_ne_zero.mpr (T.inj.ne hij.symm)
  · exact T.vtxView21_ne_zero t

/-! ### Facet functions of nearby shapes -/

/-- The affine function `y ↦ κ [Q − P, R − P, y − P]`. -/
noncomputable def detAff (κ : ℝ) (P Q R : ℝ³) : ℝ³ →ᵃ[ℝ] ℝ where
  toFun y := κ * det3 (Q - P) (R - P) (y - P)
  linear :=
    { toFun := fun u => κ * det3 (Q - P) (R - P) u
      map_add' := fun u v => by simp only [det3_expand, PiLp.add_apply]; ring
      map_smul' := fun c u => by
        simp only [det3_smul_right, smul_eq_mul, RingHom.id_apply]; ring }
  map_vadd' p v := by
    simp only [vadd_eq_add, LinearMap.coe_mk, AddHom.coe_mk, det3_expand, PiLp.add_apply,
      PiLp.sub_apply]
    ring

theorem detAff_apply (κ : ℝ) (P Q R y : ℝ³) :
    detAff κ P Q R y = κ * det3 (Q - P) (R - P) (y - P) := rfl

theorem detAff_linear (κ : ℝ) (P Q R u : ℝ³) :
    (detAff κ P Q R).linear u = κ * det3 (Q - P) (R - P) u := rfl

/-- **A facet function is a multiple of the determinant** through three non-collinear points of
the facet. -/
theorem Face16.eq_det {x : Fin 7 → ℝ³} {S : Finset (Fin 7)} (F : Face16 x S) {P Q R : Fin 7}
    (hP : P ∈ S) (hQ : Q ∈ S) (hR : R ∈ S) (hc : cross (x Q - x P) (x R - x P) ≠ 0) :
    ∃ κ : ℝ, ∀ y, F.f y = κ * det3 (x Q - x P) (x R - x P) (y - x P) := by
  set e := cross (x Q - x P) (x R - x P) with he
  have hN : F.N = (⟪F.N, e⟫ / ⟪e, e⟫) • e := eq_smul_of_cross_eq_zero hc (by
    rw [he, cross_cross_eq, real_inner_comm, F.inner_sub hQ hP, real_inner_comm,
      F.inner_sub hR hP, zero_smul, zero_smul, sub_zero])
  refine ⟨⟪F.N, e⟫ / ⟪e, e⟫, fun y => ?_⟩
  have k := F.hN y (x P)
  rw [F.zero P hP, sub_zero, hN, real_inner_smul_left] at k
  rw [k]; rfl

/-! ### Generic normal-form shapes -/

section Generic

variable {o E₁ E₂ E₃ : ℝ³} {θ : Fin 7 → ℝ}

theorem gen21_pp (h : gen21 θ ≠ 0) {i j k l m : Fin 7} (hn : [i, j, k, l, m].Nodup) :
    d21 θ i j k l m ≠ 0 := by
  have h1 := left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul h))
  have := Finset.prod_ne_zero_iff.mp h1 (i, j, k, l, m) (mem_univ _)
  simpa only [show pp21 (i, j, k, l, m) from hn, ite_true] using this

theorem gen21_pr (h : gen21 θ ≠ 0) {i j k l : Fin 7} (h1 : i ≠ j) (h2 : k ≠ l)
    (h3 : ¬ ((i = k ∧ j = l) ∨ (i = l ∧ j = k))) : par21 θ i j k l ≠ 0 := by
  have h' := right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul h))
  have := Finset.prod_ne_zero_iff.mp h' (i, j, k, l) (mem_univ _)
  simpa only [show pr21 (i, j, k, l) from ⟨h1, h2, h3⟩, ite_true] using this

theorem gen21_eq (h : gen21 θ ≠ 0) (e : Fin 5) :
    d21 θ (eq21 e).1 (eq21 e).2.1 (eq21 e).2.2.1 (eq21 e).1 (eq21 e).2.2.2 ≠ 0 :=
  Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul (left_ne_zero_of_mul h)) e (mem_univ _)

theorem gen21_vt (h : gen21 θ ≠ 0) (e : Fin 12) :
    vt21 θ (tests21 e).1 (tests21 e).2.1 (tests21 e).2.2.1 (tests21 e).2.2.2 ≠ 0 :=
  Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul h) e (mem_univ _)

theorem nfV_inj (hD : det3 E₁ E₂ E₃ ≠ 0) {a b c a' b' c' : ℝ}
    (h : nfV E₁ E₂ E₃ a b c = nfV E₁ E₂ E₃ a' b' c') : a = a' ∧ b = b' ∧ c = c' := by
  by_contra hne
  have h0 : nfV E₁ E₂ E₃ (a - a') (b - b') (c - c') = 0 := by
    rw [show nfV E₁ E₂ E₃ (a - a') (b - b') (c - c') =
      nfV E₁ E₂ E₃ a b c - nfV E₁ E₂ E₃ a' b' c' by simp only [nfV]; module, h, sub_self]
  refine nfV_ne_zero hD ?_ h0
  by_contra h'
  push Not at h'
  exact hne ⟨by linarith [h'.1], by linarith [h'.2.1], by linarith [h'.2.2]⟩

theorem exists_three_others : ∀ i j : Fin 7, i ≠ j → ∃ k l m : Fin 7, [i, j, k, l, m].Nodup := by
  decide +kernel

theorem nfShape21_inj (hD : det3 E₁ E₂ E₃ ≠ 0) (h : gen21 θ ≠ 0) :
    Function.Injective (nfShape21 o E₁ E₂ E₃ θ) := by
  intro i j e
  by_contra hij
  obtain ⟨k, l, m, hn⟩ := exists_three_others i j hij
  apply gen21_pp h hn
  have e' : nfShape21 o E₁ E₂ E₃ θ j - nfShape21 o E₁ E₂ E₃ θ i = 0 := by rw [e, sub_self]
  rw [nfShape21_sub] at e'
  obtain ⟨c0, c1, c2⟩ := nfV_inj hD (e'.trans (show (0 : ℝ³) = nfV E₁ E₂ E₃ 0 0 0 by
    simp only [nfV, zero_smul, add_zero]))
  simp only [d21, dR, Pi.sub_apply, c0, c1, c2]
  ring

theorem nfShape21_noPlaneParallel (hD : det3 E₁ E₂ E₃ ≠ 0) (h : gen21 θ ≠ 0) :
    NoPlaneParallel (univ.image (nfShape21 o E₁ E₂ E₃ θ)) := by
  intro p hp q hq r hr v hv w hw hn
  obtain ⟨i, -, rfl⟩ := mem_image.mp hp
  obtain ⟨j, -, rfl⟩ := mem_image.mp hq
  obtain ⟨k, -, rfl⟩ := mem_image.mp hr
  obtain ⟨l, -, rfl⟩ := mem_image.mp hv
  obtain ⟨m, -, rfl⟩ := mem_image.mp hw
  rw [det3_nfShape21]
  refine mul_ne_zero (gen21_pp h ?_) hD
  exact List.Nodup.of_map (nfShape21 o E₁ E₂ E₃ θ) hn

theorem nfShape21_par (hD : det3 E₁ E₂ E₃ ≠ 0) (h : gen21 θ ≠ 0) :
    ∀ a ∈ univ.image (nfShape21 o E₁ E₂ E₃ θ), ∀ b ∈ univ.image (nfShape21 o E₁ E₂ E₃ θ),
      ∀ c ∈ univ.image (nfShape21 o E₁ E₂ E₃ θ), ∀ d ∈ univ.image (nfShape21 o E₁ E₂ E₃ θ),
      a ≠ b → c ≠ d → ({a, b} : Finset ℝ³) ≠ {c, d} → ∀ t : ℝ, b - a ≠ t • (d - c) := by
  intro a ha b hb c hc d hd hab hcd hne t e
  obtain ⟨i, -, rfl⟩ := mem_image.mp ha
  obtain ⟨j, -, rfl⟩ := mem_image.mp hb
  obtain ⟨k, -, rfl⟩ := mem_image.mp hc
  obtain ⟨l, -, rfl⟩ := mem_image.mp hd
  have hij : i ≠ j := fun h' => hab (by rw [h'])
  have hkl : k ≠ l := fun h' => hcd (by rw [h'])
  have h3 : ¬ ((i = k ∧ j = l) ∨ (i = l ∧ j = k)) := by
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact hne rfl
    · exact hne (Finset.pair_comm _ _)
  apply gen21_pr h hij hkl h3
  rw [nfShape21_sub, nfShape21_sub,
    show t • nfV E₁ E₂ E₃ (co21 θ l 0 - co21 θ k 0) (co21 θ l 1 - co21 θ k 1)
        (co21 θ l 2 - co21 θ k 2) = nfV E₁ E₂ E₃ (t * (co21 θ l 0 - co21 θ k 0))
        (t * (co21 θ l 1 - co21 θ k 1)) (t * (co21 θ l 2 - co21 θ k 2)) by
      simp only [nfV, smul_add, smul_smul]] at e
  obtain ⟨c0, c1, c2⟩ := nfV_inj hD e
  simp only [par21, crSq, Pi.sub_apply, c0, c1, c2]
  ring

theorem nfShape21_eq (hD : det3 E₁ E₂ E₃ ≠ 0) (h : gen21 θ ≠ 0) (e : Fin 5) :
    det3 (nfShape21 o E₁ E₂ E₃ θ (eq21 e).2.1 - nfShape21 o E₁ E₂ E₃ θ (eq21 e).1)
      (nfShape21 o E₁ E₂ E₃ θ (eq21 e).2.2.1 - nfShape21 o E₁ E₂ E₃ θ (eq21 e).1)
      (nfShape21 o E₁ E₂ E₃ θ (eq21 e).2.2.2 - nfShape21 o E₁ E₂ E₃ θ (eq21 e).1) ≠ 0 := by
  rw [det3_nfShape21]; exact mul_ne_zero (gen21_eq h e) hD

theorem nfShape21_test (hD : det3 E₁ E₂ E₃ ≠ 0) (h : gen21 θ ≠ 0) (e : Fin 12) :
    det3 (nfShape21 o E₁ E₂ E₃ θ (tests21 e).2.1 - nfShape21 o E₁ E₂ E₃ θ (tests21 e).1)
      (nfShape21 o E₁ E₂ E₃ θ (tests21 e).2.2.1 - nfShape21 o E₁ E₂ E₃ θ (tests21 e).1)
      (vtxView21 (nfShape21 o E₁ E₂ E₃ θ) (tests21 e).2.2.2) ≠ 0 := by
  rw [det3_vtx_nfShape21]; exact mul_ne_zero hD (mul_ne_zero (gen21_vt h e) hD)

end Generic

/-! ### Certificates at named views and their limits -/

/-- `u` is a nonzero multiple of a named view. -/
def Named21 (x : Fin 7 → ℝ³) (u : ℝ³) : Prop :=
  ∃ v : (Fin 7 × Fin 7) ⊕ Fin 8, ∃ c : ℝ, c ≠ 0 ∧ u = c • view21 x v

/-- **A type-21 certificate**: a rim certificate (3, 4 or 5 corners) at a named view.  The tier
cover ends in one; with no horizontal double normal at its view it
makes the shape Rupert, and it passes to limits (`isRupert_of_tendsto_rimCert`). -/
def Cert21 (x : Fin 7 → ℝ³) : Prop := ∃ u, Named21 x u ∧ RimCert (univ.image x) u

/-- A labelled certificate at a named view, with 3, 4 or 5 corners. -/
def CertL21 (y : Fin 7 → ℝ³) (v : (Fin 7 × Fin 7) ⊕ Fin 8) (ε : Bool) :
    ((ZMod 3 → Fin 7) ⊕ (ZMod 4 → Fin 7) ⊕ (ZMod 5 → Fin 7)) → Prop :=
  Sum.elim (fun lab => RimCertAt y (sgnB ε • view21 y v) lab)
    (Sum.elim (fun lab => RimCertAt y (sgnB ε • view21 y v) lab)
      (fun lab => RimCertAt y (sgnB ε • view21 y v) lab))

/-- **Normalizing a certificate**: labels, a named view and a sign. -/
theorem Cert21.exists_certL {y : Fin 7 → ℝ³} (h : Cert21 y) :
    ∃ v ε L, CertL21 y v ε L := by
  obtain ⟨u, ⟨v, c, hc0, rfl⟩, k, hk, z, hz⟩ := h
  have hpos : 0 < |c|⁻¹ := inv_pos.mpr (abs_pos.mpr hc0)
  have hz' := hz.smul hpos
  rw [smul_smul] at hz'
  have hsg : |c|⁻¹ * c = sgnB (decide (0 < c)) := by
    rcases lt_or_gt_of_ne hc0 with h | h
    · rw [abs_of_neg h, sgnB, decide_eq_false (not_lt.mpr h.le)]
      field_simp; simp
    · rw [abs_of_pos h, sgnB, decide_eq_true h, inv_mul_cancel₀ h.ne']; simp
  rw [hsg] at hz'
  obtain ⟨lab, -, hat⟩ := hz'.toAt
  refine ⟨v, decide (0 < c), ?_⟩
  rcases hk with rfl | rfl | rfl
  · exact ⟨Sum.inl lab, hat⟩
  · exact ⟨Sum.inr (Sum.inl lab), hat⟩
  · exact ⟨Sum.inr (Sum.inr lab), hat⟩

/-- **Lemma 18.2 for one labelled certificate along a sequence of type-21 shapes.** -/
theorem isRupert_of_certL_seq21 {x : Fin 7 → ℝ³} (T : Facets21 x)
    (hnd : ∀ v, view21 x v ≠ 0 → NoHDNAt (univ.image x) (view21 x v))
    (K : ℕ → Fin 7 → ℝ³) (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m)))
    {k : ℕ} [NeZero k] (v : (Fin 7 × Fin 7) ⊕ Fin 8) (ε : Bool) (lab : ZMod k → Fin 7)
    (hc : ∃ᶠ n in atTop, RimCertAt (K n) (sgnB ε • view21 (K n) v) lab ∧
      ∀ w a b, TieInst21 x w a b → ⟪K n a - K n b, view21 (K n) w⟫ = 0) :
    IsRupert (univ.image x) := by
  obtain ⟨n₀, hn₀, -⟩ := hc.exists
  have hv : ∀ i, v ≠ .inl (i, i) := by
    rintro i rfl
    apply hn₀.ne_zero
    simp [view21]
  have hv0 := T.view21_ne_zero v hv
  have hs := sgnB_ne_zero ε
  refine isRupert_of_tendsto_rimCert x T.noSeg ⟨2, 0, 3, 6, T.det_ne⟩ lab (smul_ne_zero hs hv0)
    ((hnd v hv0).smul_view hs) K (fun n => sgnB ε • view21 (K n) v) hK
    ((tendsto_view21 hK v).const_smul _) (hc.mono fun n hn => ⟨hn.1, fun i j e => ?_⟩)
  by_cases hij : lab i = lab j
  · rw [hij]
  · rw [real_inner_smul_right, real_inner_smul_right] at e
    have e' := mul_left_cancel₀ hs e
    have h := hn.2 v (lab i) (lab j) ⟨hij, hv0, by rw [inner_sub_left, e', sub_self]⟩
    rw [inner_sub_left, sub_eq_zero] at h
    simp only [real_inner_smul_right, h]

/-- **A frequent certificate along a sequence of type-21 shapes** (Lemma 18.2 with the finitely
many labelled certificates): a subsequence carries one labelled certificate. -/
theorem isRupert_of_cert_seq21 {x : Fin 7 → ℝ³} (T : Facets21 x)
    (hnd : ∀ v, view21 x v ≠ 0 → NoHDNAt (univ.image x) (view21 x v))
    (K : ℕ → Fin 7 → ℝ³) (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m)))
    (hc : ∃ᶠ n in atTop, Cert21 (K n) ∧
      ∀ w a b, TieInst21 x w a b → ⟪K n a - K n b, view21 (K n) w⟫ = 0) :
    IsRupert (univ.image x) := by
  have h : ∃ᶠ n in atTop, ∃ q : ((Fin 7 × Fin 7) ⊕ Fin 8) × Bool ×
      ((ZMod 3 → Fin 7) ⊕ (ZMod 4 → Fin 7) ⊕ (ZMod 5 → Fin 7)),
      CertL21 (K n) q.1 q.2.1 q.2.2 ∧
        ∀ w a b, TieInst21 x w a b → ⟪K n a - K n b, view21 (K n) w⟫ = 0 :=
    hc.mono fun n hn => by
      obtain ⟨v, ε, L, hL⟩ := hn.1.exists_certL
      exact ⟨(v, ε, L), hL, hn.2⟩
  obtain ⟨⟨v, ε, L⟩, hq⟩ := frequently_exists_of_finite h
  rcases L with lab | lab | lab
  · exact isRupert_of_certL_seq21 T hnd K hK v ε lab hq
  · exact isRupert_of_certL_seq21 T hnd K hK v ε lab hq
  · exact isRupert_of_certL_seq21 T hnd K hK v ε lab hq

/-! ### The cover at a generic normal-form shape -/

/-- The named vertex crossings of `y`, as a condition on views. -/
def NamedVtx21 (y : Fin 7 → ℝ³) (u : ℝ³) : Prop :=
  ∃ t : Fin 8, ∃ c : ℝ, c ≠ 0 ∧ u = c • vtxView21 y t

theorem Cert21.of_certV {y : Fin 7 → ℝ³} (h : CertV (univ.image y) (NamedVtx21 y)) :
    Cert21 y := by
  obtain ⟨u, hu, hc⟩ := h
  refine ⟨u, ?_, hc⟩
  rcases hu with ⟨t, c, hc0, rfl⟩ | ⟨v, hv, w, hw, -, rfl⟩
  · exact ⟨.inr t, c, hc0, rfl⟩
  · obtain ⟨i, -, rfl⟩ := mem_image.mp hv
    obtain ⟨j, -, rfl⟩ := mem_image.mp hw
    exact ⟨.inl (i, j), 1, one_ne_zero, (one_smul _ _).symm⟩

/-- **One vertex test at a generic shape**: a direction of the test's line (given by the two
planes in the labels of `vtx21`) is a nonzero multiple of the named view, and the far-side test
is nonzero there. -/
theorem test21_of_perp {o E₁ E₂ E₃ : ℝ³} {θ : Fin 7 → ℝ} (hD : det3 E₁ E₂ E₃ ≠ 0)
    (hg : gen21 θ ≠ 0) (e : Fin 12) {u : ℝ³} (hu : u ≠ 0)
    (h₁ : det3 (nfShape21 o E₁ E₂ E₃ θ (vtx21 (tests21 e).2.2.2).1.2.1 -
        nfShape21 o E₁ E₂ E₃ θ (vtx21 (tests21 e).2.2.2).1.1)
      (nfShape21 o E₁ E₂ E₃ θ (vtx21 (tests21 e).2.2.2).1.2.2 -
        nfShape21 o E₁ E₂ E₃ θ (vtx21 (tests21 e).2.2.2).1.1) u = 0)
    (h₂ : det3 (nfShape21 o E₁ E₂ E₃ θ (vtx21 (tests21 e).2.2.2).2.2.1 -
        nfShape21 o E₁ E₂ E₃ θ (vtx21 (tests21 e).2.2.2).2.1)
      (nfShape21 o E₁ E₂ E₃ θ (vtx21 (tests21 e).2.2.2).2.2.2 -
        nfShape21 o E₁ E₂ E₃ θ (vtx21 (tests21 e).2.2.2).2.1) u = 0) :
    det3 (nfShape21 o E₁ E₂ E₃ θ (tests21 e).2.1 - nfShape21 o E₁ E₂ E₃ θ (tests21 e).1)
      (nfShape21 o E₁ E₂ E₃ θ (tests21 e).2.2.1 - nfShape21 o E₁ E₂ E₃ θ (tests21 e).1) u ≠ 0 ∧
    ∃ c : ℝ, c ≠ 0 ∧ u = c • vtxView21 (nfShape21 o E₁ E₂ E₃ θ) (tests21 e).2.2.2 := by
  obtain ⟨⟨c, hc, rfl⟩, hdet⟩ := vtxView21_of_perp _ _ hu h₁ h₂ (nfShape21_test hD hg e)
  exact ⟨hdet, c, hc, rfl⟩

theorem NoTieAt.smul {V : Finset ℝ³} {u : ℝ³} (h : NoTieAt V u) {c : ℝ} (hc : c ≠ 0) :
    NoTieAt V (c • u) := by
  intro s hs t ht hst e
  simp only [real_inner_smul_right] at e
  exact h s hs t ht hst (mul_left_cancel₀ hc e)

/-- The facet functions of a normal-form shape vanish on their facets. -/
theorem detAff_nfShape21 (κ : ℝ) (o E₁ E₂ E₃ : ℝ³) (θ : Fin 7 → ℝ) (P Q R i : Fin 7) :
    detAff κ (nfShape21 o E₁ E₂ E₃ θ P) (nfShape21 o E₁ E₂ E₃ θ Q) (nfShape21 o E₁ E₂ E₃ θ R)
      (nfShape21 o E₁ E₂ E₃ θ i) = κ * (d21 θ P Q R P i * det3 E₁ E₂ E₃) := by
  rw [detAff_apply, det3_nfShape21]

theorem d21_facets (θ : Fin 7 → ℝ) :
    (∀ i ∈ ({0, 1, 4} : Finset (Fin 7)), d21 θ 0 1 4 0 i = 0) ∧
    (∀ i ∈ ({0, 1, 5} : Finset (Fin 7)), d21 θ 0 1 5 0 i = 0) ∧
    (∀ i ∈ ({0, 2, 5, 6} : Finset (Fin 7)), d21 θ 2 0 6 2 i = 0) ∧
    (∀ i ∈ ({0, 4, 6} : Finset (Fin 7)), d21 θ 0 4 6 0 i = 0) ∧
    (∀ i ∈ ({1, 3, 4} : Finset (Fin 7)), d21 θ 1 3 4 1 i = 0) ∧
    (∀ i ∈ ({1, 3, 5} : Finset (Fin 7)), d21 θ 1 3 5 1 i = 0) ∧
    (∀ i ∈ ({2, 3, 4, 6} : Finset (Fin 7)), d21 θ 2 3 6 2 i = 0) ∧
    (∀ i ∈ ({2, 3, 5} : Finset (Fin 7)), d21 θ 2 3 5 2 i = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro i hi <;> fin_cases i <;>
    first
    | (exfalso; revert hi; decide)
    | (simp [d21, dR, co21, -mul_eq_zero]; done)
    | (simp [d21, dR, co21, -mul_eq_zero]; ring)

/-- The three labels of each facet used for its function: `014`, `015`, `0256` (by `2, 0, 6`),
`046`, `134`, `135`, `2346` (by `2, 3, 6`), `235`. -/
def facT : Fin 8 → Fin 7 × Fin 7 × Fin 7 :=
  ![(0, 1, 4), (0, 1, 5), (2, 0, 6), (0, 4, 6), (1, 3, 4), (1, 3, 5), (2, 3, 6), (2, 3, 5)]

/-- The facets of type 21. -/
def facS : Fin 8 → Finset (Fin 7) :=
  ![{0, 1, 4}, {0, 1, 5}, {0, 2, 5, 6}, {0, 4, 6}, {1, 3, 4}, {1, 3, 5}, {2, 3, 4, 6}, {2, 3, 5}]

/-- The facet functions `κ_f [Q − P, R − P, y − P]` of a labelled point set. -/
noncomputable def fac21 (κ : Fin 8 → ℝ) (y : Fin 7 → ℝ³) (f : Fin 8) : ℝ³ →ᵃ[ℝ] ℝ :=
  detAff (κ f) (y (facT f).1) (y (facT f).2.1) (y (facT f).2.2)

theorem fac21_zero (κ : Fin 8 → ℝ) (o E₁ E₂ E₃ : ℝ³) (θ : Fin 7 → ℝ) (f : Fin 8) (i : Fin 7)
    (hi : i ∈ facS f) : fac21 κ (nfShape21 o E₁ E₂ E₃ θ) f (nfShape21 o E₁ E₂ E₃ θ i) = 0 := by
  rw [fac21, detAff_nfShape21]
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7⟩ := d21_facets θ
  have : d21 θ (facT f).1 (facT f).2.1 (facT f).2.2 (facT f).1 i = 0 := by
    fin_cases f
    exacts [d0 i hi, d1 i hi, d2 i hi, d3 i hi, d4 i hi, d5 i hi, d6 i hi, d7 i hi]
  rw [this, zero_mul, mul_zero]

/-- Directions along the plane of `0256` (middle coordinate zero). -/
theorem det3_plane0256 (o E₁ E₂ E₃ u : ℝ³) (θ : Fin 7 → ℝ) {i j k l : Fin 7}
    (hi : co21 θ i 1 = 0) (hj : co21 θ j 1 = 0) (hk : co21 θ k 1 = 0) (hl : co21 θ l 1 = 0) :
    det3 (nfShape21 o E₁ E₂ E₃ θ j - nfShape21 o E₁ E₂ E₃ θ i)
      (nfShape21 o E₁ E₂ E₃ θ l - nfShape21 o E₁ E₂ E₃ θ k) u =
      ((co21 θ j 0 - co21 θ i 0) * (co21 θ l 2 - co21 θ k 2) -
        (co21 θ j 2 - co21 θ i 2) * (co21 θ l 0 - co21 θ k 0)) *
      det3 (nfShape21 o E₁ E₂ E₃ θ 0 - nfShape21 o E₁ E₂ E₃ θ 2)
        (nfShape21 o E₁ E₂ E₃ θ 6 - nfShape21 o E₁ E₂ E₃ θ 2) u := by
  rw [nfShape21_sub, nfShape21_sub, nfShape21_sub, nfShape21_sub, hi, hj, hk, hl]
  have e0 : co21 θ 0 = ![1, 0, 0] := rfl
  have e2 : co21 θ 2 = ![0, 0, 0] := rfl
  have e6 : co21 θ 6 = ![0, 0, 1] := rfl
  simp only [e0, e2, e6, nfV, det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  ring

/-- Directions along the plane of `2346` (first coordinate zero). -/
theorem det3_plane2346 (o E₁ E₂ E₃ u : ℝ³) (θ : Fin 7 → ℝ) {i j k l : Fin 7}
    (hi : co21 θ i 0 = 0) (hj : co21 θ j 0 = 0) (hk : co21 θ k 0 = 0) (hl : co21 θ l 0 = 0) :
    det3 (nfShape21 o E₁ E₂ E₃ θ j - nfShape21 o E₁ E₂ E₃ θ i)
      (nfShape21 o E₁ E₂ E₃ θ l - nfShape21 o E₁ E₂ E₃ θ k) u =
      ((co21 θ j 1 - co21 θ i 1) * (co21 θ l 2 - co21 θ k 2) -
        (co21 θ j 2 - co21 θ i 2) * (co21 θ l 1 - co21 θ k 1)) *
      det3 (nfShape21 o E₁ E₂ E₃ θ 3 - nfShape21 o E₁ E₂ E₃ θ 2)
        (nfShape21 o E₁ E₂ E₃ θ 6 - nfShape21 o E₁ E₂ E₃ θ 2) u := by
  rw [nfShape21_sub, nfShape21_sub, nfShape21_sub, nfShape21_sub, hi, hj, hk, hl]
  have e3 : co21 θ 3 = ![0, 1, 0] := rfl
  have e2 : co21 θ 2 = ![0, 0, 0] := rfl
  have e6 : co21 θ 6 = ![0, 0, 1] := rfl
  simp only [e3, e2, e6, nfV, det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  ring

/-- **The tier cover at a generic normal-form shape** (Theorem 16.26 in certificate form): off
the special positions of `gen21`, with determinant facet functions, at most one tie at each
segment view and at each vertex crossing, no tie along `a − b` if `a, b` tie at the view of `T1`
(the view of `Y`), and a tie at no more than one of the two views of F2, a rim certificate at a
named view. -/
theorem cert21_of_generic {o E₁ E₂ E₃ : ℝ³} {θ : Fin 7 → ℝ} {y : Fin 7 → ℝ³}
    (hy : y = nfShape21 o E₁ E₂ E₃ θ) (hD : det3 E₁ E₂ E₃ ≠ 0)
    (hg : gen21 θ ≠ 0) {κ : Fin 8 → ℝ} (hκ : ∀ f, κ f ≠ 0)
    (hneg : ∀ f i, i ∉ facS f → fac21 κ y f (y i) < 0)
    (htie : TieSeg (univ.image y))
    (hvt : ∀ t, OneTieAt (univ.image y) (vtxView21 y t))
    (hY : (⟪y 0, vtxView21 y 0⟫ = ⟪y 4, vtxView21 y 0⟫ → NoTieAt (univ.image y) (y 0 - y 4)) ∧
      (⟪y 4, vtxView21 y 1⟫ = ⟪y 0, vtxView21 y 1⟫ → NoTieAt (univ.image y) (y 4 - y 0)) ∧
      (⟪y 5, vtxView21 y 2⟫ = ⟪y 3, vtxView21 y 2⟫ → NoTieAt (univ.image y) (y 5 - y 3)) ∧
      (⟪y 3, vtxView21 y 3⟫ = ⟪y 5, vtxView21 y 3⟫ → NoTieAt (univ.image y) (y 3 - y 5)))
    (hF : (NoTieAt (univ.image y) (vtxView21 y 1) ∨ NoTieAt (univ.image y) (vtxView21 y 4)) ∧
      (NoTieAt (univ.image y) (vtxView21 y 0) ∨ NoTieAt (univ.image y) (vtxView21 y 5)) ∧
      (NoTieAt (univ.image y) (vtxView21 y 3) ∨ NoTieAt (univ.image y) (vtxView21 y 6)) ∧
      (NoTieAt (univ.image y) (vtxView21 y 2) ∨ NoTieAt (univ.image y) (vtxView21 y 7))) :
    Cert21 y := by
  subst hy
  have hfac : ∀ f i, (i ∈ facS f → fac21 κ (nfShape21 o E₁ E₂ E₃ θ) f (nfShape21 o E₁ E₂ E₃ θ i) =
      0) ∧
      (i ∉ facS f → fac21 κ (nfShape21 o E₁ E₂ E₃ θ) f (nfShape21 o E₁ E₂ E₃ θ i) < 0) :=
    fun f i => ⟨fac21_zero κ o E₁ E₂ E₃ θ f i, hneg f i⟩
  have hlin : ∀ f u, (fac21 κ (nfShape21 o E₁ E₂ E₃ θ) f).linear u = 0 →
      det3 (nfShape21 o E₁ E₂ E₃ θ (facT f).2.1 - nfShape21 o E₁ E₂ E₃ θ (facT f).1) (nfShape21 o
          E₁ E₂ E₃ θ (facT f).2.2 - nfShape21 o E₁ E₂ E₃ θ (facT f).1) u = 0 :=
    fun f u h => (mul_eq_zero.mp h).resolve_left (hκ f)
  obtain ⟨hY0, hY1, hY2, hY3⟩ := hY
  obtain ⟨hF1, hF2, hF3, hF4⟩ := hF
  have cancel : ∀ {p q w : ℝ³} {c : ℝ}, c ≠ 0 → ⟪p, c • w⟫ = ⟪q, c • w⟫ → ⟪p, w⟫ = ⟪q, w⟫ :=
    fun hc h => by simp only [real_inner_smul_right] at h; exact mul_left_cancel₀ hc h
  -- the planar equators in the labels of the vertex tests of F2
  have E0 : det3 (nfShape21 o E₁ E₂ E₃ θ 5 - nfShape21 o E₁ E₂ E₃ θ 4) (nfShape21 o E₁ E₂ E₃ θ 1 -
      nfShape21 o E₁ E₂ E₃ θ 4) (nfShape21 o E₁ E₂ E₃ θ 6 - nfShape21 o E₁ E₂ E₃ θ 4) ≠ 0 :=
      nfShape21_eq hD hg 0
  have E1 : det3 (nfShape21 o E₁ E₂ E₃ θ 3 - nfShape21 o E₁ E₂ E₃ θ 0) (nfShape21 o E₁ E₂ E₃ θ 1 -
      nfShape21 o E₁ E₂ E₃ θ 0) (nfShape21 o E₁ E₂ E₃ θ 6 - nfShape21 o E₁ E₂ E₃ θ 0) ≠ 0 :=
      nfShape21_eq hD hg 1
  have E2 : det3 (nfShape21 o E₁ E₂ E₃ θ 3 - nfShape21 o E₁ E₂ E₃ θ 0) (nfShape21 o E₁ E₂ E₃ θ 4 -
      nfShape21 o E₁ E₂ E₃ θ 0) (nfShape21 o E₁ E₂ E₃ θ 5 - nfShape21 o E₁ E₂ E₃ θ 0) ≠ 0 :=
      nfShape21_eq hD hg 2
  have E3 : det3 (nfShape21 o E₁ E₂ E₃ θ 0 - nfShape21 o E₁ E₂ E₃ θ 3) (nfShape21 o E₁ E₂ E₃ θ 1 -
      nfShape21 o E₁ E₂ E₃ θ 3) (nfShape21 o E₁ E₂ E₃ θ 2 - nfShape21 o E₁ E₂ E₃ θ 3) ≠ 0 :=
      nfShape21_eq hD hg 3
  have E4 : det3 (nfShape21 o E₁ E₂ E₃ θ 4 - nfShape21 o E₁ E₂ E₃ θ 5) (nfShape21 o E₁ E₂ E₃ θ 1 -
      nfShape21 o E₁ E₂ E₃ θ 5) (nfShape21 o E₁ E₂ E₃ θ 2 - nfShape21 o E₁ E₂ E₃ θ 5) ≠ 0 :=
      nfShape21_eq hD hg 4
  have sgn : ∀ {A B : ℝ}, A = -B → B ≠ 0 → A ≠ 0 := fun h hB => by rw [h]; exact neg_ne_zero.mpr hB
  have sgn' : ∀ {A B : ℝ}, A = B → B ≠ 0 → A ≠ 0 := fun h hB => by rw [h]; exact hB
  refine Cert21.of_certV (cert_type21_facets (L := NamedVtx21 (nfShape21 o E₁ E₂ E₃ θ)) (nfShape21
      o E₁ E₂ E₃ θ) (nfShape21_inj hD hg)
    (fac21 κ _ 0) (fac21 κ _ 1) (fac21 κ _ 2) (fac21 κ _ 3) (fac21 κ _ 4) (fac21 κ _ 5)
    (fac21 κ _ 6) (fac21 κ _ 7) (hfac 0) (hfac 1) (hfac 2) (hfac 3) (hfac 4) (hfac 5) (hfac 6)
    (hfac 7) (nfShape21_noPlaneParallel hD hg) ⟨nfShape21_par hD hg, htie.tie⟩
    ⟨nfShape21_eq hD hg 0, nfShape21_eq hD hg 1, nfShape21_eq hD hg 2, nfShape21_eq hD hg 3,
      nfShape21_eq hD hg 4⟩ ⟨?_, ?_, ?_, ?_⟩ ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_,
          ?_⟩⟩)
  · -- `T1` at `0`: `014/0256`
    intro u hu h1 h2
    have a : det3 (nfShape21 o E₁ E₂ E₃ θ 1 - nfShape21 o E₁ E₂ E₃ θ 0) (nfShape21 o E₁ E₂ E₃ θ 4 -
        nfShape21 o E₁ E₂ E₃ θ 0) u = 0 := hlin 0 u h1
    have b : det3 (nfShape21 o E₁ E₂ E₃ θ 0 - nfShape21 o E₁ E₂ E₃ θ 2) (nfShape21 o E₁ E₂ E₃ θ 6 -
        nfShape21 o E₁ E₂ E₃ θ 2) u = 0 := hlin 2 u h2
    obtain ⟨hdet, c, hc, rfl⟩ := test21_of_perp hD hg 0 hu
      (show det3 (nfShape21 o E₁ E₂ E₃ θ 4 - nfShape21 o E₁ E₂ E₃ θ 0) (nfShape21 o E₁ E₂ E₃ θ 1 -
          nfShape21 o E₁ E₂ E₃ θ 0) u = 0 by rw [det3_swap12, a, neg_zero])
      (show det3 (nfShape21 o E₁ E₂ E₃ θ 5 - nfShape21 o E₁ E₂ E₃ θ 0) (nfShape21 o E₁ E₂ E₃ θ 6 -
          nfShape21 o E₁ E₂ E₃ θ 0) u = 0 by
        rw [det3_plane0256 o E₁ E₂ E₃ u θ (i := 0) (j := 5) (k := 0) (l := 6) rfl rfl rfl rfl, b,
          mul_zero])
    exact ⟨hdet, Or.inr ⟨(hvt 0).smul hc, fun h => hY0 (cancel hc h)⟩, ⟨0, c, hc, rfl⟩⟩
  · -- `T1` at `4`: `014/2346`
    intro u hu h1 h2
    have a : det3 (nfShape21 o E₁ E₂ E₃ θ 1 - nfShape21 o E₁ E₂ E₃ θ 0) (nfShape21 o E₁ E₂ E₃ θ 4 -
        nfShape21 o E₁ E₂ E₃ θ 0) u = 0 := hlin 0 u h1
    have b : det3 (nfShape21 o E₁ E₂ E₃ θ 3 - nfShape21 o E₁ E₂ E₃ θ 2) (nfShape21 o E₁ E₂ E₃ θ 6 -
        nfShape21 o E₁ E₂ E₃ θ 2) u = 0 := hlin 6 u h2
    have e : ∀ p q r : ℝ³, det3 (p - r) (q - r) u = det3 (q - p) (r - p) u := by
      intro p q r; simp only [det3_expand, PiLp.sub_apply]; ring
    obtain ⟨hdet, c, hc, rfl⟩ := test21_of_perp hD hg 1 hu
      (show det3 (nfShape21 o E₁ E₂ E₃ θ 0 - nfShape21 o E₁ E₂ E₃ θ 4) (nfShape21 o E₁ E₂ E₃ θ 1 -
          nfShape21 o E₁ E₂ E₃ θ 4) u = 0 by rw [e, a])
      (show det3 (nfShape21 o E₁ E₂ E₃ θ 3 - nfShape21 o E₁ E₂ E₃ θ 4) (nfShape21 o E₁ E₂ E₃ θ 6 -
          nfShape21 o E₁ E₂ E₃ θ 4) u = 0 by
        rw [det3_plane2346 o E₁ E₂ E₃ u θ (i := 4) (j := 3) (k := 4) (l := 6) rfl rfl rfl rfl, b,
          mul_zero])
    exact ⟨hdet, Or.inr ⟨(hvt 1).smul hc, fun h => hY1 (cancel hc h)⟩, ⟨1, c, hc, rfl⟩⟩
  · -- `T1` at `5`: `135/0256`
    intro u hu h1 h2
    have a : det3 (nfShape21 o E₁ E₂ E₃ θ 3 - nfShape21 o E₁ E₂ E₃ θ 1) (nfShape21 o E₁ E₂ E₃ θ 5 -
        nfShape21 o E₁ E₂ E₃ θ 1) u = 0 := hlin 5 u h1
    have b : det3 (nfShape21 o E₁ E₂ E₃ θ 0 - nfShape21 o E₁ E₂ E₃ θ 2) (nfShape21 o E₁ E₂ E₃ θ 6 -
        nfShape21 o E₁ E₂ E₃ θ 2) u = 0 := hlin 2 u h2
    have e : ∀ p q r : ℝ³, det3 (q - r) (p - r) u = -det3 (q - p) (r - p) u := by
      intro p q r; simp only [det3_expand, PiLp.sub_apply]; ring
    obtain ⟨hdet, c, hc, rfl⟩ := test21_of_perp hD hg 2 hu
      (show det3 (nfShape21 o E₁ E₂ E₃ θ 3 - nfShape21 o E₁ E₂ E₃ θ 5) (nfShape21 o E₁ E₂ E₃ θ 1 -
          nfShape21 o E₁ E₂ E₃ θ 5) u = 0 by rw [e, a, neg_zero])
      (show det3 (nfShape21 o E₁ E₂ E₃ θ 0 - nfShape21 o E₁ E₂ E₃ θ 5) (nfShape21 o E₁ E₂ E₃ θ 2 -
          nfShape21 o E₁ E₂ E₃ θ 5) u = 0 by
        rw [det3_plane0256 o E₁ E₂ E₃ u θ (i := 5) (j := 0) (k := 5) (l := 2) rfl rfl rfl rfl, b,
          mul_zero])
    exact ⟨hdet, Or.inr ⟨(hvt 2).smul hc, fun h => hY2 (cancel hc h)⟩, ⟨2, c, hc, rfl⟩⟩
  · -- `T1` at `3`: `135/2346`
    intro u hu h1 h2
    have a : det3 (nfShape21 o E₁ E₂ E₃ θ 3 - nfShape21 o E₁ E₂ E₃ θ 1) (nfShape21 o E₁ E₂ E₃ θ 5 -
        nfShape21 o E₁ E₂ E₃ θ 1) u = 0 := hlin 5 u h1
    have b : det3 (nfShape21 o E₁ E₂ E₃ θ 3 - nfShape21 o E₁ E₂ E₃ θ 2) (nfShape21 o E₁ E₂ E₃ θ 6 -
        nfShape21 o E₁ E₂ E₃ θ 2) u = 0 := hlin 6 u h2
    have e : ∀ p q r : ℝ³, det3 (r - q) (p - q) u = det3 (q - p) (r - p) u := by
      intro p q r; simp only [det3_expand, PiLp.sub_apply]; ring
    obtain ⟨hdet, c, hc, rfl⟩ := test21_of_perp hD hg 3 hu
      (show det3 (nfShape21 o E₁ E₂ E₃ θ 5 - nfShape21 o E₁ E₂ E₃ θ 3) (nfShape21 o E₁ E₂ E₃ θ 1 -
          nfShape21 o E₁ E₂ E₃ θ 3) u = 0 by rw [e, a])
      (show det3 (nfShape21 o E₁ E₂ E₃ θ 4 - nfShape21 o E₁ E₂ E₃ θ 3) (nfShape21 o E₁ E₂ E₃ θ 2 -
          nfShape21 o E₁ E₂ E₃ θ 3) u = 0 by
        rw [det3_plane2346 o E₁ E₂ E₃ u θ (i := 3) (j := 4) (k := 3) (l := 2) rfl rfl rfl rfl, b,
          mul_zero])
    exact ⟨hdet, Or.inr ⟨(hvt 3).smul hc, fun h => hY3 (cancel hc h)⟩, ⟨3, c, hc, rfl⟩⟩
  -- F2 in the labelling `id` (vertex `4`): `V = 014/2346` (`t = 1`), `V′ = 046/134` (`t = 4`)
  · intro u hu h1 h2
    obtain ⟨hdet, c, hc, e⟩ := test21_of_perp hD hg 4 hu h1 h2
    exact ⟨hdet, ⟨1, c, hc, e⟩⟩
  · intro u hu h1 h2
    obtain ⟨hdet, c, hc, e⟩ := test21_of_perp hD hg 5 hu h1 h2
    exact ⟨hdet, ⟨4, c, hc, e⟩⟩
  · intro u v hu h1 h2 hv h3 h4
    obtain ⟨-, c, hc, rfl⟩ := test21_of_perp hD hg 4 hu h1 h2
    obtain ⟨-, c', hc', rfl⟩ := test21_of_perp hD hg 5 hv h3 h4
    refine Or.inr ⟨(hvt 1).smul hc, (hvt 4).smul hc', hF1.imp (·.smul hc) (·.smul hc'),
      sgn (by simp only [det3_expand, PiLp.sub_apply]; ring) E4,
      sgn' (by simp only [det3_expand, PiLp.sub_apply]; ring) E2⟩
  -- F2 in the labelling `σ1` (vertex `0`): `V = 014/0256` (`t = 0`), `V′ = 046/015` (`t = 5`)
  · intro u hu h1 h2
    obtain ⟨hdet, c, hc, e⟩ := test21_of_perp hD hg 6 hu h1 h2
    exact ⟨hdet, ⟨0, c, hc, e⟩⟩
  · intro u hu h1 h2
    obtain ⟨hdet, c, hc, e⟩ := test21_of_perp hD hg 7 hu h1 h2
    exact ⟨hdet, ⟨5, c, hc, e⟩⟩
  · intro u v hu h1 h2 hv h3 h4
    obtain ⟨-, c, hc, rfl⟩ := test21_of_perp hD hg 6 hu h1 h2
    obtain ⟨-, c', hc', rfl⟩ := test21_of_perp hD hg 7 hv h3 h4
    refine Or.inr ⟨(hvt 0).smul hc, (hvt 5).smul hc', hF2.imp (·.smul hc) (·.smul hc'),
      sgn (by simp only [det3_expand, PiLp.sub_apply]; ring) E3,
      sgn' (by simp only [det3_expand, PiLp.sub_apply]; ring) E2⟩
  -- F2 in the labelling `σ2` (vertex `3`): `V = 135/2346` (`t = 3`), `V′ = 235/134` (`t = 6`)
  · intro u hu h1 h2
    obtain ⟨hdet, c, hc, e⟩ := test21_of_perp hD hg 8 hu h1 h2
    exact ⟨hdet, ⟨3, c, hc, e⟩⟩
  · intro u hu h1 h2
    obtain ⟨hdet, c, hc, e⟩ := test21_of_perp hD hg 9 hu h1 h2
    exact ⟨hdet, ⟨6, c, hc, e⟩⟩
  · intro u v hu h1 h2 hv h3 h4
    obtain ⟨-, c, hc, rfl⟩ := test21_of_perp hD hg 8 hu h1 h2
    obtain ⟨-, c', hc', rfl⟩ := test21_of_perp hD hg 9 hv h3 h4
    refine Or.inr ⟨(hvt 3).smul hc, (hvt 6).smul hc', hF3.imp (·.smul hc) (·.smul hc'),
      sgn (by simp only [det3_expand, PiLp.sub_apply]; ring) E1,
      sgn' (by simp only [det3_expand, PiLp.sub_apply]; ring) E2⟩
  -- F2 in the labelling `σ2σ1` (vertex `5`): `V = 135/0256` (`t = 2`), `V′ = 235/015` (`t = 7`)
  · intro u hu h1 h2
    obtain ⟨hdet, c, hc, e⟩ := test21_of_perp hD hg 10 hu h1 h2
    exact ⟨hdet, ⟨2, c, hc, e⟩⟩
  · intro u hu h1 h2
    obtain ⟨hdet, c, hc, e⟩ := test21_of_perp hD hg 11 hu h1 h2
    exact ⟨hdet, ⟨7, c, hc, e⟩⟩
  · intro u v hu h1 h2 hv h3 h4
    obtain ⟨-, c, hc, rfl⟩ := test21_of_perp hD hg 10 hu h1 h2
    obtain ⟨-, c', hc', rfl⟩ := test21_of_perp hD hg 11 hv h3 h4
    refine Or.inr ⟨(hvt 2).smul hc, (hvt 7).smul hc', hF4.imp (·.smul hc) (·.smul hc'),
      sgn (by simp only [det3_expand, PiLp.sub_apply]; ring) E0,
      sgn' (by simp only [det3_expand, PiLp.sub_apply]; ring) E2⟩

/-! ### Ties across named views -/

/-- **A tie at a vertex crossing excludes ties along the segment of the tied pair**: the two ties
would be two equations (`OneTie21`). -/
theorem noTieAt_seg_of_tie {x y : Fin 7 → ℝ³} (htie : OneTie21 x)
    (hsub : ∀ v a b, a ≠ b → view21 y v ≠ 0 → ⟪y a - y b, view21 y v⟫ = 0 → TieInst21 x v a b)
    {t : Fin 8} {a b : Fin 7} (hab : a ≠ b) (hv : vtxView21 y t ≠ 0) (hw : y a - y b ≠ 0)
    (h : ⟪y a, vtxView21 y t⟫ = ⟪y b, vtxView21 y t⟫) : NoTieAt (univ.image y) (y a - y b) := by
  intro s hs s' hs' hss e
  obtain ⟨i, -, rfl⟩ := mem_image.mp hs
  obtain ⟨j, -, rfl⟩ := mem_image.mp hs'
  have hij : i ≠ j := fun h' => hss (by rw [h'])
  have t1 := hsub (.inr t) a b hab hv (by
    show ⟪y a - y b, vtxView21 y t⟫ = 0
    rw [inner_sub_left, h, sub_self])
  have t2 := hsub (.inl (b, a)) i j hij hw (by
    show ⟪y i - y j, y a - y b⟫ = 0
    rw [inner_sub_left, e, sub_self])
  rcases htie _ _ _ _ _ _ t1 t2 with ⟨⟨h1 | ⟨k, l, h1, -⟩, -⟩⟩ | ⟨k, l, h1, -⟩ <;>
    simp at h1

/-- **Ties at no more than one of two vertex crossings** (`OneTie21`). -/
theorem noTieAt_or {x y : Fin 7 → ℝ³} (htie : OneTie21 x)
    (hsub : ∀ v a b, a ≠ b → view21 y v ≠ 0 → ⟪y a - y b, view21 y v⟫ = 0 → TieInst21 x v a b)
    {t t' : Fin 8} (htt : t ≠ t') (hv : vtxView21 y t ≠ 0) (hv' : vtxView21 y t' ≠ 0) :
    NoTieAt (univ.image y) (vtxView21 y t) ∨ NoTieAt (univ.image y) (vtxView21 y t') := by
  by_contra hc
  simp only [not_or, NoTieAt, not_forall, not_not, exists_prop] at hc
  obtain ⟨⟨s, hs, s', hs', hss, e⟩, ⟨r, hr, r', hr', hrr, e'⟩⟩ := hc
  obtain ⟨i, -, rfl⟩ := mem_image.mp hs
  obtain ⟨j, -, rfl⟩ := mem_image.mp hs'
  obtain ⟨k, -, rfl⟩ := mem_image.mp hr
  obtain ⟨l, -, rfl⟩ := mem_image.mp hr'
  have t1 := hsub (.inr t) i j (fun h' => hss (by rw [h'])) hv (by
    show ⟪y i - y j, vtxView21 y t⟫ = 0
    rw [inner_sub_left, e, sub_self])
  have t2 := hsub (.inr t') k l (fun h' => hrr (by rw [h'])) hv' (by
    show ⟪y k - y l, vtxView21 y t'⟫ = 0
    rw [inner_sub_left, e', sub_self])
  rcases htie _ _ _ _ _ _ t1 t2 with ⟨⟨h1 | ⟨k, l, h1, -⟩, -⟩⟩ | ⟨k, l, h1, -⟩
  · exact htt (Sum.inr.inj h1).symm
  · simp at h1
  · simp at h1

/-- **The facet functions of a type-21 shape as determinants** (`fac21`): nonzero constants, and
the facet inequalities. -/
theorem Facets21.exists_kappa {x : Fin 7 → ℝ³} (T : Facets21 x) :
    ∃ κ : Fin 8 → ℝ, (∀ f, κ f ≠ 0) ∧ ∀ f i, i ∉ facS f → fac21 κ x f (x i) < 0 := by
  have ne : ∀ {i j : Fin 7}, i ≠ j → x i ≠ x j := fun h => T.inj.ne h
  have hD := T.det_ne
  have c26 : cross (x 0 - x 2) (x 6 - x 2) ≠ 0 := by
    intro h; apply hD
    rw [det3_swap23, show det3 (x 0 - x 2) (x 6 - x 2) (x 3 - x 2) =
      ⟪cross (x 0 - x 2) (x 6 - x 2), x 3 - x 2⟫ from rfl, h, inner_zero_left, neg_zero]
  have c36 : cross (x 3 - x 2) (x 6 - x 2) ≠ 0 := by
    intro h; apply hD
    have e : det3 (x 0 - x 2) (x 3 - x 2) (x 6 - x 2) =
        det3 (x 3 - x 2) (x 6 - x 2) (x 0 - x 2) := by
      simp only [det3_expand, PiLp.sub_apply]; ring
    rw [e, show det3 (x 3 - x 2) (x 6 - x 2) (x 0 - x 2) =
      ⟪cross (x 3 - x 2) (x 6 - x 2), x 0 - x 2⟫ from rfl, h, inner_zero_left]
  obtain ⟨k0, h0⟩ := T.f014.eq_det (P := 0) (Q := 1) (R := 4) (by decide) (by decide) (by decide)
    (cross_ne_zero_of_affine T.f015.hN (ne (by decide)) (T.f015.zero 0 (by decide))
      (T.f015.zero 1 (by decide)) (T.f015.neg 4 (by decide)))
  obtain ⟨k1, h1⟩ := T.f015.eq_det (P := 0) (Q := 1) (R := 5) (by decide) (by decide) (by decide)
    (cross_ne_zero_of_affine T.f014.hN (ne (by decide)) (T.f014.zero 0 (by decide))
      (T.f014.zero 1 (by decide)) (T.f014.neg 5 (by decide)))
  obtain ⟨k2, h2⟩ := T.f0256.eq_det (P := 2) (Q := 0) (R := 6) (by decide) (by decide)
    (by decide) c26
  obtain ⟨k3, h3⟩ := T.f046.eq_det (P := 0) (Q := 4) (R := 6) (by decide) (by decide) (by decide)
    (cross_ne_zero_of_affine T.f014.hN (ne (by decide)) (T.f014.zero 0 (by decide))
      (T.f014.zero 4 (by decide)) (T.f014.neg 6 (by decide)))
  obtain ⟨k4, h4⟩ := T.f134.eq_det (P := 1) (Q := 3) (R := 4) (by decide) (by decide) (by decide)
    (cross_ne_zero_of_affine T.f135.hN (ne (by decide)) (T.f135.zero 1 (by decide))
      (T.f135.zero 3 (by decide)) (T.f135.neg 4 (by decide)))
  obtain ⟨k5, h5⟩ := T.f135.eq_det (P := 1) (Q := 3) (R := 5) (by decide) (by decide) (by decide)
    (cross_ne_zero_of_affine T.f134.hN (ne (by decide)) (T.f134.zero 1 (by decide))
      (T.f134.zero 3 (by decide)) (T.f134.neg 5 (by decide)))
  obtain ⟨k6, h6⟩ := T.f2346.eq_det (P := 2) (Q := 3) (R := 6) (by decide) (by decide)
    (by decide) c36
  obtain ⟨k7, h7⟩ := T.f235.eq_det (P := 2) (Q := 3) (R := 5) (by decide) (by decide) (by decide)
    (cross_ne_zero_of_affine T.f2346.hN (ne (by decide)) (T.f2346.zero 2 (by decide))
      (T.f2346.zero 3 (by decide)) (T.f2346.neg 5 (by decide)))
  refine ⟨![k0, k1, k2, k3, k4, k5, k6, k7], fun f => ?_, fun f i hi => ?_⟩
  · fin_cases f
    · intro hk; have := T.f014.neg 2 (by decide); rw [h0, show k0 = 0 from hk, zero_mul] at this
      exact lt_irrefl _ this
    · intro hk; have := T.f015.neg 2 (by decide); rw [h1, show k1 = 0 from hk, zero_mul] at this
      exact lt_irrefl _ this
    · intro hk; have := T.f0256.neg 1 (by decide); rw [h2, show k2 = 0 from hk, zero_mul] at this
      exact lt_irrefl _ this
    · intro hk; have := T.f046.neg 1 (by decide); rw [h3, show k3 = 0 from hk, zero_mul] at this
      exact lt_irrefl _ this
    · intro hk; have := T.f134.neg 0 (by decide); rw [h4, show k4 = 0 from hk, zero_mul] at this
      exact lt_irrefl _ this
    · intro hk; have := T.f135.neg 0 (by decide); rw [h5, show k5 = 0 from hk, zero_mul] at this
      exact lt_irrefl _ this
    · intro hk; have := T.f2346.neg 0 (by decide); rw [h6, show k6 = 0 from hk, zero_mul] at this
      exact lt_irrefl _ this
    · intro hk; have := T.f235.neg 0 (by decide); rw [h7, show k7 = 0 from hk, zero_mul] at this
      exact lt_irrefl _ this
  · fin_cases f
    · show k0 * det3 (x 1 - x 0) (x 4 - x 0) (x i - x 0) < 0
      rw [← h0]; exact T.f014.neg i hi
    · show k1 * det3 (x 1 - x 0) (x 5 - x 0) (x i - x 0) < 0
      rw [← h1]; exact T.f015.neg i hi
    · show k2 * det3 (x 0 - x 2) (x 6 - x 2) (x i - x 2) < 0
      rw [← h2]; exact T.f0256.neg i hi
    · show k3 * det3 (x 4 - x 0) (x 6 - x 0) (x i - x 0) < 0
      rw [← h3]; exact T.f046.neg i hi
    · show k4 * det3 (x 3 - x 1) (x 4 - x 1) (x i - x 1) < 0
      rw [← h4]; exact T.f134.neg i hi
    · show k5 * det3 (x 3 - x 1) (x 5 - x 1) (x i - x 1) < 0
      rw [← h5]; exact T.f135.neg i hi
    · show k6 * det3 (x 3 - x 2) (x 6 - x 2) (x i - x 2) < 0
      rw [← h6]; exact T.f2346.neg i hi
    · show k7 * det3 (x 3 - x 2) (x 5 - x 2) (x i - x 2) < 0
      rw [← h7]; exact T.f235.neg i hi

/-- **The approximating sequence of §18.6 step 2 for type 21**: a type-21 shape `x` with at most
one tie at its named views is a limit of shapes `K_n`, each with a certificate (`Cert21`) and
with the tie of `x`.  No general position, no sign condition or Gale equality of the cover, no
(G1), no planar equator, no switch surface. -/
theorem exists_certSeq21 {x : Fin 7 → ℝ³} (T : Facets21 x) (htie : OneTie21 x) :
    ∃ K : ℕ → Fin 7 → ℝ³, (∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m))) ∧
      ∃ᶠ n in atTop, Cert21 (K n) ∧
        ∀ w a b, TieInst21 x w a b → ⟪K n a - K n b, view21 (K n) w⟫ = 0 := by
  classical
  set θ₀ := theta21 x with hθ₀
  have hx : x = nfShape21 (x 2) (x 0 - x 2) (x 3 - x 2) (x 6 - x 2) θ₀ := T.eq_nfShape
  set o := x 2 with ho
  set E₁ := x 0 - x 2 with hE₁
  set E₂ := x 3 - x 2 with hE₂
  set E₃ := x 6 - x 2 with hE₃
  obtain ⟨θs, hθs, hgen⟩ := exists_seq_eval_ne_zero genPoly21_ne_zero θ₀
  set Y : ℕ → Fin 7 → ℝ³ := fun n => nfShape21 o E₁ E₂ E₃ (θs n) with hYdef
  have hY : ∀ m, Tendsto (fun n => Y n m) atTop (𝓝 (x m)) := by
    intro m
    have := tendsto_nfShape21 (o := fun _ : ℕ => o) (E₁ := fun _ => E₁) (E₂ := fun _ => E₂)
      (E₃ := fun _ => E₃) tendsto_const_nhds tendsto_const_nhds tendsto_const_nhds
      tendsto_const_nhds hθs m
    rw [← hx] at this; exact this
  -- the shear that restores the tie of `x`, if any
  obtain ⟨ss, es, bs, hss, ⟨e₀, hes⟩, ⟨b₀, hbs⟩, horth, hrest⟩ : ∃ (ss : ℕ → ℝ) (es bs : ℕ → ℝ³),
      Tendsto ss atTop (𝓝 0) ∧ (∃ e₀, Tendsto es atTop (𝓝 e₀)) ∧
      (∃ b₀, Tendsto bs atTop (𝓝 b₀)) ∧ (∀ n, ⟪es n, bs n⟫ = 0) ∧
      ∀ᶠ n in atTop, ∀ w a b, TieInst21 x w a b →
        ⟪restore (ss n) (es n) (bs n) (Y n a) - restore (ss n) (es n) (bs n) (Y n b),
          view21 (fun i => restore (ss n) (es n) (bs n) (Y n i)) w⟫ = 0 := by
    by_cases hT : ∃ w a b, TieInst21 x w a b
    · obtain ⟨w₀, a₀, b₀, hab₀, hw₀, ht₀⟩ := hT
      set A : ℕ → ℝ³ := fun n => view21 (Y n) w₀ with hAdef
      set B : ℕ → ℝ³ := fun n => Y n a₀ - Y n b₀ with hBdef
      have hA : Tendsto A atTop (𝓝 (view21 x w₀)) := tendsto_view21 hY w₀
      have hB : Tendsto B atTop (𝓝 (x a₀ - x b₀)) := (hY a₀).sub (hY b₀)
      have hBB : 0 < ⟪x a₀ - x b₀, x a₀ - x b₀⟫ :=
        real_inner_self_pos.mpr (sub_ne_zero.mpr (T.inj.ne hab₀))
      have hAA : 0 < ⟪view21 x w₀, view21 x w₀⟫ := real_inner_self_pos.mpr hw₀
      have hAB : ⟪view21 x w₀, x a₀ - x b₀⟫ = 0 := by rw [real_inner_comm]; exact ht₀
      set E : ℕ → ℝ³ := fun n => A n - (⟪A n, B n⟫ / ⟪B n, B n⟫) • B n with hEdef
      have hE : Tendsto E atTop (𝓝 (view21 x w₀)) := by
        have h1 : Tendsto (fun n => ⟪A n, B n⟫ / ⟪B n, B n⟫) atTop
            (𝓝 (⟪view21 x w₀, x a₀ - x b₀⟫ / ⟪x a₀ - x b₀, x a₀ - x b₀⟫)) :=
          (hA.inner hB).div (hB.inner hB) hBB.ne'
        rw [hAB, zero_div] at h1
        have h2 := hA.sub (h1.smul hB)
        rw [zero_smul, sub_zero] at h2
        exact h2
      set S : ℕ → ℝ := fun n => -⟪A n, B n⟫ / (⟪A n, E n⟫ * ⟪B n, B n⟫) with hSdef
      have hS : Tendsto S atTop (𝓝 0) := by
        have h1 : Tendsto (fun n => -⟪A n, B n⟫) atTop (𝓝 (-⟪view21 x w₀, x a₀ - x b₀⟫)) :=
          (hA.inner hB).neg
        rw [hAB, neg_zero] at h1
        have h2 : Tendsto (fun n => ⟪A n, E n⟫ * ⟪B n, B n⟫) atTop
            (𝓝 (⟪view21 x w₀, view21 x w₀⟫ * ⟪x a₀ - x b₀, x a₀ - x b₀⟫)) :=
          (hA.inner hE).mul (hB.inner hB)
        have h3 := h1.div h2 (mul_pos hAA hBB).ne'
        rw [zero_div] at h3
        exact h3
      have horth : ∀ n, ⟪E n, B n⟫ = 0 := by
        intro n
        by_cases hb : ⟪B n, B n⟫ = 0
        · rw [inner_self_eq_zero.mp hb, inner_zero_right]
        · simp only [hEdef, inner_sub_left, real_inner_smul_left]
          field_simp; ring
      refine ⟨S, E, B, hS, ⟨_, hE⟩, ⟨_, hB⟩, horth, ?_⟩
      have ev1 : ∀ᶠ n in atTop, ⟪B n, B n⟫ ≠ 0 := (hB.inner hB).eventually_ne hBB.ne'
      have ev2 : ∀ᶠ n in atTop, ⟪A n, E n⟫ ≠ 0 := (hA.inner hE).eventually_ne hAA.ne'
      filter_upwards [ev1, ev2] with n h1 h2 w a b hw
      refine (htie w₀ a₀ b₀ w a b ⟨hab₀, hw₀, ht₀⟩ hw).inner_eq_zero _ ?_
      rw [← restore_sub, view21_restore (horth n)]
      show ⟪restore (S n) (E n) (B n) (B n), restore (S n) (E n) (B n) (A n)⟫ = 0
      simp only [restore, horth n, mul_zero, zero_smul, add_zero, inner_add_right,
        real_inner_smul_right]
      rw [hSdef, real_inner_comm (A n) (E n), real_inner_comm (A n) (B n)]
      field_simp
      ring
    · exact ⟨fun _ => 0, fun _ => 0, fun _ => 0, tendsto_const_nhds, ⟨0, tendsto_const_nhds⟩,
        ⟨0, tendsto_const_nhds⟩, fun _ => inner_zero_left _,
        Eventually.of_forall fun _ w a b hw => absurd ⟨w, a, b, hw⟩ hT⟩
  -- the restored shapes, as normal-form shapes
  set R : ℕ → ℝ³ → ℝ³ := fun n => restore (ss n) (es n) (bs n) with hRdef
  set K : ℕ → Fin 7 → ℝ³ := fun n =>
    nfShape21 (R n o) (R n E₁) (R n E₂) (R n E₃) (θs n) with hKdef
  have hKY : ∀ n, K n = fun i => R n (Y n i) := fun n =>
    (restore_nfShape21 (ss n) (es n) (bs n) o E₁ E₂ E₃ (θs n)).symm
  have hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m)) := by
    intro m
    simp only [hKY]
    exact tendsto_restore hss hes hbs (hY m)
  obtain ⟨κ, hκ, hneg⟩ := T.exists_kappa
  have hfac : ∀ᶠ n in atTop, ∀ f i, i ∉ facS f → fac21 κ (K n) f (K n i) < 0 := by
    refine eventually_all.mpr fun f => eventually_all.mpr fun i => ?_
    by_cases hi : i ∈ facS f
    · exact Eventually.of_forall fun _ h => absurd hi h
    · have hlim : Tendsto (fun n => fac21 κ (K n) f (K n i)) atTop
          (𝓝 (fac21 κ x f (x i))) := by
        simp only [fac21, detAff_apply]
        exact (Tendsto.det3' ((hK _).sub (hK _)) ((hK _).sub (hK _))
          ((hK _).sub (hK _))).const_mul _
      exact (hlim.eventually (gt_mem_nhds (hneg f i hi))).mono fun n hn _ => hn
  have hvtx : ∀ᶠ n in atTop, ∀ t, vtxView21 (K n) t ≠ 0 :=
    eventually_all.mpr fun t => (tendsto_view21 hK (.inr t)).eventually_ne (T.vtxView21_ne_zero t)
  have hsegs : ∀ᶠ n in atTop, ∀ i j : Fin 7, i ≠ j → K n i - K n j ≠ 0 :=
    eventually_all.mpr fun i => eventually_all.mpr fun j => by
      by_cases hij : i = j
      · exact Eventually.of_forall fun _ h => absurd hij h
      · exact (((hK i).sub (hK j)).eventually_ne (sub_ne_zero.mpr (T.inj.ne hij))).mono
          fun n hn _ => hn
  refine ⟨K, hK, Eventually.frequently ?_⟩
  filter_upwards [eventually_ties21 hK, hrest, hfac, hvtx, hsegs] with n hs hr hf hv hw
  refine ⟨?_, fun w a b hw => by rw [hKY n]; exact hr w a b hw⟩
  have hD : det3 (R n E₁) (R n E₂) (R n E₃) ≠ 0 := by
    rw [hRdef]; simp only; rw [det3_restore (horth n)]; exact T.det_ne
  have hg : gen21 (θs n) ≠ 0 := by have := hgen n; rwa [eval_genPoly21] at this
  have hsubK : ∀ w a b, a ≠ b → view21 (K n) w ≠ 0 → ⟪K n a - K n b, view21 (K n) w⟫ = 0 →
      TieInst21 x w a b := by
    intro w a b hab hw h
    refine ⟨hab, T.view21_ne_zero w ?_, hs w a b h⟩
    rintro i rfl
    exact hw (by simp [view21])
  have hgt : TieSeg (univ.image (K n)) := by
    refine ⟨fun v hv w hw hvw => ?_⟩
    obtain ⟨i, -, rfl⟩ := mem_image.mp hv
    obtain ⟨j, -, rfl⟩ := mem_image.mp hw
    exact oneTieAt_of_ties21 htie hsubK (.inl (i, j)) (sub_ne_zero.mpr (Ne.symm hvw))
  have hvt : ∀ t, OneTieAt (univ.image (K n)) (vtxView21 (K n) t) := fun t =>
    oneTieAt_of_ties21 htie hsubK (.inr t) (hv t)
  exact cert21_of_generic rfl hD hg hκ hf hgt hvt
    ⟨noTieAt_seg_of_tie htie hsubK (by decide) (hv 0) (hw 0 4 (by decide)),
      noTieAt_seg_of_tie htie hsubK (by decide) (hv 1) (hw 4 0 (by decide)),
      noTieAt_seg_of_tie htie hsubK (by decide) (hv 2) (hw 5 3 (by decide)),
      noTieAt_seg_of_tie htie hsubK (by decide) (hv 3) (hw 3 5 (by decide))⟩
    ⟨noTieAt_or htie hsubK (by decide) (hv 1) (hv 4),
      noTieAt_or htie hsubK (by decide) (hv 0) (hv 5),
      noTieAt_or htie hsubK (by decide) (hv 3) (hv 6),
      noTieAt_or htie hsubK (by decide) (hv 2) (hv 7)⟩


/-- **Type 21 outside the HDN set and codimension 2** (§18.6 step 2).  A type-21 shape `x`
(facets `T`) with at most one tie at its named views (`OneTie21`: the segments and the eight
vertex crossings of the cover) and no horizontal double normal at them is Rupert.  No general
position, no sign condition or Gale equality of the cover, no (G1), no planar equator, no switch
surface: `x` is a limit of shapes `K_n` off the special positions of the cover (`genPoly21`) with
the same tie as `x` (restored by a unimodular shear), each `K_n` has a certificate
(`cert21_of_generic`: at most one tie at each named view, no tie along `a − b` if `a, b` tie at a
view of `T1`, a tie at no more than one view of F2), a subsequence carries one labelled
certificate, and the limit lemma applies. -/
theorem isRupert_type21_limit {x : Fin 7 → ℝ³} (T : Facets21 x)
    (hnd : ∀ v, view21 x v ≠ 0 → NoHDNAt (univ.image x) (view21 x v))
    (htie : OneTie21 x) : IsRupert (univ.image x) := by
  obtain ⟨K, hK, hc⟩ := exists_certSeq21 T htie
  exact isRupert_of_cert_seq21 T hnd K hK hc

/-- The two facet normals at a vertex crossing are orthogonal to its view. -/
theorem vtxView21_perp {x : Fin 7 → ℝ³} {SP SQ : Finset (Fin 7)} (FP : Face16 x SP)
    (FQ : Face16 x SQ) (t : Fin 8) (h0 : (vtx21 t).1.1 ∈ SP) (h1 : (vtx21 t).1.2.1 ∈ SP)
    (h2 : (vtx21 t).1.2.2 ∈ SP) (k0 : (vtx21 t).2.1 ∈ SQ) (k1 : (vtx21 t).2.2.1 ∈ SQ)
    (k2 : (vtx21 t).2.2.2 ∈ SQ) :
    ⟪FP.N, vtxView21 x t⟫ = 0 ∧ ⟪FQ.N, vtxView21 x t⟫ = 0 :=
  ⟨inner_planeLine_left (FP.inner_sub h1 h0) (FP.inner_sub h2 h0),
    inner_planeLine_right (FQ.inner_sub k1 k0) (FQ.inner_sub k2 k0)⟩

/-- **Type 21 outside the HDN set and codimension 2, from the facets**: seven points labelled so
that `014, 015, 0256, 046, 134, 135, 2346, 235` are facets (functionals negative off them) are
Rupert, if there is no horizontal double normal at the view along any segment and along the
lines of the eight facet pairs `014/0256`, `014/2346`, `135/0256`, `135/2346`, `046/134`,
`046/015`, `235/134`, `235/015`, and at most one tie at these views (`OneTie21`). -/
theorem isRupert_type21_limit_facets (x : Fin 7 → ℝ³) (hx : Function.Injective x)
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
    (hnd : ∀ v ∈ univ.image x, ∀ w ∈ univ.image x, v ≠ w →
      NoHDNAt ((univ.image x).erase w) (w - v))
    (hV : NoHDNAff (univ.image x) fA fC ∧ NoHDNAff (univ.image x) fA fG ∧
      NoHDNAff (univ.image x) fF fC ∧ NoHDNAff (univ.image x) fF fG ∧
      NoHDNAff (univ.image x) fD fE ∧ NoHDNAff (univ.image x) fD fB ∧
      NoHDNAff (univ.image x) fH fE ∧ NoHDNAff (univ.image x) fH fB)
    (htie : OneTie21 x) : IsRupert (univ.image x) := by
  let T := Facets21.ofAffine x hx fA fB fC fD fE fF fG fH hA hB hC hD hE hF hG hH
  refine isRupert_type21_limit T (fun v hv => ?_) htie
  rcases v with ⟨i, j⟩ | t
  · have hij : x i ≠ x j := fun h => hv (by simp [view21, h])
    have mi := mem_image_of_mem x (mem_univ i)
    have mj := mem_image_of_mem x (mem_univ j)
    exact noHDNAt_of_erase hij (hnd _ mi _ mj hij)
      (by simpa only [neg_sub] using (hnd _ mj _ mi (Ne.symm hij)).neg)
  · obtain ⟨V1, V2, V3, V4, V5, V6, V7, V8⟩ := hV
    fin_cases t
    · obtain ⟨p, q⟩ := vtxView21_perp (x := x) T.f014 T.f0256 0 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
      exact V1 _ hv (by rw [← Face16.ofAffine_inner fA hA]; exact p)
        (by rw [← Face16.ofAffine_inner fC hC]; exact q)
    · obtain ⟨p, q⟩ := vtxView21_perp (x := x) T.f014 T.f2346 1 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
      exact V2 _ hv (by rw [← Face16.ofAffine_inner fA hA]; exact p)
        (by rw [← Face16.ofAffine_inner fG hG]; exact q)
    · obtain ⟨p, q⟩ := vtxView21_perp (x := x) T.f135 T.f0256 2 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
      exact V3 _ hv (by rw [← Face16.ofAffine_inner fF hF]; exact p)
        (by rw [← Face16.ofAffine_inner fC hC]; exact q)
    · obtain ⟨p, q⟩ := vtxView21_perp (x := x) T.f135 T.f2346 3 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
      exact V4 _ hv (by rw [← Face16.ofAffine_inner fF hF]; exact p)
        (by rw [← Face16.ofAffine_inner fG hG]; exact q)
    · obtain ⟨p, q⟩ := vtxView21_perp (x := x) T.f046 T.f134 4 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
      exact V5 _ hv (by rw [← Face16.ofAffine_inner fD hD]; exact p)
        (by rw [← Face16.ofAffine_inner fE hE]; exact q)
    · obtain ⟨p, q⟩ := vtxView21_perp (x := x) T.f046 T.f015 5 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
      exact V6 _ hv (by rw [← Face16.ofAffine_inner fD hD]; exact p)
        (by rw [← Face16.ofAffine_inner fB hB]; exact q)
    · obtain ⟨p, q⟩ := vtxView21_perp (x := x) T.f235 T.f134 6 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
      exact V7 _ hv (by rw [← Face16.ofAffine_inner fH hH]; exact p)
        (by rw [← Face16.ofAffine_inner fE hE]; exact q)
    · obtain ⟨p, q⟩ := vtxView21_perp (x := x) T.f235 T.f015 7 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
      exact V8 _ hv (by rw [← Face16.ofAffine_inner fH hH]; exact p)
        (by rw [← Face16.ofAffine_inner fB hB]; exact q)

end Minimality

end
