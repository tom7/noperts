module

public import Minimality.Type08T4
public import Minimality.QuadFacets

@[expose] public section

/-!
# Type 08: Theorem 10.1

A type-08 point set is an octahedron `O` (opposite pairs `(a, a')`, `(b, b')`,
`(c, c')`) with a cap `d` (`IsCap`): `d` lies on the planes of `abc'`, `ab'c`,
`a'bc`, beyond `abc` and beneath the other four faces.  **Theorem 10.1**
(`isRupert_type08`): with no planar equator of `O`, in general position
(`GenPos`: no two segments parallel or orthogonal; `NoPlaneParallel`: no plane
through three of the points parallel to the segment of two others) and without a
horizontal double normal at the views along the segments (`NoHDNAt`), the seven
points are Rupert.

The proof (`isRupert_type08_normalized`): in the labelling of Lemma 6
(`type08_lemma6`; `κ_a, κ_b > 0`, `[b c] < 0`), view along the QQ edge `d b`.
* If the far end of `Q_bc` is `a'` (Lemma 1 (a)), Lemma 7 makes `a' → c` a quad edge
  of `O` that is not bad, Lemma 2 makes the cap a middle at its view, and Lemma 9.3
  with a middle applies (`isRupert_quad_edge_middle`).
* If the far ends are `a` and `c`, `K_d` is the face `Q_ac` (Lemma 1 (c),
  `isRupert_type08_Q`).
* If the far ends are `c'` and `c`, the T4 `K − a` at its edge `d b` (Lemma 5,
  `isRupert_type08_T4`, with Lemmas 9.7, 4, 3 for "not bad").
Ties between the far ends would make two segments parallel (`GenPos`).
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- No plane through three of the points is parallel to the segment of two
others (a general-position condition; for type 08 it excludes, at the view along a
QQ edge `d b`, the vertex `b'` lying on the line of the images of `c`, `c'`). -/
def NoPlaneParallel (V : Finset ℝ³) : Prop :=
  ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V, ∀ v ∈ V, ∀ w ∈ V, [p, q, r, v, w].Nodup →
    det3 (q - p) (r - p) (w - v) ≠ 0

/-- `GenPos`: distinct depths along a segment, for a pair not containing its
second end. -/
theorem GenPos.inner_ne_of_ne {V : Finset ℝ³} (hg : GenPos V) {s t x y : ℝ³} (hs : s ∈ V)
    (ht : t ∈ V) (hx : x ∈ V) (hy : y ∈ V) (hst : s ≠ t) (hxy : x ≠ y)
    (hne : t ≠ x ∧ t ≠ y ∨ s ≠ y ∧ t ≠ y) : ⟪s, y - x⟫ ≠ ⟪t, y - x⟫ := by
  have hpair : ({s, t} : Finset ℝ³) ≠ {x, y} := by
    intro heq
    rcases hne with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have : t ∈ ({x, y} : Finset ℝ³) := heq ▸ (by simp)
      simp only [mem_insert, mem_singleton] at this
      tauto
    · have : y ∈ ({s, t} : Finset ℝ³) := heq ▸ (by simp)
      simp only [mem_insert, mem_singleton] at this
      tauto
  intro h
  apply (hg s hs t ht x hx y hy hst hxy hpair).2
  rw [inner_sub_left, h, sub_self]

/-- `GenPos`: two segments that are not the same pair are not parallel. -/
theorem GenPos.ne_smul {V : Finset ℝ³} (hg : GenPos V) {s t x y : ℝ³} (hs : s ∈ V)
    (ht : t ∈ V) (hx : x ∈ V) (hy : y ∈ V) (hst : s ≠ t) (hxy : x ≠ y) (hty : t ≠ x ∧ t ≠ y)
    (r : ℝ) : t - s ≠ r • (y - x) := by
  have hpair : ({s, t} : Finset ℝ³) ≠ {x, y} := by
    intro heq
    have : t ∈ ({x, y} : Finset ℝ³) := heq ▸ (by simp)
    simp only [mem_insert, mem_singleton] at this
    tauto
  exact (hg s hs t ht x hx y hy hst hxy hpair).1 r

/-- A facet function with its linear part is an affine map: a facet. -/
theorem FacetFn.isFacetTriangle {V : Finset ℝ³} {P Q R : ℝ³} (F : FacetFn V P Q R) :
    IsFacetTriangle V P Q R :=
  ⟨{ toFun := F.f
     linear :=
       { toFun := fun v => ⟪F.N, v⟫
         map_add' := fun u v => inner_add_right _ _ _
         map_smul' := fun r v => by simp [real_inner_smul_right] }
     map_vadd' := fun p v => by
       have h1 := F.hN (v + p) p
       rw [add_sub_cancel_right] at h1
       show F.f (v + p) = ⟪F.N, v⟫ + F.f p
       linarith }, F.hP, F.hQ, F.hR, F.neg⟩

theorem OctFacets.isOctahedron {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c') :
    IsOctahedron a a' b b' c c' :=
  ⟨F.nodup, F.abc.isFacetTriangle, F.abc'.isFacetTriangle, F.ab'c.isFacetTriangle,
    F.ab'c'.isFacetTriangle, F.a'bc.isFacetTriangle, F.a'bc'.isFacetTriangle,
    F.a'b'c.isFacetTriangle, F.a'b'c'.isFacetTriangle⟩

theorem type08_set_perm (a a' b b' c c' d : ℝ³) :
    (insert d ({a', a, c, c', b, b'} : Finset ℝ³)) = insert d {a, a', b, b', c, c'} ∧
    (insert d ({b, b', a, a', c, c'} : Finset ℝ³)) = insert d {a, a', b, b', c, c'} ∧
    (insert d ({a, a', c, c', b, b'} : Finset ℝ³)) = insert d {a, a', b, b', c, c'} ∧
    (insert d ({c, c', a, a', b, b'} : Finset ℝ³)) = insert d {a, a', b, b', c, c'} ∧
    (insert d ({b, b', c, c', a, a'} : Finset ℝ³)) = insert d {a, a', b, b', c, c'} ∧
    (insert d ({c, c', b, b', a, a'} : Finset ℝ³)) = insert d {a, a', b, b', c, c'} := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)

/-- The mirrored Gale vectors (`[s t] ↦ −[s t]`). -/
def GaleData.mirror {a a' b b' c c' : ℝ³} (G : GaleData a a' b b' c c') :
    GaleData a a' b b' c c' :=
  ⟨G.m, G.l, G.hm, G.hl, fun α β h1 h2 h3 h4 h5 h6 =>
    (G.indep β α (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
      (by linarith)).symm⟩

theorem GaleData.galeD_mirror {a a' b b' c c' : ℝ³} (G : GaleData a a' b b' c c') (s t : ℝ³) :
    galeD G.mirror.l G.mirror.m s t = -galeD G.l G.m s t := by
  simp only [GaleData.mirror, galeD]; ring

/-! ### Theorem 10.1 from facet functionals of the seven points -/

/-- A facet function of `{x i : i ∈ I}` from an affine map that vanishes exactly
on the indices `S`. -/
noncomputable def facetFn_of_index (x : Fin 7 → ℝ³) (f : ℝ³ →ᵃ[ℝ] ℝ) (S : Finset (Fin 7))
    (hf : ∀ i, (i ∈ S → f (x i) = 0) ∧ (i ∉ S → f (x i) < 0)) (I : Finset (Fin 7))
    {i j k : Fin 7} (hi : i ∈ S) (hj : j ∈ S) (hk : k ∈ S)
    (hI : ∀ l ∈ I, l ≠ i → l ≠ j → l ≠ k → l ∉ S) : FacetFn (I.image x) (x i) (x j) (x k) :=
  ⟨f, Classical.choose (exists_normal_of_affine f), Classical.choose_spec (exists_normal_of_affine f),
    (hf i).1 hi, (hf j).1 hj, (hf k).1 hk, fun w hw h1 h2 h3 => by
      obtain ⟨l, hl, rfl⟩ := mem_image.mp hw
      exact (hf l).2 (hI l hl (fun h => h1 (by rw [h])) (fun h => h2 (by rw [h]))
        (fun h => h3 (by rw [h])))⟩

theorem image_seven (x : Fin 7 → ℝ³) :
    (({0, 6, 3, 4, 5, 1} : Finset (Fin 7)).image x) = {x 0, x 6, x 3, x 4, x 5, x 1} ∧
    univ.image x = insert (x 2) ({x 0, x 6, x 3, x 4, x 5, x 1} : Finset ℝ³) := by
  constructor
  · simp [Finset.image_insert]
  · ext z
    simp only [mem_image, mem_univ, true_and, mem_insert, mem_singleton]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      exacts [⟨2, rfl⟩, ⟨0, rfl⟩, ⟨6, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩, ⟨5, rfl⟩, ⟨1, rfl⟩]

set_option maxHeartbeats 400000 in
/-- The facet data of type 08 (`typeb_lib.load('08-7f')`) make `x 2` a cap (`IsCap`) over the
octahedron of the other six points (opposite pairs `(0, 6)`, `(3, 4)`, `(5, 1)`; its eighth
face `035` is constructed). -/
theorem exists_type08_cap (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (fA fB fC fD fE fF fG : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 1, 2, 3} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 1, 2, 3} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({0, 2, 4, 5} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({0, 2, 4, 5} : Finset (Fin 7)) → fB (x i) < 0))
    (hC : ∀ i, (i ∈ ({2, 3, 5, 6} : Finset (Fin 7)) → fC (x i) = 0) ∧
      (i ∉ ({2, 3, 5, 6} : Finset (Fin 7)) → fC (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 1, 4} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 1, 4} : Finset (Fin 7)) → fD (x i) < 0))
    (hE : ∀ i, (i ∈ ({1, 3, 6} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({1, 3, 6} : Finset (Fin 7)) → fE (x i) < 0))
    (hF : ∀ i, (i ∈ ({1, 4, 6} : Finset (Fin 7)) → fF (x i) = 0) ∧
      (i ∉ ({1, 4, 6} : Finset (Fin 7)) → fF (x i) < 0))
    (hG : ∀ i, (i ∈ ({4, 5, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({4, 5, 6} : Finset (Fin 7)) → fG (x i) < 0)) :
    ∃ F : OctFacets (x 0) (x 6) (x 3) (x 4) (x 5) (x 1), IsCap F (x 2) := by
  classical
  obtain ⟨eI, -⟩ := image_seven x
  obtain ⟨NA, hNA⟩ := exists_normal_of_affine fA
  obtain ⟨NB, hNB⟩ := exists_normal_of_affine fB
  obtain ⟨NC, hNC⟩ := exists_normal_of_affine fC
  obtain ⟨ND, hND⟩ := exists_normal_of_affine fD
  obtain ⟨NE, hNE⟩ := exists_normal_of_affine fE
  obtain ⟨NG, hNG⟩ := exists_normal_of_affine fG
  have hN : ∀ {f : ℝ³ →ᵃ[ℝ] ℝ} {N : ℝ³}, (∀ y z, f y - f z = ⟪N, y - z⟫) →
      ∀ y z, (f : ℝ³ → ℝ) y - f z = ⟪N, y - z⟫ := fun h => h
  -- the values used below
  have A0 := (hA 0).1 (by decide); have A1 := (hA 1).1 (by decide)
  have A2 := (hA 2).1 (by decide); have A3 := (hA 3).1 (by decide)
  have A4 := (hA 4).2 (by decide); have A5 := (hA 5).2 (by decide)
  have A6 := (hA 6).2 (by decide)
  have B0 := (hB 0).1 (by decide); have B2 := (hB 2).1 (by decide)
  have B4 := (hB 4).1 (by decide); have B5 := (hB 5).1 (by decide)
  have B1 := (hB 1).2 (by decide); have B3 := (hB 3).2 (by decide)
  have C2 := (hC 2).1 (by decide); have C3 := (hC 3).1 (by decide)
  have C5 := (hC 5).1 (by decide); have C6 := (hC 6).1 (by decide)
  have C0 := (hC 0).2 (by decide)
  have D0 := (hD 0).1 (by decide); have D1 := (hD 1).1 (by decide)
  have D4 := (hD 4).1 (by decide); have D2 := (hD 2).2 (by decide)
  have D3 := (hD 3).2 (by decide); have D5 := (hD 5).2 (by decide)
  have E1 := (hE 1).1 (by decide); have E3 := (hE 3).1 (by decide)
  have E6 := (hE 6).1 (by decide); have E0 := (hE 0).2 (by decide)
  have E2 := (hE 2).2 (by decide); have E5 := (hE 5).2 (by decide)
  have G4 := (hG 4).1 (by decide); have G5 := (hG 5).1 (by decide)
  have G6 := (hG 6).1 (by decide); have G0 := (hG 0).2 (by decide)
  have G2 := (hG 2).2 (by decide); have G3 := (hG 3).2 (by decide)
  -- the plane of `0 3 5`
  set g₀ : ℝ³ → ℝ := fun X => det3 (x 3 - x 0) (x 5 - x 0) (X - x 0) with hg₀_def
  have hg₀ : ∀ y z, g₀ y - g₀ z = ⟪cross (x 3 - x 0) (x 5 - x 0), y - z⟫ := by
    intro y z; simp only [g₀, det3, ← inner_sub_right]; congr 1; abel
  have g0 : g₀ (x 0) = 0 := by simp only [g₀, sub_self]; simp [det3_expand]
  have g3 : g₀ (x 3) = 0 := by simp only [g₀, det3_expand]; ring
  have g5 : g₀ (x 5) = 0 := by simp only [g₀, det3_expand]; ring
  -- the quadrilateral `0123` (cyclic `2, 0, 1, 3`): `g₀ (x 2) = (1 − s − t) g₀ (x 1)`, `s + t > 1`
  have qA := coords_of_affine3 (hN hNA) (hN hNE) (hN hND) (o := x 1) (p := x 0) (q := x 3)
    (w := x 2) A1 A0 A3 A2 A4.ne E1 E3 E0.ne D1 D0 D3.ne
  set sA := fE (x 2) / fE (x 0)
  set tA := fD (x 2) / fD (x 3)
  have htA : 0 < tA := div_pos_of_neg_of_neg D2 D3
  have kA : 1 - sA - tA < 0 := by
    have hf := affine_frame (hN hNB) (x 1) (x 0) (x 3) sA tA
    rw [← qA, B2, B0] at hf
    nlinarith [mul_pos htA (neg_pos.mpr B3)]
  have gA : g₀ (x 2) = (1 - sA - tA) * g₀ (x 1) := by
    have hf := affine_frame hg₀ (x 1) (x 0) (x 3) sA tA
    rw [← qA, g0, g3] at hf; linarith
  -- the quadrilateral `0245` (cyclic `2, 0, 4, 5`)
  have qB := coords_of_affine3 (hN hNB) (hN hNG) (hN hND) (o := x 4) (p := x 0) (q := x 5)
    (w := x 2) B4 B0 B5 B2 B1.ne G4 G5 G0.ne D4 D0 D5.ne
  set sB := fG (x 2) / fG (x 0)
  set tB := fD (x 2) / fD (x 5)
  have htB : 0 < tB := div_pos_of_neg_of_neg D2 D5
  have kB : 1 - sB - tB < 0 := by
    have hf := affine_frame (hN hNA) (x 4) (x 0) (x 5) sB tB
    rw [← qB, A2, A0] at hf
    nlinarith [mul_pos htB (neg_pos.mpr A5)]
  have gB : g₀ (x 2) = (1 - sB - tB) * g₀ (x 4) := by
    have hf := affine_frame hg₀ (x 4) (x 0) (x 5) sB tB
    rw [← qB, g0, g5] at hf; linarith
  -- the quadrilateral `2356` (cyclic `2, 3, 6, 5`)
  have qC := coords_of_affine3 (hN hNC) (hN hNG) (hN hNE) (o := x 6) (p := x 3) (q := x 5)
    (w := x 2) C6 C3 C5 C2 C0.ne G6 G5 G3.ne E6 E3 E5.ne
  set sC := fG (x 2) / fG (x 3)
  set tC := fE (x 2) / fE (x 5)
  have htC : 0 < tC := div_pos_of_neg_of_neg E2 E5
  have kC : 1 - sC - tC < 0 := by
    have hf := affine_frame (hN hNA) (x 6) (x 3) (x 5) sC tC
    rw [← qC, A2, A3] at hf
    nlinarith [mul_pos htC (neg_pos.mpr A5)]
  have gC : g₀ (x 2) = (1 - sC - tC) * g₀ (x 6) := by
    have hf := affine_frame hg₀ (x 6) (x 3) (x 5) sC tC
    rw [← qC, g3, g5] at hf; linarith
  -- `x 2` is off the plane of `0 3 5` (else `x 5` would be on the plane of `0123`)
  have g2 : g₀ (x 2) ≠ 0 := by
    intro h0
    have hc := cross_ne_zero_of_affine (hN hNB) (hx.ne (by decide : (0 : Fin 7) ≠ 2)) B0 B2 B3
    have := affine_zero_of_coplanar (hN hNA) A0 A2 A3 hc (w := x 5) (by
      have e : det3 (x 2 - x 0) (x 3 - x 0) (x 5 - x 0) = g₀ (x 2) := by
        simp only [g₀, det3_expand]; ring
      rw [e, h0])
    linarith
  -- the face `035`, oriented so that the cap is beyond it
  set g : ℝ³ → ℝ := fun X => g₀ (x 2) * g₀ X with hg_def
  have hg : ∀ y z, g y - g z = ⟪g₀ (x 2) • cross (x 3 - x 0) (x 5 - x 0), y - z⟫ := by
    intro y z; simp only [g, real_inner_smul_left, ← hg₀]; ring
  have sq := mul_self_pos.mpr g2
  have gneg : ∀ (k : ℝ) (X : ℝ³), k < 0 → g₀ (x 2) = k * g₀ X → g X < 0 := by
    intro k X hk h
    have hX : g₀ X ≠ 0 := by intro h0; rw [h0, mul_zero] at h; exact g2 h
    have : g X = k * (g₀ X * g₀ X) := by simp only [g]; rw [h]; ring
    rw [this]; exact mul_neg_of_neg_of_pos hk (mul_self_pos.mpr hX)
  have n06 := hx.ne (by decide : (0 : Fin 7) ≠ 6)
  have n03 := hx.ne (by decide : (0 : Fin 7) ≠ 3)
  have n05 := hx.ne (by decide : (0 : Fin 7) ≠ 5)
  have n36 := hx.ne (by decide : (3 : Fin 7) ≠ 6)
  have n56 := hx.ne (by decide : (5 : Fin 7) ≠ 6)
  have n34 := hx.ne (by decide : (3 : Fin 7) ≠ 4)
  have n45 := hx.ne (by decide : (4 : Fin 7) ≠ 5)
  have n04 := hx.ne (by decide : (0 : Fin 7) ≠ 4)
  have n01 := hx.ne (by decide : (0 : Fin 7) ≠ 1)
  have n13 := hx.ne (by decide : (1 : Fin 7) ≠ 3)
  have n15 := hx.ne (by decide : (1 : Fin 7) ≠ 5)
  let Fabc : FacetFn {x 0, x 6, x 3, x 4, x 5, x 1} (x 0) (x 3) (x 5) :=
    ⟨g, _, hg, by simp only [g, g0, mul_zero], by simp only [g, g3, mul_zero],
      by simp only [g, g5, mul_zero], fun w hw h1 h2 h3 => by
        simp only [mem_insert, mem_singleton] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
        · exact absurd rfl h1
        · exact gneg _ _ kC gC
        · exact absurd rfl h2
        · exact gneg _ _ kB gB
        · exact absurd rfl h3
        · exact gneg _ _ kA gA⟩
  have hnodup : [x 0, x 6, x 3, x 4, x 5, x 1].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true]
    refine ⟨⟨n06, n03, n04, n05, n01⟩, ⟨Ne.symm n36, hx.ne (by decide), Ne.symm n56,
      hx.ne (by decide)⟩, ⟨n34, hx.ne (by decide), n13.symm⟩, ⟨n45, hx.ne (by decide)⟩, n15.symm, not_false⟩
  let F : OctFacets (x 0) (x 6) (x 3) (x 4) (x 5) (x 1) :=
    ⟨hnodup, Fabc,
      (facetFn_of_index x fA _ hA {0, 6, 3, 4, 5, 1} (i := 0) (j := 3) (k := 1)
        (by decide) (by decide) (by decide) (by decide)).congr eI,
      (facetFn_of_index x fB _ hB {0, 6, 3, 4, 5, 1} (i := 0) (j := 4) (k := 5)
        (by decide) (by decide) (by decide) (by decide)).congr eI,
      (facetFn_of_index x fD _ hD {0, 6, 3, 4, 5, 1} (i := 0) (j := 4) (k := 1)
        (by decide) (by decide) (by decide) (by decide)).congr eI,
      (facetFn_of_index x fC _ hC {0, 6, 3, 4, 5, 1} (i := 6) (j := 3) (k := 5)
        (by decide) (by decide) (by decide) (by decide)).congr eI,
      (facetFn_of_index x fE _ hE {0, 6, 3, 4, 5, 1} (i := 6) (j := 3) (k := 1)
        (by decide) (by decide) (by decide) (by decide)).congr eI,
      (facetFn_of_index x fG _ hG {0, 6, 3, 4, 5, 1} (i := 6) (j := 4) (k := 5)
        (by decide) (by decide) (by decide) (by decide)).congr eI,
      (facetFn_of_index x fF _ hF {0, 6, 3, 4, 5, 1} (i := 6) (j := 4) (k := 1)
        (by decide) (by decide) (by decide) (by decide)).congr eI⟩
  have hcap : IsCap F (x 2) :=
    ⟨A2, B2, C2, sq, D2, E2, G2, (hF 2).2 (by decide)⟩
  exact ⟨F, hcap⟩

end Minimality

end
