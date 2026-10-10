module

public import RationalApprox.TrigLemmas
public import Basic
public import Bounding
public import PointSym
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Data.Erased

@[expose] public section

/-!
# The solid model: what the certificate pipeline needs to know about a solid

The certificate pipeline (the `Atlas*` modules of `Pipeline/`) is shared by
every solid. It sees a solid only through a `SolidModel` instance:

* a rational vertex table `rationalVertices`, laid out rotation-major: there
  are `orbitCount` rotations and `seedCount` seed vertices, and vertex
  `seedCount * k + s` is (approximately) seed `s` moved by rotation `k`. The
  layout lets the certificates use a cyclic symmetry of the solid without
  knowing anything else about it;
* the exact cyclic symmetry `symmetryMatrix k` (a rotation, with
  `symmetryMatrix a * symmetryMatrix b = symmetryMatrix (a + b)`), and a
  rational stand-in `symmetryMatrixQ k` within `symmetryErrorQ` of it in
  operator norm;
* `modelErrorQ`: how far the rotated seeds may be from the rational vertices.

The Septopert's symmetry is C3 about (1,1,1), exact over ℚ (the cyclic
coordinate permutations), so both errors are 0. The icosahedral solids
(deltoidal and pentagonal hexecontahedra, snub dodecahedron) use C5 about the
z axis: `symmetryMatrixQ` holds rational Taylor values of cos and sin of
`2πk/5`, and the published coordinates are within `6 · 10⁻¹⁶` of the rotated
seeds.

The certificates are checked against `rationalVertex`, and they cover every
`CyclicModel` (below): every polyhedron whose vertex `i` is seed `seedIndex i`,
moved by `symmetryMatrix (orbitIndex i)`, within `modelErrorQ` of
`rationalVertex i`. (It was called `C5Model` before the pipeline was made
generic; the symmetry is whatever cyclic group the solid's model provides.)

Each solid provides its instance as a `scoped instance` in its own namespace,
so that no instance is in scope merely by importing a solid, and the solid's
own statements (`CertificatesValid` and the headline theorems) name its
model explicitly. The pipeline's definitions take the model as an instance
argument; the compiler specializes them to the concrete model in each
solid's checker (instance arguments are specialized by default), so the hot
loops read the solid's vertex table directly.

The exact symmetry is real-valued and noncomputable; it is stored as an
`Erased` value, so that the instance (which compiled code uses for its data
fields) stays computable.
-/

namespace Noperts.Pipeline

open scoped Matrix

/-- What the certificate pipeline needs to know about a solid. See the module
documentation. -/
class SolidModel where
  /-- The order of the cyclic symmetry used by the vertex layout. -/
  orbitCount : ℕ
  /-- The number of seed vertices (vertices per symmetry orbit). -/
  seedCount : ℕ
  orbitCount_pos : 0 < orbitCount
  seedCount_pos : 0 < seedCount
  /-- The certified rational model; vertex `seedCount * k + s` is seed `s`
  moved by rotation `k`. -/
  rationalVertices : Fin (orbitCount * seedCount) → Fin 3 → ℚ
  /-- The seed vertices. -/
  seedVertex : Fin seedCount → Fin 3 → ℚ
  /-- The exact rotations of the cyclic symmetry (erased in compiled code). -/
  symmetryMatrixErased : Erased (Fin orbitCount → Matrix (Fin 3) (Fin 3) ℝ)
  /-- Rational stand-ins for the rotations, used by the local certificates. -/
  symmetryMatrixQ : Fin orbitCount → Matrix (Fin 3) (Fin 3) ℚ
  /-- An operator-norm bound on `symmetryMatrix k - symmetryMatrixQ k`. -/
  symmetryErrorQ : ℚ
  /-- How far the rotated seeds may be from the rational vertices. -/
  modelErrorQ : ℚ
  /-- The model vertex index (slot) of a vertex number in the C++ checker's
  packed certificates. -/
  vertexSlot : ℕ → Fin (orbitCount * seedCount)
  symmetry_mem : ∀ k, symmetryMatrixErased.out k ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ
  symmetry_mul : ∀ a b,
    symmetryMatrixErased.out a * symmetryMatrixErased.out b = symmetryMatrixErased.out (a + b)
  symmetry_zero : symmetryMatrixErased.out ⟨0, orbitCount_pos⟩ = 1
  symmetryQ_close : ∀ k,
    ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
        (symmetryMatrixErased.out k - (symmetryMatrixQ k).map fun x => (x : ℝ)))‖ ≤
      (symmetryErrorQ : ℝ)
  /-- The rational vertices are within `modelErrorQ` of the rotated seeds. -/
  seed_close : ∀ i : Fin (orbitCount * seedCount),
    ‖(symmetryMatrixErased.out ⟨i.val / seedCount, Nat.div_lt_of_lt_mul (Nat.mul_comm orbitCount seedCount ▸ i.isLt)⟩).toEuclideanLin
        (toR3 (seedVertex ⟨i.val % seedCount, Nat.mod_lt _ seedCount_pos⟩)) -
      toR3 (rationalVertices i)‖ ≤ (modelErrorQ : ℝ)
  modelErrorQ_nonneg : 0 ≤ modelErrorQ
  modelErrorQ_le : modelErrorQ ≤ 1 / 10 ^ 12
  /-- Every rational vertex has norm in `[1/10, 1 - 10⁻¹²]` (checked by the
  kernel on the solid's data). -/
  rationalVertex_sq_norm_bounds : ∀ i : Fin (orbitCount * seedCount),
    (1 / 100 : ℚ) ≤ rationalVertices i 0 ^ 2 + rationalVertices i 1 ^ 2 + rationalVertices i 2 ^ 2 ∧
      rationalVertices i 0 ^ 2 + rationalVertices i 1 ^ 2 + rationalVertices i 2 ^ 2 ≤
        (1 - 1 / 10^12) ^ 2

variable [SolidModel]

instance : NeZero SolidModel.orbitCount := ⟨Nat.pos_iff_ne_zero.mp SolidModel.orbitCount_pos⟩
instance : NeZero SolidModel.seedCount := ⟨Nat.pos_iff_ne_zero.mp SolidModel.seedCount_pos⟩

abbrev VertexIndex := Fin (SolidModel.orbitCount * SolidModel.seedCount)
abbrev SeedIndex := Fin SolidModel.seedCount
abbrev OrbitIndex := Fin SolidModel.orbitCount

instance : NeZero (SolidModel.orbitCount * SolidModel.seedCount) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos SolidModel.orbitCount_pos SolidModel.seedCount_pos)⟩

def rationalVertex (i : VertexIndex) : Fin 3 → ℚ := SolidModel.rationalVertices i

def seedVertex (s : SeedIndex) : Fin 3 → ℚ := SolidModel.seedVertex s

def modelErrorQ : ℚ := SolidModel.modelErrorQ

/-- The exact rotation `k` of the solid's cyclic symmetry. -/
noncomputable def symmetryMatrix (k : OrbitIndex) : Matrix (Fin 3) (Fin 3) ℝ :=
  SolidModel.symmetryMatrixErased.out k

theorem symmetryMatrix_mem (k : OrbitIndex) :
    symmetryMatrix k ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  SolidModel.symmetry_mem k

theorem symmetryMatrix_mul (a b : OrbitIndex) :
    symmetryMatrix a * symmetryMatrix b = symmetryMatrix (a + b) :=
  SolidModel.symmetry_mul a b

@[simp] theorem symmetryMatrix_zero : symmetryMatrix 0 = 1 :=
  SolidModel.symmetry_zero

def orbitIndex (i : VertexIndex) : OrbitIndex :=
  ⟨i.val / SolidModel.seedCount,
    Nat.div_lt_of_lt_mul (Nat.mul_comm SolidModel.orbitCount SolidModel.seedCount ▸ i.isLt)⟩

def seedIndex (i : VertexIndex) : SeedIndex :=
  ⟨i.val % SolidModel.seedCount, Nat.mod_lt _ SolidModel.seedCount_pos⟩

/-- The vertex ordering is rotation-major: `seedCount` seeds for each orbit. -/
def indexEquiv : VertexIndex ≃ OrbitIndex × SeedIndex where
  toFun i := (orbitIndex i, seedIndex i)
  invFun ks := ⟨SolidModel.seedCount * ks.1.val + ks.2.val, by
    have h1 := ks.1.isLt
    have h2 := ks.2.isLt
    calc SolidModel.seedCount * ks.1.val + ks.2.val
        < SolidModel.seedCount * ks.1.val + SolidModel.seedCount := by omega
      _ = SolidModel.seedCount * (ks.1.val + 1) := by ring
      _ ≤ SolidModel.seedCount * SolidModel.orbitCount := Nat.mul_le_mul_left _ h1
      _ = _ := Nat.mul_comm _ _⟩
  left_inv i := by
    apply Fin.ext
    simp only [orbitIndex, seedIndex]
    exact Nat.div_add_mod i.val SolidModel.seedCount
  right_inv ks := by
    rcases ks with ⟨k, s⟩
    have hs := s.isLt
    have hpos := SolidModel.seedCount_pos
    apply Prod.ext <;> apply Fin.ext
    · simp only [orbitIndex]
      rw [Nat.mul_add_div hpos, Nat.div_eq_of_lt hs, Nat.add_zero]
    · simp only [seedIndex]
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hs]

def vertexIndex (k : OrbitIndex) (s : SeedIndex) : VertexIndex :=
  indexEquiv.symm (k, s)

@[simp] theorem orbitIndex_vertexIndex (k : OrbitIndex) (s : SeedIndex) :
    orbitIndex (vertexIndex k s) = k := by
  exact congrArg Prod.fst (indexEquiv.apply_symm_apply (k, s))

@[simp] theorem seedIndex_vertexIndex (k : OrbitIndex) (s : SeedIndex) :
    seedIndex (vertexIndex k s) = s := by
  exact congrArg Prod.snd (indexEquiv.apply_symm_apply (k, s))

def rationalPolyhedron : Polyhedron VertexIndex (Fin 3 → ℚ) :=
  ⟨rationalVertex⟩

theorem rationalVertex_sq_norm_bounds : ∀ i : VertexIndex,
    (1 / 100 : ℚ) ≤ rationalVertex i 0 ^ 2 + rationalVertex i 1 ^ 2 + rationalVertex i 2 ^ 2 ∧
      rationalVertex i 0 ^ 2 + rationalVertex i 1 ^ 2 + rationalVertex i 2 ^ 2 ≤
        (1 - 1 / 10^12) ^ 2 :=
  SolidModel.rationalVertex_sq_norm_bounds

theorem norm_toR3_rationalVertex (i : VertexIndex) :
    1 / 10 ≤ ‖toR3 (rationalVertex i)‖ ∧ ‖toR3 (rationalVertex i)‖ ≤ 1 - 1 / 10^12 := by
  obtain ⟨hlo, hhi⟩ := rationalVertex_sq_norm_bounds i
  set q : ℚ := rationalVertex i 0 ^ 2 + rationalVertex i 1 ^ 2 + rationalVertex i 2 ^ 2
  have hsq : ‖toR3 (rationalVertex i)‖ ^ 2 = (q : ℝ) := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, toR3, q]
    push_cast
    ring
  have hlo' : (((1 / 100 : ℚ)) : ℝ) ≤ (q : ℝ) := Rat.cast_le.mpr hlo
  have hhi' : (q : ℝ) ≤ (((1 - 1 / 10^12) ^ 2 : ℚ) : ℝ) := Rat.cast_le.mpr hhi
  push_cast at hlo' hhi'
  have hn := norm_nonneg (toR3 (rationalVertex i))
  constructor <;> nlinarith

theorem modelErrorQ_nonneg : 0 ≤ modelErrorQ := SolidModel.modelErrorQ_nonneg

theorem modelErrorQ_le : modelErrorQ ≤ 1 / 10 ^ 12 := SolidModel.modelErrorQ_le

theorem modelErrorQ_real_le : (modelErrorQ : ℝ) ≤ 1 / 10 ^ 12 := by
  have h := (Rat.cast_le (K := ℝ)).mpr modelErrorQ_le
  push_cast at h
  exact h

/-! ### Models near the rational vertices

The certificates are checked against `rationalVertex`. What they need from
the real polyhedron is only the exact cyclic symmetry and a per-vertex
distance bound, so they cover every `CyclicModel` below, not just the rotated
rational seeds (`exactModel`). -/

/-- A polyhedron with the solid's exact cyclic symmetry, near the rational
model: vertex `i` is seed `seedIndex i` moved by
`symmetryMatrix (orbitIndex i)`, and each vertex is within `modelErrorQ` of
`rationalVertex i`. -/
structure CyclicModel where
  seed : SeedIndex → ℝ³
  close : ∀ i : VertexIndex,
    ‖(symmetryMatrix (orbitIndex i)).toEuclideanLin (seed (seedIndex i)) -
      toR3 (rationalVertex i)‖ ≤ (modelErrorQ : ℝ)

namespace CyclicModel

variable (P : CyclicModel)

/-- Vertex `i`: seed `seedIndex i` moved by `symmetryMatrix (orbitIndex i)`. -/
noncomputable def vertex (i : VertexIndex) : ℝ³ :=
  (symmetryMatrix (orbitIndex i)).toEuclideanLin (P.seed (seedIndex i))

noncomputable def polyhedron : Polyhedron VertexIndex ℝ³ :=
  ⟨P.vertex⟩

noncomputable def verts : Finset ℝ³ :=
  Finset.image P.vertex Finset.univ

theorem polyhedron_hull : P.polyhedron.hull = convexHull ℝ P.verts := by
  simp only [Polyhedron.hull, polyhedron, verts, Finset.coe_image,
    Finset.coe_univ, Set.image_univ]
  congr 1

@[simp] theorem polyhedron_vertex (i : VertexIndex) : P.polyhedron.v i = P.vertex i := rfl

theorem vertex_close_model (i : VertexIndex) :
    ‖P.vertex i - toR3 (rationalVertex i)‖ ≤ (modelErrorQ : ℝ) :=
  P.close i

theorem vertex_norm_pos (i : VertexIndex) : 0 < ‖P.vertex i‖ := by
  have h := norm_sub_norm_le (toR3 (rationalVertex i)) (P.vertex i)
  rw [norm_sub_rev] at h
  have hc := P.vertex_close_model i
  have hr := (norm_toR3_rationalVertex i).1
  have he := modelErrorQ_real_le
  linarith

theorem vertex_norm_le_one (i : VertexIndex) : ‖P.vertex i‖ ≤ 1 := by
  have h := norm_le_norm_add_norm_sub' (P.vertex i) (toR3 (rationalVertex i))
  have hc := P.vertex_close_model i
  have hr := (norm_toR3_rationalVertex i).2
  have he := modelErrorQ_real_le
  linarith

noncomputable def goodPoly : GoodPoly VertexIndex where
  vertices := P.polyhedron
  nontriv := P.vertex_norm_pos
  vertex_radius_le_one := P.vertex_norm_le_one

end CyclicModel

/-- The rational seeds moved by the exact symmetry: the model the solid's
data describes (for the Septopert, the rational vertices themselves). -/
noncomputable def exactModel : CyclicModel where
  seed s := toR3 (seedVertex s)
  close := SolidModel.seed_close

/-- Seed `seedIndex i` moved by the exact rotation `symmetryMatrix (orbitIndex i)`. -/
noncomputable def exactVertex (i : VertexIndex) : ℝ³ :=
  (symmetryMatrix (orbitIndex i)).toEuclideanLin (toR3 (seedVertex (seedIndex i)))

theorem exactModel_vertex (i : VertexIndex) : exactModel.vertex i = exactVertex i := rfl

noncomputable def exactPolyhedron : Polyhedron VertexIndex ℝ³ :=
  ⟨exactVertex⟩

noncomputable def exactVerts : Finset ℝ³ :=
  Finset.image exactVertex Finset.univ

theorem exactModel_verts : exactModel.verts = exactVerts := rfl

theorem exactPolyhedron_hull :
    exactPolyhedron.hull = convexHull ℝ exactVerts := by
  simp only [Polyhedron.hull, exactPolyhedron, exactVerts, Finset.coe_image,
    Finset.coe_univ, Set.image_univ]
  congr 1

@[simp] theorem exactPolyhedron_vertex (i : VertexIndex) :
    exactPolyhedron.v i = exactVertex i := rfl

theorem exactVertex_norm_pos (i : VertexIndex) : 0 < ‖exactVertex i‖ :=
  exactModel.vertex_norm_pos i

theorem exactVertex_norm_le_one (i : VertexIndex) : ‖exactVertex i‖ ≤ 1 :=
  exactModel.vertex_norm_le_one i

noncomputable def exactGoodPoly : GoodPoly VertexIndex where
  vertices := exactPolyhedron
  nontriv := exactVertex_norm_pos
  vertex_radius_le_one := exactVertex_norm_le_one

end Noperts.Pipeline

end
