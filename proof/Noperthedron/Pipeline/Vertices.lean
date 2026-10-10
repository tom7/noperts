module

public import Noperthedron.RationalApprox.TrigLemmas
public import Noperthedron.Vertices.Taylor
public import Mathlib.Analysis.Real.Pi.Bounds
public import Noperthedron.Septopert.C3
public import Noperthedron.Septopert.ModelData

@[expose] public section

/-!
# Exact and rational vertices of the model

The Septopert (`Noperthedron.Septopert`, data in `Septopert.ModelData`),
symmetric under C3v with the 3-fold axis along (1,1,1), so that the C3
rotations are the cyclic coordinate permutations `Septopert.c3Mat k` (exact
rational matrices). The layout is rotation-major, as for the deltoidal
hexecontahedron's axis vertices: three seeds v0, v3, v6 (`Septopert.vertexQ`
indices), and vertex `3k + s` is seed `s` rotated by `c3Mat k`. The axis
vertex v6 is fixed by C3, so it appears three times (vertices 2, 5, 8);
the other six vertices of the Septopert appear once each
(`rationalVertex_eq_vertexQ`).

`rationalVertices` is exact: `exactVertex i = toR3 (rationalVertex i)`
(`exactVertex_eq`). `C5Model` (the name is historical) is any polyhedron with
exact C3 symmetry within `modelErrorQ` of the rational model; the
certificates cover all of them, the Septopert itself at distance 0. Vertices
lie inside the unit sphere (the GoodPoly invariant).
-/

namespace Noperthedron.Pipeline

open Noperthedron.Septopert (c3Mat c3SO3)

abbrev VertexIndex := Fin 9
abbrev SeedIndex := Fin 3
abbrev OrbitIndex := Fin 3

def rationalVertices : VertexIndex → Fin 3 → ℚ := ![
  ![-470319/524288, 327651/1048576, 327651/1048576],
  ![21999/32768, 11947/262144, 11947/262144],
  ![-514207/1048576, -514207/1048576, -514207/1048576],
  ![327651/1048576, 327651/1048576, -470319/524288],
  ![11947/262144, 11947/262144, 21999/32768],
  ![-514207/1048576, -514207/1048576, -514207/1048576],
  ![327651/1048576, -470319/524288, 327651/1048576],
  ![11947/262144, 21999/32768, 11947/262144],
  ![-514207/1048576, -514207/1048576, -514207/1048576]
]

/-! ### Fast evaluation in compiled code

`rationalVertices` is a `![…]` literal of big rationals. In compiled code each
access walks the `Fin.cons` chain and re-normalizes the rational literal (a
GMP gcd on ~260-bit numbers for the planarized vertices), and the native
certificate checkers access vertices tens of thousands of times per row. The
`@[csimp]` lemma below makes compiled code read a table of rationals computed
once at initialization instead. It is a proved equality, so it changes speed
only, not what is checked. (The table must hold data, not functions: the
compiler eta-expands function-valued definitions, so a table of closures
would still recompute on every access.) -/

/-- The coordinates of `rationalVertices`, computed once. -/
def rationalVerticesTable : Array (Array ℚ) :=
  Array.ofFn fun i : VertexIndex => Array.ofFn fun c : Fin 3 => rationalVertices i c

def rationalVerticesImpl (i : VertexIndex) (c : Fin 3) : ℚ :=
  (rationalVerticesTable[i.val]'(by simp [rationalVerticesTable]))[c.val]'(by
    simp [rationalVerticesTable])

@[csimp] theorem rationalVertices_eq_impl : @rationalVertices = @rationalVerticesImpl := by
  funext i c
  simp [rationalVerticesImpl, rationalVerticesTable]

abbrev stlVertices := rationalVertices

def rationalVertex (i : VertexIndex) : Fin 3 → ℚ := rationalVertices i

def seedVertex : SeedIndex → Fin 3 → ℚ := ![
  ![-470319/524288, 327651/1048576, 327651/1048576],
  ![21999/32768, 11947/262144, 11947/262144],
  ![-514207/1048576, -514207/1048576, -514207/1048576]
]

def orbitIndex (i : VertexIndex) : OrbitIndex :=
  ⟨i.val / 3, by omega⟩

def seedIndex (i : VertexIndex) : SeedIndex :=
  ⟨i.val % 3, Nat.mod_lt _ (by omega)⟩

/-- The vertex ordering is rotation-major: three seeds for each of three orbits. -/
def indexEquiv : VertexIndex ≃ OrbitIndex × SeedIndex where
  toFun i := (orbitIndex i, seedIndex i)
  invFun ks := ⟨3 * ks.1.val + ks.2.val, by omega⟩
  left_inv i := by
    apply Fin.ext
    simp [orbitIndex, seedIndex]
    omega
  right_inv ks := by
    rcases ks with ⟨k, s⟩
    apply Prod.ext <;> apply Fin.ext <;> simp [orbitIndex, seedIndex] <;> omega

def vertexIndex (k : OrbitIndex) (s : SeedIndex) : VertexIndex :=
  indexEquiv.symm (k, s)

@[simp] theorem orbitIndex_vertexIndex (k : OrbitIndex) (s : SeedIndex) :
    orbitIndex (vertexIndex k s) = k := by
  exact congrArg Prod.fst (indexEquiv.apply_symm_apply (k, s))

@[simp] theorem seedIndex_vertexIndex (k : OrbitIndex) (s : SeedIndex) :
    seedIndex (vertexIndex k s) = s := by
  exact congrArg Prod.snd (indexEquiv.apply_symm_apply (k, s))

/-- The `Septopert.vertexQ` index of each seed: v0, v3, v6. -/
def seedVertexQIndex : SeedIndex → Fin 7 := ![0, 3, 6]

/-- The `Septopert.vertexQ` index of vertex `i`: its seed moved by `c3Perm`. -/
def vertexQIndex (i : VertexIndex) : Fin 7 :=
  Septopert.c3Perm (orbitIndex i) (seedVertexQIndex (seedIndex i))

theorem seedVertex_eq_vertexQ (s : SeedIndex) :
    seedVertex s = Septopert.vertexQ (seedVertexQIndex s) := by
  revert s; decide +kernel

/-- The rational vertices are the Septopert's vertices (v6 three times). -/
theorem rationalVertex_eq_vertexQ (i : VertexIndex) :
    rationalVertex i = Septopert.vertexQ (vertexQIndex i) := by
  revert i; decide +kernel

/-- Every vertex of the Septopert is a model vertex. -/
theorem vertexQIndex_surjective : Function.Surjective vertexQIndex := by
  intro a
  fin_cases a
  exacts [⟨0, rfl⟩, ⟨6, rfl⟩, ⟨3, rfl⟩, ⟨1, rfl⟩, ⟨7, rfl⟩, ⟨4, rfl⟩, ⟨2, rfl⟩]

/-- The exact C3 action maps each seed to its model vertex. -/
theorem c3Mat_seedVertex (i : VertexIndex) :
    (c3Mat (orbitIndex i)).toEuclideanLin (toR3 (seedVertex (seedIndex i))) =
      toR3 (rationalVertex i) := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [orbitIndex, seedIndex, c3Mat, seedVertex, rationalVertex, rationalVertices, toR3,
      Matrix.toLpLin_apply, dotProduct, Fin.sum_univ_three]

def rationalPolyhedron : Polyhedron VertexIndex (Fin 3 → ℚ) :=
  ⟨rationalVertex⟩

/-- Seed `seedIndex i` moved by the exact rotation `c3Mat (orbitIndex i)`. -/
noncomputable def exactVertex (i : VertexIndex) : ℝ³ :=
  (c3Mat (orbitIndex i)).toEuclideanLin (toR3 (seedVertex (seedIndex i)))

/-- The rational model is exact. -/
theorem exactVertex_eq (i : VertexIndex) : exactVertex i = toR3 (rationalVertex i) :=
  c3Mat_seedVertex i

noncomputable def exactPolyhedron : Polyhedron VertexIndex ℝ³ :=
  ⟨exactVertex⟩

noncomputable def exactVerts : Finset ℝ³ :=
  Finset.image exactVertex Finset.univ

theorem exactPolyhedron_hull :
    exactPolyhedron.hull = convexHull ℝ exactVerts := by
  simp only [Polyhedron.hull, exactPolyhedron, exactVerts, Finset.coe_image,
    Finset.coe_univ, Set.image_univ]
  congr 1

@[simp] theorem exactPolyhedron_vertex (i : VertexIndex) :
    exactPolyhedron.v i = exactVertex i := rfl

/-- Every rational vertex has norm in `[1/10, 1 - 10⁻¹²]`. -/
theorem rationalVertex_sq_norm_bounds : ∀ i : VertexIndex,
    (1 / 100 : ℚ) ≤ rationalVertex i 0 ^ 2 + rationalVertex i 1 ^ 2 + rationalVertex i 2 ^ 2 ∧
      rationalVertex i 0 ^ 2 + rationalVertex i 1 ^ 2 + rationalVertex i 2 ^ 2 ≤
        (1 - 1 / 10^12) ^ 2 := by
  decide +kernel

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

theorem exactVertex_norm_pos (i : VertexIndex) : 0 < ‖exactVertex i‖ := by
  rw [exactVertex_eq]
  have := (norm_toR3_rationalVertex i).1
  linarith

theorem exactVertex_norm_le_one (i : VertexIndex) : ‖exactVertex i‖ ≤ 1 := by
  rw [exactVertex_eq]
  have := (norm_toR3_rationalVertex i).2
  linarith

noncomputable def exactGoodPoly : GoodPoly VertexIndex where
  vertices := exactPolyhedron
  nontriv := exactVertex_norm_pos
  vertex_radius_le_one := exactVertex_norm_le_one

/-! ### C3-symmetric models near the rational vertices

The certificates are checked against `rationalVertex`. What they need from
the real polyhedron is only exact C3 symmetry about (1,1,1) and a per-vertex
distance bound, so they cover every `C5Model` below (the name is kept from
the fivefold pipeline), not just `exactVertex`. -/

/-- The per-vertex distance the certificates allow between a model vertex and
`rationalVertex` (`TightApproximation.tightVertexErrorQ` has this value): 0,
since the rational model is the solid itself (the C++ checker's `MODEL_EXACT`:
zero support error, so exact support ties are allowed). -/
def modelErrorQ : ℚ := 0

/-- A polyhedron with exact C3 symmetry about (1,1,1), near the rational
model: vertex `i` is seed `seedIndex i` moved by `c3Mat (orbitIndex i)`, and
each vertex is within `modelErrorQ` of `rationalVertex i`. -/
structure C5Model where
  seed : SeedIndex → ℝ³
  close : ∀ i : VertexIndex,
    ‖(c3Mat (orbitIndex i)).toEuclideanLin (seed (seedIndex i)) -
      toR3 (rationalVertex i)‖ ≤ (modelErrorQ : ℝ)

namespace C5Model

variable (P : C5Model)

/-- Vertex `i`: seed `seedIndex i` moved by `c3Mat (orbitIndex i)`. -/
noncomputable def vertex (i : VertexIndex) : ℝ³ :=
  (c3Mat (orbitIndex i)).toEuclideanLin (P.seed (seedIndex i))

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
  rw [show ((modelErrorQ : ℚ) : ℝ) = 0 by norm_num [modelErrorQ]] at hc
  linarith

theorem vertex_norm_le_one (i : VertexIndex) : ‖P.vertex i‖ ≤ 1 := by
  have h := norm_le_norm_add_norm_sub' (P.vertex i) (toR3 (rationalVertex i))
  have hc := P.vertex_close_model i
  have hr := (norm_toR3_rationalVertex i).2
  rw [show ((modelErrorQ : ℚ) : ℝ) = 0 by norm_num [modelErrorQ]] at hc
  linarith

noncomputable def goodPoly : GoodPoly VertexIndex where
  vertices := P.polyhedron
  nontriv := P.vertex_norm_pos
  vertex_radius_le_one := P.vertex_norm_le_one

end C5Model

end Noperthedron.Pipeline

end
