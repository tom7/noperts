module

public import SnubDodecahedron.RationalVertices
public import RationalApprox.TrigLemmas
public import Basic
public import Bounding
public import PointSym

@[expose] public section

/-!
# Exact and rational vertices of the model

The snub dodecahedron, in a frame where z is a 5-fold axis: its 60 vertices
rotate 12 seed vertices about z in steps of 2π/5 (vertex 12k + s is seed s
rotated by 2πk/5). `rationalVertices` (in `RationalVertices`) is the
certified rational model. `exactVertex` rotates the rational seeds exactly. `C5Model` (below) is any fivefold-symmetric polyhedron within
`modelErrorQ` of the rational model; `IModel` (IcoModel.lean) adds the full
icosahedral symmetry, and the certificates cover all of them. Vertices are
scaled to lie inside the unit sphere (the GoodPoly invariant).
-/

namespace SnubDodecahedron

/-- Rational approximation of π, matching Mathlib's `pi_gt_d20` bound. -/
def piQ : ℚ := 3.14159265358979323846

def orbitIndex (i : VertexIndex) : OrbitIndex :=
  ⟨i.val / 12, by omega⟩

def seedIndex (i : VertexIndex) : SeedIndex :=
  ⟨i.val % 12, Nat.mod_lt _ (by omega)⟩

/-- The vertex ordering is rotation-major: 12 seeds for each of five orbits. -/
def indexEquiv : VertexIndex ≃ OrbitIndex × SeedIndex where
  toFun i := (orbitIndex i, seedIndex i)
  invFun ks := ⟨12 * ks.1.val + ks.2.val, by omega⟩
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

/-- A rational trigonometric approximation to the intended exact orbit vertex.
Angles in the second half of the orbit are reduced modulo `2π`, keeping their
absolute values below `π`. -/
def taylorVertex (i : VertexIndex) : Fin 3 → ℚ :=
  let k := orbitIndex i
  let k' : ℚ := if k.val ≤ 2 then k.val else k.val - 5
  let θ : ℚ := 2 * piQ * k' / 5
  let c := RationalApprox.cosℚ θ
  let s := RationalApprox.sinℚ θ
  let v := seedVertex (seedIndex i)
  ![c * v 0 - s * v 1, s * v 0 + c * v 1, v 2]

def rationalPolyhedron : Polyhedron VertexIndex (Fin 3 → ℚ) :=
  ⟨rationalVertex⟩

noncomputable def exactVertex (i : VertexIndex) : ℝ³ :=
  RzL (2 * Real.pi * (orbitIndex i : ℝ) / 5) (toR3 (seedVertex (seedIndex i)))

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

theorem exactVertex_norm_pos (i : VertexIndex) : 0 < ‖exactVertex i‖ := by
  rw [exactVertex, Bounding.Rz_preserves_norm, norm_pos_iff]
  intro h
  have hcoord := congrFun (congrArg WithLp.ofLp h) (2 : Fin 3)
  fin_cases i <;>
    simp [seedIndex, seedVertex, toR3] at hcoord

theorem exactVertex_norm_le_one (i : VertexIndex) : ‖exactVertex i‖ ≤ 1 := by
  rw [exactVertex, Bounding.Rz_preserves_norm]
  rw [← sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three,
    Real.norm_eq_abs, sq_abs, one_pow]
  fin_cases i <;>
    simp [seedIndex, seedVertex, toR3] <;>
    norm_num

noncomputable def exactGoodPoly : GoodPoly VertexIndex where
  vertices := exactPolyhedron
  nontriv := exactVertex_norm_pos
  vertex_radius_le_one := exactVertex_norm_le_one

/-! ### Fivefold-symmetric models near the rational vertices

The certificates are checked against `rationalVertex`. What they need from
the real polyhedron is only exact fivefold symmetry about z and a per-vertex
distance bound, so they cover every `C5Model` below, not just `exactVertex`. -/

/-- The per-vertex distance the certificates allow between a model vertex and
`rationalVertex` (`TightApproximation.tightVertexErrorQ` has this value). -/
def modelErrorQ : ℚ := 6 / 10^16

/-- A polyhedron with exact fivefold symmetry about z, near the rational
model: vertex `i` is seed `seedIndex i` rotated by `2π · orbitIndex i / 5`,
and each vertex is within `modelErrorQ` of `rationalVertex i`. -/
structure C5Model where
  seed : SeedIndex → ℝ³
  close : ∀ i : VertexIndex,
    ‖RzL (2 * Real.pi * (orbitIndex i : ℝ) / 5) (seed (seedIndex i)) -
      toR3 (rationalVertex i)‖ ≤ (modelErrorQ : ℝ)

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

namespace C5Model

variable (P : C5Model)

/-- Vertex `i`: seed `seedIndex i` rotated by `2π · orbitIndex i / 5`. -/
noncomputable def vertex (i : VertexIndex) : ℝ³ :=
  RzL (2 * Real.pi * (orbitIndex i : ℝ) / 5) (P.seed (seedIndex i))

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
  norm_num [modelErrorQ] at hc
  linarith

theorem vertex_norm_le_one (i : VertexIndex) : ‖P.vertex i‖ ≤ 1 := by
  have h := norm_le_norm_add_norm_sub' (P.vertex i) (toR3 (rationalVertex i))
  have hc := P.vertex_close_model i
  have hr := (norm_toR3_rationalVertex i).2
  norm_num [modelErrorQ] at hc
  linarith

noncomputable def goodPoly : GoodPoly VertexIndex where
  vertices := P.polyhedron
  nontriv := P.vertex_norm_pos
  vertex_radius_le_one := P.vertex_norm_le_one

end C5Model

end SnubDodecahedron

end
