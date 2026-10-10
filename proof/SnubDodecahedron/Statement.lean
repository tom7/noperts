module

public import Pipeline.IcoInstance
public import Pipeline.WikipediaSnub
public import SnubDodecahedron.SolidModel
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Algebra.Polynomial

@[expose] public section

/-!
# The snub dodecahedron

Wikipedia's definition (Snub dodecahedron, Cartesian coordinates): with φ
the golden ratio and ξ ≈ 0.94315 the real zero of x³ + 2x² − φ², the 60
vertices are the images of

  p = (φ² − φ²ξ, −φ³ + φξ + 2φξ², ξ)

under repeated multiplication by M₁ (the rotation by 2π/5 about (0, 1, φ))
and M₂ (the cyclic shift of coordinates, the rotation by 2π/3 about
(1, 1, 1)). `SnubOrbit` is that set, literally; `snubDodecahedron` is the
same 60 points as a `Finset` (`mem_snubDodecahedron_iff`); both are defined in
`Pipeline.WikipediaSnub`, shared with the pentagonal hexecontahedron (the
snub's polar dual). A polyhedron is
*a* snub dodecahedron (`IsSnubDodecahedron`) when its vertices are the image
of these under a similarity: a rotation or reflection, a positive scaling
and a translation. Both mirror images are included.

The same solid is cc-lib's `SnubDodecahedron()` (polyhedra.cc), checked
numerically: its normalized vertices are a rotation of these.
-/

open Noperts Noperts.Pipeline Noperts.Pipeline.WikipediaSnub

namespace SnubDodecahedron

open IcoZ
open scoped Matrix

/-- A snub dodecahedron: the image of `snubDodecahedron` under a similarity
(an orthogonal map, possibly a reflection, a positive scaling and a
translation). -/
def IsSnubDodecahedron (V : Finset ℝ³) : Prop :=
  ∃ (c : ℝ³) (s : ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ), 0 < s ∧
    M ∈ Matrix.orthogonalGroup (Fin 3) ℝ ∧
    V = snubDodecahedron.image fun x => c + s • M.toEuclideanLin x

/-! ### The snub dodecahedron is an `IModel` -/

/-- (1 − 10⁻⁹)/|p|, rounded: the rational model is the unit-circumradius solid
scaled by 1 − 10⁻⁹. -/
def snubScale : ℚ := (snubScaleNum : ℚ) / 10 ^ 40

/-- Vertex 0 of the model: Wikipedia's p, rotated into the 5-fold frame and scaled. -/
noncomputable def snubV0 : ℝ³ := (snubScale : ℝ) • snubFrame.toEuclideanLin snubP

def vertexWiki (i : Nat) : Nat := vertexWikiIndex.getD i 0
def wikiVertex (k : Nat) : Nat := wikiVertexIndex.getD k 0

/-- Decided over K: T is a rotation, `vertexWiki` is a bijection of range 60, and
g_i T = T S_{vertexWiki i} (our vertex i is the image of Wikipedia's). -/
def bridgeCheck : Bool :=
  decide (M3.mul8 (M3.transpose snubFrameT) snubFrameT = M3.scalar 3200) &&
    (List.range 60).all fun i =>
      decide (vertexWiki i < 60) && decide (wikiVertex i < 60) &&
        decide (vertexWiki (wikiVertex i) = i) &&
        decide (M3.mul8 (icoEntry (vElem i)) snubFrameT = M3.mul8 snubFrameT (wikiEntry (vertexWiki i)))

theorem bridgeCheck_eq : bridgeCheck = true := by decide +kernel

theorem ico_mul_snubFrame {i : Nat} (hi : i < 60) :
    ico (vElem i) * snubFrame = snubFrame * wiki (vertexWiki i) := by
  have hc := bridgeCheck_eq
  simp only [bridgeCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at hc
  have h' := congrArg M3.toMatrix (hc.2 i hi).2
  rw [M3.toMatrix_mul8, M3.toMatrix_mul8] at h'
  have h8 : (icoEntry (vElem i)).toMatrix * snubFrameT.toMatrix =
      snubFrameT.toMatrix * (wikiEntry (vertexWiki i)).toMatrix := by
    have := congrArg (fun M => (1 / 8 : ℝ) • M) h'
    simp only [smul_smul] at this
    norm_num at this
    exact this
  rw [ico, snubFrame, wiki, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_smul, h8]

/-! #### A rational box around `snubV0` -/

/-- `Σ_c 8 T_rc K_c` for coefficient vectors K. -/
def frameDot (K : Fin 3 → IcoZ) (r : Fin 3) : IcoZ :=
  IcoZ.add (IcoZ.add (IcoZ.mul8 (snubFrameT.entry r 0) (K 0))
    (IcoZ.mul8 (snubFrameT.entry r 1) (K 1))) (IcoZ.mul8 (snubFrameT.entry r 2) (K 2))

theorem snubV0_eq (r : Fin 3) :
    snubV0 r = (snubScale : ℝ) / 3200 * (IcoZ.val (frameDot snubPA r) +
      IcoZ.val (frameDot snubPB r) * snubXiW + IcoZ.val (frameDot snubPC r) * snubXiW ^ 2) := by
  simp only [snubV0, snubFrame, PiLp.smul_apply, smul_eq_mul, Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.smul_apply, M3.toMatrix,
    Matrix.of_apply, frameDot, IcoZ.val_add, IcoZ.val_mul8, snubP_eq]
  simp
  ring

def xiWLoSq : ℚ := xiWLo ^ 2
def xiWHiSq : ℚ := xiWHi ^ 2

def snubBox : RatBox where
  lo r := snubScale / 3200 * (IcoZ.lo (frameDot snubPA r) +
    mulLo (IcoZ.lo (frameDot snubPB r)) (IcoZ.hi (frameDot snubPB r)) xiWLo xiWHi +
    mulLo (IcoZ.lo (frameDot snubPC r)) (IcoZ.hi (frameDot snubPC r)) xiWLoSq xiWHiSq)
  hi r := snubScale / 3200 * (IcoZ.hi (frameDot snubPA r) +
    mulHi (IcoZ.lo (frameDot snubPB r)) (IcoZ.hi (frameDot snubPB r)) xiWLo xiWHi +
    mulHi (IcoZ.lo (frameDot snubPC r)) (IcoZ.hi (frameDot snubPC r)) xiWLoSq xiWHiSq)

theorem snubV0_mem : snubBox.Mem snubV0 := by
  intro r
  obtain ⟨hxlo, hxhi⟩ := snubXiW_bounds
  have hxpos := snubXiW_pos
  have hxi : ((xiWLo : ℚ) : ℝ) ≤ snubXiW ∧ snubXiW ≤ ((xiWHi : ℚ) : ℝ) := ⟨hxlo, hxhi⟩
  have hxlo0 : (0 : ℝ) ≤ (xiWLo : ℝ) := by unfold xiWLo; positivity
  have hxi2 : ((xiWLoSq : ℚ) : ℝ) ≤ snubXiW ^ 2 ∧ snubXiW ^ 2 ≤ ((xiWHiSq : ℚ) : ℝ) := by
    simp only [xiWLoSq, xiWHiSq, Rat.cast_pow]
    exact ⟨pow_le_pow_left₀ hxlo0 hxlo 2, pow_le_pow_left₀ hxpos.le hxhi 2⟩
  have hencl : ∀ x : IcoZ, ((IcoZ.lo x : ℚ) : ℝ) ≤ IcoZ.val x ∧ IcoZ.val x ≤ ((IcoZ.hi x : ℚ) : ℝ) :=
    fun x => ⟨IcoZ.lo_le_val x, IcoZ.val_le_hi x⟩
  have hB := mulLo_le (hencl (frameDot snubPB r)) hxi
  have hB' := le_mulHi (hencl (frameDot snubPB r)) hxi
  have hC := mulLo_le (hencl (frameDot snubPC r)) hxi2
  have hC' := le_mulHi (hencl (frameDot snubPC r)) hxi2
  have hA := hencl (frameDot snubPA r)
  have hq : (0 : ℝ) < (snubScale : ℝ) / 3200 := by norm_num [snubScale, snubScaleNum]
  rw [snubV0_eq]
  simp only [snubBox]
  push_cast
  constructor
  · exact mul_le_mul_of_nonneg_left (by linarith [hA.1]) hq.le
  · exact mul_le_mul_of_nonneg_left (by linarith [hA.2]) hq.le

theorem snubBox_close : closeCheck (fun _ => snubBox) = true := by decide +kernel

/-- The base point's stabilizer is trivial (`OrbitData`). -/
theorem snubV0_fixed (o : IOrbitIndex) : ∀ h ∈ icoStab o.val,
    (ico h).toEuclideanLin snubV0 = snubV0 := by
  have hstab : ∀ o : IOrbitIndex, icoStab o.val = [0] := by decide
  intro h hh
  rw [hstab o, List.mem_singleton] at hh
  subst hh
  simp

/-- The snub dodecahedron (scaled and rotated into the 5-fold frame) as an `IModel`. -/
noncomputable def snubIModel : IModel :=
  IModel.ofBoxes (fun _ => snubBox) snubBox_close (fun _ => snubV0) (fun _ => snubV0_mem)
    snubV0_fixed

theorem snubIModel_verts :
    snubIModel.toC5.verts =
      snubDodecahedron.image fun x => (0 : ℝ³) + (snubScale : ℝ) • snubFrame.toEuclideanLin x := by
  have hc := bridgeCheck_eq
  simp only [bridgeCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at hc
  have hvert : ∀ i : VertexIndex, snubIModel.toC5.vertex i =
      (snubScale : ℝ) • snubFrame.toEuclideanLin ((wiki (vertexWiki i.val)).toEuclideanLin snubP) := by
    intro i
    rw [IModel.toC5_vertex, IModel.orbit]
    change (ico (vElem i.val)).toEuclideanLin snubV0 = _
    rw [snubV0, map_smul, ← IModel.toEuclideanLin_mul, ico_mul_snubFrame i.isLt,
      IModel.toEuclideanLin_mul]
  ext v
  simp only [CyclicModel.verts, snubDodecahedron, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_range, zero_add]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨_, ⟨vertexWiki i.val, ((hc.2 i.val i.isLt).1.1.1), rfl⟩, (hvert i).symm⟩
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    obtain ⟨⟨⟨-, hlt⟩, hinv⟩, -⟩ := hc.2 g hg
    refine ⟨⟨wikiVertex g, hlt⟩, ?_⟩
    rw [hvert]
    simp only [hinv]

/-! ### Main theorem -/

/-- If no `IModel` is Rupert (what `constructSnubDodecahedron` checks), then no snub
dodecahedron is Rupert. -/
theorem snubDodecahedron_not_rupert (h : ∀ P : IModel, ¬ IsRupert P.toC5.verts) :
    ∀ V : Finset ℝ³, IsSnubDodecahedron V → ¬ IsRupert V := by
  have hsnub : ¬ IsRupert snubDodecahedron := by
    intro hr
    have hq : (0 : ℝ) < (snubScale : ℝ) := by norm_num [snubScale, snubScaleNum]
    have := isRupert_image_similarity 0 _ hq snubFrame snubFrame_orthogonal _ hr
    rw [← snubIModel_verts] at this
    exact h snubIModel this
  rintro V ⟨c, s, M, hs, hM, rfl⟩ hV
  apply hsnub
  -- Undo the similarity: x ↦ s⁻¹ Mᵀ (x − c).
  have hMt : Mᵀ ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
    rw [Matrix.mem_orthogonalGroup_iff']
    simpa using (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mp hM
  have hMM : Mᵀ * M = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hM
  have := isRupert_image_similarity (-(s⁻¹ • Mᵀ.toEuclideanLin c)) s⁻¹ (inv_pos.mpr hs) Mᵀ hMt _ hV
  convert this using 1
  rw [Finset.image_image]
  conv_lhs => rw [← Finset.image_id (s := snubDodecahedron)]
  congr 1
  funext x
  simp only [Function.comp, id, map_add, map_smul, smul_add, smul_smul, inv_mul_cancel₀ hs.ne',
    one_smul]
  rw [← IModel.toEuclideanLin_mul, hMM]
  simp

/-- Wikipedia's vertices are themselves a snub dodecahedron (the identity
similarity). -/
theorem isSnubDodecahedron_snubDodecahedron : IsSnubDodecahedron snubDodecahedron := by
  refine ⟨0, 1, 1, one_pos, Submonoid.one_mem _, ?_⟩
  ext v
  simp

/-- **Main theorem.** The snub dodecahedron (Wikipedia's vertices) is not
Rupert, given that no `IModel` is (what `constructSnubDodecahedron` checks). -/
theorem wikipediaSnubDodecahedron_not_rupert (h : ∀ P : IModel, ¬ IsRupert P.toC5.verts) :
    ¬ IsRupert snubDodecahedron :=
  snubDodecahedron_not_rupert h _ isSnubDodecahedron_snubDodecahedron

end SnubDodecahedron
