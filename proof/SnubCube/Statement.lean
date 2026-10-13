module

public import SnubCube.Caps
public import Pipeline.IcoInstance
public import Pipeline.Similarity

@[expose] public section

/-!
# The snub cube

Wikipedia's definition (Snub cube, Cartesian coordinates): with t ≈ 1.83929
the tribonacci constant (the real root of t³ = t² + t + 1, `tribonacci`), the
24 vertices are the even permutations of (±1, ±1/t, ±t) with an even number
of plus signs, together with the odd permutations with an odd number of plus
signs. `snubCube` is that set, literally: coordinate i of the point for a
permutation σ and signs s is s_i · (1, 1/t, t)_{σ(i)}, kept when σ is even
exactly when the number of plus signs is even. A polyhedron is *a* snub cube
(`IsSnubCube`) when its vertices are the image of these under a similarity: an
orthogonal map (possibly a reflection), a positive scaling and a translation.
Both mirror images are included.

The model (`SnubCube.SolidModel`) is the O-orbit of (t, 1, −t²) scaled to
circumradius 1 − 10⁻⁹: `snubOModel` is the exact solid as an `OModel` (its
base point snubScale · (t, 1, −t²) is within 6·10⁻¹⁶ of the rational base
point: kernel checked), and its vertices are `snubCube` scaled by
snubScale · t (`snubOModel_verts`), since (t, 1, −t²) = t · (1, 1/t, −t) and O
moves (1, 1/t, −t) exactly onto Wikipedia's 24 points (`slotWiki`, decided).
-/

open Noperts Noperts.Pipeline Noperts.Pipeline.KCap Noperts.Pipeline.KCap.PVec

namespace SnubCube

open scoped Matrix Pointwise

/-! ### Wikipedia's snub cube -/

/-- (1, 1/t, t). -/
noncomputable def wikiBase : Fin 3 → ℝ := ![1, 1 / tribonacci, tribonacci]

/-- The number of plus signs. -/
def plusCount (s : Fin 3 → Bool) : ℕ := (Finset.univ.filter fun i => s i = true).card

/-- The permutations and signs of Wikipedia's points: σ even exactly when the number of plus
signs is even. -/
def wikiIndex : Finset (Equiv.Perm (Fin 3) × (Fin 3 → Bool)) :=
  Finset.univ.filter fun ps => (Equiv.Perm.sign ps.1 = 1 ↔ Even (plusCount ps.2))

/-- The point of a permutation σ and signs s: coordinate i is s_i · (1, 1/t, t)_{σ(i)}. -/
noncomputable def wikiPoint (ps : Equiv.Perm (Fin 3) × (Fin 3 → Bool)) : ℝ³ :=
  WithLp.toLp 2 fun i => (if ps.2 i then 1 else -1) * wikiBase (ps.1 i)

/-- Wikipedia's snub cube. -/
noncomputable def snubCube : Finset ℝ³ := wikiIndex.image wikiPoint

/-- A snub cube: the image of `snubCube` under a similarity (an orthogonal map, possibly a
reflection, a positive scaling and a translation). -/
def IsSnubCube (V : Finset ℝ³) : Prop :=
  ∃ (c : ℝ³) (s : ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ), 0 < s ∧
    M ∈ Matrix.orthogonalGroup (Fin 3) ℝ ∧
    V = snubCube.image fun x => c + s • M.toEuclideanLin x

/-! ### The slots are Wikipedia's points -/

/-- Element g of O sends (b₀, b₁, −b₂) to the point of (σ, s): row r of g has its one nonzero
entry s_r · (−1 if σ(r) = 2) in column σ(r). -/
def combCheck (g : ℕ) (ps : Equiv.Perm (Fin 3) × (Fin 3 → Bool)) : Bool :=
  (List.finRange 3).all fun r => (List.finRange 3).all fun c =>
    octaEntry g (3 * r.val + c.val) ==
      (if c = ps.1 r then (if ps.2 r then 1 else -1) * (if c = 2 then -1 else 1) else 0)

theorem slots_wiki : ∀ i : Fin 24, ∃ ps ∈ wikiIndex, combCheck (slotElemData.getD i.val 0) ps = true := by
  decide +kernel

theorem wiki_slots : ∀ ps ∈ wikiIndex, ∃ i : Fin 24, combCheck (slotElemData.getD i.val 0) ps = true := by
  decide +kernel

theorem comb_apply {g : ℕ} {ps : Equiv.Perm (Fin 3) × (Fin 3 → Bool)} (h : combCheck g ps = true)
    (hg : g < 24) (b : Fin 3 → ℝ) :
    (octaMatrix ⟨g, hg⟩).toEuclideanLin (WithLp.toLp 2 ![b 0, b 1, -b 2]) =
      WithLp.toLp 2 (fun r => (if ps.2 r then 1 else -1) * b (ps.1 r)) := by
  simp only [combCheck, List.all_eq_true, List.mem_finRange, beq_iff_eq, true_implies] at h
  ext r
  simp only [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, octaMatrix,
    Matrix.of_apply, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, WithLp.ofLp_toLp]
  rw [h r 0, h r 1, h r 2]
  rcases hσ : ps.1 r with ⟨k, hk⟩
  interval_cases k <;> cases ps.2 r <;> simp [hσ] <;> ring

/-! ### The exact snub cube as an `OModel` -/

/-- A box around snubScale · (t, 1, −t²) (`tribonacci_enclosure`). -/
def v0Box : RatBox where
  lo := ![snubScale * tribLo, snubScale, -(snubScale * (tribHi * tribHi))]
  hi := ![snubScale * tribHi, snubScale, -(snubScale * (tribLo * tribLo))]

/-- The exact base point: snubScale · (t, 1, −t²). -/
noncomputable def snubV0 : ℝ³ :=
  WithLp.toLp 2 ![(snubScale : ℝ) * tribonacci, snubScale, -((snubScale : ℝ) * tribonacci ^ 2)]

theorem snubScale_pos : (0 : ℝ) < snubScale := by norm_num [snubScale, snubScaleNum]

theorem snubV0_mem : v0Box.Mem snubV0 := by
  obtain ⟨hl, hh⟩ := tribonacci_enclosure
  obtain ⟨hl2, hh2⟩ := TribQ.tribonacci_sq_enclosure
  push_cast at hl2 hh2
  have hs := snubScale_pos
  intro c
  fin_cases c <;> simp [v0Box, snubV0]
  · constructor <;> nlinarith
  · constructor <;> nlinarith

/-- Enclosure of `(g *ᵥ v) r` for v in B (g's entries are integers: exact). -/
def octaImageLo (g : ℕ) (B : RatBox) (r : Fin 3) : ℚ :=
  ∑ c : Fin 3, mulLo (octaEntry g (3 * r.val + c.val)) (octaEntry g (3 * r.val + c.val)) (B.lo c) (B.hi c)

def octaImageHi (g : ℕ) (B : RatBox) (r : Fin 3) : ℚ :=
  ∑ c : Fin 3, mulHi (octaEntry g (3 * r.val + c.val)) (octaEntry g (3 * r.val + c.val)) (B.lo c) (B.hi c)

theorem octaImage_mem (g : ℕ) (hg : g < 24) (B : RatBox) {v : ℝ³} (hv : B.Mem v) (r : Fin 3) :
    (octaImageLo g B r : ℝ) ≤ ((octaMatrix ⟨g, hg⟩).toEuclideanLin v) r ∧
      ((octaMatrix ⟨g, hg⟩).toEuclideanLin v) r ≤ (octaImageHi g B r : ℝ) := by
  have happly : ((octaMatrix ⟨g, hg⟩).toEuclideanLin v) r = ∑ c : Fin 3, (octaEntry g (3 * r.val + c.val) : ℝ) * v c := by
    simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, octaMatrix]
  have hentry : ∀ c : Fin 3, ((octaEntry g (3 * r.val + c.val) : ℚ) : ℝ) ≤ (octaEntry g (3 * r.val + c.val) : ℝ) ∧
      (octaEntry g (3 * r.val + c.val) : ℝ) ≤ ((octaEntry g (3 * r.val + c.val) : ℚ) : ℝ) := fun c => by
    push_cast; exact ⟨le_rfl, le_rfl⟩
  rw [happly]
  constructor
  · simp only [octaImageLo]
    push_cast
    exact Finset.sum_le_sum fun c _ => by
      have := mulLo_le (hentry c) (hv c)
      push_cast at this; exact this
  · simp only [octaImageHi]
    push_cast
    exact Finset.sum_le_sum fun c _ => by
      have := le_mulHi (hentry c) (hv c)
      push_cast at this; exact this

def octaCloseCheck (B : RatBox) : Bool :=
  (List.finRange 24).all fun i =>
    decide (∑ r, sqDistBound (octaImageLo (slotElemData.getD i.val 0) B r)
      (octaImageHi (slotElemData.getD i.val 0) B r) (rationalVerticesData i r) ≤ (6 / 10 ^ 16) ^ 2)

theorem octaCloseCheck_eq : octaCloseCheck v0Box = true := by decide +kernel

/-- The exact snub cube (scaled into the model's frame and size) as an `OModel`. -/
noncomputable def snubOModel : OModel where
  v0 := snubV0
  close i := by
    have hc := octaCloseCheck_eq
    simp only [octaCloseCheck, List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] at hc
    have hi := hc i
    have hg : slotElemData.getD i.val 0 < 24 := slotIdx_lt i.isLt
    set w := (octaMatrix (slotOcta i)).toEuclideanLin snubV0
    have hw : ∀ r, (octaImageLo (slotElemData.getD i.val 0) v0Box r : ℝ) ≤ w r ∧
        w r ≤ (octaImageHi (slotElemData.getD i.val 0) v0Box r : ℝ) := fun r =>
      octaImage_mem _ hg v0Box snubV0_mem r
    have hsq : ‖w - toR3 (rationalVertex i)‖ ^ 2 ≤ ((modelErrorQ : ℚ) : ℝ) ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      have hb : ∀ r, (w r - rationalVertex i r) ^ 2 ≤
          (sqDistBound (octaImageLo (slotElemData.getD i.val 0) v0Box r)
            (octaImageHi (slotElemData.getD i.val 0) v0Box r) (rationalVertex i r) : ℝ) :=
        fun r => sq_le_sqDistBound (hw r)
      have hiR : ((∑ r, sqDistBound (octaImageLo (slotElemData.getD i.val 0) v0Box r)
          (octaImageHi (slotElemData.getD i.val 0) v0Box r) (rationalVerticesData i r) : ℚ) : ℝ) ≤
          (((6 / 10 ^ 16) ^ 2 : ℚ) : ℝ) := by exact_mod_cast hi
      push_cast at hiR
      calc ∑ r, ‖(w - toR3 (rationalVertex i)) r‖ ^ 2
          = ∑ r, (w r - rationalVertex i r) ^ 2 := by
            simp [toR3, Real.norm_eq_abs, sq_abs]
        _ ≤ _ := Finset.sum_le_sum fun r _ => hb r
        _ ≤ _ := by
          have e : modelErrorQ = 6 / 10 ^ 16 := rfl
          rw [e]; push_cast; exact hiR
    have hpos : (0 : ℝ) ≤ (modelErrorQ : ℝ) := by exact_mod_cast modelErrorQ_nonneg
    exact (sq_le_sq₀ (norm_nonneg _) hpos).mp hsq

/-! ### The model's vertices are Wikipedia's, scaled -/

/-- snubScale · (t, 1, −t²) = (snubScale · t) · (1, 1/t, −t). -/
theorem snubV0_eq : snubV0 = ((snubScale : ℝ) * tribonacci) •
    WithLp.toLp 2 ![wikiBase 0, wikiBase 1, -wikiBase 2] := by
  have ht := tribonacci_pos
  ext r
  fin_cases r <;> simp [snubV0, wikiBase] <;> field_simp <;> ring

theorem snubOModel_vertex (i : VertexIndex) (ps : Equiv.Perm (Fin 3) × (Fin 3 → Bool))
    (h : combCheck (slotElemData.getD i.val 0) ps = true) :
    snubOModel.toC4.vertex i = ((snubScale : ℝ) * tribonacci) • wikiPoint ps := by
  rw [OModel.toC4_vertex, OModel.orbit]
  change (octaMatrix (slotOcta i)).toEuclideanLin snubV0 = _
  rw [snubV0_eq, map_smul]
  congr 1
  exact comb_apply h (slotIdx_lt i.isLt) wikiBase

theorem snubOModel_verts :
    snubOModel.toC4.verts = snubCube.image fun x => (0 : ℝ³) + ((snubScale : ℝ) * tribonacci) • x := by
  ext v
  simp only [CyclicModel.verts, snubCube, Finset.mem_image, Finset.mem_univ, true_and, zero_add]
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨ps, hps, hc⟩ := slots_wiki i
    exact ⟨_, ⟨ps, hps, rfl⟩, (snubOModel_vertex i ps hc).symm⟩
  · rintro ⟨_, ⟨ps, hps, rfl⟩, rfl⟩
    obtain ⟨i, hi⟩ := wiki_slots ps hps
    exact ⟨i, snubOModel_vertex i ps hi⟩

/-! ### The model's hull is the cap certificate's solid, scaled -/

theorem kval_seedT : kval seedT = ![tribonacci, 1, -tribonacci ^ 2] := by
  funext r
  fin_cases r <;> simp [kval, seedT, tq, ExactScalarVal.val, TribQ.val]

theorem kval_octaApplyT (g : ℕ) (hg : g < 24) (v : KVec TribQ) :
    Cap.toEuc (kval (octaApplyT g v)) = (octaMatrix ⟨g, hg⟩).toEuclideanLin (Cap.toEuc (kval v)) := by
  ext r
  simp only [Cap.toEuc, kval, octaApplyT, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three, octaMatrix, Matrix.of_apply, WithLp.ofLp_toLp, PiLp.toLp_apply]
  rw [show ExactScalarOps.add = TribQ.add from rfl, show ExactScalarOps.scale = TribQ.scale from rfl,
    show TribQ.add = (· + ·) from rfl]
  simp [ExactScalarVal.val, TribQ.val_add, TribQ.val_scale]

theorem snubOModel_orbit (i : VertexIndex) :
    snubOModel.toC4.vertex i =
      (snubScale : ℝ) • Cap.toEuc (kval (scVerts.getD i.val (fun _ => TribQ.zero))) := by
  have hi : i.val < scVerts.size := by simp [scVerts]
  have hget : scVerts.getD i.val (fun _ => TribQ.zero) = octaApplyT (slotElemData.getD i.val 0) seedT := by
    simp [scVerts, Array.getD, hi]
  rw [OModel.toC4_vertex, OModel.orbit, hget,
    kval_octaApplyT (slotElemData.getD i.val 0) (by exact slotIdx_lt i.isLt), kval_seedT]
  change (octaMatrix (slotOcta i)).toEuclideanLin snubV0 = _
  rw [← map_smul]
  congr 1
  ext r
  fin_cases r <;> simp [snubV0, Cap.toEuc]

/-- The model's hull is snubScale times the hull of a certificate with the template's vertices. -/
theorem snubOModel_hull (c : KCert TribQ) (hV : c.V = scVerts) :
    snubOModel.toC4.polyhedron.hull = (snubScale : ℝ) • c.hull := by
  rw [CyclicModel.polyhedron_hull, KCert.hull, ← convexHull_smul]
  congr 1
  ext v
  simp only [CyclicModel.verts, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range,
    Set.mem_smul_set, Set.mem_setOf_eq, List.mem_map, hV]
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨_, ⟨kval (scVerts.getD i.val (fun _ => TribQ.zero)), ⟨_, ?_, rfl⟩, rfl⟩, (snubOModel_orbit i).symm⟩
    simp only [Array.getD, scVerts, Array.mem_toList_iff, Array.getElem_mem]
    simp
    exact ⟨i.val, i.isLt, rfl⟩
  · rintro ⟨_, ⟨_, ⟨vj, hvj, rfl⟩, rfl⟩, rfl⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hvj
    have hj' : j < 24 := by simpa [scVerts] using hj
    refine ⟨⟨j, hj'⟩, ?_⟩
    rw [snubOModel_orbit]
    simp [Array.getD, scVerts, hj']

/-- The caps hold for the exact model, given a checked certificate with the template's data. -/
theorem capsHold_snubOModel (c : KCert TribQ) (hc : c.check = true) (hm : certMatches c = true) :
    CapsHold snubOModel.toC4.polyhedron.hull := by
  rw [snubOModel_hull c (certMatches_sound hm).2.2.2.2]
  exact capsHold_of_cert c hc hm _ snubScale_pos

/-! ### Main theorem -/

/-- If the exact model is not Rupert, no snub cube is (either chirality, any similarity). -/
theorem snubCube_not_rupert (h : ¬ IsRupert snubOModel.toC4.verts) :
    ∀ V : Finset ℝ³, IsSnubCube V → ¬ IsRupert V := by
  have hsnub : ¬ IsRupert snubCube := by
    intro hr
    have hq : (0 : ℝ) < (snubScale : ℝ) * tribonacci := mul_pos snubScale_pos tribonacci_pos
    have := isRupert_image_similarity 0 _ hq 1 (Submonoid.one_mem _) _ hr
    simp only [Matrix.toLpLin_one, LinearMap.id_apply] at this
    rw [← snubOModel_verts] at this
    exact h this
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
  conv_lhs => rw [← Finset.image_id (s := snubCube)]
  congr 1
  funext x
  simp only [Function.comp, id, map_add, map_smul, smul_add, smul_smul, inv_mul_cancel₀ hs.ne',
    one_smul]
  rw [← IModel.toEuclideanLin_mul, hMM]
  simp

/-- Wikipedia's vertices are themselves a snub cube (the identity similarity). -/
theorem isSnubCube_snubCube : IsSnubCube snubCube := by
  refine ⟨0, 1, 1, one_pos, Submonoid.one_mem _, ?_⟩
  ext v
  simp

end SnubCube

end
