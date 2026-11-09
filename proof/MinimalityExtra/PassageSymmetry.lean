module

public import Mathlib
public import MinimalityExtra

/-!
# The symmetry group acts on passages (V-crease identity)
-/

@[expose] public section

open scoped Classical

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace MinimalityExtra

theorem tel_mul (A B : Matrix (Fin 3) (Fin 3) ℝ) (p : ℝ³) :
    (A * B).toEuclideanLin p = A.toEuclideanLin (B.toEuclideanLin p) := by
  ext i
  simp [Matrix.mulVec_mulVec]

theorem proj_diag (e : ℝ) (A : Matrix (Fin 3) (Fin 3) ℝ) (p : ℝ³) :
    proj_xy ((Matrix.diagonal ![1, 1, e] * A).toEuclideanLin p) = proj_xy (A.toEuclideanLin p) := by
  ext i
  fin_cases i <;> simp [proj_xy, Matrix.mulVec, dotProduct,
    Matrix.diagonal_apply, Fin.sum_univ_three]

theorem orth_iff {A : Matrix (Fin 3) (Fin 3) ℝ} :
    A ∈ Matrix.orthogonalGroup (Fin 3) ℝ ↔ A * A.transpose = 1 := by
  simp [Matrix.mem_orthogonalGroup_iff]

theorem orth_iff' {A : Matrix (Fin 3) (Fin 3) ℝ} (h : A ∈ Matrix.orthogonalGroup (Fin 3) ℝ) :
    A.transpose * A = 1 := mul_eq_one_comm.mp (orth_iff.mp h)

theorem diag_one : Matrix.diagonal ![(1:ℝ), 1, 1] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem orth_det {A : Matrix (Fin 3) (Fin 3) ℝ} (h : A ∈ Matrix.orthogonalGroup (Fin 3) ℝ) :
    A.det * A.det = 1 := by
  have := congrArg Matrix.det (orth_iff.mp h)
  simpa [Matrix.det_mul] using this

theorem diag_orth {e : ℝ} (he : e * e = 1) :
    Matrix.diagonal ![(1:ℝ), 1, e] ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [orth_iff]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [he]

theorem diag_det (e : ℝ) : (Matrix.diagonal ![(1:ℝ), 1, e]).det = e := by
  simp [Matrix.det_diagonal, Fin.prod_univ_three]

/-- the rotation `diag(1,1,det g) R gᵀ` is proper -/
theorem new_rot {g R : Matrix (Fin 3) (Fin 3) ℝ} (hg : g ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (hR : R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    Matrix.diagonal ![1, 1, g.det] * R * g.transpose ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff] at hR ⊢
  have hd := orth_det hg
  have hE := diag_orth hd
  refine ⟨?_, ?_⟩
  · have hgT : g.transpose ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
      rw [orth_iff]
      simpa using orth_iff' hg
    exact (Submonoid.mul_mem _ (Submonoid.mul_mem _ hE hR.1) hgT)
  · rw [Matrix.det_mul, Matrix.det_mul, hR.2, diag_det, Matrix.det_transpose]
    linarith

/-- `g` maps the hull of `K` onto itself. -/
theorem hull_img {K : Finset ℝ³} {g : Matrix (Fin 3) (Fin 3) ℝ}
    (hg : g ∈ Matrix.orthogonalGroup (Fin 3) ℝ) (hK : ∀ v ∈ K, g.toEuclideanLin v ∈ K) :
    g.toEuclideanLin '' convexHull ℝ (K : Set ℝ³) = convexHull ℝ (K : Set ℝ³) := by
  have hTg : g.transpose * g = 1 := orth_iff' hg
  have hinj : Function.Injective (fun v : ℝ³ => g.toEuclideanLin v) := by
    intro a b hab
    have := congrArg g.transpose.toEuclideanLin hab
    simp only at this
    rw [← tel_mul, ← tel_mul, hTg] at this
    simpa using this
  have hsurj : ∀ w ∈ K, ∃ v ∈ K, g.toEuclideanLin v = w := by
    have hsub : K.image (fun v : ℝ³ => g.toEuclideanLin v) ⊆ K := by
      intro w hw
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      exact hK v hv
    have heq := Finset.eq_of_subset_of_card_le hsub
      (by rw [Finset.card_image_of_injective _ hinj])
    intro w hw
    rw [← heq] at hw
    obtain ⟨v, hv, e⟩ := Finset.mem_image.mp hw
    exact ⟨v, hv, e⟩
  have himg := (Matrix.toEuclideanLin g).image_convexHull (K : Set ℝ³)
  rw [show (⇑(Matrix.toEuclideanLin g) : ℝ³ → ℝ³) = (fun v => g.toEuclideanLin v) from rfl] at himg
  rw [himg]
  congr 1
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩; exact hK v hv
  · intro hw; obtain ⟨v, hv, e⟩ := hsurj w hw; exact ⟨v, hv, e⟩

theorem hull_fwd {K : Finset ℝ³} {g : Matrix (Fin 3) (Fin 3) ℝ}
    (hg : g ∈ Matrix.orthogonalGroup (Fin 3) ℝ) (hK : ∀ v ∈ K, g.toEuclideanLin v ∈ K)
    {q : ℝ³} (hq : q ∈ convexHull ℝ (K : Set ℝ³)) :
    g.toEuclideanLin q ∈ convexHull ℝ (K : Set ℝ³) := by
  rw [← hull_img hg hK]; exact ⟨q, hq, rfl⟩

theorem hull_bwd {K : Finset ℝ³} {g : Matrix (Fin 3) (Fin 3) ℝ}
    (hg : g ∈ Matrix.orthogonalGroup (Fin 3) ℝ) (hK : ∀ v ∈ K, g.toEuclideanLin v ∈ K)
    {q : ℝ³} (hq : q ∈ convexHull ℝ (K : Set ℝ³)) :
    g.transpose.toEuclideanLin q ∈ convexHull ℝ (K : Set ℝ³) := by
  have hTg : g.transpose * g = 1 := orth_iff' hg
  have hq' := hq
  rw [← hull_img hg hK] at hq'
  obtain ⟨w, hw, rfl⟩ := hq'
  rw [← tel_mul, hTg]; simpa using hw

theorem shadow_eq {K : Finset ℝ³} {g R : Matrix (Fin 3) (Fin 3) ℝ} (e : ℝ)
    (hg : g ∈ Matrix.orthogonalGroup (Fin 3) ℝ) (hK : ∀ v ∈ K, g.toEuclideanLin v ∈ K)
    (o : EuclideanSpace ℝ (Fin 2)) :
    { o + proj_xy ((Matrix.diagonal ![1, 1, e] * R * g.transpose).toEuclideanLin p) |
        p ∈ convexHull ℝ (K : Set ℝ³) } =
      { o + proj_xy (R.toEuclideanLin p) | p ∈ convexHull ℝ (K : Set ℝ³) } := by
  have hT : g.transpose * g = 1 := orth_iff' hg
  have key : ∀ p, proj_xy ((Matrix.diagonal ![1, 1, e] * R * g.transpose).toEuclideanLin p) =
      proj_xy (R.toEuclideanLin (g.transpose.toEuclideanLin p)) := by
    intro p
    rw [Matrix.mul_assoc, proj_diag, tel_mul]
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨g.transpose.toEuclideanLin p, hull_bwd hg hK hp, by rw [key]⟩
  · rintro ⟨q, hq, rfl⟩
    refine ⟨g.toEuclideanLin q, hull_fwd hg hK hq, ?_⟩
    have h1 : g.transpose.toEuclideanLin (g.toEuclideanLin q) = q := by
      rw [← tel_mul, hT]; simp
    rw [key, h1]

theorem outer_eq {K : Finset ℝ³} {g R : Matrix (Fin 3) (Fin 3) ℝ} (e : ℝ)
    (hg : g ∈ Matrix.orthogonalGroup (Fin 3) ℝ) (hK : ∀ v ∈ K, g.toEuclideanLin v ∈ K) :
    { proj_xy ((Matrix.diagonal ![1, 1, e] * R * g.transpose).toEuclideanLin q) |
        q ∈ convexHull ℝ (K : Set ℝ³) } =
      { proj_xy (R.toEuclideanLin q) | q ∈ convexHull ℝ (K : Set ℝ³) } := by
  have := shadow_eq (R := R) e hg hK 0
  simpa using this

theorem passageSymmetry : PassageSymmetry := by
  intro K g h hg hh hgK hhK Ri hRi o Ro hRo
  refine ⟨_, new_rot hh hRi, _, new_rot hg hRo, rfl, rfl,
    shadow_eq _ hh hhK o, outer_eq _ hg hgK, ?_⟩
  intro δ
  have hi := shadow_eq (R := Ri) h.det hh hhK o
  have ho := outer_eq (R := Ro) g.det hg hgK
  unfold PassageMargin
  rw [ho]
  constructor
  · intro H p hp
    have : o + proj_xy (Ri.toEuclideanLin p) ∈
        { o + proj_xy ((Matrix.diagonal ![1, 1, h.det] * Ri * h.transpose).toEuclideanLin p) |
          p ∈ convexHull ℝ (K : Set ℝ³) } := by rw [hi]; exact ⟨p, hp, rfl⟩
    obtain ⟨p', hp', e⟩ := this
    rw [← e]; exact H p' hp'
  · intro H p hp
    have : o + proj_xy ((Matrix.diagonal ![1, 1, h.det] * Ri * h.transpose).toEuclideanLin p) ∈
        { o + proj_xy (Ri.toEuclideanLin p) | p ∈ convexHull ℝ (K : Set ℝ³) } := by
      rw [← hi]; exact ⟨p, hp, rfl⟩
    obtain ⟨p', hp', e⟩ := this
    rw [← e]; exact H p' hp'

theorem mirrorFourPassages : MirrorFourPassages := by
  intro K S hS hdet hSK Ri hRi o Ro hRo
  have hSd : S.det = -1 := hdet
  have e1 : (Matrix.diagonal ![(1:ℝ), 1, -1]) = Matrix.diagonal ![1, 1, S.det] := by rw [hSd]
  have hflip := passageSymmetry K 1 S (by simp) hS (fun v hv => by simpa using hv) hSK Ri hRi o Ro hRo
  have htip := passageSymmetry K S 1 hS (by simp) hSK (fun v hv => by simpa using hv) Ri hRi o Ro hRo
  have hboth := passageSymmetry K S S hS hS hSK hSK Ri hRi o Ro hRo
  obtain ⟨Ri1, hRi1, Ro1, hRo1, e1i, e1o, -, -, m1⟩ := hflip
  obtain ⟨Ri2, hRi2, Ro2, hRo2, e2i, e2o, -, -, m2⟩ := htip
  obtain ⟨Ri3, hRi3, Ro3, hRo3, e3i, e3o, -, -, m3⟩ := hboth
  refine ⟨Ri3, hRi3, Ro3, hRo3, ?_, ?_, ?_⟩
  · rw [e3i, hSd]
  · rw [e3o, hSd]
  · intro δ H
    have hRi1' : Ri1 = Ri3 := by rw [e1i, e3i]
    have hRo2' : Ro2 = Ro3 := by rw [e2o, e3o]
    have hRo1' : Ro1 = Ro := by rw [e1o]; simp [Matrix.det_one, diag_one]
    have hRi2' : Ri2 = Ri := by rw [e2i]; simp [Matrix.det_one, diag_one]
    refine ⟨?_, ?_, (m3 δ).mpr H⟩
    · rw [← hRi1', ← hRo1'] at *
      exact (m1 δ).mpr H
    · rw [← hRo2', ← hRi2'] at *
      exact (m2 δ).mpr H

end MinimalityExtra
