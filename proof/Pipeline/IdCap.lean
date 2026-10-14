module

public import Pipeline.KCapTree

@[expose] public section

/-!
# Blow-up certificates at the identity

Near the identity the clearance of a pose vanishes to first order in the
rotation, so a box of rotations containing the identity cannot be checked by
interval bounds that do not scale with the rotation. The identity tube
(`AtlasProjectiveLocalViewTree`) bounds the second-order terms crudely; here
the rotations are blown up instead and balanced witnesses are checked as
polynomials divided by the rotation size, exactly as in the snub cube's caps
(`KCapCheck`), over a view triangle (`search/common/idcap.cc`).

For corners c₀, c₁, c₂ (projective view points) and a radius ρ, the chart
of the cube face (a, σ) has variables y = (μ, α, β, p₁, p₂) in
[0, ρ] × [0, 1]² × [−1, 1]² and

  view      u = c₀ + α (c₁ − c₀) + α β (c₂ − c₁)  (the triangle as a collapsed square),
  rotation  Cayley vector w = μ σ̂, σ̂_a = ±1, the other two (p₁, p₂).

Every view ξ (c₀ + w₁ (c₁ − c₀) + w₂ (c₂ − c₀)) with w₁, w₂ ≥ 0, w₁ + w₂ ≤ 1 and every
Cayley vector with |w|∞ ≤ ρ is a point of one of the six charts (`maxface`;
w = 0 at μ = 0; α = w₁ + w₂, β = w₂ / α). `IdCert.claim`: if each face's
tree checks, no such pose is Rupert.
-/

namespace Noperts.Pipeline

/-- ℚ as an exact scalar field (the Septopert's vertices are rational). -/
instance : ExactScalarOps ℚ where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  scale q a := q * a
  isZero x := decide (x = 0)
  lo x := x

noncomputable instance : ExactScalarVal ℚ where
  val x := (x : ℝ)
  val_zero := by simp [ExactScalarOps.zero]
  val_one := by simp [ExactScalarOps.one]
  val_add a b := by simp [ExactScalarOps.add]
  val_mul a b := by simp [ExactScalarOps.mul]
  val_scale q a := by simp [ExactScalarOps.scale]
  val_of_isZero a h := by
    have : a = 0 := of_decide_eq_true h
    simp [this]
  lo_le_val a := le_refl _

namespace KCap

open Noperts.Pipeline.KCap.PVec

variable {K : Type} [ExactScalarOps K]

/-- The view u = c₀ + α (c₁ − c₀) + α β (c₂ − c₁), (α, β) = (y 1, y 2) ∈ [0, 1]²: the
triangle as a collapsed square (the points with α ∈ [0, 1] at β = 0 and β = 1 are its sides
c₀c₁ and c₀c₂). -/
def idU (c : Fin 3 → KVec K) : PVec K :=
  PVec.add (PVec.const (c 0))
    (PVec.add (PVec.smul (pvar 1) (PVec.const (vsub (c 1) (c 0))))
      (PVec.smul (KPoly.mul 5 (pvar 1) (pvar 2)) (PVec.const (vsub (c 2) (c 1)))))

/-- The Cayley vector μ σ̂, σ̂ on the face (axis, sign) of [−1, 1]³ with free coordinates
y 3, y 4. -/
def idW (axis : ℕ) (sign : Bool) : PVec K :=
  PVec.smul (pvar 0) (fun i => faceCoord 3 axis sign 1 i.val)

/-- The chart box (lower end, width): μ ∈ [0, ρ], α, β ∈ [0, 1], p ∈ [−1, 1]². -/
def idBox (rho : ℚ) : Box := ![(0, rho), (0, 1), (0, 1), (-1, 2), (-1, 2)]

/-- The leaves divide by μ only (as the snub cube's F_e charts). -/
def idChartId : ChartId := ⟨.fe, 0, 0, true⟩

/-- An identity blow-up certificate: the solid's vertices, the view triangle's corners, the
radius, and per cube face a split tree of the chart box. -/
structure IdCert (K : Type) where
  V : Array (KVec K)
  c : Fin 3 → KVec K
  rho : ℚ
  faces : List ((ℕ × Bool) × KTree)

def idFaces : List (ℕ × Bool) := [(0, true), (0, false), (1, true), (1, false), (2, true), (2, false)]

def IdCert.faceCheck (cert : IdCert K) (axis : ℕ) (sign : Bool) (t : KTree) : Bool :=
  -- (The chart data once per face, not per leaf.)
  let cd := chartDataOf (idU cert.c) (idW axis sign) cert.V
  t.check (fun l box => l.check cert.V cd idChartId box) (fun _ => false) (idBox cert.rho)

def IdCert.hasFace (cert : IdCert K) (f : ℕ × Bool) : Bool :=
  cert.faces.any fun e => decide (e.1 = f) && cert.faceCheck f.1 f.2 e.2

def IdCert.check (cert : IdCert K) : Bool :=
  decide (0 ≤ cert.rho) && idFaces.all cert.hasFace

/-! ### Chart points -/

section points

variable [ExactScalarVal K]

theorem eval_idU (c : Fin 3 → KVec K) (y : Fin 5 → ℝ) :
    (idU c).eval y = kval (c 0) + (y 1 • (kval (c 1) - kval (c 0)) + (y 1 * y 2) • (kval (c 2) - kval (c 1))) := by
  simp [idU, PVec.eval_add, PVec.eval_smul, PVec.eval_const, eval_pvar, kval_vsub, KPoly.eval_mul]

theorem eval_idW (axis : ℕ) (sign : Bool) (y : Fin 5 → ℝ) :
    (idW (K := K) axis sign).eval y = y 0 • fun i =>
      if i.val = axis then ((signQ sign * 1 : ℚ) : ℝ) else y (freeVar 3 axis i.val) := by
  funext i
  show KPoly.eval 5 (KPoly.mul 5 (pvar 0) (faceCoord 3 axis sign 1 i.val)) y = _
  rw [KPoly.eval_mul, eval_pvar, eval_faceCoord]
  by_cases h : i.val = axis <;> simp [h]

/-- The chart point of a Cayley vector μ σ (σ on the face (axis, sign)) over the view
parameters α, β. -/
theorem id_point (axis : ℕ) (sign : Bool) (ha : axis < 3) (μ α β : ℝ) (σ : Fin 3 → ℝ)
    (hσ : σ ⟨axis, ha⟩ = ((signQ sign : ℚ) : ℝ)) (c : Fin 3 → KVec K) :
    let y : Fin 5 → ℝ := ![μ, α, β, (other3 axis σ).1, (other3 axis σ).2]
    (idU c).eval y = kval (c 0) + (α • (kval (c 1) - kval (c 0)) + (α * β) • (kval (c 2) - kval (c 1))) ∧
      (idW (K := K) axis sign).eval y = μ • σ := by
  intro y
  constructor
  · rw [eval_idU]
    simp [y]
  · rw [eval_idW]
    funext i
    obtain rfl | rfl | rfl : axis = 0 ∨ axis = 1 ∨ axis = 2 := by omega
    all_goals fin_cases i <;> simp [y, other3, freeVar, ← hσ]

end points

/-! ### The claim -/

section claim

variable [ExactScalarVal K]

/-- The solid: the hull of the certificate's vertices. -/
noncomputable def IdCert.hull (cert : IdCert K) : Set ℝ³ :=
  convexHull ℝ {v | ∃ vj ∈ cert.V.toList.map kval, v = Cap.toEuc vj}

theorem idBox_width {rho : ℚ} (h : 0 ≤ rho) : ∀ i, 0 ≤ (idBox rho i).2 := by
  intro i
  fin_cases i <;> simp [idBox, h]

omit [ExactScalarVal K] in
theorem hasFace_sound {cert : IdCert K} {f : ℕ × Bool} (h : cert.hasFace f = true) :
    ∃ t : KTree, cert.faceCheck f.1 f.2 t = true := by
  unfold IdCert.hasFace at h
  obtain ⟨e, -, he⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at he
  obtain ⟨rfl, hc⟩ := he
  exact ⟨e.2, hc⟩

/-- A checked face tree: no pose over a point of the chart box is Rupert. -/
theorem face_good (cert : IdCert K) (hrho : 0 ≤ cert.rho) (axis : ℕ) (sign : Bool) (t : KTree)
    (ht : cert.faceCheck axis sign t = true) (y : Fin 5 → ℝ) (hy : KPoly.InBox (idBox cert.rho) y)
    (p : MatrixPose) (ξ : ℝ) (hview : p.view = ξ • (idU cert.c).eval y)
    (hR : p.relativeRotation = cayleyMatrix ((idW (K := K) axis sign).eval y 0)
      ((idW (K := K) axis sign).eval y 1) ((idW (K := K) axis sign).eval y 2)) :
    ¬ RupertPose p cert.hull := by
  refine KTree.check_sound
    (fun l box => l.check cert.V (chartDataOf (idU cert.c) (idW axis sign) cert.V) idChartId box)
    (fun _ => false)
    (fun y => KPoly.InBox (idBox cert.rho) y → ∀ (p : MatrixPose) (ξ : ℝ),
      p.view = ξ • (idU cert.c).eval y →
      p.relativeRotation = cayleyMatrix ((idW (K := K) axis sign).eval y 0)
        ((idW (K := K) axis sign).eval y 1) ((idW (K := K) axis sign).eval y 2) →
      ¬ RupertPose p cert.hull) ?_ ?_ t (idBox cert.rho) (idBox_width hrho) ht y hy hy p ξ hview hR
  · intro l box hb hl y hyb hyr p ξ hview hR
    have h0 : 0 ≤ y 0 := by simpa [idBox] using (hyr 0).1
    exact Leaf.check_soundOf _ _ idChartId cert.V l box hl hb y hyb h0 (by simp [idChartId])
      (by simp [idChartId]) cert.hull rfl p ξ hview hR
  · intro box _ hc
    simp at hc

/-- **The identity blow-up claim**: if the certificate checks, no pose whose view is a
multiple of a point of the corners' parallelogram and whose relative rotation is the
Cayley rotation of a vector with |w|∞ ≤ ρ is Rupert. -/
theorem IdCert.claim (cert : IdCert K) (h : cert.check = true)
    (p : MatrixPose) (ξ w₁ w₂ : ℝ) (h₁ : 0 ≤ w₁) (h₂ : 0 ≤ w₂) (h₁₂ : w₁ + w₂ ≤ 1)
    (hview : p.view = ξ • (kval (cert.c 0) + (w₁ • (kval (cert.c 1) - kval (cert.c 0)) +
      w₂ • (kval (cert.c 2) - kval (cert.c 0)))))
    (w : Fin 3 → ℝ) (hw : ∀ i, |w i| ≤ cert.rho)
    (hR : p.relativeRotation = cayleyMatrix (w 0) (w 1) (w 2)) :
    ¬ RupertPose p cert.hull := by
  simp only [IdCert.check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨hrho, hfaces⟩ := h
  obtain ⟨μ, hμ0, hμle, ⟨i0, hi0⟩, a, sign, σ, hσa, hσ1, hwσ⟩ := maxface (by norm_num : 0 < 3) w
  have hmem : ((a.val, sign) : ℕ × Bool) ∈ idFaces := by
    fin_cases a <;> cases sign <;> simp [idFaces]
  obtain ⟨t, ht⟩ := hasFace_sound (hfaces _ hmem)
  -- The collapsed-square coordinates of the view: α = w₁ + w₂, β = w₂ / α.
  set α := w₁ + w₂ with hαdef
  set β := if α = 0 then 0 else w₂ / α with hβdef
  have hα : 0 ≤ α ∧ α ≤ 1 := ⟨by linarith, h₁₂⟩
  have hβ : 0 ≤ β ∧ β ≤ 1 := by
    simp only [hβdef]
    split_ifs with h0
    · exact ⟨le_refl _, zero_le_one⟩
    · have hpos : 0 < α := lt_of_le_of_ne hα.1 (Ne.symm h0)
      exact ⟨div_nonneg h₂ hpos.le, (div_le_one hpos).mpr (by linarith)⟩
  have hαβ : α * β = w₂ := by
    simp only [hβdef]
    split_ifs with h0
    · linarith
    · field_simp
  have hpt := id_point (K := K) a.val sign a.isLt μ α β σ hσa cert.c
  set y : Fin 5 → ℝ := ![μ, α, β, (other3 a.val σ).1, (other3 a.val σ).2] with hy_def
  have hμρ : μ ≤ cert.rho := by rw [← hi0]; exact hw i0
  have hother : |(other3 a.val σ).1| ≤ 1 ∧ |(other3 a.val σ).2| ≤ 1 := other3_bound a.val σ hσ1
  have hy : KPoly.InBox (idBox cert.rho) y := by
    intro i
    fin_cases i
    · simp [y, idBox, hμ0, hμρ]
    · simp [y, idBox, hα.1, hα.2]
    · simp [y, idBox, hβ.1, hβ.2]
    · have := abs_le.mp hother.1
      simp [y, idBox]; constructor <;> linarith
    · have := abs_le.mp hother.2
      simp [y, idBox]; constructor <;> linarith
  have hwy : (idW (K := K) a.val sign).eval y = w := by
    rw [hpt.2]; funext i; simp [hwσ i]
  apply face_good cert hrho a.val sign t ht y hy p ξ
  · rw [hpt.1, hview, hαβ]
    congr 1
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hαdef]
    ring
  · rw [hwy]; exact hR

end claim

end KCap

end Noperts.Pipeline

end
