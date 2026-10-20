module

public import Minimality.FirstOrder
public import Mathlib.Analysis.Convex.Radon

@[expose] public section

/-!
# A rotation axis threading the quarter-turned inward wedges

FEWER-FACES-PROOFS.md, Proposition 8.7 (line-transversal form of first-order
freedom), the direction used to prove Rupertness. A small rotation, in the sense
`σ`, about the non-horizontal line `L = {(c₀ + z c₁, z)}` moves a point
`x = (p, z)` on the screen by `σ J (p − c₀ − z c₁)` (`J` the quarter turn
`rot90`): it turns about the point where `L` meets the point's depth level
(`screenVel_axis`). If this velocity points strictly into the shadow at every
point of `V`, i.e. if `L` meets each vertex's depth level inside the vertex's
inward cone turned by a quarter turn, `V` is Rupert (`isRupert_of_axis`, via
Lemma 1, `isRupert_of_firstOrderInward`). Each vertex's condition is convex in
the line's parameters `(c₀, c₁) ∈ ℝ⁴`, so by Helly it suffices that every 5
vertices admit a common line (`isRupert_of_axis_helly`).
-/

namespace Minimality

open scoped RealInnerProductSpace

/-- The rotation vector `σ (c₁, 1)` of the axis `{(c₀ + z c₁, z)}`. -/
noncomputable def axisOmega (σ : ℝ) (c₁ : ℝ²) : ℝ³ := !₂[σ * c₁ 0, σ * c₁ 1, σ]

/-- The translation that makes the rotation `axisOmega σ c₁` fix the point
`(c₀, 0)` of the axis: `τ = −ω × (c₀, 0)`. -/
noncomputable def axisTau (σ : ℝ) (c₀ : ℝ²) : ℝ³ := !₂[σ * c₀ 1, -(σ * c₀ 0), 0]

/-- **The screen motion of a rotation about a line.** -/
theorem screenVel_axis (σ : ℝ) (c₀ c₁ : ℝ²) (x : ℝ³) :
    screenVel (axisOmega σ c₁) (axisTau σ c₀) x = σ • rot90 (proj_xy x - c₀ - x 2 • c₁) := by
  ext i; fin_cases i <;>
    simp [screenVel, crossMatrix, axisOmega, axisTau, rot90, proj_xy, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three] <;> ring

/-- **Proposition 8.7, sufficient direction** (standard view): if a small rotation
about some non-horizontal line `{(c₀ + z c₁, z)}` moves every point of `V` strictly
into the shadow, then `V` is Rupert. -/
theorem isRupert_of_axis (V : Finset ℝ³) (σ : ℝ) (c₀ c₁ : ℝ²)
    (h : ∀ v ∈ V, IsInwardAt (proj_xy '' convexHull ℝ (V : Set ℝ³)) (proj_xy v)
      (σ • rot90 (proj_xy v - c₀ - v 2 • c₁))) :
    IsRupert V :=
  isRupert_of_firstOrderInward V (axisOmega σ c₁) (axisTau σ c₀) fun v hv => by
    rw [screenVel_axis]; exact h v hv

/-- **Proposition 8.7, sufficient direction**, at the view of a rotation `Q`. -/
theorem isRupert_of_axis_image (V : Finset ℝ³) (Q : Matrix (Fin 3) (Fin 3) ℝ) (hQ : Q ∈ SO3)
    (σ : ℝ) (c₀ c₁ : ℝ²)
    (h : ∀ v ∈ V.image Q.toEuclideanLin,
      IsInwardAt (proj_xy '' convexHull ℝ ((V.image Q.toEuclideanLin : Finset ℝ³) : Set ℝ³))
        (proj_xy v) (σ • rot90 (proj_xy v - c₀ - v 2 • c₁))) :
    IsRupert V :=
  isRupert_of_isRupert_image_rotation Q hQ V (isRupert_of_axis _ σ c₀ c₁ h)

/-- The strictly inward directions at a point of a convex set form a convex set. -/
theorem convex_setOf_isInwardAt {S : Set ℝ²} (hS : Convex ℝ S) {p : ℝ²} (hp : p ∈ S) :
    Convex ℝ {d | IsInwardAt S p d} := by
  intro d₁ h₁ d₂ h₂ a b ha hb hab
  obtain ⟨ε₁, he₁, h₁⟩ := h₁
  obtain ⟨ε₂, he₂, h₂⟩ := h₂
  set ε := min ε₁ ε₂
  have hε : 0 < ε := lt_min he₁ he₂
  have shrink : ∀ {δ : ℝ} {d : ℝ²}, 0 < δ → p + δ • d ∈ interior S → ε ≤ δ →
      p + ε • d ∈ interior S := by
    intro δ d hδ hd hle
    have := hS.add_smul_mem_interior hp hd (t := ε / δ) ⟨div_pos hε hδ, (div_le_one hδ).mpr hle⟩
    rwa [smul_smul, div_mul_cancel₀ _ hδ.ne'] at this
  refine ⟨ε, hε, ?_⟩
  have e : p + ε • (a • d₁ + b • d₂) = a • (p + ε • d₁) + b • (p + ε • d₂) := by
    have hp' : p = a • p + b • p := by rw [← add_smul, hab, one_smul]
    conv_lhs => rw [hp']
    simp only [smul_add, smul_smul, mul_comm ε a, mul_comm ε b]
    abel
  rw [e]
  exact hS.interior (shrink he₁ h₁ (min_le_left _ _)) (shrink he₂ h₂ (min_le_right _ _)) ha hb hab

/-- **Proposition 8.7 with Helly** (standard view): if for one sense `σ` every
at most 5 points of `V` admit a common axis line whose rotation moves them strictly
into the shadow, then one line works for all of `V`, and `V` is Rupert. -/
theorem isRupert_of_axis_helly (V : Finset ℝ³) (σ : ℝ)
    (h : ∀ I ⊆ V, I.card ≤ 5 → ∃ c : ℝ² × ℝ², ∀ v ∈ I,
      IsInwardAt (proj_xy '' convexHull ℝ (V : Set ℝ³)) (proj_xy v)
        (σ • rot90 (proj_xy v - c.1 - v 2 • c.2))) :
    IsRupert V := by
  classical
  set S := proj_xy '' convexHull ℝ (V : Set ℝ³) with hSdef
  have hS : Convex ℝ S := (convex_convexHull ℝ (V : Set ℝ³)).linear_image projL
  let F : ℝ³ → Set (ℝ² × ℝ²) := fun v =>
    {c | IsInwardAt S (proj_xy v) (σ • rot90 (proj_xy v - c.1 - v 2 • c.2))}
  have hconv : ∀ v ∈ V, Convex ℝ (F v) := by
    intro v hv c₁ h₁ c₂ h₂ a b ha hb hab
    have hb' : b = 1 - a := by linarith
    have hp : proj_xy v ∈ S := ⟨v, subset_convexHull ℝ _ hv, rfl⟩
    have key : σ • rot90 (proj_xy v - (a • c₁ + b • c₂).1 - v 2 • (a • c₁ + b • c₂).2) =
        a • (σ • rot90 (proj_xy v - c₁.1 - v 2 • c₁.2)) +
          b • (σ • rot90 (proj_xy v - c₂.1 - v 2 • c₂.2)) := by
      subst hb'
      ext i; fin_cases i <;>
        simp [rot90, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd] <;> ring
    show IsInwardAt S (proj_xy v) _
    rw [key]
    exact convex_setOf_isInwardAt hS hp h₁ h₂ ha hb hab
  have hdim : Module.finrank ℝ (ℝ² × ℝ²) = 4 := by simp
  obtain ⟨c, hc⟩ := Convex.helly_theorem' (𝕜 := ℝ) (s := V) (F := F) hconv (fun I hI hcard => by
    obtain ⟨c, hc⟩ := h I hI (by rw [hdim] at hcard; omega)
    exact ⟨c, Set.mem_iInter₂.mpr fun v hv => hc v hv⟩)
  exact isRupert_of_axis V σ c.1 c.2 fun v hv => Set.mem_iInter₂.mp hc v hv

end Minimality

end
