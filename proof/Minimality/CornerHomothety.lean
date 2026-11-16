module

public import Minimality.CornerOrthant
public import Minimality.CornerScaling

/-!
# Lemma LH (Laplacian homothety) and the scaling normal form of a metric

Let `G` be a real `n × n` matrix with a scaling vector `v` (`v_a (G v)_a = 1`, Lemma MO,
`exists_scaling_of_posDef`), `t = 1/v` (so `G v = t`, `t · v = n`), and `m` a real number with
`N = 1 + n m ≠ 0`.

* `homMetric G v m = (G + m t tᵀ) / N` (the metric `G̃`).  In the rescaled frame
  `H = V G V = I + L_c` (`c_ab = −v_a v_b G_ab`, `scalCoef`) it is `I + L_{c̃}` with
  `c̃ = (c − m)/N` (`homMetric_rescaled`, `homMetric_laplacian`): on `1^⊥` the triangle
  Laplacian of the all-ones weights is `n I`, which is where `n m` comes from.
* **Lemma LH.**  `mulVec_homView`: for every `d̃`, the view
  `d_m = (m (t · d̃) v + d̃) / N` (`homView`) has `G d_m = G̃ d̃`.  Only `G v = t` is used:
  no symmetry, no obtuseness, no definiteness.
* `homMetric_scaling`: `v` is a scaling vector of `G̃` too.
* **Normal form (Corollary NF).**  `exists_homothety_normalForm`: if `G` is positive definite and
  obtuse (`G_ab ≤ 0`, `a ≠ b`) and `v > 0` is its scaling vector, the choice
  `m = min_{a ≠ b} c_ab ≥ 0` makes `G̃` positive definite, obtuse, with scaling vector `v`, and with a
  zero entry `G̃_ab = 0` at the argmin pair (one right angle at the corner).
* `homView_mem_cone`: `d_m` is a nonnegative combination of `v` and `d̃` when `m ≥ 0` and
  `t · d̃ ≥ 0`, so it lies in every convex cone that contains both.
* **The leaf.**  `isRupert_corner_homothety`: a closed cell containing `view v` and `view d̃`
  whose rim is robustly unimodal for the frame depths of the covector `G̃ d̃` certifies `x`.
  `isRupert_corner_homothety_twin`: the same with the hypothesis read on the twin solid (same
  frame coordinates, Gram matrix `G̃`).

Sources: Fable (MO, NF; CORNER-SO-IDEAS-FABLE §2), Gemini (LH; CORNER-SO-IDEAS-GEMINI, Wiles 1).
-/

@[expose] public section

set_option autoImplicit false

open Finset Matrix
open scoped RealInnerProductSpace

namespace Minimality
namespace CornerSnap

section General

variable {ι : Type*} [Fintype ι]

/-- The homothety metric `G̃ = (G + m t tᵀ) / (1 + n m)`, `t_a = 1 / v_a`. -/
noncomputable def homMetric (G : Matrix ι ι ℝ) (v : ι → ℝ) (m : ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun a b => (G a b + m / (v a * v b)) / (1 + Fintype.card ι * m)

/-- The contracted view `d_m = (m (t · d̃) v + d̃) / (1 + n m)`. -/
noncomputable def homView (v : ι → ℝ) (m : ℝ) (d : ι → ℝ) : ι → ℝ :=
  fun a => (m * (∑ b, d b / v b) * v a + d a) / (1 + Fintype.card ι * m)

/-- The pair coefficients `c_ab = −v_a v_b G_ab` of the rescaled frame `V G V = I + L_c`. -/
def scalCoef (G : Matrix ι ι ℝ) (v : ι → ℝ) (a b : ι) : ℝ := -(v a * v b * G a b)

/-- The shifted coefficients `c̃ = (c − m) / (1 + n m)`. -/
noncomputable def homCoef (G : Matrix ι ι ℝ) (v : ι → ℝ) (m : ℝ) (a b : ι) : ℝ :=
  (scalCoef G v a b - m) / (1 + Fintype.card ι * m)

variable {G : Matrix ι ι ℝ} {v : ι → ℝ}

theorem ne_zero_of_scaling (hv : ∀ a, v a * (G *ᵥ v) a = 1) (a : ι) : v a ≠ 0 := by
  intro h; have := hv a; rw [h, zero_mul] at this; exact zero_ne_one this

/-- **Lemma LH (Laplacian homothety).**  `G d_m = G̃ d̃` for every `d̃` and every `m`; only the
scaling identity `v_a (G v)_a = 1` is used. -/
theorem mulVec_homView (hv : ∀ a, v a * (G *ᵥ v) a = 1) (m : ℝ) (d : ι → ℝ) :
    G *ᵥ homView v m d = homMetric G v m *ᵥ d := by
  funext a
  have hva := ne_zero_of_scaling hv a
  have hGa : ∑ b, G a b * v b = 1 / v a := by
    rw [eq_div_iff hva, mul_comm]; simpa [mulVec, dotProduct] using hv a
  set N := 1 + (Fintype.card ι : ℝ) * m
  set s := ∑ b, d b / v b
  simp only [mulVec, dotProduct, homView, homMetric, Matrix.of_apply]
  have e1 : ∑ b, G a b * ((m * s * v b + d b) / N) =
      ∑ b, (m * s / N * (G a b * v b) + 1 / N * (G a b * d b)) :=
    Finset.sum_congr rfl fun b _ => by ring
  have e2 : ∑ b, (G a b + m / (v a * v b)) / N * d b =
      ∑ b, (1 / N * (G a b * d b) + m / (N * v a) * (d b / v b)) :=
    Finset.sum_congr rfl fun b _ => by
      by_cases hvb : v b = 0
      · simp [hvb]; ring
      · field_simp
  rw [e1, e2, Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [← Finset.mul_sum]
  rw [hGa]
  by_cases hN : N = 0
  · simp [hN]
  · field_simp
    ring

/-- `d̃ = v` is fixed: `d_m(v) = v` (`t · v = n`). -/
theorem homView_self (hv : ∀ a, v a * (G *ᵥ v) a = 1) {m : ℝ}
    (hN : 1 + Fintype.card ι * m ≠ 0) : homView v m v = v := by
  funext a
  have : ∑ b, v b / v b = Fintype.card ι := by
    rw [Finset.sum_congr rfl fun b _ => div_self (ne_zero_of_scaling hv b)]; simp
  simp only [homView, this]
  rw [div_eq_iff hN]; ring

/-- `v` is a scaling vector of `G̃` (needs `1 + n m ≠ 0`). -/
theorem homMetric_scaling (hv : ∀ a, v a * (G *ᵥ v) a = 1) {m : ℝ}
    (hN : 1 + Fintype.card ι * m ≠ 0) (a : ι) : v a * (homMetric G v m *ᵥ v) a = 1 := by
  rw [← mulVec_homView hv, homView_self hv hN]; exact hv a

/-- In the rescaled frame, `v_a v_b G̃_ab = −c̃_ab` (all `a, b`, the diagonal included). -/
theorem homMetric_rescaled (hv : ∀ a, v a * (G *ᵥ v) a = 1) (m : ℝ) (a b : ι) :
    v a * v b * homMetric G v m a b = -homCoef G v m a b := by
  have ha := ne_zero_of_scaling hv a
  have hb := ne_zero_of_scaling hv b
  simp only [homMetric, homCoef, scalCoef, Matrix.of_apply]
  by_cases hN : 1 + (Fintype.card ι : ℝ) * m = 0
  · simp [hN]
  · field_simp; ring

/-- **The Laplacian form** `V G̃ V = I + L_{c̃}`: off the diagonal `−c̃_ab`, on the diagonal
`1 + Σ_{j ≠ a} c̃_aj` (row sums `1`, from `homMetric_scaling`). -/
theorem homMetric_laplacian [DecidableEq ι] (hv : ∀ a, v a * (G *ᵥ v) a = 1) {m : ℝ}
    (hN : 1 + Fintype.card ι * m ≠ 0) (a b : ι) :
    v a * v b * homMetric G v m a b =
      if a = b then 1 + ∑ j ∈ univ.erase a, homCoef G v m a j else -homCoef G v m a b := by
  split_ifs with hab
  · subst hab
    have hrow : ∑ j, v a * v j * homMetric G v m a j = 1 := by
      have := homMetric_scaling hv hN a
      simp only [mulVec, dotProduct, Finset.mul_sum] at this
      rw [← this]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)] at hrow
    rw [Finset.sum_congr rfl fun j _ => homMetric_rescaled hv m a j, Finset.sum_neg_distrib] at hrow
    linarith
  · exact homMetric_rescaled hv m a b

/-- Obtuse entries: `c_ab ≥ m` gives `G̃_ab ≤ 0` (for `v_a, v_b > 0`, `1 + n m > 0`). -/
theorem homMetric_nonpos (hv : ∀ a, v a * (G *ᵥ v) a = 1) {m : ℝ}
    (hN : 0 < 1 + Fintype.card ι * m) {a b : ι} (ha : 0 < v a) (hb : 0 < v b)
    (hc : m ≤ scalCoef G v a b) : homMetric G v m a b ≤ 0 := by
  have h := homMetric_rescaled hv m a b
  have hc' : 0 ≤ homCoef G v m a b := div_nonneg (by linarith) hN.le
  have hab := mul_pos ha hb
  by_contra hcon
  push Not at hcon
  have := mul_pos hab hcon
  linarith

/-- The argmin pair: `c_ab = m` gives `G̃_ab = 0`. -/
theorem homMetric_eq_zero (hv : ∀ a, v a * (G *ᵥ v) a = 1) {m : ℝ} {a b : ι}
    (hc : scalCoef G v a b = m) : homMetric G v m a b = 0 := by
  have h := homMetric_rescaled hv m a b
  simp only [homCoef, hc, sub_self, zero_div, neg_zero] at h
  rcases mul_eq_zero.1 h with h | h
  · exact absurd h (mul_ne_zero (ne_zero_of_scaling hv a) (ne_zero_of_scaling hv b))
  · exact h

/-- `G̃ = (1 + n m)⁻¹ • (G + m • t tᵀ)`. -/
theorem homMetric_eq_smul (G : Matrix ι ι ℝ) (v : ι → ℝ) (m : ℝ) :
    homMetric G v m = (1 + Fintype.card ι * m)⁻¹ •
      (G + m • vecMulVec (fun a => (v a)⁻¹) (fun a => (v a)⁻¹)) := by
  ext a b
  simp only [homMetric, Matrix.of_apply, Matrix.smul_apply, Matrix.add_apply, vecMulVec_apply,
    smul_eq_mul, div_eq_mul_inv, mul_inv]
  ring

/-- `G̃` is positive definite when `G` is and `m ≥ 0` (no scaling identity needed). -/
theorem homMetric_posDef (hG : G.PosDef) {m : ℝ} (hm : 0 ≤ m) : (homMetric G v m).PosDef := by
  rw [homMetric_eq_smul]
  have hN : 0 < (1 + Fintype.card ι * m)⁻¹ := inv_pos.2 (by positivity)
  refine Matrix.PosDef.smul (hG.add_posSemidef (Matrix.PosSemidef.smul ?_ hm)) hN
  simpa using posSemidef_vecMulVec_self_star (fun a => (v a)⁻¹)

/-- **Corollary NF (normal form).**  `G` positive definite and obtuse, `v > 0` its scaling
vector.  With `m = min_{a ≠ b} c_ab` (`c_ab = −v_a v_b G_ab ≥ 0`), `G̃` is positive definite,
obtuse, has the same scaling vector, and has a zero entry at the argmin pair.  Needs `n ≥ 2`
(`Nontrivial ι`) for the minimum to exist. -/
theorem exists_homothety_normalForm [Nontrivial ι] (hG : G.PosDef)
    (hob : ∀ a b, a ≠ b → G a b ≤ 0) (hvpos : ∀ a, 0 < v a) (hv : ∀ a, v a * (G *ᵥ v) a = 1) :
    ∃ m, 0 ≤ m ∧ (∀ a b, a ≠ b → m ≤ scalCoef G v a b) ∧
      (∃ a b, a ≠ b ∧ scalCoef G v a b = m) ∧ (homMetric G v m).PosDef ∧
      (∀ a b, a ≠ b → homMetric G v m a b ≤ 0) ∧ (∃ a b, a ≠ b ∧ homMetric G v m a b = 0) ∧
      ∀ a, v a * (homMetric G v m *ᵥ v) a = 1 := by
  classical
  obtain ⟨a₀, b₀, hab₀⟩ := exists_pair_ne ι
  have hne : (univ.offDiag : Finset (ι × ι)).Nonempty := ⟨(a₀, b₀), by simp [hab₀]⟩
  obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image _ (fun q : ι × ι => scalCoef G v q.1 q.2) hne
  have hp' : p.1 ≠ p.2 := by simpa using hp
  set m := scalCoef G v p.1 p.2 with hm
  have hlow : ∀ a b, a ≠ b → m ≤ scalCoef G v a b := fun a b h => hmin (a, b) (by simp [h])
  have hm0 : 0 ≤ m := by
    simp only [hm, scalCoef]
    have := hob p.1 p.2 hp'
    have := mul_pos (hvpos p.1) (hvpos p.2)
    nlinarith
  have hN : 0 < 1 + Fintype.card ι * m := by positivity
  exact ⟨m, hm0, hlow, ⟨p.1, p.2, hp', rfl⟩, homMetric_posDef hG hm0,
    fun a b h => homMetric_nonpos hv hN (hvpos a) (hvpos b) (hlow a b h),
    ⟨p.1, p.2, hp', homMetric_eq_zero hv rfl⟩, homMetric_scaling hv hN.ne'⟩

/-- `d_m = (m (t · d̃) / N) v + (1 / N) d̃`, a nonnegative combination when `m ≥ 0` and
`t · d̃ ≥ 0`: it lies in every set of views closed under nonnegative combinations that contains
`v` and `d̃` (a convex cone, e.g. a closed cell). -/
theorem homView_mem_cone {K : Set (ι → ℝ)}
    (hK : ∀ x ∈ K, ∀ y ∈ K, ∀ α β : ℝ, 0 ≤ α → 0 ≤ β → α • x + β • y ∈ K) {m : ℝ} (hm : 0 ≤ m)
    {d : ι → ℝ} (hs : 0 ≤ ∑ b, d b / v b) (hvK : v ∈ K) (hdK : d ∈ K) : homView v m d ∈ K := by
  have hN : 0 < 1 + Fintype.card ι * m := by positivity
  have e : homView v m d = (m * (∑ b, d b / v b) / (1 + Fintype.card ι * m)) • v +
      (1 / (1 + Fintype.card ι * m)) • d := by
    funext a; simp only [homView, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [e]
  exact hK _ hvK _ hdK _ _ (div_nonneg (mul_nonneg hm hs) hN.le) (div_nonneg zero_le_one hN.le)

end General

/-! ### The corner leaf -/

section Corner

variable {ι : Type*}

/-- The Gram matrix `G_jk = ⟪e_j, e_k⟫` of the corner frame. -/
noncomputable def Corner.gram (C : Corner ι) : Matrix (Fin 3) (Fin 3) ℝ := Matrix.gram ℝ C.axis

/-- `G d` is the depth covector: `(G d)_k = ⟪e_k, view d⟫`. -/
theorem Corner.gram_mulVec (C : Corner ι) (d : Fin 3 → ℝ) : C.gram *ᵥ d = C.cov d := by
  funext k
  simp only [Corner.gram, mulVec, dotProduct, Matrix.gram_apply, Corner.cov, Corner.view,
    Fin.sum_univ_three, inner_add_right, inner_smul_right]
  simp [Corner.axis]
  ring

theorem Corner.gram_posDef {C : Corner ι} (hli : LinearIndependent ℝ ![C.ea, C.eb, C.ec]) :
    C.gram.PosDef :=
  Matrix.posDef_gram_of_linearIndependent hli

/-- **Lemma MO for a corner frame**: a frame with linearly independent axes has a positive
axis view `v` whose depth covector is `1 / v`. -/
theorem Corner.exists_scaling {C : Corner ι} (hli : LinearIndependent ℝ ![C.ea, C.eb, C.ec]) :
    ∃ v : Fin 3 → ℝ, (∀ a, 0 < v a) ∧ ∀ a, v a * C.cov v a = 1 := by
  obtain ⟨v, hv, h⟩ := exists_scaling_of_posDef (Corner.gram_posDef hli)
  exact ⟨v, hv, fun a => by rw [← C.gram_mulVec]; exact h a⟩

/-- The frame depth of the point `p` for a covector `l`: `Σ_k X_k(p) l_k` (the depth up to a
constant, `Corner.Rep.depth_sub_frameDepth`). -/
noncomputable def Corner.frameDepth (C : Corner ι) (l : Fin 3 → ℝ) (p : ι) : ℝ :=
  C.Xa p * l 0 + C.Xb p * l 1 + C.Xc p * l 2

theorem Corner.Rep.depth_sub_frameDepth {C : Corner ι} {x : ι → ℝ³} (hC : C.Rep x)
    (d : Fin 3 → ℝ) (p q : ι) :
    ⟪x p, C.view d⟫ - ⟪x q, C.view d⟫ = C.frameDepth (C.cov d) p - C.frameDepth (C.cov d) q := by
  rw [hC.depth_sub_formRow, C.formRow_eq_cov]
  simp only [Corner.frameDepth, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

end Corner

/-- `RobUni` depends only on the differences. -/
theorem robUni_of_sub_eq {k : ℕ} {z z' : ZMod k → ℝ} (h : ∀ i j, z i - z j = z' i - z' j)
    (hz : H21.RobUni z) : H21.RobUni z' := by
  intro B b c d h1 h2 h3 h4 ⟨e1, e2, e3, e4⟩
  refine hz B b c d h1 h2 h3 h4 ⟨?_, ?_, ?_, ?_⟩
  · linarith [h (B + b) B]
  · linarith [h (B + b) (B + c)]
  · linarith [h (B + d) B]
  · linarith [h (B + d) (B + c)]

section Leaves
open Minimality.H21

variable {n m : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}

/-- Closed cells are convex cones in frame coordinates. -/
theorem cellLe_view_comb {F : S0xFac m S x} {U Dn : Finset (Fin m)} (C : Corner (Fin n))
    {d e : Fin 3 → ℝ} (hd : CellLe F U Dn (C.view d)) (he : CellLe F U Dn (C.view e)) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) : CellLe F U Dn (C.view (α • d + β • e)) := by
  have hv : C.view (α • d + β • e) = α • C.view d + β • C.view e := by
    simp only [Corner.view, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, mul_smul,
      smul_add]
    abel
  rw [hv]
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · rw [inner_add_right, inner_smul_right, inner_smul_right]
    have := hd.1 t ht; have := he.1 t ht; positivity
  · rw [inner_add_right, inner_smul_right, inner_smul_right]
    have h1 := hd.2 t ht; have h2 := he.2 t ht
    nlinarith [mul_nonneg hα (neg_nonneg.2 h1), mul_nonneg hβ (neg_nonneg.2 h2)]

/-- **Homothety leaf (Lemma LH).**  `v` is a scaling vector of the frame metric `G`
(`v_a (G v)_a = 1`), `m ≥ 0`, and `d̃` a view with `Σ_a d̃_a / v_a ≥ 0`.  If a nonempty cell
(rim length `≥ 4`) has `view v` and `view d̃` in its closure and the rim is robustly unimodal for
the frame depths of the covector `G̃ d̃` (`G̃ = homMetric G v m`), then `x` is Rupert: the view
`d_m` of the segment `[v, d̃]` is in the closed cell and has covector `G d_m = G̃ d̃`.
Neither obtuseness nor `v > 0` is used; in use `G` is obtuse and `m = min c_ab`
(`exists_homothety_normalForm`), so `G̃` is a one-right-angle metric. -/
theorem isRupert_corner_homothety {k : ℕ} [NeZero k] (hk : 4 ≤ k) (F : S0xFac m S x)
    (hx : Function.Injective x) {c : ZMod k → Fin n} (hc : Function.Injective c)
    {U Dn : Finset (Fin m)} (hcyc : S0xCycUD S c U Dn) {a : ℝ³} (ha : CellAt F U Dn a)
    {C : Corner (Fin n)} (hC : C.Rep x) {v : Fin 3 → ℝ} (hv : ∀ a, v a * (C.gram *ᵥ v) a = 1)
    {μ : ℝ} (hμ : 0 ≤ μ) {d : Fin 3 → ℝ} (hs : 0 ≤ ∑ b, d b / v b)
    (huv : CellLe F U Dn (C.view v)) (hud : CellLe F U Dn (C.view d))
    (hR : RobUni fun i => C.frameDepth (homMetric C.gram v μ *ᵥ d) (c i)) :
    IsRupert (univ.image x) := by
  have hm : CellLe F U Dn (C.view (homView v μ d)) :=
    homView_mem_cone (K := {e | CellLe F U Dn (C.view e)})
      (fun _ hx' _ hy' _ _ hα hβ => cellLe_view_comb C hx' hy' hα hβ) hμ hs huv hud
  refine isRupert_of_closedCell hk F hx hc hcyc ha hm (robUni_of_sub_eq (fun i j => ?_) hR)
  rw [hC.depth_sub_frameDepth, ← C.gram_mulVec, mulVec_homView hv]

/-- **Twin form of the homothety leaf.**  The twin solid `x'` has a frame `C'` with the same
frame coordinates as `C` and Gram matrix `G̃ = homMetric G v m` (for obtuse `G` and
`m = min c_ab`: the same shape with one right angle at the corner).  If the twin's rim depths at
`view' d̃` are robustly unimodal and `x`'s closed cell contains `view v` and `view d̃`, then `x` is
Rupert.  (Closed cells are read in frame coordinates through `x`'s own facets.) -/
theorem isRupert_corner_homothety_twin {k : ℕ} [NeZero k] (hk : 4 ≤ k) (F : S0xFac m S x)
    (hx : Function.Injective x) {c : ZMod k → Fin n} (hc : Function.Injective c)
    {U Dn : Finset (Fin m)} (hcyc : S0xCycUD S c U Dn) {a : ℝ³} (ha : CellAt F U Dn a)
    {C : Corner (Fin n)} (hC : C.Rep x) {v : Fin 3 → ℝ} (hv : ∀ a, v a * (C.gram *ᵥ v) a = 1)
    {μ : ℝ} (hμ : 0 ≤ μ) {d : Fin 3 → ℝ} (hs : 0 ≤ ∑ b, d b / v b)
    (huv : CellLe F U Dn (C.view v)) (hud : CellLe F U Dn (C.view d))
    {C' : Corner (Fin n)} {x' : Fin n → ℝ³} (hC' : C'.Rep x') (hXa : C'.Xa = C.Xa)
    (hXb : C'.Xb = C.Xb) (hXc : C'.Xc = C.Xc) (hG : C'.gram = homMetric C.gram v μ)
    (hR : RobUni fun i => ⟪x' (c i), C'.view d⟫) :
    IsRupert (univ.image x) := by
  refine isRupert_corner_homothety hk F hx hc hcyc ha hC hv hμ hs huv hud
    (robUni_of_sub_eq (fun i j => ?_) hR)
  rw [hC'.depth_sub_frameDepth, ← C'.gram_mulVec, hG]
  simp only [Corner.frameDepth, hXa, hXb, hXc]

end Leaves

end CornerSnap
end Minimality
