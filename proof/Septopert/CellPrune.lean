module

public import Septopert.Cell
public import Pipeline.AtlasQuadratic
public import Atlas.QuadraticBernstein

@[expose] public section

/-!
# Checked prunes of the C3v cell

The C3v cell (`InC3vCell`) at a view u: tr(R c_k) ≤ tr R for the C3
rotations c_k, and tr(H_u R Q_i) ≤ tr R for the mirror ties Q_i. Both tables
are exact signed permutation matrices, so the prunes need no rounding
allowance: a box is pruned when a Bernstein/ball lower bound of the
(denominator-cleared) violation is strictly positive.

- `C3Prune.Box` (journal row `pi n`, `exact5d::IcoPruneValid` with
  `symmetry_neighbors.h`): with R = chart · cayley(w), the trace advantage
  tr(R c) − tr R of c = c3Mat (n + 1), times the Cayley denominator, is the
  quadratic Σ_ij (c_ji − δ_ij) Num_ij(w) (re-indexed `AtlasIcoPrune`).
- `MirrorPrune.Box` (journal row `ph g`, `exact5d::HalfTurnPruneValid` with
  `mirror_q.h`): over a view triangle (corners P_c, views Σ λ_c P_c, λ ≥ 0)
  the degree-2 Bernstein coefficients in λ of
  (tr(H_p R Q) − tr R) |p|² D(w), Q = mirrorQMat g, are the quadratics
    b_cd = Σ_ik N_ik [P_c,i (Q P_d)_k + P_d,i (Q P_c)_k − (P_c·P_d)(Q_ki + δ_ik)]
  (re-indexed `AtlasHalfTurnPrune` with the exact table, allowance 0); the box
  is pruned when every b_cd (c ≤ d) has a positive lower bound.

`inC3vCell_smul`: the cell depends only on the line through u, so a view
given projectively (`viewScale · Σ w_c T_c`) can be replaced by Σ w_c T_c.
-/

namespace Septopert
open Noperts

open scoped Matrix
open Noperts.Checker
open Noperts.Atlas
open Noperts.Pipeline
open CayleyAtlas

/-! ### Exact rational tables -/

/-- The C3 neighbor n (n = 0, 1) is c3Mat (n + 1), row-major as in
`symmetry_neighbors.h`. -/
def c3NeighborIdx : Fin 2 → Fin 3
  | 0 => 1
  | 1 => 2

def c3NeighborQ : Fin 2 → Fin 3 → Fin 3 → ℚ :=
  ![![![0, 1, 0], ![0, 0, 1], ![1, 0, 0]],
    ![![0, 0, 1], ![1, 0, 0], ![0, 1, 0]]]

theorem c3NeighborQ_cast (n : Fin 2) (i j : Fin 3) :
    (c3NeighborQ n i j : ℝ) = c3Mat (c3NeighborIdx n) i j := by
  fin_cases n <;> fin_cases i <;> fin_cases j <;> simp [c3NeighborQ, c3NeighborIdx, c3Mat]

/-- Q_g = mirrorQMat g, row-major as in `mirror_q.h`. -/
def mirrorQQ : Fin 3 → Fin 3 → Fin 3 → ℚ :=
  ![![![-1, 0, 0], ![0, 0, -1], ![0, -1, 0]],
    ![![0, 0, -1], ![0, -1, 0], ![-1, 0, 0]],
    ![![0, -1, 0], ![-1, 0, 0], ![0, 0, -1]]]

theorem mirrorQQ_cast (g : Fin 3) (i j : Fin 3) :
    (mirrorQQ g i j : ℝ) = mirrorQMat g i j := by
  fin_cases g <;> fin_cases i <;> fin_cases j <;> simp [mirrorQQ, mirrorQMat, mirrorMat]

/-! ### Numerators -/

theorem eval_numerator_eq (chart : ChartIndex) (i j : Fin 3) (x y z : ℝ) :
    (AtlasQuadratic.numeratorQuadratic chart i j).evalReal x y z =
      cayleyDenom x y z * (chartMatrix chart * cayleyMatrix x y z) i j := by
  rw [AtlasQuadratic.eval_numeratorQuadratic, cayleyNumeratorMatrix_eq_denom_smul,
    Matrix.mul_smul]
  simp

/-- The ball/Bernstein lower bound of a quadratic over a box's Cayley coordinates. -/
def quadLower (iv : AtlasInterval ℚ) (q : RatQuadratic3) : ℚ :=
  let vars : Fin 3 → RatBall := ![iv.coordinateBall 2, iv.coordinateBall 3, iv.coordinateBall 4]
  let ball := RatQuadratic3.evalTightBall vars q
  max (ball.center - ball.radius) (QuadraticBernstein.lower vars q)

theorem quadLower_le_eval (iv : AtlasInterval ℚ) (q : RatQuadratic3) {p : AtlasPose ℝ}
    (hp : p ∈ iv.toReal) : (quadLower iv q : ℝ) ≤ q.evalReal p.x p.y p.z := by
  have hvars : ∀ i : Fin 3,
      ((![iv.coordinateBall 2, iv.coordinateBall 3, iv.coordinateBall 4] : Fin 3 → RatBall) i).Holds
        (![p.x, p.y, p.z] i) := by
    intro i
    fin_cases i
    · exact iv.coordinateBall_holds hp 2
    · exact iv.coordinateBall_holds hp 3
    · exact iv.coordinateBall_holds hp 4
  have htight := RatBall.lower_le_of_holds (RatQuadratic3.evalTightBall_holds hvars q)
  have hbernstein := QuadraticBernstein.lower_le_evalReal hvars q
  push_cast at htight hbernstein
  unfold quadLower
  push_cast
  exact max_le htight hbernstein

/-! ### The C3 prune -/

namespace C3Prune

/-- `Σ_ij (c_ji − δ_ij) Num_ij`: the denominator-cleared trace advantage of
c = c3Mat (n + 1) (exact). -/
def advantageQuadratic (chart : ChartIndex) (n : Fin 2) : RatQuadratic3 :=
  AtlasQuadratic.sum3Q fun i => AtlasQuadratic.sum3Q fun j =>
    RatQuadratic3.scale (c3NeighborQ n j i - if i = j then 1 else 0)
      (AtlasQuadratic.numeratorQuadratic chart i j)

structure Box where
  interval : AtlasInterval ℚ
  chart : ChartIndex
  neighbor : Fin 2
deriving DecidableEq

def Box.lower (box : Box) : ℚ := quadLower box.interval (advantageQuadratic box.chart box.neighbor)

/-- `exact5d::IcoPruneValid` with the exact table (allowance 0). -/
def Box.Valid (box : Box) : Prop := 0 < box.lower

@[reducible] instance (box : Box) : Decidable box.Valid := by
  unfold Box.Valid
  infer_instance

theorem trace_advantage_eq (chart : ChartIndex) (n : Fin 2) (x y z : ℝ) :
    Matrix.trace ((chartMatrix chart * cayleyMatrix x y z) * c3Mat (c3NeighborIdx n)) -
        Matrix.trace (chartMatrix chart * cayleyMatrix x y z) =
      (advantageQuadratic chart n).evalReal x y z / cayleyDenom x y z := by
  have hd := (cayleyDenom_pos x y z).ne'
  rw [eq_div_iff hd]
  simp only [advantageQuadratic, AtlasQuadratic.sum3Q, RatQuadratic3.evalReal_add,
    RatQuadratic3.evalReal_scale, eval_numerator_eq, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Fin.sum_univ_three]
  push_cast
  simp only [c3NeighborQ_cast]
  simp
  ring

theorem Box.valid_imp_not_inCell (box : Box) (hvalid : box.Valid) {p : AtlasPose ℝ}
    (hp : p ∈ box.interval.toReal) (u : Fin 3 → ℝ) :
    ¬ InC3vCell u (chartMatrix box.chart * cayleyMatrix p.x p.y p.z) := by
  intro hcell
  have hlower := quadLower_le_eval box.interval (advantageQuadratic box.chart box.neighbor) hp
  have hvalidR : (0 : ℝ) < (box.lower : ℝ) := by exact_mod_cast hvalid
  have hpos : 0 < (advantageQuadratic box.chart box.neighbor).evalReal p.x p.y p.z := by
    unfold Box.lower at hvalidR
    linarith
  have htrace := trace_advantage_eq box.chart box.neighbor p.x p.y p.z
  have hle := hcell.1 (c3NeighborIdx box.neighbor)
  have : 0 < (advantageQuadratic box.chart box.neighbor).evalReal p.x p.y p.z /
      cayleyDenom p.x p.y p.z := div_pos hpos (cayleyDenom_pos _ _ _)
  linarith

end C3Prune

/-! ### The mirror prune -/

namespace MirrorPrune

abbrev Triangle := Fin 3 → Fin 3 → ℚ

/-- `(Q P)_k`. -/
def gApply (g : Fin 3) (P : Fin 3 → ℚ) (k : Fin 3) : ℚ := ∑ j, mirrorQQ g k j * P j

def dotQ (P Q : Fin 3 → ℚ) : ℚ := ∑ i, P i * Q i

/-- The coefficient of N_ik in b_cd. -/
def coeff (tri : Triangle) (g : Fin 3) (c d : Fin 3) (i k : Fin 3) : ℚ :=
  tri c i * gApply g (tri d) k + tri d i * gApply g (tri c) k -
    dotQ (tri c) (tri d) * (mirrorQQ g k i + if i = k then 1 else 0)

/-- b_cd as a quadratic in the Cayley coordinates. -/
def coefficientQuadratic (chart : ChartIndex) (tri : Triangle) (g : Fin 3) (c d : Fin 3) :
    RatQuadratic3 :=
  AtlasQuadratic.sum3Q fun i => AtlasQuadratic.sum3Q fun k =>
    RatQuadratic3.scale (coeff tri g c d i k) (AtlasQuadratic.numeratorQuadratic chart i k)

structure Box where
  interval : AtlasInterval ℚ
  chart : ChartIndex
  triangle : Triangle
  element : Fin 3
deriving DecidableEq

def Box.lower (box : Box) (c d : Fin 3) : ℚ :=
  quadLower box.interval (coefficientQuadratic box.chart box.triangle box.element c d)

/-- The pairs c ≤ d. -/
def pairs : List (Fin 3 × Fin 3) := [(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2)]

/-- `exact5d::HalfTurnPruneValid` with the exact table (allowance 0). -/
def Box.Valid (box : Box) : Prop := ∀ cd ∈ pairs, 0 < box.lower cd.1 cd.2

@[reducible] instance (box : Box) : Decidable box.Valid := by
  unfold Box.Valid
  infer_instance

/-- The view p = Σ λ_c P_c. -/
def viewOf (tri : Triangle) (lam : Fin 3 → ℝ) : Fin 3 → ℝ := fun i => ∑ c, lam c * (tri c i : ℝ)

/-- The algebra behind `sum_coefficients`, for arbitrary matrices. -/
theorem bernstein_identity (R G : Matrix (Fin 3) (Fin 3) ℝ) (P : Fin 3 → Fin 3 → ℝ)
    (lam : Fin 3 → ℝ) (D : ℝ) :
    ∑ c, ∑ d, lam c * lam d * ∑ i, ∑ k,
        (P c i * (∑ j, G k j * P d j) + P d i * (∑ j, G k j * P c j) -
          (∑ m, P c m * P d m) * (G k i + if i = k then 1 else 0)) * (D * R i k) =
      D * (2 * ∑ i, ∑ k, ∑ j, (∑ c, lam c * P c i) * R i k * G k j * (∑ c, lam c * P c j) -
        (∑ m, (∑ c, lam c * P c m) ^ 2) * (∑ i, ∑ k, R i k * G k i + ∑ i, R i i)) := by
  simp only [Fin.sum_univ_three, Fin.isValue]
  simp only [show (0 : Fin 3) = 0 from rfl, show (1 : Fin 3) = 1 from rfl, ite_eq_left, ite_eq_right,
    Fin.reduceEq, ite_true, ite_false]
  ring

theorem eval_coefficientQuadratic (chart : ChartIndex) (tri : Triangle) (g : Fin 3) (c d : Fin 3)
    (x y z : ℝ) :
    (coefficientQuadratic chart tri g c d).evalReal x y z =
      ∑ i, ∑ k, ((tri c i : ℝ) * (∑ j, mirrorQMat g k j * (tri d j : ℝ)) +
        (tri d i : ℝ) * (∑ j, mirrorQMat g k j * (tri c j : ℝ)) -
        (∑ m, (tri c m : ℝ) * (tri d m : ℝ)) * (mirrorQMat g k i + if i = k then 1 else 0)) *
          (cayleyDenom x y z * (chartMatrix chart * cayleyMatrix x y z) i k) := by
  simp only [coefficientQuadratic, AtlasQuadratic.sum3Q, RatQuadratic3.evalReal_add,
    RatQuadratic3.evalReal_scale, eval_numerator_eq]
  simp only [coeff, gApply, dotQ, Fin.sum_univ_three]
  push_cast
  simp only [mirrorQQ_cast]

theorem sum_coefficients (chart : ChartIndex) (tri : Triangle) (g : Fin 3) (lam : Fin 3 → ℝ)
    (x y z : ℝ) :
    ∑ c, ∑ d, lam c * lam d * (coefficientQuadratic chart tri g c d).evalReal x y z =
      cayleyDenom x y z * (2 * ∑ i, ∑ k, ∑ j, viewOf tri lam i *
          (chartMatrix chart * cayleyMatrix x y z) i k * mirrorQMat g k j * viewOf tri lam j -
        (∑ m, viewOf tri lam m ^ 2) *
          (∑ i, ∑ k, (chartMatrix chart * cayleyMatrix x y z) i k * mirrorQMat g k i +
            ∑ i, (chartMatrix chart * cayleyMatrix x y z) i i)) := by
  have h := bernstein_identity (chartMatrix chart * cayleyMatrix x y z) (mirrorQMat g)
    (fun c i => (tri c i : ℝ)) lam (cayleyDenom x y z)
  simp only [eval_coefficientQuadratic, viewOf]
  exact h

theorem coefficient_symm (chart : ChartIndex) (tri : Triangle) (g : Fin 3) (c d : Fin 3)
    (x y z : ℝ) : (coefficientQuadratic chart tri g c d).evalReal x y z =
      (coefficientQuadratic chart tri g d c).evalReal x y z := by
  rw [eval_coefficientQuadratic, eval_coefficientQuadratic]
  congr 1
  ext i
  congr 1
  ext k
  congr 1
  rw [show (∑ m, (tri c m : ℝ) * (tri d m : ℝ)) = ∑ m, (tri d m : ℝ) * (tri c m : ℝ) from
    Finset.sum_congr rfl fun m _ => mul_comm _ _]
  ring

theorem trace_halfTurn_mul (u : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix.trace (halfTurnMat u * M) =
      2 * (∑ i, ∑ j, u i * M i j * u j) / (∑ k, u k ^ 2) - Matrix.trace M := by
  have h : ∀ i j : Fin 3, halfTurnMat u i j =
      2 * u i * u j / (∑ k, u k ^ 2) - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j := by
    intro i j
    simp [halfTurnMat, Matrix.one_apply]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, h, sub_mul, Finset.sum_sub_distrib]
  have h1 : ∀ i, ∑ j, (1 : Matrix (Fin 3) (Fin 3) ℝ) i j * M j i = M i i := by
    intro i
    simp [Matrix.one_apply]
  simp only [h1]
  congr 1
  simp only [Fin.sum_univ_three]
  ring

theorem quad_pos (B : Fin 3 → Fin 3 → ℝ) (hB : ∀ c d, 0 < B c d) (lam : Fin 3 → ℝ)
    (hlam : ∀ c, 0 ≤ lam c) (hpos : 0 < ∑ c, lam c) :
    0 < ∑ c, ∑ d, lam c * lam d * B c d := by
  obtain ⟨c0, hc0⟩ : ∃ c, 0 < lam c := by
    by_contra h
    push Not at h
    have : ∑ c, lam c ≤ 0 := Finset.sum_nonpos fun c _ => h c
    linarith
  have hnn : ∀ c d, 0 ≤ lam c * lam d * B c d :=
    fun c d => mul_nonneg (mul_nonneg (hlam c) (hlam d)) (hB c d).le
  calc (0 : ℝ) < lam c0 * lam c0 * B c0 c0 := mul_pos (mul_pos hc0 hc0) (hB c0 c0)
    _ ≤ ∑ d, lam c0 * lam d * B c0 d :=
        Finset.single_le_sum (fun d _ => hnn c0 d) (Finset.mem_univ c0)
    _ ≤ ∑ c, ∑ d, lam c * lam d * B c d :=
        Finset.single_le_sum (f := fun c => ∑ d, lam c * lam d * B c d)
          (fun c _ => Finset.sum_nonneg fun d _ => hnn c d) (Finset.mem_univ c0)

theorem pairs_cover : ∀ c d : Fin 3, (c, d) ∈ pairs ∨ (d, c) ∈ pairs := by decide

/-- If the λ-form is positive, the mirror tie Q_g at u increases the trace. -/
theorem not_mirror_le_of_pos (u : Fin 3 → ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ) (g : Fin 3)
    (hinner : 0 < 2 * ∑ i, ∑ k, ∑ j, u i * R i k * mirrorQMat g k j * u j -
      (∑ m, u m ^ 2) * (∑ i, ∑ k, R i k * mirrorQMat g k i + ∑ i, R i i)) :
    ¬ Matrix.trace (halfTurnMat u * R * mirrorQMat g) ≤ Matrix.trace R := by
  intro hcellg
  have hnorm : 0 < ∑ m, u m ^ 2 := by
    rcases (Finset.sum_nonneg fun m (_ : m ∈ Finset.univ) => sq_nonneg (u m)).lt_or_eq with h | h
    · exact h
    · exfalso
      have hz : ∀ m, u m = 0 := fun m =>
        pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
          ((Finset.sum_eq_zero_iff_of_nonneg (fun m _ => sq_nonneg (u m))).mp h.symm m
            (Finset.mem_univ _))
      simp [hz] at hinner
  rw [Matrix.mul_assoc, trace_halfTurn_mul] at hcellg
  have hRG : ∑ i, ∑ j, u i * (R * mirrorQMat g) i j * u j =
      ∑ i, ∑ k, ∑ j, u i * R i k * mirrorQMat g k j * u j := by
    simp only [Matrix.mul_apply, Fin.sum_univ_three]
    ring
  have htrRG : Matrix.trace (R * mirrorQMat g) = ∑ i, ∑ k, R i k * mirrorQMat g k i := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  have htrR : Matrix.trace R = ∑ i, R i i := by simp [Matrix.trace]
  rw [hRG, htrRG, htrR] at hcellg
  rw [div_sub' (ne_of_gt hnorm), div_le_iff₀ hnorm] at hcellg
  nlinarith [hcellg, hinner, hnorm]

/-- A valid box: for every view p = Σ λ_c P_c (λ ≥ 0, not all 0) and every
pose of the box, R is not in the C3v cell at p. -/
theorem Box.valid_imp_not_inCell (box : Box) (hvalid : box.Valid) {p : AtlasPose ℝ}
    (hp : p ∈ box.interval.toReal) (lam : Fin 3 → ℝ) (hlam : ∀ c, 0 ≤ lam c)
    (hpos : 0 < ∑ c, lam c) :
    ¬ InC3vCell (viewOf box.triangle lam) (chartMatrix box.chart * cayleyMatrix p.x p.y p.z) := by
  have hle : ∀ cd ∈ pairs, 0 <
      (coefficientQuadratic box.chart box.triangle box.element cd.1 cd.2).evalReal p.x p.y p.z := by
    intro cd hcd
    have hl := quadLower_le_eval box.interval
      (coefficientQuadratic box.chart box.triangle box.element cd.1 cd.2) hp
    have hv : (0 : ℝ) < (box.lower cd.1 cd.2 : ℝ) := by exact_mod_cast hvalid cd hcd
    unfold Box.lower at hv
    linarith
  have hB : ∀ c d : Fin 3, 0 <
      (coefficientQuadratic box.chart box.triangle box.element c d).evalReal p.x p.y p.z := by
    intro c d
    rcases pairs_cover c d with h | h
    · exact hle (c, d) h
    · rw [coefficient_symm]
      exact hle (d, c) h
  have hsum := quad_pos _ hB lam hlam hpos
  rw [sum_coefficients] at hsum
  intro hcell
  apply not_mirror_le_of_pos _ _ box.element _ (hcell.2 box.element)
  have hD := cayleyDenom_pos p.x p.y p.z
  by_contra h
  push Not at h
  have := mul_le_mul_of_nonneg_left h hD.le
  linarith

end MirrorPrune

/-! ### The cell at projective views -/

theorem inC3vCell_smul {u : Fin 3 → ℝ} {κ : ℝ} (hκ : κ ≠ 0) {R : Matrix (Fin 3) (Fin 3) ℝ}
    (h : InC3vCell (κ • u) R) : InC3vCell u R := by
  refine ⟨h.1, fun i => ?_⟩
  have := h.2 i
  rwa [halfTurnMat_smul κ hκ] at this

end Septopert
