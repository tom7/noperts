module

public import Pipeline.OctaView
public import Pipeline.AtlasQuadratic
public import Pipeline.AtlasInterval

@[expose] public section

/-!
# The octahedral cell prune

A box of an atlas chart is pruned when a rotation g of O (other than the
identity) increases the trace of the relative rotation over the whole box:
then no pose of the box lies in the O cell (`InOctaCell`). With
`R = chart · cayley(x, y, z)` and `D` the Cayley denominator,
`D (tr(R g) − tr R) = Σ_ij (g_ji − δ_ij) Num_ij(x, y, z)`, a quadratic in the
Cayley coordinates with exact (integer) coefficients, bounded below by
Bernstein or tight-ball bounds. The neighbors are the 23 nontrivial
rotations: neighbor `n` is element `n + 1` of O, the order of the C++
search's table (`search/sc/symmetry_neighbors.h`, `exact5d::IcoPruneValid`).
-/

namespace Noperts.Pipeline

open Noperts.Atlas

open scoped Matrix

namespace AtlasOctaPrune

open Noperts.Checker
open CayleyAtlas

/-- Neighbor `n`: the rotation `n + 1` of O. -/
def neighbor (n : Fin 23) : OctaIndex := ⟨n.val + 1, by omega⟩

/-- `Σ_ij (g_ji − δ_ij) Num_ij`: the denominator-cleared trace advantage. -/
def advantageQuadratic (chart : ChartIndex) (n : Fin 23) : RatQuadratic3 :=
  AtlasQuadratic.sum3Q fun i => AtlasQuadratic.sum3Q fun j =>
    RatQuadratic3.scale (octaMatrixQ (neighbor n) j i - if i = j then 1 else 0)
      (AtlasQuadratic.numeratorQuadratic chart i j)

structure Box where
  interval : AtlasInterval ℚ
  chart : ChartIndex
  neighbor : Fin 23
deriving DecidableEq

def Box.variableBalls (box : Box) : Fin 3 → RatBall :=
  ![box.interval.coordinateBall 2,
    box.interval.coordinateBall 3,
    box.interval.coordinateBall 4]

def Box.tightLower (box : Box) : ℚ :=
  let ball := RatQuadratic3.evalTightBall box.variableBalls
    (advantageQuadratic box.chart box.neighbor)
  ball.center - ball.radius

def Box.lower (box : Box) : ℚ :=
  max box.tightLower
    (QuadraticBernstein.lower box.variableBalls
      (advantageQuadratic box.chart box.neighbor))

/-- The advantage is positive over the box (exact neighbors: no allowance). -/
def Box.Valid (box : Box) : Prop := 0 < box.lower

@[reducible] instance (box : Box) : Decidable box.Valid := by
  unfold Box.Valid
  infer_instance

theorem Box.lower_le_eval (box : Box) {p : AtlasPose ℝ}
    (hp : p ∈ box.interval.toReal) :
    (box.lower : ℝ) ≤
      (advantageQuadratic box.chart box.neighbor).evalReal p.x p.y p.z := by
  have hvars : ∀ i : Fin 3,
      (box.variableBalls i).Holds (![p.x, p.y, p.z] i) := by
    intro i
    fin_cases i
    · exact box.interval.coordinateBall_holds hp 2
    · exact box.interval.coordinateBall_holds hp 3
    · exact box.interval.coordinateBall_holds hp 4
  have htight := RatBall.lower_le_of_holds
    (RatQuadratic3.evalTightBall_holds hvars
      (advantageQuadratic box.chart box.neighbor))
  have hbernstein := QuadraticBernstein.lower_le_evalReal hvars
    (advantageQuadratic box.chart box.neighbor)
  push_cast at htight hbernstein
  unfold Box.lower Box.tightLower
  push_cast
  exact max_le htight hbernstein

theorem eval_numerator_eq (chart : ChartIndex) (i j : Fin 3) (x y z : ℝ) :
    (AtlasQuadratic.numeratorQuadratic chart i j).evalReal x y z =
      cayleyDenom x y z * (chartMatrix chart * cayleyMatrix x y z) i j := by
  rw [AtlasQuadratic.eval_numeratorQuadratic, cayleyNumeratorMatrix_eq_denom_smul,
    Matrix.mul_smul]
  simp

theorem trace_advantage_eq (chart : ChartIndex) (n : Fin 23) (x y z : ℝ) :
    Matrix.trace ((chartMatrix chart * cayleyMatrix x y z) * octaMatrix (neighbor n)) -
        Matrix.trace (chartMatrix chart * cayleyMatrix x y z) =
      (advantageQuadratic chart n).evalReal x y z / cayleyDenom x y z := by
  have hd := (cayleyDenom_pos x y z).ne'
  rw [eq_div_iff hd]
  have hq : ∀ i j, ((octaMatrixQ (neighbor n) j i : ℚ) : ℝ) = octaMatrix (neighbor n) j i := by
    intro i j
    rw [← octaMatrixQ_map]
    rfl
  simp only [advantageQuadratic, AtlasQuadratic.sum3Q, RatQuadratic3.evalReal_add,
    RatQuadratic3.evalReal_scale, eval_numerator_eq, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Fin.sum_univ_three]
  push_cast
  simp only [hq]
  simp
  ring

theorem Box.valid_imp_not_inOctaCell
    (box : Box) (hvalid : box.Valid) {p : AtlasPose ℝ}
    (hp : p ∈ box.interval.toReal) :
    ¬ InOctaCell (chartMatrix box.chart * cayleyMatrix p.x p.y p.z) := by
  intro hcell
  have hlower := box.lower_le_eval hp
  have hvalidReal : (0 : ℝ) < (box.lower : ℝ) := by exact_mod_cast hvalid
  have htrace := trace_advantage_eq box.chart box.neighbor p.x p.y p.z
  have hle := hcell (AtlasOctaPrune.neighbor box.neighbor)
  have : 0 < (advantageQuadratic box.chart box.neighbor).evalReal p.x p.y p.z /
      cayleyDenom p.x p.y p.z :=
    div_pos (lt_of_lt_of_le hvalidReal hlower) (cayleyDenom_pos _ _ _)
  linarith

end AtlasOctaPrune

end Noperts.Pipeline

end
