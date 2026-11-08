module

public import SeptopertM12.Model
public import Pipeline.ArcCapAxis
public import Pipeline.ArcCapDecode
public import Pipeline.IdCap

@[expose] public section

/-!
# The axis cap of SeptopertM12 (cap 2)

Near the 3-fold axis view (1, 1, 1) the rotations of SeptopertM12 are not closed by a width either. The
certificate is the U cap of `Pipeline.ArcCap` on the four sides of the square of views
u = X − a E₁ − b E₂, |a|, |b| ≤ 1/16, in the axis frame E₁ = (1, −1, 0), E₂ = (1/2, 1/2, −1),
X = (1, 1, 1) (orthogonal, squared lengths 2, 3/2, 3), with the Cayley weights (1/2, 2/3, 1/3), so that
w = (w·E₁) E₁/2 + (w·E₂) (2/3) E₂ + (w·X) X/3 has apex coordinates exactly w·E₁, w·E₂, w·X; the
parameters μ₀ = 1/16, R = 2, S = 16, R_c = 1, S_c = 16, no wedge. The certificate is exported by
`h12cap/exportaxis.sh` (`capcert-m12 --frame axis --sides 0123 --export`).

`axis_not_rupert`: a checked certificate rules out every pose (any offset) with view in the
square `InAxis` and a rotation within 1/46 in Cayley coordinates.
-/

namespace SeptopertM12
open Noperts

open Noperts.Pipeline
open Noperts.Pipeline.ArcCap
open Noperts.Pipeline.KCap

/-- The parameters of the axis cap (only the U cap's are used). -/
def axisParams : ArcCap.Params where
  mu0 := 1 / 16
  R := 2
  S := 16
  Rc := 1
  Sc := 16
  nu0 := 0
  R1 := 0
  R2 := 0
  R3 := 0
  Z := 0
  tstar := 0
  zh := 0
  zmid := 0
  bmid := 0
  tsplit := 0
  tend := 0
  f0c := 0
  f0d := 0
  f1c := 0
  f1d := 0
  wedge := false

theorem axisParams_ok : axisParams.Ok := by norm_num [ArcCap.Params.Ok, axisParams]

/-- The axis frame, with the Cayley weights (1/2, 2/3, 1/3). -/
def axisFrame : ArcCap.Frame ℚ := { E1 := ![1, -1, 0], E2 := ![1 / 2, 1 / 2, -1], X := ![1, 1, 1], k1 := 1 / 2, k2 := 2 / 3, k3 := 1 / 3 }

/-- The solid's vertices. -/
def axisVerts : Array (KCap.KVec ℚ) := Array.ofFn fun i : Fin 7 => fun j => vertexQ i j

def axisCertOk (c : ArcCap.Cert) : Bool := certCheckOn axisCharts axisVerts axisFrame axisParams c

def axisCertOkPar (c : ArcCap.Cert) : Bool := certCheckParOn axisCharts axisVerts axisFrame axisParams c

theorem axisCertOk_of_par (c : ArcCap.Cert) (h : axisCertOkPar c = true) : axisCertOk c = true :=
  certCheckOn_of_par _ _ _ _ c h

theorem kval_q (v : KCap.KVec ℚ) (i : Fin 3) : KCap.PVec.kval v i = (v i : ℝ) := rfl

theorem axisFrame_ok : FrameOkG axisFrame 2 (3 / 2) 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, rfl, rfl, rfl⟩ <;>
    simp [axisFrame, rdot, kval_q] <;> norm_num

theorem hull_axisVerts : hull axisVerts = solid := by
  unfold hull solid poly Polyhedron.hull
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq, List.mem_map, Array.mem_toList_iff, axisVerts, Array.mem_ofFn]
  constructor
  · rintro ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩, rfl⟩
    refine ⟨i, ?_⟩
    ext j
    simp [toR3, Cap.toEuc, kval_q]
  · rintro ⟨i, rfl⟩
    refine ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩, ?_⟩
    ext j
    simp [toR3, Cap.toEuc, kval_q]

/-- The views of the square |a|, |b| ≤ 1/16 of the axis frame, u = X − a E₁ − b E₂ up to scale:
v·X > 0, |v·(1, −1, 0)| ≤ v·X / 24 and |v·(1, 1, −2)| ≤ v·X / 16. -/
def InAxis (v : Fin 3 → ℝ) : Prop :=
  0 < v 0 + v 1 + v 2 ∧ 24 * |v 0 - v 1| ≤ v 0 + v 1 + v 2 ∧ 16 * |v 0 + v 1 - 2 * v 2| ≤ v 0 + v 1 + v 2

theorem inAxis_square {v : Fin 3 → ℝ} (h : InAxis v) : InSquare axisFrame 2 (3 / 2) 3 (((1 / 16 : ℚ)) : ℝ) v := by
  obtain ⟨h0, h1, h2⟩ := h
  have e1 : rdot v (KCap.PVec.kval axisFrame.E1) = v 0 - v 1 := by
    simp [axisFrame, rdot, kval_q]; ring
  have e2 : rdot v (KCap.PVec.kval axisFrame.E2) = (v 0 + v 1 - 2 * v 2) / 2 := by
    simp [axisFrame, rdot, kval_q]; ring
  have ex : rdot v (KCap.PVec.kval axisFrame.X) = v 0 + v 1 + v 2 := by
    simp [axisFrame, rdot, kval_q]
  refine ⟨by rw [ex]; exact h0, ?_, ?_⟩
  · rw [e1, ex]; push_cast; linarith
  · rw [e2, ex, abs_div]; push_cast
    rw [abs_two]; linarith

/-- The claim of the axis cap. -/
theorem axis_not_rupert (c : ArcCap.Cert) (hc : axisCertOk c = true) (p : MatrixPose) (hv : InAxis p.view)
    (w : Fin 3 → ℝ) (hR : p.relativeRotation = cayleyMatrix (w 0) (w 1) (w 2))
    (hw : rdot w w ≤ (1 / 46) ^ 2) : ¬ RupertPose p solid := by
  rw [← hull_axisVerts]
  refine square_not_rupert (n1 := 2) (n2 := 3 / 2) (nx := 3) (r := 1 / 46) axisParams_ok hc
    (by norm_num [axisParams]) (by norm_num [axisParams]) rfl (by norm_num [axisParams])
    (by norm_num [axisParams]) axisFrame_ok ?_ ?_ ?_ p (inAxis_square hv) w hR hw <;>
    norm_num [axisParams]

/-- The claim of the axis cap, for the solution tree. -/
def AxisHolds : Prop :=
  ∀ (p : MatrixPose), InAxis p.view → ∀ w : Fin 3 → ℝ,
    p.relativeRotation = cayleyMatrix (w 0) (w 1) (w 2) → rdot w w ≤ (1 / 46) ^ 2 → ¬ RupertPose p solid

theorem axisHolds_of_cert (c : ArcCap.Cert) (hc : axisCertOk c = true) : AxisHolds :=
  fun p hv w hR hw => axis_not_rupert c hc p hv w hR hw

end SeptopertM12

end
