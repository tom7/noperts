module

public import Septopert.Model
public import Pipeline.ArcCapP
public import Pipeline.ArcCapDecode
public import Pipeline.IdCap

@[expose] public section

/-!
# The P cap of Septopert (cap 3)

Near the view P = (2, 1, 0) (face 024 edge-on, with the apex face 162 edge-on as well) and along the
strip of face 024's circle of views, the rotations of Septopert are not closed by a width either. The certificate
is the P cap of `Pipeline.ArcCapP`: the U charts on the four sides of the square of views
u = X − a E₁ − b E₂, |a|, |b| ≤ 1/8, in the frame E₁ = (1/2, −1, −5/2) (= −T/2 for the circle's tangent
T = (−1, 2, 5)), E₂ = (1, −2, 1) (the normal of face 024), X = (2, 1, 0) (orthogonal, squared lengths
15/2, 6, 5), with the rotation basis W₁ = (7/10)(0, −1, 1), W₂ = (2/5)(2, −1, −1), W₃ = (4/7)(1, 1, 1) (the
flex plane perpendicular to (1, 1, 1) and its normal; orthogonal, squared lengths 49/50, 24/25, 48/49), with
μ₀ = 1/8, R = 1/2, S = 2, R_c = 1/4, S_c = 2; and the wedge along the circle (ν₀ = 1, t ≤ 1/8,
R₁ = R₂ = 2, R₃ = 16, Z = 8), to which the boxes of side 0 inside it are left. The certificate is exported
from the leaf lists of `capcert-m7 --frame P` by `h12cap/leaf2cert.py (Septopert: m7cap/p3cert.sh)`.

`pcap_not_rupert`: a checked certificate rules out every pose (any offset) with view in the region
`InP` and a rotation within 1/46 in Cayley coordinates.
-/

namespace Septopert
open Noperts

open Noperts.Pipeline
open Noperts.Pipeline.ArcCap
open Noperts.Pipeline.KCap

/-- The parameters of the P cap. -/
def pParams : ArcCap.Params where
  mu0 := 1 / 8
  R := 1 / 2
  S := 2
  Rc := 1 / 4
  Sc := 2
  nu0 := 1
  R1 := 2
  R2 := 2
  R3 := 16
  Z := 8
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
  thi := 1 / 8
  pwp := true

theorem pParams_ok : pParams.Ok := by norm_num [ArcCap.Params.Ok, pParams]

/-- The frame of the P cap: the view frame and the rotation basis. -/
def pFrame : ArcCap.Frame ℚ :=
  { E1 := ![1 / 2, -1, -5 / 2], E2 := ![1, -2, 1], X := ![2, 1, 0], k1 := 1, k2 := 1, k3 := 1,
    W1 := ![0, -7 / 10, 7 / 10], W2 := ![4 / 5, -2 / 5, -2 / 5], W3 := ![4 / 7, 4 / 7, 4 / 7] }

/-- The solid's vertices. -/
def pVerts : Array (KCap.KVec ℚ) := Array.ofFn fun i : Fin 7 => fun j => vertexQ i j

def pcapCertOk (c : ArcCap.Cert) : Bool := certCheckOn pCharts pVerts pFrame pParams c

def pcapCertOkPar (c : ArcCap.Cert) : Bool := certCheckParOn pCharts pVerts pFrame pParams c

theorem pcapCertOk_of_par (c : ArcCap.Cert) (h : pcapCertOkPar c = true) : pcapCertOk c = true :=
  certCheckOn_of_par _ _ _ _ c h

theorem kval_q (v : KCap.KVec ℚ) (i : Fin 3) : KCap.PVec.kval v i = (v i : ℝ) := rfl

theorem pFrame_ok : FrameOkP pFrame (15 / 2) 6 5 (49 / 50) (24 / 25) (48 / 49) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_,
    by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩ <;>
    simp [pFrame, rdot, kval_q] <;> norm_num

theorem hull_pVerts : hull pVerts = solid := by
  unfold hull solid poly Polyhedron.hull
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq, List.mem_map, Array.mem_toList_iff, pVerts, Array.mem_ofFn]
  constructor
  · rintro ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩, rfl⟩
    refine ⟨i, ?_⟩
    ext j
    simp [toR3, Cap.toEuc, kval_q]
  · rintro ⟨i, rfl⟩
    refine ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩, ?_⟩
    ext j
    simp [toR3, Cap.toEuc, kval_q]

/-- The region R3 of views, u = X − a E₁ − b E₂ up to scale, |a|, |b| ≤ 1/8: v·X > 0, |v·(−1, 2, 5)| ≤
(3/8) v·X and |v·(1, −2, 1)| ≤ (3/20) v·X, with X = (2, 1, 0). -/
def InP (v : Fin 3 → ℝ) : Prop :=
  0 < 2 * v 0 + v 1 ∧ 8 * |-v 0 + 2 * v 1 + 5 * v 2| ≤ 3 * (2 * v 0 + v 1) ∧
    20 * |v 0 - 2 * v 1 + v 2| ≤ 3 * (2 * v 0 + v 1)

theorem inP_square {v : Fin 3 → ℝ} (h : InP v) : InSquare pFrame (15 / 2) 6 5 (((1 / 8 : ℚ)) : ℝ) v := by
  obtain ⟨h0, h1, h2⟩ := h
  have e1 : rdot v (KCap.PVec.kval pFrame.E1) = -(-v 0 + 2 * v 1 + 5 * v 2) / 2 := by
    simp [pFrame, rdot, kval_q]; ring
  have e2 : rdot v (KCap.PVec.kval pFrame.E2) = v 0 - 2 * v 1 + v 2 := by
    simp [pFrame, rdot, kval_q]; ring
  have ex : rdot v (KCap.PVec.kval pFrame.X) = 2 * v 0 + v 1 := by
    simp [pFrame, rdot, kval_q]; ring
  refine ⟨by rw [ex]; exact h0, ?_, ?_⟩
  · rw [e1, ex, abs_div, abs_neg, abs_two]; push_cast; linarith
  · rw [e2, ex]; push_cast; linarith

/-- The claim of the P cap. -/
theorem pcap_not_rupert (c : ArcCap.Cert) (hc : pcapCertOk c = true) (p : MatrixPose) (hv : InP p.view)
    (w : Fin 3 → ℝ) (hR : p.relativeRotation = cayleyMatrix (w 0) (w 1) (w 2))
    (hw : rdot w w ≤ (1 / 46) ^ 2) : ¬ RupertPose p solid := by
  rw [← hull_pVerts]
  refine pcapGen_not_rupert (n1 := 15 / 2) (n2 := 6) (nx := 5) (m1 := 49 / 50) (m2 := 24 / 25) (m3 := 48 / 49)
    (r := 1 / 46) pParams_ok hc (by norm_num [pParams]) (by norm_num [pParams]) (by norm_num [pParams])
    (by norm_num [pParams]) (by norm_num [pParams]) (by norm_num [pParams]) (by norm_num [pParams])
    (by norm_num [pParams]) (by norm_num [pParams]) pFrame_ok ?_ ?_ ?_ p (inP_square hv) w hR hw <;>
    norm_num [pParams]


/-- The stand-in piece of cap 3 in `search/h12/arc-cap.txt` (`piece 2 1 0 -15/16 65/32 -1 17/16 -63/32 1 -9/10 41/20 5
7/4 -13/8 -5`: n₀·v > 0 and nᵢ·v ≥ 0): v·X > 0, |v·N| ≤ v·X / 32 and −v·X / 20 ≤ v·T ≤ (3/8) v·X for
N = (1, −2, 1), T = (−1, 2, 5), X = (2, 1, 0). -/
def InPiece3 (v : Fin 3 → ℝ) : Prop :=
  0 < 2 * v 0 + 1 * v 1 + 0 * v 2 ∧
    0 ≤ -15 / 16 * v 0 + 65 / 32 * v 1 + -1 * v 2 ∧ 0 ≤ 17 / 16 * v 0 + -63 / 32 * v 1 + 1 * v 2 ∧
    0 ≤ -9 / 10 * v 0 + 41 / 20 * v 1 + 5 * v 2 ∧ 0 ≤ 7 / 4 * v 0 + -13 / 8 * v 1 + -5 * v 2

/-- The piece lies in the region R3. -/
theorem inP_of_piece {v : Fin 3 → ℝ} (h : InPiece3 v) : InP v := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  refine ⟨by linarith, ?_, ?_⟩
  · rw [← abs_neg, show -(-v 0 + 2 * v 1 + 5 * v 2) = v 0 - 2 * v 1 - 5 * v 2 by ring]
    have : |v 0 - 2 * v 1 - 5 * v 2| ≤ 3 / 8 * (2 * v 0 + v 1) := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  · have : |v 0 - 2 * v 1 + v 2| ≤ 3 / 20 * (2 * v 0 + v 1) := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith

/-- The claim of the P cap for the stand-in piece, for a view in the piece: no pose with that view and a
rotation within 1/46 is Rupert. -/
theorem pcap_piece_not_rupert (c : ArcCap.Cert) (hc : pcapCertOk c = true) (p : MatrixPose)
    (hv : InPiece3 p.view) (w : Fin 3 → ℝ) (hR : p.relativeRotation = cayleyMatrix (w 0) (w 1) (w 2))
    (hw : rdot w w ≤ (1 / 46) ^ 2) : ¬ RupertPose p solid :=
  pcap_not_rupert c hc p (inP_of_piece hv) w hR hw

/-- The claim of the P cap, for the solution tree. -/
def PHolds : Prop :=
  ∀ (p : MatrixPose), InP p.view → ∀ w : Fin 3 → ℝ,
    p.relativeRotation = cayleyMatrix (w 0) (w 1) (w 2) → rdot w w ≤ (1 / 46) ^ 2 → ¬ RupertPose p solid

theorem pHolds_of_cert (c : ArcCap.Cert) (hc : pcapCertOk c = true) : PHolds :=
  fun p hv w hR hw => pcap_not_rupert c hc p hv w hR hw

end Septopert

end
