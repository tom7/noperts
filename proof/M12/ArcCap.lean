module

public import M12.Model
public import M12.ArcClaim
public import Pipeline.IdCap

@[expose] public section

/-!
# The arc cap of M12 (cap 1: U and the arc)

`arcCertOk`: an arc cap certificate (`Pipeline.ArcCapDecode`) over ℚ for M12's vertices, the
apex frame E₁ = (−1, 2, 2), E₂ = (2, −1, 2), X = (2, 2, −1) (the cube corner at v₆: v₀ − v₆, v₁ − v₆,
v₂ − v₆ = (6/16) E₁, E₂, X) and `m12Params`. The certificate is exported by
`h12cap/exportm12.sh` (`capcert-m12 --export`).

`arc_not_rupert`: a checked certificate rules out every pose (any offset) with view in the
polygon `InArc` (the half square and the wedge) and a rotation within 1/46 in Cayley coordinates.
-/

namespace M12
open Noperts

open Noperts.Pipeline
open Noperts.Pipeline.ArcCap
open Noperts.Pipeline.KCap

/-- The apex frame (as for M18). -/
def apexFrame : ArcCap.Frame ℚ := ⟨![-1, 2, 2], ![2, -1, 2], ![2, 2, -1], 1 / 3, 1 / 3, 1 / 3⟩

/-- The solid's vertices. -/
def arcVerts : Array (KCap.KVec ℚ) := Array.ofFn fun i : Fin 7 => fun j => vertexQ i j

def arcCertOk (c : ArcCap.Cert) : Bool := certCheck arcVerts apexFrame m12Params c

def arcCertOkPar (c : ArcCap.Cert) : Bool := certCheckPar arcVerts apexFrame m12Params c

theorem arcCertOk_of_par (c : ArcCap.Cert) (h : arcCertOkPar c = true) : arcCertOk c = true :=
  certCheck_of_par _ _ _ c h

theorem kval_q (v : KCap.KVec ℚ) (i : Fin 3) : KCap.PVec.kval v i = (v i : ℝ) := rfl

theorem apexFrame_ok : FrameOk apexFrame := by
  constructor <;> simp [apexFrame, rdot, kval_q] <;> norm_num

theorem hull_arcVerts : hull arcVerts = solid := by
  unfold hull solid poly Polyhedron.hull
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq, List.mem_map, Array.mem_toList_iff, arcVerts, Array.mem_ofFn]
  constructor
  · rintro ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩, rfl⟩
    refine ⟨i, ?_⟩
    ext j
    simp [toR3, Cap.toEuc, kval_q]
  · rintro ⟨i, rfl⟩
    refine ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩, ?_⟩
    ext j
    simp [toR3, Cap.toEuc, kval_q]

/-- The view polygon: `InPolygon` for the apex frame. -/
abbrev InArc (v : Fin 3 → ℝ) : Prop := InPolygon apexFrame v

/-- **The arc cap**: a checked certificate rules out every pose (any offset) with view in the
polygon and relative rotation the Cayley rotation of a vector of length at most 1/46. -/
theorem arc_not_rupert (c : ArcCap.Cert) (hc : arcCertOk c = true) (p : MatrixPose) (hv : InArc p.view)
    (w : Fin 3 → ℝ) (hR : p.relativeRotation = cayleyMatrix (w 0) (w 1) (w 2))
    (hw : rdot w w ≤ (1 / 46) ^ 2) : ¬ RupertPose p solid := by
  rw [← hull_arcVerts]
  exact arc_not_rupert_of_norm_m12 hc apexFrame_ok p hv w hR hw

/-- The claim of the arc cap. -/
def ArcHolds : Prop :=
  ∀ (p : MatrixPose), InArc p.view → ∀ w : Fin 3 → ℝ,
    p.relativeRotation = cayleyMatrix (w 0) (w 1) (w 2) → rdot w w ≤ (1 / 46) ^ 2 → ¬ RupertPose p solid

theorem arcHolds_of_cert (c : ArcCap.Cert) (hc : arcCertOk c = true) : ArcHolds :=
  fun p hv w hR hw => arc_not_rupert c hc p hv w hR hw

end M12

end
