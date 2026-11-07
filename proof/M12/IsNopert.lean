module

public import M12.IsNotRupert
public import M12.PCap
public import Nopert

@[expose] public section

/-!
# M12 is a nopert, given valid certificate data

M12 is the convex polyhedron whose vertices are the permutations of (-11, 7, 7)/16 and
(12, 3, 3)/16, and (-5, -5, -5)/16 (`M12.vertexQ`, `M12.verts` its vertex set, `M12.solid` its
hull). As for the SeptopertM18 (`SeptopertM18.lean`), the Lean proof `isNopert_of_certificatesValid`
shows that valid certificate data give `IsNopert verts`, and the program `constructM12` checks the
data natively (the tables and the cap, arc cap and axis cap certificates).

Cap 3 (`PCapClaim`, the strip of views around (2, 1, 0) with rotations within 1/46) is certified by
the P cap certificate of `M12.PCap`: `PCapOk` says that `pcapCertOk` accepts some certificate.
-/

namespace M12

open Noperts Noperts.Pipeline

/-- The P cap certificate (cap 3) is accepted by the checker. -/
def PCapOk : Prop := ∃ c : ArcCap.Cert, pcapCertOk c = true

/-- The strip `PieceInP` of cap 3 is the piece `InPiece3` of the P cap. -/
theorem inPiece3_of_pieceInP {v : Fin 3 → ℝ} (h : PieceInP v) : InPiece3 v := by
  obtain ⟨h0, h1⟩ := h
  have key : ∀ n ∈ pNs, 0 ≤ dotR n v := h1
  simp only [pNs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at key
  obtain ⟨k1, k2, k3, k4⟩ := key
  simp only [dotR, pN0] at h0 k1 k2 k3 k4
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at h0 k1 k2 k3 k4
  refine ⟨by norm_num at h0 ⊢; linarith, ?_, ?_, ?_, ?_⟩ <;> norm_num at * <;> linarith

/-- Cap 3's claim follows from an accepted P cap certificate. -/
theorem pCapClaim_of_ok (h : PCapOk) : PCapClaim := by
  obtain ⟨c, hc⟩ := h
  intro p hv w hR hw
  exact pcap_piece_not_rupert c hc p (inPiece3_of_pieceInP hv) w hR hw

/-- The certificate data is valid: four solution tables (one per chart, each passing the validity
check), the cap certificate at the mirror normal, the arc cap certificate (cap 1), the axis cap
certificate (cap 2), and the P cap certificate (cap 3). -/
def CertificatesValid : Prop :=
  ∃ table : CayleyAtlas.ChartIndex → SolutionTree.Table,
    (∀ chart, (table chart).chart = chart) ∧
    (∀ chart, (table chart).Valid) ∧
    SolutionTree.CapOk ∧
    SolutionTree.ArcOk ∧
    SolutionTree.AxisOk ∧
    PCapOk

/-- If the certificate data is valid, M12 is not Rupert. -/
theorem not_isRupert_of_certificatesValid (h : CertificatesValid) : ¬ IsRupert verts := by
  obtain ⟨table, hchart, hvalid, hcap, harc, haxis, hpc⟩ := h
  exact not_rupert_of_valid_tables table hchart hvalid hcap harc haxis (pCapClaim_of_ok hpc)

/-- M12 is a genuine solid: its vertices 0, 1, 2 and 6 span a tetrahedron. -/
theorem not_coplanar_verts : ¬ Coplanar ℝ (verts : Set ℝ³) := by
  refine not_coplanar_of_det3_ne_zero
    (a := toR3 (vertexQ 0)) (b := toR3 (vertexQ 1)) (c := toR3 (vertexQ 2)) (d := toR3 (vertexQ 6))
    (by simp [verts]) (by simp [verts]) (by simp [verts]) (by simp [verts]) ?_
  simp [det3, Matrix.det_fin_three, toR3, vertexQ]
  norm_num

/-- **M12 is a nopert**, given valid certificate data. -/
theorem isNopert_of_certificatesValid (h : CertificatesValid) : IsNopert verts :=
  ⟨not_coplanar_verts, not_isRupert_of_certificatesValid h⟩

end M12

end
