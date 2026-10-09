module

public import Noperthedron.PentagonalHexecontahedron.CapClaim
public import Noperthedron.Nopert7.Model

@[expose] public section

/-!
# The cap of the 7-vertex solid at its mirror normal

Near the mirror normal x = (1, 0, −1) (the normal of the mirror swapping the
first and third coordinates) the mirror tie H_u R Q (Q = `mirrorQMat 1` = H_x)
approaches the identity, so poses there are certified by a cap certificate
(nopert7 `capcert7.cc --export`, the isotropic (u0) charts of the deltoidal
hexecontahedron's caps over ℚ, with two-sided width witnesses). The frame is
rational and unnormalized: x = (1, 0, −1), e₁ = (0, 1, 0), e₂ = (1, 0, 1).

`certOk`: the certificate passes `CapCert.check` (Lean's own chart list,
every tree rechecked with Bernstein bounds over ℚ) and is a certificate for
this cap: its frame, μ₀ = 1/16, strong scale 2, the half-turn prune with
G = Q, and its vertices exactly `solid`'s (`vertexQ`).

The covered region, in the coordinates of the view u and of the Cayley vector
w of the relative rotation (frame coordinates u·f/|f|²):

* `InCapView u`: u₀ > u₂, 2 |u₁| ≤ μ₀ (u₀ − u₂), |u₀ + u₂| ≤ μ₀ (u₀ − u₂)
  (i.e. u ∝ x + t₁ e₁ + t₂ e₂ with |tᵢ| ≤ μ₀);
* `InCapCayley w`: |w₁| ≤ 2 μ₀, |w₀ + w₂| ≤ 4 μ₀, |w₀ − w₂| ≤ 4 μ₀²
  (i.e. w = ω₁ e₁ + ω₂ e₂ + ω_x x with |ω₁|, |ω₂| ≤ 2 μ₀, |ω_x| ≤ 2 μ₀²);
* the mirror-tie cell tr(H_u R Q) ≤ tr R (implied by `InC3vCell`).

`cap_not_rupert`: a checked certificate rules out every pose (any offset) in
that region. `capHolds_of_cert`: the trace form `CapHolds` (DH's `CapClaim`:
the cone with dual frame vectors (0, 2, 0), (1, 0, 1) and the Cayley ball
|w|² ≤ 1/8192 as a trace bound) for the solution tree.
-/

namespace Noperthedron.Nopert7

open Noperthedron.PentagonalHexecontahedron
open Noperthedron.PentagonalHexecontahedron.Cap
open Noperthedron.PentagonalHexecontahedron.PVec
open scoped Matrix

/-- A rational number in K. -/
def kq (q : ℚ) : IcoQ := IcoQ.ofRat q

/-- The cap frame. -/
def capX : KVec := ![kq 1, kq 0, kq (-1)]
def capE1 : KVec := ![kq 0, kq 1, kq 0]
def capE2 : KVec := ![kq 1, kq 0, kq 1]

/-- The cap's half-width μ₀. -/
def capMu0 : ℚ := 1 / 16

/-- The columns of Q = `mirrorQMat 1` = H_x. -/
def capGcol : Fin 3 → KVec := ![![kq 0, kq 0, kq (-1)], ![kq 0, kq (-1), kq 0], ![kq (-1), kq 0, kq 0]]

/-- The solid's vertices, exactly. -/
def solidVerts : Array KVec := Array.ofFn fun i : Fin 7 => fun j => kq (vertexQ i j)

/-- The certificate is a checked certificate for this cap. -/
def certOk (c : CapCert) : Bool :=
  c.check && decide (c.st.strongScale = 2) && decide (1 ≤ c.st.mcm) && decide (c.st.x = capX) &&
    decide (c.st.e1 = capE1) && decide (c.st.e2 = capE2) && decide (c.pr.mu0 = capMu0) &&
    decide (c.verts = solidVerts) && c.usePrune && decide (c.Gcol = capGcol)

/-! ### The real frame -/

theorem val_kq (q : ℚ) : (kq q).val = q := IcoQ.val_ofRat q

theorem kv_capX : kv capX = ![1, 0, -1] := by
  funext i; fin_cases i <;> simp [kv, PVec.kval, capX, val_kq]

theorem kv_capE1 : kv capE1 = ![0, 1, 0] := by
  funext i; fin_cases i <;> simp [kv, PVec.kval, capE1, val_kq]

theorem kv_capE2 : kv capE2 = ![1, 0, 1] := by
  funext i; fin_cases i <;> simp [kv, PVec.kval, capE2, val_kq]

theorem gMat_capGcol : gMat capGcol = mirrorQMat 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gMat, capGcol, mirrorQMat, mirrorMat, val_kq]

/-- The certificate's vertex hull is the solid. -/
theorem solid_eq_hull (V : Array KVec) (hV : V = solidVerts) :
    solid = convexHull ℝ {v | ∃ vj ∈ V.toList.map kv, v = toEuc vj} := by
  subst hV
  unfold solid poly Polyhedron.hull
  congr 1
  ext v
  simp only [Set.mem_setOf_eq, List.mem_map, Array.mem_toList_iff, solidVerts, Array.mem_ofFn]
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩, ?_⟩
    ext j
    simp [toR3, toEuc, kv, PVec.kval, val_kq]
  · rintro ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩, rfl⟩
    refine ⟨i, ?_⟩
    ext j
    simp [toR3, toEuc, kv, PVec.kval, val_kq]

/-! ### The covered region -/

/-- The cap's views: u ∝ x + t₁ e₁ + t₂ e₂ with |tᵢ| ≤ μ₀. -/
def InCapView (u : Fin 3 → ℝ) : Prop :=
  0 < u 0 - u 2 ∧ 2 * |u 1| ≤ (capMu0 : ℝ) * (u 0 - u 2) ∧ |u 0 + u 2| ≤ (capMu0 : ℝ) * (u 0 - u 2)

/-- The cap's Cayley vectors: w = ω₁ e₁ + ω₂ e₂ + ω_x x with |ω₁|, |ω₂| ≤ 2 μ₀, |ω_x| ≤ 2 μ₀². -/
def InCapCayley (w : Fin 3 → ℝ) : Prop :=
  |w 1| ≤ 2 * (capMu0 : ℝ) ∧ |w 0 + w 2| ≤ 4 * (capMu0 : ℝ) ∧ |w 0 - w 2| ≤ 4 * (capMu0 : ℝ) ^ 2

theorem frameVec_eq (st : Setup) (hx : st.x = capX) (h1 : st.e1 = capE1) (h2 : st.e2 = capE2) :
    frameVec st = ![![0, 1, 0], ![1, 0, 1], ![1, 0, -1]] := by
  funext i
  fin_cases i <;> simp [frameVec, hx, h1, h2, kv_capX, kv_capE1, kv_capE2]

theorem frameCoord_eq (st : Setup) (hx : st.x = capX) (h1 : st.e1 = capE1) (h2 : st.e2 = capE2)
    (v : Fin 3 → ℝ) :
    frameCoord st v 0 = v 1 ∧ frameCoord st v 1 = (v 0 + v 2) / 2 ∧ frameCoord st v 2 = (v 0 - v 2) / 2 := by
  simp only [frameCoord, frameVec_eq st hx h1 h2]
  refine ⟨?_, ?_, ?_⟩ <;> simp [rdot] <;> field_simp <;> ring

/-- **The cap**: a checked certificate rules out every pose (any offset) whose view is in the cap
cone, whose relative rotation is cayley(w) with w in the cap's weighted box, and which lies in the
mirror-tie cell of Q = `mirrorQMat 1`. -/
theorem cap_not_rupert (c : CapCert) (hc : certOk c = true) (p : MatrixPose) (hu : InCapView p.view)
    (w : Fin 3 → ℝ) (hR : p.relativeRotation = cayleyMatrix (w 0) (w 1) (w 2)) (hw : InCapCayley w)
    (hcell : Matrix.trace (halfTurnMat p.view * p.relativeRotation * mirrorQMat 1) ≤
      Matrix.trace p.relativeRotation) :
    ¬ RupertPose p solid := by
  simp only [certOk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hck, hS⟩, hmcm⟩, hx⟩, he1⟩, he2⟩, hmu⟩, hV⟩, hpr⟩, hG⟩ := hc
  have hf := frameCoord_eq c.st hx he1 he2
  have hrange : ∀ i : Fin 3, (c.st.range i : ℝ) = 2 := by
    intro i; simp only [Setup.range, hS]; split_ifs <;> norm_num
  obtain ⟨hu0, hu1, hu2⟩ := hu
  obtain ⟨hw1, hw2, hw3⟩ := hw
  have hmu' : (c.pr.mu0 : ℝ) = capMu0 := by rw [hmu]
  apply c.not_rupert hck (by omega) hmcm solid (solid_eq_hull c.verts hV) p
  · rw [(hf p.view).2.2]; linarith
  · rw [(hf p.view).1, (hf p.view).2.2, hmu']; linarith
  · rw [(hf p.view).2.1, (hf p.view).2.2, hmu', abs_div, abs_two]; linarith
  · exact hR
  · have h0 : |frameCoord c.st w 0| ≤ 2 * (capMu0 : ℝ) ^ isoWt 0 := by
      rw [(hf w).1, show isoWt 0 = 1 from rfl, pow_one]; exact hw1
    have h1 : |frameCoord c.st w 1| ≤ 2 * (capMu0 : ℝ) ^ isoWt 1 := by
      rw [(hf w).2.1, show isoWt 1 = 1 from rfl, pow_one, abs_div, abs_two]; linarith
    have h2 : |frameCoord c.st w 2| ≤ 2 * (capMu0 : ℝ) ^ isoWt 2 := by
      rw [(hf w).2.2, show isoWt 2 = 2 from rfl, abs_div, abs_two]; linarith
    intro i
    rw [hrange i, hmu']
    fin_cases i
    exacts [h0, h1, h2]
  · intro _
    rw [hG, gMat_capGcol]
    exact hcell

/-- The cap in the C3v cell's form. -/
theorem cap_not_rupert_of_cell (c : CapCert) (hc : certOk c = true) (p : MatrixPose) (hu : InCapView p.view)
    (w : Fin 3 → ℝ) (hR : p.relativeRotation = cayleyMatrix (w 0) (w 1) (w 2)) (hw : InCapCayley w)
    (hcell : InC3vCell p.view p.relativeRotation) : ¬ RupertPose p solid :=
  cap_not_rupert c hc p hu w hR hw (hcell.2 1)

/-! ### The trace form (DH's `CapClaim`) -/

/-- The cap claim in the solution tree's form: views with u·x > 0, |u·(0, 2, 0)| ≤ μ₀ u·x,
|u·(1, 0, 1)| ≤ μ₀ u·x, relative rotations of trace ≥ (3 − 1/8192)/(1 + 1/8192) (the Cayley ball
|w|² ≤ 1/8192), in the mirror-tie cell of Q. -/
def CapHolds : Prop :=
  CapClaim solid ![1, 0, -1] ![0, 2, 0] ![1, 0, 1] capMu0 ((3 - 1 / 8192) / (1 + 1 / 8192)) (some (mirrorQMat 1))

theorem capHolds_of_cert (c : CapCert) (hc : certOk c = true) : CapHolds := by
  have hc' := hc
  simp only [certOk, Bool.and_eq_true, decide_eq_true_eq] at hc'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hck, hS⟩, hmcm⟩, hx⟩, he1⟩, he2⟩, hmu⟩, hV⟩, hpr⟩, hG⟩ := hc'
  have hfv := frameVec_eq c.st hx he1 he2
  have hrange : ∀ i : Fin 3, (c.st.range i : ℝ) = 2 := by
    intro i; simp only [Setup.range, hS]; split_ifs <;> norm_num
  have wsq : Real.sqrt (1 / 8192) ^ 2 = 1 / 8192 := Real.sq_sqrt (by norm_num)
  have hclaim := c.claim hck (by omega) hmcm (Real.sqrt (1 / 8192)) (Real.sqrt_nonneg _)
    (by rw [wsq]; norm_num)
    (by
      intro i
      rw [wsq, hrange i, hmu, hfv]
      fin_cases i <;> simp [isoWt, rdot, capMu0] <;> norm_num)
    (by rw [hmu]; norm_num [capMu0])
    solid (solid_eq_hull c.verts hV)
  rw [wsq] at hclaim
  have hd0 : dualVec c.st 0 = ![0, 2, 0] := by
    funext k
    simp only [dualVec, hfv, hx, kv_capX]
    fin_cases k <;> simp [rdot] <;> norm_num
  have hd1 : dualVec c.st 1 = ![1, 0, 1] := by
    funext k
    simp only [dualVec, hfv, hx, kv_capX]
    fin_cases k <;> simp [rdot] <;> norm_num
  rw [hd0, hd1, hx, kv_capX, hmu, if_pos hpr, hG, gMat_capGcol] at hclaim
  exact hclaim

end Noperthedron.Nopert7
