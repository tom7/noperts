module

public import Noperthedron.PentagonalHexecontahedron.CapCert

@[expose] public section

/-!
# Cap claims

`CapClaim S x e₁ e₂ μ₀ τ G`: no pose of S is Rupert whose view u has
u·x > 0, |u·eᵢ| ≤ μ₀ u·x, whose relative rotation has trace ≥ τ, and (if G
is given) whose relative rotation R satisfies tr(H_u R G) ≤ tr R. The trace
bound replaces the Cayley ball |w| ≤ wmax (tr cayley(w) = (3 − |w|²)/(1 + |w|²)),
so the claim is invariant under conjugation.

`CapCert.claim`: a checked certificate proves the claim of its cap with
τ = (3 − wmax²)/(1 + wmax²), for the dual frame vectors (|x|²/|fᵢ|²) fᵢ of an
unnormalized orthogonal frame (`dualVec`), when the ball |w| ≤ wmax lies in
the certificate's weighted box of frame coordinates. (The deltoidal
hexecontahedron's images of caps under its icosahedral group are gone with
the icosahedral layer.)
-/

namespace Noperthedron.PentagonalHexecontahedron.Cap

open NPoly PVec
open scoped Matrix

def CapClaim (S : Set ℝ³) (x e1 e2 : Fin 3 → ℝ) (mu0 τ : ℝ) (G : Option (Matrix (Fin 3) (Fin 3) ℝ)) : Prop :=
  ∀ p : MatrixPose, 0 < rdot p.view x → |rdot p.view e1| ≤ mu0 * rdot p.view x →
    |rdot p.view e2| ≤ mu0 * rdot p.view x → τ ≤ Matrix.trace p.relativeRotation →
    (∀ G₀, G = some G₀ → Matrix.trace (halfTurnMat p.view * p.relativeRotation * G₀) ≤
      Matrix.trace p.relativeRotation) →
    ¬ RupertPose p S

theorem rdot_cayley_bound {w : Fin 3 → ℝ} {wmax : ℝ} (hw0 : 0 ≤ wmax)
    (h : (3 - wmax ^ 2) / (1 + wmax ^ 2) ≤ Matrix.trace (cayleyMatrix (w 0) (w 1) (w 2))) :
    rdot w w ≤ wmax ^ 2 := by
  rw [trace_cayleyMatrix] at h
  have hD : 0 < cayleyDenom (w 0) (w 1) (w 2) := cayleyDenom_pos _ _ _
  have hD2 : (0 : ℝ) < 1 + wmax ^ 2 := by positivity
  rw [div_le_div_iff₀ hD2 hD] at h
  simp only [cayleyDenom] at h
  simp only [rdot]
  nlinarith

/-- The dual frame vector (|x|²/|fᵢ|²) fᵢ: u·(dualVec i) = |x|² (frame coordinate i of u), so the
cone |u·dualVec i| ≤ μ₀ u·x is |uᵢ| ≤ μ₀ u_x in frame coordinates. -/
noncomputable def dualVec (st : Setup) (i : Fin 3) : Fin 3 → ℝ :=
  (rdot (kv st.x) (kv st.x) / rdot (frameVec st i) (frameVec st i)) • frameVec st i

theorem rdot_dualVec (st : Setup) (u : Fin 3 → ℝ) (i : Fin 3) :
    rdot u (dualVec st i) = rdot (kv st.x) (kv st.x) * frameCoord st u i := by
  simp only [dualVec, frameCoord, rdot, Pi.smul_apply, smul_eq_mul]; ring

theorem rdot_x_eq (st : Setup) (u : Fin 3 → ℝ) :
    rdot u (kv st.x) = rdot (kv st.x) (kv st.x) * frameCoord st u 2 := by
  have hx : frameVec st 2 = kv st.x := rfl
  by_cases h0 : rdot (kv st.x) (kv st.x) = 0
  · have : kv st.x = 0 := by
      funext k
      simp only [rdot] at h0
      fin_cases k <;> simp <;> nlinarith [mul_self_nonneg (kv st.x 0), mul_self_nonneg (kv st.x 1),
        mul_self_nonneg (kv st.x 2)]
    rw [h0, this]; simp [rdot]
  · simp only [frameCoord, hx]; field_simp

/-- A Cayley ball |w| ≤ wmax inside the weighted box of frame coordinates. -/
theorem frameCoord_le_of_ball (st : Setup) (hF : FrameOK st) {w : Fin 3 → ℝ} {wmax B : ℝ} (i : Fin 3)
    (hw : rdot w w ≤ wmax ^ 2) (hB : 0 ≤ B) (hb : wmax ^ 2 ≤ B ^ 2 * rdot (frameVec st i) (frameVec st i)) :
    |frameCoord st w i| ≤ B := by
  have hf : 0 < rdot (frameVec st i) (frameVec st i) := by
    obtain ⟨-, h1, h2, h3, -⟩ := hF
    fin_cases i
    · exact h1
    · exact h2
    · exact h3
  set f := frameVec st i
  set F := rdot f f
  unfold frameCoord
  rw [abs_div, abs_of_pos hf, div_le_iff₀ hf]
  have hcs := rdot_sq_le w f
  have h1 : rdot w f ^ 2 ≤ (B * F) ^ 2 := by
    calc rdot w f ^ 2 ≤ rdot w w * F := hcs
      _ ≤ wmax ^ 2 * F := mul_le_mul_of_nonneg_right hw hf.le
      _ ≤ B ^ 2 * F * F := mul_le_mul_of_nonneg_right hb hf.le
      _ = (B * F) ^ 2 := by ring
  exact abs_le_of_sq_le_sq' h1 (by positivity) |> fun h => abs_le.mpr ⟨h.1, h.2⟩

/-- **A checked certificate proves its cap's claim** (trace form, for the solution tree): the cone
in dual-frame form and the Cayley ball |w| ≤ wmax inside the certificate's weighted box. -/
theorem CapCert.claim (c : CapCert) (hc : c.check = true) (hS : 2 ≤ c.st.strongScale) (hmcm : 1 ≤ c.st.mcm)
    (wmax : ℝ) (hw0 : 0 ≤ wmax) (hw3 : wmax ^ 2 ≤ 3)
    (hwi : ∀ i : Fin 3, wmax ^ 2 ≤ ((c.st.range i : ℝ) * (c.pr.mu0 : ℝ) ^ isoWt i) ^ 2 *
      rdot (frameVec c.st i) (frameVec c.st i))
    (hmu : 0 ≤ (c.pr.mu0 : ℝ))
    (S : Set ℝ³) (hSdef : S = convexHull ℝ {v | ∃ vj ∈ c.verts.toList.map kv, v = toEuc vj}) :
    CapClaim S (kv c.st.x) (dualVec c.st 0) (dualVec c.st 1) c.pr.mu0 ((3 - wmax ^ 2) / (1 + wmax ^ 2))
      (if c.usePrune then some (gMat c.Gcol) else none) := by
  intro p hx he1 he2 htr hcell
  obtain ⟨hF, -, -, -⟩ := c.check_sound hc
  have hxx : 0 < rdot (kv c.st.x) (kv c.st.x) := hF.2.2.2.1
  have hτ : 0 ≤ (3 - wmax ^ 2) / (1 + wmax ^ 2) := div_nonneg (by linarith) (by positivity)
  obtain ⟨wx, wy, wz, -, hR⟩ := Noperthedron.exists_cayleyMatrix_of_trace_nonneg p.relativeRotation
    (Noperthedron.Atlas.MatrixPose.relativeRotation_mem_SO3 p) (le_trans hτ htr)
  let w : Fin 3 → ℝ := ![wx, wy, wz]
  have hRw : p.relativeRotation = cayleyMatrix (w 0) (w 1) (w 2) := hR
  have hball : rdot w w ≤ wmax ^ 2 := by
    apply rdot_cayley_bound hw0
    rw [← hRw]; exact htr
  rw [rdot_x_eq] at hx he1 he2
  rw [rdot_dualVec] at he1 he2
  have hx' : 0 < frameCoord c.st p.view 2 := (mul_pos_iff_of_pos_left hxx).mp hx
  apply c.not_rupert hc hS hmcm S hSdef p hx'
  · rw [abs_mul, abs_of_pos hxx] at he1
    nlinarith
  · rw [abs_mul, abs_of_pos hxx] at he2
    nlinarith
  · exact hRw
  · intro i
    apply frameCoord_le_of_ball c.st hF i hball (by positivity) (hwi i)
  · intro hp
    exact hcell (gMat c.Gcol) (by simp [hp])

end Noperthedron.PentagonalHexecontahedron.Cap
