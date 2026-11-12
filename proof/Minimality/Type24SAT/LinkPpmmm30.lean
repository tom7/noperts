module

public import Minimality.Type24SAT.Facets24
public import Minimality.Type24SAT.PcPpmmm30

@[expose] public section

/-! Link for the type 24 certificate Ppmmm30 (F24c, generated from the certificate ppmmm_r30): the core literals of the clause, in
literal form, imply the certificate's strict polynomial conditions in the frame F24c, hence False. -/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open scoped RealInnerProductSpace

namespace Minimality.T24.SAT
open Minimality

/-- The core of ppmmm_r30: the literals (kind, sign) of the clause NOT(core). -/
def corePpmmm30 : List (Lit24 × Int) := [(.fc 0 3 6, 1), (.fc 2 3 6, 1), (.fc 3 1 2, -1), (.kv 3 0 5 3 4, -1), (.lv 0 1 5 3 6, 1), (.lv 1 3 5 4 6, 1), (.lv 4 5 6 1 3, -1), (.mv 0 1 2 6 3 5, 1), (.mv 0 2 1 6 3 4, -1), (.mv 0 3 1 2 5 6, -1), (.mv 0 5 1 2 4 6, -1), (.mv 0 5 1 3 2 4, -1), (.mv 0 6 1 3 2 5, -1), (.mv 1 2 3 4 5 6, 1), (.nv 2 4 7, 1)]

/-- **Core of Ppmmm30 is unsatisfiable** (for a type 24 configuration with `Convex24` and `QuadD`). -/
theorem coreFalsePpmmm30 (x : Nat → ℝ³) (hQ : QuadD x) (hC : Convex24 x)
    (hcore : ∀ p ∈ corePpmmm30, LitHolds x p.1 p.2) : False := by
  obtain ⟨U, D, hF, h0, h3, h5, h2, h4z⟩ := frame24C x hQ (hdet24 x hC)
  rcases h1 : U 1 with ⟨x1a, x1b, x1c⟩
  rcases h6 : U 6 with ⟨x6a, x6b, x6c⟩
  rcases h4 : U 4 with ⟨p4a, p4b, z4⟩
  have hz4 : z4 = 0 := by simpa [h4] using h4z
  have hz0 : (U 0).z = 0 := by simp [h0]
  have hz3 : (U 3).z = 0 := by simp [h3]
  have hz5 : (U 5).z = 0 := by simp [h5]
  have hz4' : (U 4).z = 0 := h4z
  have r0 : 0 < - x1b * x6a + x1a * x6b + x1b := by
    have h := lit_frame hF (.fc 0 3 6) (by simp) (1) (hcore (.fc 0 3 6, 1) (by simp [corePpmmm30]))
    have e : ((1 : Int) : ℝ) * val3 U (.fc 0 3 6) = - x1b * x6a + x1a * x6b + x1b := by
      simp only [val3, nrm3, V3.dot, V3.cr, V3.sub, V3.smul, fa_0, fb_0, fc_0, sg_0, h0, h1, h2, h3, h6]; push_cast; ring
    rw [e] at h; exact h
  have f24 : 0 < - x1b * x6a + x1a * x6b + x1b := pos_sq (f := (- x1b * x6a + x1a * x6b + x1b)) (q := (1)) (k := (1 : ℝ)) (r0) (by norm_num) (by ring)
  have r1 : 0 < - x1c * x6b - x1c * x6a + x1b * x6c + x1a * x6c - x1b - x1a := by
    have h := lit_frame hF (.mv 0 1 2 6 3 5) (by simp) (1) (hcore (.mv 0 1 2 6 3 5, 1) (by simp [corePpmmm30]))
    have e : ((1 : Int) : ℝ) * val3 U (.mv 0 1 2 6 3 5) = - x1c * x6b - x1c * x6a + x1b * x6c + x1a * x6c - x1b - x1a := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h0, h1, h2, h3, h5, h6]; push_cast; ring
    rw [e] at h; exact h
  have f68 : 0 < - x1c * x6b - x1c * x6a + x1b * x6c + x1a * x6c - x1b - x1a := pos_sq (f := (- x1c * x6b - x1c * x6a + x1b * x6c + x1a * x6c - x1b - x1a)) (q := (1)) (k := (1 : ℝ)) (r1) (by norm_num) (by ring)
  have r2 : 0 < x1c * x6a + x1b * x6a - x1a * x6c - x1a * x6b + x6c + x6b := by
    have h := lit_frame hF (.mv 0 6 1 3 2 5) (by simp) (-1) (hcore (.mv 0 6 1 3 2 5, -1) (by simp [corePpmmm30]))
    have e : ((-1 : Int) : ℝ) * val3 U (.mv 0 6 1 3 2 5) = x1c * x6a + x1b * x6a - x1a * x6c - x1a * x6b + x6c + x6b := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h0, h1, h2, h3, h5, h6]; push_cast; ring
    rw [e] at h; exact h
  have f205 : 0 < x1c * x6a + x1b * x6a - x1a * x6c - x1a * x6b + x6c + x6b := pos_sq (f := (x1c * x6a + x1b * x6a - x1a * x6c - x1a * x6b + x6c + x6b)) (q := (1)) (k := (1 : ℝ)) (r2) (by norm_num) (by ring)
  have r3 : 0 < x1c * x6b - x1b * x6c - x6b - x1c + 1 := by
    have h := lit_frame hF (.mv 0 3 1 2 5 6) (by simp) (-1) (hcore (.mv 0 3 1 2 5 6, -1) (by simp [corePpmmm30]))
    have e : ((-1 : Int) : ℝ) * val3 U (.mv 0 3 1 2 5 6) = x1c * x6b - x1b * x6c - x6b - x1c + 1 := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h0, h1, h2, h3, h5, h6]; push_cast; ring
    rw [e] at h; exact h
  have f133 : 0 < x1c * x6b - x1b * x6c - x6b - x1c + 1 := pos_sq (f := (x1c * x6b - x1b * x6c - x6b - x1c + 1)) (q := (1)) (k := (1 : ℝ)) (r3) (by norm_num) (by ring)
  have r4 : 0 < x1c * p4a - x1c * x6a + x1a * x6c - p4a + x6a := by
    have h := lit_frame hF (.mv 0 5 1 2 4 6) (by simp) (-1) (hcore (.mv 0 5 1 2 4 6, -1) (by simp [corePpmmm30]))
    have e : ((-1 : Int) : ℝ) * val3 U (.mv 0 5 1 2 4 6) = x1c * p4a - x1c * x6a + x1a * x6c - p4a + x6a := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h0, h1, h2, h4, h5, h6, hz4]; push_cast; ring
    rw [e] at h; exact h
  have f181 : 0 < x1c * p4a - x1c * x6a + x1a * x6c - p4a + x6a := pos_sq (f := (x1c * p4a - x1c * x6a + x1a * x6c - p4a + x6a)) (q := (1)) (k := (1 : ℝ)) (r4) (by norm_num) (by ring)
  have r5 : 0 < x1c * x6b * p4a - x1c * x6a * p4b - x1b * x6c * p4a + x1a * x6c * p4b - x6b * p4a + x6a * p4b - x1c * p4a - x1c * x6b + x1b * x6c + p4a + x6b + x1c - 1 := by
    have h := lit_frame hF (.mv 1 2 3 4 5 6) (by simp) (1) (hcore (.mv 1 2 3 4 5 6, 1) (by simp [corePpmmm30]))
    have e : ((1 : Int) : ℝ) * val3 U (.mv 1 2 3 4 5 6) = x1c * x6b * p4a - x1c * x6a * p4b - x1b * x6c * p4a + x1a * x6c * p4b - x6b * p4a + x6a * p4b - x1c * p4a - x1c * x6b + x1b * x6c + p4a + x6b + x1c - 1 := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h1, h2, h3, h4, h5, h6, hz4]; push_cast; ring
    rw [e] at h; exact h
  have f235 : 0 < x1c * x6b * p4a - x1c * x6a * p4b - x1b * x6c * p4a + x1a * x6c * p4b - x6b * p4a + x6a * p4b - x1c * p4a - x1c * x6b + x1b * x6c + p4a + x6b + x1c - 1 := pos_sq (f := (x1c * x6b * p4a - x1c * x6a * p4b - x1b * x6c * p4a + x1a * x6c * p4b - x6b * p4a + x6a * p4b - x1c * p4a - x1c * x6b + x1b * x6c + p4a + x6b + x1c - 1)) (q := (1)) (k := (1 : ℝ)) (r5) (by norm_num) (by ring)
  have r6 : 0 < x6a - 1 := by
    have h := lit_frame hF (.fc 2 3 6) (by simp) (1) (hcore (.fc 2 3 6, 1) (by simp [corePpmmm30]))
    have e : ((1 : Int) : ℝ) * val3 U (.fc 2 3 6) = x6a - 1 := by
      simp only [val3, nrm3, V3.dot, V3.cr, V3.sub, V3.smul, fa_2, fb_2, fc_2, sg_2, h0, h2, h3, h5, h6]; push_cast; ring
    rw [e] at h; exact h
  have f89 : 0 < x6a - 1 := pos_sq (f := (x6a - 1)) (q := (1)) (k := (1 : ℝ)) (r6) (by norm_num) (by ring)
  have r7 : 0 < - p4b := by
    have h := cv_frame hF hC 3 2 (by decide)
    have e : cv3 U 3 2 = - p4b := by
      simp only [nrm3, cv3, V3.dot, V3.cr, V3.sub, V3.smul, fa_3, fb_3, fc_3, sg_3, h0, h2, h3, h4, hz4]; ring
    rw [e] at h; exact h
  have r8 : 0 < p4a * p4b - p4b := by
    have h := kv_frame hF 3 0 5 3 4 (-1) (by simp [hz0]) (by simp [hz5]) (by simp [hz3]) (by simp [hz4']) (by simp [fa_3, hz0]) (by simp [fb_3, hz3]) (by simp [fc_3, hz4']) (hcore (.kv 3 0 5 3 4, -1) (by simp [corePpmmm30]))
    have e : ((-1 : Int) : ℝ) * val3 U (.kv 3 0 5 3 4) = p4a * p4b - p4b := by
      simp only [val3, nrm3, V3.dot, V3.cr, V3.sub, V3.smul, fa_3, fb_3, fc_3, sg_3, h0, h3, h4, h5, hz4]; push_cast; ring
    rw [e] at h; exact h
  have f42 : 0 < - p4a + 1 := pos_sq (f := (- p4a + 1)) (q := (p4b)) (k := (1 : ℝ)) (mul_pos r7 r8) (by norm_num) (by ring)
  have f10 : 0 < - p4b := pos_sq (f := (- p4b)) (q := (1)) (k := (1 : ℝ)) (r7) (by norm_num) (by ring)
  have r9 : 0 < - x1c * p4b + p4b := by
    have h := lit_frame hF (.fc 3 1 2) (by simp) (-1) (hcore (.fc 3 1 2, -1) (by simp [corePpmmm30]))
    have e : ((-1 : Int) : ℝ) * val3 U (.fc 3 1 2) = - x1c * p4b + p4b := by
      simp only [val3, nrm3, V3.dot, V3.cr, V3.sub, V3.smul, fa_3, fb_3, fc_3, sg_3, h0, h1, h2, h3, h4, hz4]; push_cast; ring
    rw [e] at h; exact h
  have f121 : 0 < x1c - 1 := pos_sq (f := (x1c - 1)) (q := (p4b)) (k := (1 : ℝ)) (mul_pos r7 r9) (by norm_num) (by ring)
  have r10 : 0 < - x6c * p4b := by
    have h := cv_frame hF hC 3 6 (by decide)
    have e : cv3 U 3 6 = - x6c * p4b := by
      simp only [nrm3, cv3, V3.dot, V3.cr, V3.sub, V3.smul, fa_3, fb_3, fc_3, sg_3, h0, h3, h4, h6, hz4]; ring
    rw [e] at h; exact h
  have f11 : 0 < x6c := pos_sq (f := (x6c)) (q := (p4b)) (k := (1 : ℝ)) (mul_pos r7 r10) (by norm_num) (by ring)
  have r11 : 0 < - x1c * p4a - x1a + 1 := by
    have h := lit_frame hF (.mv 0 5 1 3 2 4) (by simp) (-1) (hcore (.mv 0 5 1 3 2 4, -1) (by simp [corePpmmm30]))
    have e : ((-1 : Int) : ℝ) * val3 U (.mv 0 5 1 3 2 4) = - x1c * p4a - x1a + 1 := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h0, h1, h2, h3, h4, h5, hz4]; push_cast; ring
    rw [e] at h; exact h
  have f183 : 0 < - x1c * p4a - x1a + 1 := pos_sq (f := (- x1c * p4a - x1a + 1)) (q := (1)) (k := (1 : ℝ)) (r11) (by norm_num) (by ring)
  have r12 : 0 < - x6a * x6c * p4b + x6a * x6b * p4a - x6a^2 * p4b - x6b * p4a + x6a * p4b := by
    have h := lit_frame hF (.nv 2 4 7) (by simp) (1) (hcore (.nv 2 4 7, 1) (by simp [corePpmmm30]))
    have e : ((1 : Int) : ℝ) * val3 U (.nv 2 4 7) = - x6a * x6c * p4b + x6a * x6b * p4a - x6a^2 * p4b - x6b * p4a + x6a * p4b := by
      simp only [val3, nrm3, V3.det, V3.dot, V3.cr, V3.sub, V3.smul, fa_2, fb_2, fc_2, sg_2, fa_4, fb_4, fc_4, sg_4, fa_7, fb_7, fc_7, sg_7, h0, h2, h3, h4, h5, h6, hz4]; push_cast; ring
    rw [e] at h; exact h
  have f306 : 0 < - x6a * x6c * p4b + x6a * x6b * p4a - x6a^2 * p4b - x6b * p4a + x6a * p4b := pos_sq (f := (- x6a * x6c * p4b + x6a * x6b * p4a - x6a^2 * p4b - x6b * p4a + x6a * p4b)) (q := (1)) (k := (1 : ℝ)) (r12) (by norm_num) (by ring)
  have r13 : 0 < x1c * x6b * p4a - x1c * x6a * p4b - x1b * x6c * p4a + x1a * x6c * p4b - x6c * p4b - x1c * p4a + x1c * x6a - x1a * x6c + x6c := by
    have h := lit_frame hF (.lv 4 5 6 1 3) (by simp) (-1) (hcore (.lv 4 5 6 1 3, -1) (by simp [corePpmmm30]))
    have e : ((-1 : Int) : ℝ) * val3 U (.lv 4 5 6 1 3) = x1c * x6b * p4a - x1c * x6a * p4b - x1b * x6c * p4a + x1a * x6c * p4b - x6c * p4b - x1c * p4a + x1c * x6a - x1a * x6c + x6c := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h1, h3, h4, h5, h6, hz4]; push_cast; ring
    rw [e] at h; exact h
  have f256 : 0 < x1c * x6b * p4a - x1c * x6a * p4b - x1b * x6c * p4a + x1a * x6c * p4b - x6c * p4b - x1c * p4a + x1c * x6a - x1a * x6c + x6c := pos_sq (f := (x1c * x6b * p4a - x1c * x6a * p4b - x1b * x6c * p4a + x1a * x6c * p4b - x6c * p4b - x1c * p4a + x1c * x6a - x1a * x6c + x6c)) (q := (1)) (k := (1 : ℝ)) (r13) (by norm_num) (by ring)
  have r14 : 0 < - x6b * p4a + x6a * p4b + x1b * p4a - x1a * p4b + x6b - x1b := by
    have h := lit_frame hF (.mv 0 2 1 6 3 4) (by simp) (-1) (hcore (.mv 0 2 1 6 3 4, -1) (by simp [corePpmmm30]))
    have e : ((-1 : Int) : ℝ) * val3 U (.mv 0 2 1 6 3 4) = - x6b * p4a + x6a * p4b + x1b * p4a - x1a * p4b + x6b - x1b := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h0, h1, h2, h3, h4, h6, hz4]; push_cast; ring
    rw [e] at h; exact h
  have f112 : 0 < - x6b * p4a + x6a * p4b + x1b * p4a - x1a * p4b + x6b - x1b := pos_sq (f := (- x6b * p4a + x6a * p4b + x1b * p4a - x1a * p4b + x6b - x1b)) (q := (1)) (k := (1 : ℝ)) (r14) (by norm_num) (by ring)
  have r15 : 0 < x1c * x6a - x1a * x6c - x1c := by
    have h := lit_frame hF (.lv 0 1 5 3 6) (by simp) (1) (hcore (.lv 0 1 5 3 6, 1) (by simp [corePpmmm30]))
    have e : ((1 : Int) : ℝ) * val3 U (.lv 0 1 5 3 6) = x1c * x6a - x1a * x6c - x1c := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h0, h1, h3, h5, h6]; push_cast; ring
    rw [e] at h; exact h
  have f43 : 0 < x1c * x6a - x1a * x6c - x1c := pos_sq (f := (x1c * x6a - x1a * x6c - x1c)) (q := (1)) (k := (1 : ℝ)) (r15) (by norm_num) (by ring)
  have r16 : 0 < x1c * p4b + x1c * p4a - x1c * x6b - x1c * x6a + x1b * x6c + x1a * x6c - x6c := by
    have h := lit_frame hF (.lv 1 3 5 4 6) (by simp) (1) (hcore (.lv 1 3 5 4 6, 1) (by simp [corePpmmm30]))
    have e : ((1 : Int) : ℝ) * val3 U (.lv 1 3 5 4 6) = x1c * p4b + x1c * p4a - x1c * x6b - x1c * x6a + x1b * x6c + x1a * x6c - x6c := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h1, h3, h4, h5, h6, hz4]; push_cast; ring
    rw [e] at h; exact h
  have f246 : 0 < x1c * p4b + x1c * p4a - x1c * x6b - x1c * x6a + x1b * x6c + x1a * x6c - x6c := pos_sq (f := (x1c * p4b + x1c * p4a - x1c * x6b - x1c * x6a + x1b * x6c + x1a * x6c - x6c)) (q := (1)) (k := (1 : ℝ)) (r16) (by norm_num) (by ring)
  exact Minimality.PC.pcPpmmm30 x1a x1b x1c x6a x6b x6c p4a p4b f24 f68 f205 f133 f181 f235 f89 f42 f10 f121 f11 f183 f306 f256 f112 f43 f246

#print axioms coreFalsePpmmm30

end Minimality.T24.SAT
