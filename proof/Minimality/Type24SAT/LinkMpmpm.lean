module

public import Minimality.Type24SAT.Facets24
public import Minimality.Type24SAT.PcMpmpm

@[expose] public section

/-! Link for the type 24 certificate Mpmpm (F24c, generated from the certificate mpmpm_r3): the core literals of the clause, in
literal form, imply the certificate's strict polynomial conditions in the frame F24c, hence False. -/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open scoped RealInnerProductSpace

namespace Minimality.T24.SAT
open Minimality

/-- The core of mpmpm_r3: the literals (kind, sign) of the clause NOT(core). -/
def coreMpmpm : List (Lit24 × Int) := [(.br 1 3 5 6, -1), (.fc 0 3 6, 1), (.fc 0 4 6, -1), (.fc 2 1 3, 1), (.fc 2 4 6, 1), (.fc 3 1 2, 1), (.fc 5 0 5, 1), (.fc 8 1 5, -1), (.kv 3 0 4 3 5, -1), (.kv 3 0 5 3 4, 1), (.lv 0 1 5 4 6, -1), (.lv 0 2 4 1 6, 1), (.lv 0 3 6 1 5, -1), (.lv 0 5 6 1 2, 1), (.lv 1 2 3 0 5, 1), (.lv 1 2 4 0 5, 1), (.lv 1 2 5 4 6, 1), (.lv 1 3 4 2 6, -1), (.lv 1 4 5 3 6, -1), (.mv 0 1 2 5 3 4, 1), (.mv 0 1 2 5 3 6, 1), (.mv 0 1 2 5 4 6, 1), (.mv 0 3 1 4 2 5, 1), (.mv 0 3 1 5 4 6, -1), (.mv 0 5 1 2 3 6, -1), (.mv 0 5 1 2 4 6, -1), (.mv 0 5 1 4 2 3, -1), (.mv 0 6 2 4 3 5, -1), (.nv 2 4 7, 1)]

/-- **Core of Mpmpm is unsatisfiable** (for a type 24 configuration with `Convex24` and `QuadD`). -/
theorem coreFalseMpmpm (x : Nat → ℝ³) (hQ : QuadD x) (hC : Convex24 x)
    (hcore : ∀ p ∈ coreMpmpm, LitHolds x p.1 p.2) : False := by
  obtain ⟨U, D, hF, h0, h3, h5, h2, h4z⟩ := frame24C x hQ (hdet24 x hC)
  rcases h1 : U 1 with ⟨x1a, x1b, x1c⟩
  rcases h6 : U 6 with ⟨x6a, x6b, x6c⟩
  rcases h4 : U 4 with ⟨p4a, p4b, z4⟩
  have hz4 : z4 = 0 := by simpa [h4] using h4z
  have hz0 : (U 0).z = 0 := by simp [h0]
  have hz3 : (U 3).z = 0 := by simp [h3]
  have hz5 : (U 5).z = 0 := by simp [h5]
  have hz4' : (U 4).z = 0 := h4z
  have r0 : 0 < x1a := by
    have h := cv_frame hF hC 0 5 (by decide)
    have e : cv3 U 0 5 = x1a := by
      simp only [nrm3, cv3, V3.dot, V3.cr, V3.sub, V3.smul, fa_0, fb_0, fc_0, sg_0, h0, h1, h2, h5]; ring
    rw [e] at h; exact h
  have f2 : 0 < x1a := pos_sq (f := (x1a)) (q := (1)) (k := (1 : ℝ)) (r0) (by norm_num) (by ring)
  have r1 : 0 < - p4b := by
    have h := cv_frame hF hC 3 2 (by decide)
    have e : cv3 U 3 2 = - p4b := by
      simp only [nrm3, cv3, V3.dot, V3.cr, V3.sub, V3.smul, fa_3, fb_3, fc_3, sg_3, h0, h2, h3, h4, hz4]; ring
    rw [e] at h; exact h
  have f10 : 0 < - p4b := pos_sq (f := (- p4b)) (q := (1)) (k := (1 : ℝ)) (r1) (by norm_num) (by ring)
  have r2 : 0 < - x1b * x6a + x1a * x6b + x1b := by
    have h := lit_frame hF (.fc 0 3 6) (by simp) (1) (hcore (.fc 0 3 6, 1) (by simp [coreMpmpm]))
    have e : ((1 : Int) : ℝ) * val3 U (.fc 0 3 6) = - x1b * x6a + x1a * x6b + x1b := by
      simp only [val3, nrm3, V3.dot, V3.cr, V3.sub, V3.smul, fa_0, fb_0, fc_0, sg_0, h0, h1, h2, h3, h6]; push_cast; ring
    rw [e] at h; exact h
  have f24 : 0 < - x1b * x6a + x1a * x6b + x1b := pos_sq (f := (- x1b * x6a + x1a * x6b + x1b)) (q := (1)) (k := (1 : ℝ)) (r2) (by norm_num) (by ring)
  have r3 : 0 < - x1b * p4a + x1b * x6a + x1a * p4b - x1a * x6b := by
    have h := lit_frame hF (.fc 0 4 6) (by simp) (-1) (hcore (.fc 0 4 6, -1) (by simp [coreMpmpm]))
    have e : ((-1 : Int) : ℝ) * val3 U (.fc 0 4 6) = - x1b * p4a + x1b * x6a + x1a * p4b - x1a * x6b := by
      simp only [val3, nrm3, V3.dot, V3.cr, V3.sub, V3.smul, fa_0, fb_0, fc_0, sg_0, h0, h1, h2, h4, h6, hz4]; push_cast; ring
    rw [e] at h; exact h
  have f26 : 0 < - x1b * p4a + x1b * x6a + x1a * p4b - x1a * x6b := pos_sq (f := (- x1b * p4a + x1b * x6a + x1a * p4b - x1a * x6b)) (q := (1)) (k := (1 : ℝ)) (r3) (by norm_num) (by ring)
  have r4 : 0 < - p4b^2 - p4a * p4b := by
    have h := kv_frame hF 3 0 4 3 5 (-1) (by simp [hz0]) (by simp [hz4']) (by simp [hz3]) (by simp [hz5]) (by simp [fa_3, hz0]) (by simp [fb_3, hz3]) (by simp [fc_3, hz4']) (hcore (.kv 3 0 4 3 5, -1) (by simp [coreMpmpm]))
    have e : ((-1 : Int) : ℝ) * val3 U (.kv 3 0 4 3 5) = - p4b^2 - p4a * p4b := by
      simp only [val3, nrm3, V3.dot, V3.cr, V3.sub, V3.smul, fa_3, fb_3, fc_3, sg_3, h0, h3, h4, h5, hz4]; push_cast; ring
    rw [e] at h; exact h
  have f36 : 0 < p4b + p4a := pos_sq (f := (p4b + p4a)) (q := (p4b)) (k := (1 : ℝ)) (mul_pos r1 r4) (by norm_num) (by ring)
  have r5 : 0 < - p4a * p4b + p4b := by
    have h := kv_frame hF 3 0 5 3 4 (1) (by simp [hz0]) (by simp [hz5]) (by simp [hz3]) (by simp [hz4']) (by simp [fa_3, hz0]) (by simp [fb_3, hz3]) (by simp [fc_3, hz4']) (hcore (.kv 3 0 5 3 4, 1) (by simp [coreMpmpm]))
    have e : ((1 : Int) : ℝ) * val3 U (.kv 3 0 5 3 4) = - p4a * p4b + p4b := by
      simp only [val3, nrm3, V3.dot, V3.cr, V3.sub, V3.smul, fa_3, fb_3, fc_3, sg_3, h0, h3, h4, h5, hz4]; push_cast; ring
    rw [e] at h; exact h
  have f42 : 0 < p4a - 1 := pos_sq (f := (p4a - 1)) (q := (p4b)) (k := (1 : ℝ)) (mul_pos r1 r5) (by norm_num) (by ring)
  have r6 : 0 < x1c * p4a - x1c * x6a + x1a * x6c := by
    have h := lit_frame hF (.lv 0 1 5 4 6) (by simp) (-1) (hcore (.lv 0 1 5 4 6, -1) (by simp [coreMpmpm]))
    have e : ((-1 : Int) : ℝ) * val3 U (.lv 0 1 5 4 6) = x1c * p4a - x1c * x6a + x1a * x6c := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h0, h1, h4, h5, h6, hz4]; push_cast; ring
    rw [e] at h; exact h
  have f44 : 0 < x1c * p4a - x1c * x6a + x1a * x6c := pos_sq (f := (x1c * p4a - x1c * x6a + x1a * x6c)) (q := (1)) (k := (1 : ℝ)) (r6) (by norm_num) (by ring)
  have r7 : 0 < x1c * p4a + x1b * p4a - x1a * p4b - x1c - x1b := by
    have h := lit_frame hF (.mv 0 1 2 5 3 4) (by simp) (1) (hcore (.mv 0 1 2 5 3 4, 1) (by simp [coreMpmpm]))
    have e : ((1 : Int) : ℝ) * val3 U (.mv 0 1 2 5 3 4) = x1c * p4a + x1b * p4a - x1a * p4b - x1c - x1b := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h0, h1, h2, h3, h4, h5, hz4]; push_cast; ring
    rw [e] at h; exact h
  have f64 : 0 < x1c * p4a + x1b * p4a - x1a * p4b - x1c - x1b := pos_sq (f := (x1c * p4a + x1b * p4a - x1a * p4b - x1c - x1b)) (q := (1)) (k := (1 : ℝ)) (r7) (by norm_num) (by ring)
  have r8 : 0 < x1c * x6a + x1b * x6a - x1a * x6c - x1a * x6b - x1c - x1b := by
    have h := lit_frame hF (.mv 0 1 2 5 3 6) (by simp) (1) (hcore (.mv 0 1 2 5 3 6, 1) (by simp [coreMpmpm]))
    have e : ((1 : Int) : ℝ) * val3 U (.mv 0 1 2 5 3 6) = x1c * x6a + x1b * x6a - x1a * x6c - x1a * x6b - x1c - x1b := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h0, h1, h2, h3, h5, h6]; push_cast; ring
    rw [e] at h; exact h
  have f65 : 0 < x1c * x6a + x1b * x6a - x1a * x6c - x1a * x6b - x1c - x1b := pos_sq (f := (x1c * x6a + x1b * x6a - x1a * x6c - x1a * x6b - x1c - x1b)) (q := (1)) (k := (1 : ℝ)) (r8) (by norm_num) (by ring)
  have r9 : 0 < - x1c * p4a + x1c * x6a - x1b * p4a + x1b * x6a + x1a * p4b - x1a * x6c - x1a * x6b := by
    have h := lit_frame hF (.mv 0 1 2 5 4 6) (by simp) (1) (hcore (.mv 0 1 2 5 4 6, 1) (by simp [coreMpmpm]))
    have e : ((1 : Int) : ℝ) * val3 U (.mv 0 1 2 5 4 6) = - x1c * p4a + x1c * x6a - x1b * p4a + x1b * x6a + x1a * p4b - x1a * x6c - x1a * x6b := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h0, h1, h2, h4, h5, h6, hz4]; push_cast; ring
    rw [e] at h; exact h
  have f66 : 0 < - x1c * p4a + x1c * x6a - x1b * p4a + x1b * x6a + x1a * p4b - x1a * x6c - x1a * x6b := pos_sq (f := (- x1c * p4a + x1c * x6a - x1b * p4a + x1b * x6a + x1a * p4b - x1a * x6c - x1a * x6b)) (q := (1)) (k := (1 : ℝ)) (r9) (by norm_num) (by ring)
  have r10 : 0 < - x6b * p4a + x6a * p4b + x1b * p4a - x1a * p4b := by
    have h := lit_frame hF (.lv 0 2 4 1 6) (by simp) (1) (hcore (.lv 0 2 4 1 6, 1) (by simp [coreMpmpm]))
    have e : ((1 : Int) : ℝ) * val3 U (.lv 0 2 4 1 6) = - x6b * p4a + x6a * p4b + x1b * p4a - x1a * p4b := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h0, h1, h2, h4, h6, hz4]; push_cast; ring
    rw [e] at h; exact h
  have f83 : 0 < - x6b * p4a + x6a * p4b + x1b * p4a - x1a * p4b := pos_sq (f := (- x6b * p4a + x6a * p4b + x1b * p4a - x1a * p4b)) (q := (1)) (k := (1 : ℝ)) (r10) (by norm_num) (by ring)
  have r11 : 0 < - x1a + 1 := by
    have h := lit_frame hF (.fc 2 1 3) (by simp) (1) (hcore (.fc 2 1 3, 1) (by simp [coreMpmpm]))
    have e : ((1 : Int) : ℝ) * val3 U (.fc 2 1 3) = - x1a + 1 := by
      simp only [val3, nrm3, V3.dot, V3.cr, V3.sub, V3.smul, fa_2, fb_2, fc_2, sg_2, h0, h1, h2, h3, h5]; push_cast; ring
    rw [e] at h; exact h
  have f86 : 0 < - x1a + 1 := pos_sq (f := (- x1a + 1)) (q := (1)) (k := (1 : ℝ)) (r11) (by norm_num) (by ring)
  have r12 : 0 < - p4a + x6a := by
    have h := lit_frame hF (.fc 2 4 6) (by simp) (1) (hcore (.fc 2 4 6, 1) (by simp [coreMpmpm]))
    have e : ((1 : Int) : ℝ) * val3 U (.fc 2 4 6) = - p4a + x6a := by
      simp only [val3, nrm3, V3.dot, V3.cr, V3.sub, V3.smul, fa_2, fb_2, fc_2, sg_2, h0, h2, h4, h5, h6, hz4]; push_cast; ring
    rw [e] at h; exact h
  have f90 : 0 < - p4a + x6a := pos_sq (f := (- p4a + x6a)) (q := (1)) (k := (1 : ℝ)) (r12) (by norm_num) (by ring)
  have r13 : 0 < x1c * p4b - p4b := by
    have h := lit_frame hF (.fc 3 1 2) (by simp) (1) (hcore (.fc 3 1 2, 1) (by simp [coreMpmpm]))
    have e : ((1 : Int) : ℝ) * val3 U (.fc 3 1 2) = x1c * p4b - p4b := by
      simp only [val3, nrm3, V3.dot, V3.cr, V3.sub, V3.smul, fa_3, fb_3, fc_3, sg_3, h0, h1, h2, h3, h4, hz4]; push_cast; ring
    rw [e] at h; exact h
  have f121 : 0 < - x1c + 1 := pos_sq (f := (- x1c + 1)) (q := (p4b)) (k := (1 : ℝ)) (mul_pos r1 r13) (by norm_num) (by ring)
  have r14 : 0 < - x1c * x6b + x1b * x6c - x6c := by
    have h := lit_frame hF (.lv 0 3 6 1 5) (by simp) (-1) (hcore (.lv 0 3 6 1 5, -1) (by simp [coreMpmpm]))
    have e : ((-1 : Int) : ℝ) * val3 U (.lv 0 3 6 1 5) = - x1c * x6b + x1b * x6c - x6c := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h0, h1, h3, h5, h6]; push_cast; ring
    rw [e] at h; exact h
  have f126 : 0 < - x1c * x6b + x1b * x6c - x6c := pos_sq (f := (- x1c * x6b + x1b * x6c - x6c)) (q := (1)) (k := (1 : ℝ)) (r14) (by norm_num) (by ring)
  have r15 : 0 < p4b - x1c - x1b := by
    have h := lit_frame hF (.mv 0 3 1 4 2 5) (by simp) (1) (hcore (.mv 0 3 1 4 2 5, 1) (by simp [coreMpmpm]))
    have e : ((1 : Int) : ℝ) * val3 U (.mv 0 3 1 4 2 5) = p4b - x1c - x1b := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h0, h1, h2, h3, h4, h5, hz4]; push_cast; ring
    rw [e] at h; exact h
  have f135 : 0 < p4b - x1c - x1b := pos_sq (f := (p4b - x1c - x1b)) (q := (1)) (k := (1 : ℝ)) (r15) (by norm_num) (by ring)
  have r16 : 0 < - x1c * p4b + x1c * x6b - x1b * x6c + x6c := by
    have h := lit_frame hF (.mv 0 3 1 5 4 6) (by simp) (-1) (hcore (.mv 0 3 1 5 4 6, -1) (by simp [coreMpmpm]))
    have e : ((-1 : Int) : ℝ) * val3 U (.mv 0 3 1 5 4 6) = - x1c * p4b + x1c * x6b - x1b * x6c + x6c := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h0, h1, h3, h4, h5, h6, hz4]; push_cast; ring
    rw [e] at h; exact h
  have f141 : 0 < - x1c * p4b + x1c * x6b - x1b * x6c + x6c := pos_sq (f := (- x1c * p4b + x1c * x6b - x1b * x6c + x6c)) (q := (1)) (k := (1 : ℝ)) (r16) (by norm_num) (by ring)
  have r17 : 0 < - x1c * x6a + x1a * x6c + x6a := by
    have h := lit_frame hF (.lv 0 5 6 1 2) (by simp) (1) (hcore (.lv 0 5 6 1 2, 1) (by simp [coreMpmpm]))
    have e : ((1 : Int) : ℝ) * val3 U (.lv 0 5 6 1 2) = - x1c * x6a + x1a * x6c + x6a := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h0, h1, h2, h5, h6]; push_cast; ring
    rw [e] at h; exact h
  have f172 : 0 < - x1c * x6a + x1a * x6c + x6a := pos_sq (f := (- x1c * x6a + x1a * x6c + x6a)) (q := (1)) (k := (1 : ℝ)) (r17) (by norm_num) (by ring)
  have r18 : 0 < x1c + x1a - 1 := by
    have h := lit_frame hF (.lv 1 2 3 0 5) (by simp) (1) (hcore (.lv 1 2 3 0 5, 1) (by simp [coreMpmpm]))
    have e : ((1 : Int) : ℝ) * val3 U (.lv 1 2 3 0 5) = x1c + x1a - 1 := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h0, h1, h2, h3, h5]; push_cast; ring
    rw [e] at h; exact h
  have f177 : 0 < x1c + x1a - 1 := pos_sq (f := (x1c + x1a - 1)) (q := (1)) (k := (1 : ℝ)) (r18) (by norm_num) (by ring)
  have r19 : 0 < x1c * p4a - p4a + x1a := by
    have h := lit_frame hF (.lv 1 2 4 0 5) (by simp) (1) (hcore (.lv 1 2 4 0 5, 1) (by simp [coreMpmpm]))
    have e : ((1 : Int) : ℝ) * val3 U (.lv 1 2 4 0 5) = x1c * p4a - p4a + x1a := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h0, h1, h2, h4, h5, hz4]; push_cast; ring
    rw [e] at h; exact h
  have f178 : 0 < x1c * p4a - p4a + x1a := pos_sq (f := (x1c * p4a - p4a + x1a)) (q := (1)) (k := (1 : ℝ)) (r19) (by norm_num) (by ring)
  have r20 : 0 < - x1c * x6a + x1a * x6c + x6a - x1a := by
    have h := lit_frame hF (.fc 5 0 5) (by simp) (1) (hcore (.fc 5 0 5, 1) (by simp [coreMpmpm]))
    have e : ((1 : Int) : ℝ) * val3 U (.fc 5 0 5) = - x1c * x6a + x1a * x6c + x6a - x1a := by
      simp only [val3, nrm3, V3.dot, V3.cr, V3.sub, V3.smul, fa_5, fb_5, fc_5, sg_5, h0, h1, h2, h5, h6]; push_cast; ring
    rw [e] at h; exact h
  have f179 : 0 < - x1c * x6a + x1a * x6c + x6a - x1a := pos_sq (f := (- x1c * x6a + x1a * x6c + x6a - x1a)) (q := (1)) (k := (1 : ℝ)) (r20) (by norm_num) (by ring)
  have r21 : 0 < - x1c * x6a + x1a * x6c + x6a + x1c - 1 := by
    have h := lit_frame hF (.mv 0 5 1 2 3 6) (by simp) (-1) (hcore (.mv 0 5 1 2 3 6, -1) (by simp [coreMpmpm]))
    have e : ((-1 : Int) : ℝ) * val3 U (.mv 0 5 1 2 3 6) = - x1c * x6a + x1a * x6c + x6a + x1c - 1 := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h0, h1, h2, h3, h5, h6]; push_cast; ring
    rw [e] at h; exact h
  have f180 : 0 < - x1c * x6a + x1a * x6c + x6a + x1c - 1 := pos_sq (f := (- x1c * x6a + x1a * x6c + x6a + x1c - 1)) (q := (1)) (k := (1 : ℝ)) (r21) (by norm_num) (by ring)
  have r22 : 0 < x1c * p4a - x1c * x6a + x1a * x6c - p4a + x6a := by
    have h := lit_frame hF (.mv 0 5 1 2 4 6) (by simp) (-1) (hcore (.mv 0 5 1 2 4 6, -1) (by simp [coreMpmpm]))
    have e : ((-1 : Int) : ℝ) * val3 U (.mv 0 5 1 2 4 6) = x1c * p4a - x1c * x6a + x1a * x6c - p4a + x6a := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h0, h1, h2, h4, h5, h6, hz4]; push_cast; ring
    rw [e] at h; exact h
  have f181 : 0 < x1c * p4a - x1c * x6a + x1a * x6c - p4a + x6a := pos_sq (f := (x1c * p4a - x1c * x6a + x1a * x6c - p4a + x6a)) (q := (1)) (k := (1 : ℝ)) (r22) (by norm_num) (by ring)
  have r23 : 0 < p4a - x1c - x1a := by
    have h := lit_frame hF (.mv 0 5 1 4 2 3) (by simp) (-1) (hcore (.mv 0 5 1 4 2 3, -1) (by simp [coreMpmpm]))
    have e : ((-1 : Int) : ℝ) * val3 U (.mv 0 5 1 4 2 3) = p4a - x1c - x1a := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h0, h1, h2, h3, h4, h5, hz4]; push_cast; ring
    rw [e] at h; exact h
  have f187 : 0 < p4a - x1c - x1a := pos_sq (f := (p4a - x1c - x1a)) (q := (1)) (k := (1 : ℝ)) (r23) (by norm_num) (by ring)
  have r24 : 0 < x6c * p4b + x6c * p4a + x6b + x6a := by
    have h := lit_frame hF (.mv 0 6 2 4 3 5) (by simp) (-1) (hcore (.mv 0 6 2 4 3 5, -1) (by simp [coreMpmpm]))
    have e : ((-1 : Int) : ℝ) * val3 U (.mv 0 6 2 4 3 5) = x6c * p4b + x6c * p4a + x6b + x6a := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h0, h2, h3, h4, h5, h6, hz4]; push_cast; ring
    rw [e] at h; exact h
  have f218 : 0 < x6c * p4b + x6c * p4a + x6b + x6a := pos_sq (f := (x6c * p4b + x6c * p4a + x6b + x6a)) (q := (1)) (k := (1 : ℝ)) (r24) (by norm_num) (by ring)
  have r25 : 0 < x1c * p4a - x1c * x6a + x1b * p4a - x1b * x6a - x1a * p4b + x1a * x6c + x1a * x6b - p4a + x6a := by
    have h := lit_frame hF (.lv 1 2 5 4 6) (by simp) (1) (hcore (.lv 1 2 5 4 6, 1) (by simp [coreMpmpm]))
    have e : ((1 : Int) : ℝ) * val3 U (.lv 1 2 5 4 6) = x1c * p4a - x1c * x6a + x1b * p4a - x1b * x6a - x1a * p4b + x1a * x6c + x1a * x6b - p4a + x6a := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h1, h2, h4, h5, h6, hz4]; push_cast; ring
    rw [e] at h; exact h
  have f230 : 0 < x1c * p4a - x1c * x6a + x1b * p4a - x1b * x6a - x1a * p4b + x1a * x6c + x1a * x6b - p4a + x6a := pos_sq (f := (x1c * p4a - x1c * x6a + x1b * p4a - x1b * x6a - x1a * p4b + x1a * x6c + x1a * x6b - p4a + x6a)) (q := (1)) (k := (1 : ℝ)) (r25) (by norm_num) (by ring)
  have r26 : 0 < - x1c * x6b * p4a + x1c * x6a * p4b + x1b * x6c * p4a - x1a * x6c * p4b + x6c * p4b + x1c * x6b - x1b * p4a - x1b * x6c + x1a * p4b - p4b + x1b := by
    have h := lit_frame hF (.lv 1 3 4 2 6) (by simp) (-1) (hcore (.lv 1 3 4 2 6, -1) (by simp [coreMpmpm]))
    have e : ((-1 : Int) : ℝ) * val3 U (.lv 1 3 4 2 6) = - x1c * x6b * p4a + x1c * x6a * p4b + x1b * x6c * p4a - x1a * x6c * p4b + x6c * p4b + x1c * x6b - x1b * p4a - x1b * x6c + x1a * p4b - p4b + x1b := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h1, h2, h3, h4, h6, hz4]; push_cast; ring
    rw [e] at h; exact h
  have f241 : 0 < - x1c * x6b * p4a + x1c * x6a * p4b + x1b * x6c * p4a - x1a * x6c * p4b + x6c * p4b + x1c * x6b - x1b * p4a - x1b * x6c + x1a * p4b - p4b + x1b := pos_sq (f := (- x1c * x6b * p4a + x1c * x6a * p4b + x1b * x6c * p4a - x1a * x6c * p4b + x6c * p4b + x1c * x6b - x1b * p4a - x1b * x6c + x1a * p4b - p4b + x1b)) (q := (1)) (k := (1 : ℝ)) (r26) (by norm_num) (by ring)
  have r27 : 0 < - x1c * x6b - x1c * x6a + x1b * x6c + x1a * x6c - x6c + x1c := by
    have h := lit_frame hF (.br 1 3 5 6) (by simp) (-1) (hcore (.br 1 3 5 6, -1) (by simp [coreMpmpm]))
    have e : ((-1 : Int) : ℝ) * val3 U (.br 1 3 5 6) = - x1c * x6b - x1c * x6a + x1b * x6c + x1a * x6c - x6c + x1c := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h1, h3, h5, h6]; push_cast; ring
    rw [e] at h; exact h
  have f243 : 0 < - x1c * x6b - x1c * x6a + x1b * x6c + x1a * x6c - x6c + x1c := pos_sq (f := (- x1c * x6b - x1c * x6a + x1b * x6c + x1a * x6c - x6c + x1c)) (q := (1)) (k := (1 : ℝ)) (r27) (by norm_num) (by ring)
  have r28 : 0 < x1c * x6b * p4a - x1c * x6a * p4b - x1b * x6c * p4a + x1a * x6c * p4b + x6c * p4a + x1c * p4b + x1c * x6a - x1a * x6c - x1c := by
    have h := lit_frame hF (.lv 1 4 5 3 6) (by simp) (-1) (hcore (.lv 1 4 5 3 6, -1) (by simp [coreMpmpm]))
    have e : ((-1 : Int) : ℝ) * val3 U (.lv 1 4 5 3 6) = x1c * x6b * p4a - x1c * x6a * p4b - x1b * x6c * p4a + x1a * x6c * p4b + x6c * p4a + x1c * p4b + x1c * x6a - x1a * x6c - x1c := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h1, h3, h4, h5, h6, hz4]; push_cast; ring
    rw [e] at h; exact h
  have f260 : 0 < x1c * x6b * p4a - x1c * x6a * p4b - x1b * x6c * p4a + x1a * x6c * p4b + x6c * p4a + x1c * p4b + x1c * x6a - x1a * x6c - x1c := pos_sq (f := (x1c * x6b * p4a - x1c * x6a * p4b - x1b * x6c * p4a + x1a * x6c * p4b + x6c * p4a + x1c * p4b + x1c * x6a - x1a * x6c - x1c)) (q := (1)) (k := (1 : ℝ)) (r28) (by norm_num) (by ring)
  have r29 : 0 < x1c * x6b * p4a - x1c * x6a * p4b - x1b * x6c * p4a + x1a * x6c * p4b + x6c * p4a + x1c * p4b - x1c * x6b + x1b * x6c - x6c := by
    have h := lit_frame hF (.fc 8 1 5) (by simp) (-1) (hcore (.fc 8 1 5, -1) (by simp [coreMpmpm]))
    have e : ((-1 : Int) : ℝ) * val3 U (.fc 8 1 5) = x1c * x6b * p4a - x1c * x6a * p4b - x1b * x6c * p4a + x1a * x6c * p4b + x6c * p4a + x1c * p4b - x1c * x6b + x1b * x6c - x6c := by
      simp only [val3, nrm3, V3.dot, V3.cr, V3.sub, V3.smul, fa_8, fb_8, fc_8, sg_8, h1, h3, h4, h5, h6, hz4]; push_cast; ring
    rw [e] at h; exact h
  have f280 : 0 < x1c * x6b * p4a - x1c * x6a * p4b - x1b * x6c * p4a + x1a * x6c * p4b + x6c * p4a + x1c * p4b - x1c * x6b + x1b * x6c - x6c := pos_sq (f := (x1c * x6b * p4a - x1c * x6a * p4b - x1b * x6c * p4a + x1a * x6c * p4b + x6c * p4a + x1c * p4b - x1c * x6b + x1b * x6c - x6c)) (q := (1)) (k := (1 : ℝ)) (r29) (by norm_num) (by ring)
  have r30 : 0 < - x6a * x6c * p4b + x6a * x6b * p4a - x6a^2 * p4b - x6b * p4a + x6a * p4b := by
    have h := lit_frame hF (.nv 2 4 7) (by simp) (1) (hcore (.nv 2 4 7, 1) (by simp [coreMpmpm]))
    have e : ((1 : Int) : ℝ) * val3 U (.nv 2 4 7) = - x6a * x6c * p4b + x6a * x6b * p4a - x6a^2 * p4b - x6b * p4a + x6a * p4b := by
      simp only [val3, nrm3, V3.det, V3.dot, V3.cr, V3.sub, V3.smul, fa_2, fb_2, fc_2, sg_2, fa_4, fb_4, fc_4, sg_4, fa_7, fb_7, fc_7, sg_7, h0, h2, h3, h4, h5, h6, hz4]; push_cast; ring
    rw [e] at h; exact h
  have f306 : 0 < - x6a * x6c * p4b + x6a * x6b * p4a - x6a^2 * p4b - x6b * p4a + x6a * p4b := pos_sq (f := (- x6a * x6c * p4b + x6a * x6b * p4a - x6a^2 * p4b - x6b * p4a + x6a * p4b)) (q := (1)) (k := (1 : ℝ)) (r30) (by norm_num) (by ring)
  exact Minimality.PC.pcMpmpm x1a x1b x1c x6a x6b x6c p4a p4b f2 f10 f24 f26 f36 f42 f44 f64 f65 f66 f83 f86 f90 f121 f126 f135 f141 f172 f177 f178 f179 f180 f181 f187 f218 f230 f241 f243 f260 f280 f306

#print axioms coreFalseMpmpm

end Minimality.T24.SAT
