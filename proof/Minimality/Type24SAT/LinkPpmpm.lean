module

public import Minimality.Type24SAT.FrameInst24
public import Minimality.Type24SAT.PcPpmpm

@[expose] public section

/-! Link for the type 24 certificate Ppmpm (F24, generated from the certificate ppmpm_r4): the core literals of the clause, in
literal form, imply the certificate's strict polynomial conditions in the frame F24, hence False. -/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open scoped RealInnerProductSpace

namespace Minimality.T24.SAT
open Minimality

/-- The core of ppmpm_r4: the literals (kind, sign) of the clause NOT(core). -/
def corePpmpm : List (Lit24 × Int) := [(.br 1 4 5 6, 1), (.fc 0 3 6, 1), (.fc 1 2 5, -1), (.fc 1 3 5, 1), (.fc 3 2 6, -1), (.fc 7 1 4, 1), (.kv 3 0 4 3 5, -1), (.lv 0 1 4 2 5, 1), (.lv 0 2 4 1 6, 1), (.lv 0 2 6 4 5, 1), (.lv 1 3 4 0 2, -1), (.lv 1 3 5 4 6, 1), (.lv 1 3 6 4 5, -1), (.lv 2 4 5 0 1, 1), (.lv 2 5 6 0 1, 1), (.lv 4 5 6 2 3, 1), (.mv 0 1 2 5 3 4, 1), (.mv 0 3 1 2 5 6, -1), (.mv 0 3 1 4 2 5, -1), (.mv 0 3 1 6 2 4, -1), (.mv 0 4 1 2 5 6, -1), (.mv 0 5 1 2 3 6, -1), (.mv 0 5 1 2 4 6, 1), (.mv 0 6 1 2 3 4, 1), (.nv 1 6 8, -1), (.nv 2 4 7, 1), (.nv 2 5 8, 1)]

/-- **Core of Ppmpm is unsatisfiable** (for a type 24 configuration with `Convex24` and `QuadD`). -/
theorem coreFalsePpmpm (x : Nat → ℝ³) (hQ : QuadD x) (hC : Convex24 x)
    (hcore : ∀ p ∈ corePpmpm, LitHolds x p.1 p.2) : False := by
  obtain ⟨U, D, hF, h0, h3, h4, h1, h5z⟩ := frame24F x hC hQ
  rcases h2 : U 2 with ⟨x2a, x2b, x2c⟩
  rcases h6 : U 6 with ⟨x6a, x6b, x6c⟩
  rcases h5 : U 5 with ⟨al, be, z5⟩
  have hz5 : z5 = 0 := by simpa [h5] using h5z
  have hz0 : (U 0).z = 0 := by simp [h0]
  have hz3 : (U 3).z = 0 := by simp [h3]
  have hz4 : (U 4).z = 0 := by simp [h4]
  have hz5' : (U 5).z = 0 := h5z
  have r0 : 0 < x6c - x2c := by
    have h := lit_frame hF (.fc 3 2 6) (by simp) (-1) (hcore (.fc 3 2 6, -1) (by simp [corePpmpm]))
    have e : ((-1 : Int) : ℝ) * val3 U (.fc 3 2 6) = x6c - x2c := by
      simp only [val3, nrm3, V3.dot, V3.cr, V3.sub, V3.smul, fa_3, fb_3, fc_3, sg_3, h0, h2, h3, h4, h6]; push_cast; ring
    rw [e] at h; exact h
  have f123 : 0 < x6c - x2c := pos_sq (f := (x6c - x2c)) (q := (1)) (k := (1 : ℝ)) (r0) (by norm_num) (by ring)
  have r1 : 0 < x2c * be - x2c * x6b + x2b * x6c + be - x6b := by
    have h := lit_frame hF (.mv 0 3 1 2 5 6) (by simp) (-1) (hcore (.mv 0 3 1 2 5 6, -1) (by simp [corePpmpm]))
    have e : ((-1 : Int) : ℝ) * val3 U (.mv 0 3 1 2 5 6) = x2c * be - x2c * x6b + x2b * x6c + be - x6b := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h0, h1, h2, h3, h5, h6, hz5]; push_cast; ring
    rw [e] at h; exact h
  have f133 : 0 < x2c * be - x2c * x6b + x2b * x6c + be - x6b := pos_sq (f := (x2c * be - x2c * x6b + x2b * x6c + be - x6b)) (q := (1)) (k := (1 : ℝ)) (r1) (by norm_num) (by ring)
  have r2 : 0 < - be - x2c + x2b := by
    have h := lit_frame hF (.mv 0 3 1 4 2 5) (by simp) (-1) (hcore (.mv 0 3 1 4 2 5, -1) (by simp [corePpmpm]))
    have e : ((-1 : Int) : ℝ) * val3 U (.mv 0 3 1 4 2 5) = - be - x2c + x2b := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h0, h1, h2, h3, h4, h5, hz5]; push_cast; ring
    rw [e] at h; exact h
  have f135 : 0 < - be - x2c + x2b := pos_sq (f := (- be - x2c + x2b)) (q := (1)) (k := (1 : ℝ)) (r2) (by norm_num) (by ring)
  have r3 : 0 < - x2c * x6b + x2b * x6c - x6c + x2b - 1 := by
    have h := lit_frame hF (.mv 0 3 1 6 2 4) (by simp) (-1) (hcore (.mv 0 3 1 6 2 4, -1) (by simp [corePpmpm]))
    have e : ((-1 : Int) : ℝ) * val3 U (.mv 0 3 1 6 2 4) = - x2c * x6b + x2b * x6c - x6c + x2b - 1 := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h0, h1, h2, h3, h4, h6]; push_cast; ring
    rw [e] at h; exact h
  have f142 : 0 < - x2c * x6b + x2b * x6c - x6c + x2b - 1 := pos_sq (f := (- x2c * x6b + x2b * x6c - x6c + x2b - 1)) (q := (1)) (k := (1 : ℝ)) (r3) (by norm_num) (by ring)
  have r4 : 0 < - x2c * al + x2c * x6a - x2a * x6c - al + x6a := by
    have h := lit_frame hF (.mv 0 4 1 2 5 6) (by simp) (-1) (hcore (.mv 0 4 1 2 5 6, -1) (by simp [corePpmpm]))
    have e : ((-1 : Int) : ℝ) * val3 U (.mv 0 4 1 2 5 6) = - x2c * al + x2c * x6a - x2a * x6c - al + x6a := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h0, h1, h2, h4, h5, h6, hz5]; push_cast; ring
    rw [e] at h; exact h
  have f157 : 0 < - x2c * al + x2c * x6a - x2a * x6c - al + x6a := pos_sq (f := (- x2c * al + x2c * x6a - x2a * x6c - al + x6a)) (q := (1)) (k := (1 : ℝ)) (r4) (by norm_num) (by ring)
  have r5 : 0 < - x2c * x6b * al + x2c * x6a * be + x2b * x6c * al - x2a * x6c * be - x6b * al + x6a * be - x2c * be - be := by
    have h := lit_frame hF (.mv 0 5 1 2 3 6) (by simp) (-1) (hcore (.mv 0 5 1 2 3 6, -1) (by simp [corePpmpm]))
    have e : ((-1 : Int) : ℝ) * val3 U (.mv 0 5 1 2 3 6) = - x2c * x6b * al + x2c * x6a * be + x2b * x6c * al - x2a * x6c * be - x6b * al + x6a * be - x2c * be - be := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h0, h1, h2, h3, h5, h6, hz5]; push_cast; ring
    rw [e] at h; exact h
  have f180 : 0 < - x2c * x6b * al + x2c * x6a * be + x2b * x6c * al - x2a * x6c * be - x6b * al + x6a * be - x2c * be - be := pos_sq (f := (- x2c * x6b * al + x2c * x6a * be + x2b * x6c * al - x2a * x6c * be - x6b * al + x6a * be - x2c * be - be)) (q := (1)) (k := (1 : ℝ)) (r5) (by norm_num) (by ring)
  have r6 : 0 < x2c * x6b * al - x2c * x6a * be - x2b * x6c * al + x2a * x6c * be + x6b * al - x6a * be - x2c * al - al := by
    have h := lit_frame hF (.mv 0 5 1 2 4 6) (by simp) (1) (hcore (.mv 0 5 1 2 4 6, 1) (by simp [corePpmpm]))
    have e : ((1 : Int) : ℝ) * val3 U (.mv 0 5 1 2 4 6) = x2c * x6b * al - x2c * x6a * be - x2b * x6c * al + x2a * x6c * be + x6b * al - x6a * be - x2c * al - al := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h0, h1, h2, h4, h5, h6, hz5]; push_cast; ring
    rw [e] at h; exact h
  have f181 : 0 < x2c * x6b * al - x2c * x6a * be - x2b * x6c * al + x2a * x6c * be + x6b * al - x6a * be - x2c * al - al := pos_sq (f := (x2c * x6b * al - x2c * x6a * be - x2b * x6c * al + x2a * x6c * be + x6b * al - x6a * be - x2c * al - al)) (q := (1)) (k := (1 : ℝ)) (r6) (by norm_num) (by ring)
  have r7 : 0 < x2c * x6b + x2c * x6a - x2b * x6c - x2a * x6c + x6b + x6a := by
    have h := lit_frame hF (.mv 0 6 1 2 3 4) (by simp) (1) (hcore (.mv 0 6 1 2 3 4, 1) (by simp [corePpmpm]))
    have e : ((1 : Int) : ℝ) * val3 U (.mv 0 6 1 2 3 4) = x2c * x6b + x2c * x6a - x2b * x6c - x2a * x6c + x6b + x6a := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h0, h1, h2, h3, h4, h6]; push_cast; ring
    rw [e] at h; exact h
  have f199 : 0 < x2c * x6b + x2c * x6a - x2b * x6c - x2a * x6c + x6b + x6a := pos_sq (f := (x2c * x6b + x2c * x6a - x2b * x6c - x2a * x6c + x6b + x6a)) (q := (1)) (k := (1 : ℝ)) (r7) (by norm_num) (by ring)
  have r8 : 0 < - x2b * x6a + x2a * x6b + x2b := by
    have h := lit_frame hF (.fc 0 3 6) (by simp) (1) (hcore (.fc 0 3 6, 1) (by simp [corePpmpm]))
    have e : ((1 : Int) : ℝ) * val3 U (.fc 0 3 6) = - x2b * x6a + x2a * x6b + x2b := by
      simp only [val3, nrm3, V3.dot, V3.cr, V3.sub, V3.smul, fa_0, fb_0, fc_0, sg_0, h0, h1, h2, h3, h6]; push_cast; ring
    rw [e] at h; exact h
  have f24 : 0 < - x2b * x6a + x2a * x6b + x2b := pos_sq (f := (- x2b * x6a + x2a * x6b + x2b)) (q := (1)) (k := (1 : ℝ)) (r8) (by norm_num) (by ring)
  have r9 : 0 < - x6c * be - x6b * al + x6a * be + al + x6b - 1 := by
    have h := lit_frame hF (.lv 1 3 5 4 6) (by simp) (1) (hcore (.lv 1 3 5 4 6, 1) (by simp [corePpmpm]))
    have e : ((1 : Int) : ℝ) * val3 U (.lv 1 3 5 4 6) = - x6c * be - x6b * al + x6a * be + al + x6b - 1 := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h1, h3, h4, h5, h6, hz5]; push_cast; ring
    rw [e] at h; exact h
  have f246 : 0 < - x6c * be - x6b * al + x6a * be + al + x6b - 1 := pos_sq (f := (- x6c * be - x6b * al + x6a * be + al + x6b - 1)) (q := (1)) (k := (1 : ℝ)) (r9) (by norm_num) (by ring)
  have r10 : 0 < - x6c * be - x6b * al + x6a * be - be + x6c - x6a + 1 := by
    have h := lit_frame hF (.lv 1 3 6 4 5) (by simp) (-1) (hcore (.lv 1 3 6 4 5, -1) (by simp [corePpmpm]))
    have e : ((-1 : Int) : ℝ) * val3 U (.lv 1 3 6 4 5) = - x6c * be - x6b * al + x6a * be - be + x6c - x6a + 1 := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h1, h3, h4, h5, h6, hz5]; push_cast; ring
    rw [e] at h; exact h
  have f249 : 0 < - x6c * be - x6b * al + x6a * be - be + x6c - x6a + 1 := pos_sq (f := (- x6c * be - x6b * al + x6a * be - be + x6c - x6a + 1)) (q := (1)) (k := (1 : ℝ)) (r10) (by norm_num) (by ring)
  have r11 : 0 < - x6c * al + x6b * al - x6a * be - al + x6a := by
    have h := lit_frame hF (.br 1 4 5 6) (by simp) (1) (hcore (.br 1 4 5 6, 1) (by simp [corePpmpm]))
    have e : ((1 : Int) : ℝ) * val3 U (.br 1 4 5 6) = - x6c * al + x6b * al - x6a * be - al + x6a := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h1, h4, h5, h6, hz5]; push_cast; ring
    rw [e] at h; exact h
  have f257 : 0 < - x6c * al + x6b * al - x6a * be - al + x6a := pos_sq (f := (- x6c * al + x6b * al - x6a * be - al + x6a)) (q := (1)) (k := (1 : ℝ)) (r11) (by norm_num) (by ring)
  have r12 : 0 < - x2c * x6a + x2b * x6a + x2a * x6c - x2a * x6b - x6c + x6b + x2c - x2b := by
    have h := lit_frame hF (.fc 7 1 4) (by simp) (1) (hcore (.fc 7 1 4, 1) (by simp [corePpmpm]))
    have e : ((1 : Int) : ℝ) * val3 U (.fc 7 1 4) = - x2c * x6a + x2b * x6a + x2a * x6c - x2a * x6b - x6c + x6b + x2c - x2b := by
      simp only [val3, nrm3, V3.dot, V3.cr, V3.sub, V3.smul, fa_7, fb_7, fc_7, sg_7, h1, h2, h3, h4, h6]; push_cast; ring
    rw [e] at h; exact h
  have f265 : 0 < - x2c * x6a + x2b * x6a + x2a * x6c - x2a * x6b - x6c + x6b + x2c - x2b := pos_sq (f := (- x2c * x6a + x2b * x6a + x2a * x6c - x2a * x6b - x6c + x6b + x2c - x2b)) (q := (1)) (k := (1 : ℝ)) (r12) (by norm_num) (by ring)
  have r13 : 0 < x2c * x6b * al - x2c * x6a * be - x2b * x6c * al + x2a * x6c * be - x6c * be - x2c * al + x2c * x6a - x2a * x6c + x6c := by
    have h := lit_frame hF (.lv 4 5 6 2 3) (by simp) (1) (hcore (.lv 4 5 6 2 3, 1) (by simp [corePpmpm]))
    have e : ((1 : Int) : ℝ) * val3 U (.lv 4 5 6 2 3) = x2c * x6b * al - x2c * x6a * be - x2b * x6c * al + x2a * x6c * be - x6c * be - x2c * al + x2c * x6a - x2a * x6c + x6c := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h2, h3, h4, h5, h6, hz5]; push_cast; ring
    rw [e] at h; exact h
  have f290 : 0 < x2c * x6b * al - x2c * x6a * be - x2b * x6c * al + x2a * x6c * be - x6c * be - x2c * al + x2c * x6a - x2a * x6c + x6c := pos_sq (f := (x2c * x6b * al - x2c * x6a * be - x2b * x6c * al + x2a * x6c * be - x6c * be - x2c * al + x2c * x6a - x2a * x6c + x6c)) (q := (1)) (k := (1 : ℝ)) (r13) (by norm_num) (by ring)
  have r14 : 0 < - x2c * x6b^2 * al + x2c * x6a * x6b * be - x2c * x6a * x6b * al + x2c * x6a^2 * be + x2b * x6b * x6c * al + x2b * x6a * x6c * al - x2a * x6b * x6c * be - x2a * x6a * x6c * be + x6b * x6c * be + x6a * x6c * be + x2c * x6b * al + x2c * x6b^2 - x2c * x6a * be + x2c * x6a * x6b - x2b * x6b * x6c - x2b * x6a * x6c - x2c * x6b := by
    have h := lit_frame hF (.nv 1 6 8) (by simp) (-1) (hcore (.nv 1 6 8, -1) (by simp [corePpmpm]))
    have e : ((-1 : Int) : ℝ) * val3 U (.nv 1 6 8) = - x2c * x6b^2 * al + x2c * x6a * x6b * be - x2c * x6a * x6b * al + x2c * x6a^2 * be + x2b * x6b * x6c * al + x2b * x6a * x6c * al - x2a * x6b * x6c * be - x2a * x6a * x6c * be + x6b * x6c * be + x6a * x6c * be + x2c * x6b * al + x2c * x6b^2 - x2c * x6a * be + x2c * x6a * x6b - x2b * x6b * x6c - x2b * x6a * x6c - x2c * x6b := by
      simp only [val3, nrm3, V3.det, V3.dot, V3.cr, V3.sub, V3.smul, fa_1, fb_1, fc_1, sg_1, fa_6, fb_6, fc_6, sg_6, fa_8, fb_8, fc_8, sg_8, h0, h1, h2, h3, h4, h5, h6, hz5]; push_cast; ring
    rw [e] at h; exact h
  have f304 : 0 < - x2c * x6b^2 * al + x2c * x6a * x6b * be - x2c * x6a * x6b * al + x2c * x6a^2 * be + x2b * x6b * x6c * al + x2b * x6a * x6c * al - x2a * x6b * x6c * be - x2a * x6a * x6c * be + x6b * x6c * be + x6a * x6c * be + x2c * x6b * al + x2c * x6b^2 - x2c * x6a * be + x2c * x6a * x6b - x2b * x6b * x6c - x2b * x6a * x6c - x2c * x6b := pos_sq (f := (- x2c * x6b^2 * al + x2c * x6a * x6b * be - x2c * x6a * x6b * al + x2c * x6a^2 * be + x2b * x6b * x6c * al + x2b * x6a * x6c * al - x2a * x6b * x6c * be - x2a * x6a * x6c * be + x6b * x6c * be + x6a * x6c * be + x2c * x6b * al + x2c * x6b^2 - x2c * x6a * be + x2c * x6a * x6b - x2b * x6b * x6c - x2b * x6a * x6c - x2c * x6b)) (q := (1)) (k := (1 : ℝ)) (r14) (by norm_num) (by ring)
  have r15 : 0 < x2c^2 * x6a * x6b * al - x2c^2 * x6a^2 * be - x2b * x2c * x6a * x6c * al - x2a * x2c * x6b * x6c * al + 2 * x2a * x2c * x6a * x6c * be + x2a * x2b * x6c^2 * al - x2a^2 * x6c^2 * be + x2c * x6b * x6c * al - x2c * x6a * x6c * be + x2c^2 * x6a * be - x2b * x6c^2 * al + x2a * x6c^2 * be - x2a * x2c * x6c * be := by
    have h := lit_frame hF (.nv 2 4 7) (by simp) (1) (hcore (.nv 2 4 7, 1) (by simp [corePpmpm]))
    have e : ((1 : Int) : ℝ) * val3 U (.nv 2 4 7) = x2c^2 * x6a * x6b * al - x2c^2 * x6a^2 * be - x2b * x2c * x6a * x6c * al - x2a * x2c * x6b * x6c * al + 2 * x2a * x2c * x6a * x6c * be + x2a * x2b * x6c^2 * al - x2a^2 * x6c^2 * be + x2c * x6b * x6c * al - x2c * x6a * x6c * be + x2c^2 * x6a * be - x2b * x6c^2 * al + x2a * x6c^2 * be - x2a * x2c * x6c * be := by
      simp only [val3, nrm3, V3.det, V3.dot, V3.cr, V3.sub, V3.smul, fa_2, fb_2, fc_2, sg_2, fa_4, fb_4, fc_4, sg_4, fa_7, fb_7, fc_7, sg_7, h0, h2, h3, h4, h5, h6, hz5]; push_cast; ring
    rw [e] at h; exact h
  have f306 : 0 < x2c^2 * x6a * x6b * al - x2c^2 * x6a^2 * be - x2b * x2c * x6a * x6c * al - x2a * x2c * x6b * x6c * al + 2 * x2a * x2c * x6a * x6c * be + x2a * x2b * x6c^2 * al - x2a^2 * x6c^2 * be + x2c * x6b * x6c * al - x2c * x6a * x6c * be + x2c^2 * x6a * be - x2b * x6c^2 * al + x2a * x6c^2 * be - x2a * x2c * x6c * be := pos_sq (f := (x2c^2 * x6a * x6b * al - x2c^2 * x6a^2 * be - x2b * x2c * x6a * x6c * al - x2a * x2c * x6b * x6c * al + 2 * x2a * x2c * x6a * x6c * be + x2a * x2b * x6c^2 * al - x2a^2 * x6c^2 * be + x2c * x6b * x6c * al - x2c * x6a * x6c * be + x2c^2 * x6a * be - x2b * x6c^2 * al + x2a * x6c^2 * be - x2a * x2c * x6c * be)) (q := (1)) (k := (1 : ℝ)) (r15) (by norm_num) (by ring)
  have r16 : 0 < - x2c^2 * x6b^2 * al + x2c^2 * x6a * x6b * be - x2c^2 * x6a * x6b * al + x2c^2 * x6a^2 * be + 2 * x2b * x2c * x6b * x6c * al - x2b * x2c * x6a * x6c * be + x2b * x2c * x6a * x6c * al - x2b^2 * x6c^2 * al - x2a * x2c * x6b * x6c * be + x2a * x2c * x6b * x6c * al - 2 * x2a * x2c * x6a * x6c * be + x2a * x2b * x6c^2 * be - x2a * x2b * x6c^2 * al + x2a^2 * x6c^2 * be - x2c * x6b^2 * al + x2c * x6a * x6b * be - x2c * x6a * x6b * al + x2c * x6a^2 * be + x2c^2 * x6b * al - x2c^2 * x6a * be + x2b * x6b * x6c * al + x2b * x6a * x6c * al - x2b * x2c * x6c * al + x2b * x2c * x6b * al + x2b * x2c * x6a * al - x2b^2 * x6c * al - x2a * x6b * x6c * be - x2a * x6a * x6c * be + x2a * x2c * x6c * be - x2a * x2c * x6b * be - x2a * x2c * x6a * be + x2a * x2b * x6c * be - x2a * x2b * x6c * al + x2a^2 * x6c * be + x2c * x6b * al - x2c * x6a * be - x2b * x2c * al + x2a * x2c * be := by
    have h := lit_frame hF (.nv 2 5 8) (by simp) (1) (hcore (.nv 2 5 8, 1) (by simp [corePpmpm]))
    have e : ((1 : Int) : ℝ) * val3 U (.nv 2 5 8) = - x2c^2 * x6b^2 * al + x2c^2 * x6a * x6b * be - x2c^2 * x6a * x6b * al + x2c^2 * x6a^2 * be + 2 * x2b * x2c * x6b * x6c * al - x2b * x2c * x6a * x6c * be + x2b * x2c * x6a * x6c * al - x2b^2 * x6c^2 * al - x2a * x2c * x6b * x6c * be + x2a * x2c * x6b * x6c * al - 2 * x2a * x2c * x6a * x6c * be + x2a * x2b * x6c^2 * be - x2a * x2b * x6c^2 * al + x2a^2 * x6c^2 * be - x2c * x6b^2 * al + x2c * x6a * x6b * be - x2c * x6a * x6b * al + x2c * x6a^2 * be + x2c^2 * x6b * al - x2c^2 * x6a * be + x2b * x6b * x6c * al + x2b * x6a * x6c * al - x2b * x2c * x6c * al + x2b * x2c * x6b * al + x2b * x2c * x6a * al - x2b^2 * x6c * al - x2a * x6b * x6c * be - x2a * x6a * x6c * be + x2a * x2c * x6c * be - x2a * x2c * x6b * be - x2a * x2c * x6a * be + x2a * x2b * x6c * be - x2a * x2b * x6c * al + x2a^2 * x6c * be + x2c * x6b * al - x2c * x6a * be - x2b * x2c * al + x2a * x2c * be := by
      simp only [val3, nrm3, V3.det, V3.dot, V3.cr, V3.sub, V3.smul, fa_2, fb_2, fc_2, sg_2, fa_5, fb_5, fc_5, sg_5, fa_8, fb_8, fc_8, sg_8, h0, h1, h2, h3, h4, h5, h6, hz5]; push_cast; ring
    rw [e] at h; exact h
  have f307 : 0 < - x2c^2 * x6b^2 * al + x2c^2 * x6a * x6b * be - x2c^2 * x6a * x6b * al + x2c^2 * x6a^2 * be + 2 * x2b * x2c * x6b * x6c * al - x2b * x2c * x6a * x6c * be + x2b * x2c * x6a * x6c * al - x2b^2 * x6c^2 * al - x2a * x2c * x6b * x6c * be + x2a * x2c * x6b * x6c * al - 2 * x2a * x2c * x6a * x6c * be + x2a * x2b * x6c^2 * be - x2a * x2b * x6c^2 * al + x2a^2 * x6c^2 * be - x2c * x6b^2 * al + x2c * x6a * x6b * be - x2c * x6a * x6b * al + x2c * x6a^2 * be + x2c^2 * x6b * al - x2c^2 * x6a * be + x2b * x6b * x6c * al + x2b * x6a * x6c * al - x2b * x2c * x6c * al + x2b * x2c * x6b * al + x2b * x2c * x6a * al - x2b^2 * x6c * al - x2a * x6b * x6c * be - x2a * x6a * x6c * be + x2a * x2c * x6c * be - x2a * x2c * x6b * be - x2a * x2c * x6a * be + x2a * x2b * x6c * be - x2a * x2b * x6c * al + x2a^2 * x6c * be + x2c * x6b * al - x2c * x6a * be - x2b * x2c * al + x2a * x2c * be := pos_sq (f := (- x2c^2 * x6b^2 * al + x2c^2 * x6a * x6b * be - x2c^2 * x6a * x6b * al + x2c^2 * x6a^2 * be + 2 * x2b * x2c * x6b * x6c * al - x2b * x2c * x6a * x6c * be + x2b * x2c * x6a * x6c * al - x2b^2 * x6c^2 * al - x2a * x2c * x6b * x6c * be + x2a * x2c * x6b * x6c * al - 2 * x2a * x2c * x6a * x6c * be + x2a * x2b * x6c^2 * be - x2a * x2b * x6c^2 * al + x2a^2 * x6c^2 * be - x2c * x6b^2 * al + x2c * x6a * x6b * be - x2c * x6a * x6b * al + x2c * x6a^2 * be + x2c^2 * x6b * al - x2c^2 * x6a * be + x2b * x6b * x6c * al + x2b * x6a * x6c * al - x2b * x2c * x6c * al + x2b * x2c * x6b * al + x2b * x2c * x6a * al - x2b^2 * x6c * al - x2a * x6b * x6c * be - x2a * x6a * x6c * be + x2a * x2c * x6c * be - x2a * x2c * x6b * be - x2a * x2c * x6a * be + x2a * x2b * x6c * be - x2a * x2b * x6c * al + x2a^2 * x6c * be + x2c * x6b * al - x2c * x6a * be - x2b * x2c * al + x2a * x2c * be)) (q := (1)) (k := (1 : ℝ)) (r16) (by norm_num) (by ring)
  have r17 : 0 < - al + x2a := by
    have h := lit_frame hF (.lv 0 1 4 2 5) (by simp) (1) (hcore (.lv 0 1 4 2 5, 1) (by simp [corePpmpm]))
    have e : ((1 : Int) : ℝ) * val3 U (.lv 0 1 4 2 5) = - al + x2a := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h0, h1, h2, h4, h5, hz5]; push_cast; ring
    rw [e] at h; exact h
  have f34 : 0 < - al + x2a := pos_sq (f := (- al + x2a)) (q := (1)) (k := (1 : ℝ)) (r17) (by norm_num) (by ring)
  have r18 : 0 < al - 1 := by
    have h := kv_frame hF 3 0 4 3 5 (-1) (by simp [hz0]) (by simp [hz4]) (by simp [hz3]) (by simp [hz5']) (by simp [fa_3, hz0]) (by simp [fb_3, hz3]) (by simp [fc_3, hz4]) (hcore (.kv 3 0 4 3 5, -1) (by simp [corePpmpm]))
    have e : ((-1 : Int) : ℝ) * val3 U (.kv 3 0 4 3 5) = al - 1 := by
      simp only [val3, nrm3, V3.dot, V3.cr, V3.sub, V3.smul, fa_3, fb_3, fc_3, sg_3, h0, h3, h4, h5, hz5]; push_cast; ring
    rw [e] at h; exact h
  have f36 : 0 < al - 1 := pos_sq (f := (al - 1)) (q := (1)) (k := (1 : ℝ)) (r18) (by norm_num) (by ring)
  have r19 : 0 < - x6b * al + x6a * be - x2b * x6a + x2a * x6b := by
    have h := lit_frame hF (.fc 1 2 5) (by simp) (-1) (hcore (.fc 1 2 5, -1) (by simp [corePpmpm]))
    have e : ((-1 : Int) : ℝ) * val3 U (.fc 1 2 5) = - x6b * al + x6a * be - x2b * x6a + x2a * x6b := by
      simp only [val3, nrm3, V3.dot, V3.cr, V3.sub, V3.smul, fa_1, fb_1, fc_1, sg_1, h0, h1, h2, h5, h6, hz5]; push_cast; ring
    rw [e] at h; exact h
  have f47 : 0 < - x6b * al + x6a * be - x2b * x6a + x2a * x6b := pos_sq (f := (- x6b * al + x6a * be - x2b * x6a + x2a * x6b)) (q := (1)) (k := (1 : ℝ)) (r19) (by norm_num) (by ring)
  have r20 : 0 < x6b * al - x6a * be - x6b := by
    have h := lit_frame hF (.fc 1 3 5) (by simp) (1) (hcore (.fc 1 3 5, 1) (by simp [corePpmpm]))
    have e : ((1 : Int) : ℝ) * val3 U (.fc 1 3 5) = x6b * al - x6a * be - x6b := by
      simp only [val3, nrm3, V3.dot, V3.cr, V3.sub, V3.smul, fa_1, fb_1, fc_1, sg_1, h0, h1, h3, h5, h6, hz5]; push_cast; ring
    rw [e] at h; exact h
  have f49 : 0 < x6b * al - x6a * be - x6b := pos_sq (f := (x6b * al - x6a * be - x6b)) (q := (1)) (k := (1 : ℝ)) (r20) (by norm_num) (by ring)
  have r21 : 0 < x2b * al - x2a * be - al + x2a := by
    have h := lit_frame hF (.lv 2 4 5 0 1) (by simp) (1) (hcore (.lv 2 4 5 0 1, 1) (by simp [corePpmpm]))
    have e : ((1 : Int) : ℝ) * val3 U (.lv 2 4 5 0 1) = x2b * al - x2a * be - al + x2a := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h0, h1, h2, h4, h5, hz5]; push_cast; ring
    rw [e] at h; exact h
  have f58 : 0 < x2b * al - x2a * be - al + x2a := pos_sq (f := (x2b * al - x2a * be - al + x2a)) (q := (1)) (k := (1 : ℝ)) (r21) (by norm_num) (by ring)
  have r22 : 0 < x6b * al - x6a * be - x2b * al + x2b * x6a + x2a * be - x2a * x6b := by
    have h := lit_frame hF (.lv 2 5 6 0 1) (by simp) (1) (hcore (.lv 2 5 6 0 1, 1) (by simp [corePpmpm]))
    have e : ((1 : Int) : ℝ) * val3 U (.lv 2 5 6 0 1) = x6b * al - x6a * be - x2b * al + x2b * x6a + x2a * be - x2a * x6b := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h0, h1, h2, h5, h6, hz5]; push_cast; ring
    rw [e] at h; exact h
  have f63 : 0 < x6b * al - x6a * be - x2b * al + x2b * x6a + x2a * be - x2a * x6b := pos_sq (f := (x6b * al - x6a * be - x2b * al + x2b * x6a + x2a * be - x2a * x6b)) (q := (1)) (k := (1 : ℝ)) (r22) (by norm_num) (by ring)
  have r23 : 0 < be + al - x2b - x2a := by
    have h := lit_frame hF (.mv 0 1 2 5 3 4) (by simp) (1) (hcore (.mv 0 1 2 5 3 4, 1) (by simp [corePpmpm]))
    have e : ((1 : Int) : ℝ) * val3 U (.mv 0 1 2 5 3 4) = be + al - x2b - x2a := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h0, h1, h2, h3, h4, h5, hz5]; push_cast; ring
    rw [e] at h; exact h
  have f64 : 0 < be + al - x2b - x2a := pos_sq (f := (be + al - x2b - x2a)) (q := (1)) (k := (1 : ℝ)) (r23) (by norm_num) (by ring)
  have r24 : 0 < x2c * x6a - x2a * x6c - x2a := by
    have h := lit_frame hF (.lv 0 2 4 1 6) (by simp) (1) (hcore (.lv 0 2 4 1 6, 1) (by simp [corePpmpm]))
    have e : ((1 : Int) : ℝ) * val3 U (.lv 0 2 4 1 6) = x2c * x6a - x2a * x6c - x2a := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h0, h1, h2, h4, h6]; push_cast; ring
    rw [e] at h; exact h
  have f83 : 0 < x2c * x6a - x2a * x6c - x2a := pos_sq (f := (x2c * x6a - x2a * x6c - x2a)) (q := (1)) (k := (1 : ℝ)) (r24) (by norm_num) (by ring)
  have r25 : 0 < x2c * x6b * al - x2c * x6a * be - x2b * x6c * al + x2a * x6c * be + x2c * x6a - x2a * x6c := by
    have h := lit_frame hF (.lv 0 2 6 4 5) (by simp) (1) (hcore (.lv 0 2 6 4 5, 1) (by simp [corePpmpm]))
    have e : ((1 : Int) : ℝ) * val3 U (.lv 0 2 6 4 5) = x2c * x6b * al - x2c * x6a * be - x2b * x6c * al + x2a * x6c * be + x2c * x6a - x2a * x6c := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h0, h2, h4, h5, h6, hz5]; push_cast; ring
    rw [e] at h; exact h
  have f96 : 0 < x2c * x6b * al - x2c * x6a * be - x2b * x6c * al + x2a * x6c * be + x2c * x6a - x2a * x6c := pos_sq (f := (x2c * x6b * al - x2c * x6a * be - x2b * x6c * al + x2a * x6c * be + x2c * x6a - x2a * x6c)) (q := (1)) (k := (1 : ℝ)) (r25) (by norm_num) (by ring)
  have r26 : 0 < x2c - x2b - x2a := by
    have h := lit_frame hF (.lv 1 3 4 0 2) (by simp) (-1) (hcore (.lv 1 3 4 0 2, -1) (by simp [corePpmpm]))
    have e : ((-1 : Int) : ℝ) * val3 U (.lv 1 3 4 0 2) = x2c - x2b - x2a := by
      simp only [val3, V3.det, V3.dot, V3.cr, V3.sub, h0, h1, h2, h3, h4]; push_cast; ring
    rw [e] at h; exact h
  have f97 : 0 < x2c - x2b - x2a := pos_sq (f := (x2c - x2b - x2a)) (q := (1)) (k := (1 : ℝ)) (r26) (by norm_num) (by ring)
  exact Minimality.PC.pcPpmpm x2a x2b x2c x6a x6b x6c al be f123 f133 f135 f142 f157 f180 f181 f199 f24 f246 f249 f257 f265 f290 f304 f306 f307 f34 f36 f47 f49 f58 f63 f64 f83 f96 f97

#print axioms coreFalsePpmpm

end Minimality.T24.SAT
