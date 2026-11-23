module

public import Minimality.Type24E23

@[expose] public section

/-!
# Type 24: the triple tie `z0 = z2 = z4` at `w63` with `(*)1` (TIES24P T2b, `T2B.md`)

On the triple tie at `w = x 3 - x 6` (i.e. `w ⊥` plane `x0 x2 x4`) with
`0 ≤ ⟪x0 - x2, x2 - x6⟫`, the view `b = t2bView x = mu0 (x0 - x2) + mu4 (x4 - x2)`
(`= M (x2 - q)`, `M = mu3 + mu6 > 0`, `q` the Radon point of `{0,2,4} | {3,6}` on line 36),
with level-2 tilt `x2 - x0`, gives `LexAny`, unless `s = mu0 + mu4 > 0`, where facet `346`
has a facet cell (view `-b - (s/2)(x2 - x4)`).

* Facings at `b` are facet-value identities (`t2b_fac1`, `t2b_fac2`), valid for every shape:
  `A C F G` up, `I` down, `H` edge-on, `D`, `E` of the sign of `s`, and `B` up when `s ≥ 0`.
* Depths (`t2b_depths`, rel. `x6`): `t3 = t6 = 0` (tie), `0 < t2 ≤ t0` (`(*)1`), `t1 > 0`
  (frame at `x1`, `x3` row), `t5 > 0` (quad `0345` + Radon on depth and on facet `236`),
  `t1 < t0 ∨ t5 < t0` (identity `(t5 - t0) + K5 (t1 - t0) = b5 (t2 - t0) - c5 t0`).
* Rims: `B` up: `0 6 3 5`; `B` lex-down: `0 1 6 3 5`. No `CbarIn`, `c3 > 1`, `mu* > 0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace
open Finset

namespace Minimality.T24.A20

open Minimality Minimality.H21 Minimality.H24.SAT Minimality.T24.SAT Minimality.T24.RCell
  Minimality.T24.M4 Minimality.T24 Minimality.LexCell Minimality.T24.Sym

/-- The T2b view `M (x2 - q)` (`q` the Radon point of `x0 x2 x4 | x3 x6` on line `36`). -/
noncomputable def t2bView (x : Fin 7 → ℝ³) : ℝ³ := mu0 x • (x 0 - x 2) + mu4 x • (x 4 - x 2)

/-- Second form of the view (by the Radon identity). -/
theorem t2bView_alt {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) :
    t2bView x = mu3 x • (x 2 - x 3) + mu6 x • (x 2 - x 6) := by
  have h := radon02346 F
  have hs : mu2 x = -(mu0 x + mu3 x + mu4 x + mu6 x) := by linarith [radon02346_sum x]
  rw [hs] at h
  unfold t2bView
  linear_combination (norm := module) h

theorem t2b_fac1 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : Fin 9) :
    ⟪F.N t, t2bView x⟫ = mu0 x * (F.f t (x 0) - F.f t (x 2)) +
      mu4 x * (F.f t (x 4) - F.f t (x 2)) := by
  simp only [t2bView, inner_add_right, real_inner_smul_right, ← F.hN]

theorem t2b_fac2 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (t : Fin 9) :
    ⟪F.N t, t2bView x⟫ = mu3 x * (F.f t (x 2) - F.f t (x 3)) +
      mu6 x * (F.f t (x 2) - F.f t (x 6)) := by
  rw [t2bView_alt F]
  simp only [inner_add_right, real_inner_smul_right, ← F.hN]

/-- Real core of `t5 > 0` (D1): quad `0345` and Radon, on the depth `t` and on `Y = -f_236`. -/
theorem t2b_d1_core {t0 t2 t4 t5 Y0 Y4 Y5 m0 m2 m4 al be : ℝ} (ht0 : 0 < t0) (ht2 : 0 < t2)
    (hY0 : 0 < Y0) (hY4 : 0 < Y4) (hY5 : 0 < Y5) (hm0 : 0 < m0) (hm2 : m2 < 0)
    (hal : 0 < al) (hbe : 0 < be)
    (hzr : m0 * t0 + m2 * t2 + m4 * t4 = 0) (hYr : m0 * Y0 + m4 * Y4 = 0)
    (hzq : -t0 = al * (t5 - t0) + be * (t4 - t0)) (hYq : -Y0 = al * (Y5 - Y0) + be * (Y4 - Y0)) :
    0 < t5 := by
  have h1 : m0 * (t0 * Y4 - Y0 * t4) = -m2 * Y4 * t2 := by
    linear_combination Y4 * hzr - t4 * hYr
  have h2 : 0 < t0 * Y4 - Y0 * t4 := by
    have : 0 < m0 * (t0 * Y4 - Y0 * t4) := by
      rw [h1]; exact mul_pos (mul_pos (neg_pos.2 hm2) hY4) ht2
    exact (mul_pos_iff_of_pos_left hm0).mp this
  have h3 : al * (Y0 * t5 - t0 * Y5) = be * (t0 * Y4 - Y0 * t4) := by
    linear_combination t0 * hYq - Y0 * hzq
  have h4 : 0 < Y0 * t5 - t0 * Y5 := by
    have : 0 < al * (Y0 * t5 - t0 * Y5) := by rw [h3]; exact mul_pos hbe h2
    exact (mul_pos_iff_of_pos_left hal).mp this
  have h5 : 0 < Y0 * t5 := by nlinarith [mul_pos ht0 hY5]
  exact (mul_pos_iff_of_pos_left hY0).mp h5

/-- **Depth facts at the T2b view** (relative to `x 6`). -/
theorem t2b_depths {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (htie : ⟪x 0, x 3 - x 6⟫ = ⟪x 2, x 3 - x 6⟫ ∧ ⟪x 2, x 3 - x 6⟫ = ⟪x 4, x 3 - x 6⟫)
    (hstar : 0 ≤ ⟪x 0 - x 2, x 2 - x 6⟫) :
    ⟪x 3, t2bView x⟫ = ⟪x 6, t2bView x⟫ ∧ ⟪x 6, t2bView x⟫ < ⟪x 2, t2bView x⟫ ∧
    ⟪x 2, t2bView x⟫ ≤ ⟪x 0, t2bView x⟫ ∧ ⟪x 6, t2bView x⟫ < ⟪x 1, t2bView x⟫ ∧
    ⟪x 6, t2bView x⟫ < ⟪x 5, t2bView x⟫ ∧
    (⟪x 1, t2bView x⟫ < ⟪x 0, t2bView x⟫ ∨ ⟪x 5, t2bView x⟫ < ⟪x 0, t2bView x⟫) := by
  obtain ⟨hm0, hm2, hm3, hm4, hm6⟩ := radon02346_signs F
  have T := type24OfFac F
  set b := t2bView x with hb
  have hb2 : b = mu3 x • (x 2 - x 3) + mu6 x • (x 2 - x 6) := t2bView_alt F
  -- tie: `z3 = z6`
  have e1 : ⟪x 3 - x 6, x 0 - x 2⟫ = 0 := by
    rw [real_inner_comm, inner_sub_left]; linarith [htie.1]
  have e2 : ⟪x 3 - x 6, x 4 - x 2⟫ = 0 := by
    rw [real_inner_comm, inner_sub_left]; linarith [htie.2]
  have h36 : ⟪x 3, b⟫ = ⟪x 6, b⟫ := by
    have : ⟪x 3 - x 6, b⟫ = 0 := by
      simp only [hb, t2bView, inner_add_right, real_inner_smul_right, e1, e2]; ring
    rw [inner_sub_left] at this; linarith
  -- `b ≠ 0` (facet `012` is up) and `|b|^2 = (mu3 + mu6) (z2 - z6)`
  have hA : 0 < ⟪F.N 0, b⟫ := by
    rw [hb, t2b_fac2 F, F.zero 0 2 (by decide)]
    nlinarith [mul_pos hm3 (neg_pos.2 (F.neg 0 3 (by decide))),
      mul_pos hm6 (neg_pos.2 (F.neg 0 6 (by decide)))]
  have hbne : b ≠ 0 := by
    rintro h0; rw [h0, inner_zero_right] at hA; exact lt_irrefl _ hA
  have hbb : ⟪b, b⟫ = mu3 x * (⟪x 2, b⟫ - ⟪x 3, b⟫) + mu6 x * (⟪x 2, b⟫ - ⟪x 6, b⟫) := by
    have h := congrArg (fun v => ⟪v, b⟫) hb2
    simp only [inner_add_left, real_inner_smul_left, inner_sub_left] at h
    exact h
  have hbpos : 0 < ⟪b, b⟫ := real_inner_self_pos.mpr hbne
  have h62 : ⟪x 6, b⟫ < ⟪x 2, b⟫ := by
    rw [h36] at hbb
    by_contra hn; push Not at hn
    nlinarith [mul_nonneg (add_pos hm3 hm6).le (sub_nonneg.2 hn)]
  -- `(*)1`: `z0 - z2 = (mu3 + mu6) ⟪x0 - x2, x2 - x6⟫`
  have e3 : ⟪x 0 - x 2, x 2 - x 3⟫ = ⟪x 0 - x 2, x 2 - x 6⟫ := by
    have h23 : x 2 - x 3 = (x 2 - x 6) - (x 3 - x 6) := by abel
    rw [h23, inner_sub_right, inner_sub_left (x 0) (x 2) (x 3 - x 6)]
    linarith [htie.1]
  have h20 : ⟪x 2, b⟫ ≤ ⟪x 0, b⟫ := by
    have h : ⟪x 0 - x 2, b⟫ = mu3 x * ⟪x 0 - x 2, x 2 - x 3⟫ + mu6 x * ⟪x 0 - x 2, x 2 - x 6⟫ := by
      rw [hb2, inner_add_right, real_inner_smul_right, real_inner_smul_right]
    rw [e3, inner_sub_left] at h
    nlinarith [mul_nonneg (add_pos hm3 hm6).le hstar]
  -- frame rows of `x 3` and `x 5` at vertex `1`, on the depth
  have row : ∀ v : Fin 7, ⟪x v, b⟫ = ⟪x 1, b⟫ + oblX0 x v * (⟪x 0, b⟫ - ⟪x 1, b⟫) +
      oblX2 x v * (⟪x 2, b⟫ - ⟪x 1, b⟫) + oblX6 x v * (⟪x 6, b⟫ - ⟪x 1, b⟫) := by
    intro v
    have h := congrArg (fun y => ⟪y, b⟫) (T.rep v)
    simp only [inner_add_left, real_inner_smul_left, inner_sub_left] at h
    exact h
  have ha3 : 0 < oblX0 x 3 := T.X0_pos (v := 3) (by decide)
  have hb3 : 0 < oblX2 x 3 := T.X2_pos (v := 3) (by decide)
  have hb5 : 0 < oblX2 x 5 := T.X2_pos (v := 5) (by decide)
  have hc5 : 0 < oblX6 x 5 := T.X6_pos (v := 5) (by decide)
  have hK3 : 0 < oblX0 x 3 + oblX2 x 3 + oblX6 x 3 - 1 := by
    have : mu4 x = 1 - (oblX0 x 3 + oblX2 x 3 + oblX6 x 3) := rfl
    linarith
  have hK5 : 0 < oblX0 x 5 + oblX2 x 5 + oblX6 x 5 - 1 := by
    have hom5_eq : oblX6 x 5 * omega5 x = oblX0 x 5 + oblX2 x 5 - 1 := by
      simp only [omega5]; field_simp
    have := mul_pos hc5 (one_add_omega5_pos F)
    nlinarith
  -- D2: `t1 > 0`
  have r3 := row 3
  have h61 : ⟪x 6, b⟫ < ⟪x 1, b⟫ := by
    have key : (oblX0 x 3 + oblX2 x 3 + oblX6 x 3 - 1) * (⟪x 1, b⟫ - ⟪x 6, b⟫) =
        oblX0 x 3 * (⟪x 0, b⟫ - ⟪x 6, b⟫) + oblX2 x 3 * (⟪x 2, b⟫ - ⟪x 6, b⟫) := by
      rw [h36] at r3; linear_combination r3
    have hp : 0 < (oblX0 x 3 + oblX2 x 3 + oblX6 x 3 - 1) * (⟪x 1, b⟫ - ⟪x 6, b⟫) := by
      rw [key]
      exact add_pos (mul_pos ha3 (by linarith)) (mul_pos hb3 (by linarith))
    linarith [(mul_pos_iff_of_pos_left hK3).mp hp]
  -- D3: `t1 < t0 ∨ t5 < t0`
  have r5 := row 5
  have h015 : ⟪x 1, b⟫ < ⟪x 0, b⟫ ∨ ⟪x 5, b⟫ < ⟪x 0, b⟫ := by
    by_contra hn
    simp only [not_or, not_lt] at hn
    obtain ⟨n1, n5⟩ := hn
    have key : (⟪x 5, b⟫ - ⟪x 0, b⟫) +
        (oblX0 x 5 + oblX2 x 5 + oblX6 x 5 - 1) * (⟪x 1, b⟫ - ⟪x 0, b⟫) =
        oblX2 x 5 * (⟪x 2, b⟫ - ⟪x 0, b⟫) - oblX6 x 5 * (⟪x 0, b⟫ - ⟪x 6, b⟫) := by
      linear_combination r5
    nlinarith [mul_nonneg hK5.le (sub_nonneg.2 n1), mul_nonneg hb5.le (sub_nonneg.2 h20),
      mul_pos hc5 (show 0 < ⟪x 0, b⟫ - ⟪x 6, b⟫ by linarith)]
  -- D1: `t5 > 0`
  have h65 : ⟪x 6, b⟫ < ⟪x 5, b⟫ := by
    obtain ⟨al, be, hal, hbe, _, hq⟩ := Minimality.T24.Par.par2546_quad F
    have hzq := congrArg (fun y => ⟪y, b⟫) hq
    simp only [inner_add_left, real_inner_smul_left, inner_sub_left] at hzq
    have hYq := congrArg (fun y => ⟪F.N 7, y⟫) hq
    simp only [inner_add_right, real_inner_smul_right, ← F.hN] at hYq
    rw [F.zero 7 3 (by decide)] at hYq
    have hzr := radon02346_depth F b
    have hsum := radon02346_sum x
    have hYr : mu0 x * F.f 7 (x 0) + mu4 x * F.f 7 (x 4) = 0 := by
      have h := congrArg (fun u => ⟪F.N 7, u⟫) (radon02346 F)
      simp only [inner_add_right, real_inner_smul_right, inner_zero_right] at h
      rw [← F.hN 7 (x 0) (x 1), ← F.hN 7 (x 2) (x 1), ← F.hN 7 (x 3) (x 1),
        ← F.hN 7 (x 4) (x 1), ← F.hN 7 (x 6) (x 1), F.zero 7 2 (by decide),
        F.zero 7 3 (by decide), F.zero 7 6 (by decide)] at h
      linear_combination h + F.f 7 (x 1) * hsum
    have := t2b_d1_core (t0 := ⟪x 0, b⟫ - ⟪x 6, b⟫) (t2 := ⟪x 2, b⟫ - ⟪x 6, b⟫)
      (t4 := ⟪x 4, b⟫ - ⟪x 6, b⟫) (t5 := ⟪x 5, b⟫ - ⟪x 6, b⟫)
      (Y0 := -F.f 7 (x 0)) (Y4 := -F.f 7 (x 4)) (Y5 := -F.f 7 (x 5))
      (m0 := mu0 x) (m2 := mu2 x) (m4 := mu4 x) (al := al) (be := be)
      (by linarith) (by linarith) (neg_pos.2 (F.neg 7 0 (by decide)))
      (neg_pos.2 (F.neg 7 4 (by decide))) (neg_pos.2 (F.neg 7 5 (by decide))) hm0 hm2 hal hbe
      (by rw [h36] at hzr; linear_combination hzr - ⟪x 6, b⟫ * hsum)
      (by linear_combination -hYr)
      (by rw [h36] at hzq; linear_combination hzq)
      (by linear_combination -hYq)
    linarith
  exact ⟨h36, h62, h20, h61, h65, h015⟩

/-- A facet with level-1 value `-(s f)` (`s ≤ 0`, `f < 0`) and level-2 value `f` is lex-down. -/
theorem t2b_lexDn {a d c s f : ℝ} (hv : a = -(s * f)) (hs : s ≤ 0) (hf : f < 0) (hd : d = f) :
    LexPos3 (-a) (-d) (-c) := by
  rcases hs.lt_or_eq with h | h
  · left; rw [hv]; nlinarith [mul_pos (neg_pos.2 h) (neg_pos.2 hf)]
  · right; exact ⟨by rw [hv, h]; ring, Or.inl (by rw [hd]; linarith)⟩

/-- A clause from one strict first-level comparison. -/
theorem t2b_cl {p q r s b d1 d2 : ℝ³}
    (h : ⟪r, b⟫ < ⟪p, b⟫ ∨ ⟪s, b⟫ < ⟪p, b⟫ ∨ ⟪r, b⟫ < ⟪q, b⟫ ∨ ⟪s, b⟫ < ⟪q, b⟫) :
    Minimality.GenQuad.LexClause p q r s b d1 d2 :=
  Minimality.GenQuad.lexClause_of_notM (by
    rintro ⟨h1, h2, h3, h4⟩
    rcases h with h | h | h | h <;> linarith)

private def t2b_cP2 : ZMod 4 → Fin 7 := ![0, 6, 3, 5]
private def t2b_cP3 : ZMod 5 → Fin 7 := ![0, 1, 6, 3, 5]

private theorem t2b_cP2_inj : Function.Injective t2b_cP2 := by decide
private theorem t2b_cP3_inj : Function.Injective t2b_cP3 := by decide

private theorem t2b_cycP2 : S0xCycUD s0x_S24 t2b_cP2 {0, 1, 2, 5, 6, 7} {3, 4, 8} := by decide
private theorem t2b_cycP3 : S0xCycUD s0x_S24 t2b_cP3 {0, 2, 5, 6, 7} {1, 3, 4, 8} := by decide

/-- The ten clauses of the 5-rim `0 1 6 3 5` from the first-level depth facts. -/
private theorem t2b_clauses5 {x : Fin 7 → ℝ³} {b : ℝ³}
    (h36 : ⟪x 3, b⟫ = ⟪x 6, b⟫) (h62 : ⟪x 6, b⟫ < ⟪x 2, b⟫) (h20 : ⟪x 2, b⟫ ≤ ⟪x 0, b⟫)
    (h61 : ⟪x 6, b⟫ < ⟪x 1, b⟫) (h65 : ⟪x 6, b⟫ < ⟪x 5, b⟫)
    (h015 : ⟪x 1, b⟫ < ⟪x 0, b⟫ ∨ ⟪x 5, b⟫ < ⟪x 0, b⟫) :
    ∀ (B : ZMod 5) (b' c' d' : ℕ), 0 < b' → b' < c' → c' < d' → d' < 5 →
      Minimality.GenQuad.LexClause (x (t2b_cP3 (B + b'))) (x (t2b_cP3 (B + d')))
        (x (t2b_cP3 B)) (x (t2b_cP3 (B + c'))) b (x 2 - x 0) 0 := by
  have cl : ∀ p q r s : ℝ³,
      (⟪r, b⟫ < ⟪p, b⟫ ∨ ⟪s, b⟫ < ⟪p, b⟫ ∨ ⟪r, b⟫ < ⟪q, b⟫ ∨ ⟪s, b⟫ < ⟪q, b⟫) →
      Minimality.GenQuad.LexClause p q r s b (x 2 - x 0) 0 := fun _ _ _ _ h => t2b_cl h
  -- `p = x0 x1 x6 x3 x5`
  exact Minimality.GenQuad.clauses_five (p := fun i => x (t2b_cP3 i))
        (cl (x 1) (x 3) (x 0) (x 6) (Or.inr (Or.inl (by linarith))))
        (cl (x 0) (x 6) (x 1) (x 3) (Or.inr (Or.inl (by linarith))))
        (cl (x 1) (x 5) (x 0) (x 6) (Or.inr (Or.inr (Or.inr (by linarith)))))
        (by
          rcases h015 with h | h
          · exact cl (x 0) (x 6) (x 1) (x 5) (Or.inl h)
          · exact cl (x 0) (x 6) (x 1) (x 5) (Or.inr (Or.inl h)))
        (cl (x 1) (x 5) (x 0) (x 3) (Or.inr (Or.inr (Or.inr (by linarith)))))
        (by
          rcases h015 with h | h
          · exact cl (x 0) (x 3) (x 1) (x 5) (Or.inl h)
          · exact cl (x 0) (x 3) (x 1) (x 5) (Or.inr (Or.inl h)))
        (cl (x 6) (x 5) (x 0) (x 3) (Or.inr (Or.inr (Or.inr (by linarith)))))
        (cl (x 0) (x 3) (x 6) (x 5) (Or.inl (by linarith)))
        (cl (x 6) (x 5) (x 1) (x 3) (Or.inr (Or.inr (Or.inr (by linarith)))))
        (cl (x 1) (x 3) (x 6) (x 5) (Or.inl (by linarith)))

set_option maxHeartbeats 1000000 in
/-- **T2b** (TIES24P, `T2B.md`): on the triple tie `z0 = z2 = z4` at `w63 = x 3 - x 6` with
`0 ≤ ⟪x0 - x2, x2 - x6⟫`, the view `t2bView x` (tilt `x2 - x0`) gives `LexAny`, or (when
`mu0 + mu4 > 0`) facet `8 = 346` has a facet cell: a view with `346` up and its three
neighbours `3 = 0345`, `4 = 046`, `7 = 236` down. -/
theorem t2b_closes {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (htie : ⟪x 0, x 3 - x 6⟫ = ⟪x 2, x 3 - x 6⟫ ∧ ⟪x 2, x 3 - x 6⟫ = ⟪x 4, x 3 - x 6⟫)
    (hstar : 0 ≤ ⟪x 0 - x 2, x 2 - x 6⟫) :
    Minimality.Gen.LexAny F ∨
      ∃ u : ℝ³, 0 < ⟪F.N 8, u⟫ ∧ ⟪F.N 3, u⟫ < 0 ∧ ⟪F.N 4, u⟫ < 0 ∧ ⟪F.N 7, u⟫ < 0 := by
  obtain ⟨hm0, hm2, hm3, hm4, hm6⟩ := radon02346_signs F
  obtain ⟨h36, h62, h20, h61, h65, h015⟩ := t2b_depths F htie hstar
  set b := t2bView x with hb
  have hd : ∀ t : Fin 9, ⟪F.N t, x 2 - x 0⟫ = F.f t (x 2) - F.f t (x 0) :=
    fun t => (F.hN t (x 2) (x 0)).symm
  -- facings at `b`
  have hA : 0 < ⟪F.N 0, b⟫ := by
    rw [hb, t2b_fac2 F, F.zero 0 2 (by decide)]
    nlinarith [mul_pos hm3 (neg_pos.2 (F.neg 0 3 (by decide))),
      mul_pos hm6 (neg_pos.2 (F.neg 0 6 (by decide)))]
  have hC : 0 < ⟪F.N 2, b⟫ := by
    rw [hb, t2b_fac2 F, F.zero 2 2 (by decide)]
    nlinarith [mul_pos hm3 (neg_pos.2 (F.neg 2 3 (by decide))),
      mul_pos hm6 (neg_pos.2 (F.neg 2 6 (by decide)))]
  have hF : 0 < ⟪F.N 5, b⟫ := by
    rw [hb, t2b_fac2 F, F.zero 5 2 (by decide), F.zero 5 6 (by decide)]
    nlinarith [mul_pos hm3 (neg_pos.2 (F.neg 5 3 (by decide)))]
  have hG : 0 < ⟪F.N 6, b⟫ := by
    rw [hb, t2b_fac2 F, F.zero 6 2 (by decide), F.zero 6 3 (by decide)]
    nlinarith [mul_pos hm6 (neg_pos.2 (F.neg 6 6 (by decide)))]
  have hH : ⟪F.N 7, b⟫ = 0 := by
    rw [hb, t2b_fac2 F, F.zero 7 2 (by decide), F.zero 7 3 (by decide),
      F.zero 7 6 (by decide)]; ring
  have hH2 : 0 < ⟪F.N 7, x 2 - x 0⟫ := by
    rw [hd, F.zero 7 2 (by decide)]; linarith [F.neg 7 0 (by decide)]
  have hI : ⟪F.N 8, b⟫ < 0 := by
    rw [hb, t2b_fac2 F, F.zero 8 3 (by decide), F.zero 8 6 (by decide)]
    nlinarith [mul_pos (add_pos hm3 hm6) (neg_pos.2 (F.neg 8 2 (by decide)))]
  have hD : ⟪F.N 3, b⟫ = -((mu0 x + mu4 x) * F.f 3 (x 2)) := by
    rw [hb, t2b_fac1 F, F.zero 3 0 (by decide), F.zero 3 4 (by decide)]; ring
  have hE : ⟪F.N 4, b⟫ = -((mu0 x + mu4 x) * F.f 4 (x 2)) := by
    rw [hb, t2b_fac1 F, F.zero 4 0 (by decide), F.zero 4 4 (by decide)]; ring
  have hD2 : F.f 3 (x 2) < 0 := F.neg 3 2 (by decide)
  have hE2 : F.f 4 (x 2) < 0 := F.neg 4 2 (by decide)
  by_cases hs : 0 < mu0 x + mu4 x
  · -- P1: facet cell of `346`
    right
    refine ⟨-b - ((mu0 x + mu4 x) / 2) • (x 2 - x 4), ?_, ?_, ?_, ?_⟩ <;>
      rw [inner_sub_right, inner_neg_right, real_inner_smul_right, ← F.hN]
    · rw [F.zero 8 4 (by decide)]
      nlinarith [mul_pos hs (neg_pos.2 (F.neg 8 2 (by decide)))]
    · rw [hD, F.zero 3 4 (by decide)]; nlinarith [mul_pos hs (neg_pos.2 hD2)]
    · rw [hE, F.zero 4 4 (by decide)]; nlinarith [mul_pos hs (neg_pos.2 hE2)]
    · rw [hH, F.zero 7 2 (by decide)]; nlinarith [mul_pos hs (neg_pos.2 (F.neg 7 4 (by decide)))]
  left
  have hs' : mu0 x + mu4 x ≤ 0 := not_lt.mp hs
  -- `D`, `E` lex-down at `(b, x2 - x0)`
  have hDdn := t2b_lexDn (d := ⟪F.N 3, x 2 - x 0⟫) (c := ⟪F.N 3, (0 : ℝ³)⟫) hD hs' hD2
    (by rw [hd, F.zero 3 0 (by decide)]; ring)
  have hEdn := t2b_lexDn (d := ⟪F.N 4, x 2 - x 0⟫) (c := ⟪F.N 4, (0 : ℝ³)⟫) hE hs' hE2
    (by rw [hd, F.zero 4 0 (by decide)]; ring)
  by_cases hB : 0 < ⟪F.N 1, b⟫
  · -- P2: rim `0 6 3 5`
    have hU : ∀ t ∈ ({0, 1, 2, 5, 6, 7} : Finset (Fin 9)),
        LexPos3 ⟪F.N t, b⟫ ⟪F.N t, x 2 - x 0⟫ ⟪F.N t, (0 : ℝ³)⟫ := by
      intro t ht
      fin_cases t <;> try exact absurd ht (by decide)
      · exact Or.inl hA
      · exact Or.inl hB
      · exact Or.inl hC
      · exact Or.inl hF
      · exact Or.inl hG
      · exact Or.inr ⟨hH, Or.inl hH2⟩
    have hDn : ∀ t ∈ ({3, 4, 8} : Finset (Fin 9)),
        LexPos3 (-⟪F.N t, b⟫) (-⟪F.N t, x 2 - x 0⟫) (-⟪F.N t, (0 : ℝ³)⟫) := by
      intro t ht
      fin_cases t <;> try exact absurd ht (by decide)
      · exact hDdn
      · exact hEdn
      · exact Or.inl (neg_pos.2 hI)
    exact Minimality.GenQuad.lexAny_of_clauses F (k := 4) (by norm_num) t2b_cP2_inj t2b_cycP2
      b (x 2 - x 0) 0 hU hDn
      (Minimality.GenQuad.clauses_four (p := fun i => x (t2b_cP2 i))
        (show Minimality.GenQuad.LexClause (x 6) (x 5) (x 0) (x 3) b (x 2 - x 0) 0 from
          t2b_cl (Or.inr (Or.inr (Or.inr (by linarith)))))
        (show Minimality.GenQuad.LexClause (x 0) (x 3) (x 6) (x 5) b (x 2 - x 0) 0 from
          t2b_cl (Or.inl (by linarith))))
  · -- P3: rim `0 1 6 3 5` (`B` lex-down; then `mu0 + mu4 < 0`)
    have hBle : ⟪F.N 1, b⟫ ≤ 0 := not_lt.mp hB
    have hU : ∀ t ∈ ({0, 2, 5, 6, 7} : Finset (Fin 9)),
        LexPos3 ⟪F.N t, b⟫ ⟪F.N t, x 2 - x 0⟫ ⟪F.N t, (0 : ℝ³)⟫ := by
      intro t ht
      fin_cases t <;> try exact absurd ht (by decide)
      · exact Or.inl hA
      · exact Or.inl hC
      · exact Or.inl hF
      · exact Or.inl hG
      · exact Or.inr ⟨hH, Or.inl hH2⟩
    have hBdn : LexPos3 (-⟪F.N 1, b⟫) (-⟪F.N 1, x 2 - x 0⟫) (-⟪F.N 1, (0 : ℝ³)⟫) := by
      rcases hBle.lt_or_eq with h | h
      · exact Or.inl (neg_pos.2 h)
      · refine Or.inr ⟨by rw [h, neg_zero], Or.inl ?_⟩
        rw [hd, F.zero 1 0 (by decide)]; linarith [F.neg 1 2 (by decide)]
    have hDn : ∀ t ∈ ({1, 3, 4, 8} : Finset (Fin 9)),
        LexPos3 (-⟪F.N t, b⟫) (-⟪F.N t, x 2 - x 0⟫) (-⟪F.N t, (0 : ℝ³)⟫) := by
      intro t ht
      fin_cases t <;> try exact absurd ht (by decide)
      · exact hBdn
      · exact hDdn
      · exact hEdn
      · exact Or.inl (neg_pos.2 hI)
    exact Minimality.GenQuad.lexAny_of_clauses F (k := 5) (by norm_num) t2b_cP3_inj t2b_cycP3
      b (x 2 - x 0) 0 hU hDn (t2b_clauses5 h36 h62 h20 h61 h65 h015)

/-- **T2b'**: the `pi24` image at `E23 = x 3 - x 2`: on the triple tie `z0 = z6 = z5` with
`0 ≤ ⟪x0 - x6, x6 - x2⟫`, `LexAny`, or facet `6 = 235` has a facet cell (neighbours
`3 = 0345`, `2 = 025`, `7 = 236` down). -/
theorem t2b_closes_e23 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    (htie : ⟪x 0, x 3 - x 2⟫ = ⟪x 6, x 3 - x 2⟫ ∧ ⟪x 6, x 3 - x 2⟫ = ⟪x 5, x 3 - x 2⟫)
    (hstar : 0 ≤ ⟪x 0 - x 6, x 6 - x 2⟫) :
    Minimality.Gen.LexAny F ∨
      ∃ u : ℝ³, 0 < ⟪F.N 6, u⟫ ∧ ⟪F.N 3, u⟫ < 0 ∧ ⟪F.N 2, u⟫ < 0 ∧ ⟪F.N 7, u⟫ < 0 := by
  rcases t2b_closes (sym24 F)
      (by simpa only [Function.comp_apply, pi24_0, pi24_2, pi24_3, pi24_4, pi24_6] using htie)
      (by simpa only [Function.comp_apply, pi24_0, pi24_2, pi24_6] using hstar) with h | ⟨u, hu⟩
  · exact Or.inl (lexAny_sym F h)
  · exact Or.inr ⟨u, hu⟩

end Minimality.T24.A20
