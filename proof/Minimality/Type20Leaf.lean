module

public import Minimality.Type20IMA

@[expose] public section

/-!
# Type 20: shared leaf-assembly tools (I_MC, I_V, ...)

Facing polynomials `nf` of the eight facets in the `Frame20` shape coordinates (namespace
`Minimality.CaseC20.IVT`), `leaf_of_view` (a silhouette cycle, lex facings at a view and a tilt, and
robustly unimodal depths give a Rupert point set), segment-view and depth-sign helpers, and `RobUni`
lemmas for 5- and 6-cycles (`robuni5` closes a 5-cycle goal from order facts).  The namespace `IVT`
is kept because the I_V and I_Q developments are written against it; `Type20IMCA` re-exports these
names in `IMCT`.
-/



open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset
open scoped RealInnerProductSpace

namespace Minimality.CaseC20
namespace IVT

/-- The facing polynomials of the facets `A..H` (outward normals paired with the frame vector `q`). -/
noncomputable def nf (S : Shape20) (q : C3) : Fin 8 → ℝ :=
  ![S.hm*S.sm*q.x + (S.hm + S.km*S.tm - S.km)*q.y - S.sm*(1-S.tm)*q.z,
    -S.hp*S.sp*q.x - S.kp*S.tp*q.y + S.sp*S.tp*q.z,
    -(S.hm*S.tp + S.hp*S.tm)*q.y,
    -S.hm*S.sm*q.x - S.km*S.tm*q.y - S.sm*S.tm*q.z,
    S.hp*q.x + S.hp*q.y + (1-S.tp)*q.z,
    (S.kp - S.hp*(1-S.sp))*q.x + S.kp*S.tp*q.y + S.tp*(1-S.sp)*q.z,
    S.km*q.x + S.km*q.y + (S.sm-1)*q.z,
    -S.kp*q.x]


lemma nf_B (S : Shape20) (q : C3) : nf S q 1 = -S.hp*S.sp*q.x - S.kp*S.tp*q.y + S.sp*S.tp*q.z := rfl
lemma nf_C (S : Shape20) (q : C3) : nf S q 2 = -(S.hm*S.tp + S.hp*S.tm)*q.y := rfl
lemma nf_D (S : Shape20) (q : C3) : nf S q 3 = -S.hm*S.sm*q.x - S.km*S.tm*q.y - S.sm*S.tm*q.z := rfl

lemma nf_A (S : Shape20) (q : C3) : nf S q 0 = S.hm*S.sm*q.x + (S.hm + S.km*S.tm - S.km)*q.y - S.sm*(1-S.tm)*q.z := rfl
lemma nf_E (S : Shape20) (q : C3) : nf S q 4 = S.hp*q.x + S.hp*q.y + (1-S.tp)*q.z := rfl
lemma nf_F (S : Shape20) (q : C3) : nf S q 5 = (S.kp - S.hp*(1-S.sp))*q.x + S.kp*S.tp*q.y + S.tp*(1-S.sp)*q.z := rfl
lemma nf_G (S : Shape20) (q : C3) : nf S q 6 = S.km*q.x + S.km*q.y + (S.sm-1)*q.z := rfl
lemma nf_H (S : Shape20) (q : C3) : nf S q 7 = -S.kp*q.x := rfl

/-- A linear form whose coefficient vector is proportional to `(a,b,c)` with pivot `a`. -/
lemma core_a (a b c α β δ : ℝ) (ha : a ≠ 0) (h1 : α * b = β * a) (h2 : α * c = δ * a) (q : C3) :
    q.x * α + q.y * β + q.z * δ = α / a * (a * q.x + b * q.y + c * q.z) := by
  have e1 : β = α / a * b := by field_simp; linarith
  have e2 : δ = α / a * c := by field_simp; linarith
  rw [e1, e2]; field_simp

/-- The same with pivot `b`. -/
lemma core_b (a b c α β δ : ℝ) (hb : b ≠ 0) (h1 : β * a = α * b) (h2 : β * c = δ * b) (q : C3) :
    q.x * α + q.y * β + q.z * δ = β / b * (a * q.x + b * q.y + c * q.z) := by
  have e1 : α = β / b * a := by field_simp; linarith
  have e2 : δ = β / b * c := by field_simp; linarith
  rw [e1, e2]; field_simp

variable {x : Fin 7 → ℝ³} (F : Frame20 x) (FF : S0xFac 8 h20s_S x)

lemma facing_A : ∃ l : ℝ, 0 < l ∧ ∀ q : C3,
    ⟪FF.N 0, F.toFrame7.fvC q⟫ = l * nf F.S q 0 := by
  have hm0 := F.S.hm_pos; have sm0 := F.S.sm_pos
  obtain ⟨c0, c3, c2, c4⟩ := F.facet_coords (FF.f 0) (FF.N 0) (FF.hN 0)
  have fv := fun q : C3 => F.facet_val FF 0 q
  have z1 : FF.f 0 (x 1) = 0 := FF.zero 0 1 (by decide)
  have z3 : FF.f 0 (x 3) = 0 := FF.zero 0 3 (by decide)
  have z4 : FF.f 0 (x 4) = 0 := FF.zero 0 4 (by decide)
  have n5 : FF.f 0 (x 5) < 0 := FF.neg 0 5 (by decide)
  simp only [z1, z3, z4] at c3 c4 fv
  refine ⟨(0 - FF.f 0 (x 5)) / (F.S.hm * F.S.sm), div_pos (by linarith) (by positivity), fun q => ?_⟩
  rw [fv, core_a (F.S.hm * F.S.sm) (F.S.hm + F.S.km*F.S.tm - F.S.km) (-(F.S.sm*(1-F.S.tm)))
    (0 - FF.f 0 (x 5)) (FF.f 0 (x 6) - FF.f 0 (x 5)) ⟪FF.N 0, F.e⟫ (by positivity)
    (by linear_combination F.S.hm * c4 - F.S.km * c3) (by linear_combination (-F.S.sm) * c3) q]
  simp only [nf, Matrix.cons_val_zero] <;> ring

lemma facing_B : ∃ l : ℝ, 0 < l ∧ ∀ q : C3,
    ⟪FF.N 1, F.toFrame7.fvC q⟫ = l * nf F.S q 1 := by
  have hp0 := F.S.hp_pos; have sp0 := F.S.sp_pos
  obtain ⟨c0, c3, c2, c4⟩ := F.facet_coords (FF.f 1) (FF.N 1) (FF.hN 1)
  have fv := fun q : C3 => F.facet_val FF 1 q
  have z0 : FF.f 1 (x 0) = 0 := FF.zero 1 0 (by decide)
  have z2 : FF.f 1 (x 2) = 0 := FF.zero 1 2 (by decide)
  have z5 : FF.f 1 (x 5) = 0 := FF.zero 1 5 (by decide)
  have n1 : FF.f 1 (x 1) < 0 := FF.neg 1 1 (by decide)
  simp only [z0, z2, z5] at c0 c2 fv
  refine ⟨(FF.f 1 (x 1) - 0) / (-F.S.hp * F.S.sp), div_pos_of_neg_of_neg (by linarith) (by nlinarith), fun q => ?_⟩
  rw [fv, core_a (-F.S.hp * F.S.sp) (-F.S.kp * F.S.tp) (F.S.sp * F.S.tp)
    (FF.f 1 (x 1) - 0) (FF.f 1 (x 6) - 0) ⟪FF.N 1, F.e⟫ (by nlinarith)
    (by linear_combination (-F.S.hp) * c2 + F.S.kp * c0) (by linear_combination (-F.S.sp) * c0) q]
  rw [nf_B]; ring

lemma facing_C : ∃ l : ℝ, 0 < l ∧ ∀ q : C3,
    ⟪FF.N 2, F.toFrame7.fvC q⟫ = l * nf F.S q 2 := by
  have hp0 := F.S.hp_pos; have hm0 := F.S.hm_pos; have tp0 := F.S.tp_pos; have tm0 := F.S.tm_pos
  obtain ⟨c0, c3, c2, c4⟩ := F.facet_coords (FF.f 2) (FF.N 2) (FF.hN 2)
  have fv := fun q : C3 => F.facet_val FF 2 q
  have z0 : FF.f 2 (x 0) = 0 := FF.zero 2 0 (by decide)
  have z1 : FF.f 2 (x 1) = 0 := FF.zero 2 1 (by decide)
  have z5 : FF.f 2 (x 5) = 0 := FF.zero 2 5 (by decide)
  have n6 : FF.f 2 (x 6) < 0 := FF.neg 2 6 (by decide)
  simp only [z0, z1, z5] at c0 fv
  have hd : ⟪FF.N 2, F.e⟫ = 0 := by
    have : F.S.hp * ⟪FF.N 2, F.e⟫ = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left hp0.ne'
  have hc : 0 < F.S.hm * F.S.tp + F.S.hp * F.S.tm := by positivity
  refine ⟨(FF.f 2 (x 6)) / (-(F.S.hm * F.S.tp + F.S.hp * F.S.tm)), div_pos_of_neg_of_neg n6 (by linarith), fun q => ?_⟩
  rw [fv, hd]; rw [nf_C]; field_simp; ring

lemma facing_D : ∃ l : ℝ, 0 < l ∧ ∀ q : C3,
    ⟪FF.N 3, F.toFrame7.fvC q⟫ = l * nf F.S q 3 := by
  have hm0 := F.S.hm_pos; have sm0 := F.S.sm_pos
  obtain ⟨c0, c3, c2, c4⟩ := F.facet_coords (FF.f 3) (FF.N 3) (FF.hN 3)
  have fv := fun q : C3 => F.facet_val FF 3 q
  have z3 : FF.f 3 (x 3) = 0 := FF.zero 3 3 (by decide)
  have z4 : FF.f 3 (x 4) = 0 := FF.zero 3 4 (by decide)
  have z5 : FF.f 3 (x 5) = 0 := FF.zero 3 5 (by decide)
  have n1 : FF.f 3 (x 1) < 0 := FF.neg 3 1 (by decide)
  simp only [z3, z4, z5] at c3 c4 fv
  refine ⟨(FF.f 3 (x 1) - 0) / (-F.S.hm * F.S.sm), div_pos_of_neg_of_neg (by linarith) (by nlinarith), fun q => ?_⟩
  rw [fv, core_a (-F.S.hm * F.S.sm) (-F.S.km * F.S.tm) (-(F.S.sm * F.S.tm))
    (FF.f 3 (x 1) - 0) (FF.f 3 (x 6) - 0) ⟪FF.N 3, F.e⟫ (by nlinarith)
    (by linear_combination (-F.S.hm) * c4 + F.S.km * c3) (by linear_combination (F.S.sm) * c3) q]
  rw [nf_D]; ring

lemma facing_E : ∃ l : ℝ, 0 < l ∧ ∀ q : C3,
    ⟪FF.N 4, F.toFrame7.fvC q⟫ = l * nf F.S q 4 := by
  have hp0 := F.S.hp_pos
  obtain ⟨c0, c3, c2, c4⟩ := F.facet_coords (FF.f 4) (FF.N 4) (FF.hN 4)
  have fv := fun q : C3 => F.facet_val FF 4 q
  have z0 : FF.f 4 (x 0) = 0 := FF.zero 4 0 (by decide)
  have z1 : FF.f 4 (x 1) = 0 := FF.zero 4 1 (by decide)
  have z6 : FF.f 4 (x 6) = 0 := FF.zero 4 6 (by decide)
  have n5 : FF.f 4 (x 5) < 0 := FF.neg 4 5 (by decide)
  simp only [z0, z1, z6] at c0 fv
  refine ⟨(0 - FF.f 4 (x 5)) / F.S.hp, div_pos (by linarith) hp0, fun q => ?_⟩
  rw [fv, core_a F.S.hp F.S.hp (1 - F.S.tp) (0 - FF.f 4 (x 5)) (0 - FF.f 4 (x 5)) ⟪FF.N 4, F.e⟫ hp0.ne'
    (by ring) (by linear_combination c0) q]
  simp only [nf, Matrix.cons_val, Matrix.head_cons] <;> ring

lemma facing_F : ∃ l : ℝ, 0 < l ∧ ∀ q : C3,
    ⟪FF.N 5, F.toFrame7.fvC q⟫ = l * nf F.S q 5 := by
  have kp0 := F.S.kp_pos; have tp0 := F.S.tp_pos
  obtain ⟨c0, c3, c2, c4⟩ := F.facet_coords (FF.f 5) (FF.N 5) (FF.hN 5)
  have fv := fun q : C3 => F.facet_val FF 5 q
  have z0 : FF.f 5 (x 0) = 0 := FF.zero 5 0 (by decide)
  have z2 : FF.f 5 (x 2) = 0 := FF.zero 5 2 (by decide)
  have z6 : FF.f 5 (x 6) = 0 := FF.zero 5 6 (by decide)
  have n5 : FF.f 5 (x 5) < 0 := FF.neg 5 5 (by decide)
  simp only [z0, z2, z6] at c0 c2 fv
  refine ⟨(0 - FF.f 5 (x 5)) / (F.S.kp * F.S.tp), div_pos (by linarith) (by positivity), fun q => ?_⟩
  rw [fv, core_b (F.S.kp - F.S.hp * (1 - F.S.sp)) (F.S.kp * F.S.tp) (F.S.tp * (1 - F.S.sp))
    (FF.f 5 (x 1) - FF.f 5 (x 5)) (0 - FF.f 5 (x 5)) ⟪FF.N 5, F.e⟫ (by positivity)
    (by linear_combination F.S.kp * c0 - F.S.hp * c2) (by linear_combination (F.S.tp) * c2) q]
  simp only [nf, Matrix.cons_val, Matrix.head_cons] <;> ring

lemma facing_G : ∃ l : ℝ, 0 < l ∧ ∀ q : C3,
    ⟪FF.N 6, F.toFrame7.fvC q⟫ = l * nf F.S q 6 := by
  have km0 := F.S.km_pos
  obtain ⟨c0, c3, c2, c4⟩ := F.facet_coords (FF.f 6) (FF.N 6) (FF.hN 6)
  have fv := fun q : C3 => F.facet_val FF 6 q
  have z1 : FF.f 6 (x 1) = 0 := FF.zero 6 1 (by decide)
  have z4 : FF.f 6 (x 4) = 0 := FF.zero 6 4 (by decide)
  have z6 : FF.f 6 (x 6) = 0 := FF.zero 6 6 (by decide)
  have n5 : FF.f 6 (x 5) < 0 := FF.neg 6 5 (by decide)
  simp only [z1, z4, z6] at c4 fv
  refine ⟨(0 - FF.f 6 (x 5)) / F.S.km, div_pos (by linarith) km0, fun q => ?_⟩
  rw [fv, core_a F.S.km F.S.km (F.S.sm - 1) (0 - FF.f 6 (x 5)) (0 - FF.f 6 (x 5)) ⟪FF.N 6, F.e⟫ km0.ne'
    (by ring) (by linear_combination (-1) * c4) q]
  simp only [nf, Matrix.cons_val, Matrix.head_cons] <;> ring

lemma facing_H : ∃ l : ℝ, 0 < l ∧ ∀ q : C3,
    ⟪FF.N 7, F.toFrame7.fvC q⟫ = l * nf F.S q 7 := by
  have kp0 := F.S.kp_pos
  obtain ⟨c0, c3, c2, c4⟩ := F.facet_coords (FF.f 7) (FF.N 7) (FF.hN 7)
  have fv := fun q : C3 => F.facet_val FF 7 q
  have z2 : FF.f 7 (x 2) = 0 := FF.zero 7 2 (by decide)
  have z5 : FF.f 7 (x 5) = 0 := FF.zero 7 5 (by decide)
  have z6 : FF.f 7 (x 6) = 0 := FF.zero 7 6 (by decide)
  have n1 : FF.f 7 (x 1) < 0 := FF.neg 7 1 (by decide)
  simp only [z2, z5, z6] at c2 fv
  have hd : ⟪FF.N 7, F.e⟫ = 0 := by
    have : F.S.kp * ⟪FF.N 7, F.e⟫ = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left kp0.ne'
  refine ⟨(FF.f 7 (x 1)) / (-F.S.kp), div_pos_of_neg_of_neg n1 (by linarith), fun q => ?_⟩
  rw [fv, hd]; simp only [nf, Matrix.cons_val, Matrix.head_cons]
  field_simp
  try ring

/-- Each facet normal paired with a frame vector is a positive multiple of the facing polynomial. -/
lemma facing (t : Fin 8) : ∃ l : ℝ, 0 < l ∧ ∀ q : C3,
    ⟪FF.N t, F.toFrame7.fvC q⟫ = l * nf F.S q t := by
  fin_cases t
  · exact facing_A F FF
  · exact facing_B F FF
  · exact facing_C F FF
  · exact facing_D F FF
  · exact facing_E F FF
  · exact facing_F F FF
  · exact facing_G F FF
  · exact facing_H F FF

/-- Scaling both entries of a lexicographic positivity by a positive factor. -/
lemma lp_scale {l a b : ℝ} (hl : 0 < l) (h : h21b_LP a b) : h21b_LP (l * a) (l * b) := by
  unfold h21b_LP at *
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl (mul_pos hl h)
  · exact Or.inr ⟨by rw [h1, mul_zero], mul_pos hl h2⟩

/-- The lex facing check of all eight facets at the frame views `qu`, `qv` in terms of the facing
polynomials. -/
lemma facOK (pat : Fin 8 → Bool) (qu qv : C3)
    (h : ∀ t, (pat t = true → h21b_LP (nf F.S qu t) (nf F.S qv t)) ∧
      (pat t = false → h21b_LP (-nf F.S qu t) (-nf F.S qv t))) :
    S0xFacOK FF pat (F.toFrame7.fvC qu) (F.toFrame7.fvC qv) := by
  intro t
  obtain ⟨l, hl, hq⟩ := facing F FF t
  rw [hq qu, hq qv]
  refine ⟨fun hp => lp_scale hl ((h t).1 hp), fun hp => ?_⟩
  have := lp_scale hl ((h t).2 hp)
  simpa only [mul_neg] using this

include FF in
/-- A nonzero facing polynomial shows that the view vector is nonzero. -/
lemma fvC_ne_zero (qu : C3) (t : Fin 8) (h : nf F.S qu t ≠ 0) : F.toFrame7.fvC qu ≠ 0 := by
  intro h0
  obtain ⟨l, hl, hq⟩ := facing F FF t
  have := hq qu
  rw [h0, inner_zero_right] at this
  exact h (by rcases mul_eq_zero.1 this.symm with h1 | h1; exact absurd h1 hl.ne'; exact h1)

include FF in
/-- **Leaf assembly**: a cycle `c` that is a silhouette of the pattern, facings at the frame views
`qu` (view) and `qv` (tilt) following the pattern, and robustly unimodal depths at `qu`. -/
theorem leaf_of_view {k : ℕ} [NeZero k] (hx : Function.Injective x) (hk : 3 ≤ k)
    {c : ZMod k → Fin 7} (hc : Function.Injective c) {pat : Fin 8 → Bool}
    (hcyc : S0xCycOK h20s_S c pat) (qu qv : C3) (t0 : Fin 8) (hu : nf F.S qu t0 ≠ 0)
    (h : ∀ t, (pat t = true → h21b_LP (nf F.S qu t) (nf F.S qv t)) ∧
      (pat t = false → h21b_LP (-nf F.S qu t) (-nf F.S qv t)))
    (hU : RobUni (fun a : ZMod k => F.dep qu (c a))) : IsRupert (univ.image x) := by
  obtain ⟨D⟩ := s0x_silL FF hcyc (facOK F FF pat qu qv h)
  exact s0x_sil_isRupert_lex hk hx hc (fvC_ne_zero F FF qu t0 hu) D (F.robUni_of_dep c qu hU)


/-- Segment view `x j - x i` in frame coordinates, from the coordinates of the two endpoints. -/
lemma seg_vec (i j : Fin 7) (q : C3) (hq : q = (F.toFrame7.ptC j).sub (F.toFrame7.ptC i)) :
    x j - x i = F.toFrame7.fvC q := by
  rw [hq]; exact F.toFrame7.x_sub j i

/-- The frame depth is odd in the view. -/
lemma dep_neg (a b c : ℝ) (j : Fin 7) : F.dep ⟨-a, -b, -c⟩ j = - F.dep ⟨a, b, c⟩ j := by
  fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue]; rw [Frame20.dep_0, Frame20.dep_0]; ring
  · rw [show ((⟨1, by decide⟩ : Fin 7)) = 1 from rfl, Frame20.dep_1, Frame20.dep_1]; ring
  · rw [show ((⟨2, by decide⟩ : Fin 7)) = 2 from rfl, Frame20.dep_2, Frame20.dep_2]; ring
  · rw [show ((⟨3, by decide⟩ : Fin 7)) = 3 from rfl, Frame20.dep_3, Frame20.dep_3]; ring
  · rw [show ((⟨4, by decide⟩ : Fin 7)) = 4 from rfl, Frame20.dep_4, Frame20.dep_4]; ring
  · rw [show ((⟨5, by decide⟩ : Fin 7)) = 5 from rfl, Frame20.dep_5, Frame20.dep_5]; ring
  · rw [show ((⟨6, by decide⟩ : Fin 7)) = 6 from rfl, Frame20.dep_6, Frame20.dep_6]; ring

end IVT
end Minimality.CaseC20

namespace Minimality.H20S

/-- `RobUni` is invariant under negating all depths (relabel the quadruple by a rotation). -/
theorem robUni_neg {k : ℕ} {z : ZMod k → ℝ} (h : RobUni z) : RobUni (fun i => - z i) := by
  intro B b c d hb hbc hcd hd hh
  apply h (B + b) (c - b) (d - b) (k - b) (by omega) (by omega) (by omega) (by omega)
  have e1 : (B + (b : ZMod k)) + ((c - b : ℕ) : ZMod k) = B + c := by
    rw [Nat.cast_sub hbc.le]; ring
  have e2 : (B + (b : ZMod k)) + ((d - b : ℕ) : ZMod k) = B + d := by
    rw [Nat.cast_sub (by omega : b ≤ d)]; ring
  have e3 : (B + (b : ZMod k)) + ((k - b : ℕ) : ZMod k) = B := by
    rw [Nat.cast_sub (by omega : b ≤ k), ZMod.natCast_self]; ring
  rw [e1, e2, e3]
  simp only at hh
  obtain ⟨h1, h2, h3, h4⟩ := hh
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

set_option hygiene false in
/-- Closes `RobUni z` on `ZMod 5` from strict/weak order facts about `z 0, ..., z 4` in context. -/
macro "robuni5" : tactic => `(tactic| (
  intro B b c d hb hbc hcd hd
  have hB : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := by revert B; decide
  have hb4 : b < 5 := by omega
  have hc4 : c < 5 := by omega
  obtain ⟨e01, e02, e03, e04, e11, e12, e13, e14, e21, e22, e23, e24, e31, e32, e33, e34, e41, e42, e43, e44⟩ := Minimality.H20S.zmod5_sums
  interval_cases b <;> interval_cases c <;> (try omega) <;> interval_cases d <;> (try omega) <;>
  rcases hB with rfl | rfl | rfl | rfl | rfl <;>
  · rintro ⟨a1, a2, a3, a4⟩
    revert a1 a2 a3 a4
    simp only [Nat.cast_ofNat, Nat.cast_one, e01, e02, e03, e04, e11, e12, e13, e14, e21, e22, e23, e24, e31, e32, e33, e34, e41, e42, e43, e44]
    intro a1 a2 a3 a4
    linarith))

/-- Five-cycle shape D: `z1 < z2 < z3` and `z0 < z4` (a path 1,2,3 rising, 0 below 4). -/
theorem robUni5_d {z : ZMod 5 → ℝ} (h12 : z 1 < z 2) (h23 : z 2 < z 3) (h04 : z 0 < z 4) :
    RobUni z := by robuni5

/-- Five-cycle shape E: `z1 < z0`, `z2 < z3`, and `z4` above `z0` or above `z3`. -/
theorem robUni5_e {z : ZMod 5 → ℝ} (h10 : z 1 < z 0) (h23 : z 2 < z 3)
    (h4 : ¬ (z 4 ≤ z 0 ∧ z 4 ≤ z 3)) : RobUni z := by
  have h4' : z 0 < z 4 ∨ z 3 < z 4 := by
    by_contra hc
    push Not at hc
    exact h4 ⟨hc.1, hc.2⟩
  rcases h4' with h | h <;> robuni5

/-- Five-cycle shape F: `z1 < z0`, `z2 < z1`, `z3 < z1`, `z3 < z4`. -/
theorem robUni5_f {z : ZMod 5 → ℝ} (h10 : z 1 < z 0) (h21 : z 2 < z 1) (h31 : z 3 < z 1)
    (h34 : z 3 < z 4) : RobUni z := by robuni5

end Minimality.H20S



open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset

namespace Minimality.H20S

/-- On a 5-cycle with `z0 < z4 < z3 = z2` and `z1 < z2` (a plateau at the peak), `RobUni` holds. -/
theorem robUni5_t {z : ZMod 5 → ℝ} (h04 : z 0 < z 4) (h43 : z 4 < z 3) (h32 : z 2 = z 3)
    (h12 : z 1 < z 2) : RobUni z := by
  intro B b c d hb hbc hcd hd
  have hB : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := by revert B; decide
  have hb4 : b < 5 := by omega
  have hc4 : c < 5 := by omega
  obtain ⟨e01, e02, e03, e04, e11, e12, e13, e14, e21, e22, e23, e24, e31, e32, e33, e34, e41, e42, e43, e44⟩ := zmod5_sums
  interval_cases b <;> interval_cases c <;> (try omega) <;> interval_cases d <;> (try omega) <;>
  rcases hB with rfl | rfl | rfl | rfl | rfl <;>
  · rintro ⟨a1, a2, a3, a4⟩
    revert a1 a2 a3 a4
    simp only [Nat.cast_ofNat, Nat.cast_one, e01, e02, e03, e04, e11, e12, e13, e14, e21, e22, e23, e24, e31, e32, e33, e34, e41, e42, e43, e44]
    intro a1 a2 a3 a4
    linarith

/-- On a 5-cycle with a peak plateau `z0 = z1`, `z3 < z2 < z1`, `z4 < z1`, `RobUni` holds. -/
theorem robUni5_u {z : ZMod 5 → ℝ} (h01 : z 0 = z 1) (h12 : z 2 < z 1) (h23 : z 3 < z 2)
    (h41 : z 4 < z 1) : RobUni z := by
  intro B b c d hb hbc hcd hd
  have hB : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 := by revert B; decide
  have hb4 : b < 5 := by omega
  have hc4 : c < 5 := by omega
  obtain ⟨e01, e02, e03, e04, e11, e12, e13, e14, e21, e22, e23, e24, e31, e32, e33, e34, e41, e42, e43, e44⟩ := zmod5_sums
  interval_cases b <;> interval_cases c <;> (try omega) <;> interval_cases d <;> (try omega) <;>
  rcases hB with rfl | rfl | rfl | rfl | rfl <;>
  · rintro ⟨a1, a2, a3, a4⟩
    revert a1 a2 a3 a4
    simp only [Nat.cast_ofNat, Nat.cast_one, e01, e02, e03, e04, e11, e12, e13, e14, e21, e22, e23, e24, e31, e32, e33, e34, e41, e42, e43, e44]
    intro a1 a2 a3 a4
    linarith

end Minimality.H20S



open Minimality Minimality.CaseC20 Minimality.CaseC09 Minimality.CaseC18 Minimality.H20S Minimality.H21 Finset

namespace Minimality.H20S

/-- Sums in `ZMod 6`, for rewriting cycle positions. -/
theorem zmod6_sums :     ((0:ZMod 6) + 1 = 1) ∧
    ((0:ZMod 6) + 2 = 2) ∧
    ((0:ZMod 6) + 3 = 3) ∧
    ((0:ZMod 6) + 4 = 4) ∧
    ((0:ZMod 6) + 5 = 5) ∧
    ((1:ZMod 6) + 1 = 2) ∧
    ((1:ZMod 6) + 2 = 3) ∧
    ((1:ZMod 6) + 3 = 4) ∧
    ((1:ZMod 6) + 4 = 5) ∧
    ((1:ZMod 6) + 5 = 0) ∧
    ((2:ZMod 6) + 1 = 3) ∧
    ((2:ZMod 6) + 2 = 4) ∧
    ((2:ZMod 6) + 3 = 5) ∧
    ((2:ZMod 6) + 4 = 0) ∧
    ((2:ZMod 6) + 5 = 1) ∧
    ((3:ZMod 6) + 1 = 4) ∧
    ((3:ZMod 6) + 2 = 5) ∧
    ((3:ZMod 6) + 3 = 0) ∧
    ((3:ZMod 6) + 4 = 1) ∧
    ((3:ZMod 6) + 5 = 2) ∧
    ((4:ZMod 6) + 1 = 5) ∧
    ((4:ZMod 6) + 2 = 0) ∧
    ((4:ZMod 6) + 3 = 1) ∧
    ((4:ZMod 6) + 4 = 2) ∧
    ((4:ZMod 6) + 5 = 3) ∧
    ((5:ZMod 6) + 1 = 0) ∧
    ((5:ZMod 6) + 2 = 1) ∧
    ((5:ZMod 6) + 3 = 2) ∧
    ((5:ZMod 6) + 4 = 3) ∧
    ((5:ZMod 6) + 5 = 4) := by decide

/-- On a 6-cycle with the peak `z1 > z2 > z3 > z4`, `z1 > z0 ≥ z4` and `z5 < z0`, `RobUni` holds. -/
theorem robUni6_a {z : ZMod 6 → ℝ} (h12 : z 2 < z 1) (h23 : z 3 < z 2) (h34 : z 4 < z 3)
    (h01 : z 0 < z 1) (h04 : z 4 ≤ z 0) (h50 : z 5 < z 0) : RobUni z := by
  intro B b c d hb hbc hcd hd
  have hB : B = 0 ∨ B = 1 ∨ B = 2 ∨ B = 3 ∨ B = 4 ∨ B = 5 := by revert B; decide
  have hb4 : b < 6 := by omega
  have hc4 : c < 6 := by omega
  obtain ⟨e01, e02, e03, e04, e05, e11, e12, e13, e14, e15, e21, e22, e23, e24, e25, e31, e32, e33, e34, e35, e41, e42, e43, e44, e45, e51, e52, e53, e54, e55⟩ := zmod6_sums
  interval_cases b <;> interval_cases c <;> (try omega) <;> interval_cases d <;> (try omega) <;>
  rcases hB with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rintro ⟨a1, a2, a3, a4⟩
    revert a1 a2 a3 a4
    simp only [Nat.cast_ofNat, Nat.cast_one, e01, e02, e03, e04, e05, e11, e12, e13, e14, e15, e21, e22, e23, e24, e25, e31, e32, e33, e34, e35, e41, e42, e43, e44, e45, e51, e52, e53, e54, e55]
    intro a1 a2 a3 a4
    linarith

end Minimality.H20S


namespace Minimality.CaseC20
namespace Shape20
variable (S : Shape20)

lemma sp1 : 0 < 1 - S.sp := by linarith [S.sp_lt]
lemma sm1 : 0 < 1 - S.sm := by linarith [S.sm_lt]
lemma tp1 : 0 < 1 - S.tp := by linarith [S.tp_lt]
lemma tm1 : 0 < 1 - S.tm := by linarith [S.tm_lt]

end Shape20
end Minimality.CaseC20
