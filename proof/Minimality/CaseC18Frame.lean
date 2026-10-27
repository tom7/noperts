module

public import Minimality.CaseC09Frame
public import Minimality.CaseC18Alg

@[expose] public section

/-!
# Type 18, acute case (c): the normal-form frame (`FEWER-FACES-PROOFS.md` §27, continued (2) §0)

Labels `(v, xa, m1+, m1-, xb, m2+, m2-) = (5, 3, 0, 6, 4, 1, 2)` of the faces
`014, 015, 034, 0356, 1245, 246, 256, 346`.  `TriGenPar ∧ ¬TriGenTieO` at the quadrilaterals
`0356`, `1245` (vertex `5`) give the frame `Frame18 x`: the basis `u₁ = x 3 - x 5`,
`u₂ = x 4 - x 5`, `e` in which the points are `x 5 = 0`, `x 3 = (1, 0, 0)`, `x 4 = (0, 1, 0)`,
`x 0 = (t+, 0, h+)`, `x 6 = (t-, 0, -h-)`, `x 1 = (0, s+, k+)`, `x 2 = (0, s-, -k-)`, and the
Euclidean metric is `diag(A, g)`.
-/

namespace Minimality.CaseC18

open Finset Minimality.CaseC09
open scoped RealInnerProductSpace

/-- **The normal-form frame of type 18's case (c).** -/
structure Frame18 (x : Fin 7 → ℝ³) where
  e : ℝ³
  S : Shape18
  e_ne : e ≠ 0
  indep : LinearIndependent ℝ ![x 3 - x 5, x 4 - x 5, e]
  x0_eq : x 0 = x 5 + S.tp • (x 3 - x 5) + S.hp • e
  x6_eq : x 6 = x 5 + S.tm • (x 3 - x 5) - S.hm • e
  x1_eq : x 1 = x 5 + S.sp • (x 4 - x 5) + S.kp • e
  x2_eq : x 2 = x 5 + S.sm • (x 4 - x 5) - S.km • e
  inner_u1_e : ⟪x 3 - x 5, e⟫ = 0
  inner_u2_e : ⟪x 4 - x 5, e⟫ = 0
  A12_pos : 0 < ⟪x 3 - x 5, x 4 - x 5⟫
  A12_le_A11 : ⟪x 3 - x 5, x 4 - x 5⟫ ≤ ⟪x 3 - x 5, x 3 - x 5⟫
  A12_le_A22 : ⟪x 3 - x 5, x 4 - x 5⟫ ≤ ⟪x 4 - x 5, x 4 - x 5⟫

section Alg
variable {t u s h z4 z2 : ℝ}

/-- A facet through `xa`, `xb` and one middle, with the other one off it: the roof. -/
lemma roof_of' {χ0 a b c : ℝ} (hs1 : s < 1) (ht1 : t < 1) (hh : 0 < h) (hz2 : 0 < z2)
    (hχ0 : χ0 < 0) (f3 : χ0 + a = 0) (f5 : χ0 + b = 0) (f2 : χ0 + b * s + c * z2 = 0)
    (f1 : χ0 + a * t + c * h < 0) : h / (1 - t) < z2 / (1 - s) :=
  roof_of hs1 ht1 hh hz2 hχ0 f3 f5 f2 f1

end Alg

/-- **The frame from the triple-tie data** (core). -/
theorem frame18_core (x : Fin 7 → ℝ³) (f1 f2 : ℝ³ →ᵃ[ℝ] ℝ)
    (hf1 : ∀ i : Fin 7, (i ∈ ({0, 3, 5, 6} : Finset (Fin 7)) → f1 (x i) = 0) ∧
      (i ∉ ({0, 3, 5, 6} : Finset (Fin 7)) → f1 (x i) < 0))
    (hf2 : ∀ i : Fin 7, (i ∈ ({1, 2, 4, 5} : Finset (Fin 7)) → f2 (x i) = 0) ∧
      (i ∉ ({1, 2, 4, 5} : Finset (Fin 7)) → f2 (x i) < 0))
    (m2 : f2 (x 3) ≤ f2 (x 0) ∧ f2 (x 3) ≤ f2 (x 6))
    (m1 : f1 (x 4) ≤ f1 (x 1) ∧ f1 (x 4) ≤ f1 (x 2))
    (e : ℝ³) (he : e ≠ 0) (h1e : f1 (x 5 + e) = 0) (h2e : f2 (x 5 + e) = 0)
    (hu1e : ⟪x 3 - x 5, e⟫ = 0) (hu2e : ⟪x 4 - x 5, e⟫ = 0)
    (par0 : ∀ c : ℝ, x 0 - x 3 ≠ c • e) (par6 : ∀ c : ℝ, x 6 - x 3 ≠ c • e)
    (par1 : ∀ c : ℝ, x 1 - x 4 ≠ c • e) (par2 : ∀ c : ℝ, x 2 - x 4 ≠ c • e)
    (a12 : 0 < ⟪x 3 - x 5, x 4 - x 5⟫) (a11 : ⟪x 4 - x 3, x 3 - x 5⟫ ≤ 0)
    (a22 : ⟪x 3 - x 4, x 4 - x 5⟫ ≤ 0) (hz : 0 < ⟪x 0 - x 5, e⟫)
    (φ014 φ015 φ034 φ246 φ346 : ℝ³ →ᵃ[ℝ] ℝ)
    (h014 : ∀ i : Fin 7, (i ∈ ({0, 1, 4} : Finset (Fin 7)) → φ014 (x i) = 0) ∧
      (i ∉ ({0, 1, 4} : Finset (Fin 7)) → φ014 (x i) < 0))
    (h015 : ∀ i : Fin 7, (i ∈ ({0, 1, 5} : Finset (Fin 7)) → φ015 (x i) = 0) ∧
      (i ∉ ({0, 1, 5} : Finset (Fin 7)) → φ015 (x i) < 0))
    (h034 : ∀ i : Fin 7, (i ∈ ({0, 3, 4} : Finset (Fin 7)) → φ034 (x i) = 0) ∧
      (i ∉ ({0, 3, 4} : Finset (Fin 7)) → φ034 (x i) < 0))
    (h246 : ∀ i : Fin 7, (i ∈ ({2, 4, 6} : Finset (Fin 7)) → φ246 (x i) = 0) ∧
      (i ∉ ({2, 4, 6} : Finset (Fin 7)) → φ246 (x i) < 0))
    (h346 : ∀ i : Fin 7, (i ∈ ({3, 4, 6} : Finset (Fin 7)) → φ346 (x i) = 0) ∧
      (i ∉ ({3, 4, 6} : Finset (Fin 7)) → φ346 (x i) < 0)) :
    Nonempty (Frame18 x) := by
  have h1v : f1 (x 5) = 0 := (hf1 5).1 (by decide)
  have h1_0 : f1 (x 0) = 0 := (hf1 0).1 (by decide)
  have h1_3 : f1 (x 3) = 0 := (hf1 3).1 (by decide)
  have h1_6 : f1 (x 6) = 0 := (hf1 6).1 (by decide)
  have n1_1 : f1 (x 1) < 0 := (hf1 1).2 (by decide)
  have n1_2 : f1 (x 2) < 0 := (hf1 2).2 (by decide)
  have n1_4 : f1 (x 4) < 0 := (hf1 4).2 (by decide)
  have h2v : f2 (x 5) = 0 := (hf2 5).1 (by decide)
  have h2_1 : f2 (x 1) = 0 := (hf2 1).1 (by decide)
  have h2_2 : f2 (x 2) = 0 := (hf2 2).1 (by decide)
  have h2_4 : f2 (x 4) = 0 := (hf2 4).1 (by decide)
  have n2_0 : f2 (x 0) < 0 := (hf2 0).2 (by decide)
  have n2_3 : f2 (x 3) < 0 := (hf2 3).2 (by decide)
  have n2_6 : f2 (x 6) < 0 := (hf2 6).2 (by decide)
  have hee : 0 < ⟪e, e⟫ := real_inner_self_pos.mpr he
  have hli := frame_indep he h1v h2v h1_3 h2_4 h1e h2e n2_3.ne n1_4.ne hu1e hu2e
  have dec := fun i => frame_decomp he h1v h2v h1_3 h2_4 h1e h2e n2_3.ne n1_4.ne hu1e hu2e (x i)
  obtain ⟨tp, htp⟩ : ∃ r : ℝ, r = f2 (x 0) / f2 (x 3) := ⟨_, rfl⟩
  obtain ⟨tm, htm⟩ : ∃ r : ℝ, r = f2 (x 6) / f2 (x 3) := ⟨_, rfl⟩
  obtain ⟨sp, hsp⟩ : ∃ r : ℝ, r = f1 (x 1) / f1 (x 4) := ⟨_, rfl⟩
  obtain ⟨sm, hsm⟩ : ∃ r : ℝ, r = f1 (x 2) / f1 (x 4) := ⟨_, rfl⟩
  obtain ⟨hp, hhp⟩ : ∃ r : ℝ, r = ⟪x 0 - x 5, e⟫ / ⟪e, e⟫ := ⟨_, rfl⟩
  obtain ⟨z6, hz6⟩ : ∃ r : ℝ, r = ⟪x 6 - x 5, e⟫ / ⟪e, e⟫ := ⟨_, rfl⟩
  obtain ⟨kp, hkp⟩ : ∃ r : ℝ, r = ⟪x 1 - x 5, e⟫ / ⟪e, e⟫ := ⟨_, rfl⟩
  obtain ⟨z2, hz2⟩ : ∃ r : ℝ, r = ⟪x 2 - x 5, e⟫ / ⟪e, e⟫ := ⟨_, rfl⟩
  have d0 : x 0 - x 5 = tp • (x 3 - x 5) + hp • e := by
    have := dec 0
    rw [h1_0, zero_div, zero_smul, add_zero, ← htp, ← hhp] at this
    exact this
  have d6 : x 6 - x 5 = tm • (x 3 - x 5) + z6 • e := by
    have := dec 6
    rw [h1_6, zero_div, zero_smul, add_zero, ← htm, ← hz6] at this
    exact this
  have d1 : x 1 - x 5 = sp • (x 4 - x 5) + kp • e := by
    have := dec 1
    rw [h2_1, zero_div, zero_smul, zero_add, ← hsp, ← hkp] at this
    exact this
  have d2 : x 2 - x 5 = sm • (x 4 - x 5) + z2 • e := by
    have := dec 2
    rw [h2_2, zero_div, zero_smul, zero_add, ← hsm, ← hz2] at this
    exact this
  have tp_pos : 0 < tp := by rw [htp]; exact div_pos_of_neg_of_neg n2_0 n2_3
  have tm_pos : 0 < tm := by rw [htm]; exact div_pos_of_neg_of_neg n2_6 n2_3
  have sp_pos : 0 < sp := by rw [hsp]; exact div_pos_of_neg_of_neg n1_1 n1_4
  have sm_pos : 0 < sm := by rw [hsm]; exact div_pos_of_neg_of_neg n1_2 n1_4
  have tp_lt : tp < 1 := by
    refine lt_of_le_of_ne ((div_le_one_of_neg n2_3).mpr m2.1 |> fun h => htp ▸ h) fun h => ?_
    apply par0 hp
    rw [h, one_smul] at d0
    rw [show x 0 - x 3 = (x 0 - x 5) - (x 3 - x 5) by abel, d0]
    abel
  have tm_lt : tm < 1 := by
    refine lt_of_le_of_ne ((div_le_one_of_neg n2_3).mpr m2.2 |> fun h => htm ▸ h) fun h => ?_
    apply par6 z6
    rw [h, one_smul] at d6
    rw [show x 6 - x 3 = (x 6 - x 5) - (x 3 - x 5) by abel, d6]
    abel
  have sp_lt : sp < 1 := by
    refine lt_of_le_of_ne ((div_le_one_of_neg n1_4).mpr m1.1 |> fun h => hsp ▸ h) fun h => ?_
    apply par1 kp
    rw [h, one_smul] at d1
    rw [show x 1 - x 4 = (x 1 - x 5) - (x 4 - x 5) by abel, d1]
    abel
  have sm_lt : sm < 1 := by
    refine lt_of_le_of_ne ((div_le_one_of_neg n1_4).mpr m1.2 |> fun h => hsm ▸ h) fun h => ?_
    apply par2 z2
    rw [h, one_smul] at d2
    rw [show x 2 - x 4 = (x 2 - x 5) - (x 4 - x 5) by abel, d2]
    abel
  have hp_pos : 0 < hp := by rw [hhp]; exact div_pos hz hee
  have ev0 : ∀ φ : ℝ³ →ᵃ[ℝ] ℝ,
      φ (x 0) = φ (x 5) + tp * (φ (x 3) - φ (x 5)) + hp * φ.linear e := by
    intro φ
    have := eval_dec φ (dec 0)
    rw [h1_0, zero_div, zero_mul, add_zero, ← htp, ← hhp] at this
    exact this
  have ev6 : ∀ φ : ℝ³ →ᵃ[ℝ] ℝ,
      φ (x 6) = φ (x 5) + tm * (φ (x 3) - φ (x 5)) + z6 * φ.linear e := by
    intro φ
    have := eval_dec φ (dec 6)
    rw [h1_6, zero_div, zero_mul, add_zero, ← htm, ← hz6] at this
    exact this
  have ev1 : ∀ φ : ℝ³ →ᵃ[ℝ] ℝ,
      φ (x 1) = φ (x 5) + sp * (φ (x 4) - φ (x 5)) + kp * φ.linear e := by
    intro φ
    have := eval_dec φ (dec 1)
    rw [h2_1, zero_div, zero_mul, add_zero, ← hsp, ← hkp] at this
    exact this
  have ev2 : ∀ φ : ℝ³ →ᵃ[ℝ] ℝ,
      φ (x 2) = φ (x 5) + sm * (φ (x 4) - φ (x 5)) + z2 * φ.linear e := by
    intro φ
    have := eval_dec φ (dec 2)
    rw [h2_2, zero_div, zero_mul, add_zero, ← hsm, ← hz2] at this
    exact this
  -- facet 015: m2+ above
  have A0 : φ015 (x 0) = 0 := (h015 0).1 (by decide)
  have A1 : φ015 (x 1) = 0 := (h015 1).1 (by decide)
  have A5 : φ015 (x 5) = 0 := (h015 5).1 (by decide)
  have A3 : φ015 (x 3) < 0 := (h015 3).2 (by decide)
  have A4 : φ015 (x 4) < 0 := (h015 4).2 (by decide)
  have kp_pos : 0 < kp :=
    z2_pos (a := φ015 (x 3) - φ015 (x 5)) (b := φ015 (x 4) - φ015 (x 5)) (c := φ015.linear e)
      tp_pos sp_pos hp_pos (by have := ev0 φ015; linarith) (by have := ev1 φ015; linarith)
      (by linarith) (by linarith)
  -- facets 346, 034: m1- below
  have B5 : φ346 (x 5) < 0 := (h346 5).2 (by decide)
  have B3 : φ346 (x 3) = 0 := (h346 3).1 (by decide)
  have B4 : φ346 (x 4) = 0 := (h346 4).1 (by decide)
  have B6 : φ346 (x 6) = 0 := (h346 6).1 (by decide)
  have B0 : φ346 (x 0) < 0 := (h346 0).2 (by decide)
  have B2 : φ346 (x 2) < 0 := (h346 2).2 (by decide)
  have C5 : φ034 (x 5) < 0 := (h034 5).2 (by decide)
  have C0 : φ034 (x 0) = 0 := (h034 0).1 (by decide)
  have C3 : φ034 (x 3) = 0 := (h034 3).1 (by decide)
  have C4 : φ034 (x 4) = 0 := (h034 4).1 (by decide)
  have C6 : φ034 (x 6) < 0 := (h034 6).2 (by decide)
  have C1 : φ034 (x 1) < 0 := (h034 1).2 (by decide)
  have z6_neg : z6 < 0 :=
    z4_neg (φ0 := φ346 (x 5)) (a := φ346 (x 3) - φ346 (x 5)) (c := φ346.linear e)
      (ψ0 := φ034 (x 5)) (a' := φ034 (x 3) - φ034 (x 5)) (c' := φ034.linear e)
      (t := tp) tm_lt hp_pos B5 C5 (by linarith) (by have := ev6 φ346; linarith)
      (by have := ev0 φ346; linarith) (by linarith) (by have := ev0 φ034; linarith)
      (by have := ev6 φ034; linarith)
  -- facets 246, 014: m2- below
  have D5 : φ246 (x 5) < 0 := (h246 5).2 (by decide)
  have D2 : φ246 (x 2) = 0 := (h246 2).1 (by decide)
  have D4 : φ246 (x 4) = 0 := (h246 4).1 (by decide)
  have D6 : φ246 (x 6) = 0 := (h246 6).1 (by decide)
  have D1 : φ246 (x 1) < 0 := (h246 1).2 (by decide)
  have E5 : φ014 (x 5) < 0 := (h014 5).2 (by decide)
  have E0 : φ014 (x 0) = 0 := (h014 0).1 (by decide)
  have E1 : φ014 (x 1) = 0 := (h014 1).1 (by decide)
  have E4 : φ014 (x 4) = 0 := (h014 4).1 (by decide)
  have E2 : φ014 (x 2) < 0 := (h014 2).2 (by decide)
  have z2_neg : z2 < 0 :=
    z4_neg (φ0 := φ246 (x 5)) (a := φ246 (x 4) - φ246 (x 5)) (c := φ246.linear e)
      (ψ0 := φ014 (x 5)) (a' := φ014 (x 4) - φ014 (x 5)) (c' := φ014.linear e)
      (t := sp) sm_lt kp_pos D5 E5 (by linarith) (by have := ev2 φ246; linarith)
      (by have := ev1 φ246; linarith) (by linarith) (by have := ev1 φ014; linarith)
      (by have := ev2 φ014; linarith)
  -- the roofs
  have roof_p : kp / (1 - sp) < hp / (1 - tp) :=
    roof_of (χ0 := φ034 (x 5)) (a := φ034 (x 4) - φ034 (x 5)) (b := φ034 (x 3) - φ034 (x 5))
      (c := φ034.linear e) (s := tp) (t := sp) tp_lt sp_lt kp_pos hp_pos C5 (by linarith)
      (by linarith) (by have := ev0 φ034; linarith) (by have := ev1 φ034; linarith)
  have roof_m : (-z2) / (1 - sm) < (-z6) / (1 - tm) :=
    roof_of (χ0 := φ346 (x 5)) (a := φ346 (x 4) - φ346 (x 5)) (b := φ346 (x 3) - φ346 (x 5))
      (c := -φ346.linear e) (s := tm) (t := sm) tm_lt sm_lt (neg_pos.2 z2_neg)
      (neg_pos.2 z6_neg) B5 (by linarith) (by linarith)
      (by have := ev6 φ346; linarith) (by have := ev2 φ346; linarith)
  let S : Shape18 :=
    { tp := tp, tm := tm, sp := sp, sm := sm, hp := hp, hm := -z6, kp := kp, km := -z2
      tp_pos := tp_pos, tp_lt := tp_lt, tm_pos := tm_pos, tm_lt := tm_lt
      sp_pos := sp_pos, sp_lt := sp_lt, sm_pos := sm_pos, sm_lt := sm_lt
      hp_pos := hp_pos, hm_pos := neg_pos.2 z6_neg, kp_pos := kp_pos, km_pos := neg_pos.2 z2_neg
      roof_p := roof_p, roof_m := roof_m }
  refine ⟨{ e := e
            S := S
            e_ne := he
            indep := hli
            x0_eq := ?_
            x6_eq := ?_
            x1_eq := ?_
            x2_eq := ?_
            inner_u1_e := hu1e
            inner_u2_e := hu2e
            A12_pos := a12
            A12_le_A11 := ?_
            A12_le_A22 := ?_ }⟩
  · show x 0 = x 5 + tp • (x 3 - x 5) + hp • e
    rw [add_assoc, ← d0]; abel
  · show x 6 = x 5 + tm • (x 3 - x 5) - (-z6) • e
    rw [neg_smul, sub_neg_eq_add, add_assoc, ← d6]; abel
  · show x 1 = x 5 + sp • (x 4 - x 5) + kp • e
    rw [add_assoc, ← d1]; abel
  · show x 2 = x 5 + sm • (x 4 - x 5) - (-z2) • e
    rw [neg_smul, sub_neg_eq_add, add_assoc, ← d2]; abel
  · have : ⟪x 4 - x 3, x 3 - x 5⟫ = ⟪x 4 - x 5, x 3 - x 5⟫ - ⟪x 3 - x 5, x 3 - x 5⟫ := by
      rw [← inner_sub_left]; congr 1; abel
    have c : ⟪x 4 - x 5, x 3 - x 5⟫ = ⟪x 3 - x 5, x 4 - x 5⟫ := real_inner_comm _ _
    linarith
  · have : ⟪x 3 - x 4, x 4 - x 5⟫ = ⟪x 3 - x 5, x 4 - x 5⟫ - ⟪x 4 - x 5, x 4 - x 5⟫ := by
      rw [← inner_sub_left]; congr 1; abel
    linarith

/-- **The normal-form frame of type 18's acute case (c).**  `TriGenPar` and `¬TriGenTieO` for the
faces `0356`, `1245` at the vertex `5` of a type-18 realization give the frame `Frame18 x`. -/
theorem frame18 {x : Fin 7 → ℝ³} (hx : Function.Injective x)
    (hgen : NoThreeCollinear (Finset.univ.image x))
    (hR : RealizesFaces x (sevenTypeFaces 17))
    (hP : TriGenPar (Finset.univ.image x) (({0, 3, 5, 6} : Finset (Fin 7)).image x)
      (({1, 2, 4, 5} : Finset (Fin 7)).image x) (x 5))
    (hT : ¬ TriGenTieO (Finset.univ.image x) (({0, 3, 5, 6} : Finset (Fin 7)).image x)
      (({1, 2, 4, 5} : Finset (Fin 7)).image x) (x 5)) : Nonempty (Frame18 x) := by
  classical
  obtain ⟨f1, f2, z1, n1, z2, n2, e, he, e1, e2, hpar, p, hp, q, hq, hpq, hmin1, hmin2, htie,
    hvp, hacute, ha1, ha2, hos1, hos2⟩ := not_tieO_data hP hT
  obtain ⟨φ014, h014⟩ := hR {0, 1, 4} (by decide)
  obtain ⟨φ015, h015⟩ := hR {0, 1, 5} (by decide)
  obtain ⟨φ034, h034⟩ := hR {0, 3, 4} (by decide)
  obtain ⟨φ246, h246⟩ := hR {2, 4, 6} (by decide)
  obtain ⟨φ256, h256⟩ := hR {2, 5, 6} (by decide)
  obtain ⟨φ346, h346⟩ := hR {3, 4, 6} (by decide)
  have hf1 : ∀ i : Fin 7, (i ∈ ({0, 3, 5, 6} : Finset (Fin 7)) → f1 (x i) = 0) ∧
      (i ∉ ({0, 3, 5, 6} : Finset (Fin 7)) → f1 (x i) < 0) := fun i =>
    ⟨fun hi => z1 _ (Finset.mem_image_of_mem x hi), fun hi =>
      n1 _ (Finset.mem_image_of_mem x (Finset.mem_univ i))
        (fun h => hi (hx.mem_finset_image.mp h))⟩
  have hf2 : ∀ i : Fin 7, (i ∈ ({1, 2, 4, 5} : Finset (Fin 7)) → f2 (x i) = 0) ∧
      (i ∉ ({1, 2, 4, 5} : Finset (Fin 7)) → f2 (x i) < 0) := fun i =>
    ⟨fun hi => z2 _ (Finset.mem_image_of_mem x hi), fun hi =>
      n2 _ (Finset.mem_image_of_mem x (Finset.mem_univ i))
        (fun h => hi (hx.mem_finset_image.mp h))⟩
  have h1v : f1 (x 5) = 0 := (hf1 5).1 (by decide)
  have h2v : f2 (x 5) = 0 := (hf2 5).1 (by decide)
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
  have hiS : i = 0 ∨ i = 3 ∨ i = 6 := by
    have h0 : i ≠ 5 := by
      rintro rfl
      have := hmin1 (x 0) (Finset.mem_image_of_mem x (by decide))
      have := (hf2 0).2 (by decide)
      linarith
    exact (by decide : ∀ i : Fin 7, i ∈ ({0, 3, 5, 6} : Finset (Fin 7)) → i ≠ 5 →
      (i = 0 ∨ i = 3 ∨ i = 6)) i hi h0
  have hjS : j = 1 ∨ j = 2 ∨ j = 4 := by
    have h0 : j ≠ 5 := by
      rintro rfl
      have := hmin2 (x 1) (Finset.mem_image_of_mem x (by decide))
      have := (hf1 1).2 (by decide)
      linarith
    exact (by decide : ∀ j : Fin 7, j ∈ ({1, 2, 4, 5} : Finset (Fin 7)) → j ≠ 5 →
      (j = 1 ∨ j = 2 ∨ j = 4)) j hj h0
  have h2p : f2 (x i) < 0 := (hf2 i).2 (by rcases hiS with rfl | rfl | rfl <;> decide)
  have h1q : f1 (x j) < 0 := (hf1 j).2 (by rcases hjS with rfl | rfl | rfl <;> decide)
  have h1p : f1 (x i) = 0 := (hf1 i).1 hi
  have h2q : f2 (x j) = 0 := (hf2 j).1 hj
  have hpe : ⟪x i - x 5, e⟫ = 0 := by rw [inner_sub_left]; linarith
  have hqe : ⟪x j - x 5, e⟫ = 0 := by rw [inner_sub_left]; linarith
  have hQ1 : ∀ (a b c d : Fin 7), ({0, 3, 5, 6} : Finset (Fin 7)) = {a, b, c, d} →
      ∀ y ∈ (({0, 3, 5, 6} : Finset (Fin 7)).image x), y = x a ∨ y = x b ∨ y = x c ∨ y = x d := by
    intro a b c d h y hy
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
    rw [h] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> simp
  have hQ2 : ∀ (a b c d : Fin 7), ({1, 2, 4, 5} : Finset (Fin 7)) = {a, b, c, d} →
      ∀ y ∈ (({1, 2, 4, 5} : Finset (Fin 7)).image x), y = x a ∨ y = x b ∨ y = x c ∨ y = x d := by
    intro a b c d h y hy
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
    rw [h] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> simp
  have hi3 : i = 3 := by
    rcases hiS with rfl | h | rfl
    · exact (q1_side_contra (m := x 3) (m' := x 6) he h1v h2v h1p h2q e1 e2 h2p.ne h1q.ne hpe hqe
        ((hf1 3).1 (by decide)) ((hf1 6).1 (by decide)) φ015 ((h015 5).1 (by decide))
        ((h015 0).1 (by decide)) ((h015 3).2 (by decide)) ((h015 6).2 (by decide))
        (hQ1 5 0 3 6 (by decide)) hos1).elim
    · exact h
    · exact (q1_side_contra (m := x 0) (m' := x 3) he h1v h2v h1p h2q e1 e2 h2p.ne h1q.ne hpe hqe
        ((hf1 0).1 (by decide)) ((hf1 3).1 (by decide)) φ256 ((h256 5).1 (by decide))
        ((h256 6).1 (by decide)) ((h256 0).2 (by decide)) ((h256 3).2 (by decide))
        (hQ1 5 6 0 3 (by decide)) hos1).elim
  subst hi3
  have hj4 : j = 4 := by
    rcases hjS with rfl | rfl | h
    · exact (q2_side_contra (m := x 2) (m' := x 4) he h1v h2v h1p h2q e1 e2 h2p.ne h1q.ne hpe hqe
        ((hf2 2).1 (by decide)) ((hf2 4).1 (by decide)) φ015 ((h015 5).1 (by decide))
        ((h015 1).1 (by decide)) ((h015 2).2 (by decide)) ((h015 4).2 (by decide))
        (hQ2 5 1 2 4 (by decide)) hos2).elim
    · exact (q2_side_contra (m := x 1) (m' := x 4) he h1v h2v h1p h2q e1 e2 h2p.ne h1q.ne hpe hqe
        ((hf2 1).1 (by decide)) ((hf2 4).1 (by decide)) φ256 ((h256 5).1 (by decide))
        ((h256 2).1 (by decide)) ((h256 1).2 (by decide)) ((h256 4).2 (by decide))
        (hQ2 5 2 1 4 (by decide)) hos2).elim
    · exact h
  subst hj4
  have fm1 : ∀ y : Fin 7, y ∈ ({0, 6} : Finset (Fin 7)) → ∀ c : ℝ, x y - x 3 ≠ c • e := by
    intro y hy c hc
    have hne : x 3 ≠ x y := hx.ne
      ((by decide : ∀ y : Fin 7, y ∈ ({0, 6} : Finset (Fin 7)) → 3 ≠ y) y hy)
    exact not_midPair_far1 (Finset.mem_image_of_mem x (by decide))
      (fun h => absurd (hx.mem_finset_image.mp h) (by decide)) hmin1
      (hpar (x 3) (Finset.mem_image_of_mem x (Finset.mem_univ _)) (x y)
        (Finset.mem_image_of_mem x (Finset.mem_univ _)) hne c hc)
  have fm2 : ∀ y : Fin 7, y ∈ ({1, 2} : Finset (Fin 7)) → ∀ c : ℝ, x y - x 4 ≠ c • e := by
    intro y hy c hc
    have hne : x 4 ≠ x y := hx.ne
      ((by decide : ∀ y : Fin 7, y ∈ ({1, 2} : Finset (Fin 7)) → 4 ≠ y) y hy)
    exact not_midPair_far2 (Finset.mem_image_of_mem x (by decide))
      (fun h => absurd (hx.mem_finset_image.mp h) (by decide)) hmin2
      (hpar (x 4) (Finset.mem_image_of_mem x (Finset.mem_univ _)) (x y)
        (Finset.mem_image_of_mem x (Finset.mem_univ _)) hne c hc)
  have m2 : f2 (x 3) ≤ f2 (x 0) ∧ f2 (x 3) ≤ f2 (x 6) :=
    ⟨hmin1 _ (Finset.mem_image_of_mem x (by decide)), hmin1 _ (Finset.mem_image_of_mem x (by decide))⟩
  have m1 : f1 (x 4) ≤ f1 (x 1) ∧ f1 (x 4) ≤ f1 (x 2) :=
    ⟨hmin2 _ (Finset.mem_image_of_mem x (by decide)), hmin2 _ (Finset.mem_image_of_mem x (by decide))⟩
  have hzne : ⟪x 0 - x 5, e⟫ ≠ 0 := by
    intro h0
    have d := frame_decomp he h1v h2v h1p h2q e1 e2 h2p.ne h1q.ne hpe hqe (x 0)
    rw [(hf1 0).1 (by decide), zero_div, zero_smul, add_zero, h0, zero_div, zero_smul,
      add_zero] at d
    exact hgen (x 5) (Finset.mem_image_of_mem x (Finset.mem_univ _)) (x 3)
      (Finset.mem_image_of_mem x (Finset.mem_univ _)) (x 0)
      (Finset.mem_image_of_mem x (Finset.mem_univ _)) (hx.ne (by decide)) (hx.ne (by decide))
      (hx.ne (by decide)) _ d
  have a11 : ⟪x 4 - x 3, x 3 - x 5⟫ ≤ 0 := ha1
  have a22 : ⟪x 3 - x 4, x 4 - x 5⟫ ≤ 0 := ha2
  have key : ∀ e' : ℝ³, e' ≠ 0 → f1 (x 5 + e') = 0 → f2 (x 5 + e') = 0 →
      ⟪x 3 - x 5, e'⟫ = 0 → ⟪x 4 - x 5, e'⟫ = 0 →
      (∀ c : ℝ, x 0 - x 3 ≠ c • e') → (∀ c : ℝ, x 6 - x 3 ≠ c • e') →
      (∀ c : ℝ, x 1 - x 4 ≠ c • e') → (∀ c : ℝ, x 2 - x 4 ≠ c • e') →
      0 < ⟪x 0 - x 5, e'⟫ → Nonempty (Frame18 x) :=
    fun e' he' a b c d p0 p6 p1 p2 hz' =>
      frame18_core x f1 f2 hf1 hf2 m2 m1 e' he' a b c d p0 p6 p1 p2 hacute a11 a22 hz'
        φ014 φ015 φ034 φ246 φ346 h014 h015 h034 h246 h346
  rcases lt_or_gt_of_ne hzne with hneg | hpos
  · have hl1 : f1 (x 5 + -e) = 0 := by
      have := aff_add f1 (x 5) (-e); have := aff_add f1 (x 5) e
      rw [map_neg] at *; linarith
    have hl2 : f2 (x 5 + -e) = 0 := by
      have := aff_add f2 (x 5) (-e); have := aff_add f2 (x 5) e
      rw [map_neg] at *; linarith
    refine key (-e) (neg_ne_zero.mpr he) hl1 hl2 (by rw [inner_neg_right, hpe, neg_zero])
      (by rw [inner_neg_right, hqe, neg_zero])
      (fun c h => fm1 0 (by decide) (-c) (by rw [h, smul_neg, neg_smul]))
      (fun c h => fm1 6 (by decide) (-c) (by rw [h, smul_neg, neg_smul]))
      (fun c h => fm2 1 (by decide) (-c) (by rw [h, smul_neg, neg_smul]))
      (fun c h => fm2 2 (by decide) (-c) (by rw [h, smul_neg, neg_smul])) ?_
    rw [inner_neg_right]; linarith
  · exact key e he e1 e2 hpe hqe (fm1 0 (by decide)) (fm1 6 (by decide)) (fm2 1 (by decide))
      (fm2 2 (by decide)) hpos

end Minimality.CaseC18

end
