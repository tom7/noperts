module

public import Minimality.CaseC09Frame
public import Minimality.CaseC20Alg

@[expose] public section

/-!
# Type 20, acute case (c): the normal-form frame (`FEWER-FACES-PROOFS.md` §27, continued (2) §0)

Labels `(v, xa, m1+, m1-, xb, m2+, m2-) = (5, 1, 0, 3, 6, 2, 4)` of the faces
`0135, 016, 025, 026, 134, 146, 2456, 345`.  `TriGenPar ∧ ¬TriGenTieO` at the quadrilaterals
`0135`, `2456` (vertex `5`) give the frame `Frame20 x`: the basis `u₁ = x 1 - x 5`,
`u₂ = x 6 - x 5`, `e` in which the points are `x 5 = 0`, `x 1 = (1, 0, 0)`, `x 6 = (0, 1, 0)`,
`x 0 = (t+, 0, h+)`, `x 3 = (t-, 0, -h-)`, `x 2 = (0, s+, k+)`, `x 4 = (0, s-, -k-)`, and the
Euclidean metric is `diag(A, g)`.  The roofs are `d+ < b+` (face `016`) and `b- < d-` (face `146`).
-/

namespace Minimality.CaseC20

open Finset Minimality.CaseC09
open scoped RealInnerProductSpace

/-- **The normal-form frame of type 20's case (c).** -/
structure Frame20 (x : Fin 7 → ℝ³) where
  e : ℝ³
  S : Shape20
  e_ne : e ≠ 0
  indep : LinearIndependent ℝ ![x 1 - x 5, x 6 - x 5, e]
  x0_eq : x 0 = x 5 + S.tp • (x 1 - x 5) + S.hp • e
  x3_eq : x 3 = x 5 + S.tm • (x 1 - x 5) - S.hm • e
  x2_eq : x 2 = x 5 + S.sp • (x 6 - x 5) + S.kp • e
  x4_eq : x 4 = x 5 + S.sm • (x 6 - x 5) - S.km • e
  inner_u1_e : ⟪x 1 - x 5, e⟫ = 0
  inner_u2_e : ⟪x 6 - x 5, e⟫ = 0
  A12_pos : 0 < ⟪x 1 - x 5, x 6 - x 5⟫
  A12_le_A11 : ⟪x 1 - x 5, x 6 - x 5⟫ ≤ ⟪x 1 - x 5, x 1 - x 5⟫
  A12_le_A22 : ⟪x 1 - x 5, x 6 - x 5⟫ ≤ ⟪x 6 - x 5, x 6 - x 5⟫

/-- **The frame from the triple-tie data** (core). -/
theorem frame20_core (x : Fin 7 → ℝ³) (f1 f2 : ℝ³ →ᵃ[ℝ] ℝ)
    (hf1 : ∀ i : Fin 7, (i ∈ ({0, 1, 3, 5} : Finset (Fin 7)) → f1 (x i) = 0) ∧
      (i ∉ ({0, 1, 3, 5} : Finset (Fin 7)) → f1 (x i) < 0))
    (hf2 : ∀ i : Fin 7, (i ∈ ({2, 4, 5, 6} : Finset (Fin 7)) → f2 (x i) = 0) ∧
      (i ∉ ({2, 4, 5, 6} : Finset (Fin 7)) → f2 (x i) < 0))
    (m2 : f2 (x 1) ≤ f2 (x 0) ∧ f2 (x 1) ≤ f2 (x 3))
    (m1 : f1 (x 6) ≤ f1 (x 2) ∧ f1 (x 6) ≤ f1 (x 4))
    (e : ℝ³) (he : e ≠ 0) (h1e : f1 (x 5 + e) = 0) (h2e : f2 (x 5 + e) = 0)
    (hu1e : ⟪x 1 - x 5, e⟫ = 0) (hu2e : ⟪x 6 - x 5, e⟫ = 0)
    (par0 : ∀ c : ℝ, x 0 - x 1 ≠ c • e) (par3 : ∀ c : ℝ, x 3 - x 1 ≠ c • e)
    (par2 : ∀ c : ℝ, x 2 - x 6 ≠ c • e) (par4 : ∀ c : ℝ, x 4 - x 6 ≠ c • e)
    (a12 : 0 < ⟪x 1 - x 5, x 6 - x 5⟫) (a11 : ⟪x 6 - x 1, x 1 - x 5⟫ ≤ 0)
    (a22 : ⟪x 1 - x 6, x 6 - x 5⟫ ≤ 0) (hz : 0 < ⟪x 0 - x 5, e⟫)
    (φ016 φ025 φ026 φ134 φ146 : ℝ³ →ᵃ[ℝ] ℝ)
    (h016 : ∀ i : Fin 7, (i ∈ ({0, 1, 6} : Finset (Fin 7)) → φ016 (x i) = 0) ∧
      (i ∉ ({0, 1, 6} : Finset (Fin 7)) → φ016 (x i) < 0))
    (h025 : ∀ i : Fin 7, (i ∈ ({0, 2, 5} : Finset (Fin 7)) → φ025 (x i) = 0) ∧
      (i ∉ ({0, 2, 5} : Finset (Fin 7)) → φ025 (x i) < 0))
    (h026 : ∀ i : Fin 7, (i ∈ ({0, 2, 6} : Finset (Fin 7)) → φ026 (x i) = 0) ∧
      (i ∉ ({0, 2, 6} : Finset (Fin 7)) → φ026 (x i) < 0))
    (h134 : ∀ i : Fin 7, (i ∈ ({1, 3, 4} : Finset (Fin 7)) → φ134 (x i) = 0) ∧
      (i ∉ ({1, 3, 4} : Finset (Fin 7)) → φ134 (x i) < 0))
    (h146 : ∀ i : Fin 7, (i ∈ ({1, 4, 6} : Finset (Fin 7)) → φ146 (x i) = 0) ∧
      (i ∉ ({1, 4, 6} : Finset (Fin 7)) → φ146 (x i) < 0)) :
    Nonempty (Frame20 x) := by
  have h1v : f1 (x 5) = 0 := (hf1 5).1 (by decide)
  have h1_0 : f1 (x 0) = 0 := (hf1 0).1 (by decide)
  have h1_1 : f1 (x 1) = 0 := (hf1 1).1 (by decide)
  have h1_3 : f1 (x 3) = 0 := (hf1 3).1 (by decide)
  have n1_2 : f1 (x 2) < 0 := (hf1 2).2 (by decide)
  have n1_4 : f1 (x 4) < 0 := (hf1 4).2 (by decide)
  have n1_6 : f1 (x 6) < 0 := (hf1 6).2 (by decide)
  have h2v : f2 (x 5) = 0 := (hf2 5).1 (by decide)
  have h2_2 : f2 (x 2) = 0 := (hf2 2).1 (by decide)
  have h2_4 : f2 (x 4) = 0 := (hf2 4).1 (by decide)
  have h2_6 : f2 (x 6) = 0 := (hf2 6).1 (by decide)
  have n2_0 : f2 (x 0) < 0 := (hf2 0).2 (by decide)
  have n2_1 : f2 (x 1) < 0 := (hf2 1).2 (by decide)
  have n2_3 : f2 (x 3) < 0 := (hf2 3).2 (by decide)
  have hee : 0 < ⟪e, e⟫ := real_inner_self_pos.mpr he
  have hli := frame_indep he h1v h2v h1_1 h2_6 h1e h2e n2_1.ne n1_6.ne hu1e hu2e
  have dec := fun i => frame_decomp he h1v h2v h1_1 h2_6 h1e h2e n2_1.ne n1_6.ne hu1e hu2e (x i)
  obtain ⟨tp, htp⟩ : ∃ r : ℝ, r = f2 (x 0) / f2 (x 1) := ⟨_, rfl⟩
  obtain ⟨tm, htm⟩ : ∃ r : ℝ, r = f2 (x 3) / f2 (x 1) := ⟨_, rfl⟩
  obtain ⟨sp, hsp⟩ : ∃ r : ℝ, r = f1 (x 2) / f1 (x 6) := ⟨_, rfl⟩
  obtain ⟨sm, hsm⟩ : ∃ r : ℝ, r = f1 (x 4) / f1 (x 6) := ⟨_, rfl⟩
  obtain ⟨hp, hhp⟩ : ∃ r : ℝ, r = ⟪x 0 - x 5, e⟫ / ⟪e, e⟫ := ⟨_, rfl⟩
  obtain ⟨z3, hz3⟩ : ∃ r : ℝ, r = ⟪x 3 - x 5, e⟫ / ⟪e, e⟫ := ⟨_, rfl⟩
  obtain ⟨kp, hkp⟩ : ∃ r : ℝ, r = ⟪x 2 - x 5, e⟫ / ⟪e, e⟫ := ⟨_, rfl⟩
  obtain ⟨z4, hz4⟩ : ∃ r : ℝ, r = ⟪x 4 - x 5, e⟫ / ⟪e, e⟫ := ⟨_, rfl⟩
  have d0 : x 0 - x 5 = tp • (x 1 - x 5) + hp • e := by
    have := dec 0
    rw [h1_0, zero_div, zero_smul, add_zero, ← htp, ← hhp] at this
    exact this
  have d3 : x 3 - x 5 = tm • (x 1 - x 5) + z3 • e := by
    have := dec 3
    rw [h1_3, zero_div, zero_smul, add_zero, ← htm, ← hz3] at this
    exact this
  have d2 : x 2 - x 5 = sp • (x 6 - x 5) + kp • e := by
    have := dec 2
    rw [h2_2, zero_div, zero_smul, zero_add, ← hsp, ← hkp] at this
    exact this
  have d4 : x 4 - x 5 = sm • (x 6 - x 5) + z4 • e := by
    have := dec 4
    rw [h2_4, zero_div, zero_smul, zero_add, ← hsm, ← hz4] at this
    exact this
  have tp_pos : 0 < tp := by rw [htp]; exact div_pos_of_neg_of_neg n2_0 n2_1
  have tm_pos : 0 < tm := by rw [htm]; exact div_pos_of_neg_of_neg n2_3 n2_1
  have sp_pos : 0 < sp := by rw [hsp]; exact div_pos_of_neg_of_neg n1_2 n1_6
  have sm_pos : 0 < sm := by rw [hsm]; exact div_pos_of_neg_of_neg n1_4 n1_6
  have tp_lt : tp < 1 := by
    refine lt_of_le_of_ne ((div_le_one_of_neg n2_1).mpr m2.1 |> fun h => htp ▸ h) fun h => ?_
    apply par0 hp
    rw [h, one_smul] at d0
    rw [show x 0 - x 1 = (x 0 - x 5) - (x 1 - x 5) by abel, d0]
    abel
  have tm_lt : tm < 1 := by
    refine lt_of_le_of_ne ((div_le_one_of_neg n2_1).mpr m2.2 |> fun h => htm ▸ h) fun h => ?_
    apply par3 z3
    rw [h, one_smul] at d3
    rw [show x 3 - x 1 = (x 3 - x 5) - (x 1 - x 5) by abel, d3]
    abel
  have sp_lt : sp < 1 := by
    refine lt_of_le_of_ne ((div_le_one_of_neg n1_6).mpr m1.1 |> fun h => hsp ▸ h) fun h => ?_
    apply par2 kp
    rw [h, one_smul] at d2
    rw [show x 2 - x 6 = (x 2 - x 5) - (x 6 - x 5) by abel, d2]
    abel
  have sm_lt : sm < 1 := by
    refine lt_of_le_of_ne ((div_le_one_of_neg n1_6).mpr m1.2 |> fun h => hsm ▸ h) fun h => ?_
    apply par4 z4
    rw [h, one_smul] at d4
    rw [show x 4 - x 6 = (x 4 - x 5) - (x 6 - x 5) by abel, d4]
    abel
  have hp_pos : 0 < hp := by rw [hhp]; exact div_pos hz hee
  have ev0 : ∀ φ : ℝ³ →ᵃ[ℝ] ℝ,
      φ (x 0) = φ (x 5) + tp * (φ (x 1) - φ (x 5)) + hp * φ.linear e := by
    intro φ
    have := eval_dec φ (dec 0)
    rw [h1_0, zero_div, zero_mul, add_zero, ← htp, ← hhp] at this
    exact this
  have ev3 : ∀ φ : ℝ³ →ᵃ[ℝ] ℝ,
      φ (x 3) = φ (x 5) + tm * (φ (x 1) - φ (x 5)) + z3 * φ.linear e := by
    intro φ
    have := eval_dec φ (dec 3)
    rw [h1_3, zero_div, zero_mul, add_zero, ← htm, ← hz3] at this
    exact this
  have ev2 : ∀ φ : ℝ³ →ᵃ[ℝ] ℝ,
      φ (x 2) = φ (x 5) + sp * (φ (x 6) - φ (x 5)) + kp * φ.linear e := by
    intro φ
    have := eval_dec φ (dec 2)
    rw [h2_2, zero_div, zero_mul, add_zero, ← hsp, ← hkp] at this
    exact this
  have ev4 : ∀ φ : ℝ³ →ᵃ[ℝ] ℝ,
      φ (x 4) = φ (x 5) + sm * (φ (x 6) - φ (x 5)) + z4 * φ.linear e := by
    intro φ
    have := eval_dec φ (dec 4)
    rw [h2_4, zero_div, zero_mul, add_zero, ← hsm, ← hz4] at this
    exact this
  -- facet 025: m2+ above
  have A0 : φ025 (x 0) = 0 := (h025 0).1 (by decide)
  have A2 : φ025 (x 2) = 0 := (h025 2).1 (by decide)
  have A5 : φ025 (x 5) = 0 := (h025 5).1 (by decide)
  have A1 : φ025 (x 1) < 0 := (h025 1).2 (by decide)
  have A6 : φ025 (x 6) < 0 := (h025 6).2 (by decide)
  have kp_pos : 0 < kp :=
    z2_pos (a := φ025 (x 1) - φ025 (x 5)) (b := φ025 (x 6) - φ025 (x 5)) (c := φ025.linear e)
      tp_pos sp_pos hp_pos (by have := ev0 φ025; linarith) (by have := ev2 φ025; linarith)
      (by linarith) (by linarith)
  -- facets 134, 016: m1- below
  have B5 : φ134 (x 5) < 0 := (h134 5).2 (by decide)
  have B1 : φ134 (x 1) = 0 := (h134 1).1 (by decide)
  have B3 : φ134 (x 3) = 0 := (h134 3).1 (by decide)
  have B4 : φ134 (x 4) = 0 := (h134 4).1 (by decide)
  have B0 : φ134 (x 0) < 0 := (h134 0).2 (by decide)
  have B6 : φ134 (x 6) < 0 := (h134 6).2 (by decide)
  have C5 : φ016 (x 5) < 0 := (h016 5).2 (by decide)
  have C0 : φ016 (x 0) = 0 := (h016 0).1 (by decide)
  have C1 : φ016 (x 1) = 0 := (h016 1).1 (by decide)
  have C6 : φ016 (x 6) = 0 := (h016 6).1 (by decide)
  have C3 : φ016 (x 3) < 0 := (h016 3).2 (by decide)
  have C2 : φ016 (x 2) < 0 := (h016 2).2 (by decide)
  have z3_neg : z3 < 0 :=
    z4_neg (φ0 := φ134 (x 5)) (a := φ134 (x 1) - φ134 (x 5)) (c := φ134.linear e)
      (ψ0 := φ016 (x 5)) (a' := φ016 (x 1) - φ016 (x 5)) (c' := φ016.linear e)
      (t := tp) tm_lt hp_pos B5 C5 (by linarith) (by have := ev3 φ134; linarith)
      (by have := ev0 φ134; linarith) (by linarith) (by have := ev0 φ016; linarith)
      (by have := ev3 φ016; linarith)
  -- facets 146, 026: m2- below
  have D5 : φ146 (x 5) < 0 := (h146 5).2 (by decide)
  have D1 : φ146 (x 1) = 0 := (h146 1).1 (by decide)
  have D4 : φ146 (x 4) = 0 := (h146 4).1 (by decide)
  have D6 : φ146 (x 6) = 0 := (h146 6).1 (by decide)
  have D2 : φ146 (x 2) < 0 := (h146 2).2 (by decide)
  have D3 : φ146 (x 3) < 0 := (h146 3).2 (by decide)
  have E5 : φ026 (x 5) < 0 := (h026 5).2 (by decide)
  have E0 : φ026 (x 0) = 0 := (h026 0).1 (by decide)
  have E2 : φ026 (x 2) = 0 := (h026 2).1 (by decide)
  have E6 : φ026 (x 6) = 0 := (h026 6).1 (by decide)
  have E4 : φ026 (x 4) < 0 := (h026 4).2 (by decide)
  have z4_neg' : z4 < 0 :=
    z4_neg (φ0 := φ146 (x 5)) (a := φ146 (x 6) - φ146 (x 5)) (c := φ146.linear e)
      (ψ0 := φ026 (x 5)) (a' := φ026 (x 6) - φ026 (x 5)) (c' := φ026.linear e)
      (t := sp) sm_lt kp_pos D5 E5 (by linarith) (by have := ev4 φ146; linarith)
      (by have := ev2 φ146; linarith) (by linarith) (by have := ev2 φ026; linarith)
      (by have := ev4 φ026; linarith)
  -- the roofs
  have roof_p : kp / (1 - sp) < hp / (1 - tp) :=
    roof_of (χ0 := φ016 (x 5)) (a := φ016 (x 6) - φ016 (x 5)) (b := φ016 (x 1) - φ016 (x 5))
      (c := φ016.linear e) (s := tp) (t := sp) tp_lt sp_lt kp_pos hp_pos C5 (by linarith)
      (by linarith) (by have := ev0 φ016; linarith) (by have := ev2 φ016; linarith)
  have roof_m : (-z3) / (1 - tm) < (-z4) / (1 - sm) :=
    roof_of (χ0 := φ146 (x 5)) (a := φ146 (x 1) - φ146 (x 5)) (b := φ146 (x 6) - φ146 (x 5))
      (c := -φ146.linear e) (s := sm) (t := tm) sm_lt tm_lt (neg_pos.2 z3_neg)
      (neg_pos.2 z4_neg') D5 (by linarith) (by linarith)
      (by have := ev4 φ146; linarith) (by have := ev3 φ146; linarith)
  let S : Shape20 :=
    { tp := tp, tm := tm, sp := sp, sm := sm, hp := hp, hm := -z3, kp := kp, km := -z4
      tp_pos := tp_pos, tp_lt := tp_lt, tm_pos := tm_pos, tm_lt := tm_lt
      sp_pos := sp_pos, sp_lt := sp_lt, sm_pos := sm_pos, sm_lt := sm_lt
      hp_pos := hp_pos, hm_pos := neg_pos.2 z3_neg, kp_pos := kp_pos, km_pos := neg_pos.2 z4_neg'
      roof_p := roof_p, roof_m := roof_m }
  refine ⟨{ e := e
            S := S
            e_ne := he
            indep := hli
            x0_eq := ?_
            x3_eq := ?_
            x2_eq := ?_
            x4_eq := ?_
            inner_u1_e := hu1e
            inner_u2_e := hu2e
            A12_pos := a12
            A12_le_A11 := ?_
            A12_le_A22 := ?_ }⟩
  · show x 0 = x 5 + tp • (x 1 - x 5) + hp • e
    rw [add_assoc, ← d0]; abel
  · show x 3 = x 5 + tm • (x 1 - x 5) - (-z3) • e
    rw [neg_smul, sub_neg_eq_add, add_assoc, ← d3]; abel
  · show x 2 = x 5 + sp • (x 6 - x 5) + kp • e
    rw [add_assoc, ← d2]; abel
  · show x 4 = x 5 + sm • (x 6 - x 5) - (-z4) • e
    rw [neg_smul, sub_neg_eq_add, add_assoc, ← d4]; abel
  · have : ⟪x 6 - x 1, x 1 - x 5⟫ = ⟪x 6 - x 5, x 1 - x 5⟫ - ⟪x 1 - x 5, x 1 - x 5⟫ := by
      rw [← inner_sub_left]; congr 1; abel
    have c : ⟪x 6 - x 5, x 1 - x 5⟫ = ⟪x 1 - x 5, x 6 - x 5⟫ := real_inner_comm _ _
    linarith
  · have : ⟪x 1 - x 6, x 6 - x 5⟫ = ⟪x 1 - x 5, x 6 - x 5⟫ - ⟪x 6 - x 5, x 6 - x 5⟫ := by
      rw [← inner_sub_left]; congr 1; abel
    linarith

/-- **The normal-form frame of type 20's acute case (c).**  `TriGenPar` and `¬TriGenTieO` for the
faces `0135`, `2456` at the vertex `5` of a type-20 realization give the frame `Frame20 x`. -/
theorem frame20 {x : Fin 7 → ℝ³} (hx : Function.Injective x)
    (hgen : NoThreeCollinear (Finset.univ.image x))
    (hR : RealizesFaces x (sevenTypeFaces 19))
    (hP : TriGenPar (Finset.univ.image x) (({0, 1, 3, 5} : Finset (Fin 7)).image x)
      (({2, 4, 5, 6} : Finset (Fin 7)).image x) (x 5))
    (hT : ¬ TriGenTieO (Finset.univ.image x) (({0, 1, 3, 5} : Finset (Fin 7)).image x)
      (({2, 4, 5, 6} : Finset (Fin 7)).image x) (x 5)) : Nonempty (Frame20 x) := by
  classical
  obtain ⟨f1, f2, z1, n1, z2, n2, e, he, e1, e2, hpar, p, hp, q, hq, hpq, hmin1, hmin2, htie,
    hvp, hacute, ha1, ha2, hos1, hos2⟩ := not_tieO_data hP hT
  obtain ⟨φ016, h016⟩ := hR {0, 1, 6} (by decide)
  obtain ⟨φ025, h025⟩ := hR {0, 2, 5} (by decide)
  obtain ⟨φ026, h026⟩ := hR {0, 2, 6} (by decide)
  obtain ⟨φ134, h134⟩ := hR {1, 3, 4} (by decide)
  obtain ⟨φ146, h146⟩ := hR {1, 4, 6} (by decide)
  obtain ⟨φ345, h345⟩ := hR {3, 4, 5} (by decide)
  have hf1 : ∀ i : Fin 7, (i ∈ ({0, 1, 3, 5} : Finset (Fin 7)) → f1 (x i) = 0) ∧
      (i ∉ ({0, 1, 3, 5} : Finset (Fin 7)) → f1 (x i) < 0) := fun i =>
    ⟨fun hi => z1 _ (Finset.mem_image_of_mem x hi), fun hi =>
      n1 _ (Finset.mem_image_of_mem x (Finset.mem_univ i))
        (fun h => hi (hx.mem_finset_image.mp h))⟩
  have hf2 : ∀ i : Fin 7, (i ∈ ({2, 4, 5, 6} : Finset (Fin 7)) → f2 (x i) = 0) ∧
      (i ∉ ({2, 4, 5, 6} : Finset (Fin 7)) → f2 (x i) < 0) := fun i =>
    ⟨fun hi => z2 _ (Finset.mem_image_of_mem x hi), fun hi =>
      n2 _ (Finset.mem_image_of_mem x (Finset.mem_univ i))
        (fun h => hi (hx.mem_finset_image.mp h))⟩
  have h1v : f1 (x 5) = 0 := (hf1 5).1 (by decide)
  have h2v : f2 (x 5) = 0 := (hf2 5).1 (by decide)
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
  have hiS : i = 0 ∨ i = 1 ∨ i = 3 := by
    have h0 : i ≠ 5 := by
      rintro rfl
      have := hmin1 (x 0) (Finset.mem_image_of_mem x (by decide))
      have := (hf2 0).2 (by decide)
      linarith
    exact (by decide : ∀ i : Fin 7, i ∈ ({0, 1, 3, 5} : Finset (Fin 7)) → i ≠ 5 →
      (i = 0 ∨ i = 1 ∨ i = 3)) i hi h0
  have hjS : j = 2 ∨ j = 4 ∨ j = 6 := by
    have h0 : j ≠ 5 := by
      rintro rfl
      have := hmin2 (x 2) (Finset.mem_image_of_mem x (by decide))
      have := (hf1 2).2 (by decide)
      linarith
    exact (by decide : ∀ j : Fin 7, j ∈ ({2, 4, 5, 6} : Finset (Fin 7)) → j ≠ 5 →
      (j = 2 ∨ j = 4 ∨ j = 6)) j hj h0
  have h2p : f2 (x i) < 0 := (hf2 i).2 (by rcases hiS with rfl | rfl | rfl <;> decide)
  have h1q : f1 (x j) < 0 := (hf1 j).2 (by rcases hjS with rfl | rfl | rfl <;> decide)
  have h1p : f1 (x i) = 0 := (hf1 i).1 hi
  have h2q : f2 (x j) = 0 := (hf2 j).1 hj
  have hpe : ⟪x i - x 5, e⟫ = 0 := by rw [inner_sub_left]; linarith
  have hqe : ⟪x j - x 5, e⟫ = 0 := by rw [inner_sub_left]; linarith
  have hQ1 : ∀ (a b c d : Fin 7), ({0, 1, 3, 5} : Finset (Fin 7)) = {a, b, c, d} →
      ∀ y ∈ (({0, 1, 3, 5} : Finset (Fin 7)).image x), y = x a ∨ y = x b ∨ y = x c ∨ y = x d := by
    intro a b c d h y hy
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
    rw [h] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> simp
  have hQ2 : ∀ (a b c d : Fin 7), ({2, 4, 5, 6} : Finset (Fin 7)) = {a, b, c, d} →
      ∀ y ∈ (({2, 4, 5, 6} : Finset (Fin 7)).image x), y = x a ∨ y = x b ∨ y = x c ∨ y = x d := by
    intro a b c d h y hy
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
    rw [h] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> simp
  have hi1 : i = 1 := by
    rcases hiS with rfl | h | rfl
    · exact (q1_side_contra (m := x 1) (m' := x 3) he h1v h2v h1p h2q e1 e2 h2p.ne h1q.ne hpe hqe
        ((hf1 1).1 (by decide)) ((hf1 3).1 (by decide)) φ025 ((h025 5).1 (by decide))
        ((h025 0).1 (by decide)) ((h025 1).2 (by decide)) ((h025 3).2 (by decide))
        (hQ1 5 0 1 3 (by decide)) hos1).elim
    · exact h
    · exact (q1_side_contra (m := x 0) (m' := x 1) he h1v h2v h1p h2q e1 e2 h2p.ne h1q.ne hpe hqe
        ((hf1 0).1 (by decide)) ((hf1 1).1 (by decide)) φ345 ((h345 5).1 (by decide))
        ((h345 3).1 (by decide)) ((h345 0).2 (by decide)) ((h345 1).2 (by decide))
        (hQ1 5 3 0 1 (by decide)) hos1).elim
  subst hi1
  have hj6 : j = 6 := by
    rcases hjS with rfl | rfl | h
    · exact (q2_side_contra (m := x 4) (m' := x 6) he h1v h2v h1p h2q e1 e2 h2p.ne h1q.ne hpe hqe
        ((hf2 4).1 (by decide)) ((hf2 6).1 (by decide)) φ025 ((h025 5).1 (by decide))
        ((h025 2).1 (by decide)) ((h025 4).2 (by decide)) ((h025 6).2 (by decide))
        (hQ2 5 2 4 6 (by decide)) hos2).elim
    · exact (q2_side_contra (m := x 2) (m' := x 6) he h1v h2v h1p h2q e1 e2 h2p.ne h1q.ne hpe hqe
        ((hf2 2).1 (by decide)) ((hf2 6).1 (by decide)) φ345 ((h345 5).1 (by decide))
        ((h345 4).1 (by decide)) ((h345 2).2 (by decide)) ((h345 6).2 (by decide))
        (hQ2 5 4 2 6 (by decide)) hos2).elim
    · exact h
  subst hj6
  have fm1 : ∀ y : Fin 7, y ∈ ({0, 3} : Finset (Fin 7)) → ∀ c : ℝ, x y - x 1 ≠ c • e := by
    intro y hy c hc
    have hne : x 1 ≠ x y := hx.ne
      ((by decide : ∀ y : Fin 7, y ∈ ({0, 3} : Finset (Fin 7)) → 1 ≠ y) y hy)
    exact not_midPair_far1 (Finset.mem_image_of_mem x (by decide))
      (fun h => absurd (hx.mem_finset_image.mp h) (by decide)) hmin1
      (hpar (x 1) (Finset.mem_image_of_mem x (Finset.mem_univ _)) (x y)
        (Finset.mem_image_of_mem x (Finset.mem_univ _)) hne c hc)
  have fm2 : ∀ y : Fin 7, y ∈ ({2, 4} : Finset (Fin 7)) → ∀ c : ℝ, x y - x 6 ≠ c • e := by
    intro y hy c hc
    have hne : x 6 ≠ x y := hx.ne
      ((by decide : ∀ y : Fin 7, y ∈ ({2, 4} : Finset (Fin 7)) → 6 ≠ y) y hy)
    exact not_midPair_far2 (Finset.mem_image_of_mem x (by decide))
      (fun h => absurd (hx.mem_finset_image.mp h) (by decide)) hmin2
      (hpar (x 6) (Finset.mem_image_of_mem x (Finset.mem_univ _)) (x y)
        (Finset.mem_image_of_mem x (Finset.mem_univ _)) hne c hc)
  have m2 : f2 (x 1) ≤ f2 (x 0) ∧ f2 (x 1) ≤ f2 (x 3) :=
    ⟨hmin1 _ (Finset.mem_image_of_mem x (by decide)), hmin1 _ (Finset.mem_image_of_mem x (by decide))⟩
  have m1 : f1 (x 6) ≤ f1 (x 2) ∧ f1 (x 6) ≤ f1 (x 4) :=
    ⟨hmin2 _ (Finset.mem_image_of_mem x (by decide)), hmin2 _ (Finset.mem_image_of_mem x (by decide))⟩
  have hzne : ⟪x 0 - x 5, e⟫ ≠ 0 := by
    intro h0
    have d := frame_decomp he h1v h2v h1p h2q e1 e2 h2p.ne h1q.ne hpe hqe (x 0)
    rw [(hf1 0).1 (by decide), zero_div, zero_smul, add_zero, h0, zero_div, zero_smul,
      add_zero] at d
    exact hgen (x 5) (Finset.mem_image_of_mem x (Finset.mem_univ _)) (x 1)
      (Finset.mem_image_of_mem x (Finset.mem_univ _)) (x 0)
      (Finset.mem_image_of_mem x (Finset.mem_univ _)) (hx.ne (by decide)) (hx.ne (by decide))
      (hx.ne (by decide)) _ d
  have a11 : ⟪x 6 - x 1, x 1 - x 5⟫ ≤ 0 := ha1
  have a22 : ⟪x 1 - x 6, x 6 - x 5⟫ ≤ 0 := ha2
  have key : ∀ e' : ℝ³, e' ≠ 0 → f1 (x 5 + e') = 0 → f2 (x 5 + e') = 0 →
      ⟪x 1 - x 5, e'⟫ = 0 → ⟪x 6 - x 5, e'⟫ = 0 →
      (∀ c : ℝ, x 0 - x 1 ≠ c • e') → (∀ c : ℝ, x 3 - x 1 ≠ c • e') →
      (∀ c : ℝ, x 2 - x 6 ≠ c • e') → (∀ c : ℝ, x 4 - x 6 ≠ c • e') →
      0 < ⟪x 0 - x 5, e'⟫ → Nonempty (Frame20 x) :=
    fun e' he' a b c d p0 p3 p2 p4 hz' =>
      frame20_core x f1 f2 hf1 hf2 m2 m1 e' he' a b c d p0 p3 p2 p4 hacute a11 a22 hz'
        φ016 φ025 φ026 φ134 φ146 h016 h025 h026 h134 h146
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
      (fun c h => fm1 3 (by decide) (-c) (by rw [h, smul_neg, neg_smul]))
      (fun c h => fm2 2 (by decide) (-c) (by rw [h, smul_neg, neg_smul]))
      (fun c h => fm2 4 (by decide) (-c) (by rw [h, smul_neg, neg_smul])) ?_
    rw [inner_neg_right]; linarith
  · exact key e he e1 e2 hpe hqe (fm1 0 (by decide)) (fm1 3 (by decide)) (fm2 2 (by decide))
      (fm2 4 (by decide)) hpos

end Minimality.CaseC20

end
