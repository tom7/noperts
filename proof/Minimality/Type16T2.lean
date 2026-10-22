module

public import Minimality.Type16Vtx
public import Minimality.EdgeKv

@[expose] public section

/-!
# Type 16: Lemma 19.3's `T2` at a limit shape (§22.12)

At the view along `35`, Lemma 19.3's `T1` (the closing `K_3`, rim `(3, 1, 4, x)`) has no Lemma E.
§22.12 closes its horizontal-double-normal residual through the other test of the pair, `T2`
(the vertex crossing `046/145` at `4`): where `K_5` has a weak saddle and `K_3` none, `1` lies
above `4` and `5` along `3 − 5`, and Lemma 19.3 (ii) makes `T2` unimodal.

The approximants carry Lemma 19.3's region with the certificate (`PX16`, `Reg193`); at the limit
the region holds weakly (the normal-form parameters are continuous, `pa16` …), and strictly off
its boundary (`Off193`, codimension 1, so with the horizontal double normal codimension 2).

* `pa16` … `pr16`, `NF16.prm_eq`, `tendsto_prm16`: the parameters as functions of the points.
* `Off193`, `reg193_of_limit`: the region at the limit.
* `T2_nws4`: Lemma 19.3 (ii) — `T2` has no weak saddle when `1` is above `4` and `5` along `3 − 5`.
* `isRupert_T2_at`: the resulting certificate at the limit shape.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### The normal-form parameters as functions of the points -/

/-- The frame determinant `[0 − 3, 5 − 3, 6 − 3]`. -/
noncomputable def pD16 (y : Fin 7 → ℝ³) : ℝ := det3 (y 0 - y 3) (y 5 - y 3) (y 6 - y 3)

/-- The normal-form parameters `(a, b, g, d, p, q, r)` as ratios of determinants. -/
noncomputable def prm16 (y : Fin 7 → ℝ³) : Fin 7 → ℝ :=
  ![det3 (y 2 - y 3) (y 5 - y 3) (y 6 - y 3) / pD16 y,
    det3 (y 0 - y 3) (y 2 - y 3) (y 6 - y 3) / pD16 y,
    det3 (y 0 - y 3) (y 1 - y 3) (y 6 - y 3) / pD16 y,
    det3 (y 0 - y 3) (y 5 - y 3) (y 1 - y 3) / pD16 y,
    det3 (y 4 - y 3) (y 5 - y 3) (y 6 - y 3) / pD16 y,
    det3 (y 0 - y 3) (y 4 - y 3) (y 6 - y 3) / pD16 y,
    det3 (y 0 - y 3) (y 5 - y 3) (y 4 - y 3) / pD16 y]

theorem NF16.pD_eq {x : Fin 7 → ℝ³} (N : NF16 x) : pD16 x = N.D := by
  simp only [pD16, NF16.D]
  rw [N.x0, N.x3, N.x5, N.x6, nfP_sub, nfP_sub, nfP_sub, det3_nfV]
  simp [det3c]

/-- The parameters of a normal form are `prm16`. -/
theorem NF16.prm_eq {x : Fin 7 → ℝ³} (N : NF16 x) :
    prm16 x = ![N.a, N.b, N.g, N.d, N.p, N.q, N.r] := by
  have hD : N.D ≠ 0 := N.hD
  have e := N.pD_eq
  funext i
  fin_cases i <;> simp only [prm16, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val,
    Matrix.head_cons, Matrix.tail_cons] <;>
    rw [e, div_eq_iff hD] <;>
    simp only [NF16.D] <;>
    simp only [N.x0, N.x1, N.x2, N.x3, N.x4, N.x5, N.x6] <;>
    simp only [nfP_sub, det3_nfV, det3c] <;> ring

theorem tendsto_prm16 {x : Fin 7 → ℝ³} (hD : pD16 x ≠ 0) {K : ℕ → Fin 7 → ℝ³}
    (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m))) :
    Tendsto (fun n => prm16 (K n)) atTop (𝓝 (prm16 x)) := by
  have hDt : Tendsto (fun n => pD16 (K n)) atTop (𝓝 (pD16 x)) :=
    Tendsto.det3' ((hK 0).sub (hK 3)) ((hK 5).sub (hK 3)) ((hK 6).sub (hK 3))
  have q : ∀ i j k : Fin 7, Tendsto (fun n => det3 (K n i - K n 3) (K n j - K n 3)
      (K n k - K n 3) / pD16 (K n)) atTop
      (𝓝 (det3 (x i - x 3) (x j - x 3) (x k - x 3) / pD16 x)) := fun i j k =>
    (Tendsto.det3' ((hK i).sub (hK 3)) ((hK j).sub (hK 3)) ((hK k).sub (hK 3))).div hDt hD
  refine tendsto_pi_nhds.mpr fun i => ?_
  fin_cases i
  exacts [q 2 5 6, q 0 2 6, q 0 1 6, q 0 5 1, q 4 5 6, q 0 4 6, q 0 5 4]

/-! ### Lemma 19.3's region at the limit -/

/-- The nine region polynomials of Lemma 19.3 in the parameters `θ = (a, b, g, d, p, q, r)`. -/
def reg193F (θ : Fin 7 → ℝ) : Fin 9 → ℝ :=
  ![(θ 2 - 1) * (θ 4 + θ 6) - θ 3 * (θ 5 - 1), θ 0 * (θ 5 - 1) - (θ 1 - 1) * (θ 4 + θ 6),
    θ 5 * θ 3 - θ 6 * θ 2, θ 5 - θ 2, θ 2 - 1, θ 5 - θ 1, θ 5 * (θ 0 - 1) - θ 1 * (θ 4 - 1),
    θ 3 - 1, θ 3 * θ 5 - (θ 2 - 1) * (θ 4 + θ 6 - 1)]

theorem continuous_reg193F (i : Fin 9) : Continuous fun θ : Fin 7 → ℝ => reg193F θ i := by
  fin_cases i <;> simp only [reg193F, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val,
    Matrix.head_cons, Matrix.tail_cons] <;> fun_prop

theorem reg193_iff {x : Fin 7 → ℝ³} (N : NF16 x) :
    (0 < (N.g - 1) * (N.p + N.r) - N.d * (N.q - 1) ∧
      0 < N.a * (N.q - 1) - (N.b - 1) * (N.p + N.r) ∧ 0 < N.q * N.d - N.r * N.g ∧
      0 < N.q - N.g ∧ 0 < N.g - 1 ∧ 0 < N.q - N.b ∧ 0 < N.q * (N.a - 1) - N.b * (N.p - 1) ∧
      0 < N.d - 1 ∧ 0 < N.d * N.q - (N.g - 1) * (N.p + N.r - 1)) ↔
    ∀ i, 0 < reg193F (prm16 x) i := by
  rw [N.prm_eq]
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ i
    fin_cases i
    exacts [h0, h1, h2, h3, h4, h5, h6, h7, h8]
  · intro h
    exact ⟨h 0, h 1, h 2, h 3, h 4, h 5, h 6, h 7, h 8⟩

/-- **Off the boundary of Lemma 19.3's region**: none of its nine polynomials vanishes (each a
hypersurface of shapes). -/
def Off193 (x : Fin 7 → ℝ³) : Prop := ∀ i, reg193F (prm16 x) i ≠ 0

/-- **Lemma 19.3's region at the limit**: approximants frequently in the region, the limit off
its boundary, give the limit in the region. -/
theorem reg193_of_limit {x : Fin 7 → ℝ³} (T : Type16 x) {K : ℕ → Fin 7 → ℝ³}
    (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m))) (hfreq : ∃ᶠ n in atTop, Reg193 (K n))
    (hoff : Off193 x) : Reg193 x := by
  have hD : pD16 x ≠ 0 := by rw [T.toNF.pD_eq]; exact T.toNF.hD
  have ht := tendsto_prm16 hD hK
  refine ⟨T.toNF, (reg193_iff T.toNF).mpr fun i => ?_⟩
  have hle : 0 ≤ reg193F (prm16 x) i := by
    refine le_of_tendsto_frequently tendsto_const_nhds
      (((continuous_reg193F i).tendsto _).comp ht) (hfreq.mono fun n ⟨N, hN⟩ => ?_)
    exact ((reg193_iff N).mp hN i).le
  exact lt_of_le_of_ne hle (hoff i).symm

/-! ### Lemma 19.3 (ii): `T2` -/

/-- **Lemma 19.3 (ii)**: if `1` lies below `4` and `5` along `5 − 3` (i.e. above them along
`3 − 5`), the rim `(4, 6, 3, 5)` of `T2` has no weak saddle at `vT2`. -/
theorem T2_nws4 {x : Fin 7 → ℝ³} (N : NF16 x) (hf15 : 0 < N.d * N.q - (N.g - 1) * (N.p + N.r - 1))
    (h41 : ⟪x 1, x 5 - x 3⟫ < ⟪x 4, x 5 - x 3⟫) (h51 : ⟪x 1, x 5 - x 3⟫ < ⟪x 5, x 5 - x 3⟫) :
    NWS4 (quad ⟪x 4, N.vT2⟫ ⟪x 6, N.vT2⟫ ⟪x 3, N.vT2⟫ ⟪x 5, N.vT2⟫) := by
  by_contra hN2
  have h53 : ⟪x 5, N.vT2⟫ ≤ ⟪x 3, N.vT2⟫ := by
    simp only [NWS4, quad_0, quad_1, quad_2, quad_3, not_and_or, not_or, not_lt] at hN2
    rcases hN2 with ⟨k1, k2, k3, k4⟩ | ⟨k1, k2, k3, k4⟩
    · exact k4
    · exfalso
      set K := N.q * (N.g + N.d - 1) + N.d * (N.p + N.q + N.r - 1) with hK
      have hK0 : 0 < K := by nlinarith [mul_pos N.hq N.hgd, mul_pos N.hd N.t046_5]
      refine not_weakSep_of_meet (d₀ := x 4) (d₁ := x 3) (e₀ := x 6) (e₁ := x 5) (w := N.vT2)
        (s := (N.g + N.d - 1) * (N.p + N.q + N.r - 1) / K)
        (t := (N.q * (N.g + N.d - 1) + N.d * (N.p + N.q + N.r - 1) - N.d * (N.p + N.q + N.r - 1)) / K)
        (l := -1 / K) (div_pos (mul_pos N.hgd N.t046_5) hK0).le
        ((div_le_one hK0).mpr (by nlinarith [hf15]))
        (div_pos (by nlinarith [mul_pos N.hq N.hgd]) hK0).le
        ((div_le_one hK0).mpr (by nlinarith [mul_pos N.hd N.t046_5])) ?_
        (div_neg_of_neg_of_pos (by norm_num) hK0) (N.vT2_ne hf15) k1 k2 k3 k4
      have hK0' := hK0.ne'
      simp only [NF16.vT2, NF16.f15, NF16.t0146v]
      nf_simp N
      ext k
      simp only [nfP, nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply,
        smul_eq_mul]
      field_simp
      ring
  have e2 : ⟪N.vT2, (x 5 - x 3)⟫ = -N.f15 * (⟪x 4, (x 5 - x 3)⟫ - ⟪x 1, (x 5 - x 3)⟫) +
      N.t0146v * (⟪x 5, (x 5 - x 3)⟫ - ⟪x 1, (x 5 - x 3)⟫) := by
    rw [NF16.vT2_eq]; simp only [inner_add_left, real_inner_smul_left, inner_sub_left]
  have hf : 0 < -N.f15 := by simp only [NF16.f15]; linarith
  have ht : 0 < N.t0146v := N.t0146
  have e1 : ⟪x 5, N.vT2⟫ - ⟪x 3, N.vT2⟫ = ⟪N.vT2, (x 5 - x 3)⟫ := by
    rw [inner_sub_right, real_inner_comm, real_inner_comm (x 3)]
  nlinarith [mul_pos hf (sub_pos.mpr h41), mul_pos ht (sub_pos.mpr h51)]

/-- **`T2` at the limit shape**: on Lemma 19.3's region, with `1` above `4` and `5` along
`3 − 5`, `T2` is a rim certificate at its view, and with no horizontal double normal there or
(G1) (`Sec16`, two triangles: Proposition 22.2) the shape is Rupert. -/
theorem isRupert_T2_at {x : Fin 7 → ℝ³} (T : Type16 x) (hreg : Reg193 x)
    (h41 : ⟪x 1, x 5 - x 3⟫ < ⟪x 4, x 5 - x 3⟫) (h51 : ⟪x 1, x 5 - x 3⟫ < ⟪x 5, x 5 - x 3⟫)
    (hV0 : NoHDNAt (univ.image x) (view16 x (.inr 0)) ∨ Sec16 x (.inr 0)) :
    IsRupert (univ.image x) := by
  obtain ⟨N, hR1, hR2, hD, hqg, hg1, hqb, hc, hd1, hf15⟩ := hreg
  obtain ⟨σ, hσ, hr⟩ := NF16.rim_F3_T2 N hR1 hR2 hD hqg hg1 hqb hc hd1 hf15
    (T2_nws4 N hf15 h41 h51).isRobustUnimodal
  obtain ⟨c, hc0, hce⟩ := N.namedAt_vT2 hσ
  rw [hce] at hr
  refine isRupert_of_rimCert_seq_at T (fun _ => x) (fun m => tendsto_const_nhds) (.inr 0)
    (fun _ => hV0) (Frequently.of_forall fun _ => ⟨⟨c, hc0, hr.rimCert (Or.inr (Or.inl rfl))⟩,
      fun w a b h => h.2.2⟩)

end Minimality

end
