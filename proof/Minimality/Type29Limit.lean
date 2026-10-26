module

public import Minimality.Type29CertCover
public import Minimality.Type29Bridge
public import Minimality.Type16Limit

@[expose] public section

/-!
# Type 29 outside the HDN set and codimension 2 (`FEWER-FACES-PROOFS.md` §28, §18.2, §21)

Every type-29 shape `K` of class K3a or K4a is a limit of shapes `K_n` off the affine special
positions of the cover (the polynomial genericity fields `K3Poly`, `K4Poly`, `K3C1Poly`,
`K4C1Poly`: all polynomials in the eight normal-form parameters), with the same tie as `K` at
the named views.  The cover (`NF29.cert29_K3a_all`, `NF29.cert29_K4a_all`) gives each `K_n` a
certificate `Cert29`; a subsequence carries one labelled certificate, and the limit lemma
(`isRupert_of_tendsto_rimCert`) makes `K` Rupert unless the limit view has a horizontal double
normal.  The route is that of type 16 (`Type16Limit.lean`).

* `nfShape29`, `ineq29`, `NF29.ofParams`: normal-form shapes from parameters.
* `genPoly29`: the product of the polynomial fields, a nonzero polynomial
  (`genPoly29_ne_zero`); `exists_seq_eval_ne_zero_fin`: the shapes off its zero set are dense.
* `restore`-shears (`Type16Limit`) restore one tie.
* `TieInst29`, `SameTie29`, **`OneTieGlobal29`**: ties at the named views; **at most one tie**
  (counting the tie of `s, t` along `ij` and the tie of `i, j` along `st` as one) is the
  codimension-2 condition.  `OneTieGlobal29.oneTie`: it implies the per-view `OneTie29`.
* `exists_certSeq29`, **`isRupert_type29_limit`**: a type-29 shape of class K3a or K4a with at
  most one tie at its named views and no horizontal double normal at them is Rupert.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### Shapes from parameters -/

/-- The normal-form shape of type 29 with parameters `θ = (a0, b0, h0, a2, b2, h2, s, t)` in the
frame `o; E₁, E₂, E₃` (§21.0). -/
noncomputable def nfShape29 (o E₁ E₂ E₃ : ℝ³) (θ : Fin 8 → ℝ) : Fin 7 → ℝ³ :=
  ![nfP o E₁ E₂ E₃ (θ 0) (θ 1) (-θ 2), nfP o E₁ E₂ E₃ 0 0 0,
    nfP o E₁ E₂ E₃ (θ 3) (θ 4) (-θ 5), nfP o E₁ E₂ E₃ 0 0 (-1), nfP o E₁ E₂ E₃ 1 0 0,
    nfP o E₁ E₂ E₃ 0 1 0, nfP o E₁ E₂ E₃ (θ 6) (θ 7) 0]

/-- The inequalities of `NF29` as nineteen positive quantities. -/
def ineq29 (θ : Fin 8 → ℝ) : Fin 19 → ℝ :=
  ![θ 2, θ 5, -θ 0, -θ 4, 1 - (θ 0 + θ 1 + θ 2), 1 - (θ 3 + θ 4 + θ 5),
    θ 5 * θ 1 - θ 2 * θ 4, θ 2 * θ 3 - θ 5 * θ 0, θ 0 * θ 4 - θ 3 * θ 1,
    θ 0 * θ 4 - θ 3 * θ 1 + (θ 1 * (1 - θ 5) - θ 4 * (1 - θ 2)),
    θ 0 * θ 4 - θ 3 * θ 1 + (θ 3 * (1 - θ 2) - θ 0 * (1 - θ 5)),
    -((θ 1 - 1 + θ 2) * θ 3 - θ 0 * θ 4 + θ 0 * (1 - θ 5)),
    θ 0 * θ 4 + (1 - θ 5 - θ 3) * θ 1 - θ 4 * (1 - θ 2), θ 6, θ 7, θ 6 + θ 7 - 1,
    θ 0 * θ 4 - θ 3 * θ 1 + θ 6 * (θ 1 * (1 - θ 5) - θ 4 * (1 - θ 2)) +
      θ 7 * (θ 3 * (1 - θ 2) - θ 0 * (1 - θ 5)),
    -((θ 1 - 1 + θ 2) * θ 6 - θ 0 * θ 7 + θ 0), θ 4 * θ 6 + (1 - θ 5 - θ 3) * θ 7 - θ 4]

/-- The third class coordinate `V` of Lemma 21.2 as a function of the parameters. -/
def vpoly29 (θ : Fin 8 → ℝ) : ℝ := θ 2 * (1 - θ 3 - θ 4) - θ 5 * (1 - θ 0 - θ 1)

/-- **A normal form from parameters** satisfying the inequalities of type 29. -/
noncomputable def NF29.ofParams (o E₁ E₂ E₃ : ℝ³) (θ : Fin 8 → ℝ) (hD : det3 E₁ E₂ E₃ ≠ 0)
    (h : ∀ k, 0 < ineq29 θ k) : NF29 (nfShape29 o E₁ E₂ E₃ θ) where
  o := o
  E₁ := E₁
  E₂ := E₂
  E₃ := E₃
  inj := by
    have h0 : 0 < θ 2 := h 0
    have h2 : 0 < θ 5 := h 1
    have a0 : 0 < -θ 0 := h 2
    have b2 : 0 < -θ 4 := h 3
    have hs : 0 < θ 6 := h 13
    have ht : 0 < θ 7 := h 14
    have hF4 : 0 < θ 5 * θ 1 - θ 2 * θ 4 := h 6
    intro i j e
    fin_cases i <;> fin_cases j <;>
      first
      | rfl
      | (exfalso
         obtain ⟨e1, e2, e3⟩ := nfP_coeffs hD e
         linarith)
      | (exfalso
         obtain ⟨e1, e2, e3⟩ := nfP_coeffs hD e
         have c1 : θ 5 = θ 2 := by linarith
         have c2 : θ 4 = θ 1 := by linarith
         rw [c1, c2] at hF4
         linarith)
  a0 := θ 0
  b0 := θ 1
  h0 := θ 2
  a2 := θ 3
  b2 := θ 4
  h2 := θ 5
  s := θ 6
  t := θ 7
  x0 := rfl
  x1 := rfl
  x2 := rfl
  x3 := rfl
  x4 := rfl
  x5 := rfl
  x6 := rfl
  hD := hD
  hh0 := h 0
  hh2 := h 1
  ha0 := by have : 0 < -θ 0 := h 2; linarith
  hb2 := by have : 0 < -θ 4 := h 3; linarith
  t345_0 := by have : 0 < 1 - (θ 0 + θ 1 + θ 2) := h 4; linarith
  t345_2 := by have : 0 < 1 - (θ 3 + θ 4 + θ 5) := h 5; linarith
  hF4 := h 6
  hF5 := h 7
  hDD := h 8
  hDG4 := h 9
  hDG5 := h 10
  hE35 := by
    have : 0 < -((θ 1 - 1 + θ 2) * θ 3 - θ 0 * θ 4 + θ 0 * (1 - θ 5)) := h 11
    linarith
  hE24 := h 12
  hs := h 13
  ht := h 14
  hst := by have : 0 < θ 6 + θ 7 - 1 := h 15; linarith
  d023 := h 16
  d035 := h 17
  d234 := h 18

/-- Every normal form is a shape from its parameters. -/
theorem NF29.eq_nfShape29 {x : Fin 7 → ℝ³} (N : NF29 x) :
    x = nfShape29 N.o N.E₁ N.E₂ N.E₃ ![N.a0, N.b0, N.h0, N.a2, N.b2, N.h2, N.s, N.t] := by
  funext i
  fin_cases i
  · exact N.x0
  · exact N.x1
  · exact N.x2
  · exact N.x3
  · exact N.x4
  · exact N.x5
  · exact N.x6

theorem NF29.ineq {x : Fin 7 → ℝ³} (N : NF29 x) :
    ∀ k, 0 < ineq29 ![N.a0, N.b0, N.h0, N.a2, N.b2, N.h2, N.s, N.t] k := by
  intro k
  fin_cases k
  · exact N.hh0
  · exact N.hh2
  · show 0 < -N.a0; linarith [N.ha0]
  · show 0 < -N.b2; linarith [N.hb2]
  · show 0 < 1 - (N.a0 + N.b0 + N.h0); linarith [N.t345_0]
  · show 0 < 1 - (N.a2 + N.b2 + N.h2); linarith [N.t345_2]
  · exact N.hF4
  · exact N.hF5
  · exact N.hDD
  · exact N.hDG4
  · exact N.hDG5
  · show 0 < -((N.b0 - 1 + N.h0) * N.a2 - N.a0 * N.b2 + N.a0 * (1 - N.h2)); linarith [N.hE35]
  · exact N.hE24
  · exact N.hs
  · exact N.ht
  · show 0 < N.s + N.t - 1; linarith [N.hst]
  · exact N.d023
  · exact N.d035
  · exact N.d234

theorem continuous_ineq29 (k : Fin 19) : Continuous fun θ : Fin 8 → ℝ => ineq29 θ k := by
  fin_cases k <;> simp only [ineq29] <;> fun_prop

theorem continuous_vpoly29 : Continuous vpoly29 := by
  unfold vpoly29; fun_prop

theorem tendsto_nfShape29 {ι : Type*} {l : Filter ι} {o E₁ E₂ E₃ : ι → ℝ³} {o₀ F₁ F₂ F₃ : ℝ³}
    {θ : ι → Fin 8 → ℝ} {θ₀ : Fin 8 → ℝ} (ho : Tendsto o l (𝓝 o₀))
    (h₁ : Tendsto E₁ l (𝓝 F₁)) (h₂ : Tendsto E₂ l (𝓝 F₂)) (h₃ : Tendsto E₃ l (𝓝 F₃))
    (hθ : Tendsto θ l (𝓝 θ₀)) (i : Fin 7) :
    Tendsto (fun t => nfShape29 (o t) (E₁ t) (E₂ t) (E₃ t) (θ t) i) l
      (𝓝 (nfShape29 o₀ F₁ F₂ F₃ θ₀ i)) := by
  have c : ∀ j, Tendsto (fun t => θ t j) l (𝓝 (θ₀ j)) := fun j =>
    ((continuous_apply j).tendsto θ₀).comp hθ
  have k : ∀ c : ℝ, Tendsto (fun _ : ι => c) l (𝓝 c) := fun c => tendsto_const_nhds
  fin_cases i
  · exact tendsto_nfP ho h₁ h₂ h₃ (c 0) (c 1) (c 2).neg
  · exact tendsto_nfP ho h₁ h₂ h₃ (k 0) (k 0) (k 0)
  · exact tendsto_nfP ho h₁ h₂ h₃ (c 3) (c 4) (c 5).neg
  · exact tendsto_nfP ho h₁ h₂ h₃ (k 0) (k 0) (k (-1))
  · exact tendsto_nfP ho h₁ h₂ h₃ (k 1) (k 0) (k 0)
  · exact tendsto_nfP ho h₁ h₂ h₃ (k 0) (k 1) (k 0)
  · exact tendsto_nfP ho h₁ h₂ h₃ (c 6) (c 7) (k 0)

/-! ### The polynomial genericity of the covers as one polynomial -/

/-- The polynomial fields of `K3Poly`, `K4Poly`, `K3C1Poly`, `K4C1Poly` as one product (over any
commutative ring): `h0 − 1, G4, G5, F, th, f, t − 1, h2 − 1, κ, F5h0, F4h2, σ, c0, Xf, hs, L36`
(class K3a), `b0 + h0 − 1, a2 + h2 − 1, a0 + h0, c2` (class K4a) and `s − 1` (C1 tiers). -/
def genFactors29 {R : Type*} [CommRing R] (a0 b0 h0 a2 b2 h2 s t : R) : R :=
  (h0 - 1) * (b0 * (1 - h2) - b2 * (1 - h0)) * (a2 * (1 - h0) - a0 * (1 - h2)) *
    ((h2 * b0 - h0 * b2) - (h0 * a2 - h2 * a0)) * (-a2 * t + b2 * s) *
    (-a0 * h2 * t + a2 * h0 * t + b0 * h2 * s - b2 * h0 * s - b0 * h2 + b2 * h0) * (t - 1) *
    (h2 - 1) * (-a2 - h2 + 1) * ((h0 * a2 - h2 * a0) - h0) * ((h2 * b0 - h0 * b2) - h2) *
    (a2 * t - b2 * s + h2 * t - a2 - h2 - t + 1) *
    (a0 * b2 - a2 * b0 - a2 * h0 - b0 * h2 - h0 * h2 + a2 + b0 + h0 + h2 - 1) *
    (-a0 * t + b0 * s - h0 * t - b0 - s + 1) * (h0 * s + a0) *
    (-a0 * h2 * t + b2 * h0 * s + h0 * h2 * s + a0 * h2) * (b0 + h0 - 1) * (a2 + h2 - 1) *
    (a0 + h0) *
    (-((b0 - 1 + h0) * a2 - a0 * b2 + a0 * (1 - h2)) - (1 - a0 - b0 - h0)) * (s - 1)

open MvPolynomial in
/-- **The special positions of the covers** as one polynomial in the eight parameters
`(a0, b0, h0, a2, b2, h2, s, t)`. -/
noncomputable def genPoly29 : MvPolynomial (Fin 8) ℝ :=
  genFactors29 (X 0) (X 1) (X 2) (X 3) (X 4) (X 5) (X 6) (X 7)

theorem eval_genPoly29 (θ : Fin 8 → ℝ) :
    MvPolynomial.eval θ genPoly29 =
      genFactors29 (θ 0) (θ 1) (θ 2) (θ 3) (θ 4) (θ 5) (θ 6) (θ 7) := by
  simp [genPoly29, genFactors29]

/-- **The special positions form a proper algebraic set** (`genPoly29 ≠ 0`): the integer point
`(−3, 2, 5, 7, −11, 13, 17, 19)` is off all 21 factors. -/
theorem genPoly29_ne_zero : genPoly29 ≠ 0 := by
  intro h
  have := congrArg (MvPolynomial.eval ![-3, 2, 5, 7, -11, 13, 17, 19]) h
  rw [eval_genPoly29, map_zero] at this
  simp [genFactors29] at this
  norm_num at this

section ofGen

variable {x : Fin 7 → ℝ³} (N : NF29 x)

theorem NF29.k3Poly_of_gen (h : genFactors29 N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t ≠ 0) :
    K3Poly N := by
  simp only [genFactors29, mul_ne_zero_iff, and_assoc] at h
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, -⟩ := h
  exact ⟨sub_ne_zero.mp f1, f2, f3, sub_ne_zero.mp f4, f5, f6, sub_ne_zero.mp f7,
    sub_ne_zero.mp f8, f9, sub_ne_zero.mp f10, sub_ne_zero.mp f11, f12, f13, f14, f15, f16⟩

theorem NF29.k4Poly_of_gen (h : genFactors29 N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t ≠ 0) :
    K4Poly N := by
  simp only [genFactors29, mul_ne_zero_iff, and_assoc] at h
  obtain ⟨f1, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, f17, f18, f19, f20, -⟩ := h
  exact ⟨sub_ne_zero.mp f17,
    sub_ne_zero.mp f18, sub_ne_zero.mp f1, f19, sub_ne_zero.mp f20⟩

theorem NF29.k3C1Poly_of_gen (h : genFactors29 N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t ≠ 0) :
    K3C1Poly N := by
  simp only [genFactors29, mul_ne_zero_iff, and_assoc] at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, f21⟩ := h
  exact ⟨sub_ne_zero.mp f21⟩

theorem NF29.k4C1Poly_of_gen (h : genFactors29 N.a0 N.b0 N.h0 N.a2 N.b2 N.h2 N.s N.t ≠ 0) :
    K4C1Poly N := by
  simp only [genFactors29, mul_ne_zero_iff, and_assoc] at h
  obtain ⟨-, -, -, -, -, -, f7, -, -, -, -, -, -, -, -, -, -, -, -, -, f21⟩ := h
  exact ⟨sub_ne_zero.mp f7, sub_ne_zero.mp f21⟩

end ofGen

/-- **The nonvanishing set of a nonzero polynomial is dense**, as a sequence, in any number of
variables (`exists_seq_eval_ne_zero` of type 16 for `Fin 7`; `MvPolynomial.funext_set` on
boxes). -/
theorem exists_seq_eval_ne_zero_fin {m : ℕ} {P : MvPolynomial (Fin m) ℝ} (hP : P ≠ 0)
    (θ : Fin m → ℝ) :
    ∃ θs : ℕ → Fin m → ℝ, Tendsto θs atTop (𝓝 θ) ∧ ∀ n, MvPolynomial.eval (θs n) P ≠ 0 := by
  have box : ∀ n : ℕ, ∃ θ' : Fin m → ℝ, (∀ i, |θ' i - θ i| < 1 / ((n : ℝ) + 1)) ∧
      MvPolynomial.eval θ' P ≠ 0 := by
    intro n
    have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    by_contra hc
    push Not at hc
    apply hP
    refine MvPolynomial.funext_set (R := ℝ) (σ := Fin m) (p := P) (q := 0)
      (fun i => Set.Ioo (θ i - 1 / ((n : ℝ) + 1)) (θ i + 1 / ((n : ℝ) + 1)))
      (fun i => Set.Ioo_infinite (α := ℝ) (by linarith)) fun y hy => ?_
    rw [map_zero]
    refine hc y fun i => ?_
    have := hy i (Set.mem_univ i)
    rw [abs_sub_lt_iff]; constructor <;> linarith [this.1, this.2]
  choose θs hθs hne using box
  refine ⟨θs, tendsto_pi_nhds.mpr fun i => ?_, hne⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M, hM⟩ := exists_nat_one_div_lt hε
  refine ⟨M, fun n hn => ?_⟩
  rw [Real.dist_eq]
  have h1 := hθs n i
  have h2 : 1 / ((n : ℝ) + 1) ≤ 1 / ((M : ℝ) + 1) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hn 1
  linarith

/-! ### Named views in the limit -/

variable {x : Fin 7 → ℝ³}

theorem NF29.vtxView29_5 (N : NF29 x) : vtxView29 x 5 =
    ((1 : ℝ) * N.D) • nfV N.E₁ N.E₂ N.E₃ (N.b2 * N.s - N.b2 - N.h2 * N.t) (N.b2 * N.t)
      (-N.h2 * N.t) := by
  show planeLine (x 1) (x 2) (x 4) (x 3) (x 4) (x 6) = _
  simp only [planeLine, NF29.D]
  nf29_simp N
  ext k
  simp only [nfV, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul,
    det3c]
  ring

theorem NF29.view_X_ne (N : NF29 x) : view29 x (.inr 5) ≠ 0 := by
  show vtxView29 x 5 ≠ 0
  rw [N.vtxView29_5]
  exact smul_ne_zero (mul_ne_zero one_ne_zero N.hD)
    (nfV_ne_zero N.hD (Or.inr (Or.inl (mul_ne_zero N.hb2.ne N.ht.ne'))))

/-- **The named views of a type-29 shape are nonzero** (except the degenerate segments). -/
theorem NF29.view29_ne_zero (N : NF29 x) (v : View29) (hv : ∀ i, v ≠ .inl (i, i)) :
    view29 x v ≠ 0 := by
  rcases v with ⟨i, j⟩ | t
  · exact N.seg_ne (fun h => hv i (by rw [h]))
  · fin_cases t
    · exact N.view_T1_ne
    · exact N.view_T2_ne
    · exact N.view_V_ne
    · exact N.view_T3_ne
    · exact N.view_Y1_ne
    · exact N.view_X_ne
    · exact N.view_Z_ne

theorem restore_nfShape29 (s : ℝ) (e b o E₁ E₂ E₃ : ℝ³) (θ : Fin 8 → ℝ) :
    (fun i => restore s e b (nfShape29 o E₁ E₂ E₃ θ i)) =
      nfShape29 (restore s e b o) (restore s e b E₁) (restore s e b E₂) (restore s e b E₃) θ := by
  funext i; fin_cases i <;> exact restore_nfP s e b o E₁ E₂ E₃ _ _ _

theorem view29_restore {s : ℝ} {e b : ℝ³} (h : ⟪e, b⟫ = 0) (y : Fin 7 → ℝ³) (v : View29) :
    view29 (fun i => restore s e b (y i)) v = restore s e b (view29 y v) := by
  rcases v with ⟨i, j⟩ | t
  · exact (restore_sub s e b _ _).symm
  · exact planeLine_restore h _ _ _ _ _ _

theorem tendsto_view29 {ι : Type*} {l : Filter ι} {K : ι → Fin 7 → ℝ³} {x : Fin 7 → ℝ³}
    (hK : ∀ m, Tendsto (fun n => K n m) l (𝓝 (x m))) (v : View29) :
    Tendsto (fun n => view29 (K n) v) l (𝓝 (view29 x v)) := by
  rcases v with ⟨i, j⟩ | t
  · exact (hK j).sub (hK i)
  · exact tendsto_planeLine (hK _) (hK _) (hK _) (hK _) (hK _) (hK _)

/-- **Type 29 is in convex position**: no point lies inside a segment of two others
(from `hvert`, every vertex is off the hull of the others). -/
theorem noSeg29_of_hvert {x : Fin 7 → ℝ³}
    (hvert : ∀ v ∈ univ.image x, v ∉ convexHull ℝ (((univ.image x).erase v : Finset ℝ³) : Set ℝ³)) :
    ∀ i j m : Fin 7, x m ≠ x i → x m ≠ x j → ∀ s : ℝ, 0 < s → s < 1 →
      x m ≠ x i + s • (x j - x i) := by
  intro i j m hmi hmj s hs0 hs1 he
  refine hvert (x m) (mem_image_of_mem x (mem_univ m)) ?_
  have hi : x i ∈ (((univ.image x).erase (x m) : Finset ℝ³) : Set ℝ³) := by
    simp only [coe_erase, Set.mem_sdiff, mem_coe, mem_image, mem_univ, true_and,
      Set.mem_singleton_iff]
    exact ⟨⟨i, rfl⟩, fun h => hmi h.symm⟩
  have hj : x j ∈ (((univ.image x).erase (x m) : Finset ℝ³) : Set ℝ³) := by
    simp only [coe_erase, Set.mem_sdiff, mem_coe, mem_image, mem_univ, true_and,
      Set.mem_singleton_iff]
    exact ⟨⟨j, rfl⟩, fun h => hmj h.symm⟩
  refine segment_subset_convexHull hi hj ⟨1 - s, s, by linarith, hs0.le, by ring, ?_⟩
  rw [he]; module

/-! ### Ties at the named views -/

/-- A tie at a named view: two labels `s ≠ t` at equal depth along a nonzero named view. -/
def TieInst29 (x : Fin 7 → ℝ³) (v : View29) (s t : Fin 7) : Prop :=
  s ≠ t ∧ view29 x v ≠ 0 ∧ ⟪x s - x t, view29 x v⟫ = 0

/-- Two ties that are one equation for every shape: the same view (up to reversing a segment)
and the same pair, or the tie of `s, t` along `i j` and the tie of `i, j` along `s t`. -/
def SameTie29 (v : View29) (s t : Fin 7) (v' : View29) (s' t' : Fin 7) : Prop :=
  ((v' = v ∨ ∃ i j, v = .inl (i, j) ∧ v' = .inl (j, i)) ∧
      ((s' = s ∧ t' = t) ∨ (s' = t ∧ t' = s))) ∨
    ∃ i j, v = .inl (i, j) ∧ (v' = .inl (s, t) ∨ v' = .inl (t, s)) ∧
      ((s' = i ∧ t' = j) ∨ (s' = j ∧ t' = i))

/-- **At most one tie** at the named views of `x` (§18.6, §28: conservatively over all named
views, not only the rims of one certificate): any two ties are one equation.  Two ties that are
not one equation are two conditions on the shape, so this fails only in codimension 2.  (The
per-view `OneTie29` is the consequence for the tests.) -/
def OneTieGlobal29 (x : Fin 7 → ℝ³) : Prop :=
  ∀ v s t v' s' t', TieInst29 x v s t → TieInst29 x v' s' t' → SameTie29 v s t v' s' t'

/-- One equation holds at every shape where the other does. -/
theorem SameTie29.inner_eq_zero {v : View29} {s t : Fin 7} {v' : View29} {s' t' : Fin 7}
    (h : SameTie29 v s t v' s' t') (y : Fin 7 → ℝ³) (h0 : ⟪y s - y t, view29 y v⟫ = 0) :
    ⟪y s' - y t', view29 y v'⟫ = 0 := by
  rcases h with ⟨hv, hp⟩ | ⟨i, j, rfl, hv', hp⟩
  · have hv'' : view29 y v' = view29 y v ∨ view29 y v' = -view29 y v := by
      rcases hv with rfl | ⟨i, j, rfl, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (by simp only [view29, neg_sub])
    have hp' : y s' - y t' = y s - y t ∨ y s' - y t' = -(y s - y t) := by
      rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (neg_sub _ _).symm
    rcases hv'' with e | e <;> rcases hp' with f | f <;>
      simp only [e, f, inner_neg_left, inner_neg_right, h0, neg_zero]
  · simp only [view29] at h0
    rw [inner_coords] at h0
    rcases hv' with rfl | rfl <;> rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [view29] <;> rw [inner_coords] <;>
      simp only [PiLp.sub_apply] at h0 ⊢ <;>
      first | linear_combination h0 | linear_combination -h0

/-- **At most one tie at a named view** of a shape whose ties are ties of `x`. -/
theorem oneTieAt_of_ties29 {x y : Fin 7 → ℝ³} (htie : OneTieGlobal29 x)
    (hsub : ∀ v a b, a ≠ b → view29 y v ≠ 0 → ⟪y a - y b, view29 y v⟫ = 0 → TieInst29 x v a b)
    (v : View29) (hv : view29 y v ≠ 0) : OneTieAt (univ.image y) (view29 y v) := by
  intro s hs t ht s' hs' t' ht' hst hst' e1 e2
  obtain ⟨a, -, rfl⟩ := mem_image.mp hs
  obtain ⟨b, -, rfl⟩ := mem_image.mp ht
  obtain ⟨a', -, rfl⟩ := mem_image.mp hs'
  obtain ⟨b', -, rfl⟩ := mem_image.mp ht'
  have hab : a ≠ b := fun h => hst (by rw [h])
  have hab' : a' ≠ b' := fun h => hst' (by rw [h])
  have t1 := hsub v a b hab hv (by rw [inner_sub_left, e1, sub_self])
  have t2 := hsub v a' b' hab' hv (by rw [inner_sub_left, e2, sub_self])
  rcases htie v a b v a' b' t1 t2 with ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨i, j, rfl, hv', -⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exfalso
    obtain ⟨-, hne, h0⟩ := t1
    have hij : (i = a ∧ j = b) ∨ (i = b ∧ j = a) := by
      rcases hv' with h | h
      · simp only [Sum.inl.injEq, Prod.mk.injEq] at h; exact Or.inl h
      · simp only [Sum.inl.injEq, Prod.mk.injEq] at h; exact Or.inr h
    have hne' : x j - x i ≠ 0 := hne
    have h0' : ⟪x a - x b, x j - x i⟫ = 0 := h0
    rcases hij with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2] at hne' h0'
      rw [← neg_sub, inner_neg_left, neg_eq_zero] at h0'
      exact hne' (inner_self_eq_zero.mp h0')
    · rw [h1, h2] at hne' h0'
      exact hne' (inner_self_eq_zero.mp h0')

/-- The global tie condition implies the per-view one (`OneTie29`). -/
theorem OneTieGlobal29.oneTie {x : Fin 7 → ℝ³} (h : OneTieGlobal29 x) : OneTie29 x :=
  fun v hv => oneTieAt_of_ties29 h (fun w a b hab hw h0 => ⟨hab, hw, h0⟩) v hv

/-- **Strict comparisons persist**: eventually every tie of `K_n` at a named view is a tie of the
limit `x`. -/
theorem eventually_ties29 {x : Fin 7 → ℝ³} {K : ℕ → Fin 7 → ℝ³}
    (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m))) :
    ∀ᶠ n in atTop, ∀ v a b, ⟪K n a - K n b, view29 (K n) v⟫ = 0 →
      ⟪x a - x b, view29 x v⟫ = 0 := by
  have h : ∀ q : View29 × Fin 7 × Fin 7, ∀ᶠ n in atTop,
      ⟪K n q.2.1 - K n q.2.2, view29 (K n) q.1⟫ = 0 → ⟪x q.2.1 - x q.2.2, view29 x q.1⟫ = 0 := by
    rintro ⟨v, a, b⟩
    by_cases h0 : ⟪x a - x b, view29 x v⟫ = 0
    · exact Eventually.of_forall fun _ _ => h0
    · exact ((((hK a).sub (hK b)).inner (tendsto_view29 hK v)).eventually_ne h0).mono
        fun n hn h => absurd h hn
  filter_upwards [eventually_all.mpr h] with n hn v a b h
  exact hn (v, a, b) h

/-- Two distinct views, one of them a vertex line, are never one equation. -/
theorem not_sameTie29 {v w : View29} (hvw : v ≠ w) (hr : v.isRight = true ∨ w.isRight = true)
    {s t s' t' : Fin 7} : ¬ SameTie29 v s t w s' t' := by
  rintro (⟨h | ⟨i, j, rfl, rfl⟩, -⟩ | ⟨i, j, rfl, hv', -⟩)
  · exact hvw h.symm
  · simp at hr
  · rcases hv' with rfl | rfl <;> simp at hr

/-- The distinct views of each combined pair, one a vertex line. -/
theorem pairViews29_sep : ∀ p ∈ pairViews29,
    p.1 ≠ p.2 ∧ (p.1.isRight = true ∨ p.2.isRight = true) := by
  intro p hp
  simp only [pairViews29, mem_insert, mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- **Ties at no more than one of two views** that are not one equation (`OneTieGlobal29`). -/
theorem noTieAt_or29 {x y : Fin 7 → ℝ³} (htie : OneTieGlobal29 x)
    (hsub : ∀ v a b, a ≠ b → view29 y v ≠ 0 → ⟪y a - y b, view29 y v⟫ = 0 → TieInst29 x v a b)
    {v w : View29} (hvw : v ≠ w) (hr : v.isRight = true ∨ w.isRight = true)
    (hv : view29 y v ≠ 0) (hw : view29 y w ≠ 0) :
    NoTieAt (univ.image y) (view29 y v) ∨ NoTieAt (univ.image y) (view29 y w) := by
  by_contra hc
  simp only [not_or, NoTieAt, not_forall, not_not, exists_prop] at hc
  obtain ⟨⟨s, hs, s', hs', hss, e⟩, ⟨r, hr', r', hr'', hrr, e'⟩⟩ := hc
  obtain ⟨i, -, rfl⟩ := mem_image.mp hs
  obtain ⟨j, -, rfl⟩ := mem_image.mp hs'
  obtain ⟨k, -, rfl⟩ := mem_image.mp hr'
  obtain ⟨l, -, rfl⟩ := mem_image.mp hr''
  have t1 := hsub v i j (fun h' => hss (by rw [h'])) hv (by rw [inner_sub_left, e, sub_self])
  have t2 := hsub w k l (fun h' => hrr (by rw [h'])) hw (by rw [inner_sub_left, e', sub_self])
  exact not_sameTie29 hvw hr (htie _ _ _ _ _ _ t1 t2)

/-- **The ties of `K_n` at the named views satisfy `Tie29`** when they are ties of `x`
(`OneTieGlobal29`): at most one tied pair at each view, and no tie at one view of each combined
pair. -/
theorem tie29_of_ties {x y : Fin 7 → ℝ³} (hy : Function.Injective y) (htie : OneTieGlobal29 x)
    (hsub : ∀ v a b, a ≠ b → view29 y v ≠ 0 → ⟪y a - y b, view29 y v⟫ = 0 → TieInst29 x v a b) :
    Tie29 y where
  one := fun v hv => oneTieAt_of_ties29 htie hsub v hv
  pair := fun p hp h1 h2 =>
    noTieAt_or29 htie hsub (pairViews29_sep p hp).1 (pairViews29_sep p hp).2 h1 h2

/-! ### The limit certificate -/

/-- A labelled certificate at a named view, with 3, 4 or 5 corners. -/
def CertL29 (y : Fin 7 → ℝ³) (v : View29) (ε : Bool) :
    ((ZMod 3 → Fin 7) ⊕ (ZMod 4 → Fin 7) ⊕ (ZMod 5 → Fin 7)) → Prop :=
  Sum.elim (fun lab => RimCertAt y (sgnB ε • view29 y v) lab)
    (Sum.elim (fun lab => RimCertAt y (sgnB ε • view29 y v) lab)
      (fun lab => RimCertAt y (sgnB ε • view29 y v) lab))

/-- **Normalizing a certificate**: labels, a named view and a sign. -/
theorem Cert29.exists_certL {y : Fin 7 → ℝ³} (h : Cert29 y) :
    ∃ v ε L, CertL29 y v ε L := by
  obtain ⟨v, c, hc0, k, hk, z, hz⟩ := h.rimCert
  have hpos : 0 < |c|⁻¹ := inv_pos.mpr (abs_pos.mpr hc0)
  have hz' := hz.smul hpos
  rw [smul_smul] at hz'
  have hsg : |c|⁻¹ * c = sgnB (decide (0 < c)) := by
    rcases lt_or_gt_of_ne hc0 with h | h
    · rw [abs_of_neg h, sgnB, decide_eq_false (not_lt.mpr h.le)]
      field_simp; simp
    · rw [abs_of_pos h, sgnB, decide_eq_true h, inv_mul_cancel₀ h.ne']; simp
  rw [hsg] at hz'
  obtain ⟨lab, -, hat⟩ := hz'.toAt
  refine ⟨v, decide (0 < c), ?_⟩
  rcases hk with rfl | rfl | rfl
  · exact ⟨Sum.inl lab, hat⟩
  · exact ⟨Sum.inr (Sum.inl lab), hat⟩
  · exact ⟨Sum.inr (Sum.inr lab), hat⟩

/-- **Lemma 18.2 for one labelled certificate along a sequence of type-29 shapes.** -/
theorem isRupert_of_certL_seq29 (N : NF29 x)
    (hvert : ∀ v ∈ univ.image x,
      v ∉ convexHull ℝ (((univ.image x).erase v : Finset ℝ³) : Set ℝ³))
    (hnd : ∀ v, view29 x v ≠ 0 → NoHDNAt (univ.image x) (view29 x v))
    (K : ℕ → Fin 7 → ℝ³) (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m)))
    {k : ℕ} [NeZero k] (v : View29) (ε : Bool) (lab : ZMod k → Fin 7)
    (hc : ∃ᶠ n in atTop, RimCertAt (K n) (sgnB ε • view29 (K n) v) lab ∧
      ∀ w a b, TieInst29 x w a b → ⟪K n a - K n b, view29 (K n) w⟫ = 0) :
    IsRupert (univ.image x) := by
  obtain ⟨n₀, hn₀, -⟩ := hc.exists
  have hv : ∀ i, v ≠ .inl (i, i) := by
    rintro i rfl
    apply hn₀.ne_zero
    simp [view29]
  have hv0 := N.view29_ne_zero v hv
  have hs := sgnB_ne_zero ε
  have hdet : det3 (x 4 - x 1) (x 5 - x 1) (x 3 - x 1) ≠ 0 := by
    have : det3 (x 4 - x 1) (x 5 - x 1) (x 3 - x 1) = -N.D := by
      nf29_simp N
      simp only [det3c, NF29.D]
      ring
    rw [this]; exact neg_ne_zero.mpr N.hD
  refine isRupert_of_tendsto_rimCert x (noSeg29_of_hvert hvert) ⟨1, 4, 5, 3, hdet⟩ lab
    (smul_ne_zero hs hv0) ((hnd v hv0).smul_view hs) K (fun n => sgnB ε • view29 (K n) v) hK
    ((tendsto_view29 hK v).const_smul _) (hc.mono fun n hn => ⟨hn.1, fun i j e => ?_⟩)
  by_cases hij : lab i = lab j
  · rw [hij]
  · rw [real_inner_smul_right, real_inner_smul_right] at e
    have e' := mul_left_cancel₀ hs e
    have h := hn.2 v (lab i) (lab j) ⟨hij, hv0, by rw [inner_sub_left, e', sub_self]⟩
    rw [inner_sub_left, sub_eq_zero] at h
    simp only [real_inner_smul_right, h]

/-- **A frequent certificate along a sequence of type-29 shapes** (Lemma 18.2 with the finitely
many labelled certificates): a subsequence carries one labelled certificate. -/
theorem isRupert_of_cert_seq29 (N : NF29 x)
    (hvert : ∀ v ∈ univ.image x,
      v ∉ convexHull ℝ (((univ.image x).erase v : Finset ℝ³) : Set ℝ³))
    (hnd : ∀ v, view29 x v ≠ 0 → NoHDNAt (univ.image x) (view29 x v))
    (K : ℕ → Fin 7 → ℝ³) (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m)))
    (hc : ∃ᶠ n in atTop, Cert29 (K n) ∧
      ∀ w a b, TieInst29 x w a b → ⟪K n a - K n b, view29 (K n) w⟫ = 0) :
    IsRupert (univ.image x) := by
  have h : ∃ᶠ n in atTop, ∃ q : View29 × Bool ×
      ((ZMod 3 → Fin 7) ⊕ (ZMod 4 → Fin 7) ⊕ (ZMod 5 → Fin 7)),
      CertL29 (K n) q.1 q.2.1 q.2.2 ∧
        ∀ w a b, TieInst29 x w a b → ⟪K n a - K n b, view29 (K n) w⟫ = 0 :=
    hc.mono fun n hn => by
      obtain ⟨v, ε, L, hL⟩ := hn.1.exists_certL
      exact ⟨(v, ε, L), hL, hn.2⟩
  obtain ⟨⟨v, ε, L⟩, hq⟩ := frequently_exists_of_finite h
  rcases L with lab | lab | lab
  · exact isRupert_of_certL_seq29 N hvert hnd K hK v ε lab hq
  · exact isRupert_of_certL_seq29 N hvert hnd K hK v ε lab hq
  · exact isRupert_of_certL_seq29 N hvert hnd K hK v ε lab hq

/-- **The approximating sequence with its parameters** (§18.2, §28): a type-29 shape `x` of class
K3a or K4a (`hcls`) with at most one tie at its named views is a limit of shapes `K_n`, each with a
certificate (`Cert29`) and with the tie of `x` (restored by a unimodular shear).  No polynomial
genericity, no `Nodup`, no (G1): the `K_n` are off the special positions of the cover
(`genPoly29`).  Moreover `K_n` has the normal form with parameters `θs n → θ(x)`, which carries the
closed region facts of the certificates (`Ex29.facts`) to the limit. -/
theorem exists_certSeq29_params (N : NF29 x) (htie : OneTieGlobal29 x)
    (hcls : (N.a2 < 0 ∧ 0 < N.b0 ∧ 0 < N.h0 * (1 - N.a2 - N.b2) - N.h2 * (1 - N.a0 - N.b0)) ∨
      (0 < N.a2 ∧ 0 < N.b0 ∧ N.h0 * (1 - N.a2 - N.b2) - N.h2 * (1 - N.a0 - N.b0) < 0)) :
    ∃ (K : ℕ → Fin 7 → ℝ³) (θs : ℕ → Fin 8 → ℝ),
      (∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m))) ∧
      Tendsto θs atTop (𝓝 ![N.a0, N.b0, N.h0, N.a2, N.b2, N.h2, N.s, N.t]) ∧
      ∃ᶠ n in atTop, Cert29 (K n) ∧
        (∀ w a b, TieInst29 x w a b → ⟪K n a - K n b, view29 (K n) w⟫ = 0) ∧
        ∃ Nn : NF29 (K n), ![Nn.a0, Nn.b0, Nn.h0, Nn.a2, Nn.b2, Nn.h2, Nn.s, Nn.t] = θs n := by
  classical
  set θ₀ : Fin 8 → ℝ := ![N.a0, N.b0, N.h0, N.a2, N.b2, N.h2, N.s, N.t] with hθ₀
  have hx : x = nfShape29 N.o N.E₁ N.E₂ N.E₃ θ₀ := N.eq_nfShape29
  obtain ⟨θs, hθs, hgen⟩ := exists_seq_eval_ne_zero_fin genPoly29_ne_zero θ₀
  set Y : ℕ → Fin 7 → ℝ³ := fun n => nfShape29 N.o N.E₁ N.E₂ N.E₃ (θs n) with hYdef
  have hY : ∀ m, Tendsto (fun n => Y n m) atTop (𝓝 (x m)) := by
    intro m
    have := tendsto_nfShape29 (o := fun _ : ℕ => N.o) (E₁ := fun _ => N.E₁) (E₂ := fun _ => N.E₂)
      (E₃ := fun _ => N.E₃) tendsto_const_nhds tendsto_const_nhds tendsto_const_nhds
      tendsto_const_nhds hθs m
    rw [hx]; exact this
  -- the shear that restores the tie of `x`, if any
  obtain ⟨ss, es, bs, hss, ⟨e₀, hes⟩, ⟨b₀, hbs⟩, horth, hrest⟩ : ∃ (ss : ℕ → ℝ) (es bs : ℕ → ℝ³),
      Tendsto ss atTop (𝓝 0) ∧ (∃ e₀, Tendsto es atTop (𝓝 e₀)) ∧
      (∃ b₀, Tendsto bs atTop (𝓝 b₀)) ∧ (∀ n, ⟪es n, bs n⟫ = 0) ∧
      ∀ᶠ n in atTop, ∀ w a b, TieInst29 x w a b →
        ⟪restore (ss n) (es n) (bs n) (Y n a) - restore (ss n) (es n) (bs n) (Y n b),
          view29 (fun i => restore (ss n) (es n) (bs n) (Y n i)) w⟫ = 0 := by
    by_cases hT : ∃ w a b, TieInst29 x w a b
    · obtain ⟨w₀, a₀, b₀, hab₀, hw₀, ht₀⟩ := hT
      set A : ℕ → ℝ³ := fun n => view29 (Y n) w₀ with hAdef
      set B : ℕ → ℝ³ := fun n => Y n a₀ - Y n b₀ with hBdef
      have hA : Tendsto A atTop (𝓝 (view29 x w₀)) := tendsto_view29 hY w₀
      have hB : Tendsto B atTop (𝓝 (x a₀ - x b₀)) := (hY a₀).sub (hY b₀)
      have hBB : 0 < ⟪x a₀ - x b₀, x a₀ - x b₀⟫ :=
        real_inner_self_pos.mpr (sub_ne_zero.mpr (N.inj.ne hab₀))
      have hAA : 0 < ⟪view29 x w₀, view29 x w₀⟫ := real_inner_self_pos.mpr hw₀
      have hAB : ⟪view29 x w₀, x a₀ - x b₀⟫ = 0 := by rw [real_inner_comm]; exact ht₀
      set E : ℕ → ℝ³ := fun n => A n - (⟪A n, B n⟫ / ⟪B n, B n⟫) • B n with hEdef
      have hE : Tendsto E atTop (𝓝 (view29 x w₀)) := by
        have h1 : Tendsto (fun n => ⟪A n, B n⟫ / ⟪B n, B n⟫) atTop
            (𝓝 (⟪view29 x w₀, x a₀ - x b₀⟫ / ⟪x a₀ - x b₀, x a₀ - x b₀⟫)) :=
          (hA.inner hB).div (hB.inner hB) hBB.ne'
        rw [hAB, zero_div] at h1
        have h2 := hA.sub (h1.smul hB)
        rw [zero_smul, sub_zero] at h2
        exact h2
      set S : ℕ → ℝ := fun n => -⟪A n, B n⟫ / (⟪A n, E n⟫ * ⟪B n, B n⟫) with hSdef
      have hS : Tendsto S atTop (𝓝 0) := by
        have h1 : Tendsto (fun n => -⟪A n, B n⟫) atTop (𝓝 (-⟪view29 x w₀, x a₀ - x b₀⟫)) :=
          (hA.inner hB).neg
        rw [hAB, neg_zero] at h1
        have h2 : Tendsto (fun n => ⟪A n, E n⟫ * ⟪B n, B n⟫) atTop
            (𝓝 (⟪view29 x w₀, view29 x w₀⟫ * ⟪x a₀ - x b₀, x a₀ - x b₀⟫)) :=
          (hA.inner hE).mul (hB.inner hB)
        have h3 := h1.div h2 (mul_pos hAA hBB).ne'
        rw [zero_div] at h3
        exact h3
      have horth : ∀ n, ⟪E n, B n⟫ = 0 := by
        intro n
        by_cases hb : ⟪B n, B n⟫ = 0
        · rw [inner_self_eq_zero.mp hb, inner_zero_right]
        · simp only [hEdef, inner_sub_left, real_inner_smul_left]
          field_simp; ring
      refine ⟨S, E, B, hS, ⟨_, hE⟩, ⟨_, hB⟩, horth, ?_⟩
      have ev1 : ∀ᶠ n in atTop, ⟪B n, B n⟫ ≠ 0 := (hB.inner hB).eventually_ne hBB.ne'
      have ev2 : ∀ᶠ n in atTop, ⟪A n, E n⟫ ≠ 0 := (hA.inner hE).eventually_ne hAA.ne'
      filter_upwards [ev1, ev2] with n h1 h2 w a b hw
      refine (htie w₀ a₀ b₀ w a b ⟨hab₀, hw₀, ht₀⟩ hw).inner_eq_zero _ ?_
      rw [← restore_sub, view29_restore (horth n)]
      show ⟪restore (S n) (E n) (B n) (B n), restore (S n) (E n) (B n) (A n)⟫ = 0
      simp only [restore, horth n, mul_zero, zero_smul, add_zero, inner_add_right,
        real_inner_smul_right]
      rw [hSdef, real_inner_comm (A n) (E n), real_inner_comm (A n) (B n)]
      field_simp
      ring
    · exact ⟨fun _ => 0, fun _ => 0, fun _ => 0, tendsto_const_nhds, ⟨0, tendsto_const_nhds⟩,
        ⟨0, tendsto_const_nhds⟩, fun _ => inner_zero_left _,
        Eventually.of_forall fun _ w a b hw => absurd ⟨w, a, b, hw⟩ hT⟩
  -- the restored shapes, as normal-form shapes
  set R : ℕ → ℝ³ → ℝ³ := fun n => restore (ss n) (es n) (bs n) with hRdef
  set K : ℕ → Fin 7 → ℝ³ := fun n =>
    nfShape29 (R n N.o) (R n N.E₁) (R n N.E₂) (R n N.E₃) (θs n) with hKdef
  have hKY : ∀ n, K n = fun i => R n (Y n i) := fun n =>
    (restore_nfShape29 (ss n) (es n) (bs n) N.o N.E₁ N.E₂ N.E₃ (θs n)).symm
  have hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m)) := by
    intro m
    simp only [hKY]
    exact tendsto_restore hss hes hbs (hY m)
  have hineq : ∀ᶠ n in atTop, ∀ k, 0 < ineq29 (θs n) k :=
    eventually_all.mpr fun k =>
      (((continuous_ineq29 k).tendsto θ₀).comp hθs).eventually (lt_mem_nhds (N.ineq k))
  have hcl : ∀ᶠ n in atTop, (θs n 3 < 0 ∧ 0 < θs n 1 ∧ 0 < vpoly29 (θs n)) ∨
      (0 < θs n 3 ∧ 0 < θs n 1 ∧ vpoly29 (θs n) < 0) := by
    have c3 : Tendsto (fun n => θs n 3) atTop (𝓝 N.a2) :=
      ((continuous_apply 3).tendsto θ₀).comp hθs
    have c1 : Tendsto (fun n => θs n 1) atTop (𝓝 N.b0) :=
      ((continuous_apply 1).tendsto θ₀).comp hθs
    have cv : Tendsto (fun n => vpoly29 (θs n)) atTop
        (𝓝 (N.h0 * (1 - N.a2 - N.b2) - N.h2 * (1 - N.a0 - N.b0))) :=
      (continuous_vpoly29.tendsto θ₀).comp hθs
    rcases hcls with ⟨h3, h1, hv⟩ | ⟨h3, h1, hv⟩
    · filter_upwards [c3.eventually (gt_mem_nhds h3), c1.eventually (lt_mem_nhds h1),
        cv.eventually (lt_mem_nhds hv)] with n a b c
      exact Or.inl ⟨a, b, c⟩
    · filter_upwards [c3.eventually (lt_mem_nhds h3), c1.eventually (lt_mem_nhds h1),
        cv.eventually (gt_mem_nhds hv)] with n a b c
      exact Or.inr ⟨a, b, c⟩
  refine ⟨K, θs, hK, hθs, Eventually.frequently ?_⟩
  filter_upwards [hineq, hcl, eventually_ties29 hK, hrest] with n hn hc hs hr
  have hD : det3 (R n N.E₁) (R n N.E₂) (R n N.E₃) ≠ 0 := by
    rw [hRdef]; simp only; rw [det3_restore (horth n)]; exact N.hD
  set Nn := NF29.ofParams (R n N.o) (R n N.E₁) (R n N.E₂) (R n N.E₃) (θs n) hD hn with hNn
  refine ⟨?_, fun w a b hw => by rw [hKY n]; exact hr w a b hw, Nn,
    by funext i; fin_cases i <;> rfl⟩
  have hg := hgen n
  rw [eval_genPoly29] at hg
  have hsubK : ∀ w a b, a ≠ b → view29 (K n) w ≠ 0 → ⟪K n a - K n b, view29 (K n) w⟫ = 0 →
      TieInst29 x w a b := by
    intro w a b hab hw h
    refine ⟨hab, N.view29_ne_zero w ?_, hs w a b h⟩
    rintro i rfl
    exact hw (by simp [view29])
  have T29 : Tie29 (K n) := tie29_of_ties Nn.inj htie hsubK
  rcases hc with ⟨h3, h1, hv⟩ | ⟨h3, h1, hv⟩
  · exact Nn.cert29_K3a_all h3 h1 hv (Nn.k3Poly_of_gen hg) (Nn.k3C1Poly_of_gen hg) T29
  · exact Nn.cert29_K4a_all h3 h1 hv (Nn.k4Poly_of_gen hg) (Nn.k4C1Poly_of_gen hg) T29

/-- **The approximating sequence** (§18.2, §28): `exists_certSeq29_params` without the
parameters. -/
theorem exists_certSeq29 (N : NF29 x) (htie : OneTieGlobal29 x)
    (hcls : (N.a2 < 0 ∧ 0 < N.b0 ∧ 0 < N.h0 * (1 - N.a2 - N.b2) - N.h2 * (1 - N.a0 - N.b0)) ∨
      (0 < N.a2 ∧ 0 < N.b0 ∧ N.h0 * (1 - N.a2 - N.b2) - N.h2 * (1 - N.a0 - N.b0) < 0)) :
    ∃ K : ℕ → Fin 7 → ℝ³, (∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m))) ∧
      ∃ᶠ n in atTop, Cert29 (K n) ∧
        ∀ w a b, TieInst29 x w a b → ⟪K n a - K n b, view29 (K n) w⟫ = 0 := by
  obtain ⟨K, θs, hK, -, hc⟩ := exists_certSeq29_params N htie hcls
  exact ⟨K, hK, hc.mono fun n hn => ⟨hn.1, hn.2.1⟩⟩

/-- **Type 29 outside the HDN set and codimension 2** (§18.2, §28, Theorem 21.22 and 21.11 with
Theorem P).  A type-29 shape `x` (normal form `N`, in convex position `hvert`) of class K3a
(`a2 < 0 < b0`, `V > 0`) or K4a (`a2, b0 > 0`, `V < 0`) with at most one tie at its named views
(`OneTieGlobal29`: the 21 segments and the 7 vertex lines) and no horizontal double normal at
them is Rupert.  No polynomial genericity, no `Nodup`, no (G1): `x` is a limit of shapes `K_n`
off the special positions of the cover (`genPoly29`) with the same tie as `x` (restored by a
unimodular shear), each `K_n` has a certificate (`NF29.cert29_K3a_all`, `NF29.cert29_K4a_all`),
a subsequence carries one labelled certificate, and the limit lemma applies.  The classes K3b,
K4b are this theorem for `x ∘ sigma29` (`NF29.sigma`, `image_sigma29`). -/
theorem isRupert_type29_limit (N : NF29 x)
    (hvert : ∀ v ∈ univ.image x,
      v ∉ convexHull ℝ (((univ.image x).erase v : Finset ℝ³) : Set ℝ³))
    (hcls : (N.a2 < 0 ∧ 0 < N.b0 ∧ 0 < N.h0 * (1 - N.a2 - N.b2) - N.h2 * (1 - N.a0 - N.b0)) ∨
      (0 < N.a2 ∧ 0 < N.b0 ∧ N.h0 * (1 - N.a2 - N.b2) - N.h2 * (1 - N.a0 - N.b0) < 0))
    (hnd : ∀ v, view29 x v ≠ 0 → NoHDNAt (univ.image x) (view29 x v))
    (htie : OneTieGlobal29 x) : IsRupert (univ.image x) := by
  obtain ⟨K, hK, hc⟩ := exists_certSeq29 N htie hcls
  exact isRupert_of_cert_seq29 N hvert hnd K hK hc

end Minimality

end
