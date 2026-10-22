module

public import Minimality.Type16Main
public import Mathlib.Algebra.MvPolynomial.Funext

@[expose] public section

/-!
# Type 16 outside the HDN set and codimension 2 (`FEWER-FACES-PROOFS.md` §18.6 step 2, §19.8)

Every type-16 shape `K` is a limit of shapes `K_n` off the affine special positions of the cover
(the sign conditions `Gen`, `R1`, `R2`; all polynomials in the seven normal-form parameters),
with the same ties as `K` at the named views.  The cover (`NF16.cert_nf`) gives each `K_n` a
certificate `Cert16` (a rim certificate at a named view); a subsequence carries one labelled
certificate, and the limit lemma (`isRupert_of_tendsto_rimCert`) makes `K` Rupert unless the
limit view has a horizontal double normal.

* `nfShape`, `ineq16`, `NF16.ofParams`: normal-form shapes from parameters.
* `genPoly16`: the product of the sign conditions of the route (`Gen`, its `σ`-image, `R1`,
  `R2`), a nonzero polynomial (`genPoly16_ne_zero`); `exists_seq_eval_ne_zero`: the shapes off
  its zero set are dense (`MvPolynomial.funext_set` on small boxes).
* `restore`: a unimodular shear `y ↦ y + s ⟪e, y⟫ b` (`e ⊥ b`) that restores one tie.
* `TieInst16`, `SameTie16`, `OneTie16`: ties at the named views; **at most one tie** (counting
  the tie of `s, t` along `ij` and the tie of `i, j` along `st` as one) is the codimension-2
  condition.
* **`isRupert_type16_limit`**: a type-16 shape with at most one tie at its named views and no
  horizontal double normal at them is Rupert.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-! ### Shapes from parameters -/

/-- The normal-form shape with parameters `θ = (a, b, g, d, p, q, r)` in the frame
`o; E₁, E₂, E₃`. -/
noncomputable def nfShape (o E₁ E₂ E₃ : ℝ³) (θ : Fin 7 → ℝ) : Fin 7 → ℝ³ :=
  ![nfP o E₁ E₂ E₃ 1 0 0, nfP o E₁ E₂ E₃ 0 (θ 2) (θ 3), nfP o E₁ E₂ E₃ (θ 0) (θ 1) 0,
    nfP o E₁ E₂ E₃ 0 0 0, nfP o E₁ E₂ E₃ (θ 4) (θ 5) (θ 6), nfP o E₁ E₂ E₃ 0 1 0,
    nfP o E₁ E₂ E₃ 0 0 1]

/-- The type inequalities of §19.0 as seventeen positive quantities. -/
def ineq16 (θ : Fin 7 → ℝ) : Fin 17 → ℝ :=
  ![θ 0, θ 1, θ 2, θ 3, θ 4, θ 5, θ 6, θ 0 + θ 1 - 1, θ 2 + θ 3 - 1, θ 4 + θ 5 + θ 6 - 1,
    θ 1 * (θ 4 + θ 6 - 1) - θ 5 * (θ 0 - 1), θ 2 * (θ 4 + θ 6 - 1) - θ 5 * (θ 3 - 1),
    θ 1 * θ 6 + (θ 0 - 1) * θ 6 * θ 2 - θ 3 * ((θ 0 - 1) * θ 5 - θ 1 * (θ 4 - 1)),
    θ 2 * θ 4 + (θ 3 - 1) * θ 4 * θ 1 - θ 0 * ((θ 3 - 1) * θ 5 - θ 2 * (θ 6 - 1)),
    θ 0 * (θ 5 + θ 6 - 1) - (θ 1 - 1) * θ 4, θ 3 * (θ 4 + θ 5 - 1) - (θ 2 - 1) * θ 6,
    θ 0 * θ 3 * (θ 5 - 1) - θ 3 * θ 4 * (θ 1 - 1) - θ 0 * θ 6 * (θ 2 - 1)]

theorem nfP_coeffs {o E₁ E₂ E₃ : ℝ³} (hD : det3 E₁ E₂ E₃ ≠ 0) {α β γ α' β' γ' : ℝ}
    (h : nfP o E₁ E₂ E₃ α β γ = nfP o E₁ E₂ E₃ α' β' γ') : α = α' ∧ β = β' ∧ γ = γ' := by
  by_contra hne
  have h0 : nfV E₁ E₂ E₃ (α - α') (β - β') (γ - γ') = 0 := by
    rw [← nfP_sub (o := o), h, sub_self]
  refine nfV_ne_zero hD ?_ h0
  by_contra h'
  push Not at h'
  exact hne ⟨by linarith [h'.1], by linarith [h'.2.1], by linarith [h'.2.2]⟩

/-- **A normal form from parameters** satisfying the type inequalities. -/
noncomputable def NF16.ofParams (o E₁ E₂ E₃ : ℝ³) (θ : Fin 7 → ℝ) (hD : det3 E₁ E₂ E₃ ≠ 0)
    (h : ∀ k, 0 < ineq16 θ k) : NF16 (nfShape o E₁ E₂ E₃ θ) where
  o := o
  E₁ := E₁
  E₂ := E₂
  E₃ := E₃
  inj := by
    have h0 : 0 < θ 0 := h 0
    have h1 : 0 < θ 1 := h 1
    have h2 : 0 < θ 2 := h 2
    have h3 : 0 < θ 3 := h 3
    have h4 : 0 < θ 4 := h 4
    have h5 : 0 < θ 5 := h 5
    have h6 : 0 < θ 6 := h 6
    intro i j e
    fin_cases i <;> fin_cases j <;>
      first
      | rfl
      | (exfalso
         obtain ⟨e1, e2, e3⟩ := nfP_coeffs hD e
         linarith)
  a := θ 0
  b := θ 1
  g := θ 2
  d := θ 3
  p := θ 4
  q := θ 5
  r := θ 6
  x0 := rfl
  x1 := rfl
  x2 := rfl
  x3 := rfl
  x4 := rfl
  x5 := rfl
  x6 := rfl
  hD := hD
  ha := h 0
  hb := h 1
  hg := h 2
  hd := h 3
  hp := h 4
  hq := h 5
  hr := h 6
  hab := h 7
  hgd := h 8
  t046_5 := h 9
  t0246 := h 10
  t0146 := h 11
  t024_1 := h 12
  t146_2 := h 13
  t245_6 := h 14
  t145_0 := h 15
  tB125 := h 16

/-- Every normal form is a shape from its parameters. -/
theorem NF16.eq_nfShape {x : Fin 7 → ℝ³} (N : NF16 x) :
    x = nfShape N.o N.E₁ N.E₂ N.E₃ ![N.a, N.b, N.g, N.d, N.p, N.q, N.r] := by
  funext i
  fin_cases i
  · exact N.x0
  · exact N.x1
  · exact N.x2
  · exact N.x3
  · exact N.x4
  · exact N.x5
  · exact N.x6

theorem NF16.ineq {x : Fin 7 → ℝ³} (N : NF16 x) :
    ∀ k, 0 < ineq16 ![N.a, N.b, N.g, N.d, N.p, N.q, N.r] k := by
  intro k
  fin_cases k
  exacts [N.ha, N.hb, N.hg, N.hd, N.hp, N.hq, N.hr, N.hab, N.hgd, N.t046_5, N.t0246, N.t0146,
    N.t024_1, N.t146_2, N.t245_6, N.t145_0, N.tB125]

theorem continuous_ineq16 (k : Fin 17) : Continuous fun θ : Fin 7 → ℝ => ineq16 θ k := by
  fin_cases k <;> simp only [ineq16] <;> fun_prop

theorem tendsto_nfP {ι : Type*} {l : Filter ι} {o E₁ E₂ E₃ : ι → ℝ³} {o₀ F₁ F₂ F₃ : ℝ³}
    {α β γ : ι → ℝ} {α₀ β₀ γ₀ : ℝ} (ho : Tendsto o l (𝓝 o₀)) (h₁ : Tendsto E₁ l (𝓝 F₁))
    (h₂ : Tendsto E₂ l (𝓝 F₂)) (h₃ : Tendsto E₃ l (𝓝 F₃)) (hα : Tendsto α l (𝓝 α₀))
    (hβ : Tendsto β l (𝓝 β₀)) (hγ : Tendsto γ l (𝓝 γ₀)) :
    Tendsto (fun t => nfP (o t) (E₁ t) (E₂ t) (E₃ t) (α t) (β t) (γ t)) l
      (𝓝 (nfP o₀ F₁ F₂ F₃ α₀ β₀ γ₀)) := by
  simp only [nfP]
  exact ((ho.add (hα.smul h₁)).add (hβ.smul h₂)).add (hγ.smul h₃)

theorem tendsto_nfShape {ι : Type*} {l : Filter ι} {o E₁ E₂ E₃ : ι → ℝ³} {o₀ F₁ F₂ F₃ : ℝ³}
    {θ : ι → Fin 7 → ℝ} {θ₀ : Fin 7 → ℝ} (ho : Tendsto o l (𝓝 o₀))
    (h₁ : Tendsto E₁ l (𝓝 F₁)) (h₂ : Tendsto E₂ l (𝓝 F₂)) (h₃ : Tendsto E₃ l (𝓝 F₃))
    (hθ : Tendsto θ l (𝓝 θ₀)) (i : Fin 7) :
    Tendsto (fun t => nfShape (o t) (E₁ t) (E₂ t) (E₃ t) (θ t) i) l
      (𝓝 (nfShape o₀ F₁ F₂ F₃ θ₀ i)) := by
  have c : ∀ j, Tendsto (fun t => θ t j) l (𝓝 (θ₀ j)) := fun j =>
    ((continuous_apply j).tendsto θ₀).comp hθ
  have k : ∀ c : ℝ, Tendsto (fun _ : ι => c) l (𝓝 c) := fun c => tendsto_const_nhds
  fin_cases i
  · exact tendsto_nfP ho h₁ h₂ h₃ (k 1) (k 0) (k 0)
  · exact tendsto_nfP ho h₁ h₂ h₃ (k 0) (c 2) (c 3)
  · exact tendsto_nfP ho h₁ h₂ h₃ (c 0) (c 1) (k 0)
  · exact tendsto_nfP ho h₁ h₂ h₃ (k 0) (k 0) (k 0)
  · exact tendsto_nfP ho h₁ h₂ h₃ (c 4) (c 5) (c 6)
  · exact tendsto_nfP ho h₁ h₂ h₃ (k 0) (k 1) (k 0)
  · exact tendsto_nfP ho h₁ h₂ h₃ (k 0) (k 0) (k 1)

/-! ### The sign conditions of the route as one polynomial -/

/-- The fourteen conditions of `NF16.Gen` as one product (over any commutative ring). -/
def genFactors {R : Type*} [CommRing R] (a b g d p q r : R) : R :=
  (q - g) * (r - d) * (r * g - q * d) * (a - 1) * (b - 1) * (g - 1) * (d - 1) *
    (a * q - b * p) * (q * (a - 1) - b * (p - 1)) * ((g - 1) * (p + r - 1) - d * q) *
    (q * (1 - d) + g * (r - 1)) * (p + r - 1) *
    ((b - 1) * g * p * r + (q * (1 - d) + g * (r - 1)) * (a * (q - 1) - (b - 1) * p)) *
    (d * (q * (a - 1) - b * (p - 1)) - (g - 1) * (a - 1) * r)

/-- `R1 · R2` (§19.0). -/
def rFactors {R : Type*} [CommRing R] (a b g d p q r : R) : R :=
  ((g - 1) * (p + r) - d * (q - 1)) * ((b - 1) * (p + r) - a * (q - 1))

open MvPolynomial in
/-- **The special positions of the cover** as one polynomial in `(a, b, g, d, p, q, r)`:
`Gen`, its `σ`-image and `R1 R2`. -/
noncomputable def genPoly16 : MvPolynomial (Fin 7) ℝ :=
  genFactors (X 0) (X 1) (X 2) (X 3) (X 4) (X 5) (X 6) *
    genFactors (X 3) (X 2) (X 1) (X 0) (X 6) (X 5) (X 4) *
    rFactors (X 0) (X 1) (X 2) (X 3) (X 4) (X 5) (X 6)

theorem eval_genPoly16 (θ : Fin 7 → ℝ) :
    MvPolynomial.eval θ genPoly16 =
      genFactors (θ 0) (θ 1) (θ 2) (θ 3) (θ 4) (θ 5) (θ 6) *
        genFactors (θ 3) (θ 2) (θ 1) (θ 0) (θ 6) (θ 5) (θ 4) *
        rFactors (θ 0) (θ 1) (θ 2) (θ 3) (θ 4) (θ 5) (θ 6) := by
  simp [genPoly16, genFactors, rFactors]

theorem genPoly16_ne_zero : genPoly16 ≠ 0 := by
  intro h
  have := congrArg (MvPolynomial.eval ![2, 3, 5, 7, 11, 13, 17]) h
  rw [eval_genPoly16, map_zero] at this
  simp [genFactors, rFactors] at this
  norm_num at this

theorem NF16.Gen.ofFactors {x : Fin 7 → ℝ³} (N : NF16 x)
    (h : genFactors N.a N.b N.g N.d N.p N.q N.r ≠ 0) : NF16.Gen N := by
  simp only [genFactors, mul_ne_zero_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩ := h
  exact ⟨sub_ne_zero.mp h1, sub_ne_zero.mp h2, sub_ne_zero.mp h3, sub_ne_zero.mp h4,
    sub_ne_zero.mp h5, sub_ne_zero.mp h6, sub_ne_zero.mp h7, sub_ne_zero.mp h8,
    sub_ne_zero.mp h9, sub_ne_zero.mp h10, h11, fun e => h12 (by rw [e, sub_self]), h13,
    h14⟩

/-- **The nonvanishing set of a nonzero polynomial is dense**, as a sequence: every point is a
limit of points where the polynomial does not vanish (`MvPolynomial.funext_set` on boxes). -/
theorem exists_seq_eval_ne_zero {P : MvPolynomial (Fin 7) ℝ} (hP : P ≠ 0) (θ : Fin 7 → ℝ) :
    ∃ θs : ℕ → Fin 7 → ℝ, Tendsto θs atTop (𝓝 θ) ∧ ∀ n, MvPolynomial.eval (θs n) P ≠ 0 := by
  have box : ∀ n : ℕ, ∃ θ' : Fin 7 → ℝ, (∀ i, |θ' i - θ i| < 1 / ((n : ℝ) + 1)) ∧
      MvPolynomial.eval θ' P ≠ 0 := by
    intro n
    have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    by_contra hc
    push Not at hc
    apply hP
    refine MvPolynomial.funext_set (R := ℝ) (σ := Fin 7) (p := P) (q := 0)
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

/-! ### A shear that restores one tie -/

/-- The shear `y ↦ y + s ⟪e, y⟫ b`; with `e ⊥ b` it preserves determinants. -/
noncomputable def restore (s : ℝ) (e b : ℝ³) (y : ℝ³) : ℝ³ := y + (s * ⟪e, y⟫) • b

theorem restore_add (s : ℝ) (e b y z : ℝ³) :
    restore s e b (y + z) = restore s e b y + restore s e b z := by
  simp only [restore, inner_add_right]; module

theorem restore_sub (s : ℝ) (e b y z : ℝ³) :
    restore s e b (y - z) = restore s e b y - restore s e b z := by
  simp only [restore, inner_sub_right]; module

theorem restore_smul (s : ℝ) (e b y : ℝ³) (c : ℝ) :
    restore s e b (c • y) = c • restore s e b y := by
  simp only [restore, real_inner_smul_right]; module

theorem det3_restore {s : ℝ} {e b : ℝ³} (h : ⟪e, b⟫ = 0) (a c d : ℝ³) :
    det3 (restore s e b a) (restore s e b c) (restore s e b d) = det3 a c d := by
  have h' : e 0 * b 0 + e 1 * b 1 + e 2 * b 2 = 0 := by
    simpa [PiLp.inner_apply, Fin.sum_univ_three, mul_comm] using h
  simp only [restore, det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
  linear_combination (s * ((a 1 * c 2 - a 2 * c 1) * d 0 + (a 2 * c 0 - a 0 * c 2) * d 1 +
    (a 0 * c 1 - a 1 * c 0) * d 2)) * h'

theorem planeLine_restore {s : ℝ} {e b : ℝ³} (h : ⟪e, b⟫ = 0) (p₀ p₁ p₂ q₀ q₁ q₂ : ℝ³) :
    planeLine (restore s e b p₀) (restore s e b p₁) (restore s e b p₂) (restore s e b q₀)
      (restore s e b q₁) (restore s e b q₂) = restore s e b (planeLine p₀ p₁ p₂ q₀ q₁ q₂) := by
  simp only [planeLine, ← restore_sub, det3_restore h, ← restore_smul]

theorem view16_restore {s : ℝ} {e b : ℝ³} (h : ⟪e, b⟫ = 0) (y : Fin 7 → ℝ³)
    (v : (Fin 7 × Fin 7) ⊕ Fin 6) :
    view16 (fun i => restore s e b (y i)) v = restore s e b (view16 y v) := by
  rcases v with ⟨i, j⟩ | t
  · exact (restore_sub s e b _ _).symm
  · exact planeLine_restore h _ _ _ _ _ _

theorem restore_nfP (s : ℝ) (e b o E₁ E₂ E₃ : ℝ³) (α β γ : ℝ) :
    restore s e b (nfP o E₁ E₂ E₃ α β γ) =
      nfP (restore s e b o) (restore s e b E₁) (restore s e b E₂) (restore s e b E₃) α β γ := by
  simp only [nfP, restore_add, restore_smul]

theorem restore_nfShape (s : ℝ) (e b o E₁ E₂ E₃ : ℝ³) (θ : Fin 7 → ℝ) :
    (fun i => restore s e b (nfShape o E₁ E₂ E₃ θ i)) =
      nfShape (restore s e b o) (restore s e b E₁) (restore s e b E₂) (restore s e b E₃) θ := by
  funext i; fin_cases i <;> exact restore_nfP s e b o E₁ E₂ E₃ _ _ _

theorem tendsto_restore {ι : Type*} {l : Filter ι} {s : ι → ℝ} {e b y : ι → ℝ³} {e₀ b₀ y₀ : ℝ³}
    (hs : Tendsto s l (𝓝 0)) (he : Tendsto e l (𝓝 e₀)) (hb : Tendsto b l (𝓝 b₀))
    (hy : Tendsto y l (𝓝 y₀)) : Tendsto (fun t => restore (s t) (e t) (b t) (y t)) l (𝓝 y₀) := by
  have := hy.add ((hs.mul (he.inner hy)).smul hb)
  simpa [restore] using this

/-! ### Named views in the limit -/

theorem tendsto_planeLine {ι : Type*} {l : Filter ι} {p₀ p₁ p₂ q₀ q₁ q₂ : ι → ℝ³}
    {a₀ a₁ a₂ b₀ b₁ b₂ : ℝ³} (h₀ : Tendsto p₀ l (𝓝 a₀)) (h₁ : Tendsto p₁ l (𝓝 a₁))
    (h₂ : Tendsto p₂ l (𝓝 a₂)) (k₀ : Tendsto q₀ l (𝓝 b₀)) (k₁ : Tendsto q₁ l (𝓝 b₁))
    (k₂ : Tendsto q₂ l (𝓝 b₂)) :
    Tendsto (fun t => planeLine (p₀ t) (p₁ t) (p₂ t) (q₀ t) (q₁ t) (q₂ t)) l
      (𝓝 (planeLine a₀ a₁ a₂ b₀ b₁ b₂)) := by
  simp only [planeLine]
  exact ((Tendsto.det3' (h₁.sub h₀) (h₂.sub h₀) (k₂.sub k₀)).smul (k₁.sub k₀)).sub
    ((Tendsto.det3' (h₁.sub h₀) (h₂.sub h₀) (k₁.sub k₀)).smul (k₂.sub k₀))

theorem tendsto_view16 {ι : Type*} {l : Filter ι} {K : ι → Fin 7 → ℝ³} {x : Fin 7 → ℝ³}
    (hK : ∀ m, Tendsto (fun n => K n m) l (𝓝 (x m))) (v : (Fin 7 × Fin 7) ⊕ Fin 6) :
    Tendsto (fun n => view16 (K n) v) l (𝓝 (view16 x v)) := by
  rcases v with ⟨i, j⟩ | t
  · exact (hK j).sub (hK i)
  · exact tendsto_planeLine (hK _) (hK _) (hK _) (hK _) (hK _) (hK _)

/-- **The named views of a type-16 shape are nonzero** (except the degenerate segments). -/
theorem Type16.view16_ne_zero {x : Fin 7 → ℝ³} (T : Type16 x) (v : (Fin 7 × Fin 7) ⊕ Fin 6)
    (hv : ∀ i, v ≠ .inl (i, i)) : view16 x v ≠ 0 := by
  have vtx : ∀ {y : Fin 7 → ℝ³} (N : NF16 y), ∀ t : Fin 3, vtxView16 y t.castSucc.castSucc.castSucc ≠ 0 := by
    intro y N t
    have hD : -N.D ≠ 0 := neg_ne_zero.mpr N.hD
    fin_cases t
    · show vtxView16 y 0 ≠ 0
      rw [NF16.vtxView16_vT2, smul_ne_zero_iff]
      refine ⟨hD, ?_⟩
      simp only [NF16.vT2]
      by_cases hf : N.f15 = 0
      · refine nfV_ne_zero N.hD (Or.inr (Or.inr ?_))
        rw [hf]; have := mul_pos N.t0146 N.hd; simp only [NF16.t0146v]; nlinarith
      · exact nfV_ne_zero N.hD (Or.inl (mul_ne_zero (neg_ne_zero.mpr hf) N.hp.ne'))
    · show vtxView16 y 1 ≠ 0
      rw [NF16.vtxView16_vA, smul_ne_zero_iff]
      exact ⟨hD, nfV_ne_zero N.hD (Or.inl (mul_pos N.hg N.hp).ne')⟩
    · show vtxView16 y 2 ≠ 0
      rw [NF16.vtxView16_uA, smul_ne_zero_iff]
      exact ⟨hD, nfV_ne_zero N.hD (Or.inr (Or.inl N.hq.ne'))⟩
  rcases v with ⟨i, j⟩ | t
  · have hij : i ≠ j := fun h => hv i (by rw [h])
    exact sub_ne_zero.mpr (T.inj.ne hij.symm)
  · show vtxView16 x t ≠ 0
    fin_cases t
    · exact vtx T.toNF 0
    · exact vtx T.toNF 1
    · exact vtx T.toNF 2
    · have := vtx T.sigma.toNF 0; rwa [vtxView16_sigma] at this
    · have := vtx T.sigma.toNF 1; rwa [vtxView16_sigma] at this
    · have := vtx T.sigma.toNF 2; rwa [vtxView16_sigma] at this


/-! ### Ties at the named views -/

/-- A tie at a named view: two labels `s ≠ t` at equal depth along a nonzero named view. -/
def TieInst16 (x : Fin 7 → ℝ³) (v : (Fin 7 × Fin 7) ⊕ Fin 6) (s t : Fin 7) : Prop :=
  s ≠ t ∧ view16 x v ≠ 0 ∧ ⟪x s - x t, view16 x v⟫ = 0

/-- Two ties that are one equation for every shape: the same view (up to reversing a segment)
and the same pair, or the tie of `s, t` along `i j` and the tie of `i, j` along `s t`. -/
def SameTie16 (v : (Fin 7 × Fin 7) ⊕ Fin 6) (s t : Fin 7) (v' : (Fin 7 × Fin 7) ⊕ Fin 6)
    (s' t' : Fin 7) : Prop :=
  ((v' = v ∨ ∃ i j, v = .inl (i, j) ∧ v' = .inl (j, i)) ∧
      ((s' = s ∧ t' = t) ∨ (s' = t ∧ t' = s))) ∨
    ∃ i j, v = .inl (i, j) ∧ (v' = .inl (s, t) ∨ v' = .inl (t, s)) ∧
      ((s' = i ∧ t' = j) ∨ (s' = j ∧ t' = i))

/-- **At most one tie** at the named views of `x` (19.8 (i), conservatively: over all named
views, not only the rims of one certificate): any two ties are one equation.  Two ties that are
not one equation are two conditions on the shape, so this fails only in codimension 2. -/
def OneTie16 (x : Fin 7 → ℝ³) : Prop :=
  ∀ v s t v' s' t', TieInst16 x v s t → TieInst16 x v' s' t' → SameTie16 v s t v' s' t'

theorem inner_coords (a b : ℝ³) : ⟪a, b⟫ = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, mul_comm]

/-- One equation holds at every shape where the other does. -/
theorem SameTie16.inner_eq_zero {v : (Fin 7 × Fin 7) ⊕ Fin 6} {s t : Fin 7}
    {v' : (Fin 7 × Fin 7) ⊕ Fin 6} {s' t' : Fin 7} (h : SameTie16 v s t v' s' t')
    (y : Fin 7 → ℝ³) (h0 : ⟪y s - y t, view16 y v⟫ = 0) : ⟪y s' - y t', view16 y v'⟫ = 0 := by
  rcases h with ⟨hv, hp⟩ | ⟨i, j, rfl, hv', hp⟩
  · have hv'' : view16 y v' = view16 y v ∨ view16 y v' = -view16 y v := by
      rcases hv with rfl | ⟨i, j, rfl, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (by simp only [view16, neg_sub])
    have hp' : y s' - y t' = y s - y t ∨ y s' - y t' = -(y s - y t) := by
      rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (neg_sub _ _).symm
    rcases hv'' with e | e <;> rcases hp' with f | f <;>
      simp only [e, f, inner_neg_left, inner_neg_right, h0, neg_zero]
  · simp only [view16] at h0
    rw [inner_coords] at h0
    rcases hv' with rfl | rfl <;> rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [view16] <;> rw [inner_coords] <;>
      simp only [PiLp.sub_apply] at h0 ⊢ <;>
      first | linear_combination h0 | linear_combination -h0

theorem OneTieAt.smul {V : Finset ℝ³} {u : ℝ³} (h : OneTieAt V u) {c : ℝ} (hc : c ≠ 0) :
    OneTieAt V (c • u) := by
  intro s hs t ht s' hs' t' ht' hst hst' e1 e2
  simp only [real_inner_smul_right] at e1 e2
  exact h s hs t ht s' hs' t' ht' hst hst' (mul_left_cancel₀ hc e1) (mul_left_cancel₀ hc e2)

/-- **At most one tie at a named view** of a shape whose ties are ties of `x`. -/
theorem oneTieAt_of_ties {x y : Fin 7 → ℝ³} (htie : OneTie16 x)
    (hsub : ∀ v a b, a ≠ b → view16 y v ≠ 0 → ⟪y a - y b, view16 y v⟫ = 0 → TieInst16 x v a b)
    (v : (Fin 7 × Fin 7) ⊕ Fin 6) (hv : view16 y v ≠ 0) :
    OneTieAt (univ.image y) (view16 y v) := by
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

/-- **Strict comparisons persist**: eventually every tie of `K_n` at a named view is a tie of the
limit `x`. -/
theorem eventually_ties {x : Fin 7 → ℝ³} {K : ℕ → Fin 7 → ℝ³}
    (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m))) :
    ∀ᶠ n in atTop, ∀ v a b, ⟪K n a - K n b, view16 (K n) v⟫ = 0 →
      ⟪x a - x b, view16 x v⟫ = 0 := by
  have h : ∀ q : ((Fin 7 × Fin 7) ⊕ Fin 6) × Fin 7 × Fin 7, ∀ᶠ n in atTop,
      ⟪K n q.2.1 - K n q.2.2, view16 (K n) q.1⟫ = 0 → ⟪x q.2.1 - x q.2.2, view16 x q.1⟫ = 0 := by
    rintro ⟨v, a, b⟩
    by_cases h0 : ⟪x a - x b, view16 x v⟫ = 0
    · exact Eventually.of_forall fun _ _ => h0
    · exact ((((hK a).sub (hK b)).inner (tendsto_view16 hK v)).eventually_ne h0).mono
        fun n hn h => absurd h hn
  filter_upwards [eventually_all.mpr h] with n hn v a b h
  exact hn (v, a, b) h

/-! ### The limit certificate -/

/-- The orientation sign of a normalized view. -/
def sgnB (b : Bool) : ℝ := if b then 1 else -1

theorem sgnB_ne_zero (b : Bool) : sgnB b ≠ 0 := by cases b <;> norm_num [sgnB]

/-- A labelled certificate at a named view, with 3, 4 or 5 corners. -/
def CertL16 (y : Fin 7 → ℝ³) (v : (Fin 7 × Fin 7) ⊕ Fin 6) (ε : Bool) :
    ((ZMod 3 → Fin 7) ⊕ (ZMod 4 → Fin 7) ⊕ (ZMod 5 → Fin 7)) → Prop :=
  Sum.elim (fun lab => RimCertAt y (sgnB ε • view16 y v) lab)
    (Sum.elim (fun lab => RimCertAt y (sgnB ε • view16 y v) lab)
      (fun lab => RimCertAt y (sgnB ε • view16 y v) lab))

/-- **Normalizing a certificate**: labels, a named view and a sign. -/
theorem Cert16.exists_certL {y : Fin 7 → ℝ³} (h : Cert16 y) :
    ∃ v ε L, CertL16 y v ε L := by
  obtain ⟨u, ⟨v, c, hc0, rfl⟩, k, hk, z, hz⟩ := h
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

/-- **Lemma 18.2 for one labelled certificate along a sequence of type-16 shapes.** -/
theorem isRupert_of_certL_seq {x : Fin 7 → ℝ³} (T : Type16 x)
    (hnd : ∀ v, view16 x v ≠ 0 → NoHDNAt (univ.image x) (view16 x v))
    (K : ℕ → Fin 7 → ℝ³) (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m)))
    {k : ℕ} [NeZero k] (v : (Fin 7 × Fin 7) ⊕ Fin 6) (ε : Bool) (lab : ZMod k → Fin 7)
    (hc : ∃ᶠ n in atTop, RimCertAt (K n) (sgnB ε • view16 (K n) v) lab ∧
      ∀ w a b, TieInst16 x w a b → ⟪K n a - K n b, view16 (K n) w⟫ = 0) :
    IsRupert (univ.image x) := by
  obtain ⟨n₀, hn₀, -⟩ := hc.exists
  have hv : ∀ i, v ≠ .inl (i, i) := by
    rintro i rfl
    apply hn₀.ne_zero
    simp [view16]
  have hv0 := T.view16_ne_zero v hv
  have hs := sgnB_ne_zero ε
  refine isRupert_of_tendsto_rimCert x T.noSeg ⟨3, 0, 5, 6, T.det_ne⟩ lab (smul_ne_zero hs hv0)
    ((hnd v hv0).smul_view hs) K (fun n => sgnB ε • view16 (K n) v) hK
    ((tendsto_view16 hK v).const_smul _) (hc.mono fun n hn => ⟨hn.1, fun i j e => ?_⟩)
  by_cases hij : lab i = lab j
  · rw [hij]
  · rw [real_inner_smul_right, real_inner_smul_right] at e
    have e' := mul_left_cancel₀ hs e
    have h := hn.2 v (lab i) (lab j) ⟨hij, hv0, by rw [inner_sub_left, e', sub_self]⟩
    rw [inner_sub_left, sub_eq_zero] at h
    simp only [real_inner_smul_right, h]

/-- **A frequent certificate along a sequence of type-16 shapes** (Lemma 18.2 with the finitely
many labelled certificates): a subsequence carries one labelled certificate. -/
theorem isRupert_of_cert_seq {x : Fin 7 → ℝ³} (T : Type16 x)
    (hnd : ∀ v, view16 x v ≠ 0 → NoHDNAt (univ.image x) (view16 x v))
    (K : ℕ → Fin 7 → ℝ³) (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m)))
    (hc : ∃ᶠ n in atTop, Cert16 (K n) ∧
      ∀ w a b, TieInst16 x w a b → ⟪K n a - K n b, view16 (K n) w⟫ = 0) :
    IsRupert (univ.image x) := by
  have h : ∃ᶠ n in atTop, ∃ q : ((Fin 7 × Fin 7) ⊕ Fin 6) × Bool ×
      ((ZMod 3 → Fin 7) ⊕ (ZMod 4 → Fin 7) ⊕ (ZMod 5 → Fin 7)),
      CertL16 (K n) q.1 q.2.1 q.2.2 ∧
        ∀ w a b, TieInst16 x w a b → ⟪K n a - K n b, view16 (K n) w⟫ = 0 :=
    hc.mono fun n hn => by
      obtain ⟨v, ε, L, hL⟩ := hn.1.exists_certL
      exact ⟨(v, ε, L), hL, hn.2⟩
  obtain ⟨⟨v, ε, L⟩, hq⟩ := frequently_exists_of_finite h
  rcases L with lab | lab | lab
  · exact isRupert_of_certL_seq T hnd K hK v ε lab hq
  · exact isRupert_of_certL_seq T hnd K hK v ε lab hq
  · exact isRupert_of_certL_seq T hnd K hK v ε lab hq

/-- **The approximating sequence of Theorem 19.8**: a type-16 shape `x` with at most one tie at
its named views is a limit of shapes `K_n`, each with a certificate (`Cert16`) and with the tie
of `x` (restored by a unimodular shear).  No (G1), no sign condition of the route, no general
position: the `K_n` are off the special positions of the cover (`genPoly16`). -/
theorem exists_certSeq16 {x : Fin 7 → ℝ³} (T : Type16 x) (htie : OneTie16 x) :
    ∃ K : ℕ → Fin 7 → ℝ³, (∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m))) ∧
      ∃ᶠ n in atTop, Cert16 (K n) ∧
        ∀ w a b, TieInst16 x w a b → ⟪K n a - K n b, view16 (K n) w⟫ = 0 := by
  classical
  set N := T.toNF with hNdef
  set θ₀ : Fin 7 → ℝ := ![N.a, N.b, N.g, N.d, N.p, N.q, N.r] with hθ₀
  have hx : x = nfShape N.o N.E₁ N.E₂ N.E₃ θ₀ := N.eq_nfShape
  obtain ⟨θs, hθs, hgen⟩ := exists_seq_eval_ne_zero genPoly16_ne_zero θ₀
  set Y : ℕ → Fin 7 → ℝ³ := fun n => nfShape N.o N.E₁ N.E₂ N.E₃ (θs n) with hYdef
  have hY : ∀ m, Tendsto (fun n => Y n m) atTop (𝓝 (x m)) := by
    intro m
    have := tendsto_nfShape (o := fun _ : ℕ => N.o) (E₁ := fun _ => N.E₁) (E₂ := fun _ => N.E₂)
      (E₃ := fun _ => N.E₃) tendsto_const_nhds tendsto_const_nhds tendsto_const_nhds
      tendsto_const_nhds hθs m
    rw [hx]; exact this
  -- the shear that restores the tie of `x`, if any
  obtain ⟨ss, es, bs, hss, ⟨e₀, hes⟩, ⟨b₀, hbs⟩, horth, hrest⟩ : ∃ (ss : ℕ → ℝ) (es bs : ℕ → ℝ³),
      Tendsto ss atTop (𝓝 0) ∧ (∃ e₀, Tendsto es atTop (𝓝 e₀)) ∧
      (∃ b₀, Tendsto bs atTop (𝓝 b₀)) ∧ (∀ n, ⟪es n, bs n⟫ = 0) ∧
      ∀ᶠ n in atTop, ∀ w a b, TieInst16 x w a b →
        ⟪restore (ss n) (es n) (bs n) (Y n a) - restore (ss n) (es n) (bs n) (Y n b),
          view16 (fun i => restore (ss n) (es n) (bs n) (Y n i)) w⟫ = 0 := by
    by_cases hT : ∃ w a b, TieInst16 x w a b
    · obtain ⟨w₀, a₀, b₀, hab₀, hw₀, ht₀⟩ := hT
      set A : ℕ → ℝ³ := fun n => view16 (Y n) w₀ with hAdef
      set B : ℕ → ℝ³ := fun n => Y n a₀ - Y n b₀ with hBdef
      have hA : Tendsto A atTop (𝓝 (view16 x w₀)) := tendsto_view16 hY w₀
      have hB : Tendsto B atTop (𝓝 (x a₀ - x b₀)) := (hY a₀).sub (hY b₀)
      have hBB : 0 < ⟪x a₀ - x b₀, x a₀ - x b₀⟫ :=
        real_inner_self_pos.mpr (sub_ne_zero.mpr (T.inj.ne hab₀))
      have hAA : 0 < ⟪view16 x w₀, view16 x w₀⟫ := real_inner_self_pos.mpr hw₀
      have hAB : ⟪view16 x w₀, x a₀ - x b₀⟫ = 0 := by rw [real_inner_comm]; exact ht₀
      set E : ℕ → ℝ³ := fun n => A n - (⟪A n, B n⟫ / ⟪B n, B n⟫) • B n with hEdef
      have hE : Tendsto E atTop (𝓝 (view16 x w₀)) := by
        have h1 : Tendsto (fun n => ⟪A n, B n⟫ / ⟪B n, B n⟫) atTop
            (𝓝 (⟪view16 x w₀, x a₀ - x b₀⟫ / ⟪x a₀ - x b₀, x a₀ - x b₀⟫)) :=
          (hA.inner hB).div (hB.inner hB) hBB.ne'
        rw [hAB, zero_div] at h1
        have h2 := hA.sub (h1.smul hB)
        rw [zero_smul, sub_zero] at h2
        exact h2
      set S : ℕ → ℝ := fun n => -⟪A n, B n⟫ / (⟪A n, E n⟫ * ⟪B n, B n⟫) with hSdef
      have hS : Tendsto S atTop (𝓝 0) := by
        have h1 : Tendsto (fun n => -⟪A n, B n⟫) atTop (𝓝 (-⟪view16 x w₀, x a₀ - x b₀⟫)) :=
          (hA.inner hB).neg
        rw [hAB, neg_zero] at h1
        have h2 : Tendsto (fun n => ⟪A n, E n⟫ * ⟪B n, B n⟫) atTop
            (𝓝 (⟪view16 x w₀, view16 x w₀⟫ * ⟪x a₀ - x b₀, x a₀ - x b₀⟫)) :=
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
      rw [← restore_sub, view16_restore (horth n)]
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
    nfShape (R n N.o) (R n N.E₁) (R n N.E₂) (R n N.E₃) (θs n) with hKdef
  have hKY : ∀ n, K n = fun i => R n (Y n i) := fun n =>
    (restore_nfShape (ss n) (es n) (bs n) N.o N.E₁ N.E₂ N.E₃ (θs n)).symm
  have hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m)) := by
    intro m
    simp only [hKY]
    exact tendsto_restore hss hes hbs (hY m)
  have hineq : ∀ᶠ n in atTop, ∀ k, 0 < ineq16 (θs n) k :=
    eventually_all.mpr fun k =>
      (((continuous_ineq16 k).tendsto θ₀).comp hθs).eventually (lt_mem_nhds (N.ineq k))
  refine ⟨K, hK, Eventually.frequently ?_⟩
  filter_upwards [hineq, eventually_ties hK, hrest] with n hn hs hr
  refine ⟨?_, fun w a b hw => by rw [hKY n]; exact hr w a b hw⟩
  have hD : det3 (R n N.E₁) (R n N.E₂) (R n N.E₃) ≠ 0 := by
    rw [hRdef]; simp only; rw [det3_restore (horth n)]; exact N.hD
  set Nn := NF16.ofParams (R n N.o) (R n N.E₁) (R n N.E₂) (R n N.E₃) (θs n) hD hn with hNn
  have hg := hgen n
  rw [eval_genPoly16, mul_ne_zero_iff, mul_ne_zero_iff] at hg
  obtain ⟨⟨g1, g2⟩, g3⟩ := hg
  have G : NF16.Gen Nn := NF16.Gen.ofFactors Nn g1
  have Gσ : NF16.Gen Nn.sigma := NF16.Gen.ofFactors Nn.sigma g2
  have hR : Nn.R1 ≠ 0 ∧ Nn.R2 ≠ 0 := by
    simp only [rFactors, mul_ne_zero_iff] at g3; exact g3
  have hsubK : ∀ w a b, a ≠ b → view16 (K n) w ≠ 0 → ⟪K n a - K n b, view16 (K n) w⟫ = 0 →
      TieInst16 x w a b := by
    intro w a b hab hw h
    refine ⟨hab, T.view16_ne_zero w ?_, hs w a b h⟩
    rintro i rfl
    exact hw (by simp [view16])
  have hgt : TieSeg (univ.image (K n)) := by
    refine ⟨fun v hv w hw hvw => ?_⟩
    obtain ⟨i, -, rfl⟩ := mem_image.mp hv
    obtain ⟨j, -, rfl⟩ := mem_image.mp hw
    exact oneTieAt_of_ties htie hsubK (.inl (i, j)) (sub_ne_zero.mpr (Ne.symm hvw))
  have W : NF16.Views Nn := by
    refine ⟨fun hne => ?_⟩
    have e := NF16.vtxView16_vA Nn
    have hD' : -Nn.D ≠ 0 := neg_ne_zero.mpr Nn.hD
    have hv1 : view16 (K n) (.inr 1) ≠ 0 := by
      show vtxView16 _ 1 ≠ 0
      rw [e]; exact smul_ne_zero hD' hne
    have e2 : Nn.vA = (-Nn.D)⁻¹ • view16 (K n) (.inr 1) := by
      show _ = _ • vtxView16 _ 1
      rw [e, smul_smul, inv_mul_cancel₀ hD', one_smul]
    rw [e2]
    exact (oneTieAt_of_ties htie hsubK (.inr 1) hv1).smul (inv_ne_zero hD')
  have Wσ : NF16.Views Nn.sigma := by
    refine ⟨fun hne => ?_⟩
    have e := NF16.vtxView16_vA Nn.sigma
    rw [vtxView16_sigma] at e
    have hD' : -Nn.sigma.D ≠ 0 := neg_ne_zero.mpr Nn.sigma.hD
    have hv4 : view16 (K n) (.inr 4) ≠ 0 := by
      show vtxView16 _ 4 ≠ 0
      rw [show (4 : Fin 6) = 1 + 3 from rfl, e]; exact smul_ne_zero hD' hne
    have e2 : Nn.sigma.vA = (-Nn.sigma.D)⁻¹ • view16 (K n) (.inr 4) := by
      show _ = _ • vtxView16 _ 4
      rw [show (4 : Fin 6) = 1 + 3 from rfl, e, smul_smul, inv_mul_cancel₀ hD', one_smul]
    rw [e2, image_sigma16]
    exact (oneTieAt_of_ties htie hsubK (.inr 4) hv4).smul (inv_ne_zero hD')
  exact NF16.cert_nf Nn G Gσ W Wσ hR.1 hR.2 hgt



/-- **Theorem 19.8 (type 16 outside the HDN set and codimension 2).**  A type-16 shape `x`
(facets `T`) with at most one tie at its named views (`OneTie16`: the segments and the six vertex
crossings of the cover) and no horizontal double normal at them is Rupert.  No (G1), no sign
condition of the route, no general position: `x` is a limit of shapes `K_n` off the special
positions of the cover (`genPoly16`) with the same tie as `x` (restored by a unimodular shear),
each `K_n` has a certificate (`NF16.cert_nf`), a subsequence carries one labelled certificate,
and the limit lemma applies. -/
theorem isRupert_type16_limit {x : Fin 7 → ℝ³} (T : Type16 x)
    (hnd : ∀ v, view16 x v ≠ 0 → NoHDNAt (univ.image x) (view16 x v))
    (htie : OneTie16 x) : IsRupert (univ.image x) := by
  obtain ⟨K, hK, hc⟩ := exists_certSeq16 T htie
  exact isRupert_of_cert_seq T hnd K hK hc

/-- No horizontal double normal at the views along the line of two planes given by affine face
functions. -/
def NoHDNAff (V : Finset ℝ³) (fP fQ : ℝ³ →ᵃ[ℝ] ℝ) : Prop :=
  ∀ u : ℝ³, u ≠ 0 → fP.linear u = 0 → fQ.linear u = 0 → NoHDNAt V u

/-- **Theorem 19.8 from the facets**: seven points labelled so that `0235`, `1356`
(quadrilaterals), `024`, `036`, `046`, `145`, `146`, `245` are facets (functionals negative off
them) are Rupert, if there is no horizontal double normal at the view along any segment and
along the lines of the six pairs of facets `046/145`, `036/146`, `0235/046`, `046/245`,
`036/024`, `1356/046`, and at most one tie at these views (`OneTie16`). -/
theorem isRupert_type16_limit_facets (x : Fin 7 → ℝ³) (hx : Function.Injective x)
    (fA fB fC fD fE fF fG fH : ℝ³ →ᵃ[ℝ] ℝ)
    (hA : ∀ i, (i ∈ ({0, 2, 3, 5} : Finset (Fin 7)) → fA (x i) = 0) ∧
      (i ∉ ({0, 2, 3, 5} : Finset (Fin 7)) → fA (x i) < 0))
    (hB : ∀ i, (i ∈ ({1, 3, 5, 6} : Finset (Fin 7)) → fB (x i) = 0) ∧
      (i ∉ ({1, 3, 5, 6} : Finset (Fin 7)) → fB (x i) < 0))
    (hC : ∀ i, (i ∈ ({0, 2, 4} : Finset (Fin 7)) → fC (x i) = 0) ∧
      (i ∉ ({0, 2, 4} : Finset (Fin 7)) → fC (x i) < 0))
    (hD : ∀ i, (i ∈ ({0, 3, 6} : Finset (Fin 7)) → fD (x i) = 0) ∧
      (i ∉ ({0, 3, 6} : Finset (Fin 7)) → fD (x i) < 0))
    (hE : ∀ i, (i ∈ ({0, 4, 6} : Finset (Fin 7)) → fE (x i) = 0) ∧
      (i ∉ ({0, 4, 6} : Finset (Fin 7)) → fE (x i) < 0))
    (hF : ∀ i, (i ∈ ({1, 4, 5} : Finset (Fin 7)) → fF (x i) = 0) ∧
      (i ∉ ({1, 4, 5} : Finset (Fin 7)) → fF (x i) < 0))
    (hG : ∀ i, (i ∈ ({1, 4, 6} : Finset (Fin 7)) → fG (x i) = 0) ∧
      (i ∉ ({1, 4, 6} : Finset (Fin 7)) → fG (x i) < 0))
    (hH : ∀ i, (i ∈ ({2, 4, 5} : Finset (Fin 7)) → fH (x i) = 0) ∧
      (i ∉ ({2, 4, 5} : Finset (Fin 7)) → fH (x i) < 0))
    (hnd : ∀ v ∈ univ.image x, ∀ w ∈ univ.image x, v ≠ w →
      NoHDNAt ((univ.image x).erase w) (w - v))
    (hV : NoHDNAff (univ.image x) fE fF ∧ NoHDNAff (univ.image x) fD fG ∧
      NoHDNAff (univ.image x) fA fE ∧ NoHDNAff (univ.image x) fE fH ∧
      NoHDNAff (univ.image x) fD fC ∧ NoHDNAff (univ.image x) fB fE)
    (htie : OneTie16 x) : IsRupert (univ.image x) := by
  let T : Type16 x := ⟨hx, Face16.ofAffine fA hA, Face16.ofAffine fB hB, Face16.ofAffine fC hC,
    Face16.ofAffine fD hD, Face16.ofAffine fE hE, Face16.ofAffine fF hF, Face16.ofAffine fG hG,
    Face16.ofAffine fH hH⟩
  have L : ∀ {fP fQ : ℝ³ →ᵃ[ℝ] ℝ} {SP SQ : Finset (Fin 7)}
      (hP : ∀ i, (i ∈ SP → fP (x i) = 0) ∧ (i ∉ SP → fP (x i) < 0))
      (hQ : ∀ i, (i ∈ SQ → fQ (x i) = 0) ∧ (i ∉ SQ → fQ (x i) < 0)),
      NoHDNAff (univ.image x) fP fQ →
        NoHDNLine16 (univ.image x) (Face16.ofAffine fP hP).N (Face16.ofAffine fQ hQ).N := by
    intro fP fQ SP SQ hP hQ h u hu h1 h2
    rw [Face16.ofAffine_inner] at h1 h2
    exact h u hu h1 h2
  exact isRupert_type16_limit T (T.noHDN_views hnd (L hE hF hV.1) (L hD hG hV.2.1)
    (L hA hE hV.2.2.1) (L hE hH hV.2.2.2.1) (L hD hC hV.2.2.2.2.1) (L hB hE hV.2.2.2.2.2)) htie


end Minimality

end
