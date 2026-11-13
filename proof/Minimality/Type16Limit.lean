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
  `R2`), a nonzero polynomial (`genPoly16_ne_zero`); `exists_seq_eval_ne_zero_fin`: the shapes off
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

theorem tendsto_nfP {ι : Type*} {l : Filter ι} {o E₁ E₂ E₃ : ι → ℝ³} {o₀ F₁ F₂ F₃ : ℝ³}
    {α β γ : ι → ℝ} {α₀ β₀ γ₀ : ℝ} (ho : Tendsto o l (𝓝 o₀)) (h₁ : Tendsto E₁ l (𝓝 F₁))
    (h₂ : Tendsto E₂ l (𝓝 F₂)) (h₃ : Tendsto E₃ l (𝓝 F₃)) (hα : Tendsto α l (𝓝 α₀))
    (hβ : Tendsto β l (𝓝 β₀)) (hγ : Tendsto γ l (𝓝 γ₀)) :
    Tendsto (fun t => nfP (o t) (E₁ t) (E₂ t) (E₃ t) (α t) (β t) (γ t)) l
      (𝓝 (nfP o₀ F₁ F₂ F₃ α₀ β₀ γ₀)) := by
  simp only [nfP]
  exact ((ho.add (hα.smul h₁)).add (hβ.smul h₂)).add (hγ.smul h₃)

/-! ### The sign conditions of the route as one polynomial -/

/-- **The nonvanishing set of a nonzero polynomial is dense**, as a sequence, in any number of variables: every point is a
limit of points where the polynomial does not vanish (`MvPolynomial.funext_set` on boxes). -/
theorem exists_seq_eval_ne_zero_fin {m : ℕ} {P : MvPolynomial (Fin m) ℝ} (hP : P ≠ 0) (θ : Fin m → ℝ) :
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

theorem restore_nfP (s : ℝ) (e b o E₁ E₂ E₃ : ℝ³) (α β γ : ℝ) :
    restore s e b (nfP o E₁ E₂ E₃ α β γ) =
      nfP (restore s e b o) (restore s e b E₁) (restore s e b E₂) (restore s e b E₃) α β γ := by
  simp only [nfP, restore_add, restore_smul]

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

/-- **Named views from a table of vertex crossings** (shared by types 16, 21, 29): the segments
`x j - x i` and, for each row of `vtx`, the line of two planes through label triples. -/
noncomputable def namedView {k : ℕ}
    (vtx : Fin k → (Fin 7 × Fin 7 × Fin 7) × (Fin 7 × Fin 7 × Fin 7)) (x : Fin 7 → ℝ³) :
    (Fin 7 × Fin 7) ⊕ Fin k → ℝ³
  | .inl ij => x ij.2 - x ij.1
  | .inr t => planeLine (x (vtx t).1.1) (x (vtx t).1.2.1) (x (vtx t).1.2.2) (x (vtx t).2.1)
      (x (vtx t).2.2.1) (x (vtx t).2.2.2)

theorem tendsto_namedView {k : ℕ} (vtx : Fin k → (Fin 7 × Fin 7 × Fin 7) × (Fin 7 × Fin 7 × Fin 7))
    {ι : Type*} {l : Filter ι} {K : ι → Fin 7 → ℝ³} {x : Fin 7 → ℝ³}
    (hK : ∀ m, Tendsto (fun n => K n m) l (𝓝 (x m))) (v : (Fin 7 × Fin 7) ⊕ Fin k) :
    Tendsto (fun n => namedView vtx (K n) v) l (𝓝 (namedView vtx x v)) := by
  rcases v with ⟨i, j⟩ | t
  · exact (hK j).sub (hK i)
  · exact tendsto_planeLine (hK _) (hK _) (hK _) (hK _) (hK _) (hK _)

theorem tendsto_view16 {ι : Type*} {l : Filter ι} {K : ι → Fin 7 → ℝ³} {x : Fin 7 → ℝ³}
    (hK : ∀ m, Tendsto (fun n => K n m) l (𝓝 (x m))) (v : (Fin 7 × Fin 7) ⊕ Fin 6) :
    Tendsto (fun n => view16 (K n) v) l (𝓝 (view16 x v)) := by
  rcases v with ⟨i, j⟩ | t
  · exact tendsto_namedView vtx16 hK (.inl (i, j))
  · exact tendsto_namedView vtx16 hK (.inr t)

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

/-! ### Ties at named views (generic over the vertex-line index type) -/

theorem inner_coords (a b : ℝ³) : ⟪a, b⟫ = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, mul_comm]

/-- A tie at a named view: two labels `s ≠ t` at equal depth along a nonzero named view.
(`view`: the named views of a type; `W`: its vertex-line index type.) -/
def TieInstG {W : Type*} (view : (Fin 7 → ℝ³) → (Fin 7 × Fin 7) ⊕ W → ℝ³) (x : Fin 7 → ℝ³)
    (v : (Fin 7 × Fin 7) ⊕ W) (s t : Fin 7) : Prop :=
  s ≠ t ∧ view x v ≠ 0 ∧ ⟪x s - x t, view x v⟫ = 0

/-- Two ties that are one equation for every shape: the same view (up to reversing a segment)
and the same pair, or the tie of `s, t` along `i j` and the tie of `i, j` along `s t`. -/
def SameTieG {W : Type*} (v : (Fin 7 × Fin 7) ⊕ W) (s t : Fin 7) (v' : (Fin 7 × Fin 7) ⊕ W)
    (s' t' : Fin 7) : Prop :=
  ((v' = v ∨ ∃ i j, v = .inl (i, j) ∧ v' = .inl (j, i)) ∧
      ((s' = s ∧ t' = t) ∨ (s' = t ∧ t' = s))) ∨
    ∃ i j, v = .inl (i, j) ∧ (v' = .inl (s, t) ∨ v' = .inl (t, s)) ∧
      ((s' = i ∧ t' = j) ∨ (s' = j ∧ t' = i))

/-- **At most one tie** at the named views of `x`: any two ties are one equation.  Two ties that
are not one equation are two conditions on the shape, so this fails only in codimension 2. -/
def OneTieG {W : Type*} (view : (Fin 7 → ℝ³) → (Fin 7 × Fin 7) ⊕ W → ℝ³) (x : Fin 7 → ℝ³) : Prop :=
  ∀ v s t v' s' t', TieInstG view x v s t → TieInstG view x v' s' t' → SameTieG v s t v' s' t'

/-- One equation holds at every shape where the other does. -/
theorem SameTieG.inner_eq_zero {W : Type*} {view : (Fin 7 → ℝ³) → (Fin 7 × Fin 7) ⊕ W → ℝ³}
    (hseg : ∀ x i j, view x (.inl (i, j)) = x j - x i) {v : (Fin 7 × Fin 7) ⊕ W} {s t : Fin 7}
    {v' : (Fin 7 × Fin 7) ⊕ W} {s' t' : Fin 7} (h : SameTieG v s t v' s' t')
    (y : Fin 7 → ℝ³) (h0 : ⟪y s - y t, view y v⟫ = 0) : ⟪y s' - y t', view y v'⟫ = 0 := by
  rcases h with ⟨hv, hp⟩ | ⟨i, j, rfl, hv', hp⟩
  · have hv'' : view y v' = view y v ∨ view y v' = -view y v := by
      rcases hv with rfl | ⟨i, j, rfl, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (by simp only [hseg, neg_sub])
    have hp' : y s' - y t' = y s - y t ∨ y s' - y t' = -(y s - y t) := by
      rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (neg_sub _ _).symm
    rcases hv'' with e | e <;> rcases hp' with f | f <;>
      simp only [e, f, inner_neg_left, inner_neg_right, h0, neg_zero]
  · simp only [hseg] at h0
    rw [inner_coords] at h0
    rcases hv' with rfl | rfl <;> rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [hseg] <;> rw [inner_coords] <;>
      simp only [PiLp.sub_apply] at h0 ⊢ <;>
      first | linear_combination h0 | linear_combination -h0

/-- **At most one tie at a named view** of a shape whose ties are ties of `x`. -/
theorem oneTieAt_of_tiesG {W : Type*} {view : (Fin 7 → ℝ³) → (Fin 7 × Fin 7) ⊕ W → ℝ³}
    (hseg : ∀ x i j, view x (.inl (i, j)) = x j - x i) {x y : Fin 7 → ℝ³}
    (htie : OneTieG view x)
    (hsub : ∀ v a b, a ≠ b → view y v ≠ 0 → ⟪y a - y b, view y v⟫ = 0 → TieInstG view x v a b)
    (v : (Fin 7 × Fin 7) ⊕ W) (hv : view y v ≠ 0) :
    OneTieAt (Finset.univ.image y) (view y v) := by
  intro s hs t ht s' hs' t' ht' hst hst' e1 e2
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨a', -, rfl⟩ := Finset.mem_image.mp hs'
  obtain ⟨b', -, rfl⟩ := Finset.mem_image.mp ht'
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
    have hne' : x j - x i ≠ 0 := by rwa [hseg] at hne
    have h0' : ⟪x a - x b, x j - x i⟫ = 0 := by rwa [hseg] at h0
    rcases hij with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2] at hne' h0'
      rw [← neg_sub, inner_neg_left, neg_eq_zero] at h0'
      exact hne' (inner_self_eq_zero.mp h0')
    · rw [h1, h2] at hne' h0'
      exact hne' (inner_self_eq_zero.mp h0')

/-- **Strict comparisons persist**: eventually every tie of `K_n` at a named view is a tie of the
limit `x`. -/
theorem eventually_tiesG {W : Type*} [Finite W]
    {view : (Fin 7 → ℝ³) → (Fin 7 × Fin 7) ⊕ W → ℝ³} {x : Fin 7 → ℝ³} {K : ℕ → Fin 7 → ℝ³}
    (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m)))
    (htv : ∀ v, Tendsto (fun n => view (K n) v) atTop (𝓝 (view x v))) :
    ∀ᶠ n in atTop, ∀ v a b, ⟪K n a - K n b, view (K n) v⟫ = 0 →
      ⟪x a - x b, view x v⟫ = 0 := by
  have h : ∀ q : ((Fin 7 × Fin 7) ⊕ W) × Fin 7 × Fin 7, ∀ᶠ n in atTop,
      ⟪K n q.2.1 - K n q.2.2, view (K n) q.1⟫ = 0 → ⟪x q.2.1 - x q.2.2, view x q.1⟫ = 0 := by
    rintro ⟨v, a, b⟩
    by_cases h0 : ⟪x a - x b, view x v⟫ = 0
    · exact Eventually.of_forall fun _ _ => h0
    · exact ((((hK a).sub (hK b)).inner (htv v)).eventually_ne h0).mono
        fun n hn h => absurd h hn
  filter_upwards [eventually_all.mpr h] with n hn v a b h
  exact hn (v, a, b) h

/-! ### Ties at the named views of type 16 -/

/-- Two ties that are one equation for every shape (`SameTieG`). -/
abbrev SameTie16 (v : (Fin 7 × Fin 7) ⊕ Fin 6) (s t : Fin 7) (v' : (Fin 7 × Fin 7) ⊕ Fin 6) (s' t' : Fin 7) : Prop :=
  SameTieG v s t v' s' t'

/-- One equation holds at every shape where the other does. -/
theorem SameTie16.inner_eq_zero {v : (Fin 7 × Fin 7) ⊕ Fin 6} {s t : Fin 7}
    {v' : (Fin 7 × Fin 7) ⊕ Fin 6} {s' t' : Fin 7} (h : SameTie16 v s t v' s' t')
    (y : Fin 7 → ℝ³) (h0 : ⟪y s - y t, view16 y v⟫ = 0) : ⟪y s' - y t', view16 y v'⟫ = 0 :=
  SameTieG.inner_eq_zero (fun _ _ _ => rfl) h y h0

theorem OneTieAt.smul {V : Finset ℝ³} {u : ℝ³} (h : OneTieAt V u) {c : ℝ} (hc : c ≠ 0) :
    OneTieAt V (c • u) := by
  intro s hs t ht s' hs' t' ht' hst hst' e1 e2
  simp only [real_inner_smul_right] at e1 e2
  exact h s hs t ht s' hs' t' ht' hst hst' (mul_left_cancel₀ hc e1) (mul_left_cancel₀ hc e2)

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
  obtain ⟨u, ⟨v, c, hc0, rfl⟩, k, hk, z, hz⟩ := h.toN
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

end Minimality

end
