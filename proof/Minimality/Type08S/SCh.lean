module

public import Minimality.Type08S.SCf
public import Minimality.Type08S.G9_Final

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true

set_option linter.unusedVariables false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp

/-- `isRupert_or_hdn_of_generic_cert`, refined: the "free" tests need no HDN hypothesis. -/
theorem isRupert_or_hdn_of_generic_cert_free_rim {m n q : ℕ} {ι : Type*} [Finite ι] (free : ι → Prop)
    (shape : (Fin m → ℝ) → Fin n → ℝ³) (hshape : Continuous shape)
    (P : MvPolynomial (Fin m) ℝ) (hP : P ≠ 0) (θ : Fin m → ℝ)
    (T : ι → LabTest n) (hT : ∀ c, CovView (T c).view)
    (hseg : ∀ i j m' : Fin n, shape θ m' ≠ shape θ i → shape θ m' ≠ shape θ j →
      ∀ s : ℝ, 0 < s → s < 1 → shape θ m' ≠ shape θ i + s • (shape θ j - shape θ i))
    (hsp : ∃ i j l m' : Fin n,
      det3 (shape θ j - shape θ i) (shape θ l - shape θ i) (shape θ m' - shape θ i) ≠ 0)
    (hview0 : ∀ c, (T c).view (shape θ) ≠ 0)
    (ties : Fin q → ι × Fin n × Fin n)
    (hties : ∀ t, ⟪shape θ (ties t).2.1 - shape θ (ties t).2.2, (T (ties t).1).view (shape θ)⟫ = 0)
    (hind : TieIndep (fun t => shape θ (ties t).2.1 - shape θ (ties t).2.2)
      (fun t => (T (ties t).1).view (shape θ)))
    -- every tie of every test's rim at the limit follows from the listed ties, at any shape
    (hcover : ∀ y : Fin n → ℝ³, (∀ t, ⟪y (ties t).2.1 - y (ties t).2.2, (T (ties t).1).view y⟫ = 0) →
      ∀ c (i j : ZMod (T c).k),
        ⟪shape θ ((T c).lab i), (T c).view (shape θ)⟫ = ⟪shape θ ((T c).lab j), (T c).view (shape θ)⟫ →
        ⟪y ((T c).lab i), (T c).view y⟫ = ⟪y ((T c).lab j), (T c).view y⟫)
    -- generic certificates (the geometry; MF + R2T inside)
    (hcert : ∀ᶠ p in 𝓝 (θ, (1 : ℝ³ →L[ℝ] ℝ³)), MvPolynomial.eval p.1 P ≠ 0 →
      LinearMap.det (p.2 : ℝ³ →ₗ[ℝ] ℝ³) = 1 →
      -- the listed ties stay independent at `p` (open condition, `TieIndep.eventually`)
      TieIndep (fun t => mapShape p.2 (shape p.1) (ties t).2.1 - mapShape p.2 (shape p.1) (ties t).2.2)
        (fun t => (T (ties t).1).view (mapShape p.2 (shape p.1))) →
      -- no new rim ties: a tie of a rim at `p` is a tie of the limit (closed condition; the proof
      -- of this theorem gets it eventually along the sequence from continuity)
      (∀ c (i j : ZMod (T c).k),
        ⟪mapShape p.2 (shape p.1) ((T c).lab i), (T c).view (mapShape p.2 (shape p.1))⟫ =
          ⟪mapShape p.2 (shape p.1) ((T c).lab j), (T c).view (mapShape p.2 (shape p.1))⟫ →
        ⟪shape θ ((T c).lab i), (T c).view (shape θ)⟫ = ⟪shape θ ((T c).lab j), (T c).view (shape θ)⟫) →
      (∀ t, ⟪mapShape p.2 (shape p.1) (ties t).2.1 - mapShape p.2 (shape p.1) (ties t).2.2,
        (T (ties t).1).view (mapShape p.2 (shape p.1))⟫ = 0) →
      ∃ c, (T c).Cert (mapShape p.2 (shape p.1)))
    (hfreeR : ∀ c, free c → (∃ (k' : ℕ) (_ : NeZero k') (σ : ZMod k' → ZMod (T c).k),
      RimCertAt (shape θ) ((T c).view (shape θ)) ((T c).lab ∘ σ)) → IsRupert (univ.image (shape θ))) :
    IsRupert (univ.image (shape θ)) ∨ ∃ c, ¬ free c ∧
      (∃ (k' : ℕ) (_ : NeZero k') (σ : ZMod k' → ZMod (T c).k),
        RimCertAt (shape θ) ((T c).view (shape θ)) ((T c).lab ∘ σ)) ∧
      ¬ NoHDNAt (univ.image (shape θ)) ((T c).view (shape θ)) := by
  obtain ⟨θs, L, hθs, hL, hPs, hdet, hrest⟩ := exists_seq_restore_ties shape hshape P hP θ
    (fun t => (ties t).2) (fun t => (T (ties t).1).view) (fun t => hT _) hties hind
  let K : ℕ → Fin n → ℝ³ := fun j => mapShape (L j) (shape (θs j))
  have hev : Continuous (fun p : (ℝ³ →L[ℝ] ℝ³) × ℝ³ => p.1 p.2) := continuous_fst.clm_apply continuous_snd
  have hKt : ∀ i, Tendsto (fun j => K j i) atTop (𝓝 (shape θ i)) := by
    intro i
    have h1 : Tendsto (fun j => shape (θs j) i) atTop (𝓝 (shape θ i)) :=
      ((continuous_apply i).comp hshape |>.tendsto θ).comp hθs
    have := (hev.tendsto (1, shape θ i)).comp (hL.prodMk_nhds h1)
    exact this
  have hvt : ∀ c, Tendsto (fun j => (T c).view (K j)) atTop (𝓝 ((T c).view (shape θ))) := by
    intro c
    have h1 : Tendsto (fun j => (T c).view (shape (θs j))) atTop (𝓝 ((T c).view (shape θ))) :=
      (((hT c).1.comp hshape).tendsto θ).comp hθs
    have := (hev.tendsto (1, (T c).view (shape θ))).comp (hL.prodMk_nhds h1)
    exact Tendsto.congr (fun j => ((hT c).2 (L j) (shape (θs j)) (hdet j)).symm) this
  have hpt : Tendsto (fun j => (θs j, L j)) atTop (𝓝 (θ, (1 : ℝ³ →L[ℝ] ℝ³))) :=
    hθs.prodMk_nhds hL
  have hcert' := hpt.eventually hcert
  -- independence along the sequence
  have hdv : Tendsto (fun j => ((fun t => K j (ties t).2.1 - K j (ties t).2.2),
      (fun t => (T (ties t).1).view (K j)))) atTop
      (𝓝 ((fun t => shape θ (ties t).2.1 - shape θ (ties t).2.2),
        (fun t => (T (ties t).1).view (shape θ)))) := by
    refine Tendsto.prodMk_nhds ?_ ?_
    · exact tendsto_pi_nhds.2 fun t => (hKt _).sub (hKt _)
    · exact tendsto_pi_nhds.2 fun t => hvt _
  have hind' := hdv.eventually hind.eventually
  -- no new rim ties along the sequence
  have hnew : ∀ᶠ j in atTop, ∀ c (i j' : ZMod (T c).k),
      ⟪K j ((T c).lab i), (T c).view (K j)⟫ = ⟪K j ((T c).lab j'), (T c).view (K j)⟫ →
      ⟪shape θ ((T c).lab i), (T c).view (shape θ)⟫ = ⟪shape θ ((T c).lab j'), (T c).view (shape θ)⟫ := by
    rw [Filter.eventually_all]; intro c
    rw [Filter.eventually_all]; intro i
    rw [Filter.eventually_all]; intro j'
    by_cases h : ⟪shape θ ((T c).lab i), (T c).view (shape θ)⟫ =
        ⟪shape θ ((T c).lab j'), (T c).view (shape θ)⟫
    · exact Filter.Eventually.of_forall fun _ _ => h
    · have t1 := Tendsto.inner' (hKt ((T c).lab i)) (hvt c)
      have t2 := Tendsto.inner' (hKt ((T c).lab j')) (hvt c)
      have := (t1.sub t2).eventually_ne (sub_ne_zero.2 h)
      exact this.mono fun j hj heq => absurd (sub_eq_zero.2 heq) hj
  have hfreq : ∃ᶠ j in atTop, ∃ c, (T c).Cert (K j) ∧
      ∀ i j' : ZMod (T c).k, ⟪shape θ ((T c).lab i), (T c).view (shape θ)⟫ =
        ⟪shape θ ((T c).lab j'), (T c).view (shape θ)⟫ →
        ⟪K j ((T c).lab i), (T c).view (K j)⟫ = ⟪K j ((T c).lab j'), (T c).view (K j)⟫ := by
    refine ((hcert'.and (hind'.and hnew)).frequently).mono ?_
    rintro j ⟨hc, hi, hn⟩
    have hties' := hrest j
    obtain ⟨c, hcC⟩ := hc (hPs j) (hdet j) hi hn hties'
    exact ⟨c, hcC, fun i j' h => hcover (K j) hties' c i j' h⟩
  obtain ⟨c, hcf⟩ := frequently_exists_of_finite hfreq
  by_cases hf : free c
  · left
    obtain ⟨k', hk, σ, hrim⟩ := exists_limit_rimCert T (shape θ) hsp (hview0) K hKt hvt c hcf
    exact hfreeR c hf ⟨k', hk, σ, hrim⟩
  · by_cases hN : NoHDNAt (univ.image (shape θ)) ((T c).view (shape θ))
    · left
      exact isRupert_of_tendsto_rimCert (shape θ) hseg hsp (T c).lab (hview0 c) hN
        K (fun j => (T c).view (K j)) hKt (hvt c) hcf
    · right
      obtain ⟨k', hk, σ, hrim⟩ := exists_limit_rimCert T (shape θ) hsp (hview0) K hKt hvt c hcf
      exact ⟨c, hf, ⟨k', hk, σ, hrim⟩, hN⟩




theorem isRupert_type08_limit_hdn_rim {a a' b b' c c' d : ℝ³} (N : Norm08 a a' b b' c c' d)
    {q : ℕ} (hq : q ≤ 2) (ties : Fin q → Fin 3 × Fin 7 × Fin 7)
    (hties : ∀ t, ⟪pts08 a a' b b' c c' d (ties t).2.1 - pts08 a a' b b' c c' d (ties t).2.2,
      (grp08 (ties t).1).view (pts08 a a' b b' c c' d)⟫ = 0)
    (hind : TieIndep (fun t => pts08 a a' b b' c c' d (ties t).2.1 - pts08 a a' b b' c c' d (ties t).2.2)
      (fun t => (grp08 (ties t).1).view (pts08 a a' b b' c c' d)))
    (hcover : ∀ i, ∀ T ∈ (grp08 i).tests, ∀ u v : ZMod T.k,
      T.depth (pts08 a a' b b' c c' d) u = T.depth (pts08 a a' b b' c c' d) v →
      Relation.EqvGen (fun p p' => ∃ t, (ties t).1 = i ∧ (ties t).2 = (p, p')) (T.lab u) (T.lab v))
    (hnt : ¬ Touch a a' b b' c c' d)
    (hTco : IsT a' b c d → ¬ CoT2 a a' b b' c c' d)
    (hT'co : IsT' a b c' d → ¬ CoT'2 a a' b b' c c' d) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) ∨
      ∃ t ∈ SC08,
        (∃ (k' : ℕ) (_ : NeZero k') (σ : ZMod k' → ZMod (test08 t.1 t.2.1 t.2.2).k),
          RimCertAt (pts08 a a' b b' c c' d) ((test08 t.1 t.2.1 t.2.2).view (pts08 a a' b b' c c' d))
            ((test08 t.1 t.2.1 t.2.2).lab ∘ σ)) ∧
        ¬ NoHDNAt (insert d ({a, a', b, b', c, c'} : Finset ℝ³))
          ((test08 t.1 t.2.1 t.2.2).view (pts08 a a' b b' c c' d)) := by
  classical
  have hnR : ¬ RTouch a a' b b' c c' d := by
    rintro (h | h | h)
    · exact h (fun ht => absurd (Or.inl ht) hnt)
    · exact h (fun ht => absurd (Or.inr ht) hnt)
    · exact h (fun ht => absurd (Or.inr ht) hnt)
  by_cases hT : IsT a' b c d
  · exact Or.inl (close_T2_final N hT (hTco hT) hnR)
  by_cases hT' : IsT' a b c' d
  · exact Or.inl (close_T'2_final N hT' (hT'co hT') hnR)
  obtain ⟨o, E₁, E₂, E₃, θ, hE, hθ, hpts⟩ := exists_nf08 N
  obtain ⟨hseg, hsp⟩ := seg08 N
  have hview0 := view0_test08 N
  simp only [hpts] at hseg hsp hview0 hties hind hcover
  rw [← image_pts08, hpts]
  let tI : Fin q → (Fin 3 × Bool × Bool) × Fin 7 × Fin 7 := fun t => (((ties t).1, true, true), (ties t).2)
  have hvt : ∀ i y, (test08 i true true).view y = (grp08 i).view y := fun i y => by rw [view_test08_true]
  have key : IsRupert (univ.image (nfShape08 o E₁ E₂ E₃ θ)) ∨ ∃ c : Fin 3 × Bool × Bool, ¬ (c ∉ SC08) ∧
      (∃ (k' : ℕ) (_ : NeZero k') (σ : ZMod k' → ZMod (test08 c.1 c.2.1 c.2.2).k),
        RimCertAt (nfShape08 o E₁ E₂ E₃ θ) ((test08 c.1 c.2.1 c.2.2).view (nfShape08 o E₁ E₂ E₃ θ))
          ((test08 c.1 c.2.1 c.2.2).lab ∘ σ)) ∧
      ¬ NoHDNAt (univ.image (nfShape08 o E₁ E₂ E₃ θ))
        ((test08 c.1 c.2.1 c.2.2).view (nfShape08 o E₁ E₂ E₃ θ)) := by
    refine isRupert_or_hdn_of_generic_cert_free_rim (m := 6) (n := 7) (q := q)
      (ι := Fin 3 × Bool × Bool) (fun c => c ∉ SC08) (nfShape08 o E₁ E₂ E₃) (continuous_nf08 o E₁ E₂ E₃)
      genPoly08 genPoly08_ne_zero θ (fun c => test08 c.1 c.2.1 c.2.2) (fun c => covView_test08 _ _ _)
      hseg hsp hview0 tI (by simpa [tI, hvt] using hties) (by simpa [tI, hvt] using hind)
      ?_ ?_ ?_
    · intro y hy c i j hij
      obtain ⟨T, hT, h⟩ := test08_eq c.1 c.2.1 c.2.2
      refine cover_transfer hcover ?_ hT (h.imp Eq.symm Eq.symm) i j hij
      intro t
      simpa [tI, hvt] using hy t
    · have hineq : ∀ᶠ p in 𝓝 (θ, (1 : ℝ³ →L[ℝ] ℝ³)), ∀ k, 0 < ineq08 p.1 k := by
        rw [Filter.eventually_all]
        intro k
        exact ((continuous_ineq08 k).comp continuous_fst).continuousAt.eventually (lt_mem_nhds (hθ k))
      filter_upwards [hineq] with p hp hg hdet hind' hnew hties'
      simp only [mapShape_nfShape08] at hind' hnew hties' ⊢
      have hE' : det3 (p.2 E₁) (p.2 E₂) (p.2 E₃) ≠ 0 := by
        rw [det3_map, detMap_eq08, hdet, one_mul]; exact hE
      set Y := nfShape08 (p.2 o) (p.2 E₁) (p.2 E₂) (p.2 E₃) p.1 with hY
      have hnew' : ∀ c : Fin 3 × Bool × Bool, ∀ i j : ZMod (test08 c.1 c.2.1 c.2.2).k,
          ⟪Y ((test08 c.1 c.2.1 c.2.2).lab i), (test08 c.1 c.2.1 c.2.2).view Y⟫ =
            ⟪Y ((test08 c.1 c.2.1 c.2.2).lab j), (test08 c.1 c.2.1 c.2.2).view Y⟫ →
          ⟪nfShape08 o E₁ E₂ E₃ θ ((test08 c.1 c.2.1 c.2.2).lab i),
            (test08 c.1 c.2.1 c.2.2).view (nfShape08 o E₁ E₂ E₃ θ)⟫ =
          ⟪nfShape08 o E₁ E₂ E₃ θ ((test08 c.1 c.2.1 c.2.2).lab j),
            (test08 c.1 c.2.1 c.2.2).view (nfShape08 o E₁ E₂ E₃ θ)⟫ := hnew
      have hties'' : ∀ t, ⟪Y (ties t).2.1 - Y (ties t).2.2, (grp08 (ties t).1).view Y⟫ = 0 := by
        intro t; simpa [tI, hvt] using hties' t
      have hind'' : TieIndep (fun t => Y (ties t).2.1 - Y (ties t).2.2)
          (fun t => (grp08 (ties t).1).view Y) := by simpa [tI, hvt] using hind'
      have hcov : ∀ i, ∀ T ∈ (grp08 i).tests, ∀ u v : ZMod T.k, T.depth Y u = T.depth Y v →
          Relation.EqvGen (fun p p' => ∃ t, (ties t).1 = i ∧ (ties t).2 = (p, p')) (T.lab u) (T.lab v) := by
        intro i T hT u v huv
        have hT' := hT
        rw [← grpS_true] at hT'
        obtain ⟨j, rfl⟩ := grpS_tests i true T hT'
        exact hcover i _ hT u v (hnew' (i, true, j) u v huv)
      have hno : ∀ i, ¬ (grp08 i).Straddle Y := by
        intro i hst
        fin_cases i
        all_goals first | exact hst.elim | skip
        all_goals apply hnt
        · simp only [grp08, ViewGroup.Straddle] at hst
          obtain ⟨h1, h2, -, -⟩ := hst
          have e1 := hnew' (0, true, true) 1 2 h1
          have e2 := hnew' (0, true, true) 2 3 h2
          rw [← hpts] at e1 e2
          exact Or.inl ⟨e1, e2.symm⟩
        · simp only [grp08, ViewGroup.Straddle] at hst
          obtain ⟨h1, h2, -, -⟩ := hst
          have e1 := hnew' (1, true, true) 1 2 h1
          have e2 := hnew' (1, true, true) 2 3 h2
          rw [← hpts] at e1 e2
          exact Or.inr ⟨e2.symm, e1⟩
      obtain ⟨i, s, j, hC⟩ := cert08_generic (p.2 o) (p.2 E₁) (p.2 E₂) (p.2 E₃) hE' p.1 hp hg hq ties
        hties'' hind'' hcov hno
      exact ⟨(i, s, j), hC⟩
    · intro c hc hrim
      obtain ⟨k', hk, σ, hr⟩ := hrim
      rw [← hpts] at hr
      rw [← hpts, image_pts08]
      exact rupert_of_free_limit_rim N hT hT' c hc σ hr
  exact key.imp id (fun ⟨c, hc, hr, hn⟩ => ⟨c, not_not.1 hc, hr, hn⟩)


end Type08Sp
end Minimality
