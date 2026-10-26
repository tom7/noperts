module

public import Minimality.Type29Faces

@[expose] public section

/-!
# Type 29: the labelled closings and their limit (`FEWER-FACES-PROOFS.md` §22, §28)

The limit lemma of `Type29Limit.lean` makes a type-29 shape of class K3a or K4a Rupert unless the
limit rim has a horizontal double normal (HDN) at its named view.  Theorem 28.10 replaces "no HDN
at every named view" by codimension-2 exceptions, closing by closing.  This file sets up the
finitely many closings and the limit lemma for the two-triangle views.

* `Lab29`, `Lab29.Ok`, `Lab29.view`, `CertAt29`, `cert29_iff`: the closings of the whitelists and
  the certificate of one of them.
* `CertAt29.quad_at`, `quint_at`, `tri_at`, `epair_at`: a labelled rim certificate with a sign.
* `isRupert_of_certL_seq29_or`: Lemma 18.2 with "no HDN, or `Sec29`" (two triangles).
* `RimCertAt.rev4`, `rev3`: a rim read backwards at the opposite view.
* `NF29.params_eq`, `Ex29.lim`, `Ex29.lim_of_freq`: the region facts of a certificate at the
  limit (the normal form of a point set is unique; the inequalities are closed).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

variable {x : Fin 7 → ℝ³}

instance : Fintype Ex29 := ⟨{.none, .t1, .t1o, .t2, .t2o}, by intro e; cases e <;> decide⟩

/-- **A closing of the whitelists**: a four-corner rim (with its region tag), a five-corner rim, a
triangular rim, or an edge pair `(v, w, a, b, c)` of Lemma E. -/
abbrev Lab29 : Type :=
  (View29 × (Fin 7 × Fin 7 × Fin 7 × Fin 7) × Ex29) ⊕
    (View29 × (Fin 7 × Fin 7 × Fin 7 × Fin 7 × Fin 7)) ⊕
    (View29 × (Fin 7 × Fin 7 × Fin 7) × Ex29) ⊕ (Fin 7 × Fin 7 × Fin 7 × Fin 7 × Fin 7)

/-- The closings that occur in the covers (`quadLabels29`, …, `ePairLabels29`). -/
def Lab29.Ok : Lab29 → Prop
  | .inl q => q ∈ quadLabels29
  | .inr (.inl q) => q ∈ quintLabels29
  | .inr (.inr (.inl q)) => q ∈ triLabels29
  | .inr (.inr (.inr q)) => q ∈ ePairLabels29

/-- The named view of a closing (an edge pair lives at the segment `v w`). -/
def Lab29.view : Lab29 → View29
  | .inl q => q.1
  | .inr (.inl q) => q.1
  | .inr (.inr (.inl q)) => q.1
  | .inr (.inr (.inr q)) => .inl (q.1, q.2.1)

/-- **The certificate of one closing** at a shape `y`. -/
def CertAt29 (y : Fin 7 → ℝ³) : Lab29 → Prop
  | .inl (v, (i₀, i₁, i₂, i₃), e) => e.facts y ∧ ∃ c : ℝ, c ≠ 0 ∧
      RimCertPts (univ.image y) (c • view29 y v) (quad (y i₀) (y i₁) (y i₂) (y i₃))
  | .inr (.inl (v, (i₀, i₁, i₂, i₃, i₄))) => ∃ c : ℝ, c ≠ 0 ∧
      RimCertPts (univ.image y) (c • view29 y v) (quint (y i₀) (y i₁) (y i₂) (y i₃) (y i₄))
  | .inr (.inr (.inl (v, (i₀, i₁, i₂), e))) => e.facts y ∧ ∃ c : ℝ, c ≠ 0 ∧
      RimCertPts (univ.image y) (c • view29 y v) (tri (y i₀) (y i₁) (y i₂))
  | .inr (.inr (.inr (v, w, a, b, c))) =>
      ∃ σ : ℝ, EPairData (univ.image y) σ (y v) (y w) (y a) (y b) (y c)

/-- **A type-29 certificate is the certificate of a whitelisted closing.** -/
theorem cert29_iff (y : Fin 7 → ℝ³) : Cert29 y ↔ ∃ ℓ : Lab29, ℓ.Ok ∧ CertAt29 y ℓ := by
  constructor
  · rintro (⟨v, i₀, i₁, i₂, i₃, e, hm, hf, c, hc, hr⟩ | ⟨v, i₀, i₁, i₂, i₃, i₄, hm, c, hc, hr⟩ |
      ⟨v, i₀, i₁, i₂, e, hm, hf, c, hc, hr⟩ | ⟨v, w, a, b, c, hm, σ, hσ⟩)
    · exact ⟨.inl (v, (i₀, i₁, i₂, i₃), e), hm, hf, c, hc, hr⟩
    · exact ⟨.inr (.inl (v, (i₀, i₁, i₂, i₃, i₄))), hm, c, hc, hr⟩
    · exact ⟨.inr (.inr (.inl (v, (i₀, i₁, i₂), e))), hm, hf, c, hc, hr⟩
    · exact ⟨.inr (.inr (.inr (v, w, a, b, c))), hm, σ, hσ⟩
  · rintro ⟨ℓ | ℓ | ℓ | ℓ, hok, h⟩
    · obtain ⟨v, ⟨i₀, i₁, i₂, i₃⟩, e⟩ := ℓ
      obtain ⟨hf, c, hc, hr⟩ := h
      exact Or.inl ⟨v, i₀, i₁, i₂, i₃, e, hok, hf, c, hc, hr⟩
    · obtain ⟨v, ⟨i₀, i₁, i₂, i₃, i₄⟩⟩ := ℓ
      obtain ⟨c, hc, hr⟩ := h
      exact Or.inr (Or.inl ⟨v, i₀, i₁, i₂, i₃, i₄, hok, c, hc, hr⟩)
    · obtain ⟨v, ⟨i₀, i₁, i₂⟩, e⟩ := ℓ
      obtain ⟨hf, c, hc, hr⟩ := h
      exact Or.inr (Or.inr (Or.inl ⟨v, i₀, i₁, i₂, e, hok, hf, c, hc, hr⟩))
    · obtain ⟨v, w, a, b, c⟩ := ℓ
      obtain ⟨σ, hσ⟩ := h
      exact Or.inr (Or.inr (Or.inr ⟨v, w, a, b, c, hok, σ, hσ⟩))

/-! ### Labelled rims with a sign -/

theorem quad_map {α β : Type*} (f : α → β) (a b c d : α) :
    (fun i => f (quad a b c d i)) = quad (f a) (f b) (f c) (f d) := by
  funext i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rfl

theorem quint_map {α β : Type*} (f : α → β) (a b c d e : α) :
    (fun i => f (quint a b c d e i)) = quint (f a) (f b) (f c) (f d) (f e) := by
  funext i; rcases zmod5_cases i with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem tri_map {α β : Type*} (f : α → β) (a b c : α) :
    (fun i => f (tri a b c i)) = tri (f a) (f b) (f c) := by
  funext i; rcases zmod3_cases i with rfl | rfl | rfl <;> rfl

/-- A rim certificate in point form is one in label form. -/
theorem RimCertPts.atOf {k : ℕ} {y : Fin 7 → ℝ³} {u : ℝ³} {lab : ZMod k → Fin 7}
    (h : RimCertPts (univ.image y) u (fun i => y (lab i))) : RimCertAt y u lab where
  three := h.three
  cyc := h.cyc
  left m i := h.left (y m) (mem_image_of_mem y (mem_univ m)) i
  robust := h.robust

/-- **A rim certificate at `c • w`, `c ≠ 0`, is one at `sgnB ε • w`** (positive scaling). -/
theorem RimCertPts.sgn {k : ℕ} {V : Finset ℝ³} {w : ℝ³} {Y : ZMod k → ℝ³} {c : ℝ} (hc : c ≠ 0)
    (h : RimCertPts V (c • w) Y) : ∃ ε : Bool, RimCertPts V (sgnB ε • w) Y := by
  have hpos : 0 < |c|⁻¹ := inv_pos.mpr (abs_pos.mpr hc)
  have hz' := h.smul hpos
  rw [smul_smul] at hz'
  have hsg : |c|⁻¹ * c = sgnB (decide (0 < c)) := by
    rcases lt_or_gt_of_ne hc with h | h
    · rw [abs_of_neg h, sgnB, decide_eq_false (not_lt.mpr h.le)]
      field_simp; simp
    · rw [abs_of_pos h, sgnB, decide_eq_true h, inv_mul_cancel₀ h.ne']; simp
  rw [hsg] at hz'
  exact ⟨_, hz'⟩

/-- The certificate of a four-corner closing, in label form with a sign. -/
theorem CertAt29.quad_at {y : Fin 7 → ℝ³} {v : View29} {i₀ i₁ i₂ i₃ : Fin 7} {e : Ex29}
    (h : CertAt29 y (.inl (v, (i₀, i₁, i₂, i₃), e))) :
    e.facts y ∧ ∃ ε : Bool, RimCertAt y (sgnB ε • view29 y v) (quad i₀ i₁ i₂ i₃) := by
  obtain ⟨hf, c, hc, hr⟩ := h
  obtain ⟨ε, hε⟩ := hr.sgn hc
  refine ⟨hf, ε, RimCertPts.atOf ?_⟩
  rw [quad_map]; exact hε

theorem CertAt29.quint_at {y : Fin 7 → ℝ³} {v : View29} {i₀ i₁ i₂ i₃ i₄ : Fin 7}
    (h : CertAt29 y (.inr (.inl (v, (i₀, i₁, i₂, i₃, i₄))))) :
    ∃ ε : Bool, RimCertAt y (sgnB ε • view29 y v) (quint i₀ i₁ i₂ i₃ i₄) := by
  obtain ⟨c, hc, hr⟩ := h
  obtain ⟨ε, hε⟩ := hr.sgn hc
  refine ⟨ε, RimCertPts.atOf ?_⟩
  rw [quint_map]; exact hε

theorem CertAt29.tri_at {y : Fin 7 → ℝ³} {v : View29} {i₀ i₁ i₂ : Fin 7} {e : Ex29}
    (h : CertAt29 y (.inr (.inr (.inl (v, (i₀, i₁, i₂), e))))) :
    e.facts y ∧ ∃ ε : Bool, RimCertAt y (sgnB ε • view29 y v) (tri i₀ i₁ i₂) := by
  obtain ⟨hf, c, hc, hr⟩ := h
  obtain ⟨ε, hε⟩ := hr.sgn hc
  refine ⟨hf, ε, RimCertPts.atOf ?_⟩
  rw [tri_map]; exact hε

/-- An edge pair is a rim certificate at its segment (Corollary 14.1 with ties), in label form
with 3, 4 or 5 corners (`CertL29`). -/
theorem CertAt29.epair_at {y : Fin 7 → ℝ³} {v w a b c : Fin 7}
    (h : CertAt29 y (.inr (.inr (.inr (v, w, a, b, c))))) :
    ∃ (ε : Bool) (L : (ZMod 3 → Fin 7) ⊕ (ZMod 4 → Fin 7) ⊕ (ZMod 5 → Fin 7)),
      CertL29 y (.inl (v, w)) ε L := by
  obtain ⟨σ, hσ, q₁, q₂, q₃, q₄, hE, h3, hV⟩ := h
  have hrc := rimCert_edgePairσ_robust _ hσ (img29 v) (img29 w) (img29 a) (img29 b) (img29 c)
    q₁ q₂ q₃ q₄ hE h3 hV
  obtain ⟨k, hk, Y, hY⟩ := hrc
  obtain ⟨lab, -, hat⟩ := hY.toAt
  have hs : sgnB true • view29 y (.inl (v, w)) = y w - y v := by simp [sgnB, view29]
  rcases hk with rfl | rfl | rfl
  · exact ⟨true, .inl lab, by rw [CertL29]; simp only [Sum.elim_inl]; rw [hs]; exact hat⟩
  · exact ⟨true, .inr (.inl lab), by
      rw [CertL29]; simp only [Sum.elim_inr, Sum.elim_inl]; rw [hs]; exact hat⟩
  · exact ⟨true, .inr (.inr lab), by rw [CertL29]; simp only [Sum.elim_inr]; rw [hs]; exact hat⟩

/-! ### Lemma 18.2 with a tilt alternative -/

theorem NF29.det_frame_ne (N : NF29 x) : det3 (x 4 - x 1) (x 5 - x 1) (x 3 - x 1) ≠ 0 := by
  have : det3 (x 4 - x 1) (x 5 - x 1) (x 3 - x 1) = -N.D := by
    nf29_simp N
    simp only [det3c, NF29.D]
    ring
  rw [this]; exact neg_ne_zero.mpr N.hD

/-- The limit of ties: a tie of the limit is a tie of the approximants. -/
def TiesAt29 (x : Fin 7 → ℝ³) (y : Fin 7 → ℝ³) : Prop :=
  ∀ w a b, TieInst29 x w a b → ⟪y a - y b, view29 y w⟫ = 0

/-- **Lemma 18.2 for one labelled certificate, with Proposition 22.2** (two triangles): as
`isRupert_of_certL_seq29`, with "no horizontal double normal at the named view, or `Sec29`". -/
theorem isRupert_of_certL_seq29_or (N : NF29 x)
    (K : ℕ → Fin 7 → ℝ³) (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m)))
    {k : ℕ} [NeZero k] (v : View29) (ε : Bool) (lab : ZMod k → Fin 7)
    (hnd : NoHDNAt (univ.image x) (view29 x v) ∨ Sec29 x v)
    (hc : ∃ᶠ n in atTop, RimCertAt (K n) (sgnB ε • view29 (K n) v) lab ∧ TiesAt29 x (K n)) :
    IsRupert (univ.image x) := by
  obtain ⟨n₀, hn₀, -⟩ := hc.exists
  have hv : ∀ i, v ≠ .inl (i, i) := by
    rintro i rfl
    apply hn₀.ne_zero
    simp [view29]
  have hv0 := N.view29_ne_zero v hv
  have hs := sgnB_ne_zero ε
  refine isRupert_of_tendsto_rimCert_or x N.inj N.noSeg ⟨1, 4, 5, 3, N.det_frame_ne⟩ lab
    (smul_ne_zero hs hv0) ?_ K (fun n => sgnB ε • view29 (K n) v) hK
    ((tendsto_view29 hK v).const_smul _) (hc.mono fun n hn => ⟨hn.1, fun i j e => ?_⟩)
  · rcases hnd with h | h
    · exact Or.inl (h.smul_view hs)
    · exact Or.inr fun hleft => h.tiltHides N hv0 ε hn₀ hleft
  · by_cases hij : lab i = lab j
    · rw [hij]
    · rw [real_inner_smul_right, real_inner_smul_right] at e
      have e' := mul_left_cancel₀ hs e
      have h := hn.2 v (lab i) (lab j) ⟨hij, hv0, by rw [inner_sub_left, e', sub_self]⟩
      rw [inner_sub_left, sub_eq_zero] at h
      simp only [real_inner_smul_right, h]

/-- A labelled rim certificate is a rim certificate in point form. -/
theorem RimCertAt.toPts {k : ℕ} {y : Fin 7 → ℝ³} {u : ℝ³} {lab : ZMod k → Fin 7}
    (h : RimCertAt y u lab) : RimCertPts (univ.image y) u (fun i => y (lab i)) where
  three := h.three
  mem i := mem_image_of_mem y (mem_univ _)
  cyc := h.cyc
  left z hz i := by
    obtain ⟨m, -, rfl⟩ := mem_image.mp hz
    exact h.left m i
  robust := h.robust

/-! ### Reversing a rim -/

theorem IsRobustUnimodal.reflect {k : ℕ} {z : ZMod k → ℝ} (hz : IsRobustUnimodal z) :
    IsRobustUnimodal (fun i => z (-i)) where
  noPeaks B a b c d hab hbc hcd hdk h := by
    have e : ∀ x : ℕ, x ≤ d →
        -(B + (x : ZMod k)) = (-B - (d : ZMod k)) + ((d - x : ℕ) : ZMod k) := by
      intro x hx; rw [Nat.cast_sub hx]; ring
    have ea := e a (by omega)
    have eb := e b (by omega)
    have ec := e c (by omega)
    have ed := e d le_rfl
    simp only [Nat.sub_self, Nat.cast_zero, add_zero] at ed
    simp only [ea, eb, ec, ed] at h
    refine hz.noPeaks' (-B - (d : ZMod k)) (a := 0) (b := d - c) (c := d - b) (d := d - a)
      (by omega) (by omega) (by omega) (by omega) ?_
    simp only [Nat.cast_zero, add_zero]
    obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨h4, h2, h3, h1⟩
  noTriple i j l hij hjl hil e1 e2 := hz.noTriple (-i) (-j) (-l) (neg_injective.ne hij)
    (neg_injective.ne hjl) (neg_injective.ne hil) e1 e2
  noLevelRun B a b c d hab hbc hcd hdk e := by
    have eq : ∀ x : ℕ, x ≤ d →
        -(B + (x : ZMod k)) = (-B - (d : ZMod k)) + ((d - x : ℕ) : ZMod k) := by
      intro x hx; rw [Nat.cast_sub hx]; ring
    have ea := eq a (by omega)
    have eb := eq b (by omega)
    have ec := eq c (by omega)
    have ed := eq d le_rfl
    simp only [Nat.sub_self, Nat.cast_zero, add_zero] at ed
    simp only [ea, eb, ec, ed] at e ⊢
    have := hz.noLevelRun (-B - (d : ZMod k)) 0 (d - c) (d - b) (d - a) (by omega) (by omega)
      (by omega) (by omega) e.symm
    try simp only [Nat.cast_zero, add_zero] at this
    exact ⟨fun h => this.2 ⟨h.2, h.1⟩, fun h => this.1 ⟨h.2, h.1⟩⟩

/-- **A rim read backwards, at the opposite view, is a rim.** -/
theorem RimCertPts.reflect {k : ℕ} {V : Finset ℝ³} {u : ℝ³} {Y : ZMod k → ℝ³}
    (h : RimCertPts V u Y) : RimCertPts V (-u) (fun i => Y (-i)) where
  three := h.three
  mem i := h.mem (-i)
  cyc i j hi hj := by
    have key := h.cyc (-i - 1) (-j)
      (fun e => hj (neg_injective (by rw [e]; ring)))
      (fun e => hi (neg_injective (by rw [e]; ring)))
    have e1 : -i - 1 + 1 = -i := by ring
    have e2 : -(i + 1) = -i - 1 := by ring
    rw [e1] at key
    simp only [e2]
    have : det3 (Y (-i - 1) - Y (-i)) (Y (-j) - Y (-i)) (-u) =
        det3 (Y (-i) - Y (-i - 1)) (Y (-j) - Y (-i - 1)) u := by
      simp only [det3_expand, PiLp.sub_apply, PiLp.neg_apply]; ring
    rw [this]; exact key
  left z hz i := by
    have key := h.left z hz (-i - 1)
    have e1 : -i - 1 + 1 = -i := by ring
    have e2 : -(i + 1) = -i - 1 := by ring
    rw [e1] at key
    simp only [e2]
    have : det3 (Y (-i - 1) - Y (-i)) (z - Y (-i)) (-u) =
        det3 (Y (-i) - Y (-i - 1)) (z - Y (-i - 1)) u := by
      simp only [det3_expand, PiLp.sub_apply, PiLp.neg_apply]; ring
    rw [this]; exact key
  robust := by
    have := h.robust.reflect.neg
    simpa only [inner_neg_right] using this

/-- A four-corner rim read backwards: `quad y₀ y₁ y₂ y₃` at `u` is `quad y₀ y₃ y₂ y₁` at `−u`. -/
theorem RimCertAt.rev4 {y : Fin 7 → ℝ³} {u : ℝ³} {a b c d : Fin 7}
    (h : RimCertAt y u (quad a b c d)) : RimCertAt y (-u) (quad a d c b) := by
  have h' := h.toPts.reflect
  refine RimCertPts.atOf ?_
  have e : (fun i => (fun i => y (quad a b c d i)) (-i)) = fun i => y (quad a d c b i) := by
    funext i; rcases zmod4_cases i with rfl | rfl | rfl | rfl <;> rfl
  rw [e] at h'; exact h'

/-- A triangular rim read backwards: `tri a b c` at `u` is `tri a c b` at `−u`. -/
theorem RimCertAt.rev3 {y : Fin 7 → ℝ³} {u : ℝ³} {a b c : Fin 7}
    (h : RimCertAt y u (tri a b c)) : RimCertAt y (-u) (tri a c b) := by
  have h' := h.toPts.reflect
  refine RimCertPts.atOf ?_
  have e : (fun i => (fun i => y (tri a b c i)) (-i)) = fun i => y (tri a c b i) := by
    funext i; rcases zmod3_cases i with rfl | rfl | rfl <;> rfl
  rw [e] at h'; exact h'

/-! ### The region facts at the limit -/

/-- **The normal form of a point set is unique**: the eight parameters are functions of `y`. -/
theorem NF29.params_eq {y : Fin 7 → ℝ³} (N N' : NF29 y) :
    ![N.a0, N.b0, N.h0, N.a2, N.b2, N.h2, N.s, N.t] =
      ![N'.a0, N'.b0, N'.h0, N'.a2, N'.b2, N'.h2, N'.s, N'.t] := by
  have ho : N.o = y 1 := by rw [N.x1]; simp [nfP]
  have ho' : N'.o = y 1 := by rw [N'.x1]; simp [nfP]
  have e1 : N.E₁ = y 4 - y 1 := by rw [N.x4, N.x1]; simp [nfP]
  have e1' : N'.E₁ = y 4 - y 1 := by rw [N'.x4, N'.x1]; simp [nfP]
  have e2 : N.E₂ = y 5 - y 1 := by rw [N.x5, N.x1]; simp [nfP]
  have e2' : N'.E₂ = y 5 - y 1 := by rw [N'.x5, N'.x1]; simp [nfP]
  have e3 : N.E₃ = y 1 - y 3 := by rw [N.x3, N.x1]; simp [nfP]
  have e3' : N'.E₃ = y 1 - y 3 := by rw [N'.x3, N'.x1]; simp [nfP]
  have h0 := N.x0
  have h0' := N'.x0
  have h2 := N.x2
  have h2' := N'.x2
  have h6 := N.x6
  have h6' := N'.x6
  rw [ho, e1, e2, e3] at h0 h2 h6
  rw [ho', e1', e2', e3'] at h0' h2' h6'
  have hD : det3 (y 4 - y 1) (y 5 - y 1) (y 1 - y 3) ≠ 0 := by
    have := N.hD; rwa [e1, e2, e3] at this
  obtain ⟨a0, b0, c0⟩ := nfP_coeffs hD (h0.symm.trans h0')
  obtain ⟨a2, b2, c2⟩ := nfP_coeffs hD (h2.symm.trans h2')
  obtain ⟨s, t, -⟩ := nfP_coeffs hD (h6.symm.trans h6')
  have : N.h0 = N'.h0 := by linarith
  have : N.h2 = N'.h2 := by linarith
  simp only [a0, b0, a2, b2, s, t, *]

/-- **The closed region facts of a certificate, at the limit** (in the parameters of `x`): the
facts `Ex29.facts` of the approximants `K_n`, in the limit. -/
def Ex29.lim {x : Fin 7 → ℝ³} (N : NF29 x) : Ex29 → Prop
  | .none => True
  | .t1 => (0 ≤ -N.a2 * N.t + N.b2 * N.s ∧ N.h2 ≤ 1) ∧
      0 ≤ ⟪view29 x (.inr 0), view29 x (.inr 1)⟫
  | .t1o => (0 ≤ -N.a2 * N.t + N.b2 * N.s ∧ 1 ≤ N.h2) ∧
      ⟪view29 x (.inr 0), view29 x (.inr 3)⟫ ≤ 0
  | .t2 => N.h0 ≤ N.h2 ∧ N.h2 ≤ 1
  | .t2o => N.h0 ≤ 1 ∧ 1 ≤ N.h2

/-- **The facts of a frequent certificate pass to the limit** (`Ex29.lim`): the parameters of
the approximants converge to those of `x` and the inequalities are closed. -/
theorem Ex29.lim_of_freq (N : NF29 x) (K : ℕ → Fin 7 → ℝ³)
    (hK : ∀ m, Tendsto (fun n => K n m) atTop (𝓝 (x m))) (θs : ℕ → Fin 8 → ℝ)
    (hθs : Tendsto θs atTop (𝓝 ![N.a0, N.b0, N.h0, N.a2, N.b2, N.h2, N.s, N.t])) (e : Ex29)
    (h : ∃ᶠ n in atTop, e.facts (K n) ∧
      ∃ Nn : NF29 (K n), ![Nn.a0, Nn.b0, Nn.h0, Nn.a2, Nn.b2, Nn.h2, Nn.s, Nn.t] = θs n) :
    e.lim N := by
  have c : ∀ j, Tendsto (fun n => θs n j) atTop
      (𝓝 (![N.a0, N.b0, N.h0, N.a2, N.b2, N.h2, N.s, N.t] j)) := fun j =>
    ((continuous_apply j).tendsto _).comp hθs
  have c0 := c 0; have c1 := c 1; have c2 := c 2; have c3 := c 3; have c4 := c 4
  have c5 := c 5; have c6 := c 6; have c7 := c 7
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at c0 c1 c2 c3 c4 c5 c6 c7
  -- the parameters of any normal form of `K_n` are `θs n`
  have key : ∀ n, ∀ N' : NF29 (K n), ∀ Nn : NF29 (K n),
      ![Nn.a0, Nn.b0, Nn.h0, Nn.a2, Nn.b2, Nn.h2, Nn.s, Nn.t] = θs n →
      N'.a2 = θs n 3 ∧ N'.b2 = θs n 4 ∧ N'.h0 = θs n 2 ∧ N'.h2 = θs n 5 ∧ N'.s = θs n 6 ∧
        N'.t = θs n 7 := by
    intro n N' Nn hn
    have e := NF29.params_eq N' Nn
    rw [← hn]
    have e3 := congrFun e 3; have e4 := congrFun e 4; have e2 := congrFun e 2
    have e5 := congrFun e 5; have e6 := congrFun e 6; have e7 := congrFun e 7
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at e2 e3 e4 e5 e6 e7
    exact ⟨e3, e4, e2, e5, e6, e7⟩
  have lim0 : ∀ {f : ℕ → ℝ} {L : ℝ}, Tendsto f atTop (𝓝 L) → (∃ᶠ n in atTop, 0 ≤ f n) →
      0 ≤ L := fun hf hfr => le_of_tendsto_frequently tendsto_const_nhds hf hfr
  have limle : ∀ {f g : ℕ → ℝ} {L M : ℝ}, Tendsto f atTop (𝓝 L) → Tendsto g atTop (𝓝 M) →
      (∃ᶠ n in atTop, f n ≤ g n) → L ≤ M := fun hf hg hfr => le_of_tendsto_frequently hf hg hfr
  -- `-a2 t + b2 s` and `h2` at the approximants
  have hθ : ∀ n (N' : NF29 (K n)) (Nn : NF29 (K n)),
      ![Nn.a0, Nn.b0, Nn.h0, Nn.a2, Nn.b2, Nn.h2, Nn.s, Nn.t] = θs n →
      (0 ≤ -N'.a2 * N'.t + N'.b2 * N'.s → 0 ≤ -θs n 3 * θs n 7 + θs n 4 * θs n 6) ∧
      (N'.h0 ≤ N'.h2 → θs n 2 ≤ θs n 5) ∧ (N'.h2 ≤ 1 → θs n 5 ≤ 1) ∧
      (1 ≤ N'.h2 → 1 ≤ θs n 5) ∧ (N'.h0 ≤ 1 → θs n 2 ≤ 1) := by
    intro n N' Nn hn
    obtain ⟨k3, k4, k2, k5, k6, k7⟩ := key n N' Nn hn
    rw [k3, k4, k2, k5, k6, k7]
    exact ⟨id, id, id, id, id⟩
  cases e
  · exact trivial
  · -- t1
    refine ⟨⟨lim0 ((c3.neg.mul c7).add (c4.mul c6)) (h.mono fun n hn => ?_),
      limle c5 tendsto_const_nhds (h.mono fun n hn => ?_)⟩,
      le_of_tendsto_frequently tendsto_const_nhds
        ((tendsto_view29 hK (.inr 0)).inner (tendsto_view29 hK (.inr 1)))
        (h.mono fun n hn => hn.1.2)⟩
    · obtain ⟨⟨⟨N', hN'⟩, -⟩, Nn, hn'⟩ := hn
      exact (hθ n N' Nn hn').1 hN'.1
    · obtain ⟨⟨⟨N', hN'⟩, -⟩, Nn, hn'⟩ := hn
      exact (hθ n N' Nn hn').2.2.1 hN'.2
  · -- t1o
    refine ⟨⟨lim0 ((c3.neg.mul c7).add (c4.mul c6)) (h.mono fun n hn => ?_),
      limle tendsto_const_nhds c5 (h.mono fun n hn => ?_)⟩,
      le_of_tendsto_frequently ((tendsto_view29 hK (.inr 0)).inner (tendsto_view29 hK (.inr 3)))
        tendsto_const_nhds (h.mono fun n hn => hn.1.2)⟩
    · obtain ⟨⟨⟨N', hN'⟩, -⟩, Nn, hn'⟩ := hn
      exact (hθ n N' Nn hn').1 hN'.1
    · obtain ⟨⟨⟨N', hN'⟩, -⟩, Nn, hn'⟩ := hn
      exact (hθ n N' Nn hn').2.2.2.1 hN'.2
  · -- t2
    exact ⟨limle c2 c5 (h.mono fun n hn => by
        obtain ⟨⟨N', hN'⟩, Nn, hn'⟩ := hn
        exact (hθ n N' Nn hn').2.1 hN'.1),
      limle c5 tendsto_const_nhds (h.mono fun n hn => by
        obtain ⟨⟨N', hN'⟩, Nn, hn'⟩ := hn
        exact (hθ n N' Nn hn').2.2.1 hN'.2)⟩
  · -- t2o
    exact ⟨limle c2 tendsto_const_nhds (h.mono fun n hn => by
        obtain ⟨⟨N', hN'⟩, Nn, hn'⟩ := hn
        exact (hθ n N' Nn hn').2.2.2.2 hN'.1),
      limle tendsto_const_nhds c5 (h.mono fun n hn => by
        obtain ⟨⟨N', hN'⟩, Nn, hn'⟩ := hn
        exact (hθ n N' Nn hn').2.2.2.1 hN'.2)⟩

end Minimality

end
