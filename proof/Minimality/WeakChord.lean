module

public import Minimality.GenericLeaves
public import Minimality.SlideDS
public import Minimality.RCell24

/-!
# Eclipsed-tilt subsumption on triangle circles (`Task EC`, Carbon A59 Theorem 1.1)

Formalizes `WeakChordArc` and `lexAny_or_splitAny24_of_weakChordArc`: on any triangle facet `t ≠ 3`
of a Type 24 solid `F : S0xFac 9 s0x_S24 x`, the face-chord fields `hcyc`, `hin`, `hmid` at an
on-circle view `u`, together with `RobUni` (`k ≥ 4`), `DepthSepAt`, or injective depths (`k = 3`),
yield `LexAny F ∨ SplitAny24 F` at an eclipsed-tilt perturbation `w = ρ • (u + ε • η • F.N t + δ₂ • v)`.
Tested exactly on 92 M instances before the proof (FACENORM24 A59 TESTS); on samples its hypotheses already imply the
far-vertex and Lemma H fields, so it shrinks nothing measurable; use: shorter hypotheses.  `Hole24` excludes it
(`hole24_noWeakChord`, Type24HoleConfined.lean).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped RealInnerProductSpace Topology
open Finset Filter

@[expose] public section

namespace Minimality.GenPlus

open Minimality Minimality.H21 Minimality.FaceChord Minimality.Gen
open Minimality.T24.SAT Minimality.T24.RCell Minimality.LexCell
open Minimality.Split (StrictRimN SplitRows IsDepthSeparatedAt splitRows_of_isDepthSeparatedAt)

/-- A weak chord arc on a triangle facet `t`: the `FaceChordView` fields `hcyc`, `hin`, `hmid`
at a view `u` on circle `t`, the third vertex of `t` off the rim, and robust unimodality (`k ≥ 4`),
a depth-separated pair, or injective depths (`k = 3`); no far-vertex, Lemma H, or injectivity
field otherwise. -/
def WeakChordArc {N nf : ℕ} {S : Fin nf → Finset (Fin N)} {x : Fin N → ℝ³}
    (F : S0xFac nf S x) (t : Fin nf) : Prop :=
  ∃ (u : ℝ³) (k : ℕ) (_ : NeZero k) (r : ZMod k → Fin N) (a : ZMod k) (ρ : ℝ),
    ⟪F.N t, u⟫ = 0 ∧ 3 ≤ k ∧ Function.Injective r ∧ r a ∈ S t ∧ r (a + 1) ∈ S t ∧ ρ ≠ 0 ∧
    (∃ q ∈ S t, ∀ j, q ≠ r j) ∧
    (∀ i j, j ≠ i → j ≠ i + 1 →
      0 < ρ * det3 (x (r (i + 1)) - x (r i)) (x (r j) - x (r i)) u) ∧
    (∀ q, q ∉ S t → (∀ j, q ≠ r j) → ∀ i,
      0 < ρ * det3 (x (r (i + 1)) - x (r i)) (x q - x (r i)) u) ∧
    (∀ q ∈ S t, (∀ j, q ≠ r j) → ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      x q = x (r a) + s • (x (r (a + 1)) - x (r a)) + δ • u) ∧
    ((4 ≤ k ∧ RobUni (fun i => ⟪x (r i), u⟫)) ∨
      (∃ p q : ZMod k, DepthSepAt (fun i => x (r i)) u p q) ∨
      (k = 3 ∧ Function.Injective fun i => ⟪x (r i), u⟫))

/-! ### Elementary algebraic and continuity helpers -/

private lemma exists_forall_inner_ne_zero {m : ℕ} (N : Fin m → ℝ³) (hN : ∀ s, N s ≠ 0) :
    ∃ v : ℝ³, ∀ s, ⟪N s, v⟫ ≠ 0 := by
  let p : Fin m → Polynomial ℝ := fun s =>
    Polynomial.C (N s 0) + Polynomial.C (N s 1) * Polynomial.X +
      Polynomial.C (N s 2) * Polynomial.X ^ 2
  have hp_ne : ∀ s, p s ≠ 0 := fun s hp => by
    apply hN s
    ext j
    have h0 := congr_arg (fun q : Polynomial ℝ => q.coeff 0) hp
    have h1 := congr_arg (fun q : Polynomial ℝ => q.coeff 1) hp
    have h2 := congr_arg (fun q : Polynomial ℝ => q.coeff 2) hp
    simp only [p, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at h0 h1 h2
    simp only [↓reduceIte, zero_ne_one, one_ne_zero, OfNat.zero_ne_ofNat, OfNat.ofNat_ne_zero,
      OfNat.one_ne_ofNat, OfNat.ofNat_ne_one, add_zero, zero_add] at h0 h1 h2
    fin_cases j <;> assumption
  have hdeg : ∀ s, (p s).roots.card ≤ 2 := fun s => by
    refine le_trans (Polynomial.card_roots' (p s)) ?_
    refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
    · refine le_trans (Polynomial.natDegree_add_le _ _) (max_le (by simp) ?_)
      exact le_trans (Polynomial.natDegree_C_mul_le _ _) (by simp)
    · exact le_trans (Polynomial.natDegree_C_mul_le _ _) (by simp)
  let bad : Finset ℝ := Finset.univ.biUnion fun s => (p s).roots.toFinset
  have hbad_card : bad.card ≤ 2 * m := by
    refine le_trans Finset.card_biUnion_le ?_
    calc ∑ s : Fin m, (p s).roots.toFinset.card
        ≤ ∑ s : Fin m, (p s).roots.card := Finset.sum_le_sum fun s _ => Multiset.toFinset_card_le _
      _ ≤ ∑ _s : Fin m, 2 := Finset.sum_le_sum fun s _ => hdeg s
      _ = 2 * m := by simp [mul_comm]
  let cand : Finset ℝ := (Finset.range (2 * m + 1)).image (fun n : ℕ => (n : ℝ))
  have hcand_card : cand.card = 2 * m + 1 := by
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
  have hdiff : (cand \ bad).Nonempty := by
    rw [← Finset.card_pos]
    have := Finset.card_sdiff_add_card_inter cand bad
    have hle : (cand ∩ bad).card ≤ bad.card := Finset.card_le_card Finset.inter_subset_right
    omega
  obtain ⟨t, ht⟩ := hdiff
  rw [Finset.mem_sdiff] at ht
  refine ⟨!₂[1, t, t ^ 2], fun s heq => ht.2 ?_⟩
  refine Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ s, Multiset.mem_toFinset.mpr ?_⟩
  rw [Polynomial.mem_roots (hp_ne s)]
  simp only [p, Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_pow]
  have heq' : N s 0 * 1 + N s 1 * t + N s 2 * t ^ 2 = 0 := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, Fin.sum_univ_three, dotProduct,
      star_trivial] at heq
    have h0 : (![1, t, t ^ 2] : Fin 3 → ℝ) 0 = 1 := rfl
    have h1 : (![1, t, t ^ 2] : Fin 3 → ℝ) 1 = t := rfl
    have h2 : (![1, t, t ^ 2] : Fin 3 → ℝ) 2 = t ^ 2 := rfl
    rw [h0, h1, h2] at heq
    linarith
  linarith

private lemma robUni_eventually {k : ℕ} [NeZero k] (X : ZMod k → ℝ³) (u e : ℝ³)
    (hR : RobUni (fun i => ⟪X i, u⟫)) :
    ∀ᶠ t in 𝓝 (0 : ℝ), RobUni (fun i => ⟪X i, u + t • e⟫) := by
  have hlin : ∀ i : ZMod k, ∀ t : ℝ, ⟪X i, u + t • e⟫ = ⟪X i, u⟫ + t * ⟪X i, e⟫ := fun i t => by
    rw [inner_add_right, real_inner_smul_right]
  have h4 : ∀ (B : ZMod k) (b c d : ℕ), 0 < b → b < c → c < d → d < k →
      ∀ᶠ t in 𝓝 (0 : ℝ),
        ⟪X B, u + t • e⟫ < ⟪X (B + b), u + t • e⟫ ∨
        ⟪X (B + c), u + t • e⟫ < ⟪X (B + b), u + t • e⟫ ∨
        ⟪X B, u + t • e⟫ < ⟪X (B + d), u + t • e⟫ ∨
        ⟪X (B + c), u + t • e⟫ < ⟪X (B + d), u + t • e⟫ := by
    intro B b c d hb hbc hcd hd
    have hlt_ev : ∀ i j : ZMod k, ⟪X i, u⟫ < ⟪X j, u⟫ →
        ∀ᶠ t in 𝓝 (0 : ℝ), ⟪X i, u + t • e⟫ < ⟪X j, u + t • e⟫ := by
      intro i j hij
      have hc : Continuous fun t : ℝ => ⟪X j, u + t • e⟫ - ⟪X i, u + t • e⟫ := by
        simp_rw [hlin]; fun_prop
      have h0 : 0 < (fun t : ℝ => ⟪X j, u + t • e⟫ - ⟪X i, u + t • e⟫) 0 := by
        simp; linarith
      filter_upwards [(hc.tendsto 0).eventually_const_lt h0] with t ht
      linarith
    have h4' : ⟪X B, u⟫ < ⟪X (B + b), u⟫ ∨ ⟪X (B + c), u⟫ < ⟪X (B + b), u⟫ ∨
        ⟪X B, u⟫ < ⟪X (B + d), u⟫ ∨ ⟪X (B + c), u⟫ < ⟪X (B + d), u⟫ := by
      by_contra hnot
      push Not at hnot
      exact hR B b c d hb hbc hcd hd ⟨hnot.1, hnot.2.1, hnot.2.2.1, hnot.2.2.2⟩
    rcases h4' with h | h | h | h
    · exact (hlt_ev _ _ h).mono fun _ => Or.inl
    · exact (hlt_ev _ _ h).mono fun _ ht => Or.inr (Or.inl ht)
    · exact (hlt_ev _ _ h).mono fun _ ht => Or.inr (Or.inr (Or.inl ht))
    · exact (hlt_ev _ _ h).mono fun _ ht => Or.inr (Or.inr (Or.inr ht))
  have hall : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ (B : ZMod k) (b c d : ℕ),
      0 < b → b < c → c < d → d < k →
        ⟪X B, u + t • e⟫ < ⟪X (B + b), u + t • e⟫ ∨
        ⟪X (B + c), u + t • e⟫ < ⟪X (B + b), u + t • e⟫ ∨
        ⟪X B, u + t • e⟫ < ⟪X (B + d), u + t • e⟫ ∨
        ⟪X (B + c), u + t • e⟫ < ⟪X (B + d), u + t • e⟫ := by
    rw [eventually_all]
    intro B
    have hb_fin : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ b c d : Fin k,
        0 < b.val → b.val < c.val → c.val < d.val → d.val < k →
          ⟪X B, u + t • e⟫ < ⟪X (B + b.val), u + t • e⟫ ∨
          ⟪X (B + c.val), u + t • e⟫ < ⟪X (B + b.val), u + t • e⟫ ∨
          ⟪X B, u + t • e⟫ < ⟪X (B + d.val), u + t • e⟫ ∨
          ⟪X (B + c.val), u + t • e⟫ < ⟪X (B + d.val), u + t • e⟫ := by
      refine eventually_all.mpr fun b => eventually_all.mpr fun c => eventually_all.mpr fun d => ?_
      by_cases hcond : 0 < b.val ∧ b.val < c.val ∧ c.val < d.val ∧ d.val < k
      · filter_upwards [h4 B b.val c.val d.val hcond.1 hcond.2.1 hcond.2.2.1 hcond.2.2.2] with t ht _ _ _ _
        exact ht
      · filter_upwards with t hb' hbc' hcd' hd'
        exact absurd ⟨hb', hbc', hcd', hd'⟩ hcond
    filter_upwards [hb_fin] with t ht b c d hb hbc hcd hd
    exact ht ⟨b, by omega⟩ ⟨c, by omega⟩ ⟨d, by omega⟩ hb hbc hcd hd
  filter_upwards [hall] with t ht B b c d hb hbc hcd hd hnot
  rcases ht B b c d hb hbc hcd hd with h | h | h | h <;> linarith [hnot.1, hnot.2.1, hnot.2.2.1, hnot.2.2.2]

private lemma robUni_smul {k : ℕ} [NeZero k] {z : ZMod k → ℝ} {ρ : ℝ} (hρ : ρ ≠ 0)
    (hR : RobUni z) : RobUni (fun i => ρ * z i) := by
  rcases lt_or_gt_of_ne hρ with hn | hp
  · intro B b c d hb hbc hcd hd hnot
    have h1 : z B ≤ z (B + b) := by nlinarith [hnot.1]
    have h2 : z (B + c) ≤ z (B + b) := by nlinarith [hnot.2.1]
    have h3 : z B ≤ z (B + d) := by nlinarith [hnot.2.2.1]
    have h4 : z (B + c) ≤ z (B + d) := by nlinarith [hnot.2.2.2]
    have e1 : B + (b : ZMod k) + ((c - b : ℕ) : ZMod k) = B + (c : ZMod k) := by
      rw [add_assoc, ← Nat.cast_add, Nat.add_sub_cancel' hbc.le]
    have e2 : B + (b : ZMod k) + ((d - b : ℕ) : ZMod k) = B + (d : ZMod k) := by
      rw [add_assoc, ← Nat.cast_add, Nat.add_sub_cancel' (hbc.trans hcd).le]
    have e3 : B + (b : ZMod k) + ((k - b : ℕ) : ZMod k) = B := by
      rw [add_assoc, ← Nat.cast_add, Nat.add_sub_cancel' (by omega), ZMod.natCast_self, add_zero]
    apply hR (B + b) (c - b) (d - b) (k - b) (by omega) (by omega) (by omega) (by omega)
    rw [e1, e2, e3]
    exact ⟨h2, h4, h1, h3⟩
  · intro B b c d hb hbc hcd hd hnot
    exact hR B b c d hb hbc hcd hd
      ⟨by nlinarith [hnot.1], by nlinarith [hnot.2.1], by nlinarith [hnot.2.2.1], by nlinarith [hnot.2.2.2]⟩

private lemma robUniLex_of_robUni {k : ℕ} {z : ZMod k → ℝ} (hR : RobUni z) :
    RobUniLex (fun i => (z i, (0 : ℝ), (0 : ℝ))) := by
  intro B b c d hb hbc hcd hd
  by_contra hnot
  push Not at hnot
  apply hR B b c d hb hbc hcd hd
  have hle : ∀ x y : ℝ, ¬ LexLt3 (x, (0 : ℝ), (0 : ℝ)) (y, (0 : ℝ), (0 : ℝ)) → y ≤ x := by
    intro x y h
    by_contra hlt
    exact h (Or.inl (sub_pos.mpr (not_le.mp hlt)))
  exact ⟨hle _ _ hnot.1, hle _ _ hnot.2.1, hle _ _ hnot.2.2.1, hle _ _ hnot.2.2.2⟩

private lemma depthSepAt_of_k3 {X : ZMod 3 → ℝ³} {u : ℝ³} {ρ : ℝ} (_hρ : ρ ≠ 0)
    (hcyc : ∀ i j : ZMod 3, j ≠ i → j ≠ i + 1 → 0 < ρ * det3 (X (i + 1) - X i) (X j - X i) u)
    (hinj : Function.Injective (fun i => ⟪X i, u⟫)) :
    ∃ p q : ZMod 3, DepthSepAt X u p q := by
  let z : ZMod 3 → ℝ := fun i => ⟪X i, u⟫
  have hne01 : z 0 ≠ z 1 := fun h => by have := hinj h; revert this; decide
  have hne02 : z 0 ≠ z 2 := fun h => by have := hinj h; revert this; decide
  have hne12 : z 1 ≠ z 2 := fun h => by have := hinj h; revert this; decide
  have hmid_exists : ∃ q : ZMod 3,
      (z q < z (q + 1) ∧ z (q + 2) < z q) ∨ (z (q + 1) < z q ∧ z q < z (q + 2)) := by
    dsimp [z] at hne01 hne02 hne12 ⊢
    rcases lt_or_gt_of_ne hne01 with h01 | h10 <;>
    rcases lt_or_gt_of_ne hne02 with h02 | h20 <;>
    rcases lt_or_gt_of_ne hne12 with h12 | h21
    · exact ⟨1, Or.inl ⟨by rw [show (1 + 1 : ZMod 3) = 2 from rfl]; linarith,
        by rw [show (1 + 2 : ZMod 3) = 0 from rfl]; linarith⟩⟩
    · exact ⟨2, Or.inr ⟨by rw [show (2 + 1 : ZMod 3) = 0 from rfl]; linarith,
        by rw [show (2 + 2 : ZMod 3) = 1 from rfl]; linarith⟩⟩
    · exfalso; linarith
    · exact ⟨0, Or.inl ⟨h01, h20⟩⟩
    · exact ⟨0, Or.inr ⟨h10, h02⟩⟩
    · exfalso; linarith
    · exact ⟨2, Or.inl ⟨by rw [show (2 + 1 : ZMod 3) = 0 from rfl]; linarith,
        by rw [show (2 + 2 : ZMod 3) = 1 from rfl]; linarith⟩⟩
    · exact ⟨1, Or.inr ⟨by rw [show (1 + 1 : ZMod 3) = 2 from rfl]; linarith,
        by rw [show (1 + 2 : ZMod 3) = 0 from rfl]; linarith⟩⟩
  obtain ⟨q, hq⟩ := hmid_exists
  refine ⟨q + 1, q, ?_, ?_⟩
  · intro j hj
    have hqp : q ≠ q + 1 := by rcases q with ⟨q, hq'⟩; interval_cases q <;> intro h <;> cases h
    have hqp1 : q ≠ (q + 1) + 1 := by rcases q with ⟨q, hq'⟩; interval_cases q <;> intro h <;> cases h
    have hdet_ne : det3 (X ((q + 1) + 1) - X (q + 1)) (X q - X (q + 1)) u ≠ 0 := by
      intro h0; have := hcyc (q + 1) q hqp hqp1; rw [h0, mul_zero] at this; exact lt_irrefl _ this
    have hj_cases : j = q + 1 ∨ j = (q + 1) + 1 := by
      rcases q with ⟨q, hq'⟩; rcases j with ⟨j, hj'⟩
      interval_cases q <;> interval_cases j <;> first | exact absurd rfl hj | (left; rfl) | (right; rfl)
    rcases hj_cases with rfl | rfl
    · have hswap : det3 (X ((q + 1) + 1) - X (q + 1)) (X (q + 1) - X q) u =
          -det3 (X ((q + 1) + 1) - X (q + 1)) (X q - X (q + 1)) u := by
        simp only [det3_expand, PiLp.sub_apply]; ring
      rw [hswap]
      nlinarith [sq_pos_of_ne_zero hdet_ne]
    · have hswap : det3 (X ((q + 1) + 1) - X (q + 1)) (X ((q + 1) + 1) - X q) u =
          -det3 (X ((q + 1) + 1) - X (q + 1)) (X q - X (q + 1)) u := by
        simp only [det3_expand, PiLp.sub_apply]; ring
      rw [hswap]
      nlinarith [sq_pos_of_ne_zero hdet_ne]
  · have hval : ((q + 1 : ZMod 3) - q).val = 1 := by
      rw [add_sub_cancel_left]; decide
    rw [hval]
    rcases hq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      refine ⟨fun s hs1 hs2 => ?_, fun s hs1 hs2 => ?_⟩
      · have hs : s = 1 := by omega
        subst hs; simpa using h1
      · have hs : s = 2 := by omega
        subst hs; simpa using h2
    · right
      refine ⟨fun s hs1 hs2 => ?_, fun s hs1 hs2 => ?_⟩
      · have hs : s = 1 := by omega
        subst hs; simpa using h1
      · have hs : s = 2 := by omega
        subst hs; simpa using h2

private lemma split_det3_eq (a b c : ℝ³) : Minimality.Split.det3 a b c = det3 a b c := by
  simp only [Minimality.Split.det3, det3_expand]

private lemma isDepthSeparatedAt_of_depthSepAt {k : ℕ} [NeZero k] (hk : 3 ≤ k) {X : ZMod k → ℝ³} {w : ℝ³}
    {a c : ZMod k} (hds : DepthSepAt X w a c)
    (hrim : ∀ j, j ≠ a → j ≠ a + 1 → 0 < det3 (X (a + 1) - X a) (X j - X a) w) :
    c ≠ a ∧ c ≠ a + 1 ∧ IsDepthSeparatedAt X w a c := by
  have : Fact (1 < k) := ⟨by omega⟩
  obtain ⟨hdet, hz⟩ := hds
  have ha1 : a + 1 ≠ a := by
    intro h
    have h1 : (1 : ZMod k) = 0 := by linear_combination h
    have hval := congr_arg ZMod.val h1
    rw [ZMod.val_one, ZMod.val_zero] at hval
    omega
  have hca : c ≠ a := by
    intro hc_eq
    rw [hc_eq] at hdet
    have h0 := hdet (a + 1) ha1
    rw [sub_self, show det3 (X (a + 1) - X a) 0 w = 0 by simp [det3_expand], mul_zero] at h0
    exact lt_irrefl 0 h0
  have hca1 : c ≠ a + 1 := by
    intro hc_eq
    rw [hc_eq] at hdet
    have h0 := hdet a ha1.symm
    have hz0 : det3 (X (a + 1) - X a) (X (a + 1) - X a) w = 0 := by simp [det3_expand]; ring
    rw [hz0, mul_zero] at h0
    exact lt_irrefl 0 h0
  refine ⟨hca, hca1, fun i hi => ?_, hz⟩
  have hpos := hrim c hca hca1
  have hneg : det3 (X (a + 1) - X a) (X i - X c) w < 0 := by
    nlinarith [hdet i hi]
  have hid : det3 (X (a + 1) - X a) w (X i) - det3 (X (a + 1) - X a) w (X c) =
      -det3 (X (a + 1) - X a) (X i - X c) w := by
    simp only [det3_expand, PiLp.sub_apply]; ring
  have hid' : Minimality.Split.det3 (X (a + 1) - X a) w (X c) <
      Minimality.Split.det3 (X (a + 1) - X a) w (X i) := by
    rw [split_det3_eq, split_det3_eq]
    linarith
  exact hid'

/-! ### Type-24 rim-to-facets lemma (`StrictRimN` forces `S0xCycUD` and `S0xCycOK`) -/

private lemma not_strictRim_of_radon3 {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (w : ℝ³)
    (p q a b c : Fin 7) (f1 f2 f3 : Fin 9)
    (hp1 : p ∈ s0x_S24 f1) (ha1 : a ∈ s0x_S24 f1) (hb1 : b ∈ s0x_S24 f1)
    (hc1 : c ∉ s0x_S24 f1) (hq1 : q ∉ s0x_S24 f1)
    (hp2 : p ∈ s0x_S24 f2) (ha2 : a ∈ s0x_S24 f2) (hc2 : c ∈ s0x_S24 f2)
    (hb2 : b ∉ s0x_S24 f2) (hq2 : q ∉ s0x_S24 f2)
    (hp3 : p ∈ s0x_S24 f3) (hb3 : b ∈ s0x_S24 f3) (hc3 : c ∈ s0x_S24 f3)
    (ha3 : a ∉ s0x_S24 f3) (hq3 : q ∉ s0x_S24 f3)
    (hA : 0 < det3 (x q - x p) (x a - x p) w)
    (hB : 0 < det3 (x q - x p) (x b - x p) w)
    (hC : 0 < det3 (x q - x p) (x c - x p) w) : False := by
  let v : Fin 4 → ℝ³ := ![x a - x p, x b - x p, x c - x p, x q - x p]
  have hdep : ¬ LinearIndependent ℝ v := by
    intro hli
    have hcard := hli.fintype_card_le_finrank
    rw [Fintype.card_fin, finrank_euclideanSpace_fin] at hcard
    omega
  rw [Fintype.not_linearIndependent_iff] at hdep
  obtain ⟨g, hg0, hne⟩ := hdep
  have hsum : g 0 • (x a - x p) + g 1 • (x b - x p) + g 2 • (x c - x p) + g 3 • (x q - x p) = 0 := by
    simpa [v, Fin.sum_univ_four, add_assoc] using hg0
  have hf1 : g 2 * F.f f1 (x c) + g 3 * F.f f1 (x q) = 0 := by
    have h := congr_arg (fun z : ℝ³ => ⟪F.N f1, z⟫) hsum
    simp only [inner_zero_right, inner_add_right, real_inner_smul_right, F.inner_sub,
      F.zero f1 p hp1, F.zero f1 a ha1, F.zero f1 b hb1, sub_zero, mul_zero, zero_add] at h
    exact h
  have hf2 : g 1 * F.f f2 (x b) + g 3 * F.f f2 (x q) = 0 := by
    have h := congr_arg (fun z : ℝ³ => ⟪F.N f2, z⟫) hsum
    simp only [inner_zero_right, inner_add_right, real_inner_smul_right, F.inner_sub,
      F.zero f2 p hp2, F.zero f2 a ha2, F.zero f2 c hc2, sub_zero, mul_zero, zero_add, add_zero] at h
    exact h
  have hf3 : g 0 * F.f f3 (x a) + g 3 * F.f f3 (x q) = 0 := by
    have h := congr_arg (fun z : ℝ³ => ⟪F.N f3, z⟫) hsum
    simp only [inner_zero_right, inner_add_right, real_inner_smul_right, F.inner_sub,
      F.zero f3 p hp3, F.zero f3 b hb3, F.zero f3 c hc3, sub_zero, mul_zero, add_zero] at h
    exact h
  have hc1' : F.f f1 (x c) < 0 := F.neg f1 c hc1
  have hq1' : F.f f1 (x q) < 0 := F.neg f1 q hq1
  have hb2' : F.f f2 (x b) < 0 := F.neg f2 b hb2
  have hq2' : F.f f2 (x q) < 0 := F.neg f2 q hq2
  have ha3' : F.f f3 (x a) < 0 := F.neg f3 a ha3
  have hq3' : F.f f3 (x q) < 0 := F.neg f3 q hq3
  have hg3 : g 3 ≠ 0 := by
    intro hg30
    rw [hg30, zero_mul, add_zero] at hf1 hf2 hf3
    have hg0' : g 0 = 0 := (mul_eq_zero.mp hf3).resolve_right ha3'.ne
    have hg1' : g 1 = 0 := (mul_eq_zero.mp hf2).resolve_right hb2'.ne
    have hg2' : g 2 = 0 := (mul_eq_zero.mp hf1).resolve_right hc1'.ne
    obtain ⟨i, hi⟩ := hne
    fin_cases i <;> contradiction
  have hdet_sum : g 0 * det3 (x q - x p) (x a - x p) w + g 1 * det3 (x q - x p) (x b - x p) w +
      g 2 * det3 (x q - x p) (x c - x p) w = 0 := by
    have hd := congr_arg (fun z : ℝ³ => det3 (x q - x p) z w) hsum
    have hqq : det3 (x q - x p) (x q - x p) w = 0 := by simp [det3_expand]; ring
    have hlin : det3 (x q - x p) (g 0 • (x a - x p) + g 1 • (x b - x p) +
        g 2 • (x c - x p) + g 3 • (x q - x p)) w =
        g 0 * det3 (x q - x p) (x a - x p) w + g 1 * det3 (x q - x p) (x b - x p) w +
        g 2 * det3 (x q - x p) (x c - x p) w + g 3 * det3 (x q - x p) (x q - x p) w := by
      simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    have h0 : det3 (x q - x p) 0 w = 0 := by simp [det3_expand]
    rw [hlin, hqq, mul_zero, add_zero, h0] at hd
    exact hd
  rcases lt_or_gt_of_ne hg3 with hn | hp
  · have hg0p : 0 < g 0 := by nlinarith
    have hg1p : 0 < g 1 := by nlinarith
    have hg2p : 0 < g 2 := by nlinarith
    nlinarith
  · have hg0n : g 0 < 0 := by nlinarith
    have hg1n : g 1 < 0 := by nlinarith
    have hg2n : g 2 < 0 := by nlinarith
    nlinarith

private lemma not_strictRim_of_quadDiag {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (w : ℝ³)
    (p q a b : Fin 7) (f1 f2 : Fin 9)
    (hp3 : p ∈ s0x_S24 3) (hq3 : q ∈ s0x_S24 3) (ha3 : a ∈ s0x_S24 3) (hb3 : b ∈ s0x_S24 3)
    (hp1 : p ∈ s0x_S24 f1) (hb1 : b ∈ s0x_S24 f1) (ha1 : a ∉ s0x_S24 f1) (hq1 : q ∉ s0x_S24 f1)
    (hp2 : p ∈ s0x_S24 f2) (ha2 : a ∈ s0x_S24 f2) (hb2 : b ∉ s0x_S24 f2) (hq2 : q ∉ s0x_S24 f2)
    (hA : 0 < det3 (x q - x p) (x a - x p) w)
    (hB : 0 < det3 (x q - x p) (x b - x p) w) : False := by
  have hN3 : F.N 3 ≠ 0 := by
    intro h0
    obtain ⟨j, i, hj, hi⟩ := s24_off 3
    have := F.inner_sub 3 i j
    rw [h0, inner_zero_left, F.zero 3 j hj, sub_zero] at this
    linarith [F.neg 3 i hi]
  let L : ℝ³ →ₗ[ℝ] ℝ := innerSL ℝ (F.N 3)
  have hker : Module.finrank ℝ (LinearMap.ker L) = 2 := by
    have hrange : LinearMap.range L = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro r
      refine ⟨(r / ⟪F.N 3, F.N 3⟫) • F.N 3, ?_⟩
      have hnn : ⟪F.N 3, F.N 3⟫ ≠ 0 := fun h => hN3 (inner_self_eq_zero.mp h)
      change ⟪F.N 3, (r / ⟪F.N 3, F.N 3⟫) • F.N 3⟫ = r
      rw [real_inner_smul_right]
      exact div_mul_cancel₀ _ hnn
    have hrk := LinearMap.finrank_range_add_finrank_ker L
    rw [hrange, finrank_top, finrank_euclideanSpace_fin] at hrk
    have : Module.finrank ℝ ℝ = 1 := Module.finrank_self ℝ
    omega
  have hmem : ∀ z ∈ s0x_S24 3, x z - x p ∈ LinearMap.ker L := fun z hz => by
    change ⟪F.N 3, x z - x p⟫ = 0
    rw [F.inner_sub, F.zero 3 z hz, F.zero 3 p hp3, sub_self]
  let v : Fin 3 → LinearMap.ker L :=
    ![⟨x a - x p, hmem a ha3⟩, ⟨x b - x p, hmem b hb3⟩, ⟨x q - x p, hmem q hq3⟩]
  have hdep : ¬ LinearIndependent ℝ v := by
    intro hli
    have hcard := hli.fintype_card_le_finrank
    rw [Fintype.card_fin, hker] at hcard
    omega
  rw [Fintype.not_linearIndependent_iff] at hdep
  obtain ⟨g, hg0, hne⟩ := hdep
  have hsum : g 0 • (x a - x p) + g 1 • (x b - x p) + g 2 • (x q - x p) = 0 := by
    have h := congr_arg Subtype.val hg0
    simpa [v, Fin.sum_univ_three, add_assoc] using h
  have hf1 : g 0 * F.f f1 (x a) + g 2 * F.f f1 (x q) = 0 := by
    have h := congr_arg (fun z : ℝ³ => ⟪F.N f1, z⟫) hsum
    simp only [inner_zero_right, inner_add_right, real_inner_smul_right, F.inner_sub,
      F.zero f1 p hp1, F.zero f1 b hb1, sub_zero, mul_zero, add_zero] at h
    exact h
  have hf2 : g 1 * F.f f2 (x b) + g 2 * F.f f2 (x q) = 0 := by
    have h := congr_arg (fun z : ℝ³ => ⟪F.N f2, z⟫) hsum
    simp only [inner_zero_right, inner_add_right, real_inner_smul_right, F.inner_sub,
      F.zero f2 p hp2, F.zero f2 a ha2, sub_zero, mul_zero, zero_add] at h
    exact h
  have ha1' : F.f f1 (x a) < 0 := F.neg f1 a ha1
  have hq1' : F.f f1 (x q) < 0 := F.neg f1 q hq1
  have hb2' : F.f f2 (x b) < 0 := F.neg f2 b hb2
  have hq2' : F.f f2 (x q) < 0 := F.neg f2 q hq2
  have hg2 : g 2 ≠ 0 := by
    intro hg20
    rw [hg20, zero_mul, add_zero] at hf1 hf2
    have hg0' : g 0 = 0 := (mul_eq_zero.mp hf1).resolve_right ha1'.ne
    have hg1' : g 1 = 0 := (mul_eq_zero.mp hf2).resolve_right hb2'.ne
    obtain ⟨i, hi⟩ := hne
    fin_cases i <;> contradiction
  have hdet_sum : g 0 * det3 (x q - x p) (x a - x p) w + g 1 * det3 (x q - x p) (x b - x p) w = 0 := by
    have hd := congr_arg (fun z : ℝ³ => det3 (x q - x p) z w) hsum
    have hqq : det3 (x q - x p) (x q - x p) w = 0 := by simp [det3_expand]; ring
    have hlin : det3 (x q - x p) (g 0 • (x a - x p) + g 1 • (x b - x p) + g 2 • (x q - x p)) w =
        g 0 * det3 (x q - x p) (x a - x p) w + g 1 * det3 (x q - x p) (x b - x p) w +
        g 2 * det3 (x q - x p) (x q - x p) w := by
      simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    have h0 : det3 (x q - x p) 0 w = 0 := by simp [det3_expand]
    rw [hlin, hqq, mul_zero, add_zero, h0] at hd
    exact hd
  rcases lt_or_gt_of_ne hg2 with hn | hp
  · have hg0p : 0 < g 0 := by nlinarith
    have hg1p : 0 < g 1 := by nlinarith
    nlinarith
  · have hg0n : g 0 < 0 := by nlinarith
    have hg1n : g 1 < 0 := by nlinarith
    nlinarith

private lemma inner_det3_perp_id (n E Vb Va w : ℝ³) (hE : ⟪n, E⟫ = 0) (hVb : ⟪n, Vb⟫ = 0) :
    ⟪n, Va⟫ * det3 E Vb w = ⟪n, w⟫ * det3 E Vb Va := by
  have hE' : n 0 * E 0 + n 1 * E 1 + n 2 * E 2 = 0 := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, Fin.sum_univ_three, dotProduct, star_trivial] at hE
    linarith
  have hVb' : n 0 * Vb 0 + n 1 * Vb 1 + n 2 * Vb 2 = 0 := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, Fin.sum_univ_three, dotProduct, star_trivial] at hVb
    linarith
  simp only [EuclideanSpace.inner_eq_star_dotProduct, Fin.sum_univ_three, dotProduct, star_trivial, det3_expand]
  linear_combination
    (Va 0 * (Vb 1 * w 2 - Vb 2 * w 1) + Va 1 * (Vb 2 * w 0 - Vb 0 * w 2) +
      Va 2 * (Vb 0 * w 1 - Vb 1 * w 0)) * hE' -
    (Va 0 * (E 1 * w 2 - E 2 * w 1) + Va 1 * (E 2 * w 0 - E 0 * w 2) +
      Va 2 * (E 0 * w 1 - E 1 * w 0)) * hVb'

private lemma opp_signs_of_edge {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (w : ℝ³)
    (p q va vb : Fin 7) (a b : Fin 9)
    (hpa : p ∈ s0x_S24 a) (hqa : q ∈ s0x_S24 a) (hvba : vb ∈ s0x_S24 a) (hvaa : va ∉ s0x_S24 a)
    (hpb : p ∈ s0x_S24 b) (hqb : q ∈ s0x_S24 b) (hvab : va ∈ s0x_S24 b) (hvbb : vb ∉ s0x_S24 b)
    (h1 : 0 < det3 (x q - x p) (x va - x p) w) (h2 : 0 < det3 (x q - x p) (x vb - x p) w) :
    ⟪F.N a, w⟫ * ⟪F.N b, w⟫ < 0 := by
  have haE : ⟪F.N a, x q - x p⟫ = 0 := by rw [F.inner_sub, F.zero a q hqa, F.zero a p hpa, sub_self]
  have haVb : ⟪F.N a, x vb - x p⟫ = 0 := by rw [F.inner_sub, F.zero a vb hvba, F.zero a p hpa, sub_self]
  have haVa : ⟪F.N a, x va - x p⟫ < 0 := by
    rw [F.inner_sub, F.zero a p hpa, sub_zero]; exact F.neg a va hvaa
  have hbE : ⟪F.N b, x q - x p⟫ = 0 := by rw [F.inner_sub, F.zero b q hqb, F.zero b p hpb, sub_self]
  have hbVa : ⟪F.N b, x va - x p⟫ = 0 := by rw [F.inner_sub, F.zero b va hvab, F.zero b p hpb, sub_self]
  have hbVb : ⟪F.N b, x vb - x p⟫ < 0 := by
    rw [F.inner_sub, F.zero b p hpb, sub_zero]; exact F.neg b vb hvbb
  have idA := inner_det3_perp_id (F.N a) (x q - x p) (x vb - x p) (x va - x p) w haE haVb
  have idB := inner_det3_perp_id (F.N b) (x q - x p) (x va - x p) (x vb - x p) w hbE hbVa
  have hswap : det3 (x q - x p) (x va - x p) (x vb - x p) =
      -det3 (x q - x p) (x vb - x p) (x va - x p) := det3_swap23 _ _ _
  have hLHS : 0 < (⟪F.N a, x va - x p⟫ * det3 (x q - x p) (x vb - x p) w) *
      (⟪F.N b, x vb - x p⟫ * det3 (x q - x p) (x va - x p) w) :=
    mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos haVa h2) (mul_neg_of_neg_of_pos hbVb h1)
  have hRHS : (⟪F.N a, w⟫ * det3 (x q - x p) (x vb - x p) (x va - x p)) *
      (⟪F.N b, w⟫ * det3 (x q - x p) (x va - x p) (x vb - x p)) =
      -(⟪F.N a, w⟫ * ⟪F.N b, w⟫) * (det3 (x q - x p) (x vb - x p) (x va - x p)) ^ 2 := by
    rw [hswap]; ring
  rw [idA, idB, hRHS] at hLHS
  nlinarith [sq_nonneg (det3 (x q - x p) (x vb - x p) (x va - x p))]

private def radon3Tab : Fin 3 → Fin 7 × Fin 7 × Fin 7 × Fin 9 × Fin 9 × Fin 9
  | 0 => (0, 2, 6, 0, 1, 5)
  | 1 => (0, 3, 6, 3, 4, 8)
  | 2 => (0, 2, 3, 2, 3, 6)

set_option synthInstance.maxSize 2048 in
private lemma s24_edge_classify (p q : Fin 7) (hpq : p ≠ q) :
    (∃ a b : Fin 9, ∃ va vb : Fin 7,
      p ∈ s0x_S24 a ∧ q ∈ s0x_S24 a ∧ vb ∈ s0x_S24 a ∧ va ∉ s0x_S24 a ∧
      p ∈ s0x_S24 b ∧ q ∈ s0x_S24 b ∧ va ∈ s0x_S24 b ∧ vb ∉ s0x_S24 b ∧
      (∀ v : Fin 7, v ≠ p → v ≠ q → v ∉ s0x_S24 a ∨ v ∉ s0x_S24 b) ∧
      va ≠ p ∧ va ≠ q ∧ vb ≠ p ∧ vb ≠ q) ∨
    (∃ a b : Fin 7, ∃ f1 f2 : Fin 9,
      p ∈ s0x_S24 3 ∧ q ∈ s0x_S24 3 ∧ a ∈ s0x_S24 3 ∧ b ∈ s0x_S24 3 ∧
      p ∈ s0x_S24 f1 ∧ b ∈ s0x_S24 f1 ∧ a ∉ s0x_S24 f1 ∧ q ∉ s0x_S24 f1 ∧
      p ∈ s0x_S24 f2 ∧ a ∈ s0x_S24 f2 ∧ b ∉ s0x_S24 f2 ∧ q ∉ s0x_S24 f2 ∧
      a ≠ p ∧ a ≠ q ∧ b ≠ p ∧ b ≠ q) ∨
    (∃ idx : Fin 3, ∃ sw : Bool,
      (if sw = true then q else p) ∈ s0x_S24 (radon3Tab idx).2.2.2.1 ∧
      (radon3Tab idx).1 ∈ s0x_S24 (radon3Tab idx).2.2.2.1 ∧
      (radon3Tab idx).2.1 ∈ s0x_S24 (radon3Tab idx).2.2.2.1 ∧
      (radon3Tab idx).2.2.1 ∉ s0x_S24 (radon3Tab idx).2.2.2.1 ∧
      (if sw = true then p else q) ∉ s0x_S24 (radon3Tab idx).2.2.2.1 ∧
      (if sw = true then q else p) ∈ s0x_S24 (radon3Tab idx).2.2.2.2.1 ∧
      (radon3Tab idx).1 ∈ s0x_S24 (radon3Tab idx).2.2.2.2.1 ∧
      (radon3Tab idx).2.2.1 ∈ s0x_S24 (radon3Tab idx).2.2.2.2.1 ∧
      (radon3Tab idx).2.1 ∉ s0x_S24 (radon3Tab idx).2.2.2.2.1 ∧
      (if sw = true then p else q) ∉ s0x_S24 (radon3Tab idx).2.2.2.2.1 ∧
      (if sw = true then q else p) ∈ s0x_S24 (radon3Tab idx).2.2.2.2.2 ∧
      (radon3Tab idx).2.1 ∈ s0x_S24 (radon3Tab idx).2.2.2.2.2 ∧
      (radon3Tab idx).2.2.1 ∈ s0x_S24 (radon3Tab idx).2.2.2.2.2 ∧
      (radon3Tab idx).1 ∉ s0x_S24 (radon3Tab idx).2.2.2.2.2 ∧
      (if sw = true then p else q) ∉ s0x_S24 (radon3Tab idx).2.2.2.2.2 ∧
      (radon3Tab idx).1 ≠ p ∧ (radon3Tab idx).1 ≠ q ∧
      (radon3Tab idx).2.1 ≠ p ∧ (radon3Tab idx).2.1 ≠ q ∧
      (radon3Tab idx).2.2.1 ≠ p ∧ (radon3Tab idx).2.2.1 ≠ q) := by
  revert p q hpq; decide +kernel

private lemma s24_edge_of_strictRim {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) (w : ℝ³)
    (p q : Fin 7) (hpq : p ≠ q)
    (hrim : ∀ v : Fin 7, v ≠ p → v ≠ q → 0 < det3 (x q - x p) (x v - x p) w) :
    ∃ a b : Fin 9, ⟪F.N a, w⟫ * ⟪F.N b, w⟫ < 0 ∧
      p ∈ s0x_S24 a ∧ p ∈ s0x_S24 b ∧ q ∈ s0x_S24 a ∧ q ∈ s0x_S24 b ∧
      ∀ v : Fin 7, v ≠ p → v ≠ q → v ∉ s0x_S24 a ∨ v ∉ s0x_S24 b := by
  rcases s24_edge_classify p q hpq with
    ⟨a, b, va, vb, hpa, hqa, hvba, hvaa, hpb, hqb, hvab, hvbb, hinter, hvap, hvaq, hvbp, hvbq⟩ |
    ⟨a, b, f1, f2, hp3, hq3, ha3, hb3, hp1, hb1, ha1, hq1, hp2, ha2, hb2, hq2, hap, haq, hbp, hbq⟩ |
    ⟨idx, sw, hrad⟩
  · exact ⟨a, b, opp_signs_of_edge F w p q va vb a b hpa hqa hvba hvaa hpb hqb hvab hvbb
      (hrim va hvap hvaq) (hrim vb hvbp hvbq), hpa, hpb, hqa, hqb, hinter⟩
  · exfalso
    exact not_strictRim_of_quadDiag F w p q a b f1 f2 hp3 hq3 ha3 hb3 hp1 hb1 ha1 hq1
      hp2 ha2 hb2 hq2 (hrim a hap haq) (hrim b hbp hbq)
  · exfalso
    cases sw
    · simp only [Bool.false_eq_true, ↓reduceIte] at hrad
      rcases hrad with ⟨hp1, ha1, hb1, hc1, hq1, hp2, ha2, hc2, hb2, hq2,
        hp3, hb3, hc3, ha3, hq3, hap, haq, hbp, hbq, hcp, hcq⟩
      exact not_strictRim_of_radon3 F w p q _ _ _ _ _ _ hp1 ha1 hb1 hc1 hq1 hp2 ha2 hc2 hb2 hq2
        hp3 hb3 hc3 ha3 hq3 (hrim _ hap haq) (hrim _ hbp hbq) (hrim _ hcp hcq)
    · simp only [↓reduceIte] at hrad
      rcases hrad with ⟨hp1, ha1, hb1, hc1, hq1, hp2, ha2, hc2, hb2, hq2,
        hp3, hb3, hc3, ha3, hq3, hap, haq, hbp, hbq, hcp, hcq⟩
      have hneg : ∀ v : Fin 7, v ≠ q → v ≠ p → 0 < det3 (x p - x q) (x v - x q) (-w) := by
        intro v hv1 hv2
        have := hrim v hv2 hv1
        have hid : det3 (x p - x q) (x v - x q) (-w) = det3 (x q - x p) (x v - x p) w := by
          simp only [det3_expand, PiLp.neg_apply, PiLp.sub_apply]; ring
        rw [hid]; exact this
      exact not_strictRim_of_radon3 F (-w) q p _ _ _ _ _ _ hp1 ha1 hb1 hc1 hq1 hp2 ha2 hc2 hb2 hq2
        hp3 hb3 hc3 ha3 hq3 (hneg _ haq hap) (hneg _ hbq hbp) (hneg _ hcq hcp)

private lemma s24_cyc_of_strictRimN {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x) {w : ℝ³}
    {k : ℕ} [NeZero k] (hk : 3 ≤ k) (r : ZMod k → Fin 7) (hr : Function.Injective r)
    (hrim : StrictRimN x w r) (hnz : ∀ s : Fin 9, ⟪F.N s, w⟫ ≠ 0) :
    S0xCycUD s0x_S24 r (Finset.univ.filter fun s => 0 < ⟪F.N s, w⟫)
      (Finset.univ.filter fun s => ⟪F.N s, w⟫ < 0) ∧
    S0xCycOK s0x_S24 r (fun s => decide (0 < ⟪F.N s, w⟫)) := by
  have : Fact (1 < k) := ⟨by omega⟩
  have hk1 : ∀ i : ZMod k, r i ≠ r (i + 1) := fun i heq => by
    have h := hr heq
    have h1 : (1 : ZMod k) = 0 := by linear_combination -h
    have hval := congr_arg ZMod.val h1
    rw [ZMod.val_one, ZMod.val_zero] at hval
    omega
  have hex : ∀ i : ZMod k, ∃ a b : Fin 9, ⟪F.N a, w⟫ * ⟪F.N b, w⟫ < 0 ∧
      r i ∈ s0x_S24 a ∧ r i ∈ s0x_S24 b ∧ r (i + 1) ∈ s0x_S24 a ∧ r (i + 1) ∈ s0x_S24 b ∧
      ∀ v : Fin 7, v ≠ r i → v ≠ r (i + 1) → v ∉ s0x_S24 a ∨ v ∉ s0x_S24 b := fun i =>
    s24_edge_of_strictRim F w (r i) (r (i + 1)) (hk1 i) (fun v hv1 hv2 => by
      rw [← split_det3_eq]
      exact hrim v i hv1 hv2)
  refine ⟨fun i => ?_, fun i => ?_⟩
  · obtain ⟨a, b, hab, h1, h2, h3, h4, hinter⟩ := hex i
    rcases lt_or_gt_of_ne (hnz a) with ha_neg | ha_pos
    · have hb_pos : 0 < ⟪F.N b, w⟫ := by nlinarith
      exact ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb_pos⟩,
        a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha_neg⟩, h2, h1, h4, h3,
        fun q hq1 hq2 => (hinter q hq1 hq2).symm⟩
    · have hb_neg : ⟪F.N b, w⟫ < 0 := by nlinarith
      exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha_pos⟩,
        b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb_neg⟩, h1, h2, h3, h4, hinter⟩
  · obtain ⟨a, b, hab, h1, h2, h3, h4, hinter⟩ := hex i
    rcases lt_or_gt_of_ne (hnz a) with ha_neg | ha_pos
    · have hb_pos : 0 < ⟪F.N b, w⟫ := by nlinarith
      exact ⟨b, a, decide_eq_true hb_pos, decide_eq_false (not_lt.mpr ha_neg.le),
        h2, h1, h4, h3, fun q hq1 hq2 => (hinter q hq1 hq2).symm⟩
    · have hb_neg : ⟪F.N b, w⟫ < 0 := by nlinarith
      exact ⟨a, b, decide_eq_true ha_pos, decide_eq_false (not_lt.mpr hb_neg.le),
        h1, h2, h3, h4, hinter⟩

/-! ### Main theorem `lexAny_or_splitAny24_of_weakChordArc` -/

/-- **APPROVED (A59 Theorem 1.1 for Type 24).**  On a triangle facet `t ≠ 3`, a weak chord arc
gives a lex cell (`LexAny F`) or a split cell (`SplitAny24 F`). -/
theorem lexAny_or_splitAny24_of_weakChordArc {x : Fin 7 → ℝ³} (F : S0xFac 9 s0x_S24 x)
    {t : Fin 9} (ht : t ≠ 3) (h : WeakChordArc F t) :
    Minimality.Gen.LexAny F ∨ SplitAny24 F := by
  obtain ⟨u, k, hk_ne, r, a, ρ, hnu, hk3, hr, hrA, hrB, hρ, ⟨q₀, hq₀S, hq₀r⟩, hcyc, hin, hmid,
    hbranch⟩ := h
  have : NeZero k := hk_ne
  have : Fact (1 < k) := ⟨by omega⟩
  have ht3 : (s0x_S24 t).card = 3 := by fin_cases t <;> first | exact absurd rfl ht | decide
  have ha1_ne : r a ≠ r (a + 1) := fun heq => by
    have h0 := hr heq
    have h1 : (1 : ZMod k) = 0 := by linear_combination -h0
    have hval := congr_arg ZMod.val h1
    rw [ZMod.val_one, ZMod.val_zero] at hval; omega
  have hSt_eq : s0x_S24 t = {r a, r (a + 1), q₀} := by
    have hsub : {r a, r (a + 1), q₀} ⊆ s0x_S24 t := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl <;> assumption
    have hcard : ({r a, r (a + 1), q₀} : Finset (Fin 7)).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [(hq₀r (a + 1)).symm]
      · simp [ha1_ne, (hq₀r a).symm]
    exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  have ha2_ne : a + 2 ≠ a := by
    intro h0
    have h2 : ((2 : ℕ) : ZMod k) = 0 := by simpa using (by linear_combination h0 : (2 : ZMod k) = 0)
    have hval := congr_arg ZMod.val h2
    have hk2 : 2 < k := by omega
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hk2, ZMod.val_zero] at hval; omega
  have ha21_ne : a + 2 ≠ a + 1 := by
    intro h0
    have h1 : (1 : ZMod k) = 0 := by linear_combination h0
    have hval := congr_arg ZMod.val h1
    rw [ZMod.val_one, ZMod.val_zero] at hval; omega
  have hr2S : r (a + 2) ∉ s0x_S24 t := by
    rw [hSt_eq]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h0 => ha2_ne (hr h0), fun h0 => ha21_ne (hr h0), fun h0 => (hq₀r (a + 2)) h0.symm⟩
  set n := F.N t
  set E_a := x (r (a + 1)) - x (r a)
  have fA : F.f t (x (r a)) = 0 := F.zero t _ hrA
  have fB : F.f t (x (r (a + 1))) = 0 := F.zero t _ hrB
  have f2 : F.f t (x (r (a + 2))) < 0 := F.neg t _ hr2S
  have hnE : ⟪n, E_a⟫ = 0 := by rw [F.inner_sub, fB, fA, sub_self]
  have hnZ : ⟪n, x (r (a + 2)) - x (r a)⟫ = F.f t (x (r (a + 2))) := by
    rw [F.inner_sub, fA, sub_zero]
  have hn_ne : n ≠ 0 := fun h0 => by rw [h0, inner_zero_left] at hnZ; linarith
  have hnn : 0 < ⟪n, n⟫ := inner_self_ne_zero.mpr hn_ne |>.lt_of_le' (real_inner_self_nonneg)
  have hDa_pos : 0 < ρ * det3 E_a u n := by
    have hpr := det3_perp_ratio n E_a u n (x (r (a + 2)) - x (r a))
    have hswap : det3 E_a (x (r (a + 2)) - x (r a)) u = -det3 E_a u (x (r (a + 2)) - x (r a)) :=
      det3_swap23 _ _ _
    have hcyc_a := hcyc a (a + 2) ha2_ne ha21_ne
    have hprod : ⟪n, n⟫ * (ρ * det3 E_a (x (r (a + 2)) - x (r a)) u) =
        (-⟪n, x (r (a + 2)) - x (r a)⟫) * (ρ * det3 E_a u n) := by
      have hpr' : det3 E_a u (x (r (a + 2)) - x (r a)) * ⟪n, n⟫ =
          ⟪n, x (r (a + 2)) - x (r a)⟫ * det3 E_a u n := by
        have hid := inner_det3_perp_id n E_a u (x (r (a + 2)) - x (r a)) n hnE hnu
        linarith [hid]
      rw [hswap]; linear_combination -ρ * hpr'
    nlinarith
  obtain ⟨s, δ, hs0, hs1, hδ, hq0_eq⟩ := hmid q₀ hq₀S hq₀r
  let η : ℝ := if 0 < δ then 1 else -1
  have hηδ : 0 < η * δ := by
    dsimp [η]; split_ifs with h
    · exact mul_pos one_pos h
    · exact mul_pos_of_neg_of_neg (by norm_num) (lt_of_le_of_ne (not_lt.mp h) hδ)
  let e : ℝ³ := η • n
  let u_eps : ℝ → ℝ³ := fun ε => u + ε • e
  have hrim_ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), StrictRimN x (ρ • u_eps ε) r := by
    have h_det_smul : ∀ (A B : ℝ³) (ε : ℝ),
        det3 A B (ρ • u_eps ε) = ρ * det3 A B (u_eps ε) := fun A B ε => by
      simp only [det3_expand, PiLp.smul_apply, smul_eq_mul]; ring
    have h_q0_a : ∀ ε : ℝ, 0 < ε →
        0 < ρ * det3 E_a (x q₀ - x (r a)) (u_eps ε) := fun ε hε => by
      have hsub : x q₀ - x (r a) = s • E_a + δ • u := by
        rw [hq0_eq]; abel
      have hdet_calc : det3 E_a (s • E_a + δ • u) (u + ε • η • n) =
          ε * (η * δ) * det3 E_a u n := by
        simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
      rw [hsub, show u_eps ε = u + ε • η • n from rfl, hdet_calc]
      have : ρ * (ε * (η * δ) * det3 E_a u n) = ε * (η * δ) * (ρ * det3 E_a u n) := by ring
      rw [this]
      exact mul_pos (mul_pos hε hηδ) hDa_pos
    have h_q0_ne : ∀ i : ZMod k, i ≠ a → 0 < ρ * det3 (x (r (i + 1)) - x (r i)) (x q₀ - x (r i)) u := by
      intro i hia
      have hsub : x q₀ - x (r i) = (1 - s) • (x (r a) - x (r i)) + s • (x (r (a + 1)) - x (r i)) + δ • u := by
        ext j
        have hj := congr_arg (fun v : ℝ³ => v.ofLp j) hq0_eq
        simp only [E_a, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hj ⊢
        rw [hj]; ring
      have hdet_eq : det3 (x (r (i + 1)) - x (r i)) (x q₀ - x (r i)) u =
          (1 - s) * det3 (x (r (i + 1)) - x (r i)) (x (r a) - x (r i)) u +
          s * det3 (x (r (i + 1)) - x (r i)) (x (r (a + 1)) - x (r i)) u := by
        rw [hsub]
        simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
      have hdet_mul : ρ * det3 (x (r (i + 1)) - x (r i)) (x q₀ - x (r i)) u =
          (1 - s) * (ρ * det3 (x (r (i + 1)) - x (r i)) (x (r a) - x (r i)) u) +
          s * (ρ * det3 (x (r (i + 1)) - x (r i)) (x (r (a + 1)) - x (r i)) u) := by
        rw [hdet_eq]; ring
      have h1_nonneg : 0 ≤ (1 - s) * (ρ * det3 (x (r (i + 1)) - x (r i)) (x (r a) - x (r i)) u) := by
        by_cases ha_i : a = i
        · subst ha_i; rw [sub_self]; simp [det3_expand]
        · by_cases ha_i1 : a = i + 1
          · subst ha_i1; simp [det3_expand]; ring_nf; exact le_rfl
          · exact mul_nonneg (by linarith) (hcyc i a ha_i ha_i1).le
      have h2_nonneg : 0 ≤ s * (ρ * det3 (x (r (i + 1)) - x (r i)) (x (r (a + 1)) - x (r i)) u) := by
        by_cases ha1_i : a + 1 = i
        · subst ha1_i; rw [sub_self]; simp [det3_expand]
        · by_cases ha1_i1 : a + 1 = i + 1
          · exact absurd (by linear_combination -ha1_i1) hia
          · exact mul_nonneg hs0.le (hcyc i (a + 1) ha1_i ha1_i1).le
      by_cases ha_i : a = i
      · subst ha_i
        have ha1_i1 : a + 1 ≠ a + 1 + 1 := by
          intro h0; exact ha21_ne (by linear_combination -h0)
        have h2_pos : 0 < s * (ρ * det3 (x (r (a + 1)) - x (r a)) (x (r (a + 1)) - x (r a)) u) := by
          exfalso; exact hia rfl
        linarith
      · by_cases ha_i1 : a = i + 1
        · have ha1_i : a + 1 ≠ i := by
            intro h0
            have h2 : ((2 : ℕ) : ZMod k) = 0 := by
              simpa using (by linear_combination h0 - ha_i1 : (2 : ZMod k) = 0)
            have hval := congr_arg ZMod.val h2
            have hk2 : 2 < k := by omega
            rw [ZMod.val_natCast, Nat.mod_eq_of_lt hk2, ZMod.val_zero] at hval; omega
          have ha1_i1 : a + 1 ≠ i + 1 := fun h0 => hia (by linear_combination -h0)
          have h2_pos := mul_pos hs0 (hcyc i (a + 1) ha1_i ha1_i1)
          rw [hdet_mul]; linarith
        · have h1_pos := mul_pos (by linarith : 0 < 1 - s) (hcyc i a ha_i ha_i1)
          rw [hdet_mul]; linarith
    have hcont : ∀ (q : Fin 7) (i : ZMod k),
        0 < ρ * det3 (x (r (i + 1)) - x (r i)) (x q - x (r i)) u →
        ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ρ * det3 (x (r (i + 1)) - x (r i)) (x q - x (r i)) (u_eps ε) := by
      intro q i hpos
      have hc : Continuous fun ε : ℝ => ρ * det3 (x (r (i + 1)) - x (r i)) (x q - x (r i)) (u_eps ε) := by
        simp only [u_eps, det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; fun_prop
      have h0 : 0 < (fun ε : ℝ => ρ * det3 (x (r (i + 1)) - x (r i)) (x q - x (r i)) (u_eps ε)) 0 := by
        simpa [u_eps] using hpos
      exact ((hc.tendsto 0).eventually_const_lt h0).filter_mono nhdsWithin_le_nhds
    have hall : ∀ q : Fin 7, ∀ i : ZMod k, q ≠ r i → q ≠ r (i + 1) →
        ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ρ * det3 (x (r (i + 1)) - x (r i)) (x q - x (r i)) (u_eps ε) := by
      intro q i hq1 hq2
      by_cases hq_im : ∃ j, q = r j
      · obtain ⟨j, rfl⟩ := hq_im
        exact hcont (r j) i (hcyc i j (fun h => hq1 (by rw [h])) (fun h => hq2 (by rw [h])))
      · push Not at hq_im
        by_cases hqS : q ∈ s0x_S24 t
        · have hqq : q = q₀ := by
            rw [hSt_eq] at hqS
            simp only [Finset.mem_insert, Finset.mem_singleton] at hqS
            rcases hqS with rfl | rfl | rfl
            · exact absurd rfl (hq_im a)
            · exact absurd rfl (hq_im (a + 1))
            · rfl
          subst hqq
          by_cases hia : i = a
          · subst hia
            filter_upwards [self_mem_nhdsWithin] with ε hε
            exact h_q0_a ε hε
          · exact hcont q i (h_q0_ne i hia)
        · exact hcont q i (hin q hqS hq_im i)
    have hev_all : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ q : Fin 7, ∀ i : ZMod k, q ≠ r i → q ≠ r (i + 1) →
        0 < Minimality.Split.det3 (x (r (i + 1)) - x (r i)) (x q - x (r i)) (ρ • u_eps ε) := by
      refine eventually_all.mpr fun q => eventually_all.mpr fun i => ?_
      by_cases hq : q ≠ r i ∧ q ≠ r (i + 1)
      · filter_upwards [hall q i hq.1 hq.2] with ε hε _ _
        rw [split_det3_eq, h_det_smul]; exact hε
      · filter_upwards with ε h1 h2
        exact absurd ⟨h1, h2⟩ hq
    exact hev_all
  have hN_ne : ∀ s' : Fin 9, F.N s' ≠ 0 := fun s' h0 => by
    obtain ⟨j, i, hj, hi⟩ := s24_off s'
    have := F.inner_sub s' i j
    rw [h0, inner_zero_left, F.zero s' j hj, sub_zero] at this
    linarith [F.neg s' i hi]
  obtain ⟨v, hv⟩ := exists_forall_inner_ne_zero F.N hN_ne
  have h_open_rim : ∀ u₀ : ℝ³, StrictRimN x (ρ • u₀) r →
      ∀ᶠ δ₂ in 𝓝[>] (0 : ℝ), StrictRimN x (ρ • (u₀ + δ₂ • v)) r := by
    intro u₀ hrim0
    refine eventually_all.mpr fun q => eventually_all.mpr fun i => ?_
    by_cases hq : q ≠ r i ∧ q ≠ r (i + 1)
    · have hc : Continuous fun δ₂ : ℝ => det3 (x (r (i + 1)) - x (r i)) (x q - x (r i)) (ρ • (u₀ + δ₂ • v)) := by
        simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; fun_prop
      have h0 : 0 < det3 (x (r (i + 1)) - x (r i)) (x q - x (r i)) (ρ • u₀) := by
        rw [← split_det3_eq]; exact hrim0 q i hq.1 hq.2
      filter_upwards [((hc.tendsto 0).eventually_const_lt (by simpa using h0)).filter_mono nhdsWithin_le_nhds]
        with δ₂ hδ₂ _ _
      rw [split_det3_eq]; exact hδ₂
    · filter_upwards with δ₂ h1 h2
      exact absurd ⟨h1, h2⟩ hq
  have h_open_nz : ∀ u₀ : ℝ³, ∀ᶠ δ₂ in 𝓝[>] (0 : ℝ), ∀ s' : Fin 9, ⟪F.N s', ρ • (u₀ + δ₂ • v)⟫ ≠ 0 := by
    intro u₀
    refine eventually_all.mpr fun s' => ?_
    have h0 : ⟪F.N s', v⟫ ≠ 0 := hv s'
    have hne_ev : ∀ᶠ δ₂ in 𝓝[>] (0 : ℝ), ⟪F.N s', u₀ + δ₂ • v⟫ ≠ 0 := by
      have : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ δ₂ ∈ Set.Ioo (0 : ℝ) ε₀, ⟪F.N s', u₀ + δ₂ • v⟫ ≠ 0 := by
        by_cases hu0 : ⟪F.N s', u₀⟫ = 0
        · refine ⟨1, zero_lt_one, fun δ₂ hδ₂ heq => ?_⟩
          rw [inner_add_right, real_inner_smul_right, hu0, zero_add] at heq
          rcases mul_eq_zero.mp heq with h1 | h2
          · linarith [hδ₂.1]
          · exact h0 h2
        · refine ⟨|⟪F.N s', u₀⟫| / (2 * |⟪F.N s', v⟫|), div_pos (abs_pos.mpr hu0) (by positivity),
            fun δ₂ hδ₂ heq => ?_⟩
          rw [inner_add_right, real_inner_smul_right] at heq
          have h1 : |⟪F.N s', u₀⟫| = δ₂ * |⟪F.N s', v⟫| := by
            have := eq_neg_of_add_eq_zero_left heq
            rw [this, abs_neg, abs_mul, abs_of_pos hδ₂.1]
          have h2 : δ₂ * |⟪F.N s', v⟫| < |⟪F.N s', u₀⟫| / 2 := by
            have := hδ₂.2
            calc δ₂ * |⟪F.N s', v⟫| < (|⟪F.N s', u₀⟫| / (2 * |⟪F.N s', v⟫|)) * |⟪F.N s', v⟫| :=
                  mul_lt_mul_of_pos_right this (abs_pos.mpr h0)
              _ = |⟪F.N s', u₀⟫| / 2 := by field_simp [abs_ne_zero.mpr h0]
          linarith [abs_pos.mpr hu0]
      obtain ⟨ε₀, hε₀, hI⟩ := this
      exact Filter.eventually_iff_exists_mem.mpr ⟨Set.Ioo (0 : ℝ) ε₀, Ioo_mem_nhdsGT hε₀, hI⟩
    filter_upwards [hne_ev] with δ₂ hδ₂ heq
    rw [real_inner_smul_right] at heq
    exact hδ₂ ((mul_eq_zero.mp heq).resolve_left hρ)
  -- Split on the 3 branches of `hbranch`
  have h_split_branch : ∀ (p q : ZMod k), DepthSepAt (fun i => x (r i)) u p q → SplitAny24 F := by
    intro p q hds
    have hds_ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), DepthSepAt (fun i => x (r i)) (u_eps ε) p q :=
      eventually_depthSepAt hds
    obtain ⟨ε₀, hrim0, hds0⟩ := (hrim_ev.and hds_ev).exists
    have hds_ev2 : ∀ᶠ δ₂ in 𝓝[>] (0 : ℝ), DepthSepAt (fun i => x (r i)) (u_eps ε₀ + δ₂ • v) p q :=
      eventually_depthSepAt hds0
    obtain ⟨δ₂, hrim1, hnz1, hds1⟩ :=
      ((h_open_rim (u_eps ε₀) hrim0).and ((h_open_nz (u_eps ε₀)).and hds_ev2)).exists
    set u' := u_eps ε₀ + δ₂ • v
    set w := ρ • u'
    have hds_smul : ∀ {y : ℝ³} {c : ℝ}, 0 < c → DepthSepAt (fun i => x (r i)) y p q →
        DepthSepAt (fun i => x (r i)) (c • y) p q := by
      intro y c hc ⟨hd, hz⟩
      refine ⟨fun j hj => ?_, ?_⟩
      · have hsm : ∀ A B : ℝ³, det3 A B (c • y) = c * det3 A B y := fun A B => by
          simp only [det3_expand, PiLp.smul_apply, smul_eq_mul]; ring
        rw [hsm, hsm]
        nlinarith [hd j hj, sq_pos_of_pos hc]
      · simp only [real_inner_smul_right]
        rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨fun s hs1 hs2 => mul_lt_mul_of_pos_left (h1 s hs1 hs2) hc,
            fun s hs1 hs2 => mul_lt_mul_of_pos_left (h2 s hs1 hs2) hc⟩
        · exact Or.inr ⟨fun s hs1 hs2 => mul_lt_mul_of_pos_left (h1 s hs1 hs2) hc,
            fun s hs1 hs2 => mul_lt_mul_of_pos_left (h2 s hs1 hs2) hc⟩
    have hds_w : DepthSepAt (fun i => x (r i)) w p q := by
      rcases lt_or_gt_of_ne hρ with hρn | hρp
      · have : w = (-ρ) • (-u') := by rw [smul_neg, neg_smul, neg_neg]
        rw [this]
        exact hds_smul (neg_pos.mpr hρn) hds1.neg
      · exact hds_smul hρp hds1
    obtain ⟨hqp, hqp1, hids⟩ := isDepthSeparatedAt_of_depthSepAt hk3 hds_w
      (fun j hj1 hj2 => by
        rw [← split_det3_eq]
        exact hrim1 (r j) p (fun h => hj1 (hr h)) (fun h => hj2 (hr h)))
    obtain ⟨⟨σ, hrows⟩, _⟩ := splitRows_of_isDepthSeparatedAt hk3 x w r hr hrim1 p q hids
    have hcok := (s24_cyc_of_strictRimN F hk3 r hr hrim1 hnz1).2
    refine ⟨k, hk_ne, r, (fun s' => decide (0 < ⟪F.N s', w⟫)), w, 0, p, q, σ, hk3, hr, hcok, ?_,
      hqp, hqp1, hrows⟩
    intro s'
    refine ⟨fun hs' => Or.inl (of_decide_eq_true hs'), fun hs' => Or.inl ?_⟩
    have hle : ⟪F.N s', w⟫ ≤ 0 := not_lt.mp (of_decide_eq_false hs')
    have hlt : ⟪F.N s', w⟫ < 0 := lt_of_le_of_ne hle (hnz1 s')
    linarith
  rcases hbranch with ⟨hk4, hR⟩ | ⟨p, q, hds⟩ | ⟨hk3', hinj_u⟩
  · -- Branch 1: `4 ≤ k ∧ RobUni` -> `LexAny F`
    have hR_ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), RobUni (fun i => ⟪x (r i), u_eps ε⟫) :=
      (robUni_eventually (fun i => x (r i)) u e hR).filter_mono nhdsWithin_le_nhds
    obtain ⟨ε₀, hrim0, hR0⟩ := (hrim_ev.and hR_ev).exists
    have h_open_R : ∀ᶠ δ₂ in 𝓝[>] (0 : ℝ), RobUni (fun i => ⟪x (r i), u_eps ε₀ + δ₂ • v⟫) :=
      (robUni_eventually (fun i => x (r i)) (u_eps ε₀) v hR0).filter_mono nhdsWithin_le_nhds
    obtain ⟨δ₂, hrim1, hnz1, hR1⟩ :=
      ((h_open_rim (u_eps ε₀) hrim0).and ((h_open_nz (u_eps ε₀)).and h_open_R)).exists
    set w := ρ • (u_eps ε₀ + δ₂ • v)
    have hcyc_w := (s24_cyc_of_strictRimN F hk3 r hr hrim1 hnz1).1
    left
    refine ⟨k, hk_ne, r, Finset.univ.filter (fun s => 0 < ⟪F.N s, w⟫),
      Finset.univ.filter (fun s => ⟪F.N s, w⟫ < 0), w, 0, 0, hk4, hr, hcyc_w, ?_, ?_, ?_⟩
    · intro s' hs'; exact Or.inl (Finset.mem_filter.mp hs').2
    · intro s' hs'; exact Or.inl (neg_pos.mpr (Finset.mem_filter.mp hs').2)
    · simp only [inner_zero_right]
      refine robUniLex_of_robUni ?_
      have hw : ∀ i, ⟪x (r i), w⟫ = ρ * ⟪x (r i), u_eps ε₀ + δ₂ • v⟫ := fun i => by
        simp only [w, real_inner_smul_right]
      simp_rw [hw]
      exact robUni_smul hρ hR1
  · -- Branch 2: `DepthSepAt` -> `SplitAny24 F`
    exact Or.inr (h_split_branch p q hds)
  · -- Branch 3: `k = 3 ∧ Function.Injective` -> `DepthSepAt` -> `SplitAny24 F`
    have hds_ex : ∃ p q : ZMod k, DepthSepAt (fun i => x (r i)) u p q := by
      subst hk3'
      exact depthSepAt_of_k3 hρ hcyc hinj_u
    obtain ⟨p, q, hds⟩ := hds_ex
    exact Or.inr (h_split_branch p q hds)

end Minimality.GenPlus
