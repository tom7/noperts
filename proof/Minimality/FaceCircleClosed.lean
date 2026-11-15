module

public import Minimality.RimCellClosed
public import Minimality.EdgeHDN
public import Minimality.Type21Ridge

@[expose] public section

/-!
# Two small bridge lemmas of the closed-cell route

* `H21.isRupert_faceCircleClosed` (Lemma A of `TREE2-IDEAS-FABLE.md` section 1.1): a facet `f` whose
  normal is perpendicular to `u₀`, all other facings strict at `u₀`, and robustly unimodal rim
  depths at `u₀` give Rupert.  The cell next to `u₀` on the side of `f` is nonempty (tilt along
  `±N f`), so `isRupert_of_closedCell` applies.  No hypothesis on horizontal double normals.
* `noPersistHDN_of_far_offChord` (Lemma H, section 2.2): if the farthest rim vertex `w` from a
  face (strictly) has its foot off the chord `[A, B]` (three literals), the rim has no persistent
  double normal.
-/

set_option autoImplicit false
open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality

/-- **Lemma H** (`noPersistHDN` off the chord).  `⟪n, ·⟫ ≤ κ` on `V`, the rim `x` meets the face
`⟪n, ·⟫ = κ` only in `A`, `B` (`A` a rim vertex), `w` is the unique rim vertex minimizing
`⟪n, ·⟫` (`FAR`), `u₀, e ⟂ n` independent.  If the foot of `w` on the line `AB` along `n` is
not on the line (`chi`) or not on the segment (`Γ(A w, A B) < 0` or `Γ(B w, B A) < 0`), then
the rim has no persistent double normal.  `n ≠ 0` is derived from `FAR`. -/
theorem noPersistHDN_of_far_offChord {V : Finset ℝ³} {k : ℕ} (hk : 2 ≤ k) (x : ZMod k → ℝ³)
    (hxinj : Function.Injective x) (hxV : ∀ i, x i ∈ V) {n : ℝ³} {κ : ℝ} {A B w : ℝ³}
    (hle : ∀ z ∈ V, ⟪n, z⟫ ≤ κ) (hA : ⟪n, A⟫ = κ) (hB : ⟪n, B⟫ = κ) (hAR : ∃ i, x i = A)
    (htop : ∀ m, ⟪n, x m⟫ = κ → x m = A ∨ x m = B) (hwR : ∃ i, x i = w)
    (hfar : ∀ m, x m ≠ w → ⟪n, w⟫ < ⟪n, x m⟫) {u₀ e : ℝ³} (hu : ⟪n, u₀⟫ = 0) (he : ⟪n, e⟫ = 0)
    (hind : cross u₀ e ≠ 0)
    (hoff : ⟪n, cross (B - A) (w - A)⟫ ≠ 0 ∨ ⟪w - A, B - A⟫ < 0 ∨ ⟪w - B, A - B⟫ < 0) :
    NoPersistHDN x u₀ e := by
  intro i j Y hY Y' hY' hne hYu hYe hext
  have hn0 : n ≠ 0 := by
    obtain ⟨i0, hi0⟩ := hwR
    have := hfar (i0 + 1) (fun h => zmod_ne_add_one hk i0 (hxinj (hi0.trans h.symm)))
    rintro rfl
    simp at this
  have h1 : cross n (Y' - Y) = 0 :=
    cross_eq_zero_of_perp2 hu he hYu hYe hind
  obtain ⟨r, hr⟩ : ∃ r : ℝ, Y' - Y = r • n :=
    ⟨_, eq_smul_of_cross_eq_zero hn0 h1⟩
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hne (by rw [zero_smul] at hr; exact (sub_eq_zero.mp hr))
  obtain ⟨Z, hZ, F, hF, r', hr', hFZ, -⟩ := classify_face (V := V) hk x hxinj hxV hle hA hAR htop
    hwR hwR (by intro m h _; rw [min_self]; exact hfar m h) hY hY' hr0 hr hext
  rw [segment_same] at hF
  rw [Set.mem_singleton_iff] at hF
  subst hF
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hZ
  have hα' : α = 1 - β := by linarith
  subst hα'
  have hwA : F - A = β • (B - A) + r' • n := by
    rw [← hFZ]; module
  have hnBA : ⟪n, B - A⟫ = 0 := by rw [inner_sub_right, hA, hB, sub_self]
  rcases hoff with h | h | h
  · apply h
    rw [hwA]
    simp only [cross, PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
    simp
    ring
  · have : ⟪F - A, B - A⟫ = β * ⟪B - A, B - A⟫ := by
      rw [hwA, inner_add_left, real_inner_smul_left, real_inner_smul_left, real_inner_comm,
        hnBA, mul_zero, add_zero]
    have := real_inner_self_nonneg (x := B - A)
    nlinarith [mul_nonneg hβ this]
  · have e1 : F - B = (β - 1) • (B - A) + r' • n := by rw [← sub_add_sub_cancel F A B, hwA]; module
    have : ⟪F - B, A - B⟫ = (1 - β) * ⟪B - A, B - A⟫ := by
      rw [e1, inner_add_left, real_inner_smul_left, real_inner_smul_left,
        show A - B = -(B - A) by abel, inner_neg_right, inner_neg_right, real_inner_comm, hnBA]
      ring
    have := real_inner_self_nonneg (x := B - A)
    nlinarith [mul_nonneg (sub_nonneg.mpr (by linarith : β ≤ 1)) this]

namespace H21

variable {n m : ℕ} {S : Fin m → Finset (Fin n)} {x : Fin n → ℝ³}

/-- **Lemma A** (face-circle item as a closed-cell leaf).  `f` is a facet whose normal is
perpendicular to `u₀`; every other facet of the pattern `(U, Dn)` faces strictly at `u₀`;
`f` is on one side.  Then the cell is nonempty (tilt `u₀` along `±N f`), `u₀` is in its closure,
and robustly unimodal rim depths at `u₀` give Rupert.  No hypothesis on horizontal double
normals, and `f` need not be a facet of the rim. -/
theorem isRupert_faceCircleClosed {k : ℕ} [NeZero k] (hk : 4 ≤ k) (F : S0xFac m S x)
    (hx : Function.Injective x) {c : ZMod k → Fin n} (hc : Function.Injective c)
    {U Dn : Finset (Fin m)} (hcyc : S0xCycUD S c U Dn) {f : Fin m}
    (hf : (f ∈ U ∧ f ∉ Dn) ∨ (f ∈ Dn ∧ f ∉ U)) (hNf : F.N f ≠ 0) {u₀ : ℝ³}
    (hf0 : ⟪F.N f, u₀⟫ = 0) (hU : ∀ t ∈ U, t ≠ f → 0 < ⟪F.N t, u₀⟫)
    (hD : ∀ t ∈ Dn, t ≠ f → ⟪F.N t, u₀⟫ < 0)
    (hR : RobUni (fun i => ⟪x (c i), u₀⟫)) : IsRupert (univ.image x) := by
  have hff : 0 < ⟪F.N f, F.N f⟫ := real_inner_self_pos.mpr hNf
  -- the tilt direction `σ • N f`, `σ = ±1`
  obtain ⟨σ, hσ, hfU, hfD⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ (f ∈ U → 0 < σ) ∧ (f ∈ Dn → σ < 0) := by
    rcases hf with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨1, Or.inl rfl, fun _ => one_pos, fun h => absurd h h2⟩
    · exact ⟨-1, Or.inr rfl, fun h => absurd h h2, fun _ => by norm_num⟩
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), CellAt F U Dn (u₀ + (ε * σ) • F.N f) := by
    have e : ∀ t ε, ⟪F.N t, u₀ + (ε * σ) • F.N f⟫ =
        ⟪F.N t, u₀⟫ + ε * (σ * ⟪F.N t, F.N f⟫) := by
      intro t ε; rw [inner_add_right, real_inner_smul_right]; ring
    refine (Filter.eventually_all_finset U |>.2 fun t ht => ?_).and
      (Filter.eventually_all_finset Dn |>.2 fun t ht => ?_)
    · by_cases htf : t = f
      · subst htf
        filter_upwards [self_mem_nhdsWithin] with ε hε
        rw [e, hf0, zero_add]
        exact mul_pos hε (mul_pos (hfU ht) hff)
      · filter_upwards [eventually_pos_affine (A := ⟪F.N t, u₀⟫)
          (B := σ * ⟪F.N t, F.N f⟫) (Or.inl (hU t ht htf))] with ε hε
        rwa [e]
    · by_cases htf : t = f
      · subst htf
        filter_upwards [self_mem_nhdsWithin] with ε hε
        rw [e, hf0, zero_add]
        have := mul_neg_of_neg_of_pos (hfD ht) hff
        have := mul_neg_of_pos_of_neg hε this
        linarith
      · filter_upwards [eventually_pos_affine (A := -⟪F.N t, u₀⟫)
          (B := -(σ * ⟪F.N t, F.N f⟫)) (Or.inl (by linarith [hD t ht htf]))] with ε hε
        rw [e]; linarith
  obtain ⟨ε, hε⟩ := hev.exists
  refine isRupert_of_closedCell hk F hx hc hcyc hε ⟨fun t ht => ?_, fun t ht => ?_⟩ hR
  · by_cases htf : t = f
    · subst htf; rw [hf0]
    · exact (hU t ht htf).le
  · by_cases htf : t = f
    · subst htf; rw [hf0]
    · exact (hD t ht htf).le

end H21
end Minimality

end
