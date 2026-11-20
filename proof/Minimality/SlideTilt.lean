module

public import Minimality.SlideE
public import Minimality.FaceChordFac
public import Minimality.SlideDS

@[expose] public section

open scoped RealInnerProductSpace Topology
open Finset Filter
open Minimality Minimality.FaceChord Minimality.H21

namespace Minimality

theorem noPersistHDN_smul {k : ℕ} (x : ZMod k → ℝ³) (u₀ n : ℝ³) {σ : ℝ} (hσ : σ ≠ 0)
    (h : NoPersistHDN x u₀ n) : NoPersistHDN x u₀ (σ • n) := by
  intro i j Y hY Y' hY' hne hu he
  have he' : ⟪Y' - Y, n⟫ = 0 := by
    rw [real_inner_smul_right] at he
    exact (mul_eq_zero.mp he).resolve_left hσ
  exact h i j Y hY Y' hY' hne hu he'

theorem det3_swap_two_three (A B C : ℝ³) : det3 A B C = -det3 A C B := by
  simp only [det3_expand]; ring

theorem det3_middle_decomp (X A B u₀ : ℝ³) (s δ : ℝ) :
    det3 X ((1 - s) • A + s • B + δ • u₀) u₀ =
      (1 - s) * det3 X A u₀ + s * det3 X B u₀ := by
  simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

theorem middle_sub_decomp (xq ra rb ri u₀ : ℝ³) (s δ : ℝ)
    (h : xq = ra + s • (rb - ra) + δ • u₀) :
    xq - ri = (1 - s) • (ra - ri) + s • (rb - ri) + δ • u₀ := by
  ext j
  have hj := congr_arg (fun (v : ℝ³) => v.ofLp j) h
  simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hj ⊢
  linear_combination hj

theorem det3_edge_a_zero (E u₀ : ℝ³) (s δ : ℝ) :
    det3 E (s • E + δ • u₀) u₀ = 0 := by
  simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

theorem det3_edge_a_deriv (E u₀ n : ℝ³) (s δ σ : ℝ) :
    det3 E (s • E + δ • u₀) (σ • n) = σ * δ * det3 E u₀ n := by
  simp only [det3_expand, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

/-- **The off-circle tilt leaf for the forced-depth-tie stratum.**
Generalizes `isRupert_faceChord_fac` to views with a depth tie by tilting the view
`u₀` off the facet plane along `e = σ • F.N t` (`σ = ±1`).

At a view `u₀` on the face circle of facet `t` of an `S0xFac` solid (`⟪F.N t, u₀⟫ = 0`),
with rim edge `r a → r (a + 1)` in facet `t`:
- `hnu`: `u₀` is in the facet plane (`⟪F.N t, u₀⟫ = 0`).
- `hn`: facet normal is nonzero (`F.N t ≠ 0`).
- `hk`: rim length `k ≥ 3`.
- `hA`, `hB`: rim chord endpoints `r a`, `r (a + 1)` lie in facet `t`.
- `hcyc`: the rim `r` is strictly convex at `u₀` with orientation `ρ ≠ 0`.
- `hin`: every non-facet, non-rim vertex is strictly inside the projected silhouette.
- `hmid`: every facet vertex off the rim is a chord middle over `r a → r (a + 1)`,
  `x q = x (r a) + s • (x (r (a + 1)) - x (r a)) + δ • u₀` with `0 < s < 1`,
  and all middles share the same sign of `δ` (`0 < sgn_δ * δ` for `sgn_δ ∈ {1, -1}`).
- `hds`: depth separation `DepthSepAt` holds at `u₀` (NO depth injectivity is required!).
- `hbad`: `NoPersistHDN (fun i => x (r i)) u₀ (F.N t)`.

Conclusion: `x` is Rupert (`IsRupert (univ.image x)`).

### Intended Use (Forced-Depth-Tie Stratum `TIELEAF24`)
On the tie stratum of S5 (segment 35 G-orthogonal to 025, or 25 G-orthogonal to 0345),
every on-circle view has a depth tie `z_p = z_q` with `x p - x q ∥ F.N t`, defeating standard
face-chord leaves that require injective rim depths.
Tilting `u₀ + t e` with `e = σ • F.N t`:
1. Destroys the depth tie at first order (`⟪x p - x q, e⟫ ≠ 0`).
2. Pushes the chord middle(s) strictly inside the silhouette (first order derivative along `e`).
3. Preserves `DepthSepAt` at small `t > 0` since the farthest vertex `c` lies outside the tied pair.
4. Leaves no persistent HDN since the tied pair is not perpendicular to `e`.

Status on tie points (e.g. tie/t1):
- Facet `025` (facet index 2): rim `1 6 4 3 5 2`, chord `2-5` with one middle `0`.
  The theorem applies directly with `M := ∅` in the tilt slide.
- Facet `0345` (facet index 3): with multiple middles of opposite `δ` signs,
  the theorem does not apply directly without opposite-sign middle handling. -/
theorem isRupert_faceChord_tilt {N nf : ℕ} {S : Fin nf → Finset (Fin N)} {x : Fin N → ℝ³}
    (F : S0xFac nf S x) (t : Fin nf) {u₀ : ℝ³} (hnu : ⟪F.N t, u₀⟫ = 0)
    (hn : F.N t ≠ 0)
    {k : ℕ} [NeZero k] (hk : 3 ≤ k) (r : ZMod k → Fin N) {a : ZMod k}
    (hA : r a ∈ S t) (hB : r (a + 1) ∈ S t) {ρ : ℝ} (hρ : ρ ≠ 0)
    (hcyc : ∀ i j, j ≠ i → j ≠ i + 1 →
      0 < ρ * det3 (x (r (i + 1)) - x (r i)) (x (r j) - x (r i)) u₀)
    (hin : ∀ q, q ∉ S t → (∀ j, q ≠ r j) → ∀ i,
      0 < ρ * det3 (x (r (i + 1)) - x (r i)) (x q - x (r i)) u₀)
    {sgn_δ : ℝ} (hsgn : sgn_δ = 1 ∨ sgn_δ = -1)
    (hmid : ∀ q ∈ S t, (∀ j, q ≠ r j) → ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ 0 < sgn_δ * δ ∧
      x q = x (r a) + s • (x (r (a + 1)) - x (r a)) + δ • u₀)
    (hds : ∃ a' c : ZMod k, DepthSepAt (fun i => x (r i)) u₀ a' c)
    (hbad : NoPersistHDN (fun i => x (r i)) u₀ (F.N t)) :
    IsRupert (univ.image x) := by
  classical
  set n := F.N t with hn_def
  set E_a := x (r (a + 1)) - x (r a) with hE_a
  have Nsub : ∀ i j : Fin N, ⟪n, x i - x j⟫ = F.f t (x i) - F.f t (x j) := F.inner_sub t
  have fA : F.f t (x (r a)) = 0 := F.zero t _ hA
  have fB : F.f t (x (r (a + 1))) = 0 := F.zero t _ hB
  have hnE : ⟪n, E_a⟫ = 0 := by rw [hE_a, Nsub, fB, fA, sub_self]
  have ha2 : a + 2 ≠ a := by
    have := zmod_add_ne (k := k) (a := 2) (b := 0) (by omega) (by omega) (by omega) a
    simpa using this
  have ha21 : a + 2 ≠ a + 1 := by
    have := zmod_add_ne (k := k) (a := 2) (b := 1) (by omega) (by omega) (by omega) a
    simpa using this
  have hu₀ : u₀ ≠ 0 := by
    intro h0
    have := hcyc a (a + 2) ha2 ha21
    rw [h0] at this
    have hz3 : det3 (x (r (a + 1)) - x (r a)) (x (r (a + 2)) - x (r a)) 0 = 0 := by
      simp only [det3_expand, PiLp.zero_apply]; ring
    rw [hz3, mul_zero] at this
    exact lt_irrefl _ this
  set D_a := det3 E_a u₀ n with hD_a
  have hDa : D_a ≠ 0 := by
    set Z := x (r (a + 2)) - x (r a) with hZ
    have hcyc_a := hcyc a (a + 2) ha2 ha21
    have hdetZ : det3 E_a Z u₀ ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hcyc_a
      exact lt_irrefl _ hcyc_a
    intro hDa0
    have hpr := det3_perp_ratio n E_a u₀ n Z
    have hnn : ⟪n, n⟫ ≠ 0 := by
      intro h0
      exact hn (inner_self_eq_zero.mp h0)
    have hdetEZ : det3 E_a u₀ Z = 0 := by
      have : det3 E_a u₀ Z * ⟪n, n⟫ = 0 := by
        linear_combination -hpr + ⟪n, Z⟫ * hDa0 - det3 n Z u₀ * hnE + det3 n Z E_a * hnu
      exact (mul_eq_zero.mp this).resolve_right hnn
    have hswap : det3 E_a Z u₀ = -det3 E_a u₀ Z := det3_swap_two_three E_a Z u₀
    rw [hdetEZ, neg_zero] at hswap
    exact hdetZ hswap
  set P := ρ * D_a * sgn_δ with hP_def
  have hP_ne : P ≠ 0 := by
    have hsgn_ne : sgn_δ ≠ 0 := by rcases hsgn with rfl | rfl <;> norm_num
    exact mul_ne_zero (mul_ne_zero hρ hDa) hsgn_ne
  set σ : ℝ := if 0 < P then 1 else -1 with hσ_def
  have hσ : σ = 1 ∨ σ = -1 := by
    by_cases h : 0 < P
    · simp [hσ_def, h]
    · simp [hσ_def, h]
  have hσ_ne : σ ≠ 0 := by
    rcases hσ with h1 | h2
    · rw [h1]; norm_num
    · rw [h2]; norm_num
  have hσP : 0 < σ * P := by
    dsimp [σ]
    split_ifs with h
    · simp only [one_mul]; exact h
    · simp only [neg_mul, one_mul]
      have : P < 0 := lt_of_le_of_ne (not_lt.mp h) hP_ne
      linarith
  have h_deriv_pos : ∀ δ : ℝ, 0 < sgn_δ * δ → 0 < ρ * (σ * δ * D_a) := by
    intro δ hδ
    have heq : ρ * (σ * δ * D_a) = (σ * P) * (sgn_δ * δ) := by
      rcases hsgn with rfl | rfl <;> {
        dsimp [P]
        ring
      }
    rw [heq]
    exact mul_pos hσP hδ
  set e : ℝ³ := σ • n with he_def
  have hbad' : NoPersistHDN (fun i => x (r i)) u₀ e :=
    noPersistHDN_smul (fun i => x (r i)) u₀ n hσ_ne hbad
  refine isRupert_of_slideP_uos' (univ.image x) ∅ u₀ e hu₀ (fun i => x (r i))
    (fun i => mem_image_of_mem _ (mem_univ _))
    (fun i => by simp)
    hk ρ hρ
    (fun i j hi hj => Or.inl (hcyc i j hi hj))
    ?_
    (fun m hm => by simp at hm)
    (Or.inr hds)
    hbad'
  intro y hy hyM hyc i
  obtain ⟨q, -, rfl⟩ := mem_image.mp hy
  have hq_not_r : ∀ j, q ≠ r j := fun j hj => hyc j (congr_arg x hj)
  by_cases hqS : q ∈ S t
  · obtain ⟨s, δ, hs0, hs1, hδ, hq_eq⟩ := hmid q hqS hq_not_r
    by_cases hia : i = a
    · right
      refine ⟨?_, ?_⟩
      · rw [hia, hq_eq]
        have hd1 : x (r a) + s • E_a + δ • u₀ - x (r a) = s • E_a + δ • u₀ := by abel
        rw [hd1]
        exact det3_edge_a_zero E_a u₀ s δ
      · rw [hia, hq_eq, he_def]
        have hd1 : x (r a) + s • E_a + δ • u₀ - x (r a) = s • E_a + δ • u₀ := by abel
        rw [hd1, det3_edge_a_deriv E_a u₀ n s δ σ]
        exact h_deriv_pos δ hδ
    · left
      set X := x (r (i + 1)) - x (r i)
      set A := x (r a) - x (r i)
      set B := x (r (a + 1)) - x (r i)
      have hsub : x q - x (r i) = (1 - s) • A + s • B + δ • u₀ :=
        middle_sub_decomp (x q) (x (r a)) (x (r (a + 1))) (x (r i)) u₀ s δ hq_eq
      have hdecomp : det3 X (x q - x (r i)) u₀ = (1 - s) * det3 X A u₀ + s * det3 X B u₀ := by
        rw [hsub]
        exact det3_middle_decomp X A B u₀ s δ
      have hdecomp_ρ : ρ * det3 X (x q - x (r i)) u₀ =
          (1 - s) * (ρ * det3 X A u₀) + s * (ρ * det3 X B u₀) := by
        linear_combination ρ * hdecomp
      rw [hdecomp_ρ]
      have hs0' : 0 < 1 - s := by linarith
      by_cases hia1 : i = a + 1
      · have hB0 : B = 0 := by
          dsimp [B]; rw [hia1]; exact sub_self _
        have hdetB : det3 X B u₀ = 0 := by
          rw [hB0]; simp only [det3_expand, PiLp.zero_apply]; ring
        have ha_ne1 : a ≠ a + 1 := zmod_ne_add_one (by omega) a
        have ha_ne2 : a ≠ a + 1 + 1 := by
          intro h
          apply ha2
          have : a + 2 = a + 1 + 1 := by ring
          rw [this, ← h]
        have hA_pos : 0 < ρ * det3 X A u₀ := by
          dsimp [X, A]
          rw [hia1]
          exact hcyc (a + 1) a ha_ne1 ha_ne2
        have : (1 - s) * (ρ * det3 X A u₀) + s * (ρ * det3 X B u₀) =
            (1 - s) * (ρ * det3 X A u₀) := by
          rw [hdetB, mul_zero, mul_zero, add_zero]
        rw [this]
        exact mul_pos hs0' hA_pos
      by_cases hi1a : i + 1 = a
      · have hA_eq_X : A = X := by
          dsimp [A, X]
          rw [hi1a]
        have hdetA : det3 X A u₀ = 0 := by
          rw [hA_eq_X]; simp only [det3_expand]; ring
        have ha1_ne1 : a + 1 ≠ i := by
          intro h
          apply ha2
          have : a + 2 = (a + 1) + 1 := by ring
          rw [this, h, hi1a]
        have ha1_ne2 : a + 1 ≠ i + 1 := by
          intro h
          apply hia
          exact (add_right_cancel h).symm
        have hB_pos := hcyc i (a + 1) ha1_ne1 ha1_ne2
        have : (1 - s) * (ρ * det3 X A u₀) + s * (ρ * det3 X B u₀) =
            s * (ρ * det3 X B u₀) := by
          rw [hdetA, mul_zero, mul_zero, zero_add]
        rw [this]
        exact mul_pos hs0 hB_pos
      · have ha_ne1 : a ≠ i := fun h => hia h.symm
        have ha_ne2 : a ≠ i + 1 := fun h => hi1a h.symm
        have ha1_ne1 : a + 1 ≠ i := fun h => hia1 h.symm
        have ha1_ne2 : a + 1 ≠ i + 1 := by
          intro h
          apply hia
          exact (add_right_cancel h).symm
        have hA_pos := hcyc i a ha_ne1 ha_ne2
        have hB_pos := hcyc i (a + 1) ha1_ne1 ha1_ne2
        have h1 : 0 < (1 - s) * (ρ * det3 X A u₀) := mul_pos hs0' hA_pos
        have h2 : 0 < s * (ρ * det3 X B u₀) := mul_pos hs0 hB_pos
        linarith
  · left
    exact hin q hqS hq_not_r i

end Minimality
