module

public import Minimality.Type29CertTie
public import Minimality.Type21F2Weak
public import Minimality.Generic.PairR2T
public import Minimality.Generic.NamedViews

@[expose] public section

/-!
# Type 29: the pair cores with a tie at both views, the tied pairs independent

The sign-product route of type 21 (`cert_type21_F2_weak`, `robust_rim_of_pair_signs`)
for the five pairs of `pairViewsGO29` (`P14`, `P11`, `{Xa, T2}`, `P13`, `B2`): `pair_core_ie` and
`shared_core_ie` replace `pair_core` / `shared_core`, taking `IndepF` of the two views in place
of the hypothesis `NoTieAt u ∨ NoTieAt v`.  The covariance of the named views (`covView_view29`) is
here, upstream of the pair certificates.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Minimality

open scoped RealInnerProductSpace Topology
open Filter Noperts Finset

theorem view29_eq_namedView : view29 = namedView vtxLines29 := by
  funext x v; rcases v with _ | _ <;> rfl

theorem tendsto_view29 {ι : Type*} {l : Filter ι} {K : ι → Fin 7 → ℝ³} {x : Fin 7 → ℝ³}
    (hK : ∀ m, Tendsto (fun n => K n m) l (𝓝 (x m))) (v : View29) :
    Tendsto (fun n => view29 (K n) v) l (𝓝 (view29 x v)) :=
  by rw [view29_eq_namedView]; exact tendsto_namedView vtxLines29 hK v

theorem covView_view29 (v : View29) : CovView (fun y : Fin 7 → ℝ³ => view29 y v) :=
  by rw [view29_eq_namedView]; exact covView_namedView vtxLines29 v






/-! ### `pair_core` / `shared_core` with listed ties -/

/-- **`pair_core` without `hno`** (labels in a shape `y`; the views `u = l₁ fu(y)`, `v = l₂ fv(y)`
are nonzero multiples of covariant views).  The tie hypothesis is replaced by the listed ties
(`q ≤ 2`, independent) with `hex` (a view with a tied pair has a listed tie). -/
theorem pair_core_weak (y : Fin 7 → ℝ³) (hyinj : Function.Injective y)
    (fu fv : (Fin 7 → ℝ³) → ℝ³) (hfu : CovView fu) (hfv : CovView fv)
    (d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ : Fin 7)
    (n1 : [d₀, e₀, d₁, e₁].Nodup) (n2 : [f₀, g₀, f₁, g₁].Nodup)
    {u v : ℝ³} {l1 l2 : ℝ} (hl1 : l1 ≠ 0) (hl2 : l2 ≠ 0) (hu : u = l1 • fu y) (hv : v = l2 • fv y)
    (m1u : SegMeet (y d₀) (y d₁) (y e₀) (y e₁) u) (m1v : SegMeet (y d₀) (y d₁) (y e₀) (y e₁) v)
    (m2u : SegMeet (y f₀) (y f₁) (y g₀) (y g₁) u) (m2v : SegMeet (y f₀) (y f₁) (y g₀) (y g₁) v)
    (hS2 : det3 (y g₀ - y f₀) (y f₁ - y f₀) (y g₁ - y g₀) ≠ 0)
    (hp1 : 0 < det3 u (y d₁ - y d₀) (y e₁ - y e₀) * det3 v (y d₁ - y d₀) (y e₁ - y e₀))
    (hn2 : det3 u (y f₁ - y f₀) (y g₁ - y g₀) * det3 v (y f₁ - y f₀) (y g₁ - y g₀) < 0)
    (o1 : OneTieAt (univ.image y) (fu y)) (o2 : OneTieAt (univ.image y) (fv y))
    {q : ℕ} (hq : q ≤ 2) (ties : Fin q → Bool × Fin 7 × Fin 7)
    (hties : ∀ t, ⟪y (ties t).2.1 - y (ties t).2.2,
      (pairGroup fu fv d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ (ties t).1).view y⟫ = 0)
    (hind : TieIndep (fun t => y (ties t).2.1 - y (ties t).2.2)
      (fun t => (pairGroup fu fv d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ (ties t).1).view y))
    (hex : ∀ a, (∃ i j : Fin 7, i ≠ j ∧ ⟪y i, (pairGroup fu fv d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ a).view y⟫ =
        ⟪y j, (pairGroup fu fv d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ a).view y⟫) → ∃ t, (ties t).1 = a) :
    IsRobustUnimodal (quad ⟪y f₀, v⟫ ⟪y g₀, v⟫ ⟪y f₁, v⟫ ⟪y g₁, v⟫) ∨
      (IsRobustUnimodal (quad ⟪y d₀, u⟫ ⟪y e₀, u⟫ ⟪y d₁, u⟫ ⟪y e₁, u⟫) ∧ ⟪u, v⟫ ≤ 0) := by
  by_cases hR2 : IsRobustUnimodal (quad ⟪y f₀, v⟫ ⟪y g₀, v⟫ ⟪y f₁, v⟫ ⟪y g₁, v⟫)
  · exact Or.inl hR2
  right
  have hinj := pairGroup_lab_inj fu fv n1 n2
  have hcov := hcover_of_oneTieAt (pairGroup fu fv d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁)
    (pairGroup_hTv fu fv _ _ _ _ _ _ _ _) y hyinj
    (fun a => by cases a; exact o2; exact o1) ties hties hind hex hinj
  have hdet := mul_neg_of_pos_of_neg hp1 hn2
  have hdet' : det3 (fu y) (y d₁ - y d₀) (y e₁ - y e₀) * det3 (fv y) (y d₁ - y d₀) (y e₁ - y e₀) *
      (det3 (fu y) (y f₁ - y f₀) (y g₁ - y g₀) * det3 (fv y) (y f₁ - y f₀) (y g₁ - y g₀)) < 0 :=
    hdet_smul hl1 hl2 (by rw [← hu, ← hv]; exact hdet)
  have m1u' : SegMeet (y d₀) (y d₁) (y e₀) (y e₁) (fu y) :=
    segMeet_smul hl1 (by rw [← hu]; exact m1u)
  have m1v' : SegMeet (y d₀) (y d₁) (y e₀) (y e₁) (fv y) :=
    segMeet_smul hl2 (by rw [← hv]; exact m1v)
  have m2u' : SegMeet (y f₀) (y f₁) (y g₀) (y g₁) (fu y) :=
    segMeet_smul hl1 (by rw [← hu]; exact m2u)
  have m2v' : SegMeet (y f₀) (y f₁) (y g₀) (y g₁) (fv y) :=
    segMeet_smul hl2 (by rw [← hv]; exact m2v)
  have R := robust_rim_of_pair_signs fu fv hfu hfv d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ y hdet' m1u' m1v' m2v' m2u'
    hinj hq ties hties hind hcov
  rcases R with R1 | R2
  swap
  · exact absurd (robust_quad_smul y hl2 hv _ _ _ _ R2) hR2
  refine ⟨robust_quad_smul y hl1 hu _ _ _ _ R1, ?_⟩
  have mem : ∀ k, y k ∈ Finset.univ.image y :=
    fun k => Finset.mem_image_of_mem y (Finset.mem_univ k)
  have o2v : OneTieAt (univ.image y) v := o2.of_eq_smul hv hl2
  have W2 := weakSep_of_not_robust (o2v.oneTie4 (mem f₀) (mem g₀) (mem f₁) (mem g₁)
    (List.nodup4_img hyinj n2)) hR2
  by_contra hpos
  push Not at hpos
  have hne : ⟪v, u⟫ ≠ 0 := by rw [real_inner_comm]; exact hpos.ne'
  have B := weakSep_det_sign (a' := y f₀) (a := y f₁) (b := y g₀) (b' := y g₁) (u := v) (v := u)
    W2.symm m2v m2u hne hS2
  rw [real_inner_comm] at B
  nlinarith [mul_pos hpos (neg_pos.mpr hn2), mul_comm (det3 u (y f₁ - y f₀) (y g₁ - y g₀))
    (det3 v (y f₁ - y f₀) (y g₁ - y g₀))]

/-- **`pair_core` with independent ties at both views**: `NoTieAt u ∨ NoTieAt v` is replaced by
`IndepF` of the two views (`hI`; vacuous if a view has no tie).  `u, v` are nonzero multiples of
the views `fu y`, `fv y`. -/
theorem pair_core_ie (y : Fin 7 → ℝ³) (hyinj : Function.Injective y)
    (fu fv : (Fin 7 → ℝ³) → ℝ³) (hfu : CovView fu) (hfv : CovView fv)
    (d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ : Fin 7)
    (n1 : [d₀, e₀, d₁, e₁].Nodup) (n2 : [f₀, g₀, f₁, g₁].Nodup)
    {u v : ℝ³} {l1 l2 : ℝ} (hl1 : l1 ≠ 0) (hl2 : l2 ≠ 0) (hu : u = l1 • fu y) (hv : v = l2 • fv y)
    (m1u : SegMeet (y d₀) (y d₁) (y e₀) (y e₁) u) (m1v : SegMeet (y d₀) (y d₁) (y e₀) (y e₁) v)
    (m2u : SegMeet (y f₀) (y f₁) (y g₀) (y g₁) u) (m2v : SegMeet (y f₀) (y f₁) (y g₀) (y g₁) v)
    (hS1 : det3 (y e₀ - y d₀) (y d₁ - y d₀) (y e₁ - y e₀) ≠ 0)
    (hS2 : det3 (y g₀ - y f₀) (y f₁ - y f₀) (y g₁ - y g₀) ≠ 0)
    (hp1 : 0 < det3 u (y d₁ - y d₀) (y e₁ - y e₀) * det3 v (y d₁ - y d₀) (y e₁ - y e₀))
    (hn2 : det3 u (y f₁ - y f₀) (y g₁ - y g₀) * det3 v (y f₁ - y f₀) (y g₁ - y g₀) < 0)
    (o1 : OneTieAt (univ.image y) (fu y)) (o2 : OneTieAt (univ.image y) (fv y))
    (hI : IndepF (univ.image y) (fu y) (fv y)) :
    IsRobustUnimodal (quad ⟪y f₀, v⟫ ⟪y g₀, v⟫ ⟪y f₁, v⟫ ⟪y g₁, v⟫) ∨
      (IsRobustUnimodal (quad ⟪y d₀, u⟫ ⟪y e₀, u⟫ ⟪y d₁, u⟫ ⟪y e₁, u⟫) ∧ ⟪u, v⟫ ≤ 0) := by
  have mem : ∀ k, y k ∈ Finset.univ.image y :=
    fun k => Finset.mem_image_of_mem y (Finset.mem_univ k)
  by_cases hno : NoTieAt (univ.image y) (fu y) ∨ NoTieAt (univ.image y) (fv y)
  · exact pair_core (mem d₀) (mem d₁) (mem e₀) (mem e₁) (mem f₀) (mem f₁) (mem g₀) (mem g₁)
      (List.nodup4_img hyinj n1) (List.nodup4_img hyinj n2) m1u m1v m2u m2v hS1 hS2 hp1 hn2
      (o1.of_eq_smul hu hl1) (o2.of_eq_smul hv hl2)
      (hno.imp (·.of_eq_smul hu hl1) (·.of_eq_smul hv hl2))
  · obtain ⟨i, j, k, l, e1, e2, hind'⟩ := exists_ties_of_indepF hI hno
    obtain ⟨ties, hties, hind, hex⟩ :=
      exists_listed_ties (pairGroup fu fv d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁) rfl rfl e1 e2 hind'
    exact pair_core_weak y hyinj fu fv hfu hfv d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ n1 n2 hl1 hl2 hu hv
      m1u m1v m2u m2v hS2 hp1 hn2 o1 o2 (q := 2) le_rfl ties hties hind (fun a _ => hex a)

/-- **`shared_core` without `hno`** (labels in a shape; `hS1`, `hS2` are not needed). -/
theorem shared_core_weak (y : Fin 7 → ℝ³) (hyinj : Function.Injective y)
    (fu fv : (Fin 7 → ℝ³) → ℝ³) (hfu : CovView fu) (hfv : CovView fv)
    (a' a b b' c c' : Fin 7)
    (n1 : [a', b, a, b'].Nodup) (n2 : [a', c', a, c].Nodup)
    {u v : ℝ³} {l1 l2 : ℝ} (hl1 : l1 ≠ 0) (hl2 : l2 ≠ 0) (hu : u = l1 • fu y) (hv : v = l2 • fv y)
    (m1u : SegMeet (y a') (y a) (y b) (y b') u) (m1v : SegMeet (y a') (y a) (y b) (y b') v)
    (m2u : SegMeet (y a') (y a) (y c) (y c') u) (m2v : SegMeet (y a') (y a) (y c) (y c') v)
    (hdet : det3 u (y a - y a') (y b' - y b) * det3 v (y a - y a') (y b' - y b) *
      (det3 u (y a - y a') (y c' - y c) * det3 v (y a - y a') (y c' - y c)) < 0)
    (o1 : OneTieAt (univ.image y) (fu y)) (o2 : OneTieAt (univ.image y) (fv y))
    {q : ℕ} (hq : q ≤ 2) (ties : Fin q → Bool × Fin 7 × Fin 7)
    (hties : ∀ t, ⟪y (ties t).2.1 - y (ties t).2.2,
      (pairGroup fu fv a' a b b' a' a c' c (ties t).1).view y⟫ = 0)
    (hind : TieIndep (fun t => y (ties t).2.1 - y (ties t).2.2)
      (fun t => (pairGroup fu fv a' a b b' a' a c' c (ties t).1).view y))
    (hex : ∀ e, (∃ i j : Fin 7, i ≠ j ∧ ⟪y i, (pairGroup fu fv a' a b b' a' a c' c e).view y⟫ =
        ⟪y j, (pairGroup fu fv a' a b b' a' a c' c e).view y⟫) → ∃ t, (ties t).1 = e) :
    IsRobustUnimodal (quad ⟪y a', u⟫ ⟪y b, u⟫ ⟪y a, u⟫ ⟪y b', u⟫) ∨
      IsRobustUnimodal (quad ⟪y a', v⟫ ⟪y c', v⟫ ⟪y a, v⟫ ⟪y c, v⟫) := by
  have hinj := pairGroup_lab_inj fu fv n1 n2
  have hTv := pairGroup_hTv fu fv a' a b b' a' a c' c
  have hcov := hcover_of_oneTieAt (pairGroup fu fv a' a b b' a' a c' c) hTv y hyinj
    (fun a => by cases a; exact o2; exact o1) ties hties hind hex hinj
  have hdet0 : det3 (fu y) (y a - y a') (y b' - y b) * det3 (fv y) (y a - y a') (y b' - y b) *
      (det3 (fu y) (y a - y a') (y c' - y c) * det3 (fv y) (y a - y a') (y c' - y c)) < 0 :=
    hdet_smul hl1 hl2 (by rw [← hu, ← hv]; exact hdet)
  have hflip : ∀ w P A B : ℝ³, det3 w P (A - B) = - det3 w P (B - A) := by
    intro w P A B; unfold det3; rw [← inner_neg_right, neg_sub]
  have hdet' : det3 (fu y) (y a - y a') (y b' - y b) * det3 (fv y) (y a - y a') (y b' - y b) *
      (det3 (fu y) (y a - y a') (y c - y c') * det3 (fv y) (y a - y a') (y c - y c')) < 0 := by
    rw [hflip (fu y) (y a - y a') (y c) (y c'), hflip (fv y) (y a - y a') (y c) (y c'), neg_mul_neg]
    exact hdet0
  have m1u' : SegMeet (y a') (y a) (y b) (y b') (fu y) :=
    segMeet_smul hl1 (by rw [← hu]; exact m1u)
  have m1v' : SegMeet (y a') (y a) (y b) (y b') (fv y) :=
    segMeet_smul hl2 (by rw [← hv]; exact m1v)
  have m2u' : SegMeet (y a') (y a) (y c) (y c') (fu y) :=
    segMeet_smul hl1 (by rw [← hu]; exact m2u)
  have m2v' : SegMeet (y a') (y a) (y c) (y c') (fv y) :=
    segMeet_smul hl2 (by rw [← hv]; exact m2v)
  rcases robust_rim_of_pair_signs fu fv hfu hfv a' a b b' a' a c' c y hdet' m1u' m1v' m2v'.swap_e m2u'.swap_e hinj
    hq ties hties hind hcov with R | R
  · exact Or.inl (robust_quad_smul y hl1 hu _ _ _ _ R)
  · exact Or.inr (robust_quad_smul y hl2 hv _ _ _ _ R)

/-- **`shared_core` with independent ties at both views** (see `pair_core_ie`). -/
theorem shared_core_ie (y : Fin 7 → ℝ³) (hyinj : Function.Injective y)
    (fu fv : (Fin 7 → ℝ³) → ℝ³) (hfu : CovView fu) (hfv : CovView fv)
    (a' a b b' c c' : Fin 7)
    (n1 : [a', b, a, b'].Nodup) (n2 : [a', c', a, c].Nodup)
    {u v : ℝ³} {l1 l2 : ℝ} (hl1 : l1 ≠ 0) (hl2 : l2 ≠ 0) (hu : u = l1 • fu y) (hv : v = l2 • fv y)
    (m1u : SegMeet (y a') (y a) (y b) (y b') u) (m1v : SegMeet (y a') (y a) (y b) (y b') v)
    (m2u : SegMeet (y a') (y a) (y c) (y c') u) (m2v : SegMeet (y a') (y a) (y c) (y c') v)
    (hS1 : det3 (y b - y a') (y a - y a') (y b' - y b) ≠ 0)
    (hS2 : det3 (y c - y a') (y a - y a') (y c' - y c) ≠ 0)
    (hdet : det3 u (y a - y a') (y b' - y b) * det3 v (y a - y a') (y b' - y b) *
      (det3 u (y a - y a') (y c' - y c) * det3 v (y a - y a') (y c' - y c)) < 0)
    (o1 : OneTieAt (univ.image y) (fu y)) (o2 : OneTieAt (univ.image y) (fv y))
    (hI : IndepF (univ.image y) (fu y) (fv y)) :
    IsRobustUnimodal (quad ⟪y a', u⟫ ⟪y b, u⟫ ⟪y a, u⟫ ⟪y b', u⟫) ∨
      IsRobustUnimodal (quad ⟪y a', v⟫ ⟪y c', v⟫ ⟪y a, v⟫ ⟪y c, v⟫) := by
  have mem : ∀ k, y k ∈ Finset.univ.image y :=
    fun k => Finset.mem_image_of_mem y (Finset.mem_univ k)
  by_cases hno : NoTieAt (univ.image y) (fu y) ∨ NoTieAt (univ.image y) (fv y)
  · exact shared_core (mem a') (mem a) (mem b) (mem b') (mem c) (mem c')
      (List.nodup4_img hyinj n1) (List.nodup4_img hyinj n2) m1u m1v m2u m2v hS1 hS2 hdet
      (o1.of_eq_smul hu hl1) (o2.of_eq_smul hv hl2)
      (hno.imp (·.of_eq_smul hu hl1) (·.of_eq_smul hv hl2))
  · obtain ⟨i, j, k, l, e1, e2, hind'⟩ := exists_ties_of_indepF hI hno
    obtain ⟨ties, hties, hind, hex⟩ :=
      exists_listed_ties (pairGroup fu fv a' a b b' a' a c' c) rfl rfl e1 e2 hind'
    exact shared_core_weak y hyinj fu fv hfu hfv a' a b b' c c' n1 n2 hl1 hl2 hu hv
      m1u m1v m2u m2v hdet o1 o2 (q := 2) le_rfl ties hties hind (fun a _ => hex a)

/-- **MF for the pair (V, Y)** at a unimodular `L`, generic in the pair data. `hYuni` is
`NF29.k4_Y_view` (curried); `hm` the crossing of the V diagonals with `l < 0`. -/
theorem mf_vy (L : ℝ³ →L[ℝ] ℝ³) (hL : LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) = 1)
    (y : Fin 7 → ℝ³) (hyinj : Function.Injective y) (vN : ℝ³) (hvN : vN ≠ 0) (c : ℝ) (hc : c ≠ 0)
    (fu : (Fin 7 → ℝ³) → ℝ³) (hfu : CovView fu) (hfu' : fu y = c • vN)
    (fv : (Fin 7 → ℝ³) → ℝ³) (hfv : CovView fv) (hfv' : fv y = y 5 - y 3)
    {s t l : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hm : (y 1 + t • (y 3 - y 1)) - (y 5 + s • (y 2 - y 5)) = l • vN) (hl : l < 0)
    (hYuni : ∀ w : ℝ³, 0 < ⟪y 5 - y 3, w⟫ → 0 ≤ ⟪vN, w⟫ →
      Function.Injective (quint ⟪y 5, w⟫ ⟪y 0, w⟫ ⟪y 1, w⟫ ⟪y 4, w⟫ ⟪y 6, w⟫) →
      IsCyclicUnimodal (quint ⟪y 5, w⟫ ⟪y 0, w⟫ ⟪y 1, w⟫ ⟪y 4, w⟫ ⟪y 6, w⟫))
    (i1 : Function.Injective (quad ⟪L (y 5), L (fu y)⟫ ⟪L (y 1), L (fu y)⟫ ⟪L (y 2), L (fu y)⟫
      ⟪L (y 3), L (fu y)⟫))
    (i2 : Function.Injective (quint ⟪L (y 5), L (fv y)⟫ ⟪L (y 0), L (fv y)⟫ ⟪L (y 1), L (fv y)⟫
      ⟪L (y 4), L (fv y)⟫ ⟪L (y 6), L (fv y)⟫)) :
    IsCyclicUnimodal (quad ⟪L (y 5), L (fu y)⟫ ⟪L (y 1), L (fu y)⟫ ⟪L (y 2), L (fu y)⟫
      ⟪L (y 3), L (fu y)⟫) ∨
    IsCyclicUnimodal (quint ⟪L (y 5), L (fv y)⟫ ⟪L (y 0), L (fv y)⟫ ⟪L (y 1), L (fv y)⟫
      ⟪L (y 4), L (fv y)⟫ ⟪L (y 6), L (fv y)⟫) := by
  by_contra hn
  push Not at hn
  have s1 : DepthSep (L (y 5)) (L (y 2)) (L (y 1)) (L (y 3)) (L (fu y)) := by
    by_contra hcn; exact hn.1 (quad_unimodal hcn (nodup_of_injective_quad i1))
  rw [hfu', map_smul] at s1
  have s1' := depthSep_smul hc s1
  have hw : L vN ≠ 0 := fun h => hvN (eq_zero_of_map_eq_zero_of_det_one hL h)
  have hm' : (L (y 1) + t • (L (y 3) - L (y 1))) - (L (y 5) + s • (L (y 2) - L (y 5))) = l • L vN := by
    have := congrArg L hm
    simpa [map_sub, map_add, map_smul] using this
  -- ψ_L > 0
  have hψ : ⟪L (y 3), L vN⟫ < ⟪L (y 5), L vN⟫ := by
    rcases s1' with h | h
    · exfalso
      simp only [max_lt_iff, lt_min_iff] at h
      exact not_weakSep_of_meet hs0 hs1 ht0 ht1 hm' hl hw h.1.1.le h.2.1.le (h.1.2.le) h.2.2.le
    · simp only [max_lt_iff, lt_min_iff] at h
      exact h.1.2
  -- the Y view
  set w := ContinuousLinearMap.adjoint L (L (y 5 - y 3)) with hwdef
  have hwi : ∀ p : ℝ³, ⟪p, w⟫ = ⟪L p, L (y 5 - y 3)⟫ := fun p => by
    rw [hwdef, ContinuousLinearMap.adjoint_inner_right]
  have hne : L (y 5 - y 3) ≠ 0 := fun h => by
    exact hyinj.ne (by decide : (5 : Fin 7) ≠ 3) (sub_eq_zero.mp (eq_zero_of_map_eq_zero_of_det_one hL h))
  have hsq : 0 < ⟪y 5 - y 3, w⟫ := by
    rw [hwi]; exact real_inner_self_pos.mpr hne
  have hψ' : 0 ≤ ⟪vN, w⟫ := by
    rw [hwi, real_inner_comm, map_sub, inner_sub_left]
    linarith
  have key : ∀ a b c d e : Fin 7, quint ⟪L (y a), L (fv y)⟫ ⟪L (y b), L (fv y)⟫ ⟪L (y c), L (fv y)⟫
      ⟪L (y d), L (fv y)⟫ ⟪L (y e), L (fv y)⟫ = quint ⟪y a, w⟫ ⟪y b, w⟫ ⟪y c, w⟫ ⟪y d, w⟫ ⟪y e, w⟫ := by
    intro a b c d e; rw [hfv', hwi, hwi, hwi, hwi, hwi]
  rw [key] at i2
  exact hn.2 (by rw [key]; exact hYuni w hsq hψ' i2)

/-- The two tests: V quad `(5,1,2,3)` at `fu`, Y pentagon `(5,0,1,4,6)` at `fv`. -/
noncomputable def vyGroup (fu fv : (Fin 7 → ℝ³) → ℝ³) : Bool → ViewGroup 7
  | true => .single (LabTest.quad fu 5 1 2 3)
  | false => .single (pentagonTest fv 5 0 1 4 6)

theorem vyGroup_hTv (fu fv : (Fin 7 → ℝ³) → ℝ³) :
    ∀ a, ∀ T ∈ (vyGroup fu fv a).tests, T.view = (vyGroup fu fv a).view := by
  intro a T hT
  cases a <;> simp [vyGroup, ViewGroup.tests] at hT <;> subst hT <;> rfl

theorem vyGroup_lab_inj (fu fv : (Fin 7 → ℝ³) → ℝ³) :
    ∀ a, ∀ T ∈ (vyGroup fu fv a).tests, Function.Injective T.lab := by
  intro a T hT
  cases a <;> simp [vyGroup, ViewGroup.tests] at hT <;> subst hT
  · show Function.Injective (fun i : ZMod 5 => ![(5 : Fin 7), 0, 1, 4, 6] i)
    decide
  · show Function.Injective (fun i : ZMod 4 => ![(5 : Fin 7), 1, 2, 3] i)
    decide

/-- **Robust rim for the pair (V, Y)** (the analogue of `robust_rim_of_pair_signs` for the pentagon Y; no `hno`). -/
theorem robust_rim_vy (fu fv : (Fin 7 → ℝ³) → ℝ³) (hfu : CovView fu) (hfv : CovView fv)
    (y : Fin 7 → ℝ³) (hyinj : Function.Injective y) (vN : ℝ³) (hvN : vN ≠ 0) (c : ℝ) (hc : c ≠ 0)
    (hfu' : fu y = c • vN) (hfv' : fv y = y 5 - y 3)
    {s t l : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hm : (y 1 + t • (y 3 - y 1)) - (y 5 + s • (y 2 - y 5)) = l • vN) (hl : l < 0)
    (hYuni : ∀ w : ℝ³, 0 < ⟪y 5 - y 3, w⟫ → 0 ≤ ⟪vN, w⟫ →
      Function.Injective (quint ⟪y 5, w⟫ ⟪y 0, w⟫ ⟪y 1, w⟫ ⟪y 4, w⟫ ⟪y 6, w⟫) →
      IsCyclicUnimodal (quint ⟪y 5, w⟫ ⟪y 0, w⟫ ⟪y 1, w⟫ ⟪y 4, w⟫ ⟪y 6, w⟫))
    {q : ℕ} (hq : q ≤ 2) (ties : Fin q → Bool × Fin 7 × Fin 7)
    (hties : ∀ t, ⟪y (ties t).2.1 - y (ties t).2.2, (vyGroup fu fv (ties t).1).view y⟫ = 0)
    (hind : TieIndep (fun t => y (ties t).2.1 - y (ties t).2.2)
      (fun t => (vyGroup fu fv (ties t).1).view y))
    (hcover : ∀ e, ∀ T ∈ (vyGroup fu fv e).tests, ∀ i j : ZMod T.k, T.depth y i = T.depth y j →
      Relation.EqvGen (fun p p' => ∃ t, (ties t).1 = e ∧ (ties t).2 = (p, p')) (T.lab i) (T.lab j)) :
    IsRobustUnimodal (quad ⟪y 5, fu y⟫ ⟪y 1, fu y⟫ ⟪y 2, fu y⟫ ⟪y 3, fu y⟫) ∨
    IsRobustUnimodal (quint ⟪y 5, fv y⟫ ⟪y 0, fv y⟫ ⟪y 1, fv y⟫ ⟪y 4, fv y⟫ ⟪y 6, fv y⟫) := by
  have hcov : ∀ e, CovView (vyGroup fu fv e).view := by
    intro e; cases e
    · exact hfv
    · exact hfu
  have hMF : ∀ᶠ L : ℝ³ →L[ℝ] ℝ³ in 𝓝 1, LinearMap.det (L : ℝ³ →ₗ[ℝ] ℝ³) = 1 →
      (∀ e, ∀ T ∈ (vyGroup fu fv e).tests, Function.Injective (T.depth (mapShape L y))) →
      ∃ e, ∃ T ∈ (vyGroup fu fv e).tests, IsCyclicUnimodal (T.depth (mapShape L y)) := by
    refine Filter.Eventually.of_forall fun L hL hi => ?_
    have i1 := hi true (LabTest.quad fu 5 1 2 3) (by simp [vyGroup, ViewGroup.tests])
    have i2 := hi false (pentagonTest fv 5 0 1 4 6) (by simp [vyGroup, ViewGroup.tests])
    rw [depth_quad_map hfu L y hL] at i1
    rw [depth_pentagon_map hfv L y hL] at i2
    rcases mf_vy L hL y hyinj vN hvN c hc fu hfu hfu' fv hfv hfv' hs0 hs1 ht0 ht1 hm hl hYuni
      i1 i2 with h | h
    · exact ⟨true, LabTest.quad fu 5 1 2 3, by simp [vyGroup, ViewGroup.tests], by
        rw [depth_quad_map hfu L y hL]; exact h⟩
    · exact ⟨false, pentagonTest fv 5 0 1 4 6, by simp [vyGroup, ViewGroup.tests], by
        rw [depth_pentagon_map hfv L y hL]; exact h⟩
  have := robust_corner_rim_of_MF (n := 7) (q := q) (A := Bool) y (vyGroup fu fv)
    hcov (fun e => by cases e <;> simp [vyGroup, ViewGroup.Ordered])
    (fun e T h => by
      cases e <;> simp [vyGroup] at h <;> subst h <;> simp [LabTest.quad, pentagonTest])
    (vyGroup_lab_inj fu fv) hq ties hties hind hcover hMF
  rcases this with ⟨e, T, hT, hr⟩ | ⟨e, hs⟩
  · cases e
    · simp [vyGroup, ViewGroup.tests] at hT; subst hT; right
      rwa [depth_pentagon] at hr
    · simp [vyGroup, ViewGroup.tests] at hT; subst hT; left
      rwa [depth_quad] at hr
  · cases e <;> simp [vyGroup, ViewGroup.Straddle] at hs

/-- **The robust rim of `V` or `Y` with independent ties at both views**: the two ties (one at `fu y`,
one at `fv y`, `IndepF`) are listed and `hcover` comes from `OneTieAt`. -/
theorem robust_rim_vy_ie (fu fv : (Fin 7 → ℝ³) → ℝ³) (hfu : CovView fu) (hfv : CovView fv)
    (y : Fin 7 → ℝ³) (hyinj : Function.Injective y) (vN : ℝ³) (hvN : vN ≠ 0) (c : ℝ) (hc : c ≠ 0)
    (hfu' : fu y = c • vN) (hfv' : fv y = y 5 - y 3)
    {s t l : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hm : (y 1 + t • (y 3 - y 1)) - (y 5 + s • (y 2 - y 5)) = l • vN) (hl : l < 0)
    (hYuni : ∀ w : ℝ³, 0 < ⟪y 5 - y 3, w⟫ → 0 ≤ ⟪vN, w⟫ →
      Function.Injective (quint ⟪y 5, w⟫ ⟪y 0, w⟫ ⟪y 1, w⟫ ⟪y 4, w⟫ ⟪y 6, w⟫) →
      IsCyclicUnimodal (quint ⟪y 5, w⟫ ⟪y 0, w⟫ ⟪y 1, w⟫ ⟪y 4, w⟫ ⟪y 6, w⟫))
    (o1 : OneTieAt (univ.image y) (fu y)) (o2 : OneTieAt (univ.image y) (fv y))
    (hI : IndepF (univ.image y) (fu y) (fv y))
    (hno : ¬ (NoTieAt (univ.image y) (fu y) ∨ NoTieAt (univ.image y) (fv y))) :
    IsRobustUnimodal (quad ⟪y 5, fu y⟫ ⟪y 1, fu y⟫ ⟪y 2, fu y⟫ ⟪y 3, fu y⟫) ∨
    IsRobustUnimodal (quint ⟪y 5, fv y⟫ ⟪y 0, fv y⟫ ⟪y 1, fv y⟫ ⟪y 4, fv y⟫ ⟪y 6, fv y⟫) := by
  obtain ⟨i, j, k, l', e1, e2, hind'⟩ := exists_ties_of_indepF hI hno
  obtain ⟨ties, hties, hind, hex⟩ := exists_listed_ties (vyGroup fu fv) rfl rfl e1 e2 hind'
  have hcov := hcover_of_oneTieAt (vyGroup fu fv) (vyGroup_hTv fu fv) y hyinj
    (fun a => by cases a; exact o2; exact o1) ties hties hind (fun a _ => hex a)
    (vyGroup_lab_inj fu fv)
  exact robust_rim_vy fu fv hfu hfv y hyinj vN hvN c hc hfu' hfv' hs0 hs1 ht0 ht1 hm hl hYuni
    (q := 2) le_rfl ties hties hind hcov

end Minimality

end
