module

public import Minimality.LimitRim
public import Minimality.RimHDN
public import Minimality.Perturb

@[expose] public section

set_option relaxedAutoImplicit true

/-!
# E2 (generic): the limit corner rim with robustness supplied at the limit (tt3 handoff A4)

`isRupert_or_rimHDN_of_tendsto_geom`: as `C1.isRupert_or_rimHDN_of_tendsto` (copy of
`LimitRim.isRupert_of_tendsto_rimCert`), but the approximants carry only the polygon part of the
certificate (`3 ≤ k`, strict convexity, all points weakly left: `RimGeom` of G3p), frequently, and the
robust unimodality of the labelled depths is a hypothesis **at the limit** `x` (from Lemma R2T* there),
instead of robustness at the approximants plus "no new ties".  Outcome: Rupert, or a limit corner rim
(cyclic subsequence of `lab`) with `RimCertAt`, robust, and its own horizontal double normal.
-/

set_option autoImplicit true
namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- The polygon part of `RimCertAt` (same as G3p's `RimGeom`). -/
def RimGeomG {n k : ℕ} (x : Fin n → ℝ³) (u : ℝ³) (lab : ZMod k → Fin n) : Prop :=
  3 ≤ k ∧ (∀ i j : ZMod k, j ≠ i → j ≠ i + 1 →
    0 < det3 (x (lab (i + 1)) - x (lab i)) (x (lab j) - x (lab i)) u) ∧
  ∀ (m : Fin n) (i : ZMod k), 0 ≤ det3 (x (lab (i + 1)) - x (lab i)) (x m - x (lab i)) u

theorem RimGeomG.ne_zero {n k : ℕ} {x : Fin n → ℝ³} {u : ℝ³} {lab : ZMod k → Fin n}
    (h : RimGeomG x u lab) : u ≠ 0 := by
  rintro rfl
  have := h.2.1 0 (0 - 1) (zmod_sub_one_ne h.1 0) (zmod_sub_one_ne_add_one h.1 0)
  simp [det3] at this

theorem RimGeomG.isCcwPolygon {n k : ℕ} {x : Fin n → ℝ³} {u : ℝ³} {lab : ZMod k → Fin n}
    (h : RimGeomG x u lab) {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ SO3) {r : ℝ} (hr : 0 < r)
    (hRu : R.toEuclideanLin u = r • ez) :
    IsCcwPolygon (fun i => proj_xy (R.toEuclideanLin (x (lab i)))) :=
  ⟨h.1, fun i j hi hj => by
    simp only [proj_rot_sub]; exact cross2_proj_rot_pos hR hr hRu (h.2.1 i j hi hj)⟩

theorem RimGeomG.suppIn {n k : ℕ} [NeZero k] {x : Fin n → ℝ³} {u : ℝ³} {lab : ZMod k → Fin n}
    (h : RimGeomG x u lab) (m : Fin n) : SuppIn u (fun i => x (lab i)) (x m) := by
  obtain ⟨R, hR, r, hr, hRu⟩ := exists_rotation_to_ez_pos u h.ne_zero
  have hp := h.isCcwPolygon hR hr hRu
  have hq : proj_xy (R.toEuclideanLin (x m)) ∈
      convexHull ℝ (Set.range fun i => proj_xy (R.toEuclideanLin (x (lab i)))) := by
    refine hp.mem_convexHull_of_left fun i => ?_
    have := h.2.2 m i
    rw [← cross2_proj_rot hR hRu] at this
    simp only [proj_rot_sub]
    exact nonneg_of_mul_nonneg_right (by linarith) hr
  intro w hw
  obtain ⟨y', ⟨i, rfl⟩, hle⟩ := ((innerₛₗ ℝ (proj_xy (R.toEuclideanLin w))).convexOn
    (convex_convexHull ℝ _)).exists_ge_of_mem_convexHull (subset_convexHull ℝ _) hq
  refine ⟨i, ?_⟩
  rw [inner_eq_proj_of_perp hR hr.ne' hRu hw, inner_eq_proj_of_perp hR hr.ne' hRu hw]
  simpa only [innerₛₗ_apply_apply] using hle

theorem RimGeomG.cyc_all {n k : ℕ} [NeZero k] {x : Fin n → ℝ³} {u : ℝ³}
    {lab : ZMod k → Fin n} (h : RimGeomG x u lab) {a b c : ZMod k} (hc : CycBetween a b c) :
    0 < det3 (x (lab b) - x (lab a)) (x (lab c) - x (lab a)) u := by
  obtain ⟨R, hR, r, hr, hRu⟩ := exists_rotation_to_ez_pos u h.ne_zero
  have := (h.isCcwPolygon hR hr hRu).cross2_pos_of_cycBetween hc
  rw [← cross2_proj_rot hR hRu, ← proj_rot_sub, ← proj_rot_sub]
  exact mul_pos hr this

theorem isRupert_or_rimHDN_of_tendsto_geom {n : ℕ} (x : Fin n → ℝ³)
    (hseg : ∀ i j m : Fin n, x m ≠ x i → x m ≠ x j → ∀ s : ℝ, 0 < s → s < 1 →
      x m ≠ x i + s • (x j - x i))
    (hsp : ∃ i j l m : Fin n, det3 (x j - x i) (x l - x i) (x m - x i) ≠ 0)
    {k : ℕ} [NeZero k] (lab : ZMod k → Fin n) {u : ℝ³} (hu : u ≠ 0)
    {ι : Type*} {l : Filter ι} (xs : ι → Fin n → ℝ³) (us : ι → ℝ³)
    (hxs : ∀ m, Tendsto (fun t => xs t m) l (𝓝 (x m))) (hus : Tendsto us l (𝓝 u))
    (hc : ∃ᶠ t in l, RimGeomG (xs t) (us t) lab)
    (hZ : IsRobustUnimodal (fun i => ⟪x (lab i), u⟫)) :
    IsRupert (univ.image x) ∨
      ∃ (k' : ℕ) (_ : NeZero k') (σ : ZMod k' → ZMod k),
        RimCertAt x u (lab ∘ σ) ∧ IsRobustUnimodal (fun i => ⟪x (lab (σ i)), u⟫) ∧
          ¬ NoHDNRim (fun i => x (lab (σ i))) u := by
  classical
  set X : ZMod k → ℝ³ := fun i => x (lab i) with hXdef
  -- Lemma 18.2 at `K`
  have hW : ∀ a b c, CycBetween a b c → 0 ≤ det3 (X b - X a) (X c - X a) u :=
    fun a b c h => le_of_tendsto_frequently tendsto_const_nhds
      (Tendsto.det3' ((hxs _).sub (hxs _)) ((hxs _).sub (hxs _)) hus)
      (hc.mono fun _ ht => (ht.cyc_all h).le)
  have hS : ∀ m, SuppIn u X (x m) := fun m =>
    suppIn_of_tendsto hu hus (fun i => hxs (lab i)) (hxs m) (hc.mono fun t ht => ht.suppIn m)
  -- the frame at `K`
  obtain ⟨R, hR, r, hr, hRu⟩ := exists_rotation_to_ez_pos u hu
  set P : ℝ³ → ℝ² := fun v => proj_xy (R.toEuclideanLin v) with hPdef
  have hPsub : ∀ a b, P a - P b = P (a - b) := fun a b => proj_rot_sub R a b
  have hPadd : ∀ a b, P (a + b) = P a + P b := fun a b => by
    simp only [hPdef, map_add, proj_xy_add']
  have hPsmul : ∀ (c : ℝ) a, P (c • a) = c • P a := fun c a => by
    simp only [hPdef, map_smul, proj_xy_smul']
  have hPu : P u = 0 := by
    simp only [hPdef, hRu, proj_xy_smul']
    have : proj_xy ez = 0 := by ext j; fin_cases j <;> simp [proj_xy, ez]
    rw [this, smul_zero]
  set p : ZMod k → ℝ² := fun i => P (X i) with hpdef
  have hW2 : ∀ a b c, CycBetween a b c → 0 ≤ cross2 (p b - p a) (p c - p a) := by
    intro a b c h
    have := hW a b c h
    rw [← cross2_proj_rot hR hRu, ← proj_rot_sub, ← proj_rot_sub] at this
    exact nonneg_of_mul_nonneg_right (by linarith) hr
  -- every point projects into the hull of the labels
  have hhull : ∀ m, P (x m) ∈ convexHull ℝ (Set.range p) := by
    intro m
    by_contra hnot
    obtain ⟨f, c, hfz, hfC⟩ := geometric_hahn_banach_point_closed (convex_convexHull ℝ _)
      ((Set.finite_range p).isCompact_convexHull (𝕜 := ℝ)).isClosed hnot
    have hf : ∀ z : ℝ², f z = ⟪!₂[f (EuclideanSpace.single 0 1), f (EuclideanSpace.single 1 1)],
        z⟫ := by
      intro z
      have hz : z = z 0 • EuclideanSpace.single 0 1 + z 1 • EuclideanSpace.single 1 1 := by
        ext j; fin_cases j <;> simp
      conv_lhs => rw [hz]
      rw [map_add, map_smul, map_smul]
      simp [PiLp.inner_apply, Fin.sum_univ_two, smul_eq_mul]
    obtain ⟨w, hwv, hwu, -⟩ := exists_lift_screen hR hRu
      (-!₂[f (EuclideanSpace.single 0 1), f (EuclideanSpace.single 1 1)])
    obtain ⟨i, hi⟩ := hS m w hwu
    rw [hwv, hwv, inner_neg_left, inner_neg_left, ← hf, ← hf] at hi
    have := hfC (p i) (subset_convexHull ℝ _ ⟨i, rfl⟩)
    simp only [hpdef, hXdef] at this hi
    linarith
  -- the labels are not on one line
  have hNC : ∃ a b c, cross2 (p b - p a) (p c - p a) ≠ 0 := by
    by_contra hcol
    push Not at hcol
    obtain ⟨i, j, l', m, hdet⟩ := hsp
    apply hdet
    -- a nonzero screen functional constant on the labels
    obtain ⟨ν, hν0, hν⟩ : ∃ ν : ℝ², ν ≠ 0 ∧ ∀ a, ⟪ν, p a - p 0⟫ = 0 := by
      by_cases hall : ∀ a, p a = p 0
      · refine ⟨EuclideanSpace.single 0 1, ?_, fun a => by rw [hall a, sub_self, inner_zero_right]⟩
        intro h0
        have := congrArg (fun z : ℝ² => z 0) h0
        simp at this
      push Not at hall
      obtain ⟨b, hb⟩ := hall
      refine ⟨!₂[-(p b - p 0) 1, (p b - p 0) 0], ?_, fun a => ?_⟩
      · intro h0
        apply hb
        have h0' := congrArg (fun z : ℝ² => z 0) h0
        have h1' := congrArg (fun z : ℝ² => z 1) h0
        simp at h0' h1'
        rw [← sub_eq_zero]
        ext j; fin_cases j <;> simp <;> linarith
      · rw [inner_rot_eq_cross2]; exact hcol 0 b a
    have hplane : ∀ z ∈ convexHull ℝ (Set.range p), ⟪ν, z - p 0⟫ = 0 := by
      intro z hz
      have hconv : Convex ℝ {z : ℝ² | ⟪ν, z - p 0⟫ = 0} := by
        have : {z : ℝ² | ⟪ν, z - p 0⟫ = 0} = {z : ℝ² | ⟪ν, z⟫ = ⟪ν, p 0⟫} := by
          ext z; simp only [Set.mem_setOf_eq, inner_sub_right, sub_eq_zero]
        rw [this]
        exact convex_hyperplane (innerₛₗ ℝ ν).isLinear _
      refine convexHull_min ?_ hconv hz
      rintro _ ⟨a, rfl⟩
      exact hν a
    obtain ⟨w, hwv, -, hw0⟩ := exists_lift_screen hR hRu ν
    have hperp : ∀ a b : Fin n, ⟪w, x b - x a⟫ = 0 := by
      intro a b
      have ha := hplane _ (hhull a)
      have hb := hplane _ (hhull b)
      have e : proj_xy (R.toEuclideanLin (x b - x a)) = (P (x b) - p 0) - (P (x a) - p 0) := by
        rw [← proj_rot_sub]; abel
      rw [hwv, e, inner_sub_right, ha, hb, sub_zero]
    exact det3_eq_zero_of_perp (hw0 hν0) (by rw [real_inner_comm]; exact hperp _ _)
      (by rw [real_inner_comm]; exact hperp _ _) (by rw [real_inner_comm]; exact hperp _ _)
  -- the corner rim
  obtain ⟨k', hk', σ, hσcyc, hq, hpin⟩ := exists_cornerRim p hW2 hNC
  set xc : ZMod k' → ℝ³ := fun i => X (σ i) with hxcdef
  set q : ZMod k' → ℝ² := fun i => P (xc i) with hqdef
  have hq' : IsCcwPolygon q := hq
  have hhull' : ∀ m, P (x m) ∈ convexHull ℝ (Set.range q) := fun m =>
    convexHull_min (by rintro _ ⟨i, rfl⟩; exact hpin i) (convex_convexHull ℝ _) (hhull m)
  set V := univ.image x with hVdef
  have hmem : ∀ m, x m ∈ V := fun m => mem_image_of_mem x (mem_univ m)
  set M := V.filter (fun y => ∃ a : ZMod k', ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
    y = xc a + s • (xc (a + 1) - xc a) + δ • u) with hMdef
  set D := V.filter (fun y => (∀ i, y ≠ xc i) ∧ ∃ i : ZMod k', ∃ h : ℝ, h ≠ 0 ∧
    y = xc i - h • u) with hDdef
  -- lifting from the screen
  have hlift : ∀ (y : ℝ³) (a : ZMod k') (s : ℝ), P y = q a + s • (q (a + 1) - q a) →
      ∃ δ : ℝ, y = xc a + s • (xc (a + 1) - xc a) + δ • u := by
    intro y a s h
    have h0 : P (y - xc a - s • (xc (a + 1) - xc a)) = 0 := by
      rw [← hPsub, ← hPsub, hPsmul, ← hPsub, h]; simp only [hqdef]; abel
    exact ⟨_, by rw [← eq_smul_of_proj_rot_eq_zero hR hr.ne' hRu h0]; abel⟩
  have hproj : ∀ (a : ZMod k') (s δ : ℝ),
      P (xc a + s • (xc (a + 1) - xc a) + δ • u) = q a + s • (q (a + 1) - q a) := by
    intro a s δ
    rw [hPadd, hPadd, hPsmul, hPsmul, hPu, smul_zero, add_zero, ← hPsub]
  have hxM : ∀ i, xc i ∉ M := by
    intro i hi
    obtain ⟨-, a, s, δ, hs0, hs1, -, he⟩ := mem_filter.mp hi
    have hP := congrArg P he
    rw [hproj] at hP
    have hd := hq'.edge_ne_zero a
    by_cases h1 : i = a
    · subst h1
      apply hd
      have : s • (q (i + 1) - q i) = 0 := by
        have := hP; simp only [hqdef] at this ⊢; rw [eq_comm, add_eq_left] at this; exact this
      exact (smul_eq_zero.mp this).resolve_left hs0.ne'
    by_cases h2 : i = a + 1
    · subst h2
      apply hd
      have : (1 - s) • (q (a + 1) - q a) = 0 := by
        rw [sub_smul, one_smul]
        have := hP; simp only [hqdef] at this ⊢
        rw [← sub_eq_zero] at this
        rw [← this]; abel
      exact (smul_eq_zero.mp this).resolve_left (by linarith)
    · have := hq'.2 a i h1 h2
      have e : q i - q a = s • (q (a + 1) - q a) := by
        simp only [hqdef] at hP ⊢; rw [hP]; abel
      rw [e, cross2_smul_right, cross2_self, mul_zero] at this
      exact lt_irrefl _ this
  have hin : ∀ v ∈ V, v ∉ M → v ∉ D → (∀ i, v ≠ xc i) →
      P v ∈ interior (convexHull ℝ (Set.range q)) := by
    intro v hv hvM hvD hvx
    obtain ⟨m, -, rfl⟩ := mem_image.mp hv
    rcases hq'.mem_side_of_mem_convexHull (hhull' m) with h | ⟨a, s, hs0, hs1, hside⟩
    · exact h
    exfalso
    obtain ⟨δ, hδ⟩ := hlift _ a s hside
    rcases hs0.lt_or_eq with hs0 | rfl
    · rcases hs1.lt_or_eq with hs1 | rfl
      · by_cases hδ0 : δ = 0
        · rw [hδ0, zero_smul, add_zero] at hδ
          exact hseg (lab (σ a)) (lab (σ (a + 1))) m (hvx a) (hvx (a + 1)) s hs0 hs1 hδ
        · exact hvM (mem_filter.mpr ⟨hv, a, s, δ, hs0, hs1, hδ0, hδ⟩)
      · refine hvD (mem_filter.mpr ⟨hv, hvx, a + 1, -δ, ?_, ?_⟩)
        · intro h0; apply hvx (a + 1); rw [hδ, neg_eq_zero.mp h0]; simp
        · rw [hδ]; simp only [one_smul, neg_smul, sub_neg_eq_add]; abel
    · refine hvD (mem_filter.mpr ⟨hv, hvx, a, -δ, ?_, ?_⟩)
      · intro h0; apply hvx a; rw [hδ, neg_eq_zero.mp h0]; simp
      · rw [hδ]; simp only [zero_smul, add_zero, neg_smul, sub_neg_eq_add]
  have hz : IsRobustUnimodal (fun i => (R.toEuclideanLin (xc i)) 2) := by
    have hdepth : ∀ y, (R.toEuclideanLin y) 2 = r⁻¹ * ⟪y, u⟫ := by
      intro y
      have : r * (R.toEuclideanLin y) 2 = ⟪y, u⟫ := by
        rw [← inner_ez, ← real_inner_smul_right, ← hRu, inner_toEuclideanLin_SO3 hR]
      rw [← this]; field_simp
    simp only [hdepth]
    exact (hZ.comp σ hσcyc).smul (inv_pos.mpr hr)
  by_cases hrim : NoHDNRim (fun i => x (lab (σ i))) u
  · left
    exact isRupert_of_uniform_doubles_robustUnimodal V M D R hR hr hRu xc (fun i => hmem _) hxM hq'
      hin hz (hrim R hR r hr.ne' hRu hq')
      (fun m hm => (mem_filter.mp hm).2) (fun y hy => (mem_filter.mp hy).2.2)
  · right
    have hzσ : IsRobustUnimodal (fun i => ⟪x (lab (σ i)), u⟫) := hZ.comp σ hσcyc
    refine ⟨k', hk', σ, ?_, hzσ, hrim⟩
    refine ⟨hq'.1, fun i j hi hj => ?_, fun m i => ?_, hzσ⟩
    · have := hq'.2 i j hi hj
      simp only [hqdef, hPdef, hxcdef] at this
      rw [proj_rot_sub, proj_rot_sub] at this
      rw [← cross2_proj_rot hR hRu]
      exact mul_pos hr this
    · have := hq'.left_of_mem_convexHull i (hhull' m)
      simp only [hqdef, hPdef, hxcdef] at this
      rw [proj_rot_sub, proj_rot_sub] at this
      rw [← cross2_proj_rot hR hRu]
      exact mul_nonneg hr.le this

end Minimality

#print axioms Minimality.isRupert_or_rimHDN_of_tendsto_geom
