module

public import Minimality.Type08S.C2K5ZB
public import Minimality.Type08S.C2K9K
public import Minimality.Type21Pattern

@[expose] public section


/-!
# K5Z / C: helpers for the K5 composition
* far ends at `T`, `T'` (strict, off `T ∩ T'`): `k5z_far2`, `k5z_far1`;
* `κ_b > 0` at `T` off `T'`: `k5z_kb_pos`; `κ_b = 0` with `T` or `T'` forces `T ∩ T'`: `k5z_kb0_T`, `k5z_kb0_Tp`;
* planarity in point form (`PlanarEq`) from `PlanarTwo ∨ PlanarGen`, and its invariance under the six labellings.
-/
set_option autoImplicit true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped RealInnerProductSpace Topology
open Finset Filter

namespace Minimality
namespace Type08Sp
namespace C2

/-- At `T` off `T'` the T4 far end `α1 > 1` is strict (`T4cl` gives `≤`; equality is `α1 = 1`, i.e. `T'`). -/
theorem k5z_far2 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT : IsT a' b c d)
    (hT' : ¬ IsT' a b c' d) : W.F.a'bc.f c' < W.F.a'bc.f a := by
  have h := (T4cl_of_TTp W (Or.inl hT)).2
  rcases h.lt_or_eq with h | h
  · exact h
  · exfalso; apply hT'
    have hnd := W.F.nodup
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      not_or, List.nodup_nil, and_true] at hnd
    obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
      ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
    obtain ⟨-, -, -, hc'⟩ : 0 < W.F.a'bc.f c' / W.F.a'bc.f a ∧ 0 < W.F.ab'c.f c' / W.F.ab'c.f b ∧
        1 < W.F.a'bc.f c' / W.F.a'bc.f a + W.F.ab'c.f c' / W.F.ab'c.f b ∧
        c' = d + (W.F.a'bc.f c' / W.F.a'bc.f a) • (a - d) + (W.F.ab'c.f c' / W.F.ab'c.f b) • (b - d) :=
      W.hd.perm₂₃.Qac_coords'
    have hFa := W.F.a'bc.neg a (by simp) haa' hab hac
    have ht : W.F.a'bc.f c' / W.F.a'bc.f a = 1 := by rw [h, div_self hFa.ne]
    rw [ht] at hc'
    generalize W.F.ab'c.f c' / W.F.ab'c.f b = β at hc'
    refine ⟨β, ?_⟩
    rw [hc']
    module

/-- At `T'` off `T` the T4 far end `γ6 < 1` is strict. -/
theorem k5z_far1 {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT' : IsT' a b c' d)
    (hT : ¬ IsT a' b c d) : W.F.abc'.f c < W.F.abc'.f a' := by
  have h := (T4cl_of_TTp W (Or.inr hT')).1
  rcases h.lt_or_eq with h | h
  · exact h
  · exfalso; apply hT
    have hnd := W.F.nodup
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      not_or, List.nodup_nil, and_true] at hnd
    obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
      ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd
    obtain ⟨-, -, -, ha'⟩ : 0 < W.F.ab'c.f a' / W.F.ab'c.f b ∧ 0 < W.F.abc'.f a' / W.F.abc'.f c ∧
        1 < W.F.ab'c.f a' / W.F.ab'c.f b + W.F.abc'.f a' / W.F.abc'.f c ∧
        a' = d + (W.F.ab'c.f a' / W.F.ab'c.f b) • (b - d) + (W.F.abc'.f a' / W.F.abc'.f c) • (c - d) :=
      W.hd.perm₁₂.Qac_coords'
    have hFc := W.F.abc'.neg c (by simp) (Ne.symm hac) (Ne.symm hbc) hcc'
    have ht : W.F.abc'.f a' / W.F.abc'.f c = 1 := by rw [← h, div_self hFc.ne]
    rw [ht] at ha'
    generalize W.F.ab'c.f a' / W.F.ab'c.f b = β at ha'
    refine ⟨-β, ?_⟩
    rw [ha']
    module

/-- `galeD b b' = 0` makes the equator `a a' c c'` planar (point form). -/
theorem k5z_planar_b_of_gale {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c') (G : GaleData a a' b b' c c')
    (h : galeD G.l G.m b b' = 0) : det3 (c - a) (a' - a) (c' - a) = 0 := by
  by_contra hne
  apply galeD_pair_ne_zero F.perm₁₂ G.perm₁₂ _ h
  intro h0; apply hne
  simp only [det3_expand, PiLp.sub_apply] at h0 ⊢
  linear_combination -h0

theorem k5z_planar_a_of_gale {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c') (G : GaleData a a' b b' c c')
    (h : galeD G.l G.m a a' = 0) : det3 (c - b) (b' - b) (c' - b) = 0 := by
  by_contra hne
  apply galeD_pair_ne_zero F G _ h
  intro h0; apply hne
  simp only [det3_expand, PiLp.sub_apply] at h0 ⊢
  linear_combination -h0

theorem k5z_planar_c_of_gale {a a' b b' c c' : ℝ³} (F : OctFacets a a' b b' c c') (G : GaleData a a' b b' c c')
    (h : galeD G.l G.m c c' = 0) : det3 (b - a) (a' - a) (b' - a) = 0 := by
  by_contra hne
  apply galeD_pair_ne_zero F.perm₂₃.perm₁₂ G.perm₂₃.perm₁₂ _ h
  intro h0; apply hne
  simp only [det3_expand, PiLp.sub_apply] at h0 ⊢
  linear_combination -h0

/-- `κ_b = 0` at `T` forces `T'` (`α1 = 1`). -/
theorem k5z_kb0_T {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT : IsT a' b c d)
    (hκb : det3 (c - a) (a' - a) (c' - a) = 0) : IsT' a b c' d := by
  obtain ⟨α1, α4, β1, γ4, β6, hdet, hc', hb', ha', hα1, hβ1, hαβ, hα4p, hγ4, hαγ, hβ6, -⟩ :=
    norm08w_coordsT W hT
  have e := (planar_b_iff hdet hc' ha').1 hκb
  have h1 : α1 = 1 := by
    have : β6 * (α1 - 1) = 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_left hβ6.ne'
    linarith
  refine ⟨β1, ?_⟩
  rw [hc', h1]; module

/-- `κ_b = 0` at `T'` forces `T` (`γ6 = 1`). -/
theorem k5z_kb0_Tp {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT' : IsT' a b c' d)
    (hκb : det3 (c - a) (a' - a) (c' - a) = 0) : IsT a' b c d := by
  obtain ⟨α4, β1, γ4, β6, γ6, hdet, hc', hb', ha', hβ1, hα4p, hγ4, hαγ, hβ6, hγ6, hβγ, -⟩ :=
    norm08w_coordsTp W hT'
  have e := (planar_b_iff hdet hc' ha').1 hκb
  have h1 : γ6 = 1 := by
    have : β1 * (1 - γ6) = 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_left hβ1.ne'
    linarith
  refine ⟨-β6, ?_⟩
  rw [ha', h1]; module

/-- `κ_b > 0` at `T` off `T'`. -/
theorem k5z_kb_pos {a a' b b' c c' d : ℝ³} (W : Norm08w a a' b b' c c' d) (hT : IsT a' b c d)
    (hT' : ¬ IsT' a b c' d) : 0 < galeD W.G.l W.G.m b b' := by
  rcases W.hκb.lt_or_eq with h | h
  · exact h
  · exact (hT' (k5z_kb0_T W hT (k5z_planar_b_of_gale W.F W.G h.symm))).elim

/-! ### Planarity in point form and the six labellings -/

theorem k5z_planarEq_of {a a' b b' c c' d : ℝ³} (h : PlanarTwo a a' b b' c c' ∨ PlanarGen a a' b b' c c' d) :
    PlanarEq a a' b b' c c' := by
  rcases h with h | ⟨F, -, G, hg, -⟩
  · unfold PlanarTwo at h
    unfold PlanarEq
    by_contra hn
    push Not at hn
    exact h ⟨fun h' => hn.1 h'.1, fun h' => hn.1 h'.1, fun h' => hn.2.1 h'.1⟩
  · rcases hg with hg | hg | hg
    · exact Or.inl (k5z_planar_a_of_gale F G hg)
    · exact Or.inr (Or.inl (k5z_planar_b_of_gale F G hg))
    · exact Or.inr (Or.inr (k5z_planar_c_of_gale F G hg))

theorem k5z_planarEq_perm {a a' b b' c c' : ℝ³} (h : PlanarEq a a' b b' c c') :
    PlanarEq b b' a a' c c' ∧ PlanarEq a a' c c' b b' ∧ PlanarEq c c' a a' b b' ∧
      PlanarEq b b' c c' a a' ∧ PlanarEq c c' b b' a a' := by
  unfold PlanarEq at *
  -- the three coplanarities, with the base point of each normalised
  have Pa : det3 (c - b) (b' - b) (c' - b) = 0 ↔ det3 (b - c) (c' - c) (b' - c) = 0 := by
    constructor <;> intro h0 <;> simp only [det3_expand, PiLp.sub_apply] at h0 ⊢ <;> linear_combination h0
  have Pb : det3 (c - a) (a' - a) (c' - a) = 0 ↔ det3 (a - c) (c' - c) (a' - c) = 0 := by
    constructor <;> intro h0 <;> simp only [det3_expand, PiLp.sub_apply] at h0 ⊢ <;> linear_combination h0
  have Pc : det3 (b - a) (a' - a) (b' - a) = 0 ↔ det3 (a - b) (b' - b) (a' - b) = 0 := by
    constructor <;> intro h0 <;> simp only [det3_expand, PiLp.sub_apply] at h0 ⊢ <;> linear_combination h0
  rcases h with h | h | h
  · exact ⟨Or.inr (Or.inl h), Or.inl (Pa.1 h), Or.inr (Or.inl (Pa.1 h)), Or.inr (Or.inr h),
      Or.inr (Or.inr (Pa.1 h))⟩
  · exact ⟨Or.inl h, Or.inr (Or.inr h), Or.inr (Or.inr (Pb.1 h)), Or.inl (Pb.1 h),
      Or.inr (Or.inl (Pb.1 h))⟩
  · exact ⟨Or.inr (Or.inr (Pc.1 h)), Or.inr (Or.inl h), Or.inl h, Or.inr (Or.inl (Pc.1 h)),
      Or.inl (Pc.1 h)⟩

end C2
end Type08Sp
end Minimality
