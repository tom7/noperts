module

public import Minimality.CaseC18Tests
public import Minimality.RobustCert
public import Minimality.RimCert
public import Minimality.RimHDN
public import Minimality.Type08Cases

@[expose] public section

/-!
# Type 18, acute case (c): the vertex crossing `V` as a closing at a vertex view
(`FEWER-FACES-PROOFS.md` §27, continued (3) §0, §27, continued (4) 27.51)

`Frame7.rupert_vertex`: Theorem 18.1 in its tie form at a vertex view given in frame
coordinates (`isRupert_of_vertexView_robust`): a rim cycle `c` with strictly positive screen tests,
the remaining points either strictly inside or middles over a side, robustly unimodal depths and
no horizontal double normal at the view.
-/

namespace Minimality.CaseC18

open Finset Filter Minimality.CaseC09
open scoped RealInnerProductSpace Topology

/-- The strict screen test (sign `σ`). -/
def PS (σ : ℝ) (u a b : C3) : Prop := 0 < σ * Dc a b u

theorem robust_add_const {k : ℕ} {z : ZMod k → ℝ} (hz : IsRobustUnimodal z) (a : ℝ) :
    IsRobustUnimodal (fun i => z i + a) where
  noPeaks B a' b c d hab hbc hcd hdk h := hz.noPeaks B a' b c d hab hbc hcd hdk (by
    simp only [add_lt_add_iff_right] at h; exact h)
  noTriple i j l hij hjl hil e1 e2 := hz.noTriple i j l hij hjl hil
    (add_right_cancel e1) (add_right_cancel e2)
  noLevelRun B a' b c d hab hbc hcd hdk e := by
    have := hz.noLevelRun B a' b c d hab hbc hcd hdk (add_right_cancel e)
    simp only [add_lt_add_iff_right]; exact this

namespace Frame7
variable {x : Fin 7 → ℝ³} (F : Frame7 x)

lemma fvC_lin (a u : C3) (s δ : ℝ) :
    F.fvC ⟨s * a.x + δ * u.x, s * a.y + δ * u.y, s * a.z + δ * u.z⟩ =
      s • F.fvC a + δ • F.fvC u := by
  simp only [fvC]; module

/-- **Theorem 18.1 (tie form) at a vertex view in frame coordinates**, with a level triangle rim
allowed in place of robust unimodality (it always has a horizontal double normal, which `hnd`
excludes). -/
theorem rupert_vertex_or (hx : Function.Injective x) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (c : ZMod k → Fin 7) (M : Finset (Fin 7)) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (u : C3)
    (hu : u.x ≠ 0 ∨ u.y ≠ 0 ∨ u.z ≠ 0) (hMc : ∀ m ∈ M, ∀ i, m ≠ c i)
    (hcyc : ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 →
      PS σ u ((F.ptC (c (i + 1))).sub (F.ptC (c i))) ((F.ptC (c j)).sub (F.ptC (c i))))
    (hrest : ∀ j' : Fin 7, j' ∉ M → (∀ jj, j' ≠ c jj) → ∀ i : ZMod k,
      PS σ u ((F.ptC (c (i + 1))).sub (F.ptC (c i))) ((F.ptC j').sub (F.ptC (c i))))
    (hz : IsRobustUnimodal (fun i => F.GG (F.ptC (c i)) u) ∨
      (k = 3 ∧ ∀ i j, F.GG (F.ptC (c i)) u = F.GG (F.ptC (c j)) u))
    (hnd : NoHDNAt (Finset.univ.image x) (F.fvC u))
    (hM : ∀ m ∈ M, ∃ i : ZMod k, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      (F.ptC m).x = (F.ptC (c i)).x + s * ((F.ptC (c (i + 1))).x - (F.ptC (c i)).x) + δ * u.x ∧
      (F.ptC m).y = (F.ptC (c i)).y + s * ((F.ptC (c (i + 1))).y - (F.ptC (c i)).y) + δ * u.y ∧
      (F.ptC m).z = (F.ptC (c i)).z + s * ((F.ptC (c (i + 1))).z - (F.ptC (c i)).z) + δ * u.z) :
    IsRupert (Finset.univ.image x) := by
  classical
  set u0 : ℝ³ := F.fvC u with hu0def
  have hκ := F.kap_ne
  set t := σ * F.kap with ht
  set ε : ℝ := if 0 < t then 1 else -1 with hε
  have hεs : ε = 1 ∨ ε = -1 := sgn_cases t
  have hεε : ε * ε = 1 := sgn_sq t
  have hu0 : u0 ≠ 0 := by
    intro h0
    have := F.coord_zero (a := u.x) (b := u.y) (c := u.z) (by exact h0)
    rcases hu with h | h | h
    · exact h this.1
    · exact h this.2.1
    · exact h this.2.2
  have hu' : ε • u0 ≠ 0 := by
    intro h0
    rcases hεs with h | h <;> rw [h] at h0 <;> simp at h0 <;> exact hu0 h0
  have hconv : ∀ a b : C3, 0 < σ * Dc a b u → 0 < det3 (F.fvC a) (F.fvC b) (ε • u0) := by
    intro a b h
    have hk2 : 0 < F.kap ^ 2 := by positivity
    rw [det3_smul_right, hu0def, F.det3_fvC]
    refine sgn_pos t _ ?_
    have := mul_pos hk2 h
    calc 0 < F.kap ^ 2 * (σ * Dc a b u) := this
      _ = t * (F.kap * Dc a b u) := by rw [ht]; ring
  refine isRupert_of_vertexView_robust_or (Finset.univ.image x) (M.image x) (ε • u0) hu' (k := k) hk
    (fun i => x (c i)) (fun i => Finset.mem_image_of_mem x (Finset.mem_univ _)) ?_ ?_ ?_ ?_ ?_ ?_
  · intro i hi
    obtain ⟨m, hm, hmi⟩ := Finset.mem_image.mp hi
    exact hMc m hm i (hx hmi)
  · intro i j hi hj
    show 0 < det3 (x (c (i + 1)) - x (c i)) (x (c j) - x (c i)) (ε • u0)
    rw [F.x_sub, F.x_sub]
    exact hconv _ _ (hcyc i j hi hj)
  · intro y hy hyM hyx i
    obtain ⟨j', -, rfl⟩ := Finset.mem_image.mp hy
    show 0 < det3 (x (c (i + 1)) - x (c i)) (x j' - x (c i)) (ε • u0)
    rw [F.x_sub, F.x_sub]
    exact hconv _ _ (hrest j' (fun h => hyM (Finset.mem_image_of_mem x h))
      (fun jj h => hyx jj (by simp [h])) i)
  · have hfun : (fun i : ZMod k => ε * (F.GG (F.ptC (c i)) u + ⟪F.base, u0⟫)) =
        fun i => ⟪x (c i), ε • u0⟫ := by
      funext i
      rw [real_inner_smul_right, hu0def, F.inner_x_fvC]; ring
    rcases hz with hz | ⟨hk3, hlev⟩
    · left
      have h1 := (robust_add_const hz (⟪F.base, u0⟫)).sigma hεs
      rw [← hfun]; exact h1
    · right
      refine ⟨hk3, fun i j => ?_⟩
      show ⟪x (c i), ε • u0⟫ = ⟪x (c j), ε • u0⟫
      have hi : ε * (F.GG (F.ptC (c i)) u + ⟪F.base, u0⟫) = ⟪x (c i), ε • u0⟫ := congrFun hfun i
      have hj : ε * (F.GG (F.ptC (c j)) u + ⟪F.base, u0⟫) = ⟪x (c j), ε • u0⟫ := congrFun hfun j
      rw [← hi, ← hj, hlev i j]
  · have hnd' : NoHDNAt (Finset.univ.image x) (ε • u0) := by
      rcases hεs with h | h
      · rw [h, one_smul]; exact hnd
      · rw [h, neg_one_smul]; exact hnd.neg
    exact hnd'.rim _ (fun i => Finset.mem_image_of_mem x (Finset.mem_univ _))
  · intro m hm
    obtain ⟨m0, hm0, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨i, s, δ, hs0, hs1, hδ, ex, ey, ez⟩ := hM m0 hm0
    refine ⟨i, s, ε * δ, hs0, hs1, ?_, ?_⟩
    · rcases hεs with h | h <;> rw [h] <;> simp [hδ]
    · have key : F.fvC ((F.ptC m0).sub (F.ptC (c i))) =
          s • F.fvC ((F.ptC (c (i + 1))).sub (F.ptC (c i))) + δ • u0 := by
        rw [← F.fvC_lin ((F.ptC (c (i + 1))).sub (F.ptC (c i))) u s δ]
        congr 1
        simp only [C3.sub]
        congr 1 <;> linarith
      rw [← F.x_sub, ← F.x_sub] at key
      show x m0 = x (c i) + s • (x (c (i + 1)) - x (c i)) + (ε * δ) • (ε • u0)
      rw [smul_smul, show ε * δ * ε = δ * (ε * ε) by ring, hεε, mul_one]
      have : x m0 = x (c i) + (x m0 - x (c i)) := by abel
      rw [this, key]; abel

/-- **Theorem 18.1 (tie form) at a vertex view in frame coordinates.** -/
theorem rupert_vertex (hx : Function.Injective x) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (c : ZMod k → Fin 7) (M : Finset (Fin 7)) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (u : C3)
    (hu : u.x ≠ 0 ∨ u.y ≠ 0 ∨ u.z ≠ 0) (hMc : ∀ m ∈ M, ∀ i, m ≠ c i)
    (hcyc : ∀ i j : ZMod k, j ≠ i → j ≠ i + 1 →
      PS σ u ((F.ptC (c (i + 1))).sub (F.ptC (c i))) ((F.ptC (c j)).sub (F.ptC (c i))))
    (hrest : ∀ j' : Fin 7, j' ∉ M → (∀ jj, j' ≠ c jj) → ∀ i : ZMod k,
      PS σ u ((F.ptC (c (i + 1))).sub (F.ptC (c i))) ((F.ptC j').sub (F.ptC (c i))))
    (hz : IsRobustUnimodal (fun i => F.GG (F.ptC (c i)) u))
    (hnd : NoHDNAt (Finset.univ.image x) (F.fvC u))
    (hM : ∀ m ∈ M, ∃ i : ZMod k, ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧
      (F.ptC m).x = (F.ptC (c i)).x + s * ((F.ptC (c (i + 1))).x - (F.ptC (c i)).x) + δ * u.x ∧
      (F.ptC m).y = (F.ptC (c i)).y + s * ((F.ptC (c (i + 1))).y - (F.ptC (c i)).y) + δ * u.y ∧
      (F.ptC m).z = (F.ptC (c i)).z + s * ((F.ptC (c (i + 1))).z - (F.ptC (c i)).z) + δ * u.z) :
    IsRupert (Finset.univ.image x) :=
  F.rupert_vertex_or hx hk c M σ hσ u hu hMc hcyc hrest (Or.inl hz) hnd hM

end Frame7

theorem vN4_cyc (S : Shape18) (D2n : 0 < -S.hm * S.sm * S.sp * S.tp - S.hp * S.sm * S.sp * S.tm + S.hm * S.sm * S.tp + S.hm * S.sp * S.tp + S.hp * S.sm * S.tm + S.hp * S.sp * S.tm - S.km * S.sp * S.tp - S.kp * S.sm * S.tm - S.hm * S.tp - S.hp * S.tm + S.km * S.tp + S.kp * S.tm) (Vp : 0 < -S.hm * S.sp * S.tp - S.hp * S.sp * S.tm + S.hm * S.tp + S.hp * S.tm - S.kp * S.tm) (A1z : 0 < S.hm * S.tp + S.hp * S.tm - S.hp) (A1 : 0 < S.hm * S.tp + S.hp * S.tm - S.hm) :
    ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
      PS 1 ⟨-S.sp * S.tp + S.tp, 0, -S.hp * S.sp + S.hp - S.kp⟩
        ((quad (⟨S.tp, 0, S.hp⟩ : C3) ⟨S.tm, 0, -S.hm⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ (i + 1)).sub
          (quad (⟨S.tp, 0, S.hp⟩ : C3) ⟨S.tm, 0, -S.hm⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ i))
        ((quad (⟨S.tp, 0, S.hp⟩ : C3) ⟨S.tm, 0, -S.hm⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ j).sub
          (quad (⟨S.tp, 0, S.hp⟩ : C3) ⟨S.tm, 0, -S.hm⟩ ⟨0, S.sm, -S.km⟩ ⟨0, 1, 0⟩ i)) := by
  have a1 := (mul_pos Vp S.sm_pos)
  have a2 := (mul_pos (mul_pos S.kp_pos S.sm_pos) S.tp_pos)
  have a3 := Vp
  have a4 := (mul_pos S.kp_pos S.tp_pos)
  have a5 := D2n
  have a6 := (mul_pos (mul_pos (sub_pos.2 S.sm_lt) S.kp_pos) S.tp_pos)
  have a7 := (mul_pos (mul_pos (sub_pos.2 S.sp_lt) S.km_pos) S.tp_pos)
  obtain ⟨b0, b1, b2, b3⟩ := zmod4_add_one
  intro i j h1 h2
  rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
    rcases zmod4_cases j with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [PS, Dc, C3.sub, b0, b1, b2, b3, quad_0, quad_1, quad_2, quad_3]
    linarith [a1, a2, a3, a4, a5, a6, a7]


theorem vNt_cyc (S : Shape18) (D2p : 0 < S.hm * S.sm * S.sp * S.tp + S.hp * S.sm * S.sp * S.tm - S.hm * S.sm * S.tp - S.hm * S.sp * S.tp - S.hp * S.sm * S.tm - S.hp * S.sp * S.tm + S.km * S.sp * S.tp + S.kp * S.sm * S.tm + S.hm * S.tp + S.hp * S.tm - S.km * S.tp - S.kp * S.tm) (Vp : 0 < -S.hm * S.sp * S.tp - S.hp * S.sp * S.tm + S.hm * S.tp + S.hp * S.tm - S.kp * S.tm) (A1z : 0 < S.hm * S.tp + S.hp * S.tm - S.hp) (A1 : 0 < S.hm * S.tp + S.hp * S.tm - S.hm) :
    ∀ i j : ZMod 3, j ≠ i → j ≠ i + 1 →
      PS 1 ⟨-S.sp * S.tp + S.tp, 0, -S.hp * S.sp + S.hp - S.kp⟩
        ((tri (⟨S.tp, 0, S.hp⟩ : C3) ⟨S.tm, 0, -S.hm⟩ ⟨0, 1, 0⟩ (i + 1)).sub
          (tri (⟨S.tp, 0, S.hp⟩ : C3) ⟨S.tm, 0, -S.hm⟩ ⟨0, 1, 0⟩ i))
        ((tri (⟨S.tp, 0, S.hp⟩ : C3) ⟨S.tm, 0, -S.hm⟩ ⟨0, 1, 0⟩ j).sub
          (tri (⟨S.tp, 0, S.hp⟩ : C3) ⟨S.tm, 0, -S.hm⟩ ⟨0, 1, 0⟩ i)) := by
  have a1 := Vp
  have a2 := (mul_pos S.kp_pos S.tp_pos)
  obtain ⟨b0, b1, b2⟩ := zmod3_add_one
  intro i j h1 h2
  rcases zmod3_cases i with rfl | rfl | rfl <;>
    rcases zmod3_cases j with rfl | rfl | rfl <;>
    first
    | exact absurd rfl h1
    | exact absurd (by decide) h2
    | skip
  all_goals
    simp only [PS, Dc, C3.sub, b0, b1, b2, tri_0, tri_1, tri_2]
    linarith [a1, a2]

theorem vNt_rest2 (S : Shape18) (D2p : 0 < S.hm * S.sm * S.sp * S.tp + S.hp * S.sm * S.sp * S.tm - S.hm * S.sm * S.tp - S.hm * S.sp * S.tp - S.hp * S.sm * S.tm - S.hp * S.sp * S.tm + S.km * S.sp * S.tp + S.kp * S.sm * S.tm + S.hm * S.tp + S.hp * S.tm - S.km * S.tp - S.kp * S.tm) (Vp : 0 < -S.hm * S.sp * S.tp - S.hp * S.sp * S.tm + S.hm * S.tp + S.hp * S.tm - S.kp * S.tm) (A1z : 0 < S.hm * S.tp + S.hp * S.tm - S.hp) (A1 : 0 < S.hm * S.tp + S.hp * S.tm - S.hm) :
    ∀ i : ZMod 3,
      PS 1 ⟨-S.sp * S.tp + S.tp, 0, -S.hp * S.sp + S.hp - S.kp⟩
        ((tri (⟨S.tp, 0, S.hp⟩ : C3) ⟨S.tm, 0, -S.hm⟩ ⟨0, 1, 0⟩ (i + 1)).sub
          (tri (⟨S.tp, 0, S.hp⟩ : C3) ⟨S.tm, 0, -S.hm⟩ ⟨0, 1, 0⟩ i))
        ((⟨0, S.sm, -S.km⟩ : C3).sub
          (tri (⟨S.tp, 0, S.hp⟩ : C3) ⟨S.tm, 0, -S.hm⟩ ⟨0, 1, 0⟩ i)) := by
  have a1 := (mul_pos Vp S.sm_pos)
  have a2 := (mul_pos (mul_pos S.kp_pos S.sm_pos) S.tp_pos)
  have a3 := D2p
  have a4 := (mul_pos (mul_pos (sub_pos.2 S.sm_lt) S.kp_pos) S.tp_pos)
  have a5 := (mul_pos (mul_pos (sub_pos.2 S.sp_lt) S.km_pos) S.tp_pos)
  obtain ⟨b0, b1, b2⟩ := zmod3_add_one
  intro i
  rcases zmod3_cases i with rfl | rfl | rfl <;>
  · simp only [PS, Dc, C3.sub, b0, b1, b2, tri_0, tri_1, tri_2]
    linarith [a1, a2, a3, a4, a5]


namespace Shape18
variable (S : Shape18)

/-- The view of `V`, scaled by `1 - s+`: `(t+ (1 - s+), 0, h+ (1 - s+) - k+)` (frame coordinates). -/
def uV : C3 := ⟨-S.sp * S.tp + S.tp, 0, -S.hp * S.sp + S.hp - S.kp⟩

/-- `φ(m1-)` along the view of `V`, in the normalization of `uV`. -/
noncomputable def Vp : ℝ := (1 - S.sp) * (S.hp * S.tm + S.hm * S.tp) - S.kp * S.tm
/-- `φ(xa)` along the view of `V`. -/
noncomputable def Wp : ℝ := S.hp * (1 - S.sp) - S.kp

lemma Vp_pos_iff : 0 < S.Vp ↔ 0 < (1 - S.sp) * (S.hp * S.tm + S.hm * S.tp) - S.kp * S.tm := Iff.rfl

/-- The upper middle `v` of `F1` lies over the open chord `(m1+, m1-)`. -/
lemma mid_v (hV : 0 < S.Vp) :
    ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧ 0 = S.tp + s * (S.tm - S.tp) + δ * S.uV.x ∧
      0 = S.hp + s * (-S.hm - S.hp) + δ * S.uV.z := by
  have htp := S.tp_pos; have htp1 := S.tp_lt; have htm := S.tm_pos; have hkp := S.kp_pos
  have hsp1 := S.sp_lt
  have hux : 0 < -S.sp * S.tp + S.tp := by nlinarith [mul_pos htp (sub_pos.2 hsp1)]
  have hden : 0 < S.Vp + S.tp * S.kp := by positivity
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = S.tp * S.kp / (S.Vp + S.tp * S.kp) := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hsdef]; exact div_pos (mul_pos htp hkp) hden
  have hs1 : s < 1 := by rw [hsdef, div_lt_one hden]; nlinarith
  have hPx : 0 < S.tp + s * (S.tm - S.tp) := by
    rcases le_or_gt S.tp S.tm with h | h
    · nlinarith [mul_le_mul_of_nonneg_left h hs0.le]
    · nlinarith [mul_pos hs0 (sub_pos.2 h)]
  have hs : s * (S.Vp + S.tp * S.kp) = S.tp * S.kp := by rw [hsdef]; field_simp
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = -(S.tp + s * (S.tm - S.tp)) / (-S.sp * S.tp + S.tp) := ⟨_, rfl⟩
  have hδ : δ * (-S.sp * S.tp + S.tp) = -(S.tp + s * (S.tm - S.tp)) := by
    rw [hδdef]; exact div_mul_cancel₀ _ hux.ne'
  refine ⟨s, δ, hs0, hs1, ?_, ?_, ?_⟩
  · rw [hδdef]; exact div_ne_zero (by linarith) hux.ne'
  · simp only [uV]; linarith
  · apply mul_left_cancel₀ hux.ne'
    simp only [uV, Vp] at hs hδ ⊢
    linear_combination (-(-S.hp * S.sp + S.hp - S.kp)) * hδ + hs

/-- The lower middle `xa` of `F1` lies over the open chord `(m1+, m1-)`. -/
lemma mid_xa (hV : 0 < S.Vp) (hW : S.Wp < S.Vp) :
    ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧ 1 = S.tp + s * (S.tm - S.tp) + δ * S.uV.x ∧
      0 = S.hp + s * (-S.hm - S.hp) + δ * S.uV.z := by
  have htp := S.tp_pos; have htp1 := S.tp_lt; have htm := S.tm_pos; have htm1 := S.tm_lt
  have hkp := S.kp_pos; have hsp1 := S.sp_lt
  have hux : 0 < -S.sp * S.tp + S.tp := by nlinarith [mul_pos htp (sub_pos.2 hsp1)]
  have hden : 0 < S.Vp + S.tp * S.kp := by positivity
  have hr : 0 < S.Wp + S.tp * S.kp := by
    have := S.roof_p'; unfold Wp; nlinarith
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = (S.Wp + S.tp * S.kp) / (S.Vp + S.tp * S.kp) := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hsdef]; exact div_pos hr hden
  have hs1 : s < 1 := by rw [hsdef, div_lt_one hden]; linarith
  have hPx : S.tp + s * (S.tm - S.tp) < 1 := by
    rcases le_or_gt S.tp S.tm with h | h
    · nlinarith [mul_le_mul_of_nonneg_left h hs0.le]
    · nlinarith [mul_pos hs0 (sub_pos.2 h)]
  have hs : s * (S.Vp + S.tp * S.kp) = S.Wp + S.tp * S.kp := by rw [hsdef]; field_simp
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = (1 - (S.tp + s * (S.tm - S.tp))) / (-S.sp * S.tp + S.tp) :=
    ⟨_, rfl⟩
  have hδ : δ * (-S.sp * S.tp + S.tp) = 1 - (S.tp + s * (S.tm - S.tp)) := by
    rw [hδdef]; exact div_mul_cancel₀ _ hux.ne'
  refine ⟨s, δ, hs0, hs1, ?_, ?_, ?_⟩
  · rw [hδdef]; exact div_ne_zero (by linarith) hux.ne'
  · simp only [uV]; linarith
  · apply mul_left_cancel₀ hux.ne'
    simp only [uV, Vp, Wp] at hs hδ ⊢
    linear_combination (-(-S.hp * S.sp + S.hp - S.kp)) * hδ + hs

/-- The upper middle `m2+` of `Δ` lies over the open side `(xb, m1+)`. -/
lemma mid_m2p :
    ∃ s δ : ℝ, 0 < s ∧ s < 1 ∧ δ ≠ 0 ∧ 0 = 0 + s * (S.tp - 0) + δ * S.uV.x ∧
      S.sp = 1 + s * (0 - 1) + δ * S.uV.y ∧ S.kp = 0 + s * (S.hp - 0) + δ * S.uV.z := by
  have htp := S.tp_pos; have hsp1 := S.sp_lt; have hsp := S.sp_pos
  refine ⟨1 - S.sp, -1, by linarith, by linarith, by norm_num, ?_, ?_, ?_⟩
  · simp only [uV]; ring
  · simp only [uV]; ring
  · simp only [uV]; ring

end Shape18

theorem quadTie_of_nws {z0 z1 z2 z3 : ℝ} (hA : z0 < z1 ∨ z0 < z3 ∨ z2 < z1 ∨ z2 < z3)
    (hB : z1 < z0 ∨ z3 < z0 ∨ z1 < z2 ∨ z3 < z2) : QuadTie z0 z1 z2 z3 := by
  unfold QuadTie
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨e1, e2⟩
    rcases hA with h | h | h | h <;> rcases hB with k | k | k | k <;> linarith
  · rintro ⟨e1, e2⟩
    rcases hA with h | h | h | h <;> rcases hB with k | k | k | k <;> linarith
  · rintro ⟨e1, e2⟩
    rcases hA with h | h | h | h <;> rcases hB with k | k | k | k <;> linarith
  · rintro ⟨e1, e2⟩
    rcases hA with h | h | h | h <;> rcases hB with k | k | k | k <;> linarith
  all_goals
    rintro ⟨e1, e2, e3⟩
    rcases hA with h | h | h | h <;> rcases hB with k | k | k | k <;> linarith

theorem robust_quad_of_nws {z0 z1 z2 z3 : ℝ} (hA : z0 < z1 ∨ z0 < z3 ∨ z2 < z1 ∨ z2 < z3)
    (hB : z1 < z0 ∨ z3 < z0 ∨ z1 < z2 ∨ z3 < z2) : IsRobustUnimodal (quad z0 z1 z2 z3) := by
  refine isRobustUnimodal_quad (quadTie_of_nws hA hB) ?_ ?_
  · intro h
    simp only [max_lt_iff, lt_min_iff] at h
    rcases hA with k | k | k | k <;> linarith [h.1.1, h.1.2, h.2.1, h.2.2]
  · intro h
    simp only [max_lt_iff, lt_min_iff] at h
    rcases hB with k | k | k | k <;> linarith [h.1.1, h.1.2, h.2.1, h.2.2]

namespace Shape18
variable (S : Shape18)

/-- The sign of the border `D2` between the rims of `V` (`D2 = tp tm (1-sp)(1-sm) (A1 - μ+ - μ-)`,
cleared of denominators). -/
noncomputable def D2p : ℝ :=
  (1 - S.sm) * (1 - S.sp) * (S.hm * S.tp + S.hp * S.tm) - S.km * S.tp * (1 - S.sp) -
    S.kp * S.tm * (1 - S.sm)

end Shape18

namespace Frame18
variable {x : Fin 7 → ℝ³} (F : Frame18 x)

lemma ptC_0 : F.toFrame7.ptC 0 = ⟨F.S.tp, 0, F.S.hp⟩ := by simp [toFrame7, pt]
lemma ptC_1 : F.toFrame7.ptC 1 = ⟨0, F.S.sp, F.S.kp⟩ := by simp [toFrame7, pt]
lemma ptC_2 : F.toFrame7.ptC 2 = ⟨0, F.S.sm, -F.S.km⟩ := by simp [toFrame7, pt]
lemma ptC_3 : F.toFrame7.ptC 3 = ⟨1, 0, 0⟩ := by simp [toFrame7, pt]
lemma ptC_4 : F.toFrame7.ptC 4 = ⟨0, 1, 0⟩ := by simp [toFrame7, pt]
lemma ptC_5 : F.toFrame7.ptC 5 = ⟨0, 0, 0⟩ := by simp [toFrame7, pt]
lemma ptC_6 : F.toFrame7.ptC 6 = ⟨F.S.tm, 0, -F.S.hm⟩ := by simp [toFrame7, pt]

/-- The depth of the point `j` along the view of `V`. -/
noncomputable def dV (j : Fin 7) : ℝ := F.toFrame7.GG (F.toFrame7.ptC j) F.S.uV

lemma dV_0 : F.dV 0 = F.a11 * (F.S.tp * (-F.S.sp * F.S.tp + F.S.tp)) +
    F.gg * (F.S.hp * (-F.S.hp * F.S.sp + F.S.hp - F.S.kp)) := by
  simp only [dV, ptC_0, GG_eq, Shape18.uV]; ring
lemma dV_6 : F.dV 6 = F.a11 * (F.S.tm * (-F.S.sp * F.S.tp + F.S.tp)) +
    F.gg * (-F.S.hm * (-F.S.hp * F.S.sp + F.S.hp - F.S.kp)) := by
  simp only [dV, ptC_6, GG_eq, Shape18.uV]; ring
lemma dV_2 : F.dV 2 = F.a12 * (F.S.sm * (-F.S.sp * F.S.tp + F.S.tp)) +
    F.gg * (-F.S.km * (-F.S.hp * F.S.sp + F.S.hp - F.S.kp)) := by
  simp only [dV, ptC_2, GG_eq, Shape18.uV]; ring
lemma dV_4 : F.dV 4 = F.a12 * (-F.S.sp * F.S.tp + F.S.tp) := by
  simp only [dV, ptC_4, GG_eq, Shape18.uV]; ring

/-- `Φ2` is empty for `V` (27.54, type 18): the diagonal `{m1+, m2-}` is never weakly above
`{m1-, xb}`. -/
theorem vN4_A (hD : 0 < F.S.Vp) :
    F.dV 0 < F.dV 6 ∨ F.dV 0 < F.dV 4 ∨ F.dV 2 < F.dV 6 ∨ F.dV 2 < F.dV 4 := by
  have htp := F.S.tp_pos; have htp1 := F.S.tp_lt; have htm := F.S.tm_pos; have htm1 := F.S.tm_lt
  have hsp := F.S.sp_pos; have hsp1 := F.S.sp_lt; have hsm := F.S.sm_pos; have hsm1 := F.S.sm_lt
  have hhp := F.S.hp_pos; have hhm := F.S.hm_pos; have hkp := F.S.kp_pos; have hkm := F.S.km_pos
  have hgg : 0 < F.gg := F.g_pos
  have hA11 : 0 < F.a11 := lt_of_lt_of_le F.A12_pos F.A12_le_A11
  have hA12 : 0 < F.a12 := F.A12_pos
  have rm := F.S.roof_m'
  have ux : 0 < -F.S.sp * F.S.tp + F.S.tp := by nlinarith [mul_pos htp (sub_pos.2 hsp1)]
  by_contra hc
  push Not at hc
  obtain ⟨c1, c2, c3, c4⟩ := hc
  rw [F.dV_0, F.dV_6] at c1
  rw [F.dV_2, F.dV_6] at c3
  rw [F.dV_2, F.dV_4] at c4
  rcases le_or_gt 0 (-F.S.hp * F.S.sp + F.S.hp - F.S.kp) with hW | hW
  · -- `Wp ≥ 0`: `m2- < xb`
    nlinarith [mul_pos (mul_pos hA12 ux) (sub_pos.2 hsm1),
      mul_nonneg (mul_pos hgg hkm).le hW]
  rcases le_or_gt F.S.tp F.S.tm with htt | htt
  · -- `t+ ≤ t-` : `m1+ < m1-`
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 htt) ux.le) hA11.le,
      mul_pos (mul_pos hgg (add_pos hhp hhm)) (neg_pos.2 hW)]
  · -- `t- < t+`
    have hBr : 0 < F.S.tm * (1 - F.S.sm) * (F.S.hp + F.S.hm) +
        (F.S.tp - F.S.tm) * ((1 - F.S.sm) * F.S.hm - F.S.km) := by
      rcases le_or_gt 0 ((1 - F.S.sm) * F.S.hm - F.S.km) with h | h
      · nlinarith [mul_pos (mul_pos htm (sub_pos.2 hsm1)) (add_pos hhp hhm),
          mul_nonneg (sub_pos.2 htt).le h]
      · nlinarith [mul_pos (mul_pos htm (sub_pos.2 hsm1)) hhp,
          mul_pos (sub_pos.2 htt) (neg_pos.2 h), mul_pos htm (sub_pos.2 hsm1),
          mul_pos (sub_pos.2 htm1) (neg_pos.2 h), mul_pos (sub_pos.2 htp1) hhm]
    nlinarith [mul_nonneg (mul_pos htm (sub_pos.2 hsm1)).le (sub_nonneg.2 c1),
      mul_nonneg (mul_nonneg (sub_pos.2 htt).le (sub_pos.2 hsm1).le) (sub_nonneg.2 c3),
      mul_nonneg (mul_nonneg (sub_pos.2 htt).le hsm.le) (sub_nonneg.2 c4),
      mul_pos (mul_pos hgg (neg_pos.2 hW)) hBr]

end Frame18

namespace Frame18
variable {x : Fin 7 → ℝ³} (F : Frame18 x)

/-- **`V` with the 4-cycle rim `(m1+, m1-, m2-, xb)`** (class N4, non-realizable): Rupert once
the diagonals `{m1+, m2-}`, `{m1-, xb}` are not weakly separated the other way (`hB`, which the
pair with `T_A` supplies) and `V` has no horizontal double normal. -/
theorem vN4_rupert (hx : Function.Injective x) (hD2 : F.S.D2p < 0) (hV : 0 < F.S.Vp)
    (hA1z : 0 < F.S.hm * F.S.tp - F.S.hp * (1 - F.S.tm))
    (hA1 : 0 < F.S.hp * F.S.tm - F.S.hm * (1 - F.S.tp))
    (hnd : NoHDNAt (Finset.univ.image x) (F.toFrame7.fvC F.S.uV))
    (hB : F.dV 6 < F.dV 0 ∨ F.dV 4 < F.dV 0 ∨ F.dV 6 < F.dV 2 ∨ F.dV 4 < F.dV 2) :
    IsRupert (Finset.univ.image x) := by
  have htp := F.S.tp_pos; have hsp1 := F.S.sp_lt
  have ux : 0 < -F.S.sp * F.S.tp + F.S.tp := by nlinarith [mul_pos htp (sub_pos.2 hsp1)]
  have hD2' : 0 < -F.S.hm * F.S.sm * F.S.sp * F.S.tp - F.S.hp * F.S.sm * F.S.sp * F.S.tm +
      F.S.hm * F.S.sm * F.S.tp + F.S.hm * F.S.sp * F.S.tp + F.S.hp * F.S.sm * F.S.tm +
      F.S.hp * F.S.sp * F.S.tm - F.S.km * F.S.sp * F.S.tp - F.S.kp * F.S.sm * F.S.tm -
      F.S.hm * F.S.tp - F.S.hp * F.S.tm + F.S.km * F.S.tp + F.S.kp * F.S.tm := by
    unfold Shape18.D2p at hD2; linarith
  have hV' : 0 < -F.S.hm * F.S.sp * F.S.tp - F.S.hp * F.S.sp * F.S.tm + F.S.hm * F.S.tp +
      F.S.hp * F.S.tm - F.S.kp * F.S.tm := by unfold Shape18.Vp at hV; linarith
  have hA1z' : 0 < F.S.hm * F.S.tp + F.S.hp * F.S.tm - F.S.hp := by linarith
  have hA1' : 0 < F.S.hm * F.S.tp + F.S.hp * F.S.tm - F.S.hm := by linarith
  have hc : ∀ i, F.toFrame7.ptC (quad 0 6 2 4 i) =
      quad (⟨F.S.tp, 0, F.S.hp⟩ : C3) ⟨F.S.tm, 0, -F.S.hm⟩ ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 1, 0⟩ i := by
    intro i
    rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp [quad_0, quad_1, quad_2, quad_3, ptC_0, ptC_6, ptC_2, ptC_4]
  have hAq := F.vN4_A hV
  refine F.toFrame7.rupert_vertex hx (k := 4) (by norm_num) (quad 0 6 2 4) {5, 3, 1} 1
    (Or.inl rfl) F.S.uV (Or.inl (by simpa [Shape18.uV] using ux.ne')) ?_ ?_ ?_ ?_ hnd ?_
  · intro m hm i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl <;> rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
      simp [quad_0, quad_1, quad_2, quad_3]
  · intro i j h1 h2
    simp only [hc]
    exact vN4_cyc F.S hD2' hV' hA1z' hA1' i j h1 h2
  · intro j' hj' hjc i
    exfalso
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj'
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hjc 0 (by simp [quad_0])
    · exact hj'.2.2 rfl
    · exact hjc 2 (by simp [quad_2])
    · exact hj'.2.1 rfl
    · exact hjc 3 (by simp [quad_3])
    · exact hj'.1 rfl
    · exact hjc 1 (by simp [quad_1])
  · have hf : (fun i => F.toFrame7.GG (F.toFrame7.ptC (quad 0 6 2 4 i)) F.S.uV) =
        quad (F.dV 0) (F.dV 6) (F.dV 2) (F.dV 4) := by
      funext i
      rcases zmod4_cases i with rfl | rfl | rfl | rfl <;>
        simp [quad_0, quad_1, quad_2, quad_3, dV]
    rw [hf]
    exact robust_quad_of_nws hAq hB
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl
    · obtain ⟨s, δ, hs0, hs1, hδ, ex, ez⟩ := F.S.mid_v hV
      refine ⟨0, s, δ, hs0, hs1, hδ, ?_, ?_, ?_⟩ <;>
        simp [quad_0, quad_1, ptC_5, ptC_0, ptC_6, Shape18.uV] at ex ez ⊢ <;> linarith
    · obtain ⟨s, δ, hs0, hs1, hδ, ex, ez⟩ := F.S.mid_xa hV (by
        unfold Shape18.Wp Shape18.Vp
        have := F.S.roof_p'
        nlinarith [mul_pos hA1z (sub_pos.2 (F.S.sp_lt)), F.S.kp_pos, F.S.tm_lt, F.S.tm_pos])
      refine ⟨0, s, δ, hs0, hs1, hδ, ?_, ?_, ?_⟩ <;>
        simp [quad_0, quad_1, ptC_3, ptC_0, ptC_6, Shape18.uV] at ex ez ⊢ <;> linarith
    · obtain ⟨s, δ, hs0, hs1, hδ, ex, ey, ez⟩ := F.S.mid_m2p
      have a3 : (3 : ZMod 4) + 1 = 0 := by decide
      refine ⟨3, s, δ, hs0, hs1, hδ, ?_, ?_, ?_⟩ <;>
        simp [a3, quad_0, quad_3, hc, ptC_1, ptC_0, ptC_4, Shape18.uV] at ex ey ez ⊢ <;> linarith

end Frame18

namespace Frame18
variable {x : Fin 7 → ℝ³} (F : Frame18 x)

/-- **`V` with the triangle rim `(m1+, m1-, xb)`** (class Ntri, non-realizable, `m2-` inside):
Rupert unless `V` has a horizontal double normal (three equal depths give one). -/
theorem vNt_rupert (hx : Function.Injective x) (hD2 : 0 < F.S.D2p) (hV : 0 < F.S.Vp)
    (hA1z : 0 < F.S.hm * F.S.tp - F.S.hp * (1 - F.S.tm))
    (hA1 : 0 < F.S.hp * F.S.tm - F.S.hm * (1 - F.S.tp))
    (hnd : NoHDNAt (Finset.univ.image x) (F.toFrame7.fvC F.S.uV)) :
    IsRupert (Finset.univ.image x) := by
  have htp := F.S.tp_pos; have hsp1 := F.S.sp_lt
  have ux : 0 < -F.S.sp * F.S.tp + F.S.tp := by nlinarith [mul_pos htp (sub_pos.2 hsp1)]
  have hD2' : 0 < F.S.hm * F.S.sm * F.S.sp * F.S.tp + F.S.hp * F.S.sm * F.S.sp * F.S.tm -
      F.S.hm * F.S.sm * F.S.tp - F.S.hm * F.S.sp * F.S.tp - F.S.hp * F.S.sm * F.S.tm -
      F.S.hp * F.S.sp * F.S.tm + F.S.km * F.S.sp * F.S.tp + F.S.kp * F.S.sm * F.S.tm +
      F.S.hm * F.S.tp + F.S.hp * F.S.tm - F.S.km * F.S.tp - F.S.kp * F.S.tm := by
    unfold Shape18.D2p at hD2; linarith
  have hV' : 0 < -F.S.hm * F.S.sp * F.S.tp - F.S.hp * F.S.sp * F.S.tm + F.S.hm * F.S.tp +
      F.S.hp * F.S.tm - F.S.kp * F.S.tm := by unfold Shape18.Vp at hV; linarith
  have hA1z' : 0 < F.S.hm * F.S.tp + F.S.hp * F.S.tm - F.S.hp := by linarith
  have hA1' : 0 < F.S.hm * F.S.tp + F.S.hp * F.S.tm - F.S.hm := by linarith
  have hc : ∀ i, F.toFrame7.ptC (tri 0 6 4 i) =
      tri (⟨F.S.tp, 0, F.S.hp⟩ : C3) ⟨F.S.tm, 0, -F.S.hm⟩ ⟨0, 1, 0⟩ i := by
    intro i
    rcases zmod3_cases i with rfl | rfl | rfl <;>
      simp [tri_0, tri_1, tri_2, ptC_0, ptC_6, ptC_4]
  refine F.toFrame7.rupert_vertex_or hx (k := 3) (by norm_num) (tri 0 6 4) {5, 3, 1} 1
    (Or.inl rfl) F.S.uV (Or.inl (by simpa [Shape18.uV] using ux.ne')) ?_ ?_ ?_ ?_ hnd ?_
  · intro m hm i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl <;> rcases zmod3_cases i with rfl | rfl | rfl <;>
      simp [tri_0, tri_1, tri_2]
  · intro i j h1 h2
    simp only [hc]
    exact vNt_cyc F.S hD2' hV' hA1z' hA1' i j h1 h2
  · intro j' hj' hjc i
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj'
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (by simp [tri_0]) (hjc 0)
    · exact absurd rfl hj'.2.2
    · simp only [hc]; rw [ptC_2]; exact vNt_rest2 F.S hD2' hV' hA1z' hA1' i
    · exact absurd rfl hj'.2.1
    · exact absurd (by simp [tri_2]) (hjc 2)
    · exact absurd rfl hj'.1
    · exact absurd (by simp [tri_1]) (hjc 1)
  · have hf : (fun i => F.toFrame7.GG (F.toFrame7.ptC (tri 0 6 4 i)) F.S.uV) =
        tri (F.dV 0) (F.dV 6) (F.dV 4) := by
      funext i
      rcases zmod3_cases i with rfl | rfl | rfl <;> simp [tri_0, tri_1, tri_2, dV]
    by_cases hlev : F.dV 0 = F.dV 6 ∧ F.dV 6 = F.dV 4
    · right
      refine ⟨rfl, fun i j => ?_⟩
      have e : ∀ i, F.toFrame7.GG (F.toFrame7.ptC (tri 0 6 4 i)) F.S.uV =
          tri (F.dV 0) (F.dV 6) (F.dV 4) i := fun i => congrFun hf i
      rw [e i, e j]
      rcases zmod3_cases i with rfl | rfl | rfl <;> rcases zmod3_cases j with rfl | rfl | rfl <;>
        simp only [tri_0, tri_1, tri_2] <;> linarith [hlev.1, hlev.2]
    · left
      rw [hf]
      exact isRobustUnimodal_three hlev
  · intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl
    · obtain ⟨s, δ, hs0, hs1, hδ, ex, ez⟩ := F.S.mid_v hV
      refine ⟨0, s, δ, hs0, hs1, hδ, ?_, ?_, ?_⟩ <;>
        simp [tri_0, tri_1, hc, ptC_5, ptC_0, ptC_6, Shape18.uV] at ex ez ⊢ <;> linarith
    · obtain ⟨s, δ, hs0, hs1, hδ, ex, ez⟩ := F.S.mid_xa hV (by
        unfold Shape18.Wp Shape18.Vp
        have := F.S.roof_p'
        nlinarith [mul_pos hA1z (sub_pos.2 (F.S.sp_lt)), F.S.kp_pos, F.S.tm_lt, F.S.tm_pos])
      refine ⟨0, s, δ, hs0, hs1, hδ, ?_, ?_, ?_⟩ <;>
        simp [tri_0, tri_1, hc, ptC_3, ptC_0, ptC_6, Shape18.uV] at ex ez ⊢ <;> linarith
    · obtain ⟨s, δ, hs0, hs1, hδ, ex, ey, ez⟩ := F.S.mid_m2p
      have a2 : (2 : ZMod 3) + 1 = 0 := by decide
      refine ⟨2, s, δ, hs0, hs1, hδ, ?_, ?_, ?_⟩ <;>
        simp [a2, tri_0, tri_2, hc, ptC_1, ptC_0, ptC_4, Shape18.uV] at ex ey ez ⊢ <;> linarith

end Frame18

namespace Frame18
variable {x : Fin 7 → ℝ³} (F : Frame18 x)

/-- The depth of the point `j` along the view of `T_A` (`m1+ - xa`). -/
noncomputable def dA (j : Fin 7) : ℝ := F.toFrame7.GG (F.toFrame7.ptC j) ⟨F.S.tp - 1, 0, F.S.hp⟩

lemma dA_0 : F.dA 0 = F.a11 * (F.S.tp * (F.S.tp - 1)) + F.gg * (F.S.hp * F.S.hp) := by
  simp only [dA, ptC_0, GG_eq]; ring
lemma dA_4 : F.dA 4 = F.a12 * (F.S.tp - 1) := by
  simp only [dA, ptC_4, GG_eq]; ring

/-- **`T_A`** (the edge crossing at `m1+ xa`, apex `m1+`, rim `(m1+, xb, m2-, v)`; family `A`'s `T1`
without the sign of `⟨u₁, u₂⟩`): either `K` is Rupert, or `T_A` is in its closed failure set:
`xb` and `v` weakly above `m1+` and `m2-` along the view. -/
theorem tA_or (hx : Function.Injective x) (A1 : F.S.hm * (1 - F.S.tp) < F.S.hp * F.S.tm) :
    IsRupert (Finset.univ.image x) ∨
      (F.dA 0 ≤ F.dA 4 ∧ F.dA 0 ≤ F.dA 5 ∧ F.dA 2 ≤ F.dA 4 ∧ F.dA 2 ≤ F.dA 5) := by
  by_cases hB : F.dA 4 < F.dA 0 ∨ F.dA 5 < F.dA 0 ∨ F.dA 4 < F.dA 2 ∨ F.dA 5 < F.dA 2
  swap
  · right
    push Not at hB
    obtain ⟨h1, h2, h3, h4⟩ := hB
    exact ⟨h1, h2, h3, h4⟩
  left
  have hsm := F.S.sm_pos; have htp := F.S.tp_pos; have htp1 := F.S.tp_lt
  have hhp := F.S.hp_pos; have hkm := F.S.km_pos; have hgg : 0 < F.gg := F.g_pos
  have hA11 : 0 < F.a11 := lt_of_lt_of_le F.A12_pos F.A12_le_A11
  have p0 : F.toFrame7.ptC 0 = ⟨F.S.tp, 0, F.S.hp⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p1 : F.toFrame7.ptC 1 = ⟨0, F.S.sp, F.S.kp⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p2 : F.toFrame7.ptC 2 = ⟨0, F.S.sm, -F.S.km⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p3 : F.toFrame7.ptC 3 = ⟨1, 0, 0⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p4 : F.toFrame7.ptC 4 = ⟨0, 1, 0⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p5 : F.toFrame7.ptC 5 = ⟨0, 0, 0⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  have p6 : F.toFrame7.ptC 6 = ⟨F.S.tm, 0, -F.S.hm⟩ := by simp [Frame18.toFrame7, Frame18.pt]
  refine F.toFrame7.rupert_rim4 0 4 2 5 ⟨F.S.tp, 0, F.S.hp⟩ ⟨0, 1, 0⟩ ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 0, 0⟩
    p0 p4 p2 p5 1 (Or.inl rfl) ⟨F.S.tp - 1, 0, F.S.hp⟩
    ⟨-2 * F.S.tp, 1, -2 * F.S.hp⟩ (Or.inl (sub_ne_zero.2 htp1.ne)) ?_ ?_ ?_
  · exact tA1_cyc F.S A1
  · intro j' h0 h1 h2 h3 i
    rcases fin7_cases j' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl h0
    · rw [p1]; exact tA1_rest1 F.S A1 i
    · exact absurd rfl h2
    · rw [p3]; exact tA1_rest3 F.S A1 i
    · exact absurd rfl h1
    · exact absurd rfl h3
    · rw [p6]; exact tA1_rest6 F.S A1 i
  · set Pq : ZMod 4 → C3 := quad ⟨F.S.tp, 0, F.S.hp⟩ ⟨0, 1, 0⟩ ⟨0, F.S.sm, -F.S.km⟩ ⟨0, 0, 0⟩ with hPq
    set zz : ZMod 4 → ℝ := fun i => F.toFrame7.GG (Pq i) ⟨F.S.tp - 1, 0, F.S.hp⟩ with hzz
    set ww : ZMod 4 → ℝ := fun i => F.toFrame7.GG (Pq i) ⟨-2 * F.S.tp, 1, -2 * F.S.hp⟩ with hww
    have e0 : zz 0 = F.dA 0 := by simp [hzz, hPq, quad_0, dA, p0]
    have e1 : zz 1 = F.dA 4 := by simp [hzz, hPq, quad_1, dA, p4]
    have e2 : zz 2 = F.dA 2 := by simp [hzz, hPq, quad_2, dA, p2]
    have e3 : zz 3 = F.dA 5 := by simp [hzz, hPq, quad_3, dA, p5]
    refine Q4_eventually (z := zz) (w := ww)
      (A_lex4 (p := F.S.hp * F.S.sm) (q := F.S.hp + (1 - F.S.tp) * F.S.km - F.S.hp * F.S.sm)
        (r := F.S.hp) (s := (1 - F.S.tp) * F.S.km) (mul_pos hhp hsm)
        (by nlinarith [F.S.sm_lt, mul_pos (sub_pos.2 htp1) hkm]) hhp (mul_pos (sub_pos.2 htp1) hkm)
        (by ring) ?_) ?_
    · simp only [hzz, hPq, GG_eq, quad_0, quad_1, quad_2, quad_3]
      nlinarith [mul_pos (mul_pos F.S.km_pos htp) (add_pos (mul_pos (mul_pos (sub_pos.2 htp1) (sub_pos.2 htp1)) hA11) (mul_pos (mul_pos hhp hhp) hgg))]
    · rw [e0, e1, e2, e3]
      rcases hB with h | h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl (Or.inl h))
      · exact Or.inr (Or.inr (Or.inl (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

end Frame18

namespace Frame18
variable {x : Fin 7 → ℝ³} (F : Frame18 x)

lemma dV_pos_of (hVp : F.S.dp < F.S.A1 * F.S.tp) : 0 < F.S.Vp := by
  have htm := F.S.tm_pos; have hsp1 := F.S.sp_lt
  have e1 := F.S.ap_mul; have e2 := F.S.am_mul; have e3 := F.S.dp_mul
  have h := mul_lt_mul_of_pos_right hVp (mul_pos htm (sub_pos.2 hsp1))
  have e4 : F.S.dp * (F.S.tm * (1 - F.S.sp)) = F.S.kp * F.S.tm := by rw [← e3]; ring
  have e5 : F.S.A1 * F.S.tp * (F.S.tm * (1 - F.S.sp)) =
      (1 - F.S.sp) * (F.S.hp * F.S.tm + F.S.hm * F.S.tp) := by
    unfold Shape18.A1
    rw [← e1, ← e2]; ring
  unfold Shape18.Vp
  nlinarith

/-- **The `V` side of 27.59 (b), (c)** (class N4 or Ntri, non-realizable): with `a- < b+`,
`a+ < b-` and `μ+ < A1`, `K` is Rupert off the border `D2 = 0`, a horizontal double normal of
`V` at its view. -/
theorem Vside (hx : Function.Injective x) (hVp : F.S.dp < F.S.A1 * F.S.tp)
    (h1 : F.S.am < F.S.bp) (h2 : F.S.ap < F.S.bm) (hD2 : F.S.D2p ≠ 0)
    (hnd : NoHDNAt (Finset.univ.image x) (F.toFrame7.fvC F.S.uV)) :
    IsRupert (Finset.univ.image x) := by
  have htp := F.S.tp_pos; have htp1 := F.S.tp_lt; have hsp1 := F.S.sp_lt
  have hV := F.dV_pos_of hVp
  have hA1 := sub_pos.2 (F.A1_of h1)
  have hA1z : 0 < F.S.hm * F.S.tp - F.S.hp * (1 - F.S.tm) := sub_pos.2 (F.zFrame.A1_of h2)
  rcases lt_or_gt_of_ne hD2 with hneg | hpos
  · rcases F.tA_or hx (F.A1_of h1) with h | ⟨f1, f2, f3, f4⟩
    · exact h
    · refine F.vN4_rupert hx hneg hV hA1z hA1 hnd ?_
      by_contra hc
      push Not at hc
      obtain ⟨c1, c2, c3, c4⟩ := hc
      rw [F.dA_0, F.dA_4] at f1
      rw [F.dV_0, F.dV_4] at c2
      have hgg : 0 < F.gg := F.g_pos
      have hroof := F.S.roof_p'
      nlinarith [mul_nonneg (mul_pos htp (sub_pos.2 hsp1)).le (sub_nonneg.2 f1),
        mul_nonneg (sub_pos.2 htp1).le (sub_nonneg.2 c2),
        mul_pos (mul_pos hgg F.S.hp_pos) (sub_pos.2 hroof)]
  · exact F.vNt_rupert hx hpos hV hA1z hA1 hnd

end Frame18


end Minimality.CaseC18

end
