module

public import Minimality.Type08Cases

@[expose] public section

/-!
# Type 08: the T4 case of Theorem 10.1 (Lemma 5 of `FEWER-FACES-PROOFS.md` §10)

At the view along the QQ edge `d b`, with far ends `c'` (of `Q_ab`) and `c` (of
`Q_bc`), the middles are `a` and `a'`, and `K_v ⊂ K − a` (a T4).  In the frame
`d; a, c, b` everything is explicit: `b' = d + α (a − d) + β (c − d)`
(`IsCap.Qac_coords'`), `c' = d + α₁ (a − d) + β₁ (b − d)` with `α₁ > 1` (the far end
`c'`), and every determinant test at the view is a multiple of
`E = det3 (a − d) (c − d) (b − d)` (`IsCap.det_Qac_ne`).  The sign of
`κ' = α + α₁ (β − 1)` decides whether `b'` is a corner (`κ' > 0`, the rim
`v, c, b', c'`) or hidden (`κ' < 0`, the rim is a triangle).  At a corner, Lemma 5
is Lemma 9.3's closing with `x = d`, `y = b`: the T4 edge `d → b` is not bad
(`type08_t4_not_bad`: Lemmas 9.7, 4, 3), and the claim of Lemma 9.3 uses the face
`Q_ac` through `d b'` (`quad_lower_of_face`).
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- **The claim of Lemma 9.3** (the lower boundary over the crossing of the
diagonals of the edge view along `y − x`), from one affine function `G` vanishing on
`x`, `y'` and one far end, negative at the other far end and at `y`. -/
theorem quad_lower_of_face {x y y' p p' : ℝ³} {G : ℝ³ → ℝ} {N : ℝ³}
    (hG : ∀ s t, G s - G t = ⟪N, s - t⟫) (hxy : x ≠ y) (hGx : G x = 0) (hGy' : G y' = 0)
    (hGy : G y < 0)
    (hS₂ : 0 < det3 (y' - x) (p' - x) (y - x)) (hS₄ : 0 < det3 (p - x) (y' - x) (y - x))
    (hface : (G p = 0 ∧ G p' < 0) ∨ (G p' = 0 ∧ G p < 0)) :
    det3 (y' - p) (p' - p) (y - x) * ⟪x, y - x⟫ + det3 (p - x) (p' - x) (y - x) * ⟪y', y - x⟫ <
      det3 (y' - x) (p' - x) (y - x) * ⟪p, y - x⟫ + det3 (p - x) (y' - x) (y - x) * ⟪p', y - x⟫ := by
  set u := y - x
  have hu : u ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  set S₁ := det3 (y' - p) (p' - p) u
  set S₂ := det3 (y' - x) (p' - x) u
  set S₃ := det3 (p - x) (p' - x) u
  set S₄ := det3 (p - x) (y' - x) u
  have hpar := four_point_parallel x p y' p' u hu
  have hsum := four_point_sum x p y' p' u
  set L := S₁ • x - S₂ • p + S₃ • y' - S₄ • p'
  set lam := ⟪L, u⟫ / ⟪u, u⟫
  have hL : L = -S₂ • (p - x) + S₃ • (y' - x) - S₄ • (p' - x) := by
    have : S₁ = S₂ - S₃ + S₄ := by linarith
    simp only [L, this]; module
  have hGL : ⟪N, L⟫ = -S₂ * G p - S₄ * G p' := by
    rw [hL, inner_sub_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_right, ← hG, ← hG, ← hG, hGx, hGy']
    ring
  have hGu : ⟪N, u⟫ = G y := by rw [← hG, hGx, sub_zero]
  have hpos : 0 < ⟪N, L⟫ := by
    rw [hGL]
    rcases hface with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1]; nlinarith
    · rw [h1]; nlinarith
  have hlam : lam < 0 := by
    have e : ⟪N, L⟫ = lam * G y := by
      rw [← hGu, ← real_inner_smul_right, ← hpar]
    rw [e] at hpos
    nlinarith
  have huu : 0 < ⟪u, u⟫ := real_inner_self_pos.mpr hu
  have hLu : ⟪L, u⟫ < 0 := by
    have : ⟪L, u⟫ = lam * ⟪u, u⟫ := by
      conv_lhs => rw [hpar]
      rw [real_inner_smul_left]
    rw [this]; nlinarith
  simp only [L, inner_sub_left, inner_add_left, real_inner_smul_left] at hLu
  linarith

/-- **The closing by `x` of Lemma 9.3** (and of Lemma 5): if the rim `y, p, y', p'`
along `u = y − x` has a saddle, the edge is not bad and not touching, and the claim
of Lemma 9.3 holds, then the rim `x, p, y', p'` has none. -/
theorem nws4_closing_x {x y y' p p' : ℝ³}
    (hS₁ : 0 < det3 (y' - p) (p' - p) (y - x)) (hS₂ : 0 < det3 (y' - x) (p' - x) (y - x))
    (hS₃ : 0 < det3 (p - x) (p' - x) (y - x)) (hS₄ : 0 < det3 (p - x) (y' - x) (y - x))
    (hlow : det3 (y' - p) (p' - p) (y - x) * ⟪x, y - x⟫ +
        det3 (p - x) (p' - x) (y - x) * ⟪y', y - x⟫ <
      det3 (y' - x) (p' - x) (y - x) * ⟪p, y - x⟫ + det3 (p - x) (y' - x) (y - x) * ⟪p', y - x⟫)
    (hN : ¬ NWS4 (quad ⟪y, y - x⟫ ⟪p, y - x⟫ ⟪y', y - x⟫ ⟪p', y - x⟫))
    (hgood : ¬ max ⟪y, y - x⟫ ⟪y', y - x⟫ ≤ min ⟪p, y - x⟫ ⟪p', y - x⟫)
    (htouch : ⟪p, y - x⟫ ≠ ⟪p', y - x⟫) :
    NWS4 (quad ⟪x, y - x⟫ ⟪p, y - x⟫ ⟪y', y - x⟫ ⟪p', y - x⟫) := by
  set u := y - x
  have hsum := four_point_sum x p y' p' u
  simp only [NWS4, quad_0, quad_1, quad_2, quad_3] at hN ⊢
  simp only [max_le_iff, le_min_iff, not_and_or, not_le] at hgood
  have hY : ⟪p, u⟫ ≤ ⟪y, u⟫ ∧ ⟪p', u⟫ ≤ ⟪y, u⟫ ∧ ⟪p, u⟫ ≤ ⟪y', u⟫ ∧ ⟪p', u⟫ ≤ ⟪y', u⟫ := by
    by_contra hc
    apply hN
    constructor
    · simp only [not_and_or, not_le] at hc; exact hc
    · rcases hgood with (h | h) | (h | h) <;> simp only [h, true_or, or_true]
  obtain ⟨hY1, hY2, hY3, hY4⟩ := hY
  have hx_lt : ⟪x, u⟫ < ⟪p, u⟫ ∨ ⟪x, u⟫ < ⟪p', u⟫ := by
    by_contra hc; push Not at hc
    obtain ⟨c1, c2⟩ := hc
    rcases le_total ⟪p, u⟫ ⟪p', u⟫ with hpp | hpp
    · nlinarith [mul_le_mul_of_nonneg_left c2 hS₁.le, mul_le_mul_of_nonneg_left hY4 hS₃.le,
        mul_le_mul_of_nonneg_left hpp hS₂.le, mul_eq_zero_of_left hsum ⟪p', u⟫]
    · nlinarith [mul_le_mul_of_nonneg_left c1 hS₁.le, mul_le_mul_of_nonneg_left hY3 hS₃.le,
        mul_le_mul_of_nonneg_left hpp hS₄.le, mul_eq_zero_of_left hsum ⟪p, u⟫]
  refine ⟨by rcases hx_lt with h | h; exacts [Or.inl h, Or.inr (Or.inl h)], ?_⟩
  by_contra hc
  simp only [not_or, not_lt] at hc
  obtain ⟨-, -, c3, c4⟩ := hc
  exact htouch (by linarith)

/-- Moving the corner along the view `b − d` from `d` to `b` does not change the
orientation tests. -/
theorem det3_axle_shift₁ (X Y b d : ℝ³) :
    det3 (X - b) (Y - b) (b - d) = det3 (X - d) (Y - d) (b - d) := by
  simp only [det3_expand, PiLp.sub_apply]; ring

theorem det3_axle_shift₂ (Q R b d : ℝ³) :
    det3 (b - Q) (R - Q) (b - d) = det3 (d - Q) (R - Q) (b - d) := by
  simp only [det3_expand, PiLp.sub_apply]; ring

theorem det3_axle_shift₃ (Q R b d : ℝ³) :
    det3 (R - Q) (b - Q) (b - d) = det3 (R - Q) (d - Q) (b - d) := by
  simp only [det3_expand, PiLp.sub_apply]; ring

theorem tri_injective {α : Type*} {p₀ p₁ p₂ : α} (h01 : p₀ ≠ p₁) (h02 : p₀ ≠ p₂)
    (h12 : p₁ ≠ p₂) : Function.Injective (tri p₀ p₁ p₂) := by
  intro i j hij
  rcases zmod3_cases i with rfl | rfl | rfl <;> rcases zmod3_cases j with rfl | rfl | rfl <;>
    simp_all [tri_0, tri_1, tri_2]

theorem tri_inner (p₀ p₁ p₂ u : ℝ³) :
    (fun i => ⟪tri p₀ p₁ p₂ i, u⟫) = tri ⟪p₀, u⟫ ⟪p₁, u⟫ ⟪p₂, u⟫ := by
  funext i; rcases zmod3_cases i with rfl | rfl | rfl <;> rfl

theorem zmod3_zero_add_one : (0 : ZMod 3) + 1 = 1 := by decide
theorem zmod3_zero_sub_one : (0 : ZMod 3) - 1 = 2 := by decide

/-- The determinant tests of the T4 case, as multiples of `E`. -/
theorem t4_dets {a b c d b' c' : ℝ³} {α β α₁ β₁ : ℝ}
    (hb' : b' = d + α • (a - d) + β • (c - d)) (hc' : c' = d + α₁ • (a - d) + β₁ • (b - d)) :
    let E := det3 (a - d) (c - d) (b - d)
    let κ := α + α₁ * (β - 1)
    det3 (c - d) (b' - d) (b - d) = -(α * E) ∧
    det3 (c - d) (c' - d) (b - d) = -(α₁ * E) ∧
    det3 (b' - c) (c' - c) (b - d) = -(κ * E) ∧
    det3 (b' - c) (d - c) (b - d) = -(α * E) ∧
    det3 (c' - b') (d - b') (b - d) = -(α₁ * β * E) ∧
    det3 (c' - b') (c - b') (b - d) = -(κ * E) ∧
    det3 (d - c') (c - c') (b - d) = -(α₁ * E) ∧
    det3 (d - c') (b' - c') (b - d) = -(α₁ * β * E) ∧
    det3 (c' - c) (d - c) (b - d) = -(α₁ * E) ∧
    det3 (c' - c) (b' - c) (b - d) = κ * E ∧
    det3 (c' - d) (b' - d) (b - d) = α₁ * β * E ∧
    det3 (c' - d) (c - d) (b - d) = α₁ * E ∧
    det3 (b' - c') (c - c') (b - d) = κ * E ∧
    det3 (b' - c') (d - c') (b - d) = α₁ * β * E ∧
    det3 (c - b') (d - b') (b - d) = α * E ∧
    det3 (c - b') (c' - b') (b - d) = κ * E ∧
    det3 (d - c) (c' - c) (b - d) = α₁ * E ∧
    det3 (d - c) (b' - c) (b - d) = α * E ∧
    det3 (c - c') (d - c') (b - d) = α₁ * E ∧
    det3 (c - c') (b' - c') (b - d) = -(κ * E) ∧
    det3 (b' - d) (c' - d) (b - d) = -(α₁ * β * E) ∧
    det3 (b' - d) (c - d) (b - d) = α * E ∧
    det3 (b - d) (b' - d) (c - d) = α * E ∧
    det3 (b - d) (b' - d) (c' - d) = -(α₁ * β * E) := by
  intro E κ
  subst hb' hc'
  simp only [E, κ, det3_expand, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩ <;> ring

theorem edgeMiddle_A {u v w A B m c : ℝ³} {h s δ : ℝ} (hc : c = v ∨ (c = w ∧ δ * h < 0))
    (hs0 : 0 < s) (hs1 : s < 1) (hδ : δ ≠ 0) (hm : m = c + s • (A - c) + δ • u) :
    EdgeMiddle u v w A B h m :=
  ⟨c, s, δ, hc, hs0, hs1, hδ, Or.inl hm⟩

theorem edgeMiddle_B {u v w A B m c : ℝ³} {h s δ : ℝ} (hc : c = v ∨ (c = w ∧ δ * h < 0))
    (hs0 : 0 < s) (hs1 : s < 1) (hδ : δ ≠ 0) (hm : m = B + s • (c - B) + δ • u) :
    EdgeMiddle u v w A B h m :=
  ⟨c, s, δ, hc, hs0, hs1, hδ, Or.inr hm⟩

set_option maxHeartbeats 1000000 in
/-- **Case T4 of Theorem 10.1 (Lemma 5).**  In the labelling of Lemma 6, at the view
along `d b` with far ends `c'` (of `Q_ab`) and `c` (of `Q_bc`): the middles are `a`
and `a'`; if `b'` is hidden the rim of `K_d` is the triangle `d, c, c'`, otherwise
the rim of `K_b` or of `K_d` is the quadrilateral through `c, b', c'`, unimodal by
Lemma 9.3's closing since the T4 edge `d → b` is not bad (`type08_t4_not_bad`).
With distinct depths, `b'` off the plane through `c c'` along the view, and no
horizontal double normal, `K` is Rupert. -/
theorem isRupert_type08_T4 {a a' b b' c c' d : ℝ³} (h : IsOctahedron a a' b b' c c')
    (F : OctFacets a a' b b' c c') (hd : IsCap F d) (G : GaleData a a' b b' c c')
    (hκa : 0 < galeD G.l G.m a a') (hκb : 0 < galeD G.l G.m b b')
    (hκc : galeD G.l G.m c c' ≠ 0) (hU : galeD G.l G.m b c < 0)
    (hfc' : F.a'bc.f c' < F.a'bc.f a) (hfc : F.abc'.f c < F.abc'.f a')
    (hinj : ∀ s t, (s = d ∨ s = b ∨ s = c ∨ s = b' ∨ s = c') → (t = c ∨ t = b' ∨ t = c') →
      s ≠ t → ⟪s, b - d⟫ ≠ ⟪t, b - d⟫)
    (hcorner : det3 (c' - c) (b' - c) (b - d) ≠ 0)
    (hnd : NoHDNAt ((insert d ({a, a', b, b', c, c'} : Finset ℝ³)).erase b) (b - d) ∧
      NoHDNAt ((insert d ({a, a', b, b', c, c'} : Finset ℝ³)).erase d) (b - d)) :
    IsRupert (insert d ({a, a', b, b', c, c'} : Finset ℝ³)) := by
  classical
  have hnd' := F.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd'
  obtain ⟨⟨haa', hab, hab', hac, hac'⟩, ⟨ha'b, ha'b', ha'c, ha'c'⟩, ⟨hbb', hbc, hbc'⟩,
    ⟨hb'c, hb'c'⟩, hcc', -⟩ := hnd'
  obtain ⟨hda, hda', hdb, hdb', hdc, hdc'⟩ := hd.ne
  set V : Finset ℝ³ := insert d {a, a', b, b', c, c'} with hV
  have hmemV : ∀ z ∈ V, z = d ∨ z = a ∨ z = a' ∨ z = b ∨ z = b' ∨ z = c ∨ z = c' := by
    intro z hz; simpa [V] using hz
  have hu : b - d ≠ 0 := sub_ne_zero.mpr (Ne.symm hdb)
  obtain ⟨a0, a1, a2, a3⟩ := zmod4_add_one
  obtain ⟨b0, b1, b2⟩ := zmod3_add_one
  -- coordinates
  obtain ⟨hα, hβ, -, hb'⟩ := hd.Qac_coords'
  set α := F.a'bc.f b' / F.a'bc.f a
  set β := F.abc'.f b' / F.abc'.f c
  obtain ⟨hα₁, hβ₁, -, hc'⟩ : 0 < F.a'bc.f c' / F.a'bc.f a ∧ 0 < F.ab'c.f c' / F.ab'c.f b ∧
      1 < F.a'bc.f c' / F.a'bc.f a + F.ab'c.f c' / F.ab'c.f b ∧
      c' = d + (F.a'bc.f c' / F.a'bc.f a) • (a - d) + (F.ab'c.f c' / F.ab'c.f b) • (b - d) :=
    hd.perm₂₃.Qac_coords'
  set α₁ := F.a'bc.f c' / F.a'bc.f a
  set β₁ := F.ab'c.f c' / F.ab'c.f b
  obtain ⟨hα₂, hβ₂, hαβ₂, ha'⟩ : 0 < F.ab'c.f a' / F.ab'c.f b ∧ 0 < F.abc'.f a' / F.abc'.f c ∧
      1 < F.ab'c.f a' / F.ab'c.f b + F.abc'.f a' / F.abc'.f c ∧
      a' = d + (F.ab'c.f a' / F.ab'c.f b) • (b - d) + (F.abc'.f a' / F.abc'.f c) • (c - d) :=
    hd.perm₁₂.Qac_coords'
  set α₂ := F.ab'c.f a' / F.ab'c.f b
  set β₂ := F.abc'.f a' / F.abc'.f c
  have hα₁1 : 1 < α₁ := (one_lt_div_of_neg (F.a'bc.neg a (by simp) haa' hab hac)).mpr hfc'
  have hβ₂1 : β₂ < 1 :=
    (div_lt_one_of_neg (F.abc'.neg c (by simp) (Ne.symm hac) (Ne.symm hbc) hcc')).mpr hfc
  have hα₁0 : α₁ ≠ 0 := by positivity
  -- the middles
  have hma' : a' = b + β₂ • (c - b) + (α₂ + β₂ - 1) • (b - d) := by rw [ha']; module
  have hma : a = d + α₁⁻¹ • (c' - d) + (-(β₁ / α₁)) • (b - d) := by
    have key : c' - d = α₁ • (a - d) + β₁ • (b - d) := by rw [hc']; abel
    rw [key, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hα₁0, one_smul, div_eq_inv_mul]
    module
  have hs1 : 0 < α₁⁻¹ := inv_pos.mpr (by linarith)
  have hs2 : α₁⁻¹ < 1 := inv_lt_one_of_one_lt₀ hα₁1
  have hδa : -(β₁ / α₁) < 0 := neg_neg_of_pos (div_pos hβ₁ (by linarith))
  have hδa' : 0 < α₂ + β₂ - 1 := sub_pos.mpr hαβ₂
  -- the determinant tests
  obtain ⟨D1, D2, D3, D4, D5, D6, D7, D8, D9, D10, D11, D12, D13, D14, D15, D16, D17, D18,
    D19, D20, D21, D22, D23, D24⟩ := t4_dets hb' hc'
  set E := det3 (a - d) (c - d) (b - d) with hE_def
  have hE : E ≠ 0 := hd.det_Qac_ne
  set κ := α + α₁ * (β - 1) with hκ_def
  have hκ : κ ≠ 0 := by
    intro h0; apply hcorner; rw [D10, h0, zero_mul]
  have hα₁p : 0 < α₁ := by linarith
  -- the T4 edge `d → b` is not bad
  have hgood := type08_t4_not_bad h F hd G hκa hκb hκc hU (by
    rw [D23, D24]
    have := mul_self_pos.mpr hE
    have := mul_pos (mul_pos hα hα₁p) hβ
    nlinarith)
  have hGb := F.ab'c.neg b (by simp) (Ne.symm hab) hbb' hbc
  have hGc' := F.ab'c.neg c' (by simp) (Ne.symm hac') (Ne.symm hb'c') (Ne.symm hcc')
  have hi : ∀ s t, (s = d ∨ s = b ∨ s = c ∨ s = b' ∨ s = c') → (t = c ∨ t = b' ∨ t = c') →
      s ≠ t → ⟪s, b - d⟫ ≠ ⟪t, b - d⟫ := hinj
  have hcc'u : ⟪c, b - d⟫ ≠ ⟪c', b - d⟫ := hi c c' (by simp) (by simp) hcc'
  have hb'c'u : ⟪b', b - d⟫ ≠ ⟪c', b - d⟫ := hi b' c' (by simp) (by simp) hb'c'
  have hcb'u : ⟪c, b - d⟫ ≠ ⟪b', b - d⟫ := hi c b' (by simp) (by simp) (Ne.symm hb'c)
  -- a corner of `K_v` is not a middle
  have hxM : ∀ z, (z = d ∨ z = b ∨ z = c ∨ z = b' ∨ z = c') → z ∉ ({a, a'} : Finset ℝ³) := by
    intro z hz
    simp only [mem_insert, mem_singleton, not_or]
    rcases hz with rfl | rfl | rfl | rfl | rfl
    exacts [⟨hda, hda'⟩, ⟨Ne.symm hab, Ne.symm ha'b⟩, ⟨Ne.symm hac, Ne.symm ha'c⟩,
      ⟨Ne.symm hab', Ne.symm ha'b'⟩, ⟨Ne.symm hac', Ne.symm ha'c'⟩]
  have hVd : d ∈ V := by simp [V]
  have hVb : b ∈ V := by simp [V]
  have hVc : c ∈ V := by simp [V]
  have hVb' : b' ∈ V := by simp [V]
  have hVc' : c' ∈ V := by simp [V]
  -- every point of `V` off `M` and `w` is a corner, or `b'`
  have hrest4 : ∀ (x : ZMod 4 → ℝ³) (w : ℝ³), (w = d ∨ w = b) →
      (∀ z, (z = d ∨ z = b) → z ≠ w → ∃ j, z = x j) → (∃ j, c = x j) → (∃ j, b' = x j) →
      (∃ j, c' = x j) →
      ∀ z ∈ V, z ∉ ({a, a'} : Finset ℝ³) → z ≠ w → (∀ j, z ≠ x j) → False := by
    intro x w hw hx hc hb hc'' z hz hzM hzw hzx
    rcases hmemV z hz with h | h | h | h | h | h | h
    · obtain ⟨j, hj⟩ := hx z (Or.inl h) hzw; exact hzx j hj
    · exact hzM (by simp [h])
    · exact hzM (by simp [h])
    · obtain ⟨j, hj⟩ := hx z (Or.inr h) hzw; exact hzx j hj
    · obtain ⟨j, hj⟩ := hb; exact hzx j (h ▸ hj)
    · obtain ⟨j, hj⟩ := hc; exact hzx j (h ▸ hj)
    · obtain ⟨j, hj⟩ := hc''; exact hzx j (h ▸ hj)
  have hd_ne_b := hdb
  rcases lt_or_gt_of_ne hE with hEn | hEp
  · -- `E < 0`: the counterclockwise rim runs `v, c, (b'), c'`; `A = c`, `B = c'`
    have p02 : 0 < det3 (c - d) (b' - d) (b - d) := by
      rw [D1]; exact neg_pos.mpr (mul_neg_of_pos_of_neg hα hEn)
    have p03 : 0 < det3 (c - d) (c' - d) (b - d) := by
      rw [D2]; exact neg_pos.mpr (mul_neg_of_pos_of_neg hα₁p hEn)
    have p10 : 0 < det3 (b' - c) (d - c) (b - d) := by
      rw [D4]; exact neg_pos.mpr (mul_neg_of_pos_of_neg hα hEn)
    have p20 : 0 < det3 (c' - b') (d - b') (b - d) := by
      rw [D5]; exact neg_pos.mpr (mul_neg_of_pos_of_neg (mul_pos hα₁p hβ) hEn)
    have p31 : 0 < det3 (d - c') (c - c') (b - d) := by
      rw [D7]; exact neg_pos.mpr (mul_neg_of_pos_of_neg hα₁p hEn)
    have p32 : 0 < det3 (d - c') (b' - c') (b - d) := by
      rw [D8]; exact neg_pos.mpr (mul_neg_of_pos_of_neg (mul_pos hα₁p hβ) hEn)
    have hmidA : ∀ v w : ℝ³, ∀ hh : ℝ, ((v = b ∧ w = d ∧ hh = 1) ∨ (v = d ∧ w = b ∧ hh = -1)) →
        ∀ m ∈ ({a, a'} : Finset ℝ³), EdgeMiddle (b - d) v w c c' hh m := by
      intro v w hh hvw m hm
      rcases mem_insert.mp hm with hm | hm
      · rw [hm]
        refine edgeMiddle_B (c := d) (s := 1 - α₁⁻¹) ?_ (by linarith) (by linarith) hδa.ne ?_
        · rcases hvw with ⟨-, rfl, rfl⟩ | ⟨rfl, -, -⟩
          · exact Or.inr ⟨rfl, by linarith⟩
          · exact Or.inl rfl
        · rw [hma]; module
      · rw [mem_singleton.mp hm]
        refine edgeMiddle_A (c := b) ?_ hβ₂ hβ₂1 hδa'.ne' hma'
        rcases hvw with ⟨rfl, -, -⟩ | ⟨-, rfl, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨rfl, by linarith⟩
    rcases lt_or_gt_of_ne hκ with hκn | hκp
    · -- `b'` hidden: the triangle `d, c, c'`
      have t10 : 0 < det3 (c' - c) (d - c) (b - d) := by
        rw [D9]; exact neg_pos.mpr (mul_neg_of_pos_of_neg hα₁p hEn)
      have h1 : 0 < det3 (c' - c) (b' - c) (b - d) := by
        rw [D10]; exact mul_pos_of_neg_of_neg hκn hEn
      refine isRupert_of_edgeView V {a, a'} (b - d) hu (k := 3) le_rfl (tri d c c') 0 b (-1)
        hVb (by simp only [tri_0, neg_smul, one_smul, sub_neg_eq_add]; abel) (by norm_num)
        ?_ ?_ ?_ ?_ ?_ hnd.1 ?_
      · intro i; rcases zmod3_cases i with rfl | rfl | rfl
        exacts [hVd, hVc, hVc']
      · intro i; rcases zmod3_cases i with rfl | rfl | rfl
        exacts [hxM d (by simp), hxM c (by simp), hxM c' (by simp)]
      · intro i j hi hj
        rcases zmod3_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          simp only [b0, b1, b2, tri_0, tri_1, tri_2]
        exacts [p03, t10, p31]
      · intro z hz hzM hzw hzx i
        have hzb' : z = b' := by
          rcases hmemV z hz with h | h | h | h | h | h | h
          · exact absurd (h ▸ rfl : z = tri d c c' 0) (hzx 0)
          · exact absurd (by simp [h]) hzM
          · exact absurd (by simp [h]) hzM
          · exact absurd h hzw
          · exact h
          · exact absurd (h ▸ rfl : z = tri d c c' 1) (hzx 1)
          · exact absurd (h ▸ rfl : z = tri d c c' 2) (hzx 2)
        rw [hzb']
        rcases zmod3_cases i with rfl | rfl | rfl <;> simp only [b0, b1, b2, tri_0, tri_1, tri_2]
        exacts [p02, h1, p32]
      · rw [tri_inner]
        exact isCyclicUnimodal_three (tri_injective (hi d c (by simp) (by simp) hdc)
          (hi d c' (by simp) (by simp) hdc') hcc'u)
      · rw [zmod3_zero_add_one, zmod3_zero_sub_one]
        simpa only [tri_0, tri_1, tri_2] using hmidA d b (-1) (Or.inr ⟨rfl, rfl, rfl⟩)
    · -- `b'` a corner: the quadrilateral `v, c, b', c'`
      have p13 : 0 < det3 (b' - c) (c' - c) (b - d) := by
        rw [D3]; exact neg_pos.mpr (mul_neg_of_pos_of_neg hκp hEn)
      have p21 : 0 < det3 (c' - b') (c - b') (b - d) := by
        rw [D6]; exact neg_pos.mpr (mul_neg_of_pos_of_neg hκp hEn)
      have hcyc : ∀ v, (v = d ∨ v = b) → ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
          0 < det3 (quad v c b' c' (i + 1) - quad v c b' c' i)
            (quad v c b' c' j - quad v c b' c' i) (b - d) := by
        intro v hv i j hi hj
        rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3] <;>
        rcases hv with rfl | rfl
        · exact p02
        · rw [det3_axle_shift₁]; exact p02
        · exact p03
        · rw [det3_axle_shift₁]; exact p03
        · exact p13
        · exact p13
        · exact p10
        · rw [det3_axle_shift₃]; exact p10
        · exact p20
        · rw [det3_axle_shift₃]; exact p20
        · exact p21
        · exact p21
        · exact p31
        · rw [det3_axle_shift₂]; exact p31
        · exact p32
        · rw [det3_axle_shift₂]; exact p32
      have hxV : ∀ v, (v = d ∨ v = b) → ∀ i, quad v c b' c' i ∈ V := by
        intro v hv i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
        · rcases hv with rfl | rfl; exacts [hVd, hVb]
        exacts [hVc, hVb', hVc']
      have hxM' : ∀ v, (v = d ∨ v = b) → ∀ i, quad v c b' c' i ∉ ({a, a'} : Finset ℝ³) := by
        intro v hv i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
        · exact hxM v (by rcases hv with h | h <;> simp [h])
        exacts [hxM c (by simp), hxM b' (by simp), hxM c' (by simp)]
      by_cases hN : NWS4 (quad ⟪b, b - d⟫ ⟪c, b - d⟫ ⟪b', b - d⟫ ⟪c', b - d⟫)
      · -- `K_b`
        refine isRupert_of_edgeView V {a, a'} (b - d) hu (k := 4) (by norm_num) (quad b c b' c') 0
          d 1 hVd (by simp only [quad_0, one_smul]; abel) one_ne_zero (hxV b (Or.inr rfl))
          (hxM' b (Or.inr rfl)) (hcyc b (Or.inr rfl)) ?_ ?_ hnd.2 ?_
        · intro z hz hzM hzw hzx
          exact (hrest4 (quad b c b' c') d (Or.inl rfl)
            (fun z hz hzw => ⟨0, by rcases hz with h | h; exacts [absurd h hzw, h]⟩)
            ⟨1, rfl⟩ ⟨2, rfl⟩ ⟨3, rfl⟩ z hz hzM hzw hzx).elim
        · rw [quad_inner]
          refine isCyclicUnimodal_of_NWS4 (quad_injective (hi b c (by simp) (by simp) hbc)
            (hi b b' (by simp) (by simp) hbb') (hi b c' (by simp) (by simp) hbc') hcb'u hcc'u
            hb'c'u) hN
        · rw [zmod4_zero_add_one, zmod4_zero_sub_one]
          simpa only [quad_0, quad_1, quad_3] using hmidA b d 1 (Or.inl ⟨rfl, rfl, rfl⟩)
      · -- `K_d`, by the closing of Lemma 9.3 / Lemma 5
        have hS₂ : 0 < det3 (b' - d) (c' - d) (b - d) := by
          rw [D21]; exact neg_pos.mpr (mul_neg_of_pos_of_neg (mul_pos hα₁p hβ) hEn)
        have hlow := quad_lower_of_face F.ab'c.hN hdb hd.ab'c F.ab'c.hQ hGb hS₂ p02
          (Or.inl ⟨F.ab'c.hR, hGc'⟩)
        have hN' := nws4_closing_x p13 hS₂ p03 p02 hlow hN hgood hcc'u
        refine isRupert_of_edgeView V {a, a'} (b - d) hu (k := 4) (by norm_num) (quad d c b' c') 0
          b (-1) hVb (by simp only [quad_0, neg_smul, one_smul, sub_neg_eq_add]; abel)
          (by norm_num) (hxV d (Or.inl rfl)) (hxM' d (Or.inl rfl)) (hcyc d (Or.inl rfl)) ?_ ?_
          hnd.1 ?_
        · intro z hz hzM hzw hzx
          exact (hrest4 (quad d c b' c') b (Or.inr rfl)
            (fun z hz hzw => ⟨0, by rcases hz with h | h; exacts [h, absurd h hzw]⟩)
            ⟨1, rfl⟩ ⟨2, rfl⟩ ⟨3, rfl⟩ z hz hzM hzw hzx).elim
        · rw [quad_inner]
          refine isCyclicUnimodal_of_NWS4 (quad_injective (hi d c (by simp) (by simp) hdc)
            (hi d b' (by simp) (by simp) hdb') (hi d c' (by simp) (by simp) hdc') hcb'u hcc'u
            hb'c'u) hN'
        · rw [zmod4_zero_add_one, zmod4_zero_sub_one]
          simpa only [quad_0, quad_1, quad_3] using hmidA d b (-1) (Or.inr ⟨rfl, rfl, rfl⟩)
  · -- `E > 0`: the counterclockwise rim runs `v, c', (b'), c`; `A = c'`, `B = c`
    have q02 : 0 < det3 (c' - d) (b' - d) (b - d) := by
      rw [D11]; exact mul_pos (mul_pos hα₁p hβ) hEp
    have q03 : 0 < det3 (c' - d) (c - d) (b - d) := by rw [D12]; exact mul_pos hα₁p hEp
    have q10 : 0 < det3 (b' - c') (d - c') (b - d) := by
      rw [D14]; exact mul_pos (mul_pos hα₁p hβ) hEp
    have q20 : 0 < det3 (c - b') (d - b') (b - d) := by rw [D15]; exact mul_pos hα hEp
    have q31 : 0 < det3 (d - c) (c' - c) (b - d) := by rw [D17]; exact mul_pos hα₁p hEp
    have q32 : 0 < det3 (d - c) (b' - c) (b - d) := by rw [D18]; exact mul_pos hα hEp
    have hmidA : ∀ v w : ℝ³, ∀ hh : ℝ, ((v = b ∧ w = d ∧ hh = 1) ∨ (v = d ∧ w = b ∧ hh = -1)) →
        ∀ m ∈ ({a, a'} : Finset ℝ³), EdgeMiddle (b - d) v w c' c hh m := by
      intro v w hh hvw m hm
      rcases mem_insert.mp hm with hm | hm
      · rw [hm]
        refine edgeMiddle_A (c := d) ?_ hs1 hs2 hδa.ne hma
        rcases hvw with ⟨-, rfl, rfl⟩ | ⟨rfl, -, -⟩
        · exact Or.inr ⟨rfl, by linarith⟩
        · exact Or.inl rfl
      · rw [mem_singleton.mp hm]
        refine edgeMiddle_B (c := b) (s := 1 - β₂) ?_ (by linarith) (by linarith) hδa'.ne' ?_
        · rcases hvw with ⟨rfl, -, -⟩ | ⟨-, rfl, rfl⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨rfl, by linarith⟩
        · rw [hma']; module
    rcases lt_or_gt_of_ne hκ with hκn | hκp
    · -- `b'` hidden: the triangle `d, c', c`
      have s10 : 0 < det3 (c - c') (d - c') (b - d) := by rw [D19]; exact mul_pos hα₁p hEp
      have g1 : 0 < det3 (c - c') (b' - c') (b - d) := by
        rw [D20]; exact neg_pos.mpr (mul_neg_of_neg_of_pos hκn hEp)
      refine isRupert_of_edgeView V {a, a'} (b - d) hu (k := 3) le_rfl (tri d c' c) 0 b (-1)
        hVb (by simp only [tri_0, neg_smul, one_smul, sub_neg_eq_add]; abel) (by norm_num)
        ?_ ?_ ?_ ?_ ?_ hnd.1 ?_
      · intro i; rcases zmod3_cases i with rfl | rfl | rfl
        exacts [hVd, hVc', hVc]
      · intro i; rcases zmod3_cases i with rfl | rfl | rfl
        exacts [hxM d (by simp), hxM c' (by simp), hxM c (by simp)]
      · intro i j hi hj
        rcases zmod3_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          simp only [b0, b1, b2, tri_0, tri_1, tri_2]
        exacts [q03, s10, q31]
      · intro z hz hzM hzw hzx i
        have hzb' : z = b' := by
          rcases hmemV z hz with h | h | h | h | h | h | h
          · exact absurd (h ▸ rfl : z = tri d c' c 0) (hzx 0)
          · exact absurd (by simp [h]) hzM
          · exact absurd (by simp [h]) hzM
          · exact absurd h hzw
          · exact h
          · exact absurd (h ▸ rfl : z = tri d c' c 2) (hzx 2)
          · exact absurd (h ▸ rfl : z = tri d c' c 1) (hzx 1)
        rw [hzb']
        rcases zmod3_cases i with rfl | rfl | rfl <;> simp only [b0, b1, b2, tri_0, tri_1, tri_2]
        exacts [q02, g1, q32]
      · rw [tri_inner]
        exact isCyclicUnimodal_three (tri_injective (hi d c' (by simp) (by simp) hdc')
          (hi d c (by simp) (by simp) hdc) (fun h => hcc'u h.symm))
      · rw [zmod3_zero_add_one, zmod3_zero_sub_one]
        simpa only [tri_0, tri_1, tri_2] using hmidA d b (-1) (Or.inr ⟨rfl, rfl, rfl⟩)
    · -- `b'` a corner: the quadrilateral `v, c', b', c`
      have q13 : 0 < det3 (b' - c') (c - c') (b - d) := by rw [D13]; exact mul_pos hκp hEp
      have q21 : 0 < det3 (c - b') (c' - b') (b - d) := by rw [D16]; exact mul_pos hκp hEp
      have hcyc : ∀ v, (v = d ∨ v = b) → ∀ i j : ZMod 4, j ≠ i → j ≠ i + 1 →
          0 < det3 (quad v c' b' c (i + 1) - quad v c' b' c i)
            (quad v c' b' c j - quad v c' b' c i) (b - d) := by
        intro v hv i j hi hj
        rcases zmod4_pairs i j hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp only [a0, a1, a2, a3, quad_0, quad_1, quad_2, quad_3] <;>
        rcases hv with rfl | rfl
        · exact q02
        · rw [det3_axle_shift₁]; exact q02
        · exact q03
        · rw [det3_axle_shift₁]; exact q03
        · exact q13
        · exact q13
        · exact q10
        · rw [det3_axle_shift₃]; exact q10
        · exact q20
        · rw [det3_axle_shift₃]; exact q20
        · exact q21
        · exact q21
        · exact q31
        · rw [det3_axle_shift₂]; exact q31
        · exact q32
        · rw [det3_axle_shift₂]; exact q32
      have hxV : ∀ v, (v = d ∨ v = b) → ∀ i, quad v c' b' c i ∈ V := by
        intro v hv i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
        · rcases hv with rfl | rfl; exacts [hVd, hVb]
        exacts [hVc', hVb', hVc]
      have hxM' : ∀ v, (v = d ∨ v = b) → ∀ i, quad v c' b' c i ∉ ({a, a'} : Finset ℝ³) := by
        intro v hv i; rcases zmod4_cases i with rfl | rfl | rfl | rfl
        · exact hxM v (by rcases hv with h | h <;> simp [h])
        exacts [hxM c' (by simp), hxM b' (by simp), hxM c (by simp)]
      by_cases hN : NWS4 (quad ⟪b, b - d⟫ ⟪c', b - d⟫ ⟪b', b - d⟫ ⟪c, b - d⟫)
      · -- `K_b`
        refine isRupert_of_edgeView V {a, a'} (b - d) hu (k := 4) (by norm_num) (quad b c' b' c) 0
          d 1 hVd (by simp only [quad_0, one_smul]; abel) one_ne_zero (hxV b (Or.inr rfl))
          (hxM' b (Or.inr rfl)) (hcyc b (Or.inr rfl)) ?_ ?_ hnd.2 ?_
        · intro z hz hzM hzw hzx
          exact (hrest4 (quad b c' b' c) d (Or.inl rfl)
            (fun z hz hzw => ⟨0, by rcases hz with h | h; exacts [absurd h hzw, h]⟩)
            ⟨3, rfl⟩ ⟨2, rfl⟩ ⟨1, rfl⟩ z hz hzM hzw hzx).elim
        · rw [quad_inner]
          refine isCyclicUnimodal_of_NWS4 (quad_injective (hi b c' (by simp) (by simp) hbc')
            (hi b b' (by simp) (by simp) hbb') (hi b c (by simp) (by simp) hbc)
            (fun h => hb'c'u h.symm) (fun h => hcc'u h.symm) (fun h => hcb'u h.symm)) hN
        · rw [zmod4_zero_add_one, zmod4_zero_sub_one]
          simpa only [quad_0, quad_1, quad_3] using hmidA b d 1 (Or.inl ⟨rfl, rfl, rfl⟩)
      · -- `K_d`, by the closing of Lemma 9.3 / Lemma 5
        have hS₂ : 0 < det3 (b' - d) (c - d) (b - d) := by rw [D22]; exact mul_pos hα hEp
        have hlow := quad_lower_of_face F.ab'c.hN hdb hd.ab'c F.ab'c.hQ hGb hS₂ q02
          (Or.inr ⟨F.ab'c.hR, hGc'⟩)
        have hN' := nws4_closing_x q13 hS₂ q03 q02 hlow hN (by rwa [min_comm])
          (fun h => hcc'u h.symm)
        refine isRupert_of_edgeView V {a, a'} (b - d) hu (k := 4) (by norm_num) (quad d c' b' c) 0
          b (-1) hVb (by simp only [quad_0, neg_smul, one_smul, sub_neg_eq_add]; abel)
          (by norm_num) (hxV d (Or.inl rfl)) (hxM' d (Or.inl rfl)) (hcyc d (Or.inl rfl)) ?_ ?_
          hnd.1 ?_
        · intro z hz hzM hzw hzx
          exact (hrest4 (quad d c' b' c) b (Or.inr rfl)
            (fun z hz hzw => ⟨0, by rcases hz with h | h; exacts [h, absurd h hzw]⟩)
            ⟨3, rfl⟩ ⟨2, rfl⟩ ⟨1, rfl⟩ z hz hzM hzw hzx).elim
        · rw [quad_inner]
          refine isCyclicUnimodal_of_NWS4 (quad_injective (hi d c' (by simp) (by simp) hdc')
            (hi d b' (by simp) (by simp) hdb') (hi d c (by simp) (by simp) hdc)
            (fun h => hb'c'u h.symm) (fun h => hcc'u h.symm) (fun h => hcb'u h.symm)) hN'
        · rw [zmod4_zero_add_one, zmod4_zero_sub_one]
          simpa only [quad_0, quad_1, quad_3] using hmidA d b (-1) (Or.inr ⟨rfl, rfl, rfl⟩)

end Minimality

end
