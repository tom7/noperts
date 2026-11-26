module

public import Minimality.Type24SplitFamily
public import Minimality.HiddenCapFree
public import Minimality.GenericLeaves
public import Minimality.Sym24Transport

@[expose] public section

/-!
# EPHide: hiding a vertex in an Edge-Plane certificate (type 24 chambers)

Formalization of L1 (EPHide) of the EPDEL spec (nopert229 tools/genleaves/runs/epdel/SPEC.md).  The rows of the
Edge-Plane Lemma use only the rim points, so a point off the rim enters `Gen.EdgePlaneAny` only through
`HiddenInTriangles`; `ConeHides` (the view is a combination of three independent edges at the point, one strict
sign) gives that triangle (`det3_pos_triangle_of_cone`).  The strict rim at a chamber view of the facet-sign
arrangement follows from the facet signs (`rim_det_all`, the version of `rim_det_sign` for all vertices).
`EPHideChamber` (chambers `H`, `A`, `pi24 A`) implies `Gen.EdgePlaneAny`.  The conjecture L2 (`OpenEP` in the
hidden cone) is not formalized.
-/

set_option autoImplicit false

open scoped RealInnerProductSpace
open Finset
open Minimality Minimality.H21 Minimality.T24.SAT Minimality.Split

namespace Minimality.T24.EH

variable {x : Fin 7 → ℝ³}

/-- Rim determinants of a silhouette cycle against ALL vertices (`rim_det_sign` only treats the cycle's own
vertices): one global sign `ρ`. -/
theorem rim_det_all (F : S0xFac 9 s0x_S24 x) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (c : ZMod k → Fin 7) (hc : Function.Injective c) (pat : Fin 9 → Bool)
    (hcyc : S0xCycOK s0x_S24 c pat) (u : ℝ³)
    (hfac : ∀ t, (pat t = true → 0 < ⟪F.N t, u⟫) ∧ (pat t = false → ⟪F.N t, u⟫ < 0)) :
    ∃ ρ : ℝ, (ρ = 1 ∨ ρ = -1) ∧ ∀ (i : ZMod k) (m : Fin 7), m ≠ c i → m ≠ c (i + 1) →
      0 < ρ * Split.det3 (x (c (i + 1)) - x (c i)) (x m - x (c i)) u := by
  have hx := EdgeViewLink.inj_of_fac24 F
  have hS0 : S0xFacOK F pat u 0 := fun t =>
    ⟨fun h => Or.inl ((hfac t).1 h), fun h => Or.inl (by simpa using (hfac t).2 h)⟩
  obtain ⟨D⟩ := s0x_silL F hcyc hS0
  choose μ hμ0 hμ using fun i => h21b_exists_mu hk hx hc D i
  have hsign := h21b_sign_agree hk hx hc D μ hμ0 hμ
  have Q : ∀ i m, m ≠ c i → m ≠ c (i + 1) →
      0 < D.fA i (x m) * ⟪D.B i, u⟫ - D.fB i (x m) * ⟪D.A i, u⟫ := by
    intro i m h0 h1
    have := h21b_Q_pos D i m h0 h1
    simp only [inner_zero_right, mul_zero, sub_zero, h21b_LP] at this
    rcases this with h | ⟨_, h⟩
    · exact h
    · exact absurd h (lt_irrefl _)
  have key : ∀ (i : ZMod k) (m : Fin 7),
      Split.det3 (x (c (i + 1)) - x (c i)) (x m - x (c i)) u =
        μ i * (D.fA i (x m) * ⟪D.B i, u⟫ - D.fB i (x m) * ⟪D.A i, u⟫) := by
    intro i m
    rw [Split.det3_eq_minimality]
    exact h21b_det_eq D i (μ i) (hμ i) m u
  rcases hsign with h | h
  · refine ⟨1, Or.inl rfl, fun i m h0 h1 => ?_⟩
    rw [key i m, one_mul]
    exact mul_pos (h i) (Q i m h0 h1)
  · refine ⟨-1, Or.inr rfl, fun i m h0 h1 => ?_⟩
    rw [key i m]
    have := Q i m h0 h1
    nlinarith [h i]

/-- The strict rim at a chamber view, in either orientation (`lab = c` or its reverse), the orientation fixed
by one determinant test. -/
theorem strictRimN_of_facets (F : S0xFac 9 s0x_S24 x) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (c : ZMod k → Fin 7) (hc : Function.Injective c) (pat : Fin 9 → Bool)
    (hcyc : S0xCycOK s0x_S24 c pat) (u : ℝ³)
    (hfac : ∀ t, (pat t = true → 0 < ⟪F.N t, u⟫) ∧ (pat t = false → ⟪F.N t, u⟫ < 0))
    (lab : ZMod k → Fin 7) (hlab : lab = c ∨ lab = fun i => c (-i))
    (hor : 0 < Split.det3 (x (lab 1) - x (lab 0)) (x (lab 2) - x (lab 0)) u) :
    Function.Injective lab ∧ StrictRimN x u lab := by
  obtain ⟨h10, h20⟩ := zmod_ne hk
  have h21 : (2 : ZMod k) ≠ 1 := by
    intro h
    have := zmod_ne_add_one (k := k) (by omega) 1
    apply this
    rw [one_add_one_eq_two]; exact h.symm
  obtain ⟨ρ, hρ, hrim⟩ := rim_det_all F hk c hc pat hcyc u hfac
  rcases hlab with rfl | rfl
  · refine ⟨hc, ?_⟩
    have h := hrim 0 (lab 2) (hc.ne h20) (hc.ne (by rw [zero_add]; exact h21))
    rw [zero_add] at h
    have hρ1 : ρ = 1 := by
      rcases hρ with h1 | h1
      · exact h1
      · rw [h1] at h; nlinarith
    subst hρ1
    intro m i h0 h1
    simpa using hrim i m h0 h1
  · have hinj : Function.Injective (fun i : ZMod k => c (-i)) := fun i j h => neg_injective (hc h)
    refine ⟨hinj, ?_⟩
    have n1 : (0 : ZMod k) ≠ -1 := fun h => h10 (by simpa using h.symm)
    have n2 : (0 : ZMod k) ≠ -2 := fun h => h20 (by simpa using h.symm)
    have e : (-2 + 1 : ZMod k) = -1 := by ring
    have h := hrim (-2) (c 0) (hc.ne n2) (by rw [e]; exact hc.ne n1)
    rw [e] at h
    have hneg : ρ = -1 := by
      rcases hρ with h1 | h1
      · exfalso
        simp only [neg_zero] at hor
        rw [h1] at h
        have : Split.det3 (x (c (-1)) - x (c 0)) (x (c (-2)) - x (c 0)) u =
            - Split.det3 (x (c (-1)) - x (c (-2))) (x (c 0) - x (c (-2))) u := by
          simp only [Split.det3, PiLp.sub_apply]; ring
        linarith
      · exact h1
    subst hneg
    intro m i h0 h1
    have e2 : (-i - 1 + 1 : ZMod k) = -i := by ring
    have := hrim (-i - 1) m (by rwa [show (-i - 1 : ZMod k) = -(i + 1) by ring]) (by rw [e2]; exact h0)
    rw [e2] at this
    have e3 : (-(i + 1) : ZMod k) = -i - 1 := by ring
    simp only [e3]
    have : Split.det3 (x (c (-i - 1)) - x (c (-i))) (x m - x (c (-i))) u =
        - Split.det3 (x (c (-i)) - x (c (-i - 1))) (x m - x (c (-i - 1))) u := by
      simp only [Split.det3, PiLp.sub_apply]; ring
    linarith

/-! ## Hiding by a cone, and the general lemma -/

/-- The view `w` hides the point `x v` in a tangent cone: `w` is a combination of three independent edges
`x a - x v`, `x b - x v`, `x c - x v` with coefficients of one strict sign (so `x v` projects strictly inside
the triangle `a b c`). -/
def ConeHides {n : ℕ} (x : Fin n → ℝ³) (v : Fin n) (w : ℝ³) : Prop :=
  ∃ a b c : Fin n, ∃ ca cb cc : ℝ, Split.det3 (x a - x v) (x b - x v) (x c - x v) ≠ 0 ∧
    ((0 < ca ∧ 0 < cb ∧ 0 < cc) ∨ (ca < 0 ∧ cb < 0 ∧ cc < 0)) ∧
    w = ca • (x a - x v) + cb • (x b - x v) + cc • (x c - x v)

/-- A cone-hidden point lies strictly inside a projected triangle of points. -/
theorem hiddenInTriangles_of_cone {n k : ℕ} [NeZero k] {x : Fin n → ℝ³} {w : ℝ³} {lab : ZMod k → Fin n}
    (h : ∀ m, (∀ i, m ≠ lab i) → ConeHides x m w) : HiddenInTriangles x w lab := by
  intro m hm
  obtain ⟨a, b, c, ca, cb, cc, hD, hc, rfl⟩ := h m hm
  rcases det3_pos_triangle_of_cone (x m) (x a) (x b) (x c) ca cb cc hD hc with
    ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · exact ⟨x a, mem_image_of_mem _ (mem_univ _), x b, mem_image_of_mem _ (mem_univ _), x c,
      mem_image_of_mem _ (mem_univ _), h1, h2, h3, h4⟩
  · exact ⟨x a, mem_image_of_mem _ (mem_univ _), x c, mem_image_of_mem _ (mem_univ _), x b,
      mem_image_of_mem _ (mem_univ _), h1, h2, h3, h4⟩

/-- The Edge-Plane data (`hD` and the rows) of `Gen.EdgePlaneAny`. -/
def EPRows {n k : ℕ} [NeZero k] (x : Fin n → ℝ³) (lab : ZMod k → Fin n) (w : ℝ³) (a : ZMod k)
    (s α μ : ℝ) : Prop :=
  ⟪x (lab (a + 1)) - x (lab a), w⟫ ≠ 0 ∧
    ∀ i j : ZMod k, i ≠ a → (j = i ∨ j = i + 1) →
      0 < (α + μ * ⟪x (lab j) - x (lab a), w⟫) *
          Split.det3 (x (lab (i + 1)) - x (lab i)) (x (lab (a + 1)) - x (lab a)) w +
        s * Split.edgePlaneSpin (fun i => x (lab i)) w a i j

/-- **L1 (EPHide), general form.**  A strict rim `lab` at `w`, every point off the rim hidden by a tangent cone
at `w`, and the Edge-Plane rows of the rim points give `Gen.EdgePlaneAny x`.  The rows mention only rim points,
so the hidden points enter only through `HiddenInTriangles`. -/
theorem edgePlaneAny_of_cone_hidden {n k : ℕ} [NeZero k] (hk : 3 ≤ k) (x : Fin n → ℝ³) (lab : ZMod k → Fin n)
    (hinj : Function.Injective lab) (w : ℝ³) (hrim : StrictRimN x w lab)
    (hcone : ∀ m, (∀ i, m ≠ lab i) → ConeHides x m w) (a : ZMod k) (s α μ : ℝ)
    (hrows : EPRows x lab w a s α μ) : Gen.EdgePlaneAny x :=
  ⟨k, inferInstance, lab, w, a, s, α, μ, hk, hinj, hrim, hiddenInTriangles_of_cone hcone, hrows.1, hrows.2⟩

/-! ## Chambers of the facet-sign arrangement -/

/-- A view `u` with the facet pattern `pat` (true = facing up), a rim `lab` (`c` or its reverse) with positive
orientation, every point off the rim hidden by a tangent cone at `u`, and Edge-Plane rows on the rim. -/
def EPHideOn (F : S0xFac 9 s0x_S24 x) {k : ℕ} [NeZero k] (pat : Fin 9 → Bool) (c : ZMod k → Fin 7) : Prop :=
  ∃ (u : ℝ³) (lab : ZMod k → Fin 7) (a : ZMod k) (s α μ : ℝ),
    (∀ t, (pat t = true → 0 < ⟪F.N t, u⟫) ∧ (pat t = false → ⟪F.N t, u⟫ < 0)) ∧
    (lab = c ∨ lab = fun i => c (-i)) ∧
    0 < Split.det3 (x (lab 1) - x (lab 0)) (x (lab 2) - x (lab 0)) u ∧
    (∀ m, (∀ i, m ≠ lab i) → ConeHides x m u) ∧ EPRows x lab u a s α μ

/-- **L1 (EPHide), facet form.**  If `c` is the silhouette of the facing pattern `pat`, an `EPHideOn` view gives
`Gen.EdgePlaneAny x`: the strict rim comes from the facet signs. -/
theorem edgePlaneAny_of_epHideOn (F : S0xFac 9 s0x_S24 x) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (pat : Fin 9 → Bool) (c : ZMod k → Fin 7) (hc : Function.Injective c)
    (hcyc : S0xCycOK s0x_S24 c pat) (h : EPHideOn F pat c) : Gen.EdgePlaneAny x := by
  obtain ⟨u, lab, a, s, α, μ, hfac, hlab, hor, hhid, hrows⟩ := h
  obtain ⟨hinj, hrim⟩ := strictRimN_of_facets F hk c hc pat hcyc u hfac lab hlab hor
  exact edgePlaneAny_of_cone_hidden hk x lab hinj u hrim hhid a s α μ hrows

/-- Chamber H (mask `111112222`, rim `1.2.5.3.4.6`, hidden vertex `0`). -/
def patH : Fin 9 → Bool := fun t => decide (t.val < 5)
/-- Chamber A (`< 0` on facets `0,2,3,6`, `> 0` on `1,4,5,7,8`; rim `0.1.2.3.4`, hidden `5, 6`). -/
def patA : Fin 9 → Bool := ![false, true, false, false, true, true, false, true, true]
def cH : ZMod 6 → Fin 7 := ![1, 2, 5, 3, 4, 6]
def cA : ZMod 5 → Fin 7 := ![0, 1, 2, 3, 4]

theorem cH_inj : Function.Injective cH := by decide
theorem cA_inj : Function.Injective cA := by decide
theorem cH_cyc : S0xCycOK s0x_S24 cH patH := by decide
theorem cA_cyc : S0xCycOK s0x_S24 cA patA := by decide

/-- **EPHideChamber** (L1 form of the chamber statement): an Edge-Plane certificate at a view of chamber `H`,
`A` or `A` transported by `π24`. -/
def EPHideChamber (F : S0xFac 9 s0x_S24 x) : Prop :=
  EPHideOn F patH cH ∨ EPHideOn F patA cA ∨ EPHideOn (Sym.sym24 F) patA cA

/-- `EdgePlaneAny` is invariant under a relabelling of the points. -/
theorem edgePlaneAny_of_comp {n : ℕ} (π : Equiv.Perm (Fin n)) {y : Fin n → ℝ³}
    (h : Gen.EdgePlaneAny (y ∘ π)) : Gen.EdgePlaneAny y := by
  obtain ⟨k, hne, lab, w, a, s, α, μ, hk, hinj, hrim, hhid, hD, hrows⟩ := h
  refine ⟨k, hne, fun i => π (lab i), w, a, s, α, μ, hk, π.injective.comp hinj, ?_, ?_, hD, hrows⟩
  · intro m i h0 h1
    have := hrim (π.symm m) i (by rwa [Ne, Equiv.symm_apply_eq]) (by rwa [Ne, Equiv.symm_apply_eq])
    simpa using this
  · intro m hm
    obtain ⟨p, hp, q, hq, r, hr, h1, h2, h3, h4⟩ := hhid (π.symm m)
      (fun i => by rw [Ne, Equiv.symm_apply_eq]; exact hm i)
    have mem : ∀ z ∈ (univ.image (y ∘ π) : Finset ℝ³), z ∈ (univ.image y : Finset ℝ³) := by
      intro z hz
      obtain ⟨i, _, rfl⟩ := mem_image.1 hz
      exact mem_image_of_mem _ (mem_univ _)
    exact ⟨p, mem p hp, q, mem q hq, r, mem r hr, h1, by simpa using h2, by simpa using h3,
      by simpa using h4⟩

/-- **EPHideChamber gives `Gen.EdgePlaneAny`.** -/
theorem edgePlaneAny_of_epHideChamber (F : S0xFac 9 s0x_S24 x) (h : EPHideChamber F) :
    Gen.EdgePlaneAny x := by
  rcases h with h | h | h
  · exact edgePlaneAny_of_epHideOn F (by norm_num) patH cH cH_inj cH_cyc h
  · exact edgePlaneAny_of_epHideOn F (by norm_num) patA cA cA_inj cA_cyc h
  · exact edgePlaneAny_of_comp Sym.pi24
      (edgePlaneAny_of_epHideOn (Sym.sym24 F) (by norm_num) patA cA cA_inj cA_cyc h)

end Minimality.T24.EH
