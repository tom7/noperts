module

public import Minimality.Type08S.L2.K88C

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option maxHeartbeats 1000000
open scoped RealInnerProductSpace
open Minimality Minimality.Type08Sp Minimality.Type08Sp.C2

theorem k88_ev {p q r u v : ℝ³} {pp s qq qr rr : ℝ} (h1 : ⟪p,p⟫ = pp) (h2 : ⟪p,q⟫ = -s) (h3 : ⟪p,r⟫ = -s)
    (h4 : ⟪q,q⟫ = qq) (h5 : ⟪q,r⟫ = qr) (h6 : ⟪r,r⟫ = rr) {x y z x' y' z' : ℝ}
    (hu : u = x • p + y • q + z • r) (hv : v = x' • p + y' • q + z' • r) :
    ⟪u, v⟫ = x*x'*pp - (x*y'+y*x')*s - (x*z'+z*x')*s + y*y'*qq + (y*z'+z*y')*qr + z*z'*rr := by
  rw [hu, hv, k71_gip, h1, h2, h3, h4, h5, h6]; ring

theorem k88_chart {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 pp s qq qr rr : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6)
    (h1 : ⟪a-d,a-d⟫ = pp) (h2 : ⟪a-d,b-d⟫ = -s) (h3 : ⟪a-d,c-d⟫ = -s)
    (h4 : ⟪b-d,b-d⟫ = qq) (h5 : ⟪b-d,c-d⟫ = qr) (h6 : ⟪c-d,c-d⟫ = rr) :
    ⟪b - a, b - a⟫ = pp + qq + 2*s ∧
    ⟪a' - a, b - a⟫ = β6*qq + β6*s + γ6*qr + γ6*s + pp + s ∧
    ⟪b' - a, b - a⟫ = -α1*pp - α1*s + β1*qr + β1*s + pp + s ∧
    ⟪d - a, b - a⟫ = pp + s ∧
    ⟪c' - a, b - a⟫ = -α1*pp - α1*s + β1*qq + β1*s + pp + s ∧
    ⟪c - a, b - a⟫ = pp + qr + 2*s ∧
    ⟪a - d, a' - b'⟫ = -α1*pp - β6*s + β1*s - γ6*s ∧
    ⟪a - c', a - b'⟫ = α1^2*pp - 2*α1*β1*s - 2*α1*pp + β1^2*qr + 2*β1*s + pp ∧
    ⟪c' - a, b' - c⟫ = α1^2*pp - 2*α1*β1*s - α1*pp + α1*s + β1^2*qr - β1*qr + β1*s - s ∧
    ⟪c' - a', b' - c⟫ = α1^2*pp + α1*β6*s - 2*α1*β1*s + α1*γ6*s + α1*s - β6*β1*qr + β6*qr + β1^2*qr - β1*γ6*rr - β1*qr + γ6*rr ∧
    ⟪a - c', d - a'⟫ = -α1*β6*s - α1*γ6*s + β6*β1*qq + β6*s + β1*γ6*qr + γ6*s := by
  obtain ⟨-, hc', hb', ha', -⟩ := hC
  exact ⟨(k88_ev h1 h2 h3 h4 h5 h6 (x := -1) (y := 1) (z := 0) (x' := -1) (y' := 1) (z' := 0) (u := b - a) (v := b - a) (by subst hc' hb' ha'; module) (by subst hc' hb' ha'; module)).trans (by ring),
    (k88_ev h1 h2 h3 h4 h5 h6 (x := -1) (y := β6) (z := γ6) (x' := -1) (y' := 1) (z' := 0) (u := a' - a) (v := b - a) (by subst hc' hb' ha'; module) (by subst hc' hb' ha'; module)).trans (by ring),
    (k88_ev h1 h2 h3 h4 h5 h6 (x := α1 - 1) (y := 0) (z := β1) (x' := -1) (y' := 1) (z' := 0) (u := b' - a) (v := b - a) (by subst hc' hb' ha'; module) (by subst hc' hb' ha'; module)).trans (by ring),
    (k88_ev h1 h2 h3 h4 h5 h6 (x := -1) (y := 0) (z := 0) (x' := -1) (y' := 1) (z' := 0) (u := d - a) (v := b - a) (by subst hc' hb' ha'; module) (by subst hc' hb' ha'; module)).trans (by ring),
    (k88_ev h1 h2 h3 h4 h5 h6 (x := α1 - 1) (y := β1) (z := 0) (x' := -1) (y' := 1) (z' := 0) (u := c' - a) (v := b - a) (by subst hc' hb' ha'; module) (by subst hc' hb' ha'; module)).trans (by ring),
    (k88_ev h1 h2 h3 h4 h5 h6 (x := -1) (y := 0) (z := 1) (x' := -1) (y' := 1) (z' := 0) (u := c - a) (v := b - a) (by subst hc' hb' ha'; module) (by subst hc' hb' ha'; module)).trans (by ring),
    (k88_ev h1 h2 h3 h4 h5 h6 (x := 1) (y := 0) (z := 0) (x' := -α1) (y' := β6) (z' := -β1 + γ6) (u := a - d) (v := a' - b') (by subst hc' hb' ha'; module) (by subst hc' hb' ha'; module)).trans (by ring),
    (k88_ev h1 h2 h3 h4 h5 h6 (x := 1 - α1) (y := -β1) (z := 0) (x' := 1 - α1) (y' := 0) (z' := -β1) (u := a - c') (v := a - b') (by subst hc' hb' ha'; module) (by subst hc' hb' ha'; module)).trans (by ring),
    (k88_ev h1 h2 h3 h4 h5 h6 (x := α1 - 1) (y := β1) (z := 0) (x' := α1) (y' := 0) (z' := β1 - 1) (u := c' - a) (v := b' - c) (by subst hc' hb' ha'; module) (by subst hc' hb' ha'; module)).trans (by ring),
    (k88_ev h1 h2 h3 h4 h5 h6 (x := α1) (y := -β6 + β1) (z := -γ6) (x' := α1) (y' := 0) (z' := β1 - 1) (u := c' - a') (v := b' - c) (by subst hc' hb' ha'; module) (by subst hc' hb' ha'; module)).trans (by ring),
    (k88_ev h1 h2 h3 h4 h5 h6 (x := 1 - α1) (y := -β1) (z := 0) (x' := 0) (y' := -β6) (z' := -γ6) (u := a - c') (v := d - a') (by subst hc' hb' ha'; module) (by subst hc' hb' ha'; module)).trans (by ring)⟩

theorem k88_Z {a a' b b' c c' d : ℝ³} {α1 β1 β6 γ6 pp s qq qr rr : ℝ}
    (hC : K6mCoords a a' b b' c c' d α1 β1 β6 γ6)
    (h1 : ⟪a-d,a-d⟫ = pp) (h2 : ⟪a-d,b-d⟫ = -s) (h3 : ⟪a-d,c-d⟫ = -s)
    (h4 : ⟪b-d,b-d⟫ = qq) (h5 : ⟪b-d,c-d⟫ = qr) (h6 : ⟪c-d,c-d⟫ = rr)
    (hAv : ⟪a - d, a' - b'⟫ ≠ 0)
    (hzab : ⟪a - b', k61_R a a' b b' d⟫ = 0) (hzba : ⟪a' - b, k61_R a a' b b' d⟫ = 0) :
    (α1*β6*pp*qq - α1*β6*s^2 + α1*γ6*pp*qr - α1*γ6*s^2 - β6*β1*qq*s + β6*β1*qr*s - β6*pp*qq + β6*s^2 + β1*pp*qr - β1*s^2 - γ6*pp*qr + γ6*s^2) = 0 ∧ (-α1*β6*pp*qq + α1*β6*s^2 - α1*γ6*pp*qr + α1*γ6*s^2 + α1*pp*qq - α1*s^2 + β6*β1*qq*s - β6*β1*qr*s - β1*qq*s + β1*qr*s + γ6*qq*s - γ6*qr*s) = 0 := by
  obtain ⟨-, hc', hb', ha', -⟩ := hC
  have key : ∀ x : ℝ³, ⟪x, k61_R a a' b b' d⟫ = 0 →
      ⟪x, b - d⟫ * ⟪a - d, a' - b'⟫ - ⟪b - d, a' - b'⟫ * ⟪x, a - d⟫ = 0 := by
    intro x hx
    unfold k61_R k61_lam at hx
    rw [inner_add_right, inner_smul_right] at hx
    calc ⟪x, b - d⟫ * ⟪a - d, a' - b'⟫ - ⟪b - d, a' - b'⟫ * ⟪x, a - d⟫
        = ⟪a - d, a' - b'⟫ * (⟪x, b - d⟫ + (-⟪b - d, a' - b'⟫ / ⟪a - d, a' - b'⟫) * ⟪x, a - d⟫) := by
          field_simp; ring
      _ = 0 := by rw [hx, mul_zero]
  have k1 := key _ hzab
  have k2 := key _ hzba
  have ev := fun {u v : ℝ³} {x y z x' y' z' : ℝ} (hu : u = x • (a-d) + y • (b-d) + z • (c-d))
    (hv : v = x' • (a-d) + y' • (b-d) + z' • (c-d)) => k88_ev h1 h2 h3 h4 h5 h6 hu hv
  have eAv : ⟪a - d, a' - b'⟫ = -α1*pp - β6*s + β1*s - γ6*s :=
    (ev (x := 1) (y := 0) (z := 0) (x' := -α1) (y' := β6) (z' := γ6 - β1) (by module) (by subst hb' ha'; module)).trans (by ring)
  have e1 : ⟪a - b', b - d⟫ = (1-α1)*(-s) + (-β1)*qr := (ev (x := 1-α1) (y := 0) (z := -β1) (x' := 0) (y' := 1) (z' := 0) (by subst hb'; module) (by module)).trans (by ring)
  have e2 : ⟪b - d, a' - b'⟫ = α1*s + β6*qq + (γ6-β1)*qr := (ev (x := 0) (y := 1) (z := 0) (x' := -α1) (y' := β6) (z' := γ6 - β1) (by module) (by subst hb' ha'; module)).trans (by ring)
  have e3 : ⟪a - b', a - d⟫ = (1-α1)*pp + β1*s := (ev (x := 1-α1) (y := 0) (z := -β1) (x' := 1) (y' := 0) (z' := 0) (by subst hb'; module) (by module)).trans (by ring)
  have e4 : ⟪a' - b, b - d⟫ = (β6-1)*qq + γ6*qr := (ev (x := 0) (y := β6-1) (z := γ6) (x' := 0) (y' := 1) (z' := 0) (by subst ha'; module) (by module)).trans (by ring)
  have e5 : ⟪a' - b, a - d⟫ = -(β6-1)*s - γ6*s := (ev (x := 0) (y := β6-1) (z := γ6) (x' := 1) (y' := 0) (z' := 0) (by subst ha'; module) (by module)).trans (by ring)
  rw [eAv, e1, e2, e3] at k1
  rw [eAv, e4, e2, e5] at k2
  constructor
  · linear_combination k1
  · linear_combination k2
