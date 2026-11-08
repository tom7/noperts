module

public import Minimality.Type08S.L2.K91R

@[expose] public section

set_option maxHeartbeats 1000000

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option maxHeartbeats 6400000
set_option maxRecDepth 100000
namespace Minimality.Type08Sp.C2

noncomputable def k92Wn (u v x y : ℝ) : ℝ := u^2*x + u^2*y + u*v*x + u*v*y^2 + u*v*y + 2*u*x + 2*u*y - v^2*x*y - v*x*y + v*x + v*y + x + y
noncomputable def k92qr (u v x y : ℝ) : ℝ := ((1+u)*(x+y) - v*x*y)/(v*(x+y))
noncomputable def k92pp (u v x y : ℝ) : ℝ := ((u+v+1)+(1+v)*y)*(v*(x+y))/k92Wn u v x y
noncomputable def k92G (u v x y : ℝ) (x1 x2 x3 y1 y2 y3 : ℝ) : ℝ :=
  k91G (k92pp u v x y) (-1) (k92qr u v x y + x) (k92qr u v x y) (k92qr u v x y + y) x1 x2 x3 y1 y2 y3
noncomputable def k92Pm (u v m x y : ℝ) : ℝ := m * k92Wn u v x y + v*y*(v*x+x+y)
noncomputable def k92K (u v x y : ℝ) : ℝ := v^2*x*y + v*x*y - (u+v+1)*(x+y)
noncomputable def k92l (u v x y : ℝ) : ℝ := (1+v)*x - u*y
noncomputable def k92M3 (u v x y : ℝ) : ℝ := -u^2*x - u^2*y - u*v^2*y^2 - 2*u*v*x - u*v*y^2 - 2*u*v*y - 2*u*x - 2*u*y + v^3*x*y + 2*v^2*x*y - v^2*x - v^2*y + v*x*y - 2*v*x - 2*v*y - x - y
noncomputable def k92Nbv (u v m x y : ℝ) : ℝ := m*u^2*x + m*u^2*y - m*u*v*x*y + m*u*v*x + m*u*v*y + 2*m*u*x + 2*m*u*y + m*v^2*x^2 + m*v*x^2 + m*v*x + m*v*y + m*x + m*y + v^2*x*y
noncomputable def k92TB (u v x y : ℝ) : ℝ := u^2*x + u^2*y - u*v^2*x*y - u*v*x*y + 2*u*v*x + 2*u*v*y + 2*u*x + 2*u*y + v^3*x^2 + 2*v^2*x^2 + v^2*x + v^2*y + v*x^2 + 2*v*x + 2*v*y + x + y
noncomputable def k92TP (u v x y : ℝ) : ℝ := u^2*x + u^2*y - u*v^2*x*y - u*v*x*y + u*v*x + u*v*y + 2*u*x + 2*u*y + v^3*x^2 + 2*v^2*x^2 + v*x^2 + v*x + v*y + x + y
noncomputable def k92Q (u v x y : ℝ) : ℝ := u^2*x^2 + 2*u^2*x*y + u^2*y^2 - u*v^2*x*y^2 + u*v*x^2 + 2*u*v*x*y + u*v*y^2 + 2*u*x^2 + 4*u*x*y + 2*u*y^2 + v^3*x^2*y + v^2*x^2*y + v*x^2 + 2*v*x*y + v*y^2 + x^2 + 2*x*y + y^2
noncomputable def k92Ac (u v m x y : ℝ) : ℝ := -(u+v+1)*k92Pm u v m x y/k92Wn u v x y
noncomputable def k92Bc (u v m x y : ℝ) : ℝ := k92Nbv u v m x y/(v*(x+y))
/-- Rin X = <X, (-Bv) A + Av B> -/
noncomputable def k92Rin (u v m x y : ℝ) (x1 x2 x3 : ℝ) : ℝ := k92G u v x y x1 x2 x3 (-k92Bc u v m x y) (k92Ac u v m x y) 0

theorem k92_Av (u v m x y : ℝ) (hv : 0 < v) (hx : 0 < x) (hy : 0 < y) (hW : k92Wn u v x y ≠ 0) (hP : k92Pm u v m x y ≠ 0) :
    k92G u v x y 1 0 0 (-(u+1)) ((v+1)*m) (1+u*m-(v+1)) = k92Ac u v m x y := by
  have hxy : x + y ≠ 0 := by positivity
  have hv' : v ≠ 0 := hv.ne'
  simp only [k92G, k91G, k92pp, k92qr, k92Ac]
  field_simp
  simp only [k92Wn, k92Pm]
  ring

theorem k92_Bv (u v m x y : ℝ) (hv : 0 < v) (hx : 0 < x) (hy : 0 < y) (hW : k92Wn u v x y ≠ 0) (hP : k92Pm u v m x y ≠ 0) :
    k92G u v x y 0 1 0 (-(u+1)) ((v+1)*m) (1+u*m-(v+1)) = k92Bc u v m x y := by
  have hxy : x + y ≠ 0 := by positivity
  have hv' : v ≠ 0 := hv.ne'
  simp only [k92G, k91G, k92pp, k92qr, k92Bc]
  field_simp
  simp only [k92Wn, k92Nbv]
  ring

theorem k92_F1 (u v m x y : ℝ) (hv : 0 < v) (hx : 0 < x) (hy : 0 < y) (hW : k92Wn u v x y ≠ 0) (hP : k92Pm u v m x y ≠ 0) :
    k92Rin u v m x y u (v+1) 0 = -((u+v+1)*(m*u^2*v*x^2 + m*u^2*v*x*y + m*u^2*x^2 + 2*m*u^2*x*y + m*u^2*y^2 + m*u*v^2*x^2 + m*u*v^2*x*y + 2*m*u*v*x^2 + 3*m*u*v*x*y + m*u*v*y^2 + m*u*x^2 + 2*m*u*x*y + m*u*y^2 + u*x*y + u*y^2 + v^3*x^2*y + 2*v^2*x^2*y + v*x^2*y + v*x*y + v*y^2 + x*y + y^2)/k92Wn u v x y) := by
  have hxy : x + y ≠ 0 := by positivity
  have hv' : v ≠ 0 := hv.ne'
  simp only [k92Rin, k92G, k91G, k92pp, k92qr, k92Ac, k92Bc]
  field_simp
  simp only [k92Wn, k92Pm, k92Nbv]
  ring

theorem k92_F2 (u v m x y : ℝ) (hv : 0 < v) (hx : 0 < x) (hy : 0 < y) (hW : k92Wn u v x y ≠ 0) (hP : k92Pm u v m x y ≠ 0) :
    k92Rin u v m x y (u+1) v 0 = -((u+v+1)*(m*u^2*v*x^2 + m*u^2*v*x*y + m*u^2*x*y + m*u^2*y^2 + m*u*v^2*x^2 + m*u*v^2*x*y + 2*m*u*v*x^2 - m*u*v*x*y^2 + 3*m*u*v*x*y + m*u*v*y^2 + 2*m*u*x*y + 2*m*u*y^2 + m*v^2*x^2*y + m*v^2*x^2 + m*v^2*x*y + m*v*x^2*y + m*v*x^2 + 2*m*v*x*y + m*v*y^2 + m*x*y + m*y^2 + v^3*x^2*y + v^2*x^2*y + v^2*x*y^2)/k92Wn u v x y) := by
  have hxy : x + y ≠ 0 := by positivity
  have hv' : v ≠ 0 := hv.ne'
  simp only [k92Rin, k92G, k91G, k92pp, k92qr, k92Ac, k92Bc]
  field_simp
  simp only [k92Wn, k92Pm, k92Nbv]
  ring

theorem k92_zA (u v m x y : ℝ) (hv : 0 < v) (hx : 0 < x) (hy : 0 < y) (hW : k92Wn u v x y ≠ 0) (hP : k92Pm u v m x y ≠ 0) :
    k92Rin u v m x y 1 0 0 = -((m*u^2*x*y + m*u^2*y^2 + m*u*v^2*x^2 - m*u*v^2*x*y^2 + m*u*v^2*x*y + m*u*v*x^2 - m*u*v*x*y^2 + 3*m*u*v*x*y + 2*m*u*v*y^2 + 2*m*u*x*y + 2*m*u*y^2 + m*v^3*x^2*y + m*v^3*x^2 + m*v^3*x*y + 2*m*v^2*x^2*y + 2*m*v^2*x^2 + 3*m*v^2*x*y + m*v^2*y^2 + m*v*x^2*y + m*v*x^2 + 3*m*v*x*y + 2*m*v*y^2 + m*x*y + m*y^2 - u*v*x*y - u*v*y^2 + v^3*x*y^2 + v^2*x*y^2 - v^2*x*y - v^2*y^2 - v*x*y - v*y^2)/k92Wn u v x y) := by
  have hxy : x + y ≠ 0 := by positivity
  have hv' : v ≠ 0 := hv.ne'
  simp only [k92Rin, k92G, k91G, k92pp, k92qr, k92Ac, k92Bc]
  field_simp
  simp only [k92Wn, k92Pm, k92Nbv]
  ring

theorem k92_zB (u v m x y : ℝ) (hv : 0 < v) (hx : 0 < x) (hy : 0 < y) (hW : k92Wn u v x y ≠ 0) (hP : k92Pm u v m x y ≠ 0) :
    k92Rin u v m x y 0 1 0 = -((m*u^3*x^2 + m*u^3*x*y + m*u^2*v*x^2 + m*u^2*v*x*y^2 + m*u^2*v*x*y + 2*m*u^2*x^2 + 2*m*u^2*x*y - m*u*v^2*x^2*y - m*u*v*x^2*y + m*u*v*x^2 + m*u*v*x*y + m*u*x^2 + m*u*x*y + u^2*x*y + u^2*y^2 + u*v^2*x^2*y - u*v^2*x*y^2 + u*v*x^2*y + u*v*x*y + u*v*y^2 + 2*u*x*y + 2*u*y^2 + v^3*x^2*y + 2*v^2*x^2*y + v*x^2*y + v*x*y + v*y^2 + x*y + y^2)/k92Wn u v x y) := by
  have hxy : x + y ≠ 0 := by positivity
  have hv' : v ≠ 0 := hv.ne'
  simp only [k92Rin, k92G, k91G, k92pp, k92qr, k92Ac, k92Bc]
  field_simp
  simp only [k92Wn, k92Pm, k92Nbv]
  ring

theorem k92_zab (u v m x y : ℝ) (hv : 0 < v) (hx : 0 < x) (hy : 0 < y) (hW : k92Wn u v x y ≠ 0) (hP : k92Pm u v m x y ≠ 0) :
    k92Rin u v m x y (-u) 0 (-(v+1)) = (u+v+1)*(m*k92l u v x y - y)*k92K u v x y/k92Wn u v x y := by
  have hxy : x + y ≠ 0 := by positivity
  have hv' : v ≠ 0 := hv.ne'
  simp only [k92Rin, k92G, k91G, k92pp, k92qr, k92Ac, k92Bc]
  field_simp
  simp only [k92Wn, k92Pm, k92K, k92l, k92Nbv]
  ring

theorem k92_DP (u v m x y : ℝ) (hv : 0 < v) (hx : 0 < x) (hy : 0 < y) (hW : k92Wn u v x y ≠ 0) (hP : k92Pm u v m x y ≠ 0) :
    k92G u v x y u 0 (v+1) 1 0 0 = (u+v+1)*k92K u v x y/k92Wn u v x y := by
  have hxy : x + y ≠ 0 := by positivity
  have hv' : v ≠ 0 := hv.ne'
  simp only [k92G, k91G, k92pp, k92qr]
  field_simp
  simp only [k92Wn, k92K]
  ring

theorem k92_PB (u v m x y : ℝ) (hv : 0 < v) (hx : 0 < x) (hy : 0 < y) (hW : k92Wn u v x y ≠ 0) (hP : k92Pm u v m x y ≠ 0) :
    -u*k92Ac u v m x y - (v+1)*k92Bc u v m x y = (v^2*y*k92l u v x y*k92K u v x y - k92Wn u v x y*k92TB u v x y*m)/(v*(x+y)*k92Wn u v x y) := by
  have hxy : x + y ≠ 0 := by positivity
  have hv' : v ≠ 0 := hv.ne'
  simp only [k92Ac, k92Bc]
  field_simp
  simp only [k92Wn, k92Pm, k92K, k92l, k92Nbv, k92TB]
  ring

theorem k92_PC (u v m x y : ℝ) (hv : 0 < v) (hx : 0 < x) (hy : 0 < y) (hW : k92Wn u v x y ≠ 0) (hP : k92Pm u v m x y ≠ 0) :
    (u+1)*k92Ac u v m x y + v*k92Bc u v m x y = (-v*y*k92Q u v x y + v*x*k92l u v x y*k92Wn u v x y*m)/((x+y)*k92Wn u v x y) := by
  have hxy : x + y ≠ 0 := by positivity
  have hv' : v ≠ 0 := hv.ne'
  simp only [k92Ac, k92Bc]
  field_simp
  simp only [k92Wn, k92Pm, k92l, k92Nbv, k92Q]
  ring

theorem k92_Q1 (u v m x y : ℝ) (hv : 0 < v) (hx : 0 < x) (hy : 0 < y) (hW : k92Wn u v x y ≠ 0) (hP : k92Pm u v m x y ≠ 0) :
    k92G u v x y (u+1) (-((v+1)*m)) (v+1-(1+u*m)) 0 0 1 = (v^2*y^2 - m*k92Wn u v x y)/(v*(x+y)) := by
  have hxy : x + y ≠ 0 := by positivity
  have hv' : v ≠ 0 := hv.ne'
  simp only [k92G, k91G, k92pp, k92qr]
  field_simp
  simp only [k92Wn]
  ring

theorem k92_X3 (u v m x y : ℝ) (hv : 0 < v) (hx : 0 < x) (hy : 0 < y) (hW : k92Wn u v x y ≠ 0) (hP : k92Pm u v m x y ≠ 0) :
    k92G u v x y (-u) (-(v+1)) 0 (-u) 0 (-(v+1)) = k92K u v x y*k92M3 u v x y/(v*(x+y)*k92Wn u v x y) := by
  have hxy : x + y ≠ 0 := by positivity
  have hv' : v ≠ 0 := hv.ne'
  simp only [k92G, k91G, k92pp, k92qr]
  field_simp
  simp only [k92Wn, k92K, k92M3]
  ring

theorem k92_X4 (u v m x y : ℝ) (hv : 0 < v) (hx : 0 < x) (hy : 0 < y) (hW : k92Wn u v x y ≠ 0) (hP : k92Pm u v m x y ≠ 0) :
    k92G u v x y u (v+1) 0 (u+1) 0 v = v*y*k92l u v x y*k92K u v x y/((x+y)*k92Wn u v x y) := by
  have hxy : x + y ≠ 0 := by positivity
  have hv' : v ≠ 0 := hv.ne'
  simp only [k92G, k91G, k92pp, k92qr]
  field_simp
  simp only [k92Wn, k92K, k92l]
  ring

theorem k92_H (u v m x y : ℝ) (hv : 0 < v) (hx : 0 < x) (hy : 0 < y) (hW : k92Wn u v x y ≠ 0) (hP : k92Pm u v m x y ≠ 0) :
    k92G u v x y (u+1) (v+1-(v+1)*m) (-(1+u*m)) (u+1) 0 v = v*y*k92l u v x y*k92Pm u v m x y/((x+y)*k92Wn u v x y) := by
  have hxy : x + y ≠ 0 := by positivity
  have hv' : v ≠ 0 := hv.ne'
  simp only [k92G, k91G, k92pp, k92qr]
  field_simp
  simp only [k92Wn, k92Pm, k92l]
  ring

end Minimality.Type08Sp.C2
