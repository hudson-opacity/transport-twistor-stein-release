import TransportOkaGrauert.SimpleRadialSpray
import TransportOkaGrauert.SimpleRadialDivision

/-! # Radial and transverse derivatives in geodesic normal coordinates -/

noncomputable section
namespace TransportOkaGrauert.SimpleRadialColumns
open Complex Set Metric Filter ConformalFrame SimpleDiskTarget SimpleRadialStar
open scoped ContDiff Topology

structure NormalChart (σ : ℂ → ℝ) (a : ℂ) where
  f : ℂ → ℂ
  δ : ℂ → ℝ
  F : (ℝ × ℝ) → Chart
  L : ℂ → ℂ
  sf : ContDiff ℝ ∞ f
  sd : ContDiff ℝ ∞ δ
  sF : ContDiff ℝ ∞ F
  sL : ContDiffOn ℝ ∞ L (ball 0 1)
  centre : f 0 = a
  right : ∀ y ∈ ball (0:ℂ) 1, L y ∈ retained f 1 ∧ f (L y) = y
  left : ∀ x ∈ retained f 1, f x ∈ ball (0:ℂ) 1 → L (f x) = x
  initial : ∀ α, F (α,0) = (a,α,0)
  polar : ∀ α t, (F (α,t)).1 = f (t • (Circle.exp α : ℂ)) ∧
    (F (α,t)).2.1 = α + δ (t • (Circle.exp α : ℂ))
  ode : ∀ q : ℝ × ℝ, ‖(F q).1‖ ≤ 1 →
    (fun u => fderiv ℝ F u (0,1)) =ᶠ[𝓝 q] X σ ∘ F

def chart {σ : ℂ → ℝ} (simple : SimpleMetric σ) {a : ℂ} (ha : ‖a‖ < 1) : NormalChart σ a :=
  Classical.choice (by
    obtain ⟨f,δ,F,L,sf,sd,sF,sL,h0,r,l,i,p,o⟩ := SimpleRadialSpray.normal_coordinates simple ha
    exact ⟨⟨f,δ,F,L,sf,sd,sF,sL,h0,r,l,i,p,o⟩⟩)

namespace NormalChart
variable {σ : ℂ → ℝ} {a : ℂ} (d : NormalChart σ a)

def D := beforeExit d.f 1

theorem openD : IsOpen d.D := isOpen_beforeExit d.sf.continuous 1

theorem inD {y : ℂ} (hy : y ∈ ball (0:ℂ) 1) (simple : SimpleMetric σ) (ha : ‖a‖ < 1) : d.L y ∈ d.D := by
  obtain ⟨h,r⟩ := d.right y hy
  have closed := (h : ∀ t ∈ Icc (0:ℝ) 1, ‖d.f (t • d.L y)‖ ≤ 1)
  by_cases hz : d.L y = 0
  · intro t _; simpa [hz,d.centre] using ha
  let x := d.L y
  let α := x.arg
  let n := ‖x‖
  have hp : 0 < n := norm_pos_iff.mpr hz
  have repr (t : ℝ) : along d.f x t = (d.F (α,t)).1 := by
    rw [(d.polar α t).1]
    change d.f ((t/n) • x) = _
    calc
      _ = d.f ((t/n) • (n • (Circle.exp α : ℂ))) := by rw [SimpleRadialVariation.polar_angle x]
      _ = _ := by rw [smul_smul,div_mul_cancel₀ _ hp.ne']
  have whole (t : ℝ) (ht : t ∈ Icc 0 n) : ‖(d.F (α,t)).1‖ ≤ 1 := by
    rw [← repr]; exact mem_closedBall_zero_iff.mp (along_retained hz h t ht)
  have start : fderiv ℝ d.F (α,0) (1,0) = V (d.F (α,0)) := by
    have line : HasDerivAt (fun s : ℝ => (s,(0:ℝ))) (1,0) α :=
      (hasDerivAt_id α).prodMk (hasDerivAt_const α 0)
    have actual := (d.sF.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt α line
    exact actual.unique (((hasDerivAt_const α a).prodMk ((hasDerivAt_id α).prodMk (hasDerivAt_const α (0:ℝ)))).congr_of_eventuallyEq (.of_forall d.initial))
  have geo := (SimpleRadialVariation.jacobi_of_flow simple.smooth hp.le d.F (fun _ _ => d.sF.contDiffAt)
    (fun t ht => d.ode _ (whole t ht)) start).1
  intro t ht
  rcases lt_or_eq_of_le ht.2 with h'|he
  · have hit := no_interior_contact simple geo (by simpa [d.initial] using ha) whole
      (t*n) ⟨mul_nonneg ht.1 hp.le, by simpa using mul_lt_mul_of_pos_right h' hp⟩
    rw [← repr] at hit
    exact (along_scaled d.f (x := x) hz t) ▸ hit
  · simpa [he,r] using mem_ball_zero_iff.mp hy

def frame (x : ℂ) : ℂ := Circle.exp (d.δ x)

theorem frame_smooth : ContDiff ℝ ∞ d.frame :=
  ((Complex.ofRealCLM.contDiff.comp d.sd).mul (contDiff_const (c := I))).cexp

/-- The base isothermal vector represented by a fixed normal-frame vector. -/
def base (x : ℂ) : ℂ →L[ℝ] ℂ := (ContinuousLinearMap.mul ℝ ℂ)
  ((Real.exp (-σ (d.f x)) : ℂ) * d.frame x)

theorem base_smooth (sσ : ContDiff ℝ ∞ σ) : ContDiff ℝ ∞ d.base :=
  (ContinuousLinearMap.mul ℝ ℂ).contDiff.comp
    ((Complex.ofRealCLM.contDiff.comp (sσ.comp d.sf).neg.exp).mul d.frame_smooth)

theorem polar_columns (simple : SimpleMetric σ) {x : ℂ} (hx : x ∈ d.D) (xn : x ≠ 0) :
    fderiv ℝ d.f x x = d.base x x ∧
    fderiv ℝ d.δ x x = fderiv ℝ σ (d.f x) (I * d.base x x) ∧
    ∃ k : ℝ, 0 < k ∧ fderiv ℝ d.f x (I*x) = k • d.base x (I*x) := by
  let α := x.arg
  let r := ‖x‖
  let w : ℂ := Circle.exp α
  let θ := (d.F (α,r)).2.1
  let v : ℂ := Circle.exp θ
  have hp : 0 < r := norm_pos_iff.mpr xn
  have hr : r • w = x := SimpleRadialVariation.polar_angle x
  have zR : (d.F (α,r)).1 = d.f x := (d.polar α r).1.trans (congrArg d.f hr)
  have vR : d.frame x * w = v := by
    change _ = (Circle.exp (d.F (α,r)).2.1 : ℂ)
    rw [(d.polar α r).2,hr,Circle.exp_add]
    change d.frame x * w = w * d.frame x
    exact mul_comm _ _
  have temp (t : ℝ) (ht : t ∈ Icc 0 r) : ‖(d.F (α,t)).1‖ ≤ 1 := by
    rw [(d.polar α t).1]
    have eq : t • w = (t/r) • x := by rw [← hr,smul_smul,div_mul_cancel₀ _ hp.ne']
    rw [show (Circle.exp α : ℂ) = w from rfl, eq]
    exact (hx (t/r) ⟨div_nonneg ht.1 hp.le,(div_le_one hp).mpr ht.2⟩).le
  have init : fderiv ℝ d.F (α,0) (1,0) = V (d.F (α,0)) := by
    have line := (hasDerivAt_id α).prodMk (hasDerivAt_const α (0:ℝ))
    have actual := (d.sF.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt α line
    exact actual.unique (((hasDerivAt_const α a).prodMk ((hasDerivAt_id α).prodMk (hasDerivAt_const α (0:ℝ)))).congr_of_eventuallyEq (.of_forall d.initial))
  obtain ⟨geo,j,dj,oj,j0,j1,formula⟩ := SimpleRadialVariation.jacobi_of_flow simple.smooth hp.le d.F
    (fun _ _ => d.sF.contDiffAt) (fun t ht => d.ode _ (temp t ht)) init
  have jpos := ChartJacobi.normalized_jacobi_positive simple hp geo
    (fun t ht => mem_closedBall_zero_iff.mpr (temp t ht)) oj j0 j1
  let e := Real.exp (-σ (d.f x))
  have bv : d.base x x = r • (e • v) := by
    change ((e:ℂ) * d.frame x) * x = _
    conv_lhs => arg 2; rw [← hr]
    rw [← vR]
    simp only [Complex.real_smul]
    ring
  have bIv : d.base x (I*x) = I * d.base x x := by change _ * (I*x) = I*(_*x); ring
  have odeR : fderiv ℝ d.F (α,r) (0,1) = X σ (d.F (α,r)) :=
    (d.ode _ (temp r (right_mem_Icc.mpr hp.le))).self_of_nhds
  have line := (hasDerivAt_const r α).prodMk (hasDerivAt_id r)
  have der := (d.sF.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt r line
  have travel := (hasDerivAt_id r).smul_const w
  have baseJet := (d.sf.differentiable (by simp) (r • w)).hasFDerivAt.comp_hasDerivAt r travel
  have phaseJet := ((d.sd.differentiable (by simp) (r • w)).hasFDerivAt.comp_hasDerivAt r travel).const_add α
  have baseEq := baseJet.unique (((ContinuousLinearMap.fst ℝ ℂ (ℝ × ℝ)).hasFDerivAt.comp_hasDerivAt r der).congr_of_eventuallyEq
    (.of_forall fun t => (d.polar α t).1.symm))
  have phaseEq := phaseJet.unique ((((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (.snd ℝ ℂ (ℝ × ℝ))).hasFDerivAt.comp_hasDerivAt r der).congr_of_eventuallyEq
    (.of_forall fun t => (d.polar α t).2.symm))
  change fderiv ℝ d.f (r•w) ((1:ℝ)•w) = (fderiv ℝ d.F (α,r) (0,1)).1 at baseEq
  change fderiv ℝ d.δ (r•w) ((1:ℝ)•w) = (fderiv ℝ d.F (α,r) (0,1)).2.1 at phaseEq
  rw [hr,one_smul,odeR,(SimpleRadialVariation.chart_columns σ _).1,zR] at baseEq phaseEq
  have first : fderiv ℝ d.f x x = d.base x x := by
    calc
      _ = r • fderiv ℝ d.f x w := by rw [← map_smul,hr]
      _ = _ := by rw [baseEq,bv]; rfl
  refine ⟨first,?_,j r / r,div_pos jpos hp,?_⟩
  · have drift : Isothermal.angularDrift σ (d.f x) (Circle.exp θ) = fderiv ℝ σ (d.f x) (I*v) := by
      rw [show I*v = normal θ from (SimpleRadialVariation.circle_normal _).symm]
      simp only [normal, map_smul, map_add, smul_eq_mul, Isothermal.angularDrift,Circle.coe_exp,
        Complex.exp_ofReal_mul_I_re,Complex.exp_ofReal_mul_I_im]
      ring
    calc
      _ = r • fderiv ℝ d.δ x w := by rw [← map_smul,hr]
      _ = _ := by
        rw [phaseEq,bv]
        change r * (e * Isothermal.angularDrift σ (d.f x) (Circle.exp θ)) = _
        rw [drift,mul_smul_comm,mul_smul_comm,map_smul,map_smul]
        rfl
  · have ab := (SimpleRadialVariation.angle_velocity α).const_smul r
    have zjet := (d.sf.differentiable (by simp) (r•w)).hasFDerivAt.comp_hasDerivAt α ab
    have ajet := (ContinuousLinearMap.fst ℝ ℂ (ℝ × ℝ)).hasFDerivAt.comp_hasDerivAt α
      ((d.sF.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt α
        ((hasDerivAt_id α).prodMk (hasDerivAt_const α r)))
    have actual := zjet.unique (ajet.congr_of_eventuallyEq (.of_forall fun s => (d.polar s r).1.symm))
    change fderiv ℝ d.f (r•w) (r • (I*w)) = (fderiv ℝ d.F (α,r) (1,0)).1 at actual
    rw [hr,← mul_smul_comm,hr] at actual
    rw [actual, formula r (right_mem_Icc.mpr hp.le)]
    dsimp only
    rw [zR,bIv,bv]
    change (j r * e) • (I*v) = (j r / r) • (I*(r • (e • v)))
    rw [mul_smul_comm,mul_smul_comm,smul_smul,div_mul_cancel₀ _ hp.ne',smul_smul]

end NormalChart
end TransportOkaGrauert.SimpleRadialColumns
