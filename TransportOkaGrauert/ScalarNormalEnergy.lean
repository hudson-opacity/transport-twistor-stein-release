import TransportOkaGrauert.ScalarRayPairing

/-! # The normal energy is a weighted square of complete ray integrals -/
noncomputable section
namespace TransportOkaGrauert.ScalarRayPairing
open SimpleDiskTarget JacobiEnlargement GeodesicFlowExtension ScalarGeneralFlow PathContinuation
open Set Metric MeasureTheory Filter Complex
open scoped ContDiff Topology Interval

variable {σ : ℂ → ℝ} (F : Flow σ)

theorem energy_square (W : Window F) {r : ℝ} (hr : 0 ≤ r) (hr₁ : r < 1) :
    ∃ w : AngleTrace, ContDiff ℝ ∞ w ∧ period w ∧ supported w ∧ (∀ p, 0 ≤ w p) ∧
      (∀ p : State, ‖p.1‖ ≤ r → 0 < w p) ∧
      ∀ f : AngleTrace, ContDiff ℝ ∞ f → period f → (∀ p, r < ‖p.1‖ → f p = 0) →
        integral F (fun p => f p * full F W f p) = integral F (fun p => w p * (full F W f p)^2) := by
  let χ : ContDiffBump (0:ℂ) := ⟨(1+r)/2,1,by linarith,by linarith⟩
  let b := fun p : State => χ p.1
  have sb : ContDiff ℝ ∞ b := χ.contDiff.comp contDiff_fst
  have pb : period b := fun p => by simp [b]
  have zb : supported b := fun p hp => χ.zero_of_le_dist (by simpa [χ] using hp.le)
  have positive_b (p : State) (hp : ‖p.1‖ ≤ r) : b p = 1 := χ.one_of_mem_closedBall
    (by simp only [mem_closedBall,dist_zero_right]; change ‖p.1‖ ≤ (1+r)/2; linarith)
  let B := full F W b
  have sB := full_smooth F W sb
  have pB := full_period F W pb
  have invB := full_constant F W sb zb
  have nonnegB (p : State) : 0 ≤ B p := by
    rw [show B p = _ from full_eq F W sb.continuous p]
    exact intervalIntegral.integral_nonneg_of_forall (by linarith [W.pos]) (fun _ => χ.nonneg)
  have positiveB (p : State) (hp : ‖p.1‖ ≤ r) : 0 < B p := by
    rw [show B p = _ from full_eq F W sb.continuous p]
    apply intervalIntegral.integral_pos (by linarith [W.pos])
      (sb.continuous.comp (F.smooth.continuous.comp (continuous_const.prodMk continuous_id))).continuousOn
      (fun _ _ => χ.nonneg)
    exact ⟨0,⟨by linarith [W.pos],W.pos.le⟩,by change 0 < b (F.val (p,0)); rw [F.initial,positive_b p hp]; norm_num⟩
  let K := closedBall (0:ℂ) r ×ˢ Icc (-Real.pi) Real.pi
  have cK : IsCompact K := (isCompact_closedBall _ _).prod isCompact_Icc
  have ok : (0 : State) ∈ K := ⟨by simpa using hr,⟨(neg_nonpos.mpr Real.pi_pos.le),Real.pi_pos.le⟩⟩
  obtain ⟨q,hq,hmin⟩ := cK.exists_isMinOn ⟨0,ok⟩ sB.continuous.continuousOn
  let δ := B q
  have dp : 0 < δ := positiveB q (mem_closedBall_zero_iff.mp hq.1)
  let ρ : ContDiffBump (0:ℝ) := ⟨δ/2,δ,by positivity,by linarith⟩
  let D := fun p => B p + ρ (B p)
  have sD : ContDiff ℝ ∞ D := sB.add (ρ.contDiff.comp sB)
  have dpos (p : State) : 0 < D p := by
    rcases eq_or_lt_of_le (nonnegB p) with hz|hz
    · have one : ρ 0 = 1 := ρ.one_of_mem_closedBall (mem_closedBall_self ρ.rIn_pos.le)
      simp [D,← hz,one]
    · exact add_pos_of_pos_of_nonneg hz ρ.nonneg
  let w := fun p => b p / D p
  have sw : ContDiff ℝ ∞ w := sb.div sD (fun p => (dpos p).ne')
  have pw : period w := fun p => by simp only [w,D,pb p,show B (p+(0,2*Real.pi)) = B p from pB p]
  have zw : supported w := fun p h => by simp [w,zb p h]
  have wp (p : State) (h : ‖p.1‖ ≤ r) : 0 < w p := by simp [w,positive_b _ h,dpos]
  refine ⟨w,sw,pw,zw,fun p => div_nonneg χ.nonneg (dpos p).le,wp,?_⟩
  intro f hf pf zf
  have zf₁ : supported f := fun p hp => zf _ (hr₁.trans hp)
  let A := full F W f
  let h := fun p => A p / D p
  let v := fun p => b p * h p
  have sA := full_smooth F W hf
  have pA := full_period F W pf
  have sc : ContDiff ℝ ∞ h := sA.div sD (fun p => (dpos p).ne')
  have sv : ContDiff ℝ ∞ v := sb.mul sc
  have pv : period v := fun p => by
    simp only [v,h,D,show A (p+(0,2*Real.pi)) = A p from pA p,
      show B (p+(0,2*Real.pi)) = B p from pB p,pb p]
  have zv : supported v := fun p hp => by simp [v,zb p hp]
  have inv : orbit_constant F h := fun p hp t ht => by
    simp only [h,D,show A (F.val (p,t)) = A p from full_constant F W hf zf₁ p hp t ht,
      show B (F.val (p,t)) = B p from invB p hp t ht]
  have id (p : State) (hp : p ∈ K) : full F W v p = A p := by
    have le := isMinOn_iff.mp hmin p hp
    have zρ : ρ (B p) = 0 := ρ.zero_of_le_dist (by simpa [ρ,δ,abs_of_nonneg (nonnegB p)] using le)
    have e := extract_constant F W sb.continuous sc.continuous zb inv ((mem_closedBall_zero_iff.mp hp.1).trans hr₁.le)
    change full F W v p = B p * (A p / (B p + ρ (B p))) at e
    rw [e,zρ,add_zero]
    field_simp [(positiveB p (mem_closedBall_zero_iff.mp hp.1)).ne']
  have replace : integral F (fun p => f p * A p) = integral F (fun p => f p * full F W v p) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    let p := PolarCollar.direction (ScalarLiouville.point x)
    change _ * (f p * A p) = _ * (f p * full F W v p)
    by_cases hp : ‖p.1‖ ≤ r
    · have mem : p ∈ K := ⟨mem_closedBall_zero_iff.mpr hp,⟨hx.1 2,hx.2 2⟩⟩
      rw [id p mem]
    · rw [zf p (lt_of_not_ge hp),zero_mul,zero_mul]
  have symm := symmetric F W hf pf zf₁ sv pv zv
  have squ (p : State) : full F W f p * v p = w p * (full F W f p)^2 := by
    dsimp only [v,w,h,A]; ring
  exact replace.trans (symm.trans (congrArg (integral F) (funext squ)))

end TransportOkaGrauert.ScalarRayPairing
