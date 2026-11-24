import TransportOkaGrauert.PhysicalLinearLevi
import TransportOkaGrauert.PhysicalSchurEstimate
import TransportOkaGrauert.PhysicalSteinPatch
import TransportOkaGrauert.ChartSteinAtlas

/-! # An everywhere strictly plurisubharmonic exhaustion

On each compact set the real base and velocity coordinates, together with their
complex rotations, give two uniform directional estimates. Two exponentials
supply respectively the vertical complex Hessian and the square of a gradient
transverse to the other complex directions. A regularized maximum patches the
bounded compact potential to the proper exterior exhaustion.
-/

noncomputable section
namespace TransportOkaGrauert.PhysicalStein

open ChartStein CollarGluing FrameLevi PhysicalSteinDirections PhysicalLinearLevi Set Metric
open scoped ContDiff Topology

private theorem shift_levi (j : E → E →L[ℝ] E) (u : E → ℝ) (k : ℝ) (p v : E) :
    ddC j (fun q => u q-k) p v (j p v) = ddC j u p v (j p v) := by
  have eq : dc j (fun q => u q-k) = dc j u := by funext q; simp only [dc,fderiv_sub_const]
  simp only [ddC,eq]

theorem compact_strict_potential {σ : ℂ → ℝ} (hs : ContDiff ℝ ∞ σ) (K : Set E)
    (hk : IsCompact K) (inside : K ⊆ domain) :
    ∃ g : E → ℝ, (∀ p ∈ domain, ContDiffAt ℝ ∞ g p ∧ 0 ≤ g p ∧ g p ≤ 1) ∧
      ∀ p ∈ K, StrictAt (J σ) g p := by
  obtain ⟨M,mp,bound⟩ := coordinate_bounds hs hk inside
  let B := 12*M+1
  have bbig : 12*M < B := by dsimp [B]; linarith
  have bp : 0 < B := (by positivity : 0 < 12*M).trans bbig
  let m := B*Real.exp (-B)
  have mpos : 0 < m := mul_pos bp (Real.exp_pos _)
  let A := max 1 (B * Real.exp B)
  have aone : 1 ≤ A := le_max_left ..
  have ap := zero_lt_one.trans_le aone
  let N := 4*M*A*(2+m⁻¹)+1
  have nbig : 4*M*A*(2+m⁻¹) < N := by dsimp [N]; linarith
  have np : 0 < N := (by positivity : 0 < 4*M*A*(2+m⁻¹)).trans nbig
  let u := PhysicalLeviCalculus.potential A B x y
  let k := A+Real.exp B
  let w := fun q => u q-k
  let g := PhysicalLeviCalculus.potential 0 N x w
  have wu (p : E) : ContDiffAt ℝ ∞ u p := PhysicalLeviCalculus.potential_smooth _ _ x.contDiff.contDiffAt y.contDiff.contDiffAt
  have ww (p : E) : ContDiffAt ℝ ∞ w p := (wu p).sub (contDiffAt_const (c := k))
  have yb (p : E) (hp : p ∈ domain) : |y p| ≤ 1 := (Complex.abs_re_le_norm _).trans hp.2.le
  refine ⟨g,?_,?_⟩
  · intro p hp
    have xb : x p ≤ 1 := (Complex.re_le_norm _).trans hp.1.le
    have yu := (abs_le.mp (yb p hp)).2
    have ub : u p ≤ k := add_le_add (by simpa using mul_le_mul_of_nonneg_left xb ap.le)
      (Real.exp_le_exp.mpr (by simpa using mul_le_mul_of_nonneg_left yu bp.le))
    refine ⟨PhysicalLeviCalculus.potential_smooth _ _ x.contDiff.contDiffAt (ww p),?_,?_⟩
    · simp only [g,PhysicalLeviCalculus.potential,zero_mul,zero_add]; exact (Real.exp_pos _).le
    · simp only [g,PhysicalLeviCalculus.potential,zero_mul,zero_add]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos np.le (sub_nonpos.mpr ub))
  intro p hp v vn
  let j := J σ p
  let X := pair j x v
  let Y := pair j y v
  let c := B*Real.exp (B*y p)
  let S := A • X + c • Y
  have cp : 0 < c := mul_pos bp (Real.exp_pos _)
  obtain ⟨lowerY,upperY⟩ := abs_le.mp (yb p (inside hp))
  have cm : m ≤ c := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left lowerY bp.le])) bp.le
  have ca : c ≤ A := (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (by simpa using mul_le_mul_of_nonneg_left upperY bp.le)) bp.le).trans (le_max_right ..)
  have tri : A*‖X‖ ≤ ‖S‖+c*‖Y‖ := by
    calc A*‖X‖ = ‖S-c • Y‖ := by simp [S,norm_smul,Real.norm_of_nonneg ap.le]
      _ ≤ _ := by simpa [norm_smul,Real.norm_of_nonneg cp.le] using norm_sub_le S (c • Y)
  have grad (t : E) : fderiv ℝ w p t = A*x t+c*y t := by
    simp only [w,fderiv_sub_const,u,PhysicalLeviCalculus.gradient A B x.differentiableAt y.differentiableAt,
      x.fderiv,y.fderiv,c]
  have pairS : (fderiv ℝ w p v,fderiv ℝ w p (j v)) = S := by
    apply Prod.ext <;> exact grad _
  have ss := PhysicalSchurEstimate.norm_pair_sq (fderiv ℝ w p v) (fderiv ℝ w p (j v))
  rw [pairS] at ss
  have sy := PhysicalSchurEstimate.norm_pair_sq (y v) (y (j v))
  change ‖Y‖^2 ≤ _ at sy
  obtain ⟨nz,lx,ly⟩ := bound p hp v
  let qx := ddC (J σ) x p v (j v)
  let qy := ddC (J σ) y p v (j v)
  have pos : 0 < A*qx+c*qy+B*c*‖Y‖^2+N*‖S‖^2 :=
    PhysicalSchurEstimate.positive mp aone bbig nbig mpos cm ca (norm_nonneg _) (norm_nonneg _)
      (nz vn) tri (abs_le.mp lx).1 (abs_le.mp ly).1
  have p' : 0 < A*qx+c*qy+B*c*((y v)^2+(y (j v))^2)+N*((fderiv ℝ w p v)^2+(fderiv ℝ w p (j v))^2) :=
    pos.trans_le (add_le_add (add_le_add_right (mul_le_mul_of_nonneg_left sy (mul_nonneg bp.le cp.le)) _) (mul_le_mul_of_nonneg_left ss np.le))
  have dj := (J_smooth hs (inside hp).2).differentiableAt (by simp)
  have jj := J_sq σ (inside hp).2 v
  have lu := PhysicalLeviCalculus.levi_potential A B dj x.contDiff.contDiffAt y.contDiff.contDiffAt v jj
  have lg := PhysicalLeviCalculus.levi_potential 0 N dj x.contDiff.contDiffAt ((ww p).of_le (by decide)) v jj
  change 0 < ddC (J σ) (PhysicalLeviCalculus.potential 0 N x w) p v (J σ p v)
  rw [lg,show ddC (J σ) w p v (J σ p v) = ddC (J σ) u p v (J σ p v) from shift_levi _ u k p v,lu]
  simp only [zero_mul,zero_add,y.fderiv]
  convert mul_pos (mul_pos np (Real.exp_pos (N*w p))) p' using 1
  dsimp [j,qx,qy,c]
  ring

/-- A smooth, proper, everywhere strictly plurisubharmonic exhaustion in the
actual physical complex structure for every simple conformal disk. -/
theorem simple_strict_exhaustion {σ : ℂ → ℝ} (simple : SimpleDiskTarget.SimpleMetric σ) :
    ∃ f : E → ℝ, (∀ p ∈ domain, ContDiffAt ℝ ∞ f p ∧ StrictAt (J σ) f p) ∧
      ∀ m : ℝ, IsCompact {p ∈ domain | f p ≤ m} :=
  PhysicalSteinPatch.global_of_compact simple (compact_strict_potential simple.smooth)

/-- The physical exhaustion domain is exactly the full open domain used by the
Stein criterion and its coordinate atlas. -/
theorem full_disk_domain : CollarGluing.domain = ChartSteinAtlas.domain (ball (0:ℂ) 1) := by
  ext p
  simp [CollarGluing.domain,ChartSteinAtlas.domain]

/-- The holomorphic tests on the full disk are precisely the smooth functions
whose differential intertwines the physical complex structure and multiplication
by the imaginary unit. -/
theorem full_disk_holOn_iff (σ : ℂ → ℝ) (f : E → ℂ) :
    HolOn σ (ball 0 1) f ↔ ∀ p ∈ ChartSteinAtlas.domain (ball (0:ℂ) 1),
      ContDiffAt ℝ ∞ f p ∧ ∀ v, fderiv ℝ f p (J σ p v) = Complex.I * fderiv ℝ f p v := by
  constructor
  · intro h p hp
    have hf := h (ChartSteinAtlas.interiorHomeomorph (U := ball (0:ℂ) 1) subset_rfl ⟨p,hp⟩)
    change HolAt σ f p at hf
    exact ⟨hf.1,(satisfiesCR_iff σ (mem_ball_zero_iff.mp hp.2) _).mp hf.2⟩
  · intro h p
    have m : point p.val ∈ ChartSteinAtlas.domain (ball (0:ℂ) 1) :=
      ⟨p.property.1,mem_ball_zero_iff.mpr p.property.2⟩
    obtain ⟨sm,d⟩ := h _ m
    exact ⟨sm,(satisfiesCR_iff σ p.property.2 _).mpr d⟩

/-- The strict full-disk Levi exhaustion in the domain and differential forms
of the Stein criterion. The complex Hessian is the actual exterior derivative
of the one-form `-df ∘ J`. -/
theorem full_disk_levi_exhaustion {σ : ℂ → ℝ} (simple : SimpleDiskTarget.SimpleMetric σ) :
    ∃ f : E → ℝ, (∀ p ∈ ChartSteinAtlas.domain (ball (0:ℂ) 1), ContDiffAt ℝ ∞ f p ∧
      ∀ v : E, v ≠ 0 → 0 < ddC (J σ) f p v (J σ p v)) ∧
      ∀ m : ℝ, IsCompact {p ∈ ChartSteinAtlas.domain (ball (0:ℂ) 1) | f p ≤ m} := by
  rw [← full_disk_domain]
  exact simple_strict_exhaustion simple

end TransportOkaGrauert.PhysicalStein
