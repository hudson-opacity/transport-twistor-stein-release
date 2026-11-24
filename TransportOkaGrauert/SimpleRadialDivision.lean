import TransportOkaGrauert.PencilGeometry
import TransportOkaGrauert.SmoothRadialHessian
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! # Smooth coefficient recovery in normal coordinates

A symmetric correction annihilating the radial vector and a connection
covector annihilating that vector have smooth scalar coefficients through
the origin. The identities need only hold on the normal-coordinate domain.
-/

noncomputable section
namespace TransportOkaGrauert.SimpleRadialDivision
open Set Filter Metric Complex SteinDivisor
open scoped ContDiff Topology Manifold

/-- A cutoff is identically one near a closed subset of an open chart and
identically zero near every point outside that chart. -/
theorem cutoff {U K : Set ℂ} (op : IsOpen U) (closed : IsClosed K) (inside : K ⊆ U) :
    ∃ χ : ℂ → ℝ, ContDiff ℝ ∞ χ ∧
      (∀ x ∈ K, χ =ᶠ[𝓝 x] fun _ => 1) ∧ (∀ x ∉ U, χ =ᶠ[𝓝 x] fun _ => 0) := by
  obtain ⟨χ,zero,one,_⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed (𝓘(ℝ,ℂ)) (n := ⊤)
    op.isClosed_compl closed (Set.disjoint_left.mpr (fun _ hU hK => hU (inside hK)))
  exact ⟨χ, contMDiff_iff_contDiff.mp χ.contMDiff,
    mem_nhdsSet_iff_forall.mp one, mem_nhdsSet_iff_forall.mp zero⟩

/-- Extend an open-chart function smoothly across ambient coordinates
without changing its germ anywhere on the given closed subset. -/
theorem extend {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {U K : Set ℂ}
    (op : IsOpen U) (closed : IsClosed K) (inside : K ⊆ U) {f : ℂ → E}
    (hf : ContDiffOn ℝ ∞ f U) :
    ∃ g : ℂ → E, ContDiff ℝ ∞ g ∧ ∀ x ∈ K, g =ᶠ[𝓝 x] f := by
  obtain ⟨χ,sc,one,zero⟩ := cutoff op closed inside
  refine ⟨fun x => χ x • f x, contDiff_iff_contDiffAt.mpr (fun x => ?_),fun x hx => ?_⟩
  · by_cases hx : x ∈ U
    · exact sc.contDiffAt.smul (hf.contDiffAt (op.mem_nhds hx))
    · apply (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq
      filter_upwards [zero x hx] with y hy
      simp [hy]
  · filter_upwards [one x hx] with y hy
    simp [hy]

private def complexOf (q : (ℝ × ℝ) × ℝ) : ℂ := (q.1.2 : ℂ) + (q.2 : ℂ)*I

private theorem complexOf_smooth : ContDiff ℝ ∞ complexOf :=
  (ofRealCLM.contDiff.comp (contDiff_snd.comp contDiff_fst)).add
    ((ofRealCLM.contDiff.comp contDiff_snd).mul contDiff_const)

private def coords (x : ℂ) : (ℝ × ℝ) × ℝ := ((0,x.re),x.im)

private theorem coords_smooth : ContDiff ℝ ∞ coords :=
  (contDiff_const.prodMk reCLM.contDiff).prodMk imCLM.contDiff

private theorem reconstruct (u : ℂ) : u.re • (1:ℂ) + u.im • I = u := by
  simp [Complex.real_smul]

/-- Coefficients of a real covector and a real symmetric endomorphism in
the moving frame, localized to any closed part of the normal chart. -/
theorem coefficients {U K : Set ℂ} (op : IsOpen U) (closed : IsClosed K) (inside : K ⊆ U)
    (A : ℂ → ℂ →L[ℝ] ℂ) (B : ℂ → ℂ →L[ℝ] ℝ)
    (sA : ContDiffOn ℝ ∞ A U) (sB : ContDiffOn ℝ ∞ B U)
    (radA : ∀ x ∈ U, A x x = 0) (radB : ∀ x ∈ U, B x x = 0)
    (sym : ∀ x ∈ U, (A x I).re = (A x 1).im) :
    ∃ c k : ℂ → ℝ, ContDiff ℝ ∞ c ∧ ContDiff ℝ ∞ k ∧
      ∀ x ∈ K, ∀ u : ℂ,
        A x u = (c x * longitudinal (I*x) u) • (I*x) ∧
        B x u = k x * longitudinal (I*x) u := by
  obtain ⟨χ,sc,one,zero⟩ := cutoff op closed inside
  let M (x : ℂ) := χ x • A x
  let N (x : ℂ) := χ x • B x
  have scaled {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ℂ → E}
      (h : ContDiffOn ℝ ∞ F U) : ContDiff ℝ ∞ (fun x => χ x • F x) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact sc.contDiffAt.smul (h.contDiffAt (op.mem_nhds hx))
    · apply (contDiffAt_const (c := (0:E))).congr_of_eventuallyEq
      filter_upwards [zero x hx] with y hy
      simp [hy]
  have sm : ContDiff ℝ ∞ M := scaled sA
  have sn : ContDiff ℝ ∞ N := scaled sB
  have ids (x : ℂ) : M x x = 0 ∧ N x x = 0 ∧ (M x I).re = (M x 1).im := by
    by_cases hx : x ∈ U
    · simp [M,N,radA x hx,radB x hx, Complex.real_smul, sym x hx, -Complex.ofReal_mul]
    · simp [M,N,(zero x hx).self_of_nhds]
  let l := fun q => (M (complexOf q) 1).re
  let m := fun q => (M (complexOf q) 1).im
  let n := fun q => (M (complexOf q) I).im
  let b := fun q => N (complexOf q) 1
  let d := fun q => N (complexOf q) I
  have rows (p a b : ℝ) :
      l ((p,a),b) * a + m ((p,a),b) * b = 0 ∧
      m ((p,a),b) * a + n ((p,a),b) * b = 0 := by
    let x := complexOf ((p,a),b)
    have w := (ids x).1
    have v : x = a • (1:ℂ) + b • I := by simp [x,complexOf,Complex.real_smul]
    conv_lhs at w => arg 2; rw [v]
    rw [map_add,map_smul,map_smul] at w
    have r := congrArg Complex.re w
    have i := congrArg Complex.im w
    simpa only [l,m,n, Complex.add_re,Complex.add_im, Complex.real_smul,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, add_zero, Complex.zero_re, Complex.zero_im, (ids x).2.2, mul_comm] using And.intro r i
  have Nrow (p a b' : ℝ) : b ((p,a),b') * a + d ((p,a),b') * b' = 0 := by
    let x := complexOf ((p,a),b')
    have w := (ids x).2.1
    have v : x = a • (1:ℂ) + b' • I := by simp [x,complexOf,Complex.real_smul]
    conv_lhs at w => arg 2; rw [v]
    simpa only [b,d,map_add,map_smul,smul_eq_mul,mul_comm] using w
  obtain ⟨C,sC,AC⟩ := SmoothRadialHessian.radialKernelFactor
    (reCLM.contDiff.comp ((sm.comp complexOf_smooth).clm_apply (contDiff_const (c := (1:ℂ)))))
    (imCLM.contDiff.comp ((sm.comp complexOf_smooth).clm_apply (contDiff_const (c := (1:ℂ)))))
    (imCLM.contDiff.comp ((sm.comp complexOf_smooth).clm_apply (contDiff_const (c := I))))
    (fun p a b => (rows p a b).1) (fun p a b => (rows p a b).2)
  obtain ⟨D,sD,BD⟩ := SmoothRadialHessian.radialCovectorFactor
    ((sn.comp complexOf_smooth).clm_apply (contDiff_const (c := (1:ℂ))))
    ((sn.comp complexOf_smooth).clm_apply (contDiff_const (c := I))) Nrow
  refine ⟨C ∘ coords,fun x => -D (coords x),sC.comp coords_smooth,(sD.comp coords_smooth).neg,?_⟩
  intro x hx u
  obtain ⟨a1,a2,a3⟩ := AC 0 x.re x.im
  obtain ⟨b1,b2⟩ := BD 0 x.re x.im
  have cox : complexOf ((0,x.re),x.im) = x := by simp [complexOf]
  simp only [cox, Function.comp_apply, Complex.reCLM_apply,Complex.imCLM_apply] at a1 a2 a3
  simp only [cox, Function.comp_apply] at b1 b2
  have unit := (one x hx).self_of_nhds
  change χ x = 1 at unit
  have smx : M x = A x := by simp [M,unit]
  have snx : N x = B x := by simp [N,unit]
  rw [smx] at a1 a2 a3
  rw [snx] at b1 b2
  have sa := sym x (inside hx)
  constructor
  · conv_lhs => arg 2; rw [← reconstruct u]
    rw [map_add,map_smul,map_smul]
    apply Complex.ext <;>
      simp [longitudinal, Complex.mul_re, Complex.mul_im, Complex.real_smul,
        a1,a2,a3,sa, coords, -Complex.ofReal_mul] <;> ring
  · conv_lhs => arg 2; rw [← reconstruct u]
    rw [map_add,map_smul,map_smul,b1,b2]
    simp [longitudinal, Complex.mul_re,Complex.mul_im, coords,smul_eq_mul]
    ring

end TransportOkaGrauert.SimpleRadialDivision
