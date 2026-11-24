import TransportOkaGrauert.BirkhoffCell
import TransportOkaGrauert.JumpIncoming
import TransportOkaGrauert.JumpHomotopy
import TransportOkaGrauert.FlatSimple

/-! A negative answer on the simple Euclidean disk to the boundary
sufficiency question after Theorem 5.13 of Bohr–Paternain (JÉP, 2023).
The exterior factor is normalized at infinity. Both it and the interior
factor, with inverses, are smooth in the angular variable. -/
noncomputable section
namespace TransportOkaGrauert.BoundaryJump
open BirkhoffCell JumpingLines Metric SimpleDiskTarget
open scoped ContDiff

def FactorSmooth (F : BirkhoffCell.Factor) : Prop :=
  ∀ i j, ContDiff ℝ ∞ (fun θ : ℝ => F.val (Circle.exp θ) i j) ∧
    ContDiff ℝ ∞ (fun θ : ℝ => F.inv (Circle.exp θ) i j)

def SmoothBigCell (L : BirkhoffCell.Loop) : Prop :=
  ∃ G F : BirkhoffCell.Factor, FactorSmooth G ∧ FactorSmooth F ∧
    G.val 0 = 1 ∧ ∀ v : Circle, L v = G.val (v : ℂ)⁻¹ * F.val v

theorem SmoothBigCell.bigCell {L : BirkhoffCell.Loop} (h : SmoothBigCell L) : BigCell L := by
  obtain ⟨G,F,_,_,hn,he⟩ := h
  exact ⟨G,F,hn,he⟩

private theorem smooth_of_entire {a : ℂ → ℂ} (h : Differentiable ℂ a) :
    ContDiff ℝ ∞ (fun t : ℝ => a (Circle.exp t)) := by
  have hv : ContDiff ℝ ∞ (fun t : ℝ => (Circle.exp t : ℂ)) := by
    simp only [Circle.coe_exp]
    exact (Complex.ofRealCLM.contDiff.mul contDiff_const).cexp
  exact (h.contDiff (n := ∞)).restrict_scalars ℝ |>.comp hv

/-- The two factors and their inverses are entire in their own coordinates
and hence smooth on the circle. -/
theorem smooth_at_regular_fiber {z : ℂ} (hz : z ≠ 0) :
    SmoothBigCell (fun v => W z v) := by
  let G := Factor.ofEntire (exterior z) (exteriorInv z) (exterior_entire z) (exterior_inverses z)
  let F := Factor.ofEntire (interior z) (interiorInv z) (interior_entire z) (interior_inverses hz)
  refine ⟨G,F,?_,?_,exterior_normalized z, fun v => factorization hz v.coe_ne_zero⟩
  · exact fun i j => ⟨smooth_of_entire (exterior_entire z i j).1,
      smooth_of_entire (exterior_entire z i j).2⟩
  · exact fun i j => ⟨smooth_of_entire (interior_entire z i j).1,
      smooth_of_entire (interior_entire z i j).2⟩

/-- Even the larger canonical cell, allowing merely continuous traces, misses
the center. -/
theorem center_not_big : ¬ BigCell (fun v => W 0 v) := by
  simpa [W, FlatScalar.firstIntegral, standard] using diagonal_not_big

theorem jump_exactly_at_origin (z : ℂ) :
    SmoothBigCell (fun v => W z v) ↔ z ≠ 0 := by
  refine ⟨?_, smooth_at_regular_fiber⟩
  rintro h rfl
  exact center_not_big h.bigCell

/-- The witness satisfies transport, rank, smoothness, and the boundary
test on a geometrically simple metric. At its center even a continuous
canonical factorization is impossible. -/
theorem boundary_indices_insufficient :
    SimpleMetric (fun _ : ℂ => (0 : ℝ)) ∧
    SmoothToBoundary (fun z v => W z v) ∧
    (∀ z (v : Circle), (W z v).det = 1) ∧
    (∀ z (v : Circle) (t : ℝ), W (z + t * v) v = W z v) ∧
    (∀ z ∈ sphere (0 : ℂ) 1, SmoothBigCell (fun v => W z v)) ∧
    ¬ BigCell (fun v => W 0 v) := by
  refine ⟨FlatSimple.euclidean_simple, fun _ _ _ i j => (W_smooth i j).contDiffAt,
    fun z v => W_det z v.coe_ne_zero, W_advance, ?_, center_not_big⟩
  intro z hz
  apply smooth_at_regular_fiber
  rintro rfl
  simp at hz

/-- Test the actual incoming datum by reconstructing it along each chord,
including the limiting tangent chords over the boundary. -/
def liftedIncoming (z : ℂ) (hz : ‖z‖ ≤ 1) : Loop :=
  fun v => JumpIncoming.traceW (JumpIncoming.incomingState z hz v)

theorem incoming_cell_iff (z : ℂ) (hz : ‖z‖ ≤ 1) :
    SmoothBigCell (liftedIncoming z hz) ↔ z ≠ 0 := by
  have he : liftedIncoming z hz = fun v : Circle => W z v := funext (JumpIncoming.reconstruct z hz)
  rw [he, jump_exactly_at_origin]

/-- The smooth scattering-compatible trace satisfies the paper's boundary
test and full-boundary homotopy condition, yet its invariant lift fails the
canonical Birkhoff test at an interior point. -/
theorem incoming_boundary_counterexample :
    Nonempty (boundaryWMap.Homotopy (ContinuousMap.const _ 1)) ∧
    (∀ x : Circle, SmoothBigCell (liftedIncoming x (Circle.norm_coe x).le)) ∧
    ¬ BigCell (liftedIncoming 0 (by simp)) := by
  refine ⟨⟨boundaryWNullHomotopy⟩, fun x => (incoming_cell_iff _ _).mpr x.coe_ne_zero, ?_⟩
  have he : liftedIncoming 0 (by simp) = fun v : Circle => W 0 v :=
    funext (JumpIncoming.reconstruct 0 (by simp))
  rw [he]
  exact center_not_big

end TransportOkaGrauert.BoundaryJump
