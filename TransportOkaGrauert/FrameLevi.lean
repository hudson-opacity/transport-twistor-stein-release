import TransportOkaGrauert.LeviBoundary
import Mathlib.Analysis.Calculus.DifferentialForm.VectorField
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The exterior derivative in the transport frame

This is a chart-local calculation. All vector fields are actual vector-valued functions,
their brackets are Fréchet Lie brackets, and the two-form is mathlib's exterior derivative
of the one-form `-df ∘ J`. The geometric inputs are the moving-frame structure equations.
-/

noncomputable section

namespace TransportOkaGrauert.FrameLevi

open Filter VectorField
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Directional differentiation along a vector field. -/
def along (P : E → E) (f : E → ℝ) (p : E) : ℝ := fderiv ℝ f p (P p)

/-- The real one-form used in the Levi form. -/
def dc (J : E → E →L[ℝ] E) (f : E → ℝ) (p : E) : E [⋀^Fin 1]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.ofSubsingleton ℝ E ℝ (0 : Fin 1) (-((fderiv ℝ f p).comp (J p)))

/-- Evaluation of the Levi two-form on two real vectors. -/
def ddC (J : E → E →L[ℝ] E) (f : E → ℝ) (p : E) (v w : E) : ℝ :=
  extDeriv (dc J f) p ![v, w]

private theorem cartan {form : E → E [⋀^Fin 1]→L[ℝ] ℝ} {P Q : E → E} {p : E}
    (hform : DifferentiableAt ℝ form p) (hP : DifferentiableAt ℝ P p) (hQ : DifferentiableAt ℝ Q p) :
    extDeriv form p ![P p, Q p] =
      along P (fun y => form y ![Q y]) p - along Q (fun y => form y ![P y]) p -
        form p ![lieBracket ℝ P Q p] := by
  have h := extDeriv_apply_vectorField (n := 0) (V := ![P,Q]) hform
    (by intro i; fin_cases i <;> assumption)
  have eval (y : E) : (fun i => (![P,Q] i) y) = ![P y,Q y] := by
    funext i; fin_cases i <;> rfl
  have rem0 (y : E) : (0 : Fin 2).removeNth ![P y,Q y] = ![Q y] := by
    funext i; fin_cases i; rfl
  have rem1 (y : E) : (1 : Fin 2).removeNth ![P y,Q y] = ![P y] := by
    funext i; fin_cases i; rfl
  have top : Finset.Ici (0 : Fin 1) = Finset.univ := by decide
  simp only [Nat.reduceAdd, eval, Fin.sum_univ_two, Fin.sum_univ_one, top, rem0, rem1] at h
  simpa only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_one_smul,
    Matrix.cons_val_zero, Matrix.cons_val_one, along, sub_eq_add_neg, zero_add] using h

private theorem d_dc {J : E → E →L[ℝ] E} {f : E → ℝ} {p : E}
    (hJ : DifferentiableAt ℝ J p) (hf : ContDiffAt ℝ 2 f p) :
    DifferentiableAt ℝ (dc J f) p := by
  have hd := (hf.fderiv_right (m := 1) (by decide)).differentiableAt one_ne_zero
  exact (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).differentiableAt.comp p
    (hd.clm_comp hJ).neg

/-- In radius coordinate `t = (1-r²)/(1+r²)`, this is `-log(1-r²)`. -/
def radial (a : ℝ) : ℝ := Real.log (1 + a) - Real.log a - Real.log 2

private theorem radial_deriv {a : ℝ} (ha : 0 < a) :
    HasDerivAt radial ((1+a)⁻¹ - a⁻¹) a := by
  have h1 := (hasDerivAt_const a (1 : ℝ)).add (hasDerivAt_id a)
  unfold radial
  simpa [div_eq_inv_mul] using
    ((h1.log (by dsimp; linarith)).sub (Real.hasDerivAt_log ha.ne')).sub_const (Real.log 2)

/-- The data of a moving frame in a real chart; the field equations are local. -/
structure Frame (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  X : E → E
  H : E → E
  R : E → E
  V : E → E
  J : E → E →L[ℝ] E
  t : E → ℝ
  K : E → ℝ

/-- The frame equations and regularity needed at an interior chart point. -/
structure EquationsAt (F : Frame E) (p : E) : Prop where
  dX : DifferentiableAt ℝ F.X p
  dH : DifferentiableAt ℝ F.H p
  dV : DifferentiableAt ℝ F.V p
  dR : DifferentiableAt ℝ F.R p
  dJ : DifferentiableAt ℝ F.J p
  dt : ContDiffAt ℝ 2 F.t p
  positive : 0 < F.t p
  JX : ∀ᶠ y in 𝓝 p, F.J y (F.X y) = F.t y • F.H y
  JH : ∀ᶠ y in 𝓝 p, F.J y (F.H y) = -(F.t y)⁻¹ • F.X y
  JR : ∀ᶠ y in 𝓝 p, F.J y (F.R y) = F.V y
  JV : ∀ᶠ y in 𝓝 p, F.J y (F.V y) = -F.R y
  Xt : ∀ᶠ y in 𝓝 p, along F.X F.t y = 0
  Ht : ∀ᶠ y in 𝓝 p, along F.H F.t y = 0
  Vt : ∀ᶠ y in 𝓝 p, along F.V F.t y = 0
  Rt : ∀ᶠ y in 𝓝 p, along F.R F.t y = (F.t y)^2 - 1
  XH : lieBracket ℝ F.X F.H p = F.K p • F.V p
  VX : lieBracket ℝ F.V F.X p = F.H p
  HV : lieBracket ℝ F.H F.V p = F.X p
  XR : lieBracket ℝ F.X F.R p = 0
  RH : lieBracket ℝ F.R F.H p = 0
  RV : lieBracket ℝ F.R F.V p = 0

/-- Derivatives of the angular correction entered into the boundary Schur complement. -/
def jet (F : Frame E) (h : E → ℝ) (p : E) : LeviBoundary.FrameJet where
  curvature := F.K p
  x := along F.X h p
  h := along F.H h p
  xx := along F.X (along F.X h) p
  hh := along F.H (along F.H h) p
  vv := along F.V (along F.V h) p
  hv := along F.H (along F.V h) p
  xv := along F.X (along F.V h) p

/-- The local potential extended off the unit directions. -/
def potential (F : Frame E) (h : E → ℝ) (p : E) : ℝ := radial (F.t p) + h p

private def eta (F : Frame E) (h : E → ℝ) (p : E) : E →L[ℝ] ℝ :=
  -((fderiv ℝ (potential F h) p).comp (F.J p))

private theorem along_congr (P : E → E) {f g : E → ℝ} {p : E}
    (h : f =ᶠ[𝓝 p] g) : along P f p = along P g p := by
  simp [along, h.fderiv_eq]

private theorem along_potential (F : Frame E) {h : E → ℝ} {p : E}
    (dt : DifferentiableAt ℝ F.t p) (dh : DifferentiableAt ℝ h p) (hp : 0 < F.t p)
    (P : E → E) : along P (potential F h) p =
      ((1+F.t p)⁻¹ - (F.t p)⁻¹) * along P F.t p + along P h p := by
  have hd := ((radial_deriv hp).comp_hasFDerivAt p dt.hasFDerivAt).add dh.hasFDerivAt
  exact congrArg (fun L : E →L[ℝ] ℝ => L (P p)) hd.fderiv

private theorem coframe {F : Frame E} {p : E} (q : EquationsAt F p)
    {h : E → ℝ} (dh : ContDiffAt ℝ 2 h p) (rh : ∀ᶠ y in 𝓝 p, along F.R h y = 0) :
    ∀ᶠ y in 𝓝 p,
      eta F h y (F.X y) = - (F.t y * along F.H h y) ∧
      eta F h y (F.H y) = (F.t y)⁻¹ * along F.X h y ∧
      eta F h y (F.R y) = -along F.V h y ∧
      eta F h y (F.V y) = (F.t y)⁻¹ - 1 := by
  filter_upwards [q.JX, q.JH, q.JR, q.JV, q.Xt, q.Ht, q.Vt, q.Rt, rh,
    q.dt.eventually (by decide), dh.eventually (by decide),
    q.dt.continuousAt (Ioi_mem_nhds q.positive)] with y jx jh jr jv xt ht vt rt hr dt dy hp
  change 0 < F.t y at hp
  have d := along_potential F (h := h) (dt.differentiableAt (by decide))
    (dy.differentiableAt (by decide)) hp
  simp only [eta, ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply,
    jx, jh, jr, jv, map_smul, map_neg, smul_eq_mul, neg_neg]
  change -(F.t y * along F.H (potential F h) y) = _ ∧
    -(-(F.t y)⁻¹ * along F.X (potential F h) y) = _ ∧
    -along F.V (potential F h) y = _ ∧ along F.R (potential F h) y = _
  rw [d F.H, d F.X, d F.V, d F.R, xt, ht, vt, rt, hr]
  simp only [mul_zero, zero_add, neg_mul, neg_neg, add_zero, true_and]
  field_simp [hp.ne', show 1 + F.t y ≠ 0 by linarith]
  ring

private theorem along_mul (P : E → E) {f g : E → ℝ} {p : E}
    (df : DifferentiableAt ℝ f p) (dg : DifferentiableAt ℝ g p) :
    along P (fun y => f y * g y) p = f p * along P g p + g p * along P f p := by
  simp [along, fderiv_fun_mul df dg]

private theorem along_neg (P : E → E) (f : E → ℝ) (p : E) :
    along P (fun y => -f y) p = -along P f p := by
  simp [along, fderiv_fun_neg]

private theorem along_inv (P : E → E) {t : E → ℝ} {p : E}
    (dt : DifferentiableAt ℝ t p) (ht : t p ≠ 0) :
    along P (fun y => (t y)⁻¹) p = -((t p)^2)⁻¹ * along P t p :=
  congrArg (fun L : E →L[ℝ] ℝ => L (P p)) ((hasDerivAt_inv ht).comp_hasFDerivAt p dt.hasFDerivAt).fderiv

private theorem along_sub_one (P : E → E) (f : E → ℝ) (p : E) :
    along P (fun y => f y - 1) p = along P f p := by simp [along, fderiv_sub_const]

private theorem ddC_smul_right (J : E → E →L[ℝ] E) (f : E → ℝ) (p : E) (v w : E) (a : ℝ) :
    ddC J f p v (a • w) = a * ddC J f p v w := by
  have upd (c : E) : Function.update ![v,w] (1 : Fin 2) c = ![v,c] := by
    funext i; fin_cases i <;> simp
  simpa only [ddC, upd, smul_eq_mul] using
    (extDeriv (dc J f) p).map_update_smul ![v,w] (1 : Fin 2) a w

private theorem ddC_smul_left (J : E → E →L[ℝ] E) (f : E → ℝ) (p : E) (v w : E) (a : ℝ) :
    ddC J f p (a • v) w = a * ddC J f p v w :=
  (extDeriv (dc J f) p).vecCons_smul ![w] a v

/-- The six pairwise entries of the actual exterior derivative in a transport chart.
Radial independence of the angular weight and the moving-frame structure equations are
the inputs. In particular, no entry of the exterior derivative is a hypothesis. -/
theorem levi_frame {F : Frame E} {p : E} (q : EquationsAt F p) {h : E → ℝ}
    (dh : ContDiffAt ℝ 2 h p) (rh : ∀ᶠ y in 𝓝 p, along F.R h y = 0) :
    ddC F.J (potential F h) p (F.X p) (F.J p (F.X p)) = LeviBoundary.horizontal (F.t p) (jet F h p) ∧
    ddC F.J (potential F h) p (F.R p) (F.J p (F.R p)) = LeviBoundary.vertical (F.t p) (jet F h p) ∧
    ddC F.J (potential F h) p (F.X p) (F.J p (F.R p)) = LeviBoundary.mixedJ (F.t p) (jet F h p) ∧
    ddC F.J (potential F h) p (F.X p) (F.R p) = LeviBoundary.mixedR (F.t p) (jet F h p) ∧
    ddC F.J (potential F h) p (F.J p (F.X p)) (F.R p) = -LeviBoundary.mixedJ (F.t p) (jet F h p) ∧
    ddC F.J (potential F h) p (F.J p (F.X p)) (F.J p (F.R p)) = LeviBoundary.mixedR (F.t p) (jet F h p) := by
  have hp := q.positive
  have dt := q.dt.differentiableAt (by decide)
  have df : ContDiffAt ℝ 2 (potential F h) p :=
    ((((contDiffAt_const (c := (1 : ℝ))).add q.dt).log (by dsimp; linarith)).sub
      (q.dt.log hp.ne') |>.sub contDiffAt_const).add dh
  have de := d_dc q.dJ df
  have ca (P Q : E → E) (dP : DifferentiableAt ℝ P p) (dQ : DifferentiableAt ℝ Q p) :
      ddC F.J (potential F h) p (P p) (Q p) = along P (fun y => eta F h y (Q y)) p -
        along Q (fun y => eta F h y (P y)) p - eta F h p (lieBracket ℝ P Q p) :=
    cartan de dP dQ
  have cf := coframe q dh rh
  have ex := cf.mono fun _ qy => qy.1
  have eh := cf.mono fun _ qy => qy.2.1
  have er := cf.mono fun _ qy => qy.2.2.1
  have ev := cf.mono fun _ qy => qy.2.2.2
  have ddir (P : E → E) (dP : DifferentiableAt ℝ P p) : DifferentiableAt ℝ (along P h) p :=
    ((dh.fderiv_right (m := 1) (by decide)).differentiableAt one_ne_zero).clm_apply dP
  have dinv : DifferentiableAt ℝ (fun y => (F.t y)⁻¹) p := dt.inv hp.ne'
  have bracket (P Q : E → E) (dP : DifferentiableAt ℝ P p) (dQ : DifferentiableAt ℝ Q p) :
      fderiv ℝ h p (lieBracket ℝ P Q p) =
      along P (along Q h) p - along Q (along P h) p :=
    fderiv_apply_lieBracket dh (by norm_num) dQ dP
  have bVH := bracket F.H F.V q.dH q.dV
  rw [q.HV] at bVH
  change along F.X h p = _ at bVH
  have bRH := bracket F.R F.H q.dR q.dH
  rw [q.RH, map_zero, along_congr F.H rh] at bRH
  have zH : along F.H (fun _ => (0 : ℝ)) p = 0 := by simp [along]
  rw [zH, sub_zero] at bRH
  have bXV : lieBracket ℝ F.X F.V p = -F.H p := by
    rw [lieBracket_swap, q.VX]
  have bHR : lieBracket ℝ F.H F.R p = 0 := by rw [lieBracket_swap, q.RH, neg_zero]
  have bVX := bracket F.V F.X q.dV q.dX
  rw [q.VX] at bVX
  change along F.H h p = _ at bVX
  have bRX := bracket F.X F.R q.dX q.dR
  rw [q.XR, map_zero, along_congr F.X rh] at bRX
  have zX : along F.X (fun _ => (0 : ℝ)) p = 0 := by simp [along]
  rw [zX, zero_sub] at bRX
  have rx : along F.R (along F.X h) p = 0 := neg_eq_zero.mp bRX.symm
  rw [q.JX.self_of_nhds, ddC_smul_right, ddC_smul_left, ddC_smul_left, q.JR.self_of_nhds,
    ca F.X F.H q.dX q.dH, ca F.R F.V q.dR q.dV, ca F.X F.V q.dX q.dV, ca F.X F.R q.dX q.dR,
    ca F.H F.R q.dH q.dR, ca F.H F.V q.dH q.dV, bHR, q.HV, ex.self_of_nhds,
    q.XH, map_smul, smul_eq_mul, q.RV, q.XR, map_zero, bXV, map_neg,
    ev.self_of_nhds, eh.self_of_nhds]
  rw [along_congr F.X eh, along_congr F.H ex, along_congr F.R ev, along_congr F.V er,
    along_congr F.X ev, along_congr F.V ex, along_congr F.X er, along_congr F.R ex,
    along_congr F.H er, along_congr F.R eh, along_congr F.H ev, along_congr F.V eh]
  simp only [along_neg, along_sub_one,
    along_mul _ dinv (ddir F.X q.dX), along_mul _ dt (ddir F.H q.dH), along_inv _ dt hp.ne',
    q.Xt.self_of_nhds, q.Ht.self_of_nhds, q.Vt.self_of_nhds, q.Rt.self_of_nhds,
    ← bRH, rx, LeviBoundary.horizontal, LeviBoundary.vertical, LeviBoundary.mixedJ,
    LeviBoundary.mixedR, jet]
  rw [show along F.V (along F.H h) p = along F.H (along F.V h) p - along F.X h p by linarith [bVH]]
  constructor
  · field_simp [hp.ne']; ring
  constructor
  · field_simp [hp.ne']; ring
  constructor
  · ring
  constructor
  · ring
  rw [show along F.V (along F.X h) p = along F.X (along F.V h) p + along F.H h p by linarith [bVX]]
  constructor <;> field_simp [hp.ne'] <;> ring

/-- The four real entries of the actual exterior derivative in a transport chart.
Radial independence of the angular weight and the moving-frame structure equations are
the inputs. In particular, no entry of the exterior derivative is a hypothesis. -/
theorem levi_entries {F : Frame E} {p : E} (q : EquationsAt F p) {h : E → ℝ}
    (dh : ContDiffAt ℝ 2 h p) (rh : ∀ᶠ y in 𝓝 p, along F.R h y = 0) :
    ddC F.J (potential F h) p (F.X p) (F.J p (F.X p)) = LeviBoundary.horizontal (F.t p) (jet F h p) ∧
    ddC F.J (potential F h) p (F.R p) (F.J p (F.R p)) = LeviBoundary.vertical (F.t p) (jet F h p) ∧
    ddC F.J (potential F h) p (F.X p) (F.J p (F.R p)) = LeviBoundary.mixedJ (F.t p) (jet F h p) ∧
    ddC F.J (potential F h) p (F.X p) (F.R p) = LeviBoundary.mixedR (F.t p) (jet F h p) := by
  obtain ⟨a,b,c,d,_⟩ := levi_frame q dh rh
  exact ⟨a,b,c,d⟩

private theorem ddC_add_left (J : E → E →L[ℝ] E) (f : E → ℝ) (p v w u : E) :
    ddC J f p (v+w) u = ddC J f p v u + ddC J f p w u :=
  (extDeriv (dc J f) p).vecCons_add ![u] v w

private theorem ddC_swap (J : E → E →L[ℝ] E) (f : E → ℝ) (p v w : E) :
    ddC J f p w v = -ddC J f p v w := by
  have sw : ![v,w] ∘ Equiv.swap (0 : Fin 2) 1 = ![w,v] := by
    funext i; fin_cases i <;> simp
  simpa only [ddC, ← sw] using
    (extDeriv (dc J f) p).toAlternatingMap.map_swap ![v,w] (i := 0) (j := 1) (by decide)

private theorem ddC_add_right (J : E → E →L[ℝ] E) (f : E → ℝ) (p v w u : E) :
    ddC J f p u (v+w) = ddC J f p u v + ddC J f p u w := by
  rw [ddC_swap _ _ _ (v+w) u, ddC_add_left, ddC_swap _ _ _ u v, ddC_swap _ _ _ u w]
  ring

private theorem ddC_self (J : E → E →L[ℝ] E) (f : E → ℝ) (p v : E) :
    ddC J f p v v = 0 := by linarith [ddC_swap J f p v v]

/-- Strict positivity of the actual Levi form on every nonzero vector in the real
span of the frame, from the Schur complement computed at that point. -/
theorem positive_of_schur {F : Frame E} {p : E} (q : EquationsAt F p) {h : E → ℝ}
    (dh : ContDiffAt ℝ 2 h p) (rh : ∀ᶠ y in 𝓝 p, along F.R h y = 0)
    (hB : 0 < LeviBoundary.vertical (F.t p) (jet F h p))
    (hS : 0 < LeviBoundary.schur (F.t p) (jet F h p))
    (a b c d : ℝ) {w : E}
    (hw : w = a • F.X p + b • F.J p (F.X p) + c • F.R p + d • F.J p (F.R p))
    (hne : w ≠ 0) : 0 < ddC F.J (potential F h) p w (F.J p w) := by
  have jjx : F.J p (F.J p (F.X p)) = -F.X p := by
    rw [q.JX.self_of_nhds, map_smul, q.JH.self_of_nhds, smul_smul]
    simp [q.positive.ne']
  have jjr : F.J p (F.J p (F.R p)) = -F.R p := by rw [q.JR.self_of_nhds, q.JV.self_of_nhds]
  have jw : F.J p w = (-b) • F.X p + a • F.J p (F.X p) + (-d) • F.R p + c • F.J p (F.R p) := by
    rw [hw]; simp [map_add, map_smul, jjx, jjr]; abel
  obtain ⟨hA,hB',hC,hD,hC',hD'⟩ := levi_frame q dh rh
  let A := LeviBoundary.horizontal (F.t p) (jet F h p)
  let B := LeviBoundary.vertical (F.t p) (jet F h p)
  let C := LeviBoundary.mixedJ (F.t p) (jet F h p)
  let D := LeviBoundary.mixedR (F.t p) (jet F h p)
  let L := ddC F.J (potential F h) p
  have formula : L w (F.J p w) =
      A*(a^2+b^2) + B*(c^2+d^2) + 2*C*(a*c+b*d) + 2*D*(b*c-a*d) := by
    change ddC _ _ _ _ _ = _
    rw [jw,hw]
    simp only [ddC_add_left, ddC_add_right, ddC_smul_left, ddC_smul_right, ddC_self,
      hA, hB', hC, hD, hC', hD',
      ddC_swap _ _ _ (F.X p) (F.J p (F.X p)), ddC_swap _ _ _ (F.R p) (F.J p (F.R p)),
      ddC_swap _ _ _ (F.X p) (F.R p), ddC_swap _ _ _ (F.X p) (F.J p (F.R p)),
      ddC_swap _ _ _ (F.J p (F.X p)) (F.R p), ddC_swap _ _ _ (F.J p (F.X p)) (F.J p (F.R p))]
    dsimp [A,B,C,D]
    ring
  have posB : 0 < B := hB
  change 0 < A - (C^2 + D^2)/B at hS
  have sq : L w (F.J p w) =
      (A - (C^2+D^2)/B)*(a^2+b^2) + ((B*c+C*a+D*b)^2 + (B*d+C*b-D*a)^2)/B := by
    rw [formula]
    field_simp [posB.ne']
    ring
  change 0 < L w (F.J p w)
  by_cases hab : a = 0 ∧ b = 0
  · obtain ⟨rfl,rfl⟩ := hab
    have hcd : 0 < c^2+d^2 := by
      by_contra! hz
      have hc : c = 0 := by nlinarith [sq_nonneg d, sq_nonneg c]
      have hd : d = 0 := by nlinarith [sq_nonneg d, sq_nonneg c]
      exact hne (by simpa [hc,hd] using hw)
    simpa [formula] using mul_pos posB hcd
  · have hab' : 0 < a^2+b^2 := by
      by_contra! hz; exact hab ⟨by nlinarith [sq_nonneg b], by nlinarith [sq_nonneg a]⟩
    rw [sq]
    exact add_pos_of_pos_of_nonneg (mul_pos hS hab') (div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) posB.le)

end TransportOkaGrauert.FrameLevi
