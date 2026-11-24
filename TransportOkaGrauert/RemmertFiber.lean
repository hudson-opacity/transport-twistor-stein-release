import Mathlib.Analysis.Complex.Basic

/-!
# Compact analytic sets and the fibre divisors

In a global oriented frame, the interior of the twistor disk bundle is a product
of the base with an open unit disk as a set. Its complex structure need not be
the product structure. The lemmas here use the zero sets of the holomorphic
fibre divisors to confine a compact connected analytic set to one disk. They
then use the ordinary coordinate on that disk to show that the set is a point.

The predicates on functions on `S` below allow the caller to supply the analytic
inputs: the maximum principle for a reduced compact connected analytic space,
holomorphicity of the restricted divisors, and holomorphicity of the disk
coordinate after the inclusion factors through a complex fibre. No assertion
about holomorphicity of the disk coordinate on the ambient twistor space is used.
-/

namespace TransportOkaGrauert.RemmertFiber

/-- Fibre coordinates of norm strictly less than one. -/
abbrev UnitDisk := Metric.ball (0 : ℂ) 1

variable {B : Type*} {S : Set (B × UnitDisk)}

/-- The maximum principle applied to the divisor through `a` puts every point
of `S` in the fibre through `a`. -/
theorem point_in_base_fiber
    (F : B → B × UnitDisk → ℂ)
    (zero_iff : ∀ p z, F p z = 0 ↔ z.1 = p)
    (holOnS : (S → ℂ) → Prop)
    (max_principle : ∀ f, holOnS f → ∀ a b, f a = f b)
    (divisor_hol : ∀ p, holOnS (fun z => F p z.val))
    (a b : S) : b.val.1 = a.val.1 := by
  apply (zero_iff a.val.1 b.val).mp
  calc
    F a.val.1 b.val = F a.val.1 a.val := max_principle _ (divisor_hol _) b a
    _ = 0 := (zero_iff _ _).mpr rfl

/-- A compact connected analytic set in the twistor interior has at most one
point. The restricted coordinate becomes a holomorphic function on `S` once
`S` lies in a single fibre, where the complex structure is the ordinary one. -/
theorem subsingleton_of_fiber_divisors
    (F : B → B × UnitDisk → ℂ)
    (zero_iff : ∀ p z, F p z = 0 ↔ z.1 = p)
    (holOnS : (S → ℂ) → Prop)
    (max_principle : ∀ f, holOnS f → ∀ a b, f a = f b)
    (divisor_hol : ∀ p, holOnS (fun z => F p z.val))
    (coord_hol_on_fiber : ∀ p : B, (∀ z : S, z.val.1 = p) →
      holOnS (fun z => (z.val.2 : ℂ))) : S.Subsingleton := by
  intro a ha b hb
  let a' : S := ⟨a, ha⟩
  let b' : S := ⟨b, hb⟩
  have base_eq : ∀ z : S, z.val.1 = a.1 :=
    point_in_base_fiber F zero_iff holOnS max_principle divisor_hol a'
  apply Prod.ext (base_eq b').symm
  apply Subtype.ext
  exact max_principle _ (coord_hol_on_fiber _ base_eq) a' b'

end TransportOkaGrauert.RemmertFiber
