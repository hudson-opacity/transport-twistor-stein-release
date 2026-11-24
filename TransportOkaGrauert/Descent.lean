import Std

/-!
# From transport gauges to isomorphism classes of bundles

Bohr–Paternain, Proposition 4.12 and Theorem 4.13 (DOI 10.5802/jep.231).
For a fixed positive rank, the two setoids in this file model gauge
equivalence of admissible attenuations and holomorphic isomorphism of
bundles on the closed transport twistor space. A bundle can equivalently be
presented by an integrable partial connection in a smooth trivialization
when the underlying manifold is contractible.

The analytic assertions about smooth gauges, vertical normalization and
boundary restriction are explicit inputs. The descent to the quotient,
its bijectivity and its consequence for a distinguished trivial bundle
are proved here, independently of choices of gauges or representatives.
-/

namespace TransportOkaGrauert

universe u v

/-- The representative-level content of the twistor correspondence.
In Proposition 4.12, `toBundle A` is defined by the integrable partial
connection whose vertical component vanishes and whose tangential component
is the fibrewise extension of the angular modes of `A`. -/
structure TwistorPresentation {A : Type u} {B : Type v}
    (gauge : Setoid A) (iso : Setoid B) where
  toBundle : A → B
  /-- Extension and restriction of gauges identify equivalences of representatives. -/
  gauge_iff_iso : ∀ a a', gauge.r a a' ↔ iso.r (toBundle a) (toBundle a')
  /-- Every bundle has a representative in the image, up to isomorphism. -/
  represented : ∀ b, ∃ a, iso.r b (toBundle a)

namespace TwistorPresentation

variable {A : Type u} {B : Type v} {gauge : Setoid A} {iso : Setoid B}

/-- Obtain representability from the two steps used over a disk in Proposition 4.12.
The fibrewise gauge puts an integrable partial connection into vertical normal form.
The boundary value of its remaining coefficient recovers an attenuation. -/
def ofVerticalNormalForm (toBundle : A → B)
    (gauge_iff_iso : ∀ a a', gauge.r a a' ↔ iso.r (toBundle a) (toBundle a'))
    (normal : B → Prop)
    (normalize : ∀ b, ∃ b', iso.r b b' ∧ normal b')
    (recover : ∀ b', normal b' → ∃ a, iso.r b' (toBundle a)) :
    TwistorPresentation gauge iso where
  toBundle := toBundle
  gauge_iff_iso := gauge_iff_iso
  represented b := by
    obtain ⟨b', hIso, hNormal⟩ := normalize b
    obtain ⟨a, hRecover⟩ := recover b' hNormal
    exact ⟨a, iso.iseqv.trans hIso hRecover⟩

variable (P : TwistorPresentation gauge iso)

/-- The canonical map from transport gauge classes to bundle isomorphism classes. -/
def onClasses : Quotient gauge → Quotient iso :=
  Quotient.lift (fun a => Quotient.mk iso (P.toBundle a))
    (fun a a' h => Quotient.sound ((P.gauge_iff_iso a a').mp h))

@[simp] theorem onClasses_mk (a : A) :
    P.onClasses (Quotient.mk gauge a) = Quotient.mk iso (P.toBundle a) := rfl

/-- Two gauge classes agree whenever their associated bundle classes agree. -/
theorem injective_onClasses : Function.Injective P.onClasses := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro a a' h
  exact Quotient.sound ((P.gauge_iff_iso a a').mpr (Quotient.exact h))

/-- Every class has a preimage represented by an attenuation. -/
theorem surjective_onClasses : Function.Surjective P.onClasses := by
  intro y
  refine Quotient.inductionOn y ?_
  intro b
  obtain ⟨a, h⟩ := P.represented b
  exact ⟨Quotient.mk gauge a, Quotient.sound (iso.iseqv.symm h)⟩

/-- The pointed correspondence behind the equivalence of Theorems 1.3 and 1.4.
The zero attenuation presents the product bundle; reachability of zero means
that the transport equation admits a smooth holomorphic integrating factor. -/
theorem transportTriviality_iff_bundleTriviality (zero : A) (product : B)
    (zero_product : iso.r (P.toBundle zero) product) :
    (∀ a, gauge.r a zero) ↔ (∀ b, iso.r b product) := by
  constructor
  · intro h b
    obtain ⟨a, hb⟩ := P.represented b
    exact iso.iseqv.trans hb
      (iso.iseqv.trans ((P.gauge_iff_iso a zero).mp (h a)) zero_product)
  · intro h a
    exact (P.gauge_iff_iso a zero).mpr
      (iso.iseqv.trans (h (P.toBundle a)) (iso.iseqv.symm zero_product))

/-- The bundle-triviality conclusion in the forward direction. -/
theorem allBundlesTrivial (zero : A) (product : B)
    (zero_product : iso.r (P.toBundle zero) product)
    (integratingFactors : ∀ a, gauge.r a zero) :
    ∀ b, iso.r b product :=
  (P.transportTriviality_iff_bundleTriviality zero product zero_product).mp integratingFactors

end TwistorPresentation

end TransportOkaGrauert
