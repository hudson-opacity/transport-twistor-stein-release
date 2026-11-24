module

public import RegistryDefinitions
import TransportOkaGrauert.GermStein

/-! # Proof of the transport twistor Stein theorem -/

public section
open Metric Set
namespace SteinRegistry

/-- The transport twistor interior of every smooth simple disk is Stein over every open base subdomain. -/
theorem stein_transport_twistor_interior : Statement := by
  intro σ simple U openU inside
  have metric : TransportOkaGrauert.SimpleDiskTarget.SimpleMetricGerm σ :=
    ⟨simple.smooth, simple.strictConvex, simple.escapes, simple.noConjugate⟩
  have stein := TransportOkaGrauert.GeneralStein.chart_of_smooth_germ metric U openU inside
  exact ⟨stein.convex, stein.separates, stein.coordinates⟩

end SteinRegistry
