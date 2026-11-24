import TransportOkaGrauert.ScalarWLocalization
import TransportOkaGrauert.ScalarGeneralWIdentity

/-! # Steinness of the transport twistor interior on a simple conformal disk

The localized integral of the transverse derivative is smoothing. Its square
provides the compact error in the invariant-mean construction. Scalar ray
injectivity removes the smooth cokernel, and the resulting invariant means
give the holomorphic pencils on every open base subdomain. -/
namespace TransportOkaGrauert.GeneralStein

theorem local_invariant_mean : SteinMomentBridge.LocalMeanStatement := by
  apply ScalarWRangeBridge.local_mean
  intro σ simple r hr hr₁
  apply ScalarWRangeBridge.localize_kernel simple hr hr₁
  intro B compact inside
  exact ScalarGeneralKernel.Wvalue_kernel simple compact compact inside inside

theorem universal_chart : ChartStein.GeneralSimpleSurfaceStatement := fun _ simple =>
  SteinMomentBridge.chart_of_mean simple (SteinMomentBridge.mean_from_local local_invariant_mean simple)

theorem universal_manifold : ManifoldStein.GeneralManifoldStatement :=
  ManifoldStein.manifold_of_chart universal_chart

end TransportOkaGrauert.GeneralStein
