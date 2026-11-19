module
public import MatroidCatalogue.Definitions

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
namespace Papers.RationalityTen.MatroidCatalogue

theorem extension_0_4 (hn : 0 < 8) : ExtensionCovered catalogue 0 4 hn := by
  intro B hB
  simp only [catalogue,count,Finset.range_zero,Finset.image_empty,Finset.notMem_empty] at hB

theorem coloop_0_4 (hn : 0 < 8) : ColoopCovered catalogue 0 4 hn := by
  intro hr B hB
  simp only [Nat.reduceSub,catalogue,count,Finset.range_zero,Finset.image_empty,Finset.notMem_empty] at hB

end Papers.RationalityTen.MatroidCatalogue
