module
public import MatroidCatalogue.Definitions

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
namespace Papers.RationalityTen.MatroidCatalogue

theorem extension_0_1 (hn : 0 < 8) : ExtensionCovered catalogue 0 1 hn := by
  intro B hB
  simp only [catalogue,count,Finset.range_zero,Finset.image_empty,Finset.notMem_empty] at hB

theorem coloop_0_1 (hn : 0 < 8) : ColoopCovered catalogue 0 1 hn := by
  intro hr B hB
  have hc : catalogue 0 0 = {{∅}} := by decide +kernel +revert
  rw [hc,Finset.mem_singleton] at hB
  subst B
  refine ⟨family 1 1 0, family_mem 1 1 0 (by decide), ?_⟩
  exact validWitness_sound 1 _ _ 16434824 (by decide +kernel +revert)

end Papers.RationalityTen.MatroidCatalogue
