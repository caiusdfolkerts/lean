module
public import MatroidCatalogue.Definitions

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Finset Papers.RationalityTen.BasisFamilies Papers.RationalityTen.BasisReconstruction
open Papers.RationalityTen.BasisCatalogue Papers.RationalityTen.BasisCertificates
namespace Papers.RationalityTen.MatroidCatalogue

theorem extension_0_0 (hn : 0 < 8) : ExtensionCovered catalogue 0 0 hn := by
  intro B hB M hM
  have hpos := rank_pos_of_ground_nonempty M
    (by decide : (groundPrefix 1).Nonempty)
  omega

theorem coloop_0_0 (hn : 0 < 8) : ColoopCovered catalogue 0 0 hn := by
  intro hr
  omega

end Papers.RationalityTen.MatroidCatalogue
