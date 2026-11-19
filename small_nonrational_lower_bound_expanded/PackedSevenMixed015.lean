module
prelude
public meta import LowerSchemas.FinitePackedSevenMixed
public import PackedSevenMixed015Cache
public import PackedSevenMixed015Leaves
public import IdentityGrowthRenaming
public import PackedSevenMixed015Proof000
public import PackedSevenMixed015Proof001
public import PackedSevenMixed015Proof002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenMixed015
open Papers.RationalityTen
open ConcreteGrowth GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth FiniteChecks
open RawNatGrowthSoundness RawNatGrowthCompleteness RawGrowthCacheCertificate
theorem nodeTest_complete : Interval nodeTest 0 1575 := (interval_append nodeTest 0 640 1575 checkedInterval0 (interval_append nodeTest 640 1280 1575 checkedInterval640 checkedInterval1280))
cert_renamings 521
cert_root 1575 1574
cert_nodes 1575 521 18
cert_boundary_classification 521

end Papers.RationalityTen.PackedReplay.PackedSevenMixed015
