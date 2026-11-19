module
prelude
public meta import LowerSchemas.FinitePackedSevenMixed
public import PackedSevenMixed012Cache
public import PackedSevenMixed012Leaves
public import IdentityGrowthRenaming
public import PackedSevenMixed012Proof000
public import PackedSevenMixed012Proof001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenMixed012
open Papers.RationalityTen
open ConcreteGrowth GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth FiniteChecks
open RawNatGrowthSoundness RawNatGrowthCompleteness RawGrowthCacheCertificate
theorem nodeTest_complete : Interval nodeTest 0 868 := (interval_append nodeTest 0 640 868 checkedInterval0 checkedInterval640)
cert_renamings 838
cert_root 868 867
cert_nodes 868 838 1
cert_boundary_classification 838
#print axioms boundary_classification

end Papers.RationalityTen.PackedReplay.PackedSevenMixed012
