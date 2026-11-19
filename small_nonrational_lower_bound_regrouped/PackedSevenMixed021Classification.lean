module
prelude
public meta import LowerSchemas.FinitePackedSevenMixed
public import PackedSevenMixed021

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenMixed021
open Papers.RationalityTen ConcreteGrowth GrowthDAG SparseGrowthDAG GrowthRenaming

cert_leaves_nodup
/-- Exact closed-leaf classification, retaining the no-duplicates certificate. -/
cert_boundary_classification_nodup 556
/-- Uniform word-action interface; this family needs only the empty word. -/
cert_boundary_classification_word 556 1
#print axioms boundary_classification_word
end Papers.RationalityTen.PackedReplay.PackedSevenMixed021
