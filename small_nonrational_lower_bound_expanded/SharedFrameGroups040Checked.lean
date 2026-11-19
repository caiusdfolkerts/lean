module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups040Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 0556
cert_group_pairs 0556 00000 0 128 128
cert_group_pairs 0556 00128 128 256 128
cert_group_pairs 0556 00256 256 384 128
cert_group_pairs 0556 00384 384 512 128
cert_group_pairs 0556 00512 512 640 128
cert_group_pairs 0556 00640 640 768 128
cert_group_pairs 0556 00768 768 896 128
cert_group_pairs 0556 00896 896 1024 128
cert_group_pairs 0556 01024 1024 1152 128
cert_group_pairs 0556 01152 1152 1171 19
cert_group_facts_3 0556 1171
cert_group_header 0557
cert_group_pairs 0557 00000 0 128 128
cert_group_pairs 0557 00128 128 256 128
cert_group_pairs 0557 00256 256 384 128
cert_group_pairs 0557 00384 384 512 128
cert_group_pairs 0557 00512 512 640 128
cert_group_pairs 0557 00640 640 768 128
cert_group_pairs 0557 00768 768 896 128
cert_group_pairs 0557 00896 896 1024 128
cert_group_pairs 0557 01024 1024 1152 128
cert_group_pairs 0557 01152 1152 1280 128
cert_group_pairs 0557 01280 1280 1328 48
theorem group0557_facts : group0557.Facts FacetUniverses.FullSix0.cells :=
  group0557.facts_of_checks _ group0557_header (interval_append _ 0 640 1328 (interval_append _ 0 256 640 (interval_append _ 0 128 256 group0557_pairs_00000 group0557_pairs_00128) (interval_append _ 256 384 640 group0557_pairs_00256 (interval_append _ 384 512 640 group0557_pairs_00384 group0557_pairs_00512))) (interval_append _ 640 1024 1328 (interval_append _ 640 768 1024 group0557_pairs_00640 (interval_append _ 768 896 1024 group0557_pairs_00768 group0557_pairs_00896)) (interval_append _ 1024 1152 1328 group0557_pairs_01024 (interval_append _ 1152 1280 1328 group0557_pairs_01152 group0557_pairs_01280))))
cert_group_header 0558
cert_group_pairs 0558 00000 0 127 127
cert_group_facts_6 0558
cert_group_header 0559
cert_group_pairs 0559 00000 0 128 128
cert_group_pairs 0559 00128 128 237 109
cert_group_facts 0559 237
cert_group_header 0560
cert_group_pairs 0560 00000 0 97 97
cert_group_facts_6 0560
end Papers.RationalityTen.SharedFrameCatalogue
