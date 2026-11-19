module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups041Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 0561
cert_group_pairs 0561 00000 0 128 128
cert_group_pairs 0561 00128 128 256 128
cert_group_pairs 0561 00256 256 384 128
cert_group_pairs 0561 00384 384 512 128
cert_group_pairs 0561 00512 512 640 128
cert_group_pairs 0561 00640 640 768 128
cert_group_pairs 0561 00768 768 896 128
cert_group_pairs 0561 00896 896 1024 128
cert_group_pairs 0561 01024 1024 1152 128
cert_group_pairs 0561 01152 1152 1214 62
cert_group_facts_3 0561 1214
#print axioms group0561_facts
cert_group_header 0562
cert_group_pairs 0562 00000 0 128 128
cert_group_pairs 0562 00128 128 256 128
cert_group_pairs 0562 00256 256 384 128
cert_group_pairs 0562 00384 384 512 128
cert_group_pairs 0562 00512 512 640 128
cert_group_pairs 0562 00640 640 768 128
cert_group_pairs 0562 00768 768 896 128
cert_group_pairs 0562 00896 896 1024 128
cert_group_pairs 0562 01024 1024 1152 128
cert_group_pairs 0562 01152 1152 1193 41
cert_group_facts_3 0562 1193
#print axioms group0562_facts
cert_group_header 0563
cert_group_pairs 0563 00000 0 128 128
cert_group_pairs 0563 00128 128 256 128
cert_group_pairs 0563 00256 256 384 128
cert_group_pairs 0563 00384 384 512 128
cert_group_pairs 0563 00512 512 640 128
cert_group_pairs 0563 00640 640 768 128
cert_group_pairs 0563 00768 768 896 128
cert_group_pairs 0563 00896 896 1024 128
cert_group_pairs 0563 01024 1024 1152 128
cert_group_pairs 0563 01152 1152 1280 128
cert_group_pairs 0563 01280 1280 1408 128
cert_group_pairs 0563 01408 1408 1448 40
theorem group0563_facts : group0563.Facts FacetUniverses.FullSix0.cells :=
  group0563.facts_of_checks _ group0563_header (interval_append _ 0 768 1448 (interval_append _ 0 384 768 (interval_append _ 0 128 384 group0563_pairs_00000 (interval_append _ 128 256 384 group0563_pairs_00128 group0563_pairs_00256)) (interval_append _ 384 512 768 group0563_pairs_00384 (interval_append _ 512 640 768 group0563_pairs_00512 group0563_pairs_00640))) (interval_append _ 768 1152 1448 (interval_append _ 768 896 1152 group0563_pairs_00768 (interval_append _ 896 1024 1152 group0563_pairs_00896 group0563_pairs_01024)) (interval_append _ 1152 1280 1448 group0563_pairs_01152 (interval_append _ 1280 1408 1448 group0563_pairs_01280 group0563_pairs_01408))))
#print axioms group0563_facts
end Papers.RationalityTen.SharedFrameCatalogue
