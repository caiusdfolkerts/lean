module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups093Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 1006
cert_group_pairs 1006 00000 0 128 128
cert_group_pairs 1006 00128 128 256 128
cert_group_pairs 1006 00256 256 384 128
cert_group_pairs 1006 00384 384 512 128
cert_group_pairs 1006 00512 512 640 128
cert_group_pairs 1006 00640 640 768 128
cert_group_pairs 1006 00768 768 896 128
cert_group_pairs 1006 00896 896 1024 128
cert_group_pairs 1006 01024 1024 1152 128
cert_group_pairs 1006 01152 1152 1280 128
cert_group_pairs 1006 01280 1280 1408 128
cert_group_pairs 1006 01408 1408 1536 128
cert_group_pairs 1006 01536 1536 1664 128
cert_group_pairs 1006 01664 1664 1792 128
cert_group_pairs 1006 01792 1792 1920 128
cert_group_pairs 1006 01920 1920 2048 128
cert_group_pairs 1006 02048 2048 2176 128
cert_group_pairs 1006 02176 2176 2261 85
theorem group1006_facts : group1006.Facts FacetUniverses.FullSix0.cells :=
  group1006.facts_of_checks _ group1006_header (interval_append _ 0 1152 2261 (interval_append _ 0 512 1152 (interval_append _ 0 256 512 (interval_append _ 0 128 256 group1006_pairs_00000 group1006_pairs_00128) (interval_append _ 256 384 512 group1006_pairs_00256 group1006_pairs_00384)) (interval_append _ 512 768 1152 (interval_append _ 512 640 768 group1006_pairs_00512 group1006_pairs_00640) (interval_append _ 768 896 1152 group1006_pairs_00768 (interval_append _ 896 1024 1152 group1006_pairs_00896 group1006_pairs_01024)))) (interval_append _ 1152 1664 2261 (interval_append _ 1152 1408 1664 (interval_append _ 1152 1280 1408 group1006_pairs_01152 group1006_pairs_01280) (interval_append _ 1408 1536 1664 group1006_pairs_01408 group1006_pairs_01536)) (interval_append _ 1664 1920 2261 (interval_append _ 1664 1792 1920 group1006_pairs_01664 group1006_pairs_01792) (interval_append _ 1920 2048 2261 group1006_pairs_01920 (interval_append _ 2048 2176 2261 group1006_pairs_02048 group1006_pairs_02176)))))
#print axioms group1006_facts
end Papers.RationalityTen.SharedFrameCatalogue
