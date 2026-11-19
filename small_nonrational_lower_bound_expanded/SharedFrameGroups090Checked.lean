module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups090Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 1000
cert_group_pairs 1000 00000 0 128 128
cert_group_pairs 1000 00128 128 256 128
cert_group_pairs 1000 00256 256 384 128
cert_group_pairs 1000 00384 384 512 128
cert_group_pairs 1000 00512 512 640 128
cert_group_pairs 1000 00640 640 768 128
cert_group_pairs 1000 00768 768 896 128
cert_group_pairs 1000 00896 896 1024 128
cert_group_pairs 1000 01024 1024 1152 128
cert_group_pairs 1000 01152 1152 1280 128
cert_group_pairs 1000 01280 1280 1341 61
theorem group1000_facts : group1000.Facts FacetUniverses.FullSix0.cells :=
  group1000.facts_of_checks _ group1000_header (interval_append _ 0 640 1341 (interval_append _ 0 256 640 (interval_append _ 0 128 256 group1000_pairs_00000 group1000_pairs_00128) (interval_append _ 256 384 640 group1000_pairs_00256 (interval_append _ 384 512 640 group1000_pairs_00384 group1000_pairs_00512))) (interval_append _ 640 1024 1341 (interval_append _ 640 768 1024 group1000_pairs_00640 (interval_append _ 768 896 1024 group1000_pairs_00768 group1000_pairs_00896)) (interval_append _ 1024 1152 1341 group1000_pairs_01024 (interval_append _ 1152 1280 1341 group1000_pairs_01152 group1000_pairs_01280))))
end Papers.RationalityTen.SharedFrameCatalogue
