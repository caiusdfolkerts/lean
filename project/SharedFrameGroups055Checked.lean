module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups055Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 0660
cert_group_pairs 0660 00000 0 128 128
cert_group_pairs 0660 00128 128 256 128
cert_group_pairs 0660 00256 256 384 128
cert_group_pairs 0660 00384 384 512 128
cert_group_pairs 0660 00512 512 640 128
cert_group_pairs 0660 00640 640 768 128
cert_group_pairs 0660 00768 768 896 128
cert_group_pairs 0660 00896 896 1024 128
cert_group_pairs 0660 01024 1024 1152 128
cert_group_pairs 0660 01152 1152 1280 128
cert_group_pairs 0660 01280 1280 1408 128
cert_group_pairs 0660 01408 1408 1536 128
cert_group_pairs 0660 01536 1536 1664 128
cert_group_pairs 0660 01664 1664 1792 128
cert_group_pairs 0660 01792 1792 1920 128
cert_group_pairs 0660 01920 1920 2048 128
cert_group_pairs 0660 02048 2048 2176 128
cert_group_pairs 0660 02176 2176 2304 128
cert_group_pairs 0660 02304 2304 2389 85
theorem group0660_facts : group0660.Facts FacetUniverses.FullSix0.cells :=
  group0660.facts_of_checks _ group0660_header (interval_append _ 0 1152 2389 (interval_append _ 0 512 1152 (interval_append _ 0 256 512 (interval_append _ 0 128 256 group0660_pairs_00000 group0660_pairs_00128) (interval_append _ 256 384 512 group0660_pairs_00256 group0660_pairs_00384)) (interval_append _ 512 768 1152 (interval_append _ 512 640 768 group0660_pairs_00512 group0660_pairs_00640) (interval_append _ 768 896 1152 group0660_pairs_00768 (interval_append _ 896 1024 1152 group0660_pairs_00896 group0660_pairs_01024)))) (interval_append _ 1152 1792 2389 (interval_append _ 1152 1408 1792 (interval_append _ 1152 1280 1408 group0660_pairs_01152 group0660_pairs_01280) (interval_append _ 1408 1536 1792 group0660_pairs_01408 (interval_append _ 1536 1664 1792 group0660_pairs_01536 group0660_pairs_01664))) (interval_append _ 1792 2048 2389 (interval_append _ 1792 1920 2048 group0660_pairs_01792 group0660_pairs_01920) (interval_append _ 2048 2176 2389 group0660_pairs_02048 (interval_append _ 2176 2304 2389 group0660_pairs_02176 group0660_pairs_02304)))))
#print axioms group0660_facts
end Papers.RationalityTen.SharedFrameCatalogue
