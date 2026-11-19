module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups076Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 0868
cert_group_pairs 0868 00000 0 128 128
cert_group_pairs 0868 00128 128 256 128
cert_group_pairs 0868 00256 256 284 28
cert_group_facts_2 0868 284
cert_group_header 0869
cert_group_pairs 0869 00000 0 128 128
cert_group_pairs 0869 00128 128 256 128
cert_group_pairs 0869 00256 256 384 128
cert_group_pairs 0869 00384 384 512 128
cert_group_pairs 0869 00512 512 640 128
cert_group_pairs 0869 00640 640 768 128
cert_group_pairs 0869 00768 768 896 128
cert_group_pairs 0869 00896 896 1024 128
cert_group_pairs 0869 01024 1024 1152 128
cert_group_pairs 0869 01152 1152 1280 128
cert_group_pairs 0869 01280 1280 1408 128
cert_group_pairs 0869 01408 1408 1536 128
cert_group_pairs 0869 01536 1536 1664 128
cert_group_pairs 0869 01664 1664 1792 128
cert_group_pairs 0869 01792 1792 1920 128
theorem group0869_facts : group0869.Facts FacetUniverses.FullSix0.cells :=
  group0869.facts_of_checks _ group0869_header (interval_append _ 0 896 1920 (interval_append _ 0 384 896 (interval_append _ 0 128 384 group0869_pairs_00000 (interval_append _ 128 256 384 group0869_pairs_00128 group0869_pairs_00256)) (interval_append _ 384 640 896 (interval_append _ 384 512 640 group0869_pairs_00384 group0869_pairs_00512) (interval_append _ 640 768 896 group0869_pairs_00640 group0869_pairs_00768))) (interval_append _ 896 1408 1920 (interval_append _ 896 1152 1408 (interval_append _ 896 1024 1152 group0869_pairs_00896 group0869_pairs_01024) (interval_append _ 1152 1280 1408 group0869_pairs_01152 group0869_pairs_01280)) (interval_append _ 1408 1664 1920 (interval_append _ 1408 1536 1664 group0869_pairs_01408 group0869_pairs_01536) (interval_append _ 1664 1792 1920 group0869_pairs_01664 group0869_pairs_01792))))
end Papers.RationalityTen.SharedFrameCatalogue
