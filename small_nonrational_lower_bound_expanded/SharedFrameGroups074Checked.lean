module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups074Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 0859
cert_group_pairs 0859 00000 0 128 128
cert_group_pairs 0859 00128 128 256 128
cert_group_pairs 0859 00256 256 384 128
cert_group_pairs 0859 00384 384 512 128
cert_group_pairs 0859 00512 512 640 128
cert_group_pairs 0859 00640 640 768 128
cert_group_pairs 0859 00768 768 896 128
cert_group_pairs 0859 00896 896 1024 128
cert_group_pairs 0859 01024 1024 1152 128
cert_group_pairs 0859 01152 1152 1280 128
cert_group_pairs 0859 01280 1280 1408 128
cert_group_pairs 0859 01408 1408 1536 128
cert_group_pairs 0859 01536 1536 1664 128
cert_group_pairs 0859 01664 1664 1792 128
cert_group_pairs 0859 01792 1792 1920 128
cert_group_pairs 0859 01920 1920 2048 128
cert_group_pairs 0859 02048 2048 2176 128
cert_group_pairs 0859 02176 2176 2304 128
cert_group_pairs 0859 02304 2304 2327 23
theorem group0859_facts : group0859.Facts FacetUniverses.FullSix0.cells :=
  group0859.facts_of_checks _ group0859_header (interval_append _ 0 1152 2327 (interval_append _ 0 512 1152 (interval_append _ 0 256 512 (interval_append _ 0 128 256 group0859_pairs_00000 group0859_pairs_00128) (interval_append _ 256 384 512 group0859_pairs_00256 group0859_pairs_00384)) (interval_append _ 512 768 1152 (interval_append _ 512 640 768 group0859_pairs_00512 group0859_pairs_00640) (interval_append _ 768 896 1152 group0859_pairs_00768 (interval_append _ 896 1024 1152 group0859_pairs_00896 group0859_pairs_01024)))) (interval_append _ 1152 1792 2327 (interval_append _ 1152 1408 1792 (interval_append _ 1152 1280 1408 group0859_pairs_01152 group0859_pairs_01280) (interval_append _ 1408 1536 1792 group0859_pairs_01408 (interval_append _ 1536 1664 1792 group0859_pairs_01536 group0859_pairs_01664))) (interval_append _ 1792 2048 2327 (interval_append _ 1792 1920 2048 group0859_pairs_01792 group0859_pairs_01920) (interval_append _ 2048 2176 2327 group0859_pairs_02048 (interval_append _ 2176 2304 2327 group0859_pairs_02176 group0859_pairs_02304)))))
cert_group_header 0860
cert_group_pairs 0860 00000 0 128 128
cert_group_pairs 0860 00128 128 158 30
cert_group_facts 0860 158
cert_group_header 0861
cert_group_pairs 0861 00000 0 128 128
cert_group_facts_6 0861
cert_group_header 0862
cert_group_pairs 0862 00000 0 128 128
cert_group_pairs 0862 00128 128 158 30
cert_group_facts 0862 158
cert_group_header 0863
cert_group_pairs 0863 00000 0 128 128
cert_group_pairs 0863 00128 128 184 56
cert_group_facts 0863 184
end Papers.RationalityTen.SharedFrameCatalogue
