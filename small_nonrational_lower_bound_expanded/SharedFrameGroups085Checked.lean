module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups085Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 0970
cert_group_pairs 0970 00000 0 128 128
cert_group_pairs 0970 00128 128 138 10
cert_group_facts 0970 138
cert_group_header 0971
cert_group_pairs 0971 00000 0 128 128
cert_group_pairs 0971 00128 128 187 59
cert_group_facts 0971 187
cert_group_header 0972
cert_group_pairs 0972 00000 0 125 125
cert_group_facts_6 0972
cert_group_header 0973
cert_group_pairs 0973 00000 0 128 128
cert_group_pairs 0973 00128 128 138 10
cert_group_facts 0973 138
cert_group_header 0974
cert_group_pairs 0974 00000 0 128 128
cert_group_pairs 0974 00128 128 151 23
cert_group_facts 0974 151
cert_group_header 0975
cert_group_pairs 0975 00000 0 105 105
cert_group_facts_6 0975
cert_group_header 0976
cert_group_pairs 0976 00000 0 128 128
cert_group_pairs 0976 00128 128 256 128
cert_group_pairs 0976 00256 256 384 128
cert_group_pairs 0976 00384 384 512 128
cert_group_pairs 0976 00512 512 640 128
cert_group_pairs 0976 00640 640 768 128
cert_group_pairs 0976 00768 768 896 128
cert_group_pairs 0976 00896 896 974 78
theorem group0976_facts : group0976.Facts FacetUniverses.FullSix0.cells :=
  group0976.facts_of_checks _ group0976_header (interval_append _ 0 512 974 (interval_append _ 0 256 512 (interval_append _ 0 128 256 group0976_pairs_00000 group0976_pairs_00128) (interval_append _ 256 384 512 group0976_pairs_00256 group0976_pairs_00384)) (interval_append _ 512 768 974 (interval_append _ 512 640 768 group0976_pairs_00512 group0976_pairs_00640) (interval_append _ 768 896 974 group0976_pairs_00768 group0976_pairs_00896)))
cert_group_header 0977
cert_group_pairs 0977 00000 0 128 128
cert_group_pairs 0977 00128 128 256 128
cert_group_pairs 0977 00256 256 384 128
cert_group_pairs 0977 00384 384 512 128
cert_group_pairs 0977 00512 512 640 128
cert_group_pairs 0977 00640 640 768 128
cert_group_pairs 0977 00768 768 896 128
cert_group_pairs 0977 00896 896 1024 128
cert_group_pairs 0977 01024 1024 1152 128
cert_group_pairs 0977 01152 1152 1280 128
cert_group_pairs 0977 01280 1280 1408 128
cert_group_pairs 0977 01408 1408 1536 128
cert_group_pairs 0977 01536 1536 1664 128
cert_group_pairs 0977 01664 1664 1741 77
theorem group0977_facts : group0977.Facts FacetUniverses.FullSix0.cells :=
  group0977.facts_of_checks _ group0977_header (interval_append _ 0 896 1741 (interval_append _ 0 384 896 (interval_append _ 0 128 384 group0977_pairs_00000 (interval_append _ 128 256 384 group0977_pairs_00128 group0977_pairs_00256)) (interval_append _ 384 640 896 (interval_append _ 384 512 640 group0977_pairs_00384 group0977_pairs_00512) (interval_append _ 640 768 896 group0977_pairs_00640 group0977_pairs_00768))) (interval_append _ 896 1280 1741 (interval_append _ 896 1024 1280 group0977_pairs_00896 (interval_append _ 1024 1152 1280 group0977_pairs_01024 group0977_pairs_01152)) (interval_append _ 1280 1536 1741 (interval_append _ 1280 1408 1536 group0977_pairs_01280 group0977_pairs_01408) (interval_append _ 1536 1664 1741 group0977_pairs_01536 group0977_pairs_01664))))
cert_group_header 0978
cert_group_pairs 0978 00000 0 128 128
cert_group_pairs 0978 00128 128 252 124
cert_group_facts 0978 252
cert_group_header 0979
cert_group_pairs 0979 00000 0 128 128
cert_group_pairs 0979 00128 128 238 110
cert_group_facts 0979 238
end Papers.RationalityTen.SharedFrameCatalogue
