module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups089Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 0995
cert_group_pairs 0995 00000 0 128 128
cert_group_pairs 0995 00128 128 256 128
cert_group_pairs 0995 00256 256 384 128
cert_group_pairs 0995 00384 384 512 128
cert_group_pairs 0995 00512 512 640 128
cert_group_pairs 0995 00640 640 768 128
cert_group_pairs 0995 00768 768 896 128
cert_group_pairs 0995 00896 896 1024 128
cert_group_pairs 0995 01024 1024 1152 128
cert_group_pairs 0995 01152 1152 1280 128
cert_group_pairs 0995 01280 1280 1408 128
cert_group_pairs 0995 01408 1408 1536 128
cert_group_pairs 0995 01536 1536 1664 128
cert_group_pairs 0995 01664 1664 1792 128
cert_group_pairs 0995 01792 1792 1920 128
cert_group_pairs 0995 01920 1920 2048 128
cert_group_pairs 0995 02048 2048 2176 128
cert_group_pairs 0995 02176 2176 2275 99
theorem group0995_facts : group0995.Facts FacetUniverses.FullSix0.cells :=
  group0995.facts_of_checks _ group0995_header (interval_append _ 0 1152 2275 (interval_append _ 0 512 1152 (interval_append _ 0 256 512 (interval_append _ 0 128 256 group0995_pairs_00000 group0995_pairs_00128) (interval_append _ 256 384 512 group0995_pairs_00256 group0995_pairs_00384)) (interval_append _ 512 768 1152 (interval_append _ 512 640 768 group0995_pairs_00512 group0995_pairs_00640) (interval_append _ 768 896 1152 group0995_pairs_00768 (interval_append _ 896 1024 1152 group0995_pairs_00896 group0995_pairs_01024)))) (interval_append _ 1152 1664 2275 (interval_append _ 1152 1408 1664 (interval_append _ 1152 1280 1408 group0995_pairs_01152 group0995_pairs_01280) (interval_append _ 1408 1536 1664 group0995_pairs_01408 group0995_pairs_01536)) (interval_append _ 1664 1920 2275 (interval_append _ 1664 1792 1920 group0995_pairs_01664 group0995_pairs_01792) (interval_append _ 1920 2048 2275 group0995_pairs_01920 (interval_append _ 2048 2176 2275 group0995_pairs_02048 group0995_pairs_02176)))))
#print axioms group0995_facts
cert_group_header 0996
cert_group_pairs 0996 00000 0 128 128
cert_group_pairs 0996 00128 128 220 92
cert_group_facts 0996 220
#print axioms group0996_facts
cert_group_header 0997
cert_group_pairs 0997 00000 0 128 128
cert_group_pairs 0997 00128 128 220 92
cert_group_facts 0997 220
#print axioms group0997_facts
cert_group_header 0998
cert_group_pairs 0998 00000 0 128 128
cert_group_pairs 0998 00128 128 256 128
cert_group_pairs 0998 00256 256 271 15
cert_group_facts_2 0998 271
#print axioms group0998_facts
cert_group_header 0999
cert_group_pairs 0999 00000 0 128 128
cert_group_pairs 0999 00128 128 136 8
cert_group_facts 0999 136
#print axioms group0999_facts
end Papers.RationalityTen.SharedFrameCatalogue
