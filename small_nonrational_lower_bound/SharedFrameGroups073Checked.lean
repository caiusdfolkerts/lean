module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups073Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 0857
cert_group_pairs 0857 00000 0 128 128
cert_group_pairs 0857 00128 128 256 128
cert_group_pairs 0857 00256 256 384 128
cert_group_pairs 0857 00384 384 512 128
cert_group_pairs 0857 00512 512 640 128
cert_group_pairs 0857 00640 640 768 128
cert_group_pairs 0857 00768 768 896 128
cert_group_pairs 0857 00896 896 1024 128
cert_group_pairs 0857 01024 1024 1152 128
cert_group_pairs 0857 01152 1152 1280 128
cert_group_pairs 0857 01280 1280 1408 128
cert_group_pairs 0857 01408 1408 1536 128
cert_group_pairs 0857 01536 1536 1664 128
cert_group_pairs 0857 01664 1664 1792 128
cert_group_pairs 0857 01792 1792 1844 52
theorem group0857_facts : group0857.Facts FacetUniverses.FullSix0.cells :=
  group0857.facts_of_checks _ group0857_header (interval_append _ 0 896 1844 (interval_append _ 0 384 896 (interval_append _ 0 128 384 group0857_pairs_00000 (interval_append _ 128 256 384 group0857_pairs_00128 group0857_pairs_00256)) (interval_append _ 384 640 896 (interval_append _ 384 512 640 group0857_pairs_00384 group0857_pairs_00512) (interval_append _ 640 768 896 group0857_pairs_00640 group0857_pairs_00768))) (interval_append _ 896 1408 1844 (interval_append _ 896 1152 1408 (interval_append _ 896 1024 1152 group0857_pairs_00896 group0857_pairs_01024) (interval_append _ 1152 1280 1408 group0857_pairs_01152 group0857_pairs_01280)) (interval_append _ 1408 1664 1844 (interval_append _ 1408 1536 1664 group0857_pairs_01408 group0857_pairs_01536) (interval_append _ 1664 1792 1844 group0857_pairs_01664 group0857_pairs_01792))))
#print axioms group0857_facts
cert_group_header 0858
cert_group_pairs 0858 00000 0 128 128
cert_group_pairs 0858 00128 128 256 128
cert_group_pairs 0858 00256 256 384 128
cert_group_pairs 0858 00384 384 512 128
cert_group_pairs 0858 00512 512 640 128
cert_group_pairs 0858 00640 640 768 128
cert_group_pairs 0858 00768 768 896 128
cert_group_pairs 0858 00896 896 1024 128
cert_group_pairs 0858 01024 1024 1152 128
cert_group_pairs 0858 01152 1152 1280 128
cert_group_pairs 0858 01280 1280 1284 4
theorem group0858_facts : group0858.Facts FacetUniverses.FullSix0.cells :=
  group0858.facts_of_checks _ group0858_header (interval_append _ 0 640 1284 (interval_append _ 0 256 640 (interval_append _ 0 128 256 group0858_pairs_00000 group0858_pairs_00128) (interval_append _ 256 384 640 group0858_pairs_00256 (interval_append _ 384 512 640 group0858_pairs_00384 group0858_pairs_00512))) (interval_append _ 640 1024 1284 (interval_append _ 640 768 1024 group0858_pairs_00640 (interval_append _ 768 896 1024 group0858_pairs_00768 group0858_pairs_00896)) (interval_append _ 1024 1152 1284 group0858_pairs_01024 (interval_append _ 1152 1280 1284 group0858_pairs_01152 group0858_pairs_01280))))
#print axioms group0858_facts
end Papers.RationalityTen.SharedFrameCatalogue
