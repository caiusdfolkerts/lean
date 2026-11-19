module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups072Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 0847
cert_group_pairs 0847 00000 0 128 128
cert_group_pairs 0847 00128 128 256 128
cert_group_pairs 0847 00256 256 384 128
cert_group_pairs 0847 00384 384 512 128
cert_group_pairs 0847 00512 512 640 128
cert_group_pairs 0847 00640 640 768 128
cert_group_pairs 0847 00768 768 896 128
cert_group_pairs 0847 00896 896 1024 128
cert_group_pairs 0847 01024 1024 1152 128
cert_group_pairs 0847 01152 1152 1280 128
cert_group_pairs 0847 01280 1280 1408 128
cert_group_pairs 0847 01408 1408 1536 128
cert_group_pairs 0847 01536 1536 1664 128
cert_group_pairs 0847 01664 1664 1792 128
cert_group_pairs 0847 01792 1792 1884 92
theorem group0847_facts : group0847.Facts FacetUniverses.FullSix0.cells :=
  group0847.facts_of_checks _ group0847_header (interval_append _ 0 896 1884 (interval_append _ 0 384 896 (interval_append _ 0 128 384 group0847_pairs_00000 (interval_append _ 128 256 384 group0847_pairs_00128 group0847_pairs_00256)) (interval_append _ 384 640 896 (interval_append _ 384 512 640 group0847_pairs_00384 group0847_pairs_00512) (interval_append _ 640 768 896 group0847_pairs_00640 group0847_pairs_00768))) (interval_append _ 896 1408 1884 (interval_append _ 896 1152 1408 (interval_append _ 896 1024 1152 group0847_pairs_00896 group0847_pairs_01024) (interval_append _ 1152 1280 1408 group0847_pairs_01152 group0847_pairs_01280)) (interval_append _ 1408 1664 1884 (interval_append _ 1408 1536 1664 group0847_pairs_01408 group0847_pairs_01536) (interval_append _ 1664 1792 1884 group0847_pairs_01664 group0847_pairs_01792))))
cert_group_header 0848
cert_group_pairs 0848 00000 0 128 128
cert_group_pairs 0848 00128 128 256 128
cert_group_pairs 0848 00256 256 287 31
cert_group_facts_2 0848 287
cert_group_header 0849
cert_group_pairs 0849 00000 0 128 128
cert_group_pairs 0849 00128 128 188 60
cert_group_facts 0849 188
cert_group_header 0850
cert_group_pairs 0850 00000 0 128 128
cert_group_pairs 0850 00128 128 150 22
cert_group_facts 0850 150
cert_group_header 0851
cert_group_pairs 0851 00000 0 128 128
cert_group_pairs 0851 00128 128 188 60
cert_group_facts 0851 188
cert_group_header 0852
cert_group_pairs 0852 00000 0 128 128
cert_group_facts_6 0852
cert_group_header 0853
cert_group_pairs 0853 00000 0 128 128
cert_group_pairs 0853 00128 128 137 9
cert_group_facts 0853 137
cert_group_header 0854
cert_group_pairs 0854 00000 0 128 128
cert_group_pairs 0854 00128 128 174 46
cert_group_facts 0854 174
cert_group_header 0855
cert_group_pairs 0855 00000 0 128 128
cert_group_pairs 0855 00128 128 234 106
cert_group_facts 0855 234
cert_group_header 0856
cert_group_pairs 0856 00000 0 128 128
cert_group_pairs 0856 00128 128 256 128
cert_group_pairs 0856 00256 256 262 6
cert_group_facts_2 0856 262
end Papers.RationalityTen.SharedFrameCatalogue
