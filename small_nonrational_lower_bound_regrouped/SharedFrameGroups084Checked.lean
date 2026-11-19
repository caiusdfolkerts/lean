module
prelude
public meta import LowerSchemas.FiniteSharedFrameGroups
public import SharedFrameGroups084Data
public import FullSix0FacetUniverse
@[expose] public section
namespace Papers.RationalityTen.SharedFrameCatalogue
open SharedGraphFramePairs FiniteChecks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
cert_group_header 0954
cert_group_pairs 0954 00000 0 128 128
cert_group_pairs 0954 00128 128 153 25
cert_group_facts 0954 153
#print axioms group0954_facts
cert_group_header 0955
cert_group_pairs 0955 00000 0 104 104
cert_group_facts_6 0955
#print axioms group0955_facts
cert_group_header 0956
cert_group_pairs 0956 00000 0 128 128
cert_group_pairs 0956 00128 128 136 8
cert_group_facts 0956 136
#print axioms group0956_facts
cert_group_header 0957
cert_group_pairs 0957 00000 0 128 128
cert_group_pairs 0957 00128 128 248 120
cert_group_facts 0957 248
#print axioms group0957_facts
cert_group_header 0958
cert_group_pairs 0958 00000 0 128 128
cert_group_pairs 0958 00128 128 161 33
cert_group_facts 0958 161
#print axioms group0958_facts
cert_group_header 0959
cert_group_pairs 0959 00000 0 128 128
cert_group_pairs 0959 00128 128 137 9
cert_group_facts 0959 137
#print axioms group0959_facts
cert_group_header 0960
cert_group_pairs 0960 00000 0 128 128
cert_group_pairs 0960 00128 128 161 33
cert_group_facts 0960 161
#print axioms group0960_facts
cert_group_header 0961
cert_group_pairs 0961 00000 0 128 128
cert_group_pairs 0961 00128 128 256 128
cert_group_pairs 0961 00256 256 384 128
cert_group_pairs 0961 00384 384 426 42
cert_group_facts_4 0961 426
#print axioms group0961_facts
cert_group_header 0962
cert_group_pairs 0962 00000 0 128 128
cert_group_pairs 0962 00128 128 256 128
cert_group_pairs 0962 00256 256 384 128
cert_group_pairs 0962 00384 384 512 128
cert_group_pairs 0962 00512 512 640 128
cert_group_pairs 0962 00640 640 768 128
cert_group_pairs 0962 00768 768 796 28
theorem group0962_facts : group0962.Facts FacetUniverses.FullSix0.cells :=
  group0962.facts_of_checks _ group0962_header (interval_append _ 0 384 796 (interval_append _ 0 128 384 group0962_pairs_00000 (interval_append _ 128 256 384 group0962_pairs_00128 group0962_pairs_00256)) (interval_append _ 384 640 796 (interval_append _ 384 512 640 group0962_pairs_00384 group0962_pairs_00512) (interval_append _ 640 768 796 group0962_pairs_00640 group0962_pairs_00768)))
#print axioms group0962_facts
cert_group_header 0963
cert_group_pairs 0963 00000 0 128 128
cert_group_pairs 0963 00128 128 163 35
cert_group_facts 0963 163
#print axioms group0963_facts
cert_group_header 0964
cert_group_pairs 0964 00000 0 128 128
cert_group_pairs 0964 00128 128 137 9
cert_group_facts 0964 137
#print axioms group0964_facts
cert_group_header 0965
cert_group_pairs 0965 00000 0 128 128
cert_group_pairs 0965 00128 128 256 128
cert_group_pairs 0965 00256 256 384 128
cert_group_pairs 0965 00384 384 469 85
cert_group_facts_4 0965 469
#print axioms group0965_facts
cert_group_header 0966
cert_group_pairs 0966 00000 0 125 125
cert_group_facts_6 0966
#print axioms group0966_facts
cert_group_header 0967
cert_group_pairs 0967 00000 0 128 128
cert_group_pairs 0967 00128 128 130 2
cert_group_facts 0967 130
#print axioms group0967_facts
cert_group_header 0968
cert_group_pairs 0968 00000 0 128 128
cert_group_pairs 0968 00128 128 158 30
cert_group_facts 0968 158
#print axioms group0968_facts
cert_group_header 0969
cert_group_pairs 0969 00000 0 128 128
cert_group_pairs 0969 00128 128 256 128
cert_group_pairs 0969 00256 256 259 3
cert_group_facts_2 0969 259
#print axioms group0969_facts
end Papers.RationalityTen.SharedFrameCatalogue
