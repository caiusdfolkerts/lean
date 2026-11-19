module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow29Part00067Data
public import GraphInputsRow29Part00067Frames
public import GraphInputsRow29Part00067Leaves
public import GraphInputsRow29Part00067Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00067.record007
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record007
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩, ⟨102, by decide⟩, ⟨103, by decide⟩, ⟨104, by decide⟩, ⟨105, by decide⟩, ⟨106, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), (certNat% 6), 9223934986808197120, (certNat% 7)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 8), (certNat% 9), (certNat% 4), (certNat% 10), 1706510765785088]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), (certNat% 4), (certNat% 12), (certNat% 13), (certNat% 3)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), (certNat% 15), (certNat% 6), (certNat% 16), (certNat% 17)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), (certNat% 6), (certNat% 19), (certNat% 20), (certNat% 21)]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), (certNat% 23), (certNat% 24), (certNat% 25), (certNat% 26)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 27), (certNat% 28), (certNat% 29), (certNat% 30), (certNat% 31)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 32), (certNat% 6), (certNat% 33), (certNat% 34), (certNat% 31)]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c1 c0
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 35), (certNat% 36), (certNat% 37)]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 38), 1688849860263936, (certNat% 29), (certNat% 6)]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 39), (certNat% 40), 9223934986808197120, (certNat% 29), (certNat% 20)]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨92, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 41), (certNat% 4), (certNat% 30), (certNat% 36), (certNat% 42)]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 43), (certNat% 4), (certNat% 6), (certNat% 10), (certNat% 44), (certNat% 42)]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c23 c22
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c24 c21
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c25 c14
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c26 c13
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c27 c12
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c28 c11
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c29 c10
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c30 c9
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c31 c8
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 45), (certNat% 31), (certNat% 46), (certNat% 15)]
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 47), (certNat% 48), (certNat% 49), (certNat% 50), 1708641069563904, (certNat% 51)]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c34 c33
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 52), (certNat% 53), (certNat% 54), 360287970189639680, (certNat% 44), (certNat% 17)]
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 55), (certNat% 56), (certNat% 57), (certNat% 58), 72057594037927936, (certNat% 48)]
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 59), (certNat% 60), (certNat% 61), (certNat% 62), (certNat% 63), 288230376151711744]
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c1 c0
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c1 c39
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c1 c40
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 64), 1688849860263936, 2251799813685248]
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c42 c41
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 65), (certNat% 37), 9223934986808197120, 2252349569499136]
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c44 c43
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c1 c0
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c1 c46
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c1 c47
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 66), 2251799813685248, 281509336449024]
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c49 c48
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 67), 9223934986808197120, 2252349569499136, (certNat% 3)]
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c51 c50
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 68), (certNat% 4), (certNat% 69), (certNat% 70), 562949953421312]
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c53 c52
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨92, by decide⟩ c54 c45
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 71), (certNat% 72), (certNat% 73), (certNat% 74), 9223934986808197120, (certNat% 75)]
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c56 c55
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c1 c46
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c1 c58
  let c60 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c1 c59
  let c61 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 76), (certNat% 77), 2252349569499136, (certNat% 78)]
  let c62 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c61 c60
  let c63 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 79), 2252349569499136, (certNat% 80), (certNat% 81)]
  let c64 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c1 c39
  let c65 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c1 c64
  let c66 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 82), (certNat% 77), 2252349569499136]
  let c67 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c66 c65
  let c68 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 83), 2252349569499136, (certNat% 84), (certNat% 85)]
  let c69 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨92, by decide⟩ c68 c67
  let c70 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 86), 2252349569499136, (certNat% 85), (certNat% 87), (certNat% 81)]
  let c71 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c70 c69
  let c72 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c71 c63
  let c73 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c72 c62
  let c74 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 88), (certNat% 48), (certNat% 89), (certNat% 90), (certNat% 26), (certNat% 49)]
  let c75 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c74 c73
  let c76 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 91), (certNat% 92), 2261145662521344, (certNat% 93), (certNat% 94)]
  let c77 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 95), (certNat% 9), 1026820715040473088, (certNat% 96), (certNat% 4), (certNat% 97)]
  let c78 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c77 c76
  let c79 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 98), (certNat% 19), (certNat% 99), (certNat% 21), (certNat% 100)]
  let c80 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 101), 306244774661193728, 582741162721280, (certNat% 33), (certNat% 6)]
  let c81 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 102), (certNat% 103), 582741162721280, (certNat% 33), (certNat% 6)]
  let c82 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 104), (certNat% 105), 580542139465728, (certNat% 106), (certNat% 19)]
  let c83 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 107), (certNat% 108), (certNat% 25), (certNat% 109), (certNat% 15), (certNat% 110)]
  let c84 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨91, by decide⟩ c83 c82
  let c85 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c84 c81
  let c86 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c85 c80
  let c87 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c86 c79
  let c88 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c1 c0
  let c89 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c1 c88
  let c90 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c1 c89
  let c91 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c1 c90
  let c92 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 111), (certNat% 112), (certNat% 78), 9511602413006487552]
  let c93 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c92 c91
  let c94 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c1 c88
  let c95 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 113), 9223372036854775808, 281509336449024]
  let c96 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨92, by decide⟩ c95 c94
  let c97 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 114), (certNat% 112), 9511602413006487552, (certNat% 87)]
  let c98 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c97 c96
  let c99 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 115), (certNat% 74), (certNat% 42), 450359962737049600, 9223372036854775808]
  let c100 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c99 c98
  let c101 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c100 c93
  let c102 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 116), (certNat% 117), 450359962737049600, (certNat% 26), (certNat% 49), 9223934986808197120]
  let c103 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c102 c101
  let c104 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 118), 9655717601082343424, (certNat% 73), (certNat% 119), 594475150812905472, (certNat% 33)]
  let c105 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 120), (certNat% 100), (certNat% 53), (certNat% 121)]
  let c106 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 122), (certNat% 123), 450359962737049600, (certNat% 26), (certNat% 100)]
  let c107 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 124), (certNat% 125), (certNat% 126), (certNat% 121), 580542139465728, (certNat% 19)]
  let c108 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c107 c106
  let c109 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c108 c105
  let c110 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 127), 3377699720527872, 9223934986808197120, (certNat% 128), (certNat% 129)]
  let c111 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 130), (certNat% 131), 1026820715040473088, (certNat% 4), (certNat% 132)]
  let c112 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 133), (certNat% 123), 582741162721280, (certNat% 134), (certNat% 126), (certNat% 135)]
  let c113 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c112 c111
  let c114 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c113 c110
  let c115 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 136), (certNat% 137), 1026820715040473088, (certNat% 138), (certNat% 109), (certNat% 12), 1706442046308352]
  let c116 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c115 c114
  let c117 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c116 c114
  let c118 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨91, by decide⟩ c117 c109
  let c119 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c118 c104
  let c120 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c119 c103
  let c121 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c120 c87
  let c122 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c121 c78
  let c123 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c122 c75
  let c124 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c123 c57
  let c125 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c124 c38
  let c126 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c125 c37
  let c127 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c126 c36
  let c128 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c127 c35
  let c129 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c128 c32
  c129
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record007_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record007_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00067.record007

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00067.record008
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3383d1ac3b07ce8b3272b2a6ab1a8e93a698d68d8b6638ce4b8ae0fba1cc4f1727296a4e9c66394e479694e5356352d475634cd4b4ad1b78370f23a8da3c4e5334e334ccb3c2d8b52ccb8ad2b2ae1b46c3b61e2749ca785c970dd0f23c2f1703c168c61584e07b21686314a4590e4c5294550d44d0b41dc0d8330e1314d0b12c1b21c4705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db69b6db6da6da6d24da4da49249269249269249b49269a493692492249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 36), (facetIndex 55), (facetIndex 69), (facetIndex 71), (facetIndex 92)]))
 (.leaf ([(facetIndex 63), (facetIndex 68), (facetIndex 72), (facetIndex 74), (facetIndex 102)])))
 (.branch 3
 (.leaf ([(facetIndex 37), (facetIndex 43), (facetIndex 44), (facetIndex 56), (facetIndex 57)]))
 (.leaf ([(facetIndex 70), (facetIndex 75), (facetIndex 76), (facetIndex 83)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 61), (facetIndex 62)]))
 (.leaf ([(facetIndex 65), (facetIndex 73), (facetIndex 79), (facetIndex 80), (facetIndex 84)])))
 (.branch 7
 (.leaf ([(facetIndex 33), (facetIndex 48), (facetIndex 64), (facetIndex 66), (facetIndex 88)]))
 (.branch 8
 (.leaf ([(facetIndex 32), (facetIndex 35), (facetIndex 38), (facetIndex 42), (facetIndex 46), (facetIndex 54), (facetIndex 58), (facetIndex 60), (facetIndex 85)]))
 (.leaf ([(facetIndex 34), (facetIndex 41)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "10000000000000600753005500331510301065614470722070044460702278007207867z20;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 78), (facetIndex 82)]))
 (.leaf ([(facetIndex 103), (facetIndex 105)])))
 (.branch 3
 (.leaf ([(facetIndex 47), (facetIndex 53), (facetIndex 77)]))
 (.branch 4
 (.leaf ([(facetIndex 94), (facetIndex 95), (facetIndex 96)]))
 (.leaf ([(facetIndex 98), (facetIndex 100), (facetIndex 106)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 45), (facetIndex 67), (facetIndex 81)]))
 (.leaf ([(facetIndex 86), (facetIndex 89), (facetIndex 99)])))
 (.branch 8
 (.leaf ([(facetIndex 39), (facetIndex 40), (facetIndex 52), (facetIndex 59), (facetIndex 97)]))
 (.branch 9
 (.leaf ([(facetIndex 87), (facetIndex 90), (facetIndex 91), (facetIndex 101)]))
 (.leaf ([(facetIndex 93), (facetIndex 104)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "41910846473339088608600005000200000000050000000700000270000205000077z27;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1, 2, 3]
def grouped2_0002 : List Nat := [4]
def grouped2_0003 : List Nat := [4, 5]
def grouped2_0004 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0005 : List Nat := [5]
def grouped2_0006 : List Nat := [6]
def grouped2_0007 : List Nat := [6, 7, 8]
def grouped2_0008 : List Nat := [7]
def grouped2_0009 : List Nat := [7, 8]
def grouped2_0010 : List Nat := [8]
def grouped3_0011 : List Nat := [0]
def grouped3_0012 : List Nat := [0, 1]
def grouped3_0013 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0015 : List Nat := [1]
def grouped3_0016 : List Nat := [2]
def grouped3_0017 : List Nat := [2, 3, 4]
def grouped3_0018 : List Nat := [3]
def grouped3_0019 : List Nat := [3, 4]
def grouped3_0020 : List Nat := [4]
def grouped3_0021 : List Nat := [5]
def grouped3_0022 : List Nat := [5, 6]
def grouped3_0023 : List Nat := [5, 6, 7, 8, 9]
def grouped3_0024 : List Nat := [6]
def grouped3_0025 : List Nat := [7]
def grouped3_0026 : List Nat := [7, 8, 9]
def grouped3_0027 : List Nat := [8]
def grouped3_0028 : List Nat := [8, 9]
def grouped3_0029 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00067.record008" "{\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00067.record008" 90

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00067.record008" "{\"ridges\":[[10,385],[22,560],[23,416],[24,800],[34,266],[38,164],[40,550],[41,385],[41,386],[46,266],[50,386],[54,560],[58,386],[58,416],[59,674],[60,800],[61,385],[62,385],[70,560],[73,416],[76,560],[79,416],[80,800],[83,560],[84,416],[84,800],[87,294],[90,178],[91,550],[93,294],[97,170],[101,674],[104,396]],\"owners\":[[34,266,[94,96,97,98,99],[6,43,46,49,50,51,87,89]],[46,266,[89,96,99],[6,34,43,49,50,51,87,94,97,98]],[10,385,[23,67,73,79,81,84],[41,50,61,62]],[41,385,[23,79,81,84],[10,50,61,62,67,73]],[61,385,[23,67,73,79,84],[10,41,50,62,81]],[62,385,[23,67,73,79,81],[10,41,50,61,84]],[41,386,[97,99,101],[10,50,58,61,62,89,93]],[50,386,[93,101],[10,41,58,61,62,89,97,99]],[58,386,[89,99],[10,41,50,61,62,93,97,101]],[38,164,[103,104,105],[17,64,69,72,73,86,90,93]],[22,560,[91,95,100,106],[54,70,76,83]],[54,560,[106],[22,70,76,83,91,95,100]],[70,560,[95,100,106],[22,54,76,83,91]],[76,560,[91,100],[22,54,70,83,95,106]],[83,560,[91,95],[22,54,70,76,100,106]],[23,416,[93,97,101,104],[58,73,79,84]],[58,416,[104],[23,73,79,84,93,97,101]],[73,416,[97,101],[23,58,79,84,93,104]],[79,416,[93,101],[23,58,73,84,97,104]],[84,416,[93,97,104],[23,58,73,79,101]],[24,800,[98,100,101,106],[60,80,83,84]],[60,800,[106],[24,80,83,84,98,100,101]],[80,800,[100,101],[24,60,83,84,98,106]],[84,800,[98,100,106],[24,60,80,83,101]],[87,294,[39,93],[]],[93,294,[39,87],[]],[40,550,[91],[]],[91,550,[40],[]],[97,170,[45,86],[]],[90,178,[52],[]],[59,674,[101],[]],[101,674,[59],[]],[104,396,[67,89],[]]],\"edges\":[[38,[22,24,40,47,54,59,60,70,76,80,83,84,91,95,98,100,101,106]],[42,[10,23,41,50,58,61,62,67,73,79,81,84,89,93,97,99,101,104]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00067.record008" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00067.record008\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-10,-5],[-10,-8],[-11,-5],[-11,-8],[-13,-10],[-13,-11],[-18,-7],[-20,-7],[-20,-12],[-21,-5],[-21,-8],[-21,-13],[-24,-5],[-24,-8],[-24,-12],[-24,-13],[-26,-12],[-27,-7],[-27,-12],[-30,-6],[-30,-7],[-30,-17],[-30,-28],[-30,-29],[-36,-6],[-36,-17],[-36,-28],[-36,-29],[-39,-10],[-39,-11],[-39,-21],[-39,-24],[-42,-30],[-42,-36],[-43,-6],[-43,-17],[-43,-28],[-43,-29],[-43,-42],[-46,-5],[-46,-8],[-46,-12],[-46,-13],[-46,-39],[-50,-5],[-50,-6],[-50,-8],[-50,-9],[-50,-13],[-50,-15],[-50,-17],[-50,-22],[-50,-25],[-50,-28],[-50,-29],[-50,-39],[-50,-42],[-52,-6],[-52,-17],[-52,-18],[-52,-28],[-52,-29],[-52,-42],[-7,47,49,50,51,52],[-15,43,49,52],[-1,3,30,32,34,36,38],[-12,3,34,36,38],[-26,3,30,32,34,38],[-27,3,30,32,34,36],[-12,50,52,54],[-19,46,54],[-23,43,52],[-9,55,56,57],[-2,45,48,53,58],[-22,58],[-31,48,53,58],[-33,45,53],[-37,45,48],[-3,46,50,54,56],[-23,56],[-32,50,54],[-34,46,54],[-38,46,50,56],[-4,51,53,54,58],[-25,58],[-35,53,54],[-38,51,53,58],[-41,10,46],[-46,10,41],[-11,45],[-45,11],[-50,14,40],[-44,21],[-24,54],[-54,24],[-56,30,43],[-59,18,19,20,26,27],[-60,6,17,28,29,42],[-61,5,8,9,13,15,22,23,25,39],[-62,7,12],[-63,59],[-64,61,62],[-65,61],[-65,62],[-66,60,65],[-67,60],[-66,64],[-68,63,67],[-68,66],[-69,68],[69],[-55,70],[-57,70],[-16,71],[-47,72],[-48,72],[-49,72],[-51,73],[-53,73],[-58,73],[-14,74],[-30,74],[-40,75],[-43,75],[-52,75],[-76,10,11,21,24,50],[-10,76],[-11,76],[-21,76],[-24,76],[-77,41,44,45,54],[-41,77],[-45,77],[-54,77],[-78,46,56],[-46,78],[-56,78],[-70,79],[-73,80],[-72,80],[-80,81],[-71,81],[-81,82],[-79,82],[-75,83],[-74,83],[-84,77,78],[-78,84],[-77,84],[-85,78],[-77,-78,85],[-84,86],[-87,76,85],[-85,87],[-76,-84,87],[-87,88],[-83,-86,88],[-83,-87,89],[-89,90],[-82,-88,90],[-90],[2,4,11,16,22,24,25,31,33,35,37,38,45,48,51,53,54,58],[1,3,12,19,23,26,27,30,32,34,36,38,43,46,50,52,54,56]],\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":39,\"b\":32},{\"tag\":\"incompatible\",\"a\":39,\"b\":35},{\"tag\":\"incompatible\",\"a\":40,\"b\":32},{\"tag\":\"incompatible\",\"a\":40,\"b\":35},{\"tag\":\"incompatible\",\"a\":42,\"b\":39},{\"tag\":\"incompatible\",\"a\":42,\"b\":40},{\"tag\":\"incompatible\",\"a\":49,\"b\":34},{\"tag\":\"incompatible\",\"a\":51,\"b\":34},{\"tag\":\"incompatible\",\"a\":51,\"b\":41},{\"tag\":\"incompatible\",\"a\":52,\"b\":32},{\"tag\":\"incompatible\",\"a\":52,\"b\":35},{\"tag\":\"incompatible\",\"a\":52,\"b\":42},{\"tag\":\"incompatible\",\"a\":59,\"b\":32},{\"tag\":\"incompatible\",\"a\":59,\"b\":35},{\"tag\":\"incompatible\",\"a\":59,\"b\":41},{\"tag\":\"incompatible\",\"a\":59,\"b\":42},{\"tag\":\"incompatible\",\"a\":61,\"b\":41},{\"tag\":\"incompatible\",\"a\":62,\"b\":34},{\"tag\":\"incompatible\",\"a\":62,\"b\":41},{\"tag\":\"incompatible\",\"a\":67,\"b\":33},{\"tag\":\"incompatible\",\"a\":67,\"b\":34},{\"tag\":\"incompatible\",\"a\":67,\"b\":48},{\"tag\":\"incompatible\",\"a\":67,\"b\":64},{\"tag\":\"incompatible\",\"a\":67,\"b\":66},{\"tag\":\"incompatible\",\"a\":81,\"b\":33},{\"tag\":\"incompatible\",\"a\":81,\"b\":48},{\"tag\":\"incompatible\",\"a\":81,\"b\":64},{\"tag\":\"incompatible\",\"a\":81,\"b\":66},{\"tag\":\"incompatible\",\"a\":85,\"b\":39},{\"tag\":\"incompatible\",\"a\":85,\"b\":40},{\"tag\":\"incompatible\",\"a\":85,\"b\":52},{\"tag\":\"incompatible\",\"a\":85,\"b\":59},{\"tag\":\"incompatible\",\"a\":88,\"b\":67},{\"tag\":\"incompatible\",\"a\":88,\"b\":81},{\"tag\":\"incompatible\",\"a\":89,\"b\":33},{\"tag\":\"incompatible\",\"a\":89,\"b\":48},{\"tag\":\"incompatible\",\"a\":89,\"b\":64},{\"tag\":\"incompatible\",\"a\":89,\"b\":66},{\"tag\":\"incompatible\",\"a\":89,\"b\":88},{\"tag\":\"incompatible\",\"a\":93,\"b\":32},{\"tag\":\"incompatible\",\"a\":93,\"b\":35},{\"tag\":\"incompatible\",\"a\":93,\"b\":41},{\"tag\":\"incompatible\",\"a\":93,\"b\":42},{\"tag\":\"incompatible\",\"a\":93,\"b\":85},{\"tag\":\"incompatible\",\"a\":97,\"b\":32},{\"tag\":\"incompatible\",\"a\":97,\"b\":33},{\"tag\":\"incompatible\",\"a\":97,\"b\":35},{\"tag\":\"incompatible\",\"a\":97,\"b\":38},{\"tag\":\"incompatible\",\"a\":97,\"b\":42},{\"tag\":\"incompatible\",\"a\":97,\"b\":46},{\"tag\":\"incompatible\",\"a\":97,\"b\":48},{\"tag\":\"incompatible\",\"a\":97,\"b\":54},{\"tag\":\"incompatible\",\"a\":97,\"b\":60},{\"tag\":\"incompatible\",\"a\":97,\"b\":64},{\"tag\":\"incompatible\",\"a\":97,\"b\":66},{\"tag\":\"incompatible\",\"a\":97,\"b\":85},{\"tag\":\"incompatible\",\"a\":97,\"b\":88},{\"tag\":\"incompatible\",\"a\":99,\"b\":33},{\"tag\":\"incompatible\",\"a\":99,\"b\":48},{\"tag\":\"incompatible\",\"a\":99,\"b\":49},{\"tag\":\"incompatible\",\"a\":99,\"b\":64},{\"tag\":\"incompatible\",\"a\":99,\"b\":66},{\"tag\":\"incompatible\",\"a\":99,\"b\":88},{\"tag\":\"mate\",\"ridge\":266,\"a\":34,\"owners\":[94,96,97,98,99]},{\"tag\":\"mate\",\"ridge\":266,\"a\":46,\"owners\":[89,96,99]},{\"tag\":\"mate\",\"ridge\":385,\"a\":10,\"owners\":[23,67,73,79,81,84]},{\"tag\":\"mate\",\"ridge\":385,\"a\":41,\"owners\":[23,79,81,84]},{\"tag\":\"mate\",\"ridge\":385,\"a\":61,\"owners\":[23,67,73,79,84]},{\"tag\":\"mate\",\"ridge\":385,\"a\":62,\"owners\":[23,67,73,79,81]},{\"tag\":\"mate\",\"ridge\":386,\"a\":41,\"owners\":[97,99,101]},{\"tag\":\"mate\",\"ridge\":386,\"a\":50,\"owners\":[93,101]},{\"tag\":\"mate\",\"ridge\":386,\"a\":58,\"owners\":[89,99]},{\"tag\":\"mate\",\"ridge\":164,\"a\":38,\"owners\":[103,104,105]},{\"tag\":\"mate\",\"ridge\":560,\"a\":22,\"owners\":[91,95,100,106]},{\"tag\":\"mate\",\"ridge\":560,\"a\":54,\"owners\":[106]},{\"tag\":\"mate\",\"ridge\":560,\"a\":70,\"owners\":[95,100,106]},{\"tag\":\"mate\",\"ridge\":560,\"a\":76,\"owners\":[91,100]},{\"tag\":\"mate\",\"ridge\":560,\"a\":83,\"owners\":[91,95]},{\"tag\":\"mate\",\"ridge\":416,\"a\":23,\"owners\":[93,97,101,104]},{\"tag\":\"mate\",\"ridge\":416,\"a\":58,\"owners\":[104]},{\"tag\":\"mate\",\"ridge\":416,\"a\":73,\"owners\":[97,101]},{\"tag\":\"mate\",\"ridge\":416,\"a\":79,\"owners\":[93,101]},{\"tag\":\"mate\",\"ridge\":416,\"a\":84,\"owners\":[93,97,104]},{\"tag\":\"mate\",\"ridge\":800,\"a\":24,\"owners\":[98,100,101,106]},{\"tag\":\"mate\",\"ridge\":800,\"a\":60,\"owners\":[106]},{\"tag\":\"mate\",\"ridge\":800,\"a\":80,\"owners\":[100,101]},{\"tag\":\"mate\",\"ridge\":800,\"a\":84,\"owners\":[98,100,106]},{\"tag\":\"mate\",\"ridge\":294,\"a\":87,\"owners\":[39,93]},{\"tag\":\"mate\",\"ridge\":294,\"a\":93,\"owners\":[39,87]},{\"tag\":\"mate\",\"ridge\":550,\"a\":40,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":550,\"a\":91,\"owners\":[40]},{\"tag\":\"mate\",\"ridge\":170,\"a\":97,\"owners\":[45,86]},{\"tag\":\"mate\",\"ridge\":178,\"a\":90,\"owners\":[52]},{\"tag\":\"mate\",\"ridge\":674,\"a\":59,\"owners\":[101]},{\"tag\":\"mate\",\"ridge\":674,\"a\":101,\"owners\":[59]},{\"tag\":\"mate\",\"ridge\":396,\"a\":104,\"owners\":[67,89]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[49,50,51,61,62],\"full_literals\":[-59,18,19,20,26,27]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[33,48,64,66,88],\"full_literals\":[-60,6,17,28,29,42]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[32,35,38,42,46,54,58,60,85],\"full_literals\":[-61,5,8,9,13,15,22,23,25,39]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[34,41],\"full_literals\":[-62,7,12]},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-63,59,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-64,61,62],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-65,61,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-65,false,62],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-66,60,65],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-67,60,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-66,false,64],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-68,63,67],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-68,false,66],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-69,false,68],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":103,\"full_literals\":[-55,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":105,\"full_literals\":[-57,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":47,\"full_literals\":[-16,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":94,\"full_literals\":[-47,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":95,\"full_literals\":[-48,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":96,\"full_literals\":[-49,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":98,\"full_literals\":[-51,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":100,\"full_literals\":[-53,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":106,\"full_literals\":[-58,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":45,\"full_literals\":[-14,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":67,\"full_literals\":[-30,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":86,\"full_literals\":[-40,75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":89,\"full_literals\":[-43,75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":99,\"full_literals\":[-52,75]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[39,40,52,59,97],\"full_literals\":[-76,10,11,21,24,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":39,\"full_literals\":[-10,76]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":40,\"full_literals\":[-11,76]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":52,\"full_literals\":[-21,76]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":59,\"full_literals\":[-24,76]},{\"tag\":\"group_or\",\"kind\":3,\"index\":8,\"members\":[87,90,91,101],\"full_literals\":[-77,41,44,45,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":87,\"full_literals\":[-41,77]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":91,\"full_literals\":[-45,77]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":101,\"full_literals\":[-54,77]},{\"tag\":\"group_or\",\"kind\":3,\"index\":9,\"members\":[93,104],\"full_literals\":[-78,46,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":93,\"full_literals\":[-46,78]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":104,\"full_literals\":[-56,78]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-70,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-73,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-72,false,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-80,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-71,false,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-81,82],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-79,false,82],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-75,83],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-74,false,83],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-84,77,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-78,84],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-77,false,84],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-85,false,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-77,-78,85],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-84,86],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-87,76,85],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-85,87],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-76,-84,87],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-87,88],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-83,-86,88],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-83,-87,89],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-89,90],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-82,-88,90],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":38,\"owners\":[22,24,40,47,54,59,60,70,76,80,83,84,91,95,98,100,101,106]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[10,23,41,50,58,61,62,67,73,79,81,84,89,93,97,99,101,104]}]}"
  "164 68 0 111 110 0\n165 66 0 164 109 0\n166 64 0 165 107 0\n167 -89 0 161 159 0\n168 -46 9 7 23 15 58 0 166 85 75 40 41 42 43 44 99 100 102 0\n169 -5 -76 50 0 1 3 10 13 126 0\n170 -8 -76 50 0 2 4 11 14 126 0\n171 -13 -76 50 0 5 6 12 16 126 0\n172 -39 -76 50 0 29 30 31 32 126 0\n173 -87 82 0 167 166 143 141 139 120 85 75 140 117 115 118 144 138 113 112 158 145 146 123 124 125 121 122 92 96 65 72 64 73 168 135 150 153 169 170 171 172 99 102 100 15 70 95 0\n174 77 81 0 141 139 120 119 140 116 76 85 75 118 87 142 114 133 134 90 77 74 78 94 86 84 162 0\n175 82 0 143 173 154 174 149 151 155 136 127 128 129 130 88 91 93 95 131 0\n176 -88 0 175 161 160 0\n177 -87 0 176 156 0\n178 -85 0 177 154 0\n179 -77 76 45 54 0 178 129 93 127 151 131 136 88 0\n180 -84 45 54 0 177 176 152 155 157 127 145 146 124 122 96 179 132 147 89 135 0\n181 36 27 52 3 12 19 23 26 32 34 56 30 43 46 50 38 54 0 163 66 0\n182 -36 -60 0 25 26 27 28 34 98 0\n183 -52 -60 0 58 59 61 62 63 98 0\n184 50 38 30 52 36 43 78 54 0 137 80 136 82 71 81 79 70 68 69 181 0\n185 -50 -60 0 46 51 54 55 57 98 0\n186 -60 36 43 78 54 0 137 136 183 185 83 184 20 22 23 24 33 98 0\n187 -50 -61 23 22 25 0 45 47 48 49 50 56 99 0\n188 -7 3 38 32 -59 34 19 0 7 8 18 21 97 68 0\n189 60 78 54 22 25 0 165 164 137 80 136 82 71 105 106 103 104 108 187 101 81 83 79 188 100 9 17 19 70 97 60 0\n190 36 -60 54 78 0 186 35 36 37 38 39 98 0\n191 78 54 25 22 0 189 182 190 0\n192 54 22 25 0 178 191 148 151 180 133 0\n193 -54 0 177 95 134 130 149 155 0\n194 -84 0 177 193 155 180 128 91 0\n195 -78 0 194 148 0\n196 -46 0 195 136 0\n197 -56 0 195 137 0\n198 -19 0 196 193 71 0\n199 -34 0 196 193 82 0\n200 36 50 0 196 197 195 193 165 164 198 199 79 83 81 190 67 105 106 104 108 100 101 188 0\n201 50 0 197 196 165 164 199 193 198 81 83 79 200 182 105 106 104 108 101 188 100 9 17 19 70 97 60 0\n202 -22 0 201 52 0\n203 -25 0 201 53 0\n204 0 202 203 193 192 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record008_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00067.record008

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00067.record001
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3386b0ec4f3a2ccb2a6a8eac6a3a4e8e635a36338ae1b83ee85d1cc5c9ca5a93a719566394e5a539595356354d58d3352d2b46d4743de0f23a8da338f1364e5334e334cf0b62ccb8ad2b2ac6b86d1b0ee2719e1725c3723c5c168c6298561382e07b21687114a519164c5294551342d074c388ca384c5312c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6db6db6934924d349a4d24d36d249269249a49b692492492491249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record001 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record001 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record001.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record001.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record001.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 35), (facetIndex 37), (facetIndex 51), (facetIndex 69), (facetIndex 89)]))
 (.leaf ([(facetIndex 40), (facetIndex 41), (facetIndex 61), (facetIndex 75), (facetIndex 76)])))
 (.branch 3
 (.leaf ([(facetIndex 36), (facetIndex 50), (facetIndex 52), (facetIndex 54)]))
 (.leaf ([(facetIndex 64), (facetIndex 72), (facetIndex 78), (facetIndex 79), (facetIndex 83)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 34), (facetIndex 39), (facetIndex 60), (facetIndex 73), (facetIndex 81), (facetIndex 84)]))
 (.leaf ([(facetIndex 33), (facetIndex 42), (facetIndex 55), (facetIndex 62), (facetIndex 71), (facetIndex 85), (facetIndex 90)])))
 (.branch 7
 (.leaf ([(facetIndex 38), (facetIndex 43), (facetIndex 44), (facetIndex 45), (facetIndex 56), (facetIndex 57), (facetIndex 58)]))
 (.leaf ([(facetIndex 46), (facetIndex 63), (facetIndex 65), (facetIndex 86), (facetIndex 87)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "140fec6206c1223a0003bf4c1b6a820801f6d49982128z18;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 53), (facetIndex 70), (facetIndex 82)]))
 (.leaf ([(facetIndex 47), (facetIndex 66), (facetIndex 77), (facetIndex 80)])))
 (.branch 3
 (.leaf ([(facetIndex 94), (facetIndex 95), (facetIndex 101)]))
 (.leaf ([(facetIndex 100)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 49), (facetIndex 67), (facetIndex 68), (facetIndex 74)]))
 (.leaf ([(facetIndex 88), (facetIndex 91), (facetIndex 92), (facetIndex 99)])))
 (.branch 7
 (.leaf ([(facetIndex 48), (facetIndex 59), (facetIndex 97)]))
 (.branch 8
 (.leaf ([(facetIndex 93), (facetIndex 98)]))
 (.leaf ([(facetIndex 96), (facetIndex 102)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "82357682275500500000001001004000004410000006000000000461z2f;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [2, 3]
def grouped2_0007 : List Nat := [3]
def grouped2_0008 : List Nat := [4]
def grouped2_0009 : List Nat := [4, 5]
def grouped2_0010 : List Nat := [4, 5, 6, 7]
def grouped2_0011 : List Nat := [5]
def grouped2_0012 : List Nat := [6]
def grouped2_0013 : List Nat := [6, 7]
def grouped2_0014 : List Nat := [7]
def grouped3_0015 : List Nat := [0]
def grouped3_0016 : List Nat := [0, 1]
def grouped3_0017 : List Nat := [0, 1, 2, 3]
def grouped3_0019 : List Nat := [1]
def grouped3_0020 : List Nat := [2]
def grouped3_0021 : List Nat := [2, 3]
def grouped3_0022 : List Nat := [3]
def grouped3_0023 : List Nat := [4]
def grouped3_0024 : List Nat := [4, 5]
def grouped3_0025 : List Nat := [4, 5, 6, 7, 8]
def grouped3_0026 : List Nat := [5]
def grouped3_0027 : List Nat := [6]
def grouped3_0028 : List Nat := [6, 7, 8]
def grouped3_0029 : List Nat := [7]
def grouped3_0030 : List Nat := [7, 8]
def grouped3_0031 : List Nat := [8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record001 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record001_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00067.record001" "{\"atoms\":[{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0030\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00067.record001" 72

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00067.record001" "{\"ridges\":[[21,296],[23,385],[23,416],[40,280],[41,530],[44,296],[47,394],[53,402],[56,385],[56,416],[59,385],[59,898],[64,296],[70,404],[72,385],[72,416],[73,296],[75,265],[76,280],[78,296],[78,385],[78,416],[79,296],[80,456],[82,464],[83,416],[97,306],[98,800],[98,898],[101,396],[102,568]],\"owners\":[[41,530,[88,97],[9,36,50,52,54,92,93]],[75,265,[21,44,47,48,64,66,78,79],[20,40,61,76,80]],[40,280,[99,102],[20,61,73,75,76,91,93]],[76,280,[91,99],[20,40,61,73,75,93,102]],[21,296,[91,95,96,99,101,102],[44,64,73,78,79]],[44,296,[99,101,102],[21,64,73,78,79,91,95,96]],[64,296,[91,95,96,102],[21,44,73,78,79,99,101]],[73,296,[95,96,101],[21,44,64,78,79,91,99,102]],[78,296,[91,96,99,102],[21,44,64,73,79,95,101]],[79,296,[91,95,99,101],[21,44,64,73,78,96,102]],[23,385,[47,53,59,66,70,80,82],[56,72,78,83]],[56,385,[66,70,80,82],[23,47,53,59,72,78,83]],[59,385,[23,66,70,72,78,80,82],[47,53,56,83]],[72,385,[47,53,59,80,82],[23,56,66,70,78,83]],[78,385,[53,59,70,82],[23,47,56,66,72,80,83]],[23,416,[95,98,101],[56,72,78,83]],[56,416,[101],[23,72,78,83,95,98]],[72,416,[95,98],[23,56,78,83,101]],[78,416,[98],[23,56,72,83,95,101]],[83,416,[95,101],[23,56,72,78,98]],[98,800,[24,79,81,102],[58,83,96,97]],[47,394,[95],[]],[97,306,[49,91],[]],[53,402,[],[]],[59,898,[98],[]],[98,898,[59],[]],[101,396,[66],[]],[70,404,[],[]],[102,568,[74,92],[]],[80,456,[],[]],[82,464,[],[]]],\"edges\":[[42,[23,47,53,56,59,66,70,72,78,80,82,83,95,98,101]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00067.record001" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00067.record001\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-15,-11],[-21,-9],[-21,-18],[-21,-20],[-23,-17],[-28,-3],[-29,-2],[-29,-28],[-31,-28],[-35,-21],[-36,-21],[-38,-15],[-40,-9],[-40,-18],[-40,-20],[-40,-35],[-40,-36],[-41,-15],[-43,-41],[-46,-4],[-46,-5],[-46,-16],[-46,-24],[-46,-31],[-46,-34],[-7,37,42],[-26,1,8,10,11,19,21,28,29],[-6,44,46],[-27,38,44],[-1,38,40,41,44,45,46],[-8,44,45,46],[-19,38,40,41,46],[-24,40,41,45],[-28,38,41,44,46],[-29,38,40,44,45],[-2,10,13,15,21,22,30,32],[-14,21,22,30,32],[-15,2,21,22,23,28,30,32],[-23,10,13,15,30,32],[-28,13,15,22,32],[-2,40,43,45],[-14,45],[-23,40,43],[-28,43],[-33,40,45],[-43,3,29,31,46],[-10,40],[-42,12,38],[-13],[-15,43],[-43,15],[-45,21],[-22],[-46,25,39],[-30],[-32],[-47,6,7,17,26,27],[-48,19,23,28,29,33],[-49,4,5,16,24,31,34],[-50,9,18,20,35,36],[-51,47],[-52,48],[-53,51],[-53,52],[-54,49],[-55,50],[-56,54],[-56,55],[-57,53],[-57,56],[57],[-10,58],[-21,58],[-40,59],[-45,59],[-12,60],[-25,60],[-37,61],[-38,61],[-39,61],[-44,61],[-15,62],[-43,63],[-58,64],[-59,65],[-65,66],[-64,66],[-61,67],[-60,67],[-63,68],[-62,-68,69],[-69,70],[-67,-69,71],[-71,72],[-66,-70,72],[-72],[2,10,13,14,15,21,22,23,28,30,32,33,40,43,45]],\"atoms\":[{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":59,\"b\":48},{\"tag\":\"incompatible\",\"a\":66,\"b\":46},{\"tag\":\"incompatible\",\"a\":66,\"b\":63},{\"tag\":\"incompatible\",\"a\":66,\"b\":65},{\"tag\":\"incompatible\",\"a\":72,\"b\":61},{\"tag\":\"incompatible\",\"a\":78,\"b\":24},{\"tag\":\"incompatible\",\"a\":79,\"b\":23},{\"tag\":\"incompatible\",\"a\":79,\"b\":78},{\"tag\":\"incompatible\",\"a\":81,\"b\":78},{\"tag\":\"incompatible\",\"a\":86,\"b\":66},{\"tag\":\"incompatible\",\"a\":87,\"b\":66},{\"tag\":\"incompatible\",\"a\":91,\"b\":59},{\"tag\":\"incompatible\",\"a\":95,\"b\":46},{\"tag\":\"incompatible\",\"a\":95,\"b\":63},{\"tag\":\"incompatible\",\"a\":95,\"b\":65},{\"tag\":\"incompatible\",\"a\":95,\"b\":86},{\"tag\":\"incompatible\",\"a\":95,\"b\":87},{\"tag\":\"incompatible\",\"a\":96,\"b\":59},{\"tag\":\"incompatible\",\"a\":98,\"b\":96},{\"tag\":\"incompatible\",\"a\":102,\"b\":34},{\"tag\":\"incompatible\",\"a\":102,\"b\":39},{\"tag\":\"incompatible\",\"a\":102,\"b\":60},{\"tag\":\"incompatible\",\"a\":102,\"b\":73},{\"tag\":\"incompatible\",\"a\":102,\"b\":81},{\"tag\":\"incompatible\",\"a\":102,\"b\":84},{\"tag\":\"mate\",\"ridge\":530,\"a\":41,\"owners\":[88,97]},{\"tag\":\"mate\",\"ridge\":265,\"a\":75,\"owners\":[21,44,47,48,64,66,78,79]},{\"tag\":\"mate\",\"ridge\":280,\"a\":40,\"owners\":[99,102]},{\"tag\":\"mate\",\"ridge\":280,\"a\":76,\"owners\":[91,99]},{\"tag\":\"mate\",\"ridge\":296,\"a\":21,\"owners\":[91,95,96,99,101,102]},{\"tag\":\"mate\",\"ridge\":296,\"a\":44,\"owners\":[99,101,102]},{\"tag\":\"mate\",\"ridge\":296,\"a\":64,\"owners\":[91,95,96,102]},{\"tag\":\"mate\",\"ridge\":296,\"a\":73,\"owners\":[95,96,101]},{\"tag\":\"mate\",\"ridge\":296,\"a\":78,\"owners\":[91,96,99,102]},{\"tag\":\"mate\",\"ridge\":296,\"a\":79,\"owners\":[91,95,99,101]},{\"tag\":\"mate\",\"ridge\":385,\"a\":23,\"owners\":[47,53,59,66,70,80,82]},{\"tag\":\"mate\",\"ridge\":385,\"a\":56,\"owners\":[66,70,80,82]},{\"tag\":\"mate\",\"ridge\":385,\"a\":59,\"owners\":[23,66,70,72,78,80,82]},{\"tag\":\"mate\",\"ridge\":385,\"a\":72,\"owners\":[47,53,59,80,82]},{\"tag\":\"mate\",\"ridge\":385,\"a\":78,\"owners\":[53,59,70,82]},{\"tag\":\"mate\",\"ridge\":416,\"a\":23,\"owners\":[95,98,101]},{\"tag\":\"mate\",\"ridge\":416,\"a\":56,\"owners\":[101]},{\"tag\":\"mate\",\"ridge\":416,\"a\":72,\"owners\":[95,98]},{\"tag\":\"mate\",\"ridge\":416,\"a\":78,\"owners\":[98]},{\"tag\":\"mate\",\"ridge\":416,\"a\":83,\"owners\":[95,101]},{\"tag\":\"mate\",\"ridge\":800,\"a\":98,\"owners\":[24,79,81,102]},{\"tag\":\"mate\",\"ridge\":394,\"a\":47,\"owners\":[95]},{\"tag\":\"mate\",\"ridge\":306,\"a\":97,\"owners\":[49,91]},{\"tag\":\"mate\",\"ridge\":402,\"a\":53,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":898,\"a\":59,\"owners\":[98]},{\"tag\":\"mate\",\"ridge\":898,\"a\":98,\"owners\":[59]},{\"tag\":\"mate\",\"ridge\":396,\"a\":101,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":404,\"a\":70,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":568,\"a\":102,\"owners\":[74,92]},{\"tag\":\"mate\",\"ridge\":456,\"a\":80,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":464,\"a\":82,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[40,41,61,75,76],\"full_literals\":[-47,6,7,17,26,27]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[64,72,78,79,83],\"full_literals\":[-48,19,23,28,29,33]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[34,39,60,73,81,84],\"full_literals\":[-49,4,5,16,24,31,34]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[46,63,65,86,87],\"full_literals\":[-50,9,18,20,35,36]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-51,false,47],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-52,false,48],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-53,51,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-53,false,52],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-54,49,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-55,false,50],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-56,54,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-56,false,55],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-57,53,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-57,false,56],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":47,\"full_literals\":[-10,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":66,\"full_literals\":[-21,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":95,\"full_literals\":[-40,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":101,\"full_literals\":[-45,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":49,\"full_literals\":[-12,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":74,\"full_literals\":[-25,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":88,\"full_literals\":[-37,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":91,\"full_literals\":[-38,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":92,\"full_literals\":[-39,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":99,\"full_literals\":[-44,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":59,\"full_literals\":[-15,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":98,\"full_literals\":[-43,63]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-58,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-59,false,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-65,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-64,false,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-61,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-60,false,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0029\",\"right_name\":\"grouped3_0031\",\"joined_name\":\"grouped3_0030\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-63,false,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-62,-68,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-69,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-67,-69,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-71,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-66,-70,72],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":42,\"owners\":[23,47,53,56,59,66,70,72,78,80,82,83,95,98,101]}]}"
  "98 53 0 71 69 0\n99 56 0 71 70 0\n100 51 0 98 63 0\n101 52 0 98 64 0\n102 54 0 99 67 0\n103 55 0 99 68 0\n104 47 0 100 61 0\n105 48 0 101 62 0\n106 49 0 102 65 0\n107 50 0 103 66 0\n108 -71 0 96 94 0\n109 2 10 14 15 21 23 28 33 40 43 45 0 49 53 55 56 97 0\n110 -41 66 0 56 55 53 49 86 85 74 75 45 42 87 84 73 72 18 19 40 39 36 109 0\n111 67 66 0 105 56 55 49 104 110 86 85 74 75 45 87 84 73 72 88 89 78 79 80 81 76 77 29 48 54 35 26 28 31 32 34 30 58 5 39 57 1 27 0\n112 -23 66 0 108 56 55 49 111 93 87 84 72 86 85 74 39 43 82 83 91 90 0\n113 -15 28 46 66 0 56 55 53 105 112 110 86 85 74 75 45 87 84 73 12 38 32 7 58 0\n114 28 46 66 0 56 55 53 49 112 86 85 74 75 45 42 87 84 73 72 113 51 36 109 0\n115 46 66 0 114 6 8 9 44 46 0\n116 66 0 106 86 85 74 75 110 33 115 20 21 22 24 25 59 0\n117 -70 0 116 96 95 0\n118 -69 0 117 92 0\n119 -46 0 106 20 21 22 23 24 25 59 0\n120 -28 0 119 6 8 9 44 46 0\n121 -43 0 118 51 83 82 90 91 0\n122 -15 0 121 50 0\n123 -21 0 107 2 3 4 10 11 60 0\n124 -14 0 123 53 55 56 37 0\n125 -45 0 123 52 0\n126 -40 0 107 13 14 15 16 17 60 0\n127 -10 0 126 47 0\n128 -23 0 126 121 43 0\n129 -33 0 126 125 45 0\n130 -2 0 126 125 121 41 0\n131 0 130 128 124 127 122 123 120 129 126 121 125 109 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record001.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record001.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record001.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record001.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record001 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record001.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record001.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record001.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record001.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record001 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record001_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record001 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record001_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00067.record001_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00067.record001
