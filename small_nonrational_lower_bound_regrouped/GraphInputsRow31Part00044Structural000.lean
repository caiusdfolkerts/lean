module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow31Part00044Data
public import GraphInputsRow31Part00044Frames
public import GraphInputsRow31Part00044Leaves
public import GraphInputsRow31Part00044Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00044.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00044.record006
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨99, by decide⟩, ⟨102, by decide⟩, ⟨110, by decide⟩, ⟨111, by decide⟩, ⟨112, by decide⟩, ⟨115, by decide⟩, ⟨116, by decide⟩, ⟨117, by decide⟩, ⟨121, by decide⟩, ⟨122, by decide⟩, ⟨125, by decide⟩, ⟨126, by decide⟩, ⟨127, by decide⟩, ⟨131, by decide⟩, ⟨132, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), (certNat% 5), 68582037782528, 280912026757234688]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), (certNat% 7), (certNat% 8), (certNat% 9), 61984968015872, 253890428993011712]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), (certNat% 11), (certNat% 12), 273091200548864, 1118581557448146944]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), (certNat% 14), (certNat% 15), 34153579937792, (certNat% 16)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), (certNat% 18), (certNat% 19), (certNat% 20), (certNat% 21)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), (certNat% 23), (certNat% 24), 237631950553088, (certNat% 25), (certNat% 26)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨116, by decide⟩ c5 c3
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c6 c4
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨121, by decide⟩ c7 c3
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 27), (certNat% 16), (certNat% 15), 139893063425196032, (certNat% 14)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 28), (certNat% 29), (certNat% 30), (certNat% 31), (certNat% 32)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 33), (certNat% 34), 972777519512027136, (certNat% 35), (certNat% 25), (certNat% 36)]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨127, by decide⟩ c11 c9
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c12 c10
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨131, by decide⟩ c13 c9
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 37), (certNat% 38), 97581656965120, (certNat% 39), (certNat% 40)]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 41), (certNat% 42), 115173843009536, (certNat% 39), (certNat% 43)]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 44), 291045125918818304, (certNat% 45), (certNat% 46), (certNat% 47)]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 48), (certNat% 49), 88785563942912, (certNat% 39), (certNat% 40)]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 50), 327073922937782272, (certNat% 51), (certNat% 52), (certNat% 18)]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 53), 105553116266496, 324822123124097024, (certNat% 43)]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 54), (certNat% 55), 123145302310912, 324822123124097024, (certNat% 56)]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c21 c20
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 57), (certNat% 58), 125344325566464, 1152927002164985856, (certNat% 59)]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 60), (certNat% 49), 326510972984360960, (certNat% 61), (certNat% 55)]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 62), 123145302310912, 324259173170675712, (certNat% 43), (certNat% 38)]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 63), 326510972984360960, 1152929269907718144, 106102872080384, (certNat% 43)]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 64), (certNat% 49), 1184728176975151104, 326510972984360960, (certNat% 55)]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 65), 123695058124800, (certNat% 66), (certNat% 55), 326510972984360960]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 67), 290553094465388544, 60541859004416, (certNat% 66), (certNat% 68), 36028797018963968]
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c29 c28
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c30 c27
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c31 c26
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨112, by decide⟩ c32 c25
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c33 c24
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c34 c23
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨122, by decide⟩ c35 c22
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c36 c19
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨96, by decide⟩ c37 c18
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c38 c17
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c39 c16
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c40 c15
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 69), (certNat% 70), (certNat% 19), (certNat% 20)]
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 71), (certNat% 49), (certNat% 66), (certNat% 55)]
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 72), (certNat% 73), (certNat% 15), (certNat% 74), (certNat% 75)]
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨110, by decide⟩ c44 c43
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨127, by decide⟩ c45 c42
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 76), (certNat% 38), (certNat% 77), (certNat% 20), (certNat% 78)]
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 79), (certNat% 18), (certNat% 30), (certNat% 31), (certNat% 80)]
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 81), (certNat% 82), 220452081369088, (certNat% 15), (certNat% 83), (certNat% 84)]
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c49 c48
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨115, by decide⟩ c50 c47
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c51 c46
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 85), (certNat% 86), (certNat% 87), (certNat% 88)]
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 89), (certNat% 70), (certNat% 15)]
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 90), (certNat% 91), (certNat% 92), (certNat% 15), (certNat% 70)]
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨131, by decide⟩ c55 c54
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨110, by decide⟩ c56 c53
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 93), (certNat% 94), 903534675241205760, (certNat% 15), (certNat% 95), (certNat% 96)]
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c58 c57
  let c60 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 97), 615304299089494016, 185267709280256, (certNat% 39), (certNat% 43)]
  let c61 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 98), (certNat% 99), 194063802302464, (certNat% 39), (certNat% 45)]
  let c62 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 100), 167675523235840, 651333096108457984, (certNat% 46), (certNat% 55)]
  let c63 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 101), (certNat% 102), 193514046488576, 649081296294772736]
  let c64 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 103), (certNat% 99), 649081296294772736, (certNat% 40), 202310139510784]
  let c65 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨94, by decide⟩ c64 c63
  let c66 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 104), (certNat% 58), 206708186021888, 1152924803141730304, (certNat% 105)]
  let c67 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 106), (certNat% 107), (certNat% 42), (certNat% 66)]
  let c68 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 108), 648518346341351424, 61572651155456, (certNat% 40), (certNat% 42)]
  let c69 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c68 c67
  let c70 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 109), 650770146155036672, (certNat% 102), 1184728176975151104, (certNat% 99)]
  let c71 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 110), 650770146155036672, 1152929269907718144, 194063802302464, (certNat% 102)]
  let c72 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 111), (certNat% 40), (certNat% 99), 194063802302464, 650770146155036672]
  let c73 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 112), 578853839361277952, (certNat% 83), (certNat% 113), 52776558133248, 72057594037927936]
  let c74 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c73 c72
  let c75 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨94, by decide⟩ c74 c71
  let c76 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c75 c70
  let c77 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨112, by decide⟩ c76 c69
  let c78 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c77 c66
  let c79 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨122, by decide⟩ c78 c65
  let c80 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c79 c62
  let c81 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c80 c61
  let c82 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c81 c60
  let c83 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 114), (certNat% 115), (certNat% 15), (certNat% 116), 272678883688448, (certNat% 117)]
  let c84 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨127, by decide⟩ c44 c42
  let c85 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 118), 902971725287784448, (certNat% 119), (certNat% 15), (certNat% 120), (certNat% 121)]
  let c86 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c85 c84
  let c87 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 122), (certNat% 123), (certNat% 124), (certNat% 125)]
  let c88 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 126), (certNat% 127), (certNat% 43), (certNat% 42), (certNat% 128)]
  let c89 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨131, by decide⟩ c88 c87
  let c90 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 129), (certNat% 38), (certNat% 130), 36037624250499072, 72057594037927936]
  let c91 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 131), 936748722493063168, (certNat% 45), (certNat% 47), (certNat% 132)]
  let c92 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 133), 108086421121662976, (certNat% 56), (certNat% 134), (certNat% 135), (certNat% 5)]
  let c93 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c92 c91
  let c94 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨121, by decide⟩ c93 c90
  let c95 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c94 c89
  let c96 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 136), (certNat% 137), (certNat% 138), 220452081369088, (certNat% 139), (certNat% 140)]
  let c97 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 141), (certNat% 38), (certNat% 135), 36037624250499072, 17592186044416]
  let c98 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 142), 228698418577408, (certNat% 45), (certNat% 47), (certNat% 143)]
  let c99 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 144), 26418343837696, (certNat% 56), (certNat% 134), (certNat% 130), (certNat% 3)]
  let c100 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c99 c98
  let c101 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨131, by decide⟩ c100 c97
  let c102 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 145), (certNat% 146), (certNat% 9), (certNat% 127), (certNat% 147), (certNat% 148)]
  let c103 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 149), 36028822788767744, (certNat% 40), (certNat% 38), 228698418577408]
  let c104 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 150), 36028822788767744, (certNat% 151), (certNat% 152), 228698418577408]
  let c105 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 153), 36028822788767744, (certNat% 56), (certNat% 134)]
  let c106 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 154), 36028822788767744, 228698418577408, (certNat% 59), (certNat% 155)]
  let c107 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 156), 17617955848192, 902971725287784448, (certNat% 56), (certNat% 134), (certNat% 3)]
  let c108 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨126, by decide⟩ c107 c106
  let c109 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c108 c105
  let c110 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨127, by decide⟩ c109 c104
  let c111 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨131, by decide⟩ c110 c103
  let c112 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 157), (certNat% 47), (certNat% 158), 229248174391296, (certNat% 140), (certNat% 159)]
  let c113 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 160), (certNat% 161), (certNat% 11), 228698418577408, (certNat% 5)]
  let c114 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 162), (certNat% 161), (certNat% 12), (certNat% 3), 864691128455135232]
  let c115 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 163), (certNat% 164), (certNat% 165), (certNat% 166)]
  let c116 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 167), 228698418577408, (certNat% 168), (certNat% 169), (certNat% 170), (certNat% 171)]
  let c117 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 172), 17606144688128, 290693282197929984, (certNat% 173), (certNat% 140), (certNat% 121)]
  let c118 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 174), (certNat% 175), (certNat% 43), (certNat% 176), (certNat% 140), (certNat% 148)]
  let c119 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 177), (certNat% 178), (certNat% 179), (certNat% 164), (certNat% 165), (certNat% 143), (certNat% 128)]
  let c120 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c119 c118
  let c121 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c120 c117
  let c122 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨131, by decide⟩ c121 c116
  let c123 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c122 c115
  let c124 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c123 c114
  let c125 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c124 c113
  let c126 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c125 c112
  let c127 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c126 c111
  let c128 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c127 c102
  let c129 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨112, by decide⟩ c128 c101
  let c130 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c129 c96
  let c131 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨122, by decide⟩ c130 c95
  let c132 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c131 c86
  let c133 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c132 c83
  let c134 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨110, by decide⟩ c133 c82
  let c135 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c134 c59
  let c136 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c135 c52
  let c137 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨111, by decide⟩ c136 c41
  let c138 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c137 c14
  let c139 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c138 c8
  let c140 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c139 c2
  let c141 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c140 c2
  let c142 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c141 c1
  let c143 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c142 c0
  c143
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00044.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00044.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00044.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00044.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00044.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00044.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00044.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00044.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00044.record006_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00044.record006
