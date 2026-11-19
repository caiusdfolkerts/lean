module
prelude
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
def vertexColumn : Fields := ⟨10, hexnat% "3a8ce2b8e9334ad38ccb2ac6b16c3b31ca725c8f13c2f07ce29aa5a8eac6a9a9693a2e87ae19a6598e6c5a96959362d876c3a8e63a4e538ce4b8ae1ba1e4789e1783ee25a95a4e9c66994e4b9e15a5594e5c56954d4b5c368d6354d3352d2b46d8751d2745d0f78368d6338f13a4d332cc73c2e8b62d4b32d2b2ac6b86d1b26c3bc1e8761d4731d2729c6785d1725c3783d0f23c4f0bc1f1e074c2a8a8685ac1a86858561c5292a46916439494a5194550d45342c8b12c1b41c8711c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db6db6db6da4db4936936d24da49b6db69b4da49b49a49b49b6da49b6936db6da492492492492492492692689249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨99, by decide⟩, ⟨102, by decide⟩, ⟨110, by decide⟩, ⟨111, by decide⟩, ⟨112, by decide⟩, ⟨115, by decide⟩, ⟨116, by decide⟩, ⟨117, by decide⟩, ⟨121, by decide⟩, ⟨122, by decide⟩, ⟨125, by decide⟩, ⟨126, by decide⟩, ⟨127, by decide⟩, ⟨131, by decide⟩, ⟨132, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100009c049cdcc1c601010019740000000", hexnat% "2300000000000000000c00000000000", hexnat% "24000000000000000009000000000000", hexnat% "8c0000000000000000c00000000000000", 68582037782528, 280912026757234688]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "102008c049cdcc1c601001001740000000", hexnat% "4010000000000000070070000000000", hexnat% "2300000000000000000c08000000000", hexnat% "8c0000000000000000c08000000000000", 61984968015872, 253890428993011712]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100401c049cdcc1c601071071740000000", hexnat% "2380000000000000000008000000000", hexnat% "8e0000000000000000008000000000000", 273091200548864, 1118581557448146944]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8e238c0410d0c1c200fffe0e740000000", hexnat% "c00000000000000000000000", hexnat% "1004010008000000401000000000000000", 34153579937792, hexnat% "c000000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8a220000109cc1c200ffffff740000000", hexnat% "c40000000000000000000000", hexnat% "90008000000000000000000000000", hexnat% "1004000000000000401000000000000000", hexnat% "4010c040000000000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a2300001cc081c200fff204740000000", hexnat% "80048000000000000008000000000", hexnat% "84000c000000000000000000000000000", 237631950553088, hexnat% "1004010000000000401000000000000000", hexnat% "1c400000000071000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨116, by decide⟩ c5 c3
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c6 c4
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨121, by decide⟩ c7 c3
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8e238c0410d0c1c200e0efff740000000", hexnat% "c000000000000000000000", hexnat% "1004010008000000401000000000000000", 139893063425196032, hexnat% "c00000000000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "84218000105cc1c200ffffff740000000", hexnat% "c80000000000000000000000", hexnat% "24000008000000000000000000000000", hexnat% "1000010000000000401000000000000000", hexnat% "8020c040000000000000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8c018000005cc1c200206fff740000000", hexnat% "20000048000000000008000000000000", 972777519512027136, hexnat% "220c000000000000000000000000000", hexnat% "1004010000000000401000000000000000", hexnat% "1c80000000071000000000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨127, by decide⟩ c11 c9
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c12 c10
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨131, by decide⟩ c13 c9
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18e238c04901001c600fffa02740000000", hexnat% "cc0000000000000000000000", 97581656965120, hexnat% "4010000000000001000071000000000", hexnat% "cc00000000000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18e238c04880801c600fff902740000000", hexnat% "14c0000000000000000000000", 115173843009536, hexnat% "4010000000000001000071000000000", hexnat% "14c00000000000000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18e238c04840401c600b84fff740000000", 291045125918818304, hexnat% "18c00000000000000000000", hexnat% "4010000000000001071000000000000", hexnat% "18c0000000000000000000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18c230c049cd001c600fffa82740000000", hexnat% "20080000000000000000000000000000", 88785563942912, hexnat% "4010000000000001000071000000000", hexnat% "cc00000000000000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18c238c04909cc1c600b04fff740000000", 327073922937782272, hexnat% "24000000000000000001000000000000", hexnat% "10000000000001070000000000000", hexnat% "c40000000000000000000000"]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18e639c049cc801c601b7d9ff740000000", 105553116266496, 324822123124097024, hexnat% "14c00000000000000000000"]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18e639c04980001c601b7d8ff740000000", hexnat% "4c0000000000000000000000", 123145302310912, 324822123124097024, hexnat% "1cc00000000000000000000"]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c21 c20
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18e630c049cc041c600fff886740000000", hexnat% "90000000000000000009000000000", 125344325566464, 1152927002164985856, hexnat% "1c800000000000000000000"]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18c630c04981cc1c600b06fff740000000", hexnat% "20080000000000000000000000000000", 326510972984360960, hexnat% "10000000000001071000000000000", hexnat% "4c0000000000000000000000"]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18e639c04900801c601b7f8ff740000000", 123145302310912, 324259173170675712, hexnat% "14c00000000000000000000", hexnat% "cc0000000000000000000000"]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18e639c049cc801c600b77986740000000", 326510972984360960, 1152929269907718144, 106102872080384, hexnat% "14c00000000000000000000"]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18c631c04981cc1c600b06fff740000000", hexnat% "20080000000000000000000000000000", 1184728176975151104, 326510972984360960, hexnat% "4c0000000000000000000000"]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18e639c04981801c601b778f7740000000", 123695058124800, hexnat% "4c00000000000000000000", hexnat% "4c0000000000000000000000", 326510972984360960]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18e639c04981801c601b06886740000000", 290553094465388544, 60541859004416, hexnat% "4c00000000000000000000", hexnat% "4c0000000071000000000000", 36028797018963968]
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
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8e220c041c9c81c200ffffff740000000", hexnat% "100000040400000000000000000000", hexnat% "90008000000000000000000000000", hexnat% "1004000000000000401000000000000000"]
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18c631c04981801c601ffffff740000000", hexnat% "20080000000000000000000000000000", hexnat% "4c00000000000000000000", hexnat% "4c0000000000000000000000"]
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "88200c001c1c01c200ffffff740000000", hexnat% "200000080800000000000000000000", hexnat% "1004010008000000401000000000000000", hexnat% "40100000040400000000000000000000", hexnat% "20080040000000000000000000000000"]
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨110, by decide⟩ c44 c43
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨127, by decide⟩ c45 c42
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "82239804901001c200ffff8f740000000", hexnat% "cc0000000000000000000000", hexnat% "c0004000000000000000000000000000", hexnat% "1004000000000000401000000000000000", hexnat% "cc00000000070000000000"]
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "88228800109cc1c200ffffff740000000", hexnat% "c40000000000000000000000", hexnat% "24000008000000000000000000000000", hexnat% "1000010000000000401000000000000000", hexnat% "40104040000000000000000000000000"]
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "802088001cd001c200fff306740000000", hexnat% "e0000040000000000000000000000000", 220452081369088, hexnat% "1004010008000000401000000000000000", hexnat% "cc00000000071000000000", hexnat% "304000000000000000000000000000"]
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c49 c48
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨115, by decide⟩ c50 c47
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c51 c46
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18e638c04888881c600ffffff740000000", hexnat% "10000000000001000000000000000", hexnat% "14400000000000000000000", hexnat% "1440000000000000000000000"]
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8e228c041c9c81c200ffffff740000000", hexnat% "100000040400000000000000000000", hexnat% "1004010008000000401000000000000000"]
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "88028c000c8c81c200ffffff740000000", hexnat% "2000001010000000000000000000000", hexnat% "60000040000000000000000000000000", hexnat% "1004010008000000401000000000000000", hexnat% "100000040400000000000000000000"]
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨131, by decide⟩ c55 c54
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨110, by decide⟩ c56 c53
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8028800009cc1c200304fff740000000", hexnat% "2104040000000000000000000000000", 903534675241205760, hexnat% "1004010008000000401000000000000000", hexnat% "1c40000000071000000000000", hexnat% "860000000000000000000000000000000"]
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c58 c57
  let c60 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18e238c049cc801c600775506740000000", 615304299089494016, 185267709280256, hexnat% "4010000000000001000071000000000", hexnat% "14c00000000000000000000"]
  let c61 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18e238c048c0401c600fff486740000000", hexnat% "10c0000000000000000000000", 194063802302464, hexnat% "4010000000000001000071000000000", hexnat% "18c00000000000000000000"]
  let c62 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18e238c04981cc1c600684677740000000", 167675523235840, 651333096108457984, hexnat% "4010000000000001071000000000000", hexnat% "4c0000000000000000000000"]
  let c63 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18e639c049cd401c6016fd4ff740000000", hexnat% "8c00000000000000000000", 193514046488576, 649081296294772736]
  let c64 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18e639c048c1001c6016fd47f740000000", hexnat% "10c0000000000000000000000", 649081296294772736, hexnat% "cc00000000000000000000", 202310139510784]
  let c65 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨94, by decide⟩ c64 c63
  let c66 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18e630c049cd041c600fff406740000000", hexnat% "90000000000000000009000000000", 206708186021888, 1152924803141730304, hexnat% "c800000000000000000000"]
  let c67 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18e639c04881001c601efffff740000000", hexnat% "8000000100000000000000", hexnat% "14c0000000000000000000000", hexnat% "4c00000000000000000000"]
  let c68 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18e639c04881001c6016ffc7f740000000", 648518346341351424, 61572651155456, hexnat% "cc00000000000000000000", hexnat% "14c0000000000000000000000"]
  let c69 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c68 c67
  let c70 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18e639c048c1401c600686fff740000000", 650770146155036672, hexnat% "8c00000000000000000000", 1184728176975151104, hexnat% "10c0000000000000000000000"]
  let c71 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18e639c049cd401c6006f7486740000000", 650770146155036672, 1152929269907718144, 194063802302464, hexnat% "8c00000000000000000000"]
  let c72 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18e639c048c1001c6016f74f7740000000", hexnat% "cc00000000000000000000", hexnat% "10c0000000000000000000000", 194063802302464, 650770146155036672]
  let c73 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18e639c048c1001c601686486740000000", 578853839361277952, hexnat% "cc00000000071000000000", hexnat% "10c0000000071000000000000", 52776558133248, 72057594037927936]
  let c74 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c73 c72
  let c75 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨94, by decide⟩ c74 c71
  let c76 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c75 c70
  let c77 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨112, by decide⟩ c76 c69
  let c78 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c77 c66
  let c79 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨122, by decide⟩ c78 c65
  let c80 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c79 c62
  let c81 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c80 c61
  let c82 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c81 c60
  let c83 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6010c001cc041c200fff006740000000", hexnat% "880000040000000000000000000000000", hexnat% "1004010008000000401000000000000000", hexnat% "2280000000000000000008000000000", 272678883688448, hexnat% "1c800000000071000000000"]
  let c84 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨127, by decide⟩ c44 c42
  let c85 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80200c00101cc1c200306fff740000000", 902971725287784448, hexnat% "380040000000000000000000000000", hexnat% "1004010008000000401000000000000000", hexnat% "cc0000000071000000000000", hexnat% "e0000000000000000000000000000000"]
  let c86 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c85 c84
  let c87 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18e601c049c1c01c601ffffff740000000", hexnat% "380000000000000000000000000000", hexnat% "c00000000000000000000", hexnat% "c0000000000000000000000"]
  let c88 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "182401c00880801c601ffffff740000000", hexnat% "2380040000000000000000000000000", hexnat% "14c00000000000000000000", hexnat% "14c0000000000000000000000", hexnat% "c0000000000000000000000000000000"]
  let c89 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨131, by decide⟩ c88 c87
  let c90 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "182639c04901cc1c60127ff7f000000000", hexnat% "cc0000000000000000000000", hexnat% "c0000000000000000c00000000000000", 36037624250499072, 72057594037927936]
  let c91 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "102639c04840401c6012fffff740000000", 936748722493063168, hexnat% "18c00000000000000000000", hexnat% "18c0000000000000000000000", hexnat% "8c0000000000000000000000000000000"]
  let c92 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "102609c04800001c60127f3ff040000000", 108086421121662976, hexnat% "1cc00000000000000000000", hexnat% "1cc0000000000000000000000", hexnat% "300000000000000000c00000000000", hexnat% "8c0000000000000000c00000000000000"]
  let c93 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c92 c91
  let c94 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨121, by decide⟩ c93 c90
  let c95 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c94 c89
  let c96 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400c001cc801c200fff306740000000", hexnat% "1000010008000000401000000000000000", hexnat% "8e0000040000000000000000000000000", 220452081369088, hexnat% "14c00000000071000000000", hexnat% "2380000000000000000000000000000"]
  let c97 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18e609c04901cc1c601f7f27f000000000", hexnat% "cc0000000000000000000000", hexnat% "300000000000000000c00000000000", 36037624250499072, 17592186044416]
  let c98 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18e409c04840401c601fff2ff740000000", 228698418577408, hexnat% "18c00000000000000000000", hexnat% "18c0000000000000000000000", hexnat% "2300000000000000000000000000000"]
  let c99 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "182409c04800001c6013ff27f040000000", 26418343837696, hexnat% "1cc00000000000000000000", hexnat% "1cc0000000000000000000000", hexnat% "c0000000000000000c00000000000000", hexnat% "2300000000000000000c00000000000"]
  let c100 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c99 c98
  let c101 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨131, by decide⟩ c100 c97
  let c102 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "401c00041cc1c200386fff740000000", hexnat% "1000000008000000401000000000000000", hexnat% "8c0000000000000000c08000000000000", hexnat% "2380040000000000000000000000000", hexnat% "18c0000000071000000000000", hexnat% "20000000000000000000000000000000"]
  let c103 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18e639c04901001c601f7f2ff140000000", 36028822788767744, hexnat% "cc00000000000000000000", hexnat% "cc0000000000000000000000", 228698418577408]
  let c104 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18e639c04808081c601f7f2ff140000000", 36028822788767744, hexnat% "1c400000000000000000000", hexnat% "1c40000000000000000000000", 228698418577408]
  let c105 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18e639c04800001c601f7ffff140000000", 36028822788767744, hexnat% "1cc00000000000000000000", hexnat% "1cc0000000000000000000000"]
  let c106 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18e639c04804041c601f7f2ff140000000", 36028822788767744, 228698418577408, hexnat% "1c800000000000000000000", hexnat% "1c80000000000000000000000"]
  let c107 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18e409c04800001c6013772ff140000000", 17617955848192, 902971725287784448, hexnat% "1cc00000000000000000000", hexnat% "1cc0000000000000000000000", hexnat% "2300000000000000000c00000000000"]
  let c108 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨126, by decide⟩ c107 c106
  let c109 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c108 c105
  let c110 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨127, by decide⟩ c109 c104
  let c111 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨131, by decide⟩ c110 c103
  let c112 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100401c04840401c601fff286740000000", hexnat% "18c0000000000000000000000", hexnat% "8e0000000000000000000000000000000", 229248174391296, hexnat% "2380000000000000000000000000000", hexnat% "18c00000000071000000000"]
  let c113 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2401c001cdcc1c6013ff2f7040000000", hexnat% "1000000048000000000000000700000000", hexnat% "2380000000000000000008000000000", 228698418577408, hexnat% "8c0000000000000000c00000000000000"]
  let c114 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "409c001cdcc1c6013f73ff040000000", hexnat% "1000000048000000000000000700000000", hexnat% "8e0000000000000000008000000000000", hexnat% "2300000000000000000c00000000000", 864691128455135232]
  let c115 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8e639c04800001c201f8ff8f040000000", hexnat% "1000000000000000400000000700000000", hexnat% "1cc00000000070000000000", hexnat% "1cc0000000070000000000000"]
  let c116 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8e639c04101001c201f8f28f000000000", 228698418577408, hexnat% "1000000008000000400000000740000000", hexnat% "404000000000000000000000", hexnat% "8c00000000070000000000", hexnat% "8c0000000070000000000000"]
  let c117 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80401c001cdcc1c201bf72ff400000000", 17606144688128, 290693282197929984, hexnat% "1000000048000000400000000000000000", hexnat% "2380000000000000000000000000000", hexnat% "e0000000000000000000000000000000"]
  let c118 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "180401c04880801c6013c7fff740000000", hexnat% "c0000000000000000c08000000000000", hexnat% "14c00000000000000000000", hexnat% "14c0000000030000000000000", hexnat% "2380000000000000000000000000000", hexnat% "20000000000000000000000000000000"]
  let c119 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80401c00000001c201fcff8f000000000", hexnat% "1cc0000000030000000000000", hexnat% "20080048000000000000000040000000", hexnat% "1000000000000000400000000700000000", hexnat% "1cc00000000070000000000", hexnat% "2300000000000000000000000000000", hexnat% "c0000000000000000000000000000000"]
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
