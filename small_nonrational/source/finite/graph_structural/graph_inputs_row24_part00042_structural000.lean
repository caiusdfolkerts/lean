module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00042Data
public import GraphInputsRow24Part00042Frames
public import GraphInputsRow24Part00042Leaves
public import GraphInputsRow24Part00042Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00042.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record002
def vertexColumn : Fields := ⟨10, hexnat% "f0ba2d8a6a5a95a4eac671aa669a6659996559361b89e1783ef07a1d86695a5594e6c5716a56966559595555351b49d1743de0f43b0dc3c8ea368e6358e9354d3392d4b8ad2b1ad1b26c5b0ee8761e4751cc789d2729c6745c570dc8f648961382e079912544d0b41da0d8390d4388d2344c9312c2b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6db6db69b4926db6db6db69b492492492492492492492492492489249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨66, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨86, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400004073fcf3dfc000000", 17293822569102704640, hexnat% "f00000000000000000000", 594475425690812416, 36082131922845696]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800008edcf87ffc000000", hexnat% "4000040000020000000000", 8070450532247928832, hexnat% "700000000000000000000", 6047313952768, 81909218222800896]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4600046406c77ffc000000", hexnat% "100001001008000000000", hexnat% "800008018080000000000", 774619135907725312, 81082385478713344, 35184372088832]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4100041daf76ab78000000", 16140901064562966528, hexnat% "e00000000000000000000", 362924736512, 150633093005312, 166633186212708352]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "450004508536fffc000000", hexnat% "200002002010000000000", hexnat% "800008018080000000000", 891712726219358208, 216383888346316800]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40000401ff3eaffc000000", 17293822569102704640, hexnat% "f00000000000000000000", 720576215257186304, 288442650615349248]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4000040fff026dfc000000", 8873402433536, 17293822569102704640, hexnat% "f00000000000000000000", 94008244174848, 175921860444160]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800008ffffffffc000000", hexnat% "4000040000000000000000", 8070450532247928832, hexnat% "700000000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "900009d99ff9b5c000000", hexnat% "200002002000000000000", 145241517479428096, hexnat% "44000000020000000", hexnat% "4400000000000000000000", 27021599911706624]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800008ffffc7b78000000", hexnat% "4000040000020000000000", 19394461696, 1649267441664, 8070450532247928832, hexnat% "700000000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [17872825432487755776, hexnat% "4000040004022020000000", hexnat% "f00000000000000000000", 94008244174848, 166809108073152512, 405886916416765952, 371514671104]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c12 c9
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c13 c6
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c14 c5
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c15 c4
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c16 c3
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c17 c2
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c18 c1
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c19 c0
  c20
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00042.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00042.record019
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record019
def vertexColumn : Fields := ⟨10, hexnat% "3c2aca6a4eac671aa699996558b66394e1b91e0fbc1ac6694e6c5716a599595554b56354d1b51d0f783d0ec370ea398e9354e334ccb362e4b8ad2b1ad1b0ee8761e4751cc789ca719d1715d0f23c1f6494a258361382e64549254351342da0d8390d4388d1324c3342c4b0ac8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db69a6934db6db69a693492492492492492492492492249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨80, by decide⟩, ⟨82, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "68006a24fe6e70000000", 38843551081037824, hexnat% "400040011008000000000", 360289138420744192, hexnat% "100010040000000000000", 2147483648]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "508050c5f2f8f90000000", 158331285012480, hexnat% "40004000402000000000", 225180256246431744, hexnat% "20002000000000000000", 36028865738440704]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "128012c77bffff0000000", 182466153652682752, 72057594037927936, hexnat% "440044000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "28002c119ffff0000000", hexnat% "440044000000000000000", hexnat% "100010040000000000000", 1724034232352768, 182466153652682752, 81064793292668928]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "128012a6f7ffff0000000", 328903510286401536, 72057594037927936, hexnat% "440044000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000107fffffff0000000", 2882303761517117440, hexnat% "440044000000000000000", hexnat% "28000000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10001034f7bfff0000000", hexnat% "8000800040000000000", 6917529027641081856, hexnat% "440040000000000000000", hexnat% "20000020000000000000", 328903510286401536]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c8 c6
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c9 c5
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5000505f78995b0000000", hexnat% "40004000402040000000", 55009941127168, 146367262767448064, hexnat% "20002000000200000000", hexnat% "8000800040000000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100012ff56bfff0000000", hexnat% "440044000000000000000", hexnat% "28000000000000000000", 2977477488017408]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "128050fd14ffff0000000", 2314850208468434944, 2973079441506304, hexnat% "440004000000000000000", 1161084278931456]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1080107d149fff0000000", hexnat% "20002020000000000000", 2977477488017408, 576462951326679040, hexnat% "440044000000000000000", 1161084278931456]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c15 c12
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "28002ebb9eb3f0000000", hexnat% "50000000000000000", hexnat% "500000000000000000000", hexnat% "40004000400000000000", 90073401296683008, 1161101458800640]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "600063f97c72f0000000", 288372762907508736, hexnat% "400040000000100000000", 1691083243257856, hexnat% "100010000000400000000", hexnat% "8000800000000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200020314c12a0000000", hexnat% "100010040000400000000", hexnat% "8000800020810000000", hexnat% "44004400000a140000000", 1741626418397184, 470766898548572160, 72058968427462656]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c20 c17
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c21 c16
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c22 c11
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c23 c10
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c24 c4
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c25 c1
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c26 c0
  c27
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record019_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record019_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record019_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record019_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record019_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record019_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record019_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record019_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record019_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00042.record019

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00042.record023
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record023
def vertexColumn : Fields := ⟨10, hexnat% "7319c5713cb29caaaa6a6695ab19c6a9a66659566394e338ae1b91e2785e0fbc1b25c9aa669665594e6c5716a599595555356354d3352d2b46d4749d1743db0dc3a8e6364d538ce8b62e4b52ccb8acab1ad1b26c5ba1d8791d4731e2729c6745c9715d0f23c4f0bc1f0e83662549464396154545435a0e4388c3322c4b0ac1b21c4709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6db6db6db6db6d369b4934da4926db4da4d26d24924924924924924d2489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨59, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨71, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨78, by decide⟩, ⟨81, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000309b39ef3dbc00000", 105604655874048, hexnat% "2040000000000000000", hexnat% "980000000020000000", hexnat% "4c000000010000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [50665399234068480, hexnat% "200030900000000000000", hexnat% "4e000000000000000000", 96502546432, hexnat% "9c0000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "408000b3ffeb03c00000", hexnat% "e000800000000000000", hexnat% "200030100000000000000", hexnat% "40000000038000000", 89120571392, hexnat% "180000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [50487649730822144, hexnat% "200030900000000000000", hexnat% "9c0000000000000000", 177846005792768, hexnat% "4e000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a1000b3ffe153c00000", hexnat% "200030900000000000000", hexnat% "c0000000028000000", hexnat% "44000000000000000000", 62277025792, hexnat% "800000001000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "408000b35cbffbc00000", hexnat% "1c0800000000000000", hexnat% "200030100000000000000", 179495273234432, hexnat% "e000000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "24e9f0900949243c00000", 36301600456704, 50111346242486272, 174348828672, 354317622050816]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "49f080054fffbc00000", hexnat% "200000102000000000000", 49829866970808320, hexnat% "4a000000010000000000", 178120883699712]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "24e9f090034864bc00000", 141906256330752, 50111346242486272, 174214610944, 354317622050816]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20003010214824ac00000", hexnat% "9c0800000020000000", hexnat% "4e000000010000000000", 49539771994734592, 363113715073024, 176007759790080, 2432696320]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c11 c6
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c12 c5
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c13 c4
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c14 c3
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c15 c2
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c16 c1
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c17 c0
  c18
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record023_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record023_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record023_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record023_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record023_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record023_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record023_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record023_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00042.record023_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00042.record023
