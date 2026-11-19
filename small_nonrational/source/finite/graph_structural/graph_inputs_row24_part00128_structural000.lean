module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00128Data
public import GraphInputsRow24Part00128Frames
public import GraphInputsRow24Part00128Leaves
public import GraphInputsRow24Part00128Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00128.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record003
def vertexColumn : Fields := ⟨10, hexnat% "2745b07cd8a728ea6659a568d8764b8ae0fb619c569566391e66559655356351d54d4b4ad1b45d0f743c8e6358e9394d538cc7362e2b2ae1b46c3b91d4789d2729c6785c570dd0f2712a268962382e07a61586514a499194951548d0b41d88d2384c9342c8b0ac1b21c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db6db49249b6924d34924d24934d24926d2492489249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ff3bff3c7c5c780000000", hexnat% "400028001000000000", 63772748152832, hexnat% "4000400000800000000", 4503737066323968, hexnat% "8000800000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffafa7efffff6c0000000", hexnat% "1040000000000000000", hexnat% "4000000000800000000", hexnat% "18100000100000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffff7edbd9dcc0000000", 41781441855488, 9007336693694464, 9295429643777605632, 1125899906842624]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ff8fa7ecfffd7c0000000", hexnat% "6000000000000000000", hexnat% "18100000000000000", 9007371053432832, hexnat% "1040010000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffefa7eedd9ffc0000000", 41781441855488, hexnat% "18100000000000000", hexnat% "1040010000000000000", 562949953421312]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffefa7ecdd9dc40000000", 41781441855488, hexnat% "1000030000000000000", hexnat% "10002000300000000", 9295429633040187392, hexnat% "40000002000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ff1787879fffcc0000000", hexnat% "e000000000000000000", 1688862745165824, 540431955284459520, hexnat% "18000000000000000", hexnat% "860000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ff87a7a79fffcc0000000", hexnat% "1840000000000000000", hexnat% "4000400000000000000", hexnat% "2000080000000000000", 1688862745165824, hexnat% "18100000000000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c13 c14
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ff7ff7fffd9fec0000000", hexnat% "8000000000000000000", 9223372041149743104, 41781441855488]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ff3ff7ffbd9fe80000000", 9223372041149743104, hexnat% "c000000000040000000", 41781441855488, 1125899906842624]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ff1ff7a79d9fe80000000", 41782515597312, 1688854155231232, 9331458427911667712, hexnat% "4000400000000000000", hexnat% "a000000000000000000"]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ff2b8fbe5ffffc0000000", hexnat% "4000400000000000000", hexnat% "10002000000000000", hexnat% "8020000000000000000", hexnat% "1440008000000000000", 4503599627370496]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [hexnat% "7fffffffffffffc0000000"]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ff2b9fff3c1f7c0000000", hexnat% "4000000080800000000", 59373627899904, 1125899906842624, hexnat% "1460008000000000000", hexnat% "8000000000000000000"]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c24 c23
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ff3bff9f3c1f380000000", hexnat% "400008000000000000", 1132496976609280, hexnat% "c000000080040000000", 52776558133248, 432345615767175168]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ff0b9f9e140f380000000", hexnat% "e000000000040000000", 69269232549888, hexnat% "1460200000000000000", 1829587348619264, 288230427691319296, 6755399441055744]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c27 c26
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c28 c25
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c29 c22
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c30 c21
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c31 c11
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c32 c10
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c33 c9
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c34 c0
  c35
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00128.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00128.record007
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record007
def vertexColumn : Fields := ⟨10, hexnat% "2745b0bcd8a725aa3a4ea6659a568d8765392e1b83ed86715a6394e4b999565956352d4755352d2b46dd0f2398d63a4e538cd331cd8b52e2b4ac6b86d1b0ee4751cc789d2719e1715c3743c4f0bc9c0f09a2588e07a61586314a4990e465254352342d0764350e1324d0b22c1b21c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "da6db6db6db69249249a49a4934924da4d349249b492491249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨88, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000451cce82a4f60000000", 426612659060736, hexnat% "1000010000000000000", 144116837343297536, hexnat% "28c0000000000000000", hexnat% "201000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100071c8ad8238920000000", 301721452544, 9020393394274304, 422214612549632, hexnat% "a01400000000000000", hexnat% "414000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000430dcc9264be0000000", 13519612155002880, hexnat% "800000800000000000", 144116837343297536, hexnat% "30c0000000000000000", hexnat% "410000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10002bddc80800960000000", hexnat% "1400008000000000000", 323258566049792, hexnat% "4000040000000000000", 144117120811139072, 13519612155002880]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100035ddc90000b20000000", 11270011364573184, hexnat% "a00000200000000000", hexnat% "4000040000000000000", 144117113294946304, 426612659060736]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fddec9a78de0000000", hexnat% "10004000000000000000000", 283467841536, 13519594975133696]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10005fddc88a385a0000000", 294669116243968, hexnat% "2000240000800000000", 284541583360, 13510798882111488]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000179dc88030520000000", 13519603565068288, hexnat% "4000040200800000000", hexnat% "2840000000000000000", 144116013783318528, 426612659060736]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2ad54c1ae01e0000000", hexnat% "10000108800000000000000", hexnat% "1400008000000000000", hexnat% "4000000000800000000", 144117120811139072, 13510816061980672]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000091cc80000120000000", hexnat% "30c0000000000000000", hexnat% "4000048220800000000", 426613732802560, 13519620744937472, hexnat% "601000000000000000", 144117112221204480]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c12 c9
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c13 c4
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c14 c3
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c15 c2
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c16 c1
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c17 c0
  c18
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record007_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record007_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00128.record007

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00128.record008
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record008
def vertexColumn : Fields := ⟨10, hexnat% "278d92749b16c9723c1f3629a96a8e8bad1b2699966a5a364da4e53a2e4b86e8783e9c5692e47999565956354d475534cd4b46d1743d98d638cd332cd4b4acab1ad8791d4789d2719e1745c3743c4f0bc9c8c89a0ea162588e079611a4990e5452548d1341d48c930cc8b0ac1b41c8705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db6db49b6d26db6d269269b6d26926924d249a69a492449249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨58, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1015437409458000000", hexnat% "40002000090000000000", hexnat% "2020000000180000000", 275414777856, hexnat% "80000000300000000000", 2199023255552]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [5780224455632486400, hexnat% "40002000000000000000", 345744867328, hexnat% "1010400000000000000", hexnat% "80020000000000000000", hexnat% "2000000000100000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1017417428458000000", 9007268511088640, hexnat% "2020000000180000000", 274877906944, hexnat% "40000000090000000000", hexnat% "80000000300000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [15483323547648000, 3458766163087982592, 4899986763323277312, hexnat% "3030000000140000000", hexnat% "c0000000280000000000", 362924736512, 17592320262144]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c5 c0
  c6
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record008_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00128.record008_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00128.record008
