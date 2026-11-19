module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00116Data
public import GraphInputsRow24Part00116Frames
public import GraphInputsRow24Part00116Leaves
public import GraphInputsRow24Part00116Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00116.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00116.record000
def vertexColumn : Fields := ⟨10, hexnat% "6d0ea96a3a1e9a64d98e338ae8785e0f9d16c4f1b24e9966391e5a5654d54d4b5634cd8745d0f5c368ce3c4d538cd331cd8b32e2b2ac6b86c5b0ed8731d2729e1715e0f43c8f13c1f2b252929160d82e94649324a9614a5454352342d90e1344c530ce0b12c2b41c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b4db4da6d36d24da4d249b4db4924d249249a492492249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨55, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨73, by decide⟩, ⟨76, by decide⟩, ⟨79, by decide⟩, ⟨83, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "300400bf93f0000000", hexnat% "802080080000000000000", hexnat% "10000000004800000000", 4222141830529024, hexnat% "19800000000000000", hexnat% "80002000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "103804803dc960000000", hexnat% "19800000000000000", hexnat% "802000000020010000000", 96636764160, hexnat% "80002001000000000000", 4081387162304512]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "300400280020000000", hexnat% "10000000004840000000", hexnat% "19800000000000000", hexnat% "802080080038010000000", hexnat% "80002001001600000000", 21996675006464, 4081387162304512]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00116.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00116.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00116.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00116.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00116.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00116.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00116.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00116.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00116.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00116.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00116.record004
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00116.record004
def vertexColumn : Fields := ⟨10, hexnat% "3d25cb48f26aa5a8e8ba719a639a56358b61da4e4ba1e1783eb44f16a599966392e5c5694e565655354b51d64d4b61d4745db0dc368ce3a4e5334e332cc73c2d8b92e2b4acab86c9b16c3b61e4751cc749ca719e1725c570de0f13c1f0f10e0ba51344b186439154354342d0758390cc328e0b42c2b41c4709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6db6db6d36926d24db6924d249249a4d34924936924924da492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffdcdf9fc3f9fc17d000000", hexnat% "200000080000200000000", hexnat% "2000000200002000000", 72128134580797440, hexnat% "30060000000000000000", 162129674632167424]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffff8f787e25bbffff000000", hexnat% "4000001a000000000000", 126175556357062656, hexnat% "10038000000000000000", hexnat% "20040000000000000000", hexnat% "800000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffdfe7e47ff23d47b000000", hexnat% "200002000080204000000", 178241142784, 10952754293765046272, hexnat% "1810000000000000000", 233096465088512]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffdecffc7ffdfffff000000", hexnat% "2000000200000000000", hexnat% "10000000000000000000", hexnat% "200002000000000000000", hexnat% "1001800000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffdffffde7f53defb000000", 184718020575232, hexnat% "200002080000000000000", 72057735771848704, 4398046511104]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffdef7ec63f63defb000000", 4035225266191073280, hexnat% "10810000000000000000", hexnat% "200000080080000000000", 90072134281330688, 162727720910848]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffff8c7860adffffff000000", 234187180623265792, hexnat% "40000012000000000000", hexnat% "1001c00000000000000", hexnat% "10818000000000000000", hexnat% "22060000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffffbcffffef4dffff000000", hexnat% "40000010020000000000", hexnat% "3000000000000000000", 193514046488576]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffffbffffcedffdaff000000", hexnat% "40000012000000000000", 72057752951717888, 144115188075855872]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffdffffdeff33d6ff000000", hexnat% "200002000080000000000", 72057770131587072, 215504279044096]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffffcfffcfd01c2ff000000", hexnat% "3000000020000000000", 216172902372868096, 567352294899712, 220039764508672, 52776558133248]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c13 c10
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c14 c9
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffdaf7fd7ff3ffffa000000", hexnat% "10800000000000000000", 211106299641856, 2882303761533894656, hexnat% "240000000000000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffd8efbc1ef5deffa000000", hexnat% "30040000000000000000", 148654040794791936, hexnat% "240002000000001000000", 142936578719744, hexnat% "1001c00000000000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c17 c16
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffdbfffddffdfffff000000", 144150372447944704, hexnat% "240002000000000000000"]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffdbffefdffddd3ff000000", hexnat% "10000002400000000", 37383395344384, 144115222435594240, hexnat% "240000000000000000000"]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffffcffcf1ffffc3ff000000", 864691128455135232, 144115308334940160, hexnat% "30020000000000000000", hexnat% "10000002000000000"]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffd9cffc1efdfc3fe000000", hexnat% "240002000000001000000", 188978561024, hexnat% "1001c00000000000000", 148654040794791936, hexnat% "22000000000000000000"]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c23 c22
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c24 c21
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffdbe7ec63dbfd776000000", hexnat% "1001800000001000000", hexnat% "240002000000000000000", 36641439744, 126171295749505024, hexnat% "810002000000000000"]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffddf78d3ffffffff000000", hexnat% "810000000000000000", hexnat% "200002000000000000000", 864691128455135232, hexnat% "20060000000000000000"]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffddf78d3ffffffff000000", hexnat% "200002000000000000000", 864691128455135232, hexnat% "810000000000000000", hexnat% "20060000000000000000"]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffdff7ffd7fbfe77f000000", hexnat% "800000400000000000", hexnat% "200000080000000000000", 144115293302554624]
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffdcf7afd7fbfc37f000000", hexnat% "200000080000000000000", hexnat% "800000400000000000", hexnat% "30040000000000000000", 144115310482423808, hexnat% "10000002000000000"]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c30 c29
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c31 c28
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c32 c27
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffffffff5ffefeffb000000", 17592253153280, 144115256795332608, 576460752303423488]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c35 c34
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffffcefff7ffefffff000000", hexnat% "1000000100000000000", 576460752303423488, hexnat% "30000000000000000000"]
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffdeefbe7ffeffffb000000", hexnat% "200000000000004000000", hexnat% "1000000100000000000", hexnat% "10040000000000000000", 1729382256910270464]
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c38 c37
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c39 c36
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffd8d7bc1edffeffb000000", 148618856422703104, hexnat% "10800002000000000000", hexnat% "240002000000000000000", 1729382256977379328, hexnat% "22040400000000000000"]
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c41 c40
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffdcdf9fc3f27ebfb000000", hexnat% "200000080080000000000", 228698485686272, hexnat% "30060000000000000000", hexnat% "2000000000000000000", 234187266522611712]
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffd8c78c02dffe37e000000", hexnat% "240002000000001000000", hexnat% "1001c00000000000000", hexnat% "10810002000000000000", hexnat% "22060010000000000000", 144115310482423808, 126100789566373888]
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c44 c43
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c45 c42
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c46 c33
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c47 c26
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c48 c25
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c49 c18
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c50 c15
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c51 c8
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c52 c7
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c53 c2
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c54 c1
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c55 c0
  c56
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00116.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00116.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00116.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00116.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00116.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00116.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00116.record004_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00116.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00116.record004_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00116.record004
