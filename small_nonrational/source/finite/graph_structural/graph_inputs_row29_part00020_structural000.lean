module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00020Data
public import GraphInputsRow29Part00020Frames
public import GraphInputsRow29Part00020Leaves
public import GraphInputsRow29Part00020Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00020.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record001
def vertexColumn : Fields := ⟨10, hexnat% "3e0f4368ba358b6364d332c9b16c5713cb8acaaaa6a3a8da2e96639956359362d86e0fbc1e8791d46d1745b1d26c9ca6a9c669996559365392e745c9555355352d70d9354d8b52d4745d0f6c3a8d5334d332ce8b92ccb8acab26c5b0ed4731d2729d1725c570dc4f5505c3485a1584e0b81ec86a18a5254542d074a324c2b06c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6db6d36db69b6936934db6db49b6db6d269b6d24934d34db4924da492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨86, by decide⟩, ⟨93, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40080c0202088e98800000", hexnat% "60000000000000400000", hexnat% "200000000020103000000", 18471795346636800, hexnat% "400000100400004000000", hexnat% "200000000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "60000043e08c94c00000", 8796227239936, hexnat% "80c0200000000000000", hexnat% "200400000100000001000000", 2211941711872, hexnat% "4200000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "60000341a08494c00000", 8830586978304, hexnat% "80c0002000000000000", hexnat% "200400000000400001000000", 2211941711872, hexnat% "4200000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4260000140620783400000", 549898420224, hexnat% "400000000000014000000", hexnat% "200000080001800000000000", hexnat% "8040000080800000000", 144678138029277184]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4260000140628703400000", hexnat% "400000000000014000000", hexnat% "200000080001800000000000", 2290089984, hexnat% "8040000080800000000", 144678138029277184]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2600000412a8d9ac00000", hexnat% "4000040000000200000000", hexnat% "8080202000000000000", 72268700354347008, hexnat% "200400000000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "460000140e2071fc00000", hexnat% "4200000000000000000000", 551903297536, hexnat% "200000080001000000000000", hexnat% "8040000080800000000", 144678138029277184]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6000004022050c400000", 144959613274423296, 9345848836096, hexnat% "4600000000000001000000", hexnat% "200000000100c00000000000", hexnat% "80c0000000800000000", 10779361280]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c10 c3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c11 c2
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c12 c1
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c13 c0
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record001_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00020.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00020.record008
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record008
def vertexColumn : Fields := ⟨10, hexnat% "f4368d6178b91749b16c5713c1f2e25ca6a5a95a4e87a398761b89e1783ef0761b8791d46d174571c66994e6c5a9665594e5554d54d475a362d4b51d2743db0ea398d6338d5334d331ce8b8ad2b46c9b0ecc729c6715c3723f60ca0d4348c6198961582e07b21c26294a5192542d074930ac1b21c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "69b6db6db6db6d249269b6db4d36db69b69249b6db4db492492491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨39, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨54, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨70, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨94, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5400040c081fe000000", hexnat% "3a000000000000000000", hexnat% "400000000000000000000000", 11529496529635115008, 1688901399871488]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400000400000000002000000", 11529215071838273536, hexnat% "28000000000030000000", 1759255111663616, hexnat% "4000040008048000000", 422216760033280, hexnat% "13000000000004000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c1 c0
  c2
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record008_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record008_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00020.record008

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00020.record011
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record011
def vertexColumn : Fields := ⟨10, hexnat% "f41d85e364d52d45d32c5b15c3713c1f2e25c96a3a95a3693a1eac6998d61d8ce1b89e1783ef0761b8791d46d174571e2729aa5994e745b172599565c569595555355351d70da362d4b51d2743db0ea398d6338d5334d331cd2b2ad1b0ee8791cc789c6725c570dc8fd82643489a198560b81ec8529464998942d0749322c2b06c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b69b6db6db6db4db49349269b6db69a4da4db6db6da4926db6d36924db492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨37, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨87, by decide⟩, ⟨102, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "eb0018000700185800000", hexnat% "8040000000002002000000", 1729663732021198848, 25773998080, hexnat% "4040000000000000000", hexnat% "40000000000000800000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40000200059001f00788000000", hexnat% "800000800000004000000", hexnat% "4000000002001000000", hexnat% "80a0000000000000000000", hexnat% "10000000000000c00000", hexnat% "440000000000002000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2f0008000900785c00000", hexnat% "10000600000000000", hexnat% "800000800000008000000", hexnat% "8400000000002002000000", hexnat% "41001000000000000", hexnat% "40000004000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "210000000800780400000", hexnat% "4041000000000000000", hexnat% "40000800000800000000000000", hexnat% "18000700000000000", hexnat% "80a0000000000000000000", 281475186425856, hexnat% "440000000002003000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c5 c0
  c6
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record011_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record011_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record011_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record011_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record011_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record011_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record011_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record011_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record011_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00020.record011
