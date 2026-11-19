module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00121Data
public import GraphInputsRow24Part00121Frames
public import GraphInputsRow24Part00121Leaves
public import GraphInputsRow24Part00121Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00121.record018
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record018
def vertexColumn : Fields := ⟨10, hexnat% "1d86d19c789d26c96ac695a698e6659362d92e1b91e785d16c5c95a599564d9396952d4cd1b49d70da358ce364d5334d332ce4b52d2b1ad1b16cc789ca719c970dc4f0bde08716252a1a46a168381e38619296152560d0746384e0b12c1b81c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db4da49b6db6936db6d24da6d26db693493492491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨48, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨75, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [7036874820419584, hexnat% "c04000000600000000", 3791650816, 446743707648, 2314867800654479360, hexnat% "9000000200000000000"]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record018_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record018_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record018_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record018_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record018_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record018_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record018_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record018_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record018_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00121.record018

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00121.record023
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record023
def vertexColumn : Fields := ⟨10, hexnat% "16c789ca5a8da699662d94e4b86e72569664d969565654b5c354d4b46d475c368d63a4cd32cd8b92d4b32d2b1ac9b16d8751e2749ca719c970dd0f13c2f7821c38a1a85a0e079c16856138549865258560d4341d30ca318e1324e0b12c1b81c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "d36db6db49b49b493492493493493692492489249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨77, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [3945064900329472, 1044835117844922368, hexnat% "20000070402000000000", 387620798464, 186919124205568, hexnat% "4c000000000000000", hexnat% "80000000000000000"]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record023_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record023_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record023_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record023_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record023_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record023_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record023_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record023_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record023_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00121.record023

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00121.record025
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record025
def vertexColumn : Fields := ⟨10, hexnat% "7a1b4c715c789d26c9ca6a96a3aa5a569a6659564d8b653a2e4ba1e4785e785d16c5c96a5693a659565a5655554d4b55362d4b61d4745d38e9394cb392ccb8acab1ae1b16e2729c9715c3713c1f7412c34a168382e346158342d30ca384c9314e0b12c2b81c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db69b6db6db6da49b69b6db6db6da49b492492492492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨58, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨78, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40000400000000000000", hexnat% "18000180000000000", 4611690417820270592, 622904475648, 62822285312, 412434300928]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record025_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record025_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record025_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record025_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record025_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record025_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record025_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record025_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record025_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00121.record025

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00121.record026
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record026
def vertexColumn : Fields := ⟨10, hexnat% "1e86d1ac789d26c96ac6a5a569a6658d64d8b68b92e8791e179e1745b1725a95a4e996559a54d52d4cd8b4ad8745d70da358ce364e5354cd34ccb392d4b8ad2b1ae1b46c5b31e2729c9715c3713c1f741525292a85a0e0b8d1296152560d0b61314e0b12c2b81c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36da69b4db6d24db4db6db4934936db6926d249269a492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨63, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨75, by decide⟩, ⟨78, by decide⟩, ⟨80, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40300048003f53c00000", 10133099295801344, hexnat% "8080002000000000000", 7696581394432, 36028797086072832, hexnat% "100008000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [64183997172809728, hexnat% "8080002000000000000", hexnat% "100008000000000000000", 266287972352, hexnat% "200008000000000000", hexnat% "40100000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "480080e4073e5fc00000", hexnat% "300000000000000000", hexnat% "100000000000000000000", hexnat% "80002000100000000", 2251799813685248]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4830800e023e5bc00000", hexnat% "80000000100000000", hexnat% "100000000010004000000", 4398046511104, 63050394783186944]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "48308008023e43800000", 10133099295801344, hexnat% "100000000010004000000", 4402345672704, 54043195528445952, hexnat% "80002000010000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "82800ae04195fc00000", 9241387534875885568, 163208757248, hexnat% "40100000000000000000", hexnat% "100000000020000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "828000e00115bc00000", 63050394850295808, hexnat% "40100000000600000000", 4535485464576, 34359738368, hexnat% "100008000030000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40180000001602800000", 10133099312578560, 9241387534875885568, 36591747043688448, hexnat% "200008000810000000", hexnat% "108000000020000000000", 4540854173696]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c11 c6
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c12 c1
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c13 c0
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record026_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record026_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record026_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record026_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record026_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record026_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record026_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record026_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record026_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00121.record026

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00121.record027
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record027
def vertexColumn : Fields := ⟨10, hexnat% "7a1b46b16a9695a358b68ba1e179e16c5c96a5693a7199655969695654d54d4b5634cd8b52d2b61d4745d58ce394d5334d332ce4b52e2b4ac6b86d1b16cc789ca725c570dc4f07dd085a0e0b9c168591544d152529296152560d0b61314e0b12c2b81c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6d269249b69249a6d249b6d24da4924d3492491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "300403401fa86000000", hexnat% "5c0000000000000000", 61572919590912, 2380152404139048960, 1152921505277935616, hexnat% "200c00000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3786d3c217ade000000", 1152921505143717888, hexnat% "40000008000000000", 26388279066624]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1787d0c215abe000000", hexnat% "2000020000000000000", 18279380811776, 8797166764032, hexnat% "40010000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "320613c295afe000000", 2017612633061982208, 18279380811776, hexnat% "5c0000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "338613c217ade000000", hexnat% "40000008000000000", hexnat% "400800000000000000", 288256764430778368, 1152921505143717888]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "320402c215ad6000000", 1224979099315863552, hexnat% "100000108000000000", 864699924548157440, hexnat% "482000000000000000", hexnat% "40010002000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "300442401fa9e000000", 61572651155456, 1801439851485069312, hexnat% "c0010000000000000", 2308094810101121024, hexnat% "700000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "32c113831f8fe000000", 864699924548157440, hexnat% "402000000000000000", hexnat% "104000000000000000", 1125908496777216]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7c79382078fe000000", 1657857376256, 288256764430778368, hexnat% "3000000000000000000", 1125899906842624]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7c511821fafe000000", 2882303761517117440, hexnat% "2000020000000000000", 288256764430778368, hexnat% "1000004000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "26411282068fe000000", 1726576852992, 864699924548157440, hexnat% "82010000000000000", hexnat% "1004004000000000000", hexnat% "100000100000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c15 c12
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c16 c11
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "786d38386afc000000", 1154047404547244032, hexnat% "3000000000000000000", 1717986918400, hexnat% "40000000000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c6c3839fa7c000000", 1224979098644774912, hexnat% "700000000000000000", hexnat% "3000000000082000000", 1125899906842624]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [6708173537527463936, 1855425871872, hexnat% "682000000000000000", hexnat% "3000000000082000000", 10133099161583616, hexnat% "140000000000000000"]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c21 c18
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7c680009f80c000000", 15762599769538560, hexnat% "3000000000082000000", 1513209475333357568, 52785416503296, 1125899906842624]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "34c783c087aee000000", 1649267441664, hexnat% "200500000000000000", 52776826568704, hexnat% "100000000000000000"]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3405034084aae000000", 52776826568704, 2380152404139048960, 1855425871872, hexnat% "200c00000000000000", hexnat% "1c0000000000000000"]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c25 c24
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3401404384abe000000", 1855425871872, hexnat% "202900000000000000", hexnat% "144000000000000000", 15762599769538560, hexnat% "80000000000000000"]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "340000408489e000000", 36292473651200, 2089670227636781056, hexnat% "282000000000000000", hexnat% "4000000b000000000", hexnat% "104000100000000000", 15762599769538560]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c28 c27
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c29 c26
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c30 c23
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c31 c22
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c32 c17
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c33 c10
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c34 c9
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c35 c0
  c36
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record027_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record027_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record027_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record027_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record027_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record027_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record027_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record027_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record027_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00121.record027
