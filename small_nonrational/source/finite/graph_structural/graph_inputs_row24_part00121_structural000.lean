module
prelude
public import FacetCliqueRaw
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00121Data
public import GraphInputsRow24Part00121Frames
public import GraphInputsRow24Part00121Leaves
public import GraphInputsRow24Part00121Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

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

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00121.record015
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "1f07a1b46b0ec8f13c5c8f25aa3a4e8e68d8b68b86e8783e785d16c5713c5c96a5693a7194e5a539695655352d58d3352d2b46d8751d0f56338d5334d332cc7392d4b4ac6b86d1b0ecc729c6725c3713c2f07de06c1682d06a858368382e70591526152560d84e0b12e0705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "926db6d36d249249369a6db6934db6d36db6db49a4db6d2491249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record015 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record015 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record015.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 62), (facetIndex 66), (facetIndex 67)]))
 (.leaf ([(facetIndex 60), (facetIndex 77), (facetIndex 85)])))
 (.branch 3
 (.leaf ([(facetIndex 65), (facetIndex 84), (facetIndex 86)]))
 (.leaf ([(facetIndex 21), (facetIndex 31), (facetIndex 45), (facetIndex 68), (facetIndex 69)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 25), (facetIndex 51), (facetIndex 53), (facetIndex 54)]))
 (.leaf ([(facetIndex 22), (facetIndex 23), (facetIndex 70), (facetIndex 71)])))
 (.branch 7
 (.leaf ([(facetIndex 32), (facetIndex 34), (facetIndex 35)]))
 (.leaf ([(facetIndex 24), (facetIndex 72), (facetIndex 73)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "8a00000803fb5b010001000120800018000000d86600027b58000000000000000"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 29), (facetIndex 30), (facetIndex 44), (facetIndex 58), (facetIndex 76)]))
 (.leaf ([(facetIndex 43), (facetIndex 75), (facetIndex 80), (facetIndex 81)])))
 (.branch 3
 (.leaf ([(facetIndex 26), (facetIndex 28), (facetIndex 49)]))
 (.branch 4
 (.leaf ([(facetIndex 36), (facetIndex 39), (facetIndex 40)]))
 (.leaf ([(facetIndex 47), (facetIndex 50), (facetIndex 82)])))))
 (.branch 8
 (.branch 6
 (.leaf ([(facetIndex 27), (facetIndex 46), (facetIndex 74)]))
 (.branch 7
 (.leaf ([(facetIndex 63), (facetIndex 78), (facetIndex 79)]))
 (.leaf ([(facetIndex 48), (facetIndex 59), (facetIndex 83)]))))
 (.branch 9
 (.leaf ([(facetIndex 33), (facetIndex 37), (facetIndex 52), (facetIndex 55), (facetIndex 57), (facetIndex 61), (facetIndex 64)]))
 (.branch 10
 (.leaf ([(facetIndex 38), (facetIndex 41), (facetIndex 56)]))
 (.leaf ([(facetIndex 42)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "74116600150000000008608070898008042745001a9339830080000252z1a;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 11
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
def grouped3_0017 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0019 : List Nat := [1]
def grouped3_0020 : List Nat := [2]
def grouped3_0021 : List Nat := [2, 3, 4]
def grouped3_0022 : List Nat := [3]
def grouped3_0023 : List Nat := [3, 4]
def grouped3_0024 : List Nat := [4]
def grouped3_0025 : List Nat := [5]
def grouped3_0026 : List Nat := [5, 6, 7]
def grouped3_0027 : List Nat := [5, 6, 7, 8, 9, 10]
def grouped3_0028 : List Nat := [6]
def grouped3_0029 : List Nat := [6, 7]
def grouped3_0030 : List Nat := [7]
def grouped3_0031 : List Nat := [8]
def grouped3_0032 : List Nat := [8, 9, 10]
def grouped3_0033 : List Nat := [9]
def grouped3_0034 : List Nat := [9, 10]
def grouped3_0035 : List Nat := [10]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record015 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record015_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00121.record015" "{\"atoms\":[{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group\",\"kind\":3,\"index\":10},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0029\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0029\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0034\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0032\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0032\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0027\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00121.record015" 101

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00121.record015" "{\"ridges\":[[24,38],[26,38],[26,101],[28,67],[28,198],[32,42],[32,67],[32,98],[34,67],[34,265],[35,67],[36,67],[36,113],[38,291],[39,145],[39,210],[40,338],[54,145],[57,57],[58,792],[60,265],[61,169],[62,193],[65,145],[65,273],[68,44],[70,98],[71,38],[71,42],[72,38],[72,50],[73,50],[74,38],[74,198],[75,42],[75,282],[77,296],[78,210],[79,338],[82,204],[83,396],[84,304],[85,296],[86,224]],\"owners\":[[32,67,[28,39,40],[3,23,26,34,35,36,41,42]],[34,67,[26,28,36,39,41],[3,23,32,35,40,42]],[35,67,[26,28,36,39,40,41,42],[3,23,32,34]],[34,265,[44,48,50,57,58,61],[9,30,33,60,62]],[60,265,[30,44,50,58],[9,33,34,48,57,61,62]],[65,273,[30,40,44,58],[10,38,52,53,57,64,66]],[62,193,[28,39,41,55,63],[11,49,59,66,67]],[68,44,[46,47,48,82,83],[12,22,43,70,71,80,81]],[72,50,[29,36,38,75,76,79],[14,24,37,68,73,78]],[73,50,[29,36,37,38,75,78,79],[14,24,68,72,76]],[32,98,[74,78,79],[16,26,36,41,42,70,77]],[70,98,[36,41,42,78,79],[16,26,32,74,77]],[77,296,[48,57,61,80,83],[18,33,60,75,85]],[85,296,[33,48,57,75,80],[18,60,61,77,83]],[84,304,[38,57,64,75,79],[19,52,65,80,86]],[86,224,[41,55,59,74,82],[20,63,67,78,85]],[26,101,[46,55],[]],[28,198,[74],[]],[74,198,[28],[]],[57,57,[29,43],[]],[75,282,[30],[]],[38,291,[33,42],[]],[36,113,[63,64],[]],[39,210,[78],[]],[78,210,[39],[]],[40,338,[79],[]],[79,338,[40],[]],[61,169,[47,59],[]],[82,204,[49],[]],[83,396,[50],[]],[58,792,[],[]]],\"edges\":[],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00121.record015" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00121.record015\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-6,-4],[-11,-2],[-11,-3],[-11,-4],[-11,-8],[-14,-2],[-14,-3],[-14,-8],[-14,-9],[-14,-12],[-15,-6],[-15,-11],[-16,-6],[-16,-7],[-17,-11],[-17,-13],[-18,-5],[-20,-4],[-20,-15],[-25,-13],[-27,-20],[-28,-13],[-31,-18],[-33,-15],[-33,-27],[-34,-1],[-34,-10],[-34,-24],[-36,-13],[-36,-20],[-36,-21],[-37,-11],[-37,-13],[-37,-21],[-39,-13],[-39,-19],[-42,-15],[-42,-30],[-43,-15],[-43,-19],[-43,-42],[-44,-15],[-44,-37],[-46,-34],[-47,-6],[-47,-11],[-49,-7],[-49,-20],[-50,-48],[-52,-13],[-53,-48],[-54,-11],[-54,-13],[-54,-19],[-54,-21],[-56,-13],[-60,-27],[-60,-40],[-60,-55],[-61,-21],[-61,-26],[-61,-41],[-61,-44],[-61,-56],[-62,-15],[-62,-18],[-62,-61],[-11,7,18,19],[-13,6,7,15,18,20],[-14,6,7,15,18,19,20,21],[-7,-14,-15],[-18,-32,-42],[-13,23,27,29,34,35,38],[-37,9,23,29,35],[-42,9,19,23,35],[-39,7,18,20,33,40],[-4,-48,-51],[-6,-48,-49],[-11,-48,-52],[-45,25,26,27,58,59],[-49,8,15,17,52,53,56],[-50,8,15,16,17,52,55,56],[-11,51,55,56],[-47,15,20,21,55,56],[-54,27,34,38,57,59],[-61,12,27,34,52,57],[-60,17,34,41,52,56],[-62,20,33,36,51,58],[-6,25,33],[-7,51],[-51,7],[-34,8,22],[-52,9],[-17,12,21],[-15,40,41],[-18,55],[-55,18],[-19,56],[-56,19],[-38,26,36],[-58,28],[-59,29],[-35],[-63,39,43,44],[-64,37,54,61],[-65,42,60,62],[-66,1,10,24,45,46],[-67,5,30,31,32],[-68,2,3,47,48],[-69,11,13,14],[-70,4,49,50],[-71,63],[-71,64],[-72,65],[-72,66],[-73,71],[-73,72],[-74,67],[-74,68],[-75,69],[-75,70],[-76,74],[-76,75],[-77,73],[-77,76],[77],[-8,78],[-9,78],[-23,78],[-22,79],[-52,79],[-57,79],[-6,80],[-7,80],[-15,81],[-18,81],[-19,81],[-26,82],[-29,82],[-58,82],[-25,83],[-51,83],[-40,84],[-55,84],[-56,84],[-85,27,36,59],[-27,85],[-36,85],[-59,85],[-16,86],[-33,86],[-41,86],[-20,87],[-21,88],[-79,89],[-78,89],[-82,90],[-81,90],[-90,91],[-80,91],[-91,92],[-89,92],[-85,93],[-84,-85,94],[-93,95],[-94,96],[-83,-93,96],[-88,97],[-87,97],[-97,98],[-86,98],[-86,-97,99],[-99,100],[-95,-98,100],[-96,100],[-92,-100,101],[-101]],\"atoms\":[{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group\",\"index\":10,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":26,\"b\":24},{\"tag\":\"incompatible\",\"a\":32,\"b\":22},{\"tag\":\"incompatible\",\"a\":32,\"b\":23},{\"tag\":\"incompatible\",\"a\":32,\"b\":24},{\"tag\":\"incompatible\",\"a\":32,\"b\":29},{\"tag\":\"incompatible\",\"a\":35,\"b\":22},{\"tag\":\"incompatible\",\"a\":35,\"b\":23},{\"tag\":\"incompatible\",\"a\":35,\"b\":29},{\"tag\":\"incompatible\",\"a\":35,\"b\":30},{\"tag\":\"incompatible\",\"a\":35,\"b\":33},{\"tag\":\"incompatible\",\"a\":36,\"b\":26},{\"tag\":\"incompatible\",\"a\":36,\"b\":32},{\"tag\":\"incompatible\",\"a\":37,\"b\":26},{\"tag\":\"incompatible\",\"a\":37,\"b\":28},{\"tag\":\"incompatible\",\"a\":38,\"b\":32},{\"tag\":\"incompatible\",\"a\":38,\"b\":34},{\"tag\":\"incompatible\",\"a\":39,\"b\":25},{\"tag\":\"incompatible\",\"a\":41,\"b\":24},{\"tag\":\"incompatible\",\"a\":41,\"b\":36},{\"tag\":\"incompatible\",\"a\":46,\"b\":34},{\"tag\":\"incompatible\",\"a\":48,\"b\":41},{\"tag\":\"incompatible\",\"a\":49,\"b\":34},{\"tag\":\"incompatible\",\"a\":53,\"b\":39},{\"tag\":\"incompatible\",\"a\":55,\"b\":36},{\"tag\":\"incompatible\",\"a\":55,\"b\":48},{\"tag\":\"incompatible\",\"a\":57,\"b\":21},{\"tag\":\"incompatible\",\"a\":57,\"b\":31},{\"tag\":\"incompatible\",\"a\":57,\"b\":45},{\"tag\":\"incompatible\",\"a\":59,\"b\":34},{\"tag\":\"incompatible\",\"a\":59,\"b\":41},{\"tag\":\"incompatible\",\"a\":59,\"b\":42},{\"tag\":\"incompatible\",\"a\":60,\"b\":32},{\"tag\":\"incompatible\",\"a\":60,\"b\":34},{\"tag\":\"incompatible\",\"a\":60,\"b\":42},{\"tag\":\"incompatible\",\"a\":62,\"b\":34},{\"tag\":\"incompatible\",\"a\":62,\"b\":40},{\"tag\":\"incompatible\",\"a\":65,\"b\":36},{\"tag\":\"incompatible\",\"a\":65,\"b\":51},{\"tag\":\"incompatible\",\"a\":66,\"b\":36},{\"tag\":\"incompatible\",\"a\":66,\"b\":40},{\"tag\":\"incompatible\",\"a\":66,\"b\":65},{\"tag\":\"incompatible\",\"a\":67,\"b\":36},{\"tag\":\"incompatible\",\"a\":67,\"b\":60},{\"tag\":\"incompatible\",\"a\":69,\"b\":57},{\"tag\":\"incompatible\",\"a\":70,\"b\":26},{\"tag\":\"incompatible\",\"a\":70,\"b\":32},{\"tag\":\"incompatible\",\"a\":72,\"b\":28},{\"tag\":\"incompatible\",\"a\":72,\"b\":41},{\"tag\":\"incompatible\",\"a\":73,\"b\":71},{\"tag\":\"incompatible\",\"a\":75,\"b\":34},{\"tag\":\"incompatible\",\"a\":76,\"b\":71},{\"tag\":\"incompatible\",\"a\":77,\"b\":32},{\"tag\":\"incompatible\",\"a\":77,\"b\":34},{\"tag\":\"incompatible\",\"a\":77,\"b\":40},{\"tag\":\"incompatible\",\"a\":77,\"b\":42},{\"tag\":\"incompatible\",\"a\":79,\"b\":34},{\"tag\":\"incompatible\",\"a\":84,\"b\":48},{\"tag\":\"incompatible\",\"a\":84,\"b\":63},{\"tag\":\"incompatible\",\"a\":84,\"b\":78},{\"tag\":\"incompatible\",\"a\":85,\"b\":42},{\"tag\":\"incompatible\",\"a\":85,\"b\":47},{\"tag\":\"incompatible\",\"a\":85,\"b\":64},{\"tag\":\"incompatible\",\"a\":85,\"b\":67},{\"tag\":\"incompatible\",\"a\":85,\"b\":79},{\"tag\":\"incompatible\",\"a\":86,\"b\":36},{\"tag\":\"incompatible\",\"a\":86,\"b\":39},{\"tag\":\"incompatible\",\"a\":86,\"b\":85},{\"tag\":\"mate\",\"ridge\":67,\"a\":32,\"owners\":[28,39,40]},{\"tag\":\"mate\",\"ridge\":67,\"a\":34,\"owners\":[26,28,36,39,41]},{\"tag\":\"mate\",\"ridge\":67,\"a\":35,\"owners\":[26,28,36,39,40,41,42]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[28,35,36]},{\"tag\":\"three\",\"ridge\":145,\"vertices\":[39,54,65]},{\"tag\":\"mate\",\"ridge\":265,\"a\":34,\"owners\":[44,48,50,57,58,61]},{\"tag\":\"mate\",\"ridge\":265,\"a\":60,\"owners\":[30,44,50,58]},{\"tag\":\"mate\",\"ridge\":273,\"a\":65,\"owners\":[30,40,44,58]},{\"tag\":\"mate\",\"ridge\":193,\"a\":62,\"owners\":[28,39,41,55,63]},{\"tag\":\"three\",\"ridge\":38,\"vertices\":[24,71,74]},{\"tag\":\"three\",\"ridge\":38,\"vertices\":[26,71,72]},{\"tag\":\"three\",\"ridge\":42,\"vertices\":[32,71,75]},{\"tag\":\"mate\",\"ridge\":44,\"a\":68,\"owners\":[46,47,48,82,83]},{\"tag\":\"mate\",\"ridge\":50,\"a\":72,\"owners\":[29,36,38,75,76,79]},{\"tag\":\"mate\",\"ridge\":50,\"a\":73,\"owners\":[29,36,37,38,75,78,79]},{\"tag\":\"mate\",\"ridge\":98,\"a\":32,\"owners\":[74,78,79]},{\"tag\":\"mate\",\"ridge\":98,\"a\":70,\"owners\":[36,41,42,78,79]},{\"tag\":\"mate\",\"ridge\":296,\"a\":77,\"owners\":[48,57,61,80,83]},{\"tag\":\"mate\",\"ridge\":296,\"a\":85,\"owners\":[33,48,57,75,80]},{\"tag\":\"mate\",\"ridge\":304,\"a\":84,\"owners\":[38,57,64,75,79]},{\"tag\":\"mate\",\"ridge\":224,\"a\":86,\"owners\":[41,55,59,74,82]},{\"tag\":\"mate\",\"ridge\":101,\"a\":26,\"owners\":[46,55]},{\"tag\":\"mate\",\"ridge\":198,\"a\":28,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":198,\"a\":74,\"owners\":[28]},{\"tag\":\"mate\",\"ridge\":57,\"a\":57,\"owners\":[29,43]},{\"tag\":\"mate\",\"ridge\":282,\"a\":75,\"owners\":[30]},{\"tag\":\"mate\",\"ridge\":291,\"a\":38,\"owners\":[33,42]},{\"tag\":\"mate\",\"ridge\":113,\"a\":36,\"owners\":[63,64]},{\"tag\":\"mate\",\"ridge\":210,\"a\":39,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":210,\"a\":78,\"owners\":[39]},{\"tag\":\"mate\",\"ridge\":338,\"a\":40,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":338,\"a\":79,\"owners\":[40]},{\"tag\":\"mate\",\"ridge\":169,\"a\":61,\"owners\":[47,59]},{\"tag\":\"mate\",\"ridge\":204,\"a\":82,\"owners\":[49]},{\"tag\":\"mate\",\"ridge\":396,\"a\":83,\"owners\":[50]},{\"tag\":\"mate\",\"ridge\":792,\"a\":58,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[62,66,67],\"full_literals\":[-63,39,43,44]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[60,77,85],\"full_literals\":[-64,37,54,61]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[65,84,86],\"full_literals\":[-65,42,60,62]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[21,31,45,68,69],\"full_literals\":[-66,1,10,24,45,46]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[25,51,53,54],\"full_literals\":[-67,5,30,31,32]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[22,23,70,71],\"full_literals\":[-68,2,3,47,48]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[32,34,35],\"full_literals\":[-69,11,13,14]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[24,72,73],\"full_literals\":[-70,4,49,50]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-71,63,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-71,false,64],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-72,65,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-72,false,66],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-73,71,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-73,false,72],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-74,67,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-74,false,68],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-75,69,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-75,false,70],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-76,74,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-76,false,75],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-77,73,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-77,false,76],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":29,\"full_literals\":[-8,78]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":30,\"full_literals\":[-9,78]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":44,\"full_literals\":[-23,78]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":43,\"full_literals\":[-22,79]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":75,\"full_literals\":[-52,79]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":80,\"full_literals\":[-57,79]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":26,\"full_literals\":[-6,80]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":28,\"full_literals\":[-7,80]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":36,\"full_literals\":[-15,81]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":39,\"full_literals\":[-18,81]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":40,\"full_literals\":[-19,81]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":47,\"full_literals\":[-26,82]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":50,\"full_literals\":[-29,82]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":82,\"full_literals\":[-58,82]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":46,\"full_literals\":[-25,83]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":74,\"full_literals\":[-51,83]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":63,\"full_literals\":[-40,84]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":78,\"full_literals\":[-55,84]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":79,\"full_literals\":[-56,84]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[48,59,83],\"full_literals\":[-85,27,36,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":48,\"full_literals\":[-27,85]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":59,\"full_literals\":[-36,85]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":83,\"full_literals\":[-59,85]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":37,\"full_literals\":[-16,86]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":55,\"full_literals\":[-33,86]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":64,\"full_literals\":[-41,86]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":41,\"full_literals\":[-20,87]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":42,\"full_literals\":[-21,88]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-79,89],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-78,false,89],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0023\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-82,90],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-81,false,90],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-90,91],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-80,false,91],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-91,92],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-89,false,92],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0028\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0029\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-85,93],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0028\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0029\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-84,-85,94],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-93,95],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-94,96],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-83,-93,96],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped3_0033\",\"right_name\":\"grouped3_0035\",\"joined_name\":\"grouped3_0034\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-88,97],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped3_0033\",\"right_name\":\"grouped3_0035\",\"joined_name\":\"grouped3_0034\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-87,false,97],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped3_0031\",\"right_name\":\"grouped3_0034\",\"joined_name\":\"grouped3_0032\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-97,98],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped3_0031\",\"right_name\":\"grouped3_0034\",\"joined_name\":\"grouped3_0032\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-86,false,98],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped3_0031\",\"right_name\":\"grouped3_0034\",\"joined_name\":\"grouped3_0032\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-86,-97,99],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0026\",\"right_name\":\"grouped3_0032\",\"joined_name\":\"grouped3_0027\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-99,100],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0026\",\"right_name\":\"grouped3_0032\",\"joined_name\":\"grouped3_0027\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-95,-98,100],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0026\",\"right_name\":\"grouped3_0032\",\"joined_name\":\"grouped3_0027\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-96,false,100],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-92,-100,101],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true}]}"
  "p cnf 101 177\n-6 -4 0\n-11 -2 0\n-11 -3 0\n-11 -4 0\n-11 -8 0\n-14 -2 0\n-14 -3 0\n-14 -8 0\n-14 -9 0\n-14 -12 0\n-15 -6 0\n-15 -11 0\n-16 -6 0\n-16 -7 0\n-17 -11 0\n-17 -13 0\n-18 -5 0\n-20 -4 0\n-20 -15 0\n-25 -13 0\n-27 -20 0\n-28 -13 0\n-31 -18 0\n-33 -15 0\n-33 -27 0\n-34 -1 0\n-34 -10 0\n-34 -24 0\n-36 -13 0\n-36 -20 0\n-36 -21 0\n-37 -11 0\n-37 -13 0\n-37 -21 0\n-39 -13 0\n-39 -19 0\n-42 -15 0\n-42 -30 0\n-43 -15 0\n-43 -19 0\n-43 -42 0\n-44 -15 0\n-44 -37 0\n-46 -34 0\n-47 -6 0\n-47 -11 0\n-49 -7 0\n-49 -20 0\n-50 -48 0\n-52 -13 0\n-53 -48 0\n-54 -11 0\n-54 -13 0\n-54 -19 0\n-54 -21 0\n-56 -13 0\n-60 -27 0\n-60 -40 0\n-60 -55 0\n-61 -21 0\n-61 -26 0\n-61 -41 0\n-61 -44 0\n-61 -56 0\n-62 -15 0\n-62 -18 0\n-62 -61 0\n-11 7 18 19 0\n-13 6 7 15 18 20 0\n-14 6 7 15 18 19 20 21 0\n-7 -14 -15 0\n-18 -32 -42 0\n-13 23 27 29 34 35 38 0\n-37 9 23 29 35 0\n-42 9 19 23 35 0\n-39 7 18 20 33 40 0\n-4 -48 -51 0\n-6 -48 -49 0\n-11 -48 -52 0\n-45 25 26 27 58 59 0\n-49 8 15 17 52 53 56 0\n-50 8 15 16 17 52 55 56 0\n-11 51 55 56 0\n-47 15 20 21 55 56 0\n-54 27 34 38 57 59 0\n-61 12 27 34 52 57 0\n-60 17 34 41 52 56 0\n-62 20 33 36 51 58 0\n-6 25 33 0\n-7 51 0\n-51 7 0\n-34 8 22 0\n-52 9 0\n-17 12 21 0\n-15 40 41 0\n-18 55 0\n-55 18 0\n-19 56 0\n-56 19 0\n-38 26 36 0\n-58 28 0\n-59 29 0\n-35 0\n-63 39 43 44 0\n-64 37 54 61 0\n-65 42 60 62 0\n-66 1 10 24 45 46 0\n-67 5 30 31 32 0\n-68 2 3 47 48 0\n-69 11 13 14 0\n-70 4 49 50 0\n-71 63 0\n-71 64 0\n-72 65 0\n-72 66 0\n-73 71 0\n-73 72 0\n-74 67 0\n-74 68 0\n-75 69 0\n-75 70 0\n-76 74 0\n-76 75 0\n-77 73 0\n-77 76 0\n77 0\n-8 78 0\n-9 78 0\n-23 78 0\n-22 79 0\n-52 79 0\n-57 79 0\n-6 80 0\n-7 80 0\n-15 81 0\n-18 81 0\n-19 81 0\n-26 82 0\n-29 82 0\n-58 82 0\n-25 83 0\n-51 83 0\n-40 84 0\n-55 84 0\n-56 84 0\n-85 27 36 59 0\n-27 85 0\n-36 85 0\n-59 85 0\n-16 86 0\n-33 86 0\n-41 86 0\n-20 87 0\n-21 88 0\n-79 89 0\n-78 89 0\n-82 90 0\n-81 90 0\n-90 91 0\n-80 91 0\n-91 92 0\n-89 92 0\n-85 93 0\n-84 -85 94 0\n-93 95 0\n-94 96 0\n-83 -93 96 0\n-88 97 0\n-87 97 0\n-97 98 0\n-86 98 0\n-86 -97 99 0\n-99 100 0\n-95 -98 100 0\n-96 100 0\n-92 -100 101 0\n-101 0\n"
  "178 73 0 126 124 0\n179 76 0 126 125 0\n180 71 0 178 116 0\n181 72 0 178 117 0\n182 74 0 179 122 0\n183 75 0 179 123 0\n184 63 0 180 112 0\n185 64 0 180 113 0\n186 65 0 181 114 0\n187 66 0 181 115 0\n188 67 0 182 118 0\n189 68 0 182 119 0\n190 69 0 183 120 0\n191 70 0 183 121 0\n192 85 92 0 103 185 190 161 159 158 137 160 134 136 68 157 139 102 162 156 128 129 74 127 155 130 92 138 132 131 147 148 100 85 73 105 110 86 10 0\n193 -36 91 0 190 159 158 137 160 134 136 68 135 133 29 30 31 110 70 0\n194 92 0 103 186 161 162 159 160 156 157 158 134 128 129 139 140 137 91 75 102 192 193 146 21 25 57 88 106 0\n195 -100 0 194 177 176 0\n196 -99 0 195 173 0\n197 -96 0 195 175 0\n198 -94 0 197 166 0\n199 -85 0 198 197 195 190 163 164 165 167 143 144 145 174 141 142 96 83 98 170 171 90 168 169 151 152 154 153 89 95 70 69 110 0\n200 -27 0 199 147 0\n201 -59 0 199 149 0\n202 -11 0 189 185 191 2 3 4 5 12 15 32 46 52 109 105 49 51 79 64 111 81 0\n203 -13 0 185 201 200 184 186 187 16 20 22 33 35 50 53 56 101 105 61 62 63 67 80 104 41 106 87 26 27 28 44 107 0\n204 14 0 203 190 202 110 0\n205 -2 0 204 6 0\n206 -3 0 204 7 0\n207 -8 0 204 8 0\n208 -9 0 204 9 0\n209 -12 0 204 10 0\n210 -52 0 208 93 0\n211 -21 0 185 34 55 60 105 0\n212 -17 0 211 209 94 0\n213 15 18 19 20 6 0 204 211 206 205 189 212 210 207 191 97 99 70 84 14 47 90 109 82 77 111 0\n214 18 19 6 20 0 186 184 204 213 24 37 39 42 65 71 104 106 76 58 0\n215 -18 0 186 188 17 23 66 96 59 106 38 72 108 0\n216 -55 0 215 97 0\n217 -19 0 184 185 36 40 54 98 104 64 43 105 0\n218 -56 0 217 99 0\n219 -20 0 191 216 212 210 218 207 196 18 19 48 153 111 169 82 172 150 0\n220 6 0 219 217 215 214 0\n221 -4 0 220 1 0\n222 -15 0 220 11 0\n223 -16 0 220 13 0\n224 -47 0 220 45 0\n225 -50 0 223 207 222 218 210 212 216 82 0\n226 48 0 224 189 205 206 109 0\n227 49 0 225 191 221 111 0\n228 0 226 227 220 78 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record015.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record015.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record015.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record015.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record015 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record015.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record015.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record015.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record015.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record015 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record015_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record015_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record015_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record015_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record015_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record015_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record015_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record015 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record015_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record015_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00121.record015_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00121.record015
