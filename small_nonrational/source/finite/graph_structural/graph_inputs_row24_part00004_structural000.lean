module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00004Data
public import GraphInputsRow24Part00004Frames
public import GraphInputsRow24Part00004Leaves
public import GraphInputsRow24Part00004Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00004.record009
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record009
def vertexColumn : Fields := ⟨10, hexnat% "733c272b2ac6a3a71aa6a5a366394e3386e17bc172729c6639716a5a56356354d3346d17783d0ec370f23a8f13a4e33c2d8b52ccb8ad2b1ae1b46c5b0ee8761d4731e2729c6785c9715c3743c8f13c2f07c3ce09c28c94a0e8c60d84e0b81ee05c18c5490e4c50d44d0b41d"⟩
def kindColumn : Fields := ⟨3, hexnat% "1a4da4da69249369369a4926d36da6d36db6d36d36db69b491249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨26, by decide⟩, ⟨33, by decide⟩, ⟨37, by decide⟩, ⟨45, by decide⟩, ⟨48, by decide⟩, ⟨53, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "804245121202204e00000", hexnat% "1000400000000000000000", hexnat% "110000000000000000000", 1008806316530991104, hexnat% "80020000000000000000", hexnat% "3800000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1844721202204e00000", hexnat% "110000000000000000000", hexnat% "1000400000000000000000", hexnat% "221800000000000000", hexnat% "886000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2161763005524606976, hexnat% "44001002004000000", hexnat% "1000400120000000000000", hexnat% "7800000000000000000", hexnat% "110000000000000000000", hexnat% "800200000000000000000", hexnat% "80020000000200000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨21, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c3 c1
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c4 c0
  c5
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record009_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record009_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record009_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record009_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record009_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record009_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record009_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record009_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record009_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00004.record009

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00004.record031
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record031
def vertexColumn : Fields := ⟨10, hexnat% "3c45b3c236b86d1ac671b2659a963586e17bc16c56936785d16c57172559695654d54d54d4b46d17783d0ec370f2368d63a4cd32cccb1ac9b16f07a1d8791d4731e2749c6785c9715e0f0f03a0d84e0b81ee05c10e705515250d44d0b41da0cc324c3312c2b06e0711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db6db6926da4d24db49249a4db4924924d2492492249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "51b8f9019bff0000000", hexnat% "2000000420000000000", 180319906955264, 20266198323167232]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1098f1011bff0000000", hexnat% "4000000080000000000", 250688651132928, 20266198323167232, hexnat% "2000080020000000000", hexnat% "120000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11b8458dbbff0000000", 39582418599936, 792633534417207296, hexnat% "6000000000000000000", 36028797018963968]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "198b4801bfb0000000", hexnat% "1020000000000000000", hexnat% "6000000000000000000", 324259173170675712, 32985348833280, 4749891305734144]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11b8a58f5bff0000000", hexnat% "2000080020000000000", hexnat% "4000100080000000000", 288230376151711744]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1030a58f7bff0000000", hexnat% "188000000000000000", hexnat% "2000080000000000000", 360287970189639680, hexnat% "4000000080000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10a18e5bff0000000", hexnat% "1100040000000000000", hexnat% "6000000000000000000", 28587302322176, 396316767208603648, hexnat% "a8000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6008f805bbff0000000", hexnat% "1b0000000000000000", 4683919534325760, hexnat% "1000048000000000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "60085807fbff0000000", 24910535438893056, hexnat% "90a00000000000000", hexnat% "1120000000000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20000d8f7bff0000000", hexnat% "11a0000000000000000", hexnat% "4008100080000000000", hexnat% "10a00000000000000", 288230376151711744]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "b8fc8513fb0000000", hexnat% "1100000000000000000", hexnat% "6000000000000000000", 15393162788864, 4644887945281536, 35184372088832]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6000000413530000000", 180323128180736, 540431955284459520, hexnat% "98800000200000000", hexnat% "1000058000000000000", 28621662060544, hexnat% "120000008000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c16 c13
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c17 c12
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c18 c11
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c19 c10
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c20 c5
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c21 c2
  c22
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record031_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record031_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record031_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record031_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record031_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record031_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record031_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record031_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record031_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00004.record031

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00004.record032
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record032
def vertexColumn : Fields := ⟨10, hexnat% "3c26c96a36b46b1b2659a963586e17bc16c56936745b1725596953546d17743b0f2368d63a4d9334d332cd4b32d2b1ac9b16f07a1e4751cc789d2719e1725c5783c3ce09c20e8361382e07b81704390d44d0b41dc0e8360d4330d2324c3312c2b06e0711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "9b6db6da49b6db6da492492492492492492492449249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨82, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4014017d5e5d800000000", hexnat% "800800080180000000", 2362232012800, 11839541207891968]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1001040200880000000", hexnat% "800808080100000000", hexnat% "400400690000000000000", 73254068847378432, 9587767164010496, 7696581394432, 423037098786816]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c1 c0
  c2
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record032_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record032_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record032_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record032_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record032_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record032_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record032_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record032_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record032_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00004.record032

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00004.record035
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record035
def vertexColumn : Fields := ⟨10, hexnat% "3c45d38ccb3c236b86d1ac671b2659876a38ce8ba1e17971e25a93678571565555351d70da358d3352d1778370da358cd31ce8b32cab26c5bc1e8761d4731d2719e0f23c4f0f28a0e8560da0e0b81e7043951525154350b41d30c530cc8b0ac1b11c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6db6da4d24db6d24936da4d36924926da492489249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [279645397482209280, 40132174413824, hexnat% "100000020000000000", hexnat% "b0000000018000000", 1511828488192, 9223372105574252544]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [135389465408438272, 1512231141376, 144150378890395648, hexnat% "b0000000000000000", hexnat% "100000020000000000", 9223513392885530624, 4398046511104]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c1 c0
  c2
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record035_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record035_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record035_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record035_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record035_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record035_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record035_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record035_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record035_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00004.record035

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00004.record042
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record042
def vertexColumn : Fields := ⟨10, hexnat% "15cf08f2e2aaa718e61db0e5385ef04f1e26a96a559715a5395551d70d5352d4745de0f43b0dc3a8ce334cb31cf0ba2d8b52e2b2ae1b16f0761d4731ca719e0f43c4f0f03a158360b81ee05c1c2439514550d50d0b41da0cc328c530ce0b0ac1b11c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6d36934db4da4924934924924da493692492249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨63, by decide⟩, ⟨67, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨73, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "28042fd88300000000", 10520408746717347840, hexnat% "2000800200080000000", hexnat% "400040002010000000", 1376000147456, 108086391056891904]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4817c89167f0000000", hexnat% "208004000000000000", hexnat% "2000801200000000000", 633868453412864, 9015995347763200]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "220980de087f0000000", hexnat% "400240002000000000", 27762668601344, 9570149208162304, 396316767208603648, hexnat% "80000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2409fc92024b0000000", hexnat% "280020000000000000", 27763742343168, 1829595938553856, 70922794958848]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2208a2fe88390000000", hexnat% "400040002000000000", hexnat% "80400100000000000", 1152921521786716160, 1376000147456, 108086391056891904]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20822fc98390000000", hexnat% "80400100000000000", hexnat% "2400000000000000000", 35596688949248, 108086392667504640, 1747396672599621632]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20920ff9e7f0000000", hexnat% "80020000000000000", hexnat% "2400000000000000000", 396316767208603648, 594475150812905472]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [9370717460975583232, hexnat% "2400000000000000000", 396316767208603648, hexnat% "280020000000000000", 1266663165001728, 1747396655419752448]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "240020b004090000000", hexnat% "208004000000000000", 396316768819216384, 72022306586624, hexnat% "80020180000000000", 176067889332224, 1747396672599621632]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c11 c4
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c12 c3
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c13 c2
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c14 c1
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c15 c0
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record042_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record042_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record042_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record042_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record042_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record042_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record042_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record042_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00004.record042_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00004.record042
