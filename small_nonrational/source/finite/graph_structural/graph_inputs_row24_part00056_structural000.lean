module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00056Data
public import GraphInputsRow24Part00056Frames
public import GraphInputsRow24Part00056Leaves
public import GraphInputsRow24Part00056Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00056.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record002
def vertexColumn : Fields := ⟨10, hexnat% "174a715c4f1d26c972e299a5693a599564d876a394e4b91e2785e0f9d16c571a659956539a568d8749d1743d70da358d9354cd34ccb31cd8b52d2b46c9b16c3ba1e4789c9715c3723c4f0bc1f5c1981d162a298a19a0e1c68926465154358341da0c6382c8b81c4709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "26db6926d36936db6da49b69249b4db6d26da6d24d2492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨36, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨47, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨73, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨84, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1042400000020000000000", hexnat% "20200000010008000000", 1441292618246914048, 16888498619416576, 594475219532382208, 15133048832, hexnat% "10000000000030000000"]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00056.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00056.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record003
def vertexColumn : Fields := ⟨10, hexnat% "5e1b4a719c4f07c749b25cb8a5a99a5693a1e9a6659362d876a398e4b86e4789e1783e745b15c569a6599565391e6952d475a346d8749d1743d70da358d9354cd34ccb31ce8b62e4b52d2b1ad1b26c5b0ee2729c6725c570dc8f13c2f07d705616252a868387116685254358341da0c6382c4b81c8709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "4db6db4d34db6db4db6db6d36d34924d249b4db6d26934da6924d2491249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨47, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨65, by decide⟩, ⟨75, by decide⟩, ⟨83, by decide⟩, ⟨85, by decide⟩, ⟨87, by decide⟩, ⟨95, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8020080008b401487be00000", 432345564227567616, hexnat% "22000802000000000", 74309393851613184, hexnat% "8800000000020100000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80a80002200082210a600000", 309246033920, 651896046061879296, hexnat% "8000080010041000000", 805306368, 445856363109679104]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80a00002290c822900400000", hexnat% "80000000000000a200000", 1374414700544, hexnat% "8000080000040000000", 805306368, 445856363109679104]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80a800002ebc02217be00000", 309237645312, hexnat% "20100000000000000", hexnat% "8000000010000000000", 140737488355328]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80a80002282082210a600000", 309246033920, hexnat% "8000080010041000000", 432345564764438528, 79938893385826304, 268435456]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8808000880010041400000", hexnat% "802000000004000800000000", hexnat% "22000802000000000", 279183360000, 432345564898656256, 72059793363173376, 15762598695796736]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00056.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00056.record010
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record010
def vertexColumn : Fields := ⟨10, hexnat% "29c9723c1f1d26c972729aa5aa9a368ba1e966a5876a386e8789e1783e745b15c5c96a569a6659366392e47959695956351d68d9362d1b61d2745d0f5c368d63a4d9354cd34ccb31ce8b62d4b32d2b2ac6b86c9b16c3ba1d4749c6785c9783c8f07c560d84e0ba91a2615154358344d0b58350d2324c530cc8b12c2b11c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db6db6db69a6d26db6d36db69249249a49249249249249a49a492491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨73, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨84, by decide⟩, ⟨86, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3020005f3e7ddd6000000", hexnat% "5000008800000000000000", 3404087999594496, 8070450532382146560, hexnat% "70000000020000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "500000887fed5df2000000", hexnat% "302000580000000000000", 20341166440448, hexnat% "70000000000000000", 8070450532247928832]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5000008876bfddce000000", hexnat% "302000580000000000000", 2603644339879936, 8070450532247928832, hexnat% "70000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100204780c3fdc5e000000", hexnat% "4300000000000000000000", hexnat% "38580000020000000", 1055531162664960, 31525203834044416]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "530203bd90205d6e000000", hexnat% "44000000010000000", 3404087999594496, 9219956902199296, 18865420509380608]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "530203bd90205cee000000", hexnat% "44000000010000000", 3404087999594496, 18865424804347904, 9219954754715648]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [9043263545571016704, hexnat% "78000000030000000", hexnat% "5300000000000042000000", hexnat% "2000008101000000000", 18865424804347904, 9219974082068480, 5638295627235328]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c9 c2
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c10 c1
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c11 c0
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record010_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record010_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00056.record010

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00056.record023
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record023
def vertexColumn : Fields := ⟨10, hexnat% "29c8f17272a9a2ea9655876a3a1e2783ee4571726998e4b9a55558d475a364d8b61d2743d70d63a4d534ccb31ce8b62d4b32cab86c9b0ee8751e1745c9715e0f23c1f1b1921a8660d84e0ba91646891a465854358344d0b58350c6344c930cc8b12c2b11c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db69b69369b4d249269249249249a4d2492489249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨66, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨74, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "442f434dbfc0000000", hexnat% "208008000000000000", hexnat% "4001004800000000000", 13528391068155904, 35184372088832]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "64815b8d8cc0000000", 1008806320825958400, hexnat% "4001004000200000000", 9024928879738880, 105553116266496, 2305843077933170688]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4400000008040000000", 1080863914863886336, hexnat% "248008000000000000", 13537324600131584, 3476778981049499648, 111052821889024, 2111122454872064]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record023_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record023_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record023_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record023_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record023_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record023_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record023_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record023_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record023_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00056.record023
