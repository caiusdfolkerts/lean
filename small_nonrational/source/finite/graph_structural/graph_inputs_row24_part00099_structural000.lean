module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00099Data
public import GraphInputsRow24Part00099Frames
public import GraphInputsRow24Part00099Leaves
public import GraphInputsRow24Part00099Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00099.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record000
def vertexColumn : Fields := ⟨10, hexnat% "3d0ec4f0bcb8ab23caaa3a99a2e8e635a362d876538ce2b86e4789e0fae1ac4f1aa4e94e4b98d5351d54d4b51d0f6c3a8e6338f13a4cd38ccb31ce8b52ccb8acab1ad1b26c3b51e2719e1715c370bc1fac0e81b292329164384e8c469195150d50d1342d84d1342c4b41c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "69b69b4db6db49a4db4da6d24924db6934db49b49b4d2492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨60, by decide⟩, ⟨63, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨79, by decide⟩, ⟨82, by decide⟩, ⟨86, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "9083f84888bf000000", hexnat% "80000000400000000", hexnat% "400000000200000000000", hexnat% "4080400000000000000000", 1152921779484753920]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "980278008ca3000000", 108086391258218496, hexnat% "4080400000000000000000", 10376329000711618560, hexnat% "400000000080000000000", 70369012613120]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4809800f8088caf000000", 216172782382219264, hexnat% "4000400000000000000000", 105553116266496, 10376293816339529728]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4801093c86848bf000000", hexnat% "4000400000000000000000", 13510798882111488, 566935683072, hexnat% "880000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4801000c8680cbf000000", 85568392920039424, hexnat% "4000001000000000000000", 9367487224930631680, hexnat% "880000000000000000", hexnat% "40000000c000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "801f80004af000000", hexnat% "c0000000c000000000", 114349477724160, 9367487224930631680, hexnat% "4080101000000800000000", hexnat% "400000000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [141863388832595968, hexnat% "80000000481000000", hexnat% "4080101000000800000000", hexnat% "400008000280000000000", 70369213939712, hexnat% "c0000000c000000000", 144115188075855872]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c10 c3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c11 c2
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00099.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00099.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record001
def vertexColumn : Fields := ⟨10, hexnat% "2f0ab13c1f2e2b4ab29c8f2aa8ea5687aa9b168d876a3a2e2b86e4785e0fab13c5594e479a96354d4754b4ad1b51d1743da8ce3a4d5334e332cc7362d4b2ac6b46c5b0ee8789ca719e1715c3723c4f0bc1f3a23432a164590e38471324a91a5150d50d0b4c344c5342c8b12d0705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6db69b6936db4db4da69249269a6936924926db692492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffb9f7ffee98cff6000000", hexnat% "42000001040000000000", 3504844308480, 105553116266496, hexnat% "4080000000000000000", 4503599627370496]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fffbfffaffbcff9b000000", 360287970189639680, hexnat% "4000000000060000000", 3298601992192, 70368744177664]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffb9ffffbffd7fb7000000", 2748913287168, 18014398509481984, hexnat% "6000000000040000000", hexnat% "40000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c4 c5
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c4 c6
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffffff7bffbfffbf000000", 9223372036854775808, 70369817919488, 288230376151711744]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fff9ff7bffbbffbf000000", 9223376434901286912, 70369817919488, hexnat% "2000400000000000000", hexnat% "4000000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffffff7effbcffdf000000", 9295429630892703744, 70369281048576, 3298534883328]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c4 c3
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffbbfffaffffffff000000", hexnat% "4000000000000000000", hexnat% "40000000000000000000", 360287970189639680]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffbfff7afffd3ff7000000", 360287970189639680, 9223372311732682752, hexnat% "40000000008000000000", 2199157473280]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffbbff7ebff83fd7000000", hexnat% "4000000000020000000", 18015223277420544, 9295434028939214848, hexnat% "40000000000000000000", 3298534883328]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c19 c12
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c20 c11
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c21 c2
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c22 c1
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffbdff7ffe983ff3000000", 9223693369127993344, 3848492023808, 70368744177664, hexnat% "42000000000000000000"]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffb9fff97ffc7fa1000000", 180143985094819840, hexnat% "2000400000050000000", hexnat% "4000000000000000000", hexnat% "40000000008002000000", 3298736209920]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffb9f778fe980f8a000000", 504403158533931008, 9223693369127993344, hexnat% "4080000000041000000", hexnat% "42000000008000000000", 3504760422400, 70369281048576]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c26 c25
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c27 c24
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c28 c23
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c29 c0
  c30
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record001_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00099.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00099.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record002
def vertexColumn : Fields := ⟨10, hexnat% "2f0ad0f43b13c1f2e2b4ab29c8f2aa8ea5687aa98e6a58d68d8b61d98e338ae1b91e1783eb8671aa4e9565391e6a5396354d4753352d2b46d4745d0f6c3a8e6338f1394d538cc73a2d4b32e2b2ac6b46c5b0ee8731e2729c6785c570dc8f13c2f07ce82b0ca4590e23a311c469454354342d84d1314d0b12d0705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db4db6db69b6db6da49a6da69b4da49a4934db69249a4da49b6db492491249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨63, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨72, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨86, by decide⟩, ⟨95, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40140401e80d9003e00000", hexnat% "1008000000c00000000", hexnat% "800008000400000004000000", hexnat% "101800000000000000", 123145436528640]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1149468059c01e00000", 648518346341351424, hexnat% "1c000000000000000000", hexnat% "800000000080000000000000", 131941630214144, hexnat% "4000000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800008149dc87c1c0ee00000", hexnat% "1000020000000000000", 1649284218880, hexnat% "4004000000000000000000", hexnat% "10000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800008149dc87c1c0ee00000", 1649284218880, hexnat% "1000020000000000000", hexnat% "4004000000000000000000", hexnat% "10000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8000080485c87d9c0fe00000", 585467951558164480, hexnat% "101000000000000000", hexnat% "4004000000000000000000", hexnat% "11000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8040080485c860900cc00000", hexnat% "11000000000001200000", hexnat% "101800000002000000", 18743237279744, 9007199254740992, hexnat% "40000000c0000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8000000480c0000000400000", hexnat% "11000000000001200000", 659777345409777664, 1735175176192, hexnat% "1014000c0002000000", hexnat% "400c000000000000000000", 123179863375872]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c10 c1
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c11 c0
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00099.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00099.record008
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record008
def vertexColumn : Fields := ⟨10, hexnat% "ec372e23a95aa98e61da8e338ae1b85eb84e9564d9394d51d68d634cd2b46d2745db0ea398ce354c73a2d4b32cab1af07a1cc749ca719e1715c3783c8f13c2fa911c4685a899164381ea84e13251916685894a54550d2341d88c6344c5342c4b06e0741c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6936db6924936924d269249a4d24d2492492249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "127a213bff00000000", 3377699720527872, hexnat% "200050000000000000", hexnat% "20000000800000000000", hexnat% "40400000000000000000", hexnat% "c0100000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000007c9bff00000000", hexnat% "40400000000000000000", hexnat% "40001200000000000", 8791026472627208192, hexnat% "320000000000000000", hexnat% "80100000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20027a7da9bf00000000", 20066087206912, hexnat% "300000000000000000", hexnat% "40400000000000000000", hexnat% "c0100000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "404c7b3da0bf00000000", hexnat% "320000000000000000", hexnat% "20000040090000000000", 20066087206912]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "404e733dbbff00000000", hexnat% "20000040000000000000", hexnat% "300800000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20324b7dbbff00000000", 3458764513820540928, hexnat% "c0000000000000000", hexnat% "40400000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2020437dbbff00000000", 4035225266123964416, hexnat% "40080000000000000000", hexnat% "140000000000000000", hexnat% "420000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3e7b7db1bf00000000", hexnat% "40400000000000000000", hexnat% "20000000080000000000", 2473901162496]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20326a7db9b700000000", hexnat% "40080000000000000000", hexnat% "41100000000000000", hexnat% "400000000000000000", 2508260900864]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4028423db0b300000000", hexnat% "141000000000000000", hexnat% "420100000000000000", hexnat% "20000040090400000000", 2508260900864, 2882303761517117440]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c13 c8
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c14 c3
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c15 c2
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4008000d001100000000", hexnat% "20000050890400000000", hexnat% "200020000000000000", hexnat% "42110000a200000000", 7638104968020361216, hexnat% "140000200000000000", 20100446945280]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c17 c16
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c18 c1
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c19 c0
  c20
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record008_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record008_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00099.record008

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00099.record013
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record013
def vertexColumn : Fields := ⟨10, hexnat% "ae0f43b0bc6c8f2b28eaa68ba598e6359362d8763392e2b86e8789e0fab13c6c9aa4e9a66392e5651d52d8743db0d6338f13a4cd34ccb31ce8b92ccb4acab1ae1b26c3b51d2719e1715c3783d0f0bc1f3a1341b292a28ca4584e4c46949465454351342d84d1382c4b41c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6d36d24db69b4da6db6da6da49a6da4d36926d26d2492492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨60, by decide⟩, ⟨68, by decide⟩, ⟨71, by decide⟩, ⟨74, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨85, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2100101000002000000000", hexnat% "280000000040000000000", 422282258284544, hexnat% "800000030000000000", 130604395938185216, hexnat% "4000000200000000000", 9344909312]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record013_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record013_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record013_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record013_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record013_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record013_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record013_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record013_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00099.record013_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00099.record013
