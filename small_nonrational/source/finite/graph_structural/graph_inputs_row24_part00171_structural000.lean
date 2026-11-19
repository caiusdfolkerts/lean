module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00171Data
public import GraphInputsRow24Part00171Frames
public import GraphInputsRow24Part00171Leaves
public import GraphInputsRow24Part00171Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00171.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record000
def vertexColumn : Fields := ⟨10, hexnat% "cd23c4f3328e93ac9aa669b16959568d93633a2e4b8ae1ba1e4789e1783ecc6394e725a95a5c5655556354d4cd8b52d1b61d4749d0f723a8da3c4e5354e334cccb8ad2b1ae1b46c9b0ef07a1d8791d4731e2749ca719e1745c9715c3783d0f23c4f0bc1f2b05c2a85a2a4598952529615454552344d0b41d88d2328e1344c5322c4b0ac1b"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6db6db6da6db4db6924924924924924924924924db6da49a4d36d2489249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨83, by decide⟩, ⟨88, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1080000000001da3c000000", hexnat% "400040000000000000", 1010917378856321024, 8086213130943725568, hexnat% "e078000000000000000", hexnat% "70380000000000000000", hexnat% "1800180000000000000"]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00171.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00171.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record001
def vertexColumn : Fields := ⟨10, hexnat% "cca3a4eb26a99a6c5a56558ce8b92e2ba1e4789ecc6394e725a95a5c5655554cd8b52d2b61d4749dc8ea368f1394d538cd3332e2b4ac6b86d1b26c3bc1e8761e4751cc789d2729c9783d0f0bc5c2a85a859161588e1381e2a459855151548d1341d88d2328e1344c5322c4b0ac1b81d0721c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db4926d249b6db4926d2492492492492492492492491249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200020020802200000000", hexnat% "e1c000001000000000", hexnat% "e1c0000000000000000000", hexnat% "1000100000010c00000000", 4043176934216040448, 559290778724073472, 68994354642944]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record001_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00171.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00171.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record002
def vertexColumn : Fields := ⟨10, hexnat% "32cab1ac9723c4f0bc1f32aaa9aa96a3a4e8bac9aa669a568d9362db0ea398e9394e33a2e4b8ae8791e2785e0f9a98e5392e479696354d4b51d58d534cd8b52d2b46d8751d2745d0f5a38cd332cd8b52ccb8ad2b2ae1b46c9b0ed8751cc789d2729e1745c970de0f43c8f13c2f07e388d21a16a16159292a4590e525294550d45342c8b12c1b41c8711c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "db69b6db49b6da4db6db6db4da6924924936da4db6936da49a492492692493493449249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨79, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨106, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "408100090001861d374ce800000", hexnat% "2100000040100000000", hexnat% "2e0000000020000000", hexnat% "5c00000008000000000", hexnat% "4080000000000080200000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "408100090001861cb72ce800000", hexnat% "2100000040100000000", hexnat% "2e0000000020000000", hexnat% "5c00000008000000000", hexnat% "4080000000000100400000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "408100090001861c370ce800000", hexnat% "2100000040100000000", hexnat% "420000000000000000", hexnat% "2c0000000620000000", hexnat% "5800000188000000000", hexnat% "4080000000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7e01821dfc00e800000", hexnat% "400000090000040000000000000", hexnat% "1e0000000020000000", hexnat% "c000000000000000000000000", 235149459456, hexnat% "180000000000000100000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c1800942c100018f6ee800000", 500277790638080, hexnat% "120000000100000000", hexnat% "1800820000000000000", hexnat% "400000000000040000000000000", hexnat% "2400000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c180096500001c7852e800000", hexnat% "400000000001860000000000000", 492847497216, hexnat% "1800000180000000000", hexnat% "2e0000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7c81821df848e800000", hexnat% "400000090000040000000000000", hexnat% "c000000000000000000000000", hexnat% "360000000020000000", 490700013568, hexnat% "180000000000000100000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40800052c0801dff6ee800000", hexnat% "120000000100000000", hexnat% "2c00020000000000000", hexnat% "8100090000000000000000000", hexnat% "400000000001040000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "50000000477ee800000", hexnat% "2c00020008000000000", hexnat% "8100090000000000000000000", 522268023193600, hexnat% "404080000000000000000000000", hexnat% "3e0000000000000000", 1747396655419752448]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c11 c4
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c12 c3
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c13 c2
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c14 c1
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c15 c0
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00171.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00171.record007
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record007
def vertexColumn : Fields := ⟨10, hexnat% "2785d3329c9729aa9a968da8e87a59996558d64d87633a2e4b86ecc6715c669a6659366392e47959595554d54d4b51d4cd8b52d2b72398d63c4e9364e5354cd38cd331ce8b92ccb8ad2b1ae1b26c5b0ed8751cc789d2719d1725c570de0f43c2f1b08e13a314c4718a469494652344d0b61344c9314e0b22c4b41c8711c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6db6db6db4da4926da6936d34924db4924924924d249a49a492692249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨72, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨83, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1016290fffbddf7000000", hexnat% "800004000000000000000", hexnat% "10002800000000000000", hexnat% "e0000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "14000fcf3ddf6000000", hexnat% "900004000000001000000", 853221023154176, hexnat% "e0028000000000000000", hexnat% "203800000000000000", hexnat% "10000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1e06290ff8a4191000000", hexnat% "11002000000000000000", hexnat% "800004000100406000000", 104689827840, 107202383708160, 576460752303423488]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f14020ff8b4181000000", hexnat% "800004000100406000000", 106102872080384, hexnat% "229000000000000000", 576460752303423488, 104958263296]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "900006803fbdd87000000", hexnat% "51400000000000000000", hexnat% "229000000000000000", hexnat% "a0000000000000000000", 70931696010133504]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f162a0fefbdcf7000000", 6341068275337658368, hexnat% "900000000000000000000", 281479271677952]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4280fef3dcf6000000", hexnat% "900004000000001000000", hexnat% "e0000001000000000000", hexnat% "201000000100000000", hexnat% "10002800000000000000", hexnat% "1000000080000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "9e00240ff9a45d7000000", 103616086016, hexnat% "209000000000000000", hexnat% "1400000018000000000", 105553116266496, hexnat% "10002800000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "900005803fa5df7000000", hexnat% "20228000000000000000", hexnat% "11402000000000000000", 70933343398526976, hexnat% "c0000000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11060f803fa4197000000", hexnat% "800000004000400000000", hexnat% "e1000000000000000000", 104689827840, hexnat% "20000000000000000", 69807443491684352]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "9014040fff3d437000000", 39728447488, hexnat% "e0028000000000000000", hexnat% "10002000080000000000", hexnat% "201800000000000000", 2147483648]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "95140f817baddf7000000", 18085866765287424, hexnat% "20220000000000000000", hexnat% "80000080000000000000", 11258999068426240]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f142b813aac417000000", 89060441849856, hexnat% "900004000000000000000", 109521666048, hexnat% "200008000000000000", 64176296300642304]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11060f8038add97000000", hexnat% "800000004100000000000", 106652627894272, hexnat% "e0020000000000000000", hexnat% "1000000000000000000", 69805795834855424]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000780382c097000000", hexnat% "900000000000000000000", 125627793408, 133040906960896, hexnat% "e1400000000000000000", 70931694667956224, hexnat% "228000000000000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c17 c16
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c18 c15
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c19 c12
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c20 c11
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c21 c10
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c22 c9
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c23 c8
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c24 c5
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c25 c4
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c26 c3
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c27 c2
  c28
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record007_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00171.record007_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00171.record007
