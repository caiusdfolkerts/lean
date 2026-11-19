module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow16Part00003Data
public import GraphInputsRow16Part00003Frames
public import GraphInputsRow16Part00003Leaves
public import GraphInputsRow16Part00003Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00003.record020
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record020
def vertexColumn : Fields := ⟨10, hexnat% "1f38a1eb26a5876c3a8e4b86e2785e0fb891e725a5475c368d4b46d2745d0f783c8d63a4cd31cf0ba2d8b2ac6b46c5b0ef07a1e4789d2785c970de0f43c8f13d2a268661582e07929264651542d07703a0d2318c9314d0b22c2b06e0711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6da6d24936da6d2492492492492492492492449249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨60, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨72, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200207ff85f8000000", 6755846117654528, hexnat% "80080000000000000", hexnat% "140140000000000000", hexnat% "1021020000000000000", 77309411328]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "30031c0cfff8000000", 125344325566464, 845524441759744, hexnat% "40040000000000000", hexnat% "80080000000000000", hexnat% "1021020800000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400537bfff8000000", hexnat% "80080000000000000", 3382097767038976, 225179981368524800, hexnat% "320000000000000000", hexnat% "1001000800000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "13e103bff8bf8000000", 1125917086711808, 54043195528445952, 216172782113783808, 481036337152]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10213fbff8bf8000000", 1125917086711808, hexnat% "c0000000000000000", hexnat% "300000000000000000", 481036337152]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2003bff8bf8000000", 1125917086711808, hexnat% "80080002000000000", hexnat% "200200004000000000", hexnat% "1001000001000000000", hexnat% "140140000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [3474516873314304, 879613597188096, 4504081737449472, hexnat% "200200048020000000", hexnat% "80080030010000000", hexnat% "1021020800088000000", hexnat% "140140000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c9 c2
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c10 c1
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c11 c0
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record020_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record020_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record020_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record020_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record020_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record020_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record020_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record020_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record020_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00003.record020

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00003.record025
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record025
def vertexColumn : Fields := ⟨10, hexnat% "7ce296a4e87ac9a961db0ea392e1b89e1783ee25694e479c96951d70da352d1b49d1743de0f2358e934ccb31cf0ba2d8b52ccb4ac6b46c5b0ef07a1e4789d2785c9715e0f43c8f0bc9a198361381e264650d44d07703a0d2318c930cd0b22c4b06e0711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db4db4926db6d36d2492492492492492492492491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨61, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨75, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8b022db836362000000", hexnat% "400100008004000000", 136339844497408, 10133204388282368, 17179869184]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400100800844000000", hexnat% "8202080004022000000", 1442559255642112, 7318362279378944, hexnat% "900240032000000000", 9007287570006016, 101704959787008]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c1 c0
  c2
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record025_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record025_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record025_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record025_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record025_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record025_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record025_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record025_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00003.record025_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00003.record025
