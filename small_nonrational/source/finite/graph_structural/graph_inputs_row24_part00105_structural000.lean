module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00105Data
public import GraphInputsRow24Part00105Frames
public import GraphInputsRow24Part00105Leaves
public import GraphInputsRow24Part00105Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00105.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00105.record001
def vertexColumn : Fields := ⟨10, hexnat% "2ac4f2aa4eaa655936a38ce8b92e2b86e4789e0faa94e6a555535a34cd8b52d2b46d4749d0f723a8d534ce4b32d2b2ac6b86d1b26c3ba1d8751cc789ca719c970de0f43c5ca2a2a16926458562384e0b81ea262916525454552344d0b41da0e2348d1314e0b22c4b0ac1b41c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "da6d249249249b492492492492492492492492491249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6f20bc837ff29e000000000", 235295488344064, hexnat% "10084020800000000000000", hexnat% "800200000000000000000", hexnat% "15c000000000000000", hexnat% "570000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ca872a18718e4000000000", 112027178169794560, 124794569752576, hexnat% "2000800400000000000000", hexnat% "15e000000000000000", hexnat% "578000000000000000000", hexnat% "1000400200000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6f12bc4a64521a000000000", 1157436099350495232, 233371342995456, hexnat% "10004000928000000000000", hexnat% "3b4000000000000000", hexnat% "ed0000000000000000000", 36591746972385280]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6f32bc4a64521a000000000", 1157436099350495232, 233371342995456, hexnat% "cd0000000000000000000", hexnat% "10004000928000000000000", hexnat% "3b4000000000000000", 36591746972385280]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7cb872a18718e4000000000", 112027178169794560, hexnat% "478000000000000000000", 124794569752576, hexnat% "2000800400000000000000", hexnat% "15e000000000000000", hexnat% "1000400200000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6f12bcca64521a000000000", 1157436099350495232, 233371342995456, hexnat% "334000000000000000", hexnat% "10004000928000000000000", hexnat% "ed0000000000000000000", 36591746972385280]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨89, by decide⟩ c9 c2
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c10 c1
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c11 c0
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00105.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00105.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00105.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00105.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00105.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00105.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00105.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00105.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00105.record001_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00105.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00105.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00105.record003
def vertexColumn : Fields := ⟨10, hexnat% "2783d2acaca723caaa9ab1a9695a8e87aa98e665956358b61da8e53a2e2b86eac4f1aa5598e5391e4e565555355352d4755352d2b6a338e9364d5334e332cc73a2d4b8acab1ae1b46c5b0ed8751cc729c6745c9715c3723c2fac06ca490e138b11c469294654344d0b51324c5342c4b41c8711c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36d36db6db6db6db4da49b6d26db4924da49349a6d349a492493489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨71, by decide⟩, ⟨89, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200001030780c25f2c00000", hexnat% "800000410000000000", hexnat% "c0080000000000000", 175956354400256, 281475043819520]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20000880021ed0c9e000000", 5918162944, 1159676904047902720, 2323857545162129408, hexnat% "100000000000000000", hexnat% "40080000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200001c2041ec2432400000", 40936407040, 1159676904047902720, hexnat% "800020010000800000", 36028797086072832, 1073741824]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "801038450dfec00000", 466192930177024, hexnat% "20000100000002000000000", hexnat% "42040000000000000", hexnat% "80080000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200001010b84c21f4c00000", hexnat% "80001000000000000", hexnat% "800000010000000000", hexnat% "42040000000000000", 175922028216320, 51539607552]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "41001ec0dfec00000", 2323857545162129408, hexnat% "80080000000000000", 15762598695796736, hexnat% "20000100000000000000000", hexnat% "800000010000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c10c9ec00be000000", 13510798894694400, 2305843060753301504, 5368709120, hexnat% "20000100000002000000000", hexnat% "800000010000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200009020e06d24b2c00000", hexnat% "80001000000000000", 140776277278720, 1159676904047902720, hexnat% "40000000040000000", 67108864]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "410b86425fec00000", 2323857407723175936, 1133871366144, 431008558088192, hexnat% "20000080000000000000000", hexnat% "900000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200000800816c20f0000000", 2305843060753301504, 1159676904052097024, hexnat% "40040000000000000", hexnat% "900020000000000000", 140742018203648, 1099520016384]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c11 c6
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c12 c5
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c13 c4
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c14 c3
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c15 c2
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c16 c1
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c17 c0
  c18
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00105.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00105.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00105.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00105.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00105.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00105.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00105.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00105.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00105.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00105.record003
