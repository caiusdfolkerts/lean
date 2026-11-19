module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow16Part00002Data
public import GraphInputsRow16Part00002Frames
public import GraphInputsRow16Part00002Leaves
public import GraphInputsRow16Part00002Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00002.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record001
def vertexColumn : Fields := ⟨10, hexnat% "f42f16a2e8b61db0e538ae1b89e0f8f1e26a95a4b9d14e5a54d52d475c354d2b46d2743d58d532cf0b52d2b2ac6b26c3bc1d4729c6725c3783d0f23c4f0bc1fa3072158b11c709a24a9a14951560d2354318c530cd0b0ac4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db4db6da49a6d24934d349249269a692492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨67, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [874440911176597504, 1224979115824644096, 7881299616333824, 13817983533056, hexnat% "80000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [87996413090201600, 577024801768472576, 13812614823936, 1154049603536945152, 288230513590665216, hexnat% "80000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [15797783642505216, 865254078408556544, 1374599249920, 1224981314847899648, hexnat% "80004040050000000", 9418880057344, 140874927308800]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record001_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00002.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00002.record039
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record039
def vertexColumn : Fields := ⟨10, hexnat% "34aa6b862db0ea394e1b89e17b49a67852d70da354d1b49d17783d0e932cf0ba2e4b52e2b1ae1b26c5bc1e8761cc749ca719d1715e0f43c8f0f03a518960d84e0b81e0e545254351342d07703a0d4324c3382c4b0ac1b41c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db4da4936d3692492492492492492492489249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨61, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨71, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "84211b7d1740000000", 28149696694321152, 468374363394015232, hexnat% "1a0000000000000000", 996432412672, 140737488355328]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "180667abffc0000000", 2413929400270585856, hexnat% "860000000000000000", 6772991627100160, 74766790688768]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "802008081e00000000", 252201580206489600, hexnat% "100400804080000000", hexnat% "e0000000000000000", 22519647404294144, 9009535716950016, 2097872480763904]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record039_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record039_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record039_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record039_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record039_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record039_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record039_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record039_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00002.record039_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00002.record039
