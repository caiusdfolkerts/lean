module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow16Part00030Data
public import GraphInputsRow16Part00030Frames
public import GraphInputsRow16Part00030Leaves
public import GraphInputsRow16Part00030Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00030.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record006
def vertexColumn : Fields := ⟨10, hexnat% "9b19c4f26a668ba999969598e93a2e1b91e2783e665392e665656558d5356354d4b46d4749d0f66364e538ccb362ccb2ac6b46c9b0ed8791e2719e1745c9715d0f23c1f8d23291a26858361382e64589454354344d0b4930cc8b12c2b11c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db4d34936936d34924934d349249a4d2492492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [6918285327207497728, 16888498602639360, 54043196602187776, 144115188075855872, hexnat% "8e0000000000000000", hexnat% "200000000208000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ae6226a25bff000000", 1649267441664, 6755399441055744, 13194139533312, 54043195528445952]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ae6004804bff000000", 36037593111986176, 3917010173952, 16325548649218048, 39582418599936, 162129586585337856]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ae6082881bc9000000", 4123269267456, 39583223906304, 16888498602639360, 162129586585337856]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ae42ce804bff000000", 13194139533312, 13510798882111488, 3917010173952, 2305878193585782784]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8e42c6ae4bff000000", hexnat% "200000000000000000", 1717986918400, 15762598695796736, 2305843009213693952]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8e627e03dbb7000000", 39582418599936, 36169534507319296, hexnat% "200000000048000000", 8796093022208]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ae4064004bef000000", 3917010173952, 7459086882832384, 36037593111986176, 2449993381661638656, 4398314946560]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ae4000000880000000", 36037607070629888, 4191921635328, 2449993381661638656, 17451448623169536, 4399002812416, 18155135997837312]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c13 c4
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c14 c3
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c15 c0
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record006_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00030.record006

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00030.record018
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record018
def vertexColumn : Fields := ⟨10, hexnat% "9e25c1f2726aa6a96a3a1e99695876a3a4e1ba1e1783e5c5a996479656551d64d3346d8745d0f5a364e531cd8b92d2b2ac6b86c5b0ed8791c6785d1725c570de0f13c2f07e549313285a0e239311c4691548d1358348d130cc8b0ac8705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "69b6db6d349a6d369a49269a4d26926d26d2492491249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨57, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨74, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [164383585422278656, 14987979559905787904, 27492085661696, 2040693589540864, hexnat% "4020010000000000000", 489630466048, 1042284544]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record018_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record018_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record018_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record018_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record018_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record018_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record018_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record018_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00030.record018_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00030.record018
