module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00052Data
public import GraphInputsRow24Part00052Frames
public import GraphInputsRow24Part00052Leaves
public import GraphInputsRow24Part00052Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00052.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record000
def vertexColumn : Fields := ⟨10, hexnat% "bc1f07ae1aa669a6695876a398e938ae1b91e1783eb86c93a4b91e785a95a5996552d475a364d2b46d4749d1743de0ea368e6394e8b62e4b52cab1ad1b0ef07a1d8791e2749ca719e1745c5783c8f13c2f63072168364381e1c58916685614a50d50d2341d90c6314c3342c4b06e0741c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "369b6da69b6926db4926d24d34926da4d24d2492492492492249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨82, by decide⟩, ⟨84, by decide⟩, ⟨90, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40073af02077ef0000000", hexnat% "70000000000000000000", 7212796278210560, hexnat% "40000800000080100000000", hexnat% "1000000000008000000000", 17592186044416]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "460000a03bb13f0000000", 6755983556608000, hexnat% "1000010000000000000000", hexnat% "40010802100000000000000", hexnat% "728400000000000000", 4827543240704]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400000802111040000000", hexnat% "70000000000000000000", 7212796815081472, hexnat% "72a400000000000000", hexnat% "1000010200080900000000", hexnat% "40000800100000010000000", 7587059728384]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00052.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00052.record037
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record037
def vertexColumn : Fields := ⟨10, hexnat% "6707ce2a6a6693a1eac6658d62d876a398e9386e4789e1783eb47899a699666594e479b1595354b5a358d9346d4749d17783b0e6364d5334d332cc73c2e8b62e4b8ad2b1ad1b26c5b0ee8761e4731ca745c9715c3783d0f23c4f07c740f0660b9911c5190e465254550d42d0768360e4318e0b42c2b21c4709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1a6db6db69b69b69b6d349a49b6924924db69249249b49249a492491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨73, by decide⟩, ⟨78, by decide⟩, ⟨82, by decide⟩, ⟨86, by decide⟩, ⟨96, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40429c3886b481f2000000", 216524694554148864, 288230840142397440, hexnat% "1000400404000080004000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40429c7886348dfe000000", hexnat% "1000400400000480000000000", 288653000933638144, 216172850833260544]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1004440c46c867cfdfe000000", hexnat% "2001001800000000000", 216172782113783808, hexnat% "180000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "44400444840cfdfe000000", 216559810206760960, hexnat% "183800000000000000", hexnat% "1000000400000000000000000", 721279627821056, hexnat% "2800000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000400404f037c7dfe000000", hexnat% "4040000084008000000000", hexnat% "1c3000000000000000", hexnat% "2800000000000000000", 140737488355328]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000402c07f037c5436000000", 140875061526528, hexnat% "800000009c0000000", hexnat% "4040000084008000000000", hexnat% "140000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10044404c59844c9dce000000", hexnat% "2102000000000000000", hexnat% "800000100000000000", 432627451521138688, 738872619171840]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4042903c84c4e5c6000000", hexnat% "1000400404000080000000000", 216172885192998912, hexnat% "c0000000000000000", 897202427789312]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [109295941994938368, hexnat% "2803000000000000000", hexnat% "1004440004000000040000000", 432346010904166400, hexnat% "1c0800000100000000", 1037939916144640, hexnat% "400000008000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c11 c6
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c12 c5
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c13 c4
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c14 c1
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c15 c0
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record037_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record037_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record037_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record037_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record037_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record037_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record037_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record037_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00052.record037_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00052.record037
