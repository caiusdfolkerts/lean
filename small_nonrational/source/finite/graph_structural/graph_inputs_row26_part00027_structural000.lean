module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow26Part00027Data
public import GraphInputsRow26Part00027Frames
public import GraphInputsRow26Part00027Leaves
public import GraphInputsRow26Part00027Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00027.record012
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00027.record012
def vertexColumn : Fields := ⟨10, hexnat% "aab1ac9956c38ce8b86e4789e0faa9c67255570d3362d1b51d2743dc8ea3c4d53c2e8b92ccb1ae1b46c9b0ef0761d4731e2749c6725c3783d0f2b05c8a8aa168a6458562384e0b81e8a4a9164a5454552344d0b41dc0e2328d1314e0b22c4b0ac1b41c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "4da6924926d3492492492492492492492489249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ffed56a1bffc000000000", 136233888727957504, hexnat% "200400000000000000", hexnat% "1001000000000000000", hexnat% "a8000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6ffdfea391cc000000000", hexnat% "800001102000000000000", 249589139505152, 55169095435288576, hexnat% "100200400000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7aaf72e1fffc000000000", 135107988821114880, hexnat% "8c000000000000000", hexnat% "54000000000000000000", hexnat% "801001000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "eabd73fff1dc000000000", hexnat% "54000000000000000000", 248489627877376, hexnat% "8c000000000000000", hexnat% "100200000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7aefffe1d5bc000000000", hexnat% "50000000000000000000", 180319906955264, 135670938774536192, hexnat% "801000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6aadffe1918c000000000", 253987186016256, 136796838681378816, hexnat% "100200000000000000000", hexnat% "801000000000000000000", hexnat% "54000000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c9 c0
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c11 c12
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c11 c13
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [hexnat% "d7f7fffffffc000000000", hexnat% "80800000000000000000", hexnat% "200000000000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c15 c14
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00027.record012_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00027.record012_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00027.record012_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00027.record012_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00027.record012_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00027.record012_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00027.record012_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00027.record012_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00027.record012_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00027.record012

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00027.record013
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00027.record013
def vertexColumn : Fields := ⟨10, hexnat% "bcaaa3a2eb262d876c398e538ce8b8ae4789e0faa98e4b9c94b51d70d6354d3362d2b51d2743dc8ea38ccb31ce8b62e4b52ccb8acab86d1b26c3bc1d8751cc789d2719d1725e0f0bc5cc285a298560d90e2384e07b09164a5154354348d1341dc0e2328c530ce0b42c8b12c1b41c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db49249a4936da4924d2492492492492492492492449249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fc37f86c60cc0e800000000", 4035228564658847744, 140456082098094080, hexnat% "790000000000000000", hexnat% "3c80000000000000000000", 65970697666560]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fa33f467f0c639800000000", 68539156829044736, hexnat% "398000000000000000", hexnat% "4000800000006000000000", hexnat% "1cc0000000000000000000", 30786325577728]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c2 c3
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c2 c4
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fb33f667e8e7ff800000000", hexnat% "4000800000000000000000", 104005003894587392, hexnat% "198000000000000000", hexnat% "cc0000000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fffff46fe0ef3b800000000", hexnat% "390000000000000000", hexnat% "800000004000000000", 13194139533312, 139893063425196032]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fbfffffe80f735800000000", hexnat% "400000020000a000000000", 1441151880758558720, 13194139533312, 139752325936840704]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fab7f577e2e7ff800000000", hexnat% "4000800000000000000000", hexnat% "288000000000000000", hexnat% "1480000000000000000000", 131026601658810368]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fa37f477e0e7b9800000000", hexnat% "388000000000000000", hexnat% "1c80000000000000000000", 4810363371520, 140033800913551360, hexnat% "4000800000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c11 c8
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c12 c7
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c13 c6
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c2 c14
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c2 c15
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c2 c16
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [hexnat% "1efde3fffffffff800000000", hexnat% "10200000000000000000000", hexnat% "1c000000000000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨89, by decide⟩ c18 c0
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c19 c17
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨91, by decide⟩ c20 c5
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨92, by decide⟩ c21 c0
  c22
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00027.record013_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00027.record013_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00027.record013_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00027.record013_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00027.record013_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00027.record013_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00027.record013_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00027.record013_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00027.record013_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00027.record013
