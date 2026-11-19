module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00083Data
public import GraphInputsRow29Part00083Frames
public import GraphInputsRow29Part00083Leaves
public import GraphInputsRow29Part00083Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00083.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record000
def vertexColumn : Fields := ⟨10, hexnat% "370da2b89e0f8d51743d34c5b0ec970dc2f07cd49723cb4a5a8ea968da2e87a558d6538ce2785ed8751cc6b19c571d2729aa6695a699966392e479d15a559715955554d4b51d70d9354d4b4ad1b61d2745d0f74368d63c4e5354d332cc73c2e4b52d2b2ac6b86c9b16c3b61d4745c5743c4f07f609c268518961588e13b218c4b18a4a92548d24c8b41c8705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "24d36db6db6db6db6db4924934936926da4db6db69b6da6d36db6db4db6d369b492491249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨30, by decide⟩, ⟨33, by decide⟩, ⟨39, by decide⟩, ⟨49, by decide⟩, ⟨52, by decide⟩, ⟨58, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨109, by decide⟩, ⟨111, by decide⟩, ⟨112, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80002008240000000", 292733975779082240, hexnat% "c6100000000000000000", hexnat% "f400000000000000000000", hexnat% "1a000000221000000000000000000", 266338304, hexnat% "800000000000000000000"]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00083.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00083.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record003
def vertexColumn : Fields := ⟨10, hexnat% "5d0f45b0ec570dcd8b526c972d29aa5a99a56a66599564d8b61d94e4b8ae1b91e17b61d45713c7495a4e9564d9994e5354b51d4cd2b46dd0f23a8e6358f1394d534ccb31cf0b92d4b4acab1ad1b16e4789c6715c3713c2fd81582705cc891a268a62588e07a612645929465254552344d0762328c9322c1b21c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db4936db6936da6da6926db6d24924926926db69b6da693492489249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f1f9ff8fcff8fff97c0000000", 31525231751331840, hexnat% "c00000030000000000000000", hexnat% "200001000000000000000000", hexnat% "6006000000006000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f1f9ff8fc7bafff9fc0000000", hexnat% "1008010000000000000", hexnat% "400000010400000000000000", hexnat% "200000000040000000000000", hexnat% "6006000000006000000000", hexnat% "800000020000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f1f9ff8fc5fafff9fc0000000", hexnat% "1008010000000000000", hexnat% "400000012000000000000000", hexnat% "200000000040000000000000", hexnat% "6006000000006000000000", hexnat% "800000020000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f3fbeeafcdbbfffbfc0000000", hexnat% "110000000000000000000", hexnat% "4004000000004000000000", hexnat% "1020040000000000000", hexnat% "400000012400000000000000", hexnat% "800000000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fffbffbff7fffffffc0000000", 9223372036854775808, hexnat% "4004000000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [hexnat% "fffffffffffffffffc0000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fffbfebffffffbeffc0000000", 71468255805440, hexnat% "4004000000000000000000", hexnat% "10000000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f3fbeebfefdffbeffc0000000", hexnat% "4004000000000000000000", hexnat% "100000000400000000000", hexnat% "10000200010000000000", hexnat% "c00000010000000000000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f3fbffafc39dfbeb7c0000000", hexnat% "4004000000004000000000", 9078701870284800, hexnat% "1008000000000000000", 5044031582654955520, hexnat% "c00000030000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fdf9feeff7d8ffe9740000000", hexnat% "1008010000000000000", hexnat% "10000200010000000000", hexnat% "6000000000006000000000", hexnat% "200000000000000080000000", 27021632123961344]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f7f9fe9fefffffedf40000000", hexnat% "10000000010000000000", hexnat% "800000010000002000000000", hexnat% "2002000000000080000000", hexnat% "4004000000000000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c17 c4
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c17 c18
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c17 c19
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c17 c20
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c17 c18
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c17 c22
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c17 c23
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fffbfffff7fffbeffc0000000", 9223372036854775808, hexnat% "4000000000000000000000", 71468255805440]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c25 c24
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c26 c21
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ffffeefff39ffbeff40000000", 13835058055282163712, 432345566375051264, hexnat% "100000000400000000000", hexnat% "10000000010000000000"]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c28 c27
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fff9ee9fed9ffbedf40000000", hexnat% "100000000400000000000", hexnat% "10000200010000000000", hexnat% "12400000000000000", hexnat% "6006000000002000000000", 2147483648]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c30 c29
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c31 c16
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f5f9ff8fc09cfbe9740000000", 9078701870284800, hexnat% "1008010000000000000", 8502796096475496448, hexnat% "6006000000006000000000", hexnat% "200000000000000080000000", hexnat% "800000030000000000000000"]
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c33 c32
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨94, by decide⟩ c34 c15
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c35 c14
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c36 c3
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c37 c2
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c38 c1
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c39 c0
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c40 c0
  c41
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00083.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00083.record003
