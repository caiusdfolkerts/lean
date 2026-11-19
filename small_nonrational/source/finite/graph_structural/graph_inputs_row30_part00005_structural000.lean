module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow30Part00005Data
public import GraphInputsRow30Part00005Frames
public import GraphInputsRow30Part00005Leaves
public import GraphInputsRow30Part00005Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00005.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record002
def vertexColumn : Fields := ⟨10, hexnat% "3a8e63389e3a4e53345d07ce8b92cca72aaa6aa6a5a8e87ae1b26a99a6c5a9665a364d876338ae1b89e1783ee8791cc571e2729aa5a9c6699666394e47969565655554d475334ad1b49d1743de0f23a8da3c4e9364e334cc73a2ccb8acab86c9b0ed8731d2729d1725c3723c4f0bc1fa2a2a1aa1a168661586916585494654545518c5322c4b0ac1b21c4709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6db6db49249b6db6da6d34db6db6db6da49249b4d36db6db692492492492492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨79, by decide⟩, ⟨81, by decide⟩, ⟨84, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4002800100a007fa0f000000", hexnat% "f800000000000000000000000", hexnat% "1000000c00000010000000", 25232932864, 17293822569102704640]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f80000000800003f88f000000", hexnat% "2800000a0040000000000", 31943819264, 8646911284551352320, hexnat% "401000010400000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fc01000010c0007ffff000000", hexnat% "2800000a0000000000000", 17293822569102704640]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10000104a0054fff000000", 17870283321406128128, hexnat% "200000000000002b000000000", hexnat% "400280000000000000000000", hexnat% "d800000000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4c01280010ca005ca1f000000", hexnat% "2000000000000023000000000", hexnat% "9000000000000000000000000", 25232932864, 17293822569102704640]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f80020000200003fa2f000000", hexnat% "800000a0040000000000", 9223372061550837760, 6629298651757805568, hexnat% "401000010000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800020000f8000157ff000000", hexnat% "280000000000002a000000000", hexnat% "800000a0040000000000", hexnat% "5400000000000000800000000", hexnat% "1000010400000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "bc012800000a007f28f000000", hexnat% "10c00000810000000", hexnat% "4000000000000000000000000", 2305843032299143168, 14987979559889010688]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200028000f8000157ff000000", hexnat% "104a0040000000000", hexnat% "880000000000002a000000000", hexnat% "5400000000000000800000000", hexnat% "1000000000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "28000a8000157e0000000", hexnat% "a80000000000002a000000000", hexnat% "5400000000000000800000000", 45035996525363200, 6052837899454382080, hexnat% "1000010000040000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c11 c8
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c12 c7
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c13 c6
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c14 c5
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c15 c4
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c16 c1
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c17 c0
  c18
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00005.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00005.record012
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record012
def vertexColumn : Fields := ⟨10, hexnat% "3b0ea3389e2b4ab23c1f392aca72e2aaa9ab1a9695a8e87aa98e6a59968d8b61da8e63a2e2b86e8791e1783ee8791cc6b16c789ca6a96a719566394e479395952d58d2b51d1743de0ea338f13a4d9354e332cc73c2e8b62d4b8acab1ae1b46c5b0ed8731ca719d1725c3743c8f0bc1f1d06ce0b12c2856138711a4a5194550d44d0b58344c5342c4b21c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6d26d369b6db6db4db69b4db6db6db6da4d34d24da69369349b4d2692492492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨79, by decide⟩, ⟨82, by decide⟩, ⟨87, by decide⟩, ⟨98, by decide⟩, ⟨101, by decide⟩, ⟨104, by decide⟩, ⟨105, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8000ab000017ff000000", hexnat% "8400000000408000000000", 1702181438750720, hexnat% "204000000010000000000000000", hexnat% "120000000000090200000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "124000000000090200200000000", 19008585728, 12177733399154262016, hexnat% "200008480000200000000000000", 1702181438750720, hexnat% "10000409000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c1 c0
  c2
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record012_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record012_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record012_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record012_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record012_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record012_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record012_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record012_validity Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00005.record012_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00005.record012
