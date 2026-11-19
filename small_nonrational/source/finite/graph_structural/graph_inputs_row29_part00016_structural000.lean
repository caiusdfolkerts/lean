module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00016Data
public import GraphInputsRow29Part00016Frames
public import GraphInputsRow29Part00016Leaves
public import GraphInputsRow29Part00016Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00016.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00016.record003
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
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10000104a00547ff000000", 17870283321406128128, hexnat% "400280000000000000000000", hexnat% "200000000000002b000000000", hexnat% "d800000000000000000000000", 34359738368]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4c01280010ca005ca1f000000", hexnat% "2000000000000023000000000", hexnat% "9000000000000000000000000", 25232932864, 17293822569102704640]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f80020000200003fa2f000000", hexnat% "800000a0040000000000", 9223372061550837760, 6629298651757805568, hexnat% "401000010000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a80020000000003f200000000", hexnat% "5400000000000000800000000", 12105675820920471552, 6052837899454382080, hexnat% "1000010000040004000000", hexnat% "800000a000000b000000", 2684354560]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00016.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00016.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00016.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00016.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00016.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00016.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00016.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00016.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00016.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00016.record003
