module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow26Part00024Data
public import GraphInputsRow26Part00024Frames
public import GraphInputsRow26Part00024Leaves
public import GraphInputsRow26Part00024Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00024.record045
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00024.record045
def vertexColumn : Fields := ⟨10, hexnat% "338ae1b8cd2745d0ecaca723caaa3ab1aa6a3a2ea6639b1695a361db0e33a2e2b86e6c5713c5a93a719665392e56539715555351d70d3352d2b46dc4f0b32e1b46c9bc1cc785d1715e0f43c8f13f303c328c930c8b12c34a0e3450d30c9314c8b11c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "9b4db6d36db6db6da69b6d36db6db6da69b6d369a6d2491249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩, ⟨29, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨49, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨69, by decide⟩, ⟨75, by decide⟩, ⟨78, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200002000000000000", hexnat% "48000000000000000000", 555876352, 67371008, 72057679937798144, 18014398510530560]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00024.record045_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00024.record045_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00024.record045_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00024.record045_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00024.record045_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00024.record045_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00024.record045_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00024.record045_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00024.record045_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00024.record045

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00024.record056
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00024.record056
def vertexColumn : Fields := ⟨10, hexnat% "338cd0ec37332aa8ea968da8eb2639b1635a364d8ce2b86e2785e0fb31ca4e9c64d98e539694e5554d54d4cd2b46d2745d0f72338f1334e334ce2b1ae1b26c3b49c6745c970dc8f13c2f07cca8a8aa8685a318a6158c92a4593152529515154c328c5322c4b0ac1b21c4709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6d24934d369369b69a6d24924da6d34da492492492449249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨48, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨66, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨73, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3e800510029f478000000", 153122423837818880, hexnat% "2000040000100000000", hexnat% "640019000000000000", 36028805608898560]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3e200504029f178000000", 45036007011123200, hexnat% "8000100000400000000", hexnat% "640019000000000000", 144115222435594240]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "806402b908fff8000000", hexnat% "220000000010000000000", hexnat% "108004100200000000000", hexnat% "42001040000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10a0043e028aff8000000", hexnat% "40001000000000000000", hexnat% "220000000011000000000", hexnat% "640019000000000000", hexnat% "80000000004000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c264105908e578000000", hexnat% "220000000011000000000", 153122423837818880, hexnat% "108004100200000000000", 36028805608898560]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10864433828adf8000000", hexnat% "42001040000000000000", hexnat% "220000000011000000000", 36310280585609216, hexnat% "80000000004000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2006402b921bff8000000", hexnat% "a0000000004000000000", hexnat% "42001040080000000000", hexnat% "108004100000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ea6402b928fff8000000", hexnat% "200000000010000000000", 90071992547409920, 5764607523034234880]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ea6402b928fef8000000", hexnat% "200000000010000000000", 4683743612465315840, 1170935907411296256]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "14a64033928acf8000000", 5764607523034234880, 54043208413347840, hexnat% "a0000000005000000000", hexnat% "200000000010000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2a064537929fcf8000000", 36028809903865856, hexnat% "108000000000000000000", hexnat% "42000000000000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "e064515928f478000000", hexnat% "300000000010000000000", 153122423837818880, hexnat% "a000000000100000000", 36028805608898560]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c14 c12
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10864431920ac78000000", hexnat% "a0000000005000000000", hexnat% "200000000010000000000", 45036007011123200, hexnat% "42001040080100000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "44023820ac98000000", hexnat% "a0000000005000000000", hexnat% "108004100000040000000", hexnat% "200200000010000000000", 54324679095091200, hexnat% "42001000080120000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c17 c16
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c18 c15
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c19 c11
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c20 c6
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c21 c5
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c22 c4
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c23 c3
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c24 c2
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c25 c1
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c26 c0
  c27
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00024.record056_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00024.record056_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00024.record056_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00024.record056_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00024.record056_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00024.record056_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00024.record056_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00024.record056_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00024.record056_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00024.record056
