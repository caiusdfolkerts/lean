module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow31Part00003Data
public import GraphInputsRow31Part00003Frames
public import GraphInputsRow31Part00003Leaves
public import GraphInputsRow31Part00003Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00003.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00003.record000
def vertexColumn : Fields := ⟨10, hexnat% "3b0ba1d8b91d43b0dcf0ba2b8b9274b32ac9b2b29caaaa6a3a99a568da2eac671aa6998e665956358b6338ae1b89e17bc1e86e1e45d1cc6b16c6c9726a99a4e966559364b9b15c5a966539595554d52d4cd2b46d2745dc8e63c4d538cd3392d4b8ac6b46c5b91d4789c6745c57f00b82d0cc2b09c0f3420e8361382e07b410e4351342d0770390d4388d130cc4b0ac1b11c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6d24db6db6db6db4db6db6924926db6db6db6da6db6db492492492492492492249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨64, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨95, by decide⟩, ⟨111, by decide⟩, ⟨112, by decide⟩, ⟨113, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10000000200000007ffff00000000", hexnat% "1000100e8000000000000", hexnat% "8000807400000000000000000000", hexnat% "20000000800000010000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000100e8400000000000", hexnat% "8000807400000000000000000000", 194072392237056, 846658313125888, 13679470837760, hexnat% "10000000200000004000000000000", hexnat% "20000000800000010010400000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c1 c0
  c2
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00003.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00003.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00003.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00003.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00003.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00003.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00003.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00003.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00003.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00003.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00003.record005
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00003.record005
def vertexColumn : Fields := ⟨10, hexnat% "3e0f43b0dc2f07c3c8ea368ba1e8e6358b61d8e9394cd2b46d274e332cab1ac9b31ca719c97362d4b326ca725cb4aca9aa9a96ac699a9695ac99a699b1665a568d9362d876c398e93a2e4b8ae1ba1e4789e17ae1786d1746b16c6715c4f1b25c9aa5a99a5693a69966659564d9a9665a56558d4b51d68d9362d2b46d8749d175a358d9354d332cc7362d4b4acab1ad1b26c5b29c6725c570dc8f13c2f07fa0d8390d4388d22a4a528c58952528a52548d18c5312c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "924da49b49b49a6d34db4da4db49b69b69b6db6db6db6db6db6db6db6db6db6db4d369a6d369b4d369a6d3692492491249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨33, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨46, by decide⟩, ⟨49, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨102, by decide⟩, ⟨106, by decide⟩, ⟨110, by decide⟩, ⟨111, by decide⟩, ⟨115, by decide⟩, ⟨116, by decide⟩, ⟨119, by decide⟩, ⟨123, by decide⟩, ⟨125, by decide⟩, ⟨128, by decide⟩, ⟨130, by decide⟩, ⟨131, by decide⟩, ⟨134, by decide⟩, ⟨135, by decide⟩, ⟨138, by decide⟩, ⟨139, by decide⟩, ⟨140, by decide⟩, ⟨143, by decide⟩, ⟨144, by decide⟩, ⟨145, by decide⟩, ⟨146, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "79ccd2898c4400000000000424a5242600000", 343932928, 725079540006649856, 687865856]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "79ccd28808440000000000a5240426b600000", hexnat% "184000000000000000000000000000", 343932928, 11063835754496]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "79ccd2018c440000000000042004002000000", 11073499430912, hexnat% "8800000000000000a10000000000000", 694157312, 343932928, 70368744177664]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨102, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨106, by decide⟩ c4 c0
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "79c400818c4400000000000020a1200400000", 276295581696, hexnat% "d20800000000000000000000000000000", 18014399230902272, 725149908750827520, hexnat% "8000000000000000000000000000200000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "71ccd28800440000000000a10400040200000", 18577349150769152, hexnat% "80000000000000000a5000000000", hexnat% "800000184000000000000000000000000000", 381681664, 8589934592]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "180410098c4400000000000400a5256800000", 694157312, hexnat% "8000000000000000a12000000000000", hexnat% "88c20000000000000000000000000000000", hexnat% "6140000000000000000000000000000000000", 70368744177664]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10c0d288004000000000000020a5254c00000", 723517440, 743164307260309504, hexnat% "18c040000000000000000000000000", hexnat% "610c000000000000000000000000000000000", hexnat% "800000000000000000000000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "794c00098c4400000000000004a5240200000", 381681664, hexnat% "80c28000000000000000000000000000000", 18577349150769152, hexnat% "100000000000000000a10000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "79ccc28984400000000000002004200400000", hexnat% "80400000000000000a1000000000", 379584512, hexnat% "100000000000000000a50000000000000", 70369432043520, 1073741824]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10440008004400000000000000a5240000000", hexnat% "80000018c000000000000000000000000000", hexnat% "6188000000000000000000000000000000000", 383778816, hexnat% "d28000000000000000000000000000000", 743727257213730816, 687865856]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨138, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨134, by decide⟩ c13 c10
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c14 c9
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c15 c8
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨119, by decide⟩ c16 c7
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨106, by decide⟩ c17 c6
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨144, by decide⟩ c18 c5
  c19
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00003.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00003.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00003.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00003.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00003.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00003.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00003.record005_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00003.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00003.record005_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00003.record005
