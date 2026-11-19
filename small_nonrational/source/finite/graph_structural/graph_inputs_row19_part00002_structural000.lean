module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow19Part00002Data
public import GraphInputsRow19Part00002Frames
public import GraphInputsRow19Part00002Leaves
public import GraphInputsRow19Part00002Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00002.record057
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record057
def vertexColumn : Fields := ⟨10, hexnat% "3c2cc95aa99563386e17bc1cc559a95553346d17783d0ec370f23a8f1354e334cd4b32e2b1ad1b16e8751e2729c6745c9715c8f0f03a318361382e07839314351342d07703a0d4330e2344c3312c2b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db4936db492492492492492492492249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4638707615923175424, 45035996273704960, 11529215046068469760]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [9006990948827136, 2314850346712694784, 4629700416936869888, 69793218560, 9259400833873739776]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [13897994098440142848, 114351356772352, 2314850208468434944]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [9002800939794432, 4398046511104, 63050394783186944, 16140901064495857664]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [8896801146929152, 4629700416936869888, 9259400868233478144, 110226040684544, 2314850345907388416]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [8566268785328128, 63050395051622400, 16140901064495857664, 440921342607360, 8589934592]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [9003191244947456, 1670742278144, 63050394783186944, 16140901064495857664, 2336999079936]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [8971600149872640, 4629700416936869888, 35598836432896, 45035996273704960, 11529215046068469760]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [8990843750842368, 9208409882624, 63050394783186944, 16140901064495857664, 7146825580544]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [9007198986305536, 63050394783186944, 16140901064495857664]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4080287382241280, 4926911604064256, 2314850208468434944, 54043195528445952, 13835058055282163712]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [7829718938157056, 4629700971256086528, 9072581541888, 2314885530279477248, 1132531336347648, 9259400833873739776]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c16 c11
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c17 c10
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c18 c9
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c19 c8
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c20 c7
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c21 c2
  c22
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record057_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record057_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record057_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record057_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record057_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record057_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record057_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record057_validity Papers.RationalityTen.CompactReplay.GraphInputsRow19Part00002.record057_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow19Part00002.record057
