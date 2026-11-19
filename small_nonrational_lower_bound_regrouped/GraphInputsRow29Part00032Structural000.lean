module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00032Data
public import GraphInputsRow29Part00032Frames
public import GraphInputsRow29Part00032Leaves
public import GraphInputsRow29Part00032Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00032.record010
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record010
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨41, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨69, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨85, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨97, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), 19825569038336, (certNat% 4), 246359324098560]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), 2594073387512889344, (certNat% 6), 234187180623265792, (certNat% 7), (certNat% 8)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 9), 2214592512, 270215977642229760, 2594073385365405696]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), 19795571376128, (certNat% 11), (certNat% 12), 522417556774977536, 2305843011898048512]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), 2594073387512889344, (certNat% 14), 234187180623265792, (certNat% 7), (certNat% 15)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), 2305843011629613056, (certNat% 17), (certNat% 18), 4612249110114729984, (certNat% 19)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), 4611686022856572928, (certNat% 21), (certNat% 22), (certNat% 17), (certNat% 23)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), (certNat% 25), (certNat% 26), (certNat% 27), (certNat% 12)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2828278236188770304, (certNat% 28), 2205801250816, (certNat% 17), (certNat% 29), (certNat% 30), (certNat% 31)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c11 c6
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c12 c5
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c13 c4
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c14 c1
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c15 c0
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record010_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00032.record010_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00032.record010
