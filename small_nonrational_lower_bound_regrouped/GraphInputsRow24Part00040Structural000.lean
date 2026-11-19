module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00040Data
public import GraphInputsRow24Part00040Frames
public import GraphInputsRow24Part00040Leaves
public import GraphInputsRow24Part00040Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00040.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record002
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), 37154834364760064, (certNat% 4), (certNat% 5), (certNat% 6)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), (certNat% 8), (certNat% 9), (certNat% 10), (certNat% 5), (certNat% 11)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), (certNat% 13), (certNat% 14), 63050394783186944, 2040693581152256]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), (certNat% 16), (certNat% 17), 2049489674174464, (certNat% 18), (certNat% 19)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), 63059190876209152, (certNat% 21), (certNat% 16), (certNat% 22), 2040693581152256]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 23), (certNat% 24), 2075877953241088, 65302194596872192, 4503599627370496]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), 2084674046263296, (certNat% 26), (certNat% 27), 33776997205278720, (certNat% 18)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 28), (certNat% 29), 2225420124553216, (certNat% 18), 29273603736338432, (certNat% 30), (certNat% 31)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c11 c4
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c12 c1
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c13 c0
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00040.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00040.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record006
def vertexColumn : Fields := ⟨10, (certNat% 32)⟩
def kindColumn : Fields := ⟨3, (certNat% 33)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨87, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 34), (certNat% 35), (certNat% 36), 17042430230528, 8725724278030336]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 37), (certNat% 38), 17076789968896, 8743316464074752, (certNat% 39)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 40), (certNat% 41), (certNat% 42), (certNat% 43), 3975834046038016, 17111149707264]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 44), (certNat% 45), (certNat% 46), 17317308137472, (certNat% 47)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 48), (certNat% 49), (certNat% 36), 8514618045497344, (certNat% 50), (certNat% 51)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 52), (certNat% 53), (certNat% 54), 16698832846848, (certNat% 55), (certNat% 56)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 57), (certNat% 58), (certNat% 53), (certNat% 50), (certNat% 59), (certNat% 60)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 61), (certNat% 62), 12103217840128, 8444249301319680, (certNat% 56), (certNat% 63)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 64), (certNat% 50), 12610023981056, (certNat% 65), (certNat% 66), (certNat% 67)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 68), (certNat% 69), (certNat% 49), (certNat% 59), (certNat% 50), (certNat% 67)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 70), (certNat% 71), (certNat% 56), 8532210231541760, (certNat% 72)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 73), 10101763080192, 8655355533852672, (certNat% 50), (certNat% 49), (certNat% 67)]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 74), (certNat% 75), (certNat% 76), 564065034305536, (certNat% 77), (certNat% 78), 8022036836253696]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c13 c10
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c14 c9
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c15 c8
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c16 c7
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c17 c6
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c18 c5
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c19 c4
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c20 c3
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c21 c2
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c22 c1
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c23 c0
  c24
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00040.record006_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00040.record006
