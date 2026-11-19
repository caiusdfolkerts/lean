module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00003Data
public import GraphInputsRow24Part00003Frames
public import GraphInputsRow24Part00003Leaves
public import GraphInputsRow24Part00003Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00003.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record000
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), 18178449080320, 900719929769066496, (certNat% 5)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), (certNat% 7), 18014399583223808, 36028797018963968]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 8), (certNat% 9), 324259173170675712, 2305843284091600896, 18014399583223808]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), 27021599374835712, (certNat% 11), 36028803461414912]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), (certNat% 11), 103079215104, 2473901162496]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), 8899172237312, 45035996810575872, 2200096997376, (certNat% 14)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), (certNat% 16), 18014399583223808, 324259179613126656, (certNat% 17), 6665789243392]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c10 c3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), 1801439850948198400, 18178449080320, (certNat% 19), (certNat% 20), 6803228196864]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 21), 26422672359424, 1801439850948198400, (certNat% 22), (certNat% 23), 36028803998285824]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), 4604204941312, 648518346341351424, (certNat% 25), (certNat% 26)]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 27), (certNat% 28), (certNat% 29), 91197893527994368, 481036337152, (certNat% 30)]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 31), (certNat% 3), (certNat% 32), 900719929769066496, 18245021073408, (certNat% 5)]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 33), 790273982464, 1801439850948198400, (certNat% 20), (certNat% 19), 4398046511104]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [914373667914252288, (certNat% 34), 91197893527994368, (certNat% 35), (certNat% 36), (certNat% 37), 18245021073408]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c20 c17
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c21 c16
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c22 c13
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c23 c12
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c24 c11
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c25 c0
  c26
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record000_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00003.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00003.record015
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record015
def vertexColumn : Fields := ⟨10, (certNat% 38)⟩
def kindColumn : Fields := ⟨3, (certNat% 39)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨63, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨73, by decide⟩, ⟨77, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 40), 281474976710656, (certNat% 41), 2017612633061982208, (certNat% 42)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 43), 246290604621824, (certNat% 44), 216455356602122240, 1729382256910270464, (certNat% 45)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 46), 175921860444160, (certNat% 47), (certNat% 48), 72062541840252928]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 49), 175921860444160, (certNat% 50), (certNat% 51), 72062541840252928]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 52), 90079139372990464, (certNat% 41), 246702921482240, (certNat% 53), (certNat% 54)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 55), (certNat% 53), (certNat% 56), 10376293541461622784, (certNat% 57)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [242472816782344192, (certNat% 56), 2017612633061982208, (certNat% 58), (certNat% 42), 9728478882562048]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 59), 144115188075855872, 864691128455135232, (certNat% 41), (certNat% 60)]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 61), 194217733930352640, 2017612633061982208, (certNat% 41), (certNat% 42), 202310139510784]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [69522111634341888, (certNat% 62), 218706056904179712, 2017612633061982208, (certNat% 54), (certNat% 42)]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 63), 4521226173153280, 576495936675512320, (certNat% 48), 288802122198155264]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 64), 864691128455135232, (certNat% 65), (certNat% 48), 43980465111040]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 66), 864691128455135232, (certNat% 67), (certNat% 48), 325455441821696]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 68), (certNat% 47), 2569558674112512, 4521226173153280, 571746046443520, (certNat% 69)]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c19 c16
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c20 c15
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 70), (certNat% 53), 10376293541461622784, (certNat% 71), (certNat% 51)]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 72), 1133871366144, 316659348799488, (certNat% 71), (certNat% 51)]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 73), (certNat% 71), (certNat% 74), (certNat% 75), 34359738368, (certNat% 53)]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c24 c23
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c25 c22
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 76), (certNat% 77), (certNat% 78), (certNat% 79), 218707156415807488, 17626545782784, 1152921504606846976]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c27 c26
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c28 c21
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c29 c14
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c30 c13
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c31 c10
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c32 c7
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c33 c2
  c34
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record015_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record015_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record015_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record015_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record015_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record015_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record015_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record015_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record015_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00003.record015

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00003.record039
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record039
def vertexColumn : Fields := ⟨10, (certNat% 80)⟩
def kindColumn : Fields := ⟨3, (certNat% 81)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨46, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨80, by decide⟩, ⟨86, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 82), (certNat% 83), 4755801207576985600, (certNat% 84)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 85), (certNat% 86), (certNat% 87), (certNat% 88), 910533066752, 3026418949592973312]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 89), (certNat% 90), (certNat% 91), 4755801206503243776, (certNat% 92)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 93), 108086940812705792, (certNat% 94), (certNat% 95), 2449958197289549824]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 96), (certNat% 97), (certNat% 98), (certNat% 99), 914828034048, 4179340454199820288]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 100), 112590128123215872, 29343800681824256, (certNat% 101), (certNat% 102), 924491710464, 3314649326549991424]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c9 c2
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record039_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record039_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record039_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record039_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record039_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record039_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record039_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record039_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record039_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00003.record039

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00003.record062
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record062
def vertexColumn : Fields := ⟨10, (certNat% 103)⟩
def kindColumn : Fields := ⟨3, (certNat% 104)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨72, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 105), 288230378903175168, 4612249019920416768, (certNat% 106), 108092988126658560, 2305983755291983872]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 107), (certNat% 108), 17593326895104, 1445655480385929216]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 109), 13835059154793791488, (certNat% 110), 17730765848576, 22799473381998592, 288230378299195392]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 111), (certNat% 112), (certNat% 113), 17594333528064, 288230376151711744]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 114), 292733977926565888, 13853072453791645696, (certNat% 115), 17592186044416]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 116), (certNat% 115), 108092988126658560, 17594333528064, 292733975779082240, 13853635403745067008]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 117), 13853072453791645696, (certNat% 110), 1803886264320, 292733977993674752, 17593259786240]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 118), 17593863766016, 9224216496144646144, (certNat% 106), 108092988126658560, 2305843009213693952]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 119), (certNat% 110), (certNat% 120), 22799473381998592, 17595474378752, 288230376151711744]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 121), 5531917877248, (certNat% 122), 154685931520, 324259175318159360, 19792283041792]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [16168909672017821696, (certNat% 123), 108092988126658560, (certNat% 110), 17595407269888, 292733975779082240]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 124), (certNat% 122), 108092988126658560, 13835059189153529856, 844425198567424, 17730765848576, 292733977926565888]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c15 c12
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c16 c11
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c17 c10
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c18 c9
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c19 c8
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c20 c3
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c21 c0
  c22
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record062_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record062_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record062_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record062_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record062_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record062_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record062_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record062_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00003.record062_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00003.record062
