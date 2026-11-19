module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00015Data
public import GraphInputsRow24Part00015Frames
public import GraphInputsRow24Part00015Leaves
public import GraphInputsRow24Part00015Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00015.record013
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record013
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨44, by decide⟩, ⟨47, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨81, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), (certNat% 5), 67553994410557440]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), (certNat% 7), (certNat% 8), (certNat% 9), 2666130979403333632, 773094113280]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), (certNat% 7), (certNat% 11), (certNat% 9), 2666130979403333632, 773094113280]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), (certNat% 13), (certNat% 14), (certNat% 15), 773094113280, 2305843009213693952]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), (certNat% 14), 2666130981550817280, 67553994410557440, (certNat% 17), (certNat% 18), 1082331758592]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c5 c3
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c6 c2
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c7 c1
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c8 c0
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record013_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record013_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record013_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record013_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record013_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record013_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record013_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record013_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record013_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00015.record013

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00015.record017
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record017
def vertexColumn : Fields := ⟨10, (certNat% 19)⟩
def kindColumn : Fields := ⟨3, (certNat% 20)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨67, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 21), (certNat% 22), 864691815649902592, (certNat% 23), 2828288577765376]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), (certNat% 25), 2035627031571464192, (certNat% 26), 13835128424026341376, 9007199254740992]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 27), (certNat% 28), 2035627031571464192, (certNat% 26), 13835128424026341376, 9007199254740992]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), (certNat% 30), 10403315139225845760, (certNat% 26), 2898312650817536, 4611686018427387904]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 31), (certNat% 32), 13835269161514696704, (certNat% 33), 2035627031571464192, 9007199254740992]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 34), (certNat% 23), 2900511674073088, (certNat% 35), 2035627065931202560, 13844205992025260032, 151129161728]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record017_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record017_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record017_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record017_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record017_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record017_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record017_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record017_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record017_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00015.record017

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00015.record021
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record021
def vertexColumn : Fields := ⟨10, (certNat% 36)⟩
def kindColumn : Fields := ⟨3, (certNat% 37)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 38), 576460752303423488, (certNat% 39), (certNat% 40), (certNat% 41)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 42), (certNat% 43), 901282875427520512, (certNat% 41), 206158430208, 144255925564211200]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 44), 2251799813685248, 6917529027641081856, (certNat% 45)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 46), 2251799813685248, (certNat% 47), (certNat% 48)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 49), (certNat% 50), (certNat% 39), (certNat% 40), (certNat% 51)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 52), (certNat% 53), 2278188092751872, 586312651366203392]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 54), (certNat% 55), (certNat% 56), 586312651366203392, (certNat% 57), (certNat% 51)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 58), (certNat% 59), 244641337180160, 5764607523034234880, (certNat% 60), 344525440213319680]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 61), (certNat% 39), 3395394985787392, (certNat% 62), (certNat% 63)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 64), (certNat% 65), 326528633889882112, 806144333299318784, (certNat% 66), (certNat% 67), 785055597199360]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c15 c12
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c16 c11
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c17 c2
  c18
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record021_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record021_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record021_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record021_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record021_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record021_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record021_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record021_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record021_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00015.record021

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00015.record032
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record032
def vertexColumn : Fields := ⟨10, (certNat% 68)⟩
def kindColumn : Fields := ⟨3, (certNat% 69)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨73, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨89, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [323836685559267328, (certNat% 70), (certNat% 71), 252624066475720704, 5764607523034234880, (certNat% 72)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 73), 7493989779944505344, (certNat% 74), (certNat% 75)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [71634831548612608, 216594994578849792, 8646911284551352320, (certNat% 76), (certNat% 77), 288230925907525632]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 78), (certNat% 77), 490892359383384064, 714038312960, 83316867984261120]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 79), 492018259290226688, (certNat% 80), 13194139533312]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 81), 701958717440, 8646911284551352320, (certNat% 82)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [359865482578231296, (certNat% 71), 216595269456756736, (certNat% 83), 6917529027641081856, (certNat% 84)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 85), (certNat% 75), 144115875270623232, 9183121115185152, 72057594037927936]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 86), (certNat% 47), 144115875270623232, 9183121115185152, 72057594037927936]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 87), (certNat% 71), (certNat% 88), 216454806846308352, (certNat% 89), 141012366262272]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c11 c8
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 90), (certNat% 91), 4035225266123964416, (certNat% 92)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 93), (certNat% 75), 162130136341151744, 123145302310912, 72198331526283264]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 94), 70368744177664, 8646911284551352320, (certNat% 76), (certNat% 47)]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 95), (certNat% 71), (certNat% 83), 216454806846308352, 6917529027641081856, (certNat% 96)]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c17 c14
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c18 c13
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 97), 4035225266123964416, (certNat% 92), 310748924044378112, 70368744177664, (certNat% 75)]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 98), (certNat% 99), 668503069687808, (certNat% 71)]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 100), (certNat% 101), 167759635875364864, (certNat% 102), 146028888064]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 103), 8070450532247928832, (certNat% 77), 72499597712293888, 2251799813685248]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [189162179197403136, 8646911284551352320, (certNat% 104), (certNat% 77), 310818743032741888, 200111116255232, 74590868828323840]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c24 c23
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c25 c22
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c26 c21
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c27 c20
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c28 c19
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c29 c12
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c30 c7
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c31 c6
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c32 c5
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c33 c4
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c34 c3
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c35 c0
  c36
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record032_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record032_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record032_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record032_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record032_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record032_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record032_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record032_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00015.record032_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00015.record032
