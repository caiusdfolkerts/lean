module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00016Data
public import GraphInputsRow24Part00016Frames
public import GraphInputsRow24Part00016Leaves
public import GraphInputsRow24Part00016Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00016.record015
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record015
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨75, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), 4611686023259226112, 19327352832]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), (certNat% 6), (certNat% 7), 7638104968020361216, (certNat% 8), 288230376151711744]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 9), (certNat% 10), (certNat% 11), 7638104968020361216, 18577383359512576, (certNat% 12)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), (certNat% 14), (certNat% 4), 4611686023259226112, 19327352832]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), (certNat% 16), (certNat% 7), 7638104968020361216, 13421772800, 288230376151711744]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1296342074634797056, 7638104968087470080, (certNat% 17), (certNat% 18), 562951027163136, (certNat% 12)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), (certNat% 20), 4611686022722355200, (certNat% 21), 2147483648]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), 7493989780011614208, (certNat% 23), (certNat% 24), 6442450944, (certNat% 25)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [141582050304983040, 7638104968020361216, (certNat% 26), (certNat% 27), (certNat% 28), (certNat% 29)]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 30), (certNat% 31), 18014437164187648, 140740709580800, 78813062198460416]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 32), 41875931136, (certNat% 27), 2392537302040576, 112590059403739136, 18014398509481984]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [269934597154799616, 7493989780011614208, 18014437701058560, (certNat% 33), (certNat% 34), 140740709580800, (certNat% 29)]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c16 c11
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c17 c10
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c18 c7
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c19 c6
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c20 c3
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c21 c2
  c22
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record015_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record015_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record015_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record015_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record015_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record015_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record015_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record015_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record015_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00016.record015

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00016.record022
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record022
def vertexColumn : Fields := ⟨10, (certNat% 35)⟩
def kindColumn : Fields := ⟨3, (certNat% 36)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨67, by decide⟩, ⟨72, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨85, by decide⟩, ⟨90, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 37), (certNat% 38), (certNat% 39), 1706448488759296, 1152924871861207040]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 40), (certNat% 41), (certNat% 42), 2549063090176, 577744981884665856]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 43), (certNat% 44), (certNat% 45), 450360100176003072, 1224980198156402688, (certNat% 46)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 47), (certNat% 44), (certNat% 45), 504473527009673216, 594615888301260800, (certNat% 48)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 49), (certNat% 41), 594475975446626304, 95026151424, (certNat% 44), (certNat% 50)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 51), (certNat% 52), (certNat% 53), (certNat% 54), 578167194349731840, 1224981366387507200, 450360787370770432]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record022_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record022_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record022_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record022_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record022_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record022_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record022_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record022_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00016.record022_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00016.record022
