module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00051Data
public import GraphInputsRow24Part00051Frames
public import GraphInputsRow24Part00051Leaves
public import GraphInputsRow24Part00051Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00051.record005
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record005
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨89, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 576460752303423488, (certNat% 3), (certNat% 4), (certNat% 5)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), 42949672960, (certNat% 3), (certNat% 7), (certNat% 8)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 9), 1756544592162848768, (certNat% 10), 11529215046068469760, (certNat% 11), 35970351104]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c3 c1
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c4 c0
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), 2161868558626193408, (certNat% 10), (certNat% 13), (certNat% 14), 40802189312]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c7 c1
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c8 c0
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), 344697029525504, (certNat% 16), (certNat% 17), 5368709120]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), (certNat% 19), (certNat% 5), 191402984163246080, 75041668595712, 51002736640]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), 1161928703861587968, 16140901064495857664, (certNat% 21), (certNat% 22)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 23), (certNat% 24), (certNat% 25), 576900556954533888, 78812993478983680, 1459166554145947648]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 26), 1297036692682702848, (certNat% 27), (certNat% 28), (certNat% 22)]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), (certNat% 30), (certNat% 25), 576884064280117248, 112589990684262400, 1459170677314551808]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 31), (certNat% 32), (certNat% 33), 691302542801371136, 1153273382687473664, 173516812976128, 459367164676145152]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c19 c14
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c20 c11
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c21 c10
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c22 c9
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c23 c5
  c24
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record005_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record005_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00051.record005

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00051.record008
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record008
def vertexColumn : Fields := ⟨10, (certNat% 34)⟩
def kindColumn : Fields := ⟨3, (certNat% 35)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨76, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 36), (certNat% 37), (certNat% 38), 13835058055282163712, (certNat% 39)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 40), 1589137899520, (certNat% 41), (certNat% 42), 4011018418126848, 17592186044416]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [14123289262510047232, 3940855832379392, (certNat% 43), (certNat% 44), (certNat% 45), 48378511622144, 2440951015214678016]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record008_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record008_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00051.record008

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00051.record009
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record009
def vertexColumn : Fields := ⟨10, (certNat% 46)⟩
def kindColumn : Fields := ⟨3, (certNat% 47)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨64, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨75, by decide⟩, ⟨79, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 48), 540431955284459520, (certNat% 49), (certNat% 50), 22517998136852480]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 51), 1729382256910270464, (certNat% 52), (certNat% 53), 4670725394792448]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 54), (certNat% 55), (certNat% 56), (certNat% 57), 4670725394792448]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 58), (certNat% 59), (certNat% 60), 3934190043136, (certNat% 61), 4644337115725824]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 62), 4035225403562917888, (certNat% 63), 18017697044365312, (certNat% 64), 47288345843204096]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 65), (certNat% 66), 6322191859712, (certNat% 67), 2278188092751872]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 68), (certNat% 56), 6322191859712, (certNat% 57), 2278188092751872]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 69), (certNat% 70), 2252624447406080, (certNat% 71), 5497558138880, (certNat% 60)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 72), (certNat% 73), (certNat% 74), 22521296671735808, (certNat% 64), 47288345843204096, (certNat% 75)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c13 c6
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c14 c5
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c15 c0
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record009_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record009_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record009_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record009_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record009_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record009_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record009_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record009_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record009_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00051.record009

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00051.record011
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record011
def vertexColumn : Fields := ⟨10, (certNat% 76)⟩
def kindColumn : Fields := ⟨3, (certNat% 77)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨72, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨85, by decide⟩, ⟨87, by decide⟩, ⟨91, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 78), (certNat% 79), (certNat% 80), (certNat% 81), 351280770934898688, 2770769301995520]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 82), 864692365405716480, (certNat% 83), (certNat% 84), 1125899906842624]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 85), (certNat% 86), (certNat% 87), (certNat% 88), 815187816437776384, 333267059620184064, 3597602046083072]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record011_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record011_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record011_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record011_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record011_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record011_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record011_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record011_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record011_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00051.record011

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00051.record010
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "7cb8b8a9687a698b61da8e6386e4785e0fae1e26591e5a52d475a358d1b51d1743de0ec3a8da398ce394cb3c2e8b62d4b1ae1b46c3ba1d2719d1725c5783c8f13c2f1ca4a16986298364381e1c64916585294354341da0d8390ca318c530ce0b42c4b06d0721c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36d24934d24da49269a492492492492492492492249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record010 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record010 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record010.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record010.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record010.data.quota

def groupMembers1 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 0)]))
 (.leaf ([(facetIndex 1)])))
 (.branch 3
 (.leaf ([(facetIndex 2)]))
 (.leaf ([(facetIndex 3)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 4)]))
 (.leaf ([(facetIndex 5)])))
 (.branch 7
 (.leaf ([(facetIndex 6)]))
 (.leaf ([(facetIndex 7)])))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ([(facetIndex 8)]))
 (.leaf ([(facetIndex 9)])))
 (.branch 11
 (.leaf ([(facetIndex 10)]))
 (.leaf ([(facetIndex 11)]))))
 (.branch 14
 (.branch 13
 (.leaf ([(facetIndex 12)]))
 (.leaf ([(facetIndex 13)])))
 (.branch 15
 (.leaf ([(facetIndex 14)]))
 (.leaf ([(facetIndex 15)]))))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf ([(facetIndex 16)]))
 (.leaf ([(facetIndex 17)])))
 (.branch 19
 (.leaf ([(facetIndex 18)]))
 (.leaf ([(facetIndex 19)]))))
 (.branch 22
 (.branch 21
 (.leaf ([(facetIndex 20)]))
 (.leaf ([(facetIndex 21)])))
 (.branch 23
 (.leaf ([(facetIndex 22)]))
 (.leaf ([(facetIndex 23)])))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf ([(facetIndex 24)]))
 (.leaf ([(facetIndex 25)])))
 (.branch 27
 (.leaf ([(facetIndex 26)]))
 (.leaf ([(facetIndex 27)]))))
 (.branch 30
 (.branch 29
 (.leaf ([(facetIndex 28)]))
 (.leaf ([(facetIndex 29)])))
 (.branch 31
 (.leaf ([(facetIndex 30)]))
 (.leaf ([(facetIndex 31)])))))))
def groupColors1 : PackedGraphCertificate.Fields :=
  ⟨5, sparse_nat% "ffbbcdeb38bdab49ca307b9ac5a928398a418820"⟩
def grouping1 : FacetSat.Grouping data.count where
  count := 32
  members := fun g => groupMembers1.get g
  color := fun c => groupColors1.get c.val
def groupKind1 : List Nat := List.range grouping1.count

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 34), (facetIndex 47), (facetIndex 48), (facetIndex 62), (facetIndex 75)]))
 (.leaf ([(facetIndex 33), (facetIndex 44), (facetIndex 45), (facetIndex 46), (facetIndex 51), (facetIndex 68), (facetIndex 81)])))
 (.branch 3
 (.leaf ([(facetIndex 37), (facetIndex 40), (facetIndex 41), (facetIndex 54), (facetIndex 66), (facetIndex 79)]))
 (.leaf ([(facetIndex 32), (facetIndex 39), (facetIndex 50), (facetIndex 65), (facetIndex 78)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 35), (facetIndex 38), (facetIndex 43), (facetIndex 60), (facetIndex 73)]))
 (.leaf ([(facetIndex 52), (facetIndex 53), (facetIndex 55), (facetIndex 56)])))
 (.branch 7
 (.leaf ([(facetIndex 49), (facetIndex 57)]))
 (.branch 8
 (.leaf ([(facetIndex 36), (facetIndex 42), (facetIndex 59), (facetIndex 64), (facetIndex 72), (facetIndex 77)]))
 (.leaf ([(facetIndex 58), (facetIndex 67), (facetIndex 71), (facetIndex 80)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "18237000478001823700047865525513600111472234274013z20;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 61)]))
 (.branch 2
 (.leaf ([(facetIndex 70)]))
 (.leaf ([(facetIndex 74)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 83)]))
 (.leaf ([(facetIndex 84)])))
 (.branch 6
 (.leaf ([(facetIndex 63), (facetIndex 69)]))
 (.leaf ([(facetIndex 76), (facetIndex 82)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "4780006080068000az2f;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped1_0000 : List Nat := [0, 1]
def grouped1_0001 : List Nat := [0, 1, 2, 3]
def grouped1_0002 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7]
def grouped1_0003 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def grouped1_0005 : List Nat := [2]
def grouped1_0006 : List Nat := [2, 3]
def grouped1_0007 : List Nat := [3]
def grouped1_0008 : List Nat := [4, 5]
def grouped1_0009 : List Nat := [4, 5, 6, 7]
def grouped1_0010 : List Nat := [6]
def grouped1_0011 : List Nat := [6, 7]
def grouped1_0012 : List Nat := [7]
def grouped1_0013 : List Nat := [8]
def grouped1_0014 : List Nat := [8, 9]
def grouped1_0015 : List Nat := [8, 9, 10, 11]
def grouped1_0016 : List Nat := [8, 9, 10, 11, 12, 13, 14, 15]
def grouped1_0017 : List Nat := [9]
def grouped1_0018 : List Nat := [10]
def grouped1_0019 : List Nat := [10, 11]
def grouped1_0020 : List Nat := [11]
def grouped1_0021 : List Nat := [12, 13, 14, 15]
def grouped1_0022 : List Nat := [16]
def grouped1_0023 : List Nat := [16, 17]
def grouped1_0024 : List Nat := [16, 17, 18, 19]
def grouped1_0025 : List Nat := [16, 17, 18, 19, 20, 21, 22, 23]
def grouped1_0026 : List Nat := [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]
def grouped1_0027 : List Nat := [17]
def grouped1_0028 : List Nat := [18]
def grouped1_0029 : List Nat := [18, 19]
def grouped1_0030 : List Nat := [19]
def grouped1_0031 : List Nat := [20, 21]
def grouped1_0032 : List Nat := [20, 21, 22, 23]
def grouped1_0033 : List Nat := [22]
def grouped1_0034 : List Nat := [22, 23]
def grouped1_0035 : List Nat := [23]
def grouped1_0036 : List Nat := [24]
def grouped1_0037 : List Nat := [24, 25]
def grouped1_0038 : List Nat := [24, 25, 26, 27]
def grouped1_0039 : List Nat := [24, 25, 26, 27, 28, 29, 30, 31]
def grouped1_0040 : List Nat := [25]
def grouped1_0041 : List Nat := [26]
def grouped1_0042 : List Nat := [26, 27]
def grouped1_0043 : List Nat := [27]
def grouped1_0044 : List Nat := [28]
def grouped1_0045 : List Nat := [28, 29]
def grouped1_0046 : List Nat := [28, 29, 30, 31]
def grouped1_0047 : List Nat := [29]
def grouped1_0048 : List Nat := [30]
def grouped1_0049 : List Nat := [30, 31]
def grouped1_0050 : List Nat := [31]
def grouped2_0051 : List Nat := [0]
def grouped2_0052 : List Nat := [0, 1]
def grouped2_0053 : List Nat := [0, 1, 2, 3]
def grouped2_0055 : List Nat := [1]
def grouped2_0056 : List Nat := [2]
def grouped2_0057 : List Nat := [2, 3]
def grouped2_0058 : List Nat := [3]
def grouped2_0059 : List Nat := [4]
def grouped2_0060 : List Nat := [4, 5]
def grouped2_0061 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0062 : List Nat := [5]
def grouped2_0063 : List Nat := [6]
def grouped2_0064 : List Nat := [6, 7, 8]
def grouped2_0065 : List Nat := [7]
def grouped2_0066 : List Nat := [7, 8]
def grouped2_0067 : List Nat := [8]
def grouped3_0068 : List Nat := [0]
def grouped3_0069 : List Nat := [0, 1, 2]
def grouped3_0071 : List Nat := [1]
def grouped3_0072 : List Nat := [1, 2]
def grouped3_0073 : List Nat := [2]
def grouped3_0074 : List Nat := [3]
def grouped3_0075 : List Nat := [3, 4]
def grouped3_0076 : List Nat := [3, 4, 5, 6]
def grouped3_0077 : List Nat := [4]
def grouped3_0078 : List Nat := [5]
def grouped3_0079 : List Nat := [5, 6]
def grouped3_0080 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record010 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record010_matrix_checked

def leafCount : Nat := 4
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaf0000 : List (Fin data.count) := [(facetIndex 14), (facetIndex 15), (facetIndex 16), (facetIndex 22), (facetIndex 49), (facetIndex 62), (facetIndex 65), (facetIndex 67), (facetIndex 70), (facetIndex 73), (facetIndex 77), (facetIndex 79), (facetIndex 81), (facetIndex 83)]
theorem leaf0000_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0000 = true := by
  decide +kernel
theorem leaf0000_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0000 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0000_counts_checked
def leaf0001 : List (Fin data.count) := [(facetIndex 7), (facetIndex 8), (facetIndex 16), (facetIndex 22), (facetIndex 57), (facetIndex 62), (facetIndex 65), (facetIndex 67), (facetIndex 70), (facetIndex 73), (facetIndex 77), (facetIndex 79), (facetIndex 81), (facetIndex 83)]
theorem leaf0001_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0001 = true := by
  decide +kernel
theorem leaf0001_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0001 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0001_counts_checked
def leaf0002 : List (Fin data.count) := [(facetIndex 14), (facetIndex 15), (facetIndex 24), (facetIndex 30), (facetIndex 49), (facetIndex 60), (facetIndex 64), (facetIndex 66), (facetIndex 68), (facetIndex 70), (facetIndex 75), (facetIndex 78), (facetIndex 80), (facetIndex 83)]
theorem leaf0002_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0002 = true := by
  decide +kernel
theorem leaf0002_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0002 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0002_counts_checked
def leaf0003 : List (Fin data.count) := [(facetIndex 7), (facetIndex 8), (facetIndex 24), (facetIndex 30), (facetIndex 57), (facetIndex 60), (facetIndex 64), (facetIndex 66), (facetIndex 68), (facetIndex 70), (facetIndex 75), (facetIndex 78), (facetIndex 80), (facetIndex 83)]
theorem leaf0003_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0003 = true := by
  decide +kernel
theorem leaf0003_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0003 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0003_counts_checked
def leavesTable : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf (leaf0000))
 (.leaf (leaf0001)))
 (.branch 3
 (.leaf (leaf0002))
 (.leaf (leaf0003))))
def leaves (j : Fin leafCount) : List (Fin data.count) := leavesTable.get j.val

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00051.record010" "{\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"group\",\"kind\":1,\"index\":2},{\"tag\":\"group\",\"kind\":1,\"index\":7},{\"tag\":\"group\",\"kind\":1,\"index\":8},{\"tag\":\"group\",\"kind\":1,\"index\":10},{\"tag\":\"group\",\"kind\":1,\"index\":16},{\"tag\":\"group\",\"kind\":1,\"index\":19},{\"tag\":\"group\",\"kind\":1,\"index\":22},{\"tag\":\"group\",\"kind\":1,\"index\":23},{\"tag\":\"group\",\"kind\":1,\"index\":25},{\"tag\":\"group\",\"kind\":1,\"index\":26},{\"tag\":\"group\",\"kind\":1,\"index\":28},{\"tag\":\"group\",\"kind\":1,\"index\":29},{\"tag\":\"group\",\"kind\":1,\"index\":30},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0006\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0001\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0011\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0009\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0002\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0002\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0014\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0019\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0015\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0015\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0016\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0016\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0003\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0003\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0023\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0029\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0024\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0024\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0034\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0034\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0032\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0032\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0025\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0025\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0037\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0042\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0038\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0045\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0049\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0046\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0046\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0039\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0039\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0026\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0026\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":5,\"list_name\":\"groupKind1\"},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0052\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0057\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0053\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0060\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0060\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0066\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0064\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0061\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0061\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0072\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0072\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0069\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0069\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0075\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0075\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0079\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0076\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0076\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00051.record010" 166

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00051.record010" "{\"ridges\":[[0,11],[1,7],[1,19],[1,22],[5,11],[7,11],[8,11],[8,521],[8,522],[9,50],[10,81],[11,97],[11,98],[12,131],[13,577],[14,131],[15,131],[15,515],[15,641],[18,37],[19,161],[22,73],[22,521],[23,97],[26,38],[27,38],[27,162],[30,74],[30,522],[30,578],[31,98],[32,11],[36,7],[37,19],[37,22],[37,131],[39,37],[39,38],[39,97],[39,98],[41,7],[41,641],[42,11],[44,19],[44,25],[46,73],[46,74],[48,641],[49,259],[49,515],[49,521],[49,522],[50,131],[51,515],[51,577],[51,578],[53,578],[54,35],[55,641],[56,578],[56,641],[57,259],[57,641],[57,642],[58,37],[60,25],[62,13],[62,265],[62,388],[63,521],[63,652],[64,37],[64,52],[64,81],[64,97],[65,21],[65,161],[66,37],[66,161],[67,25],[67,73],[67,97],[68,25],[68,81],[68,521],[68,584],[70,97],[70,641],[70,736],[71,38],[72,74],[73,22],[73,26],[75,14],[75,266],[75,386],[76,522],[76,652],[77,22],[77,98],[78,50],[78,162],[78,164],[79,162],[79,262],[80,26],[80,50],[80,74],[80,98],[80,112],[81,522],[81,584],[83,98],[83,162],[83,578],[83,736],[84,108]],\"owners\":[[1,7,[0,2,3,4,33,35,39,41],[36]],[36,7,[0,2,3,4,35,41],[1,33,39]],[41,7,[0,1,2,4,33,36,39],[3,35]],[62,13,[0,16,32,33,35,58,59,61],[17,34,63]],[75,14,[0,24,32,33,35,71,72,74],[25,34,76]],[1,19,[5,9,10,43,44,50,51],[37,38]],[37,19,[5,9,10,43,44,51],[1,38,50]],[44,19,[1,9,10,37,38,50],[5,43,51]],[65,21,[1,16,36,38,59,60],[18,37,64]],[54,35,[2,9,11,32,42,45,53],[12,40,55]],[64,37,[2,19,32,40,66],[18,39,58,61]],[49,259,[4,14,38,40,54],[7,43,46,57]],[57,259,[4,7,38,40,43,46],[14,49,54]],[79,262,[4,25,38,73],[28,40]],[67,25,[5,16,43,44,60],[21,42,58,68]],[68,25,[5,16,42,43,58,60],[21,44,67]],[73,26,[5,29,42,44,80,81],[24,43,71]],[80,26,[5,24,43,44,73],[29,42,71,81]],[62,265,[7,43,46,49],[17,47,60,69]],[75,266,[7,43,46,49],[25,47,73,82]],[8,521,[22,63,68,69],[35,44,48,49]],[22,521,[8,35,44,48,49,63,69],[68]],[68,521,[8,35,48,49,63,69],[22,44]],[8,522,[30,76,81,82],[35,44,48,49]],[30,522,[8,35,44,48,49,76,82],[81]],[49,522,[30,76,81],[8,35,44,48,82]],[81,522,[8,35,48,49,76,82],[30,44]],[68,81,[10,23,36,64],[21,51,59]],[19,161,[12,50,52,54,55,70],[65,66]],[65,161,[12,52,54,55,70],[19,50,66]],[66,161,[12,50,52,55,70],[19,54,65]],[27,162,[12,50,52,54,55,83],[78,79]],[78,162,[12,52,54,55,83],[27,50,79]],[79,162,[12,50,52,55,83],[27,54,78]],[83,162,[12,27,50,54,78,79],[52,55]],[13,577,[22,68,70],[51,53,56]],[51,577,[22,70],[13,53,56,68]],[53,578,[30,81],[13,51,56,83]],[56,578,[30,81],[13,51,53,83]],[75,386,[14,54,57],[28,47,79,82]],[15,641,[63,69,70],[41,48,55,56,57]],[41,641,[69,70],[15,48,55,56,57,63]],[48,641,[70],[15,41,55,56,57,63,69]],[55,641,[63,69],[15,41,48,56,57,70]],[56,641,[63,69],[15,41,48,55,57,70]],[57,641,[63,70],[15,41,48,55,56,69]],[70,641,[15,41,48,57,63,69],[55,56]],[57,642,[76,83],[15,41,48,55,56,82]],[64,52,[26,71,78],[18,58,65,77,84]],[78,164,[19,66],[27,65,79]],[62,388,[28,79],[20,66,75]],[68,584,[30],[22,81]],[81,584,[22],[30,68]],[80,112,[23,64],[31,67,77,84]],[84,108,[61,74],[]],[63,652,[76],[]],[76,652,[63],[]],[70,736,[83],[]],[83,736,[70],[]]],\"edges\":[[29,[8,22,30,35,44,48,49,63,68,69,76,81,82]],[30,[9,18,23,26,31,42,50,58,64,65,67,71,77,78,80,84]],[36,[12,19,27,50,52,54,55,65,66,70,78,79,83]],[41,[13,22,30,51,53,56,68,70,81,83]],[43,[15,41,48,55,56,57,63,69,70,76,82,83]]],\"groupings\":[1,2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00051.record010" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00051.record010\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-29,-3],[-32,-1],[-32,-7],[-32,-29],[-32,-31],[-34,-4],[-35,-1],[-35,-31],[-36,-9],[-36,-33],[-37,-4],[-38,-4],[-38,-14],[-39,-36],[-40,-1],[-40,-8],[-40,-29],[-40,-31],[-40,-32],[-41,-7],[-41,-8],[-41,-40],[-43,-8],[-43,-32],[-43,-41],[-44,-38],[-46,-1],[-46,-6],[-46,-29],[-46,-30],[-46,-31],[-46,-32],[-46,-39],[-46,-40],[-46,-41],[-46,-42],[-46,-43],[-46,-44],[-46,-45],[-47,-3],[-51,-4],[-51,-15],[-51,-38],[-52,-44],[-52,-45],[-53,-45],[-53,-46],[-54,-4],[-54,-12],[-54,-31],[-54,-34],[-54,-38],[-54,-44],[-54,-45],[-54,-46],[-54,-47],[-54,-49],[-54,-51],[-54,-52],[-54,-53],[-55,-33],[-55,-42],[-56,-55],[-57,-1],[-57,-29],[-57,-30],[-57,-31],[-57,-40],[-57,-55],[-57,-56],[-59,-5],[-59,-35],[-59,-37],[-59,-57],[-60,-31],[-60,-44],[-60,-59],[-61,-9],[-61,-33],[-61,-36],[-61,-47],[-61,-55],[-62,-3],[-62,-55],[-62,-61],[-63,-4],[-63,-59],[-63,-62],[-64,-33],[-64,-39],[-64,-42],[-64,-48],[-64,-56],[-64,-61],[-65,-30],[-65,-41],[-65,-43],[-65,-56],[-65,-58],[-65,-64],[-66,-31],[-66,-44],[-66,-46],[-66,-59],[-67,-49],[-67,-50],[-67,-52],[-68,-42],[-70,-1],[-70,-31],[-70,-68],[-70,-69],[-72,-5],[-72,-35],[-72,-37],[-72,-60],[-72,-66],[-72,-70],[-74,-9],[-74,-36],[-74,-47],[-75,-3],[-75,-36],[-75,-68],[-75,-74],[-76,-4],[-76,-72],[-76,-75],[-77,-10],[-77,-29],[-77,-33],[-77,-39],[-77,-42],[-77,-48],[-77,-55],[-77,-68],[-77,-69],[-77,-74],[-78,-43],[-78,-69],[-78,-77],[-79,-44],[-79,-46],[-79,-59],[-79,-72],[-2,1,3,4,5,30,32,36,38],[-33,1,3,4,5,32,38],[-38,1,2,3,5,30,33,36],[-1,-7,-8],[-6,-7,-8],[-7,-8,-29],[-7,-8,-39],[-59,1,16,29,30,32,55,56,58],[-72,1,21,29,30,32,68,69,71],[-2,6,9,10,40,41,47,48],[-34,6,9,10,40,41,48],[-41,2,9,10,34,35,47],[-62,2,16,33,35,56,57],[-2,-70,-74],[-34,-70,-74],[-51,3,9,11,29,39,42,50],[-61,3,18,29,37,63],[-17,-36,-63],[-36,-55,-63],[-23,-24,-36],[-24,-36,-68],[-12,-14,-15],[-14,-15,-34],[-14,-15,-47],[-46,5,14,35,37,51],[-54,5,7,35,37,40,43],[-76,5,22,35,70],[-64,6,16,40,41,57],[-65,6,16,39,40,55,57],[-41,-57,-64],[-70,6,26,39,41,77,78],[-77,6,21,40,41,70],[-19,-43,-64],[-27,-43,-69],[-27,-43,-77],[-59,7,40,43,46],[-72,7,40,43,46],[-15,-46,-48],[-8,19,60,65,66],[-19,8,32,41,45,46,60,66],[-65,8,32,45,46,60,66],[-19,-46,-60],[-46,-60,-65],[-8,27,73,78,79],[-27,8,32,41,45,46,73,79],[-46,27,73,78],[-78,8,32,45,46,73,79],[-27,-46,-73],[-9,-75,-77],[-65,10,20,33,61],[-10,-61,-65],[-11,-61,-67],[-20,-36,-67],[-36,-64,-67],[-11,-74,-80],[-28,-36,-80],[-36,-77,-80],[-18,12,47,49,51,52,67],[-62,12,49,51,52,67],[-63,12,47,49,52,67],[-24,12,47,49,51,52,80],[-75,12,49,51,52,80],[-76,12,47,49,52,80],[-80,12,24,47,51,75,76],[-13,19,65,67],[-48,19,67],[-50,27,78],[-53,27,78],[-27,-48,-80],[-72,14,51,54],[-15,60,66,67],[-38,66,67],[-45,67],[-52,60,66],[-53,60,66],[-54,60,67],[-67,15,38,45,54,60,66],[-54,73,80],[-61,23,68,75],[-75,18,63],[-59,25,76],[-65,27],[-78,19],[-77,20,61],[-81,58,71],[-60,73],[-73,60],[-67,80],[-80,67],[-3,82],[-7,83],[-8,84],[-10,85],[-16,86],[-18,87],[-19,88],[-20,89],[-22,90],[-23,91],[-25,92],[-26,93],[-27,94],[-82,95],[-95,96],[-83,97],[-97,98],[-98,99],[-96,-98,100],[-84,101],[-85,102],[-101,103],[-101,-102,104],[-103,105],[-104,106],[-99,-105,107],[-99,-106,108],[-100,-105,108],[-86,109],[-87,110],[-110,111],[-109,111],[-109,-110,112],[-89,113],[-88,113],[-88,-89,114],[-113,115],[-114,116],[-115,117],[-116,118],[-111,117],[-111,-115,118],[-112,118],[-90,119],[-91,120],[-120,121],[-119,121],[-93,122],[-92,122],[-94,123],[-123,124],[-122,-123,125],[-124,126],[-125,127],[-121,-124,127],[-127,128],[-117,-126,128],[-117,-127,129],[-118,-126,129],[-107,-129,130],[-108,-128,130],[-130],[-131,31,44,45,59,72],[-132,30,41,42,43,48,65,78],[-133,34,37,38,51,63,76],[-134,29,36,47,62,75],[-135,32,35,40,57,70],[-136,49,50,52,53],[-137,46,54],[-54,137],[-138,33,39,56,61,69,74],[-139,55,64,68,77],[-140,131],[-140,132],[-141,133],[-141,134],[-142,140],[-142,141],[-143,135,136],[-144,135],[-144,136],[-145,138],[-145,139],[-146,137],[-146,145],[-147,143],[-147,144,146],[-148,144],[-148,146],[-149,142,148],[-149,147],[149],[-58,150],[-67,151],[-71,152],[-153,80],[-80,153],[-154,81],[-81,154],[-155,60,66],[-60,155],[-156,73,79],[-73,156],[-152,157],[-151,157],[-151,-152,158],[-157,159],[-158,160],[-150,159],[-161,153,154],[-153,161],[-153,-154,162],[-163,155],[-163,156],[-155,-156,163],[-165,161,163],[-163,165],[-161,164],[-162,165],[-159,-165,166],[-160,-164,166],[-166],[-14,-15,-16,-19,-46,-59,-62,-64,-67,-70,-74,-76,-78,-80],[-7,-8,-16,-19,-54,-59,-62,-64,-67,-70,-74,-76,-78,-80],[-14,-15,-21,-27,-46,-57,-61,-63,-65,-67,-72,-75,-77,-80],[-7,-8,-21,-27,-54,-57,-61,-63,-65,-67,-72,-75,-77,-80],[8,19,27,32,41,45,46,60,65,66,73,78,79],[9,17,20,23,28,39,47,55,61,62,64,68,74,75,77,81],[12,18,24,47,49,51,52,62,63,67,75,76,80],[13,19,27,48,50,53,65,67,78,80],[15,38,45,52,53,54,60,66,67,73,79,80]],\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"group\",\"index\":2,\"kind\":1},{\"tag\":\"group\",\"index\":7,\"kind\":1},{\"tag\":\"group\",\"index\":8,\"kind\":1},{\"tag\":\"group\",\"index\":10,\"kind\":1},{\"tag\":\"group\",\"index\":16,\"kind\":1},{\"tag\":\"group\",\"index\":19,\"kind\":1},{\"tag\":\"group\",\"index\":22,\"kind\":1},{\"tag\":\"group\",\"index\":23,\"kind\":1},{\"tag\":\"group\",\"index\":25,\"kind\":1},{\"tag\":\"group\",\"index\":26,\"kind\":1},{\"tag\":\"group\",\"index\":28,\"kind\":1},{\"tag\":\"group\",\"index\":29,\"kind\":1},{\"tag\":\"group\",\"index\":30,\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":32,\"b\":2},{\"tag\":\"incompatible\",\"a\":35,\"b\":0},{\"tag\":\"incompatible\",\"a\":35,\"b\":7},{\"tag\":\"incompatible\",\"a\":35,\"b\":32},{\"tag\":\"incompatible\",\"a\":35,\"b\":34},{\"tag\":\"incompatible\",\"a\":37,\"b\":3},{\"tag\":\"incompatible\",\"a\":38,\"b\":0},{\"tag\":\"incompatible\",\"a\":38,\"b\":34},{\"tag\":\"incompatible\",\"a\":39,\"b\":9},{\"tag\":\"incompatible\",\"a\":39,\"b\":36},{\"tag\":\"incompatible\",\"a\":40,\"b\":3},{\"tag\":\"incompatible\",\"a\":41,\"b\":3},{\"tag\":\"incompatible\",\"a\":41,\"b\":14},{\"tag\":\"incompatible\",\"a\":42,\"b\":39},{\"tag\":\"incompatible\",\"a\":43,\"b\":0},{\"tag\":\"incompatible\",\"a\":43,\"b\":8},{\"tag\":\"incompatible\",\"a\":43,\"b\":32},{\"tag\":\"incompatible\",\"a\":43,\"b\":34},{\"tag\":\"incompatible\",\"a\":43,\"b\":35},{\"tag\":\"incompatible\",\"a\":44,\"b\":7},{\"tag\":\"incompatible\",\"a\":44,\"b\":8},{\"tag\":\"incompatible\",\"a\":44,\"b\":43},{\"tag\":\"incompatible\",\"a\":46,\"b\":8},{\"tag\":\"incompatible\",\"a\":46,\"b\":35},{\"tag\":\"incompatible\",\"a\":46,\"b\":44},{\"tag\":\"incompatible\",\"a\":47,\"b\":41},{\"tag\":\"incompatible\",\"a\":49,\"b\":0},{\"tag\":\"incompatible\",\"a\":49,\"b\":5},{\"tag\":\"incompatible\",\"a\":49,\"b\":32},{\"tag\":\"incompatible\",\"a\":49,\"b\":33},{\"tag\":\"incompatible\",\"a\":49,\"b\":34},{\"tag\":\"incompatible\",\"a\":49,\"b\":35},{\"tag\":\"incompatible\",\"a\":49,\"b\":42},{\"tag\":\"incompatible\",\"a\":49,\"b\":43},{\"tag\":\"incompatible\",\"a\":49,\"b\":44},{\"tag\":\"incompatible\",\"a\":49,\"b\":45},{\"tag\":\"incompatible\",\"a\":49,\"b\":46},{\"tag\":\"incompatible\",\"a\":49,\"b\":47},{\"tag\":\"incompatible\",\"a\":49,\"b\":48},{\"tag\":\"incompatible\",\"a\":50,\"b\":2},{\"tag\":\"incompatible\",\"a\":54,\"b\":3},{\"tag\":\"incompatible\",\"a\":54,\"b\":15},{\"tag\":\"incompatible\",\"a\":54,\"b\":41},{\"tag\":\"incompatible\",\"a\":55,\"b\":47},{\"tag\":\"incompatible\",\"a\":55,\"b\":48},{\"tag\":\"incompatible\",\"a\":56,\"b\":48},{\"tag\":\"incompatible\",\"a\":56,\"b\":49},{\"tag\":\"incompatible\",\"a\":57,\"b\":3},{\"tag\":\"incompatible\",\"a\":57,\"b\":12},{\"tag\":\"incompatible\",\"a\":57,\"b\":34},{\"tag\":\"incompatible\",\"a\":57,\"b\":37},{\"tag\":\"incompatible\",\"a\":57,\"b\":41},{\"tag\":\"incompatible\",\"a\":57,\"b\":47},{\"tag\":\"incompatible\",\"a\":57,\"b\":48},{\"tag\":\"incompatible\",\"a\":57,\"b\":49},{\"tag\":\"incompatible\",\"a\":57,\"b\":50},{\"tag\":\"incompatible\",\"a\":57,\"b\":52},{\"tag\":\"incompatible\",\"a\":57,\"b\":54},{\"tag\":\"incompatible\",\"a\":57,\"b\":55},{\"tag\":\"incompatible\",\"a\":57,\"b\":56},{\"tag\":\"incompatible\",\"a\":58,\"b\":36},{\"tag\":\"incompatible\",\"a\":58,\"b\":45},{\"tag\":\"incompatible\",\"a\":59,\"b\":58},{\"tag\":\"incompatible\",\"a\":60,\"b\":0},{\"tag\":\"incompatible\",\"a\":60,\"b\":32},{\"tag\":\"incompatible\",\"a\":60,\"b\":33},{\"tag\":\"incompatible\",\"a\":60,\"b\":34},{\"tag\":\"incompatible\",\"a\":60,\"b\":43},{\"tag\":\"incompatible\",\"a\":60,\"b\":58},{\"tag\":\"incompatible\",\"a\":60,\"b\":59},{\"tag\":\"incompatible\",\"a\":62,\"b\":4},{\"tag\":\"incompatible\",\"a\":62,\"b\":38},{\"tag\":\"incompatible\",\"a\":62,\"b\":40},{\"tag\":\"incompatible\",\"a\":62,\"b\":60},{\"tag\":\"incompatible\",\"a\":63,\"b\":34},{\"tag\":\"incompatible\",\"a\":63,\"b\":47},{\"tag\":\"incompatible\",\"a\":63,\"b\":62},{\"tag\":\"incompatible\",\"a\":64,\"b\":9},{\"tag\":\"incompatible\",\"a\":64,\"b\":36},{\"tag\":\"incompatible\",\"a\":64,\"b\":39},{\"tag\":\"incompatible\",\"a\":64,\"b\":50},{\"tag\":\"incompatible\",\"a\":64,\"b\":58},{\"tag\":\"incompatible\",\"a\":65,\"b\":2},{\"tag\":\"incompatible\",\"a\":65,\"b\":58},{\"tag\":\"incompatible\",\"a\":65,\"b\":64},{\"tag\":\"incompatible\",\"a\":66,\"b\":3},{\"tag\":\"incompatible\",\"a\":66,\"b\":62},{\"tag\":\"incompatible\",\"a\":66,\"b\":65},{\"tag\":\"incompatible\",\"a\":67,\"b\":36},{\"tag\":\"incompatible\",\"a\":67,\"b\":42},{\"tag\":\"incompatible\",\"a\":67,\"b\":45},{\"tag\":\"incompatible\",\"a\":67,\"b\":51},{\"tag\":\"incompatible\",\"a\":67,\"b\":59},{\"tag\":\"incompatible\",\"a\":67,\"b\":64},{\"tag\":\"incompatible\",\"a\":68,\"b\":33},{\"tag\":\"incompatible\",\"a\":68,\"b\":44},{\"tag\":\"incompatible\",\"a\":68,\"b\":46},{\"tag\":\"incompatible\",\"a\":68,\"b\":59},{\"tag\":\"incompatible\",\"a\":68,\"b\":61},{\"tag\":\"incompatible\",\"a\":68,\"b\":67},{\"tag\":\"incompatible\",\"a\":69,\"b\":34},{\"tag\":\"incompatible\",\"a\":69,\"b\":47},{\"tag\":\"incompatible\",\"a\":69,\"b\":49},{\"tag\":\"incompatible\",\"a\":69,\"b\":62},{\"tag\":\"incompatible\",\"a\":70,\"b\":52},{\"tag\":\"incompatible\",\"a\":70,\"b\":53},{\"tag\":\"incompatible\",\"a\":70,\"b\":55},{\"tag\":\"incompatible\",\"a\":71,\"b\":45},{\"tag\":\"incompatible\",\"a\":73,\"b\":0},{\"tag\":\"incompatible\",\"a\":73,\"b\":34},{\"tag\":\"incompatible\",\"a\":73,\"b\":71},{\"tag\":\"incompatible\",\"a\":73,\"b\":72},{\"tag\":\"incompatible\",\"a\":75,\"b\":4},{\"tag\":\"incompatible\",\"a\":75,\"b\":38},{\"tag\":\"incompatible\",\"a\":75,\"b\":40},{\"tag\":\"incompatible\",\"a\":75,\"b\":63},{\"tag\":\"incompatible\",\"a\":75,\"b\":69},{\"tag\":\"incompatible\",\"a\":75,\"b\":73},{\"tag\":\"incompatible\",\"a\":77,\"b\":9},{\"tag\":\"incompatible\",\"a\":77,\"b\":39},{\"tag\":\"incompatible\",\"a\":77,\"b\":50},{\"tag\":\"incompatible\",\"a\":78,\"b\":2},{\"tag\":\"incompatible\",\"a\":78,\"b\":39},{\"tag\":\"incompatible\",\"a\":78,\"b\":71},{\"tag\":\"incompatible\",\"a\":78,\"b\":77},{\"tag\":\"incompatible\",\"a\":79,\"b\":3},{\"tag\":\"incompatible\",\"a\":79,\"b\":75},{\"tag\":\"incompatible\",\"a\":79,\"b\":78},{\"tag\":\"incompatible\",\"a\":80,\"b\":10},{\"tag\":\"incompatible\",\"a\":80,\"b\":32},{\"tag\":\"incompatible\",\"a\":80,\"b\":36},{\"tag\":\"incompatible\",\"a\":80,\"b\":42},{\"tag\":\"incompatible\",\"a\":80,\"b\":45},{\"tag\":\"incompatible\",\"a\":80,\"b\":51},{\"tag\":\"incompatible\",\"a\":80,\"b\":58},{\"tag\":\"incompatible\",\"a\":80,\"b\":71},{\"tag\":\"incompatible\",\"a\":80,\"b\":72},{\"tag\":\"incompatible\",\"a\":80,\"b\":77},{\"tag\":\"incompatible\",\"a\":81,\"b\":46},{\"tag\":\"incompatible\",\"a\":81,\"b\":72},{\"tag\":\"incompatible\",\"a\":81,\"b\":80},{\"tag\":\"incompatible\",\"a\":82,\"b\":47},{\"tag\":\"incompatible\",\"a\":82,\"b\":49},{\"tag\":\"incompatible\",\"a\":82,\"b\":62},{\"tag\":\"incompatible\",\"a\":82,\"b\":75},{\"tag\":\"mate\",\"ridge\":7,\"a\":1,\"owners\":[0,2,3,4,33,35,39,41]},{\"tag\":\"mate\",\"ridge\":7,\"a\":36,\"owners\":[0,2,3,4,35,41]},{\"tag\":\"mate\",\"ridge\":7,\"a\":41,\"owners\":[0,1,2,4,33,36,39]},{\"tag\":\"three\",\"ridge\":11,\"vertices\":[0,7,8]},{\"tag\":\"three\",\"ridge\":11,\"vertices\":[5,7,8]},{\"tag\":\"three\",\"ridge\":11,\"vertices\":[7,8,32]},{\"tag\":\"three\",\"ridge\":11,\"vertices\":[7,8,42]},{\"tag\":\"mate\",\"ridge\":13,\"a\":62,\"owners\":[0,16,32,33,35,58,59,61]},{\"tag\":\"mate\",\"ridge\":14,\"a\":75,\"owners\":[0,24,32,33,35,71,72,74]},{\"tag\":\"mate\",\"ridge\":19,\"a\":1,\"owners\":[5,9,10,43,44,50,51]},{\"tag\":\"mate\",\"ridge\":19,\"a\":37,\"owners\":[5,9,10,43,44,51]},{\"tag\":\"mate\",\"ridge\":19,\"a\":44,\"owners\":[1,9,10,37,38,50]},{\"tag\":\"mate\",\"ridge\":21,\"a\":65,\"owners\":[1,16,36,38,59,60]},{\"tag\":\"three\",\"ridge\":22,\"vertices\":[1,73,77]},{\"tag\":\"three\",\"ridge\":22,\"vertices\":[37,73,77]},{\"tag\":\"mate\",\"ridge\":35,\"a\":54,\"owners\":[2,9,11,32,42,45,53]},{\"tag\":\"mate\",\"ridge\":37,\"a\":64,\"owners\":[2,19,32,40,66]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[18,39,66]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[39,58,66]},{\"tag\":\"three\",\"ridge\":38,\"vertices\":[26,27,39]},{\"tag\":\"three\",\"ridge\":38,\"vertices\":[27,39,71]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[12,14,15]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[14,15,37]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[14,15,50]},{\"tag\":\"mate\",\"ridge\":259,\"a\":49,\"owners\":[4,14,38,40,54]},{\"tag\":\"mate\",\"ridge\":259,\"a\":57,\"owners\":[4,7,38,40,43,46]},{\"tag\":\"mate\",\"ridge\":262,\"a\":79,\"owners\":[4,25,38,73]},{\"tag\":\"mate\",\"ridge\":25,\"a\":67,\"owners\":[5,16,43,44,60]},{\"tag\":\"mate\",\"ridge\":25,\"a\":68,\"owners\":[5,16,42,43,58,60]},{\"tag\":\"three\",\"ridge\":25,\"vertices\":[44,60,67]},{\"tag\":\"mate\",\"ridge\":26,\"a\":73,\"owners\":[5,29,42,44,80,81]},{\"tag\":\"mate\",\"ridge\":26,\"a\":80,\"owners\":[5,24,43,44,73]},{\"tag\":\"three\",\"ridge\":73,\"vertices\":[22,46,67]},{\"tag\":\"three\",\"ridge\":74,\"vertices\":[30,46,72]},{\"tag\":\"three\",\"ridge\":74,\"vertices\":[30,46,80]},{\"tag\":\"mate\",\"ridge\":265,\"a\":62,\"owners\":[7,43,46,49]},{\"tag\":\"mate\",\"ridge\":266,\"a\":75,\"owners\":[7,43,46,49]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[15,49,51]},{\"tag\":\"mate\",\"ridge\":521,\"a\":8,\"owners\":[22,63,68,69]},{\"tag\":\"mate\",\"ridge\":521,\"a\":22,\"owners\":[8,35,44,48,49,63,69]},{\"tag\":\"mate\",\"ridge\":521,\"a\":68,\"owners\":[8,35,48,49,63,69]},{\"tag\":\"three\",\"ridge\":521,\"vertices\":[22,49,63]},{\"tag\":\"three\",\"ridge\":521,\"vertices\":[49,63,68]},{\"tag\":\"mate\",\"ridge\":522,\"a\":8,\"owners\":[30,76,81,82]},{\"tag\":\"mate\",\"ridge\":522,\"a\":30,\"owners\":[8,35,44,48,49,76,82]},{\"tag\":\"mate\",\"ridge\":522,\"a\":49,\"owners\":[30,76,81]},{\"tag\":\"mate\",\"ridge\":522,\"a\":81,\"owners\":[8,35,48,49,76,82]},{\"tag\":\"three\",\"ridge\":522,\"vertices\":[30,49,76]},{\"tag\":\"three\",\"ridge\":50,\"vertices\":[9,78,80]},{\"tag\":\"mate\",\"ridge\":81,\"a\":68,\"owners\":[10,23,36,64]},{\"tag\":\"three\",\"ridge\":81,\"vertices\":[10,64,68]},{\"tag\":\"three\",\"ridge\":97,\"vertices\":[11,64,70]},{\"tag\":\"three\",\"ridge\":97,\"vertices\":[23,39,70]},{\"tag\":\"three\",\"ridge\":97,\"vertices\":[39,67,70]},{\"tag\":\"three\",\"ridge\":98,\"vertices\":[11,77,83]},{\"tag\":\"three\",\"ridge\":98,\"vertices\":[31,39,83]},{\"tag\":\"three\",\"ridge\":98,\"vertices\":[39,80,83]},{\"tag\":\"mate\",\"ridge\":161,\"a\":19,\"owners\":[12,50,52,54,55,70]},{\"tag\":\"mate\",\"ridge\":161,\"a\":65,\"owners\":[12,52,54,55,70]},{\"tag\":\"mate\",\"ridge\":161,\"a\":66,\"owners\":[12,50,52,55,70]},{\"tag\":\"mate\",\"ridge\":162,\"a\":27,\"owners\":[12,50,52,54,55,83]},{\"tag\":\"mate\",\"ridge\":162,\"a\":78,\"owners\":[12,52,54,55,83]},{\"tag\":\"mate\",\"ridge\":162,\"a\":79,\"owners\":[12,50,52,55,83]},{\"tag\":\"mate\",\"ridge\":162,\"a\":83,\"owners\":[12,27,50,54,78,79]},{\"tag\":\"mate\",\"ridge\":577,\"a\":13,\"owners\":[22,68,70]},{\"tag\":\"mate\",\"ridge\":577,\"a\":51,\"owners\":[22,70]},{\"tag\":\"mate\",\"ridge\":578,\"a\":53,\"owners\":[30,81]},{\"tag\":\"mate\",\"ridge\":578,\"a\":56,\"owners\":[30,81]},{\"tag\":\"three\",\"ridge\":578,\"vertices\":[30,51,83]},{\"tag\":\"mate\",\"ridge\":386,\"a\":75,\"owners\":[14,54,57]},{\"tag\":\"mate\",\"ridge\":641,\"a\":15,\"owners\":[63,69,70]},{\"tag\":\"mate\",\"ridge\":641,\"a\":41,\"owners\":[69,70]},{\"tag\":\"mate\",\"ridge\":641,\"a\":48,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":641,\"a\":55,\"owners\":[63,69]},{\"tag\":\"mate\",\"ridge\":641,\"a\":56,\"owners\":[63,69]},{\"tag\":\"mate\",\"ridge\":641,\"a\":57,\"owners\":[63,70]},{\"tag\":\"mate\",\"ridge\":641,\"a\":70,\"owners\":[15,41,48,57,63,69]},{\"tag\":\"mate\",\"ridge\":642,\"a\":57,\"owners\":[76,83]},{\"tag\":\"mate\",\"ridge\":52,\"a\":64,\"owners\":[26,71,78]},{\"tag\":\"mate\",\"ridge\":164,\"a\":78,\"owners\":[19,66]},{\"tag\":\"mate\",\"ridge\":388,\"a\":62,\"owners\":[28,79]},{\"tag\":\"mate\",\"ridge\":584,\"a\":68,\"owners\":[30]},{\"tag\":\"mate\",\"ridge\":584,\"a\":81,\"owners\":[22]},{\"tag\":\"mate\",\"ridge\":112,\"a\":80,\"owners\":[23,64]},{\"tag\":\"mate\",\"ridge\":108,\"a\":84,\"owners\":[61,74]},{\"tag\":\"mate\",\"ridge\":652,\"a\":63,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":652,\"a\":76,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":736,\"a\":70,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":736,\"a\":83,\"owners\":[70]},{\"tag\":\"group_take\",\"kind\":1,\"index\":2,\"member\":2,\"full_literals\":[-3,82]},{\"tag\":\"group_take\",\"kind\":1,\"index\":7,\"member\":7,\"full_literals\":[-7,83]},{\"tag\":\"group_take\",\"kind\":1,\"index\":8,\"member\":8,\"full_literals\":[-8,84]},{\"tag\":\"group_take\",\"kind\":1,\"index\":10,\"member\":10,\"full_literals\":[-10,85]},{\"tag\":\"group_take\",\"kind\":1,\"index\":16,\"member\":16,\"full_literals\":[-16,86]},{\"tag\":\"group_take\",\"kind\":1,\"index\":19,\"member\":19,\"full_literals\":[-18,87]},{\"tag\":\"group_take\",\"kind\":1,\"index\":22,\"member\":22,\"full_literals\":[-19,88]},{\"tag\":\"group_take\",\"kind\":1,\"index\":23,\"member\":23,\"full_literals\":[-20,89]},{\"tag\":\"group_take\",\"kind\":1,\"index\":25,\"member\":25,\"full_literals\":[-22,90]},{\"tag\":\"group_take\",\"kind\":1,\"index\":26,\"member\":26,\"full_literals\":[-23,91]},{\"tag\":\"group_take\",\"kind\":1,\"index\":28,\"member\":28,\"full_literals\":[-25,92]},{\"tag\":\"group_take\",\"kind\":1,\"index\":29,\"member\":29,\"full_literals\":[-26,93]},{\"tag\":\"group_take\",\"kind\":1,\"index\":30,\"member\":30,\"full_literals\":[-27,94]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped1_0005\",\"right_name\":\"grouped1_0007\",\"joined_name\":\"grouped1_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-82,false,95],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0006\",\"joined_name\":\"grouped1_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-95,96],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped1_0010\",\"right_name\":\"grouped1_0012\",\"joined_name\":\"grouped1_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-83,97],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped1_0008\",\"right_name\":\"grouped1_0011\",\"joined_name\":\"grouped1_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-97,98],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0009\",\"joined_name\":\"grouped1_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-98,99],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0009\",\"joined_name\":\"grouped1_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-96,-98,100],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped1_0013\",\"right_name\":\"grouped1_0017\",\"joined_name\":\"grouped1_0014\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-84,false,101],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped1_0018\",\"right_name\":\"grouped1_0020\",\"joined_name\":\"grouped1_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-85,false,102],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8,9],\"right\":[10,11],\"left_name\":\"grouped1_0014\",\"right_name\":\"grouped1_0019\",\"joined_name\":\"grouped1_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-101,false,103],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8,9],\"right\":[10,11],\"left_name\":\"grouped1_0014\",\"right_name\":\"grouped1_0019\",\"joined_name\":\"grouped1_0015\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-101,-102,104],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8,9,10,11],\"right\":[12,13,14,15],\"left_name\":\"grouped1_0015\",\"right_name\":\"grouped1_0021\",\"joined_name\":\"grouped1_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-103,false,105],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8,9,10,11],\"right\":[12,13,14,15],\"left_name\":\"grouped1_0015\",\"right_name\":\"grouped1_0021\",\"joined_name\":\"grouped1_0016\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-104,false,106],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7],\"right\":[8,9,10,11,12,13,14,15],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0003\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-99,-105,107],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7],\"right\":[8,9,10,11,12,13,14,15],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0003\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-99,-106,108],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7],\"right\":[8,9,10,11,12,13,14,15],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0003\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-100,-105,108],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16],\"right\":[17],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0027\",\"joined_name\":\"grouped1_0023\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-86,false,109],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[18],\"right\":[19],\"left_name\":\"grouped1_0028\",\"right_name\":\"grouped1_0030\",\"joined_name\":\"grouped1_0029\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-87,110],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16,17],\"right\":[18,19],\"left_name\":\"grouped1_0023\",\"right_name\":\"grouped1_0029\",\"joined_name\":\"grouped1_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-110,111],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16,17],\"right\":[18,19],\"left_name\":\"grouped1_0023\",\"right_name\":\"grouped1_0029\",\"joined_name\":\"grouped1_0024\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-109,false,111],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16,17],\"right\":[18,19],\"left_name\":\"grouped1_0023\",\"right_name\":\"grouped1_0029\",\"joined_name\":\"grouped1_0024\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-109,-110,112],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[22],\"right\":[23],\"left_name\":\"grouped1_0033\",\"right_name\":\"grouped1_0035\",\"joined_name\":\"grouped1_0034\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-89,113],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[22],\"right\":[23],\"left_name\":\"grouped1_0033\",\"right_name\":\"grouped1_0035\",\"joined_name\":\"grouped1_0034\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-88,false,113],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[22],\"right\":[23],\"left_name\":\"grouped1_0033\",\"right_name\":\"grouped1_0035\",\"joined_name\":\"grouped1_0034\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-88,-89,114],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[20,21],\"right\":[22,23],\"left_name\":\"grouped1_0031\",\"right_name\":\"grouped1_0034\",\"joined_name\":\"grouped1_0032\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-113,115],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[20,21],\"right\":[22,23],\"left_name\":\"grouped1_0031\",\"right_name\":\"grouped1_0034\",\"joined_name\":\"grouped1_0032\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-114,116],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16,17,18,19],\"right\":[20,21,22,23],\"left_name\":\"grouped1_0024\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0025\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-115,117],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16,17,18,19],\"right\":[20,21,22,23],\"left_name\":\"grouped1_0024\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0025\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-116,118],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16,17,18,19],\"right\":[20,21,22,23],\"left_name\":\"grouped1_0024\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0025\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-111,false,117],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16,17,18,19],\"right\":[20,21,22,23],\"left_name\":\"grouped1_0024\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0025\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-111,-115,118],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16,17,18,19],\"right\":[20,21,22,23],\"left_name\":\"grouped1_0024\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0025\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-112,false,118],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[24],\"right\":[25],\"left_name\":\"grouped1_0036\",\"right_name\":\"grouped1_0040\",\"joined_name\":\"grouped1_0037\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-90,119],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[26],\"right\":[27],\"left_name\":\"grouped1_0041\",\"right_name\":\"grouped1_0043\",\"joined_name\":\"grouped1_0042\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-91,false,120],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[24,25],\"right\":[26,27],\"left_name\":\"grouped1_0037\",\"right_name\":\"grouped1_0042\",\"joined_name\":\"grouped1_0038\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-120,121],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[24,25],\"right\":[26,27],\"left_name\":\"grouped1_0037\",\"right_name\":\"grouped1_0042\",\"joined_name\":\"grouped1_0038\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-119,false,121],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[28],\"right\":[29],\"left_name\":\"grouped1_0044\",\"right_name\":\"grouped1_0047\",\"joined_name\":\"grouped1_0045\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-93,122],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[28],\"right\":[29],\"left_name\":\"grouped1_0044\",\"right_name\":\"grouped1_0047\",\"joined_name\":\"grouped1_0045\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-92,false,122],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[30],\"right\":[31],\"left_name\":\"grouped1_0048\",\"right_name\":\"grouped1_0050\",\"joined_name\":\"grouped1_0049\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-94,false,123],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[28,29],\"right\":[30,31],\"left_name\":\"grouped1_0045\",\"right_name\":\"grouped1_0049\",\"joined_name\":\"grouped1_0046\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-123,124],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[28,29],\"right\":[30,31],\"left_name\":\"grouped1_0045\",\"right_name\":\"grouped1_0049\",\"joined_name\":\"grouped1_0046\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-122,-123,125],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[24,25,26,27],\"right\":[28,29,30,31],\"left_name\":\"grouped1_0038\",\"right_name\":\"grouped1_0046\",\"joined_name\":\"grouped1_0039\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-124,126],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[24,25,26,27],\"right\":[28,29,30,31],\"left_name\":\"grouped1_0038\",\"right_name\":\"grouped1_0046\",\"joined_name\":\"grouped1_0039\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-125,127],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[24,25,26,27],\"right\":[28,29,30,31],\"left_name\":\"grouped1_0038\",\"right_name\":\"grouped1_0046\",\"joined_name\":\"grouped1_0039\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-121,-124,127],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16,17,18,19,20,21,22,23],\"right\":[24,25,26,27,28,29,30,31],\"left_name\":\"grouped1_0025\",\"right_name\":\"grouped1_0039\",\"joined_name\":\"grouped1_0026\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-127,128],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16,17,18,19,20,21,22,23],\"right\":[24,25,26,27,28,29,30,31],\"left_name\":\"grouped1_0025\",\"right_name\":\"grouped1_0039\",\"joined_name\":\"grouped1_0026\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-117,-126,128],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16,17,18,19,20,21,22,23],\"right\":[24,25,26,27,28,29,30,31],\"left_name\":\"grouped1_0025\",\"right_name\":\"grouped1_0039\",\"joined_name\":\"grouped1_0026\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-117,-127,129],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[16,17,18,19,20,21,22,23],\"right\":[24,25,26,27,28,29,30,31],\"left_name\":\"grouped1_0025\",\"right_name\":\"grouped1_0039\",\"joined_name\":\"grouped1_0026\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-118,-126,129],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],\"right\":[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0026\",\"joined_name\":\"groupKind1\",\"a\":2,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-107,-129,130],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],\"right\":[16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0026\",\"joined_name\":\"groupKind1\",\"a\":3,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-108,-128,130],\"grouped\":true,\"kind\":1},{\"tag\":\"quota_upper\",\"kind\":1,\"quota\":4,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[34,47,48,62,75],\"full_literals\":[-131,31,44,45,59,72]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[33,44,45,46,51,68,81],\"full_literals\":[-132,30,41,42,43,48,65,78]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[37,40,41,54,66,79],\"full_literals\":[-133,34,37,38,51,63,76]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[32,39,50,65,78],\"full_literals\":[-134,29,36,47,62,75]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[35,38,43,60,73],\"full_literals\":[-135,32,35,40,57,70]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[52,53,55,56],\"full_literals\":[-136,49,50,52,53]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[49,57],\"full_literals\":[-137,46,54]},{\"tag\":\"group_take\",\"kind\":2,\"index\":6,\"member\":57,\"full_literals\":[-54,137]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[36,42,59,64,72,77],\"full_literals\":[-138,33,39,56,61,69,74]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[58,67,71,80],\"full_literals\":[-139,55,64,68,77]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0051\",\"right_name\":\"grouped2_0055\",\"joined_name\":\"grouped2_0052\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-140,131,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0051\",\"right_name\":\"grouped2_0055\",\"joined_name\":\"grouped2_0052\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-140,false,132],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0056\",\"right_name\":\"grouped2_0058\",\"joined_name\":\"grouped2_0057\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-141,133,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0056\",\"right_name\":\"grouped2_0058\",\"joined_name\":\"grouped2_0057\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-141,false,134],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0057\",\"joined_name\":\"grouped2_0053\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-142,140,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0052\",\"right_name\":\"grouped2_0057\",\"joined_name\":\"grouped2_0053\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-142,false,141],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0059\",\"right_name\":\"grouped2_0062\",\"joined_name\":\"grouped2_0060\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-143,135,136],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0059\",\"right_name\":\"grouped2_0062\",\"joined_name\":\"grouped2_0060\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-144,135,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0059\",\"right_name\":\"grouped2_0062\",\"joined_name\":\"grouped2_0060\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-144,false,136],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0065\",\"right_name\":\"grouped2_0067\",\"joined_name\":\"grouped2_0066\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-145,138,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0065\",\"right_name\":\"grouped2_0067\",\"joined_name\":\"grouped2_0066\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-145,false,139],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0063\",\"right_name\":\"grouped2_0066\",\"joined_name\":\"grouped2_0064\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-146,137,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0063\",\"right_name\":\"grouped2_0066\",\"joined_name\":\"grouped2_0064\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-146,false,145],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0060\",\"right_name\":\"grouped2_0064\",\"joined_name\":\"grouped2_0061\",\"a\":0,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-147,143,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0060\",\"right_name\":\"grouped2_0064\",\"joined_name\":\"grouped2_0061\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-147,144,146],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0060\",\"right_name\":\"grouped2_0064\",\"joined_name\":\"grouped2_0061\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-148,144,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0060\",\"right_name\":\"grouped2_0064\",\"joined_name\":\"grouped2_0061\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-148,false,146],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0053\",\"right_name\":\"grouped2_0061\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-149,142,148],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0053\",\"right_name\":\"grouped2_0061\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-149,false,147],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":61,\"full_literals\":[-58,150]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":70,\"full_literals\":[-67,151]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":74,\"full_literals\":[-71,152]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[83],\"full_literals\":[-153,80]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":83,\"full_literals\":[-80,153]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[84],\"full_literals\":[-154,81]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":84,\"full_literals\":[-81,154]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[63,69],\"full_literals\":[-155,60,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":63,\"full_literals\":[-60,155]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[76,82],\"full_literals\":[-156,73,79]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":76,\"full_literals\":[-73,156]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0071\",\"right_name\":\"grouped3_0073\",\"joined_name\":\"grouped3_0072\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-152,157],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0071\",\"right_name\":\"grouped3_0073\",\"joined_name\":\"grouped3_0072\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-151,false,157],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0071\",\"right_name\":\"grouped3_0073\",\"joined_name\":\"grouped3_0072\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-151,-152,158],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0068\",\"right_name\":\"grouped3_0072\",\"joined_name\":\"grouped3_0069\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-157,159],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0068\",\"right_name\":\"grouped3_0072\",\"joined_name\":\"grouped3_0069\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-158,160],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0068\",\"right_name\":\"grouped3_0072\",\"joined_name\":\"grouped3_0069\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-150,false,159],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0074\",\"right_name\":\"grouped3_0077\",\"joined_name\":\"grouped3_0075\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-161,153,154],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0074\",\"right_name\":\"grouped3_0077\",\"joined_name\":\"grouped3_0075\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-153,false,161],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0074\",\"right_name\":\"grouped3_0077\",\"joined_name\":\"grouped3_0075\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-153,-154,162],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0078\",\"right_name\":\"grouped3_0080\",\"joined_name\":\"grouped3_0079\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-163,155,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0078\",\"right_name\":\"grouped3_0080\",\"joined_name\":\"grouped3_0079\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-163,false,156],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0078\",\"right_name\":\"grouped3_0080\",\"joined_name\":\"grouped3_0079\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-155,-156,163],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0075\",\"right_name\":\"grouped3_0079\",\"joined_name\":\"grouped3_0076\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-165,161,163],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0075\",\"right_name\":\"grouped3_0079\",\"joined_name\":\"grouped3_0076\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-163,165],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0075\",\"right_name\":\"grouped3_0079\",\"joined_name\":\"grouped3_0076\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-161,false,164],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0075\",\"right_name\":\"grouped3_0079\",\"joined_name\":\"grouped3_0076\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-162,false,165],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0069\",\"right_name\":\"grouped3_0076\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-159,-165,166],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0069\",\"right_name\":\"grouped3_0076\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-160,-164,166],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"block\",\"leaf\":0,\"vertices\":[14,15,16,22,49,62,65,67,70,73,77,79,81,83]},{\"tag\":\"block\",\"leaf\":1,\"vertices\":[7,8,16,22,57,62,65,67,70,73,77,79,81,83]},{\"tag\":\"block\",\"leaf\":2,\"vertices\":[14,15,24,30,49,60,64,66,68,70,75,78,80,83]},{\"tag\":\"block\",\"leaf\":3,\"vertices\":[7,8,24,30,57,60,64,66,68,70,75,78,80,83]},{\"tag\":\"edge\",\"edge\":29,\"owners\":[8,22,30,35,44,48,49,63,68,69,76,81,82]},{\"tag\":\"edge\",\"edge\":30,\"owners\":[9,18,23,26,31,42,50,58,64,65,67,71,77,78,80,84]},{\"tag\":\"edge\",\"edge\":36,\"owners\":[12,19,27,50,52,54,55,65,66,70,78,79,83]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[13,22,30,51,53,56,68,70,81,83]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[15,41,48,55,56,57,63,69,70,76,82,83]}]}"
  "366 147 0 326 325 0\n367 143 0 366 320 0\n368 27 19 13 67 0 211 228 234 212 213 227 364 0\n369 -53 -137 0 47 60 303 0\n370 -42 -139 0 62 91 108 133 306 0\n371 -1 -135 0 2 7 15 64 109 301 0\n372 -4 -133 0 6 11 12 41 86 126 299 0\n373 -3 36 -134 0 1 40 83 122 300 0\n374 -46 -65 -155 0 103 188 334 0\n375 -54 67 0 234 49 56 57 58 59 206 205 203 204 207 208 363 0\n376 -46 -165 0 356 354 341 338 329 343 327 230 332 339 328 234 330 344 350 348 347 103 143 374 334 336 187 193 210 368 0\n377 -60 -165 0 356 326 354 341 339 328 375 376 303 318 323 324 311 307 218 75 76 77 116 297 0\n378 -165 0 356 326 354 341 343 338 339 327 329 328 230 218 234 332 330 344 350 347 375 376 303 318 323 324 311 307 377 334 101 102 104 117 297 0\n379 -163 0 378 351 0\n380 -162 0 378 353 0\n381 67 54 -72 45 60 0 117 219 220 145 232 234 217 216 365 0\n382 137 -72 45 60 0 366 117 219 220 304 318 321 315 381 105 106 302 0\n383 75 77 -63 47 12 51 -134 55 39 29 -67 76 0 380 88 233 331 346 333 209 300 165 9 80 120 163 166 198 199 201 362 0\n384 -78 -63 47 12 51 38 4 -134 -139 -138 56 55 39 32 29 1 -67 -72 0 127 113 140 141 383 122 124 125 147 306 305 94 0\n385 -75 -27 -65 -63 -14 -15 38 4 -139 -138 -57 -46 -67 -72 0 100 70 69 35 34 33 32 28 27 233 118 113 122 124 125 147 306 137 177 305 359 0\n386 38 54 -72 45 60 0 367 366 326 381 105 117 220 219 106 302 315 322 324 312 309 372 310 311 308 321 319 317 316 382 303 32 118 114 34 313 301 70 69 37 36 35 33 30 29 27 233 127 115 232 222 42 183 215 167 168 169 299 88 384 298 191 385 300 383 202 0\n387 54 -72 45 60 0 382 115 114 113 303 386 13 43 170 0\n388 -77 75 62 -134 -80 47 0 130 202 300 0\n389 29 77 75 -63 -134 -67 51 47 12 76 0 88 300 14 164 383 0\n390 -29 -135 70 35 0 4 17 65 301 0\n391 75 29 -63 -134 -80 -67 51 47 12 76 0 88 388 389 0\n392 32 57 -72 45 60 0 367 387 57 117 220 219 221 106 302 313 55 145 118 114 232 301 16 22 185 192 190 186 361 0\n393 -32 46 -72 0 3 19 24 182 0\n394 -64 -72 45 60 0 366 367 326 387 55 393 392 70 69 66 127 49 56 58 221 232 223 57 117 220 219 106 302 315 322 324 312 310 51 115 52 309 299 114 118 313 390 391 122 113 48 371 147 125 311 308 321 319 317 370 316 145 90 92 94 100 175 384 305 298 179 23 178 361 0\n395 -43 -72 45 60 0 366 367 326 114 387 51 127 49 56 58 221 232 223 57 117 220 219 106 302 315 322 324 312 310 115 52 309 299 118 313 390 391 124 55 393 392 69 321 319 317 394 306 129 123 113 371 48 122 66 146 194 157 141 145 23 97 180 185 361 0\n396 -72 45 60 0 367 366 356 326 232 113 114 115 117 118 127 220 219 387 48 49 51 52 55 56 57 58 221 223 106 328 331 302 345 315 313 352 321 322 371 355 319 324 342 316 317 311 312 340 370 308 309 310 329 299 390 391 122 123 124 125 393 147 392 66 68 69 70 146 394 306 129 132 134 137 141 194 154 305 157 395 171 298 227 186 360 0\n397 -77 129 6 39 40 -65 -59 0 227 247 284 285 287 293 277 87 74 129 131 135 136 174 239 263 266 267 275 276 264 292 271 240 289 268 225 280 242 279 195 244 224 0\n398 127 77 6 39 -123 41 78 -59 0 285 72 71 288 289 286 281 282 283 278 246 245 243 176 226 172 0\n399 -65 78 43 46 32 -59 45 60 0 296 104 95 96 98 99 227 186 247 16 237 284 181 254 149 236 151 152 150 256 250 258 251 252 260 294 397 398 290 292 295 273 275 261 271 266 259 268 263 257 242 239 255 153 238 61 82 195 0\n400 -8 65 78 43 46 -59 60 0 296 144 104 87 73 232 16 21 184 189 237 181 241 247 254 236 151 152 150 269 284 256 250 271 285 258 251 273 287 252 291 260 295 294 262 293 292 253 274 276 398 249 272 265 248 270 264 235 242 240 162 229 0\n401 41 8 65 78 46 32 -59 45 60 0 144 104 232 185 190 361 0\n402 -41 43 46 -59 0 20 22 181 0\n403 -67 56 33 61 -7 -8 -78 46 32 52 53 -59 0 367 366 326 152 151 16 228 141 140 87 74 73 72 105 106 233 302 315 313 321 322 301 318 319 324 111 303 316 317 312 51 52 56 58 305 309 310 120 125 159 299 300 158 84 358 306 0\n404 67 -59 45 60 0 104 219 220 144 232 234 375 217 216 365 0\n405 -56 68 77 -139 0 63 93 306 0\n406 -33 1 -54 32 -134 5 0 52 48 10 147 373 0\n407 -78 43 46 32 -67 52 53 -59 45 73 0 367 326 366 87 105 106 302 315 321 318 303 51 73 58 52 322 324 312 309 299 128 56 310 319 317 313 144 74 72 71 141 192 16 181 149 151 301 111 405 406 403 80 85 300 0\n408 43 46 32 -59 45 60 0 404 104 219 220 232 402 407 399 400 401 0\n409 46 32 60 -59 45 0 408 23 25 97 139 401 0\n410 -61 -65 48 -46 42 1 -134 -133 -67 63 37 5 0 35 34 33 30 29 28 106 78 79 80 81 85 196 197 156 373 300 155 161 128 148 299 0\n411 -74 64 68 29 144 0 366 326 322 324 312 310 321 319 317 120 121 125 138 300 306 84 0\n412 78 69 68 -46 1 144 -67 63 37 5 73 0 366 326 37 35 33 30 29 322 324 311 308 321 319 317 370 312 310 309 316 233 191 214 298 98 100 410 411 305 61 131 306 0\n413 -33 77 68 -139 0 61 89 306 0\n414 -74 32 -59 45 60 0 326 367 366 404 105 104 220 219 106 302 315 321 319 317 313 72 74 409 34 301 111 232 71 73 87 371 112 412 141 413 228 55 35 33 30 29 28 370 322 324 312 310 309 233 119 120 121 125 200 159 160 411 373 300 148 173 161 222 299 170 357 0\n415 32 -59 45 60 0 366 367 404 105 104 220 219 106 302 313 371 315 321 319 317 316 87 74 73 72 71 232 409 33 34 301 111 112 412 141 405 413 414 305 82 94 306 0\n416 -59 45 60 0 415 3 19 24 32 181 0\n417 -31 0 366 5 8 18 31 50 67 110 303 301 318 314 321 0\n418 -67 -136 53 52 0 105 106 302 0\n419 45 -131 60 0 417 366 232 396 416 297 26 38 44 53 102 142 303 220 318 321 315 418 234 216 365 0\n420 -45 0 366 39 45 46 54 218 303 418 318 315 321 0\n421 -67 -148 0 323 318 369 322 315 107 418 0\n422 60 0 326 420 232 419 307 311 324 323 318 369 421 234 375 303 103 143 219 217 216 365 0\n423 73 0 422 231 0\n424 155 0 422 335 0\n425 156 0 423 337 0\n426 0 424 425 379 349 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record010.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record010.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record010.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record010.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record010 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeafTable : ConcreteGrowth.Table (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record010.l) :=
(.branch 2
 (.branch 1
 (.leaf (⟨0, by decide⟩))
 (.leaf (⟨1, by decide⟩)))
 (.branch 3
 (.leaf (⟨0, by decide⟩))
 (.leaf (⟨1, by decide⟩))))
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record010.l := originalLeafTable.get j.val
def orbitWordTable : ConcreteGrowth.Table (List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record010.g)) :=
(.branch 2
 (.branch 1
 (.leaf ([]))
 (.leaf ([])))
 (.branch 3
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩]))))
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record010.g) := orbitWordTable.get j.val
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record010.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record010.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record010 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record010_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record010 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record010_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00051.record010_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00051.record010
