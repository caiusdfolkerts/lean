module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow29Part00015Data
public import GraphInputsRow29Part00015Frames
public import GraphInputsRow29Part00015Leaves
public import GraphInputsRow29Part00015Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00015.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record001
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨51, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨72, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), 9500467658752, (certNat% 4), 536870912]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), (certNat% 3), (certNat% 6), (certNat% 7), 13247826624512, 825170591744, 52789443035136]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c1 c0
  c2
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record001_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00015.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00015.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record002
def vertexColumn : Fields := ⟨10, (certNat% 8)⟩
def kindColumn : Fields := ⟨3, (certNat% 9)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [1, 2, 3, 4]
def candidates : List (Fin raw.n) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), (certNat% 11), 585467951558164480, (certNat% 12)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .size 1
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c2 c3
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c2 c4
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c2 c5
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), (certNat% 14), 285873023221760, (certNat% 12)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c2 c3
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), 585467951558164480]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), 585467951558164480, 1152921504606846976]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c2 c15
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c2 c16
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), (certNat% 18), 585467951558164480]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), 844424930131968, 585467951558164480, 1152921504606846976]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c21 c14
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), (certNat% 12), 285873023221760, 1017813515785732096, 1152921504606846976]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c23 c22
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c24 c9
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c25 c0
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 21), (certNat% 22), (certNat% 23), 285873023221760, 1017813517933215744, 1170935911706263552]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c27 c26
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), 585467951558164480, (certNat% 25), (certNat% 26), (certNat% 27), 2199023255552]
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 28), (certNat% 11), (certNat% 29), (certNat% 30), (certNat% 31), 1099511627776]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 32), 9007201402224640, (certNat% 26), (certNat% 33), (certNat% 34)]
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 35), (certNat% 26), (certNat% 36), 1128098930098176, (certNat% 37), 585467951558164480]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c32 c31
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [(certNat% 38)]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c2 c34
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c35 c35
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 39), 594475150812905472, (certNat% 12), (certNat% 37)]
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c37 c36
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 40), 844429225099264, 585467953705648128, 1170935903116328960, (certNat% 41)]
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c39 c38
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 42), (certNat% 43), (certNat% 44), 285878391930880, 3746994889972252672, 729583139634020352]
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c41 c40
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 45), 3746994889972252672, (certNat% 26), (certNat% 46), 585467953705648128]
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 47), (certNat% 22), 286972534849536, (certNat% 23), (certNat% 48), (certNat% 49)]
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 50), (certNat% 22), (certNat% 51), (certNat% 48), 1017813517933215744, 18014398509481984]
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 52), (certNat% 53), 2306405963462082560, (certNat% 54), 1017813519006957568, (certNat% 55), (certNat% 11)]
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c46 c45
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c47 c44
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c48 c43
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c49 c42
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c50 c33
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c51 c30
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c52 c29
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c53 c28
  c54
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record002_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00015.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00015.record008
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record008
def vertexColumn : Fields := ⟨10, (certNat% 56)⟩
def kindColumn : Fields := ⟨3, (certNat% 57)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 58), (certNat% 59), (certNat% 60), (certNat% 61), (certNat% 62)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 63), (certNat% 64), (certNat% 65), 3458764517041766400, 144115222435594240]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 66), (certNat% 67), 216172816473522176, 3458764517041766400, (certNat% 68)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 69), (certNat% 70), (certNat% 71), (certNat% 72), (certNat% 73)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 74), (certNat% 75), (certNat% 76), (certNat% 59), (certNat% 77)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 78), 2449958232723030016, (certNat% 79), (certNat% 60), (certNat% 80), (certNat% 81)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c9 c0
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 82), 4035225266123964416, (certNat% 83), 9529616811515969536, (certNat% 84)]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c13 c14
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c13 c15
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c13 c16
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 85), (certNat% 84), (certNat% 41), (certNat% 86)]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 87), (certNat% 86), (certNat% 88), (certNat% 83)]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 89), (certNat% 90), (certNat% 91), (certNat% 92), 2449958232723030016]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c21 c20
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c22 c19
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 93), (certNat% 83), 216172816473522176, 3458764517041766400, (certNat% 94), (certNat% 95)]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c24 c23
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c25 c11
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 96), (certNat% 97), (certNat% 98), (certNat% 99), (certNat% 41)]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 100), (certNat% 101), (certNat% 97), (certNat% 102), (certNat% 41)]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 103), 144115188075855872, (certNat% 97), (certNat% 104), (certNat% 59)]
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 105), (certNat% 106), (certNat% 107), (certNat% 104), (certNat% 108)]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 109), (certNat% 97), (certNat% 110), (certNat% 111), (certNat% 72), (certNat% 112)]
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c31 c30
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c32 c29
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c33 c28
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c34 c27
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 113), (certNat% 114), (certNat% 59), 216172833653391360, (certNat% 115)]
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 116), 2449958232723030016, 81064810606755840, (certNat% 80), (certNat% 117), (certNat% 118)]
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c37 c36
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 119), (certNat% 76), (certNat% 72), 72059793061183488, (certNat% 120)]
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 121), (certNat% 59), (certNat% 104), 90074191839100928, (certNat% 122), (certNat% 117)]
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c40 c39
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 123), (certNat% 59), (certNat% 117), (certNat% 124), (certNat% 125), (certNat% 126), 9250393776352919552]
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c42 c41
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c43 c38
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c44 c35
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c45 c26
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c46 c10
  c47
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record008_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record008_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00015.record008

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00015.record000
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3a2e4b329cb8acaa6ac6a5aa98e6a5a361da8e8b86e87ba1e47315c789ca569c6559694e5655351d58d4b46d47783c8ea368ce3c4e9364e334cc73c2e8b62e2b4ac6b86d1b31c970dc8f0bfa0c605ca8a1a168a6198561381e68519164a5194551341d28c6314c4b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "26db6d249b4da49b6db4926d36936926db69b6da492491249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record000 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record000 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record000.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record000.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record000.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 29), (facetIndex 30), (facetIndex 31), (facetIndex 32), (facetIndex 33)]))
 (.leaf ([(facetIndex 34), (facetIndex 35), (facetIndex 53), (facetIndex 62), (facetIndex 63)])))
 (.branch 3
 (.leaf ([(facetIndex 71), (facetIndex 80), (facetIndex 81)]))
 (.leaf ([(facetIndex 36), (facetIndex 54), (facetIndex 72)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 42), (facetIndex 57), (facetIndex 75)]))
 (.leaf ([(facetIndex 49), (facetIndex 50), (facetIndex 61), (facetIndex 70)])))
 (.branch 7
 (.leaf ([(facetIndex 79), (facetIndex 88)]))
 (.leaf ([(facetIndex 48), (facetIndex 60), (facetIndex 78)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6000012dc080354000026f0200c816f00010000324z19;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 55), (facetIndex 56), (facetIndex 58), (facetIndex 59)]))
 (.leaf ([(facetIndex 64), (facetIndex 67)])))
 (.branch 3
 (.leaf ([(facetIndex 73), (facetIndex 74), (facetIndex 76), (facetIndex 77)]))
 (.leaf ([(facetIndex 82), (facetIndex 85)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 37), (facetIndex 39), (facetIndex 41), (facetIndex 43), (facetIndex 45)]))
 (.leaf ([(facetIndex 38), (facetIndex 40), (facetIndex 44), (facetIndex 46), (facetIndex 47)])))
 (.branch 7
 (.leaf ([(facetIndex 51), (facetIndex 65), (facetIndex 66), (facetIndex 68), (facetIndex 69)]))
 (.leaf ([(facetIndex 52), (facetIndex 83), (facetIndex 84), (facetIndex 86), (facetIndex 87)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "fdfec00120900363b1000000007c00b6582596z1c;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [2, 3]
def grouped2_0007 : List Nat := [3]
def grouped2_0008 : List Nat := [4]
def grouped2_0009 : List Nat := [4, 5]
def grouped2_0010 : List Nat := [4, 5, 6, 7]
def grouped2_0011 : List Nat := [5]
def grouped2_0012 : List Nat := [6]
def grouped2_0013 : List Nat := [6, 7]
def grouped2_0014 : List Nat := [7]
def grouped3_0015 : List Nat := [0, 1, 2, 3]
def grouped3_0017 : List Nat := [4]
def grouped3_0018 : List Nat := [4, 5]
def grouped3_0019 : List Nat := [4, 5, 6, 7]
def grouped3_0020 : List Nat := [5]
def grouped3_0021 : List Nat := [6]
def grouped3_0022 : List Nat := [6, 7]
def grouped3_0023 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record000 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record000_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00015.record000" "{\"atoms\":[{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00015.record000" 81

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00015.record000" "{\"ridges\":[[4,133],[16,273],[22,164],[27,776],[30,131],[30,133],[32,131],[32,133],[33,133],[34,265],[34,273],[35,522],[37,298],[38,553],[39,394],[40,649],[43,306],[44,561],[45,402],[46,657],[49,289],[50,546],[53,273],[55,300],[56,396],[58,308],[59,404],[61,289],[61,385],[62,273],[63,265],[63,776],[64,360],[65,553],[66,649],[67,368],[68,561],[69,657],[70,800],[73,556],[74,652],[76,564],[77,660],[78,164],[80,522],[80,530],[81,522],[81,776],[82,616],[83,298],[84,394],[85,624],[88,800]],\"owners\":[[30,131,[9,45,46,48,49,50,52],[4,32,33,39,40]],[32,131,[9,39,40,48,49,50,52],[4,30,33,45,46]],[4,133,[14,56,59,60,61],[30,32,33]],[30,133,[14,59,60,61],[4,32,33,56]],[32,133,[14,56,60,61],[4,30,33,59]],[33,133,[14,56,59,61],[4,30,32,60]],[22,164,[14,60,61],[78,79]],[78,164,[14,61],[22,60,79]],[34,265,[55,56,64,65,66],[16,37,39,41,53,62,63]],[63,265,[37,39,55,56,64],[16,34,41,53,62,65,66]],[16,273,[43,45,47,58,59,67,68,69],[34,53,62,63]],[34,273,[58,59,67,68,69],[16,43,45,47,53,62,63]],[53,273,[43,45,47,67,68,69],[16,34,58,59,62,63]],[62,273,[43,45,47,58,59,68,69],[16,34,53,63,67]],[49,289,[55,58,64,65,67,68],[17,37,43,51,61,70]],[61,289,[37,43,51,64,65,67,68],[17,49,55,58,70]],[61,385,[39,45,52,66,69],[17,49,56,59,70]],[35,522,[73,74,82,83,84],[24,38,40,41,71,80,81]],[80,522,[38,40,41,73,74,83,84],[24,35,71,81,82]],[81,522,[38,40,73,74,82],[24,35,41,71,80,83,84]],[80,530,[44,46,47,76,77,86,87],[24,35,71,81,85]],[50,546,[73,76,82,83,85,86],[25,38,44,51,79,88]],[27,776,[41,65,66,83,84],[63,81]],[63,776,[83,84],[27,41,65,66,81]],[81,776,[65,66],[27,41,63,83,84]],[70,800,[83,86],[28,51,65,68,88]],[88,800,[65,68],[28,51,70,83,86]],[37,298,[83],[]],[83,298,[37],[]],[38,553,[65],[]],[65,553,[38],[]],[39,394,[84],[]],[84,394,[39],[]],[40,649,[66],[]],[66,649,[40],[]],[43,306,[86],[]],[44,561,[68],[]],[68,561,[44],[]],[45,402,[87],[]],[46,657,[69],[]],[69,657,[46],[]],[55,300,[],[]],[56,396,[],[]],[58,308,[],[]],[59,404,[],[]],[64,360,[],[]],[67,368,[],[]],[73,556,[],[]],[74,652,[],[]],[76,564,[],[]],[77,660,[],[]],[82,616,[],[]],[85,624,[],[]]],\"edges\":[[21,[4,14,22,30,32,33,56,59,60,61,74,77,78,79]],[28,[16,27,34,37,39,41,53,55,56,62,63,64,65,66,81,83,84]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00015.record000" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00015.record000\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-25,-3],[-34,-7],[-34,-9],[-34,-11],[-34,-25],[-35,-29],[-35,-34],[-40,-23],[-42,-40],[-43,-10],[-43,-27],[-43,-39],[-43,-42],[-44,-18],[-44,-23],[-44,-28],[-51,-2],[-51,-24],[-51,-25],[-51,-26],[-51,-45],[-51,-50],[-55,-21],[-56,-8],[-58,-16],[-59,-10],[-8,2,21,22,24,25,26,28],[-10,2,16,17,24,25,26,28],[-1,3,31,33,34,35],[-8,3,33,34,35],[-10,3,31,34,35],[-11,3,31,33,35],[-5,3,34,35],[-50,3,35],[-12,30,31,38,39,40],[-37,14,16,30,31,38],[-4,19,21,23,32,33,41,42,43],[-12,32,33,41,42,43],[-29,19,21,23,41,42,43],[-36,19,21,23,32,33,42,43],[-25,30,32,38,39,41,42],[-35,14,19,27,38,39,41,42],[-35,16,21,28,40,43],[-13,46,47,54,55,56],[-52,15,17,18,46,47,55,56],[-53,15,17,46,47,54],[-52,20,22,23,48,49,58,59],[-26,46,48,54,55,57,58],[-6,18,39,40,55,56],[-37,55,56],[-53,39,40],[-44,55,58],[-60,39,42],[-14,55],[-55,14],[-15,39],[-39,15],[-16,56],[-56,16],[-17,40],[-40,17],[-19,58],[-20,42],[-42,20],[-21,59],[-22,43],[-43,22],[-30],[-31],[-32],[-33],[-38],[-41],[-46],[-47],[-48],[-49],[-54],[-57],[-61,7,8,9,10,11],[-62,12,13,29,36,37],[-63,45,52,53],[-64,25,26,35,44],[-65,51,60],[-66,24,34,50],[-67,61],[-67,62],[-68,63],[-69,67],[-69,68],[-70,64],[-71,65],[-71,66],[-72,70],[-72,71],[-73,69],[-73,72],[73],[-14,74],[-16,74],[-18,74],[-19,74],[-21,74],[-15,75],[-17,75],[-20,75],[-22,75],[-23,75],[-39,76],[-40,76],[-42,76],[-43,76],[-28,77],[-55,77],[-56,77],[-58,77],[-59,77],[-75,78],[-74,78],[-76,-77,79],[-78,-79,80],[-80,81],[-81],[1,3,5,8,10,11,31,33,34,35,47,49,50,51],[4,6,12,14,16,18,29,30,31,36,37,38,39,40,53,55,56]],\"atoms\":[{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":49,\"b\":14},{\"tag\":\"incompatible\",\"a\":60,\"b\":29},{\"tag\":\"incompatible\",\"a\":60,\"b\":31},{\"tag\":\"incompatible\",\"a\":60,\"b\":33},{\"tag\":\"incompatible\",\"a\":60,\"b\":49},{\"tag\":\"incompatible\",\"a\":61,\"b\":53},{\"tag\":\"incompatible\",\"a\":61,\"b\":60},{\"tag\":\"incompatible\",\"a\":66,\"b\":47},{\"tag\":\"incompatible\",\"a\":68,\"b\":66},{\"tag\":\"incompatible\",\"a\":69,\"b\":32},{\"tag\":\"incompatible\",\"a\":69,\"b\":51},{\"tag\":\"incompatible\",\"a\":69,\"b\":65},{\"tag\":\"incompatible\",\"a\":69,\"b\":68},{\"tag\":\"incompatible\",\"a\":70,\"b\":41},{\"tag\":\"incompatible\",\"a\":70,\"b\":47},{\"tag\":\"incompatible\",\"a\":70,\"b\":52},{\"tag\":\"incompatible\",\"a\":79,\"b\":9},{\"tag\":\"incompatible\",\"a\":79,\"b\":48},{\"tag\":\"incompatible\",\"a\":79,\"b\":49},{\"tag\":\"incompatible\",\"a\":79,\"b\":50},{\"tag\":\"incompatible\",\"a\":79,\"b\":71},{\"tag\":\"incompatible\",\"a\":79,\"b\":78},{\"tag\":\"incompatible\",\"a\":83,\"b\":45},{\"tag\":\"incompatible\",\"a\":84,\"b\":30},{\"tag\":\"incompatible\",\"a\":86,\"b\":39},{\"tag\":\"incompatible\",\"a\":87,\"b\":32},{\"tag\":\"mate\",\"ridge\":131,\"a\":30,\"owners\":[9,45,46,48,49,50,52]},{\"tag\":\"mate\",\"ridge\":131,\"a\":32,\"owners\":[9,39,40,48,49,50,52]},{\"tag\":\"mate\",\"ridge\":133,\"a\":4,\"owners\":[14,56,59,60,61]},{\"tag\":\"mate\",\"ridge\":133,\"a\":30,\"owners\":[14,59,60,61]},{\"tag\":\"mate\",\"ridge\":133,\"a\":32,\"owners\":[14,56,60,61]},{\"tag\":\"mate\",\"ridge\":133,\"a\":33,\"owners\":[14,56,59,61]},{\"tag\":\"mate\",\"ridge\":164,\"a\":22,\"owners\":[14,60,61]},{\"tag\":\"mate\",\"ridge\":164,\"a\":78,\"owners\":[14,61]},{\"tag\":\"mate\",\"ridge\":265,\"a\":34,\"owners\":[55,56,64,65,66]},{\"tag\":\"mate\",\"ridge\":265,\"a\":63,\"owners\":[37,39,55,56,64]},{\"tag\":\"mate\",\"ridge\":273,\"a\":16,\"owners\":[43,45,47,58,59,67,68,69]},{\"tag\":\"mate\",\"ridge\":273,\"a\":34,\"owners\":[58,59,67,68,69]},{\"tag\":\"mate\",\"ridge\":273,\"a\":53,\"owners\":[43,45,47,67,68,69]},{\"tag\":\"mate\",\"ridge\":273,\"a\":62,\"owners\":[43,45,47,58,59,68,69]},{\"tag\":\"mate\",\"ridge\":289,\"a\":49,\"owners\":[55,58,64,65,67,68]},{\"tag\":\"mate\",\"ridge\":289,\"a\":61,\"owners\":[37,43,51,64,65,67,68]},{\"tag\":\"mate\",\"ridge\":385,\"a\":61,\"owners\":[39,45,52,66,69]},{\"tag\":\"mate\",\"ridge\":522,\"a\":35,\"owners\":[73,74,82,83,84]},{\"tag\":\"mate\",\"ridge\":522,\"a\":80,\"owners\":[38,40,41,73,74,83,84]},{\"tag\":\"mate\",\"ridge\":522,\"a\":81,\"owners\":[38,40,73,74,82]},{\"tag\":\"mate\",\"ridge\":530,\"a\":80,\"owners\":[44,46,47,76,77,86,87]},{\"tag\":\"mate\",\"ridge\":546,\"a\":50,\"owners\":[73,76,82,83,85,86]},{\"tag\":\"mate\",\"ridge\":776,\"a\":27,\"owners\":[41,65,66,83,84]},{\"tag\":\"mate\",\"ridge\":776,\"a\":63,\"owners\":[83,84]},{\"tag\":\"mate\",\"ridge\":776,\"a\":81,\"owners\":[65,66]},{\"tag\":\"mate\",\"ridge\":800,\"a\":70,\"owners\":[83,86]},{\"tag\":\"mate\",\"ridge\":800,\"a\":88,\"owners\":[65,68]},{\"tag\":\"mate\",\"ridge\":298,\"a\":37,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":298,\"a\":83,\"owners\":[37]},{\"tag\":\"mate\",\"ridge\":553,\"a\":38,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":553,\"a\":65,\"owners\":[38]},{\"tag\":\"mate\",\"ridge\":394,\"a\":39,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":394,\"a\":84,\"owners\":[39]},{\"tag\":\"mate\",\"ridge\":649,\"a\":40,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":649,\"a\":66,\"owners\":[40]},{\"tag\":\"mate\",\"ridge\":306,\"a\":43,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":561,\"a\":44,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":561,\"a\":68,\"owners\":[44]},{\"tag\":\"mate\",\"ridge\":402,\"a\":45,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":657,\"a\":46,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":657,\"a\":69,\"owners\":[46]},{\"tag\":\"mate\",\"ridge\":300,\"a\":55,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":396,\"a\":56,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":308,\"a\":58,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":404,\"a\":59,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":360,\"a\":64,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":368,\"a\":67,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":556,\"a\":73,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":652,\"a\":74,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":564,\"a\":76,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":660,\"a\":77,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":616,\"a\":82,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":624,\"a\":85,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[29,30,31,32,33],\"full_literals\":[-61,7,8,9,10,11]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[34,35,53,62,63],\"full_literals\":[-62,12,13,29,36,37]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[71,80,81],\"full_literals\":[-63,45,52,53]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[49,50,61,70],\"full_literals\":[-64,25,26,35,44]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[79,88],\"full_literals\":[-65,51,60]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[48,60,78],\"full_literals\":[-66,24,34,50]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-67,61,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-67,false,62],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-68,63,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-69,67,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-69,false,68],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-70,false,64],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-71,65,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-71,false,66],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-72,70,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-72,false,71],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-73,69,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-73,false,72],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":37,\"full_literals\":[-14,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":39,\"full_literals\":[-16,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":41,\"full_literals\":[-18,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":43,\"full_literals\":[-19,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":45,\"full_literals\":[-21,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":38,\"full_literals\":[-15,75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":40,\"full_literals\":[-17,75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":44,\"full_literals\":[-20,75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":46,\"full_literals\":[-22,75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":47,\"full_literals\":[-23,75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":65,\"full_literals\":[-39,76]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":66,\"full_literals\":[-40,76]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":68,\"full_literals\":[-42,76]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":69,\"full_literals\":[-43,76]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":52,\"full_literals\":[-28,77]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":83,\"full_literals\":[-55,77]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":84,\"full_literals\":[-56,77]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":86,\"full_literals\":[-58,77]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":87,\"full_literals\":[-59,77]},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-75,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-74,false,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-76,-77,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-78,-79,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-80,81],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":21,\"owners\":[4,14,22,30,32,33,56,59,60,61,74,77,78,79]},{\"tag\":\"edge\",\"edge\":28,\"owners\":[16,27,34,37,39,41,53,55,56,62,63,64,65,66,81,83,84]}]}"
  "126 69 0 98 96 0\n127 72 0 98 97 0\n128 67 0 126 89 0\n129 68 0 126 90 0\n130 70 0 127 94 0\n131 71 0 127 95 0\n132 61 0 128 86 0\n133 62 0 128 87 0\n134 63 0 129 88 0\n135 64 0 130 91 0\n136 65 0 131 92 0\n137 66 0 131 93 0\n138 -80 0 123 122 0\n139 1 3 5 8 10 11 34 35 50 51 0 69 71 75 77 124 0\n140 4 6 12 14 16 18 29 36 37 39 40 53 55 56 0 68 69 72 125 0\n141 78 0 78 75 74 73 71 70 72 69 68 118 119 104 105 106 107 108 99 100 101 102 103 46 57 61 64 67 37 39 40 36 55 59 49 35 140 0\n142 -79 0 141 138 121 0\n143 -8 76 0 134 137 135 68 70 72 73 136 75 74 109 111 53 84 20 41 18 22 85 7 83 16 14 110 51 21 82 17 112 66 60 56 24 27 45 23 0\n144 76 0 73 72 70 68 136 134 137 135 132 77 76 109 110 111 112 51 41 60 63 53 66 84 17 18 20 21 22 82 85 2 3 4 7 83 15 16 143 80 26 28 47 25 0\n145 -77 0 144 142 120 0\n146 -28 0 145 113 0\n147 -55 0 145 114 0\n148 -56 0 145 115 0\n149 -58 0 145 116 0\n150 -59 0 145 117 0\n151 -37 0 147 148 50 0\n152 -14 0 147 54 0\n153 -13 0 147 74 75 78 148 44 0\n154 -26 0 147 74 76 78 79 149 48 0\n155 -16 0 148 58 0\n156 -19 0 149 62 0\n157 -44 0 149 147 52 0\n158 -21 0 150 65 0\n159 -35 12 43 0 155 146 151 153 133 156 71 70 158 6 43 81 8 9 40 0\n160 35 -10 0 154 157 135 69 83 1 5 31 0\n161 -35 43 0 70 71 73 158 146 155 43 159 9 38 0\n162 -10 0 10 160 161 0\n163 35 11 0 154 157 135 69 71 162 83 1 5 19 29 30 33 34 139 0\n164 -35 0 73 152 72 156 161 11 12 13 42 0\n165 25 0 164 135 157 154 83 0\n166 11 0 164 163 0\n167 -3 0 165 1 0\n168 0 167 166 69 71 164 32 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record000.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record000.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record000.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record000.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record000 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record000.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record000.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record000.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record000.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record000 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record000_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record000 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record000_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record000_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00015.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00015.record004
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "ce278ab23c1f3a2e4b2aaaa6ac6a5aa99a639a9665a8e8b8ae1ba1ee8791cc571ca6a9c66394e479694e5655351d4ad0f783c8ea368d6338f13a4d9354f0ba2e2b4acab1ae1b46d8731d2729c6745c9723c2fe806c17382c4a1a168561381e68469164a5194551342d0758344c5312c1b21c4705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6d24db49b6db6d24db6db6926d249b4da6936db4924d2492249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record004 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record004 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record004.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record004.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record004.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 55), (facetIndex 57), (facetIndex 62), (facetIndex 89)]))
 (.leaf ([(facetIndex 37), (facetIndex 38), (facetIndex 72), (facetIndex 82), (facetIndex 83)])))
 (.branch 3
 (.leaf ([(facetIndex 31), (facetIndex 45), (facetIndex 46), (facetIndex 48)]))
 (.leaf ([(facetIndex 51), (facetIndex 61), (facetIndex 71)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 54), (facetIndex 87), (facetIndex 88)]))
 (.leaf ([(facetIndex 28), (facetIndex 32), (facetIndex 33), (facetIndex 39), (facetIndex 73)])))
 (.branch 7
 (.leaf ([(facetIndex 56), (facetIndex 60)]))
 (.leaf ([(facetIndex 29), (facetIndex 30), (facetIndex 35), (facetIndex 36)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "480024000002960000001e006100602090000a4fe2d5fdz15;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 34), (facetIndex 58), (facetIndex 59)]))
 (.leaf ([(facetIndex 47), (facetIndex 77), (facetIndex 78)])))
 (.branch 3
 (.leaf ([(facetIndex 63), (facetIndex 64), (facetIndex 68), (facetIndex 90), (facetIndex 92)]))
 (.branch 4
 (.leaf ([(facetIndex 40), (facetIndex 43), (facetIndex 76)]))
 (.leaf ([(facetIndex 66), (facetIndex 74), (facetIndex 91)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 44), (facetIndex 69), (facetIndex 93)]))
 (.leaf ([(facetIndex 42), (facetIndex 65), (facetIndex 70)])))
 (.branch 8
 (.leaf ([(facetIndex 41), (facetIndex 52), (facetIndex 67)]))
 (.branch 9
 (.leaf ([(facetIndex 49), (facetIndex 50), (facetIndex 53), (facetIndex 75), (facetIndex 80), (facetIndex 84), (facetIndex 85), (facetIndex 86)]))
 (.leaf ([(facetIndex 79), (facetIndex 81)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "524200088800989113840006527462200000000087088010053673z28;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [2, 3]
def grouped2_0007 : List Nat := [3]
def grouped2_0008 : List Nat := [4]
def grouped2_0009 : List Nat := [4, 5]
def grouped2_0010 : List Nat := [4, 5, 6, 7]
def grouped2_0011 : List Nat := [5]
def grouped2_0012 : List Nat := [6, 7]
def grouped3_0013 : List Nat := [0]
def grouped3_0014 : List Nat := [0, 1]
def grouped3_0015 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0017 : List Nat := [1]
def grouped3_0018 : List Nat := [2]
def grouped3_0019 : List Nat := [2, 3, 4]
def grouped3_0020 : List Nat := [3]
def grouped3_0021 : List Nat := [3, 4]
def grouped3_0022 : List Nat := [4]
def grouped3_0023 : List Nat := [5]
def grouped3_0024 : List Nat := [5, 6]
def grouped3_0025 : List Nat := [5, 6, 7, 8, 9]
def grouped3_0026 : List Nat := [6]
def grouped3_0027 : List Nat := [7]
def grouped3_0028 : List Nat := [7, 8, 9]
def grouped3_0029 : List Nat := [8]
def grouped3_0030 : List Nat := [8, 9]
def grouped3_0031 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record004 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record004_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00015.record004" "{\"atoms\":[{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0030\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00015.record004" 82

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00015.record004" "{\"ridges\":[[22,536],[23,784],[27,800],[31,273],[33,164],[38,536],[42,547],[45,273],[46,273],[47,657],[48,273],[48,784],[58,308],[64,561],[66,552],[68,368],[69,561],[70,657],[71,800],[72,536],[78,660],[82,536],[83,784],[84,610],[85,170],[87,642],[87,784],[88,672],[88,800],[90,564],[91,552],[92,624]],\"owners\":[[31,273,[63,65,68,69,70],[7,37,45,46,48,58,59]],[45,273,[58,59,63,65,69,70],[7,31,37,46,48,68]],[46,273,[58,63,65,68,69],[7,31,37,45,48,59,70]],[48,273,[58,59,63,68],[7,31,37,45,46,65,69,70]],[33,164,[91],[14,56,60,61,74,79,80,81]],[22,536,[64,65,90,92,93],[38,72,82,83]],[38,536,[90,92,93],[22,64,65,72,82,83]],[72,536,[64,65,92,93],[22,38,82,83,90]],[82,536,[64,65,90,93],[22,38,72,83,92]],[23,784,[65,69,70,93],[48,83,87]],[48,784,[93],[23,65,69,70,83,87]],[83,784,[69,70],[23,48,65,87,93]],[87,784,[65,69,93],[23,48,70,83]],[87,642,[43,52,76,81,85],[24,47,54,78,88]],[88,672,[66,91],[27,52,71,81,85]],[27,800,[53,67,69,86,93],[71,88]],[71,800,[86,93],[27,53,67,69,88]],[88,800,[67,69,93],[27,53,71,86]],[85,170,[40,74],[]],[42,547,[52,53],[]],[66,552,[75,84,86,90,92,93],[42,64,67,85,91]],[91,552,[42,64,67,84,86,92,93],[66,75,85,90]],[47,657,[70],[]],[70,657,[47],[]],[58,308,[],[]],[64,561,[69],[]],[69,561,[64],[]],[68,368,[],[]],[78,660,[],[]],[84,610,[],[]],[90,564,[],[]],[92,624,[],[]]],\"edges\":[[34,[22,23,38,47,48,64,65,69,70,72,78,82,83,87,90,92,93]],[38,[27,42,52,53,64,66,67,69,71,75,81,84,85,86,88,90,91,92,93]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00015.record004" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00015.record004\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-27,-17],[-27,-19],[-31,-20],[-31,-21],[-31,-24],[-40,-4],[-40,-6],[-40,-9],[-40,-35],[-48,-31],[-52,-20],[-52,-21],[-52,-24],[-52,-48],[-5,25,27,30,31,32],[-13,22,23,25,27,31,32],[-14,22,25,27,30,31],[-16,22,23,25,30],[-7,50],[-1,26,27,49,51,52],[-8,49,51,52],[-34,26,27,51,52],[-41,26,27,49,52],[-2,27,31,32,52],[-16,52],[-42,31,32],[-46,27,31,52],[-46,12,17,38,40,44],[-47,28,50],[-3,18,29,31,45,52],[-33,45,52],[-47,29,31,52],[-44,10,36],[-11,17,18],[-28,37,43,45,49,51,52],[-50,11,26,29,43,45,51,52],[-15,32],[-32,15],[-22],[-26,31],[-31,26],[-30],[-39],[-43],[-49],[-51],[-53,20,21,24,48],[-54,5,13,14,16],[-55,19,46,47],[-56,4,6,7,9,35],[-57,53],[-58,54],[-59,57],[-59,58],[-60,55],[-60,56],[-61,60],[-62,59],[-62,61],[62],[-23,63],[-15,64],[-25,65],[-26,65],[-10,66],[-12,66],[-38,66],[-28,67],[-36,67],[-50,67],[-31,68],[-52,68],[-27,69],[-32,69],[-17,70],[-29,70],[-18,71],[-37,71],[-44,71],[-45,71],[-40,72],[-64,73],[-63,73],[-67,74],[-66,74],[-74,75],[-65,75],[-75,76],[-73,76],[-69,77],[-68,-69,78],[-72,79],[-71,79],[-79,80],[-70,80],[-77,-80,81],[-78,81],[-76,-81,82],[-82],[1,2,8,15,16,26,27,31,32,34,39,41,42,46,49,51,52],[3,11,17,18,26,28,29,31,33,37,40,43,44,45,47,49,50,51,52]],\"atoms\":[{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":65,\"b\":52},{\"tag\":\"incompatible\",\"a\":65,\"b\":54},{\"tag\":\"incompatible\",\"a\":69,\"b\":55},{\"tag\":\"incompatible\",\"a\":69,\"b\":57},{\"tag\":\"incompatible\",\"a\":69,\"b\":62},{\"tag\":\"incompatible\",\"a\":81,\"b\":28},{\"tag\":\"incompatible\",\"a\":81,\"b\":32},{\"tag\":\"incompatible\",\"a\":81,\"b\":39},{\"tag\":\"incompatible\",\"a\":81,\"b\":73},{\"tag\":\"incompatible\",\"a\":89,\"b\":69},{\"tag\":\"incompatible\",\"a\":93,\"b\":55},{\"tag\":\"incompatible\",\"a\":93,\"b\":57},{\"tag\":\"incompatible\",\"a\":93,\"b\":62},{\"tag\":\"incompatible\",\"a\":93,\"b\":89},{\"tag\":\"mate\",\"ridge\":273,\"a\":31,\"owners\":[63,65,68,69,70]},{\"tag\":\"mate\",\"ridge\":273,\"a\":45,\"owners\":[58,59,63,65,69,70]},{\"tag\":\"mate\",\"ridge\":273,\"a\":46,\"owners\":[58,63,65,68,69]},{\"tag\":\"mate\",\"ridge\":273,\"a\":48,\"owners\":[58,59,63,68]},{\"tag\":\"mate\",\"ridge\":164,\"a\":33,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":536,\"a\":22,\"owners\":[64,65,90,92,93]},{\"tag\":\"mate\",\"ridge\":536,\"a\":38,\"owners\":[90,92,93]},{\"tag\":\"mate\",\"ridge\":536,\"a\":72,\"owners\":[64,65,92,93]},{\"tag\":\"mate\",\"ridge\":536,\"a\":82,\"owners\":[64,65,90,93]},{\"tag\":\"mate\",\"ridge\":784,\"a\":23,\"owners\":[65,69,70,93]},{\"tag\":\"mate\",\"ridge\":784,\"a\":48,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":784,\"a\":83,\"owners\":[69,70]},{\"tag\":\"mate\",\"ridge\":784,\"a\":87,\"owners\":[65,69,93]},{\"tag\":\"mate\",\"ridge\":642,\"a\":87,\"owners\":[43,52,76,81,85]},{\"tag\":\"mate\",\"ridge\":672,\"a\":88,\"owners\":[66,91]},{\"tag\":\"mate\",\"ridge\":800,\"a\":27,\"owners\":[53,67,69,86,93]},{\"tag\":\"mate\",\"ridge\":800,\"a\":71,\"owners\":[86,93]},{\"tag\":\"mate\",\"ridge\":800,\"a\":88,\"owners\":[67,69,93]},{\"tag\":\"mate\",\"ridge\":170,\"a\":85,\"owners\":[40,74]},{\"tag\":\"mate\",\"ridge\":547,\"a\":42,\"owners\":[52,53]},{\"tag\":\"mate\",\"ridge\":552,\"a\":66,\"owners\":[75,84,86,90,92,93]},{\"tag\":\"mate\",\"ridge\":552,\"a\":91,\"owners\":[42,64,67,84,86,92,93]},{\"tag\":\"mate\",\"ridge\":657,\"a\":47,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":657,\"a\":70,\"owners\":[47]},{\"tag\":\"mate\",\"ridge\":308,\"a\":58,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":561,\"a\":64,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":561,\"a\":69,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":368,\"a\":68,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":660,\"a\":78,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":610,\"a\":84,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":564,\"a\":90,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":624,\"a\":92,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[55,57,62,89],\"full_literals\":[-53,20,21,24,48]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[31,45,46,48],\"full_literals\":[-54,5,13,14,16]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[54,87,88],\"full_literals\":[-55,19,46,47]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[28,32,33,39,73],\"full_literals\":[-56,4,6,7,9,35]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-57,53,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-58,54,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-59,57,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-59,false,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-60,55,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-60,false,56],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-61,60,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-62,59,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-62,false,61],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":59,\"full_literals\":[-23,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":47,\"full_literals\":[-15,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":63,\"full_literals\":[-25,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":64,\"full_literals\":[-26,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":40,\"full_literals\":[-10,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":43,\"full_literals\":[-12,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":76,\"full_literals\":[-38,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":66,\"full_literals\":[-28,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":74,\"full_literals\":[-36,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":91,\"full_literals\":[-50,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":69,\"full_literals\":[-31,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":93,\"full_literals\":[-52,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":65,\"full_literals\":[-27,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":70,\"full_literals\":[-32,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":52,\"full_literals\":[-17,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":67,\"full_literals\":[-29,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":53,\"full_literals\":[-18,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":75,\"full_literals\":[-37,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":85,\"full_literals\":[-44,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":86,\"full_literals\":[-45,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":81,\"full_literals\":[-40,72]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-64,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-63,false,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-67,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-66,false,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-74,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-65,false,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-75,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-73,false,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-69,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-68,-69,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0029\",\"right_name\":\"grouped3_0031\",\"joined_name\":\"grouped3_0030\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-72,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0029\",\"right_name\":\"grouped3_0031\",\"joined_name\":\"grouped3_0030\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-71,false,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0028\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-79,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-70,false,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-77,-80,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0025\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-78,false,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-76,-81,82],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":34,\"owners\":[22,23,38,47,48,64,65,69,70,72,78,82,83,87,90,92,93]},{\"tag\":\"edge\",\"edge\":38,\"owners\":[27,42,52,53,64,66,67,69,71,75,81,84,85,86,88,90,91,92,93]}]}"
  "102 59 0 60 58 0\n103 61 0 60 59 0\n104 57 0 102 53 0\n105 58 0 102 54 0\n106 60 0 103 57 0\n107 53 0 104 51 0\n108 54 0 105 52 0\n109 55 0 106 55 0\n110 56 0 106 56 0\n111 1 2 8 15 16 26 27 31 32 34 41 42 46 52 0 43 45 46 100 0\n112 3 11 17 18 26 28 29 31 33 37 40 44 45 47 50 52 0 44 45 46 101 0\n113 27 76 0 42 39 108 89 82 62 38 88 87 64 41 83 61 63 18 15 17 16 48 0\n114 76 0 109 110 88 86 84 85 68 69 70 65 66 67 33 19 29 113 1 2 49 28 6 7 8 9 50 0\n115 -81 0 114 99 98 0\n116 -78 0 115 97 0\n117 -69 0 116 115 45 46 44 90 91 96 71 72 94 95 40 92 93 75 76 81 77 78 79 80 32 30 34 35 31 36 112 0\n118 -27 0 117 73 0\n119 -32 0 117 74 0\n120 -15 0 119 37 0\n121 52 31 0 46 45 119 118 120 26 40 25 21 20 22 23 24 27 111 0\n122 -52 0 107 11 12 13 14 47 0\n123 31 0 122 121 0\n124 -20 0 123 3 0\n125 -21 0 123 4 0\n126 -24 0 123 5 0\n127 -48 0 123 10 0\n128 0 126 127 107 124 125 47 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record004.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record004.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record004.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record004.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record004 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record004.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record004.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record004.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record004.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record004 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record004_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record004 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record004_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00015.record004_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00015.record004
