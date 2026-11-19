module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00091Data
public import GraphInputsRow24Part00091Frames
public import GraphInputsRow24Part00091Leaves
public import GraphInputsRow24Part00091Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00091.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record001
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨31, by decide⟩, ⟨36, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨49, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨68, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨83, by decide⟩, ⟨85, by decide⟩, ⟨89, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨97, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), 9223372036854775808, (certNat% 4), (certNat% 5), (certNat% 6)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), (certNat% 8), (certNat% 9), (certNat% 10), (certNat% 5), (certNat% 11)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), (certNat% 10), (certNat% 13), 9889904781739163648, (certNat% 14), (certNat% 15)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), 6597069766656, (certNat% 17), 571746046443520, (certNat% 18)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), 666532744850833408, (certNat% 20), (certNat% 21), (certNat% 18), (certNat% 22)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 23), (certNat% 24), (certNat% 25), 562950221856768]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 26), 9223372037123211264, (certNat% 27), (certNat% 28), (certNat% 25)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), 5066549580791808, 9295429630892703744, (certNat% 30)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 31), 5066549580791808, 108086391056891904, 9223372037123211264, (certNat% 25)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 32), 9223372037123211264, (certNat% 25), (certNat% 33), 108086391056891904]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 34), 9295429630892703744, (certNat% 30), (certNat% 35), (certNat% 36)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 37), (certNat% 25), 13743962456064, (certNat% 38), (certNat% 39), 4503599627370496]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c15 c12
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨97, by decide⟩ c16 c11
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨89, by decide⟩ c17 c8
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 40), 9889904781705609216, (certNat% 14), (certNat% 5), (certNat% 41), (certNat% 42), (certNat% 43)]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨93, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c20 c5
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c21 c2
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c22 c1
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c23 c0
  c24
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record001_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00091.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00091.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record006
def vertexColumn : Fields := ⟨10, (certNat% 44)⟩
def kindColumn : Fields := ⟨3, (certNat% 45)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨78, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 46), (certNat% 47), 59813982306828288, (certNat% 48), (certNat% 49), 2305847441619943424, 20230369705984]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record006_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00091.record006

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00091.record014
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record014
def vertexColumn : Fields := ⟨10, (certNat% 50)⟩
def kindColumn : Fields := ⟨3, (certNat% 51)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 52), 9587741394206720, (certNat% 53), (certNat% 54), (certNat% 55), (certNat% 56)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 57), (certNat% 58), 3377702941753344, (certNat% 59), 562984313159680, (certNat% 56)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 60), 46179488366592, (certNat% 61), (certNat% 62)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 63), (certNat% 25), 27487790694400, (certNat% 64), 37383395344384]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 65), (certNat% 66), (certNat% 67), (certNat% 68), (certNat% 69)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 70), (certNat% 71), 43980532219904, (certNat% 72), 9025895247380480]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 73), 9025895247380480, (certNat% 74), (certNat% 75), (certNat% 76), (certNat% 77)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c9 c2
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 78), (certNat% 79), 34628173824, (certNat% 80), 43980465111040]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 81), (certNat% 82), (certNat% 83), 46179488366592, (certNat% 84)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 85), (certNat% 79), (certNat% 86), 580576499204096, 43980465111040]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 87), (certNat% 64), (certNat% 80), 46179488366592, (certNat% 88)]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 89), 3377702404882432, (certNat% 64), 27522150432768, (certNat% 25), 37383395344384]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c16 c13
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c17 c12
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c18 c11
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 90), 43980532219904, (certNat% 91), (certNat% 92)]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 93), 2214592512, 8796093022208, (certNat% 94)]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c22 c21
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 95), (certNat% 96), (certNat% 97), 44255343017984, 2251801961168896]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c24 c23
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c25 c20
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 98), (certNat% 99), (certNat% 100)]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨97, by decide⟩ c22 c27
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 101), (certNat% 99), (certNat% 91), (certNat% 102)]
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c29 c28
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c31 c22
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [(certNat% 103)]
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c31 c33
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 104), (certNat% 99)]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c35 c34
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c31 c22
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 105), (certNat% 106), (certNat% 99)]
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c38 c37
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c39 c36
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 107), (certNat% 99), (certNat% 100), (certNat% 108)]
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c41 c40
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c42 c32
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 109), (certNat% 100), 44255343017984, (certNat% 110)]
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 111), (certNat% 97), (certNat% 112), 44255343017984, (certNat% 92)]
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c45 c44
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c46 c43
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c47 c30
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 113), 9070970929152, (certNat% 96), (certNat% 92)]
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 114), (certNat% 115), 26422638804992, (certNat% 116), (certNat% 117)]
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c50 c49
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 118), 1125900175278080, (certNat% 97), 44255343017984, (certNat% 119)]
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c31 c22
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c31 c53
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 120), (certNat% 121), (certNat% 119), (certNat% 108)]
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c55 c54
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 122), 17592454479872, (certNat% 64), (certNat% 123), (certNat% 124)]
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c57 c56
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 125), (certNat% 116), (certNat% 97), (certNat% 123), (certNat% 126), 1125900175278080]
  let c60 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c59 c58
  let c61 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c60 c52
  let c62 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c61 c51
  let c63 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c62 c48
  let c64 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c63 c26
  let c65 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 127), (certNat% 9), (certNat% 128), 580576499204096, (certNat% 129)]
  let c66 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 130), (certNat% 74), 26422638804992, (certNat% 131), (certNat% 132), (certNat% 133)]
  let c67 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c66 c65
  let c68 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 134), (certNat% 135), (certNat% 97), (certNat% 75), (certNat% 136)]
  let c69 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 137), (certNat% 138), (certNat% 75), (certNat% 97), (certNat% 139)]
  let c70 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 140), (certNat% 141), (certNat% 142), (certNat% 143)]
  let c71 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 144), 17626545782784, (certNat% 145), (certNat% 146), (certNat% 96)]
  let c72 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 147), (certNat% 138), 37383395344384, (certNat% 64), (certNat% 110)]
  let c73 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 148), (certNat% 75), (certNat% 149), (certNat% 56), (certNat% 97), (certNat% 106)]
  let c74 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c73 c72
  let c75 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c74 c71
  let c76 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c75 c70
  let c77 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c76 c69
  let c78 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c77 c68
  let c79 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 150), 3377701868011520, (certNat% 141), (certNat% 82), (certNat% 9)]
  let c80 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 151), 17626545782784, (certNat% 74), 35186519572480, (certNat% 152)]
  let c81 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 153), 3377701868011520, (certNat% 149), (certNat% 61), (certNat% 62), 35459249995776]
  let c82 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c81 c80
  let c83 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c82 c79
  let c84 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 154), (certNat% 135), (certNat% 155), (certNat% 74), (certNat% 80), (certNat% 156)]
  let c85 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 157), 43980532219904, (certNat% 82), 3377701868011520, (certNat% 9)]
  let c86 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 158), (certNat% 159), (certNat% 83), (certNat% 160), (certNat% 82)]
  let c87 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 161), (certNat% 79), 3377701868011520, (certNat% 9), 35184372088832]
  let c88 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 162), (certNat% 25), 26422638804992, 1970324836974592, (certNat% 61), 2286986333257728]
  let c89 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c88 c87
  let c90 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c89 c86
  let c91 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c90 c85
  let c92 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 163), (certNat% 74), 1153484454828703744, (certNat% 152), 35186519572480, 26422638804992]
  let c93 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 164), (certNat% 165), (certNat% 166), 562984313159680, (certNat% 121)]
  let c94 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 167), (certNat% 166), (certNat% 69), (certNat% 168), 2305843009213693952]
  let c95 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 169), (certNat% 160), (certNat% 165), 2287259063681024, (certNat% 170), (certNat% 88)]
  let c96 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c95 c94
  let c97 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c96 c93
  let c98 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 171), (certNat% 135), (certNat% 74), 17626814218240, (certNat% 123), (certNat% 86)]
  let c99 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 172), (certNat% 173), (certNat% 174), 9070970929152, (certNat% 132), 580576767639552]
  let c100 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 175), (certNat% 97), (certNat% 176), 1125902322761728, (certNat% 131), 35459249995776]
  let c101 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 177), (certNat% 176), 580576767639552, (certNat% 54), (certNat% 178), 46454366273536, 3377701868011520]
  let c102 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c101 c100
  let c103 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c102 c99
  let c104 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c103 c98
  let c105 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c104 c97
  let c106 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c105 c92
  let c107 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c106 c91
  let c108 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c107 c84
  let c109 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c108 c83
  let c110 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c109 c78
  let c111 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c110 c67
  let c112 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c111 c64
  let c113 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c112 c19
  let c114 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c113 c10
  let c115 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c114 c1
  let c116 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c115 c0
  c116
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record014_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record014_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record014_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record014_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record014_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record014_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record014_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record014_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00091.record014_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00091.record014
