module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00179Data
public import GraphInputsRow29Part00179Frames
public import GraphInputsRow29Part00179Leaves
public import GraphInputsRow29Part00179Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00179.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00179.record006
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨93, by decide⟩, ⟨96, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨110, by decide⟩, ⟨117, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), 55450570411999232, (certNat% 4), (certNat% 5), 4035788216077385728]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), (certNat% 3), 55450572559482880, (certNat% 7), 8647474234504773632, (certNat% 8)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 9), (certNat% 3), (certNat% 10), (certNat% 11), (certNat% 12), (certNat% 8)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), (certNat% 3), (certNat% 14), (certNat% 10), (certNat% 15), (certNat% 8)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), (certNat% 17), (certNat% 18), (certNat% 19), 121221156962304]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), (certNat% 21), (certNat% 22), 118764435668992, 55450570411999232, 8647474234504773632]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 23), (certNat% 24), (certNat% 22), 118764435668992, (certNat% 10), (certNat% 15)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), (certNat% 26), (certNat% 27), 48378511622144, 8646911284551352320]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 28), (certNat% 3), 37436171902517248, (certNat% 29), 1729945206863691776]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 30), (certNat% 31), 79164837199872, (certNat% 32), 8648600134411616256]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 33), (certNat% 34), (certNat% 22), 83580063580160, 4649122190329905152, 4035788216077385728]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c11 c8
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c12 c7
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 35), 101163659689984, (certNat% 36), (certNat% 18), (certNat% 37)]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 38), (certNat% 39), (certNat% 40), 43980465111040]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 41), (certNat% 40), (certNat% 42), (certNat% 43), (certNat% 44)]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 45), (certNat% 46), (certNat% 47), (certNat% 48), (certNat% 49), 50581829844992]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c19 c14
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 50), (certNat% 51), (certNat% 22), 8648318659434905600, 118764435668992, 54043195528445952]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 52), 101172249624576, (certNat% 53), (certNat% 54)]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 55), (certNat% 46), (certNat% 18), (certNat% 56), 15414637625344, (certNat% 57)]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c23 c22
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 58), (certNat% 59), (certNat% 60), (certNat% 61)]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 62), (certNat% 63), (certNat% 26), 13194139533312, (certNat% 64)]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c26 c25
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 65), (certNat% 66), (certNat% 67), 1152930300699869184, 5189554145614364672]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 68), (certNat% 67), 6342475650221211648, (certNat% 64), (certNat% 69), 50852412784640]
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c29 c28
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c30 c27
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 70), (certNat% 71), (certNat% 3), (certNat% 72), 6342475650221211648, 54043195528445952]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 73), (certNat% 74), 6342475650221211648, (certNat% 22), 118764435668992, 54043195528445952]
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 75), (certNat% 76), (certNat% 77), (certNat% 53), (certNat% 54)]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 78), (certNat% 76), (certNat% 79), (certNat% 53), (certNat% 54)]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 80), (certNat% 3), (certNat% 81), (certNat% 82), (certNat% 18), (certNat% 83)]
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c36 c35
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c37 c34
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 84), (certNat% 18), (certNat% 46), (certNat% 85), 4419521347584, (certNat% 86)]
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 87), (certNat% 88), (certNat% 89), 9070970929152, (certNat% 90), (certNat% 91)]
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 92), (certNat% 18), (certNat% 46), (certNat% 93), (certNat% 94), (certNat% 95)]
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 96), 4647996290423062528, (certNat% 97), (certNat% 59), (certNat% 98)]
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 99), (certNat% 100), (certNat% 101), (certNat% 15), (certNat% 98)]
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 102), 4648840715353194496, (certNat% 29), (certNat% 103), (certNat% 98), (certNat% 12)]
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 104), (certNat% 95), 13194139533312, (certNat% 12), (certNat% 18), (certNat% 91)]
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 105), 4649122198919839744, (certNat% 22), 83580063580160, (certNat% 106), (certNat% 107), (certNat% 83)]
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c46 c45
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c47 c44
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c48 c43
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c49 c42
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c50 c41
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c51 c40
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c52 c39
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c53 c38
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c54 c33
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c55 c32
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c56 c31
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c57 c24
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c58 c21
  let c60 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c59 c20
  let c61 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c60 c13
  let c62 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c61 c6
  let c63 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c62 c5
  let c64 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨85, by decide⟩ c63 c4
  let c65 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c64 c3
  let c66 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c65 c2
  let c67 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c66 c1
  let c68 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c67 c0
  c68
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00179.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00179.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00179.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00179.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00179.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00179.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00179.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00179.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00179.record006_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00179.record006
