module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00227Data
public import GraphInputsRow29Part00227Frames
public import GraphInputsRow29Part00227Leaves
public import GraphInputsRow29Part00227Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00227.record016
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record016
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨34, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨103, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), 1946157056, 2053641430089334784, (certNat% 4), 824684052480]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), (certNat% 6), (certNat% 7), 2199107141632, (certNat% 8)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 9), (certNat% 10), (certNat% 11)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), (certNat% 13), (certNat% 11), 72057594054705152, (certNat% 8)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), (certNat% 15), (certNat% 16), (certNat% 17), (certNat% 18), 67108864]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), (certNat% 20), (certNat% 21), (certNat% 22), (certNat% 23), 13194810621952]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), (certNat% 15), 1140850688]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), (certNat% 26), (certNat% 27), 35185714266112, 1152921504673955840]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 28), (certNat% 27), (certNat% 29)]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 30), (certNat% 31), (certNat% 29), 1152921504673955840, (certNat% 32)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 33), (certNat% 34), (certNat% 35), 1149239296, 1188950301625810944, (certNat% 36)]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c15 c10
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c16 c9
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 37), (certNat% 34), 2199123918848, (certNat% 17), (certNat% 38), 48379048493056]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 39), (certNat% 40), (certNat% 41), 1188950301701308416, (certNat% 4), 824667275264]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 42), 155759673344, (certNat% 43), (certNat% 44)]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 45), 1152921521853825024, (certNat% 21), (certNat% 46), 1476395008, (certNat% 47)]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c21 c20
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 48), 1711276032, (certNat% 34), (certNat% 49), (certNat% 50), 13194139533312]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 51), (certNat% 52), (certNat% 21), 3023698919424, (certNat% 53), 2080374784, (certNat% 54)]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c24 c23
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c25 c22
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c26 c19
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c27 c18
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨91, by decide⟩ c28 c17
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c29 c8
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c30 c7
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨103, by decide⟩ c31 c0
  c32
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record016_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record016_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record016_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record016_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record016_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record016_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record016_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record016_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00227.record016_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00227.record016
