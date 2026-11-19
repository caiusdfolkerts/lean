module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00153Data
public import GraphInputsRow29Part00153Frames
public import GraphInputsRow29Part00153Leaves
public import GraphInputsRow29Part00153Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00153.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00153.record006
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨28, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨52, by decide⟩, ⟨56, by decide⟩, ⟨59, by decide⟩, ⟨64, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨81, by decide⟩, ⟨84, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨92, by decide⟩, ⟨100, by decide⟩, ⟨103, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), (certNat% 5), (certNat% 6)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), (certNat% 3), (certNat% 4), (certNat% 8), (certNat% 9)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), (certNat% 11), (certNat% 12), 141287781040128, (certNat% 13)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), (certNat% 13), (certNat% 15), (certNat% 16), (certNat% 17)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), (certNat% 3), (certNat% 15), (certNat% 19), (certNat% 20), (certNat% 21)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c7 c0
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), (certNat% 23), (certNat% 24), (certNat% 25), (certNat% 26)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 27), (certNat% 28), (certNat% 23), (certNat% 29)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 30), (certNat% 23), (certNat% 24), (certNat% 31), 576460753108729856]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 32), (certNat% 28), (certNat% 25), (certNat% 23), (certNat% 33)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 34), (certNat% 24), (certNat% 35), (certNat% 19), (certNat% 36), (certNat% 37)]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨89, by decide⟩ c15 c12
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c16 c9
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 38), (certNat% 39), (certNat% 40), (certNat% 41), 281614831583232, (certNat% 42)]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 43), (certNat% 23), (certNat% 28), (certNat% 25), (certNat% 44)]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 45), (certNat% 46), 422212733501440, (certNat% 28)]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 47), (certNat% 23), (certNat% 48), (certNat% 49)]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 50), (certNat% 23), (certNat% 24), (certNat% 46), (certNat% 29)]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c22 c21
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 51), (certNat% 52), (certNat% 11), (certNat% 28)]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 53), (certNat% 11), (certNat% 39), (certNat% 28), (certNat% 54)]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨100, by decide⟩ c25 c24
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 55), (certNat% 46), (certNat% 24), (certNat% 39), (certNat% 56), 576460753108729856]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c27 c26
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c28 c23
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c29 c20
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c30 c19
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 57), (certNat% 39), 687194767360, (certNat% 58), (certNat% 13)]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 59), (certNat% 25), (certNat% 12), 141287781040128, (certNat% 13)]
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 60), (certNat% 39), (certNat% 61), (certNat% 13), (certNat% 62)]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 63), (certNat% 54), (certNat% 15), (certNat% 64), (certNat% 62)]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 65), (certNat% 12), 962072674304, (certNat% 66), (certNat% 29)]
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 67), (certNat% 39), (certNat% 3), 281612684099584, (certNat% 40), (certNat% 68)]
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c37 c36
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c38 c35
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c39 c34
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c40 c33
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c41 c32
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 69), (certNat% 15), 140874927308800, (certNat% 70), (certNat% 37)]
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 71), (certNat% 46), (certNat% 72), (certNat% 73), 141425219993600, 274877906944]
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c44 c43
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 74), (certNat% 46), 141287781040128, (certNat% 72), (certNat% 73), 72057594037927936]
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 75), (certNat% 39), (certNat% 40), (certNat% 41), 422350172454912, 562949953421312]
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 76), (certNat% 77), 979252543488, (certNat% 66), (certNat% 78)]
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 79), (certNat% 80), 424411488321536, (certNat% 17), (certNat% 81)]
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 82), (certNat% 83), (certNat% 78), (certNat% 81), (certNat% 84), (certNat% 85), 140875732615168]
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c50 c49
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c51 c48
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c52 c47
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c53 c46
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c54 c45
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c55 c42
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨92, by decide⟩ c56 c31
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c57 c18
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c58 c17
  let c60 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c59 c8
  c60
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00153.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00153.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00153.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00153.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00153.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00153.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00153.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00153.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00153.record006_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00153.record006
