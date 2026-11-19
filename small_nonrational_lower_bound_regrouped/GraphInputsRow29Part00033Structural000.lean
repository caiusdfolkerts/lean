module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00033Data
public import GraphInputsRow29Part00033Frames
public import GraphInputsRow29Part00033Leaves
public import GraphInputsRow29Part00033Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00033.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record001
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨39, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨47, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨68, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨85, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 1152921509455462400, (certNat% 3), 1241513984, (certNat% 4), 18014398509481984]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), (certNat% 6), (certNat% 7), 10596969923202777088, (certNat% 8), 4611686018427387904]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 9), (certNat% 10), (certNat% 11), 140739103162368, 10596969923202777088]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), (certNat% 13), (certNat% 14), 9439544820579172352, 1170935903116328960]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), (certNat% 4), (certNat% 7), (certNat% 16), 150083337191424, (certNat% 17)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), (certNat% 4), (certNat% 7), 150117696929792, (certNat% 8), (certNat% 17)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), (certNat% 16), 149533581377536, (certNat% 19), (certNat% 4), (certNat% 7)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), 13835058055282163712, (certNat% 21), 1175439502743699456, (certNat% 22)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 23), 10376293546293460992, (certNat% 24), (certNat% 14), (certNat% 25), 140738562097152]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 26), (certNat% 27), 9223372036854775808, (certNat% 21), (certNat% 28), (certNat% 7)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), 13202729467904, 13835058055282163712, (certNat% 28), (certNat% 25), (certNat% 7)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 30), 8798240505856, 22517998141046784, 13835058056355905536, 1152921509438685184, (certNat% 21), (certNat% 22)]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c12 c9
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c13 c8
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c14 c7
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c15 c6
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c16 c5
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c17 c4
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c18 c3
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c19 c2
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c20 c1
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c21 c0
  c22
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record001_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00033.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00033.record009
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record009
def vertexColumn : Fields := ⟨10, (certNat% 31)⟩
def kindColumn : Fields := ⟨3, (certNat% 32)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨32, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨42, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨65, by decide⟩, ⟨71, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨87, by decide⟩, ⟨93, by decide⟩, ⟨95, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 33), (certNat% 34), 72128031501582336, (certNat% 35)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 36), (certNat% 34), (certNat% 37), 35356170780672]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 38), (certNat% 34), (certNat% 37), (certNat% 35), 105656195481600]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 39), (certNat% 40), 144256063003164672, (certNat% 41), 105656195481600, (certNat% 42)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 43), (certNat% 44), (certNat% 45), (certNat% 46)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 47), 171798691840, 216172782113783808, (certNat% 40)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 48), (certNat% 49), (certNat% 46), (certNat% 40), 137438953472]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 50), (certNat% 51), (certNat% 52), 140913582014464, (certNat% 53), (certNat% 54)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 55), (certNat% 56), 70471823392768, (certNat% 57)]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 58), 2305843043573432320, (certNat% 57), (certNat% 59), 70437463654400]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 60), 2882303761517117440, (certNat% 61), (certNat% 59)]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 62), 103079215104, 216172782113783808, (certNat% 35)]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 63), 2305843043573432320, (certNat% 35), (certNat% 59), 68719476736]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c20 c17
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 64), (certNat% 61), 2882303761584226304, (certNat% 65), (certNat% 66)]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 67), (certNat% 68), 103079215104, (certNat% 35), 72057594037927936]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 69), (certNat% 59), 73183562664247296, (certNat% 35)]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 70), 103616086016, (certNat% 46), (certNat% 71), (certNat% 57), (certNat% 72)]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c25 c24
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c26 c23
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c27 c22
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c28 c21
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c29 c16
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 73), (certNat% 74), (certNat% 68), (certNat% 46), (certNat% 75)]
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 76), (certNat% 77), 176059299397632, (certNat% 37)]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 78), (certNat% 79), (certNat% 46), (certNat% 37), 140874927308800]
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c33 c32
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 80), (certNat% 37), (certNat% 81), (certNat% 51), (certNat% 75)]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 82), 864691128455135232, 176059299397632, (certNat% 83), (certNat% 40)]
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 84), (certNat% 81), (certNat% 85), (certNat% 51), 140874927308800, (certNat% 86)]
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c37 c36
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c38 c35
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c39 c34
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c40 c31
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 87), (certNat% 56), 105621835743232, (certNat% 57)]
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 88), 2305878193585782784, (certNat% 57), (certNat% 59), 70437463654400]
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c43 c42
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 89), 35253091565568, 216172782113783808, (certNat% 35)]
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 90), 2305878193585782784, (certNat% 35), (certNat% 59), 68719476736]
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c46 c45
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c47 c17
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 91), 2305878193652891648, (certNat% 46), (certNat% 92), 72128031501582336, (certNat% 93)]
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c49 c48
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c50 c44
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 94), (certNat% 92), (certNat% 85), (certNat% 93), 256705178760118272, (certNat% 95)]
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 96), (certNat% 57), (certNat% 83), 140909287047168, (certNat% 40)]
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 97), 70471823392768, (certNat% 35), (certNat% 98), (certNat% 40), 144256063003164672]
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c54 c53
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 99), (certNat% 92), (certNat% 100), (certNat% 85), 256705178760118272, (certNat% 95)]
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 101), 140874927308800, (certNat% 37), 1196337370497024, (certNat% 35)]
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 102), 2882303761584226304, (certNat% 37), 1196337370497024, (certNat% 35), (certNat% 103)]
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c58 c57
  let c60 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨98, by decide⟩ c59 c57
  let c61 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 104), (certNat% 105), 72128031501582336, (certNat% 57), 162270461512646656, (certNat% 40)]
  let c62 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 106), 144256063003164672, (certNat% 40), (certNat% 107), 72128031501582336, (certNat% 35)]
  let c63 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 108), 73253931408424960, 162270461512646656, (certNat% 35), (certNat% 109), (certNat% 40)]
  let c64 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 110), (certNat% 46), 73253931408424960, 162270461512646656, (certNat% 35), (certNat% 40), (certNat% 109)]
  let c65 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c64 c63
  let c66 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c65 c62
  let c67 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c66 c61
  let c68 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c67 c60
  let c69 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c68 c56
  let c70 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c69 c55
  let c71 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c70 c52
  let c72 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c71 c51
  let c73 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c72 c41
  let c74 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c73 c30
  let c75 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c74 c13
  let c76 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c75 c6
  c76
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record009_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record009_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record009_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record009_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record009_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record009_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record009_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record009_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00033.record009_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00033.record009
