module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00079Data
public import GraphInputsRow29Part00079Frames
public import GraphInputsRow29Part00079Leaves
public import GraphInputsRow29Part00079Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00079.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record002
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨61, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨80, by decide⟩, ⟨87, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨103, by decide⟩, ⟨104, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), 4512395720392704, 8246337208320, 4222124650659840]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), (certNat% 3), (certNat% 6), 4512395720392704, 8246337208320, 4222124650659840]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), (certNat% 3), (certNat% 8), (certNat% 9), (certNat% 10)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), (certNat% 12), (certNat% 13), 14293651161088, (certNat% 14), 103079215104]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), (certNat% 3), (certNat% 16), (certNat% 17), (certNat% 18), (certNat% 19)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), (certNat% 3), (certNat% 16), (certNat% 21), (certNat% 22), (certNat% 19)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 23), (certNat% 24), (certNat% 25), 281474976710656]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 26), (certNat% 3), 4512395720392704, (certNat% 27), 8246337208320, 3096224743817216]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 28), (certNat% 29), (certNat% 30), 7599824371187712, (certNat% 31)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 32), (certNat% 33), (certNat% 34), (certNat% 35), 281474976710656]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 36), (certNat% 37), (certNat% 34), (certNat% 35), 281474976710656]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 38), (certNat% 25), (certNat% 39), (certNat% 40), (certNat% 41)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c13 c10
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 42), (certNat% 43), (certNat% 12), 14293651161088, (certNat% 44), 103079215104]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 45), (certNat% 46), (certNat% 12), 7318349394477056, (certNat% 44), 52776558133248]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 47), 6150393167872, 2937895069417472, (certNat% 48), (certNat% 35), (certNat% 10)]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 49), (certNat% 16), (certNat% 50), (certNat% 51), (certNat% 52), (certNat% 53)]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 54), (certNat% 55), (certNat% 46), 7318349394477056, (certNat% 56), 52776558133248]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 57), (certNat% 58), (certNat% 35), (certNat% 56), (certNat% 53), (certNat% 8)]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 59), (certNat% 60), (certNat% 52), (certNat% 8), (certNat% 56), (certNat% 61), (certNat% 53)]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c21 c20
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c22 c19
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨97, by decide⟩ c23 c18
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨89, by decide⟩ c24 c17
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c25 c16
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c26 c15
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c27 c14
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c28 c9
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c29 c8
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c30 c5
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c31 c4
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c32 c3
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c33 c2
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c34 c1
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c35 c0
  c36
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00079.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00079.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record003
def vertexColumn : Fields := ⟨10, (certNat% 62)⟩
def kindColumn : Fields := ⟨3, (certNat% 63)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨80, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨100, by decide⟩, ⟨108, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 64), (certNat% 65), (certNat% 66), 90071992547409920, 11529215046068469760]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 67), (certNat% 68), (certNat% 69), (certNat% 70), 1143916504375361536, (certNat% 71), (certNat% 72)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c1 c0
  c2
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00079.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00079.record005
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record005
def vertexColumn : Fields := ⟨10, (certNat% 73)⟩
def kindColumn : Fields := ⟨3, (certNat% 74)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨91, by decide⟩, ⟨96, by decide⟩, ⟨98, by decide⟩, ⟨107, by decide⟩, ⟨111, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 75), (certNat% 76), (certNat% 77), (certNat% 78)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 79), (certNat% 80), (certNat% 81), (certNat% 82)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 83), (certNat% 84), (certNat% 76), (certNat% 85), (certNat% 86), (certNat% 87)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 88), (certNat% 89), 144115200960757760, (certNat% 78)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 90), (certNat% 91), 1080863944928657408, (certNat% 92), (certNat% 93), (certNat% 94)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 95), (certNat% 96), (certNat% 97), (certNat% 98)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 99), (certNat% 100), (certNat% 101), (certNat% 102), (certNat% 103), (certNat% 87)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 104), (certNat% 105), (certNat% 106), (certNat% 107), (certNat% 108), (certNat% 109)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 110), (certNat% 111), (certNat% 112), (certNat% 113), (certNat% 114)]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 115), (certNat% 116), (certNat% 117), (certNat% 103), 1116892707587883008]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 118), 1116892707587883008, (certNat% 117), (certNat% 108), (certNat% 116)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 119), 1116892707587883008, (certNat% 120), (certNat% 116), (certNat% 106), (certNat% 121)]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 122), (certNat% 121), (certNat% 123), (certNat% 120), (certNat% 106)]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 124), (certNat% 116), (certNat% 92), (certNat% 125), (certNat% 126), 1116892707587883008]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 127), (certNat% 128), (certNat% 116), (certNat% 129), (certNat% 130)]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 131), 11538222245323210752, (certNat% 132), (certNat% 133), (certNat% 134)]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 135), (certNat% 116), (certNat% 102), (certNat% 121), (certNat% 136), 1116892707587883008]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 137), 1116892707587883008, (certNat% 92), 11529218207164399616, (certNat% 116), (certNat% 78), (certNat% 138)]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c20 c19
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c21 c18
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c22 c17
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c23 c16
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c24 c15
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c25 c14
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c26 c13
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c27 c12
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c28 c11
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c29 c10
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c30 c9
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c31 c8
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c32 c7
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c33 c4
  c34
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record005_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00079.record005_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00079.record005
