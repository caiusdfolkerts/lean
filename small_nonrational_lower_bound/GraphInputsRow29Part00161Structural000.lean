module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00161Data
public import GraphInputsRow29Part00161Frames
public import GraphInputsRow29Part00161Leaves
public import GraphInputsRow29Part00161Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00161.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record001
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩, ⟨102, by decide⟩, ⟨103, by decide⟩, ⟨104, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 17317308137472000, (certNat% 3), (certNat% 4), (certNat% 5), (certNat% 6)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), (certNat% 8), 17592186044416000, (certNat% 9), (certNat% 10), (certNat% 6)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), (certNat% 12), 17451448556060672, (certNat% 13), (certNat% 5), (certNat% 10)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), (certNat% 15), 15199648742375424, 7007601020188491776, (certNat% 16), (certNat% 10)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), (certNat% 18), 14636698788954112, (certNat% 19)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), (certNat% 21), (certNat% 22), (certNat% 23), 15199648742375424, (certNat% 10)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨89, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), (certNat% 12), 15340386230730752, (certNat% 25), (certNat% 26), (certNat% 27), (certNat% 5)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c0 c10
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 28), (certNat% 29), 16191408230629376, (certNat% 30), (certNat% 4), (certNat% 5), (certNat% 6)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 31), (certNat% 8), (certNat% 32), 17029236090994688, (certNat% 33), (certNat% 6)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 34), (certNat% 12), (certNat% 35), 17451448556060672, (certNat% 36), (certNat% 10)]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 37), (certNat% 38), 17592186044416000, (certNat% 39), (certNat% 40), (certNat% 10), (certNat% 5)]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 41), (certNat% 8), (certNat% 29), 17029236090994688, (certNat% 33), (certNat% 40)]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [(certNat% 42)]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c17 c16
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c18 c15
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨91, by decide⟩ c19 c14
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨93, by decide⟩ c20 c13
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨94, by decide⟩ c21 c12
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c22 c11
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨102, by decide⟩ c23 c3
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨103, by decide⟩ c24 c2
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨104, by decide⟩ c25 c1
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c26 c0
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c27 c0
  c28
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record001_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00161.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00161.record004
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record004
def vertexColumn : Fields := ⟨10, (certNat% 43)⟩
def kindColumn : Fields := ⟨3, (certNat% 44)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩, ⟨102, by decide⟩, ⟨103, by decide⟩, ⟨104, by decide⟩, ⟨105, by decide⟩, ⟨106, by decide⟩, ⟨107, by decide⟩, ⟨108, by decide⟩, ⟨109, by decide⟩, ⟨110, by decide⟩, ⟨111, by decide⟩, ⟨112, by decide⟩, ⟨113, by decide⟩, ⟨114, by decide⟩, ⟨115, by decide⟩, ⟨116, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 45), 8926134461448323072, (certNat% 46), (certNat% 47), (certNat% 48)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 49), 9196350439090552832, (certNat% 48), (certNat% 50), (certNat% 46)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 51), 8708132091985920, 8917127262193582080, (certNat% 48), (certNat% 47)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 52), 8910442231496704, 9124292845052624896, (certNat% 46), (certNat% 50)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 53), (certNat% 54), 3993426232082432, 4089268461652410368, (certNat% 47)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 55), 144255925564211200, 1249045209153536, 1279022294173220864, (certNat% 47), (certNat% 48)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 56), (certNat% 57), (certNat% 58), 4186940278571008, 4287426845256712192, (certNat% 48)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 59), 4616189618054758400, (certNat% 58), (certNat% 60), (certNat% 61), 1864771720708096, 1909526242005090304]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 62), 4616189618054758400, (certNat% 63), (certNat% 61), (certNat% 60), 2990671627550720, 3062447746611937280]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 64), 6808175999188992, 6971572223169527808, (certNat% 54)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 65), (certNat% 66), (certNat% 67), 5770237022568448]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 68), (certNat% 48), (certNat% 69), 6953557824660045824]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 70), (certNat% 71), (certNat% 66), (certNat% 72), 4755801206503243776]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 73), (certNat% 74), (certNat% 66), (certNat% 75), 4644337115725824]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 76), (certNat% 77), 4616189618054758400, (certNat% 78), (certNat% 79), (certNat% 80), 17592186044416]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c19 c16
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c20 c15
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c21 c14
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c22 c13
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c9 c23
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 51), 8708132091985920, 8917127262193582080, (certNat% 47), (certNat% 48)]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 81), 4616189618054758400, (certNat% 63), (certNat% 58), (certNat% 61), 3975834046038016, 4071254063142928384]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 82), (certNat% 83), 8901646138474496, 9115285645797883904, (certNat% 50)]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 84), 4616189618054758400, (certNat% 58), (certNat% 63), (certNat% 60), 4081387162304512, 4179340454199820288]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 52), 8910442231496704, 9124292845052624896, (certNat% 50), (certNat% 46)]
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 85), (certNat% 86), 8637763347808256, 8845069668155654144, (certNat% 47)]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [(certNat% 87)]
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨92, by decide⟩ c31 c30
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨93, by decide⟩ c32 c29
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨94, by decide⟩ c33 c28
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c34 c27
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨97, by decide⟩ c35 c26
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨98, by decide⟩ c36 c25
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨99, by decide⟩ c37 c24
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨101, by decide⟩ c38 c12
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨102, by decide⟩ c39 c11
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨104, by decide⟩ c40 c10
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨113, by decide⟩ c41 c3
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨114, by decide⟩ c42 c2
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨115, by decide⟩ c43 c1
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨116, by decide⟩ c44 c0
  c45
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record004_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00161.record004_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00161.record004
