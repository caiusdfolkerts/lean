module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow26Part00062Data
public import GraphInputsRow26Part00062Frames
public import GraphInputsRow26Part00062Leaves
public import GraphInputsRow26Part00062Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00062.record012
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record012
def vertexColumn : Fields := ⟨10, hexnat% "31c789d26a96ac6a9a6695a69966c599695956c3a2e4ba1e479d13c699665592e47965655554b51d62d8751d0f5c338e9364e5354cd3a2d8b52e2b1ae1b46c9b16d8791d4789ca785d1725c5783d0f0bc1f66154628aa518662a619264658545528c6382c8b0ae0711c27"⟩
def kindColumn : Fields := ⟨3, hexnat% "36d36d369b69b6db6934da4d34db4db6d269269b4924da4d3249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨47, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨70, by decide⟩, ⟨74, by decide⟩, ⟨77, by decide⟩, ⟨81, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2040049208374f9a00000", 2251799813685248, 2341871806232657920, hexnat% "20400000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000048008374b0a00000", 74309393985830912, hexnat% "20002000000000000000", hexnat% "4400000000041000000", 45035996273704960]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40001208260f9a00000", 4613937886960549888, hexnat% "400080000000000000", hexnat% "220000000010400000000", 2882303761517117440]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2244020000314c9000000", 5188146770730811392, 117093590311632896, 2251799824171008, 141150610522112]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2244000800314c9000000", 81064793292668928, 7493989779944505344, 2251799824171008, 141150610522112]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "224400000020080000000", 141150612619264, 117093590328410112, 7493989797124374528, 2251868675768320, 1100585369600]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c9 c2
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record012_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record012_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record012_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record012_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record012_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record012_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record012_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record012_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record012_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00062.record012

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00062.record017
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record017
def vertexColumn : Fields := ⟨10, hexnat% "1d86e1b472a568d8b61da4e53a2e1b9d16c5c96a719a659996559366394e4b91e5a5c5595956354d4b51d70d9354d8b52d1b5c3a4e5334e332cc73a2d8b92d4b32e2b1ad8791d4789ca719e1725c570de0f43c4f0bd542a991544b1625492a545855151543528e0b22c4b0ae0711c27"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6db6da49369a6da6d24924da6db6db4d24924d2492692691249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨52, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨64, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6412e900bfbb7600000", 1224979099718516736, hexnat% "10100000000000000000", hexnat% "8000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "102e900943b7000000", 1224979099718516736, hexnat% "a410000000000000000", 2989303529472, hexnat% "14000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4580169634145107968, 2989316112384, hexnat% "14500000000000000000", hexnat% "a010000000000000000", 1374389534720]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "410001003fbb5600000", hexnat% "a410000000000000000", hexnat% "10003200000000000000", 72066391238246400, 900719925474099200]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "102f900843f6200000", hexnat% "18401000000000000000", hexnat% "2010000010000000000", 2989318209536, hexnat% "4000000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1c513f90087af6200000", hexnat% "2000000030000000000", 549776785408, 4294967296]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1a411100085af6200000", 3350678122763649024, hexnat% "100010000100000000", 2886238994432, hexnat% "4000000010000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8010100084056000000", hexnat% "14100010000000000000", 4503599627370496000, 15573450752, hexnat% "2400000010000000000", 2989316112384]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c11 c4
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c12 c3
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c13 c2
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record017_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record017_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record017_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record017_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record017_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record017_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record017_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record017_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record017_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00062.record017

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00062.record019
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record019
def vertexColumn : Fields := ⟨10, hexnat% "1b89723c2f07c749b2c6a5a56a3a4e87a71a96958d68d8b61da4e53a2e1ba1e1783e745b16a71966659566394e4b91e5c56364d5362d2b46d70da3c4e9364e5354cd38cd332cc73c2e4b52e2b4ac6b86d1b16c3ba1d8791d4731e2719e0f43c4f0bd58649522c8a6524a58344d0b58350ca381c8711c27"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6d26d36db6da6db6db6db6d36db6924926d34db4db4db6db492492691249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨17, by decide⟩, ⟨18, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨35, by decide⟩, ⟨39, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨61, by decide⟩, ⟨76, by decide⟩, ⟨85, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10010000001008000000000", 25895697857511424, hexnat% "2000002000080800000000", hexnat% "20000000002200000000000", 9007199338627072, 183762944]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record019_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record019_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record019_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record019_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record019_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record019_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record019_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record019_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record019_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00062.record019

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00062.record020
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record020
def vertexColumn : Fields := ⟨10, hexnat% "1d26c9aac6a5a56a3a4e87a71a96958d68d8b61d98e9394e8b8ae1b9d16c5a9c6659566394e47971695954d58d4b51d58d9354d8b4ad1b5c368f13a4d9394d5334e334ccb31cf0b62e4b52e2b4acab1ae1b46c5b0ee8761e4751cc789ca719e1725c570de0f43c8f13c2f649522c94a29a0e1382e645512c5492960d1342d"⟩
def kindColumn : Fields := ⟨3, hexnat% "24db4db6db69b4924936d36db6da6d24936da69b69b6d36db6db6db69b6da6d2249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f7ff07dffc1ffffffffff0000", hexnat% "800002000000000000000000", 3314649325744685056, hexnat% "400001000000000000000", hexnat% "b80000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "77fff9dffffffffffffff0000", hexnat% "8000020000000000000000000", hexnat% "800002000000000000000000", hexnat% "10000040000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f7fffbdffe5fbfdffffff0000", hexnat% "42000004000000000000", 1873497444986126336, hexnat% "800000000000020000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f7fff9dffe1fbfdffffff0000", 1008806316530991104, hexnat% "60000000000000000000", hexnat% "10800000000004000000000000", hexnat% "2001000020000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨99, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f7fffbdffcdfbfdffffff0000", hexnat% "42000004000000000000", 3602879701896396800, hexnat% "800000000000020000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f7fff9dffc9fbfdffffff0000", 2738188573441261568, hexnat% "60000000000000000000", hexnat% "10800000000004000000000000", hexnat% "2001000020000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨99, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [hexnat% "1fbffff2bfffffffffffff0000", hexnat% "d400000000000000000", hexnat% "400000000000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1fffffddffefffffffffff0000", hexnat% "20000000000000000000", hexnat% "2001000000000000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1ffffadffefbffffffffff0000", hexnat% "20010000000000000000", hexnat% "100000400000000000000", hexnat% "400000000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f7ffb9dffefffffffffff0000", hexnat% "60000000000000000000", hexnat% "400001000000000000000", hexnat% "800002000000000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [hexnat% "1bffefffffffffffffffff0000", hexnat% "4001000000000000000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "17fffe9ffffbffffffffff0000", hexnat% "100000400000000000000", hexnat% "60000000000000000000", hexnat% "8000000000000000000000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c17 c16
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "17fffb9dfeefffffffffff0000", hexnat% "400001000000000000000", hexnat% "8000020000000000000000000", hexnat% "10000000000000000", hexnat% "42000000000000000000"]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c20 c15
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨100, by decide⟩ c21 c14
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "77fbf9dffeffbbdffffff0000", hexnat% "8004000000000400000000000", hexnat% "60000000000000000000", hexnat% "2001000020000000000", hexnat% "10800000000004000000000000"]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f7ffb3dffc5ffffffffff0000", hexnat% "480000000000000000000", 4179340454199820288, hexnat% "42000000000000000000", hexnat% "10800000000000000000000000"]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "77fbf9dfeffffffffffff0000", hexnat% "4000010000000000000000", hexnat% "42000000000000000000", hexnat% "8000020000000000000000000", hexnat% "10800000000000000000000000"]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7ffff9dfed5fbbfffffff0000", 3026418949592973312, hexnat% "42000004000000000000", hexnat% "20010000400000000000", hexnat% "18000000000000000000000000"]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "77fbf9dfec5fbbdfffffd0000", hexnat% "20010000400000000000", 4179340454199951360, hexnat% "10000040000004000000000000", hexnat% "8004000000000000000000000", hexnat% "800002000000020000000000"]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c27 c26
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨16, by decide⟩ c28 c25
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c29 c24
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c30 c23
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨20, by decide⟩ c31 c22
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c32 c9
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c33 c5
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c34 c0
  c35
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record020_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record020_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record020_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record020_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record020_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record020_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record020_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record020_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00062.record020_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00062.record020
