module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow26Part00007Data
public import GraphInputsRow26Part00007Frames
public import GraphInputsRow26Part00007Leaves
public import GraphInputsRow26Part00007Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00007.record009
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record009
def vertexColumn : Fields := ⟨10, hexnat% "3c8d32cccb29cf0b8acaa9a4e8bad1ac6c9966a58d6c3a8e8b92e8789e0fbc1e2749b25c94e4b9d16c5594d5c368d9354d3352d27783d0ec370d6334d332cf0ba2d8b4acab46c9b0ef07a1e4751cc749c6725c5783d0f23c2f07c3cd0ac2918364a4990e4350b41d50cc348c930cc4709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6d36db49b6db6db4db6d26db6db6934924936d36936924926da449249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨19, by decide⟩, ⟨20, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨37, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨67, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨85, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20c0000002f80077000000", hexnat% "80000002600180000", 6597203984384, 3459890413727383552]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20c0000000f80075000000", hexnat% "80000002600180000", 6597103321088, 1125900041060352, 3459327463773962240]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80000202610180000", hexnat% "20c0000000c00040000000", 10995166609408, 21990433882112, 3459327463773962240, 1125900443713536]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record009_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record009_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record009_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record009_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record009_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record009_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record009_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record009_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record009_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00007.record009

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00007.record024
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record024
def vertexColumn : Fields := ⟨10, hexnat% "ea34ccb2aca725c2f3a2b4b8acaaaa6aa9a2eb46c9aa659a96958b6c3a8e8b92e2ba1e2783ee27496a5592e745594b5c368d9354d4b4ad2745d0f783d0ec368d6354cd32cf0ba2d8b4acab46c9b0ef07a1e4751d2729c6725c3783d0f23c2f07f42918564a4a9264550b41d50d2328c9314c4709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6db6db69b6d36db6db6d34db6db4924d34924db49a6da49249b691249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨17, by decide⟩, ⟨18, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨73, by decide⟩, ⟨78, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4200080189801fc60000", 41781441855488, 562954248388608, 2309220760473829376]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2310219121432068096, 576461302059237376, 3298543271936, hexnat% "40000000200018000000", hexnat% "2000000000001000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "420000002e081fc60000", 1653562408960, 985162418487296, 2885681478417514496]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "420000080c8c1f440000", 37383395344384, 2883570398912315392, 1103815114752, 844424930131968]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2886667229334994944, 13194173087744, hexnat% "42000000000018000000", 3298543271936, 35184372088832]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2124857890701312, 2884555561330802688, 1103806595072, hexnat% "42000000000018000000", 37383395344384]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2886394550484729856, 281474985230336, hexnat% "42000000000018000000", 3298534883328, 39582418599936]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [577445949211803648, hexnat% "42000000000018000000", 13194139533312, 1653562408960, 37383395344384, 2309220726114353152]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c10 c3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c11 c2
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c12 c1
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c13 c0
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record024_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record024_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record024_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record024_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record024_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record024_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record024_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record024_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00007.record024_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00007.record024
