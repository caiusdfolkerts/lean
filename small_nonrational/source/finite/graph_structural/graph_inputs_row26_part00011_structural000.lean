module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow26Part00011Data
public import GraphInputsRow26Part00011Frames
public import GraphInputsRow26Part00011Leaves
public import GraphInputsRow26Part00011Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00011.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record002
def vertexColumn : Fields := ⟨10, hexnat% "ec368ae364cd174d332c9b16ca723ce49b25c96a3aa9a2eb16a5956c3a8e53a1e27ab15c6a93a6998e4b959695556354d475a362d1b61d2743d58ce354d332cc7332cab1ac9b0ed4745c9715c8f07f30ac2a8c51464584e2c4a91a44d24c8b12c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "4d34db6db6db6da69b4da69369b6db6d36db6d3492692491249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [hexnat% "fffd7ffffffffffe0000", hexnat% "28000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ffffff7dffdffffe0000", 36028797018963968, 563087392374784]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f7ffeb7dffdfffbe0000", 563087392374784, 324259173174870016, hexnat% "8001000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨21, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [hexnat% "fffdfff7fffcfffe0000", hexnat% "20000000300000000", 2251799813685248]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c1 c7
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c1 c8
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c1 c10
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c1 c11
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c1 c12
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c1 c13
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c14 c9
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨21, by decide⟩ c1 c10
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c1 c16
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c1 c17
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "f7ffffffffdfdffe0000", 536870912, hexnat% "8000000002000000000"]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "77fffbffffdfff9e0000", hexnat% "8000000002000000000", hexnat% "80000000000000000000", 288230376158003200]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c21 c20
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c22 c15
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "77ffeb7dffdfff9e0000", 563087392374784, 324259173174870016, hexnat% "88000000000000000000", 1152921504608944128]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c24 c23
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c25 c6
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "77ffeb6bffffff960000", 5629499534213120, hexnat% "88000000000000000000", 324259173175394304, 1152921504608944128]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c1 c7
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c1 c28
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7fffffffffffddfe0000", hexnat% "80000000000000000000", 570425344]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c30 c29
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "77fffb7fffdffffe0000", 324259173170675712, hexnat% "88000000000000000000", 137438953472]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c32 c31
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "77ffefedffdfd9fe0000", hexnat% "80000010000000000000", hexnat% "8001000000000000000", 637534208, 563087392374784]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c34 c33
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ffffeb7fffdfd5860000", 137606725632, 537919488, 324259173175394304, 1152921504608944128]
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "57ffeb6dbfdfd1be0000", 324259173174870016, hexnat% "8001000000000000000", hexnat% "a0000010000000000000", 563087560146944, 70369348157440]
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c37 c36
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨17, by decide⟩ c38 c35
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c39 c27
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨18, by decide⟩ c40 c26
  c41
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record002_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00011.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00011.record024
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record024
def vertexColumn : Fields := ⟨10, hexnat% "398d6394ad38cd4ab2d2b1aa6a5a56aa6c5a968d8b6c3a8e538ae1bb915c4f1e24e9c6699665593678559715a55954d4b5c368d6354d2b46dc4e9354cb3c2e8b52cab1ae1b46c9b16f07a1d4729c6785d1725c3783d0f23c4f0bf0ca3072839512c471524a54348d18c530cc4b09c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36da6db6db6db49b6d26db69b6db6924936d26d34db4db49b692491249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨31, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨58, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨84, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20402c220841c0000", hexnat% "1000c00001000000200000", 35218731958272, hexnat% "10004010000400000", 134217728]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20400420080000000", hexnat% "10004010000400000", hexnat% "1000c00003000000200000", 201457664, 171798953984, 175921862017024]
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
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record024_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record024_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record024_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record024_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record024_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record024_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record024_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record024_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record024_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00011.record024
