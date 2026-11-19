module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow26Part00003Data
public import GraphInputsRow26Part00003Frames
public import GraphInputsRow26Part00003Leaves
public import GraphInputsRow26Part00003Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00003.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record006
def vertexColumn : Fields := ⟨10, hexnat% "dc2e8e63a4e5334e32acc729c67362d4b329c9729ab1a969a64d876638ae1b91e17ae19c6c9aa6693a699965a5655351d4ad1b49d175a34cc732ac6b61d2729c6745c570dc8f13c2fe82586905a49916078592948d0746314c4b06c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6da6db6db6db6d24db6936db6d26da69369a692492489249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨30, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨72, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000100010000000000", 144680345642467328, 85900656640, 37154696936292352, 1363673088, 100663296]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record006_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00003.record006

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00003.record015
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record015
def vertexColumn : Fields := ⟨10, hexnat% "d53349d2ccab26c1f352cca72b2aaa9a87ae1b46b1b26a9a66c5996959568d9361da8e63a4e33a2e2b86e1783e1e785d16c5c96a599595555351d58d334ad1b45d0f783d0ec3c8ea398d9354d331cd8b32cab1ac5b0ef07a1d8791d4731e2749ca719d1725c570dd0f23c4f0bc1fe138261515154352344d0b58344c530cc8b12c2b"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6db6db6d36db6db6db6db6db69b6da49249249b6da4924924da6db6da693493249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨24, by decide⟩, ⟨32, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨66, by decide⟩, ⟨89, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200000401e401e1016e0000", 1152939096792891392, 15496242003968, 1015561715972046848]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200000000f411f1016e0000", hexnat% "41100000000000000", 2251834173423616, 15393162788864, 1008806316530991104]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20000000e141f11016e0000", hexnat% "41100000000000000", 2251834173423616, 962072674304, 63050394783186944]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20000000e0c1f09016e0000", hexnat% "41100000000000000", 4503668346847232, 962072674304, 63050394783186944]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200000000ec11e9016e0000", hexnat% "41100000000000000", 4503668346847232, 15393162788864, 1008806316530991104]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200000400040001006e0000", 2061584302080, 135107988821114880, 32985365610496, 2161727821137838080, 6755502520270848]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨17, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨21, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨18, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨19, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record015_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record015_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record015_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record015_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record015_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record015_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record015_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record015_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record015_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00003.record015

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00003.record047
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record047
def vertexColumn : Fields := ⟨10, hexnat% "7cd8ad2e2b2a9aa9a66a5a1eac6698d61da8e63a4e4b86e2785e0fb61b4789ca669a659996479b15a535475a358d9352d1b49d1743de0f43b0f2368e6358e9364e5334c73c2e8b62e4b8ad2b1ae1b46c9b16c3ba1d8791cc749ca719c9715c3783d0f23c4f0bc1fe0b0a4a866258560b81ee07094a465254550b41d"⟩
def kindColumn : Fields := ⟨3, hexnat% "db49b6db6936d24936936db6d26da4924db6db6db4db69b6db6db6d24db6d2249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨16, by decide⟩, ⟨17, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨38, by decide⟩, ⟨43, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2102011880084003830000", hexnat% "400200000000000000000000", hexnat% "20700000000000000", hexnat% "800084000000000000000000", hexnat% "4060000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8060c4030680084003830000", 1801439850948198400, hexnat% "400002000000000000000000", hexnat% "320000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8060e4000480084003830000", hexnat% "30300000000000000", hexnat% "400002000000000000000000", hexnat% "300000000000000000000", 1729382256910270464]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "23e0001b00000002820000", hexnat% "30400000000000000", hexnat% "4000000000000001010000", hexnat% "400002000000084000000000", hexnat% "800004000080000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "61e0030780084003830000", 1729382256910270464, hexnat% "800004000000000000000000", hexnat% "400200000000000000000000", hexnat% "2000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8041c4020680084003830000", 1801439850948198400, hexnat% "400002000000000000000000", hexnat% "220000000000000000000", hexnat% "2000010000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1c0031f00000003830000", hexnat% "6020000000000000000000", hexnat% "400200000000004000000000", hexnat% "800004000080080000000000", hexnat% "2000000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "61e0000800000003810000", hexnat% "800004000080080000000000", hexnat% "30700000000000000", hexnat% "2001000004000000000", hexnat% "400200000000000000000000", 131072]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨16, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c10 c3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c11 c2
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c12 c1
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c13 c0
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record047_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record047_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record047_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record047_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record047_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record047_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record047_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record047_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00003.record047_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00003.record047
