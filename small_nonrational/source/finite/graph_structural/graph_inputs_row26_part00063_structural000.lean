module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow26Part00063Data
public import GraphInputsRow26Part00063Frames
public import GraphInputsRow26Part00063Leaves
public import GraphInputsRow26Part00063Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00063.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record003
def vertexColumn : Fields := ⟨10, hexnat% "7c1e8ce2785e3346d32c6b31c8f13c789d26c9723c9ca6a96a3a95a4e87a658d6638ce8791e179b19c4f16a6693a6598e5391e6a569595356354d4b5634cd8b52d2b61d4745d0f5a338d9334d332cc7362ccb4acab1ae1b46c5b0ed8731e1745c9715e0f43c8f13c1f61916438e18c4718a4698560d30c5312c8705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6db6db6db6db6db4d369b49a4d34db69b6d369b6d34da69b4da692492492249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨31, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨46, by decide⟩, ⟨49, by decide⟩, ⟨54, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨70, by decide⟩, ⟨73, by decide⟩, ⟨75, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [635990638592, hexnat% "a400000000004000000", hexnat% "48800020080000000", 2324490726420774912, hexnat% "90000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [569418645504, hexnat% "a400000000004000000", hexnat% "48800021000000000", 2324490726420774912, hexnat% "90000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2324490726423003136, 22347776, hexnat% "d8800000000000000", 100663296, hexnat% "a400000000000880000", 2837094334464]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨17, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨21, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00063.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00063.record017
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record017
def vertexColumn : Fields := ⟨10, hexnat% "3389e178ad2743d1ac9b1b25c8f26a96a5693a1e9a6398d62d8766392e2b86ecc6b16c6715c4f1ca5a99a569c6659566394e479a95a5994e5a5655356352d4756364d8b52d2b46d54cd362d4b86d1b16d8731e1725c5783d0f23db08b06c6484e6460d1358344c9314d0b12c8711c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6d26db6db6db6da6d36db6db6db6db6db6da4da4926924d2491249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨61, by decide⟩, ⟨64, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100002000001031be0000", 3321888768, hexnat% "200000000000900000000", hexnat% "10000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100002000000000020000", hexnat% "200010000001100000000", 34360262656, 1085276160, 621019136, 2449473536]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨17, by decide⟩ c1 c0
  c2
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record017_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record017_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record017_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record017_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record017_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record017_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record017_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record017_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record017_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00063.record017

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00063.record022
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record022
def vertexColumn : Fields := ⟨10, hexnat% "ce1b89e1786d2749b1b25c9aa5a9a6658d64d8b61d8ce8b8ae1bb319c571ca6695a719a659996559366394e4799969565655356354d475a364d3362d1b56364d5334d331cd4b32e2b4ac6b61cc789d2719d1725c570de0f23c4f0be341d18a4a86a19991626152545560d0b22c4b21c47"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6da6da4db6d36d36db6da6db6da49269b6db4db6934926d349b499249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨18, by decide⟩, ⟨19, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨25, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨39, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨60, by decide⟩, ⟨69, by decide⟩, ⟨73, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨84, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200101e008030c80000", hexnat% "1000000001400000000000", hexnat% "180000000000480000000", 9663938560, hexnat% "200000000002000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1802000014006c2840000", hexnat% "1002000000000000000000", 805830656, 1155173854176346112, 6192449491828736]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1002000017408052c40000", 1155173304957403136, hexnat% "200000000000080000", hexnat% "180000000000480000000", 8589934592]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1800000020006f0cc0000", 1155173854176346112, hexnat% "2200000000002000000", 5981343255101440, hexnat% "1000000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1155173864389476352, hexnat% "180000000000480000000", hexnat% "1002000000400000000000", 269221888, 6473924464345088, hexnat% "200000000002000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c7 c0
  c8
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record022_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record022_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record022_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record022_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record022_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record022_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record022_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record022_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00063.record022_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00063.record022
