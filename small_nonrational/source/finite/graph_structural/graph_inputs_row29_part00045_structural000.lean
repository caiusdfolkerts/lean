module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00045Data
public import GraphInputsRow29Part00045Frames
public import GraphInputsRow29Part00045Leaves
public import GraphInputsRow29Part00045Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record018
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record018
def vertexColumn : Fields := ⟨10, hexnat% "ec3a8e63345d32c5b31c57332aca723cb2aaaa6a3ab1aa6a5a36b26c5a364d8b61db0e8b92e2b86e8791e2785ee8791cc6b16c5713c789ca6a96a5693a719a6599564d9595554d4b51d54d4b4ad1b51d2745dc8ea338f13a4cd38cd332cc73c2e8b32e2b4acab1ae1b46c9b16d2729d1725c3743c8f0bc1fa8a92a28661584e49465454554344d28c6324c5322c4b11c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6db4db4db4db6db4db69b69b6db6db6db6db49349349a69349b49a4da4da492492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨82, by decide⟩, ⟨86, by decide⟩, ⟨91, by decide⟩, ⟨99, by decide⟩, ⟨103, by decide⟩, ⟨107, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "84400000000000000000000", hexnat% "888000000000004810000000000", 14740281580383633408, 2467972597174763520, 638303007145984, 8869795332096, 79691776]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record018_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record018_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record018_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record018_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record018_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record018_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record018_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record018_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record018_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record018

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record020
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record020
def vertexColumn : Fields := ⟨10, hexnat% "3b0ab26cc725ce8b92ccab26c9723cb2aaa96ac695aa98e6c5a9635b0ea3a2e2b86e8791e17ba1e4731ac5b15c4f1ca6a95a719566a539715a54d5c368d8b4ad1b61d4745d68d6338d9354cd34ccb31cd4b2ad1b16cc729c6745d0f23c2f07f28a512a1a8961584e4a469254551352328c6344c9314d0b12c2b21c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6db6da69b6da4db69b4db6db4d36db49b6d3692492492492492491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨49, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨71, by decide⟩, ⟨74, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨86, by decide⟩, ⟨88, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40808020407ffffe000000", hexnat% "4000002000000000000", 9259400833873739776, hexnat% "10100000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1400000a00017f762000000", 34829500416, hexnat% "800000400000000000", 43982612594688, hexnat% "4000002000000000000", hexnat% "1800000c0000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1800000c03bebc4000000", 4415796805632, 69122129920, 633318697598976, hexnat% "1400000a000000000000000", hexnat% "4800000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8000007ff736000000", hexnat% "40000020000c0000000", hexnat% "1800000c0000000000000", hexnat% "1400000a000000000000000", 34493956096]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "48000027f4fce000000", 550561120256, 206158430208, 9259400833873739776, hexnat% "14000002000000000000000", hexnat% "180000040000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40000020003ffffe000000", hexnat% "4000002000000000000", hexnat% "10000008000000000000000", hexnat% "800000400000000000", hexnat% "1800000c0000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800000403ffffe000000", hexnat% "800000400000000000", hexnat% "100000080000000000000", hexnat% "4000002000000000000", hexnat% "1400000a000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [70367636881408, 633319771340800, hexnat% "1800000c0000000000000", hexnat% "1400000a000000000000000", hexnat% "4800000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40040020023efede000000", hexnat% "10000008000000000000000", hexnat% "800000400100000000", hexnat% "1800000c0000000000000", 1100048498688]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800000400ffffe000000", hexnat% "800000400000000000", hexnat% "100000080000000000000", 52776558133248, hexnat% "4000002000000000000", hexnat% "1400000a000000000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1808000c24b17f2000000", hexnat% "1400000a000000000000000", 309371863040, 40269613367296, hexnat% "4000000000004000000", 17592186044416]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1800000c00b1490000000", hexnat% "1400000a000000000000000", hexnat% "4000002000244000000", hexnat% "800000400102000000", 275548995584, 40269613367296, 17626545782784]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c15 c12
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c16 c11
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c17 c10
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c18 c5
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c19 c4
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c20 c3
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c21 c2
  c22
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record020_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record020_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record020_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record020_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record020_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record020_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record020_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record020_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record020_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record020

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record024
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record024
def vertexColumn : Fields := ⟨10, hexnat% "ec3a8cd2b49d32cab3a2e4b8acaaaa6a96a3a99a568dac9aa699b16a5a56c3a8e8b92e2b86e4789e17ba1e4731ac5b15c4f16a5693a599564d9c96a5c56958d5352d4754b4ad4749d17783c8ea368d6338f13a4d9354cd362d4b32d2b2ac6b46c9b16f07a1e2749ca719e1745c9743c8f0bc1f1b312a4a161584e4a4a91a4651544d0b51324c5342c8b12c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6d36db6db6da49b6da6d36db6d24db6db6da49b4db6da4924924924db6d2492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨55, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨81, by decide⟩, ⟨84, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨105, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1188950302162681856, hexnat% "1200000000000000000000", hexnat% "2001c0000000000000010000000", hexnat% "3800c0001c000800000", 545357968703488, 15633735483392]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record024_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record024_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record024_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record024_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record024_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record024_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record024_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record024_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00045.record024_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00045.record024
