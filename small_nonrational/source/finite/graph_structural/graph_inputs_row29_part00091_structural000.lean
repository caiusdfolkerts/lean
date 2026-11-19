module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00091Data
public import GraphInputsRow29Part00091Frames
public import GraphInputsRow29Part00091Leaves
public import GraphInputsRow29Part00091Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00091.record007
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record007
def vertexColumn : Fields := ⟨10, hexnat% "3383d0dc8f13c1f332ac9b2caa6a5ab1a8e93a8d9362d8ce8b92e1ba1e4789e0fb31ac5b13c4d9394d58d5352d4753361d4749d17723a8da398d6338f13a4d938cd332ce4b52ccb86d1b26e2749ca719e1745c970de0f43c8f07f30c60e42d32238b0a318a61984ec470986519314951341dc0cc382d0b12c8711c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "936da6d369b6d26d36da6db49b4d24926db49b6da4926da4da692449249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨72, by decide⟩, ⟨77, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨86, by decide⟩, ⟨89, by decide⟩, ⟨92, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "41242200018041b0168000000", hexnat% "2000000040200000000000000", hexnat% "100002400040010000000", hexnat% "1088108001800000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000c3e00070918000000", hexnat% "4020020000000000000000000", 26389889679360, hexnat% "2000200008000001000000000", hexnat% "1000108000000000000", hexnat% "104000000004000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4020020002000030000000000", 2161727821272055808, 30788204625920, hexnat% "20000000c8000001000000000", hexnat% "100000008000800000000", hexnat% "104200000004000100000000", hexnat% "1000100000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c3 c0
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c4 c0
  c5
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record007_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record007_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00091.record007

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00091.record008
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record008
def vertexColumn : Fields := ⟨10, hexnat% "2b8cd32c9b23cccab26c8f2caaaa9a8eaa6a3a2e8d6c3a4e33a1e27b316c4f1ca6392e72559715356354d475c34cd8b52d1b61d2743dc8da358ce3c4d9334e334ccb31cf0b8ad2b2ac6b86c9b0ef0751cc785c9715e0f43c8f07f303a314c48cac1a1645a0e138e14c4b1324a91a515134c344c9322c4b41c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "d36d36db69b6d249a49b4da6d369b4db6da49349b6d269a492492449249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨59, by decide⟩, ⟨62, by decide⟩, ⟨65, by decide⟩, ⟨68, by decide⟩, ⟨71, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨86, by decide⟩, ⟨93, by decide⟩, ⟨97, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000180024802034df8000000", hexnat% "240000000001200000000", hexnat% "4800010400000000000", hexnat% "204000000000800000000000", hexnat% "8000004000000000000", hexnat% "10100008000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "220401812481ec34398000000", hexnat% "4800000000000000000", 52076478464, hexnat% "180000000000040000000", hexnat% "240000000001000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "220000802080ec04398000000", hexnat% "4800010020000000000", 52076478464, hexnat% "10100000001040000000", hexnat% "340000000000000000000", hexnat% "4080004000010000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨93, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3d010000c001bf8000000", hexnat% "2000000020800000000000000", hexnat% "c800000400000000000", 5066841638567936, hexnat% "4000004000030000000000", hexnat% "200000000000800000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2204004824816c34610000000", hexnat% "18000000000000000000", hexnat% "80000000000100000000", hexnat% "340000000000040000000", 105897787392, hexnat% "100008000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3d010001c001af8000000", hexnat% "2000000020800000000000000", hexnat% "c800000400000000000", 563246306164736, hexnat% "204000000000830000000000", 4611686018427387904]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000000020814001210000000", hexnat% "340000000000040000000", 58653147136, hexnat% "c800000400000000000", 565423854583808, hexnat% "4080004000010000000000", hexnat% "200010100008800000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c10 c3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c11 c0
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record008_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record008_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00091.record008

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00091.record009
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record009
def vertexColumn : Fields := ⟨10, hexnat% "dcccab26cb2a9a96a368d68d9362d8ce8b92e1ba1e4789e17b31ac5b1ca6695a4d9356354d4b53362d4b46d8751d2745dc8ea368e6358ce3c4e9364cd38cd332cf0b92d4b32e2b4ac6b86d1b26c5b31e2749ca719e1745c9715c3783d0f23c4f0bc1fc60e4c88e2c4b0a8691a318a6198961381ec84e1c470986519314a5194951341d"⟩
def kindColumn : Fields := ⟨3, hexnat% "34da6da6d26d24926d36d36936924936da4db6da6db6d26d369369b6da689249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨28, by decide⟩, ⟨34, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨41, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨52, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨77, by decide⟩, ⟨81, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨96, by decide⟩, ⟨100, by decide⟩, ⟨103, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "19200321810326414000000", hexnat% "90000000000000000000000000", hexnat% "220c0000000000000000", hexnat% "20000400000000000000000", hexnat% "200004000000000000000000", hexnat% "1106000000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "13260260c0000224400000000", hexnat% "18000000000100004000000", hexnat% "300000000000000000", hexnat% "10000200400000000000000000", hexnat% "80001000020810000000000000", 1152921642314235904]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1019200321810326414000000", hexnat% "90000000000000000000000000", hexnat% "2020040000000000000000", hexnat% "304000000000000000000000", hexnat% "20000400000000000000000", hexnat% "6080000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "133e002080000322014000000", hexnat% "340000000000000000", hexnat% "20400000000000000000", hexnat% "80001004000000000000000000", hexnat% "21810004400000000", hexnat% "10000200000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11000003c0000300004000000", hexnat% "1e000000000000000000000", hexnat% "1200020810000000000000", hexnat% "10020000400000000000000000", hexnat% "80200004000000000000000000", 1152924133395267584, hexnat% "22000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨92, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨96, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c7 c0
  c8
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record009_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record009_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record009_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record009_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record009_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record009_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record009_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record009_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record009_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00091.record009
