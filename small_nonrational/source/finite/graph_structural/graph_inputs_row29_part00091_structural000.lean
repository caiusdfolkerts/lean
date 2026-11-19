module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow29Part00091Data
public import GraphInputsRow29Part00091Frames
public import GraphInputsRow29Part00091Leaves
public import GraphInputsRow29Part00091Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

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

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00091.record002
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "cb31c3c8ea358ce8b92e1ba1e4789ecc6b16c6715c4f1aa5a93a719a6599c966559655554d53362d4b46d8751d276334ccb31cccb8ad2b1ae1b46c9b31e2749c6785d1725e0f43c8f13c2f07f28c530c388d22a856c84e1c44d1c26294a4a9c1615454558350d30ca318c9314c8b0ac4705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "4924db6db4db69249b4da49a4d26da4924da4da492492449249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record002 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record002 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record002.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 51), (facetIndex 52), (facetIndex 74), (facetIndex 79), (facetIndex 89)]))
 (.leaf ([(facetIndex 34), (facetIndex 37), (facetIndex 43), (facetIndex 62), (facetIndex 87)])))
 (.branch 3
 (.leaf ([(facetIndex 33), (facetIndex 47), (facetIndex 50), (facetIndex 71), (facetIndex 88)]))
 (.leaf ([(facetIndex 31), (facetIndex 44), (facetIndex 56), (facetIndex 57), (facetIndex 70), (facetIndex 90)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 38), (facetIndex 39), (facetIndex 63), (facetIndex 64)]))
 (.leaf ([(facetIndex 32), (facetIndex 48), (facetIndex 49), (facetIndex 59), (facetIndex 60), (facetIndex 72), (facetIndex 73)])))
 (.branch 7
 (.leaf ([(facetIndex 35), (facetIndex 36)]))
 (.leaf ([(facetIndex 40), (facetIndex 67), (facetIndex 91)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "ec220000000002d4c0e04845a1b0000ad40320790ec556z17;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 55), (facetIndex 61)]))
 (.branch 2
 (.leaf ([(facetIndex 58), (facetIndex 86)]))
 (.leaf ([(facetIndex 53), (facetIndex 54), (facetIndex 75), (facetIndex 76), (facetIndex 77), (facetIndex 78)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 41), (facetIndex 42), (facetIndex 65), (facetIndex 66), (facetIndex 83)]))
 (.leaf ([(facetIndex 45), (facetIndex 46), (facetIndex 68), (facetIndex 69), (facetIndex 80)])))
 (.branch 6
 (.leaf ([(facetIndex 84), (facetIndex 85)]))
 (.leaf ([(facetIndex 81), (facetIndex 82)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6d7b40924000240d80000400900001200d8z1e;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3]
def grouped2_0005 : List Nat := [3]
def grouped2_0006 : List Nat := [4, 5]
def grouped2_0007 : List Nat := [4, 5, 6, 7]
def grouped2_0008 : List Nat := [6]
def grouped2_0009 : List Nat := [6, 7]
def grouped2_0010 : List Nat := [7]
def grouped3_0011 : List Nat := [0]
def grouped3_0012 : List Nat := [0, 1, 2]
def grouped3_0014 : List Nat := [1]
def grouped3_0015 : List Nat := [1, 2]
def grouped3_0016 : List Nat := [2]
def grouped3_0017 : List Nat := [3]
def grouped3_0018 : List Nat := [3, 4]
def grouped3_0019 : List Nat := [3, 4, 5, 6]
def grouped3_0020 : List Nat := [4]
def grouped3_0021 : List Nat := [5]
def grouped3_0022 : List Nat := [5, 6]
def grouped3_0023 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record002 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record002_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00091.record002" "{\"atoms\":[{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"groupKind3\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00091.record002" 59

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00091.record002" "{\"ridges\":[[31,14],[41,294],[42,550],[45,282],[46,538],[53,306],[54,562],[58,108],[65,356],[66,612],[68,408],[69,664],[75,368],[76,624],[77,432],[78,688],[81,282],[82,538],[83,108]],\"owners\":[[31,14,[83,84,85,86],[0,32,33,34,35,36,80,81,82]],[41,294,[84],[]],[42,550,[85],[]],[45,282,[81],[]],[81,282,[45],[]],[46,538,[82],[]],[82,538,[46],[]],[53,306,[],[]],[54,562,[],[]],[58,108,[83],[]],[83,108,[58],[]],[65,356,[],[]],[66,612,[],[]],[68,408,[],[]],[69,664,[],[]],[75,368,[],[]],[76,624,[],[]],[77,432,[],[]],[78,688,[],[]]],\"edges\":[],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00091.record002" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00091.record002\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-27,-6],[-27,-13],[-27,-14],[-27,-21],[-28,-6],[-28,-13],[-28,-14],[-28,-21],[-29,-6],[-29,-13],[-29,-14],[-29,-21],[-30,-2],[-30,-9],[-30,-10],[-30,-22],[-31,-3],[-31,-18],[-32,-3],[-32,-18],[-33,-2],[-33,-9],[-33,-10],[-33,-22],[-34,-30],[-34,-33],[-35,-27],[-35,-28],[-35,-29],[-36,-31],[-36,-32],[-1,30,31,32,33],[-4,31],[-5,32],[-7,28],[-28,7],[-8,29],[-29,8],[-11],[-12],[-15,30],[-30,15],[-16],[-17],[-19],[-20],[-23],[-24],[-25],[-26],[-37,2,9,10,22,34],[-38,1,6,13,14,21,35],[-39,3,18,36],[-40,37],[-40,38],[-41,40],[-42,39],[-43,42],[-44,41],[-44,43],[44],[-45,15,33],[-15,45],[-33,45],[-46,11,12,23,24,25,26],[-47,4,5,16,17,30],[-48,7,8,19,20,27],[-7,48],[-8,48],[-49,31,32],[-31,49],[-32,49],[-50,28,29],[-28,50],[-51,45,46],[-52,51],[-53,47,48],[-48,53],[-54,49,50],[-55,50],[-49,-50,55],[-56,53,54],[-53,-55,57],[-57,59],[-58,52,56],[58],[-59]],\"atoms\":[{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":80,\"b\":44},{\"tag\":\"incompatible\",\"a\":80,\"b\":56},{\"tag\":\"incompatible\",\"a\":80,\"b\":57},{\"tag\":\"incompatible\",\"a\":80,\"b\":70},{\"tag\":\"incompatible\",\"a\":81,\"b\":44},{\"tag\":\"incompatible\",\"a\":81,\"b\":56},{\"tag\":\"incompatible\",\"a\":81,\"b\":57},{\"tag\":\"incompatible\",\"a\":81,\"b\":70},{\"tag\":\"incompatible\",\"a\":82,\"b\":44},{\"tag\":\"incompatible\",\"a\":82,\"b\":56},{\"tag\":\"incompatible\",\"a\":82,\"b\":57},{\"tag\":\"incompatible\",\"a\":82,\"b\":70},{\"tag\":\"incompatible\",\"a\":83,\"b\":33},{\"tag\":\"incompatible\",\"a\":83,\"b\":47},{\"tag\":\"incompatible\",\"a\":83,\"b\":50},{\"tag\":\"incompatible\",\"a\":83,\"b\":71},{\"tag\":\"incompatible\",\"a\":84,\"b\":40},{\"tag\":\"incompatible\",\"a\":84,\"b\":67},{\"tag\":\"incompatible\",\"a\":85,\"b\":40},{\"tag\":\"incompatible\",\"a\":85,\"b\":67},{\"tag\":\"incompatible\",\"a\":86,\"b\":33},{\"tag\":\"incompatible\",\"a\":86,\"b\":47},{\"tag\":\"incompatible\",\"a\":86,\"b\":50},{\"tag\":\"incompatible\",\"a\":86,\"b\":71},{\"tag\":\"incompatible\",\"a\":88,\"b\":83},{\"tag\":\"incompatible\",\"a\":88,\"b\":86},{\"tag\":\"incompatible\",\"a\":90,\"b\":80},{\"tag\":\"incompatible\",\"a\":90,\"b\":81},{\"tag\":\"incompatible\",\"a\":90,\"b\":82},{\"tag\":\"incompatible\",\"a\":91,\"b\":84},{\"tag\":\"incompatible\",\"a\":91,\"b\":85},{\"tag\":\"mate\",\"ridge\":14,\"a\":31,\"owners\":[83,84,85,86]},{\"tag\":\"mate\",\"ridge\":294,\"a\":41,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":550,\"a\":42,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":282,\"a\":45,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":282,\"a\":81,\"owners\":[45]},{\"tag\":\"mate\",\"ridge\":538,\"a\":46,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":538,\"a\":82,\"owners\":[46]},{\"tag\":\"mate\",\"ridge\":306,\"a\":53,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":562,\"a\":54,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":108,\"a\":58,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":108,\"a\":83,\"owners\":[58]},{\"tag\":\"mate\",\"ridge\":356,\"a\":65,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":612,\"a\":66,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":408,\"a\":68,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":664,\"a\":69,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":368,\"a\":75,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":624,\"a\":76,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":432,\"a\":77,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":688,\"a\":78,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[33,47,50,71,88],\"full_literals\":[-37,2,9,10,22,34]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[31,44,56,57,70,90],\"full_literals\":[-38,1,6,13,14,21,35]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[40,67,91],\"full_literals\":[-39,3,18,36]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-40,37,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-40,false,38],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-41,false,40],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-42,false,39],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-43,false,42],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-44,41,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-44,false,43],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[58,86],\"full_literals\":[-45,15,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":58,\"full_literals\":[-15,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":86,\"full_literals\":[-33,45]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[53,54,75,76,77,78],\"full_literals\":[-46,11,12,23,24,25,26]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[41,42,65,66,83],\"full_literals\":[-47,4,5,16,17,30]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[45,46,68,69,80],\"full_literals\":[-48,7,8,19,20,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":45,\"full_literals\":[-7,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":46,\"full_literals\":[-8,48]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[84,85],\"full_literals\":[-49,31,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":84,\"full_literals\":[-31,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":85,\"full_literals\":[-32,49]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[81,82],\"full_literals\":[-50,28,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":81,\"full_literals\":[-28,50]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-51,45,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-52,false,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-53,47,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-48,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-54,49,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-55,false,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-49,-50,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-56,53,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-53,-55,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-57,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-58,52,56],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true}]}"
  "p cnf 59 87\n-27 -6 0\n-27 -13 0\n-27 -14 0\n-27 -21 0\n-28 -6 0\n-28 -13 0\n-28 -14 0\n-28 -21 0\n-29 -6 0\n-29 -13 0\n-29 -14 0\n-29 -21 0\n-30 -2 0\n-30 -9 0\n-30 -10 0\n-30 -22 0\n-31 -3 0\n-31 -18 0\n-32 -3 0\n-32 -18 0\n-33 -2 0\n-33 -9 0\n-33 -10 0\n-33 -22 0\n-34 -30 0\n-34 -33 0\n-35 -27 0\n-35 -28 0\n-35 -29 0\n-36 -31 0\n-36 -32 0\n-1 30 31 32 33 0\n-4 31 0\n-5 32 0\n-7 28 0\n-28 7 0\n-8 29 0\n-29 8 0\n-11 0\n-12 0\n-15 30 0\n-30 15 0\n-16 0\n-17 0\n-19 0\n-20 0\n-23 0\n-24 0\n-25 0\n-26 0\n-37 2 9 10 22 34 0\n-38 1 6 13 14 21 35 0\n-39 3 18 36 0\n-40 37 0\n-40 38 0\n-41 40 0\n-42 39 0\n-43 42 0\n-44 41 0\n-44 43 0\n44 0\n-45 15 33 0\n-15 45 0\n-33 45 0\n-46 11 12 23 24 25 26 0\n-47 4 5 16 17 30 0\n-48 7 8 19 20 27 0\n-7 48 0\n-8 48 0\n-49 31 32 0\n-31 49 0\n-32 49 0\n-50 28 29 0\n-28 50 0\n-51 45 46 0\n-52 51 0\n-53 47 48 0\n-48 53 0\n-54 49 50 0\n-55 50 0\n-49 -50 55 0\n-56 53 54 0\n-53 -55 57 0\n-57 59 0\n-58 52 56 0\n58 0\n-59 0\n"
  "88 41 0 61 59 0\n89 43 0 61 60 0\n90 40 0 88 56 0\n91 42 0 89 58 0\n92 37 0 90 54 0\n93 38 0 90 55 0\n94 39 0 91 57 0\n95 -46 0 39 40 47 48 49 50 65 0\n96 -47 4 5 30 0 43 44 66 0\n97 -48 7 8 27 0 45 46 67 0\n98 -51 45 0 95 75 0\n99 -57 0 87 84 0\n100 -55 0 99 80 83 78 68 69 36 38 73 0\n101 -29 1 0 93 9 10 11 12 29 52 0\n102 -50 45 0 100 93 63 42 64 81 71 72 32 101 73 5 6 7 8 28 52 0\n103 -32 0 94 19 20 31 53 0\n104 -5 0 103 34 0\n105 -31 0 94 17 18 30 53 0\n106 -4 0 105 33 0\n107 -49 0 105 103 70 0\n108 33 30 0 104 106 105 103 107 86 93 96 41 62 32 98 102 101 76 74 79 37 85 35 82 77 97 1 2 3 4 27 52 0\n109 -33 0 92 21 22 23 24 26 51 0\n110 30 0 109 108 0\n111 -2 0 110 13 0\n112 -9 0 110 14 0\n113 -10 0 110 15 0\n114 -22 0 110 16 0\n115 -34 0 110 25 0\n116 0 115 111 92 113 112 114 51 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record002.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record002.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record002.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record002.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record002 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record002.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record002.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record002.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record002.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record002 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record002_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record002 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record002_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record002_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00091.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00091.record004
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "ce2b43d26c3b31c8f332ac9b23cb2a9a96a3ab1a8e93ac5a9635b0e938ce8791ecc5b13c7295a4e9c66394e4e5c54d58d4b51d70d3362d2b46d8751d0f72368d6338f1364cd38cd332cc73c2d4b32e2b4acab1ae1b46c3bc1e1745c5783d0f23c1fcc328c4b0a31a1625a0e138e14c4b14a46931495134c344c9342c4b21c4705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "4db6da6da6da6d24924d24926d269a6d369b6db4926934934d34da492489249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record004 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record004 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record004.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record004.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record004.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 55), (facetIndex 59), (facetIndex 60), (facetIndex 63), (facetIndex 100), (facetIndex 102)]))
 (.leaf ([(facetIndex 65), (facetIndex 97), (facetIndex 99), (facetIndex 101)])))
 (.branch 3
 (.leaf ([(facetIndex 33), (facetIndex 36), (facetIndex 56)]))
 (.leaf ([(facetIndex 57), (facetIndex 62), (facetIndex 78)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 67), (facetIndex 70), (facetIndex 98)]))
 (.leaf ([(facetIndex 34), (facetIndex 38), (facetIndex 40), (facetIndex 44), (facetIndex 52), (facetIndex 53), (facetIndex 91), (facetIndex 95)])))
 (.branch 7
 (.leaf ([(facetIndex 47), (facetIndex 86), (facetIndex 89), (facetIndex 90), (facetIndex 93), (facetIndex 94)]))
 (.leaf ([(facetIndex 54), (facetIndex 71), (facetIndex 87)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "8308bb0bb0f800000c0000f008080c001a1ed000c0500514215z19;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1]
def grouped3_0002 : List Nat := [0, 1, 2, 3]
def grouped3_0004 : List Nat := [1]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [2, 3]
def grouped3_0007 : List Nat := [3]
def grouped3_0008 : List Nat := [4]
def grouped3_0009 : List Nat := [4, 5]
def grouped3_0010 : List Nat := [4, 5, 6, 7]
def grouped3_0011 : List Nat := [5]
def grouped3_0012 : List Nat := [6]
def grouped3_0013 : List Nat := [6, 7]
def grouped3_0014 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record004 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record004_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00091.record004" "{\"atoms\":[{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00091.record004" 82

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00091.record004" "{\"ridges\":[[14,176],[15,49],[16,224],[18,524],[20,532],[24,552],[25,560],[29,524],[32,532],[34,58],[38,170],[40,547],[44,114],[45,176],[46,49],[47,547],[51,224],[52,354],[53,418],[54,547],[59,172],[63,116],[64,176],[67,773],[68,224],[69,49],[70,537],[72,104],[74,552],[75,176],[76,176],[77,49],[77,560],[79,524],[81,524],[82,524],[84,532],[85,532],[86,58],[87,58],[89,170],[90,354],[91,610],[92,552],[93,114],[94,418],[95,674],[96,560],[98,284],[100,612],[102,676],[103,552],[103,560]],\"owners\":[[72,104,[90,91,100],[12,37,58,73,89,99]],[15,49,[14,34,44,45,47,55,63,64,65,70,75],[46,69,77]],[46,49,[14,55,63,64,65,70,75],[15,34,44,45,47,69,77]],[69,49,[14,44,45,47,63,64,65,75],[15,34,46,55,70,77]],[77,49,[14,34,44,45,55,63,64,75],[15,46,47,65,69,70]],[14,176,[93,94,95,101,102],[45,64,75,76]],[45,176,[101,102],[14,64,75,76,93,94,95]],[64,176,[93,94,95],[14,45,75,76,101,102]],[75,176,[94,95,102],[14,45,64,76,93,101]],[76,176,[93,95,101,102],[14,45,64,75,94]],[16,224,[89,93,99,101],[51,68,72,75]],[51,224,[99,101],[16,68,72,75,89,93]],[68,224,[89,93],[16,51,72,75,99,101]],[18,524,[57,60,62,97,98,100],[29,79,81,82]],[29,524,[97,98,100],[18,57,60,62,79,81,82]],[79,524,[60,62,100],[18,29,57,81,82,97,98]],[81,524,[57,60,62,97,98],[18,29,79,82,100]],[82,524,[57,60,97,100],[18,29,62,79,81,98]],[20,532,[57,65,67,97,98,102],[32,79,84,85]],[32,532,[97,98,102],[20,57,65,67,79,84,85]],[84,532,[57,65,67,97,98],[20,32,79,85,102]],[85,532,[57,65,97,102],[20,32,67,79,84,98]],[24,552,[40,60,70,87,91,97,100],[74,92,103]],[74,552,[87,91,97,100],[24,40,60,70,92,103]],[92,552,[60,70,97,100],[24,40,74,87,91,103]],[103,552,[40,60,91,100],[24,70,74,87,92,97]],[25,560,[47,65,70,87,95,97,102],[77,96,103]],[77,560,[87,95,97,102],[25,47,65,70,96,103]],[96,560,[65,70,97,102],[25,47,77,87,95,103]],[103,560,[47,65,95,102],[25,70,77,87,96,97]],[67,773,[33,62],[]],[34,58,[86,87],[]],[86,58,[34,87],[]],[87,58,[34,86],[]],[70,537,[36,57,71],[]],[38,170,[89],[]],[89,170,[38],[]],[40,547,[47,54],[]],[47,547,[40,54],[]],[54,547,[40,47],[]],[44,114,[93],[]],[93,114,[44],[]],[52,354,[90],[]],[90,354,[52],[]],[53,418,[94],[]],[94,418,[53],[]],[98,284,[56,78],[]],[59,172,[99],[]],[63,116,[101],[]],[91,610,[],[]],[95,674,[],[]],[100,612,[],[]],[102,676,[],[]]],\"edges\":[[23,[18,20,29,32,33,57,60,62,65,67,79,81,82,84,85,97,98,100,102]],[30,[14,15,25,34,44,45,46,47,55,63,64,65,69,70,75,76,77,86,87,93,94,95,96,97,101,102,103]],[36,[14,16,38,45,51,53,59,64,68,72,75,76,89,93,94,95,99,101,102]],[38,[24,25,40,47,54,60,65,70,74,77,87,91,92,95,96,97,100,102,103]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00091.record004" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00091.record004\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-36,-22],[-36,-27],[-36,-31],[-38,-36],[-40,-35],[-41,-36],[-49,-36],[-53,-36],[-57,-36],[-58,-36],[-60,-23],[-60,-27],[-60,-31],[-60,-58],[-62,-27],[-62,-31],[-62,-58],[-64,-36],[-37,51,52,61],[-2,1,11,15,16,18,23,29,30,31,35,39],[-17,1,23,29,30,31,35,39],[-34,1,15,16,18,29,30,31,39],[-41,1,11,15,16,23,29,30,39],[-1,54,55,56,62,63],[-16,62,63],[-30,54,55,56],[-39,55,56,63],[-40,54,56,62,63],[-3,50,54,60,62],[-19,60,62],[-33,50,54],[-4,25,27,28,58,59,61],[-8,58,59,61],[-43,27,28,61],[-44,25,27,28,58,59],[-45,25,27,58,61],[-5,25,31,32,58,59,63],[-9,58,59,63],[-46,25,31,32,58,59],[-47,25,31,58,63],[-6,14,27,35,49,52,58,61],[-38,49,52,58,61],[-53,27,35,58,61],[-64,14,27,52,61],[-7,18,31,35,49,56,58,63],[-41,49,56,58,63],[-57,31,35,58,63],[-64,18,31,56,63],[-32,10,28],[-11,48,49],[-48,11,49],[-49,11,48],[-35,12,25,36],[-13,50],[-50,13],[-14,18,22],[-18,14,22],[-22,14,18],[-15,54],[-54,15],[-20,51],[-51,20],[-21,55],[-55,21],[-59,24,42],[-26,60],[-29,62],[-52],[-56],[-61],[-63],[-26,65],[-27,65],[-31,66],[-58,66],[-60,66],[-62,66],[-10,67],[-12,67],[-24,67],[-25,68],[-28,68],[-42,68],[-69,32,35,59],[-35,69],[-70,11,13,14,15,20,21,52,56],[-11,70],[-13,70],[-14,70],[-15,70],[-20,70],[-21,70],[-71,18,48,50,51,54,55],[-18,71],[-48,71],[-50,71],[-51,71],[-54,71],[-55,71],[-72,22,36,49],[-22,72],[-36,72],[-49,72],[-66,73],[-65,73],[-68,74],[-67,74],[-74,75],[-73,75],[-73,-74,76],[-77,69,70],[-70,77],[-69,77],[-78,71,72],[-72,78],[-71,78],[-71,-72,79],[-80,77,78],[-79,81],[-77,80],[-77,-78,81],[-75,-81,82],[-76,-80,82],[-82],[4,5,8,9,10,25,27,28,31,32,43,44,45,46,47,58,59,61,63],[1,2,7,11,15,16,17,18,23,29,30,31,34,35,39,40,41,48,49,54,55,56,57,58,62,63,64],[1,3,13,16,19,21,26,30,33,37,39,40,50,54,55,56,60,62,63],[6,7,14,18,22,27,31,35,38,41,49,52,53,56,57,58,61,63,64]],\"atoms\":[{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":71,\"b\":54},{\"tag\":\"incompatible\",\"a\":71,\"b\":60},{\"tag\":\"incompatible\",\"a\":71,\"b\":65},{\"tag\":\"incompatible\",\"a\":74,\"b\":71},{\"tag\":\"incompatible\",\"a\":76,\"b\":70},{\"tag\":\"incompatible\",\"a\":77,\"b\":71},{\"tag\":\"incompatible\",\"a\":87,\"b\":71},{\"tag\":\"incompatible\",\"a\":92,\"b\":71},{\"tag\":\"incompatible\",\"a\":96,\"b\":71},{\"tag\":\"incompatible\",\"a\":97,\"b\":71},{\"tag\":\"incompatible\",\"a\":99,\"b\":55},{\"tag\":\"incompatible\",\"a\":99,\"b\":60},{\"tag\":\"incompatible\",\"a\":99,\"b\":65},{\"tag\":\"incompatible\",\"a\":99,\"b\":97},{\"tag\":\"incompatible\",\"a\":101,\"b\":60},{\"tag\":\"incompatible\",\"a\":101,\"b\":65},{\"tag\":\"incompatible\",\"a\":101,\"b\":97},{\"tag\":\"incompatible\",\"a\":103,\"b\":71},{\"tag\":\"mate\",\"ridge\":104,\"a\":72,\"owners\":[90,91,100]},{\"tag\":\"mate\",\"ridge\":49,\"a\":15,\"owners\":[14,34,44,45,47,55,63,64,65,70,75]},{\"tag\":\"mate\",\"ridge\":49,\"a\":46,\"owners\":[14,55,63,64,65,70,75]},{\"tag\":\"mate\",\"ridge\":49,\"a\":69,\"owners\":[14,44,45,47,63,64,65,75]},{\"tag\":\"mate\",\"ridge\":49,\"a\":77,\"owners\":[14,34,44,45,55,63,64,75]},{\"tag\":\"mate\",\"ridge\":176,\"a\":14,\"owners\":[93,94,95,101,102]},{\"tag\":\"mate\",\"ridge\":176,\"a\":45,\"owners\":[101,102]},{\"tag\":\"mate\",\"ridge\":176,\"a\":64,\"owners\":[93,94,95]},{\"tag\":\"mate\",\"ridge\":176,\"a\":75,\"owners\":[94,95,102]},{\"tag\":\"mate\",\"ridge\":176,\"a\":76,\"owners\":[93,95,101,102]},{\"tag\":\"mate\",\"ridge\":224,\"a\":16,\"owners\":[89,93,99,101]},{\"tag\":\"mate\",\"ridge\":224,\"a\":51,\"owners\":[99,101]},{\"tag\":\"mate\",\"ridge\":224,\"a\":68,\"owners\":[89,93]},{\"tag\":\"mate\",\"ridge\":524,\"a\":18,\"owners\":[57,60,62,97,98,100]},{\"tag\":\"mate\",\"ridge\":524,\"a\":29,\"owners\":[97,98,100]},{\"tag\":\"mate\",\"ridge\":524,\"a\":79,\"owners\":[60,62,100]},{\"tag\":\"mate\",\"ridge\":524,\"a\":81,\"owners\":[57,60,62,97,98]},{\"tag\":\"mate\",\"ridge\":524,\"a\":82,\"owners\":[57,60,97,100]},{\"tag\":\"mate\",\"ridge\":532,\"a\":20,\"owners\":[57,65,67,97,98,102]},{\"tag\":\"mate\",\"ridge\":532,\"a\":32,\"owners\":[97,98,102]},{\"tag\":\"mate\",\"ridge\":532,\"a\":84,\"owners\":[57,65,67,97,98]},{\"tag\":\"mate\",\"ridge\":532,\"a\":85,\"owners\":[57,65,97,102]},{\"tag\":\"mate\",\"ridge\":552,\"a\":24,\"owners\":[40,60,70,87,91,97,100]},{\"tag\":\"mate\",\"ridge\":552,\"a\":74,\"owners\":[87,91,97,100]},{\"tag\":\"mate\",\"ridge\":552,\"a\":92,\"owners\":[60,70,97,100]},{\"tag\":\"mate\",\"ridge\":552,\"a\":103,\"owners\":[40,60,91,100]},{\"tag\":\"mate\",\"ridge\":560,\"a\":25,\"owners\":[47,65,70,87,95,97,102]},{\"tag\":\"mate\",\"ridge\":560,\"a\":77,\"owners\":[87,95,97,102]},{\"tag\":\"mate\",\"ridge\":560,\"a\":96,\"owners\":[65,70,97,102]},{\"tag\":\"mate\",\"ridge\":560,\"a\":103,\"owners\":[47,65,95,102]},{\"tag\":\"mate\",\"ridge\":773,\"a\":67,\"owners\":[33,62]},{\"tag\":\"mate\",\"ridge\":58,\"a\":34,\"owners\":[86,87]},{\"tag\":\"mate\",\"ridge\":58,\"a\":86,\"owners\":[34,87]},{\"tag\":\"mate\",\"ridge\":58,\"a\":87,\"owners\":[34,86]},{\"tag\":\"mate\",\"ridge\":537,\"a\":70,\"owners\":[36,57,71]},{\"tag\":\"mate\",\"ridge\":170,\"a\":38,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":170,\"a\":89,\"owners\":[38]},{\"tag\":\"mate\",\"ridge\":547,\"a\":40,\"owners\":[47,54]},{\"tag\":\"mate\",\"ridge\":547,\"a\":47,\"owners\":[40,54]},{\"tag\":\"mate\",\"ridge\":547,\"a\":54,\"owners\":[40,47]},{\"tag\":\"mate\",\"ridge\":114,\"a\":44,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":114,\"a\":93,\"owners\":[44]},{\"tag\":\"mate\",\"ridge\":354,\"a\":52,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":354,\"a\":90,\"owners\":[52]},{\"tag\":\"mate\",\"ridge\":418,\"a\":53,\"owners\":[94]},{\"tag\":\"mate\",\"ridge\":418,\"a\":94,\"owners\":[53]},{\"tag\":\"mate\",\"ridge\":284,\"a\":98,\"owners\":[56,78]},{\"tag\":\"mate\",\"ridge\":172,\"a\":59,\"owners\":[99]},{\"tag\":\"mate\",\"ridge\":116,\"a\":63,\"owners\":[101]},{\"tag\":\"mate\",\"ridge\":610,\"a\":91,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":674,\"a\":95,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":612,\"a\":100,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":676,\"a\":102,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":59,\"full_literals\":[-26,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":60,\"full_literals\":[-27,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":65,\"full_literals\":[-31,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":97,\"full_literals\":[-58,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":99,\"full_literals\":[-60,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":101,\"full_literals\":[-62,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":33,\"full_literals\":[-10,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":36,\"full_literals\":[-12,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":56,\"full_literals\":[-24,67]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":57,\"full_literals\":[-25,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":62,\"full_literals\":[-28,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":78,\"full_literals\":[-42,68]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[67,70,98],\"full_literals\":[-69,32,35,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":70,\"full_literals\":[-35,69]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[34,38,40,44,52,53,91,95],\"full_literals\":[-70,11,13,14,15,20,21,52,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":34,\"full_literals\":[-11,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":38,\"full_literals\":[-13,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":40,\"full_literals\":[-14,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":44,\"full_literals\":[-15,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":52,\"full_literals\":[-20,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":53,\"full_literals\":[-21,70]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[47,86,89,90,93,94],\"full_literals\":[-71,18,48,50,51,54,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":47,\"full_literals\":[-18,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":86,\"full_literals\":[-48,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":89,\"full_literals\":[-50,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":90,\"full_literals\":[-51,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":93,\"full_literals\":[-54,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":94,\"full_literals\":[-55,71]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[54,71,87],\"full_literals\":[-72,22,36,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":54,\"full_literals\":[-22,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":71,\"full_literals\":[-36,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":87,\"full_literals\":[-49,72]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-66,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-65,false,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-68,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-67,false,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-74,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-73,false,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-73,-74,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-77,69,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-70,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-69,false,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-78,71,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-72,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-71,false,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-71,-72,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-80,77,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-79,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-77,false,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-77,-78,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-75,-81,82],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-76,-80,82],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":23,\"owners\":[18,20,29,32,33,57,60,62,65,67,79,81,82,84,85,97,98,100,102]},{\"tag\":\"edge\",\"edge\":30,\"owners\":[14,15,25,34,44,45,46,47,55,63,64,65,69,70,75,76,77,86,87,93,94,95,96,97,101,102,103]},{\"tag\":\"edge\",\"edge\":36,\"owners\":[14,16,38,45,51,53,59,64,68,72,75,76,89,93,94,95,99,101,102]},{\"tag\":\"edge\",\"edge\":38,\"owners\":[24,25,40,47,54,60,65,70,74,77,87,91,92,95,96,97,100,102,103]}]}"
  "p cnf 82 128\n-36 -22 0\n-36 -27 0\n-36 -31 0\n-38 -36 0\n-40 -35 0\n-41 -36 0\n-49 -36 0\n-53 -36 0\n-57 -36 0\n-58 -36 0\n-60 -23 0\n-60 -27 0\n-60 -31 0\n-60 -58 0\n-62 -27 0\n-62 -31 0\n-62 -58 0\n-64 -36 0\n-37 51 52 61 0\n-2 1 11 15 16 18 23 29 30 31 35 39 0\n-17 1 23 29 30 31 35 39 0\n-34 1 15 16 18 29 30 31 39 0\n-41 1 11 15 16 23 29 30 39 0\n-1 54 55 56 62 63 0\n-16 62 63 0\n-30 54 55 56 0\n-39 55 56 63 0\n-40 54 56 62 63 0\n-3 50 54 60 62 0\n-19 60 62 0\n-33 50 54 0\n-4 25 27 28 58 59 61 0\n-8 58 59 61 0\n-43 27 28 61 0\n-44 25 27 28 58 59 0\n-45 25 27 58 61 0\n-5 25 31 32 58 59 63 0\n-9 58 59 63 0\n-46 25 31 32 58 59 0\n-47 25 31 58 63 0\n-6 14 27 35 49 52 58 61 0\n-38 49 52 58 61 0\n-53 27 35 58 61 0\n-64 14 27 52 61 0\n-7 18 31 35 49 56 58 63 0\n-41 49 56 58 63 0\n-57 31 35 58 63 0\n-64 18 31 56 63 0\n-32 10 28 0\n-11 48 49 0\n-48 11 49 0\n-49 11 48 0\n-35 12 25 36 0\n-13 50 0\n-50 13 0\n-14 18 22 0\n-18 14 22 0\n-22 14 18 0\n-15 54 0\n-54 15 0\n-20 51 0\n-51 20 0\n-21 55 0\n-55 21 0\n-59 24 42 0\n-26 60 0\n-29 62 0\n-52 0\n-56 0\n-61 0\n-63 0\n-26 65 0\n-27 65 0\n-31 66 0\n-58 66 0\n-60 66 0\n-62 66 0\n-10 67 0\n-12 67 0\n-24 67 0\n-25 68 0\n-28 68 0\n-42 68 0\n-69 32 35 59 0\n-35 69 0\n-70 11 13 14 15 20 21 52 56 0\n-11 70 0\n-13 70 0\n-14 70 0\n-15 70 0\n-20 70 0\n-21 70 0\n-71 18 48 50 51 54 55 0\n-18 71 0\n-48 71 0\n-50 71 0\n-51 71 0\n-54 71 0\n-55 71 0\n-72 22 36 49 0\n-22 72 0\n-36 72 0\n-49 72 0\n-66 73 0\n-65 73 0\n-68 74 0\n-67 74 0\n-74 75 0\n-73 75 0\n-73 -74 76 0\n-77 69 70 0\n-70 77 0\n-69 77 0\n-78 71 72 0\n-72 78 0\n-71 78 0\n-71 -72 79 0\n-80 77 78 0\n-79 81 0\n-77 80 0\n-77 -78 81 0\n-75 -81 82 0\n-76 -80 82 0\n-82 0\n4 5 8 9 10 25 27 28 31 32 43 44 45 46 47 58 59 61 63 0\n1 2 7 11 15 16 17 18 23 29 30 31 34 35 39 40 41 48 49 54 55 56 57 58 62 63 64 0\n1 3 13 16 19 21 26 30 33 37 39 40 50 54 55 56 60 62 63 0\n6 7 14 18 22 27 31 35 38 41 49 52 53 56 57 58 61 63 64 0\n"
  "129 -70 11 13 14 15 20 21 0 68 69 86 0\n130 4 5 8 9 10 25 27 28 31 32 43 44 45 46 47 58 59 0 70 71 125 0\n131 1 2 7 11 15 16 17 18 23 29 30 31 34 35 39 40 41 48 49 54 55 57 58 62 64 0 69 71 126 0\n132 1 3 13 16 19 21 26 30 33 37 39 40 50 54 55 60 62 0 69 71 127 0\n133 6 7 14 18 22 27 31 35 38 41 49 53 57 58 64 0 68 69 70 71 128 0\n134 75 0 70 71 108 109 106 107 104 105 81 82 83 78 80 74 75 73 49 34 65 40 33 38 36 32 35 37 39 130 0\n135 -81 0 134 124 122 0\n136 -79 0 135 119 0\n137 -72 36 70 0 136 89 87 117 94 95 58 52 100 0\n138 72 -78 0 135 121 112 92 64 91 62 90 60 88 55 89 87 101 103 114 57 51 93 0\n139 -78 0 135 136 70 68 71 69 121 112 113 89 85 138 117 137 94 1 2 3 4 6 7 8 9 10 18 41 45 133 0\n140 -72 0 139 115 0\n141 -71 0 139 116 0\n142 -22 0 140 101 0\n143 -36 0 140 102 0\n144 -49 0 140 103 0\n145 -18 0 141 94 0\n146 -48 0 141 95 0\n147 -50 0 141 96 0\n148 -51 0 141 97 0\n149 -54 0 141 98 0\n150 -55 0 141 99 0\n151 -14 0 145 142 56 0\n152 -11 0 146 144 50 0\n153 -13 0 147 54 0\n154 -37 0 148 68 70 19 0\n155 -20 0 148 61 0\n156 -15 0 149 59 0\n157 -33 0 149 147 31 0\n158 -39 0 150 69 71 27 0\n159 -21 0 150 63 0\n160 -30 0 150 149 69 26 0\n161 -70 0 159 153 151 152 155 156 129 0\n162 74 35 -69 0 106 107 82 83 78 80 49 65 84 0\n163 35 -80 0 124 161 139 68 71 69 70 144 142 145 151 118 111 123 162 110 104 105 74 75 73 47 48 42 46 41 45 43 133 0\n164 73 40 0 71 69 160 150 149 147 158 159 154 157 153 104 105 76 77 72 30 25 29 24 132 0\n165 -80 0 124 143 123 163 5 164 110 106 107 81 79 53 0\n166 -77 0 165 120 0\n167 -69 0 166 113 0\n168 -35 0 167 85 0\n169 60 62 0 69 71 160 150 149 147 158 159 154 157 153 28 24 25 30 66 29 132 0\n170 62 0 70 68 151 71 69 150 149 144 146 158 168 160 145 156 152 25 67 24 28 169 11 12 13 14 21 20 23 44 47 22 45 131 0\n171 -27 0 170 15 0\n172 -31 0 170 16 0\n173 -58 0 170 17 0\n174 -64 0 171 151 68 70 44 0\n175 -53 0 171 168 173 70 43 0\n176 -57 0 172 168 173 71 47 0\n177 -38 0 173 68 144 70 42 0\n178 -41 0 173 69 144 71 46 0\n179 -6 0 173 171 151 168 68 144 70 41 0\n180 -7 0 173 172 145 168 69 144 71 45 0\n181 0 179 180 151 145 142 171 172 168 177 178 144 175 176 173 174 133 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record004.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record004.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record004.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record004.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record004 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record004.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record004.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record004.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record004.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record004 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record004_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record004 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record004_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record004_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00091.record004

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00091.record005
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "338ad0f49b0ecc723c6c8f25a8eac693ac58d6c38ce8791eac5b13c6695a4e9c66394e6a5994e5c5695356352d475c364d3362d2b46d8751d0f5a358ce3c4d9334d332cc73c2d4b32d2b2ac6b86d1b0ef0785d1715e0f43c8f07f30ca0c62584ec84e1c46314c4b1c26294a469316152560d134c344c9342c4b21c4705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "26db6db6db69a6d24924936924934926936da4924d249a69b492491249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record005 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record005 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record005.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record005.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record005.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 36), (facetIndex 39), (facetIndex 56)]))
 (.branch 2
 (.leaf ([(facetIndex 82), (facetIndex 83), (facetIndex 85)]))
 (.leaf ([(facetIndex 87), (facetIndex 89), (facetIndex 95)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 37), (facetIndex 41), (facetIndex 46), (facetIndex 53), (facetIndex 54)]))
 (.leaf ([(facetIndex 55), (facetIndex 59), (facetIndex 64), (facetIndex 71), (facetIndex 72)])))
 (.branch 6
 (.leaf ([(facetIndex 88), (facetIndex 90), (facetIndex 91), (facetIndex 92), (facetIndex 93)]))
 (.leaf ([(facetIndex 94), (facetIndex 96), (facetIndex 97), (facetIndex 98), (facetIndex 99)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db65adb554082400000048000040008008d80000c0018018z1b;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1, 2]
def grouped3_0003 : List Nat := [1]
def grouped3_0004 : List Nat := [1, 2]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [3]
def grouped3_0007 : List Nat := [3, 4]
def grouped3_0008 : List Nat := [3, 4, 5, 6]
def grouped3_0009 : List Nat := [4]
def grouped3_0010 : List Nat := [5]
def grouped3_0011 : List Nat := [5, 6]
def grouped3_0012 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record005 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record005_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00091.record005" "{\"atoms\":[{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00091.record005" 74

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00091.record005" "{\"ridges\":[[5,266],[7,274],[10,524],[12,532],[18,176],[22,224],[31,266],[32,524],[34,274],[35,532],[38,266],[41,170],[42,266],[44,266],[45,266],[47,176],[48,274],[50,274],[51,274],[52,224],[53,354],[54,418],[57,524],[59,172],[60,524],[62,524],[63,524],[65,176],[66,532],[68,532],[69,532],[70,224],[71,612],[72,676],[76,104],[79,224],[80,176],[81,176],[88,58],[90,170],[91,354],[92,114],[93,418],[94,60],[96,172],[97,612],[98,116],[99,676]],\"owners\":[[5,266,[82,85,88,89,91],[31,38,42,44,45]],[31,266,[88,89,91],[5,38,42,44,45,82,85]],[38,266,[85,91],[5,31,42,44,45,82,88,89]],[42,266,[82,85,89],[5,31,38,44,45,88,91]],[44,266,[82,85,88,89],[5,31,38,42,45,91]],[45,266,[82,88,91],[5,31,38,42,44,85,89]],[7,274,[82,87,88,89,93],[34,38,48,50,51]],[34,274,[88,89,93],[7,38,48,50,51,82,87]],[48,274,[82,87,89],[7,34,38,50,51,88,93]],[50,274,[82,87,88,89],[7,34,38,48,51,93]],[51,274,[82,88,93],[7,34,38,48,50,87,89]],[10,524,[83,85,94,95,97],[32,57,60,62,63]],[32,524,[94,95,97],[10,57,60,62,63,83,85]],[57,524,[85,97],[10,32,60,62,63,83,94,95]],[60,524,[83,85,95],[10,32,57,62,63,94,97]],[62,524,[83,85,94,95],[10,32,57,60,63,97]],[63,524,[83,94,97],[10,32,57,60,62,85,95]],[12,532,[83,87,94,95,99],[35,57,66,68,69]],[35,532,[94,95,99],[12,57,66,68,69,83,87]],[66,532,[83,87,95],[12,35,57,68,69,94,99]],[68,532,[83,87,94,95],[12,35,57,66,69,99]],[69,532,[83,94,99],[12,35,57,66,68,87,95]],[76,104,[91,97],[14,40,58,77,78,90,96]],[18,176,[92,93,98,99],[47,65,79,80,81]],[47,176,[98,99],[18,65,79,80,81,92,93]],[65,176,[92,93],[18,47,79,80,81,98,99]],[80,176,[92,98,99],[18,47,65,79,81,93]],[81,176,[92,93,98],[18,47,65,79,80,99]],[22,224,[90,92,96,98],[52,70,76,79]],[52,224,[96,98],[22,70,76,79,90,92]],[70,224,[90,92],[22,52,76,79,96,98]],[79,224,[90,96],[22,52,70,76,92,98]],[88,58,[37],[]],[41,170,[90],[]],[90,170,[41],[]],[92,114,[46],[]],[53,354,[91],[]],[91,354,[53],[]],[54,418,[93],[]],[93,418,[54],[]],[94,60,[55],[]],[59,172,[96],[]],[96,172,[59],[]],[98,116,[64],[]],[71,612,[97],[]],[97,612,[71],[]],[72,676,[99],[]],[99,676,[72],[]]],\"edges\":[[15,[5,7,31,34,36,38,42,44,45,48,50,51,53,54,82,85,87,88,89,91,93]],[23,[10,12,32,35,36,57,60,62,63,66,68,69,71,72,83,85,87,94,95,97,99]],[36,[18,22,41,47,52,54,59,65,70,72,76,79,80,81,90,92,93,96,98,99]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00091.record005" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00091.record005\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,44,46,48,49,51],[-7,48,49,51],[-13,46,51],[-15,44,46,49],[-16,44,46,48,49],[-17,44,48,51],[-2,44,47,48,49,53],[-9,48,49,53],[-20,44,47,49],[-21,44,47,48,49],[-22,44,48,53],[-3,45,46,54,55,57],[-8,54,55,57],[-27,46,57],[-29,45,46,55],[-30,45,46,54,55],[-31,45,54,57],[-4,45,47,54,55,59],[-10,54,55,59],[-34,45,47,55],[-35,45,47,54,55],[-36,45,54,59],[-40,51,57],[-5,52,53,58,59],[-19,58,59],[-33,52,53],[-42,52,58,59],[-43,52,53,58],[-6,50,52,56,58],[-23,56,58],[-37,50,52],[-41,50,56],[-48,12],[-14,50],[-50,14],[-52,18],[-24,51],[-51,24],[-25,53],[-53,25],[-54,26],[-28,56],[-56,28],[-58,32],[-38,57],[-57,38],[-39,59],[-59,39],[-11,60],[-44,61],[-45,61],[-46,61],[-47,62],[-49,62],[-55,62],[-12,63],[-14,63],[-18,63],[-24,63],[-25,63],[-26,64],[-28,64],[-32,64],[-38,64],[-39,64],[-65,48,50,51,52,53],[-48,65],[-50,65],[-51,65],[-52,65],[-53,65],[-66,54,56,57,58,59],[-54,66],[-56,66],[-57,66],[-58,66],[-59,66],[-62,67],[-61,67],[-67,68],[-60,68],[-64,69],[-63,69],[-66,70],[-65,70],[-71,66],[-65,-66,71],[-69,-70,72],[-69,-71,73],[-73,74],[-68,-72,74],[-74],[1,2,7,9,11,13,15,16,17,20,21,22,24,25,44,46,47,48,49,51,53],[3,4,8,10,11,27,29,30,31,34,35,36,38,39,45,46,47,54,55,57,59],[5,6,14,19,23,25,28,33,37,39,40,41,42,43,50,52,53,56,58,59]],\"atoms\":[{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":266,\"a\":5,\"owners\":[82,85,88,89,91]},{\"tag\":\"mate\",\"ridge\":266,\"a\":31,\"owners\":[88,89,91]},{\"tag\":\"mate\",\"ridge\":266,\"a\":38,\"owners\":[85,91]},{\"tag\":\"mate\",\"ridge\":266,\"a\":42,\"owners\":[82,85,89]},{\"tag\":\"mate\",\"ridge\":266,\"a\":44,\"owners\":[82,85,88,89]},{\"tag\":\"mate\",\"ridge\":266,\"a\":45,\"owners\":[82,88,91]},{\"tag\":\"mate\",\"ridge\":274,\"a\":7,\"owners\":[82,87,88,89,93]},{\"tag\":\"mate\",\"ridge\":274,\"a\":34,\"owners\":[88,89,93]},{\"tag\":\"mate\",\"ridge\":274,\"a\":48,\"owners\":[82,87,89]},{\"tag\":\"mate\",\"ridge\":274,\"a\":50,\"owners\":[82,87,88,89]},{\"tag\":\"mate\",\"ridge\":274,\"a\":51,\"owners\":[82,88,93]},{\"tag\":\"mate\",\"ridge\":524,\"a\":10,\"owners\":[83,85,94,95,97]},{\"tag\":\"mate\",\"ridge\":524,\"a\":32,\"owners\":[94,95,97]},{\"tag\":\"mate\",\"ridge\":524,\"a\":57,\"owners\":[85,97]},{\"tag\":\"mate\",\"ridge\":524,\"a\":60,\"owners\":[83,85,95]},{\"tag\":\"mate\",\"ridge\":524,\"a\":62,\"owners\":[83,85,94,95]},{\"tag\":\"mate\",\"ridge\":524,\"a\":63,\"owners\":[83,94,97]},{\"tag\":\"mate\",\"ridge\":532,\"a\":12,\"owners\":[83,87,94,95,99]},{\"tag\":\"mate\",\"ridge\":532,\"a\":35,\"owners\":[94,95,99]},{\"tag\":\"mate\",\"ridge\":532,\"a\":66,\"owners\":[83,87,95]},{\"tag\":\"mate\",\"ridge\":532,\"a\":68,\"owners\":[83,87,94,95]},{\"tag\":\"mate\",\"ridge\":532,\"a\":69,\"owners\":[83,94,99]},{\"tag\":\"mate\",\"ridge\":104,\"a\":76,\"owners\":[91,97]},{\"tag\":\"mate\",\"ridge\":176,\"a\":18,\"owners\":[92,93,98,99]},{\"tag\":\"mate\",\"ridge\":176,\"a\":47,\"owners\":[98,99]},{\"tag\":\"mate\",\"ridge\":176,\"a\":65,\"owners\":[92,93]},{\"tag\":\"mate\",\"ridge\":176,\"a\":80,\"owners\":[92,98,99]},{\"tag\":\"mate\",\"ridge\":176,\"a\":81,\"owners\":[92,93,98]},{\"tag\":\"mate\",\"ridge\":224,\"a\":22,\"owners\":[90,92,96,98]},{\"tag\":\"mate\",\"ridge\":224,\"a\":52,\"owners\":[96,98]},{\"tag\":\"mate\",\"ridge\":224,\"a\":70,\"owners\":[90,92]},{\"tag\":\"mate\",\"ridge\":224,\"a\":79,\"owners\":[90,96]},{\"tag\":\"mate\",\"ridge\":58,\"a\":88,\"owners\":[37]},{\"tag\":\"mate\",\"ridge\":170,\"a\":41,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":170,\"a\":90,\"owners\":[41]},{\"tag\":\"mate\",\"ridge\":114,\"a\":92,\"owners\":[46]},{\"tag\":\"mate\",\"ridge\":354,\"a\":53,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":354,\"a\":91,\"owners\":[53]},{\"tag\":\"mate\",\"ridge\":418,\"a\":54,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":418,\"a\":93,\"owners\":[54]},{\"tag\":\"mate\",\"ridge\":60,\"a\":94,\"owners\":[55]},{\"tag\":\"mate\",\"ridge\":172,\"a\":59,\"owners\":[96]},{\"tag\":\"mate\",\"ridge\":172,\"a\":96,\"owners\":[59]},{\"tag\":\"mate\",\"ridge\":116,\"a\":98,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":612,\"a\":71,\"owners\":[97]},{\"tag\":\"mate\",\"ridge\":612,\"a\":97,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":676,\"a\":72,\"owners\":[99]},{\"tag\":\"mate\",\"ridge\":676,\"a\":99,\"owners\":[72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":36,\"full_literals\":[-11,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":82,\"full_literals\":[-44,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":83,\"full_literals\":[-45,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":85,\"full_literals\":[-46,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":87,\"full_literals\":[-47,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":89,\"full_literals\":[-49,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":95,\"full_literals\":[-55,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":37,\"full_literals\":[-12,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":41,\"full_literals\":[-14,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":46,\"full_literals\":[-18,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":53,\"full_literals\":[-24,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":54,\"full_literals\":[-25,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":55,\"full_literals\":[-26,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":59,\"full_literals\":[-28,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":64,\"full_literals\":[-32,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":71,\"full_literals\":[-38,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":72,\"full_literals\":[-39,64]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[88,90,91,92,93],\"full_literals\":[-65,48,50,51,52,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":88,\"full_literals\":[-48,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":90,\"full_literals\":[-50,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":91,\"full_literals\":[-51,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":92,\"full_literals\":[-52,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":93,\"full_literals\":[-53,65]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[94,96,97,98,99],\"full_literals\":[-66,54,56,57,58,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":94,\"full_literals\":[-54,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":96,\"full_literals\":[-56,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":97,\"full_literals\":[-57,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":98,\"full_literals\":[-58,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":99,\"full_literals\":[-59,66]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-62,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-61,false,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-67,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-60,false,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-64,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-63,false,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-66,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-65,false,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-71,false,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-65,-66,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-69,-70,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-69,-71,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-73,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-68,-72,74],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":15,\"owners\":[5,7,31,34,36,38,42,44,45,48,50,51,53,54,82,85,87,88,89,91,93]},{\"tag\":\"edge\",\"edge\":23,\"owners\":[10,12,32,35,36,57,60,62,63,66,68,69,71,72,83,85,87,94,95,97,99]},{\"tag\":\"edge\",\"edge\":36,\"owners\":[18,22,41,47,52,54,59,65,70,72,76,79,80,81,90,92,93,96,98,99]}]}"
  "p cnf 74 95\n-1 44 46 48 49 51 0\n-7 48 49 51 0\n-13 46 51 0\n-15 44 46 49 0\n-16 44 46 48 49 0\n-17 44 48 51 0\n-2 44 47 48 49 53 0\n-9 48 49 53 0\n-20 44 47 49 0\n-21 44 47 48 49 0\n-22 44 48 53 0\n-3 45 46 54 55 57 0\n-8 54 55 57 0\n-27 46 57 0\n-29 45 46 55 0\n-30 45 46 54 55 0\n-31 45 54 57 0\n-4 45 47 54 55 59 0\n-10 54 55 59 0\n-34 45 47 55 0\n-35 45 47 54 55 0\n-36 45 54 59 0\n-40 51 57 0\n-5 52 53 58 59 0\n-19 58 59 0\n-33 52 53 0\n-42 52 58 59 0\n-43 52 53 58 0\n-6 50 52 56 58 0\n-23 56 58 0\n-37 50 52 0\n-41 50 56 0\n-48 12 0\n-14 50 0\n-50 14 0\n-52 18 0\n-24 51 0\n-51 24 0\n-25 53 0\n-53 25 0\n-54 26 0\n-28 56 0\n-56 28 0\n-58 32 0\n-38 57 0\n-57 38 0\n-39 59 0\n-59 39 0\n-11 60 0\n-44 61 0\n-45 61 0\n-46 61 0\n-47 62 0\n-49 62 0\n-55 62 0\n-12 63 0\n-14 63 0\n-18 63 0\n-24 63 0\n-25 63 0\n-26 64 0\n-28 64 0\n-32 64 0\n-38 64 0\n-39 64 0\n-65 48 50 51 52 53 0\n-48 65 0\n-50 65 0\n-51 65 0\n-52 65 0\n-53 65 0\n-66 54 56 57 58 59 0\n-54 66 0\n-56 66 0\n-57 66 0\n-58 66 0\n-59 66 0\n-62 67 0\n-61 67 0\n-67 68 0\n-60 68 0\n-64 69 0\n-63 69 0\n-66 70 0\n-65 70 0\n-71 66 0\n-65 -66 71 0\n-69 -70 72 0\n-69 -71 73 0\n-73 74 0\n-68 -72 74 0\n-74 0\n1 2 7 9 11 13 15 16 17 20 21 22 24 25 44 46 47 48 49 51 53 0\n3 4 8 10 11 27 29 30 31 34 35 36 38 39 45 46 47 54 55 57 59 0\n5 6 14 19 23 25 28 33 37 39 40 41 42 43 50 52 53 56 58 59 0\n"
  "96 -73 0 92 90 0\n97 -71 0 96 86 89 82 61 62 63 64 65 41 43 44 46 48 72 0\n98 65 68 0 80 78 54 53 79 50 9 52 4 81 49 67 69 71 2 8 1 5 10 37 6 3 39 11 7 93 0\n99 68 0 97 80 81 78 79 49 53 55 51 52 15 20 98 87 73 75 77 13 19 16 21 22 12 18 45 17 14 47 94 0\n100 -72 0 99 92 91 0\n101 -65 0 100 85 88 83 56 57 58 59 60 33 35 36 38 40 66 0\n102 -50 0 101 68 0\n103 -51 0 101 69 0\n104 -52 0 101 70 0\n105 -53 0 101 71 0\n106 -14 0 102 34 0\n107 -37 0 104 102 31 0\n108 -25 0 105 39 0\n109 -33 0 105 104 26 0\n110 66 0 103 105 104 102 109 107 108 106 74 75 76 77 42 30 32 29 23 25 24 28 47 27 95 0\n111 70 0 110 84 0\n112 -69 0 111 100 88 0\n113 -64 0 112 82 0\n114 -26 0 113 61 0\n115 -28 0 113 62 0\n116 -32 0 113 63 0\n117 -38 0 113 64 0\n118 -39 0 113 65 0\n119 -54 0 114 41 0\n120 -56 0 115 43 0\n121 -58 0 116 44 0\n122 -57 0 117 46 0\n123 -59 0 118 48 0\n124 0 122 119 120 110 121 123 72 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record005.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record005.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record005.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record005.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record005 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record005.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record005.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record005.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record005.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record005 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record005_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record005 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record005_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00091.record005_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00091.record005
