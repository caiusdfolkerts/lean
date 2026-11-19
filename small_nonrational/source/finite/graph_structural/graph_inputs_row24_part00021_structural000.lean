module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00021Data
public import GraphInputsRow24Part00021Frames
public import GraphInputsRow24Part00021Leaves
public import GraphInputsRow24Part00021Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00021.record005
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record005
def vertexColumn : Fields := ⟨10, hexnat% "1d43d31c1f392749aac699a719a639b166595635b0e4b86e8791e17b913c719664b91e4e5c5595354b51d70d1b61d4745d0f783c4e9364e5334f0b62e2b2ac6b86d1b26c5bc1d8731ca785d1725c5783d0f13c1fc611c38b0a1990e0b8e134619194550b41d30ca318e0b0ac4709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "369b6d36d36da49a6d26da6d34d24936db49a4936db49b692489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨60, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨77, by decide⟩, ⟨81, by decide⟩, ⟨86, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400181001a05e003c00000", hexnat% "200100000080004000000", hexnat% "20400000000040000000", hexnat% "21280000080000000", 10133099161583616]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20090003e09e047c00000", hexnat% "10000040000000000", hexnat% "4001000000000000000000", hexnat% "20400000000000000000", hexnat% "21280000080000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2001212a6082086c00000", 1925219090432, hexnat% "c00000000001000000", hexnat% "20000000000000000000", hexnat% "4000010018000000000000", hexnat% "1000000040000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1925323948032, hexnat% "1900000000001000000", hexnat% "21200080080000000", hexnat% "20400000000000000000", hexnat% "4000010018000000000000", hexnat% "200000000042000000000", 46724846142357504]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c5 c0
  c6
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record005_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record005_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00021.record005

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00021.record009
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record009
def vertexColumn : Fields := ⟨10, hexnat% "761b4c707c749b23c9ca6695a3687a699964d8b61d86e4785e0fb19664d91e715654b51d70d1b61d4745d0f78364cd32cc73c2d8b92ccb1ad1b26c5b0ef0761e2729c6745c9715c3743c4f0bc1f3c30c470e2c2b068390e384d12c471164358341d30ca318e0b12e0709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b4db4db6db6db4db6936926924da49349369a6926da492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨67, by decide⟩, ⟨79, by decide⟩, ⟨83, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [7356997503171952640, 140750641692672, hexnat% "80080000000001000000", 81100046518452224, hexnat% "800000040000000000000", 17179869184]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [7356841127976108032, 288346924384256, hexnat% "80080000000001000000", 81100046518452224, hexnat% "800000040000000000000", 8796093022208]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80008637800410d000000", 15393162788864, 35253091565568, 288441491242614784, 17213423616, hexnat% "80000001000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [7066504331989614592, 290482176233832448, hexnat% "800000160000008000000", 35253091565568, hexnat% "80080000800001000000", 30098325504, 10995183386624]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c5 c0
  c6
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record009_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record009_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record009_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record009_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record009_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record009_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record009_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record009_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record009_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00021.record009

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00021.record025
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record025
def vertexColumn : Fields := ⟨10, hexnat% "3d13c1f39272b1a66a3a4e9c639b16659362d94e4b86e4783ee44f1c6599366391e4e5c5595354b51d46d4745d0f78338f13a4d938ccb3c2d8b92ccb8ae1b46c9b0ef0761ca785d1725c3743c4f0bc1fc6194c286a618c61986986439314652543530c6382c4b0ac8711c27"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6da6da4d36da6db4da49a4926d34db6d34926d349b49a4c9249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨63, by decide⟩, ⟨68, by decide⟩, ⟨73, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨80, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "180004e080e0cd800000", hexnat% "100012000000000000", hexnat% "2000100000000000000", 1729382265500205056, hexnat% "100008000021000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10187200e245800000", hexnat% "8000400800000000000", 108086393338593280, hexnat% "12000000000000000000", hexnat% "100008000021000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "81004f280004d800000", 962072674304, hexnat% "12000000000080000000", 9295431829915959296, 1729382265500205056, hexnat% "100000000001000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1120085c20212cc000000", 589971551193923584, 1152921642045800448, hexnat% "8100000800001000000", 824633720832]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "18101c7282f2cd800000", 108086391056891904, hexnat% "100008000000000000000", hexnat% "2000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8101c1282f249800000", hexnat% "12000000000080000000", hexnat% "100008000000000000000", 63050394783186944, 67108864, 72057594037927936]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [288935026890899456, hexnat% "18000000000080000000", 1729382265500205056, 63050394783186944, hexnat% "100010000000800000", 9295431829915959296, hexnat% "102000000001004000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c9 c2
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c10 c1
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c11 c0
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record025_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record025_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record025_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record025_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record025_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record025_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record025_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record025_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record025_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00021.record025

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00021.record001
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "cb0dc1f1e2e2b2a6a99ac98d61db0e8b92e8789e0f9e1e27296a4e9664d91e72535475c34cd8b52d1b61d2745d0f78370f2368d6338d931cf0ba2d8b8ad2b2ae1b46c9b0ef0791cc789d2785c970de0f43c8f0bc1f34866158d1c25894a499194558342d0770360cc348c6324c5381c4709c17"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db6db6936db6d24d26d24d249249249249a69b69a4924926d2249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record001 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record001 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record001.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record001.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record001.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 34), (facetIndex 47), (facetIndex 81), (facetIndex 82)]))
 (.leaf ([(facetIndex 38), (facetIndex 48), (facetIndex 68), (facetIndex 69)])))
 (.branch 3
 (.leaf ([(facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 53)]))
 (.leaf ([(facetIndex 42), (facetIndex 44), (facetIndex 46), (facetIndex 71), (facetIndex 72), (facetIndex 73)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 55), (facetIndex 58), (facetIndex 60), (facetIndex 61), (facetIndex 63)]))
 (.leaf ([(facetIndex 29), (facetIndex 56), (facetIndex 59), (facetIndex 64)])))
 (.branch 7
 (.leaf ([(facetIndex 32), (facetIndex 36), (facetIndex 52), (facetIndex 54)]))
 (.branch 8
 (.leaf ([(facetIndex 24), (facetIndex 25), (facetIndex 28), (facetIndex 31), (facetIndex 33), (facetIndex 35)]))
 (.leaf ([(facetIndex 30), (facetIndex 57), (facetIndex 65)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "33301100854044548546262221030303000106707678570077z18;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 41), (facetIndex 70), (facetIndex 74)]))
 (.leaf ([(facetIndex 85), (facetIndex 88)])))
 (.branch 3
 (.leaf ([(facetIndex 62), (facetIndex 67)]))
 (.leaf ([(facetIndex 89), (facetIndex 90)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 27), (facetIndex 43), (facetIndex 66)]))
 (.leaf ([(facetIndex 78), (facetIndex 79), (facetIndex 83)])))
 (.branch 7
 (.leaf ([(facetIndex 80), (facetIndex 86), (facetIndex 91)]))
 (.branch 8
 (.leaf ([(facetIndex 26), (facetIndex 37), (facetIndex 39), (facetIndex 40), (facetIndex 45)]))
 (.leaf ([(facetIndex 75), (facetIndex 76), (facetIndex 77), (facetIndex 84), (facetIndex 87)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "633186185006558880000000240002z10;70400770700000000047z1a;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [2, 3]
def grouped2_0007 : List Nat := [3]
def grouped2_0008 : List Nat := [4, 5, 6, 7, 8]
def grouped3_0009 : List Nat := [0]
def grouped3_0010 : List Nat := [0, 1]
def grouped3_0011 : List Nat := [0, 1, 2, 3]
def grouped3_0013 : List Nat := [1]
def grouped3_0014 : List Nat := [2]
def grouped3_0015 : List Nat := [2, 3]
def grouped3_0016 : List Nat := [3]
def grouped3_0017 : List Nat := [4]
def grouped3_0018 : List Nat := [4, 5]
def grouped3_0019 : List Nat := [4, 5, 6, 7, 8]
def grouped3_0020 : List Nat := [5]
def grouped3_0021 : List Nat := [6]
def grouped3_0022 : List Nat := [6, 7, 8]
def grouped3_0023 : List Nat := [7]
def grouped3_0024 : List Nat := [7, 8]
def grouped3_0025 : List Nat := [8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record001 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record001_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00021.record001" "{\"atoms\":[{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00021.record001" 77

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00021.record001" "{\"ridges\":[[7,290],[16,152],[17,296],[18,392],[26,142],[32,290],[38,152],[41,170],[42,290],[44,392],[45,650],[50,290],[51,290],[51,386],[52,290],[57,28],[57,152],[60,296],[62,204],[66,804],[68,152],[69,152],[69,392],[70,232],[71,296],[71,392],[72,296],[73,392],[76,142],[78,270],[79,554],[83,804],[84,282],[85,170],[86,554],[87,650],[90,204],[91,804]],\"owners\":[[7,290,[78,83,85,86,88],[32,42,50,51,52]],[32,290,[85,86,88],[7,42,50,51,52,78,83]],[42,290,[83,88],[7,32,50,51,52,78,85,86]],[50,290,[78,83,85,86],[7,32,42,51,52,88]],[51,290,[78,83,86],[7,32,42,50,52,85,88]],[52,290,[78,85,88],[7,32,42,50,51,83,86]],[51,386,[84,87],[9,44,48,53,54,85,88]],[57,28,[75,77,89],[11,24,55,56,58,76,90]],[16,152,[76,84,90],[38,57,68,69]],[38,152,[90],[16,57,68,69,76,84]],[57,152,[84],[16,38,68,69,76,90]],[68,152,[76,84],[16,38,57,69,90]],[69,152,[76,90],[16,38,57,68,84]],[17,296,[78,85,86,91],[42,60,71,72]],[60,296,[85,86],[17,42,71,72,78,91]],[71,296,[78,86,91],[17,42,60,72,85]],[72,296,[78,85],[17,42,60,71,86,91]],[18,392,[84,85,87],[44,69,71,73]],[44,392,[],[18,69,71,73,84,85,87]],[69,392,[85,87],[18,44,71,73,84]],[71,392,[84,87],[18,44,69,73,85]],[73,392,[84,85],[18,44,69,71,87]],[26,142,[76],[]],[76,142,[26],[]],[78,270,[27,80],[]],[84,282,[39],[]],[41,170,[85],[]],[85,170,[41],[]],[79,554,[43,86],[]],[86,554,[43,79],[]],[45,650,[87],[]],[87,650,[45],[]],[62,204,[90],[]],[90,204,[62],[]],[66,804,[83,91],[]],[83,804,[66,91],[]],[91,804,[66,83],[]],[70,232,[],[]]],\"edges\":[[27,[16,18,26,38,41,44,45,57,62,68,69,70,71,73,76,84,85,87,90]],[37,[7,17,32,42,50,51,52,60,66,71,72,74,78,83,85,86,88,91]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00021.record001" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00021.record001\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-15,-10],[-17,-10],[-20,-10],[-40,-16],[-41,-5],[-41,-14],[-41,-32],[-41,-33],[-41,-34],[-41,-39],[-42,-41],[-1,35,38,40,41,43],[-7,40,41,43],[-11,38,43],[-17,35,38,40,41],[-18,35,38,41],[-19,35,40,43],[-18,39,42],[-21,32,34,44],[-2,33,39,45],[-8,45],[-21,39],[-25,33,39],[-26,33,45],[-3,35,40,41,46],[-22,40,41],[-28,35,41,46],[-29,35,40],[-4,39,40,42],[-13],[-26,40,42],[-28,39,42],[-30,39,40],[-5,33],[-33,5],[-35,6,37],[-39,9],[-10,40],[-40,10],[-36,12,41],[-41,12,36],[-14,42],[-42,14],[-23,45],[-45,23],[-24,38,46],[-38,24,46],[-46,24,38],[-27],[-47,8,15,25,26],[-48,16,17,18,20],[-49,47],[-50,48],[-51,49,50],[-52,51],[52],[-10,53],[-31,53],[-40,54],[-43,54],[-23,55],[-44,56],[-45,56],[-6,57],[-12,57],[-24,57],[-58,35,36,38],[-35,58],[-36,58],[-38,58],[-37,59],[-46,59],[-5,60],[-9,60],[-14,60],[-32,61],[-33,61],[-34,61],[-39,61],[-42,61],[-54,62],[-53,62],[-56,63],[-55,63],[-55,-56,64],[-63,65],[-64,66],[-62,65],[-62,-64,67],[-58,68],[-57,68],[-57,-58,69],[-61,70],[-60,70],[-60,-61,71],[-70,72],[-71,73],[-59,-70,73],[-73,75],[-68,74],[-68,-73,76],[-69,-72,76],[-76,77],[-65,-75,77],[-66,-74,77],[-67,77],[-77],[2,4,5,8,10,13,14,21,23,25,26,27,28,30,33,39,40,42,45],[1,3,7,11,17,18,19,22,24,28,29,31,35,38,40,41,43,46]],\"atoms\":[{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":48,\"b\":41},{\"tag\":\"incompatible\",\"a\":50,\"b\":41},{\"tag\":\"incompatible\",\"a\":53,\"b\":41},{\"tag\":\"incompatible\",\"a\":85,\"b\":49},{\"tag\":\"incompatible\",\"a\":86,\"b\":26},{\"tag\":\"incompatible\",\"a\":86,\"b\":45},{\"tag\":\"incompatible\",\"a\":86,\"b\":75},{\"tag\":\"incompatible\",\"a\":86,\"b\":76},{\"tag\":\"incompatible\",\"a\":86,\"b\":77},{\"tag\":\"incompatible\",\"a\":86,\"b\":84},{\"tag\":\"incompatible\",\"a\":87,\"b\":86},{\"tag\":\"mate\",\"ridge\":290,\"a\":7,\"owners\":[78,83,85,86,88]},{\"tag\":\"mate\",\"ridge\":290,\"a\":32,\"owners\":[85,86,88]},{\"tag\":\"mate\",\"ridge\":290,\"a\":42,\"owners\":[83,88]},{\"tag\":\"mate\",\"ridge\":290,\"a\":50,\"owners\":[78,83,85,86]},{\"tag\":\"mate\",\"ridge\":290,\"a\":51,\"owners\":[78,83,86]},{\"tag\":\"mate\",\"ridge\":290,\"a\":52,\"owners\":[78,85,88]},{\"tag\":\"mate\",\"ridge\":386,\"a\":51,\"owners\":[84,87]},{\"tag\":\"mate\",\"ridge\":28,\"a\":57,\"owners\":[75,77,89]},{\"tag\":\"mate\",\"ridge\":152,\"a\":16,\"owners\":[76,84,90]},{\"tag\":\"mate\",\"ridge\":152,\"a\":38,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":152,\"a\":57,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":152,\"a\":68,\"owners\":[76,84]},{\"tag\":\"mate\",\"ridge\":152,\"a\":69,\"owners\":[76,90]},{\"tag\":\"mate\",\"ridge\":296,\"a\":17,\"owners\":[78,85,86,91]},{\"tag\":\"mate\",\"ridge\":296,\"a\":60,\"owners\":[85,86]},{\"tag\":\"mate\",\"ridge\":296,\"a\":71,\"owners\":[78,86,91]},{\"tag\":\"mate\",\"ridge\":296,\"a\":72,\"owners\":[78,85]},{\"tag\":\"mate\",\"ridge\":392,\"a\":18,\"owners\":[84,85,87]},{\"tag\":\"mate\",\"ridge\":392,\"a\":44,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":392,\"a\":69,\"owners\":[85,87]},{\"tag\":\"mate\",\"ridge\":392,\"a\":71,\"owners\":[84,87]},{\"tag\":\"mate\",\"ridge\":392,\"a\":73,\"owners\":[84,85]},{\"tag\":\"mate\",\"ridge\":142,\"a\":26,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":142,\"a\":76,\"owners\":[26]},{\"tag\":\"mate\",\"ridge\":270,\"a\":78,\"owners\":[27,80]},{\"tag\":\"mate\",\"ridge\":282,\"a\":84,\"owners\":[39]},{\"tag\":\"mate\",\"ridge\":170,\"a\":41,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":170,\"a\":85,\"owners\":[41]},{\"tag\":\"mate\",\"ridge\":554,\"a\":79,\"owners\":[43,86]},{\"tag\":\"mate\",\"ridge\":554,\"a\":86,\"owners\":[43,79]},{\"tag\":\"mate\",\"ridge\":650,\"a\":45,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":650,\"a\":87,\"owners\":[45]},{\"tag\":\"mate\",\"ridge\":204,\"a\":62,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":204,\"a\":90,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":804,\"a\":66,\"owners\":[83,91]},{\"tag\":\"mate\",\"ridge\":804,\"a\":83,\"owners\":[66,91]},{\"tag\":\"mate\",\"ridge\":804,\"a\":91,\"owners\":[66,83]},{\"tag\":\"mate\",\"ridge\":232,\"a\":70,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[38,48,68,69],\"full_literals\":[-47,8,15,25,26]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[49,50,51,53],\"full_literals\":[-48,16,17,18,20]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-49,false,47],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-50,48,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-51,49,50],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-52,51,false],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":41,\"full_literals\":[-10,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":74,\"full_literals\":[-31,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":85,\"full_literals\":[-40,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":88,\"full_literals\":[-43,54]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":62,\"full_literals\":[-23,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":89,\"full_literals\":[-44,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":90,\"full_literals\":[-45,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":27,\"full_literals\":[-6,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":43,\"full_literals\":[-12,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":66,\"full_literals\":[-24,57]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[78,79,83],\"full_literals\":[-58,35,36,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":78,\"full_literals\":[-35,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":79,\"full_literals\":[-36,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":83,\"full_literals\":[-38,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":80,\"full_literals\":[-37,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":91,\"full_literals\":[-46,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":26,\"full_literals\":[-5,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":39,\"full_literals\":[-9,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":45,\"full_literals\":[-14,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":75,\"full_literals\":[-32,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":76,\"full_literals\":[-33,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":77,\"full_literals\":[-34,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":84,\"full_literals\":[-39,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":87,\"full_literals\":[-42,61]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-54,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-53,false,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-56,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-55,false,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-55,-56,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-63,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-64,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-62,false,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-62,-64,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-58,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-57,false,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-57,-58,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-61,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-60,false,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-60,-61,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-70,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-71,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-59,-70,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-73,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-68,false,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-68,-73,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0019\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-69,-72,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-76,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-65,-75,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-66,-74,77],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-67,false,77],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":27,\"owners\":[16,18,26,38,41,44,45,57,62,68,69,70,71,73,76,84,85,87,90]},{\"tag\":\"edge\",\"edge\":37,\"owners\":[7,17,32,42,50,51,52,60,66,71,72,74,78,83,85,86,88,91]}]}"
  "p cnf 77 109\n-15 -10 0\n-17 -10 0\n-20 -10 0\n-40 -16 0\n-41 -5 0\n-41 -14 0\n-41 -32 0\n-41 -33 0\n-41 -34 0\n-41 -39 0\n-42 -41 0\n-1 35 38 40 41 43 0\n-7 40 41 43 0\n-11 38 43 0\n-17 35 38 40 41 0\n-18 35 38 41 0\n-19 35 40 43 0\n-18 39 42 0\n-21 32 34 44 0\n-2 33 39 45 0\n-8 45 0\n-21 39 0\n-25 33 39 0\n-26 33 45 0\n-3 35 40 41 46 0\n-22 40 41 0\n-28 35 41 46 0\n-29 35 40 0\n-4 39 40 42 0\n-13 0\n-26 40 42 0\n-28 39 42 0\n-30 39 40 0\n-5 33 0\n-33 5 0\n-35 6 37 0\n-39 9 0\n-10 40 0\n-40 10 0\n-36 12 41 0\n-41 12 36 0\n-14 42 0\n-42 14 0\n-23 45 0\n-45 23 0\n-24 38 46 0\n-38 24 46 0\n-46 24 38 0\n-27 0\n-47 8 15 25 26 0\n-48 16 17 18 20 0\n-49 47 0\n-50 48 0\n-51 49 50 0\n-52 51 0\n52 0\n-10 53 0\n-31 53 0\n-40 54 0\n-43 54 0\n-23 55 0\n-44 56 0\n-45 56 0\n-6 57 0\n-12 57 0\n-24 57 0\n-58 35 36 38 0\n-35 58 0\n-36 58 0\n-38 58 0\n-37 59 0\n-46 59 0\n-5 60 0\n-9 60 0\n-14 60 0\n-32 61 0\n-33 61 0\n-34 61 0\n-39 61 0\n-42 61 0\n-54 62 0\n-53 62 0\n-56 63 0\n-55 63 0\n-55 -56 64 0\n-63 65 0\n-64 66 0\n-62 65 0\n-62 -64 67 0\n-58 68 0\n-57 68 0\n-57 -58 69 0\n-61 70 0\n-60 70 0\n-60 -61 71 0\n-70 72 0\n-71 73 0\n-59 -70 73 0\n-73 75 0\n-68 74 0\n-68 -73 76 0\n-69 -72 76 0\n-76 77 0\n-65 -75 77 0\n-66 -74 77 0\n-67 77 0\n-77 0\n2 4 5 8 10 13 14 21 23 25 26 27 28 30 33 39 40 42 45 0\n1 3 7 11 17 18 19 22 24 28 29 31 35 38 40 41 43 46 0\n"
  "110 51 0 56 55 0\n111 -76 0 107 103 0\n112 -67 0 107 106 0\n113 2 4 5 8 10 14 21 23 25 26 28 30 33 39 40 42 45 0 30 49 108 0\n114 68 62 0 82 58 81 60 59 90 91 68 69 70 65 66 17 28 14 48 41 27 13 26 15 25 12 16 109 0\n115 41 46 58 62 0 70 46 81 60 14 59 68 28 17 82 58 27 13 26 15 25 12 16 109 0\n116 -41 65 0 86 83 63 21 88 82 57 81 59 84 61 62 5 6 7 8 9 10 11 24 19 23 20 29 33 32 113 0\n117 70 65 0 86 83 63 21 88 82 57 81 59 84 61 62 93 94 76 77 78 79 80 73 75 24 19 23 20 29 33 32 113 0\n118 65 0 111 88 114 101 116 117 96 98 102 71 72 115 92 64 65 66 36 40 47 67 0\n119 -75 0 118 107 104 0\n120 -73 0 119 99 0\n121 -71 0 120 97 0\n122 33 39 42 45 28 40 0 33 29 22 31 42 44 21 38 34 23 20 113 0\n123 -33 0 121 35 77 73 95 0\n124 -39 0 121 37 79 74 95 0\n125 -25 0 124 123 23 0\n126 -42 0 121 43 80 75 95 0\n127 -28 0 126 124 32 0\n128 -18 0 126 124 18 0\n129 -64 0 112 107 87 89 105 114 100 0\n130 -45 0 129 45 63 61 85 0\n131 -8 0 130 21 0\n132 -26 0 130 123 24 0\n133 40 0 130 123 124 127 126 122 0\n134 -16 0 133 4 0\n135 10 0 133 39 0\n136 -15 0 135 1 0\n137 -17 0 135 2 0\n138 -20 0 135 3 0\n139 -47 0 136 131 125 132 50 0\n140 -48 0 138 137 128 134 51 0\n141 -49 0 139 52 0\n142 -50 0 140 53 0\n143 0 141 142 110 54 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record001.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record001.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record001.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record001.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record001 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record001.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record001.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record001.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record001.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record001 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record001_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record001 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record001_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record001_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00021.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00021.record003
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "32c1f1e23a8da1eb26658768b86e8789e1783e78789ca5a93a479c95951d70d6362d4b46d8749d1743de0dc3c8da358ce364c73a2e4b32e2b2ac6b86c9b16c3b61e2719e1745c9715c3783c8f13c2f07cd834b06498d13246926459c15258342d0770360cc348c6324c5381d0709c17"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36da69b6db6db6d24da6924924924926d369a4d2492493691249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record003 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record003 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record003.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record003.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record003.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 36), (facetIndex 53), (facetIndex 62), (facetIndex 67), (facetIndex 82)]))
 (.leaf ([(facetIndex 37), (facetIndex 49), (facetIndex 52), (facetIndex 54), (facetIndex 55)])))
 (.branch 3
 (.leaf ([(facetIndex 25), (facetIndex 26), (facetIndex 29), (facetIndex 39), (facetIndex 40), (facetIndex 42), (facetIndex 45), (facetIndex 84)]))
 (.leaf ([(facetIndex 56), (facetIndex 59), (facetIndex 61), (facetIndex 64)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 57), (facetIndex 60), (facetIndex 68), (facetIndex 69)]))
 (.leaf ([(facetIndex 32), (facetIndex 58)])))
 (.branch 7
 (.leaf ([(facetIndex 35), (facetIndex 48), (facetIndex 50), (facetIndex 51)]))
 (.leaf ([(facetIndex 30), (facetIndex 31), (facetIndex 33), (facetIndex 34)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "200000000002400301c763241d8e010082408dfdfd009z13;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 28), (facetIndex 63), (facetIndex 66)]))
 (.leaf ([(facetIndex 43), (facetIndex 70), (facetIndex 73)])))
 (.branch 3
 (.leaf ([(facetIndex 76), (facetIndex 81)]))
 (.branch 4
 (.leaf ([(facetIndex 85), (facetIndex 86)]))
 (.leaf ([(facetIndex 71), (facetIndex 72)])))))
 (.branch 8
 (.branch 6
 (.leaf ([(facetIndex 44), (facetIndex 88)]))
 (.branch 7
 (.leaf ([(facetIndex 27), (facetIndex 38), (facetIndex 65)]))
 (.leaf ([(facetIndex 74), (facetIndex 75), (facetIndex 80)]))))
 (.branch 9
 (.leaf ([(facetIndex 78), (facetIndex 83), (facetIndex 87)]))
 (.branch 10
 (.leaf ([(facetIndex 41), (facetIndex 46), (facetIndex 47), (facetIndex 79)]))
 (.leaf ([(facetIndex 77)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "58330802798a277144100006z11;990510900600000000006z1b;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 11
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2, 3]
def grouped2_0006 : List Nat := [4]
def grouped2_0007 : List Nat := [4, 5]
def grouped2_0008 : List Nat := [4, 5, 6, 7]
def grouped2_0009 : List Nat := [5]
def grouped2_0010 : List Nat := [6, 7]
def grouped3_0011 : List Nat := [0]
def grouped3_0012 : List Nat := [0, 1]
def grouped3_0013 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0015 : List Nat := [1]
def grouped3_0016 : List Nat := [2]
def grouped3_0017 : List Nat := [2, 3, 4]
def grouped3_0018 : List Nat := [3, 4]
def grouped3_0019 : List Nat := [5]
def grouped3_0020 : List Nat := [5, 6, 7]
def grouped3_0021 : List Nat := [5, 6, 7, 8, 9, 10]
def grouped3_0022 : List Nat := [6]
def grouped3_0023 : List Nat := [6, 7]
def grouped3_0024 : List Nat := [7]
def grouped3_0025 : List Nat := [8]
def grouped3_0026 : List Nat := [8, 9, 10]
def grouped3_0027 : List Nat := [9, 10]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record003 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record003_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00021.record003" "{\"atoms\":[{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00021.record003" 52

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00021.record003" "{\"ridges\":[[13,524],[29,524],[32,22],[37,385],[46,586],[47,650],[49,385],[52,386],[54,386],[55,385],[58,28],[59,524],[62,521],[63,396],[64,521],[70,424],[71,808],[72,904],[77,538],[79,554]],\"owners\":[[32,22,[74,75,77,80],[0,25,30,31,33,34,76,81]],[37,385,[70,72,73],[9,49,52,54,55,63,66]],[49,385,[63,70,72,73],[9,37,52,54,55,66]],[55,385,[63,66,70,73],[9,37,49,52,54,72]],[52,386,[81],[9,37,49,54,55,86]],[54,386,[81],[9,37,49,52,55,86]],[58,28,[74,75,77,87],[11,25,56,57,59,76]],[62,521,[41,46,47,72],[13,29,44,59,64,71]],[64,521,[41,44,46,47],[13,29,59,62,71,72]],[13,524,[77,79,88],[29,59,62,64]],[29,524,[88],[13,59,62,64,77,79]],[59,524,[79,88],[13,29,62,64,77]],[77,538,[41],[]],[79,554,[44],[]],[46,586,[],[]],[47,650,[],[]],[63,396,[],[]],[70,424,[],[]],[71,808,[88],[]],[72,904,[],[]]],\"edges\":[[29,[13,29,41,44,46,47,59,62,64,71,72,77,79,88]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00021.record003" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00021.record003\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-5,-3],[-13,-5],[-3,23,24,25,27],[-4,19,21,22],[-9,16,19,21,22],[-12,16,18,19,22],[-10,28],[-11,28],[-13,23,24,25,29],[-15,5,7,8,21],[-17,5,6,7,8],[-1,25,26,30],[-2,30],[-14,26,30],[-25,5],[-26,6],[-7],[-8],[-16],[-19],[-20,30],[-21],[-31,4,9,10,11,12],[-32,3,13],[-33,31],[-34,33],[-35,32],[-36,35],[-37,34],[-37,36],[37],[-18,38],[-22,39],[-28,40],[-6,41],[-30,41],[-23,42],[-24,42],[-27,42],[-29,43],[-39,44],[-38,44],[-40,45],[-45,46],[-44,46],[-42,47],[-41,48],[-41,-47,49],[-43,50],[-48,-50,51],[-49,51],[-46,-51,52],[-52],[1,2,5,6,7,8,14,15,17,20,21,25,26,30]],\"atoms\":[{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":41,\"b\":32},{\"tag\":\"incompatible\",\"a\":58,\"b\":41},{\"tag\":\"mate\",\"ridge\":22,\"a\":32,\"owners\":[74,75,77,80]},{\"tag\":\"mate\",\"ridge\":385,\"a\":37,\"owners\":[70,72,73]},{\"tag\":\"mate\",\"ridge\":385,\"a\":49,\"owners\":[63,70,72,73]},{\"tag\":\"mate\",\"ridge\":385,\"a\":55,\"owners\":[63,66,70,73]},{\"tag\":\"mate\",\"ridge\":386,\"a\":52,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":386,\"a\":54,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":28,\"a\":58,\"owners\":[74,75,77,87]},{\"tag\":\"mate\",\"ridge\":521,\"a\":62,\"owners\":[41,46,47,72]},{\"tag\":\"mate\",\"ridge\":521,\"a\":64,\"owners\":[41,44,46,47]},{\"tag\":\"mate\",\"ridge\":524,\"a\":13,\"owners\":[77,79,88]},{\"tag\":\"mate\",\"ridge\":524,\"a\":29,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":524,\"a\":59,\"owners\":[79,88]},{\"tag\":\"mate\",\"ridge\":538,\"a\":77,\"owners\":[41]},{\"tag\":\"mate\",\"ridge\":554,\"a\":79,\"owners\":[44]},{\"tag\":\"mate\",\"ridge\":586,\"a\":46,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":650,\"a\":47,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":396,\"a\":63,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":424,\"a\":70,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":808,\"a\":71,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":904,\"a\":72,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[37,49,52,54,55],\"full_literals\":[-31,4,9,10,11,12]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[32,58],\"full_literals\":[-32,3,13]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-33,false,31],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-34,33,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-35,false,32],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-36,35,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-37,34,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-37,false,36],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":66,\"full_literals\":[-18,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":73,\"full_literals\":[-22,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":81,\"full_literals\":[-28,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":44,\"full_literals\":[-6,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":88,\"full_literals\":[-30,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":74,\"full_literals\":[-23,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":75,\"full_literals\":[-24,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":80,\"full_literals\":[-27,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":87,\"full_literals\":[-29,43]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-39,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-38,false,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-40,false,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-45,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-44,false,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0023\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-42,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-41,false,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-41,-47,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-43,false,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-48,-50,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0021\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-49,false,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-46,-51,52],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":29,\"owners\":[13,29,41,44,46,47,59,62,64,71,72,77,79,88]}]}"
  "p cnf 52 54\n-5 -3 0\n-13 -5 0\n-3 23 24 25 27 0\n-4 19 21 22 0\n-9 16 19 21 22 0\n-12 16 18 19 22 0\n-10 28 0\n-11 28 0\n-13 23 24 25 29 0\n-15 5 7 8 21 0\n-17 5 6 7 8 0\n-1 25 26 30 0\n-2 30 0\n-14 26 30 0\n-25 5 0\n-26 6 0\n-7 0\n-8 0\n-16 0\n-19 0\n-20 30 0\n-21 0\n-31 4 9 10 11 12 0\n-32 3 13 0\n-33 31 0\n-34 33 0\n-35 32 0\n-36 35 0\n-37 34 0\n-37 36 0\n37 0\n-18 38 0\n-22 39 0\n-28 40 0\n-6 41 0\n-30 41 0\n-23 42 0\n-24 42 0\n-27 42 0\n-29 43 0\n-39 44 0\n-38 44 0\n-40 45 0\n-45 46 0\n-44 46 0\n-42 47 0\n-41 48 0\n-41 -47 49 0\n-43 50 0\n-48 -50 51 0\n-49 51 0\n-46 -51 52 0\n-52 0\n1 2 5 6 7 8 14 15 17 20 21 25 26 30 0\n"
  "55 34 0 31 29 0\n56 36 0 31 30 0\n57 33 0 55 26 0\n58 35 0 56 28 0\n59 31 0 57 25 0\n60 32 0 58 27 0\n61 1 2 5 6 14 15 17 20 25 26 30 0 17 18 22 54 0\n62 46 0 22 20 19 59 44 45 43 41 42 34 33 32 7 8 4 5 6 23 0\n63 -51 0 62 53 52 0\n64 -49 0 63 51 0\n65 -5 0 60 1 2 24 0\n66 -15 0 65 17 18 22 10 0\n67 -25 0 65 15 0\n68 26 30 2 14 17 20 6 0 67 65 66 61 12 0\n69 41 0 18 17 65 35 36 16 11 13 21 14 68 0\n70 48 0 69 47 0\n71 -47 0 69 64 48 0\n72 -50 0 70 63 50 0\n73 -42 0 71 46 0\n74 -43 0 72 49 0\n75 -23 0 73 37 0\n76 -24 0 73 38 0\n77 -27 0 73 39 0\n78 -29 0 74 40 0\n79 -3 0 75 76 67 77 3 0\n80 -13 0 78 75 67 76 9 0\n81 0 79 80 60 24 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record003.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record003.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record003.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record003.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record003 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record003.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record003.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record003.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record003.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record003 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record003_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record003 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record003_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record003_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00021.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00021.record018
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "e61d43d0ecc6a3a35876c38ce1bb91744f1e24e9c6699666394e4b9714e565555355352d475c34cd4b4ad1b71394cd38cf0b32e2b1ae1b46c9b0ef0731d1725c570de0f43c8f13d8c1c8660bb11644d11c70962585314654348d0b46384c530ce0b0ac4709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db69b4924d34db4934da49249249a49b4d3692491249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record018 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record018 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record018.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record018.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record018.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 57), (facetIndex 63), (facetIndex 69), (facetIndex 70)]))
 (.leaf ([(facetIndex 29), (facetIndex 39), (facetIndex 71), (facetIndex 74)])))
 (.branch 3
 (.leaf ([(facetIndex 38), (facetIndex 42), (facetIndex 46), (facetIndex 65)]))
 (.leaf ([(facetIndex 35), (facetIndex 43), (facetIndex 45)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 27), (facetIndex 49), (facetIndex 51), (facetIndex 67)]))
 (.leaf ([(facetIndex 33), (facetIndex 50), (facetIndex 55), (facetIndex 58), (facetIndex 59)])))
 (.branch 7
 (.leaf ([(facetIndex 30), (facetIndex 44), (facetIndex 52), (facetIndex 68)]))
 (.branch 8
 (.leaf ([(facetIndex 25), (facetIndex 26), (facetIndex 28), (facetIndex 40)]))
 (.leaf ([(facetIndex 47), (facetIndex 48)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "10010064020000055005006454882363207120030500617477z19;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 32), (facetIndex 34), (facetIndex 37)]))
 (.leaf ([(facetIndex 73), (facetIndex 77)])))
 (.branch 3
 (.leaf ([(facetIndex 41), (facetIndex 66)]))
 (.leaf ([(facetIndex 72), (facetIndex 78)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 31), (facetIndex 53), (facetIndex 54), (facetIndex 56)]))
 (.leaf ([(facetIndex 75), (facetIndex 79), (facetIndex 80)])))
 (.branch 7
 (.leaf ([(facetIndex 36), (facetIndex 60), (facetIndex 61), (facetIndex 62), (facetIndex 64)]))
 (.leaf ([(facetIndex 76), (facetIndex 81)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "3dacfa0b0000861b60041200000000100060008z17;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [2, 3]
def grouped2_0007 : List Nat := [3]
def grouped2_0008 : List Nat := [4]
def grouped2_0009 : List Nat := [4, 5]
def grouped2_0010 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0011 : List Nat := [5]
def grouped2_0012 : List Nat := [6]
def grouped2_0013 : List Nat := [6, 7, 8]
def grouped2_0014 : List Nat := [7]
def grouped2_0015 : List Nat := [7, 8]
def grouped2_0016 : List Nat := [8]
def grouped3_0017 : List Nat := [0]
def grouped3_0018 : List Nat := [0, 1]
def grouped3_0019 : List Nat := [0, 1, 2, 3]
def grouped3_0021 : List Nat := [1]
def grouped3_0022 : List Nat := [2]
def grouped3_0023 : List Nat := [2, 3]
def grouped3_0024 : List Nat := [3]
def grouped3_0025 : List Nat := [4]
def grouped3_0026 : List Nat := [4, 5]
def grouped3_0027 : List Nat := [4, 5, 6, 7]
def grouped3_0028 : List Nat := [5]
def grouped3_0029 : List Nat := [6]
def grouped3_0030 : List Nat := [6, 7]
def grouped3_0031 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record018 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record018_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00021.record018" "{\"atoms\":[{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0030\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0030\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0027\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0027\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00021.record018" 73

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00021.record018" "{\"ridges\":[[13,196],[17,81],[18,81],[18,208],[33,193],[33,196],[35,49],[36,154],[38,530],[42,522],[43,530],[44,208],[45,81],[46,530],[50,196],[54,308],[55,208],[56,81],[57,145],[57,400],[58,196],[59,193],[59,196],[60,184],[63,400],[65,784],[68,208],[69,208],[70,400],[70,784],[75,150],[79,180],[80,208],[80,340]],\"owners\":[[42,522,[76],[4,28,38,40,73,77]],[35,49,[17,52,53,54,68],[5,29,43,60,61,62]],[38,530,[],[7,43,45,46,76,77]],[43,530,[77],[7,38,45,46,76]],[46,530,[76],[7,38,43,45,77]],[33,193,[18,66,68,69],[13,41,44,50,58,59]],[59,193,[18,41,44,66,68],[13,33,50,58,69]],[13,196,[72,75,78,79,80],[33,50,55,58,59]],[33,196,[78,79,80],[13,50,55,58,59,72,75]],[50,196,[75,79,80],[13,33,55,58,59,72,78]],[58,196,[72,75,80],[13,33,50,55,59,78,79]],[59,196,[72,75,78,79],[13,33,50,55,58,80]],[57,145,[18,36,44,60,64,68],[19,31,53,55,63,70]],[18,208,[75,79,80],[44,55,68,69]],[44,208,[79,80],[18,55,68,69,75]],[55,208,[],[18,44,68,69,75,79,80]],[68,208,[75,80],[18,44,55,69,79]],[69,208,[75,79],[18,44,55,68,80]],[80,208,[18,44,68],[55,69,75,79]],[57,400,[81],[19,63,69,70,80]],[63,400,[80],[19,57,69,70,81]],[70,400,[80],[19,57,63,69,81]],[65,784,[],[20,46,70,77,81]],[70,784,[77],[20,46,65,81]],[75,150,[31],[]],[36,154,[],[]],[79,180,[53],[]],[54,308,[],[]],[80,340,[56],[]],[60,184,[],[]]],\"edges\":[[39,[13,18,33,41,44,50,55,58,59,66,68,69,72,75,78,79,80]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00021.record018" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00021.record018\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-16,-6],[-16,-10],[-20,-16],[-23,-13],[-25,-16],[-25,-17],[-26,-17],[-31,-16],[-31,-17],[-32,-23],[-33,-5],[-33,-20],[-36,-24],[-40,-17],[-40,-24],[-41,-4],[-41,-19],[-41,-20],[-11,37],[-7,2,19,20,21,32],[-2,-3,-23],[-3,-14,-23],[-9],[-12,38],[-15,37],[-6,3,31,32,33],[-26,3,10,13,31,32],[-1,35,36,39,40,41],[-6,39,40,41],[-18,36,40,41],[-25,35,36,41],[-26,35,36,39,40],[-24,3,8,13,27,29,32],[-3,36,40,41],[-13,40,41],[-22],[-32,36,41],[-33,36,40],[-41,3,13,32],[-24,42],[-28,41],[-34,41],[-30],[-34,38],[-36,5],[-8],[-40,20],[-21],[-41,23],[-27],[-43,24,28,33,34],[-44,9,11,15,30],[-45,7,12,14],[-46,6,18,22,25,26],[-47,4,13,19,32],[-48,16,17],[-49,43],[-50,44],[-50,45],[-51,49,50],[-52,49],[-52,50],[-53,46],[-54,48],[-55,47],[-55,54],[-56,53],[-56,55],[-57,51],[-57,52,56],[57],[-38,58],[-10,59],[-31,59],[-35,60],[-39,60],[-5,61],[-20,61],[-23,61],[-62,36,40,41],[-36,62],[-40,62],[-41,62],[-29,63],[-37,64],[-42,64],[-58,65],[-60,66],[-59,66],[-66,67],[-65,67],[-61,-62,68],[-64,69],[-63,-64,70],[-70,71],[-68,71],[-68,-69,72],[-72,73],[-67,-71,73],[-73],[1,3,6,10,13,18,22,25,26,31,32,33,35,36,39,40,41]],\"atoms\":[{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":47,\"b\":33},{\"tag\":\"incompatible\",\"a\":47,\"b\":41},{\"tag\":\"incompatible\",\"a\":53,\"b\":47},{\"tag\":\"incompatible\",\"a\":56,\"b\":44},{\"tag\":\"incompatible\",\"a\":58,\"b\":47},{\"tag\":\"incompatible\",\"a\":58,\"b\":48},{\"tag\":\"incompatible\",\"a\":59,\"b\":48},{\"tag\":\"incompatible\",\"a\":66,\"b\":47},{\"tag\":\"incompatible\",\"a\":66,\"b\":48},{\"tag\":\"incompatible\",\"a\":68,\"b\":56},{\"tag\":\"incompatible\",\"a\":69,\"b\":31},{\"tag\":\"incompatible\",\"a\":69,\"b\":53},{\"tag\":\"incompatible\",\"a\":75,\"b\":57},{\"tag\":\"incompatible\",\"a\":79,\"b\":48},{\"tag\":\"incompatible\",\"a\":79,\"b\":57},{\"tag\":\"incompatible\",\"a\":80,\"b\":30},{\"tag\":\"incompatible\",\"a\":80,\"b\":52},{\"tag\":\"incompatible\",\"a\":80,\"b\":53},{\"tag\":\"mate\",\"ridge\":522,\"a\":42,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":49,\"a\":35,\"owners\":[17,52,53,54,68]},{\"tag\":\"three\",\"ridge\":81,\"vertices\":[17,18,56]},{\"tag\":\"three\",\"ridge\":81,\"vertices\":[18,45,56]},{\"tag\":\"mate\",\"ridge\":530,\"a\":38,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":530,\"a\":43,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":530,\"a\":46,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":193,\"a\":33,\"owners\":[18,66,68,69]},{\"tag\":\"mate\",\"ridge\":193,\"a\":59,\"owners\":[18,41,44,66,68]},{\"tag\":\"mate\",\"ridge\":196,\"a\":13,\"owners\":[72,75,78,79,80]},{\"tag\":\"mate\",\"ridge\":196,\"a\":33,\"owners\":[78,79,80]},{\"tag\":\"mate\",\"ridge\":196,\"a\":50,\"owners\":[75,79,80]},{\"tag\":\"mate\",\"ridge\":196,\"a\":58,\"owners\":[72,75,80]},{\"tag\":\"mate\",\"ridge\":196,\"a\":59,\"owners\":[72,75,78,79]},{\"tag\":\"mate\",\"ridge\":145,\"a\":57,\"owners\":[18,36,44,60,64,68]},{\"tag\":\"mate\",\"ridge\":208,\"a\":18,\"owners\":[75,79,80]},{\"tag\":\"mate\",\"ridge\":208,\"a\":44,\"owners\":[79,80]},{\"tag\":\"mate\",\"ridge\":208,\"a\":55,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":208,\"a\":68,\"owners\":[75,80]},{\"tag\":\"mate\",\"ridge\":208,\"a\":69,\"owners\":[75,79]},{\"tag\":\"mate\",\"ridge\":208,\"a\":80,\"owners\":[18,44,68]},{\"tag\":\"mate\",\"ridge\":400,\"a\":57,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":400,\"a\":63,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":400,\"a\":70,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":784,\"a\":65,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":784,\"a\":70,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":150,\"a\":75,\"owners\":[31]},{\"tag\":\"mate\",\"ridge\":154,\"a\":36,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":180,\"a\":79,\"owners\":[53]},{\"tag\":\"mate\",\"ridge\":308,\"a\":54,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":340,\"a\":80,\"owners\":[56]},{\"tag\":\"mate\",\"ridge\":184,\"a\":60,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[57,63,69,70],\"full_literals\":[-43,24,28,33,34]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[38,42,46,65],\"full_literals\":[-44,9,11,15,30]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[35,43,45],\"full_literals\":[-45,7,12,14]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[33,50,55,58,59],\"full_literals\":[-46,6,18,22,25,26]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[30,44,52,68],\"full_literals\":[-47,4,13,19,32]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[47,48],\"full_literals\":[-48,16,17]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-49,43,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-50,44,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-50,false,45],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-51,49,50],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-52,49,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-52,false,50],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-53,false,46],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-54,false,48],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-55,47,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-55,false,54],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-56,53,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-56,false,55],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-57,51,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-57,52,56],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":77,\"full_literals\":[-38,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":41,\"full_literals\":[-10,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":66,\"full_literals\":[-31,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":72,\"full_literals\":[-35,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":78,\"full_literals\":[-39,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":31,\"full_literals\":[-5,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":53,\"full_literals\":[-20,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":56,\"full_literals\":[-23,61]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[75,79,80],\"full_literals\":[-62,36,40,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":75,\"full_literals\":[-36,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":79,\"full_literals\":[-40,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":80,\"full_literals\":[-41,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":64,\"full_literals\":[-29,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":76,\"full_literals\":[-37,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":81,\"full_literals\":[-42,64]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-58,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0023\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-60,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-59,false,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-66,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-65,false,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-61,-62,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0029\",\"right_name\":\"grouped3_0031\",\"joined_name\":\"grouped3_0030\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-64,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0029\",\"right_name\":\"grouped3_0031\",\"joined_name\":\"grouped3_0030\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-63,-64,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0026\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0027\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-70,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0026\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0027\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-68,false,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0026\",\"right_name\":\"grouped3_0030\",\"joined_name\":\"grouped3_0027\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-68,-69,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-72,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-67,-71,73],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":39,\"owners\":[13,18,33,41,44,50,55,58,59,66,68,69,72,75,78,79,80]}]}"
  "p cnf 73 101\n-16 -6 0\n-16 -10 0\n-20 -16 0\n-23 -13 0\n-25 -16 0\n-25 -17 0\n-26 -17 0\n-31 -16 0\n-31 -17 0\n-32 -23 0\n-33 -5 0\n-33 -20 0\n-36 -24 0\n-40 -17 0\n-40 -24 0\n-41 -4 0\n-41 -19 0\n-41 -20 0\n-11 37 0\n-7 2 19 20 21 32 0\n-2 -3 -23 0\n-3 -14 -23 0\n-9 0\n-12 38 0\n-15 37 0\n-6 3 31 32 33 0\n-26 3 10 13 31 32 0\n-1 35 36 39 40 41 0\n-6 39 40 41 0\n-18 36 40 41 0\n-25 35 36 41 0\n-26 35 36 39 40 0\n-24 3 8 13 27 29 32 0\n-3 36 40 41 0\n-13 40 41 0\n-22 0\n-32 36 41 0\n-33 36 40 0\n-41 3 13 32 0\n-24 42 0\n-28 41 0\n-34 41 0\n-30 0\n-34 38 0\n-36 5 0\n-8 0\n-40 20 0\n-21 0\n-41 23 0\n-27 0\n-43 24 28 33 34 0\n-44 9 11 15 30 0\n-45 7 12 14 0\n-46 6 18 22 25 26 0\n-47 4 13 19 32 0\n-48 16 17 0\n-49 43 0\n-50 44 0\n-50 45 0\n-51 49 50 0\n-52 49 0\n-52 50 0\n-53 46 0\n-54 48 0\n-55 47 0\n-55 54 0\n-56 53 0\n-56 55 0\n-57 51 0\n-57 52 56 0\n57 0\n-38 58 0\n-10 59 0\n-31 59 0\n-35 60 0\n-39 60 0\n-5 61 0\n-20 61 0\n-23 61 0\n-62 36 40 41 0\n-36 62 0\n-40 62 0\n-41 62 0\n-29 63 0\n-37 64 0\n-42 64 0\n-58 65 0\n-60 66 0\n-59 66 0\n-66 67 0\n-65 67 0\n-61 -62 68 0\n-64 69 0\n-63 -64 70 0\n-70 71 0\n-68 71 0\n-68 -69 72 0\n-72 73 0\n-67 -71 73 0\n-73 0\n1 3 6 10 13 18 22 25 26 31 32 33 35 36 39 40 41 0\n"
  "102 -44 11 15 0 23 43 52 0\n103 -46 6 18 25 26 0 36 54 0\n104 51 0 71 69 0\n105 -72 0 100 98 0\n106 1 3 6 10 13 18 25 26 31 32 33 35 36 39 40 41 0 36 101 0\n107 62 66 0 89 74 73 88 76 75 81 82 83 28 32 31 29 30 34 38 35 37 106 0\n108 -36 28 67 0 105 104 90 107 91 87 72 44 13 45 11 77 51 92 57 97 60 93 58 85 19 25 102 0\n109 41 67 0 71 90 107 91 87 72 44 41 108 80 14 15 47 3 12 56 51 64 57 66 61 68 70 0\n110 67 0 48 71 91 87 72 24 109 16 17 18 49 4 10 55 39 65 21 22 68 20 70 53 62 59 0\n111 -71 0 110 100 99 0\n112 -70 0 111 95 0\n113 -68 0 111 96 0\n114 -62 0 113 92 77 78 79 45 47 49 80 0\n115 -36 0 114 81 0\n116 -40 0 114 82 0\n117 -41 0 114 83 0\n118 -32 0 115 117 37 0\n119 -18 0 115 116 117 30 0\n120 -3 0 115 116 117 34 0\n121 -33 0 115 116 38 0\n122 -13 0 116 117 35 0\n123 -28 0 117 41 0\n124 -34 0 117 42 0\n125 -24 0 118 122 50 120 46 112 33 40 84 86 94 0\n126 -43 0 125 121 123 124 51 0\n127 -49 0 126 57 0\n128 -52 0 127 61 0\n129 56 0 128 71 70 0\n130 53 0 129 67 0\n131 55 0 129 68 0\n132 46 0 130 63 0\n133 54 0 131 66 0\n134 48 0 133 64 0\n135 -16 0 119 132 118 122 120 1 2 5 8 103 27 0\n136 17 0 135 134 56 0\n137 -25 0 136 6 0\n138 -26 0 136 7 0\n139 -31 0 136 9 0\n140 6 0 138 132 137 119 103 0\n141 0 140 139 120 118 121 26 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record018.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record018.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record018.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record018.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record018 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record018.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record018.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record018.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record018.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record018 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record018_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record018_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record018_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record018_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record018_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record018_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record018_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record018 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record018_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record018_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00021.record018_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00021.record018
