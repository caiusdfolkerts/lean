module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow29Part00020Data
public import GraphInputsRow29Part00020Frames
public import GraphInputsRow29Part00020Leaves
public import GraphInputsRow29Part00020Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00020.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record001
def vertexColumn : Fields := ⟨10, hexnat% "3e0f4368ba358b6364d332c9b16c5713cb8acaaaa6a3a8da2e96639956359362d86e0fbc1e8791d46d1745b1d26c9ca6a9c669996559365392e745c9555355352d70d9354d8b52d4745d0f6c3a8d5334d332ce8b92ccb8acab26c5b0ed4731d2729d1725c570dc4f5505c3485a1584e0b81ec86a18a5254542d074a324c2b06c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6db6d36db69b6936934db6db49b6db6d269b6d24934d34db4924da492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨86, by decide⟩, ⟨93, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40080c0202088e98800000", hexnat% "60000000000000400000", hexnat% "200000000020103000000", 18471795346636800, hexnat% "400000100400004000000", hexnat% "200000000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "60000043e08c94c00000", 8796227239936, hexnat% "80c0200000000000000", hexnat% "200400000100000001000000", 2211941711872, hexnat% "4200000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "60000341a08494c00000", 8830586978304, hexnat% "80c0002000000000000", hexnat% "200400000000400001000000", 2211941711872, hexnat% "4200000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4260000140620783400000", 549898420224, hexnat% "400000000000014000000", hexnat% "200000080001800000000000", hexnat% "8040000080800000000", 144678138029277184]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4260000140628703400000", hexnat% "400000000000014000000", hexnat% "200000080001800000000000", 2290089984, hexnat% "8040000080800000000", 144678138029277184]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2600000412a8d9ac00000", hexnat% "4000040000000200000000", hexnat% "8080202000000000000", 72268700354347008, hexnat% "200400000000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "460000140e2071fc00000", hexnat% "4200000000000000000000", 551903297536, hexnat% "200000080001000000000000", hexnat% "8040000080800000000", 144678138029277184]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6000004022050c400000", 144959613274423296, 9345848836096, hexnat% "4600000000000001000000", hexnat% "200000000100c00000000000", hexnat% "80c0000000800000000", 10779361280]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c10 c3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c11 c2
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c12 c1
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c13 c0
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record001_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00020.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00020.record008
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record008
def vertexColumn : Fields := ⟨10, hexnat% "f4368d6178b91749b16c5713c1f2e25ca6a5a95a4e87a398761b89e1783ef0761b8791d46d174571c66994e6c5a9665594e5554d54d475a362d4b51d2743db0ea398d6338d5334d331ce8b8ad2b46c9b0ecc729c6715c3723f60ca0d4348c6198961582e07b21c26294a5192542d074930ac1b21c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "69b6db6db6db6d249269b6db4d36db69b69249b6db4db492492491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨39, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨54, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨70, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨94, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "5400040c081fe000000", hexnat% "3a000000000000000000", hexnat% "400000000000000000000000", 11529496529635115008, 1688901399871488]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400000400000000002000000", 11529215071838273536, hexnat% "28000000000030000000", 1759255111663616, hexnat% "4000040008048000000", 422216760033280, hexnat% "13000000000004000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c1 c0
  c2
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record008_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record008_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00020.record008

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00020.record011
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record011
def vertexColumn : Fields := ⟨10, hexnat% "f41d85e364d52d45d32c5b15c3713c1f2e25c96a3a95a3693a1eac6998d61d8ce1b89e1783ef0761b8791d46d174571e2729aa5994e745b172599565c569595555355351d70da362d4b51d2743db0ea398d6338d5334d331cd2b2ad1b0ee8791cc789c6725c570dc8fd82643489a198560b81ec8529464998942d0749322c2b06c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b69b6db6db6db4db49349269b6db69a4da4db6db6da4926db6d36924db492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨37, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨87, by decide⟩, ⟨102, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "eb0018000700185800000", hexnat% "8040000000002002000000", 1729663732021198848, 25773998080, hexnat% "4040000000000000000", hexnat% "40000000000000800000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40000200059001f00788000000", hexnat% "800000800000004000000", hexnat% "4000000002001000000", hexnat% "80a0000000000000000000", hexnat% "10000000000000c00000", hexnat% "440000000000002000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2f0008000900785c00000", hexnat% "10000600000000000", hexnat% "800000800000008000000", hexnat% "8400000000002002000000", hexnat% "41001000000000000", hexnat% "40000004000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "210000000800780400000", hexnat% "4041000000000000000", hexnat% "40000800000800000000000000", hexnat% "18000700000000000", hexnat% "80a0000000000000000000", 281475186425856, hexnat% "440000000002003000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c5 c0
  c6
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record011_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record011_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record011_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record011_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record011_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record011_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record011_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record011_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record011_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00020.record011

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00020.record010
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3d0ba2d8d9174cb26c3713c1f2e25cacaaaa6a3a8da1e966558d64d8763386e2785e0fbc1d86e1e4751b45d15c729aa719a6539d172599565554d54d475c362d4b51d2743db0ea398d6338d5334d331ce8b8acab0ed4731d2719d1725c570dc8fd8164550d2268661582e07b21a2629265254542d0749322c2b06c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36d26db6db6da69269a4934db6da4d369a4d369249b6db4da493692492249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record010 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record010 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record010.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record010.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record010.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 7
 (.branch 3
 (.branch 1
 (.leaf ([(facetIndex 51), (facetIndex 57), (facetIndex 94)]))
 (.branch 2
 (.leaf ([(facetIndex 62), (facetIndex 67), (facetIndex 69), (facetIndex 98)]))
 (.leaf ([(facetIndex 60), (facetIndex 95)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 66), (facetIndex 68), (facetIndex 100)]))
 (.leaf ([(facetIndex 44), (facetIndex 85), (facetIndex 86)])))
 (.branch 6
 (.leaf ([(facetIndex 87), (facetIndex 88), (facetIndex 99)]))
 (.leaf ([(facetIndex 41), (facetIndex 43), (facetIndex 90)])))))
 (.branch 10
 (.branch 8
 (.leaf ([(facetIndex 37), (facetIndex 38), (facetIndex 83), (facetIndex 92)]))
 (.branch 9
 (.leaf ([(facetIndex 31), (facetIndex 77)]))
 (.leaf ([(facetIndex 52), (facetIndex 79), (facetIndex 91)]))))
 (.branch 12
 (.branch 11
 (.leaf ([(facetIndex 32), (facetIndex 65), (facetIndex 89)]))
 (.leaf ([(facetIndex 54), (facetIndex 93)])))
 (.branch 13
 (.leaf ([(facetIndex 40), (facetIndex 45), (facetIndex 59), (facetIndex 70), (facetIndex 72)]))
 (.leaf ([(facetIndex 42)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "3510020b796a5544070009080000c0c1313a00102c0000b09000000c46d6c0770000a8z1f;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 14
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1, 2]
def grouped3_0002 : List Nat := [0, 1, 2, 3, 4, 5, 6]
def grouped3_0004 : List Nat := [1]
def grouped3_0005 : List Nat := [1, 2]
def grouped3_0006 : List Nat := [2]
def grouped3_0007 : List Nat := [3]
def grouped3_0008 : List Nat := [3, 4]
def grouped3_0009 : List Nat := [3, 4, 5, 6]
def grouped3_0010 : List Nat := [4]
def grouped3_0011 : List Nat := [5]
def grouped3_0012 : List Nat := [5, 6]
def grouped3_0013 : List Nat := [6]
def grouped3_0014 : List Nat := [7]
def grouped3_0015 : List Nat := [7, 8, 9]
def grouped3_0016 : List Nat := [7, 8, 9, 10, 11, 12, 13]
def grouped3_0017 : List Nat := [8]
def grouped3_0018 : List Nat := [8, 9]
def grouped3_0019 : List Nat := [9]
def grouped3_0020 : List Nat := [10]
def grouped3_0021 : List Nat := [10, 11]
def grouped3_0022 : List Nat := [10, 11, 12, 13]
def grouped3_0023 : List Nat := [11]
def grouped3_0024 : List Nat := [12]
def grouped3_0025 : List Nat := [12, 13]
def grouped3_0026 : List Nat := [13]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record010 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record010_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00020.record010" "{\"atoms\":[{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":11},{\"tag\":\"group\",\"kind\":3,\"index\":12},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0005\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0025\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00020.record010" 64

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00020.record010" "{\"ridges\":[[13,648],[20,194],[20,208],[23,608],[31,197],[36,648],[39,194],[39,208],[41,194],[41,225],[44,674],[45,579],[45,704],[54,197],[59,581],[61,648],[63,648],[66,449],[67,593],[67,704],[70,225],[70,704],[71,608],[72,449],[72,704],[77,204],[80,194],[80,208],[84,194],[84,208],[85,232],[88,586],[88,704],[90,704],[93,204],[94,588],[97,608],[98,600],[99,232],[99,704],[100,704],[100,912]],\"owners\":[[13,648,[87,88,98,99],[36,61,63]],[36,648,[98,99],[13,61,63,87,88]],[61,648,[87,88,99],[13,36,63,98]],[63,648,[88,98],[13,36,61,87,99]],[20,194,[31,41,45,77,85,88,90],[39,80,84]],[39,194,[77,85,88,90],[20,31,41,45,80,84]],[41,194,[20,77,80,84,88],[31,39,45,85,90]],[80,194,[41,45,85,88,90],[20,31,39,77,84]],[84,194,[31,41,45,90],[20,39,77,80,85,88]],[20,208,[54,66,67,93,98,100],[39,80,84]],[39,208,[93,98,100],[20,54,66,67,80,84]],[80,208,[66,67,98,100],[20,39,54,84,93]],[84,208,[54,66,67,100],[20,39,80,93,98]],[23,608,[43,57,70,86,90,94,99],[71,97]],[71,608,[86,90,94,99],[23,43,57,70,97]],[97,608,[43,70,86,90,99],[23,57,71,94]],[31,197,[54],[]],[54,197,[31],[]],[41,225,[70],[]],[70,225,[41],[]],[45,579,[43],[]],[44,674,[87,90],[]],[45,704,[98,99,100],[67,70,72,88,90]],[67,704,[88,90,99],[45,70,72,98,100]],[70,704,[88,98,100],[45,67,72,90,99]],[72,704,[88,90,98,99],[45,67,70,100]],[88,704,[67,70,72,100],[45,90,98,99]],[90,704,[67,72,98,100],[45,70,88,99]],[99,704,[45,67,72,100],[70,88,90,98]],[100,704,[45,70,88,90,99],[67,72,98]],[59,581,[57],[]],[66,449,[72],[]],[72,449,[66],[]],[67,593,[68],[]],[100,912,[69],[]],[77,204,[93],[]],[93,204,[77],[]],[85,232,[99],[]],[99,232,[85],[]],[88,586,[86],[]],[94,588,[],[]],[98,600,[],[]]],\"edges\":[[39,[20,31,39,41,45,54,66,67,70,72,77,80,84,85,88,90,93,98,99,100]],[41,[23,43,45,57,59,67,68,70,71,72,86,88,90,94,97,98,99,100]],[43,[13,36,44,45,61,63,67,69,70,72,87,88,90,98,99,100]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00020.record010" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00020.record010\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,28,29,34,35],[-5,34,35],[-14,28,29,35],[-15,29,34],[-2,4,7,10,23,26,29,30],[-6,23,26,29,30],[-7,2,23,24,25,29],[-24,7,10,26,29,30],[-25,4,7,10,30],[-2,11,16,17,31,34,36],[-6,31,34,36],[-24,16,17,34,36],[-25,11,16,17,36],[-3,8,12,20,27,30,32,35],[-21,27,30,32,35],[-33,8,20,27,30,35],[-4,11],[-11,4],[-7,20],[-20,7],[-10,8],[-9,28,30],[-10,34,35,36],[-17,29,30,35],[-20,29,34,36],[-22,29,30,34,35],[-29,17,20,22,36],[-30,17,22,34,36],[-35,10,17,22,36],[-36,10,20,29,30,35],[-13,12],[-16,22],[-22,16],[-17,18],[-36,19],[-23,31],[-31,23],[-26,35],[-35,26],[-29,27],[-32],[-34],[-12,37],[-17,38],[-19,38],[-16,39],[-18,39],[-36,39],[-26,40],[-27,40],[-28,41],[-29,41],[-35,41],[-7,42],[-8,42],[-30,42],[-43,4,23],[-4,43],[-23,43],[-11,44],[-31,44],[-10,45],[-20,45],[-22,45],[-38,46],[-46,47],[-37,47],[-40,48],[-39,48],[-39,-40,49],[-42,50],[-41,50],[-50,51],[-48,51],[-48,-50,52],[-49,-50,53],[-51,54],[-52,55],[-53,56],[-47,54],[-47,-51,55],[-47,-52,56],[-43,57],[-57,58],[-44,59],[-45,60],[-60,61],[-59,61],[-61,62],[-58,-61,63],[-54,-63,64],[-55,-62,64],[-56,64],[-64],[2,4,6,7,10,11,16,17,20,22,23,24,25,26,29,30,31,34,35,36],[3,8,10,12,13,17,18,20,21,22,27,29,30,32,33,34,35,36],[1,5,9,10,14,15,17,19,20,22,28,29,30,34,35,36]],\"atoms\":[{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":11,\"kind\":3},{\"tag\":\"group\",\"index\":12,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":648,\"a\":13,\"owners\":[87,88,98,99]},{\"tag\":\"mate\",\"ridge\":648,\"a\":36,\"owners\":[98,99]},{\"tag\":\"mate\",\"ridge\":648,\"a\":61,\"owners\":[87,88,99]},{\"tag\":\"mate\",\"ridge\":648,\"a\":63,\"owners\":[88,98]},{\"tag\":\"mate\",\"ridge\":194,\"a\":20,\"owners\":[31,41,45,77,85,88,90]},{\"tag\":\"mate\",\"ridge\":194,\"a\":39,\"owners\":[77,85,88,90]},{\"tag\":\"mate\",\"ridge\":194,\"a\":41,\"owners\":[20,77,80,84,88]},{\"tag\":\"mate\",\"ridge\":194,\"a\":80,\"owners\":[41,45,85,88,90]},{\"tag\":\"mate\",\"ridge\":194,\"a\":84,\"owners\":[31,41,45,90]},{\"tag\":\"mate\",\"ridge\":208,\"a\":20,\"owners\":[54,66,67,93,98,100]},{\"tag\":\"mate\",\"ridge\":208,\"a\":39,\"owners\":[93,98,100]},{\"tag\":\"mate\",\"ridge\":208,\"a\":80,\"owners\":[66,67,98,100]},{\"tag\":\"mate\",\"ridge\":208,\"a\":84,\"owners\":[54,66,67,100]},{\"tag\":\"mate\",\"ridge\":608,\"a\":23,\"owners\":[43,57,70,86,90,94,99]},{\"tag\":\"mate\",\"ridge\":608,\"a\":71,\"owners\":[86,90,94,99]},{\"tag\":\"mate\",\"ridge\":608,\"a\":97,\"owners\":[43,70,86,90,99]},{\"tag\":\"mate\",\"ridge\":197,\"a\":31,\"owners\":[54]},{\"tag\":\"mate\",\"ridge\":197,\"a\":54,\"owners\":[31]},{\"tag\":\"mate\",\"ridge\":225,\"a\":41,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":225,\"a\":70,\"owners\":[41]},{\"tag\":\"mate\",\"ridge\":579,\"a\":45,\"owners\":[43]},{\"tag\":\"mate\",\"ridge\":674,\"a\":44,\"owners\":[87,90]},{\"tag\":\"mate\",\"ridge\":704,\"a\":45,\"owners\":[98,99,100]},{\"tag\":\"mate\",\"ridge\":704,\"a\":67,\"owners\":[88,90,99]},{\"tag\":\"mate\",\"ridge\":704,\"a\":70,\"owners\":[88,98,100]},{\"tag\":\"mate\",\"ridge\":704,\"a\":72,\"owners\":[88,90,98,99]},{\"tag\":\"mate\",\"ridge\":704,\"a\":88,\"owners\":[67,70,72,100]},{\"tag\":\"mate\",\"ridge\":704,\"a\":90,\"owners\":[67,72,98,100]},{\"tag\":\"mate\",\"ridge\":704,\"a\":99,\"owners\":[45,67,72,100]},{\"tag\":\"mate\",\"ridge\":704,\"a\":100,\"owners\":[45,70,88,90,99]},{\"tag\":\"mate\",\"ridge\":581,\"a\":59,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":449,\"a\":66,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":449,\"a\":72,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":593,\"a\":67,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":912,\"a\":100,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":204,\"a\":77,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":204,\"a\":93,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":232,\"a\":85,\"owners\":[99]},{\"tag\":\"mate\",\"ridge\":232,\"a\":99,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":586,\"a\":88,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":588,\"a\":94,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":600,\"a\":98,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":57,\"full_literals\":[-12,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":67,\"full_literals\":[-17,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":69,\"full_literals\":[-19,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":66,\"full_literals\":[-16,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":68,\"full_literals\":[-18,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":100,\"full_literals\":[-36,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":85,\"full_literals\":[-26,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":86,\"full_literals\":[-27,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":87,\"full_literals\":[-28,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":88,\"full_literals\":[-29,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":99,\"full_literals\":[-35,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":41,\"full_literals\":[-7,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":43,\"full_literals\":[-8,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":90,\"full_literals\":[-30,42]},{\"tag\":\"group_or\",\"kind\":3,\"index\":8,\"members\":[31,77],\"full_literals\":[-43,4,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":31,\"full_literals\":[-4,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":77,\"full_literals\":[-23,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":11,\"member\":54,\"full_literals\":[-11,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":11,\"member\":93,\"full_literals\":[-31,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":12,\"member\":45,\"full_literals\":[-10,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":12,\"member\":70,\"full_literals\":[-20,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":12,\"member\":72,\"full_literals\":[-22,45]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0004\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0005\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-38,false,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-46,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-37,false,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-40,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-39,false,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-39,-40,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-42,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-41,false,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-50,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-48,false,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-48,-50,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0009\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-49,-50,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-51,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-52,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-53,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-47,false,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-47,-51,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-47,-52,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-43,false,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-57,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-44,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[12],\"right\":[13],\"left_name\":\"grouped3_0024\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0025\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-45,false,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[10,11],\"right\":[12,13],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-60,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[10,11],\"right\":[12,13],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-59,false,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7,8,9],\"right\":[10,11,12,13],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-61,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7,8,9],\"right\":[10,11,12,13],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-58,-61,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6],\"right\":[7,8,9,10,11,12,13],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-54,-63,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6],\"right\":[7,8,9,10,11,12,13],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-55,-62,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6],\"right\":[7,8,9,10,11,12,13],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-56,false,64],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":39,\"owners\":[20,31,39,41,45,54,66,67,70,72,77,80,84,85,88,90,93,98,99,100]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[23,43,45,57,59,67,68,70,71,72,86,88,90,94,97,98,99,100]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[13,36,44,45,61,63,67,69,70,72,87,88,90,98,99,100]}]}"
  "p cnf 64 97\n-1 28 29 34 35 0\n-5 34 35 0\n-14 28 29 35 0\n-15 29 34 0\n-2 4 7 10 23 26 29 30 0\n-6 23 26 29 30 0\n-7 2 23 24 25 29 0\n-24 7 10 26 29 30 0\n-25 4 7 10 30 0\n-2 11 16 17 31 34 36 0\n-6 31 34 36 0\n-24 16 17 34 36 0\n-25 11 16 17 36 0\n-3 8 12 20 27 30 32 35 0\n-21 27 30 32 35 0\n-33 8 20 27 30 35 0\n-4 11 0\n-11 4 0\n-7 20 0\n-20 7 0\n-10 8 0\n-9 28 30 0\n-10 34 35 36 0\n-17 29 30 35 0\n-20 29 34 36 0\n-22 29 30 34 35 0\n-29 17 20 22 36 0\n-30 17 22 34 36 0\n-35 10 17 22 36 0\n-36 10 20 29 30 35 0\n-13 12 0\n-16 22 0\n-22 16 0\n-17 18 0\n-36 19 0\n-23 31 0\n-31 23 0\n-26 35 0\n-35 26 0\n-29 27 0\n-32 0\n-34 0\n-12 37 0\n-17 38 0\n-19 38 0\n-16 39 0\n-18 39 0\n-36 39 0\n-26 40 0\n-27 40 0\n-28 41 0\n-29 41 0\n-35 41 0\n-7 42 0\n-8 42 0\n-30 42 0\n-43 4 23 0\n-4 43 0\n-23 43 0\n-11 44 0\n-31 44 0\n-10 45 0\n-20 45 0\n-22 45 0\n-38 46 0\n-46 47 0\n-37 47 0\n-40 48 0\n-39 48 0\n-39 -40 49 0\n-42 50 0\n-41 50 0\n-50 51 0\n-48 51 0\n-48 -50 52 0\n-49 -50 53 0\n-51 54 0\n-52 55 0\n-53 56 0\n-47 54 0\n-47 -51 55 0\n-47 -52 56 0\n-43 57 0\n-57 58 0\n-44 59 0\n-45 60 0\n-60 61 0\n-59 61 0\n-61 62 0\n-58 -61 63 0\n-54 -63 64 0\n-55 -62 64 0\n-56 64 0\n-64 0\n2 4 6 7 10 11 16 17 20 22 23 24 25 26 29 30 31 34 35 36 0\n3 8 10 12 13 17 18 20 21 22 27 29 30 32 33 34 35 36 0\n1 5 9 10 14 15 17 19 20 22 28 29 30 34 35 36 0\n"
  "98 -56 0 94 93 0\n99 -53 0 98 79 0\n100 2 4 6 7 10 11 16 17 20 22 23 24 25 26 29 30 31 35 36 0 42 95 0\n101 3 8 10 12 13 17 18 20 21 22 27 29 30 33 35 36 0 41 42 96 0\n102 1 5 9 10 14 15 17 19 20 22 28 29 30 35 36 0 42 97 0\n103 54 0 42 41 77 80 73 74 66 67 71 72 68 69 65 43 54 55 56 52 53 50 47 48 44 31 20 21 15 16 26 14 101 0\n104 -63 0 103 94 91 0\n105 51 43 0 42 59 37 58 18 73 74 71 72 68 69 54 55 56 52 53 49 46 48 20 21 8 24 26 9 6 5 100 0\n106 50 38 0 42 45 35 44 71 72 54 55 56 51 52 53 20 21 26 1 3 22 4 2 102 0\n107 43 55 0 42 78 58 59 18 37 105 81 66 65 44 45 35 11 106 75 68 69 49 50 46 39 40 33 10 12 13 23 25 28 7 100 0\n108 -43 0 104 83 84 90 88 85 60 61 17 36 57 0\n109 -4 0 108 58 0\n110 -23 0 108 59 0\n111 55 0 108 107 0\n112 -11 0 109 18 0\n113 -31 0 110 37 0\n114 -62 0 111 94 92 0\n115 -61 0 114 89 0\n116 -60 0 115 87 0\n117 -45 0 116 86 0\n118 -10 0 117 62 0\n119 -20 0 117 63 0\n120 -22 0 117 64 0\n121 -7 0 119 19 0\n122 -16 0 120 32 0\n123 29 30 35 36 0 42 113 122 110 120 119 112 118 121 109 9 38 11 5 24 8 100 0\n124 -29 36 49 0 120 119 27 40 34 50 47 70 0\n125 -17 -50 0 98 34 44 47 65 69 66 75 82 0\n126 36 -50 0 99 118 42 120 125 76 124 29 28 123 0\n127 -50 0 98 126 35 48 45 69 65 75 66 82 0\n128 -42 0 127 71 0\n129 -41 0 127 72 0\n130 -30 0 128 56 0\n131 -29 0 129 52 0\n132 -35 0 129 53 0\n133 -36 0 131 119 118 130 132 30 0\n134 0 132 133 131 130 123 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record010.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record010.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record010.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record010.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record010 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record010.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record010.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record010.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record010.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record010 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record010_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record010 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record010_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record010_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00020.record010

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00020.record019
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "bc358b6364d52745b15cb8ad2aca723c96a3a8da598b61d94e4b8ae1b89ee8761d46b19c789d25a95a719a665956745c966559715955558d4b51d54d4b4ad1b51d2745da8e6358e9394e332cc7352d2b2ac6b16d4749ca719c9715c3743c8f13c2fd81645305c2685a198561381ec86a1a44994950d074a324c8b06c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b69b49b6db69349b49269b6db4db4d36db6936924da6d36d34d2492492249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record019 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record019 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record019.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record019.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record019.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ([(facetIndex 66), (facetIndex 68), (facetIndex 72), (facetIndex 99)]))
 (.branch 2
 (.leaf ([(facetIndex 42), (facetIndex 89), (facetIndex 92)]))
 (.leaf ([(facetIndex 90), (facetIndex 93), (facetIndex 101)]))))
 (.branch 4
 (.leaf ([(facetIndex 36), (facetIndex 38), (facetIndex 52), (facetIndex 70), (facetIndex 87)]))
 (.branch 5
 (.leaf ([(facetIndex 58), (facetIndex 60), (facetIndex 100)]))
 (.leaf ([(facetIndex 34), (facetIndex 51), (facetIndex 81)])))))
 (.branch 9
 (.branch 7
 (.leaf ([(facetIndex 39), (facetIndex 69), (facetIndex 88)]))
 (.branch 8
 (.leaf ([(facetIndex 57), (facetIndex 59), (facetIndex 97)]))
 (.leaf ([(facetIndex 56), (facetIndex 80)]))))
 (.branch 10
 (.leaf ([(facetIndex 40), (facetIndex 84), (facetIndex 91), (facetIndex 96)]))
 (.branch 11
 (.leaf ([(facetIndex 43), (facetIndex 45), (facetIndex 55), (facetIndex 62), (facetIndex 65), (facetIndex 71)]))
 (.leaf ([(facetIndex 46), (facetIndex 64), (facetIndex 73), (facetIndex 75)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "24007900219216300900580000b0b0a36000ab0a047478a00350000ba0a109630305z22;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 12
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1, 2]
def grouped3_0002 : List Nat := [0, 1, 2, 3, 4, 5]
def grouped3_0004 : List Nat := [1]
def grouped3_0005 : List Nat := [1, 2]
def grouped3_0006 : List Nat := [2]
def grouped3_0007 : List Nat := [3]
def grouped3_0008 : List Nat := [3, 4, 5]
def grouped3_0009 : List Nat := [4]
def grouped3_0010 : List Nat := [4, 5]
def grouped3_0011 : List Nat := [5]
def grouped3_0012 : List Nat := [6]
def grouped3_0013 : List Nat := [6, 7, 8]
def grouped3_0014 : List Nat := [6, 7, 8, 9, 10, 11]
def grouped3_0015 : List Nat := [7]
def grouped3_0016 : List Nat := [7, 8]
def grouped3_0017 : List Nat := [8]
def grouped3_0018 : List Nat := [9]
def grouped3_0019 : List Nat := [9, 10, 11]
def grouped3_0020 : List Nat := [10]
def grouped3_0021 : List Nat := [10, 11]
def grouped3_0022 : List Nat := [11]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record019 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record019_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00020.record019" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group\",\"kind\":3,\"index\":10},{\"tag\":\"group\",\"kind\":3,\"index\":11},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0005\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00020.record019" 68

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00020.record019" "{\"ridges\":[[11,656],[12,672],[13,769],[23,832],[43,579],[44,656],[45,323],[46,579],[47,672],[55,113],[62,581],[63,769],[64,581],[65,337],[66,585],[67,656],[71,585],[72,904],[73,113],[74,672],[75,337],[76,769],[76,832],[77,672],[77,769],[90,592],[91,562],[92,592],[93,608],[97,788],[98,832],[99,712],[100,792],[101,592]],\"owners\":[[11,656,[91,92,99,101],[44,67,74]],[44,656,[99,101],[11,67,74,91,92]],[67,656,[91,92,101],[11,44,74,99]],[12,672,[91,93,101],[47,74,77]],[47,672,[101],[12,74,77,91,93]],[74,672,[93],[12,47,77,91,101]],[77,672,[91,93,101],[12,47,74]],[13,769,[60,64,68,71,72,75],[63,76,77]],[63,769,[68,71,72,75],[13,60,64,76,77]],[76,769,[60,68,72],[13,63,64,71,75,77]],[77,769,[60,64,68,71,75],[13,63,72,76]],[93,608,[23,62,73,76,96,98],[46,90,101]],[23,832,[64,71,75,97,100],[76,98]],[76,832,[97,100],[23,64,71,75,98]],[98,832,[71,75,100],[23,64,76,97]],[45,323,[34,39],[]],[55,113,[40,73],[]],[73,113,[40,55],[]],[91,562,[42,90],[]],[43,579,[46],[]],[46,579,[43],[]],[90,592,[59,66,75,97,99,100],[43,73,92,96,101]],[92,592,[59,66,73,75,96,97,100],[43,90,99,101]],[101,592,[43,59,66,75,97,100],[73,90,92,96,99]],[65,337,[58,75],[]],[75,337,[58,65],[]],[62,581,[59,64],[]],[64,581,[59,62],[]],[97,788,[60],[]],[66,585,[71],[]],[71,585,[66],[]],[100,792,[68],[]],[72,904,[],[]],[99,712,[],[]]],\"edges\":[[41,[23,43,46,59,62,64,66,71,73,75,76,90,92,93,96,97,98,99,100,101]],[43,[11,12,44,47,67,72,74,77,91,92,93,99,101]],[44,[13,23,60,63,64,68,71,72,75,76,77,97,98,100]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00020.record019" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00020.record019\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,33,34,39,41],[-10,39,41],[-23,33,34,41],[-2,33,35,41],[-13,41],[-28,35],[-31,33,35,41],[-3,17,20,24,25,26,29],[-19,24,25,26,29],[-30,17,24,26],[-31,17,20,24,25,29],[-35,4,18,27,30,36,38],[-4,20,25,29,37,40],[-30,37,40],[-38,25,29,40],[-11,5,6],[-14,7,27],[-27,7,14],[-33,8,32],[-9,12],[-12,9],[-32,16,22,29,37,39,40],[-34,16,22,27,29,36,37,40],[-41,9,16,22,29,37,40],[-21,15,29],[-29,15,21],[-18,16,20],[-20,16,18],[-37,17],[-22,25],[-25,22],[-40,24],[-26],[-39],[-22,42],[-24,42],[-8,43],[-34,43],[-32,44],[-35,44],[-41,44],[-15,45],[-17,45],[-40,45],[-5,46],[-6,47],[-16,48],[-37,48],[-7,49],[-36,49],[-50,9,11,14,18,21,25],[-9,50],[-14,50],[-18,50],[-21,50],[-25,50],[-51,12,20,27,29],[-12,51],[-20,51],[-27,51],[-29,51],[-44,52],[-43,52],[-52,53],[-42,-52,54],[-46,55],[-45,55],[-55,56],[-53,57],[-53,-56,58],[-54,58],[-54,-56,59],[-48,60],[-60,61],[-47,61],[-62,50,51],[-51,62],[-50,62],[-50,-51,63],[-62,64],[-63,65],[-49,64],[-49,-62,65],[-64,66],[-65,67],[-61,66],[-61,-64,67],[-57,-67,68],[-58,-66,68],[-59,68],[-68],[4,9,12,16,18,20,22,25,27,29,30,32,34,35,36,37,38,39,40,41],[1,2,10,13,23,26,28,31,33,34,35,39,41],[3,4,17,19,20,24,25,26,29,30,31,37,38,40]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group\",\"index\":10,\"kind\":3},{\"tag\":\"group\",\"index\":11,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":656,\"a\":11,\"owners\":[91,92,99,101]},{\"tag\":\"mate\",\"ridge\":656,\"a\":44,\"owners\":[99,101]},{\"tag\":\"mate\",\"ridge\":656,\"a\":67,\"owners\":[91,92,101]},{\"tag\":\"mate\",\"ridge\":672,\"a\":12,\"owners\":[91,93,101]},{\"tag\":\"mate\",\"ridge\":672,\"a\":47,\"owners\":[101]},{\"tag\":\"mate\",\"ridge\":672,\"a\":74,\"owners\":[93]},{\"tag\":\"mate\",\"ridge\":672,\"a\":77,\"owners\":[91,93,101]},{\"tag\":\"mate\",\"ridge\":769,\"a\":13,\"owners\":[60,64,68,71,72,75]},{\"tag\":\"mate\",\"ridge\":769,\"a\":63,\"owners\":[68,71,72,75]},{\"tag\":\"mate\",\"ridge\":769,\"a\":76,\"owners\":[60,68,72]},{\"tag\":\"mate\",\"ridge\":769,\"a\":77,\"owners\":[60,64,68,71,75]},{\"tag\":\"mate\",\"ridge\":608,\"a\":93,\"owners\":[23,62,73,76,96,98]},{\"tag\":\"mate\",\"ridge\":832,\"a\":23,\"owners\":[64,71,75,97,100]},{\"tag\":\"mate\",\"ridge\":832,\"a\":76,\"owners\":[97,100]},{\"tag\":\"mate\",\"ridge\":832,\"a\":98,\"owners\":[71,75,100]},{\"tag\":\"mate\",\"ridge\":323,\"a\":45,\"owners\":[34,39]},{\"tag\":\"mate\",\"ridge\":113,\"a\":55,\"owners\":[40,73]},{\"tag\":\"mate\",\"ridge\":113,\"a\":73,\"owners\":[40,55]},{\"tag\":\"mate\",\"ridge\":562,\"a\":91,\"owners\":[42,90]},{\"tag\":\"mate\",\"ridge\":579,\"a\":43,\"owners\":[46]},{\"tag\":\"mate\",\"ridge\":579,\"a\":46,\"owners\":[43]},{\"tag\":\"mate\",\"ridge\":592,\"a\":90,\"owners\":[59,66,75,97,99,100]},{\"tag\":\"mate\",\"ridge\":592,\"a\":92,\"owners\":[59,66,73,75,96,97,100]},{\"tag\":\"mate\",\"ridge\":592,\"a\":101,\"owners\":[43,59,66,75,97,100]},{\"tag\":\"mate\",\"ridge\":337,\"a\":65,\"owners\":[58,75]},{\"tag\":\"mate\",\"ridge\":337,\"a\":75,\"owners\":[58,65]},{\"tag\":\"mate\",\"ridge\":581,\"a\":62,\"owners\":[59,64]},{\"tag\":\"mate\",\"ridge\":581,\"a\":64,\"owners\":[59,62]},{\"tag\":\"mate\",\"ridge\":788,\"a\":97,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":585,\"a\":66,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":585,\"a\":71,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":792,\"a\":100,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":904,\"a\":72,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":712,\"a\":99,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":66,\"full_literals\":[-22,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":68,\"full_literals\":[-24,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":42,\"full_literals\":[-8,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":92,\"full_literals\":[-34,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":90,\"full_literals\":[-32,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":93,\"full_literals\":[-35,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":101,\"full_literals\":[-41,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":58,\"full_literals\":[-15,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":60,\"full_literals\":[-17,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":100,\"full_literals\":[-40,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":34,\"full_literals\":[-5,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":39,\"full_literals\":[-6,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":59,\"full_literals\":[-16,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":97,\"full_literals\":[-37,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":40,\"full_literals\":[-7,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":96,\"full_literals\":[-36,49]},{\"tag\":\"group_or\",\"kind\":3,\"index\":10,\"members\":[43,45,55,62,65,71],\"full_literals\":[-50,9,11,14,18,21,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":43,\"full_literals\":[-9,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":55,\"full_literals\":[-14,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":62,\"full_literals\":[-18,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":65,\"full_literals\":[-21,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":71,\"full_literals\":[-25,50]},{\"tag\":\"group_or\",\"kind\":3,\"index\":11,\"members\":[46,64,73,75],\"full_literals\":[-51,12,20,27,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":11,\"member\":46,\"full_literals\":[-12,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":11,\"member\":64,\"full_literals\":[-20,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":11,\"member\":73,\"full_literals\":[-27,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":11,\"member\":75,\"full_literals\":[-29,51]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0004\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0005\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-44,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0004\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0005\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-43,false,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-52,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-42,-52,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-46,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-45,false,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-55,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-53,false,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-53,-56,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-54,false,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-54,-56,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-48,false,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-60,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-47,false,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-62,50,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-51,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-50,false,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-50,-51,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-62,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-63,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-49,false,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-49,-62,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-64,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-65,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-61,false,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-61,-64,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-57,-67,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-58,-66,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-59,false,68],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":41,\"owners\":[23,43,46,59,62,64,66,71,73,75,76,90,92,93,96,97,98,99,100,101]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[11,12,44,47,67,72,74,77,91,92,93,99,101]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[13,23,60,63,64,68,71,72,75,76,77,97,98,100]}]}"
  "p cnf 68 94\n-1 33 34 39 41 0\n-10 39 41 0\n-23 33 34 41 0\n-2 33 35 41 0\n-13 41 0\n-28 35 0\n-31 33 35 41 0\n-3 17 20 24 25 26 29 0\n-19 24 25 26 29 0\n-30 17 24 26 0\n-31 17 20 24 25 29 0\n-35 4 18 27 30 36 38 0\n-4 20 25 29 37 40 0\n-30 37 40 0\n-38 25 29 40 0\n-11 5 6 0\n-14 7 27 0\n-27 7 14 0\n-33 8 32 0\n-9 12 0\n-12 9 0\n-32 16 22 29 37 39 40 0\n-34 16 22 27 29 36 37 40 0\n-41 9 16 22 29 37 40 0\n-21 15 29 0\n-29 15 21 0\n-18 16 20 0\n-20 16 18 0\n-37 17 0\n-22 25 0\n-25 22 0\n-40 24 0\n-26 0\n-39 0\n-22 42 0\n-24 42 0\n-8 43 0\n-34 43 0\n-32 44 0\n-35 44 0\n-41 44 0\n-15 45 0\n-17 45 0\n-40 45 0\n-5 46 0\n-6 47 0\n-16 48 0\n-37 48 0\n-7 49 0\n-36 49 0\n-50 9 11 14 18 21 25 0\n-9 50 0\n-14 50 0\n-18 50 0\n-21 50 0\n-25 50 0\n-51 12 20 27 29 0\n-12 51 0\n-20 51 0\n-27 51 0\n-29 51 0\n-44 52 0\n-43 52 0\n-52 53 0\n-42 -52 54 0\n-46 55 0\n-45 55 0\n-55 56 0\n-53 57 0\n-53 -56 58 0\n-54 58 0\n-54 -56 59 0\n-48 60 0\n-60 61 0\n-47 61 0\n-62 50 51 0\n-51 62 0\n-50 62 0\n-50 -51 63 0\n-62 64 0\n-63 65 0\n-49 64 0\n-49 -62 65 0\n-64 66 0\n-65 67 0\n-61 66 0\n-61 -64 67 0\n-57 -67 68 0\n-58 -66 68 0\n-59 68 0\n-68 0\n4 9 12 16 18 20 22 25 27 29 30 32 34 35 36 37 38 39 40 41 0\n1 2 10 13 23 26 28 31 33 34 35 39 41 0\n3 4 17 19 20 24 25 26 29 30 31 37 38 40 0\n"
  "95 -59 0 91 90 0\n96 4 9 12 16 18 20 22 25 27 29 30 32 34 35 36 37 38 40 41 0 34 92 0\n97 1 2 10 13 23 28 31 33 34 35 41 0 33 34 93 0\n98 3 4 17 19 20 24 25 29 30 31 37 38 40 0 33 94 0\n99 52 0 34 62 63 39 40 41 37 38 19 6 5 2 1 3 4 7 97 0\n100 53 0 99 64 0\n101 57 0 100 69 0\n102 -67 0 101 91 88 0\n103 -65 0 102 85 0\n104 -63 0 103 81 0\n105 -51 7 16 15 0 104 79 52 53 54 55 21 18 28 26 57 0\n106 -62 61 58 0 99 100 103 70 68 66 45 75 46 16 74 73 47 67 42 71 65 35 31 83 49 105 58 59 60 61 76 20 27 17 25 51 0\n107 51 58 0 100 99 33 71 65 36 70 68 67 43 10 29 32 35 31 59 61 8 11 13 9 15 98 0\n108 58 0 102 107 77 80 106 87 0\n109 -66 0 108 91 89 0\n110 -64 0 109 84 0\n111 -61 0 109 86 0\n112 -62 0 110 80 0\n113 -49 0 110 82 0\n114 -60 0 111 74 0\n115 -51 0 112 77 0\n116 -50 0 112 78 0\n117 -36 0 113 50 0\n118 -48 0 114 73 0\n119 -12 0 115 58 0\n120 -20 0 115 59 0\n121 -27 0 115 60 0\n122 -29 0 115 61 0\n123 -9 0 116 52 0\n124 -18 0 116 54 0\n125 -25 0 116 56 0\n126 -16 0 118 47 0\n127 -37 0 118 48 0\n128 -22 0 125 30 0\n129 40 0 34 127 117 120 122 121 125 128 123 124 126 119 13 23 15 22 24 14 12 96 0\n130 24 0 129 32 0\n131 45 0 129 44 0\n132 42 0 130 36 0\n133 55 0 131 67 0\n134 54 0 132 99 65 0\n135 56 0 133 68 0\n136 0 134 135 95 72 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record019.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record019.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record019.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record019.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record019 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record019.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record019.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record019.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record019.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record019 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record019_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record019_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record019_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record019_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record019_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record019_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record019_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record019 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record019_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record019_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00020.record019_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00020.record019
