module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow16Part00020Data
public import GraphInputsRow16Part00020Frames
public import GraphInputsRow16Part00020Leaves
public import GraphInputsRow16Part00020Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00020.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record000
def vertexColumn : Fields := ⟨10, hexnat% "2b29693ab1966a5a562d94e4b85e0fab196539b1565a56552d54d4b45d0f743b0ea368d63a4e538cd332ce4b4ae1b46c5b0ee8791d4731d2719e1725c5743c8f0bd4a298361381e524a50d44d0768390d4348ca384c3342c4b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6d26936db6d2692492492492492492492491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3003131c5ffe000000", 3623990325149696, hexnat% "20020022000000000", 1649267441664, hexnat% "40040000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "14015ce57dd8000000", 9227468800, hexnat% "20020020000000000", 299616918568960, 571746046443520, hexnat% "200200000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2002ef9fbf6000000", hexnat% "200200000000000000", hexnat% "40040000008000000", 4787290807205888, hexnat% "100100040000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3203277a27fe000000", 2392640381255680, 6322191859712, hexnat% "40040000000000000", 4503599627370496]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "14014444dffe000000", 153122387330596864, hexnat% "220000000000000000", 6896136929411072, 873012232454144, 36421322670080]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4215510233251840, hexnat% "200200000000000000", 27021597764222976, hexnat% "100100040408000000", hexnat% "60000000000000000", 4787273627336704]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [9007199221186560, hexnat% "100100000000000000", hexnat% "200200000000000000", hexnat% "40040000000000000", hexnat% "20020000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4219874020687872, hexnat% "100100000400000000", hexnat% "200200000002000000", 4785108963819520, hexnat% "40040000000000000", hexnat% "20020020000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1001006545cc000000", hexnat% "200200880020000000", hexnat% "40040000012000000", 301815941824512, 1688918579740672, 6755442390728704, hexnat% "20020002000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c11 c4
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c12 c3
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c13 c2
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c14 c1
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c15 c0
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00020.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00020.record064
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record064
def vertexColumn : Fields := ⟨10, hexnat% "2d2aca72aa99a4e8ba999564d8763392eb46b19c6a9665392e665555351d4cd4b6a398e9364e5354e334ccb31ce8b62ccb8ad2b2ad1b26c3b91d4731e2749c6745c570dc8f13ec23490e0bac13450d0b68390cc388d1324c530cd0b22c2b41c4709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "9b6db6db6936db6db6d2492492492492492492492449249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨78, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40020004021800000", hexnat% "40020005010080000000", 13220446208, 6768868458496, 765328946626560, 6826336228212736]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record064_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record064_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record064_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record064_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record064_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record064_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record064_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record064_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record064_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00020.record064

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00020.record068
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record068
def vertexColumn : Fields := ⟨10, hexnat% "3b29c3aa5a39936338ae1b91eb84e9a6659694e5a5535a34cd2b46d8751d2756338e534ce4b32cab1ae1b46c5b31ca719c3743c8f13c2fb21264581eb04e1a264932619494a54548d0752318d1312c1b41c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db69b6924926924d2493493492692492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨62, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4694031233796014080, 148620986726481920, 288247976927690752, 54043487586222080, 844562369085440, 35184372088832]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [220969329632477184, 288247968337756160, 4947802324992, 9147937816838144, 54641329853956096, 4612811918334230528]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [257706181672304640, 10133100503760896, 18049604356407296, 4899916394713317376, 558345748480, 17592186044416]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [235039205347033088, 13651536370466816, 36072794663944192, 4899916394713317376, 1143492092887040, 8589934592]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4901386055598473216, 18014677682356224, 36591746972385280, 220678580764409856, 9147937816838144, 4432943120384]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [230697503706578944, 54043487586222080, 4948607631360, 4612811918468448256, 288230384741646336, 35188667056128]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [221725459161808896, 288230384741646336, 4432943120384, 10133099161583616, 54043487586222080, 4611686568183201792]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4901518001288773632, 36600543065407488, 18014673387388928, 220678580764409856, 4432943120384, 9007200328482816]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [221118531561848832, 4899916394981752832, 36635727437496320, 10133100235325440, 18014694862225408, 4432943120384, 549755813888]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c11 c4
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c12 c3
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c13 c2
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c14 c1
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c15 c0
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record068_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record068_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record068_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record068_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record068_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record068_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record068_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record068_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record068_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00020.record068

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00020.record036
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "372e2b2aa64d8ce2b91e17ae1b24d9a95a535535334ad4749d176c3c8ea398ce394d534ce8b92ccb2ad1ba1cc789ca715c3743c8f13c2f169264581eb06a132459494a54548d0764388d2344c5312c1b41c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db4da49249a4924924d24d269b492492249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record036 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record036 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record036.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record036.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record036.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 43), (facetIndex 44), (facetIndex 46), (facetIndex 58)]))
 (.leaf ([(facetIndex 27), (facetIndex 28), (facetIndex 39), (facetIndex 52), (facetIndex 63)])))
 (.branch 3
 (.leaf ([(facetIndex 29), (facetIndex 37), (facetIndex 40), (facetIndex 41)]))
 (.leaf ([(facetIndex 34), (facetIndex 59), (facetIndex 60)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 24), (facetIndex 30), (facetIndex 31), (facetIndex 45)]))
 (.leaf ([(facetIndex 50), (facetIndex 54), (facetIndex 55)])))
 (.branch 7
 (.leaf ([(facetIndex 36), (facetIndex 51), (facetIndex 56), (facetIndex 57)]))
 (.branch 8
 (.leaf ([(facetIndex 26), (facetIndex 47), (facetIndex 48), (facetIndex 49)]))
 (.leaf ([(facetIndex 25)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "1003306655016577704000221026030044211784z18;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 32), (facetIndex 53)]))
 (.leaf ([(facetIndex 62), (facetIndex 67)])))
 (.branch 3
 (.leaf ([(facetIndex 33), (facetIndex 35), (facetIndex 38), (facetIndex 42)]))
 (.leaf ([(facetIndex 61), (facetIndex 64), (facetIndex 65), (facetIndex 66)]))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨2, sparse_nat% "7f1c00000000202088z10;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 4
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3]
def grouped2_0005 : List Nat := [3]
def grouped2_0006 : List Nat := [4]
def grouped2_0007 : List Nat := [4, 5]
def grouped2_0008 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0009 : List Nat := [5]
def grouped2_0010 : List Nat := [6]
def grouped2_0011 : List Nat := [6, 7, 8]
def grouped2_0012 : List Nat := [7]
def grouped2_0013 : List Nat := [7, 8]
def grouped2_0014 : List Nat := [8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record036 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record036_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00020.record036" "{\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":1}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00020.record036" 48

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00020.record036" "{\"ridges\":[[12,140],[17,200],[18,672],[19,704],[26,140],[36,200],[44,546],[46,578],[50,140],[51,140],[54,164],[55,164],[56,200],[57,200],[57,704],[58,672],[61,170],[65,650],[66,226]],\"owners\":[[44,546,[],[9,31,43,45,64,66]],[46,578,[],[10,37,41,43,65,66]],[12,140,[61,62,67],[26,48,50,51]],[26,140,[67],[12,48,50,51,61,62]],[50,140,[62,67],[12,26,48,51,61]],[51,140,[61],[12,26,48,50,62,67]],[54,164,[61,64],[14,30,50,55]],[55,164,[61],[14,30,50,54,64]],[17,200,[62,65,67],[36,51,56,57]],[36,200,[67],[17,51,56,57,62,65]],[56,200,[62,65],[17,36,51,57,67]],[57,200,[62,67],[17,36,51,56,65]],[18,672,[64,66],[44,55,58]],[58,672,[64],[18,44,55,66]],[19,704,[65,66],[46,57,58]],[57,704,[66],[19,46,58,65]],[61,170,[35],[]],[65,650,[38],[]],[66,226,[42],[]]],\"edges\":[[27,[12,17,26,35,36,38,48,50,51,56,57,61,62,65,67]],[43,[18,19,33,38,44,46,55,57,58,64,65,66]]],\"groupings\":[2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00020.record036" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00020.record036\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-9,-5],[-10,-7],[-11,-5],[-11,-10],[-16,-5],[-17,-8],[-19,-5],[-19,-9],[-22,-5],[-22,-15],[-22,-16],[-23,-12],[-26,-17],[-27,-10],[-28,-5],[-28,-25],[-29,-10],[-30,-10],[-30,-27],[-30,-29],[-31,-10],[-32,-5],[-32,-22],[-13],[-14],[-1,27,28,32],[-6,32],[-18,28,32],[-19,27],[-20,27,29],[-21,27],[-2,28,30,32],[-10,32],[-22,28,30],[-23,28,32],[-3,29,31],[-24,29],[-4,30,31],[-23,31],[-27,9],[-30,11],[-31,12],[-33,8,25,26],[-34,18,20,21],[-35,10,19,22,23],[-19,35],[-22,35],[-36,6,15,16,17],[-37,5],[-38,33],[-39,38],[-40,34],[-41,36,37],[-42,37],[-43,35,42],[-44,35],[-43,41],[-44,42],[-35,-42,44],[-45,40,44],[-45,43],[-46,44],[-47,39,46],[-47,45],[47],[-48,28,32],[-28,48],[-32,48],[1,2,6,9,10,11,16,18,19,22,23,27,28,30,32],[3,4,7,11,13,14,21,23,24,29,30,31]],\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":35,\"b\":25},{\"tag\":\"incompatible\",\"a\":36,\"b\":33},{\"tag\":\"incompatible\",\"a\":38,\"b\":25},{\"tag\":\"incompatible\",\"a\":38,\"b\":36},{\"tag\":\"incompatible\",\"a\":48,\"b\":25},{\"tag\":\"incompatible\",\"a\":49,\"b\":34},{\"tag\":\"incompatible\",\"a\":51,\"b\":25},{\"tag\":\"incompatible\",\"a\":51,\"b\":35},{\"tag\":\"incompatible\",\"a\":56,\"b\":25},{\"tag\":\"incompatible\",\"a\":56,\"b\":47},{\"tag\":\"incompatible\",\"a\":56,\"b\":48},{\"tag\":\"incompatible\",\"a\":57,\"b\":42},{\"tag\":\"incompatible\",\"a\":60,\"b\":49},{\"tag\":\"incompatible\",\"a\":61,\"b\":36},{\"tag\":\"incompatible\",\"a\":62,\"b\":25},{\"tag\":\"incompatible\",\"a\":62,\"b\":59},{\"tag\":\"incompatible\",\"a\":64,\"b\":36},{\"tag\":\"incompatible\",\"a\":65,\"b\":36},{\"tag\":\"incompatible\",\"a\":65,\"b\":61},{\"tag\":\"incompatible\",\"a\":65,\"b\":64},{\"tag\":\"incompatible\",\"a\":66,\"b\":36},{\"tag\":\"incompatible\",\"a\":67,\"b\":25},{\"tag\":\"incompatible\",\"a\":67,\"b\":56},{\"tag\":\"mate\",\"ridge\":546,\"a\":44,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":578,\"a\":46,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":140,\"a\":12,\"owners\":[61,62,67]},{\"tag\":\"mate\",\"ridge\":140,\"a\":26,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":140,\"a\":50,\"owners\":[62,67]},{\"tag\":\"mate\",\"ridge\":140,\"a\":51,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":164,\"a\":54,\"owners\":[61,64]},{\"tag\":\"mate\",\"ridge\":164,\"a\":55,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":200,\"a\":17,\"owners\":[62,65,67]},{\"tag\":\"mate\",\"ridge\":200,\"a\":36,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":200,\"a\":56,\"owners\":[62,65]},{\"tag\":\"mate\",\"ridge\":200,\"a\":57,\"owners\":[62,67]},{\"tag\":\"mate\",\"ridge\":672,\"a\":18,\"owners\":[64,66]},{\"tag\":\"mate\",\"ridge\":672,\"a\":58,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":704,\"a\":19,\"owners\":[65,66]},{\"tag\":\"mate\",\"ridge\":704,\"a\":57,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":170,\"a\":61,\"owners\":[35]},{\"tag\":\"mate\",\"ridge\":650,\"a\":65,\"owners\":[38]},{\"tag\":\"mate\",\"ridge\":226,\"a\":66,\"owners\":[42]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[34,59,60],\"full_literals\":[-33,8,25,26]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[50,54,55],\"full_literals\":[-34,18,20,21]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[36,51,56,57],\"full_literals\":[-35,10,19,22,23]},{\"tag\":\"group_take\",\"kind\":2,\"index\":6,\"member\":51,\"full_literals\":[-19,35]},{\"tag\":\"group_take\",\"kind\":2,\"index\":6,\"member\":56,\"full_literals\":[-22,35]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[26,47,48,49],\"full_literals\":[-36,6,15,16,17]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[25],\"full_literals\":[-37,5]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-38,false,33],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-39,false,38],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-40,false,34],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-41,36,37],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-42,false,37],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-43,35,42],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-44,35,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-43,false,41],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-44,false,42],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-35,-42,44],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-45,40,44],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-45,false,43],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-46,false,44],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-47,39,46],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-47,false,45],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[62,67],\"full_literals\":[-48,28,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":62,\"full_literals\":[-28,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":67,\"full_literals\":[-32,48]},{\"tag\":\"edge\",\"edge\":27,\"owners\":[12,17,26,35,36,38,48,50,51,56,57,61,62,65,67]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[18,19,33,38,44,46,55,57,58,64,65,66]}]}"
  "p cnf 48 70\n-9 -5 0\n-10 -7 0\n-11 -5 0\n-11 -10 0\n-16 -5 0\n-17 -8 0\n-19 -5 0\n-19 -9 0\n-22 -5 0\n-22 -15 0\n-22 -16 0\n-23 -12 0\n-26 -17 0\n-27 -10 0\n-28 -5 0\n-28 -25 0\n-29 -10 0\n-30 -10 0\n-30 -27 0\n-30 -29 0\n-31 -10 0\n-32 -5 0\n-32 -22 0\n-13 0\n-14 0\n-1 27 28 32 0\n-6 32 0\n-18 28 32 0\n-19 27 0\n-20 27 29 0\n-21 27 0\n-2 28 30 32 0\n-10 32 0\n-22 28 30 0\n-23 28 32 0\n-3 29 31 0\n-24 29 0\n-4 30 31 0\n-23 31 0\n-27 9 0\n-30 11 0\n-31 12 0\n-33 8 25 26 0\n-34 18 20 21 0\n-35 10 19 22 23 0\n-19 35 0\n-22 35 0\n-36 6 15 16 17 0\n-37 5 0\n-38 33 0\n-39 38 0\n-40 34 0\n-41 36 37 0\n-42 37 0\n-43 35 42 0\n-44 35 0\n-43 41 0\n-44 42 0\n-35 -42 44 0\n-45 40 44 0\n-45 43 0\n-46 44 0\n-47 39 46 0\n-47 45 0\n47 0\n-48 28 32 0\n-28 48 0\n-32 48 0\n1 2 6 9 10 11 16 18 19 22 23 27 28 30 32 0\n3 4 7 11 13 14 21 23 24 29 30 31 0\n"
  "71 45 0 65 64 0\n72 43 0 71 61 0\n73 41 0 72 57 0\n74 3 4 7 11 21 23 24 29 30 31 0 24 25 70 0\n75 -44 48 0 68 33 67 35 56 58 54 49 7 9 45 0\n76 -42 48 0 75 68 33 27 67 35 28 54 59 49 46 47 1 3 5 40 41 26 32 69 0\n77 -19 0 8 29 40 0\n78 48 0 71 72 77 67 68 28 35 33 75 60 52 76 55 45 34 19 20 31 30 44 0\n79 -22 37 0 73 65 78 54 58 62 63 51 50 53 10 11 23 27 66 48 16 6 13 43 0\n80 -23 0 12 39 42 0\n81 -10 0 80 2 4 14 17 18 21 31 36 37 38 74 0\n82 -5 0 78 15 22 66 0\n83 -37 0 82 49 0\n84 -42 0 83 54 0\n85 -22 0 83 79 0\n86 35 0 84 72 55 0\n87 0 86 85 80 77 81 45 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record036.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record036.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record036.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record036.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record036 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record036.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record036.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record036.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record036.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record036 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record036_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record036_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record036_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record036_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record036_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record036_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record036_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record036 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record036_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record036_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00020.record036_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00020.record036
