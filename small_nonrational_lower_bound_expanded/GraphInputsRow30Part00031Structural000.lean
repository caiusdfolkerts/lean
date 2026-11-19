module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow30Part00031Data
public import GraphInputsRow30Part00031Frames
public import GraphInputsRow30Part00031Leaves
public import GraphInputsRow30Part00031Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00031.record041
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record041
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨110, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), 3014656, 407896064, 92274688, 33554432]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record041_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record041_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record041_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record041_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record041_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record041_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record041_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record041_validity Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record041_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00031.record041

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00031.record042
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3e0f43b0f2368e6358b61d8b92b46d2cc9b29c671e2749b29a96a9695a69a66399968d9362da4e8b92e1ba1e47ae1786d1746b16c6c9726695a69966659564d9b16a5994e5a56352d68d934cd8b46d8749d70da358ce364d5334d332cd4b4ac6b46c5b31ca719c970dc4f0bee0782a4a521c5894a4681e384a52541d18c4b06c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "26db6db49b69a6da69b6db6db6924db6db6db6da6934db6d26d26db69a49a492449249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record042 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record042 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record042.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record042.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record042.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 26), (facetIndex 27), (facetIndex 69), (facetIndex 82)]))
 (.branch 2
 (.leaf ([(facetIndex 40), (facetIndex 41), (facetIndex 70), (facetIndex 90)]))
 (.leaf ([(facetIndex 28), (facetIndex 30), (facetIndex 37), (facetIndex 84)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 36), (facetIndex 67), (facetIndex 68), (facetIndex 88), (facetIndex 104)]))
 (.leaf ([(facetIndex 19), (facetIndex 21), (facetIndex 22), (facetIndex 24)])))
 (.branch 6
 (.leaf ([(facetIndex 47), (facetIndex 49), (facetIndex 52), (facetIndex 94)]))
 (.leaf ([(facetIndex 20), (facetIndex 23), (facetIndex 50), (facetIndex 95)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "3000000d400430020000000000436000000000051a8a00009013000082004d26800000000000000"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1, 2]
def grouped2_0003 : List Nat := [1]
def grouped2_0004 : List Nat := [1, 2]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [3]
def grouped2_0007 : List Nat := [3, 4]
def grouped2_0008 : List Nat := [3, 4, 5, 6]
def grouped2_0009 : List Nat := [4]
def grouped2_0010 : List Nat := [5]
def grouped2_0011 : List Nat := [5, 6]
def grouped2_0012 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record042 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record042_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00031.record042" "{\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00031.record042" 60

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00031.record042" "{\"ridges\":[[8,161],[16,548],[18,608],[22,133],[43,553],[48,561],[52,548],[60,553],[68,608],[73,554],[77,562],[88,416],[94,548],[94,656],[94,672],[95,608],[100,808],[102,816],[104,608]],\"owners\":[[22,133,[8,44,46,50,52,53],[7,24,25,40,49]],[8,161,[9,31,36,38,63,64,67,68],[24,47,52]],[94,656,[58,66,97,99,103],[15,49,64,90,102]],[16,548,[43,48,51,73,77,80,91],[52,94,95]],[52,548,[73,77,80,91],[16,43,48,51,94,95]],[94,548,[43,51,73,80,91],[16,48,52,77,95]],[94,672,[18,68,104],[16,52,64,102]],[88,416,[63,93,102],[17,38,67,81,86,104]],[18,608,[51,60,80,85,91,100],[68,95,104]],[68,608,[80,85,91,100],[18,51,60,95,104]],[95,608,[60,85,100],[18,51,68,80,91,104]],[104,608,[51,60,80,85,91],[18,68,95,100]],[43,553,[60],[]],[60,553,[43],[]],[48,561,[64],[]],[73,554,[85],[]],[77,562,[],[]],[100,808,[],[]],[102,816,[],[]]],\"edges\":[[38,[16,18,43,48,51,52,60,64,68,73,77,80,85,91,94,95,100,102,104]]],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00031.record042" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00031.record042\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-16,-8],[-17,-10],[-20,-7],[-20,-8],[-24,-6],[-24,-9],[-24,-23],[-28,-5],[-28,-14],[-28,-19],[-28,-22],[-28,-26],[-28,-27],[-30,-20],[-30,-22],[-30,-28],[-31,-28],[-32,-4],[-36,-6],[-36,-9],[-36,-23],[-38,-11],[-38,-12],[-38,-15],[-38,-37],[-40,-6],[-40,-9],[-40,-23],[-42,-7],[-42,-13],[-42,-29],[-42,-41],[-43,-25],[-43,-40],[-43,-42],[-44,-18],[-49,-2],[-49,-14],[-49,-23],[-49,-32],[-49,-45],[-49,-48],[-8,1,18,19,23,25,26],[-1,2,13,14,16,29,30,32,33],[-42,27,31,44,45,48],[-3,17,21,24,34,35,36,40],[-25,34,35,36,40],[-42,17,24,34,36,40],[-42,4,33,49],[-39,29,41,47],[-4,24,28,36,38,40,46],[-33,36,38,40,46],[-43,28,38,46],[-49,24,28,36,38,40],[-17,28],[-28,17],[-21,30],[-34,38],[-35],[-46],[-47],[-50,11,12,15,37],[-51,14,32,33,39,49],[-52,5,7,8,10],[-53,20,22,25,42],[-54,6,9,23,43],[-55,50],[-56,55],[-57,51],[-57,52],[-58,53],[-58,54],[-59,57],[-59,58],[-60,56],[-60,59],[60],[3,4,17,21,24,25,28,30,33,34,35,36,38,40,42,43,46,47,49]],\"atoms\":[{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":38,\"b\":22},{\"tag\":\"incompatible\",\"a\":43,\"b\":24},{\"tag\":\"incompatible\",\"a\":47,\"b\":21},{\"tag\":\"incompatible\",\"a\":47,\"b\":22},{\"tag\":\"incompatible\",\"a\":51,\"b\":20},{\"tag\":\"incompatible\",\"a\":51,\"b\":23},{\"tag\":\"incompatible\",\"a\":51,\"b\":50},{\"tag\":\"incompatible\",\"a\":60,\"b\":19},{\"tag\":\"incompatible\",\"a\":60,\"b\":36},{\"tag\":\"incompatible\",\"a\":60,\"b\":46},{\"tag\":\"incompatible\",\"a\":60,\"b\":49},{\"tag\":\"incompatible\",\"a\":60,\"b\":53},{\"tag\":\"incompatible\",\"a\":60,\"b\":58},{\"tag\":\"incompatible\",\"a\":64,\"b\":47},{\"tag\":\"incompatible\",\"a\":64,\"b\":49},{\"tag\":\"incompatible\",\"a\":64,\"b\":60},{\"tag\":\"incompatible\",\"a\":66,\"b\":60},{\"tag\":\"incompatible\",\"a\":67,\"b\":18},{\"tag\":\"incompatible\",\"a\":80,\"b\":20},{\"tag\":\"incompatible\",\"a\":80,\"b\":23},{\"tag\":\"incompatible\",\"a\":80,\"b\":50},{\"tag\":\"incompatible\",\"a\":85,\"b\":28},{\"tag\":\"incompatible\",\"a\":85,\"b\":30},{\"tag\":\"incompatible\",\"a\":85,\"b\":37},{\"tag\":\"incompatible\",\"a\":85,\"b\":84},{\"tag\":\"incompatible\",\"a\":91,\"b\":20},{\"tag\":\"incompatible\",\"a\":91,\"b\":23},{\"tag\":\"incompatible\",\"a\":91,\"b\":50},{\"tag\":\"incompatible\",\"a\":94,\"b\":21},{\"tag\":\"incompatible\",\"a\":94,\"b\":31},{\"tag\":\"incompatible\",\"a\":94,\"b\":63},{\"tag\":\"incompatible\",\"a\":94,\"b\":93},{\"tag\":\"incompatible\",\"a\":95,\"b\":52},{\"tag\":\"incompatible\",\"a\":95,\"b\":91},{\"tag\":\"incompatible\",\"a\":95,\"b\":94},{\"tag\":\"incompatible\",\"a\":97,\"b\":44},{\"tag\":\"incompatible\",\"a\":104,\"b\":9},{\"tag\":\"incompatible\",\"a\":104,\"b\":36},{\"tag\":\"incompatible\",\"a\":104,\"b\":50},{\"tag\":\"incompatible\",\"a\":104,\"b\":67},{\"tag\":\"incompatible\",\"a\":104,\"b\":99},{\"tag\":\"incompatible\",\"a\":104,\"b\":103},{\"tag\":\"mate\",\"ridge\":133,\"a\":22,\"owners\":[8,44,46,50,52,53]},{\"tag\":\"mate\",\"ridge\":161,\"a\":8,\"owners\":[9,31,36,38,63,64,67,68]},{\"tag\":\"mate\",\"ridge\":656,\"a\":94,\"owners\":[58,66,97,99,103]},{\"tag\":\"mate\",\"ridge\":548,\"a\":16,\"owners\":[43,48,51,73,77,80,91]},{\"tag\":\"mate\",\"ridge\":548,\"a\":52,\"owners\":[73,77,80,91]},{\"tag\":\"mate\",\"ridge\":548,\"a\":94,\"owners\":[43,51,73,80,91]},{\"tag\":\"mate\",\"ridge\":672,\"a\":94,\"owners\":[18,68,104]},{\"tag\":\"mate\",\"ridge\":416,\"a\":88,\"owners\":[63,93,102]},{\"tag\":\"mate\",\"ridge\":608,\"a\":18,\"owners\":[51,60,80,85,91,100]},{\"tag\":\"mate\",\"ridge\":608,\"a\":68,\"owners\":[80,85,91,100]},{\"tag\":\"mate\",\"ridge\":608,\"a\":95,\"owners\":[60,85,100]},{\"tag\":\"mate\",\"ridge\":608,\"a\":104,\"owners\":[51,60,80,85,91]},{\"tag\":\"mate\",\"ridge\":553,\"a\":43,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":553,\"a\":60,\"owners\":[43]},{\"tag\":\"mate\",\"ridge\":561,\"a\":48,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":554,\"a\":73,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":562,\"a\":77,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":808,\"a\":100,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":816,\"a\":102,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[28,30,37,84],\"full_literals\":[-50,11,12,15,37]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[36,67,68,88,104],\"full_literals\":[-51,14,32,33,39,49]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[19,21,22,24],\"full_literals\":[-52,5,7,8,10]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[47,49,52,94],\"full_literals\":[-53,20,22,25,42]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[20,23,50,95],\"full_literals\":[-54,6,9,23,43]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-55,false,50],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-56,false,55],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-57,51,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-57,false,52],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-58,53,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-58,false,54],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-59,57,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-59,false,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-60,56,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-60,false,59],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"edge\",\"edge\":38,\"owners\":[16,18,43,48,51,52,60,64,68,73,77,80,85,91,94,95,100,102,104]}]}"
  "79 56 0 77 75 0\n80 59 0 77 76 0\n81 55 0 79 68 0\n82 57 0 80 73 0\n83 58 0 80 74 0\n84 50 0 81 67 0\n85 51 0 82 69 0\n86 52 0 82 70 0\n87 53 0 83 71 0\n88 54 0 83 72 0\n89 3 4 17 21 24 25 28 30 33 34 36 38 40 42 43 49 0 59 60 61 78 0\n90 -40 0 88 26 27 28 34 66 0\n91 -24 43 0 88 5 6 7 66 0\n92 28 30 36 38 42 43 49 0 59 60 90 57 58 47 52 91 55 46 51 89 0\n93 -28 25 42 0 87 86 8 11 56 65 2 3 4 64 0\n94 36 38 42 43 49 0 90 59 87 58 47 93 92 14 15 65 0\n95 -36 43 0 88 19 20 21 66 0\n96 -38 0 84 22 23 24 25 62 0\n97 -34 0 96 58 0\n98 43 49 0 60 96 90 97 61 85 91 95 94 52 31 32 48 49 50 55 18 9 63 0\n99 -43 0 60 96 33 35 53 93 0\n100 -24 0 99 91 0\n101 -36 0 99 95 0\n102 49 0 99 98 0\n103 -33 0 101 96 90 60 52 0\n104 -25 0 101 59 97 90 47 0\n105 -2 0 102 37 0\n106 -14 0 102 38 0\n107 -23 0 102 39 0\n108 -32 0 102 40 0\n109 -45 0 102 41 0\n110 -48 0 102 42 0\n111 28 0 102 100 101 96 90 54 0\n112 -5 0 111 8 0\n113 -19 0 111 10 0\n114 -26 0 111 12 0\n115 -27 0 111 13 0\n116 -30 0 111 16 0\n117 -31 0 111 17 0\n118 17 0 111 56 0\n119 42 0 111 104 93 0\n120 44 0 115 117 119 109 110 45 0\n121 -10 0 118 2 0\n122 -7 0 119 29 0\n123 -13 0 119 30 0\n124 -29 0 119 31 0\n125 -18 0 120 36 0\n126 8 0 121 86 112 122 64 0\n127 -16 0 126 1 0\n128 1 0 126 125 113 107 104 114 43 0\n129 0 128 127 105 106 123 124 116 108 103 44 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record042.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record042.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record042.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record042.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record042 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record042.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record042.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record042.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record042.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record042 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record042_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record042_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record042_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record042_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record042_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record042_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record042_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record042 Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record042_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record042_validity Papers.RationalityTen.CompactReplay.GraphInputsRow30Part00031.record042_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow30Part00031.record042
