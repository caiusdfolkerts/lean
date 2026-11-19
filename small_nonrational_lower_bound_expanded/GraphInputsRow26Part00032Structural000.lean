module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow26Part00032Data
public import GraphInputsRow26Part00032Frames
public import GraphInputsRow26Part00032Leaves
public import GraphInputsRow26Part00032Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00032.record060
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record060
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨18, by decide⟩, ⟨21, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨30, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨47, by decide⟩, ⟨51, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨71, by decide⟩, ⟨73, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨87, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 74309393851613184, (certNat% 3), 42983489536, 36169534507319296]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 4), 42983489536, 36169534507319296, 74309393851613184, (certNat% 5), (certNat% 6)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c1 c0
  c2
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record060_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record060_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record060_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record060_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record060_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record060_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record060_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record060_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record060_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00032.record060

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00032.record007
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3cb8aaa9aa969c6698e61da4e4b91e178f1e26a96a659715a5394759352d4745de0dc3a8da338e5334cb31cf0ba2d8b92e2b4acab86d1b16d8791d4731d2729c6745e0f13c3cb083a158364382e07ac10e4550d50d0b41da0d8390cc328c530ce0b42c2b06d0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db6d34936db6da692492492492492492492492449249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record007 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record007 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record007.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record007.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record007.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 33), (facetIndex 60), (facetIndex 61), (facetIndex 64)]))
 (.leaf ([(facetIndex 31), (facetIndex 32), (facetIndex 36), (facetIndex 45), (facetIndex 62), (facetIndex 75)])))
 (.branch 3
 (.leaf ([(facetIndex 73), (facetIndex 74), (facetIndex 77)]))
 (.leaf ([(facetIndex 34), (facetIndex 37), (facetIndex 38), (facetIndex 39), (facetIndex 53), (facetIndex 54)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 42), (facetIndex 43), (facetIndex 46), (facetIndex 47), (facetIndex 49), (facetIndex 50)]))
 (.leaf ([(facetIndex 41), (facetIndex 51), (facetIndex 52)])))
 (.branch 7
 (.leaf ([(facetIndex 35), (facetIndex 40), (facetIndex 55), (facetIndex 56), (facetIndex 57), (facetIndex 58), (facetIndex 59)]))
 (.leaf ([(facetIndex 44), (facetIndex 48)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "10290000000040db6cddb2790f92e6d9cc12z17;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3]
def grouped2_0005 : List Nat := [3]
def grouped2_0006 : List Nat := [4]
def grouped2_0007 : List Nat := [4, 5]
def grouped2_0008 : List Nat := [4, 5, 6, 7]
def grouped2_0009 : List Nat := [5]
def grouped2_0010 : List Nat := [6]
def grouped2_0011 : List Nat := [6, 7]
def grouped2_0012 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record007 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record007_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00032.record007" "{\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00032.record007" 52

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00032.record007" "{\"ridges\":[[12,67],[12,131],[22,193],[29,194],[38,67],[40,131],[40,385],[47,521],[48,385],[49,521],[51,67],[52,131]],\"owners\":[[47,521,[70,71],[8,32,43,46,49,50,63,68]],[49,521,[63,68],[8,32,43,46,47,50,70,71]],[22,193,[12,37,53,55,58,65,67,72],[]],[29,194,[12,37,53,55,58,78,80,85],[]],[40,385,[69,71],[14,48,56,58,59,66,67]],[48,385,[66,67],[14,40,56,58,59,69,71]]],\"edges\":[[39,[12,22,29,37,53,55,58,65,67,72,78,80,85]]],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00032.record007" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00032.record007\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-9,-6],[-11,-10],[-12,-10],[-13,-5],[-13,-11],[-13,-12],[-14,-10],[-14,-13],[-15,-10],[-16,-9],[-16,-11],[-16,-12],[-16,-14],[-17,-13],[-17,-16],[-18,-10],[-18,-13],[-18,-16],[-19,-4],[-19,-6],[-19,-8],[-20,-5],[-21,-19],[-21,-20],[-22,-19],[-23,-13],[-23,-16],[-23,-19],[-23,-20],[-24,-13],[-24,-16],[-24,-20],[-25,-13],[-25,-16],[-25,-20],[-26,-7],[-26,-13],[-26,-16],[-26,-20],[-27,-13],[-27,-16],[-27,-20],[-28,-10],[-29,-9],[-29,-19],[-30,-5],[-31,-5],[-31,-7],[-31,-9],[-32,-10],[-33,-13],[-34,-13],[-34,-16],[-35,-13],[-35,-16],[-36,-19],[-36,-20],[-37,-9],[-37,-19],[-38,-7],[-38,-9],[-39,-19],[-39,-20],[-1,-7,-19],[-15,34,35],[-17,28,32],[-1,-9,-20],[-2,1,6,21,23,26,29,31,36],[-3,1,6,21,23,26,37,38,39],[-9,33,35],[-16,30,31],[-40,4,6,7,8,21,22],[-41,11,12,14,15,17,18],[-42,10,19,20],[-43,5,9,23,24,25,26,27],[-44,13,16],[-45,40],[-46,45],[-47,41],[-47,42],[-48,43,44],[-49,43],[-49,44],[-50,47,49],[-50,48],[-51,49],[-52,46,51],[-52,50],[52],[1,2,3,6,21,23,26,29,31,36,37,38,39]],\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":40,\"b\":37},{\"tag\":\"incompatible\",\"a\":42,\"b\":41},{\"tag\":\"incompatible\",\"a\":43,\"b\":41},{\"tag\":\"incompatible\",\"a\":44,\"b\":35},{\"tag\":\"incompatible\",\"a\":44,\"b\":42},{\"tag\":\"incompatible\",\"a\":44,\"b\":43},{\"tag\":\"incompatible\",\"a\":46,\"b\":41},{\"tag\":\"incompatible\",\"a\":46,\"b\":44},{\"tag\":\"incompatible\",\"a\":47,\"b\":41},{\"tag\":\"incompatible\",\"a\":48,\"b\":40},{\"tag\":\"incompatible\",\"a\":48,\"b\":42},{\"tag\":\"incompatible\",\"a\":48,\"b\":43},{\"tag\":\"incompatible\",\"a\":48,\"b\":46},{\"tag\":\"incompatible\",\"a\":49,\"b\":44},{\"tag\":\"incompatible\",\"a\":49,\"b\":48},{\"tag\":\"incompatible\",\"a\":50,\"b\":41},{\"tag\":\"incompatible\",\"a\":50,\"b\":44},{\"tag\":\"incompatible\",\"a\":50,\"b\":48},{\"tag\":\"incompatible\",\"a\":51,\"b\":34},{\"tag\":\"incompatible\",\"a\":51,\"b\":37},{\"tag\":\"incompatible\",\"a\":51,\"b\":39},{\"tag\":\"incompatible\",\"a\":52,\"b\":35},{\"tag\":\"incompatible\",\"a\":53,\"b\":51},{\"tag\":\"incompatible\",\"a\":53,\"b\":52},{\"tag\":\"incompatible\",\"a\":54,\"b\":51},{\"tag\":\"incompatible\",\"a\":55,\"b\":44},{\"tag\":\"incompatible\",\"a\":55,\"b\":48},{\"tag\":\"incompatible\",\"a\":55,\"b\":51},{\"tag\":\"incompatible\",\"a\":55,\"b\":52},{\"tag\":\"incompatible\",\"a\":56,\"b\":44},{\"tag\":\"incompatible\",\"a\":56,\"b\":48},{\"tag\":\"incompatible\",\"a\":56,\"b\":52},{\"tag\":\"incompatible\",\"a\":57,\"b\":44},{\"tag\":\"incompatible\",\"a\":57,\"b\":48},{\"tag\":\"incompatible\",\"a\":57,\"b\":52},{\"tag\":\"incompatible\",\"a\":58,\"b\":38},{\"tag\":\"incompatible\",\"a\":58,\"b\":44},{\"tag\":\"incompatible\",\"a\":58,\"b\":48},{\"tag\":\"incompatible\",\"a\":58,\"b\":52},{\"tag\":\"incompatible\",\"a\":59,\"b\":44},{\"tag\":\"incompatible\",\"a\":59,\"b\":48},{\"tag\":\"incompatible\",\"a\":59,\"b\":52},{\"tag\":\"incompatible\",\"a\":63,\"b\":41},{\"tag\":\"incompatible\",\"a\":65,\"b\":40},{\"tag\":\"incompatible\",\"a\":65,\"b\":51},{\"tag\":\"incompatible\",\"a\":66,\"b\":35},{\"tag\":\"incompatible\",\"a\":67,\"b\":35},{\"tag\":\"incompatible\",\"a\":67,\"b\":38},{\"tag\":\"incompatible\",\"a\":67,\"b\":40},{\"tag\":\"incompatible\",\"a\":68,\"b\":41},{\"tag\":\"incompatible\",\"a\":69,\"b\":44},{\"tag\":\"incompatible\",\"a\":70,\"b\":44},{\"tag\":\"incompatible\",\"a\":70,\"b\":48},{\"tag\":\"incompatible\",\"a\":71,\"b\":44},{\"tag\":\"incompatible\",\"a\":71,\"b\":48},{\"tag\":\"incompatible\",\"a\":72,\"b\":51},{\"tag\":\"incompatible\",\"a\":72,\"b\":52},{\"tag\":\"incompatible\",\"a\":78,\"b\":40},{\"tag\":\"incompatible\",\"a\":78,\"b\":51},{\"tag\":\"incompatible\",\"a\":80,\"b\":38},{\"tag\":\"incompatible\",\"a\":80,\"b\":40},{\"tag\":\"incompatible\",\"a\":85,\"b\":51},{\"tag\":\"incompatible\",\"a\":85,\"b\":52},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[12,38,51]},{\"tag\":\"mate\",\"ridge\":521,\"a\":47,\"owners\":[70,71]},{\"tag\":\"mate\",\"ridge\":521,\"a\":49,\"owners\":[63,68]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[12,40,52]},{\"tag\":\"mate\",\"ridge\":193,\"a\":22,\"owners\":[12,37,53,55,58,65,67,72]},{\"tag\":\"mate\",\"ridge\":194,\"a\":29,\"owners\":[12,37,53,55,58,78,80,85]},{\"tag\":\"mate\",\"ridge\":385,\"a\":40,\"owners\":[69,71]},{\"tag\":\"mate\",\"ridge\":385,\"a\":48,\"owners\":[66,67]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[34,37,38,39,53,54],\"full_literals\":[-40,4,6,7,8,21,22]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[42,43,46,47,49,50],\"full_literals\":[-41,11,12,14,15,17,18]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[41,51,52],\"full_literals\":[-42,10,19,20]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[35,40,55,56,57,58,59],\"full_literals\":[-43,5,9,23,24,25,26,27]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[44,48],\"full_literals\":[-44,13,16]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-45,false,40],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-46,false,45],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-47,41,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-47,false,42],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-48,43,44],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-49,43,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-49,false,44],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-50,47,49],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-50,false,48],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-51,false,49],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-52,46,51],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-52,false,50],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"edge\",\"edge\":39,\"owners\":[12,22,29,37,53,55,58,65,67,72,78,80,85]}]}"
  "91 50 0 89 88 0\n92 48 0 91 85 0\n93 -13 0 91 4 5 6 8 14 17 26 30 33 37 40 51 52 54 65 70 73 75 79 82 84 0\n94 -16 0 91 10 11 12 13 15 18 27 31 34 38 41 53 55 65 73 79 84 82 75 46 47 71 0\n95 -44 0 94 93 76 0\n96 -49 0 95 83 0\n97 43 0 95 92 81 0\n98 -51 0 96 86 0\n99 47 0 96 91 84 0\n100 46 0 98 89 87 0\n101 41 0 99 79 0\n102 42 0 99 80 0\n103 45 0 100 78 0\n104 40 0 103 77 0\n105 -10 0 101 2 3 7 9 16 43 50 73 66 0\n106 -19 0 104 19 20 21 23 25 28 45 56 59 62 72 36 48 60 64 68 69 90 0\n107 20 0 106 105 102 74 0\n108 -5 0 107 22 0\n109 -21 0 107 24 0\n110 -23 0 107 29 0\n111 -24 0 107 32 0\n112 -25 0 107 35 0\n113 -26 0 107 39 0\n114 -27 0 107 42 0\n115 -36 0 107 57 0\n116 -39 0 107 63 0\n117 9 0 112 97 108 111 110 113 114 75 0\n118 -6 0 117 1 0\n119 -29 0 117 44 0\n120 -31 0 117 49 0\n121 -37 0 117 58 0\n122 -38 0 117 61 0\n123 -1 0 117 107 67 0\n124 -2 0 123 115 120 109 113 119 110 118 68 0\n125 -3 0 123 116 122 109 113 121 110 118 69 0\n126 0 124 125 123 118 120 122 113 109 119 115 121 110 116 90 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record007.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record007.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record007.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record007.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record007 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record007.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record007.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record007.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record007.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record007 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record007_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record007 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record007_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record007_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00032.record007

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00032.record065
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "29c9729a9693a699964d89e1783ee4669a66594e6c569695656554d68d9361d2745d0f6c368d63a4e534ce8b92d2b86d1b26c5b0ed8731d2729d1715c3723c6c6486a198961382e07a91646491a619194951342d0758348c6344c9312c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db69a49249b6936d24934934d2492492492449249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record065 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record065 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record065.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record065.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record065.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 59), (facetIndex 63)]))
 (.leaf ([(facetIndex 65), (facetIndex 73)])))
 (.branch 3
 (.leaf ([(facetIndex 75)]))
 (.leaf ([(facetIndex 76)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 46), (facetIndex 48), (facetIndex 52)]))
 (.leaf ([(facetIndex 58), (facetIndex 60), (facetIndex 64)])))
 (.branch 7
 (.leaf ([(facetIndex 77), (facetIndex 78)]))
 (.leaf ([(facetIndex 79), (facetIndex 80)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "7fb340800000d0051400040041z23;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record065 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record065_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00032.record065" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":4,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":5,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00032.record065" 47

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00032.record065" "{\"ridges\":[[11,290],[20,577],[22,656],[36,290],[44,290],[45,577],[45,584],[46,650],[47,290],[48,594],[49,656],[50,290],[51,290],[52,706],[57,577],[57,584],[58,652],[60,596],[62,656],[64,708],[66,584],[67,656],[68,577],[69,656],[77,594],[78,650],[79,596],[80,652]],\"owners\":[[11,290,[73,75,76],[36,44,47,50,51]],[36,290,[76],[11,44,47,50,51,73,75]],[44,290,[73,75],[11,36,47,50,51,76]],[47,290,[75],[11,36,44,50,51,73,76]],[50,290,[73,75,76],[11,36,44,47,51]],[51,290,[73,76],[11,36,44,47,50,75]],[20,577,[48,52,60,64],[45,57,66,68]],[45,577,[60,64],[20,48,52,57,66,68]],[57,577,[48,52],[20,45,60,64,66,68]],[68,577,[48,52,60,64],[20,45,57,66]],[45,584,[79],[20,57,66,68,77]],[57,584,[77],[20,45,66,68,79]],[66,584,[],[20,45,57,68,77,79]],[22,656,[78,80],[49,62,67,69]],[49,656,[80],[22,62,67,69,78]],[62,656,[78],[22,49,67,69,80]],[67,656,[],[22,49,62,69,78,80]],[69,656,[78,80],[22,49,62,67]],[46,650,[78],[]],[78,650,[46],[]],[48,594,[77],[]],[77,594,[48],[]],[52,706,[],[]],[58,652,[80],[]],[80,652,[58],[]],[60,596,[79],[]],[79,596,[60],[]],[64,708,[],[]]],\"edges\":[[37,[11,36,44,47,50,51,59,63,65,73,75,76]],[41,[20,45,48,52,57,60,64,66,68,77,79]],[43,[22,46,49,52,58,62,64,67,69,78,80]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00032.record065" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00032.record065\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-30,-9],[-30,-29],[-32,-17],[-32,-31],[-1,26,27,28],[-4,28],[-5,26,27],[-8,27],[-11,26,27,28],[-12,26,28],[-2,9,13,17,20],[-6,17,20],[-14,9,13],[-24,9,13,17,20],[-6,31],[-14,29],[-22],[-3,30,32],[-10,32],[-18,30],[-23],[-25,30,32],[-7,30],[-30,7],[-9,29],[-29,9],[-13],[-15,32],[-32,15],[-17,31],[-31,17],[-20],[-16,33],[-19,33],[-21,34],[-26,34],[-27,35],[-28,36],[-7,37],[-9,37],[-15,38],[-17,38],[-39,29,30],[-29,39],[-30,39],[-40,31,32],[-31,40],[-32,40],[-34,41],[-33,41],[-36,42],[-35,42],[-42,43],[-41,43],[-37,-38,44],[-45,39],[-45,40],[-39,-40,45],[-44,-45,46],[-43,-46,47],[-47],[1,4,5,8,11,12,16,19,21,26,27,28],[2,6,9,13,14,17,20,22,24,29,31],[3,7,10,13,15,18,20,23,25,30,32]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":78,\"b\":48},{\"tag\":\"incompatible\",\"a\":78,\"b\":77},{\"tag\":\"incompatible\",\"a\":80,\"b\":60},{\"tag\":\"incompatible\",\"a\":80,\"b\":79},{\"tag\":\"mate\",\"ridge\":290,\"a\":11,\"owners\":[73,75,76]},{\"tag\":\"mate\",\"ridge\":290,\"a\":36,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":290,\"a\":44,\"owners\":[73,75]},{\"tag\":\"mate\",\"ridge\":290,\"a\":47,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":290,\"a\":50,\"owners\":[73,75,76]},{\"tag\":\"mate\",\"ridge\":290,\"a\":51,\"owners\":[73,76]},{\"tag\":\"mate\",\"ridge\":577,\"a\":20,\"owners\":[48,52,60,64]},{\"tag\":\"mate\",\"ridge\":577,\"a\":45,\"owners\":[60,64]},{\"tag\":\"mate\",\"ridge\":577,\"a\":57,\"owners\":[48,52]},{\"tag\":\"mate\",\"ridge\":577,\"a\":68,\"owners\":[48,52,60,64]},{\"tag\":\"mate\",\"ridge\":584,\"a\":45,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":584,\"a\":57,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":584,\"a\":66,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":656,\"a\":22,\"owners\":[78,80]},{\"tag\":\"mate\",\"ridge\":656,\"a\":49,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":656,\"a\":62,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":656,\"a\":67,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":656,\"a\":69,\"owners\":[78,80]},{\"tag\":\"mate\",\"ridge\":650,\"a\":46,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":650,\"a\":78,\"owners\":[46]},{\"tag\":\"mate\",\"ridge\":594,\"a\":48,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":594,\"a\":77,\"owners\":[48]},{\"tag\":\"mate\",\"ridge\":706,\"a\":52,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":652,\"a\":58,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":652,\"a\":80,\"owners\":[58]},{\"tag\":\"mate\",\"ridge\":596,\"a\":60,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":596,\"a\":79,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":708,\"a\":64,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":59,\"full_literals\":[-16,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":63,\"full_literals\":[-19,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":65,\"full_literals\":[-21,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":73,\"full_literals\":[-26,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":75,\"full_literals\":[-27,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":76,\"full_literals\":[-28,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":46,\"full_literals\":[-7,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":48,\"full_literals\":[-9,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":58,\"full_literals\":[-15,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":60,\"full_literals\":[-17,38]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[77,78],\"full_literals\":[-39,29,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":77,\"full_literals\":[-29,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":78,\"full_literals\":[-30,39]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[79,80],\"full_literals\":[-40,31,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":79,\"full_literals\":[-31,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":80,\"full_literals\":[-32,40]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-34,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-33,false,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-36,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-35,false,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-42,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-41,false,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-37,-38,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-45,39,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-45,false,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-39,-40,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":2,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-44,-45,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":4,\"direction\":\"forward\",\"full_literals\":[-43,-46,47],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":4,\"grouped\":true},{\"tag\":\"edge\",\"edge\":37,\"owners\":[11,36,44,47,50,51,59,63,65,73,75,76]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[20,45,48,52,57,60,64,66,68,77,79]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[22,46,49,52,58,62,64,67,69,78,80]}]}"
  "65 2 6 9 14 17 24 29 31 0 27 32 17 63 0\n66 3 7 10 15 18 25 30 32 0 27 32 21 64 0\n67 43 0 53 54 51 52 49 50 38 37 35 36 33 34 6 8 9 5 7 10 62 0\n68 -46 0 67 61 60 0\n69 37 -39 0 39 40 24 26 43 0\n70 -45 0 68 56 57 59 69 55 41 42 29 31 46 0\n71 32 30 0 23 20 19 28 18 22 66 0\n72 39 0 32 27 44 45 16 25 71 3 4 12 14 11 65 0\n73 -40 0 72 70 58 0\n74 -31 0 73 47 0\n75 -32 0 73 48 0\n76 -6 0 74 15 0\n77 -17 0 74 30 0\n78 30 0 75 71 0\n79 -9 0 78 1 0\n80 -29 0 78 2 0\n81 -14 0 79 27 13 0\n82 -24 0 79 27 77 32 14 0\n83 -2 0 79 27 77 32 11 0\n84 0 82 83 77 81 76 79 80 74 65 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record065.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record065.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record065.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record065.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record065 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record065.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record065.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record065.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record065.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record065 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record065_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record065_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record065_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record065_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record065_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record065_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record065_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record065 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record065_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record065_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00032.record065_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00032.record065
