module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow28Part00007Data
public import GraphInputsRow28Part00007Frames
public import GraphInputsRow28Part00007Leaves
public import GraphInputsRow28Part00007Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow28Part00007.record009
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record009
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), (certNat% 5), (certNat% 6), 1152358554653425664, (certNat% 7), (certNat% 8)]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record009_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record009_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record009_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record009_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record009_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record009_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record009_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record009_validity Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record009_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow28Part00007.record009

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow28Part00007.record094
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "4f07c4e87ab1aa6698e6a5a5635a364d8b61d94e338ae1ba1e479391e6c5a95a539695954d58d5352d475534cd2b46d8751db0ea368ce3a4e5334e334ccb31cd4b32cab1ae1b46f0761e4751e2719d1725e0f23d2c1703c4a85a0ea863192629a16158364384e0b81e4a4590e6853152529615154354344d0b41da0cc348ca384c530cd0b12c2b06e0741c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "492492492492492492492492492492492492492492492492491249249249249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record094 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record094 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record094.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record094.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record094.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 49), (facetIndex 50), (facetIndex 55), (facetIndex 64), (facetIndex 81), (facetIndex 100)]))
 (.leaf ([(facetIndex 51), (facetIndex 54), (facetIndex 56), (facetIndex 58), (facetIndex 71), (facetIndex 88), (facetIndex 107)])))
 (.branch 3
 (.leaf ([(facetIndex 53), (facetIndex 57), (facetIndex 73), (facetIndex 90), (facetIndex 109)]))
 (.branch 4
 (.leaf ([(facetIndex 52), (facetIndex 59), (facetIndex 67), (facetIndex 76), (facetIndex 84), (facetIndex 94), (facetIndex 95), (facetIndex 103), (facetIndex 113), (facetIndex 115)]))
 (.leaf ([(facetIndex 70), (facetIndex 75), (facetIndex 87), (facetIndex 92), (facetIndex 106), (facetIndex 111)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 60), (facetIndex 77), (facetIndex 96)]))
 (.leaf ([(facetIndex 61), (facetIndex 65), (facetIndex 72), (facetIndex 78), (facetIndex 82), (facetIndex 89), (facetIndex 93), (facetIndex 97), (facetIndex 101), (facetIndex 108), (facetIndex 112), (facetIndex 114)])))
 (.branch 8
 (.leaf ([(facetIndex 62), (facetIndex 63), (facetIndex 79), (facetIndex 80), (facetIndex 98), (facetIndex 99)]))
 (.branch 9
 (.leaf ([(facetIndex 68), (facetIndex 74), (facetIndex 85), (facetIndex 91), (facetIndex 104), (facetIndex 110)]))
 (.leaf ([(facetIndex 66), (facetIndex 69), (facetIndex 83), (facetIndex 86), (facetIndex 102), (facetIndex 105)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "36364826149839607765336482614983960776534826149839607765312101231z33;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3, 4]
def grouped2_0005 : List Nat := [3, 4]
def grouped2_0006 : List Nat := [5, 6]
def grouped2_0007 : List Nat := [5, 6, 7, 8, 9]
def grouped2_0008 : List Nat := [7]
def grouped2_0009 : List Nat := [7, 8, 9]
def grouped2_0010 : List Nat := [8]
def grouped2_0011 : List Nat := [8, 9]
def grouped2_0012 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record094 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record094_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow28Part00007.record094" "{\"atoms\":[{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"facet\",\"index\":109},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":111},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":10,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow28Part00007.record094" 47

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow28Part00007.record094" "{\"ridges\":[[14,131],[14,162],[16,131],[16,193],[16,194],[17,131],[17,641],[17,642],[25,164],[27,133],[27,193],[27,196],[28,133],[28,641],[28,644],[39,134],[39,162],[41,134],[41,194],[41,196],[42,134],[42,642],[42,644],[57,131],[62,131],[62,162],[63,131],[63,193],[63,194],[66,131],[66,162],[69,131],[69,193],[69,194],[72,162],[72,193],[72,194],[73,131],[73,162],[74,162],[75,193],[75,194],[75,642],[79,133],[79,161],[79,164],[80,193],[80,196],[83,164],[86,133],[86,193],[86,196],[89,164],[89,193],[89,196],[90,164],[91,164],[92,193],[92,196],[92,641],[92,644],[98,162],[99,134],[99,194],[99,196],[102,134],[105,194],[105,196],[108,196],[109,134],[109,162]],\"owners\":[[79,161,[14,66,72,73,74],[25,62,83,89,90,91]],[14,162,[39,98,102,108,109,110],[62,66,72,73,74]],[39,162,[14,62,66,72,73,74],[98,102,108,109,110]],[62,162,[39,102,108,109,110],[14,66,72,73,74,98]],[66,162,[39,98,108,109,110],[14,62,72,73,74,102]],[72,162,[39,98,102,109,110],[14,62,66,73,74,108]],[73,162,[39,98,102,108,110],[14,62,66,72,74,109]],[74,162,[39,98,102,108,109],[14,62,66,72,73,110]],[98,162,[14,66,72,73,74],[39,62,102,108,109,110]],[109,162,[14,62,66,72,74],[39,73,98,102,108,110]],[16,193,[27,80,86,89,92],[63,69,72,75]],[27,193,[16,63,69,72,75],[80,86,89,92]],[63,193,[27,86,89,92],[16,69,72,75,80]],[69,193,[27,80,89,92],[16,63,72,75,86]],[72,193,[27,80,86,92],[16,63,69,75,89]],[75,193,[27,80,86,89],[16,63,69,72,92]],[80,193,[16,69,72,75],[27,63,86,89,92]],[86,193,[16,63,72,75],[27,69,80,89,92]],[89,193,[16,63,69,75],[27,72,80,86,92]],[92,193,[16,63,69,72],[27,75,80,86,89]],[16,194,[41,99,105,108,111],[63,69,72,75]],[41,194,[16,63,69,72,75],[99,105,108,111]],[63,194,[41,105,108,111],[16,69,72,75,99]],[69,194,[41,99,108,111],[16,63,72,75,105]],[72,194,[41,99,105,111],[16,63,69,75,108]],[75,194,[41,99,105,108],[16,63,69,72,111]],[99,194,[16,69,72,75],[41,63,105,108,111]],[105,194,[16,63,72,75],[41,69,99,108,111]],[17,641,[28,88,91,92],[71,74,75]],[28,641,[17,71,74,75],[88,91,92]],[92,641,[17,71,74],[28,75,88,91]],[17,642,[42,107,110,111],[71,74,75]],[42,642,[17,71,74,75],[107,110,111]],[75,642,[42,107,110],[17,71,74,111]],[25,164,[39,98,102,108,109,110],[79,83,89,90,91]],[79,164,[39,102,108,109,110],[25,83,89,90,91,98]],[83,164,[39,98,108,109,110],[25,79,89,90,91,102]],[89,164,[39,98,102,109,110],[25,79,83,90,91,108]],[90,164,[39,98,102,108,110],[25,79,83,89,91,109]],[91,164,[39,98,102,108,109],[25,79,83,89,90,110]],[27,196,[41,99,105,108,111],[80,86,89,92]],[41,196,[27,80,86,89,92],[99,105,108,111]],[80,196,[41,105,108,111],[27,86,89,92,99]],[86,196,[41,99,108,111],[27,80,89,92,105]],[89,196,[41,99,105,111],[27,80,86,92,108]],[92,196,[41,99,105,108],[27,80,86,89,111]],[99,196,[27,86,89,92],[41,80,105,108,111]],[105,196,[27,80,89,92],[41,86,99,108,111]],[108,196,[27,80,86,92],[41,89,99,105,111]],[28,644,[42,107,110,111],[88,91,92]],[42,644,[28,88,91,92],[107,110,111]],[92,644,[42,107,110],[28,88,91,111]]],\"edges\":[[36,[14,25,39,62,66,72,73,74,79,83,89,90,91,98,102,108,109,110]],[39,[16,27,41,63,69,72,75,80,86,89,92,99,105,108,111]],[43,[17,28,42,71,74,75,88,91,92,107,110,111]]],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow28Part00007.record094" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow28Part00007.record094\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-13,-12],[-15,-14],[-16,-14],[-16,-15],[-17,-3],[-19,-2],[-19,-13],[-19,-15],[-19,-17],[-20,-1],[-20,-12],[-20,-14],[-20,-17],[-20,-18],[-20,-19],[-21,-13],[-22,-12],[-22,-21],[-23,-16],[-24,-14],[-24,-16],[-25,-14],[-25,-15],[-25,-23],[-25,-24],[-26,-6],[-26,-21],[-27,-23],[-28,-5],[-28,-22],[-28,-24],[-28,-26],[-29,-21],[-29,-26],[-29,-28],[-30,-10],[-31,-21],[-32,-16],[-32,-25],[-32,-30],[-33,-14],[-33,-16],[-33,-25],[-33,-32],[-34,-14],[-34,-15],[-34,-23],[-34,-24],[-34,-32],[-34,-33],[-35,-9],[-36,-30],[-37,-8],[-37,-31],[-37,-33],[-37,-35],[-38,-7],[-38,-30],[-38,-32],[-38,-35],[-38,-36],[-38,-37],[-1,-2,-3],[-1,-3,-11],[-1,-3,-13],[-1,-3,-15],[-2,-3,-12],[-2,-3,-14],[-2,-3,-18],[-3,-12,-15],[-3,-13,-14],[-3,-13,-18],[-3,-15,-18],[-5,-6,-21],[-6,-21,-24],[-7,-9,-31],[-8,-9,-32],[-9,-31,-32],[-9,-31,-36],[-21,1,14,17,18,19],[-1,7,30,32,35,36,37],[-7,1,12,14,17,18,19],[-12,7,32,35,36,37],[-14,7,30,35,36,37],[-17,7,30,32,36,37],[-18,7,30,32,35,37],[-19,7,30,32,35,36],[-30,1,14,17,18,19],[-36,1,12,14,17,19],[-2,5,22,24,26,29],[-5,2,13,15,17,20],[-13,5,24,26,29],[-15,5,22,26,29],[-17,5,22,24,29],[-20,5,22,24,26],[-22,2,15,17,20],[-24,2,13,17,20],[-26,2,13,15,20],[-29,2,13,15,17],[-2,8,31,33,35,38],[-8,2,13,15,17,20],[-13,8,33,35,38],[-15,8,31,35,38],[-17,8,31,33,38],[-20,8,31,33,35],[-31,2,15,17,20],[-33,2,13,17,20],[-3,6,25,28,29],[-6,3,16,19,20],[-29,3,16,19],[-3,9,34,37,38],[-9,3,16,19,20],[-20,9,34,37],[-4,7,30,32,35,36,37],[-21,7,32,35,36,37],[-23,7,30,35,36,37],[-26,7,30,32,36,37],[-27,7,30,32,35,37],[-28,7,30,32,35,36],[-5,8,31,33,35,38],[-8,5,22,24,26,29],[-22,8,33,35,38],[-24,8,31,35,38],[-26,8,31,33,38],[-29,8,31,33,35],[-31,5,24,26,29],[-33,5,22,26,29],[-35,5,22,24,29],[-6,9,34,37,38],[-9,6,25,28,29],[-29,9,34,37],[-39,10,11,18,27,36],[-40,12,13,21,22,30,31],[-41,14,15,23,24,32,33],[-42,39],[-43,42],[-44,41],[-45,40],[-45,44],[-46,45],[-47,43],[-47,46],[47],[1,4,7,12,14,17,18,19,21,23,26,27,28,30,32,35,36,37],[2,5,8,13,15,17,20,22,24,26,29,31,33,35,38],[3,6,9,16,19,20,25,28,29,34,37,38]],\"atoms\":[{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"facet\",\"index\":109},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":111},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":63,\"b\":62},{\"tag\":\"incompatible\",\"a\":69,\"b\":66},{\"tag\":\"incompatible\",\"a\":71,\"b\":66},{\"tag\":\"incompatible\",\"a\":71,\"b\":69},{\"tag\":\"incompatible\",\"a\":72,\"b\":17},{\"tag\":\"incompatible\",\"a\":74,\"b\":16},{\"tag\":\"incompatible\",\"a\":74,\"b\":63},{\"tag\":\"incompatible\",\"a\":74,\"b\":69},{\"tag\":\"incompatible\",\"a\":74,\"b\":72},{\"tag\":\"incompatible\",\"a\":75,\"b\":14},{\"tag\":\"incompatible\",\"a\":75,\"b\":62},{\"tag\":\"incompatible\",\"a\":75,\"b\":66},{\"tag\":\"incompatible\",\"a\":75,\"b\":72},{\"tag\":\"incompatible\",\"a\":75,\"b\":73},{\"tag\":\"incompatible\",\"a\":75,\"b\":74},{\"tag\":\"incompatible\",\"a\":79,\"b\":63},{\"tag\":\"incompatible\",\"a\":80,\"b\":62},{\"tag\":\"incompatible\",\"a\":80,\"b\":79},{\"tag\":\"incompatible\",\"a\":83,\"b\":71},{\"tag\":\"incompatible\",\"a\":86,\"b\":66},{\"tag\":\"incompatible\",\"a\":86,\"b\":71},{\"tag\":\"incompatible\",\"a\":88,\"b\":66},{\"tag\":\"incompatible\",\"a\":88,\"b\":69},{\"tag\":\"incompatible\",\"a\":88,\"b\":83},{\"tag\":\"incompatible\",\"a\":88,\"b\":86},{\"tag\":\"incompatible\",\"a\":89,\"b\":28},{\"tag\":\"incompatible\",\"a\":89,\"b\":79},{\"tag\":\"incompatible\",\"a\":90,\"b\":83},{\"tag\":\"incompatible\",\"a\":91,\"b\":27},{\"tag\":\"incompatible\",\"a\":91,\"b\":80},{\"tag\":\"incompatible\",\"a\":91,\"b\":86},{\"tag\":\"incompatible\",\"a\":91,\"b\":89},{\"tag\":\"incompatible\",\"a\":92,\"b\":79},{\"tag\":\"incompatible\",\"a\":92,\"b\":89},{\"tag\":\"incompatible\",\"a\":92,\"b\":91},{\"tag\":\"incompatible\",\"a\":98,\"b\":53},{\"tag\":\"incompatible\",\"a\":99,\"b\":79},{\"tag\":\"incompatible\",\"a\":102,\"b\":71},{\"tag\":\"incompatible\",\"a\":102,\"b\":88},{\"tag\":\"incompatible\",\"a\":102,\"b\":98},{\"tag\":\"incompatible\",\"a\":105,\"b\":66},{\"tag\":\"incompatible\",\"a\":105,\"b\":71},{\"tag\":\"incompatible\",\"a\":105,\"b\":88},{\"tag\":\"incompatible\",\"a\":105,\"b\":102},{\"tag\":\"incompatible\",\"a\":107,\"b\":66},{\"tag\":\"incompatible\",\"a\":107,\"b\":69},{\"tag\":\"incompatible\",\"a\":107,\"b\":83},{\"tag\":\"incompatible\",\"a\":107,\"b\":86},{\"tag\":\"incompatible\",\"a\":107,\"b\":102},{\"tag\":\"incompatible\",\"a\":107,\"b\":105},{\"tag\":\"incompatible\",\"a\":108,\"b\":42},{\"tag\":\"incompatible\",\"a\":109,\"b\":98},{\"tag\":\"incompatible\",\"a\":110,\"b\":41},{\"tag\":\"incompatible\",\"a\":110,\"b\":99},{\"tag\":\"incompatible\",\"a\":110,\"b\":105},{\"tag\":\"incompatible\",\"a\":110,\"b\":108},{\"tag\":\"incompatible\",\"a\":111,\"b\":39},{\"tag\":\"incompatible\",\"a\":111,\"b\":98},{\"tag\":\"incompatible\",\"a\":111,\"b\":102},{\"tag\":\"incompatible\",\"a\":111,\"b\":108},{\"tag\":\"incompatible\",\"a\":111,\"b\":109},{\"tag\":\"incompatible\",\"a\":111,\"b\":110},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[14,16,17]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[14,17,57]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[14,17,63]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[14,17,69]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[16,17,62]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[16,17,66]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[16,17,73]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[17,62,69]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[17,63,66]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[17,63,73]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[17,69,73]},{\"tag\":\"three\",\"ridge\":133,\"vertices\":[27,28,79]},{\"tag\":\"three\",\"ridge\":133,\"vertices\":[28,79,86]},{\"tag\":\"three\",\"ridge\":134,\"vertices\":[39,42,99]},{\"tag\":\"three\",\"ridge\":134,\"vertices\":[41,42,102]},{\"tag\":\"three\",\"ridge\":134,\"vertices\":[42,99,102]},{\"tag\":\"three\",\"ridge\":134,\"vertices\":[42,99,109]},{\"tag\":\"mate\",\"ridge\":161,\"a\":79,\"owners\":[14,66,72,73,74]},{\"tag\":\"mate\",\"ridge\":162,\"a\":14,\"owners\":[39,98,102,108,109,110]},{\"tag\":\"mate\",\"ridge\":162,\"a\":39,\"owners\":[14,62,66,72,73,74]},{\"tag\":\"mate\",\"ridge\":162,\"a\":62,\"owners\":[39,102,108,109,110]},{\"tag\":\"mate\",\"ridge\":162,\"a\":66,\"owners\":[39,98,108,109,110]},{\"tag\":\"mate\",\"ridge\":162,\"a\":72,\"owners\":[39,98,102,109,110]},{\"tag\":\"mate\",\"ridge\":162,\"a\":73,\"owners\":[39,98,102,108,110]},{\"tag\":\"mate\",\"ridge\":162,\"a\":74,\"owners\":[39,98,102,108,109]},{\"tag\":\"mate\",\"ridge\":162,\"a\":98,\"owners\":[14,66,72,73,74]},{\"tag\":\"mate\",\"ridge\":162,\"a\":109,\"owners\":[14,62,66,72,74]},{\"tag\":\"mate\",\"ridge\":193,\"a\":16,\"owners\":[27,80,86,89,92]},{\"tag\":\"mate\",\"ridge\":193,\"a\":27,\"owners\":[16,63,69,72,75]},{\"tag\":\"mate\",\"ridge\":193,\"a\":63,\"owners\":[27,86,89,92]},{\"tag\":\"mate\",\"ridge\":193,\"a\":69,\"owners\":[27,80,89,92]},{\"tag\":\"mate\",\"ridge\":193,\"a\":72,\"owners\":[27,80,86,92]},{\"tag\":\"mate\",\"ridge\":193,\"a\":75,\"owners\":[27,80,86,89]},{\"tag\":\"mate\",\"ridge\":193,\"a\":80,\"owners\":[16,69,72,75]},{\"tag\":\"mate\",\"ridge\":193,\"a\":86,\"owners\":[16,63,72,75]},{\"tag\":\"mate\",\"ridge\":193,\"a\":89,\"owners\":[16,63,69,75]},{\"tag\":\"mate\",\"ridge\":193,\"a\":92,\"owners\":[16,63,69,72]},{\"tag\":\"mate\",\"ridge\":194,\"a\":16,\"owners\":[41,99,105,108,111]},{\"tag\":\"mate\",\"ridge\":194,\"a\":41,\"owners\":[16,63,69,72,75]},{\"tag\":\"mate\",\"ridge\":194,\"a\":63,\"owners\":[41,105,108,111]},{\"tag\":\"mate\",\"ridge\":194,\"a\":69,\"owners\":[41,99,108,111]},{\"tag\":\"mate\",\"ridge\":194,\"a\":72,\"owners\":[41,99,105,111]},{\"tag\":\"mate\",\"ridge\":194,\"a\":75,\"owners\":[41,99,105,108]},{\"tag\":\"mate\",\"ridge\":194,\"a\":99,\"owners\":[16,69,72,75]},{\"tag\":\"mate\",\"ridge\":194,\"a\":105,\"owners\":[16,63,72,75]},{\"tag\":\"mate\",\"ridge\":641,\"a\":17,\"owners\":[28,88,91,92]},{\"tag\":\"mate\",\"ridge\":641,\"a\":28,\"owners\":[17,71,74,75]},{\"tag\":\"mate\",\"ridge\":641,\"a\":92,\"owners\":[17,71,74]},{\"tag\":\"mate\",\"ridge\":642,\"a\":17,\"owners\":[42,107,110,111]},{\"tag\":\"mate\",\"ridge\":642,\"a\":42,\"owners\":[17,71,74,75]},{\"tag\":\"mate\",\"ridge\":642,\"a\":75,\"owners\":[42,107,110]},{\"tag\":\"mate\",\"ridge\":164,\"a\":25,\"owners\":[39,98,102,108,109,110]},{\"tag\":\"mate\",\"ridge\":164,\"a\":79,\"owners\":[39,102,108,109,110]},{\"tag\":\"mate\",\"ridge\":164,\"a\":83,\"owners\":[39,98,108,109,110]},{\"tag\":\"mate\",\"ridge\":164,\"a\":89,\"owners\":[39,98,102,109,110]},{\"tag\":\"mate\",\"ridge\":164,\"a\":90,\"owners\":[39,98,102,108,110]},{\"tag\":\"mate\",\"ridge\":164,\"a\":91,\"owners\":[39,98,102,108,109]},{\"tag\":\"mate\",\"ridge\":196,\"a\":27,\"owners\":[41,99,105,108,111]},{\"tag\":\"mate\",\"ridge\":196,\"a\":41,\"owners\":[27,80,86,89,92]},{\"tag\":\"mate\",\"ridge\":196,\"a\":80,\"owners\":[41,105,108,111]},{\"tag\":\"mate\",\"ridge\":196,\"a\":86,\"owners\":[41,99,108,111]},{\"tag\":\"mate\",\"ridge\":196,\"a\":89,\"owners\":[41,99,105,111]},{\"tag\":\"mate\",\"ridge\":196,\"a\":92,\"owners\":[41,99,105,108]},{\"tag\":\"mate\",\"ridge\":196,\"a\":99,\"owners\":[27,86,89,92]},{\"tag\":\"mate\",\"ridge\":196,\"a\":105,\"owners\":[27,80,89,92]},{\"tag\":\"mate\",\"ridge\":196,\"a\":108,\"owners\":[27,80,86,92]},{\"tag\":\"mate\",\"ridge\":644,\"a\":28,\"owners\":[42,107,110,111]},{\"tag\":\"mate\",\"ridge\":644,\"a\":42,\"owners\":[28,88,91,92]},{\"tag\":\"mate\",\"ridge\":644,\"a\":92,\"owners\":[42,107,110]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[53,57,73,90,109],\"full_literals\":[-39,10,11,18,27,36]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[62,63,79,80,98,99],\"full_literals\":[-40,12,13,21,22,30,31]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[66,69,83,86,102,105],\"full_literals\":[-41,14,15,23,24,32,33]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-42,39,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-43,false,42],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-44,false,41],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-45,40,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-45,false,44],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-46,false,45],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-47,43,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-47,false,46],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":10,\"grouped\":true},{\"tag\":\"edge\",\"edge\":36,\"owners\":[14,25,39,62,66,72,73,74,79,83,89,90,91,98,102,108,109,110]},{\"tag\":\"edge\",\"edge\":39,\"owners\":[16,27,41,63,69,72,75,80,86,89,92,99,105,108,111]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[17,28,42,71,74,75,88,91,92,107,110,111]}]}"
  "147 43 0 143 141 0\n148 46 0 143 142 0\n149 42 0 147 136 0\n150 45 0 148 140 0\n151 39 0 149 135 0\n152 40 0 150 138 0\n153 44 0 150 139 0\n154 41 0 153 137 0\n155 19 20 28 29 37 38 34 25 16 3 0 112 109 146 0\n156 -16 0 154 3 4 19 21 38 42 134 0\n157 -25 0 154 22 23 24 25 39 43 134 0\n158 -34 0 154 45 46 47 48 49 50 134 0\n159 7 37 30 32 35 36 0 81 114 118 115 83 116 84 86 117 85 87 119 144 0\n160 -38 0 57 58 59 60 61 62 159 0\n161 -26 20 28 37 19 0 160 158 157 156 26 34 108 130 146 0\n162 -3 23 -1 17 32 14 0 154 10 65 66 63 97 107 134 0\n163 3 20 28 37 19 0 156 157 158 160 110 155 0\n164 17 -7 35 18 14 28 37 19 12 0 158 160 82 10 161 163 65 66 111 63 97 101 107 91 99 76 96 145 0\n165 -17 28 37 19 0 160 158 157 156 5 13 110 112 109 146 0\n166 36 7 35 32 18 14 28 37 19 0 151 165 159 36 88 10 163 64 162 132 28 0\n167 -36 14 21 28 37 19 12 0 160 158 152 165 52 89 10 163 65 66 111 63 79 96 133 0\n168 9 28 37 19 0 160 158 157 156 111 129 131 113 146 0\n169 -32 21 -9 12 0 160 152 51 40 44 77 78 102 122 133 0\n170 -18 28 37 19 0 160 168 51 165 14 161 163 69 72 73 96 106 99 97 101 107 91 145 0\n171 14 21 28 37 19 12 0 168 169 170 51 165 167 166 164 0\n172 -14 28 37 19 0 160 168 51 165 2 12 20 41 161 163 68 71 96 106 99 101 91 145 0\n173 28 37 19 12 0 157 160 165 168 51 170 172 171 16 18 27 33 37 80 130 10 74 75 90 121 127 93 145 0\n174 5 29 22 24 26 0 160 90 121 95 126 92 127 93 94 128 145 0\n175 -28 0 29 30 31 32 35 174 0\n176 8 35 31 33 0 160 100 120 105 124 103 123 125 102 122 104 145 0\n177 -37 0 53 54 55 56 176 0\n178 -19 0 6 7 8 9 15 96 98 99 97 91 174 0\n179 -17 0 177 175 178 165 0\n180 12 0 178 175 177 173 0\n181 -13 0 180 1 0\n182 -20 0 180 11 0\n183 -22 0 180 17 0\n184 -26 0 182 175 177 178 161 0\n185 3 0 182 175 177 178 163 0\n186 -2 0 185 180 67 0\n187 -15 0 185 180 70 0\n188 -29 0 186 181 187 179 99 0\n189 -24 0 186 182 179 181 97 0\n190 -5 0 186 182 187 179 181 91 0\n191 0 190 188 183 189 184 174 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record094.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record094.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record094.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record094.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record094 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record094.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record094.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record094.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record094.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record094 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record094_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record094_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record094_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record094_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record094_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record094_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record094_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record094 Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record094_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record094_validity Papers.RationalityTen.CompactReplay.GraphInputsRow28Part00007.record094_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow28Part00007.record094
