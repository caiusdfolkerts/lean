module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow23Part00014Data
public import GraphInputsRow23Part00014Frames
public import GraphInputsRow23Part00014Leaves
public import GraphInputsRow23Part00014Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00014.record093
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record093
def vertexColumn : Fields := ⟨10, hexnat% "b293ab19c659956a38ce0fac94e6c5715655568d3343db0dc358d5392d4b8ad2b2ac6b86d1b26c5bc1d8791e2729c6785c9715e0f23c4f0bc1f4d132a28ca0ea86518c6499160d931a24c90e685514c5495150d68350cc348d130ce0b22c4b0ac1b81d0721c4709c17"⟩
def kindColumn : Fields := ⟨3, hexnat% "492492492492492492492492492492492489249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "402001440000000000000", hexnat% "e00004000000000000", hexnat% "1c0000000000000000000", hexnat% "381c000007c000000000", hexnat% "a05022002000000000000", hexnat% "1c000000000000000", 2805953674084352, 842173130318282752]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record093_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record093_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record093_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record093_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record093_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record093_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record093_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record093_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record093_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00014.record093

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00014.record043
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "5713caa95635a2e4b91e1783e74729aa5594e565355355362d1743db0ce3a4d532ce8b4acab86d1b26c5b0ed4731e2749ca719d1725c3783d0f13d544b11ca88d28a8560b81ea8551346294a51951525454554342d0768330e2328c9314e0b0ac1b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "12492492492492492492492492492492492449249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record043 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record043 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record043.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record043.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record043.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 48), (facetIndex 56), (facetIndex 61), (facetIndex 65), (facetIndex 68), (facetIndex 71)]))
 (.leaf ([(facetIndex 44), (facetIndex 52), (facetIndex 76), (facetIndex 79)])))
 (.branch 3
 (.leaf ([(facetIndex 53), (facetIndex 62), (facetIndex 69), (facetIndex 70)]))
 (.branch 4
 (.leaf ([(facetIndex 41), (facetIndex 58), (facetIndex 66)]))
 (.leaf ([(facetIndex 73), (facetIndex 77), (facetIndex 78)])))))
 (.branch 8
 (.branch 6
 (.leaf ([(facetIndex 39), (facetIndex 42), (facetIndex 45), (facetIndex 55), (facetIndex 57), (facetIndex 59)]))
 (.branch 7
 (.leaf ([(facetIndex 35), (facetIndex 40), (facetIndex 63), (facetIndex 81)]))
 (.leaf ([(facetIndex 37), (facetIndex 47), (facetIndex 49), (facetIndex 51), (facetIndex 54)]))))
 (.branch 9
 (.leaf ([(facetIndex 36), (facetIndex 60), (facetIndex 72), (facetIndex 74), (facetIndex 75), (facetIndex 80)]))
 (.branch 10
 (.leaf ([(facetIndex 38), (facetIndex 64), (facetIndex 67)]))
 (.leaf ([(facetIndex 43), (facetIndex 46), (facetIndex 50)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "6814418848022093096208535057217a707a51a53659786z23;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 11
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [2, 3, 4]
def grouped2_0007 : List Nat := [3]
def grouped2_0008 : List Nat := [3, 4]
def grouped2_0009 : List Nat := [4]
def grouped2_0010 : List Nat := [5]
def grouped2_0011 : List Nat := [5, 6, 7]
def grouped2_0012 : List Nat := [5, 6, 7, 8, 9, 10]
def grouped2_0013 : List Nat := [6]
def grouped2_0014 : List Nat := [6, 7]
def grouped2_0015 : List Nat := [7]
def grouped2_0016 : List Nat := [8]
def grouped2_0017 : List Nat := [8, 9, 10]
def grouped2_0018 : List Nat := [9]
def grouped2_0019 : List Nat := [9, 10]
def grouped2_0020 : List Nat := [10]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record043 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record043_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00014.record043" "{\"atoms\":[{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group\",\"kind\":2,\"index\":10},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0014\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0019\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0019\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0017\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0017\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0012\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":6,\"list_name\":\"grouped2_0012\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":10,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00014.record043" 73

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00014.record043" "{\"ridges\":[[14,41],[24,273],[24,321],[31,642],[34,324],[35,11],[35,13],[50,11],[50,273],[54,11],[56,321],[58,162],[64,273],[67,41],[69,41],[71,273],[71,321],[77,70],[78,70],[78,324],[79,522],[79,642]],\"owners\":[[35,13,[13,14,15,62],[0,37,61,63]],[77,70,[3,35,41,46],[28,45,73,78]],[78,70,[3,35,41,45],[28,46,73,77]],[79,522,[6,37,51],[29,54,76]],[58,162,[31,79],[9,42,52,55]],[31,642,[12,54,57,59],[79]],[79,642,[12,57,59],[31,54]],[24,321,[19,46,63,66],[56,68,71]],[56,321,[19,63,66],[24,46,68,71]],[71,321,[19,46,63,66],[24,56,68]],[34,324,[19,46,63,66],[78,81]],[78,324,[19,63,66],[34,46,81]]],\"edges\":[[40,[19,24,34,46,56,63,66,68,71,78,81]]],\"groupings\":[2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00014.record043" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00014.record043\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-12,-11],[-14,-1],[-14,-11],[-15,-12],[-16,-14],[-17,-12],[-17,-14],[-17,-16],[-19,-14],[-20,-11],[-20,-12],[-20,-14],[-20,-15],[-20,-16],[-21,-2],[-23,-12],[-23,-13],[-23,-15],[-23,-21],[-23,-22],[-24,-23],[-25,-13],[-25,-21],[-25,-22],[-25,-24],[-27,-18],[-27,-25],[-28,-23],[-30,-3],[-30,-27],[-30,-29],[-31,-30],[-32,-17],[-32,-23],[-34,-12],[-34,-20],[-35,-7],[-35,-17],[-35,-32],[-35,-34],[-36,-17],[-36,-20],[-36,-35],[-37,-6],[-37,-12],[-37,-23],[-37,-26],[-37,-32],[-37,-33],[-37,-34],[-38,-23],[-38,-35],[-39,-18],[-40,-37],[-42,-14],[-42,-35],[-42,-37],[-43,-14],[-44,-4],[-44,-15],[-44,-17],[-44,-23],[-45,-17],[-45,-20],[-45,-23],[-46,-42],[-46,-45],[-48,-23],[-49,-22],[-49,-27],[-49,-39],[-50,-14],[-50,-21],[-50,-34],[-50,-35],[-50,-37],[-51,-35],[-51,-44],[-51,-50],[-11,-23,-27],[-11,4,5,6,33],[-47,1,11,16,20],[-48,1,11,16,19],[-5,-37,-39],[-49,2,13,24],[-30,9,49],[-9,3,27,29,31],[-49,3,29,31],[-8,-23,-35],[-23,-35,-41],[-8,7,20,34,36],[-28,7,34,36],[-41,7,20,34,36],[-10,7,20,34,36],[-48,7,34,36],[-52,18,25,46,49],[-53,26,33,39,40],[-54,16,30,36],[-55,43,47,48],[-56,11,15,34,51],[-57,13,21,22,24,27],[-58,12,32,42,44,45,50],[-59,14,35,37],[-60,17,20,23],[-61,52],[-62,54],[-62,55],[-63,53],[-63,62],[-64,61],[-64,63],[-65,56],[-65,57],[-66,65],[-67,59,60],[-68,59],[-68,60],[-69,58,68],[-70,58],[-69,67],[-70,68],[-71,66,70],[-72,66],[-71,69],[-72,70],[-73,64,72],[-73,71],[73],[7,8,10,20,28,34,36,38,41,48,51]],\"atoms\":[{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group\",\"index\":10,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":36,\"b\":35},{\"tag\":\"incompatible\",\"a\":38,\"b\":3},{\"tag\":\"incompatible\",\"a\":38,\"b\":35},{\"tag\":\"incompatible\",\"a\":40,\"b\":36},{\"tag\":\"incompatible\",\"a\":41,\"b\":38},{\"tag\":\"incompatible\",\"a\":43,\"b\":36},{\"tag\":\"incompatible\",\"a\":43,\"b\":38},{\"tag\":\"incompatible\",\"a\":43,\"b\":41},{\"tag\":\"incompatible\",\"a\":45,\"b\":38},{\"tag\":\"incompatible\",\"a\":46,\"b\":35},{\"tag\":\"incompatible\",\"a\":46,\"b\":36},{\"tag\":\"incompatible\",\"a\":46,\"b\":38},{\"tag\":\"incompatible\",\"a\":46,\"b\":40},{\"tag\":\"incompatible\",\"a\":46,\"b\":41},{\"tag\":\"incompatible\",\"a\":47,\"b\":6},{\"tag\":\"incompatible\",\"a\":50,\"b\":36},{\"tag\":\"incompatible\",\"a\":50,\"b\":37},{\"tag\":\"incompatible\",\"a\":50,\"b\":40},{\"tag\":\"incompatible\",\"a\":50,\"b\":47},{\"tag\":\"incompatible\",\"a\":50,\"b\":49},{\"tag\":\"incompatible\",\"a\":51,\"b\":50},{\"tag\":\"incompatible\",\"a\":52,\"b\":37},{\"tag\":\"incompatible\",\"a\":52,\"b\":47},{\"tag\":\"incompatible\",\"a\":52,\"b\":49},{\"tag\":\"incompatible\",\"a\":52,\"b\":51},{\"tag\":\"incompatible\",\"a\":54,\"b\":44},{\"tag\":\"incompatible\",\"a\":54,\"b\":52},{\"tag\":\"incompatible\",\"a\":56,\"b\":50},{\"tag\":\"incompatible\",\"a\":58,\"b\":12},{\"tag\":\"incompatible\",\"a\":58,\"b\":54},{\"tag\":\"incompatible\",\"a\":58,\"b\":57},{\"tag\":\"incompatible\",\"a\":59,\"b\":58},{\"tag\":\"incompatible\",\"a\":60,\"b\":43},{\"tag\":\"incompatible\",\"a\":60,\"b\":50},{\"tag\":\"incompatible\",\"a\":63,\"b\":36},{\"tag\":\"incompatible\",\"a\":63,\"b\":46},{\"tag\":\"incompatible\",\"a\":64,\"b\":19},{\"tag\":\"incompatible\",\"a\":64,\"b\":43},{\"tag\":\"incompatible\",\"a\":64,\"b\":60},{\"tag\":\"incompatible\",\"a\":64,\"b\":63},{\"tag\":\"incompatible\",\"a\":66,\"b\":43},{\"tag\":\"incompatible\",\"a\":66,\"b\":46},{\"tag\":\"incompatible\",\"a\":66,\"b\":64},{\"tag\":\"incompatible\",\"a\":67,\"b\":15},{\"tag\":\"incompatible\",\"a\":67,\"b\":36},{\"tag\":\"incompatible\",\"a\":67,\"b\":50},{\"tag\":\"incompatible\",\"a\":67,\"b\":53},{\"tag\":\"incompatible\",\"a\":67,\"b\":60},{\"tag\":\"incompatible\",\"a\":67,\"b\":62},{\"tag\":\"incompatible\",\"a\":67,\"b\":63},{\"tag\":\"incompatible\",\"a\":68,\"b\":50},{\"tag\":\"incompatible\",\"a\":68,\"b\":64},{\"tag\":\"incompatible\",\"a\":69,\"b\":44},{\"tag\":\"incompatible\",\"a\":70,\"b\":67},{\"tag\":\"incompatible\",\"a\":72,\"b\":38},{\"tag\":\"incompatible\",\"a\":72,\"b\":64},{\"tag\":\"incompatible\",\"a\":72,\"b\":67},{\"tag\":\"incompatible\",\"a\":73,\"b\":38},{\"tag\":\"incompatible\",\"a\":74,\"b\":13},{\"tag\":\"incompatible\",\"a\":74,\"b\":40},{\"tag\":\"incompatible\",\"a\":74,\"b\":43},{\"tag\":\"incompatible\",\"a\":74,\"b\":50},{\"tag\":\"incompatible\",\"a\":75,\"b\":43},{\"tag\":\"incompatible\",\"a\":75,\"b\":46},{\"tag\":\"incompatible\",\"a\":75,\"b\":50},{\"tag\":\"incompatible\",\"a\":76,\"b\":72},{\"tag\":\"incompatible\",\"a\":76,\"b\":75},{\"tag\":\"incompatible\",\"a\":78,\"b\":50},{\"tag\":\"incompatible\",\"a\":79,\"b\":49},{\"tag\":\"incompatible\",\"a\":79,\"b\":54},{\"tag\":\"incompatible\",\"a\":79,\"b\":69},{\"tag\":\"incompatible\",\"a\":80,\"b\":38},{\"tag\":\"incompatible\",\"a\":80,\"b\":47},{\"tag\":\"incompatible\",\"a\":80,\"b\":63},{\"tag\":\"incompatible\",\"a\":80,\"b\":64},{\"tag\":\"incompatible\",\"a\":80,\"b\":67},{\"tag\":\"incompatible\",\"a\":81,\"b\":64},{\"tag\":\"incompatible\",\"a\":81,\"b\":74},{\"tag\":\"incompatible\",\"a\":81,\"b\":80},{\"tag\":\"three\",\"ridge\":11,\"vertices\":[35,50,54]},{\"tag\":\"mate\",\"ridge\":13,\"a\":35,\"owners\":[13,14,15,62]},{\"tag\":\"mate\",\"ridge\":70,\"a\":77,\"owners\":[3,35,41,46]},{\"tag\":\"mate\",\"ridge\":70,\"a\":78,\"owners\":[3,35,41,45]},{\"tag\":\"three\",\"ridge\":41,\"vertices\":[14,67,69]},{\"tag\":\"mate\",\"ridge\":522,\"a\":79,\"owners\":[6,37,51]},{\"tag\":\"mate\",\"ridge\":162,\"a\":58,\"owners\":[31,79]},{\"tag\":\"mate\",\"ridge\":642,\"a\":31,\"owners\":[12,54,57,59]},{\"tag\":\"mate\",\"ridge\":642,\"a\":79,\"owners\":[12,57,59]},{\"tag\":\"three\",\"ridge\":273,\"vertices\":[24,50,64]},{\"tag\":\"three\",\"ridge\":273,\"vertices\":[50,64,71]},{\"tag\":\"mate\",\"ridge\":321,\"a\":24,\"owners\":[19,46,63,66]},{\"tag\":\"mate\",\"ridge\":321,\"a\":56,\"owners\":[19,63,66]},{\"tag\":\"mate\",\"ridge\":321,\"a\":71,\"owners\":[19,46,63,66]},{\"tag\":\"mate\",\"ridge\":324,\"a\":34,\"owners\":[19,46,63,66]},{\"tag\":\"mate\",\"ridge\":324,\"a\":78,\"owners\":[19,63,66]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[44,52,76,79],\"full_literals\":[-52,18,25,46,49]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[53,62,69,70],\"full_literals\":[-53,26,33,39,40]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[41,58,66],\"full_literals\":[-54,16,30,36]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[73,77,78],\"full_literals\":[-55,43,47,48]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[35,40,63,81],\"full_literals\":[-56,11,15,34,51]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[37,47,49,51,54],\"full_literals\":[-57,13,21,22,24,27]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[36,60,72,74,75,80],\"full_literals\":[-58,12,32,42,44,45,50]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[38,64,67],\"full_literals\":[-59,14,35,37]},{\"tag\":\"group_or\",\"kind\":2,\"index\":10,\"members\":[43,46,50],\"full_literals\":[-60,17,20,23]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-61,false,52],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0008\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-62,54,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-62,false,55],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-63,53,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-63,false,62],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-64,61,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-64,false,63],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0013\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0014\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-65,56,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0013\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0014\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-65,false,57],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-66,false,65],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped2_0018\",\"right_name\":\"grouped2_0020\",\"joined_name\":\"grouped2_0019\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-67,59,60],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped2_0018\",\"right_name\":\"grouped2_0020\",\"joined_name\":\"grouped2_0019\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-68,59,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped2_0018\",\"right_name\":\"grouped2_0020\",\"joined_name\":\"grouped2_0019\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-68,false,60],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped2_0016\",\"right_name\":\"grouped2_0019\",\"joined_name\":\"grouped2_0017\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-69,58,68],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped2_0016\",\"right_name\":\"grouped2_0019\",\"joined_name\":\"grouped2_0017\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-70,58,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped2_0016\",\"right_name\":\"grouped2_0019\",\"joined_name\":\"grouped2_0017\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-69,false,67],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped2_0016\",\"right_name\":\"grouped2_0019\",\"joined_name\":\"grouped2_0017\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-70,false,68],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0012\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-71,66,70],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0012\",\"a\":2,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-72,66,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0012\",\"a\":3,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-71,false,69],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0012\",\"a\":3,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-72,false,70],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-73,64,72],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-73,false,71],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":10,\"grouped\":true},{\"tag\":\"edge\",\"edge\":40,\"owners\":[19,24,34,46,56,63,66,68,71,78,81]}]}"
  "p cnf 73 129\n-12 -11 0\n-14 -1 0\n-14 -11 0\n-15 -12 0\n-16 -14 0\n-17 -12 0\n-17 -14 0\n-17 -16 0\n-19 -14 0\n-20 -11 0\n-20 -12 0\n-20 -14 0\n-20 -15 0\n-20 -16 0\n-21 -2 0\n-23 -12 0\n-23 -13 0\n-23 -15 0\n-23 -21 0\n-23 -22 0\n-24 -23 0\n-25 -13 0\n-25 -21 0\n-25 -22 0\n-25 -24 0\n-27 -18 0\n-27 -25 0\n-28 -23 0\n-30 -3 0\n-30 -27 0\n-30 -29 0\n-31 -30 0\n-32 -17 0\n-32 -23 0\n-34 -12 0\n-34 -20 0\n-35 -7 0\n-35 -17 0\n-35 -32 0\n-35 -34 0\n-36 -17 0\n-36 -20 0\n-36 -35 0\n-37 -6 0\n-37 -12 0\n-37 -23 0\n-37 -26 0\n-37 -32 0\n-37 -33 0\n-37 -34 0\n-38 -23 0\n-38 -35 0\n-39 -18 0\n-40 -37 0\n-42 -14 0\n-42 -35 0\n-42 -37 0\n-43 -14 0\n-44 -4 0\n-44 -15 0\n-44 -17 0\n-44 -23 0\n-45 -17 0\n-45 -20 0\n-45 -23 0\n-46 -42 0\n-46 -45 0\n-48 -23 0\n-49 -22 0\n-49 -27 0\n-49 -39 0\n-50 -14 0\n-50 -21 0\n-50 -34 0\n-50 -35 0\n-50 -37 0\n-51 -35 0\n-51 -44 0\n-51 -50 0\n-11 -23 -27 0\n-11 4 5 6 33 0\n-47 1 11 16 20 0\n-48 1 11 16 19 0\n-5 -37 -39 0\n-49 2 13 24 0\n-30 9 49 0\n-9 3 27 29 31 0\n-49 3 29 31 0\n-8 -23 -35 0\n-23 -35 -41 0\n-8 7 20 34 36 0\n-28 7 34 36 0\n-41 7 20 34 36 0\n-10 7 20 34 36 0\n-48 7 34 36 0\n-52 18 25 46 49 0\n-53 26 33 39 40 0\n-54 16 30 36 0\n-55 43 47 48 0\n-56 11 15 34 51 0\n-57 13 21 22 24 27 0\n-58 12 32 42 44 45 50 0\n-59 14 35 37 0\n-60 17 20 23 0\n-61 52 0\n-62 54 0\n-62 55 0\n-63 53 0\n-63 62 0\n-64 61 0\n-64 63 0\n-65 56 0\n-65 57 0\n-66 65 0\n-67 59 60 0\n-68 59 0\n-68 60 0\n-69 58 68 0\n-70 58 0\n-69 67 0\n-70 68 0\n-71 66 70 0\n-72 66 0\n-71 69 0\n-72 70 0\n-73 64 72 0\n-73 71 0\n73 0\n7 8 10 20 28 34 36 38 41 48 51 0\n"
  "130 71 0 128 127 0\n131 69 0 130 124 0\n132 67 0 131 120 0\n133 -30 49 0 29 30 31 32 86 87 0\n134 -25 -57 0 22 23 24 25 27 101 0\n135 24 13 -49 -57 0 70 69 85 101 15 0\n136 -17 50 44 35 12 -70 0 121 116 119 7 33 63 103 102 57 0\n137 -20 -51 -70 0 79 78 77 121 116 119 11 12 64 103 48 57 102 0\n138 -17 -51 -70 0 79 78 77 6 136 0\n139 -51 -70 0 121 117 116 119 77 78 79 137 138 104 16 34 46 65 102 103 55 0\n140 12 35 44 50 20 -70 0 121 117 116 119 136 104 34 46 65 102 103 55 0\n141 -12 -72 0 125 139 123 114 112 1 4 35 100 0\n142 44 50 20 -72 0 141 125 121 117 119 140 38 39 56 104 102 65 0\n143 -44 20 -60 0 61 62 104 0\n144 -50 -59 0 72 75 76 103 0\n145 20 -72 0 125 121 116 144 117 143 142 0\n146 -72 0 123 125 114 112 139 145 10 13 36 100 0\n147 64 0 146 128 126 0\n148 61 0 147 110 0\n149 63 0 147 111 0\n150 52 0 148 105 0\n151 53 0 149 108 0\n152 62 0 149 109 0\n153 54 0 152 106 0\n154 55 0 152 107 0\n155 -30 0 29 31 32 133 88 0\n156 -20 0 155 153 14 42 98 0\n157 -17 0 155 153 8 41 98 0\n158 -14 48 0 156 154 2 3 5 58 82 99 0\n159 -35 -23 0 156 68 51 28 37 40 43 77 89 90 94 129 0\n160 -23 44 50 0 156 130 131 150 16 17 19 20 21 34 46 65 68 158 159 140 103 122 116 114 118 113 102 134 135 101 66 26 96 0\n161 -37 44 50 0 131 156 157 130 151 150 160 104 117 121 122 114 113 134 118 45 47 48 49 54 57 97 102 53 71 67 96 0\n162 -14 0 2 3 5 9 158 83 0\n163 -35 0 156 37 40 43 52 77 95 92 93 91 94 129 0\n164 -37 50 0 157 156 151 130 44 46 47 49 50 54 161 104 97 59 60 78 117 84 81 121 100 122 112 114 0\n165 50 0 162 163 132 157 156 164 103 115 143 104 160 0\n166 -21 0 165 73 0\n167 -34 0 165 74 0\n168 -51 0 165 79 0\n169 -59 0 165 144 0\n170 60 0 169 132 115 0\n171 -68 0 169 116 0\n172 23 0 170 156 157 104 0\n173 -70 0 171 121 0\n174 -13 0 172 17 0\n175 -15 0 172 18 0\n176 -22 0 172 20 0\n177 -24 0 172 21 0\n178 66 0 173 130 122 0\n179 65 0 178 114 0\n180 56 0 179 112 0\n181 57 0 179 113 0\n182 11 0 180 175 168 167 100 0\n183 27 0 181 174 176 177 166 101 0\n184 0 182 183 172 80 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record043.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record043.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record043.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record043.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record043 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record043.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record043.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record043.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record043.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record043 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record043_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record043_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record043_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record043_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record043_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record043_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record043_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record043 Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record043_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record043_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record043_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00014.record043

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00014.record076
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "b19c6a9a9635a362d8ce8b92e1b91e2785eb15c5a9695356352d4cd8b52d1b51d2745db0dc3a8e9334e332cccb8ad2b1ad1b26c5bc1d8791d2729c6785d1715e0f23d4c0f14a0ea86518c6898960d90e1382e079490e685514c5894950d50d1342d0768350cc388c930cd0b12c2b06e0741c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "492492492492492492492492492492492492492449249249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record076 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record076 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record076.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record076.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record076.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 44), (facetIndex 54), (facetIndex 56), (facetIndex 57), (facetIndex 58), (facetIndex 59)]))
 (.leaf ([(facetIndex 60), (facetIndex 63), (facetIndex 64), (facetIndex 66), (facetIndex 67)])))
 (.branch 3
 (.leaf ([(facetIndex 68), (facetIndex 70), (facetIndex 71), (facetIndex 72), (facetIndex 73)]))
 (.branch 4
 (.leaf ([(facetIndex 47), (facetIndex 49), (facetIndex 51), (facetIndex 53), (facetIndex 65), (facetIndex 79), (facetIndex 93)]))
 (.leaf ([(facetIndex 74), (facetIndex 77), (facetIndex 78), (facetIndex 80), (facetIndex 81)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 82), (facetIndex 84), (facetIndex 85), (facetIndex 86), (facetIndex 87)]))
 (.leaf ([(facetIndex 48), (facetIndex 50), (facetIndex 62), (facetIndex 76), (facetIndex 90)])))
 (.branch 8
 (.leaf ([(facetIndex 52), (facetIndex 91), (facetIndex 92), (facetIndex 94), (facetIndex 95)]))
 (.branch 9
 (.leaf ([(facetIndex 45), (facetIndex 46), (facetIndex 61), (facetIndex 75), (facetIndex 89)]))
 (.leaf ([(facetIndex 43), (facetIndex 55), (facetIndex 69), (facetIndex 83), (facetIndex 88)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "77377689555595443446842222921131168100009037363638809z2b;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [2, 3, 4]
def grouped2_0007 : List Nat := [3]
def grouped2_0008 : List Nat := [3, 4]
def grouped2_0009 : List Nat := [4]
def grouped2_0010 : List Nat := [5]
def grouped2_0011 : List Nat := [5, 6]
def grouped2_0012 : List Nat := [5, 6, 7, 8, 9]
def grouped2_0013 : List Nat := [6]
def grouped2_0014 : List Nat := [7]
def grouped2_0015 : List Nat := [7, 8, 9]
def grouped2_0016 : List Nat := [8]
def grouped2_0017 : List Nat := [8, 9]
def grouped2_0018 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record076 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record076_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00014.record076" "{\"atoms\":[{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0017\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0012\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":10,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00014.record076" 67

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00014.record076" "{\"ridges\":[[16,131],[26,133],[26,641],[32,14],[38,642],[41,28],[41,44],[52,262],[55,131],[64,641],[65,131],[66,131],[67,641],[68,28],[69,133],[70,28],[71,44],[72,44],[75,52],[76,52],[78,641],[79,641],[80,133],[81,641],[83,28],[87,14],[87,44],[88,14],[92,642],[92,644],[93,642],[95,642],[95,644]],\"owners\":[[52,262,[32,37,84,86],[5,46,50,53,94]],[26,641,[16,64,65,67],[78,79,81]],[64,641,[26,79,81],[16,65,67,78]],[67,641,[26,78,79],[16,64,65,81]],[78,641,[16,65,67],[26,64,79,81]],[79,641,[16,64,67],[26,65,78,81]],[81,641,[16,64,65],[26,67,78,79]],[38,642,[16,64,65,67],[92,93,95]],[92,642,[16,65,67],[38,64,93,95]],[93,642,[16,64,67],[38,65,92,95]],[95,642,[16,64,65],[38,67,92,93]],[75,52,[33,41,90],[21,76,89]],[76,52,[33,41,89],[21,75,90]],[92,644,[26,79,81],[38,78,93,95]],[95,644,[26,78,79],[38,81,92,93]]],\"edges\":[[43,[16,26,38,64,65,67,78,79,81,92,93,95]]],\"groupings\":[2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00014.record076" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00014.record076\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-13,-8],[-15,-14],[-17,-16],[-18,-14],[-19,-14],[-22,-14],[-24,-15],[-24,-23],[-25,-24],[-26,-24],[-27,-24],[-29,-8],[-29,-24],[-32,-8],[-32,-24],[-33,-8],[-33,-24],[-34,-28],[-35,-13],[-35,-21],[-36,-8],[-36,-24],[-38,-4],[-38,-9],[-38,-10],[-38,-37],[-39,-38],[-40,-38],[-41,-38],[-42,-11],[-42,-12],[-42,-28],[-43,-5],[-43,-37],[-43,-39],[-43,-40],[-43,-41],[-44,-38],[-45,-38],[-46,-8],[-46,-18],[-46,-43],[-47,-8],[-47,-43],[-49,-35],[-49,-43],[-50,-8],[-50,-43],[-3,-42,-43],[-1,-14,-21],[-14,-20,-21],[-2,-24,-35],[-13,3,5,39,41],[-2,1,19,20,22],[-19,2,34,36],[-22,2,33,34],[-33,1,20,22],[-34,1,19,22],[-36,1,19,20],[-6,1,19,20,22],[-47,1,20,22],[-48,1,19,22],[-50,1,19,20],[-7,-23,-38],[-7,-25,-38],[-7,-26,-42],[-7,-27,-42],[-30,4,7,45],[-31,4,7,44],[-47,2,34,36],[-50,2,33,34],[-51,15,18,19,21,22],[-52,23,25,26,27,28],[-53,29,32,33,35,36],[-54,37,39,40,41,42],[-55,11,12,17,31,45],[-56,13,46,47,49,50],[-57,9,10,16,30,44],[-58,8,14,24,38,43],[-59,51],[-60,53],[-61,52],[-61,60],[-62,59],[-62,61],[-63,54],[-63,55],[-64,57],[-64,58],[-65,56],[-65,64],[-66,63],[-66,65],[-67,62],[-67,66],[67],[1,2,6,19,20,22,33,34,36,47,48,50]],\"atoms\":[{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":52,\"b\":43},{\"tag\":\"incompatible\",\"a\":60,\"b\":55},{\"tag\":\"incompatible\",\"a\":62,\"b\":61},{\"tag\":\"incompatible\",\"a\":63,\"b\":55},{\"tag\":\"incompatible\",\"a\":64,\"b\":55},{\"tag\":\"incompatible\",\"a\":67,\"b\":55},{\"tag\":\"incompatible\",\"a\":69,\"b\":60},{\"tag\":\"incompatible\",\"a\":69,\"b\":68},{\"tag\":\"incompatible\",\"a\":70,\"b\":69},{\"tag\":\"incompatible\",\"a\":71,\"b\":69},{\"tag\":\"incompatible\",\"a\":72,\"b\":69},{\"tag\":\"incompatible\",\"a\":74,\"b\":43},{\"tag\":\"incompatible\",\"a\":74,\"b\":69},{\"tag\":\"incompatible\",\"a\":77,\"b\":43},{\"tag\":\"incompatible\",\"a\":77,\"b\":69},{\"tag\":\"incompatible\",\"a\":78,\"b\":43},{\"tag\":\"incompatible\",\"a\":78,\"b\":69},{\"tag\":\"incompatible\",\"a\":79,\"b\":73},{\"tag\":\"incompatible\",\"a\":80,\"b\":52},{\"tag\":\"incompatible\",\"a\":80,\"b\":66},{\"tag\":\"incompatible\",\"a\":81,\"b\":43},{\"tag\":\"incompatible\",\"a\":81,\"b\":69},{\"tag\":\"incompatible\",\"a\":83,\"b\":33},{\"tag\":\"incompatible\",\"a\":83,\"b\":45},{\"tag\":\"incompatible\",\"a\":83,\"b\":46},{\"tag\":\"incompatible\",\"a\":83,\"b\":82},{\"tag\":\"incompatible\",\"a\":84,\"b\":83},{\"tag\":\"incompatible\",\"a\":85,\"b\":83},{\"tag\":\"incompatible\",\"a\":86,\"b\":83},{\"tag\":\"incompatible\",\"a\":87,\"b\":48},{\"tag\":\"incompatible\",\"a\":87,\"b\":50},{\"tag\":\"incompatible\",\"a\":87,\"b\":73},{\"tag\":\"incompatible\",\"a\":88,\"b\":37},{\"tag\":\"incompatible\",\"a\":88,\"b\":82},{\"tag\":\"incompatible\",\"a\":88,\"b\":84},{\"tag\":\"incompatible\",\"a\":88,\"b\":85},{\"tag\":\"incompatible\",\"a\":88,\"b\":86},{\"tag\":\"incompatible\",\"a\":89,\"b\":83},{\"tag\":\"incompatible\",\"a\":90,\"b\":83},{\"tag\":\"incompatible\",\"a\":91,\"b\":43},{\"tag\":\"incompatible\",\"a\":91,\"b\":63},{\"tag\":\"incompatible\",\"a\":91,\"b\":88},{\"tag\":\"incompatible\",\"a\":92,\"b\":43},{\"tag\":\"incompatible\",\"a\":92,\"b\":88},{\"tag\":\"incompatible\",\"a\":94,\"b\":80},{\"tag\":\"incompatible\",\"a\":94,\"b\":88},{\"tag\":\"incompatible\",\"a\":95,\"b\":43},{\"tag\":\"incompatible\",\"a\":95,\"b\":88},{\"tag\":\"three\",\"ridge\":14,\"vertices\":[32,87,88]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[16,55,66]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[55,65,66]},{\"tag\":\"three\",\"ridge\":133,\"vertices\":[26,69,80]},{\"tag\":\"mate\",\"ridge\":262,\"a\":52,\"owners\":[32,37,84,86]},{\"tag\":\"mate\",\"ridge\":641,\"a\":26,\"owners\":[16,64,65,67]},{\"tag\":\"mate\",\"ridge\":641,\"a\":64,\"owners\":[26,79,81]},{\"tag\":\"mate\",\"ridge\":641,\"a\":67,\"owners\":[26,78,79]},{\"tag\":\"mate\",\"ridge\":641,\"a\":78,\"owners\":[16,65,67]},{\"tag\":\"mate\",\"ridge\":641,\"a\":79,\"owners\":[16,64,67]},{\"tag\":\"mate\",\"ridge\":641,\"a\":81,\"owners\":[16,64,65]},{\"tag\":\"mate\",\"ridge\":642,\"a\":38,\"owners\":[16,64,65,67]},{\"tag\":\"mate\",\"ridge\":642,\"a\":92,\"owners\":[16,65,67]},{\"tag\":\"mate\",\"ridge\":642,\"a\":93,\"owners\":[16,64,67]},{\"tag\":\"mate\",\"ridge\":642,\"a\":95,\"owners\":[16,64,65]},{\"tag\":\"three\",\"ridge\":28,\"vertices\":[41,68,83]},{\"tag\":\"three\",\"ridge\":28,\"vertices\":[41,70,83]},{\"tag\":\"three\",\"ridge\":44,\"vertices\":[41,71,87]},{\"tag\":\"three\",\"ridge\":44,\"vertices\":[41,72,87]},{\"tag\":\"mate\",\"ridge\":52,\"a\":75,\"owners\":[33,41,90]},{\"tag\":\"mate\",\"ridge\":52,\"a\":76,\"owners\":[33,41,89]},{\"tag\":\"mate\",\"ridge\":644,\"a\":92,\"owners\":[26,79,81]},{\"tag\":\"mate\",\"ridge\":644,\"a\":95,\"owners\":[26,78,79]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[60,63,64,66,67],\"full_literals\":[-51,15,18,19,21,22]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[68,70,71,72,73],\"full_literals\":[-52,23,25,26,27,28]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[74,77,78,80,81],\"full_literals\":[-53,29,32,33,35,36]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[82,84,85,86,87],\"full_literals\":[-54,37,39,40,41,42]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[48,50,62,76,90],\"full_literals\":[-55,11,12,17,31,45]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[52,91,92,94,95],\"full_literals\":[-56,13,46,47,49,50]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[45,46,61,75,89],\"full_literals\":[-57,9,10,16,30,44]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[43,55,69,83,88],\"full_literals\":[-58,8,14,24,38,43]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-59,false,51],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-60,false,53],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-61,52,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-61,false,60],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-62,59,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-62,false,61],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-63,54,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-63,false,55],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0016\",\"right_name\":\"grouped2_0018\",\"joined_name\":\"grouped2_0017\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-64,57,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0016\",\"right_name\":\"grouped2_0018\",\"joined_name\":\"grouped2_0017\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-64,false,58],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-65,56,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-65,false,64],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0012\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-66,63,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0012\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-66,false,65],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-67,62,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-67,false,66],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":10,\"grouped\":true},{\"tag\":\"edge\",\"edge\":43,\"owners\":[16,26,38,64,65,67,78,79,81,92,93,95]}]}"
  "p cnf 67 97\n-13 -8 0\n-15 -14 0\n-17 -16 0\n-18 -14 0\n-19 -14 0\n-22 -14 0\n-24 -15 0\n-24 -23 0\n-25 -24 0\n-26 -24 0\n-27 -24 0\n-29 -8 0\n-29 -24 0\n-32 -8 0\n-32 -24 0\n-33 -8 0\n-33 -24 0\n-34 -28 0\n-35 -13 0\n-35 -21 0\n-36 -8 0\n-36 -24 0\n-38 -4 0\n-38 -9 0\n-38 -10 0\n-38 -37 0\n-39 -38 0\n-40 -38 0\n-41 -38 0\n-42 -11 0\n-42 -12 0\n-42 -28 0\n-43 -5 0\n-43 -37 0\n-43 -39 0\n-43 -40 0\n-43 -41 0\n-44 -38 0\n-45 -38 0\n-46 -8 0\n-46 -18 0\n-46 -43 0\n-47 -8 0\n-47 -43 0\n-49 -35 0\n-49 -43 0\n-50 -8 0\n-50 -43 0\n-3 -42 -43 0\n-1 -14 -21 0\n-14 -20 -21 0\n-2 -24 -35 0\n-13 3 5 39 41 0\n-2 1 19 20 22 0\n-19 2 34 36 0\n-22 2 33 34 0\n-33 1 20 22 0\n-34 1 19 22 0\n-36 1 19 20 0\n-6 1 19 20 22 0\n-47 1 20 22 0\n-48 1 19 22 0\n-50 1 19 20 0\n-7 -23 -38 0\n-7 -25 -38 0\n-7 -26 -42 0\n-7 -27 -42 0\n-30 4 7 45 0\n-31 4 7 44 0\n-47 2 34 36 0\n-50 2 33 34 0\n-51 15 18 19 21 22 0\n-52 23 25 26 27 28 0\n-53 29 32 33 35 36 0\n-54 37 39 40 41 42 0\n-55 11 12 17 31 45 0\n-56 13 46 47 49 50 0\n-57 9 10 16 30 44 0\n-58 8 14 24 38 43 0\n-59 51 0\n-60 53 0\n-61 52 0\n-61 60 0\n-62 59 0\n-62 61 0\n-63 54 0\n-63 55 0\n-64 57 0\n-64 58 0\n-65 56 0\n-65 64 0\n-66 63 0\n-66 65 0\n-67 62 0\n-67 66 0\n67 0\n1 2 6 19 20 22 33 34 36 47 48 50 0\n"
  "98 62 0 96 94 0\n99 66 0 96 95 0\n100 59 0 98 84 0\n101 61 0 98 85 0\n102 63 0 99 92 0\n103 65 0 99 93 0\n104 51 0 100 80 0\n105 52 0 101 82 0\n106 60 0 101 83 0\n107 54 0 102 86 0\n108 55 0 102 87 0\n109 56 0 103 90 0\n110 64 0 103 91 0\n111 53 0 106 81 0\n112 57 0 110 88 0\n113 58 0 110 89 0\n114 -14 0 104 2 4 5 6 72 51 50 63 59 61 57 54 60 62 58 97 0\n115 -38 40 7 0 107 112 108 23 24 25 26 27 29 38 39 68 69 75 78 30 31 3 76 0\n116 -8 0 109 111 1 12 14 16 21 40 43 47 77 74 45 0\n117 -38 23 0 107 105 26 27 28 29 115 75 65 32 66 67 73 0\n118 -24 23 0 105 111 109 104 7 9 10 11 13 15 17 22 73 74 18 19 20 45 52 71 70 56 55 77 72 41 0\n119 -43 0 107 109 33 34 35 36 37 42 44 46 48 75 77 49 53 0\n120 -38 0 28 117 115 64 0\n121 24 0 120 113 114 116 119 79 0\n122 -23 0 121 8 0\n123 0 121 122 118 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record076.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record076.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record076.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record076.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record076 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record076.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record076.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record076.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record076.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record076 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record076_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record076_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record076_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record076_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record076_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record076_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record076_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record076 Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record076_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record076_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record076_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00014.record076

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00014.record085
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "15a4eac6a98e6558d6a3a2e4b8ae8791e1783e56539b16a5395553568d8b52d2b61d4745d0f6c370ea368d6338cd34cf0ba2d4b8acab86c5b0ee4751e2749c6785d1725c3743c8f13d524a91aa18c6298568382e079514a519a14c5294558342d0768350cc348ca344c5382d0b0ac1b81c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "92492492492492492492492492492492492492492491249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record085 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record085 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record085.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record085.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record085.data.quota

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record085 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record085_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00014.record085" "{\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":94}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00014.record085" 39

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00014.record085" "{\"ridges\":[[12,131],[14,131],[14,193],[14,194],[16,131],[16,641],[21,161],[22,193],[23,641],[26,321],[31,162],[32,194],[33,644],[36,322],[52,131],[55,131],[55,641],[61,131],[62,641],[63,131],[63,193],[63,194],[64,641],[69,161],[72,641],[73,193],[76,161],[76,641],[77,193],[77,641],[79,321],[84,162],[87,644],[88,194],[90,162],[90,194],[91,162],[91,644],[92,194],[92,644],[94,322]],\"owners\":[[21,161,[12,52,59,61,62],[69,75,76]],[69,161,[12,59,61,62],[21,52,75,76]],[76,161,[12,52,59,61],[21,62,69,75]],[31,162,[12,52,59,61,62],[84,90,91]],[84,162,[12,59,61,62],[31,52,90,91]],[90,162,[12,52,61,62],[31,59,84,91]],[91,162,[12,52,59,61],[31,62,84,90]],[14,193,[22,73,75,77],[58,59,63,64]],[22,193,[14,58,59,63,64],[73,75,77]],[63,193,[22,73,75,77],[14,58,59,64]],[73,193,[14,59,63,64],[22,58,75,77]],[77,193,[14,58,59,63],[22,64,73,75]],[14,194,[32,88,90,92],[58,59,63,64]],[32,194,[14,58,59,63,64],[88,90,92]],[63,194,[32,88,90,92],[14,58,59,64]],[88,194,[14,59,63,64],[32,58,90,92]],[90,194,[14,58,63,64],[32,59,88,92]],[92,194,[14,58,59,63],[32,64,88,90]],[26,321,[15,47,54,60,63],[74,79]],[79,321,[15,47,60,63],[26,54,74]],[36,322,[15,47,54,60,63],[89,94]],[94,322,[15,47,60,63],[36,54,89]],[16,641,[23,72,76,77],[55,62,64]],[23,641,[16,55,62,64],[72,76,77]],[55,641,[23,76,77],[16,62,64,72]],[62,641,[23,72,77],[16,55,64,76]],[64,641,[23,72,76],[16,55,62,77]],[72,641,[16,62,64],[23,55,76,77]],[76,641,[16,55,64],[23,62,72,77]],[77,641,[16,55,62],[23,64,72,76]],[33,644,[23,72,76,77],[87,91,92]],[87,644,[23,76,77],[33,72,91,92]],[91,644,[23,72,77],[33,76,87,92]],[92,644,[23,72,76],[33,77,87,91]]],\"edges\":[[36,[12,21,31,52,59,61,62,69,75,76,84,90,91]],[39,[14,22,32,58,59,63,64,73,75,77,88,90,92]],[40,[15,26,36,47,54,60,63,74,79,89,94]],[43,[16,23,33,55,62,64,72,76,77,87,91,92]]],\"groupings\":[]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00014.record085" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00014.record085\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-16,-14],[-17,-3],[-17,-13],[-17,-15],[-18,-4],[-18,-16],[-19,-17],[-21,-2],[-21,-18],[-22,-20],[-22,-21],[-23,-1],[-23,-14],[-23,-18],[-23,-20],[-23,-21],[-27,-17],[-28,-7],[-28,-25],[-29,-6],[-29,-26],[-29,-28],[-30,-28],[-30,-29],[-35,-17],[-37,-10],[-37,-34],[-37,-36],[-38,-37],[-1,-2,-4],[-1,-2,-16],[-1,-4,-22],[-1,-16,-22],[-2,-4,-14],[-2,-4,-20],[-2,-16,-20],[-4,-14,-22],[-5,1,14,18,20,21],[-24,1,18,20,21],[-29,1,14,18,20],[-9,1,14,18,20,21],[-32,1,18,20,21],[-36,1,14,20,21],[-37,1,14,18,20],[-2,6,26,28,30],[-6,2,17,18,22,23],[-22,6,26,28,30],[-26,2,18,22,23],[-30,2,17,18,22],[-2,10,34,36,38],[-10,2,17,18,22,23],[-22,10,34,36,38],[-34,2,18,22,23],[-36,2,17,22,23],[-38,2,17,18,22],[-8,3,13,15,19,22],[-31,3,13,19,22],[-12,3,13,15,19,22],[-39,3,13,19,22],[-4,7,25,29,30],[-7,4,16,21,23],[-16,7,29,30],[-21,7,25,30],[-23,7,25,29],[-25,4,21,23],[-29,4,16,23],[-30,4,16,21],[-11,7,25,29,30],[-33,7,29,30],[-37,7,25,30],[-38,7,25,29],[1,5,9,14,18,20,21,24,28,29,32,36,37],[2,6,10,17,18,22,23,26,28,30,34,36,38],[3,8,12,13,15,19,22,27,31,35,39],[4,7,11,16,21,23,25,29,30,33,37,38]],\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":94}],\"rules\":[{\"tag\":\"incompatible\",\"a\":55,\"b\":52},{\"tag\":\"incompatible\",\"a\":58,\"b\":15},{\"tag\":\"incompatible\",\"a\":58,\"b\":47},{\"tag\":\"incompatible\",\"a\":58,\"b\":54},{\"tag\":\"incompatible\",\"a\":59,\"b\":16},{\"tag\":\"incompatible\",\"a\":59,\"b\":55},{\"tag\":\"incompatible\",\"a\":60,\"b\":58},{\"tag\":\"incompatible\",\"a\":62,\"b\":14},{\"tag\":\"incompatible\",\"a\":62,\"b\":59},{\"tag\":\"incompatible\",\"a\":63,\"b\":61},{\"tag\":\"incompatible\",\"a\":63,\"b\":62},{\"tag\":\"incompatible\",\"a\":64,\"b\":12},{\"tag\":\"incompatible\",\"a\":64,\"b\":52},{\"tag\":\"incompatible\",\"a\":64,\"b\":59},{\"tag\":\"incompatible\",\"a\":64,\"b\":61},{\"tag\":\"incompatible\",\"a\":64,\"b\":62},{\"tag\":\"incompatible\",\"a\":74,\"b\":58},{\"tag\":\"incompatible\",\"a\":75,\"b\":23},{\"tag\":\"incompatible\",\"a\":75,\"b\":72},{\"tag\":\"incompatible\",\"a\":76,\"b\":22},{\"tag\":\"incompatible\",\"a\":76,\"b\":73},{\"tag\":\"incompatible\",\"a\":76,\"b\":75},{\"tag\":\"incompatible\",\"a\":77,\"b\":75},{\"tag\":\"incompatible\",\"a\":77,\"b\":76},{\"tag\":\"incompatible\",\"a\":89,\"b\":58},{\"tag\":\"incompatible\",\"a\":91,\"b\":32},{\"tag\":\"incompatible\",\"a\":91,\"b\":88},{\"tag\":\"incompatible\",\"a\":91,\"b\":90},{\"tag\":\"incompatible\",\"a\":92,\"b\":91},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[12,14,16]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[12,14,55]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[12,16,63]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[12,55,63]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[14,16,52]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[14,16,61]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[14,55,61]},{\"tag\":\"three\",\"ridge\":131,\"vertices\":[16,52,63]},{\"tag\":\"mate\",\"ridge\":161,\"a\":21,\"owners\":[12,52,59,61,62]},{\"tag\":\"mate\",\"ridge\":161,\"a\":69,\"owners\":[12,59,61,62]},{\"tag\":\"mate\",\"ridge\":161,\"a\":76,\"owners\":[12,52,59,61]},{\"tag\":\"mate\",\"ridge\":162,\"a\":31,\"owners\":[12,52,59,61,62]},{\"tag\":\"mate\",\"ridge\":162,\"a\":84,\"owners\":[12,59,61,62]},{\"tag\":\"mate\",\"ridge\":162,\"a\":90,\"owners\":[12,52,61,62]},{\"tag\":\"mate\",\"ridge\":162,\"a\":91,\"owners\":[12,52,59,61]},{\"tag\":\"mate\",\"ridge\":193,\"a\":14,\"owners\":[22,73,75,77]},{\"tag\":\"mate\",\"ridge\":193,\"a\":22,\"owners\":[14,58,59,63,64]},{\"tag\":\"mate\",\"ridge\":193,\"a\":63,\"owners\":[22,73,75,77]},{\"tag\":\"mate\",\"ridge\":193,\"a\":73,\"owners\":[14,59,63,64]},{\"tag\":\"mate\",\"ridge\":193,\"a\":77,\"owners\":[14,58,59,63]},{\"tag\":\"mate\",\"ridge\":194,\"a\":14,\"owners\":[32,88,90,92]},{\"tag\":\"mate\",\"ridge\":194,\"a\":32,\"owners\":[14,58,59,63,64]},{\"tag\":\"mate\",\"ridge\":194,\"a\":63,\"owners\":[32,88,90,92]},{\"tag\":\"mate\",\"ridge\":194,\"a\":88,\"owners\":[14,59,63,64]},{\"tag\":\"mate\",\"ridge\":194,\"a\":90,\"owners\":[14,58,63,64]},{\"tag\":\"mate\",\"ridge\":194,\"a\":92,\"owners\":[14,58,59,63]},{\"tag\":\"mate\",\"ridge\":321,\"a\":26,\"owners\":[15,47,54,60,63]},{\"tag\":\"mate\",\"ridge\":321,\"a\":79,\"owners\":[15,47,60,63]},{\"tag\":\"mate\",\"ridge\":322,\"a\":36,\"owners\":[15,47,54,60,63]},{\"tag\":\"mate\",\"ridge\":322,\"a\":94,\"owners\":[15,47,60,63]},{\"tag\":\"mate\",\"ridge\":641,\"a\":16,\"owners\":[23,72,76,77]},{\"tag\":\"mate\",\"ridge\":641,\"a\":23,\"owners\":[16,55,62,64]},{\"tag\":\"mate\",\"ridge\":641,\"a\":55,\"owners\":[23,76,77]},{\"tag\":\"mate\",\"ridge\":641,\"a\":62,\"owners\":[23,72,77]},{\"tag\":\"mate\",\"ridge\":641,\"a\":64,\"owners\":[23,72,76]},{\"tag\":\"mate\",\"ridge\":641,\"a\":72,\"owners\":[16,62,64]},{\"tag\":\"mate\",\"ridge\":641,\"a\":76,\"owners\":[16,55,64]},{\"tag\":\"mate\",\"ridge\":641,\"a\":77,\"owners\":[16,55,62]},{\"tag\":\"mate\",\"ridge\":644,\"a\":33,\"owners\":[23,72,76,77]},{\"tag\":\"mate\",\"ridge\":644,\"a\":87,\"owners\":[23,76,77]},{\"tag\":\"mate\",\"ridge\":644,\"a\":91,\"owners\":[23,72,77]},{\"tag\":\"mate\",\"ridge\":644,\"a\":92,\"owners\":[23,72,76]},{\"tag\":\"edge\",\"edge\":36,\"owners\":[12,21,31,52,59,61,62,69,75,76,84,90,91]},{\"tag\":\"edge\",\"edge\":39,\"owners\":[14,22,32,58,59,63,64,73,75,77,88,90,92]},{\"tag\":\"edge\",\"edge\":40,\"owners\":[15,26,36,47,54,60,63,74,79,89,94]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[16,23,33,55,62,64,72,76,77,87,91,92]}]}"
  "p cnf 39 75\n-16 -14 0\n-17 -3 0\n-17 -13 0\n-17 -15 0\n-18 -4 0\n-18 -16 0\n-19 -17 0\n-21 -2 0\n-21 -18 0\n-22 -20 0\n-22 -21 0\n-23 -1 0\n-23 -14 0\n-23 -18 0\n-23 -20 0\n-23 -21 0\n-27 -17 0\n-28 -7 0\n-28 -25 0\n-29 -6 0\n-29 -26 0\n-29 -28 0\n-30 -28 0\n-30 -29 0\n-35 -17 0\n-37 -10 0\n-37 -34 0\n-37 -36 0\n-38 -37 0\n-1 -2 -4 0\n-1 -2 -16 0\n-1 -4 -22 0\n-1 -16 -22 0\n-2 -4 -14 0\n-2 -4 -20 0\n-2 -16 -20 0\n-4 -14 -22 0\n-5 1 14 18 20 21 0\n-24 1 18 20 21 0\n-29 1 14 18 20 0\n-9 1 14 18 20 21 0\n-32 1 18 20 21 0\n-36 1 14 20 21 0\n-37 1 14 18 20 0\n-2 6 26 28 30 0\n-6 2 17 18 22 23 0\n-22 6 26 28 30 0\n-26 2 18 22 23 0\n-30 2 17 18 22 0\n-2 10 34 36 38 0\n-10 2 17 18 22 23 0\n-22 10 34 36 38 0\n-34 2 18 22 23 0\n-36 2 17 22 23 0\n-38 2 17 18 22 0\n-8 3 13 15 19 22 0\n-31 3 13 19 22 0\n-12 3 13 15 19 22 0\n-39 3 13 19 22 0\n-4 7 25 29 30 0\n-7 4 16 21 23 0\n-16 7 29 30 0\n-21 7 25 30 0\n-23 7 25 29 0\n-25 4 21 23 0\n-29 4 16 23 0\n-30 4 16 21 0\n-11 7 25 29 30 0\n-33 7 29 30 0\n-37 7 25 30 0\n-38 7 25 29 0\n1 5 9 14 18 20 21 24 28 29 32 36 37 0\n2 6 10 17 18 22 23 26 28 30 34 36 38 0\n3 8 12 13 15 19 22 27 31 35 39 0\n4 7 11 16 21 23 25 29 30 33 37 38 0\n"
  "76 17 22 2 23 28 18 0 48 53 54 55 51 46 49 73 0\n77 22 2 18 23 28 0 76 2 3 4 7 17 25 57 59 56 58 74 0\n78 7 30 25 29 0 60 69 70 71 64 63 68 62 75 0\n79 -28 0 18 19 22 23 78 0\n80 4 30 16 29 21 23 0 61 65 78 0\n81 20 24 1 14 36 37 29 21 18 0 79 42 38 41 72 0\n82 -20 -4 23 18 0 79 10 35 77 0\n83 1 14 36 20 37 29 21 18 0 39 81 0\n84 -1 -4 23 18 0 79 30 32 77 0\n85 -14 -4 23 18 0 79 34 37 77 0\n86 -4 37 29 21 23 18 0 82 84 85 43 83 0\n87 16 4 29 21 23 0 67 80 0\n88 -20 -16 23 18 0 79 10 36 77 0\n89 1 20 14 37 29 21 18 0 43 83 0\n90 37 29 18 21 23 0 79 86 87 1 88 89 31 33 77 0\n91 -37 23 18 0 79 26 27 28 29 50 52 77 0\n92 -29 23 18 0 79 20 21 24 45 47 77 0\n93 29 23 18 37 0 79 90 8 11 77 0\n94 23 18 0 91 92 93 0\n95 18 0 79 94 12 13 15 16 39 42 43 38 41 44 40 72 0\n96 -4 0 95 5 0\n97 -16 0 95 6 0\n98 -21 0 95 9 0\n99 -23 0 95 14 0\n100 -29 0 97 96 99 66 0\n101 0 97 100 96 98 99 87 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record085.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record085.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record085.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record085.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record085 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record085.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record085.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record085.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record085.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record085 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record085_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record085_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record085_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record085_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record085_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record085_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record085_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record085 Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record085_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record085_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00014.record085_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00014.record085
