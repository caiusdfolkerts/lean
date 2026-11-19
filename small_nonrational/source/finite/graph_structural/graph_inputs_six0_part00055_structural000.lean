module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsSix0Part00055Data
public import GraphInputsSix0Part00055Frames
public import GraphInputsSix0Part00055Leaves
public import GraphInputsSix0Part00055Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsSix0Part00055.record063
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record063
def vertexColumn : Fields := ⟨10, hexnat% "9d6739765b5d5735755b3f0fa374dbe50eca719c1f3923aa9a6687ae1ac6718e6c5a9665a364d876a398e338ae1ba1e4789e1783e1e785b15c5c56354d475a358d3361d4745de0ec370f138cd331ce8b62ccb86d1b16f07a1d8791d4731e2749c6785d1715c3783d0f23c4f0bc1f3306c0f0ca1a83a1a43919615454351342d0746384d130cc4b0ac1b"⟩
def kindColumn : Fields := ⟨3, hexnat% "2492492491a6d34da6db6db6db4d36da4db4926d249b6924da4936db6da49a6da489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [1, 2, 3, 4]
def candidates : List (Fin raw.n) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩, ⟨102, by decide⟩, ⟨103, by decide⟩, ⟨104, by decide⟩, ⟨105, by decide⟩, ⟨106, by decide⟩, ⟨107, by decide⟩, ⟨108, by decide⟩, ⟨109, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffef7fff5effdffeffffeffffff", hexnat% "a100000000001000000", 144132780261900288, hexnat% "1080000000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffff7fffffffff8ebffffffffff", 1974722883485696, hexnat% "80000000000100000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffeffffffff1d7fffffffffffff", 16176929861514821632, hexnat% "1000000000200000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffff7fffffffff8e7ffffffffff", 1979120929996800, hexnat% "80000000000100000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ffeffffffff1cffffffffffffff", 16212958658533785600, hexnat% "1000000000200000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffffffffff1e78f3fe2fbfffff", 7788822528, 1983518976507904, 16248987455552749568]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffffffffeffff8f3fe2fffffff", hexnat% "1000000001d0000000", 1983518976507904]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffffffffef1e7ffffe2fffffff", hexnat% "1000000001d0000000", 16248987455552749568]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .size 4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨98, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨99, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨100, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨101, by decide⟩ c11 c5
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨102, by decide⟩ c12 c4
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨103, by decide⟩ c13 c3
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨104, by decide⟩ c14 c0
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨105, by decide⟩ c15 c0
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨106, by decide⟩ c16 c2
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨107, by decide⟩ c17 c1
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨108, by decide⟩ c18 c0
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨109, by decide⟩ c19 c0
  c20
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record063_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record063_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record063_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record063_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record063_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record063_certificates, Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record063_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record063_validity Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record063_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsSix0Part00055.record063

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsSix0Part00055.record003
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3a5e372ecb72bb56b5ab69da3e739ba6d95e4f8fa3d8edd56b5a75b96d59d5e575573e4f32f4b7670dc1f07ae1a96658d61da2e4b86e4785e0fae17259936479e16a539695654d51d58d3362d4b46d4749d1743de0ec370e63a4d9334c7352e2b4ad1b0ef07a1d8731d2719e1745c9715c3783c4f1a85a8990e0b81e3446916685616252550d0b41d88c6314d0b12c2b06e0741c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "492492492492492492492491b69b6da4924db49269269a49249b69b49249249a492492249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record003 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record003 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record003.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record003.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record003.data.quota

def groupMembers4 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 1
 (.leaf ([(facetIndex 94), (facetIndex 95), (facetIndex 96), (facetIndex 97), (facetIndex 98), (facetIndex 99), (facetIndex 102), (facetIndex 106), (facetIndex 107), (facetIndex 108), (facetIndex 109), (facetIndex 111), (facetIndex 115)]))
 (.branch 2
 (.leaf ([(facetIndex 90), (facetIndex 91), (facetIndex 92), (facetIndex 93), (facetIndex 100), (facetIndex 103), (facetIndex 104), (facetIndex 105), (facetIndex 110), (facetIndex 114)]))
 (.leaf ([(facetIndex 101), (facetIndex 112), (facetIndex 113), (facetIndex 116), (facetIndex 117), (facetIndex 118), (facetIndex 119), (facetIndex 120)]))))
def groupColors4 : PackedGraphCertificate.Fields :=
  ⟨2, sparse_nat% "2aa1a10054900055z2d;"⟩
def grouping4 : FacetSat.Grouping data.count where
  count := 3
  members := fun g => groupMembers4.get g
  color := fun c => groupColors4.get c.val
def groupKind4 : List Nat := List.range grouping4.count

def grouped4_0000 : List Nat := [0]
def grouped4_0002 : List Nat := [1]
def grouped4_0003 : List Nat := [1, 2]
def grouped4_0004 : List Nat := [2]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record003 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record003_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3, 4]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsSix0Part00055.record003" "{\"atoms\":[{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":111},{\"tag\":\"facet\",\"index\":112},{\"tag\":\"facet\",\"index\":113},{\"tag\":\"facet\",\"index\":114},{\"tag\":\"facet\",\"index\":115},{\"tag\":\"facet\",\"index\":116},{\"tag\":\"facet\",\"index\":117},{\"tag\":\"facet\",\"index\":118},{\"tag\":\"facet\",\"index\":119},{\"tag\":\"facet\",\"index\":120},{\"tag\":\"group\",\"kind\":4,\"index\":1},{\"tag\":\"group\",\"kind\":4,\"index\":2},{\"tag\":\"group_totalizer\",\"kind\":4,\"threshold\":2,\"list_name\":\"grouped4_0003\"},{\"tag\":\"group_totalizer\",\"kind\":4,\"threshold\":2,\"list_name\":\"groupKind4\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsSix0Part00055.record003" 52

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsSix0Part00055.record003" "{\"ridges\":[[15,133],[17,133],[17,385],[17,388],[18,641],[18,644],[21,193],[21,208],[37,198],[38,385],[38,388],[39,644],[47,193],[47,208],[49,658],[51,450],[52,706],[53,898],[61,133],[61,204],[62,385],[64,208],[65,388],[66,641],[66,644],[67,228],[68,641],[68,644],[69,385],[69,641],[69,644],[71,193],[71,208],[72,408],[73,456],[74,736],[85,388],[88,148],[88,204],[92,193],[93,193],[93,208],[100,388],[102,208],[111,644],[112,641],[113,641],[114,644],[115,208],[119,385],[120,641]],\"owners\":[[88,148,[15,32,65,66,83,84,90,114],[56,64,82,89,91,102,112,115]],[17,385,[48,51,53,72,73],[38,62,65,69,100,101,102,119,120]],[38,385,[72,73],[17,48,51,53,62,65,69,100,101,102,119,120]],[62,385,[48,51,53],[17,38,65,69,72,73,100,101,102,119,120]],[69,385,[48,51,72,73],[17,38,53,62,65,100,101,102,119,120]],[119,385,[48,51],[17,38,53,62,65,69,72,73,100,101,102,120]],[17,388,[83,85,89],[38,62,65,69,100,101,102,119,120]],[38,388,[89],[17,62,65,69,83,85,100,101,102,119,120]],[65,388,[85],[17,38,62,69,83,89,100,101,102,119,120]],[85,388,[17,62,65,89,101,102],[38,69,83,100,119,120]],[100,388,[89],[17,38,62,65,69,83,85,101,102,119,120]],[18,641,[49,52,53,74],[39,66,68,69,111,112,113,114,115,119,120]],[66,641,[52,53,74],[18,39,49,68,69,111,112,113,114,115,119,120]],[68,641,[49,52,53],[18,39,66,69,74,111,112,113,114,115,119,120]],[69,641,[49,52,74],[18,39,53,66,68,111,112,113,114,115,119,120]],[112,641,[52,53,74],[18,39,49,66,68,69,111,113,114,115,119,120]],[113,641,[49,52,53],[18,39,66,68,69,74,111,112,114,115,119,120]],[120,641,[49,52],[18,39,53,66,68,69,74,111,112,113,114,115,119]],[18,644,[84,85],[39,66,68,69,111,112,113,114,115,119,120]],[39,644,[],[18,66,68,69,84,85,111,112,113,114,115,119,120]],[66,644,[85],[18,39,68,69,84,111,112,113,114,115,119,120]],[68,644,[84,85],[18,39,66,69,111,112,113,114,115,119,120]],[69,644,[84],[18,39,66,68,85,111,112,113,114,115,119,120]],[111,644,[],[18,39,66,68,69,84,85,112,113,114,115,119,120]],[114,644,[85],[18,39,66,68,69,84,111,112,113,115,119,120]],[21,193,[37,51,52,61,67,73,74],[47,64,71,92,93,102,115]],[47,193,[61,67,73,74],[21,37,51,52,64,71,92,93,102,115]],[71,193,[37,51,52,67,74],[21,47,61,64,73,92,93,102,115]],[92,193,[61,73],[21,37,47,51,52,64,67,71,74,93,102,115]],[93,193,[37,51,52],[21,47,61,64,67,71,73,74,92,102,115]],[21,208,[82,88],[47,64,71,92,93,102,115]],[47,208,[88],[21,64,71,82,92,93,102,115]],[64,208,[],[21,47,71,82,88,92,93,102,115]],[71,208,[82],[21,47,64,88,92,93,102,115]],[93,208,[82],[21,47,64,71,88,92,102,115]],[102,208,[],[21,47,64,71,82,88,92,93,115]],[115,208,[],[21,47,64,71,82,88,92,93,102]],[37,198,[82],[]],[49,658,[84],[]],[51,450,[],[]],[52,706,[],[]],[53,898,[85],[]],[61,204,[88],[]],[88,204,[61],[]],[67,228,[],[]],[72,408,[89],[]],[73,456,[],[]],[74,736,[],[]]],\"edges\":[[39,[21,37,47,51,52,61,64,67,71,73,74,82,88,92,93,102,115]],[42,[17,38,48,51,53,62,65,69,72,73,83,85,89,100,101,102,119,120]],[43,[18,39,49,52,53,66,68,69,74,84,85,111,112,113,114,115,119,120]]],\"groupings\":[4]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsSix0Part00055.record003" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsSix0Part00055.record003\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-16,-15],[-18,-15],[-19,-2],[-19,-15],[-22,-2],[-22,-15],[-27,-10],[-27,-11],[-27,-14],[-28,-11],[-29,-10],[-29,-27],[-29,-28],[-30,-5],[-30,-6],[-30,-9],[-30,-27],[-30,-28],[-30,-29],[-31,-16],[-31,-24],[-32,-15],[-32,-31],[-33,-30],[-34,-30],[-37,-31],[-40,-31],[-41,-31],[-42,-2],[-44,-30],[-45,-15],[-46,-30],[-47,-31],[-48,-15],[-1,-2,-15],[-31,1,5,18,19,28,29,33,42],[-2,10,12,14,24,25],[-7,24,25],[-16,10,12,14],[-22,10,12,24,25],[-47,10,12],[-2,28,30,32],[-7,32],[-18,30],[-30,2,16,18,32,37,38],[-36,32],[-3,11,13,14,26],[-19,13,14,26],[-21,11,13,14],[-22,11,13,26],[-40,13,14,26],[-41,11,13,14],[-48,11,13],[-3,29,30],[-8],[-19,30],[-21,29,30],[-22,29],[-39],[-42,30],[-4,6,12,13,15,20,25,26],[-9,15,20,25,26],[-23,6,12,13,20,26],[-34,15,25],[-35,6,12,13],[-4,27,31],[-9,31],[-17],[-23,27],[-35,27],[-38],[-43],[-6,27],[-11,29],[-12],[-13],[-14,30],[-15,31],[-31,15],[-20],[-24,32],[-25],[-26],[-34,49],[-35,49],[-36,49],[-42,49],[-50,37,40,41,44,45,46,47,48],[-37,50],[-40,50],[-41,50],[-47,50],[-48,50],[-49,-50,51],[-51,52],[-52],[4,6,9,12,13,15,17,20,23,25,26,27,31,34,35,38,43],[2,7,10,12,14,16,18,22,24,25,28,30,32,36,37,38,47,48],[3,8,11,13,14,19,21,22,26,29,30,39,40,41,42,43,47,48]],\"atoms\":[{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":111},{\"tag\":\"facet\",\"index\":112},{\"tag\":\"facet\",\"index\":113},{\"tag\":\"facet\",\"index\":114},{\"tag\":\"facet\",\"index\":115},{\"tag\":\"facet\",\"index\":116},{\"tag\":\"facet\",\"index\":117},{\"tag\":\"facet\",\"index\":118},{\"tag\":\"facet\",\"index\":119},{\"tag\":\"facet\",\"index\":120},{\"tag\":\"group\",\"index\":1,\"kind\":4},{\"tag\":\"group\",\"index\":2,\"kind\":4},{\"tag\":\"group_totalizer\",\"kind\":4},{\"tag\":\"group_totalizer\",\"kind\":4}],\"rules\":[{\"tag\":\"incompatible\",\"a\":62,\"b\":61},{\"tag\":\"incompatible\",\"a\":65,\"b\":61},{\"tag\":\"incompatible\",\"a\":66,\"b\":17},{\"tag\":\"incompatible\",\"a\":66,\"b\":61},{\"tag\":\"incompatible\",\"a\":69,\"b\":17},{\"tag\":\"incompatible\",\"a\":69,\"b\":61},{\"tag\":\"incompatible\",\"a\":82,\"b\":48},{\"tag\":\"incompatible\",\"a\":82,\"b\":49},{\"tag\":\"incompatible\",\"a\":82,\"b\":53},{\"tag\":\"incompatible\",\"a\":83,\"b\":49},{\"tag\":\"incompatible\",\"a\":84,\"b\":48},{\"tag\":\"incompatible\",\"a\":84,\"b\":82},{\"tag\":\"incompatible\",\"a\":84,\"b\":83},{\"tag\":\"incompatible\",\"a\":85,\"b\":32},{\"tag\":\"incompatible\",\"a\":85,\"b\":37},{\"tag\":\"incompatible\",\"a\":85,\"b\":47},{\"tag\":\"incompatible\",\"a\":85,\"b\":82},{\"tag\":\"incompatible\",\"a\":85,\"b\":83},{\"tag\":\"incompatible\",\"a\":85,\"b\":84},{\"tag\":\"incompatible\",\"a\":88,\"b\":62},{\"tag\":\"incompatible\",\"a\":88,\"b\":72},{\"tag\":\"incompatible\",\"a\":89,\"b\":61},{\"tag\":\"incompatible\",\"a\":89,\"b\":88},{\"tag\":\"incompatible\",\"a\":90,\"b\":85},{\"tag\":\"incompatible\",\"a\":92,\"b\":85},{\"tag\":\"incompatible\",\"a\":101,\"b\":88},{\"tag\":\"incompatible\",\"a\":112,\"b\":88},{\"tag\":\"incompatible\",\"a\":113,\"b\":88},{\"tag\":\"incompatible\",\"a\":114,\"b\":17},{\"tag\":\"incompatible\",\"a\":116,\"b\":85},{\"tag\":\"incompatible\",\"a\":117,\"b\":61},{\"tag\":\"incompatible\",\"a\":118,\"b\":85},{\"tag\":\"incompatible\",\"a\":119,\"b\":88},{\"tag\":\"incompatible\",\"a\":120,\"b\":61},{\"tag\":\"three\",\"ridge\":133,\"vertices\":[15,17,61]},{\"tag\":\"mate\",\"ridge\":148,\"a\":88,\"owners\":[15,32,65,66,83,84,90,114]},{\"tag\":\"mate\",\"ridge\":385,\"a\":17,\"owners\":[48,51,53,72,73]},{\"tag\":\"mate\",\"ridge\":385,\"a\":38,\"owners\":[72,73]},{\"tag\":\"mate\",\"ridge\":385,\"a\":62,\"owners\":[48,51,53]},{\"tag\":\"mate\",\"ridge\":385,\"a\":69,\"owners\":[48,51,72,73]},{\"tag\":\"mate\",\"ridge\":385,\"a\":119,\"owners\":[48,51]},{\"tag\":\"mate\",\"ridge\":388,\"a\":17,\"owners\":[83,85,89]},{\"tag\":\"mate\",\"ridge\":388,\"a\":38,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":388,\"a\":65,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":388,\"a\":85,\"owners\":[17,62,65,89,101,102]},{\"tag\":\"mate\",\"ridge\":388,\"a\":100,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":641,\"a\":18,\"owners\":[49,52,53,74]},{\"tag\":\"mate\",\"ridge\":641,\"a\":66,\"owners\":[52,53,74]},{\"tag\":\"mate\",\"ridge\":641,\"a\":68,\"owners\":[49,52,53]},{\"tag\":\"mate\",\"ridge\":641,\"a\":69,\"owners\":[49,52,74]},{\"tag\":\"mate\",\"ridge\":641,\"a\":112,\"owners\":[52,53,74]},{\"tag\":\"mate\",\"ridge\":641,\"a\":113,\"owners\":[49,52,53]},{\"tag\":\"mate\",\"ridge\":641,\"a\":120,\"owners\":[49,52]},{\"tag\":\"mate\",\"ridge\":644,\"a\":18,\"owners\":[84,85]},{\"tag\":\"mate\",\"ridge\":644,\"a\":39,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":644,\"a\":66,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":644,\"a\":68,\"owners\":[84,85]},{\"tag\":\"mate\",\"ridge\":644,\"a\":69,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":644,\"a\":111,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":644,\"a\":114,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":193,\"a\":21,\"owners\":[37,51,52,61,67,73,74]},{\"tag\":\"mate\",\"ridge\":193,\"a\":47,\"owners\":[61,67,73,74]},{\"tag\":\"mate\",\"ridge\":193,\"a\":71,\"owners\":[37,51,52,67,74]},{\"tag\":\"mate\",\"ridge\":193,\"a\":92,\"owners\":[61,73]},{\"tag\":\"mate\",\"ridge\":193,\"a\":93,\"owners\":[37,51,52]},{\"tag\":\"mate\",\"ridge\":208,\"a\":21,\"owners\":[82,88]},{\"tag\":\"mate\",\"ridge\":208,\"a\":47,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":208,\"a\":64,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":208,\"a\":71,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":208,\"a\":93,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":208,\"a\":102,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":208,\"a\":115,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":198,\"a\":37,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":658,\"a\":49,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":450,\"a\":51,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":706,\"a\":52,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":898,\"a\":53,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":204,\"a\":61,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":204,\"a\":88,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":228,\"a\":67,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":408,\"a\":72,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":456,\"a\":73,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":736,\"a\":74,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":4,\"index\":1,\"member\":92,\"full_literals\":[-34,49]},{\"tag\":\"group_take\",\"kind\":4,\"index\":1,\"member\":93,\"full_literals\":[-35,49]},{\"tag\":\"group_take\",\"kind\":4,\"index\":1,\"member\":100,\"full_literals\":[-36,49]},{\"tag\":\"group_take\",\"kind\":4,\"index\":1,\"member\":114,\"full_literals\":[-42,49]},{\"tag\":\"group_or\",\"kind\":4,\"index\":2,\"members\":[101,112,113,116,117,118,119,120],\"full_literals\":[-50,37,40,41,44,45,46,47,48]},{\"tag\":\"group_take\",\"kind\":4,\"index\":2,\"member\":101,\"full_literals\":[-37,50]},{\"tag\":\"group_take\",\"kind\":4,\"index\":2,\"member\":112,\"full_literals\":[-40,50]},{\"tag\":\"group_take\",\"kind\":4,\"index\":2,\"member\":113,\"full_literals\":[-41,50]},{\"tag\":\"group_take\",\"kind\":4,\"index\":2,\"member\":119,\"full_literals\":[-47,50]},{\"tag\":\"group_take\",\"kind\":4,\"index\":2,\"member\":120,\"full_literals\":[-48,50]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped4_0002\",\"right_name\":\"grouped4_0004\",\"joined_name\":\"grouped4_0003\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-49,-50,51],\"grouped\":true,\"kind\":4},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped4_0000\",\"right_name\":\"grouped4_0003\",\"joined_name\":\"groupKind4\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-51,52],\"grouped\":true,\"kind\":4},{\"tag\":\"quota_upper\",\"kind\":4,\"quota\":1,\"grouped\":true},{\"tag\":\"edge\",\"edge\":39,\"owners\":[21,37,47,51,52,61,64,67,71,73,74,82,88,92,93,102,115]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[17,38,48,51,53,62,65,69,72,73,83,85,89,100,101,102,119,120]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[18,39,49,52,53,66,68,69,74,84,85,111,112,113,114,115,119,120]}]}"
  "p cnf 52 99\n-16 -15 0\n-18 -15 0\n-19 -2 0\n-19 -15 0\n-22 -2 0\n-22 -15 0\n-27 -10 0\n-27 -11 0\n-27 -14 0\n-28 -11 0\n-29 -10 0\n-29 -27 0\n-29 -28 0\n-30 -5 0\n-30 -6 0\n-30 -9 0\n-30 -27 0\n-30 -28 0\n-30 -29 0\n-31 -16 0\n-31 -24 0\n-32 -15 0\n-32 -31 0\n-33 -30 0\n-34 -30 0\n-37 -31 0\n-40 -31 0\n-41 -31 0\n-42 -2 0\n-44 -30 0\n-45 -15 0\n-46 -30 0\n-47 -31 0\n-48 -15 0\n-1 -2 -15 0\n-31 1 5 18 19 28 29 33 42 0\n-2 10 12 14 24 25 0\n-7 24 25 0\n-16 10 12 14 0\n-22 10 12 24 25 0\n-47 10 12 0\n-2 28 30 32 0\n-7 32 0\n-18 30 0\n-30 2 16 18 32 37 38 0\n-36 32 0\n-3 11 13 14 26 0\n-19 13 14 26 0\n-21 11 13 14 0\n-22 11 13 26 0\n-40 13 14 26 0\n-41 11 13 14 0\n-48 11 13 0\n-3 29 30 0\n-8 0\n-19 30 0\n-21 29 30 0\n-22 29 0\n-39 0\n-42 30 0\n-4 6 12 13 15 20 25 26 0\n-9 15 20 25 26 0\n-23 6 12 13 20 26 0\n-34 15 25 0\n-35 6 12 13 0\n-4 27 31 0\n-9 31 0\n-17 0\n-23 27 0\n-35 27 0\n-38 0\n-43 0\n-6 27 0\n-11 29 0\n-12 0\n-13 0\n-14 30 0\n-15 31 0\n-31 15 0\n-20 0\n-24 32 0\n-25 0\n-26 0\n-34 49 0\n-35 49 0\n-36 49 0\n-42 49 0\n-50 37 40 41 44 45 46 47 48 0\n-37 50 0\n-40 50 0\n-41 50 0\n-47 50 0\n-48 50 0\n-49 -50 51 0\n-51 52 0\n-52 0\n4 6 9 12 13 15 17 20 23 25 26 27 31 34 35 38 43 0\n2 7 10 12 14 16 18 22 24 25 28 30 32 36 37 38 47 48 0\n3 8 11 13 14 19 21 22 26 29 30 39 40 41 42 43 47 48 0\n"
  "100 -51 0 96 95 0\n101 4 6 9 15 23 27 31 34 35 0 75 76 68 80 82 83 71 72 97 0\n102 2 7 10 14 16 18 22 24 28 30 32 36 37 47 48 0 75 82 71 98 0\n103 3 11 14 19 21 22 29 30 40 41 42 47 48 0 55 76 83 59 72 99 0\n104 27 31 49 0 78 67 85 84 69 73 66 101 0\n105 -27 42 0 75 83 76 7 8 9 12 17 41 50 53 48 51 47 49 52 103 0\n106 29 30 49 0 77 87 105 104 79 34 6 4 33 28 27 74 54 57 103 0\n107 30 49 0 82 75 87 105 104 79 34 6 2 21 38 33 26 23 20 86 77 106 11 13 37 102 0\n108 -50 0 100 94 87 105 104 26 27 28 33 79 31 34 107 30 32 88 0\n109 -37 0 108 89 0\n110 -40 0 108 90 0\n111 -41 0 108 91 0\n112 -47 0 108 92 0\n113 -48 0 108 93 0\n114 15 31 6 9 23 27 35 34 0 75 76 80 82 83 101 61 0\n115 15 -30 0 80 83 75 76 15 65 63 25 17 16 79 114 0\n116 -2 18 -30 0 115 78 24 19 18 14 3 29 35 36 0\n117 16 32 -30 18 0 109 71 45 116 0\n118 -30 0 115 1 2 22 117 0\n119 -18 0 118 44 0\n120 -19 0 118 56 0\n121 -42 0 118 60 0\n122 -14 0 118 77 0\n123 -27 0 121 105 0\n124 -23 0 123 69 0\n125 -35 0 123 70 0\n126 -6 0 123 73 0\n127 -28 22 0 83 76 113 112 121 111 110 118 120 122 10 13 47 49 103 0\n128 -32 0 83 80 82 125 123 124 126 22 23 62 64 114 0\n129 -7 0 128 43 0\n130 -36 0 128 46 0\n131 -24 0 128 81 0\n132 -2 0 128 118 5 42 127 0\n133 29 0 113 112 121 111 110 118 120 122 58 74 54 57 103 0\n134 -10 0 133 11 0\n135 -28 0 133 13 0\n136 -22 0 134 75 131 82 40 0\n137 -16 0 134 75 122 39 0\n138 0 137 134 129 122 128 132 136 131 135 118 119 130 109 112 113 102 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record003.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record003.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record003.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record003.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record003 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record003.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record003.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record003.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record003.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record003 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record003_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record003 Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record003_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsSix0Part00055.record003_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsSix0Part00055.record003
