module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow23Part00003Data
public import GraphInputsRow23Part00003Frames
public import GraphInputsRow23Part00003Leaves
public import GraphInputsRow23Part00003Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00003.record027
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record027
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), (certNat% 5), (certNat% 6), 18014535948435456, 601295421440]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), (certNat% 8), (certNat% 9), (certNat% 10), (certNat% 11), 2305847407260205056, 90159953477632]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), (certNat% 13), (certNat% 14), 11817445422220181504, 598074195968, (certNat% 15), 244091581366272, 1729382256910270464]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), (certNat% 17), (certNat% 18), (certNat% 19), 22519372526387200, (certNat% 20), 721554505728]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 21), 2078764171264, (certNat% 22), 175640385467449344, (certNat% 23), (certNat% 24), (certNat% 25)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 26), 72620543991349248, (certNat% 27), 87960930222080, 2305843043573432320, 18015910337970176, 549755813888]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 28), 1730789631793823744, 2305983746702049280, 18032128134479872, (certNat% 29), (certNat% 30), 70934606118912, 34359738368]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 31), (certNat% 22), 16429131440647569408, (certNat% 32), 31525197391593472, (certNat% 33), 90176059604992, (certNat% 34), 2113123909632]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨42, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c10 c3
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c11 c2
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c12 c1
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c13 c0
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record027_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record027_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record027_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record027_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record027_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record027_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record027_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record027_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record027_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00003.record027

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00003.record013
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "386d1ac671b2659a96359362d94e3392e1b89e17b85d16c57172559695355352d54d3352d1b49d17783d0ec370f2358e9334d332cd4b32d2b1ac9b16d8791e2729c6785d1715e0f43c8f0f03ac1a86518c6498960d84e0b81e0e705a154531525254351342d07703a0d4330d2324c3312c2b06e0741c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "92492492492492492492492492492492492492492492249249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record013 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record013 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record013.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record013.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record013.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ([(facetIndex 52), (facetIndex 57), (facetIndex 59), (facetIndex 60), (facetIndex 64)]))
 (.branch 2
 (.leaf ([(facetIndex 54), (facetIndex 58), (facetIndex 61), (facetIndex 62), (facetIndex 65)]))
 (.leaf ([(facetIndex 70), (facetIndex 74), (facetIndex 77), (facetIndex 78), (facetIndex 81)]))))
 (.branch 4
 (.leaf ([(facetIndex 68), (facetIndex 73), (facetIndex 75), (facetIndex 76), (facetIndex 80)]))
 (.branch 5
 (.leaf ([(facetIndex 41), (facetIndex 46), (facetIndex 53), (facetIndex 69), (facetIndex 85), (facetIndex 93)]))
 (.leaf ([(facetIndex 40), (facetIndex 43), (facetIndex 51), (facetIndex 67), (facetIndex 83), (facetIndex 91)])))))
 (.branch 9
 (.branch 7
 (.leaf ([(facetIndex 84), (facetIndex 87), (facetIndex 92), (facetIndex 96)]))
 (.branch 8
 (.leaf ([(facetIndex 47), (facetIndex 86), (facetIndex 89), (facetIndex 90)]))
 (.leaf ([(facetIndex 42), (facetIndex 45), (facetIndex 48), (facetIndex 49), (facetIndex 50), (facetIndex 66), (facetIndex 82), (facetIndex 98)]))))
 (.branch 11
 (.branch 10
 (.leaf ([(facetIndex 88), (facetIndex 94), (facetIndex 95), (facetIndex 97)]))
 (.leaf ([(facetIndex 71), (facetIndex 72), (facetIndex 79)])))
 (.branch 12
 (.leaf ([(facetIndex 55), (facetIndex 56), (facetIndex 63)]))
 (.leaf ([(facetIndex 44)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "8969946577967465823a223323aa2435810b110010bb1405888748c5845z28;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 13
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record013 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record013_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00003.record013" "{\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"group\",\"kind\":2,\"index\":9}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00003.record013" 55

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00003.record013" "{\"ridges\":[[9,74],[12,290],[13,194],[14,322],[16,770],[19,76],[22,292],[23,196],[24,324],[26,772],[33,262],[35,262],[37,262],[51,74],[53,74],[54,290],[55,74],[55,194],[56,74],[56,322],[58,290],[59,194],[61,290],[61,322],[62,290],[62,770],[63,194],[63,322],[64,194],[65,322],[65,770],[66,770],[67,76],[69,76],[70,292],[71,76],[71,196],[72,76],[72,324],[74,292],[75,196],[77,292],[77,324],[78,292],[78,772],[79,196],[79,324],[80,196],[81,324],[81,772],[82,772],[86,262],[90,262],[98,262]],\"owners\":[[9,74,[30,83,85,87,88],[51,53,55,56]],[51,74,[30,85,87,88],[9,53,55,56,83]],[53,74,[30,83,87,88],[9,51,55,56,85]],[55,74,[30,83,85,88],[9,51,53,56,87]],[56,74,[30,83,85,87],[9,51,53,55,88]],[12,290,[33,86,90,93,94],[54,58,61,62]],[54,290,[33,90,93,94],[12,58,61,62,86]],[58,290,[33,86,93,94],[12,54,61,62,90]],[61,290,[33,86,90,94],[12,54,58,62,93]],[62,290,[33,86,90,93],[12,54,58,61,94]],[13,194,[34,87,91,95,96],[55,59,63,64]],[55,194,[34,91,95,96],[13,59,63,64,87]],[59,194,[34,87,95,96],[13,55,63,64,91]],[63,194,[34,87,91,96],[13,55,59,64,95]],[64,194,[34,87,91,95],[13,55,59,63,96]],[14,322,[35,88,93,95,97],[56,61,63,65]],[56,322,[35,93,95,97],[14,61,63,65,88]],[61,322,[35,88,95,97],[14,56,63,65,93]],[63,322,[35,88,93,97],[14,56,61,65,95]],[65,322,[35,88,93,95],[14,56,61,63,97]],[16,770,[37,94,97,98],[62,65,66]],[62,770,[37,97,98],[16,65,66,94]],[65,770,[37,94,98],[16,62,66,97]],[66,770,[37,94,97],[16,62,65,98]],[19,76,[30,83,85,87,88],[67,69,71,72]],[67,76,[30,85,87,88],[19,69,71,72,83]],[69,76,[30,83,87,88],[19,67,71,72,85]],[71,76,[30,83,85,88],[19,67,69,72,87]],[72,76,[30,83,85,87],[19,67,69,71,88]],[22,292,[33,86,90,93,94],[70,74,77,78]],[70,292,[33,90,93,94],[22,74,77,78,86]],[74,292,[33,86,93,94],[22,70,77,78,90]],[77,292,[33,86,90,94],[22,70,74,78,93]],[78,292,[33,86,90,93],[22,70,74,77,94]],[23,196,[34,87,91,95,96],[71,75,79,80]],[71,196,[34,91,95,96],[23,75,79,80,87]],[75,196,[34,87,95,96],[23,71,79,80,91]],[79,196,[34,87,91,96],[23,71,75,80,95]],[80,196,[34,87,91,95],[23,71,75,79,96]],[24,324,[35,88,93,95,97],[72,77,79,81]],[72,324,[35,93,95,97],[24,77,79,81,88]],[77,324,[35,88,95,97],[24,72,79,81,93]],[79,324,[35,88,93,97],[24,72,77,81,95]],[81,324,[35,88,93,95],[24,72,77,79,97]],[26,772,[37,94,97,98],[78,81,82]],[78,772,[37,97,98],[26,81,82,94]],[81,772,[37,94,98],[26,78,82,97]],[82,772,[37,94,97],[26,78,81,98]]],\"edges\":[[26,[9,19,30,51,53,55,56,67,69,71,72,83,85,87,88]],[37,[12,22,33,54,58,61,62,70,74,77,78,86,90,93,94]],[39,[13,23,34,55,59,63,64,71,75,79,80,87,91,95,96]],[40,[14,24,35,56,61,63,65,72,77,79,81,88,93,95,97]],[44,[16,26,37,62,65,66,78,81,82,94,97,98]]],\"groupings\":[]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00003.record013" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00003.record013\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-46,-13],[-46,-45],[-48,-46],[-49,-15],[-50,-14],[-50,-49],[-51,-11],[-51,-42],[-51,-43],[-51,-45],[-51,-46],[-52,-46],[-53,-12],[-53,-44],[-53,-47],[-53,-49],[-53,-50],[-54,-49],[-12,-14,-15],[-12,-14,-54],[-14,-15,-44],[-14,-15,-47],[-14,-44,-54],[-14,-47,-54],[-1,11,42,43,45,46],[-16,11,43,45,46],[-17,11,42,45,46],[-19,11,42,43,46],[-20,11,42,43,45],[-2,12,44,47,49,50],[-18,12,47,49,50],[-21,12,44,49,50],[-23,12,44,47,50],[-24,12,44,47,49],[-3,13,45,48,51,52],[-19,13,48,51,52],[-22,13,45,51,52],[-25,13,45,48,52],[-26,13,45,48,51],[-4,14,46,49,51,53],[-20,14,49,51,53],[-23,14,46,51,53],[-25,14,46,49,53],[-27,14,46,49,51],[-5,15,50,53,54],[-24,15,53,54],[-27,15,50,54],[-28,15,50,53],[-6,11,42,43,45,46],[-29,11,43,45,46],[-30,11,42,45,46],[-32,11,42,43,46],[-33,11,42,43,45],[-7,12,44,47,49,50],[-31,12,47,49,50],[-34,12,44,49,50],[-36,12,44,47,50],[-37,12,44,47,49],[-8,13,45,48,51,52],[-32,13,48,51,52],[-35,13,45,51,52],[-38,13,45,48,52],[-39,13,45,48,51],[-9,14,46,49,51,53],[-33,14,49,51,53],[-36,14,46,51,53],[-38,14,46,49,53],[-40,14,46,49,51],[-10,15,50,53,54],[-37,15,53,54],[-40,15,50,54],[-41,15,50,53],[-55,46,50,51,53],[-50,55],[1,6,11,16,17,19,20,29,30,32,33,42,43,45,46],[2,7,12,18,21,23,24,31,34,36,37,44,47,49,50],[3,8,13,19,22,25,26,32,35,38,39,45,48,51,52],[4,9,14,20,23,25,27,33,36,38,40,46,49,51,53],[5,10,15,24,27,28,37,40,41,50,53,54]],\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"group\",\"index\":9,\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":88,\"b\":34},{\"tag\":\"incompatible\",\"a\":88,\"b\":87},{\"tag\":\"incompatible\",\"a\":91,\"b\":88},{\"tag\":\"incompatible\",\"a\":93,\"b\":37},{\"tag\":\"incompatible\",\"a\":94,\"b\":35},{\"tag\":\"incompatible\",\"a\":94,\"b\":93},{\"tag\":\"incompatible\",\"a\":95,\"b\":30},{\"tag\":\"incompatible\",\"a\":95,\"b\":83},{\"tag\":\"incompatible\",\"a\":95,\"b\":85},{\"tag\":\"incompatible\",\"a\":95,\"b\":87},{\"tag\":\"incompatible\",\"a\":95,\"b\":88},{\"tag\":\"incompatible\",\"a\":96,\"b\":88},{\"tag\":\"incompatible\",\"a\":97,\"b\":33},{\"tag\":\"incompatible\",\"a\":97,\"b\":86},{\"tag\":\"incompatible\",\"a\":97,\"b\":90},{\"tag\":\"incompatible\",\"a\":97,\"b\":93},{\"tag\":\"incompatible\",\"a\":97,\"b\":94},{\"tag\":\"incompatible\",\"a\":98,\"b\":93},{\"tag\":\"three\",\"ridge\":262,\"vertices\":[33,35,37]},{\"tag\":\"three\",\"ridge\":262,\"vertices\":[33,35,98]},{\"tag\":\"three\",\"ridge\":262,\"vertices\":[35,37,86]},{\"tag\":\"three\",\"ridge\":262,\"vertices\":[35,37,90]},{\"tag\":\"three\",\"ridge\":262,\"vertices\":[35,86,98]},{\"tag\":\"three\",\"ridge\":262,\"vertices\":[35,90,98]},{\"tag\":\"mate\",\"ridge\":74,\"a\":9,\"owners\":[30,83,85,87,88]},{\"tag\":\"mate\",\"ridge\":74,\"a\":51,\"owners\":[30,85,87,88]},{\"tag\":\"mate\",\"ridge\":74,\"a\":53,\"owners\":[30,83,87,88]},{\"tag\":\"mate\",\"ridge\":74,\"a\":55,\"owners\":[30,83,85,88]},{\"tag\":\"mate\",\"ridge\":74,\"a\":56,\"owners\":[30,83,85,87]},{\"tag\":\"mate\",\"ridge\":290,\"a\":12,\"owners\":[33,86,90,93,94]},{\"tag\":\"mate\",\"ridge\":290,\"a\":54,\"owners\":[33,90,93,94]},{\"tag\":\"mate\",\"ridge\":290,\"a\":58,\"owners\":[33,86,93,94]},{\"tag\":\"mate\",\"ridge\":290,\"a\":61,\"owners\":[33,86,90,94]},{\"tag\":\"mate\",\"ridge\":290,\"a\":62,\"owners\":[33,86,90,93]},{\"tag\":\"mate\",\"ridge\":194,\"a\":13,\"owners\":[34,87,91,95,96]},{\"tag\":\"mate\",\"ridge\":194,\"a\":55,\"owners\":[34,91,95,96]},{\"tag\":\"mate\",\"ridge\":194,\"a\":59,\"owners\":[34,87,95,96]},{\"tag\":\"mate\",\"ridge\":194,\"a\":63,\"owners\":[34,87,91,96]},{\"tag\":\"mate\",\"ridge\":194,\"a\":64,\"owners\":[34,87,91,95]},{\"tag\":\"mate\",\"ridge\":322,\"a\":14,\"owners\":[35,88,93,95,97]},{\"tag\":\"mate\",\"ridge\":322,\"a\":56,\"owners\":[35,93,95,97]},{\"tag\":\"mate\",\"ridge\":322,\"a\":61,\"owners\":[35,88,95,97]},{\"tag\":\"mate\",\"ridge\":322,\"a\":63,\"owners\":[35,88,93,97]},{\"tag\":\"mate\",\"ridge\":322,\"a\":65,\"owners\":[35,88,93,95]},{\"tag\":\"mate\",\"ridge\":770,\"a\":16,\"owners\":[37,94,97,98]},{\"tag\":\"mate\",\"ridge\":770,\"a\":62,\"owners\":[37,97,98]},{\"tag\":\"mate\",\"ridge\":770,\"a\":65,\"owners\":[37,94,98]},{\"tag\":\"mate\",\"ridge\":770,\"a\":66,\"owners\":[37,94,97]},{\"tag\":\"mate\",\"ridge\":76,\"a\":19,\"owners\":[30,83,85,87,88]},{\"tag\":\"mate\",\"ridge\":76,\"a\":67,\"owners\":[30,85,87,88]},{\"tag\":\"mate\",\"ridge\":76,\"a\":69,\"owners\":[30,83,87,88]},{\"tag\":\"mate\",\"ridge\":76,\"a\":71,\"owners\":[30,83,85,88]},{\"tag\":\"mate\",\"ridge\":76,\"a\":72,\"owners\":[30,83,85,87]},{\"tag\":\"mate\",\"ridge\":292,\"a\":22,\"owners\":[33,86,90,93,94]},{\"tag\":\"mate\",\"ridge\":292,\"a\":70,\"owners\":[33,90,93,94]},{\"tag\":\"mate\",\"ridge\":292,\"a\":74,\"owners\":[33,86,93,94]},{\"tag\":\"mate\",\"ridge\":292,\"a\":77,\"owners\":[33,86,90,94]},{\"tag\":\"mate\",\"ridge\":292,\"a\":78,\"owners\":[33,86,90,93]},{\"tag\":\"mate\",\"ridge\":196,\"a\":23,\"owners\":[34,87,91,95,96]},{\"tag\":\"mate\",\"ridge\":196,\"a\":71,\"owners\":[34,91,95,96]},{\"tag\":\"mate\",\"ridge\":196,\"a\":75,\"owners\":[34,87,95,96]},{\"tag\":\"mate\",\"ridge\":196,\"a\":79,\"owners\":[34,87,91,96]},{\"tag\":\"mate\",\"ridge\":196,\"a\":80,\"owners\":[34,87,91,95]},{\"tag\":\"mate\",\"ridge\":324,\"a\":24,\"owners\":[35,88,93,95,97]},{\"tag\":\"mate\",\"ridge\":324,\"a\":72,\"owners\":[35,93,95,97]},{\"tag\":\"mate\",\"ridge\":324,\"a\":77,\"owners\":[35,88,95,97]},{\"tag\":\"mate\",\"ridge\":324,\"a\":79,\"owners\":[35,88,93,97]},{\"tag\":\"mate\",\"ridge\":324,\"a\":81,\"owners\":[35,88,93,95]},{\"tag\":\"mate\",\"ridge\":772,\"a\":26,\"owners\":[37,94,97,98]},{\"tag\":\"mate\",\"ridge\":772,\"a\":78,\"owners\":[37,97,98]},{\"tag\":\"mate\",\"ridge\":772,\"a\":81,\"owners\":[37,94,98]},{\"tag\":\"mate\",\"ridge\":772,\"a\":82,\"owners\":[37,94,97]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[88,94,95,97],\"full_literals\":[-55,46,50,51,53]},{\"tag\":\"group_take\",\"kind\":2,\"index\":9,\"member\":94,\"full_literals\":[-50,55]},{\"tag\":\"edge\",\"edge\":26,\"owners\":[9,19,30,51,53,55,56,67,69,71,72,83,85,87,88]},{\"tag\":\"edge\",\"edge\":37,\"owners\":[12,22,33,54,58,61,62,70,74,77,78,86,90,93,94]},{\"tag\":\"edge\",\"edge\":39,\"owners\":[13,23,34,55,59,63,64,71,75,79,80,87,91,95,96]},{\"tag\":\"edge\",\"edge\":40,\"owners\":[14,24,35,56,61,63,65,72,77,79,81,88,93,95,97]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[16,26,37,62,65,66,78,81,82,94,97,98]}]}"
  "80 11 46 42 43 45 0 25 49 26 50 27 51 28 52 29 53 75 0\n81 -51 0 7 8 9 10 11 80 0\n82 14 46 53 49 0 81 40 64 41 65 43 67 42 44 66 68 78 0\n83 46 53 -55 0 81 73 5 6 82 0\n84 13 52 45 48 0 81 35 59 37 38 39 61 62 63 36 60 77 0\n85 -46 0 1 2 3 12 84 0\n86 12 50 44 47 49 0 30 54 31 55 32 33 34 56 57 58 76 0\n87 -53 0 13 14 15 16 17 86 0\n88 -55 0 87 85 83 0\n89 -50 0 88 74 0\n90 15 54 0 89 87 45 46 47 48 69 70 71 72 79 0\n91 -44 -14 0 21 23 90 0\n92 -12 -14 0 19 20 90 0\n93 -47 -14 0 24 22 90 0\n94 49 0 85 87 89 82 91 92 86 93 0\n95 -15 0 94 4 0\n96 -54 0 94 18 0\n97 0 95 96 90 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record013.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record013.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record013.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record013.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record013 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record013.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record013.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record013.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record013.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record013 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record013_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record013_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record013_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record013_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record013_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record013_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record013_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record013 Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record013_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record013_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record013_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00003.record013

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00003.record064
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "aaa9a599562b86ee4751aa7192e565c54752b46d8751d2745d0f783d0ea358ce3c4e9354f0b8ac6b86c9bc1d2729d1715e0f43c8f13c1fa6154a28aa518660bb11a4551a24a98649951465454550b41dc0e8350ca318e0b22c2b41c4709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "492492492492492492492492492492492249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record064 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record064 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record064.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 39), (facetIndex 40), (facetIndex 44), (facetIndex 50), (facetIndex 51)]))
 (.leaf ([(facetIndex 33), (facetIndex 70), (facetIndex 73)])))
 (.branch 3
 (.leaf ([(facetIndex 34), (facetIndex 45), (facetIndex 71), (facetIndex 75)]))
 (.branch 4
 (.leaf ([(facetIndex 37), (facetIndex 56), (facetIndex 60), (facetIndex 62), (facetIndex 64)]))
 (.leaf ([(facetIndex 49), (facetIndex 63), (facetIndex 66), (facetIndex 68), (facetIndex 69)])))))
 (.branch 8
 (.branch 6
 (.leaf ([(facetIndex 46), (facetIndex 48), (facetIndex 52), (facetIndex 54)]))
 (.branch 7
 (.leaf ([(facetIndex 42), (facetIndex 57), (facetIndex 61), (facetIndex 65), (facetIndex 67)]))
 (.leaf ([(facetIndex 32), (facetIndex 55), (facetIndex 58), (facetIndex 59)]))))
 (.branch 9
 (.leaf ([(facetIndex 35), (facetIndex 38), (facetIndex 41), (facetIndex 53)]))
 (.branch 10
 (.leaf ([(facetIndex 43), (facetIndex 47), (facetIndex 72), (facetIndex 74)]))
 (.leaf ([(facetIndex 36)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "291921446463436377637585004595209680083a8217z20;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 11
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3, 4]
def grouped2_0005 : List Nat := [3]
def grouped2_0006 : List Nat := [3, 4]
def grouped2_0007 : List Nat := [4]
def grouped2_0008 : List Nat := [5]
def grouped2_0009 : List Nat := [5, 6, 7]
def grouped2_0010 : List Nat := [5, 6, 7, 8, 9, 10]
def grouped2_0011 : List Nat := [6]
def grouped2_0012 : List Nat := [6, 7]
def grouped2_0013 : List Nat := [7]
def grouped2_0014 : List Nat := [8, 9, 10]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record064 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record064_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00003.record064" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0012\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":6,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":10,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00003.record064" 23

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00003.record064" "{\"ridges\":[[11,770],[32,28],[41,770],[46,770],[49,770],[53,770],[54,770],[55,28],[58,28],[59,28],[63,769],[66,769],[68,769],[69,769]],\"owners\":[[63,769,[11,46,53,54],[24,41,66,68,69]],[66,769,[11,41,53,54],[24,46,63,68,69]],[68,769,[11,41,46,54],[24,53,63,66,69]],[69,769,[11,41,46,53],[24,54,63,66,68]],[11,770,[],[41,46,49,53,54]],[41,770,[],[11,46,49,53,54]],[46,770,[],[11,41,49,53,54]],[49,770,[],[11,41,46,53,54]],[53,770,[],[11,41,46,49,54]],[54,770,[],[11,41,46,49,53]],[32,28,[],[12,55,56,57,58,59]],[55,28,[],[12,32,56,57,58,59]],[58,28,[],[12,32,55,56,57,59]],[59,28,[],[12,32,55,56,57,58]]],\"edges\":[],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00003.record064" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00003.record064\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-11,1,4,6,7],[-12,1,3,6,7],[-13,1,3,4,7],[-14,1,3,4,6],[-1],[-3],[-4],[-5],[-6],[-7],[-2],[-8],[-9],[-10],[-15,5,11,12,13,14],[-16,2,8,9,10],[-17,15],[-18,17],[-19,18],[-20,16],[-21,20],[-22,21],[-23,19,22],[23]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"mate\",\"ridge\":769,\"a\":63,\"owners\":[11,46,53,54]},{\"tag\":\"mate\",\"ridge\":769,\"a\":66,\"owners\":[11,41,53,54]},{\"tag\":\"mate\",\"ridge\":769,\"a\":68,\"owners\":[11,41,46,54]},{\"tag\":\"mate\",\"ridge\":769,\"a\":69,\"owners\":[11,41,46,53]},{\"tag\":\"mate\",\"ridge\":770,\"a\":11,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":770,\"a\":41,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":770,\"a\":46,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":770,\"a\":49,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":770,\"a\":53,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":770,\"a\":54,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":28,\"a\":32,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":28,\"a\":55,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":28,\"a\":58,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":28,\"a\":59,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[49,63,66,68,69],\"full_literals\":[-15,5,11,12,13,14]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[32,55,58,59],\"full_literals\":[-16,2,8,9,10]},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-17,false,15],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-18,false,17],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-19,false,18],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0012\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-20,false,16],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-21,false,20],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-22,21,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-23,19,22],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":10,\"grouped\":true}]}"
  "25 -14 0 9 5 6 7 4 0\n26 -13 0 10 5 6 7 3 0\n27 -12 0 10 5 6 9 2 0\n28 -11 0 10 5 7 9 1 0\n29 -15 0 8 28 27 26 25 15 0\n30 -16 0 11 12 13 14 16 0\n31 -17 0 29 17 0\n32 -18 0 31 18 0\n33 -19 0 32 19 0\n34 -20 0 30 20 0\n35 -21 0 34 21 0\n36 -22 0 35 22 0\n37 -23 0 33 36 23 0\n38 0 37 24 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record064.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record064.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record064.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record064.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record064 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record064.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record064.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record064.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record064.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record064 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record064_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record064_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record064_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record064_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record064_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record064_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record064_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record064 Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record064_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record064_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00003.record064_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00003.record064
