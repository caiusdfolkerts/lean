module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow29Part00283Data
public import GraphInputsRow29Part00283Frames
public import GraphInputsRow29Part00283Leaves
public import GraphInputsRow29Part00283Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00283.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record001
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨73, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨104, by decide⟩, ⟨105, by decide⟩, ⟨108, by decide⟩, ⟨109, by decide⟩, ⟨115, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), (certNat% 5), 1120402348703744, 1147292005072633856, (certNat% 6)]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record001_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00283.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00283.record004
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record004
def vertexColumn : Fields := ⟨10, (certNat% 7)⟩
def kindColumn : Fields := ⟨3, (certNat% 8)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨80, by decide⟩, ⟨86, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩, ⟨102, by decide⟩, ⟨104, by decide⟩, ⟨107, by decide⟩, ⟨113, by decide⟩, ⟨121, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 9), (certNat% 10), (certNat% 11), (certNat% 12), (certNat% 13), 126443837194240]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), (certNat% 15), (certNat% 11), (certNat% 12), (certNat% 16), 136339441844224]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), (certNat% 18), (certNat% 19), (certNat% 20), 533535818355048448, 140050293587968, (certNat% 21)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record004_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record004_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00283.record004

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00283.record000
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "c70f2c68ba1eb16a59969595635b0e8b92e2b86e8791e2785e3c7192e479c569565655554d5c362d4b4ad1b61d4749d17713a4d9394d532cc73c2e2b4acab1ac9b16c3bc1e8761e4751e2749e1745c9715c8f13c1f390e234a1a468c6298668390e0b8e134619464c5294658350d0b4c328c6384d1324c5382d0b0ac1b81d0721c4709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1a4db6db4924926d26db6da492493692492492492492492492489249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record000 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record000 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record000.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record000.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record000.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 52), (facetIndex 60), (facetIndex 61), (facetIndex 85), (facetIndex 104)]))
 (.leaf ([(facetIndex 71), (facetIndex 72), (facetIndex 73), (facetIndex 74), (facetIndex 75)])))
 (.branch 3
 (.leaf ([(facetIndex 90), (facetIndex 91), (facetIndex 92), (facetIndex 93), (facetIndex 94)]))
 (.leaf ([(facetIndex 38), (facetIndex 41), (facetIndex 42), (facetIndex 43), (facetIndex 44), (facetIndex 69), (facetIndex 70), (facetIndex 76), (facetIndex 88), (facetIndex 89), (facetIndex 95)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 51), (facetIndex 59), (facetIndex 66), (facetIndex 84), (facetIndex 103)]))
 (.leaf ([(facetIndex 39), (facetIndex 40), (facetIndex 45), (facetIndex 46), (facetIndex 47), (facetIndex 48), (facetIndex 49), (facetIndex 50)])))
 (.branch 7
 (.leaf ([(facetIndex 53), (facetIndex 54), (facetIndex 62), (facetIndex 63), (facetIndex 64), (facetIndex 65)]))
 (.leaf ([(facetIndex 55), (facetIndex 56), (facetIndex 57), (facetIndex 58)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "80000069249b0040000032492d8136d809fffb096db6b6ddacz1c;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 82), (facetIndex 83)]))
 (.leaf ([(facetIndex 101), (facetIndex 102)])))
 (.branch 3
 (.leaf ([(facetIndex 67), (facetIndex 68), (facetIndex 77), (facetIndex 78), (facetIndex 79), (facetIndex 80), (facetIndex 81)]))
 (.branch 4
 (.leaf ([(facetIndex 86), (facetIndex 87), (facetIndex 96), (facetIndex 97), (facetIndex 98), (facetIndex 99), (facetIndex 100)]))
 (.leaf ([(facetIndex 105)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "2004b6db0000006c00124900000024z32;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 5
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
def grouped2_0008 : List Nat := [4, 5, 6, 7]
def grouped2_0009 : List Nat := [5]
def grouped2_0010 : List Nat := [6, 7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record000 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record000_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00283.record000" "{\"atoms\":[{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":2}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00283.record000" 58

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00283.record000" "{\"ridges\":[[18,261],[19,517],[28,262],[29,518],[69,261],[70,517],[73,261],[74,517],[75,261],[75,517],[88,262],[89,518],[92,262],[93,518],[94,262],[94,518],[96,340],[97,596],[98,404],[99,660],[100,788]],\"owners\":[[18,261,[4,43,45,47,49,51,77,79,81],[69,73,75]],[69,261,[4,45,47,49,51],[18,43,73,75,77,79,81]],[73,261,[4,43,47,49,51,77,79,81],[18,45,69,75]],[75,261,[4,43,45,47,49,77,79],[18,51,69,73,81]],[28,262,[4,43,45,47,49,51,96,98,100],[88,92,94]],[88,262,[4,45,47,49,51],[28,43,92,94,96,98,100]],[92,262,[4,43,47,49,51,96,98,100],[28,45,88,94]],[94,262,[4,43,45,47,49,96,98],[28,51,88,92,100]],[19,517,[5,44,46,48,50,51,78,80,81],[70,74,75]],[70,517,[5,46,48,50,51],[19,44,74,75,78,80,81]],[74,517,[5,44,48,50,51,78,80,81],[19,46,70,75]],[75,517,[5,44,46,48,50,78,80],[19,51,70,74,81]],[29,518,[5,44,46,48,50,51,97,99,100],[89,93,94]],[89,518,[5,46,48,50,51],[29,44,93,94,97,99,100]],[93,518,[5,44,48,50,51,97,99,100],[29,46,89,94]],[94,518,[5,44,46,48,50,97,99],[29,51,89,93,100]],[96,340,[77],[]],[97,596,[78],[]],[98,404,[79],[]],[99,660,[80],[]],[100,788,[81,105],[]]],\"edges\":[[22,[4,18,28,43,45,47,49,51,69,73,75,77,79,81,88,92,94,96,98,100,105]],[23,[5,19,29,44,46,48,50,51,70,74,75,78,80,81,89,93,94,97,99,100,105]]],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00283.record000" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00283.record000\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-8,-1],[-8,-2],[-9,-1],[-9,-2],[-12,-8],[-12,-9],[-13,-8],[-13,-9],[-14,-2],[-14,-12],[-14,-13],[-15,-1],[-15,-12],[-15,-13],[-15,-14],[-16,-2],[-16,-12],[-16,-13],[-16,-15],[-17,-1],[-17,-12],[-17,-13],[-17,-14],[-17,-15],[-17,-16],[-18,-2],[-18,-12],[-18,-13],[-18,-15],[-18,-17],[-19,-1],[-19,-12],[-19,-13],[-19,-14],[-19,-16],[-19,-18],[-20,-8],[-20,-9],[-20,-14],[-20,-15],[-20,-16],[-20,-17],[-20,-18],[-20,-19],[-23,-7],[-23,-10],[-23,-11],[-23,-12],[-23,-13],[-24,-7],[-24,-10],[-24,-11],[-24,-12],[-24,-13],[-25,-23],[-25,-24],[-26,-23],[-26,-24],[-29,-22],[-30,-23],[-30,-24],[-31,-7],[-31,-10],[-31,-11],[-31,-12],[-31,-13],[-31,-25],[-31,-26],[-31,-30],[-32,-7],[-32,-10],[-32,-11],[-32,-12],[-32,-13],[-32,-25],[-32,-26],[-32,-30],[-33,-7],[-33,-10],[-33,-11],[-33,-12],[-33,-13],[-33,-25],[-33,-26],[-33,-30],[-34,-7],[-34,-10],[-34,-11],[-34,-12],[-34,-13],[-34,-25],[-34,-26],[-34,-30],[-35,-20],[-35,-21],[-35,-22],[-36,-29],[-36,-35],[-37,-21],[-37,-23],[-37,-24],[-37,-26],[-37,-31],[-37,-32],[-37,-33],[-37,-34],[-38,-23],[-38,-24],[-38,-25],[-38,-31],[-38,-32],[-38,-33],[-38,-34],[-38,-37],[-40,-37],[-41,-37],[-42,-23],[-42,-24],[-42,-31],[-42,-32],[-42,-33],[-42,-34],[-42,-35],[-48,-35],[-48,-37],[-49,-20],[-49,-21],[-49,-22],[-49,-36],[-49,-48],[-3,1,12,14,16,18,20,31,33,35],[-25,1,14,16,18,20],[-27,1,12,16,18,20,31,33,35],[-29,1,12,14,16,18,31,33],[-5,1,12,14,16,18,20,43,45,47],[-37,1,14,16,18,20],[-39,1,12,16,18,20,43,45,47],[-41,1,12,14,16,18,43,45],[-4,2,13,15,17,19,20,32,34,35],[-26,2,15,17,19,20],[-28,2,13,17,19,20,32,34,35],[-29,2,13,15,17,19,32,34],[-6,2,13,15,17,19,20,44,46,47],[-38,2,15,17,19,20],[-40,2,13,17,19,20,44,46,47],[-41,2,13,15,17,19,44,46],[-43,31],[-44,32],[-45,33],[-46,34],[-47,35,49],[-50,7,10,11,12,13,25,26,30,37,38,42],[-51,20,21,22,36,48],[-52,8,9,14,15,16,17,18,19],[-53,50],[-54,53],[-55,51],[-55,52],[-56,55],[-57,54],[-57,56],[57],[-58,23,24,31,32,33,34,35],[-31,58],[-32,58],[-33,58],[-34,58],[1,3,5,12,14,16,18,20,25,27,29,31,33,35,37,39,41,43,45,47,49],[2,4,6,13,15,17,19,20,26,28,29,32,34,35,38,40,41,44,46,47,49]],\"atoms\":[{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":39,\"b\":4},{\"tag\":\"incompatible\",\"a\":39,\"b\":5},{\"tag\":\"incompatible\",\"a\":40,\"b\":4},{\"tag\":\"incompatible\",\"a\":40,\"b\":5},{\"tag\":\"incompatible\",\"a\":43,\"b\":39},{\"tag\":\"incompatible\",\"a\":43,\"b\":40},{\"tag\":\"incompatible\",\"a\":44,\"b\":39},{\"tag\":\"incompatible\",\"a\":44,\"b\":40},{\"tag\":\"incompatible\",\"a\":45,\"b\":5},{\"tag\":\"incompatible\",\"a\":45,\"b\":43},{\"tag\":\"incompatible\",\"a\":45,\"b\":44},{\"tag\":\"incompatible\",\"a\":46,\"b\":4},{\"tag\":\"incompatible\",\"a\":46,\"b\":43},{\"tag\":\"incompatible\",\"a\":46,\"b\":44},{\"tag\":\"incompatible\",\"a\":46,\"b\":45},{\"tag\":\"incompatible\",\"a\":47,\"b\":5},{\"tag\":\"incompatible\",\"a\":47,\"b\":43},{\"tag\":\"incompatible\",\"a\":47,\"b\":44},{\"tag\":\"incompatible\",\"a\":47,\"b\":46},{\"tag\":\"incompatible\",\"a\":48,\"b\":4},{\"tag\":\"incompatible\",\"a\":48,\"b\":43},{\"tag\":\"incompatible\",\"a\":48,\"b\":44},{\"tag\":\"incompatible\",\"a\":48,\"b\":45},{\"tag\":\"incompatible\",\"a\":48,\"b\":46},{\"tag\":\"incompatible\",\"a\":48,\"b\":47},{\"tag\":\"incompatible\",\"a\":49,\"b\":5},{\"tag\":\"incompatible\",\"a\":49,\"b\":43},{\"tag\":\"incompatible\",\"a\":49,\"b\":44},{\"tag\":\"incompatible\",\"a\":49,\"b\":46},{\"tag\":\"incompatible\",\"a\":49,\"b\":48},{\"tag\":\"incompatible\",\"a\":50,\"b\":4},{\"tag\":\"incompatible\",\"a\":50,\"b\":43},{\"tag\":\"incompatible\",\"a\":50,\"b\":44},{\"tag\":\"incompatible\",\"a\":50,\"b\":45},{\"tag\":\"incompatible\",\"a\":50,\"b\":47},{\"tag\":\"incompatible\",\"a\":50,\"b\":49},{\"tag\":\"incompatible\",\"a\":51,\"b\":39},{\"tag\":\"incompatible\",\"a\":51,\"b\":40},{\"tag\":\"incompatible\",\"a\":51,\"b\":45},{\"tag\":\"incompatible\",\"a\":51,\"b\":46},{\"tag\":\"incompatible\",\"a\":51,\"b\":47},{\"tag\":\"incompatible\",\"a\":51,\"b\":48},{\"tag\":\"incompatible\",\"a\":51,\"b\":49},{\"tag\":\"incompatible\",\"a\":51,\"b\":50},{\"tag\":\"incompatible\",\"a\":67,\"b\":38},{\"tag\":\"incompatible\",\"a\":67,\"b\":41},{\"tag\":\"incompatible\",\"a\":67,\"b\":42},{\"tag\":\"incompatible\",\"a\":67,\"b\":43},{\"tag\":\"incompatible\",\"a\":67,\"b\":44},{\"tag\":\"incompatible\",\"a\":68,\"b\":38},{\"tag\":\"incompatible\",\"a\":68,\"b\":41},{\"tag\":\"incompatible\",\"a\":68,\"b\":42},{\"tag\":\"incompatible\",\"a\":68,\"b\":43},{\"tag\":\"incompatible\",\"a\":68,\"b\":44},{\"tag\":\"incompatible\",\"a\":69,\"b\":67},{\"tag\":\"incompatible\",\"a\":69,\"b\":68},{\"tag\":\"incompatible\",\"a\":70,\"b\":67},{\"tag\":\"incompatible\",\"a\":70,\"b\":68},{\"tag\":\"incompatible\",\"a\":75,\"b\":66},{\"tag\":\"incompatible\",\"a\":76,\"b\":67},{\"tag\":\"incompatible\",\"a\":76,\"b\":68},{\"tag\":\"incompatible\",\"a\":77,\"b\":38},{\"tag\":\"incompatible\",\"a\":77,\"b\":41},{\"tag\":\"incompatible\",\"a\":77,\"b\":42},{\"tag\":\"incompatible\",\"a\":77,\"b\":43},{\"tag\":\"incompatible\",\"a\":77,\"b\":44},{\"tag\":\"incompatible\",\"a\":77,\"b\":69},{\"tag\":\"incompatible\",\"a\":77,\"b\":70},{\"tag\":\"incompatible\",\"a\":77,\"b\":76},{\"tag\":\"incompatible\",\"a\":78,\"b\":38},{\"tag\":\"incompatible\",\"a\":78,\"b\":41},{\"tag\":\"incompatible\",\"a\":78,\"b\":42},{\"tag\":\"incompatible\",\"a\":78,\"b\":43},{\"tag\":\"incompatible\",\"a\":78,\"b\":44},{\"tag\":\"incompatible\",\"a\":78,\"b\":69},{\"tag\":\"incompatible\",\"a\":78,\"b\":70},{\"tag\":\"incompatible\",\"a\":78,\"b\":76},{\"tag\":\"incompatible\",\"a\":79,\"b\":38},{\"tag\":\"incompatible\",\"a\":79,\"b\":41},{\"tag\":\"incompatible\",\"a\":79,\"b\":42},{\"tag\":\"incompatible\",\"a\":79,\"b\":43},{\"tag\":\"incompatible\",\"a\":79,\"b\":44},{\"tag\":\"incompatible\",\"a\":79,\"b\":69},{\"tag\":\"incompatible\",\"a\":79,\"b\":70},{\"tag\":\"incompatible\",\"a\":79,\"b\":76},{\"tag\":\"incompatible\",\"a\":80,\"b\":38},{\"tag\":\"incompatible\",\"a\":80,\"b\":41},{\"tag\":\"incompatible\",\"a\":80,\"b\":42},{\"tag\":\"incompatible\",\"a\":80,\"b\":43},{\"tag\":\"incompatible\",\"a\":80,\"b\":44},{\"tag\":\"incompatible\",\"a\":80,\"b\":69},{\"tag\":\"incompatible\",\"a\":80,\"b\":70},{\"tag\":\"incompatible\",\"a\":80,\"b\":76},{\"tag\":\"incompatible\",\"a\":81,\"b\":51},{\"tag\":\"incompatible\",\"a\":81,\"b\":59},{\"tag\":\"incompatible\",\"a\":81,\"b\":66},{\"tag\":\"incompatible\",\"a\":84,\"b\":75},{\"tag\":\"incompatible\",\"a\":84,\"b\":81},{\"tag\":\"incompatible\",\"a\":88,\"b\":59},{\"tag\":\"incompatible\",\"a\":88,\"b\":67},{\"tag\":\"incompatible\",\"a\":88,\"b\":68},{\"tag\":\"incompatible\",\"a\":88,\"b\":70},{\"tag\":\"incompatible\",\"a\":88,\"b\":77},{\"tag\":\"incompatible\",\"a\":88,\"b\":78},{\"tag\":\"incompatible\",\"a\":88,\"b\":79},{\"tag\":\"incompatible\",\"a\":88,\"b\":80},{\"tag\":\"incompatible\",\"a\":89,\"b\":67},{\"tag\":\"incompatible\",\"a\":89,\"b\":68},{\"tag\":\"incompatible\",\"a\":89,\"b\":69},{\"tag\":\"incompatible\",\"a\":89,\"b\":77},{\"tag\":\"incompatible\",\"a\":89,\"b\":78},{\"tag\":\"incompatible\",\"a\":89,\"b\":79},{\"tag\":\"incompatible\",\"a\":89,\"b\":80},{\"tag\":\"incompatible\",\"a\":89,\"b\":88},{\"tag\":\"incompatible\",\"a\":93,\"b\":88},{\"tag\":\"incompatible\",\"a\":94,\"b\":88},{\"tag\":\"incompatible\",\"a\":95,\"b\":67},{\"tag\":\"incompatible\",\"a\":95,\"b\":68},{\"tag\":\"incompatible\",\"a\":95,\"b\":77},{\"tag\":\"incompatible\",\"a\":95,\"b\":78},{\"tag\":\"incompatible\",\"a\":95,\"b\":79},{\"tag\":\"incompatible\",\"a\":95,\"b\":80},{\"tag\":\"incompatible\",\"a\":95,\"b\":81},{\"tag\":\"incompatible\",\"a\":103,\"b\":81},{\"tag\":\"incompatible\",\"a\":103,\"b\":88},{\"tag\":\"incompatible\",\"a\":105,\"b\":51},{\"tag\":\"incompatible\",\"a\":105,\"b\":59},{\"tag\":\"incompatible\",\"a\":105,\"b\":66},{\"tag\":\"incompatible\",\"a\":105,\"b\":84},{\"tag\":\"incompatible\",\"a\":105,\"b\":103},{\"tag\":\"mate\",\"ridge\":261,\"a\":18,\"owners\":[4,43,45,47,49,51,77,79,81]},{\"tag\":\"mate\",\"ridge\":261,\"a\":69,\"owners\":[4,45,47,49,51]},{\"tag\":\"mate\",\"ridge\":261,\"a\":73,\"owners\":[4,43,47,49,51,77,79,81]},{\"tag\":\"mate\",\"ridge\":261,\"a\":75,\"owners\":[4,43,45,47,49,77,79]},{\"tag\":\"mate\",\"ridge\":262,\"a\":28,\"owners\":[4,43,45,47,49,51,96,98,100]},{\"tag\":\"mate\",\"ridge\":262,\"a\":88,\"owners\":[4,45,47,49,51]},{\"tag\":\"mate\",\"ridge\":262,\"a\":92,\"owners\":[4,43,47,49,51,96,98,100]},{\"tag\":\"mate\",\"ridge\":262,\"a\":94,\"owners\":[4,43,45,47,49,96,98]},{\"tag\":\"mate\",\"ridge\":517,\"a\":19,\"owners\":[5,44,46,48,50,51,78,80,81]},{\"tag\":\"mate\",\"ridge\":517,\"a\":70,\"owners\":[5,46,48,50,51]},{\"tag\":\"mate\",\"ridge\":517,\"a\":74,\"owners\":[5,44,48,50,51,78,80,81]},{\"tag\":\"mate\",\"ridge\":517,\"a\":75,\"owners\":[5,44,46,48,50,78,80]},{\"tag\":\"mate\",\"ridge\":518,\"a\":29,\"owners\":[5,44,46,48,50,51,97,99,100]},{\"tag\":\"mate\",\"ridge\":518,\"a\":89,\"owners\":[5,46,48,50,51]},{\"tag\":\"mate\",\"ridge\":518,\"a\":93,\"owners\":[5,44,48,50,51,97,99,100]},{\"tag\":\"mate\",\"ridge\":518,\"a\":94,\"owners\":[5,44,46,48,50,97,99]},{\"tag\":\"mate\",\"ridge\":340,\"a\":96,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":596,\"a\":97,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":404,\"a\":98,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":660,\"a\":99,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":788,\"a\":100,\"owners\":[81,105]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[38,41,42,43,44,69,70,76,88,89,95],\"full_literals\":[-50,7,10,11,12,13,25,26,30,37,38,42]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[51,59,66,84,103],\"full_literals\":[-51,20,21,22,36,48]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[39,40,45,46,47,48,49,50],\"full_literals\":[-52,8,9,14,15,16,17,18,19]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-53,false,50],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-54,false,53],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-55,51,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-55,false,52],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-56,55,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-57,54,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-57,false,56],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[67,68,77,78,79,80,81],\"full_literals\":[-58,23,24,31,32,33,34,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":77,\"full_literals\":[-31,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":78,\"full_literals\":[-32,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":79,\"full_literals\":[-33,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":80,\"full_literals\":[-34,58]},{\"tag\":\"edge\",\"edge\":22,\"owners\":[4,18,28,43,45,47,49,51,69,73,75,77,79,81,88,92,94,96,98,100,105]},{\"tag\":\"edge\",\"edge\":23,\"owners\":[5,19,29,44,46,48,50,51,70,74,75,78,80,81,89,93,94,97,99,100,105]}]}"
  "170 54 0 162 160 0\n171 56 0 162 161 0\n172 53 0 170 156 0\n173 55 0 171 159 0\n174 50 0 172 155 0\n175 51 0 173 157 0\n176 52 0 173 158 0\n177 -49 0 175 126 127 128 129 130 153 0\n178 -42 -58 0 117 118 119 120 121 122 123 163 0\n179 -35 0 175 94 95 96 98 124 153 0\n180 -47 0 179 177 151 0\n181 -30 -58 0 179 60 61 69 77 85 93 163 0\n182 -24 -58 0 174 181 178 50 51 52 53 54 56 58 101 108 152 0\n183 -23 -58 0 174 181 178 45 46 47 48 49 55 57 100 107 152 0\n184 -31 -58 0 174 181 178 62 63 64 65 66 67 68 103 110 152 0\n185 -32 -58 0 174 181 178 70 71 72 73 74 75 76 104 111 152 0\n186 -33 -58 0 174 181 178 78 79 80 81 82 83 84 105 112 152 0\n187 -58 0 179 174 178 181 182 183 184 185 186 163 86 87 88 89 90 91 92 106 113 152 0\n188 -31 0 187 164 0\n189 -32 0 187 165 0\n190 -33 0 187 166 0\n191 -34 0 187 167 0\n192 -43 0 188 147 0\n193 -44 0 189 148 0\n194 -45 0 190 149 0\n195 -46 0 191 150 0\n196 -12 0 176 5 6 10 13 17 21 27 32 154 0\n197 -13 0 176 7 8 11 14 18 22 28 33 154 0\n198 18 16 -25 1 14 0 176 132 37 38 40 42 44 154 0\n199 -18 29 28 26 38 0 177 180 195 193 179 191 189 197 26 29 30 36 43 139 146 143 145 169 0\n200 18 14 -25 16 0 176 198 1 3 12 20 31 154 0\n201 -1 14 16 18 0 176 1 3 12 20 31 154 0\n202 20 14 16 18 29 27 25 37 0 177 180 194 192 179 190 188 196 201 138 137 135 131 168 0\n203 14 16 18 15 29 27 25 37 0 176 202 37 38 42 44 154 0\n204 -18 26 38 0 179 191 189 197 26 29 30 36 43 142 141 199 0\n205 2 15 19 20 29 17 41 40 26 38 0 177 180 195 193 179 191 189 197 139 143 141 169 0\n206 15 19 20 29 17 41 40 26 38 0 176 204 205 2 4 9 16 154 0\n207 -15 20 18 -37 0 12 15 19 136 0\n208 20 29 17 -37 38 0 102 204 116 115 207 206 31 34 35 136 0\n209 -20 17 18 0 176 37 38 39 40 41 44 154 0\n210 17 -37 38 0 175 102 204 125 99 209 208 59 97 153 0\n211 -17 0 179 190 188 196 20 23 24 25 30 42 136 134 133 200 203 0\n212 14 16 18 25 20 37 0 179 190 188 196 201 133 134 202 0\n213 -14 -38 20 0 211 9 15 34 144 0\n214 -16 -38 20 0 211 16 19 35 144 0\n215 -38 20 37 0 211 109 213 214 212 26 29 36 144 0\n216 -18 38 20 0 211 26 29 36 204 140 0\n217 2 15 19 38 20 0 177 180 195 193 179 191 189 211 197 139 143 141 140 145 142 146 169 0\n218 15 19 38 20 0 211 176 216 217 2 4 9 16 154 0\n219 -15 20 37 0 215 216 15 19 200 212 0\n220 20 37 0 215 216 219 218 34 35 200 212 0\n221 -20 0 211 43 209 0\n222 37 0 221 220 0\n223 -38 0 222 114 0\n224 0 222 223 211 210 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record000.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record000.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record000.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record000.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record000 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record000.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record000.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record000.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record000.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record000 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record000_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record000 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record000_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record000_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00283.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00283.record003
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "f83d0ec3c8eac6a5a568da8e93a2e87a39b169595635a364d8b61db0e9394e33a2e4b8ae1b8f13a719a659996559366394e4b91e4e5c569565655554d58d5352d475c368d6364d5362d4b46d38f1394d5334e334ccb31cf0b92d4b32e2b4acab1ae1b46c9b16c3bc1e4751cc789d2729c6785d1725c570dc8f330ac8390e1382e344b1324a9314a58350d2344d0b61344c530ce0b42c4b0ae0741c4709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "da6db6db6db6db6da4924924db6d369a6db69b4d249249a4924924924924d249249249a489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record003 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record003 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record003.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record003.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record003.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 30), (facetIndex 66), (facetIndex 67), (facetIndex 68), (facetIndex 69), (facetIndex 70), (facetIndex 71), (facetIndex 72), (facetIndex 73)]))
 (.leaf ([(facetIndex 31), (facetIndex 32), (facetIndex 34), (facetIndex 35), (facetIndex 75), (facetIndex 78)])))
 (.branch 3
 (.leaf ([(facetIndex 44), (facetIndex 45), (facetIndex 47), (facetIndex 48), (facetIndex 86), (facetIndex 89)]))
 (.leaf ([(facetIndex 97), (facetIndex 98), (facetIndex 99), (facetIndex 100), (facetIndex 101), (facetIndex 102), (facetIndex 103), (facetIndex 104)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 36), (facetIndex 37), (facetIndex 38), (facetIndex 39), (facetIndex 40), (facetIndex 41), (facetIndex 42), (facetIndex 43)]))
 (.leaf ([(facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 52), (facetIndex 53), (facetIndex 54), (facetIndex 55), (facetIndex 56)])))
 (.branch 7
 (.leaf ([(facetIndex 57), (facetIndex 58), (facetIndex 59), (facetIndex 60), (facetIndex 61), (facetIndex 62), (facetIndex 63), (facetIndex 64)]))
 (.leaf ([(facetIndex 84), (facetIndex 95), (facetIndex 96), (facetIndex 124)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "70000000000000036db6dfe00010087000040200000006db6db5b6db6a4129249242412z17;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 33), (facetIndex 46), (facetIndex 65)]))
 (.leaf ([(facetIndex 74), (facetIndex 85), (facetIndex 113)])))
 (.branch 3
 (.leaf ([(facetIndex 105), (facetIndex 106), (facetIndex 122)]))
 (.leaf ([(facetIndex 109), (facetIndex 115), (facetIndex 123)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 76), (facetIndex 77), (facetIndex 79), (facetIndex 80), (facetIndex 81), (facetIndex 82), (facetIndex 83), (facetIndex 125)]))
 (.leaf ([(facetIndex 87), (facetIndex 88), (facetIndex 90), (facetIndex 91), (facetIndex 92), (facetIndex 93), (facetIndex 94), (facetIndex 114), (facetIndex 118)])))
 (.branch 7
 (.leaf ([(facetIndex 107), (facetIndex 108), (facetIndex 110), (facetIndex 111), (facetIndex 112)]))
 (.leaf ([(facetIndex 116), (facetIndex 117), (facetIndex 119), (facetIndex 120), (facetIndex 121), (facetIndex 126)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1e06bff7f74ed9ec9000000016db45a0892482404z37;"⟩
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
def grouped2_0008 : List Nat := [4, 5, 6, 7]
def grouped3_0009 : List Nat := [0]
def grouped3_0010 : List Nat := [0, 1]
def grouped3_0011 : List Nat := [0, 1, 2, 3]
def grouped3_0013 : List Nat := [1]
def grouped3_0014 : List Nat := [2]
def grouped3_0015 : List Nat := [2, 3]
def grouped3_0016 : List Nat := [3]
def grouped3_0017 : List Nat := [4]
def grouped3_0018 : List Nat := [4, 5]
def grouped3_0019 : List Nat := [4, 5, 6, 7]
def grouped3_0020 : List Nat := [5]
def grouped3_0021 : List Nat := [6]
def grouped3_0022 : List Nat := [6, 7]
def grouped3_0023 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record003 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record003_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00283.record003" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"facet\",\"index\":109},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":111},{\"tag\":\"facet\",\"index\":112},{\"tag\":\"facet\",\"index\":114},{\"tag\":\"facet\",\"index\":115},{\"tag\":\"facet\",\"index\":116},{\"tag\":\"facet\",\"index\":117},{\"tag\":\"facet\",\"index\":118},{\"tag\":\"facet\",\"index\":119},{\"tag\":\"facet\",\"index\":120},{\"tag\":\"facet\",\"index\":121},{\"tag\":\"facet\",\"index\":123},{\"tag\":\"facet\",\"index\":125},{\"tag\":\"facet\",\"index\":126},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00283.record003" 71

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00283.record003" "{\"ridges\":[[11,273],[11,274],[31,50],[32,82],[34,273],[34,274],[35,530],[44,50],[45,82],[47,273],[47,274],[48,530],[59,273],[59,274],[62,273],[62,274],[64,273],[64,274],[75,176],[76,308],[78,208],[79,340],[81,404],[83,788],[86,176],[87,312],[89,208],[90,344],[92,408],[94,792],[107,308],[110,340],[112,788],[114,120],[116,312],[117,568],[118,154],[119,344],[120,600],[121,792],[125,116],[126,120]],\"owners\":[[31,50,[114,115,116,117,123],[9,44,57,58,59,60,105,106,107,108]],[44,50,[105,106,107,108,123],[9,31,57,58,59,60,114,115,116,117]],[32,82,[114,118,119,120,123],[10,45,57,61,62,63,105,109,110,111]],[45,82,[105,109,110,111,123],[10,32,57,61,62,63,114,118,119,120]],[11,273,[76,79,81,83,87,90,92,94],[34,47,59,62,64]],[34,273,[87,90,92,94],[11,47,59,62,64,76,79,81,83]],[47,273,[76,79,81,83],[11,34,59,62,64,87,90,92,94]],[59,273,[79,81,83,90,92,94],[11,34,47,62,64,76,87]],[62,273,[76,81,83,87,92,94],[11,34,47,59,64,79,90]],[64,273,[76,79,81,87,90,92],[11,34,47,59,62,83,94]],[11,274,[107,110,112,116,119,121],[34,47,59,62,64]],[34,274,[116,119,121],[11,47,59,62,64,107,110,112]],[47,274,[107,110,112],[11,34,59,62,64,116,119,121]],[59,274,[110,112,119,121],[11,34,47,62,64,107,116]],[62,274,[107,112,116,121],[11,34,47,59,64,110,119]],[64,274,[107,110,116,119],[11,34,47,59,62,112,121]],[35,530,[117,120,121],[12,48,60,63,64,108,111,112]],[48,530,[108,111,112],[12,35,60,63,64,117,120,121]],[75,176,[115,123,126],[22,58,86,96,106,125]],[86,176,[106,123,125],[22,58,75,96,115,126]],[78,208,[118,123,126],[23,61,89,96,109,125]],[89,208,[109,123,125],[23,61,78,96,118,126]],[118,154,[46,115],[]],[125,116,[74,105],[]],[76,308,[107],[]],[107,308,[76],[]],[79,340,[110],[]],[110,340,[79],[]],[81,404,[],[]],[83,788,[112],[]],[112,788,[83],[]],[114,120,[85,126],[]],[126,120,[85,114],[]],[87,312,[116],[]],[116,312,[87],[]],[117,568,[88],[]],[90,344,[119],[]],[119,344,[90],[]],[120,600,[91],[]],[92,408,[],[]],[94,792,[121],[]],[121,792,[94],[]]],\"edges\":[[33,[11,34,47,59,62,64,76,79,81,83,87,90,92,94,107,110,112,116,119,121]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00283.record003" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00283.record003\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-2,38,39,40,41,46],[-6,30,31,32,33,46],[-3,38,42,43,44,46],[-7,30,34,35,36,46],[-1,16,18,19,20,23,26,28,29],[-4,23,26,28,29],[-9,16,18,19,20],[-11,18,19,20,26,28,29],[-12,16,19,20,23,28,29],[-13,16,18,19,23,26,28],[-1,32,35,37,40,43,45],[-4,40,43,45],[-9,32,35,37],[-11,35,37,43,45],[-12,32,37,40,45],[-13,32,35,40,43],[-5,41,44,45],[-10,33,36,37],[-15,39,46,48],[-22,31,46,47],[-17,42,46,48],[-25,34,46,47],[-42,8,39],[-47,14,30],[-16,32],[-32,16],[-18,35],[-35,18],[-19],[-20,37],[-37,20],[-38,21,48],[-48,21,38],[-23,40],[-40,23],[-41,24],[-26,43],[-43,26],[-44,27],[-28],[-29,45],[-45,29],[-49,2,3,4,5,15,17],[-50,6,7,9,10,22,25],[-51,49],[-52,50],[-53,51],[-53,52],[-54,53],[54],[-8,55],[-14,56],[-21,56],[-30,57],[-31,57],[-34,58],[-39,58],[-46,58],[-16,59],[-18,59],[-20,59],[-23,60],[-24,60],[-26,60],[-27,60],[-29,60],[-38,60],[-32,61],[-33,61],[-35,61],[-36,61],[-37,61],[-62,40,41,43,44,45,48],[-40,62],[-41,62],[-43,62],[-44,62],[-45,62],[-48,62],[-56,63],[-55,63],[-58,64],[-57,64],[-64,65],[-63,65],[-60,66],[-59,66],[-62,67],[-61,67],[-68,62],[-61,-62,68],[-68,69],[-66,-67,69],[-66,-68,70],[-70,71],[-65,-69,71],[-71],[1,4,9,11,12,13,16,18,19,20,23,26,28,29,32,35,37,40,43,45]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"facet\",\"index\":107},{\"tag\":\"facet\",\"index\":108},{\"tag\":\"facet\",\"index\":109},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":111},{\"tag\":\"facet\",\"index\":112},{\"tag\":\"facet\",\"index\":114},{\"tag\":\"facet\",\"index\":115},{\"tag\":\"facet\",\"index\":116},{\"tag\":\"facet\",\"index\":117},{\"tag\":\"facet\",\"index\":118},{\"tag\":\"facet\",\"index\":119},{\"tag\":\"facet\",\"index\":120},{\"tag\":\"facet\",\"index\":121},{\"tag\":\"facet\",\"index\":123},{\"tag\":\"facet\",\"index\":125},{\"tag\":\"facet\",\"index\":126},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":50,\"a\":31,\"owners\":[114,115,116,117,123]},{\"tag\":\"mate\",\"ridge\":50,\"a\":44,\"owners\":[105,106,107,108,123]},{\"tag\":\"mate\",\"ridge\":82,\"a\":32,\"owners\":[114,118,119,120,123]},{\"tag\":\"mate\",\"ridge\":82,\"a\":45,\"owners\":[105,109,110,111,123]},{\"tag\":\"mate\",\"ridge\":273,\"a\":11,\"owners\":[76,79,81,83,87,90,92,94]},{\"tag\":\"mate\",\"ridge\":273,\"a\":34,\"owners\":[87,90,92,94]},{\"tag\":\"mate\",\"ridge\":273,\"a\":47,\"owners\":[76,79,81,83]},{\"tag\":\"mate\",\"ridge\":273,\"a\":59,\"owners\":[79,81,83,90,92,94]},{\"tag\":\"mate\",\"ridge\":273,\"a\":62,\"owners\":[76,81,83,87,92,94]},{\"tag\":\"mate\",\"ridge\":273,\"a\":64,\"owners\":[76,79,81,87,90,92]},{\"tag\":\"mate\",\"ridge\":274,\"a\":11,\"owners\":[107,110,112,116,119,121]},{\"tag\":\"mate\",\"ridge\":274,\"a\":34,\"owners\":[116,119,121]},{\"tag\":\"mate\",\"ridge\":274,\"a\":47,\"owners\":[107,110,112]},{\"tag\":\"mate\",\"ridge\":274,\"a\":59,\"owners\":[110,112,119,121]},{\"tag\":\"mate\",\"ridge\":274,\"a\":62,\"owners\":[107,112,116,121]},{\"tag\":\"mate\",\"ridge\":274,\"a\":64,\"owners\":[107,110,116,119]},{\"tag\":\"mate\",\"ridge\":530,\"a\":35,\"owners\":[117,120,121]},{\"tag\":\"mate\",\"ridge\":530,\"a\":48,\"owners\":[108,111,112]},{\"tag\":\"mate\",\"ridge\":176,\"a\":75,\"owners\":[115,123,126]},{\"tag\":\"mate\",\"ridge\":176,\"a\":86,\"owners\":[106,123,125]},{\"tag\":\"mate\",\"ridge\":208,\"a\":78,\"owners\":[118,123,126]},{\"tag\":\"mate\",\"ridge\":208,\"a\":89,\"owners\":[109,123,125]},{\"tag\":\"mate\",\"ridge\":154,\"a\":118,\"owners\":[46,115]},{\"tag\":\"mate\",\"ridge\":116,\"a\":125,\"owners\":[74,105]},{\"tag\":\"mate\",\"ridge\":308,\"a\":76,\"owners\":[107]},{\"tag\":\"mate\",\"ridge\":308,\"a\":107,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":340,\"a\":79,\"owners\":[110]},{\"tag\":\"mate\",\"ridge\":340,\"a\":110,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":404,\"a\":81,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":788,\"a\":83,\"owners\":[112]},{\"tag\":\"mate\",\"ridge\":788,\"a\":112,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":120,\"a\":114,\"owners\":[85,126]},{\"tag\":\"mate\",\"ridge\":120,\"a\":126,\"owners\":[85,114]},{\"tag\":\"mate\",\"ridge\":312,\"a\":87,\"owners\":[116]},{\"tag\":\"mate\",\"ridge\":312,\"a\":116,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":568,\"a\":117,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":344,\"a\":90,\"owners\":[119]},{\"tag\":\"mate\",\"ridge\":344,\"a\":119,\"owners\":[90]},{\"tag\":\"mate\",\"ridge\":600,\"a\":120,\"owners\":[91]},{\"tag\":\"mate\",\"ridge\":408,\"a\":92,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":792,\"a\":94,\"owners\":[121]},{\"tag\":\"mate\",\"ridge\":792,\"a\":121,\"owners\":[94]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[31,32,34,35,75,78],\"full_literals\":[-49,2,3,4,5,15,17]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[44,45,47,48,86,89],\"full_literals\":[-50,6,7,9,10,22,25]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-51,false,49],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-52,50,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-53,51,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-53,false,52],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-54,53,false],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":46,\"full_literals\":[-8,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":74,\"full_literals\":[-14,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":85,\"full_literals\":[-21,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":105,\"full_literals\":[-30,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":106,\"full_literals\":[-31,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":109,\"full_literals\":[-34,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":115,\"full_literals\":[-39,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":123,\"full_literals\":[-46,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":76,\"full_literals\":[-16,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":79,\"full_literals\":[-18,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":83,\"full_literals\":[-20,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":87,\"full_literals\":[-23,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":88,\"full_literals\":[-24,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":90,\"full_literals\":[-26,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":91,\"full_literals\":[-27,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":94,\"full_literals\":[-29,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":114,\"full_literals\":[-38,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":107,\"full_literals\":[-32,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":108,\"full_literals\":[-33,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":110,\"full_literals\":[-35,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":111,\"full_literals\":[-36,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":112,\"full_literals\":[-37,61]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[116,117,119,120,121,126],\"full_literals\":[-62,40,41,43,44,45,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":116,\"full_literals\":[-40,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":117,\"full_literals\":[-41,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":119,\"full_literals\":[-43,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":120,\"full_literals\":[-44,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":121,\"full_literals\":[-45,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":126,\"full_literals\":[-48,62]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-56,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-55,false,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-58,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-57,false,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-64,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-63,false,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-60,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-59,false,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-62,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-61,false,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-68,false,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-61,-62,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-68,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-66,-67,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-66,-68,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-70,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-65,-69,71],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":33,\"owners\":[11,34,47,59,62,64,76,79,81,83,87,90,92,94,107,110,112,116,119,121]}]}"
  "99 53 0 50 49 0\n100 51 0 99 47 0\n101 52 0 99 48 0\n102 49 0 100 45 0\n103 50 0 101 46 0\n104 -70 0 97 95 0\n105 1 4 9 11 12 13 16 18 20 23 26 29 32 35 37 40 43 45 0 29 40 98 0\n106 -68 21 0 104 90 94 86 62 63 64 65 66 67 35 36 38 39 42 33 73 0\n107 61 65 0 103 84 83 55 82 58 54 85 80 52 24 20 56 22 68 69 70 71 72 13 2 18 4 44 0\n108 65 0 102 84 85 82 80 81 57 58 53 51 23 106 107 91 74 75 76 77 78 79 12 17 19 32 21 1 3 43 0\n109 -69 0 108 97 96 0\n110 -68 0 109 92 0\n111 59 62 0 40 29 78 41 76 37 74 34 12 59 60 61 5 7 9 10 26 8 28 31 105 0\n112 62 0 109 74 76 78 12 34 37 41 111 87 93 89 68 70 72 13 25 11 15 16 27 14 30 105 0\n113 67 0 112 88 0\n114 -61 0 112 110 91 0\n115 -66 0 113 109 93 0\n116 -32 0 114 68 0\n117 -35 0 114 70 0\n118 -37 0 114 72 0\n119 -60 0 115 86 0\n120 -9 0 116 117 118 13 0\n121 -16 0 116 25 0\n122 -18 0 117 27 0\n123 -20 0 118 30 0\n124 -23 0 119 62 0\n125 -26 0 119 64 0\n126 -29 0 119 66 0\n127 -1 0 121 122 29 123 124 125 40 126 5 0\n128 -12 0 121 29 123 124 40 126 9 0\n129 -13 0 121 122 29 124 125 40 10 0\n130 -11 0 122 29 123 125 40 126 8 0\n131 -4 0 124 125 40 126 6 0\n132 -40 0 124 35 0\n133 -43 0 125 38 0\n134 -45 0 126 42 0\n135 0 127 130 131 120 128 129 121 122 123 124 125 126 116 117 118 132 133 134 105 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record003.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record003.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record003.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record003.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record003 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record003.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record003.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record003.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record003.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record003 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record003_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record003 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record003_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00283.record003_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00283.record003
