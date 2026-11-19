module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00001Data
public import GraphInputsRow24Part00001Frames
public import GraphInputsRow24Part00001Leaves
public import GraphInputsRow24Part00001Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00001.record007
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record007
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨87, by decide⟩, ⟨90, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [14293659549696, 54975849824256, 117093590311632896, 450359962737049600, (certNat% 2), (certNat% 3), (certNat% 4)]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record007_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record007_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00001.record007

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00001.record032
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record032
def vertexColumn : Fields := ⟨10, (certNat% 5)⟩
def kindColumn : Fields := ⟨3, (certNat% 6)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨33, by decide⟩, ⟨37, by decide⟩, ⟨41, by decide⟩, ⟨45, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), 13979173243358019584, (certNat% 8), (certNat% 9), (certNat% 10), (certNat% 11)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), (certNat% 13), (certNat% 14), (certNat% 15), (certNat% 9), (certNat% 16)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), (certNat% 13), (certNat% 18), 13979173243358019584, (certNat% 19), (certNat% 10)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), (certNat% 21), (certNat% 22), (certNat% 23), (certNat% 16), (certNat% 13)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), (certNat% 22), (certNat% 25), (certNat% 23), (certNat% 16), 4755801206907994112, (certNat% 26)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c5 c3
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c6 c0
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record032_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record032_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record032_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record032_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record032_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record032_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record032_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record032_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record032_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00001.record032

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00001.record008
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3c4f0ab29a9c6658b65386e2785e0fbc1ac669e1745b15c5c96a5995952d54d1b49d176c370f23a8e63a4d938ccb392d4b8ac6b26c5b61d4731d2729c6745c9715c3743c8f13c2f07c3ce0b420eb81d043961545254351342d07703a0d8390d4388c930cc4b0ac1b"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "d36db6db49b49a6da49249249249249249b6da69b491249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record008 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record008 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record008.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record008.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record008.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 34), (facetIndex 61), (facetIndex 68)]))
 (.leaf ([(facetIndex 35), (facetIndex 62), (facetIndex 69)])))
 (.branch 3
 (.leaf ([(facetIndex 74), (facetIndex 79)]))
 (.leaf ([(facetIndex 76), (facetIndex 80)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 63), (facetIndex 65)]))
 (.leaf ([(facetIndex 28), (facetIndex 29), (facetIndex 31), (facetIndex 33), (facetIndex 36), (facetIndex 37)])))
 (.branch 7
 (.leaf ([(facetIndex 72), (facetIndex 73), (facetIndex 75), (facetIndex 77), (facetIndex 78)]))
 (.leaf ([(facetIndex 82)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1c35b3cb600802084z11;2d228a2dz15;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record008 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record008_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00001.record008" "{\"atoms\":[{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00001.record008" 46

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00001.record008" "{\"ridges\":[[5,546],[16,324],[17,388],[29,270],[33,278],[36,294],[38,324],[39,388],[43,546],[47,546],[50,546],[51,546],[52,546],[58,324],[60,388],[61,612],[62,676],[63,804],[64,324],[66,324],[67,388],[75,270],[77,278],[78,198],[82,708]],\"owners\":[[5,546,[79,80],[43,47,50,51,52]],[43,546,[80],[5,47,50,51,52,79]],[47,546,[79],[5,43,50,51,52,80]],[50,546,[80],[5,43,47,51,52,79]],[51,546,[79],[5,43,47,50,52,80]],[52,546,[79,80],[5,43,47,50,51]],[16,324,[75,78,82],[38,58,64,66]],[38,324,[82],[16,58,64,66,75,78]],[58,324,[78,82],[16,38,64,66,75]],[64,324,[75],[16,38,58,66,78,82]],[66,324,[75,78],[16,38,58,64,82]],[17,388,[77,78,82],[39,60,64,67]],[39,388,[82],[17,60,64,67,77,78]],[60,388,[78,82],[17,39,64,67,77]],[67,388,[77,78],[17,39,60,64,82]],[29,270,[75],[]],[75,270,[29],[]],[33,278,[77],[]],[77,278,[33],[]],[36,294,[],[]],[78,198,[37],[]],[61,612,[],[]],[62,676,[],[]],[63,804,[],[]],[82,708,[65],[]]],\"edges\":[[22,[16,17,29,33,36,38,39,58,60,63,64,66,67,75,77,78,82]],[38,[5,43,47,50,51,52,61,62,63,68,69,79,80]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00001.record008" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00001.record008\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,29,30],[-10,30],[-11,29],[-12,30],[-13,29],[-14,29,30],[-2,26,28,31],[-8,31],[-15,28,31],[-20,26],[-22,26,28],[-3,27,28,31],[-9,31],[-16,28,31],[-23,27,28],[-4,26],[-26,4],[-5,27],[-27,5],[-6],[-28,7],[-17],[-18],[-19],[-31,21],[-24,32],[-25,33],[-29,34],[-30,35],[-21,36],[-4,37],[-5,37],[-7,37],[-26,38],[-27,38],[-28,38],[-31,39],[-33,40],[-32,40],[-35,41],[-34,41],[-41,42],[-40,42],[-37,43],[-36,43],[-39,44],[-38,44],[-43,-44,45],[-42,-45,46],[-46],[2,3,4,5,6,8,9,15,16,19,20,22,23,26,27,28,31],[1,10,11,12,13,14,17,18,19,24,25,29,30]],\"atoms\":[{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":546,\"a\":5,\"owners\":[79,80]},{\"tag\":\"mate\",\"ridge\":546,\"a\":43,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":546,\"a\":47,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":546,\"a\":50,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":546,\"a\":51,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":546,\"a\":52,\"owners\":[79,80]},{\"tag\":\"mate\",\"ridge\":324,\"a\":16,\"owners\":[75,78,82]},{\"tag\":\"mate\",\"ridge\":324,\"a\":38,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":324,\"a\":58,\"owners\":[78,82]},{\"tag\":\"mate\",\"ridge\":324,\"a\":64,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":324,\"a\":66,\"owners\":[75,78]},{\"tag\":\"mate\",\"ridge\":388,\"a\":17,\"owners\":[77,78,82]},{\"tag\":\"mate\",\"ridge\":388,\"a\":39,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":388,\"a\":60,\"owners\":[78,82]},{\"tag\":\"mate\",\"ridge\":388,\"a\":67,\"owners\":[77,78]},{\"tag\":\"mate\",\"ridge\":270,\"a\":29,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":270,\"a\":75,\"owners\":[29]},{\"tag\":\"mate\",\"ridge\":278,\"a\":33,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":278,\"a\":77,\"owners\":[33]},{\"tag\":\"mate\",\"ridge\":294,\"a\":36,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":198,\"a\":78,\"owners\":[37]},{\"tag\":\"mate\",\"ridge\":612,\"a\":61,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":676,\"a\":62,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":804,\"a\":63,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":708,\"a\":82,\"owners\":[65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":68,\"full_literals\":[-24,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":69,\"full_literals\":[-25,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":79,\"full_literals\":[-29,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":80,\"full_literals\":[-30,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":65,\"full_literals\":[-21,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":29,\"full_literals\":[-4,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":33,\"full_literals\":[-5,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":37,\"full_literals\":[-7,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":75,\"full_literals\":[-26,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":77,\"full_literals\":[-27,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":78,\"full_literals\":[-28,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":82,\"full_literals\":[-31,39]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-33,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-32,false,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-35,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-34,false,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-41,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-40,false,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-37,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-36,false,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-39,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-38,false,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-43,-44,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-42,-45,46],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":22,\"owners\":[16,17,29,33,36,38,39,58,60,63,64,66,67,75,77,78,82]},{\"tag\":\"edge\",\"edge\":38,\"owners\":[5,43,47,50,51,52,61,62,63,68,69,79,80]}]}"
  "53 2 3 4 5 8 9 15 16 20 22 23 26 27 28 31 0 20 24 51 0\n54 1 10 11 12 13 14 24 25 29 30 0 22 23 24 52 0\n55 42 0 42 43 40 41 38 39 29 28 27 26 2 4 1 3 5 6 54 0\n56 -45 0 55 50 49 0\n57 43 0 44 45 31 32 33 30 17 19 21 25 10 9 14 7 11 12 15 8 13 53 0\n58 -44 0 57 56 48 0\n59 -39 0 58 46 0\n60 -38 0 58 47 0\n61 -31 0 59 37 0\n62 -26 0 60 34 0\n63 -27 0 60 35 0\n64 -28 0 60 36 0\n65 -8 0 61 8 0\n66 -9 0 61 13 0\n67 -20 0 62 10 0\n68 -4 0 62 16 0\n69 -5 0 63 18 0\n70 -15 0 64 61 9 0\n71 -16 0 64 61 14 0\n72 -2 0 64 62 61 7 0\n73 -22 0 64 62 11 0\n74 -3 0 64 63 61 12 0\n75 -23 0 64 63 15 0\n76 0 74 65 72 68 69 66 70 71 67 73 75 62 63 64 61 53 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record008.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record008.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record008.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record008.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record008 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record008.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record008.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record008.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record008.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record008 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record008_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record008 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record008_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record008_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00001.record008

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00001.record022
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3c4f09b25ab86d1ac6719a6598b61b89e17bc16c569e1745b15c5c95a5596952d64d1b49d17783d0ec370da358d934ccb352d2b1ac9b16f07a1d8791d4731d2729c6715c8f0f03a258361382e07b81d0439a1645254351342d0758350d2324c3312c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db6db69249b4936da492493492492493492492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record022 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record022 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record022.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record022.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record022.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 65), (facetIndex 66), (facetIndex 67), (facetIndex 70)]))
 (.leaf ([(facetIndex 30), (facetIndex 71), (facetIndex 72), (facetIndex 73)])))
 (.branch 3
 (.leaf ([(facetIndex 39), (facetIndex 56), (facetIndex 59), (facetIndex 60)]))
 (.leaf ([(facetIndex 37), (facetIndex 55), (facetIndex 57), (facetIndex 58)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 41), (facetIndex 43), (facetIndex 44), (facetIndex 45)]))
 (.leaf ([(facetIndex 42), (facetIndex 46), (facetIndex 47), (facetIndex 48)])))
 (.branch 7
 (.leaf ([(facetIndex 33), (facetIndex 50), (facetIndex 74)]))
 (.branch 8
 (.leaf ([(facetIndex 31), (facetIndex 32), (facetIndex 34), (facetIndex 35), (facetIndex 36), (facetIndex 38)]))
 (.leaf ([(facetIndex 49), (facetIndex 51), (facetIndex 53), (facetIndex 54)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "611100000000002233238808685554445402737776771z1e;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 61), (facetIndex 68)]))
 (.leaf ([(facetIndex 62), (facetIndex 69)])))
 (.branch 3
 (.leaf ([(facetIndex 75), (facetIndex 81)]))
 (.leaf ([(facetIndex 76), (facetIndex 82)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 40), (facetIndex 52), (facetIndex 64)]))
 (.leaf ([(facetIndex 77), (facetIndex 78), (facetIndex 79)])))
 (.branch 7
 (.leaf ([(facetIndex 80), (facetIndex 83), (facetIndex 84)]))
 (.leaf ([(facetIndex 63)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6cd6b6b400008004e40000004000000004z1e;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2, 3]
def grouped2_0006 : List Nat := [4, 5]
def grouped2_0007 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0008 : List Nat := [6]
def grouped2_0009 : List Nat := [6, 7, 8]
def grouped2_0010 : List Nat := [7]
def grouped2_0011 : List Nat := [7, 8]
def grouped2_0012 : List Nat := [8]
def grouped3_0013 : List Nat := [0]
def grouped3_0014 : List Nat := [0, 1]
def grouped3_0015 : List Nat := [0, 1, 2, 3]
def grouped3_0017 : List Nat := [1]
def grouped3_0018 : List Nat := [2]
def grouped3_0019 : List Nat := [2, 3]
def grouped3_0020 : List Nat := [3]
def grouped3_0021 : List Nat := [4]
def grouped3_0022 : List Nat := [4, 5]
def grouped3_0023 : List Nat := [4, 5, 6, 7]
def grouped3_0024 : List Nat := [5]
def grouped3_0025 : List Nat := [6]
def grouped3_0026 : List Nat := [6, 7]
def grouped3_0027 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record022 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record022_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00001.record022" "{\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00001.record022" 59

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00001.record022" "{\"ridges\":[[10,289],[10,290],[21,832],[22,896],[34,289],[34,290],[44,289],[44,290],[47,289],[47,290],[49,289],[49,290],[50,290],[51,386],[53,832],[54,896],[61,356],[63,804],[65,644],[66,832],[67,896],[68,360],[70,896],[76,420],[80,774],[82,432],[83,706],[84,452]],\"owners\":[[10,289,[61,62,63,68,69],[34,44,47,49,50]],[34,289,[68,69],[10,44,47,49,50,61,62,63]],[44,289,[61,62,63,69],[10,34,47,49,50,68]],[47,289,[61,62,63,68],[10,34,44,49,50,69]],[49,289,[62,63,69],[10,34,44,47,50,61,68]],[10,290,[75,76,81,82],[34,44,47,49,50]],[34,290,[81,82],[10,44,47,49,50,75,76]],[44,290,[75,76,82],[10,34,47,49,50,81]],[47,290,[75,76,81],[10,34,44,49,50,82]],[49,290,[76,82],[10,34,44,47,50,75,81]],[50,290,[75,81],[10,34,44,47,49,76,82]],[51,386,[76,80,82],[12,38,48,50,54,77,83]],[65,644,[80],[19,39,60,67,78,84]],[21,832,[79,83,84],[53,66,70]],[53,832,[84],[21,66,70,79,83]],[66,832,[83],[21,53,70,79,84]],[22,896,[80,83,84],[54,67,70]],[54,896,[84],[22,67,70,80,83]],[67,896,[83],[22,54,70,80,84]],[70,896,[80],[22,54,67,83,84]],[80,774,[40,79],[]],[83,706,[52,78],[]],[61,356,[75],[]],[76,420,[62],[]],[63,804,[],[]],[84,452,[64,77],[]],[68,360,[81],[]],[82,432,[69],[]]],\"edges\":[[37,[10,34,44,47,49,50,61,62,63,68,69,75,76,81,82]],[44,[21,22,40,53,54,63,66,67,70,79,80,83,84]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00001.record022" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00001.record022\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,14,15,16,21,22],[-4,21,22],[-6,14,15,16,22],[-7,14,15,16,21],[-8,15,16,22],[-1,24,25,30,31],[-4,30,31],[-6,24,25,31],[-7,24,25,30],[-8,25,31],[-9,24,30],[-10,25,29,31],[-18,29],[-2,28,32,33],[-12,33],[-19,32],[-3,29,32,33],[-13,33],[-20,32],[-23,29],[-29,5,28],[-32,11,27],[-14,24],[-25,15],[-16],[-33,17,26],[-21,30],[-31,22],[-34,18,19,20,23],[-35,8,10,12,13],[-36,34],[-37,36],[-38,35],[-39,38],[-40,39],[-41,37,40],[41],[-14,42],[-21,42],[-15,43],[-22,43],[-24,44],[-30,44],[-25,45],[-31,45],[-5,46],[-11,46],[-17,46],[-26,47],[-27,47],[-28,47],[-48,29,32,33],[-29,48],[-32,48],[-33,48],[-49,16],[-43,50],[-42,50],[-45,51],[-44,51],[-44,-45,52],[-51,53],[-52,54],[-50,53],[-50,-51,54],[-47,55],[-46,55],[-56,48,49],[-48,56],[-55,57],[-55,-56,58],[-53,-58,59],[-54,-57,59],[-59],[1,4,6,7,8,9,14,15,16,21,22,24,25,30,31],[2,3,5,12,13,16,19,20,23,28,29,32,33]],\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":289,\"a\":10,\"owners\":[61,62,63,68,69]},{\"tag\":\"mate\",\"ridge\":289,\"a\":34,\"owners\":[68,69]},{\"tag\":\"mate\",\"ridge\":289,\"a\":44,\"owners\":[61,62,63,69]},{\"tag\":\"mate\",\"ridge\":289,\"a\":47,\"owners\":[61,62,63,68]},{\"tag\":\"mate\",\"ridge\":289,\"a\":49,\"owners\":[62,63,69]},{\"tag\":\"mate\",\"ridge\":290,\"a\":10,\"owners\":[75,76,81,82]},{\"tag\":\"mate\",\"ridge\":290,\"a\":34,\"owners\":[81,82]},{\"tag\":\"mate\",\"ridge\":290,\"a\":44,\"owners\":[75,76,82]},{\"tag\":\"mate\",\"ridge\":290,\"a\":47,\"owners\":[75,76,81]},{\"tag\":\"mate\",\"ridge\":290,\"a\":49,\"owners\":[76,82]},{\"tag\":\"mate\",\"ridge\":290,\"a\":50,\"owners\":[75,81]},{\"tag\":\"mate\",\"ridge\":386,\"a\":51,\"owners\":[76,80,82]},{\"tag\":\"mate\",\"ridge\":644,\"a\":65,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":832,\"a\":21,\"owners\":[79,83,84]},{\"tag\":\"mate\",\"ridge\":832,\"a\":53,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":832,\"a\":66,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":896,\"a\":22,\"owners\":[80,83,84]},{\"tag\":\"mate\",\"ridge\":896,\"a\":54,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":896,\"a\":67,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":896,\"a\":70,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":774,\"a\":80,\"owners\":[40,79]},{\"tag\":\"mate\",\"ridge\":706,\"a\":83,\"owners\":[52,78]},{\"tag\":\"mate\",\"ridge\":356,\"a\":61,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":420,\"a\":76,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":804,\"a\":63,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":452,\"a\":84,\"owners\":[64,77]},{\"tag\":\"mate\",\"ridge\":360,\"a\":68,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":432,\"a\":82,\"owners\":[69]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[65,66,67,70],\"full_literals\":[-34,18,19,20,23]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[49,51,53,54],\"full_literals\":[-35,8,10,12,13]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-36,34,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-37,36,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-38,false,35],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-39,false,38],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-40,false,39],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-41,37,40],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":61,\"full_literals\":[-14,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":68,\"full_literals\":[-21,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":62,\"full_literals\":[-15,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":69,\"full_literals\":[-22,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":75,\"full_literals\":[-24,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":81,\"full_literals\":[-30,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":76,\"full_literals\":[-25,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":82,\"full_literals\":[-31,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":40,\"full_literals\":[-5,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":52,\"full_literals\":[-11,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":64,\"full_literals\":[-17,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":77,\"full_literals\":[-26,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":78,\"full_literals\":[-27,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":79,\"full_literals\":[-28,47]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[80,83,84],\"full_literals\":[-48,29,32,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":80,\"full_literals\":[-29,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":83,\"full_literals\":[-32,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":84,\"full_literals\":[-33,48]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[63],\"full_literals\":[-49,16]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-43,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-42,false,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-45,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-44,false,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-44,-45,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-51,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-52,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-50,false,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-50,-51,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-47,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-46,false,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-56,48,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-48,false,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-55,false,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-55,-56,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-53,-58,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-54,-57,59],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":37,\"owners\":[10,34,44,47,49,50,61,62,63,68,69,75,76,81,82]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[21,22,40,53,54,63,66,67,70,79,80,83,84]}]}"
  "77 -49 0 25 56 0\n78 -56 48 0 77 68 0\n79 1 4 6 7 8 9 14 15 21 22 24 25 30 31 0 25 75 0\n80 2 3 5 12 13 19 20 23 28 29 32 33 0 25 76 0\n81 53 0 62 64 59 60 57 58 44 45 42 43 40 41 38 39 10 6 8 9 11 7 79 0\n82 -58 0 81 74 72 0\n83 -56 0 82 78 71 66 67 49 50 51 46 47 48 22 21 26 52 0\n84 -48 0 83 69 0\n85 -29 0 84 53 0\n86 -32 0 84 54 0\n87 -33 0 84 55 0\n88 -18 0 85 13 0\n89 -3 0 85 86 87 17 0\n90 -23 0 85 20 0\n91 -19 0 86 16 0\n92 -20 0 86 19 0\n93 -12 0 87 15 0\n94 -13 0 87 18 0\n95 -34 0 88 91 92 90 29 0\n96 -36 0 95 31 0\n97 -37 0 96 32 0\n98 40 0 97 37 36 0\n99 39 0 98 35 0\n100 38 0 99 34 0\n101 35 0 100 33 0\n102 25 31 0 101 93 94 85 10 12 30 0\n103 45 0 44 45 102 0\n104 51 0 103 59 0\n105 54 0 103 104 25 63 61 65 42 43 57 11 23 27 40 41 1 3 4 2 5 24 28 79 0\n106 -57 0 105 74 73 0\n107 -55 0 106 70 0\n108 -47 0 107 66 0\n109 -46 0 107 67 0\n110 -28 0 108 51 0\n111 -5 0 109 46 0\n112 -2 0 110 86 87 14 0\n113 0 110 111 94 112 89 91 92 90 93 85 86 87 80 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record022.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record022.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record022.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record022.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record022 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record022.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record022.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record022.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record022.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record022 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record022_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record022_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record022_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record022_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record022_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record022_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record022_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record022 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record022_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record022_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record022_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00001.record022

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00001.record030
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3c2e2b4aaaa5a2eb86d1aa695876c3a2e8783ef0789d25a9564b9e1745695551d70d4b51d0f783d0ec370cb31cf0ba2d8b92d4b26c5bc1e8761e4751ca719e0f43c2f07f88d128a2a83a918560d9892a439514550d4a314c3322c2b06c4709c17"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "34d34d349b69a69a69a4db4db69349b49b6924da449249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record030 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record030 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record030.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record030.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record030.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 31), (facetIndex 32), (facetIndex 53), (facetIndex 68)]))
 (.branch 2
 (.leaf ([(facetIndex 36), (facetIndex 37), (facetIndex 57), (facetIndex 72)]))
 (.leaf ([(facetIndex 25), (facetIndex 26), (facetIndex 48), (facetIndex 49), (facetIndex 63), (facetIndex 64)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 33), (facetIndex 43), (facetIndex 44)]))
 (.leaf ([(facetIndex 40), (facetIndex 61), (facetIndex 76)])))
 (.branch 6
 (.leaf ([(facetIndex 45), (facetIndex 50), (facetIndex 55), (facetIndex 59)]))
 (.leaf ([(facetIndex 46), (facetIndex 65), (facetIndex 70), (facetIndex 74)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "4181180032420a08a001521ab60400901800009z13;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1, 2]
def grouped3_0003 : List Nat := [1]
def grouped3_0004 : List Nat := [1, 2]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [3]
def grouped3_0007 : List Nat := [3, 4]
def grouped3_0008 : List Nat := [3, 4, 5, 6]
def grouped3_0009 : List Nat := [4]
def grouped3_0010 : List Nat := [5]
def grouped3_0011 : List Nat := [5, 6]
def grouped3_0012 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record030 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record030_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00001.record030" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00001.record030" 56

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00001.record030" "{\"ridges\":[[11,261],[11,321],[14,385],[20,642],[21,772],[21,832],[22,776],[22,896],[25,270],[26,525],[29,261],[31,390],[32,645],[33,771],[38,385],[39,522],[40,522],[43,450],[44,705],[45,771],[45,832],[46,771],[48,284],[49,300],[50,525],[52,261],[52,321],[53,420],[54,261],[54,772],[55,645],[55,772],[57,344],[58,385],[59,585],[60,265],[60,896],[61,705],[61,832],[63,540],[64,556],[65,270],[65,776],[68,676],[69,518],[69,578],[69,772],[70,390],[70,896],[72,600],[73,642],[74,330],[75,522],[75,896],[76,450],[76,832]],\"owners\":[[11,261,[25,31,33,48,49,50,53,55],[29,52,54]],[29,261,[48,49,50,53,55],[11,25,31,33,52,54]],[52,261,[25,31,33,49,50,53,55],[11,29,48,54]],[54,261,[25,31,48,49,53],[11,29,33,50,52,55]],[11,321,[36,43,45,57,59,61],[29,52,54]],[52,321,[36,43,45,59,61],[11,29,54,57]],[60,265,[25,36,48,49,57],[14,38,40,50,58,59]],[14,385,[31,43,46,53,55,61],[38,58,60]],[38,385,[53,55,61],[14,31,43,46,58,60]],[58,385,[31,43,46,55,61],[14,38,53,60]],[69,518,[26,32,63,64,68],[17,30,33,65,67,70]],[69,578,[37,44,72],[17,30,45,67,74,76]],[39,522,[63,64,65,72,74],[20,26,37,40,73,75]],[40,522,[20,63,64,72,73],[26,37,39,65,74,75]],[75,522,[26,37,63,64,72],[20,39,40,65,73,74]],[20,642,[32,44,46,68,70,76],[39,73,75]],[73,642,[32,44,46,70,76],[20,39,68,75]],[21,772,[33,50,55,65,70],[54,69]],[54,772,[65,70],[21,33,50,55,69]],[55,772,[21,65,69],[33,50,54,70]],[69,772,[50,55],[21,33,54,65,70]],[21,832,[45,59,61,74,76],[54,69]],[45,832,[21],[54,59,61,69,74,76]],[61,832,[21,69,74],[45,54,59,76]],[76,832,[21,54,59],[45,61,69,74]],[22,776,[40,50,59,65,74],[60,75]],[65,776,[22,59,60],[40,50,74,75]],[22,896,[46,55,61,70,76],[60,75]],[60,896,[70,76],[22,46,55,61,75]],[70,896,[22,60,61],[46,55,75,76]],[75,896,[55,61],[22,46,60,70,76]],[25,270,[65],[]],[65,270,[25],[]],[26,525,[50],[]],[50,525,[26],[]],[31,390,[70],[]],[70,390,[31],[]],[32,645,[55],[]],[55,645,[32],[]],[74,330,[36],[]],[59,585,[37],[]],[43,450,[76],[]],[76,450,[43],[]],[44,705,[61],[]],[61,705,[44],[]],[48,284,[],[]],[49,300,[],[]],[53,420,[],[]],[57,344,[],[]],[63,540,[],[]],[64,556,[],[]],[68,676,[],[]],[72,600,[],[]]],\"edges\":[[22,[11,21,25,29,31,33,48,49,50,52,53,54,55,65,69,70]],[29,[20,22,26,37,39,40,50,59,60,63,64,65,72,73,74,75]],[40,[11,21,29,36,43,45,52,54,57,59,61,69,74,76]],[42,[14,22,31,38,43,46,53,55,58,60,61,70,75,76]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00001.record030" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00001.record030\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-12,-11],[-13,-11],[-19,-6],[-19,-7],[-19,-9],[-19,-10],[-19,-12],[-19,-13],[-20,-17],[-23,-20],[-27,-13],[-30,-27],[-32,-11],[-32,-20],[-35,-20],[-38,-6],[-38,-12],[-38,-16],[-38,-35],[-41,-38],[-43,-11],[-43,-20],[-1,6,9,11,21,22,23,25,27],[-8,21,22,23,25,27],[-24,6,9,11,22,23,25,27],[-26,6,9,21,22,25],[-1,12,17,19,28,30,32],[-24,12,17,19,30,32],[-31,6,12,21,22,28],[-2,9,17,20,25,27,32],[-14,25,27,32],[-29,9,17,20,27,32],[-37,7,10,33,34,36],[-37,13,18,39],[-15,33,34,35,39,41],[-16,3,33,34,39,40],[-42,7,13,33,34,39],[-3,10,18,20,36,38,43],[-40,10,18,20,38,43],[-4,11,23,27,35,38],[-26,35,38],[-27,4,35,37],[-37,23,27],[-4,19,30,32,41,43],[-19,4],[-32,4,37,41],[-43,4,26,30],[-5,16,23,30,35,41],[-35,5,30,31],[-5,20,27,32,38,43],[-31,38,43],[-38,5,31,32],[-42,27,32],[-6,35],[-35,6],[-7,23],[-23,7],[-9,38],[-38,9],[-10,27],[-27,10],[-11,-19,-20],[-41,12],[-30,13],[-17,43],[-43,17],[-18,32],[-32,18],[-21],[-22],[-25],[-28],[-33],[-34],[-36],[-39],[-44,9,10,25,36],[-9,44],[-10,44],[-45,12,13,28,39],[-12,45],[-13,45],[-46,6,7,21,22,33,34],[-6,46],[-7,46],[-17,47],[-18,47],[-32,48],[-43,48],[-49,19,23,27,30],[-19,49],[-23,49],[-27,49],[-30,49],[-50,20,35,38,41],[-20,50],[-35,50],[-38,50],[-41,50],[-51,45,46],[-46,51],[-45,51],[-52,44,51],[-51,52],[-44,52],[-47,-48,53],[-54,49],[-54,50],[-49,-50,54],[-54,55],[-53,55],[-52,-55,56],[-56],[1,4,6,8,9,11,21,22,23,24,25,26,27,35,37,38],[3,5,7,13,15,16,23,30,31,33,34,35,39,40,41,42],[1,4,8,12,17,19,24,26,28,30,32,37,41,43],[2,5,9,14,17,20,25,27,29,31,32,38,42,43]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":36,\"b\":33},{\"tag\":\"incompatible\",\"a\":37,\"b\":33},{\"tag\":\"incompatible\",\"a\":45,\"b\":25},{\"tag\":\"incompatible\",\"a\":45,\"b\":26},{\"tag\":\"incompatible\",\"a\":45,\"b\":31},{\"tag\":\"incompatible\",\"a\":45,\"b\":32},{\"tag\":\"incompatible\",\"a\":45,\"b\":36},{\"tag\":\"incompatible\",\"a\":45,\"b\":37},{\"tag\":\"incompatible\",\"a\":46,\"b\":43},{\"tag\":\"incompatible\",\"a\":50,\"b\":46},{\"tag\":\"incompatible\",\"a\":55,\"b\":37},{\"tag\":\"incompatible\",\"a\":59,\"b\":55},{\"tag\":\"incompatible\",\"a\":61,\"b\":33},{\"tag\":\"incompatible\",\"a\":61,\"b\":46},{\"tag\":\"incompatible\",\"a\":65,\"b\":46},{\"tag\":\"incompatible\",\"a\":70,\"b\":25},{\"tag\":\"incompatible\",\"a\":70,\"b\":36},{\"tag\":\"incompatible\",\"a\":70,\"b\":40},{\"tag\":\"incompatible\",\"a\":70,\"b\":65},{\"tag\":\"incompatible\",\"a\":74,\"b\":70},{\"tag\":\"incompatible\",\"a\":76,\"b\":33},{\"tag\":\"incompatible\",\"a\":76,\"b\":46},{\"tag\":\"mate\",\"ridge\":261,\"a\":11,\"owners\":[25,31,33,48,49,50,53,55]},{\"tag\":\"mate\",\"ridge\":261,\"a\":29,\"owners\":[48,49,50,53,55]},{\"tag\":\"mate\",\"ridge\":261,\"a\":52,\"owners\":[25,31,33,49,50,53,55]},{\"tag\":\"mate\",\"ridge\":261,\"a\":54,\"owners\":[25,31,48,49,53]},{\"tag\":\"mate\",\"ridge\":321,\"a\":11,\"owners\":[36,43,45,57,59,61]},{\"tag\":\"mate\",\"ridge\":321,\"a\":52,\"owners\":[36,43,45,59,61]},{\"tag\":\"mate\",\"ridge\":265,\"a\":60,\"owners\":[25,36,48,49,57]},{\"tag\":\"mate\",\"ridge\":385,\"a\":14,\"owners\":[31,43,46,53,55,61]},{\"tag\":\"mate\",\"ridge\":385,\"a\":38,\"owners\":[53,55,61]},{\"tag\":\"mate\",\"ridge\":385,\"a\":58,\"owners\":[31,43,46,55,61]},{\"tag\":\"mate\",\"ridge\":518,\"a\":69,\"owners\":[26,32,63,64,68]},{\"tag\":\"mate\",\"ridge\":578,\"a\":69,\"owners\":[37,44,72]},{\"tag\":\"mate\",\"ridge\":522,\"a\":39,\"owners\":[63,64,65,72,74]},{\"tag\":\"mate\",\"ridge\":522,\"a\":40,\"owners\":[20,63,64,72,73]},{\"tag\":\"mate\",\"ridge\":522,\"a\":75,\"owners\":[26,37,63,64,72]},{\"tag\":\"mate\",\"ridge\":642,\"a\":20,\"owners\":[32,44,46,68,70,76]},{\"tag\":\"mate\",\"ridge\":642,\"a\":73,\"owners\":[32,44,46,70,76]},{\"tag\":\"mate\",\"ridge\":772,\"a\":21,\"owners\":[33,50,55,65,70]},{\"tag\":\"mate\",\"ridge\":772,\"a\":54,\"owners\":[65,70]},{\"tag\":\"mate\",\"ridge\":772,\"a\":55,\"owners\":[21,65,69]},{\"tag\":\"mate\",\"ridge\":772,\"a\":69,\"owners\":[50,55]},{\"tag\":\"mate\",\"ridge\":832,\"a\":21,\"owners\":[45,59,61,74,76]},{\"tag\":\"mate\",\"ridge\":832,\"a\":45,\"owners\":[21]},{\"tag\":\"mate\",\"ridge\":832,\"a\":61,\"owners\":[21,69,74]},{\"tag\":\"mate\",\"ridge\":832,\"a\":76,\"owners\":[21,54,59]},{\"tag\":\"mate\",\"ridge\":776,\"a\":22,\"owners\":[40,50,59,65,74]},{\"tag\":\"mate\",\"ridge\":776,\"a\":65,\"owners\":[22,59,60]},{\"tag\":\"mate\",\"ridge\":896,\"a\":22,\"owners\":[46,55,61,70,76]},{\"tag\":\"mate\",\"ridge\":896,\"a\":60,\"owners\":[70,76]},{\"tag\":\"mate\",\"ridge\":896,\"a\":70,\"owners\":[22,60,61]},{\"tag\":\"mate\",\"ridge\":896,\"a\":75,\"owners\":[55,61]},{\"tag\":\"mate\",\"ridge\":270,\"a\":25,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":270,\"a\":65,\"owners\":[25]},{\"tag\":\"mate\",\"ridge\":525,\"a\":26,\"owners\":[50]},{\"tag\":\"mate\",\"ridge\":525,\"a\":50,\"owners\":[26]},{\"tag\":\"mate\",\"ridge\":390,\"a\":31,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":390,\"a\":70,\"owners\":[31]},{\"tag\":\"mate\",\"ridge\":645,\"a\":32,\"owners\":[55]},{\"tag\":\"mate\",\"ridge\":645,\"a\":55,\"owners\":[32]},{\"tag\":\"three\",\"ridge\":771,\"vertices\":[33,45,46]},{\"tag\":\"mate\",\"ridge\":330,\"a\":74,\"owners\":[36]},{\"tag\":\"mate\",\"ridge\":585,\"a\":59,\"owners\":[37]},{\"tag\":\"mate\",\"ridge\":450,\"a\":43,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":450,\"a\":76,\"owners\":[43]},{\"tag\":\"mate\",\"ridge\":705,\"a\":44,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":705,\"a\":61,\"owners\":[44]},{\"tag\":\"mate\",\"ridge\":284,\"a\":48,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":300,\"a\":49,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":420,\"a\":53,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":344,\"a\":57,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":540,\"a\":63,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":556,\"a\":64,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":676,\"a\":68,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":600,\"a\":72,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[31,32,53,68],\"full_literals\":[-44,9,10,25,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":31,\"full_literals\":[-9,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":32,\"full_literals\":[-10,44]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[36,37,57,72],\"full_literals\":[-45,12,13,28,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":36,\"full_literals\":[-12,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":37,\"full_literals\":[-13,45]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[25,26,48,49,63,64],\"full_literals\":[-46,6,7,21,22,33,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":25,\"full_literals\":[-6,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":26,\"full_literals\":[-7,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":43,\"full_literals\":[-17,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":44,\"full_literals\":[-18,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":61,\"full_literals\":[-32,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":76,\"full_literals\":[-43,48]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[45,50,55,59],\"full_literals\":[-49,19,23,27,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":45,\"full_literals\":[-19,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":50,\"full_literals\":[-23,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":55,\"full_literals\":[-27,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":59,\"full_literals\":[-30,49]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[46,65,70,74],\"full_literals\":[-50,20,35,38,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":46,\"full_literals\":[-20,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":65,\"full_literals\":[-35,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":70,\"full_literals\":[-38,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":74,\"full_literals\":[-41,50]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-51,45,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-46,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-45,false,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-52,44,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-51,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-44,false,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-47,-48,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-54,49,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-54,false,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-49,-50,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-54,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-53,false,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-52,-55,56],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":22,\"owners\":[11,21,25,29,31,33,48,49,50,52,53,54,55,65,69,70]},{\"tag\":\"edge\",\"edge\":29,\"owners\":[20,22,26,37,39,40,50,59,60,63,64,65,72,73,74,75]},{\"tag\":\"edge\",\"edge\":40,\"owners\":[11,21,29,36,43,45,52,54,57,59,61,69,74,76]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[14,22,31,38,43,46,53,55,58,60,61,70,75,76]}]}"
  "118 -44 9 10 0 71 75 77 0\n119 -45 12 13 0 72 76 80 0\n120 -46 6 7 0 69 70 73 74 83 0\n121 1 4 6 8 9 11 23 24 26 27 35 37 38 0 69 70 71 114 0\n122 3 5 7 13 15 16 23 30 31 35 40 41 42 0 73 74 76 115 0\n123 1 4 8 12 17 19 24 26 30 32 37 41 43 0 72 116 0\n124 2 5 9 14 17 20 27 29 31 32 38 42 43 0 71 117 0\n125 -54 52 0 104 102 82 64 81 63 101 85 57 84 55 105 79 61 78 59 107 108 90 95 45 62 40 0\n126 17 43 1 12 8 19 24 26 30 32 37 41 0 123 44 0\n127 -50 52 0 73 74 75 69 70 71 72 125 104 101 85 57 105 79 61 24 102 82 64 81 63 84 55 33 78 26 59 95 109 9 14 22 91 27 28 126 0\n128 -32 52 0 73 74 75 104 102 81 63 101 85 57 84 55 105 79 33 61 78 59 13 46 40 0\n129 -43 52 0 69 70 71 104 102 82 64 101 85 57 84 55 105 79 61 78 26 59 21 47 40 0\n130 52 0 72 70 69 75 76 74 73 104 105 101 102 78 79 84 85 81 82 59 61 55 57 63 29 64 37 35 127 96 128 67 129 38 39 50 36 122 0\n131 -55 0 130 113 112 0\n132 -54 0 131 110 0\n133 -53 0 131 111 0\n134 -19 0 130 3 4 5 6 7 8 120 118 119 103 100 0\n135 -11 -45 0 1 2 119 0\n136 23 27 35 38 0 130 69 71 70 58 60 118 103 41 54 56 43 24 120 100 135 40 23 25 121 0\n137 27 35 38 32 43 0 71 51 58 65 53 31 136 10 30 32 50 124 0\n138 35 38 32 43 0 76 132 134 67 137 11 12 93 34 109 42 99 44 0\n139 38 32 43 0 132 51 138 15 97 109 93 94 50 49 0\n140 32 43 0 132 69 70 72 139 16 17 18 19 20 98 29 109 52 92 94 48 0\n141 -32 0 133 68 88 87 106 0\n142 43 0 141 140 0\n143 17 0 142 66 0\n144 48 0 142 89 0\n145 47 0 143 86 0\n146 0 145 144 133 106 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record030.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record030.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record030.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record030.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record030 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record030.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record030.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record030.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record030.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record030 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record030_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record030_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record030_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record030_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record030_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record030_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record030_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record030 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record030_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record030_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record030_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00001.record030

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00001.record031
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "34cab25cf0b8aaa9aa2eb46a9a561db0ea3a2e2ba1e0fbc1e27496a5592e7451d70da364d534ad17783d0ec370da354cb31cf0ba2d8b4acab46c9b0ef07a1e4751ca719e0f43c8f0bc1fe203ce0b42918560d9892a439154350b41d60d4328c530cc4709c17"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36d26da6936db4d34d34db6924d249369a6d36924db489249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record031 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record031 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record031.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record031.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record031.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 22), (facetIndex 49), (facetIndex 55)]))
 (.leaf ([(facetIndex 29), (facetIndex 30), (facetIndex 70), (facetIndex 72)])))
 (.branch 3
 (.leaf ([(facetIndex 45), (facetIndex 47), (facetIndex 48), (facetIndex 77)]))
 (.leaf ([(facetIndex 27), (facetIndex 41), (facetIndex 43)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 36), (facetIndex 50), (facetIndex 57), (facetIndex 59)]))
 (.leaf ([(facetIndex 38), (facetIndex 61), (facetIndex 76)])))
 (.branch 7
 (.leaf ([(facetIndex 28), (facetIndex 42), (facetIndex 44)]))
 (.branch 8
 (.leaf ([(facetIndex 63), (facetIndex 69)]))
 (.leaf ([(facetIndex 23), (facetIndex 33)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "2500010170000070504040000004022026363005040080011630008z17;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 51), (facetIndex 52), (facetIndex 58), (facetIndex 78)]))
 (.leaf ([(facetIndex 24), (facetIndex 31), (facetIndex 71)])))
 (.branch 3
 (.leaf ([(facetIndex 53), (facetIndex 65), (facetIndex 79)]))
 (.leaf ([(facetIndex 26), (facetIndex 32), (facetIndex 46), (facetIndex 60)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 39), (facetIndex 54), (facetIndex 62)]))
 (.leaf ([(facetIndex 25), (facetIndex 34), (facetIndex 35), (facetIndex 37), (facetIndex 40), (facetIndex 64), (facetIndex 66), (facetIndex 67)])))
 (.branch 7
 (.leaf ([(facetIndex 68), (facetIndex 73), (facetIndex 74), (facetIndex 75)]))
 (.leaf ([(facetIndex 56), (facetIndex 80)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "7400db0206b551030071100000c0005828b432000e9z12;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1, 2, 3]
def grouped2_0002 : List Nat := [4]
def grouped2_0003 : List Nat := [4, 5]
def grouped2_0004 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0005 : List Nat := [5]
def grouped2_0006 : List Nat := [6]
def grouped2_0007 : List Nat := [6, 7, 8]
def grouped2_0008 : List Nat := [7]
def grouped2_0009 : List Nat := [7, 8]
def grouped2_0010 : List Nat := [8]
def grouped3_0011 : List Nat := [0]
def grouped3_0012 : List Nat := [0, 1]
def grouped3_0013 : List Nat := [0, 1, 2, 3]
def grouped3_0015 : List Nat := [1]
def grouped3_0016 : List Nat := [2]
def grouped3_0017 : List Nat := [2, 3]
def grouped3_0018 : List Nat := [3]
def grouped3_0019 : List Nat := [4]
def grouped3_0020 : List Nat := [4, 5]
def grouped3_0021 : List Nat := [4, 5, 6, 7]
def grouped3_0022 : List Nat := [5]
def grouped3_0023 : List Nat := [6]
def grouped3_0024 : List Nat := [6, 7]
def grouped3_0025 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record031 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record031_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00001.record031" "{\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00001.record031" 76

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00001.record031" "{\"ridges\":[[6,321],[17,518],[17,580],[18,832],[21,648],[21,776],[26,523],[26,524],[29,321],[30,580],[31,645],[32,773],[43,321],[45,321],[47,321],[47,832],[52,524],[53,524],[53,645],[54,776],[56,773],[58,344],[60,585],[61,648],[61,776],[62,705],[64,538],[66,554],[67,142],[68,270],[70,518],[70,580],[71,676],[72,518],[72,832],[73,154],[74,298],[75,554],[76,648],[76,776],[77,832],[78,600],[79,524],[79,676],[80,332],[80,524]],\"owners\":[[6,321,[51,56,58,60,62],[29,43,45,47]],[29,321,[58,60,62],[6,43,45,47,51,56]],[43,321,[51,56,60,62],[6,29,45,47,58]],[45,321,[51,56,58,60],[6,29,43,47,62]],[47,321,[51,58],[6,29,43,45,56,60,62]],[17,518,[26,31,32,64,66,67,68,71],[30,70,72]],[70,518,[26,31,32,66,67,68,71],[17,30,64,72]],[72,518,[26,31,64,66,67,71],[17,30,32,68,70]],[17,580,[52,56,78,80],[30,70,72]],[30,580,[78,80],[17,52,56,70,72]],[70,580,[52,56,80],[17,30,72,78]],[18,832,[56,60,62,80],[47,72,77]],[47,832,[80],[18,56,60,62,72,77]],[72,832,[60,62],[18,47,56,77,80]],[77,832,[56,60,80],[18,47,62,72]],[21,648,[39,53,67,75,79],[61,76]],[61,648,[67,75,79],[21,39,53,76]],[76,648,[53,79],[21,39,61,67,75]],[21,776,[40,54,60,68,80],[61,76]],[54,776,[21,76],[40,60,61,68,80]],[61,776,[68,80],[21,40,54,60,76]],[76,776,[54,60,80],[21,40,61,68]],[67,142,[24,65],[]],[68,270,[25],[]],[26,523,[39,40],[]],[26,524,[78,79,80],[52,53,54,64,66,67,68]],[52,524,[64,66,67,68,79],[26,53,54,78,80]],[53,524,[64,66,68,78,80],[26,52,54,67,79]],[79,524,[26,52,54,64,68,78,80],[53,66,67]],[80,524,[26,53,64,66,67,79],[52,54,68,78]],[31,645,[53],[]],[53,645,[31],[]],[32,773,[54,56],[]],[56,773,[32,54],[]],[73,154,[34],[]],[74,298,[37],[]],[62,705,[46],[]],[80,332,[51],[]],[60,585,[52],[]],[58,344,[],[]],[64,538,[],[]],[66,554,[75],[]],[75,554,[66],[]],[71,676,[79],[]],[79,676,[71],[]],[78,600,[],[]]],\"edges\":[[23,[17,26,30,31,32,52,53,54,56,64,66,67,68,70,71,72,78,79,80]],[29,[21,26,39,40,52,53,54,60,61,64,66,67,68,75,76,78,79,80]],[40,[6,18,29,43,45,47,51,56,58,60,62,72,77,80]],[41,[17,18,30,46,47,52,56,60,62,70,72,77,78,80]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00001.record031" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00001.record031\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-26,-21],[-26,-24],[-27,-17],[-29,-26],[-31,-26],[-35,-5],[-35,-13],[-35,-16],[-39,-26],[-1,23,27,28,29,31],[-9,28,29,31],[-19,23,27,29,31],[-20,23,27,28,29],[-22,23,28],[-2,8,11,12,32,34,35,36,38],[-37,8,11,12,34,35,36,38],[-39,8,11,32,34,35,38],[-2,24,27,45,47],[-10,45,47],[-37,24,27,47],[-3,27,29,31,47],[-22,47],[-39,29,31],[-44,27,29,47],[-4,17,25,35,42,46],[-30,35,42,46],[-43,25,46],[-4,18,26,29,36,47],[-26,4,43],[-30,36,47],[-43,26,29,47],[-35,6,33],[-36,7],[-8,17,18],[-8,45,46,47],[-24,32,34,35,36,46],[-25,32,34,36,45,47],[-46,8,24,26,32,36,45,47],[-47,8,25,32,34,35,46],[-11,25],[-25,11],[-12,26,27],[-27,12,26],[-40,14],[-41,15],[-31,21],[-47,23],[-29,24],[-28],[-32],[-34,42],[-42,34],[-38,46],[-46,38],[-45],[-48,16,30,43],[-49,5,13],[-50,48],[-51,49],[-52,51],[-53,50,52],[-54,53],[54],[-23,55],[-24,55],[-6,56],[-11,56],[-38,56],[-25,57],[-33,57],[-46,57],[-8,58],[-12,58],[-21,58],[-29,58],[-17,59],[-26,59],[-7,60],[-14,60],[-15,60],[-18,60],[-34,60],[-35,60],[-61,36,40,41,42],[-36,61],[-42,61],[-62,27,47],[-27,62],[-47,62],[-56,63],[-55,63],[-55,-56,64],[-58,65],[-57,65],[-57,-58,66],[-65,67],[-63,67],[-63,-65,68],[-63,-66,69],[-64,68],[-64,-65,69],[-60,70],[-59,70],[-62,71],[-61,71],[-72,62],[-61,-62,72],[-71,73],[-70,-71,74],[-70,-72,75],[-75,76],[-67,-74,76],[-68,-73,76],[-69,76],[-76],[2,8,10,11,12,24,25,26,27,32,34,35,36,37,38,39,45,46,47],[4,8,17,18,24,25,26,29,30,32,34,35,36,42,43,45,46,47],[1,3,9,19,20,22,23,27,28,29,31,39,44,47],[2,3,10,21,22,24,27,29,31,37,39,44,45,47]],\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":54,\"b\":46},{\"tag\":\"incompatible\",\"a\":54,\"b\":52},{\"tag\":\"incompatible\",\"a\":56,\"b\":39},{\"tag\":\"incompatible\",\"a\":60,\"b\":54},{\"tag\":\"incompatible\",\"a\":62,\"b\":54},{\"tag\":\"incompatible\",\"a\":67,\"b\":23},{\"tag\":\"incompatible\",\"a\":67,\"b\":33},{\"tag\":\"incompatible\",\"a\":67,\"b\":38},{\"tag\":\"incompatible\",\"a\":72,\"b\":54},{\"tag\":\"mate\",\"ridge\":321,\"a\":6,\"owners\":[51,56,58,60,62]},{\"tag\":\"mate\",\"ridge\":321,\"a\":29,\"owners\":[58,60,62]},{\"tag\":\"mate\",\"ridge\":321,\"a\":43,\"owners\":[51,56,60,62]},{\"tag\":\"mate\",\"ridge\":321,\"a\":45,\"owners\":[51,56,58,60]},{\"tag\":\"mate\",\"ridge\":321,\"a\":47,\"owners\":[51,58]},{\"tag\":\"mate\",\"ridge\":518,\"a\":17,\"owners\":[26,31,32,64,66,67,68,71]},{\"tag\":\"mate\",\"ridge\":518,\"a\":70,\"owners\":[26,31,32,66,67,68,71]},{\"tag\":\"mate\",\"ridge\":518,\"a\":72,\"owners\":[26,31,64,66,67,71]},{\"tag\":\"mate\",\"ridge\":580,\"a\":17,\"owners\":[52,56,78,80]},{\"tag\":\"mate\",\"ridge\":580,\"a\":30,\"owners\":[78,80]},{\"tag\":\"mate\",\"ridge\":580,\"a\":70,\"owners\":[52,56,80]},{\"tag\":\"mate\",\"ridge\":832,\"a\":18,\"owners\":[56,60,62,80]},{\"tag\":\"mate\",\"ridge\":832,\"a\":47,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":832,\"a\":72,\"owners\":[60,62]},{\"tag\":\"mate\",\"ridge\":832,\"a\":77,\"owners\":[56,60,80]},{\"tag\":\"mate\",\"ridge\":648,\"a\":21,\"owners\":[39,53,67,75,79]},{\"tag\":\"mate\",\"ridge\":648,\"a\":61,\"owners\":[67,75,79]},{\"tag\":\"mate\",\"ridge\":648,\"a\":76,\"owners\":[53,79]},{\"tag\":\"mate\",\"ridge\":776,\"a\":21,\"owners\":[40,54,60,68,80]},{\"tag\":\"mate\",\"ridge\":776,\"a\":54,\"owners\":[21,76]},{\"tag\":\"mate\",\"ridge\":776,\"a\":61,\"owners\":[68,80]},{\"tag\":\"mate\",\"ridge\":776,\"a\":76,\"owners\":[54,60,80]},{\"tag\":\"mate\",\"ridge\":142,\"a\":67,\"owners\":[24,65]},{\"tag\":\"mate\",\"ridge\":270,\"a\":68,\"owners\":[25]},{\"tag\":\"mate\",\"ridge\":523,\"a\":26,\"owners\":[39,40]},{\"tag\":\"mate\",\"ridge\":524,\"a\":26,\"owners\":[78,79,80]},{\"tag\":\"mate\",\"ridge\":524,\"a\":52,\"owners\":[64,66,67,68,79]},{\"tag\":\"mate\",\"ridge\":524,\"a\":53,\"owners\":[64,66,68,78,80]},{\"tag\":\"mate\",\"ridge\":524,\"a\":79,\"owners\":[26,52,54,64,68,78,80]},{\"tag\":\"mate\",\"ridge\":524,\"a\":80,\"owners\":[26,53,64,66,67,79]},{\"tag\":\"mate\",\"ridge\":645,\"a\":31,\"owners\":[53]},{\"tag\":\"mate\",\"ridge\":645,\"a\":53,\"owners\":[31]},{\"tag\":\"mate\",\"ridge\":773,\"a\":32,\"owners\":[54,56]},{\"tag\":\"mate\",\"ridge\":773,\"a\":56,\"owners\":[32,54]},{\"tag\":\"mate\",\"ridge\":154,\"a\":73,\"owners\":[34]},{\"tag\":\"mate\",\"ridge\":298,\"a\":74,\"owners\":[37]},{\"tag\":\"mate\",\"ridge\":705,\"a\":62,\"owners\":[46]},{\"tag\":\"mate\",\"ridge\":332,\"a\":80,\"owners\":[51]},{\"tag\":\"mate\",\"ridge\":585,\"a\":60,\"owners\":[52]},{\"tag\":\"mate\",\"ridge\":344,\"a\":58,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":538,\"a\":64,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":554,\"a\":66,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":554,\"a\":75,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":676,\"a\":71,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":676,\"a\":79,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":600,\"a\":78,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[38,61,76],\"full_literals\":[-48,16,30,43]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[23,33],\"full_literals\":[-49,5,13]},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-50,false,48],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-51,false,49],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-52,false,51],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-53,50,52],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-54,false,53],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":51,\"full_literals\":[-23,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":52,\"full_literals\":[-24,55]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":24,\"full_literals\":[-6,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":31,\"full_literals\":[-11,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":71,\"full_literals\":[-38,56]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":53,\"full_literals\":[-25,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":65,\"full_literals\":[-33,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":79,\"full_literals\":[-46,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":26,\"full_literals\":[-8,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":32,\"full_literals\":[-12,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":46,\"full_literals\":[-21,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":60,\"full_literals\":[-29,58]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":39,\"full_literals\":[-17,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":54,\"full_literals\":[-26,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":25,\"full_literals\":[-7,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":34,\"full_literals\":[-14,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":37,\"full_literals\":[-15,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":40,\"full_literals\":[-18,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":66,\"full_literals\":[-34,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":67,\"full_literals\":[-35,60]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[68,73,74,75],\"full_literals\":[-61,36,40,41,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":68,\"full_literals\":[-36,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":75,\"full_literals\":[-42,61]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[56,80],\"full_literals\":[-62,27,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":56,\"full_literals\":[-27,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":80,\"full_literals\":[-47,62]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-56,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-55,false,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-55,-56,64],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-58,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-57,false,65],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-57,-58,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-65,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-63,false,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-63,-65,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-63,-66,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-64,false,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-64,-65,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-60,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-59,false,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-62,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-61,false,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-72,false,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-61,-62,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-71,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-70,-71,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-70,-72,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-75,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-67,-74,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-68,-73,76],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-69,false,76],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":23,\"owners\":[17,26,30,31,32,52,53,54,56,64,66,67,68,70,71,72,78,79,80]},{\"tag\":\"edge\",\"edge\":29,\"owners\":[21,26,39,40,52,53,54,60,61,64,66,67,68,75,76,78,79,80]},{\"tag\":\"edge\",\"edge\":40,\"owners\":[6,18,29,43,45,47,51,56,58,60,62,72,77,80]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[17,18,30,46,47,52,56,60,62,70,72,77,78,80]}]}"
  "120 53 0 63 62 0\n121 -75 0 115 111 0\n122 -69 0 115 114 0\n123 2 8 10 11 12 24 25 26 27 34 35 36 37 38 39 46 47 0 50 55 116 0\n124 4 8 17 18 24 25 26 29 30 34 35 36 42 43 46 47 0 50 55 117 0\n125 1 3 9 19 20 22 23 27 29 31 39 44 47 0 49 118 0\n126 2 3 10 21 22 24 27 29 31 37 39 44 47 0 55 119 0\n127 -72 67 0 121 97 91 64 47 96 93 73 106 110 87 103 43 77 0\n128 -62 67 0 127 97 91 64 47 96 94 69 71 27 90 66 70 32 93 73 87 107 3 43 86 25 29 0\n129 67 0 49 96 97 93 91 74 75 64 46 23 11 14 47 128 88 21 24 12 10 13 125 0\n130 -74 0 129 115 112 0\n131 35 46 61 26 62 0 55 50 89 35 53 85 86 51 37 40 88 42 19 36 16 15 17 123 0\n132 46 61 26 62 0 50 55 120 89 85 86 51 37 30 27 131 6 7 8 57 56 59 58 60 61 0\n133 61 26 62 0 122 55 50 89 85 132 54 71 68 94 90 101 99 92 95 65 72 38 0\n134 -61 0 130 105 109 102 78 79 80 82 33 44 45 52 84 0\n135 -36 0 134 85 0\n136 -42 0 134 86 0\n137 -34 0 136 51 0\n138 62 0 134 55 88 89 22 19 133 1 2 4 5 9 18 20 21 24 126 0\n139 71 0 138 104 0\n140 73 0 139 108 0\n141 -70 0 139 130 109 0\n142 -68 0 140 115 113 0\n143 -60 0 141 102 0\n144 -59 0 141 103 0\n145 -64 0 142 100 0\n146 -18 0 143 81 0\n147 -35 0 143 83 0\n148 -17 0 144 76 0\n149 -26 0 144 77 0\n150 -8 0 148 146 34 0\n151 -46 0 142 54 71 68 94 90 98 0\n152 -24 0 151 50 137 135 147 36 0\n153 -30 0 151 136 147 26 0\n154 -29 0 152 48 0\n155 47 0 55 50 151 136 135 137 153 152 154 149 146 148 147 150 37 31 28 124 0\n156 23 0 155 47 0\n157 25 0 155 151 50 150 137 147 39 0\n158 55 0 156 64 0\n159 11 0 157 41 0\n160 -56 0 158 145 92 0\n161 0 159 160 67 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record031.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record031.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record031.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record031.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record031 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record031.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record031.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record031.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record031.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record031 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record031_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record031_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record031_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record031_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record031_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record031_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record031_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record031 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record031_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record031_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00001.record031_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00001.record031
