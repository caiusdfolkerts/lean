module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow16Part00015Data
public import GraphInputsRow16Part00015Frames
public import GraphInputsRow16Part00015Leaves
public import GraphInputsRow16Part00015Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00015.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record000
def vertexColumn : Fields := ⟨10, hexnat% "332aaa6a3ab1a8e8ba1e8e62d876c38ce4789e17b31aa6693a7198e4b91e4e52d475c34cd4749d17723a8e6338f138cd332cc73c2e8b92ccb8acab1ae1b46c9b16c3bc1d8751cc729c6725c570de0f43d162384e079152344d0770388ca318d130ce0b22c4b06d0721c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6db6db6924db6db6db692492492492492492492492492449249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [16571693216563200, 19421781982969856, 540431955284459520, hexnat% "7800000000000000000", 35321811042304]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "280078141afff800000", hexnat% "5000000000000000000", 19740906642997248, 30855045054464, 15903336184152064]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000787fdfe0f800000", hexnat% "5800000000000000000", 8321499136, 33779196228534272]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "300078181b7ff800000", hexnat% "4800000000000000000", 19740906642997248, 30820685316096, 15832967439974400]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200020021a00c800000", 396316767225380864, hexnat% "5800000000000000000", 16106127360, 19984998224363520, 33105607917568, 15973705767190528]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c6 c0
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c7 c1
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c8 c0
  c9
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00015.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00015.record046
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "eaa6966c58b6c38ae1ba1e2785e3a699597152d70d2b46d8749d1772368d6338f13a4cb3c2e8b92ccb2ac6b16f0751ca785d1725c570de0f43c8f0be1a269261984e07a19265251944d0770348ca318e1324e0b22c4b06d0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "d26db4926936da492492492492492492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record046 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record046 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record046.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record046.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record046.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 58), (facetIndex 60)]))
 (.branch 2
 (.leaf ([(facetIndex 57), (facetIndex 59)]))
 (.leaf ([(facetIndex 63), (facetIndex 68)]))))
 (.branch 4
 (.leaf ([(facetIndex 69), (facetIndex 71)]))
 (.branch 5
 (.leaf ([(facetIndex 70)]))
 (.leaf ([(facetIndex 74)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "14071a000400208z2a;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 6
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1, 2]
def grouped3_0003 : List Nat := [1]
def grouped3_0004 : List Nat := [1, 2]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [3]
def grouped3_0007 : List Nat := [3, 4, 5]
def grouped3_0008 : List Nat := [4]
def grouped3_0009 : List Nat := [4, 5]
def grouped3_0010 : List Nat := [5]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record046 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record046_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00015.record046" "{\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00015.record046" 34

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00015.record046" "{\"ridges\":[[12,162],[14,769],[14,770],[36,162],[38,769],[41,162],[45,769],[45,770],[46,162],[48,769],[48,770],[49,162],[51,162],[52,769],[52,770],[58,780],[59,180],[60,788],[63,232],[69,780],[71,788]],\"owners\":[[12,162,[68,70,74],[36,41,46,49,51]],[36,162,[74],[12,41,46,49,51,68,70]],[41,162,[70],[12,36,46,49,51,68,74]],[46,162,[68,74],[12,36,41,49,51,70]],[49,162,[68,70],[12,36,41,46,51,74]],[51,162,[68,70,74],[12,36,41,46,49]],[14,769,[58,60],[38,45,48,52]],[38,769,[],[14,45,48,52,58,60]],[45,769,[60],[14,38,48,52,58]],[48,769,[58],[14,38,45,52,60]],[52,769,[58,60],[14,38,45,48]],[14,770,[69,71],[38,45,48,52]],[45,770,[71],[14,38,48,52,69]],[48,770,[69],[14,38,45,52,71]],[52,770,[69,71],[14,38,45,48]],[58,780,[69],[]],[69,780,[58],[]],[59,180,[70],[]],[60,788,[71],[]],[71,788,[60],[]],[63,232,[74],[]]],\"edges\":[[36,[12,36,41,46,49,51,57,59,63,68,70,74]],[44,[14,38,45,48,52,58,60,69,71]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00015.record046" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00015.record046\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,17,19,21],[-3,21],[-5,19],[-7,17,21],[-9,17,19],[-10,17,19,21],[-2,13,15],[-4],[-6,15],[-8,13],[-11,13,15],[-2,18,20],[-6,20],[-8,18],[-11,18,20],[-13,18],[-18,13],[-14,19],[-15,20],[-20,15],[-16,21],[-13,22],[-15,22],[-12,23],[-17,24],[-18,25],[-20,25],[-19,26],[-21,27],[-24,28],[-23,28],[-22,29],[-22,-28,30],[-27,31],[-26,31],[-25,32],[-25,-31,33],[-29,-33,34],[-30,-32,34],[-34],[1,3,5,7,9,10,12,14,16,17,19,21],[2,4,6,8,11,13,15,18,20]],\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":162,\"a\":12,\"owners\":[68,70,74]},{\"tag\":\"mate\",\"ridge\":162,\"a\":36,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":162,\"a\":41,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":162,\"a\":46,\"owners\":[68,74]},{\"tag\":\"mate\",\"ridge\":162,\"a\":49,\"owners\":[68,70]},{\"tag\":\"mate\",\"ridge\":162,\"a\":51,\"owners\":[68,70,74]},{\"tag\":\"mate\",\"ridge\":769,\"a\":14,\"owners\":[58,60]},{\"tag\":\"mate\",\"ridge\":769,\"a\":38,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":769,\"a\":45,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":769,\"a\":48,\"owners\":[58]},{\"tag\":\"mate\",\"ridge\":769,\"a\":52,\"owners\":[58,60]},{\"tag\":\"mate\",\"ridge\":770,\"a\":14,\"owners\":[69,71]},{\"tag\":\"mate\",\"ridge\":770,\"a\":45,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":770,\"a\":48,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":770,\"a\":52,\"owners\":[69,71]},{\"tag\":\"mate\",\"ridge\":780,\"a\":58,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":780,\"a\":69,\"owners\":[58]},{\"tag\":\"mate\",\"ridge\":180,\"a\":59,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":788,\"a\":60,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":788,\"a\":71,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":232,\"a\":63,\"owners\":[74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":58,\"full_literals\":[-13,22]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":60,\"full_literals\":[-15,22]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":57,\"full_literals\":[-12,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":68,\"full_literals\":[-17,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":69,\"full_literals\":[-18,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":71,\"full_literals\":[-20,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":70,\"full_literals\":[-19,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":74,\"full_literals\":[-21,27]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-24,28],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-23,false,28],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-22,false,29],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-22,-28,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-27,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-26,false,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-25,false,32],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-25,-31,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-29,-33,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-30,-32,34],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":36,\"owners\":[12,36,41,46,49,51,57,59,63,68,70,74]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[14,38,45,48,52,58,60,69,71]}]}"
  "p cnf 34 42\n-1 17 19 21 0\n-3 21 0\n-5 19 0\n-7 17 21 0\n-9 17 19 0\n-10 17 19 21 0\n-2 13 15 0\n-4 0\n-6 15 0\n-8 13 0\n-11 13 15 0\n-2 18 20 0\n-6 20 0\n-8 18 0\n-11 18 20 0\n-13 18 0\n-18 13 0\n-14 19 0\n-15 20 0\n-20 15 0\n-16 21 0\n-13 22 0\n-15 22 0\n-12 23 0\n-17 24 0\n-18 25 0\n-20 25 0\n-19 26 0\n-21 27 0\n-24 28 0\n-23 28 0\n-22 29 0\n-22 -28 30 0\n-27 31 0\n-26 31 0\n-25 32 0\n-25 -31 33 0\n-29 -33 34 0\n-30 -32 34 0\n-34 0\n1 3 5 7 9 10 12 14 16 17 19 21 0\n2 4 6 8 11 13 15 18 20 0\n"
  "43 2 6 8 11 13 15 18 20 0 8 42 0\n44 13 15 0 7 10 17 9 20 11 43 0\n45 22 0 22 23 44 0\n46 29 0 45 32 0\n47 -33 0 46 40 38 0\n48 -25 0 47 40 45 36 37 39 34 35 33 29 28 30 31 2 21 3 18 25 24 4 1 5 6 41 0\n49 -18 0 48 26 0\n50 -20 0 48 27 0\n51 -2 0 49 50 12 0\n52 -8 0 49 14 0\n53 -11 0 49 50 15 0\n54 -13 0 49 16 0\n55 -6 0 50 13 0\n56 -15 0 50 19 0\n57 0 52 51 55 53 54 56 49 50 43 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record046.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record046.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record046.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record046.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record046 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record046.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record046.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record046.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record046.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record046 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record046_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record046_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record046_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record046_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record046_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record046_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record046_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record046 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record046_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record046_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00015.record046_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00015.record046
