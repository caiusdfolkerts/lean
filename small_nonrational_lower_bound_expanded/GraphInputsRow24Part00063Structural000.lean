module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00063Data
public import GraphInputsRow24Part00063Frames
public import GraphInputsRow24Part00063Leaves
public import GraphInputsRow24Part00063Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00063.record020
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record020
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨64, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨75, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨83, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), 41658296553177088, 457946592968704, 7696581394432, 144185556820033536, (certNat% 3)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 4), 422349904019456, (certNat% 5), (certNat% 6), (certNat% 7), 37383395344384]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 8), 422352051503104, (certNat% 9), (certNat% 10), (certNat% 11), (certNat% 7)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), 45035996810575872, 10995116277760, 70403103916032, 17179869184]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), 70403640786944, 457946592968704, 63050394783186944, (certNat% 6), 19791209299968]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), 175939040313344, (certNat% 15), (certNat% 16), 29137058136064]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), 63050394783186944, 28587302322176, 145315854773387264, (certNat% 15), (certNat% 18)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), 457948740452352, 63050395320057856, (certNat% 20), (certNat% 21), (certNat% 6), 19791209299968]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c11 c2
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c12 c1
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c13 c0
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record020_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record020_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record020_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record020_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record020_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record020_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record020_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record020_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record020_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00063.record020

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00063.record003
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "29c5a95a4eac6599564d8b6a3a4e1b89e17969a65594e6c559695555352d68d8b46d8749d176c358d9354cb3a2e4b52d2b1ad1b26c5ba1e4751cc749ca719d1715e0f23e4c0f1320e8960d84e0b81e4c6490e685914950d60d1342d0754348d1324c3312c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db4db49a4936d269a492493492692492492492491249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record003 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record003 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record003.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record003.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record003.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 51), (facetIndex 56)]))
 (.leaf ([(facetIndex 71), (facetIndex 77)])))
 (.branch 3
 (.leaf ([(facetIndex 82)]))
 (.leaf ([(facetIndex 86)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 65), (facetIndex 67)]))
 (.leaf ([(facetIndex 70), (facetIndex 72)])))
 (.branch 7
 (.leaf ([(facetIndex 80), (facetIndex 81)]))
 (.leaf ([(facetIndex 84), (facetIndex 85)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "ff0b600800534082z31;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record003 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record003_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00063.record003" "{\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00063.record003" 39

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00063.record003" "{\"ridges\":[[12,321],[12,322],[20,644],[41,321],[41,322],[43,644],[49,321],[49,322],[53,321],[53,322],[55,321],[55,322],[62,644],[65,340],[66,644],[67,356],[68,644],[70,344],[72,360],[80,340],[81,356],[84,344],[85,360]],\"owners\":[[12,321,[65,67,70,72],[41,49,53,55]],[41,321,[70,72],[12,49,53,55,65,67]],[49,321,[65,67],[12,41,53,55,70,72]],[53,321,[67,72],[12,41,49,55,65,70]],[55,321,[65,70],[12,41,49,53,67,72]],[12,322,[80,81,84,85],[41,49,53,55]],[41,322,[84,85],[12,49,53,55,80,81]],[49,322,[80,81],[12,41,53,55,84,85]],[53,322,[81,85],[12,41,49,55,80,84]],[55,322,[80,84],[12,41,49,53,81,85]],[20,644,[77,82,86],[43,62,66,68]],[43,644,[86],[20,62,66,68,77,82]],[62,644,[82],[20,43,66,68,77,86]],[66,644,[77,82],[20,43,62,68,86]],[68,644,[77,86],[20,43,62,66,82]],[65,340,[80],[]],[80,340,[65],[]],[67,356,[81],[]],[81,356,[67],[]],[70,344,[84],[]],[84,344,[70],[]],[72,360,[85],[]],[85,360,[72],[]]],\"edges\":[[40,[12,41,49,53,55,65,67,70,72,80,81,84,85]],[43,[20,43,51,56,62,66,68,71,77,82,86]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00063.record003" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00063.record003\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,11,13,15,17],[-3,15,17],[-5,11,13],[-7,13,17],[-8,11,15],[-1,19,20,22,23],[-3,22,23],[-5,19,20],[-7,20,23],[-8,19,22],[-2,18,21,24],[-4,24],[-10,21],[-12,18,21],[-14,18,24],[-11,19],[-19,11],[-13,20],[-20,13],[-15,22],[-22,15],[-17,23],[-23,17],[-6,25],[-9,25],[-16,26],[-18,26],[-21,27],[-24,28],[-11,29],[-13,29],[-15,30],[-17,30],[-19,31],[-20,31],[-22,32],[-23,32],[-26,33],[-25,33],[-28,34],[-27,34],[-34,35],[-33,35],[-30,36],[-29,36],[-32,37],[-31,37],[-36,-37,38],[-35,-38,39],[-39],[1,3,5,7,8,11,13,15,17,19,20,22,23],[2,4,6,9,10,12,14,16,18,21,24]],\"atoms\":[{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":321,\"a\":12,\"owners\":[65,67,70,72]},{\"tag\":\"mate\",\"ridge\":321,\"a\":41,\"owners\":[70,72]},{\"tag\":\"mate\",\"ridge\":321,\"a\":49,\"owners\":[65,67]},{\"tag\":\"mate\",\"ridge\":321,\"a\":53,\"owners\":[67,72]},{\"tag\":\"mate\",\"ridge\":321,\"a\":55,\"owners\":[65,70]},{\"tag\":\"mate\",\"ridge\":322,\"a\":12,\"owners\":[80,81,84,85]},{\"tag\":\"mate\",\"ridge\":322,\"a\":41,\"owners\":[84,85]},{\"tag\":\"mate\",\"ridge\":322,\"a\":49,\"owners\":[80,81]},{\"tag\":\"mate\",\"ridge\":322,\"a\":53,\"owners\":[81,85]},{\"tag\":\"mate\",\"ridge\":322,\"a\":55,\"owners\":[80,84]},{\"tag\":\"mate\",\"ridge\":644,\"a\":20,\"owners\":[77,82,86]},{\"tag\":\"mate\",\"ridge\":644,\"a\":43,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":644,\"a\":62,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":644,\"a\":66,\"owners\":[77,82]},{\"tag\":\"mate\",\"ridge\":644,\"a\":68,\"owners\":[77,86]},{\"tag\":\"mate\",\"ridge\":340,\"a\":65,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":340,\"a\":80,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":356,\"a\":67,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":356,\"a\":81,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":344,\"a\":70,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":344,\"a\":84,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":360,\"a\":72,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":360,\"a\":85,\"owners\":[72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":51,\"full_literals\":[-6,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":56,\"full_literals\":[-9,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":71,\"full_literals\":[-16,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":77,\"full_literals\":[-18,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":82,\"full_literals\":[-21,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":86,\"full_literals\":[-24,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":65,\"full_literals\":[-11,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":67,\"full_literals\":[-13,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":70,\"full_literals\":[-15,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":72,\"full_literals\":[-17,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":80,\"full_literals\":[-19,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":81,\"full_literals\":[-20,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":84,\"full_literals\":[-22,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":85,\"full_literals\":[-23,32]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-26,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-25,false,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-28,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-27,false,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-34,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-33,false,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-30,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-29,false,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-32,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-31,false,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-36,-37,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-35,-38,39],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":40,\"owners\":[12,41,49,53,55,65,67,70,72,80,81,84,85]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[20,43,51,56,62,66,68,71,77,82,86]}]}"
  "53 35 0 42 43 40 41 38 39 29 28 26 27 24 25 12 15 13 11 14 52 0\n54 -38 0 53 50 49 0\n55 36 0 44 45 32 33 30 31 2 21 23 1 3 5 17 4 19 51 0\n56 -37 0 55 54 48 0\n57 -32 0 56 46 0\n58 -31 0 56 47 0\n59 -22 0 57 36 0\n60 -23 0 57 37 0\n61 -19 0 58 34 0\n62 -20 0 58 35 0\n63 -3 0 59 60 7 0\n64 -15 0 59 20 0\n65 -17 0 60 22 0\n66 -1 0 61 62 59 60 6 0\n67 -5 0 61 62 8 0\n68 -8 0 61 59 10 0\n69 -11 0 61 16 0\n70 -7 0 62 60 9 0\n71 -13 0 62 18 0\n72 0 71 68 66 70 67 69 63 64 65 61 62 59 60 51 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record003.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record003.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record003.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record003.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record003 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record003.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record003.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record003.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record003.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record003 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record003_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record003 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record003_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record003_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00063.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00063.record004
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "5aa9a5693ab1966559362da8e9386e2785e5a69956539b1565555352d68d9346d2745dd0ec358e9364d532ce8b52e2b4ac6b86d1b26c5ba1e4751cc749ca719d1715e0f23c3c4ca4a0e8960d84e0b81e4c6490e4950d44d0b41da0e4350d2344c930ce0b12c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6da6da4d249b69b693492492492492492492492491249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record004 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record004 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record004.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record004.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record004.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 64), (facetIndex 69)]))
 (.leaf ([(facetIndex 72), (facetIndex 78)])))
 (.branch 3
 (.leaf ([(facetIndex 83)]))
 (.leaf ([(facetIndex 86)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 67), (facetIndex 68)]))
 (.leaf ([(facetIndex 71), (facetIndex 73)])))
 (.branch 7
 (.leaf ([(facetIndex 81), (facetIndex 82)]))
 (.leaf ([(facetIndex 85), (facetIndex 87)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "ef85b0040029a048z32;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record004 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record004_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00063.record004" "{\"atoms\":[{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00063.record004" 40

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00063.record004" "{\"ridges\":[[13,321],[13,322],[15,642],[41,321],[41,322],[43,642],[51,321],[51,322],[52,642],[54,321],[54,322],[56,642],[57,321],[57,322],[58,642],[59,321],[59,322],[67,340],[68,356],[71,344],[73,360],[81,340],[82,356],[85,344],[87,360]],\"owners\":[[13,321,[67,68,71,73],[41,51,54,57,59]],[41,321,[71,73],[13,51,54,57,59,67,68]],[51,321,[67,68],[13,41,54,57,59,71,73]],[54,321,[68,73],[13,41,51,57,59,67,71]],[57,321,[67,71],[13,41,51,54,59,68,73]],[59,321,[67,68,71,73],[13,41,51,54,57]],[13,322,[81,82,85,87],[41,51,54,57,59]],[41,322,[85,87],[13,51,54,57,59,81,82]],[51,322,[81,82],[13,41,54,57,59,85,87]],[54,322,[82,87],[13,41,51,57,59,81,85]],[57,322,[81,85],[13,41,51,54,59,82,87]],[59,322,[81,82,85,87],[13,41,51,54,57]],[15,642,[78,83,86],[43,52,56,58]],[43,642,[86],[15,52,56,58,78,83]],[52,642,[83],[15,43,56,58,78,86]],[56,642,[78,83],[15,43,52,58,86]],[58,642,[78,86],[15,43,52,56,83]],[67,340,[81],[]],[81,340,[67],[]],[68,356,[82],[]],[82,356,[68],[]],[71,344,[85],[]],[85,344,[71],[]],[73,360,[87],[]],[87,360,[73],[]]],\"edges\":[[40,[13,41,51,54,57,59,67,68,71,73,81,82,85,87]],[43,[15,43,52,56,58,64,69,72,78,83,86]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00063.record004" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00063.record004\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,13,14,16,18],[-3,16,18],[-5,13,14],[-7,14,18],[-9,13,16],[-11,13,14,16,18],[-1,20,21,23,25],[-3,23,25],[-5,20,21],[-7,21,25],[-9,20,23],[-11,20,21,23,25],[-2,19,22,24],[-4,24],[-6,22],[-8,19,22],[-10,19,24],[-13,20],[-20,13],[-14,21],[-21,14],[-16,23],[-23,16],[-18,25],[-25,18],[-12,26],[-15,26],[-17,27],[-19,27],[-22,28],[-24,29],[-13,30],[-14,30],[-16,31],[-18,31],[-20,32],[-21,32],[-23,33],[-25,33],[-27,34],[-26,34],[-29,35],[-28,35],[-35,36],[-34,36],[-31,37],[-30,37],[-33,38],[-32,38],[-37,-38,39],[-36,-39,40],[-40],[1,3,5,7,9,11,13,14,16,18,20,21,23,25],[2,4,6,8,10,12,15,17,19,22,24]],\"atoms\":[{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":321,\"a\":13,\"owners\":[67,68,71,73]},{\"tag\":\"mate\",\"ridge\":321,\"a\":41,\"owners\":[71,73]},{\"tag\":\"mate\",\"ridge\":321,\"a\":51,\"owners\":[67,68]},{\"tag\":\"mate\",\"ridge\":321,\"a\":54,\"owners\":[68,73]},{\"tag\":\"mate\",\"ridge\":321,\"a\":57,\"owners\":[67,71]},{\"tag\":\"mate\",\"ridge\":321,\"a\":59,\"owners\":[67,68,71,73]},{\"tag\":\"mate\",\"ridge\":322,\"a\":13,\"owners\":[81,82,85,87]},{\"tag\":\"mate\",\"ridge\":322,\"a\":41,\"owners\":[85,87]},{\"tag\":\"mate\",\"ridge\":322,\"a\":51,\"owners\":[81,82]},{\"tag\":\"mate\",\"ridge\":322,\"a\":54,\"owners\":[82,87]},{\"tag\":\"mate\",\"ridge\":322,\"a\":57,\"owners\":[81,85]},{\"tag\":\"mate\",\"ridge\":322,\"a\":59,\"owners\":[81,82,85,87]},{\"tag\":\"mate\",\"ridge\":642,\"a\":15,\"owners\":[78,83,86]},{\"tag\":\"mate\",\"ridge\":642,\"a\":43,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":642,\"a\":52,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":642,\"a\":56,\"owners\":[78,83]},{\"tag\":\"mate\",\"ridge\":642,\"a\":58,\"owners\":[78,86]},{\"tag\":\"mate\",\"ridge\":340,\"a\":67,\"owners\":[81]},{\"tag\":\"mate\",\"ridge\":340,\"a\":81,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":356,\"a\":68,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":356,\"a\":82,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":344,\"a\":71,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":344,\"a\":85,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":360,\"a\":73,\"owners\":[87]},{\"tag\":\"mate\",\"ridge\":360,\"a\":87,\"owners\":[73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":64,\"full_literals\":[-12,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":69,\"full_literals\":[-15,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":72,\"full_literals\":[-17,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":78,\"full_literals\":[-19,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":83,\"full_literals\":[-22,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":86,\"full_literals\":[-24,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":67,\"full_literals\":[-13,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":68,\"full_literals\":[-14,30]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":71,\"full_literals\":[-16,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":73,\"full_literals\":[-18,31]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":81,\"full_literals\":[-20,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":82,\"full_literals\":[-21,32]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":85,\"full_literals\":[-23,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":87,\"full_literals\":[-25,33]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-27,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-26,false,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-29,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-28,false,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-35,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-34,false,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-31,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-30,false,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-33,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-32,false,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-37,-38,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-36,-39,40],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":40,\"owners\":[13,41,51,54,57,59,67,68,71,73,81,82,85,87]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[15,43,52,56,58,64,69,72,78,83,86]}]}"
  "55 36 0 44 45 42 43 40 41 31 30 28 29 26 27 14 15 16 13 17 54 0\n56 -39 0 55 52 51 0\n57 37 0 46 47 34 35 32 33 2 23 5 25 1 19 4 21 3 6 53 0\n58 -38 0 57 56 50 0\n59 -33 0 58 48 0\n60 -32 0 58 49 0\n61 -23 0 59 38 0\n62 -25 0 59 39 0\n63 -20 0 60 36 0\n64 -21 0 60 37 0\n65 -3 0 61 62 8 0\n66 -16 0 61 22 0\n67 -9 0 61 63 11 0\n68 -18 0 62 24 0\n69 -1 0 63 64 61 62 7 0\n70 -13 0 63 18 0\n71 -7 0 64 62 10 0\n72 -14 0 64 20 0\n73 -5 0 64 63 9 0\n74 -11 0 64 63 61 62 12 0\n75 0 74 72 65 71 67 69 70 73 66 68 63 64 61 62 53 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record004.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record004.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record004.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record004.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record004 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record004.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record004.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record004.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record004.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record004 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record004_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record004 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record004_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record004_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00063.record004

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00063.record013
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "d329c2f0ba598b61da8e9394e2b91e2783eb8749a64b9d16a599565a54b51d70da364d534ad8751d2743db0d6338c73a2d8b92d4b2ad1b0ee8791d2729d1725c5783c8f13c2f2c89a518660d90e078b1a249991545194358350d0754328c6324c3342c8b06d0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6924da6926d24d269249349269249a493492492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record013 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record013 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record013.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record013.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record013.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 45), (facetIndex 70)]))
 (.branch 2
 (.leaf ([(facetIndex 51), (facetIndex 71)]))
 (.leaf ([(facetIndex 77), (facetIndex 85)]))))
 (.branch 4
 (.leaf ([(facetIndex 40), (facetIndex 56), (facetIndex 63), (facetIndex 66)]))
 (.branch 5
 (.leaf ([(facetIndex 75), (facetIndex 78), (facetIndex 84)]))
 (.leaf ([(facetIndex 83)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "14a001108002000c0600003000200000003z1e;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record013 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record013_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00063.record013" "{\"atoms\":[{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00063.record013" 33

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00063.record013" "{\"ridges\":[[19,577],[21,641],[39,577],[40,646],[47,641],[51,706],[56,172],[58,580],[59,648],[63,660],[65,577],[66,676],[67,577],[69,641],[71,736],[78,646],[84,660]],\"owners\":[[19,577,[45,51,70,71],[39,58,65,67]],[39,577,[70,71],[19,45,51,58,65,67]],[65,577,[45,51,70],[19,39,58,67,71]],[67,577,[45,51,71],[19,39,58,65,70]],[58,580,[],[19,39,65,67,77,85]],[21,641,[40,51,63,66,71],[47,59,69]],[47,641,[63,66,71],[21,40,51,59,69]],[69,641,[40,51,66,71],[21,47,59,63]],[59,648,[],[21,47,69,78,84]],[40,646,[78],[]],[78,646,[40],[]],[51,706,[],[]],[56,172,[75,83],[]],[63,660,[84],[]],[84,660,[63],[]],[66,676,[],[]],[71,736,[],[]]],\"edges\":[[41,[19,39,45,51,58,65,67,70,71,77,85]],[43,[21,40,47,51,59,63,66,69,71,78,84]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00063.record013" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00063.record013\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,5,7,16,17],[-3,16,17],[-12,5,7,16],[-14,5,7,17],[-9],[-2,4,7,11,13,17],[-6,11,13,17],[-15,4,7,13,17],[-10],[-4,20],[-20,4],[-7],[-8,18,21],[-11,22],[-22,11],[-13],[-17],[-5,24],[-16,24],[-19,25],[-23,25],[-26,4,8,11,13],[-4,26],[-11,26],[-18,27],[-20,27],[-22,27],[-21,28],[-25,29],[-29,30],[-24,30],[-28,31],[-27,31],[-26,-31,32],[-30,-32,33],[-33],[1,3,5,7,9,12,14,16,17,19,23],[2,4,6,7,10,11,13,15,17,20,22]],\"atoms\":[{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":577,\"a\":19,\"owners\":[45,51,70,71]},{\"tag\":\"mate\",\"ridge\":577,\"a\":39,\"owners\":[70,71]},{\"tag\":\"mate\",\"ridge\":577,\"a\":65,\"owners\":[45,51,70]},{\"tag\":\"mate\",\"ridge\":577,\"a\":67,\"owners\":[45,51,71]},{\"tag\":\"mate\",\"ridge\":580,\"a\":58,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":641,\"a\":21,\"owners\":[40,51,63,66,71]},{\"tag\":\"mate\",\"ridge\":641,\"a\":47,\"owners\":[63,66,71]},{\"tag\":\"mate\",\"ridge\":641,\"a\":69,\"owners\":[40,51,66,71]},{\"tag\":\"mate\",\"ridge\":648,\"a\":59,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":646,\"a\":40,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":646,\"a\":78,\"owners\":[40]},{\"tag\":\"mate\",\"ridge\":706,\"a\":51,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":172,\"a\":56,\"owners\":[75,83]},{\"tag\":\"mate\",\"ridge\":660,\"a\":63,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":660,\"a\":84,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":676,\"a\":66,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":736,\"a\":71,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":45,\"full_literals\":[-5,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":70,\"full_literals\":[-16,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":77,\"full_literals\":[-19,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":85,\"full_literals\":[-23,25]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[40,56,63,66],\"full_literals\":[-26,4,8,11,13]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":40,\"full_literals\":[-4,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":63,\"full_literals\":[-11,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":75,\"full_literals\":[-18,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":78,\"full_literals\":[-20,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":84,\"full_literals\":[-22,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":83,\"full_literals\":[-21,28]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-25,29],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-29,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-24,false,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-28,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-27,false,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-26,-31,32],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-30,-32,33],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":41,\"owners\":[19,39,45,51,58,65,67,70,71,77,85]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[21,40,47,51,59,63,66,69,71,78,84]}]}"
  "39 -26 4 8 11 0 16 22 0\n40 1 3 5 12 14 16 19 23 0 12 5 17 37 0\n41 2 4 6 11 15 20 22 0 12 9 16 17 38 0\n42 30 0 17 12 30 31 29 18 19 20 21 4 2 1 3 40 0\n43 -32 0 42 36 35 0\n44 26 0 17 16 12 23 24 8 11 7 15 6 41 0\n45 -31 0 44 43 34 0\n46 -28 0 45 32 0\n47 -27 0 45 33 0\n48 -21 0 46 28 0\n49 -18 0 47 25 0\n50 -20 0 47 26 0\n51 -22 0 47 27 0\n52 -8 0 48 49 13 0\n53 -4 0 50 10 0\n54 -11 0 51 14 0\n55 0 52 53 44 54 39 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record013.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record013.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record013.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record013.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record013 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record013.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record013.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record013.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record013.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record013 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record013_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record013_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record013_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record013_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record013_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record013_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record013_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record013 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record013_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record013_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00063.record013_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00063.record013
