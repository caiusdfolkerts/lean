module
prelude
public import FacetCliqueRaw
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow31Part00173Data
public import GraphInputsRow31Part00173Frames
public import GraphInputsRow31Part00173Leaves
public import GraphInputsRow31Part00173Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00173.record011
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record011
def vertexColumn : Fields := ⟨10, hexnat% "cd2b46d2745d0f4cb2ac6b26c5b0ecccab26ca725c8f2c6a9a66a5a568dac9aa669a66598e6c5a9665a56558d68d9362d876c3a8e63a4e538cecc6b16c6715c4f1ca6a96a6695a4e9c669966659564d9c96a569665594e5c569565655554d58d5352d475c368d6364d534cd8b52d2b46dc8ea368e6358ce3c4e9364e5354cd38cd332cc73c2e8b62e4b52ccb86d1b26c5bc1e8761e4751cc789d2729c6785d1725c570de0e4388e13a314c4b11c625494a51960d4348d1361344c9314e0b42c8b12e0741c8711c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6db6db6db6db6db6db6db6db6db4924924926db6db6db49249b6db49249249249b6db492492492492492492492492499249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨108, by decide⟩, ⟨109, by decide⟩, ⟨110, by decide⟩, ⟨111, by decide⟩, ⟨112, by decide⟩, ⟨113, by decide⟩, ⟨114, by decide⟩, ⟨115, by decide⟩, ⟨116, by decide⟩, ⟨117, by decide⟩, ⟨118, by decide⟩, ⟨119, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fc08ffc003c08ffe00000000", hexnat% "fc0000000000000000000000000000", hexnat% "3f000000700000000000000000000", 17856068835082240, 18158513705074032640]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fc04ffc003c04ffd00000000", hexnat% "fc0000000000000000000000000000", hexnat% "3f000000b00000000000000000000", 17926437579259904, 18158513709368999936]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fc0000000000000000003000000000", hexnat% "ffc00000000000000000", 17996806323437568, hexnat% "3f0000000000003c0000000000000", 17368847745024, hexnat% "fc0f00000000000000000000", 18158513713663967232]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record011_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record011_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record011_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record011_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record011_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record011_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record011_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record011_validity Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record011_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00173.record011

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00173.record012
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "ccab26ca725c8f2caaaa6aa6a5a8eac6a9a66a5a568dac9aa669a66598e6c5a9665a56558d6c3a8e63a4e538cecc6b16c6715c4f1ca6a96a6695a4e9c669966659564d9c96a569665594e5c569565655554d5c368d6364d534cdc8ea368e6358ce3c4e9364e5354cd3c2e8b62e4b52ccb8ad2b2ac6b86d1b26c5bc1e8761e4751cc789d2729c6785d1725c578c9322c8728390e2384e8c5312c4718350d2344d88d2328c6384d1324c530ce0b42c8b12e0741c8711c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "124926db6db6db6db6db6db4924924926db6db6db6db6db6db492492492492492492492492492492492489249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record012 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record012 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record012.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 74), (facetIndex 75), (facetIndex 76), (facetIndex 77), (facetIndex 78), (facetIndex 79)]))
 (.leaf ([(facetIndex 104), (facetIndex 105), (facetIndex 106), (facetIndex 107), (facetIndex 108), (facetIndex 109)])))
 (.branch 3
 (.leaf ([(facetIndex 110), (facetIndex 111), (facetIndex 112), (facetIndex 113), (facetIndex 114), (facetIndex 115)]))
 (.leaf ([(facetIndex 140), (facetIndex 141), (facetIndex 142), (facetIndex 143), (facetIndex 144), (facetIndex 145)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 34), (facetIndex 35), (facetIndex 36), (facetIndex 37), (facetIndex 42), (facetIndex 43), (facetIndex 44), (facetIndex 45), (facetIndex 46), (facetIndex 47)]))
 (.leaf ([(facetIndex 38), (facetIndex 39), (facetIndex 40), (facetIndex 41), (facetIndex 68), (facetIndex 69), (facetIndex 70), (facetIndex 71), (facetIndex 72), (facetIndex 73)])))
 (.branch 7
 (.leaf ([(facetIndex 48), (facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 62), (facetIndex 63), (facetIndex 64), (facetIndex 65), (facetIndex 66), (facetIndex 67)]))
 (.leaf ([(facetIndex 52), (facetIndex 53), (facetIndex 54), (facetIndex 55), (facetIndex 56), (facetIndex 57), (facetIndex 58), (facetIndex 59), (facetIndex 60), (facetIndex 61)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6dbz12;492489249z16;2db6ddb6dbfffffffdb692492db649z1a;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [2, 3]
def grouped2_0007 : List Nat := [3]
def grouped2_0008 : List Nat := [4, 5, 6, 7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record012 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record012_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00173.record012" "{\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":111},{\"tag\":\"facet\",\"index\":112},{\"tag\":\"facet\",\"index\":113},{\"tag\":\"facet\",\"index\":114},{\"tag\":\"facet\",\"index\":115},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00173.record012" 27

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00173.record012" "{\"ridges\":[[0,14],[18,13],[74,76],[74,140],[75,76],[75,268],[76,76],[76,524],[77,140],[77,268],[79,268],[79,524],[110,76],[111,268],[112,76],[113,268],[115,268]],\"owners\":[[18,13,[0,19,20,21],[]],[0,14,[26,27,28,29],[]],[74,76,[26,111,112],[18,75,76,110]],[75,76,[26,110,112],[18,74,76,111]],[76,76,[26,110,111],[18,74,75,112]],[110,76,[18,75,76],[26,74,111,112]],[112,76,[18,74,75],[26,76,110,111]],[74,140,[27,113,114],[19,77,78,110]],[77,140,[27,110,114],[19,74,78,113]],[75,268,[28,113,115],[20,77,79,111]],[77,268,[28,111,115],[20,75,79,113]],[79,268,[28,111,113],[20,75,77,115]],[111,268,[20,77,79],[28,75,113,115]],[113,268,[20,75,79],[28,77,111,115]],[115,268,[20,75,77],[28,79,111,113]],[76,524,[29,114,115],[21,78,79,112]],[79,524,[29,112,114],[21,76,78,115]]],\"edges\":[],\"groupings\":[2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00173.record012" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00173.record012\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-10,-3],[-10,-4],[-10,-5],[-11,-3],[-11,-4],[-11,-5],[-12,-3],[-12,-4],[-12,-5],[-13,-3],[-13,-4],[-13,-5],[-14,-3],[-14,-4],[-14,-5],[-15,-3],[-15,-4],[-15,-5],[-16,-6],[-16,-7],[-16,-8],[-16,-9],[-17,-6],[-17,-7],[-17,-8],[-17,-9],[-18,-6],[-18,-7],[-18,-8],[-18,-9],[-19,-6],[-19,-7],[-19,-8],[-19,-9],[-19,-16],[-19,-18],[-20,-6],[-20,-7],[-20,-8],[-20,-9],[-20,-14],[-20,-16],[-20,-17],[-20,-18],[-20,-19],[-21,-6],[-21,-7],[-21,-8],[-21,-9],[-21,-16],[-21,-18],[-21,-20],[-2,1,3,4,5],[-1,6,7,8,9],[-10,6,17,18],[-11,6,16,18],[-12,6,16,17],[-16,2,11,12],[-18,2,10,11],[-10,7,19,20],[-13,7,16,20],[-11,8,19,21],[-13,8,17,21],[-15,8,17,19],[-17,4,13,15],[-19,4,11,15],[-21,4,11,13],[-12,9,20,21],[-15,9,18,20],[-22,10,11,12,13,14,15],[-23,16,17,18,19,20,21],[-24,22],[-25,23],[-26,24],[-26,25],[-27,26],[27]],\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":110},{\"tag\":\"facet\",\"index\":111},{\"tag\":\"facet\",\"index\":112},{\"tag\":\"facet\",\"index\":113},{\"tag\":\"facet\",\"index\":114},{\"tag\":\"facet\",\"index\":115},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":74,\"b\":19},{\"tag\":\"incompatible\",\"a\":74,\"b\":20},{\"tag\":\"incompatible\",\"a\":74,\"b\":21},{\"tag\":\"incompatible\",\"a\":75,\"b\":19},{\"tag\":\"incompatible\",\"a\":75,\"b\":20},{\"tag\":\"incompatible\",\"a\":75,\"b\":21},{\"tag\":\"incompatible\",\"a\":76,\"b\":19},{\"tag\":\"incompatible\",\"a\":76,\"b\":20},{\"tag\":\"incompatible\",\"a\":76,\"b\":21},{\"tag\":\"incompatible\",\"a\":77,\"b\":19},{\"tag\":\"incompatible\",\"a\":77,\"b\":20},{\"tag\":\"incompatible\",\"a\":77,\"b\":21},{\"tag\":\"incompatible\",\"a\":78,\"b\":19},{\"tag\":\"incompatible\",\"a\":78,\"b\":20},{\"tag\":\"incompatible\",\"a\":78,\"b\":21},{\"tag\":\"incompatible\",\"a\":79,\"b\":19},{\"tag\":\"incompatible\",\"a\":79,\"b\":20},{\"tag\":\"incompatible\",\"a\":79,\"b\":21},{\"tag\":\"incompatible\",\"a\":110,\"b\":26},{\"tag\":\"incompatible\",\"a\":110,\"b\":27},{\"tag\":\"incompatible\",\"a\":110,\"b\":28},{\"tag\":\"incompatible\",\"a\":110,\"b\":29},{\"tag\":\"incompatible\",\"a\":111,\"b\":26},{\"tag\":\"incompatible\",\"a\":111,\"b\":27},{\"tag\":\"incompatible\",\"a\":111,\"b\":28},{\"tag\":\"incompatible\",\"a\":111,\"b\":29},{\"tag\":\"incompatible\",\"a\":112,\"b\":26},{\"tag\":\"incompatible\",\"a\":112,\"b\":27},{\"tag\":\"incompatible\",\"a\":112,\"b\":28},{\"tag\":\"incompatible\",\"a\":112,\"b\":29},{\"tag\":\"incompatible\",\"a\":113,\"b\":26},{\"tag\":\"incompatible\",\"a\":113,\"b\":27},{\"tag\":\"incompatible\",\"a\":113,\"b\":28},{\"tag\":\"incompatible\",\"a\":113,\"b\":29},{\"tag\":\"incompatible\",\"a\":113,\"b\":110},{\"tag\":\"incompatible\",\"a\":113,\"b\":112},{\"tag\":\"incompatible\",\"a\":114,\"b\":26},{\"tag\":\"incompatible\",\"a\":114,\"b\":27},{\"tag\":\"incompatible\",\"a\":114,\"b\":28},{\"tag\":\"incompatible\",\"a\":114,\"b\":29},{\"tag\":\"incompatible\",\"a\":114,\"b\":78},{\"tag\":\"incompatible\",\"a\":114,\"b\":110},{\"tag\":\"incompatible\",\"a\":114,\"b\":111},{\"tag\":\"incompatible\",\"a\":114,\"b\":112},{\"tag\":\"incompatible\",\"a\":114,\"b\":113},{\"tag\":\"incompatible\",\"a\":115,\"b\":26},{\"tag\":\"incompatible\",\"a\":115,\"b\":27},{\"tag\":\"incompatible\",\"a\":115,\"b\":28},{\"tag\":\"incompatible\",\"a\":115,\"b\":29},{\"tag\":\"incompatible\",\"a\":115,\"b\":110},{\"tag\":\"incompatible\",\"a\":115,\"b\":112},{\"tag\":\"incompatible\",\"a\":115,\"b\":114},{\"tag\":\"mate\",\"ridge\":13,\"a\":18,\"owners\":[0,19,20,21]},{\"tag\":\"mate\",\"ridge\":14,\"a\":0,\"owners\":[26,27,28,29]},{\"tag\":\"mate\",\"ridge\":76,\"a\":74,\"owners\":[26,111,112]},{\"tag\":\"mate\",\"ridge\":76,\"a\":75,\"owners\":[26,110,112]},{\"tag\":\"mate\",\"ridge\":76,\"a\":76,\"owners\":[26,110,111]},{\"tag\":\"mate\",\"ridge\":76,\"a\":110,\"owners\":[18,75,76]},{\"tag\":\"mate\",\"ridge\":76,\"a\":112,\"owners\":[18,74,75]},{\"tag\":\"mate\",\"ridge\":140,\"a\":74,\"owners\":[27,113,114]},{\"tag\":\"mate\",\"ridge\":140,\"a\":77,\"owners\":[27,110,114]},{\"tag\":\"mate\",\"ridge\":268,\"a\":75,\"owners\":[28,113,115]},{\"tag\":\"mate\",\"ridge\":268,\"a\":77,\"owners\":[28,111,115]},{\"tag\":\"mate\",\"ridge\":268,\"a\":79,\"owners\":[28,111,113]},{\"tag\":\"mate\",\"ridge\":268,\"a\":111,\"owners\":[20,77,79]},{\"tag\":\"mate\",\"ridge\":268,\"a\":113,\"owners\":[20,75,79]},{\"tag\":\"mate\",\"ridge\":268,\"a\":115,\"owners\":[20,75,77]},{\"tag\":\"mate\",\"ridge\":524,\"a\":76,\"owners\":[29,114,115]},{\"tag\":\"mate\",\"ridge\":524,\"a\":79,\"owners\":[29,112,114]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[74,75,76,77,78,79],\"full_literals\":[-22,10,11,12,13,14,15]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[110,111,112,113,114,115],\"full_literals\":[-23,16,17,18,19,20,21]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-24,22,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-25,23,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-26,24,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-26,false,25],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-27,26,false],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true}]}"
  "p cnf 27 77\n-10 -3 0\n-10 -4 0\n-10 -5 0\n-11 -3 0\n-11 -4 0\n-11 -5 0\n-12 -3 0\n-12 -4 0\n-12 -5 0\n-13 -3 0\n-13 -4 0\n-13 -5 0\n-14 -3 0\n-14 -4 0\n-14 -5 0\n-15 -3 0\n-15 -4 0\n-15 -5 0\n-16 -6 0\n-16 -7 0\n-16 -8 0\n-16 -9 0\n-17 -6 0\n-17 -7 0\n-17 -8 0\n-17 -9 0\n-18 -6 0\n-18 -7 0\n-18 -8 0\n-18 -9 0\n-19 -6 0\n-19 -7 0\n-19 -8 0\n-19 -9 0\n-19 -16 0\n-19 -18 0\n-20 -6 0\n-20 -7 0\n-20 -8 0\n-20 -9 0\n-20 -14 0\n-20 -16 0\n-20 -17 0\n-20 -18 0\n-20 -19 0\n-21 -6 0\n-21 -7 0\n-21 -8 0\n-21 -9 0\n-21 -16 0\n-21 -18 0\n-21 -20 0\n-2 1 3 4 5 0\n-1 6 7 8 9 0\n-10 6 17 18 0\n-11 6 16 18 0\n-12 6 16 17 0\n-16 2 11 12 0\n-18 2 10 11 0\n-10 7 19 20 0\n-13 7 16 20 0\n-11 8 19 21 0\n-13 8 17 21 0\n-15 8 17 19 0\n-17 4 13 15 0\n-19 4 11 15 0\n-21 4 11 13 0\n-12 9 20 21 0\n-15 9 18 20 0\n-22 10 11 12 13 14 15 0\n-23 16 17 18 19 20 21 0\n-24 22 0\n-25 23 0\n-26 24 0\n-26 25 0\n-27 26 0\n27 0\n"
  "78 26 0 77 76 0\n79 24 0 78 74 0\n80 25 0 78 75 0\n81 22 0 79 72 0\n82 23 0 80 73 0\n83 -6 0 82 19 23 27 31 37 46 71 0\n84 -7 0 82 20 24 28 32 38 47 71 0\n85 -8 0 82 21 25 29 33 39 48 71 0\n86 -5 0 81 3 6 9 12 15 18 70 0\n87 -9 0 82 22 26 30 34 40 49 71 0\n88 -1 0 87 83 85 84 54 0\n89 -3 0 81 1 4 7 10 13 16 70 0\n90 -4 0 81 2 5 8 11 14 17 70 0\n91 -2 0 90 88 89 86 53 0\n92 -16 11 0 91 87 42 50 58 68 0\n93 20 16 18 0 83 84 87 90 82 56 61 69 67 66 65 71 0\n94 16 18 0 81 85 83 56 93 41 43 45 52 55 64 57 63 70 0\n95 -16 0 85 35 50 92 62 0\n96 18 0 95 94 0\n97 -19 0 96 36 0\n98 -20 0 96 44 0\n99 -21 0 96 51 0\n100 -10 0 97 84 98 60 0\n101 -11 0 97 85 99 62 0\n102 0 100 101 91 96 59 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record012.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record012.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record012.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record012.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record012 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record012.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record012.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record012.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record012.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record012 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record012_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record012_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record012_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record012_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record012_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record012_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record012_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record012 Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record012_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record012_validity Papers.RationalityTen.CompactReplay.GraphInputsRow31Part00173.record012_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow31Part00173.record012
