module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow29Part00132Data
public import GraphInputsRow29Part00132Frames
public import GraphInputsRow29Part00132Leaves
public import GraphInputsRow29Part00132Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00132.record030
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record030
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨103, by decide⟩, ⟨106, by decide⟩, ⟨107, by decide⟩, ⟨108, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), 9031412132872192, (certNat% 5)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), (certNat% 7), (certNat% 8), (certNat% 9), 77309411328]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), 11276614876790784, (certNat% 11), 211312390963200, (certNat% 12), (certNat% 13)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), (certNat% 15), (certNat% 8), (certNat% 9), 79164837199872]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), 11281006480850944, (certNat% 11), 211312390963200, (certNat% 12), (certNat% 13)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), 246531122790400, (certNat% 18), (certNat% 4), 18045214899830784, (certNat% 19), (certNat% 20)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record030_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record030_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record030_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record030_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record030_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record030_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record030_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record030_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record030_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00132.record030

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00132.record032
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "178b52b49715c4f2d2ac8f25a8ea9687ab1aa6a5a5635a362da4e538ce4b8ae8785e786d15c4f15a4e9565391e6c5715a5a5655554d54d4b5534cd2b51d176c358ce3a4e5334cb31cd4b32d2b2ac6ba1e4751cc749e1725c5743c8f13d2c0f2c29485a0ea8629a160d82e079494a4590e525294354342d074c328c530cc4b0ac1b21c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6d26db49249a4db4926db4d24da6db49349269a4924924da492491249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record032 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record032 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record032.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record032.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record032.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 53), (facetIndex 64), (facetIndex 76), (facetIndex 99)]))
 (.branch 2
 (.leaf ([(facetIndex 67), (facetIndex 89), (facetIndex 98), (facetIndex 104)]))
 (.leaf ([(facetIndex 55), (facetIndex 74), (facetIndex 77), (facetIndex 79)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 96), (facetIndex 97), (facetIndex 106)]))
 (.leaf ([(facetIndex 41), (facetIndex 42), (facetIndex 60), (facetIndex 65), (facetIndex 69), (facetIndex 86), (facetIndex 105)])))
 (.branch 6
 (.leaf ([(facetIndex 66), (facetIndex 84), (facetIndex 85), (facetIndex 102), (facetIndex 103)]))
 (.leaf ([(facetIndex 70), (facetIndex 78)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "e1b4005b00000812d0005900801a036000400040000000012z1f;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record032 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record032_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00132.record032" "{\"atoms\":[{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00132.record032" 63

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00132.record032" "{\"ridges\":[[20,321],[20,328],[24,530],[26,644],[29,592],[30,704],[38,530],[41,326],[43,644],[48,321],[48,328],[52,592],[53,657],[55,354],[56,704],[61,321],[61,328],[65,340],[67,657],[69,452],[73,321],[73,328],[75,321],[75,328],[76,240],[77,368],[78,657],[79,480],[81,532],[85,326],[88,532],[90,592],[91,532],[91,644],[92,644],[93,644],[95,592],[97,354],[99,688],[100,592],[100,704],[102,340],[103,588],[105,212],[106,368]],\"owners\":[[20,321,[41,55,65,69,77,79],[48,61,73,75]],[48,321,[65,69,77,79],[20,41,55,61,73,75]],[61,321,[55,77,79],[20,41,48,65,69,73,75]],[73,321,[41,55,69,79],[20,48,61,65,75,77]],[75,321,[41,65,69],[20,48,55,61,73,77,79]],[20,328,[85,97,102,106],[48,61,73,75]],[48,328,[102,106],[20,61,73,75,85,97]],[61,328,[97,106],[20,48,73,75,85,102]],[73,328,[85,97],[20,48,61,75,102,106]],[75,328,[85,102],[20,48,61,73,97,106]],[24,530,[29,52,53,95,99,100],[38,81,88,91]],[38,530,[29,95,99,100],[24,52,53,81,88,91]],[81,532,[66,67,104,105],[24,38,88,90,91,103]],[88,532,[66,67,103,105],[24,38,81,90,91,104]],[91,532,[66,103],[24,38,67,81,88,90,104,105]],[26,644,[67,70,104,105],[43,91,92,93]],[43,644,[104,105],[26,67,70,91,92,93]],[91,644,[70],[26,43,67,92,93,104,105]],[92,644,[67,70,105],[26,43,91,93,104]],[93,644,[67,104],[26,43,70,91,92,105]],[29,592,[66,78,103,105],[52,90,95,100]],[52,592,[103,105],[29,66,78,90,95,100]],[90,592,[78],[29,52,66,95,100,103,105]],[95,592,[66,78,105],[29,52,90,100,103]],[100,592,[66,103],[29,52,78,90,95,105]],[30,704,[70,78,105],[56,93,100]],[56,704,[105],[30,70,78,93,100]],[100,704,[70],[30,56,78,93,105]],[41,326,[85],[]],[85,326,[41],[]],[53,657,[67,78],[]],[67,657,[53,78],[]],[78,657,[53,67],[]],[55,354,[97],[]],[97,354,[55],[]],[105,212,[64,89],[]],[65,340,[102],[]],[102,340,[65],[]],[69,452,[],[]],[76,240,[98],[]],[77,368,[106],[]],[106,368,[77],[]],[79,480,[],[]],[103,588,[86],[]],[99,688,[104],[]]],\"edges\":[[34,[24,29,38,52,53,66,67,78,81,88,90,91,95,99,100,103,104,105]],[40,[20,41,48,55,61,65,69,73,75,77,79,85,97,102,106]],[43,[26,30,43,53,56,67,70,78,91,92,93,99,100,104,105]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00132.record032" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00132.record032\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-15,-7],[-16,-15],[-20,-7],[-20,-16],[-28,-15],[-28,-20],[-41,-15],[-41,-20],[-1,7,12,16,19,24,26],[-9,16,19,24,26],[-14,12,24,26],[-21,7,12,19,26],[-22,7,16,19],[-1,28,37,41,45],[-9,41,45],[-14,37,45],[-21,28,37],[-22,28,41],[-2,4,10,11,36,39,40],[-6,4,36,39,40],[-27,17,18,43,44],[-30,17,18,42,44],[-33,17,42],[-3,18,20,43,44],[-8,43,44],[-33,20],[-34,18,20,44],[-35,18,43],[-4,17,25,42,44],[-10,42,44],[-32,25],[-36,17,25,44],[-40,17,42],[-5,20,25,44],[-13,44],[-40,20],[-7,28],[-28,7],[-11,18,25],[-18,11,25],[-25,11,18],[-12,37],[-37,12],[-44,15,31],[-16,41],[-41,16],[-19],[-23,38],[-24,45],[-45,24],[-26],[-42,29],[-39,43],[-46,11,15,23,39],[-11,46],[-15,46],[-39,46],[-18,47],[-31,47],[-38,47],[-43,47],[-12,48],[-24,48],[-37,49],[-45,49],[-7,50],[-16,50],[-29,50],[-44,50],[-17,51],[-28,51],[-41,51],[-25,52],[-48,53],[-47,53],[-47,-48,54],[-55,46,53],[-53,55],[-54,56],[-46,55],[-46,-53,56],[-50,57],[-49,57],[-49,-50,58],[-52,59],[-51,59],[-51,-52,60],[-60,62],[-57,61],[-57,-59,62],[-58,62],[-55,-62,63],[-56,-61,63],[-63],[2,4,6,10,11,17,18,25,27,30,32,33,36,39,40,42,43,44],[1,7,9,12,14,16,19,21,22,24,26,28,37,41,45],[3,5,8,11,13,18,20,25,33,34,35,39,40,43,44]],\"atoms\":[{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":64,\"b\":41},{\"tag\":\"incompatible\",\"a\":65,\"b\":64},{\"tag\":\"incompatible\",\"a\":70,\"b\":41},{\"tag\":\"incompatible\",\"a\":70,\"b\":65},{\"tag\":\"incompatible\",\"a\":85,\"b\":64},{\"tag\":\"incompatible\",\"a\":85,\"b\":70},{\"tag\":\"incompatible\",\"a\":102,\"b\":64},{\"tag\":\"incompatible\",\"a\":102,\"b\":70},{\"tag\":\"mate\",\"ridge\":321,\"a\":20,\"owners\":[41,55,65,69,77,79]},{\"tag\":\"mate\",\"ridge\":321,\"a\":48,\"owners\":[65,69,77,79]},{\"tag\":\"mate\",\"ridge\":321,\"a\":61,\"owners\":[55,77,79]},{\"tag\":\"mate\",\"ridge\":321,\"a\":73,\"owners\":[41,55,69,79]},{\"tag\":\"mate\",\"ridge\":321,\"a\":75,\"owners\":[41,65,69]},{\"tag\":\"mate\",\"ridge\":328,\"a\":20,\"owners\":[85,97,102,106]},{\"tag\":\"mate\",\"ridge\":328,\"a\":48,\"owners\":[102,106]},{\"tag\":\"mate\",\"ridge\":328,\"a\":61,\"owners\":[97,106]},{\"tag\":\"mate\",\"ridge\":328,\"a\":73,\"owners\":[85,97]},{\"tag\":\"mate\",\"ridge\":328,\"a\":75,\"owners\":[85,102]},{\"tag\":\"mate\",\"ridge\":530,\"a\":24,\"owners\":[29,52,53,95,99,100]},{\"tag\":\"mate\",\"ridge\":530,\"a\":38,\"owners\":[29,95,99,100]},{\"tag\":\"mate\",\"ridge\":532,\"a\":81,\"owners\":[66,67,104,105]},{\"tag\":\"mate\",\"ridge\":532,\"a\":88,\"owners\":[66,67,103,105]},{\"tag\":\"mate\",\"ridge\":532,\"a\":91,\"owners\":[66,103]},{\"tag\":\"mate\",\"ridge\":644,\"a\":26,\"owners\":[67,70,104,105]},{\"tag\":\"mate\",\"ridge\":644,\"a\":43,\"owners\":[104,105]},{\"tag\":\"mate\",\"ridge\":644,\"a\":91,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":644,\"a\":92,\"owners\":[67,70,105]},{\"tag\":\"mate\",\"ridge\":644,\"a\":93,\"owners\":[67,104]},{\"tag\":\"mate\",\"ridge\":592,\"a\":29,\"owners\":[66,78,103,105]},{\"tag\":\"mate\",\"ridge\":592,\"a\":52,\"owners\":[103,105]},{\"tag\":\"mate\",\"ridge\":592,\"a\":90,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":592,\"a\":95,\"owners\":[66,78,105]},{\"tag\":\"mate\",\"ridge\":592,\"a\":100,\"owners\":[66,103]},{\"tag\":\"mate\",\"ridge\":704,\"a\":30,\"owners\":[70,78,105]},{\"tag\":\"mate\",\"ridge\":704,\"a\":56,\"owners\":[105]},{\"tag\":\"mate\",\"ridge\":704,\"a\":100,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":326,\"a\":41,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":326,\"a\":85,\"owners\":[41]},{\"tag\":\"mate\",\"ridge\":657,\"a\":53,\"owners\":[67,78]},{\"tag\":\"mate\",\"ridge\":657,\"a\":67,\"owners\":[53,78]},{\"tag\":\"mate\",\"ridge\":657,\"a\":78,\"owners\":[53,67]},{\"tag\":\"mate\",\"ridge\":354,\"a\":55,\"owners\":[97]},{\"tag\":\"mate\",\"ridge\":354,\"a\":97,\"owners\":[55]},{\"tag\":\"mate\",\"ridge\":212,\"a\":105,\"owners\":[64,89]},{\"tag\":\"mate\",\"ridge\":340,\"a\":65,\"owners\":[102]},{\"tag\":\"mate\",\"ridge\":340,\"a\":102,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":452,\"a\":69,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":240,\"a\":76,\"owners\":[98]},{\"tag\":\"mate\",\"ridge\":368,\"a\":77,\"owners\":[106]},{\"tag\":\"mate\",\"ridge\":368,\"a\":106,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":480,\"a\":79,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":588,\"a\":103,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":688,\"a\":99,\"owners\":[104]},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[53,64,76,99],\"full_literals\":[-46,11,15,23,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":53,\"full_literals\":[-11,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":64,\"full_literals\":[-15,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":99,\"full_literals\":[-39,46]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":67,\"full_literals\":[-18,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":89,\"full_literals\":[-31,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":98,\"full_literals\":[-38,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":104,\"full_literals\":[-43,47]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":55,\"full_literals\":[-12,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":77,\"full_literals\":[-24,48]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":97,\"full_literals\":[-37,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":106,\"full_literals\":[-45,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":41,\"full_literals\":[-7,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":65,\"full_literals\":[-16,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":86,\"full_literals\":[-29,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":105,\"full_literals\":[-44,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":66,\"full_literals\":[-17,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":85,\"full_literals\":[-28,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":102,\"full_literals\":[-41,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":78,\"full_literals\":[-25,52]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-48,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-47,false,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-47,-48,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-55,46,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-53,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-54,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-46,false,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-46,-53,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-50,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-49,false,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-49,-50,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-52,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-51,false,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-51,-52,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-60,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-57,false,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-57,-59,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-58,false,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-55,-62,63],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-56,-61,63],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":34,\"owners\":[24,29,38,52,53,66,67,78,81,88,90,91,95,99,100,103,104,105]},{\"tag\":\"edge\",\"edge\":40,\"owners\":[20,41,48,55,61,65,69,73,75,77,79,85,97,102,106]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[26,30,43,53,56,67,70,78,91,92,93,99,100,104,105]}]}"
  "98 1 7 9 12 14 16 21 22 24 28 37 41 45 0 47 51 96 0\n99 -20 48 0 51 47 62 63 11 50 43 3 4 6 8 12 10 13 9 98 0\n100 55 0 78 80 74 75 55 56 57 58 59 61 28 41 44 25 35 99 26 36 24 27 34 97 0\n101 -62 0 100 94 92 0\n102 -60 0 101 88 0\n103 -58 0 101 91 0\n104 -15 48 0 51 47 62 63 11 50 43 1 2 5 7 12 10 13 9 98 0\n105 41 16 7 12 9 45 21 22 24 28 37 14 0 98 14 0\n106 53 0 100 51 102 74 75 77 62 63 58 60 61 43 50 11 48 53 104 54 39 73 87 71 72 37 17 15 45 18 105 0\n107 28 37 41 45 0 16 42 45 15 49 37 17 18 105 0\n108 -28 0 101 38 71 66 86 82 90 0\n109 -37 0 103 101 94 106 43 64 62 83 84 89 90 68 69 93 85 86 52 79 81 73 70 30 23 33 76 55 57 31 40 29 32 61 21 22 19 20 95 0\n110 -41 0 101 46 72 67 86 82 90 0\n111 45 0 110 108 109 107 0\n112 24 0 111 50 0\n113 49 0 111 65 0\n114 48 0 112 63 0\n115 57 0 113 83 0\n116 -50 0 113 103 84 0\n117 61 0 115 89 0\n118 -59 0 115 101 90 0\n119 -29 0 116 68 0\n120 -44 0 116 69 0\n121 -56 0 117 94 93 0\n122 -52 0 118 85 0\n123 -51 0 118 86 0\n124 -42 0 119 52 0\n125 -54 0 121 79 0\n126 -46 0 121 106 81 0\n127 -25 0 122 73 0\n128 -17 0 123 70 0\n129 -10 0 124 120 30 0\n130 -33 0 124 128 23 0\n131 -40 0 124 128 33 0\n132 -47 0 125 114 76 0\n133 -11 0 126 55 0\n134 -39 0 126 57 0\n135 -32 0 127 31 0\n136 -18 0 127 133 40 0\n137 -4 0 127 128 124 120 29 0\n138 -36 0 127 128 120 32 0\n139 -43 0 132 61 0\n140 -27 0 136 128 139 120 21 0\n141 -30 0 136 124 128 120 22 0\n142 -2 0 137 129 133 138 134 131 19 0\n143 -6 0 137 138 134 131 20 0\n144 0 137 142 143 129 133 128 136 127 140 141 135 130 138 134 131 124 139 120 95 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record032.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record032.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record032.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record032.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record032 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record032.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record032.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record032.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record032.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record032 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record032_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record032_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record032_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record032_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record032_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record032_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record032_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record032 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record032_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record032_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00132.record032_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00132.record032
