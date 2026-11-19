module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow26Part00011Data
public import GraphInputsRow26Part00011Frames
public import GraphInputsRow26Part00011Leaves
public import GraphInputsRow26Part00011Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00011.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record002
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [(certNat% 2), (certNat% 3)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 4), 36028797018963968, 563087392374784]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), 563087392374784, 324259173174870016, (certNat% 6)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨21, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [(certNat% 7), (certNat% 8), 2251799813685248]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c1 c7
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c1 c8
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c1 c10
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c1 c11
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c1 c12
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c1 c13
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c14 c9
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨21, by decide⟩ c1 c10
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c1 c16
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c1 c17
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 9), 536870912, (certNat% 10)]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), (certNat% 10), (certNat% 12), 288230376158003200]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c21 c20
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c22 c15
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), 563087392374784, 324259173174870016, (certNat% 14), 1152921504608944128]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c24 c23
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c25 c6
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), 5629499534213120, (certNat% 14), 324259173175394304, 1152921504608944128]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c1 c7
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c1 c28
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), (certNat% 12), 570425344]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c30 c29
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), 324259173170675712, (certNat% 14), 137438953472]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c32 c31
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), (certNat% 19), (certNat% 6), 637534208, 563087392374784]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c34 c33
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), 137606725632, 537919488, 324259173175394304, 1152921504608944128]
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 21), 324259173174870016, (certNat% 6), (certNat% 22), 563087560146944, 70369348157440]
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c37 c36
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨17, by decide⟩ c38 c35
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c39 c27
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨18, by decide⟩ c40 c26
  c41
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record002_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00011.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00011.record024
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record024
def vertexColumn : Fields := ⟨10, (certNat% 23)⟩
def kindColumn : Fields := ⟨3, (certNat% 24)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨31, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨58, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨84, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), (certNat% 26), 35218731958272, (certNat% 27), 134217728]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 28), (certNat% 27), (certNat% 29), 201457664, 171798953984, 175921862017024]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c1 c0
  c2
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record024_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record024_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record024_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record024_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record024_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record024_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record024_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record024_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record024_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00011.record024

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00011.record001
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3b0da338ad34cab26cc723ce49b25c96ac693ac5a9655b0ea394e8791eac571aa5698e539a94e5a56352d475a362d2b46d8743d58ce354d332cc7352d2b2ac6b46c3b31c5723c1fcc2b0ca168a514a2584e2c4692544d24c4b21c4705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "924db6db69b69b69b4da6db4d36da6db6d34da6d2489249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record001 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record001 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record001.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 18), (facetIndex 19), (facetIndex 20), (facetIndex 21)]))
 (.branch 2
 (.leaf ([(facetIndex 24), (facetIndex 27), (facetIndex 54), (facetIndex 62)]))
 (.leaf ([(facetIndex 41), (facetIndex 43), (facetIndex 58), (facetIndex 71)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 72), (facetIndex 73)]))
 (.leaf ([(facetIndex 29), (facetIndex 51)])))
 (.branch 6
 (.leaf ([(facetIndex 36), (facetIndex 48)]))
 (.leaf ([(facetIndex 74)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "19b400000040080040805000410005000020201z12;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 7
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1, 2]
def grouped2_0003 : List Nat := [1]
def grouped2_0004 : List Nat := [1, 2]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [3]
def grouped2_0007 : List Nat := [3, 4]
def grouped2_0008 : List Nat := [3, 4, 5, 6]
def grouped2_0009 : List Nat := [4]
def grouped2_0010 : List Nat := [5]
def grouped2_0011 : List Nat := [5, 6]
def grouped2_0012 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record001 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record001_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00011.record001" "{\"atoms\":[{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00011.record001" 31

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00011.record001" "{\"ridges\":[[23,281],[27,322],[54,266],[57,340]],\"owners\":[[54,266,[23,26,60,61],[12,27,52,56,62]],[27,322,[57,63],[12,31,33,54,62]],[23,281,[46],[]],[57,340,[],[]]],\"edges\":[],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00011.record001" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00011.record001\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-5,-2],[-5,-3],[-6,-5],[-7,-5],[-13,-5],[-14,-12],[-15,-5],[-16,-5],[-19,-8],[-20,-9],[-20,-17],[-20,-18],[-10,1,3,13,14],[-4,11,16],[-1,8],[-11],[-21,2,4,10,15],[-22,6,7,12,17],[-23,18,19],[-24,5,9],[-25,20],[-26,21],[-26,22],[-27,26],[-28,23],[-28,24],[-29,25],[-30,28],[-30,29],[-31,27],[-31,30],[31]],\"atoms\":[{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":29,\"b\":24},{\"tag\":\"incompatible\",\"a\":29,\"b\":26},{\"tag\":\"incompatible\",\"a\":41,\"b\":29},{\"tag\":\"incompatible\",\"a\":43,\"b\":29},{\"tag\":\"incompatible\",\"a\":60,\"b\":29},{\"tag\":\"incompatible\",\"a\":61,\"b\":58},{\"tag\":\"incompatible\",\"a\":62,\"b\":29},{\"tag\":\"incompatible\",\"a\":63,\"b\":29},{\"tag\":\"incompatible\",\"a\":73,\"b\":46},{\"tag\":\"incompatible\",\"a\":74,\"b\":51},{\"tag\":\"incompatible\",\"a\":74,\"b\":71},{\"tag\":\"incompatible\",\"a\":74,\"b\":72},{\"tag\":\"mate\",\"ridge\":266,\"a\":54,\"owners\":[23,26,60,61]},{\"tag\":\"mate\",\"ridge\":322,\"a\":27,\"owners\":[57,63]},{\"tag\":\"mate\",\"ridge\":281,\"a\":23,\"owners\":[46]},{\"tag\":\"mate\",\"ridge\":340,\"a\":57,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[24,27,54,62],\"full_literals\":[-21,2,4,10,15]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[41,43,58,71],\"full_literals\":[-22,6,7,12,17]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[72,73],\"full_literals\":[-23,18,19]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[29,51],\"full_literals\":[-24,5,9]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[74],\"full_literals\":[-25,20]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-26,21,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-26,false,22],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-27,false,26],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-28,23,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-28,false,24],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-29,false,25],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-30,28,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-30,false,29],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-31,27,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-31,false,30],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true}]}"
  "33 27 0 32 30 0\n34 30 0 32 31 0\n35 26 0 33 24 0\n36 28 0 34 28 0\n37 29 0 34 29 0\n38 21 0 35 22 0\n39 22 0 35 23 0\n40 23 0 36 25 0\n41 24 0 36 26 0\n42 25 0 37 27 0\n43 20 0 42 21 0\n44 -9 0 43 10 0\n45 -17 0 43 11 0\n46 -18 0 43 12 0\n47 5 0 44 41 20 0\n48 19 0 46 40 19 0\n49 -2 0 47 1 0\n50 -3 0 47 2 0\n51 -6 0 47 3 0\n52 -7 0 47 4 0\n53 -13 0 47 5 0\n54 -15 0 47 7 0\n55 -16 0 47 8 0\n56 -8 0 48 9 0\n57 12 0 52 39 51 45 18 0\n58 -4 0 55 16 14 0\n59 -1 0 56 15 0\n60 -14 0 57 6 0\n61 10 0 58 38 49 54 17 0\n62 0 61 59 50 53 60 13 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record001.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record001.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record001.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record001.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record001 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record001.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record001.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record001.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record001.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record001 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record001_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record001 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record001_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record001_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00011.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00011.record005
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "dc3a83e3a4cd2b4e332cab1ac2f362d4b329c972ca96a1eb16a5956c3a8e5389e17ab13c5693a4d92e479a96958d4b55352d2b49d1743d58e938cc7352d2b1ac9b16c3ba1d4785c9715d0f23c4f07eb05a29452b068590e2c4712a4692548d14c4b05c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6db69b6db6db69a4d34da49349a69b49b6da4d34db492491249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record005 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record005 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record005.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record005.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record005.data.quota

def groupMembers1 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 0)]))
 (.leaf ([(facetIndex 1)])))
 (.branch 3
 (.leaf ([(facetIndex 2)]))
 (.leaf ([(facetIndex 3)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 4)]))
 (.leaf ([(facetIndex 5)])))
 (.branch 7
 (.leaf ([(facetIndex 6)]))
 (.leaf ([(facetIndex 7)])))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ([(facetIndex 8)]))
 (.leaf ([(facetIndex 9)])))
 (.branch 11
 (.leaf ([(facetIndex 10)]))
 (.leaf ([(facetIndex 11)]))))
 (.branch 14
 (.branch 13
 (.leaf ([(facetIndex 12)]))
 (.leaf ([(facetIndex 13)])))
 (.branch 15
 (.leaf ([(facetIndex 14)]))
 (.branch 16
 (.leaf ([(facetIndex 15)]))
 (.leaf ([(facetIndex 16)])))))))
def groupColors1 : PackedGraphCertificate.Fields :=
  ⟨5, sparse_nat% "107b9ac5a928398a418820"⟩
def grouping1 : FacetSat.Grouping data.count where
  count := 17
  members := fun g => groupMembers1.get g
  color := fun c => groupColors1.get c.val
def groupKind1 : List Nat := List.range grouping1.count

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 57), (facetIndex 60)]))
 (.leaf ([(facetIndex 29), (facetIndex 31), (facetIndex 50), (facetIndex 62)])))
 (.branch 3
 (.leaf ([(facetIndex 42), (facetIndex 44), (facetIndex 52), (facetIndex 74)]))
 (.leaf ([(facetIndex 46), (facetIndex 47), (facetIndex 49), (facetIndex 51)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 19), (facetIndex 38), (facetIndex 39)]))
 (.leaf ([(facetIndex 21), (facetIndex 27), (facetIndex 32)])))
 (.branch 7
 (.leaf ([(facetIndex 18), (facetIndex 20), (facetIndex 55)]))
 (.branch 8
 (.leaf ([(facetIndex 22), (facetIndex 23), (facetIndex 59)]))
 (.leaf ([(facetIndex 17)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "2000000000001007000600231303302020044000005101050007756468z11;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ([(facetIndex 24), (facetIndex 30), (facetIndex 40)]))
 (.branch 2
 (.leaf ([(facetIndex 25), (facetIndex 33), (facetIndex 43)]))
 (.leaf ([(facetIndex 34), (facetIndex 45)]))))
 (.branch 4
 (.leaf ([(facetIndex 35), (facetIndex 41)]))
 (.branch 5
 (.leaf ([(facetIndex 64), (facetIndex 65), (facetIndex 67)]))
 (.leaf ([(facetIndex 70), (facetIndex 71), (facetIndex 73)])))))
 (.branch 9
 (.branch 7
 (.leaf ([(facetIndex 72), (facetIndex 76), (facetIndex 78)]))
 (.branch 8
 (.leaf ([(facetIndex 66), (facetIndex 68), (facetIndex 79)]))
 (.leaf ([(facetIndex 26), (facetIndex 28), (facetIndex 36), (facetIndex 37), (facetIndex 48)]))))
 (.branch 10
 (.leaf ([(facetIndex 53), (facetIndex 54), (facetIndex 61), (facetIndex 69), (facetIndex 77)]))
 (.branch 11
 (.leaf ([(facetIndex 58), (facetIndex 75)]))
 (.leaf ([(facetIndex 56), (facetIndex 63)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "7696a05655974744b0900a0b0990000800201030008832100008081z19;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 12
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped1_0000 : List Nat := [0]
def grouped1_0001 : List Nat := [0, 1]
def grouped1_0002 : List Nat := [0, 1, 2, 3]
def grouped1_0003 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7]
def grouped1_0005 : List Nat := [1]
def grouped1_0006 : List Nat := [2]
def grouped1_0007 : List Nat := [2, 3]
def grouped1_0008 : List Nat := [3]
def grouped1_0009 : List Nat := [4]
def grouped1_0010 : List Nat := [4, 5]
def grouped1_0011 : List Nat := [4, 5, 6, 7]
def grouped1_0012 : List Nat := [5]
def grouped1_0013 : List Nat := [6, 7]
def grouped1_0014 : List Nat := [8, 9, 10, 11]
def grouped1_0015 : List Nat := [8, 9, 10, 11, 12, 13, 14, 15, 16]
def grouped1_0016 : List Nat := [12]
def grouped1_0017 : List Nat := [12, 13]
def grouped1_0018 : List Nat := [12, 13, 14, 15, 16]
def grouped1_0019 : List Nat := [13]
def grouped1_0020 : List Nat := [14]
def grouped1_0021 : List Nat := [14, 15, 16]
def grouped1_0022 : List Nat := [15]
def grouped1_0023 : List Nat := [15, 16]
def grouped1_0024 : List Nat := [16]
def grouped2_0025 : List Nat := [0]
def grouped2_0026 : List Nat := [0, 1]
def grouped2_0027 : List Nat := [0, 1, 2, 3]
def grouped2_0029 : List Nat := [1]
def grouped2_0030 : List Nat := [2]
def grouped2_0031 : List Nat := [2, 3]
def grouped2_0032 : List Nat := [3]
def grouped2_0033 : List Nat := [4]
def grouped2_0034 : List Nat := [4, 5]
def grouped2_0035 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0036 : List Nat := [5]
def grouped2_0037 : List Nat := [6]
def grouped2_0038 : List Nat := [6, 7, 8]
def grouped2_0039 : List Nat := [7]
def grouped2_0040 : List Nat := [7, 8]
def grouped2_0041 : List Nat := [8]
def grouped3_0042 : List Nat := [0]
def grouped3_0043 : List Nat := [0, 1, 2]
def grouped3_0044 : List Nat := [0, 1, 2, 3, 4, 5]
def grouped3_0046 : List Nat := [1]
def grouped3_0047 : List Nat := [1, 2]
def grouped3_0048 : List Nat := [2]
def grouped3_0049 : List Nat := [3]
def grouped3_0050 : List Nat := [3, 4, 5]
def grouped3_0051 : List Nat := [4]
def grouped3_0052 : List Nat := [4, 5]
def grouped3_0053 : List Nat := [5]
def grouped3_0054 : List Nat := [6]
def grouped3_0055 : List Nat := [6, 7, 8]
def grouped3_0056 : List Nat := [6, 7, 8, 9, 10, 11]
def grouped3_0057 : List Nat := [7]
def grouped3_0058 : List Nat := [7, 8]
def grouped3_0059 : List Nat := [8]
def grouped3_0060 : List Nat := [9]
def grouped3_0061 : List Nat := [9, 10, 11]
def grouped3_0062 : List Nat := [10]
def grouped3_0063 : List Nat := [10, 11]
def grouped3_0064 : List Nat := [11]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record005 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record005_matrix_checked

def leafCount : Nat := 27
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaf0000 : List (Fin data.count) := [(facetIndex 2), (facetIndex 8), (facetIndex 12), (facetIndex 20), (facetIndex 21), (facetIndex 38), (facetIndex 49), (facetIndex 52), (facetIndex 59), (facetIndex 62), (facetIndex 67), (facetIndex 71), (facetIndex 72), (facetIndex 79)]
theorem leaf0000_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0000 = true := by
  decide +kernel
theorem leaf0000_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0000 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0000_counts_checked
def leaf0001 : List (Fin data.count) := [(facetIndex 2), (facetIndex 5), (facetIndex 12), (facetIndex 19), (facetIndex 23), (facetIndex 32), (facetIndex 47), (facetIndex 50), (facetIndex 55), (facetIndex 67), (facetIndex 73), (facetIndex 74), (facetIndex 78), (facetIndex 79)]
theorem leaf0001_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0001 = true := by
  decide +kernel
theorem leaf0001_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0001 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0001_counts_checked
def leaf0002 : List (Fin data.count) := [(facetIndex 2), (facetIndex 8), (facetIndex 12), (facetIndex 20), (facetIndex 21), (facetIndex 38), (facetIndex 49), (facetIndex 52), (facetIndex 59), (facetIndex 62), (facetIndex 67), (facetIndex 73), (facetIndex 78), (facetIndex 79)]
theorem leaf0002_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0002 = true := by
  decide +kernel
theorem leaf0002_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0002 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0002_counts_checked
def leaf0003 : List (Fin data.count) := [(facetIndex 2), (facetIndex 5), (facetIndex 12), (facetIndex 17), (facetIndex 32), (facetIndex 39), (facetIndex 50), (facetIndex 52), (facetIndex 55), (facetIndex 59), (facetIndex 67), (facetIndex 73), (facetIndex 78), (facetIndex 79)]
theorem leaf0003_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0003 = true := by
  decide +kernel
theorem leaf0003_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0003 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0003_counts_checked
def leaf0004 : List (Fin data.count) := [(facetIndex 2), (facetIndex 8), (facetIndex 12), (facetIndex 20), (facetIndex 21), (facetIndex 38), (facetIndex 49), (facetIndex 52), (facetIndex 59), (facetIndex 62), (facetIndex 67), (facetIndex 70), (facetIndex 76), (facetIndex 79)]
theorem leaf0004_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0004 = true := by
  decide +kernel
theorem leaf0004_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0004 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0004_counts_checked
def leaf0005 : List (Fin data.count) := [(facetIndex 0), (facetIndex 8), (facetIndex 14), (facetIndex 22), (facetIndex 27), (facetIndex 39), (facetIndex 50), (facetIndex 52), (facetIndex 55), (facetIndex 60), (facetIndex 65), (facetIndex 68), (facetIndex 73), (facetIndex 78)]
theorem leaf0005_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0005 = true := by
  decide +kernel
theorem leaf0005_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0005 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0005_counts_checked
def leaf0006 : List (Fin data.count) := [(facetIndex 0), (facetIndex 8), (facetIndex 15), (facetIndex 21), (facetIndex 31), (facetIndex 38), (facetIndex 49), (facetIndex 52), (facetIndex 57), (facetIndex 59), (facetIndex 64), (facetIndex 66), (facetIndex 70), (facetIndex 76)]
theorem leaf0006_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0006 = true := by
  decide +kernel
theorem leaf0006_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0006 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0006_counts_checked
def leaf0007 : List (Fin data.count) := [(facetIndex 0), (facetIndex 8), (facetIndex 15), (facetIndex 21), (facetIndex 31), (facetIndex 38), (facetIndex 49), (facetIndex 52), (facetIndex 57), (facetIndex 59), (facetIndex 65), (facetIndex 68), (facetIndex 70), (facetIndex 76)]
theorem leaf0007_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0007 = true := by
  decide +kernel
theorem leaf0007_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0007 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0007_counts_checked
def leaf0008 : List (Fin data.count) := [(facetIndex 0), (facetIndex 8), (facetIndex 15), (facetIndex 21), (facetIndex 31), (facetIndex 38), (facetIndex 49), (facetIndex 52), (facetIndex 57), (facetIndex 59), (facetIndex 67), (facetIndex 70), (facetIndex 76), (facetIndex 79)]
theorem leaf0008_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0008 = true := by
  decide +kernel
theorem leaf0008_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0008 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0008_counts_checked
def leaf0009 : List (Fin data.count) := [(facetIndex 0), (facetIndex 2), (facetIndex 8), (facetIndex 21), (facetIndex 38), (facetIndex 49), (facetIndex 52), (facetIndex 57), (facetIndex 59), (facetIndex 62), (facetIndex 67), (facetIndex 70), (facetIndex 76), (facetIndex 79)]
theorem leaf0009_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0009 = true := by
  decide +kernel
theorem leaf0009_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0009 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0009_counts_checked
def leaf0010 : List (Fin data.count) := [(facetIndex 0), (facetIndex 4), (facetIndex 7), (facetIndex 22), (facetIndex 27), (facetIndex 50), (facetIndex 51), (facetIndex 55), (facetIndex 60), (facetIndex 65), (facetIndex 68), (facetIndex 73), (facetIndex 74), (facetIndex 78)]
theorem leaf0010_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0010 = true := by
  decide +kernel
theorem leaf0010_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0010 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0010_counts_checked
def leaf0011 : List (Fin data.count) := [(facetIndex 0), (facetIndex 14), (facetIndex 16), (facetIndex 22), (facetIndex 27), (facetIndex 39), (facetIndex 50), (facetIndex 51), (facetIndex 55), (facetIndex 60), (facetIndex 65), (facetIndex 68), (facetIndex 73), (facetIndex 78)]
theorem leaf0011_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0011 = true := by
  decide +kernel
theorem leaf0011_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0011 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0011_counts_checked
def leaf0012 : List (Fin data.count) := [(facetIndex 2), (facetIndex 3), (facetIndex 16), (facetIndex 17), (facetIndex 39), (facetIndex 44), (facetIndex 50), (facetIndex 51), (facetIndex 55), (facetIndex 60), (facetIndex 65), (facetIndex 68), (facetIndex 73), (facetIndex 78)]
theorem leaf0012_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0012 = true := by
  decide +kernel
theorem leaf0012_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0012 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0012_counts_checked
def leaf0013 : List (Fin data.count) := [(facetIndex 0), (facetIndex 1), (facetIndex 15), (facetIndex 31), (facetIndex 32), (facetIndex 38), (facetIndex 49), (facetIndex 52), (facetIndex 57), (facetIndex 59), (facetIndex 67), (facetIndex 70), (facetIndex 76), (facetIndex 79)]
theorem leaf0013_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0013 = true := by
  decide +kernel
theorem leaf0013_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0013 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0013_counts_checked
def leaf0014 : List (Fin data.count) := [(facetIndex 5), (facetIndex 7), (facetIndex 12), (facetIndex 19), (facetIndex 23), (facetIndex 27), (facetIndex 50), (facetIndex 51), (facetIndex 55), (facetIndex 64), (facetIndex 66), (facetIndex 73), (facetIndex 74), (facetIndex 78)]
theorem leaf0014_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0014 = true := by
  decide +kernel
theorem leaf0014_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0014 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0014_counts_checked
def leaf0015 : List (Fin data.count) := [(facetIndex 2), (facetIndex 5), (facetIndex 12), (facetIndex 20), (facetIndex 21), (facetIndex 39), (facetIndex 46), (facetIndex 52), (facetIndex 59), (facetIndex 62), (facetIndex 67), (facetIndex 73), (facetIndex 78), (facetIndex 79)]
theorem leaf0015_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0015 = true := by
  decide +kernel
theorem leaf0015_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0015 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0015_counts_checked
def leaf0016 : List (Fin data.count) := [(facetIndex 5), (facetIndex 7), (facetIndex 12), (facetIndex 19), (facetIndex 23), (facetIndex 27), (facetIndex 50), (facetIndex 51), (facetIndex 55), (facetIndex 67), (facetIndex 73), (facetIndex 74), (facetIndex 78), (facetIndex 79)]
theorem leaf0016_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0016 = true := by
  decide +kernel
theorem leaf0016_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0016 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0016_counts_checked
def leaf0017 : List (Fin data.count) := [(facetIndex 5), (facetIndex 7), (facetIndex 12), (facetIndex 19), (facetIndex 23), (facetIndex 27), (facetIndex 50), (facetIndex 51), (facetIndex 55), (facetIndex 65), (facetIndex 68), (facetIndex 73), (facetIndex 74), (facetIndex 78)]
theorem leaf0017_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0017 = true := by
  decide +kernel
theorem leaf0017_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0017 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0017_counts_checked
def leaf0018 : List (Fin data.count) := [(facetIndex 1), (facetIndex 7), (facetIndex 13), (facetIndex 18), (facetIndex 32), (facetIndex 38), (facetIndex 50), (facetIndex 52), (facetIndex 57), (facetIndex 59), (facetIndex 67), (facetIndex 70), (facetIndex 76), (facetIndex 79)]
theorem leaf0018_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0018 = true := by
  decide +kernel
theorem leaf0018_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0018 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0018_counts_checked
def leaf0019 : List (Fin data.count) := [(facetIndex 1), (facetIndex 7), (facetIndex 16), (facetIndex 19), (facetIndex 27), (facetIndex 44), (facetIndex 50), (facetIndex 51), (facetIndex 55), (facetIndex 60), (facetIndex 65), (facetIndex 68), (facetIndex 71), (facetIndex 72)]
theorem leaf0019_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0019 = true := by
  decide +kernel
theorem leaf0019_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0019 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0019_counts_checked
def leaf0020 : List (Fin data.count) := [(facetIndex 1), (facetIndex 7), (facetIndex 16), (facetIndex 19), (facetIndex 27), (facetIndex 44), (facetIndex 50), (facetIndex 51), (facetIndex 55), (facetIndex 60), (facetIndex 65), (facetIndex 68), (facetIndex 70), (facetIndex 76)]
theorem leaf0020_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0020 = true := by
  decide +kernel
theorem leaf0020_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0020 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0020_counts_checked
def leaf0021 : List (Fin data.count) := [(facetIndex 1), (facetIndex 7), (facetIndex 16), (facetIndex 19), (facetIndex 27), (facetIndex 44), (facetIndex 50), (facetIndex 51), (facetIndex 55), (facetIndex 60), (facetIndex 65), (facetIndex 68), (facetIndex 73), (facetIndex 78)]
theorem leaf0021_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0021 = true := by
  decide +kernel
theorem leaf0021_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0021 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0021_counts_checked
def leaf0022 : List (Fin data.count) := [(facetIndex 1), (facetIndex 5), (facetIndex 7), (facetIndex 19), (facetIndex 27), (facetIndex 50), (facetIndex 51), (facetIndex 55), (facetIndex 60), (facetIndex 65), (facetIndex 68), (facetIndex 73), (facetIndex 74), (facetIndex 78)]
theorem leaf0022_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0022 = true := by
  decide +kernel
theorem leaf0022_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0022 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0022_counts_checked
def leaf0023 : List (Fin data.count) := [(facetIndex 1), (facetIndex 3), (facetIndex 8), (facetIndex 18), (facetIndex 38), (facetIndex 49), (facetIndex 52), (facetIndex 57), (facetIndex 59), (facetIndex 62), (facetIndex 67), (facetIndex 70), (facetIndex 76), (facetIndex 79)]
theorem leaf0023_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0023 = true := by
  decide +kernel
theorem leaf0023_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0023 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0023_counts_checked
def leaf0024 : List (Fin data.count) := [(facetIndex 1), (facetIndex 13), (facetIndex 15), (facetIndex 18), (facetIndex 32), (facetIndex 38), (facetIndex 49), (facetIndex 52), (facetIndex 57), (facetIndex 59), (facetIndex 67), (facetIndex 70), (facetIndex 76), (facetIndex 79)]
theorem leaf0024_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0024 = true := by
  decide +kernel
theorem leaf0024_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0024 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0024_counts_checked
def leaf0025 : List (Fin data.count) := [(facetIndex 4), (facetIndex 5), (facetIndex 15), (facetIndex 17), (facetIndex 31), (facetIndex 32), (facetIndex 49), (facetIndex 52), (facetIndex 57), (facetIndex 59), (facetIndex 67), (facetIndex 70), (facetIndex 76), (facetIndex 79)]
theorem leaf0025_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0025 = true := by
  decide +kernel
theorem leaf0025_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0025 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0025_counts_checked
def leaf0026 : List (Fin data.count) := [(facetIndex 0), (facetIndex 1), (facetIndex 16), (facetIndex 27), (facetIndex 39), (facetIndex 44), (facetIndex 50), (facetIndex 51), (facetIndex 55), (facetIndex 60), (facetIndex 65), (facetIndex 68), (facetIndex 73), (facetIndex 78)]
theorem leaf0026_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0026 = true := by
  decide +kernel
theorem leaf0026_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0026 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0026_counts_checked
def leavesTable : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf (leaf0000))
 (.branch 2
 (.leaf (leaf0001))
 (.leaf (leaf0002))))
 (.branch 4
 (.leaf (leaf0003))
 (.branch 5
 (.leaf (leaf0004))
 (.leaf (leaf0005)))))
 (.branch 9
 (.branch 7
 (.leaf (leaf0006))
 (.branch 8
 (.leaf (leaf0007))
 (.leaf (leaf0008))))
 (.branch 11
 (.branch 10
 (.leaf (leaf0009))
 (.leaf (leaf0010)))
 (.branch 12
 (.leaf (leaf0011))
 (.leaf (leaf0012))))))
 (.branch 20
 (.branch 16
 (.branch 14
 (.leaf (leaf0013))
 (.branch 15
 (.leaf (leaf0014))
 (.leaf (leaf0015))))
 (.branch 18
 (.branch 17
 (.leaf (leaf0016))
 (.leaf (leaf0017)))
 (.branch 19
 (.leaf (leaf0018))
 (.leaf (leaf0019)))))
 (.branch 23
 (.branch 21
 (.leaf (leaf0020))
 (.branch 22
 (.leaf (leaf0021))
 (.leaf (leaf0022))))
 (.branch 25
 (.branch 24
 (.leaf (leaf0023))
 (.leaf (leaf0024)))
 (.branch 26
 (.leaf (leaf0025))
 (.leaf (leaf0026)))))))
def leaves (j : Fin leafCount) : List (Fin data.count) := leavesTable.get j.val

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00011.record005" "{\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"group\",\"kind\":1,\"index\":0},{\"tag\":\"group\",\"kind\":1,\"index\":2},{\"tag\":\"group\",\"kind\":1,\"index\":3},{\"tag\":\"group\",\"kind\":1,\"index\":5},{\"tag\":\"group\",\"kind\":1,\"index\":12},{\"tag\":\"group\",\"kind\":1,\"index\":15},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0001\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0007\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0002\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0002\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0010\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0011\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0003\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0003\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0017\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0023\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0021\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0018\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0018\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0015\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0015\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":4,\"list_name\":\"groupKind1\"},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0026\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0026\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0031\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0031\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0027\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0027\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0027\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0034\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0034\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0040\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0040\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0038\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0038\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0038\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0035\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0035\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0035\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group\",\"kind\":3,\"index\":10},{\"tag\":\"group\",\"kind\":3,\"index\":11},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0047\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0043\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0052\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0052\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0050\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0050\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0050\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0044\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0044\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0058\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0058\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0055\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0055\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0063\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0061\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0061\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0056\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0056\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":4,\"list_name\":\"grouped3_0056\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":4,\"list_name\":\"groupKind3\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":5,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00011.record005" 158

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00011.record005" "{\"ridges\":[[4,140],[7,168],[8,97],[12,770],[13,322],[15,352],[17,11],[17,13],[18,7],[18,67],[19,140],[20,11],[22,7],[22,133],[22,148],[23,21],[24,325],[25,643],[26,58],[27,11],[27,19],[27,81],[28,154],[29,74],[29,104],[32,19],[32,67],[32,82],[32,112],[33,547],[34,643],[35,97],[35,291],[36,60],[37,92],[38,137],[38,140],[39,140],[39,168],[40,293],[41,325],[43,549],[46,73],[47,168],[48,216],[49,97],[49,104],[49,168],[50,41],[51,176],[52,49],[53,92],[54,154],[55,14],[55,74],[55,262],[55,322],[56,650],[57,14],[57,266],[57,268],[57,772],[58,340],[59,148],[59,644],[60,22],[60,530],[60,770],[61,58],[62,74],[62,352],[63,554],[64,82],[65,82],[65,560],[66,306],[66,800],[67,770],[67,848],[68,610],[68,800],[69,60],[70,420],[71,556],[71,672],[72,556],[72,800],[73,772],[73,904],[74,148],[74,644],[74,672],[75,308],[76,420],[76,800],[77,216],[78,296],[78,800],[78,904],[79,112],[79,800],[79,848]],\"owners\":[[18,7,[1,22,23,25],[0,19,20,21,24]],[22,7,[0,18,20,24],[1,19,21,23,25]],[17,11,[2,29,30,31],[0,19,20,26,27,28]],[20,11,[2,26,27,28,29],[0,17,19,30,31]],[27,11,[0,19,20,30],[2,17,26,28,29,31]],[17,13,[4,39,40,41],[0,18,20,36,37,38]],[55,14,[0,17,19,54,56],[10,18,53,57]],[57,14,[0,17,18,19,53,54],[10,55,56]],[27,19,[1,22,23,33,34],[3,17,26,28,32]],[32,19,[1,17,22,23,28,34],[3,26,27,33]],[23,21,[5,36,37,38,42],[1,17,21,43,44]],[60,22,[1,17,21,22,53,54],[11,58,59]],[18,67,[3,32,35],[2,21,24,29,31]],[32,67,[2,18,24,31],[3,21,29,35]],[46,73,[2,18,31,41],[6,27,37,48,49,50]],[29,74,[13,53,55],[2,18,27,61,62]],[55,74,[2,27,29,61],[13,18,53,62]],[62,74,[2,18,27,53],[13,29,55,61]],[27,81,[8,51],[3,21,37,46,48]],[32,82,[53,58,67],[3,21,27,61,64,65]],[64,82,[3,21,27,53],[32,58,61,65,67]],[65,82,[3,21,27,53,58],[32,61,64,67]],[22,133,[4,39,45],[5,19,25,42,44]],[38,137,[7,49],[4,19,28,47,48]],[4,140,[54,56,69,70,71,73],[19,38,39]],[19,140,[69,70,71,73],[4,38,39,54,56]],[38,140,[56,70,71,73],[4,19,39,54,69]],[39,140,[54,56,73],[4,19,38,69,70,71]],[22,148,[14,69,74],[5,38,42,54,59]],[59,148,[5,38,42,69],[14,22,54,74]],[74,148,[5,22,38,54],[14,42,59,69]],[50,41,[7,26,36,39,47],[6,29,30,40,46]],[29,104,[15,77],[6,46,49,61,62]],[49,104,[15,61,62],[6,29,46,77]],[7,168,[69,70,71,77,78],[39,47,49]],[39,168,[77,78],[7,47,49,69,70,71]],[47,168,[70,71,78],[7,39,49,69,77]],[49,168,[69,70,71,78],[7,39,47,77]],[52,49,[8,26,32,36,46],[9,33,42,43,47]],[32,112,[77,79],[8,46,51,61,64,65]],[79,112,[8,32,46,51,61,77],[64,65]],[51,176,[16,69,74],[9,42,47,77]],[55,262,[12,60],[10,20,24,58]],[57,266,[13,30,31,62],[10,20,63]],[57,268,[40,41,70],[10,20,55,72,73]],[60,530,[33,34,65],[11,23,59,66,67]],[12,770,[63,66,67,68],[57,60]],[60,770,[63,68],[12,57,66,67]],[67,770,[12,57,63],[60,66,68]],[57,772,[75,76],[12,60,72,73]],[73,772,[12,60,75],[57,72,76]],[13,322,[24,35,58,64,67,68],[31,55,62]],[55,322,[35,64,67,68],[13,24,31,58,62]],[59,644,[45,71,73,76],[14,25,44,56,74]],[74,644,[25,56,73],[14,44,45,59,71,76]],[78,296,[15,30,40,50,62],[63,70,72]],[15,352,[35,64,68,79],[50,62]],[62,352,[79],[15,35,50,64,68]],[65,560,[16,43,52,74,75],[33,66,79]],[71,672,[16,52],[45,74,76,78]],[74,672,[78],[16,45,52,71,76]],[24,325,[41],[]],[41,325,[24],[]],[25,643,[34],[]],[34,643,[25],[]],[26,58,[61],[]],[61,58,[26],[]],[28,154,[54],[]],[54,154,[28],[]],[35,291,[30],[]],[33,547,[],[]],[36,60,[69],[]],[69,60,[36],[]],[37,92,[53],[]],[53,92,[37],[]],[40,293,[],[]],[43,549,[45],[]],[48,216,[77],[]],[77,216,[48],[]],[56,650,[],[]],[58,340,[],[]],[63,554,[],[]],[66,800,[72,76,78],[63,68,75,79]],[68,800,[72,75,76,78],[63,66,79]],[72,800,[66,68,79],[63,75,76,78]],[76,800,[63,66,68,79],[72,75,78]],[78,800,[66,68,75,79],[63,72,76]],[79,800,[63,72,76,78],[66,68,75]],[66,306,[64],[]],[68,610,[65],[]],[67,848,[79],[]],[79,848,[67],[]],[70,420,[76],[]],[76,420,[70],[]],[71,556,[72],[]],[72,556,[71],[]],[73,904,[78],[]],[78,904,[73],[]],[75,308,[],[]]],\"edges\":[[27,[4,7,19,28,38,39,47,48,49,54,56,69,70,71,73,77,78]],[44,[12,57,60,63,66,67,68,72,73,75,76,78,79]]],\"groupings\":[1,2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00011.record005" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00011.record005\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-15,-3],[-15,-14],[-16,-14],[-16,-15],[-17,-14],[-17,-16],[-18,-14],[-18,-15],[-19,-14],[-19,-16],[-19,-18],[-20,-14],[-20,-18],[-21,-14],[-21,-18],[-22,-16],[-22,-19],[-24,-14],[-24,-15],[-24,-21],[-26,-15],[-26,-24],[-27,-15],[-27,-17],[-28,-15],[-28,-17],[-28,-24],[-29,-24],[-29,-26],[-29,-27],[-31,-18],[-31,-19],[-32,-17],[-32,-24],[-32,-26],[-32,-29],[-33,-19],[-34,-19],[-35,-14],[-35,-16],[-35,-19],[-35,-22],[-35,-23],[-35,-24],[-35,-25],[-35,-33],[-35,-34],[-36,-16],[-36,-25],[-36,-33],[-36,-35],[-38,-16],[-38,-18],[-38,-26],[-39,-19],[-39,-35],[-39,-36],[-40,-36],[-41,-19],[-41,-20],[-41,-22],[-41,-35],[-42,-35],[-42,-36],[-43,-14],[-43,-24],[-43,-26],[-43,-29],[-43,-35],[-44,-14],[-44,-24],[-44,-35],[-44,-36],[-44,-39],[-45,-35],[-45,-36],[-46,-23],[-46,-26],[-46,-27],[-46,-36],[-47,-12],[-47,-17],[-47,-43],[-47,-46],[-48,-23],[-48,-29],[-48,-39],[-48,-43],[-48,-46],[-49,-20],[-49,-22],[-49,-44],[-49,-48],[-50,-14],[-50,-35],[-51,-19],[-51,-35],[-52,-18],[-52,-28],[-54,-17],[-54,-21],[-54,-52],[-56,-16],[-56,-41],[-57,-20],[-57,-56],[-58,-14],[-58,-35],[-58,-44],[-59,-29],[-59,-52],[-61,-26],[-62,-58],[-63,-26],[-63,-27],[-65,-26],[-65,-27],[-65,-29],[-65,-59],[-66,-14],[-66,-35],[-66,-36],[-67,-36],[-67,-39],[-68,-54],[-69,-39],[-70,-54],[-71,-31],[-71,-36],[-71,-42],[-71,-56],[-71,-67],[-73,-36],[-73,-39],[-73,-40],[-74,-14],[-74,-35],[-74,-44],[-74,-46],[-74,-48],[-75,-54],[-76,-57],[-15,2,19,20,22],[-19,1,15,17,21],[-14,3,26,27,28],[-17,3,23,24,25,26],[-24,1,16,17,27],[-14,5,36,37,38],[-52,1,14,16,51,53],[-54,1,14,15,16,50,51],[-24,2,19,20,30,31],[-29,2,14,19,20,25,31],[-20,6,33,34,35,39],[-57,2,14,18,19,50,51],[-15,4,29,32],[-29,3,15,21,28],[-43,3,15,28,38],[-26,10,50,52],[-52,3,24,26,58],[-59,3,15,24,50],[-24,8,48],[-29,50,55,64],[-61,4,18,24,50],[-62,4,18,24,50,55],[-19,5,36,42],[-35,7,46],[-5,51,53,66,67,68,70],[-16,66,67,68,70],[-35,53,67,68,70],[-36,51,53,70],[-19,11,66,71],[-56,6,35,39,66],[-71,6,19,35,51],[-47,7,23,33,36,44],[-8,-32,-46],[-26,12,74],[-46,12,58,59],[-7,66,67,68,74,75],[-36,74,75],[-44,67,68,75],[-46,66,67,68,75],[-49,8,23,29,33,43],[-29,74,76],[-76,8,29,43,48,58,74],[-48,13,66,71],[-52,9,57],[-54,10,27,28,59],[-54,37,38,67],[-57,30,31,62],[-9,60,63,64,65],[-57,60,65],[-64,9,54,60],[-54,72,73],[-70,9,57,72],[-10,21,32,55,61,64,65],[-52,32,61,64,65],[-56,42,68,70,73],[-71,22,53,70],[-75,12,27,37,47,59],[-12,32,61,65,76],[-59,76],[-62,13,40,49,71,72],[-68,13,49],[-71,75],[-21,38],[-38,21],[-22,31],[-31,22],[-23,58],[-58,23],[-25,51],[-51,25],[-32,27],[-30],[-33,66],[-66,33],[-34,50],[-50,34],[-37],[-40,42],[-45,74],[-74,45],[-53],[-55],[-60],[-63,69,73,75],[-65,69,72,73,75],[-69,63,65,76],[-73,60,63,65,76],[-75,63,65,72,76],[-76,60,69,73,75],[-63,61],[-65,62],[-64,76],[-76,64],[-67,73],[-73,67],[-68,69],[-69,68],[-70,75],[-75,70],[-72],[-1,77],[-78,3],[-3,78],[-4,79],[-6,80],[-9,81],[-12,82],[-77,83],[-84,78],[-78,-79,84],[-84,85],[-83,-84,86],[-80,87],[-87,88],[-85,89],[-85,-88,90],[-86,90],[-81,91],[-82,92],[-92,93],[-91,94],[-91,-93,95],[-94,96],[-95,97],[-89,-97,98],[-90,-96,98],[-98],[-99,54,57],[-54,99],[-100,26,28,47,59],[-47,100],[-101,39,41,49,71],[-102,43,44,46,48],[-48,102],[-103,16,35,36],[-35,103],[-104,18,24,29],[-18,104],[-29,104],[-105,15,17,52],[-15,105],[-106,19,20,56],[-19,106],[-107,14],[-14,107],[-108,99,100],[-109,99],[-109,100],[-110,101,102],[-111,101],[-111,102],[-112,108,111],[-113,108],[-112,109,110],[-113,109,111],[-114,109],[-113,110],[-114,111],[-115,103,104],[-116,103],[-103,115],[-116,104],[-103,-104,116],[-117,106,107],[-107,117],[-118,106],[-118,107],[-119,105,117],[-120,105,118],[-121,105],[-120,117],[-121,118],[-122,115,121],[-123,115],[-122,116,120],[-123,116,121],[-124,116],[-122,119],[-123,120],[-124,121],[-125,112],[-125,113,124],[-125,114,123],[-125,122],[125],[-126,21,27,37],[-127,22,30,40],[-40,127],[-128,31,42],[-31,128],[-129,32,38],[-38,129],[-61,130],[-62,130],[-67,131],[-68,131],[-70,131],[-132,69,73,75],[-69,132],[-73,132],[-75,132],[-133,63,65,76],[-63,133],[-65,133],[-76,133],[-134,23,25,33,34,45],[-23,134],[-25,134],[-33,134],[-34,134],[-45,134],[-135,50,51,58,66,74],[-50,135],[-51,135],[-58,135],[-66,135],[-74,135],[-136,55,72],[-137,53,60],[-138,127,128],[-128,138],[-127,138],[-139,126,138],[-138,139],[-131,140],[-130,-131,141],[-140,142],[-141,143],[-144,129],[-129,-141,144],[-142,145],[-146,139,144],[-144,146],[-139,-143,146],[-147,133,134],[-134,147],[-148,133],[-133,147],[-148,134],[-133,-134,148],[-149,132,148],[-150,132],[-149,147],[-132,-147,149],[-150,148],[-132,-148,150],[-151,136,137],[-152,135,151],[-135,152],[-153,151],[-154,149,152],[-155,149,153],[-149,154],[-155,150,152],[-149,-152,155],[-156,150,153],[-150,155],[-150,-152,156],[-145,-156,158],[-157,146,154],[-146,-154,158],[157],[-158],[-3,-8,-9,-17,-18,-35,-46,-49,-56,-59,-64,-68,-69,-76],[-3,-6,-9,-16,-20,-29,-44,-47,-52,-64,-70,-71,-75,-76],[-3,-8,-9,-17,-18,-35,-46,-49,-56,-59,-64,-70,-75,-76],[-3,-6,-9,-14,-29,-36,-47,-49,-52,-56,-64,-70,-75,-76],[-3,-8,-9,-17,-18,-35,-46,-49,-56,-59,-64,-67,-73,-76],[-1,-8,-11,-19,-24,-36,-47,-49,-52,-57,-62,-65,-70,-75],[-1,-8,-12,-18,-28,-35,-46,-49,-54,-56,-61,-63,-67,-73],[-1,-8,-12,-18,-28,-35,-46,-49,-54,-56,-62,-65,-67,-73],[-1,-8,-12,-18,-28,-35,-46,-49,-54,-56,-64,-67,-73,-76],[-1,-3,-8,-18,-35,-46,-49,-54,-56,-59,-64,-67,-73,-76],[-1,-5,-7,-19,-24,-47,-48,-52,-57,-62,-65,-70,-71,-75],[-1,-11,-13,-19,-24,-36,-47,-48,-52,-57,-62,-65,-70,-75],[-3,-4,-13,-14,-36,-41,-47,-48,-52,-57,-62,-65,-70,-75],[-1,-2,-12,-28,-29,-35,-46,-49,-54,-56,-64,-67,-73,-76],[-6,-7,-9,-16,-20,-24,-47,-48,-52,-61,-63,-70,-71,-75],[-3,-6,-9,-17,-18,-36,-43,-49,-56,-59,-64,-70,-75,-76],[-6,-7,-9,-16,-20,-24,-47,-48,-52,-64,-70,-71,-75,-76],[-6,-7,-9,-16,-20,-24,-47,-48,-52,-62,-65,-70,-71,-75],[-2,-7,-10,-15,-29,-35,-47,-49,-54,-56,-64,-67,-73,-76],[-2,-7,-13,-16,-24,-41,-47,-48,-52,-57,-62,-65,-68,-69],[-2,-7,-13,-16,-24,-41,-47,-48,-52,-57,-62,-65,-67,-73],[-2,-7,-13,-16,-24,-41,-47,-48,-52,-57,-62,-65,-70,-75],[-2,-6,-7,-16,-24,-47,-48,-52,-57,-62,-65,-70,-71,-75],[-2,-4,-8,-15,-35,-46,-49,-54,-56,-59,-64,-67,-73,-76],[-2,-10,-12,-15,-29,-35,-46,-49,-54,-56,-64,-67,-73,-76],[-5,-6,-12,-14,-28,-29,-46,-49,-54,-56,-64,-67,-73,-76],[-1,-2,-13,-24,-36,-41,-47,-48,-52,-57,-62,-65,-70,-75],[5,7,16,25,35,36,44,45,46,51,53,66,67,68,70,74,75],[9,54,57,60,63,64,65,69,70,72,73,75,76]],\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"group\",\"index\":0,\"kind\":1},{\"tag\":\"group\",\"index\":2,\"kind\":1},{\"tag\":\"group\",\"index\":3,\"kind\":1},{\"tag\":\"group\",\"index\":5,\"kind\":1},{\"tag\":\"group\",\"index\":12,\"kind\":1},{\"tag\":\"group\",\"index\":15,\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group\",\"index\":10,\"kind\":3},{\"tag\":\"group\",\"index\":11,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":18,\"b\":2},{\"tag\":\"incompatible\",\"a\":18,\"b\":17},{\"tag\":\"incompatible\",\"a\":19,\"b\":17},{\"tag\":\"incompatible\",\"a\":19,\"b\":18},{\"tag\":\"incompatible\",\"a\":20,\"b\":17},{\"tag\":\"incompatible\",\"a\":20,\"b\":19},{\"tag\":\"incompatible\",\"a\":21,\"b\":17},{\"tag\":\"incompatible\",\"a\":21,\"b\":18},{\"tag\":\"incompatible\",\"a\":22,\"b\":17},{\"tag\":\"incompatible\",\"a\":22,\"b\":19},{\"tag\":\"incompatible\",\"a\":22,\"b\":21},{\"tag\":\"incompatible\",\"a\":23,\"b\":17},{\"tag\":\"incompatible\",\"a\":23,\"b\":21},{\"tag\":\"incompatible\",\"a\":24,\"b\":17},{\"tag\":\"incompatible\",\"a\":24,\"b\":21},{\"tag\":\"incompatible\",\"a\":25,\"b\":19},{\"tag\":\"incompatible\",\"a\":25,\"b\":22},{\"tag\":\"incompatible\",\"a\":27,\"b\":17},{\"tag\":\"incompatible\",\"a\":27,\"b\":18},{\"tag\":\"incompatible\",\"a\":27,\"b\":24},{\"tag\":\"incompatible\",\"a\":29,\"b\":18},{\"tag\":\"incompatible\",\"a\":29,\"b\":27},{\"tag\":\"incompatible\",\"a\":30,\"b\":18},{\"tag\":\"incompatible\",\"a\":30,\"b\":20},{\"tag\":\"incompatible\",\"a\":31,\"b\":18},{\"tag\":\"incompatible\",\"a\":31,\"b\":20},{\"tag\":\"incompatible\",\"a\":31,\"b\":27},{\"tag\":\"incompatible\",\"a\":32,\"b\":27},{\"tag\":\"incompatible\",\"a\":32,\"b\":29},{\"tag\":\"incompatible\",\"a\":32,\"b\":30},{\"tag\":\"incompatible\",\"a\":34,\"b\":21},{\"tag\":\"incompatible\",\"a\":34,\"b\":22},{\"tag\":\"incompatible\",\"a\":35,\"b\":20},{\"tag\":\"incompatible\",\"a\":35,\"b\":27},{\"tag\":\"incompatible\",\"a\":35,\"b\":29},{\"tag\":\"incompatible\",\"a\":35,\"b\":32},{\"tag\":\"incompatible\",\"a\":36,\"b\":22},{\"tag\":\"incompatible\",\"a\":37,\"b\":22},{\"tag\":\"incompatible\",\"a\":38,\"b\":17},{\"tag\":\"incompatible\",\"a\":38,\"b\":19},{\"tag\":\"incompatible\",\"a\":38,\"b\":22},{\"tag\":\"incompatible\",\"a\":38,\"b\":25},{\"tag\":\"incompatible\",\"a\":38,\"b\":26},{\"tag\":\"incompatible\",\"a\":38,\"b\":27},{\"tag\":\"incompatible\",\"a\":38,\"b\":28},{\"tag\":\"incompatible\",\"a\":38,\"b\":36},{\"tag\":\"incompatible\",\"a\":38,\"b\":37},{\"tag\":\"incompatible\",\"a\":39,\"b\":19},{\"tag\":\"incompatible\",\"a\":39,\"b\":28},{\"tag\":\"incompatible\",\"a\":39,\"b\":36},{\"tag\":\"incompatible\",\"a\":39,\"b\":38},{\"tag\":\"incompatible\",\"a\":41,\"b\":19},{\"tag\":\"incompatible\",\"a\":41,\"b\":21},{\"tag\":\"incompatible\",\"a\":41,\"b\":29},{\"tag\":\"incompatible\",\"a\":42,\"b\":22},{\"tag\":\"incompatible\",\"a\":42,\"b\":38},{\"tag\":\"incompatible\",\"a\":42,\"b\":39},{\"tag\":\"incompatible\",\"a\":43,\"b\":39},{\"tag\":\"incompatible\",\"a\":44,\"b\":22},{\"tag\":\"incompatible\",\"a\":44,\"b\":23},{\"tag\":\"incompatible\",\"a\":44,\"b\":25},{\"tag\":\"incompatible\",\"a\":44,\"b\":38},{\"tag\":\"incompatible\",\"a\":45,\"b\":38},{\"tag\":\"incompatible\",\"a\":45,\"b\":39},{\"tag\":\"incompatible\",\"a\":46,\"b\":17},{\"tag\":\"incompatible\",\"a\":46,\"b\":27},{\"tag\":\"incompatible\",\"a\":46,\"b\":29},{\"tag\":\"incompatible\",\"a\":46,\"b\":32},{\"tag\":\"incompatible\",\"a\":46,\"b\":38},{\"tag\":\"incompatible\",\"a\":47,\"b\":17},{\"tag\":\"incompatible\",\"a\":47,\"b\":27},{\"tag\":\"incompatible\",\"a\":47,\"b\":38},{\"tag\":\"incompatible\",\"a\":47,\"b\":39},{\"tag\":\"incompatible\",\"a\":47,\"b\":42},{\"tag\":\"incompatible\",\"a\":48,\"b\":38},{\"tag\":\"incompatible\",\"a\":48,\"b\":39},{\"tag\":\"incompatible\",\"a\":49,\"b\":26},{\"tag\":\"incompatible\",\"a\":49,\"b\":29},{\"tag\":\"incompatible\",\"a\":49,\"b\":30},{\"tag\":\"incompatible\",\"a\":49,\"b\":39},{\"tag\":\"incompatible\",\"a\":50,\"b\":15},{\"tag\":\"incompatible\",\"a\":50,\"b\":20},{\"tag\":\"incompatible\",\"a\":50,\"b\":46},{\"tag\":\"incompatible\",\"a\":50,\"b\":49},{\"tag\":\"incompatible\",\"a\":51,\"b\":26},{\"tag\":\"incompatible\",\"a\":51,\"b\":32},{\"tag\":\"incompatible\",\"a\":51,\"b\":42},{\"tag\":\"incompatible\",\"a\":51,\"b\":46},{\"tag\":\"incompatible\",\"a\":51,\"b\":49},{\"tag\":\"incompatible\",\"a\":52,\"b\":23},{\"tag\":\"incompatible\",\"a\":52,\"b\":25},{\"tag\":\"incompatible\",\"a\":52,\"b\":47},{\"tag\":\"incompatible\",\"a\":52,\"b\":51},{\"tag\":\"incompatible\",\"a\":53,\"b\":17},{\"tag\":\"incompatible\",\"a\":53,\"b\":38},{\"tag\":\"incompatible\",\"a\":54,\"b\":22},{\"tag\":\"incompatible\",\"a\":54,\"b\":38},{\"tag\":\"incompatible\",\"a\":55,\"b\":21},{\"tag\":\"incompatible\",\"a\":55,\"b\":31},{\"tag\":\"incompatible\",\"a\":57,\"b\":20},{\"tag\":\"incompatible\",\"a\":57,\"b\":24},{\"tag\":\"incompatible\",\"a\":57,\"b\":55},{\"tag\":\"incompatible\",\"a\":59,\"b\":19},{\"tag\":\"incompatible\",\"a\":59,\"b\":44},{\"tag\":\"incompatible\",\"a\":60,\"b\":23},{\"tag\":\"incompatible\",\"a\":60,\"b\":59},{\"tag\":\"incompatible\",\"a\":61,\"b\":17},{\"tag\":\"incompatible\",\"a\":61,\"b\":38},{\"tag\":\"incompatible\",\"a\":61,\"b\":47},{\"tag\":\"incompatible\",\"a\":62,\"b\":32},{\"tag\":\"incompatible\",\"a\":62,\"b\":55},{\"tag\":\"incompatible\",\"a\":64,\"b\":29},{\"tag\":\"incompatible\",\"a\":65,\"b\":61},{\"tag\":\"incompatible\",\"a\":66,\"b\":29},{\"tag\":\"incompatible\",\"a\":66,\"b\":30},{\"tag\":\"incompatible\",\"a\":68,\"b\":29},{\"tag\":\"incompatible\",\"a\":68,\"b\":30},{\"tag\":\"incompatible\",\"a\":68,\"b\":32},{\"tag\":\"incompatible\",\"a\":68,\"b\":62},{\"tag\":\"incompatible\",\"a\":69,\"b\":17},{\"tag\":\"incompatible\",\"a\":69,\"b\":38},{\"tag\":\"incompatible\",\"a\":69,\"b\":39},{\"tag\":\"incompatible\",\"a\":70,\"b\":39},{\"tag\":\"incompatible\",\"a\":70,\"b\":42},{\"tag\":\"incompatible\",\"a\":71,\"b\":57},{\"tag\":\"incompatible\",\"a\":72,\"b\":42},{\"tag\":\"incompatible\",\"a\":73,\"b\":57},{\"tag\":\"incompatible\",\"a\":74,\"b\":34},{\"tag\":\"incompatible\",\"a\":74,\"b\":39},{\"tag\":\"incompatible\",\"a\":74,\"b\":45},{\"tag\":\"incompatible\",\"a\":74,\"b\":59},{\"tag\":\"incompatible\",\"a\":74,\"b\":70},{\"tag\":\"incompatible\",\"a\":76,\"b\":39},{\"tag\":\"incompatible\",\"a\":76,\"b\":42},{\"tag\":\"incompatible\",\"a\":76,\"b\":43},{\"tag\":\"incompatible\",\"a\":77,\"b\":17},{\"tag\":\"incompatible\",\"a\":77,\"b\":38},{\"tag\":\"incompatible\",\"a\":77,\"b\":47},{\"tag\":\"incompatible\",\"a\":77,\"b\":49},{\"tag\":\"incompatible\",\"a\":77,\"b\":51},{\"tag\":\"incompatible\",\"a\":78,\"b\":57},{\"tag\":\"incompatible\",\"a\":79,\"b\":60},{\"tag\":\"mate\",\"ridge\":7,\"a\":18,\"owners\":[1,22,23,25]},{\"tag\":\"mate\",\"ridge\":7,\"a\":22,\"owners\":[0,18,20,24]},{\"tag\":\"mate\",\"ridge\":11,\"a\":17,\"owners\":[2,29,30,31]},{\"tag\":\"mate\",\"ridge\":11,\"a\":20,\"owners\":[2,26,27,28,29]},{\"tag\":\"mate\",\"ridge\":11,\"a\":27,\"owners\":[0,19,20,30]},{\"tag\":\"mate\",\"ridge\":13,\"a\":17,\"owners\":[4,39,40,41]},{\"tag\":\"mate\",\"ridge\":14,\"a\":55,\"owners\":[0,17,19,54,56]},{\"tag\":\"mate\",\"ridge\":14,\"a\":57,\"owners\":[0,17,18,19,53,54]},{\"tag\":\"mate\",\"ridge\":19,\"a\":27,\"owners\":[1,22,23,33,34]},{\"tag\":\"mate\",\"ridge\":19,\"a\":32,\"owners\":[1,17,22,23,28,34]},{\"tag\":\"mate\",\"ridge\":21,\"a\":23,\"owners\":[5,36,37,38,42]},{\"tag\":\"mate\",\"ridge\":22,\"a\":60,\"owners\":[1,17,21,22,53,54]},{\"tag\":\"mate\",\"ridge\":67,\"a\":18,\"owners\":[3,32,35]},{\"tag\":\"mate\",\"ridge\":67,\"a\":32,\"owners\":[2,18,24,31]},{\"tag\":\"mate\",\"ridge\":73,\"a\":46,\"owners\":[2,18,31,41]},{\"tag\":\"mate\",\"ridge\":74,\"a\":29,\"owners\":[13,53,55]},{\"tag\":\"mate\",\"ridge\":74,\"a\":55,\"owners\":[2,27,29,61]},{\"tag\":\"mate\",\"ridge\":74,\"a\":62,\"owners\":[2,18,27,53]},{\"tag\":\"mate\",\"ridge\":81,\"a\":27,\"owners\":[8,51]},{\"tag\":\"mate\",\"ridge\":82,\"a\":32,\"owners\":[53,58,67]},{\"tag\":\"mate\",\"ridge\":82,\"a\":64,\"owners\":[3,21,27,53]},{\"tag\":\"mate\",\"ridge\":82,\"a\":65,\"owners\":[3,21,27,53,58]},{\"tag\":\"mate\",\"ridge\":133,\"a\":22,\"owners\":[4,39,45]},{\"tag\":\"mate\",\"ridge\":137,\"a\":38,\"owners\":[7,49]},{\"tag\":\"mate\",\"ridge\":140,\"a\":4,\"owners\":[54,56,69,70,71,73]},{\"tag\":\"mate\",\"ridge\":140,\"a\":19,\"owners\":[69,70,71,73]},{\"tag\":\"mate\",\"ridge\":140,\"a\":38,\"owners\":[56,70,71,73]},{\"tag\":\"mate\",\"ridge\":140,\"a\":39,\"owners\":[54,56,73]},{\"tag\":\"mate\",\"ridge\":148,\"a\":22,\"owners\":[14,69,74]},{\"tag\":\"mate\",\"ridge\":148,\"a\":59,\"owners\":[5,38,42,69]},{\"tag\":\"mate\",\"ridge\":148,\"a\":74,\"owners\":[5,22,38,54]},{\"tag\":\"mate\",\"ridge\":41,\"a\":50,\"owners\":[7,26,36,39,47]},{\"tag\":\"three\",\"ridge\":97,\"vertices\":[8,35,49]},{\"tag\":\"mate\",\"ridge\":104,\"a\":29,\"owners\":[15,77]},{\"tag\":\"mate\",\"ridge\":104,\"a\":49,\"owners\":[15,61,62]},{\"tag\":\"mate\",\"ridge\":168,\"a\":7,\"owners\":[69,70,71,77,78]},{\"tag\":\"mate\",\"ridge\":168,\"a\":39,\"owners\":[77,78]},{\"tag\":\"mate\",\"ridge\":168,\"a\":47,\"owners\":[70,71,78]},{\"tag\":\"mate\",\"ridge\":168,\"a\":49,\"owners\":[69,70,71,78]},{\"tag\":\"mate\",\"ridge\":49,\"a\":52,\"owners\":[8,26,32,36,46]},{\"tag\":\"mate\",\"ridge\":112,\"a\":32,\"owners\":[77,79]},{\"tag\":\"mate\",\"ridge\":112,\"a\":79,\"owners\":[8,32,46,51,61,77]},{\"tag\":\"mate\",\"ridge\":176,\"a\":51,\"owners\":[16,69,74]},{\"tag\":\"mate\",\"ridge\":262,\"a\":55,\"owners\":[12,60]},{\"tag\":\"mate\",\"ridge\":266,\"a\":57,\"owners\":[13,30,31,62]},{\"tag\":\"mate\",\"ridge\":268,\"a\":57,\"owners\":[40,41,70]},{\"tag\":\"mate\",\"ridge\":530,\"a\":60,\"owners\":[33,34,65]},{\"tag\":\"mate\",\"ridge\":770,\"a\":12,\"owners\":[63,66,67,68]},{\"tag\":\"mate\",\"ridge\":770,\"a\":60,\"owners\":[63,68]},{\"tag\":\"mate\",\"ridge\":770,\"a\":67,\"owners\":[12,57,63]},{\"tag\":\"mate\",\"ridge\":772,\"a\":57,\"owners\":[75,76]},{\"tag\":\"mate\",\"ridge\":772,\"a\":73,\"owners\":[12,60,75]},{\"tag\":\"mate\",\"ridge\":322,\"a\":13,\"owners\":[24,35,58,64,67,68]},{\"tag\":\"mate\",\"ridge\":322,\"a\":55,\"owners\":[35,64,67,68]},{\"tag\":\"mate\",\"ridge\":644,\"a\":59,\"owners\":[45,71,73,76]},{\"tag\":\"mate\",\"ridge\":644,\"a\":74,\"owners\":[25,56,73]},{\"tag\":\"mate\",\"ridge\":296,\"a\":78,\"owners\":[15,30,40,50,62]},{\"tag\":\"mate\",\"ridge\":352,\"a\":15,\"owners\":[35,64,68,79]},{\"tag\":\"mate\",\"ridge\":352,\"a\":62,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":560,\"a\":65,\"owners\":[16,43,52,74,75]},{\"tag\":\"mate\",\"ridge\":672,\"a\":71,\"owners\":[16,52]},{\"tag\":\"mate\",\"ridge\":672,\"a\":74,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":325,\"a\":24,\"owners\":[41]},{\"tag\":\"mate\",\"ridge\":325,\"a\":41,\"owners\":[24]},{\"tag\":\"mate\",\"ridge\":643,\"a\":25,\"owners\":[34]},{\"tag\":\"mate\",\"ridge\":643,\"a\":34,\"owners\":[25]},{\"tag\":\"mate\",\"ridge\":58,\"a\":26,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":58,\"a\":61,\"owners\":[26]},{\"tag\":\"mate\",\"ridge\":154,\"a\":28,\"owners\":[54]},{\"tag\":\"mate\",\"ridge\":154,\"a\":54,\"owners\":[28]},{\"tag\":\"mate\",\"ridge\":291,\"a\":35,\"owners\":[30]},{\"tag\":\"mate\",\"ridge\":547,\"a\":33,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":60,\"a\":36,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":60,\"a\":69,\"owners\":[36]},{\"tag\":\"mate\",\"ridge\":92,\"a\":37,\"owners\":[53]},{\"tag\":\"mate\",\"ridge\":92,\"a\":53,\"owners\":[37]},{\"tag\":\"mate\",\"ridge\":293,\"a\":40,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":549,\"a\":43,\"owners\":[45]},{\"tag\":\"mate\",\"ridge\":216,\"a\":48,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":216,\"a\":77,\"owners\":[48]},{\"tag\":\"mate\",\"ridge\":650,\"a\":56,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":340,\"a\":58,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":554,\"a\":63,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":800,\"a\":66,\"owners\":[72,76,78]},{\"tag\":\"mate\",\"ridge\":800,\"a\":68,\"owners\":[72,75,76,78]},{\"tag\":\"mate\",\"ridge\":800,\"a\":72,\"owners\":[66,68,79]},{\"tag\":\"mate\",\"ridge\":800,\"a\":76,\"owners\":[63,66,68,79]},{\"tag\":\"mate\",\"ridge\":800,\"a\":78,\"owners\":[66,68,75,79]},{\"tag\":\"mate\",\"ridge\":800,\"a\":79,\"owners\":[63,72,76,78]},{\"tag\":\"mate\",\"ridge\":306,\"a\":66,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":610,\"a\":68,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":848,\"a\":67,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":848,\"a\":79,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":420,\"a\":70,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":420,\"a\":76,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":556,\"a\":71,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":556,\"a\":72,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":904,\"a\":73,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":904,\"a\":78,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":308,\"a\":75,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":1,\"index\":0,\"member\":0,\"full_literals\":[-1,77]},{\"tag\":\"group_or\",\"kind\":1,\"index\":2,\"members\":[2],\"full_literals\":[-78,3]},{\"tag\":\"group_take\",\"kind\":1,\"index\":2,\"member\":2,\"full_literals\":[-3,78]},{\"tag\":\"group_take\",\"kind\":1,\"index\":3,\"member\":3,\"full_literals\":[-4,79]},{\"tag\":\"group_take\",\"kind\":1,\"index\":5,\"member\":5,\"full_literals\":[-6,80]},{\"tag\":\"group_take\",\"kind\":1,\"index\":12,\"member\":12,\"full_literals\":[-9,81]},{\"tag\":\"group_take\",\"kind\":1,\"index\":15,\"member\":15,\"full_literals\":[-12,82]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0005\",\"joined_name\":\"grouped1_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-77,false,83],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped1_0006\",\"right_name\":\"grouped1_0008\",\"joined_name\":\"grouped1_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-84,78,false],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped1_0006\",\"right_name\":\"grouped1_0008\",\"joined_name\":\"grouped1_0007\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-78,-79,84],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0007\",\"joined_name\":\"grouped1_0002\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-84,85],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0007\",\"joined_name\":\"grouped1_0002\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-83,-84,86],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped1_0009\",\"right_name\":\"grouped1_0012\",\"joined_name\":\"grouped1_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-80,87],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped1_0010\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-87,false,88],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0011\",\"joined_name\":\"grouped1_0003\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-85,false,89],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0011\",\"joined_name\":\"grouped1_0003\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-85,-88,90],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0011\",\"joined_name\":\"grouped1_0003\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-86,false,90],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12],\"right\":[13],\"left_name\":\"grouped1_0016\",\"right_name\":\"grouped1_0019\",\"joined_name\":\"grouped1_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-81,false,91],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15],\"right\":[16],\"left_name\":\"grouped1_0022\",\"right_name\":\"grouped1_0024\",\"joined_name\":\"grouped1_0023\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-82,false,92],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[14],\"right\":[15,16],\"left_name\":\"grouped1_0020\",\"right_name\":\"grouped1_0023\",\"joined_name\":\"grouped1_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-92,93],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12,13],\"right\":[14,15,16],\"left_name\":\"grouped1_0017\",\"right_name\":\"grouped1_0021\",\"joined_name\":\"grouped1_0018\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-91,false,94],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12,13],\"right\":[14,15,16],\"left_name\":\"grouped1_0017\",\"right_name\":\"grouped1_0021\",\"joined_name\":\"grouped1_0018\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-91,-93,95],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8,9,10,11],\"right\":[12,13,14,15,16],\"left_name\":\"grouped1_0014\",\"right_name\":\"grouped1_0018\",\"joined_name\":\"grouped1_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-94,96],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8,9,10,11],\"right\":[12,13,14,15,16],\"left_name\":\"grouped1_0014\",\"right_name\":\"grouped1_0018\",\"joined_name\":\"grouped1_0015\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-95,97],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7],\"right\":[8,9,10,11,12,13,14,15,16],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0015\",\"joined_name\":\"groupKind1\",\"a\":2,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-89,-97,98],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7],\"right\":[8,9,10,11,12,13,14,15,16],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0015\",\"joined_name\":\"groupKind1\",\"a\":3,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-90,-96,98],\"grouped\":true,\"kind\":1},{\"tag\":\"quota_upper\",\"kind\":1,\"quota\":3,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[57,60],\"full_literals\":[-99,54,57]},{\"tag\":\"group_take\",\"kind\":2,\"index\":0,\"member\":57,\"full_literals\":[-54,99]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[29,31,50,62],\"full_literals\":[-100,26,28,47,59]},{\"tag\":\"group_take\",\"kind\":2,\"index\":1,\"member\":50,\"full_literals\":[-47,100]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[42,44,52,74],\"full_literals\":[-101,39,41,49,71]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[46,47,49,51],\"full_literals\":[-102,43,44,46,48]},{\"tag\":\"group_take\",\"kind\":2,\"index\":3,\"member\":51,\"full_literals\":[-48,102]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[19,38,39],\"full_literals\":[-103,16,35,36]},{\"tag\":\"group_take\",\"kind\":2,\"index\":4,\"member\":38,\"full_literals\":[-35,103]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[21,27,32],\"full_literals\":[-104,18,24,29]},{\"tag\":\"group_take\",\"kind\":2,\"index\":5,\"member\":21,\"full_literals\":[-18,104]},{\"tag\":\"group_take\",\"kind\":2,\"index\":5,\"member\":32,\"full_literals\":[-29,104]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[18,20,55],\"full_literals\":[-105,15,17,52]},{\"tag\":\"group_take\",\"kind\":2,\"index\":6,\"member\":18,\"full_literals\":[-15,105]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[22,23,59],\"full_literals\":[-106,19,20,56]},{\"tag\":\"group_take\",\"kind\":2,\"index\":7,\"member\":22,\"full_literals\":[-19,106]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[17],\"full_literals\":[-107,14]},{\"tag\":\"group_take\",\"kind\":2,\"index\":8,\"member\":17,\"full_literals\":[-14,107]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0025\",\"right_name\":\"grouped2_0029\",\"joined_name\":\"grouped2_0026\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-108,99,100],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0025\",\"right_name\":\"grouped2_0029\",\"joined_name\":\"grouped2_0026\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-109,99,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0025\",\"right_name\":\"grouped2_0029\",\"joined_name\":\"grouped2_0026\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-109,false,100],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0030\",\"right_name\":\"grouped2_0032\",\"joined_name\":\"grouped2_0031\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-110,101,102],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0030\",\"right_name\":\"grouped2_0032\",\"joined_name\":\"grouped2_0031\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-111,101,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0030\",\"right_name\":\"grouped2_0032\",\"joined_name\":\"grouped2_0031\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-111,false,102],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0026\",\"right_name\":\"grouped2_0031\",\"joined_name\":\"grouped2_0027\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-112,108,111],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0026\",\"right_name\":\"grouped2_0031\",\"joined_name\":\"grouped2_0027\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-113,108,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0026\",\"right_name\":\"grouped2_0031\",\"joined_name\":\"grouped2_0027\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-112,109,110],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0026\",\"right_name\":\"grouped2_0031\",\"joined_name\":\"grouped2_0027\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-113,109,111],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0026\",\"right_name\":\"grouped2_0031\",\"joined_name\":\"grouped2_0027\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-114,109,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0026\",\"right_name\":\"grouped2_0031\",\"joined_name\":\"grouped2_0027\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-113,false,110],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0026\",\"right_name\":\"grouped2_0031\",\"joined_name\":\"grouped2_0027\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-114,false,111],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0033\",\"right_name\":\"grouped2_0036\",\"joined_name\":\"grouped2_0034\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-115,103,104],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0033\",\"right_name\":\"grouped2_0036\",\"joined_name\":\"grouped2_0034\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-116,103,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0033\",\"right_name\":\"grouped2_0036\",\"joined_name\":\"grouped2_0034\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-103,false,115],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0033\",\"right_name\":\"grouped2_0036\",\"joined_name\":\"grouped2_0034\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-116,false,104],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0033\",\"right_name\":\"grouped2_0036\",\"joined_name\":\"grouped2_0034\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-103,-104,116],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0039\",\"right_name\":\"grouped2_0041\",\"joined_name\":\"grouped2_0040\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-117,106,107],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0039\",\"right_name\":\"grouped2_0041\",\"joined_name\":\"grouped2_0040\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-107,117],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0039\",\"right_name\":\"grouped2_0041\",\"joined_name\":\"grouped2_0040\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-118,106,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0039\",\"right_name\":\"grouped2_0041\",\"joined_name\":\"grouped2_0040\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-118,false,107],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0037\",\"right_name\":\"grouped2_0040\",\"joined_name\":\"grouped2_0038\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-119,105,117],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0037\",\"right_name\":\"grouped2_0040\",\"joined_name\":\"grouped2_0038\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-120,105,118],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0037\",\"right_name\":\"grouped2_0040\",\"joined_name\":\"grouped2_0038\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-121,105,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0037\",\"right_name\":\"grouped2_0040\",\"joined_name\":\"grouped2_0038\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-120,false,117],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0037\",\"right_name\":\"grouped2_0040\",\"joined_name\":\"grouped2_0038\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-121,false,118],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0034\",\"right_name\":\"grouped2_0038\",\"joined_name\":\"grouped2_0035\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-122,115,121],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0034\",\"right_name\":\"grouped2_0038\",\"joined_name\":\"grouped2_0035\",\"a\":0,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-123,115,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0034\",\"right_name\":\"grouped2_0038\",\"joined_name\":\"grouped2_0035\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-122,116,120],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0034\",\"right_name\":\"grouped2_0038\",\"joined_name\":\"grouped2_0035\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-123,116,121],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0034\",\"right_name\":\"grouped2_0038\",\"joined_name\":\"grouped2_0035\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-124,116,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0034\",\"right_name\":\"grouped2_0038\",\"joined_name\":\"grouped2_0035\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-122,false,119],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0034\",\"right_name\":\"grouped2_0038\",\"joined_name\":\"grouped2_0035\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-123,false,120],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0034\",\"right_name\":\"grouped2_0038\",\"joined_name\":\"grouped2_0035\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-124,false,121],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0027\",\"right_name\":\"grouped2_0035\",\"joined_name\":\"groupKind2\",\"a\":1,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-125,112,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0027\",\"right_name\":\"grouped2_0035\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-125,113,124],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0027\",\"right_name\":\"grouped2_0035\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-125,114,123],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0027\",\"right_name\":\"grouped2_0035\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-125,false,122],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[24,30,40],\"full_literals\":[-126,21,27,37]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[25,33,43],\"full_literals\":[-127,22,30,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":43,\"full_literals\":[-40,127]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[34,45],\"full_literals\":[-128,31,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":34,\"full_literals\":[-31,128]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[35,41],\"full_literals\":[-129,32,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":41,\"full_literals\":[-38,129]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":64,\"full_literals\":[-61,130]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":65,\"full_literals\":[-62,130]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":70,\"full_literals\":[-67,131]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":71,\"full_literals\":[-68,131]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":73,\"full_literals\":[-70,131]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[72,76,78],\"full_literals\":[-132,69,73,75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":72,\"full_literals\":[-69,132]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":76,\"full_literals\":[-73,132]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":78,\"full_literals\":[-75,132]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[66,68,79],\"full_literals\":[-133,63,65,76]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":66,\"full_literals\":[-63,133]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":68,\"full_literals\":[-65,133]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":79,\"full_literals\":[-76,133]},{\"tag\":\"group_or\",\"kind\":3,\"index\":8,\"members\":[26,28,36,37,48],\"full_literals\":[-134,23,25,33,34,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":26,\"full_literals\":[-23,134]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":28,\"full_literals\":[-25,134]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":36,\"full_literals\":[-33,134]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":37,\"full_literals\":[-34,134]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":48,\"full_literals\":[-45,134]},{\"tag\":\"group_or\",\"kind\":3,\"index\":9,\"members\":[53,54,61,69,77],\"full_literals\":[-135,50,51,58,66,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":53,\"full_literals\":[-50,135]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":54,\"full_literals\":[-51,135]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":61,\"full_literals\":[-58,135]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":69,\"full_literals\":[-66,135]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":77,\"full_literals\":[-74,135]},{\"tag\":\"group_or\",\"kind\":3,\"index\":10,\"members\":[58,75],\"full_literals\":[-136,55,72]},{\"tag\":\"group_or\",\"kind\":3,\"index\":11,\"members\":[56,63],\"full_literals\":[-137,53,60]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0046\",\"right_name\":\"grouped3_0048\",\"joined_name\":\"grouped3_0047\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-138,127,128],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0046\",\"right_name\":\"grouped3_0048\",\"joined_name\":\"grouped3_0047\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-128,138],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0046\",\"right_name\":\"grouped3_0048\",\"joined_name\":\"grouped3_0047\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-127,false,138],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0042\",\"right_name\":\"grouped3_0047\",\"joined_name\":\"grouped3_0043\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-139,126,138],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0042\",\"right_name\":\"grouped3_0047\",\"joined_name\":\"grouped3_0043\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-138,139],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0051\",\"right_name\":\"grouped3_0053\",\"joined_name\":\"grouped3_0052\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-131,140],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0051\",\"right_name\":\"grouped3_0053\",\"joined_name\":\"grouped3_0052\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-130,-131,141],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0049\",\"right_name\":\"grouped3_0052\",\"joined_name\":\"grouped3_0050\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-140,142],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0049\",\"right_name\":\"grouped3_0052\",\"joined_name\":\"grouped3_0050\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-141,143],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0049\",\"right_name\":\"grouped3_0052\",\"joined_name\":\"grouped3_0050\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-144,129,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0049\",\"right_name\":\"grouped3_0052\",\"joined_name\":\"grouped3_0050\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-129,-141,144],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0043\",\"right_name\":\"grouped3_0050\",\"joined_name\":\"grouped3_0044\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-142,145],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0043\",\"right_name\":\"grouped3_0050\",\"joined_name\":\"grouped3_0044\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-146,139,144],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0043\",\"right_name\":\"grouped3_0050\",\"joined_name\":\"grouped3_0044\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-144,146],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0043\",\"right_name\":\"grouped3_0050\",\"joined_name\":\"grouped3_0044\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-139,-143,146],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0057\",\"right_name\":\"grouped3_0059\",\"joined_name\":\"grouped3_0058\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-147,133,134],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0057\",\"right_name\":\"grouped3_0059\",\"joined_name\":\"grouped3_0058\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-134,147],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0057\",\"right_name\":\"grouped3_0059\",\"joined_name\":\"grouped3_0058\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-148,133,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0057\",\"right_name\":\"grouped3_0059\",\"joined_name\":\"grouped3_0058\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-133,false,147],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0057\",\"right_name\":\"grouped3_0059\",\"joined_name\":\"grouped3_0058\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-148,false,134],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0057\",\"right_name\":\"grouped3_0059\",\"joined_name\":\"grouped3_0058\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-133,-134,148],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0054\",\"right_name\":\"grouped3_0058\",\"joined_name\":\"grouped3_0055\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-149,132,148],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0054\",\"right_name\":\"grouped3_0058\",\"joined_name\":\"grouped3_0055\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-150,132,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0054\",\"right_name\":\"grouped3_0058\",\"joined_name\":\"grouped3_0055\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-149,false,147],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0054\",\"right_name\":\"grouped3_0058\",\"joined_name\":\"grouped3_0055\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-132,-147,149],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0054\",\"right_name\":\"grouped3_0058\",\"joined_name\":\"grouped3_0055\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-150,false,148],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0054\",\"right_name\":\"grouped3_0058\",\"joined_name\":\"grouped3_0055\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-132,-148,150],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped3_0062\",\"right_name\":\"grouped3_0064\",\"joined_name\":\"grouped3_0063\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-151,136,137],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped3_0060\",\"right_name\":\"grouped3_0063\",\"joined_name\":\"grouped3_0061\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-152,135,151],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped3_0060\",\"right_name\":\"grouped3_0063\",\"joined_name\":\"grouped3_0061\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-135,false,152],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped3_0060\",\"right_name\":\"grouped3_0063\",\"joined_name\":\"grouped3_0061\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-153,false,151],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0055\",\"right_name\":\"grouped3_0061\",\"joined_name\":\"grouped3_0056\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-154,149,152],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0055\",\"right_name\":\"grouped3_0061\",\"joined_name\":\"grouped3_0056\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-155,149,153],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0055\",\"right_name\":\"grouped3_0061\",\"joined_name\":\"grouped3_0056\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-149,false,154],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0055\",\"right_name\":\"grouped3_0061\",\"joined_name\":\"grouped3_0056\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-155,150,152],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0055\",\"right_name\":\"grouped3_0061\",\"joined_name\":\"grouped3_0056\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-149,-152,155],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0055\",\"right_name\":\"grouped3_0061\",\"joined_name\":\"grouped3_0056\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-156,150,153],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0055\",\"right_name\":\"grouped3_0061\",\"joined_name\":\"grouped3_0056\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-150,false,155],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0055\",\"right_name\":\"grouped3_0061\",\"joined_name\":\"grouped3_0056\",\"a\":3,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-150,-152,156],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped3_0044\",\"right_name\":\"grouped3_0056\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":4,\"direction\":\"forward\",\"full_literals\":[-145,-156,158],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped3_0044\",\"right_name\":\"grouped3_0056\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-157,146,154],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped3_0044\",\"right_name\":\"grouped3_0056\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-146,-154,158],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":4,\"grouped\":true},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":4,\"grouped\":true},{\"tag\":\"block\",\"leaf\":0,\"vertices\":[2,8,12,20,21,38,49,52,59,62,67,71,72,79]},{\"tag\":\"block\",\"leaf\":1,\"vertices\":[2,5,12,19,23,32,47,50,55,67,73,74,78,79]},{\"tag\":\"block\",\"leaf\":2,\"vertices\":[2,8,12,20,21,38,49,52,59,62,67,73,78,79]},{\"tag\":\"block\",\"leaf\":3,\"vertices\":[2,5,12,17,32,39,50,52,55,59,67,73,78,79]},{\"tag\":\"block\",\"leaf\":4,\"vertices\":[2,8,12,20,21,38,49,52,59,62,67,70,76,79]},{\"tag\":\"block\",\"leaf\":5,\"vertices\":[0,8,14,22,27,39,50,52,55,60,65,68,73,78]},{\"tag\":\"block\",\"leaf\":6,\"vertices\":[0,8,15,21,31,38,49,52,57,59,64,66,70,76]},{\"tag\":\"block\",\"leaf\":7,\"vertices\":[0,8,15,21,31,38,49,52,57,59,65,68,70,76]},{\"tag\":\"block\",\"leaf\":8,\"vertices\":[0,8,15,21,31,38,49,52,57,59,67,70,76,79]},{\"tag\":\"block\",\"leaf\":9,\"vertices\":[0,2,8,21,38,49,52,57,59,62,67,70,76,79]},{\"tag\":\"block\",\"leaf\":10,\"vertices\":[0,4,7,22,27,50,51,55,60,65,68,73,74,78]},{\"tag\":\"block\",\"leaf\":11,\"vertices\":[0,14,16,22,27,39,50,51,55,60,65,68,73,78]},{\"tag\":\"block\",\"leaf\":12,\"vertices\":[2,3,16,17,39,44,50,51,55,60,65,68,73,78]},{\"tag\":\"block\",\"leaf\":13,\"vertices\":[0,1,15,31,32,38,49,52,57,59,67,70,76,79]},{\"tag\":\"block\",\"leaf\":14,\"vertices\":[5,7,12,19,23,27,50,51,55,64,66,73,74,78]},{\"tag\":\"block\",\"leaf\":15,\"vertices\":[2,5,12,20,21,39,46,52,59,62,67,73,78,79]},{\"tag\":\"block\",\"leaf\":16,\"vertices\":[5,7,12,19,23,27,50,51,55,67,73,74,78,79]},{\"tag\":\"block\",\"leaf\":17,\"vertices\":[5,7,12,19,23,27,50,51,55,65,68,73,74,78]},{\"tag\":\"block\",\"leaf\":18,\"vertices\":[1,7,13,18,32,38,50,52,57,59,67,70,76,79]},{\"tag\":\"block\",\"leaf\":19,\"vertices\":[1,7,16,19,27,44,50,51,55,60,65,68,71,72]},{\"tag\":\"block\",\"leaf\":20,\"vertices\":[1,7,16,19,27,44,50,51,55,60,65,68,70,76]},{\"tag\":\"block\",\"leaf\":21,\"vertices\":[1,7,16,19,27,44,50,51,55,60,65,68,73,78]},{\"tag\":\"block\",\"leaf\":22,\"vertices\":[1,5,7,19,27,50,51,55,60,65,68,73,74,78]},{\"tag\":\"block\",\"leaf\":23,\"vertices\":[1,3,8,18,38,49,52,57,59,62,67,70,76,79]},{\"tag\":\"block\",\"leaf\":24,\"vertices\":[1,13,15,18,32,38,49,52,57,59,67,70,76,79]},{\"tag\":\"block\",\"leaf\":25,\"vertices\":[4,5,15,17,31,32,49,52,57,59,67,70,76,79]},{\"tag\":\"block\",\"leaf\":26,\"vertices\":[0,1,16,27,39,44,50,51,55,60,65,68,73,78]},{\"tag\":\"edge\",\"edge\":27,\"owners\":[4,7,19,28,38,39,47,48,49,54,56,69,70,71,73,77,78]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[12,57,60,63,66,67,68,72,73,75,76,78,79]}]}"
  "435 -73 63 65 76 0 225 229 0\n436 -76 69 73 75 0 225 231 0\n437 112 0 327 323 0\n438 122 0 327 326 0\n439 119 0 438 320 0\n440 -126 21 27 0 219 328 0\n441 -127 22 40 0 214 329 0\n442 -136 0 224 242 360 0\n443 -137 0 223 225 361 0\n444 -151 0 442 443 389 0\n445 -152 135 0 444 390 0\n446 -153 0 444 392 0\n447 -155 149 0 446 394 0\n448 -156 150 0 446 398 0\n449 5 7 16 25 35 36 44 45 46 51 66 67 68 70 74 75 0 223 433 0\n450 9 54 57 63 64 65 69 70 73 75 76 0 225 242 434 0\n451 -156 0 405 448 401 384 373 369 367 337 338 339 237 239 241 340 0\n452 -148 150 0 242 379 388 341 342 343 226 227 436 344 0\n453 134 -135 0 349 350 351 352 353 210 212 216 218 222 354 0\n454 -152 -149 0 451 242 445 400 452 383 453 382 345 346 347 228 435 230 340 0\n455 -155 0 447 454 391 396 355 356 357 358 359 387 217 211 209 215 221 381 348 0\n456 -150 0 455 399 0\n457 -148 0 456 452 0\n458 -124 36 0 319 322 302 314 309 286 3 39 277 0\n459 -14 -115 36 29 0 3 7 18 39 279 277 301 0\n460 -20 -101 39 71 0 60 90 274 0\n461 -19 -103 36 0 10 41 277 0\n462 65 39 54 36 71 29 76 -133 0 225 327 458 324 295 201 191 344 270 114 289 298 325 316 321 313 297 288 292 293 459 286 309 306 314 311 318 302 304 460 461 284 103 104 277 274 44 69 72 93 279 275 8 98 84 282 272 26 0\n463 -56 26 39 54 36 71 29 59 0 327 458 324 295 103 104 106 270 289 288 298 297 325 292 293 316 321 274 459 92 93 286 309 314 311 318 302 304 277 44 69 279 275 8 98 84 282 272 26 0\n464 -20 39 54 -113 71 0 105 460 270 292 289 297 0\n465 -19 26 39 36 71 29 59 0 438 327 9 11 59 461 286 302 309 314 315 318 301 325 279 298 300 27 66 71 290 292 293 272 274 84 93 275 0\n466 -24 -49 -102 -100 26 59 0 93 92 27 66 272 275 84 0\n467 -17 -100 26 59 0 26 82 272 0\n468 -28 17 -105 0 25 99 282 0\n469 -15 -104 29 0 8 19 279 0\n470 73 75 76 -132 -133 135 0 242 439 438 327 359 179 458 324 204 183 201 358 215 357 209 356 355 193 340 126 239 462 116 233 463 464 465 284 308 314 315 459 286 306 313 310 321 317 325 302 304 298 300 289 290 292 293 270 467 468 272 83 84 469 282 98 279 154 44 71 466 277 174 275 203 274 425 0\n471 -52 -73 36 71 76 146 -133 135 0 438 327 214 242 237 337 135 134 458 324 359 183 201 358 215 357 209 98 99 102 462 464 116 233 463 465 336 284 368 308 370 314 376 315 366 459 363 286 332 306 313 321 317 325 302 304 298 300 279 289 290 292 293 44 66 71 151 466 270 272 277 174 274 202 84 426 275 0\n472 -24 -105 52 36 59 0 327 18 19 22 44 286 282 309 6 467 314 277 290 302 298 318 325 0\n473 -123 116 36 29 0 316 318 459 314 286 309 0\n474 26 -106 -114 -105 39 36 71 29 59 0 300 292 460 293 298 290 465 467 284 468 104 272 274 83 84 92 93 275 0\n475 -26 52 64 50 0 224 35 54 112 116 158 205 195 0\n476 116 -105 26 52 39 36 71 29 59 0 438 327 317 313 473 325 298 290 467 474 282 306 2 286 0\n477 -105 26 52 39 36 71 29 59 0 327 465 472 476 302 304 303 469 279 459 282 13 286 100 467 463 290 284 298 306 325 313 321 0\n478 -65 -28 -12 -46 -18 -8 -1 -49 -35 -54 -56 -73 0 237 233 413 0\n479 75 76 -132 -133 135 0 405 439 438 327 359 183 234 201 380 386 395 403 358 215 357 209 356 355 204 179 470 134 237 471 475 465 477 283 310 312 315 459 286 309 306 311 321 317 325 302 304 298 300 290 292 293 460 284 103 104 463 277 274 150 44 69 72 93 182 279 275 175 84 177 272 478 344 200 412 0\n480 39 71 26 36 -75 76 146 -133 135 0 439 438 327 214 242 458 324 241 339 141 359 183 201 358 215 357 209 462 464 465 463 233 284 336 308 368 314 370 315 376 459 366 286 363 364 306 332 330 313 310 321 317 477 325 302 304 98 99 298 300 279 289 290 292 293 44 66 71 466 151 270 272 277 274 202 84 174 427 275 0\n481 117 -39 26 36 59 0 439 438 327 87 74 56 313 310 321 317 325 302 298 300 277 290 293 6 468 272 83 84 275 0\n482 106 -117 36 29 0 438 308 306 314 286 315 459 0\n483 -14 -106 19 36 54 29 0 327 12 459 284 316 106 325 270 298 289 0\n484 -57 -106 19 0 105 106 284 0\n485 -39 26 36 54 29 59 0 327 458 324 295 55 74 87 481 482 483 286 309 484 270 289 288 298 297 467 325 293 321 311 468 272 83 84 275 0\n486 -65 -48 -16 -6 -7 -52 -47 -24 -9 -20 -71 -75 0 241 233 423 0\n487 19 -106 -71 26 36 -75 76 -133 135 0 242 327 131 458 324 295 241 141 359 183 234 201 358 215 357 209 356 483 484 284 286 270 194 13 309 289 288 314 298 297 467 325 293 321 318 311 302 304 468 469 279 272 282 34 44 66 71 84 174 173 277 275 486 344 196 420 0\n488 -19 -71 26 36 -75 29 59 135 0 327 438 214 225 223 130 128 241 141 358 215 357 209 356 9 10 11 165 461 286 302 309 317 473 314 311 325 315 298 300 301 289 290 293 469 279 270 467 282 27 66 71 189 191 149 272 84 174 275 416 0\n489 26 36 -75 76 146 -133 135 0 439 438 327 214 225 241 141 359 183 201 358 215 357 209 356 355 485 480 128 488 487 482 307 313 310 287 321 317 325 302 304 298 300 469 289 290 293 270 467 189 191 468 282 272 98 83 84 154 279 44 71 173 277 174 275 428 0\n490 -26 76 74 0 35 112 116 176 200 0\n491 106 -123 29 0 321 313 308 306 314 286 318 7 18 304 279 0\n492 -104 24 99 26 29 59 0 327 289 298 325 321 469 279 7 98 286 309 314 311 322 282 324 467 295 288 0\n493 24 84 -61 99 76 135 0 327 289 298 325 359 490 183 201 357 209 356 211 355 492 280 304 163 318 246 312 314 252 309 245 286 159 146 2 282 0\n494 -12 -91 -61 99 76 135 0 269 327 359 490 201 81 249 261 262 264 266 267 257 253 493 18 27 286 272 309 288 314 295 322 324 0\n495 -24 -100 -106 109 71 39 26 54 59 0 327 18 286 309 314 322 324 464 297 292 293 466 274 59 104 284 0\n496 65 71 39 35 -75 76 144 -133 135 0 225 242 269 219 327 359 490 241 339 141 183 201 358 191 344 270 194 115 232 289 248 335 298 260 368 325 263 372 265 334 268 205 259 491 494 199 82 273 495 492 493 304 251 253 254 319 244 258 250 324 1 256 243 464 255 144 247 284 172 0\n497 99 24 71 46 44 39 26 54 29 59 0 327 289 492 298 304 325 319 318 491 324 314 464 297 309 292 293 286 9 65 284 275 104 93 274 0\n498 -123 -57 24 29 0 491 484 9 11 286 279 309 304 314 318 0\n499 -19 -102 -101 -100 24 71 46 44 39 26 29 59 0 438 467 9 11 59 286 279 274 309 304 93 317 275 311 83 468 272 0\n500 104 106 -102 -101 -100 -57 24 -65 -36 26 -75 59 135 0 224 438 308 467 233 117 129 80 73 57 241 358 355 280 304 164 317 313 311 306 468 286 272 145 2 65 282 275 93 185 418 274 0\n501 24 -65 -36 26 -75 29 59 135 0 327 439 129 80 73 57 141 497 270 105 106 498 325 298 300 290 292 293 467 499 284 500 469 279 7 98 286 282 306 310 0\n502 106 -24 31 -65 -36 26 -75 29 59 0 214 327 439 242 57 129 141 18 286 309 314 322 324 464 66 27 19 233 117 80 73 58 48 241 285 491 306 151 325 310 298 300 289 290 292 293 270 467 272 466 275 147 282 274 202 432 0\n503 99 -106 -24 71 39 26 54 59 0 327 18 286 309 314 322 324 295 289 288 495 0\n504 -111 41 43 71 46 44 39 0 292 293 274 275 93 0\n505 -102 -11 -19 -57 -24 -65 -36 26 -75 59 0 327 242 19 18 286 309 57 73 80 129 66 59 504 300 325 321 311 314 322 324 297 290 467 282 117 48 147 27 272 233 58 241 466 275 202 417 0\n506 76 -132 -133 135 0 405 327 380 386 395 403 375 359 358 201 183 479 141 241 339 490 489 48 51 57 73 80 129 496 117 233 336 368 370 376 366 363 332 501 18 19 27 66 286 309 314 322 324 299 502 503 270 484 59 171 504 300 297 325 290 321 467 272 311 147 282 505 276 291 161 274 411 0\n507 -36 -24 57 0 219 327 18 286 309 314 322 324 20 206 71 66 28 57 80 123 129 188 464 270 289 298 297 325 504 491 59 104 284 0\n508 106 -24 57 0 439 327 438 507 44 28 19 482 491 313 310 325 317 298 302 289 277 270 6 102 282 0\n509 120 19 71 39 -106 36 35 0 438 327 321 317 325 302 300 277 292 103 460 284 0\n510 -114 -105 71 39 -24 57 0 508 507 28 22 19 298 474 289 111 270 282 100 0\n511 19 71 39 -24 57 0 327 508 507 18 286 309 314 322 324 44 28 19 509 311 510 325 473 302 277 6 103 282 284 102 464 0\n512 71 39 -24 57 0 438 327 507 18 286 309 28 511 461 302 317 473 311 325 510 0\n513 -71 -24 -76 135 0 219 225 327 142 508 507 18 286 309 314 322 324 295 20 206 71 66 44 28 27 22 19 235 358 215 357 209 356 131 132 204 188 241 270 192 289 288 298 297 325 293 321 473 311 302 461 277 173 284 6 282 111 272 84 174 275 422 0\n514 -24 -76 135 0 219 327 142 18 19 20 22 28 44 286 206 309 507 513 512 124 188 270 485 289 111 298 325 321 473 311 302 282 277 6 0\n515 -116 -105 -102 -100 48 44 36 35 24 0 302 304 277 4 6 282 468 98 111 279 29 68 272 275 84 0\n516 -105 -102 -123 -100 48 44 36 35 24 0 515 473 29 68 110 275 467 84 468 272 0\n517 -39 24 57 0 242 327 56 57 74 87 134 458 193 324 270 295 289 288 298 297 325 293 321 516 312 311 318 309 302 286 277 3 0\n518 105 -123 36 0 321 312 311 318 309 302 286 3 39 277 0\n519 35 -116 -123 36 -76 135 0 327 223 302 461 304 518 321 313 458 324 295 142 514 517 235 358 215 355 217 277 3 4 6 16 52 103 286 282 468 205 306 98 102 111 186 284 279 270 464 153 29 86 156 289 288 204 198 272 407 297 516 293 0\n520 59 -46 -100 -105 0 84 78 467 272 468 0\n521 -75 -49 -56 -3 -17 -18 -8 -59 -46 -9 -35 -76 0 235 241 408 0\n522 73 -49 -56 -3 -17 -18 -8 -59 -46 -9 -35 -76 0 521 240 63 235 436 197 406 0\n523 48 -102 -101 -9 -100 -106 -35 19 -104 -105 -76 135 0 72 69 62 142 514 517 235 359 357 355 275 520 110 111 184 469 279 282 160 13 284 131 274 522 237 410 0\n524 99 -106 -35 19 -104 -105 -113 -76 135 0 225 72 69 62 295 142 514 517 235 271 289 288 192 297 292 293 523 86 89 279 504 13 131 284 0\n525 -46 -29 -54 -106 -35 19 -105 -113 -76 135 0 242 223 100 102 282 23 468 110 187 42 127 198 125 169 193 208 62 39 142 514 517 235 356 211 357 520 177 290 297 292 460 274 284 152 430 0\n526 -116 -123 36 -76 135 0 327 242 223 518 321 313 458 324 299 142 514 517 235 356 211 302 304 461 519 39 42 62 69 72 286 208 306 524 270 100 102 125 127 193 468 282 169 198 21 23 469 86 110 187 525 504 275 166 297 291 290 460 274 272 284 152 424 0\n527 -123 36 -76 135 0 327 458 324 295 514 142 518 526 473 318 86 281 314 305 309 278 286 2 5 70 282 102 270 289 288 297 516 293 0\n528 -29 48 44 -105 -114 0 300 293 298 290 68 110 275 520 0\n529 48 44 -105 22 32 36 -76 135 0 242 327 438 142 527 325 298 289 270 100 102 282 2 286 309 314 315 21 4 300 292 514 517 141 204 460 193 237 235 359 357 528 469 477 155 304 301 317 461 277 313 143 62 69 306 504 274 184 284 429 0\n530 44 -105 22 32 36 -76 135 0 327 438 142 527 325 298 289 270 100 102 282 2 286 309 314 315 4 141 204 300 514 517 529 86 88 89 469 504 301 62 277 0\n531 -105 22 32 36 -76 135 0 327 438 527 325 300 292 142 514 517 298 289 270 141 204 460 102 100 282 2 4 286 530 72 92 277 274 302 59 104 317 284 313 306 0\n532 -44 105 0 439 327 438 219 310 70 72 73 74 286 518 309 306 325 311 298 317 289 302 461 277 484 509 52 270 132 188 0\n533 -103 35 -101 -99 36 -117 0 242 223 461 277 3 16 103 286 306 484 284 270 127 193 198 134 460 0\n534 35 36 105 0 439 327 438 224 242 219 518 325 300 292 298 290 289 532 312 315 310 533 302 317 311 308 309 286 9 12 14 18 65 94 107 120 136 459 484 284 206 517 29 110 183 162 270 104 131 172 148 504 193 188 274 84 177 272 431 0\n535 -29 -56 -46 -49 20 -1 -54 -35 -100 0 223 404 242 121 95 108 97 137 354 193 342 75 47 46 45 43 348 445 101 206 79 213 333 371 42 208 63 331 220 441 362 440 365 374 402 393 385 377 506 235 84 78 127 125 169 41 39 110 152 177 272 419 0\n536 59 -8 -18 -56 -46 -49 -1 -54 -35 -100 0 223 404 242 121 95 108 97 137 354 193 342 75 47 46 45 43 348 445 101 206 79 213 333 371 42 208 63 331 220 441 362 440 365 374 402 393 385 377 506 235 84 78 127 125 169 177 272 414 0\n537 36 105 0 439 327 438 242 223 404 532 310 283 518 325 298 300 289 290 292 534 39 40 41 42 43 44 45 46 47 56 62 63 69 75 95 97 108 121 137 286 208 348 220 331 354 309 306 441 445 311 484 362 317 270 304 101 125 127 193 150 206 169 198 342 460 274 504 284 93 79 213 440 333 365 371 374 402 393 385 377 506 235 535 279 184 536 160 415 0\n538 -106 19 105 0 242 327 537 57 312 322 324 129 133 193 464 80 532 484 284 270 104 289 298 297 325 504 321 65 311 286 309 0\n539 106 105 0 439 438 327 537 80 532 310 308 306 311 286 321 317 7 18 65 325 304 279 300 86 293 275 0\n540 105 0 438 327 532 537 57 80 129 539 538 9 11 59 286 309 311 321 317 325 304 300 504 66 68 279 0\n541 -43 46 44 -111 -19 0 438 327 242 225 293 292 9 286 309 314 315 55 11 66 67 68 279 304 301 318 461 325 129 133 298 193 289 290 270 499 191 119 0\n542 46 44 -111 -19 0 438 293 9 286 309 314 315 38 218 37 216 96 59 55 11 541 504 275 129 204 85 86 140 461 210 301 354 279 22 514 488 201 0\n543 59 -71 26 36 135 29 -19 0 488 204 0\n544 -46 -19 0 540 38 218 37 216 96 55 17 77 78 79 80 139 210 213 354 531 201 183 465 543 0\n545 -44 -19 0 438 540 9 286 309 314 315 38 218 37 216 96 17 11 71 73 109 138 461 354 301 279 36 183 531 0\n546 -19 0 327 223 242 214 225 9 32 37 38 96 286 216 218 309 314 322 324 544 545 542 300 297 325 289 318 302 461 76 133 170 222 193 240 270 343 142 189 191 113 346 354 506 0\n547 111 -36 29 0 242 546 327 133 193 300 325 491 484 270 507 289 297 324 319 322 304 314 279 309 7 286 0\n548 -104 24 135 -36 29 0 223 540 404 242 327 546 76 355 217 50 49 357 209 348 445 129 57 547 292 460 222 179 343 212 170 133 193 122 80 73 64 58 51 279 469 15 31 53 98 207 331 282 441 362 24 26 33 440 333 365 371 374 402 393 385 377 506 142 235 270 194 289 298 325 491 284 104 172 504 274 67 157 497 421 0\n549 -123 116 -36 29 0 546 129 57 547 292 460 80 73 491 318 284 314 104 309 504 286 65 0\n550 -57 135 -132 0 225 142 191 506 346 0\n551 135 -36 29 0 242 327 76 222 179 343 133 193 550 270 507 289 548 298 304 325 549 0\n552 -36 29 0 455 76 222 179 343 551 391 453 397 378 386 0\n553 -135 0 455 457 242 225 391 453 397 378 382 386 345 346 347 341 342 343 191 234 193 240 190 450 0\n554 -50 0 553 355 0\n555 -51 0 553 356 0\n556 -66 0 553 358 0\n557 -74 0 553 359 0\n558 -25 0 555 211 0\n559 -45 0 557 221 0\n560 132 36 0 223 557 556 555 559 558 341 342 343 238 236 240 180 181 169 178 168 167 449 0\n561 73 75 29 0 242 327 553 546 557 204 552 560 550 458 324 193 340 270 126 289 464 298 325 491 527 284 201 490 463 0\n562 54 75 29 0 327 553 546 557 561 134 204 552 560 550 458 324 270 464 289 298 325 491 527 284 201 490 463 0\n563 75 29 0 438 553 540 552 204 561 134 562 100 102 282 2 4 21 23 469 286 477 213 309 201 314 315 531 301 42 277 0\n564 29 0 327 553 242 552 560 550 563 141 270 289 298 325 527 506 345 346 230 0\n565 -24 0 564 28 0\n566 -26 0 564 29 0\n567 -27 0 564 30 0\n568 -32 0 564 36 0\n569 -43 0 564 68 0\n570 -48 0 564 86 0\n571 -59 0 564 110 0\n572 -65 0 564 118 0\n573 76 0 564 557 183 0\n574 64 0 564 224 554 162 0\n575 -57 0 572 225 191 0\n576 -39 0 575 565 517 0\n577 36 0 553 573 568 540 327 576 527 531 325 61 91 207 300 128 292 274 0\n578 -35 0 577 51 0\n579 -44 0 577 73 0\n580 -46 0 577 80 0\n581 -71 0 577 129 0\n582 -73 0 577 133 0\n583 70 0 577 223 555 170 0\n584 75 0 577 557 179 0\n585 -102 0 580 570 579 569 275 0\n586 -54 0 582 242 193 0\n587 9 0 583 575 242 194 0\n588 -111 0 585 293 0\n589 -99 0 586 575 270 0\n590 108 0 588 437 294 0\n591 -109 0 589 289 0\n592 100 0 589 590 288 0\n593 110 0 591 437 296 0\n594 -113 0 591 588 297 0\n595 -17 0 592 566 571 467 0\n596 101 0 593 585 291 0\n597 124 0 594 327 324 0\n598 -28 0 595 540 468 0\n599 -20 0 596 576 581 460 0\n600 121 0 597 322 0\n601 47 0 598 571 566 592 272 0\n602 118 0 600 314 0\n603 106 0 602 308 0\n604 107 0 602 309 0\n605 56 0 603 599 546 284 0\n606 14 0 604 286 0\n607 -41 0 605 104 0\n608 6 0 605 578 576 556 172 0\n609 -15 0 606 2 0\n610 3 0 606 566 567 598 145 0\n611 49 0 607 596 576 581 274 0\n612 52 0 609 540 595 282 0\n613 0 610 612 587 606 564 577 601 611 608 605 574 583 584 573 409 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record005.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record005.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record005.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record005.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record005 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeafTable : ConcreteGrowth.Table (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record005.l) :=
(.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf (⟨0, by decide⟩))
 (.branch 2
 (.leaf (⟨1, by decide⟩))
 (.leaf (⟨2, by decide⟩))))
 (.branch 4
 (.leaf (⟨3, by decide⟩))
 (.branch 5
 (.leaf (⟨4, by decide⟩))
 (.leaf (⟨5, by decide⟩)))))
 (.branch 9
 (.branch 7
 (.leaf (⟨6, by decide⟩))
 (.branch 8
 (.leaf (⟨7, by decide⟩))
 (.leaf (⟨8, by decide⟩))))
 (.branch 11
 (.branch 10
 (.leaf (⟨9, by decide⟩))
 (.leaf (⟨10, by decide⟩)))
 (.branch 12
 (.leaf (⟨11, by decide⟩))
 (.leaf (⟨12, by decide⟩))))))
 (.branch 20
 (.branch 16
 (.branch 14
 (.leaf (⟨13, by decide⟩))
 (.branch 15
 (.leaf (⟨0, by decide⟩))
 (.leaf (⟨1, by decide⟩))))
 (.branch 18
 (.branch 17
 (.leaf (⟨2, by decide⟩))
 (.leaf (⟨4, by decide⟩)))
 (.branch 19
 (.leaf (⟨5, by decide⟩))
 (.leaf (⟨6, by decide⟩)))))
 (.branch 23
 (.branch 21
 (.leaf (⟨7, by decide⟩))
 (.branch 22
 (.leaf (⟨8, by decide⟩))
 (.leaf (⟨9, by decide⟩))))
 (.branch 25
 (.branch 24
 (.leaf (⟨10, by decide⟩))
 (.leaf (⟨11, by decide⟩)))
 (.branch 26
 (.leaf (⟨12, by decide⟩))
 (.leaf (⟨13, by decide⟩)))))))
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record005.l := originalLeafTable.get j.val
def orbitWordTable : ConcreteGrowth.Table (List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record005.g)) :=
(.branch 13
 (.branch 6
 (.branch 3
 (.branch 1
 (.leaf ([]))
 (.branch 2
 (.leaf ([]))
 (.leaf ([]))))
 (.branch 4
 (.leaf ([]))
 (.branch 5
 (.leaf ([]))
 (.leaf ([])))))
 (.branch 9
 (.branch 7
 (.leaf ([]))
 (.branch 8
 (.leaf ([]))
 (.leaf ([]))))
 (.branch 11
 (.branch 10
 (.leaf ([]))
 (.leaf ([])))
 (.branch 12
 (.leaf ([]))
 (.leaf ([]))))))
 (.branch 20
 (.branch 16
 (.branch 14
 (.leaf ([]))
 (.branch 15
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩]))))
 (.branch 18
 (.branch 17
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 19
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))))
 (.branch 23
 (.branch 21
 (.leaf ([⟨1, by decide⟩]))
 (.branch 22
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩]))))
 (.branch 25
 (.branch 24
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 26
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))))))
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record005.g) := orbitWordTable.get j.val
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record005.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record005.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record005 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record005_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record005 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record005_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record005_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00011.record005

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00011.record029
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "398d52ac5b31ca73523caaac6a9a958768b86e87b913c7895a719a659959715a54b51d70da354d4b4ad1b61d4749d38f13a4d5334cb31cf0ba2d4b1ae1b46c9b19e1715c3783c4f0bc1fc5154c3292a28aa544a951465454554342d28c6324c5322c2b"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "d369b69a6db6db6db49b49a4934d34924d34da4d36d3249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record029 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record029 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record029.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record029.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record029.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 28), (facetIndex 33), (facetIndex 68), (facetIndex 70)]))
 (.leaf ([(facetIndex 43), (facetIndex 54), (facetIndex 74), (facetIndex 77)])))
 (.branch 3
 (.leaf ([(facetIndex 25), (facetIndex 35), (facetIndex 37), (facetIndex 38)]))
 (.leaf ([(facetIndex 21), (facetIndex 45), (facetIndex 46), (facetIndex 47)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 39), (facetIndex 50)]))
 (.leaf ([(facetIndex 31), (facetIndex 36), (facetIndex 41)])))
 (.branch 7
 (.leaf ([(facetIndex 27), (facetIndex 51), (facetIndex 55)]))
 (.leaf ([(facetIndex 48)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "8040000000000000c40d076d8228895400a00c10018000000000000000"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 22), (facetIndex 32), (facetIndex 59)]))
 (.leaf ([(facetIndex 24), (facetIndex 52), (facetIndex 61)])))
 (.branch 3
 (.leaf ([(facetIndex 66), (facetIndex 71)]))
 (.branch 4
 (.leaf ([(facetIndex 64), (facetIndex 75)]))
 (.leaf ([(facetIndex 67), (facetIndex 72)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 65), (facetIndex 76)]))
 (.leaf ([(facetIndex 20), (facetIndex 29), (facetIndex 30), (facetIndex 42), (facetIndex 56)])))
 (.branch 8
 (.leaf ([(facetIndex 44), (facetIndex 63), (facetIndex 69), (facetIndex 73), (facetIndex 78)]))
 (.branch 9
 (.leaf ([(facetIndex 23), (facetIndex 34), (facetIndex 49), (facetIndex 57), (facetIndex 60)]))
 (.leaf ([(facetIndex 26), (facetIndex 40), (facetIndex 53), (facetIndex 58), (facetIndex 62)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "70530742070425379180986009100800007060900000800066009018006z14;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1, 2, 3]
def grouped2_0002 : List Nat := [4]
def grouped2_0003 : List Nat := [4, 5]
def grouped2_0004 : List Nat := [4, 5, 6, 7]
def grouped2_0005 : List Nat := [5]
def grouped2_0006 : List Nat := [6]
def grouped2_0007 : List Nat := [6, 7]
def grouped2_0008 : List Nat := [7]
def grouped3_0009 : List Nat := [0]
def grouped3_0010 : List Nat := [0, 1]
def grouped3_0011 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0013 : List Nat := [1]
def grouped3_0014 : List Nat := [2]
def grouped3_0015 : List Nat := [2, 3, 4]
def grouped3_0016 : List Nat := [3]
def grouped3_0017 : List Nat := [3, 4]
def grouped3_0018 : List Nat := [4]
def grouped3_0019 : List Nat := [5]
def grouped3_0020 : List Nat := [5, 6]
def grouped3_0021 : List Nat := [5, 6, 7, 8, 9]
def grouped3_0022 : List Nat := [6]
def grouped3_0023 : List Nat := [7]
def grouped3_0024 : List Nat := [7, 8, 9]
def grouped3_0025 : List Nat := [8]
def grouped3_0026 : List Nat := [8, 9]
def grouped3_0027 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record029 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record029_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00011.record029" "{\"atoms\":[{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":7,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":4,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":5,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00011.record029" 75

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00011.record029" "{\"ridges\":[[2,82],[4,98],[15,522],[16,656],[17,524],[17,776],[19,784],[20,30],[23,519],[25,82],[26,519],[27,98],[27,100],[29,282],[30,530],[31,98],[32,330],[34,771],[35,82],[37,82],[38,82],[39,530],[39,656],[40,771],[41,98],[42,156],[49,645],[50,524],[50,776],[53,645],[54,784],[56,408],[57,648],[58,776],[60,897],[62,897],[63,30],[65,550],[67,582],[69,282],[69,530],[70,522],[72,834],[73,156],[74,532],[76,676],[77,784],[78,408],[78,776]],\"owners\":[[2,82,[66,67,71,72],[25,35,37,38]],[25,82,[71,72],[2,35,37,38,66,67]],[35,82,[67,72],[2,25,37,38,66,71]],[37,82,[66,67,72],[2,25,35,38,71]],[38,82,[66,67,71],[2,25,35,37,72]],[4,98,[64,66,71],[27,31,35,41]],[27,98,[71],[4,31,35,41,64,66]],[31,98,[66,71],[4,27,35,41,64]],[41,98,[64,66],[4,27,31,35,71]],[27,100,[75],[10,45,51,55,64,66]],[15,522,[23,30,34,63,65,69],[33,68,70]],[70,522,[23,30,34,63,69],[15,33,65,68]],[57,648,[15,70,76],[33,49,60,68,73,78]],[30,530,[16,67,72],[26,39,40,63,68,69]],[39,530,[63,67,69,72],[16,26,30,40,68]],[69,530,[16,26,39,67],[30,40,63,68,72]],[16,656,[53,57,62,73,78],[39,68]],[39,656,[73,78],[16,53,57,62,68]],[17,524,[23,44,49,63,65,73,76],[50,74]],[50,524,[63,65,73,76],[17,23,44,49,74]],[17,776,[34,58,60,69,78],[50,74]],[50,776,[69,78],[17,34,58,60,74]],[58,776,[17],[34,50,60,69,74,78]],[78,776,[17,34,50],[58,60,69,74]],[74,532,[26,53,67],[19,44,54,63,73,77]],[19,784,[40,58,62,69,72,78],[54,74,77]],[54,784,[69,72,78],[19,40,58,62,74,77]],[77,784,[40,58,62,69,78],[19,54,72,74]],[20,30,[63],[]],[63,30,[20],[]],[23,519,[26],[]],[26,519,[23],[]],[29,282,[69],[]],[69,282,[29],[]],[32,330,[],[]],[34,771,[40],[]],[40,771,[34],[]],[42,156,[73],[]],[73,156,[42],[]],[49,645,[53],[]],[53,645,[49],[]],[56,408,[78],[]],[78,408,[56],[]],[60,897,[62],[]],[62,897,[60],[]],[65,550,[],[]],[67,582,[],[]],[72,834,[],[]],[76,676,[],[]]],\"edges\":[[13,[2,4,22,25,27,31,32,35,37,38,41,64,66,67,71,72]],[44,[17,19,34,40,50,54,58,60,62,69,72,74,77,78]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00011.record029" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00011.record029\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-14,-9],[-14,-11],[-22,-14],[-25,-9],[-25,-17],[-27,-14],[-27,-25],[-29,-26],[-30,-14],[-32,-26],[-35,-7],[-35,-13],[-35,-24],[-35,-33],[-36,-25],[-37,-14],[-43,-34],[-47,-35],[-47,-43],[-49,-26],[-52,-25],[-52,-35],[-52,-38],[-52,-47],[-1,41,42,45,46],[-10,45,46],[-18,42,46],[-19,41,42,46],[-20,41,42,45],[-2,39,41,45],[-12,45],[-15,41,45],[-23,39,41],[-12,49],[-3,9,14,17,38,40,43],[-44,9,14,17,38,43],[-34,3,44,50],[-14,4,42,46],[-21,38,42,43,46],[-43,4,11,21,42],[-4,30,34,37,47,52],[-21,47,52],[-5,9,25,27,38,40,47,50],[-28,38,40,47,50],[-5,17,35,36,43,52],[-28,43,52],[-35,5],[-52,5,17,28],[-48,11,30,42],[-6,22,35,37,43,46,52],[-31,43,46,52],[-51,22,35,37,43,52],[-7,38],[-38,7],[-9,11],[-11,9],[-13,43],[-43,13],[-16],[-17,22],[-22,17],[-24,47],[-47,24],[-27,30],[-30,27],[-33,52],[-52,33],[-36,37],[-37,36],[-40],[-42],[-46],[-50],[-53,21,28],[-54,12,29,32],[-55,26],[-56,53],[-57,54],[-57,55],[-58,56,57],[-59,58],[59],[-8,60],[-41,61],[-45,61],[-39,62],[-63,7,13,14,24,33],[-7,63],[-13,63],[-14,63],[-24,63],[-33,63],[-64,25,38,43,47,52],[-25,64],[-38,64],[-43,64],[-47,64],[-52,64],[-65,9,17,27,34,36],[-9,65],[-17,65],[-27,65],[-34,65],[-36,65],[-66,11,22,30,35,37],[-11,66],[-22,66],[-30,66],[-35,66],[-37,66],[-60,67],[-62,68],[-68,69],[-61,69],[-69,70],[-67,70],[-63,71],[-72,65],[-72,66],[-65,-66,72],[-73,64],[-73,72],[-64,-72,73],[-71,-73,74],[-70,-74,75],[-75],[1,2,8,10,12,15,16,18,19,20,23,39,41,42,45,46],[5,6,17,22,28,31,35,36,37,43,46,48,51,52]],\"atoms\":[{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":30,\"b\":23},{\"tag\":\"incompatible\",\"a\":30,\"b\":26},{\"tag\":\"incompatible\",\"a\":40,\"b\":30},{\"tag\":\"incompatible\",\"a\":44,\"b\":23},{\"tag\":\"incompatible\",\"a\":44,\"b\":34},{\"tag\":\"incompatible\",\"a\":49,\"b\":30},{\"tag\":\"incompatible\",\"a\":49,\"b\":44},{\"tag\":\"incompatible\",\"a\":51,\"b\":48},{\"tag\":\"incompatible\",\"a\":53,\"b\":30},{\"tag\":\"incompatible\",\"a\":55,\"b\":48},{\"tag\":\"incompatible\",\"a\":58,\"b\":20},{\"tag\":\"incompatible\",\"a\":58,\"b\":29},{\"tag\":\"incompatible\",\"a\":58,\"b\":42},{\"tag\":\"incompatible\",\"a\":58,\"b\":56},{\"tag\":\"incompatible\",\"a\":60,\"b\":44},{\"tag\":\"incompatible\",\"a\":62,\"b\":30},{\"tag\":\"incompatible\",\"a\":69,\"b\":57},{\"tag\":\"incompatible\",\"a\":73,\"b\":58},{\"tag\":\"incompatible\",\"a\":73,\"b\":69},{\"tag\":\"incompatible\",\"a\":75,\"b\":48},{\"tag\":\"incompatible\",\"a\":78,\"b\":44},{\"tag\":\"incompatible\",\"a\":78,\"b\":58},{\"tag\":\"incompatible\",\"a\":78,\"b\":63},{\"tag\":\"incompatible\",\"a\":78,\"b\":73},{\"tag\":\"mate\",\"ridge\":82,\"a\":2,\"owners\":[66,67,71,72]},{\"tag\":\"mate\",\"ridge\":82,\"a\":25,\"owners\":[71,72]},{\"tag\":\"mate\",\"ridge\":82,\"a\":35,\"owners\":[67,72]},{\"tag\":\"mate\",\"ridge\":82,\"a\":37,\"owners\":[66,67,72]},{\"tag\":\"mate\",\"ridge\":82,\"a\":38,\"owners\":[66,67,71]},{\"tag\":\"mate\",\"ridge\":98,\"a\":4,\"owners\":[64,66,71]},{\"tag\":\"mate\",\"ridge\":98,\"a\":27,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":98,\"a\":31,\"owners\":[66,71]},{\"tag\":\"mate\",\"ridge\":98,\"a\":41,\"owners\":[64,66]},{\"tag\":\"mate\",\"ridge\":100,\"a\":27,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":522,\"a\":15,\"owners\":[23,30,34,63,65,69]},{\"tag\":\"mate\",\"ridge\":522,\"a\":70,\"owners\":[23,30,34,63,69]},{\"tag\":\"mate\",\"ridge\":648,\"a\":57,\"owners\":[15,70,76]},{\"tag\":\"mate\",\"ridge\":530,\"a\":30,\"owners\":[16,67,72]},{\"tag\":\"mate\",\"ridge\":530,\"a\":39,\"owners\":[63,67,69,72]},{\"tag\":\"mate\",\"ridge\":530,\"a\":69,\"owners\":[16,26,39,67]},{\"tag\":\"mate\",\"ridge\":656,\"a\":16,\"owners\":[53,57,62,73,78]},{\"tag\":\"mate\",\"ridge\":656,\"a\":39,\"owners\":[73,78]},{\"tag\":\"mate\",\"ridge\":524,\"a\":17,\"owners\":[23,44,49,63,65,73,76]},{\"tag\":\"mate\",\"ridge\":524,\"a\":50,\"owners\":[63,65,73,76]},{\"tag\":\"mate\",\"ridge\":776,\"a\":17,\"owners\":[34,58,60,69,78]},{\"tag\":\"mate\",\"ridge\":776,\"a\":50,\"owners\":[69,78]},{\"tag\":\"mate\",\"ridge\":776,\"a\":58,\"owners\":[17]},{\"tag\":\"mate\",\"ridge\":776,\"a\":78,\"owners\":[17,34,50]},{\"tag\":\"mate\",\"ridge\":532,\"a\":74,\"owners\":[26,53,67]},{\"tag\":\"mate\",\"ridge\":784,\"a\":19,\"owners\":[40,58,62,69,72,78]},{\"tag\":\"mate\",\"ridge\":784,\"a\":54,\"owners\":[69,72,78]},{\"tag\":\"mate\",\"ridge\":784,\"a\":77,\"owners\":[40,58,62,69,78]},{\"tag\":\"mate\",\"ridge\":30,\"a\":20,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":30,\"a\":63,\"owners\":[20]},{\"tag\":\"mate\",\"ridge\":519,\"a\":23,\"owners\":[26]},{\"tag\":\"mate\",\"ridge\":519,\"a\":26,\"owners\":[23]},{\"tag\":\"mate\",\"ridge\":282,\"a\":29,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":282,\"a\":69,\"owners\":[29]},{\"tag\":\"mate\",\"ridge\":330,\"a\":32,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":771,\"a\":34,\"owners\":[40]},{\"tag\":\"mate\",\"ridge\":771,\"a\":40,\"owners\":[34]},{\"tag\":\"mate\",\"ridge\":156,\"a\":42,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":156,\"a\":73,\"owners\":[42]},{\"tag\":\"mate\",\"ridge\":645,\"a\":49,\"owners\":[53]},{\"tag\":\"mate\",\"ridge\":645,\"a\":53,\"owners\":[49]},{\"tag\":\"mate\",\"ridge\":408,\"a\":56,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":408,\"a\":78,\"owners\":[56]},{\"tag\":\"mate\",\"ridge\":897,\"a\":60,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":897,\"a\":62,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":550,\"a\":65,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":582,\"a\":67,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":834,\"a\":72,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":676,\"a\":76,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[39,50],\"full_literals\":[-53,21,28]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[27,51,55],\"full_literals\":[-54,12,29,32]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[48],\"full_literals\":[-55,26]},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-56,53,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0007\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-57,54,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-57,false,55],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-58,56,57],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-59,false,58],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":7,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":22,\"full_literals\":[-8,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":66,\"full_literals\":[-41,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":71,\"full_literals\":[-45,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":64,\"full_literals\":[-39,62]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[20,29,30,42,56],\"full_literals\":[-63,7,13,14,24,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":20,\"full_literals\":[-7,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":29,\"full_literals\":[-13,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":30,\"full_literals\":[-14,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":42,\"full_literals\":[-24,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":56,\"full_literals\":[-33,63]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[44,63,69,73,78],\"full_literals\":[-64,25,38,43,47,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":44,\"full_literals\":[-25,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":63,\"full_literals\":[-38,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":69,\"full_literals\":[-43,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":73,\"full_literals\":[-47,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":78,\"full_literals\":[-52,64]},{\"tag\":\"group_or\",\"kind\":3,\"index\":8,\"members\":[23,34,49,57,60],\"full_literals\":[-65,9,17,27,34,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":23,\"full_literals\":[-9,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":34,\"full_literals\":[-17,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":49,\"full_literals\":[-27,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":57,\"full_literals\":[-34,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":60,\"full_literals\":[-36,65]},{\"tag\":\"group_or\",\"kind\":3,\"index\":9,\"members\":[26,40,53,58,62],\"full_literals\":[-66,11,22,30,35,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":26,\"full_literals\":[-11,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":40,\"full_literals\":[-22,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":53,\"full_literals\":[-30,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":58,\"full_literals\":[-35,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":62,\"full_literals\":[-37,66]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-60,false,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-62,false,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-68,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-61,false,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-69,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-67,false,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-63,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-72,65,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-72,false,66],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-65,-66,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-73,64,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-73,false,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-64,-72,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-71,-73,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":4,\"direction\":\"forward\",\"full_literals\":[-70,-74,75],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":4,\"grouped\":true},{\"tag\":\"edge\",\"edge\":13,\"owners\":[2,4,22,25,27,31,32,35,37,38,41,64,66,67,71,72]},{\"tag\":\"edge\",\"edge\":44,\"owners\":[17,19,34,40,50,54,58,60,62,69,72,74,77,78]}]}"
  "129 -18 0 72 71 27 0\n130 58 0 82 81 0\n131 1 2 8 10 12 15 19 20 23 39 41 45 0 59 129 71 72 127 0\n132 5 6 17 22 28 31 35 36 37 43 48 51 52 0 72 128 0\n133 70 0 72 71 115 116 113 114 111 112 84 85 83 86 28 33 26 31 29 32 25 30 131 0\n134 -74 0 133 126 125 0\n135 -73 0 134 70 73 121 122 124 118 117 88 89 90 91 92 54 58 63 67 93 4 5 7 15 36 35 99 37 0\n136 -72 -63 0 135 73 70 119 123 94 95 96 97 98 53 57 62 66 87 1 2 3 6 9 16 43 105 47 0\n137 -66 -63 0 72 71 136 120 100 101 102 103 104 56 61 65 69 105 11 12 13 14 18 22 87 41 38 0\n138 43 52 66 0 71 72 110 68 106 108 49 107 60 109 50 52 45 46 51 132 0\n139 47 52 66 0 71 138 17 110 108 106 42 40 41 0\n140 52 66 0 138 139 19 0\n141 66 0 73 70 106 107 108 55 60 64 140 21 23 24 43 44 48 0\n142 -63 0 141 137 0\n143 -7 0 142 88 0\n144 -13 0 142 89 0\n145 -24 0 142 91 0\n146 -38 0 143 54 0\n147 -43 0 144 58 0\n148 -47 0 145 63 0\n149 -21 0 146 71 147 72 39 0\n150 -28 0 146 70 148 73 44 0\n151 -53 0 150 149 74 0\n152 -56 0 151 77 0\n153 57 0 152 130 80 0\n154 54 0 153 78 0\n155 55 0 153 79 0\n156 26 0 155 76 0\n157 -29 0 156 8 0\n158 -32 0 156 10 0\n159 -49 0 156 20 0\n160 12 0 157 154 158 75 0\n161 0 160 159 34 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record029.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record029.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record029.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record029.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record029 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record029.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record029.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record029.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record029.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record029 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record029_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record029_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record029_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record029_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record029_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record029_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record029_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record029 Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record029_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record029_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00011.record029_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00011.record029
