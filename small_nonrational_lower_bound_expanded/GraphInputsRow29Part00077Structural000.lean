module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow29Part00077Data
public import GraphInputsRow29Part00077Frames
public import GraphInputsRow29Part00077Leaves
public import GraphInputsRow29Part00077Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00077.record006
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record006
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨51, by decide⟩, ⟨54, by decide⟩, ⟨57, by decide⟩, ⟨62, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨79, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨87, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), 2251902892900352, (certNat% 4), (certNat% 5), (certNat% 6)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), 4755801206503243776, 1568669696, (certNat% 8), (certNat% 9)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), (certNat% 3), 2264993953218560, (certNat% 11), (certNat% 12), (certNat% 6)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), 1956642816, (certNat% 14), 2265097032433664, 212755499974656, (certNat% 15), (certNat% 16)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c5 c0
  c6
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record006_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record006_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00077.record006

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00077.record022
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record022
def vertexColumn : Fields := ⟨10, (certNat% 17)⟩
def kindColumn : Fields := ⟨3, (certNat% 18)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [1, 2, 3, 4]
def candidates : List (Fin raw.n) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), (certNat% 20), (certNat% 21), 17884512256000, 35769024512000, 144115188075855872]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .size 1
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), 2251800082120704]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 23), (certNat% 24), (certNat% 25)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨98, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨8, by decide⟩ c1 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨20, by decide⟩ c1 c8
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c2 c9
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨77, by decide⟩ c2 c10
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨98, by decide⟩ c6 c11
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 26), (certNat% 27), (certNat% 25), (certNat% 28)]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c14 c7
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c11 c3
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), 35218731827200, (certNat% 25)]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨98, by decide⟩ c17 c16
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 30), (certNat% 25), (certNat% 28), 35768487641088]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 31), (certNat% 28), (certNat% 32), 275146342400, 35769024512000]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c21 c20
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c22 c15
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 33), 35769024512000, (certNat% 34), (certNat% 35), 2392812448382976, (certNat% 36)]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨96, by decide⟩ c24 c23
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 37), (certNat% 38), (certNat% 39), (certNat% 40), (certNat% 41)]
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 42), (certNat% 43), (certNat% 44), (certNat% 34), (certNat% 45)]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 46), (certNat% 43), (certNat% 47), (certNat% 48), (certNat% 49), (certNat% 50)]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨98, by decide⟩ c28 c27
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 51), (certNat% 35), (certNat% 21), (certNat% 52), 1161686111223808, 4503599627370496]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 53), (certNat% 21), 35769024512000, 288371116055986176, (certNat% 54), (certNat% 55)]
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 56), (certNat% 57), (certNat% 21), (certNat% 58), 1143510078062592, 35768487641088]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 59), (certNat% 35), (certNat% 60), 108086391124000768, 1179261117399040, 4503599627370496]
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 61), (certNat% 34), (certNat% 62), 17609433022464, 1125900712148992, 35768487641088]
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 63), (certNat% 48), (certNat% 62), (certNat% 49), (certNat% 64), 1143510078062592, 35768487641088]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨98, by decide⟩ c35 c34
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c36 c33
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨96, by decide⟩ c37 c32
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c38 c31
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c39 c30
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c40 c29
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c41 c26
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c42 c25
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c43 c0
  c44
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record022_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record022_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record022_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record022_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record022_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record022_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record022_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record022_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record022_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00077.record022

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00077.record023
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "394cd274cb16c3707c9cb2a6a8da2e87ae1b2699a96958d68d876c398e33a2e4b86e2785e0fb316c5a95a4d92e479c9565c5595356354d475534cd4b46d2745d0f72368cd38ccb362ccb4acab26c5b0ef0761cc789d2719e170dd0f0bc1f632321c86a858961588e13871625291a585254554348d1346324c530cc8b12c2b21c4705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db6d36da6da4926936926da4da6da4da49249b69249249349b492489249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record023 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record023 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record023.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record023.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record023.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 53), (facetIndex 69), (facetIndex 70)]))
 (.leaf ([(facetIndex 75), (facetIndex 93), (facetIndex 94)])))
 (.branch 3
 (.leaf ([(facetIndex 98), (facetIndex 99)]))
 (.leaf ([(facetIndex 61), (facetIndex 65), (facetIndex 73), (facetIndex 104)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 36), (facetIndex 40), (facetIndex 51), (facetIndex 83), (facetIndex 91)]))
 (.leaf ([(facetIndex 52), (facetIndex 79), (facetIndex 95), (facetIndex 96)])))
 (.branch 7
 (.leaf ([(facetIndex 37), (facetIndex 66), (facetIndex 80), (facetIndex 89), (facetIndex 90), (facetIndex 103)]))
 (.branch 8
 (.leaf ([(facetIndex 62), (facetIndex 100), (facetIndex 101), (facetIndex 102)]))
 (.leaf ([(facetIndex 67), (facetIndex 74)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "367772205511046600000400650001830000086300730000000054000000000040064z24;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0, 1]
def grouped3_0001 : List Nat := [0, 1, 2, 3]
def grouped3_0003 : List Nat := [2]
def grouped3_0004 : List Nat := [2, 3]
def grouped3_0005 : List Nat := [3]
def grouped3_0006 : List Nat := [4]
def grouped3_0007 : List Nat := [4, 5]
def grouped3_0008 : List Nat := [4, 5, 6, 7, 8]
def grouped3_0009 : List Nat := [5]
def grouped3_0010 : List Nat := [6]
def grouped3_0011 : List Nat := [6, 7, 8]
def grouped3_0012 : List Nat := [7]
def grouped3_0013 : List Nat := [7, 8]
def grouped3_0014 : List Nat := [8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record023 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record023_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00077.record023" "{\"atoms\":[{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00077.record023" 36

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00077.record023" "{\"ridges\":[[36,294],[40,771],[40,772],[51,418],[52,800],[61,308],[65,772],[65,785],[67,800],[73,432],[74,785],[79,294],[83,772],[83,778],[90,772],[91,898],[95,418],[96,778],[96,800],[101,556],[101,800],[103,308],[103,772],[103,800],[104,912]],\"owners\":[[36,294,[79,90],[]],[79,294,[36,90],[]],[40,771,[52],[]],[40,772,[101,103,104],[65,67,83,90,91]],[65,772,[83,90,91,101],[40,67,103,104]],[83,772,[65,67,103,104],[40,90,91,101]],[90,772,[65,104],[40,67,83,91,101,103]],[103,772,[40,83,91],[65,67,90,101,104]],[51,418,[95],[]],[95,418,[51],[]],[52,800,[101,103],[67,74,90,96]],[67,800,[96],[52,74,90,101,103]],[96,800,[67,74,103],[52,90,101]],[101,800,[52,74],[67,90,96,103]],[103,800,[52,96],[67,74,90,101]],[61,308,[103],[]],[103,308,[61],[]],[65,785,[74],[]],[74,785,[65],[]],[73,432,[],[]],[101,556,[80],[]],[83,778,[96],[]],[96,778,[83],[]],[91,898,[],[]],[104,912,[],[]]],\"edges\":[[44,[40,52,65,67,74,83,90,91,96,101,103,104]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00077.record023" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00077.record023\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,10,13],[-10,1,13],[-2,4],[-2,17,18,19],[-6,12,13,14,17],[-12,6,7,18,19],[-13,6,19],[-18,2,12,14],[-3,15],[-15,3],[-4,17,18],[-7,16],[-16,7,9,18],[-17,4,9],[-18,4,16],[-5,18],[-18,5],[-6,9],[-9,6],[-8],[-17,11],[-12,16],[-16,12],[-14],[-19],[-20,5,6,8,19],[-5,20],[-6,20],[-21,1,2,3,12,14],[-1,21],[-2,21],[-3,21],[-12,21],[-22,4,10,15,16],[-4,22],[-10,22],[-15,22],[-16,22],[-11,23],[-13,23],[-17,24],[-7,25],[-9,25],[-20,26],[-26,27],[-28,21,22],[-22,28],[-21,28],[-21,-22,29],[-25,30],[-24,30],[-24,-25,31],[-30,32],[-31,33],[-23,-30,33],[-33,34],[-28,-33,35],[-29,34],[-29,-32,35],[-35,36],[-27,-34,36],[-36],[2,4,6,7,9,12,13,14,16,17,18,19]],\"atoms\":[{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":294,\"a\":36,\"owners\":[79,90]},{\"tag\":\"mate\",\"ridge\":294,\"a\":79,\"owners\":[36,90]},{\"tag\":\"mate\",\"ridge\":771,\"a\":40,\"owners\":[52]},{\"tag\":\"mate\",\"ridge\":772,\"a\":40,\"owners\":[101,103,104]},{\"tag\":\"mate\",\"ridge\":772,\"a\":65,\"owners\":[83,90,91,101]},{\"tag\":\"mate\",\"ridge\":772,\"a\":83,\"owners\":[65,67,103,104]},{\"tag\":\"mate\",\"ridge\":772,\"a\":90,\"owners\":[65,104]},{\"tag\":\"mate\",\"ridge\":772,\"a\":103,\"owners\":[40,83,91]},{\"tag\":\"mate\",\"ridge\":418,\"a\":51,\"owners\":[95]},{\"tag\":\"mate\",\"ridge\":418,\"a\":95,\"owners\":[51]},{\"tag\":\"mate\",\"ridge\":800,\"a\":52,\"owners\":[101,103]},{\"tag\":\"mate\",\"ridge\":800,\"a\":67,\"owners\":[96]},{\"tag\":\"mate\",\"ridge\":800,\"a\":96,\"owners\":[67,74,103]},{\"tag\":\"mate\",\"ridge\":800,\"a\":101,\"owners\":[52,74]},{\"tag\":\"mate\",\"ridge\":800,\"a\":103,\"owners\":[52,96]},{\"tag\":\"mate\",\"ridge\":308,\"a\":61,\"owners\":[103]},{\"tag\":\"mate\",\"ridge\":308,\"a\":103,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":785,\"a\":65,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":785,\"a\":74,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":432,\"a\":73,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":556,\"a\":101,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":778,\"a\":83,\"owners\":[96]},{\"tag\":\"mate\",\"ridge\":778,\"a\":96,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":898,\"a\":91,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":912,\"a\":104,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[61,65,73,104],\"full_literals\":[-20,5,6,8,19]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":61,\"full_literals\":[-5,20]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":65,\"full_literals\":[-6,20]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[36,40,51,83,91],\"full_literals\":[-21,1,2,3,12,14]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":36,\"full_literals\":[-1,21]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":40,\"full_literals\":[-2,21]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":51,\"full_literals\":[-3,21]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":83,\"full_literals\":[-12,21]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[52,79,95,96],\"full_literals\":[-22,4,10,15,16]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":52,\"full_literals\":[-4,22]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":79,\"full_literals\":[-10,22]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":95,\"full_literals\":[-15,22]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":96,\"full_literals\":[-16,22]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":80,\"full_literals\":[-11,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":90,\"full_literals\":[-13,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":101,\"full_literals\":[-17,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":67,\"full_literals\":[-7,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":74,\"full_literals\":[-9,25]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-20,26],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-26,27],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-28,21,22],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-22,28],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-21,false,28],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-21,-22,29],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-25,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-24,false,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-24,-25,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-30,32],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-31,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-23,-30,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-33,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-28,-33,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-29,false,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-29,-32,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-35,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-27,-34,36],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":44,\"owners\":[40,52,65,67,74,83,90,91,96,101,103,104]}]}"
  "64 -20 5 6 0 20 25 26 0\n65 -21 1 2 3 12 0 24 29 0\n66 -35 0 62 60 0\n67 2 4 6 7 9 12 13 16 17 18 0 24 25 63 0\n68 28 20 0 25 28 19 7 27 17 47 48 35 38 31 33 14 12 67 0\n69 22 20 0 25 68 28 7 35 36 37 38 46 3 1 9 22 65 0\n70 30 20 0 25 28 19 7 27 17 50 51 42 41 13 6 4 11 67 0\n71 20 0 25 66 27 28 17 7 68 57 69 70 53 55 59 39 49 21 30 32 33 11 2 10 23 34 0\n72 26 0 71 44 0\n73 27 0 72 45 0\n74 -34 0 73 62 61 0\n75 -33 0 74 56 0\n76 -29 0 74 58 0\n77 -31 0 75 54 0\n78 -6 13 12 0 77 24 5 18 41 43 52 0\n79 -18 16 0 24 76 22 8 15 31 35 49 0\n80 -6 12 0 75 78 18 40 43 55 50 0\n81 16 0 71 22 79 16 64 80 0\n82 12 0 81 23 0\n83 22 0 81 38 0\n84 21 0 82 33 0\n85 0 84 83 76 49 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record023.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record023.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record023.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record023.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record023 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record023.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record023.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record023.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record023.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record023 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record023_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record023_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record023_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record023_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record023_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record023_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record023_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record023 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record023_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record023_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record023_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00077.record023

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00077.record033
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3b0ce278ad2743d26ce4ab29c8f29ab1a9695a8e87ae1aa6998e6a5a5635a362d876c398e93a2e2b86ecc5b13c7296a719566394e479394d58d4b51d70d6362d2b4e3c4d5334e332cc73c2d8b52e2b2ac6b86d1b16c3bc1d8731e2729c6785c9715c3783d0f23c2f8b06cc4992c2a0e139912c4711a4a51944d0b58344c9314d0b12c8711c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6da4db69b6db6db6db4d269a4db6da4da4da4d24d249369a4da4d2693492249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record033 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record033 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record033.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record033.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record033.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 6
 (.branch 3
 (.branch 1
 (.leaf ([(facetIndex 37), (facetIndex 57), (facetIndex 89)]))
 (.branch 2
 (.leaf ([(facetIndex 43), (facetIndex 69), (facetIndex 78)]))
 (.leaf ([(facetIndex 38), (facetIndex 41), (facetIndex 65), (facetIndex 67), (facetIndex 93)]))))
 (.branch 4
 (.leaf ([(facetIndex 66), (facetIndex 90), (facetIndex 92), (facetIndex 104), (facetIndex 105)]))
 (.branch 5
 (.leaf ([(facetIndex 70), (facetIndex 106)]))
 (.leaf ([(facetIndex 28), (facetIndex 31), (facetIndex 62), (facetIndex 84), (facetIndex 85)])))))
 (.branch 9
 (.branch 7
 (.leaf ([(facetIndex 61), (facetIndex 80), (facetIndex 83), (facetIndex 102), (facetIndex 103)]))
 (.branch 8
 (.leaf ([(facetIndex 54), (facetIndex 81), (facetIndex 101)]))
 (.leaf ([(facetIndex 34), (facetIndex 75), (facetIndex 82), (facetIndex 86), (facetIndex 87), (facetIndex 88), (facetIndex 91)]))))
 (.branch 10
 (.leaf ([(facetIndex 44), (facetIndex 95), (facetIndex 96), (facetIndex 98)]))
 (.branch 11
 (.leaf ([(facetIndex 50), (facetIndex 97)]))
 (.leaf ([(facetIndex 58), (facetIndex 68), (facetIndex 73)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "433667009a99023830888556876010080b0041b232005600b0007000a0000091020020008005005z1c;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 12
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1, 2]
def grouped3_0002 : List Nat := [0, 1, 2, 3, 4, 5]
def grouped3_0004 : List Nat := [1]
def grouped3_0005 : List Nat := [1, 2]
def grouped3_0006 : List Nat := [2]
def grouped3_0007 : List Nat := [3]
def grouped3_0008 : List Nat := [3, 4, 5]
def grouped3_0009 : List Nat := [4]
def grouped3_0010 : List Nat := [4, 5]
def grouped3_0011 : List Nat := [5]
def grouped3_0012 : List Nat := [6]
def grouped3_0013 : List Nat := [6, 7, 8]
def grouped3_0014 : List Nat := [6, 7, 8, 9, 10, 11]
def grouped3_0015 : List Nat := [7]
def grouped3_0016 : List Nat := [7, 8]
def grouped3_0017 : List Nat := [8]
def grouped3_0018 : List Nat := [9]
def grouped3_0019 : List Nat := [9, 10, 11]
def grouped3_0020 : List Nat := [10]
def grouped3_0021 : List Nat := [10, 11]
def grouped3_0022 : List Nat := [11]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record033 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record033_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00077.record033" "{\"atoms\":[{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group\",\"kind\":3,\"index\":10},{\"tag\":\"group\",\"kind\":3,\"index\":11},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0005\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00077.record033" 98

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00077.record033" "{\"ridges\":[[4,265],[12,164],[15,176],[19,776],[21,784],[23,552],[26,265],[33,164],[34,547],[40,265],[43,170],[45,265],[46,265],[47,265],[49,176],[50,560],[53,784],[55,164],[56,552],[58,773],[60,164],[61,533],[61,560],[63,164],[68,537],[69,424],[70,801],[71,176],[72,176],[73,801],[76,548],[76,552],[79,266],[80,54],[82,560],[83,212],[87,610],[88,674],[91,58],[91,560],[92,344],[93,600],[94,776],[94,784],[96,226],[97,560],[98,560],[98,674],[99,784],[100,552],[102,560],[102,596],[103,560],[103,660],[105,312],[106,928]],\"owners\":[[4,265,[57,58,65,67,68,69,70],[26,40,45,46,47]],[26,265,[65,67,68,69,70],[4,40,45,46,47,57,58]],[40,265,[57,58,69,70],[4,26,45,46,47,65,67,68]],[45,265,[57,58,65,68,69,70],[4,26,40,46,47,67]],[46,265,[58,65,67,68,70],[4,26,40,45,47,57,69]],[47,265,[57,65,67,69],[4,26,40,45,46,58,68,70]],[79,266,[4,40,45,46,92],[19,26,78,94]],[12,164,[75,81,86,88,101,103],[33,55,60,63]],[33,164,[101,103],[12,55,60,63,75,81,86,88]],[55,164,[81,86,88,101,103],[12,33,60,63,75]],[60,164,[75,86,88],[12,33,55,63,81,101,103]],[63,164,[75,81,88,103],[12,33,55,60,86,101]],[15,176,[81,96,98,101,103,106],[49,60,71,72]],[49,176,[101,103,106],[15,60,71,72,81,96,98]],[71,176,[81,98,103,106],[15,49,60,72,96,101]],[72,176,[81,96,98,101,103],[15,49,60,71,106]],[19,776,[58,68,70,105],[47,79,94]],[94,776,[58,70],[19,47,68,79,105]],[21,784,[68,73,105,106],[53,94,99]],[53,784,[105,106],[21,68,73,94,99]],[94,784,[73,106],[21,53,68,99,105]],[99,784,[68,73,105],[21,53,94,106]],[76,548,[61,102,103],[23,34,56,82,87,88,100]],[23,552,[44,66,70,91,95,104,105],[56,76,100]],[56,552,[91,95,104,105],[23,44,66,70,76,100]],[76,552,[66,70,104,105],[23,44,56,91,95,100]],[100,552,[44,66,70,91,105],[23,56,76,95,104]],[80,54,[28,81,82],[]],[61,533,[31],[]],[34,547,[44,50],[]],[58,773,[37],[]],[91,58,[38,90],[]],[68,537,[41,66],[]],[43,170,[75],[]],[50,560,[102,103,104,105,106],[61,66,73,82,91,97,98]],[61,560,[91,97,98,104,105,106],[50,66,73,82,102,103]],[82,560,[66,73,104,105,106],[50,61,91,97,98,102,103]],[91,560,[61,73,102,103,106],[50,66,82,97,98,104,105]],[97,560,[61,66,73,103,105,106],[50,82,91,98,102,104]],[98,560,[61,66,73,102,104,105],[50,82,91,97,103,106]],[102,560,[50,66,73,91,98,105,106],[61,82,97,103,104]],[103,560,[50,66,73,91,97,104,105],[61,82,98,102,106]],[96,226,[54,86],[]],[83,212,[62,101],[]],[105,312,[65],[]],[92,344,[67],[]],[69,424,[],[]],[70,801,[73],[]],[73,801,[70],[]],[102,596,[84],[]],[103,660,[85],[]],[87,610,[95,97],[]],[88,674,[98],[]],[98,674,[88],[]],[93,600,[104],[]],[106,928,[],[]]],\"edges\":[[28,[4,19,26,40,45,46,47,57,58,65,67,68,69,70,78,79,92,94,105]],[34,[21,31,41,50,53,61,66,68,73,82,84,85,91,93,94,97,98,99,102,103,104,105,106]],[36,[12,15,33,43,49,54,55,60,63,69,71,72,75,81,86,88,96,98,101,103,106]],[38,[23,34,44,50,56,61,66,70,73,76,82,87,88,91,95,97,98,100,102,103,104,105,106]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00077.record033" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00077.record033\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,27,28,33,35,36,37,38],[-7,33,35,36,37,38],[-14,27,28,37,38],[-18,27,28,33,36,37,38],[-19,28,33,35,36,38],[-20,27,33,35,37],[-45,1,14,18,19,57],[-2,42,47,52,54,66,68],[-10,66,68],[-25,47,52,54,66,68],[-29,42,52,54],[-32,42,47,54,68],[-3,47,61,63,66,68,71],[-21,66,68,71],[-39,47,63,68,71],[-40,47,61,63,66,68],[-4,28,36,38,70],[-59,28,38],[-5,36,41,70,71],[-23,70,71],[-59,41,71],[-64,36,41,70],[-43,30,67,68],[-6,17,34,38,56,60,69,70],[-26,56,60,69,70],[-43,34,38,69,70],[-65,17,34,38,56,70],[-46,8,47,48],[-30,9],[-11,17,22],[-28,12],[-56,13,55],[-36,15,34],[-16,42],[-22,67,68,69,70,71],[-30,56,62,63,69,70,71],[-48,34,41,69,70,71],[-56,30,41,67,68,71],[-62,30,34,41,68,70,71],[-63,30,34,41,67,69,70],[-67,22,34,41,56,63,70,71],[-68,22,34,41,56,62,69,70],[-61,24,52],[-49,31,66],[-70,33],[-57,35],[-37],[-38,41],[-41,38],[-67,50],[-68,51],[-53,60,62],[-54,63],[-63,54],[-58,69],[-71],[-12,72],[-27,72],[-44,73],[-13,74],[-15,74],[-33,74],[-35,74],[-34,75],[-55,75],[-69,75],[-70,75],[-38,76],[-8,77],[-9,77],[-31,77],[-50,77],[-51,77],[-78,30,46,49,67,68],[-30,78],[-67,78],[-68,78],[-24,79],[-47,79],[-66,79],[-42,80],[-48,80],[-52,80],[-54,80],[-56,80],[-17,81],[-60,81],[-63,81],[-22,82],[-62,82],[-28,83],[-36,83],[-41,83],[-74,84],[-73,84],[-84,85],[-72,85],[-77,86],[-76,86],[-86,87],[-75,87],[-75,-86,88],[-87,89],[-88,90],[-85,89],[-85,-87,90],[-80,91],[-79,91],[-92,78,91],[-91,92],[-78,92],[-78,-91,93],[-83,94],[-82,94],[-94,95],[-81,95],[-92,96],[-92,-95,97],[-93,97],[-89,-97,98],[-90,-96,98],[-98],[1,4,7,14,18,19,20,27,28,33,35,36,37,38,44,45,57,59,70],[5,9,15,22,23,30,34,36,41,48,50,51,56,58,59,62,63,64,67,68,69,70,71],[2,3,10,16,21,24,25,29,32,37,39,40,42,47,52,54,61,63,66,68,71],[6,11,17,22,26,30,34,38,41,43,48,53,54,56,60,62,63,65,67,68,69,70,71]],\"atoms\":[{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"facet\",\"index\":95},{\"tag\":\"facet\",\"index\":96},{\"tag\":\"facet\",\"index\":97},{\"tag\":\"facet\",\"index\":98},{\"tag\":\"facet\",\"index\":99},{\"tag\":\"facet\",\"index\":100},{\"tag\":\"facet\",\"index\":101},{\"tag\":\"facet\",\"index\":102},{\"tag\":\"facet\",\"index\":103},{\"tag\":\"facet\",\"index\":104},{\"tag\":\"facet\",\"index\":105},{\"tag\":\"facet\",\"index\":106},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group\",\"index\":10,\"kind\":3},{\"tag\":\"group\",\"index\":11,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":265,\"a\":4,\"owners\":[57,58,65,67,68,69,70]},{\"tag\":\"mate\",\"ridge\":265,\"a\":26,\"owners\":[65,67,68,69,70]},{\"tag\":\"mate\",\"ridge\":265,\"a\":40,\"owners\":[57,58,69,70]},{\"tag\":\"mate\",\"ridge\":265,\"a\":45,\"owners\":[57,58,65,68,69,70]},{\"tag\":\"mate\",\"ridge\":265,\"a\":46,\"owners\":[58,65,67,68,70]},{\"tag\":\"mate\",\"ridge\":265,\"a\":47,\"owners\":[57,65,67,69]},{\"tag\":\"mate\",\"ridge\":266,\"a\":79,\"owners\":[4,40,45,46,92]},{\"tag\":\"mate\",\"ridge\":164,\"a\":12,\"owners\":[75,81,86,88,101,103]},{\"tag\":\"mate\",\"ridge\":164,\"a\":33,\"owners\":[101,103]},{\"tag\":\"mate\",\"ridge\":164,\"a\":55,\"owners\":[81,86,88,101,103]},{\"tag\":\"mate\",\"ridge\":164,\"a\":60,\"owners\":[75,86,88]},{\"tag\":\"mate\",\"ridge\":164,\"a\":63,\"owners\":[75,81,88,103]},{\"tag\":\"mate\",\"ridge\":176,\"a\":15,\"owners\":[81,96,98,101,103,106]},{\"tag\":\"mate\",\"ridge\":176,\"a\":49,\"owners\":[101,103,106]},{\"tag\":\"mate\",\"ridge\":176,\"a\":71,\"owners\":[81,98,103,106]},{\"tag\":\"mate\",\"ridge\":176,\"a\":72,\"owners\":[81,96,98,101,103]},{\"tag\":\"mate\",\"ridge\":776,\"a\":19,\"owners\":[58,68,70,105]},{\"tag\":\"mate\",\"ridge\":776,\"a\":94,\"owners\":[58,70]},{\"tag\":\"mate\",\"ridge\":784,\"a\":21,\"owners\":[68,73,105,106]},{\"tag\":\"mate\",\"ridge\":784,\"a\":53,\"owners\":[105,106]},{\"tag\":\"mate\",\"ridge\":784,\"a\":94,\"owners\":[73,106]},{\"tag\":\"mate\",\"ridge\":784,\"a\":99,\"owners\":[68,73,105]},{\"tag\":\"mate\",\"ridge\":548,\"a\":76,\"owners\":[61,102,103]},{\"tag\":\"mate\",\"ridge\":552,\"a\":23,\"owners\":[44,66,70,91,95,104,105]},{\"tag\":\"mate\",\"ridge\":552,\"a\":56,\"owners\":[91,95,104,105]},{\"tag\":\"mate\",\"ridge\":552,\"a\":76,\"owners\":[66,70,104,105]},{\"tag\":\"mate\",\"ridge\":552,\"a\":100,\"owners\":[44,66,70,91,105]},{\"tag\":\"mate\",\"ridge\":54,\"a\":80,\"owners\":[28,81,82]},{\"tag\":\"mate\",\"ridge\":533,\"a\":61,\"owners\":[31]},{\"tag\":\"mate\",\"ridge\":547,\"a\":34,\"owners\":[44,50]},{\"tag\":\"mate\",\"ridge\":773,\"a\":58,\"owners\":[37]},{\"tag\":\"mate\",\"ridge\":58,\"a\":91,\"owners\":[38,90]},{\"tag\":\"mate\",\"ridge\":537,\"a\":68,\"owners\":[41,66]},{\"tag\":\"mate\",\"ridge\":170,\"a\":43,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":560,\"a\":50,\"owners\":[102,103,104,105,106]},{\"tag\":\"mate\",\"ridge\":560,\"a\":61,\"owners\":[91,97,98,104,105,106]},{\"tag\":\"mate\",\"ridge\":560,\"a\":82,\"owners\":[66,73,104,105,106]},{\"tag\":\"mate\",\"ridge\":560,\"a\":91,\"owners\":[61,73,102,103,106]},{\"tag\":\"mate\",\"ridge\":560,\"a\":97,\"owners\":[61,66,73,103,105,106]},{\"tag\":\"mate\",\"ridge\":560,\"a\":98,\"owners\":[61,66,73,102,104,105]},{\"tag\":\"mate\",\"ridge\":560,\"a\":102,\"owners\":[50,66,73,91,98,105,106]},{\"tag\":\"mate\",\"ridge\":560,\"a\":103,\"owners\":[50,66,73,91,97,104,105]},{\"tag\":\"mate\",\"ridge\":226,\"a\":96,\"owners\":[54,86]},{\"tag\":\"mate\",\"ridge\":212,\"a\":83,\"owners\":[62,101]},{\"tag\":\"mate\",\"ridge\":312,\"a\":105,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":344,\"a\":92,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":424,\"a\":69,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":801,\"a\":70,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":801,\"a\":73,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":596,\"a\":102,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":660,\"a\":103,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":610,\"a\":87,\"owners\":[95,97]},{\"tag\":\"mate\",\"ridge\":674,\"a\":88,\"owners\":[98]},{\"tag\":\"mate\",\"ridge\":674,\"a\":98,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":600,\"a\":93,\"owners\":[104]},{\"tag\":\"mate\",\"ridge\":928,\"a\":106,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":37,\"full_literals\":[-12,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":57,\"full_literals\":[-27,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":78,\"full_literals\":[-44,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":38,\"full_literals\":[-13,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":41,\"full_literals\":[-15,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":65,\"full_literals\":[-33,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":67,\"full_literals\":[-35,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":66,\"full_literals\":[-34,75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":90,\"full_literals\":[-55,75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":104,\"full_literals\":[-69,75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":105,\"full_literals\":[-70,75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":70,\"full_literals\":[-38,76]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":28,\"full_literals\":[-8,77]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":31,\"full_literals\":[-9,77]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":62,\"full_literals\":[-31,77]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":84,\"full_literals\":[-50,77]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":85,\"full_literals\":[-51,77]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[61,80,83,102,103],\"full_literals\":[-78,30,46,49,67,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":61,\"full_literals\":[-30,78]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":102,\"full_literals\":[-67,78]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":103,\"full_literals\":[-68,78]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":54,\"full_literals\":[-24,79]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":81,\"full_literals\":[-47,79]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":101,\"full_literals\":[-66,79]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":75,\"full_literals\":[-42,80]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":82,\"full_literals\":[-48,80]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":86,\"full_literals\":[-52,80]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":88,\"full_literals\":[-54,80]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":91,\"full_literals\":[-56,80]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":44,\"full_literals\":[-17,81]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":95,\"full_literals\":[-60,81]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":98,\"full_literals\":[-63,81]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":50,\"full_literals\":[-22,82]},{\"tag\":\"group_take\",\"kind\":3,\"index\":10,\"member\":97,\"full_literals\":[-62,82]},{\"tag\":\"group_take\",\"kind\":3,\"index\":11,\"member\":58,\"full_literals\":[-28,83]},{\"tag\":\"group_take\",\"kind\":3,\"index\":11,\"member\":68,\"full_literals\":[-36,83]},{\"tag\":\"group_take\",\"kind\":3,\"index\":11,\"member\":73,\"full_literals\":[-41,83]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0004\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0005\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-74,84],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0004\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0005\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-73,false,84],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-84,85],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-72,false,85],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-77,86],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-76,false,86],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-86,87],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-75,false,87],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-75,-86,88],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-87,89],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-88,90],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-85,false,89],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-85,-87,90],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-80,91],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-79,false,91],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-92,78,91],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-91,92],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-78,false,92],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-78,-91,93],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-83,94],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-82,false,94],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-94,95],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[9],\"right\":[10,11],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-81,false,95],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-92,false,96],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-92,-95,97],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6,7,8],\"right\":[9,10,11],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0014\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-93,false,97],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-89,-97,98],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5],\"right\":[6,7,8,9,10,11],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-90,-96,98],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":28,\"owners\":[4,19,26,40,45,46,47,57,58,65,67,68,69,70,78,79,92,94,105]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[21,31,41,50,53,61,66,68,73,82,84,85,91,93,94,97,98,99,102,103,104,105,106]},{\"tag\":\"edge\",\"edge\":36,\"owners\":[12,15,33,43,49,54,55,60,63,69,71,72,75,81,86,88,96,98,101,103,106]},{\"tag\":\"edge\",\"edge\":38,\"owners\":[23,34,44,50,56,61,66,70,73,76,82,87,88,91,95,97,98,100,102,103,104,105,106]}]}"
  "127 1 4 7 14 18 19 20 27 28 33 35 36 38 44 45 57 59 70 0 47 123 0\n128 5 9 15 22 23 30 34 36 41 48 50 51 56 58 59 62 63 64 67 68 69 70 0 56 124 0\n129 2 3 10 16 21 24 25 29 32 39 40 42 47 52 54 61 63 66 68 0 47 56 125 0\n130 6 11 17 22 26 30 34 38 41 43 48 53 54 56 60 62 63 65 67 68 69 70 0 56 126 0\n131 89 0 56 103 105 100 101 96 97 98 99 64 65 66 67 94 57 70 72 73 68 55 20 60 61 31 29 50 51 49 18 32 33 39 40 35 37 19 22 128 0\n132 -97 0 131 122 120 0\n133 -93 0 132 119 0\n134 92 0 56 110 111 107 108 77 81 83 84 78 79 80 34 43 11 54 15 12 9 14 10 13 8 16 129 0\n135 96 0 134 117 0\n136 -95 0 134 132 118 0\n137 -90 0 135 122 121 0\n138 -94 0 136 115 0\n139 -81 0 136 116 0\n140 -88 0 137 104 0\n141 -83 0 138 113 0\n142 -82 0 138 114 0\n143 -17 0 139 86 0\n144 -60 0 139 87 0\n145 -63 0 139 88 0\n146 -28 0 141 91 0\n147 -36 0 141 92 0\n148 -41 0 141 93 0\n149 -22 0 142 89 0\n150 -62 0 142 90 0\n151 -11 0 143 149 30 0\n152 -53 0 144 150 52 0\n153 -54 0 145 53 0\n154 -59 0 148 56 21 0\n155 -38 0 148 48 0\n156 75 80 0 56 145 150 144 153 152 148 155 143 149 151 85 82 64 66 67 26 27 24 41 42 36 25 130 0\n157 91 0 134 140 107 108 109 82 79 80 156 102 98 69 70 71 72 73 28 29 44 50 51 74 0\n158 -78 0 157 133 112 0\n159 -30 0 158 75 0\n160 -67 0 158 76 0\n161 -68 0 158 77 0\n162 -56 0 159 148 160 161 56 38 0\n163 -43 0 160 159 161 23 0\n164 85 0 47 154 155 147 146 96 97 94 95 58 62 63 59 3 6 1 4 45 2 5 46 7 17 127 0\n165 -87 0 164 137 106 0\n166 -75 0 165 101 0\n167 -34 0 166 64 0\n168 -69 0 166 66 0\n169 -70 0 166 67 0\n170 -65 0 167 143 155 162 169 27 0\n171 -6 0 167 143 155 162 144 168 169 24 0\n172 -48 0 167 148 168 169 56 37 0\n173 -26 0 168 144 162 169 25 0\n174 0 171 170 151 149 143 159 173 155 148 163 172 152 153 162 144 150 145 167 160 161 168 169 130 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record033.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record033.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record033.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record033.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record033 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record033.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record033.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record033.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record033.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record033 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record033_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record033_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record033_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record033_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record033_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record033_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record033_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record033 Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record033_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record033_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00077.record033_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00077.record033
