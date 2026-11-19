module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow23Part00005Data
public import GraphInputsRow23Part00005Frames
public import GraphInputsRow23Part00005Leaves
public import GraphInputsRow23Part00005Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00005.record014
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record014
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), 2134706223373615104, (certNat% 4), (certNat% 5), (certNat% 6), (certNat% 7)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 8), (certNat% 9), (certNat% 10), (certNat% 7), (certNat% 11), (certNat% 3), (certNat% 12), (certNat% 13)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), (certNat% 15), (certNat% 16), (certNat% 17), 70368744177664, (certNat% 18)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), (certNat% 20), (certNat% 21), (certNat% 22), 211106232532992, (certNat% 23), (certNat% 24)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), 486397555849035776, (certNat% 9), (certNat% 26), (certNat% 27), (certNat% 11), (certNat% 28), 211106232532992]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), 486397555849035776, (certNat% 9), (certNat% 30), (certNat% 31), (certNat% 12), (certNat% 32), (certNat% 33)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 34), (certNat% 35), (certNat% 36), (certNat% 37), (certNat% 38), (certNat% 39), 486388759756013568, (certNat% 40)]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 41), (certNat% 42), (certNat% 43), 468374361246531584, (certNat% 44), (certNat% 11), (certNat% 45), (certNat% 33)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 46), (certNat% 47), (certNat% 48), (certNat% 49), (certNat% 50), (certNat% 51), (certNat% 52), (certNat% 53)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 54), (certNat% 31), 2062683813707776000, (certNat% 48), (certNat% 55), (certNat% 49)]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 56), (certNat% 57), (certNat% 58), 1486187877032263680, (certNat% 10), (certNat% 59), (certNat% 47)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 60), (certNat% 48), (certNat% 61), (certNat% 31), (certNat% 62), (certNat% 63), (certNat% 64), (certNat% 49), 324259173170675712]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c14 c11
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c15 c10
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c16 c9
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨85, by decide⟩ c17 c8
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c18 c7
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c19 c6
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c20 c1
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c21 c0
  c22
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record014_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record014_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record014_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record014_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record014_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record014_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record014_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record014_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record014_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00005.record014

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00005.record009
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "6c8ba2da4e2b86e0fb91d45b1d24b9d1715956352d62d2b46d8743dd0dc368f1354d3362e4b52ccb1ac9b0ee4751ca719e1745c9715e0f23c1f931922c8aa0d84e0bb41c45912c6492a645854358344d0b58350ca344c930cc8b12c2b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "12492492492492492492492492492492492249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record009 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record009 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record009.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record009.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record009.data.quota

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record009 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record009_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00005.record009" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00005.record009" 14

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00005.record009" "{\"ridges\":[[11,322],[17,532],[23,529],[38,532],[41,322],[47,322],[52,529],[54,322],[57,532],[62,532],[63,532],[64,532],[69,321],[70,529]],\"owners\":[[69,321,[11,41,47,54],[24,51,65,67]],[11,322,[],[41,47,51,54,55]],[41,322,[],[11,47,51,54,55]],[47,322,[],[11,41,51,54,55]],[54,322,[],[11,41,47,51,55]],[23,529,[17,38,57,62,63],[52,69,70]],[52,529,[17,57,62,63],[23,38,69,70]],[70,529,[17,38,57,62,63],[23,52,69]],[17,532,[],[38,57,62,63,64]],[38,532,[],[17,57,62,63,64]],[57,532,[],[17,38,62,63,64]],[62,532,[],[17,38,57,63,64]],[63,532,[],[17,38,57,62,64]],[64,532,[],[17,38,57,62,63]]],\"edges\":[[34,[17,23,38,52,57,62,63,64,69,70]]],\"groupings\":[]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00005.record009" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00005.record009\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-13,1,5,6,8],[-1],[-5],[-6],[-8],[-3,2,4,9,10,11],[-7,2,9,10,11],[-14,2,4,9,10,11],[-2],[-4],[-9],[-10],[-11],[-12],[2,3,4,7,9,10,11,12,13,14]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70}],\"rules\":[{\"tag\":\"mate\",\"ridge\":321,\"a\":69,\"owners\":[11,41,47,54]},{\"tag\":\"mate\",\"ridge\":322,\"a\":11,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":322,\"a\":41,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":322,\"a\":47,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":322,\"a\":54,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":529,\"a\":23,\"owners\":[17,38,57,62,63]},{\"tag\":\"mate\",\"ridge\":529,\"a\":52,\"owners\":[17,57,62,63]},{\"tag\":\"mate\",\"ridge\":529,\"a\":70,\"owners\":[17,38,57,62,63]},{\"tag\":\"mate\",\"ridge\":532,\"a\":17,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":532,\"a\":38,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":532,\"a\":57,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":532,\"a\":62,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":532,\"a\":63,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":532,\"a\":64,\"owners\":[]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[17,23,38,52,57,62,63,64,69,70]}]}"
  "16 -13 0 5 2 3 4 1 0\n17 -7 0 13 9 11 12 7 0\n18 -3 0 13 9 10 11 12 6 0\n19 -14 0 13 9 10 11 12 8 0\n20 0 9 18 10 17 11 12 13 14 16 19 15 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record009.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record009.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record009.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record009.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record009 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record009.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record009.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record009.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record009.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record009 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record009_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record009_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record009_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record009_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record009_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record009_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record009_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record009 Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record009_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record009_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record009_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00005.record009

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00005.record048
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "1aa66a561d8ae1bb91d47896a71966665c5475c364d8b4ad1b61d68ce3c4e5354cd32cc73c2d2b1ad1b26e4729e1745c970de0f43c8f13c1f95192628aa198560bb1164651c25892a645196151560d0b58328c6344c9314d0b22c2b11c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "2492492492492492492492492492492492249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record048 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record048 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record048.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record048.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record048.data.quota

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record048 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record048_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00005.record048" "{\"atoms\":[{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00005.record048" 10

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00005.record048" "{\"ridges\":[[14,524],[21,521],[36,524],[47,521],[56,524],[59,524],[60,524],[61,524],[66,521],[68,521]],\"owners\":[[21,521,[14,36,56,59,60],[47,66,68]],[47,521,[14,56,59,60],[21,36,66,68]],[66,521,[14,36,59,60],[21,47,56,68]],[68,521,[14,36,56,59,60],[21,47,66]],[14,524,[],[36,56,59,60,61]],[36,524,[],[14,56,59,60,61]],[56,524,[],[14,36,59,60,61]],[59,524,[],[14,36,56,60,61]],[60,524,[],[14,36,56,59,61]],[61,524,[],[14,36,56,59,60]]],\"edges\":[[29,[14,21,36,47,56,59,60,61,66,68]]],\"groupings\":[]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00005.record048" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00005.record048\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-2,1,3,5,6,7],[-4,1,5,6,7],[-9,1,3,6,7],[-10,1,3,5,6,7],[-1],[-3],[-5],[-6],[-7],[-8],[1,2,3,4,5,6,7,8,9,10]],\"atoms\":[{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68}],\"rules\":[{\"tag\":\"mate\",\"ridge\":521,\"a\":21,\"owners\":[14,36,56,59,60]},{\"tag\":\"mate\",\"ridge\":521,\"a\":47,\"owners\":[14,56,59,60]},{\"tag\":\"mate\",\"ridge\":521,\"a\":66,\"owners\":[14,36,59,60]},{\"tag\":\"mate\",\"ridge\":521,\"a\":68,\"owners\":[14,36,56,59,60]},{\"tag\":\"mate\",\"ridge\":524,\"a\":14,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":524,\"a\":36,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":524,\"a\":56,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":524,\"a\":59,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":524,\"a\":60,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":524,\"a\":61,\"owners\":[]},{\"tag\":\"edge\",\"edge\":29,\"owners\":[14,21,36,47,56,59,60,61,66,68]}]}"
  "12 -9 0 9 5 6 8 3 0\n13 -4 0 9 5 7 8 2 0\n14 -2 0 9 5 6 7 8 1 0\n15 -10 0 9 5 6 7 8 4 0\n16 0 5 14 6 13 7 8 9 10 12 15 11 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record048.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record048.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record048.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record048.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record048 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record048.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record048.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record048.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record048.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record048 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record048_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record048_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record048_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record048_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record048_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record048_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record048_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record048 Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record048_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record048_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00005.record048_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00005.record048
