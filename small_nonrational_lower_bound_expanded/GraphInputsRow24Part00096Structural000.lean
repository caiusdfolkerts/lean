module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00096Data
public import GraphInputsRow24Part00096Frames
public import GraphInputsRow24Part00096Leaves
public import GraphInputsRow24Part00096Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00096.record010
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record010
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨54, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨69, by decide⟩, ⟨73, by decide⟩, ⟨77, by decide⟩, ⟨80, by decide⟩, ⟨85, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), 30786325577728, 35184372088832, 11674456134051168256, 4630263366890291200]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [3316360436118454272, 4629700691814776832, 9223654061587300352, (certNat% 4), (certNat% 3), 43980465111040]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 5), (certNat% 6), (certNat% 7), 1009369266484412416, 6917533425687592960, 9223389629040820224, (certNat% 8)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record010_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record010_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00096.record010

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00096.record011
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record011
def vertexColumn : Fields := ⟨10, (certNat% 9)⟩
def kindColumn : Fields := ⟨3, (certNat% 10)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 11), (certNat% 12), (certNat% 13), (certNat% 14), (certNat% 15), (certNat% 16)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 17), (certNat% 18), 510173395288064, 1065151889408, (certNat% 19)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 20), 893353197568, (certNat% 21), (certNat% 22), (certNat% 23)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [(certNat% 24)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), (certNat% 26), 1030792151040, (certNat% 27), (certNat% 28)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), (certNat% 13), 1065151889408, (certNat% 30), (certNat% 31), (certNat% 32)]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 33), 1065151889408, (certNat% 34), (certNat% 35), (certNat% 36), (certNat% 37), 510173932158976]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c10 c1
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c11 c0
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record011_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record011_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record011_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record011_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record011_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record011_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record011_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record011_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record011_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00096.record011

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00096.record015
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record015
def vertexColumn : Fields := ⟨10, (certNat% 38)⟩
def kindColumn : Fields := ⟨3, (certNat% 39)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 40), (certNat% 41), (certNat% 42), (certNat% 43), (certNat% 44), (certNat% 45)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 46), (certNat% 47), 35201702952960, (certNat% 48), 489626271744]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 49), 43980632883200, (certNat% 50), (certNat% 51), (certNat% 52)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 53), (certNat% 47), 429496729600, (certNat% 54), 35184372088832]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 55), (certNat% 56), (certNat% 57)]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 58), 4611686018427387904, (certNat% 57)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨80, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 59), (certNat% 60), (certNat% 61), (certNat% 62)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c10 c6
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 63), (certNat% 64), (certNat% 65), (certNat% 66), (certNat% 67)]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c12 c11
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 68), (certNat% 69), (certNat% 70), 35201736507392, (certNat% 71), (certNat% 66)]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c15 c3
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c16 c2
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c17 c1
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 72), 53326330724352, (certNat% 73), (certNat% 44), (certNat% 74), (certNat% 75), 397552910336]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨90, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c20 c0
  c21
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record015_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record015_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record015_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record015_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record015_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record015_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record015_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record015_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record015_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00096.record015

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00096.record005
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "ae2b2aaa9a96a3a2e87a559362d876a394e2b86eac6a9a6659366392e47965555355352d475a354d3346da8f13a4e538cd332cc73a2e4b52e2b2ac6b86c9b16c3ba1d2729c6745c9715c3783d0f23cac549461382ea45512c6892a5452948d1342d50e1344c530ce0b12c2b41c4709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db6d36da4924db4da6d349269249249249349a493492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record005 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record005 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record005.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record005.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record005.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 27), (facetIndex 57), (facetIndex 59), (facetIndex 72)]))
 (.leaf ([(facetIndex 30), (facetIndex 31), (facetIndex 33), (facetIndex 61), (facetIndex 64), (facetIndex 81)])))
 (.branch 3
 (.leaf ([(facetIndex 28), (facetIndex 34), (facetIndex 45), (facetIndex 58), (facetIndex 76)]))
 (.leaf ([(facetIndex 67), (facetIndex 71), (facetIndex 73)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 56), (facetIndex 74), (facetIndex 75)]))
 (.leaf ([(facetIndex 35), (facetIndex 36), (facetIndex 38)])))
 (.branch 7
 (.leaf ([(facetIndex 48), (facetIndex 49), (facetIndex 50), (facetIndex 51), (facetIndex 52), (facetIndex 53), (facetIndex 54)]))
 (.branch 8
 (.leaf ([(facetIndex 29), (facetIndex 42), (facetIndex 43), (facetIndex 44), (facetIndex 46), (facetIndex 47)]))
 (.leaf ([(facetIndex 39), (facetIndex 41)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "100002443030003001001002040666666677277780850552101172z1c;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 32), (facetIndex 60), (facetIndex 62), (facetIndex 63), (facetIndex 65)]))
 (.branch 2
 (.leaf ([(facetIndex 78), (facetIndex 79), (facetIndex 80)]))
 (.leaf ([(facetIndex 37), (facetIndex 40), (facetIndex 55)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 77), (facetIndex 83), (facetIndex 87)]))
 (.leaf ([(facetIndex 66), (facetIndex 68), (facetIndex 69), (facetIndex 70), (facetIndex 86)])))
 (.branch 6
 (.leaf ([(facetIndex 82), (facetIndex 84), (facetIndex 85)]))
 (.leaf ([(facetIndex 88), (facetIndex 89)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "3672d74125800012410000000040000000000201z1c;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 7
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
def grouped2_0008 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0009 : List Nat := [5]
def grouped2_0010 : List Nat := [6]
def grouped2_0011 : List Nat := [6, 7, 8]
def grouped2_0012 : List Nat := [7]
def grouped2_0013 : List Nat := [7, 8]
def grouped2_0014 : List Nat := [8]
def grouped3_0015 : List Nat := [0]
def grouped3_0016 : List Nat := [0, 1, 2]
def grouped3_0018 : List Nat := [1]
def grouped3_0019 : List Nat := [1, 2]
def grouped3_0020 : List Nat := [2]
def grouped3_0021 : List Nat := [3]
def grouped3_0022 : List Nat := [3, 4]
def grouped3_0023 : List Nat := [3, 4, 5, 6]
def grouped3_0024 : List Nat := [4]
def grouped3_0025 : List Nat := [5]
def grouped3_0026 : List Nat := [5, 6]
def grouped3_0027 : List Nat := [6]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record005 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record005_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00096.record005" "{\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00096.record005" 86

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00096.record005" "{\"ridges\":[[6,522],[7,35],[10,19],[10,530],[18,648],[19,176],[21,529],[21,656],[29,522],[36,35],[38,50],[39,19],[41,522],[41,530],[42,35],[44,522],[46,522],[47,522],[49,19],[49,50],[49,176],[51,50],[51,530],[52,530],[53,530],[53,656],[54,530],[59,648],[61,176],[63,212],[65,404],[66,120],[67,176],[69,216],[70,600],[71,529],[71,648],[71,656],[73,49],[73,176],[73,529],[73,656],[77,646],[79,150],[82,120],[83,154],[85,600],[86,154],[86,530],[87,674],[88,50],[88,530],[88,674]],\"owners\":[[6,522,[77,84,85,86,87],[29,41,44,46,47]],[29,522,[84,85,86,87],[6,41,44,46,47,77]],[41,522,[77,87],[6,29,44,46,47,84,85,86]],[44,522,[77,85,86],[6,29,41,46,47,84,87]],[46,522,[77,84,86,87],[6,29,41,44,47,85]],[47,522,[84,85],[6,29,41,44,46,77,86,87]],[73,49,[7,30,38,48,50,60,62,66],[19,51,61,67,68]],[38,50,[78,79,80,88],[7,30,48,49,50,51,82,83,84]],[49,50,[78,80,82,84],[7,30,38,48,50,51,79,83,88]],[51,50,[78,79,80,82,83],[7,30,38,48,49,50,84,88]],[88,50,[7,30,38,48,50,78,80,82],[49,51,79,83,84]],[21,529,[10,41,51,52,54,68,70],[71,73]],[71,529,[10,51,52,54],[21,41,68,70,73]],[73,529,[10,41,52,54,70],[21,51,68,71]],[10,530,[84,85,86,88],[41,51,52,53,54]],[41,530,[88],[10,51,52,53,54,84,85,86]],[51,530,[85,86],[10,41,52,53,54,84,88]],[52,530,[84,86,88],[10,41,51,53,54,85]],[53,530,[84,85],[10,41,51,52,54,86,88]],[54,530,[84,85,86,88],[10,41,51,52,53]],[86,530,[10,51,52,54],[41,53,84,85,88]],[88,530,[10,41,52,54,85],[51,53,84,86]],[18,648,[77,86,87,89],[47,59,71,72]],[59,648,[86,87,89],[18,47,71,72,77]],[71,648,[77,87],[18,47,59,72,86,89]],[19,176,[79,83,88,89],[49,61,67,73]],[49,176,[89],[19,61,67,73,79,83,88]],[61,176,[83,88,89],[19,49,67,73,79]],[67,176,[79,88],[19,49,61,73,83,89]],[73,176,[79,83],[19,49,61,67,88,89]],[21,656,[86,88,89],[53,71,73]],[53,656,[89],[21,71,73,86,88]],[71,656,[88],[21,53,73,86,89]],[73,656,[86],[21,53,71,88,89]],[79,150,[32],[]],[77,646,[37],[]],[83,154,[40,86],[]],[86,154,[40,83],[]],[87,674,[55,88],[]],[88,674,[55,87],[]],[63,212,[],[]],[65,404,[],[]],[66,120,[82],[]],[82,120,[66],[]],[69,216,[],[]],[70,600,[85],[]],[85,600,[70],[]]],\"edges\":[[16,[6,10,29,37,41,44,46,47,51,52,53,54,55,77,84,85,86,87,88]],[29,[6,18,29,41,44,46,47,59,68,70,71,72,77,84,85,86,87,89]],[32,[19,21,32,40,49,53,61,63,65,67,69,71,73,79,83,86,88,89]],[34,[10,21,41,51,52,53,54,68,70,71,73,84,85,86,88,89]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00096.record005" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00096.record005\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-11,-7],[-11,-8],[-13,-7],[-14,-13],[-15,-7],[-16,-7],[-16,-13],[-17,-13],[-17,-15],[-17,-16],[-19,-15],[-19,-16],[-20,-13],[-20,-14],[-20,-15],[-20,-16],[-21,-16],[-22,-3],[-22,-16],[-24,-3],[-24,-11],[-24,-13],[-24,-14],[-24,-16],[-25,-3],[-25,-14],[-25,-16],[-25,-24],[-26,-2],[-26,-8],[-26,-9],[-26,-15],[-26,-16],[-26,-22],[-26,-23],[-26,-24],[-27,-3],[-27,-16],[-27,-26],[-28,-2],[-28,-8],[-28,-9],[-28,-13],[-28,-15],[-28,-16],[-28,-22],[-28,-23],[-28,-24],[-28,-27],[-37,-10],[-38,-14],[-38,-37],[-43,-15],[-43,-25],[-49,-10],[-49,-14],[-50,-14],[-50,-15],[-50,-37],[-52,-14],[-52,-18],[-52,-21],[-52,-37],[-54,-10],[-54,-18],[-54,-19],[-54,-21],[-54,-25],[-54,-38],[-54,-42],[-54,-44],[-54,-50],[-55,-14],[-55,-16],[-55,-37],[-55,-54],[-2,-11,-17],[-1,44,50,51,52,53],[-7,50,51,52,53],[-16,44,53],[-19,44,51,52],[-20,44,50,52,53],[-21,50,51],[-3,-14,-23],[-43,2,8,13,22,24,31,33,36],[-13,45,46,47,54],[-23,45,47,48,50],[-25,45,46,47,48,49],[-54,2,8,13,22,24,45,47,48],[-6,3,16,25,26,28,38,40],[-41,3,25,26,28],[-43,3,16,26,28,40],[-3,50,51,52,54],[-16,54],[-25,51,52],[-26,50,52,54],[-27,50,51],[-28,50,51,52,54],[-52,3,25,26,28],[-54,3,16,26,28,51],[-4,44,52,53,55],[-30,52,53,55],[-41,44,53],[-5,46,49,54,55],[-23,55],[-32,49,54,55],[-37,46,54],[-43,46,49],[-6,52,54,55],[-27,55],[-41,54],[-43,52],[-46,9],[-44,12],[-49,15,52],[-52,15,49],[-53,29,54],[-54,29,53],[-34],[-35],[-36,48],[-48,36],[-39],[-40,51],[-51,40],[-56,37,41,43],[-57,10,11,13],[-58,22,23,24,25,26,27,28],[-59,7,17,18,19,20,21],[-60,14,16],[-61,56],[-62,61],[-63,57],[-64,59,60],[-65,59],[-65,60],[-66,58,65],[-67,58],[-66,64],[-67,65],[-68,63,67],[-68,66],[-69,67],[-70,62,69],[-70,68],[70],[-9,71],[-31,71],[-33,71],[-45,72],[-46,72],[-47,72],[-12,73],[-15,73],[-29,73],[-74,44,49,53],[-49,74],[-53,74],[-36,75],[-40,75],[-52,75],[-76,48,50,51],[-48,76],[-50,76],[-51,76],[-54,77],[-55,77],[-73,78],[-72,78],[-78,79],[-71,79],[-80,74,75],[-75,80],[-74,80],[-74,-75,81],[-77,82],[-83,76],[-76,82],[-76,-77,83],[-84,80,83],[-83,84],[-80,-82,84],[-80,-83,85],[-81,84],[-81,-82,85],[-85,86],[-79,-84,86],[-86],[1,3,7,12,16,19,20,21,25,26,27,28,29,44,50,51,52,53,54],[1,4,7,16,19,20,21,30,38,40,41,42,44,50,51,52,53,55],[5,6,9,15,23,27,32,34,35,37,39,41,43,46,49,52,54,55],[3,6,16,25,26,27,28,38,40,41,43,50,51,52,54,55]],\"atoms\":[{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":36,\"b\":29},{\"tag\":\"incompatible\",\"a\":36,\"b\":30},{\"tag\":\"incompatible\",\"a\":38,\"b\":29},{\"tag\":\"incompatible\",\"a\":39,\"b\":38},{\"tag\":\"incompatible\",\"a\":40,\"b\":29},{\"tag\":\"incompatible\",\"a\":41,\"b\":29},{\"tag\":\"incompatible\",\"a\":41,\"b\":38},{\"tag\":\"incompatible\",\"a\":42,\"b\":38},{\"tag\":\"incompatible\",\"a\":42,\"b\":40},{\"tag\":\"incompatible\",\"a\":42,\"b\":41},{\"tag\":\"incompatible\",\"a\":44,\"b\":40},{\"tag\":\"incompatible\",\"a\":44,\"b\":41},{\"tag\":\"incompatible\",\"a\":46,\"b\":38},{\"tag\":\"incompatible\",\"a\":46,\"b\":39},{\"tag\":\"incompatible\",\"a\":46,\"b\":40},{\"tag\":\"incompatible\",\"a\":46,\"b\":41},{\"tag\":\"incompatible\",\"a\":47,\"b\":41},{\"tag\":\"incompatible\",\"a\":48,\"b\":10},{\"tag\":\"incompatible\",\"a\":48,\"b\":41},{\"tag\":\"incompatible\",\"a\":50,\"b\":10},{\"tag\":\"incompatible\",\"a\":50,\"b\":36},{\"tag\":\"incompatible\",\"a\":50,\"b\":38},{\"tag\":\"incompatible\",\"a\":50,\"b\":39},{\"tag\":\"incompatible\",\"a\":50,\"b\":41},{\"tag\":\"incompatible\",\"a\":51,\"b\":10},{\"tag\":\"incompatible\",\"a\":51,\"b\":39},{\"tag\":\"incompatible\",\"a\":51,\"b\":41},{\"tag\":\"incompatible\",\"a\":51,\"b\":50},{\"tag\":\"incompatible\",\"a\":52,\"b\":7},{\"tag\":\"incompatible\",\"a\":52,\"b\":30},{\"tag\":\"incompatible\",\"a\":52,\"b\":32},{\"tag\":\"incompatible\",\"a\":52,\"b\":40},{\"tag\":\"incompatible\",\"a\":52,\"b\":41},{\"tag\":\"incompatible\",\"a\":52,\"b\":48},{\"tag\":\"incompatible\",\"a\":52,\"b\":49},{\"tag\":\"incompatible\",\"a\":52,\"b\":50},{\"tag\":\"incompatible\",\"a\":53,\"b\":10},{\"tag\":\"incompatible\",\"a\":53,\"b\":41},{\"tag\":\"incompatible\",\"a\":53,\"b\":52},{\"tag\":\"incompatible\",\"a\":54,\"b\":7},{\"tag\":\"incompatible\",\"a\":54,\"b\":30},{\"tag\":\"incompatible\",\"a\":54,\"b\":32},{\"tag\":\"incompatible\",\"a\":54,\"b\":38},{\"tag\":\"incompatible\",\"a\":54,\"b\":40},{\"tag\":\"incompatible\",\"a\":54,\"b\":41},{\"tag\":\"incompatible\",\"a\":54,\"b\":48},{\"tag\":\"incompatible\",\"a\":54,\"b\":49},{\"tag\":\"incompatible\",\"a\":54,\"b\":50},{\"tag\":\"incompatible\",\"a\":54,\"b\":53},{\"tag\":\"incompatible\",\"a\":67,\"b\":35},{\"tag\":\"incompatible\",\"a\":68,\"b\":39},{\"tag\":\"incompatible\",\"a\":68,\"b\":67},{\"tag\":\"incompatible\",\"a\":73,\"b\":40},{\"tag\":\"incompatible\",\"a\":73,\"b\":51},{\"tag\":\"incompatible\",\"a\":83,\"b\":35},{\"tag\":\"incompatible\",\"a\":83,\"b\":39},{\"tag\":\"incompatible\",\"a\":84,\"b\":39},{\"tag\":\"incompatible\",\"a\":84,\"b\":40},{\"tag\":\"incompatible\",\"a\":84,\"b\":67},{\"tag\":\"incompatible\",\"a\":86,\"b\":39},{\"tag\":\"incompatible\",\"a\":86,\"b\":43},{\"tag\":\"incompatible\",\"a\":86,\"b\":47},{\"tag\":\"incompatible\",\"a\":86,\"b\":67},{\"tag\":\"incompatible\",\"a\":88,\"b\":35},{\"tag\":\"incompatible\",\"a\":88,\"b\":43},{\"tag\":\"incompatible\",\"a\":88,\"b\":44},{\"tag\":\"incompatible\",\"a\":88,\"b\":47},{\"tag\":\"incompatible\",\"a\":88,\"b\":51},{\"tag\":\"incompatible\",\"a\":88,\"b\":68},{\"tag\":\"incompatible\",\"a\":88,\"b\":72},{\"tag\":\"incompatible\",\"a\":88,\"b\":77},{\"tag\":\"incompatible\",\"a\":88,\"b\":84},{\"tag\":\"incompatible\",\"a\":89,\"b\":39},{\"tag\":\"incompatible\",\"a\":89,\"b\":41},{\"tag\":\"incompatible\",\"a\":89,\"b\":67},{\"tag\":\"incompatible\",\"a\":89,\"b\":88},{\"tag\":\"three\",\"ridge\":35,\"vertices\":[7,36,42]},{\"tag\":\"mate\",\"ridge\":522,\"a\":6,\"owners\":[77,84,85,86,87]},{\"tag\":\"mate\",\"ridge\":522,\"a\":29,\"owners\":[84,85,86,87]},{\"tag\":\"mate\",\"ridge\":522,\"a\":41,\"owners\":[77,87]},{\"tag\":\"mate\",\"ridge\":522,\"a\":44,\"owners\":[77,85,86]},{\"tag\":\"mate\",\"ridge\":522,\"a\":46,\"owners\":[77,84,86,87]},{\"tag\":\"mate\",\"ridge\":522,\"a\":47,\"owners\":[84,85]},{\"tag\":\"three\",\"ridge\":19,\"vertices\":[10,39,49]},{\"tag\":\"mate\",\"ridge\":49,\"a\":73,\"owners\":[7,30,38,48,50,60,62,66]},{\"tag\":\"mate\",\"ridge\":50,\"a\":38,\"owners\":[78,79,80,88]},{\"tag\":\"mate\",\"ridge\":50,\"a\":49,\"owners\":[78,80,82,84]},{\"tag\":\"mate\",\"ridge\":50,\"a\":51,\"owners\":[78,79,80,82,83]},{\"tag\":\"mate\",\"ridge\":50,\"a\":88,\"owners\":[7,30,38,48,50,78,80,82]},{\"tag\":\"mate\",\"ridge\":529,\"a\":21,\"owners\":[10,41,51,52,54,68,70]},{\"tag\":\"mate\",\"ridge\":529,\"a\":71,\"owners\":[10,51,52,54]},{\"tag\":\"mate\",\"ridge\":529,\"a\":73,\"owners\":[10,41,52,54,70]},{\"tag\":\"mate\",\"ridge\":530,\"a\":10,\"owners\":[84,85,86,88]},{\"tag\":\"mate\",\"ridge\":530,\"a\":41,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":530,\"a\":51,\"owners\":[85,86]},{\"tag\":\"mate\",\"ridge\":530,\"a\":52,\"owners\":[84,86,88]},{\"tag\":\"mate\",\"ridge\":530,\"a\":53,\"owners\":[84,85]},{\"tag\":\"mate\",\"ridge\":530,\"a\":54,\"owners\":[84,85,86,88]},{\"tag\":\"mate\",\"ridge\":530,\"a\":86,\"owners\":[10,51,52,54]},{\"tag\":\"mate\",\"ridge\":530,\"a\":88,\"owners\":[10,41,52,54,85]},{\"tag\":\"mate\",\"ridge\":648,\"a\":18,\"owners\":[77,86,87,89]},{\"tag\":\"mate\",\"ridge\":648,\"a\":59,\"owners\":[86,87,89]},{\"tag\":\"mate\",\"ridge\":648,\"a\":71,\"owners\":[77,87]},{\"tag\":\"mate\",\"ridge\":176,\"a\":19,\"owners\":[79,83,88,89]},{\"tag\":\"mate\",\"ridge\":176,\"a\":49,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":176,\"a\":61,\"owners\":[83,88,89]},{\"tag\":\"mate\",\"ridge\":176,\"a\":67,\"owners\":[79,88]},{\"tag\":\"mate\",\"ridge\":176,\"a\":73,\"owners\":[79,83]},{\"tag\":\"mate\",\"ridge\":656,\"a\":21,\"owners\":[86,88,89]},{\"tag\":\"mate\",\"ridge\":656,\"a\":53,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":656,\"a\":71,\"owners\":[88]},{\"tag\":\"mate\",\"ridge\":656,\"a\":73,\"owners\":[86]},{\"tag\":\"mate\",\"ridge\":150,\"a\":79,\"owners\":[32]},{\"tag\":\"mate\",\"ridge\":646,\"a\":77,\"owners\":[37]},{\"tag\":\"mate\",\"ridge\":154,\"a\":83,\"owners\":[40,86]},{\"tag\":\"mate\",\"ridge\":154,\"a\":86,\"owners\":[40,83]},{\"tag\":\"mate\",\"ridge\":674,\"a\":87,\"owners\":[55,88]},{\"tag\":\"mate\",\"ridge\":674,\"a\":88,\"owners\":[55,87]},{\"tag\":\"mate\",\"ridge\":212,\"a\":63,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":404,\"a\":65,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":120,\"a\":66,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":120,\"a\":82,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":216,\"a\":69,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":600,\"a\":70,\"owners\":[85]},{\"tag\":\"mate\",\"ridge\":600,\"a\":85,\"owners\":[70]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[67,71,73],\"full_literals\":[-56,37,41,43]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[35,36,38],\"full_literals\":[-57,10,11,13]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[48,49,50,51,52,53,54],\"full_literals\":[-58,22,23,24,25,26,27,28]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[29,42,43,44,46,47],\"full_literals\":[-59,7,17,18,19,20,21]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[39,41],\"full_literals\":[-60,14,16]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-61,false,56],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-62,false,61],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-63,false,57],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-64,59,60],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-65,59,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-65,false,60],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-66,58,65],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-67,58,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-66,false,64],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-67,false,65],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-68,63,67],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-68,false,66],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0008\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-69,false,67],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-70,62,69],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-70,false,68],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":32,\"full_literals\":[-9,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":60,\"full_literals\":[-31,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":62,\"full_literals\":[-33,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":78,\"full_literals\":[-45,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":79,\"full_literals\":[-46,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":80,\"full_literals\":[-47,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":37,\"full_literals\":[-12,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":40,\"full_literals\":[-15,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":55,\"full_literals\":[-29,73]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[77,83,87],\"full_literals\":[-74,44,49,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":83,\"full_literals\":[-49,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":87,\"full_literals\":[-53,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":66,\"full_literals\":[-36,75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":70,\"full_literals\":[-40,75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":86,\"full_literals\":[-52,75]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[82,84,85],\"full_literals\":[-76,48,50,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":82,\"full_literals\":[-48,76]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":84,\"full_literals\":[-50,76]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":85,\"full_literals\":[-51,76]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":88,\"full_literals\":[-54,77]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":89,\"full_literals\":[-55,77]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-73,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-72,false,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-78,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-71,false,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-80,74,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-75,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-74,false,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-74,-75,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-77,82],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-83,76,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-76,false,82],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-76,-77,83],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-84,80,83],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-83,84],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-80,-82,84],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-80,-83,85],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-81,false,84],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3,4],\"right\":[5,6],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-81,-82,85],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-85,86],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5,6],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-79,-84,86],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":16,\"owners\":[6,10,29,37,41,44,46,47,51,52,53,54,55,77,84,85,86,87,88]},{\"tag\":\"edge\",\"edge\":29,\"owners\":[6,18,29,41,44,46,47,59,68,70,71,72,77,84,85,86,87,89]},{\"tag\":\"edge\",\"edge\":32,\"owners\":[19,21,32,40,49,53,61,63,65,67,69,71,73,79,83,86,88,89]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[10,21,41,51,52,53,54,68,70,71,73,84,85,86,88,89]}]}"
  "193 68 0 146 145 0\n194 66 0 193 142 0\n195 64 0 194 139 0\n196 -85 0 188 186 0\n197 5 6 9 15 23 27 32 37 41 43 46 49 52 54 55 0 119 120 123 191 0\n198 -83 78 0 196 146 168 153 114 169 151 155 177 183 173 174 159 160 161 158 122 125 112 80 103 118 162 107 57 126 130 131 136 132 140 144 143 0\n199 75 53 -84 0 188 187 170 198 180 168 153 114 154 161 172 115 156 0\n200 -76 -84 0 188 196 187 170 198 169 151 168 155 154 171 147 178 179 185 166 167 111 107 117 105 110 199 175 157 108 116 106 104 109 197 0\n201 74 -84 0 188 200 165 164 97 83 163 187 170 168 153 114 169 152 151 150 155 154 157 158 116 88 80 118 79 93 96 98 78 82 81 189 0\n202 26 28 54 -84 0 194 193 146 188 187 170 169 151 107 111 94 201 168 153 114 155 117 156 56 130 136 140 143 144 132 131 126 54 150 152 86 55 141 133 127 21 137 200 165 124 163 164 87 97 92 128 18 0\n203 -26 54 -84 0 193 146 188 187 170 169 151 107 111 94 201 168 153 114 155 117 156 56 130 136 140 143 144 132 131 126 150 152 86 55 141 133 127 21 2 200 163 121 171 149 148 29 34 85 0\n204 54 -84 0 188 193 146 201 200 163 121 187 170 168 153 114 169 152 151 150 155 171 149 148 94 111 107 117 86 156 55 56 130 136 140 143 141 144 133 132 127 131 2 21 126 203 202 40 46 85 0\n205 -28 -84 0 188 204 200 163 187 170 169 152 150 40 41 43 46 48 89 0\n206 -2 13 22 24 -84 0 188 194 193 205 204 68 66 65 64 200 163 187 170 169 150 152 164 87 165 97 83 29 128 137 138 135 136 141 133 127 1 77 129 14 16 130 0\n207 13 22 24 -84 0 188 193 205 204 68 64 200 163 187 170 169 150 152 164 87 165 97 206 89 2 30 127 128 133 138 141 0\n208 -13 -84 0 195 204 66 65 200 165 164 83 3 4 7 8 13 130 129 134 0\n209 -22 -84 0 205 204 200 165 18 19 34 100 0\n210 -84 0 200 165 204 205 208 209 207 20 24 36 100 0\n211 -83 0 210 181 0\n212 -81 0 210 184 0\n213 -24 0 193 146 20 21 22 23 24 28 36 48 91 130 99 136 112 140 143 141 144 133 132 127 131 50 126 0\n214 -37 51 3 26 28 54 16 0 124 92 111 52 59 63 75 97 95 109 192 0\n215 51 3 26 28 54 16 0 146 111 124 92 214 126 131 132 144 143 140 136 130 26 51 57 60 73 90 97 192 0\n216 -51 0 210 125 165 160 178 173 182 0\n217 -40 0 216 124 0\n218 -67 -3 26 28 16 22 0 213 37 25 138 140 128 136 84 130 0\n219 -37 -3 54 0 216 59 63 93 0\n220 -52 15 0 212 116 161 157 175 0\n221 -43 0 53 112 220 0\n222 -52 16 0 195 60 61 62 220 130 5 9 11 15 134 129 0\n223 -15 28 54 16 0 216 222 32 58 215 93 0\n224 26 28 54 16 22 0 216 221 146 111 215 218 219 143 126 144 131 132 0\n225 55 49 46 32 15 27 23 37 41 6 9 52 54 0 221 197 104 0\n226 28 54 16 22 0 211 111 222 223 115 224 31 35 39 96 113 59 164 179 167 109 106 225 0\n227 54 16 22 0 216 211 222 111 226 42 44 47 49 98 113 115 59 164 179 167 109 106 225 0\n228 16 22 0 210 216 217 222 227 66 67 69 70 71 72 76 166 176 182 174 158 103 79 78 82 101 102 190 0\n229 22 0 213 194 228 6 10 12 16 17 27 33 38 45 74 94 105 65 128 129 137 135 0\n230 -3 0 229 18 0\n231 -16 0 229 19 0\n232 -26 0 229 34 0\n233 -28 0 229 46 0\n234 54 0 232 216 233 230 231 215 0\n235 0 232 234 216 230 233 231 100 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record005.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record005.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record005.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record005.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record005 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record005.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record005.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record005.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record005.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record005 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record005_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record005 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record005_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record005_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00096.record005

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00096.record014
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "ae15c1f2b2aaa9a96a3a2e87aa58d62d8765392e1b85e0fab1aa699965598e4b91e695554d51d54d4b46d4745d0f6a3a4e5334e332cc73c2e8b92e2b4acab1ae1b26c5b0ee8761cc749c6785c9715c3743c4f0bc1f2d14a518a6a44b15261916439514a5254550d68350ca382d0b12c2b41c8711c27"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db6db6d34db69a49249249b6924db4d249249a49249a4924c9249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record014 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record014 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record014.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 27), (facetIndex 28), (facetIndex 29), (facetIndex 57), (facetIndex 58), (facetIndex 62), (facetIndex 79)]))
 (.leaf ([(facetIndex 30), (facetIndex 31), (facetIndex 32), (facetIndex 39), (facetIndex 40), (facetIndex 42), (facetIndex 51), (facetIndex 55), (facetIndex 81)])))
 (.branch 3
 (.leaf ([(facetIndex 63), (facetIndex 64), (facetIndex 65)]))
 (.leaf ([(facetIndex 66), (facetIndex 68), (facetIndex 72), (facetIndex 74)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 34), (facetIndex 35), (facetIndex 36), (facetIndex 37), (facetIndex 38)]))
 (.leaf ([(facetIndex 67), (facetIndex 69), (facetIndex 70), (facetIndex 71)])))
 (.branch 7
 (.leaf ([(facetIndex 43), (facetIndex 44), (facetIndex 45), (facetIndex 46), (facetIndex 47), (facetIndex 48), (facetIndex 49)]))
 (.leaf ([(facetIndex 56)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "80000c3b6bad2400007200236db6c4132490124z16;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2, 3]
def grouped2_0006 : List Nat := [4, 5]
def grouped2_0007 : List Nat := [4, 5, 6, 7]
def grouped2_0008 : List Nat := [6]
def grouped2_0009 : List Nat := [6, 7]
def grouped2_0010 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record014 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record014_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00096.record014" "{\"atoms\":[{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00096.record014" 24

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00096.record014" "{\"ridges\":[[42,522],[56,642],[81,134]],\"owners\":[[81,134,[2,36,37,38],[22,32,82,83]],[42,522,[89],[7,46,47,48,49,86,87,88]],[56,642,[83,88],[10,38,48,55,89,90]]],\"edges\":[],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00096.record014" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00096.record014\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":false,\"clauses\":[[-13,-1],[-13,-4],[-13,-5],[-13,-6],[-13,-7],[-13,-11],[-13,-12],[-15,-2],[-15,-3],[-15,-8],[-15,-9],[-16,-2],[-16,-3],[-16,-8],[-16,-9],[-17,-13],[-14,1,5,6,7],[-10,17],[-13,15,16],[-18,2,3,4,8,9,10,11,12,14],[-19,13],[-20,18],[-21,20],[-22,19],[-23,22],[-24,21],[-24,23],[24]],\"atoms\":[{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":56,\"b\":2},{\"tag\":\"incompatible\",\"a\":56,\"b\":32},{\"tag\":\"incompatible\",\"a\":56,\"b\":36},{\"tag\":\"incompatible\",\"a\":56,\"b\":37},{\"tag\":\"incompatible\",\"a\":56,\"b\":38},{\"tag\":\"incompatible\",\"a\":56,\"b\":51},{\"tag\":\"incompatible\",\"a\":56,\"b\":55},{\"tag\":\"incompatible\",\"a\":83,\"b\":30},{\"tag\":\"incompatible\",\"a\":83,\"b\":31},{\"tag\":\"incompatible\",\"a\":83,\"b\":39},{\"tag\":\"incompatible\",\"a\":83,\"b\":40},{\"tag\":\"incompatible\",\"a\":88,\"b\":30},{\"tag\":\"incompatible\",\"a\":88,\"b\":31},{\"tag\":\"incompatible\",\"a\":88,\"b\":39},{\"tag\":\"incompatible\",\"a\":88,\"b\":40},{\"tag\":\"incompatible\",\"a\":89,\"b\":56},{\"tag\":\"mate\",\"ridge\":134,\"a\":81,\"owners\":[2,36,37,38]},{\"tag\":\"mate\",\"ridge\":522,\"a\":42,\"owners\":[89]},{\"tag\":\"mate\",\"ridge\":642,\"a\":56,\"owners\":[83,88]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[30,31,32,39,40,42,51,55,81],\"full_literals\":[-18,2,3,4,8,9,10,11,12,14]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[56],\"full_literals\":[-19,13]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-20,false,18],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-21,20,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-22,false,19],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-23,false,22],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-24,21,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-24,false,23],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true}]}"
  "29 21 0 28 26 0\n30 23 0 28 27 0\n31 20 0 29 23 0\n32 22 0 30 25 0\n33 18 0 31 22 0\n34 19 0 32 24 0\n35 13 0 34 21 0\n36 -1 0 35 1 0\n37 -4 0 35 2 0\n38 -5 0 35 3 0\n39 -6 0 35 4 0\n40 -7 0 35 5 0\n41 -11 0 35 6 0\n42 -12 0 35 7 0\n43 -17 0 35 16 0\n44 -14 0 36 38 39 40 17 0\n45 -10 0 43 18 0\n46 -15 0 44 42 41 45 37 33 8 9 10 11 20 0\n47 16 0 46 35 19 0\n48 -2 0 47 12 0\n49 -3 0 47 13 0\n50 -8 0 47 14 0\n51 -9 0 47 15 0\n52 0 50 51 33 37 48 49 45 41 42 44 20 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record014.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record014.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record014.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record014.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record014 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS noSame
  exact boundary_unsat S HS noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record014.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record014.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record014.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record014.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record014 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record014_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record014_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record014_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record014_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record014_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record014_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record014_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record014 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record014_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record014_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record014_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00096.record014

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00096.record020
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "23c5c96a4ea96558b61da8e53a1e4783e5c569c66394e5558d4b51d68d9354d8b61d4743d58e9364d534ccb31ce8b4ae1b46c3ba1d4731ca785d1715e0f43c8f07e941b14a1a866258361382ea45491a68519615254358344d0b54318d1324c3342c4b0ac8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "369a6934da69b6d249249a4924934d2492492491249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record020 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record020 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record020.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record020.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record020.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 35), (facetIndex 38), (facetIndex 42), (facetIndex 60), (facetIndex 75)]))
 (.leaf ([(facetIndex 47), (facetIndex 51), (facetIndex 55), (facetIndex 70), (facetIndex 82)])))
 (.branch 3
 (.leaf ([(facetIndex 39), (facetIndex 43), (facetIndex 54), (facetIndex 64), (facetIndex 80)]))
 (.leaf ([(facetIndex 40), (facetIndex 72), (facetIndex 77), (facetIndex 78)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 36), (facetIndex 58), (facetIndex 59), (facetIndex 61), (facetIndex 62)]))
 (.leaf ([(facetIndex 33), (facetIndex 34), (facetIndex 37), (facetIndex 41)])))
 (.branch 7
 (.leaf ([(facetIndex 49), (facetIndex 50), (facetIndex 52), (facetIndex 53)]))
 (.branch 8
 (.leaf ([(facetIndex 56), (facetIndex 63), (facetIndex 65)]))
 (.leaf ([(facetIndex 44), (facetIndex 45)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "10203300003010000727440440712661660108820532054055z21;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 46), (facetIndex 48)]))
 (.branch 2
 (.leaf ([(facetIndex 74), (facetIndex 76)]))
 (.leaf ([(facetIndex 66), (facetIndex 71)]))))
 (.branch 4
 (.leaf ([(facetIndex 79), (facetIndex 83)]))
 (.branch 5
 (.leaf ([(facetIndex 57), (facetIndex 67), (facetIndex 68), (facetIndex 69)]))
 (.leaf ([(facetIndex 73), (facetIndex 81), (facetIndex 84)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "562860106842488000002z2b;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 6
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
def grouped3_0014 : List Nat := [0, 1, 2]
def grouped3_0016 : List Nat := [1]
def grouped3_0017 : List Nat := [1, 2]
def grouped3_0018 : List Nat := [2]
def grouped3_0019 : List Nat := [3]
def grouped3_0020 : List Nat := [3, 4, 5]
def grouped3_0021 : List Nat := [4]
def grouped3_0022 : List Nat := [4, 5]
def grouped3_0023 : List Nat := [5]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record020 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record020_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00096.record020" "{\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00096.record020" 62

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00096.record020" "{\"ridges\":[[10,273],[15,521],[36,524],[38,273],[45,273],[51,273],[52,273],[53,273],[58,521],[59,521],[61,521],[62,521],[66,340],[69,792],[71,368],[73,284],[79,340],[81,312],[83,368]],\"owners\":[[10,273,[57,66,67,69,71],[38,45,51,52,53]],[38,273,[67,69,71],[10,45,51,52,53,57,66]],[45,273,[66,71],[10,38,51,52,53,57,67,69]],[51,273,[57,66,69],[10,38,45,52,53,67,71]],[52,273,[57,67,69],[10,38,45,51,53,66,71]],[53,273,[57,66,67,69,71],[10,38,45,51,52]],[15,521,[46,48,68,69],[36,58,59,61,62]],[58,521,[48],[15,36,46,59,61,62,68,69]],[59,521,[46,48,69],[15,36,58,61,62,68]],[61,521,[46,48,68,69],[15,36,58,59,62]],[62,521,[46,68,69],[15,36,48,58,59,61]],[36,524,[84],[15,58,59,61,62,74,76]],[73,284,[57],[]],[66,340,[79],[]],[79,340,[66],[]],[81,312,[67],[]],[69,792,[],[]],[71,368,[83],[]],[83,368,[71],[]]],\"edges\":[[29,[15,36,46,48,58,59,61,62,68,69,74,76,84]],[33,[10,38,45,51,52,53,57,66,67,69,71,73,79,81,83]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00096.record020" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00096.record020\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-12,-7],[-13,-7],[-16,-7],[-18,-3],[-18,-6],[-18,-7],[-21,-18],[-25,-7],[-25,-10],[-25,-14],[-25,-17],[-28,-25],[-32,-18],[-36,-25],[-1,18,24,25,27,29],[-5,25,27,29],[-8,24,29],[-14,18,24,27],[-15,18,25,27],[-16,18,24,25,27,29],[-2,9,11,26,27],[-19,11],[-20,9,11,27],[-22,9,11,26,27],[-23,9,26,27],[-4,38],[-30,18],[-24,34],[-34,24],[-35,25],[-27],[-29,37],[-37,29],[-39,3,5,6,21,32],[-40,10,14,17,28,36],[-41,12,13,15,16],[-42,7,8],[-43,39],[-43,40],[-44,43],[-45,42],[-46,41],[-46,45],[-47,46],[-48,44,47],[48],[-9,49],[-11,49],[-31,50],[-33,50],[-51,24,29],[-24,51],[-29,51],[-34,52],[-37,52],[-26,53],[-38,54],[-51,55],[-50,-51,56],[-55,57],[-56,58],[-49,-55,58],[-54,59],[-53,59],[-52,60],[-52,-59,61],[-57,-61,62],[-58,-60,62],[-62],[2,4,9,11,19,20,22,23,26,27,31,33,38],[1,5,8,14,15,16,18,24,25,27,29,30,34,35,37]],\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":49,\"b\":44},{\"tag\":\"incompatible\",\"a\":50,\"b\":44},{\"tag\":\"incompatible\",\"a\":53,\"b\":44},{\"tag\":\"incompatible\",\"a\":57,\"b\":35},{\"tag\":\"incompatible\",\"a\":57,\"b\":42},{\"tag\":\"incompatible\",\"a\":57,\"b\":44},{\"tag\":\"incompatible\",\"a\":60,\"b\":57},{\"tag\":\"incompatible\",\"a\":67,\"b\":44},{\"tag\":\"incompatible\",\"a\":67,\"b\":47},{\"tag\":\"incompatible\",\"a\":67,\"b\":51},{\"tag\":\"incompatible\",\"a\":67,\"b\":55},{\"tag\":\"incompatible\",\"a\":70,\"b\":67},{\"tag\":\"incompatible\",\"a\":75,\"b\":57},{\"tag\":\"incompatible\",\"a\":82,\"b\":67},{\"tag\":\"mate\",\"ridge\":273,\"a\":10,\"owners\":[57,66,67,69,71]},{\"tag\":\"mate\",\"ridge\":273,\"a\":38,\"owners\":[67,69,71]},{\"tag\":\"mate\",\"ridge\":273,\"a\":45,\"owners\":[66,71]},{\"tag\":\"mate\",\"ridge\":273,\"a\":51,\"owners\":[57,66,69]},{\"tag\":\"mate\",\"ridge\":273,\"a\":52,\"owners\":[57,67,69]},{\"tag\":\"mate\",\"ridge\":273,\"a\":53,\"owners\":[57,66,67,69,71]},{\"tag\":\"mate\",\"ridge\":521,\"a\":15,\"owners\":[46,48,68,69]},{\"tag\":\"mate\",\"ridge\":521,\"a\":58,\"owners\":[48]},{\"tag\":\"mate\",\"ridge\":521,\"a\":59,\"owners\":[46,48,69]},{\"tag\":\"mate\",\"ridge\":521,\"a\":61,\"owners\":[46,48,68,69]},{\"tag\":\"mate\",\"ridge\":521,\"a\":62,\"owners\":[46,68,69]},{\"tag\":\"mate\",\"ridge\":524,\"a\":36,\"owners\":[84]},{\"tag\":\"mate\",\"ridge\":284,\"a\":73,\"owners\":[57]},{\"tag\":\"mate\",\"ridge\":340,\"a\":66,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":340,\"a\":79,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":312,\"a\":81,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":792,\"a\":69,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":368,\"a\":71,\"owners\":[83]},{\"tag\":\"mate\",\"ridge\":368,\"a\":83,\"owners\":[71]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[35,38,42,60,75],\"full_literals\":[-39,3,5,6,21,32]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[47,51,55,70,82],\"full_literals\":[-40,10,14,17,28,36]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[49,50,52,53],\"full_literals\":[-41,12,13,15,16]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[44,45],\"full_literals\":[-42,7,8]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-43,39,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-43,false,40],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-44,43,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-45,false,42],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-46,41,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-46,false,45],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-47,false,46],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-48,44,47],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":46,\"full_literals\":[-9,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":48,\"full_literals\":[-11,49]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":74,\"full_literals\":[-31,50]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":76,\"full_literals\":[-33,50]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[66,71],\"full_literals\":[-51,24,29]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":66,\"full_literals\":[-24,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":71,\"full_literals\":[-29,51]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":79,\"full_literals\":[-34,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":83,\"full_literals\":[-37,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":68,\"full_literals\":[-26,53]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":84,\"full_literals\":[-38,54]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-51,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-50,-51,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-55,57],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-56,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-49,-55,58],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-54,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-53,false,59],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-52,false,60],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-52,-59,61],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-57,-61,62],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-58,-60,62],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":29,\"owners\":[15,36,46,48,58,59,61,62,68,69,74,76,84]},{\"tag\":\"edge\",\"edge\":33,\"owners\":[10,38,45,51,52,53,57,66,67,69,71,73,79,81,83]}]}"
  "72 2 4 9 11 19 20 22 23 26 31 33 38 0 31 70 0\n73 1 5 8 14 15 16 18 24 25 29 30 34 35 37 0 31 71 0\n74 -46 8 0 31 42 43 41 37 1 2 3 6 8 36 19 0\n75 18 25 51 0 31 30 53 16 52 17 33 29 15 18 19 20 27 73 0\n76 25 51 0 46 31 52 53 17 74 44 45 40 38 16 75 4 5 7 13 34 0\n77 51 0 46 52 53 17 74 44 45 40 39 76 9 10 11 12 14 35 0\n78 55 0 77 58 0\n79 57 0 78 60 0\n80 -61 0 79 69 67 0\n81 -52 0 80 69 78 77 31 65 66 68 63 64 61 62 57 56 59 47 48 26 25 49 50 22 23 21 24 72 0\n82 -34 0 81 54 0\n83 -37 0 81 55 0\n84 -24 0 82 28 0\n85 -29 0 83 32 0\n86 0 84 85 77 51 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record020.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record020.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record020.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record020.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record020 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record020.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record020.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record020.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record020.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record020 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record020_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record020_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record020_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record020_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record020_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record020_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record020_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record020 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record020_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record020_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00096.record020_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00096.record020
