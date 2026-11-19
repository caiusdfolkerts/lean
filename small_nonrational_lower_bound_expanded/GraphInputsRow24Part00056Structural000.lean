module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow24Part00056Data
public import GraphInputsRow24Part00056Frames
public import GraphInputsRow24Part00056Leaves
public import GraphInputsRow24Part00056Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00056.record002
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record002
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨36, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨47, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨73, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨84, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), 1441292618246914048, 16888498619416576, 594475219532382208, 15133048832, (certNat% 4)]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record002_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record002_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00056.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00056.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record003
def vertexColumn : Fields := ⟨10, (certNat% 5)⟩
def kindColumn : Fields := ⟨3, (certNat% 6)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨47, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨65, by decide⟩, ⟨75, by decide⟩, ⟨83, by decide⟩, ⟨85, by decide⟩, ⟨87, by decide⟩, ⟨95, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), 432345564227567616, (certNat% 8), 74309393851613184, (certNat% 9)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), 309246033920, 651896046061879296, (certNat% 11), 805306368, 445856363109679104]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 12), (certNat% 13), 1374414700544, (certNat% 14), 805306368, 445856363109679104]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 15), 309237645312, (certNat% 16), (certNat% 17), 140737488355328]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), 309246033920, (certNat% 11), 432345564764438528, 79938893385826304, 268435456]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 19), (certNat% 20), (certNat% 8), 279183360000, 432345564898656256, 72059793363173376, 15762598695796736]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨83, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨22, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record003_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00056.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00056.record010
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record010
def vertexColumn : Fields := ⟨10, (certNat% 21)⟩
def kindColumn : Fields := ⟨3, (certNat% 22)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨73, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨84, by decide⟩, ⟨86, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 23), (certNat% 24), 3404087999594496, 8070450532382146560, (certNat% 25)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 26), (certNat% 27), 20341166440448, (certNat% 28), 8070450532247928832]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), (certNat% 27), 2603644339879936, 8070450532247928832, (certNat% 28)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 30), (certNat% 31), (certNat% 32), 1055531162664960, 31525203834044416]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 33), (certNat% 34), 3404087999594496, 9219956902199296, 18865420509380608]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 35), (certNat% 34), 3404087999594496, 18865424804347904, 9219954754715648]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [9043263545571016704, (certNat% 36), (certNat% 37), (certNat% 38), 18865424804347904, 9219974082068480, 5638295627235328]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨38, by decide⟩ c9 c2
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c10 c1
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c11 c0
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record010_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record010_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00056.record010

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00056.record023
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record023
def vertexColumn : Fields := ⟨10, (certNat% 39)⟩
def kindColumn : Fields := ⟨3, (certNat% 40)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨66, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨74, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 41), (certNat% 42), (certNat% 43), 13528391068155904, 35184372088832]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 44), 1008806320825958400, (certNat% 45), 9024928879738880, 105553116266496, 2305843077933170688]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 46), 1080863914863886336, (certNat% 47), 13537324600131584, 3476778981049499648, 111052821889024, 2111122454872064]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record023_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record023_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record023_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record023_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record023_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record023_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record023_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record023_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record023_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00056.record023

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00056.record004
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "174e316c7296a36966a5876a398e5392e1b89e179d16c571e25c95a4d9e1565a5595555351d70da358d5352d1b49d175c368d63a4cd32cd8b92d4b32d2b1ac9b16e8761d4789d2719e1725c5743c8f13c2f07c72a2836839611c68962549494358350da0c6324c530ce0b22c4b81c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6db6936db6da49369b6924926db6924924d249b492492491249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record004 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record004 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record004.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record004.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record004.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 51), (facetIndex 73)]))
 (.leaf ([(facetIndex 37), (facetIndex 54), (facetIndex 64), (facetIndex 65), (facetIndex 67)])))
 (.branch 3
 (.leaf ([(facetIndex 52), (facetIndex 68), (facetIndex 74)]))
 (.branch 4
 (.leaf ([(facetIndex 76), (facetIndex 80), (facetIndex 83), (facetIndex 89)]))
 (.leaf ([(facetIndex 85), (facetIndex 87)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 36), (facetIndex 42), (facetIndex 55)]))
 (.leaf ([(facetIndex 53), (facetIndex 63), (facetIndex 77), (facetIndex 79)])))
 (.branch 8
 (.leaf ([(facetIndex 78), (facetIndex 84), (facetIndex 88)]))
 (.branch 9
 (.leaf ([(facetIndex 86)]))
 (.leaf ([(facetIndex 75), (facetIndex 90)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "9374847300367639200000210116000000051620000000005000015z24;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1]
def grouped3_0002 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0004 : List Nat := [1]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [2, 3, 4]
def grouped3_0007 : List Nat := [3]
def grouped3_0008 : List Nat := [3, 4]
def grouped3_0009 : List Nat := [4]
def grouped3_0010 : List Nat := [5]
def grouped3_0011 : List Nat := [5, 6]
def grouped3_0012 : List Nat := [5, 6, 7, 8, 9]
def grouped3_0013 : List Nat := [6]
def grouped3_0014 : List Nat := [7]
def grouped3_0015 : List Nat := [7, 8, 9]
def grouped3_0016 : List Nat := [8]
def grouped3_0017 : List Nat := [8, 9]
def grouped3_0018 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record004 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record004_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00056.record004" "{\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00056.record004" 57

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00056.record004" "{\"ridges\":[[9,145],[15,292],[20,352],[31,145],[34,292],[40,145],[42,298],[47,145],[48,145],[49,145],[50,352],[51,418],[56,292],[62,292],[64,404],[66,292],[69,352],[72,352],[73,432],[74,464],[75,92],[78,298],[84,326],[86,298],[88,108],[90,340]],\"owners\":[[9,145,[54,64,65,68,73,74],[31,40,47,48,49]],[31,145,[68,73,74],[9,40,47,48,49,54,64,65]],[40,145,[64,65,73,74],[9,31,47,48,49,54,68]],[47,145,[54,64,65,68,74],[9,31,40,48,49,73]],[48,145,[54,64,65,73],[9,31,40,47,49,68,74]],[49,145,[54,64,68,73,74],[9,31,40,47,48,65]],[15,292,[78,84,88,90],[34,56,62,66]],[34,292,[88,90],[15,56,62,66,78,84]],[56,292,[84,90],[15,34,62,66,78,88]],[62,292,[78,84,88],[15,34,56,66,90]],[66,292,[78],[15,34,56,62,84,88,90]],[20,352,[84,86,88,90],[50,66,69,72]],[50,352,[88,90],[20,66,69,72,84,86]],[69,352,[84,90],[20,50,66,72,86,88]],[72,352,[84,86,88],[20,50,66,69,90]],[84,326,[36,79],[]],[42,298,[78,86],[]],[78,298,[42,86],[]],[86,298,[42,78],[]],[51,418,[],[]],[75,92,[53],[]],[88,108,[55,77],[]],[90,340,[63],[]],[64,404,[],[]],[73,432,[],[]],[74,464,[],[]]],\"edges\":[[32,[9,31,40,47,48,49,54,64,65,68,73,74,76,83,85]],[37,[15,20,34,42,50,51,56,62,66,69,72,73,78,84,86,88,90]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00056.record004" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00056.record004\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,15,20,21,23,26,27],[-4,23,26,27],[-7,20,21,26,27],[-9,15,20,21,23,27],[-10,15,20,21,26],[-11,15,20,23,26,27],[-2,31,34,37,38],[-5,37,38],[-17,34,38],[-18,31,34,37],[-22,31],[-3,34,36,37,38],[-12,37,38],[-24,34,38],[-25,34,36,37],[-34,6,32],[-8,31,36],[-31,8,36],[-36,8,31],[-13],[-28,14],[-37,16,30],[-38,19],[-20],[-26],[-27],[-15,39],[-21,39],[-23,40],[-29,41],[-33,41],[-35,42],[-6,43],[-8,43],[-16,43],[-14,44],[-19,44],[-30,44],[-32,44],[-45,31,34,37],[-31,45],[-34,45],[-37,45],[-46,36],[-36,46],[-47,28,38],[-38,47],[-39,48],[-42,49],[-41,49],[-49,50],[-40,50],[-50,51],[-48,51],[-44,52],[-43,52],[-53,46,47],[-47,53],[-46,53],[-54,45,53],[-53,54],[-45,54],[-45,-53,55],[-55,56],[-52,-54,56],[-51,-56,57],[-57],[1,4,7,9,10,11,15,20,21,23,26,27,29,33,35],[2,3,5,8,12,13,17,18,22,24,25,26,31,34,36,37,38]],\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":145,\"a\":9,\"owners\":[54,64,65,68,73,74]},{\"tag\":\"mate\",\"ridge\":145,\"a\":31,\"owners\":[68,73,74]},{\"tag\":\"mate\",\"ridge\":145,\"a\":40,\"owners\":[64,65,73,74]},{\"tag\":\"mate\",\"ridge\":145,\"a\":47,\"owners\":[54,64,65,68,74]},{\"tag\":\"mate\",\"ridge\":145,\"a\":48,\"owners\":[54,64,65,73]},{\"tag\":\"mate\",\"ridge\":145,\"a\":49,\"owners\":[54,64,68,73,74]},{\"tag\":\"mate\",\"ridge\":292,\"a\":15,\"owners\":[78,84,88,90]},{\"tag\":\"mate\",\"ridge\":292,\"a\":34,\"owners\":[88,90]},{\"tag\":\"mate\",\"ridge\":292,\"a\":56,\"owners\":[84,90]},{\"tag\":\"mate\",\"ridge\":292,\"a\":62,\"owners\":[78,84,88]},{\"tag\":\"mate\",\"ridge\":292,\"a\":66,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":352,\"a\":20,\"owners\":[84,86,88,90]},{\"tag\":\"mate\",\"ridge\":352,\"a\":50,\"owners\":[88,90]},{\"tag\":\"mate\",\"ridge\":352,\"a\":69,\"owners\":[84,90]},{\"tag\":\"mate\",\"ridge\":352,\"a\":72,\"owners\":[84,86,88]},{\"tag\":\"mate\",\"ridge\":326,\"a\":84,\"owners\":[36,79]},{\"tag\":\"mate\",\"ridge\":298,\"a\":42,\"owners\":[78,86]},{\"tag\":\"mate\",\"ridge\":298,\"a\":78,\"owners\":[42,86]},{\"tag\":\"mate\",\"ridge\":298,\"a\":86,\"owners\":[42,78]},{\"tag\":\"mate\",\"ridge\":418,\"a\":51,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":92,\"a\":75,\"owners\":[53]},{\"tag\":\"mate\",\"ridge\":108,\"a\":88,\"owners\":[55,77]},{\"tag\":\"mate\",\"ridge\":340,\"a\":90,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":404,\"a\":64,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":432,\"a\":73,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":464,\"a\":74,\"owners\":[]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":54,\"full_literals\":[-15,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":65,\"full_literals\":[-21,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":68,\"full_literals\":[-23,40]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":76,\"full_literals\":[-29,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":83,\"full_literals\":[-33,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":85,\"full_literals\":[-35,42]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":36,\"full_literals\":[-6,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":42,\"full_literals\":[-8,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":55,\"full_literals\":[-16,43]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":53,\"full_literals\":[-14,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":63,\"full_literals\":[-19,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":77,\"full_literals\":[-30,44]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":79,\"full_literals\":[-32,44]},{\"tag\":\"group_or\",\"kind\":3,\"index\":7,\"members\":[78,84,88],\"full_literals\":[-45,31,34,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":78,\"full_literals\":[-31,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":84,\"full_literals\":[-34,45]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":88,\"full_literals\":[-37,45]},{\"tag\":\"group_or\",\"kind\":3,\"index\":8,\"members\":[86],\"full_literals\":[-46,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":86,\"full_literals\":[-36,46]},{\"tag\":\"group_or\",\"kind\":3,\"index\":9,\"members\":[75,90],\"full_literals\":[-47,28,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":90,\"full_literals\":[-38,47]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-39,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-42,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-41,false,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-49,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0008\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-40,false,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-50,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-48,false,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-44,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-43,false,52],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-53,46,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-47,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-46,false,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-54,45,53],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-53,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-45,false,54],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-45,-53,55],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-55,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-52,-54,56],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-51,-56,57],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":32,\"owners\":[9,31,40,47,48,49,54,64,65,68,73,74,76,83,85]},{\"tag\":\"edge\",\"edge\":37,\"owners\":[15,20,34,42,50,51,56,62,66,69,72,73,78,84,86,88,90]}]}"
  "70 1 4 7 9 10 11 15 21 23 29 33 35 0 24 25 26 68 0\n71 2 3 5 8 12 17 18 22 24 25 31 34 36 37 38 0 20 25 69 0\n72 51 0 26 25 24 53 54 51 52 48 49 50 29 27 28 32 30 31 2 6 1 3 4 5 70 0\n73 -56 0 72 67 66 0\n74 -55 0 73 64 0\n75 -53 52 0 74 55 37 23 36 21 46 56 34 57 63 44 41 19 0\n76 -54 0 73 65 55 56 38 39 33 34 35 22 16 75 59 60 45 40 18 0\n77 -53 0 76 61 0\n78 -45 0 76 62 0\n79 -47 0 77 58 0\n80 -46 0 77 59 0\n81 -31 0 78 41 0\n82 -34 0 78 42 0\n83 -37 0 78 43 0\n84 -38 0 79 47 0\n85 -36 0 80 45 0\n86 -2 0 81 82 83 84 7 0\n87 -18 0 81 82 83 10 0\n88 -22 0 81 11 0\n89 -8 0 81 85 17 0\n90 -17 0 82 84 9 0\n91 -24 0 82 84 14 0\n92 -5 0 83 84 8 0\n93 -12 0 83 84 13 0\n94 -3 0 85 82 83 84 12 0\n95 -25 0 85 82 83 15 0\n96 0 87 88 86 94 89 90 92 93 91 95 81 82 85 83 84 71 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record004.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record004.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record004.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record004.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record004 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record004.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record004.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record004.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record004.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record004 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record004_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record004 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record004_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record004_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00056.record004

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00056.record022
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "e61785d16c5713c1f392e296ac6a9a66a3a4e9c659a96659362d94e4b86e4783ea6599566391e5c5a5595554b51d54d1b51d1743d70e9364e332ce8b62e4b52e2b86d1b26c3ba1d8751cc729e1745c970dd0f13c2f07d945286a6194619a911a6190e46525435a0c6382c4b0ac8711c27"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6db6da6db6934da69b4da4d26934da69b69a493692493693499249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record022 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record022 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record022.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record022.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record022.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 37), (facetIndex 42), (facetIndex 46), (facetIndex 63)]))
 (.leaf ([(facetIndex 32), (facetIndex 71), (facetIndex 74)])))
 (.branch 3
 (.leaf ([(facetIndex 23), (facetIndex 39), (facetIndex 40), (facetIndex 80)]))
 (.leaf ([(facetIndex 26), (facetIndex 29), (facetIndex 30), (facetIndex 33)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 22), (facetIndex 25), (facetIndex 48), (facetIndex 51), (facetIndex 53)]))
 (.leaf ([(facetIndex 54), (facetIndex 56), (facetIndex 57)])))
 (.branch 7
 (.leaf ([(facetIndex 34), (facetIndex 38), (facetIndex 59), (facetIndex 60)]))
 (.leaf ([(facetIndex 31), (facetIndex 66), (facetIndex 68), (facetIndex 73)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "20000782071c0006c2d160804000002580199ed80e05z11;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 35), (facetIndex 41), (facetIndex 81)]))
 (.leaf ([(facetIndex 62), (facetIndex 77), (facetIndex 89)])))
 (.branch 3
 (.leaf ([(facetIndex 24), (facetIndex 27), (facetIndex 47), (facetIndex 55)]))
 (.leaf ([(facetIndex 36), (facetIndex 50), (facetIndex 58), (facetIndex 61)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 49), (facetIndex 67), (facetIndex 87)]))
 (.leaf ([(facetIndex 83), (facetIndex 84), (facetIndex 88)])))
 (.branch 7
 (.leaf ([(facetIndex 21), (facetIndex 28), (facetIndex 43), (facetIndex 44), (facetIndex 45), (facetIndex 70), (facetIndex 78), (facetIndex 79)]))
 (.branch 8
 (.leaf ([(facetIndex 64), (facetIndex 69), (facetIndex 72), (facetIndex 75), (facetIndex 76), (facetIndex 82)]))
 (.leaf ([(facetIndex 52), (facetIndex 65), (facetIndex 85), (facetIndex 86)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "154885570066177007067040870130030020080340206660000003000000062002006z15;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 9
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
def grouped2_0008 : List Nat := [4, 5]
def grouped2_0009 : List Nat := [4, 5, 6, 7]
def grouped2_0010 : List Nat := [6]
def grouped2_0011 : List Nat := [6, 7]
def grouped2_0012 : List Nat := [7]
def grouped3_0013 : List Nat := [0]
def grouped3_0014 : List Nat := [0, 1]
def grouped3_0015 : List Nat := [0, 1, 2, 3]
def grouped3_0017 : List Nat := [1]
def grouped3_0018 : List Nat := [2]
def grouped3_0019 : List Nat := [2, 3]
def grouped3_0020 : List Nat := [3]
def grouped3_0021 : List Nat := [4]
def grouped3_0022 : List Nat := [4, 5]
def grouped3_0023 : List Nat := [4, 5, 6, 7, 8]
def grouped3_0024 : List Nat := [5]
def grouped3_0025 : List Nat := [6]
def grouped3_0026 : List Nat := [6, 7, 8]
def grouped3_0027 : List Nat := [7]
def grouped3_0028 : List Nat := [7, 8]
def grouped3_0029 : List Nat := [8]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record022 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record022_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00056.record022" "{\"atoms\":[{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0015\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00056.record022" 75

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00056.record022" "{\"ridges\":[[1,70],[19,328],[32,386],[39,328],[40,67],[42,642],[45,275],[52,269],[63,656],[65,280],[66,70],[68,328],[71,400],[74,70],[74,386],[75,280],[79,280],[79,786],[80,328],[82,786],[85,92],[86,300]],\"owners\":[[40,67,[1,6,30,31,47],[4,39]],[42,642,[72,82],[7,33,46,78,81]],[63,656,[72,82],[14,46,57,78,89]],[32,386,[77,81,82],[17,41,45,47,71,74]],[74,386,[41,45,77,81,82],[17,32,47,71]],[19,328,[52,61,85,86,88],[39,68,80]],[39,328,[85,86,88],[19,52,61,68,80]],[68,328,[61,88],[19,39,52,80,85,86]],[80,328,[52,61,85],[19,39,68,86,88]],[71,400,[62,89],[20,45,56,77,82]],[52,269,[24,50],[]],[45,275,[27,36],[]],[65,280,[61,62,88,89],[36,50,75,77,79,84,85]],[75,280,[50,61,62,85,89],[36,65,77,79,84,88]],[79,280,[50,61,62,84,85,88],[36,65,75,77,89]],[85,92,[49,83],[]],[86,300,[67,84],[]],[79,786,[82],[]],[82,786,[79],[]]],\"edges\":[[28,[19,24,36,39,41,50,52,61,62,65,67,68,75,77,79,80,81,84,85,86,88,89]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00056.record022" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00056.record022\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-11,-6],[-11,-8],[-11,-9],[-12,-11],[-29,-2],[-29,-4],[-29,-15],[-32,-14],[-32,-20],[-33,-32],[-35,-9],[-35,-10],[-35,-21],[-35,-31],[-35,-34],[-39,-29],[-16,1,2,9,10,21],[-1,-29,-35],[-18,33,41],[-27,33,41],[-11,37,40,41],[-35,17,19,37,40,41],[-3,24,25,44,45,46],[-15,44,45,46],[-31,25,46],[-39,24,25,44],[-32,26,47],[-24,5,23],[-19,7,13],[-28,25,26,46,47],[-36,23,25,26,44,47],[-38,23,25,26,43,44,46],[-44,22,42],[-45,30,43],[-38,41],[-41,38],[-48,14,18,20,27],[-49,11,32,35],[-50,4,15,16,39],[-51,6,8,9,12],[-52,10,29,31,34],[-53,48],[-53,49],[-54,50],[-54,51],[-55,53],[-55,54],[-56,52],[-57,56],[-58,55],[-58,57],[58],[-17,59],[-40,59],[-26,60],[-37,60],[-47,60],[-5,61],[-7,61],[-13,62],[-23,62],[-25,62],[-22,63],[-30,63],[-42,64],[-43,64],[-46,64],[-38,65],[-41,66],[-60,67],[-59,67],[-62,68],[-61,68],[-68,69],[-67,69],[-64,70],[-63,70],[-66,71],[-65,-71,72],[-72,73],[-70,-72,74],[-74,75],[-69,-73,75],[-75],[3,5,13,15,17,23,24,25,26,28,30,31,36,37,38,39,40,43,44,45,46,47]],\"atoms\":[{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":32,\"b\":26},{\"tag\":\"incompatible\",\"a\":32,\"b\":29},{\"tag\":\"incompatible\",\"a\":32,\"b\":30},{\"tag\":\"incompatible\",\"a\":33,\"b\":32},{\"tag\":\"incompatible\",\"a\":66,\"b\":6},{\"tag\":\"incompatible\",\"a\":66,\"b\":23},{\"tag\":\"incompatible\",\"a\":66,\"b\":39},{\"tag\":\"incompatible\",\"a\":71,\"b\":37},{\"tag\":\"incompatible\",\"a\":71,\"b\":46},{\"tag\":\"incompatible\",\"a\":72,\"b\":71},{\"tag\":\"incompatible\",\"a\":74,\"b\":30},{\"tag\":\"incompatible\",\"a\":74,\"b\":31},{\"tag\":\"incompatible\",\"a\":74,\"b\":47},{\"tag\":\"incompatible\",\"a\":74,\"b\":68},{\"tag\":\"incompatible\",\"a\":74,\"b\":73},{\"tag\":\"incompatible\",\"a\":80,\"b\":66},{\"tag\":\"mate\",\"ridge\":67,\"a\":40,\"owners\":[1,6,30,31,47]},{\"tag\":\"three\",\"ridge\":70,\"vertices\":[1,66,74]},{\"tag\":\"mate\",\"ridge\":642,\"a\":42,\"owners\":[72,82]},{\"tag\":\"mate\",\"ridge\":656,\"a\":63,\"owners\":[72,82]},{\"tag\":\"mate\",\"ridge\":386,\"a\":32,\"owners\":[77,81,82]},{\"tag\":\"mate\",\"ridge\":386,\"a\":74,\"owners\":[41,45,77,81,82]},{\"tag\":\"mate\",\"ridge\":328,\"a\":19,\"owners\":[52,61,85,86,88]},{\"tag\":\"mate\",\"ridge\":328,\"a\":39,\"owners\":[85,86,88]},{\"tag\":\"mate\",\"ridge\":328,\"a\":68,\"owners\":[61,88]},{\"tag\":\"mate\",\"ridge\":328,\"a\":80,\"owners\":[52,61,85]},{\"tag\":\"mate\",\"ridge\":400,\"a\":71,\"owners\":[62,89]},{\"tag\":\"mate\",\"ridge\":269,\"a\":52,\"owners\":[24,50]},{\"tag\":\"mate\",\"ridge\":275,\"a\":45,\"owners\":[27,36]},{\"tag\":\"mate\",\"ridge\":280,\"a\":65,\"owners\":[61,62,88,89]},{\"tag\":\"mate\",\"ridge\":280,\"a\":75,\"owners\":[50,61,62,85,89]},{\"tag\":\"mate\",\"ridge\":280,\"a\":79,\"owners\":[50,61,62,84,85,88]},{\"tag\":\"mate\",\"ridge\":92,\"a\":85,\"owners\":[49,83]},{\"tag\":\"mate\",\"ridge\":300,\"a\":86,\"owners\":[67,84]},{\"tag\":\"mate\",\"ridge\":786,\"a\":79,\"owners\":[82]},{\"tag\":\"mate\",\"ridge\":786,\"a\":82,\"owners\":[79]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[37,42,46,63],\"full_literals\":[-48,14,18,20,27]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[32,71,74],\"full_literals\":[-49,11,32,35]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[23,39,40,80],\"full_literals\":[-50,4,15,16,39]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[26,29,30,33],\"full_literals\":[-51,6,8,9,12]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[31,66,68,73],\"full_literals\":[-52,10,29,31,34]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-53,48,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-53,false,49],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-54,50,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-54,false,51],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-55,53,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-55,false,54],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-56,false,52],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-57,false,56],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-58,55,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-58,false,57],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":41,\"full_literals\":[-17,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":81,\"full_literals\":[-40,59]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":62,\"full_literals\":[-26,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":77,\"full_literals\":[-37,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":89,\"full_literals\":[-47,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":24,\"full_literals\":[-5,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":27,\"full_literals\":[-7,61]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":36,\"full_literals\":[-13,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":50,\"full_literals\":[-23,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":61,\"full_literals\":[-25,62]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":49,\"full_literals\":[-22,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":67,\"full_literals\":[-30,63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":83,\"full_literals\":[-42,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":84,\"full_literals\":[-43,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":88,\"full_literals\":[-46,64]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":79,\"full_literals\":[-38,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":82,\"full_literals\":[-41,66]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-60,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0014\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-59,false,67],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-62,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-61,false,68],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-68,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0014\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0015\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-67,false,69],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-64,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-63,false,70],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-66,false,71],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-65,-71,72],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-72,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-70,-72,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-74,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-69,-73,75],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":28,\"owners\":[19,24,36,39,41,50,52,61,62,65,67,68,75,77,79,80,81,84,85,86,88,89]}]}"
  "86 55 0 52 50 0\n87 57 0 52 51 0\n88 53 0 86 46 0\n89 54 0 86 47 0\n90 56 0 87 49 0\n91 48 0 88 42 0\n92 49 0 88 43 0\n93 50 0 89 44 0\n94 51 0 89 45 0\n95 52 0 90 48 0\n96 -74 0 84 82 0\n97 70 69 0 74 73 58 72 61 28 75 71 54 53 70 57 56 55 62 60 76 77 65 66 67 63 64 34 25 30 33 24 31 23 26 32 85 0\n98 41 69 0 92 75 70 55 57 27 74 73 59 72 60 29 71 54 53 56 21 22 38 0\n99 69 0 96 97 81 98 36 69 68 78 79 0\n100 -73 0 99 84 83 0\n101 -72 0 100 80 0\n102 -38 0 101 35 68 69 79 78 0\n103 -41 0 102 36 0\n104 -35 0 95 93 11 12 13 14 15 41 5 6 7 16 18 17 39 0\n105 -11 0 94 1 2 3 4 40 0\n106 32 0 105 92 104 38 0\n107 -14 0 106 8 0\n108 -20 0 106 9 0\n109 -33 0 106 10 0\n110 -18 0 109 103 19 0\n111 -27 0 109 103 20 0\n112 0 111 110 91 108 107 37 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record022.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record022.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record022.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record022.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record022 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record022.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record022.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record022.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record022.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record022 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record022_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record022_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record022_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record022_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record022_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record022_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record022_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record022 Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record022_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record022_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00056.record022_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00056.record022
