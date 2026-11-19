module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow16Part00038Data
public import GraphInputsRow16Part00038Frames
public import GraphInputsRow16Part00038Leaves
public import GraphInputsRow16Part00038Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00038.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record000
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨59, by decide⟩, ⟨63, by decide⟩, ⟨67, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [9837212835078209536, 33776997222055936, (certNat% 2), 56075093016576, 6845104128]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [9835870399450054656, 34902897128898560, (certNat% 3), 550292684800, 3779579609088, 263889300226048, 440401920]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c1 c0
  c2
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record000_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00038.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00038.record005
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record005
def vertexColumn : Fields := ⟨10, (certNat% 4)⟩
def kindColumn : Fields := ⟨3, (certNat% 5)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨39, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨71, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 6), 3458799732552368128, 1056080918478848, (certNat% 7), 159877786773749760, 33688649728, 13194189864960]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record005_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record005_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00038.record005

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00038.record011
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record011
def vertexColumn : Fields := ⟨10, (certNat% 8)⟩
def kindColumn : Fields := ⟨3, (certNat% 9)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨54, by decide⟩, ⟨57, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [1477743636119552, 164383585422278656, 14987979559905787904, (certNat% 10), 27492085661696, 1042284544, 1039386279936]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record011_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record011_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record011_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record011_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record011_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record011_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record011_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record011_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record011_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00038.record011

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00038.record025
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record025
def vertexColumn : Fields := ⟨10, (certNat% 11)⟩
def kindColumn : Fields := ⟨3, (certNat% 12)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [558446353793941504, (certNat% 13), 9253489859362816, 68081942528, 34840841814016, 8725724278030336, 275414777856]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record025_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record025_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record025_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record025_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record025_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record025_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record025_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record025_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record025_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00038.record025

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00038.record032
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record032
def vertexColumn : Fields := ⟨10, (certNat% 14)⟩
def kindColumn : Fields := ⟨3, (certNat% 15)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨58, by decide⟩, ⟨61, by decide⟩, ⟨71, by decide⟩, ⟨74, by decide⟩, ⟨77, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 16), (certNat% 17), (certNat% 18), 4362863883845632, 31526859543937024, 136545600274432]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record032_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record032_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record032_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record032_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record032_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record032_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record032_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record032_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record032_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00038.record032

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00038.record015
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "338cd32cc723c4f23a4ea9635a364da4e33a2e4ba1e4783e8e539654d58d535534cd8b52d8751d0f4d38cd332cccb8ad2b1ae1b46c3b89d2785d1715c3783d0f23c2f07e328a8c6858968384e4c529315152550d134c324c3312c2b21c4705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db69a49a49a6da49a49a69a49249369b492492449249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record015 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record015 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record015.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record015.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record015.data.quota

def groupMembers1 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 11
 (.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 0)]))
 (.leaf ([(facetIndex 1)])))
 (.branch 3
 (.leaf ([(facetIndex 2)]))
 (.branch 4
 (.leaf ([(facetIndex 3)]))
 (.leaf ([(facetIndex 4)])))))
 (.branch 8
 (.branch 6
 (.leaf ([(facetIndex 5)]))
 (.branch 7
 (.leaf ([(facetIndex 6)]))
 (.leaf ([(facetIndex 7)]))))
 (.branch 9
 (.leaf ([(facetIndex 8)]))
 (.branch 10
 (.leaf ([(facetIndex 9)]))
 (.leaf ([(facetIndex 10)]))))))
 (.branch 17
 (.branch 14
 (.branch 12
 (.leaf ([(facetIndex 11)]))
 (.branch 13
 (.leaf ([(facetIndex 12)]))
 (.leaf ([(facetIndex 13)]))))
 (.branch 15
 (.leaf ([(facetIndex 14)]))
 (.branch 16
 (.leaf ([(facetIndex 15)]))
 (.leaf ([(facetIndex 16)])))))
 (.branch 20
 (.branch 18
 (.leaf ([(facetIndex 17)]))
 (.branch 19
 (.leaf ([(facetIndex 18)]))
 (.leaf ([(facetIndex 19)]))))
 (.branch 21
 (.leaf ([(facetIndex 20)]))
 (.branch 22
 (.leaf ([(facetIndex 21)]))
 (.leaf ([(facetIndex 22)])))))))
def groupColors1 : PackedGraphCertificate.Fields :=
  ⟨5, sparse_nat% "5ab49ca307b9ac5a928398a418820"⟩
def grouping1 : FacetSat.Grouping data.count where
  count := 23
  members := fun g => groupMembers1.get g
  color := fun c => groupColors1.get c.val
def groupKind1 : List Nat := List.range grouping1.count

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 25), (facetIndex 29), (facetIndex 40), (facetIndex 50), (facetIndex 63)]))
 (.leaf ([(facetIndex 44), (facetIndex 54), (facetIndex 67)])))
 (.branch 3
 (.leaf ([(facetIndex 26), (facetIndex 46), (facetIndex 48), (facetIndex 51)]))
 (.leaf ([(facetIndex 24), (facetIndex 27), (facetIndex 62), (facetIndex 64)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 31), (facetIndex 60), (facetIndex 66), (facetIndex 68)]))
 (.leaf ([(facetIndex 34), (facetIndex 37), (facetIndex 38), (facetIndex 39)])))
 (.branch 7
 (.leaf ([(facetIndex 28), (facetIndex 41), (facetIndex 42), (facetIndex 43)]))
 (.branch 8
 (.leaf ([(facetIndex 23), (facetIndex 56), (facetIndex 70)]))
 (.leaf ([(facetIndex 30), (facetIndex 52), (facetIndex 55)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "704140303040007810820020201666055500500480632037z17;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 32), (facetIndex 33), (facetIndex 45), (facetIndex 74)]))
 (.branch 2
 (.leaf ([(facetIndex 35), (facetIndex 36), (facetIndex 58), (facetIndex 73)]))
 (.leaf ([(facetIndex 47), (facetIndex 59), (facetIndex 71), (facetIndex 76)]))))
 (.branch 4
 (.leaf ([(facetIndex 49), (facetIndex 57), (facetIndex 72)]))
 (.branch 5
 (.leaf ([(facetIndex 53), (facetIndex 61), (facetIndex 75)]))
 (.leaf ([(facetIndex 65), (facetIndex 69)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "280b4280280204580200184000000012z1a;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 6
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped1_0000 : List Nat := [0, 1, 2, 3, 4]
def grouped1_0001 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
def grouped1_0003 : List Nat := [5]
def grouped1_0004 : List Nat := [5, 6, 7]
def grouped1_0005 : List Nat := [5, 6, 7, 8, 9, 10]
def grouped1_0006 : List Nat := [6]
def grouped1_0007 : List Nat := [6, 7]
def grouped1_0008 : List Nat := [7]
def grouped1_0009 : List Nat := [8]
def grouped1_0010 : List Nat := [8, 9, 10]
def grouped1_0011 : List Nat := [9]
def grouped1_0012 : List Nat := [9, 10]
def grouped1_0013 : List Nat := [10]
def grouped1_0014 : List Nat := [11]
def grouped1_0015 : List Nat := [11, 12, 13]
def grouped1_0016 : List Nat := [11, 12, 13, 14, 15, 16]
def grouped1_0017 : List Nat := [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]
def grouped1_0018 : List Nat := [12]
def grouped1_0019 : List Nat := [12, 13]
def grouped1_0020 : List Nat := [13]
def grouped1_0021 : List Nat := [14]
def grouped1_0022 : List Nat := [14, 15, 16]
def grouped1_0023 : List Nat := [15]
def grouped1_0024 : List Nat := [15, 16]
def grouped1_0025 : List Nat := [16]
def grouped1_0026 : List Nat := [17, 18, 19]
def grouped1_0027 : List Nat := [17, 18, 19, 20, 21, 22]
def grouped1_0028 : List Nat := [20]
def grouped1_0029 : List Nat := [20, 21, 22]
def grouped1_0030 : List Nat := [21]
def grouped1_0031 : List Nat := [21, 22]
def grouped1_0032 : List Nat := [22]
def grouped2_0033 : List Nat := [0]
def grouped2_0034 : List Nat := [0, 1]
def grouped2_0035 : List Nat := [0, 1, 2, 3]
def grouped2_0037 : List Nat := [1]
def grouped2_0038 : List Nat := [2]
def grouped2_0039 : List Nat := [2, 3]
def grouped2_0040 : List Nat := [3]
def grouped2_0041 : List Nat := [4]
def grouped2_0042 : List Nat := [4, 5]
def grouped2_0043 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0044 : List Nat := [5]
def grouped2_0045 : List Nat := [6]
def grouped2_0046 : List Nat := [6, 7, 8]
def grouped2_0047 : List Nat := [7]
def grouped2_0048 : List Nat := [7, 8]
def grouped2_0049 : List Nat := [8]
def grouped3_0050 : List Nat := [0]
def grouped3_0051 : List Nat := [0, 1, 2]
def grouped3_0053 : List Nat := [1]
def grouped3_0054 : List Nat := [1, 2]
def grouped3_0055 : List Nat := [2]
def grouped3_0056 : List Nat := [3]
def grouped3_0057 : List Nat := [3, 4, 5]
def grouped3_0058 : List Nat := [4]
def grouped3_0059 : List Nat := [4, 5]
def grouped3_0060 : List Nat := [5]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record015 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record015_matrix_checked

def leafCount : Nat := 24
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaf0000 : List (Fin data.count) := [(facetIndex 5), (facetIndex 13), (facetIndex 15), (facetIndex 38), (facetIndex 43), (facetIndex 44), (facetIndex 51), (facetIndex 55), (facetIndex 62), (facetIndex 63), (facetIndex 68), (facetIndex 73), (facetIndex 76)]
theorem leaf0000_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0000 = true := by
  decide +kernel
theorem leaf0000_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0000 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0000_counts_checked
def leaf0001 : List (Fin data.count) := [(facetIndex 10), (facetIndex 20), (facetIndex 21), (facetIndex 37), (facetIndex 43), (facetIndex 44), (facetIndex 50), (facetIndex 55), (facetIndex 56), (facetIndex 64), (facetIndex 68), (facetIndex 74), (facetIndex 75)]
theorem leaf0001_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0001 = true := by
  decide +kernel
theorem leaf0001_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0001 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0001_counts_checked
def leaf0002 : List (Fin data.count) := [(facetIndex 13), (facetIndex 14), (facetIndex 15), (facetIndex 37), (facetIndex 43), (facetIndex 44), (facetIndex 51), (facetIndex 55), (facetIndex 62), (facetIndex 63), (facetIndex 68), (facetIndex 73), (facetIndex 76)]
theorem leaf0002_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0002 = true := by
  decide +kernel
theorem leaf0002_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0002 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0002_counts_checked
def leaf0003 : List (Fin data.count) := [(facetIndex 13), (facetIndex 14), (facetIndex 22), (facetIndex 37), (facetIndex 42), (facetIndex 44), (facetIndex 51), (facetIndex 55), (facetIndex 62), (facetIndex 63), (facetIndex 68), (facetIndex 73), (facetIndex 76)]
theorem leaf0003_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0003 = true := by
  decide +kernel
theorem leaf0003_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0003 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0003_counts_checked
def leaf0004 : List (Fin data.count) := [(facetIndex 10), (facetIndex 14), (facetIndex 20), (facetIndex 37), (facetIndex 42), (facetIndex 44), (facetIndex 50), (facetIndex 55), (facetIndex 64), (facetIndex 68), (facetIndex 70), (facetIndex 74), (facetIndex 75)]
theorem leaf0004_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0004 = true := by
  decide +kernel
theorem leaf0004_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0004 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0004_counts_checked
def leaf0005 : List (Fin data.count) := [(facetIndex 13), (facetIndex 14), (facetIndex 20), (facetIndex 37), (facetIndex 42), (facetIndex 44), (facetIndex 51), (facetIndex 55), (facetIndex 64), (facetIndex 68), (facetIndex 70), (facetIndex 74), (facetIndex 75)]
theorem leaf0005_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0005 = true := by
  decide +kernel
theorem leaf0005_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0005 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0005_counts_checked
def leaf0006 : List (Fin data.count) := [(facetIndex 5), (facetIndex 20), (facetIndex 22), (facetIndex 39), (facetIndex 42), (facetIndex 44), (facetIndex 48), (facetIndex 50), (facetIndex 55), (facetIndex 64), (facetIndex 68), (facetIndex 73), (facetIndex 76)]
theorem leaf0006_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0006 = true := by
  decide +kernel
theorem leaf0006_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0006 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0006_counts_checked
def leaf0007 : List (Fin data.count) := [(facetIndex 7), (facetIndex 13), (facetIndex 14), (facetIndex 39), (facetIndex 40), (facetIndex 42), (facetIndex 51), (facetIndex 55), (facetIndex 64), (facetIndex 66), (facetIndex 67), (facetIndex 73), (facetIndex 76)]
theorem leaf0007_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0007 = true := by
  decide +kernel
theorem leaf0007_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0007 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0007_counts_checked
def leaf0008 : List (Fin data.count) := [(facetIndex 7), (facetIndex 20), (facetIndex 21), (facetIndex 38), (facetIndex 40), (facetIndex 43), (facetIndex 51), (facetIndex 52), (facetIndex 54), (facetIndex 64), (facetIndex 68), (facetIndex 73), (facetIndex 76)]
theorem leaf0008_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0008 = true := by
  decide +kernel
theorem leaf0008_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0008 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0008_counts_checked
def leaf0009 : List (Fin data.count) := [(facetIndex 13), (facetIndex 14), (facetIndex 17), (facetIndex 37), (facetIndex 42), (facetIndex 44), (facetIndex 51), (facetIndex 55), (facetIndex 63), (facetIndex 68), (facetIndex 70), (facetIndex 74), (facetIndex 75)]
theorem leaf0009_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0009 = true := by
  decide +kernel
theorem leaf0009_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0009 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0009_counts_checked
def leaf0010 : List (Fin data.count) := [(facetIndex 12), (facetIndex 20), (facetIndex 22), (facetIndex 39), (facetIndex 40), (facetIndex 41), (facetIndex 51), (facetIndex 54), (facetIndex 56), (facetIndex 64), (facetIndex 68), (facetIndex 74), (facetIndex 75)]
theorem leaf0010_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0010 = true := by
  decide +kernel
theorem leaf0010_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0010 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0010_counts_checked
def leaf0011 : List (Fin data.count) := [(facetIndex 13), (facetIndex 15), (facetIndex 19), (facetIndex 38), (facetIndex 40), (facetIndex 41), (facetIndex 51), (facetIndex 55), (facetIndex 64), (facetIndex 67), (facetIndex 70), (facetIndex 74), (facetIndex 75)]
theorem leaf0011_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0011 = true := by
  decide +kernel
theorem leaf0011_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0011 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0011_counts_checked
def leaf0012 : List (Fin data.count) := [(facetIndex 20), (facetIndex 21), (facetIndex 22), (facetIndex 37), (facetIndex 42), (facetIndex 44), (facetIndex 48), (facetIndex 50), (facetIndex 55), (facetIndex 64), (facetIndex 68), (facetIndex 73), (facetIndex 76)]
theorem leaf0012_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0012 = true := by
  decide +kernel
theorem leaf0012_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0012 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0012_counts_checked
def leaf0013 : List (Fin data.count) := [(facetIndex 13), (facetIndex 14), (facetIndex 15), (facetIndex 39), (facetIndex 40), (facetIndex 41), (facetIndex 51), (facetIndex 55), (facetIndex 64), (facetIndex 66), (facetIndex 67), (facetIndex 73), (facetIndex 76)]
theorem leaf0013_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0013 = true := by
  decide +kernel
theorem leaf0013_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0013 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0013_counts_checked
def leaf0014 : List (Fin data.count) := [(facetIndex 20), (facetIndex 21), (facetIndex 22), (facetIndex 38), (facetIndex 40), (facetIndex 41), (facetIndex 51), (facetIndex 52), (facetIndex 54), (facetIndex 64), (facetIndex 68), (facetIndex 73), (facetIndex 76)]
theorem leaf0014_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0014 = true := by
  decide +kernel
theorem leaf0014_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0014 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0014_counts_checked
def leaf0015 : List (Fin data.count) := [(facetIndex 15), (facetIndex 20), (facetIndex 21), (facetIndex 37), (facetIndex 43), (facetIndex 44), (facetIndex 48), (facetIndex 50), (facetIndex 55), (facetIndex 64), (facetIndex 68), (facetIndex 73), (facetIndex 76)]
theorem leaf0015_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0015 = true := by
  decide +kernel
theorem leaf0015_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0015 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0015_counts_checked
def leaf0016 : List (Fin data.count) := [(facetIndex 13), (facetIndex 15), (facetIndex 21), (facetIndex 38), (facetIndex 40), (facetIndex 41), (facetIndex 51), (facetIndex 55), (facetIndex 64), (facetIndex 66), (facetIndex 67), (facetIndex 73), (facetIndex 76)]
theorem leaf0016_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0016 = true := by
  decide +kernel
theorem leaf0016_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0016 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0016_counts_checked
def leaf0017 : List (Fin data.count) := [(facetIndex 14), (facetIndex 20), (facetIndex 22), (facetIndex 39), (facetIndex 40), (facetIndex 41), (facetIndex 51), (facetIndex 52), (facetIndex 54), (facetIndex 64), (facetIndex 68), (facetIndex 73), (facetIndex 76)]
theorem leaf0017_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0017 = true := by
  decide +kernel
theorem leaf0017_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0017 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0017_counts_checked
def leaf0018 : List (Fin data.count) := [(facetIndex 13), (facetIndex 17), (facetIndex 21), (facetIndex 37), (facetIndex 43), (facetIndex 44), (facetIndex 51), (facetIndex 55), (facetIndex 56), (facetIndex 63), (facetIndex 68), (facetIndex 74), (facetIndex 75)]
theorem leaf0018_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0018 = true := by
  decide +kernel
theorem leaf0018_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0018 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0018_counts_checked
def leaf0019 : List (Fin data.count) := [(facetIndex 12), (facetIndex 15), (facetIndex 20), (facetIndex 38), (facetIndex 40), (facetIndex 41), (facetIndex 51), (facetIndex 54), (facetIndex 64), (facetIndex 68), (facetIndex 70), (facetIndex 74), (facetIndex 75)]
theorem leaf0019_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0019 = true := by
  decide +kernel
theorem leaf0019_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0019 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0019_counts_checked
def leaf0020 : List (Fin data.count) := [(facetIndex 13), (facetIndex 19), (facetIndex 22), (facetIndex 39), (facetIndex 40), (facetIndex 41), (facetIndex 51), (facetIndex 55), (facetIndex 56), (facetIndex 64), (facetIndex 67), (facetIndex 74), (facetIndex 75)]
theorem leaf0020_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0020 = true := by
  decide +kernel
theorem leaf0020_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0020 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0020_counts_checked
def leaf0021 : List (Fin data.count) := [(facetIndex 13), (facetIndex 20), (facetIndex 21), (facetIndex 37), (facetIndex 43), (facetIndex 44), (facetIndex 51), (facetIndex 55), (facetIndex 56), (facetIndex 64), (facetIndex 68), (facetIndex 74), (facetIndex 75)]
theorem leaf0021_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0021 = true := by
  decide +kernel
theorem leaf0021_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0021 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0021_counts_checked
def leaf0022 : List (Fin data.count) := [(facetIndex 13), (facetIndex 15), (facetIndex 20), (facetIndex 38), (facetIndex 40), (facetIndex 41), (facetIndex 51), (facetIndex 55), (facetIndex 64), (facetIndex 68), (facetIndex 70), (facetIndex 74), (facetIndex 75)]
theorem leaf0022_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0022 = true := by
  decide +kernel
theorem leaf0022_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0022 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0022_counts_checked
def leaf0023 : List (Fin data.count) := [(facetIndex 13), (facetIndex 20), (facetIndex 22), (facetIndex 39), (facetIndex 40), (facetIndex 41), (facetIndex 51), (facetIndex 55), (facetIndex 56), (facetIndex 64), (facetIndex 68), (facetIndex 74), (facetIndex 75)]
theorem leaf0023_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0023 = true := by
  decide +kernel
theorem leaf0023_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0023 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0023_counts_checked
def leavesTable : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 12
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
 (.branch 10
 (.leaf (leaf0009))
 (.branch 11
 (.leaf (leaf0010))
 (.leaf (leaf0011))))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf (leaf0012))
 (.branch 14
 (.leaf (leaf0013))
 (.leaf (leaf0014))))
 (.branch 16
 (.leaf (leaf0015))
 (.branch 17
 (.leaf (leaf0016))
 (.leaf (leaf0017)))))
 (.branch 21
 (.branch 19
 (.leaf (leaf0018))
 (.branch 20
 (.leaf (leaf0019))
 (.leaf (leaf0020))))
 (.branch 22
 (.leaf (leaf0021))
 (.branch 23
 (.leaf (leaf0022))
 (.leaf (leaf0023)))))))
def leaves (j : Fin leafCount) : List (Fin data.count) := leavesTable.get j.val

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00038.record015" "{\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"group\",\"kind\":1,\"index\":5},{\"tag\":\"group\",\"kind\":1,\"index\":6},{\"tag\":\"group\",\"kind\":1,\"index\":10},{\"tag\":\"group\",\"kind\":1,\"index\":11},{\"tag\":\"group\",\"kind\":1,\"index\":12},{\"tag\":\"group\",\"kind\":1,\"index\":13},{\"tag\":\"group\",\"kind\":1,\"index\":14},{\"tag\":\"group\",\"kind\":1,\"index\":15},{\"tag\":\"group\",\"kind\":1,\"index\":20},{\"tag\":\"group\",\"kind\":1,\"index\":21},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0007\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0004\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0012\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0010\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0005\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0001\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0019\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0019\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0015\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0015\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0024\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0022\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0016\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0016\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0031\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0029\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0029\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0027\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0027\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0017\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":4,\"list_name\":\"grouped1_0017\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":4,\"list_name\":\"groupKind1\"},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0034\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0034\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0039\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0039\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0035\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0035\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0042\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0042\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0048\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0048\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0046\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0046\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0043\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0043\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0054\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0054\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0051\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0051\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0059\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0057\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0057\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00038.record015" 144

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00038.record015" "{\"ridges\":[[1,22],[2,67],[2,70],[5,73],[7,146],[9,73],[10,268],[11,148],[12,276],[14,296],[15,304],[16,74],[16,76],[17,524],[19,530],[19,532],[20,70],[21,552],[22,546],[22,560],[23,19],[26,268],[27,13],[27,524],[30,22],[30,276],[31,532],[32,261],[32,294],[33,549],[34,41],[34,42],[35,19],[36,537],[37,42],[37,67],[38,11],[38,42],[38,289],[39,546],[39,552],[40,193],[40,194],[42,19],[42,50],[42,289],[43,19],[43,546],[43,560],[44,19],[44,67],[44,145],[44,146],[44,193],[44,194],[46,268],[46,276],[48,13],[48,268],[48,296],[50,13],[50,73],[51,69],[51,261],[51,265],[52,276],[52,304],[53,549],[54,21],[54,148],[55,261],[55,276],[56,49],[56,273],[56,304],[57,537],[59,282],[60,524],[60,532],[61,294],[62,552],[63,14],[63,74],[63,76],[64,70],[64,518],[64,522],[64,524],[66,22],[66,560],[67,22],[67,148],[67,196],[68,530],[68,532],[69,282],[70,522],[70,552],[70,560],[72,60],[73,792],[74,804],[75,804],[76,304],[76,792]],\"owners\":[[38,11,[0,5,23,25,27,36,40],[4,26,34,35,39]],[63,14,[0,17,23,24,26,58,59,60,61,62],[16,25]],[42,19,[1,7,23,29,31,36,44],[6,30,34,35,43]],[43,19,[1,7,23,29,30,35,44],[6,31,34,36,42]],[54,21,[1,12,23,28,31,45,46,47,52,53],[11,29]],[67,22,[1,19,23,28,30,58,59,60,65,66],[18,29]],[44,67,[2,5,37],[8,29]],[51,69,[2,13,29,54],[9]],[34,41,[14,48,49],[4,24,37,39,45,56,57]],[34,42,[21,61,62],[4,24,37,38,58,69,70]],[37,42,[21,58,61,62,69,70],[4,24,34,38]],[38,42,[21,58,62,70],[4,24,34,37,61,69]],[5,73,[9,50,51],[37,40]],[9,73,[5,37,40],[50,51]],[50,73,[5,37],[9,40,51]],[16,74,[5,37,40],[63,64]],[63,74,[5,37],[16,40,64]],[56,49,[6,28,41,43,53],[15,34,45,52,57]],[42,50,[22,58,66,70],[6,28,34,41,65,69]],[44,145,[11,55],[7,41,54]],[7,146,[18,67,68],[41,44]],[44,146,[18,68],[7,41,67]],[40,193,[13,54],[8,44,50]],[44,193,[13,50],[8,40,54]],[40,194,[20,67],[8,44,63]],[44,194,[20,63],[8,40,67]],[16,76,[9,50,51],[63,64]],[63,76,[9,51],[16,50,64]],[55,261,[10,26,32,48,51],[12,30,52]],[51,265,[14,35,38,56],[10,26,46]],[10,268,[59,61,71,73,74],[26,46,48,51]],[26,268,[71,73,74],[10,46,48,51,59,61]],[46,268,[61,74],[10,26,48,51,59,71,73]],[48,268,[59,73],[10,26,46,51,61,71,74]],[11,148,[18,67,68],[54,55]],[54,148,[18,68],[11,55,67]],[67,148,[11,55],[18,54,68]],[56,273,[12,30,55],[15,35,42,46]],[12,276,[59,65,71,73,75],[30,46,52,55]],[30,276,[71,73,75],[12,46,52,55,59,65]],[46,276,[65,75],[12,30,52,55,59,71,73]],[52,276,[59,73],[12,30,46,55,65,71,75]],[55,276,[59,65,71,73,75],[12,30,46,52]],[67,196,[13,50],[20,54,63]],[38,289,[15,52],[14,32,42,48]],[42,289,[14,48],[15,32,38,52]],[14,296,[61,69,71,74,76],[38,48,56]],[48,296,[69,76],[14,38,56,61,71,74]],[15,304,[65,69,71,75,76],[42,52,56]],[52,304,[69,76],[15,42,56,65,71,75]],[56,304,[65,75],[15,42,52,69,71,76]],[76,304,[15,42,52,65],[56,69,71,75]],[64,518,[19,31,33,66,68],[17,27,62]],[64,522,[21,36,39,70],[17,27,60]],[70,522,[17,27,64],[21,36,39,60]],[17,524,[47,49,72,73,74],[27,60,62,64]],[27,524,[72,73,74],[17,47,49,60,62,64]],[60,524,[49,74],[17,27,47,62,64,72,73]],[64,524,[47,49,72,73,74],[17,27,60,62]],[19,530,[22,36,43,70],[31,60,68]],[68,530,[22,36,43,70],[19,31,60]],[19,532,[47,53,72,73,75],[31,60,66,68]],[31,532,[72,73,75],[19,47,53,60,66,68]],[60,532,[53,75],[19,31,47,66,68,72,73]],[68,532,[47,53,72,73,75],[19,31,60,66]],[22,546,[21,33,39,62],[43,66]],[39,546,[22,66],[21,33,43,62]],[43,546,[21,62],[22,33,39,66]],[21,552,[49,57,72,74,76],[39,62,70]],[39,552,[72,74,76],[21,49,57,62,70]],[62,552,[57,76],[21,39,49,70,72,74]],[70,552,[49,74],[21,39,57,62,72,76]],[22,560,[53,57,72,75,76],[43,66,70]],[43,560,[72,75,76],[22,53,57,66,70]],[66,560,[57,76],[22,43,53,70,72,75]],[70,560,[53,75],[22,43,57,66,72,76]],[32,294,[61,65],[]],[61,294,[32,65],[]],[33,549,[49,53],[]],[53,549,[33,49],[]],[59,282,[35,69],[]],[69,282,[35,59],[]],[36,537,[47,57],[]],[57,537,[36,47],[]],[72,60,[45,58,71],[]],[73,792,[76],[]],[76,792,[73],[]],[74,804,[75],[]],[75,804,[74],[]]],\"edges\":[[22,[10,12,26,30,32,46,48,51,52,55,59,61,65,71,73,74,75]],[26,[5,9,16,37,40,50,51,63,64]],[29,[17,21,27,36,39,47,49,57,60,62,64,70,72,73,74,76]],[32,[7,11,18,41,44,54,55,67,68]],[34,[19,22,31,36,43,47,53,57,60,66,68,70,72,73,75,76]],[37,[14,15,32,38,42,48,52,56,61,65,69,71,74,75,76]],[38,[21,22,33,39,43,49,53,57,62,66,70,72,74,75,76]]],\"groupings\":[1,2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00038.record015" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00038.record015\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-22,-4],[-24,-7],[-24,-21],[-25,-21],[-25,-24],[-28,-9],[-29,-16],[-35,-22],[-35,-24],[-35,-25],[-37,-19],[-37,-29],[-38,-3],[-38,-22],[-38,-35],[-39,-27],[-39,-28],[-39,-29],[-40,-24],[-40,-28],[-40,-32],[-40,-36],[-41,-25],[-41,-32],[-41,-37],[-42,-23],[-42,-26],[-42,-27],[-42,-38],[-42,-39],[-44,-21],[-44,-28],[-45,-31],[-46,-22],[-46,-36],[-47,-34],[-47,-45],[-48,-3],[-48,-24],[-49,-1],[-49,-21],[-49,-22],[-49,-23],[-49,-24],[-49,-25],[-49,-43],[-49,-44],[-49,-45],[-49,-46],[-49,-47],[-49,-48],[-50,-22],[-50,-40],[-50,-46],[-51,-45],[-51,-46],[-52,-28],[-52,-42],[-53,-2],[-53,-21],[-53,-27],[-53,-29],[-53,-44],[-53,-45],[-53,-50],[-53,-51],[-53,-52],[-54,-32],[-54,-36],[-54,-40],[-54,-44],[-55,-36],[-55,-40],[-56,-41],[-57,-45],[-58,-44],[-58,-54],[-59,-47],[-60,-37],[-60,-46],[-60,-50],[-61,-25],[-62,-21],[-62,-22],[-62,-24],[-62,-57],[-62,-58],[-62,-59],[-62,-61],[-63,-41],[-63,-47],[-64,-22],[-64,-26],[-64,-29],[-64,-41],[-64,-46],[-64,-50],[-64,-60],[-65,-27],[-65,-29],[-66,-2],[-66,-26],[-66,-27],[-66,-28],[-66,-29],[-66,-64],[-66,-65],[-67,-41],[-68,-19],[-68,-21],[-68,-31],[-68,-32],[-68,-37],[-68,-41],[-68,-43],[-68,-44],[-68,-45],[-68,-56],[-68,-57],[-68,-58],[-69,-55],[-70,-21],[-70,-22],[-72,-22],[-72,-26],[-72,-30],[-72,-31],[-72,-46],[-72,-50],[-72,-51],[-72,-63],[-73,-22],[-73,-46],[-73,-50],[-74,-21],[-74,-32],[-74,-33],[-74,-34],[-74,-44],[-74,-54],[-74,-56],[-74,-58],[-74,-67],[-74,-68],[-36,1,4,21,23,25,34,38],[-25,-46,-48],[-61,1,15,21,22,24,56,57,58,59,60],[-40,2,6,21,27,29,34,42],[-41,2,6,21,27,28,33,42],[-21,-40,-42],[-21,-41,-42],[-33,-41,-42],[-52,2,10,21,26,29,43,44,45,50,51],[-65,2,17,21,26,28,56,57,58,63,64],[-2,-64,-65],[-28,-64,-65],[-42,3,4,35],[-3,-35,-42],[-49,3,11,27,52],[-3,-18,-62],[-32,12,46,47],[-32,19,59,60],[-35,19,56,59,60,67,68],[-36,19,56,60,68],[-4,7,48,49],[-7,4,35,38],[-48,4,35],[-14,4,35,38],[-61,4,35],[-54,5,26,39,41,51],[-40,20,56,64,68],[-42,9,53],[-6,16,65,66],[-42,16,66],[-38,11,52],[-42,11,48],[-38,18,65],[-42,18,61],[-14,7,48,49],[-61,7,49],[-53,8,24,30,46,49],[-30,-49,-53],[-49,12,33,36,54],[-8,57,59,69,71,72],[-24,69,71,72],[-44,59,72],[-46,57,71],[-9,16,65,66],[-52,16,66],[-65,9,53],[-54,10,28,53],[-10,57,63,69,71,73],[-28,69,71,73],[-44,63,73],[-50,57,71],[-53,57,63,69,71,73],[-65,11,48],[-36,13,50],[-40,12,46],[-12,59,67,69,72,74],[-46,67,74],[-13,63,67,69,73,74],[-50,67,74],[-54,63,73],[-74,13,40,50,63],[-62,17,29,31,64,66],[-62,19,34,37,68],[-68,15,25,62],[-15,45,47,70,71,72],[-25,70,71,72],[-58,47,72],[-62,45,47,70,71,72],[-17,20,34,41,68],[-66,20,34,41,68],[-17,45,51,70,71,73],[-29,70,71,73],[-58,51,73],[-66,45,51,70,71,73],[-20,19,31,37,60],[-37,20,64],[-41,19,60],[-19,47,55,70,72,74],[-37,70,72,74],[-60,55,74],[-68,47,72],[-20,51,55,70,73,74],[-41,70,73,74],[-64,55,74],[-68,51,73],[-30,59,63],[-59,30,63],[-31,47,51],[-51,31,47],[-57,33,67],[-67,33,57],[-34,45,55],[-55,34,45],[-70,43,56,69],[-71,74],[-74,71],[-72,73],[-73,72],[-4,75],[-5,76],[-8,77],[-9,78],[-10,79],[-11,80],[-12,81],[-13,82],[-18,83],[-19,84],[-76,85],[-85,86],[-75,86],[-77,87],[-87,88],[-86,-88,89],[-89,90],[-80,91],[-79,-80,92],[-91,93],[-78,-92,94],[-82,95],[-95,96],[-81,96],[-93,-96,97],[-94,98],[-84,99],[-99,100],[-83,-99,101],[-100,102],[-101,103],[-103,104],[-97,-103,105],[-98,-102,105],[-105,106],[-90,-104,106],[-106],[-107,23,27,38,48,61],[-108,42,52,65],[-109,24,44,46,49],[-110,22,25,60,62],[-111,29,58,64,66],[-66,111],[-112,32,35,36,37],[-37,112],[-113,26,39,40,41],[-114,21,54,68],[-115,28,50,53],[-116,107,108],[-117,107],[-117,108],[-118,109,110],[-119,109],[-119,110],[-120,116],[-120,117,119],[-121,117],[-120,118],[-121,119],[-122,111,112],[-123,111],[-123,112],[-111,-112,123],[-124,114,115],[-125,114],[-125,115],[-126,113,125],[-127,113],[-126,124],[-127,125],[-128,122],[-128,123,127],[-129,123],[-128,126],[-129,127],[-123,-127,129],[-130,120],[-130,121,129],[-130,128],[130],[-30,131],[-43,131],[-72,131],[-33,132],[-34,132],[-56,132],[-71,132],[-45,133],[-57,133],[-69,133],[-74,133],[-134,47,55,70],[-47,134],[-55,134],[-70,134],[-51,135],[-59,135],[-73,135],[-63,136],[-67,136],[-133,137],[-132,137],[-132,-133,138],[-137,139],[-138,140],[-131,139],[-136,141],[-135,141],[-141,142],[-134,142],[-134,-141,143],[-139,-143,144],[-140,-142,144],[-144],[-4,-11,-13,-36,-41,-42,-49,-53,-60,-61,-66,-71,-74],[-8,-18,-19,-35,-41,-42,-48,-53,-54,-62,-66,-72,-73],[-11,-12,-13,-35,-41,-42,-49,-53,-60,-61,-66,-71,-74],[-11,-12,-20,-35,-40,-42,-49,-53,-60,-61,-66,-71,-74],[-8,-12,-18,-35,-40,-42,-48,-53,-62,-66,-68,-72,-73],[-11,-12,-18,-35,-40,-42,-49,-53,-62,-66,-68,-72,-73],[-4,-18,-20,-37,-40,-42,-46,-48,-53,-62,-66,-71,-74],[-6,-11,-12,-37,-38,-40,-49,-53,-62,-64,-65,-71,-74],[-6,-18,-19,-36,-38,-41,-49,-50,-52,-62,-66,-71,-74],[-11,-12,-15,-35,-40,-42,-49,-53,-61,-66,-68,-72,-73],[-10,-18,-20,-37,-38,-39,-49,-52,-54,-62,-66,-72,-73],[-11,-13,-17,-36,-38,-39,-49,-53,-62,-65,-68,-72,-73],[-18,-19,-20,-35,-40,-42,-46,-48,-53,-62,-66,-71,-74],[-11,-12,-13,-37,-38,-39,-49,-53,-62,-64,-65,-71,-74],[-18,-19,-20,-36,-38,-39,-49,-50,-52,-62,-66,-71,-74],[-13,-18,-19,-35,-41,-42,-46,-48,-53,-62,-66,-71,-74],[-11,-13,-19,-36,-38,-39,-49,-53,-62,-64,-65,-71,-74],[-12,-18,-20,-37,-38,-39,-49,-50,-52,-62,-66,-71,-74],[-11,-15,-19,-35,-41,-42,-49,-53,-54,-61,-66,-72,-73],[-10,-13,-18,-36,-38,-39,-49,-52,-62,-66,-68,-72,-73],[-11,-17,-20,-37,-38,-39,-49,-53,-54,-62,-65,-72,-73],[-11,-18,-19,-35,-41,-42,-49,-53,-54,-62,-66,-72,-73],[-11,-13,-18,-36,-38,-39,-49,-53,-62,-66,-68,-72,-73],[-11,-18,-20,-37,-38,-39,-49,-53,-54,-62,-66,-72,-73],[8,10,24,28,30,44,46,49,50,53,57,59,63,69,71,72,73],[4,7,14,35,38,48,49,61,62],[15,19,25,34,37,45,47,55,58,60,62,68,70,71,72,74],[6,9,16,39,42,52,53,65,66],[17,20,29,34,41,45,51,55,58,64,66,68,70,71,73,74],[12,13,30,36,40,46,50,54,59,63,67,69,72,73,74],[19,20,31,37,41,47,51,55,60,64,68,70,72,73,74]],\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"group\",\"index\":5,\"kind\":1},{\"tag\":\"group\",\"index\":6,\"kind\":1},{\"tag\":\"group\",\"index\":10,\"kind\":1},{\"tag\":\"group\",\"index\":11,\"kind\":1},{\"tag\":\"group\",\"index\":12,\"kind\":1},{\"tag\":\"group\",\"index\":13,\"kind\":1},{\"tag\":\"group\",\"index\":14,\"kind\":1},{\"tag\":\"group\",\"index\":15,\"kind\":1},{\"tag\":\"group\",\"index\":20,\"kind\":1},{\"tag\":\"group\",\"index\":21,\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":24,\"b\":5},{\"tag\":\"incompatible\",\"a\":26,\"b\":9},{\"tag\":\"incompatible\",\"a\":26,\"b\":23},{\"tag\":\"incompatible\",\"a\":27,\"b\":23},{\"tag\":\"incompatible\",\"a\":27,\"b\":26},{\"tag\":\"incompatible\",\"a\":30,\"b\":11},{\"tag\":\"incompatible\",\"a\":31,\"b\":18},{\"tag\":\"incompatible\",\"a\":37,\"b\":24},{\"tag\":\"incompatible\",\"a\":37,\"b\":26},{\"tag\":\"incompatible\",\"a\":37,\"b\":27},{\"tag\":\"incompatible\",\"a\":39,\"b\":21},{\"tag\":\"incompatible\",\"a\":39,\"b\":31},{\"tag\":\"incompatible\",\"a\":40,\"b\":2},{\"tag\":\"incompatible\",\"a\":40,\"b\":24},{\"tag\":\"incompatible\",\"a\":40,\"b\":37},{\"tag\":\"incompatible\",\"a\":41,\"b\":29},{\"tag\":\"incompatible\",\"a\":41,\"b\":30},{\"tag\":\"incompatible\",\"a\":41,\"b\":31},{\"tag\":\"incompatible\",\"a\":42,\"b\":26},{\"tag\":\"incompatible\",\"a\":42,\"b\":30},{\"tag\":\"incompatible\",\"a\":42,\"b\":34},{\"tag\":\"incompatible\",\"a\":42,\"b\":38},{\"tag\":\"incompatible\",\"a\":43,\"b\":27},{\"tag\":\"incompatible\",\"a\":43,\"b\":34},{\"tag\":\"incompatible\",\"a\":43,\"b\":39},{\"tag\":\"incompatible\",\"a\":44,\"b\":25},{\"tag\":\"incompatible\",\"a\":44,\"b\":28},{\"tag\":\"incompatible\",\"a\":44,\"b\":29},{\"tag\":\"incompatible\",\"a\":44,\"b\":40},{\"tag\":\"incompatible\",\"a\":44,\"b\":41},{\"tag\":\"incompatible\",\"a\":46,\"b\":23},{\"tag\":\"incompatible\",\"a\":46,\"b\":30},{\"tag\":\"incompatible\",\"a\":47,\"b\":33},{\"tag\":\"incompatible\",\"a\":48,\"b\":24},{\"tag\":\"incompatible\",\"a\":48,\"b\":38},{\"tag\":\"incompatible\",\"a\":49,\"b\":36},{\"tag\":\"incompatible\",\"a\":49,\"b\":47},{\"tag\":\"incompatible\",\"a\":50,\"b\":2},{\"tag\":\"incompatible\",\"a\":50,\"b\":26},{\"tag\":\"incompatible\",\"a\":51,\"b\":0},{\"tag\":\"incompatible\",\"a\":51,\"b\":23},{\"tag\":\"incompatible\",\"a\":51,\"b\":24},{\"tag\":\"incompatible\",\"a\":51,\"b\":25},{\"tag\":\"incompatible\",\"a\":51,\"b\":26},{\"tag\":\"incompatible\",\"a\":51,\"b\":27},{\"tag\":\"incompatible\",\"a\":51,\"b\":45},{\"tag\":\"incompatible\",\"a\":51,\"b\":46},{\"tag\":\"incompatible\",\"a\":51,\"b\":47},{\"tag\":\"incompatible\",\"a\":51,\"b\":48},{\"tag\":\"incompatible\",\"a\":51,\"b\":49},{\"tag\":\"incompatible\",\"a\":51,\"b\":50},{\"tag\":\"incompatible\",\"a\":52,\"b\":24},{\"tag\":\"incompatible\",\"a\":52,\"b\":42},{\"tag\":\"incompatible\",\"a\":52,\"b\":48},{\"tag\":\"incompatible\",\"a\":53,\"b\":47},{\"tag\":\"incompatible\",\"a\":53,\"b\":48},{\"tag\":\"incompatible\",\"a\":54,\"b\":30},{\"tag\":\"incompatible\",\"a\":54,\"b\":44},{\"tag\":\"incompatible\",\"a\":55,\"b\":1},{\"tag\":\"incompatible\",\"a\":55,\"b\":23},{\"tag\":\"incompatible\",\"a\":55,\"b\":29},{\"tag\":\"incompatible\",\"a\":55,\"b\":31},{\"tag\":\"incompatible\",\"a\":55,\"b\":46},{\"tag\":\"incompatible\",\"a\":55,\"b\":47},{\"tag\":\"incompatible\",\"a\":55,\"b\":52},{\"tag\":\"incompatible\",\"a\":55,\"b\":53},{\"tag\":\"incompatible\",\"a\":55,\"b\":54},{\"tag\":\"incompatible\",\"a\":56,\"b\":34},{\"tag\":\"incompatible\",\"a\":56,\"b\":38},{\"tag\":\"incompatible\",\"a\":56,\"b\":42},{\"tag\":\"incompatible\",\"a\":56,\"b\":46},{\"tag\":\"incompatible\",\"a\":57,\"b\":38},{\"tag\":\"incompatible\",\"a\":57,\"b\":42},{\"tag\":\"incompatible\",\"a\":58,\"b\":43},{\"tag\":\"incompatible\",\"a\":59,\"b\":47},{\"tag\":\"incompatible\",\"a\":60,\"b\":46},{\"tag\":\"incompatible\",\"a\":60,\"b\":56},{\"tag\":\"incompatible\",\"a\":61,\"b\":49},{\"tag\":\"incompatible\",\"a\":62,\"b\":39},{\"tag\":\"incompatible\",\"a\":62,\"b\":48},{\"tag\":\"incompatible\",\"a\":62,\"b\":52},{\"tag\":\"incompatible\",\"a\":63,\"b\":27},{\"tag\":\"incompatible\",\"a\":64,\"b\":23},{\"tag\":\"incompatible\",\"a\":64,\"b\":24},{\"tag\":\"incompatible\",\"a\":64,\"b\":26},{\"tag\":\"incompatible\",\"a\":64,\"b\":59},{\"tag\":\"incompatible\",\"a\":64,\"b\":60},{\"tag\":\"incompatible\",\"a\":64,\"b\":61},{\"tag\":\"incompatible\",\"a\":64,\"b\":63},{\"tag\":\"incompatible\",\"a\":65,\"b\":43},{\"tag\":\"incompatible\",\"a\":65,\"b\":49},{\"tag\":\"incompatible\",\"a\":66,\"b\":24},{\"tag\":\"incompatible\",\"a\":66,\"b\":28},{\"tag\":\"incompatible\",\"a\":66,\"b\":31},{\"tag\":\"incompatible\",\"a\":66,\"b\":43},{\"tag\":\"incompatible\",\"a\":66,\"b\":48},{\"tag\":\"incompatible\",\"a\":66,\"b\":52},{\"tag\":\"incompatible\",\"a\":66,\"b\":62},{\"tag\":\"incompatible\",\"a\":67,\"b\":29},{\"tag\":\"incompatible\",\"a\":67,\"b\":31},{\"tag\":\"incompatible\",\"a\":68,\"b\":1},{\"tag\":\"incompatible\",\"a\":68,\"b\":28},{\"tag\":\"incompatible\",\"a\":68,\"b\":29},{\"tag\":\"incompatible\",\"a\":68,\"b\":30},{\"tag\":\"incompatible\",\"a\":68,\"b\":31},{\"tag\":\"incompatible\",\"a\":68,\"b\":66},{\"tag\":\"incompatible\",\"a\":68,\"b\":67},{\"tag\":\"incompatible\",\"a\":69,\"b\":43},{\"tag\":\"incompatible\",\"a\":70,\"b\":21},{\"tag\":\"incompatible\",\"a\":70,\"b\":23},{\"tag\":\"incompatible\",\"a\":70,\"b\":33},{\"tag\":\"incompatible\",\"a\":70,\"b\":34},{\"tag\":\"incompatible\",\"a\":70,\"b\":39},{\"tag\":\"incompatible\",\"a\":70,\"b\":43},{\"tag\":\"incompatible\",\"a\":70,\"b\":45},{\"tag\":\"incompatible\",\"a\":70,\"b\":46},{\"tag\":\"incompatible\",\"a\":70,\"b\":47},{\"tag\":\"incompatible\",\"a\":70,\"b\":58},{\"tag\":\"incompatible\",\"a\":70,\"b\":59},{\"tag\":\"incompatible\",\"a\":70,\"b\":60},{\"tag\":\"incompatible\",\"a\":71,\"b\":57},{\"tag\":\"incompatible\",\"a\":72,\"b\":23},{\"tag\":\"incompatible\",\"a\":72,\"b\":24},{\"tag\":\"incompatible\",\"a\":74,\"b\":24},{\"tag\":\"incompatible\",\"a\":74,\"b\":28},{\"tag\":\"incompatible\",\"a\":74,\"b\":32},{\"tag\":\"incompatible\",\"a\":74,\"b\":33},{\"tag\":\"incompatible\",\"a\":74,\"b\":48},{\"tag\":\"incompatible\",\"a\":74,\"b\":52},{\"tag\":\"incompatible\",\"a\":74,\"b\":53},{\"tag\":\"incompatible\",\"a\":74,\"b\":65},{\"tag\":\"incompatible\",\"a\":75,\"b\":24},{\"tag\":\"incompatible\",\"a\":75,\"b\":48},{\"tag\":\"incompatible\",\"a\":75,\"b\":52},{\"tag\":\"incompatible\",\"a\":76,\"b\":23},{\"tag\":\"incompatible\",\"a\":76,\"b\":34},{\"tag\":\"incompatible\",\"a\":76,\"b\":35},{\"tag\":\"incompatible\",\"a\":76,\"b\":36},{\"tag\":\"incompatible\",\"a\":76,\"b\":46},{\"tag\":\"incompatible\",\"a\":76,\"b\":56},{\"tag\":\"incompatible\",\"a\":76,\"b\":58},{\"tag\":\"incompatible\",\"a\":76,\"b\":60},{\"tag\":\"incompatible\",\"a\":76,\"b\":69},{\"tag\":\"incompatible\",\"a\":76,\"b\":70},{\"tag\":\"mate\",\"ridge\":11,\"a\":38,\"owners\":[0,5,23,25,27,36,40]},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[27,48,50]},{\"tag\":\"mate\",\"ridge\":14,\"a\":63,\"owners\":[0,17,23,24,26,58,59,60,61,62]},{\"tag\":\"mate\",\"ridge\":19,\"a\":42,\"owners\":[1,7,23,29,31,36,44]},{\"tag\":\"mate\",\"ridge\":19,\"a\":43,\"owners\":[1,7,23,29,30,35,44]},{\"tag\":\"three\",\"ridge\":19,\"vertices\":[23,42,44]},{\"tag\":\"three\",\"ridge\":19,\"vertices\":[23,43,44]},{\"tag\":\"three\",\"ridge\":19,\"vertices\":[35,43,44]},{\"tag\":\"mate\",\"ridge\":21,\"a\":54,\"owners\":[1,12,23,28,31,45,46,47,52,53]},{\"tag\":\"mate\",\"ridge\":22,\"a\":67,\"owners\":[1,19,23,28,30,58,59,60,65,66]},{\"tag\":\"three\",\"ridge\":22,\"vertices\":[1,66,67]},{\"tag\":\"three\",\"ridge\":22,\"vertices\":[30,66,67]},{\"tag\":\"mate\",\"ridge\":67,\"a\":44,\"owners\":[2,5,37]},{\"tag\":\"three\",\"ridge\":67,\"vertices\":[2,37,44]},{\"tag\":\"mate\",\"ridge\":69,\"a\":51,\"owners\":[2,13,29,54]},{\"tag\":\"three\",\"ridge\":70,\"vertices\":[2,20,64]},{\"tag\":\"mate\",\"ridge\":41,\"a\":34,\"owners\":[14,48,49]},{\"tag\":\"mate\",\"ridge\":42,\"a\":34,\"owners\":[21,61,62]},{\"tag\":\"mate\",\"ridge\":42,\"a\":37,\"owners\":[21,58,61,62,69,70]},{\"tag\":\"mate\",\"ridge\":42,\"a\":38,\"owners\":[21,58,62,70]},{\"tag\":\"mate\",\"ridge\":73,\"a\":5,\"owners\":[9,50,51]},{\"tag\":\"mate\",\"ridge\":73,\"a\":9,\"owners\":[5,37,40]},{\"tag\":\"mate\",\"ridge\":73,\"a\":50,\"owners\":[5,37]},{\"tag\":\"mate\",\"ridge\":74,\"a\":16,\"owners\":[5,37,40]},{\"tag\":\"mate\",\"ridge\":74,\"a\":63,\"owners\":[5,37]},{\"tag\":\"mate\",\"ridge\":49,\"a\":56,\"owners\":[6,28,41,43,53]},{\"tag\":\"mate\",\"ridge\":50,\"a\":42,\"owners\":[22,58,66,70]},{\"tag\":\"mate\",\"ridge\":145,\"a\":44,\"owners\":[11,55]},{\"tag\":\"mate\",\"ridge\":146,\"a\":7,\"owners\":[18,67,68]},{\"tag\":\"mate\",\"ridge\":146,\"a\":44,\"owners\":[18,68]},{\"tag\":\"mate\",\"ridge\":193,\"a\":40,\"owners\":[13,54]},{\"tag\":\"mate\",\"ridge\":193,\"a\":44,\"owners\":[13,50]},{\"tag\":\"mate\",\"ridge\":194,\"a\":40,\"owners\":[20,67]},{\"tag\":\"mate\",\"ridge\":194,\"a\":44,\"owners\":[20,63]},{\"tag\":\"mate\",\"ridge\":76,\"a\":16,\"owners\":[9,50,51]},{\"tag\":\"mate\",\"ridge\":76,\"a\":63,\"owners\":[9,51]},{\"tag\":\"mate\",\"ridge\":261,\"a\":55,\"owners\":[10,26,32,48,51]},{\"tag\":\"three\",\"ridge\":261,\"vertices\":[32,51,55]},{\"tag\":\"mate\",\"ridge\":265,\"a\":51,\"owners\":[14,35,38,56]},{\"tag\":\"mate\",\"ridge\":268,\"a\":10,\"owners\":[59,61,71,73,74]},{\"tag\":\"mate\",\"ridge\":268,\"a\":26,\"owners\":[71,73,74]},{\"tag\":\"mate\",\"ridge\":268,\"a\":46,\"owners\":[61,74]},{\"tag\":\"mate\",\"ridge\":268,\"a\":48,\"owners\":[59,73]},{\"tag\":\"mate\",\"ridge\":148,\"a\":11,\"owners\":[18,67,68]},{\"tag\":\"mate\",\"ridge\":148,\"a\":54,\"owners\":[18,68]},{\"tag\":\"mate\",\"ridge\":148,\"a\":67,\"owners\":[11,55]},{\"tag\":\"mate\",\"ridge\":273,\"a\":56,\"owners\":[12,30,55]},{\"tag\":\"mate\",\"ridge\":276,\"a\":12,\"owners\":[59,65,71,73,75]},{\"tag\":\"mate\",\"ridge\":276,\"a\":30,\"owners\":[71,73,75]},{\"tag\":\"mate\",\"ridge\":276,\"a\":46,\"owners\":[65,75]},{\"tag\":\"mate\",\"ridge\":276,\"a\":52,\"owners\":[59,73]},{\"tag\":\"mate\",\"ridge\":276,\"a\":55,\"owners\":[59,65,71,73,75]},{\"tag\":\"mate\",\"ridge\":196,\"a\":67,\"owners\":[13,50]},{\"tag\":\"mate\",\"ridge\":289,\"a\":38,\"owners\":[15,52]},{\"tag\":\"mate\",\"ridge\":289,\"a\":42,\"owners\":[14,48]},{\"tag\":\"mate\",\"ridge\":296,\"a\":14,\"owners\":[61,69,71,74,76]},{\"tag\":\"mate\",\"ridge\":296,\"a\":48,\"owners\":[69,76]},{\"tag\":\"mate\",\"ridge\":304,\"a\":15,\"owners\":[65,69,71,75,76]},{\"tag\":\"mate\",\"ridge\":304,\"a\":52,\"owners\":[69,76]},{\"tag\":\"mate\",\"ridge\":304,\"a\":56,\"owners\":[65,75]},{\"tag\":\"mate\",\"ridge\":304,\"a\":76,\"owners\":[15,42,52,65]},{\"tag\":\"mate\",\"ridge\":518,\"a\":64,\"owners\":[19,31,33,66,68]},{\"tag\":\"mate\",\"ridge\":522,\"a\":64,\"owners\":[21,36,39,70]},{\"tag\":\"mate\",\"ridge\":522,\"a\":70,\"owners\":[17,27,64]},{\"tag\":\"mate\",\"ridge\":524,\"a\":17,\"owners\":[47,49,72,73,74]},{\"tag\":\"mate\",\"ridge\":524,\"a\":27,\"owners\":[72,73,74]},{\"tag\":\"mate\",\"ridge\":524,\"a\":60,\"owners\":[49,74]},{\"tag\":\"mate\",\"ridge\":524,\"a\":64,\"owners\":[47,49,72,73,74]},{\"tag\":\"mate\",\"ridge\":530,\"a\":19,\"owners\":[22,36,43,70]},{\"tag\":\"mate\",\"ridge\":530,\"a\":68,\"owners\":[22,36,43,70]},{\"tag\":\"mate\",\"ridge\":532,\"a\":19,\"owners\":[47,53,72,73,75]},{\"tag\":\"mate\",\"ridge\":532,\"a\":31,\"owners\":[72,73,75]},{\"tag\":\"mate\",\"ridge\":532,\"a\":60,\"owners\":[53,75]},{\"tag\":\"mate\",\"ridge\":532,\"a\":68,\"owners\":[47,53,72,73,75]},{\"tag\":\"mate\",\"ridge\":546,\"a\":22,\"owners\":[21,33,39,62]},{\"tag\":\"mate\",\"ridge\":546,\"a\":39,\"owners\":[22,66]},{\"tag\":\"mate\",\"ridge\":546,\"a\":43,\"owners\":[21,62]},{\"tag\":\"mate\",\"ridge\":552,\"a\":21,\"owners\":[49,57,72,74,76]},{\"tag\":\"mate\",\"ridge\":552,\"a\":39,\"owners\":[72,74,76]},{\"tag\":\"mate\",\"ridge\":552,\"a\":62,\"owners\":[57,76]},{\"tag\":\"mate\",\"ridge\":552,\"a\":70,\"owners\":[49,74]},{\"tag\":\"mate\",\"ridge\":560,\"a\":22,\"owners\":[53,57,72,75,76]},{\"tag\":\"mate\",\"ridge\":560,\"a\":43,\"owners\":[72,75,76]},{\"tag\":\"mate\",\"ridge\":560,\"a\":66,\"owners\":[57,76]},{\"tag\":\"mate\",\"ridge\":560,\"a\":70,\"owners\":[53,75]},{\"tag\":\"mate\",\"ridge\":294,\"a\":32,\"owners\":[61,65]},{\"tag\":\"mate\",\"ridge\":294,\"a\":61,\"owners\":[32,65]},{\"tag\":\"mate\",\"ridge\":549,\"a\":33,\"owners\":[49,53]},{\"tag\":\"mate\",\"ridge\":549,\"a\":53,\"owners\":[33,49]},{\"tag\":\"mate\",\"ridge\":282,\"a\":59,\"owners\":[35,69]},{\"tag\":\"mate\",\"ridge\":282,\"a\":69,\"owners\":[35,59]},{\"tag\":\"mate\",\"ridge\":537,\"a\":36,\"owners\":[47,57]},{\"tag\":\"mate\",\"ridge\":537,\"a\":57,\"owners\":[36,47]},{\"tag\":\"mate\",\"ridge\":60,\"a\":72,\"owners\":[45,58,71]},{\"tag\":\"mate\",\"ridge\":792,\"a\":73,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":792,\"a\":76,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":804,\"a\":74,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":804,\"a\":75,\"owners\":[74]},{\"tag\":\"group_take\",\"kind\":1,\"index\":5,\"member\":5,\"full_literals\":[-4,75]},{\"tag\":\"group_take\",\"kind\":1,\"index\":6,\"member\":6,\"full_literals\":[-5,76]},{\"tag\":\"group_take\",\"kind\":1,\"index\":10,\"member\":10,\"full_literals\":[-8,77]},{\"tag\":\"group_take\",\"kind\":1,\"index\":11,\"member\":11,\"full_literals\":[-9,78]},{\"tag\":\"group_take\",\"kind\":1,\"index\":12,\"member\":12,\"full_literals\":[-10,79]},{\"tag\":\"group_take\",\"kind\":1,\"index\":13,\"member\":13,\"full_literals\":[-11,80]},{\"tag\":\"group_take\",\"kind\":1,\"index\":14,\"member\":14,\"full_literals\":[-12,81]},{\"tag\":\"group_take\",\"kind\":1,\"index\":15,\"member\":15,\"full_literals\":[-13,82]},{\"tag\":\"group_take\",\"kind\":1,\"index\":20,\"member\":20,\"full_literals\":[-18,83]},{\"tag\":\"group_take\",\"kind\":1,\"index\":21,\"member\":21,\"full_literals\":[-19,84]},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped1_0006\",\"right_name\":\"grouped1_0008\",\"joined_name\":\"grouped1_0007\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-76,false,85],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0007\",\"joined_name\":\"grouped1_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-85,86],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0007\",\"joined_name\":\"grouped1_0004\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-75,false,86],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped1_0011\",\"right_name\":\"grouped1_0013\",\"joined_name\":\"grouped1_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-77,87],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped1_0009\",\"right_name\":\"grouped1_0012\",\"joined_name\":\"grouped1_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-87,88],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped1_0004\",\"right_name\":\"grouped1_0010\",\"joined_name\":\"grouped1_0005\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-86,-88,89],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0005\",\"joined_name\":\"grouped1_0001\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-89,90],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12],\"right\":[13],\"left_name\":\"grouped1_0018\",\"right_name\":\"grouped1_0020\",\"joined_name\":\"grouped1_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-80,91],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12],\"right\":[13],\"left_name\":\"grouped1_0018\",\"right_name\":\"grouped1_0020\",\"joined_name\":\"grouped1_0019\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-79,-80,92],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[11],\"right\":[12,13],\"left_name\":\"grouped1_0014\",\"right_name\":\"grouped1_0019\",\"joined_name\":\"grouped1_0015\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-91,93],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[11],\"right\":[12,13],\"left_name\":\"grouped1_0014\",\"right_name\":\"grouped1_0019\",\"joined_name\":\"grouped1_0015\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-78,-92,94],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[15],\"right\":[16],\"left_name\":\"grouped1_0023\",\"right_name\":\"grouped1_0025\",\"joined_name\":\"grouped1_0024\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-82,false,95],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[14],\"right\":[15,16],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0024\",\"joined_name\":\"grouped1_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-95,96],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[14],\"right\":[15,16],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0024\",\"joined_name\":\"grouped1_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-81,false,96],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[11,12,13],\"right\":[14,15,16],\"left_name\":\"grouped1_0015\",\"right_name\":\"grouped1_0022\",\"joined_name\":\"grouped1_0016\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-93,-96,97],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[11,12,13],\"right\":[14,15,16],\"left_name\":\"grouped1_0015\",\"right_name\":\"grouped1_0022\",\"joined_name\":\"grouped1_0016\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-94,false,98],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[21],\"right\":[22],\"left_name\":\"grouped1_0030\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0031\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-84,false,99],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[20],\"right\":[21,22],\"left_name\":\"grouped1_0028\",\"right_name\":\"grouped1_0031\",\"joined_name\":\"grouped1_0029\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-99,100],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[20],\"right\":[21,22],\"left_name\":\"grouped1_0028\",\"right_name\":\"grouped1_0031\",\"joined_name\":\"grouped1_0029\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-83,-99,101],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17,18,19],\"right\":[20,21,22],\"left_name\":\"grouped1_0026\",\"right_name\":\"grouped1_0029\",\"joined_name\":\"grouped1_0027\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-100,102],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17,18,19],\"right\":[20,21,22],\"left_name\":\"grouped1_0026\",\"right_name\":\"grouped1_0029\",\"joined_name\":\"grouped1_0027\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-101,103],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[11,12,13,14,15,16],\"right\":[17,18,19,20,21,22],\"left_name\":\"grouped1_0016\",\"right_name\":\"grouped1_0027\",\"joined_name\":\"grouped1_0017\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-103,104],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[11,12,13,14,15,16],\"right\":[17,18,19,20,21,22],\"left_name\":\"grouped1_0016\",\"right_name\":\"grouped1_0027\",\"joined_name\":\"grouped1_0017\",\"a\":2,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-97,-103,105],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[11,12,13,14,15,16],\"right\":[17,18,19,20,21,22],\"left_name\":\"grouped1_0016\",\"right_name\":\"grouped1_0027\",\"joined_name\":\"grouped1_0017\",\"a\":3,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-98,-102,105],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9,10],\"right\":[11,12,13,14,15,16,17,18,19,20,21,22],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0017\",\"joined_name\":\"groupKind1\",\"a\":0,\"b\":4,\"direction\":\"forward\",\"full_literals\":[false,-105,106],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9,10],\"right\":[11,12,13,14,15,16,17,18,19,20,21,22],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0017\",\"joined_name\":\"groupKind1\",\"a\":2,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-90,-104,106],\"grouped\":true,\"kind\":1},{\"tag\":\"quota_upper\",\"kind\":1,\"quota\":3,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[25,29,40,50,63],\"full_literals\":[-107,23,27,38,48,61]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[44,54,67],\"full_literals\":[-108,42,52,65]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[26,46,48,51],\"full_literals\":[-109,24,44,46,49]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[24,27,62,64],\"full_literals\":[-110,22,25,60,62]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[31,60,66,68],\"full_literals\":[-111,29,58,64,66]},{\"tag\":\"group_take\",\"kind\":2,\"index\":4,\"member\":68,\"full_literals\":[-66,111]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[34,37,38,39],\"full_literals\":[-112,32,35,36,37]},{\"tag\":\"group_take\",\"kind\":2,\"index\":5,\"member\":39,\"full_literals\":[-37,112]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[28,41,42,43],\"full_literals\":[-113,26,39,40,41]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[23,56,70],\"full_literals\":[-114,21,54,68]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[30,52,55],\"full_literals\":[-115,28,50,53]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0033\",\"right_name\":\"grouped2_0037\",\"joined_name\":\"grouped2_0034\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-116,107,108],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0033\",\"right_name\":\"grouped2_0037\",\"joined_name\":\"grouped2_0034\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-117,107,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0033\",\"right_name\":\"grouped2_0037\",\"joined_name\":\"grouped2_0034\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-117,false,108],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0038\",\"right_name\":\"grouped2_0040\",\"joined_name\":\"grouped2_0039\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-118,109,110],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0038\",\"right_name\":\"grouped2_0040\",\"joined_name\":\"grouped2_0039\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-119,109,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0038\",\"right_name\":\"grouped2_0040\",\"joined_name\":\"grouped2_0039\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-119,false,110],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0034\",\"right_name\":\"grouped2_0039\",\"joined_name\":\"grouped2_0035\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-120,116,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0034\",\"right_name\":\"grouped2_0039\",\"joined_name\":\"grouped2_0035\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-120,117,119],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0034\",\"right_name\":\"grouped2_0039\",\"joined_name\":\"grouped2_0035\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-121,117,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0034\",\"right_name\":\"grouped2_0039\",\"joined_name\":\"grouped2_0035\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-120,false,118],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0034\",\"right_name\":\"grouped2_0039\",\"joined_name\":\"grouped2_0035\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-121,false,119],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0041\",\"right_name\":\"grouped2_0044\",\"joined_name\":\"grouped2_0042\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-122,111,112],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0041\",\"right_name\":\"grouped2_0044\",\"joined_name\":\"grouped2_0042\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-123,111,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0041\",\"right_name\":\"grouped2_0044\",\"joined_name\":\"grouped2_0042\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-123,false,112],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0041\",\"right_name\":\"grouped2_0044\",\"joined_name\":\"grouped2_0042\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-111,-112,123],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0047\",\"right_name\":\"grouped2_0049\",\"joined_name\":\"grouped2_0048\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-124,114,115],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0047\",\"right_name\":\"grouped2_0049\",\"joined_name\":\"grouped2_0048\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-125,114,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0047\",\"right_name\":\"grouped2_0049\",\"joined_name\":\"grouped2_0048\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-125,false,115],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0045\",\"right_name\":\"grouped2_0048\",\"joined_name\":\"grouped2_0046\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-126,113,125],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0045\",\"right_name\":\"grouped2_0048\",\"joined_name\":\"grouped2_0046\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-127,113,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0045\",\"right_name\":\"grouped2_0048\",\"joined_name\":\"grouped2_0046\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-126,false,124],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0045\",\"right_name\":\"grouped2_0048\",\"joined_name\":\"grouped2_0046\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-127,false,125],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0042\",\"right_name\":\"grouped2_0046\",\"joined_name\":\"grouped2_0043\",\"a\":0,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-128,122,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0042\",\"right_name\":\"grouped2_0046\",\"joined_name\":\"grouped2_0043\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-128,123,127],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0042\",\"right_name\":\"grouped2_0046\",\"joined_name\":\"grouped2_0043\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-129,123,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0042\",\"right_name\":\"grouped2_0046\",\"joined_name\":\"grouped2_0043\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-128,false,126],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0042\",\"right_name\":\"grouped2_0046\",\"joined_name\":\"grouped2_0043\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-129,false,127],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0042\",\"right_name\":\"grouped2_0046\",\"joined_name\":\"grouped2_0043\",\"a\":2,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-123,-127,129],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0035\",\"right_name\":\"grouped2_0043\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-130,120,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0035\",\"right_name\":\"grouped2_0043\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-130,121,129],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0035\",\"right_name\":\"grouped2_0043\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-130,false,128],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":32,\"full_literals\":[-30,131]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":45,\"full_literals\":[-43,131]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":74,\"full_literals\":[-72,131]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":35,\"full_literals\":[-33,132]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":36,\"full_literals\":[-34,132]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":58,\"full_literals\":[-56,132]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":73,\"full_literals\":[-71,132]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":47,\"full_literals\":[-45,133]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":59,\"full_literals\":[-57,133]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":71,\"full_literals\":[-69,133]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":76,\"full_literals\":[-74,133]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[49,57,72],\"full_literals\":[-134,47,55,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":49,\"full_literals\":[-47,134]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":57,\"full_literals\":[-55,134]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":72,\"full_literals\":[-70,134]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":53,\"full_literals\":[-51,135]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":61,\"full_literals\":[-59,135]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":75,\"full_literals\":[-73,135]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":65,\"full_literals\":[-63,136]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":69,\"full_literals\":[-67,136]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0053\",\"right_name\":\"grouped3_0055\",\"joined_name\":\"grouped3_0054\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-133,137],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0053\",\"right_name\":\"grouped3_0055\",\"joined_name\":\"grouped3_0054\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-132,false,137],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0053\",\"right_name\":\"grouped3_0055\",\"joined_name\":\"grouped3_0054\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-132,-133,138],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0050\",\"right_name\":\"grouped3_0054\",\"joined_name\":\"grouped3_0051\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-137,139],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0050\",\"right_name\":\"grouped3_0054\",\"joined_name\":\"grouped3_0051\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-138,140],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0050\",\"right_name\":\"grouped3_0054\",\"joined_name\":\"grouped3_0051\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-131,false,139],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0058\",\"right_name\":\"grouped3_0060\",\"joined_name\":\"grouped3_0059\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-136,141],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0058\",\"right_name\":\"grouped3_0060\",\"joined_name\":\"grouped3_0059\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-135,false,141],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0056\",\"right_name\":\"grouped3_0059\",\"joined_name\":\"grouped3_0057\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-141,142],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0056\",\"right_name\":\"grouped3_0059\",\"joined_name\":\"grouped3_0057\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-134,false,142],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0056\",\"right_name\":\"grouped3_0059\",\"joined_name\":\"grouped3_0057\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-134,-141,143],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0051\",\"right_name\":\"grouped3_0057\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-139,-143,144],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0051\",\"right_name\":\"grouped3_0057\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-140,-142,144],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"block\",\"leaf\":0,\"vertices\":[5,13,15,38,43,44,51,55,62,63,68,73,76]},{\"tag\":\"block\",\"leaf\":1,\"vertices\":[10,20,21,37,43,44,50,55,56,64,68,74,75]},{\"tag\":\"block\",\"leaf\":2,\"vertices\":[13,14,15,37,43,44,51,55,62,63,68,73,76]},{\"tag\":\"block\",\"leaf\":3,\"vertices\":[13,14,22,37,42,44,51,55,62,63,68,73,76]},{\"tag\":\"block\",\"leaf\":4,\"vertices\":[10,14,20,37,42,44,50,55,64,68,70,74,75]},{\"tag\":\"block\",\"leaf\":5,\"vertices\":[13,14,20,37,42,44,51,55,64,68,70,74,75]},{\"tag\":\"block\",\"leaf\":6,\"vertices\":[5,20,22,39,42,44,48,50,55,64,68,73,76]},{\"tag\":\"block\",\"leaf\":7,\"vertices\":[7,13,14,39,40,42,51,55,64,66,67,73,76]},{\"tag\":\"block\",\"leaf\":8,\"vertices\":[7,20,21,38,40,43,51,52,54,64,68,73,76]},{\"tag\":\"block\",\"leaf\":9,\"vertices\":[13,14,17,37,42,44,51,55,63,68,70,74,75]},{\"tag\":\"block\",\"leaf\":10,\"vertices\":[12,20,22,39,40,41,51,54,56,64,68,74,75]},{\"tag\":\"block\",\"leaf\":11,\"vertices\":[13,15,19,38,40,41,51,55,64,67,70,74,75]},{\"tag\":\"block\",\"leaf\":12,\"vertices\":[20,21,22,37,42,44,48,50,55,64,68,73,76]},{\"tag\":\"block\",\"leaf\":13,\"vertices\":[13,14,15,39,40,41,51,55,64,66,67,73,76]},{\"tag\":\"block\",\"leaf\":14,\"vertices\":[20,21,22,38,40,41,51,52,54,64,68,73,76]},{\"tag\":\"block\",\"leaf\":15,\"vertices\":[15,20,21,37,43,44,48,50,55,64,68,73,76]},{\"tag\":\"block\",\"leaf\":16,\"vertices\":[13,15,21,38,40,41,51,55,64,66,67,73,76]},{\"tag\":\"block\",\"leaf\":17,\"vertices\":[14,20,22,39,40,41,51,52,54,64,68,73,76]},{\"tag\":\"block\",\"leaf\":18,\"vertices\":[13,17,21,37,43,44,51,55,56,63,68,74,75]},{\"tag\":\"block\",\"leaf\":19,\"vertices\":[12,15,20,38,40,41,51,54,64,68,70,74,75]},{\"tag\":\"block\",\"leaf\":20,\"vertices\":[13,19,22,39,40,41,51,55,56,64,67,74,75]},{\"tag\":\"block\",\"leaf\":21,\"vertices\":[13,20,21,37,43,44,51,55,56,64,68,74,75]},{\"tag\":\"block\",\"leaf\":22,\"vertices\":[13,15,20,38,40,41,51,55,64,68,70,74,75]},{\"tag\":\"block\",\"leaf\":23,\"vertices\":[13,20,22,39,40,41,51,55,56,64,68,74,75]},{\"tag\":\"edge\",\"edge\":22,\"owners\":[10,12,26,30,32,46,48,51,52,55,59,61,65,71,73,74,75]},{\"tag\":\"edge\",\"edge\":26,\"owners\":[5,9,16,37,40,50,51,63,64]},{\"tag\":\"edge\",\"edge\":29,\"owners\":[17,21,27,36,39,47,49,57,60,62,64,70,72,73,74,76]},{\"tag\":\"edge\",\"edge\":32,\"owners\":[7,11,18,41,44,54,55,67,68]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[19,22,31,36,43,47,53,57,60,66,68,70,72,73,75,76]},{\"tag\":\"edge\",\"edge\":37,\"owners\":[14,15,32,38,42,48,52,56,61,65,69,71,74,75,76]},{\"tag\":\"edge\",\"edge\":38,\"owners\":[21,22,33,39,43,49,53,57,62,66,70,72,74,75,76]}]}"
  "388 -105 0 279 277 0\n389 120 0 322 319 0\n390 128 0 322 321 0\n391 116 0 389 297 0\n392 118 0 389 300 0\n393 122 0 390 313 0\n394 126 0 390 316 0\n395 124 0 394 311 0\n396 47 139 0 346 343 333 348 325 324 344 328 332 238 223 329 210 327 330 237 224 225 211 222 212 209 383 0\n397 139 0 346 348 343 344 323 325 331 332 333 326 329 242 235 185 193 201 203 396 50 78 91 186 184 196 192 381 0\n398 -143 0 397 356 354 0\n399 55 70 74 -134 0 398 353 350 340 227 239 216 338 217 229 228 334 226 36 37 213 214 385 0\n400 -55 74 141 0 349 342 203 201 350 340 241 341 339 230 204 72 73 121 202 200 386 0\n401 -24 -110 22 60 0 5 85 283 0\n402 66 -111 58 64 0 284 7 18 62 100 173 188 174 189 384 0\n403 74 -134 0 398 395 390 322 353 350 340 338 217 229 349 341 204 194 342 201 203 400 228 224 399 122 123 289 306 307 312 317 314 320 303 299 301 292 293 295 296 401 282 43 45 51 283 89 402 103 104 107 280 290 29 67 281 0\n404 -134 0 356 352 355 347 403 240 333 329 345 0\n405 -47 0 404 335 0\n406 -55 0 404 336 0\n407 -70 0 404 337 0\n408 36 40 -49 -53 -66 -74 0 390 356 394 322 107 144 140 135 289 307 312 317 320 299 293 67 281 30 102 309 288 333 240 329 345 347 355 351 349 341 65 205 45 301 296 42 29 292 26 103 51 280 89 283 79 176 314 304 137 136 183 286 359 0\n409 40 -49 -53 -66 -74 0 394 356 322 45 144 140 135 289 307 312 317 320 301 296 42 107 299 293 67 281 29 292 26 103 51 280 89 283 176 40 30 65 102 333 240 329 345 347 355 351 349 341 309 138 205 288 408 145 357 0\n410 -49 46 -53 -66 -74 0 390 322 107 144 140 135 289 307 312 317 320 299 293 67 281 29 26 106 103 301 296 292 314 304 240 141 136 42 45 51 176 280 89 283 79 409 22 171 199 286 360 0\n411 46 -53 -66 -74 0 322 107 144 140 135 289 307 312 317 320 299 293 67 281 29 301 295 139 410 282 2 9 39 85 165 180 179 382 0\n412 35 61 -53 -66 -74 0 394 390 322 411 80 144 140 135 289 307 312 317 320 301 296 34 107 299 293 67 281 29 292 26 103 280 146 283 38 178 35 30 106 102 314 304 309 240 136 157 286 25 220 288 363 0\n413 -40 61 -53 -66 -74 0 322 356 144 143 411 80 333 240 329 345 347 355 351 350 339 141 412 163 140 135 289 307 312 317 320 301 296 34 107 299 293 67 281 29 292 26 103 280 146 283 178 106 171 369 0\n414 61 -53 -66 -74 0 394 356 322 411 80 34 107 144 140 135 289 307 312 317 320 299 293 67 281 30 29 26 65 103 102 333 240 329 345 347 355 351 350 339 349 341 301 296 292 309 143 141 280 178 146 283 412 163 413 205 288 372 0\n415 -53 -66 -74 0 322 144 140 135 289 307 312 317 320 301 296 411 34 80 414 82 89 283 0\n416 -41 -19 -66 -74 0 322 395 390 144 140 135 289 307 312 314 304 136 139 104 306 415 290 54 317 320 301 295 52 296 81 401 282 51 299 292 43 103 45 283 89 280 15 11 286 107 293 29 281 177 101 240 137 149 365 0\n417 -19 -66 -74 0 394 390 395 322 107 144 140 135 289 307 312 317 320 299 293 139 104 306 415 290 54 301 295 52 296 81 401 282 51 292 43 103 45 283 89 280 29 281 177 15 53 102 314 304 309 240 138 136 11 286 416 288 214 371 0\n418 -66 -74 0 395 394 322 144 140 135 289 307 312 317 320 301 296 295 299 293 292 309 306 240 141 139 138 137 102 103 104 106 107 415 290 52 53 54 81 401 282 43 45 51 283 89 280 29 177 281 417 164 207 221 183 220 288 374 0\n419 -52 -74 0 395 390 144 140 135 289 307 312 314 303 142 418 402 97 306 57 67 290 0\n420 40 19 -65 -74 0 394 356 395 322 390 140 137 139 144 135 289 307 312 314 303 142 418 402 96 317 320 301 295 92 296 98 401 282 141 164 183 45 283 138 207 97 306 156 290 51 299 292 43 89 99 280 197 95 93 333 240 329 345 347 355 351 349 341 309 205 288 370 0\n421 19 42 -74 0 322 395 390 144 140 135 289 307 312 314 303 142 418 402 97 306 419 317 320 299 293 281 156 290 139 96 301 295 92 296 98 401 282 51 292 43 45 283 89 99 280 155 197 94 240 141 138 137 164 207 183 420 148 364 0\n422 42 -74 0 395 394 322 390 419 144 140 135 289 307 312 314 303 142 418 402 98 317 320 301 296 92 139 96 295 401 282 45 283 89 51 43 97 95 93 299 293 292 304 309 306 240 136 281 99 197 156 280 290 15 421 11 286 22 198 288 373 0\n423 -74 0 390 322 135 139 140 142 144 289 307 312 317 314 320 303 299 301 292 295 296 418 402 92 96 98 401 282 43 45 51 283 89 422 28 29 280 0\n424 -71 0 423 239 0\n425 -64 0 423 406 228 0\n426 -60 0 423 406 224 0\n427 -49 -19 -62 -53 -42 0 424 407 388 322 425 405 89 178 251 252 269 271 273 275 109 11 160 64 212 241 86 187 87 65 60 58 30 29 28 27 26 51 159 280 248 292 260 299 262 320 267 315 317 265 266 303 304 310 312 264 249 402 307 250 161 199 289 198 288 286 378 0\n428 -19 -62 -53 -42 0 424 407 405 279 389 322 425 89 178 251 64 212 241 126 86 187 87 85 66 63 60 30 29 28 27 26 109 252 269 271 273 274 278 259 427 282 181 295 245 301 298 256 320 292 257 315 317 280 258 303 312 254 255 402 307 253 243 289 244 167 170 358 0\n429 49 -62 -53 -42 0 424 407 405 426 389 322 425 428 221 88 162 64 212 241 126 89 178 86 187 87 85 63 60 30 29 28 27 26 282 181 295 301 298 320 292 315 317 280 303 304 310 312 402 288 307 22 70 199 289 361 113 286 0\n430 -62 -53 -42 0 405 407 424 426 322 425 64 60 58 30 29 28 27 26 86 87 88 89 212 187 178 241 160 428 162 221 429 51 159 280 292 299 320 315 317 303 304 310 312 402 288 307 22 70 199 289 362 113 286 0\n431 -40 -49 -53 -42 0 389 426 322 405 425 42 430 45 283 296 301 320 317 312 307 315 304 303 51 29 26 28 298 292 280 176 49 66 60 21 22 70 199 289 113 120 208 225 229 286 402 366 0\n432 -49 -53 -42 0 389 322 407 423 426 425 430 60 30 29 28 27 26 40 42 44 45 51 182 283 176 296 301 298 320 292 315 317 280 303 304 310 312 307 431 288 24 25 74 90 108 114 152 227 221 231 289 234 242 69 77 147 286 402 375 0\n433 -41 -53 -42 0 407 423 426 392 389 432 430 63 29 28 26 23 108 227 201 132 283 296 294 298 282 292 2 39 280 180 0\n434 -46 41 51 0 423 407 425 426 406 405 232 128 133 225 222 223 226 387 0\n435 73 41 51 45 29 0 423 424 407 425 406 236 226 218 215 229 217 385 0\n436 -127 68 -53 -42 0 433 60 30 27 310 312 288 307 70 289 0\n437 -119 22 46 49 44 0 426 295 296 282 401 0\n438 -53 -42 0 322 392 426 30 27 62 63 64 66 430 432 433 434 435 132 437 301 320 315 317 304 310 436 288 112 113 19 22 286 282 10 294 283 0\n439 -73 41 -42 0 395 394 390 322 426 438 172 6 30 29 28 27 26 132 133 134 290 308 306 312 309 317 314 288 320 304 19 21 22 70 150 299 301 289 292 295 296 113 116 286 282 10 51 283 280 89 0\n440 45 72 0 423 424 407 426 406 405 210 223 222 211 225 236 209 212 383 0\n441 41 -42 0 405 406 426 425 407 423 439 241 225 222 223 440 33 55 219 387 0\n442 -42 0 407 426 423 395 390 388 322 28 58 438 172 6 246 441 24 25 108 114 151 227 221 201 203 132 252 290 269 308 306 270 312 289 272 317 314 69 71 191 276 320 304 286 247 268 301 158 263 437 159 261 248 0\n443 -123 -107 53 -62 -49 32 37 68 50 0 425 395 89 87 51 43 41 303 304 402 103 104 280 290 15 306 286 289 69 0\n444 -117 53 -62 -49 32 37 68 50 0 390 442 292 293 443 314 312 308 290 6 57 190 281 0\n445 53 -62 -49 32 37 68 50 0 322 425 87 444 299 320 315 317 303 312 402 308 104 290 0\n446 -123 52 27 61 58 -49 32 37 68 0 425 442 391 322 51 43 41 303 304 402 107 281 293 291 299 280 320 15 317 286 312 69 307 289 0\n447 -62 -49 32 37 68 50 0 390 322 442 425 393 51 43 41 87 89 445 61 67 446 314 315 312 320 307 299 289 292 293 69 280 281 15 107 286 402 302 0\n448 -44 53 21 50 68 0 395 32 71 290 289 306 0\n449 53 58 21 22 50 46 49 68 0 322 425 448 437 301 320 315 317 303 312 402 308 104 290 0\n450 58 21 68 22 50 46 49 0 425 442 322 389 449 63 67 437 301 298 320 293 315 281 303 107 402 0\n451 22 21 68 49 50 46 0 322 450 76 77 437 289 301 307 320 312 317 0\n452 -22 49 0 1 8 14 84 168 169 167 166 382 0\n453 -21 46 49 0 426 392 452 3 4 31 83 282 283 294 0\n454 -50 0 424 129 195 440 75 0\n455 46 49 68 0 454 452 453 451 0\n456 -46 0 407 423 56 133 434 227 0\n457 119 68 0 456 389 322 425 454 442 455 41 301 298 320 293 315 317 303 312 307 308 289 77 402 104 107 290 281 67 0\n458 -129 68 0 456 426 454 442 425 391 455 42 45 457 296 283 89 87 48 440 241 125 51 43 41 315 317 303 310 312 402 307 308 103 104 107 289 290 68 70 67 447 281 25 220 291 288 280 177 175 380 0\n459 -127 68 0 456 426 322 454 425 442 458 320 299 293 292 455 42 45 457 296 283 89 48 440 241 127 125 51 43 41 310 312 318 307 308 289 68 70 447 12 25 220 287 288 305 16 17 285 280 290 206 13 67 159 281 377 0\n460 68 0 456 426 322 390 442 395 394 454 425 455 41 42 43 45 46 47 48 51 440 125 130 241 457 296 283 87 89 458 320 299 292 293 459 314 303 402 101 103 104 105 107 280 281 177 67 153 290 308 306 309 289 68 70 447 25 220 288 367 0\n461 -21 0 460 110 0\n462 -31 0 460 111 0\n463 -32 0 460 112 0\n464 -37 0 460 113 0\n465 -41 0 460 114 0\n466 -43 0 460 115 0\n467 -44 0 460 116 0\n468 -45 0 460 117 0\n469 -56 0 460 118 0\n470 -57 0 460 119 0\n471 -58 0 460 120 0\n472 72 0 460 405 225 0\n473 -51 0 462 405 233 0\n474 -22 0 472 124 0\n475 -26 0 472 125 0\n476 -63 0 472 131 0\n477 73 0 472 241 0\n478 -123 -121 0 456 474 426 425 471 442 473 468 466 461 467 463 464 454 477 472 460 394 475 465 301 296 437 45 283 89 51 43 299 293 292 303 304 402 101 103 104 105 107 280 281 177 15 67 153 286 290 22 198 308 376 309 288 0\n479 -28 -113 0 475 465 17 20 288 0\n480 -121 0 467 456 426 474 390 442 476 470 469 461 425 471 393 463 464 454 475 465 477 472 460 299 301 292 293 296 437 43 45 51 283 89 478 314 310 312 308 479 290 59 61 67 280 281 175 15 107 154 402 302 286 22 198 288 368 0\n481 129 0 480 322 320 0\n482 123 0 481 315 0\n483 127 0 481 317 0\n484 111 0 482 303 0\n485 112 0 482 304 0\n486 113 0 483 310 0\n487 125 0 483 312 0\n488 66 0 484 471 425 402 0\n489 -28 0 486 479 0\n490 115 0 487 308 0\n491 -27 0 488 103 0\n492 -65 0 488 107 0\n493 53 0 489 454 490 290 0\n494 -52 0 493 67 0\n495 -108 0 494 492 442 281 0\n496 -117 0 495 293 0\n497 107 0 495 391 291 0\n498 119 0 496 389 298 0\n499 110 0 498 296 0\n500 49 0 498 456 474 467 437 0\n501 -23 0 500 43 0\n502 -25 0 500 45 0\n503 -48 0 500 51 0\n504 62 0 502 499 474 426 283 0\n505 -61 0 504 89 0\n506 38 0 505 503 501 491 497 280 0\n507 -35 0 506 15 0\n508 18 0 506 492 177 0\n509 11 0 506 494 175 0\n510 36 0 507 464 463 485 286 0\n511 -40 0 510 22 0\n512 13 0 510 454 198 0\n513 39 0 511 465 475 486 288 0\n514 0 512 513 508 509 506 510 500 493 504 488 460 472 477 379 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record015.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record015.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record015.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record015.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record015 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeafTable : ConcreteGrowth.Table (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record015.l) :=
(.branch 12
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
 (.leaf (⟨0, by decide⟩))
 (.branch 8
 (.leaf (⟨0, by decide⟩))
 (.leaf (⟨0, by decide⟩))))
 (.branch 10
 (.leaf (⟨1, by decide⟩))
 (.branch 11
 (.leaf (⟨1, by decide⟩))
 (.leaf (⟨1, by decide⟩))))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf (⟨2, by decide⟩))
 (.branch 14
 (.leaf (⟨2, by decide⟩))
 (.leaf (⟨2, by decide⟩))))
 (.branch 16
 (.leaf (⟨3, by decide⟩))
 (.branch 17
 (.leaf (⟨3, by decide⟩))
 (.leaf (⟨3, by decide⟩)))))
 (.branch 21
 (.branch 19
 (.leaf (⟨4, by decide⟩))
 (.branch 20
 (.leaf (⟨4, by decide⟩))
 (.leaf (⟨4, by decide⟩))))
 (.branch 22
 (.leaf (⟨5, by decide⟩))
 (.branch 23
 (.leaf (⟨5, by decide⟩))
 (.leaf (⟨5, by decide⟩)))))))
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record015.l := originalLeafTable.get j.val
def orbitWordTable : ConcreteGrowth.Table (List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record015.g)) :=
(.branch 12
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
 (.leaf ([⟨1, by decide⟩]))
 (.branch 8
 (.leaf ([⟨2, by decide⟩]))
 (.leaf ([⟨3, by decide⟩]))))
 (.branch 10
 (.leaf ([⟨1, by decide⟩]))
 (.branch 11
 (.leaf ([⟨2, by decide⟩]))
 (.leaf ([⟨3, by decide⟩]))))))
 (.branch 18
 (.branch 15
 (.branch 13
 (.leaf ([⟨1, by decide⟩]))
 (.branch 14
 (.leaf ([⟨2, by decide⟩]))
 (.leaf ([⟨3, by decide⟩]))))
 (.branch 16
 (.leaf ([⟨1, by decide⟩]))
 (.branch 17
 (.leaf ([⟨2, by decide⟩]))
 (.leaf ([⟨3, by decide⟩])))))
 (.branch 21
 (.branch 19
 (.leaf ([⟨1, by decide⟩]))
 (.branch 20
 (.leaf ([⟨2, by decide⟩]))
 (.leaf ([⟨3, by decide⟩]))))
 (.branch 22
 (.leaf ([⟨1, by decide⟩]))
 (.branch 23
 (.leaf ([⟨2, by decide⟩]))
 (.leaf ([⟨3, by decide⟩])))))))
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record015.g) := orbitWordTable.get j.val
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record015.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record015.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record015 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record015_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record015_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record015_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record015_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record015_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record015_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record015_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record015 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record015_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record015_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00038.record015_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00038.record015
