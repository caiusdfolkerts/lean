module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow23Part00016Data
public import GraphInputsRow23Part00016Frames
public import GraphInputsRow23Part00016Leaves
public import GraphInputsRow23Part00016Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00016.record012
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record012
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), (certNat% 4), (certNat% 5), (certNat% 6), (certNat% 7), (certNat% 8), (certNat% 9)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), (certNat% 11), (certNat% 12), (certNat% 13), (certNat% 14), (certNat% 15), (certNat% 16), (certNat% 17)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), (certNat% 19), (certNat% 3), (certNat% 12), (certNat% 20), (certNat% 21)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), (certNat% 23), 16889323236360192, (certNat% 24), (certNat% 25), (certNat% 26), (certNat% 27), (certNat% 28)]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 29), (certNat% 30), (certNat% 31), (certNat% 12), (certNat% 32), (certNat% 33), (certNat% 34), (certNat% 35), (certNat% 36)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c7 c0
  c8
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record012_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record012_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record012_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record012_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record012_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record012_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record012_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record012_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record012_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00016.record012

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00016.record013
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record013
def vertexColumn : Fields := ⟨10, (certNat% 37)⟩
def kindColumn : Fields := ⟨3, (certNat% 38)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 39), (certNat% 40), (certNat% 41), (certNat% 42), (certNat% 43), 1044835113549955072, (certNat% 44), (certNat% 45)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 46), (certNat% 47), (certNat% 48), (certNat% 42), (certNat% 49), 1116892707587883008, (certNat% 50), (certNat% 51)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 52), (certNat% 53), (certNat% 54), 3729543441416192, 1044835113549955072, (certNat% 55), (certNat% 56), (certNat% 57), (certNat% 58)]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨86, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record013_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record013_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record013_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record013_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record013_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record013_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record013_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record013_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record013_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00016.record013

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00016.record014
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record014
def vertexColumn : Fields := ⟨10, (certNat% 59)⟩
def kindColumn : Fields := ⟨3, (certNat% 60)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 61), (certNat% 62), (certNat% 63), 17125993114238976, (certNat% 64), (certNat% 65), (certNat% 66), (certNat% 67)]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record014_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record014_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record014_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record014_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record014_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record014_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record014_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record014_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record014_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00016.record014

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00016.record017
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record017
def vertexColumn : Fields := ⟨10, (certNat% 68)⟩
def kindColumn : Fields := ⟨3, (certNat% 69)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 70), (certNat% 71), 4616196764880338944, (certNat% 72), 3993426232082432, 4089268461652410368, (certNat% 73)]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 74), 4616192504272781312, 144255925564211200, (certNat% 75), 1249045209153536, 1279022294173220864, (certNat% 73), (certNat% 76)]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 77), (certNat% 78), (certNat% 79), (certNat% 80), 4616196215124525056, (certNat% 81), 4116571534393344, 4215369251218784256]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨66, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record017_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record017_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record017_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record017_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record017_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record017_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record017_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record017_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record017_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00016.record017

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00016.record001
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "3aa9a2e966c5a965594e2ba1e4789e1783e3a6992e565c56955554d2b61d4749d1743da8d6338f1364d532ce8b52ccb86d1b16c3bc1e8791e2749ca725c570de0f43c8f1b2922a86a2694619a164584e0b81ea44a91a49951465855151342d0768350ca318e1344c9322c4b0ac1b81d0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "12492492492492492492492492492492492492492249249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record001 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record001 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record001.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record001.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record001.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 52), (facetIndex 56), (facetIndex 63), (facetIndex 79), (facetIndex 93)]))
 (.leaf ([(facetIndex 44), (facetIndex 47), (facetIndex 49), (facetIndex 64), (facetIndex 76), (facetIndex 90)])))
 (.branch 3
 (.leaf ([(facetIndex 40), (facetIndex 45), (facetIndex 46), (facetIndex 48), (facetIndex 50), (facetIndex 65)]))
 (.branch 4
 (.leaf ([(facetIndex 55), (facetIndex 58), (facetIndex 59), (facetIndex 61), (facetIndex 78), (facetIndex 92)]))
 (.leaf ([(facetIndex 41), (facetIndex 54), (facetIndex 57), (facetIndex 69), (facetIndex 72), (facetIndex 83), (facetIndex 86)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 43), (facetIndex 51), (facetIndex 62), (facetIndex 75), (facetIndex 89)]))
 (.leaf ([(facetIndex 66), (facetIndex 77), (facetIndex 80), (facetIndex 91)])))
 (.branch 8
 (.leaf ([(facetIndex 68), (facetIndex 71), (facetIndex 74), (facetIndex 82), (facetIndex 85), (facetIndex 88)]))
 (.branch 9
 (.leaf ([(facetIndex 53), (facetIndex 60), (facetIndex 67), (facetIndex 73), (facetIndex 81), (facetIndex 87)]))
 (.leaf ([(facetIndex 42), (facetIndex 70), (facetIndex 84)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "36157847947860361578479478621053833403480521212215942z28;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3, 4]
def grouped2_0005 : List Nat := [3]
def grouped2_0006 : List Nat := [3, 4]
def grouped2_0007 : List Nat := [4]
def grouped2_0008 : List Nat := [5, 6]
def grouped2_0009 : List Nat := [5, 6, 7, 8, 9]
def grouped2_0010 : List Nat := [7]
def grouped2_0011 : List Nat := [7, 8, 9]
def grouped2_0012 : List Nat := [8]
def grouped2_0013 : List Nat := [8, 9]
def grouped2_0014 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record001 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record001_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00016.record001" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":10,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00016.record001" 37

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00016.record001" "{\"ridges\":[[11,273],[11,274],[20,276],[31,276],[54,273],[54,274],[60,273],[60,274],[61,273],[61,274],[62,273],[62,274],[69,276],[73,276],[75,276],[83,276],[87,276],[89,276]],\"owners\":[[11,273,[20,69,73,75],[54,60,61,62]],[54,273,[20,73,75],[11,60,61,62,69]],[60,273,[20,69,75],[11,54,61,62,73]],[61,273,[20,69,73,75],[11,54,60,62]],[62,273,[20,69,73],[11,54,60,61,75]],[11,274,[31,83,87,89],[54,60,61,62]],[54,274,[31,87,89],[11,60,61,62,83]],[60,274,[31,83,89],[11,54,61,62,87]],[61,274,[31,83,87,89],[11,54,60,62]],[62,274,[31,83,87],[11,54,60,61,89]],[20,276,[31,83,87,89],[69,73,75]],[31,276,[20,69,73,75],[83,87,89]],[69,276,[31,87,89],[20,73,75,83]],[73,276,[31,83,89],[20,69,75,87]],[75,276,[31,83,87],[20,69,73,89]],[83,276,[20,73,75],[31,69,87,89]],[87,276,[20,69,75],[31,73,83,89]],[89,276,[20,69,73],[31,75,83,87]]],\"edges\":[[33,[11,20,31,54,60,61,62,69,73,75,83,87,89]]],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00016.record001" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00016.record001\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-5,-4],[-6,-5],[-7,-5],[-8,-5],[-9,-5],[-11,-5],[-12,-5],[-17,-13],[-17,-15],[-19,-2],[-19,-11],[-19,-18],[-20,-19],[-21,-19],[-22,-5],[-24,-3],[-24,-11],[-24,-23],[-25,-24],[-26,-24],[-27,-5],[-1,2,18,20,21],[-10,2,20,21],[-14,2,18,21],[-15,2,18,20,21],[-16,2,18,20],[-1,3,23,25,26],[-10,3,25,26],[-14,3,23,26],[-15,3,23,25,26],[-16,3,23,25],[-2,3,23,25,26],[-3,2,18,20,21],[-18,3,25,26],[-20,3,23,26],[-21,3,23,25],[-23,2,20,21],[-25,2,18,21],[-26,2,18,20],[-28,4,6,7,8,9,17],[-29,11,12,13,15,22,27],[-30,5,19,24],[-31,29],[-32,28],[-32,31],[-33,32],[-34,30],[-35,34],[-36,35],[-37,33],[-37,36],[37],[1,2,3,10,14,15,16,18,20,21,23,25,26]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":42,\"b\":40},{\"tag\":\"incompatible\",\"a\":45,\"b\":42},{\"tag\":\"incompatible\",\"a\":46,\"b\":42},{\"tag\":\"incompatible\",\"a\":48,\"b\":42},{\"tag\":\"incompatible\",\"a\":50,\"b\":42},{\"tag\":\"incompatible\",\"a\":55,\"b\":42},{\"tag\":\"incompatible\",\"a\":58,\"b\":42},{\"tag\":\"incompatible\",\"a\":65,\"b\":59},{\"tag\":\"incompatible\",\"a\":65,\"b\":61},{\"tag\":\"incompatible\",\"a\":70,\"b\":20},{\"tag\":\"incompatible\",\"a\":70,\"b\":55},{\"tag\":\"incompatible\",\"a\":70,\"b\":69},{\"tag\":\"incompatible\",\"a\":73,\"b\":70},{\"tag\":\"incompatible\",\"a\":75,\"b\":70},{\"tag\":\"incompatible\",\"a\":78,\"b\":42},{\"tag\":\"incompatible\",\"a\":84,\"b\":31},{\"tag\":\"incompatible\",\"a\":84,\"b\":55},{\"tag\":\"incompatible\",\"a\":84,\"b\":83},{\"tag\":\"incompatible\",\"a\":87,\"b\":84},{\"tag\":\"incompatible\",\"a\":89,\"b\":84},{\"tag\":\"incompatible\",\"a\":92,\"b\":42},{\"tag\":\"mate\",\"ridge\":273,\"a\":11,\"owners\":[20,69,73,75]},{\"tag\":\"mate\",\"ridge\":273,\"a\":54,\"owners\":[20,73,75]},{\"tag\":\"mate\",\"ridge\":273,\"a\":60,\"owners\":[20,69,75]},{\"tag\":\"mate\",\"ridge\":273,\"a\":61,\"owners\":[20,69,73,75]},{\"tag\":\"mate\",\"ridge\":273,\"a\":62,\"owners\":[20,69,73]},{\"tag\":\"mate\",\"ridge\":274,\"a\":11,\"owners\":[31,83,87,89]},{\"tag\":\"mate\",\"ridge\":274,\"a\":54,\"owners\":[31,87,89]},{\"tag\":\"mate\",\"ridge\":274,\"a\":60,\"owners\":[31,83,89]},{\"tag\":\"mate\",\"ridge\":274,\"a\":61,\"owners\":[31,83,87,89]},{\"tag\":\"mate\",\"ridge\":274,\"a\":62,\"owners\":[31,83,87]},{\"tag\":\"mate\",\"ridge\":276,\"a\":20,\"owners\":[31,83,87,89]},{\"tag\":\"mate\",\"ridge\":276,\"a\":31,\"owners\":[20,69,73,75]},{\"tag\":\"mate\",\"ridge\":276,\"a\":69,\"owners\":[31,87,89]},{\"tag\":\"mate\",\"ridge\":276,\"a\":73,\"owners\":[31,83,89]},{\"tag\":\"mate\",\"ridge\":276,\"a\":75,\"owners\":[31,83,87]},{\"tag\":\"mate\",\"ridge\":276,\"a\":83,\"owners\":[20,73,75]},{\"tag\":\"mate\",\"ridge\":276,\"a\":87,\"owners\":[20,69,75]},{\"tag\":\"mate\",\"ridge\":276,\"a\":89,\"owners\":[20,69,73]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[40,45,46,48,50,65],\"full_literals\":[-28,4,6,7,8,9,17]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[55,58,59,61,78,92],\"full_literals\":[-29,11,12,13,15,22,27]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[42,70,84],\"full_literals\":[-30,5,19,24]},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-31,29,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-32,28,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-32,false,31],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-33,false,32],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-34,false,30],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-35,false,34],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-36,false,35],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-37,33,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-37,false,36],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":10,\"grouped\":true},{\"tag\":\"edge\",\"edge\":33,\"owners\":[11,20,31,54,60,61,62,69,73,75,83,87,89]}]}"
  "54 33 0 52 50 0\n55 36 0 52 51 0\n56 32 0 54 46 0\n57 35 0 55 49 0\n58 28 0 56 44 0\n59 31 0 56 45 0\n60 34 0 57 48 0\n61 29 0 59 43 0\n62 30 0 60 47 0\n63 -11 0 62 6 11 17 42 0\n64 -5 0 58 63 61 1 2 3 4 5 7 15 21 40 8 9 41 0\n65 3 26 23 25 0 27 32 35 29 28 34 30 31 36 53 0\n66 -24 0 16 18 19 20 65 0\n67 19 0 66 62 64 42 0\n68 -2 0 67 10 0\n69 -18 0 67 12 0\n70 -20 0 67 13 0\n71 -21 0 67 14 0\n72 -1 0 68 69 70 71 22 0\n73 -14 0 69 68 71 24 0\n74 -15 0 69 68 70 71 25 0\n75 -16 0 69 68 70 26 0\n76 -3 0 69 68 70 71 33 0\n77 -25 0 69 68 71 38 0\n78 -26 0 69 68 70 39 0\n79 -10 0 70 68 71 23 0\n80 -23 0 70 68 71 37 0\n81 0 70 71 72 68 79 74 73 75 69 76 80 77 78 53 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record001.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record001.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record001.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record001.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record001 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record001.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record001.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record001.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record001.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record001 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record001_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record001 Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record001_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record001_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00016.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00016.record003
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "29ca68ba599561d94e4b8ae1ba1e4789e1783eaa4b959695955551d70da354d8b52d2b46d4749d1743d58ce3a4d5334cb31ce8b62d4b4ac6b86d1b16c3b49ca785d1725c3783c8f13e98870aa26946198564382e07a91a24a98649951465854558350d0b41d50ca318c9314d0b22c2b06d0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "92492492492492492492492492492492492492492491249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record003 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record003 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record003.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record003.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record003.data.quota

def groupMembers1 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 18
 (.branch 9
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
 (.branch 8
 (.leaf ([(facetIndex 7)]))
 (.leaf ([(facetIndex 8)]))))))
 (.branch 13
 (.branch 11
 (.branch 10
 (.leaf ([(facetIndex 9)]))
 (.leaf ([(facetIndex 10)])))
 (.branch 12
 (.leaf ([(facetIndex 11)]))
 (.leaf ([(facetIndex 12)]))))
 (.branch 15
 (.branch 14
 (.leaf ([(facetIndex 13)]))
 (.leaf ([(facetIndex 14)])))
 (.branch 16
 (.leaf ([(facetIndex 15)]))
 (.branch 17
 (.leaf ([(facetIndex 16)]))
 (.leaf ([(facetIndex 17)])))))))
 (.branch 27
 (.branch 22
 (.branch 20
 (.branch 19
 (.leaf ([(facetIndex 18)]))
 (.leaf ([(facetIndex 19)])))
 (.branch 21
 (.leaf ([(facetIndex 20)]))
 (.leaf ([(facetIndex 21)]))))
 (.branch 24
 (.branch 23
 (.leaf ([(facetIndex 22)]))
 (.leaf ([(facetIndex 23)])))
 (.branch 25
 (.leaf ([(facetIndex 24)]))
 (.branch 26
 (.leaf ([(facetIndex 25)]))
 (.leaf ([(facetIndex 26)]))))))
 (.branch 32
 (.branch 29
 (.branch 28
 (.leaf ([(facetIndex 27)]))
 (.leaf ([(facetIndex 28)])))
 (.branch 30
 (.leaf ([(facetIndex 29)]))
 (.branch 31
 (.leaf ([(facetIndex 30)]))
 (.leaf ([(facetIndex 31)])))))
 (.branch 34
 (.branch 33
 (.leaf ([(facetIndex 32)]))
 (.leaf ([(facetIndex 33)])))
 (.branch 35
 (.leaf ([(facetIndex 34)]))
 (.branch 36
 (.leaf ([(facetIndex 35)]))
 (.leaf ([(facetIndex 36)]))))))))
def groupColors1 : PackedGraphCertificate.Fields :=
  ⟨6, sparse_nat% "248e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040"⟩
def grouping1 : FacetSat.Grouping data.count where
  count := 37
  members := fun g => groupMembers1.get g
  color := fun c => groupColors1.get c.val
def groupKind1 : List Nat := List.range grouping1.count

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 38), (facetIndex 64), (facetIndex 67), (facetIndex 69), (facetIndex 71), (facetIndex 79)]))
 (.leaf ([(facetIndex 40), (facetIndex 46), (facetIndex 55), (facetIndex 56), (facetIndex 57), (facetIndex 60)])))
 (.branch 3
 (.leaf ([(facetIndex 39), (facetIndex 43), (facetIndex 49), (facetIndex 54), (facetIndex 59), (facetIndex 84), (facetIndex 93)]))
 (.branch 4
 (.leaf ([(facetIndex 63), (facetIndex 73), (facetIndex 74), (facetIndex 75), (facetIndex 77)]))
 (.leaf ([(facetIndex 37), (facetIndex 81), (facetIndex 85), (facetIndex 88), (facetIndex 89), (facetIndex 90), (facetIndex 91)])))))
 (.branch 8
 (.branch 6
 (.leaf ([(facetIndex 62), (facetIndex 65), (facetIndex 66), (facetIndex 68), (facetIndex 70), (facetIndex 72)]))
 (.branch 7
 (.leaf ([(facetIndex 41), (facetIndex 44), (facetIndex 76), (facetIndex 82), (facetIndex 86), (facetIndex 94)]))
 (.leaf ([(facetIndex 45), (facetIndex 50), (facetIndex 51), (facetIndex 52), (facetIndex 61)]))))
 (.branch 9
 (.leaf ([(facetIndex 53), (facetIndex 78), (facetIndex 92)]))
 (.branch 10
 (.leaf ([(facetIndex 80), (facetIndex 83), (facetIndex 87)]))
 (.leaf ([(facetIndex 42), (facetIndex 47), (facetIndex 48), (facetIndex 58)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "628444496429649083633350505055035712a111287772aa1762a61204z25;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 11
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped1_0000 : List Nat := [24]
def grouped1_0001 : List Nat := [24, 25, 26]
def grouped1_0002 : List Nat := [25]
def grouped1_0003 : List Nat := [25, 26]
def grouped1_0004 : List Nat := [26]
def grouped2_0005 : List Nat := [0]
def grouped2_0006 : List Nat := [0, 1]
def grouped2_0007 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0009 : List Nat := [1]
def grouped2_0010 : List Nat := [2]
def grouped2_0011 : List Nat := [2, 3, 4]
def grouped2_0012 : List Nat := [3]
def grouped2_0013 : List Nat := [3, 4]
def grouped2_0014 : List Nat := [4]
def grouped2_0015 : List Nat := [5]
def grouped2_0016 : List Nat := [5, 6, 7]
def grouped2_0017 : List Nat := [5, 6, 7, 8, 9, 10]
def grouped2_0018 : List Nat := [6]
def grouped2_0019 : List Nat := [6, 7]
def grouped2_0020 : List Nat := [7]
def grouped2_0021 : List Nat := [8]
def grouped2_0022 : List Nat := [8, 9, 10]
def grouped2_0023 : List Nat := [9]
def grouped2_0024 : List Nat := [9, 10]
def grouped2_0025 : List Nat := [10]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record003 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record003_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00016.record003" "{\"atoms\":[{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"group\",\"kind\":1,\"index\":24},{\"tag\":\"group\",\"kind\":1,\"index\":25},{\"tag\":\"group\",\"kind\":1,\"index\":26},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0003\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0001\"},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group\",\"kind\":2,\"index\":10},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0019\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0016\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0024\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0022\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":6,\"list_name\":\"grouped2_0017\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":10,\"list_name\":\"groupKind2\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":11,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00016.record003" 109

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00016.record003" "{\"ridges\":[[5,25],[9,81],[11,97],[12,161],[13,321],[17,517],[20,69],[20,97],[21,69],[24,137],[25,137],[26,641],[30,84],[31,98],[31,100],[32,324],[34,168],[35,532],[36,648],[44,161],[47,25],[47,81],[48,25],[50,97],[52,321],[53,137],[55,81],[55,97],[57,81],[58,81],[58,321],[59,641],[60,97],[60,161],[61,97],[61,321],[64,137],[66,69],[67,137],[69,41],[70,69],[71,517],[75,69],[76,641],[77,97],[81,84],[85,100],[86,162],[88,324],[89,84],[89,100],[90,84],[90,324],[91,100],[91,324],[92,26],[92,146],[92,168],[93,648],[94,532],[94,648],[94,656]],\"owners\":[[5,25,[14,22,23,62,63,65,78],[46,47,48]],[47,25,[14,22,23,62,65,78],[5,46,48,63]],[48,25,[14,22,23,62,63,78],[5,46,47,65]],[92,26,[5,27,47,48,49,81,83,84],[33,46,80,93]],[69,41,[6,24,46,50,51,78],[15,62,66,68,79]],[9,81,[18,63,73,74,75],[47,55,57,58]],[47,81,[18,73,74,75],[9,55,57,58,63]],[55,81,[18,63,74,75],[9,47,57,58,73]],[57,81,[18,63,73,74,75],[9,47,55,58]],[58,81,[18,63,73,75],[9,47,55,57,74]],[92,146,[10,41,57,59],[33,56,82,93]],[11,97,[20,66,73,77],[50,55,60,61]],[20,97,[11,50,55,60,61],[66,73,77]],[50,97,[20,73,77],[11,55,60,61,66]],[55,97,[20,66,77],[11,50,60,61,73]],[60,97,[20,66,73,77],[11,50,55,61]],[61,97,[20,66,73],[11,50,55,60,77]],[77,97,[11,50,55,60],[20,61,66,73]],[31,98,[11,50,55,60,61],[85,89,91]],[12,161,[24,67,78,79],[44,56,60]],[44,161,[24,78,79],[12,56,60,67]],[60,161,[24,67,78,79],[12,44,56]],[86,162,[12,56,60],[34,44,92]],[13,321,[21,70,74,77],[52,58,61]],[52,321,[21,74,77],[13,58,61,70]],[58,321,[21,70,77],[13,52,61,74]],[61,321,[21,70,74],[13,52,58,77]],[17,517,[19,43,75,76],[39,69,71,72]],[71,517,[19,43,75],[17,39,69,72,76]],[30,84,[18,63,73,74,75],[81,89,90]],[81,84,[18,73,74,75],[30,63,89,90]],[89,84,[18,63,74,75],[30,73,81,90]],[90,84,[18,63,73,75],[30,74,81,89]],[35,532,[19,43,75,76],[84,94]],[94,532,[19,43,75],[35,76,84]],[31,100,[20,66,73,77],[85,89,91]],[85,100,[20,73,77],[31,66,89,91]],[89,100,[20,66,77],[31,73,85,91]],[91,100,[20,66,73],[31,77,85,89]],[32,324,[21,70,74,77],[88,90,91]],[88,324,[21,74,77],[32,70,90,91]],[90,324,[21,70,77],[32,74,88,91]],[91,324,[21,70,74],[32,77,88,90]],[34,168,[24,67,78,79],[86,92]],[92,168,[24,67,79],[34,78,86]],[26,641,[25,54,71,79],[59,76]],[59,641,[25,71,79],[26,54,76]],[76,641,[25,54,79],[26,59,71]],[36,648,[25,54,71,79],[93,94]],[93,648,[25,71,79],[36,54,94]],[94,648,[25,54,79],[36,71,93]],[94,656,[26,59],[36,76,93]]],\"edges\":[[23,[17,19,35,39,43,69,71,72,75,76,84,94]],[31,[9,18,30,47,55,57,58,63,73,74,75,81,89,90]],[35,[11,20,31,50,55,60,61,66,73,77,85,89,91]],[36,[12,24,34,44,56,60,67,78,79,86,92]],[40,[13,21,32,52,58,61,70,74,77,88,90,91]],[43,[25,26,36,54,59,71,76,79,93,94]]],\"groupings\":[1,2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00016.record003" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00016.record003\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-30,-29],[-32,-5],[-34,-4],[-34,-29],[-35,-29],[-37,-32],[-40,-2],[-40,-27],[-40,-33],[-40,-37],[-40,-38],[-41,-16],[-41,-40],[-43,-40],[-44,-34],[-45,-29],[-46,-34],[-47,-32],[-48,-32],[-50,-11],[-50,-28],[-50,-31],[-53,-32],[-56,-50],[-56,-52],[-56,-53],[-56,-55],[-57,-53],[-57,-56],[-58,-29],[-58,-32],[-59,-50],[-59,-56],[-60,-13],[-60,-57],[-61,-12],[-61,-53],[-61,-60],[-62,-8],[-62,-50],[-62,-52],[-62,-61],[-63,-50],[-63,-54],[-63,-58],[-63,-62],[-64,-10],[-64,-50],[-64,-60],[-64,-61],[-64,-62],[-65,-17],[-65,-41],[-66,-14],[-66,-40],[-66,-65],[-69,-58],[-70,-30],[-70,-35],[-70,-45],[-71,-50],[-73,-58],[-74,-19],[-74,-26],[-74,-68],[-74,-72],[-75,-74],[-77,-30],[-77,-35],[-77,-45],[-78,-74],[-79,-27],[-79,-41],[-79,-42],[-79,-49],[-79,-60],[-79,-67],[-79,-69],[-79,-73],[-79,-76],[-81,-15],[-81,-36],[-81,-54],[-81,-58],[-81,-71],[-12,-13,-62],[-12,-57,-62],[-13,-53,-62],[-1,8,14,15,49,50,52,65],[-34,8,14,15,49,52,65],[-35,8,14,15,49,50,65],[-79,1,19,34,35,36,68,70,71],[-56,2,16,33,37,38,65],[-16,-17,-40],[-16,-17,-51],[-17,-40,-51],[-17,-40,-54],[-3,10,50,60,61,62],[-34,10,60,61,62],[-42,10,50,61,62],[-44,10,50,60,61,62],[-45,10,50,60,62],[-79,4,29,44,46],[-5,12,53,60,64],[-12,5,37,42,47,48],[-37,12,60,64],[-42,12,53,64],[-47,12,53,60,64],[-48,12,53,60],[-64,5,37,42,47],[-21,5,37,42,47,48],[-6,16,54,65,66],[-32,16,65,66],[-47,16,54,65,66],[-73,6,43,47],[-7,13,57,61,64],[-39,13,61,64],[-45,13,57,64],[-48,13,57,61],[-9,11,31,62,63],[-58,11,31,62],[-20,10,50,60,61,62],[-68,10,60,61,62],[-76,10,50,61,62],[-77,10,50,60,62],[-24,11,31,62,63],[-81,11,31,62],[-21,12,53,60,64],[-72,12,60,64],[-76,12,53,64],[-78,12,53,60],[-22,13,57,61,64],[-75,13,61,64],[-77,13,57,64],[-78,13,57,61],[-23,16,54,65,66],[-79,16,54,66],[-18,17,41,58,66],[-46,17,58,66],[-63,17,41,66],[-25,17,41,58,66],[-80,17,58,66],[-81,17,41,66],[-81,18,46],[-82,16],[-16,82],[-83,17],[-17,83],[-84,18],[-18,84],[-85,83,84],[-84,85],[-83,85],[-86,82,85],[-85,86],[-82,86],[-87,27,51,54,56,58,66],[-54,87],[-58,87],[-66,87],[-33,88],[-89,50,60,61,62,64],[-90,26,68,72,75,76,77,78],[-68,90],[-72,90],[-77,90],[-78,90],[-91,49,52,53,55,57,59],[-92,29,32,63,69,73,81],[-93,40,65,79],[-94,67,70,74],[-95,30,34,35,45],[-96,87],[-87,-88,96],[-97,89,90],[-98,89],[-98,90],[-99,97],[-100,98],[-101,96,100],[-101,99],[-102,100],[-96,-100,102],[-103,92],[-104,91],[-104,103],[-105,94],[-105,95],[-106,93],[-106,105],[-107,104],[-107,106],[-108,101],[-108,102,107],[-102,-107,109],[108],[-109],[9,11,24,28,31,56,58,59,62,63,71,81],[3,10,20,34,42,44,45,50,60,61,62,68,76,77],[5,12,21,37,42,47,48,53,60,64,72,76,78],[6,16,23,32,43,47,54,65,66,73,79],[7,13,22,39,45,48,57,61,64,75,77,78],[17,18,25,41,46,58,63,66,80,81]],\"atoms\":[{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":81},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":85},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":89},{\"tag\":\"facet\",\"index\":90},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"facet\",\"index\":94},{\"tag\":\"group\",\"index\":24,\"kind\":1},{\"tag\":\"group\",\"index\":25,\"kind\":1},{\"tag\":\"group\",\"index\":26,\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group\",\"index\":10,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":42,\"b\":41},{\"tag\":\"incompatible\",\"a\":44,\"b\":11},{\"tag\":\"incompatible\",\"a\":47,\"b\":10},{\"tag\":\"incompatible\",\"a\":47,\"b\":41},{\"tag\":\"incompatible\",\"a\":48,\"b\":41},{\"tag\":\"incompatible\",\"a\":50,\"b\":44},{\"tag\":\"incompatible\",\"a\":53,\"b\":6},{\"tag\":\"incompatible\",\"a\":53,\"b\":38},{\"tag\":\"incompatible\",\"a\":53,\"b\":46},{\"tag\":\"incompatible\",\"a\":53,\"b\":50},{\"tag\":\"incompatible\",\"a\":53,\"b\":51},{\"tag\":\"incompatible\",\"a\":54,\"b\":24},{\"tag\":\"incompatible\",\"a\":54,\"b\":53},{\"tag\":\"incompatible\",\"a\":56,\"b\":53},{\"tag\":\"incompatible\",\"a\":57,\"b\":47},{\"tag\":\"incompatible\",\"a\":58,\"b\":41},{\"tag\":\"incompatible\",\"a\":59,\"b\":47},{\"tag\":\"incompatible\",\"a\":60,\"b\":44},{\"tag\":\"incompatible\",\"a\":61,\"b\":44},{\"tag\":\"incompatible\",\"a\":63,\"b\":19},{\"tag\":\"incompatible\",\"a\":63,\"b\":39},{\"tag\":\"incompatible\",\"a\":63,\"b\":43},{\"tag\":\"incompatible\",\"a\":66,\"b\":44},{\"tag\":\"incompatible\",\"a\":69,\"b\":63},{\"tag\":\"incompatible\",\"a\":69,\"b\":65},{\"tag\":\"incompatible\",\"a\":69,\"b\":66},{\"tag\":\"incompatible\",\"a\":69,\"b\":68},{\"tag\":\"incompatible\",\"a\":70,\"b\":66},{\"tag\":\"incompatible\",\"a\":70,\"b\":69},{\"tag\":\"incompatible\",\"a\":71,\"b\":41},{\"tag\":\"incompatible\",\"a\":71,\"b\":44},{\"tag\":\"incompatible\",\"a\":72,\"b\":63},{\"tag\":\"incompatible\",\"a\":72,\"b\":69},{\"tag\":\"incompatible\",\"a\":73,\"b\":21},{\"tag\":\"incompatible\",\"a\":73,\"b\":70},{\"tag\":\"incompatible\",\"a\":74,\"b\":20},{\"tag\":\"incompatible\",\"a\":74,\"b\":66},{\"tag\":\"incompatible\",\"a\":74,\"b\":73},{\"tag\":\"incompatible\",\"a\":75,\"b\":14},{\"tag\":\"incompatible\",\"a\":75,\"b\":63},{\"tag\":\"incompatible\",\"a\":75,\"b\":65},{\"tag\":\"incompatible\",\"a\":75,\"b\":74},{\"tag\":\"incompatible\",\"a\":76,\"b\":63},{\"tag\":\"incompatible\",\"a\":76,\"b\":67},{\"tag\":\"incompatible\",\"a\":76,\"b\":71},{\"tag\":\"incompatible\",\"a\":76,\"b\":75},{\"tag\":\"incompatible\",\"a\":77,\"b\":18},{\"tag\":\"incompatible\",\"a\":77,\"b\":63},{\"tag\":\"incompatible\",\"a\":77,\"b\":73},{\"tag\":\"incompatible\",\"a\":77,\"b\":74},{\"tag\":\"incompatible\",\"a\":77,\"b\":75},{\"tag\":\"incompatible\",\"a\":78,\"b\":25},{\"tag\":\"incompatible\",\"a\":78,\"b\":54},{\"tag\":\"incompatible\",\"a\":79,\"b\":22},{\"tag\":\"incompatible\",\"a\":79,\"b\":53},{\"tag\":\"incompatible\",\"a\":79,\"b\":78},{\"tag\":\"incompatible\",\"a\":82,\"b\":71},{\"tag\":\"incompatible\",\"a\":83,\"b\":42},{\"tag\":\"incompatible\",\"a\":83,\"b\":48},{\"tag\":\"incompatible\",\"a\":83,\"b\":58},{\"tag\":\"incompatible\",\"a\":84,\"b\":63},{\"tag\":\"incompatible\",\"a\":86,\"b\":71},{\"tag\":\"incompatible\",\"a\":87,\"b\":27},{\"tag\":\"incompatible\",\"a\":87,\"b\":37},{\"tag\":\"incompatible\",\"a\":87,\"b\":81},{\"tag\":\"incompatible\",\"a\":87,\"b\":85},{\"tag\":\"incompatible\",\"a\":88,\"b\":87},{\"tag\":\"incompatible\",\"a\":90,\"b\":42},{\"tag\":\"incompatible\",\"a\":90,\"b\":48},{\"tag\":\"incompatible\",\"a\":90,\"b\":58},{\"tag\":\"incompatible\",\"a\":91,\"b\":87},{\"tag\":\"incompatible\",\"a\":92,\"b\":38},{\"tag\":\"incompatible\",\"a\":92,\"b\":54},{\"tag\":\"incompatible\",\"a\":92,\"b\":55},{\"tag\":\"incompatible\",\"a\":92,\"b\":62},{\"tag\":\"incompatible\",\"a\":92,\"b\":73},{\"tag\":\"incompatible\",\"a\":92,\"b\":80},{\"tag\":\"incompatible\",\"a\":92,\"b\":82},{\"tag\":\"incompatible\",\"a\":92,\"b\":86},{\"tag\":\"incompatible\",\"a\":92,\"b\":89},{\"tag\":\"incompatible\",\"a\":94,\"b\":23},{\"tag\":\"incompatible\",\"a\":94,\"b\":49},{\"tag\":\"incompatible\",\"a\":94,\"b\":67},{\"tag\":\"incompatible\",\"a\":94,\"b\":71},{\"tag\":\"incompatible\",\"a\":94,\"b\":84},{\"tag\":\"three\",\"ridge\":69,\"vertices\":[20,21,75]},{\"tag\":\"three\",\"ridge\":69,\"vertices\":[20,70,75]},{\"tag\":\"three\",\"ridge\":69,\"vertices\":[21,66,75]},{\"tag\":\"mate\",\"ridge\":25,\"a\":5,\"owners\":[14,22,23,62,63,65,78]},{\"tag\":\"mate\",\"ridge\":25,\"a\":47,\"owners\":[14,22,23,62,65,78]},{\"tag\":\"mate\",\"ridge\":25,\"a\":48,\"owners\":[14,22,23,62,63,78]},{\"tag\":\"mate\",\"ridge\":26,\"a\":92,\"owners\":[5,27,47,48,49,81,83,84]},{\"tag\":\"mate\",\"ridge\":41,\"a\":69,\"owners\":[6,24,46,50,51,78]},{\"tag\":\"three\",\"ridge\":137,\"vertices\":[24,25,53]},{\"tag\":\"three\",\"ridge\":137,\"vertices\":[24,25,64]},{\"tag\":\"three\",\"ridge\":137,\"vertices\":[25,53,64]},{\"tag\":\"three\",\"ridge\":137,\"vertices\":[25,53,67]},{\"tag\":\"mate\",\"ridge\":81,\"a\":9,\"owners\":[18,63,73,74,75]},{\"tag\":\"mate\",\"ridge\":81,\"a\":47,\"owners\":[18,73,74,75]},{\"tag\":\"mate\",\"ridge\":81,\"a\":55,\"owners\":[18,63,74,75]},{\"tag\":\"mate\",\"ridge\":81,\"a\":57,\"owners\":[18,63,73,74,75]},{\"tag\":\"mate\",\"ridge\":81,\"a\":58,\"owners\":[18,63,73,75]},{\"tag\":\"mate\",\"ridge\":146,\"a\":92,\"owners\":[10,41,57,59]},{\"tag\":\"mate\",\"ridge\":97,\"a\":11,\"owners\":[20,66,73,77]},{\"tag\":\"mate\",\"ridge\":97,\"a\":20,\"owners\":[11,50,55,60,61]},{\"tag\":\"mate\",\"ridge\":97,\"a\":50,\"owners\":[20,73,77]},{\"tag\":\"mate\",\"ridge\":97,\"a\":55,\"owners\":[20,66,77]},{\"tag\":\"mate\",\"ridge\":97,\"a\":60,\"owners\":[20,66,73,77]},{\"tag\":\"mate\",\"ridge\":97,\"a\":61,\"owners\":[20,66,73]},{\"tag\":\"mate\",\"ridge\":97,\"a\":77,\"owners\":[11,50,55,60]},{\"tag\":\"mate\",\"ridge\":98,\"a\":31,\"owners\":[11,50,55,60,61]},{\"tag\":\"mate\",\"ridge\":161,\"a\":12,\"owners\":[24,67,78,79]},{\"tag\":\"mate\",\"ridge\":161,\"a\":44,\"owners\":[24,78,79]},{\"tag\":\"mate\",\"ridge\":161,\"a\":60,\"owners\":[24,67,78,79]},{\"tag\":\"mate\",\"ridge\":162,\"a\":86,\"owners\":[12,56,60]},{\"tag\":\"mate\",\"ridge\":321,\"a\":13,\"owners\":[21,70,74,77]},{\"tag\":\"mate\",\"ridge\":321,\"a\":52,\"owners\":[21,74,77]},{\"tag\":\"mate\",\"ridge\":321,\"a\":58,\"owners\":[21,70,77]},{\"tag\":\"mate\",\"ridge\":321,\"a\":61,\"owners\":[21,70,74]},{\"tag\":\"mate\",\"ridge\":517,\"a\":17,\"owners\":[19,43,75,76]},{\"tag\":\"mate\",\"ridge\":517,\"a\":71,\"owners\":[19,43,75]},{\"tag\":\"mate\",\"ridge\":84,\"a\":30,\"owners\":[18,63,73,74,75]},{\"tag\":\"mate\",\"ridge\":84,\"a\":81,\"owners\":[18,73,74,75]},{\"tag\":\"mate\",\"ridge\":84,\"a\":89,\"owners\":[18,63,74,75]},{\"tag\":\"mate\",\"ridge\":84,\"a\":90,\"owners\":[18,63,73,75]},{\"tag\":\"mate\",\"ridge\":532,\"a\":35,\"owners\":[19,43,75,76]},{\"tag\":\"mate\",\"ridge\":532,\"a\":94,\"owners\":[19,43,75]},{\"tag\":\"mate\",\"ridge\":100,\"a\":31,\"owners\":[20,66,73,77]},{\"tag\":\"mate\",\"ridge\":100,\"a\":85,\"owners\":[20,73,77]},{\"tag\":\"mate\",\"ridge\":100,\"a\":89,\"owners\":[20,66,77]},{\"tag\":\"mate\",\"ridge\":100,\"a\":91,\"owners\":[20,66,73]},{\"tag\":\"mate\",\"ridge\":324,\"a\":32,\"owners\":[21,70,74,77]},{\"tag\":\"mate\",\"ridge\":324,\"a\":88,\"owners\":[21,74,77]},{\"tag\":\"mate\",\"ridge\":324,\"a\":90,\"owners\":[21,70,77]},{\"tag\":\"mate\",\"ridge\":324,\"a\":91,\"owners\":[21,70,74]},{\"tag\":\"mate\",\"ridge\":168,\"a\":34,\"owners\":[24,67,78,79]},{\"tag\":\"mate\",\"ridge\":168,\"a\":92,\"owners\":[24,67,79]},{\"tag\":\"mate\",\"ridge\":641,\"a\":26,\"owners\":[25,54,71,79]},{\"tag\":\"mate\",\"ridge\":641,\"a\":59,\"owners\":[25,71,79]},{\"tag\":\"mate\",\"ridge\":641,\"a\":76,\"owners\":[25,54,79]},{\"tag\":\"mate\",\"ridge\":648,\"a\":36,\"owners\":[25,54,71,79]},{\"tag\":\"mate\",\"ridge\":648,\"a\":93,\"owners\":[25,71,79]},{\"tag\":\"mate\",\"ridge\":648,\"a\":94,\"owners\":[25,54,79]},{\"tag\":\"mate\",\"ridge\":656,\"a\":94,\"owners\":[26,59]},{\"tag\":\"group_or\",\"kind\":1,\"index\":24,\"members\":[24],\"full_literals\":[-82,16]},{\"tag\":\"group_take\",\"kind\":1,\"index\":24,\"member\":24,\"full_literals\":[-16,82]},{\"tag\":\"group_or\",\"kind\":1,\"index\":25,\"members\":[25],\"full_literals\":[-83,17]},{\"tag\":\"group_take\",\"kind\":1,\"index\":25,\"member\":25,\"full_literals\":[-17,83]},{\"tag\":\"group_or\",\"kind\":1,\"index\":26,\"members\":[26],\"full_literals\":[-84,18]},{\"tag\":\"group_take\",\"kind\":1,\"index\":26,\"member\":26,\"full_literals\":[-18,84]},{\"tag\":\"merge\",\"left\":[25],\"right\":[26],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0004\",\"joined_name\":\"grouped1_0003\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-85,83,84],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[25],\"right\":[26],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0004\",\"joined_name\":\"grouped1_0003\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-84,85],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[25],\"right\":[26],\"left_name\":\"grouped1_0002\",\"right_name\":\"grouped1_0004\",\"joined_name\":\"grouped1_0003\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-83,false,85],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[24],\"right\":[25,26],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0003\",\"joined_name\":\"grouped1_0001\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-86,82,85],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[24],\"right\":[25,26],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0003\",\"joined_name\":\"grouped1_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-85,86],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[24],\"right\":[25,26],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0003\",\"joined_name\":\"grouped1_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-82,false,86],\"grouped\":true,\"kind\":1},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[38,64,67,69,71,79],\"full_literals\":[-87,27,51,54,56,58,66]},{\"tag\":\"group_take\",\"kind\":2,\"index\":0,\"member\":67,\"full_literals\":[-54,87]},{\"tag\":\"group_take\",\"kind\":2,\"index\":0,\"member\":71,\"full_literals\":[-58,87]},{\"tag\":\"group_take\",\"kind\":2,\"index\":0,\"member\":79,\"full_literals\":[-66,87]},{\"tag\":\"group_take\",\"kind\":2,\"index\":1,\"member\":46,\"full_literals\":[-33,88]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[63,73,74,75,77],\"full_literals\":[-89,50,60,61,62,64]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[37,81,85,88,89,90,91],\"full_literals\":[-90,26,68,72,75,76,77,78]},{\"tag\":\"group_take\",\"kind\":2,\"index\":4,\"member\":81,\"full_literals\":[-68,90]},{\"tag\":\"group_take\",\"kind\":2,\"index\":4,\"member\":85,\"full_literals\":[-72,90]},{\"tag\":\"group_take\",\"kind\":2,\"index\":4,\"member\":90,\"full_literals\":[-77,90]},{\"tag\":\"group_take\",\"kind\":2,\"index\":4,\"member\":91,\"full_literals\":[-78,90]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[62,65,66,68,70,72],\"full_literals\":[-91,49,52,53,55,57,59]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[41,44,76,82,86,94],\"full_literals\":[-92,29,32,63,69,73,81]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[53,78,92],\"full_literals\":[-93,40,65,79]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[80,83,87],\"full_literals\":[-94,67,70,74]},{\"tag\":\"group_or\",\"kind\":2,\"index\":10,\"members\":[42,47,48,58],\"full_literals\":[-95,30,34,35,45]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-96,87,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-87,-88,96],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-97,89,90],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-98,89,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-98,false,90],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-99,false,97],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-100,false,98],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-101,96,100],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0007\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-101,false,99],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0007\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-102,false,100],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0007\",\"a\":2,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-96,-100,102],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0018\",\"right_name\":\"grouped2_0020\",\"joined_name\":\"grouped2_0019\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-103,92,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped2_0015\",\"right_name\":\"grouped2_0019\",\"joined_name\":\"grouped2_0016\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-104,91,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6,7],\"left_name\":\"grouped2_0015\",\"right_name\":\"grouped2_0019\",\"joined_name\":\"grouped2_0016\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-104,false,103],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped2_0023\",\"right_name\":\"grouped2_0025\",\"joined_name\":\"grouped2_0024\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-105,94,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[9],\"right\":[10],\"left_name\":\"grouped2_0023\",\"right_name\":\"grouped2_0025\",\"joined_name\":\"grouped2_0024\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-105,false,95],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped2_0021\",\"right_name\":\"grouped2_0024\",\"joined_name\":\"grouped2_0022\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-106,93,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9,10],\"left_name\":\"grouped2_0021\",\"right_name\":\"grouped2_0024\",\"joined_name\":\"grouped2_0022\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-106,false,105],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped2_0016\",\"right_name\":\"grouped2_0022\",\"joined_name\":\"grouped2_0017\",\"a\":2,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-107,104,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6,7],\"right\":[8,9,10],\"left_name\":\"grouped2_0016\",\"right_name\":\"grouped2_0022\",\"joined_name\":\"grouped2_0017\",\"a\":3,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-107,false,106],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":6,\"direction\":\"backward\",\"full_literals\":[-108,101,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-108,102,107],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9,10],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":6,\"direction\":\"forward\",\"full_literals\":[-102,-107,109],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":10,\"grouped\":true},{\"tag\":\"quota_upper\",\"kind\":2,\"quota\":10,\"grouped\":true},{\"tag\":\"edge\",\"edge\":23,\"owners\":[17,19,35,39,43,69,71,72,75,76,84,94]},{\"tag\":\"edge\",\"edge\":31,\"owners\":[9,18,30,47,55,57,58,63,73,74,75,81,89,90]},{\"tag\":\"edge\",\"edge\":35,\"owners\":[11,20,31,50,55,60,61,66,73,77,85,89,91]},{\"tag\":\"edge\",\"edge\":36,\"owners\":[12,24,34,44,56,60,67,78,79,86,92]},{\"tag\":\"edge\",\"edge\":40,\"owners\":[13,21,32,52,58,61,70,74,77,88,90,91]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[25,26,36,54,59,71,76,79,93,94]}]}"
  "204 101 0 196 193 0\n205 99 0 204 181 0\n206 97 0 205 178 0\n207 41 85 87 0 152 150 160 159 153 148 139 144 142 140 141 203 0\n208 86 87 -93 0 160 158 155 156 146 137 207 13 53 170 0\n209 85 -86 87 0 154 207 145 12 0\n210 -41 -93 0 13 53 73 170 0\n211 16 47 43 65 79 6 87 0 115 160 158 113 136 201 0\n212 17 -85 66 58 41 0 147 138 151 149 0\n213 -70 34 -95 0 58 59 60 172 0\n214 34 -79 -90 -105 0 80 77 188 187 213 171 64 65 66 67 71 163 68 70 172 69 0\n215 -79 -90 -105 0 214 3 4 15 17 103 0\n216 87 79 -93 0 210 158 159 160 208 209 212 52 170 14 94 112 114 211 0\n217 -17 54 58 -40 65 33 -87 0 55 11 10 8 7 96 94 157 93 0\n218 17 58 66 41 0 139 142 138 140 141 143 203 0\n219 58 -40 65 33 -87 41 0 55 218 97 217 0\n220 -58 -92 0 30 31 45 57 62 84 169 0\n221 65 -100 -107 0 197 195 183 192 189 190 179 177 215 216 174 161 191 186 184 220 210 170 219 0\n222 -65 -107 0 191 186 184 220 192 189 210 52 56 218 0\n223 -32 78 72 76 60 42 0 2 6 18 19 23 110 105 111 200 0\n224 -29 -95 0 1 4 5 16 172 0\n225 -56 49 -91 0 25 26 27 29 33 168 0\n226 54 -79 66 -107 0 204 191 185 75 225 72 192 189 210 186 184 220 218 222 221 180 173 137 157 95 0\n227 -79 66 -107 0 192 190 188 224 191 186 184 74 76 78 79 80 215 165 167 223 226 44 83 169 0\n228 -40 -107 0 204 222 221 180 173 191 186 184 220 192 189 210 9 219 0\n229 64 53 -63 -107 0 206 46 43 192 190 189 222 228 170 215 175 167 165 80 76 74 162 36 104 106 108 128 109 200 0\n230 -64 -63 -107 0 46 43 192 190 189 222 228 170 215 166 164 80 76 74 47 50 98 102 101 122 99 199 0\n231 -63 -107 0 206 192 190 189 222 228 170 215 175 76 43 46 230 162 229 37 0\n232 -61 64 -107 0 192 190 189 222 228 170 215 167 165 80 76 74 36 37 104 106 108 128 109 200 0\n233 62 64 -107 0 206 232 192 190 188 224 189 222 228 170 79 78 74 76 80 215 165 167 223 191 186 184 231 169 175 162 20 22 127 0\n234 -62 -107 0 192 190 188 224 189 222 228 170 79 78 74 76 80 215 165 167 223 191 186 184 231 169 85 82 81 227 54 164 77 75 187 39 40 41 91 89 90 213 92 171 63 0\n235 -107 0 192 189 190 222 228 170 74 76 80 215 164 166 234 233 47 48 50 98 102 101 122 99 199 0\n236 102 0 235 196 194 0\n237 100 0 236 182 0\n238 98 0 237 179 0\n239 89 0 238 176 0\n240 10 62 50 60 61 0 98 102 123 101 122 99 100 124 125 199 0\n241 -64 0 47 48 49 50 51 240 0\n242 12 60 53 0 241 104 106 129 131 108 128 109 107 130 200 0\n243 60 50 62 0 239 241 162 36 37 242 0\n244 13 61 57 0 241 116 117 134 119 132 118 133 135 202 0\n245 -60 0 34 35 38 244 0\n246 59 81 9 11 31 56 58 28 62 63 71 0 198 126 0\n247 62 0 245 243 20 21 22 24 32 43 61 120 127 121 246 0\n248 -61 0 247 42 0\n249 -13 0 247 245 86 88 242 0\n250 57 0 249 248 244 0\n251 -53 0 250 28 0\n252 -12 0 250 247 87 0\n253 0 252 251 245 242 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record003.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record003.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record003.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record003.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record003 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record003.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record003.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record003.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record003.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record003 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record003_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record003 Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record003_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record003_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00016.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00016.record005
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "aaa9a2e9661da8e8b8ae1ba1e4789e1783eaa6992e5651d68d8b4ad1b61d4749d1743da8d6338e9364cd32cc738ac6b86d1b16c3bc1e8791e2749ca785c970dd0f23c4f55152a28aa269461991615a0e0b81e546892a49951465454558342d0768350ca318d1324c5382c8b0ac1b81d0711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "12492492492492492492492492492492492492492249249249249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record005 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record005 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record005.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record005.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record005.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 40), (facetIndex 67), (facetIndex 71), (facetIndex 75), (facetIndex 76)]))
 (.leaf ([(facetIndex 41), (facetIndex 42), (facetIndex 43), (facetIndex 44), (facetIndex 45), (facetIndex 46), (facetIndex 47), (facetIndex 48), (facetIndex 49), (facetIndex 50), (facetIndex 51)])))
 (.branch 3
 (.leaf ([(facetIndex 59), (facetIndex 60), (facetIndex 61), (facetIndex 62), (facetIndex 65)]))
 (.branch 4
 (.leaf ([(facetIndex 66), (facetIndex 68), (facetIndex 69), (facetIndex 70), (facetIndex 73)]))
 (.leaf ([(facetIndex 72), (facetIndex 74), (facetIndex 77), (facetIndex 78), (facetIndex 79)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 82), (facetIndex 86), (facetIndex 88), (facetIndex 91), (facetIndex 92), (facetIndex 93)]))
 (.leaf ([(facetIndex 56), (facetIndex 58), (facetIndex 63), (facetIndex 64)])))
 (.branch 8
 (.leaf ([(facetIndex 81), (facetIndex 85), (facetIndex 89), (facetIndex 90)]))
 (.branch 9
 (.leaf ([(facetIndex 80), (facetIndex 83), (facetIndex 84), (facetIndex 87)]))
 (.leaf ([(facetIndex 52), (facetIndex 53), (facetIndex 54), (facetIndex 55), (facetIndex 57)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "55577585788578444004340333032662222696999911111111111z29;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def grouped2_0000 : List Nat := [0]
def grouped2_0001 : List Nat := [0, 1]
def grouped2_0002 : List Nat := [0, 1, 2, 3, 4]
def grouped2_0004 : List Nat := [1]
def grouped2_0005 : List Nat := [2]
def grouped2_0006 : List Nat := [2, 3, 4]
def grouped2_0007 : List Nat := [3]
def grouped2_0008 : List Nat := [3, 4]
def grouped2_0009 : List Nat := [4]
def grouped2_0010 : List Nat := [5]
def grouped2_0011 : List Nat := [5, 6]
def grouped2_0012 : List Nat := [5, 6, 7, 8, 9]
def grouped2_0013 : List Nat := [6]
def grouped2_0014 : List Nat := [7]
def grouped2_0015 : List Nat := [7, 8, 9]
def grouped2_0016 : List Nat := [8]
def grouped2_0017 : List Nat := [8, 9]
def grouped2_0018 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record005 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record005_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00016.record005" "{\"atoms\":[{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0017\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0012\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":10,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00016.record005" 80

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00016.record005" "{\"ridges\":[[14,35],[16,515],[19,13],[19,517],[24,145],[25,161],[26,641],[30,518],[35,146],[36,162],[37,642],[43,35],[45,515],[48,515],[49,517],[51,261],[51,515],[51,517],[52,35],[55,515],[57,35],[57,515],[62,515],[64,35],[65,35],[65,515],[69,13],[69,261],[70,517],[71,13],[76,261],[77,145],[78,145],[78,641],[79,161],[80,28],[83,28],[84,28],[84,518],[87,518],[91,146],[92,146],[92,642],[93,162]],\"owners\":[[19,517,[5,45,48,49,50,51],[70,73,74]],[49,517,[19,70,73,74],[5,45,48,50,51]],[51,517,[19,70,73,74],[5,45,48,49,50]],[70,517,[5,48,49,50,51],[19,45,73,74]],[30,518,[5,45,48,49,50,51],[84,87,88]],[84,518,[5,48,49,50,51],[30,45,87,88]],[87,518,[5,45,49,50,51],[30,48,84,88]],[24,145,[11,44,59,60,61,62],[68,77,78]],[77,145,[11,44,60,61,62],[24,59,68,78]],[78,145,[11,44,59,60,61],[24,62,68,77]],[35,146,[11,44,59,60,61,62],[82,91,92]],[91,146,[11,44,60,61,62],[35,59,82,92]],[92,146,[11,44,59,60,61],[35,62,82,91]],[25,161,[14,46,59,63,65],[72,77,79]],[79,161,[14,46,59,63],[25,65,72,77]],[36,162,[14,46,59,63,65],[86,91,93]],[93,162,[14,46,59,63],[36,65,86,91]],[26,641,[16,50,62,65],[74,78,79]],[78,641,[16,50,65],[26,62,74,79]],[37,642,[16,50,62,65],[88,92,93]],[92,642,[16,50,65],[37,62,88,93]],[80,28,[17,67,68,69,70],[28,66,81,82,83,84]],[83,28,[17,66,67,68,70],[28,69,80,81,82,84]],[84,28,[17,66,67,68,69],[28,70,80,81,82,83]]],\"edges\":[[23,[5,19,30,45,48,49,50,51,70,73,74,84,87,88]],[32,[11,24,35,44,59,60,61,62,68,77,78,82,91,92]],[36,[14,25,36,46,59,63,65,72,77,79,86,91,93]],[43,[16,26,37,50,62,65,74,78,79,88,92,93]]],\"groupings\":[2]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00016.record005" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00016.record005\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-21,-1],[-21,-19],[-23,-21],[-25,-21],[-26,-20],[-27,-2],[-27,-18],[-28,-2],[-28,-18],[-29,-14],[-29,-15],[-29,-16],[-29,-18],[-29,-19],[-29,-24],[-30,-26],[-30,-29],[-31,-15],[-31,-16],[-31,-20],[-31,-22],[-31,-24],[-31,-30],[-32,-17],[-32,-20],[-32,-23],[-32,-26],[-33,-18],[-33,-26],[-33,-27],[-33,-28],[-34,-18],[-34,-27],[-34,-28],[-34,-29],[-35,-18],[-35,-27],[-35,-28],[-35,-29],[-36,-18],[-36,-19],[-36,-27],[-36,-28],[-36,-29],[-37,-17],[-37,-20],[-37,-26],[-37,-31],[-38,-20],[-38,-23],[-39,-22],[-39,-31],[-40,-6],[-40,-17],[-41,-40],[-43,-17],[-43,-41],[-44,-29],[-44,-41],[-45,-17],[-45,-20],[-45,-21],[-45,-22],[-45,-40],[-46,-26],[-46,-42],[-47,-5],[-47,-40],[-47,-41],[-47,-43],[-47,-44],[-48,-29],[-48,-31],[-48,-42],[-49,-23],[-49,-33],[-50,-23],[-51,-26],[-51,-42],[-52,-19],[-52,-29],[-52,-42],[-53,-22],[-53,-31],[-53,-42],[-55,-27],[-55,-28],[-57,-29],[-58,-26],[-59,-31],[-59,-47],[-60,-29],[-60,-31],[-61,-26],[-62,-19],[-62,-29],[-63,-22],[-63,-31],[-6,-43,-45],[-3,-26,-38],[-17,-31,-38],[-26,-38,-39],[-25,-43,-50],[-4,-19,-31],[-4,-22,-29],[-4,-25,-31],[-25,-29,-39],[-25,-31,-36],[-6,1,19,22,23,24,25],[-23,6,44,47,48],[-25,6,44,47,48],[-44,1,22,23,24,25],[-10,1,19,22,23,24,25],[-57,1,22,23,24,25],[-59,1,19,23,24,25],[-7,2,18,33,34,35,36],[-51,2,18,34,35,36],[-52,2,18,33,34,35],[-11,2,18,33,34,35,36],[-61,2,18,34,35,36],[-62,2,18,33,34,35],[-8,3,20,33,37,39],[-53,3,20,33,37],[-12,3,20,33,37,39],[-63,3,20,33,37],[-9,4,24,36,39],[-52,4,24,39],[-13,4,24,36,39],[-62,4,24,39],[-54,5,41,42,43,44],[-56,5,40,41,42,44],[-57,5,40,41,42,43],[-64,14,41,45,49,50],[-65,15,16,17,18,19,20,21,22,23,24,25],[-66,33,34,35,36,39],[-67,40,42,43,44,47],[-68,46,48,51,52,53],[-69,30,32,37,38],[-70,54,56,57,59],[-71,26,27,28,29,31],[-72,64],[-72,65],[-73,67],[-73,68],[-74,66],[-74,73],[-75,72],[-75,74],[-76,69],[-77,70],[-77,71],[-78,77],[-79,76],[-79,78],[-80,75],[-80,79],[80],[1,6,10,19,22,23,24,25,44,47,48,57,59,60],[2,7,11,18,33,34,35,36,42,51,52,55,61,62],[3,8,12,20,33,37,39,46,51,53,58,61,63],[4,9,13,24,36,39,48,52,53,60,62,63]],\"atoms\":[{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"facet\",\"index\":82},{\"tag\":\"facet\",\"index\":83},{\"tag\":\"facet\",\"index\":84},{\"tag\":\"facet\",\"index\":86},{\"tag\":\"facet\",\"index\":87},{\"tag\":\"facet\",\"index\":88},{\"tag\":\"facet\",\"index\":91},{\"tag\":\"facet\",\"index\":92},{\"tag\":\"facet\",\"index\":93},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":47,\"b\":5},{\"tag\":\"incompatible\",\"a\":47,\"b\":45},{\"tag\":\"incompatible\",\"a\":49,\"b\":47},{\"tag\":\"incompatible\",\"a\":51,\"b\":47},{\"tag\":\"incompatible\",\"a\":52,\"b\":46},{\"tag\":\"incompatible\",\"a\":53,\"b\":11},{\"tag\":\"incompatible\",\"a\":53,\"b\":44},{\"tag\":\"incompatible\",\"a\":54,\"b\":11},{\"tag\":\"incompatible\",\"a\":54,\"b\":44},{\"tag\":\"incompatible\",\"a\":55,\"b\":40},{\"tag\":\"incompatible\",\"a\":55,\"b\":41},{\"tag\":\"incompatible\",\"a\":55,\"b\":42},{\"tag\":\"incompatible\",\"a\":55,\"b\":44},{\"tag\":\"incompatible\",\"a\":55,\"b\":45},{\"tag\":\"incompatible\",\"a\":55,\"b\":50},{\"tag\":\"incompatible\",\"a\":56,\"b\":52},{\"tag\":\"incompatible\",\"a\":56,\"b\":55},{\"tag\":\"incompatible\",\"a\":57,\"b\":41},{\"tag\":\"incompatible\",\"a\":57,\"b\":42},{\"tag\":\"incompatible\",\"a\":57,\"b\":46},{\"tag\":\"incompatible\",\"a\":57,\"b\":48},{\"tag\":\"incompatible\",\"a\":57,\"b\":50},{\"tag\":\"incompatible\",\"a\":57,\"b\":56},{\"tag\":\"incompatible\",\"a\":58,\"b\":43},{\"tag\":\"incompatible\",\"a\":58,\"b\":46},{\"tag\":\"incompatible\",\"a\":58,\"b\":49},{\"tag\":\"incompatible\",\"a\":58,\"b\":52},{\"tag\":\"incompatible\",\"a\":59,\"b\":44},{\"tag\":\"incompatible\",\"a\":59,\"b\":52},{\"tag\":\"incompatible\",\"a\":59,\"b\":53},{\"tag\":\"incompatible\",\"a\":59,\"b\":54},{\"tag\":\"incompatible\",\"a\":60,\"b\":44},{\"tag\":\"incompatible\",\"a\":60,\"b\":53},{\"tag\":\"incompatible\",\"a\":60,\"b\":54},{\"tag\":\"incompatible\",\"a\":60,\"b\":55},{\"tag\":\"incompatible\",\"a\":61,\"b\":44},{\"tag\":\"incompatible\",\"a\":61,\"b\":53},{\"tag\":\"incompatible\",\"a\":61,\"b\":54},{\"tag\":\"incompatible\",\"a\":61,\"b\":55},{\"tag\":\"incompatible\",\"a\":62,\"b\":44},{\"tag\":\"incompatible\",\"a\":62,\"b\":45},{\"tag\":\"incompatible\",\"a\":62,\"b\":53},{\"tag\":\"incompatible\",\"a\":62,\"b\":54},{\"tag\":\"incompatible\",\"a\":62,\"b\":55},{\"tag\":\"incompatible\",\"a\":63,\"b\":43},{\"tag\":\"incompatible\",\"a\":63,\"b\":46},{\"tag\":\"incompatible\",\"a\":63,\"b\":52},{\"tag\":\"incompatible\",\"a\":63,\"b\":57},{\"tag\":\"incompatible\",\"a\":64,\"b\":46},{\"tag\":\"incompatible\",\"a\":64,\"b\":49},{\"tag\":\"incompatible\",\"a\":65,\"b\":48},{\"tag\":\"incompatible\",\"a\":65,\"b\":57},{\"tag\":\"incompatible\",\"a\":66,\"b\":19},{\"tag\":\"incompatible\",\"a\":66,\"b\":43},{\"tag\":\"incompatible\",\"a\":67,\"b\":66},{\"tag\":\"incompatible\",\"a\":69,\"b\":43},{\"tag\":\"incompatible\",\"a\":69,\"b\":67},{\"tag\":\"incompatible\",\"a\":70,\"b\":55},{\"tag\":\"incompatible\",\"a\":70,\"b\":67},{\"tag\":\"incompatible\",\"a\":71,\"b\":43},{\"tag\":\"incompatible\",\"a\":71,\"b\":46},{\"tag\":\"incompatible\",\"a\":71,\"b\":47},{\"tag\":\"incompatible\",\"a\":71,\"b\":48},{\"tag\":\"incompatible\",\"a\":71,\"b\":66},{\"tag\":\"incompatible\",\"a\":72,\"b\":52},{\"tag\":\"incompatible\",\"a\":72,\"b\":68},{\"tag\":\"incompatible\",\"a\":73,\"b\":17},{\"tag\":\"incompatible\",\"a\":73,\"b\":66},{\"tag\":\"incompatible\",\"a\":73,\"b\":67},{\"tag\":\"incompatible\",\"a\":73,\"b\":69},{\"tag\":\"incompatible\",\"a\":73,\"b\":70},{\"tag\":\"incompatible\",\"a\":74,\"b\":55},{\"tag\":\"incompatible\",\"a\":74,\"b\":57},{\"tag\":\"incompatible\",\"a\":74,\"b\":68},{\"tag\":\"incompatible\",\"a\":75,\"b\":49},{\"tag\":\"incompatible\",\"a\":75,\"b\":59},{\"tag\":\"incompatible\",\"a\":76,\"b\":49},{\"tag\":\"incompatible\",\"a\":77,\"b\":52},{\"tag\":\"incompatible\",\"a\":77,\"b\":68},{\"tag\":\"incompatible\",\"a\":78,\"b\":45},{\"tag\":\"incompatible\",\"a\":78,\"b\":55},{\"tag\":\"incompatible\",\"a\":78,\"b\":68},{\"tag\":\"incompatible\",\"a\":79,\"b\":48},{\"tag\":\"incompatible\",\"a\":79,\"b\":57},{\"tag\":\"incompatible\",\"a\":79,\"b\":68},{\"tag\":\"incompatible\",\"a\":82,\"b\":53},{\"tag\":\"incompatible\",\"a\":82,\"b\":54},{\"tag\":\"incompatible\",\"a\":84,\"b\":55},{\"tag\":\"incompatible\",\"a\":86,\"b\":52},{\"tag\":\"incompatible\",\"a\":87,\"b\":57},{\"tag\":\"incompatible\",\"a\":87,\"b\":73},{\"tag\":\"incompatible\",\"a\":88,\"b\":55},{\"tag\":\"incompatible\",\"a\":88,\"b\":57},{\"tag\":\"incompatible\",\"a\":91,\"b\":52},{\"tag\":\"incompatible\",\"a\":92,\"b\":45},{\"tag\":\"incompatible\",\"a\":92,\"b\":55},{\"tag\":\"incompatible\",\"a\":93,\"b\":48},{\"tag\":\"incompatible\",\"a\":93,\"b\":57},{\"tag\":\"three\",\"ridge\":13,\"vertices\":[19,69,71]},{\"tag\":\"three\",\"ridge\":35,\"vertices\":[14,52,64]},{\"tag\":\"three\",\"ridge\":35,\"vertices\":[43,57,64]},{\"tag\":\"three\",\"ridge\":35,\"vertices\":[52,64,65]},{\"tag\":\"three\",\"ridge\":261,\"vertices\":[51,69,76]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[16,45,57]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[16,48,55]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[16,51,57]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[51,55,65]},{\"tag\":\"three\",\"ridge\":515,\"vertices\":[51,57,62]},{\"tag\":\"mate\",\"ridge\":517,\"a\":19,\"owners\":[5,45,48,49,50,51]},{\"tag\":\"mate\",\"ridge\":517,\"a\":49,\"owners\":[19,70,73,74]},{\"tag\":\"mate\",\"ridge\":517,\"a\":51,\"owners\":[19,70,73,74]},{\"tag\":\"mate\",\"ridge\":517,\"a\":70,\"owners\":[5,48,49,50,51]},{\"tag\":\"mate\",\"ridge\":518,\"a\":30,\"owners\":[5,45,48,49,50,51]},{\"tag\":\"mate\",\"ridge\":518,\"a\":84,\"owners\":[5,48,49,50,51]},{\"tag\":\"mate\",\"ridge\":518,\"a\":87,\"owners\":[5,45,49,50,51]},{\"tag\":\"mate\",\"ridge\":145,\"a\":24,\"owners\":[11,44,59,60,61,62]},{\"tag\":\"mate\",\"ridge\":145,\"a\":77,\"owners\":[11,44,60,61,62]},{\"tag\":\"mate\",\"ridge\":145,\"a\":78,\"owners\":[11,44,59,60,61]},{\"tag\":\"mate\",\"ridge\":146,\"a\":35,\"owners\":[11,44,59,60,61,62]},{\"tag\":\"mate\",\"ridge\":146,\"a\":91,\"owners\":[11,44,60,61,62]},{\"tag\":\"mate\",\"ridge\":146,\"a\":92,\"owners\":[11,44,59,60,61]},{\"tag\":\"mate\",\"ridge\":161,\"a\":25,\"owners\":[14,46,59,63,65]},{\"tag\":\"mate\",\"ridge\":161,\"a\":79,\"owners\":[14,46,59,63]},{\"tag\":\"mate\",\"ridge\":162,\"a\":36,\"owners\":[14,46,59,63,65]},{\"tag\":\"mate\",\"ridge\":162,\"a\":93,\"owners\":[14,46,59,63]},{\"tag\":\"mate\",\"ridge\":641,\"a\":26,\"owners\":[16,50,62,65]},{\"tag\":\"mate\",\"ridge\":641,\"a\":78,\"owners\":[16,50,65]},{\"tag\":\"mate\",\"ridge\":642,\"a\":37,\"owners\":[16,50,62,65]},{\"tag\":\"mate\",\"ridge\":642,\"a\":92,\"owners\":[16,50,65]},{\"tag\":\"mate\",\"ridge\":28,\"a\":80,\"owners\":[17,67,68,69,70]},{\"tag\":\"mate\",\"ridge\":28,\"a\":83,\"owners\":[17,66,67,68,70]},{\"tag\":\"mate\",\"ridge\":28,\"a\":84,\"owners\":[17,66,67,68,69]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[40,67,71,75,76],\"full_literals\":[-64,14,41,45,49,50]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[41,42,43,44,45,46,47,48,49,50,51],\"full_literals\":[-65,15,16,17,18,19,20,21,22,23,24,25]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[59,60,61,62,65],\"full_literals\":[-66,33,34,35,36,39]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[66,68,69,70,73],\"full_literals\":[-67,40,42,43,44,47]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[72,74,77,78,79],\"full_literals\":[-68,46,48,51,52,53]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[56,58,63,64],\"full_literals\":[-69,30,32,37,38]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[80,83,84,87],\"full_literals\":[-70,54,56,57,59]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[52,53,54,55,57],\"full_literals\":[-71,26,27,28,29,31]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-72,64,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-72,false,65],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0008\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-73,67,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0008\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-73,false,68],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-74,66,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-74,false,73],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-75,72,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-75,false,74],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-76,false,69],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0016\",\"right_name\":\"grouped2_0018\",\"joined_name\":\"grouped2_0017\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-77,70,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0016\",\"right_name\":\"grouped2_0018\",\"joined_name\":\"grouped2_0017\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-77,false,71],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-78,false,77],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0012\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-79,76,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0012\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-79,false,78],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-80,75,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-80,false,79],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":10,\"grouped\":true},{\"tag\":\"edge\",\"edge\":23,\"owners\":[5,19,30,45,48,49,50,51,70,73,74,84,87,88]},{\"tag\":\"edge\",\"edge\":32,\"owners\":[11,24,35,44,59,60,61,62,68,77,78,82,91,92]},{\"tag\":\"edge\",\"edge\":36,\"owners\":[14,25,36,46,59,63,65,72,77,79,86,91,93]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[16,26,37,50,62,65,74,78,79,88,92,93]}]}"
  "162 75 0 157 155 0\n163 79 0 157 156 0\n164 72 0 162 147 0\n165 74 0 162 148 0\n166 76 0 163 153 0\n167 78 0 163 154 0\n168 64 0 164 141 0\n169 65 0 164 142 0\n170 66 0 165 145 0\n171 73 0 165 146 0\n172 69 0 166 149 0\n173 77 0 167 152 0\n174 67 0 171 143 0\n175 68 0 171 144 0\n176 70 0 173 150 0\n177 71 0 173 151 0\n178 -41 42 0 174 55 57 59 69 136 0\n179 -42 0 175 66 74 79 82 85 137 0\n180 -41 0 179 178 0\n181 -28 0 179 8 9 31 34 38 43 87 117 120 118 119 121 116 159 0\n182 -26 0 172 5 16 27 29 47 65 78 89 94 138 102 100 124 122 125 123 160 0\n183 -45 -29 16 47 0 179 174 169 72 58 15 14 13 11 60 61 62 63 64 136 99 110 111 134 0\n184 -25 -50 -29 47 0 179 174 72 58 111 103 53 136 0\n185 -17 38 30 0 172 24 45 138 0\n186 -22 -29 0 96 92 81 72 44 15 51 83 97 105 126 128 161 0\n187 -25 45 -29 47 0 170 180 168 44 39 35 10 107 184 135 133 76 0\n188 -23 45 14 0 180 168 75 77 133 0\n189 -20 30 0 172 25 46 49 138 0\n190 -17 44 47 0 179 174 54 56 136 0\n191 -29 16 47 0 169 10 11 13 14 15 17 58 72 88 92 183 186 187 188 189 190 134 1 109 113 115 158 0\n192 -21 -31 47 0 93 90 73 22 21 1 2 3 4 109 113 114 112 158 0\n193 -18 39 0 170 28 32 36 40 135 0\n194 -17 -31 0 23 101 185 0\n195 -19 -31 0 98 93 84 73 52 22 41 80 95 104 126 128 161 0\n196 -25 -31 0 98 93 84 73 52 22 108 106 126 128 127 129 161 0\n197 -31 16 47 0 169 172 18 20 21 22 23 48 52 192 193 194 195 196 134 26 50 138 0\n198 -27 0 179 6 7 30 33 37 42 86 118 121 117 120 119 116 159 0\n199 -29 47 0 12 191 0\n200 47 0 182 181 198 177 199 140 19 197 0\n201 -5 0 200 67 0\n202 -40 0 200 68 0\n203 -43 0 200 70 0\n204 -44 0 200 71 0\n205 -59 0 200 91 0\n206 -56 0 201 179 202 204 180 131 0\n207 -54 0 201 203 179 180 204 130 0\n208 -57 0 203 201 202 179 180 132 0\n209 0 207 206 176 205 208 139 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record005.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record005.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record005.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record005.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record005 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record005.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record005.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record005.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record005.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record005 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record005_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record005_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record005_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record005_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record005_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record005_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record005_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record005 Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record005_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record005_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00016.record005_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00016.record005
