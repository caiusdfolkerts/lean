module
prelude
public meta import CertificateNumbers
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow16Part00029Data
public import GraphInputsRow16Part00029Frames
public import GraphInputsRow16Part00029Leaves
public import GraphInputsRow16Part00029Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record000
def vertexColumn : Fields := ⟨10, (certNat% 0)⟩
def kindColumn : Fields := ⟨3, (certNat% 1)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 2), (certNat% 3), 2568459162484736, 180143985094819840, (certNat% 4), 17867063951360]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [16254561396195328, 1689468335554560, 270215977642229760, (certNat% 5), (certNat% 6), 70368744177664]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 7), (certNat% 8), 55566139392, 3802111208849408, 43980465111040]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 9), (certNat% 6), 53085795778560, 1692698687832064, 281474976710656]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 10), (certNat% 11), (certNat% 5), 54043195528445952, (certNat% 12)]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 13), 288230513590665216, 5067649092419584, 143486267424768, 17592186044416]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 14), (certNat% 15), (certNat% 16), 36310546873581568, (certNat% 17), 19791209299968]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 18), (certNat% 19), (certNat% 20), 51539607552, (certNat% 21)]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 22), 30786325577728, (certNat% 17), 11258999068426240, 432345564227567616, (certNat% 23)]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 24), 88046829568, 9429411719806976, 288230376151711744, 34359738368]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 25), 88046829568, 11399736556781568, 288230376151711744, 34359738368]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 26), 88046829568, (certNat% 27), 11681211533492224, 34359738368, 486388759756013568]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c14 c11
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [13591217178673152, (certNat% 28), 563035852767232, 486388759823122432, (certNat% 8), 3802111208849408, 57483842289664]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c17 c10
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c18 c9
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c19 c8
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c20 c3
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c21 c2
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c22 c1
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c23 c0
  c24
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record000_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record008
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record008
def vertexColumn : Fields := ⟨10, (certNat% 29)⟩
def kindColumn : Fields := ⟨3, (certNat% 30)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 31), (certNat% 32), 63050394783186944, (certNat% 33), 42331197669376]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 34), (certNat% 35), 2269667146072064, 162129586585337856, (certNat% 36), 68719476736]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 37), 343597383680, 45035996273704960, 144124121607831552, 1165482325442560]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 38), 343597383680, (certNat% 39), (certNat% 40), 1165482325442560]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 41), 1165483399184384, (certNat% 42), (certNat% 43), (certNat% 44), 68987912192]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 45), 162129586585337856, (certNat% 36), (certNat% 46), 240518168576, (certNat% 47)]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 48), 144124121607831552, 615726511554560, (certNat% 49), 2252143411068928, 5915372557434880]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 50), 577094071001022464, 5910974510923776, (certNat% 51), 52776558133248]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 52), (certNat% 51), (certNat% 53), 52776558133248, 5915372557434880, 27021597764222976]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 54), 63050394783186944, (certNat% 55), 7107243161944064, (certNat% 56), 277025390592]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 57), (certNat% 58), 5985775661350912, (certNat% 59), (certNat% 60), 2269392268165120, 18014398509481984]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c14 c11
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c15 c8
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c16 c7
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c17 c6
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c18 c1
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c19 c0
  c20
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record008_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record008_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record008

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record032
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record032
def vertexColumn : Fields := ⟨10, (certNat% 61)⟩
def kindColumn : Fields := ⟨3, (certNat% 62)⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 63), 123147449794560, 74309393851613184, (certNat% 64), 6917529027641081856]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 65), 15942918602752, (certNat% 66), 4683743612465315840, 2305983746702049280, 17179869184]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [280315016773632, (certNat% 67), (certNat% 68), 6917529027641081856, 20266198625157120, 72057619807731712]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [(certNat% 69), (certNat% 70), 24769798218973184, 5260204364768739328, 110226040684544, 2305993092550885376, 26893877248]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c5 c0
  c6
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record032_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record032_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record032_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record032_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record032_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record032_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record032_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record032_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record032_matrix_checked B H)
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record032

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record001
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "9aa5a8e9a69999695a364b86e2785e0fa699663969665656558d52d1b49d1743dc8da398e9364e538ce4b8ad2b1ae1b26c5b0ee4751cc789ca719e1745c570dd0f23d86498961382e07985494951342d0758390e2348e1324c4b0ac1b41c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6da69b4924db4d3692492492492492492492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record001 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record001 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record001.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record001.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record001.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 27), (facetIndex 31), (facetIndex 56), (facetIndex 61)]))
 (.leaf ([(facetIndex 28), (facetIndex 34), (facetIndex 37), (facetIndex 52), (facetIndex 63), (facetIndex 76)])))
 (.branch 3
 (.leaf ([(facetIndex 54), (facetIndex 55), (facetIndex 57), (facetIndex 58)]))
 (.branch 4
 (.leaf ([(facetIndex 67), (facetIndex 68), (facetIndex 70), (facetIndex 71)]))
 (.leaf ([(facetIndex 32), (facetIndex 41), (facetIndex 42), (facetIndex 49), (facetIndex 50)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 35), (facetIndex 45), (facetIndex 47), (facetIndex 48), (facetIndex 51), (facetIndex 53)]))
 (.leaf ([(facetIndex 30), (facetIndex 33), (facetIndex 36), (facetIndex 38), (facetIndex 46)])))
 (.branch 8
 (.leaf ([(facetIndex 69), (facetIndex 74)]))
 (.branch 9
 (.leaf ([(facetIndex 39), (facetIndex 40), (facetIndex 43), (facetIndex 44)]))
 (.leaf ([(facetIndex 29)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "1070033733000100002202251544556588448861651640691z1c;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 59), (facetIndex 60), (facetIndex 62)]))
 (.leaf ([(facetIndex 64), (facetIndex 65), (facetIndex 66)])))
 (.branch 3
 (.leaf ([(facetIndex 72), (facetIndex 73), (facetIndex 75)]))
 (.leaf ([(facetIndex 77), (facetIndex 78), (facetIndex 79)]))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨2, sparse_nat% "fc8a0015z20;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 4
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

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
def grouped3_0019 : List Nat := [0]
def grouped3_0020 : List Nat := [0, 1]
def grouped3_0022 : List Nat := [1]
def grouped3_0023 : List Nat := [2]
def grouped3_0024 : List Nat := [2, 3]
def grouped3_0025 : List Nat := [3]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record001 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record001_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record001" "{\"atoms\":[{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0008\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0011\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0017\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0012\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0012\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record001" 76

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record001" "{\"ridges\":[[3,70],[10,529],[10,530],[12,545],[13,578],[17,69],[17,76],[23,70],[23,76],[32,530],[33,70],[35,546],[37,70],[38,578],[42,530],[45,545],[45,546],[46,577],[46,578],[47,529],[47,530],[47,545],[48,529],[48,530],[48,577],[50,529],[50,530],[51,545],[51,577],[51,578],[53,545],[54,44],[55,69],[56,28],[57,69],[58,44],[59,564],[60,596],[62,612],[64,568],[65,600],[66,616],[67,44],[68,70],[69,28],[70,70],[71,44],[72,546],[77,568],[78,600],[79,616]],\"owners\":[[17,69,[3,30,33,36,37,38,60,62],[55,57]],[55,69,[3,33,36,37,38,62],[17,30,57,60]],[57,69,[3,30,36,37,38,60],[17,33,55,62]],[3,70,[23,68,70,73,75],[30,33,36,37,38]],[23,70,[3,30,33,36,37,38,73,75],[68,70]],[33,70,[23,68,73],[3,30,36,37,38,70,75]],[37,70,[23,68,70,73,75],[3,30,33,36,38]],[68,70,[3,33,36,37,38,75],[23,30,70,73]],[70,70,[3,30,36,37,38,73],[23,33,68,75]],[10,529,[59,60,64,65],[32,42,47,48,50]],[47,529,[60,65],[10,32,42,48,50,59,64]],[48,529,[59,64],[10,32,42,47,50,60,65]],[50,529,[59,60,64,65],[10,32,42,47,48]],[10,530,[72,73,77,78],[32,42,47,48,50]],[32,530,[77,78],[10,42,47,48,50,72,73]],[42,530,[72,73],[10,32,47,48,50,77,78]],[47,530,[73,78],[10,32,42,48,50,72,77]],[48,530,[72,77],[10,32,42,47,50,73,78]],[50,530,[72,73,77,78],[10,32,42,47,48]],[12,545,[59,62,64,66],[35,45,47,51,53]],[45,545,[59,62],[12,35,47,51,53,64,66]],[47,545,[62,66],[12,35,45,51,53,59,64]],[51,545,[59,64],[12,35,45,47,53,62,66]],[53,545,[59,62,64,66],[12,35,45,47,51]],[35,546,[77,79],[12,45,47,51,53,72,75]],[45,546,[72,75],[12,35,47,51,53,77,79]],[72,546,[12,45,51,53,79],[35,47,75,77]],[46,577,[60,62],[13,38,48,51,65,66]],[48,577,[62,66],[13,38,46,51,60,65]],[51,577,[60,65],[13,38,46,48,62,66]],[13,578,[73,75,78,79],[38,46,48,51]],[38,578,[78,79],[13,46,48,51,73,75]],[46,578,[73,75],[13,38,48,51,78,79]],[51,578,[73,78],[13,38,46,48,75,79]],[56,28,[21,67,68],[15,54,55,69]],[69,28,[15,54,55],[21,56,67,68]],[54,44,[22,70,71],[16,57,58,67]],[58,44,[22,67,70],[16,54,57,71]],[67,44,[16,57,58],[22,54,70,71]],[71,44,[16,54,57],[22,58,67,70]],[17,76,[23,68,70],[55,57]],[23,76,[17,55,57],[68,70]],[59,564,[72],[]],[60,596,[73],[]],[62,612,[75],[]],[64,568,[77],[]],[77,568,[64],[]],[65,600,[78],[]],[78,600,[65],[]],[66,616,[79],[]],[79,616,[66],[]]],\"edges\":[[20,[3,17,23,30,33,36,37,38,55,57,60,62,68,70,73,75]],[34,[10,32,42,47,48,50,59,60,64,65,72,73,77,78]],[38,[12,35,45,47,51,53,59,62,64,66,72,75,77,79]],[41,[13,38,46,48,51,60,62,65,66,73,75,78,79]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record001" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record001\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-12,-1],[-13,-12],[-15,-13],[-16,-12],[-17,-16],[-18,-12],[-18,-15],[-18,-17],[-19,-12],[-20,-12],[-20,-15],[-20,-17],[-24,-20],[-25,-3],[-25,-13],[-25,-20],[-25,-22],[-26,-13],[-27,-16],[-28,-16],[-28,-25],[-29,-7],[-30,-6],[-30,-29],[-32,-5],[-32,-11],[-32,-16],[-32,-29],[-32,-30],[-32,-31],[-33,-30],[-39,-13],[-40,-16],[-40,-38],[-41,-10],[-42,-9],[-42,-30],[-42,-41],[-44,-8],[-44,-11],[-44,-16],[-44,-41],[-44,-42],[-44,-43],[-45,-33],[-45,-42],[-46,-37],[-47,-34],[-47,-37],[-47,-46],[-48,-14],[-48,-36],[-49,-46],[-49,-47],[-50,-40],[-51,-13],[-51,-30],[-51,-38],[-51,-40],[-51,-42],[-51,-50],[-52,-16],[-52,-38],[-52,-50],[-52,-51],[-7,1,13,16,18,19,20,35,37],[-30,1,16,18,19,20,37],[-32,1,13,18,19,20,35],[-1,10,42,44,47,49],[-10,1,13,16,18,19,20,47,49],[-16,10,42,47],[-19,10,42,44,47,49],[-42,1,16,18,19,20,49],[-44,1,13,18,19,20,47],[-2,34,35,38,39],[-24,35,39],[-25,34,38],[-26,34,35,38,39],[-2,46,47,50,51],[-15,50,51],[-21,46,47],[-24,47,51],[-25,46,50],[-26,46,47,50,51],[-3,34,37,38,40],[-22,34,37],[-24,37,40],[-27,34,38],[-28,34,37,38,40],[-17,50,52],[-22,46,49],[-46,3,22,27,28,52],[-23,35,37],[-25,37,40],[-27,35,39],[-4,47,49,51,52],[-20,51,52],[-23,47,49],[-27,47,51],[-31,8,41,42],[-43,5,29,30],[-29,9,44,45],[-33,9,41,44],[-41,6,32,33],[-45,6,29,32],[-7,10,42,44],[-10,7,30,32],[-34,46],[-35,47],[-37,49],[-38,50],[-50,38],[-39,51],[-51,39],[-40,52],[-52,40],[-53,11,14,31,36],[-54,29,30,32,33],[-55,41,42,44,45],[-56,17,22,24,25,27,28],[-57,13,16,18,20,23],[-58,43,48],[-59,12],[-60,53],[-61,55],[-62,54],[-62,61],[-63,60],[-63,62],[-64,56],[-64,57],[-65,59],[-66,58,65],[-67,65],[-68,64,66],[-69,64,67],[-70,63,69],[-70,68],[70],[-38,71],[-39,71],[-40,71],[-46,72],[-47,72],[-49,72],[-73,50,51,52],[-50,73],[-51,73],[-52,73],[-71,74],[-75,73],[-72,-73,75],[-74,-75,76],[-76],[1,7,10,13,16,18,19,20,30,32,35,37,42,44,47,49],[2,15,21,24,25,26,34,35,38,39,46,47,50,51],[3,17,22,24,27,28,34,37,38,40,46,49,50,52],[4,20,23,25,27,35,37,39,40,47,49,51,52]],\"atoms\":[{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":9,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":29,\"b\":3},{\"tag\":\"incompatible\",\"a\":30,\"b\":29},{\"tag\":\"incompatible\",\"a\":32,\"b\":30},{\"tag\":\"incompatible\",\"a\":33,\"b\":29},{\"tag\":\"incompatible\",\"a\":35,\"b\":33},{\"tag\":\"incompatible\",\"a\":36,\"b\":29},{\"tag\":\"incompatible\",\"a\":36,\"b\":32},{\"tag\":\"incompatible\",\"a\":36,\"b\":35},{\"tag\":\"incompatible\",\"a\":37,\"b\":29},{\"tag\":\"incompatible\",\"a\":38,\"b\":29},{\"tag\":\"incompatible\",\"a\":38,\"b\":32},{\"tag\":\"incompatible\",\"a\":38,\"b\":35},{\"tag\":\"incompatible\",\"a\":47,\"b\":38},{\"tag\":\"incompatible\",\"a\":48,\"b\":12},{\"tag\":\"incompatible\",\"a\":48,\"b\":30},{\"tag\":\"incompatible\",\"a\":48,\"b\":38},{\"tag\":\"incompatible\",\"a\":48,\"b\":45},{\"tag\":\"incompatible\",\"a\":50,\"b\":30},{\"tag\":\"incompatible\",\"a\":51,\"b\":33},{\"tag\":\"incompatible\",\"a\":53,\"b\":33},{\"tag\":\"incompatible\",\"a\":53,\"b\":48},{\"tag\":\"incompatible\",\"a\":54,\"b\":17},{\"tag\":\"incompatible\",\"a\":55,\"b\":16},{\"tag\":\"incompatible\",\"a\":55,\"b\":54},{\"tag\":\"incompatible\",\"a\":57,\"b\":15},{\"tag\":\"incompatible\",\"a\":57,\"b\":27},{\"tag\":\"incompatible\",\"a\":57,\"b\":33},{\"tag\":\"incompatible\",\"a\":57,\"b\":54},{\"tag\":\"incompatible\",\"a\":57,\"b\":55},{\"tag\":\"incompatible\",\"a\":57,\"b\":56},{\"tag\":\"incompatible\",\"a\":58,\"b\":55},{\"tag\":\"incompatible\",\"a\":65,\"b\":30},{\"tag\":\"incompatible\",\"a\":66,\"b\":33},{\"tag\":\"incompatible\",\"a\":66,\"b\":64},{\"tag\":\"incompatible\",\"a\":67,\"b\":23},{\"tag\":\"incompatible\",\"a\":68,\"b\":22},{\"tag\":\"incompatible\",\"a\":68,\"b\":55},{\"tag\":\"incompatible\",\"a\":68,\"b\":67},{\"tag\":\"incompatible\",\"a\":70,\"b\":21},{\"tag\":\"incompatible\",\"a\":70,\"b\":27},{\"tag\":\"incompatible\",\"a\":70,\"b\":33},{\"tag\":\"incompatible\",\"a\":70,\"b\":67},{\"tag\":\"incompatible\",\"a\":70,\"b\":68},{\"tag\":\"incompatible\",\"a\":70,\"b\":69},{\"tag\":\"incompatible\",\"a\":71,\"b\":58},{\"tag\":\"incompatible\",\"a\":71,\"b\":68},{\"tag\":\"incompatible\",\"a\":72,\"b\":62},{\"tag\":\"incompatible\",\"a\":73,\"b\":59},{\"tag\":\"incompatible\",\"a\":73,\"b\":62},{\"tag\":\"incompatible\",\"a\":73,\"b\":72},{\"tag\":\"incompatible\",\"a\":74,\"b\":31},{\"tag\":\"incompatible\",\"a\":74,\"b\":61},{\"tag\":\"incompatible\",\"a\":75,\"b\":72},{\"tag\":\"incompatible\",\"a\":75,\"b\":73},{\"tag\":\"incompatible\",\"a\":77,\"b\":66},{\"tag\":\"incompatible\",\"a\":78,\"b\":30},{\"tag\":\"incompatible\",\"a\":78,\"b\":55},{\"tag\":\"incompatible\",\"a\":78,\"b\":64},{\"tag\":\"incompatible\",\"a\":78,\"b\":66},{\"tag\":\"incompatible\",\"a\":78,\"b\":68},{\"tag\":\"incompatible\",\"a\":78,\"b\":77},{\"tag\":\"incompatible\",\"a\":79,\"b\":33},{\"tag\":\"incompatible\",\"a\":79,\"b\":64},{\"tag\":\"incompatible\",\"a\":79,\"b\":77},{\"tag\":\"incompatible\",\"a\":79,\"b\":78},{\"tag\":\"mate\",\"ridge\":69,\"a\":17,\"owners\":[3,30,33,36,37,38,60,62]},{\"tag\":\"mate\",\"ridge\":69,\"a\":55,\"owners\":[3,33,36,37,38,62]},{\"tag\":\"mate\",\"ridge\":69,\"a\":57,\"owners\":[3,30,36,37,38,60]},{\"tag\":\"mate\",\"ridge\":70,\"a\":3,\"owners\":[23,68,70,73,75]},{\"tag\":\"mate\",\"ridge\":70,\"a\":23,\"owners\":[3,30,33,36,37,38,73,75]},{\"tag\":\"mate\",\"ridge\":70,\"a\":33,\"owners\":[23,68,73]},{\"tag\":\"mate\",\"ridge\":70,\"a\":37,\"owners\":[23,68,70,73,75]},{\"tag\":\"mate\",\"ridge\":70,\"a\":68,\"owners\":[3,33,36,37,38,75]},{\"tag\":\"mate\",\"ridge\":70,\"a\":70,\"owners\":[3,30,36,37,38,73]},{\"tag\":\"mate\",\"ridge\":529,\"a\":10,\"owners\":[59,60,64,65]},{\"tag\":\"mate\",\"ridge\":529,\"a\":47,\"owners\":[60,65]},{\"tag\":\"mate\",\"ridge\":529,\"a\":48,\"owners\":[59,64]},{\"tag\":\"mate\",\"ridge\":529,\"a\":50,\"owners\":[59,60,64,65]},{\"tag\":\"mate\",\"ridge\":530,\"a\":10,\"owners\":[72,73,77,78]},{\"tag\":\"mate\",\"ridge\":530,\"a\":32,\"owners\":[77,78]},{\"tag\":\"mate\",\"ridge\":530,\"a\":42,\"owners\":[72,73]},{\"tag\":\"mate\",\"ridge\":530,\"a\":47,\"owners\":[73,78]},{\"tag\":\"mate\",\"ridge\":530,\"a\":48,\"owners\":[72,77]},{\"tag\":\"mate\",\"ridge\":530,\"a\":50,\"owners\":[72,73,77,78]},{\"tag\":\"mate\",\"ridge\":545,\"a\":12,\"owners\":[59,62,64,66]},{\"tag\":\"mate\",\"ridge\":545,\"a\":45,\"owners\":[59,62]},{\"tag\":\"mate\",\"ridge\":545,\"a\":47,\"owners\":[62,66]},{\"tag\":\"mate\",\"ridge\":545,\"a\":51,\"owners\":[59,64]},{\"tag\":\"mate\",\"ridge\":545,\"a\":53,\"owners\":[59,62,64,66]},{\"tag\":\"mate\",\"ridge\":546,\"a\":35,\"owners\":[77,79]},{\"tag\":\"mate\",\"ridge\":546,\"a\":45,\"owners\":[72,75]},{\"tag\":\"mate\",\"ridge\":546,\"a\":72,\"owners\":[12,45,51,53,79]},{\"tag\":\"mate\",\"ridge\":577,\"a\":46,\"owners\":[60,62]},{\"tag\":\"mate\",\"ridge\":577,\"a\":48,\"owners\":[62,66]},{\"tag\":\"mate\",\"ridge\":577,\"a\":51,\"owners\":[60,65]},{\"tag\":\"mate\",\"ridge\":578,\"a\":13,\"owners\":[73,75,78,79]},{\"tag\":\"mate\",\"ridge\":578,\"a\":38,\"owners\":[78,79]},{\"tag\":\"mate\",\"ridge\":578,\"a\":46,\"owners\":[73,75]},{\"tag\":\"mate\",\"ridge\":578,\"a\":51,\"owners\":[73,78]},{\"tag\":\"mate\",\"ridge\":28,\"a\":56,\"owners\":[21,67,68]},{\"tag\":\"mate\",\"ridge\":28,\"a\":69,\"owners\":[15,54,55]},{\"tag\":\"mate\",\"ridge\":44,\"a\":54,\"owners\":[22,70,71]},{\"tag\":\"mate\",\"ridge\":44,\"a\":58,\"owners\":[22,67,70]},{\"tag\":\"mate\",\"ridge\":44,\"a\":67,\"owners\":[16,57,58]},{\"tag\":\"mate\",\"ridge\":44,\"a\":71,\"owners\":[16,54,57]},{\"tag\":\"mate\",\"ridge\":76,\"a\":17,\"owners\":[23,68,70]},{\"tag\":\"mate\",\"ridge\":76,\"a\":23,\"owners\":[17,55,57]},{\"tag\":\"mate\",\"ridge\":564,\"a\":59,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":596,\"a\":60,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":612,\"a\":62,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":568,\"a\":64,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":568,\"a\":77,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":600,\"a\":65,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":600,\"a\":78,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":616,\"a\":66,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":616,\"a\":79,\"owners\":[66]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[27,31,56,61],\"full_literals\":[-53,11,14,31,36]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[54,55,57,58],\"full_literals\":[-54,29,30,32,33]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[67,68,70,71],\"full_literals\":[-55,41,42,44,45]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[35,45,47,48,51,53],\"full_literals\":[-56,17,22,24,25,27,28]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[30,33,36,38,46],\"full_literals\":[-57,13,16,18,20,23]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[69,74],\"full_literals\":[-58,43,48]},{\"tag\":\"group_or\",\"kind\":2,\"index\":9,\"members\":[29],\"full_literals\":[-59,12]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-60,53,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped2_0007\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0008\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-61,55,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-62,54,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0008\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-62,false,61],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-63,60,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-63,false,62],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-64,56,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped2_0010\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0011\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-64,false,57],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped2_0016\",\"right_name\":\"grouped2_0018\",\"joined_name\":\"grouped2_0017\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-65,false,59],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-66,58,65],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0017\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-67,false,65],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0012\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-68,64,66],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped2_0011\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0012\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-69,64,67],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-70,63,69],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0012\",\"joined_name\":\"groupKind2\",\"a\":5,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-70,false,68],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":64,\"full_literals\":[-38,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":65,\"full_literals\":[-39,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":66,\"full_literals\":[-40,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":72,\"full_literals\":[-46,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":73,\"full_literals\":[-47,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":75,\"full_literals\":[-49,72]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[77,78,79],\"full_literals\":[-73,50,51,52]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":77,\"full_literals\":[-50,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":78,\"full_literals\":[-51,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":79,\"full_literals\":[-52,73]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-71,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-75,false,73],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-72,-73,75],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-74,-75,76],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":20,\"owners\":[3,17,23,30,33,36,37,38,55,57,60,62,68,70,73,75]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[10,32,42,47,48,50,59,60,64,65,72,73,77,78]},{\"tag\":\"edge\",\"edge\":38,\"owners\":[12,35,45,47,51,53,59,62,64,66,72,75,77,79]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[13,38,46,48,51,60,62,65,66,73,75,78,79]}]}"
  "159 68 0 139 138 0\n160 -75 0 154 151 153 150 140 141 142 112 114 116 146 0\n161 -12 72 0 145 110 144 109 1 2 4 6 9 10 66 70 68 74 67 73 155 0\n162 10 19 30 32 42 44 13 16 18 20 72 0 145 110 144 109 69 106 155 0\n163 -10 30 32 42 44 -62 0 127 125 126 35 107 119 22 45 118 0\n164 30 32 42 44 13 16 18 20 72 0 139 161 123 132 134 144 145 98 121 131 136 137 129 163 72 162 0\n165 32 42 44 13 16 18 20 72 0 139 161 123 132 134 144 145 98 121 131 136 137 129 127 125 164 23 24 31 104 105 119 0\n166 -32 -53 -58 0 25 26 28 29 30 101 122 51 52 117 0\n167 44 13 16 18 20 72 0 139 159 161 123 132 144 145 98 121 131 135 133 134 136 137 128 124 166 129 126 165 36 37 38 46 102 103 118 0\n168 13 16 18 20 72 0 159 139 161 123 132 134 144 145 98 121 131 135 136 133 137 128 124 167 39 40 42 43 44 100 122 51 52 117 0\n169 52 40 20 25 27 51 37 39 23 47 35 49 0 158 96 0\n170 52 -13 20 72 0 144 109 32 95 56 15 145 98 110 115 169 0\n171 -13 20 72 0 144 109 143 108 81 3 15 18 32 56 76 170 63 64 75 156 0\n172 51 -16 20 72 0 145 110 33 94 62 19 144 98 109 113 169 0\n173 -16 20 72 0 139 161 123 132 134 145 110 143 91 144 5 19 20 27 33 41 87 94 120 130 136 137 129 172 57 60 163 71 0\n174 -51 17 72 0 145 110 143 108 91 58 59 61 65 88 89 85 87 157 0\n175 40 20 72 0 144 171 173 168 8 174 99 113 145 98 110 109 116 94 169 0\n176 20 72 0 144 109 143 108 81 171 173 168 7 8 174 113 82 175 34 55 77 78 75 156 0\n177 72 0 143 144 81 108 109 176 11 12 13 16 174 97 113 63 64 78 75 156 0\n178 -73 0 177 160 152 0\n179 -50 0 178 147 0\n180 -51 0 178 148 0\n181 -52 0 178 149 0\n182 -15 0 179 180 80 0\n183 -17 0 179 181 90 0\n184 -38 0 179 111 0\n185 -39 0 180 113 0\n186 -40 0 181 115 0\n187 -20 0 181 180 97 0\n188 46 25 47 0 185 184 179 180 182 82 109 81 108 84 79 156 0\n189 25 47 0 180 186 185 181 187 99 109 188 47 53 93 169 0\n190 47 0 180 179 181 99 189 14 17 21 83 92 0\n191 -34 0 190 48 0\n192 -37 0 190 49 0\n193 -46 0 190 50 0\n194 -49 0 190 54 0\n195 -22 0 191 192 86 0\n196 -27 0 191 184 88 0\n197 -28 0 191 184 192 186 89 0\n198 -3 0 192 184 191 186 85 0\n199 -24 0 192 186 87 0\n200 0 198 195 183 199 196 181 179 192 184 186 193 191 194 197 157 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record001.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record001.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record001.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record001.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record001 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record001.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record001.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record001.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record001.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record001 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record001_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record001 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record001_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record001_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record006
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "1aa96a666598e93a2e2b91e1783e6a659995956364d8b4ad4745d0f6a368e6364e5354f0b62e4b4acab86c5b0ed8791cc789c6745c970de0f43c8f13e2a468a61582e07a29464a51542d0758390e2328d1314e0b42c2b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "db6da4926db6d2492492492492492492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record006 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record006 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record006.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record006.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record006.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 59), (facetIndex 60)]))
 (.leaf ([(facetIndex 58), (facetIndex 61)])))
 (.branch 3
 (.leaf ([(facetIndex 62), (facetIndex 69)]))
 (.leaf ([(facetIndex 63), (facetIndex 70)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 71)]))
 (.leaf ([(facetIndex 72)])))
 (.branch 7
 (.leaf ([(facetIndex 73)]))
 (.leaf ([(facetIndex 74)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1f58d000068804z2b;"⟩
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
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record006 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record006_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record006" "{\"atoms\":[{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0006\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0002\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0010\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record006" 42

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record006" "{\"ridges\":[[13,577],[13,578],[14,386],[37,577],[37,578],[38,385],[44,577],[44,578],[45,386],[48,577],[48,578],[49,386],[50,577],[50,578],[51,386],[58,588],[59,396],[60,404],[61,612],[62,600],[69,588],[71,404],[72,612],[73,600],[74,424]],\"owners\":[[13,577,[58,61,62],[37,44,48,50]],[37,577,[62],[13,44,48,50,58,61]],[44,577,[61],[13,37,48,50,58,62]],[48,577,[58,61],[13,37,44,50,62]],[50,577,[58,62],[13,37,44,48,61]],[13,578,[69,72,73],[37,44,48,50]],[37,578,[73],[13,44,48,50,69,72]],[44,578,[72],[13,37,48,50,69,73]],[48,578,[69,72],[13,37,44,50,73]],[50,578,[69,73],[13,37,44,48,72]],[38,385,[63],[14,45,49,51,59,60]],[14,386,[70,71,74],[38,45,49,51]],[45,386,[71],[14,38,49,51,70,74]],[49,386,[70,74],[14,38,45,51,71]],[51,386,[70,71],[14,38,45,49,74]],[58,588,[69],[]],[69,588,[58],[]],[59,396,[70],[]],[60,404,[71],[]],[71,404,[60],[]],[61,612,[72],[]],[72,612,[61],[]],[62,600,[73],[]],[73,600,[62],[]],[74,424,[63],[]]],\"edges\":[[41,[13,37,44,48,50,58,61,62,69,72,73]],[42,[14,38,45,49,51,59,60,63,70,71,74]]],\"groupings\":[3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record006" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record006\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,11,14,15],[-3,15],[-5,14],[-7,11,14],[-9,11,15],[-1,17,20,21],[-3,21],[-5,20],[-7,17,20],[-9,17,21],[-4,16],[-2,18,19,22],[-6,19],[-8,18,22],[-10,18,19],[-11,17],[-17,11],[-12,18],[-13,19],[-19,13],[-14,20],[-20,14],[-15,21],[-21,15],[-22,16],[-13,23],[-11,24],[-14,24],[-25,15,17],[-15,25],[-17,25],[-16,26],[-18,26],[-27,19],[-19,27],[-28,20],[-20,28],[-21,29],[-24,30],[-23,-24,31],[-26,32],[-33,25],[-25,32],[-25,-26,33],[-32,34],[-33,35],[-30,34],[-30,-32,35],[-30,-33,36],[-31,35],[-37,27,28],[-28,37],[-27,37],[-27,-28,38],[-29,39],[-39,40],[-37,40],[-37,-39,41],[-38,41],[-34,-41,42],[-35,-40,42],[-36,42],[-42],[1,3,5,7,9,11,14,15,17,20,21],[2,4,6,8,10,12,13,16,18,19,22]],\"atoms\":[{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":577,\"a\":13,\"owners\":[58,61,62]},{\"tag\":\"mate\",\"ridge\":577,\"a\":37,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":577,\"a\":44,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":577,\"a\":48,\"owners\":[58,61]},{\"tag\":\"mate\",\"ridge\":577,\"a\":50,\"owners\":[58,62]},{\"tag\":\"mate\",\"ridge\":578,\"a\":13,\"owners\":[69,72,73]},{\"tag\":\"mate\",\"ridge\":578,\"a\":37,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":578,\"a\":44,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":578,\"a\":48,\"owners\":[69,72]},{\"tag\":\"mate\",\"ridge\":578,\"a\":50,\"owners\":[69,73]},{\"tag\":\"mate\",\"ridge\":385,\"a\":38,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":386,\"a\":14,\"owners\":[70,71,74]},{\"tag\":\"mate\",\"ridge\":386,\"a\":45,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":386,\"a\":49,\"owners\":[70,74]},{\"tag\":\"mate\",\"ridge\":386,\"a\":51,\"owners\":[70,71]},{\"tag\":\"mate\",\"ridge\":588,\"a\":58,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":588,\"a\":69,\"owners\":[58]},{\"tag\":\"mate\",\"ridge\":396,\"a\":59,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":404,\"a\":60,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":404,\"a\":71,\"owners\":[60]},{\"tag\":\"mate\",\"ridge\":612,\"a\":61,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":612,\"a\":72,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":600,\"a\":62,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":600,\"a\":73,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":424,\"a\":74,\"owners\":[63]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":60,\"full_literals\":[-13,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":58,\"full_literals\":[-11,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":61,\"full_literals\":[-14,24]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[62,69],\"full_literals\":[-25,15,17]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":62,\"full_literals\":[-15,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":69,\"full_literals\":[-17,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":63,\"full_literals\":[-16,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":70,\"full_literals\":[-18,26]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[71],\"full_literals\":[-27,19]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":71,\"full_literals\":[-19,27]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[72],\"full_literals\":[-28,20]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":72,\"full_literals\":[-20,28]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":73,\"full_literals\":[-21,29]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-24,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-23,-24,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-26,32],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-33,25,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-25,false,32],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0005\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"grouped3_0006\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-25,-26,33],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-32,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-33,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-30,false,34],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-30,-32,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-30,-33,36],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0006\",\"joined_name\":\"grouped3_0002\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-31,false,35],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-37,27,28],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-28,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-27,false,37],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-27,-28,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-29,false,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-39,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-37,false,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-37,-39,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0009\",\"right_name\":\"grouped3_0013\",\"joined_name\":\"grouped3_0010\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-38,false,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-34,-41,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-35,-40,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0002\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-36,false,42],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":41,\"owners\":[13,37,44,48,50,58,61,62,69,72,73]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[14,38,45,49,51,59,60,63,70,71,74]}]}"
  "66 -36 0 63 62 0\n67 34 0 45 47 43 39 30 31 27 28 2 24 1 4 5 3 22 64 0\n68 -41 0 67 63 60 0\n69 -38 0 68 59 0\n70 26 19 0 19 13 32 33 11 25 18 15 12 14 65 0\n71 37 33 0 52 53 37 35 8 21 70 44 30 31 2 24 16 9 6 10 64 0\n72 27 35 0 46 71 35 51 70 36 41 22 48 28 39 0\n73 35 0 68 69 46 50 71 58 55 38 7 23 72 34 54 20 37 26 8 21 40 27 1 4 5 17 64 0\n74 -40 0 73 63 61 0\n75 -39 0 74 56 0\n76 -37 0 74 57 0\n77 -29 0 75 55 0\n78 33 0 76 71 0\n79 -21 0 77 38 0\n80 25 0 78 42 0\n81 -30 0 78 66 49 0\n82 -15 0 79 23 0\n83 17 0 80 82 29 0\n84 -24 0 81 39 0\n85 11 0 83 17 0\n86 0 85 84 27 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record006.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record006.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record006.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record006.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record006 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record006.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record006.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record006.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record006.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record006 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record006_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record006_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record006_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record006_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record006_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record006_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record006_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record006 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record006_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record006_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record006_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record006

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record007
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "8f1b2999962d98e93a2e4785e0f9b18e6a5995958d4b56362d8751d1743d68e6364d332cd8b92d4b8ac5b0ed8791cc789c6745c9715e0f43c8f0be4c468a60d84e07a4946645894a50d60d1341d60ca344c3342c4b06c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6d34d24da4d269249349249a492492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record007 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record007 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record007.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record007.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record007.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 30), (facetIndex 37), (facetIndex 43), (facetIndex 51), (facetIndex 67)]))
 (.leaf ([(facetIndex 44), (facetIndex 46), (facetIndex 47), (facetIndex 49)])))
 (.branch 3
 (.leaf ([(facetIndex 35), (facetIndex 54), (facetIndex 56), (facetIndex 57), (facetIndex 59), (facetIndex 60)]))
 (.leaf ([(facetIndex 63), (facetIndex 64), (facetIndex 65)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 27), (facetIndex 32), (facetIndex 34), (facetIndex 45), (facetIndex 69)]))
 (.leaf ([(facetIndex 29), (facetIndex 39), (facetIndex 40), (facetIndex 42)])))
 (.branch 7
 (.leaf ([(facetIndex 50), (facetIndex 52), (facetIndex 53)]))
 (.leaf ([(facetIndex 28), (facetIndex 31), (facetIndex 33), (facetIndex 36), (facetIndex 38)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "2001b6024120b6188261145bc753ce2f8z14;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 41), (facetIndex 48)]))
 (.leaf ([(facetIndex 55), (facetIndex 58)])))
 (.branch 3
 (.leaf ([(facetIndex 61), (facetIndex 66)]))
 (.leaf ([(facetIndex 62), (facetIndex 70)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 68)]))
 (.leaf ([(facetIndex 71)])))
 (.branch 7
 (.leaf ([(facetIndex 72)]))
 (.leaf ([(facetIndex 73)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "3eac40800d00402z29;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3]
def grouped2_0005 : List Nat := [3]
def grouped2_0006 : List Nat := [4, 5]
def grouped2_0007 : List Nat := [4, 5, 6, 7]
def grouped2_0008 : List Nat := [6]
def grouped2_0009 : List Nat := [6, 7]
def grouped2_0010 : List Nat := [7]
def grouped3_0011 : List Nat := [0]
def grouped3_0012 : List Nat := [0, 1]
def grouped3_0013 : List Nat := [0, 1, 2, 3]
def grouped3_0015 : List Nat := [1]
def grouped3_0016 : List Nat := [2]
def grouped3_0017 : List Nat := [2, 3]
def grouped3_0018 : List Nat := [3]
def grouped3_0019 : List Nat := [4]
def grouped3_0020 : List Nat := [4, 5]
def grouped3_0021 : List Nat := [4, 5, 6, 7]
def grouped3_0022 : List Nat := [5]
def grouped3_0023 : List Nat := [6]
def grouped3_0024 : List Nat := [6, 7]
def grouped3_0025 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record007 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record007_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record007" "{\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0020\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record007" 51

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record007" "{\"ridges\":[[11,386],[17,548],[35,545],[38,385],[41,554],[44,386],[47,386],[48,610],[49,386],[54,548],[55,396],[57,548],[58,404],[59,548],[60,548],[61,568],[66,554],[68,396],[71,610],[72,432],[73,568]],\"owners\":[[38,385,[62],[11,44,47,49,55,58]],[11,386,[68,70,72],[38,44,47,49]],[44,386,[70,72],[11,38,47,49,68]],[47,386,[68],[11,38,44,49,70,72]],[49,386,[68,70],[11,38,44,47,72]],[35,545,[61],[17,41,48,54,57,59,60]],[17,548,[66,71,73],[35,54,57,59,60]],[54,548,[71],[17,35,57,59,60,66,73]],[57,548,[66,71],[17,35,54,59,60,73]],[59,548,[66,73],[17,35,54,57,60,71]],[60,548,[66,71,73],[17,35,54,57,59]],[41,554,[66],[]],[66,554,[41],[]],[48,610,[71],[]],[71,610,[48],[]],[55,396,[68],[]],[68,396,[55],[]],[58,404,[70],[]],[61,568,[73],[]],[73,568,[61],[]],[72,432,[62],[]]],\"edges\":[[38,[17,35,41,48,54,57,59,60,61,66,71,73]],[42,[11,38,44,47,49,55,58,62,68,70,72]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record007" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record007\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-14,-12],[-21,-10],[-25,-11],[-25,-22],[-25,-23],[-4,20],[-1,25,26,28],[-6,26,28],[-7,25],[-9,25,26],[-3,19],[-2,24,27,29],[-13,27],[-15,24,27],[-17,24,29],[-18,24,27,29],[-5,24],[-24,5],[-8,27],[-27,8],[-14,25],[-25,14],[-16,26],[-19,29],[-29,19],[-28,20],[-30,21,22,23],[-31,10,11,12],[-32,30],[-33,32],[-34,31],[-35,34],[-36,33],[-36,35],[36],[-5,37],[-8,37],[-38,19,24],[-19,38],[-24,38],[-20,39],[-26,39],[-40,25],[-25,40],[-41,27],[-27,41],[-29,42],[-37,43],[-39,44],[-45,38],[-38,-39,45],[-45,46],[-43,-44,46],[-43,-45,47],[-48,40,41],[-41,48],[-40,48],[-42,49],[-49,50],[-48,50],[-46,-50,51],[-47,51],[-51],[2,3,5,8,13,15,17,18,19,24,27,29],[1,4,6,7,9,14,16,20,25,26,28]],\"atoms\":[{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":55,\"b\":53},{\"tag\":\"incompatible\",\"a\":63,\"b\":50},{\"tag\":\"incompatible\",\"a\":68,\"b\":52},{\"tag\":\"incompatible\",\"a\":68,\"b\":64},{\"tag\":\"incompatible\",\"a\":68,\"b\":65},{\"tag\":\"mate\",\"ridge\":385,\"a\":38,\"owners\":[62]},{\"tag\":\"mate\",\"ridge\":386,\"a\":11,\"owners\":[68,70,72]},{\"tag\":\"mate\",\"ridge\":386,\"a\":44,\"owners\":[70,72]},{\"tag\":\"mate\",\"ridge\":386,\"a\":47,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":386,\"a\":49,\"owners\":[68,70]},{\"tag\":\"mate\",\"ridge\":545,\"a\":35,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":548,\"a\":17,\"owners\":[66,71,73]},{\"tag\":\"mate\",\"ridge\":548,\"a\":54,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":548,\"a\":57,\"owners\":[66,71]},{\"tag\":\"mate\",\"ridge\":548,\"a\":59,\"owners\":[66,73]},{\"tag\":\"mate\",\"ridge\":548,\"a\":60,\"owners\":[66,71,73]},{\"tag\":\"mate\",\"ridge\":554,\"a\":41,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":554,\"a\":66,\"owners\":[41]},{\"tag\":\"mate\",\"ridge\":610,\"a\":48,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":610,\"a\":71,\"owners\":[48]},{\"tag\":\"mate\",\"ridge\":396,\"a\":55,\"owners\":[68]},{\"tag\":\"mate\",\"ridge\":396,\"a\":68,\"owners\":[55]},{\"tag\":\"mate\",\"ridge\":404,\"a\":58,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":568,\"a\":61,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":568,\"a\":73,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":432,\"a\":72,\"owners\":[62]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[63,64,65],\"full_literals\":[-30,21,22,23]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[50,52,53],\"full_literals\":[-31,10,11,12]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-32,false,30],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-33,false,32],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-34,31,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-35,false,34],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-36,33,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-36,false,35],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":41,\"full_literals\":[-5,37]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":48,\"full_literals\":[-8,37]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[61,66],\"full_literals\":[-38,19,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":61,\"full_literals\":[-19,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":66,\"full_literals\":[-24,38]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":62,\"full_literals\":[-20,39]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":70,\"full_literals\":[-26,39]},{\"tag\":\"group_or\",\"kind\":3,\"index\":4,\"members\":[68],\"full_literals\":[-40,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":68,\"full_literals\":[-25,40]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[71],\"full_literals\":[-41,27]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":71,\"full_literals\":[-27,41]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":73,\"full_literals\":[-29,42]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-37,false,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-39,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-45,38,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0018\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-38,-39,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-45,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-43,-44,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-43,-45,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-48,40,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-41,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0019\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0020\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-40,false,48],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0025\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-42,49],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-49,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-48,false,50],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-46,-50,51],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-47,false,51],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":38,\"owners\":[17,35,41,48,54,57,59,60,61,66,71,73]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[11,38,44,47,49,55,58,62,68,70,72]}]}"
  "66 33 0 35 33 0\n67 35 0 35 34 0\n68 32 0 66 30 0\n69 34 0 67 32 0\n70 30 0 68 29 0\n71 31 0 69 31 0\n72 -47 0 63 62 0\n73 39 25 0 21 9 41 42 6 26 8 23 7 10 65 0\n74 48 45 0 56 57 46 44 13 19 73 51 39 40 11 25 15 17 12 14 16 64 0\n75 40 46 0 52 74 44 55 73 45 49 20 53 37 48 0\n76 -25 0 70 71 3 4 5 22 27 1 2 28 0\n77 -40 0 76 43 0\n78 46 0 77 75 0\n79 -50 0 78 63 61 0\n80 -49 0 79 59 0\n81 -48 0 79 60 0\n82 -42 0 80 58 0\n83 45 0 81 74 0\n84 -29 0 82 47 0\n85 38 0 83 50 0\n86 -43 0 83 72 54 0\n87 -19 0 84 24 0\n88 24 0 85 87 38 0\n89 -37 0 86 48 0\n90 5 0 88 18 0\n91 0 90 89 36 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record007.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record007.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record007.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record007.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record007 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record007.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record007.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record007.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record007.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record007 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record007_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record007 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record007_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record007_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record007

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record017
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "2749b19c9c99a36a6665a568d8766386e4789e17a719a599564d999715656558d4756364d8b52d1b51d2745d98d9394cd38cc7362ccb2ad1b26c5b61e4789c6785d1725c570dd0f23c4f07c6a0ba616465162469896154550d0b46324c5322c4b0ac2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db6db6da6da49b4924d34926d249a49349b492492491249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record017 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record017 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record017.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record017.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record017.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 30), (facetIndex 49), (facetIndex 51), (facetIndex 59), (facetIndex 63)]))
 (.leaf ([(facetIndex 22), (facetIndex 37), (facetIndex 68)])))
 (.branch 3
 (.leaf ([(facetIndex 24), (facetIndex 48), (facetIndex 50), (facetIndex 53)]))
 (.leaf ([(facetIndex 44), (facetIndex 57), (facetIndex 62)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 23), (facetIndex 35), (facetIndex 38), (facetIndex 39)]))
 (.leaf ([(facetIndex 40), (facetIndex 43), (facetIndex 45), (facetIndex 64)])))
 (.branch 7
 (.leaf ([(facetIndex 28), (facetIndex 29), (facetIndex 55), (facetIndex 56), (facetIndex 58)]))
 (.branch 8
 (.leaf ([(facetIndex 21), (facetIndex 26), (facetIndex 27), (facetIndex 34), (facetIndex 42)]))
 (.leaf ([(facetIndex 25), (facetIndex 31)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "100050300063660200202005357054410470080667782417z15;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 33), (facetIndex 36), (facetIndex 47)]))
 (.leaf ([(facetIndex 32), (facetIndex 41), (facetIndex 54)])))
 (.branch 3
 (.leaf ([(facetIndex 66), (facetIndex 67), (facetIndex 69)]))
 (.branch 4
 (.leaf ([(facetIndex 70), (facetIndex 71), (facetIndex 72)]))
 (.leaf ([(facetIndex 73), (facetIndex 76), (facetIndex 78)])))))
 (.branch 7
 (.branch 6
 (.leaf ([(facetIndex 74), (facetIndex 77), (facetIndex 80)]))
 (.leaf ([(facetIndex 46), (facetIndex 52)])))
 (.branch 8
 (.leaf ([(facetIndex 65), (facetIndex 79)]))
 (.branch 9
 (.leaf ([(facetIndex 60), (facetIndex 61)]))
 (.leaf ([(facetIndex 75)]))))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "5745495433320227000880000010600000600001000000001z20;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 10
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1, 2, 3]
def grouped2_0002 : List Nat := [4]
def grouped2_0003 : List Nat := [4, 5]
def grouped2_0004 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0005 : List Nat := [5]
def grouped2_0006 : List Nat := [6]
def grouped2_0007 : List Nat := [6, 7, 8]
def grouped2_0008 : List Nat := [7]
def grouped2_0009 : List Nat := [7, 8]
def grouped2_0010 : List Nat := [8]
def grouped3_0011 : List Nat := [0]
def grouped3_0012 : List Nat := [0, 1]
def grouped3_0013 : List Nat := [0, 1, 2, 3, 4]
def grouped3_0015 : List Nat := [1]
def grouped3_0016 : List Nat := [2]
def grouped3_0017 : List Nat := [2, 3, 4]
def grouped3_0018 : List Nat := [3]
def grouped3_0019 : List Nat := [3, 4]
def grouped3_0020 : List Nat := [4]
def grouped3_0021 : List Nat := [5]
def grouped3_0022 : List Nat := [5, 6]
def grouped3_0023 : List Nat := [5, 6, 7, 8, 9]
def grouped3_0024 : List Nat := [6]
def grouped3_0025 : List Nat := [7]
def grouped3_0026 : List Nat := [7, 8, 9]
def grouped3_0027 : List Nat := [8]
def grouped3_0028 : List Nat := [8, 9]
def grouped3_0029 : List Nat := [9]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record017 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record017_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record017" "{\"atoms\":[{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0003\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0007\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group\",\"kind\":3,\"index\":6},{\"tag\":\"group\",\"kind\":3,\"index\":7},{\"tag\":\"group\",\"kind\":3,\"index\":8},{\"tag\":\"group\",\"kind\":3,\"index\":9},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0012\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0019\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0017\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0013\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0022\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0028\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0023\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record017" 90

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record017" "{\"ridges\":[[1,22],[7,146],[10,268],[11,276],[12,532],[13,545],[15,392],[16,577],[16,592],[17,400],[18,608],[21,22],[24,268],[25,22],[26,22],[27,22],[27,146],[28,22],[28,276],[29,532],[31,548],[32,582],[33,390],[35,146],[39,138],[40,82],[42,146],[43,592],[44,146],[44,400],[45,608],[46,92],[47,156],[48,268],[50,268],[51,545],[52,588],[53,268],[54,116],[55,548],[56,592],[57,276],[57,400],[58,276],[59,608],[62,392],[62,400],[63,608],[64,592],[64,608],[65,92],[72,582],[74,582],[79,588],[80,116]],\"owners\":[[1,22,[65,66,67,70,71,72,73],[21,25,26,27,28,29]],[21,22,[70,71,72,73],[1,25,26,27,28,29,65,66,67]],[25,22,[65,66,67,72,73],[1,21,26,27,28,29,70,71]],[26,22,[66,67,71,73],[1,21,25,27,28,29,65,70,72]],[27,22,[65,67,70,71,72],[1,21,25,26,28,29,66,73]],[28,22,[65,66,70,71,72],[1,21,25,26,27,29,67,73]],[39,138,[66,75],[5,23,35,37,38,69,76]],[40,82,[65,72,75],[6,26,34,42,43,70,77]],[7,146,[66,73,75,76],[27,35,42,44]],[27,146,[75,76],[7,35,42,44,66,73]],[35,146,[73],[7,27,42,44,66,75,76]],[42,146,[66,73,76],[7,27,35,44,75]],[44,146,[66,75],[7,27,35,42,73,76]],[10,268,[67,69,78],[24,48,50,53]],[24,268,[78],[10,48,50,53,67,69]],[48,268,[69],[10,24,50,53,67,78]],[50,268,[67,69,78],[10,24,48,53]],[53,268,[67],[10,24,48,50,69,78]],[11,276,[67,73,78],[28,48,57,58]],[28,276,[78],[11,48,57,58,67,73]],[57,276,[67],[11,28,48,58,73,78]],[58,276,[67,73,78],[11,28,48,57]],[12,532,[71,72,80],[29,55,56,58]],[29,532,[80],[12,55,56,58,71,72]],[13,545,[18,41,45,63,64],[31,51,55]],[51,545,[18,41,45,64],[13,31,55,63]],[31,548,[79,80],[13,51,55,59,71,74]],[55,548,[74,79],[13,31,51,59,71,80]],[15,392,[69,76,78],[39,53,62]],[62,392,[69],[15,39,53,76,78]],[16,577,[18,32,45,52,59,63],[43,56]],[16,592,[72,77,80],[43,56,64]],[43,592,[80],[16,56,64,72,77]],[56,592,[77],[16,43,64,72,80]],[64,592,[72],[16,43,56,77,80]],[17,400,[73,76,78],[44,57,62]],[44,400,[78],[17,57,62,73,76]],[57,400,[76],[17,44,62,73,78]],[62,400,[73],[17,44,57,76,78]],[18,608,[74,77,79,80],[45,59,63,64]],[45,608,[79,80],[18,59,63,64,74,77]],[59,608,[77],[18,45,63,64,74,79,80]],[63,608,[74,77,80],[18,45,59,64,79]],[64,608,[74,79],[18,45,59,63,77,80]],[32,582,[72,74],[]],[72,582,[32,74],[]],[74,582,[32,72],[]],[33,390,[69,73],[]],[46,92,[65],[]],[65,92,[46],[]],[47,156,[66,78],[]],[52,588,[79],[]],[79,588,[52],[]],[54,116,[70,80],[]],[80,116,[54,70],[]]],\"edges\":[[18,[1,11,12,21,25,26,27,28,29,46,47,48,54,55,56,57,58,65,66,67,70,71,72,73,78,80]],[22,[10,11,24,28,33,48,50,53,57,58,67,69,73,78]],[32,[7,17,27,35,42,44,47,57,60,62,66,73,75,76,78]],[38,[13,18,31,41,45,51,55,59,63,64,71,74,77,79,80]],[41,[16,18,32,43,45,52,56,59,63,64,72,74,77,79,80]],[42,[15,17,33,39,44,53,57,62,69,73,76,78]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record017" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record017\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-52,-24],[-52,-51],[-57,-13],[-1,46,47,48,50,51,52,53],[-11,50,51,52,53],[-13,46,47,48,52,53],[-14,47,48,51,53],[-15,46,48,50,51,52],[-16,46,47,50,51,52],[-22,47,55],[-23,46,52,55],[-2,47,53,55,56],[-15,55,56],[-21,53],[-25,47,53,56],[-27,47,55],[-3,48,49,58],[-12,58],[-31,49],[-32,48,49,58],[-35,48],[-4,48,53,58],[-16,58],[-39,48],[-40,48,53,58],[-5,51,52,60],[-17,60],[-6,10,24,28,44,45],[-33,10,24,28,45],[-18,59,60],[-37,54,59],[-7,49,56,58],[-43,49],[-8,10,19,28,34,41,44],[-8,52,57,60],[-26,60],[-38,57],[-45,52],[-9,53,56,58],[-27,58],[-39,56],[-43,53],[-10,54,57,59,60],[-28,59,60],[-41,57],[-44,54,57,60],[-45,54,59],[-19,52,54],[-52,19,54],[-54,19,52],[-20,49,53],[-29,46],[-46,29],[-30,47,58],[-34,59],[-59,34],[-36,50,60],[-60,36,50],[-61,23,26,28,45],[-62,13,18],[-63,61],[-64,62],[-65,64],[-66,63,65],[-67,66],[67],[-20,68],[-30,68],[-19,69],[-36,69],[-47,70],[-48,70],[-49,70],[-50,71],[-51,71],[-52,71],[-53,72],[-56,72],[-58,72],[-73,54,57,60],[-54,73],[-57,73],[-60,73],[-74,29,34],[-29,74],[-34,74],[-46,75],[-59,75],[-42,76],[-55,77],[-69,78],[-68,78],[-72,79],[-71,79],[-71,-72,80],[-79,81],[-80,82],[-70,81],[-70,-79,82],[-81,83],[-82,84],[-78,83],[-78,-81,84],[-85,73,74],[-74,85],[-73,85],[-77,86],[-76,86],[-86,87],[-75,87],[-87,88],[-85,88],[-85,-87,89],[-83,-89,90],[-84,-88,90],[-90],[1,4,5,11,13,14,15,16,17,29,30,31,36,37,38,39,40,46,47,48,50,51,52,53,58,60],[3,4,12,16,20,31,32,35,39,40,48,49,53,58],[2,9,15,21,25,27,30,39,42,43,47,53,55,56,58],[6,10,18,24,28,33,37,41,44,45,51,54,57,59,60],[8,10,19,26,28,34,38,41,44,45,52,54,57,59,60],[7,9,20,22,27,35,39,43,49,53,56,58]],\"atoms\":[{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"facet\",\"index\":78},{\"tag\":\"facet\",\"index\":79},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group\",\"index\":6,\"kind\":3},{\"tag\":\"group\",\"index\":7,\"kind\":3},{\"tag\":\"group\",\"index\":8,\"kind\":3},{\"tag\":\"group\",\"index\":9,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":72,\"b\":41},{\"tag\":\"incompatible\",\"a\":72,\"b\":71},{\"tag\":\"incompatible\",\"a\":77,\"b\":25},{\"tag\":\"mate\",\"ridge\":22,\"a\":1,\"owners\":[65,66,67,70,71,72,73]},{\"tag\":\"mate\",\"ridge\":22,\"a\":21,\"owners\":[70,71,72,73]},{\"tag\":\"mate\",\"ridge\":22,\"a\":25,\"owners\":[65,66,67,72,73]},{\"tag\":\"mate\",\"ridge\":22,\"a\":26,\"owners\":[66,67,71,73]},{\"tag\":\"mate\",\"ridge\":22,\"a\":27,\"owners\":[65,67,70,71,72]},{\"tag\":\"mate\",\"ridge\":22,\"a\":28,\"owners\":[65,66,70,71,72]},{\"tag\":\"mate\",\"ridge\":138,\"a\":39,\"owners\":[66,75]},{\"tag\":\"mate\",\"ridge\":82,\"a\":40,\"owners\":[65,72,75]},{\"tag\":\"mate\",\"ridge\":146,\"a\":7,\"owners\":[66,73,75,76]},{\"tag\":\"mate\",\"ridge\":146,\"a\":27,\"owners\":[75,76]},{\"tag\":\"mate\",\"ridge\":146,\"a\":35,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":146,\"a\":42,\"owners\":[66,73,76]},{\"tag\":\"mate\",\"ridge\":146,\"a\":44,\"owners\":[66,75]},{\"tag\":\"mate\",\"ridge\":268,\"a\":10,\"owners\":[67,69,78]},{\"tag\":\"mate\",\"ridge\":268,\"a\":24,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":268,\"a\":48,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":268,\"a\":50,\"owners\":[67,69,78]},{\"tag\":\"mate\",\"ridge\":268,\"a\":53,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":276,\"a\":11,\"owners\":[67,73,78]},{\"tag\":\"mate\",\"ridge\":276,\"a\":28,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":276,\"a\":57,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":276,\"a\":58,\"owners\":[67,73,78]},{\"tag\":\"mate\",\"ridge\":532,\"a\":12,\"owners\":[71,72,80]},{\"tag\":\"mate\",\"ridge\":532,\"a\":29,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":545,\"a\":13,\"owners\":[18,41,45,63,64]},{\"tag\":\"mate\",\"ridge\":545,\"a\":51,\"owners\":[18,41,45,64]},{\"tag\":\"mate\",\"ridge\":548,\"a\":31,\"owners\":[79,80]},{\"tag\":\"mate\",\"ridge\":548,\"a\":55,\"owners\":[74,79]},{\"tag\":\"mate\",\"ridge\":392,\"a\":15,\"owners\":[69,76,78]},{\"tag\":\"mate\",\"ridge\":392,\"a\":62,\"owners\":[69]},{\"tag\":\"mate\",\"ridge\":577,\"a\":16,\"owners\":[18,32,45,52,59,63]},{\"tag\":\"mate\",\"ridge\":592,\"a\":16,\"owners\":[72,77,80]},{\"tag\":\"mate\",\"ridge\":592,\"a\":43,\"owners\":[80]},{\"tag\":\"mate\",\"ridge\":592,\"a\":56,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":592,\"a\":64,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":400,\"a\":17,\"owners\":[73,76,78]},{\"tag\":\"mate\",\"ridge\":400,\"a\":44,\"owners\":[78]},{\"tag\":\"mate\",\"ridge\":400,\"a\":57,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":400,\"a\":62,\"owners\":[73]},{\"tag\":\"mate\",\"ridge\":608,\"a\":18,\"owners\":[74,77,79,80]},{\"tag\":\"mate\",\"ridge\":608,\"a\":45,\"owners\":[79,80]},{\"tag\":\"mate\",\"ridge\":608,\"a\":59,\"owners\":[77]},{\"tag\":\"mate\",\"ridge\":608,\"a\":63,\"owners\":[74,77,80]},{\"tag\":\"mate\",\"ridge\":608,\"a\":64,\"owners\":[74,79]},{\"tag\":\"mate\",\"ridge\":582,\"a\":32,\"owners\":[72,74]},{\"tag\":\"mate\",\"ridge\":582,\"a\":72,\"owners\":[32,74]},{\"tag\":\"mate\",\"ridge\":582,\"a\":74,\"owners\":[32,72]},{\"tag\":\"mate\",\"ridge\":390,\"a\":33,\"owners\":[69,73]},{\"tag\":\"mate\",\"ridge\":92,\"a\":46,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":92,\"a\":65,\"owners\":[46]},{\"tag\":\"mate\",\"ridge\":156,\"a\":47,\"owners\":[66,78]},{\"tag\":\"mate\",\"ridge\":588,\"a\":52,\"owners\":[79]},{\"tag\":\"mate\",\"ridge\":588,\"a\":79,\"owners\":[52]},{\"tag\":\"mate\",\"ridge\":116,\"a\":54,\"owners\":[70,80]},{\"tag\":\"mate\",\"ridge\":116,\"a\":80,\"owners\":[54,70]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[40,43,45,64],\"full_literals\":[-61,23,26,28,45]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[25,31],\"full_literals\":[-62,13,18]},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0003\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-63,false,61],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-64,false,62],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0006\",\"right_name\":\"grouped2_0009\",\"joined_name\":\"grouped2_0007\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-65,false,64],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0004\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-66,63,65],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-67,false,66],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":33,\"full_literals\":[-20,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":47,\"full_literals\":[-30,68]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":32,\"full_literals\":[-19,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":54,\"full_literals\":[-36,69]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":66,\"full_literals\":[-47,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":67,\"full_literals\":[-48,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":69,\"full_literals\":[-49,70]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":70,\"full_literals\":[-50,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":71,\"full_literals\":[-51,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":72,\"full_literals\":[-52,71]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":73,\"full_literals\":[-53,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":76,\"full_literals\":[-56,72]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":78,\"full_literals\":[-58,72]},{\"tag\":\"group_or\",\"kind\":3,\"index\":5,\"members\":[74,77,80],\"full_literals\":[-73,54,57,60]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":74,\"full_literals\":[-54,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":77,\"full_literals\":[-57,73]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":80,\"full_literals\":[-60,73]},{\"tag\":\"group_or\",\"kind\":3,\"index\":6,\"members\":[46,52],\"full_literals\":[-74,29,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":46,\"full_literals\":[-29,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":6,\"member\":52,\"full_literals\":[-34,74]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":65,\"full_literals\":[-46,75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":7,\"member\":79,\"full_literals\":[-59,75]},{\"tag\":\"group_take\",\"kind\":3,\"index\":8,\"member\":60,\"full_literals\":[-42,76]},{\"tag\":\"group_take\",\"kind\":3,\"index\":9,\"member\":75,\"full_literals\":[-55,77]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-69,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0011\",\"right_name\":\"grouped3_0015\",\"joined_name\":\"grouped3_0012\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-68,false,78],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-72,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-71,false,79],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0020\",\"joined_name\":\"grouped3_0019\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-71,-72,80],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-79,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0017\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-80,82],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-70,false,81],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3,4],\"left_name\":\"grouped3_0016\",\"right_name\":\"grouped3_0019\",\"joined_name\":\"grouped3_0017\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-70,-79,82],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-81,83],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-82,84],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-78,false,83],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3,4],\"left_name\":\"grouped3_0012\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0013\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-78,-81,84],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-85,73,74],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-74,85],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5],\"right\":[6],\"left_name\":\"grouped3_0021\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"grouped3_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-73,false,85],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-77,86],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[8],\"right\":[9],\"left_name\":\"grouped3_0027\",\"right_name\":\"grouped3_0029\",\"joined_name\":\"grouped3_0028\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-76,false,86],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-86,87],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[7],\"right\":[8,9],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0028\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-75,false,87],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-87,88],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-85,false,88],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[5,6],\"right\":[7,8,9],\"left_name\":\"grouped3_0022\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0023\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-85,-87,89],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-83,-89,90],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2,3,4],\"right\":[5,6,7,8,9],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0023\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-84,-88,90],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":18,\"owners\":[1,11,12,21,25,26,27,28,29,46,47,48,54,55,56,57,58,65,66,67,70,71,72,73,78,80]},{\"tag\":\"edge\",\"edge\":22,\"owners\":[10,11,24,28,33,48,50,53,57,58,67,69,73,78]},{\"tag\":\"edge\",\"edge\":32,\"owners\":[7,17,27,35,42,44,47,57,60,62,66,73,75,76,78]},{\"tag\":\"edge\",\"edge\":38,\"owners\":[13,18,31,41,45,51,55,59,63,64,71,74,77,79,80]},{\"tag\":\"edge\",\"edge\":41,\"owners\":[16,18,32,43,45,52,56,59,63,64,72,74,77,79,80]},{\"tag\":\"edge\",\"edge\":42,\"owners\":[15,17,33,39,44,53,57,62,69,73,76,78]}]}"
  "123 66 0 66 65 0\n124 83 0 100 102 96 98 92 93 72 73 67 77 79 17 20 21 22 24 25 19 18 23 118 0\n125 -89 0 124 116 114 0\n126 81 85 0 106 83 27 82 37 105 86 56 81 31 85 53 96 98 93 94 71 72 73 77 79 74 75 76 7 54 4 6 9 22 24 25 8 19 5 57 26 117 0\n127 85 84 0 105 106 86 81 82 83 56 46 47 37 45 36 44 43 126 103 91 69 49 34 121 0\n128 52 60 19 -85 0 125 123 113 110 88 44 30 36 55 87 52 84 104 109 107 90 38 50 11 80 59 3 61 60 64 62 63 0\n129 -71 30 84 0 125 127 113 109 108 89 107 90 101 97 94 95 99 77 78 79 71 14 39 42 15 41 13 40 12 119 0\n130 78 84 0 127 91 92 69 70 68 129 74 76 58 128 0\n131 84 0 125 127 113 109 107 90 130 103 96 98 93 71 72 73 77 78 79 16 10 21 24 32 33 51 39 122 0\n132 -88 0 131 116 115 0\n133 -87 0 132 111 0\n134 -85 0 132 112 0\n135 -75 0 133 110 0\n136 -74 0 134 105 0\n137 -73 0 134 106 0\n138 -59 0 135 88 0\n139 -34 0 136 86 0\n140 -54 0 137 81 0\n141 -57 0 137 82 0\n142 -60 0 137 83 0\n143 -37 0 140 138 31 0\n144 -45 0 140 138 47 0\n145 -38 0 141 37 0\n146 -41 0 141 45 0\n147 -10 0 141 138 140 142 43 0\n148 -44 0 141 140 142 46 0\n149 -26 0 142 36 0\n150 -18 0 142 138 30 0\n151 -28 0 142 138 44 0\n152 52 0 142 138 141 140 144 148 146 145 139 151 149 147 48 35 121 0\n153 -24 0 152 1 0\n154 -51 0 152 2 0\n155 -6 0 153 147 151 148 144 28 0\n156 -33 0 153 147 151 144 29 0\n157 0 155 153 150 147 151 156 143 146 148 144 154 140 141 138 142 120 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record017.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record017.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record017.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record017.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record017 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record017.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record017.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record017.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record017.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record017 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record017_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record017_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record017_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record017_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record017_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record017_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record017_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record017 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record017_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record017_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record017_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record017

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record033
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "9d26c1f2729a87a9999695a361da8e63a4e8b86e1783e9a47999595554756364d3362d1b45d0f66364d331cd8b92e2b2ac6b16c3b91e2719c9715c3783d0f13c2f07e689322a619168388e1c469615151548d1358344c3322c2b41c8705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "69b4da6da4936d269249349b49269269b692492449249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record033 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record033 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record033.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record033.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record033.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 26), (facetIndex 30), (facetIndex 43), (facetIndex 54), (facetIndex 68)]))
 (.leaf ([(facetIndex 40), (facetIndex 51), (facetIndex 63)])))
 (.branch 3
 (.leaf ([(facetIndex 28), (facetIndex 34), (facetIndex 41), (facetIndex 42)]))
 (.leaf ([(facetIndex 29), (facetIndex 46), (facetIndex 52), (facetIndex 53)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 36), (facetIndex 47), (facetIndex 56), (facetIndex 57)]))
 (.leaf ([(facetIndex 23), (facetIndex 24), (facetIndex 25), (facetIndex 27), (facetIndex 64)])))
 (.branch 7
 (.leaf ([(facetIndex 37), (facetIndex 38)]))
 (.branch 8
 (.leaf ([(facetIndex 49), (facetIndex 50)]))
 (.leaf ([(facetIndex 61), (facetIndex 62), (facetIndex 71), (facetIndex 74)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "8008000000518800044003317704300022106640200003250555z17;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 31), (facetIndex 32), (facetIndex 45), (facetIndex 66)]))
 (.branch 2
 (.leaf ([(facetIndex 33), (facetIndex 35), (facetIndex 60), (facetIndex 67)]))
 (.leaf ([(facetIndex 48), (facetIndex 58), (facetIndex 65), (facetIndex 75)]))))
 (.branch 4
 (.leaf ([(facetIndex 39), (facetIndex 55), (facetIndex 69)]))
 (.branch 5
 (.leaf ([(facetIndex 44), (facetIndex 59), (facetIndex 72)]))
 (.leaf ([(facetIndex 70), (facetIndex 73)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "42c158210001880600002004000600208z18;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 6
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
def grouped2_0008 : List Nat := [4]
def grouped2_0009 : List Nat := [4, 5]
def grouped2_0010 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0011 : List Nat := [5]
def grouped2_0012 : List Nat := [6]
def grouped2_0013 : List Nat := [6, 7, 8]
def grouped2_0014 : List Nat := [7]
def grouped2_0015 : List Nat := [7, 8]
def grouped2_0016 : List Nat := [8]
def grouped3_0017 : List Nat := [0]
def grouped3_0018 : List Nat := [0, 1, 2]
def grouped3_0020 : List Nat := [1]
def grouped3_0021 : List Nat := [1, 2]
def grouped3_0022 : List Nat := [2]
def grouped3_0023 : List Nat := [3]
def grouped3_0024 : List Nat := [3, 4, 5]
def grouped3_0025 : List Nat := [4]
def grouped3_0026 : List Nat := [4, 5]
def grouped3_0027 : List Nat := [5]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record033 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record033_matrix_checked

def leafCount : Nat := 32
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaf0000 : List (Fin data.count) := [(facetIndex 6), (facetIndex 7), (facetIndex 8), (facetIndex 37), (facetIndex 50), (facetIndex 51), (facetIndex 53), (facetIndex 56), (facetIndex 64), (facetIndex 66), (facetIndex 68), (facetIndex 71), (facetIndex 75)]
theorem leaf0000_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0000 = true := by
  decide +kernel
theorem leaf0000_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0000 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0000_counts_checked
def leaf0001 : List (Fin data.count) := [(facetIndex 6), (facetIndex 7), (facetIndex 13), (facetIndex 38), (facetIndex 40), (facetIndex 49), (facetIndex 53), (facetIndex 56), (facetIndex 64), (facetIndex 67), (facetIndex 68), (facetIndex 72), (facetIndex 74)]
theorem leaf0001_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0001 = true := by
  decide +kernel
theorem leaf0001_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0001 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0001_counts_checked
def leaf0002 : List (Fin data.count) := [(facetIndex 8), (facetIndex 18), (facetIndex 19), (facetIndex 37), (facetIndex 42), (facetIndex 50), (facetIndex 51), (facetIndex 53), (facetIndex 56), (facetIndex 64), (facetIndex 66), (facetIndex 71), (facetIndex 75)]
theorem leaf0002_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0002 = true := by
  decide +kernel
theorem leaf0002_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0002 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0002_counts_checked
def leaf0003 : List (Fin data.count) := [(facetIndex 6), (facetIndex 18), (facetIndex 19), (facetIndex 37), (facetIndex 43), (facetIndex 50), (facetIndex 51), (facetIndex 53), (facetIndex 56), (facetIndex 64), (facetIndex 66), (facetIndex 71), (facetIndex 75)]
theorem leaf0003_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0003 = true := by
  decide +kernel
theorem leaf0003_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0003 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0003_counts_checked
def leaf0004 : List (Fin data.count) := [(facetIndex 8), (facetIndex 14), (facetIndex 15), (facetIndex 37), (facetIndex 42), (facetIndex 50), (facetIndex 51), (facetIndex 53), (facetIndex 64), (facetIndex 66), (facetIndex 68), (facetIndex 71), (facetIndex 75)]
theorem leaf0004_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0004 = true := by
  decide +kernel
theorem leaf0004_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0004 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0004_counts_checked
def leaf0005 : List (Fin data.count) := [(facetIndex 5), (facetIndex 8), (facetIndex 13), (facetIndex 38), (facetIndex 42), (facetIndex 49), (facetIndex 53), (facetIndex 56), (facetIndex 64), (facetIndex 67), (facetIndex 68), (facetIndex 72), (facetIndex 74)]
theorem leaf0005_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0005 = true := by
  decide +kernel
theorem leaf0005_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0005 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0005_counts_checked
def leaf0006 : List (Fin data.count) := [(facetIndex 8), (facetIndex 13), (facetIndex 20), (facetIndex 37), (facetIndex 42), (facetIndex 49), (facetIndex 53), (facetIndex 56), (facetIndex 64), (facetIndex 67), (facetIndex 68), (facetIndex 72), (facetIndex 74)]
theorem leaf0006_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0006 = true := by
  decide +kernel
theorem leaf0006_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0006 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0006_counts_checked
def leaf0007 : List (Fin data.count) := [(facetIndex 4), (facetIndex 5), (facetIndex 8), (facetIndex 42), (facetIndex 50), (facetIndex 51), (facetIndex 53), (facetIndex 56), (facetIndex 64), (facetIndex 66), (facetIndex 68), (facetIndex 71), (facetIndex 75)]
theorem leaf0007_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0007 = true := by
  decide +kernel
theorem leaf0007_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0007 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0007_counts_checked
def leaf0008 : List (Fin data.count) := [(facetIndex 4), (facetIndex 10), (facetIndex 13), (facetIndex 40), (facetIndex 42), (facetIndex 50), (facetIndex 53), (facetIndex 56), (facetIndex 64), (facetIndex 66), (facetIndex 68), (facetIndex 71), (facetIndex 75)]
theorem leaf0008_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0008 = true := by
  decide +kernel
theorem leaf0008_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0008 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0008_counts_checked
def leaf0009 : List (Fin data.count) := [(facetIndex 4), (facetIndex 13), (facetIndex 20), (facetIndex 40), (facetIndex 42), (facetIndex 49), (facetIndex 53), (facetIndex 56), (facetIndex 64), (facetIndex 67), (facetIndex 68), (facetIndex 72), (facetIndex 74)]
theorem leaf0009_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0009 = true := by
  decide +kernel
theorem leaf0009_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0009 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0009_counts_checked
def leaf0010 : List (Fin data.count) := [(facetIndex 4), (facetIndex 13), (facetIndex 21), (facetIndex 40), (facetIndex 42), (facetIndex 49), (facetIndex 53), (facetIndex 56), (facetIndex 64), (facetIndex 66), (facetIndex 68), (facetIndex 71), (facetIndex 75)]
theorem leaf0010_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0010 = true := by
  decide +kernel
theorem leaf0010_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0010 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0010_counts_checked
def leaf0011 : List (Fin data.count) := [(facetIndex 8), (facetIndex 20), (facetIndex 22), (facetIndex 37), (facetIndex 42), (facetIndex 50), (facetIndex 51), (facetIndex 53), (facetIndex 56), (facetIndex 64), (facetIndex 65), (facetIndex 68), (facetIndex 69)]
theorem leaf0011_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0011 = true := by
  decide +kernel
theorem leaf0011_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0011 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0011_counts_checked
def leaf0012 : List (Fin data.count) := [(facetIndex 8), (facetIndex 20), (facetIndex 22), (facetIndex 37), (facetIndex 42), (facetIndex 50), (facetIndex 51), (facetIndex 53), (facetIndex 56), (facetIndex 64), (facetIndex 66), (facetIndex 68), (facetIndex 75)]
theorem leaf0012_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0012 = true := by
  decide +kernel
theorem leaf0012_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0012 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0012_counts_checked
def leaf0013 : List (Fin data.count) := [(facetIndex 8), (facetIndex 20), (facetIndex 22), (facetIndex 37), (facetIndex 42), (facetIndex 50), (facetIndex 51), (facetIndex 53), (facetIndex 56), (facetIndex 64), (facetIndex 67), (facetIndex 68), (facetIndex 72)]
theorem leaf0013_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0013 = true := by
  decide +kernel
theorem leaf0013_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0013 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0013_counts_checked
def leaf0014 : List (Fin data.count) := [(facetIndex 8), (facetIndex 16), (facetIndex 22), (facetIndex 37), (facetIndex 42), (facetIndex 50), (facetIndex 51), (facetIndex 53), (facetIndex 56), (facetIndex 61), (facetIndex 67), (facetIndex 68), (facetIndex 72)]
theorem leaf0014_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0014 = true := by
  decide +kernel
theorem leaf0014_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0014 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0014_counts_checked
def leaf0015 : List (Fin data.count) := [(facetIndex 8), (facetIndex 16), (facetIndex 17), (facetIndex 37), (facetIndex 42), (facetIndex 50), (facetIndex 51), (facetIndex 53), (facetIndex 56), (facetIndex 66), (facetIndex 68), (facetIndex 71), (facetIndex 75)]
theorem leaf0015_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0015 = true := by
  decide +kernel
theorem leaf0015_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0015 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0015_counts_checked
def leaf0016 : List (Fin data.count) := [(facetIndex 11), (facetIndex 12), (facetIndex 13), (facetIndex 38), (facetIndex 40), (facetIndex 42), (facetIndex 49), (facetIndex 56), (facetIndex 64), (facetIndex 67), (facetIndex 68), (facetIndex 72), (facetIndex 74)]
theorem leaf0016_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0016 = true := by
  decide +kernel
theorem leaf0016_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0016 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0016_counts_checked
def leaf0017 : List (Fin data.count) := [(facetIndex 8), (facetIndex 11), (facetIndex 12), (facetIndex 37), (facetIndex 42), (facetIndex 50), (facetIndex 51), (facetIndex 56), (facetIndex 64), (facetIndex 66), (facetIndex 68), (facetIndex 71), (facetIndex 75)]
theorem leaf0017_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0017 = true := by
  decide +kernel
theorem leaf0017_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0017 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0017_counts_checked
def leaf0018 : List (Fin data.count) := [(facetIndex 13), (facetIndex 18), (facetIndex 19), (facetIndex 38), (facetIndex 40), (facetIndex 42), (facetIndex 49), (facetIndex 53), (facetIndex 56), (facetIndex 64), (facetIndex 67), (facetIndex 72), (facetIndex 74)]
theorem leaf0018_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0018 = true := by
  decide +kernel
theorem leaf0018_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0018 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0018_counts_checked
def leaf0019 : List (Fin data.count) := [(facetIndex 11), (facetIndex 18), (facetIndex 19), (facetIndex 38), (facetIndex 40), (facetIndex 42), (facetIndex 49), (facetIndex 54), (facetIndex 56), (facetIndex 64), (facetIndex 67), (facetIndex 72), (facetIndex 74)]
theorem leaf0019_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0019 = true := by
  decide +kernel
theorem leaf0019_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0019 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0019_counts_checked
def leaf0020 : List (Fin data.count) := [(facetIndex 13), (facetIndex 14), (facetIndex 15), (facetIndex 38), (facetIndex 40), (facetIndex 42), (facetIndex 49), (facetIndex 53), (facetIndex 64), (facetIndex 67), (facetIndex 68), (facetIndex 72), (facetIndex 74)]
theorem leaf0020_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0020 = true := by
  decide +kernel
theorem leaf0020_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0020 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0020_counts_checked
def leaf0021 : List (Fin data.count) := [(facetIndex 8), (facetIndex 10), (facetIndex 13), (facetIndex 37), (facetIndex 42), (facetIndex 50), (facetIndex 53), (facetIndex 56), (facetIndex 64), (facetIndex 66), (facetIndex 68), (facetIndex 71), (facetIndex 75)]
theorem leaf0021_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0021 = true := by
  decide +kernel
theorem leaf0021_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0021 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0021_counts_checked
def leaf0022 : List (Fin data.count) := [(facetIndex 8), (facetIndex 13), (facetIndex 21), (facetIndex 37), (facetIndex 42), (facetIndex 49), (facetIndex 53), (facetIndex 56), (facetIndex 64), (facetIndex 66), (facetIndex 68), (facetIndex 71), (facetIndex 75)]
theorem leaf0022_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0022 = true := by
  decide +kernel
theorem leaf0022_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0022 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0022_counts_checked
def leaf0023 : List (Fin data.count) := [(facetIndex 9), (facetIndex 10), (facetIndex 13), (facetIndex 38), (facetIndex 40), (facetIndex 42), (facetIndex 53), (facetIndex 56), (facetIndex 64), (facetIndex 67), (facetIndex 68), (facetIndex 72), (facetIndex 74)]
theorem leaf0023_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0023 = true := by
  decide +kernel
theorem leaf0023_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0023 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0023_counts_checked
def leaf0024 : List (Fin data.count) := [(facetIndex 5), (facetIndex 8), (facetIndex 9), (facetIndex 38), (facetIndex 42), (facetIndex 51), (facetIndex 53), (facetIndex 56), (facetIndex 64), (facetIndex 67), (facetIndex 68), (facetIndex 72), (facetIndex 74)]
theorem leaf0024_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0024 = true := by
  decide +kernel
theorem leaf0024_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0024 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0024_counts_checked
def leaf0025 : List (Fin data.count) := [(facetIndex 8), (facetIndex 9), (facetIndex 21), (facetIndex 37), (facetIndex 42), (facetIndex 51), (facetIndex 53), (facetIndex 56), (facetIndex 64), (facetIndex 66), (facetIndex 68), (facetIndex 71), (facetIndex 75)]
theorem leaf0025_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0025 = true := by
  decide +kernel
theorem leaf0025_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0025 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0025_counts_checked
def leaf0026 : List (Fin data.count) := [(facetIndex 8), (facetIndex 9), (facetIndex 20), (facetIndex 37), (facetIndex 42), (facetIndex 51), (facetIndex 53), (facetIndex 56), (facetIndex 64), (facetIndex 67), (facetIndex 68), (facetIndex 72), (facetIndex 74)]
theorem leaf0026_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0026 = true := by
  decide +kernel
theorem leaf0026_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0026 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0026_counts_checked
def leaf0027 : List (Fin data.count) := [(facetIndex 13), (facetIndex 21), (facetIndex 22), (facetIndex 38), (facetIndex 40), (facetIndex 42), (facetIndex 49), (facetIndex 53), (facetIndex 56), (facetIndex 64), (facetIndex 65), (facetIndex 68), (facetIndex 69)]
theorem leaf0027_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0027 = true := by
  decide +kernel
theorem leaf0027_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0027 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0027_counts_checked
def leaf0028 : List (Fin data.count) := [(facetIndex 13), (facetIndex 21), (facetIndex 22), (facetIndex 38), (facetIndex 40), (facetIndex 42), (facetIndex 49), (facetIndex 53), (facetIndex 56), (facetIndex 64), (facetIndex 67), (facetIndex 68), (facetIndex 72)]
theorem leaf0028_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0028 = true := by
  decide +kernel
theorem leaf0028_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0028 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0028_counts_checked
def leaf0029 : List (Fin data.count) := [(facetIndex 13), (facetIndex 21), (facetIndex 22), (facetIndex 38), (facetIndex 40), (facetIndex 42), (facetIndex 49), (facetIndex 53), (facetIndex 56), (facetIndex 64), (facetIndex 66), (facetIndex 68), (facetIndex 75)]
theorem leaf0029_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0029 = true := by
  decide +kernel
theorem leaf0029_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0029 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0029_counts_checked
def leaf0030 : List (Fin data.count) := [(facetIndex 13), (facetIndex 16), (facetIndex 22), (facetIndex 38), (facetIndex 40), (facetIndex 42), (facetIndex 49), (facetIndex 53), (facetIndex 56), (facetIndex 62), (facetIndex 66), (facetIndex 68), (facetIndex 75)]
theorem leaf0030_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0030 = true := by
  decide +kernel
theorem leaf0030_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0030 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0030_counts_checked
def leaf0031 : List (Fin data.count) := [(facetIndex 13), (facetIndex 16), (facetIndex 17), (facetIndex 38), (facetIndex 40), (facetIndex 42), (facetIndex 49), (facetIndex 53), (facetIndex 56), (facetIndex 67), (facetIndex 68), (facetIndex 72), (facetIndex 74)]
theorem leaf0031_counts_checked :
    FacetSat.RawProjection.leafCountsCheck data.toData.kind requirements kindKeys leaf0031 = true := by
  decide +kernel
theorem leaf0031_checked :
    FacetSat.Boundary.leafCheck data.toData.kind requirements leaf0031 = true :=
  FacetSat.RawProjection.leafCheck_of_counts _ _ _ _ kindKeys_checked leaf0031_counts_checked
def leavesTable : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (leaf0000))
 (.leaf (leaf0001)))
 (.branch 3
 (.leaf (leaf0002))
 (.leaf (leaf0003))))
 (.branch 6
 (.branch 5
 (.leaf (leaf0004))
 (.leaf (leaf0005)))
 (.branch 7
 (.leaf (leaf0006))
 (.leaf (leaf0007)))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf (leaf0008))
 (.leaf (leaf0009)))
 (.branch 11
 (.leaf (leaf0010))
 (.leaf (leaf0011))))
 (.branch 14
 (.branch 13
 (.leaf (leaf0012))
 (.leaf (leaf0013)))
 (.branch 15
 (.leaf (leaf0014))
 (.leaf (leaf0015))))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf (leaf0016))
 (.leaf (leaf0017)))
 (.branch 19
 (.leaf (leaf0018))
 (.leaf (leaf0019))))
 (.branch 22
 (.branch 21
 (.leaf (leaf0020))
 (.leaf (leaf0021)))
 (.branch 23
 (.leaf (leaf0022))
 (.leaf (leaf0023)))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf (leaf0024))
 (.leaf (leaf0025)))
 (.branch 27
 (.leaf (leaf0026))
 (.leaf (leaf0027))))
 (.branch 30
 (.branch 29
 (.leaf (leaf0028))
 (.leaf (leaf0029)))
 (.branch 31
 (.leaf (leaf0030))
 (.leaf (leaf0031)))))))
def leaves (j : Fin leafCount) : List (Fin data.count) := leavesTable.get j.val

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record033" "{\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0015\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":9,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0021\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0018\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0026\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0024\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record033" 114

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record033" "{\"ridges\":[[2,134],[3,259],[3,261],[5,137],[5,138],[6,50],[8,259],[10,137],[10,140],[11,69],[11,84],[15,81],[15,112],[16,138],[16,140],[17,14],[17,518],[19,262],[21,580],[27,518],[28,50],[29,84],[32,549],[33,69],[33,579],[34,50],[35,90],[37,131],[37,138],[38,11],[38,546],[38,552],[39,579],[40,11],[40,137],[40,138],[40,259],[40,385],[41,50],[41,112],[42,50],[42,259],[42,273],[42,274],[45,60],[46,84],[48,549],[49,69],[49,76],[49,133],[49,140],[50,13],[50,524],[50,580],[50,584],[51,137],[51,140],[51,261],[51,385],[51,388],[52,84],[52,112],[53,69],[53,84],[53,261],[53,273],[53,276],[55,549],[56,41],[56,49],[56,73],[56,81],[56,104],[56,112],[58,60],[60,102],[61,518],[61,546],[62,518],[62,580],[63,138],[63,140],[64,134],[64,138],[64,518],[64,522],[64,524],[66,564],[67,518],[67,580],[67,594],[68,134],[68,274],[68,276],[68,386],[68,388],[69,102],[71,104],[71,546],[71,584],[71,608],[72,112],[72,546],[72,594],[73,60],[74,104],[74,580],[74,608],[75,112],[75,564]],\"owners\":[[38,11,[0,5,23,25,26,35,40],[4,27,34,36,39]],[40,11,[0,4,23,25,27,34,35,36,38,39],[5,26]],[50,13,[0,10,23,24,26,45,51],[9,27,46,47,48]],[17,14,[0,16,23,24,25,26,58,59,60,63],[61,62]],[37,131,[2,8,30,43],[5]],[49,133,[2,13,30,54],[10]],[64,134,[2,19,30,68],[16]],[42,259,[3,8,26,40],[7]],[53,261,[3,13,26,51],[12]],[19,262,[3,18,26],[63]],[56,41,[4,24,37,38,48],[14,34,45,47,57]],[5,137,[10,49,51],[37,40]],[10,137,[5,37,40],[49,51]],[40,137,[10,49],[5,37,51]],[51,137,[5,37],[10,40,49]],[5,138,[16,63,64],[37,40]],[16,138,[5,37,40],[63,64]],[37,138,[16,63,64],[5,40]],[40,138,[16,64],[5,37,63]],[63,138,[5,37],[16,40,64]],[64,138,[5,37,40],[16,63]],[56,49,[6,28,42],[15,34,45,52]],[6,50,[58,65,66,70,72],[28,34,41,42]],[28,50,[70,72],[6,34,41,42,58,65,66]],[34,50,[65,66,72],[6,28,41,42,58,70]],[41,50,[58,66],[6,28,34,42,65,70,72]],[42,50,[58,65,66,70,72],[6,28,34,41]],[42,273,[12,53,54],[7,43]],[53,273,[7,42,43],[12,54]],[42,274,[18,68],[7,43]],[68,274,[7,42],[18,43]],[40,385,[13,54],[8,43,51]],[51,385,[8,43],[13,40,54]],[68,386,[8,40],[19,43,63]],[56,73,[9,25,39,49,50],[14,35,36,46,57]],[49,76,[21,59,60,62,73,74],[9,25,46,47]],[10,140,[16,63,64],[49,51]],[16,140,[10,49,51],[63,64]],[49,140,[16,63,64],[10,51]],[51,140,[16,64],[10,49,63]],[63,140,[10,49],[16,51,64]],[15,81,[11,29,35,46,53],[41,56]],[56,81,[11,29,53],[15,35,41,46]],[11,84,[59,65,67,73,75],[29,46,52,53]],[29,84,[73,75],[11,46,52,53,59,65,67]],[46,84,[65,67,75],[11,29,52,53,59,73]],[52,84,[59,67],[11,29,46,53,65,73,75]],[53,84,[59,65,67,73,75],[11,29,46,52]],[53,276,[18,68],[12,54]],[68,276,[12,53],[18,54]],[51,388,[19,68],[13,54,63]],[68,388,[13,51],[19,54,63]],[56,104,[22,60,71,74],[14,36,47,70,73]],[71,104,[14,47,56,73],[22,36,60,70,74]],[74,104,[14,36,56,70],[22,47,60,71,73]],[15,112,[65,70,72,73,75],[41,52,56]],[41,112,[73,75],[15,52,56,65,70,72]],[52,112,[70,72],[15,41,56,65,73,75]],[56,112,[65,72,75],[15,41,52,70,73]],[72,112,[15,52,56,73],[41,65,70,75]],[75,112,[15,41,56,70],[52,65,72,73]],[17,518,[32,33,66,67,69],[27,61,62,64]],[27,518,[66,67,69],[17,32,33,61,62,64]],[61,518,[33,67],[17,27,32,62,64,66,69]],[62,518,[32,66],[17,27,33,61,64,67,69]],[64,518,[32,33,66,67,69],[17,27,61,62]],[67,518,[17,27,32,61,64],[33,62,66,69]],[64,522,[20,38,39,71],[17,27,62]],[50,524,[17,61,64],[21,27,48,74]],[64,524,[21,48,50,74],[17,27,61]],[38,546,[66,69,72],[20,32,44,61,71]],[61,546,[44,72],[20,32,38,66,69,71]],[71,546,[32,66],[20,38,44,61,69,72]],[72,546,[20,32,38,61],[44,66,69,71]],[38,552,[22,74],[20,48,57,61]],[21,580,[33,55,67,69,75],[50,62,74]],[50,580,[67,69,75],[21,33,55,62,74]],[62,580,[55,75],[21,33,50,67,69,74]],[67,580,[21,50,55,74],[33,62,69,75]],[74,580,[33,67],[21,50,55,62,69,75]],[50,584,[22,71],[21,39,57,62]],[71,584,[21,50],[22,39,57,62]],[71,608,[55,75],[22,44,57,69,72,74]],[74,608,[44,72],[22,55,57,69,71,75]],[60,102,[31,65,69],[]],[69,102,[31,60,65],[]],[32,549,[48,55],[]],[48,549,[32,55],[]],[55,549,[32,48],[]],[33,579,[39,44],[]],[39,579,[33,44],[]],[35,90,[59,70],[]],[45,60,[58,73],[]],[58,60,[45,73],[]],[73,60,[45,58],[]],[66,564,[75],[]],[75,564,[66],[]],[67,594,[72],[]],[72,594,[67],[]]],\"edges\":[[23,[17,21,27,32,33,48,50,55,61,62,64,66,67,69,74,75]],[27,[5,10,16,37,40,49,51,63,64]],[30,[6,15,28,34,41,42,45,52,56,58,65,66,70,72,73,75]],[31,[11,15,29,35,41,46,52,53,56,59,65,67,70,72,73,75]]],\"groupings\":[2,3]}"

facet_refute_shared% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record033" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record033\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-24,-5],[-25,-10],[-27,-16],[-29,-23],[-35,-33],[-37,-1],[-37,-23],[-37,-24],[-37,-25],[-37,-26],[-37,-27],[-37,-34],[-37,-36],[-38,-24],[-38,-27],[-38,-34],[-38,-36],[-38,-37],[-40,-2],[-40,-24],[-40,-30],[-40,-37],[-42,-29],[-42,-30],[-43,-40],[-43,-42],[-46,-23],[-49,-1],[-49,-23],[-49,-24],[-49,-25],[-49,-26],[-49,-27],[-49,-46],[-49,-47],[-49,-48],[-50,-27],[-50,-32],[-50,-38],[-50,-46],[-50,-47],[-50,-48],[-50,-49],[-51,-2],[-51,-25],[-51,-30],[-51,-49],[-53,-23],[-53,-28],[-53,-30],[-54,-51],[-54,-53],[-56,-23],[-56,-34],[-56,-41],[-56,-46],[-56,-52],[-57,-38],[-57,-50],[-59,-33],[-60,-50],[-61,-24],[-61,-27],[-61,-28],[-61,-38],[-61,-52],[-62,-29],[-62,-41],[-62,-50],[-63,-27],[-63,-30],[-64,-1],[-64,-23],[-64,-24],[-64,-25],[-64,-26],[-64,-27],[-64,-58],[-64,-59],[-64,-60],[-64,-61],[-64,-62],[-64,-63],[-66,-47],[-67,-25],[-67,-35],[-67,-36],[-68,-63],[-69,-24],[-69,-25],[-69,-36],[-69,-48],[-70,-33],[-70,-67],[-71,-29],[-71,-36],[-71,-38],[-71,-41],[-71,-57],[-74,-24],[-74,-28],[-74,-47],[-74,-50],[-74,-52],[-74,-57],[-74,-61],[-75,-47],[-75,-58],[-38,1,5,23,25,26,35,40],[-40,1,4,23,25,27,34,35,36,38,39],[-50,1,10,23,24,26,45,51],[-17,1,16,23,24,25,26,58,59,60,63],[-37,2,8,30,43],[-49,2,13,30,54],[-64,2,19,30,68],[-2,-64,-68],[-42,3,8,26,40],[-3,-8,-42],[-3,-40,-42],[-53,3,13,26,51],[-3,-51,-53],[-19,3,18,26],[-56,4,24,37,38,48],[-5,10,49,51],[-10,5,37,40],[-40,10,49],[-51,5,37],[-5,16,63,64],[-16,5,37,40],[-37,16,63,64],[-40,16,64],[-63,5,37],[-64,5,37,40],[-56,6,28,42],[-6,58,65,66,70,72],[-28,70,72],[-34,65,66,72],[-41,58,66],[-42,58,65,66,70,72],[-42,12,53,54],[-53,7,42,43],[-42,18,68],[-68,7,42],[-40,13,54],[-51,8,43],[-68,8,40],[-11,-33,-49],[-33,-49,-53],[-56,9,25,39,49,50],[-49,21,59,60,62,73,74],[-10,16,63,64],[-16,10,49,51],[-49,16,63,64],[-51,16,64],[-63,10,49],[-15,11,29,35,46,53],[-56,11,29,53],[-11,59,65,67,73,75],[-29,73,75],[-46,65,67,75],[-52,59,67],[-53,59,65,67,73,75],[-53,18,68],[-68,12,53],[-51,19,68],[-68,13,51],[-56,22,60,71,74],[-71,14,47,56,73],[-74,14,36,56,70],[-15,65,70,72,73,75],[-41,73,75],[-52,70,72],[-56,65,72,75],[-72,15,52,56,73],[-75,15,41,56,70],[-17,32,33,66,67,69],[-27,66,67,69],[-61,33,67],[-62,32,66],[-64,32,33,66,67,69],[-67,17,27,32,61,64],[-64,20,38,39,71],[-50,17,61,64],[-64,21,48,50,74],[-38,66,69,72],[-61,44,72],[-71,32,66],[-72,20,32,38,61],[-38,22,74],[-21,33,55,67,69,75],[-50,67,69,75],[-62,55,75],[-67,21,50,55,74],[-74,33,67],[-50,22,71],[-71,21,50],[-71,55,75],[-74,44,72],[-60,31,65,69],[-69,31,60,65],[-32,48,55],[-48,32,55],[-55,32,48],[-33,39,44],[-39,33,44],[-35,59,70],[-45,58,73],[-58,45,73],[-73,45,58],[-66,75],[-75,66],[-67,72],[-72,67],[-76,26,30,43,54,68],[-43,76],[-68,76],[-77,40,51,63],[-40,77],[-51,77],[-78,28,34,41,42],[-42,78],[-79,29,46,52,53],[-53,79],[-80,36,47,56,57],[-56,80],[-81,23,24,25,27,64],[-64,81],[-82,37,38],[-37,82],[-38,82],[-83,49,50],[-49,83],[-50,83],[-84,61,62,71,74],[-71,84],[-74,84],[-85,76,77],[-86,76],[-86,77],[-76,-77,86],[-87,78,79],[-88,78],[-88,79],[-78,-79,88],[-89,85],[-89,86,88],[-90,86],[-89,87],[-90,88],[-86,-88,90],[-91,80,81],[-92,80],[-92,81],[-80,-81,92],[-93,83,84],[-94,83],[-94,84],[-83,-84,94],[-95,82,94],[-96,82],[-95,93],[-96,94],[-82,-94,96],[-97,91],[-97,92,96],[-98,92],[-97,95],[-98,96],[-92,-96,98],[-99,89],[-99,90,98],[-99,97],[-90,-98,100],[99],[-100],[-31,101],[-32,101],[-45,101],[-66,101],[-33,102],[-60,102],[-67,102],[-48,103],[-58,103],[-65,103],[-75,103],[-39,104],[-55,104],[-69,104],[-44,105],[-59,105],[-72,105],[-70,106],[-73,106],[-103,107],[-102,107],[-102,-103,108],[-107,109],[-108,110],[-101,109],[-101,-107,110],[-106,111],[-105,111],[-111,112],[-104,112],[-104,-111,113],[-109,-113,114],[-110,-112,114],[-114],[-6,-7,-8,-37,-50,-51,-53,-56,-64,-66,-68,-71,-75],[-6,-7,-13,-38,-40,-49,-53,-56,-64,-67,-68,-72,-74],[-8,-18,-19,-37,-42,-50,-51,-53,-56,-64,-66,-71,-75],[-6,-18,-19,-37,-43,-50,-51,-53,-56,-64,-66,-71,-75],[-8,-14,-15,-37,-42,-50,-51,-53,-64,-66,-68,-71,-75],[-5,-8,-13,-38,-42,-49,-53,-56,-64,-67,-68,-72,-74],[-8,-13,-20,-37,-42,-49,-53,-56,-64,-67,-68,-72,-74],[-4,-5,-8,-42,-50,-51,-53,-56,-64,-66,-68,-71,-75],[-4,-10,-13,-40,-42,-50,-53,-56,-64,-66,-68,-71,-75],[-4,-13,-20,-40,-42,-49,-53,-56,-64,-67,-68,-72,-74],[-4,-13,-21,-40,-42,-49,-53,-56,-64,-66,-68,-71,-75],[-8,-20,-22,-37,-42,-50,-51,-53,-56,-64,-65,-68,-69],[-8,-20,-22,-37,-42,-50,-51,-53,-56,-64,-66,-68,-75],[-8,-20,-22,-37,-42,-50,-51,-53,-56,-64,-67,-68,-72],[-8,-16,-22,-37,-42,-50,-51,-53,-56,-61,-67,-68,-72],[-8,-16,-17,-37,-42,-50,-51,-53,-56,-66,-68,-71,-75],[-11,-12,-13,-38,-40,-42,-49,-56,-64,-67,-68,-72,-74],[-8,-11,-12,-37,-42,-50,-51,-56,-64,-66,-68,-71,-75],[-13,-18,-19,-38,-40,-42,-49,-53,-56,-64,-67,-72,-74],[-11,-18,-19,-38,-40,-42,-49,-54,-56,-64,-67,-72,-74],[-13,-14,-15,-38,-40,-42,-49,-53,-64,-67,-68,-72,-74],[-8,-10,-13,-37,-42,-50,-53,-56,-64,-66,-68,-71,-75],[-8,-13,-21,-37,-42,-49,-53,-56,-64,-66,-68,-71,-75],[-9,-10,-13,-38,-40,-42,-53,-56,-64,-67,-68,-72,-74],[-5,-8,-9,-38,-42,-51,-53,-56,-64,-67,-68,-72,-74],[-8,-9,-21,-37,-42,-51,-53,-56,-64,-66,-68,-71,-75],[-8,-9,-20,-37,-42,-51,-53,-56,-64,-67,-68,-72,-74],[-13,-21,-22,-38,-40,-42,-49,-53,-56,-64,-65,-68,-69],[-13,-21,-22,-38,-40,-42,-49,-53,-56,-64,-67,-68,-72],[-13,-21,-22,-38,-40,-42,-49,-53,-56,-64,-66,-68,-75],[-13,-16,-22,-38,-40,-42,-49,-53,-56,-62,-66,-68,-75],[-13,-16,-17,-38,-40,-42,-49,-53,-56,-67,-68,-72,-74],[17,21,27,32,33,48,50,55,61,62,64,66,67,69,74,75],[5,10,16,37,40,49,51,63,64],[6,15,28,34,41,42,45,52,56,58,65,66,70,72,73,75],[11,15,29,35,41,46,52,53,56,59,65,67,70,72,73,75]],\"atoms\":[{\"tag\":\"facet\",\"index\":0},{\"tag\":\"facet\",\"index\":2},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":4},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":6},{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":12},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":16},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":24},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":24,\"b\":5},{\"tag\":\"incompatible\",\"a\":25,\"b\":10},{\"tag\":\"incompatible\",\"a\":27,\"b\":16},{\"tag\":\"incompatible\",\"a\":29,\"b\":23},{\"tag\":\"incompatible\",\"a\":35,\"b\":33},{\"tag\":\"incompatible\",\"a\":37,\"b\":0},{\"tag\":\"incompatible\",\"a\":37,\"b\":23},{\"tag\":\"incompatible\",\"a\":37,\"b\":24},{\"tag\":\"incompatible\",\"a\":37,\"b\":25},{\"tag\":\"incompatible\",\"a\":37,\"b\":26},{\"tag\":\"incompatible\",\"a\":37,\"b\":27},{\"tag\":\"incompatible\",\"a\":37,\"b\":34},{\"tag\":\"incompatible\",\"a\":37,\"b\":36},{\"tag\":\"incompatible\",\"a\":38,\"b\":24},{\"tag\":\"incompatible\",\"a\":38,\"b\":27},{\"tag\":\"incompatible\",\"a\":38,\"b\":34},{\"tag\":\"incompatible\",\"a\":38,\"b\":36},{\"tag\":\"incompatible\",\"a\":38,\"b\":37},{\"tag\":\"incompatible\",\"a\":40,\"b\":2},{\"tag\":\"incompatible\",\"a\":40,\"b\":24},{\"tag\":\"incompatible\",\"a\":40,\"b\":30},{\"tag\":\"incompatible\",\"a\":40,\"b\":37},{\"tag\":\"incompatible\",\"a\":42,\"b\":29},{\"tag\":\"incompatible\",\"a\":42,\"b\":30},{\"tag\":\"incompatible\",\"a\":43,\"b\":40},{\"tag\":\"incompatible\",\"a\":43,\"b\":42},{\"tag\":\"incompatible\",\"a\":46,\"b\":23},{\"tag\":\"incompatible\",\"a\":49,\"b\":0},{\"tag\":\"incompatible\",\"a\":49,\"b\":23},{\"tag\":\"incompatible\",\"a\":49,\"b\":24},{\"tag\":\"incompatible\",\"a\":49,\"b\":25},{\"tag\":\"incompatible\",\"a\":49,\"b\":26},{\"tag\":\"incompatible\",\"a\":49,\"b\":27},{\"tag\":\"incompatible\",\"a\":49,\"b\":46},{\"tag\":\"incompatible\",\"a\":49,\"b\":47},{\"tag\":\"incompatible\",\"a\":49,\"b\":48},{\"tag\":\"incompatible\",\"a\":50,\"b\":27},{\"tag\":\"incompatible\",\"a\":50,\"b\":32},{\"tag\":\"incompatible\",\"a\":50,\"b\":38},{\"tag\":\"incompatible\",\"a\":50,\"b\":46},{\"tag\":\"incompatible\",\"a\":50,\"b\":47},{\"tag\":\"incompatible\",\"a\":50,\"b\":48},{\"tag\":\"incompatible\",\"a\":50,\"b\":49},{\"tag\":\"incompatible\",\"a\":51,\"b\":2},{\"tag\":\"incompatible\",\"a\":51,\"b\":25},{\"tag\":\"incompatible\",\"a\":51,\"b\":30},{\"tag\":\"incompatible\",\"a\":51,\"b\":49},{\"tag\":\"incompatible\",\"a\":53,\"b\":23},{\"tag\":\"incompatible\",\"a\":53,\"b\":28},{\"tag\":\"incompatible\",\"a\":53,\"b\":30},{\"tag\":\"incompatible\",\"a\":54,\"b\":51},{\"tag\":\"incompatible\",\"a\":54,\"b\":53},{\"tag\":\"incompatible\",\"a\":56,\"b\":23},{\"tag\":\"incompatible\",\"a\":56,\"b\":34},{\"tag\":\"incompatible\",\"a\":56,\"b\":41},{\"tag\":\"incompatible\",\"a\":56,\"b\":46},{\"tag\":\"incompatible\",\"a\":56,\"b\":52},{\"tag\":\"incompatible\",\"a\":57,\"b\":38},{\"tag\":\"incompatible\",\"a\":57,\"b\":50},{\"tag\":\"incompatible\",\"a\":59,\"b\":33},{\"tag\":\"incompatible\",\"a\":60,\"b\":50},{\"tag\":\"incompatible\",\"a\":61,\"b\":24},{\"tag\":\"incompatible\",\"a\":61,\"b\":27},{\"tag\":\"incompatible\",\"a\":61,\"b\":28},{\"tag\":\"incompatible\",\"a\":61,\"b\":38},{\"tag\":\"incompatible\",\"a\":61,\"b\":52},{\"tag\":\"incompatible\",\"a\":62,\"b\":29},{\"tag\":\"incompatible\",\"a\":62,\"b\":41},{\"tag\":\"incompatible\",\"a\":62,\"b\":50},{\"tag\":\"incompatible\",\"a\":63,\"b\":27},{\"tag\":\"incompatible\",\"a\":63,\"b\":30},{\"tag\":\"incompatible\",\"a\":64,\"b\":0},{\"tag\":\"incompatible\",\"a\":64,\"b\":23},{\"tag\":\"incompatible\",\"a\":64,\"b\":24},{\"tag\":\"incompatible\",\"a\":64,\"b\":25},{\"tag\":\"incompatible\",\"a\":64,\"b\":26},{\"tag\":\"incompatible\",\"a\":64,\"b\":27},{\"tag\":\"incompatible\",\"a\":64,\"b\":58},{\"tag\":\"incompatible\",\"a\":64,\"b\":59},{\"tag\":\"incompatible\",\"a\":64,\"b\":60},{\"tag\":\"incompatible\",\"a\":64,\"b\":61},{\"tag\":\"incompatible\",\"a\":64,\"b\":62},{\"tag\":\"incompatible\",\"a\":64,\"b\":63},{\"tag\":\"incompatible\",\"a\":66,\"b\":47},{\"tag\":\"incompatible\",\"a\":67,\"b\":25},{\"tag\":\"incompatible\",\"a\":67,\"b\":35},{\"tag\":\"incompatible\",\"a\":67,\"b\":36},{\"tag\":\"incompatible\",\"a\":68,\"b\":63},{\"tag\":\"incompatible\",\"a\":69,\"b\":24},{\"tag\":\"incompatible\",\"a\":69,\"b\":25},{\"tag\":\"incompatible\",\"a\":69,\"b\":36},{\"tag\":\"incompatible\",\"a\":69,\"b\":48},{\"tag\":\"incompatible\",\"a\":70,\"b\":33},{\"tag\":\"incompatible\",\"a\":70,\"b\":67},{\"tag\":\"incompatible\",\"a\":71,\"b\":29},{\"tag\":\"incompatible\",\"a\":71,\"b\":36},{\"tag\":\"incompatible\",\"a\":71,\"b\":38},{\"tag\":\"incompatible\",\"a\":71,\"b\":41},{\"tag\":\"incompatible\",\"a\":71,\"b\":57},{\"tag\":\"incompatible\",\"a\":74,\"b\":24},{\"tag\":\"incompatible\",\"a\":74,\"b\":28},{\"tag\":\"incompatible\",\"a\":74,\"b\":47},{\"tag\":\"incompatible\",\"a\":74,\"b\":50},{\"tag\":\"incompatible\",\"a\":74,\"b\":52},{\"tag\":\"incompatible\",\"a\":74,\"b\":57},{\"tag\":\"incompatible\",\"a\":74,\"b\":61},{\"tag\":\"incompatible\",\"a\":75,\"b\":47},{\"tag\":\"incompatible\",\"a\":75,\"b\":58},{\"tag\":\"mate\",\"ridge\":11,\"a\":38,\"owners\":[0,5,23,25,26,35,40]},{\"tag\":\"mate\",\"ridge\":11,\"a\":40,\"owners\":[0,4,23,25,27,34,35,36,38,39]},{\"tag\":\"mate\",\"ridge\":13,\"a\":50,\"owners\":[0,10,23,24,26,45,51]},{\"tag\":\"mate\",\"ridge\":14,\"a\":17,\"owners\":[0,16,23,24,25,26,58,59,60,63]},{\"tag\":\"mate\",\"ridge\":131,\"a\":37,\"owners\":[2,8,30,43]},{\"tag\":\"mate\",\"ridge\":133,\"a\":49,\"owners\":[2,13,30,54]},{\"tag\":\"mate\",\"ridge\":134,\"a\":64,\"owners\":[2,19,30,68]},{\"tag\":\"three\",\"ridge\":134,\"vertices\":[2,64,68]},{\"tag\":\"mate\",\"ridge\":259,\"a\":42,\"owners\":[3,8,26,40]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[3,8,42]},{\"tag\":\"three\",\"ridge\":259,\"vertices\":[3,40,42]},{\"tag\":\"mate\",\"ridge\":261,\"a\":53,\"owners\":[3,13,26,51]},{\"tag\":\"three\",\"ridge\":261,\"vertices\":[3,51,53]},{\"tag\":\"mate\",\"ridge\":262,\"a\":19,\"owners\":[3,18,26]},{\"tag\":\"mate\",\"ridge\":41,\"a\":56,\"owners\":[4,24,37,38,48]},{\"tag\":\"mate\",\"ridge\":137,\"a\":5,\"owners\":[10,49,51]},{\"tag\":\"mate\",\"ridge\":137,\"a\":10,\"owners\":[5,37,40]},{\"tag\":\"mate\",\"ridge\":137,\"a\":40,\"owners\":[10,49]},{\"tag\":\"mate\",\"ridge\":137,\"a\":51,\"owners\":[5,37]},{\"tag\":\"mate\",\"ridge\":138,\"a\":5,\"owners\":[16,63,64]},{\"tag\":\"mate\",\"ridge\":138,\"a\":16,\"owners\":[5,37,40]},{\"tag\":\"mate\",\"ridge\":138,\"a\":37,\"owners\":[16,63,64]},{\"tag\":\"mate\",\"ridge\":138,\"a\":40,\"owners\":[16,64]},{\"tag\":\"mate\",\"ridge\":138,\"a\":63,\"owners\":[5,37]},{\"tag\":\"mate\",\"ridge\":138,\"a\":64,\"owners\":[5,37,40]},{\"tag\":\"mate\",\"ridge\":49,\"a\":56,\"owners\":[6,28,42]},{\"tag\":\"mate\",\"ridge\":50,\"a\":6,\"owners\":[58,65,66,70,72]},{\"tag\":\"mate\",\"ridge\":50,\"a\":28,\"owners\":[70,72]},{\"tag\":\"mate\",\"ridge\":50,\"a\":34,\"owners\":[65,66,72]},{\"tag\":\"mate\",\"ridge\":50,\"a\":41,\"owners\":[58,66]},{\"tag\":\"mate\",\"ridge\":50,\"a\":42,\"owners\":[58,65,66,70,72]},{\"tag\":\"mate\",\"ridge\":273,\"a\":42,\"owners\":[12,53,54]},{\"tag\":\"mate\",\"ridge\":273,\"a\":53,\"owners\":[7,42,43]},{\"tag\":\"mate\",\"ridge\":274,\"a\":42,\"owners\":[18,68]},{\"tag\":\"mate\",\"ridge\":274,\"a\":68,\"owners\":[7,42]},{\"tag\":\"mate\",\"ridge\":385,\"a\":40,\"owners\":[13,54]},{\"tag\":\"mate\",\"ridge\":385,\"a\":51,\"owners\":[8,43]},{\"tag\":\"mate\",\"ridge\":386,\"a\":68,\"owners\":[8,40]},{\"tag\":\"three\",\"ridge\":69,\"vertices\":[11,33,49]},{\"tag\":\"three\",\"ridge\":69,\"vertices\":[33,49,53]},{\"tag\":\"mate\",\"ridge\":73,\"a\":56,\"owners\":[9,25,39,49,50]},{\"tag\":\"mate\",\"ridge\":76,\"a\":49,\"owners\":[21,59,60,62,73,74]},{\"tag\":\"mate\",\"ridge\":140,\"a\":10,\"owners\":[16,63,64]},{\"tag\":\"mate\",\"ridge\":140,\"a\":16,\"owners\":[10,49,51]},{\"tag\":\"mate\",\"ridge\":140,\"a\":49,\"owners\":[16,63,64]},{\"tag\":\"mate\",\"ridge\":140,\"a\":51,\"owners\":[16,64]},{\"tag\":\"mate\",\"ridge\":140,\"a\":63,\"owners\":[10,49]},{\"tag\":\"mate\",\"ridge\":81,\"a\":15,\"owners\":[11,29,35,46,53]},{\"tag\":\"mate\",\"ridge\":81,\"a\":56,\"owners\":[11,29,53]},{\"tag\":\"mate\",\"ridge\":84,\"a\":11,\"owners\":[59,65,67,73,75]},{\"tag\":\"mate\",\"ridge\":84,\"a\":29,\"owners\":[73,75]},{\"tag\":\"mate\",\"ridge\":84,\"a\":46,\"owners\":[65,67,75]},{\"tag\":\"mate\",\"ridge\":84,\"a\":52,\"owners\":[59,67]},{\"tag\":\"mate\",\"ridge\":84,\"a\":53,\"owners\":[59,65,67,73,75]},{\"tag\":\"mate\",\"ridge\":276,\"a\":53,\"owners\":[18,68]},{\"tag\":\"mate\",\"ridge\":276,\"a\":68,\"owners\":[12,53]},{\"tag\":\"mate\",\"ridge\":388,\"a\":51,\"owners\":[19,68]},{\"tag\":\"mate\",\"ridge\":388,\"a\":68,\"owners\":[13,51]},{\"tag\":\"mate\",\"ridge\":104,\"a\":56,\"owners\":[22,60,71,74]},{\"tag\":\"mate\",\"ridge\":104,\"a\":71,\"owners\":[14,47,56,73]},{\"tag\":\"mate\",\"ridge\":104,\"a\":74,\"owners\":[14,36,56,70]},{\"tag\":\"mate\",\"ridge\":112,\"a\":15,\"owners\":[65,70,72,73,75]},{\"tag\":\"mate\",\"ridge\":112,\"a\":41,\"owners\":[73,75]},{\"tag\":\"mate\",\"ridge\":112,\"a\":52,\"owners\":[70,72]},{\"tag\":\"mate\",\"ridge\":112,\"a\":56,\"owners\":[65,72,75]},{\"tag\":\"mate\",\"ridge\":112,\"a\":72,\"owners\":[15,52,56,73]},{\"tag\":\"mate\",\"ridge\":112,\"a\":75,\"owners\":[15,41,56,70]},{\"tag\":\"mate\",\"ridge\":518,\"a\":17,\"owners\":[32,33,66,67,69]},{\"tag\":\"mate\",\"ridge\":518,\"a\":27,\"owners\":[66,67,69]},{\"tag\":\"mate\",\"ridge\":518,\"a\":61,\"owners\":[33,67]},{\"tag\":\"mate\",\"ridge\":518,\"a\":62,\"owners\":[32,66]},{\"tag\":\"mate\",\"ridge\":518,\"a\":64,\"owners\":[32,33,66,67,69]},{\"tag\":\"mate\",\"ridge\":518,\"a\":67,\"owners\":[17,27,32,61,64]},{\"tag\":\"mate\",\"ridge\":522,\"a\":64,\"owners\":[20,38,39,71]},{\"tag\":\"mate\",\"ridge\":524,\"a\":50,\"owners\":[17,61,64]},{\"tag\":\"mate\",\"ridge\":524,\"a\":64,\"owners\":[21,48,50,74]},{\"tag\":\"mate\",\"ridge\":546,\"a\":38,\"owners\":[66,69,72]},{\"tag\":\"mate\",\"ridge\":546,\"a\":61,\"owners\":[44,72]},{\"tag\":\"mate\",\"ridge\":546,\"a\":71,\"owners\":[32,66]},{\"tag\":\"mate\",\"ridge\":546,\"a\":72,\"owners\":[20,32,38,61]},{\"tag\":\"mate\",\"ridge\":552,\"a\":38,\"owners\":[22,74]},{\"tag\":\"mate\",\"ridge\":580,\"a\":21,\"owners\":[33,55,67,69,75]},{\"tag\":\"mate\",\"ridge\":580,\"a\":50,\"owners\":[67,69,75]},{\"tag\":\"mate\",\"ridge\":580,\"a\":62,\"owners\":[55,75]},{\"tag\":\"mate\",\"ridge\":580,\"a\":67,\"owners\":[21,50,55,74]},{\"tag\":\"mate\",\"ridge\":580,\"a\":74,\"owners\":[33,67]},{\"tag\":\"mate\",\"ridge\":584,\"a\":50,\"owners\":[22,71]},{\"tag\":\"mate\",\"ridge\":584,\"a\":71,\"owners\":[21,50]},{\"tag\":\"mate\",\"ridge\":608,\"a\":71,\"owners\":[55,75]},{\"tag\":\"mate\",\"ridge\":608,\"a\":74,\"owners\":[44,72]},{\"tag\":\"mate\",\"ridge\":102,\"a\":60,\"owners\":[31,65,69]},{\"tag\":\"mate\",\"ridge\":102,\"a\":69,\"owners\":[31,60,65]},{\"tag\":\"mate\",\"ridge\":549,\"a\":32,\"owners\":[48,55]},{\"tag\":\"mate\",\"ridge\":549,\"a\":48,\"owners\":[32,55]},{\"tag\":\"mate\",\"ridge\":549,\"a\":55,\"owners\":[32,48]},{\"tag\":\"mate\",\"ridge\":579,\"a\":33,\"owners\":[39,44]},{\"tag\":\"mate\",\"ridge\":579,\"a\":39,\"owners\":[33,44]},{\"tag\":\"mate\",\"ridge\":90,\"a\":35,\"owners\":[59,70]},{\"tag\":\"mate\",\"ridge\":60,\"a\":45,\"owners\":[58,73]},{\"tag\":\"mate\",\"ridge\":60,\"a\":58,\"owners\":[45,73]},{\"tag\":\"mate\",\"ridge\":60,\"a\":73,\"owners\":[45,58]},{\"tag\":\"mate\",\"ridge\":564,\"a\":66,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":564,\"a\":75,\"owners\":[66]},{\"tag\":\"mate\",\"ridge\":594,\"a\":67,\"owners\":[72]},{\"tag\":\"mate\",\"ridge\":594,\"a\":72,\"owners\":[67]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[26,30,43,54,68],\"full_literals\":[-76,26,30,43,54,68]},{\"tag\":\"group_take\",\"kind\":2,\"index\":0,\"member\":43,\"full_literals\":[-43,76]},{\"tag\":\"group_take\",\"kind\":2,\"index\":0,\"member\":68,\"full_literals\":[-68,76]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[40,51,63],\"full_literals\":[-77,40,51,63]},{\"tag\":\"group_take\",\"kind\":2,\"index\":1,\"member\":40,\"full_literals\":[-40,77]},{\"tag\":\"group_take\",\"kind\":2,\"index\":1,\"member\":51,\"full_literals\":[-51,77]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[28,34,41,42],\"full_literals\":[-78,28,34,41,42]},{\"tag\":\"group_take\",\"kind\":2,\"index\":2,\"member\":42,\"full_literals\":[-42,78]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[29,46,52,53],\"full_literals\":[-79,29,46,52,53]},{\"tag\":\"group_take\",\"kind\":2,\"index\":3,\"member\":53,\"full_literals\":[-53,79]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[36,47,56,57],\"full_literals\":[-80,36,47,56,57]},{\"tag\":\"group_take\",\"kind\":2,\"index\":4,\"member\":56,\"full_literals\":[-56,80]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[23,24,25,27,64],\"full_literals\":[-81,23,24,25,27,64]},{\"tag\":\"group_take\",\"kind\":2,\"index\":5,\"member\":64,\"full_literals\":[-64,81]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[37,38],\"full_literals\":[-82,37,38]},{\"tag\":\"group_take\",\"kind\":2,\"index\":6,\"member\":37,\"full_literals\":[-37,82]},{\"tag\":\"group_take\",\"kind\":2,\"index\":6,\"member\":38,\"full_literals\":[-38,82]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[49,50],\"full_literals\":[-83,49,50]},{\"tag\":\"group_take\",\"kind\":2,\"index\":7,\"member\":49,\"full_literals\":[-49,83]},{\"tag\":\"group_take\",\"kind\":2,\"index\":7,\"member\":50,\"full_literals\":[-50,83]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[61,62,71,74],\"full_literals\":[-84,61,62,71,74]},{\"tag\":\"group_take\",\"kind\":2,\"index\":8,\"member\":71,\"full_literals\":[-71,84]},{\"tag\":\"group_take\",\"kind\":2,\"index\":8,\"member\":74,\"full_literals\":[-74,84]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-85,76,77],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-86,76,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-86,false,77],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-76,-77,86],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-87,78,79],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-88,78,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-88,false,79],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-78,-79,88],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-89,85,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-89,86,88],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-90,86,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-89,false,87],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-90,false,88],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-86,-88,90],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-91,80,81],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-92,80,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-92,false,81],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-80,-81,92],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-93,83,84],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-94,83,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-94,false,84],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0014\",\"right_name\":\"grouped2_0016\",\"joined_name\":\"grouped2_0015\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-83,-84,94],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-95,82,94],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-96,82,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-95,false,93],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-96,false,94],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0015\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-82,-94,96],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":0,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-97,91,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-97,92,96],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-98,92,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-97,false,95],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-98,false,96],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-92,-96,98],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":2,\"b\":5,\"direction\":\"backward\",\"full_literals\":[-99,89,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-99,90,98],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-99,false,97],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":5,\"direction\":\"forward\",\"full_literals\":[-90,-98,100],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"quota_upper\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":31,\"full_literals\":[-31,101]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":32,\"full_literals\":[-32,101]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":45,\"full_literals\":[-45,101]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":66,\"full_literals\":[-66,101]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":33,\"full_literals\":[-33,102]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":60,\"full_literals\":[-60,102]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":67,\"full_literals\":[-67,102]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":48,\"full_literals\":[-48,103]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":58,\"full_literals\":[-58,103]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":65,\"full_literals\":[-65,103]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":75,\"full_literals\":[-75,103]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":39,\"full_literals\":[-39,104]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":55,\"full_literals\":[-55,104]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":69,\"full_literals\":[-69,104]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":44,\"full_literals\":[-44,105]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":59,\"full_literals\":[-59,105]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":72,\"full_literals\":[-72,105]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":70,\"full_literals\":[-70,106]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":73,\"full_literals\":[-73,106]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-103,107],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-102,false,107],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0020\",\"right_name\":\"grouped3_0022\",\"joined_name\":\"grouped3_0021\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-102,-103,108],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-107,109],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0018\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-108,110],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-101,false,109],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0017\",\"right_name\":\"grouped3_0021\",\"joined_name\":\"grouped3_0018\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-101,-107,110],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-106,111],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0025\",\"right_name\":\"grouped3_0027\",\"joined_name\":\"grouped3_0026\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-105,false,111],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-111,112],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-104,false,112],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0023\",\"right_name\":\"grouped3_0026\",\"joined_name\":\"grouped3_0024\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-104,-111,113],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-109,-113,114],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0018\",\"right_name\":\"grouped3_0024\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-110,-112,114],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"block\",\"leaf\":0,\"vertices\":[6,7,8,37,50,51,53,56,64,66,68,71,75]},{\"tag\":\"block\",\"leaf\":1,\"vertices\":[6,7,13,38,40,49,53,56,64,67,68,72,74]},{\"tag\":\"block\",\"leaf\":2,\"vertices\":[8,18,19,37,42,50,51,53,56,64,66,71,75]},{\"tag\":\"block\",\"leaf\":3,\"vertices\":[6,18,19,37,43,50,51,53,56,64,66,71,75]},{\"tag\":\"block\",\"leaf\":4,\"vertices\":[8,14,15,37,42,50,51,53,64,66,68,71,75]},{\"tag\":\"block\",\"leaf\":5,\"vertices\":[5,8,13,38,42,49,53,56,64,67,68,72,74]},{\"tag\":\"block\",\"leaf\":6,\"vertices\":[8,13,20,37,42,49,53,56,64,67,68,72,74]},{\"tag\":\"block\",\"leaf\":7,\"vertices\":[4,5,8,42,50,51,53,56,64,66,68,71,75]},{\"tag\":\"block\",\"leaf\":8,\"vertices\":[4,10,13,40,42,50,53,56,64,66,68,71,75]},{\"tag\":\"block\",\"leaf\":9,\"vertices\":[4,13,20,40,42,49,53,56,64,67,68,72,74]},{\"tag\":\"block\",\"leaf\":10,\"vertices\":[4,13,21,40,42,49,53,56,64,66,68,71,75]},{\"tag\":\"block\",\"leaf\":11,\"vertices\":[8,20,22,37,42,50,51,53,56,64,65,68,69]},{\"tag\":\"block\",\"leaf\":12,\"vertices\":[8,20,22,37,42,50,51,53,56,64,66,68,75]},{\"tag\":\"block\",\"leaf\":13,\"vertices\":[8,20,22,37,42,50,51,53,56,64,67,68,72]},{\"tag\":\"block\",\"leaf\":14,\"vertices\":[8,16,22,37,42,50,51,53,56,61,67,68,72]},{\"tag\":\"block\",\"leaf\":15,\"vertices\":[8,16,17,37,42,50,51,53,56,66,68,71,75]},{\"tag\":\"block\",\"leaf\":16,\"vertices\":[11,12,13,38,40,42,49,56,64,67,68,72,74]},{\"tag\":\"block\",\"leaf\":17,\"vertices\":[8,11,12,37,42,50,51,56,64,66,68,71,75]},{\"tag\":\"block\",\"leaf\":18,\"vertices\":[13,18,19,38,40,42,49,53,56,64,67,72,74]},{\"tag\":\"block\",\"leaf\":19,\"vertices\":[11,18,19,38,40,42,49,54,56,64,67,72,74]},{\"tag\":\"block\",\"leaf\":20,\"vertices\":[13,14,15,38,40,42,49,53,64,67,68,72,74]},{\"tag\":\"block\",\"leaf\":21,\"vertices\":[8,10,13,37,42,50,53,56,64,66,68,71,75]},{\"tag\":\"block\",\"leaf\":22,\"vertices\":[8,13,21,37,42,49,53,56,64,66,68,71,75]},{\"tag\":\"block\",\"leaf\":23,\"vertices\":[9,10,13,38,40,42,53,56,64,67,68,72,74]},{\"tag\":\"block\",\"leaf\":24,\"vertices\":[5,8,9,38,42,51,53,56,64,67,68,72,74]},{\"tag\":\"block\",\"leaf\":25,\"vertices\":[8,9,21,37,42,51,53,56,64,66,68,71,75]},{\"tag\":\"block\",\"leaf\":26,\"vertices\":[8,9,20,37,42,51,53,56,64,67,68,72,74]},{\"tag\":\"block\",\"leaf\":27,\"vertices\":[13,21,22,38,40,42,49,53,56,64,65,68,69]},{\"tag\":\"block\",\"leaf\":28,\"vertices\":[13,21,22,38,40,42,49,53,56,64,67,68,72]},{\"tag\":\"block\",\"leaf\":29,\"vertices\":[13,21,22,38,40,42,49,53,56,64,66,68,75]},{\"tag\":\"block\",\"leaf\":30,\"vertices\":[13,16,22,38,40,42,49,53,56,62,66,68,75]},{\"tag\":\"block\",\"leaf\":31,\"vertices\":[13,16,17,38,40,42,49,53,56,67,68,72,74]},{\"tag\":\"edge\",\"edge\":23,\"owners\":[17,21,27,32,33,48,50,55,61,62,64,66,67,69,74,75]},{\"tag\":\"edge\",\"edge\":27,\"owners\":[5,10,16,37,40,49,51,63,64]},{\"tag\":\"edge\",\"edge\":30,\"owners\":[6,15,28,34,41,42,45,52,56,58,65,66,70,72,73,75]},{\"tag\":\"edge\",\"edge\":31,\"owners\":[11,15,29,35,41,46,52,53,56,59,65,67,70,72,73,75]}]}"
  "346 89 0 274 270 0\n347 97 0 274 272 0\n348 85 0 346 245 0\n349 87 0 346 248 0\n350 91 0 347 264 0\n351 95 0 347 267 0\n352 93 0 351 261 0\n353 109 0 298 300 295 296 276 277 279 283 285 286 280 281 282 179 203 200 178 194 180 190 191 177 176 342 0\n354 -113 0 353 309 307 0\n355 107 104 0 289 288 295 296 283 286 280 282 201 210 192 190 178 194 180 191 177 176 342 0\n356 84 64 27 50 0 352 347 257 255 262 231 265 29 30 31 253 226 0\n357 -61 67 103 101 0 279 211 285 213 173 137 284 138 278 209 64 66 178 93 170 135 139 344 0\n358 67 74 103 101 69 0 352 279 211 278 284 209 159 138 285 277 187 179 213 191 177 160 173 357 234 255 356 231 79 180 147 148 161 5 93 156 345 0\n359 -49 63 56 94 36 0 351 347 274 262 268 271 247 239 265 252 259 35 47 224 217 58 22 228 0\n360 -50 56 -80 36 0 41 59 224 0\n361 56 84 -67 0 352 347 257 262 265 253 252 255 87 85 360 231 29 30 33 359 226 83 0\n362 50 -42 -53 -22 -56 -77 -76 -81 -82 -83 -67 74 55 0 26 52 50 53 212 85 193 231 30 32 33 47 226 214 83 166 217 338 22 228 0\n363 61 -67 74 29 60 41 71 62 32 55 0 352 351 347 274 212 85 234 257 255 262 259 268 265 271 253 247 249 238 239 242 243 361 53 54 56 57 167 222 49 50 52 220 26 362 37 39 188 228 8 10 22 226 214 146 83 323 217 0\n364 -56 -61 -67 74 29 60 41 71 0 347 274 81 66 65 64 63 62 212 85 53 54 56 167 226 253 265 266 260 262 271 228 256 247 249 10 22 238 239 242 243 220 222 24 26 52 214 88 146 130 217 324 47 231 0\n365 -49 64 52 38 28 27 24 25 29 41 0 347 274 29 32 34 47 226 253 265 266 260 271 228 247 249 12 22 238 239 242 243 217 220 222 71 88 26 52 214 0\n366 94 64 38 27 24 25 0 351 347 262 259 265 228 253 7 226 0\n367 74 103 101 69 55 0 350 347 279 211 278 284 209 159 276 285 199 138 277 187 179 358 85 87 363 62 63 64 65 66 81 364 365 366 256 231 360 251 252 226 265 7 260 228 0\n368 64 -49 -67 -74 29 41 32 0 350 274 47 34 33 32 29 212 87 85 106 105 104 102 101 100 181 365 226 16 253 251 266 224 271 247 249 238 239 242 243 220 222 24 26 52 214 88 166 153 217 341 0\n369 92 -64 -49 -67 -74 29 41 73 0 347 274 227 83 47 34 32 212 94 87 104 101 265 266 254 260 271 225 247 249 174 169 238 239 242 243 217 222 19 21 22 25 52 114 228 214 16 330 220 0\n370 42 -53 -40 -38 -56 -64 -49 -67 -74 41 0 346 52 144 25 21 54 32 212 101 141 220 134 242 311 246 214 238 0\n371 -53 -77 90 -38 -56 -64 -49 -67 -74 41 0 47 83 217 21 19 212 52 223 144 370 221 244 250 240 216 142 115 328 0\n372 68 -76 -42 -11 -40 -38 -56 -64 -49 -67 -74 0 25 21 19 32 212 142 115 214 329 0\n373 -77 90 -38 -56 -64 -49 -67 -74 29 41 0 349 346 54 83 47 34 212 104 101 217 371 222 157 243 241 246 220 238 372 164 166 326 0\n374 -38 -92 -64 -49 -94 -67 -74 29 41 0 275 348 346 102 105 87 252 224 54 47 34 32 212 104 101 18 230 263 269 273 373 218 239 237 133 246 242 243 220 222 24 26 52 214 166 146 315 0\n375 77 -20 38 -56 -64 -49 -67 -74 29 41 0 348 346 274 54 47 34 32 212 104 101 218 239 237 246 247 242 243 271 220 222 268 24 26 52 260 214 228 166 146 316 0\n376 -83 -67 -74 29 41 73 32 39 0 274 212 87 86 85 236 106 105 104 103 102 101 258 231 28 29 32 33 34 47 368 83 369 252 224 54 374 188 375 217 21 22 25 110 228 260 268 271 247 249 238 242 243 220 222 119 52 120 214 319 0\n377 38 -68 -64 -53 -42 -9 -77 -56 -82 -67 -74 32 0 116 83 26 24 212 106 188 228 22 113 217 336 0\n378 40 -38 -68 -64 -53 -42 -9 -77 -56 -67 -74 0 83 76 72 53 212 86 85 217 109 146 334 0\n379 -64 -53 -42 -9 -77 -76 -56 -82 49 -67 -74 32 0 52 26 24 212 76 214 377 378 126 144 333 0\n380 -67 -74 29 41 73 32 39 0 351 347 274 105 104 103 102 101 100 85 87 376 232 256 262 259 268 265 271 252 253 247 249 224 238 239 242 243 53 54 56 149 220 222 379 226 11 15 228 0\n381 103 101 69 55 39 0 279 211 278 277 284 285 209 138 159 367 104 380 213 194 160 173 5 60 93 158 162 170 345 0\n382 104 110 0 299 287 288 289 355 301 277 279 202 211 179 381 297 280 282 190 176 178 180 194 191 177 342 0\n383 69 84 66 32 33 67 0 211 191 180 177 356 0\n384 50 64 84 0 352 255 356 231 33 0\n385 64 25 24 84 0 257 384 37 39 366 0\n386 -50 -64 -65 -69 -79 -78 -77 -76 -80 -82 29 41 71 39 111 0 83 76 91 303 292 302 293 172 136 39 40 195 360 182 228 222 54 22 50 52 220 217 26 145 214 321 0\n387 -103 110 0 354 352 351 347 274 382 306 303 290 292 198 212 186 302 293 172 136 294 299 295 297 301 280 281 276 277 278 279 205 208 211 179 187 138 159 234 257 255 262 259 268 265 271 252 247 249 238 239 242 243 383 89 90 91 92 200 385 76 83 386 184 231 34 47 359 222 217 54 167 50 52 22 25 144 220 228 214 337 0\n388 110 0 354 382 306 302 303 293 294 291 292 172 206 212 387 285 286 173 160 170 158 162 159 171 345 0\n389 -112 0 388 309 308 0\n390 -111 0 389 304 0\n391 -104 0 389 305 0\n392 -106 0 390 302 0\n393 -105 0 390 303 0\n394 -39 0 391 287 0\n395 -55 0 391 288 0\n396 -69 0 391 289 0\n397 -70 0 392 293 0\n398 -73 0 392 294 0\n399 -44 0 393 290 0\n400 -59 0 393 291 0\n401 -72 0 393 292 0\n402 -33 0 394 399 204 0\n403 -28 0 397 401 136 0\n404 -52 0 397 401 172 0\n405 -35 0 397 400 206 0\n406 -61 0 399 401 186 0\n407 -67 0 401 212 0\n408 -74 0 401 399 198 0\n409 84 50 -64 0 352 351 400 398 274 395 402 407 396 408 403 404 83 82 80 76 257 255 262 259 231 268 34 36 47 150 271 201 190 247 249 180 238 239 242 243 217 21 22 25 228 16 17 189 359 55 220 23 119 222 120 52 339 214 0\n410 94 50 -64 0 408 406 395 351 347 274 394 403 404 82 409 234 197 211 107 196 99 98 97 96 95 83 76 75 262 259 258 268 265 228 232 271 252 12 22 247 249 224 238 239 242 243 56 149 217 220 222 44 46 51 26 113 214 335 0\n411 -40 -53 -56 50 -64 0 408 406 395 394 405 274 403 52 50 54 410 256 231 82 409 234 197 211 196 98 97 96 77 76 75 73 72 22 25 110 144 228 260 268 271 247 249 238 242 214 220 320 0\n412 -53 -56 50 -64 0 408 406 395 348 346 274 403 54 410 256 231 47 82 409 234 197 211 196 98 97 83 76 50 52 411 217 239 237 246 247 242 271 220 268 26 260 214 228 146 166 332 0\n413 88 51 38 63 0 346 274 249 246 271 239 268 217 260 22 228 0\n414 50 -64 0 406 408 395 404 347 274 83 82 409 234 95 96 97 99 197 107 410 256 231 34 47 413 243 222 412 224 252 265 266 260 271 228 247 22 239 217 0\n415 -96 98 -79 -78 -51 -37 -76 -64 0 396 407 402 406 408 397 398 404 403 51 46 22 12 414 38 180 191 41 40 227 82 76 262 269 257 254 234 225 95 98 175 168 222 220 121 26 117 214 314 0\n416 -88 -51 -82 -86 -64 0 396 407 402 275 347 408 394 403 404 51 46 414 39 228 13 12 238 38 180 191 233 40 80 76 242 243 250 273 415 265 263 252 258 360 235 55 167 182 220 23 26 222 145 214 322 0\n417 -68 42 -53 -71 -56 -51 -37 -64 0 396 407 402 403 134 22 414 38 180 191 146 143 310 0\n418 -79 88 -51 -37 -76 -64 0 396 407 402 274 408 406 404 403 82 249 271 268 262 257 234 95 13 414 266 252 360 51 46 38 180 191 40 76 244 222 221 134 417 163 165 214 313 0\n419 -82 -86 -77 -64 0 396 407 402 274 406 408 349 403 238 414 38 180 191 39 83 82 76 228 12 13 22 217 46 51 416 249 271 266 268 252 262 360 257 55 234 95 418 223 241 157 220 26 140 145 214 327 0\n420 40 -86 -77 -64 0 396 407 402 347 403 274 351 408 406 404 238 414 40 82 419 259 257 234 95 260 268 271 249 243 222 52 76 98 96 265 252 360 54 242 220 24 26 214 42 39 74 229 123 38 180 191 83 217 133 146 317 0\n421 -86 -77 -64 0 396 407 402 351 347 406 408 274 403 404 414 38 180 191 43 42 40 39 82 76 74 238 419 229 259 260 257 268 265 234 271 252 95 96 98 249 360 242 243 54 123 220 222 24 26 52 214 420 126 144 318 0\n422 -77 -64 0 396 407 402 346 274 406 408 404 403 414 38 180 191 40 39 83 82 76 421 246 247 240 242 243 271 215 216 266 268 252 260 262 228 257 12 13 22 234 360 217 95 98 145 165 222 220 118 122 312 0\n423 -64 0 398 402 407 396 348 274 406 408 404 403 72 73 74 76 78 82 83 207 414 38 39 40 191 180 422 218 219 239 237 111 413 247 242 243 271 266 268 252 260 262 228 257 12 13 234 360 95 98 222 220 50 52 26 214 146 166 331 0\n424 -37 -81 0 423 7 8 9 11 226 0\n425 -98 0 423 266 268 253 260 262 256 424 228 14 15 39 231 29 31 226 0\n426 90 0 425 274 271 0\n427 86 0 426 247 0\n428 88 0 426 249 0\n429 76 0 427 238 0\n430 77 0 427 239 0\n431 78 0 428 242 0\n432 79 0 428 243 0\n433 -23 0 404 432 4 27 48 222 0\n434 -27 37 0 423 3 33 70 128 151 131 154 343 0\n435 -25 37 0 423 2 31 45 124 126 152 155 343 0\n436 -24 37 0 423 1 20 30 125 127 129 132 343 0\n437 37 0 433 350 347 401 396 406 408 404 432 431 403 429 423 430 434 435 436 226 385 253 251 265 260 262 228 256 16 17 39 58 97 185 189 231 234 84 210 32 34 47 67 68 224 222 220 50 52 26 214 88 166 153 217 340 0\n438 -1 0 437 6 0\n439 -24 0 437 8 0\n440 -25 0 437 9 0\n441 -26 0 437 10 0\n442 -27 0 437 11 0\n443 -34 0 437 12 0\n444 -36 0 437 13 0\n445 -38 0 437 18 0\n446 -40 0 437 22 0\n447 -81 0 437 424 0\n448 84 0 439 423 440 385 0\n449 94 0 445 442 423 439 440 366 0\n450 80 0 447 350 251 0\n451 83 0 449 256 0\n452 -62 -49 0 445 440 439 442 403 423 404 67 68 365 0\n453 -49 0 406 408 448 445 440 439 442 403 423 404 452 234 95 98 365 0\n454 50 0 453 451 231 0\n455 -46 0 454 40 0\n456 -60 0 454 61 0\n457 -62 0 454 69 0\n458 75 0 454 396 407 191 0\n459 17 0 454 423 406 183 0\n460 56 0 454 444 450 360 0\n461 71 0 457 448 408 406 234 0\n462 66 0 458 211 0\n463 -41 0 460 55 0\n464 -29 0 461 95 0\n465 42 0 463 443 403 431 220 0\n466 53 0 464 432 455 404 222 0\n467 -43 0 465 26 0\n468 -54 0 466 52 0\n469 -63 0 429 468 441 467 71 88 214 0\n470 -58 0 458 108 0\n471 16 0 459 438 433 439 440 441 470 400 456 469 112 0\n472 -30 0 465 24 0\n473 51 0 469 430 446 217 0\n474 68 0 472 467 441 468 429 214 0\n475 8 0 473 467 145 0\n476 0 475 474 459 437 465 454 473 466 460 462 471 461 458 325 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record033.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record033.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record033.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record033.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record033 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeafTable : ConcreteGrowth.Table (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record033.l) :=
(.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf (⟨0, by decide⟩))
 (.leaf (⟨1, by decide⟩)))
 (.branch 3
 (.leaf (⟨2, by decide⟩))
 (.leaf (⟨3, by decide⟩))))
 (.branch 6
 (.branch 5
 (.leaf (⟨4, by decide⟩))
 (.leaf (⟨5, by decide⟩)))
 (.branch 7
 (.leaf (⟨6, by decide⟩))
 (.leaf (⟨7, by decide⟩)))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf (⟨8, by decide⟩))
 (.leaf (⟨9, by decide⟩)))
 (.branch 11
 (.leaf (⟨10, by decide⟩))
 (.leaf (⟨11, by decide⟩))))
 (.branch 14
 (.branch 13
 (.leaf (⟨12, by decide⟩))
 (.leaf (⟨13, by decide⟩)))
 (.branch 15
 (.leaf (⟨14, by decide⟩))
 (.leaf (⟨15, by decide⟩))))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf (⟨0, by decide⟩))
 (.leaf (⟨1, by decide⟩)))
 (.branch 19
 (.leaf (⟨2, by decide⟩))
 (.leaf (⟨3, by decide⟩))))
 (.branch 22
 (.branch 21
 (.leaf (⟨4, by decide⟩))
 (.leaf (⟨5, by decide⟩)))
 (.branch 23
 (.leaf (⟨6, by decide⟩))
 (.leaf (⟨7, by decide⟩)))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf (⟨8, by decide⟩))
 (.leaf (⟨9, by decide⟩)))
 (.branch 27
 (.leaf (⟨10, by decide⟩))
 (.leaf (⟨11, by decide⟩))))
 (.branch 30
 (.branch 29
 (.leaf (⟨12, by decide⟩))
 (.leaf (⟨13, by decide⟩)))
 (.branch 31
 (.leaf (⟨14, by decide⟩))
 (.leaf (⟨15, by decide⟩)))))))
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record033.l := originalLeafTable.get j.val
def orbitWordTable : ConcreteGrowth.Table (List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record033.g)) :=
(.branch 16
 (.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([]))
 (.leaf ([])))
 (.branch 3
 (.leaf ([]))
 (.leaf ([]))))
 (.branch 6
 (.branch 5
 (.leaf ([]))
 (.leaf ([])))
 (.branch 7
 (.leaf ([]))
 (.leaf ([])))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf ([]))
 (.leaf ([])))
 (.branch 11
 (.leaf ([]))
 (.leaf ([]))))
 (.branch 14
 (.branch 13
 (.leaf ([]))
 (.leaf ([])))
 (.branch 15
 (.leaf ([]))
 (.leaf ([]))))))
 (.branch 24
 (.branch 20
 (.branch 18
 (.branch 17
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 19
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩]))))
 (.branch 22
 (.branch 21
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 23
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))))
 (.branch 28
 (.branch 26
 (.branch 25
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 27
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩]))))
 (.branch 30
 (.branch 29
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))
 (.branch 31
 (.leaf ([⟨1, by decide⟩]))
 (.leaf ([⟨1, by decide⟩])))))))
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record033.g) := orbitWordTable.get j.val
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record033.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record033.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record033 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record033_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record033_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record033_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record033_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record033_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record033_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record033_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record033 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record033_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record033_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00029.record033_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00029.record033
