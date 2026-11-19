module
prelude
public import FacetCliqueRaw
public import FacetSatEdges
public import FacetSatGroups
public import FacetSatRaw
public import GraphDirectCore
public import GraphInputsRow16Part00025Data
public import GraphInputsRow16Part00025Frames
public import GraphInputsRow16Part00025Leaves
public import GraphInputsRow16Part00025Metadata
public meta import FacetSatFacts
public meta import FacetSatInitials
public meta import HexNatLiteral
public meta import KernelDecideContext
public meta import RupProofTerm
public meta import SparseNatLiteral

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00025.record019
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record019
def vertexColumn : Fields := ⟨10, hexnat% "29c5aaa6a5a364d8ce4b86e4789e17b315a699a9665a56354d68d3352d1b61d4749d176a358e938cd3362d4b32d2b1ac9b16e8731e2749ca785d1725c570dd0f0bd1a1988e1381e46685894658548d1341d48c6344d0b22c4b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db69a4936d249a4d24934da492492492492491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4400175303020773376, 17454747090944, hexnat% "80008000000000000", hexnat% "100020000000000000", hexnat% "460000000000000000", 37717646879227904]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "810089fef7e000000", hexnat% "100020000000000000", hexnat% "460000000000000000", 3170534208535789568, 114278840544526336]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [3287064915365330944, 1161928703861587968, 163827232538624, hexnat% "4e0000000004000000", hexnat% "100000008000000000", 11407433138176]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "43d14005ffe000000", 163827232538624, hexnat% "80008002000000000", 45598946227126272, hexnat% "520000000000000000", 11544872091648]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1010a6818fba000000", 3242591800426233856, hexnat% "4e0000000004000000", 15805479649280, 17593259786240, 6755399441055744]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [4332462870118793216, 163827232538624, hexnat% "80008006044000000", hexnat% "560000000002000000", 11544872091648, 114278840544526336, 107642617856]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c6 c3
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c7 c2
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c8 c1
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c9 c0
  c10
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record019_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record019_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record019_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record019_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record019_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record019_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record019_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record019_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record019_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00025.record019

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00025.record020
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record020
def vertexColumn : Fields := ⟨10, hexnat% "cc96aa6aa6a5a364d8ce4b86e4789e17b315a699a96958d5353352d1b51d2745dc8ea398d63c4e938cd33a2d8b52ccb4ac6b86c9b16e8731e2749ca785d1725c570dd0f0bd1a1988e1381e464652344d0768388d2318e1344d0b22c4b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6da6924db6db4d2492492492492492492492491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨72, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400bee5f6646000000", hexnat% "1380000000000000000", 4961065184002048, 41741713408, 549755813888]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [17700625345150976, hexnat% "400200010000000000", hexnat% "100081004000000000", 666532744850833408, hexnat% "1280000000000000000", 30923764531200]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400200030912000000", 702561541936906240, hexnat% "1380000000000000000", 66932770340864, 17029261860798464, 633322053042176, 281544233058304]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c3 c0
  c4
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record020_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record020_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record020_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record020_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record020_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record020_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record020_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record020_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record020_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00025.record020

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00025.record022
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record022
def vertexColumn : Fields := ⟨10, hexnat% "26ca716aa9936a3a2e4b86e4789e17b299a569a66a5996954d68d9362d4b46d8751d2745da8d6364d33a2d4b8ad2b1ac9b16e8731e2749ca745c570de0f43c8f0bd1a198961381e46685894652560d1341d48c6344c9342c4b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6da4936da49a49a49269269a492492492491249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4080275fffe000000", hexnat% "a0000000000000000", 1533475673119653888, 37436171902517248, hexnat% "100010000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a008d35ebfe000000", 70385924046848, hexnat% "40102000000000000", hexnat% "100050000000000000", 1441151949478035456, 576460752303423488]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a000575e2fe000000", hexnat% "40102000000000000", hexnat% "100010000800000000", 1209216499948978176, 288230449166155776, 576460769483292672]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "e058f047ffe000000", 53876069761024, 1747396655419752448, 70918499991552, hexnat% "100010000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "101dd955b43e000000", hexnat% "e0000000000000000", 50465865728, 35459249995776, 1688849860263936]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8084471efee000000", 4398314946560, hexnat% "120000000000000000", hexnat% "40102000000000000", 1441151949478035456, 43065671436730368]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [2115073616444915712, hexnat% "100000018000000000", 22265110462464, 35186519572480, 37436171902517248, hexnat% "e0000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "215df043f7e000000", 576460752303423488, hexnat% "100000018000000000", 87960930222080, hexnat% "c0000004080000000", 35184372088832]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c1dcf0076bc000000", 53876069761024, hexnat% "120000000042000000", 70373039144960, 4947802324992, 4503633987108864]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [90125210346323968, 1765411053929234432, hexnat% "e0000000000000000", 76416091684864, 288230483525894144, 4222124650659840, hexnat% "100010000040000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c11 c6
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c12 c5
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c13 c4
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c14 c3
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c15 c2
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c16 c1
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c17 c0
  c18
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record022_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record022_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record022_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record022_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record022_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record022_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record022_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record022_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record022_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00025.record022

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00025.record023
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record023
def vertexColumn : Fields := ⟨10, hexnat% "26a8e87a599361da8e3391e2785e9a6391e5654d475a34cd4749d17723a8e6358e331ce4b32e2b1ae1b46c9b16c3ba1d8751cc749c6725c570de0f43d32a29162384e07931a25152344d0768388d2318d130ce0b22c4b06d0721c4705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db69a4926db4d2492492492492492492492449249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "400800020220000000", hexnat% "100200212010000000", 135107988955332608, hexnat% "f0000000000000000", 127775277056, 8884053952430080, 84387517431808]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record023_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record023_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record023_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record023_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record023_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record023_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record023_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record023_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record023_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00025.record023

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00025.record001
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "8f13aa5956a394e338ae1ba1e4783ec66394e695556359354d3362d2b46d8751d0f69354d33a2d8b32d2b2ac6b86d1b0ee8751cc729c6785d1725c5783d0f07e8c528362384e0ba8952685854358348d1342d50d130cd0b22c4b0ac8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1b6d249369b69a4924934d249249a492492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record001 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record001 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record001.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record001.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record001.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 40), (facetIndex 44), (facetIndex 48), (facetIndex 49)]))
 (.leaf ([(facetIndex 53), (facetIndex 56), (facetIndex 60), (facetIndex 62)])))
 (.branch 3
 (.leaf ([(facetIndex 28), (facetIndex 69), (facetIndex 70), (facetIndex 71), (facetIndex 72)]))
 (.leaf ([(facetIndex 29), (facetIndex 33), (facetIndex 38), (facetIndex 47), (facetIndex 73)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 27), (facetIndex 34), (facetIndex 35), (facetIndex 39), (facetIndex 51), (facetIndex 66)]))
 (.leaf ([(facetIndex 42), (facetIndex 43), (facetIndex 45), (facetIndex 46)])))
 (.branch 7
 (.leaf ([(facetIndex 54), (facetIndex 55), (facetIndex 57), (facetIndex 58), (facetIndex 59)]))
 (.leaf ([(facetIndex 30), (facetIndex 31), (facetIndex 32), (facetIndex 36), (facetIndex 37)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "1a490100041db1d88800768b408ff91ffda8z14;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 8
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 41), (facetIndex 50)]))
 (.branch 2
 (.leaf ([(facetIndex 52), (facetIndex 61)]))
 (.leaf ([(facetIndex 67), (facetIndex 74)]))))
 (.branch 4
 (.leaf ([(facetIndex 68), (facetIndex 75)]))
 (.branch 5
 (.leaf ([(facetIndex 63), (facetIndex 64), (facetIndex 65)]))
 (.leaf ([(facetIndex 76), (facetIndex 77)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "2d680003424808000001z27;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 6
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped2_0000 : List Nat := [0, 1]
def grouped2_0001 : List Nat := [0, 1, 2, 3]
def grouped2_0003 : List Nat := [2]
def grouped2_0004 : List Nat := [2, 3]
def grouped2_0005 : List Nat := [3]
def grouped2_0006 : List Nat := [4, 5, 6, 7]
def grouped3_0007 : List Nat := [0]
def grouped3_0008 : List Nat := [0, 1, 2]
def grouped3_0010 : List Nat := [1]
def grouped3_0011 : List Nat := [1, 2]
def grouped3_0012 : List Nat := [2]
def grouped3_0013 : List Nat := [3]
def grouped3_0014 : List Nat := [3, 4, 5]
def grouped3_0015 : List Nat := [4]
def grouped3_0016 : List Nat := [4, 5]
def grouped3_0017 : List Nat := [5]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record001 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record001_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00025.record001" "{\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0004\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0011\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"grouped3_0008\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0016\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0014\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00025.record001" 47

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00025.record001" "{\"ridges\":[[10,273],[10,274],[17,529],[32,273],[33,529],[40,274],[48,274],[49,273],[49,274],[52,284],[53,529],[60,529],[61,340],[62,529],[63,312],[65,792],[68,538],[74,340],[75,658],[76,312],[77,568]],\"owners\":[[10,273,[52,61,63,65],[32,40,48,49]],[32,273,[63,65],[10,40,48,49,52,61]],[49,273,[52,63,65],[10,32,40,48,61]],[10,274,[67,74,76],[32,40,48,49]],[40,274,[74],[10,32,48,49,67,76]],[48,274,[67,74],[10,32,40,49,76]],[49,274,[67,76],[10,32,40,48,74]],[17,529,[41,50,64,65],[33,53,60,62]],[33,529,[64,65],[17,41,50,53,60,62]],[53,529,[50],[17,33,41,60,62,64,65]],[60,529,[41,50,65],[17,33,53,62,64]],[62,529,[41,64,65],[17,33,50,53,60]],[68,538,[41],[]],[75,658,[50],[]],[52,284,[67],[]],[61,340,[74],[]],[74,340,[61],[]],[63,312,[76],[]],[76,312,[63],[]],[77,568,[64],[]],[65,792,[],[]]],\"edges\":[[33,[10,32,40,48,49,52,61,63,65,67,74,76]],[34,[17,33,41,50,53,60,62,64,65,68,75,77]]],\"groupings\":[2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00025.record001" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00025.record001\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-14,-5],[-17,-16],[-19,-3],[-21,-19],[-22,-19],[-23,-19],[-24,-19],[-27,-17],[-1,11,14,16,18],[-4,16,18],[-9,11,16,18],[-1,19,25,27],[-6,25],[-8,19,25],[-9,19,27],[-2,7,10,17,18],[-5,17,18],[-12,10],[-13,7,10,18],[-15,7,17,18],[-20,7],[-26,10],[-11,19],[-14,25],[-25,14],[-16,27],[-27,16],[-28,17],[-18],[-29,3,21,22,23,24],[-30,29],[-31,30],[-32,31],[32],[-7,33],[-10,33],[-11,34],[-14,34],[-19,35],[-25,35],[-16,36],[-17,36],[-27,37],[-35,38],[-34,38],[-34,-35,39],[-38,40],[-39,41],[-33,40],[-33,-39,42],[-36,43],[-36,-37,44],[-43,45],[-44,46],[-40,-46,47],[-41,-45,47],[-42,47],[-47],[1,4,6,8,9,11,14,16,18,19,25,27],[2,5,7,10,12,13,15,17,18,20,26,28]],\"atoms\":[{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":76},{\"tag\":\"facet\",\"index\":77},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":61,\"b\":33},{\"tag\":\"incompatible\",\"a\":64,\"b\":63},{\"tag\":\"incompatible\",\"a\":67,\"b\":28},{\"tag\":\"incompatible\",\"a\":69,\"b\":67},{\"tag\":\"incompatible\",\"a\":70,\"b\":67},{\"tag\":\"incompatible\",\"a\":71,\"b\":67},{\"tag\":\"incompatible\",\"a\":72,\"b\":67},{\"tag\":\"incompatible\",\"a\":76,\"b\":64},{\"tag\":\"mate\",\"ridge\":273,\"a\":10,\"owners\":[52,61,63,65]},{\"tag\":\"mate\",\"ridge\":273,\"a\":32,\"owners\":[63,65]},{\"tag\":\"mate\",\"ridge\":273,\"a\":49,\"owners\":[52,63,65]},{\"tag\":\"mate\",\"ridge\":274,\"a\":10,\"owners\":[67,74,76]},{\"tag\":\"mate\",\"ridge\":274,\"a\":40,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":274,\"a\":48,\"owners\":[67,74]},{\"tag\":\"mate\",\"ridge\":274,\"a\":49,\"owners\":[67,76]},{\"tag\":\"mate\",\"ridge\":529,\"a\":17,\"owners\":[41,50,64,65]},{\"tag\":\"mate\",\"ridge\":529,\"a\":33,\"owners\":[64,65]},{\"tag\":\"mate\",\"ridge\":529,\"a\":53,\"owners\":[50]},{\"tag\":\"mate\",\"ridge\":529,\"a\":60,\"owners\":[41,50,65]},{\"tag\":\"mate\",\"ridge\":529,\"a\":62,\"owners\":[41,64,65]},{\"tag\":\"mate\",\"ridge\":538,\"a\":68,\"owners\":[41]},{\"tag\":\"mate\",\"ridge\":658,\"a\":75,\"owners\":[50]},{\"tag\":\"mate\",\"ridge\":284,\"a\":52,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":340,\"a\":61,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":340,\"a\":74,\"owners\":[61]},{\"tag\":\"mate\",\"ridge\":312,\"a\":63,\"owners\":[76]},{\"tag\":\"mate\",\"ridge\":312,\"a\":76,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":568,\"a\":77,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":792,\"a\":65,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[28,69,70,71,72],\"full_literals\":[-29,3,21,22,23,24]},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0003\",\"right_name\":\"grouped2_0005\",\"joined_name\":\"grouped2_0004\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-30,29,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-31,false,30],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-32,31,false],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":41,\"full_literals\":[-7,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":50,\"full_literals\":[-10,33]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":52,\"full_literals\":[-11,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":61,\"full_literals\":[-14,34]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":67,\"full_literals\":[-19,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":74,\"full_literals\":[-25,35]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":63,\"full_literals\":[-16,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":64,\"full_literals\":[-17,36]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":76,\"full_literals\":[-27,37]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-35,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-34,false,38],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0010\",\"right_name\":\"grouped3_0012\",\"joined_name\":\"grouped3_0011\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-34,-35,39],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-38,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-39,41],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-33,false,40],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0007\",\"right_name\":\"grouped3_0011\",\"joined_name\":\"grouped3_0008\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-33,-39,42],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-36,false,43],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0015\",\"right_name\":\"grouped3_0017\",\"joined_name\":\"grouped3_0016\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-36,-37,44],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-43,45],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0013\",\"right_name\":\"grouped3_0016\",\"joined_name\":\"grouped3_0014\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-44,46],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-40,-46,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-41,-45,47],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0014\",\"joined_name\":\"groupKind3\",\"a\":3,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-42,false,47],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":33,\"owners\":[10,32,40,48,49,52,61,63,65,67,74,76]},{\"tag\":\"edge\",\"edge\":34,\"owners\":[17,33,41,50,53,60,62,64,65,68,75,77]}]}"
  "p cnf 47 60\n-14 -5 0\n-17 -16 0\n-19 -3 0\n-21 -19 0\n-22 -19 0\n-23 -19 0\n-24 -19 0\n-27 -17 0\n-1 11 14 16 18 0\n-4 16 18 0\n-9 11 16 18 0\n-1 19 25 27 0\n-6 25 0\n-8 19 25 0\n-9 19 27 0\n-2 7 10 17 18 0\n-5 17 18 0\n-12 10 0\n-13 7 10 18 0\n-15 7 17 18 0\n-20 7 0\n-26 10 0\n-11 19 0\n-14 25 0\n-25 14 0\n-16 27 0\n-27 16 0\n-28 17 0\n-18 0\n-29 3 21 22 23 24 0\n-30 29 0\n-31 30 0\n-32 31 0\n32 0\n-7 33 0\n-10 33 0\n-11 34 0\n-14 34 0\n-19 35 0\n-25 35 0\n-16 36 0\n-17 36 0\n-27 37 0\n-35 38 0\n-34 38 0\n-34 -35 39 0\n-38 40 0\n-39 41 0\n-33 40 0\n-33 -39 42 0\n-36 43 0\n-36 -37 44 0\n-43 45 0\n-44 46 0\n-40 -46 47 0\n-41 -45 47 0\n-42 47 0\n-47 0\n1 4 6 8 9 11 14 16 18 19 25 27 0\n2 5 7 10 12 13 15 17 18 20 26 28 0\n"
  "61 31 0 34 33 0\n62 30 0 61 32 0\n63 29 0 62 31 0\n64 -42 0 58 57 0\n65 1 4 6 8 9 11 14 16 19 25 27 0 29 59 0\n66 2 5 7 10 12 13 15 17 20 26 28 0 29 60 0\n67 17 5 33 0 29 35 36 19 22 18 21 28 20 16 66 0\n68 -17 38 0 29 44 39 40 14 13 45 38 37 2 8 10 11 9 65 0\n69 40 0 29 47 49 35 36 21 18 22 19 68 17 28 20 16 66 0\n70 -46 0 69 58 55 0\n71 -44 0 70 54 0\n72 -16 0 71 26 41 43 52 0\n73 -4 0 72 29 10 0\n74 -27 0 72 27 0\n75 19 25 8 0 72 73 74 24 13 23 15 12 65 0\n76 -19 0 63 3 4 5 6 7 30 0\n77 -25 39 0 25 40 38 46 0\n78 25 0 76 14 75 0\n79 14 0 78 25 0\n80 39 0 78 77 0\n81 -5 0 79 1 0\n82 41 0 80 48 0\n83 -33 0 80 64 50 0\n84 -45 0 82 58 56 0\n85 17 0 83 81 67 0\n86 -43 0 84 53 0\n87 36 0 85 42 0\n88 0 87 86 51 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record001.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record001.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record001.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record001.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record001 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record001.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record001.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record001.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record001.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record001 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record001_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record001 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record001_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record001_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00025.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00025.record002
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "8ea9655936a394e338ae1ba1e0fa39a55554d68d534cd2b46d8743dc4e9354e334ce4b52ccb8acab1ae1b0ee8761cc749ca719e1725c5783d0f07e8a519160d88e1382ea2545454352344d0b68350e1344c3382c8b12c2b41c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6d24924d3692492692492492492492492491249249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record002 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record002 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record002.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record002.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record002.data.quota

def groupMembers1 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 14
 (.branch 7
 (.branch 3
 (.branch 1
 (.leaf ([(facetIndex 0)]))
 (.branch 2
 (.leaf ([(facetIndex 1)]))
 (.leaf ([(facetIndex 2)]))))
 (.branch 5
 (.branch 4
 (.leaf ([(facetIndex 3)]))
 (.leaf ([(facetIndex 4)])))
 (.branch 6
 (.leaf ([(facetIndex 5)]))
 (.leaf ([(facetIndex 6)])))))
 (.branch 10
 (.branch 8
 (.leaf ([(facetIndex 7)]))
 (.branch 9
 (.leaf ([(facetIndex 8)]))
 (.leaf ([(facetIndex 9)]))))
 (.branch 12
 (.branch 11
 (.leaf ([(facetIndex 10)]))
 (.leaf ([(facetIndex 11)])))
 (.branch 13
 (.leaf ([(facetIndex 12)]))
 (.leaf ([(facetIndex 13)]))))))
 (.branch 21
 (.branch 17
 (.branch 15
 (.leaf ([(facetIndex 14)]))
 (.branch 16
 (.leaf ([(facetIndex 15)]))
 (.leaf ([(facetIndex 16)]))))
 (.branch 19
 (.branch 18
 (.leaf ([(facetIndex 17)]))
 (.leaf ([(facetIndex 18)])))
 (.branch 20
 (.leaf ([(facetIndex 19)]))
 (.leaf ([(facetIndex 20)])))))
 (.branch 25
 (.branch 23
 (.branch 22
 (.leaf ([(facetIndex 21)]))
 (.leaf ([(facetIndex 22)])))
 (.branch 24
 (.leaf ([(facetIndex 23)]))
 (.leaf ([(facetIndex 24)]))))
 (.branch 27
 (.branch 26
 (.leaf ([(facetIndex 25)]))
 (.leaf ([(facetIndex 26)])))
 (.branch 28
 (.leaf ([(facetIndex 27)]))
 (.leaf ([(facetIndex 28)])))))))
def groupColors1 : PackedGraphCertificate.Fields :=
  ⟨5, sparse_nat% "1cdeb38bdab49ca307b9ac5a928398a418820"⟩
def grouping1 : FacetSat.Grouping data.count where
  count := 29
  members := fun g => groupMembers1.get g
  color := fun c => groupColors1.get c.val
def groupKind1 : List Nat := List.range grouping1.count

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 30), (facetIndex 32), (facetIndex 37), (facetIndex 39), (facetIndex 51), (facetIndex 62), (facetIndex 73)]))
 (.leaf ([(facetIndex 31), (facetIndex 40), (facetIndex 44), (facetIndex 46), (facetIndex 60), (facetIndex 71)])))
 (.branch 3
 (.leaf ([(facetIndex 29), (facetIndex 33), (facetIndex 34), (facetIndex 49), (facetIndex 61), (facetIndex 72)]))
 (.leaf ([(facetIndex 42), (facetIndex 50), (facetIndex 52), (facetIndex 53)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 35), (facetIndex 38), (facetIndex 47), (facetIndex 59), (facetIndex 70)]))
 (.leaf ([(facetIndex 54), (facetIndex 56), (facetIndex 57), (facetIndex 58)])))
 (.branch 7
 (.leaf ([(facetIndex 41), (facetIndex 43), (facetIndex 45), (facetIndex 48)]))
 (.branch 8
 (.leaf ([(facetIndex 65), (facetIndex 67), (facetIndex 68), (facetIndex 69)]))
 (.leaf ([(facetIndex 36)]))))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨4, sparse_nat% "21477707000214555053303264161636104084220102z1d;"⟩
def grouping2 : FacetSat.Grouping data.count where
  count := 9
  members := fun g => groupMembers2.get g
  color := fun c => groupColors2.get c.val
def groupKind2 : List Nat := List.range grouping2.count

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 2
 (.branch 1
 (.leaf ([(facetIndex 55), (facetIndex 63)]))
 (.leaf ([(facetIndex 64), (facetIndex 66)])))
 (.branch 3
 (.leaf ([(facetIndex 74)]))
 (.leaf ([(facetIndex 75)]))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨2, sparse_nat% "e00011z20;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 4
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped1_0000 : List Nat := [0, 1, 2, 3, 4, 5, 6]
def grouped1_0001 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]
def grouped1_0003 : List Nat := [7, 8, 9]
def grouped1_0004 : List Nat := [7, 8, 9, 10, 11, 12, 13]
def grouped1_0005 : List Nat := [10]
def grouped1_0006 : List Nat := [10, 11]
def grouped1_0007 : List Nat := [10, 11, 12, 13]
def grouped1_0008 : List Nat := [11]
def grouped1_0009 : List Nat := [12]
def grouped1_0010 : List Nat := [12, 13]
def grouped1_0011 : List Nat := [13]
def grouped1_0012 : List Nat := [14]
def grouped1_0013 : List Nat := [14, 15, 16]
def grouped1_0014 : List Nat := [14, 15, 16, 17, 18, 19, 20]
def grouped1_0015 : List Nat := [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]
def grouped1_0016 : List Nat := [15, 16]
def grouped1_0017 : List Nat := [17]
def grouped1_0018 : List Nat := [17, 18]
def grouped1_0019 : List Nat := [17, 18, 19, 20]
def grouped1_0020 : List Nat := [18]
def grouped1_0021 : List Nat := [19]
def grouped1_0022 : List Nat := [19, 20]
def grouped1_0023 : List Nat := [20]
def grouped1_0024 : List Nat := [21]
def grouped1_0025 : List Nat := [21, 22]
def grouped1_0026 : List Nat := [21, 22, 23, 24]
def grouped1_0027 : List Nat := [21, 22, 23, 24, 25, 26, 27, 28]
def grouped1_0028 : List Nat := [22]
def grouped1_0029 : List Nat := [23, 24]
def grouped1_0030 : List Nat := [25]
def grouped1_0031 : List Nat := [25, 26]
def grouped1_0032 : List Nat := [25, 26, 27, 28]
def grouped1_0033 : List Nat := [26]
def grouped1_0034 : List Nat := [27]
def grouped1_0035 : List Nat := [27, 28]
def grouped1_0036 : List Nat := [28]
def grouped2_0037 : List Nat := [0]
def grouped2_0038 : List Nat := [0, 1]
def grouped2_0039 : List Nat := [0, 1, 2, 3]
def grouped2_0041 : List Nat := [1]
def grouped2_0042 : List Nat := [2]
def grouped2_0043 : List Nat := [2, 3]
def grouped2_0044 : List Nat := [3]
def grouped2_0045 : List Nat := [4]
def grouped2_0046 : List Nat := [4, 5]
def grouped2_0047 : List Nat := [4, 5, 6, 7, 8]
def grouped2_0048 : List Nat := [5]
def grouped2_0049 : List Nat := [6]
def grouped2_0050 : List Nat := [6, 7, 8]
def grouped2_0051 : List Nat := [7]
def grouped2_0052 : List Nat := [7, 8]
def grouped2_0053 : List Nat := [8]
def grouped3_0054 : List Nat := [0]
def grouped3_0055 : List Nat := [0, 1]
def grouped3_0057 : List Nat := [1]
def grouped3_0058 : List Nat := [2]
def grouped3_0059 : List Nat := [2, 3]
def grouped3_0060 : List Nat := [3]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record002 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record002_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00025.record002" "{\"atoms\":[{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"group\",\"kind\":1,\"index\":11},{\"tag\":\"group\",\"kind\":1,\"index\":13},{\"tag\":\"group\",\"kind\":1,\"index\":14},{\"tag\":\"group\",\"kind\":1,\"index\":18},{\"tag\":\"group\",\"kind\":1,\"index\":19},{\"tag\":\"group\",\"kind\":1,\"index\":20},{\"tag\":\"group\",\"kind\":1,\"index\":21},{\"tag\":\"group\",\"kind\":1,\"index\":25},{\"tag\":\"group\",\"kind\":1,\"index\":26},{\"tag\":\"group\",\"kind\":1,\"index\":27},{\"tag\":\"group\",\"kind\":1,\"index\":28},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0006\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0010\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0007\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0007\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0004\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0004\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0001\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0001\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0013\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0018\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0022\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0022\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0019\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0019\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0019\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0014\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0014\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0014\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0025\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0026\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0031\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0031\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0035\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0035\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0032\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0032\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":4,\"list_name\":\"grouped1_0032\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":1,\"list_name\":\"grouped1_0027\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0027\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0027\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":4,\"list_name\":\"grouped1_0027\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":2,\"list_name\":\"grouped1_0015\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":3,\"list_name\":\"grouped1_0015\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":4,\"list_name\":\"grouped1_0015\"},{\"tag\":\"group_totalizer\",\"kind\":1,\"threshold\":4,\"list_name\":\"groupKind1\"},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":1},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":4},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group\",\"kind\":2,\"index\":8},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0038\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0043\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0039\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0046\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0046\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":1,\"list_name\":\"grouped2_0052\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0052\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0050\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":3,\"list_name\":\"grouped2_0050\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0047\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":5,\"list_name\":\"grouped2_0047\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":1},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0055\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0055\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0059\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0059\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"groupKind3\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00025.record002" 143

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00025.record002" "{\"ridges\":[[10,49],[10,50],[13,259],[14,642],[15,37],[18,21],[18,37],[19,21],[21,521],[22,42],[25,38],[25,52],[28,522],[29,21],[34,530],[36,35],[36,37],[36,38],[36,131],[36,133],[36,134],[40,642],[41,49],[43,35],[43,41],[43,42],[43,67],[48,521],[48,522],[49,35],[49,49],[49,50],[49,273],[50,49],[50,50],[51,274],[51,321],[51,322],[53,515],[54,21],[56,37],[57,41],[58,133],[60,521],[61,37],[62,21],[63,21],[63,133],[63,660],[64,41],[64,521],[64,568],[65,52],[67,38],[67,44],[68,42],[69,134],[71,522],[71,648],[72,52],[72,276],[73,22],[74,134],[74,660],[75,42],[75,50],[75,522],[75,568]],\"owners\":[[19,21,[1,18,29,32,33,34,54,55,63],[62]],[62,21,[1,18,29,33,34,54,55,63],[19,32]],[73,22,[1,25,29,33,34,65,66,74],[26,32]],[36,38,[22,25,67,72],[2,35,37,68]],[43,67,[3,13,32,38,51],[7,35,46,48]],[36,131,[8,14,46,52],[4,33,38,39,44]],[13,259,[5,11,30,37,39,49,53],[47]],[53,515,[9,14,31,40,45,48],[12,34,50]],[75,522,[9,28,31,48,71],[42,45,66]],[10,49,[18,54,61,64],[41,49,50]],[41,49,[18,61],[10,49,50,54,64]],[49,49,[18,54,64],[10,41,50,61]],[50,49,[18,54,61],[10,41,49,64]],[10,50,[25,65,72,75],[41,49,50]],[49,50,[25,65,75],[10,41,50,72]],[50,50,[25,65,72],[10,41,49,75]],[75,50,[10,25,49,72],[41,50,65]],[49,273,[19,62],[11,51,53,61]],[51,274,[26,72],[11,49,53,73]],[34,530,[75],[12,42,50,52,53,66,74]],[51,321,[20,59],[13,47,62]],[51,322,[27,70],[13,47,73]],[14,642,[28,71,74],[40,52]],[40,642,[28],[14,52,71,74]],[67,44,[15,54,57],[22,56,65,68]],[25,52,[18,54,61],[65,72]],[65,52,[18,61],[25,54,72]],[72,52,[18,54],[25,61,65]],[72,276,[19,62],[26,61,73]],[71,648,[21],[28,60]],[63,660,[74],[]],[74,660,[63],[]],[64,568,[75],[]],[75,568,[64],[]]],\"edges\":[[30,[10,18,25,41,49,50,54,61,64,65,72,75]],[43,[14,21,28,40,52,60,63,71,74]]],\"groupings\":[1,2,3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00025.record002" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00025.record002\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-27,-1],[-27,-2],[-27,-3],[-27,-20],[-27,-23],[-27,-24],[-27,-25],[-28,-27],[-29,-27],[-30,-27],[-31,-27],[-32,-27],[-34,-4],[-34,-5],[-34,-21],[-34,-22],[-34,-26],[-35,-34],[-37,-34],[-38,-34],[-39,-4],[-39,-37],[-42,-8],[-43,-39],[-44,-6],[-44,-23],[-44,-40],[-44,-42],[-44,-43],[-45,-20],[-45,-27],[-46,-45],[-47,-34],[-47,-46],[-48,-27],[-48,-46],[-49,-46],[-50,-49],[-51,-49],[-53,-42],[-53,-50],[-54,-52],[-56,-27],[-56,-46],[-58,-34],[-58,-57],[-59,-27],[-59,-57],[-60,-49],[-60,-57],[-61,-60],[-62,-60],[-64,-61],[-65,-24],[-65,-63],[-66,-20],[-66,-32],[-66,-33],[-66,-36],[-66,-41],[-66,-45],[-66,-46],[-66,-56],[-66,-57],[-12,1,11,20,23,24,25,45,46,54],[-53,1,11,20,24,25,45,46,54],[-11,-12,-54],[-11,-20,-54],[-11,-53,-54],[-12,-45,-54],[-45,-53,-54],[-64,1,16,20,24,25,56,57,65],[-27,-34,-40],[-10,-11,-27],[-10,-27,-52],[-11,-27,-47],[-27,-47,-52],[-27,15,16,58,63],[-16,-27,-58],[-34,2,8,23,29,42],[-27,4,9,37,43],[-27,-49,-54],[-27,-60,-65],[-8,3,7,21,28,30,40,44],[-34,-48,-55],[-15,-34,-66],[-34,-59,-66],[-44,5,9,22,31,36,39],[-14,-39,-55],[-39,-51,-55],[-66,5,19,22,39,62],[-19,-39,-66],[-39,-62,-66],[-6,11,45,52,55],[-32,11,52],[-40,11,45,55],[-41,11,45,52],[-6,16,56,63,66],[-40,16,56,66],[-41,16,56,63],[-66,6,16,40,63],[-40,12,53],[-42,17,63],[-25,66],[-42,13,50],[-42,18,61],[-9,19,62,65],[-31,19],[-58,10,45,48],[-16,11,45,52],[-56,11,52],[-63,11,45],[-63,12,53],[-62,14],[-54,65],[-65,54],[-55,66],[-66,55],[-7,67],[-68,8],[-8,68],[-9,69],[-11,70],[-12,71],[-13,72],[-14,73],[-16,74],[-17,75],[-18,76],[-19,77],[-67,78],[-68,79],[-79,80],[-78,-79,81],[-80,82],[-81,83],[-82,84],[-83,85],[-69,86],[-70,87],[-72,88],[-71,88],[-71,-72,89],[-88,90],[-87,90],[-87,-88,91],[-87,-89,92],[-90,93],[-91,94],[-92,95],[-86,93],[-86,-90,94],[-73,96],[-96,97],[-74,98],[-74,-75,99],[-77,100],[-76,-77,101],[-100,102],[-101,103],[-98,-100,103],[-99,103],[-99,-101,104],[-102,105],[-103,106],[-104,108],[-97,105],[-97,-103,107],[-106,109],[-108,111],[-93,-105,109],[-93,-106,110],[-93,-107,111],[-94,-105,110],[-94,-106,111],[-95,-105,111],[-111,112],[-84,-110,112],[-85,-109,112],[-112],[-113,21,23,28,30,42,53,64],[-114,22,31,35,37,51,62],[-115,20,24,25,40,52,63],[-116,33,41,43,44],[-117,26,29,38,50,61],[-118,45,47,48,49],[-119,32,34,36,39],[-120,56,58,59,60],[-121,27],[-122,113],[-122,114],[-123,115],[-123,116],[-124,122],[-124,123],[-125,117,118],[-126,117],[-126,118],[-127,120,121],[-128,120],[-128,121],[-129,119,128],[-130,119],[-129,127],[-130,128],[-131,125],[-131,126,130],[-132,126],[-131,129],[-132,130],[-133,124,132],[-133,131],[133],[-134,46,54],[-135,55,57],[-55,135],[-136,65],[-65,136],[-137,66],[-66,137],[-135,138],[-139,134],[-139,135],[-140,136,137],[-141,137],[-136,-137,141],[-142,139,140],[-138,-141,143],[142],[-143],[6,11,16,32,40,41,45,52,55,56,63,66],[9,14,19,31,43,51,54,62,65]],\"atoms\":[{\"tag\":\"facet\",\"index\":1},{\"tag\":\"facet\",\"index\":3},{\"tag\":\"facet\",\"index\":5},{\"tag\":\"facet\",\"index\":8},{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":10},{\"tag\":\"facet\",\"index\":11},{\"tag\":\"facet\",\"index\":13},{\"tag\":\"facet\",\"index\":14},{\"tag\":\"facet\",\"index\":15},{\"tag\":\"facet\",\"index\":18},{\"tag\":\"facet\",\"index\":19},{\"tag\":\"facet\",\"index\":20},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":25},{\"tag\":\"facet\",\"index\":26},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":28},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":31},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":33},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":35},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":37},{\"tag\":\"facet\",\"index\":38},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":48},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":50},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":56},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":66},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":69},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"group\",\"index\":11,\"kind\":1},{\"tag\":\"group\",\"index\":13,\"kind\":1},{\"tag\":\"group\",\"index\":14,\"kind\":1},{\"tag\":\"group\",\"index\":18,\"kind\":1},{\"tag\":\"group\",\"index\":19,\"kind\":1},{\"tag\":\"group\",\"index\":20,\"kind\":1},{\"tag\":\"group\",\"index\":21,\"kind\":1},{\"tag\":\"group\",\"index\":25,\"kind\":1},{\"tag\":\"group\",\"index\":26,\"kind\":1},{\"tag\":\"group\",\"index\":27,\"kind\":1},{\"tag\":\"group\",\"index\":28,\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group_totalizer\",\"kind\":1},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":1,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":4,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group\",\"index\":8,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":1,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"incompatible\",\"a\":36,\"b\":1},{\"tag\":\"incompatible\",\"a\":36,\"b\":3},{\"tag\":\"incompatible\",\"a\":36,\"b\":5},{\"tag\":\"incompatible\",\"a\":36,\"b\":29},{\"tag\":\"incompatible\",\"a\":36,\"b\":32},{\"tag\":\"incompatible\",\"a\":36,\"b\":33},{\"tag\":\"incompatible\",\"a\":36,\"b\":34},{\"tag\":\"incompatible\",\"a\":37,\"b\":36},{\"tag\":\"incompatible\",\"a\":38,\"b\":36},{\"tag\":\"incompatible\",\"a\":39,\"b\":36},{\"tag\":\"incompatible\",\"a\":40,\"b\":36},{\"tag\":\"incompatible\",\"a\":41,\"b\":36},{\"tag\":\"incompatible\",\"a\":43,\"b\":8},{\"tag\":\"incompatible\",\"a\":43,\"b\":9},{\"tag\":\"incompatible\",\"a\":43,\"b\":30},{\"tag\":\"incompatible\",\"a\":43,\"b\":31},{\"tag\":\"incompatible\",\"a\":43,\"b\":35},{\"tag\":\"incompatible\",\"a\":44,\"b\":43},{\"tag\":\"incompatible\",\"a\":46,\"b\":43},{\"tag\":\"incompatible\",\"a\":47,\"b\":43},{\"tag\":\"incompatible\",\"a\":48,\"b\":8},{\"tag\":\"incompatible\",\"a\":48,\"b\":46},{\"tag\":\"incompatible\",\"a\":51,\"b\":13},{\"tag\":\"incompatible\",\"a\":52,\"b\":48},{\"tag\":\"incompatible\",\"a\":53,\"b\":10},{\"tag\":\"incompatible\",\"a\":53,\"b\":32},{\"tag\":\"incompatible\",\"a\":53,\"b\":49},{\"tag\":\"incompatible\",\"a\":53,\"b\":51},{\"tag\":\"incompatible\",\"a\":53,\"b\":52},{\"tag\":\"incompatible\",\"a\":54,\"b\":29},{\"tag\":\"incompatible\",\"a\":54,\"b\":36},{\"tag\":\"incompatible\",\"a\":55,\"b\":54},{\"tag\":\"incompatible\",\"a\":56,\"b\":43},{\"tag\":\"incompatible\",\"a\":56,\"b\":55},{\"tag\":\"incompatible\",\"a\":57,\"b\":36},{\"tag\":\"incompatible\",\"a\":57,\"b\":55},{\"tag\":\"incompatible\",\"a\":58,\"b\":55},{\"tag\":\"incompatible\",\"a\":59,\"b\":58},{\"tag\":\"incompatible\",\"a\":60,\"b\":58},{\"tag\":\"incompatible\",\"a\":62,\"b\":51},{\"tag\":\"incompatible\",\"a\":62,\"b\":59},{\"tag\":\"incompatible\",\"a\":63,\"b\":61},{\"tag\":\"incompatible\",\"a\":65,\"b\":36},{\"tag\":\"incompatible\",\"a\":65,\"b\":55},{\"tag\":\"incompatible\",\"a\":67,\"b\":43},{\"tag\":\"incompatible\",\"a\":67,\"b\":66},{\"tag\":\"incompatible\",\"a\":68,\"b\":36},{\"tag\":\"incompatible\",\"a\":68,\"b\":66},{\"tag\":\"incompatible\",\"a\":69,\"b\":58},{\"tag\":\"incompatible\",\"a\":69,\"b\":66},{\"tag\":\"incompatible\",\"a\":70,\"b\":69},{\"tag\":\"incompatible\",\"a\":71,\"b\":69},{\"tag\":\"incompatible\",\"a\":73,\"b\":70},{\"tag\":\"incompatible\",\"a\":74,\"b\":33},{\"tag\":\"incompatible\",\"a\":74,\"b\":72},{\"tag\":\"incompatible\",\"a\":75,\"b\":29},{\"tag\":\"incompatible\",\"a\":75,\"b\":41},{\"tag\":\"incompatible\",\"a\":75,\"b\":42},{\"tag\":\"incompatible\",\"a\":75,\"b\":45},{\"tag\":\"incompatible\",\"a\":75,\"b\":50},{\"tag\":\"incompatible\",\"a\":75,\"b\":54},{\"tag\":\"incompatible\",\"a\":75,\"b\":55},{\"tag\":\"incompatible\",\"a\":75,\"b\":65},{\"tag\":\"incompatible\",\"a\":75,\"b\":66},{\"tag\":\"mate\",\"ridge\":21,\"a\":19,\"owners\":[1,18,29,32,33,34,54,55,63]},{\"tag\":\"mate\",\"ridge\":21,\"a\":62,\"owners\":[1,18,29,33,34,54,55,63]},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[18,19,63]},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[18,29,63]},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[18,62,63]},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[19,54,63]},{\"tag\":\"three\",\"ridge\":21,\"vertices\":[54,62,63]},{\"tag\":\"mate\",\"ridge\":22,\"a\":73,\"owners\":[1,25,29,33,34,65,66,74]},{\"tag\":\"three\",\"ridge\":35,\"vertices\":[36,43,49]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[15,18,36]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[15,36,61]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[18,36,56]},{\"tag\":\"three\",\"ridge\":37,\"vertices\":[36,56,61]},{\"tag\":\"mate\",\"ridge\":38,\"a\":36,\"owners\":[22,25,67,72]},{\"tag\":\"three\",\"ridge\":38,\"vertices\":[25,36,67]},{\"tag\":\"mate\",\"ridge\":67,\"a\":43,\"owners\":[3,13,32,38,51]},{\"tag\":\"mate\",\"ridge\":131,\"a\":36,\"owners\":[8,14,46,52]},{\"tag\":\"three\",\"ridge\":133,\"vertices\":[36,58,63]},{\"tag\":\"three\",\"ridge\":134,\"vertices\":[36,69,74]},{\"tag\":\"mate\",\"ridge\":259,\"a\":13,\"owners\":[5,11,30,37,39,49,53]},{\"tag\":\"three\",\"ridge\":41,\"vertices\":[43,57,64]},{\"tag\":\"three\",\"ridge\":42,\"vertices\":[22,43,75]},{\"tag\":\"three\",\"ridge\":42,\"vertices\":[43,68,75]},{\"tag\":\"mate\",\"ridge\":515,\"a\":53,\"owners\":[9,14,31,40,45,48]},{\"tag\":\"three\",\"ridge\":521,\"vertices\":[21,48,64]},{\"tag\":\"three\",\"ridge\":521,\"vertices\":[48,60,64]},{\"tag\":\"mate\",\"ridge\":522,\"a\":75,\"owners\":[9,28,31,48,71]},{\"tag\":\"three\",\"ridge\":522,\"vertices\":[28,48,75]},{\"tag\":\"three\",\"ridge\":522,\"vertices\":[48,71,75]},{\"tag\":\"mate\",\"ridge\":49,\"a\":10,\"owners\":[18,54,61,64]},{\"tag\":\"mate\",\"ridge\":49,\"a\":41,\"owners\":[18,61]},{\"tag\":\"mate\",\"ridge\":49,\"a\":49,\"owners\":[18,54,64]},{\"tag\":\"mate\",\"ridge\":49,\"a\":50,\"owners\":[18,54,61]},{\"tag\":\"mate\",\"ridge\":50,\"a\":10,\"owners\":[25,65,72,75]},{\"tag\":\"mate\",\"ridge\":50,\"a\":49,\"owners\":[25,65,75]},{\"tag\":\"mate\",\"ridge\":50,\"a\":50,\"owners\":[25,65,72]},{\"tag\":\"mate\",\"ridge\":50,\"a\":75,\"owners\":[10,25,49,72]},{\"tag\":\"mate\",\"ridge\":273,\"a\":49,\"owners\":[19,62]},{\"tag\":\"mate\",\"ridge\":274,\"a\":51,\"owners\":[26,72]},{\"tag\":\"mate\",\"ridge\":530,\"a\":34,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":321,\"a\":51,\"owners\":[20,59]},{\"tag\":\"mate\",\"ridge\":322,\"a\":51,\"owners\":[27,70]},{\"tag\":\"mate\",\"ridge\":642,\"a\":14,\"owners\":[28,71,74]},{\"tag\":\"mate\",\"ridge\":642,\"a\":40,\"owners\":[28]},{\"tag\":\"mate\",\"ridge\":44,\"a\":67,\"owners\":[15,54,57]},{\"tag\":\"mate\",\"ridge\":52,\"a\":25,\"owners\":[18,54,61]},{\"tag\":\"mate\",\"ridge\":52,\"a\":65,\"owners\":[18,61]},{\"tag\":\"mate\",\"ridge\":52,\"a\":72,\"owners\":[18,54]},{\"tag\":\"mate\",\"ridge\":276,\"a\":72,\"owners\":[19,62]},{\"tag\":\"mate\",\"ridge\":648,\"a\":71,\"owners\":[21]},{\"tag\":\"mate\",\"ridge\":660,\"a\":63,\"owners\":[74]},{\"tag\":\"mate\",\"ridge\":660,\"a\":74,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":568,\"a\":64,\"owners\":[75]},{\"tag\":\"mate\",\"ridge\":568,\"a\":75,\"owners\":[64]},{\"tag\":\"group_take\",\"kind\":1,\"index\":11,\"member\":11,\"full_literals\":[-7,67]},{\"tag\":\"group_or\",\"kind\":1,\"index\":13,\"members\":[13],\"full_literals\":[-68,8]},{\"tag\":\"group_take\",\"kind\":1,\"index\":13,\"member\":13,\"full_literals\":[-8,68]},{\"tag\":\"group_take\",\"kind\":1,\"index\":14,\"member\":14,\"full_literals\":[-9,69]},{\"tag\":\"group_take\",\"kind\":1,\"index\":18,\"member\":18,\"full_literals\":[-11,70]},{\"tag\":\"group_take\",\"kind\":1,\"index\":19,\"member\":19,\"full_literals\":[-12,71]},{\"tag\":\"group_take\",\"kind\":1,\"index\":20,\"member\":20,\"full_literals\":[-13,72]},{\"tag\":\"group_take\",\"kind\":1,\"index\":21,\"member\":21,\"full_literals\":[-14,73]},{\"tag\":\"group_take\",\"kind\":1,\"index\":25,\"member\":25,\"full_literals\":[-16,74]},{\"tag\":\"group_take\",\"kind\":1,\"index\":26,\"member\":26,\"full_literals\":[-17,75]},{\"tag\":\"group_take\",\"kind\":1,\"index\":27,\"member\":27,\"full_literals\":[-18,76]},{\"tag\":\"group_take\",\"kind\":1,\"index\":28,\"member\":28,\"full_literals\":[-19,77]},{\"tag\":\"merge\",\"left\":[10],\"right\":[11],\"left_name\":\"grouped1_0005\",\"right_name\":\"grouped1_0008\",\"joined_name\":\"grouped1_0006\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-67,78],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[12],\"right\":[13],\"left_name\":\"grouped1_0009\",\"right_name\":\"grouped1_0011\",\"joined_name\":\"grouped1_0010\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-68,79],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11],\"right\":[12,13],\"left_name\":\"grouped1_0006\",\"right_name\":\"grouped1_0010\",\"joined_name\":\"grouped1_0007\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-79,80],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[10,11],\"right\":[12,13],\"left_name\":\"grouped1_0006\",\"right_name\":\"grouped1_0010\",\"joined_name\":\"grouped1_0007\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-78,-79,81],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[7,8,9],\"right\":[10,11,12,13],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0007\",\"joined_name\":\"grouped1_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-80,82],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[7,8,9],\"right\":[10,11,12,13],\"left_name\":\"grouped1_0003\",\"right_name\":\"grouped1_0007\",\"joined_name\":\"grouped1_0004\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-81,83],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6],\"right\":[7,8,9,10,11,12,13],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0004\",\"joined_name\":\"grouped1_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-82,84],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6],\"right\":[7,8,9,10,11,12,13],\"left_name\":\"grouped1_0000\",\"right_name\":\"grouped1_0004\",\"joined_name\":\"grouped1_0001\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-83,85],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[14],\"right\":[15,16],\"left_name\":\"grouped1_0012\",\"right_name\":\"grouped1_0016\",\"joined_name\":\"grouped1_0013\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-69,false,86],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17],\"right\":[18],\"left_name\":\"grouped1_0017\",\"right_name\":\"grouped1_0020\",\"joined_name\":\"grouped1_0018\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-70,87],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[19],\"right\":[20],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0023\",\"joined_name\":\"grouped1_0022\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-72,88],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[19],\"right\":[20],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0023\",\"joined_name\":\"grouped1_0022\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-71,false,88],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[19],\"right\":[20],\"left_name\":\"grouped1_0021\",\"right_name\":\"grouped1_0023\",\"joined_name\":\"grouped1_0022\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-71,-72,89],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17,18],\"right\":[19,20],\"left_name\":\"grouped1_0018\",\"right_name\":\"grouped1_0022\",\"joined_name\":\"grouped1_0019\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-88,90],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17,18],\"right\":[19,20],\"left_name\":\"grouped1_0018\",\"right_name\":\"grouped1_0022\",\"joined_name\":\"grouped1_0019\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-87,false,90],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17,18],\"right\":[19,20],\"left_name\":\"grouped1_0018\",\"right_name\":\"grouped1_0022\",\"joined_name\":\"grouped1_0019\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-87,-88,91],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[17,18],\"right\":[19,20],\"left_name\":\"grouped1_0018\",\"right_name\":\"grouped1_0022\",\"joined_name\":\"grouped1_0019\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-87,-89,92],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[14,15,16],\"right\":[17,18,19,20],\"left_name\":\"grouped1_0013\",\"right_name\":\"grouped1_0019\",\"joined_name\":\"grouped1_0014\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-90,93],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[14,15,16],\"right\":[17,18,19,20],\"left_name\":\"grouped1_0013\",\"right_name\":\"grouped1_0019\",\"joined_name\":\"grouped1_0014\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-91,94],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[14,15,16],\"right\":[17,18,19,20],\"left_name\":\"grouped1_0013\",\"right_name\":\"grouped1_0019\",\"joined_name\":\"grouped1_0014\",\"a\":0,\"b\":3,\"direction\":\"forward\",\"full_literals\":[false,-92,95],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[14,15,16],\"right\":[17,18,19,20],\"left_name\":\"grouped1_0013\",\"right_name\":\"grouped1_0019\",\"joined_name\":\"grouped1_0014\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-86,false,93],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[14,15,16],\"right\":[17,18,19,20],\"left_name\":\"grouped1_0013\",\"right_name\":\"grouped1_0019\",\"joined_name\":\"grouped1_0014\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-86,-90,94],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[21],\"right\":[22],\"left_name\":\"grouped1_0024\",\"right_name\":\"grouped1_0028\",\"joined_name\":\"grouped1_0025\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-73,false,96],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[21,22],\"right\":[23,24],\"left_name\":\"grouped1_0025\",\"right_name\":\"grouped1_0029\",\"joined_name\":\"grouped1_0026\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-96,false,97],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[25],\"right\":[26],\"left_name\":\"grouped1_0030\",\"right_name\":\"grouped1_0033\",\"joined_name\":\"grouped1_0031\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-74,false,98],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[25],\"right\":[26],\"left_name\":\"grouped1_0030\",\"right_name\":\"grouped1_0033\",\"joined_name\":\"grouped1_0031\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-74,-75,99],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[27],\"right\":[28],\"left_name\":\"grouped1_0034\",\"right_name\":\"grouped1_0036\",\"joined_name\":\"grouped1_0035\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-77,100],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[27],\"right\":[28],\"left_name\":\"grouped1_0034\",\"right_name\":\"grouped1_0036\",\"joined_name\":\"grouped1_0035\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-76,-77,101],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[25,26],\"right\":[27,28],\"left_name\":\"grouped1_0031\",\"right_name\":\"grouped1_0035\",\"joined_name\":\"grouped1_0032\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-100,102],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[25,26],\"right\":[27,28],\"left_name\":\"grouped1_0031\",\"right_name\":\"grouped1_0035\",\"joined_name\":\"grouped1_0032\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-101,103],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[25,26],\"right\":[27,28],\"left_name\":\"grouped1_0031\",\"right_name\":\"grouped1_0035\",\"joined_name\":\"grouped1_0032\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-98,-100,103],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[25,26],\"right\":[27,28],\"left_name\":\"grouped1_0031\",\"right_name\":\"grouped1_0035\",\"joined_name\":\"grouped1_0032\",\"a\":2,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-99,false,103],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[25,26],\"right\":[27,28],\"left_name\":\"grouped1_0031\",\"right_name\":\"grouped1_0035\",\"joined_name\":\"grouped1_0032\",\"a\":2,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-99,-101,104],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[21,22,23,24],\"right\":[25,26,27,28],\"left_name\":\"grouped1_0026\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0027\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-102,105],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[21,22,23,24],\"right\":[25,26,27,28],\"left_name\":\"grouped1_0026\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0027\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-103,106],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[21,22,23,24],\"right\":[25,26,27,28],\"left_name\":\"grouped1_0026\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0027\",\"a\":0,\"b\":4,\"direction\":\"forward\",\"full_literals\":[false,-104,108],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[21,22,23,24],\"right\":[25,26,27,28],\"left_name\":\"grouped1_0026\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0027\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-97,false,105],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[21,22,23,24],\"right\":[25,26,27,28],\"left_name\":\"grouped1_0026\",\"right_name\":\"grouped1_0032\",\"joined_name\":\"grouped1_0027\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-97,-103,107],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[14,15,16,17,18,19,20],\"right\":[21,22,23,24,25,26,27,28],\"left_name\":\"grouped1_0014\",\"right_name\":\"grouped1_0027\",\"joined_name\":\"grouped1_0015\",\"a\":0,\"b\":2,\"direction\":\"forward\",\"full_literals\":[false,-106,109],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[14,15,16,17,18,19,20],\"right\":[21,22,23,24,25,26,27,28],\"left_name\":\"grouped1_0014\",\"right_name\":\"grouped1_0027\",\"joined_name\":\"grouped1_0015\",\"a\":0,\"b\":4,\"direction\":\"forward\",\"full_literals\":[false,-108,111],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[14,15,16,17,18,19,20],\"right\":[21,22,23,24,25,26,27,28],\"left_name\":\"grouped1_0014\",\"right_name\":\"grouped1_0027\",\"joined_name\":\"grouped1_0015\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-93,-105,109],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[14,15,16,17,18,19,20],\"right\":[21,22,23,24,25,26,27,28],\"left_name\":\"grouped1_0014\",\"right_name\":\"grouped1_0027\",\"joined_name\":\"grouped1_0015\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-93,-106,110],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[14,15,16,17,18,19,20],\"right\":[21,22,23,24,25,26,27,28],\"left_name\":\"grouped1_0014\",\"right_name\":\"grouped1_0027\",\"joined_name\":\"grouped1_0015\",\"a\":1,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-93,-107,111],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[14,15,16,17,18,19,20],\"right\":[21,22,23,24,25,26,27,28],\"left_name\":\"grouped1_0014\",\"right_name\":\"grouped1_0027\",\"joined_name\":\"grouped1_0015\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-94,-105,110],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[14,15,16,17,18,19,20],\"right\":[21,22,23,24,25,26,27,28],\"left_name\":\"grouped1_0014\",\"right_name\":\"grouped1_0027\",\"joined_name\":\"grouped1_0015\",\"a\":2,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-94,-106,111],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[14,15,16,17,18,19,20],\"right\":[21,22,23,24,25,26,27,28],\"left_name\":\"grouped1_0014\",\"right_name\":\"grouped1_0027\",\"joined_name\":\"grouped1_0015\",\"a\":3,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-95,-105,111],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9,10,11,12,13],\"right\":[14,15,16,17,18,19,20,21,22,23,24,25,26,27,28],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0015\",\"joined_name\":\"groupKind1\",\"a\":0,\"b\":4,\"direction\":\"forward\",\"full_literals\":[false,-111,112],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9,10,11,12,13],\"right\":[14,15,16,17,18,19,20,21,22,23,24,25,26,27,28],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0015\",\"joined_name\":\"groupKind1\",\"a\":1,\"b\":3,\"direction\":\"forward\",\"full_literals\":[-84,-110,112],\"grouped\":true,\"kind\":1},{\"tag\":\"merge\",\"left\":[0,1,2,3,4,5,6,7,8,9,10,11,12,13],\"right\":[14,15,16,17,18,19,20,21,22,23,24,25,26,27,28],\"left_name\":\"grouped1_0001\",\"right_name\":\"grouped1_0015\",\"joined_name\":\"groupKind1\",\"a\":2,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-85,-109,112],\"grouped\":true,\"kind\":1},{\"tag\":\"quota_upper\",\"kind\":1,\"quota\":3,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[30,32,37,39,51,62,73],\"full_literals\":[-113,21,23,28,30,42,53,64]},{\"tag\":\"group_or\",\"kind\":2,\"index\":1,\"members\":[31,40,44,46,60,71],\"full_literals\":[-114,22,31,35,37,51,62]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[29,33,34,49,61,72],\"full_literals\":[-115,20,24,25,40,52,63]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[42,50,52,53],\"full_literals\":[-116,33,41,43,44]},{\"tag\":\"group_or\",\"kind\":2,\"index\":4,\"members\":[35,38,47,59,70],\"full_literals\":[-117,26,29,38,50,61]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[54,56,57,58],\"full_literals\":[-118,45,47,48,49]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[41,43,45,48],\"full_literals\":[-119,32,34,36,39]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[65,67,68,69],\"full_literals\":[-120,56,58,59,60]},{\"tag\":\"group_or\",\"kind\":2,\"index\":8,\"members\":[36],\"full_literals\":[-121,27]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0037\",\"right_name\":\"grouped2_0041\",\"joined_name\":\"grouped2_0038\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-122,113,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0037\",\"right_name\":\"grouped2_0041\",\"joined_name\":\"grouped2_0038\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-122,false,114],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0042\",\"right_name\":\"grouped2_0044\",\"joined_name\":\"grouped2_0043\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-123,115,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0042\",\"right_name\":\"grouped2_0044\",\"joined_name\":\"grouped2_0043\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-123,false,116],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0038\",\"right_name\":\"grouped2_0043\",\"joined_name\":\"grouped2_0039\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-124,122,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0038\",\"right_name\":\"grouped2_0043\",\"joined_name\":\"grouped2_0039\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-124,false,123],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0045\",\"right_name\":\"grouped2_0048\",\"joined_name\":\"grouped2_0046\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-125,117,118],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0045\",\"right_name\":\"grouped2_0048\",\"joined_name\":\"grouped2_0046\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-126,117,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0045\",\"right_name\":\"grouped2_0048\",\"joined_name\":\"grouped2_0046\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-126,false,118],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0051\",\"right_name\":\"grouped2_0053\",\"joined_name\":\"grouped2_0052\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-127,120,121],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0051\",\"right_name\":\"grouped2_0053\",\"joined_name\":\"grouped2_0052\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-128,120,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[7],\"right\":[8],\"left_name\":\"grouped2_0051\",\"right_name\":\"grouped2_0053\",\"joined_name\":\"grouped2_0052\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-128,false,121],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0049\",\"right_name\":\"grouped2_0052\",\"joined_name\":\"grouped2_0050\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-129,119,128],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0049\",\"right_name\":\"grouped2_0052\",\"joined_name\":\"grouped2_0050\",\"a\":0,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-130,119,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0049\",\"right_name\":\"grouped2_0052\",\"joined_name\":\"grouped2_0050\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-129,false,127],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7,8],\"left_name\":\"grouped2_0049\",\"right_name\":\"grouped2_0052\",\"joined_name\":\"grouped2_0050\",\"a\":1,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-130,false,128],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0046\",\"right_name\":\"grouped2_0050\",\"joined_name\":\"grouped2_0047\",\"a\":0,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-131,125,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0046\",\"right_name\":\"grouped2_0050\",\"joined_name\":\"grouped2_0047\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-131,126,130],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0046\",\"right_name\":\"grouped2_0050\",\"joined_name\":\"grouped2_0047\",\"a\":1,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-132,126,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0046\",\"right_name\":\"grouped2_0050\",\"joined_name\":\"grouped2_0047\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-131,false,129],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7,8],\"left_name\":\"grouped2_0046\",\"right_name\":\"grouped2_0050\",\"joined_name\":\"grouped2_0047\",\"a\":2,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-132,false,130],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0039\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-133,124,132],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7,8],\"left_name\":\"grouped2_0039\",\"right_name\":\"grouped2_0047\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-133,false,131],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[55,63],\"full_literals\":[-134,46,54]},{\"tag\":\"group_or\",\"kind\":3,\"index\":1,\"members\":[64,66],\"full_literals\":[-135,55,57]},{\"tag\":\"group_take\",\"kind\":3,\"index\":1,\"member\":64,\"full_literals\":[-55,135]},{\"tag\":\"group_or\",\"kind\":3,\"index\":2,\"members\":[74],\"full_literals\":[-136,65]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":74,\"full_literals\":[-65,136]},{\"tag\":\"group_or\",\"kind\":3,\"index\":3,\"members\":[75],\"full_literals\":[-137,66]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":75,\"full_literals\":[-66,137]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0054\",\"right_name\":\"grouped3_0057\",\"joined_name\":\"grouped3_0055\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-135,138],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0054\",\"right_name\":\"grouped3_0057\",\"joined_name\":\"grouped3_0055\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-139,134,false],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped3_0054\",\"right_name\":\"grouped3_0057\",\"joined_name\":\"grouped3_0055\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-139,false,135],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0058\",\"right_name\":\"grouped3_0060\",\"joined_name\":\"grouped3_0059\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-140,136,137],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0058\",\"right_name\":\"grouped3_0060\",\"joined_name\":\"grouped3_0059\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-141,false,137],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped3_0058\",\"right_name\":\"grouped3_0060\",\"joined_name\":\"grouped3_0059\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-136,-137,141],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0055\",\"right_name\":\"grouped3_0059\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-142,139,140],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped3_0055\",\"right_name\":\"grouped3_0059\",\"joined_name\":\"groupKind3\",\"a\":1,\"b\":2,\"direction\":\"forward\",\"full_literals\":[-138,-141,143],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_lower\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":30,\"owners\":[10,18,25,41,49,50,54,61,64,65,72,75]},{\"tag\":\"edge\",\"edge\":43,\"owners\":[14,21,28,40,52,60,63,71,74]}]}"
  "p cnf 143 232\n-27 -1 0\n-27 -2 0\n-27 -3 0\n-27 -20 0\n-27 -23 0\n-27 -24 0\n-27 -25 0\n-28 -27 0\n-29 -27 0\n-30 -27 0\n-31 -27 0\n-32 -27 0\n-34 -4 0\n-34 -5 0\n-34 -21 0\n-34 -22 0\n-34 -26 0\n-35 -34 0\n-37 -34 0\n-38 -34 0\n-39 -4 0\n-39 -37 0\n-42 -8 0\n-43 -39 0\n-44 -6 0\n-44 -23 0\n-44 -40 0\n-44 -42 0\n-44 -43 0\n-45 -20 0\n-45 -27 0\n-46 -45 0\n-47 -34 0\n-47 -46 0\n-48 -27 0\n-48 -46 0\n-49 -46 0\n-50 -49 0\n-51 -49 0\n-53 -42 0\n-53 -50 0\n-54 -52 0\n-56 -27 0\n-56 -46 0\n-58 -34 0\n-58 -57 0\n-59 -27 0\n-59 -57 0\n-60 -49 0\n-60 -57 0\n-61 -60 0\n-62 -60 0\n-64 -61 0\n-65 -24 0\n-65 -63 0\n-66 -20 0\n-66 -32 0\n-66 -33 0\n-66 -36 0\n-66 -41 0\n-66 -45 0\n-66 -46 0\n-66 -56 0\n-66 -57 0\n-12 1 11 20 23 24 25 45 46 54 0\n-53 1 11 20 24 25 45 46 54 0\n-11 -12 -54 0\n-11 -20 -54 0\n-11 -53 -54 0\n-12 -45 -54 0\n-45 -53 -54 0\n-64 1 16 20 24 25 56 57 65 0\n-27 -34 -40 0\n-10 -11 -27 0\n-10 -27 -52 0\n-11 -27 -47 0\n-27 -47 -52 0\n-27 15 16 58 63 0\n-16 -27 -58 0\n-34 2 8 23 29 42 0\n-27 4 9 37 43 0\n-27 -49 -54 0\n-27 -60 -65 0\n-8 3 7 21 28 30 40 44 0\n-34 -48 -55 0\n-15 -34 -66 0\n-34 -59 -66 0\n-44 5 9 22 31 36 39 0\n-14 -39 -55 0\n-39 -51 -55 0\n-66 5 19 22 39 62 0\n-19 -39 -66 0\n-39 -62 -66 0\n-6 11 45 52 55 0\n-32 11 52 0\n-40 11 45 55 0\n-41 11 45 52 0\n-6 16 56 63 66 0\n-40 16 56 66 0\n-41 16 56 63 0\n-66 6 16 40 63 0\n-40 12 53 0\n-42 17 63 0\n-25 66 0\n-42 13 50 0\n-42 18 61 0\n-9 19 62 65 0\n-31 19 0\n-58 10 45 48 0\n-16 11 45 52 0\n-56 11 52 0\n-63 11 45 0\n-63 12 53 0\n-62 14 0\n-54 65 0\n-65 54 0\n-55 66 0\n-66 55 0\n-7 67 0\n-68 8 0\n-8 68 0\n-9 69 0\n-11 70 0\n-12 71 0\n-13 72 0\n-14 73 0\n-16 74 0\n-17 75 0\n-18 76 0\n-19 77 0\n-67 78 0\n-68 79 0\n-79 80 0\n-78 -79 81 0\n-80 82 0\n-81 83 0\n-82 84 0\n-83 85 0\n-69 86 0\n-70 87 0\n-72 88 0\n-71 88 0\n-71 -72 89 0\n-88 90 0\n-87 90 0\n-87 -88 91 0\n-87 -89 92 0\n-90 93 0\n-91 94 0\n-92 95 0\n-86 93 0\n-86 -90 94 0\n-73 96 0\n-96 97 0\n-74 98 0\n-74 -75 99 0\n-77 100 0\n-76 -77 101 0\n-100 102 0\n-101 103 0\n-98 -100 103 0\n-99 103 0\n-99 -101 104 0\n-102 105 0\n-103 106 0\n-104 108 0\n-97 105 0\n-97 -103 107 0\n-106 109 0\n-108 111 0\n-93 -105 109 0\n-93 -106 110 0\n-93 -107 111 0\n-94 -105 110 0\n-94 -106 111 0\n-95 -105 111 0\n-111 112 0\n-84 -110 112 0\n-85 -109 112 0\n-112 0\n-113 21 23 28 30 42 53 64 0\n-114 22 31 35 37 51 62 0\n-115 20 24 25 40 52 63 0\n-116 33 41 43 44 0\n-117 26 29 38 50 61 0\n-118 45 47 48 49 0\n-119 32 34 36 39 0\n-120 56 58 59 60 0\n-121 27 0\n-122 113 0\n-122 114 0\n-123 115 0\n-123 116 0\n-124 122 0\n-124 123 0\n-125 117 118 0\n-126 117 0\n-126 118 0\n-127 120 121 0\n-128 120 0\n-128 121 0\n-129 119 128 0\n-130 119 0\n-129 127 0\n-130 128 0\n-131 125 0\n-131 126 130 0\n-132 126 0\n-131 129 0\n-132 130 0\n-133 124 132 0\n-133 131 0\n133 0\n-134 46 54 0\n-135 55 57 0\n-55 135 0\n-136 65 0\n-65 136 0\n-137 66 0\n-66 137 0\n-135 138 0\n-139 134 0\n-139 135 0\n-140 136 137 0\n-141 137 0\n-136 -137 141 0\n-142 139 140 0\n-138 -141 143 0\n142 0\n-143 0\n6 11 16 32 40 41 45 52 55 56 63 66 0\n9 14 19 31 43 51 54 62 65 0\n"
  "233 -111 0 180 177 0\n234 -108 0 233 170 0\n235 -104 0 234 166 0\n236 131 0 213 212 0\n237 125 0 236 206 0\n238 129 0 236 209 0\n239 127 0 238 204 0\n240 -141 0 230 225 228 219 221 118 216 0\n241 -34 -132 -66 0 210 205 201 189 47 35 200 208 198 63 61 33 45 186 188 49 0\n242 -132 -137 0 240 226 218 219 59 57 210 203 205 201 189 241 187 21 22 24 92 93 81 107 0\n243 -39 -137 0 240 226 218 115 219 118 24 92 93 89 90 107 108 232 0\n244 121 -34 -66 0 239 236 87 118 85 45 33 63 61 201 199 205 188 207 49 198 186 0\n245 43 62 -34 -137 0 236 213 237 180 20 219 118 85 61 33 19 18 242 211 194 191 16 244 189 11 182 39 186 196 17 9 87 63 45 198 207 205 200 188 51 185 41 14 243 91 130 157 159 164 2 13 195 193 60 58 184 25 26 27 28 81 80 122 121 139 132 151 133 135 137 178 174 172 152 165 144 161 142 155 124 127 113 101 0\n246 -68 62 -34 -137 0 240 236 213 237 180 245 29 20 219 118 85 61 33 19 18 242 211 194 191 16 244 189 11 182 39 186 196 17 9 87 63 45 198 207 205 200 188 51 185 41 14 243 91 130 157 73 7 6 5 1 10 8 3 15 190 226 218 64 56 120 132 23 84 181 119 72 131 127 134 155 136 161 138 165 179 169 0\n247 63 99 -42 -27 15 58 0 78 103 127 128 156 0\n248 62 -34 -137 0 213 237 236 235 233 219 244 189 5 11 9 2 87 86 118 85 45 33 20 19 18 17 16 14 243 242 211 194 191 63 61 91 130 182 39 186 198 196 207 205 200 188 51 185 41 246 121 80 106 129 158 160 163 165 175 149 247 112 113 123 124 140 142 146 0\n249 -42 50 -97 -27 15 58 45 0 233 167 176 150 40 105 125 141 144 148 173 168 162 247 112 113 123 124 140 143 147 0\n250 -34 -137 0 240 213 236 180 243 242 211 194 190 226 218 115 219 118 63 62 61 59 56 14 15 16 17 20 33 45 85 86 87 244 189 2 3 8 9 10 11 1 5 6 7 73 248 52 114 188 126 200 153 205 154 207 167 197 198 186 38 185 53 249 80 181 121 66 132 123 133 140 135 145 137 148 178 171 174 179 152 138 139 136 122 134 88 131 84 119 0\n251 -11 -137 0 236 238 219 59 57 243 250 187 202 201 189 47 35 203 207 198 200 63 61 74 76 109 186 188 49 0\n252 -137 0 240 213 238 236 219 226 56 57 59 61 62 63 218 115 242 211 195 192 243 250 187 202 203 200 201 207 189 198 1 5 6 7 35 47 251 65 66 112 102 183 75 77 186 49 109 188 0\n253 -66 0 252 220 0\n254 -25 0 253 104 0\n255 -55 0 253 117 0\n256 130 -27 -65 0 236 213 254 255 116 82 35 31 4 42 55 54 210 207 211 198 195 186 192 76 183 96 0\n257 -27 -65 0 253 255 116 42 55 12 31 35 43 47 83 256 205 200 188 109 79 74 98 99 100 231 0\n258 11 45 -65 0 253 255 116 42 55 95 111 94 110 96 97 231 0\n259 -11 53 -65 0 213 254 257 189 201 205 210 211 195 192 116 42 55 54 67 68 102 183 0\n260 53 -65 0 213 254 257 189 201 205 210 211 195 192 116 42 55 54 259 258 30 70 183 102 0\n261 -65 0 116 260 69 71 258 0\n262 -54 0 261 115 0\n263 -136 0 261 217 0\n264 -140 0 263 252 224 0\n265 139 0 264 229 227 0\n266 134 0 265 222 0\n267 135 0 265 223 0\n268 46 0 266 262 214 0\n269 57 0 267 255 215 0\n270 -45 0 268 32 0\n271 -47 0 268 34 0\n272 -48 0 268 36 0\n273 -49 0 268 37 0\n274 -56 0 268 44 0\n275 -58 0 269 46 0\n276 -59 0 269 48 0\n277 -60 0 269 50 0\n278 -118 0 273 271 270 272 186 0\n279 -120 0 277 275 274 276 188 0\n280 -126 0 278 198 0\n281 -128 0 279 200 0\n282 130 0 280 236 207 0\n283 0 282 281 205 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record002.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record002.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record002.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record002.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record002 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record002.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record002.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record002.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record002.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record002 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record002_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record002_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record002_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record002_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record002_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record002_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record002_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record002 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record002_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record002_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record002_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00025.record002

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00025.record004
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "29a56b168d936a394e338ae1ba1e4783ea6559c56354d68d534cd2b46d8751d0f713a4d538cd33a2d4b32cab1ae1b46c9b16f0761e4731e2749ca719e1745c3783d0f07c3aa19462384e0b839a15452344d0b68350e1344c3322c4b0ac1b81d0721c4709c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "36db4924da6db69249b492492492492492492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record004 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record004 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record004.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record004.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record004.data.quota

def groupMembers2 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf ([(facetIndex 27), (facetIndex 30), (facetIndex 45), (facetIndex 46), (facetIndex 55), (facetIndex 68)]))
 (.leaf ([(facetIndex 28), (facetIndex 33), (facetIndex 37), (facetIndex 38), (facetIndex 48), (facetIndex 61), (facetIndex 74)])))
 (.branch 3
 (.leaf ([(facetIndex 29), (facetIndex 58), (facetIndex 59), (facetIndex 60), (facetIndex 62)]))
 (.leaf ([(facetIndex 71), (facetIndex 72), (facetIndex 73), (facetIndex 75)]))))
 (.branch 6
 (.branch 5
 (.leaf ([(facetIndex 31), (facetIndex 35), (facetIndex 50), (facetIndex 52)]))
 (.leaf ([(facetIndex 42), (facetIndex 43), (facetIndex 44), (facetIndex 51), (facetIndex 53), (facetIndex 54)])))
 (.branch 7
 (.leaf ([(facetIndex 41), (facetIndex 47), (facetIndex 49)]))
 (.leaf ([(facetIndex 32), (facetIndex 34), (facetIndex 36), (facetIndex 39), (facetIndex 40)])))))
def groupColors2 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "65b60000008a48016cb31c05b77e4f9cf811z15;"⟩
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
def grouped2_0008 : List Nat := [4]
def grouped2_0009 : List Nat := [4, 5]
def grouped2_0010 : List Nat := [4, 5, 6, 7]
def grouped2_0011 : List Nat := [5]
def grouped2_0012 : List Nat := [6]
def grouped2_0013 : List Nat := [6, 7]
def grouped2_0014 : List Nat := [7]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record004 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record004_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00025.record004" "{\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"group\",\"kind\":2,\"index\":0},{\"tag\":\"group\",\"kind\":2,\"index\":2},{\"tag\":\"group\",\"kind\":2,\"index\":3},{\"tag\":\"group\",\"kind\":2,\"index\":5},{\"tag\":\"group\",\"kind\":2,\"index\":6},{\"tag\":\"group\",\"kind\":2,\"index\":7},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0001\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0006\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0002\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0009\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":2,\"list_name\":\"grouped2_0013\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":4,\"list_name\":\"grouped2_0010\"},{\"tag\":\"group_totalizer\",\"kind\":2,\"threshold\":8,\"list_name\":\"groupKind2\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00025.record004" 53

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00025.record004" "{\"ridges\":[[17,137],[23,138],[32,529],[41,74],[47,137],[49,138],[51,529],[53,529],[54,529],[58,44],[58,76],[59,44],[59,137],[60,76],[60,137],[62,137],[67,137],[73,138],[75,138],[80,664]],\"owners\":[[41,74,[22,71,73,74],[8,45,47,48,79]],[17,137,[9,42,46,47,49,67],[59,60,62]],[59,137,[9,42,47,49,67],[17,46,60,62]],[60,137,[9,42,46,49,67],[17,47,59,62]],[62,137,[9,42,46,47],[17,49,59,60,67]],[23,138,[9,42,46,47,49,80],[72,73,75]],[49,138,[23,72,73],[9,42,46,47,75,80]],[73,138,[9,42,46,49,80],[23,47,72,75]],[75,138,[9,42,46,47],[23,49,72,73,80]],[32,529,[67],[12,44,51,53,54,57,64,65]],[51,529,[57,65,67],[12,32,44,53,54,64]],[53,529,[57,64,65],[12,32,44,51,54,67]],[54,529,[57,64,67],[12,32,44,51,53,65]],[58,44,[21,68,72],[15,55,59,71]],[59,44,[21,68,71],[15,55,58,72]],[58,76,[22,73,74],[16,60,61,71]],[60,76,[22,71,74],[16,58,61,73]],[80,664,[67],[]]],\"edges\":[[27,[9,17,23,42,46,47,49,59,60,62,67,72,73,75,80]]],\"groupings\":[2]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00025.record004" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00025.record004\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-10,-8],[-11,-8],[-12,-8],[-13,-8],[-14,-1],[-15,-14],[-16,-14],[-19,-14],[-20,-6],[-20,-7],[-20,-15],[-20,-16],[-20,-17],[-20,-18],[-20,-19],[-21,-1],[-21,-14],[-22,-14],[-24,-14],[-26,-25],[-29,-20],[-30,-21],[-31,-25],[-32,-25],[-33,-15],[-33,-17],[-33,-21],[-33,-23],[-33,-30],[-34,-26],[-34,-31],[-34,-32],[-35,-5],[-35,-27],[-36,-4],[-36,-5],[-36,-7],[-36,-28],[-36,-35],[-37,-3],[-37,-5],[-37,-7],[-37,-20],[-37,-29],[-37,-34],[-37,-35],[-37,-36],[-38,-36],[-39,-21],[-39,-33],[-14,4,35,37,38],[-2,1,15,19,20,21,33],[-28,1,15,20,21,33],[-29,1,15,19,21,33],[-30,1,15,19,20],[-20,-28,-33],[-5,1,15,19,20,21,40],[-21,5,36,37],[-37,1,15,19,21,40],[-39,1,15,19,20],[-9,33],[-22,26,32,33],[-23,26,31,32],[-24,26,31,33],[-27,3,34,36],[-28,3,34,35],[-27,4,37,38],[-29,4,35,38],[-40,33],[-41,6,8,18,19,25,34],[-42,7,27,28,29,30],[-43,35,36,37,39],[-44,15,16,17,22,23,24],[-45,14,20,21],[-46,9,10,11,12,13],[-47,41],[-48,42],[-48,43],[-49,47],[-49,48],[-50,44],[-51,45],[-51,46],[-52,50],[-52,51],[-53,49],[-53,52],[53],[1,2,5,15,19,20,21,28,29,30,33,36,37,39,40]],\"atoms\":[{\"tag\":\"facet\",\"index\":9},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":21},{\"tag\":\"facet\",\"index\":22},{\"tag\":\"facet\",\"index\":23},{\"tag\":\"facet\",\"index\":27},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":30},{\"tag\":\"facet\",\"index\":32},{\"tag\":\"facet\",\"index\":34},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":39},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":43},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":46},{\"tag\":\"facet\",\"index\":47},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":54},{\"tag\":\"facet\",\"index\":55},{\"tag\":\"facet\",\"index\":57},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":62},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":67},{\"tag\":\"facet\",\"index\":68},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"facet\",\"index\":72},{\"tag\":\"facet\",\"index\":73},{\"tag\":\"facet\",\"index\":74},{\"tag\":\"facet\",\"index\":75},{\"tag\":\"facet\",\"index\":80},{\"tag\":\"group\",\"index\":0,\"kind\":2},{\"tag\":\"group\",\"index\":2,\"kind\":2},{\"tag\":\"group\",\"index\":3,\"kind\":2},{\"tag\":\"group\",\"index\":5,\"kind\":2},{\"tag\":\"group\",\"index\":6,\"kind\":2},{\"tag\":\"group\",\"index\":7,\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2},{\"tag\":\"group_totalizer\",\"kind\":2}],\"rules\":[{\"tag\":\"incompatible\",\"a\":34,\"b\":30},{\"tag\":\"incompatible\",\"a\":36,\"b\":30},{\"tag\":\"incompatible\",\"a\":39,\"b\":30},{\"tag\":\"incompatible\",\"a\":40,\"b\":30},{\"tag\":\"incompatible\",\"a\":41,\"b\":9},{\"tag\":\"incompatible\",\"a\":42,\"b\":41},{\"tag\":\"incompatible\",\"a\":43,\"b\":41},{\"tag\":\"incompatible\",\"a\":46,\"b\":41},{\"tag\":\"incompatible\",\"a\":47,\"b\":27},{\"tag\":\"incompatible\",\"a\":47,\"b\":29},{\"tag\":\"incompatible\",\"a\":47,\"b\":42},{\"tag\":\"incompatible\",\"a\":47,\"b\":43},{\"tag\":\"incompatible\",\"a\":47,\"b\":44},{\"tag\":\"incompatible\",\"a\":47,\"b\":45},{\"tag\":\"incompatible\",\"a\":47,\"b\":46},{\"tag\":\"incompatible\",\"a\":49,\"b\":9},{\"tag\":\"incompatible\",\"a\":49,\"b\":41},{\"tag\":\"incompatible\",\"a\":51,\"b\":41},{\"tag\":\"incompatible\",\"a\":54,\"b\":41},{\"tag\":\"incompatible\",\"a\":57,\"b\":55},{\"tag\":\"incompatible\",\"a\":60,\"b\":47},{\"tag\":\"incompatible\",\"a\":62,\"b\":49},{\"tag\":\"incompatible\",\"a\":64,\"b\":55},{\"tag\":\"incompatible\",\"a\":65,\"b\":55},{\"tag\":\"incompatible\",\"a\":67,\"b\":42},{\"tag\":\"incompatible\",\"a\":67,\"b\":44},{\"tag\":\"incompatible\",\"a\":67,\"b\":49},{\"tag\":\"incompatible\",\"a\":67,\"b\":53},{\"tag\":\"incompatible\",\"a\":67,\"b\":62},{\"tag\":\"incompatible\",\"a\":68,\"b\":57},{\"tag\":\"incompatible\",\"a\":68,\"b\":64},{\"tag\":\"incompatible\",\"a\":68,\"b\":65},{\"tag\":\"incompatible\",\"a\":71,\"b\":23},{\"tag\":\"incompatible\",\"a\":71,\"b\":58},{\"tag\":\"incompatible\",\"a\":72,\"b\":22},{\"tag\":\"incompatible\",\"a\":72,\"b\":23},{\"tag\":\"incompatible\",\"a\":72,\"b\":29},{\"tag\":\"incompatible\",\"a\":72,\"b\":59},{\"tag\":\"incompatible\",\"a\":72,\"b\":71},{\"tag\":\"incompatible\",\"a\":73,\"b\":21},{\"tag\":\"incompatible\",\"a\":73,\"b\":23},{\"tag\":\"incompatible\",\"a\":73,\"b\":29},{\"tag\":\"incompatible\",\"a\":73,\"b\":47},{\"tag\":\"incompatible\",\"a\":73,\"b\":60},{\"tag\":\"incompatible\",\"a\":73,\"b\":68},{\"tag\":\"incompatible\",\"a\":73,\"b\":71},{\"tag\":\"incompatible\",\"a\":73,\"b\":72},{\"tag\":\"incompatible\",\"a\":74,\"b\":72},{\"tag\":\"incompatible\",\"a\":75,\"b\":49},{\"tag\":\"incompatible\",\"a\":75,\"b\":67},{\"tag\":\"mate\",\"ridge\":74,\"a\":41,\"owners\":[22,71,73,74]},{\"tag\":\"mate\",\"ridge\":137,\"a\":17,\"owners\":[9,42,46,47,49,67]},{\"tag\":\"mate\",\"ridge\":137,\"a\":59,\"owners\":[9,42,47,49,67]},{\"tag\":\"mate\",\"ridge\":137,\"a\":60,\"owners\":[9,42,46,49,67]},{\"tag\":\"mate\",\"ridge\":137,\"a\":62,\"owners\":[9,42,46,47]},{\"tag\":\"three\",\"ridge\":137,\"vertices\":[47,59,67]},{\"tag\":\"mate\",\"ridge\":138,\"a\":23,\"owners\":[9,42,46,47,49,80]},{\"tag\":\"mate\",\"ridge\":138,\"a\":49,\"owners\":[23,72,73]},{\"tag\":\"mate\",\"ridge\":138,\"a\":73,\"owners\":[9,42,46,49,80]},{\"tag\":\"mate\",\"ridge\":138,\"a\":75,\"owners\":[9,42,46,47]},{\"tag\":\"mate\",\"ridge\":529,\"a\":32,\"owners\":[67]},{\"tag\":\"mate\",\"ridge\":529,\"a\":51,\"owners\":[57,65,67]},{\"tag\":\"mate\",\"ridge\":529,\"a\":53,\"owners\":[57,64,65]},{\"tag\":\"mate\",\"ridge\":529,\"a\":54,\"owners\":[57,64,67]},{\"tag\":\"mate\",\"ridge\":44,\"a\":58,\"owners\":[21,68,72]},{\"tag\":\"mate\",\"ridge\":44,\"a\":59,\"owners\":[21,68,71]},{\"tag\":\"mate\",\"ridge\":76,\"a\":58,\"owners\":[22,73,74]},{\"tag\":\"mate\",\"ridge\":76,\"a\":60,\"owners\":[22,71,74]},{\"tag\":\"mate\",\"ridge\":664,\"a\":80,\"owners\":[67]},{\"tag\":\"group_or\",\"kind\":2,\"index\":0,\"members\":[27,30,45,46,55,68],\"full_literals\":[-41,6,8,18,19,25,34]},{\"tag\":\"group_or\",\"kind\":2,\"index\":2,\"members\":[29,58,59,60,62],\"full_literals\":[-42,7,27,28,29,30]},{\"tag\":\"group_or\",\"kind\":2,\"index\":3,\"members\":[71,72,73,75],\"full_literals\":[-43,35,36,37,39]},{\"tag\":\"group_or\",\"kind\":2,\"index\":5,\"members\":[42,43,44,51,53,54],\"full_literals\":[-44,15,16,17,22,23,24]},{\"tag\":\"group_or\",\"kind\":2,\"index\":6,\"members\":[41,47,49],\"full_literals\":[-45,14,20,21]},{\"tag\":\"group_or\",\"kind\":2,\"index\":7,\"members\":[32,34,36,39,40],\"full_literals\":[-46,9,10,11,12,13]},{\"tag\":\"merge\",\"left\":[0],\"right\":[1],\"left_name\":\"grouped2_0000\",\"right_name\":\"grouped2_0004\",\"joined_name\":\"grouped2_0001\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-47,41,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-48,42,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[2],\"right\":[3],\"left_name\":\"grouped2_0005\",\"right_name\":\"grouped2_0007\",\"joined_name\":\"grouped2_0006\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-48,false,43],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-49,47,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1],\"right\":[2,3],\"left_name\":\"grouped2_0001\",\"right_name\":\"grouped2_0006\",\"joined_name\":\"grouped2_0002\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-49,false,48],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped2_0008\",\"right_name\":\"grouped2_0011\",\"joined_name\":\"grouped2_0009\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-50,false,44],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":0,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-51,45,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[6],\"right\":[7],\"left_name\":\"grouped2_0012\",\"right_name\":\"grouped2_0014\",\"joined_name\":\"grouped2_0013\",\"a\":1,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-51,false,46],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":1,\"b\":2,\"direction\":\"backward\",\"full_literals\":[-52,50,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[4,5],\"right\":[6,7],\"left_name\":\"grouped2_0009\",\"right_name\":\"grouped2_0013\",\"joined_name\":\"grouped2_0010\",\"a\":2,\"b\":1,\"direction\":\"backward\",\"full_literals\":[-52,false,51],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":3,\"b\":4,\"direction\":\"backward\",\"full_literals\":[-53,49,false],\"grouped\":true,\"kind\":2},{\"tag\":\"merge\",\"left\":[0,1,2,3],\"right\":[4,5,6,7],\"left_name\":\"grouped2_0002\",\"right_name\":\"grouped2_0010\",\"joined_name\":\"groupKind2\",\"a\":4,\"b\":3,\"direction\":\"backward\",\"full_literals\":[-53,false,52],\"grouped\":true,\"kind\":2},{\"tag\":\"quota_lower\",\"kind\":2,\"quota\":8,\"grouped\":true},{\"tag\":\"edge\",\"edge\":27,\"owners\":[9,17,23,42,46,47,49,59,60,62,67,72,73,75,80]}]}"
  "p cnf 53 89\n-10 -8 0\n-11 -8 0\n-12 -8 0\n-13 -8 0\n-14 -1 0\n-15 -14 0\n-16 -14 0\n-19 -14 0\n-20 -6 0\n-20 -7 0\n-20 -15 0\n-20 -16 0\n-20 -17 0\n-20 -18 0\n-20 -19 0\n-21 -1 0\n-21 -14 0\n-22 -14 0\n-24 -14 0\n-26 -25 0\n-29 -20 0\n-30 -21 0\n-31 -25 0\n-32 -25 0\n-33 -15 0\n-33 -17 0\n-33 -21 0\n-33 -23 0\n-33 -30 0\n-34 -26 0\n-34 -31 0\n-34 -32 0\n-35 -5 0\n-35 -27 0\n-36 -4 0\n-36 -5 0\n-36 -7 0\n-36 -28 0\n-36 -35 0\n-37 -3 0\n-37 -5 0\n-37 -7 0\n-37 -20 0\n-37 -29 0\n-37 -34 0\n-37 -35 0\n-37 -36 0\n-38 -36 0\n-39 -21 0\n-39 -33 0\n-14 4 35 37 38 0\n-2 1 15 19 20 21 33 0\n-28 1 15 20 21 33 0\n-29 1 15 19 21 33 0\n-30 1 15 19 20 0\n-20 -28 -33 0\n-5 1 15 19 20 21 40 0\n-21 5 36 37 0\n-37 1 15 19 21 40 0\n-39 1 15 19 20 0\n-9 33 0\n-22 26 32 33 0\n-23 26 31 32 0\n-24 26 31 33 0\n-27 3 34 36 0\n-28 3 34 35 0\n-27 4 37 38 0\n-29 4 35 38 0\n-40 33 0\n-41 6 8 18 19 25 34 0\n-42 7 27 28 29 30 0\n-43 35 36 37 39 0\n-44 15 16 17 22 23 24 0\n-45 14 20 21 0\n-46 9 10 11 12 13 0\n-47 41 0\n-48 42 0\n-48 43 0\n-49 47 0\n-49 48 0\n-50 44 0\n-51 45 0\n-51 46 0\n-52 50 0\n-52 51 0\n-53 49 0\n-53 52 0\n53 0\n1 2 5 15 19 20 21 28 29 30 33 36 37 39 40 0\n"
  "90 49 0 88 86 0\n91 52 0 88 87 0\n92 47 0 90 79 0\n93 48 0 90 80 0\n94 50 0 91 84 0\n95 51 0 91 85 0\n96 41 0 92 76 0\n97 42 0 93 77 0\n98 43 0 93 78 0\n99 44 0 94 81 0\n100 45 0 95 82 0\n101 46 0 95 83 0\n102 -5 39 0 98 33 36 41 72 0\n103 -37 1 40 0 97 100 40 42 43 44 45 46 47 65 66 71 22 74 6 8 59 0\n104 -14 20 29 36 1 33 0 69 103 6 8 17 52 53 60 57 55 89 0\n105 -21 36 37 0 49 58 102 0\n106 20 29 36 1 33 0 100 69 103 105 104 74 0\n107 36 20 1 33 0 100 69 103 105 74 106 6 8 54 0\n108 20 33 36 0 100 107 5 16 74 0\n109 -8 9 0 101 1 2 3 4 75 0\n110 -25 26 33 -20 0 99 13 12 11 23 24 64 63 62 73 0\n111 26 33 -20 0 96 99 61 109 15 14 13 12 11 9 110 70 31 32 64 63 62 73 0\n112 33 -20 0 96 15 14 9 61 109 111 20 30 70 0\n113 -20 36 0 98 97 10 21 43 112 29 50 56 72 71 34 0\n114 20 36 0 99 100 108 25 26 27 28 74 7 18 19 73 0\n115 36 0 113 114 0\n116 -4 0 115 35 0\n117 -7 0 115 37 0\n118 -28 0 115 38 0\n119 -35 0 115 39 0\n120 -37 0 115 47 0\n121 -38 0 115 48 0\n122 -27 0 116 120 121 67 0\n123 -29 0 119 116 121 68 0\n124 -14 0 121 116 120 119 51 0\n125 30 0 122 97 117 123 118 71 0\n126 -21 0 125 22 0\n127 -33 0 125 29 0\n128 20 0 126 100 124 74 0\n129 0 127 128 112 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record004.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record004.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record004.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record004.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record004 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record004.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record004.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record004.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record004.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record004 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record004_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record004 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record004_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record004_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00025.record004

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxErrors 5
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00025.record029
open Papers.RationalityTen

def vertexColumn : PackedGraphCertificate.Fields :=
  ⟨10, sparse_nat% "56aa64d876a38ce8b92e4785eca559a96354d475934cd8b52d4745da8d531ce8b62d4b32e2b4ad1b16e8731e2749ca719d1725e0f43c2f07e8c4c8560d88e13931a2685894550d60d2344d48d1314c3342c8b12c8711c2705c0f"⟩
def kindColumn : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6d249b69b49249369a4924d2492492492449249249249249249249"⟩
def data : FacetSat.Data :=
  FacetSat.RawProjection.data Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record029 vertexColumn kindColumn
theorem projection_checked :
    FacetSat.RawProjection.check Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record029 vertexColumn kindColumn = true := by
  decide +kernel

def facetIndex (i : Nat) : Fin data.count :=
  ⟨i % data.count, Nat.mod_lt _ (by decide)⟩
def ridgeIndex (i : Nat) : Fin 1024 :=
  ⟨i % 1024, Nat.mod_lt _ (by decide)⟩
def edgeCount : Nat := 45
def requiredEdges : Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record029.data.requiredEdges
def edgeRows : Fin edgeCount → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record029.data.edgeRows
def edgeIndex (i : Nat) : Fin edgeCount :=
  ⟨i % edgeCount, Nat.mod_lt _ (by decide)⟩

def requirements : Nat → Nat := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record029.data.quota

def groupMembers3 : ConcreteGrowth.Table (List (Fin data.count)) :=
(.branch 3
 (.branch 1
 (.leaf ([(facetIndex 42), (facetIndex 49)]))
 (.branch 2
 (.leaf ([(facetIndex 51), (facetIndex 60)]))
 (.leaf ([(facetIndex 65), (facetIndex 70)]))))
 (.branch 4
 (.leaf ([(facetIndex 63), (facetIndex 71)]))
 (.branch 5
 (.leaf ([(facetIndex 52), (facetIndex 61)]))
 (.leaf ([(facetIndex 64)])))))
def groupColors3 : PackedGraphCertificate.Fields :=
  ⟨3, sparse_nat% "6800156210000042z26;"⟩
def grouping3 : FacetSat.Grouping data.count where
  count := 6
  members := fun g => groupMembers3.get g
  color := fun c => groupColors3.get c.val
def groupKind3 : List Nat := List.range grouping3.count

def grouped3_0000 : List Nat := [0]
def grouped3_0001 : List Nat := [0, 1, 2]
def grouped3_0003 : List Nat := [1]
def grouped3_0004 : List Nat := [1, 2]
def grouped3_0005 : List Nat := [2]
def grouped3_0006 : List Nat := [3]
def grouped3_0007 : List Nat := [3, 4, 5]
def grouped3_0008 : List Nat := [4]
def grouped3_0009 : List Nat := [4, 5]
def grouped3_0010 : List Nat := [5]

theorem ridge_matrix_checked :
    data.ridgeMatrix = PackedIncidenceMatrix.code (ConcreteGrowth.ridgeList data.cells) :=
  FacetSat.RawProjection.ridge_matrix Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record029 vertexColumn kindColumn
    Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record029_matrix_checked

def leafCount : Nat := 0
def kindKeys : List Nat := [1, 2, 3]
theorem kindKeys_checked : FacetSat.RawProjection.kindKeysCheck data.toData.kind kindKeys = true := by
  decide +kernel
def leaves (j : Fin leafCount) : List (Fin data.count) := Fin.elim0 j

facet_model% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00025.record029" "{\"atoms\":[{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"group\",\"kind\":3,\"index\":0},{\"tag\":\"group\",\"kind\":3,\"index\":2},{\"tag\":\"group\",\"kind\":3,\"index\":3},{\"tag\":\"group\",\"kind\":3,\"index\":4},{\"tag\":\"group\",\"kind\":3,\"index\":5},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0004\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":2,\"list_name\":\"grouped3_0001\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0009\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":1,\"list_name\":\"grouped3_0007\"},{\"tag\":\"group_totalizer\",\"kind\":3,\"threshold\":3,\"list_name\":\"groupKind3\"}]}"
facet_atoms% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00025.record029" 33

facet_facts% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00025.record029" "{\"ridges\":[[7,266],[17,545],[29,266],[36,548],[40,266],[41,266],[42,554],[44,266],[45,266],[49,674],[51,284],[53,545],[58,545],[59,545],[60,344],[61,808],[65,554],[70,674]],\"owners\":[[7,266,[63,64,71],[29,40,41,44,45]],[29,266,[71],[7,40,41,44,45,63,64]],[40,266,[64],[7,29,41,44,45,63,71]],[41,266,[63,71],[7,29,40,44,45,64]],[44,266,[63,64],[7,29,40,41,45,71]],[45,266,[63,64,71],[7,29,40,41,44]],[17,545,[42,49,61],[36,53,58,59]],[53,545,[49],[17,36,42,58,59,61]],[58,545,[42,49,61],[17,36,53,59]],[59,545,[42,61],[17,36,49,53,58]],[36,548,[],[17,53,58,59,65,70]],[42,554,[65],[]],[65,554,[42],[]],[49,674,[70],[]],[70,674,[49],[]],[51,284,[63],[]],[60,344,[71],[]],[61,808,[],[]]],\"edges\":[[28,[7,29,40,41,44,45,51,52,60,61,63,64,71]],[38,[17,36,42,49,53,58,59,61,65,70]]],\"groupings\":[3]}"

facet_refute% "Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00025.record029" "{\"namespace\":\"Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00025.record029\",\"lower_only\":false,\"coverage\":true,\"edge_cover\":true,\"clauses\":[[-1,18,19,22],[-3,22],[-5,19],[-6,18,22],[-8,18,19],[-9,18,19,22],[-2,7,10,17],[-13,10],[-14,7,10,17],[-15,7,17],[-4],[-7,20],[-20,7],[-10,21],[-21,10],[-11,18],[-16,22],[-17],[-23,7,10],[-7,23],[-10,23],[-20,24],[-21,24],[-18,25],[-22,25],[-12,26],[-19,27],[-24,28],[-29,23,28],[-28,29],[-23,29],[-23,-28,30],[-27,31],[-26,31],[-31,32],[-25,32],[-30,-32,33],[-33],[1,3,5,6,8,9,11,12,16,17,18,19,22],[2,4,7,10,13,14,15,17,20,21]],\"atoms\":[{\"tag\":\"facet\",\"index\":7},{\"tag\":\"facet\",\"index\":17},{\"tag\":\"facet\",\"index\":29},{\"tag\":\"facet\",\"index\":36},{\"tag\":\"facet\",\"index\":40},{\"tag\":\"facet\",\"index\":41},{\"tag\":\"facet\",\"index\":42},{\"tag\":\"facet\",\"index\":44},{\"tag\":\"facet\",\"index\":45},{\"tag\":\"facet\",\"index\":49},{\"tag\":\"facet\",\"index\":51},{\"tag\":\"facet\",\"index\":52},{\"tag\":\"facet\",\"index\":53},{\"tag\":\"facet\",\"index\":58},{\"tag\":\"facet\",\"index\":59},{\"tag\":\"facet\",\"index\":60},{\"tag\":\"facet\",\"index\":61},{\"tag\":\"facet\",\"index\":63},{\"tag\":\"facet\",\"index\":64},{\"tag\":\"facet\",\"index\":65},{\"tag\":\"facet\",\"index\":70},{\"tag\":\"facet\",\"index\":71},{\"tag\":\"group\",\"index\":0,\"kind\":3},{\"tag\":\"group\",\"index\":2,\"kind\":3},{\"tag\":\"group\",\"index\":3,\"kind\":3},{\"tag\":\"group\",\"index\":4,\"kind\":3},{\"tag\":\"group\",\"index\":5,\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3},{\"tag\":\"group_totalizer\",\"kind\":3}],\"rules\":[{\"tag\":\"mate\",\"ridge\":266,\"a\":7,\"owners\":[63,64,71]},{\"tag\":\"mate\",\"ridge\":266,\"a\":29,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":266,\"a\":40,\"owners\":[64]},{\"tag\":\"mate\",\"ridge\":266,\"a\":41,\"owners\":[63,71]},{\"tag\":\"mate\",\"ridge\":266,\"a\":44,\"owners\":[63,64]},{\"tag\":\"mate\",\"ridge\":266,\"a\":45,\"owners\":[63,64,71]},{\"tag\":\"mate\",\"ridge\":545,\"a\":17,\"owners\":[42,49,61]},{\"tag\":\"mate\",\"ridge\":545,\"a\":53,\"owners\":[49]},{\"tag\":\"mate\",\"ridge\":545,\"a\":58,\"owners\":[42,49,61]},{\"tag\":\"mate\",\"ridge\":545,\"a\":59,\"owners\":[42,61]},{\"tag\":\"mate\",\"ridge\":548,\"a\":36,\"owners\":[]},{\"tag\":\"mate\",\"ridge\":554,\"a\":42,\"owners\":[65]},{\"tag\":\"mate\",\"ridge\":554,\"a\":65,\"owners\":[42]},{\"tag\":\"mate\",\"ridge\":674,\"a\":49,\"owners\":[70]},{\"tag\":\"mate\",\"ridge\":674,\"a\":70,\"owners\":[49]},{\"tag\":\"mate\",\"ridge\":284,\"a\":51,\"owners\":[63]},{\"tag\":\"mate\",\"ridge\":344,\"a\":60,\"owners\":[71]},{\"tag\":\"mate\",\"ridge\":808,\"a\":61,\"owners\":[]},{\"tag\":\"group_or\",\"kind\":3,\"index\":0,\"members\":[42,49],\"full_literals\":[-23,7,10]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":42,\"full_literals\":[-7,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":0,\"member\":49,\"full_literals\":[-10,23]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":65,\"full_literals\":[-20,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":2,\"member\":70,\"full_literals\":[-21,24]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":63,\"full_literals\":[-18,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":3,\"member\":71,\"full_literals\":[-22,25]},{\"tag\":\"group_take\",\"kind\":3,\"index\":4,\"member\":52,\"full_literals\":[-12,26]},{\"tag\":\"group_take\",\"kind\":3,\"index\":5,\"member\":64,\"full_literals\":[-19,27]},{\"tag\":\"merge\",\"left\":[1],\"right\":[2],\"left_name\":\"grouped3_0003\",\"right_name\":\"grouped3_0005\",\"joined_name\":\"grouped3_0004\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-24,28],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":0,\"direction\":\"backward\",\"full_literals\":[-29,23,28],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-28,29],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-23,false,29],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0],\"right\":[1,2],\"left_name\":\"grouped3_0000\",\"right_name\":\"grouped3_0004\",\"joined_name\":\"grouped3_0001\",\"a\":1,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-23,-28,30],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0009\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-27,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[4],\"right\":[5],\"left_name\":\"grouped3_0008\",\"right_name\":\"grouped3_0010\",\"joined_name\":\"grouped3_0009\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-26,false,31],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":0,\"b\":1,\"direction\":\"forward\",\"full_literals\":[false,-31,32],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[3],\"right\":[4,5],\"left_name\":\"grouped3_0006\",\"right_name\":\"grouped3_0009\",\"joined_name\":\"grouped3_0007\",\"a\":1,\"b\":0,\"direction\":\"forward\",\"full_literals\":[-25,false,32],\"grouped\":true,\"kind\":3},{\"tag\":\"merge\",\"left\":[0,1,2],\"right\":[3,4,5],\"left_name\":\"grouped3_0001\",\"right_name\":\"grouped3_0007\",\"joined_name\":\"groupKind3\",\"a\":2,\"b\":1,\"direction\":\"forward\",\"full_literals\":[-30,-32,33],\"grouped\":true,\"kind\":3},{\"tag\":\"quota_upper\",\"kind\":3,\"quota\":2,\"grouped\":true},{\"tag\":\"edge\",\"edge\":28,\"owners\":[7,29,40,41,44,45,51,52,60,61,63,64,71]},{\"tag\":\"edge\",\"edge\":38,\"owners\":[17,36,42,49,53,58,59,61,65,70]}]}"
  "p cnf 33 40\n-1 18 19 22 0\n-3 22 0\n-5 19 0\n-6 18 22 0\n-8 18 19 0\n-9 18 19 22 0\n-2 7 10 17 0\n-13 10 0\n-14 7 10 17 0\n-15 7 17 0\n-4 0\n-7 20 0\n-20 7 0\n-10 21 0\n-21 10 0\n-11 18 0\n-16 22 0\n-17 0\n-23 7 10 0\n-7 23 0\n-10 23 0\n-20 24 0\n-21 24 0\n-18 25 0\n-22 25 0\n-12 26 0\n-19 27 0\n-24 28 0\n-29 23 28 0\n-28 29 0\n-23 29 0\n-23 -28 30 0\n-27 31 0\n-26 31 0\n-31 32 0\n-25 32 0\n-30 -32 33 0\n-33 0\n1 3 5 6 8 9 11 12 16 17 18 19 22 0\n2 4 7 10 13 14 15 17 20 21 0\n"
  "41 1 3 5 6 8 9 11 12 16 18 19 22 0 18 39 0\n42 2 7 10 13 14 15 20 21 0 11 18 40 0\n43 29 0 18 30 31 28 20 21 22 23 7 10 8 9 42 0\n44 28 0 43 28 29 22 23 12 14 19 0\n45 7 10 0 18 7 10 13 8 15 9 42 0\n46 23 0 20 21 45 0\n47 30 0 46 44 32 0\n48 -32 0 47 38 37 0\n49 -31 0 48 35 0\n50 -25 0 48 36 0\n51 -27 0 49 33 0\n52 -26 0 49 34 0\n53 -18 0 50 24 0\n54 -22 0 50 25 0\n55 -19 0 51 27 0\n56 -12 0 52 26 0\n57 -6 0 53 54 4 0\n58 -11 0 53 16 0\n59 -3 0 54 2 0\n60 -16 0 54 17 0\n61 -5 0 55 3 0\n62 -1 0 55 53 54 1 0\n63 -8 0 55 53 5 0\n64 -9 0 55 53 54 6 0\n65 0 64 56 62 59 63 61 58 57 60 53 55 54 41 0\n"

theorem local_coverage
    (valid : GraphGrowthInputs.Valid Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record029.inputs)
    (matrix : MatrixGraphProblem.Checked Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record029.data)
    (B : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record029.n))
    (H : GraphGrowthConstraints.Target (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record029.inputs.problem valid) B) :
    ∃ j : Fin leafCount, GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
      (SparseGrowthDAG.family B) := by
  apply FacetSat.RawProjection.coverage_with_edges Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record029 valid matrix
    vertexColumn kindColumn projection_checked leaves _ B H
  intro S HS edgeCover noSame
  exact boundary_unsat S HS edgeCover noSame
def originalLeaf (j : Fin leafCount) : Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record029.l := Fin.elim0 j
def orbitWord (j : Fin leafCount) : List (Fin Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record029.g) := Fin.elim0 j
theorem orbit_words_checked : ∀ j : Fin leafCount,
    SparseGrowthDAG.sameCheck (Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record029.leaf (originalLeaf j))
      (GraphCaseCertificate.rawApplyWord Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record029.maps (orbitWord j) (leaves j)) = true := by
  decide +kernel

theorem direct_core : GraphCaseCertificate.DirectCore Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record029 where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record029_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record029_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record029_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record029_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record029_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record029_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record029_leaf_certificates_checked⟩
  complete := GraphCaseCertificate.complete_of_orbits Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record029 Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record029_validity
    leaves originalLeaf orbitWord orbit_words_checked
    (local_coverage Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record029_validity Papers.RationalityTen.CompactReplay.GraphInputsRow16Part00025.record029_matrix_checked)


end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow16Part00025.record029
