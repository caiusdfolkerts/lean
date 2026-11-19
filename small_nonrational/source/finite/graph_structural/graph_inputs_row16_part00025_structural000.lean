module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow16Part00025Data
public import GraphInputsRow16Part00025Frames
public import GraphInputsRow16Part00025Leaves
public import GraphInputsRow16Part00025Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

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
