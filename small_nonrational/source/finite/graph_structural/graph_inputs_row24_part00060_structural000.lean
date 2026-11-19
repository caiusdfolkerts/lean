module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00060Data
public import GraphInputsRow24Part00060Frames
public import GraphInputsRow24Part00060Leaves
public import GraphInputsRow24Part00060Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00060.record009
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record009
def vertexColumn : Fields := ⟨10, hexnat% "e529c67392a699ae1b16a5996959568d9361da8e638ce2b86e8791e2785e0f879e1715955558d5351d68d634cd2b61d4745d0f783c4e5354e334cc73a2d8b32cab86d1b16c3bc1e8761e4751cc789d2729c6785d1715c3783d0f23c4f0bc1f1e0741b05c0f0721a85a0e869a15851948d1342da0d8318c8b12c2b"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6db6db6db4db69b6924db6d24936926db69249b49a4db6da6db6d24c9249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨32, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨78, by decide⟩, ⟨83, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [73113125234147328, hexnat% "81e000000000000000", hexnat% "410206040c0000000000", hexnat% "806000000018101800000"]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record009_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record009_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record009_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record009_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record009_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record009_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record009_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record009_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record009_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00060.record009

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00060.record016
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record016
def vertexColumn : Fields := ⟨10, hexnat% "2b8b92d4ad2aca70dc8f0bc568da2ea6659a568d94e4b85e0fae1786d1ac5c96a559364b9b16a59956539695954d58d4b5534cd4b4ad2745d0f56338d5334cb352ccb2ad1b26c5b0ed4749c670dd0f13ed09512a1582e078d14a4a9264550b41d50d2314d0b0ac1b11c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "da6db6db6da6d24da6d349b6db49b6d24926934d2492492449249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨64, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨72, by decide⟩, ⟨84, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10080005497f800000", hexnat% "280000000000000000", hexnat% "100100000c000000000000", hexnat% "10000002000000000", 288241373415473152, 2305895794361761792]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1001110c0c0c28c0800000", 1378684502016, 2305897993921888256, hexnat% "80000000003000000", 469762048, hexnat% "200000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1000180c041f49ff800000", hexnat% "1000008000000000000", 2305878202175717376, hexnat% "10000002000000000", hexnat% "200000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1808000f497f800000", hexnat% "200000200200000000", 139586437120, hexnat% "100100000c000000000000", 2594090977551450112, hexnat% "10000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "190c0c076bff800000", hexnat% "200000200000000000", hexnat% "1001000000000000000000", 2305860601399738368, 8796093022208]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "111080c046ad2800000", 1099729731584, hexnat% "1000000000180000000000", 4831838208, 2594110768760750080, hexnat% "280000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨25, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "100001080c002800800000", hexnat% "1100000040000000000", 1374725079040, 2594128370073600000, hexnat% "280000000001000000", 8803609214976, 167772160]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c9 c4
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c10 c1
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
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record016_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record016_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record016_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record016_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record016_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record016_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record016_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record016_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record016_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00060.record016

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00060.record023
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record023
def vertexColumn : Fields := ⟨10, hexnat% "2e8b61d45d2ac4f2e25cacaaaa6a3a8da1e96639956359361d8ae0fb61b4571b2669a6659365391e565554d54d475a362d4b51d2743db0e6358d5334d331ce8b92ccb8ac6b26c5b0ed4731d2719d1725c570dc8f270d2268962382e07a61585518a5254542d0746314c2b06c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6db6da6db4da49a69b6da4d369249a4934db4924da492489249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨71, by decide⟩, ⟨76, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "844186188c99800000", hexnat% "180000000000400000", hexnat% "10000040000000000", 9359043042738176, hexnat% "10000000020302000000", 140737488355328]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "19002340859fc00000", 142945101545472, 4612811952693968896, 36033195065475072, hexnat% "40100180000000000", hexnat% "10800000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1d00205e8589c00000", 4612811952693968896, 72620544259784704, 36310272062783488, hexnat% "10800000000202000000", 140737488355328]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1900a7c08f8fc00000", 13194407968768, hexnat% "10800000020000000000", hexnat% "44000100000000000", 72057594037927936]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "190025408f89c00000", 72620544259784704, 142936545165312, hexnat% "44000180000000000", 36033195132583936, hexnat% "10800000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "98018106838fc00000", hexnat% "10004000000400000000", 211106232532992, 9570149476597760, hexnat% "50000180000000000", 1125934266580992]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1d01a05c8089c00000", 1688850128699392, 4611686069966995456, 422212565729280, hexnat% "10800000020200000000", 4294967296]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "190127ce869fc00000", hexnat% "800080000000000000", hexnat% "10004000000100000000", 17626545782784, hexnat% "40000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "14126dc8c9d800000", 36310271995674624, hexnat% "40000000000000000", hexnat% "180000000000400000", hexnat% "10000000020302000000", hexnat% "800000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1d4101da8e9fc00000", 1688849860263936, 4402341478400, 45035996273704960, hexnat% "10800000000000000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10994001d2879fc00000", 1688884220002304, 13194139533312, hexnat% "40100000000000000", 45035996273704960]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10190001d2829fc00000", hexnat% "800180000000000000", 4402341478400, 9570149208162304, 4612811969873838080, hexnat% "40000080000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c14 c11
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "190000808099c00000", 36033195132583936, 1759252964179968, hexnat% "40100180000000000", 9288674231451648, hexnat% "10800000020202000000", 4611686039902224384]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨28, by decide⟩ c17 c10
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨64, by decide⟩ c18 c7
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨24, by decide⟩ c19 c6
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c20 c5
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨39, by decide⟩ c21 c2
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨23, by decide⟩ c22 c1
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
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record023_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record023_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record023_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record023_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record023_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record023_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record023_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record023_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00060.record023_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00060.record023
