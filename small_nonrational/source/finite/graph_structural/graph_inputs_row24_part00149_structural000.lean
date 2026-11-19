module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00149Data
public import GraphInputsRow24Part00149Frames
public import GraphInputsRow24Part00149Leaves
public import GraphInputsRow24Part00149Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00149.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record003
def vertexColumn : Fields := ⟨10, hexnat% "278cd2749b25c8f13c1f33296a3a4e8bac9aa669b16959568d936938ce8b92e2ba1e4785e0fa714e4b91e5a599655556354d4753352d1b51d1743d68e5354e334ccb332d2b2ad1b26c3b61e4751cc789d2729e1745c570dd0f0bc1f2b25216a462384e4c4a916439494a52344d0b51314c8b12c1b41c8711c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6db4db6db4db49b4da6d249b6d349349a4d34d249249a4d2692249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨68, by decide⟩, ⟨71, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨79, by decide⟩, ⟨87, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8412c2ec09fdb7000000", hexnat% "10000020000000000", hexnat% "8008000000000000000000", 422212465065984, hexnat% "800000200000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "809382acabc1b7000000", hexnat% "8000000001000000000000", 4629700416936869888, hexnat% "c000000001400000000", 171798691840]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8810c2eca87db7000000", hexnat% "4800000000000000000", hexnat% "8000000001000000000000", hexnat% "10000028000000000", hexnat% "20000010000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8091c2ac2ae9b7000000", hexnat% "20040010000000000", hexnat% "8000000001800000000000", hexnat% "c000000001400000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "801182ac2ac837000000", hexnat% "20040010000000000", hexnat% "4800000000000000000", hexnat% "8000000001800000000000", 4611686162308792320, hexnat% "8000000001400000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c6 c1
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c7 c0
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8088128049a9c035000000", hexnat% "10024000002000000", 4755801210798211072, hexnat% "800080020080000000", 257698037760, hexnat% "4000000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "48040ec0b2587000000", hexnat% "1800000c000000000", hexnat% "20200200000000000", hexnat% "8000000001800010000000", hexnat% "8000000001800000000", hexnat% "80100000000020000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "808010028da12d35000000", hexnat% "c000000001000000000", 4638707616225165312, hexnat% "38000004000000000", 11544872091648, hexnat% "800000000080000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c8000882b7db7000000", hexnat% "8000000001800000000000", 4639833516098453504, hexnat% "18000008000000000", hexnat% "80100200000000000000", hexnat% "20000000000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800003c2eda1cdb7000000", 206158430208, hexnat% "800000020000000000", hexnat% "4100000080000000000", hexnat% "88000000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8342eca345a6000000", 9223372586627366912, 240786604032, hexnat% "8080100001000000000000", hexnat% "4000000080000000000", hexnat% "8000000000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c14 c13
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80801242cda10531000000", hexnat% "18020000000000000", hexnat% "c000000001000000000", 174046838784, hexnat% "800000024000000000", 9345848836096]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c9002c8abfdb7000000", hexnat% "8080000001000000000000", 4621819117588971520, hexnat% "38000000000000000"]
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "80041002c98bcc37000000", hexnat% "800000200180000000", hexnat% "88000000001000000000", 4611686155866341376, hexnat% "18024000000000000", hexnat% "20000000000000000"]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c18 c17
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40242ec09bdb7000000", hexnat% "18000004000000000", hexnat% "800000220000000000", hexnat% "8088100000000000000000", 422212465065984]
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8382c8abc5a6000000", 4611686155866341376, hexnat% "c100000001000000000", 34644951040, hexnat% "8080000001000000000000", 10133099161583616]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "382cc294424000000", hexnat% "8000000001800010000000", 4620693217715683328, hexnat% "4800000000000000000", 2748795846656, hexnat% "88100000001000000000", 178241142784]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c22 c21
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c23 c20
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c24 c19
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c25 c16
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c26 c15
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c27 c12
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c28 c11
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c29 c10
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c30 c9
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c31 c8
  c32
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00149.record003

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00149.record004
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record004
def vertexColumn : Fields := ⟨10, hexnat% "3349b25c8f13ccca6a96a3a4eb26a99a699b16959568d936938ce8b92e2b86e8791e2785e0f93969665955558d5353352d1b51d2743d68e6394d538cd3332d2b1ad1b26c3b61e4751cc789d2729c6785d1725c570dd0f23c4f0bc1f950ac172522a85a2a459494a5454552344d0b41d48ca344c5322c4b0ac1b"⟩
def kindColumn : Fields := ⟨3, hexnat% "369b6d36db6d36db6d36da6d349a49249349a49249b6da4da69b492249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨68, by decide⟩, ⟨73, by decide⟩, ⟨81, by decide⟩, ⟨89, by decide⟩, ⟨94, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "42020010dfc0500141000000", 1411772930064384, 2251799813685248, hexnat% "20020001802000000", 184718154792960, hexnat% "2000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "42020010050dfc0141000000", hexnat% "20020001802000000", 5782621921543716864, 9223372036854775808, 756604737599569920, hexnat% "2000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20212952950194f000000", hexnat% "420000000000000000000000", 189115999977472, 774619135907725312, 4612811918334230528]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20000025fcd3c114f000000", 211106232532992, 9007233614479360, hexnat% "400200108000000000000000", hexnat% "2000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20fc4fc100f000000", 9288674231451648, 5764607527329202176, hexnat% "20200100008000040000000", hexnat% "2000000000800000000", hexnat% "400000008000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "202100be1fc194f000000", 9225623836668461056, hexnat% "21400000000000000", hexnat% "420000000000000000000000", 4612811918334230528]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40000000d3e5541149000000", hexnat% "20200100008000000000000", 864691128488689664, hexnat% "20000000800000000", hexnat% "2000000000004000000", 184717953466368]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40020010c300101048000000", hexnat% "2000000000c000000000000", hexnat% "21440000000000000", 9363441022140416, 612489549439827968, 184717953466368, hexnat% "2000000000900000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c11 c2
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c12 c1
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c13 c0
  c14
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record004_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00149.record004_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00149.record004
