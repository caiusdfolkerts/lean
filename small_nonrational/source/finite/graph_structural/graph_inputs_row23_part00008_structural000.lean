module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow23Part00008Data
public import GraphInputsRow23Part00008Frames
public import GraphInputsRow23Part00008Leaves
public import GraphInputsRow23Part00008Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00008.record007
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record007
def vertexColumn : Fields := ⟨10, hexnat% "2f07c2e87ad1a562d876c398e9394e3392e1b91e278b91e745954b51d70d6364d534cd4b46d4749dd0e532cc73c2d8b92d4b32d2b1ad1b26e8761d4731e2749c6785d1725e0f2b05c0f0aa1683ac1a46298560d90e2384e0b81e2a4590e705914a5154354348d1342d0770390ca314c3342c8b12c2b06e0741c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "12492492492492492492492492492492492492492489249249249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6040c0b6c5ffc00000000000", hexnat% "618000000000000000000", hexnat% "30c0000000000000000000000", hexnat% "100020010000000000000000", hexnat% "14008801000800000000000000", hexnat% "20004002000000000000000", hexnat% "28803100480200000000000000", hexnat% "10002001000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "37fe0500281ffc00000000000", hexnat% "304000000000000000", hexnat% "608000000000000000000", hexnat% "13e00000000000000", hexnat% "27c00000000000000000", hexnat% "14000880040000000000000000", hexnat% "28801100080000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "29c833805c03ffc00000000000", hexnat% "14008801000800000000000000", hexnat% "2040408204000000000000000", hexnat% "334000000000000000000000", hexnat% "3b400000000000000", hexnat% "76800000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2806ffc281ffc00000000000", hexnat% "304000000000000000", hexnat% "3040000000000000000000000", hexnat% "13e00000000000000", hexnat% "13e000000000000000000000", hexnat% "28801100080000000000000000", hexnat% "14400800040000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20c041833ffffc00000000000", hexnat% "1000200000000000000000000", hexnat% "100020000000000000000000", hexnat% "47c00000000000000000", hexnat% "23e000000000000000000000", hexnat% "c0000000000000000", hexnat% "28801100000000000000000000", hexnat% "14400880000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2ad055a2a51ffc00000000000", hexnat% "100020010000000000000000", hexnat% "1000200100000000000000000", 12538021362599460864, hexnat% "20004000000000000000000", hexnat% "28003000400000000000000000", hexnat% "10004000800000000000000000", hexnat% "4408881040000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "208041020415bc00000000000", hexnat% "100020010080000000000000", hexnat% "1000200100024000000000000", hexnat% "20004002000000000000000", hexnat% "29e00000000000000", hexnat% "28803100480000000000000000", hexnat% "4b800000000000000000", hexnat% "25c000000000000000000000", hexnat% "14400880040000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨62, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c9 c2
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨91, by decide⟩ c10 c1
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c11 c0
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record007_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record007_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record007_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record007_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record007_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record007_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record007_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record007_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record007_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00008.record007

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00008.record037
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record037
def vertexColumn : Fields := ⟨10, hexnat% "ea2eb168d8b6538ce2b86e0f9c93a4b9d15558d5352d70d3352d2b46d4743d38f13a4cd38cd4b1ac9b0ef0791d4731e2729c6745c9715e0f43c8f07f14530b2328aa858361382ec44b1524c92a70551615454354344d0b4c328e1324c3322c4b0ae0711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "92492492492492492492492492492492492449249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "607cefede3f3800000000", hexnat% "58000000000000000000", hexnat% "80000020008000000000", 492856087150592, hexnat% "310000000000000000", hexnat% "120000100000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "605c096de2d1000000000", hexnat% "4a000000000000000000", hexnat% "10022000000000000000", 513368850956288, hexnat% "80120000000000000", hexnat% "120000000000000000000", hexnat% "80000000000000000000", hexnat% "354800000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "59c2f61a293000000000", hexnat% "600000004000000000000", 63050944539000832, hexnat% "24000000000000000000", hexnat% "350800020000000000", hexnat% "82000000100800000000", hexnat% "100080101000000000000", 215779156951040]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "180b218000000000000", 64177394201657344, hexnat% "180080000020000000000", hexnat% "354800000000000000", hexnat% "202400402080800000000", hexnat% "41c000000001000000000", hexnat% "20000101402000000000", hexnat% "40020000200000000000", 163552354631680]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c5 c2
  c6
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record037_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record037_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record037_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record037_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record037_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record037_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record037_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record037_validity Papers.RationalityTen.CompactReplay.GraphInputsRow23Part00008.record037_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow23Part00008.record037
