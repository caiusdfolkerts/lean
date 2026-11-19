module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00099Data
public import GraphInputsRow29Part00099Frames
public import GraphInputsRow29Part00099Leaves
public import GraphInputsRow29Part00099Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00099.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record001
def vertexColumn : Fields := ⟨10, hexnat% "ce2b89e0f8cd0f4372b29c8f2caaaa6aa6a5a8eaa6a5a36a3a2e87ac99a6598e635a362d8766394e3389e17b31ac6713c719a6659367256956539715356354d4b51d58d534cd4749d17723a8da398d6338e9394cd38ccb31ce8b62e4b52ccb86c9b16f0761d4731e2749ca719e1725c570dd0f23c4f07cb41d322c292629866c26192645925455c0e0b42c8b12d0721c47"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db69b6d36db6db6d249b49b6db6da4936db4da4db6926db6db6da49249249349349a499249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨67, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨105, by decide⟩, ⟨110, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2003c0000018100001ee1000000", hexnat% "4000000002080000010000000000", hexnat% "1c000000008000000000", hexnat% "c00000000000600c000000", 32985361416192, 432345564227567616]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20020c00009050000fecc800000", hexnat% "4000000000008000000000000000", hexnat% "1e000000000000000000", hexnat% "1c0000000000000020000000", 144115188096827392, 34084860461056]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20020c00008830000feac400000", hexnat% "4000000000010000000000000000", hexnat% "1e000000000000000000", hexnat% "1c0000000000000040000000", 288230376176877568, 34084860461056]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "20020000000010000108c000000", hexnat% "1e000000008000000000", hexnat% "4000000000098000000000000000", hexnat% "1cc000000000000000000000", 61740154880, 432345564256927744, 34497177321472]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c4 c1
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c5 c0
  c6
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record001_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00099.record001

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00099.record010
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record010
def vertexColumn : Fields := ⟨10, hexnat% "3d0ec372b29c8f26a96a3ab1a368e635a362d8763392e2b86eac6713c5a95a4e9c64d9394d58d4b51d4cd4b4ad1b6a368e6358ce3c4e9394cd38ccb31cf0b62d4b32d2b2ac6b86d1b31e2749e170dd0f0bc9c173222685a29866258562384e07b212645929465254552344d0770388d2328c6384c9314d0b22c4b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6d36db6d24d24d26db6da49a49a492492492492492492492449249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨101, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [33989202949439488, 4467575228398043136, hexnat% "3000180007008000000000", hexnat% "30001800180220000000000", hexnat% "2038801c404000000000000000", hexnat% "78000180000000000"]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record010_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record010_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00099.record010

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00099.record023
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record023
def vertexColumn : Fields := ⟨10, hexnat% "3707c9c8da8e87ac9966c58d68d8763392e2b83e9c4d98e479c9565c54d58d4753352d2b43d98d63c4e9394cd38cc7332e2b4acab86c3bc1d8751cc789ca785d170dd0f1b09c173221a89a16926198961588e1382e07b211a49916525194951548d1342d0770388d2318e1324c5322c4b0ac1b41c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1269a49a69249a69269a492492492492492492492249249249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffeeb12307ff00000000000", hexnat% "1c080000000000000", hexnat% "10600000000000000000", hexnat% "104800800000000000000", hexnat% "c0700000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨89, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3bbc7fff2307ff00000000000", hexnat% "1c080000000000000", hexnat% "41800000000000000000000", hexnat% "402000000800000000000000", hexnat% "c0700000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨89, by decide⟩ c1 c3
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1b2c6cb1bf0c0e00000000000", hexnat% "800200101100000000000", 17451448556060672, hexnat% "40600000000000000", hexnat% "30400000000000000000", hexnat% "c1000000000000000000000", hexnat% "2412104800800000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1f2c6cb13f4c0e00000000000", hexnat% "c0303000000000000", hexnat% "800200000100000000000", 16888498602639360, hexnat% "30400000000000000000", hexnat% "2012104800800000000000000", hexnat% "c1000000000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1bffeffd2327ff00000000000", hexnat% "200100000000000000", hexnat% "1c080000000000000", hexnat% "c0400000000000000", hexnat% "2400100000800000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1bbd6ffd2307ff00000000000", hexnat% "1c080000000000000", hexnat% "40000040000000000000000", hexnat% "800200100000000000000", hexnat% "2402100000800000000000000", hexnat% "80600000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨75, by decide⟩ c1 c9
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "ab86ab12003ff00000000000", hexnat% "1f0c0000000000000", hexnat% "10600000000000000000", hexnat% "41800000000000000000000", hexnat% "2402104800800000000000000", hexnat% "c0700000000000000", hexnat% "1104040000000000000000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1bfd6eb10307ff00000000000", hexnat% "3c080000000000000", hexnat% "10600000000000000000", hexnat% "800000100000000000000", hexnat% "c0600000000000000", hexnat% "2402104800800000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "1b2c7cb13f4c0e00000000000", hexnat% "c0303000000000000", hexnat% "800200000100000000000", 16888498602639360, hexnat% "30400000000000000000", hexnat% "c1000000000000000000000", hexnat% "2412004800800000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [hexnat% "3fffffffffffff00000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨79, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨87, by decide⟩ c16 c13
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨89, by decide⟩ c17 c12
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c18 c5
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨93, by decide⟩ c19 c6
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c20 c5
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨68, by decide⟩ c21 c4
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c22 c2
  c23
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record023_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record023_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record023_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record023_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record023_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record023_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record023_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record023_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record023_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00099.record023

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00099.record024
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record024
def vertexColumn : Fields := ⟨10, hexnat% "32c9b0dc8f07cca96a3693a1eb26358b6c38ce8b92e1b83eca6695a4d98e5391e725994d58d4b5c368d934cd8b52d1b61d0f72358cd34ccb3c2d8b52ccb8ad2b1ad1b0ef0731e2749ca783d0f0bc742705c1c89a16866258560d88e1381ec8471c24991662519495154358348d1341d48c6324c530cd0b22c4b06c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "da69b4d349a6d24da6d24924924d249249249a493492491249249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨80, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨88, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨93, by decide⟩, ⟨95, by decide⟩, ⟨98, by decide⟩, ⟨100, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "14ad38200a83de0e0000000000", hexnat% "f10000000000000000", 3170586914226962432, hexnat% "10004000400000000000", hexnat% "b000000000000000000", hexnat% "104001000800000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4ac39200abdde260000000000", 4755880371340443648, hexnat% "f10000000000000000", hexnat% "1a000000000000000000", hexnat% "10010004000000800000000000", hexnat% "1000000100000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "42438210aefde360000000000", hexnat% "10800000000000000000", hexnat% "710000080000000000", hexnat% "a000000400000000000", hexnat% "10890104001000800000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "108d310512145afe0000000000", 253327479039590400, 7493989779944505344, hexnat% "e90000000000000000", hexnat% "4200820008000000000000000", hexnat% "1a000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "42438210abddeb60000000000", 4755880371340443648, hexnat% "f10000000000000000", hexnat% "1a000000000000000000", hexnat% "10890104000000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4101f0b841af20000000000", 7493989779944505344, hexnat% "f000000c0000000000", 271341877549072384, hexnat% "4202820000000000000000000", hexnat% "10890100001000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4100300041a900000000000", 271355071688605696, 7494095333060771840, hexnat% "18080000000000000000", hexnat% "f10000000000000000", hexnat% "4202820028000020000000000", hexnat% "10890104001000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨73, by decide⟩ c6 c5
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c7 c4
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c8 c3
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c9 c2
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c10 c1
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c11 c0
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record024_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record024_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record024_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record024_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record024_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record024_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record024_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record024_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00099.record024_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00099.record024
