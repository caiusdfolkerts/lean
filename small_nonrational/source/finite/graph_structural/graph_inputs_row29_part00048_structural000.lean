module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00048Data
public import GraphInputsRow29Part00048Frames
public import GraphInputsRow29Part00048Leaves
public import GraphInputsRow29Part00048Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00048.record008
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00048.record008
def vertexColumn : Fields := ⟨10, hexnat% "16c3707c9cb8acaaaa5ab1aa68da8e87ae1b26a9966c5a9635a361d98e538ce4b8ae1b91e2785e0fa71e2729aa569c6699366391e785c96a559715a54d58d4756354d3352d2b46d4749d1743de0f23a8e6358f13a4e5334e331cf0ba2d8b52ccb8ad2b2ac6b86d1b26c5b0ef07a1d8751cc789d2729c6785d1725c570dd0f23c4f0bc1fc8a924a86a2685a4986625856c86914a469264594946525455"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db4d349a69a6934db4d349b69a6934d34d269b69a69369b6d36db6db69a6d26db6da69b49b6db249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨57, by decide⟩, ⟨62, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩, ⟨74, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨79, by decide⟩, ⟨81, by decide⟩, ⟨83, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨88, by decide⟩, ⟨90, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨97, by decide⟩, ⟨99, by decide⟩, ⟨103, by decide⟩, ⟨105, by decide⟩, ⟨106, by decide⟩, ⟨108, by decide⟩, ⟨110, by decide⟩, ⟨112, by decide⟩, ⟨114, by decide⟩, ⟨115, by decide⟩, ⟨117, by decide⟩, ⟨119, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10080000804000000000000000000", hexnat% "6030040000000000000000", hexnat% "50280400000000000000000", hexnat% "c0600800000000000000000000000", hexnat% "a05008000000000000000000000000", hexnat% "2400000120000000000000000", 4755892471538384896]
  c0
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00048.record008_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00048.record008_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00048.record008_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00048.record008_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00048.record008_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00048.record008_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00048.record008_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00048.record008_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00048.record008_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00048.record008

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00048.record023
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00048.record023
def vertexColumn : Fields := ⟨10, hexnat% "ccaaae1b26a99564d8ce2b91e27b31aa785c96a555535334ad4749de0f23a8e63c4d538cd33a2ccb8acab46c9bc1e8761d4731e2749ca725d0f1e0741b05c0f0721a85a0e866458560d88e1382e078711a4590e465454550d48d1342d07703a0e2318d1314c3322c4b0ac1b41c8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db6924936db492492492492492492492489249249249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fceffc00000000000", 3530822107858468864, hexnat% "cc00000000000000000", hexnat% "6600000000000000000000", hexnat% "3000000000000000000", hexnat% "1800000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3cfdffc00000000000", hexnat% "30200000000000000", hexnat% "3c00000000000000000", hexnat% "1e00000000000000000000", hexnat% "c000000000000000000", hexnat% "6000000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2007ffff7c00000000000", hexnat% "c800000000000000000", hexnat% "6400000000000000000000", hexnat% "1002000008000000000000", hexnat% "801000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fcff7400000000000", hexnat% "cc00000800000000000", hexnat% "6600000000000000000000", 3461016313634226176, hexnat% "3000000000000000000", hexnat% "1800000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7e00beffffc00000000000", hexnat% "8010000000000000000", hexnat% "3400000000000000000", hexnat% "4000000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7e007efdffc00000000000", hexnat% "10200000000000000", hexnat% "3800000000000000000", hexnat% "c000000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6003efdffc00000000000", hexnat% "1800000000000000000000", hexnat% "6000000000000000000000", hexnat% "10200000000000000", hexnat% "3c00000000000000000", hexnat% "c000000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c8 c5
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "a017fffffc00000000000", hexnat% "1002000000000000000000", hexnat% "4008000000000000000000", hexnat% "4800000000000000000", hexnat% "2400000000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "200437fffc00000000000", hexnat% "3800000000000000000", hexnat% "4008000000000000000000", hexnat% "1c00000000000000000000", hexnat% "3c8000000000000000", hexnat% "2004000000000000000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8013eadffc00000000000", hexnat% "1002001000000000000000", hexnat% "14200000000000000", hexnat% "cc00000000000000000", hexnat% "6600000000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "403c3d7c5c00000000000", hexnat% "4008000010000000000000", hexnat% "1a00000000000000000000", 2317102008282120192, hexnat% "3c0800000000000000", hexnat% "2004000002000000000000"]
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40080303d5800000000000", hexnat% "202020000000000000", hexnat% "1002001008400000000000", hexnat% "801080400000000000000", hexnat% "14c802000000000000", hexnat% "4c00000000000000000", hexnat% "2600000000000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨57, by decide⟩ c15 c14
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c16 c13
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c17 c12
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c18 c9
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c19 c4
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨54, by decide⟩ c20 c1
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c21 c0
  c22
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00048.record023_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00048.record023_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00048.record023_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00048.record023_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00048.record023_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00048.record023_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00048.record023_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00048.record023_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00048.record023_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00048.record023
