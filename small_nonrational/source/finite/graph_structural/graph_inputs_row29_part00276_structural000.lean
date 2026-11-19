module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00276Data
public import GraphInputsRow29Part00276Frames
public import GraphInputsRow29Part00276Leaves
public import GraphInputsRow29Part00276Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00276.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00276.record000
def vertexColumn : Fields := ⟨10, hexnat% "3343b0dc8f13ccc8ea36a3a4eb26a99a639b169595635a364d8ce8b92e2b86e8791e2785e0fb313a4d98e539c96a5694e5c5655554d58d5358b52d1b61d4749d0f723a8da338f1394d5334e334ce2b4ac6b86d1b26c3bc1e8761e4751cc789d2729c6785d1725c570de0f43c8f13c2f07ccc2b05c328aa168c92a45931625494a5855151548d1342d074c388d2328e1344c5322c4b0ac1b"⟩
def kindColumn : Fields := ⟨3, hexnat% "349b6936db6db6da6d36da6d26d24924924924924924924924926db6924d269b692449249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨92, by decide⟩, ⟨97, by decide⟩, ⟨100, by decide⟩, ⟨113, by decide⟩, ⟨114, by decide⟩, ⟨118, by decide⟩, ⟨119, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c60000033ffffe3f30480780000000", hexnat% "12100000000000334000000000", hexnat% "1c0c0000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "840000023fbfe21910000780000000", hexnat% "1c0600380000000000", hexnat% "420000010040002020000000000000", hexnat% "1c0c0034000000000", hexnat% "12100000000000400000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c6000003044263e7f0000780000000", hexnat% "1c1800000000000000", hexnat% "381800000034000000000", hexnat% "12100000000000780000000000", hexnat% "383c000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "840012123c0e7e07307b4780000000", hexnat% "420000010040002000000000000000", hexnat% "1d8c0000000000000", hexnat% "3b1800000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c60000033c4e622120480700000000", hexnat% "1c0600300000000000", hexnat% "12100000000000034080000000", hexnat% "3b1800000000000000000", hexnat% "1d8d0000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8400000204323fdff0000780000000", hexnat% "420000010040402000000000000000", hexnat% "380c000000380000000000", hexnat% "381800000034000000000", hexnat% "12100000000000400000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4200121107c3e1e1f07b4780000000", hexnat% "840000020000020000000000000000", hexnat% "383c000000000000000000", hexnat% "1c1e00000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c6000003044263e1f0404780000000", hexnat% "381800000030000000000", hexnat% "12100000000000380000000000", hexnat% "1c1e00000000000000", hexnat% "383c000000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "840012123c2e3e37307b4780000000", hexnat% "1c8c0000000000000", hexnat% "391800000000000000000", hexnat% "420000010040400000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "840012123c1e3e2f307b4780000000", hexnat% "1d0c0000000000000", hexnat% "3a1800000000000000000", hexnat% "420000010040400000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c60012130402622130780780000000", hexnat% "1c1e00000000000000", hexnat% "383c000000000000000000", hexnat% "3c1800000004000000000", hexnat% "1c0c0030000000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c60012130442602130704780000000", hexnat% "1e0600080000000000", hexnat% "383c000000000000000000", hexnat% "1d8c0000000000000", hexnat% "381800000030000000000"]
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "60010030400202030300180000000", hexnat% "c00000000002400000000000000000", hexnat% "383c000000000000000000", hexnat% "1d8c0000000000000", hexnat% "1e0700000000000000", hexnat% "21000000000004b4600000000", hexnat% "3c1800000000000000000"]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨88, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨89, by decide⟩ c14 c11
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c15 c10
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨45, by decide⟩ c16 c9
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c17 c8
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c18 c7
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c19 c6
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨82, by decide⟩ c20 c5
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c21 c4
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c22 c3
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c23 c2
  c24
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00276.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00276.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00276.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00276.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00276.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00276.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00276.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00276.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00276.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00276.record000
