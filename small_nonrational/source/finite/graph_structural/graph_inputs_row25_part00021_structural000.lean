module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow25Part00021Data
public import GraphInputsRow25Part00021Frames
public import GraphInputsRow25Part00021Leaves
public import GraphInputsRow25Part00021Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00021.record011
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record011
def vertexColumn : Fields := ⟨10, hexnat% "3707a1e45d1cc6b16c3b15c37362b89e2d4b329c972729aa5a8ea9695a369a68d9366392e2b89eb86715c5693a659564d9594e5554d58d5351d54d3352d2b46d4749d176c3a8e6358ce394d5334e334cc7392d4b32d2b2ac6b86d1b26c5b89d2785d1725c3743c2f5611c46926299164388e07a6138651324592948d0762328e1322c1b21c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "36db6da6db6db6db69a6924926d249a6db6d34d24d269369b6d34d2492492489249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨46, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨84, by decide⟩, ⟨86, by decide⟩, ⟨100, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "17c080022000137c000000", hexnat% "10004000000000000000000000", 633458284036096, hexnat% "30000010000000000000", hexnat% "1400080000400000000", hexnat% "2100804008000000000", 2377902836634615808]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "57c2c02b16029f7c000000", hexnat% "10000000100080000000000000", 70508330614784, hexnat% "11000000000000000000", hexnat% "20000020000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "17c0800300021b7c000000", hexnat% "10004000000000000000000000", 633458284036096, hexnat% "2102800008000000000", hexnat% "1400080000400000000", hexnat% "30000010000000000000", 10133099161583616]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c2 c1
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4432100836428718000000", hexnat% "10000000002080000000000000", hexnat% "1c00000000000000000", hexnat% "1380000000000004000000", hexnat% "40000300000000000000", 242665652224, 1610612736]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "17c040030400197c000000", hexnat% "2002800028000000000", hexnat% "10004000800000000000000000", hexnat% "20100020000000000000", 70379481595904, hexnat% "1000080002400000000", hexnat% "10000012000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10004041d02396023d08000000", hexnat% "30000000000000000000", hexnat% "1700000000000000000000", 4093640704, 9077576588853248, hexnat% "82000800008000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10004041d02396023d88000000", hexnat% "30000000000000000000", 1946157056, 9077576588853248, hexnat% "1700000000000000000000", hexnat% "82000800008000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "17c08002840035fc000000", hexnat% "11000002000000000000", hexnat% "10004000000000000000000000", 13581176216223744, hexnat% "402100020800000000", hexnat% "22100000000000000000", 576461302059237376]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "c1c0098400affc000000", hexnat% "1700000000000000000000", hexnat% "10004000000200001000000000", 13581167626289152, hexnat% "2002000020000000000", hexnat% "20100000000000000000", hexnat% "10000002000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10004040800284001568000000", hexnat% "1000002002000000000", hexnat% "20100020000000000000", hexnat% "1700000000000000000000", hexnat% "402100020800000000", hexnat% "10000010400000000000", hexnat% "82000800008004000000", 11005853696]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c10 c9
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c11 c8
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c12 c7
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c13 c6
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨78, by decide⟩ c14 c5
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨50, by decide⟩ c15 c4
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨27, by decide⟩ c16 c3
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨32, by decide⟩ c17 c0
  c18
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record011_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record011_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record011_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record011_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record011_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record011_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record011_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record011_validity Papers.RationalityTen.CompactReplay.GraphInputsRow25Part00021.record011_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow25Part00021.record011
