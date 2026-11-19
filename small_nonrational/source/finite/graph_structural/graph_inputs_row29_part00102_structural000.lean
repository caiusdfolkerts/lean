module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00102Data
public import GraphInputsRow29Part00102Frames
public import GraphInputsRow29Part00102Leaves
public import GraphInputsRow29Part00102Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00102.record001
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00102.record001
def vertexColumn : Fields := ⟨10, hexnat% "31ca725c3723c2f07cc699a568da4e8ba1eb16358b6c38ce2ba1e4789e1783ec669966659564d98e5392e479c5695954d58d4b5c368d934cd8b4ad8751d2745d0f71364d5334d332cf0b62d4b32d2b2ae1b46c9b16c3bc1cc729e1745e0f43c1f1d06c1c86a19896158362384e0bb111c7091a46585495154358348d1342d18d1324c530cd0b22c4b0ac8711c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "db6da6db6d349a4da4936db6da4924924924d24924924924d249a492489249249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨101, by decide⟩, ⟨108, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "d9c00104308219fc000000000", 133419138960850944, 8502796096475496448, hexnat% "3b80000000000000000", hexnat% "ec000000000000000000", hexnat% "1020020100008000400000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10201e01000bfffbdfc000000000", hexnat% "1800000000000000000000000", hexnat% "c000000000000000000000000", hexnat% "3f00000000000000000", hexnat% "fc000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10291e01104bfffbd2c000000000", hexnat% "4800004100000080000000000", hexnat% "3a00000010000000000", hexnat% "e8000000040000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "49400041283fb5fc000000000", 8935141660703064064, hexnat% "9080000000000000000000000", hexnat% "3e80000000000000000", hexnat% "f8000000000000000000", hexnat% "1020020100010000800000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "90000fc4bfe239e4000000000", hexnat% "3b00000018000000000", hexnat% "10201e0100000000400000000000", hexnat% "4800000000008000000000000", 130604389193744384]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "fffb80039fc000000000", 141863388262170624, hexnat% "10201e0100000000400000000000", hexnat% "1800000000000000000000000", 9079256848778919936, hexnat% "c000000000000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "d9c0015500a2b9e4000000000", 8358680908399640576, hexnat% "e8080000000000000000", 130606038461186048, hexnat% "1020020100038000400000000000", hexnat% "2a00000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "102d1e01114bbefbdac000000000", 4683749110023454720, hexnat% "800004100000000000000000", hexnat% "e8000000000000000000", hexnat% "2a00000000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "d000013fb89fbd9c000000000", hexnat% "ec000000060000000000", hexnat% "10201e0100000000000000000000", hexnat% "800000000200000000000000", 8358680908399640576]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "40000114001fbd98000000000", 9079263445848686592, hexnat% "91c0000000000004000000000", hexnat% "2b80000000000000000", hexnat% "ec000000000000000000", hexnat% "1020020100038000000000000000", hexnat% "800000000000000000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c10 c7
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨98, by decide⟩ c11 c6
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c12 c5
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c13 c4
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c14 c1
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c15 c3
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c16 c2
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c17 c1
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c18 c0
  c19
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00102.record001_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00102.record001_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00102.record001_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00102.record001_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00102.record001_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00102.record001_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00102.record001_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00102.record001_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00102.record001_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00102.record001
