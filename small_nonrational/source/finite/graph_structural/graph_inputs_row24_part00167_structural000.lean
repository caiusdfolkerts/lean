module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00167Data
public import GraphInputsRow24Part00167Frames
public import GraphInputsRow24Part00167Leaves
public import GraphInputsRow24Part00167Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00167.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00167.record000
def vertexColumn : Fields := ⟨10, hexnat% "f83d13c1f2b23cb2a3aa5a36a3a2e87a698e635a362d8765392e1b85e0fab1ca659366394e4b9696354d4b55352d4745d0f723a8da3a4e5334e332cf0b92d4b32e2b4acab86c9b16c3b61d4789d2729e1725c570dd0f13c2f07e38350b48a92a31926298d18645931495154c382d0b12d0721c47"⟩
def kindColumn : Fields := ⟨3, hexnat% "34db69b69b4934da6db6926db69b69b6db4da4924d34d269349a4d9249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨23, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨47, by decide⟩, ⟨54, by decide⟩, ⟨58, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨72, by decide⟩, ⟨75, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨82, by decide⟩, ⟨86, by decide⟩, ⟨91, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4280700009f280c000000", hexnat% "4001000000008000000000", hexnat% "80000000400000000000000", 18014398534647808, hexnat% "c0000000000220000000", 5368709120]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4280600408a2b0c800000", hexnat% "80040000000000000000000", hexnat% "81000000000040000000", hexnat% "4000000000118000000000", 4398063288320, hexnat% "10400000020000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "840280104001fab6d800000", hexnat% "400000000800000000000", hexnat% "60040000000000000", hexnat% "81000000000000000000", hexnat% "40000000000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "804280704409ba86c800000", hexnat% "4001000000000000000000", hexnat% "c0000000000200000000", 4402358255616]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "800e801040091a26c000000", hexnat% "4400000000000000000000", hexnat% "60040000800000000", 6601373122560, hexnat% "1000000000001000000", 8796093022208]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c4 c3
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c5 c2
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8046802044082280c800000", hexnat% "50000000000000000", hexnat% "4001000000008000000000", 13975420928, hexnat% "80000000000020000000", 31885837205504]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "60440802804000000", hexnat% "80068000000000008000000", hexnat% "4001000000008000000000", hexnat% "400010000010000000000", hexnat% "80000000000260000000", 6601373122560, 26388295843840]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨47, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨58, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨26, by decide⟩ c10 c1
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨37, by decide⟩ c11 c0
  c12
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00167.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00167.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00167.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00167.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00167.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00167.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00167.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00167.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00167.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00167.record000
