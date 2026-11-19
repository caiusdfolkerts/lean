module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow24Part00137Data
public import GraphInputsRow24Part00137Frames
public import GraphInputsRow24Part00137Leaves
public import GraphInputsRow24Part00137Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00137.record004
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00137.record004
def vertexColumn : Fields := ⟨10, hexnat% "d525a1e966959561da1e4789e0fb519a6591e74599565c565555475a362d4749d0f56338e531ce4b1ae1b46c9b16c3b61e4751d2719e1725c570de0f43cac871522a8a64588e0b81e945512a619296154560d2342d0754328c6344c5322c2b06d0721c2705c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "1b6da69249a6db4934924924d24924d2492491249249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ecff5ffff6de00000000", 11529215046068469760, hexnat% "12000000000000000000", 10033043603456, hexnat% "1000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3e8ffd0ffb6d800000000", hexnat% "10002000000000000000", 10058813407232, hexnat% "1000100400000000000", 1008806316530991104, hexnat% "6000000000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fcff70fff6de00000000", 10033043603456, 1080863910568919040, 9223372036854775808, hexnat% "3000000000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .size 3
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .size 2
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨76, by decide⟩ c5 c4
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3effffffdbffe00000000", hexnat% "10000000000000000000", 633318697598976]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨53, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ecffffddbffe00000000", 9570149208162304, hexnat% "12000000000000000000", hexnat% "1000000400000000000"]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c9 c8
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fffff8ddbffe00000000", 9570149208162304, 72127962782105600, 432345564227567616]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c11 c8
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3ecff787fbffe00000000", hexnat% "12000000000000000000", hexnat% "1000100400000000000", 468374361246531584, 9223372036854775808]
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c13 c12
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c14 c10
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3fc7f705dbed400000000", 9571283079528448, hexnat% "1000100402200000000", 1044835113549955072, 9223372036854775808, hexnat% "2800000000000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨44, by decide⟩ c17 c3
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "3e82f107e058000000000", 1116892733357686784, hexnat% "50c000000000000000", hexnat% "10002000821000000000", hexnat% "7800000000000000000", 9242769620992, 404620279021568]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨52, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨51, by decide⟩ c20 c2
  c21
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00137.record004_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00137.record004_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00137.record004_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00137.record004_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00137.record004_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00137.record004_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00137.record004_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00137.record004_validity Papers.RationalityTen.CompactReplay.GraphInputsRow24Part00137.record004_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow24Part00137.record004
