module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow26Part00085Data
public import GraphInputsRow26Part00085Frames
public import GraphInputsRow26Part00085Leaves
public import GraphInputsRow26Part00085Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00085.record010
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record010
def vertexColumn : Fields := ⟨10, hexnat% "dccc8da8e93ac9b16a599695956358ce8b92e2b86e8791e2785ecc4d98e539c9715a559595555354cd8b52d2b46d8751d2745dc8f13a4d9394d5334e334cccb8ad2b2ac6b86d1b0ef07a1d8791d4731ca719e1745c9715e0f43c1f2685a899262384e0b899166254948d1342d88d2384d1324c5322c4b0ac1b81d0721c4709c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "da6d36db69249b49a6d36db69249b492492492492492492492492489249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2, 3]
def candidates : List (Fin raw.n) := [⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩, ⟨102, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7dfc3fffffc090009e40000000", hexnat% "203c000000000000000000000", 34503619772416, 2261053303544610816, 2310065133864353792]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "6ff83efffff000101e40000000", hexnat% "10040100000090008000000000", hexnat% "3c000000000000000000000", 16911433728000, 1108131798937763840, 4222124650659840]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7dfeffdfe3c098809f40000000", hexnat% "201c0000000000000000", hexnat% "2010000000000006000000000", 2307848518422757376, 34087007944704, 2260877381684166656]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7dfdffdfd3c094409ec0000000", hexnat% "202c0000000000000000", hexnat% "2020000000000006000000000", 2308974418329600000, 34089155428352, 2260947750428344320]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7dfc3fdfc3c890089e40000000", 25707526750208, 1684592551241187328, hexnat% "203c0000000000000000", hexnat% "203c000000000000000000000", 2310065133864353792]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7dfc3fdfc3c490049e40000000", 30105573261312, 1972822927392899072, hexnat% "203c0000000000000000", hexnat% "203c000000000000000000000", 2310065133864353792]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7dfc3fdfc3c290029e40000000", 32304596516864, 2116938115468754944, hexnat% "203c0000000000000000", hexnat% "203c000000000000000000000", 2310065133864353792]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "7dfc3fdfc3c190019e40000000", 33404108144640, 2188995709506682880, hexnat% "203c0000000000000000", hexnat% "203c000000000000000000000", 2310065133864353792]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 3 [hexnat% "53ffffe07cffffffffc0000000", hexnat% "2c000000000000000000000000", hexnat% "1f830000000000000000"]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨91, by decide⟩ c8 c0
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨92, by decide⟩ c9 c7
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨93, by decide⟩ c10 c6
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨94, by decide⟩ c11 c5
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨95, by decide⟩ c12 c4
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c13 c3
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨85, by decide⟩ c14 c2
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨96, by decide⟩ c15 c1
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨102, by decide⟩ c16 c0
  c17
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record010_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record010_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record010_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record010_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record010_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record010_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record010_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record010_validity Papers.RationalityTen.CompactReplay.GraphInputsRow26Part00085.record010_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow26Part00085.record010
