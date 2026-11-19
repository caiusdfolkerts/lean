module
prelude
public import FacetCliqueRaw
public import GraphDirectCore
public import GraphInputsRow29Part00094Data
public import GraphInputsRow29Part00094Frames
public import GraphInputsRow29Part00094Leaves
public import GraphInputsRow29Part00094Metadata
public meta import HexNatLiteral
public meta import KernelDecideContext

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00094.record000
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record000
def vertexColumn : Fields := ⟨10, hexnat% "ce0f8ad0f4cb0ec3723c2f07cccab2cab1a36a3a4e8bac9aa669a96958d68d8b6c394e33a2e4b8ae8789e1783ecc4f13a4d94e4b91e725694e5356352d475534cd2b46d2745d0f72368f138cd332cd4b32d2b2ad1b26c3bc1d8751e2749ca785c9715c3723c2f07f244b0d216b063190e138d12c52916439315252950d1342d30c9314d0b12c1b41c8711c0f"⟩
def kindColumn : Fields := ⟨3, hexnat% "6db4db6db6d36d36da6d24d36d369a4924934d249a4db6d249a4924d2693491249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨74, by decide⟩, ⟨77, by decide⟩, ⟨81, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨88, by decide⟩, ⟨93, by decide⟩, ⟨97, by decide⟩, ⟨107, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "802203a25debc83ceb4e0000000", 1108101562368, hexnat% "200000100000000000", hexnat% "10000000100000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "802203a21dcbc838ab0e0000000", 1125281431552, 92358976733184, hexnat% "4200000000000000000", hexnat% "10000020100000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨49, by decide⟩ c1 c0
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "802203a01dcbc808830c0000000", hexnat% "4200000000000000000", 3848290697216, 373834490314752, hexnat% "10020020100000600000000", 562949953421312]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c3 c2
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000805e01c839c06e0000000", hexnat% "10020028100000000000000", hexnat% "c0000011000000000", hexnat% "800200200100000002000000000", hexnat% "3000000000028000000000", 2305913377957871616]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "13a20eaad81de86e0000000", hexnat% "40000011000000000", hexnat% "800200000100000002000000000", hexnat% "5000002000000000000", hexnat% "2000000001000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "11020eaad81dc06e0000000", hexnat% "4040000000000000000", hexnat% "800200200100000002000000000", hexnat% "2000801001000000000000000", 563018672898048, hexnat% "2000000000038000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c7 c6
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2200a05e63d83dcb2e0000000", hexnat% "800000000180000000000000000", hexnat% "3000000000020000000000", hexnat% "10020008000000400000000", 1099511627776]
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "802203a015e3d80cbb2c0000000", hexnat% "a00000140000000000", hexnat% "20000001000020000000", hexnat% "4008002000400000000", hexnat% "10000000000000000000000"]
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2002801e63d80de92c0000000", hexnat% "80000012000000000", hexnat% "4008002000400000000", hexnat% "1020000001000020000000", hexnat% "10000000000000000000000", hexnat% "800200200100000000000000000"]
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨41, by decide⟩ c11 c10
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨85, by decide⟩ c12 c10
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨46, by decide⟩ c13 c9
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "12021aebd81dfb6e0000000", hexnat% "4400002000000000000", hexnat% "1800000000000000000000", hexnat% "2000000000000000000000000", hexnat% "800200200100000000000000000"]
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "10021a2bd81dd0660000000", hexnat% "4040000000000000000", hexnat% "2000800400000000080000000", hexnat% "800000000180000002000000000", hexnat% "3000000000028000000000", hexnat% "200200000002001000000000"]
  let c17 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c16 c15
  let c18 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8002122251e9982cf3660000000", hexnat% "2000800400000000080000000", hexnat% "a00000100000000000", hexnat% "1000002001008000000000", 288230376151711744]
  let c19 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "22108254699828816a0000000", hexnat% "800000000180000002000000000", hexnat% "a00400000000000000", hexnat% "2000000000038000000000", 373835027185664, hexnat% "1200002000000000000000"]
  let c20 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨93, by decide⟩ c19 c18
  let c21 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "201182146bd819bb6e0000000", hexnat% "800000000180000000000000000", hexnat% "a00000040000000000", hexnat% "4000002000000000000", hexnat% "202200000000000000000000", 70368744177664]
  let c22 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8002022001e19824f30c0000000", hexnat% "a00000100000000000", hexnat% "1000002001008020000000", hexnat% "4000400000000000000", hexnat% "2000801400000800000000000", hexnat% "10020008000000600000000"]
  let c23 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "22108254e99828816a0000000", hexnat% "a00400000000000000", hexnat% "800000200100000002000000000", hexnat% "2000000000038000000000", 373835027185664, hexnat% "1000002000000000000000"]
  let c24 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "202205ee9d825fb6e0000000", hexnat% "800000000100000000000000000", hexnat% "1000002001000000000000", hexnat% "2010820000000800000000000"]
  let c25 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8002022003e99800bb6e0000000", hexnat% "4000400000000000000", hexnat% "2010820000000800000000000", hexnat% "800000540000000000", hexnat% "1000002001000000000000", hexnat% "1400002000000000000"]
  let c26 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨69, by decide⟩ c25 c24
  let c27 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2012201eb983dfb6e0000000", hexnat% "800002000000000000000000000", hexnat% "2010800000000000000000000", hexnat% "a00400000000000000", hexnat% "5400000000000000000"]
  let c28 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8002002001e99834db4c0000000", hexnat% "3000000000020000000000", 2594073385902276608, hexnat% "a00000100000000000", hexnat% "5400000000000000000", hexnat% "2010820000000800200000000"]
  let c29 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c28 c27
  let c30 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "802203a057ebd82cf32c0000000", hexnat% "800000100000000000", 282025269395456, hexnat% "10020000000000400000000"]
  let c31 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2201a25e2bd83dd92e0000000", hexnat% "10000000000000400000000", hexnat% "2000000000022000000000", hexnat% "c0000000000000000", hexnat% "800000000100000000000000000"]
  let c32 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2200a056699838d1680000000", hexnat% "10020000000000020000000", hexnat% "800000500040000000", hexnat% "800000000180000002000000000", hexnat% "3000000000028000000000", 2594073385365405696]
  let c33 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨48, by decide⟩ c32 c31
  let c34 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨81, by decide⟩ c33 c30
  let c35 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2012019abd835fb0e0000000", hexnat% "800002000000000000000000000", hexnat% "4240000000000000000", hexnat% "2000800400000800000000000", hexnat% "10020000000000600000000"]
  let c36 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2213a2546b9838b96e0000000", hexnat% "80400000000000000", hexnat% "800000000100000002000000000", hexnat% "800000540000000000", hexnat% "200000000000000000"]
  let c37 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "211025e6bd83dd96e0000000", hexnat% "2000800000000000000000000", hexnat% "800000000180000002000000000", hexnat% "2200000000020000000000"]
  let c38 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8002132259e99828bb6e0000000", 2594073385365405696, hexnat% "2000800400000000000000000", 373833953443840, hexnat% "200000000000000000"]
  let c39 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8002112259ebd83c9b6e0000000", hexnat% "2000000000020000000000", hexnat% "200000140000000000", hexnat% "2000800400000000000000000"]
  let c40 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "8002110258ebd828996e0000000", hexnat% "2000800400000000000000000", 373833953443840, hexnat% "2200000000022000000000", hexnat% "100000000000000000", hexnat% "200000000000000000"]
  let c41 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨61, by decide⟩ c40 c39
  let c42 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨107, by decide⟩ c41 c38
  let c43 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨71, by decide⟩ c42 c37
  let c44 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨84, by decide⟩ c43 c36
  let c45 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "2000010e9d800914c0000000", hexnat% "800000200100000002000000000", hexnat% "4400002000000000000", hexnat% "3000000000028000000000", hexnat% "a00000140000000000", hexnat% "2010820000000800200000000", 2306194853471453184]
  let c46 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨34, by decide⟩ c45 c44
  let c47 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c46 c35
  let c48 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨72, by decide⟩ c47 c34
  let c49 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨36, by decide⟩ c48 c29
  let c50 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨40, by decide⟩ c49 c26
  let c51 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨63, by decide⟩ c50 c23
  let c52 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨93, by decide⟩ c51 c22
  let c53 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c52 c21
  let c54 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨65, by decide⟩ c53 c20
  let c55 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨56, by decide⟩ c54 c17
  let c56 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨60, by decide⟩ c55 c14
  let c57 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨55, by decide⟩ c56 c8
  let c58 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨43, by decide⟩ c57 c5
  let c59 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨59, by decide⟩ c58 c4
  c59
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record000_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record000_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record000_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record000_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record000_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record000_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record000_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record000_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record000_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00094.record000

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00094.record003
open Papers.RationalityTen PackedGraphCertificate GraphCaseCertificate
abbrev raw := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record003
def vertexColumn : Fields := ⟨10, hexnat% "ad32c3b31c3723c2f2b2ca8eac68da8e8bac9aa6698e6c5a96958d68d8b6c394e33a2e4b8ae1ba1e4789e1783e3a4d92e725694e5c56352d54d334ad1b51d2743dc8da338f138ccb352ccb2ac6b46c9b0ef0761d4731e2749ca719e1745c9715c3743c8f13c2f07f243512c173223492a168d14a45931525294951550d1342d074c348ca324c5342c4b0ac1b"⟩
def kindColumn : Fields := ⟨3, hexnat% "69b4db4da6d36db69b6db4db6d369a49b4924924936924924db4d26da4d3491249249249249249249249"⟩
def data := FacetSat.RawProjection.data raw vertexColumn kindColumn
theorem projection_checked : FacetSat.RawProjection.check raw vertexColumn kindColumn = true :=
  by decide_kernel_context
def selectedKinds : List Nat := [2]
def candidates : List (Fin raw.n) := [⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨74, by decide⟩, ⟨77, by decide⟩, ⟨83, by decide⟩, ⟨90, by decide⟩, ⟨97, by decide⟩, ⟨100, by decide⟩, ⟨103, by decide⟩, ⟨107, by decide⟩, ⟨110, by decide⟩]
def requirements : Nat → Nat := GraphFacetClique.restrictedQuota selectedKinds raw.data.quota
theorem candidates_complete : FacetSat.cliqueCoverageCheck data.kind selectedKinds candidates = true :=
  by decide_kernel_context
def certificate : CliqueExclusion.QuotaCertificate raw.n :=
  let c0 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "204082185dc2e8b1ae0000000", hexnat% "4080000000000000000000000000", 166914661189419008, hexnat% "4a2000000000000000", hexnat% "810000004000000000000000000"]
  let c1 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "408204082406d0368b1ae0000000", hexnat% "1000800000000000000", 452611762550734848, hexnat% "c90000000000000000", hexnat% "810000000002001000000000000"]
  let c2 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "408204082404f0278b1ae0000000", hexnat% "1000800000000000000", 452611762550734848, hexnat% "c90000000000000000", hexnat% "810000000020010000000000000"]
  let c3 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "408204082004d0268b1ae0000000", hexnat% "1000800000000000000", 452611762550734848, hexnat% "c90000000000000000", hexnat% "810000004022011000000000000"]
  let c4 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "48920408240220110b1ae0000000", hexnat% "1000800000000000000", 13088586417045504, hexnat% "5d000000000000000", 450359962737049600, hexnat% "c80000000000000000"]
  let c5 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "cff204091ae0000000", hexnat% "4002000801000000020000000000", 16747761114284032, 306244774661193728, hexnat% "80000000000800000000000000", hexnat% "810040024000000000000000000"]
  let c6 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "81004002443203f881ae0000000", hexnat% "4d000000000000000", 450361062248677376, hexnat% "880000000000000000", hexnat% "2000801000800020000000000", hexnat% "4080000000000000000000000000"]
  let c7 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4cff040891ae0000000", hexnat% "4002000801000000020000000000", 17732923532771328, 432345564227567616, hexnat% "810040020000000000000000000", hexnat% "80000000000800000000000000"]
  let c8 : CliqueExclusion.QuotaCertificate raw.n := .classes 2 [hexnat% "4082000804480000020ae0000000", 17873661021126656, hexnat% "1000800000000000000", hexnat% "7f000000000000000", hexnat% "800400010000000000", hexnat% "810040020000000000000000000", 162138451397836800]
  let c9 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨67, by decide⟩ c8 c7
  let c10 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨74, by decide⟩ c9 c6
  let c11 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨70, by decide⟩ c10 c5
  let c12 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨35, by decide⟩ c11 c4
  let c13 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨33, by decide⟩ c12 c3
  let c14 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨29, by decide⟩ c13 c2
  let c15 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨31, by decide⟩ c14 c1
  let c16 : CliqueExclusion.QuotaCertificate raw.n := .split ⟨30, by decide⟩ c15 c0
  c16
theorem checked : CliqueExclusion.checkQuotas data.relation data.kind
    candidates requirements certificate = true := by decide_kernel_context
theorem local_excluded (valid : GraphGrowthInputs.Valid raw.inputs)
    (matrix : MatrixGraphProblem.Checked raw.data) (B : List (Fin raw.n))
    (H : GraphGrowthConstraints.Target (raw.inputs.problem valid) B) : False :=
  FacetSat.RawProjection.excluded_of_clique raw valid matrix vertexColumn kindColumn
    projection_checked selectedKinds candidates candidates_complete certificate checked B H
theorem direct_core : DirectCore raw where
  matrix := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record003_matrix_checked
  valid := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record003_validity
  literal := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record003_literal
  leaf_nodup := by decide +kernel
  frames := Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record003_frames_supported Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record003_cells_exact
  leaves_checked := ⟨Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record003_certificates, Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record003_leaf_certificates_checked⟩
  complete := fun B H => False.elim (local_excluded Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record003_validity Papers.RationalityTen.CompactReplay.GraphInputsRow29Part00094.record003_matrix_checked B H)
#print axioms local_excluded
end Papers.RationalityTen.StructuralGraphCases.GraphInputsRow29Part00094.record003
