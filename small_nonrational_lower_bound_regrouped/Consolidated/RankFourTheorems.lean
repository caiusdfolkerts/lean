module
public import Consolidated.RankFourCharts00
public import Consolidated.RankFourCharts01
public import Consolidated.RankFourCharts02
public import Consolidated.RankFourCharts03
public import Consolidated.RankFourCharts04
public import Consolidated.RankFourCharts05
public import Consolidated.RankFourCharts06
public import Consolidated.RankFourCharts07
public import Consolidated.RankFourCharts08
public import Consolidated.RankFourCharts09
public import Consolidated.RankFourCharts10
public import Consolidated.RankFourCharts11
public import Consolidated.RankFourCharts12
public import Consolidated.RankFourCharts13
public import Consolidated.RankFourCharts14
public import Consolidated.RankFourCharts15
public import Consolidated.RankFourCharts16
public import Consolidated.RankFourCharts17
public import Consolidated.RankFourCharts18
public import Consolidated.RankFourCharts19
public import Consolidated.RankFourCharts20
public import Consolidated.RankFourCharts21
public import Consolidated.RankFourCharts22
public import Consolidated.RankFourCharts23
public import Consolidated.RankFourCharts24
public import Consolidated.RankFourCharts25
public import Consolidated.SelectedRankGeometry
public import Consolidated.SemanticCatalogue
public import MatroidChecked.ChartRealization
public import MatroidChecked.ExactDensity
public import MatroidChecked.GoldenIdentification
public import MatroidChecked.ZeroRows
public import Papers.RationalityTenVectorBasisFamilies


section BundlePart0
/- Source: MatroidChecked/VectorCoverage.lean -/





@[expose] public section

/-!
# Exhaustive coverage for actual rank-four vector configurations

The conclusion is about the linear-independence pattern of eight vectors
over any field.  It does not assume the input belongs to a supplied list.
Zero vectors are excluded here because the finite catalogue is loopless;
`MatroidChecked.ZeroRows` handles them by duplicate replacement and exact restoration.
-/

noncomputable section
namespace Papers.RationalityTen.MatroidChecked

open Finset Submodule
open BasisFamilies BasisReconstruction VectorBasisFamilies

variable {K : Type*} [Field K]

/-- Every spanning configuration of eight nonzero vectors in `K⁴` has,
after a genuine permutation of its labels, one of the 832 literal basis
families.  The finite extension certificates establish exhaustiveness. -/
theorem vector_configuration_covered
    (p : Fin 8 → Fin 4 → K)
    (hspan : span K (Set.range p) = ⊤)
    (hnz : ∀ i, p i ≠ 0) :
    ∃ i : Fin 832, ∃ σ : Equiv.Perm (Fin 8),
      (vectorBases p).image (fun S => S.image σ) =
        MatroidCatalogue.N8R4.family i.val := by
  obtain ⟨i,σ,hfix,heq⟩ :=
    MatroidCatalogue.catalogue_complete_eight_rank_four_index
      (vectorBasisFamily p hspan hnz)
  exact ⟨i,σ,heq⟩

end Papers.RationalityTen.MatroidChecked

end
end
end BundlePart0

section BundlePart1
/- Source: MatroidChecked/RankFourCatalogueDensity.lean -/







@[expose] public section
noncomputable section

/-!
# Assembly of the exhaustive rank-four result

The finite chart aggregation supplies one theorem per nonexceptional
catalogue index. The universal results here use actual matroid coverage,
restore zero rows, and identify the remaining exception with the exact
matrix in the paper. No catalogue-membership premise is imposed on the
input matrix.
-/

namespace Papers.RationalityTen.MatroidChecked.RankFourCatalogueDensity

open Matrix Set Filter Topology
open VectorBasisFamilies (vectorBases)
open ChartRealization (FamilyRationallyDense)
open Papers.MatrixGaugeNormalization (ZeroRationalRealizations)
open ZeroRows


theorem loopless_density (H : CatalogueDensityProofs) : LooplessNongoldenDensity := by
  intro p hspan hnz hgolden
  obtain ⟨i,σ,hcatalogue⟩ := vector_configuration_covered p hspan hnz
  have hi : i ≠ 563 := by
    intro h
    subst i
    exact hgolden σ hcatalogue
  exact H i hi p σ hcatalogue

/-- The eight-row statement includes zero vectors. Its only exception is
isomorphism to the explicitly identified golden basis family. -/
theorem rank_four_density (H : CatalogueDensityProofs)
    (p : Matrix (Fin 8) (Fin 4) ℝ)
    (hspan : Submodule.span ℝ (Set.range p) = ⊤)
    (hgolden : ¬ HasGoldenMatroid p) :
    p ∈ closure (ZeroRationalRealizations p) := by
  by_cases hnz : ∀ i, p i ≠ 0
  · exact loopless_density H p hspan hnz (fun σ h => hgolden ⟨σ,h⟩)
  · have hz : ∃ i, p i = 0 := by
      by_contra h
      apply hnz
      intro i hi
      exact h ⟨i,hi⟩
    obtain ⟨i,hi⟩ := hz
    exact density_with_zero_row (loopless_density H) p hspan i hi

theorem rank_four_density_below_eight (H : CatalogueDensityProofs)
    {n : ℕ} (p : Matrix (Fin n) (Fin 4) ℝ) (hn : n < 8)
    (hspan : Submodule.span ℝ (Set.range p) = ⊤) :
    p ∈ closure (ZeroRationalRealizations p) :=
  density_fewer_than_eight (loopless_density H) p hn hspan

/-- The exceptional predicate is exactly isomorphism to the paper's
displayed matrix, for either real root of its defining quadratic. -/
theorem hasGoldenMatroid_iff_paper_matrix
    (p : Matrix (Fin 8) (Fin 4) ℝ) (t : ℝ) (ht : t^2 + t - 1 = 0) :
    HasGoldenMatroid p ↔ ∃ σ : Equiv.Perm (Fin 8),
      (vectorBases p).image (fun S => S.image σ) =
        vectorBases (GoldenIdentification.goldenRows t) :=
  GoldenIdentification.golden_isomorphism_iff p t ht

end Papers.RationalityTen.MatroidChecked.RankFourCatalogueDensity

end
end
end BundlePart1

section BundlePart2
/- Source: MatroidChecked/CatalogueDensityAssembly.lean -/





























@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-!
# The complete family of ordinary rank-four density certificates

Each of the831 nonexceptional catalogue types has a universal theorem for
its actual real representations. Exhaustion of all represented matroids is
a separate dependency, used by the unrestricted result in VerifiedRankFour.
-/

namespace Papers.RationalityTen.MatroidChecked.VerifiedRankFour
open RankFourCatalogueDensity

/-- All 831 nonexceptional cases are actual universal density theorems. -/
theorem catalogue_density_proofs : CatalogueDensityProofs := by
  unfold CatalogueDensityProofs
  refine (Fin.forall_fin_add (m := 416) (n := 416) _).2 ⟨?_, ?_⟩
  · refine (Fin.forall_fin_add (m := 208) (n := 208) _).2 ⟨?_, ?_⟩
    · refine (Fin.forall_fin_add (m := 104) (n := 104) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 52) (n := 52) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 26) (n := 26) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 13) (n := 13) _).2 ⟨?_, ?_⟩
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart0.family_rationally_dense
              · exact Papers.RationalityTen.Chart1.family_rationally_dense
              · exact Papers.RationalityTen.Chart2.family_rationally_dense
              · exact Papers.RationalityTen.Chart3.family_rationally_dense
              · exact Papers.RationalityTen.Chart4.family_rationally_dense
              · exact Papers.RationalityTen.Chart5.family_rationally_dense
              · exact Papers.RationalityTen.Chart6.family_rationally_dense
              · exact Papers.RationalityTen.Chart7.family_rationally_dense
              · exact Papers.RationalityTen.Chart8.family_rationally_dense
              · exact Papers.RationalityTen.Chart9.family_rationally_dense
              · exact Papers.RationalityTen.Chart10.family_rationally_dense
              · exact Papers.RationalityTen.Chart11.family_rationally_dense
              · exact Papers.RationalityTen.Chart12.family_rationally_dense
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart13.family_rationally_dense
              · exact Papers.RationalityTen.Chart14.family_rationally_dense
              · exact Papers.RationalityTen.Chart15.family_rationally_dense
              · exact Papers.RationalityTen.Chart16.family_rationally_dense
              · exact Papers.RationalityTen.Chart17.family_rationally_dense
              · exact Papers.RationalityTen.Chart18.family_rationally_dense
              · exact Papers.RationalityTen.Chart19.family_rationally_dense
              · exact Papers.RationalityTen.Chart20.family_rationally_dense
              · exact Papers.RationalityTen.Chart21.family_rationally_dense
              · exact Papers.RationalityTen.Chart22.family_rationally_dense
              · exact Papers.RationalityTen.Chart23.family_rationally_dense
              · exact Papers.RationalityTen.Chart24.family_rationally_dense
              · exact Papers.RationalityTen.Chart25.family_rationally_dense
          · refine (Fin.forall_fin_add (m := 13) (n := 13) _).2 ⟨?_, ?_⟩
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart26.family_rationally_dense
              · exact Papers.RationalityTen.Chart27.family_rationally_dense
              · exact Papers.RationalityTen.Chart28.family_rationally_dense
              · exact Papers.RationalityTen.Chart29.family_rationally_dense
              · exact Papers.RationalityTen.Chart30.family_rationally_dense
              · exact Papers.RationalityTen.Chart31.family_rationally_dense
              · exact Papers.RationalityTen.Chart32.family_rationally_dense
              · exact Papers.RationalityTen.Chart33.family_rationally_dense
              · exact Papers.RationalityTen.Chart34.family_rationally_dense
              · exact Papers.RationalityTen.Chart35.family_rationally_dense
              · exact Papers.RationalityTen.Chart36.family_rationally_dense
              · exact Papers.RationalityTen.Chart37.family_rationally_dense
              · exact Papers.RationalityTen.Chart38.family_rationally_dense
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart39.family_rationally_dense
              · exact Papers.RationalityTen.Chart40.family_rationally_dense
              · exact Papers.RationalityTen.Chart41.family_rationally_dense
              · exact Papers.RationalityTen.Chart42.family_rationally_dense
              · exact Papers.RationalityTen.Chart43.family_rationally_dense
              · exact Papers.RationalityTen.Chart44.family_rationally_dense
              · exact Papers.RationalityTen.Chart45.family_rationally_dense
              · exact Papers.RationalityTen.Chart46.family_rationally_dense
              · exact Papers.RationalityTen.Chart47.family_rationally_dense
              · exact Papers.RationalityTen.Chart48.family_rationally_dense
              · exact Papers.RationalityTen.Chart49.family_rationally_dense
              · exact Papers.RationalityTen.Chart50.family_rationally_dense
              · exact Papers.RationalityTen.Chart51.family_rationally_dense
        · refine (Fin.forall_fin_add (m := 26) (n := 26) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 13) (n := 13) _).2 ⟨?_, ?_⟩
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart52.family_rationally_dense
              · exact Papers.RationalityTen.Chart53.family_rationally_dense
              · exact Papers.RationalityTen.Chart54.family_rationally_dense
              · exact Papers.RationalityTen.Chart55.family_rationally_dense
              · exact Papers.RationalityTen.Chart56.family_rationally_dense
              · exact Papers.RationalityTen.Chart57.family_rationally_dense
              · exact Papers.RationalityTen.Chart58.family_rationally_dense
              · exact Papers.RationalityTen.Chart59.family_rationally_dense
              · exact Papers.RationalityTen.Chart60.family_rationally_dense
              · exact Papers.RationalityTen.Chart61.family_rationally_dense
              · exact Papers.RationalityTen.Chart62.family_rationally_dense
              · exact Papers.RationalityTen.Chart63.family_rationally_dense
              · exact Papers.RationalityTen.Chart64.family_rationally_dense
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart65.family_rationally_dense
              · exact Papers.RationalityTen.Chart66.family_rationally_dense
              · exact Papers.RationalityTen.Chart67.family_rationally_dense
              · exact Papers.RationalityTen.Chart68.family_rationally_dense
              · exact Papers.RationalityTen.Chart69.family_rationally_dense
              · exact Papers.RationalityTen.Chart70.family_rationally_dense
              · exact Papers.RationalityTen.Chart71.family_rationally_dense
              · exact Papers.RationalityTen.Chart72.family_rationally_dense
              · exact Papers.RationalityTen.Chart73.family_rationally_dense
              · exact Papers.RationalityTen.Chart74.family_rationally_dense
              · exact Papers.RationalityTen.Chart75.family_rationally_dense
              · exact Papers.RationalityTen.Chart76.family_rationally_dense
              · exact Papers.RationalityTen.Chart77.family_rationally_dense
          · refine (Fin.forall_fin_add (m := 13) (n := 13) _).2 ⟨?_, ?_⟩
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart78.family_rationally_dense
              · exact Papers.RationalityTen.Chart79.family_rationally_dense
              · exact Papers.RationalityTen.Chart80.family_rationally_dense
              · exact Papers.RationalityTen.Chart81.family_rationally_dense
              · exact Papers.RationalityTen.Chart82.family_rationally_dense
              · exact Papers.RationalityTen.Chart83.family_rationally_dense
              · exact Papers.RationalityTen.Chart84.family_rationally_dense
              · exact Papers.RationalityTen.Chart85.family_rationally_dense
              · exact Papers.RationalityTen.Chart86.family_rationally_dense
              · exact Papers.RationalityTen.Chart87.family_rationally_dense
              · exact Papers.RationalityTen.Chart88.family_rationally_dense
              · exact Papers.RationalityTen.Chart89.family_rationally_dense
              · exact Papers.RationalityTen.Chart90.family_rationally_dense
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart91.family_rationally_dense
              · exact Papers.RationalityTen.Chart92.family_rationally_dense
              · exact Papers.RationalityTen.Chart93.family_rationally_dense
              · exact Papers.RationalityTen.Chart94.family_rationally_dense
              · exact Papers.RationalityTen.Chart95.family_rationally_dense
              · exact Papers.RationalityTen.Chart96.family_rationally_dense
              · exact Papers.RationalityTen.Chart97.family_rationally_dense
              · exact Papers.RationalityTen.Chart98.family_rationally_dense
              · exact Papers.RationalityTen.Chart99.family_rationally_dense
              · exact Papers.RationalityTen.Chart100.family_rationally_dense
              · exact Papers.RationalityTen.Chart101.family_rationally_dense
              · exact Papers.RationalityTen.Chart102.family_rationally_dense
              · exact Papers.RationalityTen.Chart103.family_rationally_dense
      · refine (Fin.forall_fin_add (m := 52) (n := 52) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 26) (n := 26) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 13) (n := 13) _).2 ⟨?_, ?_⟩
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart104.family_rationally_dense
              · exact Papers.RationalityTen.Chart105.family_rationally_dense
              · exact Papers.RationalityTen.Chart106.family_rationally_dense
              · exact Papers.RationalityTen.Chart107.family_rationally_dense
              · exact Papers.RationalityTen.Chart108.family_rationally_dense
              · exact Papers.RationalityTen.Chart109.family_rationally_dense
              · exact Papers.RationalityTen.Chart110.family_rationally_dense
              · exact Papers.RationalityTen.Chart111.family_rationally_dense
              · exact Papers.RationalityTen.Chart112.family_rationally_dense
              · exact Papers.RationalityTen.Chart113.family_rationally_dense
              · exact Papers.RationalityTen.Chart114.family_rationally_dense
              · exact Papers.RationalityTen.Chart115.family_rationally_dense
              · exact Papers.RationalityTen.Chart116.family_rationally_dense
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart117.family_rationally_dense
              · exact Papers.RationalityTen.Chart118.family_rationally_dense
              · exact Papers.RationalityTen.Chart119.family_rationally_dense
              · exact Papers.RationalityTen.Chart120.family_rationally_dense
              · exact Papers.RationalityTen.Chart121.family_rationally_dense
              · exact Papers.RationalityTen.Chart122.family_rationally_dense
              · exact Papers.RationalityTen.Chart123.family_rationally_dense
              · exact Papers.RationalityTen.Chart124.family_rationally_dense
              · exact Papers.RationalityTen.Chart125.family_rationally_dense
              · exact Papers.RationalityTen.Chart126.family_rationally_dense
              · exact Papers.RationalityTen.Chart127.family_rationally_dense
              · exact Papers.RationalityTen.Chart128.family_rationally_dense
              · exact Papers.RationalityTen.Chart129.family_rationally_dense
          · refine (Fin.forall_fin_add (m := 13) (n := 13) _).2 ⟨?_, ?_⟩
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart130.family_rationally_dense
              · exact Papers.RationalityTen.Chart131.family_rationally_dense
              · exact Papers.RationalityTen.Chart132.family_rationally_dense
              · exact Papers.RationalityTen.Chart133.family_rationally_dense
              · exact Papers.RationalityTen.Chart134.family_rationally_dense
              · exact Papers.RationalityTen.Chart135.family_rationally_dense
              · exact Papers.RationalityTen.Chart136.family_rationally_dense
              · exact Papers.RationalityTen.Chart137.family_rationally_dense
              · exact Papers.RationalityTen.Chart138.family_rationally_dense
              · exact Papers.RationalityTen.Chart139.family_rationally_dense
              · exact Papers.RationalityTen.Chart140.family_rationally_dense
              · exact Papers.RationalityTen.Chart141.family_rationally_dense
              · exact Papers.RationalityTen.Chart142.family_rationally_dense
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart143.family_rationally_dense
              · exact Papers.RationalityTen.Chart144.family_rationally_dense
              · exact Papers.RationalityTen.Chart145.family_rationally_dense
              · exact Papers.RationalityTen.Chart146.family_rationally_dense
              · exact Papers.RationalityTen.Chart147.family_rationally_dense
              · exact Papers.RationalityTen.Chart148.family_rationally_dense
              · exact Papers.RationalityTen.Chart149.family_rationally_dense
              · exact Papers.RationalityTen.Chart150.family_rationally_dense
              · exact Papers.RationalityTen.Chart151.family_rationally_dense
              · exact Papers.RationalityTen.Chart152.family_rationally_dense
              · exact Papers.RationalityTen.Chart153.family_rationally_dense
              · exact Papers.RationalityTen.Chart154.family_rationally_dense
              · exact Papers.RationalityTen.Chart155.family_rationally_dense
        · refine (Fin.forall_fin_add (m := 26) (n := 26) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 13) (n := 13) _).2 ⟨?_, ?_⟩
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart156.family_rationally_dense
              · exact Papers.RationalityTen.Chart157.family_rationally_dense
              · exact Papers.RationalityTen.Chart158.family_rationally_dense
              · exact Papers.RationalityTen.Chart159.family_rationally_dense
              · exact Papers.RationalityTen.Chart160.family_rationally_dense
              · exact Papers.RationalityTen.Chart161.family_rationally_dense
              · exact Papers.RationalityTen.Chart162.family_rationally_dense
              · exact Papers.RationalityTen.Chart163.family_rationally_dense
              · exact Papers.RationalityTen.Chart164.family_rationally_dense
              · exact Papers.RationalityTen.Chart165.family_rationally_dense
              · exact Papers.RationalityTen.Chart166.family_rationally_dense
              · exact Papers.RationalityTen.Chart167.family_rationally_dense
              · exact Papers.RationalityTen.Chart168.family_rationally_dense
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart169.family_rationally_dense
              · exact Papers.RationalityTen.Chart170.family_rationally_dense
              · exact Papers.RationalityTen.Chart171.family_rationally_dense
              · exact Papers.RationalityTen.Chart172.family_rationally_dense
              · exact Papers.RationalityTen.Chart173.family_rationally_dense
              · exact Papers.RationalityTen.Chart174.family_rationally_dense
              · exact Papers.RationalityTen.Chart175.family_rationally_dense
              · exact Papers.RationalityTen.Chart176.family_rationally_dense
              · exact Papers.RationalityTen.Chart177.family_rationally_dense
              · exact Papers.RationalityTen.Chart178.family_rationally_dense
              · exact Papers.RationalityTen.Chart179.family_rationally_dense
              · exact Papers.RationalityTen.Chart180.family_rationally_dense
              · exact Papers.RationalityTen.Chart181.family_rationally_dense
          · refine (Fin.forall_fin_add (m := 13) (n := 13) _).2 ⟨?_, ?_⟩
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart182.family_rationally_dense
              · exact Papers.RationalityTen.Chart183.family_rationally_dense
              · exact Papers.RationalityTen.Chart184.family_rationally_dense
              · exact Papers.RationalityTen.Chart185.family_rationally_dense
              · exact Papers.RationalityTen.Chart186.family_rationally_dense
              · exact Papers.RationalityTen.Chart187.family_rationally_dense
              · exact Papers.RationalityTen.Chart188.family_rationally_dense
              · exact Papers.RationalityTen.Chart189.family_rationally_dense
              · exact Papers.RationalityTen.Chart190.family_rationally_dense
              · exact Papers.RationalityTen.Chart191.family_rationally_dense
              · exact Papers.RationalityTen.Chart192.family_rationally_dense
              · exact Papers.RationalityTen.Chart193.family_rationally_dense
              · exact Papers.RationalityTen.Chart194.family_rationally_dense
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart195.family_rationally_dense
              · exact Papers.RationalityTen.Chart196.family_rationally_dense
              · exact Papers.RationalityTen.Chart197.family_rationally_dense
              · exact Papers.RationalityTen.Chart198.family_rationally_dense
              · exact Papers.RationalityTen.Chart199.family_rationally_dense
              · exact Papers.RationalityTen.Chart200.family_rationally_dense
              · exact Papers.RationalityTen.Chart201.family_rationally_dense
              · exact Papers.RationalityTen.Chart202.family_rationally_dense
              · exact Papers.RationalityTen.Chart203.family_rationally_dense
              · exact Papers.RationalityTen.Chart204.family_rationally_dense
              · exact Papers.RationalityTen.Chart205.family_rationally_dense
              · exact Papers.RationalityTen.Chart206.family_rationally_dense
              · exact Papers.RationalityTen.Chart207.family_rationally_dense
    · refine (Fin.forall_fin_add (m := 104) (n := 104) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 52) (n := 52) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 26) (n := 26) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 13) (n := 13) _).2 ⟨?_, ?_⟩
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart208.family_rationally_dense
              · exact Papers.RationalityTen.Chart209.family_rationally_dense
              · exact Papers.RationalityTen.Chart210.family_rationally_dense
              · exact Papers.RationalityTen.Chart211.family_rationally_dense
              · exact Papers.RationalityTen.Chart212.family_rationally_dense
              · exact Papers.RationalityTen.Chart213.family_rationally_dense
              · exact Papers.RationalityTen.Chart214.family_rationally_dense
              · exact Papers.RationalityTen.Chart215.family_rationally_dense
              · exact Papers.RationalityTen.Chart216.family_rationally_dense
              · exact Papers.RationalityTen.Chart217.family_rationally_dense
              · exact Papers.RationalityTen.Chart218.family_rationally_dense
              · exact Papers.RationalityTen.Chart219.family_rationally_dense
              · exact Papers.RationalityTen.Chart220.family_rationally_dense
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart221.family_rationally_dense
              · exact Papers.RationalityTen.Chart222.family_rationally_dense
              · exact Papers.RationalityTen.Chart223.family_rationally_dense
              · exact Papers.RationalityTen.Chart224.family_rationally_dense
              · exact Papers.RationalityTen.Chart225.family_rationally_dense
              · exact Papers.RationalityTen.Chart226.family_rationally_dense
              · exact Papers.RationalityTen.Chart227.family_rationally_dense
              · exact Papers.RationalityTen.Chart228.family_rationally_dense
              · exact Papers.RationalityTen.Chart229.family_rationally_dense
              · exact Papers.RationalityTen.Chart230.family_rationally_dense
              · exact Papers.RationalityTen.Chart231.family_rationally_dense
              · exact Papers.RationalityTen.Chart232.family_rationally_dense
              · exact Papers.RationalityTen.Chart233.family_rationally_dense
          · refine (Fin.forall_fin_add (m := 13) (n := 13) _).2 ⟨?_, ?_⟩
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart234.family_rationally_dense
              · exact Papers.RationalityTen.Chart235.family_rationally_dense
              · exact Papers.RationalityTen.Chart236.family_rationally_dense
              · exact Papers.RationalityTen.Chart237.family_rationally_dense
              · exact Papers.RationalityTen.Chart238.family_rationally_dense
              · exact Papers.RationalityTen.Chart239.family_rationally_dense
              · exact Papers.RationalityTen.Chart240.family_rationally_dense
              · exact Papers.RationalityTen.Chart241.family_rationally_dense
              · exact Papers.RationalityTen.Chart242.family_rationally_dense
              · exact Papers.RationalityTen.Chart243.family_rationally_dense
              · exact Papers.RationalityTen.Chart244.family_rationally_dense
              · exact Papers.RationalityTen.Chart245.family_rationally_dense
              · exact Papers.RationalityTen.Chart246.family_rationally_dense
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart247.family_rationally_dense
              · exact Papers.RationalityTen.Chart248.family_rationally_dense
              · exact Papers.RationalityTen.Chart249.family_rationally_dense
              · exact Papers.RationalityTen.Chart250.family_rationally_dense
              · exact Papers.RationalityTen.Chart251.family_rationally_dense
              · exact Papers.RationalityTen.Chart252.family_rationally_dense
              · exact Papers.RationalityTen.Chart253.family_rationally_dense
              · exact Papers.RationalityTen.Chart254.family_rationally_dense
              · exact Papers.RationalityTen.Chart255.family_rationally_dense
              · exact Papers.RationalityTen.Chart256.family_rationally_dense
              · exact Papers.RationalityTen.Chart257.family_rationally_dense
              · exact Papers.RationalityTen.Chart258.family_rationally_dense
              · exact Papers.RationalityTen.Chart259.family_rationally_dense
        · refine (Fin.forall_fin_add (m := 26) (n := 26) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 13) (n := 13) _).2 ⟨?_, ?_⟩
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart260.family_rationally_dense
              · exact Papers.RationalityTen.Chart261.family_rationally_dense
              · exact Papers.RationalityTen.Chart262.family_rationally_dense
              · exact Papers.RationalityTen.Chart263.family_rationally_dense
              · exact Papers.RationalityTen.Chart264.family_rationally_dense
              · exact Papers.RationalityTen.Chart265.family_rationally_dense
              · exact Papers.RationalityTen.Chart266.family_rationally_dense
              · exact Papers.RationalityTen.Chart267.family_rationally_dense
              · exact Papers.RationalityTen.Chart268.family_rationally_dense
              · exact Papers.RationalityTen.Chart269.family_rationally_dense
              · exact Papers.RationalityTen.Chart270.family_rationally_dense
              · exact Papers.RationalityTen.Chart271.family_rationally_dense
              · exact Papers.RationalityTen.Chart272.family_rationally_dense
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart273.family_rationally_dense
              · exact Papers.RationalityTen.Chart274.family_rationally_dense
              · exact Papers.RationalityTen.Chart275.family_rationally_dense
              · exact Papers.RationalityTen.Chart276.family_rationally_dense
              · exact Papers.RationalityTen.Chart277.family_rationally_dense
              · exact Papers.RationalityTen.Chart278.family_rationally_dense
              · exact Papers.RationalityTen.Chart279.family_rationally_dense
              · exact Papers.RationalityTen.Chart280.family_rationally_dense
              · exact Papers.RationalityTen.Chart281.family_rationally_dense
              · exact Papers.RationalityTen.Chart282.family_rationally_dense
              · exact Papers.RationalityTen.Chart283.family_rationally_dense
              · exact Papers.RationalityTen.Chart284.family_rationally_dense
              · exact Papers.RationalityTen.Chart285.family_rationally_dense
          · refine (Fin.forall_fin_add (m := 13) (n := 13) _).2 ⟨?_, ?_⟩
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart286.family_rationally_dense
              · exact Papers.RationalityTen.Chart287.family_rationally_dense
              · exact Papers.RationalityTen.Chart288.family_rationally_dense
              · exact Papers.RationalityTen.Chart289.family_rationally_dense
              · exact Papers.RationalityTen.Chart290.family_rationally_dense
              · exact Papers.RationalityTen.Chart291.family_rationally_dense
              · exact Papers.RationalityTen.Chart292.family_rationally_dense
              · exact Papers.RationalityTen.Chart293.family_rationally_dense
              · exact Papers.RationalityTen.Chart294.family_rationally_dense
              · exact Papers.RationalityTen.Chart295.family_rationally_dense
              · exact Papers.RationalityTen.Chart296.family_rationally_dense
              · exact Papers.RationalityTen.Chart297.family_rationally_dense
              · exact Papers.RationalityTen.Chart298.family_rationally_dense
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart299.family_rationally_dense
              · exact Papers.RationalityTen.Chart300.family_rationally_dense
              · exact Papers.RationalityTen.Chart301.family_rationally_dense
              · exact Papers.RationalityTen.Chart302.family_rationally_dense
              · exact Papers.RationalityTen.Chart303.family_rationally_dense
              · exact Papers.RationalityTen.Chart304.family_rationally_dense
              · exact Papers.RationalityTen.Chart305.family_rationally_dense
              · exact Papers.RationalityTen.Chart306.family_rationally_dense
              · exact Papers.RationalityTen.Chart307.family_rationally_dense
              · exact Papers.RationalityTen.Chart308.family_rationally_dense
              · exact Papers.RationalityTen.Chart309.family_rationally_dense
              · exact Papers.RationalityTen.Chart310.family_rationally_dense
              · exact Papers.RationalityTen.Chart311.family_rationally_dense
      · refine (Fin.forall_fin_add (m := 52) (n := 52) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 26) (n := 26) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 13) (n := 13) _).2 ⟨?_, ?_⟩
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart312.family_rationally_dense
              · exact Papers.RationalityTen.Chart313.family_rationally_dense
              · exact Papers.RationalityTen.Chart314.family_rationally_dense
              · exact Papers.RationalityTen.Chart315.family_rationally_dense
              · exact Papers.RationalityTen.Chart316.family_rationally_dense
              · exact Papers.RationalityTen.Chart317.family_rationally_dense
              · exact Papers.RationalityTen.Chart318.family_rationally_dense
              · exact Papers.RationalityTen.Chart319.family_rationally_dense
              · exact Papers.RationalityTen.Chart320.family_rationally_dense
              · exact Papers.RationalityTen.Chart321.family_rationally_dense
              · exact Papers.RationalityTen.Chart322.family_rationally_dense
              · exact Papers.RationalityTen.Chart323.family_rationally_dense
              · exact Papers.RationalityTen.Chart324.family_rationally_dense
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart325.family_rationally_dense
              · exact Papers.RationalityTen.Chart326.family_rationally_dense
              · exact Papers.RationalityTen.Chart327.family_rationally_dense
              · exact Papers.RationalityTen.Chart328.family_rationally_dense
              · exact Papers.RationalityTen.Chart329.family_rationally_dense
              · exact Papers.RationalityTen.Chart330.family_rationally_dense
              · exact Papers.RationalityTen.Chart331.family_rationally_dense
              · exact Papers.RationalityTen.Chart332.family_rationally_dense
              · exact Papers.RationalityTen.Chart333.family_rationally_dense
              · exact Papers.RationalityTen.Chart334.family_rationally_dense
              · exact Papers.RationalityTen.Chart335.family_rationally_dense
              · exact Papers.RationalityTen.Chart336.family_rationally_dense
              · exact Papers.RationalityTen.Chart337.family_rationally_dense
          · refine (Fin.forall_fin_add (m := 13) (n := 13) _).2 ⟨?_, ?_⟩
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart338.family_rationally_dense
              · exact Papers.RationalityTen.Chart339.family_rationally_dense
              · exact Papers.RationalityTen.Chart340.family_rationally_dense
              · exact Papers.RationalityTen.Chart341.family_rationally_dense
              · exact Papers.RationalityTen.Chart342.family_rationally_dense
              · exact Papers.RationalityTen.Chart343.family_rationally_dense
              · exact Papers.RationalityTen.Chart344.family_rationally_dense
              · exact Papers.RationalityTen.Chart345.family_rationally_dense
              · exact Papers.RationalityTen.Chart346.family_rationally_dense
              · exact Papers.RationalityTen.Chart347.family_rationally_dense
              · exact Papers.RationalityTen.Chart348.family_rationally_dense
              · exact Papers.RationalityTen.Chart349.family_rationally_dense
              · exact Papers.RationalityTen.Chart350.family_rationally_dense
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart351.family_rationally_dense
              · exact Papers.RationalityTen.Chart352.family_rationally_dense
              · exact Papers.RationalityTen.Chart353.family_rationally_dense
              · exact Papers.RationalityTen.Chart354.family_rationally_dense
              · exact Papers.RationalityTen.Chart355.family_rationally_dense
              · exact Papers.RationalityTen.Chart356.family_rationally_dense
              · exact Papers.RationalityTen.Chart357.family_rationally_dense
              · exact Papers.RationalityTen.Chart358.family_rationally_dense
              · exact Papers.RationalityTen.Chart359.family_rationally_dense
              · exact Papers.RationalityTen.Chart360.family_rationally_dense
              · exact Papers.RationalityTen.Chart361.family_rationally_dense
              · exact Papers.RationalityTen.Chart362.family_rationally_dense
              · exact Papers.RationalityTen.Chart363.family_rationally_dense
        · refine (Fin.forall_fin_add (m := 26) (n := 26) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 13) (n := 13) _).2 ⟨?_, ?_⟩
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart364.family_rationally_dense
              · exact Papers.RationalityTen.Chart365.family_rationally_dense
              · exact Papers.RationalityTen.Chart366.family_rationally_dense
              · exact Papers.RationalityTen.Chart367.family_rationally_dense
              · exact Papers.RationalityTen.Chart368.family_rationally_dense
              · exact Papers.RationalityTen.Chart369.family_rationally_dense
              · exact Papers.RationalityTen.Chart370.family_rationally_dense
              · exact Papers.RationalityTen.Chart371.family_rationally_dense
              · exact Papers.RationalityTen.Chart372.family_rationally_dense
              · exact Papers.RationalityTen.Chart373.family_rationally_dense
              · exact Papers.RationalityTen.Chart374.family_rationally_dense
              · exact Papers.RationalityTen.Chart375.family_rationally_dense
              · exact Papers.RationalityTen.Chart376.family_rationally_dense
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart377.family_rationally_dense
              · exact Papers.RationalityTen.Chart378.family_rationally_dense
              · exact Papers.RationalityTen.Chart379.family_rationally_dense
              · exact Papers.RationalityTen.Chart380.family_rationally_dense
              · exact Papers.RationalityTen.Chart381.family_rationally_dense
              · exact Papers.RationalityTen.Chart382.family_rationally_dense
              · exact Papers.RationalityTen.Chart383.family_rationally_dense
              · exact Papers.RationalityTen.Chart384.family_rationally_dense
              · exact Papers.RationalityTen.Chart385.family_rationally_dense
              · exact Papers.RationalityTen.Chart386.family_rationally_dense
              · exact Papers.RationalityTen.Chart387.family_rationally_dense
              · exact Papers.RationalityTen.Chart388.family_rationally_dense
              · exact Papers.RationalityTen.Chart389.family_rationally_dense
          · refine (Fin.forall_fin_add (m := 13) (n := 13) _).2 ⟨?_, ?_⟩
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart390.family_rationally_dense
              · exact Papers.RationalityTen.Chart391.family_rationally_dense
              · exact Papers.RationalityTen.Chart392.family_rationally_dense
              · exact Papers.RationalityTen.Chart393.family_rationally_dense
              · exact Papers.RationalityTen.Chart394.family_rationally_dense
              · exact Papers.RationalityTen.Chart395.family_rationally_dense
              · exact Papers.RationalityTen.Chart396.family_rationally_dense
              · exact Papers.RationalityTen.Chart397.family_rationally_dense
              · exact Papers.RationalityTen.Chart398.family_rationally_dense
              · exact Papers.RationalityTen.Chart399.family_rationally_dense
              · exact Papers.RationalityTen.Chart400.family_rationally_dense
              · exact Papers.RationalityTen.Chart401.family_rationally_dense
              · exact Papers.RationalityTen.Chart402.family_rationally_dense
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart403.family_rationally_dense
              · exact Papers.RationalityTen.Chart404.family_rationally_dense
              · exact Papers.RationalityTen.Chart405.family_rationally_dense
              · exact Papers.RationalityTen.Chart406.family_rationally_dense
              · exact Papers.RationalityTen.Chart407.family_rationally_dense
              · exact Papers.RationalityTen.Chart408.family_rationally_dense
              · exact Papers.RationalityTen.Chart409.family_rationally_dense
              · exact Papers.RationalityTen.Chart410.family_rationally_dense
              · exact Papers.RationalityTen.Chart411.family_rationally_dense
              · exact Papers.RationalityTen.Chart412.family_rationally_dense
              · exact Papers.RationalityTen.Chart413.family_rationally_dense
              · exact Papers.RationalityTen.Chart414.family_rationally_dense
              · exact Papers.RationalityTen.Chart415.family_rationally_dense
  · refine (Fin.forall_fin_add (m := 208) (n := 208) _).2 ⟨?_, ?_⟩
    · refine (Fin.forall_fin_add (m := 104) (n := 104) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 52) (n := 52) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 26) (n := 26) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 13) (n := 13) _).2 ⟨?_, ?_⟩
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart416.family_rationally_dense
              · exact Papers.RationalityTen.Chart417.family_rationally_dense
              · exact Papers.RationalityTen.Chart418.family_rationally_dense
              · exact Papers.RationalityTen.Chart419.family_rationally_dense
              · exact Papers.RationalityTen.Chart420.family_rationally_dense
              · exact Papers.RationalityTen.Chart421.family_rationally_dense
              · exact Papers.RationalityTen.Chart422.family_rationally_dense
              · exact Papers.RationalityTen.Chart423.family_rationally_dense
              · exact Papers.RationalityTen.Chart424.family_rationally_dense
              · exact Papers.RationalityTen.Chart425.family_rationally_dense
              · exact Papers.RationalityTen.Chart426.family_rationally_dense
              · exact Papers.RationalityTen.Chart427.family_rationally_dense
              · exact Papers.RationalityTen.Chart428.family_rationally_dense
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart429.family_rationally_dense
              · exact Papers.RationalityTen.Chart430.family_rationally_dense
              · exact Papers.RationalityTen.Chart431.family_rationally_dense
              · exact Papers.RationalityTen.Chart432.family_rationally_dense
              · exact Papers.RationalityTen.Chart433.family_rationally_dense
              · exact Papers.RationalityTen.Chart434.family_rationally_dense
              · exact Papers.RationalityTen.Chart435.family_rationally_dense
              · exact Papers.RationalityTen.Chart436.family_rationally_dense
              · exact Papers.RationalityTen.Chart437.family_rationally_dense
              · exact Papers.RationalityTen.Chart438.family_rationally_dense
              · exact Papers.RationalityTen.Chart439.family_rationally_dense
              · exact Papers.RationalityTen.Chart440.family_rationally_dense
              · exact Papers.RationalityTen.Chart441.family_rationally_dense
          · refine (Fin.forall_fin_add (m := 13) (n := 13) _).2 ⟨?_, ?_⟩
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart442.family_rationally_dense
              · exact Papers.RationalityTen.Chart443.family_rationally_dense
              · exact Papers.RationalityTen.Chart444.family_rationally_dense
              · exact Papers.RationalityTen.Chart445.family_rationally_dense
              · exact Papers.RationalityTen.Chart446.family_rationally_dense
              · exact Papers.RationalityTen.Chart447.family_rationally_dense
              · exact Papers.RationalityTen.Chart448.family_rationally_dense
              · exact Papers.RationalityTen.Chart449.family_rationally_dense
              · exact Papers.RationalityTen.Chart450.family_rationally_dense
              · exact Papers.RationalityTen.Chart451.family_rationally_dense
              · exact Papers.RationalityTen.Chart452.family_rationally_dense
              · exact Papers.RationalityTen.Chart453.family_rationally_dense
              · exact Papers.RationalityTen.Chart454.family_rationally_dense
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart455.family_rationally_dense
              · exact Papers.RationalityTen.Chart456.family_rationally_dense
              · exact Papers.RationalityTen.Chart457.family_rationally_dense
              · exact Papers.RationalityTen.Chart458.family_rationally_dense
              · exact Papers.RationalityTen.Chart459.family_rationally_dense
              · exact Papers.RationalityTen.Chart460.family_rationally_dense
              · exact Papers.RationalityTen.Chart461.family_rationally_dense
              · exact Papers.RationalityTen.Chart462.family_rationally_dense
              · exact Papers.RationalityTen.Chart463.family_rationally_dense
              · exact Papers.RationalityTen.Chart464.family_rationally_dense
              · exact Papers.RationalityTen.Chart465.family_rationally_dense
              · exact Papers.RationalityTen.Chart466.family_rationally_dense
              · exact Papers.RationalityTen.Chart467.family_rationally_dense
        · refine (Fin.forall_fin_add (m := 26) (n := 26) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 13) (n := 13) _).2 ⟨?_, ?_⟩
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart468.family_rationally_dense
              · exact Papers.RationalityTen.Chart469.family_rationally_dense
              · exact Papers.RationalityTen.Chart470.family_rationally_dense
              · exact Papers.RationalityTen.Chart471.family_rationally_dense
              · exact Papers.RationalityTen.Chart472.family_rationally_dense
              · exact Papers.RationalityTen.Chart473.family_rationally_dense
              · exact Papers.RationalityTen.Chart474.family_rationally_dense
              · exact Papers.RationalityTen.Chart475.family_rationally_dense
              · exact Papers.RationalityTen.Chart476.family_rationally_dense
              · exact Papers.RationalityTen.Chart477.family_rationally_dense
              · exact Papers.RationalityTen.Chart478.family_rationally_dense
              · exact Papers.RationalityTen.Chart479.family_rationally_dense
              · exact Papers.RationalityTen.Chart480.family_rationally_dense
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart481.family_rationally_dense
              · exact Papers.RationalityTen.Chart482.family_rationally_dense
              · exact Papers.RationalityTen.Chart483.family_rationally_dense
              · exact Papers.RationalityTen.Chart484.family_rationally_dense
              · exact Papers.RationalityTen.Chart485.family_rationally_dense
              · exact Papers.RationalityTen.Chart486.family_rationally_dense
              · exact Papers.RationalityTen.Chart487.family_rationally_dense
              · exact Papers.RationalityTen.Chart488.family_rationally_dense
              · exact Papers.RationalityTen.Chart489.family_rationally_dense
              · exact Papers.RationalityTen.Chart490.family_rationally_dense
              · exact Papers.RationalityTen.Chart491.family_rationally_dense
              · exact Papers.RationalityTen.Chart492.family_rationally_dense
              · exact Papers.RationalityTen.Chart493.family_rationally_dense
          · refine (Fin.forall_fin_add (m := 13) (n := 13) _).2 ⟨?_, ?_⟩
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart494.family_rationally_dense
              · exact Papers.RationalityTen.Chart495.family_rationally_dense
              · exact Papers.RationalityTen.Chart496.family_rationally_dense
              · exact Papers.RationalityTen.Chart497.family_rationally_dense
              · exact Papers.RationalityTen.Chart498.family_rationally_dense
              · exact Papers.RationalityTen.Chart499.family_rationally_dense
              · exact Papers.RationalityTen.Chart500.family_rationally_dense
              · exact Papers.RationalityTen.Chart501.family_rationally_dense
              · exact Papers.RationalityTen.Chart502.family_rationally_dense
              · exact Papers.RationalityTen.Chart503.family_rationally_dense
              · exact Papers.RationalityTen.Chart504.family_rationally_dense
              · exact Papers.RationalityTen.Chart505.family_rationally_dense
              · exact Papers.RationalityTen.Chart506.family_rationally_dense
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart507.family_rationally_dense
              · exact Papers.RationalityTen.Chart508.family_rationally_dense
              · exact Papers.RationalityTen.Chart509.family_rationally_dense
              · exact Papers.RationalityTen.Chart510.family_rationally_dense
              · exact Papers.RationalityTen.Chart511.family_rationally_dense
              · exact Papers.RationalityTen.Chart512.family_rationally_dense
              · exact Papers.RationalityTen.Chart513.family_rationally_dense
              · exact Papers.RationalityTen.Chart514.family_rationally_dense
              · exact Papers.RationalityTen.Chart515.family_rationally_dense
              · exact Papers.RationalityTen.Chart516.family_rationally_dense
              · exact Papers.RationalityTen.Chart517.family_rationally_dense
              · exact Papers.RationalityTen.Chart518.family_rationally_dense
              · exact Papers.RationalityTen.Chart519.family_rationally_dense
      · refine (Fin.forall_fin_add (m := 52) (n := 52) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 26) (n := 26) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 13) (n := 13) _).2 ⟨?_, ?_⟩
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart520.family_rationally_dense
              · exact Papers.RationalityTen.Chart521.family_rationally_dense
              · exact Papers.RationalityTen.Chart522.family_rationally_dense
              · exact Papers.RationalityTen.Chart523.family_rationally_dense
              · exact Papers.RationalityTen.Chart524.family_rationally_dense
              · exact Papers.RationalityTen.Chart525.family_rationally_dense
              · exact Papers.RationalityTen.Chart526.family_rationally_dense
              · exact Papers.RationalityTen.Chart527.family_rationally_dense
              · exact Papers.RationalityTen.Chart528.family_rationally_dense
              · exact Papers.RationalityTen.Chart529.family_rationally_dense
              · exact Papers.RationalityTen.Chart530.family_rationally_dense
              · exact Papers.RationalityTen.Chart531.family_rationally_dense
              · exact Papers.RationalityTen.Chart532.family_rationally_dense
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart533.family_rationally_dense
              · exact Papers.RationalityTen.Chart534.family_rationally_dense
              · exact Papers.RationalityTen.Chart535.family_rationally_dense
              · exact Papers.RationalityTen.Chart536.family_rationally_dense
              · exact Papers.RationalityTen.Chart537.family_rationally_dense
              · exact Papers.RationalityTen.Chart538.family_rationally_dense
              · exact Papers.RationalityTen.Chart539.family_rationally_dense
              · exact Papers.RationalityTen.Chart540.family_rationally_dense
              · exact Papers.RationalityTen.Chart541.family_rationally_dense
              · exact Papers.RationalityTen.Chart542.family_rationally_dense
              · exact Papers.RationalityTen.Chart543.family_rationally_dense
              · exact Papers.RationalityTen.Chart544.family_rationally_dense
              · exact Papers.RationalityTen.Chart545.family_rationally_dense
          · refine (Fin.forall_fin_add (m := 13) (n := 13) _).2 ⟨?_, ?_⟩
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart546.family_rationally_dense
              · exact Papers.RationalityTen.Chart547.family_rationally_dense
              · exact Papers.RationalityTen.Chart548.family_rationally_dense
              · exact Papers.RationalityTen.Chart549.family_rationally_dense
              · exact Papers.RationalityTen.Chart550.family_rationally_dense
              · exact Papers.RationalityTen.Chart551.family_rationally_dense
              · exact Papers.RationalityTen.Chart552.family_rationally_dense
              · exact Papers.RationalityTen.Chart553.family_rationally_dense
              · exact Papers.RationalityTen.Chart554.family_rationally_dense
              · exact Papers.RationalityTen.Chart555.family_rationally_dense
              · exact Papers.RationalityTen.Chart556.family_rationally_dense
              · exact Papers.RationalityTen.Chart557.family_rationally_dense
              · exact Papers.RationalityTen.Chart558.family_rationally_dense
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart559.family_rationally_dense
              · exact Papers.RationalityTen.Chart560.family_rationally_dense
              · exact Papers.RationalityTen.Chart561.family_rationally_dense
              · exact Papers.RationalityTen.Chart562.family_rationally_dense
              · exact (hi rfl).elim
              · exact Papers.RationalityTen.Chart564.family_rationally_dense
              · exact Papers.RationalityTen.Chart565.family_rationally_dense
              · exact Papers.RationalityTen.Chart566.family_rationally_dense
              · exact Papers.RationalityTen.Chart567.family_rationally_dense
              · exact Papers.RationalityTen.Chart568.family_rationally_dense
              · exact Papers.RationalityTen.Chart569.family_rationally_dense
              · exact Papers.RationalityTen.Chart570.family_rationally_dense
              · exact Papers.RationalityTen.Chart571.family_rationally_dense
        · refine (Fin.forall_fin_add (m := 26) (n := 26) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 13) (n := 13) _).2 ⟨?_, ?_⟩
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart572.family_rationally_dense
              · exact Papers.RationalityTen.Chart573.family_rationally_dense
              · exact Papers.RationalityTen.Chart574.family_rationally_dense
              · exact Papers.RationalityTen.Chart575.family_rationally_dense
              · exact Papers.RationalityTen.Chart576.family_rationally_dense
              · exact Papers.RationalityTen.Chart577.family_rationally_dense
              · exact Papers.RationalityTen.Chart578.family_rationally_dense
              · exact Papers.RationalityTen.Chart579.family_rationally_dense
              · exact Papers.RationalityTen.Chart580.family_rationally_dense
              · exact Papers.RationalityTen.Chart581.family_rationally_dense
              · exact Papers.RationalityTen.Chart582.family_rationally_dense
              · exact Papers.RationalityTen.Chart583.family_rationally_dense
              · exact Papers.RationalityTen.Chart584.family_rationally_dense
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart585.family_rationally_dense
              · exact Papers.RationalityTen.Chart586.family_rationally_dense
              · exact Papers.RationalityTen.Chart587.family_rationally_dense
              · exact Papers.RationalityTen.Chart588.family_rationally_dense
              · exact Papers.RationalityTen.Chart589.family_rationally_dense
              · exact Papers.RationalityTen.Chart590.family_rationally_dense
              · exact Papers.RationalityTen.Chart591.family_rationally_dense
              · exact Papers.RationalityTen.Chart592.family_rationally_dense
              · exact Papers.RationalityTen.Chart593.family_rationally_dense
              · exact Papers.RationalityTen.Chart594.family_rationally_dense
              · exact Papers.RationalityTen.Chart595.family_rationally_dense
              · exact Papers.RationalityTen.Chart596.family_rationally_dense
              · exact Papers.RationalityTen.Chart597.family_rationally_dense
          · refine (Fin.forall_fin_add (m := 13) (n := 13) _).2 ⟨?_, ?_⟩
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart598.family_rationally_dense
              · exact Papers.RationalityTen.Chart599.family_rationally_dense
              · exact Papers.RationalityTen.Chart600.family_rationally_dense
              · exact Papers.RationalityTen.Chart601.family_rationally_dense
              · exact Papers.RationalityTen.Chart602.family_rationally_dense
              · exact Papers.RationalityTen.Chart603.family_rationally_dense
              · exact Papers.RationalityTen.Chart604.family_rationally_dense
              · exact Papers.RationalityTen.Chart605.family_rationally_dense
              · exact Papers.RationalityTen.Chart606.family_rationally_dense
              · exact Papers.RationalityTen.Chart607.family_rationally_dense
              · exact Papers.RationalityTen.Chart608.family_rationally_dense
              · exact Papers.RationalityTen.Chart609.family_rationally_dense
              · exact Papers.RationalityTen.Chart610.family_rationally_dense
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart611.family_rationally_dense
              · exact Papers.RationalityTen.Chart612.family_rationally_dense
              · exact Papers.RationalityTen.Chart613.family_rationally_dense
              · exact Papers.RationalityTen.Chart614.family_rationally_dense
              · exact Papers.RationalityTen.Chart615.family_rationally_dense
              · exact Papers.RationalityTen.Chart616.family_rationally_dense
              · exact Papers.RationalityTen.Chart617.family_rationally_dense
              · exact Papers.RationalityTen.Chart618.family_rationally_dense
              · exact Papers.RationalityTen.Chart619.family_rationally_dense
              · exact Papers.RationalityTen.Chart620.family_rationally_dense
              · exact Papers.RationalityTen.Chart621.family_rationally_dense
              · exact Papers.RationalityTen.Chart622.family_rationally_dense
              · exact Papers.RationalityTen.Chart623.family_rationally_dense
    · refine (Fin.forall_fin_add (m := 104) (n := 104) _).2 ⟨?_, ?_⟩
      · refine (Fin.forall_fin_add (m := 52) (n := 52) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 26) (n := 26) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 13) (n := 13) _).2 ⟨?_, ?_⟩
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart624.family_rationally_dense
              · exact Papers.RationalityTen.Chart625.family_rationally_dense
              · exact Papers.RationalityTen.Chart626.family_rationally_dense
              · exact Papers.RationalityTen.Chart627.family_rationally_dense
              · exact Papers.RationalityTen.Chart628.family_rationally_dense
              · exact Papers.RationalityTen.Chart629.family_rationally_dense
              · exact Papers.RationalityTen.Chart630.family_rationally_dense
              · exact Papers.RationalityTen.Chart631.family_rationally_dense
              · exact Papers.RationalityTen.Chart632.family_rationally_dense
              · exact Papers.RationalityTen.Chart633.family_rationally_dense
              · exact Papers.RationalityTen.Chart634.family_rationally_dense
              · exact Papers.RationalityTen.Chart635.family_rationally_dense
              · exact Papers.RationalityTen.Chart636.family_rationally_dense
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart637.family_rationally_dense
              · exact Papers.RationalityTen.Chart638.family_rationally_dense
              · exact Papers.RationalityTen.Chart639.family_rationally_dense
              · exact Papers.RationalityTen.Chart640.family_rationally_dense
              · exact Papers.RationalityTen.Chart641.family_rationally_dense
              · exact Papers.RationalityTen.Chart642.family_rationally_dense
              · exact Papers.RationalityTen.Chart643.family_rationally_dense
              · exact Papers.RationalityTen.Chart644.family_rationally_dense
              · exact Papers.RationalityTen.Chart645.family_rationally_dense
              · exact Papers.RationalityTen.Chart646.family_rationally_dense
              · exact Papers.RationalityTen.Chart647.family_rationally_dense
              · exact Papers.RationalityTen.Chart648.family_rationally_dense
              · exact Papers.RationalityTen.Chart649.family_rationally_dense
          · refine (Fin.forall_fin_add (m := 13) (n := 13) _).2 ⟨?_, ?_⟩
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart650.family_rationally_dense
              · exact Papers.RationalityTen.Chart651.family_rationally_dense
              · exact Papers.RationalityTen.Chart652.family_rationally_dense
              · exact Papers.RationalityTen.Chart653.family_rationally_dense
              · exact Papers.RationalityTen.Chart654.family_rationally_dense
              · exact Papers.RationalityTen.Chart655.family_rationally_dense
              · exact Papers.RationalityTen.Chart656.family_rationally_dense
              · exact Papers.RationalityTen.Chart657.family_rationally_dense
              · exact Papers.RationalityTen.Chart658.family_rationally_dense
              · exact Papers.RationalityTen.Chart659.family_rationally_dense
              · exact Papers.RationalityTen.Chart660.family_rationally_dense
              · exact Papers.RationalityTen.Chart661.family_rationally_dense
              · exact Papers.RationalityTen.Chart662.family_rationally_dense
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart663.family_rationally_dense
              · exact Papers.RationalityTen.Chart664.family_rationally_dense
              · exact Papers.RationalityTen.Chart665.family_rationally_dense
              · exact Papers.RationalityTen.Chart666.family_rationally_dense
              · exact Papers.RationalityTen.Chart667.family_rationally_dense
              · exact Papers.RationalityTen.Chart668.family_rationally_dense
              · exact Papers.RationalityTen.Chart669.family_rationally_dense
              · exact Papers.RationalityTen.Chart670.family_rationally_dense
              · exact Papers.RationalityTen.Chart671.family_rationally_dense
              · exact Papers.RationalityTen.Chart672.family_rationally_dense
              · exact Papers.RationalityTen.Chart673.family_rationally_dense
              · exact Papers.RationalityTen.Chart674.family_rationally_dense
              · exact Papers.RationalityTen.Chart675.family_rationally_dense
        · refine (Fin.forall_fin_add (m := 26) (n := 26) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 13) (n := 13) _).2 ⟨?_, ?_⟩
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart676.family_rationally_dense
              · exact Papers.RationalityTen.Chart677.family_rationally_dense
              · exact Papers.RationalityTen.Chart678.family_rationally_dense
              · exact Papers.RationalityTen.Chart679.family_rationally_dense
              · exact Papers.RationalityTen.Chart680.family_rationally_dense
              · exact Papers.RationalityTen.Chart681.family_rationally_dense
              · exact Papers.RationalityTen.Chart682.family_rationally_dense
              · exact Papers.RationalityTen.Chart683.family_rationally_dense
              · exact Papers.RationalityTen.Chart684.family_rationally_dense
              · exact Papers.RationalityTen.Chart685.family_rationally_dense
              · exact Papers.RationalityTen.Chart686.family_rationally_dense
              · exact Papers.RationalityTen.Chart687.family_rationally_dense
              · exact Papers.RationalityTen.Chart688.family_rationally_dense
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart689.family_rationally_dense
              · exact Papers.RationalityTen.Chart690.family_rationally_dense
              · exact Papers.RationalityTen.Chart691.family_rationally_dense
              · exact Papers.RationalityTen.Chart692.family_rationally_dense
              · exact Papers.RationalityTen.Chart693.family_rationally_dense
              · exact Papers.RationalityTen.Chart694.family_rationally_dense
              · exact Papers.RationalityTen.Chart695.family_rationally_dense
              · exact Papers.RationalityTen.Chart696.family_rationally_dense
              · exact Papers.RationalityTen.Chart697.family_rationally_dense
              · exact Papers.RationalityTen.Chart698.family_rationally_dense
              · exact Papers.RationalityTen.Chart699.family_rationally_dense
              · exact Papers.RationalityTen.Chart700.family_rationally_dense
              · exact Papers.RationalityTen.Chart701.family_rationally_dense
          · refine (Fin.forall_fin_add (m := 13) (n := 13) _).2 ⟨?_, ?_⟩
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart702.family_rationally_dense
              · exact Papers.RationalityTen.Chart703.family_rationally_dense
              · exact Papers.RationalityTen.Chart704.family_rationally_dense
              · exact Papers.RationalityTen.Chart705.family_rationally_dense
              · exact Papers.RationalityTen.Chart706.family_rationally_dense
              · exact Papers.RationalityTen.Chart707.family_rationally_dense
              · exact Papers.RationalityTen.Chart708.family_rationally_dense
              · exact Papers.RationalityTen.Chart709.family_rationally_dense
              · exact Papers.RationalityTen.Chart710.family_rationally_dense
              · exact Papers.RationalityTen.Chart711.family_rationally_dense
              · exact Papers.RationalityTen.Chart712.family_rationally_dense
              · exact Papers.RationalityTen.Chart713.family_rationally_dense
              · exact Papers.RationalityTen.Chart714.family_rationally_dense
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart715.family_rationally_dense
              · exact Papers.RationalityTen.Chart716.family_rationally_dense
              · exact Papers.RationalityTen.Chart717.family_rationally_dense
              · exact Papers.RationalityTen.Chart718.family_rationally_dense
              · exact Papers.RationalityTen.Chart719.family_rationally_dense
              · exact Papers.RationalityTen.Chart720.family_rationally_dense
              · exact Papers.RationalityTen.Chart721.family_rationally_dense
              · exact Papers.RationalityTen.Chart722.family_rationally_dense
              · exact Papers.RationalityTen.Chart723.family_rationally_dense
              · exact Papers.RationalityTen.Chart724.family_rationally_dense
              · exact Papers.RationalityTen.Chart725.family_rationally_dense
              · exact Papers.RationalityTen.Chart726.family_rationally_dense
              · exact Papers.RationalityTen.Chart727.family_rationally_dense
      · refine (Fin.forall_fin_add (m := 52) (n := 52) _).2 ⟨?_, ?_⟩
        · refine (Fin.forall_fin_add (m := 26) (n := 26) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 13) (n := 13) _).2 ⟨?_, ?_⟩
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart728.family_rationally_dense
              · exact Papers.RationalityTen.Chart729.family_rationally_dense
              · exact Papers.RationalityTen.Chart730.family_rationally_dense
              · exact Papers.RationalityTen.Chart731.family_rationally_dense
              · exact Papers.RationalityTen.Chart732.family_rationally_dense
              · exact Papers.RationalityTen.Chart733.family_rationally_dense
              · exact Papers.RationalityTen.Chart734.family_rationally_dense
              · exact Papers.RationalityTen.Chart735.family_rationally_dense
              · exact Papers.RationalityTen.Chart736.family_rationally_dense
              · exact Papers.RationalityTen.Chart737.family_rationally_dense
              · exact Papers.RationalityTen.Chart738.family_rationally_dense
              · exact Papers.RationalityTen.Chart739.family_rationally_dense
              · exact Papers.RationalityTen.Chart740.family_rationally_dense
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart741.family_rationally_dense
              · exact Papers.RationalityTen.Chart742.family_rationally_dense
              · exact Papers.RationalityTen.Chart743.family_rationally_dense
              · exact Papers.RationalityTen.Chart744.family_rationally_dense
              · exact Papers.RationalityTen.Chart745.family_rationally_dense
              · exact Papers.RationalityTen.Chart746.family_rationally_dense
              · exact Papers.RationalityTen.Chart747.family_rationally_dense
              · exact Papers.RationalityTen.Chart748.family_rationally_dense
              · exact Papers.RationalityTen.Chart749.family_rationally_dense
              · exact Papers.RationalityTen.Chart750.family_rationally_dense
              · exact Papers.RationalityTen.Chart751.family_rationally_dense
              · exact Papers.RationalityTen.Chart752.family_rationally_dense
              · exact Papers.RationalityTen.Chart753.family_rationally_dense
          · refine (Fin.forall_fin_add (m := 13) (n := 13) _).2 ⟨?_, ?_⟩
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart754.family_rationally_dense
              · exact Papers.RationalityTen.Chart755.family_rationally_dense
              · exact Papers.RationalityTen.Chart756.family_rationally_dense
              · exact Papers.RationalityTen.Chart757.family_rationally_dense
              · exact Papers.RationalityTen.Chart758.family_rationally_dense
              · exact Papers.RationalityTen.Chart759.family_rationally_dense
              · exact Papers.RationalityTen.Chart760.family_rationally_dense
              · exact Papers.RationalityTen.Chart761.family_rationally_dense
              · exact Papers.RationalityTen.Chart762.family_rationally_dense
              · exact Papers.RationalityTen.Chart763.family_rationally_dense
              · exact Papers.RationalityTen.Chart764.family_rationally_dense
              · exact Papers.RationalityTen.Chart765.family_rationally_dense
              · exact Papers.RationalityTen.Chart766.family_rationally_dense
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart767.family_rationally_dense
              · exact Papers.RationalityTen.Chart768.family_rationally_dense
              · exact Papers.RationalityTen.Chart769.family_rationally_dense
              · exact Papers.RationalityTen.Chart770.family_rationally_dense
              · exact Papers.RationalityTen.Chart771.family_rationally_dense
              · exact Papers.RationalityTen.Chart772.family_rationally_dense
              · exact Papers.RationalityTen.Chart773.family_rationally_dense
              · exact Papers.RationalityTen.Chart774.family_rationally_dense
              · exact Papers.RationalityTen.Chart775.family_rationally_dense
              · exact Papers.RationalityTen.Chart776.family_rationally_dense
              · exact Papers.RationalityTen.Chart777.family_rationally_dense
              · exact Papers.RationalityTen.Chart778.family_rationally_dense
              · exact Papers.RationalityTen.Chart779.family_rationally_dense
        · refine (Fin.forall_fin_add (m := 26) (n := 26) _).2 ⟨?_, ?_⟩
          · refine (Fin.forall_fin_add (m := 13) (n := 13) _).2 ⟨?_, ?_⟩
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart780.family_rationally_dense
              · exact Papers.RationalityTen.Chart781.family_rationally_dense
              · exact Papers.RationalityTen.Chart782.family_rationally_dense
              · exact Papers.RationalityTen.Chart783.family_rationally_dense
              · exact Papers.RationalityTen.Chart784.family_rationally_dense
              · exact Papers.RationalityTen.Chart785.family_rationally_dense
              · exact Papers.RationalityTen.Chart786.family_rationally_dense
              · exact Papers.RationalityTen.Chart787.family_rationally_dense
              · exact Papers.RationalityTen.Chart788.family_rationally_dense
              · exact Papers.RationalityTen.Chart789.family_rationally_dense
              · exact Papers.RationalityTen.Chart790.family_rationally_dense
              · exact Papers.RationalityTen.Chart791.family_rationally_dense
              · exact Papers.RationalityTen.Chart792.family_rationally_dense
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart793.family_rationally_dense
              · exact Papers.RationalityTen.Chart794.family_rationally_dense
              · exact Papers.RationalityTen.Chart795.family_rationally_dense
              · exact Papers.RationalityTen.Chart796.family_rationally_dense
              · exact Papers.RationalityTen.Chart797.family_rationally_dense
              · exact Papers.RationalityTen.Chart798.family_rationally_dense
              · exact Papers.RationalityTen.Chart799.family_rationally_dense
              · exact Papers.RationalityTen.Chart800.family_rationally_dense
              · exact Papers.RationalityTen.Chart801.family_rationally_dense
              · exact Papers.RationalityTen.Chart802.family_rationally_dense
              · exact Papers.RationalityTen.Chart803.family_rationally_dense
              · exact Papers.RationalityTen.Chart804.family_rationally_dense
              · exact Papers.RationalityTen.Chart805.family_rationally_dense
          · refine (Fin.forall_fin_add (m := 13) (n := 13) _).2 ⟨?_, ?_⟩
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart806.family_rationally_dense
              · exact Papers.RationalityTen.Chart807.family_rationally_dense
              · exact Papers.RationalityTen.Chart808.family_rationally_dense
              · exact Papers.RationalityTen.Chart809.family_rationally_dense
              · exact Papers.RationalityTen.Chart810.family_rationally_dense
              · exact Papers.RationalityTen.Chart811.family_rationally_dense
              · exact Papers.RationalityTen.Chart812.family_rationally_dense
              · exact Papers.RationalityTen.Chart813.family_rationally_dense
              · exact Papers.RationalityTen.Chart814.family_rationally_dense
              · exact Papers.RationalityTen.Chart815.family_rationally_dense
              · exact Papers.RationalityTen.Chart816.family_rationally_dense
              · exact Papers.RationalityTen.Chart817.family_rationally_dense
              · exact Papers.RationalityTen.Chart818.family_rationally_dense
            · intro i hi
              fin_cases i
              · exact Papers.RationalityTen.Chart819.family_rationally_dense
              · exact Papers.RationalityTen.Chart820.family_rationally_dense
              · exact Papers.RationalityTen.Chart821.family_rationally_dense
              · exact Papers.RationalityTen.Chart822.family_rationally_dense
              · exact Papers.RationalityTen.Chart823.family_rationally_dense
              · exact Papers.RationalityTen.Chart824.family_rationally_dense
              · exact Papers.RationalityTen.Chart825.family_rationally_dense
              · exact Papers.RationalityTen.Chart826.family_rationally_dense
              · exact Papers.RationalityTen.Chart827.family_rationally_dense
              · exact Papers.RationalityTen.Chart828.family_rationally_dense
              · exact Papers.RationalityTen.Chart829.family_rationally_dense
              · exact Papers.RationalityTen.Chart830.family_rationally_dense
              · exact Papers.RationalityTen.Chart831.family_rationally_dense

end Papers.RationalityTen.MatroidChecked.VerifiedRankFour

end
end
end BundlePart2

section BundlePart3
/- Source: MatroidChecked/VerifiedRankFour.lean -/







@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Papers.RationalityTen.MatroidChecked.VerifiedRankFour

open Set Topology Matrix RankFourCatalogueDensity ExactDensity

/-- Lemma 11: every spanning eight-vector configuration outside the
identified golden matroid is a limit of rational representations
with precisely the same vanishing maximal minors. Zero vectors are included. -/
theorem lemma11_rank_four_dense (p : Matrix (Fin 8) (Fin 4) ℝ)
    (hspan : Submodule.span ℝ (Set.range p) = ⊤)
    (hgolden : ¬ HasGoldenMatroid p) :
    p ∈ closure (ExactRationalRealizations p) :=
  exact_density_of_zero_density p
    (rank_four_density catalogue_density_proofs p hspan hgolden)

theorem rank_four_fewer_than_eight_dense {n : ℕ}
    (p : Matrix (Fin n) (Fin 4) ℝ) (hn : n < 8)
    (hspan : Submodule.span ℝ (Set.range p) = ⊤) :
    p ∈ closure (ExactRationalRealizations p) :=
  exact_density_of_zero_density p
    (rank_four_density_below_eight catalogue_density_proofs p hn hspan)

/-- The paper's rational-density statement with all labelled determinant
signs retained, including every repeated or zero row allowed by rank four. -/
theorem lemma11_rank_four_chirotope_dense (p : Matrix (Fin 8) (Fin 4) ℝ)
    (hspan : Submodule.span ℝ (Set.range p) = ⊤)
    (hgolden : ¬ HasGoldenMatroid p) :
    p ∈ closure (ChirotopeDensity.RationalRealizations p) :=
  (ExactSelectedRanks.exact_density_iff_chirotope_density p).mp
    (lemma11_rank_four_dense p hspan hgolden)

/-- The exact exceptional-case formulation of Lemma11, including the
converse: the golden represented matroid has no rational realization. -/
theorem lemma11_rank_four_dense_iff (p : Matrix (Fin 8) (Fin 4) ℝ)
    (hspan : Submodule.span ℝ (Set.range p) = ⊤) :
    p ∈ closure (ChirotopeDensity.RationalRealizations p) ↔ ¬ HasGoldenMatroid p := by
  constructor
  · intro hdense hgolden
    exact GoldenExceptionExact.golden_not_rationally_dense p hgolden hdense
  · exact lemma11_rank_four_chirotope_dense p hspan

end Papers.RationalityTen.MatroidChecked.VerifiedRankFour

end
end
end BundlePart3

section BundlePart4
/- Source: MatroidChecked/PaperRankFourTheorem.lean -/




@[expose] public section
noncomputable section

/-!
# Lemma 11 with the rational coordinates and determinant signs written out

This reader-facing statement identifies the exception with the actual displayed
matrix, rather than with its catalogue index. Its root parameter is arbitrary:
both real solutions of `t² + t - 1 = 0` give the same exceptional matroid.
-/

namespace Papers.RationalityTen.MatroidChecked.PaperRankFourTheorem

open Matrix Set Topology
open VectorBasisFamilies (vectorBases)
open GoldenIdentification
open RankFourCatalogueDensity

/-- The full rank-four claim of Lemma 11, expressed directly using the usual
embedding of the rationals, actual determinants, and the displayed exception. -/
theorem lemma11 (p : Matrix (Fin 8) (Fin 4) ℝ)
    (hspan : Submodule.span ℝ (Set.range p) = ⊤)
    (t : ℝ) (ht : t ^ 2 + t - 1 = 0) :
    p ∈ closure {q : Matrix (Fin 8) (Fin 4) ℝ |
      (∀ i j, ∃ a : ℚ, (a : ℝ) = q i j) ∧
      ∀ b : Fin 4 → Fin 8,
        SignType.sign (Matrix.of (fun i j => q (b i) j)).det =
          SignType.sign (Matrix.of (fun i j => p (b i) j)).det} ↔
      ¬ ∃ σ : Equiv.Perm (Fin 8),
        (vectorBases p).image (fun S => S.image σ) =
          vectorBases (goldenRows t) := by
  change p ∈ closure (ChirotopeDensity.RationalRealizations p) ↔ _
  exact (VerifiedRankFour.lemma11_rank_four_dense_iff p hspan).trans
    (not_congr (golden_isomorphism_iff p t ht))

/-- The nine dependent four-element sets stated immediately after Lemma 11,
expressed for the displayed matrix itself. Lean labels start at zero. -/
theorem lemma11_nonbases (t : ℝ) (ht : t ^ 2 + t - 1 = 0) :
    (Finset.univ : Finset (Fin 8)).powersetCard 4 \
      vectorBases (goldenRows t) = paperNonbases := by
  rw [golden_vectorBases t ht]
  exact golden_nonbases_exact

end Papers.RationalityTen.MatroidChecked.PaperRankFourTheorem

end
end
end BundlePart4

section BundlePart5
/- Source: MatroidChecked/MatrixClassificationAssembly.lean -/




@[expose] public section
noncomputable section

/-!
# Closed matrix classification consequences

The rank-four hypothesis of the generic reconstruction is discharged here
by the exhaustive finite catalogue and its actual-realization chart proofs.
Both exported propositions have exactly the unrestricted statements used
by the polytope geometry.
-/

namespace Papers.RationalityTen.MatroidChecked.MatrixClassificationAssembly
open ChirotopeDensity

theorem eight_row_density_or_four_column_support : EightRowMatrixDensityOrFourSupport :=
  MatrixClassificationCore.eight_row_density_or_four_column_support
    VerifiedRankFour.lemma11_rank_four_dense

theorem nine_column_exceptional_matrix_density : NineColumnExceptionalMatrixDensity :=
  MatrixClassificationCore.nine_column_exceptional_matrix_density
    VerifiedRankFour.lemma11_rank_four_dense

end Papers.RationalityTen.MatroidChecked.MatrixClassificationAssembly

end
end
end BundlePart5
