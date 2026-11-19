module
public import MatroidChecked.ChartPolynomial
public import Papers.RationalityTenOrderedMinors
public import MatroidCatalogue.N8R4
public import Mathlib.Tactic.Linarith
public import Mathlib.Basic.Real.Basic

@[expose] public section
noncomputable section

/-!
# Identification of the exceptional catalogue entry

The matrix below is the matrix displayed in Lemma 11 of the paper. The
finite permutation and every maximal minor are checked in Lean. Thus the
exceptional index is identified by its mathematical basis family, without
trusting a catalogue name, an unverified lookup, or a symbolic status flag.
-/

namespace Papers.RationalityTen.MatroidChecked.GoldenIdentification

open Matrix Finset ChartPolynomial
open BasisCertificates (checkedPermutation ValidPermutation Table)
open VectorBasisFamilies (vectorBases mem_vectorBases det_ne_zero_iff_basis_image
  span_of_independent_card)

def goldenBlock (t : ℝ) : Coordinate → Coordinate → ℝ :=
  ![![1,1,0,1], ![1,0,1,1], ![0,1,t,t+1], ![1,1,t,0]]

def goldenRows (t : ℝ) : Matrix Point Coordinate ℝ := rowMatrix (goldenBlock t)

def catalogueToPaperCode : ℕ := 12219921

theorem catalogueToPaper_valid : ValidPermutation 8 catalogueToPaperCode := by
  decide +kernel

def catalogueToPaper : Equiv.Perm Point :=
  checkedPermutation 8 catalogueToPaperCode catalogueToPaper_valid

def goldenFamily : Finset (Finset Point) :=
  (MatroidCatalogue.N8R4.family 563).image (fun A => A.image catalogueToPaper)

def goldenBasisFlags : Fin 70 → Bool :=
  ![true, true, true, true, false, false, true, true, true, true, true, true, false, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, false, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, false, true]

def goldenMinorRemainders (t : ℝ) : Fin 70 → ℝ :=
  ![1, 1, 1, t, 0, 0, -1, -t, -t - 1, -1, -t, -t - 1, 0, -t - 1, -1, 1, 0, 1, 1, -1, 1 - t, 1, 1, 1, t, 1, t, t + 1, -1, -1, 1, -1, -t - 2, 0, t + 1, -1, -1, 0, -1, 0, t, -1, t, -1, -t, -1, -t, -t - 1, -t, -t, t, -t, 1, t + 1, 1, -1, 1, 0, 1, 1, -1, -t, 1, -1, -t - 1, t + 1, t + 1, -t - 1, 0, t + 2]

def paperNonbases : Finset (Finset Point) :=
  {{0,1,2,7},{0,1,3,4},{0,1,5,6},{0,2,3,5},{0,4,6,7},
    {1,2,3,6},{1,2,4,5},{2,3,4,7},{3,5,6,7}}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem golden_basis_pattern : ∀ i, goldenBasisFlags i = true ↔ minorSet i ∈ goldenFamily := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem golden_nonbases_exact :
    (univ : Finset Point).powersetCard 4 \ goldenFamily = paperNonbases := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem golden_basis_card : ∀ A ∈ goldenFamily, A.card = 4 := by
  decide +kernel

/- Reduction of all 70 actual determinants under the stated quadratic,
including the determinant of the identity basis. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem golden_minor_eq (t : ℝ) (ht : t^2 + t - 1 = 0) (i : Fin 70) :
    ((goldenRows t).submatrix (minorRows i) id).det = goldenMinorRemainders t i := by
  rw [goldenRows,minorFormula_correct]
  fin_cases i <;>
    dsimp [goldenBlock,minorFormula,minorFormulaTree,FormulaTable.get,goldenMinorRemainders] <;>
    norm_num <;> nlinarith only [ht]

theorem golden_remainders_nonzero (t : ℝ) (ht : t^2 + t - 1 = 0) (i : Fin 70) :
    goldenMinorRemainders t i ≠ 0 ↔ goldenBasisFlags i = true := by
  have h0 : t ≠ 0 := by intro h; rw [h] at ht; norm_num at ht
  have h1 : t ≠ 1 := by intro h; rw [h] at ht; norm_num at ht
  have hn1 : t ≠ -1 := by intro h; rw [h] at ht; norm_num at ht
  have hn2 : t ≠ -2 := by intro h; rw [h] at ht; norm_num at ht
  have hp1 : t + 1 ≠ 0 := by intro h; apply hn1; linarith
  have hp2 : t + 2 ≠ 0 := by intro h; apply hn2; linarith
  have hm1 : -t - 1 ≠ 0 := by intro h; apply hn1; linarith
  have hm2 : -t - 2 ≠ 0 := by intro h; apply hn2; linarith
  have h1m : 1 - t ≠ 0 := by intro h; apply h1; linarith
  fin_cases i <;> simp [goldenMinorRemainders,goldenBasisFlags,h0,hp1,hp2,hm1,hm2,h1m]

/-- Exact identification of every basis and every nonbasis of the paper's
displayed real matrix with the relabelled exceptional catalogue entry. -/
theorem golden_vectorBases (t : ℝ) (ht : t^2 + t - 1 = 0) :
    vectorBases (goldenRows t) = goldenFamily := by
  ext A
  by_cases hc : A.card = 4
  · obtain ⟨i,rfl⟩ := exists_minorSet A hc
    change (univ.image (minorRows i)) ∈ vectorBases (fun i j => goldenRows t i j) ↔ _
    rw [← det_ne_zero_iff_basis_image]
    have hm : (fun a b => goldenRows t (minorRows i a) b) =
        (goldenRows t).submatrix (minorRows i) id := by ext a b; rfl
    rw [hm]
    rw [golden_minor_eq t ht,golden_remainders_nonzero t ht,golden_basis_pattern]
  · constructor
    · intro h
      exact (hc ((mem_vectorBases _ A).mp h).1).elim
    · intro h
      exact (hc (golden_basis_card A h)).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem golden_triples_extend :
    ∀ S : Finset Point, S.card = 3 → ∃ A ∈ goldenFamily, S ⊆ A := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem golden_fives_contain_basis :
    ∀ S : Finset Point, S.card = 5 → ∃ A ∈ goldenFamily, A ⊆ S := by
  decide +kernel

theorem golden_triple_independent (t : ℝ) (ht : t^2 + t - 1 = 0)
    (S : Finset Point) (hS : S.card = 3) :
    LinearIndepOn ℝ (goldenRows t) (S : Set Point) := by
  obtain ⟨A,hA,hSA⟩ := golden_triples_extend S hS
  rw [← golden_vectorBases t ht] at hA
  exact ((mem_vectorBases _ A).mp hA).2.mono hSA

theorem golden_five_spans (t : ℝ) (ht : t^2 + t - 1 = 0)
    (S : Finset Point) (hS : S.card = 5) :
    Submodule.span ℝ ((goldenRows t) '' (S : Set Point)) = ⊤ := by
  obtain ⟨A,hA,hAS⟩ := golden_fives_contain_basis S hS
  rw [← golden_vectorBases t ht] at hA
  obtain ⟨hcard,hLI⟩ := (mem_vectorBases _ A).mp hA
  have hspan := span_of_independent_card (goldenRows t) A hLI hcard
  apply top_unique
  rw [← hspan]
  apply Submodule.span_mono
  rintro _ ⟨x,hx,rfl⟩
  exact ⟨x,hAS hx,rfl⟩

theorem golden_isomorphism_iff (p : Matrix Point Coordinate ℝ)
    (t : ℝ) (ht : t^2 + t - 1 = 0) :
    (∃ σ : Equiv.Perm Point, (vectorBases p).image (fun A => A.image σ) =
      MatroidCatalogue.N8R4.family 563) ↔
    (∃ σ : Equiv.Perm Point, (vectorBases p).image (fun A => A.image σ) =
      vectorBases (goldenRows t)) := by
  rw [golden_vectorBases t ht]
  constructor
  · rintro ⟨σ,hσ⟩
    refine ⟨σ.trans catalogueToPaper,?_⟩
    rw [goldenFamily,← hσ]
    simp only [Finset.image_image,Equiv.coe_trans,Function.comp_def,Equiv.trans_apply]
  · rintro ⟨σ,hσ⟩
    refine ⟨σ.trans catalogueToPaper.symm,?_⟩
    have h := congrArg
      (fun B : Finset (Finset Point) => B.image (fun A => A.image catalogueToPaper.symm)) hσ
    simpa only [goldenFamily,Finset.image_image,Equiv.coe_trans,Function.comp_def,Equiv.trans_apply,
      Equiv.symm_apply_apply,Finset.image_id,Finset.image_id'] using h

end Papers.RationalityTen.MatroidChecked.GoldenIdentification
