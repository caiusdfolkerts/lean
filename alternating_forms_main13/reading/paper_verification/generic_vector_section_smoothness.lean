module

public import PaperVerification.UniversalCriticalSections
public import PaperVerification.MatrixRightInverseCriterion
public import PaperVerification.FormallySmoothRelations
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.RingTheory.Finiteness.Quotient
import Mathlib.Tactic

/-!
# Generic smoothness of a generated vector-valued section

On a smooth affine chart with a free differential module, a finite generating
family of sections is an evaluation matrix with a right inverse. We construct
a nonzero polynomial in its original parameters such that every specialization
outside its zero set has a smooth literal quotient ring.

No smoothness, reducedness, regular-sequence condition, or rank hypothesis on
the specialized zero scheme is assumed.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open KaehlerDifferential

namespace PaperVerification.GenericSectionDifferentials

variable {K R ι κ τ : Type*} [Field K] [CharZero K] [CommRing R]
  [Algebra K R] [Fintype ι] [Fintype κ] [Fintype τ] [DecidableEq κ]

/-- The original linear combination of the chosen generating sections. -/
def linearSection (v : Matrix κ ι R) (a : ι → K) (j : κ) : R :=
  ∑ i, a i • v j i

lemma linearSection_gradient (b : Module.Basis τ R Ω[R⁄K])
    (v : Matrix κ ι R) (a : ι → K) (j : κ) (t : τ) :
    b.repr (D K R (linearSection v a j)) t =
      ∑ i, a i • b.repr (D K R (v j i)) t := by
  simp only [linearSection,map_sum,Derivation.map_smul,Finset.sum_apply']
  apply Finset.sum_congr rfl
  intro i hi
  exact congrArg (fun z => z t) (b.repr.toLinearMap.map_smul_of_tower (a i)
    (D K R (v j i)))

set_option backward.isDefEq.respectTransparency false in
/-- Every specialization outside the constructed nonempty principal open
cuts out a smooth affine zero scheme. The algebra is the actual ideal quotient
by the components of the original section. -/
theorem linearSection_quotient_smooth [Algebra.FiniteType K R]
    [Algebra.FormallySmooth K R]
    (b : Module.Basis τ R Ω[R⁄K]) (v : Matrix κ ι R)
    (u : Matrix ι κ R) (hvu : v * u = 1) (a : ι → K)
    (ha : MvPolynomial.aeval a (criticalAvoidancePolynomial b v u hvu) ≠ 0) :
    Algebra.Smooth K (R ⧸ Ideal.span (Set.range (linearSection v a))) := by
  classical
  let I := Ideal.span (Set.range (linearSection v a))
  let S := R ⧸ I
  let P := Algebra.Extension.ofSurjective (Ideal.Quotient.mkₐ K I)
    (Ideal.Quotient.mkₐ_surjective K I)
  let G : Matrix κ τ S := fun j t =>
    algebraMap R S (b.repr (D K R (linearSection v a j)) t)
  have hG : ∀ (J : Ideal S) [J.IsMaximal],
      LinearIndependent (S ⧸ J) (G.map (Ideal.Quotient.mk J)) := by
    intro J hJ
    let L := S ⧸ J
    letI : Field L := Ideal.Quotient.field J
    let χ : R →ₐ[K] L := (Ideal.Quotient.mkₐ K J).comp (Ideal.Quotient.mkₐ K I)
    let a' : ι → L := fun i => algebraMap K L (a i)
    have ha' : MvPolynomial.aeval a' (criticalAvoidancePolynomial b v u hvu) ≠ 0 := by
      have he : algebraMap K L (MvPolynomial.aeval a (criticalAvoidancePolynomial b v u hvu)) =
          MvPolynomial.aeval a' (criticalAvoidancePolynomial b v u hvu) := by
        simpa only [Algebra.ofId_apply,a'] using
          (MvPolynomial.comp_aeval_apply a (Algebra.ofId K L)
            (criticalAvoidancePolynomial b v u hvu))
      rw [← he]
      intro h
      exact ha ((algebraMap K L).injective (h.trans (map_zero _).symm))
    have hz : ∀ j, ∑ i, a' i * χ (v j i) = 0 := by
      intro j
      have hz' : algebraMap R S (linearSection v a j) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self j))
      have h : χ (linearSection v a j) = 0 := by
        change Ideal.Quotient.mk J (algebraMap R S (linearSection v a j)) = 0
        rw [hz',map_zero]
      simpa only [linearSection,map_sum,Algebra.smul_def,map_mul,AlgHom.commutes,a'] using h
    have hind := specialized_gradient_linearIndependent b v u hvu χ a' ha' hz
    convert hind using 1
    funext j t
    change χ (b.repr (D K R (linearSection v a j)) t) = _
    rw [linearSection_gradient]
    simp only [map_sum,a',Algebra.smul_def,map_mul,AlgHom.commutes]
  obtain ⟨U,hU⟩ := matrix_rightInverse_of_residue_rows G hG
  have hf : Ideal.span (Set.range (linearSection v a)) = P.ker := by
    exact Ideal.mk_ker.symm
  letI : Algebra.FormallySmooth K P.Ring :=
    inferInstanceAs (Algebra.FormallySmooth K R)
  have hs : Algebra.FormallySmooth K S :=
    formallySmooth_of_jacobian_rightInverse P b (linearSection v a) hf U hU
  letI : Algebra.FinitePresentation K S :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact ⟨hs, inferInstance⟩

/-- The good parameter locus has a rational point over the original field.
Characteristic zero is used through infinitude, as well as in the differential
argument that constructs its nonzero defining polynomial. -/
theorem exists_linearSection_smooth [Algebra.FiniteType K R]
    [Algebra.FormallySmooth K R]
    (b : Module.Basis τ R Ω[R⁄K]) (v : Matrix κ ι R)
    (u : Matrix ι κ R) (hvu : v * u = 1) :
    ∃ a : ι → K,
      MvPolynomial.aeval a (criticalAvoidancePolynomial b v u hvu) ≠ 0 ∧
      Algebra.Smooth K (R ⧸ Ideal.span (Set.range (linearSection v a))) := by
  classical
  letI : Infinite K := Infinite.of_injective Nat.cast Nat.cast_injective
  have hex : ∃ a : ι → K,
      MvPolynomial.aeval a (criticalAvoidancePolynomial b v u hvu) ≠ 0 := by
    by_contra h
    push Not at h
    apply criticalAvoidancePolynomial_ne_zero b v u hvu
    apply MvPolynomial.funext
    intro a
    simpa only [map_zero, MvPolynomial.aeval_eq_eval] using h a
  obtain ⟨a,ha⟩ := hex
  exact ⟨a,ha,linearSection_quotient_smooth b v u hvu a ha⟩

end PaperVerification.GenericSectionDifferentials
