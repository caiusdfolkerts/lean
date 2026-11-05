module

public import PaperVerification.AlternatingFormsPluckerIsotropy
public import PaperVerification.GradedDehomogenization

/-!
# The actual homogeneous cone of the isotropic Plücker equations

The generic maximal-minor map multiplies ordinary degrees by the row count.
For a positive row count this proves that its actual kernel is homogeneous.
Together with the literal degree-one wedge equations, it supplies the genuine
homogeneous ideal required by the dehomogenization dimension argument.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial Matrix
open scoped BigOperators

namespace PaperVerification.AlternatingForms

variable {K : Type*} [Field K] {s n t m : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

theorem genericPluckerMinor_isHomogeneous (I : PluckerIndex s n) :
    (genericPluckerMinor (K := K) I).IsHomogeneous s := by
  classical
  rw [genericPluckerMinor,Matrix.det_apply]
  apply IsHomogeneous.sum
  intro σ hσ
  have hp : (∏ i : Fin s, (X (σ i,I.val i) : MvPolynomial (Fin s × Fin n) K)).IsHomogeneous s := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,
      Nat.cast_id] using
      IsHomogeneous.prod Finset.univ (fun i : Fin s => (X (σ i,I.val i) : MvPolynomial (Fin s × Fin n) K))
        (fun _ => 1) (fun i hi => isHomogeneous_X K _)
  simpa only [Units.smul_def,Matrix.of_apply,MvPolynomial.mem_homogeneousSubmodule] using
    (homogeneousSubmodule (Fin s × Fin n) K s).smul_of_tower_mem (Equiv.Perm.sign σ : ℤ) hp

theorem genericPluckerMap_isHomogeneous (f : MvPolynomial (PluckerIndex s n) K)
    (d : ℕ) (hf : f.IsHomogeneous d) :
    (genericPluckerMap f).IsHomogeneous (s*d) :=
  hf.aeval _ (fun I => genericPluckerMinor_isHomogeneous I)

theorem genericPluckerMap_component (hs : 0<s)
    (f : MvPolynomial (PluckerIndex s n) K) (d : ℕ) :
    homogeneousComponent (s*d) (genericPluckerMap f) =
      genericPluckerMap (homogeneousComponent d f) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial a c =>
    rw [homogeneousComponent_of_mem (genericPluckerMap_isHomogeneous _ a.degree
      (isHomogeneous_monomial c rfl)),
      homogeneousComponent_of_mem (isHomogeneous_monomial c rfl)]
    by_cases he : d=a.degree
    · simp only [he,ite_true]
    · have hne : s*d≠s*a.degree := fun h => he (Nat.eq_of_mul_eq_mul_left hs h)
      simp only [he,hne,ite_false,map_zero]
  | add f g hf hg => simp only [map_add,hf,hg]

theorem matrixPluckerIdeal_isHomogeneous (hs : 0<s) :
    (matrixPluckerIdeal (K := K) (s := s) (n := n)).IsHomogeneous
      (homogeneousSubmodule (PluckerIndex s n) K) := by
  intro d f hf
  change genericPluckerMap f=0 at hf
  change genericPluckerMap
    (DirectSum.decompose (homogeneousSubmodule (PluckerIndex s n) K) f d :
      MvPolynomial (PluckerIndex s n) K)=0
  have hc : (DirectSum.decompose (homogeneousSubmodule (PluckerIndex s n) K) f d :
      MvPolynomial (PluckerIndex s n) K)=homogeneousComponent d f :=
    MvPolynomial.decomposition.decompose'_apply f d
  rw [hc,←genericPluckerMap_component hs,hf,map_zero]

theorem orderedPluckerCoordinate_isHomogeneous (I : Fin s → Fin n) :
    (orderedPluckerCoordinate (K := K) I).IsHomogeneous 1 := by
  classical
  unfold orderedPluckerCoordinate
  split_ifs
  · exact (homogeneousSubmodule (PluckerIndex s n) K 1).smul_mem _ (isHomogeneous_X K _)
  · exact isHomogeneous_zero _ K _

theorem pluckerIsotropyEquation_isHomogeneous (f : StrictPairs n → K) (J : Fin t → Fin n) :
    (pluckerIsotropyEquation f J).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro a ha
  exact (homogeneousSubmodule (PluckerIndex (t+2) n) K 1).smul_mem _
    (orderedPluckerCoordinate_isHomogeneous _)

theorem isotropicPluckerIdeal_isHomogeneous (forms : Fin m → StrictPairs n → K) :
    (isotropicPluckerIdeal (t := t) forms).IsHomogeneous
      (homogeneousSubmodule (PluckerIndex (t+2) n) K) := by
  apply (matrixPluckerIdeal_isHomogeneous (by omega : 0<t+2)).sup
  apply Ideal.homogeneous_span
  rintro q ⟨a,rfl⟩
  exact ⟨1,pluckerIsotropyEquation_isHomogeneous _ _⟩

end PaperVerification.AlternatingForms
