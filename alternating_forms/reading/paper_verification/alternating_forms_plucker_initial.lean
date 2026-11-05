module

public import PaperVerification.AlternatingFormsPrefixWeights
public import PaperVerification.WeightedInitialComparison

/-!
# The actual Grassmannian identities survive vertex-weight initialization

Generic matrix entries have the weight of their column. Every maximal minor
has the sum of its selected column weights, so the generic-minor map commutes
with the corresponding weighted homogeneous components. This proves the
required inclusion of the entire actual Plücker kernel in the initial ideal
of the isotropic equations, without assuming a list of Plücker generators.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace PaperVerification.AlternatingForms

open scoped BigOperators
open MvPolynomial Matrix
open PaperVerification.WeightedInitialFiber

variable {K : Type*} [Field K] {s n t m : ℕ}

theorem genericPluckerMinor_isWeightedHomogeneous (w : Fin n → ℕ)
    (I : PluckerIndex s n) :
    (genericPluckerMinor (K := K) I).IsWeightedHomogeneous
      (fun a : Fin s × Fin n => w a.2) (pluckerVertexWeight w I) := by
  classical
  rw [genericPluckerMinor,Matrix.det_apply]
  apply IsWeightedHomogeneous.sum
  intro σ hσ
  have hp : (∏ i : Fin s,(X (σ i,I.val i) : MvPolynomial (Fin s × Fin n) K)).IsWeightedHomogeneous (fun a : Fin s × Fin n => w a.2)
        (pluckerVertexWeight w I) := by
    exact IsWeightedHomogeneous.prod Finset.univ
      (fun i : Fin s => (X (σ i,I.val i) : MvPolynomial (Fin s × Fin n) K))
      (fun i => w (I.val i))
      (fun i hi => isWeightedHomogeneous_X K (fun a : Fin s × Fin n => w a.2) _)
  simpa only [Units.smul_def,Matrix.of_apply,mem_weightedHomogeneousSubmodule] using
    (weightedHomogeneousSubmodule K (fun a : Fin s × Fin n => w a.2)
      (pluckerVertexWeight w I)).smul_of_tower_mem (Equiv.Perm.sign σ : ℤ) hp

theorem genericPluckerMap_isWeightedHomogeneous (w : Fin n → ℕ)
    (f : MvPolynomial (PluckerIndex s n) K) (d : ℕ)
    (hf : f.IsWeightedHomogeneous (pluckerVertexWeight w) d) :
    (genericPluckerMap f).IsWeightedHomogeneous (fun a : Fin s × Fin n => w a.2) d :=
  hf.aeval (fun I => genericPluckerMinor_isWeightedHomogeneous w I)

theorem genericPluckerMap_weightedComponent (w : Fin n → ℕ)
    (f : MvPolynomial (PluckerIndex s n) K) (d : ℕ) :
    weightedHomogeneousComponent (fun a : Fin s × Fin n => w a.2) d
      (genericPluckerMap f) =
        genericPluckerMap (weightedHomogeneousComponent (pluckerVertexWeight w) d f) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial a c =>
      rw [weightedHomogeneousComponent_of_mem
        (genericPluckerMap_isWeightedHomogeneous w _ (Finsupp.weight (pluckerVertexWeight w) a)
          (isWeightedHomogeneous_monomial (pluckerVertexWeight w) a c rfl)),
        weightedHomogeneousComponent_of_mem
          (isWeightedHomogeneous_monomial (pluckerVertexWeight w) a c rfl)]
      split_ifs <;> simp only [map_zero]
  | add f g hf hg => simp only [map_add,hf,hg]

theorem matrixPluckerIdeal_weightedComponent_mem (w : Fin n → ℕ)
    (f : MvPolynomial (PluckerIndex s n) K) (hf : f∈matrixPluckerIdeal) (d : ℕ) :
    weightedHomogeneousComponent (pluckerVertexWeight w) d f∈matrixPluckerIdeal := by
  change genericPluckerMap f=0 at hf
  change genericPluckerMap (weightedHomogeneousComponent (pluckerVertexWeight w) d f)=0
  rw [←genericPluckerMap_weightedComponent w,hf,map_zero]

/-- The whole generic-minor kernel is included in the actual initial ideal
of the linear isotropy equations, for the induced vertex weights. -/
theorem matrixPluckerIdeal_le_initial_isotropic (forms : Fin m → StrictPairs n → K)
    (w : Fin n → ℕ) :
    matrixPluckerIdeal ≤ initialIdeal (isotropicPluckerIdeal (t := t) forms)
      (pluckerVertexWeight w) := by
  intro f hf
  have hcomp (d : ℕ) : weightedHomogeneousComponent (pluckerVertexWeight w) d f ∈
      initialIdeal (isotropicPluckerIdeal (t := t) forms) (pluckerVertexWeight w) := by
    have hmem : weightedHomogeneousComponent (pluckerVertexWeight w) d f ∈
        isotropicPluckerIdeal (t := t) forms :=
      Submodule.mem_sup_left (matrixPluckerIdeal_weightedComponent_mem w f hf d)
    have hc := component_mem_initialIdeal (isotropicPluckerIdeal (t := t) forms)
      (pluckerVertexWeight w) (weightedHomogeneousComponent (pluckerVertexWeight w) d f)
      hmem d (weightBound_component (pluckerVertexWeight w) f d d le_rfl)
    rwa [weightedHomogeneousComponent_eq_self
      (weightedHomogeneousComponent_isWeightedHomogeneous d f)] at hc
  rw [←sum_components_of_bound (pluckerVertexWeight w) f
    (weightedTotalDegree (pluckerVertexWeight w) f) (weightBound_total _ f)]
  exact (initialIdeal (isotropicPluckerIdeal (t := t) forms) (pluckerVertexWeight w)).sum_mem
    (fun d hd => hcomp d)

end PaperVerification.AlternatingForms
