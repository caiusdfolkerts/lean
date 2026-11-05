module

public import PaperVerification.ToricPointedMonoids
public import PaperVerification.ToricCoordinateDifferentials
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Independent actual cotangent vectors of semigroup atoms

At the rational point of a pointed semigroup algebra which kills all
nonconstant characters, the coefficient of an indecomposable exponent
is a genuine derivation. Its universal Kähler functional isolates the
corresponding cotangent vector. Consequently distinct atoms give
linearly independent vectors in the actual cotangent fibre, in every
characteristic.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open AddMonoidAlgebra KaehlerDifferential
open scoped TensorProduct BigOperators Classical

variable (k : Type*) [Field k] (S : Type*) [AddCommMonoid S]
    (hzero : ∀ a b : S,a+b=0 → a=0 ∧ b=0)

def pointedEvaluationMonoid : Multiplicative S →* k where
  toFun s := if s.toAdd=0 then 1 else 0
  map_one' := by simp
  map_mul' s t := by
    by_cases hs : s.toAdd=0 <;> by_cases ht : t.toAdd=0
    · simp [hs,ht]
    · simp [hs,ht]
    · simp [hs,ht]
    · have hst : s.toAdd+t.toAdd≠0 := fun h => hs (hzero _ _ h).1
      simp [hs,ht,hst]

/-- The actual rational closed-orbit point of a pointed semigroup algebra. -/
def pointedAugmentation : AddMonoidAlgebra k S →ₐ[k] k :=
  AddMonoidAlgebra.lift k k S (pointedEvaluationMonoid k S hzero)

@[simp] theorem pointedAugmentation_single (m : S) (r : k) :
    pointedAugmentation k S hzero (single m r) = if m=0 then r else 0 := by
  by_cases hm : m=0 <;>
    simp [pointedAugmentation,pointedEvaluationMonoid,hm]

def pointedAlgebra : Algebra (AddMonoidAlgebra k S) k :=
  (pointedAugmentation k S hzero).toRingHom.toAlgebra

def pointedScalarTower :
    letI := pointedAlgebra k S hzero
    IsScalarTower k (AddMonoidAlgebra k S) k := by
  letI := pointedAlgebra k S hzero
  exact IsScalarTower.of_algebraMap_eq fun r =>
    ((pointedAugmentation k S hzero).commutes r).symm

abbrev PointedCotangentFiber : Type _ :=
  letI := pointedAlgebra k S hzero
  k ⊗[AddMonoidAlgebra k S] Ω[AddMonoidAlgebra k S⁄k]

abbrev pointedCotangentFiber_addCommGroup :
    AddCommGroup (PointedCotangentFiber k S hzero) := by
  letI := pointedAlgebra k S hzero
  exact inferInstanceAs (AddCommGroup (k ⊗[AddMonoidAlgebra k S] Ω[AddMonoidAlgebra k S⁄k]))

abbrev pointedCotangentFiber_module : Module k (PointedCotangentFiber k S hzero) := by
  letI := pointedAlgebra k S hzero
  exact inferInstanceAs (Module k (k ⊗[AddMonoidAlgebra k S] Ω[AddMonoidAlgebra k S⁄k]))

def pointedCotangentVector (m : S) : PointedCotangentFiber k S hzero := by
  letI := pointedAlgebra k S hzero
  exact 1 ⊗ₜ[AddMonoidAlgebra k S] D k (AddMonoidAlgebra k S) (single m 1)

/-- A coefficient at an atom satisfies Leibniz at the actual augmentation. -/
def atomCoefficientDerivation (p : S) (hp0 : p≠0)
    (hpatom : ∀ a b : S,a+b=p → a=0 ∨ b=0) :
    letI := pointedAlgebra k S hzero
    Derivation k (AddMonoidAlgebra k S) k := by
  letI := pointedAlgebra k S hzero
  refine
    { (AddMonoidAlgebra.basis S k).coord p with
      map_one_eq_zero' := ?_
      leibniz' := ?_ }
  · change (1 : AddMonoidAlgebra k S).coeff p=0
    simp [AddMonoidAlgebra.one_def,hp0,Ne.symm hp0]
  · intro f g
    change (f*g).coeff p =
      pointedAugmentation k S hzero f * g.coeff p +
        pointedAugmentation k S hzero g * f.coeff p
    induction f using AddMonoidAlgebra.induction_on with
    | of a =>
        induction g using AddMonoidAlgebra.induction_on with
        | of b =>
            change (single a (1:k)*single b 1).coeff p = _
            by_cases ha : a=0
            · subst a
              simp [hp0,Ne.symm hp0]
            by_cases hb : b=0
            · subst b
              simp [hp0,Ne.symm hp0]
            have hab : a+b≠p := by
              intro hh
              rcases hpatom a b hh with h|h
              · exact ha h
              · exact hb h
            simp [single_mul_single,ha,hb,hab,Ne.symm hab]
        | add g g' hg hg' =>
            simp only [mul_add,map_add,coeff_add,Finsupp.add_apply,hg,hg']
            ring
        | smul r g hg =>
            simp only [mul_smul_comm,coeff_smul,map_smul,Finsupp.smul_apply,smul_eq_mul,hg]
            ring
    | add f f' hf hf' =>
        simp only [add_mul,map_add,coeff_add,Finsupp.add_apply,hf,hf']
        ring
    | smul r f hf =>
        simp only [smul_mul_assoc,coeff_smul,map_smul,Finsupp.smul_apply,smul_eq_mul,hf]
        ring

def atomCotangentCoordinate (p : S) (hp0 : p≠0)
    (hpatom : ∀ a b : S,a+b=p → a=0 ∨ b=0) :
    PointedCotangentFiber k S hzero →ₗ[k] k := by
  letI := pointedAlgebra k S hzero
  letI := pointedScalarTower k S hzero
  exact (atomCoefficientDerivation k S hzero p hp0 hpatom).liftKaehlerDifferential.liftBaseChange k

@[simp] theorem atomCotangentCoordinate_vector
    (p : S) (hp0 : p≠0)
    (hpatom : ∀ a b : S,a+b=p → a=0 ∨ b=0) (m : S) :
    atomCotangentCoordinate k S hzero p hp0 hpatom
      (pointedCotangentVector k S hzero m) = if m=p then 1 else 0 := by
  letI := pointedAlgebra k S hzero
  letI := pointedScalarTower k S hzero
  change (atomCoefficientDerivation k S hzero p hp0 hpatom).liftKaehlerDifferential.liftBaseChange k
    (1 ⊗ₜ[AddMonoidAlgebra k S] D k (AddMonoidAlgebra k S) (single m 1)) = _
  rw [LinearMap.liftBaseChange_tmul,one_smul,Derivation.liftKaehlerDifferential_comp_D]
  change (single m (1:k)).coeff p = _
  simp only [coeff_single,Finsupp.single_apply]

theorem linearIndependent_pointedCotangentAtoms
    {ι : Type*} (p : ι → S) (hpinj : Function.Injective p)
    (hp0 : ∀ i,p i≠0)
    (hpatom : ∀ i,∀ a b : S,a+b=p i → a=0 ∨ b=0) :
    LinearIndependent k (fun i => pointedCotangentVector k S hzero (p i)) := by
  rw [linearIndependent_iff']
  intro s c h i hi
  have hc := congrArg (atomCotangentCoordinate k S hzero (p i) (hp0 i) (hpatom i)) h
  simpa only [map_sum,map_smul,map_zero,atomCotangentCoordinate_vector,
    hpinj.eq_iff,smul_eq_mul,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq',hi,if_pos] using hc

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.linearIndependent_pointedCotangentAtoms
