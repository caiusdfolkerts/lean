module

public import Continuation.Divisor.FanoClosure
public import Continuation.Divisor.IntrinsicBoundaryFoundations
public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.Group.Submonoid.Finsupp
public import Mathlib.Algebra.MonoidAlgebra.Grading
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Data.Real.Basic
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.Basis.SMul
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring

/-!
# Reconstruction of the original toric scheme

These complete recovered proof sections complement the existing checked
fan, boundary, and actual-section owners. The selection manifest records
all source identities and the three already-owned prefixes omitted here.
No mathematical theorem is replaced by an assumption.
-/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

section
-- BEGIN PaperVerification.ToricMonoidCotangent



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

end
-- END PaperVerification.ToricMonoidCotangent
end

section
-- BEGIN PaperVerification.ToricSmoothCotangentRank



/-!
# Smooth cotangent fibres have the actual generic differential rank

Smoothness makes the Kähler module finite projective, hence finite flat.
The existing rank-at-prime theorem then identifies its fibre dimension
with its fraction-field rank. This argument requires no additional
regular-local-ring or normality hypothesis.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open KaehlerDifferential
open scoped TensorProduct Classical

section GenericRank

variable (k R K : Type*) [Field k] [CommRing R] [IsDomain R] [Field K]
    [Algebra k R] [Algebra k K] [Algebra R K] [IsScalarTower k R K]
    [IsFractionRing R K] {n : ℕ}
    (bK : Module.Basis (Fin n) K Ω[K⁄k])

include bK in
theorem kaehler_finrank_eq_generic_basis : Module.finrank R Ω[R⁄k] = n := by
  calc
    Module.finrank R Ω[R⁄k] = Module.finrank R Ω[K⁄k] :=
      (IsLocalizedModule.finrank_eq (nonZeroDivisors R)
        (KaehlerDifferential.map k k R K) le_rfl).symm
    _ = Module.finrank K Ω[K⁄k] :=
      (IsFractionRing.finrank_right_eq R K Ω[K⁄k]).symm
    _ = n := by simpa using Module.finrank_eq_card_basis bK

variable [Algebra.Smooth k R] [Algebra R k] [IsScalarTower k R k]

include bK in
/-- The point is specified by the actual algebra structure R→k. -/
theorem smooth_rational_cotangent_finrank :
    Module.finrank k (k ⊗[R] Ω[R⁄k]) = n := by
  let p₀ : PrimeSpectrum k := ⟨⊥,inferInstance⟩
  let p : PrimeSpectrum R := p₀.comap (algebraMap R k)
  have hb := Module.rankAtStalk_baseChange (R := R) (M := Ω[R⁄k]) p₀
  rw [Module.rankAtStalk_eq_finrank_of_free] at hb
  calc
    Module.finrank k (k ⊗[R] Ω[R⁄k]) = Module.rankAtStalk Ω[R⁄k] p := hb
    _ = Module.finrank R Ω[R⁄k] := by
      rw [Module.rankAtStalk_eq]
      exact p.asIdeal.finrank_fiber_eq_finrank
    _ = n := kaehler_finrank_eq_generic_basis k R K bK

end GenericRank

section Pointed

variable (k : Type*) [Field k] (S : Type*) [AddCommMonoid S]
    (hzero : ∀ a b : S,a+b=0 → a=0 ∧ b=0)
    [IsDomain (AddMonoidAlgebra k S)] [Algebra.Smooth k (AddMonoidAlgebra k S)]
    (K : Type*) [Field K] [Algebra k K] [Algebra (AddMonoidAlgebra k S) K]
    [IsScalarTower k (AddMonoidAlgebra k S) K]
    [IsFractionRing (AddMonoidAlgebra k S) K]
    {n : ℕ} (bK : Module.Basis (Fin n) K Ω[K⁄k])

include bK in
theorem pointedCotangentFiber_finrank :
    Module.finrank k (PointedCotangentFiber k S hzero) = n := by
  letI := pointedAlgebra k S hzero
  letI := pointedScalarTower k S hzero
  exact smooth_rational_cotangent_finrank k (AddMonoidAlgebra k S) K bK

include hzero bK in
theorem pointed_atoms_card_le {ι : Type*} [Fintype ι]
    (p : ι → S) (hpinj : Function.Injective p)
    (hp0 : ∀ i,p i≠0)
    (hpatom : ∀ i,∀ a b : S,a+b=p i → a=0 ∨ b=0) :
    Fintype.card ι ≤ n := by
  letI := pointedAlgebra k S hzero
  letI := pointedScalarTower k S hzero
  have hli := linearIndependent_pointedCotangentAtoms k S hzero p hpinj hp0 hpatom
  have hcard := hli.fintype_card_le_finrank
  rw [pointedCotangentFiber_finrank k S hzero K bK] at hcard
  exact hcard

end Pointed

end PaperVerification.ToricCharacters

end
-- END PaperVerification.ToricSmoothCotangentRank
end

section
-- BEGIN PaperVerification.ToricInvariantAffineAlgebras



/-!
# Actual invariant affine coordinate algebras are semigroup algebras

The exponent monoid is recovered from the characters actually contained
in a subalgebra of the Laurent algebra. Algebraic coaction stability
implies equality with its semigroup algebra. Finite type implies finite
generation of that monoid. A common actual fraction field implies that
its differences generate the whole character lattice. Normality, when
available, implies saturation by the monic equation `T^N-χ^(Nm)`.
None of these conclusions is included in the definition of the monoid.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open AddMonoidAlgebra
open scoped TensorProduct Classical

variable (k : Type*) [Field k] {M : Type*} [AddCommGroup M]

/-- The characters literally belonging to the given affine algebra. -/
def affineExponentMonoid (A : Subalgebra k (AddMonoidAlgebra k M)) : AddSubmonoid M where
  carrier := {m | single m (1 : k) ∈ A}
  zero_mem' := by
    change single (0 : M) (1 : k) ∈ A
    simpa only [AddMonoidAlgebra.one_def] using A.one_mem
  add_mem' := by
    intro m p hm hp
    change single (m+p) (1 : k) ∈ A
    simpa using A.mul_mem hm hp

@[simp] theorem mem_affineExponentMonoid
    (A : Subalgebra k (AddMonoidAlgebra k M)) (m : M) :
    m ∈ affineExponentMonoid k A ↔ single m (1 : k) ∈ A := Iff.rfl

theorem invariantAffineAlgebra_eq_semigroup
    (A : Subalgebra k (AddMonoidAlgebra k M))
    (hA : IsCharacterStable k A.toSubmodule) :
    A = monoidChartAlgebra k (affineExponentMonoid k A) := by
  apply Subalgebra.toSubmodule_injective
  rw [monoidChartAlgebra_toSubmodule]
  exact stable_eq_characterModule k A.toSubmodule hA

/-- The constructed isomorphism retains the literal character embedding
into the ambient Laurent algebra. -/
def invariantAffineSemigroupEquiv
    (A : Subalgebra k (AddMonoidAlgebra k M))
    (hA : IsCharacterStable k A.toSubmodule) :
    AddMonoidAlgebra k (affineExponentMonoid k A) ≃ₐ[k] A :=
  (monoidChartAlgebraEquiv k (affineExponentMonoid k A)).trans
    (Subalgebra.equivOfEq _ _ (invariantAffineAlgebra_eq_semigroup k A hA).symm)

@[simp] theorem invariantAffineSemigroupEquiv_single
    (A : Subalgebra k (AddMonoidAlgebra k M))
    (hA : IsCharacterStable k A.toSubmodule) (m : affineExponentMonoid k A) (r : k) :
    ((invariantAffineSemigroupEquiv k A hA (single m r) : A) : AddMonoidAlgebra k M) =
      single (m : M) r := by
  change monoidChartMap k (affineExponentMonoid k A) (single m r) = _
  exact monoidChartMap_single k _ m r

theorem affineExponentMonoid_finitelyGenerated
    (A : Subalgebra k (AddMonoidAlgebra k M))
    (hA : IsCharacterStable k A.toSubmodule) [Algebra.FiniteType k A] :
    AddMonoid.FG (affineExponentMonoid k A) := by
  letI : Algebra.FiniteType k (AddMonoidAlgebra k (affineExponentMonoid k A)) :=
    Algebra.FiniteType.equiv inferInstance (invariantAffineSemigroupEquiv k A hA).symm
  exact AddMonoidAlgebra.fg_of_finiteType (R := k)

theorem exists_finite_affine_exponent_generators
    (A : Subalgebra k (AddMonoidAlgebra k M))
    (hA : IsCharacterStable k A.toSubmodule) [Algebra.FiniteType k A] :
    ∃ S : Finset M, AddSubmonoid.closure (S : Set M) = affineExponentMonoid k A := by
  letI := affineExponentMonoid_finitelyGenerated k A hA
  exact AddSubmonoid.exists_of_isAddFG _

section Coaction

variable {R : Type*} [CommRing R] [Algebra k R]
    (f : R →ₐ[k] AddMonoidAlgebra k M)
    (δ : R →ₗ[k] AddMonoidAlgebra k M ⊗[k] R)

/-- An actual equivariant comorphism gives stability of its actual range.
The equality involves the Hopf comultiplication over all test algebras. -/
theorem range_isCharacterStable_of_coaction
    (hδ : ∀ r : R,
      Coalgebra.comul (R := k) (f r) =
        TensorProduct.map (LinearMap.id : AddMonoidAlgebra k M →ₗ[k] _)
          f.toLinearMap (δ r)) :
    IsCharacterStable k f.range.toSubmodule := by
  rintro z ⟨r, rfl⟩
  let fr : R →ₗ[k] f.range := f.rangeRestrict.toLinearMap
  refine ⟨TensorProduct.map (LinearMap.id : AddMonoidAlgebra k M →ₗ[k] _)
    fr (δ r), ?_⟩
  have hmaps :
      (TensorProduct.map (LinearMap.id : AddMonoidAlgebra k M →ₗ[k] _)
        f.range.toSubmodule.subtype).comp
          (TensorProduct.map (LinearMap.id : AddMonoidAlgebra k M →ₗ[k] _) fr) =
      TensorProduct.map (LinearMap.id : AddMonoidAlgebra k M →ₗ[k] _) f.toLinearMap := by
    ext a b
    rfl
  exact (congrArg (fun g => g (δ r)) hmaps).trans (hδ r).symm

end Coaction

section FractionField

variable (A : Subalgebra k (AddMonoidAlgebra k M))
    (hA : IsCharacterStable k A.toSubmodule)
    (K : Type*) [Field K] [Algebra (AddMonoidAlgebra k M) K]
    [Algebra A K]

/-- In this common-fraction-field interface, the scalar tower refers to
the chosen algebra map A→K, rather than the separate inherited action
of the ambient Laurent algebra on K. -/
local instance affineFractionAlgebraSMul : SMul A K :=
  (inferInstance : Algebra A K).toSMul

variable [IsScalarTower A (AddMonoidAlgebra k M) K]
    [IsFractionRing A K]
    (hinj : Function.Injective (algebraMap (AddMonoidAlgebra k M) K))

include hA hinj in
/-- Every lattice character is a quotient of characters from the actual
affine monoid. This follows from the common fraction field, not from a
generating-lattice premise attached to the affine chart. -/
theorem exists_affine_exponent_difference (m : M) :
    ∃ p ∈ affineExponentMonoid k A, ∃ q ∈ affineExponentMonoid k A, m = p-q := by
  letI : IsDomain A := Function.Injective.isDomain (algebraMap A K)
    (IsFractionRing.injective A K)
  obtain ⟨a,b,hb,hfrac⟩ := IsFractionRing.div_surjective A
    (algebraMap (AddMonoidAlgebra k M) K (single m (1:k)))
  have hb0 : (b : AddMonoidAlgebra k M) ≠ 0 := by
    intro h
    apply (mem_nonZeroDivisors_iff_ne_zero.mp hb)
    exact Subtype.ext h
  have hK0 : algebraMap A K b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hmul : single m (1:k) * (b : AddMonoidAlgebra k M) = a := by
    apply hinj
    have hbmap : algebraMap (AddMonoidAlgebra k M) K (b : AddMonoidAlgebra k M) =
        algebraMap A K b :=
      (IsScalarTower.algebraMap_apply A (AddMonoidAlgebra k M) K b).symm
    have hamap : algebraMap A K a =
        algebraMap (AddMonoidAlgebra k M) K (a : AddMonoidAlgebra k M) :=
      IsScalarTower.algebraMap_apply A (AddMonoidAlgebra k M) K a
    exact (map_mul (algebraMap (AddMonoidAlgebra k M) K)
      (single m (1:k)) (b : AddMonoidAlgebra k M)).trans
        ((congrArg (algebraMap (AddMonoidAlgebra k M) K (single m (1:k)) * ·)
          hbmap).trans (((div_eq_iff hK0).mp hfrac).symm.trans hamap))
  obtain ⟨q,hq⟩ := Finsupp.support_nonempty_iff.mpr (by
    intro hz
    apply hb0
    exact AddMonoidAlgebra.ext hz)
  have hq0 : (b : AddMonoidAlgebra k M).coeff q ≠ 0 := Finsupp.mem_support_iff.mp hq
  have hqA : q ∈ affineExponentMonoid k A :=
    single_mem_of_stable k A.toSubmodule hA b b.property q hq0
  have hp0 : (a : AddMonoidAlgebra k M).coeff (m+q) ≠ 0 := by
    rw [← hmul, AddMonoidAlgebra.coeff_single_mul_add, one_mul]
    exact hq0
  have hpA : m+q ∈ affineExponentMonoid k A :=
    single_mem_of_stable k A.toSubmodule hA a a.property (m+q) hp0
  exact ⟨m+q,hpA,q,hqA,by abel⟩

include hA hinj in
theorem affineExponentMonoid_groupClosure :
    AddSubgroup.closure (affineExponentMonoid k A : Set M) = ⊤ := by
  apply eq_top_iff.mpr
  intro m hm
  obtain ⟨p,hp,q,hq,rfl⟩ := exists_affine_exponent_difference k A hA K hinj m
  exact AddSubgroup.sub_mem _ (AddSubgroup.subset_closure hp)
    (AddSubgroup.subset_closure hq)

include hinj in
/-- Saturation is forced by integral closedness of the actual affine
coordinate ring in its actual fraction field. -/
theorem affineExponentMonoid_saturated [IsIntegrallyClosed A]
    (m : M) {N : ℕ} (hN : 0<N)
    (hm : N • m ∈ affineExponentMonoid k A) :
    m ∈ affineExponentMonoid k A := by
  let x := algebraMap (AddMonoidAlgebra k M) K (single m (1:k))
  let a : A := ⟨single (N • m) 1, hm⟩
  have hpow : x^N = algebraMap A K a := by
    change (algebraMap (AddMonoidAlgebra k M) K (single m (1:k)))^N = _
    rw [← map_pow, IsScalarTower.algebraMap_apply A (AddMonoidAlgebra k M) K]
    simp [a]
  have hx : IsIntegral A (x^N) := by
    rw [hpow]
    exact isIntegral_algebraMap
  obtain ⟨y,hy⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow hN hx
  have he : (y : AddMonoidAlgebra k M) = single m (1:k) := by
    apply hinj
    exact (IsScalarTower.algebraMap_apply A (AddMonoidAlgebra k M) K y).symm.trans hy
  change single m (1:k) ∈ A
  exact he ▸ y.property

end FractionField

end PaperVerification.ToricCharacters

end
-- END PaperVerification.ToricInvariantAffineAlgebras
end

section
-- BEGIN PaperVerification.ToricSmoothPointedSemigroup



/-!
# Smooth pointed affine toric charts have unimodular semigroups

The proof derives a primitive lattice basis directly from actual
algebraic smoothness. Minimal monoid generators give independent actual
cotangent vectors. Smoothness bounds their number by the generic rank.
The common fraction field supplies generation of the entire lattice;
the resulting integer spanning family is therefore a basis. No normality,
saturation, regular-local-ring criterion, or cone-basis conclusion is
assumed.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open PaperVerification.ToricGeometry
open KaehlerDifferential
open scoped BigOperators Classical

section BasisMonoid

variable {ι M : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup M] [Module ℤ M]

theorem closure_basis_eq_coordinateCone (b : Module.Basis ι ℤ M) :
    AddSubmonoid.closure (Set.range b) = coordinateConeMonoid b Finset.univ := by
  apply le_antisymm
  · apply AddSubmonoid.closure_le.mpr
    rintro _ ⟨i,rfl⟩
    intro j hj
    simp only [Module.Basis.repr_self,Finsupp.single_apply]
    split_ifs <;> norm_num
  · intro x hx
    have hrepr (i : ι) : 0≤b.repr x i := hx i (Finset.mem_univ i)
    have he : x = ∑ i, (b.repr x i).toNat • b i := by
      calc
        x = ∑ i, b.repr x i • b i := by
          exact (b.sum_repr x).symm.trans
            (Finset.sum_congr rfl (fun i _ =>
              int_smul_eq_zsmul (inferInstance : Module ℤ M) (b.repr x i) (b i)))
        _ = ∑ i, (b.repr x i).toNat • b i := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [← natCast_zsmul,Int.toNat_of_nonneg (hrepr i)]
    rw [he]
    exact AddSubmonoid.sum_mem _ fun i hi =>
      AddSubmonoid.nsmul_mem _ (AddSubmonoid.subset_closure (Set.mem_range_self i)) _

end BasisMonoid

section Smooth

variable (k : Type*) [Field k] {n : ℕ} (S : AddSubmonoid (Lattice n))
    (hpointed : IsPointedMonoid S) (hfg : S.FG)
    (hgroup : AddSubgroup.closure (S : Set (Lattice n))=⊤)
    [IsDomain (AddMonoidAlgebra k S)] [Algebra.Smooth k (AddMonoidAlgebra k S)]
    (K : Type*) [Field K] [Algebra k K] [Algebra (AddMonoidAlgebra k S) K]
    [IsScalarTower k (AddMonoidAlgebra k S) K]
    [IsFractionRing (AddMonoidAlgebra k S) K]
    (bK : Module.Basis (Fin n) K Ω[K⁄k])

include hpointed hfg hgroup bK in
/-- A literal smooth pointed affine semigroup chart has a genuine full
integral exponent basis. This implication is valid over every field. -/
theorem exists_unimodular_semigroup_basis :
    ∃ b : Module.Basis (Fin n) ℤ (Lattice n),
      S = coordinateConeMonoid b Finset.univ := by
  obtain ⟨G,hG,hAtoms⟩ := exists_finite_atom_generators S hpointed hfg
  have hzero : ∀ a b : S,a+b=0 → a=0 ∧ b=0 := by
    intro a b hab
    have h := hpointed a.val a.property b.val b.property
      (congrArg Subtype.val hab)
    exact ⟨Subtype.ext h.1,Subtype.ext h.2⟩
  let p : G → S := fun g => ⟨g.val,(hAtoms g.val g.property).1⟩
  have hpinj : Function.Injective p := by
    intro i j h
    apply Subtype.ext
    exact congrArg (fun s : S => (s : Lattice n)) h
  have hp0 (i : G) : p i≠0 := by
    intro h
    exact (hAtoms i.val i.property).2.1 (congrArg Subtype.val h)
  have hpatom (i : G) (a b : S) (hab : a+b=p i) : a=0 ∨ b=0 := by
    have h := (hAtoms i.val i.property).2.2 a.val a.property b.val b.property
      (congrArg Subtype.val hab)
    exact h.imp Subtype.ext Subtype.ext
  have hcard : Fintype.card G≤n :=
    pointed_atoms_card_le k S hzero K bK p hpinj hp0 hpatom
  let v : G → Lattice n := fun g => g.val
  have hspan : ⊤≤Submodule.span ℤ (Set.range v) := by
    let V := Submodule.span ℤ (Set.range v)
    have hSG : (S : Set (Lattice n)) ⊆ V := by
      intro x hx
      rw [← hG] at hx
      induction hx using AddSubmonoid.closure_induction with
      | mem x hx => exact Submodule.subset_span ⟨⟨x,hx⟩,rfl⟩
      | zero => exact V.zero_mem
      | add x y hx hy ihx ihy => exact V.add_mem ihx ihy
    have hcl : AddSubgroup.closure (S : Set (Lattice n))≤V.toAddSubgroup :=
      (AddSubgroup.closure_le _).mpr hSG
    rw [hgroup] at hcl
    exact hcl
  have hfin : Module.finrank ℤ (Lattice n)=n := by
    simpa [ToricGeometry.Lattice] using Module.finrank_eq_card_basis (Pi.basisFun ℤ (Fin n))
  have hli : LinearIndependent ℤ v :=
    linearIndependent_of_top_le_span_of_card_le_finrank hspan (hfin.symm ▸ hcard)
  let bG : Module.Basis G ℤ (Lattice n) := Module.Basis.mk hli hspan
  have hcardEq : Fintype.card G=Fintype.card (Fin n) := by
    rw [← Module.finrank_eq_card_basis bG,hfin,Fintype.card_fin]
  let e : G ≃ Fin n := Fintype.equivOfCardEq hcardEq
  let b : Module.Basis (Fin n) ℤ (Lattice n) := bG.reindex e
  have hrange : Set.range b = (G : Set (Lattice n)) := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      simpa only [b,Module.Basis.reindex_apply,bG,Module.Basis.mk_apply,v,
        Finset.mem_coe] using
        (e.symm i).property
    · intro hx
      refine ⟨e ⟨x,hx⟩,?_⟩
      simp [b,bG,v]
  refine ⟨b,?_⟩
  rw [← closure_basis_eq_coordinateCone,hrange,hG]

end Smooth

section InvariantAffine

variable (k : Type*) [Field k] {n : ℕ}
    (A : Subalgebra k (AddMonoidAlgebra k (Lattice n)))
    (hA : IsCharacterStable k A.toSubmodule)
    (hpointed : IsPointedMonoid (affineExponentMonoid k A))
    [Algebra.Smooth k A]
    (K : Type*) [Field K] [Algebra k K]
    [Algebra (AddMonoidAlgebra k (Lattice n)) K]
    [IsScalarTower k (AddMonoidAlgebra k (Lattice n)) K]
    [IsFractionRing (AddMonoidAlgebra k (Lattice n)) K]
    [Algebra A K]

/-- The common-fraction-field tower uses the chosen affine algebra map. -/
local instance invariantAffineAlgebraSMul : SMul A K :=
  (inferInstance : Algebra A K).toSMul

variable [IsScalarTower A (AddMonoidAlgebra k (Lattice n)) K]
    [IsFractionRing A K]

include hA hpointed K in
/-- A pointed invariant affine coordinate algebra of a smooth intrinsic
torus embedding is a polynomial character chart in an integral lattice
basis. The lattice-generation condition is derived from the actual
function field, and the finite-generation condition from finite type. -/
theorem smooth_invariant_affineAlgebra_eq_coordinateCone :
    ∃ b : Module.Basis (Fin n) ℤ (Lattice n),
      A = monoidChartAlgebra k (coordinateConeMonoid b Finset.univ) := by
  let S := affineExponentMonoid k A
  let e : AddMonoidAlgebra k S ≃ₐ[k] A := invariantAffineSemigroupEquiv k A hA
  letI : Algebra (AddMonoidAlgebra k S) K :=
    ((algebraMap A K).comp e.toRingEquiv.toRingHom).toAlgebra
  letI : IsScalarTower k A K := IsScalarTower.of_algebraMap_eq (by
    intro r
    exact (IsScalarTower.algebraMap_apply k
      (AddMonoidAlgebra k (Lattice n)) K r).trans
      (IsScalarTower.algebraMap_apply A
        (AddMonoidAlgebra k (Lattice n)) K (algebraMap k A r)).symm)
  letI : IsScalarTower k (AddMonoidAlgebra k S) K :=
    IsScalarTower.of_algebraMap_eq (by
      intro r
      change algebraMap k K r = algebraMap A K (e (algebraMap k (AddMonoidAlgebra k S) r))
      rw [e.commutes,← IsScalarTower.algebraMap_apply k A K])
  letI : IsFractionRing (AddMonoidAlgebra k S) K :=
    IsFractionRing.of_ringEquiv_left e.toRingEquiv (fun _=>rfl)
  letI : IsDomain (AddMonoidAlgebra k S) :=
    Function.Injective.isDomain (algebraMap (AddMonoidAlgebra k S) K)
      (IsFractionRing.injective (AddMonoidAlgebra k S) K)
  letI : Algebra.Smooth k (AddMonoidAlgebra k S) := Algebra.Smooth.of_equiv e.symm
  have hfg : S.FG := affineExponentMonoid_finitelyGenerated k A hA
  have hgroup : AddSubgroup.closure (S : Set (Lattice n))=⊤ :=
    affineExponentMonoid_groupClosure k A hA K
      (IsFractionRing.injective (AddMonoidAlgebra k (Lattice n)) K)
  let bK : Module.Basis (Fin n) K Ω[K⁄k] :=
    fractionLogDifferentialBasis k K (Pi.basisFun ℤ (Fin n))
  obtain ⟨b,hb⟩ := exists_unimodular_semigroup_basis k S hpointed hfg hgroup K bK
  exact ⟨b,(invariantAffineAlgebra_eq_semigroup k A hA).trans (congrArg (monoidChartAlgebra k) hb)⟩

end InvariantAffine

end PaperVerification.ToricCharacters

end
-- END PaperVerification.ToricSmoothPointedSemigroup
end

section
-- BEGIN PaperVerification.ToricFaceInheritance
/-!
# Face coordinates for smooth lattice polytopes

The coordinate support of a face is determined by the incident edge rays that
remain in that face. This gives a coordinate sublattice of an actual integral
basis, hence a saturated lattice, without assuming a face-inheritance theorem.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical
open Set
open PaperVerification.ToricExchange

section AffineCoordinates

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

theorem affine_apply_add_smul (f : E →ᵃ[ℝ] ℝ) (v w : E) (a : ℝ) :
    f (v + a • w) = f v + a * f.linear w := by
  rw [add_comm]
  change f ((a • w) +ᵥ v) = _
  rw [AffineMap.map_vadd]
  simp [map_smul, vadd_eq_add, smul_eq_mul, add_comm]

theorem affine_apply_basis_coordinates (f : E →ᵃ[ℝ] ℝ)
    (b : Module.Basis ι ℝ E) (v x : E) :
    f x = f v + ∑ i, b.repr (x - v) i * f.linear (b i) := by
  have hx : x = (∑ i, b.repr (x - v) i • b i) +ᵥ v := by
    rw [b.sum_repr]
    simp
  calc
    f x = f ((∑ i, b.repr (x - v) i • b i) +ᵥ v) := congrArg f hx
    _ = _ := by
      rw [AffineMap.map_vadd]
      simp [map_sum, map_smul, vadd_eq_add, smul_eq_mul, add_comm]

/-- A positive basis coordinate of a point on a face forces that edge ray
to remain in the same face. The proof uses actual affine slacks and their
nonnegative weighted sum, rather than a combinatorial face assumption. -/
theorem positive_coordinate_endpoint_mem_face {κ : Type*}
    (H : AffineInequalities κ E) (J : Set κ)
    (b : Module.Basis ι ℝ E) (v : E) (hv : v ∈ H.face J)
    (lengths : ι → ℝ) (hlength : ∀ i, 0 < lengths i)
    (hedges : ∀ i, v + lengths i • b i ∈ H.region)
    (hcone : ∀ x ∈ H.region, ∀ i, 0 ≤ b.repr (x - v) i)
    (x : E) (hx : x ∈ H.face J) (i : ι) (hi : 0 < b.repr (x - v) i) :
    v + lengths i • b i ∈ H.face J := by
  refine ⟨hedges i, ?_⟩
  intro k hk
  have hv0 : H.slack k v = 0 := hv.2 k hk
  have hx0 : H.slack k x = 0 := hx.2 k hk
  have hcoef (j : ι) : 0 ≤ (H.slack k).linear (b j) := by
    have hj := hedges j k
    rw [affine_apply_add_smul, hv0, zero_add] at hj
    exact nonneg_of_mul_nonneg_right hj (hlength j)
  have hterms (j : ι) :
      0 ≤ b.repr (x - v) j * (H.slack k).linear (b j) :=
    mul_nonneg (hcone x hx.1 j) (hcoef j)
  have hsum : (∑ j, b.repr (x - v) j * (H.slack k).linear (b j)) = 0 := by
    have h := affine_apply_basis_coordinates (H.slack k) b v x
    rw [hv0, hx0, zero_add] at h
    exact h.symm
  have hle : b.repr (x - v) i * (H.slack k).linear (b i) ≤ 0 := by
    have h := Finset.single_le_sum (f := fun j =>
      b.repr (x - v) j * (H.slack k).linear (b j)) (fun j _ => hterms j)
      (Finset.mem_univ i)
    rwa [hsum] at h
  have hzero := le_antisymm hle (hterms i)
  have hlin : (H.slack k).linear (b i) = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hi.ne'
  rw [affine_apply_add_smul, hv0, hlin, mul_zero, add_zero]

end AffineCoordinates

/-- The origin together with one nonzero point on every coordinate axis
affinely spans the full coordinate space, including dimension zero. -/
theorem affineSpan_eq_top_of_scaled_axes {d : ℕ} (S : Set (Ambient d))
    (hzero : (0 : Ambient d) ∈ S) (lengths : Fin d → ℝ)
    (hlength : ∀ i, lengths i ≠ 0)
    (haxes : ∀ i, lengths i • Pi.basisFun ℝ (Fin d) i ∈ S) :
    affineSpan ℝ S = ⊤ := by
  have hspan : Submodule.span ℝ S = ⊤ := by
    apply top_unique
    rw [← (Pi.basisFun ℝ (Fin d)).span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have hi := (Submodule.span ℝ S).smul_mem (lengths i)⁻¹
      (Submodule.subset_span (haxes i))
    simpa [smul_smul, hlength i] using hi
  rw [affineSpan_eq_span_of_zero_mem (subset_affineSpan ℝ S hzero)]
  rw [hspan] <;> rfl

/-- Indices of the incident basis directions whose endpoints lie on a specified face. -/
def faceEdgeIndices {n : ℕ} (F : Set (Ambient n)) (v : Ambient n)
    (b : Module.Basis (Fin n) ℝ (Ambient n)) (lengths : Fin n → ℝ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => v + lengths i • b i ∈ F)

@[simp] theorem mem_faceEdgeIndices {n : ℕ} (F : Set (Ambient n)) (v : Ambient n)
    (b : Module.Basis (Fin n) ℝ (Ambient n)) (lengths : Fin n → ℝ) (i : Fin n) :
    i ∈ faceEdgeIndices F v b lengths ↔ v + lengths i • b i ∈ F := by
  classical
  simp [faceEdgeIndices]

/-- An actual nonempty face in a supporting basis orthant is exactly the
coordinate section obtained by setting its omitted edge coordinates to zero. -/
theorem face_eq_coordinate_section {n : ℕ} {κ : Type*} [Finite κ]
    (H : AffineInequalities κ (Ambient n)) (F : Set (Ambient n))
    (hFconv : Convex ℝ F) (hF : IsExtreme ℝ H.region F)
    (b : Module.Basis (Fin n) ℝ (Ambient n)) (v : Ambient n) (hv : v ∈ F)
    (lengths : Fin n → ℝ) (hlength : ∀ i, 0 < lengths i)
    (hedges : ∀ i, v + lengths i • b i ∈ H.region)
    (hcone : ∀ x ∈ H.region, ∀ i, 0 ≤ b.repr (x - v) i) :
    F = {x ∈ H.region | ∀ i ∉ faceEdgeIndices F v b lengths,
      b.repr (x - v) i = 0} := by
  classical
  obtain ⟨z, hz, hFeq⟩ := H.exists_activeFace_eq hFconv hF ⟨v, hv⟩
  let J := H.jointZeros z z
  have hvJ : v ∈ H.face J := by simpa only [hFeq] using hv
  ext x
  constructor
  · intro hx
    refine ⟨hF.subset hx, ?_⟩
    intro i hi
    have hnonneg := hcone x (hF.subset hx) i
    by_contra hne
    have hpos : 0 < b.repr (x - v) i := lt_of_le_of_ne hnonneg (Ne.symm hne)
    have hxJ : x ∈ H.face J := by simpa only [hFeq] using hx
    have hiJ := positive_coordinate_endpoint_mem_face H J b v hvJ lengths hlength
      hedges hcone x hxJ i hpos
    apply hi
    apply (mem_faceEdgeIndices F v b lengths i).mpr
    simpa only [hFeq] using hiJ
  · rintro ⟨hxP, hxzero⟩
    rw [hFeq]
    refine ⟨hxP, ?_⟩
    intro k hk
    have hv0 : H.slack k v = 0 := hvJ.2 k hk
    have hterm (i : Fin n) :
        b.repr (x - v) i * (H.slack k).linear (b i) = 0 := by
      by_cases hi : i ∈ faceEdgeIndices F v b lengths
      · have hwi : v + lengths i • b i ∈ H.face J := by
          have hiF := (mem_faceEdgeIndices F v b lengths i).mp hi
          simpa only [hFeq] using hiF
        have hzero := hwi.2 k hk
        rw [affine_apply_add_smul, hv0, zero_add] at hzero
        have hlin := (mul_eq_zero.mp hzero).resolve_left (hlength i).ne'
        rw [hlin, mul_zero]
      · rw [hxzero i hi, zero_mul]
    rw [affine_apply_basis_coordinates (H.slack k) b v x, hv0]
    simp only [hterm, Finset.sum_const_zero, add_zero]

namespace LatticePolytope

variable {n : ℕ} (P : LatticePolytope n)

/-- A convex face is generated by the original integral generators it contains. -/
theorem face_eq_hull_lattice_filter (F : Set (Ambient n))
    (hFconv : Convex ℝ F) (hF : IsExtreme ℝ P.carrier F) :
    F = convexHull ℝ ((embed n) ''
      ((P.generators.filter fun z => embed n z ∈ F) : Set (Lattice n))) := by
  classical
  let s := P.generators.image (embed n)
  have hs : convexHull ℝ (s : Set (Ambient n)) = P.carrier := by
    simp [s, carrier, Finset.coe_image]
  have h := convex_face_eq_convexHull_filter s F hFconv (by simpa only [hs] using hF)
  calc
    F = convexHull ℝ (faceGenerators s F : Set (Ambient n)) := h
    _ = _ := by
      congr 1
      ext x
      simp only [faceGenerators, Finset.mem_coe, Finset.mem_filter, Finset.mem_image,
        Set.mem_image, s]
      constructor
      · rintro ⟨⟨z, hz, rfl⟩, hx⟩
        exact ⟨z, ⟨hz, hx⟩, rfl⟩
      · rintro ⟨z, ⟨hz, hx⟩, rfl⟩
        exact ⟨⟨z, hz, rfl⟩, hx⟩

/-- Every nonempty actual convex face has an actual vertex. -/
theorem face_vertices_nonempty (F : Set (Ambient n))
    (hFconv : Convex ℝ F) (hF : IsExtreme ℝ P.carrier F) (hFne : F.Nonempty) :
    (F.extremePoints ℝ).Nonempty := by
  have hcompact : IsCompact F := by
    rw [P.face_eq_hull_lattice_filter F hFconv hF]
    exact ((P.generators.filter fun z => embed n z ∈ F).finite_toSet.image
      (embed n)).isCompact_convexHull ℝ
  exact hcompact.extremePoints_nonempty hFne

/-- Supporting basis coordinates follow from the complete list of actual
incident edges. This form retains a specified primitive basis. -/
theorem basis_cone_of_incident_edges (v : Ambient n)
    (hv : v ∈ P.carrier.extremePoints ℝ) (vZ : Lattice n)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (lengths : Fin n → ℕ)
    (hvZ : embed n vZ = v)
    (hall : ∀ w, P.IsEdge v w →
      ∃ i, w = embed n (vZ + (lengths i : ℤ) • b i)) :
    ∀ x ∈ P.carrier, ∀ i, 0 ≤ (integralBasisReal b).repr (x - v) i := by
  classical
  let s := P.generators.image (embed n)
  have hs : convexHull ℝ (s : Set (Ambient n)) = P.carrier := by
    simp [s, carrier, Finset.coe_image]
  have hv' : v ∈ (convexHull ℝ (s : Set (Ambient n))).extremePoints ℝ := by
    simpa only [hs] using hv
  have hedgeRay : ∀ w : Ambient n, v ≠ w →
      IsExtreme ℝ (convexHull ℝ (s : Set (Ambient n))) (segment ℝ v w) →
      ∃ i : Fin n, ∃ a : ℝ, 0 ≤ a ∧ w - v = a • integralBasisReal b i := by
    intro w hvw hface
    obtain ⟨i, rfl⟩ := hall w ⟨hvw, by simpa only [hs] using hface⟩
    refine ⟨i, (lengths i : ℝ), Nat.cast_nonneg _, ?_⟩
    rw [map_add, hvZ, integralBasisReal_apply, add_sub_cancel_left]
    ext j
    simp [embed, Int.cast_mul]
  have h := PaperVerification.ToricVertexCone.nonnegative_basis_coordinates_of_incident_edges
    s v hv' (integralBasisReal b) hedgeRay
  simpa only [hs] using h

/-- Every face, at every one of its vertices, has saturated integral coordinates
in which its complete incident edge family consists of the standard coordinate
axes. Its coordinate polytope is full dimensional; a proper face has strictly
smaller dimension. No face-smoothness theorem is assumed. -/
theorem exists_face_chart_at_vertex (hP : P.Smooth)
    (F : Set (Ambient n)) (hFconv : Convex ℝ F)
    (hF : IsExtreme ℝ P.carrier F) (v : Ambient n)
    (hv : v ∈ F.extremePoints ℝ) :
    ∃ (d : ℕ) (Q : LatticePolytope d) (e : IntegralAffineEmbedding d n)
      (lengths : Fin d → ℕ),
      d ≤ n ∧ (F ≠ P.carrier → d < n) ∧
      e.realMap 0 = v ∧ e.realMap '' Q.carrier = F ∧
      (∀ i, 0 < lengths i ∧ Q.IsEdge 0
        (embed d ((lengths i : ℤ) • Pi.basisFun ℤ (Fin d) i))) ∧
      (∀ w, Q.IsEdge 0 w → ∃ i,
        w = embed d ((lengths i : ℤ) • Pi.basisFun ℤ (Fin d) i)) := by
  classical
  have hvP := hF.extremePoints_subset_extremePoints hv
  obtain ⟨vZ, b, lengths, hvZ, hedges, hall⟩ := hP v hvP
  let bR := integralBasisReal b
  let lR : Fin n → ℝ := fun i => lengths i
  have hlR (i : Fin n) : 0 < lR i := by
    change (0 : ℝ) < (lengths i : ℝ)
    exact_mod_cast (hedges i).1
  have hendpoint (i : Fin n) :
      embed n (vZ + (lengths i : ℤ) • b i) = v + lR i • bR i := by
    rw [map_add, hvZ]
    ext j
    simp [lR, bR, integralBasisReal_apply, embed, Int.cast_mul]
  have hcone := P.basis_cone_of_incident_edges v hvP vZ b lengths hvZ hall
  obtain ⟨κ, hκ, H, hHP⟩ := P.hasFiniteHalfspaces
  letI := hκ
  let I := faceEdgeIndices F v bR lR
  have hsection : F = {x ∈ P.carrier | ∀ i ∉ I, bR.repr (x - v) i = 0} := by
    have h := face_eq_coordinate_section H F hFconv
      (by simpa only [← hHP] using hF) bR v hv.1 lR hlR
      (fun i => by
        rw [← hHP, ← hendpoint]
        exact (P.edge_endpoints_extreme (hedges i).2).2.1)
      (by simpa only [← hHP] using hcone)
    simpa only [← hHP, I] using h
  let d := I.card
  let a : Fin d ↪ Fin n := (I.orderEmbOfFin rfl).toEmbedding
  have harange : Set.range a = (I : Set (Fin n)) := by
    exact Finset.range_orderEmbOfFin I rfl
  have haI (i : Fin d) : a i ∈ I := by
    change a i ∈ (I : Set (Fin n))
    rw [← harange]
    exact Set.mem_range_self i
  let e := selectedBasisChart vZ b a
  let proj : Lattice n → Lattice d := fun z i => b.repr (z - vZ) (a i)
  let S := P.generators.filter (fun z => embed n z ∈ F)
  let qgens := S.image proj
  let Qset := convexHull ℝ ((embed d) '' (qgens : Set (Lattice d)))
  have hcoord (x : Ambient n) (hx : x ∈ F) :
      ∀ j ∉ Set.range a, bR.repr (x - v) j = 0 := by
    have hx' : x ∈ {x ∈ P.carrier | ∀ i ∉ I, bR.repr (x - v) i = 0} := by
      rwa [← hsection]
    intro j hj
    exact hx'.2 j (by simpa only [harange, Finset.mem_coe] using hj)
  have hreconstruct (z : Lattice n) (hz : embed n z ∈ F) : e.latticeMap (proj z) = z := by
    have hz0 (j : Fin n) (hj : j ∉ Set.range a) : b.repr (z - vZ) j = 0 := by
      have h := hcoord (embed n z) hz j hj
      rw [← hvZ, ← map_sub, integralBasisReal_repr] at h
      exact Int.cast_eq_zero.mp h
    change vZ + selectedBasisMap b a (fun i => b.repr (z - vZ) (a i)) = z
    rw [selectedBasisMap_repr_restrict b a (z - vZ) hz0]
    abel
  have hgenimage : e.realMap '' ((embed d) '' (qgens : Set (Lattice d))) =
      (embed n) '' (S : Set (Lattice n)) := by
    ext x
    constructor
    · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hq
      rw [← e.embed_latticeMap, hreconstruct z (Finset.mem_filter.mp hz).2]
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨embed d (proj z), ⟨proj z, Finset.mem_image.mpr ⟨z, hz, rfl⟩, rfl⟩, ?_⟩
      rw [← e.embed_latticeMap, hreconstruct z (Finset.mem_filter.mp hz).2]
  have himage : e.realMap '' Qset = F := by
    rw [e.realMap.image_convexHull, hgenimage]
    exact (P.face_eq_hull_lattice_filter F hFconv hF).symm
  have hezero : e.realMap 0 = v := by
    simp only [e, selectedBasisChart_realMap, Pi.zero_apply, zero_smul,
      Finset.sum_const_zero, add_zero, hvZ]
  have hmem (x : Ambient d) : x ∈ Qset ↔ e.realMap x ∈ F := by
    rw [← himage]
    exact e.realMap_injective.mem_set_image.symm
  have hzero : (0 : Ambient d) ∈ Qset := (hmem 0).mpr (hezero.symm ▸ hv.1)
  have heaxis (i : Fin d) : e.realMap
      ((lengths (a i) : ℝ) • Pi.basisFun ℝ (Fin d) i) =
        embed n (vZ + (lengths (a i) : ℤ) • b (a i)) := by
    change embed n vZ + selectedBasisMap bR a
      ((lengths (a i) : ℝ) • Pi.basisFun ℝ (Fin d) i) = _
    rw [map_smul]
    have hsingle : selectedBasisMap bR a (Pi.basisFun ℝ (Fin d) i) = bR (a i) := by
      simpa only [Pi.basisFun_apply, selectedBasisMap_single, one_smul]
        using selectedBasisMap_single bR a i (1 : ℝ)
    rw [hsingle, hvZ, hendpoint]
  have haxes (i : Fin d) :
      (lengths (a i) : ℝ) • Pi.basisFun ℝ (Fin d) i ∈ Qset := by
    apply (hmem _).mpr
    rw [heaxis, hendpoint]
    exact (mem_faceEdgeIndices F v bR lR (a i)).mp (haI i)
  have hfull : affineSpan ℝ Qset = ⊤ :=
    affineSpan_eq_top_of_scaled_axes Qset hzero (fun i => lengths (a i))
      (fun i => (hlR (a i)).ne') haxes
  have hqne : qgens.Nonempty := by
    obtain ⟨x, hx⟩ := convexHull_nonempty_iff.mp ⟨0, hzero⟩
    obtain ⟨q, hq, rfl⟩ := hx
    exact ⟨q, hq⟩
  let Q : LatticePolytope d := ⟨qgens, hqne, hfull⟩
  have hQset : Q.carrier = Qset := rfl
  have hd : d ≤ n := by
    calc
      d = I.card := rfl
      _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ I)
      _ = n := Finset.card_fin n
  have hdstrict (hproper : F ≠ P.carrier) : d < n := by
    apply lt_of_le_of_ne hd
    intro hdn
    have hI : I = Finset.univ := Finset.eq_of_subset_of_card_le (Finset.subset_univ I)
      (by simpa only [Finset.card_fin, ← hdn] using (le_rfl : I.card ≤ I.card))
    apply hproper
    rw [hsection, hI]
    simp
  have heembedaxis (i : Fin d) :
      e.realMap (embed d ((lengths (a i) : ℤ) • Pi.basisFun ℤ (Fin d) i)) =
      embed n (vZ + (lengths (a i) : ℤ) • b (a i)) := by
    rw [← e.embed_latticeMap]
    congr 1
    change vZ + selectedBasisMap b a
      ((lengths (a i) : ℤ) • Pi.basisFun ℤ (Fin d) i) = _
    rw [map_smul]
    have hs : selectedBasisMap b a (Pi.basisFun ℤ (Fin d) i) = b (a i) := by
      simpa only [Pi.basisFun_apply, selectedBasisMap_single, one_smul]
        using selectedBasisMap_single b a i (1 : ℤ)
    rw [hs]
  refine ⟨d, Q, e, fun i => lengths (a i), hd, hdstrict, hezero, himage, ?_, ?_⟩
  · intro i
    refine ⟨(hedges (a i)).1, ?_, ?_⟩
    · intro heq
      have h := congrArg e.realMap heq
      rw [hezero, heembedaxis] at h
      exact (hedges (a i)).2.1 h
    · apply (affine_isExtreme_image_iff e.realMap e.realMap_injective _ _).mp
      rw [hQset, himage, image_segment, hezero, heembedaxis]
      apply (hedges (a i)).2.2.mono hF.subset
      apply hFconv.segment_subset hv.1
      rw [hendpoint]
      exact (mem_faceEdgeIndices F v bR lR (a i)).mp (haI i)
  · intro w hw
    have hwF : e.realMap w ∈ F := by
      rw [← himage]
      exact ⟨w, (Q.edge_endpoints_extreme hw).2.1, rfl⟩
    have hedgeP : P.IsEdge v (e.realMap w) := by
      refine ⟨?_, ?_⟩
      · intro h
        apply hw.1
        apply e.realMap_injective
        simpa only [hezero] using h
      · have h := affine_isExtreme_image e.realMap e.realMap_injective hw.2
        rw [hQset, himage, image_segment, hezero] at h
        exact hF.trans h
    obtain ⟨j, hj⟩ := hall (e.realMap w) hedgeP
    have hjI : j ∈ I := by
      apply (mem_faceEdgeIndices F v bR lR j).mpr
      rw [← hendpoint, ← hj]
      exact hwF
    have hjrange : j ∈ Set.range a := by rwa [harange]
    obtain ⟨i, rfl⟩ := hjrange
    refine ⟨i, e.realMap_injective ?_⟩
    rw [heembedaxis]
    exact hj

end LatticePolytope

end PaperVerification.ToricGeometry
end
-- END PaperVerification.ToricFaceInheritance
end

section
-- BEGIN PaperVerification.ToricSemigroupPolytopes



/-!
# Primitive affine semigroup charts reconstruct the actual smooth polytope

The input semigroups are the additive closures of literal weight
differences. Their basis descriptions give supporting orthants and
positive points on every coordinate ray of the actual convex hull.
Every incident edge is then proved to be a coordinate edge using its
actual minimal face. This supplies the ordinary polytope smoothness
predicate and its complete normal fan, without inserting an edge or
fan correspondence as an assumption.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open PaperVerification.ToricCharacters PaperVerification.ToricExchange
open PaperVerification.ToricVertexCone
open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] {n : ℕ}

theorem positive_axis_point_of_differenceMonoid (a : ι → Lattice n) (j : ι)
    (z : Lattice n) (hz : z∈differenceWeightMonoid a j) (hz0 : z≠0) :
    ∃ ε : ℝ,0<ε ∧ embed n (a j)+ε • embed n z∈
      convexHull ℝ (Set.range (fun i=>embed n (a i))) := by
  obtain ⟨c,hc⟩ := AddSubmonoid.exists_of_mem_closure_range
    (fun i=>a i-a j) z hz
  let N : ℕ := ∑ i,c i
  have hN : 0<N := by
    by_contra h
    have hzero : N=0 := Nat.eq_zero_of_le_zero (le_of_not_gt h)
    have hci : ∀ i,c i=0 := fun i=>
      (Finset.sum_eq_zero_iff.mp hzero) i (Finset.mem_univ i)
    exact hz0 (by simpa [hci] using hc)
  have hNR : (0 : ℝ)<N := by exact_mod_cast hN
  let w : ι → ℝ := fun i=>(c i : ℝ)/(N : ℝ)
  have hw0 (i : ι) : 0≤w i := div_nonneg (Nat.cast_nonneg _) hNR.le
  have hw1 : ∑ i,w i=1 := by
    simp only [w,← Finset.sum_div,← Nat.cast_sum,show ∑ i,c i=N from rfl]
    exact div_self hNR.ne'
  have hcR : embed n z=∑ i,(c i : ℝ) • (embed n (a i)-embed n (a j)) := by
    simpa only [map_sum,map_nsmul,map_sub,Nat.cast_smul_eq_nsmul] using congrArg (embed n) hc
  have hcomb : ∑ i,w i • embed n (a i)=
      embed n (a j)+(N : ℝ)⁻¹ • embed n z := by
    have hNcast : ∑ i,(c i : ℝ)=(N : ℝ) := by simp [N]
    rw [hcR,Finset.smul_sum]
    simp only [smul_sub,Finset.sum_sub_distrib,smul_smul]
    rw [← Finset.sum_smul]
    have hsum : ∑ i,(N : ℝ)⁻¹*(c i : ℝ)=1 := by
      rw [← Finset.mul_sum,hNcast,inv_mul_cancel₀ hNR.ne']
    rw [hsum,one_smul]
    simp only [w,div_eq_mul_inv,mul_comm]
    module
  refine ⟨(N : ℝ)⁻¹,inv_pos.mpr hNR,?_⟩
  rw [← hcomb]
  exact mem_convexHull_of_exists_fintype w (fun i=>embed n (a i)) hw0 hw1
    (fun i=>Set.mem_range_self i) rfl

theorem affineSpan_eq_top_of_difference_basis (a : ι → Lattice n) (j : ι)
    (b : Module.Basis (Fin n) ℤ (Lattice n))
    (hb : ∀ i,b i∈differenceWeightMonoid a j) :
    affineSpan ℝ (convexHull ℝ (Set.range (fun i=>embed n (a i))))=⊤ := by
  let P := convexHull ℝ (Set.range (fun i=>embed n (a i)))
  let A := affineSpan ℝ P
  have hv : embed n (a j)∈A :=
    subset_affineSpan ℝ _ (subset_convexHull ℝ _ (Set.mem_range_self j))
  have hdir (i : Fin n) : integralBasisReal b i∈A.direction := by
    obtain ⟨ε,hε,hpoint⟩ := positive_axis_point_of_differenceMonoid a j (b i) (hb i)
      (b.ne_zero i)
    have h := AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ _ hpoint) hv
    have h' : ε • integralBasisReal b i∈A.direction := by
      simpa only [vsub_eq_sub,add_sub_cancel_left,integralBasisReal_apply] using h
    simpa only [smul_smul,inv_mul_cancel₀ hε.ne',one_smul] using
      A.direction.smul_mem ε⁻¹ h'
  have hall (x : Ambient n) : x∈A.direction := by
    rw [← (integralBasisReal b).sum_repr x]
    exact Submodule.sum_mem _ (fun i hi=>A.direction.smul_mem _ (hdir i))
  apply top_unique
  intro x hx
  simpa only [vadd_eq_add,sub_add_cancel] using
    AffineSubspace.vadd_mem_of_mem_direction (hall (x-embed n (a j))) hv

theorem hull_orthant_of_difference_basis (a : ι → Lattice n) (j : ι)
    (b : Module.Basis (Fin n) ℤ (Lattice n))
    (hS : differenceWeightMonoid a j=coordinateConeMonoid b Finset.univ) :
    ∀ x∈convexHull ℝ (Set.range (fun i=>embed n (a i))),∀ l,
      0≤(integralBasisReal b).repr (x-embed n (a j)) l := by
  intro x hx l
  let f := (integralBasisReal b).coord l
  have hgen (i : ι) : f (embed n (a j))≤f (embed n (a i)) := by
    have hi : a i-a j∈coordinateConeMonoid b Finset.univ := hS ▸
      AddSubmonoid.subset_closure (Set.mem_range_self i)
    have hcoord : 0≤b.repr (a i-a j) l := hi l (Finset.mem_univ l)
    have hreal : 0≤(integralBasisReal b).repr
        (embed n (a i)-embed n (a j)) l := by
      rw [← map_sub,integralBasisReal_repr]
      exact_mod_cast hcoord
    simpa only [f,Module.Basis.coord_apply,map_sub,Finsupp.sub_apply,sub_nonneg] using hreal
  have hbound : f (embed n (a j))≤f x :=
    convexHull_min (by rintro _ ⟨i,rfl⟩;exact hgen i)
      ((convex_Ici (f (embed n (a j)))).linear_preimage f) hx
  simpa only [f,Module.Basis.coord_apply,map_sub,Finsupp.sub_apply,sub_nonneg] using hbound

namespace LatticePolytope

variable (P : LatticePolytope n)

/-- Orthant coordinates plus genuine positive feasible axis points
exhaust all incident edges of an actual polytope. -/
theorem edge_has_coordinate_direction_of_orthant_axes (v : Ambient n)
    (b : Module.Basis (Fin n) ℝ (Ambient n))
    (horthant : ∀ x∈P.carrier,∀ j,0≤b.repr (x-v) j)
    (haxes : ∀ i,∃ ε : ℝ,0<ε ∧ v+ε • b i∈P.carrier)
    (w : Ambient n) (hedge : P.IsEdge v w) :
    ∃ i,w∈P.coordinateRayFace v b i := by
  obtain ⟨κ,hκ,H,hPH⟩ := P.hasFiniteHalfspaces
  letI := hκ
  obtain ⟨hv,hw⟩ := P.edge_endpoints_extreme hedge
  have hpositive : ∃ i,0<b.repr (w-v) i := by
    by_contra hn
    push_neg at hn
    apply hedge.1
    apply b.ext_elem
    intro i
    have hz := le_antisymm (hn i) (horthant w hw.1 i)
    have he : b.repr w i=b.repr v i := by
      simpa only [map_sub,Finsupp.sub_apply,sub_eq_zero] using hz
    exact he.symm
  obtain ⟨i,hi⟩ := hpositive
  choose ε hε hεP using haxes
  have hvF : v∈H.face (H.jointZeros v w) := by
    exact ⟨hPH ▸ hv.1,fun k hk=>hk.1⟩
  have hwF : w∈H.face (H.jointZeros v w) := by
    exact ⟨hPH ▸ hw.1,fun k hk=>hk.2⟩
  have hzF := positive_coordinate_endpoint_mem_face H (H.jointZeros v w)
    b v hvF ε hε (fun j=>hPH ▸ hεP j)
    (fun x hx=>horthant x (hPH.symm ▸ hx)) w hwF i hi
  have hmin := H.jointFace_minimal (hPH ▸ hv.1) (hPH ▸ hw.1)
    (convex_segment v w) (by simpa only [← hPH] using hedge.2)
    (left_mem_segment ℝ v w) (right_mem_segment ℝ v w)
  obtain ⟨r,t,hr,ht,hrt,hline⟩ := hmin hzF
  have hcoords (j : Fin n) :
      ε i*(if i=j then 1 else 0)=t*b.repr (w-v) j := by
    have he := congrArg (fun x=>b.repr x j) hline
    simp only [map_add,map_smul,Finsupp.add_apply,Finsupp.smul_apply,
      Module.Basis.repr_self_apply,smul_eq_mul] at he
    simp only [map_sub,Finsupp.sub_apply]
    have hrtj := congrArg (fun s : ℝ=>s * (b.repr v) j) hrt
    nlinarith only [he,hrtj]
  have htne : t≠0 := by
    intro h
    exact (hε i).ne' (by simpa [h] using hcoords i)
  refine ⟨i,hw.1,?_⟩
  intro j hji
  have h := hcoords j
  rw [if_neg (Ne.symm hji),mul_zero] at h
  exact (mul_eq_zero.mp h.symm).resolve_left htne

theorem smooth_of_vertex_orthants_and_axes
    (hlocal : ∀ v∈P.carrier.extremePoints ℝ,
      ∃ (vZ : Lattice n) (b : Module.Basis (Fin n) ℤ (Lattice n)),
        vZ∈P.generators ∧ embed n vZ=v ∧
        (∀ x∈P.carrier,∀ i,0≤(integralBasisReal b).repr (x-v) i) ∧
        (∀ i,∃ ε : ℝ,0<ε ∧ v+ε • integralBasisReal b i∈P.carrier)) : P.Smooth := by
  intro v hv
  obtain ⟨vZ,b,hvZ,rfl,horthant,haxes⟩ := hlocal v hv
  choose lengths hlengths using fun i=>P.coordinateRayFace_eq_integral_edge
    vZ hvZ b horthant i (haxes i)
  refine ⟨vZ,b,lengths,rfl,fun i=>⟨(hlengths i).1,(hlengths i).2.1⟩,?_⟩
  intro w hw
  obtain ⟨i,hi⟩ := P.edge_has_coordinate_direction_of_orthant_axes
    (embed n vZ) (integralBasisReal b) horthant haxes w hw
  have hwseg := (hlengths i).2.2 ▸ hi
  have hverts := P.edge_endpoints_extreme hw
  have hend := (P.edge_endpoints_extreme (hlengths i).2.1).2.1
  rcases (mem_extremePoints_iff_forall_segment.mp hverts.2).2
    _ hverts.1.1 _ hend hwseg with hvw|hew
  · exact (hw.1 hvw).elim
  · exact ⟨i,hew.symm⟩

end LatticePolytope

/-- Literal basis semigroups at all actual vertex charts reconstruct the
actual finite convex hull as a smooth full-dimensional lattice polytope. -/
theorem exists_smooth_polytope_of_vertex_semigroups [Nonempty ι]
    (a : ι → Lattice n)
    (hlocal : ∀ j : vertexWeightIndices a,
      ∃ b : Module.Basis (Fin n) ℤ (Lattice n),
        differenceWeightMonoid a j.val=coordinateConeMonoid b Finset.univ) :
    ∃ P : LatticePolytope n,
      P.carrier=convexHull ℝ (Set.range (fun i=>embed n (a i))) ∧ P.Smooth := by
  have hverts : (vertexWeightIndices a : Set ι).Nonempty := by
    by_contra h
    have hempty : vertexWeightIndices a=∅ := Finset.eq_empty_iff_forall_notMem.mpr
      (fun i hi=>h ⟨i,hi⟩)
    have hH := hull_vertexWeightIndices a
    have hzero : convexHull ℝ (Set.range (fun i : vertexWeightIndices a=>embed n (a i.val)))=∅ := by
      haveI : IsEmpty (vertexWeightIndices a) := ⟨fun i=>by simpa [hempty] using i.property⟩
      simp only [Set.range_eq_empty,convexHull_empty]
    have hmem := subset_convexHull ℝ (Set.range (fun i=>embed n (a i)))
      (Set.mem_range_self (Classical.arbitrary ι))
    rw [← hH,hzero] at hmem
    exact hmem
  obtain ⟨j,hj⟩ := hverts
  obtain ⟨b,hb⟩ := hlocal ⟨j,hj⟩
  have hfull : affineSpan ℝ
      (convexHull ℝ (Set.range (fun i=>embed n (a i))))=⊤ :=
    affineSpan_eq_top_of_difference_basis a j b (fun i=>by
      rw [hb]
      intro l hl
      simp only [Module.Basis.repr_self_apply]
      split_ifs <;> norm_num)
  let P : LatticePolytope n :=
    { generators := Finset.univ.image a
      nonempty := ⟨a j,Finset.mem_image.mpr ⟨j,Finset.mem_univ j,rfl⟩⟩
      fullDimensional := by
        simpa only [Finset.coe_image,Finset.coe_univ,Set.image_univ,← Set.range_comp'] using hfull }
  have hcarrier : P.carrier=convexHull ℝ (Set.range (fun i=>embed n (a i))) := by
    simp only [P,LatticePolytope.carrier,Finset.coe_image,Finset.coe_univ,
      Set.image_univ,← Set.range_comp']
  refine ⟨P,hcarrier,P.smooth_of_vertex_orthants_and_axes ?_⟩
  intro v hv
  rw [hcarrier] at hv
  obtain ⟨j,rfl⟩ := extremePoints_convexHull_subset hv
  have hj : j∈vertexWeightIndices a := Finset.mem_filter.mpr ⟨Finset.mem_univ j,hv⟩
  obtain ⟨b,hb⟩ := hlocal ⟨j,hj⟩
  refine ⟨a j,b,Finset.mem_image.mpr ⟨j,Finset.mem_univ j,rfl⟩,rfl,?_,?_⟩
  · simpa only [hcarrier] using hull_orthant_of_difference_basis a j b hb
  · intro i
    have hbi : b i∈differenceWeightMonoid a j := by
      rw [hb]
      intro l hl
      simp only [Module.Basis.repr_self_apply]
      split_ifs <;> norm_num
    simpa only [hcarrier,integralBasisReal_apply] using
      positive_axis_point_of_differenceMonoid a j (b i) hbi (b.ne_zero i)

end PaperVerification.ToricGeometry

end
-- END PaperVerification.ToricSemigroupPolytopes
end

section
-- BEGIN PaperVerification.ToricChosenVertexFans



/-!
# The actual normal fan retaining specified vertex character bases

The normal fan is constructed from any specified primitive edge bases at
the actual vertices. This retains exactly the bases recovered from the
smooth affine semigroup charts, so subsequent scheme identifications use
literal coordinate-ring equalities, without an unproved choice-of-basis
dictionary.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.LatticePolytope

open Set
open PaperVerification.ToricCharacters
open scoped BigOperators Classical

variable {n : ℕ} (P : LatticePolytope n)

theorem exists_normal_fan_with_chosen_vertex_bases {J : Type*} [Fintype J]
    (v : J → Lattice n) (b : J → Module.Basis (Fin n) ℤ (Lattice n))
    (lengths : J → Fin n → ℕ)
    (hvertices : Set.range (fun j=>embed n (v j))=P.carrier.extremePoints ℝ)
    (hedges : ∀ j i,0<lengths j i ∧
      P.IsEdge (embed n (v j)) (embed n (v j+(lengths j i : ℤ) • b j i)))
    (horthant : ∀ j x,x∈P.carrier → ∀ i,
      0≤(integralBasisReal (b j)).repr (x-embed n (v j)) i) :
    ∃ «Σ» : SmoothCompleteFan n,
      «Σ».realCones=P.normalFan ∧ «Σ».IsPure ∧
      (∀ j,Finset.univ.image (integralDualBasis (b j))∈«Σ».cones) ∧
      (∀ t∈«Σ».cones,∃ j,t⊆Finset.univ.image (integralDualBasis (b j))) ∧
      (∀ j,P.normalCone (embed n (v j))=
        (latticeRayCone (Finset.univ.image (integralDualBasis (b j))) : Set (Ambient n))) := by
  let d : J → Module.Basis (Fin n) ℤ (Lattice n) := fun j=>integralDualBasis (b j)
  have hv (j : J) : embed n (v j)∈P.carrier :=
    ((hvertices ▸ Set.mem_range_self j) : embed n (v j)∈P.carrier.extremePoints ℝ).1
  have hnormal (j : J) : P.normalCone (embed n (v j))=
      (latticeRayCone (Finset.univ.image (d j)) : Set (Ambient n)) :=
    P.normalCone_eq_latticeRayCone (v j) (b j) (lengths j) (hedges j) (horthant j)
  have hinter (j l : J) :
      latticeRayCone (Finset.univ.image (d j)) ⊓
          latticeRayCone (Finset.univ.image (d l))=
        latticeRayCone ((Finset.univ.image (d j))∩(Finset.univ.image (d l))) :=
    P.normalCone_basis_common_rays (v j) (v l) (hv j) (hv l)
      (b j) (b l) (lengths j) (lengths l) (hedges j) (hedges l)
      (horthant j) (horthant l)
  have hcover (u : Ambient n) : ∃ j,u∈latticeRayCone (Finset.univ.image (d j)) := by
    let f : Ambient n →ₗ[ℝ] ℝ := dotProductEquiv ℝ (Fin n) u
    obtain ⟨x,hx,hmin⟩ := P.exists_minimizing_vertex f
    obtain ⟨j,rfl⟩ := hvertices.symm ▸ hx
    refine ⟨j,?_⟩
    change u∈(latticeRayCone (Finset.univ.image (d j)) : Set (Ambient n))
    rw [← hnormal j]
    intro y hy
    change 0≤f (y-embed n (v j))
    rw [map_sub]
    exact sub_nonneg.mpr (hmin y hy)
  let «Σ» := fanOfBasisFamily d hinter hcover
  have hs (j : J) : Finset.univ.image (d j)∈«Σ».cones :=
    (mem_basisFamilyCones d _).mpr ⟨j,Finset.Subset.refl _⟩
  refine ⟨«Σ»,?_,fanOfBasisFamily_isPure d hinter hcover,hs,
    fun t ht=>(mem_basisFamilyCones d t).mp ht,hnormal⟩
  ext C
  constructor
  · rintro ⟨s,hs,rfl⟩
    obtain ⟨j,hj⟩ := (mem_basisFamilyCones d s).mp hs
    let I := basisRayIndices (d j) s
    have hI : I.image (d j)=s := image_basisRayIndices (d j) s hj
    have h := P.subbasis_mem_normalFan (v j) (hv j) (b j) (lengths j)
      (hedges j) (horthant j) I
    change (latticeRayCone (I.image (d j)) : Set (Ambient n))∈P.normalFan at h
    simpa only [hI] using h
  · rintro ⟨x,hx,rfl⟩
    have hhull : x∈convexHull ℝ (Set.range (fun j=>embed n (v j))) := by
      rw [hvertices,P.hull_vertices]
      exact hx
    obtain ⟨p,hp,hpsum,hpm⟩ :=
      PaperVerification.Toric.exists_probability_of_mem_convexHull_range
        (fun j=>embed n (v j)) hhull
    let K := Finset.univ.filter (fun j : J=>0<p j)
    have hK : K.Nonempty := by
      have hpos : 0<∑ j,p j := by rw [hpsum];norm_num
      obtain ⟨j,hj,hpj⟩ := (Finset.sum_pos_iff_of_nonneg (fun j _=>hp j)).mp hpos
      exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ j,hpj⟩⟩
    obtain ⟨s,hs',hspec⟩ := «Σ».exists_cone_finite_intersection K
      (fun j=>Finset.univ.image (d j)) hK (fun j hj=>hs j)
    refine ⟨s,hs',?_⟩
    ext u
    rw [← hpm,P.mem_normalCone_convex_average (fun j=>embed n (v j)) p hv hp hpsum u]
    change (∀ i,0<p i → u∈P.normalCone (embed n (v i))) ↔ u∈latticeRayCone s
    rw [hspec u]
    simp only [hnormal,K,Finset.mem_filter,Finset.mem_univ,true_and]
    exact Iff.rfl

end PaperVerification.ToricGeometry.LatticePolytope

namespace PaperVerification.ToricGeometry

open Set
open PaperVerification.ToricCharacters
open scoped BigOperators Classical

set_option maxHeartbeats 2000000 in
/-- Reconstruction retaining the actual affine-chart semigroups and the
literal vertex normal cones required for scheme gluing. -/
theorem exists_polytope_fan_of_vertex_semigroups {ι : Type*}
    [Fintype ι] [Nonempty ι] {n : ℕ} (a : ι → Lattice n)
    (hlocal : ∀ j : vertexWeightIndices a,
      ∃ b : Module.Basis (Fin n) ℤ (Lattice n),
        differenceWeightMonoid a j.val=coordinateConeMonoid b Finset.univ) :
    ∃ (P : LatticePolytope n) («Σ» : SmoothCompleteFan n)
      (s : vertexWeightIndices a → Finset (Lattice n)),
      P.carrier=convexHull ℝ (Set.range (fun i=>embed n (a i))) ∧ P.Smooth ∧
      «Σ».realCones=P.normalFan ∧ «Σ».IsPure ∧
      (∀ j,s j∈«Σ».cones) ∧ (∀ t∈«Σ».cones,∃ j,t⊆s j) ∧
      (∀ j,dualConeMonoid (s j)=differenceWeightMonoid a j.val) ∧
      (∀ j,P.normalCone (embed n (a j.val))=(latticeRayCone (s j) : Set (Ambient n))) := by
  obtain ⟨P,hP,hPs⟩ := exists_smooth_polytope_of_vertex_semigroups a hlocal
  choose b hb using hlocal
  have hvertices : Set.range (fun j : vertexWeightIndices a=>embed n (a j.val))=
      P.carrier.extremePoints ℝ := by rw [hP];exact range_vertexWeightIndices a
  have horthant (j : vertexWeightIndices a) (x : Ambient n) (hx : x∈P.carrier) :
      ∀ i,0≤(integralBasisReal (b j)).repr (x-embed n (a j.val)) i :=
    hull_orthant_of_difference_basis a j.val (b j) (hb j) x (hP ▸ hx)
  have hv (j : vertexWeightIndices a) : a j.val∈P.generators := by
    have hex : embed n (a j.val)∈P.carrier.extremePoints ℝ :=
      hvertices ▸ Set.mem_range_self j
    obtain ⟨z,hz,he⟩ := P.extreme_integral hex
    exact (embed_injective n he) ▸ hz
  have haxis (j : vertexWeightIndices a) (i : Fin n) :
      ∃ ε : ℝ,0<ε ∧ embed n (a j.val)+ε • integralBasisReal (b j) i∈P.carrier := by
    have hbi : b j i∈differenceWeightMonoid a j.val := by
      rw [hb j]
      intro l hl
      simp only [Module.Basis.repr_self_apply]
      split_ifs <;> norm_num
    simpa only [hP,integralBasisReal_apply] using
      positive_axis_point_of_differenceMonoid a j.val (b j i) hbi ((b j).ne_zero i)
  choose lengths hlengths using fun j i=>P.coordinateRayFace_eq_integral_edge
    (a j.val) (hv j) (b j) (horthant j) i (haxis j i)
  have hedges (j : vertexWeightIndices a) (i : Fin n) :
      0<lengths j i ∧ P.IsEdge (embed n (a j.val))
        (embed n (a j.val+(lengths j i : ℤ) • b j i)) :=
    ⟨(hlengths j i).1,(hlengths j i).2.1⟩
  obtain ⟨«Σ»,«hΣ»,hpure,hs,hcover,hnormal⟩ := P.exists_normal_fan_with_chosen_vertex_bases
    (fun j : vertexWeightIndices a=>a j.val) b lengths hvertices hedges horthant
  refine ⟨P,«Σ»,fun j=>Finset.univ.image (integralDualBasis (b j)),
    hP,hPs,«hΣ»,hpure,hs,hcover,?_,hnormal⟩
  intro j
  rw [dualConeMonoid_basis_eq,integralDualBasis_involutive,← hb j]

end PaperVerification.ToricGeometry

end
-- END PaperVerification.ToricChosenVertexFans
end

section
-- BEGIN PaperVerification.ToricFiniteCharacterSubspaces



/-!
# Finite algebraic subrepresentations generated by finitely many sections

A finite collection in a coaction-stable Laurent subspace is contained
in the span of finitely many characters from that same subspace. This
does not require a prior finite-dimensionality theorem for all global
sections. It is the finite representation used in the projective
linearization construction.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open AddMonoidAlgebra
open scoped TensorProduct Classical

variable (k : Type*) [Field k] {M : Type*} [AddCommGroup M]

theorem characterModule_isCharacterStable (S : Set M) :
    IsCharacterStable k (characterModule k S) := by
  let V := characterModule k S
  let Q : Submodule k (AddMonoidAlgebra k M ⊗[k] AddMonoidAlgebra k M) :=
    LinearMap.range (TensorProduct.map
      (LinearMap.id : AddMonoidAlgebra k M →ₗ[k] _) V.subtype)
  have hle : V ≤ Q.comap (Coalgebra.comul (R := k)) := by
    rw [show V = characterModule k S from rfl, characterModule_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨m,hm,rfl⟩
    have hmem : single m (1:k) ∈ V := by
      rw [show V = characterModule k S from rfl, characterModule_eq_span]
      exact Submodule.subset_span ⟨m,hm,rfl⟩
    refine ⟨single m (1:k) ⊗ₜ[k] (⟨single m (1:k),hmem⟩ : V), ?_⟩
    simp [AddMonoidAlgebra.comul_single]
  exact fun f hf => hle hf

theorem exists_finite_character_subspace
    (V : Submodule k (AddMonoidAlgebra k M)) (hV : IsCharacterStable k V)
    (F : Finset (AddMonoidAlgebra k M)) (hF : ∀ f∈F,f∈V) :
    ∃ S : Finset M,
      (∀ f∈F,f∈characterModule k (S : Set M)) ∧
      characterModule k (S : Set M) ≤ V ∧
      IsCharacterStable k (characterModule k (S : Set M)) := by
  let S : Finset M := F.biUnion (fun f => f.coeff.support)
  refine ⟨S, ?_, ?_, characterModule_isCharacterStable k _⟩
  · intro f hf
    rw [mem_characterModule_iff]
    intro m hm
    exact Finset.mem_biUnion.mpr ⟨f,hf,hm⟩
  · rw [characterModule_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨m,hm,rfl⟩
    obtain ⟨f,hf,hmf⟩ := Finset.mem_biUnion.mp hm
    exact single_mem_of_stable k V hV f (hF f hf) m
      (Finsupp.mem_support_iff.mp hmf)

theorem finiteDimensional_characterModule (S : Finset M) :
    FiniteDimensional k (characterModule k (S : Set M)) := by
  let e : characterModule k (S : Set M) ≃ₗ[k] (S : Set M) →₀ k :=
    AddMonoidAlgebra.supportedEquivFinsupp (R := k) (S := k) (S : Set M)
  exact FiniteDimensional.of_injective e.toLinearMap e.injective

end PaperVerification.ToricCharacters

end
-- END PaperVerification.ToricFiniteCharacterSubspaces
end

section
-- BEGIN PaperVerification.ToricIntrinsicAffineCharts



/-!
# Ordinary smooth scheme charts give actual unimodular exponent charts

An actual open immersion from the character torus gives the common
function field, with its exact coordinate maps. Ordinary smoothness of
the affine structure morphism gives algebraic smoothness. The pointed
semigroup classification then supplies a genuine primitive lattice basis.
Neither a function-field equality nor a lattice-generation conclusion is
assumed separately.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory

theorem affineOpenCoordinateMap_specMap {A B : CommRingCat.{u}}
    [IsDomain A] [IsDomain B] (φ : A⟶B) [IsOpenImmersion (Spec.map φ)] :
    (affineOpenCoordinateMap B (Spec.map φ)).comp φ.hom=
      affineOpenCoordinateMap A (𝟙 (Spec A)) := by
  ext a
  have hsec : (Spec.map φ).appTop ((Scheme.ΓSpecIso A).inv a)=
      (Scheme.ΓSpecIso B).inv (φ a) := by
    exact congrArg (fun f=>f a) (Scheme.ΓSpecIso_inv_naturality φ).symm
  have h := openImmersionGlobalToFunctionField_restrict (Spec.map φ)
    (𝟙 (Spec A)) ((Scheme.ΓSpecIso A).inv a)
  simpa only [Category.comp_id,hsec,affineOpenCoordinateMap,RingHom.comp_apply] using h

end PaperVerification.ToricSchemes

namespace PaperVerification.ToricCharacters

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricGeometry PaperVerification.ToricSchemes

variable (k : Type u) [Field k] {n : ℕ}
    [IsDomain (AddMonoidAlgebra k (Lattice n))]

theorem affineExponentMonoid_monoidChartAlgebra (S : AddSubmonoid (Lattice n)) :
    affineExponentMonoid k (monoidChartAlgebra k S)=S := by
  ext m
  simp [mem_affineExponentMonoid,mem_monoidChartAlgebra]

/-- This theorem consumes literal scheme smoothness and the literal open
torus inclusion. Its output is an actual equality of exponent monoids. -/
theorem pointed_semigroup_basis_of_smooth_open_torus
    (S : AddSubmonoid (Lattice n)) (hS : IsPointedMonoid S)
    [Smooth (Spec.map (CommRingCat.ofHom
      (algebraMap k (monoidChartAlgebra k S))))]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (monoidChartAlgebra k S).val.toRingHom))] :
    ∃ b : Module.Basis (Fin n) ℤ (Lattice n),
      S=coordinateConeMonoid b Finset.univ := by
  let A := monoidChartAlgebra k S
  let R := AddMonoidAlgebra k (Lattice n)
  let X := Spec (CommRingCat.of A)
  let K := X.functionField
  let j : Spec (CommRingCat.of R)⟶X := Spec.map (CommRingCat.ofHom A.val.toRingHom)
  letI : Algebra A K := affineOpenCoordinateAlgebra (CommRingCat.of A) (𝟙 X)
  letI : IsFractionRing A K := affineOpenCoordinate_isFractionRing (CommRingCat.of A) (𝟙 X)
  letI : Algebra R K := affineOpenCoordinateAlgebra (CommRingCat.of R) j
  letI : IsFractionRing R K := affineOpenCoordinate_isFractionRing (CommRingCat.of R) j
  have hmaps : (algebraMap R K).comp A.val.toRingHom=algebraMap A K :=
    affineOpenCoordinateMap_specMap (CommRingCat.ofHom A.val.toRingHom)
  letI : SMul A K := (inferInstance : Algebra A K).toSMul
  letI : IsScalarTower A R K := IsScalarTower.of_algebraMap_eq (fun a=>
    (congrArg (fun f=>f a) hmaps).symm)
  letI : Algebra k K := ((algebraMap A K).comp (algebraMap k A)).toAlgebra
  letI : IsScalarTower k A K := IsScalarTower.of_algebraMap_eq (fun r=>rfl)
  letI : IsScalarTower k R K := IsScalarTower.of_algebraMap_eq (by
    intro r
    change algebraMap A K (algebraMap k A r)=algebraMap R K (algebraMap k R r)
    rw [← congrArg (fun f=>f (algebraMap k A r)) hmaps]
    rfl)
  letI : Algebra.Smooth k A := by
    apply RingHom.smooth_algebraMap.mp
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mp
      (inferInstance : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k A))))
  have hstable : IsCharacterStable k A.toSubmodule := by
    rw [show A.toSubmodule=characterModule k (S : Set (Lattice n)) from
      monoidChartAlgebra_toSubmodule k S]
    exact characterModule_isCharacterStable k (S : Set (Lattice n))
  have hpointed : IsPointedMonoid (affineExponentMonoid k A) := by
    simpa only [A,affineExponentMonoid_monoidChartAlgebra] using hS
  obtain ⟨b,hb⟩ := smooth_invariant_affineAlgebra_eq_coordinateCone k A hstable hpointed K
  refine ⟨b,?_⟩
  have he := congrArg (affineExponentMonoid k) hb
  simpa only [A,affineExponentMonoid_monoidChartAlgebra] using he

end PaperVerification.ToricCharacters

end
-- END PaperVerification.ToricIntrinsicAffineCharts
end

section
-- BEGIN PaperVerification.ToricSmoothMonomialFan



/-!
# Ordinary smoothness reconstructs the actual fan of a monomial Proj

Smoothness is the ordinary scheme-morphism predicate over the field.
The torus is required to be the actual open character torus. These
geometric conditions imply the unimodular semigroup charts used in the
preceding construction, and hence yield an actual scheme isomorphism
over the original field.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

universe u

namespace PaperVerification.ToricCharacters

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricGeometry
open scoped Classical

variable {ι : Type*} {n : ℕ} (a : ι → Lattice n) (k : Type u) [Field k]

theorem monomialCoordinateChart_smooth
    [Smooth (monomialProjectiveToSpec a k)] (j : ι) :
    Smooth (Spec.map (CommRingCat.ofHom
      (algebraMap k (monoidChartAlgebra k (differenceWeightMonoid a j))))) := by
  letI : IsOpenImmersion (monomialCoordinateChartMap a k j) :=
    monomialCoordinateChartMap_isOpenImmersion a k j
  have h : Smooth (monomialCoordinateChartMap a k j≫monomialProjectiveToSpec a k) :=
    inferInstance
  exact (monomialCoordinateChartMap_toSpec a k j) ▸ h

theorem monomialCoordinateChart_torus_isOpenImmersion (j₀ j : ι)
    [IsOpenImmersion (monomialTorusChart a k j₀)] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (monoidChartAlgebra k (differenceWeightMonoid a j)).val.toRingHom)) := by
  haveI : IsOpenImmersion (monomialTorusChart a k j) := by
    rw [monomialTorusChart_independent a k j j₀]
    infer_instance
  let f := Spec.map (CommRingCat.ofHom
    (monoidChartAlgebra k (differenceWeightMonoid a j)).val.toRingHom)
  letI : IsOpenImmersion (monomialCoordinateChartMap a k j) :=
    monomialCoordinateChartMap_isOpenImmersion a k j
  haveI : IsOpenImmersion (f≫monomialCoordinateChartMap a k j) :=
    (monomialCoordinateChartMap_torus a k j).symm ▸
      (inferInstance : IsOpenImmersion (monomialTorusChart a k j))
  exact IsOpenImmersion.of_comp f (monomialCoordinateChartMap a k j)

theorem smooth_monomial_vertex_semigroup [Fintype ι]
    [Smooth (monomialProjectiveToSpec a k)] (j₀ : ι)
    [IsOpenImmersion (monomialTorusChart a k j₀)]
    (j : vertexWeightIndices a) :
    ∃ b : Module.Basis (Fin n) ℤ (Lattice n),
      differenceWeightMonoid a j.val=coordinateConeMonoid b Finset.univ := by
  letI := monomialCoordinateChart_smooth a k j.val
  letI := monomialCoordinateChart_torus_isOpenImmersion a k j₀ j.val
  exact pointed_semigroup_basis_of_smooth_open_torus k (differenceWeightMonoid a j.val)
    (differenceWeightMonoid_pointed_at_vertex a j.val (Finset.mem_filter.mp j.property).2)

end PaperVerification.ToricCharacters



namespace PaperVerification.ToricGeometry

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricCharacters
open scoped Classical

/-- Faithful reconstruction for an ordinary smooth monomial projective
scheme with its actual open character torus. -/
theorem exists_smooth_normal_fan_of_monomial_projective {ι : Type*}
    [Fintype ι] {n : ℕ} (a : ι → Lattice n) (k : Type u) [Field k]
    [Smooth (monomialProjectiveToSpec a k)] (j₀ : ι)
    [IsOpenImmersion (monomialTorusChart a k j₀)] :
    ∃ (P : LatticePolytope n) («Σ» : SmoothCompleteFan n)
      (e : «Σ».fanScheme k≅monomialProjectiveScheme a k),
      P.carrier=convexHull ℝ (Set.range (fun i=>embed n (a i))) ∧ P.Smooth ∧
      «Σ».realCones=P.normalFan ∧ «Σ».IsPure ∧
      e.hom≫monomialProjectiveToSpec a k=«Σ».fanSchemeStructureMap k ∧
      (∀ j : ι,«Σ».splitTorusOpenMap k≫e.hom=monomialTorusChart a k j) := by
  letI : Nonempty ι := ⟨j₀⟩
  have hlocal := smooth_monomial_vertex_semigroup a k j₀
  obtain ⟨P,«Σ»,s,hP,hPs,«hΣ»,hpure,hs,hcover,hdual,hnormal⟩ :=
    exists_polytope_fan_of_vertex_semigroups a hlocal
  have hv (j : vertexWeightIndices a) : embed n (a j.val)∈P.carrier := by
    rw [hP]
    exact subset_convexHull ℝ _ (Set.mem_range_self j.val)
  let e := «Σ».monomialNormalFanIso P a k s hdual hs hcover hv hnormal
  refine ⟨P,«Σ»,e,hP,hPs,«hΣ»,hpure,
    «Σ».monomialNormalFanIso_toSpec P a k s hdual hs hcover hv hnormal,?_⟩
  intro j
  obtain ⟨i,hi⟩ := hcover ∅ «Σ».empty_mem
  rw [«Σ».monomialNormalFanIso_torus P a k s hdual hs hcover hv hnormal i,
    monomialTorusChart_independent a k i.val j]

end PaperVerification.ToricGeometry

end
-- END PaperVerification.ToricSmoothMonomialFan
end

#print axioms PaperVerification.ToricGeometry.exists_smooth_normal_fan_of_monomial_projective
