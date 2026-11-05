module

public import Mathlib.RingTheory.Kaehler.JacobiZariski
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.Smooth.Field
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Tactic

/-!
# Independent differentials for a generic vector-valued section

The first two lemmas adapt the proof in OpenAI's public `CriticalLocus.lean`,
commit `4eaee87548250b2682affda7d05d947c05554bae`,
`OAI/AlgebraicGeometry/Seshadri/Bertini/`. The original source is distributed
under Apache-2.0. Its proof uses Mathlib's Jacobi--Zariski sequence and formal
smoothness of extensions of characteristic-zero fields.

The final theorem is the vector-valued extension needed for a generated
bundle. At a common zero of the section, independence of the coefficient
parameters and surjectivity of evaluation force independence of the section's
differentials. The target is the actual module of Kähler differentials.
-/

@[expose] public section
noncomputable section
open scoped TensorProduct BigOperators
open KaehlerDifferential

namespace PaperVerification.GenericSectionDifferentials

theorem mapBaseChange_injective_of_formallySmooth
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.FormallySmooth A B] :
    Function.Injective (KaehlerDifferential.mapBaseChange R A B) := by
  apply (KaehlerDifferential.mapBaseChange R A B).ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro x hx
  obtain ⟨y, hy⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange R A B x).mp hx
  rw [show y=0 from Subsingleton.elim _ _, map_zero] at hy
  exact hy.symm ▸ Submodule.zero_mem _

variable {K L ι : Type*} [Field K] [Field L] [CharZero K] [Algebra K L]

/-- Algebraically independent parameters have independent actual differentials. -/
theorem algebraicIndependent_differentials [Algebra.EssFiniteType K L]
    (v : ι → L) (hv : AlgebraicIndependent K v) :
    LinearIndependent L (fun i => KaehlerDifferential.D K L (v i)) := by
  let A := MvPolynomial ι K
  let F := FractionRing A
  let a : A →ₐ[K] L := MvPolynomial.aeval v
  let b : F →ₐ[K] L := IsFractionRing.liftAlgHom hv
  let : Algebra A L := a.toRingHom.toAlgebra
  let : Algebra F L := b.toRingHom.toAlgebra
  let : IsScalarTower K A L := IsScalarTower.of_algHom a
  let : IsScalarTower K F L := IsScalarTower.of_algHom b
  let : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun x => by
    change a x = IsFractionRing.lift hv (algebraMap A F x)
    exact (IsFractionRing.lift_algebraMap hv x).symm
  let : Algebra.EssFiniteType F L := Algebra.EssFiniteType.of_comp K F L
  let : Algebra.FormallySmooth A F :=
    Algebra.FormallySmooth.of_isLocalization (nonZeroDivisors A)
  let : Algebra.FormallySmooth A L := Algebra.FormallySmooth.comp A F L
  have hinj := mapBaseChange_injective_of_formallySmooth K A L
  have h := ((KaehlerDifferential.mvPolynomialBasis K ι).baseChange L).linearIndependent
  have h' := h.map' (KaehlerDifferential.mapBaseChange K A L)
    (LinearMap.ker_eq_bot.mpr hinj)
  convert h' using 1
  funext i
  simp only [Function.comp_apply, Module.Basis.baseChange_apply,
    KaehlerDifferential.mvPolynomialBasis_apply]
  change (D K L) (v i) = (mapBaseChange K A L) (1 ⊗ₜ[A] (D K A) (MvPolynomial.X i))
  rw [mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
  congr 1
  exact (MvPolynomial.aeval_X v i).symm

/-- At a zero of a generic section, linearly independent evaluation rows give
linearly independent differentials. The result allows any number of bundle
components and any finite family of generating sections. -/
theorem section_differentials_linearIndependent [Algebra.EssFiniteType K L]
    [Fintype ι] {κ : Type*} (v : κ → ι → L) (a : ι → L)
    (hv : LinearIndependent L v) (ha : AlgebraicIndependent K a)
    (hzero : ∀ j, ∑ i, a i * v j i = 0) :
    LinearIndependent L (fun j => ∑ i, a i • D K L (v j i)) := by
  let T := Fintype.linearCombination L (fun i => D K L (a i))
  have hT : Function.Injective T :=
    (linearIndependent_iff_injective_fintypeLinearCombination).mp
      (algebraicIndependent_differentials a ha)
  have hnT : Function.Injective (-T) := by
    intro x y h
    exact hT (neg_injective h)
  have hlin := hv.map' (-T) (LinearMap.ker_eq_bot.mpr hnT)
  convert hlin using 1
  funext j
  change (∑ i, a i • D K L (v j i)) = -(∑ i, v j i • D K L (a i))
  apply eq_neg_iff_add_eq_zero.mpr
  have hd := congrArg (D K L) (hzero j)
  simpa only [map_sum, Derivation.leibniz, Finset.sum_add_distrib, map_zero] using hd

end PaperVerification.GenericSectionDifferentials
