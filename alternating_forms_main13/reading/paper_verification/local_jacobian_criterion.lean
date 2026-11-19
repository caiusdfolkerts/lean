module

public import PaperVerification.FormallySmoothRelations
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.Tactic

/-!
# The local Jacobian criterion in terms of defining equations

Independence of the defining differentials over the residue field splits the
cotangent map. This formulation does not assume that the conormal module is
already free, or that the given equations are already a regular sequence.
-/

@[expose] public section
noncomputable section
open scoped BigOperators TensorProduct
open KaehlerDifferential

namespace PaperVerification.GenericSectionDifferentials

/-- Over a local ring, independence modulo the maximal ideal splits a finite
family of vectors in a finite free module. -/
theorem linearCombination_split_of_residue_independent
    {R M κ : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    [Fintype κ] (v : κ → M)
    (hv : LinearIndependent (IsLocalRing.ResidueField R)
      (fun i => (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] v i)) :
    ∃ l : M →ₗ[R] (κ → R),
      l.comp (Fintype.linearCombination R v) = LinearMap.id := by
  classical
  let k := IsLocalRing.ResidueField R
  let F := Fintype.linearCombination R v
  let b := (Pi.basisFun R κ).baseChange k
  have he : F.baseChange k = b.constr k (fun i => (1 : k) ⊗ₜ[R] v i) := by
    apply b.ext
    intro i
    simp [F, b, Module.Basis.baseChange_apply]
  apply (IsLocalRing.split_injective_iff_lTensor_residueField_injective F).mpr
  change Function.Injective (F.baseChange k)
  rw [he]
  exact b.injective_constr_of_linearIndependent hv

/-- Equations whose differentials are independent in the residue field cut
out a formally smooth local quotient of a smooth ambient algebra. -/
theorem formallySmooth_of_residue_independent_equations
    {K S κ : Type*} [CommRing K] [CommRing S] [IsLocalRing S]
    [Algebra K S] [Fintype κ]
    (P : Algebra.Extension K S) [Algebra.FormallySmooth K P.Ring]
    [Module.Free P.Ring Ω[P.Ring⁄K]] [Module.Finite P.Ring Ω[P.Ring⁄K]]
    (f : κ → P.Ring) (hf : Ideal.span (Set.range f)=P.ker)
    (hind : LinearIndependent (IsLocalRing.ResidueField S)
      (fun i => (1 : IsLocalRing.ResidueField S) ⊗ₜ[S]
        ((1 : S) ⊗ₜ[P.Ring] D K P.Ring (f i)))) :
    Algebra.FormallySmooth K S := by
  let g : κ → P.Cotangent := fun i => Algebra.Extension.Cotangent.mk
    ⟨f i, hf ▸ Ideal.subset_span (Set.mem_range_self i)⟩
  let F := Fintype.linearCombination S g
  let J := Fintype.linearCombination S (fun i => P.cotangentComplex (g i))
  have hspan : Submodule.span S (Set.range g)=⊤ :=
    Algebra.Extension.Cotangent.span_eq_top_of_span_eq_ker f hf
  have hsurj : Function.Surjective F :=
    (span_range_eq_top_iff_surjective_fintypeLinearCombination S g).mp hspan
  have hJ : J=P.cotangentComplex.comp F := by
    ext x
    simp [J,F,Fintype.linearCombination_apply]
  have hind' : LinearIndependent (IsLocalRing.ResidueField S)
      (fun i => (1 : IsLocalRing.ResidueField S) ⊗ₜ[S]
        P.cotangentComplex (g i)) := by
    simpa only [g,Algebra.Extension.cotangentComplex_mk] using hind
  obtain ⟨l,hl⟩ := linearCombination_split_of_residue_independent
    (fun i => P.cotangentComplex (g i)) hind'
  apply P.formallySmooth_iff_split_injection.mpr
  refine ⟨F.comp l,?_⟩
  apply LinearMap.ext
  intro x
  obtain ⟨y,rfl⟩ := hsurj x
  have hy := LinearMap.congr_fun hl y
  change l (J y)=y at hy
  rw [hJ,LinearMap.comp_apply] at hy
  exact congrArg F hy

end PaperVerification.GenericSectionDifferentials
