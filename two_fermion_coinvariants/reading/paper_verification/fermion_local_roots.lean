module

public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.Algebra.Algebra.Basic

/-!
# Residue maps for the actual local coefficient algebra

The hypotheses are the usual local-ring structure and an actual algebra map
to its coefficient field; surjectivity and its kernel are derived.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion

variable {F A : Type*} [Field F] [CommRing A] [Algebra F A]

theorem residueAlgHom_surjective (f : A →ₐ[F] F) : Function.Surjective f := by
  intro c
  refine ⟨algebraMap F A c,?_⟩
  simpa only [Algebra.algebraMap_self,RingHom.id_apply] using f.commutes c

theorem residueAlgHom_ker [IsLocalRing A] (f : A →ₐ[F] F) :
    RingHom.ker f.toRingHom=IsLocalRing.maximalIdeal A :=
  IsLocalRing.ker_eq_maximalIdeal f.toRingHom (residueAlgHom_surjective f)

theorem unit_iff_residue_ne_zero [IsLocalRing A] (f : A →ₐ[F] F) (a : A) :
    IsUnit a ↔ f a≠0 := by
  rw [←IsLocalRing.notMem_maximalIdeal,←residueAlgHom_ker f,RingHom.mem_ker]
  rfl

end PaperVerification.Fermion

