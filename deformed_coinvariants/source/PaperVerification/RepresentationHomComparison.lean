module

public import PaperVerification.SemisimpleHomComparison
public import TauCeti.RepresentationTheory.AsModule
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Original-field representation reconstruction

Finite-coordinate test representations suffice: every finite representation
is transported along its actual finite basis. The module/representation
dictionary is proved explicitly for the source modules. Maschke's theorem,
the complement argument, and arbitrary-field multiplicity reconstruction
then produce a genuine equivalence of the original representations.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Representation
open scoped MonoidAlgebra

namespace PaperVerification.RepresentationHomComparison

variable {K G : Type*} [Field K] [Group G]

section Transport

variable {L T V : Type*} [AddCommGroup L] [Module K L]
  [AddCommGroup T] [Module K T] [AddCommGroup V] [Module K V]

def conjugateRepresentation (e : L ≃ₗ[K] T) (τ : Representation K G L) :
    Representation K G T := (LinearEquiv.conjRingEquiv e).toMonoidHom.comp τ

def conjugateEquiv (e : L ≃ₗ[K] T) (τ : Representation K G L) :
    τ.Equiv (conjugateRepresentation e τ) :=
  Representation.Equiv.mk e (by
    intro g
    apply LinearMap.ext
    intro x
    change e (τ g x) = e (τ g (e.symm (e x)))
    rw [LinearEquiv.symm_apply_apply])

/-- Changing the source by an actual equivalence changes the intertwining
space by a genuine linear equivalence over the original coefficient field. -/
def intertwinerSourceEquiv {τ : Representation K G L} {υ : Representation K G T}
    (e : τ.Equiv υ) (ρ : Representation K G V) :
    IntertwiningMap τ ρ ≃ₗ[K] IntertwiningMap υ ρ :=
  (IntertwiningMap.equivLinearMapAsModule τ ρ).trans
    ((LinearEquiv.congrLeft ρ.asModule K (TauCeti.Representation.asModuleLinearEquivOfEquiv e)).trans
      (IntertwiningMap.equivLinearMapAsModule υ ρ).symm)

end Transport

section ModuleDictionary

variable (L : Type*) [AddCommGroup L] [Module K L] [Module K[G] L] [IsScalarTower K K[G] L]

theorem ofModulePrime_asAlgebraHom :
    (Representation.ofModule' (k := K) (G := G) L).asAlgebraHom = Algebra.lsmul K K L :=
  (MonoidAlgebra.lift K (L →ₗ[K] L) G).apply_symm_apply _

/-- Returning from the representation associated to a group-algebra module
gives that very module, including its actual scalar action. -/
def moduleRepresentationAsModuleEquiv :
    (Representation.ofModule' (k := K) (G := G) L).asModule ≃ₗ[K[G]] L where
  toAddEquiv := (Representation.ofModule' (k := K) (G := G) L).asModuleEquiv.toAddEquiv
  map_smul' a x := by
    change (Representation.ofModule' (k := K) (G := G) L).asModuleEquiv (a • x) =
      a • (Representation.ofModule' (k := K) (G := G) L).asModuleEquiv x
    rw [Representation.asModuleEquiv_map_smul,ofModulePrime_asAlgebraHom]
    rfl

def moduleSourceHomEquiv {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) :
    IntertwiningMap (Representation.ofModule' (k := K) (G := G) L) ρ ≃ₗ[K]
      (L →ₗ[K[G]] ρ.asModule) :=
  (IntertwiningMap.equivLinearMapAsModule (Representation.ofModule' (k := K) (G := G) L) ρ).trans
    (LinearEquiv.congrLeft ρ.asModule K (moduleRepresentationAsModuleEquiv L))

end ModuleDictionary

section Comparison

variable {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [Module.Finite K V] [Module.Finite K W]
variable (ρ : Representation K G V) (σ : Representation K G W)

/-- There is no restriction to specially chosen irreducible models: an
arbitrary finite source representation is reduced to coordinates by its basis. -/
theorem hom_finrank_le_of_coordinate_tests
    (hle : ∀ r : ℕ, ∀ τ : Representation K G (Fin r → K),
      Module.finrank K (IntertwiningMap τ ρ) ≤ Module.finrank K (IntertwiningMap τ σ))
    {L : Type*} [AddCommGroup L] [Module K L] [Module.Finite K L]
    (τ : Representation K G L) :
    Module.finrank K (IntertwiningMap τ ρ) ≤ Module.finrank K (IntertwiningMap τ σ) := by
  let e := (Module.finBasis K L).equivFun
  let υ := conjugateRepresentation e τ
  have h := hle (Module.finrank K L) υ
  rw [← (intertwinerSourceEquiv (conjugateEquiv e τ) ρ).finrank_eq,
    ← (intertwinerSourceEquiv (conjugateEquiv e τ) σ).finrank_eq] at h
  exact h

/-- The regular representation is among the coordinate tests, so the Hom
inequality also compares the dimensions of the underlying vector spaces. -/
theorem finrank_le_of_coordinate_hom_tests [Finite G]
    (hle : ∀ r : ℕ, ∀ τ : Representation K G (Fin r → K),
      Module.finrank K (IntertwiningMap τ ρ) ≤ Module.finrank K (IntertwiningMap τ σ)) :
    Module.finrank K V ≤ Module.finrank K W := by
  have h := hom_finrank_le_of_coordinate_tests ρ σ hle
    (Representation.ofModule' (k := K) (G := G) K[G])
  rw [(moduleSourceHomEquiv K[G] ρ).finrank_eq,
    (moduleSourceHomEquiv K[G] σ).finrank_eq,
    (LinearMap.ringLmapEquivSelf K[G] K ρ.asModule).finrank_eq,
    (LinearMap.ringLmapEquivSelf K[G] K σ.asModule).finrank_eq,
    ρ.asModuleEquiv.finrank_eq, σ.asModuleEquiv.finrank_eq] at h
  exact h

/-- Equal dimension and the proved Hom lower bounds yield an actual
original-field representation equivalence, with no splitting-field premise. -/
theorem nonempty_equiv_of_coordinate_hom_le_of_finrank_eq [Finite G]
    [NeZero (Nat.card G : K)]
    (hle : ∀ r : ℕ, ∀ τ : Representation K G (Fin r → K),
      Module.finrank K (IntertwiningMap τ ρ) ≤ Module.finrank K (IntertwiningMap τ σ))
    (hdim : Module.finrank K V = Module.finrank K W) : Nonempty (ρ.Equiv σ) := by
  apply (TauCeti.Representation.nonempty_equiv_iff (ρ := ρ) (σ := σ)).mpr
  apply SemisimpleHomComparison.nonempty_linearEquiv_of_hom_finrank_le_of_finrank_eq
    (K := K) (A := K[G])
  · intro S
    letI : Module.Finite K S := Module.Finite.of_injective
      (S.subtype.restrictScalars K) Subtype.val_injective
    have h := hom_finrank_le_of_coordinate_tests ρ σ hle
      (Representation.ofModule' (k := K) (G := G) S)
    rw [(moduleSourceHomEquiv S ρ).finrank_eq,(moduleSourceHomEquiv S σ).finrank_eq] at h
    exact h
  · rw [ρ.asModuleEquiv.finrank_eq,σ.asModuleEquiv.finrank_eq]
    exact hdim

end Comparison

end PaperVerification.RepresentationHomComparison
