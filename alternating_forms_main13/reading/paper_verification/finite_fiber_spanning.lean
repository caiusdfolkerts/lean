module

public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Spanning a finite module from all residue fibers

A proper submodule of a finite module lies in a maximal submodule.  The
quotient is simple, and its annihilator is a maximal ideal of the scalar
ring.  Therefore a family that spans modulo every maximal ideal already
spans the original module.  No flatness or absence of torsion is assumed.
-/

@[expose] public section
set_option autoImplicit false

namespace PaperVerification

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem span_restrictScalars_of_surjective
    {S : Type*} [CommRing S] [Algebra R S] [Module S M] [IsScalarTower R S M]
    (h : Function.Surjective (algebraMap R S)) {ι : Type*} (v : ι → M) :
    Submodule.span R (Set.range v) = (Submodule.span S (Set.range v)).restrictScalars R := by
  apply le_antisymm (Submodule.span_le_restrictScalars R S _)
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact Submodule.zero_mem _
  | add x y hx hy ihx ihy => exact Submodule.add_mem _ ihx ihy
  | smul c x hx ih =>
      obtain ⟨r,rfl⟩ := h c
      rw [IsScalarTower.algebraMap_smul]
      exact Submodule.smul_mem _ r ih

theorem submodule_eq_top_of_residue_sup_eq_top [Module.Finite R M]
    (N : Submodule R M)
    (h : ∀ m : Ideal R, m.IsMaximal → N ⊔ m • (⊤ : Submodule R M)=⊤) : N=⊤ := by
  rcases eq_top_or_exists_le_coatom N with hN | ⟨P,hP,hNP⟩
  · exact hN
  · letI : IsSimpleModule R (M⧸P) := isSimpleModule_iff_isCoatom.mpr hP
    let m : Ideal R := Module.annihilator R (M⧸P)
    have hm : m.IsMaximal := IsSimpleModule.annihilator_isMaximal
    have hmul : m • (⊤ : Submodule R M)≤P := by
      apply Submodule.smul_le.mpr
      intro r hr x hx
      apply (Submodule.Quotient.mk_eq_zero P).mp
      rw [Submodule.Quotient.mk_smul]
      exact Module.mem_annihilator.mp hr (Submodule.Quotient.mk x)
    have htop : (⊤ : Submodule R M)≤P := by
      rw [← h m hm]
      exact sup_le hNP hmul
    exact (hP.ne_top (top_unique htop)).elim

theorem span_eq_top_of_residue_sup_eq_top [Module.Finite R M]
    {ι : Type*} (v : ι → M)
    (h : ∀ m : Ideal R, m.IsMaximal →
      Submodule.span R (Set.range v) ⊔ m • (⊤ : Submodule R M)=⊤) :
    Submodule.span R (Set.range v)=⊤ :=
  submodule_eq_top_of_residue_sup_eq_top _ h

end PaperVerification
