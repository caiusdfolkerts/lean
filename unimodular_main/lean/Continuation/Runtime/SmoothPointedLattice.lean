module

public import Continuation.Runtime.IntrinsicMonomialReconstruction

/-!
# Smooth pointed monoids in an arbitrary finite integral lattice

The cotangent argument for the standard lattice applies to any finite
free integral lattice. Keeping the quotient lattice itself here avoids
choosing coordinates before splitting off the invertible exponents.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace PaperVerification.ToricCharacters

open PaperVerification.ToricGeometry KaehlerDifferential
open scoped BigOperators Classical

variable (k : Type*) [Field k] {M : Type*} [AddCommGroup M]
    [Module.Free ℤ M] [Module.Finite ℤ M] (S : AddSubmonoid M)
    (hpointed : IsPointedMonoid S) (hfg : S.FG)
    (hgroup : AddSubgroup.closure (S : Set M) = ⊤)
    [IsDomain (AddMonoidAlgebra k S)] [Algebra.Smooth k (AddMonoidAlgebra k S)]
    (K : Type*) [Field K] [Algebra k K] [Algebra (AddMonoidAlgebra k S) K]
    [IsScalarTower k (AddMonoidAlgebra k S) K]
    [IsFractionRing (AddMonoidAlgebra k S) K]
    (bK : Module.Basis (Fin (Module.finrank ℤ M)) K Ω[K⁄k])

include hpointed hfg hgroup bK in
/-- Every smooth pointed affine monoid spanning its lattice is the
nonnegative span of a genuine integral basis of that same lattice. -/
theorem exists_unimodular_semigroup_basis_of_finite_free :
    ∃ b : Module.Basis (Fin (Module.finrank ℤ M)) ℤ M,
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
    exact congrArg (fun s : S => (s : M)) h
  have hp0 (i : G) : p i≠0 := by
    intro h
    exact (hAtoms i.val i.property).2.1 (congrArg Subtype.val h)
  have hpatom (i : G) (a b : S) (hab : a+b=p i) : a=0 ∨ b=0 := by
    have h := (hAtoms i.val i.property).2.2 a.val a.property b.val b.property
      (congrArg Subtype.val hab)
    exact h.imp Subtype.ext Subtype.ext
  have hcard : Fintype.card G ≤ Module.finrank ℤ M :=
    pointed_atoms_card_le k S hzero K bK p hpinj hp0 hpatom
  let v : G → M := fun g => g.val
  have hspan : ⊤≤Submodule.span ℤ (Set.range v) := by
    let V := Submodule.span ℤ (Set.range v)
    have hSG : (S : Set M) ⊆ V := by
      intro x hx
      rw [← hG] at hx
      induction hx using AddSubmonoid.closure_induction with
      | mem x hx => exact Submodule.subset_span ⟨⟨x,hx⟩,rfl⟩
      | zero => exact V.zero_mem
      | add x y hx hy ihx ihy => exact V.add_mem ihx ihy
    have hcl : AddSubgroup.closure (S : Set M)≤V.toAddSubgroup :=
      (AddSubgroup.closure_le _).mpr hSG
    rw [hgroup] at hcl
    exact hcl
  have hli : LinearIndependent ℤ v :=
    linearIndependent_of_top_le_span_of_card_le_finrank hspan hcard
  let bG : Module.Basis G ℤ M := Module.Basis.mk hli hspan
  have hcardEq : Fintype.card G=Fintype.card (Fin (Module.finrank ℤ M)) := by
    rw [← Module.finrank_eq_card_basis bG,Fintype.card_fin]
  let e : G ≃ Fin (Module.finrank ℤ M) := Fintype.equivOfCardEq hcardEq
  let b : Module.Basis (Fin (Module.finrank ℤ M)) ℤ M := bG.reindex e
  have hrange : Set.range b = (G : Set M) := by
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


end PaperVerification.ToricCharacters
