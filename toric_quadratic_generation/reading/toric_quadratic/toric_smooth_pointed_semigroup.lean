module

public import PaperVerification.ToricSmoothCotangentRank
public import PaperVerification.ToricInvariantAffineAlgebras
public import PaperVerification.ToricIntegralBasis
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring

@[expose] public section

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

#print axioms PaperVerification.ToricCharacters.exists_unimodular_semigroup_basis
#print axioms PaperVerification.ToricCharacters.smooth_invariant_affineAlgebra_eq_coordinateCone
