module

public import Lean.Elab.BuiltinEvalCommand
public meta import Lean.Elab.BuiltinEvalCommand
public import Lean.Util.CollectAxioms
public meta import Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public meta import Lean.Util.FoldConsts
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import paper_verification.toric002
public import paper_verification.toric010
public import paper_verification.toric016
public import paper_verification.toric024

@[expose] public section


-- BEGIN ORIGINAL PaperVerification.ToricSmoothPointedSemigroup
section Source_ToricSmoothPointedSemigroup

-- original header: module

-- original header: public import PaperVerification.ToricSmoothCotangentRank
-- original header: public import PaperVerification.ToricInvariantAffineAlgebras
-- original header: public import PaperVerification.ToricIntegralBasis
-- original header: public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
-- original header: public import Mathlib.Tactic.Push
-- original header: public import Mathlib.Tactic.Ring

-- original header: @[expose] public section

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
end
end Source_ToricSmoothPointedSemigroup
-- END ORIGINAL PaperVerification.ToricSmoothPointedSemigroup


-- BEGIN ORIGINAL PaperVerification.ToricIntrinsicAffineCharts
section Source_ToricIntrinsicAffineCharts

-- original header: module

-- original header: public import PaperVerification.ToricSmoothPointedSemigroup
-- original header: public import PaperVerification.ToricFiniteCharacterSubspaces
-- original header: public import PaperVerification.ToricFunctionFieldBridge
-- original header: public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

-- original header: @[expose] public section

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

#print axioms PaperVerification.ToricCharacters.pointed_semigroup_basis_of_smooth_open_torus
end
end Source_ToricIntrinsicAffineCharts
-- END ORIGINAL PaperVerification.ToricIntrinsicAffineCharts


