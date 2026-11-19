module

public import Mathlib.Algebra.MonoidAlgebra.Defs
import all Mathlib.Algebra.MonoidAlgebra.Defs

public import Continuation.Runtime.SaturatedMonoidSplitting
public import Continuation.Runtime.SmoothAlgebraRetract
public import Continuation.Runtime.MonomialFractionField
public import Continuation.Runtime.SmoothPointedLattice
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.RingTheory.FinitePresentation

/-!
# Smooth affine monoids with arbitrary torus factors

The units of a saturated affine monoid form a saturated integral
sublattice. After an integral splitting, its pointed factor is an actual
algebra retract, and therefore smooth. Its characters generate its actual
quotient lattice and its fraction field is the Laurent fraction field.
The pointed cotangent argument consequently gives a basis of that
quotient, without a fixed-point assumption on the original chart.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.ToricCharacters

open PaperVerification.ToricGeometry
open scoped Classical

variable {M : Type*} [AddCommGroup M] (S : AddSubmonoid M)
    (s : ReducedExponentLattice S →ₗ[ℤ] M)
    (hs : (monoidUnitModule S).mkQ.comp s = LinearMap.id)

include hs

/-- Quotienting by invertible exponents preserves generation of the
whole exponent lattice. -/
theorem pointedMonoidPart_groupClosure
    (hgroup : AddSubgroup.closure (S : Set M) = ⊤) :
    AddSubgroup.closure (pointedMonoidPart S s : Set (ReducedExponentLattice S)) = ⊤ := by
  let q := (monoidUnitModule S).mkQ.toAddMonoidHom
  have h := congrArg (fun H : AddSubgroup M => H.map q) hgroup
  rw [AddMonoidHom.map_closure,
    AddSubgroup.map_top_of_surjective q (monoidUnitModule S).mkQ_surjective] at h
  rw [pointedMonoidPart_eq_map S s hs]
  exact h

/-- The ordinary no-cancellation formulation of pointedness used by the
cotangent argument follows from the actual zero support. -/
theorem pointedMonoidPart_isPointedMonoid : IsPointedMonoid (pointedMonoidPart S s) := by
  intro x hx y hy hxy
  have hyx : y = -x := by
    simpa [add_assoc] using congrArg (fun z => -x + z) hxy
  have hx0 := pointedMonoidPart_isPointed S s hs x hx (hyx ▸ hy)
  exact ⟨hx0, by simpa [hx0] using hxy⟩

/-- Evaluation of the invertible character factor at one is an actual
algebra retraction. Smoothness descends along its section. -/
theorem pointedMonoidPart_smooth (k : Type*) [Field k]
    (hfg : S.FG) [Algebra.Smooth k (AddMonoidAlgebra k S)] :
    Algebra.Smooth k (AddMonoidAlgebra k (pointedMonoidPart S s)) := by
  let i := AddMonoidAlgebra.mapDomainAlgHom k k (pointedMonoidInclusion S s)
  let r := AddMonoidAlgebra.mapDomainAlgHom k k (pointedMonoidProjection S s hs)
  have hri : r.comp i = AlgHom.id k (AddMonoidAlgebra k (pointedMonoidPart S s)) := by
    rw [← AddMonoidAlgebra.mapDomainAlgHom_comp,
      pointedMonoidProjection_comp_inclusion S s hs,
      AddMonoidAlgebra.mapDomainAlgHom_id]
  letI : Algebra.FormallySmooth k (AddMonoidAlgebra k (pointedMonoidPart S s)) :=
    formallySmooth_of_algebra_retract i r hri
  letI : AddMonoid.FG (pointedMonoidPart S s) :=
    (AddMonoid.fg_iff_addSubmonoid_fg _).mpr
      (pointedMonoidPart_finitelyGenerated S s hs hfg)
  exact ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

/-- A smooth pointed factor is the nonnegative span of an integral basis
of the quotient lattice. Its dimension is the actual quotient rank. -/
theorem pointedMonoidPart_basis [Module.Finite ℤ M]
    (hsat : ∀ (x : M) (N : ℕ), 0 < N → N • x ∈ S → x ∈ S)
    (k : Type*) [Field k] (hfg : S.FG)
    (hgroup : AddSubgroup.closure (S : Set M) = ⊤)
    [Algebra.Smooth k (AddMonoidAlgebra k S)] :
    ∃ b : Module.Basis (Fin (Module.finrank ℤ (ReducedExponentLattice S)))
        ℤ (ReducedExponentLattice S),
      pointedMonoidPart S s = coordinateConeMonoid b Finset.univ := by
  let Q := ReducedExponentLattice S
  let P := pointedMonoidPart S s
  letI : Module.IsTorsionFree ℤ Q := reducedExponentLattice_isTorsionFree S hsat
  letI : Module.Free ℤ Q := Module.free_of_finite_type_torsion_free'
  let b₀ := Module.finBasis ℤ Q
  letI : UniqueSums Q := UniqueSums.of_injective_addHom b₀.repr.toAddMonoidHom.toAddHom
    b₀.repr.injective inferInstance
  let L := AddMonoidAlgebra k Q
  let K := FractionRing L
  let A := monoidChartAlgebra k P
  let e : AddMonoidAlgebra k P ≃ₐ[k] A := monoidChartAlgebraEquiv k P
  letI : Algebra A K := ((algebraMap L K).comp A.val).toAlgebra
  letI : SMul A K := (inferInstance : Algebra A K).toSMul
  letI towerALK : IsScalarTower A L K := ⟨by
    intro a b c
    simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
    change (algebraMap L K ((a : L) * b)) * c =
      (algebraMap L K (a : L)) * ((algebraMap L K b) * c)
    rw [map_mul, mul_assoc]⟩
  letI : IsScalarTower A (AddMonoidAlgebra k Q) K := towerALK
  have hPgroup := pointedMonoidPart_groupClosure S s hs hgroup
  have hAgroup : AddSubgroup.closure
      {m : Q | AddMonoidAlgebra.single m (1 : k) ∈ A} = ⊤ := by
    have hset : {m : Q | AddMonoidAlgebra.single m (1 : k) ∈ A} = (P : Set Q) := by
      ext m
      simp only [Set.mem_setOf_eq, A, mem_monoidChartAlgebra]
      constructor
      · intro h
        exact h (by simp)
      · intro hm q hq
        have hqm : q = m := by simpa using hq
        exact hqm.symm ▸ hm
    rw [hset]
    exact hPgroup
  letI : IsFractionRing A K :=
    subalgebra_isFractionRing_of_character_groupClosure A K hAgroup
  letI : Algebra (AddMonoidAlgebra k P) K :=
    ((algebraMap A K).comp e.toRingEquiv.toRingHom).toAlgebra
  letI : IsScalarTower k (AddMonoidAlgebra k P) K :=
    IsScalarTower.of_algebraMap_eq (by
      intro c
      change algebraMap k K c = algebraMap A K (e (algebraMap k (AddMonoidAlgebra k P) c))
      rw [e.commutes]
      exact IsScalarTower.algebraMap_apply k L K c)
  letI : IsFractionRing (AddMonoidAlgebra k P) K :=
    IsFractionRing.of_ringEquiv_left e.toRingEquiv (fun _ => rfl)
  letI : IsDomain (AddMonoidAlgebra k P) :=
    Function.Injective.isDomain (algebraMap (AddMonoidAlgebra k P) K)
      (IsFractionRing.injective (AddMonoidAlgebra k P) K)
  letI : Algebra.Smooth k (AddMonoidAlgebra k P) :=
    pointedMonoidPart_smooth S s hs k hfg
  exact exists_unimodular_semigroup_basis_of_finite_free k P
    (pointedMonoidPart_isPointedMonoid S s hs)
    (pointedMonoidPart_finitelyGenerated S s hs hfg) hPgroup K
    (fractionLogDifferentialBasis k K b₀)


omit hs in
/-- Reindexing a basis transports exactly the same coordinate inequalities. -/
theorem coordinateConeMonoid_reindex {E ι κ : Type*} [AddCommGroup E]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (b : Module.Basis ι ℤ E) (e : ι ≃ κ) (I : Finset ι) :
    coordinateConeMonoid (b.reindex e) (I.image e) = coordinateConeMonoid b I := by
  ext x
  constructor
  · intro hx i hi
    have h := hx (e i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    simpa only [Module.Basis.repr_reindex_apply, e.symm_apply_apply] using h
  · intro hx i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    simpa only [Module.Basis.repr_reindex_apply, e.symm_apply_apply] using hx j hj

omit hs in
/-- The full affine monoid, including every invertible direction, is a
coordinate cone in a basis of its original ambient integral lattice. -/
theorem smooth_saturatedMonoid_eq_coordinateCone [Module.Free ℤ M] [Module.Finite ℤ M]
    (hsat : ∀ (x : M) (N : ℕ), 0 < N → N • x ∈ S → x ∈ S)
    (k : Type*) [Field k] (hfg : S.FG)
    (hgroup : AddSubgroup.closure (S : Set M) = ⊤)
    [Algebra.Smooth k (AddMonoidAlgebra k S)] :
    ∃ (b : Module.Basis (Fin (Module.finrank ℤ M)) ℤ M)
      (I : Finset (Fin (Module.finrank ℤ M))), S = coordinateConeMonoid b I := by
  obtain ⟨s, hs⟩ := exists_reducedExponentSection S hsat
  obtain ⟨bQ, hQ⟩ := pointedMonoidPart_basis S s hs hsat k hfg hgroup
  let bU := Module.finBasis ℤ (monoidUnitModule S)
  let eS := latticeUnitSplitEquiv S s hs
  let b := (bU.prod bQ).map eS.symm
  let I : Finset (Fin (Module.finrank ℤ (monoidUnitModule S)) ⊕
      Fin (Module.finrank ℤ (ReducedExponentLattice S))) :=
    Finset.univ.image Sum.inr
  have hrepr (x : M) (j : Fin (Module.finrank ℤ (ReducedExponentLattice S))) :
      b.repr x (Sum.inr j) = bQ.repr ((monoidUnitModule S).mkQ x) j := by
    change (bU.prod bQ).repr (eS x) (Sum.inr j) = _
    rw [Module.Basis.prod_repr_inr]
    rfl
  have hS : S = coordinateConeMonoid b I := by
    ext x
    have hx : x ∈ S ↔ (monoidUnitModule S).mkQ x ∈ pointedMonoidPart S s :=
      mem_iff_reducedExponentSection_mem S s hs x
    rw [hx, hQ]
    constructor
    · intro hx i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      rw [hrepr]
      exact hx j (Finset.mem_univ _)
    · intro hx j hj
      rw [← hrepr]
      exact hx (Sum.inr j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  let J := Fin (Module.finrank ℤ (monoidUnitModule S)) ⊕
    Fin (Module.finrank ℤ (ReducedExponentLattice S))
  have hcard : Fintype.card J = Fintype.card (Fin (Module.finrank ℤ M)) := by
    rw [← Module.finrank_eq_card_basis b, Fintype.card_fin]
  let e : J ≃ Fin (Module.finrank ℤ M) := Fintype.equivOfCardEq hcard
  exact ⟨b.reindex e, I.image e, hS.trans (coordinateConeMonoid_reindex b e I).symm⟩

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.smooth_saturatedMonoid_eq_coordinateCone
