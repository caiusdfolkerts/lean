module

public import Mathlib.Algebra.Group.Submonoid.Support
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.RingTheory.Int.Basic

/-!
# Splitting off the units of a saturated affine monoid

The support `S ∩ -S` is the subgroup of invertible exponents. Saturation
makes its quotient torsion free. In a finite lattice that quotient is free,
so the quotient map has an integral linear section. Restricting this
splitting gives a pointed monoid and an actual additive equivalence
`S ≃ support(S) × pointedPart(S)`.

This is the algebraic step needed to retain torus factors in invariant
affine charts; it makes no fixed-point or full-dimensional-cone assumption.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

namespace PaperVerification.ToricCharacters

variable {M : Type u} [AddCommGroup M] (S : AddSubmonoid M)

/-- The actual subgroup of invertible exponents, as an integral submodule. -/
abbrev monoidUnitModule : Submodule ℤ M := S.support.toIntSubmodule

/-- The exponent lattice modulo all invertible exponents. -/
abbrev ReducedExponentLattice := M ⧸ monoidUnitModule S

theorem monoidUnitModule_saturated
    (hsat : ∀ (x : M) (N : ℕ), 0 < N → N • x ∈ S → x ∈ S)
    (x : M) (N : ℕ) (hN : 0 < N) (hx : N • x ∈ monoidUnitModule S) :
    x ∈ monoidUnitModule S := by
  change x ∈ S ∧ -x ∈ S
  change N • x ∈ S ∧ -(N • x) ∈ S at hx
  exact ⟨hsat x N hN hx.1, hsat (-x) N hN (by simpa using hx.2)⟩

theorem monoidUnitModule_int_saturated
    (hsat : ∀ (x : M) (N : ℕ), 0 < N → N • x ∈ S → x ∈ S)
    (x : M) (a : ℤ) (ha : a ≠ 0) (hx : a • x ∈ monoidUnitModule S) :
    x ∈ monoidUnitModule S := by
  cases a with
  | ofNat N =>
      exact monoidUnitModule_saturated S hsat x N
        (Nat.pos_of_ne_zero (by simpa using ha)) (by simpa using hx)
  | negSucc N =>
      apply monoidUnitModule_saturated S hsat x (N + 1) (Nat.succ_pos _)
      have hn := (monoidUnitModule S).neg_mem hx
      change -((-((N + 1 : ℕ) : ℤ)) • x) ∈ monoidUnitModule S at hn
      simpa only [neg_smul, neg_neg, natCast_zsmul] using hn

/-- The actual quotient lattice has no integer torsion. -/
theorem reducedExponentLattice_isTorsionFree
    (hsat : ∀ (x : M) (N : ℕ), 0 < N → N • x ∈ S → x ∈ S) :
    Module.IsTorsionFree ℤ (ReducedExponentLattice S) := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro a x hx
  by_cases ha : a = 0
  · exact Or.inl ha
  · right
    obtain ⟨y, rfl⟩ := (monoidUnitModule S).mkQ_surjective x
    apply (Submodule.Quotient.mk_eq_zero (monoidUnitModule S)).mpr
    apply monoidUnitModule_int_saturated S hsat y a ha
    apply (Submodule.Quotient.mk_eq_zero (monoidUnitModule S)).mp
    change (monoidUnitModule S).mkQ (a • y) = 0
    rw [map_smul]
    exact hx

/-- Saturation supplies an integral linear section of the quotient map. -/
theorem exists_reducedExponentSection [Module.Finite ℤ M]
    (hsat : ∀ (x : M) (N : ℕ), 0 < N → N • x ∈ S → x ∈ S) :
    ∃ s : ReducedExponentLattice S →ₗ[ℤ] M,
      (monoidUnitModule S).mkQ.comp s = LinearMap.id := by
  letI : Module.IsTorsionFree ℤ (ReducedExponentLattice S) :=
    reducedExponentLattice_isTorsionFree S hsat
  letI : Module.Free ℤ (ReducedExponentLattice S) :=
    Module.free_of_finite_type_torsion_free'
  exact (monoidUnitModule S).mkQ.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (monoidUnitModule S).mkQ_surjective)

variable (s : ReducedExponentLattice S →ₗ[ℤ] M)
    (hs : (monoidUnitModule S).mkQ.comp s = LinearMap.id)

include hs

theorem reducedExponentSection_apply (x : ReducedExponentLattice S) :
    (monoidUnitModule S).mkQ (s x) = x :=
  congrArg (fun f : ReducedExponentLattice S →ₗ[ℤ] ReducedExponentLattice S => f x) hs

theorem sub_reducedExponentSection_mem_units (x : M) :
    x - s ((monoidUnitModule S).mkQ x) ∈ monoidUnitModule S := by
  apply (Submodule.Quotient.mk_eq_zero (monoidUnitModule S)).mp
  change (monoidUnitModule S).mkQ (x - s ((monoidUnitModule S).mkQ x)) = 0
  rw [map_sub, reducedExponentSection_apply S s hs, sub_self]

/-- The chosen representative of a quotient exponent is in the original
monoid exactly when any representative is. -/
theorem mem_iff_reducedExponentSection_mem (x : M) :
    x ∈ S ↔ s ((monoidUnitModule S).mkQ x) ∈ S := by
  have hu := sub_reducedExponentSection_mem_units S s hs x
  change x - s ((monoidUnitModule S).mkQ x) ∈ S ∧
    -(x - s ((monoidUnitModule S).mkQ x)) ∈ S at hu
  constructor
  · intro hx
    have h := S.add_mem hx hu.2
    convert h using 1 <;> abel
  · intro hx
    have h := S.add_mem hx hu.1
    convert h using 1 <;> abel

/-- The integral splitting on the entire ambient lattice. Its first
coordinate is an actual invertible exponent, and its second is the
original quotient exponent. -/
def latticeUnitSplitEquiv :
    M ≃ₗ[ℤ] monoidUnitModule S × ReducedExponentLattice S where
  toFun x := (⟨x - s ((monoidUnitModule S).mkQ x),
    sub_reducedExponentSection_mem_units S s hs x⟩, (monoidUnitModule S).mkQ x)
  invFun x := x.1.val + s x.2
  left_inv x := by
    change x - s ((monoidUnitModule S).mkQ x) +
      s ((monoidUnitModule S).mkQ x) = x
    abel
  right_inv x := by
    have hu : (monoidUnitModule S).mkQ x.1.val = 0 :=
      (Submodule.Quotient.mk_eq_zero (monoidUnitModule S)).mpr x.1.property
    apply Prod.ext
    · apply Subtype.ext
      change x.1.val + s x.2 - s ((monoidUnitModule S).mkQ (x.1.val + s x.2)) = x.1.val
      rw [map_add, hu, reducedExponentSection_apply S s hs, zero_add]
      abel
    · change (monoidUnitModule S).mkQ (x.1.val + s x.2) = x.2
      rw [map_add, hu, reducedExponentSection_apply S s hs, zero_add]
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      change x + y - s ((monoidUnitModule S).mkQ (x + y)) =
        (x - s ((monoidUnitModule S).mkQ x)) +
          (y - s ((monoidUnitModule S).mkQ y))
      rw [map_add, map_add]
      abel
    · exact map_add _ x y
  map_smul' a x := by
    apply Prod.ext
    · apply Subtype.ext
      change a • x - s ((monoidUnitModule S).mkQ (a • x)) =
        a • (x - s ((monoidUnitModule S).mkQ x))
      rw [map_smul, map_smul, smul_sub]
    · exact map_smul _ a x

/-- The reduced monoid, in the quotient lattice itself. -/
def pointedMonoidPart : AddSubmonoid (ReducedExponentLattice S) :=
  S.comap s.toAddMonoidHom

theorem pointedMonoidPart_isPointed : (pointedMonoidPart S s).IsPointed := by
  intro x hx hnx
  have hu : s x ∈ monoidUnitModule S := by
    change s x ∈ S ∧ -(s x) ∈ S
    refine ⟨hx, ?_⟩
    change s (-x) ∈ S at hnx
    simpa only [map_neg] using hnx
  have hz : (monoidUnitModule S).mkQ (s x) = 0 := (Submodule.Quotient.mk_eq_zero (monoidUnitModule S)).mpr hu
  rwa [reducedExponentSection_apply S s hs] at hz

theorem pointedMonoidPart_eq_map :
    pointedMonoidPart S s = S.map (monoidUnitModule S).mkQ.toAddMonoidHom := by
  ext x
  constructor
  · intro hx
    exact ⟨s x, hx, reducedExponentSection_apply S s hs x⟩
  · rintro ⟨y, hy, rfl⟩
    exact (mem_iff_reducedExponentSection_mem S s hs y).mp hy

theorem pointedMonoidPart_finitelyGenerated (hfg : S.FG) :
    (pointedMonoidPart S s).FG := by
  rw [pointedMonoidPart_eq_map S s hs]
  exact hfg.map _

/-- The actual projection of the monoid to its pointed part. -/
def pointedMonoidProjection : S →+ pointedMonoidPart S s where
  toFun x := ⟨(monoidUnitModule S).mkQ x,
    (mem_iff_reducedExponentSection_mem S s hs x).mp x.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add (monoidUnitModule S).mkQ x.val y.val)

/-- The chosen integral section restricts to an actual monoid homomorphism. -/
def pointedMonoidInclusion : pointedMonoidPart S s →+ S where
  toFun x := ⟨s x, x.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add s x.val y.val)

theorem pointedMonoidProjection_comp_inclusion :
    (pointedMonoidProjection S s hs).comp (pointedMonoidInclusion S s) =
      AddMonoidHom.id (pointedMonoidPart S s) := by
  ext x
  exact reducedExponentSection_apply S s hs x

/-- Splitting the invertible exponents loses no original monoid element
and changes no original exponent in the ambient lattice. -/
def saturatedMonoidSplitEquiv : S ≃+ monoidUnitModule S × pointedMonoidPart S s where
  toFun x :=
    (⟨x.val - s ((monoidUnitModule S).mkQ x.val),
      sub_reducedExponentSection_mem_units S s hs x.val⟩,
      pointedMonoidProjection S s hs x)
  invFun x := ⟨x.1.val + s x.2.val, S.add_mem x.1.property.1 x.2.property⟩
  left_inv x := by
    apply Subtype.ext
    change (x.val - s ((monoidUnitModule S).mkQ x.val)) +
      s ((monoidUnitModule S).mkQ x.val) = x.val
    abel
  right_inv x := by
    have hu : (monoidUnitModule S).mkQ x.1.val = 0 :=
      (Submodule.Quotient.mk_eq_zero (monoidUnitModule S)).mpr x.1.property
    apply Prod.ext
    · apply Subtype.ext
      change x.1.val + s x.2.val - s ((monoidUnitModule S).mkQ (x.1.val + s x.2.val)) = x.1.val
      rw [map_add, hu, reducedExponentSection_apply S s hs, zero_add]
      abel
    · apply Subtype.ext
      change (monoidUnitModule S).mkQ (x.1.val + s x.2.val) = x.2.val
      rw [map_add, hu, reducedExponentSection_apply S s hs, zero_add]
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      change x.val + y.val - s ((monoidUnitModule S).mkQ (x.val + y.val)) =
        (x.val - s ((monoidUnitModule S).mkQ x.val)) +
          (y.val - s ((monoidUnitModule S).mkQ y.val))
      rw [map_add, map_add]
      abel
    · exact (pointedMonoidProjection S s hs).map_add x y

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.reducedExponentLattice_isTorsionFree
#print axioms PaperVerification.ToricCharacters.exists_reducedExponentSection
#print axioms PaperVerification.ToricCharacters.latticeUnitSplitEquiv
#print axioms PaperVerification.ToricCharacters.pointedMonoidPart_isPointed
#print axioms PaperVerification.ToricCharacters.pointedMonoidProjection_comp_inclusion
#print axioms PaperVerification.ToricCharacters.saturatedMonoidSplitEquiv
