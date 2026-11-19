module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Tactic.Abel

/-!
# Genuine integral acyclic-carrier constructions

A carrier includes actual chain complexes, monic inclusions, compatible
face maps, and explicit proofs of augmented and positive-degree exactness.
The constructions below lift genuine cycles recursively to extend a
vertex map and to compare two carried chain maps by an actual homotopy.
None of these carrier properties is asserted for a new geometric example
without its own proof.

This is an exact extraction of the CycleLifts and AcyclicCarriers sections
of BondalThomsen/Cohomology/ConvexNerve/AcyclicCarrierAssembly.lean,
commit 9a2bdcdcf6b25710459f7f476c9c62de3039b7bb. Only the enclosing
namespace and explicit imports are changed; the generic proof body is
unchanged. Candidate source, pending pinned compilation.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open scoped Classical Simplicial

attribute [local instance] Classical.decEq

namespace ToricPower.CechAcyclicCarrier

section CycleLifts

noncomputable def integerCycleLift (sequence : ShortComplex AddCommGrpCat.{0})
    (exact : sequence.Exact) (cycle : AddCommGrpCat.of ℤ ⟶ sequence.X₂)
    (closed : cycle ≫ sequence.g = 0) : AddCommGrpCat.of ℤ ⟶ sequence.X₁ := by
  have closedValue : sequence.g (cycle (1 : ℤ)) = 0 :=
    ConcreteCategory.congr_hom closed (1 : ℤ)
  let filling := ((ShortComplex.ab_exact_iff sequence).mp exact (cycle (1 : ℤ)) closedValue).choose
  exact AddCommGrpCat.ofHom (zmultiplesHom sequence.X₁ filling)

theorem integerCycleLift_comp (sequence : ShortComplex AddCommGrpCat.{0})
    (exact : sequence.Exact) (cycle : AddCommGrpCat.of ℤ ⟶ sequence.X₂)
    (closed : cycle ≫ sequence.g = 0) :
    integerCycleLift sequence exact cycle closed ≫ sequence.f = cycle := by
  apply AddCommGrpCat.int_hom_ext
  change sequence.f ((1 : ℤ) • _) = cycle 1
  rw [one_zsmul]
  exact ((ShortComplex.ab_exact_iff sequence).mp exact (cycle 1)
    (ConcreteCategory.congr_hom closed 1)).choose_spec

end CycleLifts

section AcyclicCarriers

variable (simplicial : SSet.{0}) (target : ChainComplex AddCommGrpCat.{0} ℕ)
variable {augmentationObject : AddCommGrpCat.{0}}
variable (augmentation : target.X 0 ⟶ augmentationObject)

structure IntegralAcyclicCarrier where
  complex : ∀ degree, simplicial _⦋degree⦌ → ChainComplex AddCommGrpCat.{0} ℕ
  inclusion : ∀ degree simplex, complex degree simplex ⟶ target
  inclusion_mono : ∀ degree simplex component, Mono ((inclusion degree simplex).f component)
  faceMap : ∀ degree (deleted : Fin (degree + 2)) (simplex : simplicial _⦋degree + 1⦌),
    complex degree (simplicial.δ deleted simplex) ⟶ complex (degree + 1) simplex
  faceMap_inclusion : ∀ degree deleted simplex,
    faceMap degree deleted simplex ≫ inclusion (degree + 1) simplex =
      inclusion degree (simplicial.δ deleted simplex)
  augmentation_zero : ∀ degree simplex,
    (complex degree simplex).d 1 0 ≫ (inclusion degree simplex).f 0 ≫ augmentation = 0
  exact_zero : ∀ degree simplex,
    (ShortComplex.mk ((complex degree simplex).d 1 0)
      ((inclusion degree simplex).f 0 ≫ augmentation)
      (augmentation_zero degree simplex)).Exact
  exact_positive : ∀ degree simplex component,
    (complex degree simplex).ExactAt (component + 1)

namespace IntegralAcyclicCarrier

variable {simplicial target augmentation}
variable (carrier : IntegralAcyclicCarrier simplicial target augmentation)

structure CarriedIntegralChainMap
    (mapping : simplicial.chainComplex (AddCommGrpCat.of ℤ) ⟶ target) where
  value : ∀ degree simplex, AddCommGrpCat.of ℤ ⟶ (carrier.complex degree simplex).X degree
  value_inclusion : ∀ degree simplex,
    value degree simplex ≫ (carrier.inclusion degree simplex).f degree =
      simplicial.ιChainComplex simplex ≫ mapping.f degree

def CarrierHomotopyValues (degree : ℕ) :=
  ∀ simplex : simplicial _⦋degree⦌,
    AddCommGrpCat.of ℤ ⟶ (carrier.complex degree simplex).X (degree + 1)

noncomputable def carrierHomotopyComponent (degree : ℕ)
    (values : carrier.CarrierHomotopyValues degree) :
    (simplicial.chainComplex (AddCommGrpCat.of ℤ)).X degree ⟶ target.X (degree + 1) :=
  Sigma.desc fun simplex => values simplex ≫ (carrier.inclusion degree simplex).f (degree + 1)

theorem carrierHomotopyComponent_generator (degree : ℕ)
    (values : carrier.CarrierHomotopyValues degree) (simplex : simplicial _⦋degree⦌) :
    simplicial.ιChainComplex simplex ≫ carrier.carrierHomotopyComponent degree values =
      values simplex ≫ (carrier.inclusion degree simplex).f (degree + 1) :=
  Sigma.ι_comp_desc _ _

variable {mapping : simplicial.chainComplex (AddCommGrpCat.of ℤ) ⟶ target}
variable (carried : carrier.CarriedIntegralChainMap mapping)

noncomputable def initialCarrierValues
    (augmentationZero : mapping.f 0 ≫ augmentation = 0) : carrier.CarrierHomotopyValues 0 :=
  fun simplex => integerCycleLift _ (carrier.exact_zero 0 simplex) (carried.value 0 simplex) (by
    rw [← Category.assoc, carried.value_inclusion, Category.assoc, augmentationZero, comp_zero])

theorem initialCarrierComponent_boundary
    (augmentationZero : mapping.f 0 ≫ augmentation = 0) :
    carrier.carrierHomotopyComponent 0 (carrier.initialCarrierValues carried augmentationZero) ≫
      target.d 1 0 = mapping.f 0 := by
  apply SSet.chainComplex_hom_ext
  intro simplex
  rw [← Category.assoc, carrierHomotopyComponent_generator, Category.assoc,
    (carrier.inclusion 0 simplex).comm]
  rw [← Category.assoc, initialCarrierValues, integerCycleLift_comp, carried.value_inclusion]

noncomputable def carrierResidual (degree : ℕ)
    (values : carrier.CarrierHomotopyValues degree) (simplex : simplicial _⦋degree + 1⦌) :
    AddCommGrpCat.of ℤ ⟶ (carrier.complex (degree + 1) simplex).X (degree + 1) :=
  carried.value (degree + 1) simplex -
    ∑ deleted : Fin (degree + 2), ((-1 : ℤ) ^ deleted.val) •
      (values (simplicial.δ deleted simplex) ≫ (carrier.faceMap degree deleted simplex).f (degree + 1))

theorem carrierResidual_inclusion (degree : ℕ)
    (values : carrier.CarrierHomotopyValues degree) (simplex : simplicial _⦋degree + 1⦌) :
    carrier.carrierResidual carried degree values simplex ≫
      (carrier.inclusion (degree + 1) simplex).f (degree + 1) =
    simplicial.ιChainComplex simplex ≫
      (mapping.f (degree + 1) -
        (simplicial.chainComplex (AddCommGrpCat.of ℤ)).d (degree + 1) degree ≫
          carrier.carrierHomotopyComponent degree values) := by
  rw [carrierResidual, sub_comp, carried.value_inclusion, sum_comp, comp_sub,
    ← Category.assoc, SSet.ιChainComplex_d, sum_comp]
  congr 1
  apply Finset.sum_congr rfl
  intro deleted _member
  rw [zsmul_comp, zsmul_comp, Category.assoc, ← HomologicalComplex.comp_f,
    carrier.faceMap_inclusion, carrierHomotopyComponent_generator]

theorem carrierResidual_closed (degree : ℕ)
    (values : carrier.CarrierHomotopyValues degree)
    (previous : (simplicial.chainComplex (AddCommGrpCat.of ℤ)).X (degree - 1) ⟶ target.X degree)
    (equation : mapping.f degree =
      (simplicial.chainComplex (AddCommGrpCat.of ℤ)).d degree (degree - 1) ≫ previous +
        carrier.carrierHomotopyComponent degree values ≫ target.d (degree + 1) degree)
    (simplex : simplicial _⦋degree + 1⦌) :
    carrier.carrierResidual carried degree values simplex ≫
      (carrier.complex (degree + 1) simplex).d (degree + 1) degree = 0 := by
  let := carrier.inclusion_mono (degree + 1) simplex degree
  apply (cancel_mono ((carrier.inclusion (degree + 1) simplex).f degree)).mp
  rw [zero_comp, Category.assoc, ← (carrier.inclusion (degree + 1) simplex).comm,
    ← Category.assoc, carrierResidual_inclusion, Category.assoc, sub_comp,
    mapping.comm, Category.assoc, equation, comp_add, ← Category.assoc,
    HomologicalComplex.d_comp_d, zero_comp, zero_add, sub_self, comp_zero]

noncomputable def nextCarrierValues (degree : ℕ)
    (values : carrier.CarrierHomotopyValues degree)
    (previous : (simplicial.chainComplex (AddCommGrpCat.of ℤ)).X (degree - 1) ⟶ target.X degree)
    (equation : mapping.f degree =
      (simplicial.chainComplex (AddCommGrpCat.of ℤ)).d degree (degree - 1) ≫ previous +
        carrier.carrierHomotopyComponent degree values ≫ target.d (degree + 1) degree) :
    carrier.CarrierHomotopyValues (degree + 1) := fun simplex =>
  integerCycleLift ((carrier.complex (degree + 1) simplex).sc' (degree + 2) (degree + 1) degree)
    ((HomologicalComplex.exactAt_iff' _ (degree + 2) (degree + 1) degree
      (by simp) (by simp)).mp (carrier.exact_positive (degree + 1) simplex degree))
    (carrier.carrierResidual carried degree values simplex)
    (carrier.carrierResidual_closed carried degree values previous equation simplex)

theorem nextCarrierComponent_boundary (degree : ℕ)
    (values : carrier.CarrierHomotopyValues degree)
    (previous : (simplicial.chainComplex (AddCommGrpCat.of ℤ)).X (degree - 1) ⟶ target.X degree)
    (equation : mapping.f degree =
      (simplicial.chainComplex (AddCommGrpCat.of ℤ)).d degree (degree - 1) ≫ previous +
        carrier.carrierHomotopyComponent degree values ≫ target.d (degree + 1) degree) :
    carrier.carrierHomotopyComponent (degree + 1)
        (carrier.nextCarrierValues carried degree values previous equation) ≫
      target.d (degree + 2) (degree + 1) =
    mapping.f (degree + 1) -
      (simplicial.chainComplex (AddCommGrpCat.of ℤ)).d (degree + 1) degree ≫
        carrier.carrierHomotopyComponent degree values := by
  apply SSet.chainComplex_hom_ext
  intro simplex
  rw [← Category.assoc, carrierHomotopyComponent_generator, Category.assoc,
    (carrier.inclusion (degree + 1) simplex).comm, ← Category.assoc]
  have filling := integerCycleLift_comp
    ((carrier.complex (degree + 1) simplex).sc' (degree + 2) (degree + 1) degree)
    ((HomologicalComplex.exactAt_iff' _ (degree + 2) (degree + 1) degree
      (by simp) (by simp)).mp (carrier.exact_positive (degree + 1) simplex degree))
    (carrier.carrierResidual carried degree values simplex)
    (carrier.carrierResidual_closed carried degree values previous equation simplex)
  change carrier.nextCarrierValues carried degree values previous equation simplex ≫
    (carrier.complex (degree + 1) simplex).d (degree + 2) (degree + 1) =
      carrier.carrierResidual carried degree values simplex at filling
  rw [filling, carrierResidual_inclusion]

noncomputable def recursiveCarrierHomotopyValues
    (augmentationZero : mapping.f 0 ≫ augmentation = 0) :
    (degree : ℕ) → Σ' (previous :
      (simplicial.chainComplex (AddCommGrpCat.of ℤ)).X (degree - 1) ⟶ target.X degree)
      (values : carrier.CarrierHomotopyValues degree),
      mapping.f degree =
        ((simplicial.chainComplex (AddCommGrpCat.of ℤ)).d degree (degree - 1) ≫ previous +
          carrier.carrierHomotopyComponent degree values ≫ target.d (degree + 1) degree) :=
  Nat.rec
    ⟨0, carrier.initialCarrierValues carried augmentationZero, by
      rw [comp_zero, zero_add]
      exact (carrier.initialCarrierComponent_boundary carried augmentationZero).symm⟩
    (fun degree previousData => ⟨carrier.carrierHomotopyComponent degree previousData.2.1,
      carrier.nextCarrierValues carried degree previousData.2.1 previousData.1 previousData.2.2, by
        rw [carrier.nextCarrierComponent_boundary]
        change mapping.f (degree + 1) =
          ((simplicial.chainComplex (AddCommGrpCat.of ℤ)).d (degree + 1) degree ≫
            carrier.carrierHomotopyComponent degree previousData.2.1) +
          (mapping.f (degree + 1) -
            (simplicial.chainComplex (AddCommGrpCat.of ℤ)).d (degree + 1) degree ≫
              carrier.carrierHomotopyComponent degree previousData.2.1)
        abel⟩)

noncomputable def globalCarrierHomotopyComponent
    (augmentationZero : mapping.f 0 ≫ augmentation = 0) (degree : ℕ) :
    (simplicial.chainComplex (AddCommGrpCat.of ℤ)).X degree ⟶ target.X (degree + 1) :=
  carrier.carrierHomotopyComponent degree
    (carrier.recursiveCarrierHomotopyValues carried augmentationZero degree).2.1

theorem globalCarrierHomotopyComponent_zero
    (augmentationZero : mapping.f 0 ≫ augmentation = 0) :
    carrier.globalCarrierHomotopyComponent carried augmentationZero 0 ≫ target.d 1 0 = mapping.f 0 :=
  carrier.initialCarrierComponent_boundary carried augmentationZero

theorem globalCarrierHomotopyComponent_succ
    (augmentationZero : mapping.f 0 ≫ augmentation = 0) (degree : ℕ) :
    mapping.f (degree + 1) =
      (simplicial.chainComplex (AddCommGrpCat.of ℤ)).d (degree + 1) degree ≫
        carrier.globalCarrierHomotopyComponent carried augmentationZero degree +
      carrier.globalCarrierHomotopyComponent carried augmentationZero (degree + 1) ≫
        target.d (degree + 2) (degree + 1) :=
  (carrier.recursiveCarrierHomotopyValues carried augmentationZero (degree + 1)).2.2

noncomputable def carriedNullHomotopy
    (augmentationZero : mapping.f 0 ≫ augmentation = 0) : Homotopy mapping 0 where
  hom degree component := if equality : degree + 1 = component then
    carrier.globalCarrierHomotopyComponent carried augmentationZero degree ≫
      eqToHom (congrArg target.X equality) else 0
  zero degree component unrelated := by
    rw [dite_eq_right]
    exact unrelated
  comm degree := by
    rw [HomologicalComplex.zero_f_apply, add_zero, Homotopy.prevD_chainComplex]
    cases degree with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex, zero_add]
      simpa only [dite_true, eqToHom_refl, Category.comp_id] using
        (carrier.globalCarrierHomotopyComponent_zero carried augmentationZero).symm
    | succ degree =>
      rw [Homotopy.dNext_succ_chainComplex]
      simpa only [dite_true, eqToHom_refl, Category.comp_id] using
        carrier.globalCarrierHomotopyComponent_succ carried augmentationZero degree

variable {first second : simplicial.chainComplex (AddCommGrpCat.of ℤ) ⟶ target}

def subtractCarriedMaps (firstCarried : carrier.CarriedIntegralChainMap first)
    (secondCarried : carrier.CarriedIntegralChainMap second) :
    carrier.CarriedIntegralChainMap (first - second) where
  value degree simplex := firstCarried.value degree simplex - secondCarried.value degree simplex
  value_inclusion degree simplex := by
    rw [sub_comp, firstCarried.value_inclusion, secondCarried.value_inclusion,
      HomologicalComplex.sub_f_apply, comp_sub]

noncomputable def carriedMapsHomotopy (firstCarried : carrier.CarriedIntegralChainMap first)
    (secondCarried : carrier.CarriedIntegralChainMap second)
    (sameAugmentation : first.f 0 ≫ augmentation = second.f 0 ≫ augmentation) :
    Homotopy first second :=
  Homotopy.equivSubZero.symm
    (carrier.carriedNullHomotopy (carrier.subtractCarriedMaps firstCarried secondCarried) (by
      rw [HomologicalComplex.sub_f_apply, sub_comp, sameAugmentation, sub_self]))

def CarrierMapValues (degree : ℕ) :=
  ∀ simplex : simplicial _⦋degree⦌,
    AddCommGrpCat.of ℤ ⟶ (carrier.complex degree simplex).X degree

noncomputable def carrierMapComponent (degree : ℕ) (values : carrier.CarrierMapValues degree) :
    (simplicial.chainComplex (AddCommGrpCat.of ℤ)).X degree ⟶ target.X degree :=
  Sigma.desc fun simplex => values simplex ≫ (carrier.inclusion degree simplex).f degree

theorem carrierMapComponent_generator (degree : ℕ) (values : carrier.CarrierMapValues degree)
    (simplex : simplicial _⦋degree⦌) :
    simplicial.ιChainComplex simplex ≫ carrier.carrierMapComponent degree values =
      values simplex ≫ (carrier.inclusion degree simplex).f degree :=
  Sigma.ι_comp_desc _ _

noncomputable def carrierMapBoundary (degree : ℕ) (values : carrier.CarrierMapValues degree)
    (simplex : simplicial _⦋degree + 1⦌) :
    AddCommGrpCat.of ℤ ⟶ (carrier.complex (degree + 1) simplex).X degree :=
  ∑ deleted : Fin (degree + 2), ((-1 : ℤ) ^ deleted.val) •
    (values (simplicial.δ deleted simplex) ≫ (carrier.faceMap degree deleted simplex).f degree)

theorem carrierMapBoundary_inclusion (degree : ℕ) (values : carrier.CarrierMapValues degree)
    (simplex : simplicial _⦋degree + 1⦌) :
    carrier.carrierMapBoundary degree values simplex ≫ (carrier.inclusion (degree + 1) simplex).f degree =
      simplicial.ιChainComplex simplex ≫
        (simplicial.chainComplex (AddCommGrpCat.of ℤ)).d (degree + 1) degree ≫
          carrier.carrierMapComponent degree values := by
  rw [carrierMapBoundary, sum_comp, ← Category.assoc, SSet.ιChainComplex_d, sum_comp]
  apply Finset.sum_congr rfl
  intro deleted _member
  rw [zsmul_comp, zsmul_comp, Category.assoc, ← HomologicalComplex.comp_f,
    carrier.faceMap_inclusion, carrierMapComponent_generator]

noncomputable def initialCarrierMapValues (vertices : carrier.CarrierMapValues 0)
    (compatible : ∀ simplex : simplicial _⦋1⦌,
      vertices (simplicial.δ 0 simplex) ≫ (carrier.inclusion 0 (simplicial.δ 0 simplex)).f 0 ≫ augmentation =
      vertices (simplicial.δ 1 simplex) ≫ (carrier.inclusion 0 (simplicial.δ 1 simplex)).f 0 ≫ augmentation) :
    carrier.CarrierMapValues 1 := fun simplex =>
  integerCycleLift _ (carrier.exact_zero 1 simplex) (carrier.carrierMapBoundary 0 vertices simplex) (by
    rw [← Category.assoc, carrierMapBoundary_inclusion, ← Category.assoc, SSet.ιChainComplex_d,
      Fin.sum_univ_two, Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one,
      neg_smul, one_smul, add_comp, neg_comp, carrierMapComponent_generator,
      carrierMapComponent_generator, add_comp]
    simp only [neg_comp, Category.assoc]
    rw [compatible, add_neg_cancel])

theorem initialCarrierMapComponent_boundary (vertices : carrier.CarrierMapValues 0)
    (compatible : ∀ simplex : simplicial _⦋1⦌,
      vertices (simplicial.δ 0 simplex) ≫ (carrier.inclusion 0 (simplicial.δ 0 simplex)).f 0 ≫ augmentation =
      vertices (simplicial.δ 1 simplex) ≫ (carrier.inclusion 0 (simplicial.δ 1 simplex)).f 0 ≫ augmentation) :
    carrier.carrierMapComponent 1 (carrier.initialCarrierMapValues vertices compatible) ≫ target.d 1 0 =
      (simplicial.chainComplex (AddCommGrpCat.of ℤ)).d 1 0 ≫ carrier.carrierMapComponent 0 vertices := by
  apply SSet.chainComplex_hom_ext
  intro simplex
  rw [← Category.assoc, carrierMapComponent_generator, Category.assoc,
    (carrier.inclusion 1 simplex).comm, ← Category.assoc, initialCarrierMapValues,
    integerCycleLift_comp, carrierMapBoundary_inclusion]

theorem carrierMapBoundary_closed (degree : ℕ) (previous : carrier.CarrierMapValues degree)
    (values : carrier.CarrierMapValues (degree + 1))
    (equation : carrier.carrierMapComponent (degree + 1) values ≫ target.d (degree + 1) degree =
      (simplicial.chainComplex (AddCommGrpCat.of ℤ)).d (degree + 1) degree ≫
        carrier.carrierMapComponent degree previous)
    (simplex : simplicial _⦋degree + 2⦌) :
    carrier.carrierMapBoundary (degree + 1) values simplex ≫
      (carrier.complex (degree + 2) simplex).d (degree + 1) degree = 0 := by
  let := carrier.inclusion_mono (degree + 2) simplex degree
  apply (cancel_mono ((carrier.inclusion (degree + 2) simplex).f degree)).mp
  rw [zero_comp, Category.assoc, ← (carrier.inclusion (degree + 2) simplex).comm,
    ← Category.assoc, carrierMapBoundary_inclusion, Category.assoc, Category.assoc, equation,
    HomologicalComplex.d_comp_d_assoc, zero_comp, comp_zero]

noncomputable def nextCarrierMapValues (degree : ℕ) (previous : carrier.CarrierMapValues degree)
    (values : carrier.CarrierMapValues (degree + 1))
    (equation : carrier.carrierMapComponent (degree + 1) values ≫ target.d (degree + 1) degree =
      (simplicial.chainComplex (AddCommGrpCat.of ℤ)).d (degree + 1) degree ≫
        carrier.carrierMapComponent degree previous) :
    carrier.CarrierMapValues (degree + 2) := fun simplex =>
  integerCycleLift ((carrier.complex (degree + 2) simplex).sc' (degree + 2) (degree + 1) degree)
    ((HomologicalComplex.exactAt_iff' _ (degree + 2) (degree + 1) degree
      (by simp) (by simp)).mp (carrier.exact_positive (degree + 2) simplex degree))
    (carrier.carrierMapBoundary (degree + 1) values simplex)
    (carrier.carrierMapBoundary_closed degree previous values equation simplex)

theorem nextCarrierMapComponent_boundary (degree : ℕ) (previous : carrier.CarrierMapValues degree)
    (values : carrier.CarrierMapValues (degree + 1))
    (equation : carrier.carrierMapComponent (degree + 1) values ≫ target.d (degree + 1) degree =
      (simplicial.chainComplex (AddCommGrpCat.of ℤ)).d (degree + 1) degree ≫
        carrier.carrierMapComponent degree previous) :
    carrier.carrierMapComponent (degree + 2) (carrier.nextCarrierMapValues degree previous values equation) ≫
      target.d (degree + 2) (degree + 1) =
    (simplicial.chainComplex (AddCommGrpCat.of ℤ)).d (degree + 2) (degree + 1) ≫
      carrier.carrierMapComponent (degree + 1) values := by
  apply SSet.chainComplex_hom_ext
  intro simplex
  rw [← Category.assoc, carrierMapComponent_generator, Category.assoc,
    (carrier.inclusion (degree + 2) simplex).comm, ← Category.assoc]
  have filling := integerCycleLift_comp
    ((carrier.complex (degree + 2) simplex).sc' (degree + 2) (degree + 1) degree)
    ((HomologicalComplex.exactAt_iff' _ (degree + 2) (degree + 1) degree
      (by simp) (by simp)).mp (carrier.exact_positive (degree + 2) simplex degree))
    (carrier.carrierMapBoundary (degree + 1) values simplex)
    (carrier.carrierMapBoundary_closed degree previous values equation simplex)
  change carrier.nextCarrierMapValues degree previous values equation simplex ≫
    (carrier.complex (degree + 2) simplex).d (degree + 2) (degree + 1) =
      carrier.carrierMapBoundary (degree + 1) values simplex at filling
  rw [filling, carrierMapBoundary_inclusion]

noncomputable def recursiveCarrierMapValues (vertices : carrier.CarrierMapValues 0)
    (compatible : ∀ simplex : simplicial _⦋1⦌,
      vertices (simplicial.δ 0 simplex) ≫ (carrier.inclusion 0 (simplicial.δ 0 simplex)).f 0 ≫ augmentation =
      vertices (simplicial.δ 1 simplex) ≫ (carrier.inclusion 0 (simplicial.δ 1 simplex)).f 0 ≫ augmentation) :
    (degree : ℕ) → Σ' (previous : carrier.CarrierMapValues degree)
      (values : carrier.CarrierMapValues (degree + 1)),
      carrier.carrierMapComponent (degree + 1) values ≫ target.d (degree + 1) degree =
        (simplicial.chainComplex (AddCommGrpCat.of ℤ)).d (degree + 1) degree ≫
          carrier.carrierMapComponent degree previous :=
  Nat.rec ⟨vertices, carrier.initialCarrierMapValues vertices compatible,
    carrier.initialCarrierMapComponent_boundary vertices compatible⟩
    (fun degree previousData =>
      ⟨previousData.2.1, carrier.nextCarrierMapValues degree previousData.1 previousData.2.1 previousData.2.2,
        carrier.nextCarrierMapComponent_boundary degree previousData.1 previousData.2.1 previousData.2.2⟩)

noncomputable def extendCarriedVertexMap (vertices : carrier.CarrierMapValues 0)
    (compatible : ∀ simplex : simplicial _⦋1⦌,
      vertices (simplicial.δ 0 simplex) ≫ (carrier.inclusion 0 (simplicial.δ 0 simplex)).f 0 ≫ augmentation =
      vertices (simplicial.δ 1 simplex) ≫ (carrier.inclusion 0 (simplicial.δ 1 simplex)).f 0 ≫ augmentation) :
    simplicial.chainComplex (AddCommGrpCat.of ℤ) ⟶ target where
  f degree := carrier.carrierMapComponent degree
    (carrier.recursiveCarrierMapValues vertices compatible degree).1
  comm' degree component adjacent := by
    rcases adjacent with (rfl : component + 1 = degree)
    exact (carrier.recursiveCarrierMapValues vertices compatible component).2.2

noncomputable def extendCarriedVertexMap_carried (vertices : carrier.CarrierMapValues 0)
    (compatible : ∀ simplex : simplicial _⦋1⦌,
      vertices (simplicial.δ 0 simplex) ≫ (carrier.inclusion 0 (simplicial.δ 0 simplex)).f 0 ≫ augmentation =
      vertices (simplicial.δ 1 simplex) ≫ (carrier.inclusion 0 (simplicial.δ 1 simplex)).f 0 ≫ augmentation) :
    carrier.CarriedIntegralChainMap (carrier.extendCarriedVertexMap vertices compatible) where
  value degree := (carrier.recursiveCarrierMapValues vertices compatible degree).1
  value_inclusion degree simplex :=
    (carrier.carrierMapComponent_generator degree
      (carrier.recursiveCarrierMapValues vertices compatible degree).1 simplex).symm

end IntegralAcyclicCarrier

end AcyclicCarriers

end ToricPower.CechAcyclicCarrier
