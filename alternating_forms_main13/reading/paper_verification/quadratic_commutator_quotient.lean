module

public import PaperVerification.TwoStepCentralLie
public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.Algebra.RingQuot
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Tactic.Abel

/-!
# A commutator presentation and the genuine enveloping algebra

The source here is the actual quotient of the free associative algebra by
quadratic commutator relations in the kernel of a specified bracket map.
It is not defined as an enveloping algebra.  If its two commutator directions
are proved central, universal properties construct inverse algebra maps to
Mathlib's enveloping algebra of the actual central Lie algebra.

The centrality hypothesis is an intermediate algebraic condition; the
exterior cubic-injectivity argument must prove it before this theorem can
be used for Proposition 5.3.  The ordinary quadratic-dual annihilator
identification is also a separate required comparison.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.QuadraticCommutatorQuotient

open TwoStepCentralLie

variable {K ν Z : Type*} [Field K] [Fintype ν] [DecidableEq ν]
  [AddCommGroup Z] [Module K Z]

abbrev V := ν → K
abbrev PairCoordinates := (ν × ν) → K

variable (D : Data (K := K) (V := V (K := K) (ν := ν)) (Z := Z))

/-- The bracket on a formal linear combination of ordered pairs. -/
def bracketMap : PairCoordinates (K := K) (ν := ν) →ₗ[K] Z :=
  (Pi.basisFun K (ν × ν)).constr K
    (fun p => D.bilinear (Pi.basisFun K ν p.1) (Pi.basisFun K ν p.2))

/-- Surjectivity of the actual bracket coefficients identifies the second
degree with brackets of the original degree-one generators. -/
theorem degreeTwo_eq_span_generator_brackets
    (hD : Function.Surjective (bracketMap D)) :
    degreeTwo D=Submodule.span K (Set.range (fun p : ν × ν =>
      ⁅generator D (Pi.basisFun K ν p.1),generator D (Pi.basisFun K ν p.2)⁆)) := by
  apply le_antisymm
  · rintro x ⟨z,rfl⟩
    obtain ⟨a,rfl⟩ := hD z
    rw [←(Pi.basisFun K (ν × ν)).sum_repr a]
    simp only [map_sum,map_smul]
    apply Submodule.sum_mem
    intro p hp
    apply Submodule.smul_mem
    rw [bracketMap,Module.Basis.constr_basis]
    exact Submodule.subset_span ⟨p,rfl⟩
  · apply Submodule.span_le.mpr
    rintro x ⟨p,rfl⟩
    exact ⟨D.bilinear (Pi.basisFun K ν p.1) (Pi.basisFun K ν p.2),rfl⟩

section Commutators

variable {A : Type*} [Ring A] [Algebra K A]

def commutator (x y : A) : A := x*y-y*x

def commutatorMap (X : ν → A) : PairCoordinates (K := K) (ν := ν) →ₗ[K] A :=
  (Pi.basisFun K (ν × ν)).constr K (fun p => commutator (X p.1) (X p.2))

@[simp] theorem commutatorMap_basis (X : ν → A) (p : ν × ν) :
    commutatorMap X (Pi.basisFun K (ν × ν) p)=commutator (X p.1) (X p.2) := by
  simp [commutatorMap]

def commutatorBilinear (X : V (K := K) (ν := ν) →ₗ[K] A) :
    V (K := K) (ν := ν) →ₗ[K] V (K := K) (ν := ν) →ₗ[K] A :=
  LinearMap.mk₂ K (fun v w => commutator (X v) (X w))
    (by intros; simp only [commutator,map_add,add_mul,mul_add]; abel)
    (by intros; simp only [commutator,map_smul,smul_mul_assoc,mul_smul_comm,smul_sub])
    (by intros; simp only [commutator,map_add,add_mul,mul_add]; abel)
    (by intros; simp only [commutator,map_smul,smul_mul_assoc,mul_smul_comm,smul_sub])

@[simp] theorem commutatorBilinear_apply (X : V (K := K) (ν := ν) →ₗ[K] A) (v w) :
    commutatorBilinear X v w=commutator (X v) (X w) := rfl

end Commutators

/-- Relations are imposed in the free associative algebra itself. -/
inductive Relation : FreeAlgebra K ν → FreeAlgebra K ν → Prop
  | kernel (a : PairCoordinates (K := K) (ν := ν)) (ha : bracketMap D a=0) :
      Relation (commutatorMap (FreeAlgebra.ι K) a) 0

abbrev Algebra := RingQuot (Relation D)

def quotientMap : FreeAlgebra K ν →ₐ[K] Algebra D := RingQuot.mkAlgHom K (Relation D)

def X (i : ν) : Algebra D := quotientMap D (FreeAlgebra.ι K i)

def XLinear : V (K := K) (ν := ν) →ₗ[K] Algebra D :=
  (Pi.basisFun K ν).constr K (X D)

@[simp] theorem XLinear_basis (i : ν) : XLinear D (Pi.basisFun K ν i)=X D i := by
  simp [XLinear]

theorem quotientMap_commutator (a : PairCoordinates (K := K) (ν := ν)) :
    quotientMap D (commutatorMap (FreeAlgebra.ι K) a)=commutatorMap (X D) a := by
  have h : (quotientMap D).toLinearMap.comp (commutatorMap (FreeAlgebra.ι K))=
      commutatorMap (X D) := by
    apply (Pi.basisFun K (ν × ν)).ext
    intro p
    rw [LinearMap.comp_apply,commutatorMap_basis,commutatorMap_basis]
    simp only [AlgHom.toLinearMap_apply,commutator,map_sub,map_mul,X]
  exact LinearMap.congr_fun h a

theorem bracket_ker_le_commutator_ker :
    LinearMap.ker (bracketMap D) ≤ LinearMap.ker (commutatorMap (X D)) := by
  intro a ha
  change bracketMap D a=0 at ha
  change commutatorMap (X D) a=0
  rw [← quotientMap_commutator]
  exact (RingQuot.mkAlgHom_rel K (Relation.kernel a ha)).trans (map_zero _)

variable (hD : Function.Surjective (bracketMap D))

/-- The central-coordinate map is obtained by factoring the actual
commutator map through its proved kernel inclusion. -/
def centralMap : Z →ₗ[K] Algebra D :=
  (bracketMap D).liftOfSurjective hD
    ⟨commutatorMap (X D),bracket_ker_le_commutator_ker D⟩

@[simp] theorem centralMap_bracketMap (a : PairCoordinates (K := K) (ν := ν)) :
    centralMap D hD (bracketMap D a)=commutatorMap (X D) a := by
  simp [centralMap]

theorem X_commutator (i j : ν) :
    commutator (X D i) (X D j)=
      centralMap D hD (D.bilinear (Pi.basisFun K ν i) (Pi.basisFun K ν j)) := by
  have h := centralMap_bracketMap D hD (Pi.basisFun K (ν × ν) (i,j))
  rw [commutatorMap_basis] at h
  simpa only [bracketMap,Module.Basis.constr_basis] using h.symm

theorem XLinear_commutator (v w : V (K := K) (ν := ν)) :
    commutator (XLinear D v) (XLinear D w)=centralMap D hD (D.bilinear v w) := by
  have h : commutatorBilinear (XLinear D)=D.bilinear.compr₂ (centralMap D hD) := by
    apply (Pi.basisFun K ν).ext
    intro i
    apply (Pi.basisFun K ν).ext
    intro j
    simpa only [commutatorBilinear_apply,XLinear_basis,LinearMap.compr₂_apply]
      using X_commutator D hD i j
  exact LinearMap.congr_fun (LinearMap.congr_fun h v) w

/-- Commuting with each original generator implies commuting with every
element of the actual free-algebra quotient. -/
theorem commute_all_of_generators (z : Algebra D) (hz : ∀ i, Commute (X D i) z) :
    ∀ a : Algebra D, Commute a z := by
  intro a
  obtain ⟨a,rfl⟩ := RingQuot.mkAlgHom_surjective K (Relation D) a
  change Commute (quotientMap D a) z
  induction a using FreeAlgebra.induction with
  | grade0 c =>
      rw [AlgHom.commutes]
      exact Algebra.commutes c z
  | grade1 i => exact hz i
  | mul a b ha hb => simpa only [map_mul] using ha.mul_left hb
  | add a b ha hb => simpa only [map_add] using ha.add_left hb

section EnvelopingComparison

attribute [local instance 100] LieRing.ofAssociativeRing

variable (hcentral : ∀ i z, Commute (X D i) (centralMap D hD z))

def toEnvelopingFree : FreeAlgebra K ν →ₐ[K] UniversalEnvelopingAlgebra K (LieSpace D) :=
  FreeAlgebra.lift K (fun i =>
    UniversalEnvelopingAlgebra.ι K (generator D (Pi.basisFun K ν i)))

theorem toEnvelopingFree_commutator (a : PairCoordinates (K := K) (ν := ν)) :
    toEnvelopingFree D (commutatorMap (FreeAlgebra.ι K) a)=
      UniversalEnvelopingAlgebra.ι K (central D (bracketMap D a)) := by
  have h : (toEnvelopingFree D).toLinearMap.comp (commutatorMap (FreeAlgebra.ι K))=
      (UniversalEnvelopingAlgebra.ι K).toLinearMap.comp
        ((central D).comp (bracketMap D)) := by
    apply (Pi.basisFun K (ν × ν)).ext
    rintro ⟨i,j⟩
    simp only [LinearMap.comp_apply,AlgHom.toLinearMap_apply,commutatorMap_basis,commutator,map_sub,map_mul,
      toEnvelopingFree,FreeAlgebra.lift_ι_apply,bracketMap,Module.Basis.constr_basis]
    exact ((UniversalEnvelopingAlgebra.ι K).map_lie
      (generator D (Pi.basisFun K ν i)) (generator D (Pi.basisFun K ν j))).symm
  exact LinearMap.congr_fun h a

def toEnveloping : Algebra D →ₐ[K] UniversalEnvelopingAlgebra K (LieSpace D) :=
  RingQuot.liftAlgHom K ⟨toEnvelopingFree D,by
    intro a b h
    cases h with
    | kernel a ha =>
        rw [toEnvelopingFree_commutator,ha,map_zero,map_zero,map_zero]⟩

@[simp] theorem toEnveloping_X (i : ν) :
    toEnveloping D (X D i)=UniversalEnvelopingAlgebra.ι K
      (generator D (Pi.basisFun K ν i)) := by
  simp [toEnveloping,X,quotientMap,RingQuot.liftAlgHom_mkAlgHom_apply,toEnvelopingFree]

theorem toEnveloping_central (z : Z) :
    toEnveloping D (centralMap D hD z)=UniversalEnvelopingAlgebra.ι K (central D z) := by
  obtain ⟨a,rfl⟩ := hD z
  rw [centralMap_bracketMap,← quotientMap_commutator]
  rw [toEnveloping,quotientMap,RingQuot.liftAlgHom_mkAlgHom_apply,
    toEnvelopingFree_commutator]

def fromEnveloping : UniversalEnvelopingAlgebra K (LieSpace D) →ₐ[K] Algebra D :=
  TwoStepCentralLie.lift D (XLinear D) (centralMap D hD)
    (XLinear_commutator D hD)
    (fun v z => commute_all_of_generators D _ (fun i => hcentral i z) (XLinear D v))
    (fun z z' => commute_all_of_generators D _ (fun i => hcentral i z') (centralMap D hD z))

@[simp] theorem fromEnveloping_generator (v : V (K := K) (ν := ν)) :
    fromEnveloping D hD hcentral (UniversalEnvelopingAlgebra.ι K (generator D v))=
      XLinear D v := by
  unfold fromEnveloping
  exact TwoStepCentralLie.lift_generator D _ _ _ _ _ v

@[simp] theorem fromEnveloping_central (z : Z) :
    fromEnveloping D hD hcentral (UniversalEnvelopingAlgebra.ι K (central D z))=
      centralMap D hD z := by
  unfold fromEnveloping
  exact TwoStepCentralLie.lift_central D _ _ _ _ _ z

theorem from_toEnveloping :
    (fromEnveloping D hD hcentral).comp (toEnveloping D)=AlgHom.id K (Algebra D) := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext i
  change fromEnveloping D hD hcentral (toEnveloping D (X D i))=X D i
  rw [toEnveloping_X,fromEnveloping_generator,XLinear_basis]

theorem to_fromEnveloping :
    (toEnveloping D).comp (fromEnveloping D hD hcentral)=
      AlgHom.id K (UniversalEnvelopingAlgebra K (LieSpace D)) := by
  have hX (v : V (K := K) (ν := ν)) :
      toEnveloping D (XLinear D v)=UniversalEnvelopingAlgebra.ι K (generator D v) := by
    have h : (toEnveloping D).toLinearMap.comp (XLinear D)=
        (UniversalEnvelopingAlgebra.ι K).toLinearMap.comp (generator D) := by
      apply (Pi.basisFun K ν).ext
      intro i
      simp only [LinearMap.comp_apply,AlgHom.toLinearMap_apply,LieHom.coe_toLinearMap,
      XLinear_basis,toEnveloping_X]
    exact LinearMap.congr_fun h v
  apply UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro x
  rw [← generator_add_central D x]
  simp only [LieHom.coe_comp,AlgHom.coe_toLieHom,Function.comp_apply,
    AlgHom.comp_apply,AlgHom.id_apply,map_add,fromEnveloping_generator,
    fromEnveloping_central,hX,toEnveloping_central]

/-- The two explicitly constructed maps are inverses.  This theorem uses
the actual free quotient and Mathlib's ordinary universal enveloping algebra. -/
def envelopingEquiv : Algebra D ≃ₐ[K] UniversalEnvelopingAlgebra K (LieSpace D) :=
  AlgEquiv.ofAlgHom (toEnveloping D) (fromEnveloping D hD hcentral)
    (to_fromEnveloping D hD hcentral) (from_toEnveloping D hD hcentral)

end EnvelopingComparison
end PaperVerification.QuadraticCommutatorQuotient
