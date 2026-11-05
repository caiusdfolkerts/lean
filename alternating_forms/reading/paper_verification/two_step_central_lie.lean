module

public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.Abel

/-!
# The genuine central two-step Lie algebra and its universal maps

An alternating bilinear map `B : V × V → Z` defines the ordinary Lie
algebra `V ⊕ Z`, with `Z` central and `[v,w]=B(v,w)`.  No Lie superalgebra
convention is used.  The universal maps below go to Mathlib's actual
universal enveloping algebra, not to a separately defined surrogate.

This supporting source is a proof candidate until checked with its complete
dependency closure.  It does not assert Proposition 5.3 by itself.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.TwoStepCentralLie

variable {K V Z : Type*} [CommRing K]
  [AddCommGroup V] [Module K V] [AddCommGroup Z] [Module K Z]

/-- The actual alternating bilinear bracket data. -/
structure Data where
  bilinear : V →ₗ[K] V →ₗ[K] Z
  alternating : ∀ v, bilinear v v=0

/-- The underlying vector space is the literal direct sum of generators
and central directions.  The data parameter keeps distinct Lie brackets
on this vector space distinct at the type level. -/
def LieSpace (D : Data (K := K) (V := V) (Z := Z)) := V × Z

variable (D : Data (K := K) (V := V) (Z := Z))

instance : AddCommGroup (LieSpace D) := inferInstanceAs (AddCommGroup (V × Z))
instance : Module K (LieSpace D) := inferInstanceAs (Module K (V × Z))

def coordinates : LieSpace D ≃ₗ[K] V × Z := LinearEquiv.refl K _

def generator : V →ₗ[K] LieSpace D := LinearMap.inl K V Z
def central : Z →ₗ[K] LieSpace D := LinearMap.inr K V Z

@[simp] theorem coordinates_generator (v : V) : coordinates D (generator D v)=(v,0) := rfl
@[simp] theorem coordinates_central (z : Z) : coordinates D (central D z)=(0,z) := rfl

instance : Bracket (LieSpace D) (LieSpace D) where
  bracket x y := ((0 : V),D.bilinear x.1 y.1)

@[simp] theorem bracket_coordinates (x y : LieSpace D) :
    coordinates D ⁅x,y⁆=((0 : V),D.bilinear x.1 y.1) := rfl

instance : LieRing (LieSpace D) where
  toAddCommGroup := inferInstanceAs (AddCommGroup (LieSpace D))
  toBracket := inferInstanceAs (Bracket (LieSpace D) (LieSpace D))
  add_lie x y z := by
    apply (coordinates D).injective
    change ((0 : V),D.bilinear (x.1+y.1) z.1) =
      ((0 : V),D.bilinear x.1 z.1)+((0 : V),D.bilinear y.1 z.1)
    simp only [map_add, LinearMap.add_apply, Prod.mk_add_mk, zero_add]
  lie_add x y z := by
    apply (coordinates D).injective
    change ((0 : V),D.bilinear x.1 (y.1+z.1)) =
      ((0 : V),D.bilinear x.1 y.1)+((0 : V),D.bilinear x.1 z.1)
    simp only [map_add, Prod.mk_add_mk, zero_add]
  lie_self x := by
    change ((0 : V),D.bilinear x.1 x.1)=((0 : V),(0 : Z))
    rw [D.alternating]
  leibniz_lie x y z := by
    apply (coordinates D).injective
    change ((0 : V),D.bilinear x.1 0)=((0 : V),D.bilinear 0 z.1)+((0 : V),D.bilinear y.1 0)
    simp

instance : LieAlgebra K (LieSpace D) where
  toModule := inferInstanceAs (Module K (LieSpace D))
  lie_smul t x y := by
    apply (coordinates D).injective
    change ((0 : V),D.bilinear x.1 (t • y.1))=t • ((0 : V),D.bilinear x.1 y.1)
    simp

@[simp] theorem generator_bracket (v w : V) :
    ⁅generator D v,generator D w⁆=central D (D.bilinear v w) := rfl

@[simp] theorem central_bracket (z : Z) (x : LieSpace D) : ⁅central D z,x⁆=0 := by
  change ((0 : V),D.bilinear 0 x.1)=((0 : V),(0 : Z))
  simp

@[simp] theorem bracket_central (x : LieSpace D) (z : Z) : ⁅x,central D z⁆=0 := by
  change ((0 : V),D.bilinear x.1 0)=((0 : V),(0 : Z))
  simp

/-- Every threefold bracket vanishes in the actual Lie algebra. -/
theorem bracket_bracket_eq_zero (x y z : LieSpace D) : ⁅⁅x,y⁆,z⁆=0 := by
  change ((0 : V),D.bilinear 0 z.1)=((0 : V),(0 : Z))
  simp

@[simp] theorem bracket_nested_eq_zero (x y z : LieSpace D) : ⁅x,⁅y,z⁆⁆=0 := by
  change ((0 : V),D.bilinear x.1 0)=((0 : V),(0 : Z))
  simp

theorem generator_injective : Function.Injective (generator D) := by
  intro v w h
  exact congrArg Prod.fst h

theorem central_injective : Function.Injective (central D) := by
  intro v w h
  exact congrArg Prod.snd h

@[simp] theorem generator_add_central (x : LieSpace D) :
    generator D x.1+central D x.2=x := by
  apply (coordinates D).injective
  change (x.1,0)+(0,x.2)=(x.1,x.2)
  simp

/-- The two homogeneous generator subspaces are literal linear-map ranges. -/
def degreeOne : Submodule K (LieSpace D) := LinearMap.range (generator D)
def degreeTwo : Submodule K (LieSpace D) := LinearMap.range (central D)

def degreeOneEquiv : V ≃ₗ[K] degreeOne D :=
  LinearEquiv.ofInjective (generator D) (generator_injective D)

def degreeTwoEquiv : Z ≃ₗ[K] degreeTwo D :=
  LinearEquiv.ofInjective (central D) (central_injective D)

theorem degree_subspaces_disjoint : Disjoint (degreeOne D) (degreeTwo D) := by
  rw [Submodule.disjoint_def]
  rintro x ⟨v,rfl⟩ ⟨z,hz⟩
  have hv : v=0 := (congrArg Prod.fst hz).symm
  rw [hv,map_zero]

theorem degree_subspaces_span : degreeOne D ⊔ degreeTwo D=⊤ := by
  apply top_unique
  intro x hx
  rw [← generator_add_central D x]
  exact Submodule.add_mem_sup ⟨x.1,rfl⟩ ⟨x.2,rfl⟩

section FiniteDimensions

theorem finrank_degreeOne : Module.finrank K (degreeOne D)=Module.finrank K V :=
  (degreeOneEquiv D).finrank_eq.symm

theorem finrank_degreeTwo : Module.finrank K (degreeTwo D)=Module.finrank K Z :=
  (degreeTwoEquiv D).finrank_eq.symm

end FiniteDimensions

section UniversalProperty

variable {A : Type*} [Ring A] [Algebra K A]
attribute [local instance 100] LieRing.ofAssociativeRing

theorem lie_eq_zero_of_commute {x y : A} (h : Commute x y) : ⁅x,y⁆=0 :=
  sub_eq_zero.mpr h.eq

/-- A linear assignment of generators and central directions satisfying
the displayed commutator equations gives an actual Lie homomorphism. -/
def liftLie (X : V →ₗ[K] A) (C : Z →ₗ[K] A)
    (hXX : ∀ v w, ⁅X v,X w⁆=C (D.bilinear v w))
    (hXC : ∀ v z, Commute (X v) (C z))
    (hCC : ∀ z z', Commute (C z) (C z')) :
    LieSpace D →ₗ⁅K⁆ A where
  toLinearMap := X.coprod C
  map_lie' {x y} := by
    change X 0+C (D.bilinear x.1 y.1)=⁅X x.1+C x.2,X y.1+C y.2⁆
    rw [map_zero,zero_add,add_lie,lie_add,lie_add,hXX,
      lie_eq_zero_of_commute (hXC x.1 y.2),
      lie_eq_zero_of_commute (hXC y.1 x.2).symm,
      lie_eq_zero_of_commute (hCC x.2 y.2)]
    simp

@[simp] theorem liftLie_generator (X : V →ₗ[K] A) (C : Z →ₗ[K] A)
    (hXX : ∀ v w, ⁅X v,X w⁆=C (D.bilinear v w))
    (hXC : ∀ v z, Commute (X v) (C z))
    (hCC : ∀ z z', Commute (C z) (C z')) (v : V) :
    liftLie D X C hXX hXC hCC (generator D v)=X v := by
  change X v+C 0=X v
  simp

@[simp] theorem liftLie_central (X : V →ₗ[K] A) (C : Z →ₗ[K] A)
    (hXX : ∀ v w, ⁅X v,X w⁆=C (D.bilinear v w))
    (hXC : ∀ v z, Commute (X v) (C z))
    (hCC : ∀ z z', Commute (C z) (C z')) (z : Z) :
    liftLie D X C hXX hXC hCC (central D z)=C z := by
  change X 0+C z=C z
  simp

/-- The standard enveloping-algebra map supplied by that Lie homomorphism. -/
def lift (X : V →ₗ[K] A) (C : Z →ₗ[K] A)
    (hXX : ∀ v w, ⁅X v,X w⁆=C (D.bilinear v w))
    (hXC : ∀ v z, Commute (X v) (C z))
    (hCC : ∀ z z', Commute (C z) (C z')) :
    UniversalEnvelopingAlgebra K (LieSpace D) →ₐ[K] A :=
  UniversalEnvelopingAlgebra.lift K (liftLie D X C hXX hXC hCC)

@[simp] theorem lift_generator (X : V →ₗ[K] A) (C : Z →ₗ[K] A)
    (hXX : ∀ v w, ⁅X v,X w⁆=C (D.bilinear v w))
    (hXC : ∀ v z, Commute (X v) (C z))
    (hCC : ∀ z z', Commute (C z) (C z')) (v : V) :
    lift D X C hXX hXC hCC (UniversalEnvelopingAlgebra.ι K (generator D v))=X v := by
  rw [lift,UniversalEnvelopingAlgebra.lift_ι_apply,liftLie_generator]

@[simp] theorem lift_central (X : V →ₗ[K] A) (C : Z →ₗ[K] A)
    (hXX : ∀ v w, ⁅X v,X w⁆=C (D.bilinear v w))
    (hXC : ∀ v z, Commute (X v) (C z))
    (hCC : ∀ z z', Commute (C z) (C z')) (z : Z) :
    lift D X C hXX hXC hCC (UniversalEnvelopingAlgebra.ι K (central D z))=C z := by
  rw [lift,UniversalEnvelopingAlgebra.lift_ι_apply,liftLie_central]

end UniversalProperty
end PaperVerification.TwoStepCentralLie
