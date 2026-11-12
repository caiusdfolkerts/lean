module

public import ToricPower.CechNegativeSupportGeneric
public import ToricPower.CechProductElements
public import Mathlib.Algebra.Category.ModuleCat.Limits

/-!
# The relative Čech complex with its literal scalar action

Each tuple coefficient is the submodule of the coefficient field that
vanishes when the tuple is forbidden. The cochain maps retain the same
scalar, and the differential is the alternating coface differential.
Shrinking the forbidden-ray set gives an actual linear map of complexes.

These definitions retain the full Čech complex, including all tuple
degrees. No truncation or cohomological finiteness is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped Classical Simplicial

namespace ToricPower.LinearRelativeCech

variable (k : Type) [Field k] {Ray : Type*} {Chart : Type}
  (incidence : Ray → Chart → Prop) (negative : Ray → Prop)

/-- The literal zero-or-scalar coefficient, as a submodule of the field. -/
def scalar (degree : ℕ) (tuple : Fin (degree+1) → Chart) : Submodule k k where
  carrier := {a | NegativeSupportCech.tupleForbidden incidence negative degree tuple → a = 0}
  zero_mem' := fun _ => rfl
  add_mem' := fun ha hb h => by rw [ha h, hb h, zero_add]
  smul_mem' := fun r a ha h => by rw [ha h, smul_zero]

/-- An actual tuple cochain, with the componentwise vector-space action. -/
def degree (q : ℕ) : ModuleCat k :=
  ModuleCat.of k (∀ tuple : Fin (q+1) → Chart, scalar k incidence negative q tuple)

/-- Every coface or codegeneracy keeps the actual coefficient. -/
def tupleMap {p q : ℕ} (selection : Fin (p+1) → Fin (q+1)) :
    degree k incidence negative p ⟶ degree k incidence negative q :=
  ModuleCat.ofHom
    { toFun := fun a tuple => ⟨(a (tuple ∘ selection)).val, fun forbidden =>
        (a (tuple ∘ selection)).property
          (NegativeSupportCech.tupleForbidden_precomp incidence negative selection tuple forbidden)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- The complete cosimplicial vector-space object. -/
def cosimplicial : CosimplicialObject (ModuleCat k) where
  obj a := degree k incidence negative a.len
  map f := tupleMap k incidence negative f.toOrderHom
  map_id a := by
    ext x tuple
    rfl
  map_comp f g := by
    ext x tuple
    rfl

/-- The literal vector-space relative Čech complex. -/
def complex : CochainComplex (ModuleCat k) ℕ :=
  AlgebraicTopology.AlternatingCofaceMapComplex.obj (cosimplicial k incidence negative)

variable {negative} {next : Ray → Prop} (h : ∀ r, next r → negative r)

/-- Inclusion of the allowed tuples gives the actual linear cochain map. -/
def degreeMap (q : ℕ) : degree k incidence negative q ⟶ degree k incidence next q :=
  ModuleCat.ofHom
    { toFun := fun a tuple => ⟨(a tuple).val, fun forbidden => by
        rcases forbidden with ⟨r, hr, ht⟩
        exact (a tuple).property ⟨r, h r hr, ht⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- The same coefficient inclusions respect every cosimplicial map. -/
def cosimplicialMap : cosimplicial k incidence negative ⟶ cosimplicial k incidence next where
  app a := degreeMap k incidence h a.len
  naturality {a b} f := by
    ext x tuple
    rfl

/-- The actual map of all cochain degrees and differentials. -/
def complexMap : complex k incidence negative ⟶ complex k incidence next :=
  AlgebraicTopology.AlternatingCofaceMapComplex.map (cosimplicialMap k incidence h)

section Diagrams

variable {C : Type*} [Category* C] (neg : C → Ray → Prop)
  (monotone : ∀ {c d : C}, (c ⟶ d) → ∀ r, neg d r → neg c r)

/-- A genuine diagram of cosimplicial vector spaces for every
contravariantly monotone forbidden-ray predicate. -/
def cosimplicialDiagram : C ⥤ CosimplicialObject (ModuleCat k) where
  obj c := cosimplicial k incidence (neg c)
  map f := cosimplicialMap k incidence (monotone f)
  map_id c := by
    ext q x tuple
    rfl
  map_comp f g := by
    ext q x tuple
    rfl

/-- The full complex-valued diagram, formed before derived localization. -/
def complexDiagram : C ⥤ CochainComplex (ModuleCat k) ℕ :=
  cosimplicialDiagram k incidence neg monotone ⋙ AlgebraicTopology.alternatingCofaceMapComplex _

end Diagrams

variable (negative)

/-- The scalar coefficient has the original relative additive group. -/
def scalarAddEquiv (q : ℕ) (tuple : Fin (q+1) → Chart) :
    NegativeSupportCech.relativeScalarCoefficient k incidence negative q tuple ≃+
      scalar k incidence negative q tuple where
  toFun x := ⟨x.val, x.property⟩
  invFun x := ⟨x.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The actual additive degree comparison, preserving every tuple scalar. -/
def degreeAddEquiv (q : ℕ) :
    NegativeSupportCech.relativeDegree k incidence negative q ≃+
      degree k incidence negative q :=
  (CechProductElements.productElementsEquiv
    (NegativeSupportCech.relativeCoefficient k incidence negative q)).trans
      (AddEquiv.piCongrRight (fun tuple => scalarAddEquiv k incidence negative q tuple))

@[simp]
theorem degreeAddEquiv_apply_val (q : ℕ)
    (a : NegativeSupportCech.relativeDegree k incidence negative q)
    (tuple : Fin (q+1) → Chart) :
    (degreeAddEquiv k incidence negative q a tuple).val =
      (Limits.Pi.π (NegativeSupportCech.relativeCoefficient k incidence negative q) tuple a).val := by
  change ((CechProductElements.productElementsEquiv
    (NegativeSupportCech.relativeCoefficient k incidence negative q)) a tuple).val = _
  rw [CechProductElements.productElementsEquiv_apply]

/-- Forgetting scalars recovers the original relative cosimplicial
complex with its actual tuple restrictions. -/
def cosimplicialForgetIso :
    NegativeSupportCech.relativeCosimplicial k incidence negative ≅
      cosimplicial k incidence negative ⋙ forget₂ (ModuleCat k) AddCommGrpCat :=
  NatIso.ofComponents (fun a => (degreeAddEquiv k incidence negative a.len).toAddCommGrpIso)
    (fun {a b} f => by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro x
      funext tuple
      apply Subtype.ext
      change (degreeAddEquiv k incidence negative b.len
        (NegativeSupportCech.relativeTupleMap k incidence negative f.toOrderHom x) tuple).val =
        (degreeAddEquiv k incidence negative a.len x (tuple ∘ f.toOrderHom)).val
      rw [degreeAddEquiv_apply_val, degreeAddEquiv_apply_val]
      exact congrArg Subtype.val (ConcreteCategory.congr_hom
        (Limits.Pi.lift_comp_π
          (fun t => Limits.Pi.π
            (NegativeSupportCech.relativeCoefficient k incidence negative a.len)
            (t ∘ f.toOrderHom) ≫ AddCommGrpCat.ofHom
              (NegativeSupportCech.relativeScalarRestriction k incidence negative f.toOrderHom t))
          tuple) x))

end ToricPower.LinearRelativeCech

end
