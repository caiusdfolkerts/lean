module

public import ToricPower.CoherentFoundations
public import Mathlib.CategoryTheory.Triangulated.TStructure.Induced

/-!
# Generation by single objects in a bounded derived category

A bounded object is assembled from objects concentrated in one degree by
the actual truncation triangles of its t-structure. Consequently an exact
essentially surjective functor of abelian categories sends bounded-derived
generators to generators. Essential surjectivity is required only on the
abelian categories; no lifting of arbitrary differentials is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated
open scoped ZeroObject

namespace ToricPower

universe w₁ w₂ v₁ v₂ u₁ u₂

section TStructure

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]

/-- A triangulated subcategory containing every object concentrated in one
degree contains every bounded object. The proof uses finite induction on
the cohomological interval and actual truncation triangles. -/
theorem prop_of_tBounded_of_prop_concentrated
    (t : TStructure C) (P : ObjectProperty C)
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    (hsingle : ∀ (X : C) (n : ℤ), t.IsGE X n → t.IsLE X n → P X)
    (X : C) (hX : t.bounded X) : P X := by
  have hinterval : ∀ n : ℕ, ∀ (K : C) (a : ℤ),
      t.IsGE K a → t.IsLE K (a + n) → P K := by
    intro n
    induction n with
    | zero =>
        intro K a hge hle
        exact hsingle K a hge (by simpa using hle)
    | succ n ih =>
        intro K a hge hle
        letI := hge
        letI := hle
        let b : ℤ := a + (n + 1 : ℕ)
        have hb : b - 1 = a + n := by dsimp [b]; omega
        have hleftLE : t.IsLE ((t.truncLT b).obj K) (a + n) := by
          have h : t.IsLE ((t.truncLT b).obj K) (b - 1) := inferInstance
          simpa only [hb] using h
        have hleft : P ((t.truncLT b).obj K) :=
          ih _ a inferInstance hleftLE
        have hright : P ((t.truncGE b).obj K) := by
          apply hsingle _ b inferInstance
          change t.IsLE ((t.truncGE b).obj K) (a + (n + 1 : ℕ))
          infer_instance
        exact P.ext_of_isTriangulatedClosed₂ _
          (t.triangleLTGE_distinguished b K) hleft hright
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hX
  letI := ha
  letI := hb
  exact hinterval (b - a).toNat X a ha
    (t.isLE_of_le X b _ (by omega))

end TStructure

section BoundedDerived

variable (A : Type u₁) [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]

/-- The actual single-object embeddings in every integer degree form a
classical generating collection of the actual bounded derived category. -/
theorem boundedSingleFunctors_classicalGenerators :
    ObjectProperty.IsClassicalTriangulatedGenerator
      (ObjectProperty.ofObj (fun p : ℤ × A =>
        (TauCeti.DerivedCategory.Bounded.singleFunctor A p.1).obj p.2)) := by
  letI : Nonempty A := ⟨0⟩
  let t := DerivedCategory.TStructure.t (C := A)
  let P := ObjectProperty.ofObj (fun p : ℤ × A =>
    (TauCeti.DerivedCategory.Bounded.singleFunctor A p.1).obj p.2)
  change P.triangEnvelope = ⊤
  apply le_antisymm le_top
  intro X _
  apply prop_of_tBounded_of_prop_concentrated t.onBounded P.triangEnvelope
  · intro K n hge hle
    have hge' : K.obj.IsGE n := (t.bounded.tStructure_isGE_iff t K n).mp hge
    have hle' : K.obj.IsLE n := (t.bounded.tStructure_isLE_iff t K n).mp hle
    letI := hge'
    letI := hle'
    obtain ⟨M, ⟨e⟩⟩ := K.obj.exists_iso_singleFunctor_obj_of_isGE_of_isLE n
    let e' : K ≅ (TauCeti.DerivedCategory.Bounded.singleFunctor A n).obj M :=
      t.bounded.fullyFaithfulι.preimageIso e
    apply P.triangEnvelope.prop_of_iso e'.symm
    exact P.le_triangEnvelope _ (ObjectProperty.ofObj_apply _ (n, M))
  · obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := X.property
    exact ⟨⟨a, (t.bounded.tStructure_isGE_iff t X a).mpr ha⟩,
      ⟨b, (t.bounded.tStructure_isLE_iff t X b).mpr hb⟩⟩

variable {A} {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]

/-- An exact functor that is essentially surjective on abelian objects
preserves classical generators of the bounded derived categories. -/
theorem boundedDerived_generator_of_essentiallySurjective
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.EssSurj] (G : DerivedCategory.Bounded A)
    (hG : (ObjectProperty.singleton G).IsClassicalTriangulatedGenerator) :
    ObjectProperty.IsClassicalTriangulatedGenerator
      (ObjectProperty.singleton (F.mapBoundedDerivedCategory.obj G)) := by
  letI : Nonempty B := ⟨0⟩
  apply obj_classicalGenerator_of_generatingRetracts F.mapBoundedDerivedCategory G hG
    (ObjectProperty.ofObj (fun p : ℤ × B =>
      (TauCeti.DerivedCategory.Bounded.singleFunctor B p.1).obj p.2))
    (boundedSingleFunctors_classicalGenerators B)
  intro K hK
  obtain ⟨⟨n, M⟩⟩ := hK
  let N := F.objPreimage M
  let e : F.mapBoundedDerivedCategory.obj
      ((TauCeti.DerivedCategory.Bounded.singleFunctor A n).obj N) ≅
      (TauCeti.DerivedCategory.Bounded.singleFunctor B n).obj M :=
    (F.mapBoundedDerivedCategorySingleFunctor n).app N ≪≫
      (TauCeti.DerivedCategory.Bounded.singleFunctor B n).mapIso (F.objObjPreimageIso M)
  exact ⟨_, ⟨Retract.ofIso e.symm⟩⟩

end BoundedDerived

end ToricPower

end
