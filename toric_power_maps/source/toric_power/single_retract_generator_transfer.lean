module

public import ToricPower.InvertibleProjectionFormula

/-! ## Source module `ToricPower.SingleRetractGeneratorTransfer`
Original SHA256: b37eb1165e147681f69e828cd3efd94cea66ef184dffc721487ba1441d0daf18.
Original sources are retained in `third_party/coherent_sources`.
-/
section CoherentSource12

/-!
# Generation from retracts of a generating collection

For an exact functor, it is enough that a generating collection in the target
consist of retracts of images. In particular, for an exact endofunctor it
suffices to exhibit the original generator as one retract of one image.

This is the categorical form useful when a generator is a finite sum of line
bundles: a splitting of the pushed-forward structure sheaf and the invertible
projection formula supply the retractions of the individual line bundles.
Neither a natural splitting on all coherent sheaves nor an exact pullback
functor is required.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace ToricPower

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [IsTriangulated D]

/-- An exact functor carries a classical generator to a classical generator
if a generating collection in the target consists of retracts of images. -/
theorem obj_classicalGenerator_of_generatingRetracts
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (G : C) (hG : (ObjectProperty.singleton G).IsClassicalTriangulatedGenerator)
    (P : ObjectProperty D) [P.Nonempty]
    (hP : P.IsClassicalTriangulatedGenerator)
    (hF : ∀ Y, P Y → ∃ X : C, Nonempty (Retract Y (F.obj X))) :
    (ObjectProperty.singleton (F.obj G)).IsClassicalTriangulatedGenerator := by
  have h : P.triangEnvelope ≤ (ObjectProperty.singleton (F.obj G)).triangEnvelope := by
    refine (P.triangEnvelope_le_iff
      (Q := (ObjectProperty.singleton (F.obj G)).triangEnvelope)).2 ?_
    intro Y hY
    obtain ⟨X, ⟨r⟩⟩ := hF Y hY
    apply (ObjectProperty.singleton (F.obj G)).triangEnvelope.prop_of_retract r
    have hX : (ObjectProperty.singleton G).triangEnvelope X := by
      rw [hG]
      trivial
    have hFX := exactFunctor_map_mem_triangEnvelope F (ObjectProperty.singleton G) hX
    rwa [singleton_map_triangEnvelope] at hFX
  change (ObjectProperty.singleton (F.obj G)).triangEnvelope = ⊤
  rw [hP] at h
  exact le_antisymm le_top h

/-- Only one image retraction is needed if its retract is itself a target
generator. The object whose image contains that retract is unrestricted. -/
theorem obj_classicalGenerator_of_generatorRetract
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (G : C) (hG : (ObjectProperty.singleton G).IsClassicalTriangulatedGenerator)
    (H : D) (hH : (ObjectProperty.singleton H).IsClassicalTriangulatedGenerator)
    (X : C) (r : Retract H (F.obj X)) :
    (ObjectProperty.singleton (F.obj G)).IsClassicalTriangulatedGenerator := by
  apply obj_classicalGenerator_of_generatingRetracts F G hG
    (ObjectProperty.singleton H) hH
  intro Y hY
  have hY' : H = Y := (ObjectProperty.singleton_iff H Y).1 hY
  subst Y
  exact ⟨X, ⟨r⟩⟩

/-- For an exact endofunctor, one retraction of the original generator
suffices to prove that its image is again a generator. -/
theorem obj_classicalGenerator_of_selfRetract
    [IsTriangulated C] (F : C ⥤ C) [F.CommShift ℤ] [F.IsTriangulated]
    (G : C) (hG : (ObjectProperty.singleton G).IsClassicalTriangulatedGenerator)
    (X : C) (r : Retract G (F.obj X)) :
    (ObjectProperty.singleton (F.obj G)).IsClassicalTriangulatedGenerator :=
  obj_classicalGenerator_of_generatorRetract F G hG G hG X r

end ToricPower


-- Close scopes implicitly ended by the original source EOF.
end
end CoherentSource12
