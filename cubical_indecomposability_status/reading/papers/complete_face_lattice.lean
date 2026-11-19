module
public import papers.polytope_geometry
public import Mathlib.Order.Hom.WithTopBot

@[expose] public section

/-!
# Including the empty face

The polytope foundation stores nonempty exposed faces. This file proves that
its notion of combinatorial equivalence is equivalent to an order isomorphism
of the complete exposed-face posets, including the empty face.
-/

noncomputable section
namespace Papers.Polytopes
open Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

def CompleteFaceType {d : ℕ} (P : ConvexPolytope d) :=
  {F : Set (E d) // IsExposed ℝ P.toSet F}

instance {d : ℕ} (P : ConvexPolytope d) : PartialOrder (CompleteFaceType P) :=
  inferInstanceAs (PartialOrder {F : Set (E d) // IsExposed ℝ P.toSet F})

instance {d : ℕ} (P : ConvexPolytope d) : OrderBot (CompleteFaceType P) where
  bot := ⟨∅, isExposed_empty⟩
  bot_le _ := Set.empty_subset _

theorem completeFace_ne_bot_iff {d : ℕ} {P : ConvexPolytope d} (F : CompleteFaceType P) :
    F ≠ ⊥ ↔ F.val.Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  exact not_congr ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

def nonemptyFaceOrderIso {d : ℕ} (P : ConvexPolytope d) :
    FaceType P ≃o {F : CompleteFaceType P // F ≠ ⊥} where
  toFun F := ⟨⟨F.val, F.property.1⟩,
    (completeFace_ne_bot_iff _).mpr F.property.2⟩
  invFun F := ⟨F.val.val, F.val.property, (completeFace_ne_bot_iff F.val).mp F.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

def completeFaceOrderIso {d : ℕ} (P : ConvexPolytope d) :
    WithBot (FaceType P) ≃o CompleteFaceType P := by
  classical
  exact (nonemptyFaceOrderIso P).withBotCongr.trans WithBot.subtypeOrderIso

def extendFaceOrderIso {d e : ℕ} {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) : CompleteFaceType P ≃o CompleteFaceType Q :=
  (completeFaceOrderIso P).symm.trans (φ.withBotCongr.trans (completeFaceOrderIso Q))

def restrictCompleteFaceOrderIso {d e : ℕ} {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : CompleteFaceType P ≃o CompleteFaceType Q) : FaceType P ≃o FaceType Q := by
  let ψ : {F : CompleteFaceType P // F ≠ ⊥} ≃o {F : CompleteFaceType Q // F ≠ ⊥} := {
    toFun := fun F => ⟨φ F.val, by
      intro h
      apply F.property
      apply φ.injective
      simpa only [φ.map_bot] using h⟩
    invFun := fun F => ⟨φ.symm F.val, by
      intro h
      apply F.property
      apply φ.symm.injective
      simpa only [φ.symm.map_bot] using h⟩
    left_inv := fun F => Subtype.ext (φ.symm_apply_apply F.val)
    right_inv := fun F => Subtype.ext (φ.apply_symm_apply F.val)
    map_rel_iff' := φ.le_iff_le }
  exact (nonemptyFaceOrderIso P).trans (ψ.trans (nonemptyFaceOrderIso Q).symm)

theorem nonempty_face_iso_iff_complete_face_iso {d e : ℕ}
    (P : ConvexPolytope d) (Q : ConvexPolytope e) :
    Nonempty (FaceType P ≃o FaceType Q) ↔ Nonempty (CompleteFaceType P ≃o CompleteFaceType Q) :=
  ⟨fun ⟨φ⟩ => ⟨extendFaceOrderIso φ⟩, fun ⟨φ⟩ => ⟨restrictCompleteFaceOrderIso φ⟩⟩

end Papers.Polytopes
