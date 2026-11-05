module
public import mixed_results.koszul_family_elimination
public import shared_results.part018_koszul_coefficient_projection

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.KoszulSelectedElimination -/
section

/-! # Selected coefficient degrees survive Koszul elimination -/

section
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace FourPapers.KoszulFamilyElimination
open Classical CommAlg HomologicalPerturbation
open scoped TensorProduct
universe u
variable {K A B V W : Type u} [Field K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B] [Fintype V] [LinearOrder V]
  [Fintype W] [LinearOrder W]
  (f : V → A) (g : W → A) (F : A →ₐ[K] B)
  (C : LinearContraction (R := K) (M := A ⊗[K] Simplicial.Ambient V K) (H := B))
  (hd : C.d=TensorExteriorKoszul.differential (K := K) (M := A) f)
  (hp : C.projection=(KoszulAugmentation.augmentation (V := V) F).toLinearMap)

local instance : LinearOrder (V ⊕ W) :=
  LinearOrder.lift' (fun z : V ⊕ W => (toLex z : Lex (V ⊕ W))) (fun _ _ h => h)

/-- The equivalence on actual homology restricts to the selected
coefficient-degree classes, without a grading assumption on the homotopy. -/
theorem homologyEquiv_selectedClasses
    (P : A →ₗ[K] A) (Q : B →ₗ[K] B)
    (hQ : ∀ b, Q (Q b)=Q b)
    (hPmul : ∀ v a, P (Sum.elim f g v*a)=Sum.elim f g v*P a)
    (hQmul : ∀ w b, Q (F (g w)*b)=F (g w)*Q b)
    (hF : ∀ a, F (P a)=Q (F a)) :
    homologyEquiv f g F C hd hp ''
      (TensorExteriorKoszul.parityDifferential (K := K) (Sum.elim f g)).classesFrom
        (LinearMap.range (KoszulCoefficientProjection.tensor (V := V ⊕ W) P))=
      (TensorExteriorKoszul.parityDifferential (K := K) (fun w => F (g w))).classesFrom
        (LinearMap.range (KoszulCoefficientProjection.tensor (V := W) Q)) := by
  apply ParityDifferential.homologyEquivOfRetract_classesFrom
    (P := KoszulCoefficientProjection.tensor P)
    (Q := KoszulCoefficientProjection.tensor Q)
  · exact KoszulCoefficientProjection.differential_commute (Sum.elim f g) P hPmul
  · exact KoszulCoefficientProjection.differential_commute (fun w => F (g w)) Q hQmul
  · exact KoszulCoefficientProjection.right_commute F P Q hF
  · intro x
    exact ⟨x,rfl⟩
  · rintro y ⟨b,rfl⟩
    exact KoszulCoefficientProjection.tensor_idempotent Q hQ b
  · exact KoszulCoefficientProjection.map_range
      (KoszulSummandProjection.right (V := V) (W := W) F).toLinearMap
      (KoszulCoefficientProjection.tensor P) (KoszulCoefficientProjection.tensor Q)
      (KoszulCoefficientProjection.right_commute F P Q hF)

include C hd hp in
theorem selectedGeneration_iff
    (P : A →ₗ[K] A) (Q : B →ₗ[K] B)
    (hQ : ∀ b, Q (Q b)=Q b)
    (hPmul : ∀ v a, P (Sum.elim f g v*a)=Sum.elim f g v*P a)
    (hQmul : ∀ w b, Q (F (g w)*b)=F (g w)*Q b)
    (hF : ∀ a, F (P a)=Q (F a)) :
    Algebra.adjoin K
      ((TensorExteriorKoszul.parityDifferential (K := K) (Sum.elim f g)).classesFrom
        (LinearMap.range (KoszulCoefficientProjection.tensor (V := V ⊕ W) P)))=⊤ ↔
    Algebra.adjoin K
      ((TensorExteriorKoszul.parityDifferential (K := K) (fun w => F (g w))).classesFrom
        (LinearMap.range (KoszulCoefficientProjection.tensor (V := W) Q)))=⊤ :=
  adjoin_eq_top_iff_of_algEquiv (homologyEquiv f g F C hd hp) _ _
    (homologyEquiv_selectedClasses f g F C hd hp P Q hQ hPmul hQmul hF)

end FourPapers.KoszulFamilyElimination

end
end
end

end
