module

public import Lean.Elab.BuiltinEvalCommand
public meta import Lean.Elab.BuiltinEvalCommand
public import Lean.Util.CollectAxioms
public meta import Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public meta import Lean.Util.FoldConsts
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import paper_verification.toric022
public import paper_verification.toric023
public import paper_verification.toric025
public import paper_verification.toric032

@[expose] public section


-- BEGIN ORIGINAL PaperVerification.ToricEquivariantRigidity
section Source_ToricEquivariantRigidity

-- original header: module

-- original header: public import PaperVerification.ToricTorusCoactionRational
-- original header: public import PaperVerification.ToricActionProductProperties
-- original header: public import Mathlib.AlgebraicGeometry.Morphisms.Separated

-- original header: @[expose] public section

/-!
# Equivariance from an actual dense torus

A morphism over the ground field which agrees with the given torus
embeddings is equivariant. The equality is proved on the genuine scheme
product of two tori, then extended from that dense open subscheme to the
reduced action product. In particular no assertion about rational points
is substituted for equality of scheme morphisms.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

open AlgebraicGeometry CategoryTheory MonoidalCategory MonObj

variable {k : Type u} [Field k] {n : ℕ}
    {X Y : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n→ℤ)) X]
    [ModObj (splitTorusOver k (Fin n→ℤ)) Y]
    [IsIntegral X.left] [Smooth X.hom] [IsSeparated Y.hom]
    (T : SplitToricEmbedding k n X) (S : SplitToricEmbedding k n Y)

/-- The actual action square follows from the actual dense-torus square. -/
theorem isModHom_of_torus_compatibility (f : X ⟶ Y)
    (htorus : T.torus ≫ f = S.torus) :
    IsModHom (splitTorusOver k (Fin n→ℤ)) f := by
  let G := splitTorusOver k (Fin n→ℤ)
  letI : IsLocallyNoetherian X.left :=
    LocallyOfFiniteType.isLocallyNoetherian X.hom
  letI : IsIntegral (G⊗G).left := T.doubleTorus_integral
  letI : IsIntegral (G⊗X).left := inferInstance
  letI : IsDominant T.doubleTorusMap := inferInstance
  constructor
  apply Over.OverMorphism.ext
  have hbase : (γ[G,X] ≫ f).left ≫ Y.hom =
      (G ◁ f ≫ γ[G,Y]).left ≫ Y.hom :=
    (γ[G,X] ≫ f).w.trans (G ◁ f ≫ γ[G,Y]).w.symm
  apply ext_of_isDominant_of_isSeparated Y.hom hbase T.doubleTorusMap
  have heq : (G ◁ T.torus) ≫ (γ[G,X] ≫ f) =
      (G ◁ T.torus) ≫ ((G ◁ f) ≫ γ[G,Y]) := by
    calc
      _ = μ[G] ≫ (T.torus ≫ f) := by
        rw [← Category.assoc,← T.equivariant,Category.assoc]
      _ = μ[G] ≫ S.torus := by rw [htorus]
      _ = (G ◁ S.torus) ≫ γ[G,Y] := S.equivariant
      _ = (G ◁ T.torus) ≫ ((G ◁ f) ≫ γ[G,Y]) := by
        rw [← htorus,MonoidalCategory.whiskerLeft_comp,Category.assoc]
  exact congrArg (fun g : G⊗G ⟶ Y => g.left) heq

/-- A torus-preserving isomorphism of the underlying schemes over the
field is an isomorphism respecting the genuine torus actions. -/
theorem iso_isModHom_of_torus_compatibility (e : X ≅ Y)
    (htorus : T.torus ≫ e.hom = S.torus) :
    IsModHom (splitTorusOver k (Fin n→ℤ)) e.hom :=
  T.isModHom_of_torus_compatibility S e.hom htorus

end PaperVerification.ToricSchemes.SplitToricEmbedding

#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.isModHom_of_torus_compatibility
end
end Source_ToricEquivariantRigidity
-- END ORIGINAL PaperVerification.ToricEquivariantRigidity


-- BEGIN ORIGINAL PaperVerification.ToricFanCharacterTranslations
section Source_ToricFanCharacterTranslations

-- original header: module

-- original header: public import PaperVerification.ToricFanCartierArithmetic
-- original header: public import PaperVerification.ToricCartierScaleCocycle

-- original header: @[expose] public section

/-!
# Character translations of actual fan Cartier sheaves

Changing ray coefficients by the pairing with one integral character
translates every genuine local Cartier point by that character. The
resulting actual sheaf isomorphism is multiplication by the rational
character. Thus the customary lattice translations are proved principal
translations of the actual invertible sheaves.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]
    (hpure : «Σ».IsPure)

theorem cartierLatticePoint_characterTranslation
    (a b : Lattice n → ℤ) (m : Lattice n)
    (h : ∀ v ∈ «Σ».rays,b v=a v-integerPairing v m) (s : «Σ».fullCones) :
    «Σ».cartierLatticePoint b s=«Σ».cartierLatticePoint a s+m := by
  symm
  apply «Σ».eq_cartierLatticePoint_of_pairings
  intro v hv
  rw [integerPairing_add,«Σ».cartierLatticePoint_pairing a s v hv,
    h v («Σ».ray_mem_of_mem_cone («Σ».fullCones_mem s) hv)]
  omega

/-- The character translate is a principal change of the actual
fractional presentation, with an actual isomorphism of its sheaf. -/
theorem fanCartierData_characterTranslation
    (a b : Lattice n → ℤ) (m : Lattice n)
    (h : ∀ v ∈ «Σ».rays,b v=a v-integerPairing v m) :
    («Σ».fanCartierData k hpure a).LinearlyEquivalent
      («Σ».fanCartierData k hpure b) := by
  let C := «Σ».fanCartierCocycle k hpure a
  let E := «Σ».fanCartierCocycle k hpure b
  let q := «Σ».rationalCharacter k m
  have he (i : C.index) : (C.scale q).generator i=E.generator i := by
    change «Σ».rationalCharacter k m *
        «Σ».rationalCharacter k («Σ».cartierLatticePoint a i.down) =
      «Σ».rationalCharacter k («Σ».cartierLatticePoint b i.down)
    rw [«Σ».cartierLatticePoint_characterTranslation a b m h,
      «Σ».rationalCharacter_add k]
    exact mul_comm _ _
  have hCE : (C.scale q).toCartierData.Equivalent E.toCartierData := by
    apply (C.scale q).equivalent_of_generatorRatios E
    · intro i j x hi hj
      rw [he i]
      exact E.transition i j x hi hj
    · intro i j x hi hj
      rw [he j]
      exact E.transition i j x hi hj
  exact ⟨C.scaleSheafIso q ≪≫ hCE.choose⟩

/-- The corresponding polytope is the literal integral translation of
the original halfspace intersection, even without positivity. -/
theorem fanPolytope_characterTranslation
    (a b : Lattice n → ℤ) (m : Lattice n)
    (h : ∀ v ∈ «Σ».rays,b v=a v-integerPairing v m) :
    «Σ».fanPolytope (fun v => (b v : ℝ)) =
      (fun x : Ambient n => x+embed n m) '' «Σ».fanPolytope (fun v => (a v : ℝ)) := by
  ext x
  constructor
  · intro hx
    refine ⟨x-embed n m,?_,sub_add_cancel _ _⟩
    intro v hv
    have hvx := hx v hv
    change -(b v : ℝ) ≤ _ at hvx
    rw [h v hv,Int.cast_sub] at hvx
    rw [map_sub,normalRay_pairing_lattice]
    change -((a v : ℝ)-(integerPairing v m : ℝ)) ≤ _ at hvx
    change -(a v : ℝ) ≤ _
    change -(a v : ℝ) ≤ _-(integerPairing v m : ℝ)
    linarith
  · rintro ⟨y,hy,rfl⟩ v hv
    have hvy := hy v hv
    change -(b v : ℝ) ≤ _
    rw [h v hv,Int.cast_sub,map_add,normalRay_pairing_lattice]
    change -((a v : ℝ)-(integerPairing v m : ℝ)) ≤ _+(integerPairing v m : ℝ)
    linarith

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.fanCartierData_characterTranslation
end
end Source_ToricFanCharacterTranslations
-- END ORIGINAL PaperVerification.ToricFanCharacterTranslations


