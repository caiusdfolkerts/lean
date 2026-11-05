module

public import PaperVerification.ToricChartActions
public import PaperVerification.ToricOrbitChartMaps

@[expose] public section

/-! # Actual affine coactions and their genuine scheme-morphism equations -/

noncomputable section

universe u v w

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open MonoidalCategory MonObj
open PaperVerification.ToricCharacters
open scoped TensorProduct

section Categorical

variable {C : Type u} {D : Type v} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.LaxMonoidal]
    {T Q A B : C}

/-- Naturality of the tensorator turns an actual algebra coaction
identity into the corresponding action identity after a monoidal functor. -/
theorem map_coaction_intertwining (r : T ⟶ Q) (f : B ⟶ A)
    (a : T ⊗ A ⟶ A) (b : Q ⊗ B ⟶ B)
    (h : T ◁ f ≫ a = r ▷ B ≫ b ≫ f) :
    F.obj T ◁ F.map f ≫ (Functor.LaxMonoidal.μ F T A ≫ F.map a) =
      F.map r ▷ F.obj B ≫ (Functor.LaxMonoidal.μ F Q B ≫ F.map b) ≫ F.map f := by
  rw [← Category.assoc,Functor.LaxMonoidal.μ_natural_right,Category.assoc,
    ← F.map_comp,h,F.map_comp,F.map_comp]
  rw [← Category.assoc,← Functor.LaxMonoidal.μ_natural_left,Category.assoc,Category.assoc]

end Categorical

local instance (k : Type u) [CommRing k] :
    (algSpec (CommRingCat.of k)).LaxMonoidal :=
  (AlgebraicGeometry.braidedAlgSpec (R := CommRingCat.of k)).toMonoidal.toLaxMonoidal

section AffineMorphism

variable (k : Type u) [CommRing k]

/-- The actual morphism of affine schemes associated to a coaction. -/
def affineCoactionMorphism {T A : Type u} [CommRing T] [CommRing A]
    [Algebra k T] [Algebra k A] (d : A →ₐ[k] T ⊗[k] A) :
    ((Spec (CommRingCat.of T)).asOver (Spec (CommRingCat.of k))) ⊗
      ((Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of k))) ⟶
        (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of k)) :=
  Functor.LaxMonoidal.μ (algSpec (CommRingCat.of k))
      (op (CommAlgCat.of k T)) (op (CommAlgCat.of k A)) ≫
    (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom d).op

end AffineMorphism

section Characters

variable (k : Type (max u v)) [CommRing k] {M : Type v} [AddCommGroup M]

/-- The coaction on the literal chart subalgebra, transported through its
proved semigroup-algebra equivalence. -/
def monoidChartCoaction (S : AddSubmonoid M) :
    monoidChartAlgebra k S →ₐ[k]
      AddMonoidAlgebra k M ⊗[k] monoidChartAlgebra k S :=
  (Algebra.TensorProduct.map (AlgHom.id k (AddMonoidAlgebra k M))
    (monoidChartAlgebraEquiv k S).toAlgHom).comp
      ((semigroupChartCoaction k S).comp (monoidChartAlgebraEquiv k S).symm.toAlgHom)

@[simp] theorem monoidChartCoaction_character (S : AddSubmonoid M) (m : M) (hm : m∈S) :
    monoidChartCoaction k S (chartCharacter k S m hm) =
      AddMonoidAlgebra.single m 1 ⊗ₜ[k] chartCharacter k S m hm := by
  simp only [monoidChartCoaction,AlgHom.comp_apply,AlgEquiv.coe_algHom,
    monoidChartAlgebraEquiv_symm_character,semigroupChartCoaction_single,
    Algebra.TensorProduct.map_tmul,AlgHom.id_apply,
    monoidChartAlgebraEquiv_single_character]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem semigroupChart_action_coaction (S : AddSubmonoid M) :
    γ[splitTorusOver k M,semigroupChartOver k S] =
      affineCoactionMorphism k (semigroupChartCoaction k S) := by
  apply Over.OverMorphism.ext
  exact semigroupChart_action_spec k S

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The transported chart action really is the spectrum of the displayed
coaction on its actual coordinate subalgebra. -/
theorem monoidChart_action_coaction (S : AddSubmonoid M) :
    γ[splitTorusOver k M,monoidChartSchemeOver k S] =
      affineCoactionMorphism k (monoidChartCoaction k S) := by
  let F := algSpec (CommRingCat.of k)
  letI : F.LaxMonoidal :=
    (AlgebraicGeometry.braidedAlgSpec (R := CommRingCat.of k)).toMonoidal.toLaxMonoidal
  let T : (CommAlgCat k)ᵒᵖ := op (CommAlgCat.of k (AddMonoidAlgebra k M))
  let A : (CommAlgCat k)ᵒᵖ := op (CommAlgCat.of k (monoidChartAlgebra k S))
  let B : (CommAlgCat k)ᵒᵖ := op (CommAlgCat.of k (AddMonoidAlgebra k S))
  let e : A ⟶ B := (CommAlgCat.ofHom (monoidChartAlgebraEquiv k S).toAlgHom).op
  let e' : B ⟶ A := (CommAlgCat.ofHom (monoidChartAlgebraEquiv k S).symm.toAlgHom).op
  change (F.obj T ◁ F.map e) ≫
    γ[splitTorusOver k M,semigroupChartOver k S] ≫ F.map e' = _
  rw [semigroupChart_action_coaction]
  change (F.obj T ◁ F.map e) ≫
    (Functor.LaxMonoidal.μ F T B ≫ F.map
      (CommAlgCat.ofHom (semigroupChartCoaction k S)).op) ≫ F.map e' =
    Functor.LaxMonoidal.μ F T A ≫ F.map (CommAlgCat.ofHom (monoidChartCoaction k S)).op
  simp only [Category.assoc]
  rw [Functor.LaxMonoidal.μ_natural_right_assoc F T e,
    ← F.map_comp,← F.map_comp]
  rfl

end Characters

section AffineIntertwining

variable (k : Type u) [CommRing k]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A literal coaction equation gives a literal affine action equation. -/
theorem affineCoaction_intertwining
    {T Q A B : Type u} [CommRing T] [CommRing Q] [CommRing A] [CommRing B]
    [Algebra k T] [Algebra k Q] [Algebra k A] [Algebra k B]
    (r : Q →ₐ[k] T) (f : A →ₐ[k] B)
    (a : A →ₐ[k] T ⊗[k] A) (b : B →ₐ[k] Q ⊗[k] B)
    (h : (Algebra.TensorProduct.map (AlgHom.id k T) f).comp a =
      (Algebra.TensorProduct.map r (AlgHom.id k B)).comp (b.comp f)) :
    (Spec (CommRingCat.of T)).asOver (Spec (CommRingCat.of k)) ◁
      (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom f).op ≫ affineCoactionMorphism k a =
    ((algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom r).op ▷
        (Spec (CommRingCat.of B)).asOver (Spec (CommRingCat.of k))) ≫
      affineCoactionMorphism k b ≫
        (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom f).op := by
  unfold affineCoactionMorphism
  apply map_coaction_intertwining (algSpec (CommRingCat.of k))
    (CommAlgCat.ofHom r).op (CommAlgCat.ofHom f).op
    (CommAlgCat.ofHom a).op (CommAlgCat.ofHom b).op
  exact congrArg (fun z => (CommAlgCat.ofHom z).op) h

end AffineIntertwining

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.monoidChart_action_coaction
