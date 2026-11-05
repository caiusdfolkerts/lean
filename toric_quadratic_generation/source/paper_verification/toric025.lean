module

public import Lean.Elab.BuiltinEvalCommand
public meta import Lean.Elab.BuiltinEvalCommand
public import Lean.Util.CollectAxioms
public meta import Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public meta import Lean.Util.FoldConsts
public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.Order.KrullDimension
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AsSubring
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Smooth.IntegralClosure
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
public import Mathlib.Topology.Sober
public import paper_verification.toric010
public import paper_verification.toric022
public import paper_verification.toric029
public import paper_verification.toric030

@[expose] public section


-- BEGIN ORIGINAL PaperVerification.ToricBoundaryComponents
section Source_ToricBoundaryComponents

-- original header: module

-- original header: public import PaperVerification.ToricIntrinsicAction
-- original header: public import PaperVerification.ToricTorusGeometricIntegral
-- original header: public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

-- original header: @[expose] public section

/-!
# Actual invariance of the irreducible boundary components

The torus projection has geometrically irreducible fibres, so the
preimage of an irreducible component is irreducible. Its image under the
action lies in the boundary and contains the original component by the
unit section. Maximality forces equality. This argument takes place on
the genuine scheme product and works over finite fields as well.
-/

noncomputable section

universe u v

namespace CategoryTheory

open MonoidalCategory CartesianMonoidalCategory

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- Base change along a product projection, with the literal chosen
cartesian tensor product. -/
theorem isPullback_whiskerLeft_snd (G : C) {X Y : C} (f : Y ⟶ X) :
    IsPullback (G ◁ f) (snd G Y) (snd G X) f := by
  refine IsPullback.mk' (by simp) ?_ ?_
  · intro Z a b hab hsnd
    apply CartesianMonoidalCategory.hom_ext
    · have h := congrArg (fun z => z ≫ fst G X) hab
      simpa only [Category.assoc, whiskerLeft_fst, Category.comp_id] using h
    · exact hsnd
  · intro Z a b hab
    refine ⟨lift (a ≫ fst G X) b, ?_, by simp⟩
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · simpa only [Category.assoc, whiskerLeft_snd, lift_snd_assoc] using hab.symm

end CategoryTheory

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory MonObj

/-- Maximal irreducibility inside the actual boundary, without a chosen
fan or a description by invariant coordinate divisors. -/
def IsBoundaryComponent {X : Type*} [TopologicalSpace X]
    (B Z : Set X) : Prop :=
  Maximal (fun W : Set X => IsIrreducible W ∧ W ⊆ B) Z

/-- An irreducible family inside a boundary that contains one whole
irreducible component must remain in that component. -/
theorem boundaryComponent_image_eq
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {B Z : Set X} (hZ : IsBoundaryComponent B Z)
    (p a : Y → X) (e : X → Y)
    (ha : Continuous a) (hpZ : IsIrreducible (p ⁻¹' Z))
    (hB : ∀ y, p y ∈ B → a y ∈ B)
    (hp : ∀ x, p (e x)=x) (he : ∀ x, a (e x)=x) :
    a '' (p ⁻¹' Z)=Z := by
  have hsub : Z ⊆ a '' (p ⁻¹' Z) := by
    intro x hx
    exact ⟨e x,by simpa only [Set.mem_preimage,hp] using hx,he x⟩
  apply Set.Subset.antisymm _ hsub
  exact hZ.2 ⟨hpZ.image a ha.continuousOn,by
    rintro x ⟨y,hy,rfl⟩
    exact hB y (hZ.1.2 hy)⟩ hsub

/-- An open-immersion pullback identifies its actual open image. -/
theorem opensRange_of_isPullback {P A B X : Scheme.{u}}
    {f : P ⟶ A} {g : P ⟶ B} {a : A ⟶ X} {j : B ⟶ X}
    (h : IsPullback f g a j) [IsOpenImmersion j] :
    letI : IsOpenImmersion f := MorphismProperty.of_isPullback h.flip inferInstance
    f.opensRange = a ⁻¹ᵁ j.opensRange := by
  letI : IsOpenImmersion f := MorphismProperty.of_isPullback h.flip inferInstance
  have he := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback h.flip
    (⊤ : B.Opens)
  simpa only [Scheme.Hom.preimage_top,Scheme.Hom.image_top_eq_opensRange] using he

variable (k : Type u) [Field k] (n : ℕ)
    (X : Over (Spec (CommRingCat.of k)))
    [ModObj (splitTorusOver k (Fin n → ℤ)) X]

namespace SplitToricEmbedding

variable {k n X} (T : SplitToricEmbedding k n X)

/-- The action and projection have exactly the same inverse image of the
actual dense torus open. This uses the genuine action pullback square. -/
theorem action_preimage_torusOpen :
    (γ[splitTorusOver k (Fin n → ℤ),X]).left ⁻¹ᵁ T.torusOpen =
      (snd (splitTorusOver k (Fin n → ℤ)) X).left ⁻¹ᵁ T.torusOpen := by
  letI : IsOpenImmersion ((Over.forget (Spec (CommRingCat.of k))).map T.torus) :=
    T.open_immersion
  have ha := (T.torus_action_isPullback).map (Over.forget (Spec (CommRingCat.of k)))
  have hp := (isPullback_whiskerLeft_snd (splitTorusOver k (Fin n → ℤ)) T.torus).map
    (Over.forget (Spec (CommRingCat.of k)))
  exact (opensRange_of_isPullback ha).symm.trans (opensRange_of_isPullback hp)

theorem action_preimage_boundary :
    (γ[splitTorusOver k (Fin n → ℤ),X]).left ⁻¹' T.boundary =
      (snd (splitTorusOver k (Fin n → ℤ)) X).left ⁻¹' T.boundary := by
  have h := congrArg (fun U : (splitTorusOver k (Fin n → ℤ) ⊗ X).left.Opens =>
    (U : Set (splitTorusOver k (Fin n → ℤ) ⊗ X).left)ᶜ)
    T.action_preimage_torusOpen
  exact h

/-- Every actual irreducible boundary component is invariant under the
whole group scheme action. No rational-point density is used. -/
theorem boundaryComponent_invariant {Z : Set X.left}
    (hZ : IsBoundaryComponent T.boundary Z) :
    (γ[splitTorusOver k (Fin n → ℤ),X]).left ''
        ((snd (splitTorusOver k (Fin n → ℤ)) X).left ⁻¹' Z) = Z := by
  let G := splitTorusOver k (Fin n → ℤ)
  let e : X ⟶ G ⊗ X := lift (1 : X ⟶ G) (𝟙 X)
  have hp : e ≫ snd G X = 𝟙 X := by simp only [e,lift_snd]
  have ha : e ≫ γ[G,X] = 𝟙 X := by
    change (1 : X ⟶ G) • (𝟙 X) = 𝟙 X
    exact one_smul _ _
  apply boundaryComponent_image_eq hZ
    (snd G X).left (γ[G,X]).left e.left (γ[G,X]).left.continuous
    (torusProjection_isIrreducible_preimage k n X hZ.1.1)
  · intro y hy
    change y ∈ (γ[G,X]).left ⁻¹' T.boundary
    rw [T.action_preimage_boundary]
    exact hy
  · intro x
    exact congrArg (fun f : X ⟶ X => f.left x) hp
  · intro x
    exact congrArg (fun f : X ⟶ X => f.left x) ha

end SplitToricEmbedding

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.boundaryComponent_invariant
end
end Source_ToricBoundaryComponents
-- END ORIGINAL PaperVerification.ToricBoundaryComponents


-- BEGIN ORIGINAL PaperVerification.ToricBoundaryFixedPoints
section Source_ToricBoundaryFixedPoints

-- original header: module

-- original header: public import PaperVerification.ToricBoundaryComponents
-- original header: public import Mathlib.Topology.Sober
-- original header: public import Mathlib.Order.KrullDimension

-- original header: @[expose] public section

/-!
# The action graph fixes the codimension-one boundary points

Every codimension-one point of a proper closed subset of an integral
scheme is the generic point of one of its irreducible components. The
components of the torus-product boundary are exactly the inverse images
of the original boundary components. The action graph preserves each of
them, hence fixes their genuine scheme points.
-/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace PaperVerification.ToricSchemes

section Topology

variable {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]

/-- Relative irreducible components exist without a finiteness hypothesis. -/
theorem exists_boundaryComponent_containing {Z S : Set A}
    (hS : IsIrreducible S) (hSZ : S⊆Z) :
    ∃ W : Set A,IsBoundaryComponent Z W ∧ S⊆W := by
  classical
  obtain ⟨W,hSW,hW⟩ := zorn_subset_nonempty
    {W : Set A | IsPreirreducible W ∧ W⊆Z}
    (fun c hc hchain _=>by
      refine ⟨⋃₀ c,⟨?_,?_⟩,?_⟩
      · intro U V hU hV hSU hSV
        obtain ⟨a,ha,haU⟩ := hSU
        obtain ⟨b,hb,hbV⟩ := hSV
        obtain ⟨P,hP,haP⟩ := Set.mem_sUnion.mp ha
        obtain ⟨Q,hQ,hbQ⟩ := Set.mem_sUnion.mp hb
        rcases hchain.total hP hQ with hPQ | hQP
        · obtain ⟨x,hxQ,hxUV⟩ := (hc hQ).1 U V hU hV
            ⟨a,hPQ haP,haU⟩ ⟨b,hbQ,hbV⟩
          exact ⟨x,Set.mem_sUnion_of_mem hxQ hQ,hxUV⟩
        · obtain ⟨x,hxP,hxUV⟩ := (hc hP).1 U V hU hV
            ⟨a,haP,haU⟩ ⟨b,hQP hbQ,hbV⟩
          exact ⟨x,Set.mem_sUnion_of_mem hxP hP,hxUV⟩
      · rintro x ⟨P,hP,hxP⟩
        exact (hc hP).2 hxP
      · intro P hP
        exact Set.subset_sUnion_of_mem hP)
    S ⟨hS.2,hSZ⟩
  refine ⟨W,⟨⟨⟨hS.1.mono hSW,hW.prop.1⟩,hW.prop.2⟩,?_⟩,hSW⟩
  intro V hV hWV
  exact (hW.eq_of_subset ⟨hV.1.2,hV.2⟩ hWV).ge

theorem boundaryComponent_isClosed {Z W : Set A} (hZ : IsClosed Z)
    (hW : IsBoundaryComponent Z W) : IsClosed W := by
  have hc : closure W⊆W := hW.2
    ⟨hW.1.1.closure,closure_minimal hW.1.2 hZ⟩ subset_closure
  exact isClosed_of_closure_subset hc

/-- An irreducible-preimage surjection identifies the actual components
of a closed boundary with their inverse images. -/
theorem boundaryComponent_preimage (p : B→A) (hp : Continuous p)
    (hsurj : Function.Surjective p)
    (hirr : ∀ Z : Set A,IsIrreducible Z→IsIrreducible (p ⁻¹' Z))
    {Z W : Set A} (hW : IsBoundaryComponent Z W) :
    IsBoundaryComponent (p ⁻¹' Z) (p ⁻¹' W) := by
  refine ⟨⟨hirr W hW.1.1,Set.preimage_mono hW.1.2⟩,?_⟩
  intro V hV hWV
  have hWV' : W⊆p '' V := by
    intro x hx
    obtain ⟨y,rfl⟩ := hsurj x
    exact ⟨y,hWV hx,rfl⟩
  have hmax : p '' V⊆W := hW.2
    ⟨hV.1.image p hp.continuousOn,by
      rintro x ⟨y,hy,rfl⟩
      exact hV.2 hy⟩ hWV'
  exact fun y hy=>hmax ⟨y,hy,rfl⟩

theorem boundaryComponent_eq_preimage (p : B→A) (hp : Continuous p)
    (hirr : ∀ Z : Set A,IsIrreducible Z→IsIrreducible (p ⁻¹' Z))
    {Z : Set A} {W : Set B} (hW : IsBoundaryComponent (p ⁻¹' Z) W) :
    ∃ C : Set A,IsBoundaryComponent Z C ∧ W=p ⁻¹' C := by
  obtain ⟨C,hC,hWC⟩ := exists_boundaryComponent_containing
    (hW.1.1.image p hp.continuousOn) (by
      rintro x ⟨y,hy,rfl⟩
      exact hW.1.2 hy)
  have hsub : W⊆p ⁻¹' C := fun y hy=>hWC ⟨y,hy,rfl⟩
  exact ⟨C,hC,Set.Subset.antisymm hsub
    (hW.2 ⟨hirr C hC.1.1,Set.preimage_mono hC.1.2⟩ hsub)⟩

theorem boundaryComponent_homeomorph (e : A ≃ₜ A) {Z W : Set A}
    (he : e ⁻¹' Z=Z) (hW : IsBoundaryComponent Z W) :
    IsBoundaryComponent Z (e '' W) := by
  refine ⟨⟨hW.1.1.image e e.continuous.continuousOn,?_⟩,?_⟩
  · rintro x ⟨y,hy,rfl⟩
    change y∈e ⁻¹' Z
    rw [he]
    exact hW.1.2 hy
  · intro V hV hWV
    have hpre : IsIrreducible (e ⁻¹' V) := by
      simpa only [e.image_symm] using hV.1.image e.symm e.symm.continuous.continuousOn
    have hpreZ : e ⁻¹' V⊆Z := by
      rw [← he]
      exact Set.preimage_mono hV.2
    have hWpre : W⊆e ⁻¹' V := fun x hx=>hWV ⟨x,hx,rfl⟩
    have hmax := hW.2 ⟨hpre,hpreZ⟩ hWpre
    intro x hx
    exact ⟨e.symm x,hmax (by simpa),e.apply_symm_apply x⟩

end Topology

section Codimension

variable {X : Scheme.{u}} [IsIntegral X]

/-- A codimension-one point in a proper closed boundary is itself the
generic point of an actual maximal irreducible boundary component. -/
theorem codimensionOne_boundaryComponent {Z : Set X} (hZ : IsClosed Z)
    (hgeneric : genericPoint X∉Z) (x : X) (hx : x∈Z)
    (hcodim : Order.coheight x=1) : IsBoundaryComponent Z (closure {x}) := by
  refine ⟨⟨isIrreducible_singleton.closure,
    closure_minimal (Set.singleton_subset_iff.mpr hx) hZ⟩,?_⟩
  intro W hW hxW
  let y := hW.1.genericPoint
  have hy : IsGenericPoint y (closure W) := hW.1.isGenericPoint_genericPoint_closure
  have hyZ : y∈Z := (closure_minimal hW.2 hZ) hy.mem
  have hxy : x≤y := Scheme.le_iff_specializes.mpr
    (hy.specializes (subset_closure (hxW (subset_closure (Set.mem_singleton x)))))
  have hyx : y=x := by
    by_contra hne
    have hlt : x<y := lt_of_le_not_ge hxy (by
      intro hyx
      exact hne ((Scheme.le_iff_specializes.mp hxy).antisymm
        (Scheme.le_iff_specializes.mp hyx)).eq)
    have hc : Order.coheight y≤0 :=
      ((Order.coheight_eq_coe_add_one_iff (x := x) (n := 0)).mp
        (by simpa using hcodim)).2.2 y hlt
    have hmax : IsMax y := Order.coheight_eq_zero.mp (le_antisymm hc bot_le)
    have hty : (⊤ : X) ≤ y := hmax (show y ≤ ⊤ from le_top)
    have htop : y=⊤ :=
      ((Scheme.le_iff_specializes.mp hty).antisymm
        (Scheme.le_iff_specializes.mp (show y ≤ ⊤ from le_top))).eq
    apply hgeneric
    change (⊤ : X) ∈ Z
    exact htop ▸ hyZ
  rw [← hyx,hy.def]
  exact subset_closure

end Codimension

variable (k : Type u) [Field k] (n : ℕ)
    (X : Over (Spec (CommRingCat.of k)))
    [ModObj (splitTorusOver k (Fin n→ℤ)) X]

namespace SplitToricEmbedding

variable {k n X} (T : SplitToricEmbedding k n X)

def graphIso (_T : SplitToricEmbedding k n X) : (splitTorusOver k (Fin n→ℤ) ⊗ X).left ≅
    (splitTorusOver k (Fin n→ℤ) ⊗ X).left :=
  (Over.forget (Spec (CommRingCat.of k))).mapIso
    (ModObj.actionGraphIso (splitTorusOver k (Fin n→ℤ)) X)

def productBoundary : Set (splitTorusOver k (Fin n→ℤ) ⊗ X).left :=
  (snd (splitTorusOver k (Fin n→ℤ)) X).left ⁻¹' T.boundary

@[reassoc] theorem graph_hom_snd :
    T.graphIso.hom ≫ (snd (splitTorusOver k (Fin n→ℤ)) X).left =
      (γ[splitTorusOver k (Fin n→ℤ),X]).left := by
  exact congrArg (fun a : splitTorusOver k (Fin n→ℤ) ⊗ X ⟶ X=>a.left)
    (ModObj.actionGraphIso_hom_snd (splitTorusOver k (Fin n→ℤ)) X)

theorem graph_preimage_productBoundary :
    T.graphIso.hom ⁻¹' T.productBoundary=T.productBoundary := by
  change ((T.graphIso.hom ≫ (snd (splitTorusOver k (Fin n→ℤ)) X).left) ⁻¹' T.boundary) = _
  rw [graph_hom_snd]
  exact T.action_preimage_boundary

theorem graph_preserves_productComponent {Z : Set X.left}
    (hZ : IsBoundaryComponent T.boundary Z) :
    T.graphIso.hom '' ((snd (splitTorusOver k (Fin n→ℤ)) X).left ⁻¹' Z) =
      (snd (splitTorusOver k (Fin n→ℤ)) X).left ⁻¹' Z := by
  let G := splitTorusOver k (Fin n→ℤ)
  let p := (snd G X).left
  have hpSurj : Function.Surjective p := by
    intro x
    refine ⟨(lift (1 : X ⟶ G) (𝟙 X)).left x,?_⟩
    exact congrArg (fun f : X ⟶ X=>f.left x) (lift_snd (1 : X ⟶ G) (𝟙 X))
  have hcomp := boundaryComponent_preimage p p.continuous hpSurj
    (fun Z hZ=>torusProjection_isIrreducible_preimage k n X hZ) hZ
  have himage := boundaryComponent_homeomorph T.graphIso.hom.homeomorph
    T.graph_preimage_productBoundary hcomp
  have hsub : T.graphIso.hom '' (p ⁻¹' Z)⊆p ⁻¹' Z := by
    rintro y ⟨z,hz,rfl⟩
    have hact : (γ[G,X]).left z∈Z := by
      rw [← T.boundaryComponent_invariant hZ]
      exact ⟨z,hz,rfl⟩
    change (T.graphIso.hom ≫ p) z∈Z
    rw [graph_hom_snd]
    exact hact
  exact Set.Subset.antisymm hsub (himage.2 hcomp.1 hsub)

/-- Once integrality of the actual product is supplied (derived in the
smooth application), the graph automorphism fixes every codimension-one
point outside the product torus. -/
theorem graph_fixes_codimensionOne_boundary
    [IsIntegral X.left]
    [IsIntegral (splitTorusOver k (Fin n→ℤ) ⊗ X).left]
    (y : (splitTorusOver k (Fin n→ℤ) ⊗ X).left)
    (hy : y∈T.productBoundary) (hcodim : Order.coheight y=1) :
    T.graphIso.hom y=y := by
  let G := splitTorusOver k (Fin n→ℤ)
  let p := (snd G X).left
  have hclosed : IsClosed T.productBoundary := T.boundary_isClosed.preimage p.continuous
  letI : IsIntegral (splitTorus k (Fin n→ℤ)) :=
    splitTorus_integral k n
  have hopen : Nonempty (p ⁻¹ᵁ T.torusOpen) := by
    let t := genericPoint (splitTorus k (Fin n→ℤ))
    let x := T.torus.left t
    refine ⟨⟨(lift (1 : X ⟶ G) (𝟙 X)).left x,?_⟩⟩
    change p ((lift (1 : X ⟶ G) (𝟙 X)).left x)∈T.torusOpen
    have he : p ((lift (1 : X ⟶ G) (𝟙 X)).left x) = x :=
      congrArg (fun f : X ⟶ X=>f.left x)
        (lift_snd (1 : X ⟶ G) (𝟙 X))
    rw [he]
    exact ⟨t,rfl⟩
  letI := hopen
  have hgeneric : genericPoint (G⊗X).left∉T.productBoundary := by
    change ¬ ¬ (p (genericPoint (G⊗X).left) ∈ T.torusOpen)
    exact not_not.mpr (genericPoint_mem_open (G⊗X).left (p ⁻¹ᵁ T.torusOpen))
  have hcomp := codimensionOne_boundaryComponent hclosed hgeneric y hy hcodim
  obtain ⟨Z,hZ,hclosure⟩ := boundaryComponent_eq_preimage p p.continuous
    (fun Z hZ=>torusProjection_isIrreducible_preimage k n X hZ) hcomp
  have himage : T.graphIso.hom '' closure {y}=closure {y} := by
    rw [hclosure]
    exact T.graph_preserves_productComponent hZ
  have hgp : IsGenericPoint (T.graphIso.hom y) (closure {y}) := by
    have h := (isGenericPoint_closure (x := y)).image T.graphIso.hom.continuous
    rw [himage,closure_closure] at h
    exact h
  exact hgp.eq isGenericPoint_closure

end SplitToricEmbedding

end PaperVerification.ToricSchemes
end
end Source_ToricBoundaryFixedPoints
-- END ORIGINAL PaperVerification.ToricBoundaryFixedPoints


-- BEGIN ORIGINAL PaperVerification.ToricActionProductProperties
section Source_ToricActionProductProperties

-- original header: module

-- original header: public import PaperVerification.ToricBoundaryFixedPoints
-- original header: public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

-- original header: @[expose] public section

/-! # Actual geometric properties of the torus action product -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits
open MonoidalCategory CartesianMonoidalCategory MonObj
open PaperVerification.ToricCharacters

namespace PaperVerification.ToricSchemes

variable (k : Type u) [Field k] (n : ℕ)
    (X : Over (Spec (CommRingCat.of k)))

/-- The already proved torus integrality with the literal over-object domain. -/
instance splitTorusOver_left_integral :
    IsIntegral (splitTorusOver k (Fin n→ℤ)).left :=
  splitTorus_integral k n

instance torusProduct_integral [IsIntegral X.left] [IsLocallyNoetherian X.left] :
    IsIntegral (splitTorusOver k (Fin n→ℤ) ⊗ X).left := by
  change IsIntegral (pullback (splitTorusOver k (Fin n→ℤ)).hom X.hom)
  infer_instance

/-- The self-action object's scheme is the same actual product scheme. -/
instance torusActionObject_integral [IsIntegral X.left] [IsLocallyNoetherian X.left] :
    IsIntegral (MonoidalLeftActionStruct.actionObj (splitTorusOver k (Fin n→ℤ)) X).left := by
  change IsIntegral (splitTorusOver k (Fin n→ℤ) ⊗ X).left
  exact torusProduct_integral k n X

instance torusProjection_surjective :
    Surjective (snd (splitTorusOver k (Fin n→ℤ)) X).left := by
  change Surjective (pullback.snd (splitTorusOver k (Fin n→ℤ)).hom X.hom)
  infer_instance

variable [ModObj (splitTorusOver k (Fin n→ℤ)) X]

instance torusAction_surjective : Surjective (γ[splitTorusOver k (Fin n→ℤ),X]).left := by
  constructor
  intro x
  let G := splitTorusOver k (Fin n→ℤ)
  let e : X ⟶ G⊗X := lift (1 : X ⟶ G) (𝟙 X)
  refine ⟨e.left x,?_⟩
  have h : e≫γ[G,X]=𝟙 X := by
    change (1 : X ⟶ G) • (𝟙 X)=𝟙 X
    exact one_smul _ _
  exact congrArg (fun f : X ⟶ X=>f.left x) h

namespace SplitToricEmbedding

variable {k n X} (T : SplitToricEmbedding k n X) [Smooth X.hom]

/-- The given immersion, exposed at the literal split-torus scheme type. -/
instance torus_scheme_isOpenImmersion :
    IsOpenImmersion (show splitTorus k (Fin n→ℤ) ⟶ X.left from T.torus.left) :=
  T.open_immersion

/-- The same given immersion, exposed at its actual affine spectrum type. -/
instance torus_coordinate_isOpenImmersion :
    IsOpenImmersion (show Spec (CommRingCat.of (torusCoordinateRing k n)) ⟶ X.left
      from T.torus.left) :=
  T.open_immersion

/-- The actual torus inclusion respects the given structure maps. -/
instance torus_scheme_isOver :
    (show splitTorus k (Fin n→ℤ) ⟶ X.left from T.torus.left).IsOver
      (Spec (CommRingCat.of k)) where
  comp_over := T.torus.w

/-- The same structural compatibility at the literal coordinate spectrum. -/
instance torus_coordinate_isOver :
    (show Spec (CommRingCat.of (torusCoordinateRing k n)) ⟶ X.left
      from T.torus.left).IsOver (Spec (CommRingCat.of k)) where
  comp_over := T.torus.w

include T in
theorem torus_smooth : Smooth (splitTorusOver k (Fin n→ℤ)).hom := by
  rw [← T.torus.w]
  infer_instance

include T in
/-- The ordinary smoothness of the action product follows from the
actual dense open torus immersion and base change. -/
theorem product_smooth : Smooth (splitTorusOver k (Fin n→ℤ) ⊗ X).hom := by
  let G := splitTorusOver k (Fin n→ℤ)
  letI : Smooth G.hom := T.torus_smooth
  letI : Smooth (snd G X).left := by
    change Smooth (pullback.snd G.hom X.hom)
    infer_instance
  rw [← (snd G X).w]
  infer_instance

include T in
theorem product_locallyNoetherian :
    IsLocallyNoetherian (splitTorusOver k (Fin n→ℤ) ⊗ X).left := by
  letI := T.product_smooth
  exact LocallyOfFiniteType.isLocallyNoetherian
    (splitTorusOver k (Fin n→ℤ) ⊗ X).hom

end SplitToricEmbedding

end PaperVerification.ToricSchemes
end
end Source_ToricActionProductProperties
-- END ORIGINAL PaperVerification.ToricActionProductProperties


-- BEGIN ORIGINAL PaperVerification.ToricCartierOrders
section Source_ToricCartierOrders

-- original header: module

-- original header: public import PaperVerification.ToricCartierPresentation
-- original header: public import Mathlib.AlgebraicGeometry.OrderOfVanishing
-- original header: public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic

-- original header: @[expose] public section

/-!
# Orders and degrees of actual Cartier divisors

The coefficient is computed using Mathlib's order in the actual local ring.
Since our local generators generate `O(D)`, their orders have the opposite
sign from the coefficients of `D`. Independence of the chosen frame follows
from its regular-unit transition function. The construction descends through
the equivalence of embedded fractional sheaves.

The cycle constructor below requires a proof of local finiteness. Thus the
definition of degree cannot silently replace an infinite divisor by a finite
sum or treat a nonproper curve as a proper curve. In the applications the
support and the actual residue degrees are computed on the invariant curve.
-/

noncomputable section

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry

namespace PaperVerification.ToricSchemes

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

theorem rationalOrder_one (x : X) : X.ord (1 : X.functionField) x = 0 := by
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨x,trivial⟩⟩
  simpa only [map_one] using
    X.ord_of_isUnit (U := ⊤) (f := (1 : Γ(X,⊤))) isUnit_one
      (x := x) (show x ∈ (⊤ : X.Opens) from trivial)

theorem rationalOrder_inv {r : X.functionField} (hr : r ≠ 0) (x : X) :
    X.ord r⁻¹ x = - X.ord r x := by
  have h := X.ord_mul (x := x) hr (inv_ne_zero hr)
  rw [mul_inv_cancel₀ hr,rationalOrder_one] at h
  omega

theorem rationalOrder_div {r s : X.functionField}
    (hr : r ≠ 0) (hs : s ≠ 0) (x : X) :
    X.ord (r/s) x = X.ord r x - X.ord s x := by
  rw [div_eq_mul_inv,X.ord_mul hr (inv_ne_zero hs),rationalOrder_inv hs]
  rfl

theorem rationalOrder_pow {r : X.functionField} (hr : r ≠ 0)
    (n : ℕ) (x : X) : X.ord (r^n) x = (n : ℤ) * X.ord r x := by
  induction n with
  | zero => simp [rationalOrder_one]
  | succ n ih =>
      rw [pow_succ,X.ord_mul (pow_ne_zero n hr) hr,ih]
      push_cast
      ring

theorem rationalOrder_zpow {r : X.functionField} (hr : r ≠ 0)
    (n : ℤ) (x : X) : X.ord (r^n) x = n * X.ord r x := by
  cases n with
  | ofNat n => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using rationalOrder_pow hr n x
  | negSucc n =>
      rw [zpow_negSucc,rationalOrder_inv (pow_ne_zero _ hr),rationalOrder_pow hr,
        Int.negSucc_eq]
      push_cast
      ring

namespace CartierData

variable (D E : CartierData X)

/-- The order of an actual rational frame is independent of the frame at
every point in the overlap. -/
theorem frameOrder_eq {U W : X.Opens} [Nonempty U] [Nonempty W]
    (e : D.Frame U) (f : D.Frame W) {x : X} (hxU : x∈U) (hxW : x∈W) :
    X.ord (D.frameRationalGenerator e) x =
      X.ord (D.frameRationalGenerator f) x := by
  let V : X.Opens := U⊓W
  letI : Nonempty V := ⟨⟨x,hxU,hxW⟩⟩
  obtain ⟨a,ha⟩ := D.exists_frameTransitionUnit e f
    (V := V) inf_le_left inf_le_right
  have h := X.ord_of_isUnit (U := V) a.isUnit (x := x) ⟨hxU,hxW⟩
  rw [ha,rationalOrder_div (D.frameRationalGenerator_ne_zero e)
    (D.frameRationalGenerator_ne_zero f)] at h
  omega

/-- The actual Weil coefficient of a Cartier divisor. At noncodimension-one
points the value is zero, as in Mathlib's order function. -/
def weilCoefficient (x : X) : ℤ :=
  - X.ord (D.localCocycle.generator x : X.functionField) x

/-- Any actual local frame computes the coefficient, not only the selected
frame used in the definition. -/
theorem weilCoefficient_eq_neg_frameOrder {U : X.Opens} [Nonempty U]
    (e : D.Frame U) {x : X} (hxU : x∈U) :
    D.weilCoefficient x = -X.ord (D.frameRationalGenerator e) x := by
  let W := invertibleOpen D.locallyFree x
  letI : Nonempty W := ⟨⟨x,mem_invertibleOpen D.locallyFree x⟩⟩
  change -X.ord (D.frameRationalGenerator (invertibleFrame D.locallyFree x)) x = _
  rw [D.frameOrder_eq (invertibleFrame D.locallyFree x) e
    (mem_invertibleOpen D.locallyFree x) hxU]

@[simp] theorem weilCoefficient_eq_zero_of_coheight_ne_one {x : X}
    (hx : Order.coheight x ≠ 1) : D.weilCoefficient x = 0 := by
  simp [weilCoefficient,Scheme.ord_eq_zero_of_coheight_neq_one hx]

/-- Frames of equivalent embedded fractional sheaves differ by an actual
regular unit. This conclusion uses the embedding-preserving equivalence,
not merely an isomorphism of the underlying line bundles. -/
theorem exists_equivalentFrameTransitionUnit (hDE : D.Equivalent E)
    {U W V : X.Opens} [Nonempty U] [Nonempty W] [Nonempty V]
    (e : D.Frame U) (f : E.Frame W) (hVU : V≤U) (hVW : V≤W) :
    ∃ a : Γ(X,V)ˣ, X.germToFunctionField V (a : Γ(X,V)) =
      D.frameRationalGenerator e / E.frameRationalGenerator f := by
  have hD : D.frameRationalGenerator e ∈ E.sectionValueRange V := by
    rw [← D.equivalent_sectionValueRange E hDE V]
    exact ⟨D.frameGenerator e V hVU,D.sectionValue_frameGenerator e hVU⟩
  have hE : E.frameRationalGenerator f ∈ D.sectionValueRange V := by
    rw [D.equivalent_sectionValueRange E hDE V]
    exact ⟨E.frameGenerator f V hVW,E.sectionValue_frameGenerator f hVW⟩
  obtain ⟨a,ha⟩ := (E.mem_sectionValueRange_iff f hVW _).mp hD
  obtain ⟨b,hb⟩ := (D.mem_sectionValueRange_iff e hVU _).mp hE
  have hab : a*b=1 := by
    apply X.germToFunctionField_injective V
    rw [map_mul,map_one]
    apply mul_right_cancel₀ (D.frameRationalGenerator_ne_zero e)
    rw [mul_assoc,hb,ha,one_mul]
  let aUnit : Γ(X,V)ˣ := ⟨a,b,hab,by simpa only [mul_comm] using hab⟩
  exact ⟨aUnit,(eq_div_iff (E.frameRationalGenerator_ne_zero f)).mpr ha⟩

theorem equivalent_weilCoefficient (hDE : D.Equivalent E) :
    D.weilCoefficient = E.weilCoefficient := by
  funext x
  let U := invertibleOpen D.locallyFree x
  let W := invertibleOpen E.locallyFree x
  let V : X.Opens := U⊓W
  have hxU : x∈U := mem_invertibleOpen D.locallyFree x
  have hxW : x∈W := mem_invertibleOpen E.locallyFree x
  letI : Nonempty U := ⟨⟨x,hxU⟩⟩
  letI : Nonempty W := ⟨⟨x,hxW⟩⟩
  letI : Nonempty V := ⟨⟨x,hxU,hxW⟩⟩
  let e := invertibleFrame D.locallyFree x
  let f := invertibleFrame E.locallyFree x
  obtain ⟨a,ha⟩ := D.exists_equivalentFrameTransitionUnit E hDE e f
    (V := V) inf_le_left inf_le_right
  have h := X.ord_of_isUnit (U := V) a.isUnit (x := x) ⟨hxU,hxW⟩
  rw [ha,rationalOrder_div (D.frameRationalGenerator_ne_zero e)
    (E.frameRationalGenerator_ne_zero f)] at h
  rw [D.weilCoefficient_eq_neg_frameOrder e hxU,
    E.weilCoefficient_eq_neg_frameOrder f hxW]
  omega

/-- The actual Weil cycle, provided its coefficients have locally finite
support. The coefficients are already fixed by the actual local orders. -/
def weilCycle (h : LocallyFiniteSupport D.weilCoefficient) :
    AlgebraicCycle X ℤ where
  toFun := D.weilCoefficient
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' x _ := h x

@[simp] theorem weilCycle_apply
    (h : LocallyFiniteSupport D.weilCoefficient) (x : X) :
    D.weilCycle h x = D.weilCoefficient x := rfl

theorem weilCycle_isWeilDivisor
    (h : LocallyFiniteSupport D.weilCoefficient) :
    AlgebraicCycle.IsWeilDivisor (D.weilCycle h) := by
  intro x hx
  by_contra hcodim
  exact hx (D.weilCoefficient_eq_zero_of_coheight_ne_one hcodim)

/-- Finite support is sufficient, without a separatedness or a T1-space
assumption. This is useful for an explicitly computed invariant curve. -/
theorem locallyFiniteSupport_weilCoefficient_of_finite
    (h : (Function.support D.weilCoefficient).Finite) :
    LocallyFiniteSupport D.weilCoefficient := by
  intro x
  exact ⟨Set.univ,Filter.univ_mem,by simpa only [Set.univ_inter] using h⟩

/-- Degree uses the actual residue degrees of the structure morphism. -/
def degree {Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace X]
    (h : LocallyFiniteSupport D.weilCoefficient) : ℤ :=
  AlgebraicCycle.degree f (D.weilCycle h)

theorem degree_eq_finsum {Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace X]
    (h : LocallyFiniteSupport D.weilCoefficient) :
    D.degree f h = ∑ᶠ x, f.residueDegree x • D.weilCoefficient x := rfl

theorem degree_eq_sum_of_support_subset {Y : Scheme.{u}} (f : X ⟶ Y)
    [CompactSpace X] (h : LocallyFiniteSupport D.weilCoefficient)
    (s : Finset X) (hs : Function.support D.weilCoefficient ⊆ s) :
    D.degree f h = ∑ x ∈ s, f.residueDegree x • D.weilCoefficient x := by
  rw [degree_eq_finsum]
  apply finsum_eq_finsetSum_of_support_subset
  intro x hx
  apply hs
  intro hz
  exact hx (by simp [hz])

theorem equivalent_degree (hDE : D.Equivalent E) {Y : Scheme.{u}}
    (f : X ⟶ Y) [CompactSpace X]
    (hD : LocallyFiniteSupport D.weilCoefficient)
    (hE : LocallyFiniteSupport E.weilCoefficient) :
    D.degree f hD = E.degree f hE := by
  rw [degree_eq_finsum,degree_eq_finsum,D.equivalent_weilCoefficient E hDE]

end CartierData

namespace CartierDivisor

/-- Weil coefficients are independent of the presentation of a Cartier
divisor as an invertible embedded fractional sheaf. -/
def weilCoefficient : CartierDivisor X → X → ℤ :=
  Quotient.lift CartierData.weilCoefficient
    (fun _ _ h => CartierData.equivalent_weilCoefficient _ _ h)

@[simp] theorem weilCoefficient_ofData (D : CartierData X) :
    weilCoefficient (ofData D) = D.weilCoefficient := rfl

end CartierDivisor

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.CartierData.equivalent_weilCoefficient
#print axioms PaperVerification.ToricSchemes.CartierData.equivalent_degree
end
end Source_ToricCartierOrders
-- END ORIGINAL PaperVerification.ToricCartierOrders


-- BEGIN ORIGINAL PaperVerification.ToricNormalHeightOne
section Source_ToricNormalHeightOne

-- original header: module

-- original header: public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
-- original header: public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
-- original header: public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
-- original header: public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
-- original header: public import Mathlib.RingTheory.Localization.AsSubring

-- original header: @[expose] public section

/-!
# A normal Noetherian domain is the intersection of its height-one local rings

The argument uses actual denominator ideals in the fraction field. A prime
denominator ideal has height one: the determinant trick supplies an element
whose principal ideal has that prime as a minimal prime. Associated primes
of the quotient of the fraction field by the ring then detect every rational
function that is not regular. No factoriality assumption is used.
-/

noncomputable section

namespace PaperVerification.ToricSchemes

open scoped nonZeroDivisors

variable (R K : Type*) [CommRing R] [Field K] [Algebra R K]
    [IsDomain R] [IsFractionRing R K]

/-- The actual image of the domain in its fraction field, as an `R`-module. -/
def fractionRingImage : Submodule R K :=
  LinearMap.range (Algebra.linearMap R K)

@[simp] theorem mem_fractionRingImage (z : K) :
    z ∈ fractionRingImage R K ↔ ∃ a : R, algebraMap R K a = z := Iff.rfl

/-- The ideal of denominators that clear the given rational function. -/
def fractionDenominatorIdeal (z : K) : Ideal R :=
  (fractionRingImage R K).colon {z}

@[simp] theorem mem_fractionDenominatorIdeal (z : K) (r : R) :
    r ∈ fractionDenominatorIdeal R K z ↔
      ∃ a : R, algebraMap R K a = algebraMap R K r * z := by
  rw [fractionDenominatorIdeal,Submodule.mem_colon_singleton]
  change (∃ a : R,algebraMap R K a = r • z) ↔ _
  rw [Algebra.smul_def]

theorem fractionDenominatorIdeal_eq_top_iff (z : K) :
    fractionDenominatorIdeal R K z = ⊤ ↔ z ∈ fractionRingImage R K := by
  rw [Ideal.eq_top_iff_one,mem_fractionDenominatorIdeal,mem_fractionRingImage]
  simp only [map_one,one_mul]

theorem fractionDenominatorIdeal_ne_bot (z : K) :
    fractionDenominatorIdeal R K z ≠ ⊥ := by
  obtain ⟨a,b,hb,hab⟩ := IsFractionRing.div_surjective R z
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap R K b ≠ 0 := by
    intro h
    apply hb0
    exact (IsFractionRing.injective R K) (by simpa only [map_zero] using h)
  have hbmem : b ∈ fractionDenominatorIdeal R K z := by
    apply (mem_fractionDenominatorIdeal R K z b).mpr
    refine ⟨a,?_⟩
    rw [← hab]
    field_simp
  intro h
  exact hb0 (by simpa only [h,Submodule.mem_bot] using hbmem)

variable [IsNoetherianRing R] [IsIntegrallyClosed R]

/-- A denominator ideal that is prime is necessarily a height-one prime.
The nontrivial step is the determinant trick on its actual image in `K`. -/
theorem fractionDenominatorIdeal_height_eq_one (z : K)
    (hprime : (fractionDenominatorIdeal R K z).IsPrime) :
    (fractionDenominatorIdeal R K z).height = 1 := by
  let P : Ideal R := fractionDenominatorIdeal R K z
  letI : P.IsPrime := hprime
  have hP0 : P ≠ ⊥ := fractionDenominatorIdeal_ne_bot R K z
  let N : Submodule R K := Submodule.map (Algebra.linearMap R K) (P : Submodule R R)
  have hN0 : N ≠ ⊥ := by
    intro hN
    apply hP0
    apply le_antisymm _ bot_le
    intro a ha
    have haK : algebraMap R K a ∈ N := Submodule.mem_map.mpr ⟨a,ha,rfl⟩
    have ha0 : algebraMap R K a = 0 := by simpa only [hN,Submodule.mem_bot] using haK
    change a = 0
    exact (IsFractionRing.injective R K) (by simpa only [map_zero] using ha0)
  have hNfg : N.FG := (IsNoetherian.noetherian P).map (Algebra.linearMap R K)
  have hnotstable : ¬ ∀ w ∈ N,z • w ∈ N := by
    intro hstable
    have hzint : IsIntegral R z :=
      isIntegral_of_smul_mem_submodule N hN0 hNfg z hstable
    obtain ⟨r,hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hzint
    apply hprime.ne_top
    exact (fractionDenominatorIdeal_eq_top_iff R K z).mpr ⟨r,hr⟩
  push_neg at hnotstable
  obtain ⟨w,hw,hnw⟩ := hnotstable
  obtain ⟨a,ha,rfl⟩ := Submodule.mem_map.mp hw
  obtain ⟨b,hb⟩ := (mem_fractionDenominatorIdeal R K z a).mp ha
  have hbP : b ∉ P := by
    intro hbmem
    apply hnw
    apply Submodule.mem_map.mpr
    refine ⟨b,hbmem,?_⟩
    change algebraMap R K b = z * algebraMap R K a
    simpa only [mul_comm] using hb
  have hminimal : P ∈ (Ideal.span {a}).minimalPrimes := by
    refine ⟨⟨hprime,(Ideal.span_singleton_le_iff_mem P).mpr ha⟩,?_⟩
    intro Q hQ hQP
    intro t ht
    obtain ⟨c,hc⟩ := (mem_fractionDenominatorIdeal R K z t).mp ht
    have hmul : b*t = a*c := by
      apply IsFractionRing.injective R K
      simp only [map_mul]
      rw [hb,hc]
      ring
    have haQ : a ∈ Q := hQ.2 (Ideal.subset_span (Set.mem_singleton a))
    have hbt : b*t ∈ Q := by
      rw [hmul]
      exact Q.mul_mem_right c haQ
    exact (hQ.1.mem_or_mem hbt).resolve_left (fun hbQ => hbP (hQP hbQ))
  apply le_antisymm
  · exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes
      (Ideal.span {a}) P hminimal
  · simpa only [Ideal.height_bot,zero_add] using
      Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hP0)

/-- The annihilator of a rational function modulo the ring is its actual
denominator ideal. -/
theorem fraction_quotient_annihilator (z : K) :
    (⊥ : Submodule R (K ⧸ fractionRingImage R K)).colon
        {(fractionRingImage R K).mkQ z} = fractionDenominatorIdeal R K z := by
  ext r
  rw [Submodule.mem_colon_singleton,Submodule.mem_bot,← map_smul]
  change ((Submodule.Quotient.mk (r • z) : K ⧸ fractionRingImage R K) = 0) ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  rw [fractionDenominatorIdeal,Submodule.mem_colon_singleton]

/-- If a rational function is not in the ring, a height-one prime contains
every denominator that would clear it. -/
theorem exists_heightOne_containing_denominators (z : K)
    (hz : z ∉ fractionRingImage R K) :
    ∃ P : Ideal R, P.IsPrime ∧ P.height = 1 ∧
      fractionDenominatorIdeal R K z ≤ P := by
  let M := K ⧸ fractionRingImage R K
  have hzQ : (fractionRingImage R K).mkQ z ≠ 0 := by
    intro h
    apply hz
    change (Submodule.Quotient.mk z : K ⧸ fractionRingImage R K) = 0 at h
    exact (Submodule.Quotient.mk_eq_zero (fractionRingImage R K)).mp h
  obtain ⟨P,hP,hzP⟩ :=
    exists_le_isAssociatedPrime_of_isNoetherianRing R
      ((fractionRingImage R K).mkQ z) hzQ
  obtain ⟨hp,y,hy⟩ := isAssociatedPrime_iff.mp hP
  obtain ⟨w,rfl⟩ := (fractionRingImage R K).mkQ_surjective y
  rw [fraction_quotient_annihilator] at hy hzP
  refine ⟨P,hp,?_,hzP⟩
  rw [hy]
  exact fractionDenominatorIdeal_height_eq_one R K w (hy ▸ hp)

/-- The actual localization at a prime, regarded as a subalgebra of the
given fraction field. -/
def heightOneLocalRing (P : Ideal R) [P.IsPrime] : Subalgebra R K :=
  Localization.subalgebra.ofField K P.primeCompl P.primeCompl_le_nonZeroDivisors

theorem mem_heightOneLocalRing_iff (P : Ideal R) [P.IsPrime] (z : K) :
    z ∈ heightOneLocalRing R K P ↔
      ∃ s : R, s ∉ P ∧ s ∈ fractionDenominatorIdeal R K z := by
  change (∃ a s : R, ∃ hs : s ∈ P.primeCompl,
    z = algebraMap R K a * (algebraMap R K s)⁻¹) ↔ _
  constructor
  · rintro ⟨a,s,hs,rfl⟩
    refine ⟨s,hs,(mem_fractionDenominatorIdeal R K _ _).mpr ⟨a,?_⟩⟩
    have hs0 : algebraMap R K s ≠ 0 := by
      intro h
      have hsR : s = 0 := (IsFractionRing.injective R K)
        (by simpa only [map_zero] using h)
      apply hs
      change s ∈ P
      simpa only [hsR] using P.zero_mem
    field_simp
  · rintro ⟨s,hs,hsz⟩
    obtain ⟨a,ha⟩ := (mem_fractionDenominatorIdeal R K z s).mp hsz
    refine ⟨a,s,hs,?_⟩
    have hs0 : algebraMap R K s ≠ 0 := by
      intro h
      have hsR : s = 0 := (IsFractionRing.injective R K)
        (by simpa only [map_zero] using h)
      apply hs
      change s ∈ P
      simpa only [hsR] using P.zero_mem
    rw [ha]
    field_simp

/-- This subalgebra is the range of any actual localization at the same
prime, when its map to the fraction field is the compatible algebra map. -/
theorem mem_heightOneLocalRing_iff_localization_range (P : Ideal R) [P.IsPrime]
    (A : Type*) [CommRing A] [Algebra R A] [IsLocalization.AtPrime A P]
    [Algebra A K] [IsScalarTower R A K] (z : K) :
    z ∈ heightOneLocalRing R K P ↔ z ∈ (algebraMap A K).range := by
  have hmap : Localization.mapToFractionRing K P.primeCompl A
      P.primeCompl_le_nonZeroDivisors = IsScalarTower.toAlgHom R A K := by
    apply IsLocalization.algHom_ext P.primeCompl
    ext r
  change z ∈ heightOneLocalRing R K P ↔ z ∈ (IsScalarTower.toAlgHom R A K).range
  rw [← hmap]
  exact (Localization.subalgebra.mem_range_mapToFractionRing_iff_ofField
    K P.primeCompl P.primeCompl_le_nonZeroDivisors A z).symm

/-- A normal Noetherian domain is exactly the intersection of its actual
localizations at all height-one primes, inside any of its fraction fields. -/
theorem mem_fractionRingImage_iff_heightOne (z : K) :
    z ∈ fractionRingImage R K ↔
      ∀ (P : Ideal R) (hP : P.IsPrime), P.height = 1 →
        z ∈ @heightOneLocalRing R K _ _ _ _ _ P hP := by
  constructor
  · rintro ⟨r,rfl⟩ P hP _
    letI : P.IsPrime := hP
    exact (heightOneLocalRing R K P).algebraMap_mem r
  · intro h
    by_contra hz
    obtain ⟨P,hP,hheight,hden⟩ := exists_heightOne_containing_denominators R K z hz
    letI : P.IsPrime := hP
    obtain ⟨s,hs,hsz⟩ := (mem_heightOneLocalRing_iff R K P z).mp (h P hP hheight)
    exact hs (hden hsz)

end PaperVerification.ToricSchemes
end
end Source_ToricNormalHeightOne
-- END ORIGINAL PaperVerification.ToricNormalHeightOne


-- BEGIN ORIGINAL PaperVerification.ToricNormalOrders
section Source_ToricNormalOrders

-- original header: module

-- original header: public import PaperVerification.ToricNormalHeightOne
-- original header: public import PaperVerification.ToricRegularRational
-- original header: public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
-- original header: public import Mathlib.RingTheory.KrullDimension.Field
-- original header: public import Mathlib.AlgebraicGeometry.OrderOfVanishing

-- original header: @[expose] public section

/-!
# Orders detect regularity in normal local rings of dimension one

These statements use Mathlib's actual local-ring order and the actual
generic stalk of a scheme. In particular, order zero is identified with
an honest unit of the local ring, not stipulated in a divisor definition.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory TopologicalSpace

/-- A normal Noetherian local domain of dimension one is a DVR. -/
theorem discreteValuationRing_of_normal_dimensionOne (A : Type*)
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] (hdim : ringKrullDim A = 1) :
    IsDiscreteValuationRing A := by
  have hnf : ¬ IsField A := by
    intro hf
    have hzero := ringKrullDim_eq_zero_of_isField hf
    rw [hdim] at hzero
    exact one_ne_zero hzero
  letI : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.mpr hdim.le
  apply ((IsDiscreteValuationRing.TFAE A hnf).out 1 4).mpr
  refine ⟨inferInstance,IsLocalRing.maximalIdeal A,⟨?_,inferInstance⟩,?_⟩
  · exact (IsLocalRing.isField_iff_maximalIdeal_eq).not.mp hnf
  · intro P hP
    exact IsLocalRing.eq_maximalIdeal (hP.2.isMaximal_of_ne_bot hP.1)

/-- The exact unit criterion for the actual order homomorphism of a DVR. -/
theorem ordFrac_eq_one_iff_unit (A K : Type*)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] (z : K) :
    Ring.ordFrac A z = 1 ↔ ∃ u : Aˣ, algebraMap A K (u : A) = z := by
  change z ∈ MonoidHom.mker (Ring.ordFrac A) ↔ _
  rw [Ring.mker_ordFrac_eq_isUnitSubmonoid]
  change (∃ a : A, IsUnit a ∧ algebraMap A K a = z) ↔ _
  constructor
  · rintro ⟨a,⟨u,rfl⟩,ha⟩
    exact ⟨u,ha⟩
  · rintro ⟨u,hu⟩
    exact ⟨u,u.isUnit,hu⟩

/-- Nonnegative additive order is equivalent to actual regularity in a
DVR; in multiplicative notation this is the inequality `1 ≤ ordFrac`. -/
theorem one_le_ordFrac_iff_regular (A K : Type*)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (z : K) (hz : z ≠ 0) :
    1 ≤ Ring.ordFrac A z ↔ ∃ a : A, algebraMap A K a = z := by
  constructor
  · intro h
    rw [Ring.ordFrac_eq_valuation_inv] at h
    have hv0 : 0 < (IsDiscreteValuationRing.maximalIdeal A).valuation K z :=
      zero_lt_iff.mpr ((map_ne_zero _).mpr hz)
    exact IsDiscreteValuationRing.exists_lift_of_le_one ((one_le_inv₀ hv0).mp h)
  · rintro ⟨a,rfl⟩
    apply Ring.ordFrac_ge_one_of_ne_zero
    intro ha
    apply hz
    simp [ha]

section Schemes

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

theorem normal_codimensionOne_stalk_isDVR (x : X)
    [IsIntegrallyClosed (X.presheaf.stalk x)]
    (hx : Order.coheight x = 1) : IsDiscreteValuationRing (X.presheaf.stalk x) := by
  apply discreteValuationRing_of_normal_dimensionOne
  rw [ringKrullDim_stalk_eq_coheight,hx]
  rfl

/-- A nonzero rational function has order zero at a normal codimension-one
point exactly when it is the image of an actual unit of the stalk. -/
theorem rationalOrder_zero_iff_stalkUnit (x : X)
    [IsIntegrallyClosed (X.presheaf.stalk x)] (hx : Order.coheight x = 1)
    (z : X.functionField) (hz : z ≠ 0) :
    X.ord z x = 0 ↔
      ∃ u : (X.presheaf.stalk x)ˣ,
        algebraMap (X.presheaf.stalk x) X.functionField (u : X.presheaf.stalk x) = z := by
  letI := normal_codimensionOne_stalk_isDVR x hx
  rw [X.ord_eq_iff hx hz]
  change Ring.ordFrac (X.presheaf.stalk x) z = 1 ↔ _
  exact ordFrac_eq_one_iff_unit _ _ z

/-- The sign of the actual local order detects membership in the actual
local ring, under the proved normality and codimension hypotheses. -/
theorem rationalOrder_nonnegative_iff_regularAt (x : X)
    [IsIntegrallyClosed (X.presheaf.stalk x)] (hx : Order.coheight x = 1)
    (z : X.functionField) (hz : z ≠ 0) :
    0 ≤ X.ord z x ↔ z ∈ regularAtSubring X x := by
  letI := normal_codimensionOne_stalk_isDVR x hx
  rw [X.le_ord_iff hx hz]
  change 1 ≤ Ring.ordFrac (X.presheaf.stalk x) z ↔ _
  exact one_le_ordFrac_iff_regular _ _ z hz

end Schemes

end PaperVerification.ToricSchemes
end
end Source_ToricNormalOrders
-- END ORIGINAL PaperVerification.ToricNormalOrders


-- BEGIN ORIGINAL PaperVerification.ToricEtaleNormal
section Source_ToricEtaleNormal

-- original header: module

-- original header: public import Mathlib.RingTheory.Smooth.IntegralClosure
-- original header: public import Mathlib.RingTheory.Smooth.Flat
-- original header: public import Mathlib.RingTheory.Flat.TorsionFree
-- original header: public import Mathlib.RingTheory.Localization.BaseChange
-- original header: public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

-- original header: @[expose] public section

/-!
# Normality of an étale domain over a normal domain

Smooth base change commutes with integral closure. For an étale domain,
its generic fibre is a finite-dimensional domain over the fraction field,
and hence is itself a field. Its literal localization presentation then
identifies it as a fraction field of the original domain. This proves
absolute integral closedness without assuming it as an additional local
hypothesis on a smooth scheme.
-/

noncomputable section

namespace PaperVerification.ToricSchemes

open scoped TensorProduct nonZeroDivisors

variable (R S : Type*) [CommRing R] [CommRing S]
    [IsDomain R] [IsDomain S] [Algebra R S]

/-- Flatness makes the image of every nonzero base element a nonzero
element of the domain upstairs. -/
theorem genericFibre_denominators [Module.Flat R S] :
    Algebra.algebraMapSubmonoid S R⁰ ≤ S⁰ := by
  exact map_le_nonZeroDivisors_of_injective (algebraMap R S)
    (FaithfulSMul.algebraMap_injective R S) le_rfl

/-- Relative normality in the genuine tensor-product generic fibre.
Surjectivity of the proved integral-closure comparison is essential here. -/
theorem integrallyClosedIn_genericFibre [IsIntegrallyClosed R]
    [Algebra.Smooth R S] :
    IsIntegrallyClosedIn S (S ⊗[R] FractionRing R) := by
  let F := FractionRing R
  let A := S ⊗[R] F
  have hM : Algebra.algebraMapSubmonoid S R⁰ ≤ S⁰ :=
    genericFibre_denominators R S
  apply isIntegrallyClosedIn_iff.mpr
  refine ⟨IsLocalization.injective A hM,?_⟩
  intro z hz
  obtain ⟨u,hu⟩ :=
    (TensorProduct.toIntegralClosure_bijective_of_smooth
      (R := R) (S := S) (B := F)).2 ⟨z,hz⟩
  have hφ : ∀ u : S ⊗[R] integralClosure R F,
      ∃ s : S, algebraMap S A s =
        ((TensorProduct.toIntegralClosure R S F) u : A) := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => exact ⟨0,by simp⟩
    | add u v hu hv =>
        obtain ⟨s,hs⟩ := hu
        obtain ⟨t,ht⟩ := hv
        refine ⟨s+t,?_⟩
        simpa only [map_add,Subalgebra.coe_add,hs,ht]
    | tmul s c =>
        obtain ⟨r,hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral
          (R := R) (K := F) c.2
        refine ⟨s * algebraMap R S r,?_⟩
        simp only [TensorProduct.toIntegralClosure,AlgHom.coe_codRestrict,
          Algebra.TensorProduct.map_tmul,AlgHom.id_apply,
          Algebra.TensorProduct.algebraMap_apply,Algebra.algebraMap_self,
          RingHom.id_apply]
        change (s * algebraMap R S r) ⊗ₜ[R] (1 : F) = s ⊗ₜ[R] (c : F)
        rw [← hr]
        calc
          (s * algebraMap R S r) ⊗ₜ[R] (1 : F) = (r • s) ⊗ₜ[R] (1 : F) := by
            rw [Algebra.smul_def,mul_comm]
          _ = s ⊗ₜ[R] (r • (1 : F)) := TensorProduct.smul_tmul r s (1 : F)
          _ = s ⊗ₜ[R] algebraMap R F r := by rw [Algebra.smul_def,mul_one]
  obtain ⟨s,hs⟩ := hφ u
  exact ⟨s,hs.trans (congrArg Subtype.val hu)⟩

/-- A domain that is étale over an integrally closed domain is integrally
closed. All normality of the upstairs ring is a conclusion. -/
theorem isIntegrallyClosed_of_etale [IsIntegrallyClosed R]
    [Algebra.Etale R S] : IsIntegrallyClosed S := by
  let F := FractionRing R
  let A := F ⊗[R] S
  letI : Algebra S A := Algebra.TensorProduct.rightAlgebra
  have hM : Algebra.algebraMapSubmonoid S R⁰ ≤ S⁰ :=
    genericFibre_denominators R S
  letI : IsLocalization (Algebra.algebraMapSubmonoid S R⁰) A :=
    IsLocalization.tensorRight (R := R) (S := S) F R⁰
  letI : IsDomain A := IsLocalization.isDomain_of_le_nonZeroDivisors A hM
  letI : Module.Finite F A := Algebra.FormallyUnramified.finite_of_free F A
  have hfield : IsField A :=
    isField_of_isIntegral_of_isField' (R := F) (S := A) (Field.toIsField F)
  letI : Field A := hfield.toField
  letI : FaithfulSMul S A := (faithfulSMul_iff_algebraMap_injective S A).mpr
    (IsLocalization.injective A hM)
  letI : IsFractionRing S A := by
    apply IsFractionRing.of_field S A
    intro z
    obtain ⟨s,m,hm⟩ := IsLocalization.exists_mk'_eq
      (Algebra.algebraMapSubmonoid S R⁰) z
    refine ⟨s,m,?_⟩
    rw [← hm]
    exact (eq_div_iff (IsLocalization.map_units A m).ne_zero).mpr
      (IsLocalization.mk'_spec A s m)
  let e : S ⊗[R] F ≃ₐ[S] A := Algebra.TensorProduct.commRight R S F
  have hnormal : IsIntegrallyClosedIn S A :=
    e.isIntegrallyClosedIn.mp (integrallyClosedIn_genericFibre R S)
  exact (isIntegrallyClosed_iff_isIntegrallyClosedIn A).mpr hnormal

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.isIntegrallyClosed_of_etale
end
end Source_ToricEtaleNormal
-- END ORIGINAL PaperVerification.ToricEtaleNormal


-- BEGIN ORIGINAL PaperVerification.ToricSmoothNormal
section Source_ToricSmoothNormal

-- original header: module

-- original header: public import PaperVerification.ToricEtaleNormal
-- original header: public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
-- original header: public import Mathlib.RingTheory.Localization.LocalizationLocalization
-- original header: public import Mathlib.RingTheory.Polynomial.UniqueFactorization
-- original header: public import Mathlib.RingTheory.Polynomial.RationalRoot
-- original header: public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

-- original header: @[expose] public section

/-!
# Integral closedness derived from ordinary smoothness

The local presentation theorem for smooth algebras gives standard étale
charts over polynomial rings. The preceding étale result proves integral
closedness on these charts. Localization and the actual local criterion
then prove it for the original algebra. On an integral scheme smooth over
a field, this applies to every affine coordinate ring and every actual
stalk. Normality is consequently a conclusion, not an additional input.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory
open scoped nonZeroDivisors

variable (k S : Type*) [Field k] [CommRing S] [IsDomain S]
    [Algebra k S] [Algebra.Smooth k S]

include k

/-- Every prime has a genuine principal neighborhood with integrally
closed coordinate ring. The local algebra structure over a polynomial
ring is supplied by the smooth local presentation theorem. -/
theorem exists_integrallyClosed_away_of_smooth (p : Ideal S) [p.IsPrime] :
    ∃ f : S, f ∉ p ∧ IsIntegrallyClosed (Localization.Away f) := by
  obtain ⟨f,hfp,n,ha,ht,he⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := k) (p := p)
  letI : Algebra (MvPolynomial (Fin n) k) (Localization.Away f) := ha
  letI : IsScalarTower k (MvPolynomial (Fin n) k) (Localization.Away f) := ht
  letI : Algebra.IsStandardEtale (MvPolynomial (Fin n) k) (Localization.Away f) := he
  have hf : f ≠ 0 := fun h => hfp (h ▸ p.zero_mem)
  letI : IsDomain (Localization.Away f) := Localization.Away.isDomain hf
  exact ⟨f,hfp,isIntegrallyClosed_of_etale
    (MvPolynomial (Fin n) k) (Localization.Away f)⟩

/-- Normality of a smooth affine integral algebra, with no normality or
regularity hypothesis on that algebra. -/
theorem isIntegrallyClosed_of_smooth_field : IsIntegrallyClosed S := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro p hp0 hp
  obtain ⟨f,hfp,hfNormal⟩ := exists_integrallyClosed_away_of_smooth k S p
  have hf : f ≠ 0 := fun h => hfp (h ▸ p.zero_mem)
  let A := Localization.Away f
  letI : IsDomain A := Localization.Away.isDomain hf
  letI : IsIntegrallyClosed A := hfNormal
  have hdis : Disjoint (Submonoid.powers f : Set S) (p : Set S) := by
    exact (Ideal.disjoint_powers_iff_notMem_of_isPrime (I := p) f).mpr hfp
  let q : Ideal A := p.map (algebraMap S A)
  letI : q.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) A p
      inferInstance hdis
  have hq : q.comap (algebraMap S A) = p :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers f) A
      inferInstance hdis
  letI : IsIntegrallyClosed (Localization.AtPrime q) :=
    isIntegrallyClosed_of_isLocalization (Localization.AtPrime q)
      q.primeCompl q.primeCompl_le_nonZeroDivisors
  let e := IsLocalization.localizationLocalizationAtPrimeIsoLocalization
    (Submonoid.powers f) q
  have hn : IsIntegrallyClosed (Localization.AtPrime (q.comap (algebraMap S A))) :=
    (inferInstance : IsIntegrallyClosed (Localization.AtPrime q)).of_equiv
      e.symm.toRingEquiv
  let p' : PrimeSpectrum S := ⟨q.comap (algebraMap S A),inferInstance⟩
  let p₀ : PrimeSpectrum S := ⟨p,inferInstance⟩
  have hpEq : p'=p₀ := PrimeSpectrum.ext hq
  exact (congrArg
    (fun z : PrimeSpectrum S => IsIntegrallyClosed (Localization.AtPrime z.asIdeal))
    hpEq).mp hn

omit k

section Schemes

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [Smooth f]

include f

/-- The actual ring of functions on each nonempty affine open of an
integral scheme smooth over a field is integrally closed. -/
theorem smooth_affineOpen_isIntegrallyClosed (U : X.Opens)
    (hU : IsAffineOpen U) [Nonempty U] : IsIntegrallyClosed Γ(X,U) := by
  let R := Γ(Spec (.of k),⊤)
  let e : R ≃+* k := (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv
  letI : Field R := (e.isField (Field.toIsField k)).toField
  have hpre : U ≤ f ⁻¹ᵁ (⊤ : (Spec (.of k)).Opens) := by simp
  letI : Algebra R Γ(X,U) := (f.appLE ⊤ U hpre).hom.toAlgebra
  letI : Algebra.Smooth R Γ(X,U) :=
    (f.smooth_appLE (isAffineOpen_top _) hU hpre).toAlgebra
  exact isIntegrallyClosed_of_smooth_field R Γ(X,U)

/-- Integral closedness of each literal local ring follows from an actual
affine neighborhood and the stalk localization theorem. -/
theorem smooth_stalk_isIntegrallyClosed (x : X) :
    IsIntegrallyClosed (X.presheaf.stalk x) := by
  obtain ⟨_,⟨U,hU,rfl⟩,hxU,-⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ x) isOpen_univ
  letI : Nonempty U := ⟨⟨x,hxU⟩⟩
  letI : IsIntegrallyClosed Γ(X,U) := smooth_affineOpen_isIntegrallyClosed f U hU
  letI : Algebra Γ(X,U) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x,hxU⟩
  let p := hU.primeIdealOf ⟨x,hxU⟩
  letI : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
    hU.isLocalization_stalk ⟨x,hxU⟩
  exact isIntegrallyClosed_of_isLocalization (X.presheaf.stalk x)
    p.asIdeal.primeCompl p.asIdeal.primeCompl_le_nonZeroDivisors

end Schemes

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.isIntegrallyClosed_of_smooth_field
#print axioms PaperVerification.ToricSchemes.smooth_stalk_isIntegrallyClosed
end
end Source_ToricSmoothNormal
-- END ORIGINAL PaperVerification.ToricSmoothNormal


-- BEGIN ORIGINAL PaperVerification.ToricNormalCartier
section Source_ToricNormalCartier

-- original header: module

-- original header: public import PaperVerification.ToricNormalOrders
-- original header: public import PaperVerification.ToricSmoothNormal
-- original header: public import PaperVerification.ToricCartierOrders
-- original header: public import PaperVerification.ToricCartierRangeEquality

-- original header: @[expose] public section

/-!
# Cartier divisors are detected by their genuine Weil orders on smooth schemes

Normality is derived from ordinary smoothness over the ground field. The
height-one intersection theorem is applied to actual affine coordinate
rings and their actual stalk localizations. Thus the resulting injectivity
statement concerns actual invertible fractional sheaves on the scheme.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace PaperVerification.ToricSchemes

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- On a normal affine open, regularity is detected at the actual points
of codimension one in that open. -/
theorem normalAffine_regular_iff_codimensionOne (U : X.Opens)
    (hU : IsAffineOpen U) [Nonempty U] [IsIntegrallyClosed Γ(X,U)]
    (z : X.functionField) :
    z ∈ (X.germToFunctionField U).hom.range ↔
      ∀ x∈U, Order.coheight x = 1 → z∈regularAtSubring X x := by
  let R := Γ(X,U)
  letI : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨U,hU⟩
  letI : IsFractionRing R X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  constructor
  · rintro ⟨s,rfl⟩ x hx _
    exact regular_germ_mem_regularAt X U s x hx
  · intro h
    change z ∈ fractionRingImage R X.functionField
    apply (mem_fractionRingImage_iff_heightOne R X.functionField z).mpr
    intro P hP hheight
    letI : P.IsPrime := hP
    let p : Spec (.of R) := ⟨P,hP⟩
    let x : X := hU.fromSpec p
    have hxU : x∈U := by
      change x ∈ (U : Set X)
      rw [← hU.range_fromSpec]
      exact ⟨p,rfl⟩
    have hxheight : Order.coheight x = 1 := by
      calc
        Order.coheight x = Order.coheight p :=
          coheight_eq_of_isOpenImmersion hU.fromSpec
        _ = P.height := (idealHeight_eq_coheight (.of R) p).symm
        _ = 1 := hheight
    letI : Algebra R (X.presheaf.stalk x) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x,hxU⟩
    letI : IsLocalization.AtPrime (X.presheaf.stalk x) P :=
      hU.isLocalization_stalk' p hxU
    letI : IsScalarTower R (X.presheaf.stalk x) X.functionField :=
      functionField_isScalarTower X U ⟨x,hxU⟩
    exact (mem_heightOneLocalRing_iff_localization_range R X.functionField
      P (X.presheaf.stalk x) z).mpr (h x hxU hxheight)

variable {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) [Smooth f]

include f

/-- A nonzero rational function on a smooth integral scheme is regular on
an arbitrary open exactly when its orders are nonnegative there. -/
theorem smooth_regular_range_iff_orders (U : X.Opens) [Nonempty U]
    (z : X.functionField) (hz : z ≠ 0) :
    z ∈ (X.germToFunctionField U).hom.range ↔
      ∀ x∈U, 0 ≤ X.ord z x := by
  constructor
  · rintro ⟨s,rfl⟩ x hx
    by_cases hcodim : Order.coheight x=1
    · letI : IsIntegrallyClosed (X.presheaf.stalk x) :=
        smooth_stalk_isIntegrallyClosed f x
      exact (rationalOrder_nonnegative_iff_regularAt x hcodim _ hz).mpr
        (regular_germ_mem_regularAt X U s x hx)
    · simp [Scheme.ord_eq_zero_of_coheight_neq_one hcodim]
  · intro h
    apply (mem_regular_range_iff_stalkwise X U z).mpr
    intro x hx
    obtain ⟨V,hV,hxV,hVU⟩ := exists_isAffineOpen_mem_and_subset (x := x) hx
    letI : Nonempty V := ⟨⟨x,hxV⟩⟩
    letI : IsIntegrallyClosed Γ(X,V) :=
      smooth_affineOpen_isIntegrallyClosed f V hV
    have hzV : z∈(X.germToFunctionField V).hom.range := by
      apply (normalAffine_regular_iff_codimensionOne V hV z).mpr
      intro y hy hcodim
      letI : IsIntegrallyClosed (X.presheaf.stalk y) :=
        smooth_stalk_isIntegrallyClosed f y
      exact (rationalOrder_nonnegative_iff_regularAt y hcodim z hz).mp
        (h y (hVU hy))
    obtain ⟨s,hs⟩ := hzV
    rw [← hs]
    exact regular_germ_mem_regularAt X V s x hxV

/-- Vanishing of every genuine Weil order is equivalent to a genuine
regular unit on the open, including nonaffine opens. -/
theorem smooth_regular_unit_iff_orders_zero (U : X.Opens) [Nonempty U]
    (z : X.functionField) (hz : z ≠ 0) :
    (∃ a : Γ(X,U)ˣ,X.germToFunctionField U (a : Γ(X,U))=z) ↔
      ∀ x∈U,X.ord z x=0 := by
  constructor
  · rintro ⟨a,rfl⟩ x hx
    exact X.ord_of_isUnit a.isUnit hx
  · intro h
    have hpos : z∈(X.germToFunctionField U).hom.range :=
      (smooth_regular_range_iff_orders f U z hz).mpr
        (fun x hx => (h x hx).ge)
    have hneg : z⁻¹∈(X.germToFunctionField U).hom.range := by
      apply (smooth_regular_range_iff_orders f U z⁻¹ (inv_ne_zero hz)).mpr
      intro x hx
      rw [rationalOrder_inv hz,h x hx,neg_zero]
    obtain ⟨a,ha⟩ := hpos
    obtain ⟨b,hb⟩ := hneg
    have hab : a*b=1 := by
      apply X.germToFunctionField_injective U
      rw [map_mul,map_one,ha,hb,mul_inv_cancel₀ hz]
    exact ⟨⟨a,b,hab,by simpa only [mul_comm] using hab⟩,ha⟩

namespace CartierData

/-- Equality of the actual Weil coefficients forces equality of Cartier
divisors as embedded fractional sheaves. Normality is a theorem here,
derived from smoothness, not an additional input about the scheme. -/
theorem equivalent_of_weilCoefficient_eq (D E : CartierData X)
    (hcoeff : D.weilCoefficient = E.weilCoefficient) : D.Equivalent E := by
  let C := D.localCocycle
  let B := E.localCocycle
  have hratios : C.GeneratorRatioRegular B ∧ B.GeneratorRatioRegular C := by
    have hunit : ∀ (i : C.index) (j : B.index)
        (V : X.Opens) [Nonempty V], V≤C.openSet i⊓B.openSet j →
        ∃ a : Γ(X,V)ˣ, X.germToFunctionField V (a : Γ(X,V)) =
          (C.generator i : X.functionField)/(B.generator j : X.functionField) := by
      intro i j V hV hsub
      letI := hV
      letI : Nonempty (invertibleOpen D.locallyFree i) :=
        ⟨⟨i,mem_invertibleOpen D.locallyFree i⟩⟩
      letI : Nonempty (invertibleOpen E.locallyFree j) :=
        ⟨⟨j,mem_invertibleOpen E.locallyFree j⟩⟩
      apply (smooth_regular_unit_iff_orders_zero f V _
        (div_ne_zero (C.generator i).ne_zero (B.generator j).ne_zero)).mpr
      intro x hx
      rw [rationalOrder_div (C.generator i).ne_zero (B.generator j).ne_zero]
      have heq := congrFun hcoeff x
      rw [D.weilCoefficient_eq_neg_frameOrder
          (invertibleFrame D.locallyFree i) (hsub hx).1,
        E.weilCoefficient_eq_neg_frameOrder
          (invertibleFrame E.locallyFree j) (hsub hx).2] at heq
      change -X.ord (C.generator i : X.functionField) x =
        -X.ord (B.generator j : X.functionField) x at heq
      omega
    constructor
    · intro i j x hxi hxj
      let V := C.openSet i⊓B.openSet j
      letI : Nonempty V := ⟨⟨x,hxi,hxj⟩⟩
      obtain ⟨a,ha⟩ := hunit i j V le_rfl
      rw [← ha]
      exact regular_germ_mem_regularAt X V a x ⟨hxi,hxj⟩
    · intro j i x hxj hxi
      let V := C.openSet i⊓B.openSet j
      letI : Nonempty V := ⟨⟨x,hxi,hxj⟩⟩
      obtain ⟨a,ha⟩ := hunit i j V le_rfl
      have hinv : X.germToFunctionField V ((a⁻¹ : Γ(X,V)ˣ) : Γ(X,V)) =
          (B.generator j : X.functionField)/(C.generator i : X.functionField) := by
        have hmul := congrArg (X.germToFunctionField V) a.val_inv
        rw [map_mul,map_one,ha] at hmul
        change (C.generator i : X.functionField) / (B.generator j : X.functionField) *
          X.germToFunctionField V ((a⁻¹ : Γ(X,V)ˣ) : Γ(X,V)) = 1 at hmul
        apply mul_left_cancel₀
          (div_ne_zero (C.generator i).ne_zero (B.generator j).ne_zero)
        rw [hmul]
        field_simp
      rw [← hinv]
      exact regular_germ_mem_regularAt X V (a⁻¹ : Γ(X,V)ˣ) x ⟨hxi,hxj⟩
  exact D.equivalent_trans B.toCartierData E
    (D.equivalent_trans C.toCartierData B.toCartierData
      D.equivalent_localCocycle
      (C.equivalent_of_generatorRatios B hratios.1 hratios.2))
    (E.equivalent_symm B.toCartierData E.equivalent_localCocycle)

end CartierData

end PaperVerification.ToricSchemes
end
end Source_ToricNormalCartier
-- END ORIGINAL PaperVerification.ToricNormalCartier


-- BEGIN ORIGINAL PaperVerification.ToricOrderTransport
section Source_ToricOrderTransport

-- original header: module

-- original header: public import PaperVerification.ToricDominantFunctionField
-- original header: public import Mathlib.AlgebraicGeometry.OrderOfVanishing
-- original header: public import Mathlib.RingTheory.Ideal.Maps

-- original header: @[expose] public section

/-!
# Transport of actual orders through isomorphisms

Ring order is transported using the order isomorphism of the actual ideal
lattices and the quotient-length formula. Its fraction-field extension is
then transported by writing an arbitrary fraction as a quotient. The
scheme statement uses the genuine maps on local and generic stalks.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory
open scoped nonZeroDivisors

section Rings

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The module length defining order is preserved by the actual ring
isomorphism, including the infinite-length case. -/
theorem ord_ringEquiv (e : R ≃+* S) (r : R) :
    Ring.ord S (e r) = Ring.ord R r := by
  rw [Ring.ord,Ring.ord,Module.length_quotient,Module.length_quotient]
  simpa only [RingEquiv.idealComapOrderIso_symm_apply,
    Ideal.map_span,Set.image_singleton] using
    Order.coheight_orderIso e.idealComapOrderIso.symm (Ideal.span {r})

variable [IsDomain R] [IsDomain S]

theorem ordMonoidWithZeroHom_ringEquiv (e : R ≃+* S) (r : R) :
    Ring.ordMonoidWithZeroHom S (e r) = Ring.ordMonoidWithZeroHom R r := by
  by_cases hr : r=0
  · simp [hr]
  have her : e r≠0 := (map_ne_zero_iff e e.injective).mpr hr
  rw [Ring.ordMonoidWithZeroHom_eq_ord
      (mem_nonZeroDivisors_iff_ne_zero.mpr her),
    Ring.ordMonoidWithZeroHom_eq_ord
      (mem_nonZeroDivisors_iff_ne_zero.mpr hr),ord_ringEquiv]

variable [IsNoetherianRing R] [IsNoetherianRing S]
    [Ring.KrullDimLE 1 R] [Ring.KrullDimLE 1 S]
    {K L : Type*} [Field K] [Field L]
    [Algebra R K] [Algebra S L] [IsFractionRing R K] [IsFractionRing S L]

/-- Functoriality of the existing fraction-field order under compatible
isomorphisms of the local ring and its fraction field. -/
theorem ordFrac_ringEquiv (e : R ≃+* S) (E : K ≃+* L)
    (hE : ∀ r : R,E (algebraMap R K r)=algebraMap S L (e r)) (z : K) :
    Ring.ordFrac S (E z) = Ring.ordFrac R z := by
  obtain ⟨a,b,hb,rfl⟩ := IsFractionRing.div_surjective R z
  by_cases ha : a=0
  · simp [ha]
  have hb' : b≠0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hea : e a≠0 := (map_ne_zero_iff e e.injective).mpr ha
  have heb : e b≠0 := (map_ne_zero_iff e e.injective).mpr hb'
  rw [map_div₀,hE,hE,map_div₀,map_div₀,
    Ring.ordFrac_eq_ord S hea,Ring.ordFrac_eq_ord S heb,
    Ring.ordFrac_eq_ord R ha,Ring.ordFrac_eq_ord R hb',
    ordMonoidWithZeroHom_ringEquiv,ordMonoidWithZeroHom_ringEquiv]

end Rings

section Schemes

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

/-- Restriction to an actual open subscheme preserves all local orders.
The equality includes the zero rational function and all codimensions. -/
theorem schemeOrder_openImmersion (j : Y ⟶ X) [IsOpenImmersion j]
    [IsDominant j] (y : Y) (z : X.functionField) :
    Y.ord (dominantFunctionFieldMap j z) y = X.ord z (j y) := by
  have hh : Order.coheight (j y)=Order.coheight y :=
    coheight_eq_of_isOpenImmersion j
  by_cases hy : Order.coheight y=1
  · have hx : Order.coheight (j y)=1 := hh.trans hy
    letI : Ring.KrullDimLE 1 (Y.presheaf.stalk y) :=
      krullDimLE_of_coheight_le hy.le
    letI : Ring.KrullDimLE 1 (X.presheaf.stalk (j y)) :=
      krullDimLE_of_coheight_le hx.le
    let e := (asIso (j.stalkMap y)).commRingCatIsoToRingEquiv
    let E := openImmersionFunctionFieldEquiv j
    have hE (a : X.presheaf.stalk (j y)) :
        E (algebraMap (X.presheaf.stalk (j y)) X.functionField a) =
          algebraMap (Y.presheaf.stalk y) Y.functionField (e a) := by
      change dominantFunctionFieldMap j
          (algebraMap (X.presheaf.stalk (j y)) X.functionField a) = _
      exact dominantFunctionFieldMap_stalk j y a
    have ho : Y.ordHom y hy (dominantFunctionFieldMap j z) =
        X.ordHom (j y) hx z :=
      ordFrac_ringEquiv e E hE z
    rw [Y.ord_eq_ordHom_of_coheight_eq_one hy,
      X.ord_eq_ordHom_of_coheight_eq_one hx,ho]
  · have hx : Order.coheight (j y)≠1 := fun h=>hy (hh.symm.trans h)
    rw [Scheme.ord_eq_zero_of_coheight_neq_one hy,
      Scheme.ord_eq_zero_of_coheight_neq_one hx]

/-- In particular, a scheme isomorphism preserves actual orders of
vanishing under its genuine pullback on rational functions. -/
theorem schemeOrder_iso (e : Y ≅ X) (y : Y) (z : X.functionField) :
    Y.ord (dominantFunctionFieldMap e.hom z) y = X.ord z (e.hom y) :=
  schemeOrder_openImmersion e.hom y z

end Schemes

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.ordFrac_ringEquiv
#print axioms PaperVerification.ToricSchemes.schemeOrder_iso
end
end Source_ToricOrderTransport
-- END ORIGINAL PaperVerification.ToricOrderTransport


-- BEGIN ORIGINAL PaperVerification.ToricCartierBoundaryInvariance
section Source_ToricCartierBoundaryInvariance

-- original header: module

-- original header: public import PaperVerification.ToricDominantCartierPullback
-- original header: public import PaperVerification.ToricNormalCartier
-- original header: public import PaperVerification.ToricOrderTransport
-- original header: public import PaperVerification.ToricBoundaryFixedPoints
-- original header: public import PaperVerification.ToricCartierChartValues

-- original header: @[expose] public section

/-!
# Genuine Cartier invariance from fixed boundary components

This file retains the actual rational embedding of each invertible sheaf.
The normalized representative is proved to have unit local frames on the
dense torus. Actual generic-stalk pullback preserves this property. On a
smooth scheme, an automorphism fixing the codimension-one boundary points
therefore preserves the Cartier divisor, by the proved Cartier-to-Weil
injectivity theorem.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

universe u

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace PaperVerification.ToricSchemes

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- Both a rational function and its inverse lie in the actual local ring. -/
def IsRegularUnitAt (X : Scheme.{u}) [IsIntegral X] (x : X) (z : X.functionField) : Prop :=
  z∈regularAtSubring X x ∧ z⁻¹∈regularAtSubring X x

theorem isRegularUnitAt_pullback (f : Y ⟶ X) [IsDominant f]
    (y : Y) (z : X.functionField) (h : IsRegularUnitAt X (f y) z) :
    IsRegularUnitAt Y y (dominantFunctionFieldMap f z) := by
  refine ⟨dominantFunctionFieldMap_mem_regularAt f y z h.1,?_⟩
  simpa only [map_inv₀] using dominantFunctionFieldMap_mem_regularAt f y z⁻¹ h.2

theorem rationalOrder_zero_of_isRegularUnitAt [IsLocallyNoetherian X]
    (x : X) (z : X.functionField) (hz : z≠0) (h : IsRegularUnitAt X x z) :
    X.ord z x=0 := by
  obtain ⟨a,ha⟩ := h.1
  obtain ⟨b,hb⟩ := h.2
  have hab : a*b=1 := by
    apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
    rw [map_mul,map_one,ha,hb,mul_inv_cancel₀ hz]
  let aU : (X.presheaf.stalk x)ˣ := ⟨a,b,hab,by simpa only [mul_comm] using hab⟩
  by_cases hx : Order.coheight x=1
  · letI : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
    apply (X.ord_eq_iff hx hz).mpr
    change Ring.ordFrac (X.presheaf.stalk x) z=1
    rw [← ha]
    exact Ring.ordFrac_of_isUnit aU.isUnit
  · exact Scheme.ord_eq_zero_of_coheight_neq_one hx z

namespace RationalCartierCocycle

variable (C : RationalCartierCocycle X)

def HasUnitFramesOn (U : X.Opens) : Prop :=
  ∀ i (x : X),x∈U→x∈C.openSet i→IsRegularUnitAt X x (C.generator i : X.functionField)

theorem HasUnitFramesOn.pow {C : RationalCartierCocycle X}
    {U : X.Opens} (h : C.HasUnitFramesOn U) (n : ℕ) :
    (C.pow n).HasUnitFramesOn U := by
  intro i x hx hi
  change IsRegularUnitAt X x ((C.generator i : X.functionField)^n)
  obtain ⟨hpos,hneg⟩ := h i x hx hi
  refine ⟨?_,?_⟩
  · exact (regularAtSubring X x).pow_mem hpos n
  · simpa only [inv_pow] using (regularAtSubring X x).pow_mem hneg n

/-- Unit frames are independent of the actual Cartier presentation. -/
theorem HasUnitFramesOn.of_equivalent {C : RationalCartierCocycle X} {U : X.Opens}
    (h : C.HasUnitFramesOn U) (D : RationalCartierCocycle X)
    (he : C.toCartierData.Equivalent D.toCartierData) : D.HasUnitFramesOn U := by
  intro j x hx hj
  obtain ⟨i,hi⟩ := C.covers x
  have hC := h i x hx hi
  have hDC := D.generatorRatios_of_equivalent C
    (C.toCartierData.equivalent_symm D.toCartierData he) j i x hj hi
  have hCD := C.generatorRatios_of_equivalent D he i j x hi hj
  refine ⟨?_,?_⟩
  · have hh := (regularAtSubring X x).mul_mem hDC hC.1
    simpa only [div_mul_cancel₀ _ (C.generator i).ne_zero] using hh
  · have hh := (regularAtSubring X x).mul_mem hC.2 hCD
    have heq : (C.generator i : X.functionField)⁻¹ *
        ((C.generator i : X.functionField)/(D.generator j : X.functionField)) =
        (D.generator j : X.functionField)⁻¹ := by
      field_simp [Units.ne_zero]
    simpa only [heq] using hh

theorem hasUnitFramesOn_pullback (U : X.Opens) (h : C.HasUnitFramesOn U)
    (f : Y ⟶ X) [IsDominant f] :
    (C.dominantPullback f).HasUnitFramesOn (f ⁻¹ᵁ U) := by
  intro i y hyU hyi
  exact isRegularUnitAt_pullback f y _ (h i (f y) hyU hyi)

theorem weilCoefficient_eq_neg_generator [IsLocallyNoetherian X]
    (i : C.index) (x : X) (hx : x∈C.openSet i) :
    C.toCartierData.weilCoefficient x = -X.ord (C.generator i : X.functionField) x := by
  letI : Nonempty (C.openSet i) := ⟨⟨x,hx⟩⟩
  rw [C.toCartierData.weilCoefficient_eq_neg_frameOrder (C.localFrame i) hx]
  change -X.ord (C.toCartierData.sectionValue (C.openSet i)
    (ModuleFrame.generator (C.localFrame i) (C.openSet i) le_rfl)) x = _
  rw [localFrame_generator_value]

theorem weilCoefficient_zero_of_unitFrames [IsLocallyNoetherian X]
    (U : X.Opens) (h : C.HasUnitFramesOn U) (x : X) (hx : x∈U) :
    C.toCartierData.weilCoefficient x=0 := by
  obtain ⟨i,hi⟩ := C.covers x
  rw [C.weilCoefficient_eq_neg_generator i x hi,
    rationalOrder_zero_of_isRegularUnitAt x _ (C.generator i).ne_zero (h i x hx hi),neg_zero]

theorem weilCoefficient_pullback_iso [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (e : Y≅X) (y : Y) :
    (C.dominantPullback e.hom).toCartierData.weilCoefficient y =
      C.toCartierData.weilCoefficient (e.hom y) := by
  obtain ⟨i,hi⟩ := C.covers (e.hom y)
  rw [(C.dominantPullback e.hom).weilCoefficient_eq_neg_generator i y hi,
    C.weilCoefficient_eq_neg_generator i (e.hom y) hi,
    dominantPullback_generator,schemeOrder_iso]

end RationalCartierCocycle

namespace CartierData

variable (D : CartierData X)

theorem hasUnitFramesOn_nsmul {U : X.Opens}
    (h : D.localCocycle.HasUnitFramesOn U) (n : ℕ) :
    (D.nsmul n).localCocycle.HasUnitFramesOn U :=
  (h.pow n).of_equivalent (D.nsmul n).localCocycle
    (D.nsmul n).equivalent_localCocycle

theorem weilCoefficient_dominantPullback_iso
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (e : Y≅X) (y : Y) :
    (D.dominantPullback e.hom).weilCoefficient y = D.weilCoefficient (e.hom y) := by
  rw [dominantPullback,D.localCocycle.weilCoefficient_pullback_iso]
  exact (congrFun (D.equivalent_weilCoefficient D.localCocycle.toCartierData
    D.equivalent_localCocycle) (e.hom y)).symm

/-- An actual automorphism fixing the codimension-one support fixes the
Cartier divisor itself. No linear-equivalence relaxation occurs here. -/
theorem equivalent_pullback_of_boundary_fixed
    [IsLocallyNoetherian X] {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [Smooth f] (e : X≅X)
    (B : Set X) (hB : e.hom ⁻¹' B=B)
    (hfixed : ∀ x∈B,Order.coheight x=1→e.hom x=x)
    (hzero : ∀ x∉B,D.weilCoefficient x=0) :
    (D.dominantPullback e.hom).Equivalent D := by
  apply equivalent_of_weilCoefficient_eq f
  funext x
  by_cases hcodim : Order.coheight x=1
  · rw [D.weilCoefficient_dominantPullback_iso e]
    by_cases hx : x∈B
    · rw [hfixed x hx hcodim]
    · have hex : e.hom x∉B := by
        intro h
        apply hx
        change x∈e.hom ⁻¹' B at h
        rwa [hB] at h
      rw [hzero _ hex,hzero _ hx]
  · rw [weilCoefficient_eq_zero_of_coheight_ne_one _ hcodim,
      weilCoefficient_eq_zero_of_coheight_ne_one _ hcodim]

end CartierData

namespace RationalCartierCocycle

theorem equivalent_pullback_of_boundary_fixed
    [IsLocallyNoetherian X] {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [Smooth f] (C : RationalCartierCocycle X)
    (e : X≅X) (B : Set X) (hB : e.hom ⁻¹' B=B)
    (hfixed : ∀ x∈B,Order.coheight x=1→e.hom x=x)
    (hzero : ∀ x∉B,C.toCartierData.weilCoefficient x=0) :
    (C.dominantPullback e.hom).toCartierData.Equivalent C.toCartierData := by
  apply CartierData.equivalent_of_weilCoefficient_eq f
  funext x
  by_cases hcodim : Order.coheight x=1
  · rw [C.weilCoefficient_pullback_iso e]
    by_cases hx : x∈B
    · rw [hfixed x hx hcodim]
    · have hex : e.hom x∉B := by
        intro h
        apply hx
        change x∈e.hom ⁻¹' B at h
        rwa [hB] at h
      rw [hzero _ hex,hzero _ hx]
  · rw [CartierData.weilCoefficient_eq_zero_of_coheight_ne_one _ hcodim,
      CartierData.weilCoefficient_eq_zero_of_coheight_ne_one _ hcodim]

end RationalCartierCocycle

section NormalizedTorus

variable (k : Type u) [Field k] (n : ℕ) (X : Scheme.{u}) [IsIntegral X]
    (j : splitTorus k (Fin n→ℤ) ⟶ X) [IsOpenImmersion j]
    (D : CartierData X)

theorem torusNormalizedCartier_chartGenerator :
    (torusNormalizedCartier k n X j D).chartFrameRationalGenerator j
      (torusNormalizedCartierSheafIso k n X j D)=1 := by
  rw [CartierData.chartFrameRationalGenerator,torusNormalizedCartier_value]
  have h : (torusNormalizedCartierSheafIso k n X j D).hom.app ⊤
      ((torusNormalizedCartierSheafIso k n X j D).inv.app ⊤
        (1 : Γ(splitTorus k (Fin n→ℤ),⊤))) =
      (1 : Γ(splitTorus k (Fin n→ℤ),⊤)) := by
    simpa only [Scheme.Modules.Hom.comp_app,Scheme.Modules.Hom.id_app,
      ConcreteCategory.comp_apply,ConcreteCategory.id_apply] using
      congrArg (fun φ=>φ.app ⊤ (1 : Γ(splitTorus k (Fin n→ℤ),⊤)))
        (torusNormalizedCartierSheafIso k n X j D).inv_hom_id
  exact (congrArg (openImmersionRegularToFunctionField j ⊤) h).trans (map_one _)

theorem torusNormalizedCartier_range_on_open (V : X.Opens) [Nonempty V]
    (hV : V≤j.opensRange) :
    ((torusNormalizedCartier k n X j D).sectionValueRange V : Set X.functionField)=
      Set.range (X.germToFunctionField V) := by
  ext z
  change z ∈ (torusNormalizedCartier k n X j D).sectionValueRange V ↔
    z ∈ Set.range (X.germToFunctionField V)
  rw [(torusNormalizedCartier k n X j D).mem_sectionValueRange_iff_chartFrame
    j (torusNormalizedCartierSheafIso k n X j D) V hV z,
    torusNormalizedCartier_chartGenerator]
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a,(mul_one (X.germToFunctionField V a)).symm.trans ha⟩
  · rintro ⟨a,ha⟩
    exact ⟨a,(mul_one (X.germToFunctionField V a)).trans ha⟩

/-- Every actual local rational frame of the normalized divisor is a
regular unit at every point of the torus open. -/
theorem torusNormalizedCartier_unitFrames :
    (torusNormalizedCartier k n X j D).localCocycle.HasUnitFramesOn j.opensRange := by
  let E := torusNormalizedCartier k n X j D
  intro i x hx hxi
  let V : X.Opens := E.localCocycle.openSet i⊓j.opensRange
  letI : Nonempty V := ⟨⟨x,hxi,hx⟩⟩
  letI : Nonempty (invertibleOpen E.locallyFree i ⊓ j.opensRange : X.Opens) :=
    ⟨⟨x,hxi,hx⟩⟩
  letI : Nonempty (invertibleOpen E.locallyFree i) :=
    ⟨⟨i,mem_invertibleOpen E.locallyFree i⟩⟩
  let e := invertibleFrame E.locallyFree i
  have hrange := torusNormalizedCartier_range_on_open k n X j D V inf_le_right
  have hq : (E.localCocycle.generator i : X.functionField)∈E.sectionValueRange V := by
    refine ⟨E.frameGenerator e V inf_le_left,?_⟩
    exact E.sectionValue_frameGenerator e inf_le_left
  change (E.localCocycle.generator i : X.functionField) ∈
    ((torusNormalizedCartier k n X j D).sectionValueRange V : Set X.functionField) at hq
  rw [hrange] at hq
  obtain ⟨a,ha⟩ := hq
  have hone : (1 : X.functionField)∈E.sectionValueRange V := by
    change (1 : X.functionField) ∈
      ((torusNormalizedCartier k n X j D).sectionValueRange V : Set X.functionField)
    rw [hrange]
    exact ⟨1,map_one _⟩
  obtain ⟨b,hb⟩ := (E.mem_sectionValueRange_iff e inf_le_left 1).mp hone
  have hb' : X.germToFunctionField V b=(E.localCocycle.generator i : X.functionField)⁻¹ := by
    apply mul_right_cancel₀ (E.localCocycle.generator i).ne_zero
    rw [inv_mul_cancel₀ (E.localCocycle.generator i).ne_zero]
    exact hb
  constructor
  · rw [← ha]
    exact regular_germ_mem_regularAt X V a x ⟨hxi,hx⟩
  · rw [← hb']
    exact regular_germ_mem_regularAt X V b x ⟨hxi,hx⟩

end NormalizedTorus

end PaperVerification.ToricSchemes
end
end Source_ToricCartierBoundaryInvariance
-- END ORIGINAL PaperVerification.ToricCartierBoundaryInvariance


-- BEGIN ORIGINAL PaperVerification.ToricNormalizedCartierAction
section Source_ToricNormalizedCartierAction

-- original header: module

-- original header: public import PaperVerification.ToricCartierBoundaryInvariance
-- original header: public import PaperVerification.ToricActionProductProperties

-- original header: @[expose] public section

/-!
# The normalized Cartier divisor is invariant under the actual torus action

The only geometric assumptions are an actual dense equivariant open torus
embedding and ordinary smoothness. Normality, product integrality, local
Noetherianity, boundary invariance, and equality of Cartier presentations
are conclusions of the preceding proofs. The comparison is equality of
embedded fractional sheaves, which is stronger than an unspecified
isomorphism of line bundles.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

variable {k : Type u} [Field k] {n : ℕ}
    {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n→ℤ)) X]
    [IsIntegral X.left] [Smooth X.hom]
    (T : SplitToricEmbedding k n X)

theorem action_pullback_equivalent_of_unitFrames
    [IsLocallyNoetherian X.left] (E : CartierData X.left)
    (hE : E.localCocycle.HasUnitFramesOn T.torusOpen) :
    (E.dominantPullback (γ[splitTorusOver k (Fin n→ℤ),X]).left).Equivalent
      (E.dominantPullback (snd (splitTorusOver k (Fin n→ℤ)) X).left) := by
  let G := splitTorusOver k (Fin n→ℤ)
  let Y := G⊗X
  let p := (snd G X).left
  let a := (γ[G,X]).left
  let C := E.localCocycle
  let P := C.dominantPullback p
  letI : IsLocallyNoetherian Y.left := T.product_locallyNoetherian
  letI : Smooth Y.hom := T.product_smooth
  have hunit : P.HasUnitFramesOn (p ⁻¹ᵁ T.torusOpen) :=
    C.hasUnitFramesOn_pullback T.torusOpen
      hE p
  have hzero : ∀ y∉T.productBoundary,P.toCartierData.weilCoefficient y=0 := by
    intro y hy
    apply P.weilCoefficient_zero_of_unitFrames (p ⁻¹ᵁ T.torusOpen) hunit y
    exact Classical.not_not.mp hy
  have hInv : (P.dominantPullback T.graphIso.hom).toCartierData.Equivalent
      P.toCartierData :=
    P.equivalent_pullback_of_boundary_fixed Y.hom T.graphIso T.productBoundary
      T.graph_preimage_productBoundary T.graph_fixes_codimensionOne_boundary hzero
  have hcomp := C.dominantPullback_comp_equivalent p T.graphIso.hom
  have hpa : T.graphIso.hom ≫ p = a := T.graph_hom_snd
  have hcomp' : (P.dominantPullback T.graphIso.hom).toCartierData.Equivalent
      (C.dominantPullback a).toCartierData := by
    simpa only [P, hpa] using hcomp
  exact (C.dominantPullback a).toCartierData.equivalent_trans
    (P.dominantPullback T.graphIso.hom).toCartierData P.toCartierData
    ((P.dominantPullback T.graphIso.hom).toCartierData.equivalent_symm
      (C.dominantPullback a).toCartierData hcomp') hInv

theorem normalized_action_pullback_equivalent_of_locallyNoetherian
    [IsLocallyNoetherian X.left] (D : CartierData X.left) :
    ((torusNormalizedCartier k n X.left T.torus.left D).dominantPullback
      (γ[splitTorusOver k (Fin n→ℤ),X]).left).Equivalent
        ((torusNormalizedCartier k n X.left T.torus.left D).dominantPullback
          (snd (splitTorusOver k (Fin n→ℤ)) X).left) :=
  T.action_pullback_equivalent_of_unitFrames
    (torusNormalizedCartier k n X.left T.torus.left D)
    (torusNormalizedCartier_unitFrames k n X.left T.torus.left D)

/-- The local Noetherian condition in the proof is derived from ordinary
smoothness over the field and is absent from the mathematical inputs. -/
theorem normalized_action_pullback_equivalent (D : CartierData X.left) :
    letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
    ((torusNormalizedCartier k n X.left T.torus.left D).dominantPullback
      (γ[splitTorusOver k (Fin n→ℤ),X]).left).Equivalent
        ((torusNormalizedCartier k n X.left T.torus.left D).dominantPullback
          (snd (splitTorusOver k (Fin n→ℤ)) X).left) := by
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  exact T.normalized_action_pullback_equivalent_of_locallyNoetherian D

/-- The corresponding isomorphism of the actual ordinary sheaf pullbacks.
It is obtained from equality of their proved fractional realizations. -/
def normalizedActionSheafIso (D : CartierData X.left) :
    letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
    (Scheme.Modules.pullback (γ[splitTorusOver k (Fin n→ℤ),X]).left).obj
        (torusNormalizedCartier k n X.left T.torus.left D).sheaf ≅
      (Scheme.Modules.pullback (snd (splitTorusOver k (Fin n→ℤ)) X).left).obj
        (torusNormalizedCartier k n X.left T.torus.left D).sheaf := by
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let E := torusNormalizedCartier k n X.left T.torus.left D
  exact E.dominantPullbackSheafIso (γ[splitTorusOver k (Fin n→ℤ),X]).left ≪≫
    (T.normalized_action_pullback_equivalent D).choose ≪≫
      (E.dominantPullbackSheafIso (snd (splitTorusOver k (Fin n→ℤ)) X).left).symm

end PaperVerification.ToricSchemes.SplitToricEmbedding
end
end Source_ToricNormalizedCartierAction
-- END ORIGINAL PaperVerification.ToricNormalizedCartierAction


-- BEGIN ORIGINAL PaperVerification.ToricIntrinsicSectionCharacters
section Source_ToricIntrinsicSectionCharacters

-- original header: module

-- original header: public import PaperVerification.ToricNormalizedCartierAction
-- original header: public import PaperVerification.ToricBaseSectionNaturality
-- original header: public import PaperVerification.ToricCharacterSubrepresentations
-- original header: public import PaperVerification.ToricCartierRationalSections

-- original header: @[expose] public section

/-!
# Laurent values of actual intrinsic toric global sections

The dense open torus and the proved torus Picard trivialization give the
Laurent polynomial of a genuine global section. No fan, affine invariant
cover, character basis, or section-coaction hypothesis enters this map.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

universe u

open AlgebraicGeometry CategoryTheory Opposite
open PaperVerification.ToricCharacters
open scoped PaperVerification.ToricSchemes.BaseSections

namespace PaperVerification.ToricSchemes

variable (k : Type u) [Field k] (n : ℕ)
    (X : Scheme.{u}) [IsIntegral X] [X.Over (Spec (CommRingCat.of k))]
    (j : splitTorus k (Fin n→ℤ) ⟶ X) [hj : IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k))]

local instance openTorus_coordinate_isDomain : IsDomain (torusCoordinateRing k n) :=
  torusCoordinateRing_isDomain k n

local instance openTorus_coordinate_isOpenImmersion :
    IsOpenImmersion (show Spec (CommRingCat.of (torusCoordinateRing k n)) ⟶ X from j) := hj

local instance openTorus_coordinate_isOver :
    (show Spec (CommRingCat.of (torusCoordinateRing k n)) ⟶ X from j).IsOver
      (Spec (CommRingCat.of k)) :=
  inferInstanceAs (j.IsOver (Spec (CommRingCat.of k)))

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual coordinate-ring embedding from the dense open torus,
with the base scalars supplied by the actual structural morphism. -/
def openTorusRationalAlgHom : AddMonoidAlgebra k (Fin n→ℤ) →ₐ[k] X.functionField where
  __ := affineOpenCoordinateMap (CommRingCat.of (torusCoordinateRing k n)) j
  commutes' c := by
    change affineOpenCoordinateMap (CommRingCat.of (torusCoordinateRing k n)) j
      (algebraMap k (torusCoordinateRing k n) c) = algebraMap k X.functionField c
    apply (torusOpenFunctionFieldEquiv k n X j).injective
    have hs : (Scheme.ΓSpecIso (CommRingCat.of (torusCoordinateRing k n))).hom
        (j.appTop (BaseSections.scalarMap k X ⊤ c)) =
          algebraMap k (torusCoordinateRing k n) c := by
      calc
        _ = (Scheme.ΓSpecIso (CommRingCat.of (torusCoordinateRing k n))).hom
            (BaseSections.scalarMap k
              (Spec (CommRingCat.of (torusCoordinateRing k n))) ⊤ c) :=
          congrArg (Scheme.ΓSpecIso (CommRingCat.of (torusCoordinateRing k n))).hom
            (BaseSections.scalarMap_top_natural k j c)
        _ = (Scheme.ΓSpecIso (CommRingCat.of (torusCoordinateRing k n))).hom
            ((Scheme.ΓSpecIso (CommRingCat.of (torusCoordinateRing k n))).inv
              (algebraMap k (torusCoordinateRing k n) c)) :=
          congrArg (Scheme.ΓSpecIso (CommRingCat.of (torusCoordinateRing k n))).hom
            (BaseSections.scalarMap_affine_top k (torusCoordinateRing k n) c)
        _ = _ := by simp only [Iso.inv_hom_id_apply]
    calc
      _ = algebraMap (torusCoordinateRing k n) (FractionRing (torusCoordinateRing k n))
          (algebraMap k (torusCoordinateRing k n) c) :=
        affineOpenFunctionFieldEquiv_coordinateMap
          (CommRingCat.of (torusCoordinateRing k n)) j _
      _ = algebraMap (torusCoordinateRing k n) (FractionRing (torusCoordinateRing k n))
          ((Scheme.ΓSpecIso (CommRingCat.of (torusCoordinateRing k n))).hom
            (j.appTop (BaseSections.scalarMap k X ⊤ c))) :=
        congrArg (algebraMap (torusCoordinateRing k n)
          (FractionRing (torusCoordinateRing k n))) hs.symm
      _ = torusOpenFunctionFieldEquiv k n X j
          (X.germToFunctionField ⊤ (BaseSections.scalarMap k X ⊤ c)) :=
        (torusOpenFunctionFieldEquiv_germ_top k n X j
          (BaseSections.scalarMap k X ⊤ c)).symm
      _ = _ := congrArg (torusOpenFunctionFieldEquiv k n X j)
        (BaseSections.germ_scalarMap k ⊤ c)

theorem openTorusRationalAlgHom_injective :
    Function.Injective (openTorusRationalAlgHom k n X j) :=
  (openImmersionGlobalToFunctionField_injective j).comp
    (Scheme.ΓSpecIso (CommRingCat.of (torusCoordinateRing k n))).commRingCatIsoToRingEquiv.symm.injective

@[simp] theorem openTorusRationalAlgHom_value (f : AddMonoidAlgebra k (Fin n→ℤ)) :
    openTorusRationalAlgHom k n X j f =
      openImmersionGlobalToFunctionField j
        ((Scheme.ΓSpecIso (CommRingCat.of (torusCoordinateRing k n))).inv f) := rfl

variable (D : CartierData X)

/-- Restriction of a genuine global section to the actual open torus. -/
def normalizedGlobalTorusRestriction
    (s : Γ((torusNormalizedCartier k n X j D).sheaf,⊤)) :
    Γ((torusNormalizedCartier k n X j D).sheaf.restrict j,⊤) :=
  ((torusNormalizedCartier k n X j D).sheaf.restrictAppIso j ⊤).inv
    ((torusNormalizedCartier k n X j D).sheaf.presheaf.map
      (homOfLE (show j ''ᵁ (⊤ : (splitTorus k (Fin n→ℤ)).Opens)≤⊤ from le_top)).op s)

theorem normalizedGlobalTorusRestriction_value
    (s : Γ((torusNormalizedCartier k n X j D).sheaf,⊤)) :
    (torusNormalizedCartier k n X j D).alongSectionValue j ⊤
      (normalizedGlobalTorusRestriction k n X j D s) =
      (torusNormalizedCartier k n X j D).globalSectionValue k s := by
  let E := torusNormalizedCartier k n X j D
  letI : Nonempty (j ''ᵁ (⊤ : (splitTorus k (Fin n→ℤ)).Opens)) :=
    openImmersion_image_nonempty j ⊤
  change E.sectionValue (j ''ᵁ ⊤)
    ((E.sheaf.restrictAppIso j ⊤).hom
      ((E.sheaf.restrictAppIso j ⊤).inv
        (E.sheaf.presheaf.map (homOfLE le_top).op s)))=E.sectionValue ⊤ s
  simp only [Iso.inv_hom_id_apply]
  exact E.sectionValue_restrict (homOfLE le_top) s

/-- The explicit Laurent polynomial of the normalized section. -/
def normalizedSectionLaurent
    (s : Γ((torusNormalizedCartier k n X j D).sheaf,⊤)) :
    AddMonoidAlgebra k (Fin n→ℤ) :=
  (Scheme.ΓSpecIso (CommRingCat.of (torusCoordinateRing k n))).hom
    ((torusNormalizedCartierSheafIso k n X j D).hom.app ⊤
      (normalizedGlobalTorusRestriction k n X j D s))

/-- The Laurent polynomial has exactly the original rational value. -/
theorem normalizedSectionLaurent_value
    (s : Γ((torusNormalizedCartier k n X j D).sheaf,⊤)) :
    openTorusRationalAlgHom k n X j (normalizedSectionLaurent k n X j D s) =
      (torusNormalizedCartier k n X j D).globalSectionValue k s := by
  calc
    _ = openImmersionRegularToFunctionField j ⊤
        ((torusNormalizedCartierSheafIso k n X j D).hom.app ⊤
          (normalizedGlobalTorusRestriction k n X j D s)) := by
      exact congrArg (openImmersionGlobalToFunctionField j)
        (Iso.hom_inv_id_apply
          (Scheme.ΓSpecIso (CommRingCat.of (torusCoordinateRing k n))) _)
    _ = (torusNormalizedCartier k n X j D).alongSectionValue j ⊤
        (normalizedGlobalTorusRestriction k n X j D s) :=
      (torusNormalizedCartier_value k n X j D ⊤ _).symm
    _ = _ := normalizedGlobalTorusRestriction_value k n X j D s

/-- The Laurent-value map is linear over the true base field, proved
through its actual injective rational-value map. -/
def normalizedSectionLaurentLinear :
    Γ((torusNormalizedCartier k n X j D).sheaf,⊤) →ₗ[k]
      AddMonoidAlgebra k (Fin n→ℤ) where
  toFun := normalizedSectionLaurent k n X j D
  map_add' s t := by
    apply openTorusRationalAlgHom_injective k n X j
    rw [map_add,normalizedSectionLaurent_value,normalizedSectionLaurent_value,
      normalizedSectionLaurent_value,map_add]
  map_smul' c s := by
    apply openTorusRationalAlgHom_injective k n X j
    rw [map_smul,normalizedSectionLaurent_value,normalizedSectionLaurent_value,
      map_smul]
    rfl

theorem normalizedSectionLaurentLinear_injective :
    Function.Injective (normalizedSectionLaurentLinear k n X j D) := by
  intro s t h
  apply (torusNormalizedCartier k n X j D).globalSectionValue_injective k
  rw [← normalizedSectionLaurent_value,← normalizedSectionLaurent_value]
  exact congrArg (openTorusRationalAlgHom k n X j) h

/-- The actual Laurent image of the genuine normalized global-section
space. Coaction stability is proved subsequently, not built into it. -/
def normalizedGlobalCharacters : Submodule k (AddMonoidAlgebra k (Fin n→ℤ)) :=
  (normalizedSectionLaurentLinear k n X j D).range

theorem mem_normalizedGlobalCharacters_iff (f : AddMonoidAlgebra k (Fin n→ℤ)) :
    f∈normalizedGlobalCharacters k n X j D ↔
      openTorusRationalAlgHom k n X j f∈
        ((torusNormalizedCartier k n X j D).globalSectionValue k).range := by
  constructor
  · rintro ⟨s,rfl⟩
    exact ⟨s,(normalizedSectionLaurent_value k n X j D s).symm⟩
  · rintro ⟨s,hs⟩
    refine ⟨s,?_⟩
    apply openTorusRationalAlgHom_injective k n X j
    exact (normalizedSectionLaurent_value k n X j D s).trans hs

def normalizedGlobalSectionCoordinates :
    Γ((torusNormalizedCartier k n X j D).sheaf,⊤) ≃ₗ[k]
      normalizedGlobalCharacters k n X j D :=
  LinearEquiv.ofInjective (normalizedSectionLaurentLinear k n X j D)
    (normalizedSectionLaurentLinear_injective k n X j D)

/-- The literal Laurent part of the actual section image of any Cartier
presentation. No normalization or stability is included in the definition. -/
def torusSectionCharacters (E : CartierData X) :
    Submodule k (AddMonoidAlgebra k (Fin n→ℤ)) :=
  ((E.globalSectionValue k).range).comap (openTorusRationalAlgHom k n X j).toLinearMap

@[simp] theorem mem_torusSectionCharacters (E : CartierData X)
    (f : AddMonoidAlgebra k (Fin n→ℤ)) :
    f∈torusSectionCharacters k n X j E ↔
      openTorusRationalAlgHom k n X j f∈(E.globalSectionValue k).range := Iff.rfl

theorem normalizedGlobalCharacters_eq_torusSectionCharacters :
    normalizedGlobalCharacters k n X j D =
      torusSectionCharacters k n X j (torusNormalizedCartier k n X j D) := by
  ext f
  exact mem_normalizedGlobalCharacters_iff k n X j D f

/-- Actual unit local frames on the torus force every genuine global
section to restrict to a Laurent polynomial. -/
theorem globalSectionValue_in_torusRange_of_unitFrames (E : CartierData X)
    (hE : E.localCocycle.HasUnitFramesOn j.opensRange)
    (z : X.functionField) (hz : z∈(E.globalSectionValue k).range) :
    ∃ f : AddMonoidAlgebra k (Fin n→ℤ),openTorusRationalAlgHom k n X j f=z := by
  let U := j ''ᵁ (⊤ : (splitTorus k (Fin n→ℤ)).Opens)
  letI : Nonempty U := openImmersion_image_nonempty j ⊤
  have hregular : ∀ x∈U,z∈regularAtSubring X x := by
    intro x hx
    obtain ⟨i,hi⟩ := E.localCocycle.covers x
    have hr := (E.mem_sectionValueRange_iff_localStalks ⊤ z).mp hz i x trivial hi
    have hq := hE i x (by simpa only [U,Scheme.Hom.image_top_eq_opensRange] using hx) hi
    have h := (regularAtSubring X x).mul_mem hr hq.1
    simpa only [div_mul_cancel₀ _ (E.localCocycle.generator i).ne_zero] using h
  obtain ⟨a,ha⟩ := exists_regularSection_of_stalkwise X U z hregular
  let f := (Scheme.ΓSpecIso (CommRingCat.of (torusCoordinateRing k n))).hom
    ((j.appIso ⊤).hom a)
  refine ⟨f,?_⟩
  calc
    _ = openImmersionRegularToFunctionField j ⊤ ((j.appIso ⊤).hom a) := by
      exact congrArg (openImmersionGlobalToFunctionField j)
        (Iso.hom_inv_id_apply
          (Scheme.ΓSpecIso (CommRingCat.of (torusCoordinateRing k n))) _)
    _ = X.germToFunctionField U ((j.appIso ⊤).inv ((j.appIso ⊤).hom a)) :=
      openImmersionRegularToFunctionField_eq_germ_image j ⊤ _
    _ = X.germToFunctionField U a :=
      congrArg (X.germToFunctionField U) (Iso.hom_inv_id_apply (j.appIso ⊤) a)
    _ = z := ha

def torusSectionCharacterValue (E : CartierData X) :
    torusSectionCharacters k n X j E →ₗ[k] X.functionField :=
  (openTorusRationalAlgHom k n X j).toLinearMap.comp
    (torusSectionCharacters k n X j E).subtype

theorem torusSectionCharacterValue_injective (E : CartierData X) :
    Function.Injective (torusSectionCharacterValue k n X j E) :=
  (openTorusRationalAlgHom_injective k n X j).comp Subtype.val_injective

theorem torusSectionCharacterValue_range (E : CartierData X)
    (hE : E.localCocycle.HasUnitFramesOn j.opensRange) :
    (torusSectionCharacterValue k n X j E).range=(E.globalSectionValue k).range := by
  ext z
  constructor
  · rintro ⟨f,rfl⟩
    exact f.property
  · intro hz
    obtain ⟨f,hf⟩ := globalSectionValue_in_torusRange_of_unitFrames k n X j E hE z hz
    refine ⟨⟨f,?_⟩,hf⟩
    change openTorusRationalAlgHom k n X j f∈(E.globalSectionValue k).range
    rwa [hf]

/-- A genuine base-linear coordinate equivalence for every presentation
with proved unit frames on the torus, including actual tensor powers. -/
def torusSectionCoordinates (E : CartierData X)
    (hE : E.localCocycle.HasUnitFramesOn j.opensRange) :
    Γ(E.sheaf,⊤) ≃ₗ[k] torusSectionCharacters k n X j E :=
  (LinearEquiv.ofInjective (E.globalSectionValue k)
    (E.globalSectionValue_injective k)).trans
    ((LinearEquiv.ofEq _ _ (torusSectionCharacterValue_range k n X j E hE).symm).trans
      (LinearEquiv.ofInjective (torusSectionCharacterValue k n X j E)
        (torusSectionCharacterValue_injective k n X j E)).symm)

theorem torusSectionCoordinates_value (E : CartierData X)
    (hE : E.localCocycle.HasUnitFramesOn j.opensRange) (s : Γ(E.sheaf,⊤)) :
    openTorusRationalAlgHom k n X j ((torusSectionCoordinates k n X j E hE s).val)=
      E.globalSectionValue k s := by
  change torusSectionCharacterValue k n X j E (torusSectionCoordinates k n X j E hE s)=_
  simp only [torusSectionCoordinates,LinearEquiv.trans_apply,
    LinearEquiv.ofInjective_symm_apply,LinearEquiv.coe_ofEq_apply,
    LinearEquiv.ofInjective_apply]

end PaperVerification.ToricSchemes
end
end Source_ToricIntrinsicSectionCharacters
-- END ORIGINAL PaperVerification.ToricIntrinsicSectionCharacters


-- BEGIN ORIGINAL PaperVerification.ToricActionSectionRegularity
section Source_ToricActionSectionRegularity

-- original header: module

-- original header: public import PaperVerification.ToricIntrinsicSectionCharacters
-- original header: public import PaperVerification.ToricCartierRationalSections

-- original header: @[expose] public section

/-!
# Actual local regularity of the torus action on a normalized section

This is the geometric input to coefficient extraction. It is a statement
about ordinary regular functions on the actual product scheme and follows
from the independently proved equality of its fractional Cartier sheaves.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open PaperVerification.ToricCharacters
open scoped PaperVerification.ToricSchemes.BaseSections

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

variable {k : Type u} [Field k] {n : ℕ}
    {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n→ℤ)) X]
    [IsIntegral X.left] [Smooth X.hom] [IsLocallyNoetherian X.left]
    (T : SplitToricEmbedding k n X) (D : CartierData X.left)

theorem action_ratio_regular_of_unitFrames
    (E : CartierData X.left) (hE : E.localCocycle.HasUnitFramesOn T.torusOpen)
    (f : AddMonoidAlgebra k (Fin n→ℤ))
    (hf : f∈torusSectionCharacters k n X.left T.torus.left E)
    (i : E.localCocycle.index)
    (U : X.left.Opens) [Nonempty U]
    (hU : U≤E.localCocycle.openSet i) :
    let p := (snd (splitTorusOver k (Fin n→ℤ)) X).left
    letI : Nonempty (p ⁻¹ᵁ U) := dominant_preimage_nonempty p U
    dominantFunctionFieldMap (γ[splitTorusOver k (Fin n→ℤ),X]).left
        (openTorusRationalAlgHom k n X.left T.torus.left f) /
      dominantFunctionFieldMap p
        (E.localCocycle.generator i :
          X.left.functionField) ∈
      ((splitTorusOver k (Fin n→ℤ)⊗X).left.germToFunctionField (p ⁻¹ᵁ U)).hom.range := by
  let G := splitTorusOver k (Fin n→ℤ)
  let Y := (G⊗X).left
  let p := (snd G X).left
  let a := (γ[G,X]).left
  let q := openTorusRationalAlgHom k n X.left T.torus.left f
  letI : Nonempty (p ⁻¹ᵁ U) := dominant_preimage_nonempty p U
  have hq : q∈E.sectionValueRange ⊤ :=
    hf
  have ha : dominantFunctionFieldMap a q∈(E.dominantPullback a).sectionValueRange ⊤ := by
    letI : Nonempty (a ⁻¹ᵁ (⊤ : X.left.Opens)) := dominant_preimage_nonempty a ⊤
    exact E.dominantPullback_mem_sectionValueRange a ⊤ q hq
  have hp : dominantFunctionFieldMap a q∈(E.dominantPullback p).sectionValueRange ⊤ := by
    rw [← (E.dominantPullback a).equivalent_sectionValueRange
      (E.dominantPullback p)
      (T.action_pullback_equivalent_of_unitFrames E hE) ⊤]
    exact ha
  obtain ⟨s,hs⟩ := hp
  have hlocal : dominantFunctionFieldMap a q∈
      (E.dominantPullback p).sectionValueRange (p ⁻¹ᵁ U) :=
    ⟨(E.dominantPullback p).sheaf.presheaf.map (homOfLE le_top).op s,
      ((E.dominantPullback p).sectionValue_restrict (homOfLE le_top) s).trans hs⟩
  exact ((E.localCocycle.dominantPullback p).mem_sectionValueRange_iff i
    (p ⁻¹ᵁ U) (p.preimage_mono hU) (dominantFunctionFieldMap a q)).mp hlocal

theorem normalized_action_ratio_regular
    (f : AddMonoidAlgebra k (Fin n→ℤ))
    (hf : f∈normalizedGlobalCharacters k n X.left T.torus.left D)
    (i : (torusNormalizedCartier k n X.left T.torus.left D).localCocycle.index)
    (U : X.left.Opens) [Nonempty U]
    (hU : U≤(torusNormalizedCartier k n X.left T.torus.left D).localCocycle.openSet i) :
    let p := (snd (splitTorusOver k (Fin n→ℤ)) X).left
    letI : Nonempty (p ⁻¹ᵁ U) := dominant_preimage_nonempty p U
    dominantFunctionFieldMap (γ[splitTorusOver k (Fin n→ℤ),X]).left
        (openTorusRationalAlgHom k n X.left T.torus.left f) /
      dominantFunctionFieldMap p
        ((torusNormalizedCartier k n X.left T.torus.left D).localCocycle.generator i :
          X.left.functionField) ∈
      ((splitTorusOver k (Fin n→ℤ)⊗X).left.germToFunctionField (p ⁻¹ᵁ U)).hom.range :=
  T.action_ratio_regular_of_unitFrames (torusNormalizedCartier k n X.left T.torus.left D)
    (torusNormalizedCartier_unitFrames k n X.left T.torus.left D) f
    ((mem_normalizedGlobalCharacters_iff k n X.left T.torus.left D f).mp hf) i U hU

end PaperVerification.ToricSchemes.SplitToricEmbedding
end
end Source_ToricActionSectionRegularity
-- END ORIGINAL PaperVerification.ToricActionSectionRegularity


-- BEGIN ORIGINAL PaperVerification.ToricAffinePullbackSections
section Source_ToricAffinePullbackSections

-- original header: module

-- original header: public import PaperVerification.ToricFunctionFieldBridge

-- original header: @[expose] public section

/-!
# Pulling regular functions through an actual affine chart square

This argument does not require dominance. A function which is regular
on an ambient affine chart pulls back through its actual coordinate-ring
homomorphism. The conclusion is expressed in the function field of the
source only after pulling back the regular section.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (R S : CommRingCat.{u}) [IsDomain R] [IsDomain S]
    (j : Spec R ⟶ X) (l : Spec S ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion l]

/-- The actual regular function on the image of an affine chart. -/
def affineChartSection (r : R) : Γ(X,j ''ᵁ (⊤ : (Spec R).Opens)) :=
  (j.appIso ⊤).inv ((Scheme.ΓSpecIso R).inv r)

theorem affineChartSection_germ
    [Nonempty (j ''ᵁ (⊤ : (Spec R).Opens))] (r : R) :
    X.germToFunctionField (j ''ᵁ (⊤ : (Spec R).Opens))
      (affineChartSection R j r) = affineOpenCoordinateMap R j r :=
  (openImmersionRegularToFunctionField_eq_germ_image j ⊤
    ((Scheme.ΓSpecIso R).inv r)).symm

variable (f : Y ⟶ X) (φ : R ⟶ S)
    (hcomm : l ≫ f = Spec.map φ ≫ j)

include hcomm in
theorem affineChartSquare_image_le :
    l ''ᵁ (⊤ : (Spec S).Opens) ≤ f ⁻¹ᵁ (j ''ᵁ (⊤ : (Spec R).Opens)) := by
  rintro y ⟨q,hq,rfl⟩
  exact ⟨Spec.map φ q,trivial,
    (congrArg (fun g : Spec S ⟶ X=>g q) hcomm).symm⟩

set_option backward.isDefEq.respectTransparency.types false in
theorem affineChartSquare_sections :
    f.appLE (j ''ᵁ (⊤ : (Spec R).Opens)) (l ''ᵁ (⊤ : (Spec S).Opens))
        (affineChartSquare_image_le R S j l f φ hcomm) ≫ (l.appIso ⊤).hom =
      (j.appIso ⊤).hom ≫ (Spec.map φ).appTop := by
  rw [l.appIso_hom',j.appIso_hom']
  change f.appLE _ _ _ ≫ l.appLE _ ⊤ _ =
    j.appLE _ ⊤ _ ≫ (Spec.map φ).appLE ⊤ ⊤ le_top
  rw [Scheme.Hom.appLE_comp_appLE,Scheme.Hom.appLE_comp_appLE]
  have hc {a b : Spec S ⟶ X} (hab : a = b)
      (ha : (⊤ : (Spec S).Opens) ≤ a ⁻¹ᵁ (j ''ᵁ (⊤ : (Spec R).Opens)))
      (hb : (⊤ : (Spec S).Opens) ≤ b ⁻¹ᵁ (j ''ᵁ (⊤ : (Spec R).Opens))) :
      a.appLE (j ''ᵁ (⊤ : (Spec R).Opens)) ⊤ ha =
        b.appLE (j ''ᵁ (⊤ : (Spec R).Opens)) ⊤ hb := by
    cases hab
    rfl
  have ha : (⊤ : (Spec S).Opens) ≤ (l ≫ f) ⁻¹ᵁ (j ''ᵁ (⊤ : (Spec R).Opens)) :=
    (l.preimage_image_eq ⊤).ge.trans
      (l.preimage_mono (affineChartSquare_image_le R S j l f φ hcomm))
  exact hc hcomm ha (hcomm ▸ ha)

/-- Equality of genuine regular sections on the source chart image. -/
theorem affineChartSection_pullback (r : R) :
    f.appLE (j ''ᵁ (⊤ : (Spec R).Opens)) (l ''ᵁ (⊤ : (Spec S).Opens))
      (affineChartSquare_image_le R S j l f φ hcomm)
      (affineChartSection R j r) = affineChartSection S l (φ r) := by
  apply (l.appIso ⊤).commRingCatIsoToRingEquiv.injective
  calc
    (l.appIso ⊤).hom
        (f.appLE _ _ (affineChartSquare_image_le R S j l f φ hcomm)
          (affineChartSection R j r)) =
      (Spec.map φ).appTop ((j.appIso ⊤).hom (affineChartSection R j r)) :=
        congrArg (fun g=>g (affineChartSection R j r))
          (affineChartSquare_sections R S j l f φ hcomm)
    _ = (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv r) := by
      simp only [affineChartSection,Iso.inv_hom_id_apply]
    _ = (Scheme.ΓSpecIso S).inv (φ r) :=
      (congrArg (fun g=>g r) (Scheme.ΓSpecIso_inv_naturality φ)).symm
    _ = (l.appIso ⊤).hom (affineChartSection S l (φ r)) := by
      simp only [affineChartSection,Iso.inv_hom_id_apply]

include hcomm in
/-- On any smaller open, a regular function with the specified affine
coordinate value pulls back to the value of the actual affine ring map.
Only the regular section is pulled through `f`; no map `K(X) → K(Y)` is
used or assumed. -/
theorem affineChartSection_pullback_value
    (hpre : f ⁻¹ᵁ (j ''ᵁ (⊤ : (Spec R).Opens)) =
      l ''ᵁ (⊤ : (Spec S).Opens))
    (U : X.Opens) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)]
    (hU : U≤j ''ᵁ (⊤ : (Spec R).Opens))
    (r : Γ(X,U)) (a : R)
    (hr : X.germToFunctionField U r=affineOpenCoordinateMap R j a) :
    Y.germToFunctionField (f ⁻¹ᵁ U) (f.app U r) =
      affineOpenCoordinateMap S l (φ a) := by
  let V := j ''ᵁ (⊤ : (Spec R).Opens)
  let W := l ''ᵁ (⊤ : (Spec S).Opens)
  letI : Nonempty V := openImmersion_image_nonempty j ⊤
  letI : Nonempty W := openImmersion_image_nonempty l ⊤
  have hW : f ⁻¹ᵁ U≤W := by
    change f ⁻¹ᵁ U ≤ l ''ᵁ (⊤ : (Spec S).Opens)
    rw [← hpre]
    exact f.preimage_mono hU
  have heq : r = X.presheaf.map (homOfLE hU).op (affineChartSection R j a) := by
    apply X.germToFunctionField_injective U
    rw [germToFunctionField_restrict,affineChartSection_germ,hr]
  rw [heq]
  have hs : f.app U
      (X.presheaf.map (homOfLE hU).op (affineChartSection R j a)) =
      Y.presheaf.map (homOfLE hW).op
        (f.appLE V W (affineChartSquare_image_le R S j l f φ hcomm)
          (affineChartSection R j a)) := by
    have hm : X.presheaf.map (homOfLE hU).op ≫ f.app U =
        f.appLE V W (affineChartSquare_image_le R S j l f φ hcomm) ≫
          Y.presheaf.map (homOfLE hW).op := by
      rw [f.app_eq_appLE,f.map_appLE,f.appLE_map]
    exact congrArg
      (fun g : Γ(X,V) ⟶ Γ(Y,f ⁻¹ᵁ U) => g.hom (affineChartSection R j a)) hm
  rw [hs,affineChartSection_pullback R S j l f φ hcomm,germToFunctionField_restrict,
    affineChartSection_germ]

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.affineChartSection_pullback_value
end
end Source_ToricAffinePullbackSections
-- END ORIGINAL PaperVerification.ToricAffinePullbackSections


-- BEGIN ORIGINAL PaperVerification.ToricDominantAffineCoordinates
section Source_ToricDominantAffineCoordinates

-- original header: module

-- original header: public import PaperVerification.ToricAffinePullbackSections
-- original header: public import PaperVerification.ToricDominantFunctionField

-- original header: @[expose] public section

/-! # Actual dominant rational pullback in commuting affine charts -/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (R S : CommRingCat.{u}) [IsDomain R] [IsDomain S]
    (j : Spec R ⟶ X) (l : Spec S ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion l]
    (f : Y ⟶ X) [IsDominant f] (φ : R ⟶ S)
    (hcomm : l ≫ f = Spec.map φ ≫ j)

include hcomm in
theorem dominantFunctionFieldMap_affineCoordinate (a : R) :
    dominantFunctionFieldMap f (affineOpenCoordinateMap R j a) =
      affineOpenCoordinateMap S l (φ a) := by
  let U := j ''ᵁ (⊤ : (Spec R).Opens)
  let V := l ''ᵁ (⊤ : (Spec S).Opens)
  letI : Nonempty U := openImmersion_image_nonempty j ⊤
  letI : Nonempty V := openImmersion_image_nonempty l ⊤
  letI : Nonempty (f ⁻¹ᵁ U) := dominant_preimage_nonempty f U
  have hVU : V≤f ⁻¹ᵁ U := affineChartSquare_image_le R S j l f φ hcomm
  rw [← affineChartSection_germ R j a,dominantFunctionFieldMap_germ]
  calc
    Y.germToFunctionField (f ⁻¹ᵁ U) (f.app U (affineChartSection R j a)) =
        Y.germToFunctionField V
          (f.appLE U V hVU (affineChartSection R j a)) := by
      change _=Y.germToFunctionField V
        (Y.presheaf.map (homOfLE hVU).op (f.app U (affineChartSection R j a)))
      exact (germToFunctionField_restrict Y (homOfLE hVU) _).symm
    _ = Y.germToFunctionField V (affineChartSection S l (φ a)) := by
      rw [affineChartSection_pullback R S j l f φ hcomm]
    _ = affineOpenCoordinateMap S l (φ a) := affineChartSection_germ S l _

end PaperVerification.ToricSchemes
end
end Source_ToricDominantAffineCoordinates
-- END ORIGINAL PaperVerification.ToricDominantAffineCoordinates


-- BEGIN ORIGINAL PaperVerification.ToricTensorFractions
section Source_ToricTensorFractions

-- original header: module

-- original header: public import PaperVerification.ToricLaurentPicard
-- original header: public import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
-- original header: public import Mathlib.RingTheory.Localization.FractionRing
-- original header: public import Mathlib.RingTheory.Flat.Basic

-- original header: @[expose] public section

/-!
# Actual Laurent scalar extension and tensor denominator clearing

The tensor product with a lattice character algebra remains a domain over
an arbitrary domain. A tensor with a fraction field admits one common
denominator from the original coefficient ring. These elementary facts
will prove injectivity of the actual torus-product rational map.
-/

noncomputable section

universe u

namespace PaperVerification.ToricCharacters

open AddMonoidAlgebra
open scoped TensorProduct nonZeroDivisors

theorem latticeGroupAlgebra_isDomain (R : Type*) [CommRing R] [IsDomain R] (n : ℕ) :
    IsDomain (AddMonoidAlgebra R (Fin n→ℤ)) := by
  letI := torusCoordinateRing_isDomain (FractionRing R) n
  let f := AddMonoidAlgebra.mapRingHom (Fin n→ℤ) (algebraMap R (FractionRing R))
  apply Function.Injective.isDomain f
  exact AddMonoidAlgebra.map_injective (algebraMap R (FractionRing R)).toAddMonoidHom
    (IsFractionRing.injective R (FractionRing R))

def latticeTensorAlgEquiv (k : Type*) [CommRing k] (n : ℕ)
    (R : Type*) [CommRing R] [Algebra k R] :
    AddMonoidAlgebra k (Fin n→ℤ) ⊗[k] R ≃ₐ[k] AddMonoidAlgebra R (Fin n→ℤ) :=
  (Algebra.TensorProduct.comm k (AddMonoidAlgebra k (Fin n→ℤ)) R).trans
    ((AddMonoidAlgebra.scalarTensorEquiv k R (M:=Fin n→ℤ)).restrictScalars k)

theorem latticeTensor_isDomain (k : Type*) [CommRing k] (n : ℕ)
    (R : Type*) [CommRing R] [IsDomain R] [Algebra k R] :
    IsDomain (AddMonoidAlgebra k (Fin n→ℤ) ⊗[k] R) := by
  letI := latticeGroupAlgebra_isDomain R n
  exact MulEquiv.isDomain (AddMonoidAlgebra R (Fin n→ℤ))
    (latticeTensorAlgEquiv k n R).toMulEquiv

section Denominators

variable (k A R K : Type*) [CommRing k] [CommRing A] [CommRing R] [IsDomain R]
    [Field K] [Algebra k A] [Algebra k R] [Algebra k K] [Algebra R K]
    [IsScalarTower k R K] [IsFractionRing R K]

/-- A tensor has finitely many fraction coefficients, so a single
nonzero coefficient-ring denominator clears all of them. -/
theorem tensor_exists_common_denominator (w : A ⊗[k] K) :
    ∃ (d : R) (_ : d≠0) (t : A ⊗[k] R),
      Algebra.TensorProduct.map (AlgHom.id k A) (IsScalarTower.toAlgHom k R K) t=
        (1 ⊗ₜ[k] algebraMap R K d)*w := by
  let F := Algebra.TensorProduct.map (AlgHom.id k A) (IsScalarTower.toAlgHom k R K)
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨1,one_ne_zero,0,by simp⟩
  | tmul a z =>
      obtain ⟨r,d,hd,hz⟩ := IsFractionRing.div_surjective R z
      have hd0 : d≠0 := mem_nonZeroDivisors_iff_ne_zero.mp hd
      have hdK : algebraMap R K d≠0 := by
        simpa only [map_zero] using (IsFractionRing.injective R K).ne hd0
      refine ⟨d,hd0,a ⊗ₜ[k] r,?_⟩
      rw [← hz]
      simp only [Algebra.TensorProduct.map_tmul,AlgHom.id_apply,
        IsScalarTower.toAlgHom_apply,Algebra.TensorProduct.tmul_mul_tmul,one_mul]
      rw [mul_div_cancel₀ _ hdK]
  | add w z hw hz =>
      obtain ⟨d,hd,t,ht⟩ := hw
      obtain ⟨e,he,u,hu⟩ := hz
      refine ⟨d*e,mul_ne_zero hd he,(1 ⊗ₜ[k] e)*t+(1 ⊗ₜ[k] d)*u,?_⟩
      change F _=_
      rw [map_add,map_mul,map_mul,show F t=(1 ⊗ₜ[k] algebraMap R K d)*w from ht,
        show F u=(1 ⊗ₜ[k] algebraMap R K e)*z from hu]
      simp only [F,Algebra.TensorProduct.map_tmul,AlgHom.id_apply,
        IsScalarTower.toAlgHom_apply,map_mul]
      have hprod : (1 ⊗ₜ[k] (algebraMap R K d*algebraMap R K e) : A ⊗[k] K)=
          (1 ⊗ₜ[k] algebraMap R K d)*(1 ⊗ₜ[k] algebraMap R K e) := by
        simp only [Algebra.TensorProduct.tmul_mul_tmul,one_mul]
      rw [hprod]
      ring

end Denominators

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.tensor_exists_common_denominator
end
end Source_ToricTensorFractions
-- END ORIGINAL PaperVerification.ToricTensorFractions


-- BEGIN ORIGINAL PaperVerification.ToricAffineProductCharts
section Source_ToricAffineProductCharts

-- original header: module

-- original header: public import PaperVerification.ToricActionProductProperties
-- original header: public import PaperVerification.ToricBaseSectionNaturality
-- original header: public import PaperVerification.ToricDominantAffineCoordinates
-- original header: public import PaperVerification.ToricTensorFractions

-- original header: @[expose] public section

/-!
# The actual affine charts of a torus product

For an actual affine open immersion `Spec R → X`, its inverse image in
the torus product is literally the spectrum of `k[M] ⊗ R`. The two
projection coordinate maps and the regular-function range in the actual
generic stalk are proved from the genuine pullback and sheaf maps.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory
open PaperVerification.ToricCharacters
open scoped TensorProduct BaseSections Classical

section AffineCoordinates

variable (k : Type u) [CommRing k]
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of k))]
    (R : Type u) [CommRing R] [IsDomain R] [Algebra k R]
    (j : Spec (CommRingCat.of R)⟶X) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k))]

/-- The exact affine coordinate embedding respects the actual base
field structure, as proved by scalar naturality through the chart. -/
def affineCoordinateValueAlgHom : R →ₐ[k] X.functionField where
  __ := affineOpenCoordinateMap (CommRingCat.of R) j
  commutes' c := by
    apply (affineOpenFunctionFieldEquiv (CommRingCat.of R) j).injective
    change affineOpenFunctionFieldEquiv (CommRingCat.of R) j
      (affineOpenCoordinateMap (CommRingCat.of R) j (algebraMap k R c)) = _
    rw [affineOpenFunctionFieldEquiv_coordinateMap]
    change _=affineOpenFunctionFieldEquiv (CommRingCat.of R) j
      (X.germToFunctionField ⊤ (BaseSections.scalarMap k X ⊤ c))
    rw [affineOpenFunctionFieldEquiv_germ_top,
      BaseSections.scalarMap_top_natural k j c, BaseSections.scalarMap_affine_top k R c]
    simp only [Iso.inv_hom_id_apply]

theorem affineCoordinateValueAlgHom_injective :
    Function.Injective (affineCoordinateValueAlgHom k R j) :=
  (openImmersionGlobalToFunctionField_injective j).comp
    (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.injective

end AffineCoordinates

theorem affineOpenCoordinate_range {X : Scheme.{u}} [IsIntegral X]
    (R : CommRingCat.{u}) [IsDomain R] (j : Spec R⟶X) [IsOpenImmersion j] :
    letI : Nonempty (j ''ᵁ (⊤ : (Spec R).Opens)) := openImmersion_image_nonempty j ⊤
    Set.range (affineOpenCoordinateMap R j)=
      Set.range (X.germToFunctionField (j ''ᵁ (⊤ : (Spec R).Opens))) := by
  letI : Nonempty (j ''ᵁ (⊤ : (Spec R).Opens)) := openImmersion_image_nonempty j ⊤
  ext x
  constructor
  · rintro ⟨r,rfl⟩
    exact ⟨affineChartSection R j r,affineChartSection_germ R j r⟩
  · rintro ⟨r,rfl⟩
    refine ⟨(Scheme.ΓSpecIso R).hom ((j.appIso ⊤).hom r),?_⟩
    rw [← affineChartSection_germ]
    congr 1
    simp only [affineChartSection,Iso.hom_inv_id_apply]

section AffineOpen

variable (k : Type u) [CommRing k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] (U : X.Opens) (hU : IsAffineOpen U)

theorem affineOpen_fromSpec_toBase :
    hU.fromSpec≫(X ↘ Spec (CommRingCat.of k))=
      Spec.map (CommRingCat.ofHom (BaseSections.scalarMap k X U)) := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec (X ↘ Spec (CommRingCat.of k))
    (isAffineOpen_top (Spec (CommRingCat.of k))) hU
    (show U ≤ (X ↘ Spec (CommRingCat.of k)) ⁻¹ᵁ ⊤ by simp)
  rw [← h,IsAffineOpen.fromSpec_top,Scheme.isoSpec_Spec_inv,← Spec.map_comp]
  congr 1

theorem affineOpen_fromSpec_isOver :
    hU.fromSpec.IsOver (Spec (CommRingCat.of k)) :=
  ⟨affineOpen_fromSpec_toBase k X U hU⟩

theorem affineOpenCoordinateMap_fromSpec [IsIntegral X] [Nonempty U] (r : Γ(X,U)) :
    affineOpenCoordinateMap Γ(X,U) hU.fromSpec r=X.germToFunctionField U r := by
  letI : Nonempty (hU.fromSpec ⁻¹ᵁ U) := openImmersion_preimage_nonempty hU.fromSpec U
  apply (openImmersionFunctionFieldEquiv hU.fromSpec).injective
  change openImmersionFunctionFieldEquiv hU.fromSpec
    ((openImmersionFunctionFieldEquiv hU.fromSpec).symm
      ((Spec Γ(X,U)).germToFunctionField ⊤ ((Scheme.ΓSpecIso Γ(X,U)).inv r))) = _
  rw [RingEquiv.apply_symm_apply, openImmersionFunctionFieldEquiv_germ,hU.fromSpec_app_self]
  simp only [ConcreteCategory.comp_apply]
  exact (germToFunctionField_restrict (Spec Γ(X,U))
    (eqToHom hU.fromSpec_preimage_self) ((Scheme.ΓSpecIso Γ(X,U)).inv r)).symm

end AffineOpen

section Product

variable (k : Type u) [Field k] (n : ℕ)
    (X : Over (Spec (CommRingCat.of k)))
    (R : Type u) [CommRing R] [Algebra k R]
    (j : Spec (CommRingCat.of R)⟶X.left)
    [IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of k))]

local notation "A" => AddMonoidAlgebra k (Fin n→ℤ)
local notation "G" => splitTorusOver k (Fin n→ℤ)
local notation "Y" => Functor.obj (Over.forget (Spec (CommRingCat.of k))) (G ⊗ X)

/-- The actual affine inverse image, using the literal tensor coordinate
ring and the genuine base-change map of the open immersion. -/
def torusProductAffineChart : Spec (CommRingCat.of (A ⊗[k] R))⟶Y :=
  (pullbackSpecIso k A R).inv≫
    pullback.map (G).hom (Spec.map (CommRingCat.ofHom (algebraMap k R)))
      (G).hom X.hom (𝟙 (G).left) j (𝟙 (Spec (CommRingCat.of k)))
      (by exact (Category.comp_id (G).hom).trans (Category.id_comp (G).hom).symm)
      (by
        have hj := comp_over j (Spec (CommRingCat.of k))
        change j ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k R)) at hj
        exact (Category.comp_id _).trans hj.symm)

@[reassoc] theorem torusProductAffineChart_fst :
    torusProductAffineChart k n X R j≫(fst G X).left=
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] R).toRingHom) := by
  simp only [torusProductAffineChart,Over.fst_left,Category.assoc,pullback.map,
    pullback.lift_fst,Category.comp_id,pullbackSpecIso_inv_fst]
  erw [Category.assoc, pullback.lift_fst]
  exact pullbackSpecIso_inv_fst k A R

@[reassoc] theorem torusProductAffineChart_snd :
    torusProductAffineChart k n X R j≫(snd G X).left=
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : R →ₐ[k] A ⊗[k] R).toRingHom)≫j := by
  simp only [torusProductAffineChart,Over.snd_left,Category.assoc,pullback.map,
    pullback.lift_snd,pullbackSpecIso_inv_snd_assoc]
  erw [Category.assoc, pullback.lift_snd]
  change (pullbackSpecIso k A R).inv ≫
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k A)))
        (Spec.map (CommRingCat.ofHom (algebraMap k R))) ≫ j = _
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun f : Spec (CommRingCat.of (A ⊗[k] R)) ⟶ Spec (CommRingCat.of R) => f ≫ j)
      (pullbackSpecIso_inv_snd k A R))

theorem torusProductAffineChart_isPullback :
    IsPullback (torusProductAffineChart k n X R j)
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : R →ₐ[k] A ⊗[k] R).toRingHom))
      (snd G X).left j := by
  apply IsPullback.of_right (t:=IsPullback.of_hasPullback (G).hom X.hom)
  · have hfst : torusProductAffineChart k n X R j ≫ pullback.fst (G).hom X.hom =
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] R).toRingHom) :=
      torusProductAffineChart_fst k n X R j
    have hj := comp_over j (Spec (CommRingCat.of k))
    change j ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k R)) at hj
    rw [hfst,hj]
    refine IsPullback.of_iso_pullback ⟨?_⟩ (pullbackSpecIso k A R).symm ?_ ?_
    · change Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] R).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap k A)) =
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight : R →ₐ[k] A ⊗[k] R).toRingHom) ≫
            Spec.map (CommRingCat.ofHom (algebraMap k R))
      rw [← Spec.map_comp,← Spec.map_comp]
      congr 1
      ext c
      simp
    · exact pullbackSpecIso_inv_fst k A R
    · exact pullbackSpecIso_inv_snd k A R
  · exact torusProductAffineChart_snd k n X R j

instance torusProductAffineChart_isOpenImmersion :
    IsOpenImmersion (torusProductAffineChart k n X R j) :=
  MorphismProperty.of_isPullback
    (torusProductAffineChart_isPullback k n X R j).flip inferInstance

theorem torusProductAffineChart_opensRange :
    (torusProductAffineChart k n X R j).opensRange=(snd G X).left ⁻¹ᵁ j.opensRange := by
  apply TopologicalSpace.Opens.ext
  simpa only [Set.preimage_univ,Set.image_univ,Scheme.Hom.coe_opensRange,
    Scheme.Hom.coe_preimage] using
    Scheme.image_preimage_eq_of_isPullback
      (torusProductAffineChart_isPullback k n X R j).flip Set.univ

end Product

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.torusProductAffineChart_isPullback
end
end Source_ToricAffineProductCharts
-- END ORIGINAL PaperVerification.ToricAffineProductCharts


-- BEGIN ORIGINAL PaperVerification.ToricProductRationalMap
section Source_ToricProductRationalMap

-- original header: module

-- original header: public import PaperVerification.ToricAffineProductCharts

-- original header: @[expose] public section

/-!
# Actual rational functions on a torus product

The tensor map is defined using the genuine two projections on generic
stalks. Its injectivity is proved on an actual nonempty affine chart,
after clearing finitely many coefficient denominators. For every actual
affine open, its regular-function range is exactly the tensor extension
of the original regular-function range.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory
open PaperVerification.ToricCharacters
open scoped TensorProduct BaseSections Classical

variable (k : Type u) [Field k] (n : ℕ)
    (X : Over (Spec (CommRingCat.of k)))
    [IsIntegral X.left] [IsLocallyNoetherian X.left]

local notation "A" => AddMonoidAlgebra k (Fin n→ℤ)
local notation "G" => splitTorusOver k (Fin n→ℤ)
local notation "Y" => Functor.obj (Over.forget (Spec (CommRingCat.of k))) (G ⊗ X)

local instance coefficientTorusDomain : IsDomain A := torusCoordinateRing_isDomain k n

local instance productRationalIntegral : IsIntegral Y := torusProduct_integral k n X

local instance productRationalOver : (Y).Over (Spec (CommRingCat.of k)) :=
  OverClass.fromOver (G ⊗ X)

instance torusProduct_firstProjection_surjective : Surjective (fst G X).left := by
  letI : Surjective X.hom := by
    constructor
    intro z
    exact ⟨Classical.choice (inferInstance : Nonempty X.left),Subsingleton.elim _ _⟩
  change Surjective (pullback.fst (G).hom X.hom)
  infer_instance

/-- Literal regular torus coordinates inside its actual generic stalk. -/
def torusCoordinateValueAlgHom : A →ₐ[k] (G).left.functionField := by
  let j : Spec (CommRingCat.of A) ⟶ (G).left := 𝟙 (G).left
  letI : IsOpenImmersion j := by change IsOpenImmersion (𝟙 (G).left); infer_instance
  letI : j.IsOver (Spec (CommRingCat.of k)) := by
    constructor
    change (𝟙 (G).left) ≫ (G).hom = (G).hom
    exact Category.id_comp _
  exact affineCoordinateValueAlgHom k A j

/-- The actual product rational embedding: character coordinates are
pulled through the first projection, coefficients through the second. -/
def torusProductRationalMap : A ⊗[k] X.left.functionField →ₐ[k] (Y).functionField :=
  Algebra.TensorProduct.lift
    ((BaseSections.dominantFunctionFieldAlgHom k (fst G X).left).comp
      (torusCoordinateValueAlgHom k n))
    (BaseSections.dominantFunctionFieldAlgHom k (snd G X).left)
    (fun _ _=>Commute.all _ _)

@[simp] theorem torusProductRationalMap_tmul (f : A) (z : X.left.functionField) :
    torusProductRationalMap k n X (f ⊗ₜ[k] z)=
      dominantFunctionFieldMap (fst G X).left (torusCoordinateValueAlgHom k n f)*
        dominantFunctionFieldMap (snd G X).left z := rfl

section AffineChart

variable (R : Type u) [CommRing R] [IsDomain R] [Algebra k R]
    (j : Spec (CommRingCat.of R)⟶X.left)
    [IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of k))]

/-- On an actual affine product chart the abstract tensor formula is
exactly the genuine chart coordinate-to-generic-stalk map. -/
theorem torusProductRationalMap_affineCoordinate (t : A ⊗[k] R) :
    letI := latticeTensor_isDomain k n R
    torusProductRationalMap k n X
        (Algebra.TensorProduct.map (AlgHom.id k A) (affineCoordinateValueAlgHom k R j) t)=
      affineOpenCoordinateMap (CommRingCat.of (A ⊗[k] R))
        (torusProductAffineChart k n X R j) t := by
  letI := latticeTensor_isDomain k n R
  let j₀ : Spec (CommRingCat.of A) ⟶ (G).left := 𝟙 (G).left
  letI : IsOpenImmersion j₀ := by
    change IsOpenImmersion (𝟙 (G).left)
    infer_instance
  induction t using TensorProduct.induction_on with
  | zero =>
      exact (congrArg (torusProductRationalMap k n X)
        (map_zero (Algebra.TensorProduct.map (AlgHom.id k A)
          (affineCoordinateValueAlgHom k R j)))).trans
        ((map_zero (torusProductRationalMap k n X)).trans
          (map_zero (affineOpenCoordinateMap (CommRingCat.of (A ⊗[k] R))
            (torusProductAffineChart k n X R j))).symm)
  | tmul f r =>
      simp only [Algebra.TensorProduct.map_tmul,AlgHom.id_apply,torusProductRationalMap_tmul]
      change dominantFunctionFieldMap (fst G X).left
          (affineOpenCoordinateMap (CommRingCat.of A) j₀ f)*
        dominantFunctionFieldMap (snd G X).left
          (affineOpenCoordinateMap (CommRingCat.of R) j r)=_
      rw [dominantFunctionFieldMap_affineCoordinate (CommRingCat.of A)
        (CommRingCat.of (A ⊗[k] R)) j₀
        (torusProductAffineChart k n X R j) (fst G X).left
        (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] R).toRingHom)
        (by exact (torusProductAffineChart_fst k n X R j).trans (Category.comp_id _).symm),
        dominantFunctionFieldMap_affineCoordinate (CommRingCat.of R)
        (CommRingCat.of (A ⊗[k] R)) j
        (torusProductAffineChart k n X R j) (snd G X).left
        (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : R →ₐ[k] A ⊗[k] R).toRingHom)
        (torusProductAffineChart_snd k n X R j)]
      rw [← map_mul]
      congr 1
      change (f ⊗ₜ[k] (1 : R)) * ((1 : A) ⊗ₜ[k] r) = f ⊗ₜ[k] r
      rw [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]
  | add t v ht hv => simp only [map_add,ht,hv]

theorem torusProductRationalMap_affineCoordinate_range :
    letI := latticeTensor_isDomain k n R
    let l := torusProductAffineChart k n X R j
    letI : Nonempty (l ''ᵁ (⊤ : (Spec (CommRingCat.of (A ⊗[k] R))).Opens)) :=
      openImmersion_image_nonempty l ⊤
    Set.range (fun t : A ⊗[k] R=>torusProductRationalMap k n X
      (Algebra.TensorProduct.map (AlgHom.id k A) (affineCoordinateValueAlgHom k R j) t))=
      Set.range ((Y).germToFunctionField (l ''ᵁ (⊤ : (Spec (CommRingCat.of (A ⊗[k] R))).Opens))) := by
  letI := latticeTensor_isDomain k n R
  simp_rw [torusProductRationalMap_affineCoordinate]
  exact affineOpenCoordinate_range (CommRingCat.of (A ⊗[k] R))
    (torusProductAffineChart k n X R j)

end AffineChart

theorem torusProductRationalMap_injective : Function.Injective (torusProductRationalMap k n X) := by
  obtain ⟨U,hU,hx,hsub⟩ := exists_isAffineOpen_mem_and_subset
    (show genericPoint X.left∈(⊤ : X.left.Opens) from trivial)
  letI : Nonempty U := ⟨⟨genericPoint X.left,hx⟩⟩
  let R := Γ(X.left,U)
  let j := hU.fromSpec
  letI : j.IsOver (Spec (CommRingCat.of k)) := affineOpen_fromSpec_isOver k X.left U hU
  letI : IsFractionRing R X.left.functionField :=
    functionField_isFractionRing_of_isAffineOpen X.left U hU
  letI : IsScalarTower k R X.left.functionField :=
    IsScalarTower.of_algebraMap_eq (fun c=>(BaseSections.germ_scalarMap k U c).symm)
  letI := latticeTensor_isDomain k n R
  letI := latticeTensor_isDomain k n X.left.functionField
  let F := Algebra.TensorProduct.map (AlgHom.id k A)
    (BaseSections.regularValueAlgHom k U)
  have hF (t : A ⊗[k] R) : torusProductRationalMap k n X (F t)=
      affineOpenCoordinateMap (CommRingCat.of (A ⊗[k] R))
        (torusProductAffineChart k n X R j) t := by
    have he : BaseSections.regularValueAlgHom k U=affineCoordinateValueAlgHom k R j := by
      ext r
      exact (affineOpenCoordinateMap_fromSpec X.left U hU r).symm
    rw [show F=Algebra.TensorProduct.map (AlgHom.id k A)
      (affineCoordinateValueAlgHom k R j) from congrArg (Algebra.TensorProduct.map (AlgHom.id k A)) he]
    exact torusProductRationalMap_affineCoordinate k n X R j t
  apply (injective_iff_map_eq_zero _).mpr
  intro w hw
  obtain ⟨d,hd,t,ht⟩ := tensor_exists_common_denominator k A R X.left.functionField w
  change F t=(1 ⊗ₜ[k] X.left.germToFunctionField U d)*w at ht
  have hct : affineOpenCoordinateMap (CommRingCat.of (A ⊗[k] R))
      (torusProductAffineChart k n X R j) t=0 := by
    rw [← hF,ht,map_mul,hw,mul_zero]
  have ht0 : t=0 := by
    apply (openImmersionGlobalToFunctionField_injective
      (torusProductAffineChart k n X R j)).comp
        (Scheme.ΓSpecIso (CommRingCat.of (A ⊗[k] R))).commRingCatIsoToRingEquiv.symm.injective
    change affineOpenCoordinateMap (CommRingCat.of (A ⊗[k] R))
        (torusProductAffineChart k n X R j) t =
      affineOpenCoordinateMap (CommRingCat.of (A ⊗[k] R))
        (torusProductAffineChart k n X R j) 0
    exact hct.trans (map_zero (affineOpenCoordinateMap (CommRingCat.of (A ⊗[k] R))
      (torusProductAffineChart k n X R j))).symm
  have hden : (1 ⊗ₜ[k] X.left.germToFunctionField U d : A ⊗[k] X.left.functionField)≠0 := by
    intro hz
    have hm := congrArg (torusProductRationalMap k n X) hz
    simp only [torusProductRationalMap_tmul,map_one,one_mul,map_zero] at hm
    have hdz : X.left.germToFunctionField U d=0 :=
      (dominantFunctionFieldMap (snd G X).left).injective (hm.trans (map_zero _).symm)
    exact hd (X.left.germToFunctionField_injective U (hdz.trans (map_zero _).symm))
  rw [ht0,map_zero] at ht
  exact (mul_eq_zero.mp ht.symm).resolve_left hden

theorem torusProductRationalMap_regularAffine_range (U : X.left.Opens)
    (hU : IsAffineOpen U) [Nonempty U] :
    letI : Nonempty ((snd G X).left ⁻¹ᵁ U) := dominant_preimage_nonempty (snd G X).left U
    Set.range (fun t : A ⊗[k] Γ(X.left,U)=>torusProductRationalMap k n X
      (Algebra.TensorProduct.map (AlgHom.id k A) (BaseSections.regularValueAlgHom k U) t))=
      Set.range ((Y).germToFunctionField ((snd G X).left ⁻¹ᵁ U)) := by
  letI : Nonempty ((snd G X).left ⁻¹ᵁ U) := dominant_preimage_nonempty (snd G X).left U
  let R := Γ(X.left,U)
  let j := hU.fromSpec
  letI : j.IsOver (Spec (CommRingCat.of k)) := affineOpen_fromSpec_isOver k X.left U hU
  letI := latticeTensor_isDomain k n R
  let l := torusProductAffineChart k n X R j
  have he : BaseSections.regularValueAlgHom k U=affineCoordinateValueAlgHom k R j := by
    ext r
    exact (affineOpenCoordinateMap_fromSpec X.left U hU r).symm
  have hV : l ''ᵁ (⊤ : (Spec (CommRingCat.of (A ⊗[k] R))).Opens)=(snd G X).left ⁻¹ᵁ U := by
    rw [Scheme.Hom.image_top_eq_opensRange,torusProductAffineChart_opensRange,
      hU.opensRange_fromSpec]
  rw [he]
  letI : Nonempty (l ''ᵁ (⊤ : (Spec (CommRingCat.of (A ⊗[k] R))).Opens)) :=
    openImmersion_image_nonempty l ⊤
  have hRange {V W : (Y).Opens} [Nonempty V] [Nonempty W] (h : V=W) :
      Set.range ((Y).germToFunctionField V)=Set.range ((Y).germToFunctionField W) := by
    subst W
    rfl
  exact (torusProductRationalMap_affineCoordinate_range k n X R j).trans
    (hRange hV)

/-- Exact coefficientwise regularity on every affine open, stated in
the actual function field of the actual product scheme. -/
theorem torusProductRationalMap_mem_regularAffine_iff (U : X.left.Opens)
    (hU : IsAffineOpen U) [Nonempty U] (w : A ⊗[k] X.left.functionField) :
    letI : Nonempty ((snd G X).left ⁻¹ᵁ U) := dominant_preimage_nonempty (snd G X).left U
    torusProductRationalMap k n X w∈
      Set.range ((Y).germToFunctionField ((snd G X).left ⁻¹ᵁ U)) ↔
      w∈LinearMap.range (TensorProduct.map (LinearMap.id : A →ₗ[k] A)
        (BaseSections.regularValueAlgHom k U).toLinearMap) := by
  letI : Nonempty ((snd G X).left ⁻¹ᵁ U) := dominant_preimage_nonempty (snd G X).left U
  rw [← torusProductRationalMap_regularAffine_range k n X U hU]
  constructor
  · rintro ⟨t,ht⟩
    exact ⟨t,torusProductRationalMap_injective k n X ht⟩
  · rintro ⟨t,rfl⟩
    exact ⟨t,rfl⟩

section Naturality

variable {Z : Over (Spec (CommRingCat.of k))}
    [IsIntegral Z.left] [IsLocallyNoetherian Z.left]
    (j : Z⟶X) [IsDominant j.left]
    [IsDominant (splitTorusOver k (Fin n→ℤ) ◁ j).left]

theorem torusProductRationalMap_natural (w : A ⊗[k] X.left.functionField) :
    dominantFunctionFieldMap (G ◁ j).left (torusProductRationalMap k n X w)=
      torusProductRationalMap k n Z
        (Algebra.TensorProduct.map (AlgHom.id k A)
          (BaseSections.dominantFunctionFieldAlgHom k j.left) w) := by
  have hfst : (G ◁ j).left≫(fst G X).left=(fst G Z).left := by
    change ((G ◁ j)≫fst G X).left=(fst G Z).left
    simp
  have hsnd : (G ◁ j).left≫(snd G X).left=(snd G Z).left≫j.left := by
    change ((G ◁ j)≫snd G X).left=((snd G Z)≫j).left
    simp
  have hmap {Y₁ Y₂ : Scheme.{u}} [IsIntegral Y₁] [IsIntegral Y₂]
      (f g : Y₁ ⟶ Y₂) [IsDominant f] [IsDominant g] (h : f=g) :
      dominantFunctionFieldMap f=dominantFunctionFieldMap g := by
    subst g
    rfl
  have hfstField :
      (dominantFunctionFieldMap (G ◁ j).left).comp
        (dominantFunctionFieldMap (fst G X).left) =
      dominantFunctionFieldMap (fst G Z).left :=
    (dominantFunctionFieldMap_comp (G ◁ j).left (fst G X).left).symm.trans
      (hmap _ _ hfst)
  have hsndField :
      (dominantFunctionFieldMap (G ◁ j).left).comp
        (dominantFunctionFieldMap (snd G X).left) =
      (dominantFunctionFieldMap (snd G Z).left).comp
        (dominantFunctionFieldMap j.left) :=
    (dominantFunctionFieldMap_comp (G ◁ j).left (snd G X).left).symm.trans
      ((hmap _ _ hsnd).trans
        (dominantFunctionFieldMap_comp (snd G Z).left j.left))
  induction w using TensorProduct.induction_on with
  | zero =>
      exact ((congrArg (dominantFunctionFieldMap (G ◁ j).left)
        (map_zero (torusProductRationalMap k n X))).trans
        (map_zero (dominantFunctionFieldMap (G ◁ j).left))).trans
        ((congrArg (torusProductRationalMap k n Z)
          (map_zero (Algebra.TensorProduct.map (AlgHom.id k A)
            (BaseSections.dominantFunctionFieldAlgHom k j.left)))).trans
          (map_zero (torusProductRationalMap k n Z))).symm
  | tmul f z =>
      simp only [Algebra.TensorProduct.map_tmul,AlgHom.id_apply,torusProductRationalMap_tmul,map_mul]
      change dominantFunctionFieldMap (G ◁ j).left
          (dominantFunctionFieldMap (fst G X).left (torusCoordinateValueAlgHom k n f))*
        dominantFunctionFieldMap (G ◁ j).left
          (dominantFunctionFieldMap (snd G X).left z)=_
      exact congrArg₂ (· * ·)
        (congrArg (fun φ : (G).left.functionField →+* (G ⊗ Z).left.functionField =>
          φ (torusCoordinateValueAlgHom k n f)) hfstField)
        (congrArg (fun φ : X.left.functionField →+* (G ⊗ Z).left.functionField =>
          φ z) hsndField)
  | add w v hw hv => simp only [map_add,hw,hv]

end Naturality

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.torusProductRationalMap_injective
#print axioms PaperVerification.ToricSchemes.torusProductRationalMap_mem_regularAffine_iff
end
end Source_ToricProductRationalMap
-- END ORIGINAL PaperVerification.ToricProductRationalMap


-- BEGIN ORIGINAL PaperVerification.ToricTensorCharacterCoefficients
section Source_ToricTensorCharacterCoefficients

-- original header: module

-- original header: public import PaperVerification.ToricCharacterSubrepresentations
-- original header: public import Mathlib.RingTheory.TensorProduct.Basic

-- original header: @[expose] public section

/-! # Coefficient extraction in the genuine tensor product -/

noncomputable section

namespace PaperVerification.ToricCharacters

open AddMonoidAlgebra
open scoped TensorProduct

variable (k : Type*) [Field k] {M : Type*} [AddCommGroup M]

theorem characterCoefficient_map
    {V W : Type*} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (l : V →ₗ[k] W)
    (m : M) (z : AddMonoidAlgebra k M ⊗[k] V) :
    characterCoefficient k m
      (TensorProduct.map (LinearMap.id : AddMonoidAlgebra k M →ₗ[k] _) l z) =
        l (characterCoefficient k m z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul f v => simp only [TensorProduct.map_tmul,LinearMap.id_apply,
      characterCoefficient_tmul,map_smul]
  | add z w hz hw => simp only [map_add,hz,hw]

theorem characterCoefficient_mem_range
    {V W : Type*} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (l : V →ₗ[k] W)
    (m : M) (z : AddMonoidAlgebra k M ⊗[k] W)
    (hz : z∈(TensorProduct.map
      (LinearMap.id : AddMonoidAlgebra k M →ₗ[k] _) l).range) :
    characterCoefficient k m z∈l.range := by
  obtain ⟨w,rfl⟩ := hz
  exact ⟨characterCoefficient k m w,(characterCoefficient_map k l m w).symm⟩

variable {A : Type*} [CommRing A] [Algebra k A]

theorem characterCoefficient_mul_one_tmul (m : M)
    (z : AddMonoidAlgebra k M ⊗[k] A) (a : A) :
    characterCoefficient k m (z*(1⊗ₜ[k]a)) =
      characterCoefficient k m z*a := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul f b =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul,mul_one,
        characterCoefficient_tmul,smul_mul_assoc]
  | add z w hz hw => simp only [add_mul,map_add,hz,hw]

/-- The coefficient of the actual coaction, after mapping the second
factor to a field and dividing by one genuine rational local frame. -/
theorem characterCoefficient_coaction_ratio
    (ι : AddMonoidAlgebra k M →ₐ[k] A) (f : AddMonoidAlgebra k M)
    (a : A) (m : M) :
    characterCoefficient k m
      ((Algebra.TensorProduct.map (AlgHom.id k _) ι
        (Coalgebra.comul (R:=k) f))*(1⊗ₜ[k]a)) =
          ι (single m (f.coeff m))*a := by
  rw [characterCoefficient_mul_one_tmul]
  change characterCoefficient k m
      (TensorProduct.map (LinearMap.id : AddMonoidAlgebra k M →ₗ[k] _)
        ι.toLinearMap (Coalgebra.comul (R:=k) f))*a = _
  rw [characterCoefficient_map,characterCoefficient_comul]
  rfl

end PaperVerification.ToricCharacters
end
end Source_ToricTensorCharacterCoefficients
-- END ORIGINAL PaperVerification.ToricTensorCharacterCoefficients


