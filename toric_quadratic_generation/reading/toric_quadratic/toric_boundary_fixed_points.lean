module

public import PaperVerification.ToricBoundaryComponents
public import Mathlib.Topology.Sober
public import Mathlib.Order.KrullDimension

@[expose] public section

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
