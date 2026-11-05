module

public import Continuation.Divisor.InvariantCurves
public import Continuation.Runtime.GroupActionRestriction
public import Continuation.Runtime.GroupActionInvariantPreimage
public import Continuation.Runtime.GroupActionSaturation

/-!
# Dense open tori on invariant open subschemes

Restricting to an invariant open containing the torus preserves the actual
split torus embedding. The saturation of every nonempty open contains that
whole torus, even over a finite field. The latter fact is proved using points
of actual scheme fibre products, with no rational-point assumption.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

variable {k : Type u} [Field k] {n : ℕ}
    {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n → ℤ)) X]
    (T : SplitToricEmbedding k n X)

/-- Restrict the actual equivariant dense open immersion to an invariant
open containing its image. The resulting torus is the original torus. -/
def restrictToInvariantOpen (U : X.left.Opens)
    (hU : (γ[splitTorusOver k (Fin n → ℤ),X]).left ⁻¹ᵁ U =
      (snd (splitTorusOver k (Fin n → ℤ)) X).left ⁻¹ᵁ U)
    (hT : T.torusOpen ≤ U) :
    letI := GroupAction.restrictedModObj X (splitTorusOver k (Fin n → ℤ)) U hU
    SplitToricEmbedding k n (GroupAction.openOver X U) := by
  let G := splitTorusOver k (Fin n → ℤ)
  letI := GroupAction.restrictedModObj X G U hU
  let i := GroupAction.openInclusion X U
  let j : G ⟶ GroupAction.openOver X U :=
    GroupAction.openLift X U T.torus hT
  have hj : j ≫ i = T.torus := GroupAction.openLift_inclusion X U T.torus hT
  have hjleft : j.left ≫ U.ι = T.torus.left := congrArg (fun f => f.left) hj
  refine ⟨j, ?_, ?_, ?_⟩
  · haveI : IsOpenImmersion (j.left ≫ U.ι) := hjleft.symm ▸ T.open_immersion
    exact IsOpenImmersion.of_comp j.left U.ι
  · have hpre : Dense (U.ι ⁻¹' Set.range T.torus.left) :=
      T.dense.preimage U.ι.isOpenEmbedding.isOpenMap
    have hrange : Set.range j.left = U.ι ⁻¹' Set.range T.torus.left := by
      ext x
      constructor
      · rintro ⟨t, rfl⟩
        refine ⟨t, ?_⟩
        exact (congrArg (fun f : G.left ⟶ X.left => f t) hjleft).symm
      · rintro ⟨t, ht⟩
        refine ⟨t, U.ι.isOpenEmbedding.injective ?_⟩
        exact (congrArg (fun f : G.left ⟶ X.left => f t) hjleft).trans ht
    change Dense (Set.range j.left)
    exact hrange.symm ▸ hpre
  · apply (cancel_mono i).mp
    change (μ[G] ≫ j) ≫ i =
      ((G ◁ j) ≫ GroupAction.restrictedAction X G U hU) ≫ i
    rw [Category.assoc, hj, Category.assoc,
      GroupAction.restrictedAction_inclusion,
      ← whiskerLeft_comp_assoc, hj]
    exact T.equivariant

/-- Restriction retains the original torus morphism after the actual open
immersion. This identity also fixes the character-lattice coordinates. -/
@[reassoc (attr := simp)]
theorem restrictToInvariantOpen_torus (U : X.left.Opens)
    (hU : (γ[splitTorusOver k (Fin n → ℤ),X]).left ⁻¹ᵁ U =
      (snd (splitTorusOver k (Fin n → ℤ)) X).left ⁻¹ᵁ U)
    (hT : T.torusOpen ≤ U) :
    letI := GroupAction.restrictedModObj X (splitTorusOver k (Fin n → ℤ)) U hU
    (T.restrictToInvariantOpen U hU hT).torus ≫ GroupAction.openInclusion X U =
      T.torus := by
  letI := GroupAction.restrictedModObj X (splitTorusOver k (Fin n → ℤ)) U hU
  exact GroupAction.openLift_inclusion X U T.torus hT

/-- The restricted dense torus is exactly the inverse image of the
original dense torus; no alternative identification is chosen. -/
theorem restrictToInvariantOpen_torusOpen (U : X.left.Opens)
    (hU : (γ[splitTorusOver k (Fin n → ℤ),X]).left ⁻¹ᵁ U =
      (snd (splitTorusOver k (Fin n → ℤ)) X).left ⁻¹ᵁ U)
    (hT : T.torusOpen ≤ U) :
    letI := GroupAction.restrictedModObj X (splitTorusOver k (Fin n → ℤ)) U hU
    (T.restrictToInvariantOpen U hU hT).torusOpen = U.ι ⁻¹ᵁ T.torusOpen := by
  letI := GroupAction.restrictedModObj X (splitTorusOver k (Fin n → ℤ)) U hU
  let j := (T.restrictToInvariantOpen U hU hT).torus
  have hj : j.left ≫ U.ι = T.torus.left :=
    congrArg (fun f => f.left) (T.restrictToInvariantOpen_torus U hU hT)
  apply TopologicalSpace.Opens.ext
  change Set.range j.left = U.ι ⁻¹' Set.range T.torus.left
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨t, ?_⟩
    exact (congrArg (fun f => f t) hj).symm
  · rintro ⟨t, ht⟩
    refine ⟨t, U.ι.isOpenEmbedding.injective ?_⟩
    exact (congrArg (fun f => f t) hj).trans ht

/-- A nonempty open's saturation contains the entire dense open torus.
The proof lifts arbitrary pairs of scheme points to the fibre product;
those pairs are not required to be rational over the ground field. -/
theorem torusOpen_subset_saturation (U : X.left.Opens) [Nonempty U] :
    (T.torusOpen : Set X.left) ⊆
      GroupAction.saturation (splitTorusOver k (Fin n → ℤ)) X (U : Set X.left) := by
  let G := splitTorusOver k (Fin n → ℤ)
  have hUne : (U : Set X.left).Nonempty := by
    obtain ⟨x⟩ := ‹Nonempty U›
    exact ⟨x.val, x.property⟩
  obtain ⟨u, hu⟩ := T.dense.exists_mem_open U.isOpen hUne
  rintro x ⟨t, rfl⟩
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := G.hom) (g := G.hom) t u (Subsingleton.elim _ _)
  let q : G ⊗ G ⟶ G ⊗ G :=
    lift (fst G G * (snd G G)⁻¹) (snd G G)
  have hq : q ≫ μ[G] = fst G G := by
    change ((fst G G) * (snd G G)⁻¹) * (snd G G) = fst G G
    exact _root_.inv_mul_cancel_right _ _
  let e : G ⊗ G ⟶ G ⊗ X := q ≫ (G ◁ T.torus)
  have hp : e ≫ snd G X = snd G G ≫ T.torus := by
    simp [e, q]
  have ha : e ≫ γ[G,X] = fst G G ≫ T.torus := by
    dsimp only [e]
    rw [Category.assoc, ← T.equivariant, ← Category.assoc, hq]
  refine ⟨e.left z, ?_, ?_⟩
  · change (snd G X).left (e.left z) ∈ U
    have hpz := congrArg (fun f : G ⊗ G ⟶ X => f.left z) hp
    change (snd G X).left (e.left z) = T.torus.left ((snd G G).left z) at hpz
    rw [hpz]
    change T.torus.left (pullback.snd G.hom G.hom z) ∈ U
    rwa [hz₂]
  · have haz := congrArg (fun f : G ⊗ G ⟶ X => f.left z) ha
    change (γ[G,X]).left (e.left z) = T.torus.left ((fst G G).left z) at haz
    rw [haz]
    change T.torus.left (pullback.fst G.hom G.hom z) = T.torus.left t
    rw [hz₁]

end PaperVerification.ToricSchemes.SplitToricEmbedding

#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.restrictToInvariantOpen
#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.torusOpen_subset_saturation
