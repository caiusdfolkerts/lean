module

public import PaperVerification.ToricChartCoaction
public import PaperVerification.ToricFanAction
public import PaperVerification.ToricOrbitClosedImmersion

@[expose] public section

/-!
# Genuine torus invariance of the actual orbit closed immersion

The quotient torus is acted on through the homomorphism induced by the
saturated inclusion of its character lattice. The chart quotient kills
exactly the characters positive on the orbit cone. Its displayed coaction
identity is transported to actual affine schemes and then glued along the
actual open cover. The resulting equivariance is an equality of morphisms
over Spec(k), including arbitrary test schemes.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open MonoidalCategory MonObj
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped TensorProduct

variable {n : ℕ} (k : Type u) [CommRing k]
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))

/-- The actual pullback of characters along the quotient-torus map. -/
def orbitTorusCharacterMap :
    AddMonoidAlgebra k (Lattice (n-I.card)) →ₐ[k] AddMonoidAlgebra k (Lattice n) :=
  (AddMonoidAlgebra.mapDomainBialgHom k
    (faceTangentLattice b I).toAddMonoidHom).toAlgHom

@[simp] theorem orbitTorusCharacterMap_single (m : Lattice (n-I.card)) (a : k) :
    orbitTorusCharacterMap k b I (AddMonoidAlgebra.single m a) =
      AddMonoidAlgebra.single (faceTangentLattice b I m) a :=
  AddMonoidAlgebra.mapDomainBialgHom_single (R := k) _ m a

/-- The quotient map of actual split group schemes. -/
def orbitTorusMapOver :
    ToricSchemes.splitTorusOver k (Lattice n) ⟶
      ToricSchemes.splitTorusOver k (Lattice (n-I.card)) :=
  (algSpec (CommRingCat.of k)).map
    (CommAlgCat.ofHom (orbitTorusCharacterMap k b I)).op

instance orbitTorusMapOver_isMonHom : IsMonHom (orbitTorusMapOver k b I) := by
  change IsMonHom (((bialgSpec (CommRingCat.of k)).map
    (CommBialgCat.ofHom (AddMonoidAlgebra.mapDomainBialgHom k
      (faceTangentLattice b I).toAddMonoidHom)).op).hom)
  infer_instance

/-- The quotient of a chart commutes with the genuine character
coactions, including the characters sent to zero. -/
theorem orbitQuotientAlgebraMap_coaction
    (s : Finset (Lattice n)) (hIs : I.image b⊆s) :
    (Algebra.TensorProduct.map
        (AlgHom.id k (AddMonoidAlgebra k (Lattice n)))
        (orbitQuotientAlgebraMap k b I s hIs)).comp
      (monoidChartCoaction k (dualConeMonoid s)) =
    (Algebra.TensorProduct.map (orbitTorusCharacterMap k b I)
        (AlgHom.id k (monoidChartAlgebra k
          (dualConeMonoid (orbitQuotientCone b I s))))).comp
      ((monoidChartCoaction k (dualConeMonoid (orbitQuotientCone b I s))).comp
        (orbitQuotientAlgebraMap k b I s hIs)) := by
  classical
  apply chartAlgHom_ext_characters
  intro m hm
  by_cases hann : ∀ u∈I.image b,integerPairing u m=0
  · have hproj : faceCharacterProjection b I m∈
        dualConeMonoid (orbitQuotientCone b I s) :=
      faceCharacterProjection_mem_quotientDualCone b I s ⟨⟨m,hm⟩,hann⟩
    have hmap : orbitQuotientAlgebraMap k b I s hIs
        (chartCharacter k (dualConeMonoid s) m hm) =
          chartCharacter k (dualConeMonoid (orbitQuotientCone b I s))
            (faceCharacterProjection b I m) hproj := by
      apply Subtype.ext
      rw [orbitQuotientAlgebraMap_character,dif_pos hann]
      rfl
    simp only [AlgHom.comp_apply,monoidChartCoaction_character,
      Algebra.TensorProduct.map_tmul,AlgHom.id_apply,hmap,
      orbitTorusCharacterMap_single,faceTangentLattice_projection b I m hann]
  · have hmap : orbitQuotientAlgebraMap k b I s hIs
        (chartCharacter k (dualConeMonoid s) m hm) = 0 := by
      apply Subtype.ext
      rw [orbitQuotientAlgebraMap_character,dif_neg hann]
      rfl
    simp only [AlgHom.comp_apply,monoidChartCoaction_character,
      Algebra.TensorProduct.map_tmul,AlgHom.id_apply,hmap,map_zero,
      TensorProduct.tmul_zero]

instance orbitQuotientChartMap_isOver
    (s : Finset (Lattice n)) (hIs : I.image b⊆s) :
    (orbitQuotientChartMap k b I s hIs).IsOver (Spec (CommRingCat.of k)) := by
  exact ⟨((algSpec (CommRingCat.of k)).map
    (CommAlgCat.ofHom (orbitQuotientAlgebraMap k b I s hIs)).op).w⟩

/-- The actual affine orbit chart map intertwines the two group-scheme
actions through the actual quotient-torus homomorphism. -/
theorem orbitQuotientChartMap_action
    (s : Finset (Lattice n)) (hIs : I.image b⊆s) :
    ToricSchemes.splitTorusOver k (Lattice n) ◁
        (orbitQuotientChartMap k b I s hIs).asOver (Spec (CommRingCat.of k)) ≫
      γ[ToricSchemes.splitTorusOver k (Lattice n),
        (coneChart k s).asOver (Spec (CommRingCat.of k))] =
    orbitTorusMapOver k b I ▷
        (coneChart k (orbitQuotientCone b I s)).asOver (Spec (CommRingCat.of k)) ≫
      γ[ToricSchemes.splitTorusOver k (Lattice (n-I.card)),
        (coneChart k (orbitQuotientCone b I s)).asOver (Spec (CommRingCat.of k))] ≫
        (orbitQuotientChartMap k b I s hIs).asOver (Spec (CommRingCat.of k)) := by
  let G := ToricSchemes.splitTorusOver k (Lattice n)
  let Q := ToricSchemes.splitTorusOver k (Lattice (n-I.card))
  let U := monoidChartSchemeOver k (dualConeMonoid (orbitQuotientCone b I s))
  let V := monoidChartSchemeOver k (dualConeMonoid s)
  let ρ : G ⟶ Q := orbitTorusMapOver k b I
  let q : U ⟶ V := (algSpec (CommRingCat.of k)).map
    (CommAlgCat.ofHom (orbitQuotientAlgebraMap k b I s hIs)).op
  change G ◁ q ≫ γ[G,V] = ρ ▷ U ≫ γ[Q,U] ≫ q
  have h₁ : G ◁ q ≫ γ[G,V] = G ◁ q ≫ affineCoactionMorphism k
      (monoidChartCoaction k (dualConeMonoid s)) :=
    congrArg (fun h : G ⊗ V ⟶ V => G ◁ q ≫ h)
      (monoidChart_action_coaction k (dualConeMonoid s))
  have h₂ : G ◁ q ≫ affineCoactionMorphism k
      (monoidChartCoaction k (dualConeMonoid s)) =
      ρ ▷ U ≫ affineCoactionMorphism k
        (monoidChartCoaction k (dualConeMonoid (orbitQuotientCone b I s))) ≫ q :=
    affineCoaction_intertwining k (orbitTorusCharacterMap k b I)
      (orbitQuotientAlgebraMap k b I s hIs)
      (monoidChartCoaction k (dualConeMonoid s))
      (monoidChartCoaction k (dualConeMonoid (orbitQuotientCone b I s)))
      (orbitQuotientAlgebraMap_coaction k b I s hIs)
  have h₃ : ρ ▷ U ≫ affineCoactionMorphism k
      (monoidChartCoaction k (dualConeMonoid (orbitQuotientCone b I s))) ≫ q =
      ρ ▷ U ≫ γ[Q,U] ≫ q :=
    congrArg (fun h : Q ⊗ U ⟶ U => ρ ▷ U ≫ h ≫ q)
      (monoidChart_action_coaction k
        (dualConeMonoid (orbitQuotientCone b I s))).symm
  exact h₁.trans (h₂.trans h₃)

namespace SmoothCompleteFan

variable («Σ» : SmoothCompleteFan n) (hF : I.image b∈«Σ».cones)

instance orbitClosureMap_isOver :
    («Σ».orbitClosureMap k b I hF).IsOver (Spec (CommRingCat.of k)) where
  comp_over := by
    apply ((«Σ».completeQuotientStarFan b I hF).fanSchemeOpenCover k).hom_ext
    intro t
    obtain ⟨s,rfl⟩ := «Σ».orbitConeQuotientIndex_surjective b I hF t
    let U := coneChart k (orbitQuotientCone b I s.val)
    let V := coneChart k s.val
    let Z := («Σ».completeQuotientStarFan b I hF).fanScheme k
    let j : U ⟶ Z := («Σ».completeQuotientStarFan b I hF).fanChartMap k
      («Σ».orbitConeQuotientIndex b I hF s)
    let i : V ⟶ «Σ».fanScheme k := «Σ».fanChartMap k ⟨s.val,s.property.1⟩
    let q : U ⟶ V := orbitQuotientChartMap k b I s.val s.property.2
    let f : Z ⟶ «Σ».fanScheme k := «Σ».orbitClosureMap k b I hF
    have hj : j ≫ f = q ≫ i := «Σ».orbitClosureMap_chart k b I hF s
    have hjbase : j ≫ (Z ↘ Spec (CommRingCat.of k)) =
        (U ↘ Spec (CommRingCat.of k)) :=
      comp_over ((«Σ».completeQuotientStarFan b I hF).fanChartMap k
        («Σ».orbitConeQuotientIndex b I hF s)) (Spec (CommRingCat.of k))
    have hibase : i ≫ («Σ».fanScheme k ↘ Spec (CommRingCat.of k)) =
        (V ↘ Spec (CommRingCat.of k)) :=
      comp_over («Σ».fanChartMap k ⟨s.val,s.property.1⟩) (Spec (CommRingCat.of k))
    have hqbase : q ≫ (V ↘ Spec (CommRingCat.of k)) =
        (U ↘ Spec (CommRingCat.of k)) :=
      comp_over (orbitQuotientChartMap k b I s.val s.property.2) (Spec (CommRingCat.of k))
    change j ≫ (f ≫ («Σ».fanScheme k ↘ Spec (CommRingCat.of k))) =
      j ≫ (Z ↘ Spec (CommRingCat.of k))
    calc
      _ = (j ≫ f) ≫ («Σ».fanScheme k ↘ Spec (CommRingCat.of k)) :=
        (Category.assoc _ _ _).symm
      _ = (q ≫ i) ≫ («Σ».fanScheme k ↘ Spec (CommRingCat.of k)) :=
        congrArg (fun h : U ⟶ «Σ».fanScheme k =>
          h ≫ («Σ».fanScheme k ↘ Spec (CommRingCat.of k))) hj
      _ = q ≫ (i ≫ («Σ».fanScheme k ↘ Spec (CommRingCat.of k))) :=
        Category.assoc _ _ _
      _ = q ≫ (V ↘ Spec (CommRingCat.of k)) :=
        congrArg (fun h : V ⟶ Spec (CommRingCat.of k) => q ≫ h) hibase
      _ = (U ↘ Spec (CommRingCat.of k)) := hqbase
      _ = _ := hjbase.symm

@[reassoc] theorem orbitClosureMap_chart_over (s : «Σ».OrbitConeIndex b I) :
    ((«Σ».completeQuotientStarFan b I hF).fanChartMap k
        («Σ».orbitConeQuotientIndex b I hF s)).asOver (Spec (CommRingCat.of k)) ≫
      («Σ».orbitClosureMap k b I hF).asOver (Spec (CommRingCat.of k)) =
    (orbitQuotientChartMap k b I s.val s.property.2).asOver (Spec (CommRingCat.of k)) ≫
      («Σ».fanChartMap k ⟨s.val,s.property.1⟩).asOver (Spec (CommRingCat.of k)) := by
  apply Over.OverMorphism.ext
  exact «Σ».orbitClosureMap_chart k b I hF s

/-- The actual orbit closed immersion is equivariant. This statement
holds as an equality over Spec(k), not only on rational points. -/
theorem orbitClosureMap_action :
    ToricSchemes.splitTorusOver k (Lattice n) ◁
        («Σ».orbitClosureMap k b I hF).asOver (Spec (CommRingCat.of k)) ≫
      γ[ToricSchemes.splitTorusOver k (Lattice n),«Σ».fanSchemeOver k] =
    orbitTorusMapOver k b I ▷
        («Σ».completeQuotientStarFan b I hF).fanSchemeOver k ≫
      γ[ToricSchemes.splitTorusOver k (Lattice (n-I.card)),
        («Σ».completeQuotientStarFan b I hF).fanSchemeOver k] ≫
        («Σ».orbitClosureMap k b I hF).asOver (Spec (CommRingCat.of k)) := by
  let Γ := «Σ».completeQuotientStarFan b I hF
  let G := ToricSchemes.splitTorusOver k (Lattice n)
  let Q := ToricSchemes.splitTorusOver k (Lattice (n-I.card))
  let X := Γ.fanSchemeOver k
  let Y := «Σ».fanSchemeOver k
  let ρ : G ⟶ Q := orbitTorusMapOver k b I
  let f : X ⟶ Y := («Σ».orbitClosureMap k b I hF).asOver (Spec (CommRingCat.of k))
  apply tensorCover_hom_ext (Γ.fanSchemeOpenCover k) G Y
  intro t
  obtain ⟨s,rfl⟩ := «Σ».orbitConeQuotientIndex_surjective b I hF t
  let U := monoidChartSchemeOver k
    (dualConeMonoid (orbitQuotientCone b I s.val))
  let V := monoidChartSchemeOver k (dualConeMonoid s.val)
  let j : U ⟶ X := (Γ.fanChartMap k
    («Σ».orbitConeQuotientIndex b I hF s)).asOver (Spec (CommRingCat.of k))
  let i : V ⟶ Y := («Σ».fanChartMap k ⟨s.val,s.property.1⟩).asOver
    (Spec (CommRingCat.of k))
  let q : U ⟶ V := (orbitQuotientChartMap k b I s.val s.property.2).asOver
    (Spec (CommRingCat.of k))
  letI : IsModHom G i := «Σ».fanChartMap_isModHom k ⟨s.val,s.property.1⟩
  letI : IsModHom Q j := Γ.fanChartMap_isModHom k
    («Σ».orbitConeQuotientIndex b I hF s)
  have hj : j ≫ f = q ≫ i := «Σ».orbitClosureMap_chart_over k b I hF s
  have hi_action : γ[G,V] ≫ i = G ◁ i ≫ γ[G,Y] :=
    IsModHom.smul_hom (A := G) (f := i)
  have hj_action : γ[Q,U] ≫ j = Q ◁ j ≫ γ[Q,X] :=
    IsModHom.smul_hom (A := Q) (f := j)
  have hq_action : G ◁ q ≫ γ[G,V] = ρ ▷ U ≫ γ[Q,U] ≫ q :=
    orbitQuotientChartMap_action k b I s.val s.property.2
  change G ◁ j ≫ (G ◁ f ≫ γ[G,Y]) =
    G ◁ j ≫ (ρ ▷ X ≫ γ[Q,X] ≫ f)
  calc
    _ = (G ◁ j ≫ G ◁ f) ≫ γ[G,Y] := (Category.assoc _ _ _).symm
    _ = G ◁ (j ≫ f) ≫ γ[G,Y] :=
      congrArg (fun h : G ⊗ U ⟶ G ⊗ Y => h ≫ γ[G,Y])
        (whiskerLeft_comp G j f).symm
    _ = G ◁ (q ≫ i) ≫ γ[G,Y] :=
      congrArg (fun h : U ⟶ Y => G ◁ h ≫ γ[G,Y]) hj
    _ = (G ◁ q ≫ G ◁ i) ≫ γ[G,Y] :=
      congrArg (fun h : G ⊗ U ⟶ G ⊗ Y => h ≫ γ[G,Y])
        (whiskerLeft_comp G q i)
    _ = G ◁ q ≫ (G ◁ i ≫ γ[G,Y]) := Category.assoc _ _ _
    _ = G ◁ q ≫ (γ[G,V] ≫ i) :=
      congrArg (fun h : G ⊗ V ⟶ Y => G ◁ q ≫ h) hi_action.symm
    _ = (G ◁ q ≫ γ[G,V]) ≫ i := (Category.assoc _ _ _).symm
    _ = (ρ ▷ U ≫ γ[Q,U] ≫ q) ≫ i :=
      congrArg (fun h : G ⊗ U ⟶ V => h ≫ i) hq_action
    _ = ρ ▷ U ≫ γ[Q,U] ≫ (q ≫ i) := by simp only [Category.assoc]
    _ = ρ ▷ U ≫ γ[Q,U] ≫ (j ≫ f) :=
      congrArg (fun h : U ⟶ Y => ρ ▷ U ≫ γ[Q,U] ≫ h) hj.symm
    _ = ρ ▷ U ≫ (γ[Q,U] ≫ j) ≫ f := by simp only [Category.assoc]
    _ = ρ ▷ U ≫ (Q ◁ j ≫ γ[Q,X]) ≫ f :=
      congrArg (fun h : Q ⊗ U ⟶ X => ρ ▷ U ≫ h ≫ f) hj_action
    _ = (ρ ▷ U ≫ Q ◁ j) ≫ γ[Q,X] ≫ f := by simp only [Category.assoc]
    _ = (G ◁ j ≫ ρ ▷ X) ≫ γ[Q,X] ≫ f :=
      congrArg (fun h : G ⊗ U ⟶ Q ⊗ X => h ≫ γ[Q,X] ≫ f)
        (whisker_exchange ρ j).symm
    _ = _ := by simp only [Category.assoc]

/-- The original torus acts on the quotient-star scheme through its
actual quotient homomorphism. Kept explicit to avoid competing instances
for the quotient torus's own action. -/
def orbitClosureSourceAction :
    ModObj (ToricSchemes.splitTorusOver k (Lattice n))
      ((«Σ».completeQuotientStarFan b I hF).fanSchemeOver k) :=
  Mod.scalarRestriction (orbitTorusMapOver k b I)
    ((«Σ».completeQuotientStarFan b I hF).fanSchemeOver k)

/-- The already-proved closed immersion identifies an invariant closed
subscheme, with invariance witnessed by an actual group-scheme action. -/
theorem orbitClosureMap_equivariant :
    letI := «Σ».orbitClosureSourceAction k b I hF
    IsModHom (ToricSchemes.splitTorusOver k (Lattice n))
      ((«Σ».orbitClosureMap k b I hF).asOver (Spec (CommRingCat.of k))) := by
  letI := «Σ».orbitClosureSourceAction k b I hF
  constructor
  exact («Σ».orbitClosureMap_action k b I hF).symm

end SmoothCompleteFan
end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.orbitClosureMap_action
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.orbitClosureMap_equivariant
