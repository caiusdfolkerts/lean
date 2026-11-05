module

public import PaperVerification.ToricActionGluing
public import PaperVerification.ToricChartActions
public import PaperVerification.ToricFanCharacters

@[expose] public section

/-!
# The actual split-torus action on the glued fan scheme

Every chart action is the spectrum of the character coaction. Its face
inclusions are equivariant, and the actual directed affine open cover
glues these maps into a group-scheme action. The embedded dense torus
inherits its genuine multiplication map.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open MonoidalCategory MonObj
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes

theorem action_extends_mul_comp {C : Type*} [Category C] [MonoidalCategory C]
    (G A B : C) [MonObj G] [ModObj G A] [ModObj G B]
    (f : G ⟶ A) (g : A ⟶ B) [IsModHom G g]
    (hf : μ[G] ≫ f = G ◁ f ≫ γ[G,A]) :
    μ[G] ≫ (f ≫ g) = G ◁ (f ≫ g) ≫ γ[G,B] := by
  have hg : γ[G,A] ≫ g = G ◁ g ≫ γ[G,B] :=
    IsModHom.smul_hom (A := G) (f := g)
  calc
    μ[G] ≫ (f ≫ g) = (μ[G] ≫ f) ≫ g := (Category.assoc _ _ _).symm
    _ = (G ◁ f ≫ γ[G,A]) ≫ g := congrArg (fun h => h ≫ g) hf
    _ = G ◁ f ≫ (γ[G,A] ≫ g) := Category.assoc _ _ _
    _ = G ◁ f ≫ (G ◁ g ≫ γ[G,B]) := congrArg (fun h => G ◁ f ≫ h) hg
    _ = (G ◁ f ≫ G ◁ g) ≫ γ[G,B] := (Category.assoc _ _ _).symm
    _ = G ◁ (f ≫ g) ≫ γ[G,B] :=
      congrArg (fun h => h ≫ γ[G,B]) (whiskerLeft_comp G f g).symm

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [CommRing k]

instance coneChart_isOver (s : Finset (Lattice n)) :
    (coneChart k s).Over (Spec (CommRingCat.of k)) := by
  change (monoidChartScheme k (dualConeMonoid s)).Over _
  infer_instance

instance coneChartFaceMap_isOver {s t : Finset (Lattice n)} (hts : t ⊆ s) :
    (coneChartFaceMap k hts).IsOver (Spec (CommRingCat.of k)) := by
  change (monoidChartSpecMap k (dualConeMonoid_antitone hts)).IsOver _
  infer_instance

/-- The actual structure morphism to the field spectrum is glued from
its specified algebra structures on every semigroup chart. -/
def fanSchemeBaseCocone : Cocone («Σ».coneDiagram k) where
  pt := Spec (CommRingCat.of k)
  «ι» := {
    app := fun s => coneChart k s.val ↘ Spec (CommRingCat.of k)
    naturality := by
      intro s t h
      change coneChartFaceMap k (leOfHom h) ≫
        (coneChart k t.val ↘ Spec (CommRingCat.of k)) =
          (coneChart k s.val ↘ Spec (CommRingCat.of k)) ≫ 𝟙 _
      simpa only [Category.comp_id] using
        (comp_over (coneChartFaceMap k (leOfHom h)) (Spec (CommRingCat.of k))) }

def fanSchemeStructureMap : «Σ».fanScheme k ⟶ Spec (CommRingCat.of k) :=
  colimit.desc («Σ».coneDiagram k) («Σ».fanSchemeBaseCocone k)

instance fanScheme_isOver : («Σ».fanScheme k).Over (Spec (CommRingCat.of k)) where
  hom := «Σ».fanSchemeStructureMap k

instance fanChartMap_isOver (s : «Σ».ConeIndex) :
    («Σ».fanChartMap k s).IsOver (Spec (CommRingCat.of k)) where
  comp_over := by
    change colimit.ι («Σ».coneDiagram k) s ≫
      colimit.desc («Σ».coneDiagram k) («Σ».fanSchemeBaseCocone k) = _
    exact colimit.ι_desc («Σ».fanSchemeBaseCocone k) s

instance fanSchemeOpenCover_preorder : Preorder («Σ».fanSchemeOpenCover k).I₀ :=
  inferInstanceAs (Preorder «Σ».ConeIndex)

instance fanSchemeOpenCover_category : Category («Σ».fanSchemeOpenCover k).I₀ :=
  inferInstanceAs (Category «Σ».ConeIndex)

instance fanSchemeOpenCover_isOver :
    («Σ».fanSchemeOpenCover k).Over (Spec (CommRingCat.of k)) where
  over s := coneChart_isOver k s.val
  isOver_map s := «Σ».fanChartMap_isOver k s

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The common-face pullback supplies actual local directedness of the
chosen affine cover, including its residue-field-compatible point lifting. -/
instance fanSchemeOpenCover_locallyDirected : («Σ».fanSchemeOpenCover k).LocallyDirected where
  trans {s t} h := coneChartFaceMap k (leOfHom h)
  trans_id s := coneChartFaceMap_self k s.val
  trans_comp hst htu := (coneChartFaceMap_comp k (leOfHom htu) (leOfHom hst)).symm
  w h := «Σ».fanChartMap_naturality k (leOfHom h)
  directed {s t} x := by
    let l : «Σ».ConeIndex :=
      ⟨t.val ∩ s.val, «Σ».downward t.val t.property _ Finset.inter_subset_left⟩
    let H := «Σ».fanChart_inter_isPullback k t s
    refine ⟨l,homOfLE Finset.inter_subset_right,homOfLE Finset.inter_subset_left,
      H.isoPullback.inv x,?_⟩
    have heq : pullback.lift
        (coneChartFaceMap k (Finset.inter_subset_right : t.val∩s.val ⊆ s.val))
        (coneChartFaceMap k (Finset.inter_subset_left : t.val∩s.val ⊆ t.val))
        ((«Σ».fanChartMap_naturality k (s := l) (t := s)
          Finset.inter_subset_right).trans
            («Σ».fanChartMap_naturality k (s := l) (t := t)
              Finset.inter_subset_left).symm) =
        H.isoPullback.hom := by
      apply pullback.hom_ext <;> simp
    change (pullback.lift
      (coneChartFaceMap k (Finset.inter_subset_right : t.val∩s.val ⊆ s.val))
      (coneChartFaceMap k (Finset.inter_subset_left : t.val∩s.val ⊆ t.val)) _)
        (H.isoPullback.inv x) = x
    have hpoint := congrArg
      (fun f : coneChart k (t.val∩s.val) ⟶
        pullback («Σ».fanChartMap k s) («Σ».fanChartMap k t) =>
          f (H.isoPullback.inv x)) heq
    have hcancel := congrArg
      (fun f : pullback («Σ».fanChartMap k s) («Σ».fanChartMap k t) ⟶
        pullback («Σ».fanChartMap k s) («Σ».fanChartMap k t) => f x)
      H.isoPullback.inv_hom_id
    change H.isoPullback.hom (H.isoPullback.inv x) = x at hcancel
    exact hpoint.trans hcancel
  property_trans {s t} h :=
    «Σ».coneChartFaceMap_isOpenImmersion k t.val s.val t.property (leOfHom h)

abbrev fanSchemeOver : Over (Spec (CommRingCat.of k)) :=
  («Σ».fanScheme k).asOver (Spec (CommRingCat.of k))

instance coneChart_torusAction (s : Finset (Lattice n)) :
    ModObj (ToricSchemes.splitTorusOver k (Lattice n))
      ((coneChart k s).asOver (Spec (CommRingCat.of k))) := by
  change ModObj (ToricSchemes.splitTorusOver k (Lattice n))
    (monoidChartSchemeOver k (dualConeMonoid s))
  infer_instance

instance coneChartFaceMap_isModHom {s t : Finset (Lattice n)} (hts : t ⊆ s) :
    IsModHom (ToricSchemes.splitTorusOver k (Lattice n))
      ((coneChartFaceMap k hts).asOver (Spec (CommRingCat.of k))) := by
  change IsModHom (ToricSchemes.splitTorusOver k (Lattice n))
    (monoidChartSpecMapOver k (dualConeMonoid_antitone hts))
  infer_instance

/-- Genuine action of the split group scheme on the actual glued scheme. -/
instance fanScheme_torusAction :
    ModObj (ToricSchemes.splitTorusOver k (Lattice n)) («Σ».fanSchemeOver k) := by
  letI : ∀ i : («Σ».fanSchemeOpenCover k).I₀,
      ModObj (ToricSchemes.splitTorusOver k (Lattice n))
        (((«Σ».fanSchemeOpenCover k).X i).asOver (Spec (CommRingCat.of k))) :=
    fun i => coneChart_torusAction k i.val
  exact gluedModObj («Σ».fanSchemeOpenCover k)
    (ToricSchemes.splitTorusOver k (Lattice n)) (fun {i j} h => by
      change IsModHom (ToricSchemes.splitTorusOver k (Lattice n))
        ((coneChartFaceMap k (leOfHom h)).asOver (Spec (CommRingCat.of k)))
      exact coneChartFaceMap_isModHom k (leOfHom h))

instance fanChartMap_isModHom (s : «Σ».ConeIndex) :
    IsModHom (ToricSchemes.splitTorusOver k (Lattice n))
      ((«Σ».fanChartMap k s).asOver (Spec (CommRingCat.of k))) := by
  letI : ∀ i : («Σ».fanSchemeOpenCover k).I₀,
      ModObj (ToricSchemes.splitTorusOver k (Lattice n))
        (((«Σ».fanSchemeOpenCover k).X i).asOver (Spec (CommRingCat.of k))) :=
    fun i => coneChart_torusAction k i.val
  exact gluedModObj_chart («Σ».fanSchemeOpenCover k)
    (ToricSchemes.splitTorusOver k (Lattice n)) (fun {i j} h => by
      change IsModHom (ToricSchemes.splitTorusOver k (Lattice n))
        ((coneChartFaceMap k (leOfHom h)).asOver (Spec (CommRingCat.of k)))
      exact coneChartFaceMap_isModHom k (leOfHom h)) s

/-- Actual torus-to-chart morphism, with its specified algebra map. -/
def torusChartMapOver («Σ» : SmoothCompleteFan n) (s : Finset (Lattice n)) :
    ToricSchemes.splitTorusOver k (Lattice n) ⟶
      (coneChart k s).asOver (Spec (CommRingCat.of k)) :=
  torusToSemigroupChartOver k (dualConeMonoid s) ≫
    (monoidChartSchemeOverIso k (dualConeMonoid s)).inv

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc] theorem torusChartMapOver_action (s : Finset (Lattice n)) :
    μ[ToricSchemes.splitTorusOver k (Lattice n)] ≫ «Σ».torusChartMapOver k s =
      ToricSchemes.splitTorusOver k (Lattice n) ◁ «Σ».torusChartMapOver k s ≫
        γ[ToricSchemes.splitTorusOver k (Lattice n),
          (coneChart k s).asOver (Spec (CommRingCat.of k))] := by
  change μ[ToricSchemes.splitTorusOver k (Lattice n)] ≫
      (torusToSemigroupChartOver k (dualConeMonoid s) ≫
        (monoidChartSchemeOverIso k (dualConeMonoid s)).inv) =
    ToricSchemes.splitTorusOver k (Lattice n) ◁
      (torusToSemigroupChartOver k (dualConeMonoid s) ≫
        (monoidChartSchemeOverIso k (dualConeMonoid s)).inv) ≫
      γ[ToricSchemes.splitTorusOver k (Lattice n),
        monoidChartSchemeOver k (dualConeMonoid s)]
  apply action_extends_mul_comp
  simpa only [id_tensorHom] using
    (semigroupChart_action_extends_torus k (dualConeMonoid s)).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem torusChartMapOver_zero :
    («Σ».torusChartMapOver k (∅ : Finset (Lattice n))).left =
      (zeroConeChartIso k n).inv := by
  change Spec.map (CommRingCat.ofHom (monoidChartMap k (dualConeMonoid ∅)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (monoidChartAlgebraEquiv k (dualConeMonoid ∅)).symm.toRingHom) =
    Spec.map (CommRingCat.ofHom (zeroConeChartAlgEquiv k n).toRingHom)
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro f
  exact congrArg Subtype.val
    ((monoidChartAlgebraEquiv k (dualConeMonoid (∅ : Finset (Lattice n)))).apply_symm_apply f)

instance geometricSplitTorus_isOver :
    (PaperVerification.ToricGeometry.splitTorus k n).Over (Spec (CommRingCat.of k)) := by
  change (ToricSchemes.splitTorus k (Lattice n)).Over _
  infer_instance

instance torusOpenMap_isOver :
    («Σ».torusOpenMap k).IsOver (Spec (CommRingCat.of k)) := by
  change («Σ».fanChartMap k «Σ».zeroConeIndex).IsOver _
  exact «Σ».fanChartMap_isOver k «Σ».zeroConeIndex

instance splitTorusOpenMap_isOver :
    («Σ».splitTorusOpenMap k).IsOver (Spec (CommRingCat.of k)) := by
  constructor
  change ((zeroConeChartIso k n).inv ≫ «Σ».torusOpenMap k) ≫
      («Σ».fanScheme k ↘ Spec (CommRingCat.of k)) = _
  rw [Category.assoc,comp_over]
  exact (congrArg (fun f => f ≫ (coneChart k (∅ : Finset (Lattice n)) ↘
    Spec (CommRingCat.of k))) («Σ».torusChartMapOver_zero k).symm).trans
      (Over.w («Σ».torusChartMapOver k ∅))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The global action restricts to the actual torus multiplication.
This equality is over Spec(k), not just on k-rational points. -/
theorem fanScheme_action_extends_torus :
    μ[ToricSchemes.splitTorusOver k (Lattice n)] ≫
        («Σ».splitTorusOpenMap k).asOver (Spec (CommRingCat.of k)) =
      ToricSchemes.splitTorusOver k (Lattice n) ◁
        («Σ».splitTorusOpenMap k).asOver (Spec (CommRingCat.of k)) ≫
          γ[ToricSchemes.splitTorusOver k (Lattice n),«Σ».fanSchemeOver k] := by
  have hmap : («Σ».splitTorusOpenMap k).asOver (Spec (CommRingCat.of k)) =
      «Σ».torusChartMapOver k ∅ ≫
        («Σ».fanChartMap k «Σ».zeroConeIndex).asOver (Spec (CommRingCat.of k)) := by
    apply Over.OverMorphism.ext
    change (zeroConeChartIso k n).inv ≫ «Σ».torusOpenMap k =
      («Σ».torusChartMapOver k ∅).left ≫ «Σ».fanChartMap k «Σ».zeroConeIndex
    rw [«Σ».torusChartMapOver_zero]
    rfl
  erw [hmap]
  exact action_extends_mul_comp
    (ToricSchemes.splitTorusOver k (Lattice n))
    ((coneChart k ∅).asOver (Spec (CommRingCat.of k))) («Σ».fanSchemeOver k)
    («Σ».torusChartMapOver k ∅)
    ((«Σ».fanChartMap k «Σ».zeroConeIndex).asOver (Spec (CommRingCat.of k)))
    («Σ».torusChartMapOver_action k ∅)

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.fanScheme_torusAction
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.fanScheme_action_extends_torus
