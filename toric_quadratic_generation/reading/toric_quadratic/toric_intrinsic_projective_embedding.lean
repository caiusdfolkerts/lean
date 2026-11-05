module

public import PaperVerification.ToricAmpleProjectiveEmbedding
public import PaperVerification.ToricSectionSpanningEmbedding
public import PaperVerification.ToricIntrinsicPowerCharacters

@[expose] public section

/-!
# A genuine finite character embedding of an intrinsic smooth toric scheme

The argument starts with an arbitrary actual ample Cartier sheaf. Its
proved rational normalization preserves ampleness. Denominator clearing
constructs a finite projective embedding, and the genuine section
coaction supplies a finite character family spanning those sections.
The graded substitution theorem preserves the closed immersion.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

open AlgebraicGeometry CategoryTheory TopologicalSpace
open MonoidalCategory
open scoped Classical BaseSections

variable {k : Type u} [Field k] {n : ℕ}
    {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n→ℤ)) X]
    [IsIntegral X.left] [Smooth X.hom] [IsProper X.hom]
    (T : SplitToricEmbedding k n X)

/-- An actual finite character-valued section system defining a genuine
closed immersion of the original scheme into polynomial projective space.
The character equation retains the actual dense-torus function-field map. -/
theorem exists_character_projective_embedding
    (D : CartierData X.left) (hD : D.IsAmple) :
    ∃ (C : RationalCartierCocycle X.left)
      (F : Finset (Fin n→ℤ)) (e : ULift.{u} F→Γ(C.sheaf,⊤)),
      (∀ m : ULift.{u} F,C.toCartierData.sectionValue ⊤ (e m)=
        openTorusRationalAlgHom k n X.left T.torus.left
          (AddMonoidAlgebra.single m.down.val (1:k))) ∧
      ∃ hcover : (⨆ m : ULift.{u} F,C.nonvanishingOpen (e m))=⊤,
        IsClosedImmersion (C.sectionProjectiveMap k e hcover) := by
  letI : IsProper (X.left ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (IsProper X.hom)
  letI : LocallyOfFiniteType (X.left ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (LocallyOfFiniteType X.hom)
  let E := torusNormalizedCartier k n X.left T.torus.left D
  have hE : E.IsAmple :=
    (torusNormalizedCartier_isAmple_iff k n X.left T.torus.left D).mpr hD
  let C₀ := E.localCocycle
  letI : CompactSpace X.left := hE.1
  have hC₀ : C₀.HasUnitFramesOn T.torusOpen :=
    torusNormalizedCartier_unitFrames k n X.left T.torus.left D
  obtain ⟨a,ha,I,hI,s,hnonempty,haff,hcover⟩ :=
    (show C₀.IsAmple from hE).exists_common_power_nonempty_affine_cover
  letI : Fintype I := hI
  obtain ⟨b,hb,J,hJ,t,chooseChart,ht,hall,hchosen,haff',hgen⟩ :=
    (C₀.pow a).exists_power_chart_generators k s hnonempty haff hcover
  letI : Fintype J := hJ
  let C := (C₀.pow a).pow b
  have hC : C.toCartierData.localCocycle.HasUnitFramesOn T.torusOpen :=
    ((hC₀.pow a).pow b).of_equivalent C.toCartierData.localCocycle
      C.toCartierData.equivalent_localCocycle
  obtain ⟨F,e₀,he₀,hspan₀⟩ := T.exists_finite_torus_eigensections_of_unitFrames
    C.toCartierData hC t
  let e : ULift.{u} F→Γ(C.sheaf,⊤) := fun m => e₀ m.down
  have hrange : Set.range e = Set.range e₀ := by
    ext q
    constructor
    · rintro ⟨m,rfl⟩
      exact ⟨m.down,rfl⟩
    · rintro ⟨m,rfl⟩
      exact ⟨ULift.up m,rfl⟩
  have hspan (i : J) : t i ∈ Submodule.span k (Set.range e) := by
    rw [hrange]
    exact hspan₀ i
  have hrepr (i : J) : ∃ c : ULift.{u} F→₀k,Finsupp.linearCombination k e c=t i := by
    simpa only [Finsupp.linearCombination_apply] using
      (Finsupp.mem_span_range_iff_exists_finsupp.mp (hspan i))
  choose c hc using hrepr
  have hnew : (⨆ m : ULift.{u} F,C.nonvanishingOpen (e m))=⊤ :=
    C.nonvanishing_cover_of_spans k t e hall (fun i=>⟨c i,hc i⟩)
  refine ⟨C,F,e,(fun m=>(he₀ m.down).symm),hnew,?_⟩
  exact C.sectionProjectiveMap_isClosedImmersion_of_spanning_chartGenerators
    k t e c hc hnew chooseChart hchosen haff' hgen

end PaperVerification.ToricSchemes.SplitToricEmbedding

#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.exists_character_projective_embedding
