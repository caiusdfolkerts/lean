module

public import PaperVerification.ToricMonomialImageComparison
public import PaperVerification.ToricIntrinsicProjectiveEmbedding
public import PaperVerification.ToricSmoothMonomialFan

@[expose] public section

/-!
# Fan reconstruction from an intrinsic smooth projective toric scheme

The hypotheses are the ordinary smooth and proper structural morphisms,
an actual dense equivariant open split torus, and an actual ample Cartier
sheaf. Character sections are obtained from the proved section coaction.
Their genuine projective closed immersion is identified with the genuine
monomial Proj by equality of kernel ideal sheaves. Ordinary smoothness
then reconstructs unimodular affine semigroups and the complete normal
fan. The result is an actual scheme isomorphism preserving the field and
the original torus; no fan classification is assumed as a premise.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

open AlgebraicGeometry CategoryTheory MonoidalCategory
open PaperVerification.ToricCharacters PaperVerification.ToricGeometry
open scoped Classical BaseSections

variable {k : Type u} [Field k] {n : ℕ}
    {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n→ℤ)) X]
    [IsIntegral X.left] [Smooth X.hom] [IsProper X.hom]
    (T : SplitToricEmbedding k n X)

local instance : IsDomain (AddMonoidAlgebra k (Fin n→ℤ)) :=
  torusCoordinateRing_isDomain k n

/-- Intrinsic geometric hypotheses yield an actual complete smooth fan
and an actual scheme isomorphism over the original field. -/
theorem exists_smooth_complete_fan
    (D : CartierData X.left) (hD : D.IsAmple) :
    ∃ (P : LatticePolytope n) («Σ» : SmoothCompleteFan n)
      (e : «Σ».fanScheme k≅X.left),
      P.Smooth ∧ «Σ».realCones=P.normalFan ∧ «Σ».IsPure ∧
      e.hom≫X.hom=«Σ».fanSchemeStructureMap k ∧
      «Σ».splitTorusOpenMap k≫e.hom=T.torus.left := by
  obtain ⟨C,F,s,hvalue,hcover,hclosed⟩ := T.exists_character_projective_embedding D hD
  let a : ULift.{u} F→Lattice n := fun m => m.down.val
  have hF : Nonempty (ULift.{u} F) := by
    have hη : genericPoint X.left∈⨆ i : ULift.{u} F,C.nonvanishingOpen (s i) := by
      rw [hcover]; trivial
    obtain ⟨i,hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hη
    exact ⟨i⟩
  let i₀ : ULift.{u} F := Classical.choice hF
  letI : IsClosedImmersion (C.sectionProjectiveMap k s hcover) := hclosed
  let e₀ : X.left≅monomialProjectiveScheme a k :=
    C.characterMonomialImageIso k T.torus.left a s hvalue T.dense hcover i₀
  let j : Spec (CommRingCat.of (AddMonoidAlgebra k (Lattice n))) ⟶ X.left :=
    T.torus.left
  letI : IsOpenImmersion j := T.open_immersion
  have htorus : T.torus.left≫e₀.hom=monomialTorusChart a k i₀ :=
    C.characterMonomialImageIso_torus k T.torus.left a s hvalue T.dense hcover i₀
  letI : IsDominant T.torus.left := ⟨T.dense⟩
  have hbase : e₀.hom≫monomialProjectiveToSpec a k=X.hom := by
    apply ext_of_isDominant T.torus.left
    rw [← Category.assoc,htorus]
    change monomialTorusChart a k i₀ ≫ monomialProjectiveToSpec a k = j ≫ X.hom
    exact (monomialTorusChart_toSpec a k i₀).trans T.torus.w.symm
  have hbase' : monomialProjectiveToSpec a k=e₀.inv≫X.hom := by
    rw [← hbase]
    simp
  letI : Smooth (monomialProjectiveToSpec a k) := by
    rw [hbase']
    infer_instance
  letI : IsOpenImmersion (monomialTorusChart a k i₀) := by
    rw [← htorus]
    change IsOpenImmersion (j ≫ e₀.hom)
    infer_instance
  obtain ⟨P,«Σ»,e₁,hP,hPs,«hΣ»,hpure,hbase₁,htorus₁⟩ :=
    exists_smooth_normal_fan_of_monomial_projective a k i₀
  refine ⟨P,«Σ»,e₁.trans e₀.symm,hPs,«hΣ»,hpure,?_,?_⟩
  · simp only [Iso.trans_hom,Iso.symm_hom,Category.assoc]
    rw [← hbase',hbase₁]
  · simp only [Iso.trans_hom,Iso.symm_hom,← Category.assoc]
    rw [htorus₁ i₀,← htorus]
    change (j ≫ e₀.hom) ≫ e₀.inv = j
    simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]

end PaperVerification.ToricSchemes.SplitToricEmbedding

#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.exists_smooth_complete_fan
