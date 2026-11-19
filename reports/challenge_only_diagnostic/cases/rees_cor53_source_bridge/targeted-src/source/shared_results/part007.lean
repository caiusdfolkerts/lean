module
public import graph_foundation.part009
public import shared_results.part006

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphGroebner -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
noncomputable section
namespace FourPapers.Sublattice
open Classical MvPolynomial CommAlg.Polymatroid
universe u
variable {N : ℕ} {k : Type u} [CommRing k] [IsDomain k]

lemma graphPairExponent_sub_same_first (i j l : Fin N) (hjl : j≠l) :
    graphPairExponent.{u} i l-graphPairExponent i j=Finsupp.single ⟨1,ULift.up l⟩ 1 := by
  ext v
  rcases v with ⟨r,⟨h⟩⟩
  fin_cases r
  all_goals simp only [graphPairExponent,Finsupp.tsub_apply,Finsupp.add_apply,Finsupp.single_apply]
  all_goals by_cases hj : j=h <;> by_cases hl : l=h <;> simp_all

lemma graphPairExponent_sub_same_last (i h j : Fin N) (hih : i≠h) :
    graphPairExponent.{u} h j-graphPairExponent i j=Finsupp.single ⟨0,ULift.up h⟩ 1 := by
  ext v
  rcases v with ⟨r,⟨a⟩⟩
  fin_cases r
  all_goals simp only [graphPairExponent,Finsupp.tsub_apply,Finsupp.add_apply,Finsupp.single_apply]
  all_goals by_cases hi : i=a <;> by_cases hh : h=a <;> simp_all

lemma graphPairExponent_sup_disjoint (i j h l : Fin N) (hih : i≠h) (hjl : j≠l) :
    graphPairExponent.{u} i j⊔graphPairExponent h l=
      graphPairExponent i j+graphPairExponent h l := by
  ext v
  rcases v with ⟨r,⟨a⟩⟩
  fin_cases r
  · by_cases hi : i=a <;> by_cases hh : h=a
    all_goals simp_all [graphPairExponent,Finsupp.sup_apply,Finsupp.add_apply,Finsupp.single_apply]
  · by_cases hj : j=a <;> by_cases hl : l=a
    all_goals simp_all [graphPairExponent,Finsupp.sup_apply,Finsupp.add_apply,Finsupp.single_apply]

lemma graphBinomial_sPolynomial_same_first (i j l : Fin N)
    (hij : i< j) (hil : i< l) (hjl : j≠l) :
    graphLexOrder.sPolynomial (graphBinomial (k:=k) i j) (graphBinomial i l)=
      -X ⟨1,ULift.up i⟩*graphBinomial j l := by
  rw [MonomialOrder.sPolynomial,graphBinomial_degree (k := k) hij,graphBinomial_degree (k := k) hil,
    graphBinomial_leadingCoeff (k := k) hij,graphBinomial_leadingCoeff (k := k) hil,
    graphPairExponent_sub_same_first i j l hjl,
    graphPairExponent_sub_same_first i l j hjl.symm]
  change X ⟨1,ULift.up l⟩*graphBinomial (k:=k) i j-
    X ⟨1,ULift.up j⟩*graphBinomial i l=_
  simp only [graphBinomial_variables (k := k)]
  ring

lemma graphBinomial_sPolynomial_same_last (i h j : Fin N)
    (hij : i< j) (hhj : h< j) (hih : i≠h) :
    graphLexOrder.sPolynomial (graphBinomial (k:=k) i j) (graphBinomial h j)=
      X ⟨0,ULift.up j⟩*graphBinomial i h := by
  rw [MonomialOrder.sPolynomial,graphBinomial_degree (k := k) hij,graphBinomial_degree (k := k) hhj,
    graphBinomial_leadingCoeff (k := k) hij,graphBinomial_leadingCoeff (k := k) hhj,
    graphPairExponent_sub_same_last i h j hih,
    graphPairExponent_sub_same_last h i j hih.symm]
  change X ⟨0,ULift.up h⟩*graphBinomial (k:=k) i j-
    X ⟨0,ULift.up i⟩*graphBinomial h j=_
  simp only [graphBinomial_variables (k := k)]
  ring

/-- The quadratic generators of an actually closed labeled graph form a
monic Gröbner basis in the literal two-row polynomial ring, in every
characteristic. All S-pairs are treated without a graph-size bound. -/
theorem closedGraph_binomial_groebner {G : SimpleGraph (Fin N)}
    (hG : ClosedLabeling G) :
    graphLexOrder.IsGroebnerBasis (graphBinomialGenerators (k:=k) G)
      (graphBinomialIdeal (k:=k) G) := by
  apply MonomialOrder.isGroebnerBasis_span_of_isRemainder_sPolynomial_zero
  · rintro _ ⟨i,j,hij,hadj,rfl⟩ _
    rw [graphBinomial_leadingCoeff (k := k) hij]
    exact isUnit_one
  · rintro _ ⟨i,j,hij,hijG,rfl⟩ _ ⟨h,l,hhl,hhlG,rfl⟩
    by_cases hih : i=h
    · subst h
      by_cases hjl : j=l
      · subst l
        rw [MonomialOrder.sPolynomial_self]
        exact MonomialOrder.isRemainder_zero_left_iff.mpr rfl
      · rw [graphBinomial_sPolynomial_same_first (k := k) i j l hij hhl hjl]
        have hjlG := hG.1 hij hhl hjl hijG hhlG
        rcases lt_or_gt_of_ne hjl with hjl' | hlj'
        · exact MonicBinomialBuchberger.single_product graphLexOrder _ _
            (graphBinomial_mem (k := k) hjl' hjlG)
        · rw [graphBinomial_swap (k := k) l j,neg_mul_neg]
          exact MonicBinomialBuchberger.single_product graphLexOrder _ _
            (graphBinomial_mem (k := k) hlj' hjlG.symm)
    · by_cases hjl : j=l
      · subst l
        rw [graphBinomial_sPolynomial_same_last (k := k) i h j hij hhl hih]
        have hihG := hG.2 hij hhl hih hijG hhlG
        rcases lt_or_gt_of_ne hih with hih' | hhi'
        · exact MonicBinomialBuchberger.single_product graphLexOrder _ _
            (graphBinomial_mem (k := k) hih' hihG)
        · rw [graphBinomial_swap (k := k) h i,mul_neg,←neg_mul]
          exact MonicBinomialBuchberger.single_product graphLexOrder _ _
            (graphBinomial_mem (k := k) hhi' hihG.symm)
      · exact MonicBinomialBuchberger.coprime_binomial_pair graphLexOrder
          (graphPairExponent_order hij) (graphPairExponent_order hhl)
          (graphPairExponent_sup_disjoint i j h l hih hjl)
          (graphBinomial_mem (k := k) hij hijG) (graphBinomial_mem (k := k) hhl hhlG)

/-- The normal-form exponents are exactly the monomials outside the
sublattice edge ideal, not an assumed or abstract standard-basis predicate. -/
theorem closedGraph_standardMonomials {G : SimpleGraph (Fin N)}
    (hG : ClosedLabeling G) (a : Exponent (FiniteVariable.{u} (GraphRows N))) :
    a∈graphLexOrder.standardMonomials (graphBinomialIdeal (k:=k) G) ↔
      ¬Contains (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) a := by
  rw [(closedGraph_binomial_groebner (k:=k) hG).mem_standardMonomials_iff]
  constructor
  · intro h hc
    rcases hc with ⟨b,hb,hba⟩
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hb
    rcases (mem_graphEdgeLattice G e).mp he with ⟨helt,heG⟩
    apply h _ (graphBinomial_mem (k := k) helt heG) (graphBinomial_ne_zero (k := k) helt)
    rw [graphBinomial_degree (k := k) helt,graphPairExponent_eq_row,graphTuple_eta]
    exact hba
  · rintro h _ ⟨i,j,hij,hijG,rfl⟩ _ hle
    apply h
    refine ⟨finiteRowExponent (GraphRows N) (graphTuple i j),?_,?_⟩
    · apply Finset.mem_image.mpr
      refine ⟨graphTuple i j,?_,rfl⟩
      apply (mem_graphEdgeLattice G _).mpr
      simpa only [graphTuple_zero,graphTuple_one] using And.intro hij hijG
    · rw [graphBinomial_degree (k := k) hij,graphPairExponent_eq_row] at hle
      exact hle

end FourPapers.Sublattice


end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphGroebnerWeight -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000
noncomputable section
namespace FourPapers.Sublattice
open Classical MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
universe u
variable {N : ℕ} {k : Type u} [CommRing k] [IsDomain k]

/-- A nonnegative weight strictly selecting every diagonal binomial term. -/
def graphDiagonalWeight (v : FiniteVariable.{u} (GraphRows N)) : ℕ :=
  if v.1=0 then N-v.2.down.val else 0

lemma graphPairExponent_weight (i j : Fin N) :
    Finsupp.weight graphDiagonalWeight (graphPairExponent.{u} i j)=N-i.val := by
  simp [graphPairExponent,graphDiagonalWeight,Finsupp.weight_single]

lemma graphBinomial_weight_tail {i j : Fin N} (hij : i< j)
    (a : FiniteVariable.{u} (GraphRows N) →₀ ℕ)
    (ha : a∈(monomial (graphLexOrder.degree (graphBinomial (k:=k) i j)) 1-
      graphBinomial (k:=k) i j).support) :
    Finsupp.weight graphDiagonalWeight a<
      Finsupp.weight graphDiagonalWeight (graphLexOrder.degree (graphBinomial (k:=k) i j)) := by
  rw [graphBinomial_degree (k := k) hij] at ha ⊢
  have ht : monomial (graphPairExponent i j) (1:k)-graphBinomial i j=
      monomial (graphPairExponent j i) 1 := by
    unfold graphBinomial
    abel
  rw [ht,support_monomial,if_neg one_ne_zero,Finset.mem_singleton] at ha
  subst a
  rw [graphPairExponent_weight,graphPairExponent_weight]
  have hj := j.isLt
  have hi : i.val< j.val := hij
  omega

theorem graphBinomialGenerators_weight_tails (G : SimpleGraph (Fin N)) :
    ∀g∈graphBinomialGenerators (k:=k) G,g≠0→
      ∀a∈(monomial (graphLexOrder.degree g) 1-g).support,
        Finsupp.weight graphDiagonalWeight a<
          Finsupp.weight graphDiagonalWeight (graphLexOrder.degree g) := by
  rintro _ ⟨i,j,hij,_,rfl⟩ _ a ha
  exact graphBinomial_weight_tail (k := k) hij a ha

/-- The usual vertex degree together with the two row degrees. -/
def graphVertexRowDegree (v : FiniteVariable.{u} (GraphRows N)) :
    (Fin N →₀ ℕ) × (Fin 2 →₀ ℕ) :=
  (Finsupp.single v.2.down 1,Finsupp.single v.1 1)

lemma graphPairExponent_vertexRowDegree (i j : Fin N) :
    Finsupp.weight graphVertexRowDegree (graphPairExponent.{u} i j)=
      Finsupp.weight graphVertexRowDegree (graphPairExponent.{u} j i) := by
  simp only [graphPairExponent,map_add,Finsupp.weight_single,one_nsmul,graphVertexRowDegree]
  apply Prod.ext
  · exact add_comm _ _
  · rfl

/-- Homogeneity is proved in the actual polynomial ring, simultaneously for
vertex and row degree. Summing the vertex coordinates gives total degree. -/
theorem graphBinomialIdeal_vertexRow_homogeneous (G : SimpleGraph (Fin N)) :
    (graphBinomialIdeal (k:=k) G).IsHomogeneous
      (weightedHomogeneousSubmodule k graphVertexRowDegree) := by
  apply Ideal.homogeneous_span
  rintro _ ⟨i,j,_,_,rfl⟩
  refine ⟨Finsupp.weight graphVertexRowDegree (graphPairExponent i j),?_⟩
  exact (isWeightedHomogeneous_monomial graphVertexRowDegree
    (graphPairExponent i j) (1:k) rfl).sub
      (isWeightedHomogeneous_monomial graphVertexRowDegree
        (graphPairExponent j i) (1:k) (graphPairExponent_vertexRowDegree i j).symm)

end FourPapers.Sublattice


end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.FullKoszulContraction -/
section

section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

abbrev FullFaceModule (α : Exponent V) := TotalFaceModule (k := k) (fullKoszulFaces α)

def fullFaceDifferential (α : Exponent V) : Module.End k (FullFaceModule (k := k) α) :=
  idealTotalDifferential (fullKoszulFaces_downward α)

def fullFaceCreation (α : Exponent V) (e : V) (he : 0<α e) :
    Module.End k (FullFaceModule (k := k) α) :=
  ((Simplicial.creation e).domRestrict (FullFaceModule (k := k) α)).codRestrict _
    (fun x => creation_mem_basisSpan e (fun F hF => fullKoszulFaces_insert he hF) x.property)

lemma fullFace_contraction (α : Exponent V) (e : V) (he : 0<α e) :
    (fullFaceDifferential (k := k) α).comp (fullFaceCreation α e he) +
      (fullFaceCreation α e he).comp (fullFaceDifferential α)=LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change Simplicial.boundary (Simplicial.creation e x.val) +
    Simplicial.creation e (Simplicial.boundary x.val)=x.val
  rw [Simplicial.boundary_creation]
  exact sub_add_cancel _ _

end FourPapers.Sublattice
end

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.FullKoszulProjection -/
section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
/- SOURCE FourPapers.Sublattice.FullKoszulProjection -/
section ExtensionSource2

section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

/-- Literal quotient projection on the ambient homogeneous polynomial strand. -/
def fullFaceQuotientProjection (B : Family V) (α : Exponent V) :
    Module.End k (FullFaceModule (k := k) α) :=
  ((quotientFaceProjection B α).domRestrict (FullFaceModule (k := k) α)).codRestrict _
    (by
      intro x
      have hx : quotientFaceProjection (k := k) B α x.val ∈
          TotalFaceModule (k := k) (quotientKoszulFaces B α) :=
        relativeProjection_mem (Simplicial.basis (k := k)) (fullKoszulFaces α)
          (forbiddenKoszulFaces B α) x.val
      exact Submodule.span_mono (Set.image_mono
        (show {F | quotientKoszulFaces B α F} ⊆ {F | fullKoszulFaces α F} from
          fun _ hF => hF.1)) hx)

@[simp] lemma fullFaceQuotientProjection_val (B : Family V) (α : Exponent V)
    (x : FullFaceModule (k := k) α) :
    (fullFaceQuotientProjection B α x).val=quotientFaceProjection B α x.val := rfl

lemma fullFaceQuotientProjection_idempotent (B : Family V) (α : Exponent V) :
    (fullFaceQuotientProjection (k := k) B α).comp (fullFaceQuotientProjection B α)=
      fullFaceQuotientProjection B α := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact relativeProjection_idempotent Simplicial.basis (fullKoszulFaces α)
    (forbiddenKoszulFaces B α) x.val

lemma fullFaceQuotientProjection_differential (B : Family V) (α : Exponent V) :
    (fullFaceQuotientProjection (k := k) B α).comp
        ((fullFaceDifferential α).comp (fullFaceQuotientProjection B α)) =
      (fullFaceQuotientProjection B α).comp (fullFaceDifferential α) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact relativeProjection_map_projection (Simplicial.basis (k := k)) (fullKoszulFaces α)
    (forbiddenKoszulFaces B α) Simplicial.boundary
    (fun _ hx => boundary_mem_basisSpan (forbiddenKoszulFaces_downward B α) hx) x.property

/-- The full ambient contraction gives a faithful connecting-cycle criterion
for the actual homogeneous quotient Koszul complex. -/
theorem fullQuotientCycle_span_of_connecting (B : Family V) (α : Exponent V)
    (e : V) (he : 0<α e) (G : Set (FullFaceModule (k := k) α))
    (hG : ∀x∈G, fullFaceQuotientProjection B α x=x)
    (z : FullFaceModule (k := k) α)
    (hz : fullFaceQuotientProjection B α z=z)
    (hδ : fullFaceDifferential α z ∈
      (Submodule.span k G ⊔ LinearMap.ker (fullFaceQuotientProjection B α)).map
        (fullFaceDifferential α)) :
    z∈Submodule.span k G ⊔ LinearMap.range
      ((fullFaceQuotientProjection B α).comp
        ((fullFaceDifferential α).comp (fullFaceQuotientProjection B α))) :=
  quotientCycle_mem_span_of_connecting (R := k) (M := FullFaceModule (k := k) α)
    (fullFaceDifferential (k := k) α)
    (fullFaceQuotientProjection (k := k) B α) (fullFaceCreation (k := k) α e he)
    (fullFaceQuotientProjection_idempotent (k := k) B α)
    (fullFaceQuotientProjection_differential (k := k) B α)
    (fullFace_contraction (k := k) α e he) G hG z hz hδ

end FourPapers.Sublattice
end

end
end ExtensionSource2


end

/- BEGIN EXACT BODY: FourPapers.Sublattice.RectangleFaceCycles -/
section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
/- SOURCE FourPapers.Sublattice.RectangleFaceCycles -/
section ExtensionSource3

section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

/-- The fine strand occupied by one complete bipartite rectangle. -/
def rectangleFaceDegree (X Y : Finset V) : Exponent V := faceExponent (X∪Y)

/-- Literal linear-strand rectangle representative. The exterior signs come
from the already fixed orientation of the actual finite variable set. -/
def rectangleFaceVector (X Y : Finset V) : Simplicial.Ambient V k :=
  Simplicial.boundary (Simplicial.basis X) * Simplicial.basis Y

lemma boundary_mem_eraseSpan (X : Finset V) :
    Simplicial.boundary (Simplicial.basis (k := k) X) ∈
      basisSpan Simplicial.basis (fun F => ∃x∈X, F=X.erase x) := by
  rw [Simplicial.boundary_eq_sum]
  apply Submodule.sum_mem
  intro x _
  rw [Simplicial.contraction_basis]
  split_ifs with hx
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨X.erase x,⟨x,hx,rfl⟩,rfl⟩)
  · exact Submodule.zero_mem _

lemma rectangle_residual_one (X Y : Finset V) (hXY : Disjoint X Y)
    {x : V} (hx : x∈X) :
    rectangleFaceDegree X Y-faceExponent ((X.erase x)∪Y)=Finsupp.single x 1 := by
  unfold rectangleFaceDegree
  rw [faceExponent_union_of_disjoint X Y hXY,
    residual_union_of_disjoint (faceExponent X) (faceExponent Y) (X.erase x) Y
      (hXY.mono_left (Finset.erase_subset _ _))
      (faceExponent_mono (Finset.erase_subset _ _)) le_rfl,tsub_self,add_zero]
  rw [←faceExponent_erase_add hx,add_tsub_cancel_left]

lemma rectangle_residual_pair (X Y : Finset V) (hXY : Disjoint X Y)
    {x y : V} (hx : x∈X) (hy : y∈Y) :
    rectangleFaceDegree X Y-faceExponent ((X.erase x)∪(Y.erase y))=
      Finsupp.single x 1+Finsupp.single y 1 := by
  unfold rectangleFaceDegree
  rw [faceExponent_union_of_disjoint X Y hXY,
    residual_union_of_disjoint (faceExponent X) (faceExponent Y) (X.erase x) (Y.erase y)
      (hXY.mono (Finset.erase_subset _ _) (Finset.erase_subset _ _))
      (faceExponent_mono (Finset.erase_subset _ _))
      (faceExponent_mono (Finset.erase_subset _ _))]
  rw [←faceExponent_erase_add hx,←faceExponent_erase_add hy,
    add_tsub_cancel_left,add_tsub_cancel_left]

lemma rectangleFaceVector_mem (B : Family V) (X Y : Finset V)
    (hXY : Disjoint X Y) (hlinear : ∀x∈X, ¬Contains B (Finsupp.single x 1)) :
    rectangleFaceVector (k := k) X Y ∈
      TotalFaceModule (k := k) (quotientKoszulFaces B (rectangleFaceDegree X Y)) := by
  apply faceSpan_mul_mem (fun F => ∃x∈X, F=X.erase x) (fun F => F=Y)
    (quotientKoszulFaces B (rectangleFaceDegree X Y)) _
    (boundary_mem_eraseSpan X) (Submodule.subset_span ⟨Y,rfl,rfl⟩)
  intro F hF G hG _
  obtain ⟨x,hx,rfl⟩ := hF
  subst G
  refine ⟨?_,?_⟩
  · exact faceExponent_mono (Finset.union_subset_union (Finset.erase_subset _ _) le_rfl)
  · change ¬Contains B (rectangleFaceDegree X Y-faceExponent ((X.erase x)∪Y))
    rw [rectangle_residual_one X Y hXY hx]
    exact hlinear x hx

lemma rectangleFaceVector_boundary_mem (B : Family V) (X Y : Finset V)
    (hXY : Disjoint X Y)
    (hedges : ∀x∈X, ∀y∈Y, Contains B (Finsupp.single x 1+Finsupp.single y 1)) :
    Simplicial.boundary (rectangleFaceVector (k := k) X Y) ∈
      basisSpan Simplicial.basis (forbiddenKoszulFaces B (rectangleFaceDegree X Y)) := by
  have hformula : Simplicial.boundary (rectangleFaceVector (k := k) X Y) =
      CliffordAlgebra.involute (Simplicial.boundary (Simplicial.basis X)) *
        Simplicial.boundary (Simplicial.basis Y) := by
    unfold rectangleFaceVector Simplicial.boundary
    rw [CliffordAlgebra.contractLeft_mul,CliffordAlgebra.contractLeft_contractLeft,
      zero_mul,zero_add]
  rw [hformula]
  apply faceSpan_mul_mem (fun F => ∃x∈X, F=X.erase x)
    (fun F => ∃y∈Y, F=Y.erase y)
    (forbiddenKoszulFaces B (rectangleFaceDegree X Y)) _
    (faceSpan_involute_mem (fun F => ∃x∈X, F=X.erase x) (boundary_mem_eraseSpan X))
    (boundary_mem_eraseSpan Y)
  intro F hF G hG _
  obtain ⟨x,hx,rfl⟩ := hF
  obtain ⟨y,hy,rfl⟩ := hG
  change Contains B (rectangleFaceDegree X Y-faceExponent ((X.erase x)∪(Y.erase y)))
  rw [rectangle_residual_pair X Y hXY hx hy]
  exact hedges x hx y hy

/-- Actual element of the homogeneous quotient Koszul face module. -/
def rectangleQuotientCycle (B : Family V) (X Y : Finset V)
    (hXY : Disjoint X Y) (hlinear : ∀x∈X, ¬Contains B (Finsupp.single x 1)) :
    TotalFaceModule (k := k) (quotientKoszulFaces B (rectangleFaceDegree X Y)) :=
  ⟨rectangleFaceVector X Y,rectangleFaceVector_mem B X Y hXY hlinear⟩

/-- The complete-bipartite hypothesis kills the actual projected boundary. -/
theorem rectangleQuotientCycle_closed (B : Family V) (X Y : Finset V)
    (hXY : Disjoint X Y) (hlinear : ∀x∈X, ¬Contains B (Finsupp.single x 1))
    (hedges : ∀x∈X, ∀y∈Y, Contains B (Finsupp.single x 1+Finsupp.single y 1)) :
    quotientTotalDifferential B (rectangleFaceDegree X Y)
      (rectangleQuotientCycle (k := k) B X Y hXY hlinear)=0 := by
  apply Subtype.ext
  exact relativeProjection_zero_on_discarded (Simplicial.basis (k := k))
    (fullKoszulFaces (rectangleFaceDegree X Y))
    (forbiddenKoszulFaces B (rectangleFaceDegree X Y))
    (rectangleFaceVector_boundary_mem (k := k) B X Y hXY hedges)

end FourPapers.Sublattice
end

end
end ExtensionSource3


end

/- BEGIN EXACT BODY: FourPapers.Sublattice.RectangleProjection -/
section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
/- SOURCE FourPapers.Sublattice.RectangleProjection -/
section ExtensionSource4

section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

/-- Exterior forms each of whose basis terms contains the indicated variable. -/
def exteriorVariableSpan (e : V) : Submodule k (Simplicial.Ambient V k) :=
  basisSpan Simplicial.basis (fun F => e∈F)

lemma mem_full_faceSpan (x : Simplicial.Ambient V k) :
    x∈basisSpan Simplicial.basis (fun _ => True) := by
  have h : basisSpan (Simplicial.basis (V := V) (k := k)) (fun _ => True)=⊤ := by
    simp only [basisSpan,Set.setOf_true,Set.image_univ,Module.Basis.span_eq]
  rw [h]
  trivial

lemma creation_mem_variableSpan (e : V) (x : Simplicial.Ambient V k) :
    Simplicial.creation e x∈exteriorVariableSpan (k := k) e := by
  rw [←Simplicial.basis.linearCombination_repr x,Finsupp.linearCombination_apply,
    Finsupp.sum,map_sum]
  apply Submodule.sum_mem
  intro F hF
  rw [map_smul]
  apply Submodule.smul_mem
  rw [Simplicial.creation_basis]
  split_ifs with he
  · exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨insert e F,Finset.mem_insert_self e F,rfl⟩)

lemma exteriorVariableSpan_mul_left (e : V) {x y : Simplicial.Ambient V k}
    (hx : x∈exteriorVariableSpan (k := k) e) : x*y∈exteriorVariableSpan (k := k) e := by
  exact faceSpan_mul_mem (fun F => e∈F) (fun _ => True) (fun F => e∈F)
    (fun F hF G _ _ => Finset.mem_union_left G hF) hx (mem_full_faceSpan y)

lemma exteriorVariableSpan_mul_right (e : V) {x y : Simplicial.Ambient V k}
    (hy : y∈exteriorVariableSpan (k := k) e) : x*y∈exteriorVariableSpan (k := k) e := by
  exact faceSpan_mul_mem (fun _ => True) (fun F => e∈F) (fun F => e∈F)
    (fun F _ G hG _ => Finset.mem_union_right F hG) (mem_full_faceSpan x) hy

lemma exteriorVariableSpan_involute (e : V) {x : Simplicial.Ambient V k}
    (hx : x∈exteriorVariableSpan (k := k) e) :
    CliffordAlgebra.involute x∈exteriorVariableSpan (k := k) e :=
  faceSpan_involute_mem (fun F => e∈F) hx

lemma quotientFaceProjection_zero_variableSpan (B : Family V) (α : Exponent V)
    {e : V} (he : α e=0) {x : Simplicial.Ambient V k}
    (hx : x∈exteriorVariableSpan (k := k) e) : quotientFaceProjection B α x=0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F,hF,rfl⟩ := hx
    change e∈F at hF
    have hn : ¬fullKoszulFaces α F := by
      intro h
      have hh := h e
      simp only [faceExponent_apply,if_pos hF,he] at hh
      omega
    simp [quotientFaceProjection,hn]
  | zero => exact map_zero _
  | add x y hx hy ihx ihy => rw [map_add,ihx,ihy,add_zero]
  | smul c x hx ih => rw [map_smul,ih,smul_zero]

/-- Orientation convenient for the maximal-edge connecting computation. -/
def distinguishedRectangleVector (e f : V) (u v : Simplicial.Ambient V k) :
    Simplicial.Ambient V k :=
  Simplicial.boundary (Simplicial.creation e u) * Simplicial.creation f v

/-- After the two distinguished variables have been removed from the fine
shift, the connecting boundary is exactly the remaining exterior product.
All other terms vanish under the literal quotient projection because they
still contain one of those variables. This also includes multiplication by an
arbitrary residual form, so no unsupported tensor-of-ideals argument is used. -/
theorem distinguishedRectangle_connecting_projection
    (B : Family V) (α : Exponent V) (e f : V) (he : α e=0) (hf : α f=0)
    (u v r : Simplicial.Ambient V k) :
    quotientFaceProjection B α
      (Simplicial.boundary (distinguishedRectangleVector e f u v*r)) =
      quotientFaceProjection B α (CliffordAlgebra.involute u*v*r) := by
  let A := Simplicial.boundary (Simplicial.creation e u)
  let C := Simplicial.creation f v
  have hA : Simplicial.boundary A=0 := Simplicial.boundary_boundary _
  have hC : Simplicial.boundary C=v-Simplicial.creation f (Simplicial.boundary v) :=
    Simplicial.boundary_creation f v
  have hlast : quotientFaceProjection B α
      (CliffordAlgebra.involute (A*C)*Simplicial.boundary r)=0 := by
    apply quotientFaceProjection_zero_variableSpan B α hf
    apply exteriorVariableSpan_mul_left f
    apply exteriorVariableSpan_involute f
    exact exteriorVariableSpan_mul_right f (creation_mem_variableSpan f v)
  have hmiddle : quotientFaceProjection B α
      (CliffordAlgebra.involute A * Simplicial.creation f (Simplicial.boundary v) * r)=0 := by
    apply quotientFaceProjection_zero_variableSpan B α hf
    apply exteriorVariableSpan_mul_left f
    exact exteriorVariableSpan_mul_right f (creation_mem_variableSpan f _)
  have hfirst : quotientFaceProjection B α
      (CliffordAlgebra.involute (Simplicial.creation e (Simplicial.boundary u))*v*r)=0 := by
    apply quotientFaceProjection_zero_variableSpan B α he
    apply exteriorVariableSpan_mul_left e
    apply exteriorVariableSpan_mul_left e
    exact exteriorVariableSpan_involute e (creation_mem_variableSpan e _)
  have hleib (x y : Simplicial.Ambient V k) :
      Simplicial.boundary (x*y)=Simplicial.boundary x*y+
        CliffordAlgebra.involute x*Simplicial.boundary y :=
    CliffordAlgebra.contractLeft_mul _ x y
  change quotientFaceProjection B α (Simplicial.boundary ((A*C)*r))=_
  rw [hleib,hleib,hA,zero_mul,zero_add,hC,mul_sub,sub_mul,map_add,hlast,add_zero,
    map_sub,hmiddle,sub_zero]
  have heq : A=u-Simplicial.creation e (Simplicial.boundary u) :=
    Simplicial.boundary_creation e u
  rw [heq,map_sub,sub_mul,sub_mul,map_sub,hfirst,sub_zero]

end FourPapers.Sublattice
end

end
end ExtensionSource4


end

/- BEGIN EXACT BODY: FourPapers.Sublattice.GraphGeometrySource -/
section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
/- SOURCE FourPapers.Sublattice.GraphGeometrySource -/
section ExtensionSource11

end ExtensionSource11


end

/- BEGIN EXACT BODY: FourPapers.Sublattice.GraphRectangleProducts -/
section

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {N : ℕ} {k : Type u} [CommRing k]

/-- A literal ordered two-row rectangle retained by the current variable
restriction. Its complete bipartite edges belong to the original graph. -/
structure GraphRectangle (G : SimpleGraph (Fin N))
    (A : ∀r,Finset (Fin (GraphRows N r))) where
  X : Finset (FiniteVariable.{u} (GraphRows N))
  Y : Finset (FiniteVariable.{u} (GraphRows N))
  nonemptyX : X.Nonempty
  nonemptyY : Y.Nonempty
  rowX : ∀v∈X,v.1=0
  rowY : ∀v∈Y,v.1=1
  retainedX : ∀v∈X,v.2.down∈A v.1
  retainedY : ∀v∈Y,v.2.down∈A v.1
  edges : ∀x∈X,∀y∈Y,x.2.down<y.2.down ∧ G.Adj x.2.down y.2.down

variable {G : SimpleGraph (Fin N)} {A : ∀r,Finset (Fin (GraphRows N r))}

lemma GraphRectangle.disjoint (R : GraphRectangle.{u} G A) : Disjoint R.X R.Y := by
  apply Finset.disjoint_left.mpr
  intro v hx hy
  have h0 := R.rowX v hx
  have h1 := R.rowY v hy
  omega

def graphRestrictedFamily (G : SimpleGraph (Fin N))
    (A : ∀r,Finset (Fin (GraphRows N r))) : Family (FiniteVariable.{u} (GraphRows N)) :=
  finiteRowFamily (GraphRows N) (finiteRowRestriction (graphEdgeLattice G) A)

lemma graphRowExponent_pair (x y : FiniteVariable.{u} (GraphRows N))
    (hx : x.1=0) (hy : y.1=1) :
    finiteRowExponent (GraphRows N) (graphTuple x.2.down y.2.down)=
      Finsupp.single x 1+Finsupp.single y 1 := by
  rcases x with ⟨r,⟨i⟩⟩
  rcases y with ⟨s,⟨j⟩⟩
  change r=0 at hx
  change s=1 at hy
  subst r
  subst s
  simp [finiteRowExponent,Fin.sum_univ_two]

lemma graphRestrictedFamily_no_linear (G : SimpleGraph (Fin N))
    (A : ∀r,Finset (Fin (GraphRows N r))) (v : FiniteVariable.{u} (GraphRows N)) :
    ¬Contains (graphRestrictedFamily G A) (Finsupp.single v 1) := by
  rintro ⟨b,hb,hbv⟩
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
  have hh := degree_mono hbv
  simp only [finiteRowExponent_degree,Finsupp.degree_single] at hh
  omega

lemma GraphRectangle.edge_contains (R : GraphRectangle.{u} G A)
    (x : FiniteVariable.{u} (GraphRows N)) (hx : x∈R.X)
    (y : FiniteVariable.{u} (GraphRows N)) (hy : y∈R.Y) :
    Contains (graphRestrictedFamily G A) (Finsupp.single x 1+Finsupp.single y 1) := by
  refine ⟨finiteRowExponent (GraphRows N) (graphTuple x.2.down y.2.down),?_,?_⟩
  · apply Finset.mem_image.mpr
    refine ⟨graphTuple x.2.down y.2.down,
      (mem_finiteRowRestriction _ _ _).mpr ⟨?_,?_⟩,rfl⟩
    · exact (mem_graphEdgeLattice G _).mpr (R.edges x hx y hy)
    · intro r
      fin_cases r
      · change x.2.down ∈ A 0
        rcases x with ⟨rx, ⟨ix⟩⟩
        have hr : rx = 0 := R.rowX ⟨rx, ULift.up ix⟩ hx
        subst rx
        exact R.retainedX _ hx
      · change y.2.down ∈ A 1
        rcases y with ⟨ry, ⟨iy⟩⟩
        have hr : ry = 1 := R.rowY ⟨ry, ULift.up iy⟩ hy
        subst ry
        exact R.retainedY _ hy
  · exact (graphRowExponent_pair x y (R.rowX x hx) (R.rowY y hy)).le

def GraphRectangle.fineDegree (R : GraphRectangle.{u} G A) :
    Exponent (FiniteVariable.{u} (GraphRows N)) := rectangleFaceDegree R.X R.Y

def GraphRectangle.vector (R : GraphRectangle.{u} G A) :
    Simplicial.Ambient (FiniteVariable.{u} (GraphRows N)) k := rectangleFaceVector R.X R.Y

lemma GraphRectangle.vector_mem (R : GraphRectangle.{u} G A) :
    R.vector (k := k)∈TotalFaceModule (quotientKoszulFaces (graphRestrictedFamily G A) R.fineDegree) :=
  rectangleFaceVector_mem _ R.X R.Y R.disjoint
    (fun x _ => graphRestrictedFamily_no_linear G A x)

lemma GraphRectangle.vector_closed (R : GraphRectangle.{u} G A) :
    quotientFaceProjection (graphRestrictedFamily G A) R.fineDegree
      (Simplicial.boundary (R.vector (k := k)))=0 :=
  relativeProjection_zero_on_discarded (Simplicial.basis (k := k)) _ _
    (rectangleFaceVector_boundary_mem (k := k) _ R.X R.Y R.disjoint R.edge_contains)

def graphRectangleListDegree (L : List (GraphRectangle.{u} G A)) :
    Exponent (FiniteVariable.{u} (GraphRows N)) := (L.map GraphRectangle.fineDegree).sum

def graphRectangleListVector (L : List (GraphRectangle.{u} G A)) :
    Simplicial.Ambient (FiniteVariable.{u} (GraphRows N)) k :=
  (L.map (GraphRectangle.vector (k := k))).prod

lemma graphRectangleListVector_full (L : List (GraphRectangle.{u} G A)) :
    graphRectangleListVector (k := k) L∈
      TotalFaceModule (fullKoszulFaces (graphRectangleListDegree L)) := by
  induction L with
  | nil =>
    change (1 : Simplicial.Ambient _ k)∈TotalFaceModule (fullKoszulFaces 0)
    rw [←faceBasis_empty]
    exact Submodule.subset_span ⟨∅,by simp [fullKoszulFaces,faceExponent],rfl⟩
  | cons R L ih =>
    change R.vector (k := k)*graphRectangleListVector L∈
      TotalFaceModule (fullKoszulFaces (R.fineDegree+graphRectangleListDegree L))
    exact fullFaceSpan_mul _ _
      (Submodule.span_mono (Set.image_mono (fun _ hs => hs.1)) R.vector_mem) ih

lemma graphRectangleListVector_closed (L : List (GraphRectangle.{u} G A)) :
    quotientFaceProjection (graphRestrictedFamily G A) (graphRectangleListDegree L)
      (Simplicial.boundary (graphRectangleListVector (k := k) L))=0 := by
  induction L with
  | nil => simp [graphRectangleListVector,graphRectangleListDegree,Simplicial.boundary]
  | cons R L ih =>
    have hR : R.vector (k := k) ∈ TotalFaceModule (fullKoszulFaces R.fineDegree) :=
      Submodule.span_mono (Set.image_mono (fun _ hs => hs.1)) (R.vector_mem (k := k))
    have hL := graphRectangleListVector_full (k := k) L
    have hh := quotientFaceProjection_product_cycle (graphRestrictedFamily G A)
      R.fineDegree (graphRectangleListDegree L) hR hL (R.vector_closed (k := k)) ih
    rw [quotientFaceProjection_boundary _ _ (fullFaceSpan_mul _ _ hR hL)] at hh
    exact hh

/-- An honest finite product of rectangle cycles in one specified fine degree.
The final quotient projection is retained explicitly. -/
def graphRectangleProduct (α : Exponent (FiniteVariable.{u} (GraphRows N)))
    (L : {L : List (GraphRectangle.{u} G A) // graphRectangleListDegree L=α}) :
    TotalFaceModule (k := k) (quotientKoszulFaces (graphRestrictedFamily G A) α) :=
  ⟨quotientFaceProjection (graphRestrictedFamily G A) α (graphRectangleListVector L.val),
    relativeProjection_mem _ _ _ _⟩

def graphRectangleProductSpan (G : SimpleGraph (Fin N))
    (A : ∀r,Finset (Fin (GraphRows N r)))
    (α : Exponent (FiniteVariable.{u} (GraphRows N))) :
    Submodule k (TotalFaceModule (k := k) (quotientKoszulFaces (graphRestrictedFamily G A) α)) :=
  Submodule.span k (Set.range (graphRectangleProduct (G := G) (A := A) (k := k) α))

lemma graphRectangleProduct_closed (α : Exponent (FiniteVariable.{u} (GraphRows N)))
    (L : {L : List (GraphRectangle.{u} G A) // graphRectangleListDegree L=α}) :
    quotientTotalDifferential (graphRestrictedFamily G A) α (graphRectangleProduct (k := k) α L)=0 := by
  apply Subtype.ext
  change quotientFaceProjection _ α (Simplicial.boundary (quotientFaceProjection _ α
    (graphRectangleListVector L.val)))=0
  have hfull : graphRectangleListVector (k := k) L.val∈TotalFaceModule (fullKoszulFaces α) := by
    simpa only [L.property] using graphRectangleListVector_full (k := k) L.val
  rw [quotientFaceProjection_boundary _ α hfull]
  simpa only [L.property] using graphRectangleListVector_closed (k := k) L.val

lemma graphRectangleProductSpan_le_cycles (G : SimpleGraph (Fin N))
    (A : ∀r,Finset (Fin (GraphRows N r)))
    (α : Exponent (FiniteVariable.{u} (GraphRows N))) :
    graphRectangleProductSpan (k := k) G A α≤
      LinearMap.ker (quotientTotalDifferential (graphRestrictedFamily G A) α) := by
  apply Submodule.span_le.mpr
  rintro x ⟨L,rfl⟩
  exact graphRectangleProduct_closed α L

end FourPapers.Sublattice
end

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphProducts -/
section

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096

noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {N : ℕ} {k : Type u} [CommRing k]
variable {G : SimpleGraph (Fin N)}
variable {A : ∀r, Finset (Fin (GraphRows N r))}

local instance : DecidableEq (FiniteVariable.{u} (GraphRows N)) :=
  (inferInstance : LinearOrder (FiniteVariable.{u} (GraphRows N))).toDecidableEq

/-- Face coordinates whose polynomial coefficient uses only the first row.
Products of the rectangle representatives have this stronger support property. -/
def graphPureXFaces (α : Exponent (FiniteVariable.{u} (GraphRows N)))
    (F : Finset (FiniteVariable.{u} (GraphRows N))) : Prop :=
  fullKoszulFaces α F ∧
    ∀ v, v.1 = 1 → (α - faceExponent F) v = 0

lemma graphPureXFaces_quotient
    (α : Exponent (FiniteVariable.{u} (GraphRows N)))
    {F : Finset (FiniteVariable.{u} (GraphRows N))}
    (hF : graphPureXFaces α F) : quotientKoszulFaces (graphRestrictedFamily G A) α F := by
  refine ⟨hF.1, ?_⟩
  rintro ⟨b, hb, hbα⟩
  letI : DecidableEq (FiniteVariable.{u} (GraphRows N)) :=
    fun a b => Sigma.instDecidableEqSigma a b
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
  have h := hbα ⟨1, ULift.up (a 1)⟩
  rw [hF.2 _ rfl] at h
  simp only [finiteRowExponent_apply, ite_true] at h
  omega

lemma graphPureXFaces_union
    (α β : Exponent (FiniteVariable.{u} (GraphRows N)))
    {F H : Finset (FiniteVariable.{u} (GraphRows N))}
    (hF : graphPureXFaces α F) (hH : graphPureXFaces β H) (hFH : Disjoint F H) :
    graphPureXFaces (α + β) (F ∪ H) := by
  refine ⟨fullKoszulFaces_union α β F H hF.1 hH.1 hFH, ?_⟩
  intro v hv
  rw [residual_union_of_disjoint α β F H hFH hF.1 hH.1,
    Finsupp.add_apply, hF.2 v hv, hH.2 v hv, zero_add]

lemma GraphRectangle.vector_pureX (R : GraphRectangle.{u} G A) :
    R.vector (k := k) ∈ TotalFaceModule (graphPureXFaces R.fineDegree) := by
  change Simplicial.boundary (Simplicial.basis (k := k) R.X) *
    Simplicial.basis (k := k) R.Y ∈ _
  apply faceSpan_mul_mem (k := k) (fun F => ∃ x ∈ R.X, F = R.X.erase x)
    (fun F => F = R.Y) (graphPureXFaces R.fineDegree) _
    (boundary_mem_eraseSpan (k := k) R.X) (Submodule.subset_span ⟨R.Y, rfl, rfl⟩)
  intro F hF H hH hd
  obtain ⟨x, hx, rfl⟩ := hF
  subst H
  refine ⟨faceExponent_mono (Finset.union_subset_union (Finset.erase_subset _ _) le_rfl), ?_⟩
  intro v hv
  rw [show R.fineDegree = rectangleFaceDegree R.X R.Y from rfl,
    rectangle_residual_one R.X R.Y R.disjoint hx]
  have hne : x ≠ v := by
    intro h
    have hx0 := R.rowX x hx
    rw [h, hv] at hx0
    omega
  simp [Finsupp.single_apply, hne]

/-- No quotient projection changes a product of rectangle representatives:
its coefficients are pure x-monomials and the graph ideal requires a y-variable. -/
lemma graphRectangleListVector_pureX (L : List (GraphRectangle.{u} G A)) :
    graphRectangleListVector (k := k) L ∈
      TotalFaceModule (graphPureXFaces (graphRectangleListDegree L)) := by
  induction L with
  | nil =>
    change (1 : Simplicial.Ambient _ k) ∈ TotalFaceModule (graphPureXFaces 0)
    rw [← faceBasis_empty]
    apply Submodule.subset_span
    refine ⟨∅, ?_, rfl⟩
    simp [graphPureXFaces, fullKoszulFaces, faceExponent]
  | cons R L ih =>
    change R.vector (k := k) * graphRectangleListVector L ∈
      TotalFaceModule (graphPureXFaces (R.fineDegree + graphRectangleListDegree L))
    exact faceSpan_mul_mem _ _ _
      (fun F hF H hH hd => graphPureXFaces_union _ _ hF hH hd) (R.vector_pureX (k := k)) ih

lemma graphRectangleListVector_mem (L : List (GraphRectangle.{u} G A)) :
    graphRectangleListVector (k := k) L ∈
      TotalFaceModule (quotientKoszulFaces (graphRestrictedFamily G A)
        (graphRectangleListDegree L)) :=
  Submodule.span_mono (Set.image_mono (fun _ h => graphPureXFaces_quotient _ h))
    (graphRectangleListVector_pureX L)

lemma graphRectangleListVector_projection (L : List (GraphRectangle.{u} G A)) :
    quotientFaceProjection (graphRestrictedFamily G A) (graphRectangleListDegree L)
      (graphRectangleListVector (k := k) L) = graphRectangleListVector L :=
  relativeProjection_eq_self (graphRectangleListVector_mem L)

@[simp] lemma graphRectangleProduct_val
    (α : Exponent (FiniteVariable.{u} (GraphRows N)))
    (L : {L : List (GraphRectangle.{u} G A) // graphRectangleListDegree L = α}) :
    (graphRectangleProduct (k := k) α L).val = graphRectangleListVector L.val := by
  change quotientFaceProjection (graphRestrictedFamily G A) α
    (graphRectangleListVector (k := k) L.val) = _
  simpa only [L.property] using graphRectangleListVector_projection (k := k) L.val

@[simp] lemma graphRectangleListDegree_append
    (L M : List (GraphRectangle.{u} G A)) :
    graphRectangleListDegree (L ++ M) = graphRectangleListDegree L + graphRectangleListDegree M := by
  simp [graphRectangleListDegree]

@[simp] lemma graphRectangleListVector_append
    (L M : List (GraphRectangle.{u} G A)) :
    graphRectangleListVector (k := k) (L ++ M) =
      graphRectangleListVector L * graphRectangleListVector M := by
  simp [graphRectangleListVector]

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.GraphRestrictionRecursion -/
section

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 250000
set_option maxRecDepth 4096
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {d : ℕ} {n : Fin d → ℕ}

lemma contains_finiteRowRestriction_iff (E : Finset (FiniteTuple n))
    (A : ∀r, Finset (Fin (n r))) (α : Exponent (FiniteVariable.{u} n))
    (hα : SupportedRows A α) :
    Contains (finiteRowFamily n (finiteRowRestriction E A)) α ↔
      Contains (finiteRowFamily n E) α := by
  constructor
  · rintro ⟨b,hb,hbα⟩
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
    exact ⟨_,Finset.mem_image.mpr
      ⟨a,((mem_finiteRowRestriction E A a).mp ha).1,rfl⟩,hbα⟩
  · rintro ⟨b,hb,hbα⟩
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
    refine ⟨_,Finset.mem_image.mpr ⟨a,(mem_finiteRowRestriction E A a).mpr ⟨ha,?_⟩,rfl⟩,hbα⟩
    intro r
    apply hα r (a r)
    have h := hbα ⟨r,ULift.up (a r)⟩
    simpa only [finiteRowExponent_apply,ite_true,Nat.succ_le_iff] using h

lemma quotientFaces_finiteRowRestriction (E : Finset (FiniteTuple n))
    (A : ∀r, Finset (Fin (n r))) (α : Exponent (FiniteVariable.{u} n))
    (hα : SupportedRows A α) :
    quotientKoszulFaces (finiteRowFamily n (finiteRowRestriction E A)) α =
      quotientKoszulFaces (finiteRowFamily n E) α := by
  funext F
  apply propext
  change (faceExponent F≤α ∧ ¬Contains (finiteRowFamily n (finiteRowRestriction E A))
    (α-faceExponent F)) ↔ (faceExponent F≤α ∧ ¬Contains (finiteRowFamily n E) (α-faceExponent F))
  rw [contains_finiteRowRestriction_iff E A _ (hα.mono tsub_le_self)]

variable {N : ℕ}

/-- The residual is a restriction in the two *separate* rows. It is not
assumed to be the edge set of another interval graph. -/
def graphResidualRows (G : SimpleGraph (Fin N))
    (a : FiniteTuple (GraphRows N)) (A : ∀r, Finset (Fin (GraphRows N r))) :
    ∀r, Finset (Fin (GraphRows N r)) :=
  fun r => if r=0 then (A r).filter (fun h => ¬G.Adj h (a 1))
    else (A r).filter (fun h => h≤a 0)

lemma graphResidualRows_subset (G : SimpleGraph (Fin N))
    (a : FiniteTuple (GraphRows N)) (A : ∀r, Finset (Fin (GraphRows N r))) (r : Fin 2) :
    graphResidualRows G a A r ⊆ A r := by
  unfold graphResidualRows
  split_ifs <;> exact Finset.filter_subset _ _

lemma graphResidualRows_lattice_eq (G : SimpleGraph (Fin N))
    (a : FiniteTuple (GraphRows N)) (A : ∀r, Finset (Fin (GraphRows N r))) :
    finiteRowRestriction (graphEdgeLattice G) (graphResidualRows G a A) =
      finiteRowRestriction (graphResidualEdges G a) A := by
  ext b
  rw [mem_finiteRowRestriction,mem_finiteRowRestriction,graphResidualEdges_variable_restriction]
  constructor
  · rintro ⟨hb,hA⟩
    have h0 := hA 0
    have h1 := hA 1
    simp only [graphResidualRows,ite_true,Finset.mem_filter] at h0
    simp only [graphResidualRows,show (1 : Fin 2)≠0 from by decide,
      ite_false,Finset.mem_filter] at h1
    refine ⟨⟨hb,h0.2,h1.2⟩,?_⟩
    intro r
    exact graphResidualRows_subset G a A r (hA r)
  · rintro ⟨⟨hb,h0,h1⟩,hA⟩
    refine ⟨hb,?_⟩
    intro r
    fin_cases r
    · simp [graphResidualRows,hA 0,h0]
    · simp [graphResidualRows,hA 1,h1]

/-- The residual induction strictly decreases the number of retained edges. -/
lemma graphResidualRows_card_lt (G : SimpleGraph (Fin N))
    (a : FiniteTuple (GraphRows N)) (A : ∀r, Finset (Fin (GraphRows N r)))
    (ha : a∈finiteRowRestriction (graphEdgeLattice G) A) :
    (finiteRowRestriction (graphEdgeLattice G) (graphResidualRows G a A)).card <
      (finiteRowRestriction (graphEdgeLattice G) A).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_,?_⟩
  · intro b hb
    rcases (mem_finiteRowRestriction _ _ b).mp hb with ⟨hb,hA⟩
    exact (mem_finiteRowRestriction _ _ b).mpr
      ⟨hb,fun r => graphResidualRows_subset G a A r (hA r)⟩
  · intro heq
    have ha' : a∈finiteRowRestriction (graphEdgeLattice G) (graphResidualRows G a A) :=
      heq.symm ▸ ha
    have h0 := ((mem_finiteRowRestriction _ _ a).mp ha').2 0
    simp only [graphResidualRows,ite_true,Finset.mem_filter] at h0
    exact h0.2 (((mem_graphEdgeLattice G a).mp
      ((mem_finiteRowRestriction _ _ a).mp ha).1).2)

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.GraphSupportedColons -/
section

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {N : ℕ} {G : SimpleGraph (Fin N)}
variable (A : ∀r,Finset (Fin (GraphRows N r)))

lemma restrictedGraphPredecessor_contains (hG : IntervalLabeling G)
    {a : FiniteTuple (GraphRows N)} (ha : a∈finiteRowRestriction (graphEdgeLattice G) A)
    (γ : Exponent (FiniteVariable.{u} (GraphRows N))) (hγ : SupportedRows A γ) :
    Contains (finitePredecessorFamily (GraphRows N)
      (finiteRowRestriction (graphEdgeLattice G) A) a) γ↔Contains (graphColonFamily G a) γ := by
  rw [←finiteCoordinatePredecessor_contains_iff
      (finiteRowRestriction_closed (graphEdgeLattice_closed hG) A) ha,
    restrictedCoordinatePredecessor_contains_iff _ A ha γ hγ]
  exact graphCoordinateColon_contains_iff hG ((mem_finiteRowRestriction _ A a).mp ha).1 γ

lemma restrictedGraphPredecessor_faces (hG : IntervalLabeling G)
    {a : FiniteTuple (GraphRows N)} (ha : a∈finiteRowRestriction (graphEdgeLattice G) A)
    (γ : Exponent (FiniteVariable.{u} (GraphRows N))) (hγ : SupportedRows A γ) :
    quotientKoszulFaces (finitePredecessorFamily (GraphRows N)
      (finiteRowRestriction (graphEdgeLattice G) A) a) γ =
        quotientKoszulFaces (graphColonFamily G a) γ := by
  funext F
  apply propext
  change (fullKoszulFaces γ F ∧ ¬Contains _ (γ-faceExponent F))↔
    (fullKoszulFaces γ F ∧ ¬Contains _ (γ-faceExponent F))
  rw [restrictedGraphPredecessor_contains A hG ha _ (hγ.mono tsub_le_self)]

lemma graphResidualFine_supported
    {a : FiniteTuple (GraphRows N)}
    (γ : Exponent (FiniteVariable.{u} (GraphRows N)))
    (hγ : SupportedRows A γ) (hbound : RowBound γ a)
    (hzero : ∀r,γ ⟨r,ULift.up (a r)⟩=0) :
    SupportedRows (graphResidualRows G a A)
      (γ.filter (fun v => v∉graphLinearVariables G a)) := by
  intro r j hj
  have hjγ : 0<γ ⟨r,ULift.up j⟩ := by
    by_cases hn : (⟨r,ULift.up j⟩ : FiniteVariable.{u} (GraphRows N))∈graphLinearVariables G a
    · simp [Finsupp.filter_apply,hn] at hj
    · simpa [Finsupp.filter_apply,hn] using hj
  have hn : (⟨r,ULift.up j⟩ : FiniteVariable.{u} (GraphRows N))∉graphLinearVariables G a := by
    intro hm
    simp [Finsupp.filter_apply,hm] at hj
  have hjA := hγ r j hjγ
  have hjle := hbound ⟨r,ULift.up j⟩ (Nat.ne_of_gt hjγ)
  have hjne : j≠a r := by
    intro he
    subst j
    rw [hzero r] at hjγ
    omega
  have hjlt : j<a r := lt_of_le_of_ne hjle hjne
  fin_cases r
  · have hnot : ¬G.Adj j (a 1) := by
      intro hAdj
      exact hn ((graphLinearVariables_mem_x G a j).mpr ⟨hjlt,hAdj⟩)
    simpa [graphResidualRows,hnot] using hjA
  · have hle : j≤a 0 := by
      by_contra h
      exact hn ((graphLinearVariables_mem_y G a j).mpr ⟨lt_of_not_ge h,hjlt⟩)
    simpa [graphResidualRows,hle] using hjA

end FourPapers.Sublattice
end

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphColon -/
section

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096

noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

/-- Filtering an exponent is independent of the decision procedure used
for the predicate. This normal form handles the concrete finite-variable
decision procedure and the classical one in the separated-factor theorem. -/
private def classicalExponentFilter (S : V → Prop) (α : Exponent V) : Exponent V :=
  @Finsupp.filter V ℕ _ S (fun v => Classical.propDecidable (S v)) α

private lemma exponentFilter_eq_classical (S : V → Prop) (h : DecidablePred S)
    (α : Exponent V) :
    @Finsupp.filter V ℕ _ S h α = classicalExponentFilter S α :=
  congrArg (fun d : DecidablePred S => @Finsupp.filter V ℕ _ S d α)
    (Subsingleton.elim h (fun v => Classical.propDecidable (S v)))

/-- A squarefree exponent is the exponent of its actual support. -/
lemma squarefreeExponent_eq_faceExponent_support (α : Exponent V)
    (hα : ∀ v, α v ≤ 1) : faceExponent α.support = α := by
  ext v
  by_cases hv : α v = 0
  · simp [faceExponent_apply, Finsupp.mem_support_iff, hv]
  · have hv1 : α v = 1 := by have := hα v; omega
    simp [faceExponent_apply, Finsupp.mem_support_iff, hv, hv1]

lemma faceExponent_injective_local : Function.Injective (faceExponent (V := V)) := by
  intro A B h
  ext v
  have hv := congrArg (fun α : Exponent V => α v) h
  simp only [faceExponent_apply] at hv
  by_cases ha : v ∈ A <;> by_cases hb : v ∈ B <;> simp_all

lemma squarefreeExponent_filter (α : Exponent V) (hα : ∀ v, α v ≤ 1)
    (P : V → Prop) [DecidablePred P] : ∀ v, (α.filter P) v ≤ 1 := by
  intro v
  by_cases hv : P v <;> simp [Finsupp.filter_apply, hv, hα v]

lemma variableQuotient_faces_eq_support (L : Finset V) (α : Exponent V)
    (hα : ∀ v, α v ≤ 1) :
    quotientKoszulFaces (variableMonomialFamily L) (α.filter (fun v => v ∈ L)) =
      (fun F => F = (α.filter (fun v => v ∈ L)).support) := by
  funext F
  apply propext
  rw [quotientVariableFamily_faces_iff]
  · have hs : faceExponent (α.filter (fun v => v ∈ L)).support =
        α.filter (fun v => v ∈ L) :=
      squarefreeExponent_eq_faceExponent_support _ (by
        intro v
        by_cases hv : v ∈ L <;> simp [Finsupp.filter_apply, hv, hα v])
    constructor
    · intro hF
      exact faceExponent_injective_local (hF.trans hs.symm)
    · rintro rfl
      exact hs
  · intro v hv
    by_contra hn
    simp [Finsupp.filter_apply, hn] at hv

variable {N : ℕ} {G : SimpleGraph (Fin N)}

@[simp] lemma finiteRowRestriction_univ {d : ℕ} {n : Fin d → ℕ}
    (E : Finset (FiniteTuple n)) : finiteRowRestriction E (fun _ => Finset.univ) = E := by
  ext a
  simp

def graphColonLinearDegree (G : SimpleGraph (Fin N))
    (a : FiniteTuple (GraphRows N)) (γ : Exponent (FiniteVariable.{u} (GraphRows N))) :=
  γ.filter (fun v => v ∈ graphLinearVariables G a)

def graphColonResidualDegree (G : SimpleGraph (Fin N))
    (a : FiniteTuple (GraphRows N)) (γ : Exponent (FiniteVariable.{u} (GraphRows N))) :=
  γ.filter (fun v => v ∉ graphLinearVariables G a)

lemma graphColonDegree_add (a : FiniteTuple (GraphRows N))
    (γ : Exponent (FiniteVariable.{u} (GraphRows N))) :
    graphColonLinearDegree G a γ + graphColonResidualDegree G a γ = γ :=
  Finsupp.filter_add_filter_not γ (fun v => v ∈ graphLinearVariables G a)

lemma rowMaximum_residual_squarefree
    {α : Exponent (FiniteVariable.{u} (GraphRows N))}
    {a : FiniteTuple (GraphRows N)} (hα : RowMaximum α a)
    (hsq : ∀ v, α v ≤ 1) :
    (∀ v, (α - finiteRowExponent (GraphRows N) a) v ≤ 1) ∧
      RowBound (α - finiteRowExponent (GraphRows N) a) a ∧
      (∀ r, (α - finiteRowExponent (GraphRows N) a) ⟨r, ULift.up (a r)⟩ = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v
    exact ((tsub_le_self : α - finiteRowExponent (GraphRows N) a ≤ α) v).trans (hsq v)
  · intro v hv
    apply hα.2 v
    intro hzero
    exact hv (by simp [Finsupp.tsub_apply, hzero])
  · intro r
    have hle := hsq ⟨r, ULift.up (a r)⟩
    simp only [Finsupp.tsub_apply, finiteRowExponent_apply, ite_true]
    exact Nat.sub_eq_zero_of_le hle

lemma graphColonResidualDegree_lt
    {α : Exponent (FiniteVariable.{u} (GraphRows N))}
    {a : FiniteTuple (GraphRows N)} (hα : RowMaximum α a) :
    (graphColonResidualDegree G a (α - finiteRowExponent (GraphRows N) a)).degree < α.degree := by
  have hle : graphColonResidualDegree G a (α - finiteRowExponent (GraphRows N) a) ≤
      α - finiteRowExponent (GraphRows N) a := by
    intro v
    by_cases hv : v ∈ graphLinearVariables G a <;>
      simp [graphColonResidualDegree, Finsupp.filter_apply, hv]
  have hdeg := congrArg Finsupp.degree (tsub_add_cancel_of_le hα.1)
  simp only [map_add, finiteRowExponent_degree] at hdeg
  have hsmall := degree_mono hle
  omega

lemma graphColonResidual_quotientFaces
    (a : FiniteTuple (GraphRows N))
    (γ : Exponent (FiniteVariable.{u} (GraphRows N)))
    (hbound : RowBound γ a) (hzero : ∀ r, γ ⟨r, ULift.up (a r)⟩ = 0) :
    quotientKoszulFaces (finiteRowFamily (GraphRows N) (graphResidualEdges G a))
      (graphColonResidualDegree G a γ) =
    quotientKoszulFaces (finiteRowFamily (GraphRows N) (graphEdgeLattice G))
      (graphColonResidualDegree G a γ) := by
  have hs := graphResidualFine_supported (G := G) (fun _ => Finset.univ) γ
    (by intro r j hj; exact Finset.mem_univ j) hbound hzero
  have h := quotientFaces_finiteRowRestriction (graphEdgeLattice G)
    (graphResidualRows G a (fun _ => Finset.univ))
    (graphColonResidualDegree G a γ) hs
  rw [graphResidualRows_lattice_eq, finiteRowRestriction_univ] at h
  exact h

/-- In a squarefree degree below the distinguished edge, the predecessor
complex is one fixed exterior face times a smaller strand of the original
graph quotient. The residual factor is identified by actual monomial membership. -/
theorem closedGraphColon_faces_factorization
    (hG : IntervalLabeling G)
    {a : FiniteTuple (GraphRows N)} (ha : a ∈ graphEdgeLattice G)
    (γ : Exponent (FiniteVariable.{u} (GraphRows N)))
    (hsq : ∀ v, γ v ≤ 1) (hbound : RowBound γ a)
    (hzero : ∀ r, γ ⟨r, ULift.up (a r)⟩ = 0) :
    quotientKoszulFaces (finitePredecessorFamily (GraphRows N) (graphEdgeLattice G) a) γ =
      splitFacePredicate (fun v => v ∈ graphLinearVariables G a)
        (fun F => F = (graphColonLinearDegree G a γ).support)
        (quotientKoszulFaces (finiteRowFamily (GraphRows N) (graphEdgeLattice G))
          (graphColonResidualDegree G a γ)) := by
  have hcontains : ∀ α : Exponent (FiniteVariable.{u} (GraphRows N)),
      Contains (finitePredecessorFamily (GraphRows N) (graphEdgeLattice G) a) α ↔
        Contains (graphColonFamily G a) α := by
    intro α
    rw [← finiteCoordinatePredecessor_contains_iff (graphEdgeLattice_closed hG) ha]
    exact graphCoordinateColon_contains_iff hG ha α
  rw [quotientKoszulFaces_eq_of_contains hcontains γ]
  have hsep : quotientKoszulFaces (graphColonFamily G a) γ =
      splitFacePredicate (fun v => v ∈ graphLinearVariables G a)
        (quotientKoszulFaces (variableMonomialFamily (graphLinearVariables G a))
          (graphColonLinearDegree G a γ))
        (quotientKoszulFaces (finiteRowFamily (GraphRows N) (graphResidualEdges G a))
          (graphColonResidualDegree G a γ)) := by
    letI : DecidableEq (FiniteVariable.{u} (GraphRows N)) :=
      (inferInstance : LinearOrder (FiniteVariable.{u} (GraphRows N))).toDecidableEq
    have hfamily : graphColonFamily G a =
        variableMonomialFamily (graphLinearVariables G a) ∪
          finiteRowFamily (GraphRows N) (graphResidualEdges G a) := by
      ext b
      simp only [graphColonFamily, variableMonomialFamily, Finset.mem_union, Finset.mem_image]
    rw [hfamily]
    funext F
    apply propext
    simpa only [graphColonLinearDegree, graphColonResidualDegree,
      exponentFilter_eq_classical] using quotientSeparated_faces
      (fun v => v ∈ graphLinearVariables G a)
      (variableMonomialFamily (graphLinearVariables G a))
      (finiteRowFamily (GraphRows N) (graphResidualEdges G a))
      (by
        intro b hb v hv
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hb
        by_contra hn
        have hne : w ≠ v := by intro h; exact hn (h ▸ hw)
        simp [Finsupp.single_apply, hne] at hv)
      (by
        intro c hc v hv hvl
        letI : DecidableEq (FiniteVariable.{u} (GraphRows N)) :=
          fun a b => Sigma.instDecidableEqSigma a b
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hc
        exact hv (graphColon_disjoint_support G hvl hb)) γ F
  have hlin := variableQuotient_faces_eq_support (graphLinearVariables G a) γ hsq
  simp only [exponentFilter_eq_classical] at hlin
  rw [hsep]
  simp only [graphColonLinearDegree, exponentFilter_eq_classical]
  rw [hlin,
    graphColonResidual_quotientFaces a γ hbound hzero]

/-- The fixed left factor really uses only the linear-colon variables. -/
lemma graphColonLinear_support (a : FiniteTuple (GraphRows N))
    (γ : Exponent (FiniteVariable.{u} (GraphRows N))) :
    ∀ v ∈ (graphColonLinearDegree G a γ).support, v ∈ graphLinearVariables G a := by
  intro v hv
  have hn := Finsupp.mem_support_iff.mp hv
  by_contra h
  simp [graphColonLinearDegree, Finsupp.filter_apply, h] at hn

lemma graphColonResidual_face_support (a : FiniteTuple (GraphRows N))
    (γ : Exponent (FiniteVariable.{u} (GraphRows N)))
    (F : Finset (FiniteVariable.{u} (GraphRows N)))
    (hF : quotientKoszulFaces (finiteRowFamily (GraphRows N) (graphEdgeLattice G))
      (graphColonResidualDegree G a γ) F) :
    ∀ v ∈ F, v ∉ graphLinearVariables G a := by
  intro v hv hn
  have h := hF.1 v
  simp [faceExponent_apply, hv, graphColonResidualDegree, Finsupp.filter_apply, hn] at h

def closedGraphColonFactor (hG : IntervalLabeling G)
    {a : FiniteTuple (GraphRows N)} (ha : a ∈ graphEdgeLattice G)
    (γ : Exponent (FiniteVariable.{u} (GraphRows N)))
    (hsq : ∀ v, γ v ≤ 1) (hbound : RowBound γ a)
    (hzero : ∀ r, γ ⟨r, ULift.up (a r)⟩ = 0) :
    TotalFaceModule (k := k)
      (quotientKoszulFaces (finiteRowFamily (GraphRows N) (graphEdgeLattice G))
        (graphColonResidualDegree G a γ)) ≃ₗ[k]
    TotalFaceModule (k := k)
      (quotientKoszulFaces (finitePredecessorFamily (GraphRows N) (graphEdgeLattice G) a) γ) :=
  (fixedFaceFactorEquiv (fun v => v ∈ graphLinearVariables G a)
    (graphColonLinearDegree G a γ).support
    (quotientKoszulFaces (finiteRowFamily (GraphRows N) (graphEdgeLattice G))
      (graphColonResidualDegree G a γ))
    (graphColonLinear_support a γ) (graphColonResidual_face_support a γ)).trans
      (LinearEquiv.ofEq _ _ (by rw [closedGraphColon_faces_factorization hG ha γ hsq hbound hzero]))

lemma closedGraphColonFactor_val (hG : IntervalLabeling G)
    {a : FiniteTuple (GraphRows N)} (ha : a ∈ graphEdgeLattice G)
    (γ : Exponent (FiniteVariable.{u} (GraphRows N)))
    (hsq : ∀ v, γ v ≤ 1) (hbound : RowBound γ a)
    (hzero : ∀ r, γ ⟨r, ULift.up (a r)⟩ = 0)
    (x : TotalFaceModule (k := k)
      (quotientKoszulFaces (finiteRowFamily (GraphRows N) (graphEdgeLattice G))
        (graphColonResidualDegree G a γ))) :
    (closedGraphColonFactor hG ha γ hsq hbound hzero x).val =
      Simplicial.basis (graphColonLinearDegree G a γ).support * x.val :=
  fixedFaceFactorEquiv_val (k := k)
    (fun v => v ∈ graphLinearVariables G a) (graphColonLinearDegree G a γ).support
    (quotientKoszulFaces (finiteRowFamily (GraphRows N) (graphEdgeLattice G))
      (graphColonResidualDegree G a γ))
    (graphColonLinear_support a γ) (graphColonResidual_face_support a γ) x

lemma closedGraphColonFactor_differential (hG : IntervalLabeling G)
    {a : FiniteTuple (GraphRows N)} (ha : a ∈ graphEdgeLattice G)
    (γ : Exponent (FiniteVariable.{u} (GraphRows N)))
    (hsq : ∀ v, γ v ≤ 1) (hbound : RowBound γ a)
    (hzero : ∀ r, γ ⟨r, ULift.up (a r)⟩ = 0)
    (x : TotalFaceModule (k := k)
      (quotientKoszulFaces (finiteRowFamily (GraphRows N) (graphEdgeLattice G))
        (graphColonResidualDegree G a γ))) :
    quotientTotalDifferential (finitePredecessorFamily (GraphRows N) (graphEdgeLattice G) a) γ
        (closedGraphColonFactor hG ha γ hsq hbound hzero x) =
      (-1 : k)^(graphColonLinearDegree G a γ).support.card •
        closedGraphColonFactor hG ha γ hsq hbound hzero
          (quotientTotalDifferential (finiteRowFamily (GraphRows N) (graphEdgeLattice G))
            (graphColonResidualDegree G a γ) x) := by
  have h := congrArg Subtype.val (fixedFaceFactorEquiv_differential
    (fun v => v ∈ graphLinearVariables G a) (graphColonLinearDegree G a γ).support
    (quotientKoszulFaces (finiteRowFamily (GraphRows N) (graphEdgeLattice G))
      (graphColonResidualDegree G a γ))
    (graphColonLinear_support a γ) (graphColonResidual_face_support a γ) x)
  apply Subtype.ext
  change quotientFaceProjection _ γ
    (Simplicial.boundary ((closedGraphColonFactor hG ha γ hsq hbound hzero x).val)) = _
  simp only [Submodule.coe_smul, closedGraphColonFactor_val]
  rw [quotientFaceProjection_eq_faceProjection,
    closedGraphColon_faces_factorization hG ha γ hsq hbound hzero,
    quotientTotalDifferential_eq_projected]
  simpa only [projectedTotalDifferential, LinearMap.codRestrict_apply,
    LinearMap.comp_apply, Submodule.subtype_apply, fixedFaceFactorEquiv_val,
    Submodule.coe_smul] using h

lemma closedGraphColonFactor_cycle_iff (hG : IntervalLabeling G)
    {a : FiniteTuple (GraphRows N)} (ha : a ∈ graphEdgeLattice G)
    (γ : Exponent (FiniteVariable.{u} (GraphRows N)))
    (hsq : ∀ v, γ v ≤ 1) (hbound : RowBound γ a)
    (hzero : ∀ r, γ ⟨r, ULift.up (a r)⟩ = 0)
    (x : TotalFaceModule (k := k)
      (quotientKoszulFaces (finiteRowFamily (GraphRows N) (graphEdgeLattice G))
        (graphColonResidualDegree G a γ))) :
    quotientTotalDifferential (finitePredecessorFamily (GraphRows N) (graphEdgeLattice G) a) γ
      (closedGraphColonFactor hG ha γ hsq hbound hzero x) = 0 ↔
    quotientTotalDifferential (finiteRowFamily (GraphRows N) (graphEdgeLattice G))
      (graphColonResidualDegree G a γ) x = 0 := by
  have hs : IsUnit ((-1 : k)^(graphColonLinearDegree G a γ).support.card) :=
    (IsUnit.neg isUnit_one).pow _
  rw [closedGraphColonFactor_differential, hs.smul_eq_zero, LinearEquiv.map_eq_zero_iff]

lemma closedGraphColonFactor_boundary (hG : IntervalLabeling G)
    {a : FiniteTuple (GraphRows N)} (ha : a ∈ graphEdgeLattice G)
    (γ : Exponent (FiniteVariable.{u} (GraphRows N)))
    (hsq : ∀ v, γ v ≤ 1) (hbound : RowBound γ a)
    (hzero : ∀ r, γ ⟨r, ULift.up (a r)⟩ = 0)
    (x : TotalFaceModule (k := k)
      (quotientKoszulFaces (finiteRowFamily (GraphRows N) (graphEdgeLattice G))
        (graphColonResidualDegree G a γ))) :
    closedGraphColonFactor hG ha γ hsq hbound hzero
      (quotientTotalDifferential (finiteRowFamily (GraphRows N) (graphEdgeLattice G))
        (graphColonResidualDegree G a γ) x) ∈
    LinearMap.range (quotientTotalDifferential
      (finitePredecessorFamily (GraphRows N) (graphEdgeLattice G) a) γ) := by
  have hs : IsUnit ((-1 : k)^(graphColonLinearDegree G a γ).support.card) :=
    (IsUnit.neg isUnit_one).pow _
  apply (Submodule.smul_mem_iff_of_isUnit _ hs).mp
  rw [← closedGraphColonFactor_differential]
  exact ⟨closedGraphColonFactor hG ha γ hsq hbound hzero x, rfl⟩

/-- Cycle-level factorization, valid over every commutative coefficient ring.
No Künneth dimension argument or chosen homology basis is needed here. -/
theorem closedGraphColon_cycle_factorization
    (hG : IntervalLabeling G)
    {a : FiniteTuple (GraphRows N)} (ha : a ∈ graphEdgeLattice G)
    (γ : Exponent (FiniteVariable.{u} (GraphRows N)))
    (hsq : ∀ v, γ v ≤ 1) (hbound : RowBound γ a)
    (hzero : ∀ r, γ ⟨r, ULift.up (a r)⟩ = 0)
    (z : TotalFaceModule (k := k)
      (quotientKoszulFaces (finitePredecessorFamily (GraphRows N) (graphEdgeLattice G) a) γ))
    (hz : quotientTotalDifferential
      (finitePredecessorFamily (GraphRows N) (graphEdgeLattice G) a) γ z = 0) :
    ∃ x : TotalFaceModule (k := k)
      (quotientKoszulFaces (finiteRowFamily (GraphRows N) (graphEdgeLattice G))
        (graphColonResidualDegree G a γ)),
      quotientTotalDifferential (finiteRowFamily (GraphRows N) (graphEdgeLattice G))
        (graphColonResidualDegree G a γ) x = 0 ∧
      z.val = Simplicial.basis (graphColonLinearDegree G a γ).support * x.val := by
  let S := fun v => v ∈ graphLinearVariables G a
  let F := (graphColonLinearDegree G a γ).support
  let Q := quotientKoszulFaces (finiteRowFamily (GraphRows N) (graphEdgeLattice G))
    (graphColonResidualDegree G a γ)
  have hf := closedGraphColon_faces_factorization hG ha γ hsq hbound hzero
  let z' : TotalFaceModule (k := k) (splitFacePredicate S (fun A => A = F) Q) :=
    ⟨z.val, by rw [← hf]; exact z.property⟩
  have hz' : projectedTotalDifferential _ z' = 0 := by
    apply Subtype.ext
    change faceProjection (splitFacePredicate S (fun A => A = F) Q)
      (Simplicial.boundary z.val) = 0
    rw [← hf, ← quotientFaceProjection_eq_faceProjection]
    exact congrArg Subtype.val hz
  obtain ⟨x, hx, heq⟩ := fixedFace_cycle_factorization S F Q
    (graphColonLinear_support a γ) (graphColonResidual_face_support a γ) z' hz'
  refine ⟨x, ?_, heq⟩
  rw [quotientTotalDifferential_eq_projected]
  exact hx

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.GraphRectangleGeometry -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 200000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Polymatroid
universe u
variable {N : ℕ} {G : SimpleGraph (Fin N)}

/-- Every two distinct vertices in the interval spanned by an edge are
adjacent. This is the exact clique used to lift a rectangle cycle. -/
lemma interval_edge_spans_clique (hG : IntervalLabeling G)
    {i j u v : Fin N} (hij : G.Adj i j) (hiu : i≤u) (hiv : i≤v)
    (huj : u≤j) (hvj : v≤j) (huv : u≠v) : G.Adj u v := by
  rcases lt_or_gt_of_ne huv with huv | hvu
  · have huj' : u<j := huv.trans_le hvj
    have hujG := interval_adj_left hG hij hiu huj'
    exact interval_adj_right hG hujG huv hvj
  · have hvj' : v<j := hvu.trans_le huj
    have hvjG := interval_adj_left hG hij hiv hvj'
    exact (interval_adj_right hG hvjG hvu huj).symm

/-- The distinguished edge and the two linear-variable factors form one
complete bipartite rectangle. -/
lemma graphColon_rectangle_edges (hG : IntervalLabeling G)
    {a : FiniteTuple (GraphRows N)} (ha : a∈graphEdgeLattice G)
    {x y : Fin N}
    (hx : x=a 0 ∨ (⟨0,ULift.up x⟩ : FiniteVariable.{u} (GraphRows N))∈graphLinearVariables G a)
    (hy : y=a 1 ∨ (⟨1,ULift.up y⟩ : FiniteVariable.{u} (GraphRows N))∈graphLinearVariables G a) :
    x<y ∧ G.Adj x y := by
  have haG := ((mem_graphEdgeLattice G a).mp ha).2
  have ha01 := ((mem_graphEdgeLattice G a).mp ha).1
  have hxj : G.Adj x (a 1) := by
    rcases hx with rfl | hx
    · exact haG
    · exact ((graphLinearVariables_mem_x G a x).mp hx).2
  have hxi : x≤a 0 := by
    rcases hx with rfl | hx
    · exact le_rfl
    · exact ((graphLinearVariables_mem_x G a x).mp hx).1.le
  rcases hy with rfl | hy
  · exact ⟨hxi.trans_lt ha01,hxj⟩
  · have hy' := (graphLinearVariables_mem_y G a y).mp hy
    have hxy : x<y := hxi.trans_lt hy'.1
    exact ⟨hxy,interval_adj_right hG hxj hxy hy'.2.le⟩

/-- A nonempty rectangle in an interval graph lies in a clique. This is a
statement about the original graph, so its later quotient map is available. -/
lemma interval_rectangle_is_clique (hG : IntervalLabeling G)
    (X Y : Finset (Fin N)) (hX : X.Nonempty) (hY : Y.Nonempty)
    (hXY : ∀x∈X, ∀y∈Y, x<y ∧ G.Adj x y)
    {u v : Fin N} (hu : u∈X∪Y) (hv : v∈X∪Y) (huv : u≠v) : G.Adj u v := by
  obtain ⟨x,hx⟩ := hX
  obtain ⟨y,hy⟩ := hY
  rcases Finset.mem_union.mp hu with hu | hu
  · rcases Finset.mem_union.mp hv with hv | hv
    · rcases lt_or_gt_of_ne huv with huv | hvu
      · exact interval_adj_right hG (hXY u hu y hy).2 huv (hXY v hv y hy).1.le
      · exact (interval_adj_right hG (hXY v hv y hy).2 hvu (hXY u hu y hy).1.le).symm
    · exact (hXY u hu v hv).2
  · rcases Finset.mem_union.mp hv with hv | hv
    · exact (hXY v hv u hu).2.symm
    · rcases lt_or_gt_of_ne huv with huv | hvu
      · exact interval_adj_left hG (hXY x hx v hv).2 (hXY x hx u hu).1.le huv
      · exact (interval_adj_left hG (hXY x hx u hu).2 (hXY x hx v hv).1.le hvu).symm

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphRectangleStep -/
section

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096

noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {k : Type u} [CommRing k]
variable {N : ℕ} {G : SimpleGraph (Fin N)}

def graphRowPart (F : Finset (FiniteVariable.{u} (GraphRows N))) (r : Fin 2) :=
  F.filter (fun v => v.1 = r)

lemma graphVariable_eq_of_row (v : FiniteVariable.{u} (GraphRows N)) (r : Fin 2)
    (hv : v.1 = r) : v = ⟨r, ULift.up v.2.down⟩ := by
  rcases v with ⟨s, ⟨i⟩⟩
  change s = r at hv
  subst s
  rfl

lemma graphRowParts_union (F : Finset (FiniteVariable.{u} (GraphRows N))) :
    graphRowPart F 0 ∪ graphRowPart F 1 = F := by
  ext v
  have hr : v.1 = 0 ∨ v.1 = 1 := by omega
  simp only [graphRowPart, Finset.mem_union, Finset.mem_filter]
  tauto

lemma graphRowParts_disjoint (F : Finset (FiniteVariable.{u} (GraphRows N))) :
    Disjoint (graphRowPart F 0) (graphRowPart F 1) := by
  apply Finset.disjoint_left.mpr
  intro v hv0 hv1
  have h0 := (Finset.mem_filter.mp hv0).2
  have h1 := (Finset.mem_filter.mp hv1).2
  omega

lemma graphColon_not_mem_distinguished (a : FiniteTuple (GraphRows N)) (r : Fin 2) :
    (⟨r, ULift.up (a r)⟩ : FiniteVariable.{u} (GraphRows N)) ∉ graphLinearVariables G a := by
  fin_cases r
  · simp [graphLinearVariables_mem_x]
  · simp [graphLinearVariables_mem_y]

/-- The new linear generator adjoining the distinguished edge in the colon
recursion. Both nonempty row sets and all original graph edges are explicit. -/
def graphColonRectangle (hG : IntervalLabeling G)
    {a : FiniteTuple (GraphRows N)} (ha : a ∈ graphEdgeLattice G)
    (F : Finset (FiniteVariable.{u} (GraphRows N)))
    (hF : ∀ v ∈ F, v ∈ graphLinearVariables G a) :
    GraphRectangle.{u} G (fun _ => Finset.univ) where
  X := insert ⟨0, ULift.up (a 0)⟩ (graphRowPart F 0)
  Y := insert ⟨1, ULift.up (a 1)⟩ (graphRowPart F 1)
  nonemptyX := Finset.insert_nonempty _ _
  nonemptyY := Finset.insert_nonempty _ _
  rowX := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · rfl
    · exact (Finset.mem_filter.mp hv).2
  rowY := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · rfl
    · exact (Finset.mem_filter.mp hv).2
  retainedX := by intro v hv; exact Finset.mem_univ _
  retainedY := by intro v hv; exact Finset.mem_univ _
  edges := by
    intro x hx y hy
    apply graphColon_rectangle_edges hG ha
    · rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Or.inl rfl
      · refine Or.inr ?_
        rw [← graphVariable_eq_of_row x 0 (Finset.mem_filter.mp hx).2]
        exact hF x (Finset.mem_filter.mp hx).1
    · rcases Finset.mem_insert.mp hy with rfl | hy
      · exact Or.inl rfl
      · refine Or.inr ?_
        rw [← graphVariable_eq_of_row y 1 (Finset.mem_filter.mp hy).2]
        exact hF y (Finset.mem_filter.mp hy).1

lemma graphColonRectangle_union (hG : IntervalLabeling G)
    {a : FiniteTuple (GraphRows N)} (ha : a ∈ graphEdgeLattice G)
    (F : Finset (FiniteVariable.{u} (GraphRows N)))
    (hF : ∀ v ∈ F, v ∈ graphLinearVariables G a) :
    (graphColonRectangle hG ha F hF).X ∪ (graphColonRectangle hG ha F hF).Y =
      insert ⟨0, ULift.up (a 0)⟩ (insert ⟨1, ULift.up (a 1)⟩ F) := by
  change (insert _ (graphRowPart F 0)) ∪ (insert _ (graphRowPart F 1)) = _
  rw [Finset.insert_union, Finset.union_insert, graphRowParts_union]

lemma graphColonRectangle_fineDegree (hG : IntervalLabeling G)
    {a : FiniteTuple (GraphRows N)} (ha : a ∈ graphEdgeLattice G)
    (F : Finset (FiniteVariable.{u} (GraphRows N)))
    (hF : ∀ v ∈ F, v ∈ graphLinearVariables G a) :
    (graphColonRectangle hG ha F hF).fineDegree =
      finiteRowExponent (GraphRows N) a + faceExponent F := by
  let e : FiniteVariable.{u} (GraphRows N) := ⟨0, ULift.up (a 0)⟩
  let f : FiniteVariable.{u} (GraphRows N) := ⟨1, ULift.up (a 1)⟩
  have hef : e ≠ f := by intro h; have := congrArg Sigma.fst h; simp [e, f] at this
  have he : e ∉ F := fun h => graphColon_not_mem_distinguished a 0 (hF e h)
  have hf : f ∉ F := fun h => graphColon_not_mem_distinguished a 1 (hF f h)
  have hrow : finiteRowExponent (GraphRows N) a = Finsupp.single e 1 + Finsupp.single f 1 := by
    simpa only [e, f, graphTuple_eta] using graphRowExponent_pair e f rfl rfl
  rw [hrow]
  ext v
  simp only [GraphRectangle.fineDegree, rectangleFaceDegree, faceExponent_apply,
    graphColonRectangle, Finset.mem_union, Finset.mem_insert, graphRowPart,
    Finset.mem_filter, Finsupp.add_apply]
  dsimp only [e, f] at he hf hef
  by_cases hve : v = e
  · subst v
    simp [e, f, Finsupp.single_apply, he, hef, hef.symm]
  · by_cases hvf : v = f
    · subst v
      simp [e, f, Finsupp.single_apply, hf, hef, hef.symm]
    · have hr : v.1 = 0 ∨ v.1 = 1 := by omega
      dsimp only [e, f] at hve hvf
      rcases hr with hr | hr <;>
        simp [e, f, Finsupp.single_apply, hve, hvf, Ne.symm hve, Ne.symm hvf, hr]

lemma graphColonRectangle_degree_decomposition (hG : IntervalLabeling G)
    {a : FiniteTuple (GraphRows N)} (ha : a ∈ graphEdgeLattice G)
    (γ : Exponent (FiniteVariable.{u} (GraphRows N)))
    (hsq : ∀ v, γ v ≤ 1) :
    (graphColonRectangle hG ha (graphColonLinearDegree G a γ).support
      (graphColonLinear_support a γ)).fineDegree + graphColonResidualDegree G a γ =
      finiteRowExponent (GraphRows N) a + γ := by
  have hs : faceExponent (graphColonLinearDegree G a γ).support =
      graphColonLinearDegree G a γ :=
    squarefreeExponent_eq_faceExponent_support _ (squarefreeExponent_filter γ hsq _)
  rw [graphColonRectangle_fineDegree, add_assoc, hs, graphColonDegree_add]

variable {V : Type u} [Fintype V] [LinearOrder V]

lemma creation_basis_scalar (e : V) (F : Finset V) (he : e ∉ F) :
    ∃ c : k, IsUnit c ∧
      Simplicial.creation e (Simplicial.basis (k := k) F) = c • Simplicial.basis (insert e F) := by
  let s := TauCeti.ExteriorAlgebra.basisEraseSign e (insert e F)
  refine ⟨((s : ℤ) : k), s.isUnit.map (Int.castRingHom k), ?_⟩
  rw [Simplicial.creation_basis, if_neg he]
  change (s : ℤ) • Simplicial.basis (k := k) (insert e F) =
    ((s : ℤ) : k) • Simplicial.basis (k := k) (insert e F)
  exact (Int.cast_smul_eq_zsmul k (s : ℤ) (Simplicial.basis (k := k) (insert e F))).symm

lemma faceBasis_product_scalar (F H : Finset V) (hFH : Disjoint F H) :
    ∃ c : k, IsUnit c ∧ Simplicial.basis (k := k) F * Simplicial.basis H =
      c • Simplicial.basis (F ∪ H) := by
  let s := faceWedgeSign F H hFH
  refine ⟨((s : ℤ) : k), s.isUnit.map (Int.castRingHom k), ?_⟩
  rw [faceBasis_mul_of_disjoint F H hFH]
  change (s : ℤ) • Simplicial.basis (k := k) (F ∪ H) =
    ((s : ℤ) : k) • Simplicial.basis (k := k) (F ∪ H)
  exact (Int.cast_smul_eq_zsmul k (s : ℤ) (Simplicial.basis (k := k) (F ∪ H))).symm

/-- The connecting image of the new rectangle is the fixed colon factor,
up to two explicit invertible sign scalars. Keeping both scalars avoids
division in the coefficient ring and includes characteristic two. -/
theorem graphColonRectangle_connecting_scaled (hG : IntervalLabeling G)
    {a : FiniteTuple (GraphRows N)} (ha : a ∈ graphEdgeLattice G)
    (F : Finset (FiniteVariable.{u} (GraphRows N)))
    (hF : ∀ v ∈ F, v ∈ graphLinearVariables G a)
    (B : Family (FiniteVariable.{u} (GraphRows N)))
    (γ : Exponent (FiniteVariable.{u} (GraphRows N)))
    (he : γ ⟨0, ULift.up (a 0)⟩ = 0) (hf : γ ⟨1, ULift.up (a 1)⟩ = 0)
    (r : Simplicial.Ambient (FiniteVariable.{u} (GraphRows N)) k) :
    ∃ ε η : k, IsUnit ε ∧ IsUnit η ∧
      ε • quotientFaceProjection B γ
        (Simplicial.boundary ((graphColonRectangle hG ha F hF).vector * r)) =
      η • quotientFaceProjection B γ (Simplicial.basis F * r) := by
  let e : FiniteVariable.{u} (GraphRows N) := ⟨0, ULift.up (a 0)⟩
  let f : FiniteVariable.{u} (GraphRows N) := ⟨1, ULift.up (a 1)⟩
  let U := graphRowPart F 0
  let W := graphRowPart F 1
  have heu : e ∉ U := fun h => graphColon_not_mem_distinguished a 0
    (hF e (Finset.mem_filter.mp h).1)
  have hfw : f ∉ W := fun h => graphColon_not_mem_distinguished a 1
    (hF f (Finset.mem_filter.mp h).1)
  obtain ⟨cx, hcx, hx⟩ := creation_basis_scalar (k := k) e U heu
  obtain ⟨cy, hcy, hy⟩ := creation_basis_scalar (k := k) f W hfw
  obtain ⟨cw, hcw, hw⟩ := faceBasis_product_scalar (k := k) U W (graphRowParts_disjoint F)
  letI : DecidableEq (FiniteVariable.{u} (GraphRows N)) :=
    (inferInstance : LinearOrder (FiniteVariable.{u} (GraphRows N))).toDecidableEq
  have huw : U ∪ W = F := by
    ext v
    have hr : v.1 = 0 ∨ v.1 = 1 := by omega
    simp only [Finset.mem_union, U, W, graphRowPart, Finset.mem_filter]
    tauto
  rw [huw] at hw
  have hvec : distinguishedRectangleVector e f (Simplicial.basis (k := k) U)
      (Simplicial.basis W) = (cx * cy) • (graphColonRectangle hG ha F hF).vector := by
    rw [distinguishedRectangleVector, hx, hy, map_smul, smul_mul_smul_comm]
    have hxset : insert e U = (graphColonRectangle hG ha F hF).X := by
      ext v
      simp only [graphColonRectangle, Finset.mem_insert, e, U]
    have hyset : insert f W = (graphColonRectangle hG ha F hF).Y := by
      ext v
      simp only [graphColonRectangle, Finset.mem_insert, f, W]
    rw [hxset, hyset]
    rfl
  refine ⟨cx * cy, (-1 : k)^U.card * cw, hcx.mul hcy,
    ((IsUnit.neg isUnit_one).pow U.card).mul hcw, ?_⟩
  have h := distinguishedRectangle_connecting_projection B γ e f he hf
    (Simplicial.basis (k := k) U) (Simplicial.basis W) r
  have hi : CliffordAlgebra.involute (Simplicial.basis (k := k) U) =
      (-1 : k)^U.card • Simplicial.basis U :=
    TauCeti.ExteriorAlgebra.involute_basis (Pi.basisFun k _) U
  rw [hvec, smul_mul_assoc, map_smul, map_smul, hi, smul_mul_assoc,
    hw, smul_smul, smul_mul_assoc, map_smul] at h
  exact h

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphConnecting -/
section

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096

noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

/-- The kernel of the literal quotient projection is the ideal strand.
This assertion uses the ordinary polynomial Koszul coordinates. -/
lemma quotientProjection_zero_mem_ideal (B : Family V) (α : Exponent V)
    {x : Simplicial.Ambient V k}
    (hx : x ∈ TotalFaceModule (fullKoszulFaces α))
    (hq : quotientFaceProjection B α x = 0) :
    x ∈ TotalFaceModule (koszulFaces B α) := by
  have h := (basisSpan (Simplicial.basis (k := k))
    (fun F => fullKoszulFaces α F ∧ forbiddenKoszulFaces B α F)).neg_mem
      (relativeProjection_sub_mem_full_discarded (Simplicial.basis (k := k))
        (fullKoszulFaces α) (forbiddenKoszulFaces B α) hx)
  change -(quotientFaceProjection B α x - x) ∈ TotalFaceModule (koszulFaces B α) at h
  simpa only [hq, zero_sub, neg_neg] using h

/-- A quotient cycle whose connecting cycle bounds in the ideal itself
bounds in the quotient. The proof is an explicit ambient contraction. -/
theorem quotientCycle_boundary_of_total_ideal_filling
    (B : Family V) (α : Exponent V) (e : V) (he : 0 < α e)
    (z : TotalFaceModule (k := k) (quotientKoszulFaces B α))
    (a : TotalFaceModule (k := k) (koszulFaces B α))
    (ha : Simplicial.boundary a.val = Simplicial.boundary z.val) :
    ∃ y : TotalFaceModule (k := k) (quotientKoszulFaces B α),
      quotientTotalDifferential B α y = z := by
  have hzfull : z.val ∈ TotalFaceModule (fullKoszulFaces α) :=
    Submodule.span_mono (Set.image_mono (fun _ hs => hs.1)) z.property
  have hafull : a.val ∈ TotalFaceModule (fullKoszulFaces α) :=
    Submodule.span_mono (Set.image_mono (fun _ hs => hs.1)) a.property
  have hclosed : Simplicial.boundary (z.val - a.val) = 0 := by
    rw [map_sub, ha, sub_self]
  have hcreation : Simplicial.creation e (z.val - a.val) ∈
      TotalFaceModule (fullKoszulFaces α) :=
    creation_mem_basisSpan e (fun _ hs => fullKoszulFaces_insert he hs)
      (Submodule.sub_mem _ hzfull hafull)
  refine ⟨⟨quotientFaceProjection B α (Simplicial.creation e (z.val - a.val)),
    relativeProjection_mem _ _ _ _⟩, ?_⟩
  apply Subtype.ext
  change quotientFaceProjection B α (Simplicial.boundary
    (quotientFaceProjection B α (Simplicial.creation e (z.val - a.val)))) = z.val
  rw [quotientFaceProjection_boundary B α hcreation,
    Simplicial.boundary_creation, hclosed, map_zero, sub_zero, map_sub,
    quotientFaceProjection_zero_on_ideal B α a.property, sub_zero]
  exact relativeProjection_eq_self z.property

variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

/-- For positive fine degree with maximum `a`, the connecting map from the
quotient to the actual predecessor quotient detects boundaries. This is the
map used to reduce the graph induction to a smaller variable restriction. -/
theorem firstPowerQuotientCycle_boundary_of_colon_filling
    (hE : finiteLatticeClosed n E)
    {α : Exponent (FiniteVariable.{u} n)} {a : E}
    (hα : RowMaximum α a.val)
    (e : FiniteVariable.{u} n) (he : 0 < α e)
    (z : TotalFaceModule (k := k) (quotientKoszulFaces
      (exponentPowerFamily (finiteRowFamily n E) 1) α))
    (hz : quotientTotalDifferential
      (exponentPowerFamily (finiteRowFamily n E) 1) α z = 0)
    (hfill : ∃ y : TotalFaceModule (k := k)
      (quotientKoszulFaces (finitePredecessorFamily n E a.val)
        (α - finiteRowExponent n a.val)),
      (quotientTotalDifferential (finitePredecessorFamily n E a.val)
        (α - finiteRowExponent n a.val) y).val =
      quotientFaceProjection (finitePredecessorFamily n E a.val)
        (α - finiteRowExponent n a.val) (Simplicial.boundary z.val)) :
    ∃ y, quotientTotalDifferential
      (exponentPowerFamily (finiteRowFamily n E) 1) α y = z := by
  let B := exponentPowerFamily (finiteRowFamily n E) 1
  have hzfull : z.val ∈ TotalFaceModule (fullKoszulFaces α) :=
    Submodule.span_mono (Set.image_mono (fun _ hs => hs.1)) z.property
  have hdideal : Simplicial.boundary z.val ∈ TotalFaceModule (koszulFaces B α) :=
    quotientProjection_zero_mem_ideal B α
      (boundary_mem_basisSpan (fullKoszulFaces_downward α) hzfull)
      (congrArg Subtype.val hz)
  let dz : TotalFaceModule (k := k) (koszulFaces B α) :=
    ⟨Simplicial.boundary z.val, hdideal⟩
  have hdz : idealTotalDifferential (koszulFaces_downward B α) dz = 0 := by
    apply Subtype.ext
    exact Simplicial.boundary_boundary z.val
  have hcolon : ∃ y, quotientTotalDifferential (finitePredecessorFamily n E a.val)
      (α - finiteRowExponent n a.val) y = firstPowerFaceProjection hE hα dz := by
    obtain ⟨y, hy⟩ := hfill
    refine ⟨y, ?_⟩
    apply Subtype.ext
    rw [firstPowerFaceProjection_val]
    exact hy
  obtain ⟨w, hw⟩ := (firstPowerFaceCycle_boundary_iff hE hα dz hdz).mpr hcolon
  exact quotientCycle_boundary_of_total_ideal_filling B α e he z w
    (congrArg Subtype.val hw)

/-- The literal connecting-coordinate map: take the ordinary exterior
boundary and then the predecessor quotient projection. It is defined on the
entire quotient coordinate module; its cycle property is proved below. -/
def quotientConnectingProjection (B C : Family V) (α γ : Exponent V) :
    TotalFaceModule (k := k) (quotientKoszulFaces B α) →ₗ[k]
      TotalFaceModule (k := k) (quotientKoszulFaces C γ) :=
  LinearMap.codRestrict _
    ((quotientFaceProjection C γ).comp
      (Simplicial.boundary.comp (TotalFaceModule (k := k)
        (quotientKoszulFaces B α)).subtype))
    (fun x => relativeProjection_mem _ _ _ _)

@[simp] lemma quotientConnectingProjection_val (B C : Family V) (α γ : Exponent V)
    (x : TotalFaceModule (k := k) (quotientKoszulFaces B α)) :
    (quotientConnectingProjection B C α γ x).val =
      quotientFaceProjection C γ (Simplicial.boundary x.val) := rfl

theorem firstPowerConnecting_cycle (hE : finiteLatticeClosed n E)
    {α : Exponent (FiniteVariable.{u} n)} {a : E} (hα : RowMaximum α a.val)
    (z : TotalFaceModule (k := k) (quotientKoszulFaces (finiteRowFamily n E) α))
    (hz : quotientTotalDifferential (finiteRowFamily n E) α z = 0) :
    quotientTotalDifferential (finitePredecessorFamily n E a.val)
      (α - finiteRowExponent n a.val)
      (quotientConnectingProjection (finiteRowFamily n E) (finitePredecessorFamily n E a.val)
        α (α - finiteRowExponent n a.val) z) = 0 := by
  have hzfull : z.val ∈ TotalFaceModule (fullKoszulFaces α) :=
    Submodule.span_mono (Set.image_mono (fun _ hs => hs.1)) z.property
  have hdideal := quotientProjection_zero_mem_ideal (finiteRowFamily n E) α
    (boundary_mem_basisSpan (fullKoszulFaces_downward α) hzfull)
    (congrArg Subtype.val hz)
  let dz : TotalFaceModule (k := k)
      (koszulFaces (exponentPowerFamily (finiteRowFamily n E) 1) α) :=
    ⟨Simplicial.boundary z.val, by simpa only [exponentPowerFamily_one] using hdideal⟩
  have hdz : idealTotalDifferential
      (koszulFaces_downward (exponentPowerFamily (finiteRowFamily n E) 1) α) dz = 0 := by
    apply Subtype.ext
    exact Simplicial.boundary_boundary z.val
  have heq : firstPowerFaceProjection hE hα dz =
      quotientConnectingProjection (finiteRowFamily n E) (finitePredecessorFamily n E a.val)
        α (α - finiteRowExponent n a.val) z := by
    apply Subtype.ext
    rw [firstPowerFaceProjection_val]
    rfl
  rw [← heq, ← firstPowerFaceProjection_differential, hdz, map_zero]

theorem firstPowerConnecting_detects_boundaries (hE : finiteLatticeClosed n E)
    {α : Exponent (FiniteVariable.{u} n)} {a : E} (hα : RowMaximum α a.val)
    (e : FiniteVariable.{u} n) (he : 0 < α e)
    (z : TotalFaceModule (k := k) (quotientKoszulFaces (finiteRowFamily n E) α))
    (hz : quotientTotalDifferential (finiteRowFamily n E) α z = 0)
    (hfill : ∃ y, quotientTotalDifferential (finitePredecessorFamily n E a.val)
      (α - finiteRowExponent n a.val) y =
      quotientConnectingProjection (finiteRowFamily n E) (finitePredecessorFamily n E a.val)
        α (α - finiteRowExponent n a.val) z) :
    ∃ y, quotientTotalDifferential (finiteRowFamily n E) α y = z := by
  have h := firstPowerQuotientCycle_boundary_of_colon_filling (k := k) hE hα e he
  rw [exponentPowerFamily_one_of_decidable] at h
  apply h z hz
  obtain ⟨y, hy⟩ := hfill
  exact ⟨y, congrArg Subtype.val hy⟩

end FourPapers.Sublattice

namespace FourPapers.Sublattice
variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N]

/-- A connecting map may change homological degree and anticommute with the
differential. Only cycle preservation and proved boundary detection are needed
to transport a generating set. -/
theorem cycle_spanning_of_connecting_detection
    (D : Module.End R M) (d : Module.End R N) (q : M →ₗ[R] N)
    (hcycle : ∀ x, D x = 0 → d (q x) = 0)
    (hdetect : ∀ x, D x = 0 → (∃ y, d y = q x) → ∃ y, D y = x)
    (G : Set M) (hG : G ⊆ LinearMap.ker D)
    (hspan : LinearMap.ker d ≤ (Submodule.span R G).map q ⊔ LinearMap.range d) :
    LinearMap.ker D ≤ Submodule.span R G ⊔ LinearMap.range D := by
  intro z hz
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (hspan (hcycle z hz))
  obtain ⟨x, hx, hqx⟩ := ha
  have hxclosed : D x = 0 := (Submodule.span_le.mpr hG) hx
  have hclosed : D (z - x) = 0 := by
    rw [map_sub, show D z = 0 from hz, hxclosed, sub_self]
  have hproj : ∃ y, d y = q (z - x) := by
    obtain ⟨y, hy⟩ := hb
    refine ⟨y, ?_⟩
    rw [map_sub, hqx, ← hab, add_sub_cancel_left]
    exact hy
  obtain ⟨y, hy⟩ := hdetect (z - x) hclosed hproj
  exact Submodule.mem_sup.mpr ⟨x, hx, z - x, ⟨y, hy⟩, by abel⟩

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphContractions -/
section

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096

noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

/-- If every diagonal coefficient block contracts, a strictly lowering
perturbation of their direct sum contracts as well. The block homotopies
preserve block weight, so the existing integral triangular inverse applies. -/
lemma closedGraph_block_cycle_boundary
    {K B : Type*} [CommRing K] {M : B → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)] {J : B → Type*}
    (b : ∀ i, Module.Basis (J i) K (M i)) (rank : B → ℕ)
    (D : Module.End K (Π₀ i, M i)) (dB H : ∀ i, Module.End K (M i))
    (hD : D * D = 0) (hdB : ∀ i, dB i * dB i = 0)
    (hH : ∀ i, dB i * H i + H i * dB i = 1)
    (hlow : ∀ i j : Sigma J, rank i.1 ≤ rank j.1 →
      (DFinsupp.basis b).repr ((D - blockSpecialDifferential dB)
        ((DFinsupp.basis b) i)) j = 0)
    (x : Π₀ i, M i) (hx : D x = 0) : ∃ y, D y = x := by
  let h : Module.End K (Π₀ i, M i) := DFinsupp.mapRange.linearMap H
  have hh : blockSpecialDifferential dB * h + h * blockSpecialDifferential dB = 1 := by
    apply LinearMap.ext
    intro z
    apply DFinsupp.ext
    intro i
    exact LinearMap.congr_fun (hH i) (z i)
  have hl : ∀ i j : Sigma J, rank i.1 ≤ rank j.1 →
      (DFinsupp.basis b).repr ((D - blockSpecialDifferential dB)
        (h ((DFinsupp.basis b) i))) j = 0 :=
    lower_after_weight_preserving (DFinsupp.basis b) (fun i => rank i.1)
      (D - blockSpecialDifferential dB) h hlow (blockMap_basis_weight b rank H)
  let T := h * (perturbationEquiv (DFinsupp.basis b) (fun i => rank i.1)
    D (blockSpecialDifferential dB) h hl).symm.toLinearMap
  have hc : D * T + T * D = 1 := lowerPerturbation_contracts
    (DFinsupp.basis b) (fun i => rank i.1) D (blockSpecialDifferential dB) h
    hD (blockSpecialDifferential_square_zero dB hdB) hh hl
  refine ⟨T x, ?_⟩
  have hc' := LinearMap.congr_fun hc x
  change D (T x) + T (D x) = x at hc'
  simpa only [hx, map_zero, add_zero] using hc'

/-- If the coordinatewise row maximum is absent from the lattice, every
first-power block contracts, including blocks below incomparable generators.
This argument uses only the first-power normal form and its strict triangular
differential; it does not invoke the all-powers decomposition. -/
theorem firstPowerTotalCycle_boundary_of_missing_maximum
    (hE : finiteLatticeClosed n E)
    {α : Exponent (FiniteVariable.{u} n)} {a : FiniteTuple n}
    (hα : RowMaximum α a) (ha : a ∉ E)
    (x : TotalFaceModule (k := k)
      (koszulFaces (exponentPowerFamily (finiteRowFamily n E) 1) α))
    (hx : idealTotalDifferential
      (koszulFaces_downward (exponentPowerFamily (finiteRowFamily n E) 1) α) x = 0) :
    ∃ y, idealTotalDifferential
      (koszulFaces_downward (exponentPowerFamily (finiteRowFamily n E) 1) α) y = x := by
  let b := fun w : AdmissibleChain n E 1 α => totalFaceBasis (k := k)
    (quotientKoszulFaces (finiteChainCoefficientFamily n w.val)
      (α - finiteChainShift n w.val))
  let rank := fun w : AdmissibleChain n E 1 α => finiteChainFactorWeight.{u} w.val
  let dB := fun w : AdmissibleChain n E 1 α => quotientTotalDifferential (k := k)
    (finiteChainCoefficientFamily n w.val) (α - finiteChainShift n w.val)
  have hcontract : ∀ w : AdmissibleChain n E 1 α,
      ∃ H : Module.End k (TotalFaceModule (k := k)
        (quotientKoszulFaces (finiteChainCoefficientFamily n w.val)
          (α - finiteChainShift n w.val))), dB w * H + H * dB w = 1 := by
    intro w
    let c : E := w.val.val 0
    have he : singletonChain c = w.val := singletonChain_eq w.val
    have hc : finiteRowExponent n c.val ≤ α := by
      simpa only [← he, singletonChain_shift] using w.property
    have hca : c.val ≠ a := by
      intro h
      exact ha (h ▸ c.property)
    have hcoef : finiteChainCoefficientFamily.{u} n w.val =
        finitePredecessorFamily n E c.val := by rw [← he, singletonChain_coefficient]
    have hshift : finiteChainShift.{u} n w.val = finiteRowExponent n c.val := by
      rw [← he, singletonChain_shift]
    dsimp only [dB]
    rw [hcoef, hshift]
    obtain ⟨H, hH, _⟩ := firstPowerBlock_contractible_of_distinct_maximum (k := k) hE hα hc hca
    exact ⟨H, hH⟩
  let H := fun w : AdmissibleChain n E 1 α => (hcontract w).choose
  let t := chainTotalEquiv hE 1 α k
  have hx' : chainTotalOrdinaryDifferential hE 1 α k (t.symm x) = 0 := by
    simp only [chainTotalOrdinaryDifferential, LinearMap.comp_apply, LinearEquiv.coe_coe,
      t, LinearEquiv.apply_symm_apply, hx, map_zero]
  obtain ⟨y, hy⟩ := closedGraph_block_cycle_boundary b rank
    (chainTotalOrdinaryDifferential hE 1 α k) dB H
    (chainTotalOrdinaryDifferential_square_zero hE 1 α k)
    (fun w => quotientTotalDifferential_comp _ _)
    (fun w => (hcontract w).choose_spec)
    (chainTotalDifferential_strictLower hE 1 α k) (t.symm x) hx'
  refine ⟨t y, ?_⟩
  have h := congrArg t hy
  simpa only [chainTotalOrdinaryDifferential, LinearMap.comp_apply, LinearEquiv.coe_coe,
    t, LinearEquiv.apply_symm_apply] using h

theorem firstPowerQuotientCycle_boundary_of_missing_maximum
    (hE : finiteLatticeClosed n E)
    {α : Exponent (FiniteVariable.{u} n)} {a : FiniteTuple n}
    (hα : RowMaximum α a) (ha : a ∉ E)
    (e : FiniteVariable.{u} n) (he : 0 < α e)
    (z : TotalFaceModule (k := k) (quotientKoszulFaces (finiteRowFamily n E) α))
    (hz : quotientTotalDifferential (finiteRowFamily n E) α z = 0) :
    ∃ y, quotientTotalDifferential (finiteRowFamily n E) α y = z := by
  have hzfull : z.val ∈ TotalFaceModule (fullKoszulFaces α) :=
    Submodule.span_mono (Set.image_mono (fun _ hs => hs.1)) z.property
  have hdideal := quotientProjection_zero_mem_ideal (finiteRowFamily n E) α
    (boundary_mem_basisSpan (fullKoszulFaces_downward α) hzfull)
    (congrArg Subtype.val hz)
  let dz : TotalFaceModule (k := k) (koszulFaces (finiteRowFamily n E) α) :=
    ⟨Simplicial.boundary z.val, hdideal⟩
  have hdz : idealTotalDifferential (koszulFaces_downward (finiteRowFamily n E) α) dz = 0 := by
    apply Subtype.ext
    exact Simplicial.boundary_boundary z.val
  have hfill := firstPowerTotalCycle_boundary_of_missing_maximum (k := k) hE hα ha
  rw [exponentPowerFamily_one_of_decidable] at hfill
  obtain ⟨w, hw⟩ := hfill dz hdz
  exact quotientCycle_boundary_of_total_ideal_filling (finiteRowFamily n E) α e he z w
    (congrArg Subtype.val hw)

/-- Every fine degree containing a row generator has actual row maxima.
The maxima are chosen from the finite supports; no nonempty row convention
or extra graph hypothesis is implicit. -/
theorem rowMaximum_exists_of_generator
    (α : Exponent (FiniteVariable.{u} n))
    {b : FiniteTuple n} (hb : finiteRowExponent n b ≤ α) :
    ∃ a : FiniteTuple n, RowMaximum α a := by
  let S : ∀ r, Finset (Fin (n r)) := fun r =>
    Finset.univ.filter (fun j => 0 < α ⟨r, ULift.up j⟩)
  have hS : ∀ r, (S r).Nonempty := by
    intro r
    refine ⟨b r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    have h := hb ⟨r, ULift.up (b r)⟩
    simpa only [finiteRowExponent_apply, ite_true, Nat.succ_le_iff] using h
  let a : FiniteTuple n := fun r => (S r).max' (hS r)
  refine ⟨a, ?_, ?_⟩
  · rintro ⟨r, ⟨j⟩⟩
    rw [finiteRowExponent_apply]
    by_cases h : a r = j
    · rw [if_pos h]
      have hj : j ∈ S r := h ▸ Finset.max'_mem (S r) (hS r)
      exact Nat.succ_le_iff.mpr (Finset.mem_filter.mp hj).2
    · rw [if_neg h]
      exact Nat.zero_le _
  · rintro ⟨r, ⟨j⟩⟩ hj
    apply Finset.le_max'
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.pos_of_ne_zero hj⟩

variable {V : Type u} [Fintype V] [LinearOrder V]

lemma idealFaceModule_eq_bot_of_not_contains (B : Family V) (α : Exponent V)
    (hα : ¬Contains B α) : TotalFaceModule (k := k) (koszulFaces B α) = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro x ⟨F, hF, rfl⟩
  obtain ⟨b, hb, hbα⟩ := hF.2
  exact (hα ⟨b, hb, hbα.trans tsub_le_self⟩).elim

theorem quotientCycle_boundary_of_not_contains (B : Family V) (α : Exponent V)
    (hα : ¬Contains B α) (e : V) (he : 0 < α e)
    (z : TotalFaceModule (k := k) (quotientKoszulFaces B α))
    (hz : quotientTotalDifferential B α z = 0) :
    ∃ y, quotientTotalDifferential B α y = z := by
  have hzfull : z.val ∈ TotalFaceModule (fullKoszulFaces α) :=
    Submodule.span_mono (Set.image_mono (fun _ hs => hs.1)) z.property
  have hdideal := quotientProjection_zero_mem_ideal B α
    (boundary_mem_basisSpan (fullKoszulFaces_downward α) hzfull)
    (congrArg Subtype.val hz)
  rw [idealFaceModule_eq_bot_of_not_contains B α hα, Submodule.mem_bot] at hdideal
  exact quotientCycle_boundary_of_total_ideal_filling B α e he z 0
    (by simpa only [ZeroMemClass.coe_zero, map_zero] using hdideal.symm)

end FourPapers.Sublattice

end
end
end


end
