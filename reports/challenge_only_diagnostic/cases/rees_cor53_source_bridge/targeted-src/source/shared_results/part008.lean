module
public import graph_foundation.part009
public import shared_results.part007

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphSpanning -/
section

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {k : Type u} [CommRing k]
variable {N : ℕ} {G : SimpleGraph (Fin N)}

/-- The product representative in the unrelabelled original graph family.
The only conversion from the earlier restricted-family interface is the
proved equality of restriction to all variables with the original family. -/
def closedGraphProduct (α : Exponent (FiniteVariable.{u} (GraphRows N)))
    (L : {L : List (GraphRectangle.{u} G (fun _ => Finset.univ)) //
      graphRectangleListDegree L = α}) :
    TotalFaceModule (k := k)
      (quotientKoszulFaces (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) α) :=
  ⟨graphRectangleListVector L.val, by
    simpa only [graphRestrictedFamily, finiteRowRestriction_univ, L.property] using
      graphRectangleListVector_mem (k := k) L.val⟩

@[simp] lemma closedGraphProduct_val
    (α : Exponent (FiniteVariable.{u} (GraphRows N)))
    (L : {L : List (GraphRectangle.{u} G (fun _ => Finset.univ)) //
      graphRectangleListDegree L = α}) :
    (closedGraphProduct (k := k) α L).val = graphRectangleListVector L.val := rfl

def closedGraphProductSpan (G : SimpleGraph (Fin N))
    (α : Exponent (FiniteVariable.{u} (GraphRows N))) :
    Submodule k (TotalFaceModule (k := k)
      (quotientKoszulFaces (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) α)) :=
  Submodule.span k (Set.range (closedGraphProduct (G := G) (k := k) α))

lemma closedGraphProduct_closed (α : Exponent (FiniteVariable.{u} (GraphRows N)))
    (L : {L : List (GraphRectangle.{u} G (fun _ => Finset.univ)) //
      graphRectangleListDegree L = α}) :
    quotientTotalDifferential (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) α
      (closedGraphProduct (k := k) α L) = 0 := by
  apply Subtype.ext
  change quotientFaceProjection (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) α
    (Simplicial.boundary (graphRectangleListVector (k := k) L.val)) = 0
  simpa only [graphRestrictedFamily, finiteRowRestriction_univ, L.property] using
    graphRectangleListVector_closed (k := k) L.val

lemma closedGraphProductSpan_le_cycles (α : Exponent (FiniteVariable.{u} (GraphRows N))) :
    closedGraphProductSpan (k := k) G α ≤
      LinearMap.ker (quotientTotalDifferential
        (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) α) := by
  apply Submodule.span_le.mpr
  rintro x ⟨L, rfl⟩
  exact closedGraphProduct_closed α L

lemma closedGraph_zero_degree_span
    (z : TotalFaceModule (k := k)
      (quotientKoszulFaces (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) 0)) :
    z ∈ closedGraphProductSpan (k := k) G 0 := by
  let Q := quotientKoszulFaces (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) 0
  let P := closedGraphProductSpan (k := k) G 0
  have hz : z.val ∈ P.map (TotalFaceModule (k := k) Q).subtype := by
    apply (Submodule.span_le.mpr ?_) z.property
    rintro x ⟨F, hF, rfl⟩
    have hF0 : F = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      have h := hF.1 v
      simp [faceExponent_apply, hv] at h
    subst F
    refine ⟨closedGraphProduct (k := k) 0 ⟨[], rfl⟩,
      Submodule.subset_span ⟨⟨[], rfl⟩, rfl⟩, ?_⟩
    simp only [Submodule.subtype_apply, closedGraphProduct_val,
      graphRectangleListVector, List.map_nil, List.prod_nil, faceBasis_empty]
  obtain ⟨w, hw, hwz⟩ := hz
  have h : w = z := Subtype.ext hwz
  exact h ▸ hw

/-- Each product from the strictly smaller residual strand has an actual
product preimage under the colon connecting map, up to an invertible sign.
This assertion constructs that preimage, rather than assuming liftability. -/
theorem closedGraphColon_product_in_connecting_image (hG : IntervalLabeling G)
    {α : Exponent (FiniteVariable.{u} (GraphRows N))}
    {a : FiniteTuple (GraphRows N)} (ha : a ∈ graphEdgeLattice G)
    (hα : RowMaximum α a) (hsq : ∀ v, α v ≤ 1)
    (L : {L : List (GraphRectangle.{u} G (fun _ => Finset.univ)) //
      graphRectangleListDegree L =
        graphColonResidualDegree G a (α - finiteRowExponent (GraphRows N) a)}) :
    closedGraphColonFactor hG ha (α - finiteRowExponent (GraphRows N) a)
      (rowMaximum_residual_squarefree hα hsq).1
      (rowMaximum_residual_squarefree hα hsq).2.1
      (rowMaximum_residual_squarefree hα hsq).2.2
      (closedGraphProduct (k := k) _ L) ∈
    (closedGraphProductSpan (k := k) G α).map
      (quotientConnectingProjection (finiteRowFamily (GraphRows N) (graphEdgeLattice G))
        (finitePredecessorFamily (GraphRows N) (graphEdgeLattice G) a)
        α (α - finiteRowExponent (GraphRows N) a)) := by
  let γ := α - finiteRowExponent (GraphRows N) a
  let F := (graphColonLinearDegree G a γ).support
  let R := graphColonRectangle hG ha F (graphColonLinear_support a γ)
  let f := closedGraphColonFactor (k := k) hG ha γ
    (rowMaximum_residual_squarefree hα hsq).1
    (rowMaximum_residual_squarefree hα hsq).2.1
    (rowMaximum_residual_squarefree hα hsq).2.2
  let q := quotientConnectingProjection (k := k)
    (finiteRowFamily (GraphRows N) (graphEdgeLattice G))
    (finitePredecessorFamily (GraphRows N) (graphEdgeLattice G) a) α γ
  let P := (closedGraphProductSpan (k := k) G α).map q
  have hdegree : graphRectangleListDegree (R :: L.val) = α := by
    change R.fineDegree + graphRectangleListDegree L.val = α
    rw [L.property, graphColonRectangle_degree_decomposition hG ha γ
      (rowMaximum_residual_squarefree hα hsq).1, add_comm]
    exact tsub_add_cancel_of_le hα.1
  let w := closedGraphProduct (k := k) α ⟨R :: L.val, hdegree⟩
  let x := closedGraphProduct (k := k) (graphColonResidualDegree G a γ) L
  have hqw : q w ∈ P := ⟨w, Submodule.subset_span ⟨⟨R :: L.val, hdegree⟩, rfl⟩, rfl⟩
  obtain ⟨ε, η, hε, hη, hscaled⟩ := graphColonRectangle_connecting_scaled (k := k)
    hG ha F (graphColonLinear_support a γ)
    (finitePredecessorFamily (GraphRows N) (graphEdgeLattice G) a) γ
    ((rowMaximum_residual_squarefree hα hsq).2.2 0)
    ((rowMaximum_residual_squarefree hα hsq).2.2 1)
    (graphRectangleListVector (k := k) L.val)
  have hfix : quotientFaceProjection
      (finitePredecessorFamily (GraphRows N) (graphEdgeLattice G) a) γ
      (Simplicial.basis F * graphRectangleListVector (k := k) L.val) =
        Simplicial.basis F * graphRectangleListVector L.val := by
    have h := relativeProjection_eq_self (f x).property
    simpa only [f, x, F, quotientFaceProjection,
      closedGraphColonFactor_val, closedGraphProduct_val] using h
  rw [hfix] at hscaled
  have heq : ε • q w = η • f x := by
    apply Subtype.ext
    simpa only [q, w, f, x, R, F, Submodule.coe_smul, quotientConnectingProjection_val,
      closedGraphProduct_val, graphRectangleListVector, List.map_cons, List.prod_cons,
      closedGraphColonFactor_val] using hscaled
  apply (P.smul_mem_iff_of_isUnit hη).mp
  rw [← heq]
  exact P.smul_mem ε hqw

/-- Transport a cycle-spanning statement along a map that is surjective
on cycles and preserves boundaries. The pointwise hypotheses use one
linear-equivalence coercion throughout the concrete graph application. -/
lemma cycles_generated_through_equiv
    {R M₁ M₂ : Type*} [CommRing R] [AddCommGroup M₁] [AddCommGroup M₂]
    [Module R M₁] [Module R M₂]
    (f : M₁ ≃ₗ[R] M₂) (D : Module.End R M₁) (d : Module.End R M₂)
    (P : Submodule R M₁) (Q : Submodule R M₂)
    (hcycle : ∀ y, d y = 0 → ∃ x, D x = 0 ∧ f x = y)
    (hboundary : ∀ x, f (D x) ∈ LinearMap.range d)
    (hgen : ∀ x, x ∈ P → f x ∈ Q)
    (hspan : LinearMap.ker D ≤ P ⊔ LinearMap.range D) :
    LinearMap.ker d ≤ Q ⊔ LinearMap.range d := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hcycle y hy
  obtain ⟨g, hg, b, hb, hgb⟩ := Submodule.mem_sup.mp (hspan hx)
  refine Submodule.mem_sup.mpr ⟨f g, hgen g hg, f b, ?_, ?_⟩
  · obtain ⟨z, rfl⟩ := hb
    exact hboundary z
  · rw [← map_add, hgb]

#check cycles_generated_through_equiv

attribute [local irreducible] closedGraphColonFactor quotientTotalDifferential
set_option backward.isDefEq.respectTransparency true

/-- The proved colon cycle factorization is surjective on cycles as a
literal map between the two coefficient modules. -/
theorem closedGraphColonFactor_cycles_surjective (hG : IntervalLabeling G)
    {a : FiniteTuple (GraphRows N)} (ha : a ∈ graphEdgeLattice G)
    (γ : Exponent (FiniteVariable.{u} (GraphRows N)))
    (hsq : ∀ v, γ v ≤ 1) (hbound : RowBound γ a)
    (hzero : ∀ r, γ ⟨r, ULift.up (a r)⟩ = 0)
    (z : TotalFaceModule (k := k)
      (quotientKoszulFaces (finitePredecessorFamily (GraphRows N) (graphEdgeLattice G) a) γ))
    (hz : quotientTotalDifferential (k := k)
      (finitePredecessorFamily (GraphRows N) (graphEdgeLattice G) a) γ z = 0) :
    ∃ x : TotalFaceModule (k := k)
      (quotientKoszulFaces (finiteRowFamily (GraphRows N) (graphEdgeLattice G))
        (graphColonResidualDegree G a γ)),
      quotientTotalDifferential (k := k) (finiteRowFamily (GraphRows N) (graphEdgeLattice G))
        (graphColonResidualDegree G a γ) x = 0 ∧
      closedGraphColonFactor (k := k) hG ha γ hsq hbound hzero x = z := by
  obtain ⟨x, hx, he⟩ := closedGraphColon_cycle_factorization (k := k)
    hG ha γ hsq hbound hzero z hz
  refine ⟨x, hx, ?_⟩
  apply Subtype.ext
  exact (closedGraphColonFactor_val (k := k) hG ha γ hsq hbound hzero x).trans he.symm

#check closedGraphColonFactor_cycles_surjective

/-- Every rectangle product maps into the specified connecting image;
linearity extends the explicit product calculation to its span. -/
theorem closedGraphColon_products_in_connecting_image (hG : IntervalLabeling G)
    {α : Exponent (FiniteVariable.{u} (GraphRows N))}
    {a : FiniteTuple (GraphRows N)} (haE : a ∈ graphEdgeLattice G)
    (ha : RowMaximum α a) (hsq : ∀ v, α v ≤ 1)
    (x : TotalFaceModule (k := k)
      (quotientKoszulFaces (finiteRowFamily (GraphRows N) (graphEdgeLattice G))
        (graphColonResidualDegree G a (α - finiteRowExponent (GraphRows N) a))))
    (hx : x ∈ closedGraphProductSpan (k := k) G
      (graphColonResidualDegree G a (α - finiteRowExponent (GraphRows N) a))) :
    closedGraphColonFactor (k := k) hG haE (α - finiteRowExponent (GraphRows N) a)
      (rowMaximum_residual_squarefree ha hsq).1
      (rowMaximum_residual_squarefree ha hsq).2.1
      (rowMaximum_residual_squarefree ha hsq).2.2 x ∈
    (closedGraphProductSpan (k := k) G α).map
      (quotientConnectingProjection (k := k)
        (finiteRowFamily (GraphRows N) (graphEdgeLattice G))
        (finitePredecessorFamily (GraphRows N) (graphEdgeLattice G) a)
        α (α - finiteRowExponent (GraphRows N) a)) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨L, rfl⟩ := hy
      exact closedGraphColon_product_in_connecting_image (k := k)
        (G := G) hG haE ha hsq L
  | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
  | add y z hy hz ihy ihz =>
      rw [map_add]
      exact Submodule.add_mem _ ihy ihz
  | smul c y hy ih =>
      rw [map_smul]
      exact Submodule.smul_mem _ c ih

#check closedGraphColon_products_in_connecting_image

/-- The colon factor transports the smaller graph's cycle spanning
statement to the image needed by the connecting map. Keeping this step
separate makes the main degree induction use a proved map-level lemma. -/
theorem closedGraphColon_cycles_in_connecting_image (hG : IntervalLabeling G)
    {α : Exponent (FiniteVariable.{u} (GraphRows N))}
    {a : FiniteTuple (GraphRows N)} (haE : a ∈ graphEdgeLattice G)
    (ha : RowMaximum α a) (hsq : ∀ v, α v ≤ 1)
    (hsmall : LinearMap.ker (quotientTotalDifferential (k := k)
        (finiteRowFamily (GraphRows N) (graphEdgeLattice G))
        (graphColonResidualDegree G a (α - finiteRowExponent (GraphRows N) a))) ≤
      closedGraphProductSpan (k := k) G
        (graphColonResidualDegree G a (α - finiteRowExponent (GraphRows N) a)) ⊔
        LinearMap.range (quotientTotalDifferential (k := k)
          (finiteRowFamily (GraphRows N) (graphEdgeLattice G))
          (graphColonResidualDegree G a (α - finiteRowExponent (GraphRows N) a)))) :
    LinearMap.ker (quotientTotalDifferential (k := k)
      (finitePredecessorFamily (GraphRows N) (graphEdgeLattice G) a)
      (α - finiteRowExponent (GraphRows N) a)) ≤
    (closedGraphProductSpan (k := k) G α).map
      (quotientConnectingProjection (k := k)
        (finiteRowFamily (GraphRows N) (graphEdgeLattice G))
        (finitePredecessorFamily (GraphRows N) (graphEdgeLattice G) a)
        α (α - finiteRowExponent (GraphRows N) a)) ⊔
      LinearMap.range (quotientTotalDifferential (k := k)
        (finitePredecessorFamily (GraphRows N) (graphEdgeLattice G) a)
        (α - finiteRowExponent (GraphRows N) a)) := by
  let γ := α - finiteRowExponent (GraphRows N) a
  let δ := graphColonResidualDegree G a γ
  let C := finitePredecessorFamily (GraphRows N) (graphEdgeLattice G) a
  let B := finiteRowFamily (GraphRows N) (graphEdgeLattice G)
  let q : TotalFaceModule (k := k) (quotientKoszulFaces B α) →ₗ[k]
      TotalFaceModule (k := k) (quotientKoszulFaces C γ) :=
    quotientConnectingProjection (k := k) B C α γ
  let f : TotalFaceModule (k := k) (quotientKoszulFaces B δ) ≃ₗ[k]
      TotalFaceModule (k := k) (quotientKoszulFaces C γ) :=
    closedGraphColonFactor (k := k) hG haE γ
    (rowMaximum_residual_squarefree ha hsq).1
    (rowMaximum_residual_squarefree ha hsq).2.1
    (rowMaximum_residual_squarefree ha hsq).2.2
  change LinearMap.ker (quotientTotalDifferential (k := k) C γ) ≤
    (closedGraphProductSpan (k := k) G α).map q ⊔
      LinearMap.range (quotientTotalDifferential (k := k) C γ)
  exact cycles_generated_through_equiv (R := k)
    (M₁ := TotalFaceModule (k := k) (quotientKoszulFaces B δ))
    (M₂ := TotalFaceModule (k := k) (quotientKoszulFaces C γ)) f
    (quotientTotalDifferential (k := k) B δ) (quotientTotalDifferential (k := k) C γ)
    (closedGraphProductSpan (k := k) G δ)
    ((closedGraphProductSpan (k := k) G α).map q)
    (closedGraphColonFactor_cycles_surjective (k := k) hG haE γ
      (rowMaximum_residual_squarefree ha hsq).1
      (rowMaximum_residual_squarefree ha hsq).2.1
      (rowMaximum_residual_squarefree ha hsq).2.2)
    (closedGraphColonFactor_boundary (k := k) hG haE γ
      (rowMaximum_residual_squarefree ha hsq).1
      (rowMaximum_residual_squarefree ha hsq).2.1
      (rowMaximum_residual_squarefree ha hsq).2.2)
    (closedGraphColon_products_in_connecting_image (k := k) hG haE ha hsq)
    hsmall

set_option backward.isDefEq.respectTransparency false

/-- Every quotient Koszul cycle of an interval-labelled graph is homologous
to a linear combination of products of its literal rectangle cycles.

The induction decreases the actual fine degree. Repeated coordinates and
missing row maxima contract explicitly; the remaining predecessor strand
factors into a fixed exterior face and a strictly smaller original graph
strand. The coefficient ring is arbitrary, including positive characteristic.
-/
theorem closedGraph_quotient_cycles_generated (hG : IntervalLabeling G)
    (α : Exponent (FiniteVariable.{u} (GraphRows N))) :
    LinearMap.ker (quotientTotalDifferential (k := k)
      (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) α) ≤
      closedGraphProductSpan G α ⊔
        LinearMap.range (quotientTotalDifferential
          (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) α) := by
  have hall : ∀ m : ℕ, ∀ β : Exponent (FiniteVariable.{u} (GraphRows N)),
      β.degree = m →
      LinearMap.ker (quotientTotalDifferential (k := k)
        (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) β) ≤
        closedGraphProductSpan G β ⊔
          LinearMap.range (quotientTotalDifferential
            (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) β) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro β hdegree z hz
      by_cases hzero : β = 0
      · subst β
        exact (show closedGraphProductSpan (k := k) G 0 ≤ _ from le_sup_left)
          (closedGraph_zero_degree_span z)
      obtain ⟨e, he⟩ : ∃ e, 0 < β e := by
        by_contra h
        push_neg at h
        apply hzero
        ext v
        exact Nat.eq_zero_of_le_zero (h v)
      by_cases hsq : ∀ v, β v ≤ 1
      · by_cases hcontains : Contains (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) β
        · obtain ⟨b, hb, hbβ⟩ := hcontains
          obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hb
          obtain ⟨a, ha⟩ := rowMaximum_exists_of_generator β hbβ
          by_cases haE : a ∈ graphEdgeLattice G
          · let γ := β - finiteRowExponent (GraphRows N) a
            let δ := graphColonResidualDegree G a γ
            let C := finitePredecessorFamily (GraphRows N) (graphEdgeLattice G) a
            let B := finiteRowFamily (GraphRows N) (graphEdgeLattice G)
            let q := quotientConnectingProjection (k := k) B C β γ
            have hδ : δ.degree < m := by
              rw [← hdegree]
              exact graphColonResidualDegree_lt (G := G) ha
            have hsmall := ih δ.degree hδ δ rfl
            have hspan := closedGraphColon_cycles_in_connecting_image
              (k := k) hG haE ha hsq hsmall
            have hgen := cycle_spanning_of_connecting_detection
              (quotientTotalDifferential (k := k) B β)
              (quotientTotalDifferential C γ) q
              (fun x hx => firstPowerConnecting_cycle (k := k) (graphEdgeLattice_closed hG)
                (a := ⟨a, haE⟩) ha x hx)
              (fun x hx hh => firstPowerConnecting_detects_boundaries (k := k)
                (graphEdgeLattice_closed hG) (a := ⟨a, haE⟩) ha e he x hx hh)
              (Set.range (closedGraphProduct (G := G) (k := k) β))
              (fun x hx => (closedGraphProductSpan_le_cycles β)
                (Submodule.subset_span hx)) hspan
            exact hgen hz
          · apply (show LinearMap.range (quotientTotalDifferential (k := k)
                (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) β) ≤ _ from le_sup_right)
            exact (firstPowerQuotientCycle_boundary_of_missing_maximum (k := k)
                (graphEdgeLattice_closed hG) ha haE e he z hz)
        · apply (show LinearMap.range (quotientTotalDifferential (k := k)
              (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) β) ≤ _ from le_sup_right)
          exact quotientCycle_boundary_of_not_contains (k := k) _ β hcontains e he z hz
      · push_neg at hsq
        obtain ⟨v, hv⟩ := hsq
        apply (show LinearMap.range (quotientTotalDifferential (k := k)
          (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) β) ≤ _ from le_sup_right)
        apply quotient_cycle_boundary_of_two_le (k := k) (e := v) _ (by omega) z hz
        intro c hc
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
        rcases v with ⟨r, ⟨j⟩⟩
        simp only [finiteRowExponent_apply]
        split_ifs <;> omega
  exact hall α.degree α rfl

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphGrading -/
section

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 500000
set_option maxRecDepth 4096

noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u

lemma basisSpan_and_mem {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (b : Module.Basis I R M) (P Q : I → Prop) {x : M}
    (hx : x ∈ basisSpan b P) (hy : x ∈ basisSpan b Q) :
    x ∈ basisSpan b (fun i => P i ∧ Q i) := by
  rw [basisSpan, b.mem_span_image] at hx hy ⊢
  intro i hi
  exact ⟨hx hi, hy hi⟩

variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

lemma faceCardSpan_mul {x y : Simplicial.Ambient V k} (p q : ℕ)
    (hx : x ∈ basisSpan Simplicial.basis (fun F => F.card = p))
    (hy : y ∈ basisSpan Simplicial.basis (fun F => F.card = q)) :
    x * y ∈ basisSpan Simplicial.basis (fun F => F.card = p + q) := by
  apply faceSpan_mul_mem _ _ _ _ hx hy
  intro F hF H hH hFH
  rw [Finset.card_union_of_disjoint hFH, hF, hH]

variable {N : ℕ} {G : SimpleGraph (Fin N)}
variable {A : ∀ r, Finset (Fin (GraphRows N r))}

local instance : DecidableEq (FiniteVariable.{u} (GraphRows N)) :=
  (inferInstance : LinearOrder (FiniteVariable.{u} (GraphRows N))).toDecidableEq

/-- The genuine exterior degree of a rectangle representative. -/
def GraphRectangle.homologicalDegree (R : GraphRectangle.{u} G A) : ℕ :=
  R.X.card - 1 + R.Y.card

lemma GraphRectangle.vector_card (R : GraphRectangle.{u} G A) :
    R.vector (k := k) ∈ basisSpan Simplicial.basis
      (fun F => F.card = R.homologicalDegree) := by
  apply faceSpan_mul_mem (fun F => ∃ x ∈ R.X, F = R.X.erase x)
    (fun F => F = R.Y) (fun F => F.card = R.homologicalDegree) _
    (boundary_mem_eraseSpan (k := k) R.X) (Submodule.subset_span ⟨R.Y, rfl, rfl⟩)
  intro F hF H hH hFH
  obtain ⟨x, hx, rfl⟩ := hF
  subst H
  rw [Finset.card_union_of_disjoint hFH, Finset.card_erase_of_mem hx]
  rfl

def graphRectangleListHomologicalDegree (L : List (GraphRectangle.{u} G A)) : ℕ :=
  (L.map GraphRectangle.homologicalDegree).sum

lemma graphRectangleListVector_card (L : List (GraphRectangle.{u} G A)) :
    graphRectangleListVector (k := k) L ∈ basisSpan Simplicial.basis
      (fun F => F.card = graphRectangleListHomologicalDegree L) := by
  induction L with
  | nil =>
    change (1 : Simplicial.Ambient (FiniteVariable.{u} (GraphRows N)) k) ∈
      basisSpan (Simplicial.basis (k := k))
        (fun F : Finset (FiniteVariable.{u} (GraphRows N)) => F.card = 0)
    rw [← faceBasis_empty]
    exact Submodule.subset_span ⟨∅, rfl, rfl⟩
  | cons R L ih =>
    change R.vector (k := k) * graphRectangleListVector (k := k) L ∈
      basisSpan (Simplicial.basis (k := k))
        (fun F : Finset (FiniteVariable.{u} (GraphRows N)) =>
          F.card = R.homologicalDegree + graphRectangleListHomologicalDegree L)
    exact faceCardSpan_mul (V := FiniteVariable.{u} (GraphRows N)) (k := k)
      _ _ (R.vector_card (k := k)) ih

lemma closedGraphProduct_homogeneous
    (α : Exponent (FiniteVariable.{u} (GraphRows N)))
    (L : {L : List (GraphRectangle.{u} G (fun _ => Finset.univ)) //
      graphRectangleListDegree L = α}) :
    closedGraphProduct (k := k) α L ∈ totalFacePiece
      (quotientKoszulFaces (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) α)
      (graphRectangleListHomologicalDegree L.val) := by
  change (closedGraphProduct (k := k) α L).val ∈ Simplicial.Chains _ _
  exact basisSpan_and_mem (Simplicial.basis (k := k)) _ _
    (closedGraphProduct (k := k) α L).property (graphRectangleListVector_card (k := k) L.val)

end FourPapers.Sublattice



namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {k : Type u} [CommRing k] {N : ℕ} {G : SimpleGraph (Fin N)}

/-- The graph cycle spanning result with the homological degree fully retained.
Its generators are precisely the previously constructed rectangle products of
that exterior degree, and the filling has exterior degree p+1. -/
theorem closedGraph_homogeneous_cycles_generated (hG : IntervalLabeling G)
    (α : Exponent (FiniteVariable.{u} (GraphRows N))) (p : ℕ)
    (z : TotalFaceModule (k := k)
      (quotientKoszulFaces (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) α))
    (hzp : z ∈ totalFacePiece
      (quotientKoszulFaces (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) α) p)
    (hz : quotientTotalDifferential (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) α z = 0) :
    ∃ g, g ∈ Submodule.span k ((closedGraphProduct (G := G) (k := k) α) ''
      {L | graphRectangleListHomologicalDegree L.val = p}) ∧
      ∃ y, y ∈ totalFacePiece
        (quotientKoszulFaces (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) α) (p + 1) ∧
        g + quotientTotalDifferential (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) α y = z := by
  let Q := quotientKoszulFaces (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) α
  let b := totalFaceBasis (k := k) Q
  let deg := fun F : {F // Q F} => F.val.card
  let D := quotientTotalDifferential (k := k)
    (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) α
  have hpiece : ∀ i, totalFacePiece (k := k) Q i = Grading.Piece b deg i :=
    fun i => totalFacePiece_eq_basis_span Q i
  have hb : ∀ F, b F ∈ totalFacePiece (k := k) Q (deg F) := by
    intro F
    rw [hpiece]
    exact Grading.basis_mem_piece b deg F
  have hzero : ∀ F, deg F = 0 → D (b F) = 0 := by
    intro F hF
    exact quotientTotalDifferential_zero_degree _ α (b F) (hF ▸ hb F)
  have hlower : ∀ F, D (b F) ∈ Grading.Piece b deg (deg F - 1) := by
    intro F
    by_cases hF : deg F = 0
    · rw [hzero F hF]
      exact Submodule.zero_mem _
    · obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero hF
      rw [hq, Nat.succ_sub_one, ← hpiece]
      exact quotientTotalDifferential_lowers _ α q (b F) (by
        simpa only [hq, Nat.succ_eq_add_one] using hb F)
  have h := homogeneous_cycle_spanning b deg D hlower hzero
    (closedGraphProduct (G := G) (k := k) α)
    (fun L => graphRectangleListHomologicalDegree L.val)
    (fun L => by
      rw [← hpiece]
      exact closedGraphProduct_homogeneous (k := k) α L)
    (closedGraph_quotient_cycles_generated (k := k) hG α) p z
    (by rw [← hpiece]; exact hzp) hz
  simpa only [← hpiece] using h

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.PolynomialFineContraction -/
section

/-!
# An explicit integral contraction of the polynomial Koszul complex

In each nonzero fine degree, choose a variable appearing in that degree and
use exterior creation by that variable. The zero fine degree is retained as
the coefficient ring. The construction is linear in every strand and uses
no division, characteristic assumption, or homology-dimension argument.
-/

section
set_option autoImplicit false
noncomputable section

namespace FourPapers.PolynomialFineContraction

open Classical DirectSum CommAlg CommAlg.Koszul CommAlg.Polymatroid
open FourPapers.Sublattice

universe u
variable {R V : Type u} [CommRing R] [Fintype V] [LinearOrder V]

instance (priority := 1200) fullFaceAddCommGroup (α : Exponent V) :
    AddCommGroup (FullFaceModule (k := R) α) :=
  Submodule.addCommGroup (R := R) (M := Simplicial.Ambient V R) (FullFaceModule α)

instance (priority := 1200) fullFaceModule (α : Exponent V) :
    Module R (FullFaceModule (k := R) α) :=
  Submodule.module (R := R) (M := Simplicial.Ambient V R) (FullFaceModule α)

lemma zero_face_eq_empty (F : Finset V) (hF : fullKoszulFaces (0 : Exponent V) F) :
    F = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  have h := hF v
  simp only [fullKoszulFaces, faceExponent_apply, hv, if_true,
    Finsupp.zero_apply] at h
  omega

def zeroFaceIndexEquiv : {F : Finset V // fullKoszulFaces (0 : Exponent V) F} ≃ PUnit.{u + 1} where
  toFun _ := PUnit.unit
  invFun _ := ⟨∅, by simp [fullKoszulFaces, faceExponent]⟩
  left_inv F := Subtype.ext (zero_face_eq_empty F.val F.property).symm
  right_inv x := Subsingleton.elim _ _

def zeroFaceEquiv : FullFaceModule (V := V) (k := R) 0 ≃ₗ[R] R :=
  (totalFaceBasis (k := R) (fullKoszulFaces (0 : Exponent V))).equiv
    (Module.Basis.singleton PUnit.{u + 1} R) zeroFaceIndexEquiv

lemma zeroFaceDifferential : fullFaceDifferential (V := V) (k := R) 0 = 0 := by
  apply (totalFaceBasis (k := R) (fullKoszulFaces (0 : Exponent V))).ext
  intro F
  apply Subtype.ext
  simp only [fullFaceDifferential, idealTotalDifferential_val, totalFaceBasis_val,
    LinearMap.zero_apply, Submodule.coe_zero]
  rw [zero_face_eq_empty F.val F.property, faceBasis_empty]
  exact CliffordAlgebra.contractLeft_one _ _

lemma exists_positive_coordinate (α : Exponent V) (hα : α ≠ 0) : ∃ v, 0 < α v := by
  by_contra! h
  apply hα
  ext v
  exact Nat.eq_zero_of_le_zero (h v)

def coordinate (α : Exponent V) (hα : α ≠ 0) : V :=
  Classical.choose (exists_positive_coordinate α hα)

lemma coordinate_positive (α : Exponent V) (hα : α ≠ 0) :
    0 < α (coordinate α hα) :=
  Classical.choose_spec (exists_positive_coordinate α hα)

def strandHomotopy (α : Exponent V) :
    Module.End R (FullFaceModule (k := R) α) :=
  if hα : α = 0 then 0 else
    fullFaceCreation α (coordinate α hα) (coordinate_positive α hα)

@[simp] lemma strandHomotopy_zero : strandHomotopy (V := V) (R := R) 0 = 0 := by
  simp [strandHomotopy]

lemma strand_homotopy (α : Exponent V) (hα : α ≠ 0) :
    fullFaceDifferential α * strandHomotopy (R := R) α +
      strandHomotopy α * fullFaceDifferential α = 1 := by
  rw [strandHomotopy, dif_neg hα]
  exact fullFace_contraction α (coordinate α hα) (coordinate_positive α hα)

lemma strandHomotopy_square (α : Exponent V) :
    strandHomotopy (R := R) α * strandHomotopy α = 0 := by
  by_cases hα : α = 0
  · subst α
    rw [strandHomotopy_zero, zero_mul]
  · rw [strandHomotopy, dif_neg hα]
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change ExteriorAlgebra.ι R ((Pi.basisFun R V) (coordinate α hα)) *
      (ExteriorAlgebra.ι R ((Pi.basisFun R V) (coordinate α hα)) * x.val) = 0
    rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]

abbrev FineTotal := ⨁ α : Exponent V, FullFaceModule (k := R) α

def differential : Module.End R (FineTotal (R := R) (V := V)) :=
  DirectSum.lmap (fun α => fullFaceDifferential α)

def homotopy : Module.End R (FineTotal (R := R) (V := V)) :=
  DirectSum.lmap (fun α => strandHomotopy α)

def inclusion : R →ₗ[R] FineTotal (R := R) (V := V) :=
  (DirectSum.lof R (Exponent V) (fun α => ↥(FullFaceModule (k := R) α)) 0).comp
    (zeroFaceEquiv (R := R) (V := V)).symm.toLinearMap

def projection : FineTotal (R := R) (V := V) →ₗ[R] R :=
  (zeroFaceEquiv (R := R) (V := V)).toLinearMap.comp
    (DirectSum.component R (Exponent V) (fun α => ↥(FullFaceModule (k := R) α)) 0)

@[simp] lemma differential_lof (α : Exponent V) (x : FullFaceModule (k := R) α) :
    differential (DirectSum.lof R (Exponent V) (fun α => ↥(FullFaceModule (k := R) α)) α x) =
      DirectSum.lof R (Exponent V) (fun α => ↥(FullFaceModule (k := R) α)) α
        (fullFaceDifferential α x) := by
  simp only [differential, DirectSum.lmap_lof]

@[simp] lemma homotopy_lof (α : Exponent V) (x : FullFaceModule (k := R) α) :
    homotopy (DirectSum.lof R (Exponent V) (fun α => ↥(FullFaceModule (k := R) α)) α x) =
      DirectSum.lof R (Exponent V) (fun α => ↥(FullFaceModule (k := R) α)) α
        (strandHomotopy α x) := by
  simp only [homotopy, DirectSum.lmap_lof]

@[simp] lemma projection_lof_zero (x : FullFaceModule (V := V) (k := R) 0) :
    projection (DirectSum.lof R (Exponent V) (fun α => ↥(FullFaceModule (k := R) α)) 0 x) =
      zeroFaceEquiv x := by
  simp only [projection, LinearMap.comp_apply, DirectSum.component.lof_self,
    LinearEquiv.coe_coe]

lemma projection_lof_ne (α : Exponent V) (hα : α ≠ 0)
    (x : FullFaceModule (k := R) α) :
    projection (DirectSum.lof R (Exponent V) (fun α => ↥(FullFaceModule (k := R) α)) α x) = 0 := by
  change zeroFaceEquiv ((DirectSum.of (fun α => ↥(FullFaceModule (k := R) α)) α x) 0) = 0
  have hz := DirectSum.of_eq_of_ne (β := fun a => ↥(FullFaceModule (k := R) a))
    α 0 x (Ne.symm hα)
  exact (congrArg (fun y : FullFaceModule (k := R) (0 : Exponent V) =>
    zeroFaceEquiv (R := R) (V := V) y) hz).trans
      (map_zero (zeroFaceEquiv (R := R) (V := V)))

lemma inclusion_projection_zero (x : FullFaceModule (V := V) (k := R) 0) :
    inclusion (projection (DirectSum.lof R (Exponent V) (fun α => ↥(FullFaceModule (k := R) α)) 0 x)) =
      DirectSum.lof R (Exponent V) (fun α => ↥(FullFaceModule (k := R) α)) 0 x := by
  rw [projection_lof_zero]
  change DirectSum.lof R (Exponent V) (fun α => ↥(FullFaceModule (k := R) α)) 0
    (zeroFaceEquiv.symm (zeroFaceEquiv x)) = _
  rw [LinearEquiv.symm_apply_apply]

def contraction : HomologicalPerturbation.LinearContraction
    (R := R) (M := FineTotal (R := R) (V := V)) (H := R) where
  d := differential
  h := homotopy
  inclusion := inclusion
  projection := projection
  differential := by
    apply DirectSum.linearMap_ext
    intro α
    apply LinearMap.ext
    intro x
    change differential (differential
      (DirectSum.lof R (Exponent V) (fun α => ↥(FullFaceModule (k := R) α)) α x)) = 0
    rw [differential_lof, differential_lof]
    have hd : fullFaceDifferential α (fullFaceDifferential (k := R) α x) = 0 := by
      apply Subtype.ext
      exact Simplicial.boundary_boundary x.val
    rw [hd, map_zero]
  retract := by
    apply LinearMap.ext
    intro r
    change projection (DirectSum.lof R (Exponent V) (fun α => ↥(FullFaceModule (k := R) α)) 0
      (zeroFaceEquiv.symm r)) = r
    rw [projection_lof_zero, LinearEquiv.apply_symm_apply]
  inclusion_cycle := by
    apply LinearMap.ext
    intro r
    change differential (DirectSum.lof R (Exponent V) (fun α => ↥(FullFaceModule (k := R) α)) 0
      (zeroFaceEquiv.symm r)) = 0
    rw [differential_lof, zeroFaceDifferential, LinearMap.zero_apply, map_zero]
  projection_boundary := by
    apply DirectSum.linearMap_ext
    intro α
    apply LinearMap.ext
    intro x
    change projection (differential
      (DirectSum.lof R (Exponent V) (fun α => ↥(FullFaceModule (k := R) α)) α x)) = 0
    rw [differential_lof]
    by_cases hα : α = 0
    · subst α
      rw [zeroFaceDifferential, LinearMap.zero_apply, map_zero, map_zero]
    · exact projection_lof_ne α hα _
  homotopy := by
    apply DirectSum.linearMap_ext
    intro α
    apply LinearMap.ext
    intro x
    change differential (homotopy
          (DirectSum.lof R (Exponent V) (fun α => ↥(FullFaceModule (k := R) α)) α x)) +
        homotopy (differential
          (DirectSum.lof R (Exponent V) (fun α => ↥(FullFaceModule (k := R) α)) α x)) =
      DirectSum.lof R (Exponent V) (fun α => ↥(FullFaceModule (k := R) α)) α x -
        inclusion (projection
          (DirectSum.lof R (Exponent V) (fun α => ↥(FullFaceModule (k := R) α)) α x))
    rw [homotopy_lof, differential_lof, differential_lof, homotopy_lof]
    by_cases hα : α = 0
    · subst α
      rw [strandHomotopy_zero, zeroFaceDifferential]
      simp only [LinearMap.zero_apply, map_zero, add_zero,
        inclusion_projection_zero, sub_self]
    · rw [projection_lof_ne α hα, map_zero, sub_zero, ← map_add]
      exact congrArg (DirectSum.lof R (Exponent V) (fun α => ↥(FullFaceModule (k := R) α)) α)
        (LinearMap.congr_fun (strand_homotopy (R := R) α hα) x)
  squareHomotopy := by
    apply DirectSum.linearMap_ext
    intro α
    apply LinearMap.ext
    intro x
    change homotopy (homotopy
      (DirectSum.lof R (Exponent V) (fun α => ↥(FullFaceModule (k := R) α)) α x)) = 0
    have hx := LinearMap.congr_fun (strandHomotopy_square (R := R) α) x
    change strandHomotopy α (strandHomotopy α x) = 0 at hx
    rw [homotopy_lof, homotopy_lof, hx, map_zero]
  homotopyInclusion := by
    apply LinearMap.ext
    intro r
    change homotopy (DirectSum.lof R (Exponent V) (fun α => ↥(FullFaceModule (k := R) α)) 0
      (zeroFaceEquiv.symm r)) = 0
    rw [homotopy_lof, strandHomotopy_zero, LinearMap.zero_apply, map_zero]
  projectionHomotopy := by
    apply DirectSum.linearMap_ext
    intro α
    apply LinearMap.ext
    intro x
    change projection (homotopy
      (DirectSum.lof R (Exponent V) (fun α => ↥(FullFaceModule (k := R) α)) α x)) = 0
    rw [homotopy_lof]
    by_cases hα : α = 0
    · subst α
      rw [strandHomotopy_zero, LinearMap.zero_apply, map_zero, map_zero]
    · exact projection_lof_ne α hα _

end FourPapers.PolynomialFineContraction

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphHomologyMaps -/
section

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 500000
set_option maxRecDepth 4096

noncomputable section

namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
open FourPapers.FilteredHomology

section LinearHomology
variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N]

/-- A map on actual cycles that carries actual boundaries to boundaries induces
a map on the literal kernel/range quotient. No choice of homology coordinates
or field hypothesis is used. -/
def closedGraphHomologyMap (D : Module.End R M) (d : Module.End R N)
    (hD : D.comp D = 0) (hd : d.comp d = 0) (q : M →ₗ[R] N)
    (hcycle : ∀ x, D x = 0 → d (q x) = 0)
    (hboundary : ∀ x, ∃ y, d y = q (D x)) :
    Homology D D hD →ₗ[R] Homology d d hd :=
  (LinearMap.range (boundaryMap D D hD)).liftQ
    ((homologyClass d d hd).comp
      ((q.domRestrict (LinearMap.ker D)).codRestrict _
        (fun x => hcycle x.val x.property))) (by
      rintro x ⟨y, rfl⟩
      change homologyClass d d hd
        ⟨q (D y), hcycle (D y) (LinearMap.congr_fun hD y)⟩ = 0
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      obtain ⟨z, hz⟩ := hboundary y
      exact ⟨z, Subtype.ext hz⟩)

@[simp] lemma closedGraphHomologyMap_class
    (D : Module.End R M) (d : Module.End R N)
    (hD : D.comp D = 0) (hd : d.comp d = 0) (q : M →ₗ[R] N)
    (hcycle : ∀ x, D x = 0 → d (q x) = 0)
    (hboundary : ∀ x, ∃ y, d y = q (D x)) (x : LinearMap.ker D) :
    closedGraphHomologyMap D d hD hd q hcycle hboundary (homologyClass D D hD x) =
      homologyClass d d hd ⟨q x.val, hcycle x.val x.property⟩ := rfl

lemma closedGraphHomologyMap_injective
    (D : Module.End R M) (d : Module.End R N)
    (hD : D.comp D = 0) (hd : d.comp d = 0) (q : M →ₗ[R] N)
    (hcycle : ∀ x, D x = 0 → d (q x) = 0)
    (hboundary : ∀ x, ∃ y, d y = q (D x))
    (hdetect : ∀ x, D x = 0 → (∃ y, d y = q x) → ∃ y, D y = x) :
    Function.Injective (closedGraphHomologyMap D d hD hd q hcycle hboundary) := by
  intro x y hxy
  obtain ⟨z, rfl⟩ := (LinearMap.range (boundaryMap D D hD)).mkQ_surjective x
  obtain ⟨w, rfl⟩ := (LinearMap.range (boundaryMap D D hD)).mkQ_surjective y
  change homologyClass d d hd ⟨q z.val, hcycle z.val z.property⟩ =
    homologyClass d d hd ⟨q w.val, hcycle w.val w.property⟩ at hxy
  obtain ⟨a, ha⟩ := (homologyClass_eq_iff d d hd _ _).mp hxy
  apply (homologyClass_eq_iff D D hD z w).mpr
  apply hdetect (z.val - w.val)
  · rw [map_sub, z.property, w.property, sub_self]
  · exact ⟨a, by simpa only [map_sub] using ha⟩

lemma closedGraphHomologyMap_surjective
    (D : Module.End R M) (d : Module.End R N)
    (hD : D.comp D = 0) (hd : d.comp d = 0) (q : M →ₗ[R] N)
    (hcycle : ∀ x, D x = 0 → d (q x) = 0)
    (hboundary : ∀ x, ∃ y, d y = q (D x))
    (hspan : LinearMap.ker d ≤ (LinearMap.ker D).map q ⊔ LinearMap.range d) :
    Function.Surjective (closedGraphHomologyMap D d hD hd q hcycle hboundary) := by
  intro y
  obtain ⟨z, rfl⟩ := (LinearMap.range (boundaryMap d d hd)).mkQ_surjective y
  obtain ⟨a, ⟨x, hx, hqx⟩, b, ⟨w, hw⟩, hab⟩ := Submodule.mem_sup.mp (hspan z.property)
  refine ⟨homologyClass D D hD ⟨x, hx⟩, ?_⟩
  rw [closedGraphHomologyMap_class]
  apply (homologyClass_eq_iff d d hd _ z).mpr
  refine ⟨-w, ?_⟩
  change d (-w) = q x - z.val
  rw [map_neg, hw, hqx, ← hab]
  abel

/-- A connecting map is a genuine homology isomorphism once it both detects
boundaries and spans the target modulo boundaries. -/
def closedGraphHomologyEquiv
    (D : Module.End R M) (d : Module.End R N)
    (hD : D.comp D = 0) (hd : d.comp d = 0) (q : M →ₗ[R] N)
    (hcycle : ∀ x, D x = 0 → d (q x) = 0)
    (hboundary : ∀ x, ∃ y, d y = q (D x))
    (hdetect : ∀ x, D x = 0 → (∃ y, d y = q x) → ∃ y, D y = x)
    (hspan : LinearMap.ker d ≤ (LinearMap.ker D).map q ⊔ LinearMap.range d) :
    Homology D D hD ≃ₗ[R] Homology d d hd :=
  LinearEquiv.ofBijective (closedGraphHomologyMap D d hD hd q hcycle hboundary)
    ⟨closedGraphHomologyMap_injective D d hD hd q hcycle hboundary hdetect,
      closedGraphHomologyMap_surjective D d hD hd q hcycle hboundary hspan⟩

/-- Multiplying a differential by a unit, and transporting it by an actual
module equivalence, preserves the literal homology quotient. -/
def closedGraphScaledHomologyEquiv
    (D : Module.End R M) (d : Module.End R N)
    (hD : D.comp D = 0) (hd : d.comp d = 0) (f : M ≃ₗ[R] N)
    (u : R) (hu : IsUnit u) (hcomm : ∀ x, d (f x) = u • f (D x)) :
    Homology D D hD ≃ₗ[R] Homology d d hd := by
  have hcycle : ∀ x, D x = 0 → d (f x) = 0 := by
    intro x hx
    rw [hcomm, hx, map_zero, smul_zero]
  have hboundary : ∀ x, ∃ y, d y = f (D x) := by
    intro x
    have hh : u • f (D x) ∈ LinearMap.range d := by
      rw [← hcomm]
      exact ⟨f x, rfl⟩
    exact (Submodule.smul_mem_iff_of_isUnit _ hu).mp hh
  have hdetect : ∀ x, D x = 0 → (∃ y, d y = f x) → ∃ y, D y = x := by
    rintro x _ ⟨y, hy⟩
    refine ⟨u • f.symm y, ?_⟩
    apply f.injective
    rw [map_smul, map_smul, ← hcomm, f.apply_symm_apply, hy]
  have hspan : LinearMap.ker d ≤
      (LinearMap.ker D).map f.toLinearMap ⊔ LinearMap.range d := by
    intro y hy
    refine Submodule.mem_sup.mpr ⟨y, ?_, 0, Submodule.zero_mem _, add_zero y⟩
    refine ⟨f.symm y, ?_, f.apply_symm_apply y⟩
    have hh := hcomm (f.symm y)
    rw [f.apply_symm_apply, show d y = 0 from hy] at hh
    exact f.injective (by simpa only [map_zero] using (hu.smul_eq_zero.mp hh.symm))
  exact closedGraphHomologyEquiv D d hD hd f.toLinearMap hcycle hboundary hdetect hspan

lemma closedGraphHomology_subsingleton_of_boundaries
    (D : Module.End R M) (hD : D.comp D = 0)
    (hfill : ∀ x, D x = 0 → ∃ y, D y = x) :
    Subsingleton (Homology D D hD) := by
  constructor
  intro x y
  obtain ⟨z, rfl⟩ := (LinearMap.range (boundaryMap D D hD)).mkQ_surjective x
  obtain ⟨w, rfl⟩ := (LinearMap.range (boundaryMap D D hD)).mkQ_surjective y
  apply (homologyClass_eq_iff D D hD z w).mpr
  apply hfill
  rw [map_sub, z.property, w.property, sub_self]

def closedGraphZeroDifferentialHomologyEquiv
    (D : Module.End R M) (hD : D.comp D = 0) (hz : D = 0) :
    Homology D D hD ≃ₗ[R] M := by
  let c : M →ₗ[R] LinearMap.ker D :=
    (LinearMap.id : M →ₗ[R] M).codRestrict _ (by intro x; simp [hz])
  let L := (homologyClass D D hD).comp c
  have hinj : Function.Injective L := by
    intro x y hxy
    obtain ⟨z, hz'⟩ := (homologyClass_eq_iff D D hD (c x) (c y)).mp hxy
    have hh : (0 : M) = x - y := by simpa only [hz, LinearMap.zero_apply, c,
      LinearMap.codRestrict_apply, LinearMap.id_apply] using hz'
    exact sub_eq_zero.mp hh.symm
  have hsurj : Function.Surjective L := by
    intro y
    obtain ⟨z, rfl⟩ := (LinearMap.range (boundaryMap D D hD)).mkQ_surjective y
    exact ⟨z.val, rfl⟩
  exact (LinearEquiv.ofBijective L ⟨hinj, hsurj⟩).symm

end LinearHomology

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

/-- A quotient face cannot lie entirely in a residual strand whose removed
monomial already belongs to the ideal. Consequently the smaller-strand
projection annihilates the original quotient module. -/
lemma quotientProjection_residual_zero (B C : Family V) (α β : Exponent V)
    (hβ : Contains B β) (hβα : β ≤ α)
    (x : TotalFaceModule (k := k) (quotientKoszulFaces B α)) :
    quotientFaceProjection C (α - β) x.val = 0 := by
  have hker : TotalFaceModule (k := k) (quotientKoszulFaces B α) ≤
      LinearMap.ker (quotientFaceProjection C (α - β)) := by
    apply Submodule.span_le.mpr
    rintro z ⟨F, hF, rfl⟩
    change quotientFaceProjection C (α - β) (Simplicial.basis F) = 0
    rw [quotientFaceProjection, relativeProjection_basis]
    apply if_neg
    intro hQ
    obtain ⟨b, hb, hbb⟩ := hβ
    apply hF.2
    refine ⟨b, hb, hbb.trans ?_⟩
    intro v
    have h1 := hQ.1 v
    have h2 := hβα v
    change faceExponent F v ≤ α v - β v at h1
    change β v ≤ α v - faceExponent F v
    omega
  exact hker x.property

variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

/-- The literal first-power connecting map anticommutes with the differentials
on every vector, not only on cycles. This supplies the boundary-preservation
needed for a map on integral homology. -/
theorem firstPowerConnecting_anticommutes (hE : finiteLatticeClosed n E)
    {α : Exponent (FiniteVariable.{u} n)} {a : E} (hα : RowMaximum α a.val)
    (z : TotalFaceModule (k := k) (quotientKoszulFaces (finiteRowFamily n E) α)) :
    quotientTotalDifferential (finitePredecessorFamily n E a.val)
      (α - finiteRowExponent n a.val)
      (quotientConnectingProjection (finiteRowFamily n E) (finitePredecessorFamily n E a.val)
        α (α - finiteRowExponent n a.val) z) =
    -quotientConnectingProjection (finiteRowFamily n E) (finitePredecessorFamily n E a.val)
        α (α - finiteRowExponent n a.val)
        (quotientTotalDifferential (finiteRowFamily n E) α z) := by
  let B := finiteRowFamily n E
  let C := finitePredecessorFamily n E a.val
  let γ := α - finiteRowExponent n a.val
  let D := quotientTotalDifferential (k := k) B α
  let q := quotientConnectingProjection (k := k) B C α γ
  have hzfull : z.val ∈ TotalFaceModule (fullKoszulFaces α) :=
    Submodule.span_mono (Set.image_mono (fun _ hs => hs.1)) z.property
  have hdfull := boundary_mem_basisSpan (fullKoszulFaces_downward α) hzfull
  have hideal : Simplicial.boundary z.val - (D z).val ∈
      TotalFaceModule (koszulFaces B α) := by
    have hh := (TotalFaceModule (k := k) (koszulFaces B α)).neg_mem
      (relativeProjection_sub_mem_full_discarded (Simplicial.basis (k := k))
        (fullKoszulFaces α) (forbiddenKoszulFaces B α) hdfull)
    simpa only [neg_sub, D, quotientTotalDifferential_val, quotientFaceProjection] using hh
  let w : TotalFaceModule (k := k)
      (koszulFaces (exponentPowerFamily B 1) α) :=
    ⟨Simplicial.boundary z.val - (D z).val, by
      simpa only [exponentPowerFamily_one] using hideal⟩
  have hqzero : quotientFaceProjection C γ (D z).val = 0 :=
    quotientProjection_residual_zero B C α (finiteRowExponent n a.val)
      ⟨finiteRowExponent n a.val, Finset.mem_image.mpr ⟨a.val, a.property, rfl⟩, le_rfl⟩
      hα.1 (D z)
  have hproj : firstPowerFaceProjection hE hα w = q z := by
    apply Subtype.ext
    rw [firstPowerFaceProjection_val]
    change quotientFaceProjection C γ
      (Simplicial.boundary z.val - (D z).val) = quotientFaceProjection C γ (Simplicial.boundary z.val)
    rw [map_sub, hqzero, sub_zero]
  have hh := firstPowerFaceProjection_differential hE hα w
  rw [hproj] at hh
  have hval := congrArg Subtype.val hh
  rw [firstPowerFaceProjection_val, idealTotalDifferential_val] at hval
  change quotientFaceProjection C γ
      (Simplicial.boundary (Simplicial.boundary z.val - (D z).val)) =
    (quotientTotalDifferential C γ (q z)).val at hval
  rw [map_sub, Simplicial.boundary_boundary, zero_sub, map_neg] at hval
  apply Subtype.ext
  exact hval.symm

theorem firstPowerConnecting_boundaries (hE : finiteLatticeClosed n E)
    {α : Exponent (FiniteVariable.{u} n)} {a : E} (hα : RowMaximum α a.val)
    (z : TotalFaceModule (k := k) (quotientKoszulFaces (finiteRowFamily n E) α)) :
    ∃ y, quotientTotalDifferential (finitePredecessorFamily n E a.val)
      (α - finiteRowExponent n a.val) y =
      quotientConnectingProjection (finiteRowFamily n E) (finitePredecessorFamily n E a.val)
        α (α - finiteRowExponent n a.val)
        (quotientTotalDifferential (finiteRowFamily n E) α z) := by
  refine ⟨-quotientConnectingProjection (finiteRowFamily n E)
    (finitePredecessorFamily n E a.val) α (α - finiteRowExponent n a.val) z, ?_⟩
  rw [map_neg, firstPowerConnecting_anticommutes hE hα, neg_neg]

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.FirstPowerConnectingSurjective -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
open FourPapers.FilteredHomology
universe u
variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

/-- Surjectivity of the actual connecting map, modulo actual boundaries, for
every finite sublattice. The proof lifts a predecessor cycle through the
already constructed first-power chain section, integrates the resulting ideal
cycle in the full Koszul strand, and applies the literal quotient projection. -/
theorem firstPowerConnecting_lift_cycle (hE : finiteLatticeClosed n E)
    {α : Exponent (FiniteVariable.{u} n)} {a : E} (hα : RowMaximum α a.val)
    (e : FiniteVariable.{u} n) (he : 0 < α e)
    (x : TotalFaceModule (k := k)
      (quotientKoszulFaces (finitePredecessorFamily n E a.val)
        (α - finiteRowExponent n a.val)))
    (hx : quotientTotalDifferential (finitePredecessorFamily n E a.val)
      (α - finiteRowExponent n a.val) x = 0) :
    ∃ z : TotalFaceModule (k := k) (quotientKoszulFaces (finiteRowFamily n E) α),
      ∃ y : TotalFaceModule (k := k)
        (quotientKoszulFaces (finitePredecessorFamily n E a.val)
          (α - finiteRowExponent n a.val)),
      quotientTotalDifferential (finiteRowFamily n E) α z = 0 ∧
      quotientConnectingProjection (finiteRowFamily n E) (finitePredecessorFamily n E a.val)
        α (α - finiteRowExponent n a.val) z +
        quotientTotalDifferential (finitePredecessorFamily n E a.val)
          (α - finiteRowExponent n a.val) y = x := by
  let B := finiteRowFamily n E
  let C := finitePredecessorFamily n E a.val
  let γ := α - finiteRowExponent n a.val
  let t := firstPowerExteriorLift (k := k) hE hα x
  have htideal : t.val ∈ TotalFaceModule (koszulFaces B α) := by
    simpa only [B, exponentPowerFamily_one] using t.property
  have htfull : t.val ∈ TotalFaceModule (fullKoszulFaces α) :=
    Submodule.span_mono (Set.image_mono (fun _ h => h.1)) htideal
  have htcycle : Simplicial.boundary t.val = 0 := by
    have hh := firstPowerExteriorLift_differential (k := k) hE hα x
    rw [hx, map_zero] at hh
    exact congrArg Subtype.val hh
  let v := Simplicial.creation e t.val
  have hvfull : v ∈ TotalFaceModule (fullKoszulFaces α) :=
    creation_mem_basisSpan e (fun _ h => fullKoszulFaces_insert he h) htfull
  have hvboundary : Simplicial.boundary v = t.val := by
    simp only [v, Simplicial.boundary_creation, htcycle, map_zero, sub_zero]
  let z : TotalFaceModule (k := k) (quotientKoszulFaces B α) :=
    ⟨quotientFaceProjection B α v, relativeProjection_mem _ _ _ _⟩
  have hzcycle : quotientTotalDifferential B α z = 0 := by
    apply Subtype.ext
    change quotientFaceProjection B α (Simplicial.boundary (quotientFaceProjection B α v)) = 0
    rw [quotientFaceProjection_boundary B α hvfull, hvboundary]
    exact quotientFaceProjection_zero_on_ideal B α htideal
  have hwideal : v - z.val ∈ TotalFaceModule (koszulFaces B α) := by
    have hh := (TotalFaceModule (k := k) (koszulFaces B α)).neg_mem
      (relativeProjection_sub_mem_full_discarded (Simplicial.basis (k := k))
        (fullKoszulFaces α) (forbiddenKoszulFaces B α) hvfull)
    change v - quotientFaceProjection B α v ∈ TotalFaceModule (koszulFaces B α)
    simpa only [neg_sub, quotientFaceProjection] using hh
  let w : TotalFaceModule (k := k) (koszulFaces (exponentPowerFamily B 1) α) :=
    ⟨v - z.val, by simpa only [exponentPowerFamily_one] using hwideal⟩
  refine ⟨z, firstPowerFaceProjection hE hα w, hzcycle, ?_⟩
  rw [← firstPowerFaceProjection_differential]
  apply Subtype.ext
  rw [Submodule.coe_add, quotientConnectingProjection_val, firstPowerFaceProjection_val,
    idealTotalDifferential_val]
  change quotientFaceProjection C γ (Simplicial.boundary z.val) +
      quotientFaceProjection C γ (Simplicial.boundary (v - z.val)) = x.val
  have hadd : z.val + (v - z.val) = v := by abel
  rw [← map_add, ← map_add, hadd, hvboundary]
  have hp := congrArg Subtype.val (firstPowerFaceProjection_lift (k := k) hE hα x)
  rw [firstPowerFaceProjection_val] at hp
  exact hp

theorem firstPowerConnecting_cycle_span (hE : finiteLatticeClosed n E)
    {α : Exponent (FiniteVariable.{u} n)} {a : E} (hα : RowMaximum α a.val)
    (e : FiniteVariable.{u} n) (he : 0 < α e) :
    LinearMap.ker (quotientTotalDifferential (k := k)
      (finitePredecessorFamily n E a.val) (α - finiteRowExponent n a.val)) ≤
      (LinearMap.ker (quotientTotalDifferential (finiteRowFamily n E) α)).map
        (quotientConnectingProjection (finiteRowFamily n E) (finitePredecessorFamily n E a.val)
          α (α - finiteRowExponent n a.val)) ⊔
      LinearMap.range (quotientTotalDifferential (finitePredecessorFamily n E a.val)
        (α - finiteRowExponent n a.val)) := by
  intro x hx
  obtain ⟨z, y, hz, hzy⟩ := firstPowerConnecting_lift_cycle hE hα e he x hx
  exact Submodule.mem_sup.mpr ⟨_, ⟨z, hz, rfl⟩, _, ⟨y, rfl⟩, hzy⟩

/-- The quotient strand and the distinguished predecessor strand have
isomorphic integral homology in all rows. Exterior degree is lowered by one
by the displayed connecting map; no first-power Betti equality is assumed. -/
def firstPowerConnectingHomologyEquiv (hE : finiteLatticeClosed n E)
    {α : Exponent (FiniteVariable.{u} n)} {a : E} (hα : RowMaximum α a.val)
    (e : FiniteVariable.{u} n) (he : 0 < α e) :
    Homology (quotientTotalDifferential (k := k) (finiteRowFamily n E) α)
      (quotientTotalDifferential (finiteRowFamily n E) α)
      (quotientTotalDifferential_comp (finiteRowFamily n E) α) ≃ₗ[k]
    Homology (quotientTotalDifferential (k := k) (finitePredecessorFamily n E a.val)
        (α - finiteRowExponent n a.val))
      (quotientTotalDifferential (finitePredecessorFamily n E a.val)
        (α - finiteRowExponent n a.val))
      (quotientTotalDifferential_comp (finitePredecessorFamily n E a.val)
        (α - finiteRowExponent n a.val)) :=
  closedGraphHomologyEquiv _ _ _ _ _
    (firstPowerConnecting_cycle hE hα)
    (firstPowerConnecting_boundaries hE hα)
    (firstPowerConnecting_detects_boundaries hE hα e he)
    (firstPowerConnecting_cycle_span hE hα e he)

end FourPapers.Sublattice
end

#print axioms FourPapers.Sublattice.firstPowerConnectingHomologyEquiv

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphIntegral -/
section

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
open FourPapers.FilteredHomology
universe u
variable {k : Type u} [CommRing k]

variable {N : ℕ} {G : SimpleGraph (Fin N)}

/-- The colon target is spanned, modulo actual boundaries, by the connecting
images of actual source cycles. This is the surjectivity half of the integral
homology recursion, stronger than a dimension comparison over a field. -/
theorem closedGraphConnecting_cycle_span (hG : IntervalLabeling G)
    {α : Exponent (FiniteVariable.{u} (GraphRows N))}
    {a : FiniteTuple (GraphRows N)} (ha : a ∈ graphEdgeLattice G)
    (hα : RowMaximum α a) (hsq : ∀ v, α v ≤ 1) :
    LinearMap.ker (quotientTotalDifferential (k := k)
      (finitePredecessorFamily (GraphRows N) (graphEdgeLattice G) a)
      (α - finiteRowExponent (GraphRows N) a)) ≤
      (LinearMap.ker (quotientTotalDifferential
        (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) α)).map
        (quotientConnectingProjection (finiteRowFamily (GraphRows N) (graphEdgeLattice G))
          (finitePredecessorFamily (GraphRows N) (graphEdgeLattice G) a)
          α (α - finiteRowExponent (GraphRows N) a)) ⊔
      LinearMap.range (quotientTotalDifferential
        (finitePredecessorFamily (GraphRows N) (graphEdgeLattice G) a)
        (α - finiteRowExponent (GraphRows N) a)) := by
  have hsmall := closedGraph_quotient_cycles_generated (k := k) hG
    (graphColonResidualDegree G a (α - finiteRowExponent (GraphRows N) a))
  exact (closedGraphColon_cycles_in_connecting_image (k := k) hG ha hα hsq hsmall).trans
    (sup_le_sup (Submodule.map_mono (closedGraphProductSpan_le_cycles (k := k) (G := G) α))
      le_rfl)

/-- The fine strand and its smaller residual graph strand have isomorphic
integral homology. The first equivalence is the actual connecting map; the
second removes the fixed exterior factor with its unit sign. -/
def closedGraphResidualHomologyEquiv (hG : IntervalLabeling G)
    {α : Exponent (FiniteVariable.{u} (GraphRows N))}
    {a : FiniteTuple (GraphRows N)} (ha : a ∈ graphEdgeLattice G)
    (hα : RowMaximum α a) (hsq : ∀ v, α v ≤ 1) :
    ClosedGraphFaceHomology (k := k)
      (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) α ≃ₗ[k]
    ClosedGraphFaceHomology (k := k)
      (finiteRowFamily (GraphRows N) (graphEdgeLattice G))
      (graphColonResidualDegree G a (α - finiteRowExponent (GraphRows N) a)) := by
  let γ := α - finiteRowExponent (GraphRows N) a
  let δ := graphColonResidualDegree G a γ
  let B := finiteRowFamily (GraphRows N) (graphEdgeLattice G)
  let C := finitePredecessorFamily (GraphRows N) (graphEdgeLattice G) a
  let D := quotientTotalDifferential (k := k) B α
  let d := quotientTotalDifferential (k := k) C γ
  let q := quotientConnectingProjection (k := k) B C α γ
  let e : FiniteVariable.{u} (GraphRows N) := ⟨0, ULift.up (a 0)⟩
  have he : 0 < α e := by
    have hh := hα.1 e
    simpa only [e, finiteRowExponent_apply, ite_true, Nat.succ_le_iff] using hh
  let qH := closedGraphHomologyEquiv D d
    (quotientTotalDifferential_comp B α) (quotientTotalDifferential_comp C γ) q
    (fun x hx => firstPowerConnecting_cycle (graphEdgeLattice_closed hG)
      (a := ⟨a, ha⟩) hα x hx)
    (fun x => firstPowerConnecting_boundaries (graphEdgeLattice_closed hG)
      (a := ⟨a, ha⟩) hα x)
    (fun x hx hh => firstPowerConnecting_detects_boundaries (graphEdgeLattice_closed hG)
      (a := ⟨a, ha⟩) hα e he x hx hh)
    (closedGraphConnecting_cycle_span hG ha hα hsq)
  let f := closedGraphColonFactor (k := k) hG ha γ
    (rowMaximum_residual_squarefree hα hsq).1
    (rowMaximum_residual_squarefree hα hsq).2.1
    (rowMaximum_residual_squarefree hα hsq).2.2
  let fH := closedGraphScaledHomologyEquiv (quotientTotalDifferential (k := k) B δ) d
    (quotientTotalDifferential_comp B δ) (quotientTotalDifferential_comp C γ) f
    ((-1 : k) ^ (graphColonLinearDegree G a γ).support.card)
    ((IsUnit.neg isUnit_one).pow _)
    (closedGraphColonFactor_differential hG ha γ
      (rowMaximum_residual_squarefree hα hsq).1
      (rowMaximum_residual_squarefree hα hsq).2.1
      (rowMaximum_residual_squarefree hα hsq).2.2)
  exact qH.trans fH.symm

section ZeroStrand
variable {V : Type u} [Fintype V] [LinearOrder V]

def closedGraphZeroStrandHomologyEquiv (B : Family V) (hB : ¬Contains B 0) :
    ClosedGraphFaceHomology (k := k) B 0 ≃ₗ[k] k := by
  let Q := quotientKoszulFaces B 0
  let I := {F : Finset V // Q F}
  letI : Unique I :=
    { default := ⟨∅, (quotientKoszulFaces_zero_iff B hB ∅).mpr rfl⟩
      uniq := fun F => Subtype.ext ((quotientKoszulFaces_zero_iff B hB F.val).mp F.property) }
  let e : TotalFaceModule (k := k) Q ≃ₗ[k] k :=
    (totalFaceBasis (k := k) Q).equivFun.trans (LinearEquiv.funUnique I k k)
  have hzero : quotientTotalDifferential (k := k) B 0 = 0 := by
    apply LinearMap.ext
    intro x
    apply quotientTotalDifferential_zero_degree B 0 x
    change x.val ∈ Simplicial.Chains Q 0
    apply Submodule.span_mono (Set.image_mono ?_) x.property
    intro F hF
    exact ⟨hF, by rw [(quotientKoszulFaces_zero_iff B hB F).mp hF]; rfl⟩
  let e₀ : ClosedGraphFaceHomology (k := k) B 0 ≃ₗ[k]
      TotalFaceModule (k := k) Q := by
    unfold ClosedGraphFaceHomology
    exact closedGraphZeroDifferentialHomologyEquiv (R := k)
      (M := TotalFaceModule (k := k) Q) (quotientTotalDifferential B 0)
      (quotientTotalDifferential_comp B 0) hzero
  exact e₀.trans e

end ZeroStrand

/-- The two possible integral models of a fine strand: zero, or one copy of
the coefficient ring. This predicate asserts an actual module equivalence in
the nonzero case; it is stronger than a Betti-number calculation. -/
def ClosedGraphSmallFreeModel (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] : Prop :=
  Subsingleton M ∨ Nonempty (M ≃ₗ[R] R)

lemma ClosedGraphSmallFreeModel.of_equiv
    {R M P : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup P]
    [Module R M] [Module R P] (e : M ≃ₗ[R] P) (h : ClosedGraphSmallFreeModel R P) :
    ClosedGraphSmallFreeModel R M := by
  unfold ClosedGraphSmallFreeModel at h ⊢
  cases h with
  | inl h => exact Or.inl ⟨fun x y => e.injective (h.allEq (e x) (e y))⟩
  | inr hf => exact Or.inr ⟨e.trans (Classical.choice hf)⟩

lemma ClosedGraphSmallFreeModel.free
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (h : ClosedGraphSmallFreeModel R M) : Module.Free R M := by
  unfold ClosedGraphSmallFreeModel at h
  cases h with
  | inl h =>
    letI : Subsingleton M := h
    infer_instance
  | inr he => exact Module.Free.of_equiv (Classical.choice he).symm

/-- Every fine quotient Koszul strand of an interval-labelled graph has
integral homology zero or free of rank one. The proof uses the actual residual
homology isomorphism, and therefore excludes torsion without appealing to
computational evidence or equality of dimensions over selected fields. -/
theorem closedGraph_fine_homology_small (hG : IntervalLabeling G)
    (α : Exponent (FiniteVariable.{u} (GraphRows N))) :
    ClosedGraphSmallFreeModel k (ClosedGraphFaceHomology (k := k)
      (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) α) := by
  have hall : ∀ m : ℕ, ∀ β : Exponent (FiniteVariable.{u} (GraphRows N)), β.degree = m →
      ClosedGraphSmallFreeModel k (ClosedGraphFaceHomology (k := k)
        (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) β) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro β hdegree
      let B := finiteRowFamily (GraphRows N) (graphEdgeLattice G)
      by_cases hzero : β = 0
      · subst β
        apply Or.inr
        refine ⟨closedGraphZeroStrandHomologyEquiv B ?_⟩
        rintro ⟨b, hb, hb0⟩
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
        have hh := hb0 ⟨0, ULift.up (a 0)⟩
        simp [finiteRowExponent_apply] at hh
      obtain ⟨e, he⟩ : ∃ e, 0 < β e := by
        by_contra h
        push_neg at h
        apply hzero
        ext v
        exact Nat.eq_zero_of_le_zero (h v)
      by_cases hsq : ∀ v, β v ≤ 1
      · by_cases hcontains : Contains B β
        · obtain ⟨b, hb, hbβ⟩ := hcontains
          obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hb
          obtain ⟨a, ha⟩ := rowMaximum_exists_of_generator β hbβ
          by_cases haE : a ∈ graphEdgeLattice G
          · let δ := graphColonResidualDegree G a (β - finiteRowExponent (GraphRows N) a)
            have hδ : δ.degree < m := by
              rw [← hdegree]
              exact graphColonResidualDegree_lt (G := G) ha
            exact ClosedGraphSmallFreeModel.of_equiv
              (closedGraphResidualHomologyEquiv (k := k) hG haE ha hsq)
              (ih δ.degree hδ δ rfl)
          · apply Or.inl
            apply closedGraphHomology_subsingleton_of_boundaries
            intro z hz
            exact firstPowerQuotientCycle_boundary_of_missing_maximum
              (graphEdgeLattice_closed hG) ha haE e he z hz
        · apply Or.inl
          apply closedGraphHomology_subsingleton_of_boundaries
          intro z hz
          exact quotientCycle_boundary_of_not_contains B β hcontains e he z hz
      · push_neg at hsq
        obtain ⟨v, hv⟩ := hsq
        apply Or.inl
        apply closedGraphHomology_subsingleton_of_boundaries
        intro z hz
        apply quotient_cycle_boundary_of_two_le (e := v) _ (by omega) z hz
        intro c hc
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
        rcases v with ⟨r, ⟨j⟩⟩
        simp only [finiteRowExponent_apply]
        split_ifs <;> omega
  exact hall α.degree α rfl

theorem closedGraph_fine_homology_free (hG : IntervalLabeling G)
    (α : Exponent (FiniteVariable.{u} (GraphRows N))) :
    Module.Free k (ClosedGraphFaceHomology (k := k)
      (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) α) :=
  (closedGraph_fine_homology_small (k := k) hG α).free

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphRestrictedIntegral -/
section

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
open FourPapers.FilteredHomology
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

private def restrictedClassicalFilter (S : V → Prop) (α : Exponent V) : Exponent V :=
  @Finsupp.filter V ℕ _ S (fun v => Classical.propDecidable (S v)) α

private lemma restrictedFilter_eq_classical (S : V → Prop) (h : DecidablePred S)
    (α : Exponent V) :
    @Finsupp.filter V ℕ _ S h α = restrictedClassicalFilter S α :=
  congrArg (fun d : DecidablePred S => @Finsupp.filter V ℕ _ S d α)
    (Subsingleton.elim h (fun v => Classical.propDecidable (S v)))

/-- Equality of the literal quotient face predicates gives an equivalence of
the actual homology quotients, through the same exterior vectors. -/
def quotientFaceHomologyEquivOfFaces (B C : Family V) (α β : Exponent V)
    (h : quotientKoszulFaces B α = quotientKoszulFaces C β) :
    ClosedGraphFaceHomology (k := k) B α ≃ₗ[k] ClosedGraphFaceHomology (k := k) C β := by
  let f : TotalFaceModule (k := k) (quotientKoszulFaces B α) ≃ₗ[k]
      TotalFaceModule (k := k) (quotientKoszulFaces C β) :=
    { toFun x := ⟨x.val, by simpa only [← h] using x.property⟩
      invFun x := ⟨x.val, by simpa only [h] using x.property⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  unfold ClosedGraphFaceHomology
  apply closedGraphScaledHomologyEquiv (R := k)
    (M := TotalFaceModule (k := k) (quotientKoszulFaces B α))
    (N := TotalFaceModule (k := k) (quotientKoszulFaces C β))
    (quotientTotalDifferential B α)
    (quotientTotalDifferential C β) (quotientTotalDifferential_comp B α)
    (quotientTotalDifferential_comp C β) f 1 isUnit_one
  intro x
  apply Subtype.ext
  change quotientFaceProjection C β (Simplicial.boundary x.val) =
    (1 : k) • quotientFaceProjection B α (Simplicial.boundary x.val)
  simp only [one_smul, quotientFaceProjection_eq_faceProjection, h]

lemma forbiddenKoszulFaces_insert_of_free_variable {B : Family V}
    {α : Exponent V} {e : V} (hB : ∀ b ∈ B, b e = 0) (F : Finset V) :
    forbiddenKoszulFaces B α (insert e F) ↔ forbiddenKoszulFaces B α F := by
  constructor
  · exact forbiddenKoszulFaces_downward B α (Finset.subset_insert e F)
  · rintro ⟨b, hb, hbα⟩
    refine ⟨b, hb, ?_⟩
    intro v
    by_cases hv : v = e
    · subst v
      rw [hB b hb]
      exact zero_le
    · simpa [Finsupp.tsub_apply, faceExponent_apply, hv] using hbα v

theorem quotientTotalCreation_contracts_free_variable {B : Family V}
    {α : Exponent V} {e : V} (hB : ∀ b ∈ B, b e = 0) (he : 0 < α e) :
    quotientTotalDifferential (k := k) B α ∘ₗ quotientTotalCreation B α e +
      quotientTotalCreation B α e ∘ₗ quotientTotalDifferential B α = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change quotientFaceProjection B α (Simplicial.boundary
      (quotientFaceProjection B α (Simplicial.creation e x.val))) +
    quotientFaceProjection B α (Simplicial.creation e
      (quotientFaceProjection B α (Simplicial.boundary x.val))) = x.val
  unfold quotientFaceProjection
  refine relative_contraction_identity (K := k) (M := Simplicial.Ambient V k)
    (I := Finset V) (Simplicial.basis (k := k)) (fullKoszulFaces α)
    (forbiddenKoszulFaces B α) (Simplicial.boundary (k := k))
    (Simplicial.creation (k := k) e) ?_ ?_ ?_ ?_ ?_ x.property
  · exact fun _ hx => boundary_mem_basisSpan (fullKoszulFaces_downward α) hx
  · exact fun _ hx => creation_mem_basisSpan e
      (fun _ hs => fullKoszulFaces_insert he hs) hx
  · exact fun _ hx => boundary_mem_basisSpan (forbiddenKoszulFaces_downward B α) hx
  · exact fun _ hx => creation_mem_basisSpan e
      (fun F hF => (forbiddenKoszulFaces_insert_of_free_variable hB F).mpr hF) hx
  · intro y
    rw [Simplicial.boundary_creation]
    exact sub_add_cancel _ _

lemma quotient_cycle_boundary_free_variable {B : Family V}
    {α : Exponent V} {e : V} (hB : ∀ b ∈ B, b e = 0) (he : 0 < α e)
    (z : TotalFaceModule (k := k) (quotientKoszulFaces B α))
    (hz : quotientTotalDifferential B α z = 0) :
    ∃ y, quotientTotalDifferential B α y = z := by
  refine ⟨quotientTotalCreation B α e z, ?_⟩
  have hh := LinearMap.congr_fun (quotientTotalCreation_contracts_free_variable hB he) z
  change quotientTotalDifferential B α (quotientTotalCreation B α e z) +
    quotientTotalCreation B α e (quotientTotalDifferential B α z) = z at hh
  simpa only [hz, map_zero, add_zero] using hh

variable {N : ℕ} {G : SimpleGraph (Fin N)}

/-- The integral result holds for arbitrary separate row restrictions. A
positive coordinate outside the retained variables is contracted explicitly;
inside the restriction the quotient face complex equals the original one. -/
theorem closedGraph_restricted_homology_small (hG : IntervalLabeling G)
    (A : ∀ r, Finset (Fin (GraphRows N r)))
    (α : Exponent (FiniteVariable.{u} (GraphRows N))) :
    ClosedGraphSmallFreeModel k (ClosedGraphFaceHomology (k := k)
      (finiteRowFamily (GraphRows N) (finiteRowRestriction (graphEdgeLattice G) A)) α) := by
  by_cases hs : SupportedRows A α
  · exact ClosedGraphSmallFreeModel.of_equiv
      (quotientFaceHomologyEquivOfFaces _ _ α α
        (quotientFaces_finiteRowRestriction (graphEdgeLattice G) A α hs))
      (closedGraph_fine_homology_small (k := k) hG α)
  · change ¬∀ r j, 0 < α ⟨r, ULift.up j⟩ → j ∈ A r at hs
    push_neg at hs
    obtain ⟨r, j, hj, hjA⟩ := hs
    apply Or.inl
    apply closedGraphHomology_subsingleton_of_boundaries
    intro z hz
    apply quotient_cycle_boundary_free_variable (e := ⟨r, ULift.up j⟩) _ hj z hz
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    have haA := ((mem_finiteRowRestriction _ A a).mp ha).2 r
    have hne : a r ≠ j := fun he => hjA (he ▸ haA)
    simp only [finiteRowExponent_apply, if_neg hne]

/-- Splitting off a disjoint linear-variable ideal forces a single exterior
face in every squarefree fine degree. -/
lemma linearVariableQuotient_faces_factor (L : Finset V) (B : Family V)
    (hB : ∀ b ∈ B, ∀ v, b v ≠ 0 → v ∉ L) (α : Exponent V)
    (hsq : ∀ v, α v ≤ 1) :
    quotientKoszulFaces (variableMonomialFamily L ∪ B) α =
      splitFacePredicate (fun v => v ∈ L)
        (fun F => F = (α.filter (fun v => v ∈ L)).support)
        (quotientKoszulFaces B (α.filter (fun v => v ∉ L))) := by
  have hsep : quotientKoszulFaces (variableMonomialFamily L ∪ B) α =
      splitFacePredicate (fun v => v ∈ L)
        (quotientKoszulFaces (variableMonomialFamily L) (α.filter (fun v => v ∈ L)))
        (quotientKoszulFaces B (α.filter (fun v => v ∉ L))) := by
    funext F
    apply propext
    simpa only [restrictedFilter_eq_classical] using quotientSeparated_faces
      (fun v => v ∈ L) (variableMonomialFamily L) B
      (by
        intro b hb v hv
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hb
        by_contra hn
        have hne : w ≠ v := by intro he; exact hn (he ▸ hw)
        simp [Finsupp.single_apply, hne] at hv)
      hB α F
  rw [hsep, variableQuotient_faces_eq_support L α hsq]

def linearVariableQuotientFactor (L : Finset V) (B : Family V)
    (hB : ∀ b ∈ B, ∀ v, b v ≠ 0 → v ∉ L) (α : Exponent V)
    (hsq : ∀ v, α v ≤ 1) :
    TotalFaceModule (k := k) (quotientKoszulFaces B (α.filter (fun v => v ∉ L))) ≃ₗ[k]
      TotalFaceModule (k := k) (quotientKoszulFaces (variableMonomialFamily L ∪ B) α) :=
  (fixedFaceFactorEquiv (fun v => v ∈ L) (α.filter (fun v => v ∈ L)).support
    (quotientKoszulFaces B (α.filter (fun v => v ∉ L)))
    (by
      intro v hv
      have hn := Finsupp.mem_support_iff.mp hv
      by_contra hh
      simp [Finsupp.filter_apply, hh] at hn)
    (by
      intro F hF v hv hn
      have hh := hF.1 v
      simp [faceExponent_apply, Finsupp.filter_apply, hv, hn] at hh)).trans
    (LinearEquiv.ofEq _ _ (by rw [linearVariableQuotient_faces_factor L B hB α hsq]))

lemma linearVariableQuotientFactor_val (L : Finset V) (B : Family V)
    (hB : ∀ b ∈ B, ∀ v, b v ≠ 0 → v ∉ L) (α : Exponent V)
    (hsq : ∀ v, α v ≤ 1)
    (x : TotalFaceModule (k := k) (quotientKoszulFaces B (α.filter (fun v => v ∉ L)))) :
    (linearVariableQuotientFactor L B hB α hsq x).val =
      Simplicial.basis (α.filter (fun v => v ∈ L)).support * x.val := by
  simp only [linearVariableQuotientFactor, LinearEquiv.trans_apply,
    LinearEquiv.coe_ofEq_apply]
  exact fixedFaceFactorEquiv_val (k := k) _ _ _ _ _ x

lemma linearVariableQuotientFactor_differential (L : Finset V) (B : Family V)
    (hB : ∀ b ∈ B, ∀ v, b v ≠ 0 → v ∉ L) (α : Exponent V)
    (hsq : ∀ v, α v ≤ 1)
    (x : TotalFaceModule (k := k) (quotientKoszulFaces B (α.filter (fun v => v ∉ L)))) :
    quotientTotalDifferential (variableMonomialFamily L ∪ B) α
      (linearVariableQuotientFactor L B hB α hsq x) =
      (-1 : k) ^ (α.filter (fun v => v ∈ L)).support.card •
        linearVariableQuotientFactor L B hB α hsq
          (quotientTotalDifferential B (α.filter (fun v => v ∉ L)) x) := by
  have hh := congrArg Subtype.val (fixedFaceFactorEquiv_differential
    (fun v => v ∈ L) (α.filter (fun v => v ∈ L)).support
    (quotientKoszulFaces B (α.filter (fun v => v ∉ L)))
    (by
      intro v hv
      have hn := Finsupp.mem_support_iff.mp hv
      by_contra h
      simp [Finsupp.filter_apply, h] at hn)
    (by
      intro F hF v hv hn
      have h := hF.1 v
      simp [faceExponent_apply, Finsupp.filter_apply, hv, hn] at h) x)
  apply Subtype.ext
  change quotientFaceProjection _ α
    (Simplicial.boundary ((linearVariableQuotientFactor L B hB α hsq x).val)) = _
  simp only [Submodule.coe_smul, linearVariableQuotientFactor_val]
  rw [quotientFaceProjection_eq_faceProjection,
    linearVariableQuotient_faces_factor L B hB α hsq,
    quotientTotalDifferential_eq_projected]
  simpa only [projectedTotalDifferential, LinearMap.codRestrict_apply,
    LinearMap.comp_apply, Submodule.subtype_apply, fixedFaceFactorEquiv_val,
    Submodule.coe_smul] using hh

def linearVariableQuotientHomologyEquiv (L : Finset V) (B : Family V)
    (hB : ∀ b ∈ B, ∀ v, b v ≠ 0 → v ∉ L) (α : Exponent V)
    (hsq : ∀ v, α v ≤ 1) :
    ClosedGraphFaceHomology (k := k) (variableMonomialFamily L ∪ B) α ≃ₗ[k]
      ClosedGraphFaceHomology (k := k) B (α.filter (fun v => v ∉ L)) := by
  let e : ClosedGraphFaceHomology (k := k) B (α.filter (fun v => v ∉ L)) ≃ₗ[k]
      ClosedGraphFaceHomology (k := k) (variableMonomialFamily L ∪ B) α := by
    unfold ClosedGraphFaceHomology
    exact closedGraphScaledHomologyEquiv (R := k)
      (M := TotalFaceModule (k := k) (quotientKoszulFaces B (α.filter (fun v => v ∉ L))))
      (N := TotalFaceModule (k := k) (quotientKoszulFaces (variableMonomialFamily L ∪ B) α))
      (quotientTotalDifferential B (α.filter (fun v => v ∉ L)))
      (quotientTotalDifferential (variableMonomialFamily L ∪ B) α)
      (quotientTotalDifferential_comp B (α.filter (fun v => v ∉ L)))
      (quotientTotalDifferential_comp (variableMonomialFamily L ∪ B) α)
      (linearVariableQuotientFactor L B hB α hsq)
      ((-1 : k) ^ (α.filter (fun v => v ∈ L)).support.card)
      ((IsUnit.neg isUnit_one).pow _)
      (linearVariableQuotientFactor_differential L B hB α hsq)
  exact e.symm

private lemma restrictedVariableFamily_le_one (L : Finset V)
    (b : Exponent V) (hb : b ∈ variableMonomialFamily L) (v : V) : b v ≤ 1 := by
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hb
  simp only [Finsupp.single_apply]
  split_ifs <;> omega

theorem closedGraph_linear_restriction_homology_small (hG : IntervalLabeling G)
    (L : Finset (FiniteVariable.{u} (GraphRows N)))
    (A : ∀ r, Finset (Fin (GraphRows N r)))
    (hA : ∀ r j, j ∈ A r → (⟨r, ULift.up j⟩ : FiniteVariable.{u} (GraphRows N)) ∉ L)
    (α : Exponent (FiniteVariable.{u} (GraphRows N))) :
    ClosedGraphSmallFreeModel k (ClosedGraphFaceHomology (k := k)
      (variableMonomialFamily L ∪
        finiteRowFamily (GraphRows N) (finiteRowRestriction (graphEdgeLattice G) A)) α) := by
  by_cases hsq : ∀ v, α v ≤ 1
  · let B := finiteRowFamily (GraphRows N) (finiteRowRestriction (graphEdgeLattice G) A)
    have hB : ∀ b ∈ B, ∀ v, b v ≠ 0 → v ∉ L := by
      intro b hb v hv
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
      rcases v with ⟨r, ⟨j⟩⟩
      have haA := ((mem_finiteRowRestriction _ A a).mp ha).2 r
      by_cases he : a r = j
      · exact hA r j (he ▸ haA)
      · simp [finiteRowExponent_apply, he] at hv
    let C := variableMonomialFamily L ∪ B
    change ClosedGraphSmallFreeModel k (ClosedGraphFaceHomology (k := k) C α)
    letI : DecidableEq (FiniteVariable.{u} (GraphRows N)) := LinearOrder.toDecidableEq
    let C' := variableMonomialFamily L ∪ B
    have hC : C = C' := by
      ext b
      simp only [C, C', Finset.mem_union]
    let e₀ : ClosedGraphFaceHomology (k := k) C α ≃ₗ[k]
        ClosedGraphFaceHomology (k := k) C' α :=
      quotientFaceHomologyEquivOfFaces C C' α α
        (congrArg (fun D => quotientKoszulFaces D α) hC)
    let δ := α.filter (fun v => v ∉ L)
    let e : ClosedGraphFaceHomology (k := k) C' α ≃ₗ[k]
        ClosedGraphFaceHomology (k := k) B δ :=
      linearVariableQuotientHomologyEquiv (k := k) L B hB α hsq
    have hsmall : ClosedGraphSmallFreeModel k (ClosedGraphFaceHomology (k := k) B δ) :=
      closedGraph_restricted_homology_small (k := k) hG A δ
    exact ClosedGraphSmallFreeModel.of_equiv (R := k)
      (M := ClosedGraphFaceHomology (k := k) C α)
      (P := ClosedGraphFaceHomology (k := k) B δ) (e₀.trans e) hsmall
  · push_neg at hsq
    obtain ⟨v, hv⟩ := hsq
    apply Or.inl
    apply closedGraphHomology_subsingleton_of_boundaries
    intro z hz
    apply quotient_cycle_boundary_of_two_le (e := v) _ (by omega) z hz
    intro b hb
    rcases Finset.mem_union.mp hb with hb | hb
    · exact restrictedVariableFamily_le_one L b hb v
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
      rcases v with ⟨r, ⟨j⟩⟩
      simp only [finiteRowExponent_apply]
      split_ifs <;> omega

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.UnitIntervalHomology -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
open FourPapers.FilteredHomology
universe u
variable {k : Type u} [CommRing k]
variable {d N : ℕ}
variable {E : Finset ((Fin (d+1) → Fin N))}

def facetColonLinearDegree (E : Finset ((Fin (d+1) → Fin N)))
    (a : (Fin (d+1) → Fin N))
    (γ : Exponent (FiniteVariable.{u} (UnitIntervalRows d N))) :=
  γ.filter (fun v => v ∈ facetLinearVariables E a)

def facetColonResidualDegree (E : Finset ((Fin (d+1) → Fin N)))
    (a : (Fin (d+1) → Fin N))
    (γ : Exponent (FiniteVariable.{u} (UnitIntervalRows d N))) :=
  γ.filter (fun v => v ∉ facetLinearVariables E a)

lemma facetColonDegree_add (a : (Fin (d+1) → Fin N))
    (γ : Exponent (FiniteVariable.{u} (UnitIntervalRows d N))) :
    facetColonLinearDegree E a γ + facetColonResidualDegree E a γ = γ :=
  Finsupp.filter_add_filter_not γ (fun v => v ∈ facetLinearVariables E a)

lemma unitInterval_rowMaximum_residual_squarefree
    {α : Exponent (FiniteVariable.{u} (UnitIntervalRows d N))}
    {a : (Fin (d+1) → Fin N)} (hα : RowMaximum α a)
    (hsq : ∀ v, α v ≤ 1) :
    (∀ v, (α - finiteRowExponent (UnitIntervalRows d N) a) v ≤ 1) ∧
      RowBound (α - finiteRowExponent (UnitIntervalRows d N) a) a ∧
      (∀ r, (α - finiteRowExponent (UnitIntervalRows d N) a) ⟨r, ULift.up (a r)⟩ = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v
    exact ((tsub_le_self : α - finiteRowExponent (UnitIntervalRows d N) a ≤ α) v).trans (hsq v)
  · intro v hv
    apply hα.2 v
    intro hzero
    exact hv (by simp [Finsupp.tsub_apply, hzero])
  · intro r
    have hle := hsq ⟨r, ULift.up (a r)⟩
    simp only [Finsupp.tsub_apply, finiteRowExponent_apply, ite_true]
    exact Nat.sub_eq_zero_of_le hle

lemma facetColonResidualDegree_lt
    {α : Exponent (FiniteVariable.{u} (UnitIntervalRows d N))}
    {a : (Fin (d+1) → Fin N)} (hα : RowMaximum α a) :
    (facetColonResidualDegree E a (α - finiteRowExponent (UnitIntervalRows d N) a)).degree < α.degree := by
  have hle : facetColonResidualDegree E a (α - finiteRowExponent (UnitIntervalRows d N) a) ≤
      α - finiteRowExponent (UnitIntervalRows d N) a := by
    intro v
    by_cases hv : v ∈ facetLinearVariables E a <;>
      simp [facetColonResidualDegree, Finsupp.filter_apply, hv]
  have hdeg := congrArg Finsupp.degree (tsub_add_cancel_of_le hα.1)
  simp only [map_add, finiteRowExponent_degree] at hdeg
  have hsmall := degree_mono hle
  omega

lemma facetResidualFine_supported
    {a : (Fin (d+1) → Fin N)}
    (γ : Exponent (FiniteVariable.{u} (UnitIntervalRows d N)))
    (hbound : RowBound γ a) (hzero : ∀ r, γ ⟨r, ULift.up (a r)⟩ = 0) :
    SupportedRows (facetResidualRows E a) (facetColonResidualDegree E a γ) := by
  intro r j hj
  have hjγ : 0 < γ ⟨r, ULift.up j⟩ := by
    by_cases hn : (⟨r, ULift.up j⟩ : FiniteVariable.{u} (UnitIntervalRows d N)) ∈ facetLinearVariables E a
    · simp [facetColonResidualDegree, Finsupp.filter_apply, hn] at hj
    · simpa [facetColonResidualDegree, Finsupp.filter_apply, hn] using hj
  have hn : (⟨r, ULift.up j⟩ : FiniteVariable.{u} (UnitIntervalRows d N)) ∉ facetLinearVariables E a := by
    intro hm
    simp [facetColonResidualDegree, Finsupp.filter_apply, hm] at hj
  have hjle := hbound ⟨r, ULift.up j⟩ (Nat.ne_of_gt hjγ)
  have hjne : j ≠ a r := by
    intro he
    subst j
    rw [hzero r] at hjγ
    omega
  have hjlt : j < a r := lt_of_le_of_ne hjle hjne
  revert hn hjlt
  refine Fin.cases ?_ (fun s => ?_) r
  · intro hn hjlt
    have hnot : ¬facetCoverAt E a j := fun h =>
      hn ((facetLinearVariables_zero a j).mpr ⟨hjlt, h⟩)
    simp [facetResidualRows, hnot]
  · intro hn hjlt
    have hle : j ≤ a s.castSucc := by
      by_contra h
      exact hn ((facetLinearVariables_succ a s j).mpr ⟨hjlt, lt_of_not_ge h⟩)
    simp [facetResidualRows, hle]

lemma facetResidualRows_lattice_eq (a : (Fin (d+1) → Fin N)) :
    finiteRowRestriction E (facetResidualRows E a) = facetResidualFacets E a := by
  ext b
  rw [mem_finiteRowRestriction, facetResidualFacets_restriction]

lemma facetColonResidual_quotientFaces (a : (Fin (d+1) → Fin N))
    (γ : Exponent (FiniteVariable.{u} (UnitIntervalRows d N)))
    (hbound : RowBound γ a) (hzero : ∀ r, γ ⟨r, ULift.up (a r)⟩ = 0) :
    quotientKoszulFaces (finiteRowFamily (UnitIntervalRows d N) (facetResidualFacets E a))
      (facetColonResidualDegree E a γ) =
    quotientKoszulFaces (finiteRowFamily (UnitIntervalRows d N) E)
      (facetColonResidualDegree E a γ) := by
  have h := quotientFaces_finiteRowRestriction E (facetResidualRows E a)
    (facetColonResidualDegree E a γ) (facetResidualFine_supported γ hbound hzero)
  rwa [facetResidualRows_lattice_eq] at h

lemma unitIntervalPredecessor_faces (hE : UnitIntervalFacetFamily E)
    {a : (Fin (d+1) → Fin N)} (ha : a ∈ E)
    (γ : Exponent (FiniteVariable.{u} (UnitIntervalRows d N))) :
    quotientKoszulFaces (finitePredecessorFamily (UnitIntervalRows d N) E a) γ =
      quotientKoszulFaces (facetColonFamily E a) γ := by
  apply quotientKoszulFaces_eq_of_contains
  intro α
  rw [← finiteCoordinatePredecessor_contains_iff hE.latticeClosed ha]
  exact facetCoordinateColon_contains_iff hE ha α

lemma facetResidualFamily_disjoint (hE : UnitIntervalFacetFamily E)
    (a : (Fin (d+1) → Fin N)) :
    ∀ b ∈ finiteRowFamily (UnitIntervalRows d N) (facetResidualFacets E a),
      ∀ v, b v ≠ 0 → v ∉ facetLinearVariables E a := by
  intro b hb v hv hvl
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hb
  exact hv (facetColon_disjoint_support hE hvl hc)

/-- The entire integral homology of a positive fine quotient strand reduces
to a smaller strand of the same arbitrary-row unit-interval ideal. The
equivalence is induced by the genuine connecting map and literal exterior
factorization of its actual colon. -/
def unitIntervalResidualHomologyEquiv (hE : UnitIntervalFacetFamily E)
    {α : Exponent (FiniteVariable.{u} (UnitIntervalRows d N))}
    {a : (Fin (d+1) → Fin N)} (ha : a ∈ E)
    (hα : RowMaximum α a) (hsq : ∀ v, α v ≤ 1) :
    ClosedGraphFaceHomology (k := k) (finiteRowFamily (UnitIntervalRows d N) E) α ≃ₗ[k]
      ClosedGraphFaceHomology (k := k) (finiteRowFamily (UnitIntervalRows d N) E)
        (facetColonResidualDegree E a (α - finiteRowExponent (UnitIntervalRows d N) a)) := by
  letI : DecidableEq (FiniteVariable.{u} (UnitIntervalRows d N)) :=
    (inferInstance : LinearOrder (FiniteVariable.{u} (UnitIntervalRows d N))).toDecidableEq
  let γ := α - finiteRowExponent (UnitIntervalRows d N) a
  let δ := facetColonResidualDegree E a γ
  let L := facetLinearVariables E a
  let D := finiteRowFamily (UnitIntervalRows d N) (facetResidualFacets E a)
  have hfamily : facetColonFamily E a = variableMonomialFamily L ∪ D := by
    dsimp only [L, D]
    ext b
    simp only [facetColonFamily, variableMonomialFamily, Finset.mem_union, Finset.mem_image]
  have hδ : γ.filter (fun v => v ∉ L) = δ := by
    dsimp only [L, δ]
    ext v
    by_cases hv : v ∈ facetLinearVariables E a <;>
      simp only [facetColonResidualDegree, Finsupp.filter_apply, hv, not_true_eq_false,
        not_false_eq_true, ite_false, ite_true]
  let e : FiniteVariable.{u} (UnitIntervalRows d N) := ⟨0, ULift.up (a 0)⟩
  have he : 0 < α e := by
    have hh := hα.1 e
    simpa only [e, finiteRowExponent_apply, ite_true, Nat.succ_le_iff] using hh
  let qH : ClosedGraphFaceHomology (k := k) (finiteRowFamily (UnitIntervalRows d N) E) α ≃ₗ[k]
      ClosedGraphFaceHomology (k := k) (finitePredecessorFamily (UnitIntervalRows d N) E a) γ := by
    unfold ClosedGraphFaceHomology
    exact firstPowerConnectingHomologyEquiv (k := k) hE.latticeClosed
      (a := ⟨a, ha⟩) hα e he
  let cH := quotientFaceHomologyEquivOfFaces (k := k)
    (finitePredecessorFamily (UnitIntervalRows d N) E a) (variableMonomialFamily L ∪ D) γ γ
    ((unitIntervalPredecessor_faces hE ha γ).trans
      (congrArg (fun H => quotientKoszulFaces H γ) hfamily))
  let fH := linearVariableQuotientHomologyEquiv (k := k) L D
    (facetResidualFamily_disjoint hE a) γ
    (unitInterval_rowMaximum_residual_squarefree hα hsq).1
  let rH := quotientFaceHomologyEquivOfFaces (k := k)
    D (finiteRowFamily (UnitIntervalRows d N) E) (γ.filter (fun v => v ∉ L)) δ
    (by
      rw [hδ]
      exact facetColonResidual_quotientFaces a γ
        (unitInterval_rowMaximum_residual_squarefree hα hsq).2.1
        (unitInterval_rowMaximum_residual_squarefree hα hsq).2.2)
  exact qH.trans (cH.trans (fH.trans rH))

/-- In every fine degree the actual quotient Koszul homology is either zero
or one copy of the coefficient ring, over every commutative ring. This is the
integral, arbitrary-row form of the positive recursion in Lemma 6.1. -/
theorem unitInterval_fine_homology_small (hE : UnitIntervalFacetFamily E)
    (α : Exponent (FiniteVariable.{u} (UnitIntervalRows d N))) :
    ClosedGraphSmallFreeModel k (ClosedGraphFaceHomology (k := k)
      (finiteRowFamily (UnitIntervalRows d N) E) α) := by
  have hall : ∀ m : ℕ, ∀ β : Exponent (FiniteVariable.{u} (UnitIntervalRows d N)), β.degree = m →
      ClosedGraphSmallFreeModel k (ClosedGraphFaceHomology (k := k)
        (finiteRowFamily (UnitIntervalRows d N) E) β) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro β hdegree
      let B := finiteRowFamily (UnitIntervalRows d N) E
      by_cases hzero : β = 0
      · subst β
        apply Or.inr
        refine ⟨closedGraphZeroStrandHomologyEquiv B ?_⟩
        rintro ⟨b, hb, hb0⟩
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
        have hh := hb0 ⟨0, ULift.up (a 0)⟩
        simp [finiteRowExponent_apply] at hh
      obtain ⟨e, he⟩ : ∃ e, 0 < β e := by
        by_contra h
        push_neg at h
        apply hzero
        ext v
        exact Nat.eq_zero_of_le_zero (h v)
      by_cases hsq : ∀ v, β v ≤ 1
      · by_cases hcontains : Contains B β
        · obtain ⟨b, hb, hbβ⟩ := hcontains
          obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hb
          obtain ⟨a, ha⟩ := rowMaximum_exists_of_generator β hbβ
          by_cases haE : a ∈ E
          · let δ := facetColonResidualDegree E a (β - finiteRowExponent (UnitIntervalRows d N) a)
            have hδ : δ.degree < m := by
              rw [← hdegree]
              exact facetColonResidualDegree_lt ha
            exact ClosedGraphSmallFreeModel.of_equiv
              (unitIntervalResidualHomologyEquiv (k := k) hE haE ha hsq)
              (ih δ.degree hδ δ rfl)
          · apply Or.inl
            apply closedGraphHomology_subsingleton_of_boundaries
            intro z hz
            exact firstPowerQuotientCycle_boundary_of_missing_maximum
              hE.latticeClosed ha haE e he z hz
        · apply Or.inl
          apply closedGraphHomology_subsingleton_of_boundaries
          intro z hz
          exact quotientCycle_boundary_of_not_contains B β hcontains e he z hz
      · push_neg at hsq
        obtain ⟨v, hv⟩ := hsq
        apply Or.inl
        apply closedGraphHomology_subsingleton_of_boundaries
        intro z hz
        apply quotient_cycle_boundary_of_two_le (e := v) _ (by omega) z hz
        intro c hc
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
        rcases v with ⟨r, ⟨j⟩⟩
        simp only [finiteRowExponent_apply]
        split_ifs <;> omega
  exact hall α.degree α rfl

theorem unitInterval_fine_homology_free (hE : UnitIntervalFacetFamily E)
    (α : Exponent (FiniteVariable.{u} (UnitIntervalRows d N))) :
    Module.Free k (ClosedGraphFaceHomology (k := k)
      (finiteRowFamily (UnitIntervalRows d N) E) α) :=
  (unitInterval_fine_homology_small (k := k) hE α).free

end FourPapers.Sublattice
end

#print axioms FourPapers.Sublattice.unitIntervalResidualHomologyEquiv
#print axioms FourPapers.Sublattice.unitInterval_fine_homology_free

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.FaceResidueGrading -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

/-- Exterior cardinality recorded modulo an arbitrary integer. This auxiliary
grading avoids truncated subtraction in shifted quotient complexes. -/
def faceResidueSpace (t : ℕ) (r : ZMod t) : Submodule k (Simplicial.Ambient V k) :=
  basisSpan Simplicial.basis (fun F => (F.card : ZMod t) = r)

def totalFaceResidueSpace (P : Finset V → Prop) (t : ℕ) (r : ZMod t) :
    Submodule k (TotalFaceModule (k := k) P) :=
  (faceResidueSpace t r).comap (TotalFaceModule (k := k) P).subtype

lemma totalFaceResidueSpace_eq (P : Finset V → Prop) (t : ℕ) (r : ZMod t) :
    totalFaceResidueSpace (k := k) P t r =
      basisSpan (totalFaceBasis P) (fun F => (F.val.card : ZMod t) = r) := by
  apply Submodule.map_injective_of_injective
    (Submodule.subtype_injective (TotalFaceModule (k := k) P))
  rw [totalFaceResidueSpace, Submodule.map_comap_eq, Submodule.range_subtype,
    basisSpan, Submodule.map_span]
  have hinter : faceResidueSpace (V := V) (k := k) t r ⊓ TotalFaceModule P =
      basisSpan Simplicial.basis (fun F => P F ∧ (F.card : ZMod t) = r) := by
    ext x
    simp only [Submodule.mem_inf, faceResidueSpace, TotalFaceModule, basisSpan,
      Module.Basis.mem_span_image]
    constructor
    · rintro ⟨h1, h2⟩ F hF
      exact ⟨h2 hF, h1 hF⟩
    · intro h
      exact ⟨fun F hF => (h hF).2, fun F hF => (h hF).1⟩
  rw [inf_comm, hinter]
  apply congrArg (Submodule.span k)
  ext x
  constructor
  · rintro ⟨F, ⟨hP, hF⟩, rfl⟩
    refine ⟨totalFaceBasis (k := k) P ⟨F, hP⟩, ⟨⟨F, hP⟩, hF, rfl⟩, ?_⟩
    exact totalFaceBasis_val P ⟨F, hP⟩
  · rintro ⟨y, ⟨F, hF, rfl⟩, rfl⟩
    exact ⟨F.val, ⟨F.property, hF⟩, (totalFaceBasis_val P F).symm⟩

lemma boundary_mem_faceResidueSpace (t : ℕ) (r : ZMod t)
    {x : Simplicial.Ambient V k} (hx : x ∈ faceResidueSpace t r) :
    Simplicial.boundary x ∈ faceResidueSpace t (r-1) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨F, hF, rfl⟩ := hy
    apply Submodule.span_mono (Set.image_mono (fun G hG => ?_))
      (boundary_mem_eraseSpan (k := k) F)
    obtain ⟨v, hv, rfl⟩ := hG
    have hpos : 1 ≤ F.card := Finset.card_pos.mpr ⟨v, hv⟩
    change (F.card : ZMod t) = r at hF
    change ((F.erase v).card : ZMod t) = r - 1
    simp only [Finset.card_erase_of_mem hv, Nat.cast_sub hpos, Nat.cast_one, hF]
  | zero => simpa using (faceResidueSpace (V := V) (k := k) t (r-1)).zero_mem
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

lemma quotientFaceProjection_residue (B : Family V) (α : Exponent V)
    (t : ℕ) (r : ZMod t) {x : Simplicial.Ambient V k}
    (hx : x ∈ faceResidueSpace t r) :
    quotientFaceProjection B α x ∈ faceResidueSpace t r := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨F, hF, rfl⟩ := hy
    rw [quotientFaceProjection, relativeProjection_basis]
    split_ifs
    · exact Submodule.subset_span ⟨F, hF, rfl⟩
    · exact Submodule.zero_mem _
  | zero => simpa using (faceResidueSpace (V := V) (k := k) t r).zero_mem
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

lemma signedBasisEquiv_symm_basis {I J R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (b : Module.Basis I R M) (c : Module.Basis J R N)
    (e : I ≃ J) (ε : I → ℤˣ) (j : J) :
    (signedBasisEquiv b c e ε).symm (c j) = (ε (e.symm j))⁻¹ • b (e.symm j) := by
  apply (signedBasisEquiv b c e ε).injective
  rw [LinearEquiv.apply_symm_apply, map_zsmul_unit, signedBasisEquiv_basis,
    e.apply_symm_apply, inv_smul_smul]

lemma fixedFaceIndexEquiv_card (S : V → Prop) (A : Finset V) (Q : Finset V → Prop)
    (hA : ∀ v ∈ A, S v) (hQ : ∀ G, Q G → ∀ v ∈ G, ¬S v)
    (G : {G // Q G}) :
    (fixedFaceIndexEquiv S A Q hA hQ G).val.card = A.card + G.val.card := by
  change (A ∪ G.val).card = _
  exact Finset.card_union_of_disjoint (Finset.disjoint_left.mpr
    (fun v hv hv' => hQ G.val G.property v hv' (hA v hv)))

/-- Removing a forced exterior face lowers the residue by its cardinality.
The proof uses the actual signed basis equivalence, so arbitrary orientations
of the finite variable set cause no additional assumption. -/
lemma fixedFaceFactorEquiv_symm_residue (S : V → Prop) (A : Finset V)
    (Q : Finset V → Prop) (hA : ∀ v ∈ A, S v) (hQ : ∀ G, Q G → ∀ v ∈ G, ¬S v)
    (t : ℕ) (r : ZMod t)
    (x : TotalFaceModule (k := k) (splitFacePredicate S (fun F => F=A) Q))
    (hx : x.val ∈ faceResidueSpace t r) :
    ((fixedFaceFactorEquiv S A Q hA hQ).symm x).val ∈
      faceResidueSpace t (r - A.card) := by
  have hx' : x ∈ basisSpan (totalFaceBasis (k := k)
      (splitFacePredicate S (fun F => F=A) Q))
      (fun F => (F.val.card : ZMod t) = r) := by
    rw [← totalFaceResidueSpace_eq]
    exact hx
  have hmap : basisSpan (totalFaceBasis (k := k)
      (splitFacePredicate S (fun F => F=A) Q))
      (fun F => (F.val.card : ZMod t) = r) ≤
      (totalFaceResidueSpace Q t (r-A.card)).comap
        (fixedFaceFactorEquiv S A Q hA hQ).symm.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro y ⟨F, hF, rfl⟩
    change ((fixedFaceFactorEquiv S A Q hA hQ).symm
      (totalFaceBasis _ F)).val ∈ faceResidueSpace t (r-A.card)
    rw [fixedFaceFactorEquiv, signedBasisEquiv_symm_basis, Submodule.coe_smul_of_tower,
      totalFaceBasis_val]
    let G := (fixedFaceIndexEquiv S A Q hA hQ).symm F
    have hc : (G.val.card : ZMod t) = r - A.card := by
      have hh := fixedFaceIndexEquiv_card S A Q hA hQ G
      rw [(fixedFaceIndexEquiv S A Q hA hQ).apply_symm_apply] at hh
      have hcast := congrArg (fun n : ℕ => (n : ZMod t)) hh
      rw [Nat.cast_add, hF] at hcast
      exact (eq_sub_iff_add_eq).mpr (by simpa only [add_comm] using hcast.symm)
    change (_ : ℤˣ) • Simplicial.basis G.val ∈ faceResidueSpace t (r-A.card)
    rw [Units.smul_def, ← Int.cast_smul_eq_zsmul k]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨G.val, hc, rfl⟩)
  exact hmap hx'

lemma faceResidueSpace_of_homogeneous (P : Finset V → Prop) (p t : ℕ)
    {x : Simplicial.Ambient V k} (hx : x ∈ Simplicial.Chains P p) :
    x ∈ faceResidueSpace t (p : ZMod t) :=
  Submodule.span_mono (Set.image_mono (fun F hF => congrArg (fun n : ℕ => (n : ZMod t)) hF.2)) hx

/-- Literal transport along equality of surviving faces; the underlying
exterior vector and its cardinality are unchanged. -/
def quotientFaceCast (B C : Family V) (α β : Exponent V)
    (h : quotientKoszulFaces B α = quotientKoszulFaces C β) :
    TotalFaceModule (k := k) (quotientKoszulFaces B α) ≃ₗ[k]
      TotalFaceModule (k := k) (quotientKoszulFaces C β) :=
  LinearEquiv.ofEq _ _ (by rw [h])

@[simp] lemma quotientFaceCast_val (B C : Family V) (α β : Exponent V)
    (h : quotientKoszulFaces B α = quotientKoszulFaces C β)
    (x : TotalFaceModule (k := k) (quotientKoszulFaces B α)) :
    (quotientFaceCast B C α β h x).val = x.val :=
  LinearEquiv.coe_ofEq_apply _ x

lemma quotientFaceCast_differential (B C : Family V) (α β : Exponent V)
    (h : quotientKoszulFaces B α = quotientKoszulFaces C β)
    (x : TotalFaceModule (k := k) (quotientKoszulFaces B α)) :
    quotientTotalDifferential C β (quotientFaceCast B C α β h x) =
      quotientFaceCast B C α β h (quotientTotalDifferential B α x) := by
  apply Subtype.ext
  simp only [quotientTotalDifferential_val, quotientFaceCast_val,
    quotientFaceProjection_eq_faceProjection, h]

lemma quotientFaceCast_boundary_iff (B C : Family V) (α β : Exponent V)
    (h : quotientKoszulFaces B α = quotientKoszulFaces C β)
    (x : TotalFaceModule (k := k) (quotientKoszulFaces B α)) :
    (∃ y, quotientTotalDifferential C β y = quotientFaceCast B C α β h x) ↔
      ∃ y, quotientTotalDifferential B α y = x := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨(quotientFaceCast B C α β h).symm y, ?_⟩
    apply (quotientFaceCast B C α β h).injective
    rw [← quotientFaceCast_differential, LinearEquiv.apply_symm_apply, hy]
  · rintro ⟨y, hy⟩
    exact ⟨quotientFaceCast B C α β h y, by rw [quotientFaceCast_differential, hy]⟩

end FourPapers.Sublattice
end

#print axioms FourPapers.Sublattice.fixedFaceFactorEquiv_symm_residue

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.UnitIntervalCongruence -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

lemma linearVariableQuotientFactor_symm_residue (L : Finset V) (B : Family V)
    (hB : ∀ b ∈ B, ∀ v, b v ≠ 0 → v ∉ L) (α : Exponent V)
    (hsq : ∀ v, α v ≤ 1) (t : ℕ) (r : ZMod t)
    (x : TotalFaceModule (k := k) (quotientKoszulFaces (variableMonomialFamily L ∪ B) α))
    (hx : x.val ∈ faceResidueSpace t r) :
    ((linearVariableQuotientFactor L B hB α hsq).symm x).val ∈
      faceResidueSpace t (r - (α.filter (fun v => v ∈ L)).support.card) := by
  unfold linearVariableQuotientFactor
  rw [LinearEquiv.trans_symm, LinearEquiv.trans_apply, LinearEquiv.ofEq_symm]
  apply fixedFaceFactorEquiv_symm_residue
  simpa only [LinearEquiv.coe_ofEq_apply] using hx

lemma linearVariableQuotientFactor_symm_cycle (L : Finset V) (B : Family V)
    (hB : ∀ b ∈ B, ∀ v, b v ≠ 0 → v ∉ L) (α : Exponent V)
    (hsq : ∀ v, α v ≤ 1)
    (x : TotalFaceModule (k := k) (quotientKoszulFaces (variableMonomialFamily L ∪ B) α))
    (hx : quotientTotalDifferential (variableMonomialFamily L ∪ B) α x = 0) :
    quotientTotalDifferential B (α.filter (fun v => v ∉ L))
      ((linearVariableQuotientFactor L B hB α hsq).symm x) = 0 := by
  let f := linearVariableQuotientFactor (k := k) L B hB α hsq
  have h := linearVariableQuotientFactor_differential L B hB α hsq (f.symm x)
  rw [show linearVariableQuotientFactor L B hB α hsq = f from rfl,
    f.apply_symm_apply, hx] at h
  have hu : IsUnit ((-1 : k) ^ (α.filter (fun v => v ∈ L)).support.card) :=
    (IsUnit.neg isUnit_one).pow _
  apply f.injective
  rw [map_zero]
  exact hu.smul_eq_zero.mp h.symm

lemma linearVariableQuotientFactor_boundary_of_symm (L : Finset V) (B : Family V)
    (hB : ∀ b ∈ B, ∀ v, b v ≠ 0 → v ∉ L) (α : Exponent V)
    (hsq : ∀ v, α v ≤ 1)
    (x : TotalFaceModule (k := k) (quotientKoszulFaces (variableMonomialFamily L ∪ B) α))
    (hx : ∃ y, quotientTotalDifferential B (α.filter (fun v => v ∉ L)) y =
      (linearVariableQuotientFactor L B hB α hsq).symm x) :
    ∃ y, quotientTotalDifferential (variableMonomialFamily L ∪ B) α y = x := by
  obtain ⟨y, hy⟩ := hx
  have h := linearVariableQuotientFactor_differential L B hB α hsq y
  rw [hy, LinearEquiv.apply_symm_apply] at h
  have hu : IsUnit ((-1 : k) ^ (α.filter (fun v => v ∈ L)).support.card) :=
    (IsUnit.neg isUnit_one).pow _
  have hm : ((-1 : k) ^ (α.filter (fun v => v ∈ L)).support.card) • x ∈
      LinearMap.range (quotientTotalDifferential (variableMonomialFamily L ∪ B) α) :=
    ⟨linearVariableQuotientFactor L B hB α hsq y, h⟩
  exact (Submodule.smul_mem_iff_of_isUnit _ hu).mp hm

variable {d N : ℕ}
variable {E : Finset ((Fin (d+1) → Fin N))}

lemma unitInterval_residual_degree_formula
    {α : Exponent (FiniteVariable.{u} (UnitIntervalRows d N))}
    {a : (Fin (d+1) → Fin N)} (hα : RowMaximum α a)
    (hsq : ∀ v, α v ≤ 1) :
    α.degree =
      (facetColonResidualDegree E a (α - finiteRowExponent (UnitIntervalRows d N) a)).degree +
      (facetColonLinearDegree E a (α - finiteRowExponent (UnitIntervalRows d N) a)).support.card + (d+1) := by
  let γ := α - finiteRowExponent (UnitIntervalRows d N) a
  have hγsq : ∀ v, γ v ≤ 1 := (unitInterval_rowMaximum_residual_squarefree hα hsq).1
  have hLsq : ∀ v, (facetColonLinearDegree E a γ) v ≤ 1 := by
    intro v
    by_cases hv : v ∈ facetLinearVariables E a <;>
      simp [facetColonLinearDegree, Finsupp.filter_apply, hv, hγsq v]
  have hL := congrArg Finsupp.degree
    (squarefreeExponent_eq_faceExponent_support (facetColonLinearDegree E a γ) hLsq)
  rw [degree_faceExponent] at hL
  have hsum := congrArg Finsupp.degree (facetColonDegree_add (E := E) a γ)
  simp only [map_add] at hsum
  have hrow := congrArg Finsupp.degree (tsub_add_cancel_of_le hα.1)
  simp only [map_add, finiteRowExponent_degree] at hrow
  change γ.degree + (d + 1) = α.degree at hrow
  change _ = (facetColonResidualDegree E a γ).degree +
    (facetColonLinearDegree E a γ).support.card + (d+1)
  omega

lemma unitInterval_residual_degree_residue
    {α : Exponent (FiniteVariable.{u} (UnitIntervalRows d N))}
    {a : (Fin (d+1) → Fin N)} (hα : RowMaximum α a)
    (hsq : ∀ v, α v ≤ 1) :
    ((facetColonResidualDegree E a (α - finiteRowExponent (UnitIntervalRows d N) a)).degree : ZMod d) =
      (α.degree : ZMod d) - 1 -
        (facetColonLinearDegree E a (α - finiteRowExponent (UnitIntervalRows d N) a)).support.card := by
  have h := congrArg (fun i : ℕ => (i : ZMod d)) (unitInterval_residual_degree_formula (E := E) hα hsq)
  simp only [Nat.cast_add, Nat.cast_one, ZMod.natCast_self, zero_add] at h
  linear_combination -h

/-- The residue grading proves the no-cancellation support statement of 6.1
at the level of actual cycles and actual boundaries, over every coefficient ring.
For `d+1` rows the permitted congruence is internal degree minus homological
degree divisible by `d`; no restriction to a field is used. -/
theorem unitInterval_residue_cycle_boundary (hE : UnitIntervalFacetFamily E)
    (α : Exponent (FiniteVariable.{u} (UnitIntervalRows d N))) (r : ZMod d)
    (z : TotalFaceModule (k := k) (quotientKoszulFaces (finiteRowFamily (UnitIntervalRows d N) E) α))
    (hzr : z.val ∈ faceResidueSpace d r)
    (hz : quotientTotalDifferential (finiteRowFamily (UnitIntervalRows d N) E) α z = 0)
    (hr : r ≠ (α.degree : ZMod d)) :
    ∃ y, quotientTotalDifferential (finiteRowFamily (UnitIntervalRows d N) E) α y = z := by
  have hall : ∀ m : ℕ, ∀ β : Exponent (FiniteVariable.{u} (UnitIntervalRows d N)), β.degree = m →
      ∀ s : ZMod d, ∀ x : TotalFaceModule (k := k)
        (quotientKoszulFaces (finiteRowFamily (UnitIntervalRows d N) E) β),
      x.val ∈ faceResidueSpace d s →
      quotientTotalDifferential (finiteRowFamily (UnitIntervalRows d N) E) β x = 0 →
      s ≠ (β.degree : ZMod d) →
      ∃ y, quotientTotalDifferential (finiteRowFamily (UnitIntervalRows d N) E) β y = x := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro β hdegree s x hxs hx hs
      let B := finiteRowFamily (UnitIntervalRows d N) E
      by_cases hzero : β = 0
      · subst β
        have hn : ¬Contains B 0 := by
          rintro ⟨b, hb, hb0⟩
          obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
          have hh := hb0 ⟨0, ULift.up (a 0)⟩
          simp [finiteRowExponent_apply] at hh
        have hxs0 : x.val ∈ faceResidueSpace d (0 : ZMod d) := by
          apply Submodule.span_mono (Set.image_mono (fun F hF => ?_)) x.property
          have hF0 := (quotientKoszulFaces_zero_iff B hn F).mp hF
          simp [hF0]
        have h1 := Grading.projection_eq_self
          (show x.val ∈ Grading.Piece Simplicial.basis (fun F => (F.card : ZMod d)) s from hxs)
        have h0 := Grading.projection_eq_zero (by simpa using hs)
          (show x.val ∈ Grading.Piece Simplicial.basis (fun F => (F.card : ZMod d)) 0 from hxs0)
        have hx0 : x.val = 0 := h1.symm.trans h0
        exact ⟨0, by apply Subtype.ext; simpa only [map_zero, ZeroMemClass.coe_zero] using hx0.symm⟩
      obtain ⟨e, he⟩ : ∃ e, 0 < β e := by
        by_contra h
        push_neg at h
        apply hzero
        ext v
        exact Nat.eq_zero_of_le_zero (h v)
      by_cases hsq : ∀ v, β v ≤ 1
      · by_cases hcontains : Contains B β
        · obtain ⟨b, hb, hbβ⟩ := hcontains
          obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hb
          obtain ⟨a, ha⟩ := rowMaximum_exists_of_generator β hbβ
          by_cases haE : a ∈ E
          · letI : DecidableEq (FiniteVariable.{u} (UnitIntervalRows d N)) :=
              (inferInstance : LinearOrder (FiniteVariable.{u} (UnitIntervalRows d N))).toDecidableEq
            let γ := β - finiteRowExponent (UnitIntervalRows d N) a
            let L := facetLinearVariables E a
            let δ := γ.filter (fun v => v ∉ L)
            have hδ : δ = facetColonResidualDegree E a γ := by
              dsimp only [δ, L]
              ext v
              by_cases hv : v ∈ facetLinearVariables E a <;>
                simp only [facetColonResidualDegree, Finsupp.filter_apply, hv,
                  not_true_eq_false, not_false_eq_true, ite_false, ite_true]
            have hL : γ.filter (fun v => v ∈ L) = facetColonLinearDegree E a γ := by
              dsimp only [L]
              ext v
              by_cases hv : v ∈ facetLinearVariables E a <;>
                simp only [facetColonLinearDegree, Finsupp.filter_apply, hv, ite_false, ite_true]
            let C := finitePredecessorFamily (UnitIntervalRows d N) E a
            let D := finiteRowFamily (UnitIntervalRows d N) (facetResidualFacets E a)
            have hγsq := (unitInterval_rowMaximum_residual_squarefree ha hsq).1
            have hfaces : quotientKoszulFaces C γ = quotientKoszulFaces (variableMonomialFamily L ∪ D) γ := by
              have hfamily : facetColonFamily E a = variableMonomialFamily L ∪ D := by
                dsimp only [L, D]
                ext b
                simp only [facetColonFamily, variableMonomialFamily, Finset.mem_union,
                  Finset.mem_image]
              exact (unitIntervalPredecessor_faces hE haE γ).trans
                (congrArg (fun H => quotientKoszulFaces H γ) hfamily)
            let q := quotientConnectingProjection B C β γ x
            have hqcycle : quotientTotalDifferential C γ q = 0 :=
              firstPowerConnecting_cycle hE.latticeClosed (a := ⟨a, haE⟩) ha x hx
            have hqr : q.val ∈ faceResidueSpace d (s-1) :=
              quotientFaceProjection_residue C γ d (s-1) (boundary_mem_faceResidueSpace d s hxs)
            let q' := quotientFaceCast C (variableMonomialFamily L ∪ D) γ γ hfaces q
            have hq'cycle : quotientTotalDifferential (variableMonomialFamily L ∪ D) γ q' = 0 := by
              rw [show q' = quotientFaceCast C (variableMonomialFamily L ∪ D) γ γ hfaces q from rfl,
                quotientFaceCast_differential, hqcycle, map_zero]
            let f := linearVariableQuotientFactor (k := k) L D (facetResidualFamily_disjoint hE a) γ hγsq
            let y := f.symm q'
            have hycycle : quotientTotalDifferential D δ y = 0 :=
              linearVariableQuotientFactor_symm_cycle L D (facetResidualFamily_disjoint hE a) γ hγsq q' hq'cycle
            have hyr : y.val ∈ faceResidueSpace d (s-1-(facetColonLinearDegree E a γ).support.card) := by
              simpa only [hL] using
                linearVariableQuotientFactor_symm_residue L D (facetResidualFamily_disjoint hE a) γ hγsq
                  d (s-1) q' (by simpa only [q', quotientFaceCast_val] using hqr)
            have hres : quotientKoszulFaces D δ = quotientKoszulFaces B δ := by
              rw [hδ]
              exact facetColonResidual_quotientFaces a γ
                (unitInterval_rowMaximum_residual_squarefree ha hsq).2.1
                (unitInterval_rowMaximum_residual_squarefree ha hsq).2.2
            let y' := quotientFaceCast D B δ δ hres y
            have hy'cycle : quotientTotalDifferential B δ y' = 0 := by
              rw [show y' = quotientFaceCast D B δ δ hres y from rfl,
                quotientFaceCast_differential, hycycle, map_zero]
            have hy'r : y'.val ∈ faceResidueSpace d (s-1-(facetColonLinearDegree E a γ).support.card) := by
              simpa only [y', quotientFaceCast_val] using hyr
            have hsmall : δ.degree < m := by
              rw [hδ, ← hdegree]
              exact facetColonResidualDegree_lt ha
            have hne : s-1-(facetColonLinearDegree E a γ).support.card ≠ (δ.degree : ZMod d) := by
              rw [hδ, unitInterval_residual_degree_residue (E := E) ha hsq]
              intro hh
              exact hs (sub_left_inj.mp (sub_left_inj.mp hh))
            have hyfill := ih δ.degree hsmall δ rfl _ y' hy'r hy'cycle hne
            have hfillD : ∃ v, quotientTotalDifferential D δ v = y :=
              (quotientFaceCast_boundary_iff D B δ δ hres y).mp hyfill
            have hfillLD := linearVariableQuotientFactor_boundary_of_symm L D
              (facetResidualFamily_disjoint hE a) γ hγsq q' hfillD
            have hfillC := (quotientFaceCast_boundary_iff C (variableMonomialFamily L ∪ D)
              γ γ hfaces q).mp hfillLD
            exact firstPowerConnecting_detects_boundaries hE.latticeClosed (a := ⟨a, haE⟩)
              ha e he x hx hfillC
          · exact firstPowerQuotientCycle_boundary_of_missing_maximum hE.latticeClosed ha haE e he x hx
        · exact quotientCycle_boundary_of_not_contains B β hcontains e he x hx
      · push_neg at hsq
        obtain ⟨v, hv⟩ := hsq
        apply quotient_cycle_boundary_of_two_le (e := v) _ (by omega) x hx
        intro c hc
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
        rcases v with ⟨r, ⟨j⟩⟩
        simp only [finiteRowExponent_apply]
        split_ifs <;> omega
  exact hall α.degree α rfl r z hzr hz hr

theorem unitInterval_homogeneous_cycle_boundary (hE : UnitIntervalFacetFamily E)
    (α : Exponent (FiniteVariable.{u} (UnitIntervalRows d N))) (p : ℕ)
    (z : TotalFaceModule (k := k) (quotientKoszulFaces (finiteRowFamily (UnitIntervalRows d N) E) α))
    (hzp : z ∈ totalFacePiece (quotientKoszulFaces (finiteRowFamily (UnitIntervalRows d N) E) α) p)
    (hz : quotientTotalDifferential (finiteRowFamily (UnitIntervalRows d N) E) α z = 0)
    (hp : (p : ZMod d) ≠ (α.degree : ZMod d)) :
    ∃ y, quotientTotalDifferential (finiteRowFamily (UnitIntervalRows d N) E) α y = z :=
  unitInterval_residue_cycle_boundary hE α (p : ZMod d) z
    (faceResidueSpace_of_homogeneous _ p d hzp) hz hp

end FourPapers.Sublattice
end

#print axioms FourPapers.Sublattice.unitInterval_residue_cycle_boundary

end
end


end
