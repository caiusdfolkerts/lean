module
public import applications_verification
public import schur_theory
public import rank_stratum_verification
public import corollary_seven_two
public import supplementary_verification

-- Generated verification output directories.
run_cmd Lean.Elab.Command.liftIO do
  IO.FS.createDirAll ".lake/reports/audit"


/-!
# Complete mathematical statement and trust gate

The examples below are deliberately closed: every matrix size, coefficient
ring, field, partition family, and base-change morphism is quantified explicitly.
They compare the paper's mathematical objects with the proved endpoints.
The final read-only command audits the transitive axioms of the principal core
and all extensions; it never inserts declarations into the environment.
-/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open scoped BigOperators
universe u

example (n : ℕ) (K : Type u) [Field K] (t s : ℕ)
    (ht : 1 ≤ t) (htn : t ≤ n) (hs : 1 ≤ s) :
    FourPapers.Symmetric.Schur.quotientHilbertSeries n K
        (FourPapers.Symmetric.symbolicPower
          (FourPapers.Symmetric.determinantalIdeal n K t) s) =
      FourPapers.Symmetric.Schur.schurHilbertSeries n t s :=
  FourPapers.Symmetric.Schur.corollary_5_3_schur_hilbert_series
    n K t s ht htn hs

example (n : ℕ) (K : Type u) [Field K] (q : ℕ) :
    FourPapers.Symmetric.Schur.quotientHilbertSeries n K
        (FourPapers.Symmetric.determinantalIdeal n K (q + 1)) =
      FourPapers.Symmetric.Schur.rankSchurSeries n q :=
  FourPapers.Symmetric.Schur.corollary_5_3_rank_schur_hilbert_series n K q

-- Expanding both the actual quotient piece and the partition condition makes
-- the mathematical strength visible without relying on the names of the
-- formal-series definitions.
example (n : ℕ) (K : Type u) [Field K] (t s : ℕ)
    (ht : 1 ≤ t) (htn : t ≤ n) (hs : 1 ≤ s) (d : Fin n →₀ ℕ) :
    Module.finrank K
      (FourPapers.Symmetric.Pivot.quotientPiece
        (FourPapers.Symmetric.symbolicPower
          (FourPapers.Symmetric.determinantalIdeal n K t) s)
        FourPapers.Symmetric.endpointWeight d) =
      ∑ᶠ μ : YoungDiagram,
        if μ.rowLens.length ≤ n ∧ (μ.rowLens.drop (t - 1)).sum < s then
          (FourPapers.Symmetric.Schur.schurPolynomial n
            (FourPapers.Symmetric.Schur.doubleShape μ)).coeff d
        else 0 := by
  exact FourPapers.Symmetric.Schur.corollary_5_3_schur_hilbert_coefficient
    n K t s ht htn hs d

#print axioms FourPapers.Symmetric.Schur.corollary_5_3_schur_hilbert_series
#print axioms FourPapers.Symmetric.Schur.corollary_5_3_rank_schur_hilbert_series

-- Explicit parentheses ensure that truncation is applied separately to each
-- minor size, exactly as in the paper's gamma score.
example (n : ℕ)
    (T : FourPapers.Symmetric.Schur.EvenSemistandardTableaux n)
    (t : ℕ) (ht : 1 ≤ t) :
    (∑ j : Fin (FourPapers.Symmetric.Schur.columnPairCount T),
      ((FourPapers.Symmetric.Schur.bitableauMinor T j).size + 1 - t)) =
      ((FourPapers.Symmetric.Schur.tableauHalfShape T).rowLens.drop (t - 1)).sum :=
  FourPapers.Symmetric.Schur.bitableau_minor_score T t ht

noncomputable section
namespace FourPapers.Symmetric.Strata.CompleteGeometryStatements
open CategoryTheory AlgebraicGeometry

example {n : ℕ} (w : SymmetricRook n) (R : Type u) [CommRing R] :
    Spec (CommRingCat.of (AffineTorus.CoordinateRing R w.a w.b)) ≅
      rankStratumScheme w.val.rankProfile R :=
  w.openSchemeIso R

example {n : ℕ} (w : SymmetricRook n) (R : Type u) [CommRing R] :
    ((w.openSchemeIso R).hom ≫ rankStratumImmersion w.val.rankProfile R) ≫
        Spec.map (CommRingCat.ofHom (rankLocusCoefficientMap w.val.rankProfile R)) =
      Spec.map (CommRingCat.ofHom
        (algebraMap R (AffineTorus.CoordinateRing R w.a w.b))) :=
  w.openSchemeIso_over R

example {n : ℕ} (w : SymmetricRook n) (R : Type u) [CommRing R]
    (T : Scheme.{u}) (f : T ⟶ Spec (CommRingCat.of R)) :
    Limits.pullback (AffineTorus.structureMap R w.a w.b) f ≅
      Limits.pullback
        (rankStratumImmersion w.val.rankProfile R ≫ w.locusStructureMap R) f :=
  w.openSchemeIso_after_baseChange R f

example {n : ℕ} (w : SymmetricRook n) (F : Type u) [Field F] :
    Dense (rankStratumOpen w.val.rankProfile F) ∧
      ringKrullDim (RankLocusRing w.val.rankProfile F) = w.a + w.b ∧
      Scheme.IsRationalOver (w.locusStructureMap F) ∧
      ∃ U : (rankLocusScheme w.val.rankProfile F).Opens,
        Dense (U : Set (rankLocusScheme w.val.rankProfile F)) ∧
          Smooth (U.ι ≫ w.locusStructureMap F) :=
  proposition_6_5_geometry w F

example {n : ℕ} (w : SymmetricRook n) (F : Type u) [Field F] :
    Scheme.BirationalOver (w.locusStructureMap F)
      (𝔸(AffineTorus.AffineIndices w.a w.b; Spec (CommRingCat.of F)) ↘
        Spec (CommRingCat.of F)) :=
  w.locus_birational_affineSpace F

example {n : ℕ} (w : SymmetricRook n) (R : Type u) [CommRing R] :
    Smooth (rankStratumImmersion w.val.rankProfile R ≫ w.locusStructureMap R) :=
  w.stratumStructureMap_smooth R

example {n : ℕ} (w : SymmetricRook n) (F : Type u) [Field F] [Fintype F] :
    Nat.card (RankLocusPoints w.val.rankProfile F) =
      ∑ v : BoundedRooks w.val.rankProfile,
        Nat.card F ^ v.val.a * (Nat.card F - 1) ^ v.val.b :=
  proposition_6_5_point_count w F

example {n : ℕ} (r : RankArray n) (F : Type u) [Field F] :
    RankLocusRationalPoints r F ≃ RankLocusPoints r F :=
  rankLocusRationalPointEquiv r

example {n : ℕ} (w : SymmetricRook n) (F : Type u) [Field F] [Fintype F] :
    Nat.card (RankLocusRationalPoints w.val.rankProfile F) =
      ∑ v : BoundedRooks w.val.rankProfile,
        Nat.card F ^ v.val.a * (Nat.card F - 1) ^ v.val.b :=
  proposition_6_5_scheme_point_count (F := F) w

/-- Scheme dimension is the dimension of the actual rank-bounded locus. -/
example {n : ℕ} (w : SymmetricRook n) (F : Type u) [Field F] :
    topologicalKrullDim (rankLocusScheme w.val.rankProfile F) = w.a + w.b := by
  exact (w.locus_dimension_eq_stratum F).trans (w.stratum_dimension F)

end FourPapers.Symmetric.Strata.CompleteGeometryStatements
end


/-
Independent closed statement checks for the complete verification gate.
The gate imports CorollarySevenTwo before this file's body.  Each example
spells out its parameters and the original mathematical objects.
-/

section CorollarySevenTwoClosedStatements
open FourPapers.Symmetric MvPolynomial
open scoped BigOperators Pointwise

/-- Literal partition hypothesis, real convex hull, and positive orthant. -/
example (n : ℕ) (K : Type*) [Field K]
    (shapes : Finset (List ℕ)) (hshapes : shapes.Nonempty)
    (hdecreasing : ∀ σ ∈ shapes, σ.SortedGE)
    (hpositive : ∀ σ ∈ shapes, ∀ a ∈ σ, 1 ≤ a)
    (hfirst : ∀ σ ∈ shapes, σ.headD 0 ≤ n)
    (m : Entry n →₀ ℕ) :
    monomial m (1 : K) ∈ initialIdeal K
        (CommAlg.idealIntegralClosure
          (∑ σ ∈ shapes, (σ.map (determinantalIdeal n K)).prod)) ↔
      (fun j : Fin n => (gamma (j.val + 1) m : ℝ)) ∈
        convexHull ℝ (Set.range (fun σ : shapes => fun j : Fin n =>
          ((σ.val.map (fun a => a + 1 - (j.val + 1))).sum : ℝ))) +
          {z : Fin n → ℝ | 0 ≤ z} := by
  simpa only [IntegralClosure.shapePolytope, DeterminantalTransfer.gamma] using
    IntegralClosure.corollary_7_2_first_part K shapes hshapes hdecreasing hpositive hfirst m

/-- Actual integral closure equals the sum indexed by all real polytope points. -/
example (n : ℕ) (K : Type*) [Field K]
    (shapes : Finset (List ℕ)) (hshapes : shapes.Nonempty)
    (hdecreasing : ∀ σ ∈ shapes, σ.SortedGE)
    (hfirst : ∀ σ ∈ shapes, σ.headD 0 ≤ n) :
    CommAlg.idealIntegralClosure
        (∑ σ ∈ shapes, (σ.map (determinantalIdeal n K)).prod) =
      ⨆ a ∈ convexHull ℝ (Set.range (fun σ : shapes => fun j : Fin n =>
          ((σ.val.map (fun b => b + 1 - (j.val + 1))).sum : ℝ))),
        ⨅ j : Fin n, symbolicPower (determinantalIdeal n K (j.val + 1))
          (Nat.ceil (a j)) := by
  letI : Nonempty shapes := by
    obtain ⟨σ, hσ⟩ := hshapes
    exact ⟨⟨σ, hσ⟩⟩
  rw [IntegralClosure.partition_sum_eq_shapeSum]
  simpa only [IntegralClosure.shapePolytope, DeterminantalTransfer.gamma] using
    IntegralClosure.corollary_7_2_symbolic_formula K (fun σ : shapes => σ.val)
      (fun σ a ha =>
        (IntegralClosure.partition_parts_le_iff_head σ.val
          (hdecreasing σ.val σ.property) n).mpr (hfirst σ.val σ.property) a ha)

/-- The same integer model gives the actual closure over every field. -/
example (n : ℕ) (K : Type*) [Field K]
    (α : Type*) [Fintype α] [Nonempty α]
    (sizes : α → List ℕ) (hsizes : ∀ i a, a ∈ sizes i → a ≤ n) :
    (BoundedLattice.ideal (IntegralClosure.closureExpression (n := n) sizes)).map
        (MvPolynomial.map (Int.castRingHom K)) =
      CommAlg.idealIntegralClosure
        (⨆ i, ((sizes i).map (determinantalIdeal n K)).prod) :=
  IntegralClosure.corollary_7_2_integral_model K sizes hsizes

/-- No field or characteristic assumption enters the coefficient-change quotient. -/
example (n : ℕ) (R : Type*) [CommRing R]
    (α : Type*) [Fintype α] (sizes : α → List ℕ) :
    Module.Free R (CoordinateRing n R ⧸
      (BoundedLattice.ideal (IntegralClosure.closureExpression (n := n) sizes)).map
        (MvPolynomial.map (Int.castRingHom R))) :=
  IntegralClosure.corollary_7_2_model_free R sizes

/-- A single homogeneous triangular integer basis adapts to every expression. -/
example (n : ℕ) :
    ∃ b : Module.Basis (Entry n →₀ ℕ) ℤ (CoordinateRing n ℤ),
      (∀ m, (b m).coeff m = 1 ∧
        (b m).IsWeightedHomogeneous (fun _ : Entry n => (1 : ℕ))
          (Finsupp.weight (fun _ : Entry n => (1 : ℕ)) m) ∧
        (foldedOrder n).toSyn ((foldedOrder n).degree (b m)) ≤
          (foldedOrder n).toSyn m) ∧
      ∀ e : BoundedLattice.Expr n,
        (BoundedLattice.ideal e).restrictScalars ℤ =
          Submodule.span ℤ (b '' BoundedLattice.monomials e) :=
  BoundedLattice.exists_integral_simultaneous_basis n

/-- Every coefficient specialization of the simultaneous family is free and flat. -/
example (n : ℕ) (R : Type*) [CommRing R]
    (φ : Polynomial ℤ →+* R) (e : BoundedLattice.Expr n) :
    Module.Free R (CoordinateRing n R ⧸
        (BoundedLattice.deformation e).map (MvPolynomial.map φ)) ∧
      Module.Flat R (CoordinateRing n R ⧸
        (BoundedLattice.deformation e).map (MvPolynomial.map φ)) :=
  ⟨BoundedLattice.deformation_free R φ e, BoundedLattice.deformation_flat R φ e⟩

/-- Its actual fibers are the integer ideal and its folded-order initial ideal. -/
example (n : ℕ) (e : BoundedLattice.Expr n) :
    (BoundedLattice.deformation e).map (Deformation.specialization 1) =
        BoundedLattice.ideal e ∧
      (BoundedLattice.deformation e).map (Deformation.specialization 0) =
        Simultaneous.orderInitialIdeal (foldedOrder n) (BoundedLattice.ideal e) :=
  ⟨BoundedLattice.deformation_at_one e, BoundedLattice.deformation_at_zero e⟩

/-- Actual northwest ideals and actual integral closures have compatible initials. -/
example (n : ℕ) (K : Type*) [Field K]
    (r : RankArray n) (hr : ∀ i j, r i j = r j i)
    (α : Type*) [Fintype α] [Nonempty α]
    (sizes : α → List ℕ) (hsizes : ∀ i a, a ∈ sizes i → a ≤ n) :
    initialIdeal K (northwestIdeal K r ⊓
        CommAlg.idealIntegralClosure
          (⨆ i, ((sizes i).map (determinantalIdeal n K)).prod)) =
      initialIdeal K (northwestIdeal K r) ⊓
        initialIdeal K (CommAlg.idealIntegralClosure
          (⨆ i, ((sizes i).map (determinantalIdeal n K)).prod)) := by
  simpa only [BoundedLattice.fieldIdeal_northwest,
    IntegralClosure.closureExpression_field K sizes hsizes,
    IntegralClosure.shapeSumIdeal, IntegralClosure.shapeProductIdeal] using
    BoundedLattice.initial_inf K (BoundedLattice.northwest r hr)
      (IntegralClosure.closureExpression sizes)

example (n : ℕ) (K : Type*) [Field K]
    (r : RankArray n) (hr : ∀ i j, r i j = r j i)
    (α : Type*) [Fintype α] [Nonempty α]
    (sizes : α → List ℕ) (hsizes : ∀ i a, a ∈ sizes i → a ≤ n) :
    initialIdeal K (northwestIdeal K r ⊔
        CommAlg.idealIntegralClosure
          (⨆ i, ((sizes i).map (determinantalIdeal n K)).prod)) =
      initialIdeal K (northwestIdeal K r) ⊔
        initialIdeal K (CommAlg.idealIntegralClosure
          (⨆ i, ((sizes i).map (determinantalIdeal n K)).prod)) := by
  simpa only [BoundedLattice.fieldIdeal_northwest,
    IntegralClosure.closureExpression_field K sizes hsizes,
    IntegralClosure.shapeSumIdeal, IntegralClosure.shapeProductIdeal] using
    BoundedLattice.initial_sup K (BoundedLattice.northwest r hr)
      (IntegralClosure.closureExpression sizes)

/-- Arbitrary coefficient change commutes with mixed intersections and sums. -/
example (n : ℕ) (R : Type*) [CommRing R]
    (r : RankArray n) (hr : ∀ i j, r i j = r j i)
    (α : Type*) [Fintype α] (sizes : α → List ℕ) :
    let A := BoundedLattice.ideal (BoundedLattice.northwest r hr)
    let B := BoundedLattice.ideal (IntegralClosure.closureExpression (n := n) sizes)
    let φ := MvPolynomial.map (Int.castRingHom R)
    (A ⊓ B).map φ = A.map φ ⊓ B.map φ ∧
      (A ⊔ B).map φ = A.map φ ⊔ B.map φ :=
  ⟨BoundedLattice.coefficient_change_inf R (BoundedLattice.northwest r hr)
      (IntegralClosure.closureExpression sizes),
    BoundedLattice.coefficient_change_sup R (BoundedLattice.northwest r hr)
      (IntegralClosure.closureExpression sizes)⟩

/-- Intersections in the same family commute with every base change in the parameter. -/
example (n : ℕ) (R : Type*) [CommRing R]
    (φ : Polynomial ℤ →+* R) (e f : BoundedLattice.Expr n) :
    (BoundedLattice.deformation e ⊓ BoundedLattice.deformation f).map
        (MvPolynomial.map φ) =
      (BoundedLattice.deformation e).map (MvPolynomial.map φ) ⊓
        (BoundedLattice.deformation f).map (MvPolynomial.map φ) :=
  BoundedLattice.deformation_map_inf R φ e f

/-- Actual unit fibers over a field are variable rescalings of the full integral closure. -/
example (n : ℕ) (K : Type*) [Field K]
    (α : Type*) [Fintype α] [Nonempty α]
    (sizes : α → List ℕ) (hsizes : ∀ i a, a ∈ sizes i → a ≤ n)
    (φ : Polynomial ℤ →+* K) (x : Kˣ) (hx : φ Polynomial.X = (x : K)) :
    (BoundedLattice.deformation (IntegralClosure.closureExpression (n := n) sizes)).map
        (MvPolynomial.map φ) =
      (CommAlg.idealIntegralClosure
        (⨆ i, ((sizes i).map (determinantalIdeal n K)).prod)).map
          (Deformation.variableScaling
            (fun i : Entry n => x ^ ((i.val.1.val + 1) * (i.val.2.val + 1)))).toRingHom :=
  IntegralClosure.corollary_7_2_deformation_unit_field K φ x hx sizes hsizes

/-- The unit-fiber formula itself is valid over every commutative ring. -/
example (n : ℕ) (R : Type*) [CommRing R]
    (φ : Polynomial ℤ →+* R) (x : Rˣ) (hx : φ Polynomial.X = (x : R))
    (e : BoundedLattice.Expr n) :
    (BoundedLattice.deformation e).map (MvPolynomial.map φ) =
      (BoundedLattice.baseChangedIdeal R e).map
        (Deformation.variableScaling
          (fun i : Entry n => x ^ ((i.val.1.val + 1) * (i.val.2.val + 1)))).toRingHom :=
  BoundedLattice.deformation_map_unit φ x hx e

/-- Every arbitrary coefficient homomorphism preserves the model and mixed intersections. -/
example (n : ℕ) (A B : Type*) [CommRing A] [CommRing B]
    (φ : A →+* B) (e f : BoundedLattice.Expr n) :
    (BoundedLattice.baseChangedIdeal A e).map (MvPolynomial.map φ) =
        BoundedLattice.baseChangedIdeal B e ∧
      (BoundedLattice.baseChangedIdeal A e ⊓ BoundedLattice.baseChangedIdeal A f).map
          (MvPolynomial.map φ) =
        (BoundedLattice.baseChangedIdeal A e).map (MvPolynomial.map φ) ⊓
          (BoundedLattice.baseChangedIdeal A f).map (MvPolynomial.map φ) :=
  ⟨BoundedLattice.baseChangedIdeal_map φ e, BoundedLattice.baseChangedIdeal_map_inf φ e f⟩

/-- The basis elements in every fiber are the same literal monomial residue classes. -/
example (n : ℕ) (R : Type*) [CommRing R]
    (φ : Polynomial ℤ →+* R) (e : BoundedLattice.Expr n) :
    let I := (BoundedLattice.deformation e).map (MvPolynomial.map φ)
    let v : (foldedOrder n).standardMonomials (BoundedLattice.ideal e) →
        CoordinateRing n R ⧸ I := fun a => Ideal.Quotient.mk I (monomial a.val 1)
    LinearIndependent R v ∧ Submodule.span R (Set.range v) = ⊤ :=
  BoundedLattice.deformation_standard_basis R φ e

/-- The extended compatible lattice is distributive after every coefficient change. -/
example (n : ℕ) (R : Type*) [CommRing R] (e f g : BoundedLattice.Expr n) :
    BoundedLattice.baseChangedIdeal R e ⊓
        (BoundedLattice.baseChangedIdeal R f ⊔ BoundedLattice.baseChangedIdeal R g) =
      (BoundedLattice.baseChangedIdeal R e ⊓ BoundedLattice.baseChangedIdeal R f) ⊔
        (BoundedLattice.baseChangedIdeal R e ⊓ BoundedLattice.baseChangedIdeal R g) :=
  BoundedLattice.baseChanged_distributive R e f g

/-- Sums commute with arbitrary coefficient homomorphisms as well. -/
example (n : ℕ) (A B : Type*) [CommRing A] [CommRing B]
    (φ : A →+* B) (e f : BoundedLattice.Expr n) :
    (BoundedLattice.baseChangedIdeal A e ⊔ BoundedLattice.baseChangedIdeal A f).map
        (MvPolynomial.map φ) =
      (BoundedLattice.baseChangedIdeal A e).map (MvPolynomial.map φ) ⊔
        (BoundedLattice.baseChangedIdeal A f).map (MvPolynomial.map φ) :=
  BoundedLattice.baseChangedIdeal_map_sup φ e f

/-- Finite sums in the same family commute with every parameter specialization. -/
example (n : ℕ) (R : Type*) [CommRing R]
    (φ : Polynomial ℤ →+* R) (e f : BoundedLattice.Expr n) :
    (BoundedLattice.deformation e ⊔ BoundedLattice.deformation f).map
        (MvPolynomial.map φ) =
      (BoundedLattice.deformation e).map (MvPolynomial.map φ) ⊔
        (BoundedLattice.deformation f).map (MvPolynomial.map φ) :=
  BoundedLattice.deformation_map_sup R φ e f

/-- The integer models have literal standard-monomial quotient bases over every ring. -/
example (n : ℕ) (R : Type*) [CommRing R] (e : BoundedLattice.Expr n) :
    let v : (foldedOrder n).standardMonomials (BoundedLattice.ideal e) →
        CoordinateRing n R ⧸ BoundedLattice.baseChangedIdeal R e :=
      fun a => Ideal.Quotient.mk _ (monomial a.val 1)
    LinearIndependent R v ∧ Submodule.span R (Set.range v) = ⊤ :=
  BoundedLattice.standard_monomial_basis R e

/-- Initial ideals of the integral models preserve sums over arbitrary rings. -/
example (n : ℕ) (R : Type*) [CommRing R] (e f : BoundedLattice.Expr n) :
    Simultaneous.orderInitialIdeal (foldedOrder n)
        (BoundedLattice.baseChangedIdeal R e ⊔ BoundedLattice.baseChangedIdeal R f) =
      Simultaneous.orderInitialIdeal (foldedOrder n) (BoundedLattice.baseChangedIdeal R e) ⊔
        Simultaneous.orderInitialIdeal (foldedOrder n) (BoundedLattice.baseChangedIdeal R f) := by
  exact BoundedLattice.initial_sup_after_baseChange R e f

/-- The same statement holds for actual intersections, without flatness assumptions. -/
example (n : ℕ) (R : Type*) [CommRing R] (e f : BoundedLattice.Expr n) :
    Simultaneous.orderInitialIdeal (foldedOrder n)
        (BoundedLattice.baseChangedIdeal R e ⊓ BoundedLattice.baseChangedIdeal R f) =
      Simultaneous.orderInitialIdeal (foldedOrder n) (BoundedLattice.baseChangedIdeal R e) ⊓
        Simultaneous.orderInitialIdeal (foldedOrder n) (BoundedLattice.baseChangedIdeal R f) := by
  exact BoundedLattice.initial_inf_after_baseChange R e f

end CorollarySevenTwoClosedStatements


/- Independent closed types for the remark following Corollary 6.1. -/
section OtherAntidiagonalOrdersClosedStatements
open FourPapers.Symmetric MvPolynomial
open scoped BigOperators

example (n : ℕ) (K : Type*) [Field K]
    (r : RankArray n) (hr : ∀ i j, r i j = r j i)
    (conditions : List (ℕ × ℕ))
    (hc : ∀ ts ∈ conditions, 1 ≤ ts.1 ∧ ts.1 ≤ n ∧ 1 ≤ ts.2)
    (ω : MonomialOrder (Entry n))
    (hω : ∀ δ : MinorData n, ω.degree (δ.polynomial K) = δ.exponent) :
    ω.IsGroebnerBasis (mixedGenerators K r conditions) (mixedIdeal K r conditions) ∧
      Ideal.span (ω.leadingTerm '' (mixedIdeal K r conditions : Set (CoordinateRing n K))) =
        northwestAntidiagonalIdeal K r ⊔
          ∑ ts ∈ conditions.toFinset, symbolicAntidiagonalIdeal K n ts.1 ts.2 :=
  ⟨OrderTransfer.mixed_field_groebner n K r hr conditions hc ω hω,
    OrderTransfer.mixed_field_initial n K r hr conditions hc ω hω⟩

example (n : ℕ) (R : Type*) [CommRing R]
    (r : RankArray n) (hr : ∀ i j, r i j = r j i)
    (conditions : List (ℕ × ℕ))
    (hc : ∀ ts ∈ conditions, 1 ≤ ts.1 ∧ ts.1 ≤ n ∧ 1 ≤ ts.2)
    (ω : MonomialOrder (Entry n))
    (hω : ∀ δ : MinorData n, ω.degree (δ.polynomial ℤ) = δ.exponent) :
    ω.IsGroebnerBasis (mixedGenerators R r conditions) (integralMixedIdeal R r conditions) ∧
      Ideal.span (ω.leadingTerm ''
        (integralMixedIdeal R r conditions : Set (CoordinateRing n R))) =
        northwestAntidiagonalIdeal R r ⊔
          ∑ ts ∈ conditions.toFinset, symbolicAntidiagonalIdeal R n ts.1 ts.2 := by
  let D : MixedDatum n := ⟨r,hr,conditions,hc⟩
  exact ⟨OrderTransfer.mixed_groebner_after_baseChange R D ω hω,
    OrderTransfer.mixed_initial_after_baseChange R D ω hω⟩

example (n : ℕ) (R : Type*) [CommRing R]
    (r : RankArray n) (hr : ∀ i j, r i j = r j i)
    (conditions : List (ℕ × ℕ))
    (hc : ∀ ts ∈ conditions, 1 ≤ ts.1 ∧ ts.1 ≤ n ∧ 1 ≤ ts.2)
    (ω : MonomialOrder (Entry n))
    (hω : ∀ δ : MinorData n, ω.degree (δ.polynomial ℤ) = δ.exponent) :
    let v : ω.standardMonomials (Ideal.span (mixedGenerators ℤ r conditions)) →
        CoordinateRing n R ⧸ integralMixedIdeal R r conditions :=
      fun a => Ideal.Quotient.mk _ (monomial a.val 1)
    LinearIndependent R v ∧ Submodule.span R (Set.range v) = ⊤ := by
  let D : MixedDatum n := ⟨r,hr,conditions,hc⟩
  exact OrderTransfer.standard_basis_after_baseChange R D ω hω

/-- The order need only select the antidiagonals over this coefficient ring. -/
example (n : ℕ) (R : Type*) [CommRing R]
    (r : RankArray n) (hr : ∀ i j, r i j = r j i)
    (conditions : List (ℕ × ℕ))
    (hc : ∀ ts ∈ conditions, 1 ≤ ts.1 ∧ ts.1 ≤ n ∧ 1 ≤ ts.2)
    (ω : MonomialOrder (Entry n))
    (hω : ∀ δ : MinorData n, ω.degree (δ.polynomial R) = δ.exponent) :
    ω.IsGroebnerBasis (mixedGenerators R r conditions) (integralMixedIdeal R r conditions) ∧
      Ideal.span (ω.leadingTerm ''
        (integralMixedIdeal R r conditions : Set (CoordinateRing n R))) =
        northwestAntidiagonalIdeal R r ⊔
          ∑ ts ∈ conditions.toFinset, symbolicAntidiagonalIdeal R n ts.1 ts.2 := by
  let D : MixedDatum n := ⟨r,hr,conditions,hc⟩
  exact ⟨OrderTransfer.mixed_groebner_of_selects R D ω hω,
    OrderTransfer.mixed_initial_of_selects R D ω hω⟩

example (n : ℕ) (R : Type*) [CommRing R]
    (r : RankArray n) (hr : ∀ i j, r i j = r j i)
    (conditions : List (ℕ × ℕ))
    (hc : ∀ ts ∈ conditions, 1 ≤ ts.1 ∧ ts.1 ≤ n ∧ 1 ≤ ts.2)
    (ω : MonomialOrder (Entry n))
    (hω : ∀ δ : MinorData n, ω.degree (δ.polynomial R) = δ.exponent) :
    let v : ω.standardMonomials (integralMixedIdeal R r conditions) →
        CoordinateRing n R ⧸ integralMixedIdeal R r conditions :=
      fun a => Ideal.Quotient.mk _ (monomial a.val 1)
    LinearIndependent R v ∧ Submodule.span R (Set.range v) = ⊤ := by
  let D : MixedDatum n := ⟨r,hr,conditions,hc⟩
  exact OrderTransfer.standard_basis_of_selects R D ω hω

end OtherAntidiagonalOrdersClosedStatements

/- Independent fully expanded checks for the transpose fixed-locus remark. -/
section TransposeFixedLocusClosedStatements
open FourPapers.Symmetric MvPolynomial
open scoped BigOperators

example (n : ℕ) (R : Type*) [CommRing R] :
    (MvPolynomial (Fin n × Fin n) R ⧸
      Ideal.span (Set.range (fun f : MvPolynomial (Fin n × Fin n) R =>
        f - MvPolynomial.rename Prod.swap f))) ≃ₐ[R] MvPolynomial (Entry n) R :=
  Transpose.coordinateRingEquiv n R

example (n : ℕ) (R : Type*) [CommRing R] :
    RingHom.ker
        ((MvPolynomial.rename (fun ij : Fin n × Fin n => fold ij.1 ij.2) :
          MvPolynomial (Fin n × Fin n) R →ₐ[R] MvPolynomial (Entry n) R).toRingHom) =
      Ideal.span (Set.range (fun ij : Fin n × Fin n =>
        (X ij : MvPolynomial (Fin n × Fin n) R) - X ij.swap)) :=
  Transpose.ker_foldHom n R

/-- The nonsymmetric family is the normalized actual determinant. -/
example (n t : ℕ) (a b : Fin t ↪o Fin n) :
    C (Polynomial.X ^ Deformation.minorWeight a b) *
      (∑ π : Equiv.Perm (Fin t),
        C (Polynomial.C (signCoefficient ℤ π) *
          Polynomial.X ^ (Deformation.termWeight a b π - Deformation.minorWeight a b)) *
            ∏ p, (X (a (π p), b p) : MvPolynomial (Fin n × Fin n) (Polynomial ℤ))) =
      Matrix.det (Matrix.of (fun i j : Fin t =>
        C (Polynomial.X ^ (((a i).val + 1) * ((b j).val + 1))) *
          (X (a i,b j) : MvPolynomial (Fin n × Fin n) (Polynomial ℤ)))) :=
  Transpose.normalizedMinor_normalized_determinant a b

/-- The normalized family is folded before taking the parameter fibers. -/
example (n t : ℕ) (a b : Fin t ↪o Fin n) :
    (MvPolynomial.rename (fun ij : Fin n × Fin n => fold ij.1 ij.2) :
        MvPolynomial (Fin n × Fin n) (Polynomial ℤ) →ₐ[Polynomial ℤ]
          MvPolynomial (Entry n) (Polynomial ℤ))
      (∑ π : Equiv.Perm (Fin t),
        C (Polynomial.C (signCoefficient ℤ π) *
          Polynomial.X ^ (Deformation.termWeight a b π - Deformation.minorWeight a b)) *
            ∏ p, X (a (π p), b p)) = Deformation.minorDeformation a b :=
  Transpose.foldHom_normalizedMinor a b

example (n t : ℕ) (a b : Fin t ↪o Fin n) :
    (MvPolynomial.rename (fun ij : Fin n × Fin n => fold ij.1 ij.2) :
        MvPolynomial (Fin n × Fin n) (Polynomial ℤ) →ₐ[Polynomial ℤ]
          MvPolynomial (Entry n) (Polynomial ℤ))
      (Matrix.det (Matrix.of (fun i j : Fin t =>
        C (Polynomial.X ^ (((a i).val + 1) * ((b j).val + 1))) *
          (X (a i,b j) : MvPolynomial (Fin n × Fin n) (Polynomial ℤ))))) =
      C (Polynomial.X ^ Deformation.minorWeight a b) * Deformation.minorDeformation a b :=
  Transpose.fixed_locus_normalized_minor a b

example :
    Deformation.minorDeformation (OrderEmbedding.id (Fin 2)) (OrderEmbedding.id (Fin 2)) =
      C Polynomial.X * (X (fold (0 : Fin 2) 0) : CoordinateRing 2 (Polynomial ℤ)) *
        X (fold (1 : Fin 2) 1) - X (fold (0 : Fin 2) 1) ^ 2 :=
  Transpose.two_by_two_deformation

example (R : Type*) [CommRing R] :
    MvPolynomial.map (Int.castRingHom R)
      (Deformation.specialization 0
        (Deformation.minorDeformation (OrderEmbedding.id (Fin 2)) (OrderEmbedding.id (Fin 2)))) =
          -(X (fold (0 : Fin 2) 1) : CoordinateRing 2 R) ^ 2 := by
  have h : Deformation.specialization 0
      (Deformation.minorDeformation
        (OrderEmbedding.id (Fin 2)) (OrderEmbedding.id (Fin 2))) =
        -(X (fold (0 : Fin 2) 1) : CoordinateRing 2 ℤ) ^ 2 :=
    Transpose.two_by_two_special_fiber
  simpa using congrArg (MvPolynomial.map (Int.castRingHom R)) h

end TransposeFixedLocusClosedStatements

example (K : Type u) [Field K] :
    ¬ IsIntegrallyClosed
      (FourPapers.Symmetric.Rees.initialAlgebra
        (FourPapers.Symmetric.foldedOrder 4)
        (FourPapers.Symmetric.Rees.determinantalSymbolicRees 4 K 2 (by decide))) := by
  exact FourPapers.Symmetric.Rees.Nonnormal.initial_symbolic_rees_not_integrallyClosed K

example (n : ℕ) (μ : YoungDiagram) :
    FourPapers.Symmetric.Schur.ShapeTableaux n μ ≃
      {S : SemistandardYoungTableau μ //
        ∀ c : ↥μ.cells, S c.val.1 c.val.2 < n} :=
  FourPapers.Symmetric.Schur.shapeTableauEquivMathlib n μ

#print axioms FourPapers.Symmetric.Rees.Nonnormal.initial_symbolic_rees_not_integrallyClosed
#print axioms FourPapers.Symmetric.Schur.shapeTableauEquivMathlib
#print axioms FourPapers.Symmetric.Schur.schurPolynomial_eq_mathlibTableauSum
end

set_option maxHeartbeats 8000000 in
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let constants := env.checked.get.constants.foldStage2
    (fun acc name ci => acc.push (name, ci)) (#[] : Array (Name × ConstantInfo))
  let allowed : Array Name := #["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let roots : Array Name := #[
    "FourPapers.Symmetric.symmetric_rank_loci".toName,
    "FourPapers.Symmetric.symmetric_rank_quotient_isDomain".toName,
    "FourPapers.Symmetric.compatible_rank_and_symbolic_conditions".toName,
    "FourPapers.Symmetric.compatible_initial_ideal".toName,
    "FourPapers.Symmetric.integral_rank_and_symbolic_conditions".toName,
    "FourPapers.Symmetric.integralMixedBasis".toName,
    "FourPapers.Symmetric.integralMixedBasis_apply".toName,
    "FourPapers.Symmetric.northwest_groebner".toName,
    "FourPapers.Symmetric.pairedTableau_rank_statistics".toName,
    "FourPapers.Symmetric.pairedTableau_packing_statistics".toName,
    "FourPapers.Symmetric.pairedTableau_packing_conjugate".toName,
    "FourPapers.Symmetric.insertion_statistics".toName,
    "FourPapers.Symmetric.hasSymbolicAntidiagonal_iff_gamma".toName,
    "FourPapers.Symmetric.mixedCarrierCorrespondence".toName,
    "FourPapers.Symmetric.symbolicPower_eq_localization_comap".toName,
    "FourPapers.Symmetric.symbolicGenerators_finite".toName,
    "FourPapers.Symmetric.northwestGenerators_finite".toName,
    "FourPapers.Symmetric.Pivot.lemma_3_3_symmetric".toName,
    "FourPapers.Symmetric.Pivot.symbolicPower_comap_genericFirstPivotChart".toName,
    "FourPapers.Symmetric.northwestQuotientBaseChangeEquiv".toName,
    "FourPapers.Symmetric.symmetric_rank_baseChange_isDomain".toName,
    "FourPapers.Symmetric.symmetric_rank_geometric_fibers".toName,
    "FourPapers.Symmetric.Simultaneous.exists_polynomial_simultaneous_basis".toName,
    "FourPapers.Symmetric.all_mixed_integral_simultaneous_basis".toName,
    "FourPapers.Symmetric.MixedLatticeExpression.adapted".toName,
    "FourPapers.Symmetric.integralMixedIdeal_field_eq_mixedIdeal".toName,
    "FourPapers.Symmetric.MixedLatticeExpression.baseChangedIdeal_eq_fieldIdeal".toName,
    "FourPapers.Symmetric.mixed_lattice_baseChange".toName,
    "FourPapers.Symmetric.mixed_lattice_baseChange_hom".toName,
    "FourPapers.Symmetric.mixed_lattice_map_inf".toName,
    "FourPapers.Symmetric.mixed_lattice_distributive_after_baseChange".toName,
    "FourPapers.Symmetric.mixed_lattice_initial_sup_after_baseChange".toName,
    "FourPapers.Symmetric.mixed_lattice_initial_inf_after_baseChange".toName,
    "FourPapers.Symmetric.mixed_lattice_standard_monomial_basis".toName,
    "FourPapers.Symmetric.mixed_lattice_quotient_free".toName,
    "FourPapers.Symmetric.mixed_lattice_quotient_flat".toName,
    "FourPapers.Symmetric.mixed_field_lattice_initial_sup".toName,
    "FourPapers.Symmetric.mixed_field_lattice_initial_inf".toName,
    "FourPapers.Symmetric.mixed_field_lattice_distributive".toName,
    "FourPapers.Symmetric.mixed_field_lattice_monomial_basis".toName,
    "FourPapers.Symmetric.Deformation.minorWeight_eq_paper_sum".toName,
    "FourPapers.Symmetric.Deformation.minorDeformation_normalized_determinant".toName,
    "FourPapers.Symmetric.Deformation.minorDeformation_at_one".toName,
    "FourPapers.Symmetric.Deformation.minorDeformation_at_zero".toName,
    "FourPapers.Symmetric.Deformation.deformed_simultaneous_basis".toName,
    "FourPapers.Symmetric.Deformation.latticeDeformation_free".toName,
    "FourPapers.Symmetric.Deformation.latticeDeformation_standard_basis".toName,
    "FourPapers.Symmetric.Deformation.latticeDeformation_quotient_free".toName,
    "FourPapers.Symmetric.Deformation.latticeDeformation_quotient_flat".toName,
    "FourPapers.Symmetric.Deformation.latticeDeformation_map_inf".toName,
    "FourPapers.Symmetric.Deformation.latticeDeformation_at_one".toName,
    "FourPapers.Symmetric.Deformation.latticeDeformation_at_zero".toName,
    "FourPapers.Symmetric.Deformation.latticeDeformation_at_one_after_baseChange".toName,
    "FourPapers.Symmetric.Deformation.latticeDeformation_at_zero_after_baseChange".toName,
    "FourPapers.Symmetric.Deformation.latticeDeformation_map_unit".toName,
    "FourPapers.Symmetric.Rees.corollary_7_1_sagbi".toName,
    "FourPapers.Symmetric.Rees.corollary_7_1_monomialBasis".toName,
    "FourPapers.Symmetric.Rees.corollary_7_1_monomialBasis_apply".toName,
    "FourPapers.Symmetric.gamma_add_fullAntidiagonal".toName,
    "FourPapers.Symmetric.fullDeterminant_pow_mul_mem_symbolicPower_iff".toName,
    "FourPapers.Symmetric.symbolicPower_inter_fullDeterminantal".toName,
    "FourPapers.Symmetric.JointSagbi.determinantGenerators_sagbi".toName,
    "FourPapers.Symmetric.JointSagbi.proposition_7_3_sagbi".toName,
    "FourPapers.Symmetric.JointSagbi.not_isSagbiBasis_two_threshold".toName,
    "FourPapers.Symmetric.JointSagbi.isSagbiBasis_iff_leadingMonomials".toName,
    "FourPapers.Symmetric.JointSagbi.joint_minor_sagbi_iff_full_size".toName,
    "FourPapers.Symmetric.Schur.schurPolynomial_coeff".toName,
    "FourPapers.Symmetric.Schur.pairedTableau_content_weight".toName,
    "FourPapers.Symmetric.Schur.schur_coefficient_support_finite".toName,
    "FourPapers.Symmetric.Schur.rank_schur_coefficient_support_finite".toName,
    "FourPapers.Symmetric.Schur.corollary_5_3_schur_hilbert_coefficient".toName,
    "FourPapers.Symmetric.Schur.corollary_5_3_schur_hilbert_series".toName,
    "FourPapers.Symmetric.Schur.corollary_5_3_rank_schur_hilbert_series".toName,
    "FourPapers.Symmetric.Schur.tableauRowExponent_injective".toName,
    "FourPapers.Symmetric.Schur.degreeTableaux_card_eq_finrank".toName,
    "FourPapers.Symmetric.Schur.degreeTableauBasis".toName,
    "FourPapers.Symmetric.Schur.degreeSymbolicQuotient_finrank".toName,
    "FourPapers.Symmetric.Schur.doubleShape_colLen_even".toName,
    "FourPapers.Symmetric.Schur.doubleShape_colLen_odd".toName,
    "FourPapers.Symmetric.Schur.columnSizes_score_eq_tail".toName,
    "FourPapers.Symmetric.Schur.bitableauPolynomial_isHomogeneous".toName,
    "FourPapers.Symmetric.Schur.bitableau_minor_score".toName,
    "FourPapers.Symmetric.Schur.bitableauRowExponent_eq".toName,
    "FourPapers.Symmetric.Schur.bitableauLexExponent_injective".toName,
    "FourPapers.Symmetric.Strata.exactMinorRank_iff_rank".toName,
    "FourPapers.Symmetric.Strata.exists_unique_symmetric_rook".toName,
    "FourPapers.Symmetric.Strata.SymmetricRook.exponents_empty".toName,
    "FourPapers.Symmetric.Strata.SymmetricRook.exponents_zeroExtend".toName,
    "FourPapers.Symmetric.Strata.SymmetricRook.exponents_diagonalExtend".toName,
    "FourPapers.Symmetric.Strata.SymmetricRook.exponents_pairedExtend".toName,
    "FourPapers.Symmetric.Strata.SymmetricRook.openSchemeIso".toName,
    "FourPapers.Symmetric.Strata.SymmetricRook.openSchemeIso_over".toName,
    "FourPapers.Symmetric.Strata.SymmetricRook.openSchemeIso_after_baseChange".toName,
    "FourPapers.Symmetric.Strata.SymmetricRook.openSchemeIso_after_baseChange_over".toName,
    "FourPapers.Symmetric.Strata.SymmetricRook.locus_birational_affineSpace".toName,
    "FourPapers.Symmetric.Strata.SymmetricRook.stratumStructureMap_smooth".toName,
    "FourPapers.Symmetric.Strata.proposition_6_5_geometry".toName,
    "FourPapers.Symmetric.Strata.proposition_6_5_point_count".toName,
    "FourPapers.Symmetric.Strata.rankLocusRationalPointEquiv".toName,
    "FourPapers.Symmetric.Strata.proposition_6_5_scheme_point_count".toName,
    "CommAlg.IntegralOverIdeal.of_pow".toName,
    "CommAlg.idealIntegralClosure_isIntegrallyClosed".toName,
    "FourPapers.Symmetric.DeterminantalTransfer.tupleProduct_mem_integralClosure_product".toName,
    "FourPapers.Symmetric.DeterminantalTransfer.tupleProduct_integral_of_convex_scores".toName,
    "FourPapers.Symmetric.DeterminantalTransfer.integralOver_sum_products_iff_support".toName,
    "FourPapers.Symmetric.RationalPolyhedra.nonnegative_separation".toName,
    "FourPapers.Symmetric.RationalPolyhedra.mem_upperHull_iff_ceilingVectors".toName,
    "FourPapers.Symmetric.symbolicPower_iff_basis_support_of_weight".toName,
    "FourPapers.Symmetric.IntegralClosure.closure_eq_finite_symbolic_lattice_of_minor_basis".toName,
    "FourPapers.Symmetric.BoundedLattice.exists_integral_simultaneous_basis".toName,
    "FourPapers.Symmetric.BoundedLattice.initial_inf".toName,
    "FourPapers.Symmetric.BoundedLattice.coefficient_change_inf".toName,
    "FourPapers.Symmetric.BoundedLattice.standard_monomial_basis".toName,
    "FourPapers.Symmetric.BoundedLattice.deformation_flat".toName,
    "FourPapers.Symmetric.BoundedLattice.deformation_at_zero".toName,
    "FourPapers.Symmetric.BoundedLattice.baseChangedIdeal_map".toName,
    "FourPapers.Symmetric.BoundedLattice.baseChangedIdeal_map_inf".toName,
    "FourPapers.Symmetric.BoundedLattice.deformation_standard_basis".toName,
    "FourPapers.Symmetric.BoundedLattice.deformation_map_unit".toName,
    "FourPapers.Symmetric.IntegralClosure.integralClosure_eq_symbolic_intersections".toName,
    "FourPapers.Symmetric.IntegralClosure.corollary_7_2_initial".toName,
    "FourPapers.Symmetric.IntegralClosure.corollary_7_2".toName,
    "FourPapers.Symmetric.IntegralClosure.corollary_7_2_first_part".toName,
    "FourPapers.Symmetric.IntegralClosure.corollary_7_2_integral_model".toName,
    "FourPapers.Symmetric.IntegralClosure.corollary_7_2_deformation_flat".toName,
    "FourPapers.Symmetric.IntegralClosure.corollary_7_2_symbolic_formula".toName,
    "FourPapers.Symmetric.IntegralClosure.corollary_7_2_model_free".toName,
    "FourPapers.Symmetric.IntegralClosure.corollary_7_2_deformation_free".toName,
    "FourPapers.Symmetric.IntegralClosure.corollary_7_2_deformation_fibers".toName,
    "FourPapers.Symmetric.IntegralClosure.corollary_7_2_deformation_standard_basis".toName,
    "FourPapers.Symmetric.IntegralClosure.corollary_7_2_deformation_unit".toName,
    "FourPapers.Symmetric.IntegralClosure.corollary_7_2_deformation_unit_field".toName,
    "FourPapers.Symmetric.IntegralClosure.corollary_7_2_model_map".toName,
    "FourPapers.Symmetric.Strata.exists_recipe_realizing_symmetric_rook".toName,
    "FourPapers.Symmetric.Strata.SymmetricRook.recipe_rook_eq".toName,
    "FourPapers.Symmetric.BoundedLattice.initial_sup_after_baseChange".toName,
    "FourPapers.Symmetric.BoundedLattice.initial_inf_after_baseChange".toName,
    "MonomialOrder.IsGroebnerBasis.changeOrder_of_degree_eq".toName,
    "FourPapers.Symmetric.OrderTransfer.mixed_field_groebner".toName,
    "FourPapers.Symmetric.OrderTransfer.mixed_field_initial".toName,
    "FourPapers.Symmetric.OrderTransfer.mixed_groebner_after_baseChange".toName,
    "FourPapers.Symmetric.OrderTransfer.standard_basis_after_baseChange".toName,
    "FourPapers.Symmetric.OrderTransfer.mixed_initial_after_baseChange".toName,
    "FourPapers.Symmetric.OrderTransfer.integral_standardMonomials_eq".toName,
    "FourPapers.Symmetric.OrderTransfer.mixed_groebner_of_selects".toName,
    "FourPapers.Symmetric.OrderTransfer.mixed_initial_of_selects".toName,
    "FourPapers.Symmetric.OrderTransfer.standard_basis_of_selects".toName,
    "FourPapers.Symmetric.Transpose.ker_foldHom".toName,
    "FourPapers.Symmetric.Transpose.coordinateRingEquiv".toName,
    "FourPapers.Symmetric.Transpose.fixed_locus_normalized_minor".toName,
    "FourPapers.Symmetric.Transpose.foldHom_normalizedMinor".toName,
    "FourPapers.Symmetric.Transpose.normalizedMinor_normalized_determinant".toName,
    "FourPapers.Symmetric.Transpose.two_by_two_deformation".toName,
    "FourPapers.Symmetric.Transpose.two_by_two_special_fiber".toName,
    "FourPapers.Symmetric.Rees.Nonnormal.pairedTableau_hole".toName,
    "FourPapers.Symmetric.Rees.Nonnormal.hole_not_mem".toName,
    "FourPapers.Symmetric.Rees.Nonnormal.hole_square_mem".toName,
    "FourPapers.Symmetric.Rees.Nonnormal.initial_symbolic_rees_not_integrallyClosed".toName,
    "FourPapers.Symmetric.Schur.shapeTableauEquivMathlib".toName,
    "FourPapers.Symmetric.Schur.schurPolynomial_eq_mathlibTableauSum".toName]
  let mut runtimeOnly : Array Name := #[]
  let mut auditedImports : NameSet := {}
  for (name, ci) in constants do
    if ci.isAxiom then
      throwError "Unapproved local axiom: {name}"
    if ci.isUnsafe || ci.isPartial then
      unless name.getString! == "_unsafe_rec" do
        throwError "Authored or unrecognized unsafe declaration: {name}"
      match env.find? name.getPrefix with
      | some parent =>
        if parent.isUnsafe || parent.isPartial || parent.isAxiom then
          throwError "Unsafe runtime companion lacks safe defining declaration: {name}"
      | none => throwError "Unrecognized runtime companion: {name}"
      runtimeOnly := runtimeOnly.push name
    else
      for dep in ci.type.getUsedConstants ++ ((ci.value? true).map Expr.getUsedConstants |>.getD #[]) do
        if let some info := env.find? dep then
          if info.isUnsafe || info.isPartial then
            throwError "Unsafe proof dependency {dep} in safe declaration {name}"
          if info.isAxiom && !auditedImports.contains dep then
            -- Exported theorems may have axiom-shaped public declarations. Stock Lean's
            -- exportedAxiomsExt stores their checked, transitive axiom dependencies.
            -- collectAxioms uses that metadata rather than misclassifying proof stubs.
            let deps ← collectAxioms dep
            for ax in deps do
              if !allowed.contains ax then
                throwError "Unapproved imported axiom {ax}, reached through {dep} in {name}"
            auditedImports := auditedImports.insert dep
  let mut rootAxioms : Array Json := #[]
  for root in roots do
    unless env.contains root do
      throwError "Required final theorem is unavailable: {root}"
    let axioms ← collectAxioms root
    for ax in axioms do
      if !allowed.contains ax then
        throwError "Unapproved transitive axiom in {root}: {ax}"
    rootAxioms := rootAxioms.push <| Json.mkObj [
      ("theorem", toJson root.toString), ("axioms", toJson (axioms.map Name.toString))]
  let ctors (ci : ConstantInfo) : Array Name :=
    match ci with
    | .inductInfo v => v.ctors.toArray
    | _ => #[]
  let mut names : NameSet := {}
  for (name, ci) in constants do
    names := names.insert name
    for dep in ci.type.getUsedConstants do
      names := names.insert dep
    for dep in (ci.value? true).map Expr.getUsedConstants |>.getD #[] do
      names := names.insert dep
    for dep in ctors ci do
      names := names.insert dep
  for root in roots do
    names := names.insert root
  let dictionary := names.toArray.qsort Name.lt
  let mut indices : NameMap Nat := {}
  for i in [:dictionary.size] do
    indices := indices.insert dictionary[i]! i
  let index (n : Name) := (indices.find? n).getD 0
  let data := constants.map fun (name, ci) =>
    Json.arr #[toJson (index name), toJson (ci.type.getUsedConstants.map index),
      toJson (((ci.value? true).map Expr.getUsedConstants |>.getD #[]).map index),
      toJson ((ctors ci).map index), toJson ci.isAxiom, toJson ci.isUnsafe, toJson ci.isPartial]
  let graph := Json.mkObj [
    ("format", toJson "local-proof-dag-v1"),
    ("columns", toJson (#["name", "type", "value", "inductiveCtors", "axiom", "unsafe", "partial"] : Array String)),
    ("names", toJson (dictionary.map Name.toString)),
    ("nodes", Json.arr data),
    ("roots", toJson (roots.map index)),
    ("root_axioms", Json.arr rootAxioms),
    ("compiler_runtime_only", toJson (runtimeOnly.map Name.toString))]
  liftIO <| IO.FS.createDirAll ".lake/reports/audit"
  liftIO <| IO.FS.writeFile ".lake/reports/audit/complete_dependency_graph.json" (Json.compress graph)
  logInfo m!"COMPLETE_VERIFICATION_AUDIT_OK {constants.size} local declarations; {roots.size} verification roots; only propext, Classical.choice, Quot.sound; no authored axioms or unsafe proof dependencies."
