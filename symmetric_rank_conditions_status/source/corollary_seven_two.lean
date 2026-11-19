module
public import integral_closure_theory
public import gram_bitableaux

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-!
# Corollary 7.2: integral closures of finite sums of minor products

The coefficient field is arbitrary.  The shape family is finite and
nonempty, its parts are bounded only by the matrix size, and every monomial
exponent is unrestricted.  The proof supplies the full integral-closure
formula, the stated initial-ideal criterion, a common compatible-lattice
expression over the integers, and the associated simultaneous flat family.

Lists are used for shapes.  No ordering assumption is needed in the stronger
family theorem; the final wrapper takes the literal positive decreasing
partition lists appearing in the paper.
-/

noncomputable section
namespace FourPapers.Symmetric.IntegralClosure
open scoped BigOperators Pointwise
open MvPolynomial

variable {n : ℕ} {α : Type*} [Fintype α]

theorem bitableau_gamma (T : Schur.EvenSemistandardTableaux n) (j : Fin n) :
    DeterminantalTransfer.gamma ((Schur.bitableauMinors T).map MinorData.size) (j.val+1) =
      Gram.tableauScore T j := by
  have hh := Schur.bitableau_minor_score T (j.val+1) (by omega)
  simpa only [DeterminantalTransfer.gamma,Schur.bitableauMinors,List.map_map,
    List.map_ofFn,List.sum_ofFn,Function.comp_def,Gram.tableauScore,
    Nat.add_sub_cancel] using hh

/-- The exact finite version of Henriques--Varbaro's symbolic-intersection
formula, derived here from kernel-checked determinant and convex arguments. -/
theorem integralClosure_eq_symbolic_intersections
    (K : Type*) [Field K] [Nonempty α]
    (sizes : α → List ℕ) (hsizes : ∀ i a, a ∈ sizes i → a ≤ n) :
    CommAlg.idealIntegralClosure (shapeSumIdeal n K sizes) =
      (RationalPolyhedra.ceilingVectors (fun i (j : Fin n) =>
        DeterminantalTransfer.gamma (sizes i) (j.val+1))).sup
          (fun a => ⨅ j : Fin n, symbolicPower (determinantalIdeal n K (j.val+1)) (a j)) := by
  apply closure_eq_finite_symbolic_lattice_of_minor_basis
    (Gram.bitableauBasis n K) Schur.bitableauMinors
    (by
      intro T
      rw [Gram.bitableauBasis_apply,Schur.bitableauPolynomial_eq_list_product])
    sizes hsizes (Gram.hom n K).toRingHom Gram.weight
  · intro a ha f
    exact Gram.bound_zero_of_nonnegative_weight K a ha (Gram.hom n K f)
  · intro a ha t r c
    change CommAlg.RealWeight.Bound (Gram.weight a)
      (2 * ∑ j : Fin n, a j * (t + 1 - (j.val + 1) : ℕ))
        (Gram.hom n K ((genericMatrix n K).submatrix r c).det)
    simpa only [Nat.add_sub_add_right] using Gram.hom_tupleMinor_bound K r c a ha
  · intro a ha f c
    change CommAlg.RealWeight.Bound (Gram.weight a) c (Gram.hom n K f) ↔
      ∀ T, (Gram.bitableauBasis n K).repr f T ≠ 0 → c ≤
        2 * ∑ j : Fin n, a j *
          (DeterminantalTransfer.gamma ((Schur.bitableauMinors T).map MinorData.size)
            (j.val + 1) : ℕ)
    simpa only [bitableau_gamma,Gram.tableauWeight] using
      Gram.bound_hom_iff_basis_support n K a ha f c

def symbolicIntersection (a : Fin n → ℕ) : BoundedLattice.Expr n :=
  BoundedLattice.meetFamily (fun j => BoundedLattice.symbolic j (a j)) (List.ofFn id)

def closureExpression (sizes : α → List ℕ) : BoundedLattice.Expr n :=
  BoundedLattice.joinFamily symbolicIntersection
    (RationalPolyhedra.ceilingVectors (fun i (j : Fin n) =>
      DeterminantalTransfer.gamma (sizes i) (j.val+1))).toList

theorem symbolicIntersection_field (K : Type*) [Field K] (a : Fin n → ℕ) :
    BoundedLattice.fieldIdeal K (symbolicIntersection a) =
      ⨅ j : Fin n, symbolicPower (determinantalIdeal n K (j.val+1)) (a j) := by
  ext f
  rw [symbolicIntersection,BoundedLattice.mem_fieldIdeal_meetFamily]
  simp [BoundedLattice.fieldIdeal_symbolic,Ideal.mem_iInf,List.mem_ofFn]

theorem symbolicIntersection_monomials (a : Fin n → ℕ) (m : Entry n →₀ ℕ) :
    m ∈ BoundedLattice.monomials (symbolicIntersection a) ↔
      ∀ j : Fin n, a j ≤ gamma (j.val+1) m := by
  rw [symbolicIntersection,BoundedLattice.mem_monomials_meetFamily]
  simp [BoundedLattice.mem_monomials_symbolic,List.mem_ofFn]

theorem closureExpression_field (K : Type*) [Field K] [Nonempty α]
    (sizes : α → List ℕ) (hsizes : ∀ i a, a ∈ sizes i → a ≤ n) :
    BoundedLattice.fieldIdeal K (closureExpression sizes) =
      CommAlg.idealIntegralClosure (shapeSumIdeal n K sizes) := by
  classical
  rw [closureExpression,BoundedLattice.fieldIdeal_joinFamily,
    Finset.toList_toFinset,integralClosure_eq_symbolic_intersections K sizes hsizes]
  apply Finset.sup_congr rfl
  intro a ha
  exact symbolicIntersection_field K a

theorem closureExpression_monomials (sizes : α → List ℕ) (m : Entry n →₀ ℕ) :
    m ∈ BoundedLattice.monomials (closureExpression sizes) ↔
      (fun j : Fin n => (gamma (j.val+1) m : ℝ)) ∈
        RationalPolyhedra.upperHull (fun i (j : Fin n) =>
          (DeterminantalTransfer.gamma (sizes i) (j.val+1) : ℝ)) := by
  rw [closureExpression,BoundedLattice.mem_monomials_joinFamily,
    RationalPolyhedra.mem_upperHull_iff_ceilingVectors]
  simp only [Finset.mem_toList,symbolicIntersection_monomials,Pi.le_def]

def shapePolytope (sizes : α → List ℕ) : Set (Fin n → ℝ) :=
  convexHull ℝ (Set.range (fun i (j : Fin n) =>
    (DeterminantalTransfer.gamma (sizes i) (j.val+1) : ℝ)))

/-- The literal symbolic-intersection formula indexed by every real
point of the paper's polytope. The finite ceiling formula above is proved
equivalent to this actual ideal sum. -/
theorem corollary_7_2_symbolic_formula (K : Type*) [Field K] [Nonempty α]
    (sizes : α → List ℕ) (hsizes : ∀ i a, a ∈ sizes i → a ≤ n) :
    CommAlg.idealIntegralClosure (shapeSumIdeal n K sizes) =
      ⨆ a ∈ shapePolytope sizes,
        ⨅ j : Fin n, symbolicPower (determinantalIdeal n K (j.val+1)) (Nat.ceil (a j)) := by
  rw [integralClosure_eq_symbolic_intersections K sizes hsizes,
    RationalPolyhedra.ceilingVectors_sup_eq_iSup]
  rfl

/-- Corollary 7.2's monomial equivalence, with the literal convex hull and
the positive real orthant on the right. -/
theorem corollary_7_2_initial (K : Type*) [Field K] [Nonempty α]
    (sizes : α → List ℕ) (hsizes : ∀ i a, a ∈ sizes i → a ≤ n)
    (m : Entry n →₀ ℕ) :
    monomial m (1 : K) ∈ initialIdeal K
        (CommAlg.idealIntegralClosure (shapeSumIdeal n K sizes)) ↔
      (fun j : Fin n => (gamma (j.val+1) m : ℝ)) ∈
        shapePolytope sizes + {z : Fin n → ℝ | 0 ≤ z} := by
  rw [← closureExpression_field K sizes hsizes,BoundedLattice.monomial_mem_initial_iff,
    closureExpression_monomials,RationalPolyhedra.upperHull_eq_minkowski]
  rfl

/-- The common integral model specializes to the actual integral closure
over every field, including characteristic two. -/
theorem corollary_7_2_integral_model (K : Type*) [Field K] [Nonempty α]
    (sizes : α → List ℕ) (hsizes : ∀ i a, a ∈ sizes i → a ≤ n) :
    (BoundedLattice.ideal (closureExpression sizes)).map
        (MvPolynomial.map (Int.castRingHom K)) =
      CommAlg.idealIntegralClosure (shapeSumIdeal n K sizes) := by
  rw [← BoundedLattice.baseChangedIdeal_eq_map,
    BoundedLattice.baseChangedIdeal_eq_fieldIdeal,closureExpression_field K sizes hsizes]

/-- Arbitrary coefficient change preserves a free quotient for the
integral model selected by the closure formula. -/
theorem corollary_7_2_model_free (R : Type*) [CommRing R]
    (sizes : α → List ℕ) :
    Module.Free R (CoordinateRing n R ⧸
      (BoundedLattice.ideal (closureExpression sizes)).map
        (MvPolynomial.map (Int.castRingHom R))) := by
  rw [← BoundedLattice.baseChangedIdeal_eq_map]
  exact BoundedLattice.quotient_free R (closureExpression sizes)

/-- The flat family is the same compatible simultaneous degeneration used
for northwest rank conditions and symbolic powers. -/
theorem corollary_7_2_deformation_free (R : Type*) [CommRing R]
    (φ : Polynomial ℤ →+* R) (sizes : α → List ℕ) :
    Module.Free R (CoordinateRing n R ⧸
      (BoundedLattice.deformation (closureExpression sizes)).map (MvPolynomial.map φ)) :=
  BoundedLattice.deformation_free R φ (closureExpression sizes)

theorem corollary_7_2_deformation_flat (R : Type*) [CommRing R]
    (φ : Polynomial ℤ →+* R) (sizes : α → List ℕ) :
    Module.Flat R (CoordinateRing n R ⧸
      (BoundedLattice.deformation (closureExpression sizes)).map (MvPolynomial.map φ)) :=
  BoundedLattice.deformation_flat R φ (closureExpression sizes)

/-- The literal standard monomials form the same basis in every member
of the simultaneous family, after every coefficient specialization. -/
theorem corollary_7_2_deformation_standard_basis (R : Type*) [CommRing R]
    (φ : Polynomial ℤ →+* R) (sizes : α → List ℕ) :
    let I := (BoundedLattice.deformation (closureExpression sizes)).map (MvPolynomial.map φ)
    let v : (foldedOrder n).standardMonomials
        (BoundedLattice.ideal (closureExpression sizes)) → CoordinateRing n R ⧸ I :=
      fun a => Ideal.Quotient.mk I (monomial a.val 1)
    LinearIndependent R v ∧ Submodule.span R (Set.range v) = ⊤ :=
  BoundedLattice.deformation_standard_basis R φ (closureExpression sizes)

/-- Every invertible fiber of the integer model is its prescribed variable rescaling. -/
theorem corollary_7_2_deformation_unit (R : Type*) [CommRing R]
    (φ : Polynomial ℤ →+* R) (x : Rˣ) (hx : φ Polynomial.X = (x : R))
    (sizes : α → List ℕ) :
    (BoundedLattice.deformation (closureExpression sizes)).map (MvPolynomial.map φ) =
      (BoundedLattice.baseChangedIdeal R (closureExpression sizes)).map
        (Deformation.variableScaling (fun i : Entry n => x ^ Deformation.entryWeight i)).toRingHom :=
  BoundedLattice.deformation_map_unit φ x hx (closureExpression sizes)

/-- Over a field, the same rescaled ideal is the actual integral closure. -/
theorem corollary_7_2_deformation_unit_field (K : Type*) [Field K] [Nonempty α]
    (φ : Polynomial ℤ →+* K) (x : Kˣ) (hx : φ Polynomial.X = (x : K))
    (sizes : α → List ℕ) (hsizes : ∀ i a, a ∈ sizes i → a ≤ n) :
    (BoundedLattice.deformation (closureExpression sizes)).map (MvPolynomial.map φ) =
      (CommAlg.idealIntegralClosure (shapeSumIdeal n K sizes)).map
        (Deformation.variableScaling (fun i : Entry n => x ^ Deformation.entryWeight i)).toRingHom := by
  rw [corollary_7_2_deformation_unit K φ x hx,
    BoundedLattice.baseChangedIdeal_eq_fieldIdeal,closureExpression_field K sizes hsizes]

/-- The chosen integer model is functorial under all coefficient maps. -/
theorem corollary_7_2_model_map {A B : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) (sizes : α → List ℕ) :
    (BoundedLattice.baseChangedIdeal A (closureExpression (n := n) sizes)).map
        (MvPolynomial.map φ) = BoundedLattice.baseChangedIdeal B (closureExpression sizes) :=
  BoundedLattice.baseChangedIdeal_map φ (closureExpression sizes)

theorem corollary_7_2_deformation_fibers (sizes : α → List ℕ) :
    (BoundedLattice.deformation (closureExpression (n := n) sizes)).map
        (Deformation.specialization 1) =
        BoundedLattice.ideal (closureExpression (n := n) sizes) ∧
      (BoundedLattice.deformation (closureExpression (n := n) sizes)).map
          (Deformation.specialization 0) =
        Simultaneous.orderInitialIdeal (foldedOrder n)
          (BoundedLattice.ideal (closureExpression (n := n) sizes)) :=
  ⟨BoundedLattice.deformation_at_one _,BoundedLattice.deformation_at_zero _⟩

theorem partition_sum_eq_shapeSum (n : ℕ) (R : Type*) [CommRing R]
    (shapes : Finset (List ℕ)) :
    (∑ σ ∈ shapes, (σ.map (determinantalIdeal n R)).prod) =
      shapeSumIdeal n R (fun σ : shapes => σ.val) := by
  rw [Ideal.sum_eq_sup,Finset.sup_eq_iSup,shapeSumIdeal,iSup_subtype]
  rfl

/-- The paper's literal finite-set statement.  The entries of every list
are positive and weakly decreasing, hence are precisely partition parts.
The proof also covers the empty partition if it is admitted by convention. -/
theorem corollary_7_2 (K : Type*) [Field K]
    (shapes : Finset (List ℕ)) (hshapes : shapes.Nonempty)
    (_hdecreasing : ∀ σ ∈ shapes, σ.SortedGE)
    (hparts : ∀ σ ∈ shapes, ∀ a ∈ σ, 1 ≤ a ∧ a ≤ n)
    (m : Entry n →₀ ℕ) :
    monomial m (1 : K) ∈ initialIdeal K
        (CommAlg.idealIntegralClosure (∑ σ ∈ shapes, (σ.map (determinantalIdeal n K)).prod)) ↔
      (fun j : Fin n => (gamma (j.val+1) m : ℝ)) ∈
        shapePolytope (fun σ : shapes => σ.val) + {z : Fin n → ℝ | 0 ≤ z} := by
  letI : Nonempty shapes := by
    obtain ⟨σ,hσ⟩ := hshapes
    exact ⟨⟨σ,hσ⟩⟩
  rw [partition_sum_eq_shapeSum]
  exact corollary_7_2_initial K (fun σ : shapes => σ.val)
    (fun σ a ha => (hparts σ.val σ.property a ha).2) m

/-- For a partition, bounding its first part is exactly the same as
bounding all its parts.  The empty partition has first-part default zero. -/
theorem partition_parts_le_iff_head (σ : List ℕ) (hσ : σ.SortedGE) (n : ℕ) :
    (∀ a ∈ σ, a ≤ n) ↔ σ.headD 0 ≤ n := by
  cases σ with
  | nil => simp
  | cons a L =>
      constructor
      · intro h
        exact h a (List.mem_cons_self ..)
      · intro hn b hb
        obtain ⟨i,hi⟩ := List.mem_iff_get.mp hb
        have hh : (a :: L).get i ≤ a :=
          hσ.antitone_get
            (show (⟨0,by simp⟩ : Fin (a :: L).length) ≤ i from Nat.zero_le _)
        rw [hi] at hh
        exact hh.trans hn

/-- Corollary 7.2 with the paper's hypothesis stated literally as
`σ₁ ≤ n`, rather than its equivalent all-parts formulation. -/
theorem corollary_7_2_first_part (K : Type*) [Field K]
    (shapes : Finset (List ℕ)) (hshapes : shapes.Nonempty)
    (hdecreasing : ∀ σ ∈ shapes, σ.SortedGE)
    (hpositive : ∀ σ ∈ shapes, ∀ a ∈ σ, 1 ≤ a)
    (hfirst : ∀ σ ∈ shapes, σ.headD 0 ≤ n)
    (m : Entry n →₀ ℕ) :
    monomial m (1 : K) ∈ initialIdeal K
        (CommAlg.idealIntegralClosure (∑ σ ∈ shapes, (σ.map (determinantalIdeal n K)).prod)) ↔
      (fun j : Fin n => (gamma (j.val+1) m : ℝ)) ∈
        shapePolytope (fun σ : shapes => σ.val) + {z : Fin n → ℝ | 0 ≤ z} := by
  apply corollary_7_2 K shapes hshapes hdecreasing
  intro σ hσ a ha
  exact ⟨hpositive σ hσ a ha,
    (partition_parts_le_iff_head σ (hdecreasing σ hσ) n).mpr (hfirst σ hσ) a ha⟩

end FourPapers.Symmetric.IntegralClosure

namespace FourPapers.Symmetric.BoundedLattice

/-- Initial ideals of all the integral models preserve sums over every
commutative coefficient ring.  This includes every closure expression. -/
theorem initial_sup_after_baseChange {n : ℕ} (R : Type*) [CommRing R]
    (e f : Expr n) :
    Simultaneous.orderInitialIdeal (foldedOrder n)
        (baseChangedIdeal R e ⊔ baseChangedIdeal R f) =
      Simultaneous.orderInitialIdeal (foldedOrder n) (baseChangedIdeal R e) ⊔
        Simultaneous.orderInitialIdeal (foldedOrder n) (baseChangedIdeal R f) := by
  cases e <;> cases f <;>
    simp [baseChangedIdeal, orderInitialIdeal_top, mixed_lattice_initial_sup_after_baseChange]

/-- Initial ideals also preserve actual intersections, with no flatness
or nontriviality hypothesis on the coefficient ring. -/
theorem initial_inf_after_baseChange {n : ℕ} (R : Type*) [CommRing R]
    (e f : Expr n) :
    Simultaneous.orderInitialIdeal (foldedOrder n)
        (baseChangedIdeal R e ⊓ baseChangedIdeal R f) =
      Simultaneous.orderInitialIdeal (foldedOrder n) (baseChangedIdeal R e) ⊓
        Simultaneous.orderInitialIdeal (foldedOrder n) (baseChangedIdeal R f) := by
  cases e <;> cases f <;>
    simp [baseChangedIdeal, orderInitialIdeal_top, mixed_lattice_initial_inf_after_baseChange]

end FourPapers.Symmetric.BoundedLattice
end

#print axioms FourPapers.Symmetric.IntegralClosure.integralClosure_eq_symbolic_intersections
#print axioms FourPapers.Symmetric.IntegralClosure.corollary_7_2_initial
#print axioms FourPapers.Symmetric.IntegralClosure.corollary_7_2
#print axioms FourPapers.Symmetric.IntegralClosure.corollary_7_2_first_part
#print axioms FourPapers.Symmetric.IntegralClosure.corollary_7_2_integral_model
#print axioms FourPapers.Symmetric.IntegralClosure.corollary_7_2_deformation_flat

#print axioms FourPapers.Symmetric.IntegralClosure.corollary_7_2_symbolic_formula
#print axioms FourPapers.Symmetric.IntegralClosure.corollary_7_2_model_free
#print axioms FourPapers.Symmetric.IntegralClosure.corollary_7_2_deformation_free
#print axioms FourPapers.Symmetric.IntegralClosure.corollary_7_2_deformation_fibers

#print axioms FourPapers.Symmetric.IntegralClosure.corollary_7_2_deformation_standard_basis
#print axioms FourPapers.Symmetric.IntegralClosure.corollary_7_2_deformation_unit
#print axioms FourPapers.Symmetric.IntegralClosure.corollary_7_2_deformation_unit_field
#print axioms FourPapers.Symmetric.IntegralClosure.corollary_7_2_model_map

#print axioms FourPapers.Symmetric.BoundedLattice.initial_sup_after_baseChange
#print axioms FourPapers.Symmetric.BoundedLattice.initial_inf_after_baseChange
