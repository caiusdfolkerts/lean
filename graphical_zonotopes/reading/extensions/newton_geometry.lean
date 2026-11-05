module

public import Papers.GraphicalZonotopes.PolynomialWeights
public import Papers.GraphicalZonotopes.PathDimension
public import Papers.GraphicalZonotopes.LatticeSupport
public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Every polynomial with the path Newton polytope is absolutely irreducible

The Newton polytope is the ordinary real convex hull of the exponent support.
For a product whose Newton polytope is a supermodular base polytope, minimum
subset weights and maximum total weight prove the actual Minkowski identity.
This avoids needing a generic Newton-product theorem for arbitrary polytopes.

The factorization argument uses the original supermodular extreme ray and one
literal slack of value one. Factor Newton polytopes have integral lower-support
values and nonnegative coordinates. The singleton minima of the two factors
therefore vanish separately, so their lower-support functions need no further
translation normalization.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section
open scoped Classical BigOperators Pointwise

namespace GraphicalZonotopes.NewtonGeometry

open Finset
open PolynomialWeights

variable {V R : Type*} [Fintype V] [DecidableEq V] [CommSemiring R]

/-- Exponents are embedded in the actual standard real coordinate space. -/
def exponentVector (d : V →₀ ℕ) : V → ℝ := fun v => (d v : ℝ)

/-- The ordinary Newton polytope, including the empty polytope for zero. -/
def newtonPolytope (p : MvPolynomial V R) : Set (V → ℝ) :=
  convexHull ℝ (exponentVector '' (p.support : Set (V →₀ ℕ)))

@[simp] theorem exponentVector_zero : exponentVector (0 : V →₀ ℕ) = 0 := by
  funext v
  simp [exponentVector]

@[simp] theorem exponentVector_add (d e : V →₀ ℕ) :
    exponentVector (d + e) = exponentVector d + exponentVector e := by
  funext v
  simp [exponentVector, Nat.cast_add]

theorem support_mem_newton {p : MvPolynomial V R} {d : V →₀ ℕ}
    (hd : d ∈ p.support) : exponentVector d ∈ newtonPolytope p :=
  subset_convexHull ℝ _ ⟨d, hd, rfl⟩

@[simp] theorem newton_zero : newtonPolytope (0 : MvPolynomial V R) = ∅ := by
  simp [newtonPolytope]

theorem newton_nonempty {p : MvPolynomial V R} (hp : p ≠ 0) :
    (newtonPolytope p).Nonempty := by
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hp
  exact ⟨exponentVector d, support_mem_newton hd⟩

theorem newton_lattice (p : MvPolynomial V R) : LatticePolytope (newtonPolytope p) := by
  classical
  refine ⟨p.support.image (fun d => fun v => (d v : ℤ)), ?_⟩
  unfold newtonPolytope
  congr 1
  ext x
  constructor
  · rintro ⟨d, hd, rfl⟩
    refine ⟨fun v => (d v : ℤ), mem_image.mpr ⟨d, hd, rfl⟩, ?_⟩
    funext v
    simp [exponentVector]
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨d, hd, rfl⟩ := mem_image.mp hy
    refine ⟨d, hd, ?_⟩
    funext v
    simp [exponentVector]

theorem newton_C {c : R} (hc : c ≠ 0) :
    newtonPolytope (MvPolynomial.C c : MvPolynomial V R) = {0} := by
  classical
  simp [newtonPolytope, MvPolynomial.support_C, hc]

theorem newton_map {S : Type*} [CommSemiring S] (f : R →+* S)
    (hf : Function.Injective f) (p : MvPolynomial V R) :
    newtonPolytope (MvPolynomial.map f p) = newtonPolytope p := by
  unfold newtonPolytope
  rw [MvPolynomial.support_map_of_injective p hf]

def subsetWeight (S : Finset V) : V → ℕ := fun v => if v ∈ S then 1 else 0

theorem subsetSum_exponentVector (d : V →₀ ℕ) (S : Finset V) :
    subsetSum (exponentVector d) S = (weight (subsetWeight S) d : ℝ) := by
  change subsetSum (exponentVector d) S =
    (weight (fun v => if v ∈ S then 1 else 0) d : ℝ)
  rw [weight_indicator]
  simp [subsetSum, exponentVector]

private theorem convex_subsetSum_ge (S : Finset V) (c : ℝ) :
    Convex ℝ {x : V → ℝ | c ≤ subsetSum x S} := by
  intro x hx y hy a b ha hb hab
  change c ≤ subsetSum (a • x + b • y) S
  rw [subsetSum_add, subsetSum_smul, subsetSum_smul]
  calc
    c = a * c + b * c := by rw [← add_mul, hab, one_mul]
    _ ≤ a * subsetSum x S + b * subsetSum y S :=
      add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)

private theorem convex_subsetSum_le (S : Finset V) (c : ℝ) :
    Convex ℝ {x : V → ℝ | subsetSum x S ≤ c} := by
  intro x hx y hy a b ha hb hab
  change subsetSum (a • x + b • y) S ≤ c
  rw [subsetSum_add, subsetSum_smul, subsetSum_smul]
  calc
    a * subsetSum x S + b * subsetSum y S ≤ a * c + b * c :=
      add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    _ = c := by rw [← add_mul, hab, one_mul]

theorem lower_weight_bound (p : MvPolynomial V R) (S : Finset V)
    {x : V → ℝ} (hx : x ∈ newtonPolytope p) :
    (minWeight (subsetWeight S) p : ℝ) ≤ subsetSum x S := by
  apply convexHull_min ?_ (convex_subsetSum_ge S _) hx
  rintro y ⟨d, hd, rfl⟩
  change (minWeight (subsetWeight S) p : ℝ) ≤ subsetSum (exponentVector d) S
  rw [subsetSum_exponentVector]
  exact_mod_cast minWeight_le_of_mem_support (subsetWeight S) hd

theorem upper_weight_bound (p : MvPolynomial V R) (S : Finset V)
    {x : V → ℝ} (hx : x ∈ newtonPolytope p) :
    subsetSum x S ≤ (maxWeight (subsetWeight S) p : ℝ) := by
  apply convexHull_min ?_ (convex_subsetSum_le S _) hx
  rintro y ⟨d, hd, rfl⟩
  change subsetSum (exponentVector d) S ≤ (maxWeight (subsetWeight S) p : ℝ)
  rw [subsetSum_exponentVector]
  exact_mod_cast weight_le_maxWeight_of_mem_support (subsetWeight S) hd

/-- The ordinary geometric lower support is exactly the smallest subset weight. -/
theorem lowerSupport_newton {p : MvPolynomial V R} (hp : p ≠ 0) (S : Finset V) :
    lowerSupport (newtonPolytope p) S = (minWeight (subsetWeight S) p : ℝ) := by
  obtain ⟨d, hd, hwd⟩ := exists_weight_eq_minWeight (subsetWeight S) hp
  have hleast : IsLeast ((fun x => subsetSum x S) '' newtonPolytope p)
      (minWeight (subsetWeight S) p : ℝ) := by
    refine ⟨⟨exponentVector d, support_mem_newton hd, ?_⟩, ?_⟩
    · change subsetSum (exponentVector d) S = (minWeight (subsetWeight S) p : ℝ)
      rw [subsetSum_exponentVector, hwd]
    · rintro _ ⟨x, hx, rfl⟩
      exact lower_weight_bound p S hx
  exact hleast.csInf_eq

theorem lowerSupport_newton_nonnegative {p : MvPolynomial V R} (hp : p ≠ 0)
    (S : Finset V) : 0 ≤ lowerSupport (newtonPolytope p) S := by
  rw [lowerSupport_newton hp S]
  exact Nat.cast_nonneg _

/-- The easy direction uses only support containment for multiplication. -/
theorem newton_product_subset_sum (p q : MvPolynomial V R) :
    newtonPolytope (p * q) ⊆ newtonPolytope p + newtonPolytope q := by
  apply convexHull_min ?_ ((newton_lattice p).convex.add (newton_lattice q).convex)
  rintro x ⟨d, hd, rfl⟩
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hd)
  rw [← hab, exponentVector_add]
  exact Set.add_mem_add (support_mem_newton ha) (support_mem_newton hb)

section Domain

variable [NoZeroDivisors R]

/-- Subset minima add even when coefficients of individual product monomials
cancel. The retained-monomial weight lift proves the needed noncancellation. -/
theorem lowerSupport_newton_mul {p q : MvPolynomial V R} (hp : p ≠ 0) (hq : q ≠ 0) :
    lowerSupport (newtonPolytope (p * q)) =
      lowerSupport (newtonPolytope p) + lowerSupport (newtonPolytope q) := by
  funext S
  simp only [Pi.add_apply, lowerSupport_newton (mul_ne_zero hp hq),
    lowerSupport_newton hp, lowerSupport_newton hq, minWeight_mul _ hp hq, Nat.cast_add]

/-- The actual Newton-product identity when the product polytope is a
supermodular base polytope. All lower facet inequalities and the total affine
hyperplane are proved from extremal polynomial support weights. -/
theorem newton_mul_of_basePolytope {p q : MvPolynomial V R} (hp : p ≠ 0) (hq : q ≠ 0)
    {z : SetFunction V} (hn : Normalized z) (hs : Supermodular z)
    (hnewt : newtonPolytope (p * q) = basePolytope z) :
    newtonPolytope p + newtonPolytope q = basePolytope z := by
  have hsum : lowerSupport (newtonPolytope p) + lowerSupport (newtonPolytope q) = z := by
    rw [← lowerSupport_newton_mul hp hq, hnewt, lowerSupport_basePolytope hn hs]
  have hmax : (maxWeight (subsetWeight univ) (p * q) : ℝ) = z univ := by
    obtain ⟨d, hd, hwd⟩ := exists_weight_eq_maxWeight (subsetWeight univ) (mul_ne_zero hp hq)
    have hmem := support_mem_newton hd
    rw [hnewt] at hmem
    have ht := hmem.1
    rw [subsetSum_exponentVector, hwd] at ht
    exact ht
  have hmaxsum : (maxWeight (subsetWeight univ) p : ℝ) +
      (maxWeight (subsetWeight univ) q : ℝ) = z univ := by
    rw [← Nat.cast_add, ← maxWeight_mul _ hp hq]
    exact hmax
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨x, hx, y, hy, rfl⟩
    have hlower : ∀ S, z S ≤ subsetSum (x + y) S := by
      intro S
      have he := congrFun hsum S
      change lowerSupport (newtonPolytope p) S + lowerSupport (newtonPolytope q) S = z S at he
      rw [← he, subsetSum_add]
      exact add_le_add (lowerSupport_le (newton_lattice p).compact hx S)
        (lowerSupport_le (newton_lattice q).compact hy S)
    refine ⟨le_antisymm ?_ (hlower univ), hlower⟩
    calc
      subsetSum (x + y) univ = subsetSum x univ + subsetSum y univ := subsetSum_add _ _ _
      _ ≤ (maxWeight (subsetWeight univ) p : ℝ) +
          (maxWeight (subsetWeight univ) q : ℝ) :=
        add_le_add (upper_weight_bound p univ hx) (upper_weight_bound q univ hy)
      _ = z univ := hmaxsum
  · rw [← hnewt]
    exact newton_product_subset_sum p q

end Domain

section Field

variable {K : Type*} [Field K]

theorem isUnit_of_newton_zero {p : MvPolynomial V K} (hp : p ≠ 0)
    (hnewt : newtonPolytope p = {0}) : IsUnit p := by
  have he : p = MvPolynomial.monomial 0 (p.coeff 0) := by
    apply MvPolynomial.eq_monomial_of_support_subset_singleton
    intro d hd
    have hd0 := support_mem_newton hd
    rw [hnewt, Set.mem_singleton_iff] at hd0
    ext v
    have hv := congrFun hd0 v
    change (d v : ℝ) = 0 at hv
    exact_mod_cast hv
  rw [← MvPolynomial.C_apply] at he
  have hc : p.coeff 0 ≠ 0 := by
    intro hc
    apply hp
    rw [he, hc, map_zero]
  rw [he]
  exact (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C

/-- A factorization of a normalized extreme base polytope with a unit slack
has a factor whose Newton polytope is the origin. -/
theorem factor_newton_zero_of_extreme_unit_slack {p q : MvPolynomial V K}
    (hp : p ≠ 0) (hq : q ≠ 0) {z : SetFunction V}
    (hz : ExtremeSupermodular z) {u v : V} {S : Finset V}
    (hδ : delta z u v S = 1)
    (hnewt : newtonPolytope (p * q) = basePolytope z) :
    newtonPolytope p = {0} ∨ newtonPolytope q = {0} := by
  let P := newtonPolytope p
  let Q := newtonPolytope q
  let f := lowerSupport P
  let g := lowerSupport Q
  have hP : IsCompact P := (newton_lattice p).compact
  have hQ : IsCompact Q := (newton_lattice q).compact
  have hnP : P.Nonempty := newton_nonempty hp
  have hnQ : Q.Nonempty := newton_nonempty hq
  have he : P + Q = basePolytope z := newton_mul_of_basePolytope hp hq hz.1.1 hz.2.1 hnewt
  have hes : Q + P = basePolytope z := by rw [add_comm]; exact he
  have hsum : f + g = z := by
    change lowerSupport P + lowerSupport Q = z
    rw [← lowerSupport_add hP hQ hnP hnQ, he, lowerSupport_basePolytope hz.1.1 hz.2.1]
  have hf0 : ∀ T, 0 ≤ f T := fun T => lowerSupport_newton_nonnegative hp T
  have hg0 : ∀ T, 0 ≤ g T := fun T => lowerSupport_newton_nonnegative hq T
  have hfn : TranslationNormalized f := by
    refine ⟨lowerSupport_normalized hP hnP, ?_⟩
    intro w
    have ht := congrFun hsum {w}
    change f {w} + g {w} = z {w} at ht
    rw [hz.1.2 w] at ht
    exact le_antisymm (by linarith [hg0 {w}]) (hf0 {w})
  have hgn : TranslationNormalized g := by
    refine ⟨lowerSupport_normalized hQ hnQ, ?_⟩
    intro w
    have ht := congrFun hsum {w}
    change f {w} + g {w} = z {w} at ht
    rw [hz.1.2 w] at ht
    exact le_antisymm (by linarith [hf0 {w}]) (hg0 {w})
  have hfs : Supermodular f :=
    summand_lowerSupport_supermodular hz.1.1 hz.2.1 hP hQ hnP hnQ he
  have hgs : Supermodular g :=
    summand_lowerSupport_supermodular hz.1.1 hz.2.1 hQ hP hnQ hnP hes
  have hfi : IntegerValued f := (newton_lattice p).lowerSupport_integerValued hnP
  have hgi : IntegerValued g := (newton_lattice q).lowerSupport_integerValued hnQ
  have hbodyP : P = basePolytope f :=
    summand_eq_basePolytope hz.1.1 hz.2.1 hP hQ (newton_lattice p).convex hnP hnQ he
  have hbodyQ : Q = basePolytope g :=
    summand_eq_basePolytope hz.1.1 hz.2.1 hQ hP (newton_lattice q).convex hnQ hnP hes
  obtain ⟨a, ha, hfa⟩ := hz.2.2.2 f g hfn hgn hfs hgs hsum
  obtain ⟨b, hb, hgb⟩ := hz.2.2.2 g f hgn hfn hgs hfs (by rw [add_comm]; exact hsum)
  have hdf : delta f u v S = a := by rw [hfa, delta_smul, hδ, mul_one]
  have hdg : delta g u v S = b := by rw [hgb, delta_smul, hδ, mul_one]
  by_cases ha0 : a = 0
  · left
    change P = {0}
    rw [hbodyP, hfa, ha0, zero_smul, basePolytope_zero]
  by_cases hb0 : b = 0
  · right
    change Q = {0}
    rw [hbodyQ, hgb, hb0, zero_smul, basePolytope_zero]
  have hdf1 := hfi.positive_delta_ge_one u v S
    (by rw [hdf]; exact lt_of_le_of_ne ha (Ne.symm ha0))
  have hdg1 := hgi.positive_delta_ge_one u v S
    (by rw [hdg]; exact lt_of_le_of_ne hb (Ne.symm hb0))
  have hdsum : delta f u v S + delta g u v S = 1 := by rw [← delta_add, hsum, hδ]
  exfalso
  linarith

/-- A general characteristic-independent criterion: an exact normalized
extreme Newton base polytope with one unit elemental slack forces irreducibility. -/
theorem irreducible_of_newton_base_extreme_unit_slack {p : MvPolynomial V K}
    {z : SetFunction V} (hz : ExtremeSupermodular z) {u v : V} {S : Finset V}
    (hδ : delta z u v S = 1) (hnewt : newtonPolytope p = basePolytope z) :
    Irreducible p := by
  have hp : p ≠ 0 := by
    intro hp0
    have hn := basePolytope_nonempty hz.1.1 hz.2.1
    rw [← hnewt, hp0, newton_zero] at hn
    exact Set.not_nonempty_empty hn
  constructor
  · intro hu
    obtain ⟨c, hc, rfl⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hu
    have hzero : basePolytope z = ({0} : Set (V → ℝ)) :=
      hnewt.symm.trans (newton_C hc.ne_zero)
    have hls := congrArg lowerSupport hzero
    rw [lowerSupport_basePolytope hz.1.1 hz.2.1] at hls
    apply hz.2.2.1
    calc
      z = lowerSupport ({0} : Set (V → ℝ)) := hls
      _ = 0 := by funext T; simp [lowerSupport, subsetSum]
  · intro a b hab
    have ha : a ≠ 0 := by intro ha0; apply hp; rw [hab, ha0, zero_mul]
    have hb : b ≠ 0 := by intro hb0; apply hp; rw [hab, hb0, mul_zero]
    have hn : newtonPolytope (a * b) = basePolytope z := by rw [← hab]; exact hnewt
    rcases factor_newton_zero_of_extreme_unit_slack ha hb hz hδ hn with ha0 | hb0
    · exact Or.inl (isUnit_of_newton_zero ha ha0)
    · exact Or.inr (isUnit_of_newton_zero hb hb0)

end Field

section Path

variable {K : Type*} [Field K]

/-- The ordinary irreducibility assertion for every polynomial with the
literal path Newton polytope, in every field and for every `n ≥ 4`. -/
theorem irreducible_of_newton_path {n : ℕ} (hn : 4 ≤ n)
    {p : MvPolynomial (Fin n) K} (hnewt : newtonPolytope p = Path.polytope n) :
    Irreducible p := by
  obtain ⟨S, _hu, _hv, hδ⟩ := Path.consecutive_positive_slack hn
    (⟨0, by omega⟩ : Fin (n - 1))
  exact irreducible_of_newton_base_extreme_unit_slack (Path.setFunction_extreme hn) hδ hnewt

/-- The conclusion persists under every field embedding, because scalar
extension preserves the entire exponent support. -/
theorem irreducible_map_of_newton_path {L : Type*} [Field L] (f : K →+* L)
    {n : ℕ} (hn : 4 ≤ n) {p : MvPolynomial (Fin n) K}
    (hnewt : newtonPolytope p = Path.polytope n) :
    Irreducible (MvPolynomial.map f p) := by
  apply irreducible_of_newton_path hn
  rw [newton_map f f.injective p, hnewt]

/-- Corollary A.3: every polynomial with exactly `Q_n` as its Newton polytope
is irreducible after extension to an algebraic closure. -/
theorem corollary_A_3_absoluteIrreducible {n : ℕ} (hn : 4 ≤ n)
    {p : MvPolynomial (Fin n) K} (hnewt : newtonPolytope p = Path.polytope n) :
    Irreducible (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) p) :=
  irreducible_map_of_newton_path (algebraMap K (AlgebraicClosure K)) hn hnewt

end Path

end GraphicalZonotopes.NewtonGeometry
