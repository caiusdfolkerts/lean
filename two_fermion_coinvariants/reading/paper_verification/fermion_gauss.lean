module

public import PaperVerification.FermionExterior
public import PaperVerification.FermionGaussDividedPowers
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Ring

/-!
# The algebraic diagonal Gauss factorization

These are the finite operator identities needed for a direct proof of the diagonal
case of Lemma 3.1. It is proved for the actual creation and contraction
operators, without diagonalization, characteristic-zero specialization, or
Zariski density. The first-order rank-one identity and the equal-degree projection
remain separate obligations; this file does not claim the prefix bound.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion

open scoped BigOperators

section AbstractPair

variable {B : Type*} [Ring B]

/-- Anticommuting square-zero factors give a square-zero pair operator. -/
theorem pair_square_of_anticomm (a b : B)
    (hab : a * b = -(b * a)) (ha : a * a = 0) :
    (b * a) * (b * a) = 0 := by
  calc
    (b * a) * (b * a) = b * (a * b) * a := by noncomm_ring
    _ = b * (-(b * a)) * a := by rw [hab]
    _ = -((b * b) * (a * a)) := by noncomm_ring
    _ = 0 := by rw [ha, mul_zero, neg_zero]

end AbstractPair

namespace Exterior

variable {R V I : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [Fintype I] [DecidableEq I]

local notation "E" => ExteriorAlgebra R V

variable (b : Module.Basis (I ⊕ I) R V)

@[simp]
theorem pairLower_square (i : I) : pairLower b i * pairLower b i = 0 :=
  pair_square_of_anticomm _ _ (annihilation_anticomm_eq _ _) (annihilation_square _)

@[simp]
theorem pairRaise_square (i : I) : pairRaise b i * pairRaise b i = 0 :=
  pair_square_of_anticomm _ _ (creation_anticomm_eq _ _) (creation_square _)

/-- Each paired contraction is a generalized inverse of its paired creation. -/
theorem pairLower_pairRaise_pairLower (i : I) :
    pairLower b i * (pairRaise b i * pairLower b i) = pairLower b i := by
  let a : Module.End R E := annihilation (b.coord (.inl i))
  let d : Module.End R E := annihilation (b.coord (.inr i))
  let c : Module.End R E := creation (b (.inl i))
  let f : Module.End R E := creation (b (.inr i))
  have ha : a * a = 0 := annihilation_square _
  have hd : d * d = 0 := annihilation_square _
  have had : a * d = -(d * a) := annihilation_anticomm_eq _ _
  have hleft : (c * a) * (d * a) = 0 := by
    calc
      (c * a) * (d * a) = c * (a * d) * a := by noncomm_ring
      _ = c * (-(d * a)) * a := by rw [had]
      _ = -((c * d) * (a * a)) := by
        apply LinearMap.ext
        intro z
        simp only [Module.End.mul_apply, LinearMap.neg_apply, map_neg]
      _ = 0 := by rw [ha, mul_zero, neg_zero]
  have hright : (f * d) * (d * a) = 0 := by
    calc
      (f * d) * (d * a) = f * (d * d) * a := by noncomm_ring
      _ = 0 := by rw [hd, mul_zero, zero_mul]
  have hcomm : pairLower b i * pairRaise b i =
      pairRaise b i * pairLower b i + (1 - c * a - f * d) := by
    exact pair_operator_commutator a d c f
      (by simpa [a, c] using annihilation_creation (b.coord (.inl i)) (b (.inl i)))
      (by simpa [d, f] using annihilation_creation (b.coord (.inr i)) (b (.inr i)))
      (by simpa [a, f] using annihilation_creation (b.coord (.inl i)) (b (.inr i)))
      (by simpa [d, c] using annihilation_creation (b.coord (.inr i)) (b (.inl i)))
  have hleft' : (c * a) * pairLower b i = 0 := hleft
  have hright' : (f * d) * pairLower b i = 0 := hright
  calc
    pairLower b i * (pairRaise b i * pairLower b i) =
        (pairLower b i * pairRaise b i) * pairLower b i := by rw [mul_assoc]
    _ = (pairRaise b i * pairLower b i + (1 - c * a - f * d)) * pairLower b i := by
      rw [hcomm]
    _ = pairLower b i := by
      rw [add_mul, sub_mul, sub_mul, one_mul, mul_assoc, pairLower_square,
        mul_zero, hleft', hright', zero_add, sub_zero, sub_zero]

/-- Each paired creation is a generalized inverse of its paired contraction. -/
theorem pairRaise_pairLower_pairRaise (i : I) :
    pairRaise b i * (pairLower b i * pairRaise b i) = pairRaise b i := by
  let a : Module.End R E := annihilation (b.coord (.inl i))
  let d : Module.End R E := annihilation (b.coord (.inr i))
  let c : Module.End R E := creation (b (.inl i))
  let f : Module.End R E := creation (b (.inr i))
  have hc : c * c = 0 := creation_square _
  have hf : f * f = 0 := creation_square _
  have hfc : f * c = -(c * f) := creation_anticomm_eq _ _
  have hleft : (c * f) * (c * a) = 0 := by
    calc
      (c * f) * (c * a) = c * (f * c) * a := by noncomm_ring
      _ = c * (-(c * f)) * a := by rw [hfc]
      _ = -((c * c) * (f * a)) := by
        apply LinearMap.ext
        intro z
        simp only [Module.End.mul_apply, LinearMap.neg_apply, map_neg]
      _ = 0 := by rw [hc, zero_mul, neg_zero]
  have hright : (c * f) * (f * d) = 0 := by
    calc
      (c * f) * (f * d) = c * (f * f) * d := by noncomm_ring
      _ = 0 := by rw [hf, mul_zero, zero_mul]
  have hcomm : pairLower b i * pairRaise b i =
      pairRaise b i * pairLower b i + (1 - c * a - f * d) := by
    exact pair_operator_commutator a d c f
      (by simpa [a, c] using annihilation_creation (b.coord (.inl i)) (b (.inl i)))
      (by simpa [d, f] using annihilation_creation (b.coord (.inr i)) (b (.inr i)))
      (by simpa [a, f] using annihilation_creation (b.coord (.inl i)) (b (.inr i)))
      (by simpa [d, c] using annihilation_creation (b.coord (.inr i)) (b (.inl i)))
  have hleft' : pairRaise b i * (c * a) = 0 := hleft
  have hright' : pairRaise b i * (f * d) = 0 := hright
  have hff : pairRaise b i * (pairRaise b i * pairLower b i) = 0 := by
    rw [← mul_assoc, pairRaise_square, zero_mul]
  rw [hcomm, mul_add, mul_sub, mul_sub, mul_one, hff, hleft', hright',
    zero_add, sub_zero, sub_zero]

end Exterior

section Gauss

variable {R B : Type*} [CommRing R] [Ring B] [Algebra R B]

/-- The one-pair diagonal operator: on vacuum, occupied pair and single modes
its eigenvalues are respectively `1+a*b`, `c`, and `1`, when `c*(1+a*b)=1`. -/
def pairGaussDiagonal (a b c : R) (e f : B) : B :=
  1 + (a * b) • (e * f) - (a * b * c) • (f * e)

/-- The exact Gauss factorization for a pair of square-zero generalized inverses.
All scalar coefficients are central because the ambient ring is an `R`-algebra. -/
theorem pair_gauss_factorization (a b c : R) (e f : B)
    (he : e * e = 0) (hf : f * f = 0)
    (hef : e * (f * e) = e) (hfe : f * (e * f) = f)
    (hc : c * (1 + a * b) = 1) :
    (1 + a • e) * (1 + b • f) =
      (1 + (b * c) • f) * pairGaussDiagonal a b c e f * (1 + (a * c) • e) := by
  have hffe : f * (f * e) = 0 := by rw [← mul_assoc, hf, zero_mul]
  have hFD : f * pairGaussDiagonal a b c e f = (1 + a * b) • f := by
    simp only [pairGaussDiagonal, mul_sub, mul_add, mul_one, mul_smul_comm,
      hfe, hffe, smul_zero, sub_zero]
    rw [add_smul,one_smul]
  have hright : pairGaussDiagonal a b c e f * (1 + (a * c) • e) =
      pairGaussDiagonal a b c e f + a • e := by
    have hac : a * c + a * b * (a * c) = a := by
      calc
        a * c + a * b * (a * c) = a * (c * (1 + a * b)) := by ring
        _ = a := by rw [hc, mul_one]
    calc
      pairGaussDiagonal a b c e f * (1 + (a * c) • e) =
          pairGaussDiagonal a b c e f + (a * c + a * b * (a * c)) • e := by
        simp only [pairGaussDiagonal, mul_add, sub_mul, add_mul, mul_one,
          one_mul, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc, he,
          hef, mul_zero, smul_zero, sub_zero,smul_add,smul_smul,add_smul,mul_comm]
      _ = _ := by rw [hac]
  have hbc : b * c * (1 + a * b) = b := by rw [mul_assoc, hc, mul_one]
  symm
  calc
    (1 + (b * c) • f) * pairGaussDiagonal a b c e f * (1 + (a * c) • e) =
        pairGaussDiagonal a b c e f + a • e +
          (b * c * (1 + a * b)) • f + (a * b * c) • (f * e) := by
      rw [mul_assoc, hright]
      simp only [add_mul, one_mul, mul_add, smul_mul_assoc, mul_smul_comm,
        hFD, smul_smul,smul_add,mul_assoc]
      abel
    _ = 1 + a • e + b • f + (a * b) • (e * f) := by
      rw [hbc]
      unfold pairGaussDiagonal
      abel
    _ = (1 + a • e) * (1 + b • f) := by
      simp only [mul_add, add_mul, one_mul, mul_one, smul_mul_assoc,
        mul_smul_comm, smul_smul,smul_add,mul_comm]
      abel

/-- The factorization for the literal exterior pair operators, over every
commutative coefficient ring and every number of pairs. -/
theorem exterior_pair_gauss_factorization
    {V I : Type*} [AddCommGroup V] [Module R V] [Fintype I] [DecidableEq I]
    (basis : Module.Basis (I ⊕ I) R V) (i : I) (a b c : R)
    (hc : c * (1 + a * b) = 1) :
    (1 + a • Exterior.pairLower basis i) * (1 + b • Exterior.pairRaise basis i) =
      (1 + (b * c) • Exterior.pairRaise basis i) *
        pairGaussDiagonal a b c (Exterior.pairLower basis i) (Exterior.pairRaise basis i) *
          (1 + (a * c) • Exterior.pairLower basis i) :=
  pair_gauss_factorization a b c _ _
    (Exterior.pairLower_square basis i) (Exterior.pairRaise_square basis i)
    (Exterior.pairLower_pairRaise_pairLower basis i)
    (Exterior.pairRaise_pairLower_pairRaise basis i) hc

end Gauss


section OrderedProducts

variable {B J : Type*} [Monoid B]

/-- Reorder two products when factors at distinct indices commute. The list
retains its order, so no commutativity of the ambient algebra is assumed. -/
theorem list_prod_mul_of_cross_commute (l : List J) (hl : l.Nodup)
    (f g : J → B) (h : ∀ i ∈ l, ∀ j ∈ l, i ≠ j → Commute (g i) (f j)) :
    (l.map f).prod * (l.map g).prod = (l.map (fun i ↦ f i * g i)).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
      have hnodup := List.nodup_cons.mp hl
      have htail : ∀ a ∈ l, ∀ c ∈ l, a ≠ c → Commute (g a) (f c) := by
        intro a ha c hc hac
        exact h a (List.mem_cons_of_mem i ha) c (List.mem_cons_of_mem i hc) hac
      have hcomm : Commute (g i) (l.map f).prod := by
        apply Commute.list_prod_right
        intro x hx
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
        exact h i (List.mem_cons_self) j (List.mem_cons_of_mem i hj)
          (fun hij ↦ hnodup.1 (hij.symm ▸ hj))
      rw [List.map_cons, List.map_cons, List.map_cons, List.prod_cons,
        List.prod_cons, List.prod_cons, ← ih hnodup.2 htail]
      calc
        (f i * (l.map f).prod) * (g i * (l.map g).prod) =
            f i * ((l.map f).prod * g i) * (l.map g).prod := by simp only [mul_assoc]
        _ = f i * (g i * (l.map f).prod) * (l.map g).prod := by rw [hcomm.eq]
        _ = (f i * g i) * ((l.map f).prod * (l.map g).prod) := by simp only [mul_assoc]

end OrderedProducts

section CommutingPairs

variable {R B J : Type*} [CommRing R] [Ring B] [Algebra R B]

 theorem commute_smul_left_of_commute {x y : B} (h : Commute x y) (a : R) :
    Commute (a • x) y := by
  change (a • x) * y = y * (a • x)
  rw [smul_mul_assoc, mul_smul_comm, h.eq]

 theorem commute_smul_right_of_commute {x y : B} (h : Commute x y) (a : R) :
    Commute x (a • y) :=
  (commute_smul_left_of_commute h.symm a).symm

 theorem commute_one_add_smul_left {x y : B} (h : Commute x y) (a : R) :
    Commute (1 + a • x) y :=
  (Commute.one_left y).add_left (commute_smul_left_of_commute h a)

 theorem commute_one_add_smul_right {x y : B} (h : Commute x y) (a : R) :
    Commute x (1 + a • y) :=
  (commute_one_add_smul_left h.symm a).symm

 theorem commute_one_add_smul {x y : B} (h : Commute x y) (a b : R) :
    Commute (1 + a • x) (1 + b • y) :=
  commute_one_add_smul_right (commute_one_add_smul_left h a) b

 theorem commute_pairGaussDiagonal {e f x : B} (he : Commute e x)
    (hf : Commute f x) (a b c : R) :
    Commute (pairGaussDiagonal a b c e f) x :=
  ((Commute.one_left x).add_left
    (commute_smul_left_of_commute (he.mul_left hf) (a * b))).sub_left
      (commute_smul_left_of_commute (hf.mul_left he) (a * b * c))

/-- Gauss factorization for every finite number of commuting pairs. This
identity already has the three ordered factors of Lemma 3.1; it uses only
one-pair relations and commutation at distinct indices. -/
theorem commuting_pairs_gauss_factorization (l : List J) (hl : l.Nodup)
    (a b c : J → R) (e f : J → B)
    (he : ∀ i, e i * e i = 0) (hf : ∀ i, f i * f i = 0)
    (hef : ∀ i, e i * (f i * e i) = e i)
    (hfe : ∀ i, f i * (e i * f i) = f i)
    (hc : ∀ i, c i * (1 + a i * b i) = 1)
    (hcross : ∀ i j, i ≠ j →
      Commute (e i) (e j) ∧ Commute (e i) (f j) ∧
        Commute (f i) (e j) ∧ Commute (f i) (f j)) :
    (l.map (fun i ↦ 1 + a i • e i)).prod *
      (l.map (fun i ↦ 1 + b i • f i)).prod =
    (l.map (fun i ↦ 1 + (b i * c i) • f i)).prod *
      (l.map (fun i ↦ pairGaussDiagonal (a i) (b i) (c i) (e i) (f i))).prod *
        (l.map (fun i ↦ 1 + (a i * c i) • e i)).prod := by
  let D : J → B := fun i ↦ pairGaussDiagonal (a i) (b i) (c i) (e i) (f i)
  let U : J → B := fun i ↦ 1 + (b i * c i) • f i
  let L : J → B := fun i ↦ 1 + (a i * c i) • e i
  have hUD : (l.map U).prod * (l.map D).prod =
      (l.map (fun i ↦ U i * D i)).prod := by
    apply list_prod_mul_of_cross_commute l hl
    intro i hi j hj hij
    exact commute_one_add_smul_right
      (commute_pairGaussDiagonal (hcross i j hij).2.1 (hcross i j hij).2.2.2
        (a i) (b i) (c i)) _
  have hUDL : (l.map (fun i ↦ U i * D i)).prod * (l.map L).prod =
      (l.map (fun i ↦ (U i * D i) * L i)).prod := by
    apply list_prod_mul_of_cross_commute l hl
    intro i hi j hj hij
    apply Commute.mul_right
    · exact commute_one_add_smul (hcross i j hij).2.1 _ _
    · exact (commute_one_add_smul_right
        (commute_pairGaussDiagonal (hcross j i hij.symm).1 (hcross j i hij.symm).2.2.1
          (a j) (b j) (c j)) _).symm
  calc
    _ = (l.map (fun i ↦ (1 + a i • e i) * (1 + b i • f i))).prod := by
      apply list_prod_mul_of_cross_commute l hl
      intro i hi j hj hij
      exact commute_one_add_smul (hcross i j hij).2.2.1 _ _
    _ = (l.map (fun i ↦ (U i * D i) * L i)).prod := by
      congr 1
      apply List.map_congr_left
      intro i hi
      exact pair_gauss_factorization (a i) (b i) (c i) (e i) (f i)
        (he i) (hf i) (hef i) (hfe i) (hc i)
    _ = _ := by rw [← hUDL, ← hUD]

end CommutingPairs


section ScalarProducts

variable {R B J W : Type*} [CommRing R] [Ring B] [Algebra R B]
    [AddCommGroup W] [Module R W]

 theorem list_prod_smul_factors (l : List J) (a : J → R) (f : J → B) :
    (l.map (fun i ↦ a i • f i)).prod = (l.map a).prod • (l.map f).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
      simp only [List.map_cons, List.prod_cons, ih, smul_mul_assoc,
        mul_smul_comm, smul_smul]
      rw [mul_comm]

 theorem list_prod_apply_eigenvector (l : List J) (f : J → Module.End R W)
    (a : J → R) (w : W) (h : ∀ i ∈ l, f i w = a i • w) :
    (l.map f).prod w = (l.map a).prod • w := by
  induction l with
  | nil => simp
  | cons i l ih =>
      rw [List.map_cons, List.prod_cons, Module.End.mul_apply,
        ih (fun j hj ↦ h j (List.mem_cons_of_mem i hj)), map_smul,
        h i (List.mem_cons_self), List.map_cons, List.prod_cons, smul_smul]
      rw [mul_comm]

end ScalarProducts

namespace Exterior

variable {R V I : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [Fintype I] [DecidableEq I]

variable (b : Module.Basis (I ⊕ I) R V)

 theorem pairLower_commute (i j : I) : Commute (pairLower b i) (pairLower b j) := by
  have h (l m : Module.Dual R V) :
      annihilation l * annihilation m + annihilation m * annihilation l = 0 := by
    rw [annihilation_anticomm_eq]
    exact neg_add_cancel _
  exact disjoint_pair_operators_commute _ _ _ _ (h _ _) (h _ _) (h _ _) (h _ _)

 theorem pairRaise_commute (i j : I) : Commute (pairRaise b i) (pairRaise b j) :=
  disjoint_pair_operators_commute _ _ _ _
    (creation_anticomm _ _) (creation_anticomm _ _) (creation_anticomm _ _) (creation_anticomm _ _)

 theorem pairLower_pairRaise_commute (i j : I) (hij : i ≠ j) :
    Commute (pairLower b i) (pairRaise b j) := by
  apply sub_eq_zero.mp
  simpa only [if_neg hij] using pair_commutator b i j

/-- The exact diagonal Gauss factorization for all actual exterior pairs.
There is no restriction on the number of pairs or on their scalar parameters. -/
theorem diagonal_gauss_product (l : List I) (hl : l.Nodup)
    (a c d : I → R) (hd : ∀ i, d i * (1 + a i * c i) = 1) :
    (l.map (fun i ↦ 1 + a i • pairLower b i)).prod *
      (l.map (fun i ↦ 1 + c i • pairRaise b i)).prod =
    (l.map (fun i ↦ 1 + (c i * d i) • pairRaise b i)).prod *
      (l.map (fun i ↦ pairGaussDiagonal (a i) (c i) (d i)
        (pairLower b i) (pairRaise b i))).prod *
      (l.map (fun i ↦ 1 + (a i * d i) • pairLower b i)).prod := by
  apply commuting_pairs_gauss_factorization l hl a c d _ _
    (pairLower_square b) (pairRaise_square b)
    (pairLower_pairRaise_pairLower b) (pairRaise_pairLower_pairRaise b) hd
  intro i j hij
  exact ⟨pairLower_commute b i j, pairLower_pairRaise_commute b i j hij,
    (pairLower_pairRaise_commute b j i hij.symm).symm, pairRaise_commute b i j⟩


/-- The coordinate occupation projection. -/
def occupation (j : I ⊕ I) : Module.End R (ExteriorAlgebra R V) :=
  creation (b j) * annihilation (b.coord j)

 theorem occupation_basis [LinearOrder (I ⊕ I)] (j : I ⊕ I) (s : Finset (I ⊕ I)) :
    occupation b j (b.ExteriorAlgebra s) =
      if j ∈ s then b.ExteriorAlgebra s else 0 :=
  by
    by_cases hj : j ∈ s
    · simpa only [occupation, Module.End.mul_apply, creation_apply, annihilation, if_pos hj] using
        TauCeti.ExteriorAlgebra.ι_mul_contractLeft_coord_basis b j s
    · simpa only [occupation, Module.End.mul_apply, creation_apply, annihilation, if_neg hj] using
        TauCeti.ExteriorAlgebra.ι_mul_contractLeft_coord_basis b j s

 theorem occupation_pair (i : I) :
    occupation b (.inl i) * occupation b (.inr i) = pairRaise b i * pairLower b i := by
  let a : Module.End R (ExteriorAlgebra R V) := annihilation (b.coord (.inl i))
  let d : Module.End R (ExteriorAlgebra R V) := annihilation (b.coord (.inr i))
  let c : Module.End R (ExteriorAlgebra R V) := creation (b (.inl i))
  let f : Module.End R (ExteriorAlgebra R V) := creation (b (.inr i))
  have hcross : a * f = -(f * a) := by
    apply eq_neg_of_add_eq_zero_left
    simpa [a, f] using annihilation_creation (b.coord (.inl i)) (b (.inr i))
  have had : a * d = -(d * a) := annihilation_anticomm_eq _ _
  change (c * a) * (f * d) = (c * f) * (d * a)
  calc
    (c * a) * (f * d) = c * (a * f) * d := by noncomm_ring
    _ = c * (-(f * a)) * d := by rw [hcross]
    _ = -((c * f) * (a * d)) := by
      apply LinearMap.ext
      intro z
      simp only [Module.End.mul_apply, LinearMap.neg_apply, map_neg]
    _ = -((c * f) * (-(d * a))) := by rw [had]
    _ = (c * f) * (d * a) := by
      apply LinearMap.ext
      intro z
      simp only [Module.End.mul_apply, LinearMap.neg_apply, map_neg, neg_neg]

 theorem pairRaise_pairLower_basis [LinearOrder (I ⊕ I)] (i : I)
    (s : Finset (I ⊕ I)) :
    (pairRaise b i * pairLower b i) (b.ExteriorAlgebra s) =
      if Sum.inl i ∈ s ∧ Sum.inr i ∈ s then b.ExteriorAlgebra s else 0 := by
  rw [← occupation_pair, Module.End.mul_apply, occupation_basis]
  by_cases hξ : Sum.inr i ∈ s
  · simp only [if_pos hξ, if_true, occupation_basis, hξ, and_true]
  · simp only [if_neg hξ, map_zero, hξ, and_false, if_false]

 theorem pairLower_pairRaise_basis [LinearOrder (I ⊕ I)] (i : I)
    (s : Finset (I ⊕ I)) :
    (pairLower b i * pairRaise b i) (b.ExteriorAlgebra s) =
      if Sum.inl i ∉ s ∧ Sum.inr i ∉ s then b.ExteriorAlgebra s else 0 := by
  have hcomm : pairLower b i * pairRaise b i =
      pairRaise b i * pairLower b i + (1 - occupation b (.inl i) - occupation b (.inr i)) := by
    exact pair_operator_commutator _ _ _ _
      (by simpa using annihilation_creation (b.coord (.inl i)) (b (.inl i)))
      (by simpa using annihilation_creation (b.coord (.inr i)) (b (.inr i)))
      (by simpa using annihilation_creation (b.coord (.inl i)) (b (.inr i)))
      (by simpa using annihilation_creation (b.coord (.inr i)) (b (.inl i)))
  rw [hcomm]
  simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.one_apply,
    occupation_basis, pairRaise_pairLower_basis]
  by_cases hθ : Sum.inl i ∈ s <;> by_cases hξ : Sum.inr i ∈ s <;>
    simp only [hθ, hξ, and_self, and_false, false_and, not_true_eq_false,
      not_false_eq_true, if_true, if_false] <;> abel

/-- The diagonal factor has exactly the determinant-times-inverse eigenvalue
in each of the four one-pair occupation states. -/
theorem pairGaussDiagonal_basis [LinearOrder (I ⊕ I)] (i : I)
    (s : Finset (I ⊕ I)) (a c d : R) (hd : d * (1 + a * c) = 1) :
    pairGaussDiagonal a c d (pairLower b i) (pairRaise b i) (b.ExteriorAlgebra s) =
      (if Sum.inl i ∈ s ∧ Sum.inr i ∈ s then d
       else if Sum.inl i ∉ s ∧ Sum.inr i ∉ s then 1 + a * c else 1) •
        b.ExteriorAlgebra s := by
  have hd' : 1 - a * c * d = d := by
    calc
      1 - a * c * d = d * (1 + a * c) - a * c * d := by rw [hd]
      _ = d := by ring
  simp only [pairGaussDiagonal, LinearMap.sub_apply, LinearMap.add_apply,
    Module.End.one_apply, LinearMap.smul_apply, pairLower_pairRaise_basis,
    pairRaise_pairLower_basis]
  by_cases hθ : Sum.inl i ∈ s <;> by_cases hξ : Sum.inr i ∈ s <;>
    simp only [hθ, hξ, and_self, and_false, false_and, not_true_eq_false,
      not_false_eq_true, if_true, if_false, smul_zero, add_zero, sub_zero]
  · simpa only [sub_smul, one_smul] using
      congrArg (fun r : R ↦ r • b.ExteriorAlgebra s) hd'
  · exact (one_smul R _).symm
  · exact (one_smul R _).symm
  · rw [add_smul, one_smul]


/-- The literal linear substitution multiplying both colors at each index
by a specified scalar. Its exterior-algebra map is the diagonal `Γ` action. -/
def modeScaling (c : I → R) : V →ₗ[R] V :=
  b.constr R fun j ↦ (Sum.elim c c j) • b j

@[simp] theorem modeScaling_basis (c : I → R) (j : I ⊕ I) :
    modeScaling b c (b j) = (Sum.elim c c j) • b j :=
  b.constr_basis R _ j

/-- The actual exterior substitution acts on each wedge basis vector by
multiplication with the product of its selected diagonal entries. -/
theorem exterior_modeScaling_basis [LinearOrder (I ⊕ I)] (c : I → R)
    (s : Finset (I ⊕ I)) :
    ExteriorAlgebra.map (modeScaling b c) (b.ExteriorAlgebra s) =
      (∏ j ∈ s, Sum.elim c c j) • b.ExteriorAlgebra s := by
  rw [Module.Basis.exteriorAlgebra_eq_prod_map_sort, map_list_prod]
  simp only [List.map_map, Function.comp_def, ExteriorAlgebra.map_apply_ι,
    modeScaling_basis, map_smul]
  rw [list_prod_smul_factors]
  congr 1
  simpa only [Finset.sort_toFinset] using
    (List.prod_toFinset (Sum.elim c c) (s.sort_nodup (· ≤ ·))).symm

/-- The product of all one-pair diagonal factors is exactly the determinant
factor times the literal exterior substitution. -/
theorem diagonalProduct_eq_modeScaling [LinearOrder (I ⊕ I)]
    (a c d : I → R) (hd : ∀ i, d i * (1 + a i * c i) = 1) :
    (Finset.univ.toList.map (fun i ↦ pairGaussDiagonal (a i) (c i) (d i)
      (pairLower b i) (pairRaise b i))).prod =
      (∏ i, (1 + a i * c i)) • (ExteriorAlgebra.map (modeScaling b d)).toLinearMap := by
  apply b.ExteriorAlgebra.ext
  intro s
  let eigenvalue : I → R := fun i ↦
    if Sum.inl i ∈ s ∧ Sum.inr i ∈ s then d i
    else if Sum.inl i ∉ s ∧ Sum.inr i ∉ s then 1 + a i * c i else 1
  have heigen := list_prod_apply_eigenvector Finset.univ.toList
    (fun i ↦ pairGaussDiagonal (a i) (c i) (d i) (pairLower b i) (pairRaise b i))
    eigenvalue (b.ExteriorAlgebra s) (fun i _ ↦ pairGaussDiagonal_basis b i s (a i) (c i) (d i) (hd i))
  rw [heigen, LinearMap.smul_apply, AlgHom.toLinearMap_apply, exterior_modeScaling_basis,
    smul_smul, Finset.prod_map_toList]
  congr 1
  have hfactor (i : I) : eigenvalue i = (1 + a i * c i) *
      (if Sum.inl i ∈ s then d i else 1) * (if Sum.inr i ∈ s then d i else 1) := by
    have hd' : (1 + a i * c i) * d i = 1 := by rw [mul_comm]; exact hd i
    by_cases hθ : Sum.inl i ∈ s <;> by_cases hξ : Sum.inr i ∈ s <;>
      simp [eigenvalue, hθ, hξ, hd']
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, mul_assoc]
  congr 1
  rw [← Finset.prod_ite_mem_eq s (Sum.elim d d), Fintype.prod_sum_type]
  rfl

/-- Coordinate contraction pulls back through the diagonal substitution by
the same diagonal scalar. -/
theorem coord_modeScaling (d : I → R) (j : I ⊕ I) :
    (b.coord j).comp (modeScaling b d) = (Sum.elim d d j) • b.coord j := by
  apply b.ext
  intro i
  by_cases hij : i = j
  · subst i
    simp [modeScaling_basis, Module.Basis.coord_apply]
  · simp [modeScaling_basis, Module.Basis.coord_apply, Finsupp.single_eq_of_ne hij,
      Finsupp.single_eq_of_ne (Ne.symm hij)]

/-- Naturality of contraction gives the exact intertwiner for the full
Gauss diagonal, with its scalar determinant factor retained. -/
theorem annihilation_diagonalProduct [LinearOrder (I ⊕ I)]
    (a c d : I → R) (hd : ∀ i, d i * (1 + a i * c i) = 1)
    (l : Module.Dual R V) (w : ExteriorAlgebra R V) :
    annihilation l
      ((Finset.univ.toList.map (fun i ↦ pairGaussDiagonal (a i) (c i) (d i)
        (pairLower b i) (pairRaise b i))).prod w) =
      (∏ i, (1 + a i * c i)) •
        ExteriorAlgebra.map (modeScaling b d)
          (annihilation (l.comp (modeScaling b d)) w) := by
  rw [diagonalProduct_eq_modeScaling b a c d hd, LinearMap.smul_apply,
    AlgHom.toLinearMap_apply, map_smul]
  congr 1
  exact ExteriorAlgebra.contractLeft_map (modeScaling b d) l w

end Exterior

section NilpotentInverse

variable {R : Type*} [CommRing R]

/-- The inverse of `1+u*v*y` when `y` has the specified nilpotence bound. -/
def gaussNilpotentInverse (u v y : R) (N : ℕ) : R :=
  ∑ k ∈ Finset.range N, ((-u * v) * y) ^ k

/-- The same inverse identity only requires nilpotence of the parameter-times-
coordinate product. This applies in every truncated polynomial or power-series
ring, even when the coordinate itself is not nilpotent. -/
theorem gaussNilpotentInverse_mul_of_product_pow_eq_zero
    (u v y : R) (N : ℕ) (hy : ((-u * v) * y) ^ N = 0) :
    gaussNilpotentInverse u v y N * (1 + u * y * v) = 1 := by
  calc
    _ = (∑ k ∈ Finset.range N, ((-u * v) * y) ^ k) * (1 - (-u * v) * y) := by
      unfold gaussNilpotentInverse
      congr 1
      ring
    _ = 1 - ((-u * v) * y) ^ N := geom_sum_mul_neg _ _
    _ = 1 := by rw [hy, sub_zero]

 theorem gaussNilpotentInverse_mul (u v y : R) (N : ℕ) (hy : y ^ N = 0) :
    gaussNilpotentInverse u v y N * (1 + u * y * v) = 1 := by
  calc
    _ = (∑ k ∈ Finset.range N, ((-u * v) * y) ^ k) * (1 - (-u * v) * y) := by
      unfold gaussNilpotentInverse
      congr 1
      ring
    _ = 1 - ((-u * v) * y) ^ N := geom_sum_mul_neg _ _
    _ = 1 := by rw [mul_pow, hy, mul_zero, sub_zero]

/-- The finite inverse polynomial, common to all diagonal coordinates. -/
def gaussInversePolynomial (u v : R) (N : ℕ) : Polynomial R :=
  ∑ k ∈ Finset.range N, (Polynomial.C (-u * v) * Polynomial.X) ^ k

 theorem gaussInversePolynomial_eval (u v y : R) (N : ℕ) :
    (gaussInversePolynomial u v N).eval y = gaussNilpotentInverse u v y N := by
  simp only [gaussInversePolynomial, gaussNilpotentInverse, Polynomial.eval_finsetSum,
    Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]

/-- One common polynomial realizes every weighted inverse coefficient in the
last factor of the diagonal Gauss product. -/
def gaussAnnihilatorPolynomial (u v : R) (N : ℕ) : Polynomial R :=
  Polynomial.C u * Polynomial.X *
    ∑ k ∈ Finset.range N, (Polynomial.C (-u * v) * Polynomial.X) ^ k

 theorem gaussAnnihilatorPolynomial_eval (u v y : R) (N : ℕ) :
    (gaussAnnihilatorPolynomial u v N).eval y =
      u * y * gaussNilpotentInverse u v y N := by
  simp only [gaussAnnihilatorPolynomial, gaussNilpotentInverse,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_finsetSum, Polynomial.eval_pow]

end NilpotentInverse

namespace Exterior

variable {R V I : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [Fintype I] [DecidableEq I]

variable (b : Module.Basis (I ⊕ I) R V)

/-- The last factor of the actual diagonal Gauss product fixes every vector
killed by all mixed polynomial currents. The inverse coefficients are the
explicit finite geometric sums; no formal inverse is postulated. -/
theorem diagonal_gauss_right_fixes
    (y : I → R) (u v : R) (N : ℕ)
    (hfac : IsUnit ((Fintype.card I).factorial : R))
    (w : ExteriorAlgebra R V)
    (hw : ∀ p : Polynomial R, (∑ i, p.eval (y i) • pairLower b i) w = 0) :
    ((Finset.univ.toList.map fun i ↦
      1 + (u * y i * gaussNilpotentInverse u v (y i) N) • pairLower b i).prod) w = w := by
  let a : I → Module.End R (ExteriorAlgebra R V) := fun i ↦
    (u * y i * gaussNilpotentInverse u v (y i) N) • pairLower b i
  let l := Finset.univ.toList.map a
  have hsq : ∀ f ∈ l, f * f = 0 := by
    intro f hf
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hf
    simp only [a, smul_mul_assoc, mul_smul_comm, smul_smul, pairLower_square, smul_zero]
  have hcomm : ∀ f ∈ l, ∀ g ∈ l, Commute f g := by
    intro f hf g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hf
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg
    exact commute_smul_right_of_commute (R := R)
      (commute_smul_left_of_commute (R := R) (pairLower_commute b i j)
        (u * y i * gaussNilpotentInverse u v (y i) N))
      (u * y j * gaussNilpotentInverse u v (y j) N)
  have hsum : l.sum w = 0 := by
    have h := hw (gaussAnnihilatorPolynomial u v N)
    simpa only [l, Finset.sum_map_toList, a, gaussAnnihilatorPolynomial_eval] using h
  have hfac' : IsUnit (l.length.factorial : R) := by
    simpa only [l, List.length_map, Finset.length_toList, Finset.card_univ] using hfac
  simpa only [l, a, List.map_map, Function.comp_def] using
    prod_one_add_apply_eq_self_of_sum_apply_eq_zero l hsq hcomm hfac' w hsum

/-- The diagonal Gauss factorization on a mixed-harmonic vector, with the
annihilator factor rigorously removed. Nilpotence of the parameter-times-coordinate
products realizes the inverse coefficients as finite polynomials. -/
theorem diagonal_gauss_apply_primitive
    (y : I → R) (u v : R) (N : ℕ) (hy : ∀ i, ((-u * v) * y i) ^ N = 0)
    (hfac : IsUnit ((Fintype.card I).factorial : R))
    (w : ExteriorAlgebra R V)
    (hw : ∀ p : Polynomial R, (∑ i, p.eval (y i) • pairLower b i) w = 0) :
    ((Finset.univ.toList.map fun i ↦ 1 + (u * y i) • pairLower b i).prod)
      (((Finset.univ.toList.map fun i ↦ 1 + v • pairRaise b i).prod) w) =
    ((Finset.univ.toList.map fun i ↦
      1 + (v * gaussNilpotentInverse u v (y i) N) • pairRaise b i).prod)
      (((Finset.univ.toList.map fun i ↦
        pairGaussDiagonal (u * y i) v (gaussNilpotentInverse u v (y i) N)
          (pairLower b i) (pairRaise b i)).prod) w) := by
  have h := congrArg (fun f : Module.End R (ExteriorAlgebra R V) ↦ f w)
    (diagonal_gauss_product b Finset.univ.toList Finset.univ.nodup_toList
      (fun i ↦ u * y i) (fun _ ↦ v) (fun i ↦ gaussNilpotentInverse u v (y i) N)
      (fun i ↦ gaussNilpotentInverse_mul_of_product_pow_eq_zero u v (y i) N (hy i)))
  simpa only [Module.End.mul_apply, diagonal_gauss_right_fixes b y u v N hfac w hw]
    using h

/-- The coefficient of exterior raising order `j` vanishes above the precise
primitive height. This is the finite divided-power form of the truncated
exponential used in Lemma 3.1. -/
theorem primitive_elementary_raising_eq_zero
    (hfac : IsUnit ((Fintype.card I).factorial : R))
    (k : ℕ) (w : ExteriorAlgebra R V) (hw : w ∈ ⋀[R]^k V)
    (he : lowering b w = 0) (hk : k ≤ Fintype.card I)
    (j : ℕ) (hj : Fintype.card I - k < j) :
    elementaryOperator (Finset.univ.toList.map (pairRaise b)) j w = 0 := by
  by_cases hlarge : Fintype.card I < j
  · rw [elementaryOperator_eq_zero_of_length_lt _ j
      (by simpa only [List.length_map, Finset.length_toList, Finset.card_univ] using hlarge)]
    rfl
  have hunit : IsUnit (j.factorial : R) :=
    unit_factorialCast_of_le hfac (Nat.le_of_not_gt hlarge)
  have hsq : ∀ f ∈ Finset.univ.toList.map (pairRaise b), f * f = 0 := by
    intro f hf
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hf
    exact pairRaise_square b i
  have hcomm : ∀ f ∈ Finset.univ.toList.map (pairRaise b),
      ∀ g ∈ Finset.univ.toList.map (pairRaise b), Commute f g := by
    intro f hf g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hf
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg
    exact pairRaise_commute b i j
  apply elementary_apply_eq_zero_of_sum_power_eq_zero _ hsq hcomm j hunit w
  rw [Finset.sum_map_toList]
  change (raising b ^ j) w = 0
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show Fintype.card I - k + 1 ≤ j by omega)
  rw [hd, add_comm (Fintype.card I - k + 1), pow_add, Module.End.mul_apply,
    primitive_raising_pow_eq_zero b hfac k w hw he hk, map_zero]

end Exterior

end PaperVerification.Fermion
