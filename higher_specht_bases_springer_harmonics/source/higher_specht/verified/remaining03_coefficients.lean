module

public import higher_specht.verified.remaining03_fiber
public import tau_ceti.ring_theory.semisimple.isotypic_tensor
public import Mathlib.Algebra.Field.ZMod

/- Generated ordinary source-preserving proof stage. See audit/staged_specht_remaining/Remaining03Coefficients/manifest.json. -/

@[expose] public section

section CanonicalSource26
/- Source: HigherSpecht/FactorialUnits.lean -/



/-!
# The exact coefficient diagonal has only subgroup-order denominators

Both finite sets on the apolar diagonal are actual stabilizer subgroups.
Their cardinalities divide `n!` by Lagrange. Consequently the diagonal is
a unit over any coefficient ring in which `n!` is a unit, with no bound
depending on a polynomial exponent or the parameter `s`.
-/

noncomputable section
open Finset TauCeti TauCeti.YoungTableau
open scoped Classical

namespace HigherSpecht

def valueStabilizer {ι A : Type*} (G : Subgroup (Equiv.Perm ι)) (f : ι → A) : Subgroup G where
  carrier := {g | ∀ i, f (g.val i) = f i}
  one_mem' := by intro i; rfl
  mul_mem' := by
    intro g h hg hh i
    exact (hg (h.val i)).trans (hh i)
  inv_mem' := by
    intro g hg i
    have h := hg (g.val.symm i)
    simpa only [Subgroup.coe_inv, Equiv.Perm.inv_def, Equiv.apply_symm_apply] using h.symm

theorem valueStabilizer_card {ι A : Type*} [Fintype ι]
    (G : Subgroup (Equiv.Perm ι)) (f : ι → A) :
    (univ.filter (fun g : G => ∀ i, f (g.val i) = f i)).card = Nat.card (valueStabilizer G f) := by
  let e : ↥(univ.filter (fun g : G => ∀ i, f (g.val i) = f i)) ≃ valueStabilizer G f :=
    { toFun g := ⟨g.val, (mem_filter.mp g.property).2⟩
      invFun g := ⟨g.val, mem_filter.mpr ⟨mem_univ _, g.property⟩⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using Fintype.card_congr e

theorem valueStabilizer_card_dvd_factorial {n : ℕ} {A : Type*}
    (G : Subgroup (Equiv.Perm (Fin n))) (f : Fin n → A) :
    Nat.card (valueStabilizer G f) ∣ n.factorial := by
  have h := (valueStabilizer G f).card_subgroup_dvd_card.trans G.card_subgroup_dvd_card
  simpa only [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] using h

/-- This form keeps the supplied finite set literal, so applying Lagrange
never compares two independently synthesized enumerations of a subgroup. -/
private theorem stabilizerFinset_card_dvd_factorial {n : ℕ} {A : Type*}
    (G : Subgroup (Equiv.Perm (Fin n))) (f : Fin n → A) (s : Finset G)
    (hs : ∀ g : G, g ∈ s ↔ ∀ i, f (g.val i) = f i) :
    s.card ∣ n.factorial := by
  let e : ↥s ≃ valueStabilizer G f :=
    { toFun g := ⟨g.val, (hs g.val).mp g.property⟩
      invFun g := ⟨g.val, (hs g.val).mpr g.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  have hcard : s.card = Nat.card (valueStabilizer G f) := by
    calc
      s.card = Nat.card ↥s := by
        simp only [Nat.card_eq_fintype_card, Fintype.card_coe]
      _ = Nat.card (valueStabilizer G f) := Nat.card_congr e
  have hd := valueStabilizer_card_dvd_factorial G f
  rwa [← hcard] at hd

theorem rowFillingStabilizers_card_dvd_factorial {mu : YoungDiagram}
    (T : YoungTableau mu) (b : Fin mu.card →₀ ℕ) :
    (rowFillingStabilizers T b).card ∣ mu.card.factorial := by
  have heq : rowFillingStabilizers T b =
      univ.filter (fun g : rowSubgroup T => ∀ i, b (g.val i) = b i) := by
    ext g
    simp only [rowFillingStabilizers, mem_filter, mem_univ, true_and]
    constructor
    · intro h i
      have hh := congrArg (fun v : Fin mu.card →₀ ℕ => v (g.val i)) h
      simpa only [permutedExponent_apply, Equiv.symm_apply_apply] using hh.symm
    · intro h
      ext i
      have hh := h (g.val.symm i)
      simpa only [permutedExponent_apply, Equiv.apply_symm_apply] using hh.symm
  apply stabilizerFinset_card_dvd_factorial (rowSubgroup T) (fun i => b i)
    (rowFillingStabilizers T b)
  intro g
  simp only [heq, mem_filter, mem_univ, true_and]

theorem fixedWitnessPermutations_card_dvd_factorial {n : ℕ}
    (G : Subgroup (Equiv.Perm (Fin n))) (r : Fin n →₀ ℕ) (c : Fin n → ℤ) :
    (fixedWitnessPermutations G r c).card ∣ n.factorial := by
  have heq : fixedWitnessPermutations G r c =
      univ.filter (fun g : G => ∀ i,
        (intExponent r (g.val i), c (g.val i)) = (intExponent r i, c i)) := by
    ext g
    simp only [mem_fixedWitnessPermutations, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hr, hc⟩ i
      exact Prod.ext (congrFun hr i) (congrFun hc i)
    · intro h
      exact ⟨funext (fun i => congrArg Prod.fst (h i)),
        funext (fun i => congrArg Prod.snd (h i))⟩
  apply stabilizerFinset_card_dvd_factorial G (fun i => (intExponent r i, c i))
    (fixedWitnessPermutations G r c)
  intro g
  simp only [heq, mem_filter, mem_univ, true_and]

theorem natCast_isUnit_of_dvd_factorial {R : Type*} [CommRing R] {n d : ℕ}
    (hn : IsUnit (n.factorial : R)) (hd : d ∣ n.factorial) : IsUnit (d : R) := by
  obtain ⟨q, hq⟩ := hd
  obtain ⟨u, hu⟩ := hn
  have hmul : (d : R) * ((q : R) * (u⁻¹ : Rˣ)) = 1 := by
    rw [← mul_assoc, ← Nat.cast_mul, ← hq, ← hu, Units.mul_inv]
  exact ⟨⟨(d : R), (q : R) * (u⁻¹ : Rˣ), hmul, by rw [mul_comm]; exact hmul⟩, rfl⟩

theorem rowFillingStabilizers_card_isUnit {R : Type*} [CommRing R]
    {mu : YoungDiagram} (hfac : IsUnit (mu.card.factorial : R))
    (T : YoungTableau mu) (b : Fin mu.card →₀ ℕ) :
    IsUnit ((rowFillingStabilizers T b).card : R) :=
  natCast_isUnit_of_dvd_factorial hfac (rowFillingStabilizers_card_dvd_factorial T b)

theorem fixedWitnessPermutations_card_isUnit {R : Type*} [CommRing R]
    {n : ℕ} (hfac : IsUnit (n.factorial : R))
    (G : Subgroup (Equiv.Perm (Fin n))) (r : Fin n →₀ ℕ) (c : Fin n → ℤ) :
    IsUnit ((fixedWitnessPermutations G r c).card : R) :=
  natCast_isUnit_of_dvd_factorial hfac (fixedWitnessPermutations_card_dvd_factorial G r c)

theorem factorial_ne_zero_of_char_gt {K : Type*} [Field K] {p : ℕ} [CharP K p]
    {n : ℕ} (hn : n < p) : (n.factorial : K) ≠ 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.factorial_succ, Nat.cast_mul]
      apply mul_ne_zero
      · intro hzero
        have hd := (CharP.cast_eq_zero_iff K p (n + 1)).mp hzero
        exact (Nat.not_dvd_of_pos_of_lt (Nat.succ_pos n) hn) hd
      · exact ih (by omega)

end HigherSpecht
end
end CanonicalSource26

section CanonicalSource27
/- Source: HigherSpecht/IntegralPolytabloids.lean -/



/-!
# Integral polytabloids and their actual coefficient representations

The coefficient space is the finite function space on ordinary tabloids.
The column operator and polytabloid are their literal signed finite sums.
The rational comparison is used only to transfer identities between integer
coefficients; no rational scalar is mapped into a field of positive
characteristic.
-/

noncomputable section
open Finset TauCeti TauCeti.YoungTableau Module
open scoped Classical

namespace HigherSpecht

abbrev TabloidSpaceOver (R : Type*) (mu : YoungDiagram) := TableauTabloid mu → R

def tabloidRepresentationOver (R : Type*) [CommRing R] (mu : YoungDiagram) :
    Representation R (Equiv.Perm (Fin mu.card)) (TabloidSpaceOver R mu) where
  toFun g :=
    { toFun f := fun q => f (g⁻¹ • q)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_one' := by ext f q; simp
  map_mul' g h := by ext f q; simp [mul_smul]

@[simp] theorem tabloidRepresentationOver_apply {R : Type*} [CommRing R]
    {mu : YoungDiagram} (g : Equiv.Perm (Fin mu.card))
    (f : TabloidSpaceOver R mu) (q : TableauTabloid mu) :
    tabloidRepresentationOver R mu g f q = f (g⁻¹ • q) := rfl

@[simp] theorem tabloidRepresentationOver_single {R : Type*} [CommRing R]
    {mu : YoungDiagram} (g : Equiv.Perm (Fin mu.card)) (q : TableauTabloid mu) (a : R) :
    tabloidRepresentationOver R mu g (Pi.single q a) = Pi.single (g • q) a := by
  classical
  ext x
  simp only [tabloidRepresentationOver_apply, Pi.single_apply]
  have hiff : g⁻¹ • x = q ↔ x = g • q := by
    constructor
    · intro h; simpa only [smul_inv_smul] using congrArg (g • ·) h
    · intro h; rw [h, inv_smul_smul]
  exact ite_cond_congr (propext hiff)

def columnActionOver {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    {mu : YoungDiagram} (rho : Representation R (Equiv.Perm (Fin mu.card)) V)
    (T : YoungTableau mu) : V →ₗ[R] V :=
  ∑ g : colSubgroup T, ((Equiv.Perm.sign g.val : ℤ) : R) • rho g.val

@[simp] theorem columnActionOver_apply {R V : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] {mu : YoungDiagram}
    (rho : Representation R (Equiv.Perm (Fin mu.card)) V) (T : YoungTableau mu) (v : V) :
    columnActionOver rho T v =
      ∑ g : colSubgroup T, ((Equiv.Perm.sign g.val : ℤ) : R) • rho g.val v := by
  simp only [columnActionOver, LinearMap.sum_apply, LinearMap.smul_apply]

def columnElementOver (R : Type*) [CommRing R] {mu : YoungDiagram}
    (T : YoungTableau mu) : MonoidAlgebra R (Equiv.Perm (Fin mu.card)) :=
  ∑ g : colSubgroup T, MonoidAlgebra.single g.val ((Equiv.Perm.sign g.val : ℤ) : R)

theorem columnActionOver_eq_asAlgebraHom {R V : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] {mu : YoungDiagram}
    (rho : Representation R (Equiv.Perm (Fin mu.card)) V) (T : YoungTableau mu) :
    columnActionOver rho T = rho.asAlgebraHom (columnElementOver R T) := by
  ext v
  simp only [columnElementOver, map_sum, LinearMap.sum_apply,
    Representation.asAlgebraHom_single, columnActionOver_apply, LinearMap.smul_apply]

def polytabloidOver (R : Type*) [CommRing R] {mu : YoungDiagram}
    (T : YoungTableau mu) : TabloidSpaceOver R mu :=
  ∑ g : colSubgroup T, ((Equiv.Perm.sign g.val : ℤ) : R) •
    Pi.single (g.val • tabloid T) 1

theorem polytabloidOver_eq_columnAction {R : Type*} [CommRing R]
    {mu : YoungDiagram} (T : YoungTableau mu) :
    polytabloidOver R T =
      columnActionOver (tabloidRepresentationOver R mu) T (Pi.single (tabloid T) 1) := by
  simp only [polytabloidOver, columnActionOver_apply, tabloidRepresentationOver_single]

theorem polytabloidOver_cast {R : Type*} [CommRing R] {mu : YoungDiagram}
    (T : YoungTableau mu) (q : TableauTabloid mu) :
    ((polytabloidOver ℤ T q : ℤ) : R) = polytabloidOver R T q := by
  simp [polytabloidOver, Pi.single_apply]

theorem polytabloidOver_rat_apply {mu : YoungDiagram}
    (T : YoungTableau mu) (q : TableauTabloid mu) :
    polytabloidOver ℚ T q = (polytabloid T).coeff q := by
  rw [polytabloid_eq_sum]
  simp only [polytabloidOver, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Pi.single_apply, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MonoidAlgebra.coeff_smul, Finsupp.smul_apply, MonoidAlgebra.coeff_single,
    Finsupp.single_apply, eq_comm]

@[simp] theorem polytabloidOver_tabloid {R : Type*} [CommRing R]
    {mu : YoungDiagram} (T : YoungTableau mu) : polytabloidOver R T (tabloid T) = 1 := by
  have hQ : (polytabloidOver ℤ T (tabloid T) : ℚ) = 1 := by
    rw [polytabloidOver_cast, polytabloidOver_rat_apply, polytabloid_coeff_tabloid]
  have hZ : polytabloidOver ℤ T (tabloid T) = 1 := by exact_mod_cast hQ
  rw [← polytabloidOver_cast, hZ, Int.cast_one]

theorem polytabloidOver_ne_zero {R : Type*} [CommRing R] [Nontrivial R]
    {mu : YoungDiagram} (T : YoungTableau mu) : polytabloidOver R T ≠ 0 := by
  intro h
  have := congrFun h (tabloid T)
  simpa only [polytabloidOver_tabloid, Pi.zero_apply, one_ne_zero] using this

theorem polytabloidOver_eq_zero_of_forall_ne {R : Type*} [CommRing R]
    {mu : YoungDiagram} (T : YoungTableau mu) (q : TableauTabloid mu)
    (hq : ∀ g ∈ colSubgroup T, g • tabloid T ≠ q) : polytabloidOver R T q = 0 := by
  rw [polytabloidOver, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro g _
  simp only [Pi.smul_apply, Pi.single_apply, if_neg (hq g.val g.property).symm,
    smul_zero]

theorem polytabloidOver_relabel {R : Type*} [CommRing R] {mu : YoungDiagram}
    (g : Equiv.Perm (Fin mu.card)) (T : YoungTableau mu) :
    polytabloidOver R (relabel g T) = tabloidRepresentationOver R mu g (polytabloidOver R T) := by
  ext q
  have hQ : (polytabloidOver ℤ (relabel g T) q : ℚ) =
      (polytabloidOver ℤ T (g⁻¹ • q) : ℚ) := by
    rw [polytabloidOver_cast, polytabloidOver_cast, polytabloidOver_rat_apply,
      polytabloidOver_rat_apply, polytabloid_relabel, Representation.coeff_ofMulAction]
  have hZ : polytabloidOver ℤ (relabel g T) q = polytabloidOver ℤ T (g⁻¹ • q) := by
    exact_mod_cast hQ
  simpa only [polytabloidOver_cast, tabloidRepresentationOver_apply] using
    congrArg (fun z : ℤ => (z : R)) hZ

def spechtSubrepresentationOver (R : Type*) [CommRing R] (mu : YoungDiagram) :
    Subrepresentation (tabloidRepresentationOver R mu) where
  toSubmodule := Submodule.span R (Set.range (polytabloidOver R (mu := mu)))
  apply_mem_toSubmodule g _ hv := by
    have h : Submodule.span R (Set.range (polytabloidOver R (mu := mu))) ≤
        (Submodule.span R (Set.range (polytabloidOver R (mu := mu)))).comap
          (tabloidRepresentationOver R mu g) := by
      rw [Submodule.span_le]
      rintro _ ⟨T, rfl⟩
      exact Submodule.subset_span ⟨relabel g T, polytabloidOver_relabel g T⟩
    exact h hv

theorem polytabloidOver_mem {R : Type*} [CommRing R] {mu : YoungDiagram}
    (T : YoungTableau mu) : polytabloidOver R T ∈ spechtSubrepresentationOver R mu :=
  Submodule.subset_span ⟨T, rfl⟩

theorem spechtSubrepresentationOver_span_orbit {R : Type*} [CommRing R]
    {mu : YoungDiagram} (T : YoungTableau mu) :
    (spechtSubrepresentationOver R mu).toSubmodule = Submodule.span R
      (Set.range fun g : Equiv.Perm (Fin mu.card) =>
        tabloidRepresentationOver R mu g (polytabloidOver R T)) := by
  change Submodule.span R _ = _
  congr 1
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨U, rfl⟩
    obtain ⟨g, rfl⟩ := exists_relabel_eq T U
    exact ⟨g, (polytabloidOver_relabel g T).symm⟩
  · rintro _ ⟨g, rfl⟩
    exact ⟨relabel g T, polytabloidOver_relabel g T⟩

instance {K : Type*} [Field K] (mu : YoungDiagram) :
    FiniteDimensional K (spechtSubrepresentationOver K mu).toSubmodule :=
  FiniteDimensional.finiteDimensional_submodule _

end HigherSpecht
end
end CanonicalSource27

section CanonicalSource28
/- Source: HigherSpecht/IntegralColumnOperators.lean -/



/-!
# Integral column-operator identities

James's single-tabloid identity is transferred through the injective map
`ℤ → ℚ`, then through `ℤ → R`. This proves the genuine identity over every
commutative coefficient ring, including characteristic two. The use of the
rational theorem therefore introduces neither a characteristic-zero
assumption nor a map from the rationals into the target ring.
-/

noncomputable section
open Finset TauCeti TauCeti.YoungTableau Module
open scoped Classical

namespace HigherSpecht

theorem columnElementOver_eq_subgroupCharSum {R : Type*} [CommRing R]
    {mu : YoungDiagram} (T : YoungTableau mu) :
    columnElementOver R T =
      subgroupCharSum ((Units.coeHom R).comp (signLinearCharacter R (Fin mu.card)))
        (colSubgroup T) := by
  simp only [columnElementOver, subgroupCharSum_def, MonoidHom.coe_comp,
    Function.comp_apply, Units.coeHom_apply, coe_signLinearCharacter_apply,
    MonoidAlgebra.of_apply, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]

theorem columnElementOver_sq {R : Type*} [CommRing R]
    {mu : YoungDiagram} (T : YoungTableau mu) :
    columnElementOver R T * columnElementOver R T =
      Nat.card (colSubgroup T) • columnElementOver R T := by
  rw [columnElementOver_eq_subgroupCharSum, subgroupCharSum_mul_self]

theorem columnActionOver_apply_eq_zero_of_odd_fix
    {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    {mu : YoungDiagram} (T : YoungTableau mu)
    (rho : Representation R (Equiv.Perm (Fin mu.card)) V)
    (h2inj : Function.Injective (fun v : V => (2 : ℕ) • v))
    {g : Equiv.Perm (Fin mu.card)} (hg : g ∈ colSubgroup T)
    (hsign : Equiv.Perm.sign g = -1) {v : V} (hfix : rho g v = v) :
    columnActionOver rho T v = 0 := by
  rw [columnActionOver_eq_asAlgebraHom, columnElementOver_eq_subgroupCharSum]
  apply asAlgebraHom_subgroupCharSum_apply_eq_zero _ _ h2inj rho hg _ hfix
  simp only [MonoidHom.coe_comp, Function.comp_apply, Units.coeHom_apply,
    coe_signLinearCharacter_apply, Equiv.Perm.sign_inv, hsign,
    Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]

theorem columnActionOver_cast {R : Type*} [CommRing R] {mu : YoungDiagram}
    (T : YoungTableau mu) (v : TabloidSpaceOver ℤ mu) (q : TableauTabloid mu) :
    ((columnActionOver (tabloidRepresentationOver ℤ mu) T v q : ℤ) : R) =
      columnActionOver (tabloidRepresentationOver R mu) T (fun q => (v q : R)) q := by
  simp [columnActionOver_apply, tabloidRepresentationOver_apply]

theorem columnActionOver_rat_apply {mu : YoungDiagram} (T : YoungTableau mu)
    (v : (permutationModule (shapePartition mu)).V) (q : TableauTabloid mu) :
    columnActionOver (tabloidRepresentationOver ℚ mu) T (fun x => v.coeff x) q =
      ((permutationModule (shapePartition mu)).ρ.asAlgebraHom
        (columnAntisymmetrizer T) v).coeff q := by
  rw [asAlgebraHom_columnAntisymmetrizer_apply]
  simp only [columnActionOver_apply, Finset.sum_apply, Pi.smul_apply,
    tabloidRepresentationOver_apply, smul_eq_mul, MonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply, MonoidAlgebra.coeff_smul, Finsupp.smul_apply,
    Representation.coeff_ofMulAction]

def columnSingleCoefficient {mu : YoungDiagram} (T : YoungTableau mu)
    (q : TableauTabloid mu) : ℤ :=
  columnActionOver (tabloidRepresentationOver ℤ mu) T (Pi.single q 1) (tabloid T)

theorem columnActionOver_single_int {mu : YoungDiagram} (T : YoungTableau mu)
    (q : TableauTabloid mu) :
    columnActionOver (tabloidRepresentationOver ℤ mu) T (Pi.single q 1) =
      columnSingleCoefficient T q • polytabloidOver ℤ T := by
  obtain ⟨c, -, hc⟩ := exists_eq_smul_polytabloid_single T q
  have hcoeff (x : TableauTabloid mu) :
      (columnActionOver (tabloidRepresentationOver ℤ mu) T (Pi.single q 1) x : ℚ) =
        c * (polytabloidOver ℤ T x : ℚ) := by
    rw [columnActionOver_cast]
    have hs : (fun x => (((Pi.single q (1 : ℤ) : TabloidSpaceOver ℤ mu) x : ℤ) : ℚ)) =
        fun x => (MonoidAlgebra.single q (1 : ℚ)).coeff x := by
      ext x
      simp [Pi.single_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply, eq_comm]
    rw [hs, columnActionOver_rat_apply, hc,
      MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul,
      polytabloidOver_cast, polytabloidOver_rat_apply]
  have hcint : c = (columnSingleCoefficient T q : ℚ) := by
    simpa only [polytabloidOver_tabloid, Int.cast_one, mul_one,
      columnSingleCoefficient] using (hcoeff (tabloid T)).symm
  ext x
  have hx := hcoeff x
  rw [hcint, ← Int.cast_mul] at hx
  exact_mod_cast hx

theorem columnActionOver_single {R : Type*} [CommRing R] {mu : YoungDiagram}
    (T : YoungTableau mu) (q : TableauTabloid mu) :
    columnActionOver (tabloidRepresentationOver R mu) T (Pi.single q 1) =
      (columnSingleCoefficient T q : R) • polytabloidOver R T := by
  ext x
  have h := congrArg (fun v : TabloidSpaceOver ℤ mu => (v x : R))
    (columnActionOver_single_int T q)
  rw [columnActionOver_cast] at h
  have hsingle : (fun y => (((Pi.single q (1 : ℤ) : TabloidSpaceOver ℤ mu) y : ℤ) : R)) =
      (Pi.single q (1 : R) : TabloidSpaceOver R mu) := by
    funext y
    simp only [Pi.single_apply, Int.cast_ite, Int.cast_one, Int.cast_zero]
  rw [hsingle] at h
  simpa only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, polytabloidOver_cast] using h

theorem exists_columnActionOver_eq_smul {R : Type*} [CommRing R]
    {mu : YoungDiagram} (T : YoungTableau mu) (v : TabloidSpaceOver R mu) :
    ∃ c : R, columnActionOver (tabloidRepresentationOver R mu) T v =
      c • polytabloidOver R T := by
  have hv : v = ∑ q : TableauTabloid mu, v q • Pi.single q 1 := by
    ext x
    simp [Pi.single_apply]
  refine ⟨∑ q : TableauTabloid mu, v q * (columnSingleCoefficient T q : R), ?_⟩
  conv_lhs => rw [hv]
  rw [map_sum]
  simp only [map_smul, columnActionOver_single, smul_smul, Finset.sum_smul]

theorem columnActionOver_polytabloid {R : Type*} [CommRing R]
    {mu : YoungDiagram} (T : YoungTableau mu) :
    columnActionOver (tabloidRepresentationOver R mu) T (polytabloidOver R T) =
      (Nat.card (colSubgroup T) : R) • polytabloidOver R T := by
  rw [polytabloidOver_eq_columnAction]
  simp only [columnActionOver_eq_asAlgebraHom]
  rw [← Module.End.mul_apply, ← map_mul, columnElementOver_sq, map_nsmul,
    LinearMap.smul_apply, Nat.cast_smul_eq_nsmul]

theorem columnActionOver_polytabloid_ne_zero {K : Type*} [Field K]
    {mu : YoungDiagram} (hfac : (mu.card.factorial : K) ≠ 0) (T : YoungTableau mu) :
    columnActionOver (tabloidRepresentationOver K mu) T (polytabloidOver K T) ≠ 0 := by
  rw [columnActionOver_polytabloid]
  apply smul_ne_zero
  · apply (natCast_isUnit_of_dvd_factorial (isUnit_iff_ne_zero.mpr hfac) ?_).ne_zero
    have h := (colSubgroup T).card_subgroup_dvd_card
    simpa only [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] using h
  · exact polytabloidOver_ne_zero T

end HigherSpecht
end
end CanonicalSource28

section CanonicalSource29
/- Source: HigherSpecht/IntegralStandardPolytabloids.lean -/



/-!
# Unit-triangular independence of ordinary standard polytabloids

The distinguished coefficient is exactly one. Thus this part holds over
every commutative ring; the later irreducibility argument is the place where
invertibility of `n!` is needed.
-/

noncomputable section
open Finset TauCeti TauCeti.YoungTableau Module
open scoped Classical

namespace HigherSpecht

/-- A finite rank for the actual tabloid-dominance preorder. Counting all
 dominated tableaux is enough: dominance gives inclusion of these finite
 sets, and equal cardinality forces reverse dominance. No unfolding of the
 imported dominance predicate is needed. -/
def tabloidDominanceRank {mu : YoungDiagram} (T : YoungTableau mu) : ℕ :=
  (Finset.univ.filter fun U : YoungTableau mu => TabloidDominates T U).card

theorem tabloidDominanceRank_congr {mu : YoungDiagram} {T U : YoungTableau mu}
    (h : rowIndex T = rowIndex U) : tabloidDominanceRank T = tabloidDominanceRank U := by
  unfold tabloidDominanceRank
  apply congrArg Finset.card
  apply Finset.ext
  intro V
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact tabloidDominates_congr (tabloid_eq_iff_rowIndex_eq.mpr h) rfl

theorem rowIndex_eq_of_dominates_rank {mu : YoungDiagram} {T U : YoungTableau mu}
    (h : TabloidDominates T U) (hw : tabloidDominanceRank T ≤ tabloidDominanceRank U) :
    rowIndex U = rowIndex T := by
  have hsubset : (Finset.univ.filter fun V : YoungTableau mu => TabloidDominates U V) ⊆
      (Finset.univ.filter fun V : YoungTableau mu => TabloidDominates T V) := by
    intro V hV
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ V,
      TabloidDominates.trans h (Finset.mem_filter.mp hV).2⟩
  unfold tabloidDominanceRank at hw
  have heq := Finset.eq_of_subset_of_card_le hsubset hw
  have hmem : T ∈ Finset.univ.filter (fun V : YoungTableau mu => TabloidDominates U V) := by
    rw [heq]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ T, tabloidDominates_refl T⟩
  exact tabloid_eq_iff_rowIndex_eq.mp
    (TabloidDominates.antisymm (Finset.mem_filter.mp hmem).2 h)

theorem linearIndependent_polytabloidOver {R : Type*} [CommRing R]
    (mu : YoungDiagram) :
    LinearIndependent R (fun T : StandardYoungTableau mu => polytabloidOver R T.toTableau) := by
  rw [linearIndependent_iff']
  intro s c hsum T1 hT1
  by_contra hc
  obtain ⟨T0, hT0, hmax⟩ := exists_max_image (s.filter (fun T => c T ≠ 0))
    (fun T => tabloidDominanceRank T.toTableau) ⟨T1, mem_filter.mpr ⟨hT1, hc⟩⟩
  obtain ⟨hT0s, hc0⟩ := mem_filter.mp hT0
  have hzero : ∀ T ∈ s, T ≠ T0 →
      (c T • polytabloidOver R T.toTableau) (tabloid T0.toTableau) = 0 := by
    intro T hTs hne
    by_cases hct : c T = 0
    · simp only [hct, zero_smul, Pi.zero_apply]
    have hp : polytabloidOver R T.toTableau (tabloid T0.toTableau) = 0 := by
      apply polytabloidOver_eq_zero_of_forall_ne
      intro g hg htab
      apply hne
      have hdom := tabloidDominates_relabel_of_mem_colSubgroup T hg
      have hrow : rowIndex (relabel g T.toTableau) = rowIndex T0.toTableau := by
        rw [← tabloid_eq_iff_rowIndex_eq, tabloid_relabel, htab]
      have hw : tabloidDominanceRank T.toTableau ≤ tabloidDominanceRank (relabel g T.toTableau) := by
        rw [tabloidDominanceRank_congr hrow]
        exact hmax T (mem_filter.mpr ⟨hTs, hct⟩)
      exact StandardYoungTableau.rowIndex_injective mu
        ((rowIndex_eq_of_dominates_rank hdom hw).symm.trans hrow)
    simp only [Pi.smul_apply, hp, smul_zero]
  have hz := congrFun hsum (tabloid T0.toTableau)
  rw [Finset.sum_apply, Finset.sum_eq_single_of_mem T0 hT0s hzero] at hz
  simp only [Pi.smul_apply, polytabloidOver_tabloid, smul_eq_mul,
    mul_one, Pi.zero_apply] at hz
  exact hc0 hz

def standardPolytabloidOver {R : Type*} [CommRing R] {mu : YoungDiagram}
    (T : StandardYoungTableau mu) : (spechtSubrepresentationOver R mu).toSubmodule :=
  ⟨polytabloidOver R T.toTableau, polytabloidOver_mem T.toTableau⟩

theorem linearIndependent_standardPolytabloidOver {R : Type*} [CommRing R]
    (mu : YoungDiagram) :
    LinearIndependent R (standardPolytabloidOver (R := R) (mu := mu)) := by
  exact LinearIndependent.of_comp (spechtSubrepresentationOver R mu).toSubmodule.subtype
    (linearIndependent_polytabloidOver mu)

end HigherSpecht
end
end CanonicalSource29

section CanonicalSource30
/- Source: HigherSpecht/IntegralSpechtPolynomialMap.lean -/



/-!
# The literal higher Specht map over arbitrary coefficients

The map sends a tabloid to the sum over its actual row-equivalent tableaux.
Its restriction to the integral polytabloid span sends every standard
polytabloid to the manuscript's unnormalized higher Specht polynomial.
-/

noncomputable section
open Finset TauCeti TauCeti.YoungTableau Module MvPolynomial
open scoped Classical

namespace HigherSpecht

variable {R : Type*} [CommRing R] {mu : YoungDiagram}

def tableauCochargeMonomialOver (S : StandardYoungTableau mu) (T : YoungTableau mu) :
    PolynomialRing mu.card R := monomial (transportedCocharge S T) 1

theorem rename_tableauCochargeMonomialOver (S : StandardYoungTableau mu)
    (T : YoungTableau mu) (g : Equiv.Perm (Fin mu.card)) :
    rename g (tableauCochargeMonomialOver (R := R) S T) =
      tableauCochargeMonomialOver S (relabel g T) := by
  rw [tableauCochargeMonomialOver, rename_monomial_permuted, tableauCochargeMonomialOver]
  apply congrArg (fun a : Fin mu.card →₀ ℕ => MvPolynomial.monomial a (1 : R))
  apply Finsupp.ext
  intro i
  simp only [permutedExponent_apply, transportedCocharge,
    Finsupp.equivFunOnFinite_symm_apply_apply, relabel_symm_apply, Equiv.Perm.inv_def]

def tabloidPolynomialOver (S : StandardYoungTableau mu) (q : TableauTabloid mu) :
    PolynomialRing mu.card R :=
  ∑ T : YoungTableau mu, if tabloid T = q then tableauCochargeMonomialOver S T else 0

theorem tabloidPolynomialOver_tabloid (S : StandardYoungTableau mu) (T : YoungTableau mu) :
    tabloidPolynomialOver (R := R) S (tabloid T) =
      rowSymmetrize (rowSubgroup T) (tableauCochargeMonomialOver S T) := by
  rw [tabloidPolynomialOver, ← Finset.sum_filter]
  rw [Finset.sum_subtype (p := fun U : YoungTableau mu => tabloid U = tabloid T)
    _ (by intro U; simp only [Finset.mem_filter, Finset.mem_univ, true_and])
    (tableauCochargeMonomialOver (R := R) S)]
  rw [← Equiv.sum_comp (tableauRowOrbitEquiv T)
    (fun U : {U : YoungTableau mu // tabloid U = tabloid T} =>
      tableauCochargeMonomialOver (R := R) S U.val)]
  unfold rowSymmetrize
  apply Finset.sum_congr rfl
  intro g _
  exact (rename_tableauCochargeMonomialOver S T g.val).symm

theorem tabloidPolynomialOver_smul (S : StandardYoungTableau mu)
    (q : TableauTabloid mu) (g : Equiv.Perm (Fin mu.card)) :
    tabloidPolynomialOver (R := R) S (g • q) = rename g (tabloidPolynomialOver S q) := by
  rw [tabloidPolynomialOver, tabloidPolynomialOver, map_sum]
  rw [← Equiv.sum_comp (tableauRelabelEquiv g)
    (fun T : YoungTableau mu => if tabloid T = g • q then
      tableauCochargeMonomialOver (R := R) S T else 0)]
  apply Finset.sum_congr rfl
  intro T _
  change (if tabloid (relabel g T) = g • q then
    tableauCochargeMonomialOver S (relabel g T) else 0) = _
  rw [tabloid_relabel]
  by_cases hq : tabloid T = q
  · simp only [hq, if_true, rename_tableauCochargeMonomialOver]
  · have hq' : g • tabloid T ≠ g • q := fun h => hq ((MulAction.injective g) h)
    simp only [if_neg hq, if_neg hq', map_zero]

def tabloidPolynomialLinearOver (S : StandardYoungTableau mu) :
    TabloidSpaceOver R mu →ₗ[R] PolynomialRing mu.card R where
  toFun v := ∑ q : TableauTabloid mu, v q • tabloidPolynomialOver S q
  map_add' v w := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [Pi.smul_apply, smul_smul, Finset.smul_sum, RingHom.id_apply, smul_eq_mul]

@[simp] theorem tabloidPolynomialLinearOver_single (S : StandardYoungTableau mu)
    (q : TableauTabloid mu) (a : R) :
    tabloidPolynomialLinearOver S (Pi.single q a) = a • tabloidPolynomialOver S q := by
  simp [tabloidPolynomialLinearOver, Pi.single_apply]

def tabloidPolynomialIntertwinerOver (S : StandardYoungTableau mu) :
    (tabloidRepresentationOver R mu).IntertwiningMap (polynomialRepresentation R mu.card) where
  toLinearMap := tabloidPolynomialLinearOver S
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    change (∑ q : TableauTabloid mu, v (g⁻¹ • q) • tabloidPolynomialOver S q) =
      rename g (∑ q : TableauTabloid mu, v q • tabloidPolynomialOver S q)
    rw [map_sum]
    rw [← Equiv.sum_comp (MulAction.toPerm g)
      (fun q : TableauTabloid mu => v (g⁻¹ • q) • tabloidPolynomialOver (R := R) S q)]
    apply Finset.sum_congr rfl
    intro q _
    simp only [MulAction.toPerm_apply, inv_smul_smul, map_smul,
      tabloidPolynomialOver_smul]

theorem tabloidPolynomialLinearOver_polytabloid (S : StandardYoungTableau mu)
    (T : YoungTableau mu) :
    tabloidPolynomialLinearOver (R := R) S (polytabloidOver R T) =
      youngApply T (tableauCochargeMonomialOver S T) := by
  rw [polytabloidOver, map_sum]
  simp only [map_smul, tabloidPolynomialLinearOver_single, one_smul,
    tabloidPolynomialOver_smul, tabloidPolynomialOver_tabloid]
  rfl

def higherSpechtIntertwinerOver (S : StandardYoungTableau mu) :
    (spechtSubrepresentationOver R mu).toRepresentation.IntertwiningMap
      (polynomialRepresentation R mu.card) :=
  (tabloidPolynomialIntertwinerOver S).comp (spechtSubrepresentationOver R mu).subtype

@[simp] theorem higherSpechtIntertwinerOver_standard (S T : StandardYoungTableau mu) :
    higherSpechtIntertwinerOver (R := R) S (standardPolytabloidOver T) =
      higherSpechtPolynomial S T := by
  simp only [higherSpechtIntertwinerOver, Representation.IntertwiningMap.comp_apply,
    Subrepresentation.coe_subtype, tabloidPolynomialIntertwinerOver,
    Representation.IntertwiningMap.coe_mk, standardPolytabloidOver]
  exact tabloidPolynomialLinearOver_polytabloid S T.toTableau

abbrev partitionSpechtRepresentationOver (R : Type*) [CommRing R] {n : ℕ}
    (part : n.Partition) :=
  (spechtSubrepresentationOver R (YoungDiagram.ofPartition part)).toRepresentation.comp
    (finCongr (YoungDiagram.card_ofPartition part).symm).permCongrHom.toMonoidHom

def partitionHigherSpechtIntertwinerOver {n : ℕ} (part : n.Partition)
    (S : StandardYoungTableau (YoungDiagram.ofPartition part)) :
    Representation.IntertwiningMap (partitionSpechtRepresentationOver R part)
      (polynomialRepresentation R n) where
  toLinearMap := (MvPolynomial.rename (finCongr (YoungDiagram.card_ofPartition part))).toLinearMap ∘ₗ
    (higherSpechtIntertwinerOver S).toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    let e := finCongr (YoungDiagram.card_ofPartition part)
    have h := DFunLike.congr_fun ((higherSpechtIntertwinerOver (R := R) S).isIntertwining'
      (e.symm.permCongr g)) v
    change rename e
      (higherSpechtIntertwinerOver S
        ((spechtSubrepresentationOver R (YoungDiagram.ofPartition part)).toRepresentation
          (e.symm.permCongr g) v)) =
      rename g (rename e (higherSpechtIntertwinerOver S v))
    rw [show higherSpechtIntertwinerOver S
        ((spechtSubrepresentationOver R (YoungDiagram.ofPartition part)).toRepresentation
          (e.symm.permCongr g) v) =
        rename (e.symm.permCongr g) (higherSpechtIntertwinerOver S v) from h]
    rw [MvPolynomial.rename_rename, MvPolynomial.rename_rename]
    congr 1

def partitionGriffinIntertwinerOver {n : ℕ} (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (part : n.Partition) (i : PartitionGriffinCopies n lam hk s part) :
    Representation.IntertwiningMap (partitionSpechtRepresentationOver R part)
      (griffinRepresentation R n lam s) :=
  (quotientProjectionIntertwiner (griffinIdeal R n lam s)
    (permutationStable_griffinIdeal lam s)).comp
      ((symmetricMultiplicationIntertwiner
        (elementaryMultiplier n (n - lam.card) i.multiplier.rowLen)
        (elementaryMultiplier_isSymmetric n (n - lam.card) i.multiplier.rowLen)).comp
          (partitionHigherSpechtIntertwinerOver part i.left))

@[simp] theorem partitionGriffinIntertwinerOver_standard {n : ℕ}
    (lam : YoungDiagram) (hk : lam.card ≤ n) (s : ℕ) (part : n.Partition)
    (i : PartitionGriffinCopies n lam hk s part)
    (T : StandardYoungTableau (YoungDiagram.ofPartition part)) :
    partitionGriffinIntertwinerOver (R := R) lam hk s part i (standardPolytabloidOver T) =
      Ideal.Quotient.mk (griffinIdeal R n lam s)
        (rename (finCongr (YoungDiagram.card_ofPartition part))
          (higherSpechtPolynomial i.left T) *
          elementaryMultiplier n (n - lam.card) i.multiplier.rowLen) := by
  change Ideal.Quotient.mk (griffinIdeal R n lam s)
    (rename (finCongr (YoungDiagram.card_ofPartition part))
      (higherSpechtIntertwinerOver (R := R) i.left (standardPolytabloidOver T)) *
        elementaryMultiplier n (n - lam.card) i.multiplier.rowLen) = _
  rw [higherSpechtIntertwinerOver_standard]

end HigherSpecht
end
end CanonicalSource30

section CanonicalSource31
/- Source: HigherSpecht/AdmissibleSpechtDistinctness.lean -/



/-!
# Distinct shapes in every characteristic in which `n!` is nonzero

The proof uses actual column antisymmetrizers and James's row/column counting
lemma. It does not assume modular Specht classification or a decomposition
of the regular representation.
-/

noncomputable section
open Finset TauCeti TauCeti.YoungTableau Module
open scoped Classical

namespace HigherSpecht

theorem two_ne_zero_of_factorial_ne_zero {K : Type*} [Field K] {n : ℕ}
    (hfac : (n.factorial : K) ≠ 0) (hn : 2 ≤ n) : (2 : K) ≠ 0 := by
  have hd : 2 ∣ n.factorial := by simpa using Nat.factorial_dvd_factorial hn
  exact (natCast_isUnit_of_dvd_factorial (isUnit_iff_ne_zero.mpr hfac) hd).ne_zero

theorem transported_column_single_eq_zero {K : Type*} [Field K]
    {lam mu : YoungDiagram} (e : Fin lam.card ≃ Fin mu.card)
    (hfac : (lam.card.factorial : K) ≠ 0) (T : YoungTableau lam)
    (q : TableauTabloid mu) {x y : Fin mu.card} (hxy : x ≠ y)
    (hcol : colIndex T (e.symm x) = colIndex T (e.symm y))
    (hfix : Equiv.swap x y • q = q) :
    columnActionOver ((tabloidRepresentationOver K mu).comp e.permCongrHom.toMonoidHom)
      T (Pi.single q 1) = 0 := by
  have hne : e.symm x ≠ e.symm y := e.symm.injective.ne hxy
  have hcard : 2 ≤ lam.card := by
    have hx := (e.symm x).isLt
    have hy := (e.symm y).isLt
    have hval : (e.symm x).val ≠ (e.symm y).val := fun h => hne (Fin.ext h)
    omega
  have htwo := two_ne_zero_of_factorial_ne_zero hfac hcard
  have h2inj : Function.Injective (fun v : TabloidSpaceOver K mu => (2 : ℕ) • v) := by
    intro v w h
    ext q
    exact mul_left_cancel₀ htwo (by
      simpa only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat] using congrFun h q)
  apply columnActionOver_apply_eq_zero_of_odd_fix T _ h2inj
    (swap_mem_colSubgroup hcol) (Equiv.Perm.sign_swap hne)
  change tabloidRepresentationOver K mu (e.permCongrHom
    (Equiv.swap (e.symm x) (e.symm y))) (Pi.single q 1) = _
  have he : e.permCongrHom (Equiv.swap (e.symm x) (e.symm y)) = Equiv.swap x y := by
    change (e.symm.trans (Equiv.swap (e.symm x) (e.symm y))).trans e = _
    rw [Equiv.symm_trans_swap_trans, e.apply_symm_apply, e.apply_symm_apply]
  rw [he, tabloidRepresentationOver_single, hfix]

theorem rowLens_le_of_transported_column_ne_zero {K : Type*} [Field K]
    {lam mu : YoungDiagram} (e : Fin lam.card ≃ Fin mu.card)
    (hfac : (lam.card.factorial : K) ≠ 0) (T : YoungTableau lam)
    (v : TabloidSpaceOver K mu)
    (hv : columnActionOver
      ((tabloidRepresentationOver K mu).comp e.permCongrHom.toMonoidHom) T v ≠ 0)
    (k : ℕ) :
    (mu.rowLens.take k).sum ≤ (lam.rowLens.take k).sum := by
  have hex : ∃ q : TableauTabloid mu, columnActionOver
      ((tabloidRepresentationOver K mu).comp e.permCongrHom.toMonoidHom)
      T (Pi.single q 1) ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    have hsum : v = ∑ q : TableauTabloid mu, v q • Pi.single q 1 := by
      ext q
      simp [Pi.single_apply]
    rw [hsum, map_sum]
    simp only [map_smul, h, smul_zero, Finset.sum_const_zero]
  obtain ⟨q, hq⟩ := hex
  obtain ⟨U, rfl⟩ := tabloid_surjective (μ := mu) q
  apply YoungTableau.sum_take_rowLens_le_of_injective T U e.symm _ k
  intro x y hrow hcol
  by_contra hxy
  exact hq (transported_column_single_eq_zero e hfac T _ hxy hcol
    (smul_tabloid_eq_self_iff.mpr (swap_mem_rowSubgroup hrow)))

theorem columnActionOver_intertwiner {R V W : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    {lam : YoungDiagram} {rho : Representation R (Equiv.Perm (Fin lam.card)) V}
    {tau : Representation R (Equiv.Perm (Fin lam.card)) W}
    (f : rho.IntertwiningMap tau) (T : YoungTableau lam) (v : V) :
    f (columnActionOver rho T v) = columnActionOver tau T (f v) := by
  simp only [columnActionOver_apply, map_sum, map_smul, f.isIntertwining]

theorem columnActionOver_subrepresentation {R V : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] {lam : YoungDiagram}
    {rho : Representation R (Equiv.Perm (Fin lam.card)) V}
    (S : Subrepresentation rho) (T : YoungTableau lam) (v : S.toSubmodule) :
    ((columnActionOver S.toRepresentation T v : S.toSubmodule) : V) =
      columnActionOver rho T v := by
  simpa only [Subrepresentation.coe_subtype] using
    columnActionOver_intertwiner S.subtype T v

theorem rowLens_le_of_specht_embedding {K : Type*} [Field K]
    {lam mu : YoungDiagram} (e : Fin lam.card ≃ Fin mu.card)
    (hfac : (lam.card.factorial : K) ≠ 0)
    (f : (spechtSubrepresentationOver K lam).toRepresentation.IntertwiningMap
      ((tabloidRepresentationOver K mu).comp e.permCongrHom.toMonoidHom))
    (hf : Function.Injective f) (k : ℕ) :
    (mu.rowLens.take k).sum ≤ (lam.rowLens.take k).sum := by
  obtain ⟨T⟩ := YoungTableau.nonempty lam
  let v : (spechtSubrepresentationOver K lam).toSubmodule :=
    ⟨polytabloidOver K T, polytabloidOver_mem T⟩
  apply rowLens_le_of_transported_column_ne_zero e hfac T (f v) _ k
  rw [← columnActionOver_intertwiner]
  intro hz
  have hzero : columnActionOver (spechtSubrepresentationOver K lam).toRepresentation T v = 0 :=
    hf (hz.trans (map_zero f).symm)
  apply columnActionOver_polytabloid_ne_zero hfac T
  have h := congrArg Subtype.val hzero
  simpa only [columnActionOver_subrepresentation, v, ZeroMemClass.coe_zero] using h

def partitionSpechtEquivToDiagram {K : Type*} [Field K] {n : ℕ}
    {lam mu : n.Partition}
    (f : Representation.Equiv (partitionSpechtRepresentationOver K lam)
      (partitionSpechtRepresentationOver K mu)) :
    (spechtSubrepresentationOver K (YoungDiagram.ofPartition lam)).toRepresentation.IntertwiningMap
      ((spechtSubrepresentationOver K (YoungDiagram.ofPartition mu)).toRepresentation.comp
        (finCongr ((YoungDiagram.card_ofPartition lam).trans
          (YoungDiagram.card_ofPartition mu).symm)).permCongrHom.toMonoidHom) where
  toLinearMap := f.toLinearMap
  isIntertwining' g := by
    let el := (finCongr (YoungDiagram.card_ofPartition lam).symm).permCongrHom
    let em := (finCongr (YoungDiagram.card_ofPartition mu).symm).permCongrHom
    let e := (finCongr ((YoungDiagram.card_ofPartition lam).trans
      (YoungDiagram.card_ofPartition mu).symm)).permCongrHom
    have h := f.toIntertwiningMap.isIntertwining' (el.symm g)
    have he : em (el.symm g) = e g := by
      ext x
      simp [el, em, e, Equiv.permCongrHom_coe, Equiv.permCongr_apply, finCongr]
    simpa only [partitionSpechtRepresentationOver, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, el, em, e, MulEquiv.apply_symm_apply, he] using h

theorem partitionSpecht_dominates_of_equiv {K : Type*} [Field K] {n : ℕ}
    {lam mu : n.Partition} (hfac : (n.factorial : K) ≠ 0)
    (f : Representation.Equiv (partitionSpechtRepresentationOver K lam)
      (partitionSpechtRepresentationOver K mu)) : lam.Dominates mu := by
  let fd := partitionSpechtEquivToDiagram f
  let fm :
      (spechtSubrepresentationOver K (YoungDiagram.ofPartition lam)).toRepresentation.IntertwiningMap
        ((tabloidRepresentationOver K (YoungDiagram.ofPartition mu)).comp
          (finCongr ((YoungDiagram.card_ofPartition lam).trans
            (YoungDiagram.card_ofPartition mu).symm)).permCongrHom.toMonoidHom) :=
    { toLinearMap := (spechtSubrepresentationOver K (YoungDiagram.ofPartition mu)).toSubmodule.subtype
        ∘ₗ fd.toLinearMap
      isIntertwining' g := by
        apply LinearMap.ext
        intro v
        exact congrArg Subtype.val (DFunLike.congr_fun (fd.isIntertwining' g) v) }
  apply Nat.Partition.dominates_iff.mpr
  intro k
  have hf : Function.Injective fm := Subtype.val_injective.comp f.injective
  simpa only [YoungDiagram.rowLens_ofPartition_eq_sort_parts] using
    rowLens_le_of_specht_embedding
      (finCongr ((YoungDiagram.card_ofPartition lam).trans (YoungDiagram.card_ofPartition mu).symm))
      (by simpa only [YoungDiagram.card_ofPartition] using hfac) fm hf k

theorem partitionSpecht_eq_of_equiv {K : Type*} [Field K] {n : ℕ}
    {lam mu : n.Partition} (hfac : (n.factorial : K) ≠ 0)
    (f : Representation.Equiv (partitionSpechtRepresentationOver K lam)
      (partitionSpechtRepresentationOver K mu)) : lam = mu :=
  (partitionSpecht_dominates_of_equiv hfac f).antisymm
    (partitionSpecht_dominates_of_equiv hfac f.symm)

end HigherSpecht
end
end CanonicalSource31

section CanonicalSource32
/- Source: HigherSpecht/CyclicSimpleCriterion.lean -/



/-!
# A cyclic-vector criterion for simplicity

In a semisimple module, a cyclic vector is a simple generator if some algebra
operator has image in its scalar line and does not kill it. The argument uses
actual complements. It works over any field and does not use a positive form.
-/

noncomputable section

open scoped MonoidAlgebra

namespace HigherSpecht

section Algebra

variable {K A M : Type*} [Field K] [Ring A] [Algebra K A]
  [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]

/-- A rank-one algebra operator detecting a cyclic vector forces a
semisimple module to be simple. The image hypothesis is an actual scalar
multiple statement, not a dimension or irreducibility assumption. -/
theorem isSimpleModule_of_cyclic_rankOne
    [IsSemisimpleModule A M] (v : M)
    (hcyclic : Submodule.span A ({v} : Set M) = ⊤)
    (a : A) (hline : ∀ x : M, ∃ c : K, a • x = c • v)
    (hdetect : a • v ≠ 0) : IsSimpleModule A M := by
  have hv : v ≠ 0 := by
    intro h
    exact hdetect (by simp [h])
  letI : Nontrivial M := ⟨⟨v, 0, hv⟩⟩
  have htop (P : Submodule A M) (hvP : v ∈ P) : P = ⊤ := by
    apply top_unique
    rw [← hcyclic]
    exact Submodule.span_le.mpr (by simpa using hvP)
  refine { eq_bot_or_eq_top := ?_ }
  intro P
  obtain ⟨Q, hPQ⟩ := exists_isCompl P
  have hvsum : v ∈ P ⊔ Q := by rw [hPQ.sup_eq_top]; trivial
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hvsum
  obtain ⟨c, hc⟩ := hline x
  obtain ⟨d, hd⟩ := hline y
  by_cases hc0 : c = 0
  · have hd0 : d ≠ 0 := by
      intro hd0
      apply hdetect
      rw [← hxy, smul_add, hc, hd]
      simp [hc0, hd0]
    have hvQ : v ∈ Q := by
      apply ((Q.restrictScalars K).smul_mem_iff hd0).mp
      change d • v ∈ Q
      rw [← hd]
      exact Q.smul_mem a hy
    have hQ : Q = ⊤ := htop Q hvQ
    exact Or.inl (hPQ.disjoint.eq_bot_of_le (by rw [hQ]; exact le_top))
  · have hvP : v ∈ P := by
      apply ((P.restrictScalars K).smul_mem_iff hc0).mp
      change c • v ∈ P
      rw [← hc]
      exact P.smul_mem a hx
    exact Or.inr (htop P hvP)

end Algebra

section Group

variable {K G M : Type*} [Field K] [Group G] [Finite G]
  [NeZero (Nat.card G : K)] [AddCommGroup M]
  [Module K M] [Module K[G] M] [IsScalarTower K K[G] M]

/-- Maschke supplies the semisimplicity in the cyclic-vector criterion. -/
theorem isSimpleModule_of_finite_group_cyclic_rankOne
    (v : M) (hcyclic : Submodule.span K[G] ({v} : Set M) = ⊤)
    (a : K[G]) (hline : ∀ x : M, ∃ c : K, a • x = c • v)
    (hdetect : a • v ≠ 0) : IsSimpleModule K[G] M :=
  isSimpleModule_of_cyclic_rankOne v hcyclic a hline hdetect

end Group

end HigherSpecht
end
end CanonicalSource32

section CanonicalSource33
/- Source: HigherSpecht/AdmissibleSpechtSimplicity.lean -/



/-!
# Actual modular Specht irreducibility in the nonmodular range

Maschke applies because `n!` is nonzero in the field. The literal column
operator has scalar-line image, detects the cyclic polytabloid, and therefore
forces the actual polytabloid span to be simple. No modular classification
or standard-basis spanning theorem is used.
-/

noncomputable section
open Finset TauCeti TauCeti.YoungTableau Module
open scoped Classical MonoidAlgebra

namespace HigherSpecht

theorem span_asModule_singleton_eq_top_of_span_orbit
    {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
    (rho : Representation K G V) (v : V)
    (hv : Submodule.span K (Set.range (fun g => rho g v)) = ⊤) :
    Submodule.span K[G] ({rho.asModuleEquiv.symm v} : Set rho.asModule) = ⊤ := by
  let P := Submodule.span K[G] ({rho.asModuleEquiv.symm v} : Set rho.asModule)
  have hp : ∀ w ∈ Submodule.span K (Set.range (fun g => rho g v)),
      rho.asModuleEquiv.symm w ∈ P := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
        obtain ⟨g, rfl⟩ := hw
        rw [Representation.asModuleEquiv_symm_map_rho]
        exact P.smul_mem _ (Submodule.subset_span (Set.mem_singleton _))
    | zero => simpa only [map_zero] using P.zero_mem
    | add x y _ _ hx hy => simpa only [map_add] using P.add_mem hx hy
    | smul c x _ hx =>
        rw [Representation.asModuleEquiv_symm_map_smul]
        exact P.smul_mem _ hx
  apply top_unique
  intro x hx
  have hmem : rho.asModuleEquiv x ∈ Submodule.span K (Set.range (fun g => rho g v)) := by
    rw [hv]
    trivial
  simpa only [LinearEquiv.symm_apply_apply] using hp _ hmem

theorem spechtOver_cyclic {K : Type*} [Field K] {mu : YoungDiagram}
    (T : YoungTableau mu) :
    Submodule.span K (Set.range fun g : Equiv.Perm (Fin mu.card) =>
      (spechtSubrepresentationOver K mu).toRepresentation g
        ⟨polytabloidOver K T, polytabloidOver_mem T⟩) = ⊤ := by
  let S := spechtSubrepresentationOver K mu
  let P := Submodule.span K (Set.range fun g : Equiv.Perm (Fin mu.card) =>
    S.toRepresentation g ⟨polytabloidOver K T, polytabloidOver_mem T⟩)
  have h : ∀ w ∈ Submodule.span K (Set.range fun g =>
      tabloidRepresentationOver K mu g (polytabloidOver K T)),
      ∀ hw : w ∈ S, (⟨w, hw⟩ : S.toSubmodule) ∈ P := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
        obtain ⟨g, rfl⟩ := hw
        intro hmem
        exact Submodule.subset_span ⟨g, rfl⟩
    | zero => intro hmem; exact P.zero_mem
    | add x y hx hy ihx ihy =>
        intro hmem
        have hxS : x ∈ S := by
          change x ∈ (spechtSubrepresentationOver K mu).toSubmodule
          rw [spechtSubrepresentationOver_span_orbit T]
          exact hx
        have hyS : y ∈ S := by
          change y ∈ (spechtSubrepresentationOver K mu).toSubmodule
          rw [spechtSubrepresentationOver_span_orbit T]
          exact hy
        exact P.add_mem (ihx hxS) (ihy hyS)
    | smul c x hx ihx =>
        intro hmem
        have hxS : x ∈ S := by
          change x ∈ (spechtSubrepresentationOver K mu).toSubmodule
          rw [spechtSubrepresentationOver_span_orbit T]
          exact hx
        exact P.smul_mem c (ihx hxS)
  apply top_unique
  intro x hx
  have hxspan : x.val ∈ Submodule.span K (Set.range fun g =>
      tabloidRepresentationOver K mu g (polytabloidOver K T)) := by
    rw [← spechtSubrepresentationOver_span_orbit T]
    exact x.property
  exact h x.val hxspan x.property

set_option backward.isDefEq.respectTransparency false in
theorem spechtSubrepresentationOver_isIrreducible {K : Type*} [Field K]
    {mu : YoungDiagram} (hfac : (mu.card.factorial : K) ≠ 0) :
    (spechtSubrepresentationOver K mu).toRepresentation.IsIrreducible := by
  let S := spechtSubrepresentationOver K mu
  let rho : Representation K (Equiv.Perm (Fin mu.card)) S.toSubmodule := S.toRepresentation
  obtain ⟨T⟩ := YoungTableau.nonempty mu
  let v : S.toSubmodule := ⟨polytabloidOver K T, polytabloidOver_mem T⟩
  let vm := rho.asModuleEquiv.symm v
  letI : NeZero (Nat.card (Equiv.Perm (Fin mu.card)) : K) := ⟨by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] using hfac⟩
  apply (Representation.irreducible_iff_isSimpleModule_asModule rho).mpr
  apply isSimpleModule_of_finite_group_cyclic_rankOne
    (K := K) (G := Equiv.Perm (Fin mu.card)) (M := rho.asModule) vm
    (span_asModule_singleton_eq_top_of_span_orbit rho v (spechtOver_cyclic T))
    (columnElementOver K T)
  · intro x
    obtain ⟨c, hc⟩ := exists_columnActionOver_eq_smul T (rho.asModuleEquiv x).val
    refine ⟨c, ?_⟩
    apply rho.asModuleEquiv.injective
    apply Subtype.ext
    rw [Representation.asModuleEquiv_map_smul]
    simp only [map_smul, vm, LinearEquiv.apply_symm_apply, v]
    rw [Subrepresentation.coe_toRepresentation_asAlgebraHom_apply,
      ← columnActionOver_eq_asAlgebraHom]
    exact hc
  · intro hz
    apply columnActionOver_polytabloid_ne_zero hfac T
    have h := congrArg (fun x => (rho.asModuleEquiv x).val) hz
    rw [Representation.asModuleEquiv_map_smul] at h
    simp only [vm, LinearEquiv.apply_symm_apply, v, map_zero,
      ZeroMemClass.coe_zero] at h
    rw [Subrepresentation.coe_toRepresentation_asAlgebraHom_apply,
      ← columnActionOver_eq_asAlgebraHom] at h
    exact h

theorem partitionSpechtRepresentationOver_isIrreducible {K : Type*} [Field K]
    {n : ℕ} (hfac : (n.factorial : K) ≠ 0) (part : n.Partition) :
    Representation.IsIrreducible (partitionSpechtRepresentationOver K part) := by
  apply (MulEquiv.isIrreducible_comp_equiv_iff
    (finCongr (YoungDiagram.card_ofPartition part).symm).permCongrHom
    (spechtSubrepresentationOver K (YoungDiagram.ofPartition part)).toRepresentation).mpr
  exact spechtSubrepresentationOver_isIrreducible
    (by simpa only [YoungDiagram.card_ofPartition] using hfac)

end HigherSpecht
end
end CanonicalSource33

section CanonicalSource34
/- Source: HigherSpecht/AdmissibleFixedTableau.lean -/



/-! Fixed-tableau coefficient separation in the exact admissible
characteristics. The defining ideal is the actual Griffin ideal and the
functional is the integral coefficient functional, so no exponent-dependent
factorial and no additional condition on `s` enters the proof. -/

noncomputable section
open TauCeti TauCeti.YoungTableau Module

namespace HigherSpecht

theorem griffin_fixedTableau_linearIndependent_of_factorial_ne_zero
    {K : Type*} [Field K] {mu lam : YoungDiagram}
    {hk : lam.card ≤ mu.card} {s : ℕ}
    (hfac : (mu.card.factorial : K) ≠ 0)
    (T : StandardYoungTableau mu) (hs : lam.colLen 0 ≤ s) :
    LinearIndependent K (fun i : FixedGriffinIndex mu lam hk s =>
      Ideal.Quotient.mk (griffinIdeal K mu.card lam s) (fixedGriffinPolynomial T i)) := by
  let N := (griffinIdeal K mu.card lam s).restrictScalars K
  let L : FixedGriffinIndex mu lam hk s → Module.Dual K (GriffinRing K mu.card lam s) :=
    fun i => N.liftQ (fixedGriffinFunctional T i) (fixedGriffinFunctional_kills T hs i)
  apply linearIndependent_of_pairing_key (fixedGriffinKey T) L
  · intro i j hne hkey
    exact fixedGriffinFunctional_offDiagonal T i j hne hkey
  · intro i
    change fixedGriffinFunctional (R := K) T i (fixedGriffinPolynomial T i) ≠ 0
    rw [fixedGriffinFunctional_diagonal]
    exact mul_ne_zero
      (rowFillingStabilizers_card_isUnit (isUnit_iff_ne_zero.mpr hfac) T.toTableau
        (transportedCocharge i.left T.toTableau)).ne_zero
      (fixedWitnessPermutations_card_isUnit (isUnit_iff_ne_zero.mpr hfac)
        (griffinWitnessGroup i.left T.toTableau lam.card hk)
        (griffinWitnessRejection i.left T.toTableau i.multiplier lam.card hk s)
        (fun j => (colIndex T.toTableau j : ℤ))).ne_zero

theorem griffin_fixedTableau_linearIndependent_of_char_gt
    {K : Type*} [Field K] {p : ℕ} [CharP K p] {mu lam : YoungDiagram}
    {hk : lam.card ≤ mu.card} {s : ℕ} (hp : mu.card < p)
    (T : StandardYoungTableau mu) (hs : lam.colLen 0 ≤ s) :
    LinearIndependent K (fun i : FixedGriffinIndex mu lam hk s =>
      Ideal.Quotient.mk (griffinIdeal K mu.card lam s) (fixedGriffinPolynomial T i)) :=
  griffin_fixedTableau_linearIndependent_of_factorial_ne_zero
    (factorial_ne_zero_of_char_gt hp) T hs

end HigherSpecht
end
end CanonicalSource34

section CanonicalSource35
/- Source: HigherSpecht/AlgebraicallyClosedCopies.lean -/



/-!
# Complete copies over an algebraically closed coefficient field

This is the ordinary simple-module evaluation theorem, applied to genuinely
independent source vectors and genuinely independent equivariant maps.
Neither a classification nor a completeness assertion for the family of
simple modules is needed.
-/

noncomputable section
open Module TauCeti
open scoped Classical TensorProduct DirectSum MonoidAlgebra

namespace HigherSpecht

def intertwinerValueOver {K G V M : Type*} [Field K] [Group G]
    [AddCommGroup V] [Module K V] [AddCommGroup M] [Module K M]
    (sigma : Representation K G V) (rho : Representation K G M) (v : V) :
    sigma.IntertwiningMap rho →ₗ[K] M where
  toFun f := f v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Tensor-family independence and its injective image, proved over abstract
modules so representation coercions never enter the direct-sum calculation. -/
private theorem independent_directSum_tensor_image
    {K J : Type*} [Field K] [DecidableEq J]
    {P Q : J → Type*} {M : Type*}
    [∀ j, AddCommGroup (P j)] [∀ j, Module K (P j)]
    [∀ j, AddCommGroup (Q j)] [∀ j, Module K (Q j)]
    [AddCommGroup M] [Module K M] {A I : J → Type*}
    (a : ∀ j, A j → P j) (v : ∀ j, I j → Q j)
    (ha : ∀ j, LinearIndependent K (a j))
    (hv : ∀ j, LinearIndependent K (v j))
    (F : (Π₀ j, P j ⊗[K] Q j) →ₗ[K] M) (hF : Function.Injective F)
    (b : (Σ j, A j × I j) → M)
    (hb : ∀ z, F (DFinsupp.single z.1
      (a z.1 z.2.1 ⊗ₜ[K] v z.1 z.2.2)) = b z) :
    LinearIndependent K b := by
  have ht (j : J) : LinearIndependent K
      (fun z : A j × I j => a j z.1 ⊗ₜ[K] v j z.2) :=
    LinearIndependent.tmul_of_isDomain (R := K) (M := P j) (N := Q j)
      (ι := A j) (κ := I j) (v := a j) (w := v j) (ha j) (hv j)
  have hs : LinearIndependent K (fun z : Σ j, A j × I j =>
      (DFinsupp.single z.1 (a z.1 z.2.1 ⊗ₜ[K] v z.1 z.2.2) :
        Π₀ j, P j ⊗[K] Q j)) :=
    DFinsupp.linearIndependent_single (R := K) (M := fun j => P j ⊗[K] Q j)
      (φ := fun j => A j × I j) (fun j (z : A j × I j) => a j z.1 ⊗ₜ[K] v j z.2) ht
  have hm : LinearIndependent K (fun z : Σ j, A j × I j =>
      F (DFinsupp.single z.1 (a z.1 z.2.1 ⊗ₜ[K] v z.1 z.2.2))) :=
    LinearIndependent.map' (R := K) (M := Π₀ j, P j ⊗[K] Q j) (M' := M)
      (ι := Σ j, A j × I j)
      (v := fun z : Σ j, A j × I j =>
        DFinsupp.single z.1 (a z.1 z.2.1 ⊗ₜ[K] v z.1 z.2.2))
      hs F (LinearMap.ker_eq_bot.mpr hF)
  exact Eq.mp (congrArg (fun w : (Σ j, A j × I j) → M => LinearIndependent K w)
    (funext hb)) hm

theorem independent_simple_intertwiner_copies
    {K G J : Type*} [Field K] [IsAlgClosed K] [Group G] [Finite G]
    {V : J → Type*} [∀ j, AddCommGroup (V j)] [∀ j, Module K (V j)]
    (sigma : ∀ j, Representation K G (V j))
    [∀ j, (sigma j).IsIrreducible]
    (hdistinct : ∀ i j, Nonempty ((sigma i).Equiv (sigma j)) → i = j)
    {M : Type*} [AddCommGroup M] [Module K M]
    (rho : Representation K G M) {A I : J → Type*}
    (a : ∀ j, A j → V j)
    (f : ∀ j, I j → (sigma j).IntertwiningMap rho)
    (v0 : ∀ j, V j)
    (ha : ∀ j, LinearIndependent K (a j))
    (hf : ∀ j, LinearIndependent K (fun i => f j i (v0 j))) :
    LinearIndependent K (fun z : Σ j, A j × I j => f z.1 z.2.2 (a z.1 z.2.1)) := by
  let S (j : J) := (sigma j).asModule
  let av (j : J) (i : A j) : S j := (sigma j).asModuleEquiv.symm (a j i)
  let fv (j : J) (i : I j) : S j →ₗ[K[G]] rho.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule (sigma j) rho (f j i)
  have ha' (j : J) : LinearIndependent K (av j) :=
    (ha j).map' (sigma j).asModuleEquiv.symm.toLinearMap
      (LinearMap.ker_eq_bot.mpr (sigma j).asModuleEquiv.symm.injective)
  have hf' (j : J) : LinearIndependent K (fv j) := by
    have hmaps : LinearIndependent K (f j) :=
      LinearIndependent.of_comp (intertwinerValueOver (sigma j) rho (v0 j)) (hf j)
    exact hmaps.map'
      (Representation.IntertwiningMap.equivLinearMapAsModule (sigma j) rho).toLinearMap
      (LinearMap.ker_eq_bot.mpr
        (Representation.IntertwiningMap.equivLinearMapAsModule (sigma j) rho).injective)
  have hdist : ∀ i j, Nonempty (S i ≃ₗ[K[G]] S j) → i = j := by
    rintro i j ⟨e⟩
    let g := (Representation.IntertwiningMap.equivLinearMapAsModule (sigma i) (sigma j)).symm
      e.toLinearMap
    have hg : Function.Bijective g := e.bijective
    exact hdistinct i j ⟨g.ofBijective hg⟩
  let F : (Π₀ j, S j ⊗[K] (S j →ₗ[K[G]] rho.asModule)) →ₗ[K] M :=
    rho.asModuleEquiv.toLinearMap ∘ₗ
      (directSumIsotypicEval K K[G] S rho.asModule).restrictScalars K
  have hF : Function.Injective F := rho.asModuleEquiv.injective.comp
    (directSumIsotypicEval_injective K S hdist)
  apply independent_directSum_tensor_image (K := K) (P := S)
    (Q := fun j => S j →ₗ[K[G]] rho.asModule) av fv ha' hf' F hF
    (fun z : Σ j, A j × I j => f z.1 z.2.2 (a z.1 z.2.1))
  intro z
  change rho.asModuleEquiv (directSumIsotypicEval K K[G] S rho.asModule
    (DFinsupp.single z.1 (av z.1 z.2.1 ⊗ₜ[K] fv z.1 z.2.2))) = _
  rw [directSumIsotypicEval_single, isotypicEval_tmul]
  have heval : rho.asModuleEquiv (fv z.1 z.2.2 (av z.1 z.2.1)) =
      f z.1 z.2.2 ((sigma z.1).asModuleEquiv (av z.1 z.2.1)) :=
    Representation.IntertwiningMap.equivLinearMapAsModule_apply
      (f z.1 z.2.2) (av z.1 z.2.1)
  exact heval.trans (congrArg (f z.1 z.2.2)
    ((sigma z.1).asModuleEquiv.apply_symm_apply (a z.1 z.2.1)))

end HigherSpecht
end
end CanonicalSource35

section CanonicalSource36
/- Source: HigherSpecht/AdmissibleGriffinIndependence.lean -/



/-!
# The complete prescribed family in every admissible characteristic

Actual integral coefficient separation, actual modular Specht modules, and
the simple-module evaluation map supply independence of all right tableaux
and all shapes. Extension to the algebraic closure is used only for that
general evaluation theorem and is then descended through the literal
coefficient map of the quotient.
-/

noncomputable section
open TauCeti TauCeti.YoungTableau Module MvPolynomial
open scoped Classical TensorProduct

namespace HigherSpecht

@[simp] theorem partitionGriffinIntertwinerOver_family
    {K : Type*} [Field K] {n : ℕ} (lam : YoungDiagram) (hk : lam.card ≤ n) (s : ℕ)
    (z : PartitionGriffinVectorIndex n lam hk s) :
    partitionGriffinIntertwinerOver (R := K) lam hk s z.1 z.2.2
        (standardPolytabloidOver z.2.1) =
      griffinFamily K n lam hk s (partitionGriffinIndex z) := by
  rw [partitionGriffinIntertwinerOver_standard]
  rfl

theorem griffin_fixedTableau_renamed_independent_of_factorial_ne_zero
    {K : Type*} [Field K] {mu lam : YoungDiagram} {n s : ℕ}
    (hn : mu.card = n) (hk : lam.card ≤ n) (hfac : (n.factorial : K) ≠ 0)
    (T : StandardYoungTableau mu) (hheight : lam.colLen 0 ≤ s) :
    LinearIndependent K (fun i : FixedGriffinIndex mu lam (by omega) s =>
      Ideal.Quotient.mk (griffinIdeal K n lam s)
        (rename (finCongr hn) (higherSpechtPolynomial i.left T) *
          elementaryMultiplier n (n - lam.card) i.multiplier.rowLen)) := by
  subst n
  simpa only [finCongr_refl, Equiv.coe_refl, rename_id_apply,
    fixedGriffinPolynomial] using
    griffin_fixedTableau_linearIndependent_of_factorial_ne_zero (hk := hk) hfac T hheight

theorem griffinFamily_linearIndependent_algClosed
    (K : Type*) [Field K] [IsAlgClosed K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) (s : ℕ)
    (hfac : (n.factorial : K) ≠ 0) (hheight : lam.colLen 0 ≤ s) :
    LinearIndependent K (griffinFamily K n lam hk s) := by
  let sigma (part : n.Partition) := partitionSpechtRepresentationOver K part
  letI (part : n.Partition) : Representation.IsIrreducible (sigma part) :=
    partitionSpechtRepresentationOver_isIrreducible hfac part
  let a (part : n.Partition) (T : StandardYoungTableau (YoungDiagram.ofPartition part)) :=
    standardPolytabloidOver (R := K) T
  let f (part : n.Partition) (i : PartitionGriffinCopies n lam hk s part) :=
    partitionGriffinIntertwinerOver (R := K) lam hk s part i
  let T0 (part : n.Partition) :=
    StandardYoungTableau.rowSuperstandard (YoungDiagram.ofPartition part)
  have hf (part : n.Partition) : LinearIndependent K (fun i => f part i (a part (T0 part))) := by
    have h := griffin_fixedTableau_renamed_independent_of_factorial_ne_zero
      (YoungDiagram.card_ofPartition part) hk hfac (T0 part) hheight
    simpa only [f, a, partitionGriffinIntertwinerOver_standard] using h
  have hfull := independent_simple_intertwiner_copies sigma
    (fun i j ⟨e⟩ => partitionSpecht_eq_of_equiv hfac e)
    (griffinRepresentation K n lam s) a f (fun part => a part (T0 part))
    (fun part => linearIndependent_standardPolytabloidOver _) hf
  have hfamily : (fun z : PartitionGriffinVectorIndex n lam hk s =>
      f z.1 z.2.2 (a z.1 z.2.1)) =
      griffinFamily K n lam hk s ∘ partitionGriffinIndexEquiv n lam hk s := by
    funext z
    exact partitionGriffinIntertwinerOver_family lam hk s z
  have hindex : LinearIndependent K
      (griffinFamily K n lam hk s ∘ partitionGriffinIndexEquiv n lam hk s) :=
    Eq.mp (congrArg
      (fun v : PartitionGriffinVectorIndex n lam hk s → GriffinRing K n lam s =>
        LinearIndependent K v) hfamily) hfull
  have h := hindex.comp (partitionGriffinIndexEquiv n lam hk s).symm
    (partitionGriffinIndexEquiv n lam hk s).symm.injective
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using h

def griffinCoefficientExtension (K L : Type*) [Field K] [Field L] [Algebra K L]
    (n : ℕ) (lam : YoungDiagram) (s : ℕ) :
    GriffinRing K n lam s →ₗ[K] GriffinRing L n lam s :=
  ((griffinBaseChangeEquiv K L n lam s).toLinearEquiv.toLinearMap.restrictScalars K) ∘ₗ
    TensorProduct.mk K L (GriffinRing K n lam s) 1

@[simp] theorem griffinCoefficientExtension_family
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n) (s : ℕ)
    (i : GriffinIndex n lam hk s) :
    griffinCoefficientExtension K L n lam s (griffinFamily K n lam hk s i) =
      griffinFamily L n lam hk s i := by
  exact griffinBaseChangeEquiv_family n lam hk s i

theorem griffinFamily_linearIndependent_of_factorial_ne_zero
    (K : Type*) [Field K] (n : ℕ) (lam : YoungDiagram)
    (hk : lam.card ≤ n) (s : ℕ) (hfac : (n.factorial : K) ≠ 0)
    (hheight : lam.colLen 0 ≤ s) :
    LinearIndependent K (griffinFamily K n lam hk s) := by
  let L := AlgebraicClosure K
  have hfacL : (n.factorial : L) ≠ 0 := by
    intro hz
    apply hfac
    apply (algebraMap K L).injective
    simpa only [map_natCast, map_zero] using hz
  have hL := griffinFamily_linearIndependent_algClosed L n lam hk s hfacL hheight
  have hK : LinearIndependent K (griffinFamily L n lam hk s) := hL.restrict_scalars' K
  apply LinearIndependent.of_comp (griffinCoefficientExtension K L n lam s)
  simpa only [Function.comp_def, griffinCoefficientExtension_family] using hK

end HigherSpecht
end
end CanonicalSource36

section CanonicalSource37
/- Source: HigherSpecht/AdmissibleBases.lean -/



/-!
# The exact characteristic range of the prescribed bases

The prescribed bases retain their polynomial representatives, prefix
eligibility, both standard tableaux, and the complete multiplier rectangle.
The finite combinatorial count is independent of the coefficient field.
The pairing and the factorial obstruction give the exact field-characteristic
range for these unnormalized families.
-/

noncomputable section
open TauCeti Module
open scoped Classical

namespace HigherSpecht

theorem factorial_ne_zero_iff_characteristic_range
    (K : Type*) [Field K] (n : ℕ) :
    (n.factorial : K) ≠ 0 ↔ ringChar K = 0 ∨ n < ringChar K := by
  constructor
  · intro hfac
    by_cases hp : ringChar K = 0
    · exact Or.inl hp
    · right
      by_contra h
      apply hfac
      exact (CharP.cast_eq_zero_iff K (ringChar K) _).mpr
        (Nat.dvd_factorial (Nat.pos_of_ne_zero hp) (Nat.le_of_not_gt h))
  · rintro (hp | hp)
    · letI : CharZero K := (CharP.ringChar_zero_iff_CharZero K).mp hp
      exact Nat.cast_ne_zero.mpr n.factorial_ne_zero
    · exact factorial_ne_zero_of_char_gt hp

def griffinPrescribedBasisAdmissible
    (K : Type*) [Field K] (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s)
    (hfac : (n.factorial : K) ≠ 0) :
    Basis (GriffinIndex n lam hk s) K (GriffinRing K n lam s) := by
  letI := (finite_griffinStaircaseExponents (n := n) (μ := lam) s hs hheight).fintype
  letI : FiniteDimensional K (GriffinRing K n lam s) :=
    Module.Finite.of_basis (griffinStandardMonomialBasis hk s hs hheight)
  apply basisOfLinearIndependentOfCardEqFinrank' (griffinFamily K n lam hk s)
    (griffinFamily_linearIndependent_of_factorial_ne_zero K n lam hk s hfac hheight)
  rw [finrank_griffin_eq_staircase_card K hk s hs hheight, ← Nat.card_eq_fintype_card]
  exact griffin_index_card_eq_staircase n lam hk s hs hheight

@[simp] theorem griffinPrescribedBasisAdmissible_apply
    (K : Type*) [Field K] (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s)
    (hfac : (n.factorial : K) ≠ 0) (i : GriffinIndex n lam hk s) :
    griffinPrescribedBasisAdmissible K n lam hk s hs hheight hfac i =
      griffinFamily K n lam hk s i := by
  simp only [griffinPrescribedBasisAdmissible, coe_basisOfLinearIndependentOfCardEqFinrank']

theorem griffin_specifiedBasis_of_factorial_ne_zero
    (K : Type*) [Field K] (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s)
    (hfac : (n.factorial : K) ≠ 0) :
    IsSpecifiedBasis (R := K) (griffinFamily K n lam hk s) :=
  ⟨griffinPrescribedBasisAdmissible K n lam hk s hs hheight hfac,
    griffinPrescribedBasisAdmissible_apply K n lam hk s hs hheight hfac⟩

theorem untruncatedVectorFamily_independent_of_finite_independence
    (R : Type*) [CommRing R] (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (hb : ∀ s : ℕ, 0 < s → lam.colLen 0 ≤ s →
      LinearIndependent R (griffinFamily R n lam hk s)) :
    LinearIndependent R (untruncatedVectorFamily R n lam hk) := by
  apply linearIndependent_iff_finset_linearIndependent.mpr
  intro t
  have h := (hb (finiteGriffinBound t)
    (finiteGriffinBound_pos t) (finiteGriffinBound_height t)).comp
      (finiteUntruncatedToGriffin t) (finiteUntruncatedToGriffin_injective t)
  apply LinearIndependent.of_comp
    (untruncatedToGriffinProjection R n lam (finiteGriffinBound t)).toLinearMap
  simpa only [Function.comp_def, AlgHom.toLinearMap_apply,
    untruncatedToGriffinProjection_family] using h

def untruncatedVectorBasisFromAnyFiniteBases
    (R : Type*) [CommRing R] (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (hb : ∀ s : ℕ, 0 < s → lam.colLen 0 ≤ s →
      IsSpecifiedBasis (R := R) (griffinFamily R n lam hk s)) :
    Basis (UntruncatedVectorIndex n lam hk) R (UntruncatedRing R n lam) := by
  apply Basis.mk
  · apply untruncatedVectorFamily_independent_of_finite_independence R n lam hk
    intro s hs hh
    obtain ⟨B, hB⟩ := hb s hs hh
    simpa only [← funext hB] using B.linearIndependent
  · exact untruncatedVectorFamily_spans_of_finite_bases R n lam hk hb

@[simp] theorem untruncatedVectorBasisFromAnyFiniteBases_apply
    (R : Type*) [CommRing R] (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (hb : ∀ s : ℕ, 0 < s → lam.colLen 0 ≤ s →
      IsSpecifiedBasis (R := R) (griffinFamily R n lam hk s))
    (i : UntruncatedVectorIndex n lam hk) :
    untruncatedVectorBasisFromAnyFiniteBases R n lam hk hb i =
      untruncatedVectorFamily R n lam hk i := by
  simp only [untruncatedVectorBasisFromAnyFiniteBases, Basis.mk_apply]

def springerPrescribedBasisFromAnyFiniteBases
    (R : Type*) [CommRing R] (lam : YoungDiagram)
    (hb : ∀ s : ℕ, 0 < s → lam.colLen 0 ≤ s →
      IsSpecifiedBasis (R := R) (griffinFamily R lam.card lam le_rfl s)) :
    Basis (SpringerIndex lam) R (SpringerRing R lam) :=
  (untruncatedVectorBasisFromAnyFiniteBases R lam.card lam le_rfl hb).reindex
    (springerUntruncatedVectorIndexEquiv lam).symm

@[simp] theorem springerPrescribedBasisFromAnyFiniteBases_apply
    (R : Type*) [CommRing R] (lam : YoungDiagram)
    (hb : ∀ s : ℕ, 0 < s → lam.colLen 0 ≤ s →
      IsSpecifiedBasis (R := R) (griffinFamily R lam.card lam le_rfl s))
    (i : SpringerIndex lam) :
    springerPrescribedBasisFromAnyFiniteBases R lam hb i = springerFamily R lam i := by
  change ((untruncatedVectorBasisFromAnyFiniteBases R lam.card lam le_rfl hb).reindex
    (springerUntruncatedVectorIndexEquiv lam).symm) i =
      (springerFamily R lam i : UntruncatedRing R lam.card lam)
  rw [Basis.reindex_apply, untruncatedVectorBasisFromAnyFiniteBases_apply]
  exact springerUntruncatedVectorIndexEquiv_family R lam i

def springerPrescribedBasisAdmissible (K : Type*) [Field K] (lam : YoungDiagram)
    (hfac : (lam.card.factorial : K) ≠ 0) :
    Basis (SpringerIndex lam) K (SpringerRing K lam) :=
  springerPrescribedBasisFromAnyFiniteBases K lam
    (fun s hs hh => griffin_specifiedBasis_of_factorial_ne_zero K lam.card lam le_rfl s hs hh hfac)

@[simp] theorem springerPrescribedBasisAdmissible_apply
    (K : Type*) [Field K] (lam : YoungDiagram) (hfac : (lam.card.factorial : K) ≠ 0)
    (i : SpringerIndex lam) :
    springerPrescribedBasisAdmissible K lam hfac i = springerFamily K lam i :=
  springerPrescribedBasisFromAnyFiniteBases_apply K lam _ i

theorem springer_specifiedBasis_of_factorial_ne_zero
    (K : Type*) [Field K] (lam : YoungDiagram) (hfac : (lam.card.factorial : K) ≠ 0) :
    IsSpecifiedBasis (R := K) (springerFamily K lam) :=
  ⟨springerPrescribedBasisAdmissible K lam hfac,
    springerPrescribedBasisAdmissible_apply K lam hfac⟩

/-- The full field-range assertion for the literal finite Griffin family. -/
theorem corollary_8_1_griffin_characteristic (K : Type*) [Field K] :
    GriffinCharacteristicTarget K := by
  intro n lam hk s hlam hheight
  have hs := (height_pos_of_card_pos lam hlam).trans_le hheight
  constructor
  · intro hB
    by_cases hp : ringChar K = 0
    · exact Or.inl hp
    · right
      by_contra h
      exact not_griffinBasis_of_small_characteristic (Nat.pos_of_ne_zero hp)
        n lam hk s hs (Nat.le_of_not_gt h) hB
  · intro hchar
    exact griffin_specifiedBasis_of_factorial_ne_zero K n lam hk s hs hheight
      ((factorial_ne_zero_iff_characteristic_range K n).mpr hchar)

/-- The original Springer family has the same exact characteristic range. -/
theorem corollary_8_1_springer_characteristic (K : Type*) [Field K] :
    SpringerCharacteristicTarget K := by
  intro lam
  constructor
  · intro hB
    by_cases hp : ringChar K = 0
    · exact Or.inl hp
    · right
      by_contra h
      exact not_springerBasis_of_small_characteristic (Nat.pos_of_ne_zero hp)
        lam (Nat.le_of_not_gt h) hB
  · intro hchar
    exact springer_specifiedBasis_of_factorial_ne_zero K lam
      ((factorial_ne_zero_iff_characteristic_range K lam.card).mpr hchar)

end HigherSpecht
end
end CanonicalSource37

section CanonicalSource38
/- Source: HigherSpecht/IntegralInterpolation.lean -/



/-!
# Integer interpolation at a unimodular set of coordinates

If integer vectors have a square coordinate minor of determinant a unit,
then every integer vector in their rational span already lies in their
integer span.  The proof uses the literal integer inverse of that minor.
No rational coefficient is transported into a field of positive
characteristic.
-/

noncomputable section
open Matrix Module
open scoped Classical

namespace HigherSpecht

theorem exists_integer_expansion_of_unimodular_coordinates
    {I Q : Type*} [Fintype I] [DecidableEq I]
    (a : I → Q → ℤ) (pivot : I → Q) (v : Q → ℤ)
    (hunit : IsUnit (Matrix.of (fun i j => a j (pivot i))).det)
    (hQ : ∃ d : I → ℚ, ∀ q, ∑ i, d i * (a i q : ℚ) = (v q : ℚ)) :
    ∃ c : I → ℤ, ∀ q, ∑ i, c i * a i q = v q := by
  let A : Matrix I I ℤ := Matrix.of (fun i j => a j (pivot i))
  let b : I → ℤ := fun i => v (pivot i)
  let c : I → ℤ := A⁻¹ *ᵥ b
  let AQ : Matrix I I ℚ := A.map (Int.castRingHom ℚ)
  let BQ : Matrix I I ℚ := (A⁻¹).map (Int.castRingHom ℚ)
  obtain ⟨d, hd⟩ := hQ
  have hAd : AQ *ᵥ d = fun i => (b i : ℚ) := by
    funext i
    change (∑ j, (a j (pivot i) : ℚ) * d j) = (v (pivot i) : ℚ)
    simpa only [mul_comm] using hd (pivot i)
  have hBA : BQ * AQ = 1 := by
    change (A⁻¹).map (Int.castRingHom ℚ) * A.map (Int.castRingHom ℚ) = 1
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul A hunit]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hcd : (fun i => (c i : ℚ)) = d := by
    calc
      (fun i => (c i : ℚ)) = BQ *ᵥ (fun i => (b i : ℚ)) := by
        funext i
        exact (Int.castRingHom ℚ).map_mulVec A⁻¹ b i
      _ = BQ *ᵥ (AQ *ᵥ d) := by rw [hAd]
      _ = d := by rw [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]
  refine ⟨c, fun q => ?_⟩
  apply Int.cast_injective (α := ℚ)
  simp only [Int.cast_sum, Int.cast_mul]
  calc
    ∑ i, (c i : ℚ) * (a i q : ℚ) = ∑ i, d i * (a i q : ℚ) := by
      exact Finset.sum_congr rfl (fun i _ => by rw [congrFun hcd i])
    _ = (v q : ℚ) := hd q

theorem integer_span_of_rational_span_of_unimodular_coordinates
    {I Q : Type*} [Fintype I] [DecidableEq I]
    (a : I → Q → ℤ) (pivot : I → Q) (v : Q → ℤ)
    (hunit : IsUnit (Matrix.of (fun i j => a j (pivot i))).det)
    (hQ : (fun q => (v q : ℚ)) ∈
      Submodule.span ℚ (Set.range (fun i q => (a i q : ℚ)))) :
    v ∈ Submodule.span ℤ (Set.range a) := by
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hQ
  obtain ⟨c, hc⟩ := exists_integer_expansion_of_unimodular_coordinates a pivot v hunit
    ⟨d, fun q => by simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun hd q⟩
  apply (Submodule.mem_span_range_iff_exists_fun ℤ).mpr
  refine ⟨c, funext fun q => ?_⟩
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hc q

end HigherSpecht
end
end CanonicalSource38

section CanonicalSource39
/- Source: HigherSpecht/IntegralStandardBasis.lean -/



/-!
# The ordinary standard Specht basis over every commutative ring

The distinguished tabloid-coordinate matrix is block triangular by the
finite rank of the actual tabloid-dominance preorder.  Its diagonal blocks are identity matrices, so
its determinant is the integer one.  Rational straightening therefore
has integer coefficients by unimodular interpolation.  Transporting only
those integer identities gives spanning over an arbitrary coefficient
ring, including fields of admissible positive characteristic.
-/

noncomputable section
open Finset TauCeti TauCeti.YoungTableau Module Matrix
open scoped Classical

namespace HigherSpecht

theorem standard_polytabloid_pivot_zero {R : Type*} [CommRing R]
    {mu : YoungDiagram} (T U : StandardYoungTableau mu) (hne : T ≠ U)
    (hw : tabloidDominanceRank U.toTableau ≤ tabloidDominanceRank T.toTableau) :
    polytabloidOver R U.toTableau (tabloid T.toTableau) = 0 := by
  apply polytabloidOver_eq_zero_of_forall_ne
  intro g hg htab
  have hdom := tabloidDominates_relabel_of_mem_colSubgroup U hg
  have hrow : rowIndex (relabel g U.toTableau) = rowIndex T.toTableau := by
    rw [← tabloid_eq_iff_rowIndex_eq, tabloid_relabel, htab]
  have hweight : tabloidDominanceRank U.toTableau ≤
      tabloidDominanceRank (relabel g U.toTableau) := by
    rw [tabloidDominanceRank_congr hrow]
    exact hw
  have heq : U = T := StandardYoungTableau.rowIndex_injective mu
    ((rowIndex_eq_of_dominates_rank hdom hweight).symm.trans hrow)
  exact hne heq.symm

def standardPolytabloidPivotMatrix (R : Type*) [CommRing R] (mu : YoungDiagram) :
    Matrix (StandardYoungTableau mu) (StandardYoungTableau mu) R :=
  Matrix.of fun T U => polytabloidOver R U.toTableau (tabloid T.toTableau)

theorem standardPolytabloidPivotMatrix_blockTriangular
    (R : Type*) [CommRing R] (mu : YoungDiagram) :
    (standardPolytabloidPivotMatrix R mu).BlockTriangular
      (fun T => tabloidDominanceRank T.toTableau) := by
  intro T U hlt
  exact standard_polytabloid_pivot_zero T U
    (fun h => (ne_of_lt hlt) (congrArg (fun V => tabloidDominanceRank V.toTableau) h.symm))
    hlt.le

theorem standardPolytabloidPivotMatrix_block_eq_one
    (R : Type*) [CommRing R] (mu : YoungDiagram) (w : ℕ) :
    (standardPolytabloidPivotMatrix R mu).toSquareBlock
      (fun T => tabloidDominanceRank T.toTableau) w = 1 := by
  ext T U
  change polytabloidOver R U.val.toTableau (tabloid T.val.toTableau) = _
  by_cases h : T = U
  · subst U
    simp only [polytabloidOver_tabloid, Matrix.one_apply_eq]
  · have hne : T.val ≠ U.val := fun he => h (Subtype.ext he)
    rw [standard_polytabloid_pivot_zero T.val U.val hne (by rw [T.property, U.property])]
    exact (Matrix.one_apply_ne h).symm

@[simp] theorem standardPolytabloidPivotMatrix_det
    (R : Type*) [CommRing R] (mu : YoungDiagram) :
    (standardPolytabloidPivotMatrix R mu).det = 1 := by
  rw [(standardPolytabloidPivotMatrix_blockTriangular R mu).det]
  simp only [standardPolytabloidPivotMatrix_block_eq_one, Matrix.det_one,
    Finset.prod_const_one]

theorem polytabloidOver_integer_expansion {mu : YoungDiagram} (T : YoungTableau mu) :
    ∃ c : StandardYoungTableau mu → ℤ, ∀ q,
      ∑ U, c U * polytabloidOver ℤ U.toTableau q = polytabloidOver ℤ T q := by
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp
    (polytabloid_mem_span_polytabloid_standard T)
  apply exists_integer_expansion_of_unimodular_coordinates
    (fun U : StandardYoungTableau mu => polytabloidOver ℤ U.toTableau)
    (fun U => tabloid U.toTableau) (polytabloidOver ℤ T)
  · change IsUnit (standardPolytabloidPivotMatrix ℤ mu).det
    rw [standardPolytabloidPivotMatrix_det]
    exact isUnit_one
  · refine ⟨d, fun q => ?_⟩
    have h := congrArg (fun v => v.coeff q) hd
    simpa only [polytabloidOver_cast, polytabloidOver_rat_apply,
      MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
      MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul] using h

theorem polytabloidOver_mem_span_standard
    {R : Type*} [CommRing R] {mu : YoungDiagram} (T : YoungTableau mu) :
    polytabloidOver R T ∈ Submodule.span R
      (Set.range (fun U : StandardYoungTableau mu => polytabloidOver R U.toTableau)) := by
  obtain ⟨c, hc⟩ := polytabloidOver_integer_expansion T
  apply (Submodule.mem_span_range_iff_exists_fun R).mpr
  refine ⟨fun U => (c U : R), funext fun q => ?_⟩
  have h := congrArg (Int.castRingHom R) (hc q)
  simpa only [map_sum, map_mul, Int.coe_castRingHom, polytabloidOver_cast,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h

theorem spechtSubrepresentationOver_eq_span_standard
    (R : Type*) [CommRing R] (mu : YoungDiagram) :
    (spechtSubrepresentationOver R mu).toSubmodule = Submodule.span R
      (Set.range (fun T : StandardYoungTableau mu => polytabloidOver R T.toTableau)) := by
  apply le_antisymm
  · change Submodule.span R _ ≤ _
    apply Submodule.span_le.mpr
    rintro _ ⟨T, rfl⟩
    exact polytabloidOver_mem_span_standard T
  · apply Submodule.span_le.mpr
    rintro _ ⟨T, rfl⟩
    exact polytabloidOver_mem T.toTableau

def standardPolytabloidBasisOver (R : Type*) [CommRing R] (mu : YoungDiagram) :
    Basis (StandardYoungTableau mu) R (spechtSubrepresentationOver R mu).toSubmodule :=
  (Basis.span (linearIndependent_polytabloidOver (R := R) mu)).map
    (LinearEquiv.ofEq _ _ (spechtSubrepresentationOver_eq_span_standard R mu).symm)

@[simp] theorem standardPolytabloidBasisOver_apply
    (R : Type*) [CommRing R] (mu : YoungDiagram) (T : StandardYoungTableau mu) :
    standardPolytabloidBasisOver R mu T = standardPolytabloidOver T := by
  apply Subtype.ext
  simp [standardPolytabloidBasisOver, standardPolytabloidOver]

@[simp] theorem standardPolytabloidOver_span (R : Type*) [CommRing R] (mu : YoungDiagram) :
    Submodule.span R (Set.range (standardPolytabloidOver (R := R) (mu := mu))) = ⊤ := by
  have he : (⇑(standardPolytabloidBasisOver R mu) :
      StandardYoungTableau mu → (spechtSubrepresentationOver R mu).toSubmodule) =
      standardPolytabloidOver (R := R) :=
    funext (standardPolytabloidBasisOver_apply R mu)
  rw [← he]
  exact (standardPolytabloidBasisOver R mu).span_eq

end HigherSpecht
end
end CanonicalSource39

section CanonicalSource40
/- Source: HigherSpecht/AdmissibleSpechtCopies.lean -/



/-!
# The exact prescribed copies in admissible characteristic

The spans below are the spans of the literal fixed-left-tableau polynomial
families.  Integral standard-polytabloid spanning identifies them with the
ranges of the actual equivariant polynomial maps.  Coefficient separation
proves those maps are nonzero; Maschke and the column operator then identify
each range with the ordinary simple Specht module of the stated shape.
-/

noncomputable section
open TauCeti TauCeti.YoungTableau Module MvPolynomial
open scoped Classical MonoidAlgebra

namespace HigherSpecht

theorem irreducible_of_representation_equiv
    {K G V W : Type*} [Field K] [Group G]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    {rho : Representation K G V} {sigma : Representation K G W}
    [rho.IsIrreducible] (e : rho.Equiv sigma) : sigma.IsIrreducible := by
  let em : rho.asModule ≃ₗ[K[G]] sigma.asModule := LinearEquiv.ofBijective
    (Representation.IntertwiningMap.equivLinearMapAsModule rho sigma e.toIntertwiningMap)
    e.toLinearEquiv.bijective
  apply (Representation.irreducible_iff_isSimpleModule_asModule sigma).mpr
  exact em.isSimpleModule_iff.mp inferInstance

theorem linearMap_range_eq_span_standard
    {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    {mu : YoungDiagram} (f : (spechtSubrepresentationOver R mu).toSubmodule →ₗ[R] V) :
    LinearMap.range f = Submodule.span R
      (Set.range (fun T : StandardYoungTableau mu => f (standardPolytabloidOver T))) := by
  rw [← Submodule.map_top, ← standardPolytabloidOver_span R mu,
    Submodule.map_span, ← Set.range_comp']

def griffinFixedCopySpanOver (K : Type*) [Field K]
    {n : ℕ} (lam : YoungDiagram) (hk : lam.card ≤ n) (s : ℕ)
    (part : n.Partition) (i : PartitionGriffinCopies n lam hk s part) :
    Submodule K (GriffinRing K n lam s) :=
  Submodule.span K (Set.range (fun T : StandardYoungTableau (YoungDiagram.ofPartition part) =>
    Ideal.Quotient.mk (griffinIdeal K n lam s)
      (rename (finCongr (YoungDiagram.card_ofPartition part))
        (higherSpechtPolynomial i.left T) *
        elementaryMultiplier n (n - lam.card) i.multiplier.rowLen)))

def griffinFixedCopyOver (K : Type*) [Field K]
    {n : ℕ} (lam : YoungDiagram) (hk : lam.card ≤ n) (s : ℕ)
    (part : n.Partition) (i : PartitionGriffinCopies n lam hk s part) :
    Subrepresentation (griffinRepresentation K n lam s) :=
  (partitionGriffinIntertwinerOver (R := K) lam hk s part i).range

@[simp] theorem griffinFixedCopyOver_toSubmodule
    (K : Type*) [Field K] {n : ℕ} (lam : YoungDiagram)
    (hk : lam.card ≤ n) (s : ℕ) (part : n.Partition)
    (i : PartitionGriffinCopies n lam hk s part) :
    (griffinFixedCopyOver K lam hk s part i).toSubmodule =
      griffinFixedCopySpanOver K lam hk s part i := by
  change LinearMap.range
    (partitionGriffinIntertwinerOver (R := K) lam hk s part i).toLinearMap = _
  rw [linearMap_range_eq_span_standard]
  simp only [Representation.IntertwiningMap.coe_toLinearMap,
    partitionGriffinIntertwinerOver_standard, griffinFixedCopySpanOver]

theorem partitionGriffinIntertwinerOver_ne_zero
    {K : Type*} [Field K] {n : ℕ} (lam : YoungDiagram)
    (hk : lam.card ≤ n) (s : ℕ) (part : n.Partition)
    (i : PartitionGriffinCopies n lam hk s part)
    (hfac : (n.factorial : K) ≠ 0) (hheight : lam.colLen 0 ≤ s) :
    partitionGriffinIntertwinerOver (R := K) lam hk s part i ≠ 0 := by
  let T := StandardYoungTableau.rowSuperstandard (YoungDiagram.ofPartition part)
  have hn := (griffin_fixedTableau_renamed_independent_of_factorial_ne_zero
    (YoungDiagram.card_ofPartition part) hk hfac T hheight).ne_zero i
  intro hz
  have h := congrArg (fun f => f (standardPolytabloidOver (R := K) T)) hz
  apply hn
  simpa only [partitionGriffinIntertwinerOver_standard,
    Representation.IntertwiningMap.coe_zero, Pi.zero_apply] using h

def griffinFixedCopyEquivOver
    {K : Type*} [Field K] {n : ℕ} (lam : YoungDiagram)
    (hk : lam.card ≤ n) (s : ℕ) (part : n.Partition)
    (i : PartitionGriffinCopies n lam hk s part)
    (hfac : (n.factorial : K) ≠ 0) (hheight : lam.colLen 0 ≤ s) :
    Representation.Equiv (partitionSpechtRepresentationOver K part)
      (griffinFixedCopyOver K lam hk s part i).toRepresentation := by
  letI := partitionSpechtRepresentationOver_isIrreducible hfac part
  let f := partitionGriffinIntertwinerOver (R := K) lam hk s part i
  have hf : Function.Injective f :=
    (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right
      (partitionGriffinIntertwinerOver_ne_zero lam hk s part i hfac hheight)
  exact f.equivOfRange hf rfl

theorem corollary_8_1_griffin_copy_irreducible
    {K : Type*} [Field K] {n : ℕ} (lam : YoungDiagram)
    (hk : lam.card ≤ n) (s : ℕ) (part : n.Partition)
    (i : PartitionGriffinCopies n lam hk s part)
    (hchar : ringChar K = 0 ∨ n < ringChar K) (hheight : lam.colLen 0 ≤ s) :
    (griffinFixedCopyOver K lam hk s part i).toRepresentation.IsIrreducible ∧
      Nonempty (Representation.Equiv (partitionSpechtRepresentationOver K part)
        (griffinFixedCopyOver K lam hk s part i).toRepresentation) := by
  have hfac := (factorial_ne_zero_iff_characteristic_range K n).mpr hchar
  letI := partitionSpechtRepresentationOver_isIrreducible hfac part
  let e := griffinFixedCopyEquivOver lam hk s part i hfac hheight
  exact ⟨irreducible_of_representation_equiv e, ⟨e⟩⟩

def springerCopyIndex {lam : YoungDiagram} (part : lam.card.Partition)
    (S : StandardYoungTableau (YoungDiagram.ofPartition part)) (hS : CatDominates S lam)
    (T : StandardYoungTableau (YoungDiagram.ofPartition part)) : SpringerIndex lam :=
  ⟨(standardPairPartitionEquiv lam.card).symm ⟨part, S, T⟩, hS⟩

theorem springerCopyIndex_injective {lam : YoungDiagram} (part : lam.card.Partition)
    (S : StandardYoungTableau (YoungDiagram.ofPartition part)) (hS : CatDominates S lam) :
    Function.Injective (springerCopyIndex part S hS) := by
  intro T U h
  have hp := congrArg (fun z : SpringerIndex lam =>
    standardPairPartitionEquiv lam.card z.val) h
  simp only [springerCopyIndex, Equiv.apply_symm_apply] at hp
  have hpair : (S, T) = (S, U) := eq_of_heq (Sigma.mk.inj_iff.mp hp).2
  exact congrArg Prod.snd hpair

def partitionSpringerIntertwinerOver {R : Type*} [CommRing R]
    (lam : YoungDiagram) (part : lam.card.Partition)
    (S : StandardYoungTableau (YoungDiagram.ofPartition part)) :
    Representation.IntertwiningMap (partitionSpechtRepresentationOver R part)
      (springerRepresentation R lam) :=
  (quotientProjectionIntertwiner (springerIdeal R lam)
    (permutationStable_untruncatedIdeal lam)).comp
      (partitionHigherSpechtIntertwinerOver part S)

@[simp] theorem partitionSpringerIntertwinerOver_standard
    {R : Type*} [CommRing R] (lam : YoungDiagram) (part : lam.card.Partition)
    (S T : StandardYoungTableau (YoungDiagram.ofPartition part)) :
    partitionSpringerIntertwinerOver (R := R) lam part S (standardPolytabloidOver T) =
      Ideal.Quotient.mk (springerIdeal R lam)
        (rename (finCongr (YoungDiagram.card_ofPartition part))
          (higherSpechtPolynomial S T)) := by
  change Ideal.Quotient.mk (springerIdeal R lam)
    (rename (finCongr (YoungDiagram.card_ofPartition part))
      (higherSpechtIntertwinerOver (R := R) S (standardPolytabloidOver T))) = _
  rw [higherSpechtIntertwinerOver_standard]

@[simp] theorem partitionSpringerIntertwinerOver_family
    {R : Type*} [CommRing R] (lam : YoungDiagram) (part : lam.card.Partition)
    (S : StandardYoungTableau (YoungDiagram.ofPartition part)) (hS : CatDominates S lam)
    (T : StandardYoungTableau (YoungDiagram.ofPartition part)) :
    partitionSpringerIntertwinerOver (R := R) lam part S (standardPolytabloidOver T) =
      springerFamily R lam (springerCopyIndex part S hS T) := by
  rw [partitionSpringerIntertwinerOver_standard]
  rfl

def springerFixedCopySpanOver (K : Type*) [Field K]
    (lam : YoungDiagram) (part : lam.card.Partition)
    (S : StandardYoungTableau (YoungDiagram.ofPartition part)) :
    Submodule K (SpringerRing K lam) :=
  Submodule.span K (Set.range (fun T : StandardYoungTableau (YoungDiagram.ofPartition part) =>
    Ideal.Quotient.mk (springerIdeal K lam)
      (rename (finCongr (YoungDiagram.card_ofPartition part))
        (higherSpechtPolynomial S T))))

def springerFixedCopyOver (K : Type*) [Field K]
    (lam : YoungDiagram) (part : lam.card.Partition)
    (S : StandardYoungTableau (YoungDiagram.ofPartition part)) :
    Subrepresentation (springerRepresentation K lam) :=
  (partitionSpringerIntertwinerOver (R := K) lam part S).range

@[simp] theorem springerFixedCopyOver_toSubmodule
    (K : Type*) [Field K] (lam : YoungDiagram) (part : lam.card.Partition)
    (S : StandardYoungTableau (YoungDiagram.ofPartition part)) :
    (springerFixedCopyOver K lam part S).toSubmodule = springerFixedCopySpanOver K lam part S := by
  change LinearMap.range (partitionSpringerIntertwinerOver (R := K) lam part S).toLinearMap = _
  rw [linearMap_range_eq_span_standard]
  simp only [Representation.IntertwiningMap.coe_toLinearMap,
    partitionSpringerIntertwinerOver_standard, springerFixedCopySpanOver]

def springerFixedCopyEquivOver
    {K : Type*} [Field K] (lam : YoungDiagram) (part : lam.card.Partition)
    (S : StandardYoungTableau (YoungDiagram.ofPartition part)) (hS : CatDominates S lam)
    (hfac : (lam.card.factorial : K) ≠ 0) :
    Representation.Equiv (partitionSpechtRepresentationOver K part)
      (springerFixedCopyOver K lam part S).toRepresentation := by
  let f := partitionSpringerIntertwinerOver (R := K) lam part S
  have hi : LinearIndependent K
      (fun T : StandardYoungTableau (YoungDiagram.ofPartition part) =>
        springerPrescribedBasisAdmissible K lam hfac (springerCopyIndex part S hS T)) :=
    (springerPrescribedBasisAdmissible K lam hfac).linearIndependent.comp
      (springerCopyIndex part S hS) (springerCopyIndex_injective part S hS)
  have he : (fun T : StandardYoungTableau (YoungDiagram.ofPartition part) =>
      springerPrescribedBasisAdmissible K lam hfac (springerCopyIndex part S hS T)) =
      (fun T => f.toLinearMap (standardPolytabloidOver T)) := by
    funext T
    rw [springerPrescribedBasisAdmissible_apply]
    exact (partitionSpringerIntertwinerOver_family lam part S hS T).symm
  have hli : LinearIndependent K
      (fun T : StandardYoungTableau (YoungDiagram.ofPartition part) =>
        f.toLinearMap (standardPolytabloidOver T)) :=
    Eq.mp (congrArg
      (fun v : StandardYoungTableau (YoungDiagram.ofPartition part) → SpringerRing K lam =>
        LinearIndependent K v) he) hi
  have hf : Function.Injective f := LinearMap.injective_of_linearIndependent (f := f.toLinearMap)
    (standardPolytabloidOver_span K (YoungDiagram.ofPartition part)) hli
  exact f.equivOfRange hf rfl

theorem corollary_8_1_springer_copy_irreducible
    {K : Type*} [Field K] (lam : YoungDiagram) (part : lam.card.Partition)
    (S : StandardYoungTableau (YoungDiagram.ofPartition part)) (hS : CatDominates S lam)
    (hchar : ringChar K = 0 ∨ lam.card < ringChar K) :
    (springerFixedCopyOver K lam part S).toRepresentation.IsIrreducible ∧
      Nonempty (Representation.Equiv (partitionSpechtRepresentationOver K part)
        (springerFixedCopyOver K lam part S).toRepresentation) := by
  have hfac := (factorial_ne_zero_iff_characteristic_range K lam.card).mpr hchar
  letI := partitionSpechtRepresentationOver_isIrreducible hfac part
  let e := springerFixedCopyEquivOver lam part S hS hfac
  exact ⟨irreducible_of_representation_equiv e, ⟨e⟩⟩

end HigherSpecht
end
end CanonicalSource40

section CanonicalSource41
/- Source: HigherSpecht/IntegralDeterminantUnits.lean -/



/-!
# From the exact field range to the integral localization

A nonzero integer that survives reduction modulo every prime larger than
`n` divides a power of `n!`. Its image is therefore a unit in every
commutative ring in which `n!` is a unit, in particular in `ℤ[1/n!]`.
-/

noncomputable section
open scoped Classical

namespace HigherSpecht

theorem integer_dvd_factorial_power_of_large_prime_reductions
    (n : ℕ) (D : ℤ) (hD : D ≠ 0)
    (hmod : ∀ p : ℕ, p.Prime → n < p → (D : ZMod p) ≠ 0) :
    ∃ m : ℕ, D ∣ (n.factorial : ℤ) ^ m := by
  have hsub : D.natAbs.primeFactors ⊆ n.factorial.primeFactors := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ D.natAbs := Nat.dvd_of_mem_primeFactors hp
    have hpn : p ≤ n := by
      by_contra h
      apply hmod p hprime (Nat.lt_of_not_ge h)
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd D p).mpr (Int.natCast_dvd.mpr hpd)
    exact Nat.mem_primeFactors.mpr ⟨hprime,
      Nat.dvd_factorial hprime.pos hpn, n.factorial_ne_zero⟩
  have habs : D.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hD
  obtain ⟨m, hm⟩ := (Nat.exists_dvd_pow_iff habs n.factorial_ne_zero).mpr hsub
  refine ⟨m, ?_⟩
  have h := Int.dvd_natCast.mpr hm
  simpa only [Nat.cast_pow] using h

theorem intCast_isUnit_of_dvd_factorial_power
    {R : Type*} [CommRing R] {n m : ℕ} {D : ℤ}
    (hfac : IsUnit (n.factorial : R)) (hdiv : D ∣ (n.factorial : ℤ) ^ m) :
    IsUnit (D : R) := by
  obtain ⟨q, hq⟩ := hdiv
  obtain ⟨u, hu⟩ := hfac.pow m
  have hmul : (D : R) * ((q : R) * (u⁻¹ : Rˣ)) = 1 := by
    rw [← mul_assoc, ← Int.cast_mul, ← hq, Int.cast_pow, Int.cast_natCast,
      ← hu, Units.mul_inv]
  exact ⟨⟨(D : R), (q : R) * (u⁻¹ : Rˣ), hmul,
    by rw [mul_comm]; exact hmul⟩, rfl⟩

theorem intCast_isUnit_of_large_prime_reductions
    {R : Type*} [CommRing R] (n : ℕ) (D : ℤ)
    (hfac : IsUnit (n.factorial : R)) (hD : D ≠ 0)
    (hmod : ∀ p : ℕ, p.Prime → n < p → (D : ZMod p) ≠ 0) :
    IsUnit (D : R) := by
  obtain ⟨m, hm⟩ := integer_dvd_factorial_power_of_large_prime_reductions n D hD hmod
  exact intCast_isUnit_of_dvd_factorial_power hfac hm

/-- The coefficient ring meant by `ℤ[1/n!]` in Corollary 8.1. -/
abbrev FactorialLocalization (n : ℕ) := Localization.Away (n.factorial : ℤ)

theorem factorial_isUnit_localization (n : ℕ) :
    IsUnit (n.factorial : FactorialLocalization n) := by
  simpa only [map_natCast] using
    (IsLocalization.Away.algebraMap_isUnit (S := FactorialLocalization n) (n.factorial : ℤ))

end HigherSpecht
end
end CanonicalSource41

section CanonicalSource42
/- Source: HigherSpecht/LocalizedGriffinBases.lean -/



/-!
# The prescribed bases over `ℤ[1/n!]`

The square matrix is formed in the actual integral staircase basis. Its
reductions are invertible in every admissible field by the preceding full
field theorem. Thus its determinant has only prime factors at most `n`.
The resulting argument works over every commutative ring where `n!` is a
unit, and specializes to the exact localization named by the paper.
-/

noncomputable section
open TauCeti Module Matrix
open scoped Classical TensorProduct

namespace HigherSpecht

def griffinIndexStaircaseEquiv (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    GriffinIndex n lam hk s ≃ GriffinStaircaseExponents n lam s := by
  letI := (finite_griffinStaircaseExponents (n := n) (μ := lam) s hs hheight).fintype
  exact Fintype.equivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card] using
      griffin_index_card_eq_staircase n lam hk s hs hheight)

def griffinIntegralCoordinateBasis (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    Basis (GriffinIndex n lam hk s) ℤ (GriffinRing ℤ n lam s) :=
  (griffinStandardMonomialBasis hk s hs hheight).reindex
    (griffinIndexStaircaseEquiv n lam hk s hs hheight).symm

def griffinIntegralCoefficientMatrix (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    Matrix (GriffinIndex n lam hk s) (GriffinIndex n lam hk s) ℤ :=
  (griffinIntegralCoordinateBasis n lam hk s hs hheight).toMatrix
    (griffinFamily ℤ n lam hk s)

def griffinIntegralCoefficientDet (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) : ℤ :=
  (griffinIntegralCoefficientMatrix n lam hk s hs hheight).det

def griffinScalarCoordinateBasis (R : Type*) [CommRing R] [Nontrivial R]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    Basis (GriffinIndex n lam hk s) R (GriffinRing R n lam s) :=
  ((griffinIntegralCoordinateBasis n lam hk s hs hheight).baseChange R).map
    (griffinBaseChangeEquiv ℤ R n lam s).toLinearEquiv

theorem griffinScalarCoordinateBasis_repr_family (R : Type*) [CommRing R] [Nontrivial R]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s)
    (i j : GriffinIndex n lam hk s) :
    (griffinScalarCoordinateBasis R n lam hk s hs hheight).repr
        (griffinFamily R n lam hk s j) i =
      (griffinIntegralCoefficientMatrix n lam hk s hs hheight i j : R) := by
  change ((griffinIntegralCoordinateBasis n lam hk s hs hheight).baseChange R).repr
    ((griffinBaseChangeEquiv ℤ R n lam s).symm (griffinFamily R n lam hk s j)) i = _
  rw [← griffinBaseChangeEquiv_family (R := ℤ) (S := R) n lam hk s j,
    AlgEquiv.symm_apply_apply, Basis.baseChange_repr_tmul]
  simp only [griffinIntegralCoefficientMatrix, Basis.toMatrix_apply,
    zsmul_eq_mul, mul_one]

theorem griffinIntegralCoefficientDet_cast (R : Type*) [CommRing R] [Nontrivial R]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    (griffinIntegralCoefficientDet n lam hk s hs hheight : R) =
      (griffinScalarCoordinateBasis R n lam hk s hs hheight).det
        (griffinFamily R n lam hk s) := by
  rw [griffinIntegralCoefficientDet, Int.cast_det, Basis.det_apply]
  congr 1
  ext i j
  exact (griffinScalarCoordinateBasis_repr_family R n lam hk s hs hheight i j).symm

theorem griffinIntegralCoefficientDet_cast_ne_zero (K : Type*) [Field K]
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s)
    (hfac : (n.factorial : K) ≠ 0) :
    (griffinIntegralCoefficientDet n lam hk s hs hheight : K) ≠ 0 := by
  rw [griffinIntegralCoefficientDet_cast]
  have h := (griffinScalarCoordinateBasis K n lam hk s hs hheight).isUnit_det
    (griffinPrescribedBasisAdmissible K n lam hk s hs hheight hfac)
  have he : (⇑(griffinPrescribedBasisAdmissible K n lam hk s hs hheight hfac) :
      GriffinIndex n lam hk s → GriffinRing K n lam s) = griffinFamily K n lam hk s :=
    funext (griffinPrescribedBasisAdmissible_apply K n lam hk s hs hheight hfac)
  rw [he] at h
  exact h.ne_zero

theorem griffinIntegralCoefficientDet_ne_zero
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    griffinIntegralCoefficientDet n lam hk s hs hheight ≠ 0 := by
  have h := griffinIntegralCoefficientDet_cast_ne_zero ℚ n lam hk s hs hheight
    (Nat.cast_ne_zero.mpr n.factorial_ne_zero)
  intro hz
  exact h (by rw [hz, Int.cast_zero])

theorem griffinIntegralCoefficientDet_isUnit
    (R : Type*) [CommRing R] (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s)
    (hfac : IsUnit (n.factorial : R)) :
    IsUnit (griffinIntegralCoefficientDet n lam hk s hs hheight : R) := by
  apply intCast_isUnit_of_large_prime_reductions n _ hfac
    (griffinIntegralCoefficientDet_ne_zero n lam hk s hs hheight)
  intro p hp hnp
  letI : Fact p.Prime := ⟨hp⟩
  exact griffinIntegralCoefficientDet_cast_ne_zero (ZMod p) n lam hk s hs hheight
    (factorial_ne_zero_of_char_gt hnp)

theorem griffin_specifiedBasis_of_factorial_isUnit
    (R : Type*) [CommRing R] [Nontrivial R] (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s)
    (hfac : IsUnit (n.factorial : R)) :
    IsSpecifiedBasis (R := R) (griffinFamily R n lam hk s) := by
  have hd := griffinIntegralCoefficientDet_isUnit R n lam hk s hs hheight hfac
  rw [griffinIntegralCoefficientDet_cast] at hd
  obtain ⟨hind, hspan⟩ :=
    (griffinScalarCoordinateBasis R n lam hk s hs hheight).is_basis_iff_det.mpr hd
  exact ⟨Basis.mk hind hspan.ge, fun i => Basis.mk_apply _ _ i⟩

/-- The finite integral assertion of Corollary 8.1 over the actual ring
`Localization.Away (n! : ℤ)`. -/
theorem corollary_8_1_griffin_localized
    (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    IsSpecifiedBasis (R := FactorialLocalization n)
      (griffinFamily (FactorialLocalization n) n lam hk s) := by
  letI : IsDomain (FactorialLocalization n) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors
      (R := ℤ) (M := Submonoid.powers (n.factorial : ℤ)) (FactorialLocalization n)
      (powers_le_nonZeroDivisors_of_noZeroDivisors
        (Nat.cast_ne_zero.mpr n.factorial_ne_zero))
  exact griffin_specifiedBasis_of_factorial_isUnit (FactorialLocalization n)
    n lam hk s hs hheight (factorial_isUnit_localization n)

/-- The original Springer representatives over the same exact localization. -/
theorem corollary_8_1_springer_localized (lam : YoungDiagram) :
    IsSpecifiedBasis (R := FactorialLocalization lam.card)
      (springerFamily (FactorialLocalization lam.card) lam) := by
  let hb := fun s hs hh => corollary_8_1_griffin_localized lam.card lam le_rfl s hs hh
  exact ⟨springerPrescribedBasisFromAnyFiniteBases _ lam hb,
    springerPrescribedBasisFromAnyFiniteBases_apply _ lam hb⟩

end HigherSpecht
end
end CanonicalSource42

section CanonicalSource43
/- Source: HigherSpecht/GriffinCharacteristicAllPartitions.lean -/



/-!
# The characteristic criterion with the empty partition included

The original polynomial representatives are unchanged.  Positivity of `s`
is explicit, so the statement also covers the empty partition.  Necessity
uses the actual one-row vector, whose unnormalised Young operator is `n!`;
sufficiency is the full admissible-characteristic basis theorem.

This source was reconstructed after the execution-environment reset.  It
does not inherit a compilation or dependency certificate from an earlier
draft.
-/

noncomputable section
open TauCeti Module

namespace HigherSpecht

theorem corollary_8_1_griffin_characteristic_all_partitions
    (K : Type*) [Field K] (n : ℕ) (lam : YoungDiagram) (hk : lam.card ≤ n)
    (s : ℕ) (hs : 0 < s) (hheight : lam.colLen 0 ≤ s) :
    IsSpecifiedBasis (R := K) (griffinFamily K n lam hk s) ↔
      ringChar K = 0 ∨ n < ringChar K := by
  constructor
  · intro hB
    by_cases hp : ringChar K = 0
    · exact Or.inl hp
    · right
      by_contra h
      exact not_griffinBasis_of_small_characteristic (Nat.pos_of_ne_zero hp)
        n lam hk s hs (Nat.le_of_not_gt h) hB
  · intro hchar
    exact griffin_specifiedBasis_of_factorial_ne_zero K n lam hk s hs hheight
      ((factorial_ne_zero_iff_characteristic_range K n).mpr hchar)

end HigherSpecht
end
end CanonicalSource43
