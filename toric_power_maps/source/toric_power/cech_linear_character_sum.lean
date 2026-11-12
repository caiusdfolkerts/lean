module

public import ToricPower.LinearRelativeCech
public import ToricPower.CechCharacterComplex
public import ToricPower.CechToricLinearComplex
public import ToricPower.ModuleDirectSumColimit

/-!
# The full scalar-linear character decomposition of toric Čech complexes

Every character summand is its literal relative Čech complex. Monomial
insertion is a map of cosimplicial modules, and the resulting map from
the unrestricted direct sum is an isomorphism for a finite affine cover.
The indexing equivalence is arbitrary; in the arrangement application it
is the negative of the chosen lattice basis.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TauCeti.Toric
open scoped Classical Simplicial BigOperators

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  {Index : Type} (charts : Index → fan.cones) (b : fan.Ray → ℤ)

abbrev toricCechLinearWeightComplex (m : N →+ ℤ) :=
  LinearRelativeCech.complex ℂ (toricCechRayIncidence fan charts)
    (toricCharacterNegative fan b m)

/-- Insert one genuine character into every tuple's Laurent polynomial. -/
def toricCechLinearWeightDegreeInclusion (m : N →+ ℤ) (q : ℕ) :
    (toricCechLinearWeightComplex fan charts b m).X q ⟶
      (toricCechLaurentLinearComplex fan charts b).X q :=
  ModuleCat.ofHom
    { toFun := fun a tuple => toricCechWeightScalarToLaurent fan charts b m q tuple
        ⟨(a tuple).val, (a tuple).property⟩
      map_add' := by
        intro a c
        funext tuple
        apply Subtype.ext
        exact Finsupp.single_add _ _ _
      map_smul' := by
        intro r a
        funext tuple
        apply Subtype.ext
        exact (Finsupp.smul_single r m (a tuple).val).symm }

/-- Extract one genuine character from every tuple. -/
def toricCechLinearWeightDegreeProjection (m : N →+ ℤ) (q : ℕ) :
    (toricCechLaurentLinearComplex fan charts b).X q ⟶
      (toricCechLinearWeightComplex fan charts b m).X q :=
  ModuleCat.ofHom
    { toFun := fun p tuple =>
        let a := toricCechWeightLaurentToScalar fan charts b m q tuple (p tuple)
        ⟨a.val, a.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

@[simp]
theorem toricCechLinearWeightDegreeInclusion_val (m : N →+ ℤ) (q : ℕ)
    (a : (toricCechLinearWeightComplex fan charts b m).X q)
    (tuple : Fin (q+1) → Index) :
    ((toricCechLinearWeightDegreeInclusion fan charts b m q) a tuple).val =
      Finsupp.single m (a tuple).val := rfl

@[simp]
theorem toricCechLinearWeightDegreeProjection_val (m : N →+ ℤ) (q : ℕ)
    (p : (toricCechLaurentLinearComplex fan charts b).X q)
    (tuple : Fin (q+1) → Index) :
    ((toricCechLinearWeightDegreeProjection fan charts b m q) p tuple).val =
      (p tuple).val m := rfl

/-- Monomial insertion respects all cofaces and codegeneracies literally. -/
def toricCechLinearWeightCosimplicialInclusion (m : N →+ ℤ) :
    LinearRelativeCech.cosimplicial ℂ (toricCechRayIncidence fan charts)
        (toricCharacterNegative fan b m) ⟶
      toricCechLaurentLinearCosimplicial fan charts b where
  app q := toricCechLinearWeightDegreeInclusion fan charts b m q.len
  naturality {x y} f := by
    ext x tuple
    rfl

def toricCechLinearWeightInclusion (m : N →+ ℤ) :
    toricCechLinearWeightComplex fan charts b m ⟶
      toricCechLaurentLinearComplex fan charts b :=
  AlgebraicTopology.AlternatingCofaceMapComplex.map
    (toricCechLinearWeightCosimplicialInclusion fan charts b m)

variable {Weight : Type} (e : Weight ≃ (N →+ ℤ))

/-- Literal degree coordinates, with no categorical products remaining. -/
abbrev ToricCechLinearCharacterSumDegree (q : ℕ) :=
  Π₀ w : Weight, (toricCechLinearWeightComplex fan charts b (e w)).X q

def toricCechLinearCharacterSumDegreeMap (q : ℕ) :
    ToricCechLinearCharacterSumDegree fan charts b e q →ₗ[ℂ]
      (toricCechLaurentLinearComplex fan charts b).X q :=
  DFinsupp.lsum ℂ (fun m =>
    (toricCechLinearWeightDegreeInclusion fan charts b (e m) q).hom)

@[simp]
theorem toricCechLinearCharacterSumDegreeMap_single (q : ℕ) (m : Weight)
    (a : (toricCechLinearWeightComplex fan charts b (e m)).X q) :
    toricCechLinearCharacterSumDegreeMap fan charts b e q (DFinsupp.single m a) =
      toricCechLinearWeightDegreeInclusion fan charts b (e m) q a :=
  DFinsupp.lsum_single (S := ℂ) _ _ _

/-- The unrestricted algebraic sum of the full relative complexes. -/
def toricCechLinearCharacterSum : CochainComplex (ModuleCat ℂ) ℕ :=
  ModuleDirectSum.complex ℂ (fun m => toricCechLinearWeightComplex fan charts b (e m))

/-- The universal sum of the actual monomial inclusions. -/
def toricCechLinearCharacterSumMap :
    toricCechLinearCharacterSum fan charts b e ⟶
      toricCechLaurentLinearComplex fan charts b :=
  (ModuleDirectSum.complexCoconeIsColimit ℂ
    (fun m => toricCechLinearWeightComplex fan charts b (e m))).desc
      { pt := toricCechLaurentLinearComplex fan charts b
        ι := Discrete.natTrans (fun m => toricCechLinearWeightInclusion fan charts b (e m.as)) }

@[reassoc]
theorem toricCechLinearCharacterSumMap_inclusion (m : Weight) :
    ModuleDirectSum.complexInclusion ℂ
        (fun w => toricCechLinearWeightComplex fan charts b (e w)) m ≫
      toricCechLinearCharacterSumMap fan charts b e =
        toricCechLinearWeightInclusion fan charts b (e m) :=
  (ModuleDirectSum.complexCoconeIsColimit ℂ _).fac _ ⟨m⟩

/-- In each degree the categorical map is the literal finite sum of
the monomials of all nonzero character coefficients. -/
theorem toricCechLinearCharacterSumMap_f (q : ℕ) :
    (toricCechLinearCharacterSumMap fan charts b e).f q =
      ModuleCat.ofHom (DFinsupp.lsum ℂ
        (fun m => (toricCechLinearWeightDegreeInclusion fan charts b (e m) q).hom)) := by
  apply ModuleCat.hom_ext
  apply DFinsupp.lhom_ext
  intro m a
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f => f.f q) (toricCechLinearCharacterSumMap_inclusion fan charts b e m)) a
  change _ = (DFinsupp.lsum ℂ
    (fun w => (toricCechLinearWeightDegreeInclusion fan charts b (e w) q).hom))
      (DFinsupp.single m a)
  rw [DFinsupp.lsum_single]
  exact h

@[simp]
theorem toricCechLinearCharacterSumMap_single [DecidableEq Weight] (q : ℕ) (m : Weight)
    (a : (toricCechLinearWeightComplex fan charts b (e m)).X q) :
    (toricCechLinearCharacterSumMap fan charts b e).f q (DFinsupp.single m a) =
      toricCechLinearWeightDegreeInclusion fan charts b (e m) q a := by
  rw [toricCechLinearCharacterSumMap_f]
  exact DFinsupp.lsum_single (S := ℂ) _ _ _

/-- Extraction recovers every summand, including those absent from the support. -/
theorem toricCechLinearCharacterSumMap_projection (q : ℕ) (m : Weight)
    (p : ToricCechLinearCharacterSumDegree fan charts b e q) :
    toricCechLinearWeightDegreeProjection fan charts b (e m) q
      (toricCechLinearCharacterSumDegreeMap fan charts b e q p) = p m := by
  have h : (toricCechLinearWeightDegreeProjection fan charts b (e m) q).hom.comp
      (toricCechLinearCharacterSumDegreeMap fan charts b e q) =
      DFinsupp.lapply m := by
    apply DFinsupp.lhom_ext
    intro w a
    change toricCechLinearWeightDegreeProjection fan charts b (e m) q
        (toricCechLinearCharacterSumDegreeMap fan charts b e q (DFinsupp.single w a)) = _
    rw [toricCechLinearCharacterSumDegreeMap_single]
    by_cases hw : w = m
    · subst w
      rw [DFinsupp.lapply_apply, DFinsupp.single_eq_same]
      funext tuple
      apply Subtype.ext
      rw [toricCechLinearWeightDegreeProjection_val,
        toricCechLinearWeightDegreeInclusion_val]
      exact Finsupp.single_eq_same
    · rw [DFinsupp.lapply_apply, DFinsupp.single_eq_of_ne (Ne.symm hw)]
      funext tuple
      apply Subtype.ext
      rw [toricCechLinearWeightDegreeProjection_val,
        toricCechLinearWeightDegreeInclusion_val]
      exact Finsupp.single_eq_of_ne (fun h => hw (e.injective h.symm))
  exact DFunLike.congr_fun h p

variable [Fintype Index]

/-- The finite union of the actual Laurent supports across all tuples. -/
def toricCechLinearDegreeSupport (q : ℕ)
    (p : (toricCechLaurentLinearComplex fan charts b).X q) : Finset (N →+ ℤ) :=
  Finset.univ.biUnion (fun tuple : Fin (q+1) → Index => (p tuple).val.support)

theorem toricCechLinearCharacterSumMap_bijective (q : ℕ) :
    Function.Bijective ((toricCechLinearCharacterSumMap fan charts b e).f q) := by
  rw [toricCechLinearCharacterSumMap_f]
  change Function.Bijective (toricCechLinearCharacterSumDegreeMap fan charts b e q)
  constructor
  · intro p r h
    apply DFinsupp.ext
    intro m
    rw [← toricCechLinearCharacterSumMap_projection fan charts b e q m p,
      ← toricCechLinearCharacterSumMap_projection fan charts b e q m r, h]
  · intro p
    let support := toricCechLinearDegreeSupport fan charts b q p
    refine ⟨∑ m ∈ support, DFinsupp.single (e.symm m)
      (toricCechLinearWeightDegreeProjection fan charts b (e (e.symm m)) q p), ?_⟩
    rw [map_sum]
    simp only [toricCechLinearCharacterSumDegreeMap_single]
    apply funext
    intro tuple
    rw [Finset.sum_apply]
    apply Subtype.ext
    simp only [Submodule.coe_sum,
      toricCechLinearWeightDegreeInclusion_val,
      toricCechLinearWeightDegreeProjection_val, Equiv.apply_symm_apply]
    have hs : (p tuple).val.support ⊆ support := by
      intro m hm
      exact Finset.mem_biUnion.mpr ⟨tuple, Finset.mem_univ _, hm⟩
    calc
      _ = ∑ m ∈ (p tuple).val.support, Finsupp.single m ((p tuple).val m) :=
        (Finset.sum_subset hs (fun m _ hm => by
          rw [Finsupp.notMem_support_iff.mp hm, Finsupp.single_zero])).symm
      _ = (p tuple).val := Finsupp.sum_single _

/-- The actual full-character chain map is an isomorphism. -/
def toricCechLinearCharacterSumIso :
    toricCechLinearCharacterSum fan charts b e ≅
      toricCechLaurentLinearComplex fan charts b := by
  let f := toricCechLinearCharacterSumMap fan charts b e
  haveI : ∀ q, IsIso (f.f q) := fun q =>
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (toricCechLinearCharacterSumMap_bijective fan charts b e q)
  haveI : IsIso f := HomologicalComplex.Hom.isIso_of_components f
  exact asIso f

end ToricPower

end
