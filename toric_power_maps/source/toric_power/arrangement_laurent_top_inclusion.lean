module

public import ToricPower.ArrangementMinimalCoface
public import ToricPower.ArrangementTopCofaceCoordinates
public import ToricPower.ArrangementLaurentWeightInclusions
public import ToricPower.FinsuppPartitionColimit

/-!
# The original full Laurent top inclusion and its character fibers

The top-cell map is the literal copower inclusion. Each allowed fiber is
the original top support map, while each forbidden source is actually
zero. Their compatibility is an equality before taking homology.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (S : Set (Fin s))
  (c : IncidenceObject A) (k : Type) [Field k]

local notation "singleTop" => HomologicalComplex.single (ModuleCat k) (ComplexShape.up ℕ) n

def representedLaurentTopCofaceInclusion (d : NormalizedCell A n)
    (f : c ⟶ (⟨n,d⟩ : IncidenceObject A)) :
    (singleTop).obj ((reflectedLaurentDiagram A S k).obj ⟨n,d⟩) ⟶
      representableLaurentCellularComplex A S k c :=
  HomologicalComplex.mkHomFromSingle
    (Cellular.vectorCopowerInclusion k ((reflectedLaurentDiagram A S k).obj ⟨n,d⟩)
      ((Cellular.representable k c).obj ⟨n,d⟩) (ModuleCat.freeMk f) ≫
      arrangementCellularCochainInclusion A k
        (Cellular.covariantCopowerDiagram k (reflectedLaurentDiagram A S k)
          (Cellular.representable k c)) n d)
    (fun q relation => by
      have above : n < q := by have successor : q = n+1 := relation.symm; omega
      exact (arrangementCellularCochainComplex_isZero_X_above A k
        (Cellular.covariantCopowerDiagram k (reflectedLaurentDiagram A S k)
          (Cellular.representable k c)) q above).eq_of_tgt _ _)

theorem representedLaurentTopCofaceInclusion_generator
    (d : NormalizedCell A n) (f : c ⟶ (⟨n,d⟩ : IncidenceObject A))
    (r : ReflectedLaurentWeight A S ⟨n,d⟩) (a : k) :
    (representedLaurentTopCofaceInclusion A S c k d f).f n
      ((HomologicalComplex.singleObjXSelf (.up ℕ) n
        ((reflectedLaurentDiagram A S k).obj ⟨n,d⟩)).inv (Finsupp.single r a)) =
      arrangementCellularCochainInclusion A k
        (Cellular.covariantCopowerDiagram k (reflectedLaurentDiagram A S k)
          (Cellular.representable k c)) n d
        (Cellular.vectorCopowerInclusion k
          ((reflectedLaurentDiagram A S k).obj ⟨n,d⟩)
          ((Cellular.representable k c).obj ⟨n,d⟩) (ModuleCat.freeMk f)
          (Finsupp.single r a)) := by
  simp only [representedLaurentTopCofaceInclusion, HomologicalComplex.mkHomFromSingle_f,
    ModuleCat.comp_apply, Iso.inv_hom_id_apply]
  rfl

/-- The proof fiber is either an actual one-dimensional coefficient
or an actually zero coefficient; no character has been truncated. -/
def representedSupportedWeightCoefficient (m : Fin n → ℤ) : ModuleCat k :=
  ModuleCat.of k (PLift (RepresentableSupportedWeight A S c m) →₀ k)

variable
  (strictDirection : ∃ v : Fin n → ℝ, ∀ i ∈ Sum.inl '' S,
    0 < augmentedForms A i v)
  (minimal : Fin n → ℤ)
  (minimal_eq : ∀ i ∈ S, rayPairing A minimal i = c.2.val.val.1 (.inl i) - 1)
  (p : RepresentableCostalkIndex A c S minimal n)

def representedTopCofaceFiberMap (m : Fin n → ℤ) :
    (singleTop).obj (representedSupportedWeightCoefficient A S c k m) ⟶
      representedWeightCellularComplex A S c m k :=
  if supported : RepresentableSupportedWeight A S c m then
    (singleTop).map (Finsupp.uniqueLinearEquiv k k
      (⟨supported⟩ : PLift (RepresentableSupportedWeight A S c m))).toModuleIso.hom ≫
      representedTopCofaceMap A k S c m
        (representedMinimalTopCofaceAt A S c strictDirection minimal minimal_eq p m supported)
  else 0

theorem representedTopCofaceFiberMap_generator (m : Fin n → ℤ)
    (h : PLift (RepresentableSupportedWeight A S c m)) (a : k) :
    (representedTopCofaceFiberMap A S c k strictDirection minimal minimal_eq p m).f n
      ((HomologicalComplex.singleObjXSelf (.up ℕ) n
        (representedSupportedWeightCoefficient A S c k m)).inv (Finsupp.single h a)) =
      (representedWeightCellularCoordinates A S c m k n).symm
        (Finsupp.single
          (representedMinimalTopCofaceAt A S c strictDirection minimal minimal_eq p m h.down) a) := by
  rw [representedTopCofaceFiberMap, dif_pos h.down]
  simp only [HomologicalComplex.comp_f, HomologicalComplex.single_map_f_self,
    ModuleCat.comp_apply, Iso.inv_hom_id_apply]
  change (representedTopCofaceMap A k S c m
      (representedMinimalTopCofaceAt A S c strictDirection minimal minimal_eq p m h.down)).f n
      ((HomologicalComplex.singleObjXSelf (.up ℕ) n (ModuleCat.of k k)).inv
        ((Finsupp.uniqueLinearEquiv k k (⟨h.down⟩ : PLift _)) (Finsupp.single h a))) = _
  rw [show (⟨h.down⟩ : PLift (RepresentableSupportedWeight A S c m)) = h from Subsingleton.elim _ _]
  simp only [Finsupp.uniqueLinearEquiv_apply, Finsupp.single_eq_same]
  exact representedTopCofaceMap_generator A S c m k _ a

theorem representedTopCofaceFiberMap_quasiIso (m : Fin n → ℤ) :
    QuasiIso (representedTopCofaceFiberMap A S c k strictDirection minimal minimal_eq p m) := by
  by_cases supported : RepresentableSupportedWeight A S c m
  · rw [representedTopCofaceFiberMap, dif_pos supported]
    haveI := representedTopCofaceMap_quasiIso A k S c m
      (representedMinimalTopCofaceAt A S c strictDirection minimal minimal_eq p m supported)
    infer_instance
  · letI : IsEmpty (PLift (RepresentableSupportedWeight A S c m)) :=
      ⟨fun h => supported h.down⟩
    have zeroSource : IsZero ((singleTop).obj
        (representedSupportedWeightCoefficient A S c k m)) := by
      apply (singleTop).map_isZero
      change IsZero (ModuleCat.of k (PLift (RepresentableSupportedWeight A S c m) →₀ k))
      exact ModuleCat.isZero_of_subsingleton _
    rw [quasiIso_iff]
    intro q
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact ((HomologicalComplex.homologyFunctor (ModuleCat k) (.up ℕ) q).map_isZero zeroSource).isIso
      (representedWeightCellularComplex_isZero_homology_of_empty A S c m k
        (Set.not_nonempty_iff_eq_empty.mp supported) q) _

def representedTopCofaceFamilyMap :
    Discrete.functor (fun m => (singleTop).obj (representedSupportedWeightCoefficient A S c k m)) ⟶
      Discrete.functor (fun m => representedWeightCellularComplex A S c m k) :=
  Discrete.natTrans (fun m => representedTopCofaceFiberMap A S c k strictDirection minimal minimal_eq p m.as)

end ToricPower.IntegralArrangement

end
