module

public import ToricPower.ArrangementWeightCostalkComparison
public import ToricPower.ArrangementCochainColimits
public import ToricPower.ModuleDirectSumColimit
public import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-!
# The full representable cellular complex splits into its genuine weights

Every Laurent basis vector records both a monomial and its actual
incidence translation. Their difference is its total character. This
exhaustive reindexing is natural for every incidence, hence gives an
isomorphism of the actual coefficient diagrams. Preservation of colimits
by the independently constructed cellular cochain functor then gives an
isomorphism of complete complexes with the unrestricted direct sum of the
geometric costalk fibers. No character bound or finite-support hypothesis
on the whole family is imposed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (S : Set (Fin s))
  (c : IncidenceObject A)

/-- Every genuine Laurent incidence lies in exactly one total character. -/
def representedLaurentFiberEquiv (d : IncidenceObject A) :
    RepresentedLaurentIndex A S c d ≃
      Σ m : Fin n → ℤ, RepresentedWeightIndex A S c m d where
  toFun p := ⟨p.2.val - p.1.val, ⟨p.1, by
    simpa only [sub_add_cancel] using p.2.property⟩⟩
  invFun p := ⟨p.2.val, ⟨p.1 + p.2.val.val, p.2.property⟩⟩
  left_inv p := by
    rcases p with ⟨f, m, hm⟩
    change (⟨f, ⟨m - f.val + f.val, _⟩⟩ : RepresentedLaurentIndex A S c d) =
      ⟨f, ⟨m, hm⟩⟩
    simp only [sub_add_cancel]
  right_inv p := by
    rcases p with ⟨m, f, hm⟩
    change (⟨m + f.val - f.val, ⟨f, _⟩⟩ :
      Σ m : Fin n → ℤ, RepresentedWeightIndex A S c m d) = ⟨m, ⟨f, hm⟩⟩
    apply Sigma.ext (add_sub_cancel_right m f.val)
    apply (Subtype.heq_iff_coe_eq (fun p => by
      simp only [add_sub_cancel_right])).mpr
    rfl

/-- The exhaustive reindexing intertwines the two actual incidence maps. -/
theorem representedLaurentFiberEquiv_symm_map {d e : IncidenceObject A}
    (h : d ⟶ e) (m : Fin n → ℤ) (f : RepresentedWeightIndex A S c m d) :
    representedLaurentIndexMap A S c h
        ((representedLaurentFiberEquiv A S c d).symm ⟨m, f⟩) =
      (representedLaurentFiberEquiv A S c e).symm
        ⟨m, representedWeightIndexMap A S c m h f⟩ := by
  change (⟨f.val ≫ h, ⟨m + f.val.val + h.val, _⟩⟩ :
      RepresentedLaurentIndex A S c e) =
    ⟨f.val ≫ h, ⟨m + (f.val ≫ h).val, _⟩⟩
  simp only [incidence_comp_val, add_assoc]

variable (k : Type) [Field k]

/-- The same exhaustive coordinate change is linear over the actual
coefficient field. -/
def representedLaurentFiberLinearEquiv (d : IncidenceObject A) :
    (RepresentedLaurentIndex A S c d →₀ k) ≃ₗ[k]
      Π₀ m : Fin n → ℤ, (RepresentedWeightIndex A S c m d →₀ k) :=
  (Finsupp.mapDomain.linearEquiv k k (representedLaurentFiberEquiv A S c d)).trans
    (sigmaFinsuppLequivDFinsupp k)

theorem representedLaurentFiberLinearEquiv_single (d : IncidenceObject A)
    (m : Fin n → ℤ) (f : RepresentedWeightIndex A S c m d) (r : k) :
    representedLaurentFiberLinearEquiv A S c k d
        (Finsupp.single ((representedLaurentFiberEquiv A S c d).symm ⟨m, f⟩) r) =
      DFinsupp.single m (Finsupp.single f r) := by
  change sigmaFinsuppLequivDFinsupp k
    (Finsupp.mapDomain (representedLaurentFiberEquiv A S c d)
      (Finsupp.single ((representedLaurentFiberEquiv A S c d).symm ⟨m, f⟩) r)) = _
  rw [Finsupp.mapDomain_single, Equiv.apply_symm_apply]
  exact sigmaFinsuppEquivDFinsupp_single
    (⟨m, f⟩ : Σ w : Fin n → ℤ, RepresentedWeightIndex A S c w d) r

def representedWeightFamily :
    Discrete (Fin n → ℤ) ⥤ (IncidenceObject A ⥤ ModuleCat.{0} k) :=
  Discrete.functor (fun m => representedWeightDiagram A S c m k)

/-- The actual coefficient diagram is the literal full sum of its
character-fiber diagrams, naturally for every translated incidence. -/
def representedLaurentDiagramWeightSumIso :
    representedLaurentDiagram A S c k ≅
      (representedWeightFamily A S c k).flip ⋙ ModuleDirectSum.sumFunctor k :=
  NatIso.ofComponents
    (fun d => (representedLaurentFiberLinearEquiv A S c k d).toModuleIso)
    (by
      intro d e h
      apply ModuleCat.hom_ext
      apply Finsupp.lhom_ext
      intro p r
      obtain ⟨⟨m, f⟩, rfl⟩ := (representedLaurentFiberEquiv A S c d).symm.surjective p
      change representedLaurentFiberLinearEquiv A S c k e
          (Finsupp.mapDomain (representedLaurentIndexMap A S c h)
            (Finsupp.single ((representedLaurentFiberEquiv A S c d).symm ⟨m, f⟩) r)) =
        DFinsupp.mapRange.linearMap
          (fun w : Fin n → ℤ => ((representedWeightDiagram A S c w k).map h).hom)
          (representedLaurentFiberLinearEquiv A S c k d
            (Finsupp.single ((representedLaurentFiberEquiv A S c d).symm ⟨m, f⟩) r))
      rw [Finsupp.mapDomain_single, representedLaurentFiberEquiv_symm_map,
        representedLaurentFiberLinearEquiv_single,
        representedLaurentFiberLinearEquiv_single]
      simp only [DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_single,
        representedWeightDiagram_map_single])

/-- The same natural decomposition through the actual categorical
coproduct, so any colimit-preserving construction may consume it. -/
def representedLaurentDiagramCoproductIso :
    representedLaurentDiagram A S c k ≅ colimit (representedWeightFamily A S c k) :=
  representedLaurentDiagramWeightSumIso A S c k ≪≫
    Functor.isoWhiskerLeft (representedWeightFamily A S c k).flip
      (ModuleDirectSum.sumFunctorIsoColim k) ≪≫
    (colimitIsoFlipCompColim (representedWeightFamily A S c k)).symm

def representedWeightFamilyComplexIso :
    representedWeightFamily A S c k ⋙ arrangementCellularCochainFunctor A k ≅
      Discrete.functor (fun m => representedWeightCellularComplex A S c m k) :=
  Discrete.natIso (fun _ => Iso.refl _)

/-- The original cellular cochain complex is the unrestricted sum of
its actual fixed-character cellular complexes, including all differentials. -/
def representedLaurentCochainWeightSumIso :
    arrangementCellularCochainComplex A k (representedLaurentDiagram A S c k) ≅
      ModuleDirectSum.complex k (fun m => representedWeightCellularComplex A S c m k) :=
  (arrangementCellularCochainFunctor A k).mapIso
      (representedLaurentDiagramCoproductIso A S c k) ≪≫
    preservesColimitIso (arrangementCellularCochainFunctor A k)
      (representedWeightFamily A S c k) ≪≫
    HasColimit.isoOfNatIso (representedWeightFamilyComplexIso A S c k) ≪≫
    (ModuleDirectSum.complexColimitIso k
      (fun m => representedWeightCellularComplex A S c m k)).symm

/-- This is the actual original representable A-cell complex, not an
independently defined replacement matrix. -/
def representableCellularWeightSumIso :
    representableLaurentCellularComplex A S k c ≅
      ModuleDirectSum.complex k (fun m => representedWeightCellularComplex A S c m k) :=
  representedLaurentCellularComplexIso A S c k ≪≫
    representedLaurentCochainWeightSumIso A S c k

/-- The unrestricted weight decomposition preserves the actual field
structure on homology, in every degree. -/
def representableCellularHomologyWeightSumIso (q : ℕ) :
    (representableLaurentCellularComplex A S k c).homology q ≅
      ModuleCat.of k (Π₀ m : Fin n → ℤ,
        (representedWeightCellularComplex A S c m k).homology q) :=
  (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℕ) q).mapIso
      (representableCellularWeightSumIso A S c k) ≪≫
    ModuleDirectSum.homologyIso k
      (fun m => representedWeightCellularComplex A S c m k) q

end ToricPower.IntegralArrangement
