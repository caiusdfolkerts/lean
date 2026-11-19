module

public import ToricPower.ArrangementClosedDualFunctor
public import ToricPower.FiniteBiproductShortExact
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-! # Exactness of the actual dual Cartier coefficients

Each cellular degree is a finite sum of inverse Cartier tensor
equivalences. These equivalences are exact and preserve injectives;
the statements retain the original coefficient maps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TauCeti.Toric
open ToricPower.IntegralArrangement
open scoped Classical

namespace ToricPower

universe u v

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (k : Type) [CommRing k]

section Additive
variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear k B] [HasFiniteBiproducts B]

instance arrangementCellularChainFunctor_additive :
    (arrangementCellularChainFunctor A k (B := B)).Additive where
  map_add {P Q α β} := by
    apply HomologicalComplex.Hom.ext
    funext q
    change biproduct.map (fun c : NormalizedCell A q => (α+β).app (op ⟨q,c⟩)) =
      biproduct.map (fun c : NormalizedCell A q => α.app (op ⟨q,c⟩)) +
        biproduct.map (fun c : NormalizedCell A q => β.app (op ⟨q,c⟩))
    apply biproduct.hom_ext'
    intro c
    simp only [biproduct.ι_map,NatTrans.app_add,Preadditive.comp_add,Preadditive.add_comp]

end Additive

section Exact

variable {B : Type u} [Category.{v} B] [Abelian B] [Linear k B] [HasFiniteBiproducts B]
  {E : Type*} [Category E] [Abelian E]
  (D : (IncidenceObject A)ᵒᵖ ⥤ E ⥤ B)
  [∀ c, (D.obj c).Additive]
  [∀ c, PreservesFiniteLimits (D.obj c)]
  [∀ c, PreservesFiniteColimits (D.obj c)]
  (supported : IncidenceObject A → Prop)
  (downward : ∀ {c d : IncidenceObject A}, (c ⟶ d) → supported d → supported c)

local instance exactClosedProofFinite (c : IncidenceObject A) :
    Fintype (PLift (supported c)) := Fintype.ofFinite _
local instance exactClosedCellsFinite (q : ℕ) : Fintype (NormalizedCell A q) :=
  Fintype.ofFinite _

theorem closedCellularDegree_shortExact (q : ℕ) (S : ShortComplex E)
    (hS : S.ShortExact) :
    (S.map (D.flip ⋙ Cellular.closedContravariantLabelEndofunctor supported downward ⋙
      arrangementCellularChainFunctor A k ⋙ HomologicalComplex.eval B (.down ℕ) q)).ShortExact := by
  let f (c : NormalizedCell A q) :=
    biproduct.map (fun _ : PLift (supported ⟨q,c⟩) => (D.obj (op ⟨q,c⟩)).map S.f)
  let g (c : NormalizedCell A q) :=
    biproduct.map (fun _ : PLift (supported ⟨q,c⟩) => (D.obj (op ⟨q,c⟩)).map S.g)
  have innerZero (c : NormalizedCell A q) (_ : PLift (supported ⟨q,c⟩)) :
      (D.obj (op ⟨q,c⟩)).map S.f ≫ (D.obj (op ⟨q,c⟩)).map S.g = 0 := by
    rw [← CategoryTheory.Functor.map_comp,S.zero,CategoryTheory.Functor.map_zero]
  have zero (c : NormalizedCell A q) : f c ≫ g c = 0 :=
    biproduct_map_comp_zero _ _ (innerZero c)
  have exactAt (c : NormalizedCell A q) : (ShortComplex.mk (f c) (g c) (zero c)).ShortExact :=
    biproduct_shortExact _ _ (innerZero c) (fun _ => hS.map_of_exact (D.obj (op ⟨q,c⟩)))
  exact biproduct_shortExact f g zero exactAt

end Exact

section Toric

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  [nonempty : Nonempty fan.cones] (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (selected : Set (Fin s ⊕ Fin n))

local instance closedDualExactBiproducts : HasFiniteBiproducts (QCoh fan.algebraicRealization) :=
  HasFiniteBiproducts.of_hasFiniteProducts
local instance closedDualExactIntegral : IsIntegral fan.algebraicRealization :=
  toricSchemeIntegral fan nonempty

local notation "Φ" => arrangementClosedDualFunctor fan regular basis rays selected

instance arrangementClosedDualFunctor_additive : (Φ).Additive := by
  unfold arrangementClosedDualFunctor arrangementClosedDualCoefficientFunctor
  letI : (arrangementDualInverseTensorFunctor fan regular basis rays).flip.Additive :=
    arrangementDualInverseTensorFunctor_flip_additive fan regular basis rays
  letI : (Cellular.closedContravariantLabelEndofunctor
      (B := QCoh fan.algebraicRealization)
      (closedIntegralRowsSupport (fanArrangementMatrix fan basis rays) selected)
      (closedIntegralRowsSupport_incidence (fanArrangementMatrix fan basis rays) selected)).Additive :=
    Cellular.closedContravariantLabelEndofunctor_additive _ _
  letI : (arrangementCellularChainFunctor (fanArrangementMatrix fan basis rays) ℂ
      (B := QCoh fan.algebraicRealization)).Additive :=
    arrangementCellularChainFunctor_additive _ _
  infer_instance

theorem arrangementClosedDualFunctor_degree_shortExact (q : ℕ)
    (S : ShortComplex (QCoh fan.algebraicRealization)) (hS : S.ShortExact) :
    (S.map ((Φ) ⋙ HomologicalComplex.eval (QCoh fan.algebraicRealization) (.down ℕ) q)).ShortExact :=
  closedCellularDegree_shortExact (fanArrangementMatrix fan basis rays) ℂ
    (arrangementDualInverseTensorFunctor fan regular basis rays)
    (closedIntegralRowsSupport (fanArrangementMatrix fan basis rays) selected)
    (closedIntegralRowsSupport_incidence (fanArrangementMatrix fan basis rays) selected) q S hS

instance arrangementClosedDualFunctor_degree_preservesFiniteLimits (q : ℕ) :
    PreservesFiniteLimits ((Φ) ⋙ HomologicalComplex.eval (QCoh fan.algebraicRealization) (.down ℕ) q) := by
  apply (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono _).mpr
  intro S hS
  have h := arrangementClosedDualFunctor_degree_shortExact fan regular basis rays selected q S hS
  exact ⟨h.exact,h.mono_f⟩

instance arrangementClosedDualFunctor_degree_preservesFiniteColimits (q : ℕ) :
    PreservesFiniteColimits ((Φ) ⋙ HomologicalComplex.eval (QCoh fan.algebraicRealization) (.down ℕ) q) := by
  apply (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi _).mpr
  intro S hS
  have h := arrangementClosedDualFunctor_degree_shortExact fan regular basis rays selected q S hS
  exact ⟨h.exact,h.epi_g⟩

theorem arrangementClosedDualFunctor_preservesInjectives (q : ℕ)
    (M : QCoh fan.algebraicRealization) (injective : Injective M) :
    Injective (((Φ).obj M).X q) := by
  letI := injective
  change Injective (⨁ fun c : NormalizedCell (fanArrangementMatrix fan basis rays) q =>
    ⨁ fun _ : PLift (closedIntegralRowsSupport (fanArrangementMatrix fan basis rays) selected ⟨q,c⟩) =>
      ((arrangementDualInverseTensorFunctor fan regular basis rays).obj (op ⟨q,c⟩)).obj M)
  infer_instance

end Toric

end ToricPower

end
