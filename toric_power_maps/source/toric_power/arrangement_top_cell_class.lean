module

public import ToricPower.ArrangementTopCellSupport
public import ToricPower.TopHomologyAugmentation

/-!
# The nonzero ambient class of each actual top cell

The one-cell cochain generator maps nontrivially to the fixed ambient
top class. Its image stays nonzero under extension into any bounded
convex open union of cells. The proof uses the already established
naturality of the actual cellular top class, rather than choosing a
new orientation for each larger support.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Set
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)
  (c : Cell (augmentedForms A) n) (k : Type) [Field k]

local notation "U" => topCellSupport A c
local notation "K" => openSupportCochainComplex A k U

theorem topCellCochain_outgoing : (K).d n (n+1) = 0 :=
  (topCellCochain_isZero_X A c k (n+1) (Nat.succ_ne_self n)).eq_of_tgt _ _

/-- The canonical top quotient followed by the ambient orientation. -/
def topCellCochainTopFunctional : (K).X n ⟶ ModuleCat.of k k :=
  (K).pOpcycles n ≫
    ((K).isoHomologyι n (n+1) (by simp) (topCellCochain_outgoing A c k)).inv ≫
      (openSupportCochainTopClassIso A k U (topCellSupport_convex A c)
        (topCellSupport_nonempty A c) (topCellSupport_bounded A c)).hom

instance topCellCochainTopFunctional_epi : Epi (topCellCochainTopFunctional A c k) := by
  unfold topCellCochainTopFunctional
  infer_instance

/-- The genuine characteristic-cell generator, with coefficient one
in the original relative cellular coordinates. -/
def topCellCochainGenerator : (K).X n := (topCellCochainTermIso A c k).inv 1

theorem topCellCochainGenerator_coordinates :
    openSupportCochainCoordinates A k U n (topCellCochainGenerator A c k) =
      Finsupp.single (topCellSupport_index A c) 1 := by
  change openSupportCochainCoordinates A k U n
    ((openSupportCochainCoordinates A k U n).symm
      ((Finsupp.uniqueLinearEquiv k k (topCellSupport_index A c)).symm 1)) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- Its actual top cohomology coefficient cannot vanish: the top
quotient is epic and its source has the single displayed generator. -/
theorem topCellCochainTopFunctional_generator_ne_zero :
    topCellCochainTopFunctional A c k (topCellCochainGenerator A c k) ≠ 0 := by
  let f : ModuleCat.of k k ⟶ ModuleCat.of k k :=
    (topCellCochainTermIso A c k).inv ≫ topCellCochainTopFunctional A c k
  have epic : Epi f := by dsimp only [f]; infer_instance
  have surjective := (ModuleCat.epi_iff_surjective f).mp epic
  intro zero
  obtain ⟨a, ha⟩ := surjective 1
  have fone : f 1 = 0 := zero
  have fa : f a = 0 := by
    have linear := f.hom.map_smul a (1 : k)
    simpa only [smul_eq_mul, mul_one, fone, mul_zero] using linear
  exact one_ne_zero (ha.symm.trans fa)

variable (V : OpenCellSupport A) (inclusion : U ≤ V)
  (convexV : Convex ℝ (V.val : Set (Fin n → ℝ)))
  (nonemptyV : (V.val : Set (Fin n → ℝ)).Nonempty)
  (boundedV : Bornology.IsBounded (V.val : Set (Fin n → ℝ)))
  (outgoingV : (openSupportCochainComplex A k V).d n (n+1) = 0)

/-- The actual extension of the same characteristic cochain has the
same nonzero ambient coefficient in every such larger support. -/
theorem topCellCochain_extension_topClass_ne_zero :
    ((openSupportCochainComplex A k V).pOpcycles n ≫
      ((openSupportCochainComplex A k V).isoHomologyι n (n+1) (by simp) outgoingV).inv ≫
        (openSupportCochainTopClassIso A k V convexV nonemptyV boundedV).hom)
      ((openSupportCochainExtension A k inclusion).f n
        (topCellCochainGenerator A c k)) ≠ 0 := by
  have quotient := topHomologyQuotient_natural K n (topCellCochain_outgoing A c k)
    outgoingV (openSupportCochainExtension A k inclusion)
  have classes := openSupportCochainTopClassIso_natural A k inclusion
    (topCellSupport_convex A c) convexV (topCellSupport_nonempty A c) nonemptyV
    (topCellSupport_bounded A c) boundedV
  have maps : (openSupportCochainExtension A k inclusion).f n ≫
      (openSupportCochainComplex A k V).pOpcycles n ≫
        ((openSupportCochainComplex A k V).isoHomologyι n (n+1) (by simp) outgoingV).inv ≫
          (openSupportCochainTopClassIso A k V convexV nonemptyV boundedV).hom =
      topCellCochainTopFunctional A c k := by
    rw [← Category.assoc, ← Category.assoc, quotient, Category.assoc,
      Category.assoc, classes]
    rfl
  intro zero
  apply topCellCochainTopFunctional_generator_ne_zero A c k
  exact (ConcreteCategory.congr_hom maps (topCellCochainGenerator A c k)).symm.trans zero

end ToricPower.IntegralArrangement
