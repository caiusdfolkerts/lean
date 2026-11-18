module

public import ToricPower.DiagonalCellFrames
public import ToricPower.DiagonalStripComparison
public import ToricPower.DiagonalGlobalSquare

/-!
# The actual cellular boundary in the literal Cartier frames

The globally defined finite incidence column has character entry `(a,-a)`.
In the independently chosen local Cartier frames its character is
`(a+q_left,target-q_left,source, -a+q_right,target-q_right,source)`.
Both entries are proved regular from the genuine attaching-map support.

The resulting finite matrix is proved equal to the genuine cellular
differential under the explicit free-module basis equivalences. Its
exactness is therefore inherited from the contractible weight strips;
neither exactness nor the matrix comparison is assumed in frame data.

Candidate source pending compilation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Topology Topology.RelCWComplex
open scoped Classical BigOperators

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (k : Type) [CommRing k] (A : Fin s → Fin n → ℤ)
  (S T : Set (Fin s))

local instance diagonalFramedBoundaryPeriodicCW : CWComplex (arrangementCarrier A) :=
  periodicArrangementCWComplex A

local instance diagonalFramedBoundaryStripCW (u : Fin n → ℤ) :
    CWComplex (diagonalStripCarrier A S T u) :=
  inferInstanceAs (CWComplex (diagonalStripSubcomplex A S T u : Set (Fin n → ℝ)))

theorem arrangement_boundaryColumn_translate (v : Fin n → ℤ) (d : ℕ)
    (j : Cell (augmentedForms A) (d+1)) :
    TauCeti.cellularBoundaryColumn (arrangementCarrier A) k d
        (translateCell A v j) =
      Finsupp.mapDomain (translateCell A v)
        (TauCeti.cellularBoundaryColumn (arrangementCarrier A) k d j) :=
  cellularBoundaryColumn_naturality (arrangementCarrier A) (arrangementCarrier A)
    (arrangementTranslation_cellular A v) k
    (fun _ => translateCell A v) (arrangementTranslation_characteristic A v) d j

variable {S T} {d : ℕ}
  (F : DiagonalCellFrames A S T d) (G : DiagonalCellFrames A S T (d+1))
  (j : NormalizedCell A (d+1))

local instance termsFintype : Fintype (DiagonalGlobalColumnTerm k A d j) :=
  Fintype.ofFinite _

/-- The literal normalized character pair of one supported global
monomial map. Membership follows from its actual incidence support. -/
def diagonalFramedMonomial (p : DiagonalGlobalColumnTerm k A d j) :
    rayCharacterMonoid A S × rayCharacterMonoid A T :=
  (⟨p.val.2+F.left p.val.1-G.left j,by
      intro ρ hρ
      rw [rayPairing_sub,rayPairing_add,F.left_eq _ ρ hρ,G.left_eq _ ρ hρ]
      have h := (diagonalGlobalColumnTerm_regular k A d j p ρ).1
      omega⟩,
    ⟨-p.val.2+F.right p.val.1-G.right j,by
      intro ρ hρ
      have hneg : rayPairing A (-p.val.2) ρ = -rayPairing A p.val.2 ρ := by
        simpa using rayPairing_sub A 0 p.val.2 ρ
      rw [rayPairing_sub,rayPairing_add,hneg,F.right_eq _ ρ hρ,G.right_eq _ ρ hρ]
      have h := (diagonalGlobalColumnTerm_regular k A d j p ρ).2
      omega⟩)

def diagonalFramedTarget (p : DiagonalGlobalColumnTerm k A d j) :
    {c : Cell (augmentedForms A) d // stripCellAllowed A S T (G.weight j 0) c} :=
  ⟨translateCell A (-G.left j+p.val.2) p.val.1.val,by
    apply (stripCellAllowed_translate_iff A S T (G.weight j 0)
      (-G.left j+p.val.2) p.val.1.val).mpr
    apply diagonalGlobalTerm_monomialAllowed A k S T (G.weight j 0) (-G.left j) d j _ p
    have h := G.allowed j 0
    simpa only [diagonalMonomialAllowed, Prod.fst_zero, Prod.fst, Prod.snd,
      AddSubmonoid.coe_zero,zero_sub] using
      (stripCellAllowed_translate_iff A S T (G.weight j 0)
        (0-G.left j) j.val).mp h⟩

theorem diagonalFramedMonomial_cell (p : DiagonalGlobalColumnTerm k A d j) :
    F.cell p.val.1 (diagonalFramedMonomial k A F G j p) =
      ⟨G.weight j 0,diagonalFramedTarget k A G j p⟩ := by
  have hw : F.weight p.val.1 (diagonalFramedMonomial k A F G j p) = G.weight j 0 := by
    change ((p.val.2+F.left p.val.1-G.left j)-F.left p.val.1)+
      ((-p.val.2+F.right p.val.1-G.right j)-F.right p.val.1) =
        (0-G.left j)+(0-G.right j)
    abel
  apply diagonalChartCell_ext A hw
  change translateCell A ((p.val.2+F.left p.val.1-G.left j)-F.left p.val.1) p.val.1.val =
    translateCell A (-G.left j+p.val.2) p.val.1.val
  congr 1
  abel

/-- The independently defined strip boundary is exactly the finite
global incidence sum after translating into the selected source frame. -/
theorem diagonalFramedStripColumn :
    TauCeti.cellularBoundaryColumn (diagonalStripCarrier A S T (G.weight j 0)) k d
        (G.cell j 0).2 =
      ∑ p : DiagonalGlobalColumnTerm k A d j,
        Finsupp.single (diagonalFramedTarget k A G j p)
          (diagonalGlobalColumn k A d j p.val) := by
  apply Finsupp.mapDomain_injective Subtype.val_injective
  refine (diagonalStrip_boundaryColumn_ambient A k S T
    (G.weight j 0) d (G.cell j 0).2).symm.trans ?_
  simp only [Finsupp.mapDomain_finsetSum,Finsupp.mapDomain_single]
  change TauCeti.cellularBoundaryColumn (arrangementCarrier A) k d
      (translateCell A (0-G.left j) j.val) = _
  rw [zero_sub,arrangement_boundaryColumn_translate]
  have hsum :
      Finsupp.mapDomain (translateCell A (-G.left j))
          (TauCeti.cellularBoundaryColumn (arrangementCarrier A) k d j.val) =
        (diagonalGlobalColumn k A d j).sum (fun p r =>
          Finsupp.single (translateCell A (-G.left j+p.2) p.1.val) r) := by
    rw [diagonalGlobalColumn_sum]
    unfold Finsupp.mapDomain
    apply Finsupp.sum_congr
    intro c hc
    congr 1
    change translateCell A (-G.left j) c =
      translateCell A (-G.left j+coordinateCeilings A c) (normalizeCell A c).val
    rw [add_comm (-G.left j) (coordinateCeilings A c),
      ← translateCell_add,translate_normalizeCell]
  rw [hsum,Finsupp.sum,
    Finset.sum_subtype (diagonalGlobalColumn k A d j).support (fun _ => Iff.rfl)] <;> rfl

/-- The actual finite column as polynomials in the local Cartier frames. -/
def diagonalFramedGlobalColumn : NormalizedCell A d →₀ DiagonalChartRing k A S T :=
  ∑ p : DiagonalGlobalColumnTerm k A d j,
    Finsupp.single p.val.1
      (AddMonoidAlgebra.single (diagonalFramedMonomial k A F G j p)
        (diagonalGlobalColumn k A d j p.val))

/-- Applying the independently constructed local free-module basis
equivalence turns the finite global matrix column into the actual
cellular boundary column. -/
theorem diagonalFramedGlobalColumn_compare :
    F.linearEquiv k (diagonalFramedGlobalColumn k A F G j) =
      diagonalChartBoundaryColumn k A S T d (G.cell j 0) := by
  unfold diagonalFramedGlobalColumn
  rw [map_sum]
  simp_rw [F.linearEquiv_single,diagonalFramedMonomial_cell]
  unfold diagonalChartBoundaryColumn
  change _ = diagonalWeightInjection k A S T (G.weight j 0) d
    (TauCeti.cellularBoundaryColumn (diagonalStripCarrier A S T (G.weight j 0)) k d
      (G.cell j 0).2)
  rw [diagonalFramedStripColumn]
  simp [diagonalWeightInjection,Finsupp.mapDomain_finsetSum,Finsupp.mapDomain_single]

/-- The finite local matrix of the actual global sheaf boundary. -/
def diagonalFramedBoundary :
    (NormalizedCell A (d+1) →₀ DiagonalChartRing k A S T) →ₗ[DiagonalChartRing k A S T]
      (NormalizedCell A d →₀ DiagonalChartRing k A S T) :=
  Finsupp.linearCombination (DiagonalChartRing k A S T)
    (diagonalFramedGlobalColumn k A F G)

/-- Equality of the full matrices over the actual chart ring, obtained
from the actual geometric incidence calculation on their basis columns. -/
theorem diagonalFramedBoundary_compare :
    (F.linearEquiv k).toLinearMap.comp (diagonalFramedBoundary k A F G) =
      (diagonalChartBoundaryLinear k A S T d).comp (G.linearEquiv k).toLinearMap := by
  apply Finsupp.lhom_ext
  intro j r
  change F.linearEquiv k
      (diagonalFramedBoundary k A F G (Finsupp.single j r)) =
    diagonalChartBoundaryLinear k A S T d
      (G.linearEquiv k (Finsupp.single j r))
  have hsingle : (Finsupp.single j r : NormalizedCell A (d+1) →₀ DiagonalChartRing k A S T) =
      r • Finsupp.single j 1 := by simp
  rw [hsingle,map_smul,map_smul,map_smul,map_smul]
  congr 1
  rw [diagonalFramedBoundary,Finsupp.linearCombination_single,one_smul,
    diagonalFramedGlobalColumn_compare]
  change diagonalChartBoundaryColumn k A S T d (G.cell j 0) =
    diagonalChartBoundary k A S T d
      (G.linearEquiv k (Finsupp.single j (1 : DiagonalChartRing k A S T)))
  have hone : (1 : DiagonalChartRing k A S T) = AddMonoidAlgebra.single 0 1 := rfl
  rw [hone,G.linearEquiv_single,diagonalChartBoundary_single,one_smul]

end ToricPower.IntegralArrangement
