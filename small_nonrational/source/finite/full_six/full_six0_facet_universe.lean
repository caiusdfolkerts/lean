module
prelude
public import FullSmallFacetUniverse
public import FullSix0FacetUniverseDataPart000
public import FullSix0FacetUniverseDataPart001
public import FullSix0FacetUniverseDataPart002
public import FullSix0FacetUniverseDataPart003
public import FullSix0FacetUniverseDataPart004
public import FullSix0FacetUniverseDataPart005
public import FullSix0FacetUniverseDataPart006
public import FullSix0FacetUniverseDataPart007
public import FullSix0FacetUniverseDataPart008
public import FullSix0FacetUniverseDataPart009
public import FullSix0FacetUniverseDataPart010
public import FullSix0FacetUniverseDataPart011
public import FullSix0FacetUniverseDataPart012
public import FullSix0FacetUniverseDataPart013
public import FullSix0FacetUniverseDataPart014
public import FullSix0FacetUniverseDataPart015
public import FullSix0FacetUniverseDataPart016
public import FullSix0FacetUniverseDataPart017
public import FullSix0FacetUniverseDataPart018
public import FullSix0FacetUniverseDataPart019
public import FullSix0FacetUniverseDataPart020
public import FullSix0FacetUniverseDataPart021
public import FullSix0FacetUniverseDataPart022
public import FullSix0FacetUniverseDataPart023
public import FullSix0FacetUniverseDataPart024
public import FullSix0FacetUniverseDataPart025
public import FullSix0FacetUniverseDataPart026
public import FullSix0FacetUniverseDataPart027
public import FullSix0FacetUniverseDataPart028
public import FullSix0FacetUniverseDataPart029
public import FullSix0FacetUniverseDataPart030
public import FullSix0FacetUniverseDataPart031
public import FullSix0FacetUniverseDataPart032
public import FullSix0FacetUniverseDataPart033
public import FullSix0FacetUniverseDataPart034
public import FullSix0FacetUniverseDataPart035
public import FullSix0FacetUniverseDataPart036

@[expose] public section

/-! The complete common universe for the remaining one-six-facet budget.
Its first6510entries are exactly the existing small-facet universe. -/
namespace Papers.RationalityTen.FacetUniverses.FullSix0
open Papers.RationalityTen.ConcreteGrowth
abbrev cellCount : Nat := 44310
noncomputable def dispatch : Table (Nat → Nat) :=
(.branch 18432
 (.branch 9216
 (.branch 4096
 (.branch 2048
 (.branch 1024
 (.leaf Data.Part000.lookup)
 (.leaf Data.Part001.lookup))
 (.branch 3072
 (.leaf Data.Part002.lookup)
 (.leaf Data.Part003.lookup)))
 (.branch 6144
 (.branch 5120
 (.leaf Data.Part004.lookup)
 (.leaf Data.Part005.lookup))
 (.branch 7168
 (.leaf Data.Part006.lookup)
 (.branch 8192
 (.leaf Data.Part007.lookup)
 (.leaf Data.Part008.lookup)))))
 (.branch 13312
 (.branch 11264
 (.branch 10240
 (.leaf Data.Part009.lookup)
 (.leaf Data.Part010.lookup))
 (.branch 12288
 (.leaf Data.Part011.lookup)
 (.leaf Data.Part012.lookup)))
 (.branch 15360
 (.branch 14336
 (.leaf Data.Part013.lookup)
 (.leaf Data.Part014.lookup))
 (.branch 16384
 (.leaf Data.Part015.lookup)
 (.branch 17408
 (.leaf Data.Part016.lookup)
 (.leaf Data.Part017.lookup))))))
 (.branch 27648
 (.branch 22528
 (.branch 20480
 (.branch 19456
 (.leaf Data.Part018.lookup)
 (.leaf Data.Part019.lookup))
 (.branch 21504
 (.leaf Data.Part020.lookup)
 (.leaf Data.Part021.lookup)))
 (.branch 24576
 (.branch 23552
 (.leaf Data.Part022.lookup)
 (.leaf Data.Part023.lookup))
 (.branch 25600
 (.leaf Data.Part024.lookup)
 (.branch 26624
 (.leaf Data.Part025.lookup)
 (.leaf Data.Part026.lookup)))))
 (.branch 32768
 (.branch 29696
 (.branch 28672
 (.leaf Data.Part027.lookup)
 (.leaf Data.Part028.lookup))
 (.branch 30720
 (.leaf Data.Part029.lookup)
 (.branch 31744
 (.leaf Data.Part030.lookup)
 (.leaf Data.Part031.lookup))))
 (.branch 34816
 (.branch 33792
 (.leaf Data.Part032.lookup)
 (.leaf Data.Part033.lookup))
 (.branch 35840
 (.leaf Data.Part034.lookup)
 (.branch 36864
 (.leaf Data.Part035.lookup)
 (.leaf Data.Part036.lookup)))))))
noncomputable def sixCode (i : Nat) : Nat := (dispatch.get i) i
noncomputable def cells (i : Fin cellCount) : Cell :=
  if h : i.val < 6510 then FullSmall.cells ⟨i.val,h⟩
  else Papers.RationalityTen.Six0PackedCell.unpack (sixCode (i.val-6510))
noncomputable def kind (i : Fin cellCount) : Nat := (cells i).kind
noncomputable def ridgeList := Papers.RationalityTen.ConcreteGrowth.ridgeList cells
noncomputable def literalCompatible (a b : Fin cellCount) : Bool :=
  Papers.RationalityTen.ConcreteGrowth.compatible (cells a) (cells b)

theorem cells_small (i : Fin 6510) :
    cells (Fin.castLE (by decide) i) = FullSmall.cells i := by
  dsimp only [cells, Fin.castLE]
  rw [dif_pos i.isLt]

theorem suffix_kind (i : Fin 37800) :
    (cells ⟨6510 + i.val, by change 6510 + i.val < 44310; omega⟩).kind = 4 := by
  have h : ¬6510 + i.val < 6510 := by omega
  simp only [cells, h, dite_false, Papers.RationalityTen.Six0PackedCell.unpack]
end Papers.RationalityTen.FacetUniverses.FullSix0
