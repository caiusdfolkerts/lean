module
prelude
public import GraphRouteCasesData
public import SharedSmallRoots31

@[expose] public section
noncomputable section

@[reducible] def Papers.RationalityTen.SharedEmptyKeys.Row31.offset : Nat :=
27927
def Papers.RationalityTen.SharedEmptyKeys.Row31.rootCode : Fin
    Papers.RationalityTen.SharedSmallRootCertificates.Row31.rootCount →
  Nat :=
fun i => (Papers.RationalityTen.SharedSmallRootCertificates.Row31.entry i).val.snd
def Papers.RationalityTen.SharedEmptyKeys.Row31.test : Nat → Bool :=
fun i =>
  Decidable.decide
    (Papers.RationalityTen.GraphRoutes.emptyRootKeys.entry (Papers.RationalityTen.SharedEmptyKeys.Row31.offset + i) =
      (31,
        Papers.RationalityTen.SharedSmallRootReplay.complement
          (Papers.RationalityTen.SharedEmptyKeys.Row31.rootCode
            (Fin.ofNat Papers.RationalityTen.SharedSmallRootCertificates.Row31.rootCount i))))

