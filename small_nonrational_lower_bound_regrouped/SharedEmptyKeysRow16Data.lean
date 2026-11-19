module
prelude
public import GraphRouteCasesData
public import SharedSmallRoots16

@[expose] public section
noncomputable section

@[reducible] def Papers.RationalityTen.SharedEmptyKeys.Row16.offset : Nat :=
0
def Papers.RationalityTen.SharedEmptyKeys.Row16.rootCode : Fin
    Papers.RationalityTen.SharedSmallRootCertificates.Row16.rootCount →
  Nat :=
fun i => (Papers.RationalityTen.SharedSmallRootCertificates.Row16.entry i).val.snd
def Papers.RationalityTen.SharedEmptyKeys.Row16.test : Nat → Bool :=
fun i =>
  Decidable.decide
    (Papers.RationalityTen.GraphRoutes.emptyRootKeys.entry (Papers.RationalityTen.SharedEmptyKeys.Row16.offset + i) =
      (16,
        Papers.RationalityTen.SharedSmallRootReplay.complement
          (Papers.RationalityTen.SharedEmptyKeys.Row16.rootCode
            (Fin.ofNat Papers.RationalityTen.SharedSmallRootCertificates.Row16.rootCount i))))

