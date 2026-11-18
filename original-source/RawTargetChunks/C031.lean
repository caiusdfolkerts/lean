module
public import RawTargetChunks.C031A
public import RawTargetChunks.C031B

@[expose] public section
namespace Nonrational.TerminalData

noncomputable def chunkTree031 : TargetTree :=
  .branch 64 chunkPart031A chunkPart031B

end Nonrational.TerminalData
