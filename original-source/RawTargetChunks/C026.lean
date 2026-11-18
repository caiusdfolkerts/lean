module
public import RawTargetChunks.C026A
public import RawTargetChunks.C026B

@[expose] public section
namespace Nonrational.TerminalData

noncomputable def chunkTree026 : TargetTree :=
  .branch 64 chunkPart026A chunkPart026B

end Nonrational.TerminalData
