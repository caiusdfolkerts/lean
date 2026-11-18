module
public import RawTargetChunks.C034A
public import RawTargetChunks.C034B

@[expose] public section
namespace Nonrational.TerminalData

noncomputable def chunkTree034 : TargetTree :=
  .branch 64 chunkPart034A chunkPart034B

end Nonrational.TerminalData
