module
public import RawTargetChunks.C028A
public import RawTargetChunks.C028B

@[expose] public section
namespace Nonrational.TerminalData

noncomputable def chunkTree028 : TargetTree :=
  .branch 64 chunkPart028A chunkPart028B

end Nonrational.TerminalData
