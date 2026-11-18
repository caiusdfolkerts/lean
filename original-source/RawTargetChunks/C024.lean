module
public import RawTargetChunks.C024A
public import RawTargetChunks.C024B

@[expose] public section
namespace Nonrational.TerminalData

noncomputable def chunkTree024 : TargetTree :=
  .branch 64 chunkPart024A chunkPart024B

end Nonrational.TerminalData
