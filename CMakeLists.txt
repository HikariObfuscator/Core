add_llvm_library(LLVMObfuscation
  FunctionCallObfuscate.cpp
  CryptoUtils.cpp
  BogusControlFlow.cpp
  Substitution.cpp
  Flattening.cpp
  Utils.cpp
  SplitBasicBlocks.cpp
  AntiClassDump.cpp
  StringEncryption.cpp
  IndirectBranch.cpp
  FunctionWrapper.cpp
  Obfuscation.cpp
  DEPENDS
  intrinsics_gen
  )
execute_process(
  COMMAND git log -1 --format=%H
  WORKING_DIRECTORY ${CMAKE_CURRENT_LIST_DIR}
  OUTPUT_VARIABLE HIKARI_GIT_COMMIT_HASH
  OUTPUT_STRIP_TRAILING_WHITESPACE
)
target_compile_definitions(LLVMObfuscation PRIVATE "-DGIT_COMMIT_HASH=\"${HIKARI_GIT_COMMIT_HASH}\"")
