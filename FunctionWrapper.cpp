// For open-source license, please refer to [License](https://github.com/HikariObfuscator/Hikari/wiki/License).
//===----------------------------------------------------------------------===//
#include "llvm/IR/CallSite.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Value.h"
#include "llvm/Pass.h"
#include "llvm/Transforms/Obfuscation/Obfuscation.h"
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <string>
using namespace llvm;
using namespace std;
static cl::opt<int>
    ProbRate("fw_prob",
             cl::desc("Choose the probability [%] For Each CallSite To Be "
                      "Obfuscated By FunctionWrapper"),
             cl::value_desc("Probability Rate"), cl::init(30), cl::Optional);
static cl::opt<int> ObfTimes(
    "fw_times",
    cl::desc(
        "Choose how many time the FunctionWrapper pass loop on a CallSite"),
    cl::value_desc("Number of Times"), cl::init(2), cl::Optional);
namespace llvm {
struct FunctionWrapper : public ModulePass {
  static char ID;
  bool flag;
  FunctionWrapper() : ModulePass(ID) { this->flag = true; }
  FunctionWrapper(bool flag) : ModulePass(ID) { this->flag = flag; }
  StringRef getPassName() const override {
    return StringRef("FunctionWrapper");
  }
  bool runOnModule(Module &M) override {
    vector<CallSite *> callsites;
    for (Module::iterator iter = M.begin(); iter != M.end(); iter++) {
      Function &F = *iter;
      if (toObfuscate(flag, &F, "fw")) {
        errs() << "Running FunctionWrapper On " << F.getName() << "\n";
        for (inst_iterator fi = inst_begin(&F); fi != inst_end(&F); fi++) {
          Instruction *Inst = &*fi;
          if (isa<CallInst>(Inst) || isa<InvokeInst>(Inst)) {
            if ((int)llvm::cryptoutils->get_range(100) <= ProbRate) {
              callsites.push_back(new CallSite(Inst));
            }
          }
        }
      }
    }
    for (CallSite *CS : callsites) {
      for (int i = 0; i < ObfTimes && CS != nullptr; i++) {
        CS = HandleCallSite(CS);
      }
    }
    return true;
  } // End of runOnModule
  CallSite *HandleCallSite(CallSite *CS) {
    Value *calledFunction = CS->getCalledFunction();
    if (calledFunction == nullptr) {
      calledFunction = CS->getCalledValue()->stripPointerCasts();
    }
    // Filter out IndirectCalls that depends on the context
    // Otherwise It'll be blantantly troublesome since you can't reference an
    // Instruction outside its BB  Too much trouble for a hobby project
    // To be precise, we only keep CS that refers to a non-intrinsic function
    // either directly or through casting
    if (calledFunction == nullptr ||
        (!isa<ConstantExpr>(calledFunction) &&
         !isa<Function>(calledFunction)) ||
        CS->getIntrinsicID() != Intrinsic::ID::not_intrinsic) {
      return nullptr;
    }
    if (Function *tmp = dyn_cast<Function>(calledFunction)) {
      if (tmp->getName().startswith("clang.")) {
        // Clang Intrinsic
        return nullptr;
      }
      for(auto argiter = tmp->arg_begin(); argiter!= tmp->arg_end(); ++argiter) {
       Argument& arg=*(argiter);
       if(arg.hasByValAttr()){
        // Arguments with byval attribute yields issues without proper handling.
        // The "proper" method to handle this is to revisit and patch attribute stealing code.
        // Technically readonly attr probably should also get filtered out here.

        // Nah too much work. This would do for open-source version since private already
        // this pass with more advanced solutions 
	return nullptr;       
       }   
      }
    }
    // Create a new function which in turn calls the actual function
    vector<Type *> types;
    for (unsigned i = 0; i < CS->getNumArgOperands(); i++) {
      types.push_back(CS->getArgOperand(i)->getType());
    }
    FunctionType *ft =
        FunctionType::get(CS->getType(), ArrayRef<Type *>(types), false);
    Function *func =
        Function::Create(ft, GlobalValue::LinkageTypes::InternalLinkage,
                         "HikariFunctionWrapper", CS->getParent()->getModule());
      //Trolling was all fun and shit so old implementation forced this symbol to exist in all objects
    appendToCompilerUsed(*func->getParent(), {func});
    BasicBlock *BB = BasicBlock::Create(func->getContext(), "", func);
    IRBuilder<> IRB(BB);
    vector<Value *> params;
    for (auto arg = func->arg_begin(); arg != func->arg_end(); arg++) {
      params.push_back(arg);
    }
    Value *retval = IRB.CreateCall(ConstantExpr::getBitCast(cast<Function>(calledFunction),CS->getCalledValue()->getType()), ArrayRef<Value *>(params));
    if (ft->getReturnType()->isVoidTy()) {
      IRB.CreateRetVoid();
    } else {
      IRB.CreateRet(retval);
    }
    CS->setCalledFunction(func);
    CS->mutateFunctionType(ft);
    Instruction *Inst = CS->getInstruction();
    delete CS;
    return new CallSite(Inst);
  }
};
ModulePass *createFunctionWrapperPass() { return new FunctionWrapper(); }
ModulePass *createFunctionWrapperPass(bool flag) {
  return new FunctionWrapper(flag);
}
} // namespace llvm

char FunctionWrapper::ID = 0;
INITIALIZE_PASS(FunctionWrapper, "funcwra", "Enable FunctionWrapper.", true,
                true)
