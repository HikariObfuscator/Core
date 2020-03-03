// For open-source license, please refer to [License](https://github.com/HikariObfuscator/Hikari/wiki/License).
//===----------------------------------------------------------------------===//
#include "llvm/Transforms/Obfuscation/StringEncryption.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Value.h"
#include "llvm/Pass.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/Obfuscation/CryptoUtils.h"
#include "llvm/Transforms/Obfuscation/Obfuscation.h"
#include "llvm/Transforms/Obfuscation/Utils.h"
#include <cstdlib>
#include <iostream>
#include <map>
#include <set>
#include <string>
using namespace llvm;
using namespace std;
namespace llvm {
struct StringEncryption : public ModulePass {
  static char ID;
  map<Function * /*Function*/, GlobalVariable * /*Decryption Status*/>
      encstatus;
  bool flag;
  StringEncryption() : ModulePass(ID) { this->flag = true; }
  StringEncryption(bool flag) : ModulePass(ID) { this->flag = flag; }
  StringRef getPassName() const override {
    return StringRef("StringEncryption");
  }
  bool runOnModule(Module &M) override {
    // in runOnModule. We simple iterate function list and dispatch functions
    // to handlers
    for (Module::iterator iter = M.begin(); iter != M.end(); iter++) {
      Function *F = &(*iter);

      if (toObfuscate(flag, F, "strenc")) {
        errs() << "Running StringEncryption On " << F->getName() << "\n";
        Constant *S = ConstantInt::get(Type::getInt32Ty(M.getContext()), 0);
        GlobalVariable *GV = new GlobalVariable(
            M, S->getType(), false, GlobalValue::LinkageTypes::PrivateLinkage,
            S, "");
        encstatus[F] = GV;
        HandleFunction(F);
      }
    }
    return true;
  } // End runOnModule
  void HandleFunction(Function *Func) {
    FixFunctionConstantExpr(Func);
    set<GlobalVariable *> Globals;
    set<User *> Users;
    for (BasicBlock &BB : *Func) {
      for (Instruction &I : BB) {
        for (Value *Op : I.operands()) {
          if (GlobalVariable *G = dyn_cast<GlobalVariable>(Op->stripPointerCasts())) {
            if(User* U=dyn_cast<User>(Op)){
              Users.insert(U);
            }
            Users.insert(&I);
            Globals.insert(G);
          }
        }
      }
    }
    set<GlobalVariable *> rawStrings;
    set<GlobalVariable *> objCStrings;
    map<GlobalVariable *, pair<Constant *, GlobalVariable *>> GV2Keys;
    map<GlobalVariable * /*old*/, pair<GlobalVariable * /*encrypted*/, GlobalVariable * /*decrypt space*/>> old2new;
    for (GlobalVariable *GV : Globals) {
      if (GV->hasInitializer() &&
          GV->getSection() != StringRef("llvm.metadata") &&
          GV->getSection().find(StringRef("__objc")) == string::npos &&
          GV->getName().find("OBJC") == string::npos) {
        if (GV->getInitializer()->getType() ==
            Func->getParent()->getTypeByName("struct.__NSConstantString_tag")) {
          objCStrings.insert(GV);
          rawStrings.insert(
              cast<GlobalVariable>(cast<ConstantStruct>(GV->getInitializer())
                                       ->getOperand(2)
                                       ->stripPointerCasts()));

        } else if (isa<ConstantDataSequential>(GV->getInitializer())) {
          rawStrings.insert(GV);
        }else if(isa<ConstantArray>(GV->getInitializer())){
           ConstantArray* CA=cast<ConstantArray>(GV->getInitializer());
           for(unsigned i=0;i<CA->getNumOperands();i++){
             Value* op=CA->getOperand(i)->stripPointerCasts();
             if(GlobalVariable* GV=dyn_cast<GlobalVariable>(op)){
               Globals.insert(GV);
             }
           }

        }
      }
    }
    for (GlobalVariable *GV : rawStrings) {
      if (GV->getInitializer()->isZeroValue() ||
          GV->getInitializer()->isNullValue()) {
        continue;
      }
      ConstantDataSequential *CDS =
          cast<ConstantDataSequential>(GV->getInitializer());
      Type *memberType = CDS->getElementType();
      // Ignore non-IntegerType
      if (!isa<IntegerType>(memberType)) {
        continue;
      }
      IntegerType *intType = cast<IntegerType>(memberType);
      Constant *KeyConst = NULL;
      Constant *EncryptedConst = NULL;
      Constant *DummyConst = NULL;
      if (intType == Type::getInt8Ty(GV->getParent()->getContext())) {
        vector<uint8_t> keys;
        vector<uint8_t> encry;
        vector<uint8_t> dummy;
        for (unsigned i = 0; i < CDS->getNumElements(); i++) {
          uint8_t K = cryptoutils->get_uint8_t();
          uint64_t V = CDS->getElementAsInteger(i);
          keys.push_back(K);
          encry.push_back(K ^ V);
          dummy.push_back(rand());
        }
        KeyConst = ConstantDataArray::get(GV->getParent()->getContext(),
                                          ArrayRef<uint8_t>(keys));
        EncryptedConst = ConstantDataArray::get(GV->getParent()->getContext(),
                                                ArrayRef<uint8_t>(encry));
        DummyConst = ConstantDataArray::get(GV->getParent()->getContext(),
                                                ArrayRef<uint8_t>(dummy));

      } else if (intType == Type::getInt16Ty(GV->getParent()->getContext())) {
        vector<uint16_t> keys;
        vector<uint16_t> encry;
        vector<uint16_t> dummy;
        for (unsigned i = 0; i < CDS->getNumElements(); i++) {
          uint16_t K = cryptoutils->get_uint16_t();
          uint64_t V = CDS->getElementAsInteger(i);
          keys.push_back(K);
          encry.push_back(K ^ V);
          dummy.push_back(rand());
        }
        KeyConst = ConstantDataArray::get(GV->getParent()->getContext(),
                                          ArrayRef<uint16_t>(keys));
        EncryptedConst = ConstantDataArray::get(GV->getParent()->getContext(),
                                                ArrayRef<uint16_t>(encry));
        DummyConst = ConstantDataArray::get(GV->getParent()->getContext(),
                                                ArrayRef<uint16_t>(dummy));
      } else if (intType == Type::getInt32Ty(GV->getParent()->getContext())) {
        vector<uint32_t> keys;
        vector<uint32_t> encry;
        vector<uint32_t> dummy;
        for (unsigned i = 0; i < CDS->getNumElements(); i++) {
          uint32_t K = cryptoutils->get_uint32_t();
          uint64_t V = CDS->getElementAsInteger(i);
          keys.push_back(K);
          encry.push_back(K ^ V);
          dummy.push_back(rand());
        }
        KeyConst = ConstantDataArray::get(GV->getParent()->getContext(),
                                          ArrayRef<uint32_t>(keys));
        EncryptedConst = ConstantDataArray::get(GV->getParent()->getContext(),
                                                ArrayRef<uint32_t>(encry));
        DummyConst = ConstantDataArray::get(GV->getParent()->getContext(),
                                                ArrayRef<uint32_t>(dummy));
      } else if (intType == Type::getInt64Ty(GV->getParent()->getContext())) {
        vector<uint64_t> keys;
        vector<uint64_t> encry;
        vector<uint64_t> dummy;
        for (unsigned i = 0; i < CDS->getNumElements(); i++) {
          uint64_t K = cryptoutils->get_uint64_t();
          uint64_t V = CDS->getElementAsInteger(i);
          keys.push_back(K);
          encry.push_back(K ^ V);
          dummy.push_back(rand());
        }
        KeyConst = ConstantDataArray::get(GV->getParent()->getContext(),
                                          ArrayRef<uint64_t>(keys));
        EncryptedConst = ConstantDataArray::get(GV->getParent()->getContext(),
                                                ArrayRef<uint64_t>(encry));
        DummyConst = ConstantDataArray::get(GV->getParent()->getContext(),
                                                ArrayRef<uint64_t>(dummy));
      } else {
        errs() << "Unsupported CDS Type\n";
        abort();
      }
      // Prepare new rawGV
      GlobalVariable *EncryptedRawGV = new GlobalVariable(
          *(GV->getParent()), EncryptedConst->getType(), false,
          GV->getLinkage(), EncryptedConst, "EncryptedString", nullptr,
          GV->getThreadLocalMode(), GV->getType()->getAddressSpace());
      GlobalVariable *DecryptSpaceGV = new GlobalVariable(
          *(GV->getParent()), DummyConst->getType(), false,
          GV->getLinkage(), DummyConst, "DecryptSpace", nullptr,
          GV->getThreadLocalMode(), GV->getType()->getAddressSpace());
      old2new[GV] = make_pair(EncryptedRawGV, DecryptSpaceGV);
      GV2Keys[DecryptSpaceGV] = make_pair(KeyConst, EncryptedRawGV);
    }
    // Now prepare ObjC new GV
    for (GlobalVariable *GV : objCStrings) {
      ConstantStruct *CS = cast<ConstantStruct>(GV->getInitializer());
      GlobalVariable *oldrawString = cast<GlobalVariable>(CS->getOperand(2)->stripPointerCasts());
      if (old2new.find(oldrawString) == old2new.end()) { // Filter out zero initializers
        continue;
      }
      GlobalVariable *EncryptedOCGV = ObjectivCString(GV, "EncryptedStringObjC", oldrawString, old2new[oldrawString].first, CS);
      GlobalVariable *DecryptSpaceOCGV = ObjectivCString(GV, "DecryptSpaceObjC", oldrawString, old2new[oldrawString].second, CS);
      old2new[GV] = make_pair(EncryptedOCGV, DecryptSpaceOCGV);
    } // End prepare ObjC new GV
    if(old2new.empty() || GV2Keys.empty())
      return;
    // Replace Uses
    for (User *U : Users) {
      for (map<GlobalVariable *, pair<GlobalVariable *, GlobalVariable *>>::iterator iter =
               old2new.begin();
           iter != old2new.end(); ++iter) {
        U->replaceUsesOfWith(iter->first, iter->second.second);
        iter->first->removeDeadConstantUsers();
      }
    } // End Replace Uses
    // CleanUp Old ObjC GVs
    for (GlobalVariable *GV : objCStrings) {
      if (GV->getNumUses() == 0) {
        GV->dropAllReferences();
        old2new.erase(GV);
        GV->eraseFromParent();
      }
    }
    // CleanUp Old Raw GVs
    for (map<GlobalVariable *, pair<GlobalVariable *, GlobalVariable *>>::iterator iter =
             old2new.begin();
         iter != old2new.end(); ++iter) {
      GlobalVariable *toDelete = iter->first;
      toDelete->removeDeadConstantUsers();
      if (toDelete->getNumUses() == 0) {
        toDelete->dropAllReferences();
        toDelete->eraseFromParent();
      }
    }
    GlobalVariable *StatusGV = encstatus[Func];
    /*
      - Split Original EntryPoint BB into A and C.
      - Create new BB as Decryption BB between A and C. Adjust the terminators
      into: A (Alloca a new array containing all)
              |
              B(If not decrypted)
              |
              C
    */
    BasicBlock *A = &(Func->getEntryBlock());
    BasicBlock *C = A->splitBasicBlock(A->getFirstNonPHIOrDbgOrLifetime());
    C->setName("PrecedingBlock");
    BasicBlock *B =
        BasicBlock::Create(Func->getContext(), "StringDecryptionBB", Func, C);
    // Change A's terminator to jump to B
    // We'll add new terminator to jump C later
    BranchInst *newBr = BranchInst::Create(B);
    ReplaceInstWithInst(A->getTerminator(), newBr);
    IRBuilder<> IRB(A->getFirstNonPHIOrDbgOrLifetime());
    // Insert DecryptionCode
    HandleDecryptionBlock(B, C, GV2Keys);
    // Add atomic load checking status in A
    LoadInst *LI = IRB.CreateLoad(StatusGV, "LoadEncryptionStatus");
    LI->setAtomic(AtomicOrdering::Acquire); // Will be released at the start of
                                            // C
    LI->setAlignment(4);
    Value *condition = IRB.CreateICmpEQ(
        LI, ConstantInt::get(Type::getInt32Ty(Func->getContext()), 0));
    A->getTerminator()->eraseFromParent();
    BranchInst::Create(B, C, condition, A);
    // Add StoreInst atomically in C start
    // No matter control flow is coming from A or B, the GVs must be decrypted
    IRBuilder<> IRBC(C->getFirstNonPHIOrDbgOrLifetime());
    StoreInst *SI = IRBC.CreateStore(
        ConstantInt::get(Type::getInt32Ty(Func->getContext()), 1), StatusGV);
    SI->setAlignment(4);
    SI->setAtomic(AtomicOrdering::Release); // Release the lock acquired in LI

  } // End of HandleFunction

  GlobalVariable *ObjectivCString(GlobalVariable *GV, string name, GlobalVariable *oldrawString, GlobalVariable *newString, ConstantStruct *CS) {
      Value *zero = ConstantInt::get(Type::getInt32Ty(GV->getContext()), 0);
      vector<Constant *> vals;
      vals.push_back(CS->getOperand(0));
      vals.push_back(CS->getOperand(1));
      Constant *GEPed = ConstantExpr::getInBoundsGetElementPtr(nullptr, newString, {zero, zero});
      if (GEPed->getType() == CS->getOperand(2)->getType()) {
        vals.push_back(GEPed);
      } else {
        Constant *BitCasted = ConstantExpr::getBitCast(newString, CS->getOperand(2)->getType());
        vals.push_back(BitCasted);
      }
      vals.push_back(CS->getOperand(3));
      Constant *newCS = ConstantStruct::get(CS->getType(), ArrayRef<Constant *>(vals));
      return new GlobalVariable(
          *(GV->getParent()), newCS->getType(), false, GV->getLinkage(), newCS,
          name.c_str(), nullptr, GV->getThreadLocalMode(),
          GV->getType()->getAddressSpace());
  }

  void HandleDecryptionBlock(BasicBlock *B, BasicBlock *C,
                             map<GlobalVariable *, pair<Constant *, GlobalVariable *>> &GV2Keys) {
    IRBuilder<> IRB(B);
    Value *zero = ConstantInt::get(Type::getInt32Ty(B->getContext()), 0);
    for (map<GlobalVariable *, pair<Constant *, GlobalVariable *>>::iterator iter = GV2Keys.begin();
         iter != GV2Keys.end(); ++iter) {
      ConstantDataArray *CastedCDA = cast<ConstantDataArray>(iter->second.first);
      // Prevent optimization of encrypted data
      appendToCompilerUsed(*iter->second.second->getParent(),
                           {iter->second.second});
      // Element-By-Element XOR so the fucking verifier won't complain
      // Also, this hides keys
      for (unsigned i = 0; i < CastedCDA->getType()->getNumElements(); i++) {
        Value *offset = ConstantInt::get(Type::getInt32Ty(B->getContext()), i);
        Value *EncryptedGEP = IRB.CreateGEP(iter->second.second, {zero, offset});
        Value *DecryptedGEP = IRB.CreateGEP(iter->first, {zero, offset});
        LoadInst *LI = IRB.CreateLoad(EncryptedGEP, "EncryptedChar");
        Value *XORed = IRB.CreateXor(LI, CastedCDA->getElementAsConstant(i));
        IRB.CreateStore(XORed, DecryptedGEP);
      }
    }
    IRB.CreateBr(C);
  } // End of HandleDecryptionBlock
  bool doFinalization(Module &M) override {
    encstatus.clear();
    return false;
  }
};
ModulePass *createStringEncryptionPass() { return new StringEncryption(); }
ModulePass *createStringEncryptionPass(bool flag) {
  return new StringEncryption(flag);
}
} // namespace llvm

char StringEncryption::ID = 0;
INITIALIZE_PASS(StringEncryption, "strcry", "Enable String Encryption", true,
                true)
