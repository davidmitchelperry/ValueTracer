// ValueTracer.cpp 
// Instruments the program with printf statements
// to track variable changes/updates

#define DEBUG_TYPE "hello"
#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/ValueSymbolTable.h"
#include "llvm/IR/ValueMap.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/TypeBuilder.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstrTypes.h"
#include <llvm/IR/DerivedTypes.h>

#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/Dwarf.h"

#include "llvm/IR/IntrinsicInst.h"

#include <map>
#include <vector>
#include <sstream>
using namespace llvm;

Module *mod_ptr;

Constant *geti8StrVal(Module &M, char const *str, Twine const &name) {

  LLVMContext &ctx = M.getContext();
  Constant *strConstant = ConstantDataArray::getString(ctx, str);
  GlobalVariable *GVStr =
      new GlobalVariable(M, strConstant->getType(), true,
                         GlobalValue::InternalLinkage, strConstant, name);
  Constant *zero = Constant::getNullValue(IntegerType::getInt32Ty(ctx));
  Constant *indices[] = { zero, zero };
  Constant *strVal = ConstantExpr::getGetElementPtr(NULL, GVStr, indices, true);
  return strVal;
}

static Function *printf_prototype(LLVMContext &ctx, Module *mod) {

  // FunctionType *printf_type =
  //    TypeBuilder<int(char *, ...), false>::get(getGlobalContext());

  FunctionType *printf_type =
      TypeBuilder<int(char *, ...), false>::get(mod->getContext());

  Function *func = cast<Function>(mod->getOrInsertFunction(
      "printf", printf_type,
      AttributeSet().addAttribute(mod->getContext(), 1U, Attribute::NoAlias)));

  return func;
}

void buildArrayPrintingLoop(Instruction *inst, int arraySize, Value *array) {

  LLVMContext &ctx = mod_ptr->getContext();
  IRBuilder<> builder(ctx);
  Function *printf_func = printf_prototype(ctx, mod_ptr);

  // Insert print instruction indicating start of an array
  // trace after the store
  Instruction *after_store = inst->getNextNode();
  CallInst *print_array_start = builder.CreateCall(
      printf_func,
      geti8StrVal(*mod_ptr, ("\ntrace:array_start:" + array->getName().str() +
                             "\n").c_str(),
                  "formatString"));
  print_array_start->insertBefore(inst);

  // allocate an int for counting loop iterations
  AllocaInst *print_counter_alloca =
      builder.CreateAlloca(Type::getInt32Ty(ctx), nullptr, "print_counter");
  print_counter_alloca->insertAfter(inst);

  // Allocate the counter's value to 0
  StoreInst *print_counter_init = builder.CreateStore(
      ConstantInt::get(Type::getInt32Ty(ctx), 0), print_counter_alloca);
  print_counter_init->insertAfter(print_counter_alloca);

  // Load the variables value onto the stack
  LoadInst *print_counter_load = builder.CreateLoad(print_counter_alloca);
  print_counter_load->insertAfter(print_counter_init);

  // Create the BB executed when the loop is entered
  BasicBlock *cond_block =
      print_counter_load->getParent()->splitBasicBlock(print_counter_load);

  // Create the loop conditional (loop_ct < array size)
  Instruction *print_compare = dyn_cast<Instruction>(builder.CreateICmpSLT(
      print_counter_load, ConstantInt::get(Type::getInt32Ty(ctx), arraySize)));
  print_compare->insertAfter(print_counter_load);

  // cast the counter variable so that it can be used as an
  // index
  Instruction *sext = dyn_cast<Instruction>(
      builder.CreateSExt(print_counter_load, IntegerType::get(ctx, 64)));
  sext->insertAfter(print_compare);

  // create the indicies for the GEP that accesses
  std::vector<Value *> indicies;
  ConstantInt *const_int32_11 =
      ConstantInt::get(mod_ptr->getContext(), APInt(32, StringRef("0"), 10));
  indicies.push_back(const_int32_11);
  indicies.push_back(sext);

  // create the gep to calculate the location of the value
  // being read from the array
  Instruction *print_gep =
      dyn_cast<Instruction>(builder.CreateGEP(array, indicies));
  print_gep->insertAfter(sext);

  // Load the value from the array
  LoadInst *load_array_idx = builder.CreateLoad(print_gep);
  load_array_idx->insertAfter(print_gep);

  // Print the array value
  std::vector<Value *> params;
  params.push_back(geti8StrVal(*mod_ptr, "\ntrace:%d\n", "formatString"));
  params.push_back(load_array_idx);
  CallInst *print_call = builder.CreateCall(printf_func, params);
  print_call->insertAfter(load_array_idx);

  // Create the final exit block by splitting
  BasicBlock *exit_block =
      print_call->getParent()->splitBasicBlock(print_call->getNextNode());

  // Create the final loop body block by splitting
  BasicBlock *loop_body = print_gep->getParent()->splitBasicBlock(print_gep);

  // Insert branching function of the loop (the loop's "jump")
  BranchInst *print_cmp_branch =
      builder.CreateCondBr(print_compare, loop_body, exit_block);
  ReplaceInstWithInst(cond_block->getTerminator(), print_cmp_branch);
  Instruction *print_ct_inc = dyn_cast<Instruction>(builder.CreateAdd(
      print_counter_load, ConstantInt::get(Type::getInt32Ty(ctx), 1)));
  print_ct_inc->insertAfter(print_call);
  builder.CreateStore(print_ct_inc, print_counter_alloca)
      ->insertAfter(print_ct_inc);

  ReplaceInstWithInst(print_ct_inc->getParent()->getTerminator(),
                      builder.CreateBr(cond_block));

  CallInst *print_array_end = builder.CreateCall(
      printf_func,
      geti8StrVal(*mod_ptr, ("\ntrace:array_end:" + array->getName().str() +
                             "\n").c_str(),
                  "formatString"));
  print_array_end->insertBefore(after_store);
}

// Recursive function for tracing an array's allocation to first
// find the array's allocated size and then insers
// code that print's the array's values in the executable
void handleArray(Instruction *inst, int arraySize, Value *array) {

  // If the array's size is statically assigned
  if (AllocaInst *ai = dyn_cast<AllocaInst>(inst)) {
    Value *val = cast<Value>(inst);
    int size;
    if (ArrayType *arr_ty = dyn_cast<ArrayType>(ai->getAllocatedType())) {
      size = arr_ty->getNumElements();
    } else {
      llvm::errs()
          << "handleArray Error: Handling allocate of non-array type!\n";
    }
    // If an instruction every uses the array check to
    // make sure it's size is not modified
    for (Value::user_iterator user = val->user_begin(), e = val->user_end();
         user != e; user++) {
      if (Instruction *user_inst = dyn_cast<Instruction>((*user))) {
        handleArray(user_inst, size, nullptr);
      }
    }
  }
  // If the instruction is accessing a individual element of
  // the array
  else if (GetElementPtrInst *gep = dyn_cast<GetElementPtrInst>(inst)) {
    Value *val = cast<Value>(inst);
    for (Value::user_iterator user = val->user_begin(), e = val->user_end();
         user != e; user++) {
      if (Instruction *user_inst = dyn_cast<Instruction>((*user))) {
        handleArray(user_inst, arraySize, gep->getOperand(0));
      }
    }
  }
  // If the use of the array involves a cast
  else if (BitCastInst *bit = dyn_cast<BitCastInst>(inst)) {
    Value *val = cast<Value>(inst);
    for (Value::user_iterator user = val->user_begin(), e = val->user_end();
         user != e; user++) {
      if (Instruction *user_inst = dyn_cast<Instruction>((*user))) {
        handleArray(user_inst, arraySize, bit->getOperand(0));
      }
    }
  }
  // If the array is used in a function call
  else if (CallInst *ci = dyn_cast<CallInst>(inst)) {
    std::string calledFuncName = ci->getCalledFunction()->getName().str();

    // if the function can make an update to the
    // array print the result
    if (calledFuncName == "llvm.memset.p0i8.i64") {
      buildArrayPrintingLoop(inst, arraySize, array);
    } else if (calledFuncName == "llvm.memcpy.p0i8.p0i8.i64") {
      buildArrayPrintingLoop(inst, arraySize, array);
    }

  }
  // If the array is written to, print it
  else if (StoreInst *si = dyn_cast<StoreInst>(inst)) {
    buildArrayPrintingLoop(inst, arraySize, array);
  }
}

void getFuncVarnames(Function *func,
                     std::map<std::string, std::string> *varnames) {

  // Iterate through each BB
  iplist<BasicBlock> &bb = func->getBasicBlockList();
  for (auto bb_it = bb.begin(); bb_it != bb.end(); bb_it++) {
    // Iterate through each inst
    iplist<Instruction> &inst = bb_it->getInstList();
    for (auto inst_it = inst.begin(); inst_it != inst.end(); inst_it++) {
      // Use dbg statements to get the llvm names of variables
      if (DbgDeclareInst *ddi = dyn_cast<DbgDeclareInst>(&(*inst_it))) {
        if (Value *v = dyn_cast<Value>(ddi->getOperand(0))) {
          // Get the corresponding LLVM variable name. This is quite ugly but I
          // cannot figure
          // out how to get the name of a user created variable if LLVM changes
          // it. For instance,
          // when variables in different scopes have different names LLVM
          // changes it but I can't
          // find the changed name in the debug info.
          std::string info;
          llvm::raw_string_ostream rso(info);
          v->print(rso);
          std::string holder = rso.str();
          holder = holder.substr(holder.find("%") + 1);
          if (holder.find("argv") == std::string::npos &&
              holder.find("argc") == std::string::npos) {
            (*varnames)[holder] = "";
          }
        }
      }
    }
  }
}

void getFuncAllocates(Function *func, std::vector<AllocaInst *> *allocates,
                      std::map<std::string, std::string> *varnames) {

  // Iterate through each BB
  iplist<BasicBlock> &bb = func->getBasicBlockList();
  for (iplist<BasicBlock>::iterator bb_it = bb.begin(); bb_it != bb.end();
       bb_it++) {
    // Iterate through each instruction looking for allocations
    iplist<Instruction> &inst = bb_it->getInstList();
    for (iplist<Instruction>::iterator inst_it = inst.begin();
         inst_it != inst.end(); inst_it++) {
      if (AllocaInst *ai = dyn_cast<AllocaInst>(&(*inst_it))) {
        // If the allocates uses a variable in
        // varname (user created variable)
        if (varnames->find(ai->getName()) != varnames->end()) {
          ai->setName(ai->getParent()->getParent()->getName().str() + "_" +
                      ai->getName().str());
          allocates->push_back(ai);
        }
      }
    }
  }
}

STATISTIC(HelloCounter, "Counts number of functions greeted");
namespace {
// Hello - The first implementation, without getAnalysisUsage.
struct Hello : public ModulePass {
  static char ID; // Pass identification, replacement for typeid
  Hello() : ModulePass(ID) {}

  bool runOnModule(Module &M) override {

    LLVMContext &ctx = M.getContext();
    IRBuilder<> builder(ctx);
    Function *printf_func = printf_prototype(ctx, &M);
    mod_ptr = &M;

    // Get all uses of programmer created variables
    iplist<Function> &fl = M.getFunctionList();
    for (iplist<Function>::iterator func_it = fl.begin(); func_it != fl.end();
         func_it++) {

      std::map<std::string, std::string> varnames;
      getFuncVarnames(*(&func_it), &varnames);
      std::vector<AllocaInst *> allocates;
      getFuncAllocates(*(&func_it), &allocates, &varnames);

      // For allocate use of programmer created variable
      for (int i = 0; i < allocates.size(); i++) {
        Value *val = cast<Value>(allocates[i]);
        // If allocating an  integer type
        if (IntegerType *int_type =
                dyn_cast<IntegerType>(allocates[i]->getAllocatedType())) {
          // Iterate through all uses of the int
          for (Value::user_iterator user = val->user_begin(),
                                    e = val->user_end();
               user != e; user++) {
            if (Instruction *inst = dyn_cast<Instruction>((*user))) {
              // If the instruction writes to the particular variable
              if (StoreInst *si = dyn_cast<StoreInst>(inst)) {
                // Print the name of the variable being written to and
                // it's new value in the trace
                std::string varName = allocates[i]->getName().str();
                LoadInst *printLoad =
                    builder.CreateLoad(si->getOperand(1), "loadForPrint");
                printLoad->insertAfter(si);
                std::vector<Value *> params;
                params.push_back(
                    geti8StrVal(M, ("\ntrace:" + allocates[i]->getName().str() +
                                    ":%d\n").c_str(),
                                "formatString"));
                params.push_back(printLoad);
                builder.CreateCall(printf_func, params)->insertAfter(printLoad);
              }
            }
          }
        }
        // If the programmer created variable is a static array
        else if (ArrayType *arr_type =
                     dyn_cast<ArrayType>(allocates[i]->getAllocatedType())) {
          handleArray(allocates[i], 0, nullptr);
        } else {
          llvm::errs() << "Error: Allocation of unknown type!\n";
        }
      }
    }

    return false;
  }
};
}

char Hello::ID = 0;
static RegisterPass<Hello> X("ValueTracerPass", "Hello World Pass");
