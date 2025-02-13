#include "SDSESearcher.h"
#include "klee/Module/KModule.h" // Include KModule header
#include "klee/Support/CompilerWarning.h"
#include <llvm-13/llvm/Support/raw_ostream.h> // Required for raw_ostream &os
#include <llvm-13/llvm/IR/DebugInfoMetadata.h> // Required for DILocation
#include <llvm-13/llvm/IR/Instructions.h> // Required for Instructions
#include <limits> // Required for std::numeric_limits

#include <igraph/igraph.h> // Required for igraph functions
#include <igraph/igraph_paths.h> // Required for shortest path functions
#include <cassert> // Required for assert

using namespace klee;
using namespace llvm;


SDSESearcher::SDSESearcher(KModule &kmodule, InMemoryExecutionTree *executionTree, int target, std::string targetFile, Executor &executor)
    :  target{target}, targetFile{targetFile}, executionTree{executionTree}, idBitMask{static_cast<uint8_t>(executionTree ? executionTree->getNextId() : 0)},
        bbToIndex(), icfg(*kmodule.module.get(), bbToIndex), executor(executor), kmodule{kmodule}
      {
  assert(executionTree);
  // std::cout << "SDSESearcher created" << std::endl;
  llvm::Module *module = kmodule.module.get();


  icfg.generateIGraph(i_cfg);


  bool debug =false;
  if(debug){
    generateCFG();
  }
}

#define IS_OUR_NODE_VALID(n)                                                   \
  (((n).getPointer() != nullptr) && (((n).getInt() & idBitMask) != 0))


//change to leave out the mycfg stuff to work with icfg instead
//should return an int with the length of the shortest path
//this can than be used to select the state with the shortest path left to the target
int SDSESearcher::computeShortestPath(unsigned int t, llvm::BasicBlock *currnode, std::unordered_map<llvm::BasicBlock*, int> bbToIndex) {
        std::unordered_map<ExecutionTreeNode*, int> distances;
        std::unordered_map<ExecutionTreeNode*, ExecutionTreeNode*> predecessors;


        llvm::raw_ostream &os = llvm::errs();

        llvm::BasicBlock *target = nullptr;


        //where do i need to go
        for (const auto &nodePair: icfg.blockToICFGNodes){
          llvm::BasicBlock *BB = nodePair.first;

          for (auto &inst: *BB){
            if(llvm::DILocation *loc = inst.getDebugLoc()){
              auto line = loc->getLine();
              // os <<"Instruction: "<<inst << "\n";
              // os <<"Source: "<<loc->getFilename().str() << " Line: " << line << "\n";
              if(loc->getFilename().str() == targetFile && line == t){
                // os << "Target line found" << "\n";
                target = BB;
                break;
              }
            }
          }
          if (target!=nullptr) break;
        }

        if (!target){
          // os << "Target not found" << "\n";
          return -1;
        }


        igraph_integer_t from = bbToIndex[currnode];
        igraph_integer_t to = bbToIndex[target];



        assert(target && "Target not found");
        // as i have access to the igraph version of the CFG, i can use the igraph library to compute the shortest path
        // required parameters: next node(s), target node, cfg

        igraph_vector_t shortestpath;
        igraph_vector_init(&shortestpath, 0);

        igraph_get_shortest_path_dijkstra(&i_cfg,&shortestpath, NULL, from, to, NULL,  IGRAPH_OUT);


        if(from == to){
          os<<"path completed"<<"\n";
          foundTarget=true;
        }

        if (igraph_vector_size(&shortestpath) > 0) {
          return igraph_vector_size(&shortestpath);
        } else {
          return -1;
        }
    }

void SDSESearcher::printName(llvm::raw_ostream &os) {
  os << "SDSESearcher\n";
}

bool SDSESearcher::empty() {
  return !IS_OUR_NODE_VALID(executionTree->root);
}


void SDSESearcher::update(ExecutionState *current,
                                const std::vector<ExecutionState *> &addedStates,
                                const std::vector<ExecutionState *> &removedStates) {


  if(foundTarget){
    executor.prepareForEarlyExit();
    executor.setHaltExecution(true);
    igraph_destroy(&i_cfg);
    return;
  }

  states.insert(states.end(), addedStates.begin(), addedStates.end());



  //remove states
  for (const auto state : removedStates) {
    auto it = std::find(states.begin(), states.end(), state);
    assert(it != states.end() && "invalid state removed");
    states.erase(it);
  }

}


void SDSESearcher::generateCFG() {

  FILE *f = fopen("igraph_cfg.dot", "w");
  if (f == NULL) {
      llvm::errs() << "Error: Could not open file " << "igraph_cfg.dot" << " for writing.\n";
      return;
    }


    igraph_write_graph_dot(&i_cfg, f);
    fclose(f);

}


ExecutionState &SDSESearcher::selectState() {


  llvm::raw_ostream &os = llvm::outs();


  ICFGNode *currentNode = nullptr;

  bool nodeFound = false;


  for (auto es : states) {
    auto pc = es->prevPC;
    auto source = pc->info->file;

    if (icfg.blockToICFGNodes.count(pc->inst->getParent())) {

        auto& icfgNodes =icfg.blockToICFGNodes[pc->inst->getParent()];
        if(!icfgNodes.empty()){
          currentNode = icfgNodes.front().get();
          nodeFound=true;
        }
    }
  }

  int shortestPath = std::numeric_limits<int>::max();
  ExecutionState *nextState_test = nullptr;
  if(nodeFound){
    for (auto es:states){
      auto pc = es->pc;
      int temp = computeShortestPath(this->getTarget(), pc->inst->getParent(), bbToIndex);
      if (temp == -1){
        return *states.back();
      }
      if (temp < shortestPath){
        shortestPath = temp;
        nextState_test = es;
      }
    }
    return *nextState_test;
  }


  return *states.back();
}