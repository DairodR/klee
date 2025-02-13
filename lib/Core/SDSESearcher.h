#ifndef SDSESEARCHER_H
#define SDSESEARCHER_H

#include "Searcher.h"
#include "ICFG.h" // Include ICFG header as SDSESearcher uses ICFG
#include "ExecutionTree.h" // Include ExecutionTree header as SDSESearcher uses InMemoryExecutionTree
#include "Executor.h" // Include Executor header as SDSESearcher uses Executor

#include <string>
#include <unordered_map>
#include <limits>

namespace llvm {
    class raw_ostream;
    class BasicBlock;
    class Module;
}

namespace klee {
    class KModule;
    class ExecutionState;
    class InMemoryExecutionTree;
    class Executor;

class SDSESearcher : public Searcher {
private:
    InMemoryExecutionTree *executionTree;
    uint8_t idBitMask;
    std::vector<ExecutionState*> states;

    int target;
    std::string targetFile;
    std::unordered_map<llvm::BasicBlock*, int> bbToIndex;
    ICFG icfg;
    igraph_t i_cfg;
    class Executor &executor; // Executor is a member
    KModule &kmodule;
    bool foundTarget = false;

    int computeShortestPath(unsigned int t, llvm::BasicBlock *currnode, std::unordered_map<llvm::BasicBlock*, int> bbToIndex);
    void generateCFG();


public:
    SDSESearcher(KModule &kmodule, InMemoryExecutionTree *executionTree, int target, std::string targetFile, Executor &executor);
    ~SDSESearcher() override {}; // Ensure proper destruction if needed

    ExecutionState &selectState() override;
    void update(ExecutionState *current,
                const std::vector<ExecutionState *> &addedStates,
                const std::vector<ExecutionState *> &removedStates) override;
    bool empty() override;
    void printName(llvm::raw_ostream &os) override;

    unsigned int getTarget() const { return target; }
};

} // namespace klee

#endif // SDSESEARCHER_H