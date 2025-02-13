#include "ICFG.h"
#include "klee/Support/CompilerWarning.h"
#include <llvm-13/llvm/IR/Instructions.h> // Required for dyn_cast, cast, ReturnInst, InvokeInst
#include <llvm-13/llvm/IR/CFG.h> // Required for successors
#include <llvm-13/llvm/IR/Module.h>
#include <llvm-13/llvm/Support/raw_ostream.h> // Required for raw_ostream &os
#include <llvm-13/llvm/Support/FormatVariadic.h> // Required for llvm::formatv

#include <cassert>

using namespace klee;
using namespace llvm;

ICFGNode::ICFGNode(llvm::Function* enclosingFunction, llvm::BasicBlock* bb)
    : enclosingFunction{enclosingFunction}, bb{bb} {}

ICFGNode::ICFGNode(llvm::Function* enclosingFunction)
    : enclosingFunction{enclosingFunction}, bb{nullptr} {} // Constructor for external function nodes


llvm::Instruction* ICFGNode::getTerminator() const {
    if (bb) {
        return bb->getTerminator();
    }
    return nullptr; // For external function nodes which don't have a BB
}

ICFG::ICFG(llvm::Module& module, std::unordered_map<llvm::BasicBlock *, int> &bbToIndex) {
    int index = 0;
    // first just build the ICFG nodes for all blocks, split on known calls
    for (auto& func : module) {
        for (auto& bb : func) {
            auto& blockNodes = blockToICFGNodes[&bb];
            blockNodes.emplace_back(std::make_unique<ICFGNode>(&func, &bb));

            bbToIndex[&bb] = index++;

            auto currentNode = [&] () -> Node* {
                return blockNodes.back().get();
            };

            for (auto& inst : bb) {
                currentNode()->insts.push_back(&inst);
                if (auto call = llvm::dyn_cast<llvm::CallBase>(&inst)) {
                    auto callee = call->getCalledFunction();
                    if (callee) { // this is a direct call
                        assert(!interproceduralCallEdges.count(call)); // we should only visit each call once
                        interproceduralCallEdges[call] = callee;
                        blockNodes.emplace_back(std::make_unique<Node>(&func, &bb));
                    }
                }
            }

            if (currentNode()->insts.empty())
                blockNodes.pop_back();
            assert(!blockNodes.empty());
        }
    }

    // then link them all based on intraprocedural & interprocedural edges
    // initialize the edges
    for (auto& [bb, icfgnodes] : blockToICFGNodes) {
        for (auto& icfgNode : icfgnodes) {
            llvm::Instruction* terminator = icfgNode->getTerminator();
            if (llvm::CallBase *callBaseTerminator = llvm::dyn_cast<llvm::CallBase>(terminator)) {
                // terminator is a llvm::CallBase*, now it's safe to use it as a key for interproceduralCallEdges
                auto edgeIt = interproceduralCallEdges.find(callBaseTerminator);
                if (edgeIt != interproceduralCallEdges.end()) {
                    // this edge is interprocedural

                    // figure out the return site in the caller
                    auto callerReturnSiteICFGNode = [&] () -> ICFGNode* {
                        ///FIXME: we do not model the exceptional flow here.
                        auto callerReturnSite = [&] (llvm::CallBase* call) -> llvm::Instruction* {
                            if (auto invoke = llvm::dyn_cast<llvm::InvokeInst>(call))
                                return &invoke->getNormalDest()->front();
                            auto next = call->getNextNode();
                            assert(next && "if it isnt an invoke, it cant be a terminator!");
                            return next;
                        } (llvm::cast<llvm::CallBase>(callBaseTerminator));
                        assert(callerReturnSite);
                        // for invokes, the return BB may not be the same as the caller BB
                        return getICFGNodeStartingWith(callerReturnSite);
                    } ();

                    auto callee = edgeIt->second;
                    assert(callee);
                    ///TODO: it's annoying that the ICFG will contain infeasible flow from one callsite to all the others, through the callee
                    // i wish there was a way to avoid this, without context cloning the function (which has its own set of problems)
                    // link this icfgnode to the entry icfgnode of the callee
                    if (callee->isDeclaration()) {
                        auto calleeICFGNode = externalFuncICFGNodes.emplace_back(std::make_unique<ICFGNode>(callee, nullptr)).get();
                        icfgEdges[icfgNode.get()].insert(calleeICFGNode);
                        icfgEdges[calleeICFGNode].insert(callerReturnSiteICFGNode);
                    } else {
                        auto entryBlock = &callee->getEntryBlock();
                        auto entryICFGNode = blockToICFGNodes.find(entryBlock)->second.front().get();
                        assert(entryICFGNode->insts.front() == &entryBlock->front());
                        icfgEdges[icfgNode.get()].insert(entryICFGNode);

                        // link all normal return paths in the callee back to the normal return site in the caller
                        ///FIXME: we ignore exceptional flow here
                        for (auto& calleeBB : *callee) {
                            if (auto ret = llvm::dyn_cast<llvm::ReturnInst>(calleeBB.getTerminator())) {
                                auto retICFGNode = blockToICFGNodes.find(&calleeBB)->second.back().get();
                                assert(retICFGNode->insts.back() == ret);
                                icfgEdges[retICFGNode].insert(callerReturnSiteICFGNode);
                            }
                        }
                    }
                }
            } else {
                // all this node's successors are intraprocedural
                assert(icfgNode->getTerminator() == bb->getTerminator() && "this edge should always be intraprocedural!");
                // this is inter-block flow
                for (auto successor : llvm::successors(bb)) {
                    auto succICFGNode = blockToICFGNodes.find(successor)->second.front().get();
                    assert(succICFGNode->insts.front() == &successor->front());
                    icfgEdges[icfgNode.get()].insert(succICFGNode);
                }
            }
        }
    }
}

ICFG::~ICFG(){
    igraph_destroy(&i_cfg);
}


ICFGNode* ICFG::getICFGNodeStartingWith(llvm::Instruction* startingInst) const {
    auto& retblockICFGNodes = blockToICFGNodes.find(startingInst->getParent())->second;
    for (auto& node : retblockICFGNodes) {
        for (auto inst : node->insts) {
            if (inst == startingInst)
                return node.get();
        }
    }
    assert(!"Can't find ICFG node starting with `inst`!");
};

void ICFG::dumpToDOTFile(llvm::StringRef filename) const {
    std::error_code code;
    llvm::raw_fd_ostream outputFile(filename, code);
    assert(code.value() == 0);

    outputFile << "digraph \"ICFG\" {\n";

    // we want to draw boundary boxes around functions in the ICFG
    // first figure out which functions exist
    llvm::DenseSet<llvm::Function*> funcs;
    for (auto& [bb, icfgnodes] : blockToICFGNodes) {
        funcs.insert(bb->getParent());
    }

    // first dump all the intra-function nodes
    // i'm using the unique in-memory node address as the label here
    // dump them all as part of a subgraph per-function
    size_t numNodes = 0;
    for (auto func : funcs) {
        outputFile << llvm::formatv("\tsubgraph cluster_{0} {\n", func->getName());
        outputFile << llvm::formatv("\t\tlabel = \"{0}\";\n", func->getName());
        for (auto& bb : *func) {
            auto& icfgNodes = blockToICFGNodes.find(&bb)->second;
            for (auto& icfgnode : icfgNodes) {
                auto line = llvm::formatv("\t\tnode{0} [shape=record,style=\"filled\",color=\"black\",penwidth=1,fillcolor=\"grey\",label=\"#block{0}\"];", (void*) icfgnode.get()).str();
                outputFile << line << "\n";
                numNodes++;
            }
        }
        outputFile << "\tcolor=blue;\n";
        outputFile << "\t}\n";
    }

    // then dump the dummy nodes for the library calls
    for (auto& dummyLibFuncNode : externalFuncICFGNodes) {
        auto line = llvm::formatv("\tnode{0} [shape=record,style=\"filled\",color=\"black\",penwidth=1,fillcolor=\"darkgrey\",label=\"{1}\"];", (void*) dummyLibFuncNode.get(), dummyLibFuncNode->enclosingFunction->getName()).str();
        outputFile << line << "\n";
        numNodes++;
    }

    // then dump all the edges
    size_t numEdges = 0;
    for (auto& [src, dests] : icfgEdges) {
        for (auto dest : dests) {
            auto line = llvm::formatv("\tnode{0} -> node{1} [penwidth=1];", (void*)src, (void*)dest).str();
            outputFile << line << "\n";
            numEdges++;
        }
    }

    outputFile << "}\n";
    outputFile.flush();
    outputFile.close();

    llvm::errs() << llvm::formatv("Dumped DOT graph with {0} nodes and {1} edges to {2}\n", numNodes, numEdges, filename);
}


void ICFG::generateIGraph(igraph_t& i_graph) {
    // Map to store ICFGNode to vertex index mapping
    std::unordered_map<ICFGNode*, int> nodeToIndex;
    int index = 0;

    // Count the total number of nodes
    int totalNodes = 0;
    for (const auto& entry : blockToICFGNodes) {
        totalNodes += entry.second.size();
    }
    // Initialize the igraph with the correct number of vertices
    igraph_empty(&i_graph, totalNodes, IGRAPH_DIRECTED);
    // Assign each ICFGNode a unique vertex index
    for (const auto& entry : blockToICFGNodes) {
        for (const auto& icfgNode : entry.second) {
            nodeToIndex[icfgNode.get()] = index++;
        }
    }

    // Add edges to the igraph
    for (const auto& [fromNode, successors] : icfgEdges) {
        int fromIndex = nodeToIndex[fromNode];
        for (ICFGNode* toNode : successors) {
            int toIndex = nodeToIndex[toNode];
            igraph_add_edge(&i_graph, fromIndex, toIndex);
        }
    }
}