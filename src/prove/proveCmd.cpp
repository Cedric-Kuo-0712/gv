/****************************************************************************
  FileName     [ proveCmd.cpp ]
  PackageName  [ prove ]
  Synopsis     [ Define basic prove package commands ]
  Author       [ ]
  Copyright    [ Copyright(c) 2023-present DVLab, GIEE, NTU, Taiwan ]
 ****************************************************************************/

#include "proveCmd.h"

#include <cstring>
#include <iomanip>

#include "bddMgrV.h"
#include "cirGate.h"
#include "cirMgr.h"
#include "gvMsg.h"
#include "util.h"

using namespace std;

bool initProveCmd() {
    return (gvCmdMgr->regCmd("PINITialstate", 5, new PInitialStateCmd) &&
            gvCmdMgr->regCmd("PTRansrelation", 3, new PTransRelationCmd) &&
            gvCmdMgr->regCmd("PIMAGe", 5, new PImageCmd) &&
            gvCmdMgr->regCmd("PCHECKProperty", 7, new PCheckPropertyCmd));
}

extern BddNodeV getBddNodeV(const string& bddName);

//----------------------------------------------------------------------
//    PINITialstate [(string varName)]
//----------------------------------------------------------------------
GVCmdExecStatus
PInitialStateCmd::exec(const string& option) {
    vector<string> options;
    GVCmdExec::lexOptions(option, options);
    if (options.size() > 1) {
        return GVCmdExec::errorOption(GV_CMD_OPT_EXTRA, options[1]);
    }
    string token = "";
    if (options.size()) {
        if (!isValidVarName(options[0]))
            return GVCmdExec::errorOption(GV_CMD_OPT_ILLEGAL, options[0]);
        else token = options[0];
    }

    bddMgrV->buildPInitialState();
    if (!token.empty() &&
        !bddMgrV->addBddNodeV(token, bddMgrV->getPInitState()())) {
        gvMsg(GV_MSG_ERR)
            << "\"" << token
            << "\" has Already been Associated With Another BddNode!!" << endl;
        return GVCmdExec::errorOption(GV_CMD_OPT_ILLEGAL, token);
    }
    return GV_CMD_EXEC_DONE;
}

void PInitialStateCmd::usage(const bool& verbose) const {
    cout << "Usage: PINITialstate [(string varName)]" << endl;
}

void PInitialStateCmd::help() const {
    cout << setw(20) << left << "PINITialstate: "
         << "Set initial state BDD" << endl;
}

//----------------------------------------------------------------------
//    PTRansrelation [(string triName)] [(string trName)]
//----------------------------------------------------------------------
GVCmdExecStatus
PTransRelationCmd::exec(const string& option) {
    size_t op = 0;
    vector<string> options;
    GVCmdExec::lexOptions(option, options);
    if (options.size() > 2)
        return GVCmdExec::errorOption(GV_CMD_OPT_EXTRA, options[2]);

    string triName, trName;
    if (op < options.size()) {
        triName = options[op++];
        if (!isValidVarName(triName))
            return GVCmdExec::errorOption(GV_CMD_OPT_ILLEGAL, triName);
    }
    if (op < options.size()) {
        trName = options[op++];
        if (!isValidVarName(trName))
            return GVCmdExec::errorOption(GV_CMD_OPT_ILLEGAL, trName);
    }
    bddMgrV->buildPTransRelation();
    if (!triName.empty() &&
        !bddMgrV->addBddNodeV(triName, bddMgrV->getPTri()())) {
        gvMsg(GV_MSG_ERR)
            << "\"" << triName
            << "\" has Already been Associated With Another BddNode!!" << endl;
        return GVCmdExec::errorOption(GV_CMD_OPT_ILLEGAL, triName);
    }
    if (!trName.empty() && !bddMgrV->addBddNodeV(trName, bddMgrV->getPTr()())) {
        gvMsg(GV_MSG_ERR)
            << "\"" << trName
            << "\" has Already been Associated With Another BddNode!!" << endl;
        return GVCmdExec::errorOption(GV_CMD_OPT_ILLEGAL, trName);
    }
    return GV_CMD_EXEC_DONE;
}

void PTransRelationCmd::usage(const bool& verbose) const {
    cout
        << "Usage: PTRansrelation [(string triName)] [(stirng trName)]" << endl;
}

void PTransRelationCmd::help() const {
    cout << setw(20) << left << "PTRansrelation: "
         << "build the transition relationship in BDDs" << endl;
}

//----------------------------------------------------------------------
//    PIMAGe [-Next <(int numTimeframes)> | -UntilFixed <cap>] [(string varName)]
//    (-UntilFixed is an alias for -Next: run up to <cap> image steps but stop
//     early when reachability saturates; use a large cap to "run until fixed".)
//----------------------------------------------------------------------
GVCmdExecStatus
PImageCmd::exec(const string& option) {
    if (bddMgrV->getPInitState()() == 0) {
        gvMsg(GV_MSG_ERR) << "BDD of Initial State is Not Yet Constructed !!!"
                          << endl;
        return GV_CMD_EXEC_ERROR;
    } else if (bddMgrV->getPTr()() == 0) {
        gvMsg(GV_MSG_ERR)
            << "BDD of Transition Relation is Not Yet Constructed !!!" << endl;
        return GV_CMD_EXEC_ERROR;
    }

    int  level         = 1;
    bool levelExplicit = false;
    string name;
    vector<string> options;
    GVCmdExec::lexOptions(option, options);

    for (size_t i = 0, n = options.size(); i < n; ++i)
        if (!myStrNCmp("-Next", options[i], 2) ||
            !myStrNCmp("-UntilFixed", options[i], 7)) {
            if (++i < n) {
                if (!myStr2Int(options[i], level) || level <= 0)
                    return GVCmdExec::errorOption(GV_CMD_OPT_ILLEGAL,
                                                  options[i]);
                if (levelExplicit)
                    return GVCmdExec::errorOption(GV_CMD_OPT_EXTRA,
                                                  options[i - 1]);
                levelExplicit = true;
            } else
                return GVCmdExec::errorOption(GV_CMD_OPT_MISSING,
                                              options[i - 1]);
        } else if (name.empty()) {
            name = options[i];
            if (!isValidVarName(name))
                return GVCmdExec::errorOption(GV_CMD_OPT_ILLEGAL, name);
        } else return GVCmdExec::errorOption(GV_CMD_OPT_ILLEGAL, options[i]);
    bddMgrV->buildPImage(level);
    const unsigned steps = bddMgrV->getPImageStepCount();
    if (bddMgrV->isPFixed())
        gvMsg(GV_MSG_IFO)
            << "[Prove] Reachability fixed point after " << steps
            << " image step(s): no new states in the last step (complete reach "
               "set for this TR, within step cap)."
            << endl;
    else
        gvMsg(GV_MSG_IFO)
            << "[Prove] Fixed point not reached: ran " << steps << " image step(s)"
            << " (cap was " << level
            << "); increase -next / -untilFixed cap or run PIMAGe again to "
               "extend reach."
            << endl;
    if (!name.empty())
        bddMgrV->forceAddBddNodeV(name, bddMgrV->getPReachState()());
    return GV_CMD_EXEC_DONE;
}

void PImageCmd::usage(const bool& verbose) const {
    cout << "Usage: PIMAGe [-Next <(int numTimeframes)> | "
            "-UntilFixed <(int maxSteps)>] [(string varName)]"
         << endl;
}

void PImageCmd::help() const {
    cout << setw(20) << left << "PIMAGe: "
         << "build the next state images in BDDs (stops early at reachability "
            "fixed point; -untilFixed <cap> = same as -next <cap>, for clarity)"
         << endl;
}

//----------------------------------------------------------------------
//    PCHECKProperty < -Netid <netId> | -Output <outputIndex> > >
//----------------------------------------------------------------------
GVCmdExecStatus
PCheckPropertyCmd::exec(const string& option) {
    if (bddMgrV->getPReachState()() == 0) {
        gvMsg(GV_MSG_ERR) << "BDD of Reached State is Not Yet Constructed !!!"
                          << endl;
        return GV_CMD_EXEC_ERROR;
    }

    vector<string> options;
    GVCmdExec::lexOptions(option, options);

    if (options.size() < 2)
        return GVCmdExec::errorOption(GV_CMD_OPT_MISSING, "");
    if (options.size() > 2)
        return GVCmdExec::errorOption(GV_CMD_OPT_EXTRA, options[2]);

    bool isNet = false;

    if (!myStrNCmp("-Netid", options[0], 2)) isNet = true;
    else if (!myStrNCmp("-Output", options[0], 2)) isNet = false;
    else return GVCmdExec::errorOption(GV_CMD_OPT_ILLEGAL, options[0]);

    int num = 0;
    if (!myStr2Int(options[1], num) || (num < 0))
        return GVCmdExec::errorOption(GV_CMD_OPT_ILLEGAL, options[1]);
    if (isNet) {
        if ((unsigned)num >= cirMgr->getNumTots()) {
            gvMsg(GV_MSG_ERR) << "Net with Id " << num
                              << " does NOT Exist in Current Ntk !!" << endl;
            return GVCmdExec::errorOption(GV_CMD_OPT_ILLEGAL, options[1]);
        }
        // netId = GVNetId::makeNetId(num);
    } else {
        if ((unsigned)num >= cirMgr->getNumPOs()) {
            gvMsg(GV_MSG_ERR) << "Output with Index " << num
                              << " does NOT Exist in Current Ntk !!" << endl;
            return GVCmdExec::errorOption(GV_CMD_OPT_ILLEGAL, options[1]);
        }
        // netId = gvNtkMgr->getOutput(num);
    }

    BddNodeV monitor;
    string monitorName;
    if (isNet) {
        gv::cir::CirGate* g = cirMgr->getGate((unsigned)num);
        if (!g) {
            gvMsg(GV_MSG_ERR) << "Net with Id " << num
                              << " does NOT Exist in Current Ntk !!" << endl;
            return GVCmdExec::errorOption(GV_CMD_OPT_ILLEGAL, options[1]);
        }
        monitor     = bddMgrV->getBddNodeV(g->getGid());
        monitorName = "net_" + to_string(num);
    } else {
        monitor     = bddMgrV->getBddNodeV(cirMgr->getPo(num)->getGid());
        monitorName = cirMgr->getPo(num)->getName();
    }
    assert(monitor());
    bddMgrV->runPCheckProperty(monitorName, monitor);

    return GV_CMD_EXEC_DONE;
}

void PCheckPropertyCmd::usage(const bool& verbose) const {
    cout << "Usage: PCHECKProperty < -Netid <netId> | -Output <outputIndex> >"
         << endl;
}

void PCheckPropertyCmd::help() const {
    cout << setw(20) << left << "PCHECKProperty:"
         << "check the monitor by BDDs" << endl;
}
