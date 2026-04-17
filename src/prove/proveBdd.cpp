/****************************************************************************
  FileName     [ proveBdd.cpp ]
  PackageName  [ prove ]
  Synopsis     [ For BDD-based verification ]
  Author       [ ]
  Copyright    [ Copyright(c) 2023-present DVLab, GIEE, NTU, Taiwan ]
****************************************************************************/

#include "bddMgrV.h"
#include "gvMsg.h"
// #include "gvNtk.h"
#include <algorithm>
#include <cstdlib>
#include <cstring>
#include <iomanip>
#include <iostream>
#include <numeric>
#include <vector>

#include "cirGate.h"
#include "cirMgr.h"
#include "util.h"

namespace {
bool envOn(const char* key, bool defaultVal = false) {
    const char* v = getenv(key);
    if (!v) return defaultVal;
    if (!strcmp(v, "1") || !strcmp(v, "true") || !strcmp(v, "TRUE") ||
        !strcmp(v, "on") || !strcmp(v, "ON"))
        return true;
    if (!strcmp(v, "0") || !strcmp(v, "false") || !strcmp(v, "FALSE") ||
        !strcmp(v, "off") || !strcmp(v, "OFF"))
        return false;
    return defaultVal;
}

// GV_TR_PART_ORDER: file | reverse | smallest | largest (default: smallest when
// early quant is on, else file).
const char* trPartOrderFromEnv(bool earlyQuant) {
    const char* v = getenv("GV_TR_PART_ORDER");
    if (v && v[0]) return v;
    return earlyQuant ? "smallest" : "file";
}
}  // namespace

void BddMgrV::buildPInitialState() {
    _initState = BddNodeV::_one;
    for (unsigned i = 0, n = cirMgr->getNumLATCHs(); i < n; ++i) {
        // Initial state: all current-state latches are 0.
        _initState &= ~getBddNodeV(cirMgr->getRo(i)->getGid());
    }
    _reachStates.clear();
    _reachStates.push_back(_initState);
    _isFixed = false;
}

void BddMgrV::buildPTransRelation() {
    _useConjTrPartition = envOn("GV_TR_CONJ_PARTITION", true);
    _useTrEarlyQuant    = envOn("GV_TR_EARLY_QUANT", true);
    _trParts.clear();
    _trPartPerm.clear();
    _trPartPiDeps.clear();
    _trPartCsDeps.clear();
    _tri = BddNodeV::_one;
    for (unsigned i = 0, n = cirMgr->getNumLATCHs(); i < n; ++i) {
        const BddNodeV nsVar  = getBddNodeV(cirMgr->getRi(i)->getName());
        const BddNodeV nsFunc = getBddNodeV(cirMgr->getRi(i)->getGid());
        const BddNodeV eq     = (nsVar & nsFunc) | ((~nsVar) & (~nsFunc));
        if (_useConjTrPartition) _trParts.push_back(eq);
        _tri &= eq;
    }

    // In partition mode, defer PI-quantification to image construction to avoid
    // building a fully PI-quantified monolithic TR upfront.
    if (_useConjTrPartition) {
        _tr = _tri;
        const unsigned nPart = (unsigned)_trParts.size();
        if (_useTrEarlyQuant && nPart > 0) {
            const unsigned nPI  = cirMgr->getNumPIs();
            const unsigned nCS = cirMgr->getNumLATCHs();
            const unsigned csBase = nPI + 1;
            _trPartPiDeps.resize(nPart);
            _trPartCsDeps.resize(nPart);
            for (unsigned bi = 0; bi < nPart; ++bi) {
                for (unsigned p = 0; p < nPI; ++p) {
                    if (_trParts[bi].dependsOnLevel(p + 1))
                        _trPartPiDeps[bi].push_back(p);
                }
                for (unsigned c = 0; c < nCS; ++c) {
                    if (_trParts[bi].dependsOnLevel(csBase + c))
                        _trPartCsDeps[bi].push_back(c);
                }
            }
            _trPartPerm.resize(nPart);
            iota(_trPartPerm.begin(), _trPartPerm.end(), 0u);
            const char* ord = trPartOrderFromEnv(true);
            if (!strcmp(ord, "reverse")) {
                reverse(_trPartPerm.begin(), _trPartPerm.end());
            } else if (!strcmp(ord, "smallest")) {
                sort(_trPartPerm.begin(), _trPartPerm.end(),
                     [&](unsigned a, unsigned b) {
                         const unsigned sa =
                             (unsigned)_trPartPiDeps[a].size() +
                             (unsigned)_trPartCsDeps[a].size();
                         const unsigned sb =
                             (unsigned)_trPartPiDeps[b].size() +
                             (unsigned)_trPartCsDeps[b].size();
                         if (sa != sb) return sa < sb;
                         return _trParts[a].getLevel() < _trParts[b].getLevel();
                     });
            } else if (!strcmp(ord, "largest")) {
                sort(_trPartPerm.begin(), _trPartPerm.end(),
                     [&](unsigned a, unsigned b) {
                         const unsigned sa =
                             (unsigned)_trPartPiDeps[a].size() +
                             (unsigned)_trPartCsDeps[a].size();
                         const unsigned sb =
                             (unsigned)_trPartPiDeps[b].size() +
                             (unsigned)_trPartCsDeps[b].size();
                         if (sa != sb) return sa > sb;
                         return _trParts[a].getLevel() > _trParts[b].getLevel();
                     });
            }
            // "file" and unknown tokens: keep identity 0..n-1
            gvMsg(GV_MSG_IFO) << "[Prove] PTRansrelation uses conjunctive partition with "
                              << nPart << " block(s), order=\"" << ord
                              << "\", earlyQuant=on." << endl;
        } else {
            gvMsg(GV_MSG_IFO) << "[Prove] PTRansrelation uses conjunctive partition with "
                              << _trParts.size() << " block(s), earlyQuant=off." << endl;
        }
    } else {
        // Legacy monolithic PI-quantified TR.
        _tr = _tri;
        for (unsigned i = 0, n = cirMgr->getNumPIs(); i < n; ++i) {
            _tr = _tr.exist(i + 1);
        }
    }
}

BddNodeV BddMgrV::restrict(const BddNodeV& f, const BddNodeV& g) {
    if (g == BddNodeV::_zero) {
        cout << "Error in restrict!!" << endl;
    }
    if (g == BddNodeV::_one) {
        return f;
    }
    if (f == BddNodeV::_zero || f == BddNodeV::_one) {
        return f;
    }
    unsigned a = g.getLevel();
    if (g.getLeftCofactor(a) == BddNodeV::_zero) {
        return restrict(f.getRightCofactor(a), g.getRightCofactor(a));
    }
    if (g.getRightCofactor(a) == BddNodeV::_zero) {
        return restrict(f.getLeftCofactor(a), g.getLeftCofactor(a));
    }
    if (f.getLeftCofactor(a) == f.getRightCofactor(a)) {
        return restrict(f, g.getLeftCofactor(a) | g.getRightCofactor(a));
    }
    BddNodeV newNode =
        (~getSupport(a)& restrict(f.getRightCofactor(a),
                                  g.getRightCofactor(a))) |
        (getSupport(a)& restrict(f.getLeftCofactor(a), g.getLeftCofactor(a)));
    return newNode;
}

void BddMgrV::buildPImage(int level) {
    if (_reachStates.empty()) _reachStates.push_back(_initState);
    _isFixed        = false;
    _pimageStepsRun = 0;

    const bool enableFrontierSimp = envOn("GV_FRONTIER_SIMPLIFY", true);
    const bool useRestrictSimp     = envOn("GV_FRONTIER_USE_RESTRICT", false);

    for (int t = 0; t < level; ++t) {
        const BddNodeV prevReach = _reachStates.back();
        BddNodeV frontier         = prevReach;

        // Frontier = newly discovered states from the last iteration.
        if (_reachStates.size() > 1) frontier &= ~_reachStates[_reachStates.size() - 2];

        // Optional restrict-based frontier compaction. Do NOT intersect frontier
        // with ~prevReach: frontier is always ⊆ prevReach, so that would empty it
        // and falsely finish in one image step when GV_FRONTIER_SIMPLIFY is on.
        if (enableFrontierSimp && useRestrictSimp && frontier != BddNodeV::_zero) {
            frontier = restrict(frontier, prevReach | frontier);
        }

        const BddNodeV ns      = find_ns(frontier);
        const BddNodeV nextCS  = ns_to_cs(ns);
        const BddNodeV newReach = prevReach | nextCS;

        ++_pimageStepsRun;
        if (newReach == prevReach) {
            _isFixed = true;
            return;
        }
        _reachStates.push_back(newReach);
    }
}

void BddMgrV::runPCheckProperty(const string& name, BddNodeV monitor) {
    // Check AG(~monitor) by testing if any reachable state violates it.
    const BddNodeV bad = getPReachState() & monitor;
    if (bad == BddNodeV::_zero) {
        gvMsg(GV_MSG_IFO) << "Property AG(~" << name << ") holds." << endl;
    } else {
        gvMsg(GV_MSG_IFO) << "Property AG(~" << name << ") is violated." << endl;
        gvMsg(GV_MSG_IFO) << "Counterexample cubes: " << bad.countCube() << endl;
    }
}

BddNodeV
BddMgrV::find_ns(BddNodeV cs) {
    BddNodeV ns = cs;
    if (_useConjTrPartition && !_trParts.empty()) {
        if (_useTrEarlyQuant && _trPartPerm.size() == _trParts.size() &&
            _trPartPiDeps.size() == _trParts.size() &&
            _trPartCsDeps.size() == _trParts.size()) {
            const unsigned nPI  = cirMgr->getNumPIs();
            const unsigned nCS  = cirMgr->getNumLATCHs();
            const unsigned csBase = nPI + 1;
            vector<unsigned> remPi(nPI, 0), remCs(nCS, 0);
            for (unsigned bi = 0; bi < (unsigned)_trPartPiDeps.size(); ++bi) {
                for (unsigned p : _trPartPiDeps[bi]) ++remPi[p];
                for (unsigned c : _trPartCsDeps[bi]) ++remCs[c];
            }
            vector<char> piDone(nPI, 0), csDone(nCS, 0);
            for (unsigned step = 0; step < (unsigned)_trPartPerm.size(); ++step) {
                const unsigned bi = _trPartPerm[step];
                ns &= _trParts[bi];
                for (unsigned p : _trPartPiDeps[bi]) {
                    if (piDone[p]) continue;
                    if (--remPi[p] == 0u) {
                        ns      = ns.exist(p + 1);
                        piDone[p] = 1;
                    }
                }
                for (unsigned c : _trPartCsDeps[bi]) {
                    if (csDone[c]) continue;
                    if (--remCs[c] == 0u) {
                        ns        = ns.exist(csBase + c);
                        csDone[c] = 1;
                    }
                }
            }
            for (unsigned p = 0; p < nPI; ++p) {
                if (!piDone[p]) ns = ns.exist(p + 1);
            }
            for (unsigned c = 0; c < nCS; ++c) {
                if (!csDone[c]) ns = ns.exist(csBase + c);
            }
        } else {
            for (size_t i = 0; i < _trParts.size(); ++i) {
                ns &= _trParts[i];
            }
            for (unsigned i = 0, n = cirMgr->getNumPIs(); i < n; ++i) {
                ns = ns.exist(i + 1);
            }
        }
    } else {
        ns &= _tr;
    }
    const unsigned csBase = cirMgr->getNumPIs() + 1;
    for (unsigned i = 0, n = cirMgr->getNumLATCHs(); i < n; ++i) {
        ns = ns.exist(csBase + i);
    }
    return ns;
}

BddNodeV
BddMgrV::ns_to_cs(BddNodeV ns) {
    BddNodeV cs = ns;
    const unsigned piNum    = cirMgr->getNumPIs();
    const unsigned ffNum    = cirMgr->getNumLATCHs();
    const unsigned nsBaseLv = piNum + ffNum + 1;
    for (unsigned i = 0; i < ffNum; ++i) {
        const unsigned nsLevel = nsBaseLv + i;
        const BddNodeV csVar   = getBddNodeV(cirMgr->getRo(i)->getGid());
        const BddNodeV when1   = cs.getLeftCofactor(nsLevel);
        const BddNodeV when0   = cs.getRightCofactor(nsLevel);
        cs                     = (csVar & when1) | ((~csVar) & when0);
    }
    return cs;
}
