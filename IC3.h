/*********************************************************************
 Copyright (c) 2013, Aaron Bradley, 2018 - 2022 Tobias Seufert

 Permission is hereby granted, free of charge, to any person obtaining
 a copy of this software and associated documentation files (the
 "Software"), to deal in the Software without restriction, including
 without limitation the rights to use, copy, modify, merge, publish,
 distribute, sublicense, and/or sell copies of the Software, and to
 permit persons to whom the Software is furnished to do so, subject to
 the following conditions:

 The above copyright notice and this permission notice shall be
 included in all copies or substantial portions of the Software.

 THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
 OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *********************************************************************/

#ifndef IC3_h_INCLUDED
#define IC3_h_INCLUDED

#include "Model.h"

namespace IC3
{
// The State structures are for tracking trees of (lifted) CTIs.
// Because States are created frequently, I want to avoid dynamic
// memory management; instead their (de)allocation is handled via
// a vector-based pool.
struct State
{
	size_t successor;  // successor State
	LitVec latches;
	LitVec inputs;
	size_t index;      // for pool
	bool used;         // for pool
};


// A proof obligation.
struct Obligation
{
	Obligation(size_t st, size_t l, size_t d) :
			state(st), level(l), depth(d)
	{
	}
	size_t state;  // Generalize this state...
	size_t level;  // ... relative to this level.
	size_t depth;  // Length of CTI suffix to error.
};

#if defined(FBPDR_USE_PO_INTERSECTION) || defined(FBPDR_USE_PO_INTERSECTION_SEMANTIC)

// A CubeSet is a set of ordered (by integer value) vectors of
// Minisat::Lits.
static bool _LitVecComp(const LitVec &v1, const LitVec &v2)
{
	if (v1.size() < v2.size())
		return true;
	if (v1.size() > v2.size())
		return false;
	for (size_t i = 0; i < v1.size(); ++i)
	{
		if (v1[i] < v2[i])
			return true;
		if (v2[i] < v1[i])
			return false;
	}
	if(v1.bad < v2.bad)
	{
		return true;
	}

	return false;
}
#else
// A CubeSet is a set of ordered (by integer value) vectors of
// Minisat::Lits.
static bool _LitVecComp(const LitVec &v1, const LitVec &v2)
{
	if (v1.size() < v2.size())
		return true;
	if (v1.size() > v2.size())
		return false;
	for (size_t i = 0; i < v1.size(); ++i)
	{
		if (v1[i] < v2[i])
			return true;
		if (v2[i] < v1[i])
			return false;
	}
	return false;
}
static bool _LitVecEq(const LitVec &v1, const LitVec &v2)
{
	if (v1.size() != v2.size())
		return false;
	for (size_t i = 0; i < v1.size(); ++i)
		if (v1[i] != v2[i])
			return false;
	return true;
}
#endif

class LitVecComp
{
public:
	bool operator()(const LitVec &v1, const LitVec &v2) const
	{
		return _LitVecComp(v1, v2);
	}
};
typedef set<LitVec, LitVecComp> CubeSet;
// For IC3's overall frame structure.
struct Frame
{
	size_t k;             // steps from initial state
	CubeSet borderCubes;  // additional cubes in this and previous frames
	Minisat::Lit actLit;  // frame activation literal, assume actLit -> activate
						  // frame clauses contain ~actLit -> deactivate
};

#define ORIG_PDR_HANDLE 0
#define REV_PDR_HANDLE 1
#define NO_KILL 0
#define KILL_CURRENT_THREAD 1

struct ThreadHandle
{
	ThreadHandle() : awake(ORIG_PDR_HANDLE), kill(NO_KILL)
	{
	}

	uint8_t awake;
	uint8_t kill;

};
/*
static void check(Model &model, vector<State> &states, vector<State> &statesOther,
		vector<Frame> &frames, vector<Frame> &framesOther,
		deeperPoFirst &pos, deeperPoFirst &posOther, int verbose = 0, // 0: silent, 1: stats, 2: informative
		bool basic = false,    // simple inductive generalization
		bool random = false,   // random runs for statistical profiling
		bool revpdr = false);  // reverse of standard pdr*/

}

#endif
