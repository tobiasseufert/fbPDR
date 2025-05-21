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

#include <algorithm>
#include <iostream>
#include <fstream>
#include <set>
#include <sys/times.h>
#include <map>

#include "IC3.h"
#include "Solver.h"
#include "Vec.h"


namespace IC3
{

class IC3
{
public:
	IC3(Model &_model,
#ifdef FBPDR
			vector<State> *_states, vector<State> *_statesOther,
			vector<Frame> *_frames, vector<Frame> *_framesOther,
#if defined(FBPDR_USE_PO_INTERSECTION) || defined(FBPDR_USE_PO_INTERSECTION_SEMANTIC)
			DeeperPoFirst *_pos, DeeperPoFirst *_posOther,
#endif
			ThreadHandle *_thHandle,
#endif /*FBPDR*/
			int _verbose, bool _basic, bool _random, bool _revpdr) :
			model(_model), k(1), nextState(0), litOrder(), slimLitOrder(), numLits(
					0), numUpdates(0), maxDepth(1), maxCTGs(3), maxJoins(
					1 << 20), micAttempts(3), cexState(0), nQuery(0), nCTI(0), nCTG(
					0), nmic(0), satTime(0), nCoreReduced(0), nAbortJoin(0), nAbortMic(
					0), poRedTime(0), strengthenTime(0), currentClock(0), startTime(
					0),
#ifdef FBPDR
					states(_states), statesOther(_statesOther), frames(_frames), framesOther(
							_framesOther),
#if defined(FBPDR_USE_PO_INTERSECTION) || defined(FBPDR_USE_PO_INTERSECTION_SEMANTIC)
					pos(_pos), posOther(_posOther),
#endif
					thHandle(_thHandle),
#endif /*FBPDR*/
					revpdr(_revpdr), verbose(_verbose), random(_random)
	{

#ifdef FBPDR
		if (idleState())
			throw std::runtime_error("killed");
#endif

#ifndef FBPDR
		//create frame instance
		frames = new vector<Frame>();
		states = new vector<State>();
#endif

		slimLitOrder.heuristicLitOrder = &litOrder;
		if (_basic)
		{
			cout << "basic!?" << endl;
			maxDepth = 0;
			maxJoins = 0;
			maxCTGs = 0;
		}

		consecSolver = model.newSolver();
		model.loadTransitionRelationConsec(*consecSolver);
		if (random)
		{
			cout << "random!?" << endl;
			consecSolver->random_seed = rand();
			consecSolver->rnd_init_act = true;
		}

		// construct lifting solver
		if (!revpdr)
		{
			lifts = model.newSolver();
			// don't assert primed invariant constraints
			model.loadTransitionRelation(*lifts, false);
			// assert notInvConstraints (in stateOf) when lifting
			notInvConstraints = Minisat::mkLit(lifts->newVar());
			Minisat::vec<Minisat::Lit> cls;
			cls.push(~notInvConstraints);
			for (vector<Minisat::Lit>::const_iterator i =
					model.invariantConstraints().begin();
					i != model.invariantConstraints().end(); ++i)
				cls.push(model.primeLit(~*i));
			lifts->addClause_(cls);
		}
	}
	~IC3()
	{
		if (consecSolver)
			delete consecSolver;
		if (!revpdr && lifts)
			delete lifts;
#ifndef FBPDR
		//create frame instance
		delete frames;
		delete states;
#endif
	}

	// The main loop.
	bool check()
	{
		startTime = time();  // stats

#ifdef revpogen
		if (revpdr)
			initRevPDRpoGen();
#endif

		while (true)
		{
			if (verbose > 1)
				cout << "Level " << k << endl;
			extend();                         // push frontier frame
			if (!strengthen())
				return false;  // strengthen to remove bad successors
			if (propagate())
				return true;     // propagate clauses; check for proof
			printStats();
			++k;                              // increment frontier
		}
	}


	void printWitness()
	{
		if(revpdr)
			printWitnessRevPDR();
		else
			printWitnessOrigPDR();

	}

	void printStats()
	{
		if (!verbose)
			return;
		clock_t etime = time();
		cout << ". Elapsed time: " << ((double) etime / sysconf(_SC_CLK_TCK))
				<< endl;
		etime -= startTime;
		if (!etime)
			etime = 1;
		cout << ". % SAT:        "
				<< (int) (100 * (((double) satTime) / ((double) etime)))
				<< endl;
		cout << ". K:            " << k << endl;
		cout << ". # Queries:    " << nQuery << endl;
		cout << ". # CTIs:       " << nCTI << endl;
		cout << ". # CTGs:       " << nCTG << endl;
		cout << ". # mic calls:  " << nmic << endl;
		cout << ". Queries/sec:  "
				<< (int) (((double) nQuery) / ((double) etime)
						* sysconf(_SC_CLK_TCK)) << endl;
		cout << ". Mics/sec:     "
				<< (int) (((double) nmic) / ((double) etime)
						* sysconf(_SC_CLK_TCK)) << endl;
		cout << ". # Red. cores: " << nCoreReduced << endl;
		cout << ". # Int. joins: " << nAbortJoin << endl;
		cout << ". # Int. mics:  " << nAbortMic << endl;
		cout << ". Init Time: " << ((double) isInitTime / sysconf(_SC_CLK_TCK))
				<< endl;
		if (numUpdates)
			cout << ". Avg lits/cls: " << numLits / numUpdates << endl;
	}

private:

	int verbose; // 0: silent, 1: stats, 2: all
	bool revpdr; //true: use Reverse PDR, false: standard
	bool random;
	ThreadHandle *thHandle;

	clock_t strengthenTime;
	clock_t currentClock;

	struct SupportVar
	{
		unsigned int index;
		unsigned int outDegr;

		SupportVar(const SupportVar &sv) :
				index(sv.index), outDegr(sv.outDegr)
		{
		} //copy constructor
		SupportVar(SupportVar &&sv) :
				index(sv.index), outDegr(sv.outDegr) //move constructor
		{
			sv.index = 0;
			sv.outDegr = 0;
		}

		//copy assignment
		SupportVar& operator=(const SupportVar &sv)
		{
			this->index = sv.index;
			this->outDegr = sv.outDegr;
			return *this;
		}

		SupportVar() :
				index(0), outDegr(0)
		{
		}
		SupportVar(unsigned int i, unsigned int o) :
				index(i), outDegr(o)
		{
		}

		bool operator ==(SupportVar sv) const
		{
			return (index == sv.index);
		}
		bool operator !=(SupportVar sv) const
		{
			return (index != sv.index);
		}
	};

	class SuppVarComp
	{
	public:
		bool operator()(const SupportVar &v1, const SupportVar &v2) const
		{
			if (v1.outDegr > v2.outDegr)
				return true;  // prefer higher out degree
			if (v1.outDegr < v2.outDegr)
				return false;
			if (v1.index < v2.index)
				return true;  // canonical final decider
			return false;
		}
	};
	typedef std::set<SupportVar, SuppVarComp> SvPrioQueue;

	class ReverseVarComp
	{
	public:
		bool operator()(const Minisat::Var &v1, const Minisat::Var &v2) const
		{
			if (v1 > v2)
				return true;
			return false;
		}
	};

	//vector holding the number of occurences of an input in
	//the conflict of a lifting call
	vector<unsigned int> inputConflictOcc;

	//state variables with disjoint support sets
	std::vector<unsigned int> stateVarsWithDisjSupp;
	//ordered out degrees of support variables (of transition functions)
	SvPrioQueue orderedSuppDegr;

	string stringOfLitVec(const LitVec &vec)
	{
		stringstream ss;
		for (vector<Minisat::Lit>::const_iterator i = vec.begin();
				i != vec.end(); ++i)
			ss << model.stringOfLit(*i) << " ";
		return ss.str();
	}

	Model &model;
	size_t k;

	vector<State> *states;
	vector<State> *statesOther;
	size_t nextState;
	// WARNING: do not keep reference across newState() calls
	State& state(size_t sti)
	{
		return (*states)[sti - 1];
	}
	State& stateOther(size_t sti)
	{
		return (*statesOther)[sti - 1];
	}
	size_t newState()
	{
		if (nextState >= states->size())
		{
			states->resize(states->size() + 1);
			states->back().index = states->size();
			states->back().used = false;
		}
		size_t ns = nextState;
		assert(!states->at(ns).used);
		states->at(ns).used = true;
		while (nextState < states->size() && states->at(nextState).used)
			nextState++;
		return ns + 1;
	}
	void delState(size_t sti)
	{
		State &st = state(sti);
		st.used = false;
		st.latches.clear();
		st.inputs.clear();
		if (nextState > st.index - 1)
			nextState = st.index - 1;
	}
	void resetStates()
	{
		for (vector<State>::iterator i = states->begin(); i != states->end();
				++i)
		{
			i->used = false;
			i->latches.clear();
			i->inputs.clear();
		}
		nextState = 0;
	}

	class ObligationComp
	{
	public:
		bool operator()(const Obligation &o1, const Obligation &o2) const
		{
			if (o1.level < o2.level)
				return true;  // prefer lower levels (required)
			if (o1.level > o2.level)
				return false;
			if (o1.depth < o2.depth)
				return true;  // prefer shallower (heuristic)
			if (o1.depth > o2.depth)
				return false;
			if (o1.state < o2.state)
				return true;  // canonical final decider
			return false;
		}
	};
	typedef set<Obligation, ObligationComp> PriorityQueue;

#if defined(FBPDR_USE_PO_INTERSECTION) || defined(FBPDR_USE_PO_INTERSECTION_SEMANTIC)
	DeeperPoFirst *pos;
	DeeperPoFirst *posOther;

	void insertIntoPoShare(DeeperPoFirst *share, const Obligation &po)
	{
		FullObligation fPo(state(po.state).latches, po.level, po.depth);
		share->insert(fPo);
	}
#endif

	vector<Frame> *frames;
#ifdef FBPDR
	vector<Frame> *framesOther;
#endif
	Minisat::Solver *consecSolver;

	Minisat::Solver *lifts;
	Minisat::Lit notInvConstraints;

	// Push a new Frame.
	void extend()
	{
		while (frames->size() < k + 2)
		{
			frames->resize(frames->size() + 1);
			Frame &fr = frames->back();
			fr.k = frames->size() - 1;
			fr.actLit = Minisat::mkLit(consecSolver->newVar(), false);

			if (fr.k == 0)
			{
				if (!revpdr)
				{
					model.loadInitialCondition(*consecSolver, fr.actLit);
				}
				else
					consecSolver->addClause(model.primedError(), ~fr.actLit); //reverse PDR
			}
		}
	}

	// Structure and methods for imposing priorities on literals
	// through ordering the dropping of literals in mic (drop leftmost
	// literal first) and assumptions to Minisat.  The implemented
	// ordering prefers to keep literals that appear frequently in
	// addCube() calls.
	struct HeuristicLitOrder
	{
		HeuristicLitOrder() :
				_mini(1 << 20)
		{
		}
		vector<float> counts;
		size_t _mini;
		void count(const LitVec &cube)
		{
			assert(!cube.empty());
			// assumes cube is ordered
			size_t sz = (size_t) Minisat::toInt(Minisat::var(cube.back()));
			if (sz >= counts.size())
				counts.resize(sz + 1);
			_mini = (size_t) Minisat::toInt(Minisat::var(cube[0]));
			for (vector<Minisat::Lit>::const_iterator i = cube.begin();
					i != cube.end(); ++i)
				counts[(size_t) Minisat::toInt(Minisat::var(*i))] += 1;
		}
		void decay()
		{
			for (size_t i = _mini; i < counts.size(); ++i)
				counts[i] *= 0.99;
		}
	} litOrder;

	struct SlimLitOrder
	{
		HeuristicLitOrder *heuristicLitOrder;

		SlimLitOrder()
		{
		}

		bool operator()(const Minisat::Lit &l1, const Minisat::Lit &l2) const
		{
			// l1, l2 must be unprimed
			size_t i2 = (size_t) Minisat::toInt(Minisat::var(l2));
			if (i2 >= heuristicLitOrder->counts.size())
				return false;
			size_t i1 = (size_t) Minisat::toInt(Minisat::var(l1));
			if (i1 >= heuristicLitOrder->counts.size())
				return true;
			return (heuristicLitOrder->counts[i1]
					< heuristicLitOrder->counts[i2]);
		}
	} slimLitOrder;

	float numLits, numUpdates;
	void updateLitOrder(const LitVec &cube, size_t level)
	{
		litOrder.decay();
		numUpdates += 1;
		numLits += cube.size();
		litOrder.count(cube);
	}

	// order according to preference
	void orderCube(LitVec &cube)
	{
		stable_sort(cube.begin(), cube.end(), slimLitOrder);
	}

	typedef Minisat::vec<Minisat::Lit> MSLitVec;

	// Orders assumptions for Minisat.
	void orderAssumps(MSLitVec &cube, bool rev, int start = 0)
	{
		stable_sort(cube + start, cube + cube.size(), slimLitOrder);
		if (rev)
			reverse(cube + start, cube + cube.size());
	}

	//pushes all necessary frame activation literals into assumps,
	//which are required to check for reachability with frame "frameIndex".
	//Delta encoded trace: For frame i, activate frames i+1, i+2, ... as well
	void prepareConsecAssumps(MSLitVec &assumps, size_t frameIndex, bool onlySubsumption = false)
	{
		if(!onlySubsumption)
			assumps.push(model.getTransActLit());
		if (frameIndex > 0)
		{
			for (size_t i = frameIndex; i < frames->size(); ++i)
			{
				assert(frames->at(i).k == i);
				assumps.push(frames->at(i).actLit);
			}
		}
		else
		{
			assumps.push(frames->at(0).actLit);
		}
	}

	LitVec currBadInput;
	// Assumes that last call to fr.consecution->solve() was
	// satisfiable.  Extracts state(s) cube from satisfying
	// assignment.
	size_t stateOf(Frame &fr, size_t succ = 0, bool noCTG = false)
	{
		// create state
		size_t st = newState();
		state(st).successor = succ;
		if(succ==0 && !currBadInput.empty())
			currBadInput.clear();
		MSLitVec assumps;
		assumps.capacity(
				1 + 2 * (model.endInputs() - model.beginInputs())
						+ (model.endLatches() - model.beginLatches()));
		Minisat::Lit act = Minisat::mkLit(lifts->newVar()); // activation literal
		assumps.push(act);
		Minisat::vec<Minisat::Lit> cls;
		cls.push(~act);
		cls.push(notInvConstraints);  // successor must satisfy inv. constraint
		if (succ == 0)
			cls.push(~model.primedError());
		else
			for (vector<Minisat::Lit>::const_iterator i =
					state(succ).latches.begin(); i != state(succ).latches.end();
					++i)
				cls.push(model.primeLit(~*i));
		lifts->addClause_(cls);

		// extract and assert primary inputs
		for (VarVec::const_iterator i = model.beginInputs();
				i != model.endInputs(); ++i)
		{
			Minisat::lbool val = consecSolver->modelValue(i->var());
			if (val != Minisat::l_Undef)
			{
				Minisat::Lit pi = i->lit(val == Minisat::l_False);
				state(st).inputs.push_back(pi);  // record full inputs
				assumps.push(pi);
			}
		}
		// some properties include inputs, so assert primed inputs after
		for (VarVec::const_iterator i = model.beginInputs();
				i != model.endInputs(); ++i)
		{
			Minisat::lbool pval = consecSolver->modelValue(
					model.primeVar(*i).var());
			if (pval != Minisat::l_Undef)
				assumps.push(model.primeLit(i->lit(pval == Minisat::l_False)));
			if (succ == 0) //store inputs that lead to final bad state
				currBadInput.push_back(i->lit(pval == Minisat::l_False));
		}
		int sz = assumps.size();
		// extract and assert latches
		LitVec latches;
		for (VarVec::const_iterator i = model.beginLatches();
				i != model.endLatches(); ++i)
		{
			Minisat::lbool val = consecSolver->modelValue(i->var());
			if (val != Minisat::l_Undef)
			{
				Minisat::Lit la = i->lit(val == Minisat::l_False);
				latches.push_back(la);
				assumps.push(la);
			}
		}
		orderAssumps(assumps, false, sz); // empirically found to be best choice
		// State s, inputs i, transition relation T, successor t:
		//   s & i & T & ~t' is unsat
		// Core assumptions reveal a lifting of s.
		++nQuery;
		startTimer();  // stats
		bool rv = lifts->solve(assumps);
		endTimer(satTime);
		assert(!rv);
		// obtain lifted latch set from unsat core
		for (vector<Minisat::Lit>::const_iterator i = latches.begin();
				i != latches.end(); ++i)
			if (lifts->conflict.has(~*i))
			{
				state(st).latches.push_back(*i);  // record lifted latches
			}
		// deactivate negation of successor
		lifts->releaseVar(~act);
		return st;
	}

	// Assumes that last call to fr.consecution->solve() was
	// satisfiable.  Extracts state(s) cube from satisfying
	// assignment. Reverse: No Lifting
	// Reverse: succ is pred (to be precise)
	size_t stateOfReverse(Frame &fr, size_t pred = 0)
	{
		// create state
		size_t st = newState();
		state(st).successor = pred; //actually predecessor in Rev PDR
		if(fr.k == 0 && !currBadInput.empty())
			currBadInput.clear();
		// extract and assert primary inputs
		for (VarVec::const_iterator i = model.beginInputs();
				i != model.endInputs(); ++i)
		{
			Minisat::lbool val = consecSolver->modelValue(i->var());
			if (val != Minisat::l_Undef)
			{
				Minisat::Lit pi = i->lit(val == Minisat::l_False);
				state(st).inputs.push_back(pi);  // record full inputs
			}
		}

		// extract and assert latches,
		// extract primed -> unprime
		LitVec latches;
		for (VarVec::const_iterator i = model.beginLatches();
				i != model.endLatches(); ++i)
		{
			Minisat::lbool val = consecSolver->modelValue(
					model.primeVar(*i).var());
			if (val != Minisat::l_Undef)
			{
				Minisat::Lit la = i->lit(val == Minisat::l_False);
				state(st).latches.push_back(la);
			}
		}

		if (fr.k == 0) //collect primed inputs for counterexample printing
		{
			for (VarVec::const_iterator i = model.beginInputs();
				i != model.endInputs(); ++i)
			{
				Minisat::lbool pval = consecSolver->modelValue(
					model.primeVar(*i).var());
				if (pval != Minisat::l_Undef)
				{
					Minisat::Lit pi = i->lit(pval == Minisat::l_False);
					currBadInput.push_back(pi);  // record full inputs
				}
			}
		}

#ifdef revpogen
		if (pred == 0)
		{
			LitVec predlatches;
			LitVec init = model.getInitLits();
			for (auto &lit : init)
			{
				predlatches.push_back(lit);
			}
			generalizeNextStateStructAdv(consecSolver, predlatches,
					state(st).latches);
		}
		else
		{
			generalizeNextStateStructAdv(consecSolver, state(pred).latches,
					state(st).latches);
		}

		assert(state(st).latches.size() > 0);
		assert(pred == 0 || state(pred).latches.size() > 0);
#endif

		return st;
	}

	// Checks if cube contains any initial states.
	// returns: 1: initiation holds; 0: doesn't hold because of intersection with
	// original initial states; 2: doesn't hold because of intersection with
	// reachable states
	int initiation(const LitVec &latches, size_t depth = 0)
	{
		//if error is trvially unsat, revPDR may deduce empty cubes
		if (latches.size() == 0)
		{
			return false;
		}

		clock_t currClk = time();
		bool rv = model.isInitial(latches, revpdr);
		isInitTime+=(time() - currClk);
#ifdef FBPDR_USE_PO_INTERSECTION
		if (rv)
			return 0;
		else
		{
			if (!poIntersection(latches, depth))
				return 1;
			else
				return 2; // intersection with reachable states
		}
#else
		return !rv;
#endif
	}

	/*
	 * ungeneralizes a reachable cube
	 */
	void ungenReachableCube(LitVec &cube, const LitSet &unreachableCore)
	{
		if (verbose > 1)
		{
			cout << "core: " << unreachableCore.size() << endl;
			cout << "old cube: " << cube.size() << endl;
		}
		if (unreachableCore.size() > 0)
		{
			LitSet tmp(cube.begin(), cube.end());
			for (const auto &lit : unreachableCore)
			{
				if (tmp.find(lit) == tmp.end())
				{
					tmp.insert(lit); //cube.push_back(lit);
				}
			}
			vector<Minisat::Lit> tmpVec(tmp.begin(), tmp.end());
			cube.swap(tmpVec);
		}
		cout << "resulting cube: " << cube.size() << endl;
	}

	// Check if ~latches is inductive relative to frame fi.  If it's
	// inductive and core is provided, extracts the unsat core.  If
	// it's not inductive and pred is provided, extracts
	// predecessor(s).
	bool consecution(size_t fi, const LitVec &latches, size_t succ = 0,
			LitVec *core = NULL, size_t *pred = NULL, bool orderedCore = false,
			bool noCTG = true)
	{
		Frame &fr = (*frames)[fi];
		MSLitVec assumps, cls;

		assumps.capacity(1 + latches.size() + (frames->size() - fi));
		cls.capacity(1 + latches.size());
		Minisat::Lit act = Minisat::mkLit(consecSolver->newVar());
		assumps.push(act);
		cls.push(~act);

		//include necessary frame activation literals
		prepareConsecAssumps(assumps, fi);

		//store current assumption vector size
		size_t prevAssumpSize = assumps.size();

		for (vector<Minisat::Lit>::const_iterator i = latches.begin();
				i != latches.end(); ++i)
		{
			if (!revpdr)
				cls.push(~*i);
			else
				cls.push(~model.primeLit(*i)); //reverse PDR: primed
			assumps.push(*i);  // push unprimed...
		}
		// ... order... (empirically found to best choice)
		if (pred)
			orderAssumps(assumps, false, prevAssumpSize);
		else
			orderAssumps(assumps, orderedCore, prevAssumpSize);
		// ... now prime (don't prime for reverse PDR)
		if (!revpdr)
		{
			for (int i = prevAssumpSize; i < assumps.size(); ++i)
				assumps[i] = model.primeLit(assumps[i]);
		}
		consecSolver->addClause_(cls);

		// F_fi & ~latches & T & latches'
		++nQuery;
		startTimer();  // stats
		bool rv = consecSolver->solve(assumps);
		endTimer(satTime);
		if (rv)
		{
			// fails: extract predecessor(s)
			if (pred)
			{
				if (!revpdr)
				{
					*pred = stateOf(fr, succ, noCTG);
				}
				else
					*pred = stateOfReverse(fr, succ);
			}
			consecSolver->releaseVar(~act);
			return false;
		}
		// succeeds
		if (core)
		{
			if (pred && orderedCore)
			{
				// redo with correctly ordered assumps
				reverse(assumps + prevAssumpSize, assumps + assumps.size());
				++nQuery;
				startTimer();  // stats
				rv = consecSolver->solve(assumps);
				assert(!rv);
				endTimer(satTime);
			}
			assert(core->size() == 0);
			for (vector<Minisat::Lit>::const_iterator i = latches.begin();
					i != latches.end(); ++i)
			{
				if (!revpdr)
				{
					if (consecSolver->conflict.has(~model.primeLit(*i)))
						core->push_back(*i);
				}
				else
				{   //reverse PDR case (no successor)
					if (consecSolver->conflict.has(~*i))
						core->push_back(*i);
				}
			}
#ifdef FBPDR_USE_PO_INTERSECTION
			LitSet unreachableCore;
			int initIndicator = initiation(*core);
			if (initIndicator != 1)
				*core = latches;
#else
			if (!initiation(*core))
			{
#ifdef FBPDR_USE_PO_INTERSECTION_SEMANTIC
				model.ungenInitCube(*core, latches, revpdr);
#else
				*core = latches;
#endif	/*FBPDR_USE_PO_INTERSECTION_SEMANTIC*/
			}
#endif
		}
		consecSolver->releaseVar(~act);
		return true;
	}

	size_t maxDepth, maxCTGs, maxJoins, micAttempts;

// Based on
//
//   Zyad Hassan, Aaron R. Bradley, and Fabio Somenzi, "Better
//   Generalization in IC3," (submitted May 2013)
//
// Improves upon "down" from the original paper (and the FMCAD'07
// paper) by handling CTGs.
	bool ctgDown(size_t level, LitVec &cube, size_t keepTo, size_t recDepth)
	{
		size_t ctgs = 0, joins = 0;
		while (true)
		{
			// induction check
			if (!initiation(cube))
				return false;
			if (revpdr) //no ctg analysis with reverse PDR (empirically found better)
				recDepth = maxDepth + 1;
			if (recDepth > maxDepth)
			{
				// quick check if recursion depth is exceeded
				LitVec core;
				bool rv = consecution(level, cube, 0, &core, NULL, true, false);
				if (rv && core.size() < cube.size())
				{
					++nCoreReduced;  // stats
					cube = core;
				}
				return rv;
			}
			// prepare to obtain CTG
			size_t cubeState = newState();
			state(cubeState).successor = 0;
			state(cubeState).latches = cube;
			size_t ctg;
			LitVec core;
			if (consecution(level, cube, cubeState, &core, &ctg, true, false))
			{
				if (core.size() < cube.size())
				{
					++nCoreReduced;  // stats
					cube = core;
				}
				// inductive, so clean up
				delState(cubeState);
				return true;
			}
			// not inductive, address interfering CTG
			LitVec ctgCore;
			bool ret = false;
			if (ctgs < maxCTGs && level > 1 && initiation(state(ctg).latches)
					&& consecution(level - 1, state(ctg).latches, cubeState,
							&ctgCore, NULL, false, false))
			{
				// CTG is inductive relative to level-1; push forward and generalize
				++nCTG;  // stats
				++ctgs;
				size_t j = level;
				// QUERY: generalize then push or vice versa?
				while (j <= k && consecution(j, ctgCore))
					++j;
				mic(j - 1, ctgCore, recDepth + 1);
				addCube(j, ctgCore);
			}
			else if (joins < maxJoins)
			{
				// ran out of CTG attempts, so join instead
				ctgs = 0;
				++joins;
				LitVec tmp;
				for (size_t i = 0; i < cube.size(); ++i)
					if (binary_search(state(ctg).latches.begin(),
							state(ctg).latches.end(), cube[i]))
						tmp.push_back(cube[i]);
					else if (i < keepTo)
					{
						// previously failed when this literal was dropped
						++nAbortJoin;  // stats
						ret = true;
						break;
					}
				cube = tmp;  // enlarged cube
			}
			else
				ret = true;
			// clean up
			delState(cubeState);
			delState(ctg);
			if (ret)
				return false;
		}
	}

// Extracts minimal inductive (relative to level) subclause from
// ~cube --- at least that's where the name comes from.  With
// ctgDown, it's not quite a MIC anymore, but what's returned is
// inductive relative to the possibly modifed level.
	void mic(size_t level, LitVec &cube, size_t recDepth)
	{
		++nmic;  // stats
		// try dropping each literal in turn
		size_t attempts = micAttempts;
		orderCube(cube);
		for (size_t i = 0; i < cube.size();)
		{
			LitVec cp(cube.begin(), cube.begin() + i);
			cp.insert(cp.end(), cube.begin() + i + 1, cube.end());
			if (ctgDown(level, cp, i, recDepth))
			{
				// maintain original order
				LitSet lits(cp.begin(), cp.end());
				LitVec tmp;
				for (vector<Minisat::Lit>::const_iterator j = cube.begin();
						j != cube.end(); ++j)
					if (lits.find(*j) != lits.end())
						tmp.push_back(*j);
				cube.swap(tmp);
				// reset attempts
				attempts = micAttempts;
			}
			else
			{
				if (!--attempts)
				{
					// Limit number of attempts: if micAttempts literals in a
					// row cannot be dropped, conclude that the cube is just
					// about minimal.  Definitely improves mics/second to use
					// a low micAttempts, but does it improve overall
					// performance?
					++nAbortMic;  // stats
					return;
				}
				++i;
			}
		}
	}

// wrapper to start inductive generalization
	void mic(size_t level, LitVec &cube)
	{
		mic(level, cube, 1);
	}

	size_t earliest;  // track earliest modified level in a major iteration

// Adds cube to frames at and below level, unless !toAll, in which
// case only to level.
	void addCube(size_t level, LitVec &cube, bool toAll = true, bool silent =
			false)
	{
		if (!revpdr)
		{
			assert(!cube.empty());
		}
		else
		{
			//reverse PDR may proof the empty cube to be unable
			//to reach the unsafe states -> design is safe
			if (cube.empty())
			{
				consecSolver->addEmptyClause();
				return;
			}
		}
		sort(cube.begin(), cube.end());

		pair<CubeSet::iterator, bool> rv = (*frames)[level].borderCubes.insert(
				cube);
		if (!rv.second)
			return;
		if (!silent && verbose > 1)
			cout << level << ": " << stringOfLitVec(cube) << endl;
		earliest = min(earliest, level);
		MSLitVec cls;
		cls.capacity(cube.size() + 1);

		if (!revpdr)
		{
			for (vector<Minisat::Lit>::const_iterator i = cube.begin();
					i != cube.end(); ++i)
				cls.push(~*i);
		}
		else
		{
			//reverse: frames hold primed clauses
			for (vector<Minisat::Lit>::const_iterator i = cube.begin();
					i != cube.end(); ++i)
				cls.push(~model.primeLit(*i));
		}
		//learn clause
		cls.push(~(*frames)[level].actLit);
		consecSolver->addClause(cls);

		if (toAll && !silent)
			updateLitOrder(cube, level);
	}

	// ~cube was found to be inductive relative to level; now see if
	// we can do better.
	size_t generalize(size_t level, LitVec cube)
	{
		// generalize
		mic(level, cube);
		// push
		do
		{
			++level;
		} while (level <= k && consecution(level, cube));
		//cout << "level to add: " << level << endl;
		addCube(level, cube);
		//cout << ".. done" << endl;
		return level;
	}

	size_t cexState;  // beginning of counterexample trace

	// Process obligations according to priority.
	bool handleObligations(PriorityQueue obls)
	{
		while (!obls.empty())
		{
			PriorityQueue::iterator obli = obls.begin();
			Obligation obl = *obli;
			LitVec core;
			size_t predi;
			//intersection with counterpart proof obligations?
#ifdef FBPDR_USE_PO_INTERSECTION
			if (posOther->size() > 0)
			{
				if (poIntersection(state(obl.state).latches, obl.depth))
				{
					// An initial state is a predecessor.
					cexState = obl.state;
					return false;
				}
			}
#endif

#ifdef FBPDR_USE_PO_INTERSECTION_SEMANTIC
			if (posOther->size() > 0 && false) //TODO: witnesses from PO intersections
			{
				if (!initiation(state(obl.state).latches, obl.depth))
				{
					// An initial state is a predecessor.
					cexState = obl.state;
					return false;
				}
			}
#endif
			// Is the obligation fulfilled?
			if (consecution(obl.level, state(obl.state).latches, obl.state,
					&core, &predi))
			{
				// Yes, so generalize and possibly produce a new obligation
				// at a higher level.
				obls.erase(obli);
				size_t n = generalize(obl.level, core);
				if (n <= k)
					obls.insert(Obligation(obl.state, n, obl.depth));
			}
			else if (obl.level == 0)
			{
				// No, in fact an initial state is a predecessor.
				cexState = predi;
				return false;
			}
			else
			{
				++nCTI;  // stats
				++CTIperFrame;
				// No, so focus on predecessor.
				obls.insert(Obligation(predi, obl.level - 1, obl.depth + 1));
#if defined(FBPDR_USE_PO_INTERSECTION) || defined(FBPDR_USE_PO_INTERSECTION_SEMANTIC)
				addPoToShare(Obligation(predi, obl.level - 1, obl.depth + 1));
#endif
			}

#ifdef FBPDR
			//during iteration over cubesets in propagation phase:
			//do not allow alterations by other PDR version (no switching between threads here)
			//if (pred != NULL)
			{
				if (idleState())
					throw std::runtime_error("killed");
			}

#ifdef FBPDR_USE_LEMMA_SHARING
#ifdef FBPDR_REMOVE_DISCHARGED_POS
			removeDischargedPos(obls);
#endif /*FBPDR_REMOVE_DISCHARGED_POS*/
#endif
#endif
		}
		return true;
	}

	bool trivial;  // indicates whether strengthening was required
	unsigned int CTIperFrame = 0;
	int oldnCTI = 0;
	// Strengthens frontier to remove error successors.
	bool strengthen()
	{
		CTIperFrame = 0; //reset with each new frame
		oldnCTI = nCTI;
#ifndef FBPDR_USE_LEMMA_SHARING
		Frame &frontier = (*frames)[k];
		earliest = k + 1;  // earliest frame with enlarged borderCubes
#endif
		trivial = true;  // whether any cubes are generated
		while (true)
		{
#ifdef FBPDR_USE_LEMMA_SHARING
			//during "handleObligations" the trace may be extended!
			Frame &frontier = (*frames)[k];
			earliest = k + 1;  // earliest frame with enlarged borderCubes
#endif
			++nQuery;
			startTimer();  // stats
			bool rv;
			Minisat::vec<Minisat::Lit> assumps;
			if (!revpdr)
			{
				assumps.capacity(1 + (frames->size() - frontier.k));
				assumps.push(model.primedError());
			}
			else
			{
				LitVec init = model.getInitLits();
				assumps.capacity(init.size() + (frames->size() - frontier.k));
				for (auto &lit : init)
				{
					assumps.push(lit);
				}
			}
			prepareConsecAssumps(assumps, frontier.k);
			rv = consecSolver->solve(assumps);
			endTimer(satTime);
			if (!rv)
				return true;
			// handle CTI with error successor
			++nCTI;  // stats
			CTIperFrame++;
			trivial = false;
			PriorityQueue pq;
			// enqueue main obligation and handle
			if (!revpdr)
				pq.insert(Obligation(stateOf(frontier, 0, true), k - 1, 1));
			else
				pq.insert(Obligation(stateOfReverse(frontier), k - 1, 1));

			if (!handleObligations(pq))
				return false;
			// finished with States for this iteration, so clean up
			resetStates();
		}
	}

	// Propagates clauses forward
	bool propagate(bool checkTermination = true)
	{
		if (verbose > 1)
			cout << "propagate" << endl;
		// 1. clean up: remove c in frame i if c appears in frame j when i < j
		CubeSet all;
		for (size_t i = k + 1; i >= earliest; --i)
		{
			Frame &fr = (*frames)[i];
			CubeSet rem, nall;
			set_difference(fr.borderCubes.begin(), fr.borderCubes.end(),
					all.begin(), all.end(), inserter(rem, rem.end()),
					LitVecComp());
			if (verbose > 1)
				cout << i << " " << fr.borderCubes.size() << " " << rem.size()
						<< " ";
			fr.borderCubes.swap(rem);
			set_union(rem.begin(), rem.end(), all.begin(), all.end(),
					inserter(nall, nall.end()), LitVecComp());
			all.swap(nall);
			for (CubeSet::const_iterator i = fr.borderCubes.begin();
					i != fr.borderCubes.end(); ++i)
				assert(all.find(*i) != all.end());
			if (verbose > 1)
				cout << all.size() << endl;
		}
		// 2. check if each c in frame i can be pushed to frame j
		for (size_t i = trivial ? k : 1; i <= k; ++i)
		{
			int ckeep = 0, cprop = 0, cdrop = 0;
			Frame &fr = (*frames)[i];
			for (CubeSet::iterator j = fr.borderCubes.begin();
					j != fr.borderCubes.end();)
			{
#if defined(FBPDR_USE_PO_INTERSECTION) || defined(FBPDR_USE_PO_INTERSECTION_SEMANTIC)
				if(!j->bad) //ignore bad cubes here! No propagation
#endif
				{
					LitVec core;
					if (consecution(i, *j, 0, &core))
					{
						++cprop;
						// only add to frame i+1 unless the core is reduced
						addCube(i + 1, core, core.size() < j->size(), true);
						CubeSet::iterator tmp = j;
						++j;
						fr.borderCubes.erase(tmp);
					}
					else
					{
						++ckeep;
						++j;
					}
				}
#if defined(FBPDR_USE_PO_INTERSECTION) || defined(FBPDR_USE_PO_INTERSECTION_SEMANTIC)
				else
				{
					++j;
					//cout << "bad cube ignored" << endl;
				}
#endif
			}
			if (verbose > 1)
				cout << i << " " << ckeep << " " << cprop << " " << cdrop
						<< endl;
			if (fr.borderCubes.empty() && checkTermination
#ifdef FBPDR_USE_LEMMA_SHARING
					&& fr.k > highestStrengthenedFrame // do not check termination for strengthened frames
#endif
					)
			{
				//printCertificateCnf(fr);
				buildCertifaiger(fr, revpdr);
				return true;
			}
		}
		// 3. simplify frames
		consecSolver->simplify();
		if (!revpdr)
			lifts->simplify();
		return false;
	}

	Minisat::Var currCertVarInd = 0;
	Minisat::Var getCertMappedVar(map<Minisat::Var, Minisat::Var>& varIndexMapping, Minisat::Var var)
	{
		if(varIndexMapping.find(var) == varIndexMapping.end())
		{
			++currCertVarInd;
			varIndexMapping.insert(pair<Minisat::Var, Minisat::Var>(var, currCertVarInd));
			return currCertVarInd;
		}
		else
			return varIndexMapping.at(var);
	}

	void printCertificateCnf(const Frame & frame)
	{
		std::string header = "p cnf ";
		std::string clauses = "";
		std::string footer = "";
		unsigned nClauses = 0;
		unsigned maxVar = 0;
		map<Minisat::Var, string> varNameMapping; // mapping: name of variable (certificate index)
		map<Minisat::Var, Minisat::Var> varIndexMapping; // mapping: certificate index of local index variable 
		currCertVarInd = 0;
		for (size_t i = frame.k; i < frames->size(); ++i)
		{
			Frame &fr = frames->at(i);
			for (CubeSet::iterator j = fr.borderCubes.begin();
					j != fr.borderCubes.end(); ++j)
			{
				++nClauses;
				for (auto & lit: *j)
				{
					cout << (~lit).x << ", ";
					unsigned certVar = getCertMappedVar(varIndexMapping, Minisat::var(lit));
					if (certVar > maxVar) maxVar = certVar;
					clauses.append(to_string(certVar * (int)pow(-1, (int)Minisat::sign(lit))));
					clauses.append(" ");
					varNameMapping.insert(pair<Minisat::Var, string>(certVar, model.varOfLit(lit).name()));
				}
				clauses.append("0\n");
				cout << "\n";
			}
		}
		cout << endl;
		header.append(to_string(maxVar));
		header.append(" ");
		header.append(to_string(nClauses));
		header.append("\n");

		for(auto & [var, name]: varNameMapping)
		{
			//footer.append("c ");
			footer.append(name);
			footer.append(" = ");
			footer.append(to_string(2*var));
			footer.append("\n");
		}
		cout << header << clauses << footer << endl;
	}

	size_t currNewAigMaxVar = model.getAigMaxVar();
	vector<Minisat::Lit> cubeAnds;
	void buildCertifaiger(const Frame & frame, const bool revpdr)
	{
		aiger *aig = aiger_init();
		for(VarVec::const_iterator i = model.beginInputs(); i != model.endInputs(); ++i)
		{
			aiger_add_input(aig, Minisat::toInt(i->lit(false)), i->name().c_str());
		}
		for(VarVec::const_iterator i = model.beginLatches(); i != model.endLatches(); ++i)
		{
			aiger_add_latch(aig, Minisat::toInt(i->lit(false)), Minisat::toInt(model.nextStateFn(*i)),  i->name().c_str());
		}
		for(AigVec::const_iterator a = model.beginAnds(); a != model.endAnds(); ++a)
		{
			aiger_add_and(aig, Minisat::toInt(a->lhs), Minisat::toInt(a->rhs0), Minisat::toInt(a->rhs1));
		}
		assert(cubeAnds.size() == 0);
		for (size_t i = frame.k; i < frames->size(); ++i)
		{
			Frame &fr = frames->at(i);
			for (CubeSet::iterator j = fr.borderCubes.begin();
					j != fr.borderCubes.end(); ++j)
			{
				aigerAndsOfCube(aig, *j);
			}
		}
		
		if(revpdr)
		{
			if(cubeAnds.size() >= 1)
				aigerAndsOfCube(aig, model.getInitLits());
			finalBigOrNegated(aig);
		}
		else
			finalBigOr(aig);

		aiger_check(aig);
		int ret = aiger_open_and_write_to_file(aig, "./certificate.aag");
		assert(ret);

		aiger_reset(aig);
	}

	// cube = (l1 * l2* ... ) => andi = (...(((l1 * l2) * l3) * l4) ... )
	void aigerAndsOfCube(aiger * aig, const LitVec & cube)
	{
		if(cube.size() > 1)
		{
			for (size_t i = 0; i < cube.size() - 1; ++i)
			{
				++currNewAigMaxVar;
				aiger_add_and(aig, 2*currNewAigMaxVar, ((i==0) ? Minisat::toInt(cube[i]) : (2*(currNewAigMaxVar-1))), Minisat::toInt(cube[i+1]));
			}
			cubeAnds.push_back(Minisat::mkLit(currNewAigMaxVar, false));
		}
		else
		{
			assert(cube.size() == 1);
			cubeAnds.push_back(cube[0]);
		}
	}

	// error + and1 + and2 + ... (strengthening property)
	void finalBigOr(aiger * aig)
	{
		if(cubeAnds.size() >= 1)
		{
			++currNewAigMaxVar;
			aiger_add_and(aig, 2*currNewAigMaxVar, Minisat::toInt(~model.error()), Minisat::toInt(~cubeAnds[0])); // OR (negate operands and output) 

			if(cubeAnds.size() > 1)
			{
				for (size_t i = 0; i < cubeAnds.size() - 1; ++i)
				{
					++currNewAigMaxVar;
					aiger_add_and(aig, 2*currNewAigMaxVar, 2*(currNewAigMaxVar-1), Minisat::toInt(~cubeAnds[i+1]));
				}
			}
			aiger_add_output(aig, 2*currNewAigMaxVar+1, "O_cert"); //negated because of OR
		}
		else
			aiger_add_output(aig, Minisat::toInt(model.error()), "one_inductive"); //negated because of OR
	}
	// strengthen the property with the negated invariant (Reverse PDR proof)
	void finalBigOrNegated(aiger * aig)
	{
		if(cubeAnds.size() >= 1)
		{
			++currNewAigMaxVar;
			if(cubeAnds.size() == 1)
				aiger_add_and(aig, 2*currNewAigMaxVar, Minisat::toInt(~model.error()), Minisat::toInt(cubeAnds[0])); // OR (negate operands and output) 
			else
				aiger_add_and(aig, 2*currNewAigMaxVar, Minisat::toInt(~cubeAnds[0]), Minisat::toInt(~cubeAnds[1]));
			if(cubeAnds.size() > 1)
			{
				for (size_t i = 0; i < cubeAnds.size() - 1; ++i)
				{
					++currNewAigMaxVar;
					aiger_add_and(aig, 2*currNewAigMaxVar, 2*(currNewAigMaxVar-1), Minisat::toInt(~cubeAnds[i+1]));
				}
			}
			++currNewAigMaxVar;
			aiger_add_and(aig, 2*currNewAigMaxVar, Minisat::toInt(~model.error()), 2*(currNewAigMaxVar-1)+1); //negate OR-Tree output of proof

			aiger_add_output(aig, 2*currNewAigMaxVar+1, "O_cert"); //negated because of OR
		}
		else
			aiger_add_output(aig, Minisat::toInt(model.error()), "one_inductive");
	}

	/*
	 * More advanced structural generalization of Reverse PDR CTIs
	 * based on a bipartite graph.
	 * See our paper (Seufert and Scholl, DATE'18)
	 */
	void generalizeNextStateStructAdv(Minisat::Solver *slv, LitVec presentState,
			LitVec &nextState)
	{
		typedef vector<Minisat::Var> MSVarVec;
		MSVarVec arbitraryPresentStateBits;
		MSVarVec prunableNextStateVars;
		MSVarVec possPrunableNextStateVars;

		ternBool l_T((uint8_t) 1);
		ternBool l_F((uint8_t) 0);
		ternBool l_U((uint8_t) 2);

		bool sortps = true;

		//alter present state - add some literals with high out degree
		uint8_t found = 0;

		assert(!presentState.empty());

		/****************/
		//"left hand side approach"
		unsigned int nLatches = (model.endLatches() - model.beginLatches());
		//unsigned int nInputs=(model->endInputs()-model->beginInputs());

		LitSet presentStateSet;
		for (auto &lit : presentState)
			presentStateSet.insert(lit);
		presentState.clear();

		for (SvPrioQueue::const_iterator i = orderedSuppDegr.begin();
				i != orderedSuppDegr.end(); ++i)
		{
			Minisat::lbool val = slv->modelValue(i->index);
			Minisat::Lit la = Minisat::mkLit(i->index,
					(val == Minisat::l_False));
			if (presentStateSet.find(la) == presentStateSet.end()
					&& i->index > 0 && i->outDegr > 1)
			{
				if (i->outDegr < (nLatches / 2))
					break;	//heuristics, stop when outdegree seems not worth it
				found++;
				presentStateSet.insert(la);
			}

		}

		for (auto &lit : presentStateSet)
			presentState.push_back(lit);
		sortps = false;

		if (sortps)
		{
			std::sort(presentState.begin(), presentState.end());
		}

		Minisat::Var posVar = model.beginInputs()->var();

		//get present-state variables not contained in present-state cube to block
		std::vector<ternBool> valuation(model.getMaxVar() + 1, l_U);
		for (auto &lit : presentState)
		{
			valuation[lit.x >> 1] = !Minisat::sign(lit);
			while (Minisat::var(lit) > posVar)
			{
				arbitraryPresentStateBits.push_back(posVar);
				posVar++;
			}
			if (Minisat::var(lit) == posVar)
			{
				posVar++;
			}
		}
		posVar = Minisat::var(presentState[presentState.size() - 1]) + 1;
		while (posVar < model.endLatches()->var())
		{
			arbitraryPresentStateBits.push_back(posVar);
			posVar++;
		}

		//std::cout << "circuit propagation and traversation ..."; std::cout.flush();
		//propagate constants - find irrelevant unassigned support parts
		//could already find some (non-trivial) constant functions
		std::vector<unsigned int> outDegreesUnderAssignment =
				model.outDegrSuppVars;
		std::set<unsigned int> constants;
		model.circuitPropagation(valuation, constants);
		for (VarVec::const_iterator i = model.beginLatches();
				i != model.endLatches(); ++i)
		{
			if (model.nextStateFn(*i).x <= 1)
			{
				constants.insert(i->var());
				continue;		//no trivially constant functions
			}

			std::set<unsigned int> irrSuppVars = model.circuitTrav(valuation,
					i->var());
			for (std::set<unsigned int>::const_iterator i = irrSuppVars.begin();
					i != irrSuppVars.end(); ++i)
				outDegreesUnderAssignment[*i]--;

#ifdef FBPDR
			if (idleState())
				throw std::runtime_error("killed");
#endif
		}

		//check for common inputs/arbitrary state variables
		for (VarVec::const_iterator i = model.beginLatches();
				i != model.endLatches(); ++i)
		{
			if (model.nextStateFn(*i).x <= 1)
				continue;		//no trivially constant functions

			std::vector<unsigned int> suppI = model.getTransitionSupport(*i);
			//prune next-states by structural checks
			bool intersect = false;
			for (auto &suppVar : suppI)
			{
				//only check for inputs and arbitrary present state variables
				if (std::binary_search(arbitraryPresentStateBits.begin(),
						arbitraryPresentStateBits.end(), suppVar))
				{
					//is there at least one support variable with out degree > 1?
					if (outDegreesUnderAssignment[suppVar] > 1)
					{
						intersect = true;
						break;
					}
				}
			}
			//add !variable! to log disjoint next-state coi, non-constant
			if (!intersect && constants.find(i->var()) == constants.end())
				possPrunableNextStateVars.push_back(i->var());
		}

		//simulate random patterns -> no change? assume constant
		PatternFix res = model.simFixRndPatterns(presentState);
		for (auto &possPrunableVar : possPrunableNextStateVars)
		{
			if (!res[possPrunableVar - model.beginLatches()->var()].all()
					&& !res[possPrunableVar - model.beginLatches()->var()].none())
				prunableNextStateVars.push_back(possPrunableVar);
		}

		//prune possible next-state vars
		//exploit the fact that latch vars are enumerated
		std::sort(prunableNextStateVars.begin(), prunableNextStateVars.end());
		unsigned int pruningCount = 0;
		unsigned int idx = 0;

		for (size_t i = 0; i < nextState.size();)
		{
			if (std::binary_search(prunableNextStateVars.begin(),
					prunableNextStateVars.end(), Minisat::var(nextState[i])))
			{
				nextState[i] = nextState.back();
				nextState.pop_back();
			}
			else
				++i;
		}
		std::sort(nextState.begin(), nextState.end());
	}

	/*
	 * Preprocessing step for Reverse PDR PO generalization
	 */
	void initRevPDRpoGen()
	{
		//simulate random patterns -> no change? assume constant
		LitVec presentState;
		std::vector<Var> possPrunableNextStateVars;
		PatternFix res = model.simFixRndPatterns(presentState);

		stateVarsWithDisjSupp.clear();
		for (VarVec::const_iterator i = model.beginLatches();
				i != model.endLatches(); ++i)
		{
			model.getTransitionSupport(*i);

			bool notConst = false;
			for (size_t k = 1;
					k < res.at(i->var() - model.beginLatches()->var()).size();
					++k)
			{
				if (res[i->var() - model.beginLatches()->var()][k]
						!= res[i->var() - model.beginLatches()->var()][0])
					notConst = true;
			}

			if (notConst)
				possPrunableNextStateVars.push_back(*i);

#ifdef FBPDR
			if (idleState())
				throw std::runtime_error("killed");
#endif
		}

		for (std::vector<Var>::const_iterator i =
				possPrunableNextStateVars.begin();
				i != possPrunableNextStateVars.end(); ++i)
		{
			if (model.nextStateFn(*i).x > 1) //no constant functions
			{
				std::vector<unsigned int> suppI = model.getTransitionSupport(
						*i);
				//prune next-states by structural checks
				bool intersect = false;
				for (auto &suppVar : suppI)
				{
					//is there at least one support variable with out degree > 1?
					if (model.outDegrSuppVars[suppVar] > 1)
					{
						intersect = true;
						break;
					}
				}
				//add !variable! to log disjoint next-state coi
				if (!intersect)
					stateVarsWithDisjSupp.push_back(i->var());

#ifdef FBPDR
				if (idleState())
					throw std::runtime_error("killed");
#endif
			}
		}

		//store support variables ordered by out degree
		for (unsigned int i = 0; i < model.outDegrSuppVars.size(); ++i)
			orderedSuppDegr.insert(SupportVar(i, model.outDegrSuppVars[i]));
	}

	/* syntactic check for intersection of Proof-obligations with
	 * extended init / unsafe states (by proof-obligations of the
	 * reverted variant), alternative to SAT-based solution used in
	 * (Seufert, Scholl, DATE'18)
	 *
	 * core yields a subset of cube-literals which are responsible for
	 * cube being disjoint from all reachable states
	 */
#ifdef FBPDR_USE_PO_INTERSECTION
	bool poIntersection(const LitVec &cube, size_t depth, LitSet *core = NULL, size_t mindepth = 0)
	{
		for (auto &poOther : *posOther)
		{
			if (depth > 0
					&& (poOther.depth + depth)
							< (std::max(getSafeDepth(), getSafeDepthOther())))
				break; //if cube is an actual PO (indicated by depth > 0), don't check if CEX of respective length is provably absent
			else
			{
				if(depth == 0 && mindepth > 0 && poOther.depth < mindepth)
					break; //if a minimum depth is given, terminate if it is not exceeded
			}
			bool disjoint = false;
			for (auto &lit : cube)
			{
				disjoint = std::binary_search(poOther.lats.begin(),
						poOther.lats.end(), ~lit);
				if (disjoint)
				{
					if (core)
						core->insert(lit);
					break;
				}
			}
			if (!disjoint)
			{
				/*cout << "poOther: ";
				 for(auto& lit: poOther.lats)
				 cout << lit.x << ", ";
				 cout << endl;
				 cout << "current PO: ";
				 for(auto& lit: cube)
				 cout << lit.x << ", ";
				 cout << endl;*/
				if (core)
					core->clear();
				return true;
			}
		}

		return false;
	}
#endif

#if defined(FBPDR_USE_PO_INTERSECTION) || defined(FBPDR_USE_PO_INTERSECTION_SEMANTIC)
	int poIntersectionThresh = 200; // TODO: magic number into options
	/* add PO-state to shared proof obligations */
	void addPoToShare(const Obligation &po)
	{
		assert(!state(po.state).latches.empty());
		if (pos->size() < poIntersectionThresh)
			insertIntoPoShare(pos, po);
		else
		{
#ifdef DEEPER_PO_FIRST
			if (po.depth > (--pos->end())->depth)
#endif
#ifdef SHORTER_PO_FIRST
			if(state(po.state).latches.size() < (--pos->end())->lats.size())
#endif
			{
				pos->erase(--pos->end());
				insertIntoPoShare(pos, po);
			}
		}
	}
#endif

	/*
	 * returns the safe depth of the respective trace
	 */
	size_t getSafeDepth()
	{
		return k - 1;
	}

#ifdef FBPDR
	size_t getSafeDepthOther()
	{
		if (framesOther->size() > 3)
		{
			return (framesOther->size() - 3);
		}
		else
			return 0;
	}
#endif /*FBPDR*/

	/*
	 * yields execution of particular IC3 thread
	 */
	void yieldExecution()
	{
#if defined(FBPDR_USE_PO_INTERSECTION) || defined(FBPDR_USE_PO_INTERSECTION_SEMANTIC)
		if(verbose > 1)
			cout << "collected " << pos->size() << " POs." << endl;
#endif
		if (!revpdr)
		{
			//wake up reverse
			thHandle->awake = REV_PDR_HANDLE;
			if(verbose > 1)
				std::cout << "switch to reverse..." << std::endl;
		}
		else
		{
			//wake up original
			thHandle->awake = ORIG_PDR_HANDLE;
			if(verbose > 1)
				std::cout << "switch to original..." << std::endl;
		}
	}
#if defined(FBPDR_USE_PO_INTERSECTION) || defined(FBPDR_USE_PO_INTERSECTION_SEMANTIC)
	/*
	 * check the trace for bad cubes (blocking provably reachable states).
	 * Of course: only check for intersections with states which are "deeper"
	 * than the frame for which the cube was blocked. Set mindepth to frame of cube
	 */
	void checkForBadCubes()
	{
		vector<std::pair<LitVec, size_t>> badCubes;
		for (size_t i = 1; i < frames->size(); ++i)
		{
			Frame &fr = (*frames)[i];
			for (CubeSet::iterator j = fr.borderCubes.begin();
				j != fr.borderCubes.end();)
			{
#ifdef FBPDR_USE_PO_INTERSECTION
				if(!j->bad && poIntersection(*j,0,NULL,fr.k))
#else
				if(!j->bad && !initiation(*j))
#endif
				{
					badCubes.push_back(pair<LitVec, size_t>(*j, i)); //copy out - remove from set - insert again ... (TODO: refrain from sets here - again??)
					badCubes.back().first.bad = true;  //flag cube as bad, since it will eventually be reachable
					//cout << "bad cube found!" << endl;
					//(proven by reverted counterpart)
					CubeSet::iterator tmp = j;
					++j;
					fr.borderCubes.erase(tmp);
				}
				else
					++j;
			}
		}
		for(auto& badCube: badCubes)
			(*frames)[badCube.second].borderCubes.insert(badCube.first);
	}
#endif

	/*
	 * claims execution of particular IC3 thread, processing of shared
	 * lemmas etc. is put here.
	 */
#ifdef FBPDR
	bool firstRun = true;
	void takeExecutionOrig()
	{
		//woken up

#ifdef FBPDR_USE_PO_INTERSECTION_SEMANTIC
		/* rebuild init-solver with included reachable states from Rev. PDR */
		model.rebuildInitsWithPo(posOther, revpdr);
#endif

		asleep = false;
		//check for all cubes if they are bad (premise: the reverted counterpart
		//has already found reachable states)
#if defined(FBPDR_USE_PO_INTERSECTION) || defined(FBPDR_USE_PO_INTERSECTION_SEMANTIC)
		checkForBadCubes();
#endif

#ifdef FBPDR_USE_LEMMA_SHARING
		if (!firstRun)
		{
			extendTrace();
			strengthenTraceByCounterpartLemmas();
		}
#endif
		//TODO
		firstRun = false;
	}
	void takeExecutionRev()
	{
		//woken up
		asleep = false;

#ifdef FBPDR_USE_PO_INTERSECTION_SEMANTIC
		/* rebuild init-solver with included backward-reachable states from PDR */
		model.rebuildInitsWithPo(posOther, revpdr);
#endif
		//check for all cubes if they are bad (premise: the reverted counterpart
		//has already found reachable states)
#if defined(FBPDR_USE_PO_INTERSECTION) || defined(FBPDR_USE_PO_INTERSECTION_SEMANTIC)
		checkForBadCubes();
#endif

#ifdef FBPDR_USE_LEMMA_SHARING
		if (!firstRun)
		{
			extendTrace();
			strengthenTraceByCounterpartLemmas();
		}
#endif
		//TODO
		firstRun = false;
	}
#endif

	/*
	 * Controls switching PDR variants after a particular amount of time.
	 * One thread is put to sleep while the other is awake.
	 * -> "single-threaded" algorithm
	 */
#ifdef FBPDR
	clock_t lastSleep = 0;
	int idleTime = 30;
	bool asleep = false;
	bool idleState()
	{
		//terminate this thread when kill-signal is active
		if (thHandle->kill == KILL_CURRENT_THREAD)
			return true;

		//thread yields execution after a fixed period of time (idleTime seconds)
		if (lastSleep == 0)
			lastSleep = clock();
		int currentExecTime = (((float) (clock() - lastSleep)) / CLOCKS_PER_SEC);
		if (currentExecTime > idleTime)
		{
			if (verbose > 1)
				cout << "yield after: " << currentExecTime << " s" << endl;
			yieldExecution();
			//TODO: what if current variant excessively exceeded its time share?
		}

		//this part is only relevant if a thread wakes up
		if (!revpdr)
		{
			while (thHandle->awake == REV_PDR_HANDLE
					&& thHandle->kill == NO_KILL)
			{
				std::this_thread::sleep_for(std::chrono::milliseconds(100));
				lastSleep = clock();
				asleep = true;
			}
			//original PDR wakes up
			if (asleep)
			{
				takeExecutionOrig();
			}
		}
		else
		{
			while (thHandle->awake == ORIG_PDR_HANDLE
					&& thHandle->kill == NO_KILL)
			{
				std::this_thread::sleep_for(std::chrono::milliseconds(100));
				lastSleep = clock();
				asleep = true;
			}
			//Reverse PDR wakes up
			if (asleep)
			{
				takeExecutionRev();
			}
		}
		return false;
	}
#endif

#ifdef FBPDR_USE_LEMMA_SHARING
	bool loadCounterpartLemmas(Minisat::Solver &slv, size_t frame = 1)
	{
		//dual counterpart of var -> var + maxVar()
		model.initDualRailSolver(slv);
		//dual-rail encoding!
		// var = 1 (var = 1, dual_var = 0)
		// var = 0 (var = 0, dual_var = 1)
		// var = X (var = 0, dual_var = 0)
		if (getSafeDepthOther() == 0)
			return false;
		for (auto i = getSafeDepthOther() - frame; i < framesOther->size(); ++i)
		{
			for (auto &cube : (*framesOther)[i].borderCubes)
			{
				Minisat::vec<Minisat::Lit> cl;
				for (auto lit : cube)
				{
					Minisat::Lit pushLit;
					if (Minisat::sign(lit))
						pushLit = Minisat::mkLit(
								model.getDualVar(Minisat::var(lit)), false);
					else
						pushLit = lit;

					cl.push(pushLit);
				}
				assert(cl.size() > 0);
				slv.addClause_(cl);
				assert(slv.okay());
				assert(slv.nClauses() > 0 || slv.nAssigns() > 0);
			}
		}

		return true;
	}

	/*
	 * extracts subcube from CNF and adds blocking
	 * clause accordingly in slv
	 * */
	LitVec extractAndBlockMinimalSubcube(Minisat::Solver &slv)
	{
		LitVec subcube;
		//use a dual-rail encoding to acquire minimal subcubes efficiently

		bool rv = slv.solve();
		if (!rv)
			return LitVec(); // no more subcubes to extract

		//extract subcube: all latches without dont't care valuation
		for (VarVec::const_iterator i = model.beginLatches();
				i != model.endLatches(); ++i)
		{
			Minisat::lbool val = slv.modelValue(i->var());
			Minisat::lbool dualVal = slv.modelValue(model.getDualVar(i->var()));

			if (val != Minisat::l_Undef)
			{
				if (val != Minisat::l_False || dualVal != Minisat::l_False) // (0,0) don't care, (1,1) forbidden
				{
					Minisat::Lit la = i->lit(val == Minisat::l_False);
					subcube.push_back(~la);
				}
				else
					assert(
							val == Minisat::l_False
									&& dualVal == Minisat::l_False);
			}
		}

		//add blocking clause
		Minisat::vec<Minisat::Lit> blockingClause;
		for (auto &lit : subcube) //caution: subcube is already negated (technically a clause, but really a cube - duality of the problem!)
		{
			blockingClause.push(lit);
		}
		slv.addClause(blockingClause);

		return subcube;
	}

	void strengthenTraceByCounterpartLemmasFrOne()
	{
		//early out
		if (!numUpdates)
			return;

		LitVec subcube;
		int clLimitDivisor = 1;
		int clSizeLimitDivisor = 20;
		int currentClSize = 0;
		int nClauses = 0;
		auto nLatches = model.endLatches() - model.beginLatches();
		Minisat::Solver *slv = model.newSolver();
		if (loadCounterpartLemmas(*slv))
		{
			while (true)
			{
				subcube = extractAndBlockMinimalSubcube(*slv);
				currentClSize = (int) subcube.size();
				if (!subcube.empty() && currentClSize <= (numLits / numUpdates) // nLatches / clSizeLimitDivisor
						&& nClauses
								< ((slv->nClauses() + slv->nAssigns())
										/ clLimitDivisor)
						&& initiation(subcube))
				{
					if(!isBlocked(subcube, 1))
					{
						//assert(consecution(0, subcube));
						addCube(1, subcube); //first try: just block in frame 1
						cout << "strengthen with clause of size " << currentClSize
								<< endl;
						nClauses++;
					}
				}
				else
					break;
			}

			//cout << "strengthened with " << nClauses << " clauses." << endl;
			//try to propagate further
			propagate(false);
		}
		else
		{
			cout << "nothing strengthened -- counterpart trace to short"
					<< endl;
		}
		delete slv;
	}

	int highestStrengthenedFrame = 0;
	void strengthenTraceByCounterpartLemmas()
	{
		//early out
		if (!numUpdates)
			return;

		LitVec subcube;
		int clLimitDivisor = 1;
		int clSizeLimitDivisor = 20;
		int currentClSize = 0;
		int nClauses = 0;
		auto nLatches = model.endLatches() - model.beginLatches();
		for(auto frame = 1; frame < getSafeDepthOther(); ++frame)
		{
			Minisat::Solver *slv = model.newSolver();
			if (loadCounterpartLemmas(*slv, frame))
			{
				while (true)
				{
					subcube = extractAndBlockMinimalSubcube(*slv);
					currentClSize = (int) subcube.size();
					if (!subcube.empty() && currentClSize <= (numLits / numUpdates) // nLatches / clSizeLimitDivisor
							&& nClauses
									< ((slv->nClauses() + slv->nAssigns())
											/ clLimitDivisor)
							&& initiation(subcube))
					{
						if(!isBlocked(subcube, frame))
						{
							//assert(consecution(0, subcube));
							addCube(frame, subcube); //first try: just block in frame 1
							cout << "strengthen with clause of size " << currentClSize
									<< endl;
							nClauses++;
						}
					}
					else
						break;
				}

				//cout << "strengthened with " << nClauses << " clauses." << endl;
				if(nClauses > 0 && frame > highestStrengthenedFrame)
					highestStrengthenedFrame = frame;
			}
			else
			{
				cout << "nothing strengthened -- counterpart trace to short"
						<< endl;
			}
			delete slv;
		}

		//try to propagate further
		propagate(false);
	}

	bool latelyExtended = false;
	void extendTrace()
	{
		//if other variant progressed quicker - keep up
		if( (k-1) < getSafeDepthOther())
		{
			cout << "trace extended by " << (getSafeDepthOther() + 1 - k) << endl;
			k = getSafeDepthOther() + 1;
			extend();
			latelyExtended = true;
		}
	}

	void removeDischargedPos(PriorityQueue& obls)
	{
		if(latelyExtended)
		{
			size_t i = 0;
			//remove all trivially discharged POs -
			//if they represent a CEX candidate shorter than
			//the safe portion of the trace of the other variant
			//we can consider them discharged.
			auto oblIt = obls.begin();
			while(oblIt != obls.end())
			{
				if(oblIt->level + oblIt->depth < getSafeDepthOther())
			    {
					oblIt = obls.erase(oblIt);
					//cout << "po removed" << endl;
			    }
			    else
			    {
			        ++oblIt;
			    }
			}

			latelyExtended = false;
		}
	}
#endif

	bool isBlocked(const LitVec& cube, const size_t frame)
	{
		MSLitVec assumps;
		prepareConsecAssumps(assumps, frame, true);
		for( auto & lit: cube)
			assumps.push(lit);
		bool rv = consecSolver->solve(assumps);
		// c & R_frame -> SAT, not entirely blocked / UNSAT entirely blocked resp. subsumed
		bool isBlocked = !rv;
		return isBlocked;
	}


	void printAbsoluteValuesOfState(const LitVec &inps, std::string& witness)
	{
		for (const auto &lit : inps)
			witness.append(to_string( (int) (!Minisat::sign(lit)) )); //input vectors are always full assignments
		witness.append("\n");
	}

	void printInitialStateWithDontCares(std::string& witness)
	{
		size_t initIdx = 0;
		//Premise: lats is sorted by variable index
		LitVec init = model.getInitLits();
		for (VarVec::const_iterator it = model.beginLatches();
				it != model.endLatches(); ++it)
		{
			if (initIdx >= init.size()
					|| it->var() < Minisat::var(init[initIdx]))
			{
          		witness.append("x"); //not included in lats -> don't care
			}
			else
			{
				assert(initIdx < init.size());
          		witness.append(std::to_string((int) (!Minisat::sign(init[initIdx]))));		
				initIdx++;
			}
		}
      	witness.append("\n");
	}
	// Follows and prints chain of states from cexState forward.
	void printWitnessOrigPDR()
	{
		if (cexState != 0)
		{
			std::string witness = "1\n";
			witness.append("b0\n"); //TODO: only single property ...
			//print initial state (including don't care values)
			printInitialStateWithDontCares(witness);
			size_t curr = cexState;
			while (curr)
			{
				assert(
					state(curr).inputs.size()
						== (model.endInputs() - model.beginInputs()));
				printAbsoluteValuesOfState(state(curr).inputs, witness);
				curr = state(curr).successor;
			}
			//print last input - not contained in po-chain
			for (const auto &lit : currBadInput)
				witness.append(to_string((int) (!Minisat::sign(lit))));
			witness.append("\n");
			assert(currBadInput.size() > 0);

			witness.append(".\n"); //end of witness

			ofstream witness_file;
			witness_file.open("counterexample");
			witness_file << witness;
			witness_file.close();
		}
	}

	// Follows and prints chain of states from cexState forward.
	void printWitnessRevPDR()
	{
		if (cexState != 0)
		{
			std::string witness = "1\n";
			std::string revWitness = "";
			witness.append("b0\n"); //TODO: only single property ...
			//print initial state (including don't care values)
			printInitialStateWithDontCares(witness);
			size_t curr = cexState;
			while (curr)
			{
				assert(
					state(curr).inputs.size()
						== (model.endInputs() - model.beginInputs()));
				printAbsoluteValuesOfState(state(curr).inputs, revWitness);
				curr = state(curr).successor;
			}
			//Hack: rev PDR witness is reversed
			istringstream f(revWitness);
			string line;
			vector<string> lines;    
			while (std::getline(f, line)) {
				lines.push_back(line);
			}
			for(vector<string>::const_reverse_iterator it = lines.rbegin(); it != lines.rend(); ++it)
			{
				witness.append(*it);
				witness.append("\n");
			}
			for (auto &lit : currBadInput)
				witness.append(to_string((int) (!Minisat::sign(lit))));
			witness.append("\n");
			assert(currBadInput.size() > 0);

			witness.append(".\n"); //end of witness

			ofstream witness_file;
			witness_file.open("counterexample");
			witness_file << witness;
			witness_file.close();
		}
	}

	int nQuery, nCTI, nCTG, nmic;
	//float poReduction, nPoReductions, nSuccessPoRed;
	clock_t startTime, satTime, poRedTime, isInitTime;
	int nCoreReduced, nAbortJoin, nAbortMic;
	clock_t time()
	{
		struct tms t;
		times(&t);
		return t.tms_utime;
	}
	clock_t timer;
	void startTimer()
	{
		timer = time();
	}
	void endTimer(clock_t &t)
	{
		t += (time() - timer);
	}
};

// IC3 does not check for 0-step and 1-step reachability, so do it
// separately.
static bool baseCases(Model &model)
{
	Minisat::Solver *base0 = model.newSolver();
	model.loadInitialCondition(*base0);
	model.loadError(*base0);
	bool rv = base0->solve(model.error());
	delete base0;
	if (rv)
		return false;

	Minisat::Solver *base1 = model.newSolver();
	model.loadInitialCondition(*base1);
	model.loadTransitionRelation(*base1);
	rv = base1->solve(model.primedError());
	delete base1;
	if (rv)
		return false;

	model.lockPrimes();

	return true;
}

}
