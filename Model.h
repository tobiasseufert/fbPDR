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

#ifndef MODEL_H_INCLUDED
#define MODEL_H_INCLUDED

#include <algorithm>
#include <set>
#include <sstream>
#include <unordered_map>
#include <vector>
#include <bitset>
#include <queue>
#include <chrono>
#include <thread>

extern "C"
{
#include "aiger.h"
}
#include "Solver.h"
#include "SimpSolver.h"
#include "Config.h"


// Read it and weep: yes, it's in a header file; no, I don't want to
// have std:: all over the place.
using namespace std;

// A row of the AIGER spec: lhs = rhs0 & rhs1.
struct AigRow
{
	AigRow(Minisat::Lit _lhs, Minisat::Lit _rhs0, Minisat::Lit _rhs1) :
			lhs(_lhs), rhs0(_rhs0), rhs1(_rhs1)
	{
	}
	Minisat::Lit lhs, rhs0, rhs1;
};
// Intended to hold the AND section of an AIGER spec.
typedef vector<AigRow> AigVec;

#if defined(FBPDR_USE_PO_INTERSECTION) || defined(FBPDR_USE_PO_INTERSECTION_SEMANTIC)
struct LitVec
{
	std::vector<Minisat::Lit> literals;
	bool bad;

	//default constructor
	LitVec() : literals(vector<Minisat::Lit>()), bad(false){}
	LitVec(vector<Minisat::Lit>::const_iterator it1, vector<Minisat::Lit>::const_iterator it2) :
		bad(false), literals(std::vector<Minisat::Lit>(it1, it2))
	{	}

	//copy constructor.
	LitVec(const LitVec& c) : literals(c.literals) , bad(c.bad){}

	//copy assignment
	LitVec& operator=(const LitVec& c)
	{
		this->literals = c.literals;
		this->bad = c.bad;
		return *this;
	}

	typedef std::vector<Minisat::Lit>::iterator it;
	typedef std::vector<Minisat::Lit>::const_iterator cit;
	/* inserts range of elements at it */
	void insert(it position, it rangebegin, it rangeend)
	{
		literals.insert(position, rangebegin, rangeend);
	}

	/**  Returns amount of literals the cube holds. */
	size_t size() const { return literals.size(); }

	/**  Removes all elements from the container literals, leaving it with a size of zero. */
	void clear() noexcept { literals.clear(); bad = false; }

	/**  Returns whether the container literals size is zero. */
	bool empty() const noexcept { return literals.empty(); }

	/**  Return an iterator pointing to the first (past-the-end) element in the literals container. */
	it begin() { return literals.begin(); }
	it end() { return literals.end(); }
	cit begin() const { return literals.begin(); }
	cit end() const { return literals.end(); }

	/** Returns a reference to the element at position i in the literals container. */
	Minisat::Lit& operator [] (int i) { return literals[i]; }
	Minisat::Lit operator [] (int i) const { return literals[i]; }

	/**  Remove from the literals container either a single element (position) or a range of elements ([first,last)). */
	it erase (cit position) { return literals.erase(position); };
	it erase (cit first, cit last) { return literals.erase(first, last); };

	/**  Add a new element at the end of the literals, after its current last element. */
	void push_back (const Minisat::Lit& val) { literals.push_back(val); };
	void push_back (Minisat::Lit&& val) { literals.push_back(val); };

	/**  Exchange the content of the literals by the content of c.literals. */
	void swap (LitVec& c) { literals.swap(c.literals); bad = c.bad; }
	void swap (std::vector<Minisat::Lit>& c) { literals.swap(c); }

	Minisat::Lit& back() { return literals.back(); }
	const Minisat::Lit& back() const { return literals.back(); }

	void pop_back() { return literals.pop_back(); }

	/**  Cube comparison operators. */
    bool operator == (LitVec& c) const { return (literals == c.literals && bad == c.bad); }
    bool operator != (LitVec& c) const { return (literals != c.literals || bad != c.bad); }

};
#else
typedef vector<Minisat::Lit> LitVec;
#endif

// A lightweight wrapper around Minisat::Var that includes a name.
class Var
{
public:
	Var(const string name)
	{
		_var = gvi++;
		_name = name;
	}
	size_t index() const
	{
		return (size_t) _var;
	}
	Minisat::Var var() const
	{
		return _var;
	}
	Minisat::Lit lit(bool neg) const
	{
		return Minisat::mkLit(_var, neg);
	}
	string name() const
	{
		return _name;
	}
private:
	static Minisat::Var gvi;  // aligned with solvers
	Minisat::Var _var;        // corresponding Minisat::Var in *any* solver
	string _name;
};

typedef vector<Var> VarVec;

class VarComp
{
public:
	bool operator()(const Var &v1, const Var &v2) const
	{
		return v1.index() < v2.index();
	}
};
typedef set<Var, VarComp> VarSet;
typedef set<Minisat::Lit> LitSet;

#if defined(FBPDR_USE_PO_INTERSECTION) || defined(FBPDR_USE_PO_INTERSECTION_SEMANTIC)
// A proof obligation with a concrete state
struct FullObligation
{
	FullObligation(LitVec st, size_t l, size_t d) :
		lats(st), level(l), depth(d)
	{
	}
	LitVec lats;  // Generalize this state...
	size_t level;  // ... relative to this level.
	size_t depth;  // Length of CTI suffix to error.
};
// Prefer deeper proof obligations from reverted counterpart
class RevObligationComp
{
public:
	bool operator()(const FullObligation &o1, const FullObligation &o2) const
	{
		if (o1.depth > o2.depth)
			return true;  // prefer deeper (heuristic)
		if (o1.depth < o2.depth)
			return false;
		if (o1.lats.size() < o2.lats.size())
				return true;
		if (o1.lats.size() > o2.lats.size())
			return false;
		for (size_t i = 0; i < o1.lats.size(); ++i)
		{
			if (o1.lats[i] < o2.lats[i])
				return true;
			if (o2.lats[i] < o1.lats[i])
				return false;
		} // canonical final decider
		return false;
	}
};
//prefer shorter pos
class SFObligationComp
{
public:
	bool operator()(const FullObligation &o1, const FullObligation &o2) const
	{
		if (o1.lats.size() < o2.lats.size())
			return true;
		if (o1.lats.size() > o2.lats.size())
			return false;
		if (o1.depth > o2.depth)
			return true;  // prefer deeper (heuristic)
		if (o1.depth < o2.depth)
			return false;
		for (size_t i = 0; i < o1.lats.size(); ++i)
		{
			if (o1.lats[i] < o2.lats[i])
				return true;
			if (o2.lats[i] < o1.lats[i])
				return false;
		} // canonical final decider
		return false;
	}
};
#ifdef DEEPER_PO_FIRST
typedef set<FullObligation, RevObligationComp> DeeperPoFirst;
#endif
#ifdef SHORTER_PO_FIRST
typedef set<FullObligation, SFObligationComp> DeeperPoFirst;
#endif
#endif

/*** ternary bool ***/
//lookup table for 0/1/x
const std::vector<std::vector<uint8_t>> andTab
{
{ 0, 0, 0 },
{ 0, 1, 2 },
{ 0, 2, 2 } };
const std::vector<std::vector<uint8_t>> orTab
{
{ 0, 1, 2 },
{ 1, 1, 1 },
{ 2, 1, 2 } };
const std::vector<uint8_t> notTab
{ 1, 0, 2 };
//ternary bool {0=false,1=true,2=dont care}
struct ternBool
{
	uint8_t value;

	ternBool()
	{
	}
	ternBool(uint8_t value) :
			value(value)
	{
		assert(value <= 2);
	}

	bool operator ==(ternBool b) const
	{
		return (b.value == value);
	}
	bool operator !=(ternBool b) const
	{
		return (b.value != value);
	}

	ternBool operator &&(ternBool b)
	{
		return ternBool(andTab[this->value][b.value]);
	}

	ternBool operator ||(ternBool b)
	{
		return ternBool(orTab[this->value][b.value]);
	}

	ternBool operator !()
	{
		return ternBool(notTab[this->value]);
	}
};
/*** ternary bool ***/
const size_t ternsimBitWidth = 64;
const int gBitwidth = 20;
typedef std::vector<std::bitset<gBitwidth>> PatternFix;

// A simple wrapper around an AIGER-specified invariance benchmark.
// It specifically disallows primed variables beyond those required to
// express the (property-constrained) transition relation and the
// primed error constraint.  Variables are kept aligned with the
// variables of any solver created through newSolver().
class Model
{
public:
	// Construct a model from a vector of variables, indices indicating
	// divisions between variable types, constraints, next-state
	// functions, the error, and the AND table, closely reflecting the
	// AIGER format.  Easier to use "modelFromAiger()", below.
	Model(vector<Var> _vars, size_t _inputs, size_t _latches, size_t _reps,
			LitVec _init, LitVec _constraints, LitVec _nextStateFns,
			Minisat::Lit _err, AigVec _aig) :
			vars(_vars), inputs(_inputs), latches(_latches), reps(_reps), primes(
					_vars.size()), primesUnlocked(true), aig(_aig), init(_init), constraints(
					_constraints), nextStateFns(_nextStateFns), _error(_err), inits(
			NULL), sslv(NULL), sslvConsec(NULL), sslvError(NULL), transActLit(Minisat::mkLit(0,false))
	{
		// create primed inputs and latches in known region of vars
		for (size_t i = inputs; i < reps; ++i)
		{
			stringstream ss;
			ss << vars[i].name() << "'";
			vars.push_back(Var(ss.str()));
		}
		// same with primed error
		_primedError = primeLit(_error);
		// same with primed constraints
		for (vector<Minisat::Lit>::const_iterator i = constraints.begin();
				i != constraints.end(); ++i)
			primeLit(*i);

		/* revPDR po gen */
		transitionSupport.resize(endLatches()->var() - beginLatches()->var());
		circuitNodeSuccessors.resize(getMaxVar() + 1);
		outDegrSuppVars.resize(endLatches()->var(), 0);

	}
	~Model();

	// Returns the Var of the given Minisat::Lit.
	const Var& varOfLit(Minisat::Lit lit) const
	{
		Minisat::Var v = Minisat::var(lit);
		assert((unsigned ) v < vars.size());
		return vars[v];
	}

	// Returns the name of the Minisat::Lit.
	string stringOfLit(Minisat::Lit lit) const
	{
		stringstream ss;
		if (Minisat::sign(lit))
			ss << "~";
		ss << varOfLit(lit).name();
		return ss.str();
	}

	// Returns the primed Var/Minisat::Lit for the given
	// Var/Minisat::Lit.  Once lockPrimes() is called, primeVar() fails
	// (with an assertion violation) if it is asked to create a new
	// variable.
	const Var& primeVar(const Var &v, Minisat::SimpSolver *slv = NULL);
	Minisat::Lit primeLit(Minisat::Lit lit, Minisat::SimpSolver *slv = NULL)
	{
		const Var &pv = primeVar(varOfLit(lit), slv);
		return pv.lit(Minisat::sign(lit));
	}
	Minisat::Var unprimeVar(Minisat::Var var)
	{
		size_t i = (size_t) var;
		if (i >= primes && i < primes + reps - inputs)
			return (Minisat::Var) (i - primes + inputs);
		else
			return var;
	}
	Minisat::Lit unprimeLit(Minisat::Lit lit)
	{
		size_t i = (size_t) var(lit);
		if (i >= primes && i < primes + reps - inputs)
			return Minisat::mkLit((Minisat::Var) (i - primes + inputs),
					sign(lit));
		else
			return lit;
	}

	// Once all primed variables have been created, it locks the Model
	// from creating any further ones.  Then Solver::newVar() may be
	// called safely.
	//
	// WARNING: Do not call Solver::newVar() until lockPrimes() has been
	// called.
	void lockPrimes()
	{
		primesUnlocked = false;
	}

	// Minisat::Lits corresponding to true/false.
	Minisat::Lit btrue() const
	{
		return Minisat::mkLit(vars[0].var(), true);
	}
	Minisat::Lit bfalse() const
	{
		return Minisat::mkLit(vars[0].var(), false);
	}

	// Primary inputs.
	VarVec::const_iterator beginInputs() const
	{
		return vars.begin() + inputs;
	}
	VarVec::const_iterator endInputs() const
	{
		return vars.begin() + latches;
	}

	// Latches.
	VarVec::const_iterator beginLatches() const
	{
		return vars.begin() + latches;
	}
	VarVec::const_iterator endLatches() const
	{
		return vars.begin() + reps;
	}

	// Ands.
	AigVec::const_iterator beginAnds() const
	{
		return aig.begin();
	}
	AigVec::const_iterator endAnds() const
	{
		return aig.end();
	}

	bool isLatch(Minisat::Var v) const
	{
		return (v >= latches && v < reps);
	}
	bool isInput(Minisat::Var v) const
	{
		return (v >= inputs && v < latches);
	}
	bool isAnd(Minisat::Var v) const
	{
		return (v >= reps && v < primes);
	}
	bool isPrimed(Minisat::Var v) const
	{
		return (v >= primes && v < primes + reps - inputs);
	}

	// Next-state function for given latch.
	Minisat::Lit nextStateFn(const Var &latch) const
	{
		assert(latch.index() >= latches && latch.index() < reps);
		return nextStateFns[latch.index() - latches];
	}

	// Error and its primed form.
	Minisat::Lit error() const
	{
		return _error;
	}
	Minisat::Lit primedError() const
	{
		return _primedError;
	}

	// Invariant constraints
	const LitVec& invariantConstraints()
	{
		return constraints;
	}

	Minisat::SimpSolver* getTransSslv() const
	{
		return sslv;
	}
	Minisat::SimpSolver* getErrorSslv() const
	{
		return sslvError;
	}
	// Creates a Solver and initializes its variables to maintain
	// alignment with the Model's variables.
	Minisat::Solver* newSolver() const;

	//loads dual rail encoding (another vars.size() amount of variables)
	void initDualRailSolver(Minisat::Solver &slv) const;
	Minisat::Var getDualVar(const Minisat::Var &v) const
	{
		assert(v > 0);
		assert(v < vars.size());
		return (vars[v].var() + vars.size());
	}

	// Loads the TR into the solver.  Also loads the primed error
	// definition such that Model::primedError() need only be asserted
	// to activate it.  Invariant constraints (AIGER 1.9) and the
	// negation of the error are always added --- except that the primed
	// form of the invariant constraints are not asserted if
	// !primeConstraints.
	void loadTransitionRelation(Minisat::Solver &slv, bool primeConstraints =
			true, bool addConstraints = true);
	//trans with activation literal
	void loadTransitionRelationConsec(Minisat::Solver &slv);
	Minisat::Lit getTransActLit() { assert(Minisat::toInt(transActLit) != 0); return transActLit; }

	// Loads the initial condition into the solver.
	void loadInitialCondition(Minisat::Solver &slv, Minisat::Lit actLit =
			Minisat::mkLit(0, false)) const;

#ifdef FBPDR_USE_PO_INTERSECTION_SEMANTIC
	void loadReachableStates(Minisat::Solver &slv, const DeeperPoFirst* posOther, bool revpdr);
	void rebuildInitsWithPo(const DeeperPoFirst* posOther, bool revpdr);
#endif

	// Loads the error into the solver, which is only necessary for the
	// 0-step base case of IC3.
	void loadError(Minisat::Solver &slv);

	// Use this method to allow the Model to decide how best to decide
	// if a cube has an initial state.
	bool isInitial(const LitVec &latches, bool reverse);
	// ... repair if cube is generalized too much
	void ungenInitCube(LitVec &genCube, const LitVec &originalCube,
			bool revpdr = false);

	LitVec getInitLits();
	size_t getMaxVar() const;
	size_t getAigMaxVar() const;
	/*Rev PDR po generalization */
	std::vector<unsigned int>& getTransitionSupport(Var v);
	//only propagation, no correct constant checking
	std::set<unsigned int> circuitTrav(std::vector<ternBool> &valuation,
			unsigned int stateVar);
	void circuitPropagation(std::vector<ternBool> &valuation,
			std::set<unsigned int> &constants);
	//plain simulation of circuit with random patterns
	//returns bit (vector) for each next state function
	PatternFix simFixRndPatterns(LitVec &presentState); //uses std::bitset with constant bitwidth -> more efficient

	//stores out degree of support nodes (inputs, latches)
	//out degree of i -> node supports i transition functions
	std::vector<unsigned int> outDegrSuppVars;
	//stores support variables ordered by their number of occurrence in transition functions
	std::vector<unsigned int> suppByNumOfOcc;

private:
	VarVec vars;
	const size_t inputs, latches, reps, primes;

	bool primesUnlocked;
	typedef unordered_map<size_t, size_t> IndexMap;
	IndexMap primedAnds;

	const AigVec aig;
	const LitVec init, constraints, nextStateFns;
	const Minisat::Lit _error;
	Minisat::Lit _primedError;

	Minisat::Lit transActLit;

	Minisat::Solver *inits;
	LitSet initLits;

	Minisat::SimpSolver *sslv;
	Minisat::SimpSolver *sslvConsec;
	Minisat::SimpSolver *sslvError;

	//stores for each variable (node/latch/input) its successors in latch transition function
	std::vector<std::set<unsigned int>> circuitNodeSuccessors;
	bool circuitNodeSuccessorsActive = false;
	//stores support (input/latch variables) of transition function for each latch
	std::vector<std::vector<unsigned int>> transitionSupport;
};

// The easiest way to create a model.
Model* modelFromAiger(aiger *aig, unsigned int propertyIndex);

#endif
