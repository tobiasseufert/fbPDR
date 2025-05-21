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

#include <iostream>

#include "Model.h"
#include "SimpSolver.h"
#include "Vec.h"

Minisat::Var Var::gvi = 0;

Model::~Model()
{
	if (inits)
		delete inits;
	if (sslv)
		delete sslv;
	if (sslvError)
		delete sslvError;
}

const Var& Model::primeVar(const Var &v, Minisat::SimpSolver *slv)
{
	// var for false
	if (v.index() == 0)
		return v;
	// latch or PI
	if (v.index() < reps)
		return vars[primes + v.index() - inputs];
	// AND lit
	assert(v.index() >= reps && v.index() < primes);
	// created previously?
	IndexMap::const_iterator i = primedAnds.find(v.index());
	size_t index;
	if (i == primedAnds.end())
	{
		// no, so make sure the model hasn't been locked
		assert(primesUnlocked);
		// create a primed version
		stringstream ss;
		ss << v.name() << "'";
		index = vars.size();
		vars.push_back(Var(ss.str()));
		if (slv)
		{
			Minisat::Var _v = slv->newVar();
			assert(_v == vars.back().var());
		}
		assert(vars.back().index() == index);
		primedAnds.insert(IndexMap::value_type(v.index(), index));
	}
	else
		index = i->second;
	return vars[index];
}

Minisat::Solver* Model::newSolver() const
{
	Minisat::Solver *slv = new Minisat::Solver();
	// load all variables to maintain alignment
	for (size_t i = 0; i < vars.size(); ++i)
	{
		Minisat::Var nv = slv->newVar();
		assert(nv == vars[i].var());
	}
	return slv;
}

void Model::initDualRailSolver(Minisat::Solver &slv) const
{
	// load all dual variables
	for (size_t i = 0; i < vars.size(); ++i)
	{
		slv.newVar(); //before (1,1) forbidding clause! -> variables aligned
		if(i > 0)
		{
			Minisat::Lit lit = Minisat::mkLit(i, true);
			Minisat::Lit auxLit = Minisat::mkLit(getDualVar(i), true);
			slv.addClause(lit, auxLit);
		}
	}
}


void Model::loadTransitionRelation(Minisat::Solver &slv, bool primeConstraints, bool addConstraints)
{
	if (!sslv)
	{
		// create a simplified CNF version of (this slice of) the TR
		sslv = new Minisat::SimpSolver();
		// introduce all variables to maintain alignment
		for (size_t i = 0; i < vars.size(); ++i)
		{
			Minisat::Var nv = sslv->newVar();
			assert(nv == vars[i].var());
		}
		// freeze inputs, latches, and special nodes (and primed forms)
		for (VarVec::const_iterator i = beginInputs(); i != endInputs(); ++i)
		{
			sslv->setFrozen(i->var(), true);
			sslv->setFrozen(primeVar(*i).var(), true);
		}
		for (VarVec::const_iterator i = beginLatches(); i != endLatches(); ++i)
		{
			sslv->setFrozen(i->var(), true);
			sslv->setFrozen(primeVar(*i).var(), true);
		}
		sslv->setFrozen(varOfLit(error()).var(), true);
		sslv->setFrozen(varOfLit(primedError()).var(), true);
		for (vector<Minisat::Lit>::const_iterator i = constraints.begin();
				i != constraints.end(); ++i)
		{
			Var v = varOfLit(*i);
			sslv->setFrozen(v.var(), true);
			sslv->setFrozen(primeVar(v).var(), true);
		}
		// initialize with roots of required formulas
		LitSet require;  // unprimed formulas
		for (VarVec::const_iterator i = beginLatches(); i != endLatches(); ++i)
			require.insert(nextStateFn(*i));
		require.insert(_error);
		if(addConstraints)
			require.insert(constraints.begin(), constraints.end());
		LitSet prequire; // for primed formulas; always subset of require
		prequire.insert(_error);
		if(addConstraints)
			prequire.insert(constraints.begin(), constraints.end());
		// traverse AIG backward
		for (AigVec::const_reverse_iterator i = aig.rbegin(); i != aig.rend();
				++i)
		{
			// skip if this row is not required
			if (require.find(i->lhs) == require.end()
					&& require.find(~i->lhs) == require.end())
				continue;
			// encode into CNF
			sslv->addClause(~i->lhs, i->rhs0);
			sslv->addClause(~i->lhs, i->rhs1);
			sslv->addClause(~i->rhs0, ~i->rhs1, i->lhs);
			// require arguments
			require.insert(i->rhs0);
			require.insert(i->rhs1);
			// primed: skip if not required
			if (prequire.find(i->lhs) == prequire.end()
					&& prequire.find(~i->lhs) == prequire.end())
				continue;
			// encode PRIMED form into CNF
			Minisat::Lit r0 = primeLit(i->lhs, sslv), r1 = primeLit(i->rhs0,
					sslv), r2 = primeLit(i->rhs1, sslv);
			sslv->addClause(~r0, r1);
			sslv->addClause(~r0, r2);
			sslv->addClause(~r1, ~r2, r0);
			// require arguments
			prequire.insert(i->rhs0);
			prequire.insert(i->rhs1);
		}
		// assert literal for true
		sslv->addClause(btrue());
		// assert ~error, constraints, and primed constraints
		sslv->addClause(~_error);
		if(addConstraints)
		{
			for (vector<Minisat::Lit>::const_iterator i = constraints.begin();
					i != constraints.end(); ++i)
			{
				sslv->addClause(*i);
			}
		}
		// assert l' = f for each latch l
		for (VarVec::const_iterator i = beginLatches(); i != endLatches(); ++i)
		{
			Minisat::Lit platch = primeLit(i->lit(false)), f = nextStateFn(*i);
			sslv->addClause(~platch, f);
			sslv->addClause(~f, platch);
		}
		sslv->eliminate(true);
	}
	// load the clauses from the simplified context
	assert(sslv->nVars() == vars.size());
	while (slv.nVars() < sslv->nVars())
		slv.newVar();
	for (Minisat::ClauseIterator c = sslv->clausesBegin();
			c != sslv->clausesEnd(); ++c)
	{
		const Minisat::Clause &cls = *c;
		Minisat::vec<Minisat::Lit> cls_;
		for (int i = 0; i < cls.size(); ++i)
			cls_.push(cls[i]);
		slv.addClause_(cls_);
	}
	for (Minisat::TrailIterator c = sslv->trailBegin(); c != sslv->trailEnd();
			++c)
		slv.addClause(*c);
	if (primeConstraints && addConstraints)
		for (vector<Minisat::Lit>::const_iterator i = constraints.begin();
				i != constraints.end(); ++i)
			slv.addClause(primeLit(*i));
}

void Model::loadTransitionRelationConsec(Minisat::Solver &slv)
{
	if (!sslvConsec)
	{
		// create a simplified CNF version of (this slice of) the TR
		sslv = new Minisat::SimpSolver();
		// introduce all variables to maintain alignment
		for (size_t i = 0; i < vars.size(); ++i)
		{
			Minisat::Var nv = sslv->newVar();
			assert(nv == vars[i].var());
		}
		// freeze inputs, latches, and special nodes (and primed forms)
		for (VarVec::const_iterator i = beginInputs(); i != endInputs(); ++i)
		{
			sslv->setFrozen(i->var(), true);
			sslv->setFrozen(primeVar(*i).var(), true);
		}
		for (VarVec::const_iterator i = beginLatches(); i != endLatches(); ++i)
		{
			sslv->setFrozen(i->var(), true);
			sslv->setFrozen(primeVar(*i).var(), true);
		}
		sslv->setFrozen(varOfLit(error()).var(), true);
		sslv->setFrozen(varOfLit(primedError()).var(), true);
		for (vector<Minisat::Lit>::const_iterator i = constraints.begin();
				i != constraints.end(); ++i)
		{
			Var v = varOfLit(*i);
			sslv->setFrozen(v.var(), true);
			sslv->setFrozen(primeVar(v).var(), true);
		}
		// initialize with roots of required formulas
		LitSet require;  // unprimed formulas
		for (VarVec::const_iterator i = beginLatches(); i != endLatches(); ++i)
			require.insert(nextStateFn(*i));
		require.insert(_error);
		require.insert(constraints.begin(), constraints.end());
		LitSet prequire; // for primed formulas; always subset of require
		prequire.insert(_error);
		prequire.insert(constraints.begin(), constraints.end());
		// traverse AIG backward
		for (AigVec::const_reverse_iterator i = aig.rbegin(); i != aig.rend();
				++i)
		{
			// skip if this row is not required
			if (require.find(i->lhs) == require.end()
					&& require.find(~i->lhs) == require.end())
				continue;
			// encode into CNF
			sslv->addClause(~i->lhs, i->rhs0);
			sslv->addClause(~i->lhs, i->rhs1);
			sslv->addClause(~i->rhs0, ~i->rhs1, i->lhs);
			// require arguments
			require.insert(i->rhs0);
			require.insert(i->rhs1);
			// primed: skip if not required
			if (prequire.find(i->lhs) == prequire.end()
					&& prequire.find(~i->lhs) == prequire.end())
				continue;
			// encode PRIMED form into CNF
			Minisat::Lit r0 = primeLit(i->lhs, sslv), r1 = primeLit(i->rhs0,
					sslv), r2 = primeLit(i->rhs1, sslv);
			sslv->addClause(~r0, r1);
			sslv->addClause(~r0, r2);
			sslv->addClause(~r1, ~r2, r0);
			// require arguments
			prequire.insert(i->rhs0);
			prequire.insert(i->rhs1);
		}
		// assert literal for true
		sslv->addClause(btrue());
		// assert ~error, constraints, and primed constraints
		sslv->addClause(~_error);
		for (vector<Minisat::Lit>::const_iterator i = constraints.begin();
				i != constraints.end(); ++i)
		{
			sslv->addClause(*i);
		}
		// assert l' = f for each latch l
		for (VarVec::const_iterator i = beginLatches(); i != endLatches(); ++i)
		{
			Minisat::Lit platch = primeLit(i->lit(false)), f = nextStateFn(*i);
			sslv->addClause(~platch, f);
			sslv->addClause(~f, platch);
		}
		sslv->eliminate(true);
	}
	// load the clauses from the simplified context
	assert(sslv->nVars() == vars.size());
	while (slv.nVars() < sslv->nVars())
		slv.newVar();
	transActLit = Minisat::mkLit(slv.newVar(), false);
	for (Minisat::ClauseIterator c = sslv->clausesBegin();
			c != sslv->clausesEnd(); ++c)
	{
		const Minisat::Clause &cls = *c;
		Minisat::vec<Minisat::Lit> cls_;
		for (int i = 0; i < cls.size(); ++i)
			cls_.push(cls[i]);
		cls_.push(~transActLit);
		slv.addClause_(cls_);
	}
	for (Minisat::TrailIterator c = sslv->trailBegin(); c != sslv->trailEnd();
			++c)
		slv.addClause(*c, ~transActLit);
	for (vector<Minisat::Lit>::const_iterator i = constraints.begin();
			i != constraints.end(); ++i)
		slv.addClause(primeLit(*i), ~transActLit);
}

void Model::loadInitialCondition(Minisat::Solver &slv, Minisat::Lit actLit) const
{
	slv.addClause(btrue());
	if(actLit.x == 0)
	{
		for (vector<Minisat::Lit>::const_iterator i = init.begin(); i != init.end(); ++i)
			slv.addClause(*i);
	}
	else
	{
		for (vector<Minisat::Lit>::const_iterator i = init.begin(); i != init.end(); ++i)
			slv.addClause(*i, ~actLit);
	}
	if (constraints.empty())
		return;
	// impose invariant constraints on initial states (AIGER 1.9)
	LitSet require;
	require.insert(constraints.begin(), constraints.end());
	for (AigVec::const_reverse_iterator i = aig.rbegin(); i != aig.rend(); ++i)
	{
		// skip if this (*i) is not required
		if (require.find(i->lhs) == require.end()
				&& require.find(~i->lhs) == require.end())
			continue;
		// encode into CNF
		if(actLit.x == 0)
		{
			slv.addClause(~i->lhs, i->rhs0);
			slv.addClause(~i->lhs, i->rhs1);
			slv.addClause(~i->rhs0, ~i->rhs1, i->lhs);
		}
		else
		{
			slv.addClause(~i->lhs, i->rhs0, ~actLit);
			slv.addClause(~i->lhs, i->rhs1, ~actLit);
			slv.addClause(~i->rhs0, ~i->rhs1, i->lhs, ~actLit);
		}
		// require arguments
		require.insert(i->rhs0);
		require.insert(i->rhs1);
	}
	if(actLit.x == 0)
	{
		for (vector<Minisat::Lit>::const_iterator i = constraints.begin(); i != constraints.end();
				++i)
		{
			slv.addClause(*i);
		}
	}
	else
	{
		for (vector<Minisat::Lit>::const_iterator i = constraints.begin(); i != constraints.end();
						++i)
		{
			slv.addClause(*i, ~actLit);
		}
	}
}

#ifdef FBPDR_USE_PO_INTERSECTION_SEMANTIC
void Model::loadReachableStates(Minisat::Solver &slv, const DeeperPoFirst* posOther, bool revpdr)
{
	slv.addClause(btrue());
	LitSet require;
	require.insert(constraints.begin(), constraints.end());
	Minisat::Var initAuxVar;
	Minisat::Lit initAuxLit;
	if(!revpdr)
	{
		initAuxVar = slv.newVar();
		initAuxLit = Minisat::mkLit(initAuxVar,false);
		for (vector<Minisat::Lit>::const_iterator i = init.begin(); i != init.end(); ++i)
		{
			Minisat::vec<Minisat::Lit> cl;
			cl.push(*i);
			cl.push(~initAuxLit);
			slv.addClause(cl);
		}
		for (AigVec::const_reverse_iterator i = aig.rbegin(); i != aig.rend(); ++i)
		{
			// skip if this (*i) is not required
			if (require.find(i->lhs) == require.end()
					&& require.find(~i->lhs) == require.end())
				continue;
			// encode into CNF
			slv.addClause(~i->lhs, i->rhs0);
			slv.addClause(~i->lhs, i->rhs1);
			slv.addClause(~i->rhs0, ~i->rhs1, i->lhs);
			// require arguments
			require.insert(i->rhs0);
			require.insert(i->rhs1);
		}
		for (vector<Minisat::Lit>::const_iterator i = constraints.begin(); i != constraints.end();
				++i)
		{
			slv.addClause(*i);
		}
	}
	else
	{
		slv.addClause(error());
		loadError(slv);
	}
	//add proof obligations from reverted counterpart
	Minisat::vec<Minisat::Lit> generalFullCl;
	if(posOther)
	{
		std::vector<Minisat::Lit> poAuxLits;
		for(auto& po: *posOther)
		{
			Minisat::Var poAuxVar = slv.newVar();
			Minisat::Lit poAuxLit = Minisat::mkLit(poAuxVar,false);
			poAuxLits.push_back(poAuxLit);
			for(auto& lit: po.lats)
			{
				Minisat::vec<Minisat::Lit> cl;
				cl.push(lit);
				cl.push(~poAuxLit);
				slv.addClause(cl);
			}
		}

		//Combining s_all <-> (s_init + s_po1 + s_po2 + ... )
		for(auto& poAuxLit: poAuxLits)
		{
			generalFullCl.push(poAuxLit);
		}
	}
	//init/unsafe lit
	if(revpdr)
		generalFullCl.push(error());
	else
		generalFullCl.push(initAuxLit);
	slv.addClause(generalFullCl);
}
#endif

#ifdef FBPDR_USE_PO_INTERSECTION_SEMANTIC
void Model::rebuildInitsWithPo(const DeeperPoFirst* posOther, bool revpdr)
{
	if(inits)
	{
		delete inits;
	}
	inits = newSolver();
	loadReachableStates(*inits, posOther, revpdr);
}
#endif

void Model::loadError(Minisat::Solver &slv)
{
	if (!sslvError)
	{
		// create a simplified CNF version of (this slice of) the TR
		sslvError = new Minisat::SimpSolver();
		// introduce all variables to maintain alignment
		for (size_t i = 0; i < vars.size(); ++i)
		{
			Minisat::Var nv = sslvError->newVar();
			assert(nv == vars[i].var());
		}
		// freeze inputs, latches, and special nodes (and primed forms)
		for (VarVec::const_iterator i = beginInputs(); i != endInputs(); ++i)
		{
			sslvError->setFrozen(i->var(), true);
		}
		for (VarVec::const_iterator i = beginLatches(); i != endLatches(); ++i)
		{
			sslvError->setFrozen(i->var(), true);
		}
		sslvError->setFrozen(varOfLit(error()).var(), true);
		sslvError->setFrozen(varOfLit(primedError()).var(), true);
		for (vector<Minisat::Lit>::const_iterator i = constraints.begin();
				i != constraints.end(); ++i)
		{
			Var v = varOfLit(*i);
			sslvError->setFrozen(v.var(), true);
		}
		// initialize with roots of required formulas
		LitSet require;  // unprimed formulas
		require.insert(_error);
		require.insert(constraints.begin(), constraints.end());
		// traverse AIG backward
		for (AigVec::const_reverse_iterator i = aig.rbegin(); i != aig.rend();
				++i)
		{
			// skip if this row is not required
			if (require.find(i->lhs) == require.end()
					&& require.find(~i->lhs) == require.end())
				continue;
			// encode into CNF
			sslvError->addClause(~i->lhs, i->rhs0);
			sslvError->addClause(~i->lhs, i->rhs1);
			sslvError->addClause(~i->rhs0, ~i->rhs1, i->lhs);
			// require arguments
			require.insert(i->rhs0);
			require.insert(i->rhs1);
		}
		// assert literal for true
		sslvError->addClause(btrue());
		for (vector<Minisat::Lit>::const_iterator i = constraints.begin();
				i != constraints.end(); ++i)
		{
			sslvError->addClause(*i);
		}
		sslvError->eliminate(true);
	}
	// load the clauses from the simplified context
	while (slv.nVars() < sslvError->nVars())
		slv.newVar();
	for (Minisat::ClauseIterator c = sslvError->clausesBegin();
			c != sslvError->clausesEnd(); ++c)
	{
		const Minisat::Clause &cls = *c;
		Minisat::vec<Minisat::Lit> cls_;
		for (int i = 0; i < cls.size(); ++i)
			cls_.push(cls[i]);
		slv.addClause_(cls_);
	}
	for (Minisat::TrailIterator c = sslvError->trailBegin();
			c != sslvError->trailEnd(); ++c)
		slv.addClause(*c);
}

bool Model::isInitial(const LitVec &latches, bool rev)
{
	if (!rev)
	{
#ifndef FBPDR_USE_PO_INTERSECTION_SEMANTIC
		if (constraints.empty())
		{
			// an intersection check (AIGER 1.9 w/o invariant constraints)
			if (initLits.empty())
				initLits.insert(init.begin(), init.end());
			for (vector<Minisat::Lit>::const_iterator i = latches.begin(); i != latches.end();
					++i)
				if (initLits.find(~*i) != initLits.end())
					return false;
			return true;
		}
		else
#endif /*FBPDR_USE_PO_INTERSECTION_SEMANTIC*/
		{
			// a full SAT query
			if (!inits)
			{
				inits = newSolver();
				loadInitialCondition(*inits);
			}
			Minisat::vec<Minisat::Lit> assumps;
			assumps.capacity(latches.size());
			for (vector<Minisat::Lit>::const_iterator i = latches.begin(); i != latches.end();
					++i)
				assumps.push(*i);
			return inits->solve(assumps);
		}
	}
	else
	{
		// a full SAT query
		if (!inits)
		{
			inits = newSolver();
			inits->addClause(error());
			loadError(*inits);
		}

		Minisat::vec<Minisat::Lit> assumps;
		assumps.capacity(latches.size());
		for (vector<Minisat::Lit>::const_iterator i = latches.begin(); i != latches.end();
				++i)
			assumps.push(*i);
		return inits->solve(assumps);
	}

}

/*
 * Un-generalize an unprimed cube which has an intersection
 * with the initial states.
 */
void Model::ungenInitCube(LitVec &genCube, const LitVec &originalCube,
		bool revpdr)
{
	assert(!originalCube.empty());
#ifndef	FBPDR_USE_PO_INTERSECTION_SEMANTIC
	if (!revpdr && invariantConstraints().empty()) //trivial early out
	{
		//only possible for pre 1.9 AIGER models and
		//original PDR
		if (initLits.empty())
			initLits.insert(init.begin(), init.end());
		for (auto &lit : originalCube)
		{
			if (initLits.find(~lit) != initLits.end())
			{
				genCube.push_back(lit);
				sort(genCube.begin(), genCube.end());
				return;
			}
		}
		assert(false);
	}
#endif /*FBPDR_USE_PO_INTERSECTION_SEMANTIC*/

	Minisat::vec<Minisat::Lit> assumps;

	assert(inits);
	if (!inits)
	{
		inits = newSolver();
		if(revpdr)
		{
			inits->addClause(error());
			loadError(*inits);
		}
		else
		{
			loadInitialCondition(*inits);
		}
	}

	/*
	 * Check which literals of the original cube are responsible
	 * for being disjoint from the initial states.
	 * In case they have been dropped re-push them into the
	 * generalized cube.
	 */
	assumps.capacity(originalCube.size());
	for (auto &lit : originalCube)
	{
		assumps.push(lit);
	}
	assert(inits);
	bool intersect = inits->solve(assumps);
	assert(!intersect);

	size_t oldszGenCube = genCube.size();
	for (int i = 0; i < inits->conflict.size(); ++i)
	{
		if (!std::binary_search(genCube.begin(), genCube.end(),
				~inits->conflict[i]))
			genCube.push_back(~inits->conflict[i]);
	}
	if (oldszGenCube < genCube.size())
	{
		sort(genCube.begin(), genCube.end());
	}
}

//return init literal set
LitVec Model::getInitLits()
{
	return this->init;
}

size_t Model::getMaxVar() const
{
	return vars.size();
}


size_t Model::getAigMaxVar() const
{
	if (aig.size() > 0)
	{
		return Minisat::var((aig.end()-1)->lhs);
	}
	else
		return 1;
}

void Model::circuitPropagation(std::vector<ternBool> &valuation,
		std::set<unsigned int> &constants)
{
	ternBool l_T((uint8_t) 1);
	ternBool l_F((uint8_t) 0);
	ternBool l_U((uint8_t) 2);

	//calculate ANDs
	for (AigVec::const_iterator i = aig.begin(); i != aig.end(); ++i)
	{
		ternBool rhs0Valuation, rhs1Valuation;
		if (i->rhs0.x > 1)
		{
			if (!Minisat::sign(i->rhs0))
				rhs0Valuation = valuation[i->rhs0.x >> 1];
			else
				rhs0Valuation = !valuation[i->rhs0.x >> 1];

			//log this and node as successor of signal rhs0
			if (!circuitNodeSuccessorsActive)
				circuitNodeSuccessors[i->rhs0.x >> 1].insert(i->lhs.x >> 1);
		}
		else
		{
			rhs0Valuation = i->rhs0.x;
		}

		if (i->rhs1.x > 1)
		{
			if (!Minisat::sign(i->rhs1))
				rhs1Valuation = valuation[i->rhs1.x >> 1];
			else
				rhs1Valuation = !valuation[i->rhs1.x >> 1];

			//log this and node as successor of signal rhs1
			if (!circuitNodeSuccessorsActive)
				circuitNodeSuccessors[i->rhs1.x >> 1].insert(i->lhs.x >> 1);
		}
		else
		{
			rhs1Valuation = i->rhs1.x;
		}

		valuation[i->lhs.x >> 1] = (rhs0Valuation && rhs1Valuation);
	}

	//calculate latch inputs (next state)
	//negate if there is a last NOT-gate
	for (VarVec::const_iterator it = beginLatches(); it != endLatches(); ++it)
	{
		if (nextStateFn(*it).x > 1)
		{
			if (Minisat::sign(nextStateFn(*it)))
			{
				valuation[nextStateFn(*it).x >> 1] =
						!valuation[nextStateFn(*it).x >> 1];
			}
		}
		else
			valuation[nextStateFn(*it).x >> 1] = nextStateFn(*it).x;

		if (valuation[nextStateFn(*it).x >> 1] != l_U)
			constants.insert(it->var());
	}

	if (!circuitNodeSuccessorsActive)
		circuitNodeSuccessorsActive = true;
}

PatternFix Model::simFixRndPatterns(LitVec &presentState)
{
	PatternFix res(endLatches() - beginLatches());
	PatternFix valuation(getMaxVar() + 1);
	//create patterns for each input
	srand(1);
	for (VarVec::const_iterator i = beginInputs(); i != endLatches(); ++i)
	{
		std::bitset<gBitwidth> bitvec;
		for (size_t i = 0; i < gBitwidth; ++i)
			bitvec[i] = rand() % 2;
		valuation[i->var()] = bitvec;
	}
	for (auto &lit : presentState)
	{
		std::bitset<gBitwidth> bitvec;
		for (size_t k = 0; k < gBitwidth; ++k)
			bitvec[k] = !Minisat::sign(lit);
		valuation[lit.x >> 1] = bitvec;
	}

	//calculate ANDs
	for (AigVec::const_iterator i = aig.begin(); i != aig.end(); ++i)
	{
		std::bitset<gBitwidth> rhs0Valuation, rhs1Valuation;
		if (i->rhs0.x > 1)
		{
			if (!Minisat::sign(i->rhs0))
				rhs0Valuation = valuation[i->rhs0.x >> 1];
			else
				rhs0Valuation = ~(valuation[i->rhs0.x >> 1]);
		}
		else
		{
			if (!i->rhs0.x)
				rhs0Valuation.reset();
			else
				rhs0Valuation.set();
		}

		if (i->rhs1.x > 1)
		{
			if (!Minisat::sign(i->rhs1))
				rhs1Valuation = valuation[i->rhs1.x >> 1];
			else
				rhs1Valuation = ~(valuation[i->rhs1.x >> 1]);
		}
		else
		{
			if (!i->rhs1.x)
				rhs1Valuation.reset();
			else
				rhs1Valuation.set();
		}

		valuation[i->lhs.x >> 1] = rhs0Valuation & rhs1Valuation;
	}

	//calculate latch inputs (next state)
	//negate if there is a last NOT-gate
	for (VarVec::const_iterator it = beginLatches(); it != endLatches(); ++it)
	{
		if (nextStateFn(*it).x > 1)
		{
			if (Minisat::sign(nextStateFn(*it)))
				res[it->var() - beginLatches()->var()] =
						~(valuation[nextStateFn(*it).x >> 1]);
			else
				res[it->var() - beginLatches()->var()] = valuation[nextStateFn(
						*it).x >> 1];
		}
		else
		{
			if (!nextStateFn(*it).x)
				res[it->var() - beginLatches()->var()].reset();
			else
				res[it->var() - beginLatches()->var()].set();
		}
	}
	return res;
}

std::set<unsigned int> Model::circuitTrav(std::vector<ternBool> &valuation,
		unsigned int stateVar)
{
	ternBool l_T((uint8_t) 1);
	ternBool l_F((uint8_t) 0);
	ternBool l_U((uint8_t) 2);

	std::set<unsigned int> irrVarInFnSupp;

	Minisat::Lit nxt = nextStateFn(varOfLit(Minisat::mkLit(stateVar, false)));

	//if nxt is constant -> decrement all non-assigned variable outdegrees?
	if (valuation[nxt.x >> 1] != l_U)
	{
		std::vector<unsigned int> supp = getTransitionSupport(
				varOfLit(Minisat::mkLit(stateVar, false)));
		//assert(supp.size()>1);
		for (unsigned int i = 0; i < supp.size(); ++i)
		{
			//only unassigned
			if (valuation[supp[i]] != l_U)
				continue;
			else
			{
				//irrelevant support variable
				irrVarInFnSupp.insert(supp[i]);
			}
		}
		return irrVarInFnSupp;
	}

	//find state variables with only irrelevant "fanout"
	//calculate ANDs - start at next state of this latch
	std::vector<bool> irrelevantVars(this->getMaxVar() + 1, false);
	if (Minisat::var(nxt) >= endLatches()->var())
	{
		AigVec::const_reverse_iterator it = aig.rend()
				- (Minisat::var(nxt) - (aig.begin()->lhs.x >> 1) + 1);
		assert(Minisat::var(it->lhs) == Minisat::var(nxt));
		LitSet require;
		require.insert(nxt);
		for (AigVec::const_reverse_iterator i = it; i != aig.rend(); ++i)
		{
			if (require.find(i->lhs) == require.end()
					&& require.find(~i->lhs) == require.end())
			{
				continue;
			}

			//already "irrelevant"?
			if (valuation[i->lhs.x >> 1] != l_U
					|| irrelevantVars[i->lhs.x >> 1])
			{
				if (i->rhs0.x > 1 && (i->rhs0.x >> 1) >= endLatches()->var())
					require.insert(i->rhs0);
				if (i->rhs1.x > 1 && (i->rhs1.x >> 1) >= endLatches()->var())
					require.insert(i->rhs1);
				continue;
			}

			bool irrelevant = true;
			if (Minisat::var(i->lhs) == Minisat::var(nxt))
				irrelevant = false;
			else
			{
				for (auto &succ : circuitNodeSuccessors[i->lhs.x >> 1])
				{
					if (valuation[succ] == l_U && !irrelevantVars[succ])
					{
						if (require.find(Minisat::mkLit(succ, false))
								!= require.end()
								|| require.find(Minisat::mkLit(succ, true))
										!= require.end())
						{
							irrelevant = false;
							break;
						}
					}
				}
			}

			//if irrelevant -> use constant valuation as helper
			//(semantically incorrect but sufficient)
			if (irrelevant)
			{
				irrelevantVars[i->lhs.x >> 1] = true;
			}

			if (i->rhs0.x > 1 && (i->rhs0.x >> 1) >= endLatches()->var())
				require.insert(i->rhs0);
			if (i->rhs1.x > 1 && (i->rhs1.x >> 1) >= endLatches()->var())
				require.insert(i->rhs1);
		}

		//which (unassigned) present state variables are no longer in transition support?
		std::vector<unsigned int>& supp = getTransitionSupport(
				varOfLit(Minisat::mkLit(stateVar, false)));
		//assert(supp.size()>1);
		for (unsigned int i = 0; i < supp.size(); ++i)
		{
			//only unassigned
			if (valuation[supp[i]] != l_U)
				continue;
			bool irrelevant = true;
			for (auto &succ : circuitNodeSuccessors[supp[i]])
			{
				if (valuation[succ] == l_U && !irrelevantVars[succ])
				{
					if (require.find(Minisat::mkLit(succ, false))
							!= require.end()
							|| require.find(Minisat::mkLit(succ, true))
									!= require.end())
					{

						irrelevant = false;
						break;
					}
				}
			}
			if (irrelevant)
			{
				//irrelevant support variable
				irrVarInFnSupp.insert(supp[i]);
			}
		}
	}
	valuation.clear();
	return irrVarInFnSupp;
}

std::vector<unsigned int>& Model::getTransitionSupport(Var v)
{

	if (transitionSupport[v.var() - beginLatches()->var()].size() > 0)
	{
		return transitionSupport[v.var() - beginLatches()->var()];
	}
	else
	{
		LitSet require;  // unprimed formulas
		std::vector<unsigned int> support;
		if ((nextStateFn(v).x >> 1) < endLatches()->var()
				&& nextStateFn(v).x > 1)
		{
			support.push_back(nextStateFn(v).x >> 1);
		}
		else
		{
			if (Minisat::var(nextStateFn(v)) >= endLatches()->var())
			{
				require.insert(nextStateFn(v));
				AigVec::const_reverse_iterator it = aig.rend()
						- (Minisat::var(nextStateFn(v))
								- (aig.begin()->lhs.x >> 1) + 1);
				assert(Minisat::var(it->lhs) == Minisat::var(nextStateFn(v)));
				// traverse AIG backward
				for (AigVec::const_reverse_iterator i = it; i != aig.rend();
						++i)
				{
					// skip if this row is not required
					if (require.find(i->lhs) == require.end()
							&& require.find(~i->lhs) == require.end())
						continue;

					if ((i->rhs0.x >> 1) < endLatches()->var() && i->rhs0.x > 1)
					{
						support.push_back(i->rhs0.x >> 1); //store vars in support set
					}
					else
						require.insert(i->rhs0);

					if ((i->rhs1.x >> 1) < endLatches()->var() && i->rhs1.x > 1)
					{
						support.push_back(i->rhs1.x >> 1); //store vars in support set
					}
					else
						require.insert(i->rhs1);
				}
				std::sort(support.begin(), support.end());
			}

		}

		//exploit that support is sorted -
		//avoid counting the same supp var twice
		for (unsigned int i = 0; i < support.size(); ++i)
		{
			if (i > 0)
			{
				if (support[i] != support[i - 1])
					outDegrSuppVars[support[i]]++;
			}
			else
				outDegrSuppVars[support[i]]++;
		}
		transitionSupport[v.var() - beginLatches()->var()] = support;
		return transitionSupport[v.var() - beginLatches()->var()];
	}
}

// Creates a named variable.
Var var(const aiger_symbol *syms, size_t i, const char prefix, bool prime =
		false)
{
	const aiger_symbol &sym = syms[i];
	stringstream ss;
	if (sym.name)
		ss << sym.name;
	else
		ss << prefix << i;
	if (prime)
		ss << "'";
	return Var(ss.str());
}

Minisat::Lit lit(const VarVec &vars, unsigned int l)
{
	return vars[l >> 1].lit(aiger_sign(l));
}

Model* modelFromAiger(aiger *aig, unsigned int propertyIndex)
{
	VarVec vars(1, Var("false"));
	LitVec init, constraints, nextStateFns;

	// declare primary inputs and latches
	for (size_t i = 0; i < aig->num_inputs; ++i)
		vars.push_back(var(aig->inputs, i, 'i'));
	for (size_t i = 0; i < aig->num_latches; ++i)
		vars.push_back(var(aig->latches, i, 'l'));

	// the AND section
	AigVec aigv;
	for (size_t i = 0; i < aig->num_ands; ++i)
	{
		// 1. create a representative
		stringstream ss;
		ss << 'r' << i;
		vars.push_back(Var(ss.str()));
		const Var &rep = vars.back();
		// 2. obtain arguments of AND as lits
		Minisat::Lit l0 = lit(vars, aig->ands[i].rhs0);
		Minisat::Lit l1 = lit(vars, aig->ands[i].rhs1);
		// 3. add AIG row
		aigv.push_back(AigRow(rep.lit(false), l0, l1));
	}

	// acquire latches' initial states and next-state functions
	for (size_t i = 0; i < aig->num_latches; ++i)
	{
		const Var &latch = vars[1 + aig->num_inputs + i];
		// initial condition
		unsigned int r = aig->latches[i].reset;
		if (r < 2)
			init.push_back(latch.lit(r == 0));
		// next-state function
		nextStateFns.push_back(lit(vars, aig->latches[i].next));
	}

	// invariant constraints
	for (size_t i = 0; i < aig->num_constraints; ++i)
		constraints.push_back(lit(vars, aig->constraints[i].lit));

	// acquire error from given propertyIndex
	if ((aig->num_bad > 0 && aig->num_bad <= propertyIndex)
			|| (aig->num_outputs > 0 && aig->num_outputs <= propertyIndex))
	{
		cout << "Bad property index specified." << endl;
		return 0;
	}
	Minisat::Lit err =
			aig->num_bad > 0 ?
					lit(vars, aig->bad[propertyIndex].lit) :
					lit(vars, aig->outputs[propertyIndex].lit);

	return new Model(vars, 1, 1 + aig->num_inputs,
			1 + aig->num_inputs + aig->num_latches, init, constraints, nextStateFns, err,
			aigv);
}
