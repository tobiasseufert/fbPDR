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
#include <string>
#include <time.h>

extern "C"
{
#include "aiger.h"
}
#include "IC3.h"
#include "IC3.cpp"
#include "Model.h"


static void check(Model &model,
#ifdef FBPDR
		vector<IC3::State> *states,
		vector<IC3::State> *statesOther, vector<IC3::Frame> *frames,
		vector<IC3::Frame> *framesOther,
#if defined(FBPDR_USE_PO_INTERSECTION) || defined(FBPDR_USE_PO_INTERSECTION_SEMANTIC)
		DeeperPoFirst *pos, DeeperPoFirst *posOther,
#endif
		IC3::ThreadHandle *thHandle,
#endif /*FBPDR*/
		int verbose,
		bool basic, bool random, bool revpdr)
{
	IC3::IC3 ic3(model,
#ifdef FBPDR
			states, statesOther, frames, framesOther,
#if defined(FBPDR_USE_PO_INTERSECTION) || defined(FBPDR_USE_PO_INTERSECTION_SEMANTIC)
			pos, posOther,
#endif
			thHandle,
#endif /*FBPDR*/
			verbose, basic, random, revpdr);
	try{
		bool rv = ic3.check();
		if (!rv)
			ic3.printWitness();
		if (verbose)
			ic3.printStats();
		cout << !rv << endl;
#ifdef FBPDR
		if(thHandle)
			thHandle->kill = KILL_CURRENT_THREAD;
#endif
	}
	catch(std::exception& e)
	{
		//thread is terminated by other one, which found a result
		return;
	}
}

int main(int argc, char **argv)
{
	unsigned int propertyIndex = 0;
	bool basic = false, random = false;
#ifndef FBPDR
	bool revpdr = false;
#endif
	int verbose = 0;
	for (int i = 1; i < argc; ++i)
	{
		if (string(argv[i]) == "-v")
			// option: verbosity
			verbose = 2;
		else if (string(argv[i]) == "-s")
			// option: print statistics
			verbose = max(1, verbose);
		else if (string(argv[i]) == "-r")
		{
			// option: randomize the run, which is useful in performance
			// testing; default behavior is deterministic
			srand(time(NULL));
			random = true;
		}
		else if (string(argv[i]) == "-b")
			// option: use basic generalization
			basic = true;
#ifndef FBPDR
		else if (string(argv[i]) == "-x")
			// option: reversePDR
			revpdr = true;
#endif
		else if (string(argv[i]) == "-h")
		{
			// option: print help
			cout << "Usage: IC3 [-v] [-s] [-r] [-b] [-x] [propertyIndex] < [AIGER file]" << endl;
			cout << "  -v: verbose output" << endl;
			cout << "  -s: print statistics" << endl;
			cout << "  -r: randomize the run" << endl;
			cout << "  -b: use basic generalization" << endl;
#ifndef FBPDR
			cout << "  -x: use reverse PDR" << endl;
#endif
			cout << "  propertyIndex: index of the property to check" << endl;
			cout << "  If no propertyIndex is given, the first property is used." << endl;
			cout << "  If no properties are given, the program will exit." << endl;
			return 0;
		}
		else
			// optional argument: set property index
			propertyIndex = (unsigned) atoi(argv[i]);
	}

	// read AIGER model
	aiger *aig = aiger_init();
	const char *msg = aiger_read_from_file(aig, stdin);
	if (msg)
	{
		cout << msg << endl;
		return 0;
	}
	// create the Model from the obtained aig
	Model *model = modelFromAiger(aig, propertyIndex);
	aiger_reset(aig);
	if (!model)
		return 0;

	if (!IC3::baseCases(*model))
	{
		cout << 1 << endl;
		return 0;
	}

	//"shared memory", absence of data races by design (alternating execution)
#ifdef FBPDR
	vector<IC3::Frame> *framesOrig = new vector<IC3::Frame>();
	vector<IC3::Frame> *framesRev = new vector<IC3::Frame>();
	vector<IC3::State> *statesOrig = new vector<IC3::State>();
	vector<IC3::State> *statesRev = new vector<IC3::State>();
#if defined(FBPDR_USE_PO_INTERSECTION) || defined(FBPDR_USE_PO_INTERSECTION_SEMANTIC)
	DeeperPoFirst *posOrig = new DeeperPoFirst();
	DeeperPoFirst *posRev = new DeeperPoFirst();
#endif
	IC3::ThreadHandle *thHandle = new IC3::ThreadHandle();
#endif /*FBPDR*/

	// model check it
#ifdef FBPDR
	std::thread t2(check, std::ref(*model), statesOrig, statesRev, framesOrig, framesRev,
#if defined(FBPDR_USE_PO_INTERSECTION) || defined(FBPDR_USE_PO_INTERSECTION_SEMANTIC)
			posOrig, posRev,
#endif /*FBPDR_USE_PO_INTERSECTION*/
			thHandle, verbose, basic, random, false); //original PDR
	std::thread t1(check, std::ref(*model), statesRev, statesOrig, framesRev, framesOrig,
#if defined(FBPDR_USE_PO_INTERSECTION) || defined(FBPDR_USE_PO_INTERSECTION_SEMANTIC)
			posRev, posOrig,
#endif /*FBPDR_USE_PO_INTERSECTION*/
			thHandle, verbose, basic, random, true); //Reverse PDR
	t2.join();
	t1.join();
#else
	check(*model, verbose, basic, random, revpdr);
#endif /*FBPDR*/

	/*cleanup*/
#ifdef FBPDR
	delete model;
	delete framesOrig;
	delete framesRev;
	delete statesOrig;
	delete statesRev;
#if defined(FBPDR_USE_PO_INTERSECTION) || defined(FBPDR_USE_PO_INTERSECTION_SEMANTIC)
	delete posOrig;
	delete posRev;
#endif /*FBPDR_USE_PO_INTERSECTION*/
	delete thHandle;
#endif /*FBPDR*/

	return 1;
}
