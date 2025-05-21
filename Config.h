/*********************************************************************
 Copyright (c) 2021, Tobias Seufert

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

#ifndef CONFIG_H_INCLUDED
#define CONFIG_H_INCLUDED

/* Lifting */
//#define USE_IGBG
/* Reverse PDR */
//#define revpogen
/* fbPDR functionality */
#define FBPDR
#ifdef FBPDR
#define FBPDR_USE_PO_INTERSECTION
#ifdef FBPDR_USE_PO_INTERSECTION
//#define SHORTER_PO_FIRST
#define DEEPER_PO_FIRST
#endif /*FBPDR_USE_PO_INTERSECTION*/
#ifndef FBPDR_USE_PO_INTERSECTION
//#define FBPDR_USE_PO_INTERSECTION_SEMANTIC
#ifdef FBPDR_USE_PO_INTERSECTION_SEMANTIC
#define DEEPER_PO_FIRST
#endif/*FBPDR_USE_PO_INTERSECTION_SEMANTIC*/
#endif /*not FBPDR_USE_PO_INTERSECTION*/
//#define FBPDR_USE_LEMMA_SHARING
#ifdef FBPDR_USE_LEMMA_SHARING
#define FBPDR_REMOVE_DISCHARGED_POS
#endif /*FBPDR_USE_LEMMA_SHARING*/
#endif /*FBPDR*/

/* subsumption checking (semantically) */
#define CHECK_PO_SUBSUMPTION

#endif
