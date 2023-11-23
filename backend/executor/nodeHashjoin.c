/*-------------------------------------------------------------------------
 *
 * nodeHashjoin.c
 *	  Routines to handle hash join nodes
 *
 * Portions Copyright (c) 1996-2005, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  $PostgreSQL: pgsql/src/backend/executor/nodeHashjoin.c,v 1.75.2.3 2005/11/28 23:46:24 tgl Exp $
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include "executor/executor.h"
#include "executor/hashjoin.h"
#include "executor/nodeHash.h"
#include "executor/nodeHashjoin.h"
#include "optimizer/clauses.h"
#include "utils/memutils.h"


static TupleTableSlot *ExecHashJoinOuterGetTuple(PlanState *outerNode,
						  HashJoinState *hjstate,
						  uint32 *hashvalue);
static TupleTableSlot *ExecHashJoinGetSavedTuple(HashJoinState *hjstate,
						  BufFile *file,
						  uint32 *hashvalue,
						  TupleTableSlot *tupleSlot);
static int	ExecHashJoinNewBatch(HashJoinState *hjstate);


/* ----------------------------------------------------------------
 *		ExecHashJoin
 *
 *		This function implements the Hybrid Hashjoin algorithm.
 *
 *		Note: the relation we build hash table on is the "inner"
 *			  the other one is "outer".
 * ----------------------------------------------------------------
 */
TupleTableSlot *				/* return: a tuple or NULL */
ExecHashJoin(HashJoinState *node)
{
	EState	   *estate;
	PlanState  *outerNode;
	HashState  *inner_hashNode; //CSI3130: Added inner node
	// CSI3530 il faut un innerNode aussi //CSI3130 You need an inner node too
	HashState  *outer_hashNode; //CSI3130: Changed for outer node
	List	   *joinqual;
	List	   *otherqual;
	TupleTableSlot *inntuple; 
	TupleTableSlot *outtuple; //CSI3130: Added outer tuple for outer join operation 
	// CSI3530 il faut un outer_hashtable aussi //CSI 3130 You need an outer_hashtable node too
	ExprContext *econtext;
	ExprDoneCond isDone;
	HashJoinTable inner_hashtable; //CSI3130: Renamed for differentiation of inner and outer hashtables
	HashJoinTable outer_hashtable; //CSI3130: Added outer hash table initialization for outer join operation
	HeapTuple	curtuple;
	TupleTableSlot *outerTupleSlot; 
	TupleTableSlot *innerTupleSlot; //CSI3130: Added inner tuple slot for inner join
    // CSI3530 il faut un innerTupleSlot aussi //CSI3130 You need an innerTupleSlot too
	uint32		hashvalue;
	int			batchno;

	/*
	 * get information from HashJoin node
	 */
	estate = node->js.ps.state;
	joinqual = node->js.joinqual;
	otherqual = node->js.ps.qual;
	inner_hashNode = (HashState *) innerPlanState(node); //CSI3130: renamed to innerHashNode for Inner Join Hash Table Search (HTS)
	outer_hashNode = (HashState *) outerPlanState(node); //CSI3130: added outerHashNode for outer join operation 
	//outerNode = outerPlanState(node); //CSI3130: Commented this out, no longer needed
	// CSI3530 and CSI3130 ...
	
	/*
	 * get information from HashJoin state
	 */
	 // CSI3530 and CSI3130 ...
	inner_hashtable = node->inner_hj_HashTable; //CSI3130: Added inner hash table for inner join
	outer_hashtable = node->outer_hj_HashTable; //CSI3130: Added outer hash table for outer join
    
	econtext = node->js.ps.ps_ExprContext;

	/*
	 * Check to see if we're still projecting out tuples from a previous join
	 * tuple (because there is a function-returning-set in the projection
	 * expressions).  If so, try to project another one.
	 */
	//CSI3130: Commented out the following if block of code
	/*	
	if (node->js.ps.ps_TupFromTlist)
	{
		TupleTableSlot *result;

		result = ExecProject(node->js.ps.ps_ProjInfo, &isDone);
		if (isDone == ExprMultipleResult)
			return result;
		/* Done with that source tuple... 
	node->js.ps.ps_TupFromTlist = false;
	}*/


	/*
	 * If we're doing an IN join, we want to return at most one row per outer
	 * tuple; so we can stop scanning the inner scan if we matched on the
	 * previous try.
	 */
	if (node->js.jointype == JOIN_IN && node->hj_MatchedOuter)
		node->hj_NeedNewOuter = true;

	/*
	 * Reset per-tuple memory context to free any expression evaluation
	 * storage allocated in the previous tuple cycle.  Note this can't happen
	 * until we're done projecting out tuples from a join tuple.
	 */
	ResetExprContext(econtext);

	/*
	 * if this is the first call, build the hash table for inner relation
	 */
	//CSI3130: Modified the if-statement condition for inner and outer hashtables
	if (inner_hashtable == NULL && outer_hashtable == NULL) //CSI3530 and CSI3130 ..
	{
		/*
		 * If the outer relation is completely empty, we can quit without
		 * building the hash table.  However, for an inner join it is only a
		 * win to check this when the outer relation's startup cost is less
		 * than the projected cost of building the hash table.	Otherwise it's
		 * best to build the hash table first and see if the inner relation is
		 * empty.  (When it's an outer join, we should always make this check,
		 * since we aren't going to be able to skip the join on the strength
		 * of an empty inner relation anyway.)
		 *
		 * If we are rescanning the join, we make use of information gained
		 * on the previous scan: don't bother to try the prefetch if the
		 * previous scan found the outer relation nonempty.  This is not
		 * 100% reliable since with new parameters the outer relation might
		 * yield different results, but it's a good heuristic.
		 *
		 * The only way to make the check is to try to fetch a tuple from the
		 * outer plan node.  If we succeed, we have to stash it away for later
		 * consumption by ExecHashJoinOuterGetTuple.
		 */
		if (node->js.jointype == JOIN_LEFT ||
			(outerNode->plan->startup_cost < hashNode->ps.plan->total_cost &&
			 !node->hj_OuterNotEmpty))
		{
			node->hj_FirstOuterTupleSlot = ExecProcNode(outerNode);
			if (TupIsNull(node->hj_FirstOuterTupleSlot))
			{
				node->hj_OuterNotEmpty = false;
				return NULL;
			}
			else
				node->hj_OuterNotEmpty = true;
		}
		else
			node->hj_FirstOuterTupleSlot = NULL;

		/*
		 * create the hash table
		 */
		inner_hashtable = ExecHashTableCreate((Hash *) inner_hashNode->ps.plan,node->hj_HashOperators);
		node->inner_hj_HashTable = inner_hashtable; //CSI3130: inner hashtable initialize with the inner_hashNode as parser

		outer_hashtable = ExecHashTableCreate((Hash *) outer_hashNode->ps.plan,node->hj_HashOperators); 

		node->outer_hj_HashTable = outer_hashtable; //CSI3130: outer hashtable initialize with the outer_hashNode as parser

		/*
		 * execute the Hash node, to build the hash table
		 */
		 //CSI3130: added inner and outer hash tables to build the hash table, only one table gets built on execution
		inner_hashNode->hashtable = inner_hashtable; 
		outer_hashNode->hashtable = outer_hashtable;
		//CSI3130: Commented out the following code. Code is no longer needed for hashjoin algorithm
		/*
		(void)MultiExecProcNode((PlanState*)hashNode);

		
		 * If the inner relation is completely empty, and we're not doing an
		 * outer join, we can quit without scanning the outer relation.
		 
		 //if (hashtable->totalTuples == 0 && node->js.jointype != JOIN_LEFT)
		return NULL;

		/*
		 * need to remember whether nbatch has increased since we began
		 * scanning the outer relation
		 
		hashtable->nbatch_outstart = hashtable->nbatch;

		/*
		 * Reset OuterNotEmpty for scan.  (It's OK if we fetched a tuple
		 * above, because ExecHashJoinOuterGetTuple will immediately
		 * set it again.)
		 
		node->hj_OuterNotEmpty = false;
		}
		*/

	/*
	 * run the hash join process
	 */
	for (;;)
	{
		/*
		 * If we don't have an outer tuple, get the next one
		 */
		// CSI3130: Changes Begin
		//CSI3130: if-statement changed, specify conditions for inner and outer join, when to no longer search for new tuples
		if ((node->hj_NeedNewInner || node->inner_exhausted) && (node->hj_NeedNewOuter || node->outer_exhausted))
		{
			outerTupleSlot = ExecHashJoinOuterGetTuple(outerNode,
				node,
				&hashvalue);
			if (!node->inner_exhausted)

			{
				innerTupleSlot = ExecProcNode((PlanState*)inner_hashNode);
				node->isNextFetchInner = false;
				node->js.ps.ps_InnerTupleSlot = innerTupleSlot;
				if (!TupIsNull(innerTupleSlot)) {
					node->hj_NeedNewOuter = false;
					bool isNullAttr;
					//printf("Found a new inner \n"); //test inner/outer join search for new tuple 
					ExprContext* econtext = node->js.ps.ps_ExprContext;
					econtext->ecxt_innertuple = innerTupleSlot;
					hashvalue = ExecHashGetHashValue(outer_hashtable, econtext, node->hj_InnerHashKeys);
					node->js.ps.ps_InnerTupleSlot = innerTupleSlot;
					econtext->ecxt_innertuple = node->js.ps.ps_InnerTupleSlot;

					node->inner_hj_CurHashValue = hashvalue;
					ExecHashGetBucketAndBatch(outer_hashtable, hashvalue, &node->outer_hj_CurBucketNo, &batchno);
					node->outer_hj_CurTuple = NULL;
				}
				else {
					node->inner_exhausted = true;
				}
			}
			if (!node->outer_exhausted)
			{
				outerTupleSlot = ExecProcNode((PlanState*)outer_hashNode);
				node->isNextFetchInner = true;
				node->js.ps.ps_OuterTupleSlot = outerTupleSlot;

				if (!TupIsNull(outerTupleSlot))
				{
					bool isNullAttr;
					//printf("Found a new outer \n"); //We found a new outer 

					node->hj_OuterNotEmpty = true;
					ExprContext* econtext = node->js.ps.ps_ExprContext;
					econtext->ecxt_outertuple = outerTupleSlot;
					hashvalue = ExecHashGetHashValue(inner_hashtable, econtext, node->hj_OuterHashKeys);

					node->js.ps.ps_OuterTupleSlot = outerTupleSlot;
					econtext->ecxt_outertuple = outerTupleSlot;
					node->hj_NeedNewOuter = false;
					node->hj_MatchedOuter = false;
					/*
					 * now we have an outer tuple, find the corresponding bucket for
					 * this tuple from the hash table
					 */
					node->outer_hj_CurHashValue = hashvalue;
					ExecHashGetBucketAndBatch(inner_hashtable, hashvalue,
						&node->inner_hj_CurBucketNo, &batchno);
					node->inner_hj_CurTuple = NULL;


					/*
					 * Now we've got an outer tuple and the corresponding hash bucket,
					 * but this tuple may not belong to the current batch.
					 */
					if (batchno != hashtable->curbatch)
					{
						/*
						 * Need to postpone this outer tuple to a later batch. Save it
						 * in the corresponding outer-batch file.
						 */
						Assert(batchno > hashtable->curbatch);
						ExecHashJoinSaveTuple(ExecFetchSlotTuple(outerTupleSlot),
							hashvalue,
							&inner_hashtable->outerBatchFile[batchno]); //CSI3130: Changed for inner hashtable
						node->hj_NeedNewOuter = true;
						continue;		/* loop around for a new outer tuple */
					}
				}
				else {
					node->outer_exhausted = true;
				}
			}
		}
		//CSI3130: We've exhausted the inner and outer tuples that have been hashed and now we need to probe the hashed values for matching
		if (node->inner_exhausted && node->outer_exhausted)
		{
			printf("Exhausted inner (%f) tuples and outer (%f) tuples \n", inner_hashtable->totalTuples, outer_hashtable->totalTuples);
			printf("Number of inner hash table matches found is %d \n", node->matches_by_probing_inner);
			printf("Number of outer hash table matches found is %d \n", node->matches_by_probing_outer);
			return NULL;
		}
		//CSI3130:Changes End.

		/*
		 * OK, scan the selected hash bucket for matches
		 */
		//CSI3130: Changes begin.
		if (!TupIsNull(node->js.ps.ps_InnerTupleSlot))
		{
			for (;;)
			{
				ExprContext* econtext = node->js.ps.ps_ExprContext;
				econtext->ecxt_innertuple = node->js.ps.ps_InnerTupleSlot;
				curtuple = ExecScanHashBucketProbeOuter(node, econtext); //CSI3130: Add this function
				if (curtuple == NULL)
					break;			/* out of matches */

				/*
				 * we've got a match, but still need to test non-hashed quals
				 */
				outtuple = ExecStoreTuple(curtuple,
					node->outer_hj_HashTupleSlot,
					InvalidBuffer,
					false);	/* don't pfree this tuple */
				econtext->ecxt_outertuple = outtuple;

				/* reset temp memory each time to avoid leaks from qual expr */
				ResetExprContext(econtext);

				/*
				 * if we pass the qual, then save state for next call and have
				 * ExecProject form the projection, store it in the tuple table,
				 * and return the slot.
				 *
				 * Only the joinquals determine MatchedOuter status, but all quals
				 * must pass to actually return the tuple.
				 */
				if (!node->outer_exhausted && !node->hj_NeedNewOuter && !TupIsNull(node->js.ps.ps_OuterTupleSlot) &&
					ItemPointerGetBlockNumber(&curtuple->t_data->t_ctid) == ItemPointerGetBlockNumber(&node->js.ps.ps_OuterTupleSlot->tts_tuple->t_data->t_ctid)
					&& ItemPointerGetOffsetNumber(&curtuple->t_data->t_ctid) == ItemPointerGetOffsetNumber(js.ps.ps_OuterTupleSlot->tts_tuple->t_data->t_ctid))
				{
					//printf("Repeat Tuple Found, do not evaluate \n");
				}
				else if (joinqual == NIL || ExecQual(joinqual, econtext, false))
				{
					//node->hj_MatchedOuter = true; //CSI3130: Commented out 

					if (otherqual == NIL || ExecQual(otherqual, econtext, false))
					{
						TupleTableSlot* result;

						result = ExecProject(node->js.ps.ps_ProjInfo, &isDone);

						if (isDone != ExprEndResult)
						{
							node->matches_by_probing_outer++; //CSI3130: Increase Match Counter
							node->js.ps.ps_TupFromTlist =
								(isDone == ExprMultipleResult);
							return result;
						}
					}
				}
			}
		}
		node->hj_NeedNewOuter = true;
		node->js.ps.ps_InnerTupleSlot = NULL;
		
		//CSI3130: New if and for loop block for probing inner hash table using current outer tuple
		if (!TupIsNull(node->js.ps.ps_OuterTupleSlot))
		{
			for (;;)
			{
				ExprContext* econtext = node->js.ps.ps_ExprContext;
				econtext->ecxt_outertuple = node->js.ps.ps_OuterTupleSlot;

				curtuple = ExecScanHashBucketProbeInner(node, econtext);
				if (curtuple == NULL) //CSI3130: No more matches found, break out of for loop probe
				{
					break;
				}
				inntuple = ExecStoreTuple(curtuple, node->inner_hj_HashTupleSlot, InvalidBuffer, false);
				econtext->ecxt_innertuple = inntuple;

				ResetExprContext(econtext); //CSI3130: Reset the temporary memory to avoid memory leaks
				if (joinqual == NIL || ExecQual(joinqual, econtext, false))
				{
					node->hj_MatchedOuter = true; 

					if (otherqual == NIL || ExecQual(otherqual, econtext, false))
					{
						TupleTableSlot *result;

						result = ExecProject(node->js.ps.ps_ProjInfo, &isDone);

						if (isDone != ExprEndResult)
						{
							node->matches_by_probing_inner++; //CSI3130: Increase Match Counter for inner probe
							node->js.ps.ps_TupFromTlist =
								(isDone == ExprMultipleResult);
							return result;
						}
					}
					/*
					 * If we didn't return a tuple, may need to set NeedNewOuter
					 */
					if (node->js.jointype == JOIN_IN)
					{
						node->hj_NeedNewOuter = true;
						break;		/* out of loop over hash bucket */
					}

				}

			}
		}
		//CSI3130: Changes end.

				

		/*
		 * Now the current outer tuple has run out of matches, so check
		 * whether to emit a dummy outer-join tuple. If not, loop around to
		 * get a new outer tuple.
		 */
		node->hj_NeedNewOuter = true;
		node->js.ps.ps_OuterTupleSlot = NULL; //CSI3130: set the outerTupleSlot to NULL so we can probe new outer tuples
		node->hj_OuterNotEmpty = false; //CSI3130: outer tuple and node at the moment are empty


		if (!node->hj_MatchedOuter &&
			node->js.jointype == JOIN_LEFT)
		{
			/*
			 * We are doing an outer join and there were no join matches for
			 * this outer tuple.  Generate a fake join tuple with nulls for
			 * the inner tuple, and return it if it passes the non-join quals.
			 */
			econtext->ecxt_innertuple = node->hj_NullInnerTupleSlot;

			if (ExecQual(otherqual, econtext, false))
			{
				/*
				 * qualification was satisfied so we project and return the
				 * slot containing the result tuple using ExecProject().
				 */
				TupleTableSlot *result;

				result = ExecProject(node->js.ps.ps_ProjInfo, &isDone);

				if (isDone != ExprEndResult)
				{
					node->js.ps.ps_TupinFromTlist =
						(isDone == ExprMultipleResult);
					return result;
				}
			}
		}
	}
}

/* ----------------------------------------------------------------
 *		ExecInitHashJoin
 *
 *		Init routine for HashJoin node.
 * ----------------------------------------------------------------
 */
HashJoinState *
ExecInitHashJoin(HashJoin *node, EState *estate)
{
	HashJoinState *hjstate;
	//Plan	   *outerNode;
	Hash	   *inner_hashNode; //CSI3130: Initialize both the inner and outer hash nodes for the hash join / hash tables
	Hash	   *outer_hashNode
	List	   *lclauses;
	List	   *rclauses;
	List	   *hoperators;
	ListCell   *l;

	/*
	 * create state structure
	 */
	hjstate = makeNode(HashJoinState);
	hjstate->js.ps.plan = (Plan *) node;
	hjstate->js.ps.state = estate;

	/*
	 * Miscellaneous initialization
	 *
	 * create expression context for node
	 */
	ExecAssignExprContext(estate, &hjstate->js.ps);

	/*
	 * initialize child expressions
	 */
	hjstate->js.ps.targetlist = (List *)
		ExecInitExpr((Expr *) node->join.plan.targetlist,
					 (PlanState *) hjstate);
	hjstate->js.ps.qual = (List *)
		ExecInitExpr((Expr *) node->join.plan.qual,
					 (PlanState *) hjstate);
	hjstate->js.jointype = node->join.jointype;
	hjstate->js.joinqual = (List *)
		ExecInitExpr((Expr *) node->join.joinqual,
					 (PlanState *) hjstate);
	hjstate->hashclauses = (List *)
		ExecInitExpr((Expr *) node->hashclauses,
					 (PlanState *) hjstate);

	/*
	 * initialize child nodes
	 */
	outer_hashNode = (Hash *) outerPlan(node); //CSI3130: Renamed for current project context
	// CSI3530 and CSI3130 ...
	inner_hashNode = (Hash *) innerPlan(node); //CSI3130: Renamed as well for same reason

	outerPlanState(hjstate) = ExecInitNode((Plan *) outer_hashNode, estate); //CSI3130: Variable renaming again
	// CSI3530 and CSI3130 ...
	innerPlanState(hjstate) = ExecInitNode((Plan *) inner_hashNode, estate);

#define HASHJOIN_NSLOTS 3

	/*
	 * tuple table initialization
	 */
	// CSI3530 and CSI3130 ... 
	ExecInitResultTupleSlot(estate, &hjstate->js.ps);
	hjstate->hj_OuterTupleSlot = ExecInitExtraTupleSlot(estate);
	hjstate->hj_InnerTupleSlot = ExecInitExtraTupleSlot(estate);

	switch (node->join.jointype)
	{
		case JOIN_INNER:
		case JOIN_IN:
			break;
		case JOIN_LEFT:
			hjstate->hj_NullInnerTupleSlot =
				ExecInitNullTupleSlot(estate,
								 ExecGetResultType(innerPlanState(hjstate)));
			break;
		default:
			elog(ERROR, "unrecognized join type: %d",
				 (int) node->join.jointype);
	}

	/*
	 * now for some voodoo.  our temporary tuple slot is actually the result
	 * tuple slot of the Hash node (which is our inner plan).  we do this
	 * because Hash nodes don't return tuples via ExecProcNode() -- instead
	 * the hash join node uses ExecScanHashBucket() to get at the contents of
	 * the hash table.	-cim 6/9/91
	 */
	{
		HashState  *hashstate = (HashState *) innerPlanState(hjstate);
		TupleTableSlot *slot = hashstate->ps.ps_ResultTupleSlot;

		hjstate->inner_hj_HashTupleSlot = slot; //CSI3130: Renamed to inner for inner and outer tuple slots

		hashstate = (HashState *)outerPlanState(hjstate); //CSI3130: Next 3 lines for outer tuple slot initialization
		slot = hashstate->ps.ps_ResultTupleSlot;

		hjstate->outer_hj_HashTupleSlot = slot;
	}

	/*
	 * initialize tuple type and projection info
	 */
	ExecAssignResultTypeFromTL(&hjstate->js.ps);
	ExecAssignProjectionInfo(&hjstate->js.ps); //CSI3530 and CSI3130

	ExecSetSlotDescriptor(hjstate->hj_OuterTupleSlot,
		ExecGetResultType(outerPlanState(hjstate)),
		false); //CSI3530 and CSI3130

	ExecSetSlotDescriptor(hjstate->hj_InnerTupleSlot,
		ExecGetResultType(innerPlanState(hjstate)),
		false); //CSI3130: Added inner plan and inner tuple slot to the execution set slot descriptor which describes how the plan gets executed

	/*
	 * initialize hash-specific info 
	 * CSI3130: Added inner and outer hashtables and initialize each to their respective NULL values
	 */
	hjstate->inner_hj_HashTable = NULL;
	hjstate->outer_hj_HashTable = NULL;

	//CSI3530 and CSI3130...
	hjstate->hj_FirstOuterTupleSlot = NULL;

	//CSI3530 Plein d'initialisations a faire ici // CSI3130 Initialize here

	hjstate->inner_hj_CurHashValue = 0;
	hjstate->outer_hj_CurHashValue = 0;
	hjstate->inner_hj_CurBucketNo = 0;
	hjstate->outer_hj_CurBucketNo = 0;
	hjstate->inner_hj_CurTuple = NULL;
	hjstate->outer_hj_CurTuple = NULL;
	hjstate->inner_exhausted = false;
	hjstate->outer_exhausted = false;


	/*
	 * Deconstruct the hash clauses into outer and inner argument values, so
	 * that we can evaluate those subexpressions separately.  Also make a list
	 * of the hash operator OIDs, in preparation for looking up the hash
	 * functions to use.
	 */
	lclauses = NIL;
	rclauses = NIL;
	hoperators = NIL;
	foreach(l, hjstate->hashclauses)
	{
		FuncExprState *fstate = (FuncExprState *) lfirst(l);
		OpExpr	   *hclause;

		Assert(IsA(fstate, FuncExprState));
		hclause = (OpExpr *) fstate->xprstate.expr;
		Assert(IsA(hclause, OpExpr));
		lclauses = lappend(lclauses, linitial(fstate->args));
		rclauses = lappend(rclauses, lsecond(fstate->args));
		hoperators = lappend_oid(hoperators, hclause->opno);
	}
	hjstate->hj_OuterHashKeys = lclauses;
	hjstate->hj_InnerHashKeys = rclauses;
	hjstate->hj_HashOperators = hoperators;
	/* child Hash node needs to evaluate inner hash keys, too */
	((HashState *) innerPlanState(hjstate))->hashkeys = rclauses;

	((HashState *) outerPlanState(hjstate))->hashkeys = lclauses; //CSI3130: Added OuterPlanState since we are encoding outer and inner

	hjstate->js.ps.ps_OuterTupleSlot = NULL;
	hjstate->js.ps.ps_InnerTupleSlot = NULL;
	hjstate->js.ps.ps_TupFromTlist = false;
	hjstate->hj_NeedNewOuter = true;
	hjstate->hj_NeedNewInner = true; //CSI3130: Added Inner Flag for getting new inner tuple
	hjstate->hj_MatchedOuter = false;
	hjstate->hj_OuterNotEmpty = false;
	hjstate->matches_by_probing_inner = 0; //CSI3130: Match Tracker for inner join matches
	hjstate->matches_by_probing_outer = 0; //CSI3130: Match Tracker for outer join matches
	

	return hjstate;
}

int
ExecCountSlotsHashJoin(HashJoin *node)
{
	return ExecCountSlotsNode(outerPlan(node)) +
		ExecCountSlotsNode(innerPlan(node)) +
		HASHJOIN_NSLOTS;
}

/* ----------------------------------------------------------------
 *		ExecEndHashJoin
 *
 *		clean up routine for HashJoin node
 * ----------------------------------------------------------------
 */
void
ExecEndHashJoin(HashJoinState *node)
{
	/*
	 * Free hash table
	 */
	if (node->inner_hj_HashTable) //CSI3130: Variable modify since hj_Hashtable Does Not Exist
	{
		ExecHashTableDestroy(node->inner_hj_HashTable);
		node->inner_hj_HashTable = NULL;
	}
	if (node->outer_hj_HashTable) //CSI3130: Added outerHashtable cleanup
	{
		ExecHashTableDestroy(node->outer_hj_HashTable);
		node->outer_hj_HashTable = NULL;
	}


	/*
	 * Free the exprcontext
	 */
	ExecFreeExprContext(&node->js.ps);

	/*
	 * clean out the tuple table
	 */
	ExecClearTuple(node->js.ps.ps_ResultTupleSlot);
	ExecClearTuple(node->hj_OuterTupleSlot);
	ExecClearTuple(node->hj_InnerTupleSlot); //CSI3130: Added inner tuple slot clear
	// CSI3530 and CSI3130 ...
	ExecClearTuple(node->inner_hj_HashTupleSlot); 
	ExecClearTuple(node->outer_hj_HashTupleSlot); //CSI3130: Added inner and outer hash tuple slot clear

	/*
	 * clean up subtrees
	 */
	ExecEndNode(outerPlanState(node));
	ExecEndNode(innerPlanState(node));
}

/*
 * ExecHashJoinOuterGetTuple
 *
 *		get the next outer tuple for hashjoin: either by
 *		executing a plan node in the first pass, or from
 *		the temp files for the hashjoin batches.
 *
 * Returns a null slot if no more outer tuples.  On success, the tuple's
 * hash value is stored at *hashvalue --- this is either originally computed,
 * or re-read from the temp file.
 */
static TupleTableSlot *
ExecHashJoinOuterGetTuple(PlanState *outerNode,
						  HashJoinState *hjstate,
						  uint32 *hashvalue)
{
	HashJoinTable hashtable = hjstate->inner_hj_HashTable; //CSI3130: modified to inner hashtable
	int			curbatch = hashtable->curbatch;
	TupleTableSlot *slot;

	if (curbatch == 0)
	{							/* if it is the first pass */

		/*
		 * Check to see if first outer tuple was already fetched by
		 * ExecHashJoin() and not used yet.
		 */
		slot = hjstate->hj_FirstOuterTupleSlot;
		if (!TupIsNull(slot))
			hjstate->hj_FirstOuterTupleSlot = NULL;
		else
			slot = ExecProcNode(outerNode);
		if (!TupIsNull(slot))
		{
			/*
			 * We have to compute the tuple's hash value.
			 */
			ExprContext *econtext = hjstate->js.ps.ps_ExprContext;

			econtext->ecxt_outertuple = slot;
			*hashvalue = ExecHashGetHashValue(hashtable, econtext,
											  hjstate->hj_OuterHashKeys);

			/* remember outer relation is not empty for possible rescan */
			hjstate->hj_OuterNotEmpty = true;

			return slot;
		}

		/*
		 * We have just reached the end of the first pass. Try to switch to a
		 * saved batch.
		 */
		curbatch = ExecHashJoinNewBatch(hjstate);
	}

	/*
	 * Try to read from a temp file. Loop allows us to advance to new batches
	 * as needed.  NOTE: nbatch could increase inside ExecHashJoinNewBatch, so
	 * don't try to optimize this loop.
	 */
	while (curbatch < hashtable->nbatch)
	{
		slot = ExecHashJoinGetSavedTuple(hjstate,
										 hashtable->outerBatchFile[curbatch],
										 hashvalue,
										 hjstate->hj_OuterTupleSlot);
		if (!TupIsNull(slot))
			return slot;
		curbatch = ExecHashJoinNewBatch(hjstate);
	}

	/* Out of batches... */
	return NULL;
}

/*
 * ExecHashJoinNewBatch
 *		switch to a new hashjoin batch
 *
 * Returns the number of the new batch (1..nbatch-1), or nbatch if no more.
 * We will never return a batch number that has an empty outer batch file.
 */
static int
ExecHashJoinNewBatch(HashJoinState *hjstate)
{
	HashJoinTable hashtable = hjstate->inner_hj_HashTable; //CSI3130: Modified to inner hashtable
	int			nbatch;
	int			curbatch;
	BufFile    *innerFile;
	TupleTableSlot *slot;
	uint32		hashvalue;

start_over:
	nbatch = hashtable->nbatch;
	curbatch = hashtable->curbatch;

	if (curbatch > 0)
	{
		/*
		 * We no longer need the previous outer batch file; close it right
		 * away to free disk space.
		 */
		if (hashtable->outerBatchFile[curbatch])
			BufFileClose(hashtable->outerBatchFile[curbatch]);
		hashtable->outerBatchFile[curbatch] = NULL;
	}

	/*
	 * We can always skip over any batches that are completely empty on both
	 * sides.  We can sometimes skip over batches that are empty on only one
	 * side, but there are exceptions:
	 *
	 * 1. In a LEFT JOIN, we have to process outer batches even if the inner
	 * batch is empty.
	 *
	 * 2. If we have increased nbatch since the initial estimate, we have to
	 * scan inner batches since they might contain tuples that need to be
	 * reassigned to later inner batches.
	 *
	 * 3. Similarly, if we have increased nbatch since starting the outer
	 * scan, we have to rescan outer batches in case they contain tuples that
	 * need to be reassigned.
	 */
	curbatch++;
	while (curbatch < nbatch &&
		   (hashtable->outerBatchFile[curbatch] == NULL ||
			hashtable->innerBatchFile[curbatch] == NULL))
	{
		if (hashtable->outerBatchFile[curbatch] &&
			hjstate->js.jointype == JOIN_LEFT)
			break;				/* must process due to rule 1 */
		if (hashtable->innerBatchFile[curbatch] &&
			nbatch != hashtable->nbatch_original)
			break;				/* must process due to rule 2 */
		if (hashtable->outerBatchFile[curbatch] &&
			nbatch != hashtable->nbatch_outstart)
			break;				/* must process due to rule 3 */
		/* We can ignore this batch. */
		/* Release associated temp files right away. */
		if (hashtable->innerBatchFile[curbatch])
			BufFileClose(hashtable->innerBatchFile[curbatch]);
		hashtable->innerBatchFile[curbatch] = NULL;
		if (hashtable->outerBatchFile[curbatch])
			BufFileClose(hashtable->outerBatchFile[curbatch]);
		hashtable->outerBatchFile[curbatch] = NULL;
		curbatch++;
	}

	if (curbatch >= nbatch)
		return curbatch;		/* no more batches */

	hashtable->curbatch = curbatch;

	/*
	 * Reload the hash table with the new inner batch (which could be empty)
	 */
	ExecHashTableReset(hashtable);

	innerFile = hashtable->innerBatchFile[curbatch];

	if (innerFile != NULL)
	{
		if (BufFileSeek(innerFile, 0, 0L, SEEK_SET))
			ereport(ERROR,
					(errcode_for_file_access(),
				   errmsg("could not rewind hash-join temporary file: %m")));

		while ((slot = ExecHashJoinGetSavedTuple(hjstate,
												 innerFile,
												 &hashvalue,
												 hjstate->hj_HashTupleSlot)))
		{
			/*
			 * NOTE: some tuples may be sent to future batches.  Also, it is
			 * possible for hashtable->nbatch to be increased here!
			 */
			ExecHashTableInsert(hashtable,
								ExecFetchSlotTuple(slot),
								hashvalue);
		}

		/*
		 * after we build the hash table, the inner batch file is no longer
		 * needed
		 */
		BufFileClose(innerFile);
		hashtable->innerBatchFile[curbatch] = NULL;
	}

	/*
	 * If there's no outer batch file, advance to next batch.
	 */
	if (hashtable->outerBatchFile[curbatch] == NULL)
		goto start_over;

	/*
	 * Rewind outer batch file, so that we can start reading it.
	 */
	if (BufFileSeek(hashtable->outerBatchFile[curbatch], 0, 0L, SEEK_SET))
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not rewind hash-join temporary file: %m")));

	return curbatch;
}

/*
 * ExecHashJoinSaveTuple
 *		save a tuple to a batch file.
 *
 * The data recorded in the file for each tuple is its hash value,
 * then an image of its HeapTupleData (with meaningless t_data pointer)
 * followed by the HeapTupleHeader and tuple data.
 *
 * Note: it is important always to call this in the regular executor
 * context, not in a shorter-lived context; else the temp file buffers
 * will get messed up.
 */
void
ExecHashJoinSaveTuple(HeapTuple heapTuple, uint32 hashvalue,
					  BufFile **fileptr)
{
	BufFile    *file = *fileptr;
	size_t		written;

	if (file == NULL)
	{
		/* First write to this batch file, so open it. */
		file = BufFileCreateTemp(false);
		*fileptr = file;
	}

	written = BufFileWrite(file, (void *) &hashvalue, sizeof(uint32));
	if (written != sizeof(uint32))
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not write to hash-join temporary file: %m")));

	written = BufFileWrite(file, (void *) heapTuple, sizeof(HeapTupleData));
	if (written != sizeof(HeapTupleData))
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not write to hash-join temporary file: %m")));

	written = BufFileWrite(file, (void *) heapTuple->t_data, heapTuple->t_len);
	if (written != (size_t) heapTuple->t_len)
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not write to hash-join temporary file: %m")));
}

/*
 * ExecHashJoinGetSavedTuple
 *		read the next tuple from a batch file.	Return NULL if no more.
 *
 * On success, *hashvalue is set to the tuple's hash value, and the tuple
 * itself is stored in the given slot.
 */
static TupleTableSlot *
ExecHashJoinGetSavedTuple(HashJoinState *hjstate,
						  BufFile *file,
						  uint32 *hashvalue,
						  TupleTableSlot *tupleSlot)
{
	HeapTupleData htup;
	size_t		nread;
	HeapTuple	heapTuple;

	nread = BufFileRead(file, (void *) hashvalue, sizeof(uint32));
	if (nread == 0)
		return NULL;			/* end of file */
	if (nread != sizeof(uint32))
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not read from hash-join temporary file: %m")));
	nread = BufFileRead(file, (void *) &htup, sizeof(HeapTupleData));
	if (nread != sizeof(HeapTupleData))
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not read from hash-join temporary file: %m")));
	heapTuple = palloc(HEAPTUPLESIZE + htup.t_len);
	memcpy((char *) heapTuple, (char *) &htup, sizeof(HeapTupleData));
	heapTuple->t_datamcxt = CurrentMemoryContext;
	heapTuple->t_data = (HeapTupleHeader)
		((char *) heapTuple + HEAPTUPLESIZE);
	nread = BufFileRead(file, (void *) heapTuple->t_data, htup.t_len);
	if (nread != (size_t) htup.t_len)
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not read from hash-join temporary file: %m")));
	return ExecStoreTuple(heapTuple, tupleSlot, InvalidBuffer, true);
}


void
ExecReScanHashJoin(HashJoinState *node, ExprContext *exprCtxt)
{
	/*
	 * In a multi-batch join, we currently have to do rescans the hard way,
	 * primarily because batch temp files may have already been released. But
	 * if it's a single-batch join, and there is no parameter change for the
	 * inner subnode, then we can just re-use the existing hash table without
	 * rebuilding it.
	 */
	if (node->inner_hj_HashTable != NULL) //CSI3130: Modified Variable Name to inner
	{
		if (node->inner_hj_HashTable->nbatch == 1 &&
			((PlanState *) node)->righttree->chgParam == NULL)
		{
			/*
			 * okay to reuse the hash table; needn't rescan inner, either.
			 *
			 * What we do need to do is reset our state about the emptiness
			 * of the outer relation, so that the new scan of the outer will
			 * update it correctly if it turns out to be empty this time.
			 * (There's no harm in clearing it now because ExecHashJoin won't
			 * need the info.  In the other cases, where the hash table
			 * doesn't exist or we are destroying it, we leave this state
			 * alone because ExecHashJoin will need it the first time
			 * through.)
			 */
			node->hj_OuterNotEmpty = false;
		}
		else
		{
			/* must destroy and rebuild hash table */
			ExecHashTableDestroy(node->inner_hj_HashTable); //CSI3130: Variable modify to inner
			node->inner_hj_HashTable = NULL;

			/*
			 * if chgParam of subnode is not null then plan will be re-scanned
			 * by first ExecProcNode.
			 */
			if (((PlanState *) node)->righttree->chgParam == NULL)
				ExecReScan(((PlanState *) node)->righttree, exprCtxt);
		}
	}

	/* Always reset intra-tuple state */
	node->outer_hj_CurHashValue = 0; //CSI3130: Modified all variables to default values for both and inner and outer probe
	node->inner_hj_CurHashValue = 0;
	
	node->inner_hj_CurBucketNo = 0;
	node->outer_hj_CurBucketNo = 0;

	node->inner_hj_CurTuple = NULL;
	node->outer_hj_CurTuple = NULL;

	node->js.ps.ps_OuterTupleSlot = NULL;
	node->js.ps.ps_InnerTupleSlot = NULL;

	node->js.ps.ps_TupFromTlist = false;

	node->hj_NeedNewOuter = true;
	

	node->hj_MatchedOuter = false;


	
	node->hj_FirstOuterTupleSlot = NULL;
	node->hj_FirstInnerTupleSlot = NULL;

	/*
	 * if chgParam of subnode is not null then plan will be re-scanned by
	 * first ExecProcNode.
	 */
	if (((PlanState *) node)->lefttree->chgParam == NULL)
		ExecReScan(((PlanState *) node)->lefttree, exprCtxt);
}