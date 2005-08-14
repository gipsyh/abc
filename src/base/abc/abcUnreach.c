/**CFile****************************************************************

  FileName    [abcUnreach.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Network and node package.]

  Synopsis    [Computes unreachable states for small benchmarks.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: abcUnreach.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "abc.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

static DdNode *    Abc_NtkTransitionRelation( DdManager * dd, Abc_Ntk_t * pNtk, int fVerbose );
static DdNode *    Abc_NtkInitStateAndVarMap( DdManager * dd, Abc_Ntk_t * pNtk, int fVerbose );
static DdNode *    Abc_NtkComputeUnreachable( DdManager * dd, Abc_Ntk_t * pNtk, DdNode * bRelation, DdNode * bInitial, bool fVerbose );
static Abc_Ntk_t * Abc_NtkConstructExdc     ( DdManager * dd, Abc_Ntk_t * pNtk, DdNode * bUnreach );

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFITIONS                           ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Extracts sequential DCs of the network.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkExtractSequentialDcs( Abc_Ntk_t * pNtk, bool fVerbose )
{
    int fCheck   = 1;
    int fReorder = 1;
    DdManager * dd;
    DdNode * bRelation, * bInitial, * bUnreach;

    // remove EXDC network if present
    if ( pNtk->pExdc )
    {
        Abc_NtkDelete( pNtk->pExdc );
        pNtk->pExdc = NULL; 
    }

    // compute the global BDDs of the latches
    dd = Abc_NtkGlobalBdds( pNtk, 1 );    
    if ( dd == NULL )
        return 0;
    if ( fVerbose )
        printf( "The shared BDD size is %d nodes.\n", Cudd_ReadKeys(dd) - Cudd_ReadDead(dd) );

    // create the transition relation (dereferenced global BDDs)
    bRelation = Abc_NtkTransitionRelation( dd, pNtk, fVerbose );              Cudd_Ref( bRelation );
    // create the initial state and the variable map
    bInitial  = Abc_NtkInitStateAndVarMap( dd, pNtk, fVerbose );              Cudd_Ref( bInitial );
    // compute the unreachable states
    bUnreach  = Abc_NtkComputeUnreachable( dd, pNtk, bRelation, bInitial, fVerbose );   Cudd_Ref( bUnreach );
    Cudd_RecursiveDeref( dd, bRelation );
    Cudd_RecursiveDeref( dd, bInitial );

    // reorder and disable reordering
    if ( fReorder )
    {
        if ( fVerbose )
            fprintf( stdout, "BDD nodes in the unreachable states before reordering %d.\n", Cudd_DagSize(bUnreach) );
        Cudd_ReduceHeap( dd, CUDD_REORDER_SYMM_SIFT, 1 );
        Cudd_AutodynDisable( dd );
        if ( fVerbose )
            fprintf( stdout, "BDD nodes in the unreachable states after reordering %d.\n", Cudd_DagSize(bUnreach) );
    }

    // allocate ZDD variables
    Cudd_zddVarsFromBddVars( dd, 2 );
    // create the EXDC network representing the unreachable states
    pNtk->pExdc = Abc_NtkConstructExdc( dd, pNtk, bUnreach );
    Cudd_RecursiveDeref( dd, bUnreach );
    Extra_StopManager( dd );

    // make sure that everything is okay
    if ( fCheck && !Abc_NtkCheck( pNtk->pExdc ) )
    {
        printf( "Abc_NtkExtractSequentialDcs: The network check has failed.\n" );
        Abc_NtkDelete( pNtk->pExdc );
        return 0;
    }
    return 1;
}

/**Function*************************************************************

  Synopsis    [Computes the transition relation of the network.]

  Description [Assumes that the global BDDs are computed.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
DdNode * Abc_NtkTransitionRelation( DdManager * dd, Abc_Ntk_t * pNtk, int fVerbose )
{
    DdNode * bRel, * bTemp, * bProd, * bVar, * bInputs;
    Abc_Obj_t * pNode;
    int fReorder = 1;
    int i;

    // extand the BDD manager to represent NS variables
    assert( dd->size == Abc_NtkCiNum(pNtk) );
    Cudd_bddIthVar( dd, Abc_NtkCiNum(pNtk) + Abc_NtkLatchNum(pNtk) - 1 );

    // enable reordering
    if ( fReorder )
        Cudd_AutodynEnable( dd, CUDD_REORDER_SYMM_SIFT );
    else
        Cudd_AutodynDisable( dd );

    // compute the transition relation
    bRel = b1;   Cudd_Ref( bRel );
    Abc_NtkForEachLatch( pNtk, pNode, i )
    {
        bVar  = Cudd_bddIthVar( dd, Abc_NtkCiNum(pNtk) + i );
        bProd = Cudd_bddXnor( dd, bVar, (DdNode *)pNode->pNext );   Cudd_Ref( bProd );
        bRel  = Cudd_bddAnd( dd, bTemp = bRel, bProd );             Cudd_Ref( bRel );
        Cudd_RecursiveDeref( dd, bTemp ); 
        Cudd_RecursiveDeref( dd, bProd ); 
    }
    // free the global BDDs
    Abc_NtkFreeGlobalBdds( dd, pNtk );

    // quantify the PI variables
    bInputs = Extra_bddComputeRangeCube( dd, 0, Abc_NtkPiNum(pNtk) );    Cudd_Ref( bInputs );
    bRel    = Cudd_bddExistAbstract( dd, bTemp = bRel, bInputs );    Cudd_Ref( bRel );
    Cudd_RecursiveDeref( dd, bTemp ); 
    Cudd_RecursiveDeref( dd, bInputs ); 

    // reorder and disable reordering
    if ( fReorder )
    {
        if ( fVerbose )
            fprintf( stdout, "BDD nodes in the transition relation before reordering %d.\n", Cudd_DagSize(bRel) );
        Cudd_ReduceHeap( dd, CUDD_REORDER_SYMM_SIFT, 100 );
        Cudd_AutodynDisable( dd );
        if ( fVerbose )
            fprintf( stdout, "BDD nodes in the transition relation after reordering %d.\n", Cudd_DagSize(bRel) );
    }
    Cudd_Deref( bRel );
    return bRel;
}

/**Function*************************************************************

  Synopsis    [Computes the initial state and sets up the variable map.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
DdNode * Abc_NtkInitStateAndVarMap( DdManager * dd, Abc_Ntk_t * pNtk, int fVerbose )
{
    DdNode ** pbVarsX, ** pbVarsY;
    DdNode * bTemp, * bProd, * bVar;
    Abc_Obj_t * pLatch;
    int i;

    // set the variable mapping for Cudd_bddVarMap()
    pbVarsX = ALLOC( DdNode *, dd->size );
    pbVarsY = ALLOC( DdNode *, dd->size );
    bProd = b1;         Cudd_Ref( bProd );
    Abc_NtkForEachLatch( pNtk, pLatch, i )
    {
        pbVarsX[i] = dd->vars[ Abc_NtkPiNum(pNtk) + i ];
        pbVarsY[i] = dd->vars[ Abc_NtkCiNum(pNtk) + i ];
        // get the initial value of the latch
        bVar  = Cudd_NotCond( pbVarsX[i], !Abc_LatchIsInit1(pLatch) );
        bProd = Cudd_bddAnd( dd, bTemp = bProd, bVar );      Cudd_Ref( bProd );
        Cudd_RecursiveDeref( dd, bTemp ); 
    }
    Cudd_SetVarMap( dd, pbVarsX, pbVarsY, Abc_NtkLatchNum(pNtk) );
    FREE( pbVarsX );
    FREE( pbVarsY );

    Cudd_Deref( bProd );
    return bProd;
}

/**Function*************************************************************

  Synopsis    [Computes the set of unreachable states.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
DdNode * Abc_NtkComputeUnreachable( DdManager * dd, Abc_Ntk_t * pNtk, DdNode * bTrans, DdNode * bInitial, bool fVerbose )
{
    DdNode * bRelation, * bReached, * bCubeCs;
    DdNode * bCurrent, * bNext, * bTemp;
    int nIters;

    // perform reachability analisys
    bCurrent  = bInitial;   Cudd_Ref( bCurrent );
    bReached  = bInitial;   Cudd_Ref( bReached );
    bRelation = bTrans;     Cudd_Ref( bRelation );
    bCubeCs   = Extra_bddComputeRangeCube( dd, Abc_NtkPiNum(pNtk), Abc_NtkCiNum(pNtk) );    Cudd_Ref( bCubeCs );
    for ( nIters = 1; ; nIters++ )
    {
        // compute the next states
        bNext = Cudd_bddAndAbstract( dd, bRelation, bCurrent, bCubeCs );  Cudd_Ref( bNext );
        Cudd_RecursiveDeref( dd, bCurrent );
        // remap these states into the current state vars
        bNext = Cudd_bddVarMap( dd, bTemp = bNext );                      Cudd_Ref( bNext );
        Cudd_RecursiveDeref( dd, bTemp );
        // check if there are any new states
        if ( Cudd_bddLeq( dd, bNext, bReached ) )
            break;
        // get the new states
        bCurrent = Cudd_bddAnd( dd, bNext, Cudd_Not(bReached) );          Cudd_Ref( bCurrent );
        // minimize the new states with the reached states
//        bCurrent = Cudd_bddConstrain( dd, bTemp = bCurrent, Cudd_Not(bReached) ); Cudd_Ref( bCurrent );
//        Cudd_RecursiveDeref( dd, bTemp );
        // add to the reached states
        bReached = Cudd_bddOr( dd, bTemp = bReached, bNext );             Cudd_Ref( bReached );
        Cudd_RecursiveDeref( dd, bTemp );
        Cudd_RecursiveDeref( dd, bNext );
        // minimize the transition relation
//        bRelation = Cudd_bddConstrain( dd, bTemp = bRelation, Cudd_Not(bReached) ); Cudd_Ref( bRelation );
//        Cudd_RecursiveDeref( dd, bTemp );
    }
    Cudd_RecursiveDeref( dd, bRelation );
    Cudd_RecursiveDeref( dd, bCubeCs );
    Cudd_RecursiveDeref( dd, bNext );
    // report the stats
    if ( fVerbose )
    {
    fprintf( stdout, "Reachability analysis completed in %d iterations.\n", nIters );
    fprintf( stdout, "The number of minterms in the reachable state set = %d.\n", 
                        (int)Cudd_CountMinterm(dd, bReached, Abc_NtkLatchNum(pNtk) ) ); 
    }
//PRB( dd, bReached );
    Cudd_Deref( bReached );
    return Cudd_Not( bReached );
}

/**Function*************************************************************

  Synopsis    [Creates the EXDC network.]

  Description [The set of unreachable states depends on CS variables.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Abc_Ntk_t * Abc_NtkConstructExdc( DdManager * dd, Abc_Ntk_t * pNtk, DdNode * bUnreach )
{
    Abc_Ntk_t * pNtkNew;
    Abc_Obj_t * pNode, * pNodeNew;
    int * pPermute;
    int i;

    // start the new network
    pNtkNew = Abc_NtkAlloc( ABC_NTK_LOGIC_BDD );
    // create PIs corresponding to LOs
    Abc_NtkForEachLatch( pNtk, pNode, i )
        pNode->pCopy = Abc_NtkCreatePi(pNtkNew);

    // create a new node
    pNodeNew = Abc_NtkCreateNode(pNtkNew);
    // add the fanins corresponding to latch outputs
    Abc_NtkForEachLatch( pNtk, pNode, i )
        Abc_ObjAddFanin( pNodeNew, pNode->pCopy );

    // create the logic function
    pPermute = ALLOC( int, dd->size );
    for ( i = 0; i < dd->size; i++ )
        pPermute[i] = -1;
    Abc_NtkForEachLatch( pNtk, pNode, i )
        pPermute[Abc_NtkPiNum(pNtk) + i] = i;
    // remap the functions
    pNodeNew->pData = Extra_TransferPermute( dd, pNtkNew->pManFunc, bUnreach, pPermute );   Cudd_Ref( pNodeNew->pData );
    free( pPermute );
    Abc_NodeMinimumBase( pNodeNew );

    // make the new node drive all the COs
    Abc_NtkForEachCo( pNtk, pNode, i )
        Abc_ObjAddFanin( Abc_NtkCreatePo(pNtkNew), pNodeNew );

    // copy the CI/CO names
    Abc_NtkForEachLatch( pNtk, pNode, i )
        Abc_NtkLogicStoreName( Abc_NtkPi(pNtkNew,i), Abc_ObjName(pNode) );
    Abc_NtkForEachPo( pNtk, pNode, i )
        Abc_NtkLogicStoreName( Abc_NtkPo(pNtkNew,i), Abc_ObjName(pNode) );
    Abc_NtkForEachLatch( pNtk, pNode, i )
        Abc_NtkLogicStoreName( Abc_NtkCo(pNtkNew,Abc_NtkPoNum(pNtk) + i), Abc_ObjName(pNode) );

    // transform the network to the SOP representation
    Abc_NtkBddToSop( pNtkNew );
    return pNtkNew;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


