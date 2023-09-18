#include "pic3.h"
#include "pdrInt.h"
#include "pdr.h"
#include "aig/ioa/ioa.h"

static void *pic3abc_create()
{
	Pdr_Par_t *pars = ABC_CALLOC(Pdr_Par_t, 1);
	Pdr_ManSetDefaultParams(pars);
	pars->nRandomSeed = rand();
	Pdr_Man_t *pdr = ABC_CALLOC(Pdr_Man_t, 1);
	pdr->pPars = pars;
	return pdr;
}

static void pic3abc_set_model(void *this, char *model)
{
	Pdr_Man_t *p = this;
	Aig_Man_t *aig = Ioa_ReadAiger(model, 1);
	p->pAig = aig;
}

static void pic3abc_set_synchronizer(void *this, struct Synchronizer synchronizer)
{
	Pdr_Man_t *p = this;
	p->pic3.synchronizer = synchronizer;
}

static void pic3abc_set_random_seed(void *this, int random)
{
	Pdr_Man_t *p = this;
	p->pPars->nRandomSeed = random;
}

static void pic3abc_diversify(void *this, int rank, int size)
{
	Pdr_Man_t *p = this;
	if (rank == 0) {
		p->pPars->fVerbose = 1;
	}
}

static int pic3abc_solve(void *this)
{
	extern int Pdr_ManSolveInt(Pdr_Man_t * p);
	Pdr_Man_t *p = this;
	printf("%d\n", p->pPars->nRandomSeed);
	pic3abc_start(p, NULL);
	int RetValue = Pdr_ManSolveInt(p);
	return RetValue;
}

struct Pic3Interface pic3abc = {
	.create = pic3abc_create,
	.set_model = pic3abc_set_model,
	.set_synchronizer = pic3abc_set_synchronizer,
	.set_random_seed = pic3abc_set_random_seed,
	.diversify = pic3abc_diversify,
	.solve = pic3abc_solve,
};

void pic3abc_start(Pdr_Man_t *p, Vec_Int_t *vPrioInit)
{
	Pdr_Par_t *pPars = p->pPars;
	Aig_Man_t *pAig = p->pAig;
	p->pGia = (pPars->fFlopPrio || p->pPars->fNewXSim || p->pPars->fUseAbs) ? Gia_ManFromAigSimple(pAig) : NULL;
	p->vSolvers = Vec_PtrAlloc(0);
	p->vClauses = Vec_VecAlloc(0);
	p->pQueue = NULL;
	p->pOrder = ABC_ALLOC(int, Aig_ManRegNum(pAig));
	p->vActVars = Vec_IntAlloc(256);
	if (!p->pPars->fMonoCnf)
		p->vVLits = Vec_WecStart(1 + Abc_MaxInt(1, Aig_ManLevels(pAig)));
	// internal use
	p->nPrioShift = Abc_Base2Log(Aig_ManRegNum(pAig));
	if (vPrioInit)
		p->vPrio = vPrioInit;
	else if (pPars->fFlopPrio)
		p->vPrio = Pdr_ManDeriveFlopPriorities2(p->pGia, 1);
	//    else if ( p->pPars->fNewXSim )
	//        p->vPrio = Vec_IntStartNatural( Aig_ManRegNum(pAig) );
	else
		p->vPrio = Vec_IntStart(Aig_ManRegNum(pAig));
	p->vLits = Vec_IntAlloc(100); // array of literals
	p->vCiObjs = Vec_IntAlloc(100); // cone leaves
	p->vCoObjs = Vec_IntAlloc(100); // cone roots
	p->vCiVals = Vec_IntAlloc(100); // cone leaf values
	p->vCoVals = Vec_IntAlloc(100); // cone root values
	p->vNodes = Vec_IntAlloc(100); // cone nodes
	p->vUndo = Vec_IntAlloc(100); // cone undos
	p->vVisits = Vec_IntAlloc(100); // intermediate
	p->vCi2Rem = Vec_IntAlloc(100); // CIs to be removed
	p->vRes = Vec_IntAlloc(100); // final result
	p->pCnfMan = Cnf_ManStart();
	// ternary simulation
	p->pTxs3 = pPars->fNewXSim ? Txs3_ManStart(p, pAig, p->vPrio) : NULL;
	// additional AIG data-members
	if (pAig->pFanData == NULL)
		Aig_ManFanoutStart(pAig);
	if (pAig->pTerSimData == NULL)
		pAig->pTerSimData = ABC_CALLOC(unsigned, 1 + (Aig_ManObjNumMax(pAig) / 16));
	// time spent on each outputs
	if (pPars->nTimeOutOne) {
		int i;
		p->pTime4Outs = ABC_ALLOC(abctime, Saig_ManPoNum(pAig));
		for (i = 0; i < Saig_ManPoNum(pAig); i++)
			p->pTime4Outs[i] = pPars->nTimeOutOne * CLOCKS_PER_SEC / 1000 + 1;
	}
	if (p->pPars->fSolveAll) {
		p->vCexes = Vec_PtrStart(Saig_ManPoNum(p->pAig));
		p->pPars->vOutMap = Vec_IntAlloc(Saig_ManPoNum(pAig));
		Vec_IntFill(p->pPars->vOutMap, Saig_ManPoNum(pAig), -2);
	}
}

void pic3_share_lemma(Pdr_Man_t *p, int k, Pdr_Set_t *cube)
{
	Aig_Obj_t *pObj;
	int *lits = ABC_CALLOC(int, cube->nLits);
	int offset = (p->pAig->nTruePis + 1) * 2;
	for (int i = 0; i < cube->nLits; i++) {
		assert(cube->Lits[i] != -1);
		lits[i] = cube->Lits[i] + offset;
	}
	struct Lemma lemma = {
		.frame_idx = k,
		.lits = lits,
		.num_lit = cube->nLits,
	};
	p->pic3.synchronizer.share_lemma(p->pic3.synchronizer.data, lemma);
}

void pic3_handle_message(Pdr_Man_t *p)
{
	int offset = (p->pAig->nTruePis + 1) * 2;
	while (true) {
		struct Message *message = p->pic3.synchronizer.receive_message(p->pic3.synchronizer.data);
		if (message == NULL) {
			break;
		}
		if (message->type == Lemma) {
			struct Lemma lemma = message->lemma;
			for (int i = 0; i < lemma.num_lit; i++) {
				lemma.lits[i] -= offset;
			}
			Vec_Int_t lits = { .nCap = lemma.num_lit, .nSize = lemma.num_lit, .pArray = lemma.lits };
			Vec_Int_t *pilits = Vec_IntAlloc(0);
			Pdr_Set_t *cube = Pdr_SetCreate(&lits, pilits);
			ABC_FREE(lits.pArray);
			Vec_IntFree(pilits);
			if (Pdr_ManCheckContainment(p, lemma.frame_idx, cube)) {
				Pdr_SetDeref(cube);
				continue;
			} else {
				if (Vec_PtrSize(p->vClauses) > lemma.frame_idx) {
					Vec_VecPush(p->vClauses, lemma.frame_idx, cube);
					for (int i = 1; i <= lemma.frame_idx; i++)
						Pdr_ManSolverAddClause(p, i, cube);
				} else {
					abort();
				}
			}
		} else if (message->type == FrameBlocked) {
		}
	}
}