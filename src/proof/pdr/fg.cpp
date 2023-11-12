#include <bits/stdc++.h>
using namespace std;

map<pair<vector<int>, int>, set<int>> failure_push;

extern "C"
{
#include "pdrInt.h"
#include "misc/vec/vec.h"
    int pf_succ, pf_fail;
    size_t fg_down_succ, fg_down_fail;

    int sat_var(Pdr_Man_t *p, int k, int lit)
    {
        Aig_Obj_t *pObj = Saig_ManLi(p->pAig, Abc_Lit2Var(lit));
        if (p->pPars->fMonoCnf)
            return p->pCnf1->pVarNums[Aig_ObjId(pObj)];
        Vec_Int_t *vId2Vars = p->pvId2Vars + Aig_ObjId(pObj);
        int iVar = Vec_IntGetEntry(vId2Vars, k);
        if (iVar == 0)
            return -1;
        return iVar;
    }

    Pdr_Set_t *fg_Pdr_SetCreate(vector<int> &vLits)
    {
        Pdr_Set_t *p;
        int i;
        p = (Pdr_Set_t *)ABC_ALLOC(char, sizeof(Pdr_Set_t) + vLits.size() * sizeof(int));
        p->nLits = vLits.size();
        p->nTotal = vLits.size();
        p->nRefs = 1;
        p->Sign = 0;
        for (i = 0; i < p->nLits; i++)
        {
            p->Lits[i] = vLits[i];
            p->Sign |= ((word)1 << (p->Lits[i] % 63));
        }
        Vec_IntSelectSort(p->Lits, p->nLits);
        return p;
    }

    void clean_ctp()
    {
        failure_push.clear();
    }

    void record_ctp(Pdr_Man_t *p, int k, Pdr_Set_t *cube)
    {
        sat_solver *pSat = Pdr_ManSolver(p, k);
        set<int> ctp;
        for (int i = 0; i < Saig_ManRegNum(p->pAig); ++i)
        {
            int iVar = sat_var(p, k, i * 2);
            if (iVar == -1)
                continue;
            int val = sat_solver_var_value(pSat, iVar);
            ctp.insert(Abc_Var2Lit(i, val == 0));
        }
        vector<int> fail_lemma;
        for (int i = 0; i < cube->nLits; ++i)
        {
            if (ctp.find(cube->Lits[i]) == ctp.end())
                abort();
            fail_lemma.push_back(cube->Lits[i]);
        }
        sort(fail_lemma.begin(), fail_lemma.end());
        failure_push[make_pair(fail_lemma, k)] = ctp;
    }

    vector<Pdr_Set_t *> parent_lemmas(Pdr_Man_t *p, int k, Pdr_Set_t *pCubeMin)
    {
        vector<Pdr_Set_t *> res;
        Pdr_Set_t *pThis;
        int i;
        Vec_PtrForEachEntry(Pdr_Set_t *, Vec_VecEntry(p->vClauses, k), pThis, i)
        {
            if (Pdr_SetContains(pCubeMin, pThis))
                res.push_back(Pdr_SetDup(pThis));
        }
        return res;
    }

    int fg_ZPdr_ManDown(Pdr_Man_t *p, int k, Pdr_Set_t **ppCube, Pdr_Set_t *pPred, Hash_Int_t *keep, Pdr_Set_t *pIndCube, int *added, vector<int> &diff, set<int> &black)
    {
        set<int> black_clone(black);
        int RetValue = 0, CtgRetValue, i, ctgAttempts, l, micResult;
        int kMax = Vec_PtrSize(p->vSolvers) - 1;
        Pdr_Set_t *pCubeTmp, *pCubeMin, *pCtg;
        bool changed = false;
        while (RetValue == 0)
        {
            ctgAttempts = 0;
            while (p->pPars->fCtgs && RetValue == 0 && k > 1 && ctgAttempts < 3)
            {
                pCtg = Pdr_SetDup(pPred);
                // Check CTG for inductiveness
                if (Pdr_SetIsInit(pCtg, -1))
                {
                    Pdr_SetDeref(pCtg);
                    break;
                }
                if (*added == 0)
                {
                    for (i = 1; i <= k; i++)
                        Pdr_ManSolverAddClause(p, i, pIndCube);
                    *added = 1;
                }
                ctgAttempts++;
                CtgRetValue = Pdr_ManCheckCube(p, k - 1, pCtg, NULL, p->pPars->nConfLimit, 0, 1);
                if (CtgRetValue != 1)
                {
                    Pdr_SetDeref(pCtg);
                    break;
                }
                pCubeMin = Pdr_ManReduceClause(p, k - 1, pCtg);
                if (pCubeMin == NULL)
                    pCubeMin = Pdr_SetDup(pCtg);

                for (l = k; l < kMax; l++)
                    if (!Pdr_ManCheckCube(p, l, pCubeMin, NULL, 0, 0, 1))
                        break;
                micResult = ZPdr_ManSimpleMic(p, l - 1, &pCubeMin);
                assert(micResult != -1);

                // add new clause
                if (p->pPars->fVeryVerbose)
                {
                    Abc_Print(1, "Adding cube ");
                    Pdr_SetPrint(stdout, pCubeMin, Aig_ManRegNum(p->pAig), NULL);
                    Abc_Print(1, " to frame %d.\n", l);
                }
                // set priority flops
                for (i = 0; i < pCubeMin->nLits; i++)
                {
                    assert(pCubeMin->Lits[i] >= 0);
                    assert((pCubeMin->Lits[i] / 2) < Aig_ManRegNum(p->pAig));
                    if ((Vec_IntEntry(p->vPrio, pCubeMin->Lits[i] / 2) >> p->nPrioShift) == 0)
                        p->nAbsFlops++;
                    Vec_IntAddToEntry(p->vPrio, pCubeMin->Lits[i] / 2, 1 << p->nPrioShift);
                }

                Vec_VecPush(p->vClauses, l, pCubeMin); // consume ref
                p->nCubes++;
                // add clause
                for (i = 1; i <= l; i++)
                    Pdr_ManSolverAddClause(p, i, pCubeMin);
                Pdr_SetDeref(pPred);
                RetValue = Pdr_ManCheckCube(p, k, *ppCube, &pPred, p->pPars->nConfLimit, 0, 1);
                assert(RetValue >= 0);
                Pdr_SetDeref(pCtg);
                if (RetValue == 1)
                {
                    Pdr_Set_t *core = Pdr_ManReduceClause(p, k, *ppCube);
                    if (core != NULL)
                    {
                        Pdr_SetDeref(*ppCube);
                        *ppCube = core;
                    }
                    // printf ("IT'S A ONE\n");
                    return 1;
                }
                else if (!changed)
                {
                    black = black_clone;
                    sat_solver *pSat = Pdr_ManSolver(p, k);
                    for (int di = 0; di < diff.size(); ++di)
                    {
                        int iVar = sat_var(p, k, diff[di]);
                        if (iVar == -1)
                        {
                            black.insert(diff[di]);
                            continue;
                        }
                        int val = sat_solver_var_value(pSat, iVar);
                        if (val != Abc_LitIsCompl(diff[di]))
                            black.insert(diff[di]);
                    }
                }
            }

            // join
            if (p->pPars->fVeryVerbose)
            {
                printf("Cube:\n");
                ZPdr_SetPrint(*ppCube);
                printf("\nPred:\n");
                ZPdr_SetPrint(pPred);
            }
            changed = true;
            *ppCube = ZPdr_SetIntersection(pCubeTmp = *ppCube, pPred, keep);
            Pdr_SetDeref(pCubeTmp);
            Pdr_SetDeref(pPred);
            if (*ppCube == NULL)
                return 0;
            if (p->pPars->fVeryVerbose)
            {
                printf("Intersection:\n");
                ZPdr_SetPrint(*ppCube);
            }
            if (Pdr_SetIsInit(*ppCube, -1))
            {
                if (p->pPars->fVeryVerbose)
                    printf("Failed initiation\n");
                return 0;
            }
            RetValue = Pdr_ManCheckCube(p, k, *ppCube, &pPred, p->pPars->nConfLimit, 0, 1);
            if (RetValue == -1)
                return -1;
            if (RetValue == 1)
            {
                // printf ("*********IT'S A ONE\n");
                break;
            }
            if (RetValue == 0 && (*ppCube)->nLits == 1)
            {
                Pdr_SetDeref(pPred); // fixed memory leak
                // A workaround for the incomplete assignment returned by the SAT
                // solver
                return 0;
            }
        }
        return 1;
    }

    bool fg_ctg_down(Pdr_Man_t *p, int k, Pdr_Set_t **pCube, Hash_Int_t *keep, vector<int> &diff, set<int> &black)
    {
        Pdr_Set_t *pPred = NULL;
        if (Pdr_ManCheckCube(p, k, *pCube, &pPred, p->pPars->nConfLimit, 1, 1))
        {
            Pdr_Set_t *core = Pdr_ManReduceClause(p, k, *pCube);
            if (core != NULL)
            {
                Pdr_SetDeref(*pCube);
                *pCube = core;
            }
            return true;
        }
        else
        {
            Pdr_Set_t *pCubeCpy = Pdr_SetDup(*pCube);
            int added = 1;
            if (fg_ZPdr_ManDown(p, k, &pCubeCpy, pPred, keep, NULL, &added, diff, black))
            {
                Pdr_SetDeref(*pCube);
                *pCube = pCubeCpy;
                return true;
            }
            else
            {
                if (pCubeCpy)
                    Pdr_SetDeref(pCubeCpy);
                return false;
            }
        }
    }

    bool fg_simple_down(Pdr_Man_t *p, int k, Pdr_Set_t **pCube)
    {
        if (Pdr_ManCheckCube(p, k, *pCube, NULL, p->pPars->nConfLimit, 1, 1))
        {
            Pdr_Set_t *core = Pdr_ManReduceClause(p, k, *pCube);
            if (core != NULL)
            {
                Pdr_SetDeref(*pCube);
                *pCube = core;
            }
            return true;
        }
        return false;
    }

    Pdr_Set_t *fg(Pdr_Man_t *p, int k, Pdr_Set_t *pCubeMin, int simple)
    {
        // if (!simple)
        // {
        //     cout << "fg ";
        //     for (int i = 0; i < pCubeMin->nLits; ++i)
        //         cout << pCubeMin->Lits[i] << " ";
        //     cout << endl;
        // }
        Pdr_Set_t *res = NULL;
        size_t sum = fg_down_fail + fg_down_succ;
        if (sum > 1000 && 20 * fg_down_succ < sum)
            return res;
        Hash_Int_t *keep = NULL;
        vector<Pdr_Set_t *> parents = parent_lemmas(p, k, pCubeMin);
        for (auto &pa : parents)
        {
            if (Pdr_SetContains(pa, pCubeMin))
            {
                if (pa->nLits != pCubeMin->nLits)
                    abort();
                res = pCubeMin;
                goto cleanup;
            }
        }
        for (auto &pa : parents)
        {
            // if (!simple)
            // {
            //     cout << "pa ";
            //     for (int i = 0; i < pa->nLits; ++i)
            //         cout << pa->Lits[i] << " ";
            //     cout << endl;
            // }
            vector<int> vp;
            keep = Hash_IntAlloc(1);
            for (int i = 0; i < pa->nLits; ++i)
            {
                Hash_IntWriteEntry(keep, pa->Lits[i], 0);
                vp.push_back(pa->Lits[i]);
            }
            auto t = failure_push.find(make_pair(vp, k));
            if (t == failure_push.end())
                continue;
            vector<int> diff;
            for (int i = 0; i < pCubeMin->nLits; ++i)
            {
                if (t->second.find(Abc_LitNot(pCubeMin->Lits[i])) != t->second.end())
                {
                    diff.push_back(pCubeMin->Lits[i]);
                }
            }
            sort(diff.begin(), diff.end(), [&](int a, int b)
                 { return Vec_IntEntry(p->vPrio, Abc_Lit2Var(a)) > Vec_IntEntry(p->vPrio, Abc_Lit2Var(b)); });
            // cout << "diff ";
            // for (int i = 0; i < diff.size(); ++i)
            //     cout << diff[i] << " ";
            // cout << endl;
            set<int> black;
            int num_pred = 0;
            if (diff.size())
            {
                for (int di = 0; di < diff.size(); ++di)
                {
                    if (black.find(diff[di]) != black.end())
                        continue;
                    vp.push_back(diff[di]);
                    Pdr_Set_t *Cond = fg_Pdr_SetCreate(vp);
                    num_pred += 1;
                    if (num_pred > 3)
                        break;
                    if (simple)
                    {
                        if (fg_simple_down(p, k, &Cond))
                        {
                            res = Cond;
                            fg_down_succ += 1;
                            // cout << "success" << endl;
                            goto cleanup;
                        }
                    }
                    else
                    {
                        if (fg_ctg_down(p, k, &Cond, keep, diff, black))
                        {
                            res = Cond;
                            // cout << "success" << endl;
                            fg_down_succ += 1;
                            goto cleanup;
                        }
                    }
                    fg_down_fail += 1;
                    // cout << "failed" << endl;
                    vp.pop_back();
                    Pdr_SetDeref(Cond);
                    if (simple)
                    {
                        sat_solver *pSat = Pdr_ManSolver(p, k);
                        for (int dj = 0; dj < diff.size(); ++dj)
                        {
                            int iVar = sat_var(p, k, diff[dj]);
                            if (iVar == -1)
                            {
                                black.insert(diff[dj]);
                                continue;
                            }
                            int val = sat_solver_var_value(pSat, iVar);
                            if (val != Abc_LitIsCompl(diff[dj]))
                                black.insert(diff[dj]);
                        }
                    }
                }
            }
            else
            {
                Pdr_Set_t *pad = Pdr_SetDup(pa);
                if (fg_simple_down(p, k, &pad))
                {
                    res = pad;
                    // cout << "try p success" << endl;
                    goto cleanup;
                }
                record_ctp(p, k, pad);
                Pdr_SetDeref(pad);
            }
            if (keep)
            {
                Hash_IntFree(keep);
                keep = NULL;
            }
        }
    cleanup:
        if (keep)
            Hash_IntFree(keep);
        for (auto &p : parents)
        {
            Pdr_SetDeref(p);
        }
        return res;
    }
}