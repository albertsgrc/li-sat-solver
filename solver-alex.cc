#include <iostream>
#include <stdlib.h>
#include <algorithm>
#include <vector>
#include <time.h>
using namespace std;

#define UNDEF -1
#define TRUE 1
#define FALSE 0

uint numVars;
uint numClauses;
vector<vector<int> > clauses;
vector<int> model;
vector<int> modelStack;
uint indexOfNextLitToPropagate;
uint decisionLevel;
//Mine
//Posicio i conte el indentificador de la clausula on apareix
//negatiu/positiu, respectivament
vector <vector <int> > clausNeg;
vector <vector <int> > clausPos;
vector<int> conflictiveNeg;
vector<int> conflictivePos;
int propagacions;
int decisions;
struct P{
    int literal;
    int aparicionsMin;
    P(){

    }
    P(int l,int ap){
        this->literal=l;
        this->aparicionsMin=ap;
    }
};
struct Literal{
    int literal;
    int conflictRate;
};

//funcio ordenacio
bool fOrdena(P a,P b){return a.aparicionsMin>b.aparicionsMin;}

void readClauses( ){
    // Skip comments
    char c = cin.get();
    while (c == 'c') {
        while (c != '\n') c = cin.get();
        c = cin.get();
    }
    // Read "cnf numVars numClauses"
    string aux;
    cin >> aux >> numVars >> numClauses;
    clauses.resize(numClauses);
    clausNeg.resize(numVars+1);
    clausPos.resize(numVars+1);
    conflictiveNeg.resize(numVars+1,0);
    conflictivePos.resize(numVars+1,0);
    // Read clauses
    for (uint i = 0; i < numClauses; ++i) {
        int lit;
        while (cin >> lit and lit != 0){
            if (lit<0) clausNeg[-lit].push_back(i);
            else clausPos[lit].push_back(i);
            clauses[i].push_back(lit);
        }
    }

}



int currentValueInModel(int lit){
    if (lit >= 0) return model[lit];
    else {
        if (model[-lit] == UNDEF) return UNDEF;
        else return 1 - model[-lit];
    }
}


void setLiteralToTrue(int lit){
    modelStack.push_back(lit);
    if (lit > 0) model[lit] = TRUE;
    else model[-lit] = FALSE;
}


bool propagateGivesConflict (vector<int>& nextLitsToPropagate) {
    ++propagacions;
    bool conflict = false;
    int size=nextLitsToPropagate.size();
    for (int i=0;not conflict and i<size;++i){
        vector<int> clausAViatjar;
        //si literal positiu-> propago per negatius per trobar conflictes mes rapidament
        if (nextLitsToPropagate[i]>0) clausAViatjar = clausNeg[nextLitsToPropagate[i]];
        else clausAViatjar = clausPos[abs(nextLitsToPropagate[i])];
        int aparicions = clausAViatjar.size();
        for (int j=0;j<aparicions;++j){
            bool someLitTrue = false;
            int numUndefs = 0;
            int lastLitUndef = 0;
            for (int k=0;not someLitTrue and k<clauses[clausAViatjar[j]].size();++k){
                int val = currentValueInModel(clauses[clausAViatjar[j]][k]);//kfkf
                if (val == TRUE) someLitTrue = true;
                else if (val == UNDEF){ ++numUndefs; lastLitUndef = clauses[clausAViatjar[j]][k];}
            }
            if (not someLitTrue and numUndefs == 0){
                conflict=true; // conflict! all lits false
                if (nextLitsToPropagate[i]>0) ++conflictivePos[nextLitsToPropagate[i]];
                else ++conflictiveNeg[-nextLitsToPropagate[i]];
            }
            else if (not someLitTrue and numUndefs == 1 and not conflict){
                //Propago el ultim indefinit trobat
                setLiteralToTrue(lastLitUndef);
                nextLitsToPropagate.push_back(lastLitUndef);
                ++size;
            }
        }
    }
    return conflict;
}




void backtrack(){
    uint i = modelStack.size() -1;
    int lit = 0;
    while (modelStack[i] != 0){ // 0 is the DL mark
        lit = modelStack[i];
        model[abs(lit)] = UNDEF;
        modelStack.pop_back();
        --i;
    }
    // at this point, lit is the last decision
    modelStack.pop_back(); // remove the DL mark
    --decisionLevel;
    setLiteralToTrue(-lit);  // reverse last decision
}

// Heuristic for finding the next decision literal:
int getNextDecisionLiteral(){
    ++decisions;
    int maxi=0;
    int ret=-1;
    for (int i=1;i<conflictivePos.size();++i){
        if (model[i]==UNDEF){
            if (conflictivePos[i]>maxi or conflictiveNeg[i]>maxi or ret==-1){
                maxi= max(conflictivePos[i],conflictiveNeg[i]);
                ret =i;
            }
        }
    }
    if (ret !=-1) return ret;
    else return 0; // reurns 0 when all literals are defined

}

void checkmodel(){
    for (int i = 0; i < numClauses; ++i){
        bool someTrue = false;
        for (int j = 0; not someTrue and j < clauses[i].size(); ++j)
            someTrue = (currentValueInModel(clauses[i][j]) == TRUE);
        if (not someTrue) {
            cout << "Error in model, clause is not satisfied:";
            for (int j = 0; j < clauses[i].size(); ++j) cout << clauses[i][j] << " ";
            cout << endl;
            exit(1);
        }
    }
}

int main(){
    clock_t t = clock();
    propagacions=0;
    decisions=0;
    readClauses(); // reads numVars, numClauses and clauses
    model.resize(numVars+1,UNDEF);
    decisionLevel = 0;

    // Take care of initial unit clauses, if any
    for (uint i = 0; i < numClauses; ++i)
        if (clauses[i].size() == 1) {
            int lit = clauses[i][0];
            int val = currentValueInModel(lit);
            if (val == FALSE) {cout << "UNSATISFIABLE" << endl; return 10;}
            else if (val == UNDEF) setLiteralToTrue(lit);
        }

    int decisionLit = getNextDecisionLiteral();
    modelStack.push_back(0);  // push mark indicating new DL
    ++decisionLevel;
    setLiteralToTrue(decisionLit);
    vector<int> litToPropagate(1);
    litToPropagate[0] = decisionLit;
    ++decisions;


    // DPLL algorithm
    while (true) {
        //Primer escollim el literal, despres el propaguem
        while ( propagateGivesConflict(litToPropagate) ) {
            if ( decisionLevel == 0) { cout <<"propagacions: " << propagacions << endl << "decisions: " << decisions <<  endl << (clock()-(float)t)/CLOCKS_PER_SEC << " " << decisions<< " " << propagacions/((clock()-(float)t)/CLOCKS_PER_SEC) << " UNSATISFIABLE" << endl; return 10; }
            backtrack();
            litToPropagate[0] = modelStack[modelStack.size()-1];
        }
        decisionLit= getNextDecisionLiteral();
        if (decisionLit == 0) { checkmodel();cout <<(clock()-(float)t)/CLOCKS_PER_SEC << " " << decisions<< " " << propagacions/((clock()-(float)t)/CLOCKS_PER_SEC) << " SATISFIABLE" << endl;return 20; }
        // start new decision level:
        modelStack.push_back(0);  // push mark indicating new DL
        ++decisionLevel;
        setLiteralToTrue(decisionLit);    // now push decisionLit on top of the mark
        litToPropagate[0] = decisionLit;
    }
}
