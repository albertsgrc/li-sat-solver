#include <iostream>
#include <stdlib.h>
#include <algorithm>
#include <vector>

#include <unordered_set>
using namespace std;

#define UNDEF -1
#define TRUE 1
#define FALSE 0

const int NO_DECISION_LITERAL = 0;
const int UPPER_IS_DECISION_MARK = 0;

// Nombre de variables del test
uint n_vars;

// Nombre de clàusules del test
uint n_clauses;

// Vector on cada element és una clàusula,
// que és alhora un vector de literals
vector<vector<int> > clauses;

// Interpretació de la fórmula
// Quan una variable no s'ha propagat encara
// El seu valor en l'array es indefinit
// Només hi ha un valor per variable
vector<int> model;

// Ni puta idea
vector<int> model_stack;

// Index del següent literal que s'ha decidit propagar
// en la model_stack
uint ind_next_lit_to_propagate;

// Nombre de decisions que s'han pres fins al moment
uint decision_level;


/**
 My datastructures
**/

vector<vector<int>> clauses_pos;
vector<vector<int>> clauses_neg;

void skip_comments() {
    // Skip comments
    char c = cin.get();
    while (c == 'c') {
        while (c != '\n') c = cin.get();
        c = cin.get();
    }
}

void read_header() {
    string aux;
    cin >> aux >> n_vars >> n_clauses;
    clauses.resize(n_clauses); 
}

void read_clauses() {
    for (uint i = 0; i < n_clauses; ++i) {
        int lit;
        while (cin >> lit and lit != 0) clauses[i].push_back(lit);
    }
}

void read_clauses_file() {
    skip_comments();
     
    read_header();

    read_clauses();    
}


void assign_clauses_sign_info() {
    for (int var = 1; var <= n_vars; ++var) {
        for (int i = 0; i < n_clauses; ++i) {
            for (int j = 0; j < clauses[i].size(); ++j) {
                int lit = clauses[i][j];
                
                if (lit > 0) {
                    if (lit == var) {
                        clauses_pos[var].push_back(i);
                        break;
                    }
                } 
                else if (lit == -var) {
                    clauses_neg[var].push_back(i);
                    break;   
                }
            }
        }
    }
}

void init_data_structures() {
    read_clauses_file();

    int greatest_var = n_vars + 1;
    model.resize(greatest_var,UNDEF);

    clauses_pos.resize(greatest_var);
    clauses_neg.resize(greatest_var);

    assign_clauses_sign_info();

    ind_next_lit_to_propagate = 0;  
    decision_level = 0;
}


inline int current_value_in_model(int lit) {
    if (lit >= 0) return model[lit];
    else {
        if (model[-lit] == UNDEF) return UNDEF;
        else return 1 - model[-lit];
    }
}

// El valor que retornarà l'avaluació del literal serà TRUE,
// independentment de si és una variable negada o no
// Aquesta mateixa funció serveix per posarlos a FALSE,
// cridant-la amb el literal negat.
inline void set_lit_to_true(int lit) {
    model_stack.push_back(lit);
    if (lit > 0) model[lit] = TRUE;
    else model[-lit] = FALSE;     
}


bool propagate_gives_conflict() {
    while (ind_next_lit_to_propagate < model_stack.size()) {
        ++ind_next_lit_to_propagate;
        
        for (uint i = 0; i < n_clauses; ++i) {
            bool someLitTrue = false;
            int numUndefs = 0;
            int lastLitUndef = 0;
            
            for (uint k = 0; not someLitTrue and k < clauses[i].size(); ++k){
                int val = current_value_in_model(clauses[i][k]);
                if (val == TRUE) someLitTrue = true;
                else if (val == UNDEF) { ++numUndefs; lastLitUndef = clauses[i][k]; }
            }
            
            if (not someLitTrue and numUndefs == 0) return true; // conflict! all lits false
            else if (not someLitTrue and numUndefs == 1) set_lit_to_true(lastLitUndef);  
        }    
    }
    
    return false;
}


inline void decide_literal_true(int decision_lit) {
    model_stack.push_back(UPPER_IS_DECISION_MARK);
    ++ind_next_lit_to_propagate;
    ++decision_level;
    set_lit_to_true(decision_lit);
}

inline void decide_literal_false(int decision_lit) {
    model_stack.pop_back(); // remove the DL mark
    --decision_level;
    ind_next_lit_to_propagate = model_stack.size();
    set_lit_to_true(-decision_lit); // reverse last decision
}

inline int undo_until_last_decision() {
    uint i = model_stack.size() - 1;
    int lit = 0;

    // Desfem totes les propagacions
    // fins que ens trobem una decisió
    while (model_stack[i] != UPPER_IS_DECISION_MARK) {
        lit = model_stack[i];
        model[abs(lit)] = UNDEF;
        model_stack.pop_back();
        --i;
    }

    return lit;
}

void backtrack() {
    decide_literal_false(undo_until_last_decision());
}


// Heuristic for finding the next decision literal:
// Devuelve 0 cuando todas las variables están definidas
int get_next_decision_literal(){
    for (uint i = 1; i <= n_vars; ++i) // stupid heuristic:
        if (model[i] == UNDEF) return i;  // returns first UNDEF var, positively
    
    return NO_DECISION_LITERAL; // reurns 0 when all literals are defined
}

/**
  Comprova que la interpretació efectivament es un model
  i.e totes les clàusules són positives
**/
void check_model() {
    for (int i = 0; i < n_clauses; ++i) {
        bool someTrue = false;
        for (int j = 0; not someTrue and j < clauses[i].size(); ++j)
            someTrue = (current_value_in_model(clauses[i][j]) == TRUE);
        
        if (not someTrue) {
            cout << "Error in model, clause is not satisfied:";
            for (int j = 0; j < clauses[i].size(); ++j) cout << clauses[i][j] << " ";
            cout << endl;
            exit(1);
        }
    }  
}

void finish_with_result(bool satisfiable) {
    if (satisfiable) {
        check_model(); 
        cout << "SATISFIABLE" << endl; 
        exit(10);
    }
    else {
        cout << "UNSATISFIABLE" << endl; 
        exit(20);
    }
}


void take_care_of_initial_unit_clauses() {
    for (uint i = 0; i < n_clauses; ++i)
        if (clauses[i].size() == 1) {
            int lit = clauses[i][0];
            int val = current_value_in_model(lit);
            if (val == FALSE) finish_with_result(false);
            else if (val == UNDEF) set_lit_to_true(lit);
        }
}

void run_dpll() {
    while (true) {
        while (propagate_gives_conflict()) {
            if (decision_level == 0) finish_with_result(false); 
            else backtrack();
        }

        int decision_lit = get_next_decision_literal();
        if (decision_lit == NO_DECISION_LITERAL) 
            finish_with_result(true);
        
        decide_literal_true(decision_lit);
    }
}

int main() { 
    init_data_structures();
  
    take_care_of_initial_unit_clauses();
  
    run_dpll();
}  
