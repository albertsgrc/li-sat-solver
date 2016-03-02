#include <iostream>
#include <algorithm>
#include <vector>
#include <stdlib.h>
#include <ctime>
using namespace std;

/***************/
/** CONSTANTS **/
/***************/

#define UNDEF -1
#define TRUE 1
#define FALSE 0

const int ALL_LITERALS_DEFINED = 0;
const int MARK_UPPER_IS_DECISION = 0;

/***************************/
/** BASIC DATA STRUCTURES **/
/***************************/

uint n_clauses;
vector<vector<int> > clauses;

uint n_vars;
vector<int> model;

uint ind_next_lit_to_propagate;
vector<int> model_stack;

uint decision_level;

// Statistics

uint decisions;
uint propagations;
clock_t begin_clk;

/*********************************/
/** PROPAGATION OPTIMIZATION DS **/
/*********************************/

vector<vector<vector<int>* > > clauses_var_positive;
vector<vector<vector<int>* > > clauses_var_negative;

/*******************/
/** HEURISTICS DS **/
/*******************/

vector<int> var_occurrences;
vector<int> vars_sorted_by_most_occurring;

/***********************/
/** TRIVIAL FUNCTIONS **/
/***********************/

// IDEA: Reverse condition
inline int current_value_in_model(int lit) {
    if (lit >= 0) return model[lit];
    else {
        if (model[-lit] == UNDEF) return UNDEF;
        else return 1 - model[-lit];
}   }

// IDEA: Reverse condition
inline void set_lit_to_true(int lit) {
    if (lit > 0) model[lit] = TRUE;
    else model[-lit] = FALSE;

    model_stack.push_back(lit);
}

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
}   }   }

void finish_with_result(bool satisfiable) {
    double elapsed_secs = double(clock() - begin_clk)/CLOCKS_PER_SEC;
    cout << "time: " << elapsed_secs << " secs" << endl;

    cout << "decisions: " << decisions << endl
         << "propagations/sec: " << propagations/elapsed_secs << endl;

    if (satisfiable) { check_model(); cout << "SATISFIABLE" << endl; }
    else cout << "UNSATISFIABLE" << endl;

    exit(satisfiable ? 10 : 20);
}

void take_care_of_initial_unit_clauses() {
    for (uint i = 0; i < n_clauses; ++i) {
        if (clauses[i].size() == 1) {
            int lit = clauses[i][0];
            int val = current_value_in_model(lit);
            if (val == FALSE) finish_with_result(false);
            else if (val == UNDEF) set_lit_to_true(lit);
}   }   }

/***********/
/** UTILS **/
/***********/
/*
int get_var_index_in_clause(int clause, int var) {
    for (int j = 0; j < clauses[clause].size(); ++j) {
        int lit = clauses[clause][j];
        if (lit == var or lit == -var) return j;
    }

    return UNDEF;
}*/

/*
inline bool var_is_in_clause(int clause, int var) {
    return get_var_index_in_clause(clause, var) != UNDEF;
}*/

/*****************************/
/** HEURISTICS COMPUTATIONS **/
/*****************************/

inline bool occurrence_sort(int var_1, int var_2) {
    return var_occurrences[var_1] > var_occurrences[var_2];
}

void assign_occurrence_sorted_var_list() {
    vars_sorted_by_most_occurring.resize(n_vars);

    for (int var = 1; var <= n_vars; ++var)
        vars_sorted_by_most_occurring[var-1] = var;

    sort(vars_sorted_by_most_occurring.begin(),
         vars_sorted_by_most_occurring.end(),
         occurrence_sort);
}

/***********************************/
/** DATA STRUCTURE INITIALIZATION **/
/***********************************/

void skip_comments() {
    char c = cin.get();
    while (c == 'c') {
        while (c != '\n') c = cin.get();
        c = cin.get();
    }
}

void read_header() {
    string aux;
    cin >> aux >> n_vars >> n_clauses;
}

void create_data_structures() {
    int greatest_var = n_vars + 1;

    clauses.resize(n_clauses);
    model.resize(greatest_var, UNDEF);
    var_occurrences.resize(greatest_var, 0);
    clauses_var_positive.resize(greatest_var);
    clauses_var_negative.resize(greatest_var);
}

void read_clauses_and_compute_data_structures() {
    for (uint i = 0; i < n_clauses; ++i) {
        int lit;
        while (cin >> lit and lit != 0) {
            int var = abs(lit);
            ++var_occurrences[var];

            if (lit > 0) clauses_var_positive[var].push_back(&clauses[i]);
            else         clauses_var_negative[var].push_back(&clauses[i]);

            clauses[i].push_back(lit);
        }
    }

    ind_next_lit_to_propagate = decision_level = decisions = propagations = 0;
}

void init_data_structures() {
    skip_comments();

    read_header();

    create_data_structures();

    read_clauses_and_compute_data_structures();

    assign_occurrence_sorted_var_list();
}

/***************************************************************/
/** IMPORTANT METHODS - get_next_decision_literal & propagate **/
/***************************************************************/

inline int get_next_decision_literal() {
    for (int i = 0; i < n_vars; ++i) {
        int var = vars_sorted_by_most_occurring[i];

        if (model[var] == UNDEF) return var;
    }

    return ALL_LITERALS_DEFINED;
}

inline bool propagate() {
    int lit_to_propagate = model_stack[ind_next_lit_to_propagate];

    vector<vector<int>* >& clauses_opposite = lit_to_propagate > 0 ?
                                        clauses_var_negative[lit_to_propagate] :
                                        clauses_var_positive[-lit_to_propagate];

    for (int i = 0; i < clauses_opposite.size(); ++i) {
        // TODO: Mirar si es pot marcar el nombre de clausules indefinides dinamicament
        vector<int>& clause = *clauses_opposite[i];
        int num_undefs = 0;
        int last_lit_undef;
        bool some_lit_true = false;

        for (int j = 0; not some_lit_true and j < clause.size(); ++j) {
            int lit = clause[j];
            int val = current_value_in_model(lit);

            if (val == UNDEF) { ++num_undefs; last_lit_undef = lit; }
            else if (val == TRUE) some_lit_true = true;
        }

        if (not some_lit_true and num_undefs < 2) {
            if (num_undefs == 1) set_lit_to_true(last_lit_undef);
            else return true;
        }
    }

    return false;
}

inline bool propagate_gives_conflict() {
    while (ind_next_lit_to_propagate < model_stack.size()) {
        if (propagate()) return true;

        ++propagations;
        ++ind_next_lit_to_propagate;
    }

    return false;
}

/***************/
/** DECISIONS **/
/***************/

inline void decide_literal_true(int decision_lit) {
    ++decisions;

    model_stack.push_back(MARK_UPPER_IS_DECISION);
    ++ind_next_lit_to_propagate;
    ++decision_level;
    set_lit_to_true(decision_lit);
}

inline void decide_literal_false(int decision_lit) {
    ++decisions;

    model_stack.pop_back(); // remove the DL mark
    --decision_level;
    ind_next_lit_to_propagate = model_stack.size();
    set_lit_to_true(-decision_lit); // reverse last decision
}

/***************************/
/** DECISION BACKTRACKING **/
/***************************/

void backtrack() {
    uint i = model_stack.size() - 1;
    int lit;

    while (model_stack[i] != MARK_UPPER_IS_DECISION) {
        lit = model_stack[i];
        model[abs(lit)] = UNDEF;
        model_stack.pop_back();
        --i;
    }

    decide_literal_false(lit);
}

/***************************/
/** MAIN & DPLL ALGORITHM **/
/***************************/

void run_dpll() {
    while (true) {
        while (propagate_gives_conflict()) {
            if (decision_level == 0) finish_with_result(false);
            else backtrack();
        }

        int decision_lit = get_next_decision_literal();
        if (decision_lit == ALL_LITERALS_DEFINED) finish_with_result(true);

        decide_literal_true(decision_lit);
}   }

int main() {
    cout.setf(ios::fixed);
    cout.precision(3);

    begin_clk = clock();

    init_data_structures();

    take_care_of_initial_unit_clauses();

    run_dpll();
}
