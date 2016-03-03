#include <iostream>
#include <algorithm>
#include <vector>
#include <stdlib.h>
#include <ctime>
using namespace std;

/***************/
/** CONSTANTS **/
/***************/

const int UNDEF = -1;
const int TRUE = 1;
const int FALSE = 0;
const int ALL_LITERALS_DEFINED = 0;
const int MARK_UPPER_IS_DECISION = 0;

const float OCCURRENCE_HEURISTIC_FACTOR = 0.1f;
const int HEURISTIC_RESET_REDUCTION_FACTOR = 2;
const int MAX_CONFLICTS_UNTIL_RESET = 500;

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

unsigned long long decisions;
unsigned long long propagations;
clock_t begin_clk;

/*********************************/
/** PROPAGATION OPTIMIZATION DS **/
/*********************************/

vector<vector<vector<int>* > > clauses_where_var_positive;
vector<vector<vector<int>* > > clauses_where_var_negative;

/*******************/
/** HEURISTICS DS **/
/*******************/

int conflicts_since_last_reset;
vector<int> heuristic_value;

/***********************/
/** TRIVIAL FUNCTIONS **/
/***********************/

inline int current_value_in_model(int lit) {
    if (lit >= 0) return model[lit];
    else {
        if (model[-lit] == UNDEF) return UNDEF;
        else return 1 - model[-lit];
}   }

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

/*****************************/
/** HEURISTICS COMPUTATIONS **/
/*****************************/

void reset_conflict_info() {
    conflicts_since_last_reset = 0;

    for (int var = 1; var <= n_vars; ++var)
        heuristic_value[var] /= HEURISTIC_RESET_REDUCTION_FACTOR;
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
    heuristic_value.resize(greatest_var, 0);
    clauses_where_var_positive.resize(greatest_var);
    clauses_where_var_negative.resize(greatest_var);
}

void read_clauses_and_compute_data_structures() {
    for (uint i = 0; i < n_clauses; ++i) {
        int lit;
        while (cin >> lit and lit != 0) {
            int var = abs(lit);
            ++heuristic_value[var];

            if (lit > 0) clauses_where_var_positive[var].push_back(&clauses[i]);
            else         clauses_where_var_negative[var].push_back(&clauses[i]);

            clauses[i].push_back(lit);
        }
    }

    for (int var = 1; var <= n_vars; ++var)
        heuristic_value[var] *= OCCURRENCE_HEURISTIC_FACTOR;

    ind_next_lit_to_propagate = decision_level = decisions = propagations =
    conflicts_since_last_reset = 0;
}

void init_data_structures() {
    skip_comments();

    read_header();

    create_data_structures();

    read_clauses_and_compute_data_structures();
}

/***************************************************************/
/** IMPORTANT METHODS - get_next_decision_literal & propagate **/
/***************************************************************/

inline int get_next_decision_literal() {
    int max_heuristic_value = -1;
    int max_var;

    for (int var = 1; var <= n_vars; ++var)
        if (model[var] == UNDEF and heuristic_value[var] > max_heuristic_value) {
            max_heuristic_value = heuristic_value[var];
            max_var = var;
        }

    return max_heuristic_value != -1 ? max_var : ALL_LITERALS_DEFINED;
}

inline bool propagate() {
    int lit_to_propagate = model_stack[ind_next_lit_to_propagate];

    int var = abs(lit_to_propagate);
    vector<vector<int>* >& clauses_opposite = lit_to_propagate > 0 ?
                                                clauses_where_var_negative[var] :
                                                clauses_where_var_positive[var];

    for (int i = 0; i < clauses_opposite.size(); ++i) {
        // TODO: Mirar si es pot marcar el nombre de clausules indefinides dinamicament
        vector<int>& clause = *clauses_opposite[i];
        int num_undefs = 0;
        int last_lit_undef;
        bool some_lit_true = false;

        // Could stop when num_undefs >= 2, but doesn't pay off in clauses of size 3
        for (int j = 0; not some_lit_true and j < clause.size(); ++j) {
            int lit = clause[j];
            int val = current_value_in_model(lit);

            if (val == UNDEF) { ++num_undefs; last_lit_undef = lit; }
            else if (val == TRUE) some_lit_true = true;
        }

        if (not some_lit_true and num_undefs < 2) {
            if (num_undefs == 1) set_lit_to_true(last_lit_undef);
            else {
                ++heuristic_value[var];
                ++conflicts_since_last_reset;

                if (conflicts_since_last_reset == MAX_CONFLICTS_UNTIL_RESET)
                    reset_conflict_info();

                return true;
            }
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
    model_stack.push_back(MARK_UPPER_IS_DECISION);
    ++ind_next_lit_to_propagate;
    ++decision_level;
    set_lit_to_true(decision_lit);
}

inline void decide_literal_false(int decision_lit) {
    model_stack.pop_back(); // Remove decision mark
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

        ++decisions;
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
