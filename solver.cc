#include <iostream>
#include <algorithm>
#include <vector>
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
vector<int> model_stack; // Contains absolute variables

uint decision_level;

// Statistics

uint decisions;
uint propagations;
clock_t begin_clk;

/*********************************/
/** PROPAGATION OPTIMIZATION DS **/
/*********************************/

vector<vector<int> > clauses_pos_by_var;
vector<vector<int> > clauses_neg_by_var;

/*******************/
/** HEURISTICS DS **/
/*******************/

vector<int> var_occurrences;
vector<int> vars_sorted_by_most_occurring;

/***********************/
/** TRIVIAL FUNCTIONS **/
/***********************/

void read_clauses() {
    char c = cin.get();
    while (c == 'c') {
        while (c != '\n') c = cin.get();
        c = cin.get();
    }

    string aux;
    cin >> aux >> n_vars >> n_clauses;
    clauses.resize(n_clauses);

    for (uint i = 0; i < n_clauses; ++i) {
        int lit;
        while (cin >> lit and lit != 0) clauses[i].push_back(lit);
}   }

// IDEA: Reverse condition
inline int current_value_in_model(int lit) {
    if (lit >= 0) return model[lit];
    else {
        if (model[-lit] == UNDEF) return UNDEF;
        else return 1 - model[-lit];
}   }

// IDEA: Reverse condition
inline void set_lit_to_true(int lit) {
    if (lit > 0) {
        model_stack.push_back(lit);
        model[lit] = TRUE;
    }
    else {
        model_stack.push_back(-lit);
        model[-lit] = FALSE;
}   }

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

    cerr << "decisions: " << decisions << endl
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

int get_var_index_in_clause(int clause, int var) {
    for (int j = 0; j < clauses[clause].size(); ++j) {
        int lit = clauses[clause][j];
        if (lit == var or lit == -var) return j;
    }

    return UNDEF;
}

inline bool var_is_in_clause(int clause, int var) {
    return get_var_index_in_clause(clause, var) != UNDEF;
}

/***********************************/
/** PROPAGATION DS INITIALIZATION **/
/***********************************/

void get_var_appearance_info() {
    clauses_pos_by_var.resize(n_vars + 1, vector<int>(0));
    clauses_neg_by_var.resize(n_vars + 1, vector<int>(0));

    for (int var = 1; var <= n_vars; ++var)
        for (int clause = 0; clause < n_clauses; ++clause) {
            int index = get_var_index_in_clause(clause, var);

            if (index != UNDEF) {
                if (clauses[clause][index] > 0) clauses_pos_by_var[var].push_back(clause);
                else clauses_neg_by_var[var].push_back(clause);
            }
        }
}

/*****************************/
/** HEURISTICS COMPUTATIONS **/
/*****************************/

int get_var_occurrences(int var) {
    int n_occurrences = 0;

    for (int clause = 0; clause < n_clauses; ++clause)
        if (var_is_in_clause(clause, var)) ++n_occurrences;

    return n_occurrences;
}

inline bool occurrence_sort(int var_1, int var_2) {
    return var_occurrences[var_1] > var_occurrences[var_2];
}

void assign_occurrence_sorted_var_list() {
    var_occurrences.resize(n_vars + 1);
    vars_sorted_by_most_occurring.resize(n_vars);

    for (int var = 1; var <= n_vars; ++var) {
        var_occurrences[var] = get_var_occurrences(var);
        vars_sorted_by_most_occurring[var-1] = var;
    }

    sort(vars_sorted_by_most_occurring.begin(),
         vars_sorted_by_most_occurring.end(),
         occurrence_sort);
}

/*******************************************/
/** DATA STRUCTURE INITIALIZATION MANAGER **/
/*******************************************/

void init_data_structures() {
    read_clauses();

    model.resize(n_vars + 1, UNDEF);

    get_var_appearance_info();

    assign_occurrence_sorted_var_list();

    ind_next_lit_to_propagate = decision_level = decisions = propagations = 0;
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
    int var = model_stack[ind_next_lit_to_propagate];

    vector<int>& clauses_opposite = model[var] == TRUE ?
                                        clauses_neg_by_var[var] :
                                        clauses_pos_by_var[var];

    for (int i = 0; i < clauses_opposite.size(); ++i) {
        // TODO: Mirar si es pot marcar el nombre de clausules indefinides dinamicament
        int clause = clauses_opposite[i];
        int num_undefs = 0;
        int last_lit_undef;
        bool some_lit_true = false;

        for (int j = 0; not some_lit_true and j < clauses[clause].size(); ++j) {
            int lit = clauses[clause][j];
            int val = current_value_in_model(lit);

            if (val == TRUE) some_lit_true = true;
            else if (val == UNDEF) { ++num_undefs; last_lit_undef = lit; }
        }

        if (not some_lit_true) {
            if (num_undefs == 0) return true;
            else if (num_undefs == 1) set_lit_to_true(last_lit_undef);
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
        model[lit] = UNDEF;
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
