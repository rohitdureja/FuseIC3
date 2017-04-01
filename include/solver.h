/** -*- C++ -*-
 * 
 * SMT solver interface for IC3
 * author: Alberto Griggio <griggio@fbk.eu>
 * 
 * This file is part of ic3ia.
 * Copyright (C) 2015 Fondazione Bruno Kessler.
 *
 * ic3ia is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * ic3ia is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with ic3ia.  If not, see <http://www.gnu.org/licenses/>.
 */

#pragma once

#include "utils.h"
#include "opts.h"


namespace nexus {

/**
 * A class for managing the interaction between the IC3 engine and the SMT
 * solver
 */
class Solver {
public:
    Solver(msat_env env, const Options &opts);
    ~Solver();

    void add(msat_term formula, msat_term label);
    ///< adds the assertion "label -> formula" to the SMT solver
    
    void add_clause(const TermList &clause, msat_term label);
    ///< adds the clause "label -> clause" to the SMT solver
        
    void add_cube_as_clause(const TermList &cube, msat_term label);
    ///< adds the clause "label -> ~cube[0] | ... | ~cube[N]" to the SMT solver
    
    void add_cube_as_clause(const TermList &cube);
    ///< like the above, when no label is needed
    
    void add_disjunct_cubes(const std::vector<TermList> &cubes);
    ///< add disjunction of all cubes in the SMT solver

    void push();
    ///< push a backtracking point in the SMT solver
    
    void pop();
    ///< pop a backtracking point from the SMT solver
    
    void assume(msat_term a);
    ///< add an assumption to the SMT solver
    
    bool check();
    ///< checks satisfiability under the current set of assumptions (added
    ///< with Solver::assume()). At the end of each check() call, the set of
    ///< assumptions is emptied automatically
    
    const TermSet &unsat_assumptions();
    ///< if the last check() call returned false, get a subset of the
    ///< assumptions sufficient for the SMT context to be unsat
    
    bool model_value(msat_term pred);
    ///< if the last check() call returned true, get the truth assignment to
    ///< the given predicate
    
    void reset();
    ///< reset the SMT context completely (removing all the asserted formulas
    ///< and reinitializing the internal solver state)

private:
    Solver(const Solver &other);
    Solver &operator=(const Solver &other);

    msat_env env_;
    ///< the underlying SMT solver
    
    TermList a_;
    ///< the current list assumptions 

    TermSet uc_;
    ///< subset of assumptions sufficient for unsatisfiability
};

} // namespace nexus
