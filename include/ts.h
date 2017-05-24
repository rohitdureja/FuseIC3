/**
 * Manager for transition systems
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

namespace fuse {

/**
 * A simple class for representing a transition system.
 *
 * We represent a transition system (TS) using 3 formulas: init for the
 * initial states, trans for the transition relation, and prop for the
 * invariant property. Init and prop are over a set of state variables X,
 * whereas trans is over state variables X, next-state variables X', and input
 * variables Y.
 */
class TransitionSystem {
public:
    TransitionSystem(msat_env env);
    ///< constructor taking as input a MathSAT environment for building terms

    void initialize(const TermMap &statevars,
                    msat_term init, msat_term trans, msat_term prop);
    ///< initialization of the TS from the 3 formulas mentioned above and a
    ///< map from state variables to their primed version

    msat_env get_env() const { return env_; }

    const TermList &statevars() const { return statevars_; }
    const TermList &inputvars() const { return inputvars_; }
    const TermList &nextstatevars() const { return nextstatevars_; }

    msat_term init() const { return init_; }
    msat_term trans() const { return trans_; }
    msat_term prop() const { return prop_; }

    bool is_statevar(msat_term t) const
    { return statevars_set_.find(t) != statevars_set_.end(); }

    bool is_nextstatevar(msat_term t) const
    { return nextstatevars_set_.find(t) != nextstatevars_set_.end(); }

    bool is_inputvar(msat_term t) const
    { return inputvars_set_.find(t) != inputvars_set_.end(); }
    
    msat_term cur(msat_term next_formula) const;
    ///< given a formula f(X',Y) over next-state vars X' and input vars Y,
    ///< returns f(X,Y)
    
    msat_term next(msat_term cur_formula) const;
    ///< given a formula f(X,Y) over state vars X and input vars Y,
    ///< returns f(X',Y)

private:
    void reset();
    void collect_inputs();
    
    msat_env env_;
    TermList statevars_;
    TermList nextstatevars_;
    TermList inputvars_;

    TermSet statevars_set_;
    TermSet nextstatevars_set_;
    TermSet inputvars_set_;
    
    mutable TermMap cur2next_;
    mutable TermMap next2cur_;
    msat_term init_;
    msat_term trans_;
    msat_term prop_;
};

} // namespace FuseIC3
