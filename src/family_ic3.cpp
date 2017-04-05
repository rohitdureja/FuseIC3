/*
 * This file is part of Nexus Model Checker.
 * author: Rohit Dureja
 *
 * Copyright (C) 2017 Iowa State University
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 * --- Derived from ic3ia by Alberto Griggio ---
 * ---   Copyright of original code follows  ---
 *
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

#include <family_ic3.h>
#include <sstream>
#include <iomanip>
#include <algorithm>


namespace nexus {

FamilyIC3::FamilyIC3(const msat_env &env, const Options &opts):
    ts_(nullptr),
    opts_(opts),
    vp_(env),
    solver_(env, opts)
{
    // generate labels
    init_label_ = make_label("init");
    trans_label_ = make_label("trans");
    bad_label_ = make_label("bad");

    // reset measured parameters
    last_reset_calls_ = 0;
    num_solve_calls_ = 0;
    num_solve_sat_calls_ = 0;
    num_solve_unsat_calls_ = 0;

    num_solver_reset_ = 0;

    num_added_cubes_ = 0;
    num_subsumed_cubes_ = 0;

    num_block_ = 0;

    max_cube_size_ = 0;
    avg_cube_size_ = 0;

    solve_time_ = 0;
    solve_sat_time_ = 0;
    solve_unsat_time_ = 0;
    block_time_ = 0;
    generalize_and_push_time_ = 0;
    rec_block_time_ = 0;
    propagate_time_ = 0;
    total_time_ = 0;

    // status of family run
    model_count_ = 0;
    last_checked_ = false;
}


//-----------------------------------------------------------------------------
// public methods
//-----------------------------------------------------------------------------

void FamilyIC3::configure(const TransitionSystem *ts) {

    if(!opts_.family)
        // clean up context
        hard_reset();

    ts_ = ts;
}

bool FamilyIC3::prove()
{
    // to maintain time, defined in utils.h
    TimeKeeper t(total_time_);

    initialize();

    // check if last found invariant is valid in the new model
    if(initial_invariant_check())
        return true;

    // find minimal subclause of last known invariant that is inductive
    // with respect to the current model.
    //
    // The implementation follows the description in the paper
    // - Chockler, H., Ivrii, A., Matsliah, A., Moran, S., & Nevo, Z. Incremental
    //   Formal Verification of Hardware. FMCAD 2011
    std::vector<TermList> minimal_invariant;
    std::cout << invariant_finder(minimal_invariant) << std::endl;

    if (!check_init()) {
        return false;
    }

    while (true) {
        Cube bad;
        while (get_bad(bad)) {

            if (!rec_block(bad)) {
                logger(1) << "found counterexample at depth " << depth()
                          << endlog;
                model_count_ += 1;
                return false;
            }
        }
        new_frame();
        if (propagate()) {
            model_count_ += 1;
            return true;
        }
    }
}


bool FamilyIC3::witness(std::vector<TermList> &out)
{
    if (!cex_.empty()) {
        std::swap(cex_, out);
        return true;
    }
    else if (!invariant_.empty()) {
        std::swap(invariant_, out);
        return true;
    }
    return false;
}


void FamilyIC3::print_stats() const
{
#define print_stat(n)                        \
    std::cout << #n << " = " << std::setprecision(3) << std::fixed       \
              << n ## _ << "\n"

    print_stat(num_solve_calls);
    print_stat(num_solve_sat_calls);
    print_stat(num_solve_unsat_calls);
    print_stat(num_solver_reset);
    print_stat(num_added_cubes);
    print_stat(num_subsumed_cubes);
    print_stat(num_block);
    print_stat(max_cube_size);
    print_stat(avg_cube_size);
    print_stat(solve_time);
    print_stat(solve_sat_time);
    print_stat(solve_unsat_time);
    print_stat(block_time);
    print_stat(generalize_and_push_time);
    print_stat(rec_block_time);
    print_stat(propagate_time);
    print_stat(total_time);
}


//-----------------------------------------------------------------------------
// major methods
//-----------------------------------------------------------------------------

// method to check if new model satisfies last known invariant
bool FamilyIC3::initial_invariant_check()
{
    if(model_count_ > 0 && !last_invariant_.empty()) {
        logger(2) << "Trying last known invariant:" << endlog;
        for(Cube &c: last_invariant_) {
            logcube(2, c);
            logger(2) << endlog;
        }

        // check if last invariant is inductive in the current model
        if (!initiation_check(last_invariant_) &&
                !consecution_check(last_invariant_))
            std::cout << "here" << std::endl;
            return true;
    }
    return false;
}

// method to find minimal inductive subclause from last known invariant
bool FamilyIC3::invariant_finder(std::vector<TermList> &inv)
{
    if(model_count_ > 0 && !last_invariant_.empty()) {

        // copy last known invariant to temp
        inv = last_invariant_;

        // at this point temp is a vector of cubes. since we are interested
        // in clauses, we use negation in all operations

        // remove clauses not in init.
        remove_clauses_violating_init(inv);

        // find minimal inductive subclause
        if(find_minimal_inductive_subclause(inv))
            return true;
    }
    return false;
}

bool FamilyIC3::check_init()
{
    TimeKeeper t(solve_time_);

    activate_frame(0); // frame_[0] is init
    activate_bad();

    bool sat = solve();

    if (sat) {
        cex_.push_back(TermList());
        // this is a bit more abstract than it could...
        get_cube_from_model(cex_.back());
    }

    return !sat;
}


bool FamilyIC3::get_bad(Cube &out)
{
	activate_frame(depth());
    activate_bad();

    if (solve()) {
        get_cube_from_model(out);

        logger(2) << "got bad cube of size " << out.size()
                  << ": ";
        logcube(3, out);
        logger(2) << endlog;

        return true;
    } else {
        return false;
    }
}


bool FamilyIC3::rec_block(const Cube &bad)
{
    TimeKeeper t(rec_block_time_);

    ProofQueue queue;

    queue.push_new(bad, depth());

    while (!queue.empty()) {
        // periodically reset the solver -- clean up "garbage"
        // (e.g. subsumed/learned clauses, bad variable scores...)
        if (num_solve_calls_ - last_reset_calls_ > 5000) {
            reset_solver();
        }

        ProofObligation *p = queue.top();

        logger(2) << "looking at proof obligation of size " << p->cube.size()
                  << " at idx " << p->idx << ": ";
        logcube(3, p->cube);
        logger(2) << endlog;

        if (p->idx == 0) {
            // build the cex trace by following the chain of CTIs
            last_checked_ = false;
            last_cex_.clear();
            cex_.clear();
            while (p) {
                cex_.push_back(p->cube);
                last_cex_.push_back(p->cube);
                p = p->next;
            }
            return false;
        }

        if (!is_blocked(p->cube, p->idx)) {
            Cube c;
            if (block(p->cube, p->idx, &c, true)) {
                // c is inductive relative to F[idx-1]
                unsigned int idx = p->idx;
                // generalize c and find the highest idx frame for which
                // relative induction holds
                generalize_and_push(c, idx);
                // add c to F[idx]...F[0]
                add_blocked(c, idx);
                if (idx < depth() && !opts_.stack) {
                    // if we are not at the frontier, try to block p at later
                    // steps. Remember that p is a state that leads to a bad
                    // state in depth()-p->idx steps. Therefore, p is also
                    // bad and if we want to prove the property, our inductive
                    // invariant must not intersect with it. Since we have p
                    // already, it makes sense to exploit this information and
                    // schedule the proof obligation right away. Notice that
                    // this just an optimization, and it can be turned off
                    // without affecting correctness or completeness. However,
                    // this optimization is typically quite effective, and it
                    // is the reason why IC3 might sometimes find cex traces
                    // that are longer that the current depth()
                    queue.push_new(p->cube, p->idx+1, p->next);
                }
                queue.pop();
            } else {
                logger(2) << "got CTI of size " << c.size()
                          << ": ";
                logcube(3, c);
                logger(2) << endlog;
                // c is a predecessor to the bad cube p->cube, so we need to
                // block it at earlier steps in the trace
                queue.push_new(c, p->idx-1, p);
            }
        } else {
            queue.pop();
        }
    }

    return true;
}


bool FamilyIC3::propagate()
{
    TimeKeeper t(propagate_time_);
    std::vector<Cube> to_add;

    size_t k = 1;
    for ( ; k < depth(); ++k) {
        to_add.clear();
        Frame &f = frames_[k];
        // forward propagation: try to see if f[k] is inductive relative to
        // F[k+1]
        for (size_t i = 0; i < f.size(); ++i) {
            to_add.push_back(Cube());

            logger(2) << "trying to propagate cube of size " << f[i].size()
                      << ": ";
            logcube(3, f[i]);
            logger(2) << " from " << k << " to " << k+1 << endlog;

            if (!block(f[i], k+1, &to_add.back(), false)) {
                to_add.pop_back();
            } else {
                logger(2) << "success" << endlog;
            }
        }

        for (Cube &c : to_add) {
            add_blocked(c, k+1);
        }
        if (frames_[k].empty()) {
            // fixpoint: frames_[k] == frames_[k+1]
            break;
        }
    }

    if (k < depth()) {
        logger(2) << "fixpoint found at frame " << k << endlog;
        logger(2) << "invariant:" << endlog;
        last_checked_ = true;
        invariant_.clear();
        last_invariant_.clear();
        for (size_t i = k+1; i < frames_.size(); ++i) {
            Frame &f = frames_[i];
            for (Cube &c : f) {
                logcube(2, c);
                logger(2) << endlog;
                invariant_.push_back(c);
                last_invariant_.push_back(c);
                for (msat_term &l : invariant_.back()) {
                    l = msat_make_not(ts_->get_env(), l);
                }
            }
        }
        return true;
    }

    return false;
}


bool FamilyIC3::block(const Cube &c, unsigned int idx, Cube *out, bool compute_cti)
{
    TimeKeeper t(block_time_);
    ++num_block_;

    assert(idx > 0);

    // check whether ~c is inductive relative to F[idx-1], i.e.
    // ~c & F[idx-1] & T |= ~c', that is
    // solve(~c & F[idx-1] & T & c') is unsat

    // activate T and F[idx-1]
    activate_frame(idx-1);
    activate_trans();

    // assume c'
    Cube primed = get_next(c);
        for (msat_term l : primed) {
            solver_.assume(l);
    }

    // temporarily assert ~c
    solver_.push();
    solver_.add_cube_as_clause(c);
    bool sat = solve();

    if (!sat) {
        // relative induction succeeds. If required (out != NULL), generalize
        // ~c to a stronger clause, by looking at the literals of c' that occur
        // in the unsat core. If g' is a subset of c',
        // then if "~c & F[idx-1] & T & g'" is unsat, then so is
        // "~g & F[idx-1] & T & g'" (since ~g is stronger than ~c)
        if (out) {
            // try minimizing using the unsat core
            const TermSet &core = solver_.unsat_assumptions();
            Cube &candidate = *out;
            Cube rest;
            candidate.clear();

            for (size_t i = 0; i < primed.size(); ++i) {
                msat_term a = primed[i];
                if (core.find(a) != core.end()) {
                    candidate.push_back(c[i]);
                } else {
                    rest.push_back(c[i]);
                }
            }
            solver_.pop();

            // now candidate is a subset of c that is enough for
            // "~c & F[idx-1] & T & candidate'" to be unsat.
            // However, we are not done yet. If candidate intersects the
            // initial states (i.e. "init & candidate" is sat), then ~candidate
            // is not inductive relative to F[idx-1], as the base case
            // fails. We fix this by re-adding back literals until
            // "init & candidate" is unsat
            ensure_not_initial(candidate, rest);
        } else {
            solver_.pop();
        }

        return true;
    } else {
        // relative induction fails. If requested, extract a predecessor of c
        // (i.e. a counterexample to induction - CTI) from the model found by
        // the SMT solver
        Cube inputs;
        if (compute_cti) {
            assert(out);
            get_cube_from_model(*out);
        }
        solver_.pop();

        return false;
    }
}


void FamilyIC3::generalize(Cube &c, unsigned int &idx)
{
    tmp_ = c;
    gen_needed_.clear();

    typedef std::uniform_int_distribution<int> RandInt;
    RandInt dis;

    logger(2) << "trying to generalize cube of size " << c.size()
              << " at " << idx << ": ";
    logcube(3, c);
    logger(2) << endlog;

    // ~c is inductive relative to idx-1, and we want to generalize ~c to a
    // stronger clause ~g. We do this by dropping literals and calling block()
    // again: every time block() succeeds, it will further generalize its
    // input cube using the unsat core found by the SMT solver (see above)
    //
    // More sophisticated (more effective but harder to understand) strategies
    // exist, see e.g. the paper
    // - Hassan, Somenzi, Bradley: Better generalization in IC3. FMCAD'13
    //
    for (size_t i = 0; i < tmp_.size() && tmp_.size() > 1; ) {
        msat_term l = tmp_[i];
        if (gen_needed_.find(l) == gen_needed_.end()) {
            auto it = tmp_.erase(tmp_.begin()+i);

            logger(3) << "trying to drop " << logterm(ts_->get_env(), l)
                      << endlog;

            if (is_initial(tmp_) || !block(tmp_, idx, &tmp_, false)) {
                // remember that we failed to remove l, so that we do not try
                // this again later in the loop
                gen_needed_.insert(l);
                tmp_.insert(it, l);
                ++i;
            }
        }
    }

    std::swap(tmp_, c);
}


void FamilyIC3::push(Cube &c, unsigned int &idx)
{
    // find the highest idx frame in F which can successfully block c. As a
    // byproduct, this also further strenghens ~c if possible
    while (idx < depth()-1) {
        tmp_.clear();
        if (block(c, idx+1, &tmp_, false)) {
            std::swap(tmp_, c);
            ++idx;
        } else {
            break;
        }
    }
}


//-----------------------------------------------------------------------------
// minor/helper methods
//-----------------------------------------------------------------------------


void FamilyIC3::initialize()
{
    for (msat_term v : ts_->statevars()) {
        if (msat_term_is_boolean_constant(ts_->get_env(), v)) {
            state_vars_.push_back(v);
            // fill the maps lbl2next_ and lbl2next_ also for Boolean state
            // vars. This makes the implementation of get_next() and refine()
            // simpler, as we do not need to check for special cases
            lbl2next_[v] = ts_->next(v);
        }
    }

    solver_.add(ts_->init(), init_label_);
    solver_.add(ts_->trans(), trans_label_);
    msat_term bad = lit(ts_->prop(), true);
    solver_.add(bad, bad_label_);

    // the first frame is init
    frames_.push_back(Frame());
    frame_labels_.push_back(init_label_);

    logger(1) << "initialized IC3: " << ts_->statevars().size() << " state vars,"
              << " " << ts_->inputvars().size() << " input vars " << endlog;
}


void FamilyIC3::new_frame()
{
    if (depth()) {
        logger(1) << depth() << ": " << flushlog;
        for (size_t i = 1; i <= depth(); ++i) {
            Frame &f = frames_[i];
            logger(1) << f.size() << " ";
        }
        logger(1) << endlog;
    }

    frames_.push_back(Frame());
    frame_labels_.push_back(make_label("frame"));
}


void FamilyIC3::generalize_and_push(Cube &c, unsigned int &idx)
{
    TimeKeeper t(generalize_and_push_time_);

    generalize(c, idx);
    push(c, idx);
}


void FamilyIC3::add_blocked(Cube &c, unsigned int idx)
{
    // whenever we add a clause ~c to an element of F, we also remove subsumed
    // clauses. This automatically keeps frames_ in a "delta encoded" form, in
    // which each clause is stored only in the last frame in which it
    // occurs. However, this does not remove subsumed clauses from the
    // underlying SMT solver. We address this by resetting the solver every
    // once in a while (see the comment in rec_block())
    for (size_t d = 1; d < idx+1; ++d) {
        Frame &fd = frames_[d];
        size_t j = 0;
        for (size_t i = 0; i < fd.size(); ++i) {
            if (!subsumes(c, fd[i])) {
                fd[j++] = fd[i];
            } else {
                ++num_subsumed_cubes_;
            }
        }
        fd.resize(j);
    }

    solver_.add_cube_as_clause(c, frame_labels_[idx]);
    frames_[idx].push_back(c);

    logger(2) << "adding cube of size " << c.size() << " at level " << idx
              << ": ";
    logcube(3, c);
    logger(2) << endlog;

    ++num_added_cubes_;
    max_cube_size_ = std::max(uint32_t(c.size()), max_cube_size_);
    avg_cube_size_ += (double(c.size()) - avg_cube_size_) / num_added_cubes_;
}


FamilyIC3::Cube FamilyIC3::get_next(const Cube &c)
{
    Cube ret;
    ret.reserve(c.size());

    for (msat_term l : c) {
        auto it = lbl2next_.find(var(l));
        assert(it != lbl2next_.end());
        ret.push_back(lit(it->second, l != it->first));
    }
    return ret;
}


void FamilyIC3::get_cube_from_model(Cube &out)
{
    out.clear();
    for (msat_term v : state_vars_) {
        out.push_back(lit(v, !solver_.model_value(v)));
    }
    std::sort(out.begin(), out.end());
}


inline bool FamilyIC3::subsumes(const Cube &a, const Cube &b)
{
    return (a.size() <= b.size() &&
            std::includes(b.begin(), b.end(), a.begin(), a.end()));
}


bool FamilyIC3::is_blocked(const Cube &c, unsigned int idx)
{
    // first check syntactic subsumption
    for (size_t i = idx; i < frames_.size(); ++i) {
        Frame &f = frames_[i];
        for (size_t j = 0; j < f.size(); ++j) {
            Cube &fj = f[j];
            if (subsumes(fj, c)) {
                ++num_subsumed_cubes_;
                return true;
            }
        }
    }

    // then semantic
    activate_frame(idx);
    activate_trans_bad(false, false);

    for (size_t i = 0; i < c.size(); ++i) {
        solver_.assume(c[i]);
    }
    bool sat = solve();

    return !sat;
}


bool FamilyIC3::is_initial(const Cube &c)
{
    activate_frame(0);
    activate_trans_bad(false, false);

    for (msat_term l : c) {
        solver_.assume(l);
    }
    bool sat = solve();
    return sat;
}


void FamilyIC3::ensure_not_initial(Cube &c, Cube &rest)
{
    // we know that "init & c & rest" is unsat. If "init & c" is sat, we find
    // a small subset of "rest" to add-back to c to restore unsatisfiability
    if (is_initial(c)) {
        size_t n = c.size();
        c.insert(c.end(), rest.begin(), rest.end());

        bool yes = is_initial(c);
        assert(!yes);

        const TermSet &core = solver_.unsat_assumptions();
        c.resize(n);

        for (msat_term l : rest) {
            if (core.find(l) != core.end()) {
                c.push_back(l);
            }
        }

        std::sort(c.begin(), c.end());
    }
}


inline void FamilyIC3::activate_frame(unsigned int idx)
{
    for (unsigned int i = 0; i < frame_labels_.size(); ++i) {
        solver_.assume(lit(frame_labels_[i], i < idx));
    }
}


inline void FamilyIC3::activate_bad() { activate_trans_bad(false, true); }

inline void FamilyIC3::activate_trans() { activate_trans_bad(true, false); }

inline void FamilyIC3::activate_trans_bad(bool trans_active, bool bad_active)
{
    solver_.assume(lit(trans_label_, !trans_active));
    solver_.assume(lit(bad_label_, !bad_active));
}


bool FamilyIC3::solve()
{
    double elapse = 0;
    bool ret = false;
    {
        TimeKeeper t(elapse);
        ++num_solve_calls_;

        ret = solver_.check();
    }
    solve_time_ += elapse;
    if (ret) {
        solve_sat_time_ += elapse;
        ++num_solve_sat_calls_;
    } else {
        solve_unsat_time_ += elapse;
        ++num_solve_unsat_calls_;
    }
    return ret;
}


void FamilyIC3::hard_reset()
{
    // reset solver
    solver_.reset();

    // reset internal state
    frames_.clear();
    frame_labels_.clear();
    state_vars_.clear();
    lbl2next_.clear();
    cex_.clear();
    invariant_.clear();
    tmp_.clear();
    gen_needed_.clear();
    last_reset_calls_ = 0;
    last_checked_ = false;
}

void FamilyIC3::reset_solver()
{
    logger(2) << "resetting SMT solver" << endlog;
    ++num_solver_reset_;
    solver_.reset();
    last_reset_calls_ = num_solve_calls_;

    // re-add initial states, transition relation and bad states
    solver_.add(ts_->init(), init_label_);
    solver_.add(ts_->trans(), trans_label_);
    msat_term bad = lit(ts_->prop(), true);
    solver_.add(bad, bad_label_);

    // re-add all the clauses in the frames
    for (size_t i = 0; i < frames_.size(); ++i) {
        msat_term l = frame_labels_[i];
        for (Cube &c : frames_[i]) {
            solver_.add_cube_as_clause(c, l);
        }
    }
}


inline size_t FamilyIC3::depth()
{
    return frames_.size()-1;
}


inline msat_term FamilyIC3::make_label(const char *name)
{
    return vp_.fresh_var(name);
}


inline msat_term FamilyIC3::var(msat_term t)
{
    return nexus::var(ts_->get_env(), t);
}


inline msat_term FamilyIC3::lit(msat_term t, bool neg)
{
    return nexus::lit(ts_->get_env(), t, neg);
}


Logger &FamilyIC3::logcube(unsigned int level, const Cube &c)
{
    logger(level) << "[ ";
    for (msat_term l : c) {
        msat_term v = var(l);
        logger(level) << (l == v ? "" : "~") << logterm(ts_->get_env(), v) <<" ";
    }
    logger(level) << "]" << flushlog;
    return Logger::get();
}

bool FamilyIC3::initiation_check(const std::vector<TermList> &inv)
{
    // we have to check if (init & !inv) is unsat

    // create temporary assertion
    solver_.push();

    // add !inv
    // Note: inv is a vector of clauses stored as cubes. since we are negating
    // we add a disjunction of all cubes in inv, which is same as adding the
    // negation of the conjunction of a vector of clauses.
    solver_.add_disjunct_cubes(inv);

    // activate init
    activate_frame(0);
    activate_trans_bad(false, false);

    // check satisfiability
    bool sat = solve();

    solver_.pop();

    return sat;
}

bool FamilyIC3::consecution_check(const std::vector<TermList> &inv)
{
    // we have to check  if (inv & trans & !inv')

    // activate trans
    activate_trans_bad(true, false);

    // create temporary assertion
    solver_.push();

    // add inv
    // Note: inv is a vector of clauses stored as cubes. since we have to add
    // inv directly to the solver, we add the conjunction of the negation of
    // cubes. the negation is done by the function add_cube_as_clause.
    for(TermList c: inv) {
        solver_.add_cube_as_clause(c);
    }

    // add !inv'
    // we first create inv' by using get_next()
    std::vector<TermList> invp;
    for(TermList c : inv) {
        invp.push_back(get_next(c));
    }
    // Note: invp is a vector of clauses stored as cubes. since we are negating
    // we add a disjunction of all cubes in inv, which is same as adding the
    // negation of the conjunction of a vector of clauses.
    solver_.add_disjunct_cubes(invp);

    // check satisfiability
    bool sat = solve();

    solver_.pop();

    return sat;
}

void FamilyIC3::remove_clauses_violating_init(std::vector<TermList> &cubes)
{
    std::vector<TermList> good_cubes; // temp to hold sat cubes
    good_cubes.clear();

    for(TermList cube : cubes) {
        // activate init
        activate_frame(0);
        activate_trans_bad(false, false);

        // create temporary assertion
        solver_.pop();

        // add !cube
        // Note: c is vector of cubes. we have to check satisfiability of I & !cl,
        // where cl is the clause being considered. since c has cubes already, we
        // directly add it to the solver. therefore, !cl = cube.
        solver_.add_cube_as_cube(cube);

        // check satisfiability
        bool sat = solve();

        if(!sat)
            good_cubes.push_back(cube);

        solver_.push();
    }

    // swap
    cubes = good_cubes;
}

bool FamilyIC3::find_minimal_inductive_subclause(std::vector<TermList> &cubes)
{
    std::vector<TermList> temp;
    temp = cubes;

    std::vector<msat_term> x_labels;
    std::vector<msat_term> y_labels;

    // create temporary instance
    solver_.push();

    for(Cube c : cubes) {
        // introduce auxiliary variables for each clause
        msat_term x_label = make_label("x");
        msat_term y_label = make_label("y");

        // generate shifted copy of c
        Cube cprimed = get_next(c);

        // add the clause (!x | c) (equivalent to x => c)
        solver_.add_cube_as_clause(c, x_label);

        // for each literal a in the clause c', add clause (y | !a)
        // to the solver. equivalent to (c' => y)
        for(msat_term lit : cprimed) {
            solver_.add(y_label, lit);
        }

        x_labels.push_back(x_label);
        y_labels.push_back(y_label);
    }

    uint32_t iter = 0;
    while(!temp.empty()) {

        // add x_labels as assumptions
        for(msat_term label : x_labels)
            solver_.assume(label);


        // create expression of the form (!y1 | !y2 | ... | !yk) from y_labels
        msat_term t = msat_make_false(ts_->get_env());
        for(msat_term y : y_labels) {
            t = msat_make_or(ts_->get_env(), t, msat_make_not(ts_->get_env(), y));
        }

        // create temporary instance
        solver_.push();
        solver_.add(t);

        bool sat = solve();

        solver_.pop();
        if(!sat) {
            // found minimal subclause
            std::cout << "here" << std::endl;
            cubes = temp;
            solver_.pop();
            return true;
        }
        else {
            for(uint32_t i = 0 ; i < y_labels.size() ; ) {
                bool val = solver_.model_value(y_labels[i]);
                if (!val) {
                    // remove clause
                    temp.erase(temp.begin()+i);
                    x_labels.erase(x_labels.begin()+i);
                    y_labels.erase(y_labels.begin()+i);
                }
                else
                    ++i;
            }
        }
        iter += 1;
    }
    solver_.pop();
    return false;
}



} // namespace nexus
