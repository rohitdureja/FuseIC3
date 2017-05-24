/*
 * This file is part of FuseIC3.
 * author: Rohit Dureja <dureja at iastate dot edu>
 *
 * Copyright (C) 2017 Rohit Dureja,
 *                    Iowa State University
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

#include <sstream>
#include <iomanip>
#include <algorithm>
#include <fstream>
#include <set>
#include "../include/fuse.h"


namespace fuse {

FuseIC3::FuseIC3(const msat_env &env, const Options &opts):
    ts_(nullptr),
    opts_(opts),
    vp_(env),
    rng_(opts.seed),
    solver_(env, opts)
{
    // generate labels
    init_label_ = make_label("init");
    trans_label_ = make_label("trans");
    bad_label_ = make_label("bad");

    hard_reset();
}


//-----------------------------------------------------------------------------
// public methods
//-----------------------------------------------------------------------------

void FuseIC3::configure(const TransitionSystem *ts) {

    if(!opts_.family)
        hard_reset();
    else
        soft_reset();

    ts_ = ts;
}

bool FuseIC3::prove()
{
    initialize();
    apply_cone_of_influence();
    TimeKeeper t(total_time_);

    // check if last found invariant is valid in the new model
    if(opts_.family) {
        if(opts_.algorithm > 1) {
            if(initial_invariant_check()) {
                last_checked_ = true;
                model_count_++;
                check_type_ = invar;
                return true;
            }
        }
        if(simulate_last_cex()) {
            // last cex holds in the model being checked
            last_checked_ = false;
            cex_ = last_cex_;
            model_count_++;
            check_type_ = cex;
            return false;
        }

        // find minimal subclause of last known invariant that is inductive
        // with respect to the current model.
        //
        // The implementation follows the description in the paper
        // - Chockler, H., Ivrii, A., Matsliah, A., Moran, S., & Nevo, Z. Incremental
        //   Formal Verification of Hardware. FMCAD 2011
        if(opts_.algorithm == 1) {
            min_clause_.clear();
            if(invariant_finder(min_clause_)) {
                logger(1) << "Found minimal inductive subclause"
                          << endlog;
                // add min clause to solver
                for(Cube c : min_clause_) {
                    solver_.add_cube_as_clause(c, min_clause_label_);
                }
            }
            else
                min_clause_.clear();
        }
    }

    if (!check_init()) {

        last_checked_ = false;
        model_count_++;
        check_type_ = init;
        return false;
    }

    // increment frame count
    frame_number++;

    while (true) {
        Cube bad;
        if(opts_.algorithm > 2 && model_count_ > 0) {
            // check if F[i-1] & T |= F[i]'
            std::list<Cube *> frame;
            while(!check_frame_invariant(depth(), frame)) {
                frame_repair(depth(), frame);
            }
            if (propagate()) {
                model_count_ += 1;
                print_frames();
                check_type_ = pdr;
                return true;
            }
        }

        while (get_bad(bad)) {
            if (!rec_block(bad)) {
                logger(1) << "found counterexample at depth " << depth()
                          << endlog;
                model_count_ += 1;
                print_frames();
                check_type_ = pdr;
                return false;
            }
        }
        new_frame();
        if(opts_.algorithm <=2 || model_count_ < 1) {
            // to maintain time, defined in utils.h

            if (propagate()) {

                model_count_ += 1;
                print_frames();
                check_type_ = pdr;
                return true;
            }
        }
    }
    return false;
}


bool FuseIC3::witness(std::vector<TermList> &out)
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


void FuseIC3::print_stats() const
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

void FuseIC3::save_stats() const
{
    std::ofstream xmlfile;
    std::string fl = opts_.filename;
    fl.erase(fl.end()-4, fl.end());
    std::string filename;
    if(opts_.algorithm == 0)
        filename = ".original";
    else if(opts_.algorithm == 1)
        filename = ".chockler";
    else if(opts_.algorithm == 3)
        filename = ".FuseIC3";
    xmlfile.open(fl + filename + ".log.xml");

#define save_stat(name, value) \
    xmlfile << "<" << name ">" << std::setprecision(3) << std::fixed \
            << value ## _ << "</" << name ">" << std::endl;

    xmlfile << "<statistics>" << std::endl;

    save_stat("num_solve_calls", num_solve_calls);
    save_stat("num_solve_sat_calls", num_solve_sat_calls);
    save_stat("num_solve_unsat_calls", num_solve_unsat_calls);
    save_stat("num_solver_reset", num_solver_reset);
    save_stat("num_added_cubes", num_added_cubes);
    save_stat("num_subsumed_cubes", num_subsumed_cubes);
    save_stat("num_block", num_block);
    save_stat("max_cube_size", max_cube_size);
    save_stat("avg_cube_size", avg_cube_size);
    save_stat("solve_time", solve_time);
    save_stat("solve_sat_time", solve_sat_time);
    save_stat("solve_unsat_time", solve_unsat_time);
    save_stat("block_time", block_time);
    save_stat("generalize_and_push_time", generalize_and_push_time);
    save_stat("rec_block_time", rec_block_time);
    save_stat("propagate_time", propagate_time);
    save_stat("total_time", total_time);
    xmlfile << "<result>";
    xmlfile << (last_checked_ ? "True" : "False");
    xmlfile << "</result>" << std::endl;

    xmlfile << "</statistics>" << std::endl;

    xmlfile.close();
}


//-----------------------------------------------------------------------------
// major methods
//-----------------------------------------------------------------------------

// method to check if new model satisfies last known invariant
bool FuseIC3::initial_invariant_check()
{

    if(model_count_ > 0 && !last_invariant_.empty()) {

        logger(2) << "Trying last known invariant:" << endlog;
        for(Cube &c: last_invariant_) {
            logcube(3, c);
            logger(2) << endlog;
        }

        // check if last invariant is inductive in the current model
        if (!initiation_check(last_invariant_) &&
                !consecution_check(last_invariant_) &&
                !property_check(last_invariant_)) {
            invariant_.clear();
            for(Cube c : last_invariant_) {
                invariant_.push_back(c);
                for (msat_term &l : invariant_.back())
                    l = msat_make_not(ts_->get_env(), l);
            }
            return true;
        }
    }
    return false;
}

bool FuseIC3::simulate_last_cex()
{
    if(model_count_ > 0 && !last_cex_.empty()) {

        logger(1) << "Checking last known counterexample" << endlog;
        // first check if first state in the cex intersects
        // with one of the initial states

        // activate init
        activate_frame(0);

        // create temporary assertion
        solver_.push();

        // check first state of cex
        solver_.add_cube_as_cube(last_cex_[0]);

        bool sat = solve();

        if (!sat)
            return false;

        solver_.pop();

        // create temporary assertion
        solver_.push();

        activate_trans_bad(false, true);

        // check last state of cex
        solver_.add_cube_as_cube(last_cex_.back());

        sat = solve();

        solver_.pop();


        // if sat, the initial state is valid, and we proceed with
        // checking the rest of the cex. otherwise, the cex is invalid.
        if(sat)
        {
            // try simulating cex
            for(unsigned int i = 0 ; i < last_cex_.size() - 1 ; ++i)
            {
                //activate_trans
                activate_trans_bad(true, false);

                // create temporary assertion
                solver_.push();

                // add ith state from cex
                solver_.add_cube_as_cube(last_cex_[i]);

                // add (i+1)th state from cex (next state)
                solver_.add_cube_as_clause(get_next(last_cex_[i+1]));

                sat = solve();

                solver_.pop();

                // if unsat, cex is invalid
                if(!sat)
                    return false;
            }
            return true; // cex valid
        }
        return false;
    }
    return false;
}

// method to find minimal inductive subclause from last known invariant
bool FuseIC3::invariant_finder(std::vector<TermList> &inv)
{
    if(model_count_ > 0 && !last_cex_.empty()) {
        // find the minimal inductive subclause from the set of
        // frames computed for the last model.

        min_clause_.clear();

        // copy old frames
        inv.clear();

        get_old_frame(inv);


        // at this point temp is a vector of cubes. since we are interested
        // in clauses, we use negation in all operations

        // remove clauses not in init.
        remove_clauses_violating_init(inv);

        // find minimal inductive subclause

        if(find_minimal_inductive_subclause(inv)) {
            min_clause_label_ = make_label("min");
            return true;
        }

    }
    else if(model_count_ > 0 && !last_invariant_.empty()) {

        min_clause_.clear();

        // copy last known invariant to temp
        inv = last_invariant_;

        // at this point temp is a vector of cubes. since we are interested
        // in clauses, we use negation in all operations

        // remove clauses not in init.
        remove_clauses_violating_init(inv);

        // find minimal inductive subclause

        if(find_minimal_inductive_subclause(inv)) {

            min_clause_label_ = make_label("min");
            return true;
        }
    }

    return false;
}

bool FuseIC3::check_init()
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


bool FuseIC3::get_bad(Cube &out)
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


bool FuseIC3::rec_block(const Cube &bad)
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


bool FuseIC3::propagate()
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

        if(opts_.algorithm > 2 && k > old_frames_.size()-1 && old_frame_extended_) {
            if (frames_[k].empty()) {

                // fixpoint: frames_[k] == frames_[k+1]
                break;
            }
        }
        else if(opts_.algorithm > 2 && model_count_ > 0 && old_frames_.size() > 0) {
            // check if frame k equals frame k + 1
            // we first check this using sat?(frames_[k] & !frames_[k+1])
            // activate frames_[k]
            activate_frame(k);

            solver_.push();
            // add new frames
            solver_.add_disjunct_cubes(frames_[k+1]);

            // add old frames
            std::list<Cube *> frame;
            std::vector<Cube> ff;
            get_old_frame(k+1, frame);
            if(frame.size() > 0) {

                for(std::list<Cube *>::iterator it = frame.begin();
                    it != frame.end(); ++it) {
                    Cube * c = *it;
                    if(!c->empty())
                        ff.push_back(*c);
                }
            }
            if(!ff.empty())
                solver_.add_disjunct_cubes(ff);

            bool res = solve();

            solver_.pop();

            if(res) {
                break;
            }
        }
        else {
            if (frames_[k].empty()) {
                break;
            }
        }
    }

    if (k < depth()) {
        logger(1) << "fixpoint found at frame " << k << endlog;
        logger(2) << "invariant:" << endlog;
        last_checked_ = true;
        invariant_.clear();
        last_invariant_.clear();
        for (size_t i = k+1; i < frames_.size(); ++i) {
            Frame &f = frames_[i];
            for (Cube &c : f) {
                logcube(3, c);
                logger(3) << endlog;
                invariant_.push_back(c);
                last_invariant_.push_back(c);
                for (msat_term &l : invariant_.back()) {
                    l = msat_make_not(ts_->get_env(), l);
                }
            }
        }
        last_cex_.clear();
        return true;
    }

    return false;
}



bool FuseIC3::block(const Cube &c, unsigned int idx, Cube *out, bool compute_cti)
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


void FuseIC3::generalize(Cube &c, unsigned int &idx)
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


void FuseIC3::push(Cube &c, unsigned int &idx)
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


bool FuseIC3::check_frame_invariant(unsigned int idx, std::list<Cube *> &cubes)
{
    if(!old_frame_extended_) {

        if (idx > 0 && old_frames_.size() > 0 && idx <= old_frames_.size() - 1) {

            print_frames();
            // activate trans
            activate_trans_bad(true, false);

            // activate frame F[idx-1]
            activate_frame(idx-1);

            // create temporary assertion
            solver_.push();

            std::list<Cube *> frame;

            get_old_frame(idx, frame);

            std::vector<Cube> pcubes;
            for(std::list<Cube *>::iterator it = frame.begin();
                it != frame.end(); ++it) {
                Cube * c = *it;
                // get next state version of cube
                if(!c->empty()) {
                    Cube cp = get_next(*c);
                    pcubes.push_back(cp);
                    logger(3) << endlog;
                    logcube(3,cp);
                    logger(3) << endlog;
                }
            }

            solver_.add_disjunct_cubes(pcubes);

            bool sat = solve();

            solver_.pop();

            if(sat) {
                // F[idx-1] & T & ~F[idx] is satisfiable, we repair frame
                cubes.clear();
                std::swap(cubes, frame);
                return false;
            }
            else {
                // add F[idx] from old frames to new frames
                logger(1) << "Frame check successful. Old Frame " << idx
                          << " moved to New Frame " << idx
                          << endlog;
                for(std::list<Cube *>::iterator it = frame.begin();
                    it != frame.end(); ++it) {
                    Cube * c = *it;

                    if(!c->empty()) {
                        add_old_frame(*c, idx);

                    }
                }
                print_frames();
                cubes.clear();
                return true;
            }
        }
        else if (idx > old_frames_.size() - 1)
        {
            // copy the last old frame to a new
            std::list<Cube> tmp;
            auto it = old_frames_.rbegin();
            old_frames_.push_back(*it);
            old_frame_extended_ = true;
            cubes.clear();
            logger(2) << "Old Frames Extended" << endlog;
            std::list<Cube *> frame;
            get_old_frame(1, frame);
            std::swap(cubes, frame);
            return false;
        }
    }
    return true;
}

void FuseIC3::lavish_frame_repair(unsigned int idx, std::list<Cube *> &frame)
{
    logger(1) << "Attempting Lavish Frame Repair at idx: " << idx
              << endlog;

    if(idx > 0) {
        // find clauses responsible
        std::list<Cube *> cubes;
        find_cubes_at_fault(idx, frame, cubes);
        logger(2) << "Faulty cubes in Old Frame idx = "
                  << idx << ": " << cubes.size() << endlog;
        // we start repairing each cube in the list of cubes
        // in lavish frame repair, these cubes are simply dropped.

        for(std::list<Cube *>::iterator it = cubes.begin();
            it != cubes.end(); ++it) {
            Cube * c = *it;
            c->clear();
        }
        if(old_frame_extended_) {
            // add frame contents to main new frame
            for(std::list<Cube *>::iterator it = frame.begin();
               it != frame.end(); ++it) {
               Cube * c = *it;
               if(!c->empty())
                   add_blocked(*c, idx);
            }
        }
        return;
    }
}

void FuseIC3::sensible_frame_repair(unsigned int idx, std::list<Cube *> &frame)
{
    logger(1) << "Attempting Sensible Frame Repair at idx: " << idx
              << endlog;

    typedef std::uniform_int_distribution<int> RandInt;
    RandInt dis;

    if(idx > 0) {
        // find clauses responsible
        std::list<Cube *> cubes;
        find_cubes_at_fault(idx, frame, cubes);

        // we start repairing each cube in the list of cubes
        // in sensible frame repair, these cubes are repaired by adding
        // missing literals.


        for(std::list<Cube *>::iterator it = cubes.begin();
            it != cubes.end(); ++it) {

            //reset_solver();
            Cube * c = *it;

            // find literals in current cube
            std::set<msat_term> current;
            for(msat_term l : *c)
                current.insert(var(l));

            // find literal not in cube
            std::vector<msat_term> rest;
            std::set_difference(state_vars_.begin(), state_vars_.end(),
                                current.begin(), current.end(),
                                std::inserter(rest, rest.begin()));

            // activate trans
            activate_trans_bad(true, false);

            // activate frame
            activate_frame(idx - 1);

            // create temporary assertion
            solver_.push();

            // add next state version of cube to solver
            solver_.add_cube_as_cube(get_next(*c));

            bool sat = solve();

            while(sat && !rest.empty()) {
                // get model assignment for a literal not in the cube
                // generate random number
                size_t j = (dis(rng_,
                            RandInt::param_type(1, rest.size())) - 1);

                bool val = solver_.model_value(ts_->next(rest[j]));

                // update cube c;
                c->push_back(lit(rest[j], val ? false : true));

                // remove added literal from rest
                rest.erase(rest.begin() + j);
                solver_.pop();

                // activate trans
                activate_trans_bad(true, false);

                // activate frame
                activate_frame(idx - 1);

                // create temporary assertion
                solver_.push();

                // add next state version of cube to solver
                solver_.add_cube_as_cube(get_next(*c));

                sat = solve();

            }
            solver_.pop();
            if(sat || rest.empty()) // means there is only one state
                                    // missing from the cube
                c->clear();
            else if(!sat) {
                exit(-3);
                // TODO: generalization appears here
            }
        }
        return;

    }
}



//-----------------------------------------------------------------------------
// minor/helper methods
//-----------------------------------------------------------------------------


void FuseIC3::initialize()
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


void FuseIC3::new_frame()
{
    if (depth()) {
        logger(1) << depth() << ": " << flushlog;
        for (size_t i = 1; i <= depth(); ++i) {
            Frame &f = frames_[i];
            logger(1) << f.size() << " ";
        }
        logger(1) << endlog;
    }

    // increment frame count
    frame_number++;

    if(frame_number >= frames_.size())
        frames_.push_back(Frame());

    frame_labels_.push_back(make_label("frame"));
//    if(opts_.algorithm == 1 && !min_clause_.empty()){
//        for(Cube c : min_clause_) {
//            frames_[depth()].push_back(c);
//            add_blocked(c, depth());
//        }
//    }
}


void FuseIC3::generalize_and_push(Cube &c, unsigned int &idx)
{
    TimeKeeper t(generalize_and_push_time_);

    generalize(c, idx);
    push(c, idx);
}

void FuseIC3::add_blocked(Cube &c, unsigned int idx)
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


inline void FuseIC3::add_old_frame(Cube &c, unsigned int idx)
{
    solver_.add_cube_as_clause(c, frame_labels_[idx]);
}


FuseIC3::Cube FuseIC3::get_next(const Cube &c)
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


void FuseIC3::get_cube_from_model(Cube &out)
{
    out.clear();
    for (msat_term v : state_vars_) {
        out.push_back(lit(v, !solver_.model_value(v)));
    }
    std::sort(out.begin(), out.end());
}


inline bool FuseIC3::subsumes(const Cube &a, const Cube &b)
{
    return (a.size() <= b.size() &&
            std::includes(b.begin(), b.end(), a.begin(), a.end()));
}


bool FuseIC3::is_blocked(const Cube &c, unsigned int idx)
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


bool FuseIC3::is_initial(const Cube &c)
{
    activate_frame(0);
    activate_trans_bad(false, false);

    for (msat_term l : c) {
        solver_.assume(l);
    }
    bool sat = solve();
    return sat;
}


void FuseIC3::ensure_not_initial(Cube &c, Cube &rest)
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


inline void FuseIC3::activate_frame(unsigned int idx)
{
    if(opts_.algorithm == 1 && min_clause_.size() > 0
            && idx > 0) {
        solver_.assume(min_clause_label_);
    }

    for (unsigned int i = 0; i < frame_labels_.size(); ++i) {
        solver_.assume(lit(frame_labels_[i], i < idx));
    }
}


inline void FuseIC3::activate_bad() { activate_trans_bad(false, true); }

inline void FuseIC3::activate_trans() { activate_trans_bad(true, false); }

inline void FuseIC3::activate_trans_bad(bool trans_active, bool bad_active)
{
    solver_.assume(lit(trans_label_, !trans_active));
    solver_.assume(lit(bad_label_, !bad_active));
}


bool FuseIC3::solve()
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


void FuseIC3::hard_reset()
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
    min_clause_.clear();
    tmp_.clear();
    gen_needed_.clear();
    vp_.id_reset();

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
    frame_number = 0;

}


void FuseIC3::soft_reset()
{
    // reset solver
    solver_.reset();

    // store old frames
    old_frames_.clear();
    std::vector<std::list<Cube>> temp;
    if(opts_.algorithm> 2) {
        if(frames_.size() > old_frames_.size() && check_type_ == pdr) {

            for(unsigned int i = 1 ; i < frames_.size() ; ++i) {
                std::list<Cube> lst;
                for(Cube c : frames_[i]) {
                    lst.push_back(c);
                }
                if(!lst.empty()) {
                    temp.push_back(lst);
                }
                else if(i < old_frames_.size()) {
                    temp.push_back(old_frames_[i-1]);
                }
            }
        }

        old_frames_.clear();
        std::swap(old_frames_, temp);
        if(old_frames_.size() == 1)
            old_frames_.clear();
    }

    last_checked_ = false;
    // reset internal state
    frames_.clear();
    frame_labels_.clear();
    state_vars_.clear();
    lbl2next_.clear();
    cex_.clear();
    invariant_.clear();
    min_clause_.clear();
    tmp_.clear();
    gen_needed_.clear();


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


    frame_number = 0;
    vp_.id_reset();
    old_frame_extended_ = false;

}


void FuseIC3::reset_solver()
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

    // re-add the old_frame contents
    if(old_frames_.size() > 0) {
        for(unsigned int idx = 1 ; idx < old_frames_.size() ; ++idx) {
            std::list<Cube *> frame;
            get_old_frame(idx, frame);
            for(std::list<Cube *>::iterator it = frame.begin();
                it != frame.end() ; ++it) {
                Cube *c = *it;
                if(!c->empty()) {
                    add_old_frame(*c, idx);
                }
            }
        }
    }
}


inline size_t FuseIC3::depth()
{
    return frame_number - 1;
}


inline msat_term FuseIC3::make_label(const char *name)
{
    return vp_.fresh_var(name);
}


inline msat_term FuseIC3::var(msat_term t)
{
    return fuse::var(ts_->get_env(), t);
}


inline msat_term FuseIC3::lit(msat_term t, bool neg)
{
    return fuse::lit(ts_->get_env(), t, neg);
}


Logger &FuseIC3::logcube(unsigned int level, const Cube &c)
{
    logger(level) << "[ ";
    for (msat_term l : c) {
        msat_term v = var(l);
        logger(level) << (l == v ? "" : "~") << logterm(ts_->get_env(), v) <<" ";
    }
    logger(level) << "]" << flushlog;
    return Logger::get();
}

bool FuseIC3::initiation_check(const std::vector<TermList> &inv)
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

bool FuseIC3::consecution_check(const std::vector<TermList> &inv)
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

bool FuseIC3::property_check(const std::vector<TermList> &inv)
{
    // we have to check if (inv & !p) is unsat

    // create temporary assertion
    solver_.push();

    // add inv
    // Note: inv is a vector of clauses stored as cubes.
    for(Cube c: inv)
        solver_.add_cube_as_clause(c);

    // activate bad
    activate_trans_bad(false, true);

    // check satisfiability
    bool sat = solve();

    solver_.pop();

    return sat;
}

void FuseIC3::remove_clauses_violating_init(std::vector<TermList> &cubes)
{
    std::vector<TermList> good_cubes; // temp to hold sat cubes
    good_cubes.clear();

    for(TermList cube : cubes) {
        // activate init
        activate_frame(0);
        activate_trans_bad(false, false);

        // create temporary assertion
        solver_.push();

        // add !cube
        // Note: c is vector of cubes. we have to check satisfiability of I & !cl,
        // where cl is the clause being considered. since c has cubes already, we
        // directly add it to the solver. therefore, !cl = cube.
        solver_.add_cube_as_cube(cube);

        // check satisfiability
        bool sat = solve();

        if(!sat)
            good_cubes.push_back(cube);

        solver_.pop();
    }

    // swap
    std::swap(cubes,good_cubes);
}

bool FuseIC3::find_minimal_inductive_subclause(std::vector<TermList> &cubes)
{
    std::vector<TermList> temp;
    temp = cubes;

    std::vector<msat_term> x_labels;
    std::vector<msat_term> y_labels;

    // create temporary instance
    solver_.push();

    for(Cube c : cubes) {

        logger(3) << "Cube: ";
        logcube(3,c);
        logger(3) << endlog;
        // introduce auxiliary variables for each clause
        msat_term x_label = make_label("x");
        msat_term y_label = make_label("y");

        // generate shifted copy of c

        Cube cprimed = get_next(c);

        logger(3) << "Cube: ";
        logcube(3,cprimed);
        logger(3) << endlog;

        // add the clause (!x | c) (equivalent to x => c)
        solver_.add_cube_as_clause(c, x_label);

        // for each literal a in the clause c', add clause (y | !a)
        // to the solver. equivalent to (c' => y)
        for(msat_term literal : cprimed) {
            solver_.add_binary_clause(y_label, literal);
        }

        x_labels.push_back(x_label);
        y_labels.push_back(y_label);
    }

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

        activate_trans_bad(true, false);

        bool sat = solve();

        if(!sat) {
            // found minimal subclause
            std::swap(temp, cubes);
            solver_.pop();
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
        solver_.pop();
    }
    solver_.pop();
    return false;
}

void FuseIC3::print_frames()
{
    for(unsigned int i = 0 ; i < frames_.size() ; ++i)
    {
        std::vector<Cube> cubes = frames_[i];
        logger(2) << "Frame["<< i <<"]" << endlog;
        for(unsigned int j = 0 ; j < cubes.size() ; ++j)
        {
            logcube(3, cubes[j]);
            logger(3) << endlog;
        }
        logger(2) << endlog;
    }
}

void FuseIC3::get_old_frame(unsigned int idx, std::list<Cube *> &frame)
{
    Cube * c;
    for(unsigned int i = idx-1 ; i < old_frames_.size() ; ++i) {
        for(std::list<Cube>::iterator it = old_frames_[i].begin() ;
            it != old_frames_[i].end() ; ++it) {
            c = &*it;
            frame.push_back(c);
        }
    }
}

void FuseIC3::get_old_frame(std::vector<Cube> &frame)
{
    frame.clear();
    Cube * c;
    if(old_frames_.size() > 0) {
        for(std::list<Cube>::iterator it = old_frames_[0].begin() ;
            it != old_frames_[0].end() ; ++it) {
            c = &*it;
            frame.push_back(*c);
        }
    }

}

void FuseIC3::apply_cone_of_influence()
{
    // remove vars not in current model from old frames
    for(unsigned int j = 0 ; j < old_frames_.size() ;) {
        std::list<Cube> &f = old_frames_[j];
        if(!f.empty()) {
            for(std::list<Cube>::iterator it = f.begin();
                it != f.end();)
            {
                Cube &c = *it;
                if(!c.empty()) {
                    for(unsigned int i = 0 ; i < c.size() ;) {
                        auto jt = lbl2next_.find(var(c[i]));
                        if(jt == lbl2next_.end()) {
                                c.erase(c.begin() + i);
                        }
                        else {
                            ++i;
                        }
                    }
                    if(c.empty()) {
                        it = f.erase(it);
                    }
                    else
                        ++it;
                }
                else {
                    it = f.erase(it);
                    continue;
                }

            }
            if(f.empty())
                old_frames_.erase(old_frames_.begin() + j);
            else
                ++j;
        }
        else {
            old_frames_.erase(old_frames_.begin() + j);
            ++j;
            continue;
        }
    }

    // check if all good
    for(unsigned int j = 0 ; j < old_frames_.size() ;) {
        std::list<Cube> &f = old_frames_[j];
        for(std::list<Cube>::iterator it = f.begin();
            it != f.end();) {
            Cube &c = *it;
            if(c.empty())
                break;
            for(unsigned int i = 0 ; i < c.size() ;) {
                auto jt = lbl2next_.find(var(c[i]));
                if(jt == lbl2next_.end()) {
                    std::cout << "Error\n";
                    logger(1) << logterm(ts_->get_env(), var(c[i]));
                    exit(-3);
                }
                else {
                    ++i;
                }
            }
            ++it;
        }
        ++j;
    }

    // remove vars not in current model from cex
    for(Cube &c : last_cex_) {
        for(unsigned int i = 0 ; i < c.size() ;) {
            auto it = lbl2next_.find(var(c[i]));
            if(it == lbl2next_.end()) {
                // check if input
                if(!ts_->is_inputvar(var(c[i])))
                    c.erase(c.begin() + i);
            }
            else {
                ++i;
            }
        }
    }

    // remove vars not in current model from invariant
    for(unsigned int i = 0 ; i < last_invariant_.size() ;) {
        Cube &c = last_invariant_[i];
        for(unsigned int j = 0 ; j < c.size() ;) {
            auto it = lbl2next_.find(var(c[j]));
            if(it == lbl2next_.end()) {
                c.erase(c.begin() + j);
            }
            else {
                ++j;
            }
        }
        if(c.empty())
            last_invariant_.erase(last_invariant_.begin() + i);
        else
            ++i;
    }
}

inline void FuseIC3::frame_repair(unsigned int idx, std::list<Cube *> &frame)
{
    return opts_.algorithm == 3 ? lavish_frame_repair(idx, frame)
                                : sensible_frame_repair(idx, frame);
}

void FuseIC3::find_cubes_at_fault(unsigned int idx, std::list<Cube *> &frame,
                             std::list<Cube *> &cubes)
{

    std::vector<msat_term> y_labels;
    std::unordered_map<msat_term, Cube *> cmap;

    solver_.push();
    // introduce a new aux variable y for each clause
    // add (y | !a) for each literal in the clause
    for(std::list<Cube *>::iterator it = frame.begin();
        it != frame.end();
        ++it) {
        Cube cp = get_next(*(*it));
        msat_term yl = make_label("y");

        for(msat_term lit : cp) {
            solver_.add_binary_clause(yl, lit);
        }

        y_labels.push_back(yl);
        cmap.insert(std::pair<msat_term, Cube *>(yl, *it));
    }

    while(cmap.size() > 0) {
        msat_term expr = msat_make_false(ts_->get_env());
        for(msat_term lbl : y_labels)
            expr = msat_make_or(ts_->get_env(),
                                expr,
                                msat_make_not(ts_->get_env(), lbl));
        solver_.push();
        solver_.add(expr);

        // activate trans
        activate_trans_bad(true, false);

        // activate F[idx - 1]
        activate_frame(idx - 1);

        bool sat = solve();

        if(!sat) {
            solver_.pop();
            break;
        }
        else {
            // extract values of y
            for(unsigned int i = 0 ; i < y_labels.size() ;) {
                bool val = solver_.model_value(y_labels[i]);
                if(!val) { // clause needs repair
                    // remove from further consideration
                    cubes.push_back(cmap[y_labels[i]]);
                    cmap.erase(y_labels[i]);

                    y_labels.erase(y_labels.begin() + i);
                }
                else
                    ++i;
            }
            solver_.pop();
        }
    }
    solver_.pop();
    return;
}


} // namespace FuseIC3
