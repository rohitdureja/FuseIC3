/*
 * This file is part of Nexus Model Checker.
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

#pragma once

#include "ts.h"
#include "solver.h"
#include <queue>
#include <random>
#include <list>

namespace nexus {

/**
 * A simple implementation of the IC3 algorithm for model families. Aimed at
 * simplicity, conciseness, and ease of understanding rather than at raw
 * performance.
 *
 */
class FamilyIC3 {
public:
    FamilyIC3(const msat_env &env, const Options &opts);

    bool prove();
    ///< main method: check whether the property holds or not

    bool witness(std::vector<TermList> &out);
    ///< compute a witness for the property: a counterexample trace if the
    ///< property is false (where each element of the vector is an assignment
    ///< to state an input vars), or an inductive invariant if the property
    ///< holds (in this case, each element of the vector is a clause that is
    ///< part of the invariant)

    void print_stats() const;
    ///< print search statistics on stdout

    void configure(const TransitionSystem *ts);
    ///< configure the algorithm object with a new transition system/model
    ///< helps keep reusing the same object, and therefore, old internal
    ///< data structures.

    void save_stats() const;
    ///< save the algorithm statistics as an xml file in the current directory

private:
    //------------------------------------------------------------------------
    // internal data structures
    //------------------------------------------------------------------------

    typedef TermList Cube;
    ///< a cube is a conjunction of literals, represented as a vector

    typedef std::vector<Cube> Frame;
    ///< a Frame (an element of the trace F) is a vector of cubes

    typedef std::vector<Frame> FrameList;
    ///< the trace F is a vector of frames

    /**
     * A proof obligation is a pair <C,k> where C is a bad cube to block and k
     * is a position in the current trace. The pair represents the relative
     * induction query:
     *    ~C & F[k] & T |= ~C'
     * where F is the current trace and T the transition relation.
     *
     * Proof obligations are linked together (via the next field) to form a
     * counterexample trace
     */
    struct ProofObligation {
        Cube cube;
        unsigned int idx;
        ProofObligation *next;

        ProofObligation(Cube c, unsigned int t, ProofObligation *n=NULL):
            cube(c), idx(t), next(n) {}

        bool operator<(const ProofObligation &other) const
        { return idx < other.idx; }
    };

    /**
     * Ordering for proof obligations in the priority queue (see below)
     */
    struct ProofObligationOrder {
        bool operator()(const ProofObligation *a,
                        const ProofObligation *b) const { return (*b) < (*a); }
    };

    /**
     * Priority queue of proof obligations
     */
    class ProofQueue {
    public:
        ~ProofQueue()
        {
            for (auto p : store_) {
                delete p;
            }
        }

        void push_new(const Cube &c, unsigned int t, ProofObligation *n=NULL)
        {
            ProofObligation *po = new ProofObligation(c, t, n);
            push(po);
            store_.push_back(po);
        }

        void push(ProofObligation *p) { queue_.push(p); }
        ProofObligation *top() { return queue_.top(); }
        void pop() { queue_.pop(); }
        bool empty() const { return queue_.empty(); }

    private:
        typedef std::priority_queue<ProofObligation *,
                                    std::vector<ProofObligation *>,
                                    ProofObligationOrder> Queue;
        Queue queue_;
        std::vector<ProofObligation *> store_;
    };


    //------------------------------------------------------------------------
    // major methods
    //------------------------------------------------------------------------

    bool initial_invariant_check();
    ///< check whether the model satisfies the previously found invariant

    bool simulate_last_cex();
    ///< simulate the counterexample from the last run to check if it is
    ///< valid in the current model being checked. if valid, the property
    ///< is false for the model. Otherwise, proceed.

    bool invariant_finder(std::vector<TermList> &invariant);
    ///< find the minimal subclause in the last found invariants that is
    ///< inductive with respect to the current model being checked

    bool check_init();
    ///< check whether the property is satisfied by the initial states

    bool get_bad(Cube &out);
    ///< check whether the last frame in the trace (i.e. F[N]) intersects the
    ///< bad states. If so, compute a cube in the intersection

    bool rec_block(const Cube &bad);
    ///< strengthen all the elements of the trace F[1]...F[N] so that the bad
    ///< cube in input is blocked by F[N] (i.e. their intersection is empty --
    ///< F[N] & bad is unsat). If this is not possible, false is returned
    ///< and a counterexample trace is generated

    bool propagate();
    ///< forward propagation of cubes. For each element F[i] in the trace, for
    ///< each clause c in F[i], if (F[i] & T |= c'), add c to F[i+1]. If a
    ///< fixpoint is found (F[i] == F[i+1]), return true and store F[i] as
    ///< inductive invariant

    bool block(const Cube &c, unsigned int idx, Cube *out, bool compute_cti);
    ///< check whether (~c & F[idx-1] & T |= ~c'). If so and if out is not
    ///< NULL, store in *out a generalization of c that can still be blocked by
    ///< F[idx]. If not and compute_cti is true, store in *out
    ///< a counterexample to induction (CTI), i.e. a predecessor of c'
    ///< that in included in F[idx]

    void generalize(Cube &c, unsigned int &idx);
    ///< perform inductive generalization of the input cube c, by dropping
    ///< literals from it as long as (~c & F[idx] & T |= ~c')

    void push(Cube &c, unsigned int &idx);
    ///< find the highest index idx for which (~c & F[idx] & T |= ~c')

    bool check_frame_invariant(unsigned int idx, std::list<Cube *> &cubes);
    ///< check whether the frames invariant F[i-1] & T |= F[i] holds

    void lavish_frame_repair(unsigned int idx, std::list<Cube *> &cubes);
    ///< clauses in F[idx] that violate F[idx-1] & T |= F[idx]' are replaced
    ///< with True which makes the formula UNSAT

    void sensible_frame_repair(unsigned int idx, std::list<Cube *> &cubes);
    ///< clauses in F[idx] that violate F[idx-1] & T |= F[idx]' are replaced
    ///< generalized clauses which makes the formula UNSAT

    //------------------------------------------------------------------------
    // minor/helper methods
    //------------------------------------------------------------------------

    void initialize();
    ///< initialize the internal state

    void new_frame();
    ///< add a new element to the trace F

    void generalize_and_push(Cube &c, unsigned int &idx);
    ///< generalize(c, idx) and push(c, idx)

    void add_blocked(Cube &c, unsigned int idx);
    ///< add the clause ~c to F[1]...F[idx]

    Cube get_next(const Cube &c);
    ///< return the cube c'

    void get_cube_from_model(Cube &out);
    ///< extract a cube from the satisfying assignment found by the SMT solver
    ///< for the last solve() call

    bool subsumes(const Cube &a, const Cube &b);
    ///< checks whether a subsumes b

    bool is_blocked(const Cube &c, unsigned int idx);
    ///< returns true if c does not intersect F[idx]

    bool is_initial(const Cube &c);
    ///< returns true if c intersects the initial states

    void ensure_not_initial(Cube &c, Cube &rest);
    ///< assuming that is_initial(c & rest) is false, moves literals from rest
    ///< to c until is_initial(c) is false

    void activate_frame(unsigned int idx);
    ///< activates the frame at index "idx" in the SMT solver. if idx is
    ///< equal to depth(), deactivates all frames

    void activate_trans_bad(bool trans_active, bool bad_active);
    ///< activates/deactivates the constraints for the transition relation and
    ///< the bad states in the SMT solver, according to the input values

    void activate_bad();
    ///< shortcut for activate_trans_bad(false, true)

    void activate_trans();
    ///< shortcut for activate_trans_bad(true, false)

    bool solve();
    ///< wrapper for Solver::check() that also updates statistics

    void hard_reset();
    ///< reset algorithm instance by flushing internal data structures

    void soft_reset();
    ///< reset algorithm instance by partially flushing internal data
    ///< structures. this method doesn't clear last stored frames.

    void reset_solver();
    ///< reset and reinitialize the underlying SMT solver

    size_t depth();
    ///< return the maximum index in the current trace F

    msat_term make_label(const char *name=NULL);
    ///< create a fresh Boolean label

    msat_term var(msat_term t);
    ///< see var() in utils.h

    msat_term lit(msat_term t, bool neg);
    ///< see lit() in utils.h

    Logger &logcube(unsigned int level, const Cube &c);
    ///< logger function for cubes

    bool initiation_check(const std::vector<TermList> &inv);
    ///< check if invariant satisfies initiation, I => Inv

    bool consecution_check(const std::vector<TermList> &inv);
    ///< check if invariant satisfies consecution, Inv & T => Inv'

    void remove_clauses_violating_init(std::vector<TermList> &cubes);
    ///< remove clauses from cubes not in the initial states set

    bool find_minimal_inductive_subclause(std::vector<TermList> &cubes);
    ///< find minimal inductive subclause c (subset of cubes)
    ///< such that c & T => c'. Return true and replace cubes with found
    ///< sublcause, if one exists. Otherwise, return false.


    void print_frames();
    ///< print all cubes in frames to stdout

    void get_old_frame(unsigned int idx, std::list<Cube *> &frame);
    ///< returns the cubes in frame at idx from the set of frames
    ///< for the last model checked

    void get_old_frame(std::vector<Cube> &frame);
    ///< returns all cubes in the frames for the last model checked

    inline void frame_repair(unsigned int idx, std::list<Cube *> &frame);

    void find_cubes_at_fault(unsigned int idx, std::list<Cube *> &frame,
                             std::list<Cube *> &cubes);

    //------------------------------------------------------------------------
    // internal state
    //------------------------------------------------------------------------

    const TransitionSystem  *ts_; ///< the input transition system
    const Options &opts_; ///< algorithm options

    VarProvider vp_; ///< provider for fresh variables
    std::minstd_rand rng_; ///< pseudo-random number generator

    Solver solver_; ///< the SMT solver

    msat_term init_label_;
    ///< activation label for init. Activation labels are used for incremental
    ///< solving, for temporarily disabling some constraints. If "l" is an
    ///< activation label for a formula "f", we add the formula "l -> f" to the
    ///< SMT solver, and then add "l" to the list of assumptions whenever we
    ///< need to consider "f" for the SMT query, and "~l" whenever we want to
    ///< temporarily disable "f"

    msat_term trans_label_; ///< activation label for trans (see above)
    msat_term bad_label_; ///< activation label for ~prop (see above)

    FrameList frames_;
    ///< the trace of clauses F. This is represented using a "delta encoding",
    ///< in which each clause is stored only in the last index of F in which
    ///< it occurs. Moreover, we store cubes "c" instead of clauses "~c",
    ///< so that all the internal methods only have to deal with cubes.
    ///< Therefore, the actual set of clauses corresponding to F[k]
    ///< can be retrieved by taking the negation of all the cubes in
    ///< frames_[k], ..., frames_[depth()].
    ///<
    ///< Whenever a cube is pushed forward from i to i+1, it is explicitly
    ///< removed from frames_[i] before adding it  to frames_[i+1].
    ///< Therefore, a fixpoint can be detected by simply checking if frames_[j]
    ///< is empty

    TermList frame_labels_;
    ///< activation labels for trace elements. Given the delta encoding
    ///< described above, we activate F[i] by adding ~frame_labels_[0], ...,
    ///< ~frame_labels_[i-1] and frame_labels_[i], ..., frame_labels_[depth()]
    ///< to the SMT assumptions

    TermList state_vars_;
    ///< state variables as seen by IC3. For purely Boolean systems, this is
    ///< identical to the state vars in ts_. For infinite-state systems, this
    ///< set contains all the Boolean state vars of ts_, plus one fresh Boolean
    ///< label for each predicate in the current abstraction (see below the
    ///< description of pred2lbl_). All cubes and clauses handled by IC3 are
    ///< always expressed over this set of variables

    TermMap lbl2next_;
    ///< if l1 is the label for pred and l2 is the label for ts_.next(pred),
    ///< then lbl2next_[l1] = l2. This is used in get_next()

    std::vector<TermList> cex_;
    ///< counterexample trace if property failed

    std::vector<TermList> invariant_;
    ///< inductive invariant if property passed

    Cube tmp_; ///< temporary storage used by cube generalization methods

    TermSet gen_needed_;
    ///< set of literals that cannot be dropped from the current cube. used in
    ///< generalize()

    uint32_t last_reset_calls_; ///< number of SMT queries since last reset

    uint32_t model_count_;
    ///< count of models checked

    bool last_checked_;
    ///< result from previous run of verification

    std::vector<TermList> last_cex_;
    ///< cex from previous run of verification

    std::vector<TermList> last_invariant_;
    ///< invariant from previous run of verification

    std::vector<Cube> minimal_subclause_;
    ///< minimal inductive subclause from last known invariant

    msat_term minimal_subclause_label_;
    ///< activation label for minimal inductive

    unsigned int frame_number = 0;
    ///< maintain current active frame

    std::vector<std::list<Cube>> old_frames_;

    std::vector<Cube> min_clause_;

    //------------------------------------------------------------------------
    // statistics
    //------------------------------------------------------------------------
    uint32_t num_solve_calls_;
    uint32_t num_solve_sat_calls_;
    uint32_t num_solve_unsat_calls_;
    uint32_t num_solver_reset_;
    uint32_t num_added_cubes_;
    uint32_t num_subsumed_cubes_;
    uint32_t num_block_;
    uint32_t max_cube_size_;
    double avg_cube_size_;
    double solve_time_;
    double solve_sat_time_;
    double solve_unsat_time_;
    double block_time_;
    double generalize_and_push_time_;
    double rec_block_time_;
    double propagate_time_;
    double total_time_;
};

} // namespace nexus
