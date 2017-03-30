/*
 * This file is part of Nexus Model Checker.
 * Copyright (C) 2017 Rohit Dureja.
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
 */


#include "ic3.h"
#include <iostream>
#include <stdlib.h>
#include <signal.h>


using namespace vtsa2015;

IC3 *the_ic3 = NULL;


/** \brief Handler for raised interrupts
 *
 * This functions handles interrupts raised during the execution of Nexus
 *
 * \return 	None
 *
 * \param 	signo	Number of the signal that interrupted execution.
 */
void handle_interrupt(int signo)
{
    if (the_ic3) {
        the_ic3->print_stats();
    }
    std::cout 	<< "interrupted by signal " << signo << "\nunknown"
    			<< std::endl;

    exit(signo);
}

/** \brief Read the VMT file
 *
 * This function reads the VMT specified as input and splits it into the
 * transition relation, initial state, and bad property
 *
 * \return 			True if file parsed successfully, otherwise false.
 *
 * \param 	opts	Command line options in which opts.filename is the file
 * 					to read.
 *
 * \param 	ts		Transition system object to store read file contents.
 */
bool read_file(const Options &opts, TransitionSystem &ts)
{

    // create pointer to mathsat terms
    msat_term *terms;

    // create 2-D array to store annotations
    char **annots;

    // number of mathsat terms
    size_t n;

    // file handler for input file
    FILE *file = nullptr;

    // if filename specified in otions, then open the file
    if (!opts.filename.empty()) {
        file = fopen(opts.filename.c_str(), "r");
    }

    // error in opening file
    if (!file) {
        return false;
    }

    // parse the VMT file to an annotated list
    int err = msat_annotated_list_from_smtlib2_file(ts.get_env(), file, &n,
                                                    &terms, &annots);

    // if error in reading file
    if (err) {
        return false;
    }

    // unordered map of msat terms to msat terms
    TermMap statevars;

    // create msat terms
    msat_term init, trans, prop;

    // parse annotated list
    for (size_t i = 0; i < n; ++i) {
        std::string key(annots[2*i]);
        msat_term t = terms[i];
        if (key == "init") {
            init = t;
        } else if (key == "trans") {
            trans = t;
        } else if (key == "invar-property") {
            prop = t;
        } else if (key == "next") {
            std::string val(annots[2*i+1]);
            if (val.length() && val[0] == '|') {
                val = val.substr(1, val.length()-2);
            }
            msat_decl d = msat_find_decl(ts.get_env(), val.c_str());
            if (MSAT_ERROR_DECL(d)) {
                d = msat_declare_function(ts.get_env(), val.c_str(),
                                          msat_term_get_type(terms[i]));
            }
            msat_term n = msat_make_constant(ts.get_env(), d);
            statevars[t] = n;
        }
    }

    // initialize the transition system
    ts.initialize(statevars, init, trans, prop);

    // free up msat terms
    msat_free(terms);
    for (size_t i = 0; i < n; ++i) {
        msat_free(annots[2*i]);
        msat_free(annots[2*i+1]);
    }
    msat_free(annots);

    logger(1) << "parsed system with " << statevars.size() << " state variables"
              << endlog;

    return true;
}


Options parse_options(int argc, const char **argv)
{
    Options ret;

    bool ok = true;
    for (int i = 1; i < argc; ++i) {
        std::string a(argv[i]);
        if (a == "-v") {
            if (i+1 < argc) {
                std::istringstream buf(argv[i+1]);
                int val;
                if (buf >> val) {
                    ret.verbosity = val;
                    set_verbosity(val);
                } else {
                    ok = false;
                    break;
                }
                ++i;
            } else {
                ok = false;
                break;
            }
        } else if (a == "-w") {
            ret.witness = true;
        } else if (a == "-p") {
            ret.nopreds = true;
        } else if (a == "-t") {
            if (i+1 < argc) {
                ret.trace = argv[i+1];
                ++i;
            } else {
                ok = false;
                break;
            }
        } else if (a == "-r") {
            if (i+1 < argc) {
                std::istringstream buf(argv[i+1]);
                int val;
                if (buf >> val) {
                    ret.seed = val;
                } else {
                    ok = false;
                    break;
                }
                ++i;
            } else {
                ok = false;
                break;
            }
        } else if (a == "-s") {
            ret.stack = true;
        } else if (a == "-h" || a == "-help" || a == "--help") {
            std::cout << "USAGE: " << argv[0] << " [OPTIONS] FILENAME.vmt"
                      << "\n\n   -v N : set verbosity level"
                      << "\n   -w : print witness"
                      << "\n   -p : do not use initial predicates (if any)"
                      << "\n   -t NAME : dump SMT queries into NAME.main.smt2 "
                      << "and NAME.itp.smt2"
                      << "\n   -r VAL : set random seed to VAL "
                      << "(0 to disable [default])"
                      << "\n   -s : stack-based proof obligation management"
                      << std::endl;
            exit(0);
            break;
        } else if (a[0] != '-' && ret.filename.empty()) {
            ret.filename = a;
        } else {
            ok = false;
            break;
        }
    }
    if (!ok) {
        std::cout << "Error in parsing command-line options (use -h for help)"
                  << std::endl;
        exit(1);
    }

    return ret;
}


int main(int argc, const char **argv)
{
    // parse command line options
    Options options = parse_options(argc, argv);

    // create mathsat configuration and environment
    msat_config config = msat_create_config();
    msat_env env = msat_create_env(config);

    // destroy mathsat configurations
    msat_destroy_config(config);

    // EnvDeleter struct defined in utils.h
    // Object del_env of EnvDeleter deletes env
    // TODO: check if this is needed
    EnvDeleter del_env(env);


    // create object to store the tr
    TransitionSystem ts(env);

    // read_ts parses the VMT file
    // defined in main.cpp
    if (!read_file(options, ts)) {
        // error in reading file
        std::cout << "ERROR reading input" << std::endl;
        return 1;
    }

    // at this point model has been and stored in ts

    // create IC3 instance
    IC3 ic3ia(ts, options);


    signal(SIGINT, handle_interrupt);


    the_ic3 = &ic3ia;

    // check the transition system
    bool safe = ic3ia.prove();

    if (options.witness) {
        std::vector<TermList> wit;
        if (!ic3ia.witness(wit)) {
            std::cout << "ERROR computing witness" << std::endl;
        } else {
            std::cout << (safe ? "invariant" : "counterexample") << "\n";
            for (size_t i = 0; i < wit.size(); ++i) {
                TermList &w = wit[i];
                std::cout << ";; " << (safe ? "clause " : "step ") << i
                          << "\n" << (safe ? "(or" : "(and") << "\n";
                for (msat_term t : w) {
                    std::cout << "  " << logterm(env, t) << "\n";
                }
                std::cout << ")\n";
            }
            std::cout.flush();
        }
    }

    ic3ia.print_stats();

    std::cout << (safe ? "safe" : "unsafe") << std::endl;
    return 0;
}
