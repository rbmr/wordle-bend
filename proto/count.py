#!/usr/bin/env python3
"""Patch the emitted C with counters mirroring Rust's solver metrics.

states  : one per class-node search start (child_glist call; Rust increments
          states_evaluated in min_state_val just before it searches a set)
guesses : one per histogram start (the guess's class structure is computed;
          Rust increments guesses_evaluated per guess it evaluates)
scans   : one per candidate read in a histogram (hist5_one entry)
fill    : one per drain start (fill5_go entry)
Counts mirror src/ of the Rust solver, which reports them from
`states_evaluated` (incremented in min_state_val before it searches a set) and
`guesses_evaluated` (incremented per guess whose cheap bound still beats the
running best). Here:

  bend emitted C          Rust counter
  child_glist call        states_evaluated
  histogram start         guesses_evaluated (narrower on the Rust side: it only
                          counts guesses that set a new best lower bound)
  hist5_one entry         (no Rust equivalent; one per candidate read)
  fill5_go entry          (no Rust equivalent; one per guessed partition)

Usage: bend proto/src/main.bend -o solver.c
       python3 proto/bench/count.py solver.c count.c
       clang -O2 count.c -lpthread -lm -o solver && ./solver ...
The counters print on stderr at exit. Counters are plain globals, so run with
+RTS --threads 1 for exact values.
"""
import re, sys

src = open(sys.argv[1]).read()
n_states = src.count("WL_CASE(FID_solve_fast_child_glist)")
src = src.replace("WL_CASE(FID_solve_fast_child_glist)",
                  "WL_CASE(FID_solve_fast_child_glist)\n    CNT_states++;", 1) \
    if False else src.replace("WL_CASE(FID_solve_fast_child_glist)\n",
                              "WL_CASE(FID_solve_fast_child_glist)\n    CNT_states++;\n")
guesse_pat = "if (spin_solve_fast_hist5_go(e, _o_5, _row_0, _S_0, _buf_4, _skip_self_0, 0, _buf_1, _buf_3, 0ull, 0ull, _o_4[0]) == 0) {"
n_guess = src.count(guesse_pat)
src = src.replace(guesse_pat, "CNT_guesses++; " + guesse_pat)
n_scans = 0
pat = r'(INLINE [^\n]*spin_solve_fast_hist5_one\(Env e[^)]*\) \{\n  u32 wpoll = 0;)'
src, n_scans = re.subn(pat, r'\1 CNT_scans++;', src)
n_fill = 0
pat = r'(INLINE [^\n]*spin_solve_fast_fill5_go\(Env e[^)]*\) \{\n  u32 wpoll = 0;)'
src, n_fill = re.subn(pat, r'\1 CNT_fill++;', src)

decl = "static unsigned long CNT_states, CNT_guesses, CNT_scans, CNT_fill;\n"
decl += '__attribute__((destructor)) static void dump_counts(void){\n'
decl += '  fprintf(stderr, "COUNT states %lu guesses %lu scans %lu fill %lu\\n", CNT_states, CNT_guesses, CNT_scans, CNT_fill);\n'
decl += '}\n'
src = src.replace("// Types\n// =====\n", decl + "// Types\n// =====\n", 1)
open(sys.argv[2], 'w').write(src)
print("states-sites", n_states, "guess-sites", n_guess, "scans", n_scans, "fill", n_fill)
