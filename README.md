Section 4: Interval analysis on NTT program
--------------------------------------
```
$ dune build interval_abstract.exe
$ _build/default/interval_abstract.exe
ok
```

Section 5.3: Verifying modular-reduction algorithms
--------------------------------------
```
$ dune build z3_verify.exe
$ _build/default/z3_verify.exe
Verifying Barrett reduction impl by Z3...
Verifying Montgomery multiplication impl by Z3... (this is slow)
ok
```

Section 5.4: Proving correctness of the simplifid NTT program
----------------------------------------------------
```
$ dune build symbolic.exe
$ _build/default/symbolic.exe
ok
```
