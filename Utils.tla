This is a snapshot of a few operators from the TLA+
community modules at https://github.com/tlaplus/CommunityModules

------- MODULE Utils -------

MapThenFoldSet(op(_,_), base, f(_), choose(_), S) ==
  LET iter[s \in SUBSET S] ==
        IF s = {} THEN base
        ELSE LET x == choose(s)
             IN  op(f(x), iter[s \ {x}])
  IN  iter[S]

FoldFunctionOnSet(op(_,_), base, fun, indices) ==
  MapThenFoldSet(op, base, LAMBDA i : fun[i], LAMBDA s: CHOOSE x \in s : TRUE, indices)

============================