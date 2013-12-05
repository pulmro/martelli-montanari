martelli-montanari
==================

An implementation of Martelli-Montanari unification algorithm for Prolog written in Prolog,
based on the article "A. Martelli, U. Montanari, An Efficient Unification Algorithm" in
ACM TOPLAS, 1982.
Martelli-Montanari algorithm advantages are sound unification (it realizes the occur check:
unification of a variable V and a structure S that contains it will fail, avoiding loops);



Usage:
The predicate unify_mm/2 has to be called to realize the unification

unify_mm(List, System)

where List is the list of terms to unify and System is the triangular system of multi-equations.
Examples:

?- unify_mm([X,f(X)],T_sys)
Error: cycle
false.

?- unify_mm([X1,f(X2,X3),f(X3,X2)],T_sys)
T_sys = [[X3,X2]=nil, [X1]=f(X2,X3)].

T_sys contains the triangular system, i.e the system solved:
the structure List=t you get in the T_sys system means that the variables in the List are all
unified to term t.