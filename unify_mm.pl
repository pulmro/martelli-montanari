% Unify Martelli-Montanari. Implementation of Martelli-Montanari unification algorithm
% Copyright (C) 2009  Emanuele Bigiarini

% This program is free software: you can redistribute it and/or modify
% it under the terms of the GNU General Public License as published by
% the Free Software Foundation, either version 3 of the License, or
% (at your option) any later version.

% This program is distributed in the hope that it will be useful,
% but WITHOUT ANY WARRANTY; without even the implied warranty of
% MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
% GNU General Public License for more details.

% You should have received a copy of the GNU General Public License
% along with this program.  If not, see <http://www.gnu.org/licenses/>.
% --------------------------------------------------------------------------------------------------

% unify_mm(List, System)
% System è il sistema di equazioni in forma risolta che seguono dal problema di unificare i termini 
% nella lista List.

unify_mm(L,T)		:- prepara(L,Tree,Z,Counter), unify_sys(Tree,[],T,Z,Counter).

%++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
%			PREDICATI DELL'ALGORITMO DI UNIFICAZIONE

% unify_sys(Tree, Solved_sys, Temp_solved_sys, Zero_meq_list, Counter)
% Temp_solved_sys è il sistema temoraneamente risolto,
% Counter il numero di equazioni ancora da eliminare
unify_sys(_,T,T,[],0)		:-	!.
unify_sys(_,_,_,[],_)			:-	write('Error: cycle'),
						fail, !.
unify_sys(U,T,Ts,[{0,S=[]}|Z],Co)	:-	!, Co_n is Co-1, unify_sys(U,[S=nil|T],Ts,Z,Co_n).
unify_sys(U,T,Ts,[{0,S=M}|Z],Co)	:-	cpf(M,C,F-[]),
						compact(F,U,Uo,Z,Zo,0,El),
						Co_n is Co - El -1,
						unify_sys(Uo,[S=C|T],Ts,Zo,Co_n).

% cpf(Multi_term,Common,Frontier)
% Common è la parte comune di Multiterm, Frontier è la sua frontiera.
cpf(T,Fu,Nil-Nil)		:-	functor(T,Fu,0),!.
cpf([],[],[]-[])			:-	!.
cpf([{[]=Mi}|T],[Ci|Ct],F)	:-	!, append_d_l(Fi,Ft,F), cpf(Mi,Ci,Fi), cpf(T,Ct,Ft).

cpf([{[S|St]=Mi}|T],[S|Ct],F)	:-	!, append_d_l([{[S|St]=Mi}|Nil]-Nil,Ft,F), cpf(T,Ct,Ft).

cpf(T,C,F)		:-	functor(T,Fu,N), functor(C,Fu,N),
				T=..[Fu|A1], C=..[Fu|A2],
				cpf(A1,A2,F).

% compact(Frontier, U_old, U_new, Z_old, Z_new, El_temp, El)
% U_new è l'albero risultato della compattazione della frontiera nell'albero U_old,
%  aggiornando la list Z_old delle multiequazioni con contatore 0 e il contatore
%  El_temp delle equazioni già eliminate.
compact([],U,U,Z,Z,El,El)		:-	!.
compact([{[V|Se]=M}|T],Ui,Uo,Zi,Zo,El_t,El)	:-
						m_tree(Ui,V,{Cv,Sv=Mv},Mef,Ut),
						Cv1 is Cv - 1,
						compact_iter(Se,Ut,{Cv1,Sv=Mv},Mef,Ut1,M,El_t,El_1),
						update_zerome(Mef,Zi,Zt),
						compact(T,Ut1,Uo,Zt,Zo,El_1,El).

compact_iter([],U,{Ct,St=Mt},{Ct,St=Mf},U,M,El,El)	:-
							merge_mt(Mt,M,Mf).
compact_iter([H|T],Ui,{Ct,St=Mt},Mef,Uo,M,El_t,El)	:-
							mbchk(H,St), !,
							Ct1 is Ct -1,
							m_tree(Ui,H,_,Mef,Ut),
							compact_iter(T,Ut,{Ct1,St=Mt},Mef,Uo,M,El_t,El).
compact_iter([H|T],Ui,{Ct,St=Mt},Mef,Uo,M,El_t,El)	:-
							m_tree(Ui,H,{Ch,Sh=Mh},Mef,Ut),
							Ch1 is Ch -1,
							merge_me({Ct,St=Mt},{Ch1,Sh=Mh},MeT),
							El_tt is El_t + 1,
							compact_iter(T,Ut,MeT,Mef,Uo,M,El_tt,El).

% update_zerome(Mult_eq, Old_Zero_list, New_Zero_list)
% New_Zero_list è la Old_Zero_list con in testa Mult_eq se ha contatore 0.
update_zerome({0,S=M},Zi,[{0,S=M}|Zi])	:- !.
update_zerome(_,Zi,Zi).

%_________________Manipolazione di multitermini e multiequazioni_____________________________________

% merge_mt(Mult1,Mult2,Mult3)
% Mult3 è (se esiste) il multitermine risultato del merge di Mult1 e Mult2
merge_mt([],M2,M2)		:-	!.
merge_mt(M1,[],M1)		:-	!.
merge_mt([{S1i=M1i}|T1],[{S2i=M2i}|T2],[{S3i=M3i}|T3])	:- !,
							union_se(S1i,S2i,S3i),
							merge_mt(M1i,M2i,M3i),
							merge_mt(T1,T2,T3).
merge_mt(M1,M2,M3)		:-	M1=..[F|A1], M2=..[F|A2], functor(M1,F,N), functor(M2,F,N),
					functor(M3,F,N), M3=..[F|A3],
					merge_mt(A1,A2,A3).

% merge_me(Mult_eq1,Mult_eq2,Mult_eq3)
% Mult_eq3 è (se esiste) la multiequazione risultato del merge di Mult_eq1 e Mult_eq2
merge_me(M1,M2,M1)				:-	M1==M2,!.
merge_me({C1,S1=T1},{C2,S2=T2},M3)		:-	length(S1,N1),
							length(S2,N2),
							N1 < N2,
							merge_me({C2,S2=T2},{C1,S1=T1},M3).
merge_me({C1,S1=T1},{C2,S2=T2},{C3,S3=T3})	:-	C3 is C1 + C2,
							append(S2,S1,S3), %NON EFFICIENTE
							merge_mt(T1,T2,T3).

%++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
%					PREDICATI DI PREPARAZIONE

%__________________Predicati per la trasformazione da MultiSet in MultiTerm____________________________

% trasf_begin(List,Meq,Vars)
% Meq è la multiequazione risultante la trasformazione della lista List di termini, dove Vars è la lista
%  di variabili presenti all'interno dei termini.

trasf_begin(L,{S=R},V)		:-	separa(L,S,M,_), trasf(M,R,V).

trasf([],[],X-X)		:-	!.
trasf([[S,M]|T],[{S=Rm}|Rt],V)	:-	!, append_d_l(Vm,Vt,V), trasf(M,Rm,Vm), trasf(T,Rt,Vt).

trasf(L,R,V)			:-	functor_list(L,F,N), args(L,N,[],A,X-X,Vl),
					append_d_l(Vl,Vt,V), functor(R,F,N), R=..[F|R1],
					trasf(A,R1,Vt).

% Predicati ausiliari:

% functor_list(List,Funtore,Arietà)
% Come functor/3 ma valido per liste di termini.
functor_list([],nil,nil)	:- !.
functor_list(L,F,N)	:- functor_list_1(L,F,N).

functor_list_1([],_,_).
functor_list_1([T|L],F,N)	:- functor(T,F,N), functor_list_1(L,F,N).

% arg_list(Indice,List,Args)
% Come arg/3 ma valido per liste di termini.
arg_list(_,[],[])		:-	!.
arg_list(I,[H|T],[A|At])	:-	arg(I,H,A), arg_list(I,T,At).

% args(List,Indice,Temp_args,Args,Temp_vars,Vars)
% Lo scopo di questo predicato è quello di raggruppare gli argomenti di stesso indice di termini diversi, a sua volta 
%  distinti tra variabili e non. Un esempio è il goal:
% 	?- args([f(X1,X2),f(g(X3),b),f(g(t),X4)], 2, [], A, Nil-Nil, Vars-[]).
% 	A = [[[X1], [g(X3), g(t)]], [[X2, X4], [b]]],
%	Nil = [],
%	Vars = [X1, X4, X2].
args(_,0,A,A,V,V)	:-	!.
args(L,I,At,A,Vt,V)	:-	arg_list(I,L,Ai), separa(Ai,S,M,Vi), append_d_l(Vi,Vt,Vtt), I1 is I-1, 
				args(L,I1,[[S,M]|At],A,Vtt,V).

% separa(List,Vars,NonVars,Vars_d_l)
% Vars e NonVars sono liste di variabili e non variabili ottenute da List. Vars_d_l è la lista differenza.
separa([],[],[],Nil-Nil).
separa([H|T],[H|St],M,V)	:-	var(H), !, append_d_l(Vt, [H|L] - L, V), separa(T,St,M,Vt).
separa([H|T],S,[H|Mt],V)	:-	separa(T,S,Mt,V).


%____Predicati per la costruzione del sistema di equazioni e la trasformazione in albero binario bilanciato____

% prepara(List,Tree,Zero_meq,Num_eq)
% Tree è l'albero di equazioni, Zero_meq è la lista di equaz con contatore 0, 
%  Num_eq è il numero iniziale di equazioni a partire dalla lista List di termini.
prepara(L,Tree,Z,N)		:-
				trasf_begin(L,Me,V-[]), msort(V,Vars), 
				build_sys(Vars,nil,0,X-X,Sy-[],0,N1), N is N1+1,
				sys_tree(Sy,Me,Tree,Z).

% build_sys(Vars, Last_var, Num_last_var, Temp_sys, Sys, Temp_num_eq, Num_eq)
% Sys è il sistema iniziale (necessario per innescare l'algoritmo di unificazione) creato
%  a partire dalla lista di variabili, in cui si tiene conto del numero di occorrenze di ogni
%  variabile. Infine Num_eq è il numero di equazioni.
% Un esempio è il goal:
%  ?- build_sys([X1,X2,X2,X3],nil,0,Nil-Nil,Sys-[],0,N).
%  Nil = [{1, [X1]=[]}, {2, [X2]=[]}, {1, [X3]=[]}],
%  Sys = [{1, [X1]=[]}, {2, [X2]=[]}, {1, [X3]=[]}],
%  N = 3.
build_sys([],nil,0,Sy,Sy,Num,Num)	:- !.
build_sys([],P,C,St,Sy,Num_t,Num)	:-
					!, append_d_l(St,[{C,[P]=[]}|L]-L,Sy), Num is Num_t+1.
build_sys([V|T],nil,0,Syt,Sy,Num_t,Num)	:-
					!, build_sys(T,V,1,Syt,Sy,Num_t,Num).
build_sys([V|T],P,C,Syt,Sy,Num_t,Num)	:-
					V==P,!, C1 is C+1, build_sys(T,P,C1,Syt,Sy,Num_t,Num).
build_sys([V|T],P,C,Syt,Sy,Num_t,Num)	:-
					append_d_l(Syt,[{C,[P]=[]}|L]-L,Sytt), Num_t1 is Num_t+1, 
					build_sys(T,V,1,Sytt,Sy,Num_t1,Num).

% sys_tree(System, M_equation, Tree, Z_meq_list)
% Tree è l'abero creato a partire dal sistema iniziale, facendo uso (se necessario) della multiequaz M_equation.
% Si aggiorna la lista di multiequazioni con contatore zero, se necessario.
sys_tree(Sys,{[]=M},Tree,Z)	:-	!, crea_albero(Sys,Tree), update_zerome({0,[New_var]=M},[],Z).
sys_tree(Sys,{S=M},Tree,Z)	:-	crea_albero(Sys,Tree_t), counter_me(Tree_t,0,S,{C,S=M},Tree),
					update_zerome({C,S=M},[],Z).

% counter_me(Tree_old,Counter,List_of_vars,M_equation,Tree_new)
% Predicato per il calcolo del numero di occorrenze delle variabili in List_of_vars all'interno del multitermine
%  (creato a partire dai termini da unificare). Tale numero è il contatore della multiequazione iniziale.
%  Aggiorna l'albero se necessario.
counter_me(Tree,C,[],{C,S=M},Tree)		:- !.
counter_me(Tree1,Ct,[H|T],{C,S=M},Tree)		:- 
						m_tree(Tree1,H,{C1,_=_},{C,S=M},Tree2), Ctt is Ct+C1, 
						counter_me(Tree2,Ctt,T,{C,S=M},Tree).


%_________________________Predicati per la gestione dell'albero________________________________________________

% crea_albero(System,Tree)
% Tree è l'albero bilanciato di nodi Variabile-Multiequazione a partire dal sistema System
crea_albero([],nil)	:- !.
crea_albero(Sy,[V-{C,[V]=M},L,R])	:-
					dividi(Sy,{C,[V]=M},L1,R1), crea_albero(L1,L), crea_albero(R1,R).

dividi(Sy,X,L,R)		:-	length(Sy,N), N1 is (N // 2) +1, dividi_2(Sy,N1,X,D-D,L,R).

dividi_2([H|T],1,H,L-[],L,T)	:-	!.
dividi_2([H|T],N,X,Lt,L,R)	:-	append_d_l(Lt,[H|Y]-Y,Ltt), N1 is N-1, dividi_2(T,N1,X,Ltt,L,R).


% m_tree(Tree_old,E,Me,Ms,Tree_new)
% Tree_new è l'albero Tree_old in cui al nodo E-Me è stata sostituita la m.equazione Me con la Ms 
m_tree(nil,_,{0,[]=[]},_,nil)			:-	!.
m_tree([N-Me,L,R],E,Me,Ms,[N-Ms,L,R])	:-	E==N, !.
m_tree([N-M,L,R],E,Me,Ms,[N-M,L1,R])	:-	E@<N, !, m_tree(L,E,Me,Ms,L1).
m_tree([N-M,L,R],E,Me,Ms,[N-M,L,R1])	:-	m_tree(R,E,Me,Ms,R1).


%++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
%					PREDICATI AUSILIARI

% mbchk(Element,List)
% Predicato che verifica se vi è un elemento uguale(identico) a Element nella lista List
mbchk(_,[]) :- fail.
mbchk(E,[H|_]) :- E==H , ! .
mbchk(E,[_|T]) :- mbchk(E,T).

% union_se(A,B,C)
% C è l'unione di A e B dove A e B sono insiemi di variabili.
union_se([],L,L)	:- !.
union_se([H|T], L, R) :-
	mbchk(H, L), !, 
	union_se(T, L, R).
union_se([H|T], L, [H|R]) :-
	union_se(T, L, R).

% append_d_l(L1,L2,L3)
% Concatenazione di liste differenza
append_d_l(X1 - X2, X2 - Y2, X1 - Y2).