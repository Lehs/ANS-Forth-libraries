
\ Testing tautologies

\ Propositional logic, variables
base @ 2 base !
cell 100 = [if]
11111111111111110000000000000000 constant p
11111111000000001111111100000000 constant q
11110000111100001111000011110000 constant r
11001100110011001100110011001100 constant s
10101010101010101010101010101010 constant t
[else]
1111111111111111111111111111111100000000000000000000000000000000 constant p
1111111111111111000000000000000011111111111111110000000000000000 constant q
1111111100000000111111110000000011111111000000001111111100000000 constant r
1111000011110000111100001111000011110000111100001111000011110000 constant s
1100110011001100110011001100110011001100110011001100110011001100 constant t
1010101010101010101010101010101010101010101010101010101010101010 constant u
[then]
base !

\ Propositional logic, constants
: n true xor ;                    \ negation
: -> swap n or ;                  \ implication
: <-> 2dup -> -rot swap -> and ;  \ equivalence
: & and ;
: v or ;
: <+> xor ;

: tautology? true = if ." is " else ." isn't " then ." a tautology" ;

\ examples:
\ p q v p -> tautology?
\ p q -> q r -> & r -> tautology?
\ p q & p -> tautology?
\ p q & r -> p q r -> -> <-> tautology?
\ ((p&q)->r)<->(p->(q->r))
