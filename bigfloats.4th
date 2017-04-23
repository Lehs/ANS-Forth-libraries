\ ANS-Forth big rational with big floating point representation
\ https://github.com/Lehs/ANS-Forth-libraries

false [if]
Big integer rationals are stored as a pair of big integers on the big stack as

q 123456789012345678901234/1111111111114242642

and printed out as

q. 61728394506172839450617/555555555557121321

q+, q-, q*, q/, qdrop, qdup, qswap, qover, qrot, qnip, qtuck and qpick
works as should be expected.

f 123.456789012345

put the corresponding rational on stack and 

7 qf. print the rational at big stack as a float with 7 decimals.
[then]

s" bigintegers.4th" included
\ https://github.com/Lehs/ANS-Forth-libraries

: qreduce \ q -- q'
  bover bover bgcd btuck b/ brot brot b/ bswap ;

: q \ -- q
  [char] / parse vpush v>b b qreduce ;
\ q 1234567890/123456789

: b|. b>v$ type bdrop ;

: q. \ q --
  bswap b|. ." /" b. ;

: q* \ q1 q2 -- q3
  brot b* brot brot b* bswap qreduce ;

: q/ \ q1 q2 -- q3
  bswap q* ;

\ a b c d -- ad+bc/bd
: q+ \ q1 q2 -- q3
  >bx brot bx b*         \ b c ad 
  bswap 2 bpick b* b+    \ b ad+bc
  bswap bx> b* ;         \ ad+bc bd

: q- \ q1 q2 -- q3
  >bx brot bx b*         \ b c ad 
  bswap 2 bpick b* b-    \ b ad+bc
  bswap bx> b* ;         \ ad+bc bd

: qdrop  bdrop bdrop ;
: qdup  bover bover ;
: qover  3 bpick 3 bpick ;
: qpick  2* 1+ dup bpick bpick ;
: qnip  brot bdrop brot bdrop ;
: qswap  brot >bx brot bx> ;
: qtuck  qswap qover ;
: qrot  >bx >bx qswap bx> bx> qswap ;

: .q  \ print stack, provided that big stack only contains q-numbers
  bempty 0=
  if cr qdup q. >bx >bx recurse bx> bx> then ;

: v& \ v1 v2 -- v3
  nextfree bdrop bvp @ ! ;

: vr0> \ v -- v flag
  false nextfree bvp @ cell+ @
  do i c@ [char] 0 <>
     if 0= leave then
  loop ;

: vpush~ \ ad n -- v
  >r nextfree r@ over + tov r> cmove ;

: bs** \ b n -- b^n
  bone 0 do bover b* loop bnip ;
 
: f \ -- q
  [char] . parse vpush 
  bl parse ?dup 
  if tuck vpush~ vr0> 
     if v& v>b bten bs** qreduce
     else drop bdrop v>b bone 
     then 
  else drop v>b bone
  then ;
\ f 123.456789

: qf. \ q n --   n is the number of decimals
  btuck b/mod b|.
  bten bs** b* bswap b/ ." ." b. ;

