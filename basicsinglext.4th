\ Basic number theoretic package, extension to ANS Forth
\ s" basicsinglext.4th" included

: wordexist bl word find nip ;

cell 8 * constant bits

: sqrtf \ u -- floor
  0 d>f fsqrt f>s ;

: log~ \ n -- 1+log n    2-logarithm
  bits locals| lg |
  bits 0 
  do 1 rshift ?dup 0=
     if i 1+ to lg 
        leave 
     then 
  loop lg ;

: umin \ u1 u2 -- u
  2dup u< if drop else nip then ;

: umax \ u1 u2 -- u
  2dup u< if nip else drop then ;

: umod \ u q -- u(mod q)
  0 swap um/mod drop ; 

: ugcd \ u1 u2 -- u      \ Greatest common divisor
  2dup u< if swap then   \ smallest of a b on top of stack (tos)
  ?dup 0= if exit then   \ return second value if tos is zero
  begin tuck             \ y x y first time b a b
     0 swap um/mod       \ y x 0 y --> y r q
     drop dup 0=         \ y r [r=0]
  until drop ;           \ y

: u*mod \ u1 u2 u3 -- u1*u2(mod u3)
  >r r@ umod swap r@ umod um*
  r> um/mod drop ;

: u**mod \ b a m -- x
  locals| m a b | 
  1                      \ preparation for repeated multiplication
  a log~ 0               \ n 0 n is the number of binary digits in a
  ?do a 1 i lshift and   \ flag the i-th digit of a is 0/1
     if b m u*mod        \ multiply if flag
     then b dup m        \ square b for each i: b b^2 b^4 b^8 ...
     u*mod to b          \ new squared number to b
  loop ;                 \ result of the repeated multiplication

cell 4 =
[if]
: isprime \ u -- flag
  dup 5 u< if 2 4 within exit then
  dup 1 and 0= if 0= exit then
  true over sqrtf 3 umax 1+ 3
  do over i umod 0= 
     if 0= leave then 2
  +loop nip ;
[else]
: 2/mod \ n -- r q
  dup 1 and swap 1 rshift ;

: get-rs \ numb r -- r s     numb odd
  0 locals| r numb | 
  numb 1-
  begin dup 2/mod swap 0=       \ n qoute rest=0
  while nip r 1+ to r
  repeat 2drop
  r numb 1- r rshift ;

: rabin-miller1 \ numb -- flag    numb odd
  dup get-rs false
  locals| flag s r numb |
  2 s numb u**mod 1 =
  if true exit
  then r 0
  ?do 2 s i lshift numb u**mod numb 1- =
     if true to flag leave then
  loop flag ;

create pnr
2 c, 3 c, 5 c, 7 c, 11 c, 13 c, 17 c, 19 c, 23 c, 29 c, 31 c, 37 c,

: rabin-miller2 \ numb a -- flag 
  over get-rs false locals| flag s r a numb |
  a s numb u**mod 1 =
  if true exit
  then r 0
  ?do a s i lshift numb u**mod numb 1- =
     if true to flag leave then
  loop flag ;

: rmx \ numb -- n 64 bit integers
  dup 2047 u< if drop 1 exit then
  dup 1373653 u< if drop 2 exit then
  dup 25326001 u< if drop 3 exit then
  dup 3215031751 u< if drop 4 exit then
  dup 2152302898747 u< if drop 5 exit then
  dup 3474749660383 u< if drop 6 exit then
  dup 341550071728321 u< if drop 8 exit then
  3825123056546413051 u< if 11 else 12 then ;

: isprime \ numb -- flag 
  dup rmx 0
  do dup i pnr + c@ rabin-miller2 0=
     if 0= leave then
  loop 0= 0= ;
[then]

: nextprime \ u -- p
  begin dup isprime 0=
  while 1+
  repeat ;

: func \ numb n -- m 
  dup um* 1 0 d+ rot um/mod drop ; 

: pollard1 \ numb start -- pfac flag     numb is an odd composite
  dup dup locals| beta alpha start numb | 0   
  begin drop numb alpha func to alpha
     numb dup beta func func to beta
     alpha beta - abs                  \ |alpha-beta|
     numb ugcd dup numb =              \ gcd flag 
     if false exit 
     then dup 1 = 0=                   \ gcd<>1 
  until true ;

: pollard2 \ numb -- prime numb>1
  dup 1 and 0= if drop 2 exit then
  dup isprime if exit then
  dup sqrtf dup * over = 
  if sqrtf exit then -1 2              \ numb 100 0 
  do dup i pollard1                    \ numb pfac flag
     if leave                          \ numb pfac
     then drop                         \ numb
  loop nip ;                           \ pfac

: pollard \ n -- p1 ... pk      
  dup pollard2 2dup =                  \ n q f=
  if drop exit                         \ n
  then dup >r 
  0 swap um/mod nip recurse            \ q n/q
  r> recurse ;

: pollard# \ numb -- p1 ... pk k
  depth >r
  pollard depth r> - 1+ ;

\ Sorting the stack

: lower \ m1 ... mn m n+1 -- m1 ... m ... mi n+1  
\ lower m on stack until next number not is greater
  dup 2 =
  if drop 2dup u>
     if swap
     then 2 exit
  then >r 2dup u> 0= 
  if r> exit
  then r> rot >r 
  1- recurse 1+ r> swap ;

: sort \ m1 ... mn n -- s1 ... sn n o(n²)
  dup 3 <
  if dup 2 =
     if drop 2dup u> 
        if swap 
        then 2 
     then exit
  then dup >r
  1- recurse roll 
  r> lower ;

: primefactors \ u -- q1 q2 ... qn n  q1<=q2<=...<=qn
  pollard# sort ;

wordexist sp!
[if]
sp@ sp@ - 0< [if] ' - [else] ' + [then] constant op
: drops \ a1 ... an n --
  sp@ over 1+ cells op execute sp! ;
[else]
: drops \ a1 ... an n --
  0 ?do drop loop ;
[then]

: radical \ n -- r 
  1 locals| p n |
  n primefactors 1 swap 0 
  do over p =
     if nip
     else over to p *
     then 
  loop ; 
\ The product of all different prime factors of n

: totients \ n -- t 
  1 locals| tot |
  primefactors 0
  do 2dup =
     if tot * to tot
     else 1- tot * to tot
     then
  loop tot ;
\ The number of integers k:1,...,n-1 
\ whith gcd(k,n)=1

: mobius \ n -- m
  dup 2 u< if drop 1 exit then
  1 swap
  primefactors
  dup true locals| sqrfree facts | 0
  do 2dup =
     if false to sqrfree
        facts i - drops leave 
     then drop
  loop sqrfree
  if facts 1 and
     if -1
     else 1
     then
  else 0
  then nip ;
\ m=0 if n not squarefree
\ m=1 if even numbers of prime factors
\ m=-1 if odd numbers of prime factors

: bigomega \ n -- b 
  dup 2 u< if drop 0 exit then
  pollard# dup >r drops r> ;
\ The number of prime factors of n

: smallomega \ n -- s      two pollard!
  dup 2 u< if drop 0 exit then
  radical 
  pollard# dup >r drops r> ;
\ The number of different prime factors of n

: legendre \ a p -- i    p odd prime
  tuck dup 1- 2/ swap u**mod dup 1 >
  if swap - else nip then ;
\ (a/p)=1 if exist n with n^2=a(mod p) and a<>0
\ (a/p)=-1 if not exist n with n^2=a(mod p)
\ (a/p)=0 if a=0(mod p)

: tau \ u -- n
  1 0 locals| m n |
  primefactors 0
  do 2dup =
     if m 1+ to m drop
     else drop m 2 + n * to n 0 to m
     then
  loop n ;
\ The number of divisors of u

: sigma \ u -- s
  1 1 locals| p s |
  primefactors 0
  do 2dup =
     if p * to p
     else dup dup * p * 1- swap 1- / 
        s * to s
        1 to p
     then
  loop s ;
\ The sum of all divisors of u 
