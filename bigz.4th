\ bigZ

s" bigintegers.4th" included
s" primecounting.4th" included
s" nestedsets.4th" included

\ cond ( n -- flag )
: sqr dup sqrtf dup * = ;
: sqrfree dup radical = ;
: twinprime dup isprime over 2 + isprime rot 2 - isprime or and ;  
: singleprime dup isprime swap twinprime 0= and ;
: semiprime bigomega 2 = ;
: primepower smallomega 1 = ;
: biprime smallomega 2 = ;

\ cond ( m n -- flag )
: coprime ugcd 1 = ;
: divide swap mod 0= ; 

: xzmerge \ s -- 
  xst zst setmove
  zswap zetmerge 
  zst xst setmove ; 
  
: xzmergered \ s --
  xst zst setmove
  zswap zetmerge 
  set-sort reduce
  zst xst setmove ; 

: factorset \ n -- set
  primefactors locals| n |
  n 0 do >zst loop
  n 2* negate >zst 
  set-sort 
  zst> 1- >zst ;

: set-of-factors \ s -- s'
  0 >xst
  foreach
  do zst> factorset zfence xzmerge loop
  xst zst setmove ;

\ testing for small (fast) single number divisors
\ of big number w in the intervall n,m-1
: sfac \ w -- w ?v | m n -- f 
  bdupeven if 2drop 2 bdup b2/ exit then
  0 locals| flag | 
  do bdup i pnr@ bs/mod 0= 
     if i pnr@ to flag leave then bdrop
  loop flag ;

: sfacset \ b -- b' set
  0                           \ count of the number of elements
  begin pi_plim 1 sfac ?dup 
  while >zst 2 - bnip
  repeat >zst reduce ;

1k bvariable alpha
1k bvariable beta

: bpollard1 \ w -- v | a -- f
  len1 cell = if drop b>s pollard2 s>b true exit then
  s>b bdup alpha b! beta b! bzero true
  begin bdrop
     alpha b@ bdup b* b1+ bover bmod alpha b!
     beta b@ bdup b* b1+ bover bmod
     bdup b* b1+ bover bmod beta b!
     alpha b@ beta b@ |b-|
     bover
     bgcd 
     b2dup= if bdrop 0= exit then
     bone b2dup= bdrop 0=
  until bnip ;

: bpollard2 \ w -- v
  bdup bisprime if exit then
  pi_plim 1 sfac ?dup if bdrop bdrop s>b exit then
  0 begin 1+ dup bpollard1 until drop ;
  
: bfac1 \ w -- v1...vn
  bdup bpollard2
  bone b2dup= bdrop
  if bdrop exit
  then btuck b/ recurse ;

: bfac bfac1 bdrop ;
  
: bfac# \ w -- v1...vn | -- n
  bdepth 1- bfac bdepth swap - ;

: bsfactors \ w -- v1 ... vn set
  sfacset bfac ;

\ -------------------------

[defined] sp0 0= [if]
s0 constant sp0
r0 constant rp0
[then]

: new-data-stack \ u -- 
  dup aligned allocate throw + dup sp0 ! sp! ; 

100000 cells new-data-stack
100001 cells allocate throw 100000 cells + align rp0 ! q
