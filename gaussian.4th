\ Gaussian integers
\ Typical restriction, the norm must be a single cell integer
false [if]
Complex numbers with integer components are represented as two singles on the stack.
3 -4 g. 3-4i  ok
There words g+ g- g* g/ gmod ggcd isgprime gfactors
More information on
https://forthmath.blogspot.se
https://github.com/Lehs/ANS-Forth-libraries
[then]

s" numbertheory.4th" included

: gnorm \ a b -- u
  dup * swap dup * + ;

: g< \ a b c d -- flag
  gnorm -rot gnorm u> ;

\ print single cell signed numbers without spaces
\ http://www.forth.com/starting-forth/sf7/sf7.html
: .sign-w/o-space \ n --
  dup 0< swap abs 0 <# #s rot sign #> type ;

: g. \ a b --
  2dup 0. d= if d. exit then
  swap dup \ b a a
  if over
     if dup .sign-w/o-space
     else dup .
     then
  then swap dup 0< 0= \ a b f
  if dup \ a b b
     if swap if ." +" then dup 1 > \ b f
        if .sign-w/o-space else drop then ." i" space
     else 2drop
     then
  else nip dup \ b b
     if dup -1 < \ b f
        if .sign-w/o-space else ." -" drop then ." i" space
     else drop
     then
  then ;

: .gs depth 2 < if exit then 2>r recurse 2r> 2dup g. ;
\ print the stack of Gaussian numbers

: g+ \ a b c d -- a+c b+d
  under+ under+ ;

: g- \ a b c d -- a-c b-d
  negate under+ negate under+ ;

: g* \ a b c d -- e f
  locals| d c b a |
  a c m* b d m* d- d>s a d m* b c m* d+ d>s ;

: g/ \ a b c d -- e f 
  locals| d c b a |
  c dup m* d dup m* d+ d>f
  a c m* b d m* d+ d>f fover f/
  b c m* a d m* d- d>f frot f/
  fswap f>d d>s f>d d>s ;

: g/' \ a b c d -- e f 
  locals| d c b a |
  c dup m* d dup m* d+ d>f
  a c m* b d m* d+ d>f fover f/ fround
  b c m* a d m* d- d>f frot f/ fround
  fswap f>d d>s f>d d>s ;

: gmod \ a b c d -- e f 
  2over 2over g/' g* g- ;

: ggcd \ a b c d -- e f     Euclid's algorithm
  0 0 locals| t s d c b a |
  a b c d g<
  if a c to a to c
     b d to b to d
  then
  begin c d or \ while c+id<>0
  while c to s d to t
     a b c d gmod to d to c
     t to b s to a
  repeat a b ;

: gnormal \ a b -- c d     c>=d and c>=0
  2dup abs swap abs >
  if 0 1 g* then over 0<
  if negate swap negate swap then ;

\ http://mathworld.wolfram.com/GaussianPrime.html
: gprime1 \ n -- flag
  abs dup isprime swap 3 and 3 = and ;

: isgprime \ a b -- flag
  over 0= if nip gprime1 exit then
  dup 0= if drop gprime1 exit then
  gnorm isprime ;

: .normgp \ a b norm -- 
  cr 8 .r space g. ;

: .gprime \ norm -- 
  locals| norm | 
  norm 2 = if 1 1 norm .normgp exit then 
  norm sqrtf 1+ 0 
  do i 0 
     ?do i j gnorm norm = 
        if i j isgprime 
           if j i norm .normgp then 
        then 
     loop 
  loop ; 

: .gps 1+ 2 do i .gprime loop ;

: gfunc \ a b x y -- u v 
  2dup g* -1 0 g+ 2swap gmod ;

: gpollard1 \ a b c d -- p q flag   a+ib not having factor 2
  2dup locals| beta2 beta1 alpha2 alpha1 b a | 0.
  begin 2drop a b alpha1 alpha2 gfunc to alpha2 to alpha1
     a b 2dup beta1 beta2 gfunc gfunc to beta2 to beta1
     alpha1 alpha2 beta1 beta2 g-
     a b ggcd 2dup a b d=
     if false exit
     then 2dup gnorm 1 = 0=
  until true ;

: gpollard2 \ a b -- p q 
  false locals| flag |
  2dup gnorm 1 = if exit then
  2dup 2 0 gmod d0= if 2drop 1 1 exit then
  2dup isgprime if exit then -1 1
  do i 0
     do 2dup j i gpollard1
        if true to flag leave then 2drop
     loop flag if leave then
  loop 2swap 2drop ;

: gfactors \ a b -- p1 q1 ... pk qk 
  2dup gpollard2 2over 2over gnorm -rot gnorm =
  if 2drop exit
  then 2dup 2>r g/ recurse 2r> recurse ;
\ For unknown reason gfactors doesn't work for GForth 0.7.0 32 bit Windows
\ It works for GForth Android, Gforth 64 bit Windows and SP-Forth+ Windows
