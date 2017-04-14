\ Signed big integers
\ Absolute values on b-stack and "negative flags" on data stack
false [if]
sb -80173583758375837581735317510835 cr sb.
-80173583758375837581735317510835  ok
[then]

s" bigintegers.4th" included

: sb. \ b f --
  if ." -" then b. ;

: sb  bl parse over c@ [char] - =
  dup >r if swap 1+ swap 1- then 
  vpush v>b r> ;

: sb+ \ b1 f1 b2 f2 -- b3 f3
  tuck xor
  if b~ swap 0= if 0= then
  else b+ 
  then ;

: sb- \ b1 f1 b2 f2 -- b3 f3
  0= sb+ ;

: sb* \ b1 f1 b2 f2 -- b3 f3
  xor b* ;

: sb/ \ b1 f1 b2 f2 -- b3 f3
  xor b/mod bswap b0= 0= 
  if dup if b1+ then then ;

: sbdup  bdup dup ;
: sbswap  bswap swap ;
: sbdrop  bdrop drop ;
: sbover  bover over ;
: sbtuck  btuck tuck ;
: sbrot  brot rot ;
: sbnip  bnip nip ;
: sbpick  dup bpick pick ;

: .sb  bempty 0=
  if cr sbdup sb. >r >bx recurse bx> r> then ;
  
: sb>s \ b f -- n
  b>s swap if negate then ;

: sbabs \ b f -- b 0
  drop 0 ;

: sbnegate \ b f -- b f'
  0= ;

