\ Prime counting via the sieve of Eratosthenes

s" numbertheory.4th" included

: 8/mod \ n -- r q
  dup 7 and swap 3 rshift ;

: prevprime \ numb -- prime 
  dup 3 u< if drop 2 exit then
  1- 1 or
  begin dup isprime 0=
  while 2 -
  repeat ;

wordexist under+ 0=
[if]
: under+ \ a b c -- a+c b 
  rot + swap ;
[then]

: 65536/mod \ n -- r q 
  dup 65535 and swap 16 rshift ;

\ bit arrays

: adbit \ i ad -- j a 
  swap 8/mod rot + ;

: setbit \ i ad --
  adbit 1 rot lshift over c@ or swap c! ;

: tglbit \ i ad --
  adbit 1 rot lshift over c@ xor swap c! ;

: clrbit \ i ad --
  adbit 1 rot lshift 255 xor over c@ and swap c! ;

: bit@ \ i ad -- bit
  adbit c@ swap rshift 1 and ;

: bit! \ bit i ad --
  rot if setbit else clrbit then ;

: bit? \ i ad -- f 
  bit@ negate ;

: bitarray \ bits -- ad | n -- bit
  8/mod swap 0= 0= negate + allocate throw
  create dup ,
  does> @ swap 8/mod rot + bit@ ;

\ multiple byte read/write in arrays

variable ebuf
1 ebuf ! ebuf c@ negate
[if] \ little-endian
: mb! \ n ad i -- 
  2>r ebuf ! ebuf 2r> cmove ;

: mb@ \ ad i -- n 
  ebuf 0 over ! swap cmove ebuf @ ;
[else] \ big-endian
: mb! \ n ad i -- 
  2>r ebuf ! ebuf cell + r@ - 2r> cmove ;

: mb@ \ ad i -- n 
  ebuf 0 over ! cell + over - swap cmove ebuf @ ;
[then]

\ the sieve of Eratosthenes 
\ three different buffer sizes

\ 0xfffff constant plim 
\ 82025 constant pi_plim 

  16777215 constant plim 
  1077871 constant pi_plim 

\ 100000000 constant plim \ 100000000 takes 6 times 
\ 5761455 constant pi_plim \ longer time to load 

plim bitarray prime_ constant pbuf 
\ prime_ \ n -- flag   n<plim

: resetsieve \ -- 
  pbuf plim 8/mod swap 0= 0= - + pbuf 
  do true i ! cell +loop ;

: sieve \ -- 
  resetsieve
  0 pbuf clrbit
  1 pbuf clrbit
  plim sqrtf 1+ 2
  do i pbuf bit@
     if plim 1+ i dup *
        do i pbuf clrbit j +loop
     then
  loop ; sieve

plim prevprime constant pmax_

: nextprime_ \ numb -- prime   numb<pmax_
  dup 3 u< if drop 2 exit then
  1 or
  begin dup prime_ 0=
  while 2 +
  repeat ;

: prevprime_ \ numb -- prime 
  dup 3 u< if drop 2 exit then
  1- 1 or
  begin dup prime_ 0=
  while 2 -
  repeat ;

: isprime \ n -- flag 
  dup plim u>
  if isprime
  else prime_ negate
  then ;

: nextprime \ numb -- prime 
  dup pmax_ u<
  if nextprime_
  else nextprime
  then ;

: prevprime \ numb -- prime 
  dup plim u<
  if prevprime_
  else prevprime
  then ;

plim 65536/mod swap 0= 0= - constant breaknumbers
pi_plim 2* allocate throw constant pnrbuf
breaknumbers cells allocate throw constant breaks

: init_pnr \ -- 
  0 pad ! 0 breaks !
  1 pi_plim 1+ 1
  do nextprime_ dup \ p p
     65536/mod pad @ = 0= \ p r flag
     if 1 pad +! \ p r
        i 1- pad @ cells breaks + ! \ p r
     then pnrbuf i 1- 2* + 2 mb! 1+ \ p+1
  loop drop ; init_pnr
\ it takes less than a second to store all primes less than 2^24

: newintbreaks \ i j x -- i' j' 
  >r 2dup + 2/ dup
  cells breaks + @ r> u> \ i j k flag
  if -rot nip else nip then ;

: pnr@ \ n -- p    n < pi_plim
  1- dup >r 2* pnrbuf + 2 mb@
  breaknumbers 0
  begin r@ newintbreaks 2dup - 2 u<
  until rdrop nip 16 lshift + ;
\ nth prime

: newintpnr \ i j x -- i' j' 
  >r 2dup + 2/ dup pnr@ r> u> \ i j k flag
  if -rot nip else nip then ;

wordexist pi [if] : fpi pi ; [then]

: pi \ x -- n 
  >r pi_plim 1+ 0  \ x < plim
  begin r@ newintpnr 2dup - 2 u< \ i j flag
  until rdrop nip ;
\ number of primes less than or equal than x
