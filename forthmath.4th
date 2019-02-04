\ ForthMath

\ Basic number theoretic package, extension to ANS Forth
\
\ SP-Forth require
\ S" lib/ext/caseins.f" INCLUDED
\ S" ~af/lib/locals-ans.f" INCLUDED
\ S" lib/include/double.f" INCLUDED
\ S" lib/include/float2.f" INCLUDED
\ CASE-INS ON
\
\ s" numbertheory.4th" included
\ Unsigned integer number theory basicsinglext.4th 
\
\ isprime \ u -- flag
\ nextprime \ u -- p   p smallest prime > u
\ primefactors \ u -- q1 q2 ... qn n
\ radical \ n -- r
\ totients \ n -- t
\ mobius \ n -- m
\ bigomega \ n -- b 
\ smallomega \ n -- s
\ legendre \ a p -- i
\ jacobi \ a n -- i
\ kronecker \ a n -- i
\ tau \ u -- n        The number of divisors of u
\ sigma \ u -- s      The sum of all divisors of u
\ sigma** \ u k -- s  The sum of the kth power of all divisors of u
\ factorial \ n -- n!
\ ** \ b n -- b^n
\ choose \ n k -- nCk
\ sqrtf \ u -- floor
\ log~ \ n -- 1+log n
\ umin \ u1 u2 -- u
\ umax \ u1 u2 -- u
\ umod \ u q -- u(mod q)
\ ugcd \ u1 u2 -- u
\ u*mod \ u1 u2 u3 -- u1*u2(mod u3)
\ u**mod \ b a m -- b^a(mod m)

0 warnings !

bl word [defined] find nip 0= [if]
: [defined] bl word find nip 0<> ;
[then]

cell 8 * constant bits

: 2/mod \ n -- r q
  dup 1 and swap 1 rshift ;

: choose \ n k -- nCk
  1 swap 0
  ?do over i - i 1+ */
  loop nip ;

: sqrtf \ u -- floor
  0 d>f fsqrt f>d drop ;

: log~ \ n -- 1+log n    2-logarithm
  bits locals| lg |
  bits 0 
  do 1 rshift ?dup 0=
     if i 1+ to lg 
        leave 
     then 
  loop lg ;

[defined] umin 0= [if] 
: umin \ u1 u2 -- u
  2dup u< if drop else nip then ;
[then]
[defined] umax 0= [if]
: umax \ u1 u2 -- u
  2dup u< if nip else drop then ;
[then]
[defined] umod 0= [if]
: umod \ u q -- u(mod q)
  0 swap um/mod drop ; 
[then]

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
  dup 5 u< if 2 4 within exit then
  dup 1 and 0= if 0= exit then
  dup rmx 0
  do dup i pnr + c@ rabin-miller2 0=
     if 0= leave then
  loop 0= 0= ;
[then]

: nextprime \ u -- p
  dup 2 < if drop 2 exit 
  then 1+ 1 or
  begin dup isprime 0=
  while 2 +
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
  dup 1 = if 0= exit then
  pollard# sort ;

[defined] sp!
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
  dup 1 = if exit then 
  1 locals| tot | 0 swap
  primefactors 0
  do 2dup =
     if tot * to tot
     else 1- tot * to tot
     then
  loop drop tot ;
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

: tau \ u -- n
  1 0 locals| m n | 0 swap
  primefactors 0
  ?do 2dup =
     if m 1+ to m drop
     else drop m 2 + n * to n 0 to m
     then
  loop drop n ;
\ The number of divisors of u

: sigma \ u -- s
  1 1 locals| p s | 0 swap
  primefactors 0
  ?do 2dup =
     if p * to p
     else dup dup * p * 1- swap 1- / 
        s * to s
        1 to p
     then
  loop drop s ;
\ The sum of all divisors of u 

: ** \ b e -- b^e 
  dup 0= if 2drop 1 exit then
  1 swap 0 do over * loop nip ;

: factorial \ n -- n!
  1+ 1 swap 1
  ?do i * loop ;

: sigma** \ u k -- s
  1 1 locals| p s k | 0 swap
  primefactors 0
  ?do 2dup =
     if p * to p
     else dup dup * p * k ** 1- swap k ** 1- / 
        s * to s
        1 to p
     then
  loop drop s ;
\ The sum of all kth powers of divisors of u 

: -1** \ n -- i 
  1 and if -1 else 1 then ;
  
: unit* \ i j -- k 
  xor 1+ ;
  
: oddpart \ a -- i odd    a=odd*2^i
  0 swap
  begin 2/mod swap 0=
  while 1 rot + swap
  repeat 2* 1+ ;

: legendre \ a p -- i    p odd prime
  tuck dup 1- 2/ swap u**mod dup 1 >
  if swap - else nip then ;
\ (a/p)=1 if exist n with n^2=a(mod p) and a<>0
\ (a/p)=-1 if not exist n with n^2=a(mod p)
\ (a/p)=0 if a=0(mod p)

: jacobi \ a n -- j 
  1 locals| unit n a |
  a n ugcd 1 = 0= if 0 exit then 
  begin n 1 = a 1 = or if unit exit then
     a n mod ?dup 0= if 0 exit then
     oddpart to a 1 and
     if n dup * 1- 3 rshift -1** unit unit* to unit 
     then a n ugcd 1 = 0= if 0 exit then
     n a to n to a
     a 1- n 1- * 2 rshift -1** unit unit* to unit
  again ; 

: kronecker \ a n -- j 
  0 locals| unit n a |
  n 0= if a abs 1 = if 1 else 0 then exit then
  n dup abs to n 0<
  if a 0< if -1 else 1 then
  else 1
  then to unit
  a dup abs to a \ old_a
  n oddpart to n dup \ old_a i i
  if a 1 and 0= \ old_a i f
     if 2drop 0 exit 
     else 1 and \ old_a f
        if a 7 and 1+ 4 and \ old_a
           if unit negate to unit then \ old_a
        then
     then
  else drop
  then a n jacobi ?dup 0=
  if drop 0 exit then
  unit unit* to unit \ old_a
  0< if n 1- 2/ -1** else 1 then 
  unit unit* ;

\ Prime squeezing and counting
false [if]
It's possible to store consecutive prime series in tables using only two bytes
per prime number up to virtually any size (at least 100 decimals or so), with 
a technique using that the prime gaps for those numbers are less than 65536=2^16.
What's stored in the main table are the prime numbers modulo 65536, and in a 
minor table "break points" are stored: the number n when the next prime Pn+1 
divided with 65536 is greater than the same for the previous prime. 
A fast search in the minor table gives the index number, that multiplied with 65536 
should be added to the number in the main table to get the prime.

See also http://forthmath.blogspot.in/2015/12/prime-tables-and-prime-counting-function.html
[then]

: 8/mod \ n -- r q
  dup 7 and swap 3 rshift ;

: prevprime \ numb -- prime 
  dup 4 u< if drop 2 exit then
  2 - 1 or
  begin dup isprime 0=
  while 2 -
  repeat ;

[defined] under+ 0=
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
\ three different buffer sizes can be selected

\ 0xfffff constant plim 
\ 82025 constant pi_plim 

\ 16777215 constant plim 
\ 1077871 constant pi_plim 

  100000000 constant plim  \ 100000000 takes 6 times 
  5761455 constant pi_plim \ longer time to load 

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
  dup 2 u< if drop 2 exit then
  1+ 1 or
  begin dup prime_ 0=
  while 2 +
  repeat ;

: prevprime_ \ numb -- prime 
  dup 4 u< if drop 2 exit then
  2 - 1 or
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
     then pnrbuf i 1- 2* + 2 mb!    \ p+1
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
  until r> drop nip 16 lshift + ;
\ nth prime

: newintpnr \ i j x -- i' j' 
  >r 2dup + 2/ dup pnr@ r> u> \ i j k flag
  if -rot nip else nip then ;

[defined] pi [if] : fpi pi ; [then]

: pi \ x -- n 
  >r pi_plim 1+ 0  \ x < plim
  begin r@ newintpnr 2dup - 2 u< \ i j flag
  until r> drop nip ;
\ number of primes less than or equal than x 

\ unsigned natural numbers of dynamical length in 32+ bit ANS Forth
\ https://github.com/Lehs/ANS-Forth-libraries
\ https://forthmath.blogspot.se

true value karatsuba \ multiplication 

base @ hex

\ miscellanous

[defined] 0!    0= [if] : 0! 0 swap ! ; [then]
[defined] 1+!   0= [if] : 1+! 1 swap +! ; [then]
[defined] u2/   0= [if] : u2/ 1 rshift ; [then]
[defined] u/    0= [if] : u/ 0 swap um/mod nip ; [then]
[defined] umod  0= [if] : umod 0 swap um/mod drop ; [then]
[defined] cell- 0= [if] : cell- cell - ; [then]
[defined] rdrop 0= [if] : rdrop r> drop ; [then]
[defined] .r    0= [if] : .r >r 0 <# #S #> r> over - spaces type ; [then]
[defined] s>f   0= [if] : s>f s>d d>f ; [then]
[defined] f>s   0= [if] : f>s f>d d>s ; [then]

: d256*  \ ud -- 256ud
  over 8 lshift rot 0FF000000 and 018 rshift
  rot 8 lshift or ;

: sqrtc \ m -- n  ceiling
  1- sqrtf 1+ ;

0400 constant 1k
0800 constant 2k
cell negate constant -cell

     bits 1- constant bits-1
 bits-1 log~ constant lbits
cell log~ 1- constant lcell

: 4/mod \ n -- r q
  dup 3 and swap 2 rshift ;

: 8/mod \ n -- r q
  dup 7 and swap 3 rshift ;

: bits/mod \ n -- r q
  dup bits-1 and swap lbits rshift ;
\ /mod with number of bits/cell as nominator

: 256/mod \ n -- r q
  dup 0FF and swap 8 rshift ;

\ extra stack for singel numbers
\ create xs here 2k allot dup !
08000 allocate throw aligned dup constant xs dup !

: >xs  xs cell over +! @ ! ;
: xs>  xs dup @ @ -cell rot +! ;
: xs@  xs @ @ ;
: xs!  xs @ ! ;
: xs+!  xs @ +! ; 
: xspick  xs @ swap cells - @ ;
: xsdepth  xs dup @ swap - lcell rshift ;
: xsdrop  -cell xs +! ;

: .xs \ --
  xs dup @ cell+ swap cell+
  ?do i @ . cell
  +loop ;


\ pseudo random numbers

  variable rnd

: reset_seed 0ABCDEF1 rnd ! ; reset_seed

: rand \ -- u
  rnd @ 08088405 * 1+ dup rnd ! ;

: random \ u1 -- u2
  rand um* nip ;


\ big integers based on cell "digits"

\ main stack
\ pointer stack in high mem towards low mem
\ array stack in low mem towards high mem
\ little endian

080000 constant maxv
maxv cell + allocate throw aligned constant v$0
\ align create v$0 maxv cell+ allot 
v$0 maxv + constant b0
variable bvp

\ extra stack
080000 constant maxx
maxx cell + allocate throw aligned constant x$0
\ align create x$0 maxx cell+ allot 
x$0 maxx + constant x0
variable xp

\ extra pad
02000 dup allocate throw aligned constant pad1
\ align create pad1 02000 dup allot
pad1 + cell - constant pad2

: rez \ a n -- a' n'  delete leading zero ascii 48
  dup 1 =
  if exit
  then over c@ 030 =
  if 1 /string recurse
  then ;

: asc>  0F and ;    \ ascii number to binary number
: >asc  030 or ;    \ reverse
: vst!  b0 cell - bvp ! v$0 bvp @ ! ;

vst!   \ initialize stack for dynamical numbers

: nextfree \ -- a 
  bvp @ @ ;
\ address to new number array
  
: first \ -- a 
  bvp @ cell + @ ;  \ big on tos
  
: second \ -- a
  bvp @ 2 cells + @ ;  \ big on second
  
: third \ -- a 
  bvp @ 3 cells + @ ;  \ big on third

: vp+ \ -- 
  -cell bvp +! ;    \ stack pointer

: tov \ ad --    address of number array to stack
  vp+ bvp @ ! ;

: bempty \ -- flag 
  nextfree v$0 = ;
\ big stack empty
  
: len1 \ -- n 
  nextfree first - ;  \ get length to first
  
: len2 \ -- n 
  first second - ;
  
: len3 \ -- n 
  second third - ;
  
: top$ \ -- a n 
  first len1 ;
  
: sec$ \ -- a n 
  second len2 ;
  
: thi$ \ -- a n 
  third len3 ;

: s>b \ u -- big
  nextfree tuck ! cell+ tov ;
\ convert unsigned single to big

: d>b \ ud -- big
  swap nextfree dup >r 2!
  r> cell+ cell+ tov ;
\ convert unsigned double to big

: bsconstant \ n --   single as a big constant
  create , does> @ s>b ;

: bdconstant \ ud --
  create , , does> 2@ d>b ;

: vpush \ a n --  put ascii-string on stack
  rez >xs nextfree xs@ over + tov xs> cmove ;

: bpush \ a n --  put number array on stack
  nextfree over aligned     \ a n nxt na
  2dup + cell - 0!          \ a n nxt na
  over + tov                \ a n nxt
  swap cmove ;

: bpusha \ a n --  put aligned number array on stack
  nextfree 2>r 2r@ swap move
  2r> + tov ;

: bdupall \ v -- v u        allocate array of same size as btos
  nextfree len1 + tov ;

: bdrop  cell bvp +! ; \ 0 move
: bdup  top$ bpusha ; \ 1 move
: vdup  top$ vpush ; 
: bover  sec$ bpusha ; \ 1 move
: boover  thi$ bpusha ; \ 1 move

: bdrops \ bi ... b0 n -- bi .. bn
  cells bvp +! ;

: bvariable \ n --   the number of bytes to be allocated
  create allocate throw cell , , does> ;

: bdup! \ big ad -- big 
  dup cell+ @ first nextfree over - rot swap >r r@ cmove
  r> swap ! ;

: b! \ big ad --
  bdup! bdrop ;

: b@ \ ad -- big
  2@ bpusha ;

: xstack!  x0 cell - xp ! x$0 xp @ ! ; xstack!  \ xtra stack

: xp+ \ -- 
  -cell xp +! ;

: tox \ a -- 
  xp+ xp @ ! ;
 
: xnext \ -- ad 
  xp @ @ ;

: xfirst \ -- ad
  xp @ cell+ @ ;
  
: xsecond \ -- ad 
  xp @ 2 cells + @ ;
  
: xthird \ -- ad 
  xp @ 3 cells + @ ;
  
: xlen \ -- n 
  xnext xfirst - ;
  
: xpush \ a n -- 
  rez >xs xnext xs@ over + tox xs> cmove ;

: bxpush \ a n -- 
  >xs xnext xs@ over + tox xs> cmove ;
  
: xdrop  cell xp +! ;
: xdrops cells xp +! ;

: xempty \ -- f 
  xnext x$0 = ;

: >bx \ v -- 
  top$ bxpush bdrop ;
  
: bdup>x \ v -- v 
  top$ bxpush ;
  
: bx  \ -- v 
  xfirst xnext over - bpusha ;
  
: bx> \ -- v 
  bx xdrop ;

: by  \ -- v  y is the second value on x-stack
  xsecond xfirst over - bpusha ;

: bz  \ -- v 
  xthird xsecond over - bpusha ;
  
: v>x \ v -- 
  top$ bdrop xpush ;
  
: vx  \ -- v 
  xfirst xnext over - vpush ;
  
: vx> \ -- v 
  vx xdrop ;

: vy  \ -- v
  xsecond xfirst over - vpush ;

: bnip  top$ 2 bdrops bpusha ; \ 1 move
: bswap  bover top$ sec$ 3 bdrops bpusha bpusha ; \ 3 move
: vswap  v>x v>x vy vx> xdrop ; 
: brot  boover top$ sec$ thi$ 4 bdrops bpusha bpusha bpusha ; \ 4 move
: btuck  bswap bover ; \ 4 move 
: b2dup  bover bover ; \ 2 move
: b2drop  2 bdrops ; \ 0 move
: b3dup  boover boover boover ; \ 3 move
: bunderdup  >bx bdup bx> ; \ 3 move
: b-rot  boover boover top$ sec$ thi$ 5 bdrops bpusha bpusha bpusha ; \ 5 move

: reztop  top$ xpush bdrop bx> ;      \ clean leading asczeros
: vzero  [char] 0 nextfree tuck c! 1+ tov ;
: bzero 0 s>b ;                    \ small bigintegers
: bone  1 s>b ;
: btwo  2 s>b ;
: bthree 3 s>b ;
: bten  0A s>b ;

: byte1@ \ v -- v | -- b  get least significant byte of tos
  first c@ ;

: byte2@ \ v -- v | -- b  least sign byte on second number
  second c@ ;

: <vtop  \ delete unwanted leading asc zeros
  begin len1 2 <=
     if exit then nextfree 1- c@ 0=
  while -1 bvp @ +!
  repeat ;

: <top  \ delete unwanted leading zeros
  begin len1 cell > 0=
     if nextfree 0! exit
     then nextfree cell - @ 0=
  while -cell bvp @ +!
  repeat nextfree 0! cell len1 3 and - 3 and bvp @ +! ;

: bs/mod \ v n -- q r    v=nq+r
  locals| x |
  bdupall nextfree cell - 0!
  0 0 len1 cell -
  do i second + @ swap x um/mod i first + ! -cell
  +loop <top bnip ;

: vr< \ u v -- u v f    compare numbers as asc strings
  reztop <vtop vswap reztop <vtop vswap
  len2 len1 2dup <
  if 2drop true exit
  then dup locals| k | >
  if false exit
  then first nextfree 1-
  do i k - c@ i c@ 2dup = 0=
     if < if true else false then unloop exit
     then 2drop -1
  +loop false ;

: vr= \ u v -- u v | -- f
  vr< if false exit then
  vswap vr< if vswap false exit then vswap true ;

: v2/  \ v -- v/2
\ divide asc number by 2
  nextfree first 0 locals| y x |
  begin x c@ over x >
  while asc> 2/mod y + >asc x c!
     negate 5 and to y x 1+ to x
  repeat reztop <vtop 2drop ;

: v>byte \ u -- v f r
\ divide asc-string by 256 leaving rest r. f true if v=0
  xsdepth false locals| y |
  8 0
  do nextfree 1- c@ 1 and >xs v2/ vzero vr= bdrop
     if true to y leave then
  loop xsdepth swap - 0 tuck
  do 2* xs> + loop y swap ;

: nth \ n -- ad/0 
  1+ bvp @ swap cells +
  dup b0 = if drop 0 else @ then ;

: len# \ n -- m
  dup nth swap 1- nth ?dup
  if swap else v$0 swap then - ;

: bpick \ bn ... b0 -- bn ... b0 bm | m --
  dup nth swap len# bpusha ; \ 1 MOVE

\ a b c d -- a b c d a b
: b2over  3 bpick 3 bpick ; \ 2 move
: b2swap  b2over top$ sec$ thi$ 3 nth 3 len# 6 bdrops bpusha bpusha bpusha bpusha ; \ 6 move

\ : b2rot \ a b c d e f -- c d e f a b

: xnth \ n -- b/0 
  1+ xp @ swap cells +
  dup x0 = if drop 0 else @ then ;

: xlen# \ n -- m
  dup xnth swap 1- xnth ?dup
  if swap else x$0 swap then - ;

: bxpick \ xn ... x0 -- xn ... x0 xm | m --
  dup xnth swap xlen# bpusha ;

: #>bx \ bn ... b0 -- bn ... bm  x: -- bm-1 ... b0 | m --
  0 do >bx loop ;

: #bx> \ -- bm-1 ... b0  x: bm-1 ... b0 -- | m --
  0 do bx> loop ;

: bdepth \ -- n
  040 0          \ depth of stack
  do i nth 0= if i leave then loop ;

: v>b  \ convert asc-number to digital bignumber
  pad 1k 2dup + pad
  do v>byte i c!
     if drop i 1+ 0! i pad - 1+ cell+ leave then
  loop bdrop bpush <top ;

\ : s>b~  0 <# #s #> vpush v>b ;

: b>s  \ big -- u  conv big to single
  first @ bdrop ;

\ : d>b~  <# #s #> vpush v>b ;

: b>d  \ big -- ud
  top$ 5 < if @ 0 else 2@ swap then bdrop ;

: v  bl parse vpush ;     \ 'v 12345' put asc numb on tos
: b  v v>b ;              \ put bigint on tos
: cl vst! xstack! ;       \ clear stacks

: .v  cr bdepth ?dup    \ print asc numb stack
  if 0 do i nth i len# type cr loop then ;

: .bytes cr bdepth ?dup    \ print byte string stack
  if 0 do i nth i len# 0
          do i over + c@ base @ >xs
             hex 0 <# # # #> type space xs> base !
          loop drop cr
       loop
  then ;

: b+_s>=f \ u v -- u+v    u >= v
  len2 nextfree over len1 - dup bvp @ +! erase
  0 locals| x |
  nextfree first
  do i over - @ i @ 0 tuck d+ x 0 d+ to x i ! cell
  +loop drop x ?dup if nextfree cell bvp @ +! ! then ;

: bover+ \ u v -- u u+v    adding bigint
  len2 len1 < 0=
  if b+_s>=f
  else bswap b+_s>=f
  then ;

: b+ \ u v -- u+v
  bover+ bnip ;

: b2dup< \ u v -- u v f  
  len2 len1 2dup u<
  if 2drop true exit
  then dup pad1 ! u>
  if false exit
  then second first locals| x y | 
  0 pad1 @ cell -
  do y i + @ x i + @ 2dup = 0=
     if u< if true else false then unloop exit
     then 2drop -cell
  +loop false ;

: b< \ u v -- | --f    bigstack less
  b2dup< 2 bdrops ;

: b2dup= \ u v -- u v | -- f
  b2dup< if false exit then
  bswap b2dup< if bswap false exit then bswap true ;

: b= \ u v -- | --f
  b2dup= 2 bdrops ;

: b2dup> \ u v -- u v | -- f
  b2dup= b2dup< or 0= ;

: b> \ u v -- | --f
  b2dup> 2 bdrops ;

: bdup0= \ v -- v | -- f
  len1 cell - first @ or 0= ;

: b0= \ v -- | -- f
  bdup0= bdrop ;

: b>v$ \ b -- b | -- a n
  pad2 pad1 ! bdup 0A
  begin dup bs/mod >asc pad1 @ c! -1 pad1 +! bdup0= until
  drop bdrop 1 pad1 +! pad1 @ pad2 over - 1+ ;

: b>v  \ b -- b v
  b>v$ vpush ;

: bdec# \ b -- b | -- n 
  b>v$ nip ;

: bdup. \ b -- b
  b>v$ type space ;

: b. \ b --
  bdup. bdrop ;

: .b  bempty 0=
  if cr bdup. >bx recurse bx> then ;

: .x  xempty 0=
  if bx> cr bdup. recurse >bx then ;

: gtx? \ v -- v | -- f    greater than value in bx?
  len1 xlen 2dup <
  if 2drop false exit then >
  if true exit then false 0 xlen cell -
  do first i + @ xfirst i + @ 2dup <
     if 2drop leave then >
     if 0= leave then -cell
  +loop ;

: +x>=y? \ v -- | -- f    add v to bx and compare with y
  bx> b+ bx> b2dup< >bx >bx 0=
  dup if xdrop xdrop then ;  \ 2 xdrop when equal or greater

variable borrow
: b~ \ u v -- |u-v| flag
  b2dup< if bswap true else false then 
  first len1 + len2 len1 - dup bvp @ +! erase
  false borrow ! 
  second first locals| x y |
  len1 0
  do i y + @ 0
     borrow @ 0 d-
     i x + @ 0 d-
     abs borrow ! i y + ! cell
  +loop bdrop <top ;

: br~ \ u v -- |u-v| v flag
  b2dup< if bswap true else false then 
  first len1 + len2 len1 - dup bvp @ +! erase
  false borrow ! 
  second first locals| x y | 
  len1 0
  do i y + @ 0
     borrow @ 0 d-
     i x + @ 0 d-
     abs borrow ! i y + ! cell
  +loop <top ;

: b- \ u v -- u-v
  b~ if cr ." negative big!" cr 10 throw then ;

: br- \ u v -- u-v v
  br~ if cr ." negative big!" cr 10 throw then ;

: |b-| \ u v -- |u-v|
  b~ drop ;

: |br-| \ u v -- |u-v| v
  br~ drop ;

: bcells* \ big m -- big*C^m
  cells top$ locals| n ad mb |
  ad ad mb + n move
  ad mb erase
  mb bvp @ +! ;

: bcells/ \ big m -- big/C^m
  cells top$ locals| n ad mb |
  ad mb + ad n move
  mb negate bvp @ +! ;

: bsl \ n i -- n1 n0        big shift left, n < cell, i<bits
  dup 
  if 2dup bits swap - rshift
     -rot lshift 
  else swap
  then ;

: bsr \ n i -- n1 n0
  2dup rshift -rot
  bits swap - lshift ;

: brshift \ big n -- big'
  bits/mod locals| a b |
  a bcells/ 0 to a
  first nextfree cell -
  do i @ b bsr swap
     a or i ! to a -cell
  +loop <top ;

: blshift \ big n -- big'
  bits/mod swap 0 locals| a b |
  nextfree first
  do i @ b bsl a or i ! to a cell
  +loop a nextfree ! cell bvp @ +!
  bcells* <top ;

: bor \ b1 b2 -- b1Vb2    len2>=len1
  len2 len1 - nextfree over bvp @ +! swap erase
  len2 0
  do i second + @ i first + dup >r @ or r> ! 
  loop bnip ;

: bdup1and \ v -- v i
  first @ 1 and s>b ;

: bdupeven \ v -- v flag
  first @ 1 and 0= ;

: bdupodd \ v -- v flag
  bdupeven 0= ;

: b1or \ v -- v'
  first @ 1 or first ! ;

: b2/mod \ v -- r k
  bdup1and bswap 1 brshift ;

: msb@ \ v -- v | -- c    most significant byte in value on tos
  nextfree cell- nextfree 1-
  do i c@ ?dup if leave then -1 +loop ;

: msb@2 \ u v -- u v | -- c  most sign byte second for on stack
  first cell- first 1-
  do i c@ ?dup if leave then -1 +loop ;

: z# \ v -- v n      nr of zero bytes in most sign cell tos
  0 locals| x |
  nextfree
  begin 1- dup c@ 0=
  while x 1+ to x
  repeat drop x ;

: z#2 \ u v -- u v n
  0 locals| x |
  first
  begin 1- dup c@ 0=
  while x 1+ to x
  repeat drop x ;

: blog~ \ v -- v | -- n       8(len-1)+log(byte0)+1
  len1 z# - 1- 3 lshift msb@ log~ + ; 
\ n is the number of binary digits

: blog~2 \ u v -- u v | -- n
  len2 z#2 - 1- 3 lshift msb@2 log~ + ;

: bslog \ v -- n   integer part of 2-logarithm
  blog~ 1- bdrop ;

: b1+ bone b+ ;
: b1- bone b- ;
: b2+ btwo b+ ;
: b2- btwo b- ;

: b2* \ v -- 2v
  1 blshift ;

: b2/ \ v -- v/2
  1 brshift ;

: b256* \ v -- 256v
  top$ over 1+ swap cmove>
  bvp @ 1+! 0 first c! ;

: last!> \ n --
  nextfree cell - ! cell bvp @ +! ;

: cell*x \ n -- n*v ; x: v -- v 
  0 locals| k |
  bzero
  xnext xfirst
  do dup i @ um* k 0 d+ to k last!> cell 
  +loop k nextfree cell - ! drop <top ;

: bs@* \ single ad n -- big
  0 locals| k | 
  bzero over + swap
  do dup i @ um* k 0 d+ to k last!> cell 
  +loop k nextfree cell - ! drop <top ;

: bs* \ v n -- n*v 
  >bx cell*x xdrop ;

: bdups* \ v n -- v n*v 
  0 locals| k |
  bzero first second
  do dup i @ um* k 0 d+ to k last!> cell +loop
  k nextfree cell - ! drop <top ;

: bitsblshift~ \ v -- w 
  top$ over cell+ swap move
  cell bvp @ +! 0 first ! ;
\ big shift left with number of bits (32 or 64)

: bitsblshift \ v -- w 
  1 bcells* ;

: b* \ u v -- u*v
  len1 len2 < if bswap then
  >bx bzero second first cell -
  do bitsblshift i @ cell*x b+ -cell +loop
  bnip xdrop <top ;

: b@* \ ad1 n1 ad2 n2 -- big
  bzero dup 3 pick < if 2swap then
  over + cell -
  do bitsblshift 2dup i @ -rot bs@* b+ -cell 
  +loop 2drop <top ;

: bcells. \ b --    32 bit cells
  base @ hex
  top$ over + swap
  do i @ 0 <# # # # # # # # # #> type space cell 
  +loop bdrop base ! ;

: .cells \ --
  bdepth 0
  ?do i bpick cr bcells. loop ;

: bmerge \ u v -- w 
  bvp @ @ cell bvp +! bvp @ ! ;

: bsplit \ w ad -- u v 
  dup nextfree < 
  if bvp @ dup @ vp+ bvp @ ! ! 
  else drop bzero
  then ;

: btransmul \ x y -- x0 x1 y0 y1 m     B=2^bits 
  len1 len2 max cell + lcell 1+ rshift     \ m
  dup >r cells 
  >bx first over + bsplit 
  bx> first + bsplit r> ; 
\ x=x0+x1*B^m  y=y0+y1*B^m 

084 value karalim

false [if]
: b@* \ ad1 n1 ad2 n2 -- big
  dup 3 pick max karalim < 
  if b@* exit then
  btransmul >r                   \ x0 x1 y0 y1
  3 bpick 2 bpick recurse >bx    \ bx: x0*y0
  2 bpick 1 bpick recurse >bx    \ bx: x0*y0 x1*y1
  b+ >bx b+ bx>   recurse        \ (x0+x1)(y0+y1)
  bx b- by b- r@ bcells*         \ z1*C^m
  bx> r> 2* bcells* bx> b+ b+ <top ;
\ Karatsuba multiplication .115171 .124531
[then]

karatsuba [if]
: b* \ x y -- xy
  len1 len2 max karalim < 
  if b* exit then
  btransmul >r                   \ x0 x1 y0 y1
  3 bpick 2 bpick recurse >bx    \ bx: x0*y0
  2 bpick 1 bpick recurse >bx    \ bx: x0*y0 x1*y1
  b+ >bx b+ bx>   recurse        \ (x0+x1)(y0+y1)
  bx b- by b- r@ bcells*         \ z1*C^m
  bx> r> 2* bcells* bx> b+ b+ <top ;
\ Karatsuba multiplication
[then]

: brandom \ n -- u     n is the maximal number of decimal digits in 
  bzero 0 do bten b* 10 random s>b b+ loop ;

: brand# \ n -- u      n is the exact number of decimal digits in u
  9 random 1+ s>b 1 
  ?do bten b* 10 random s>b b+ loop ;

\ 2^sxn+1=2*2^sxn-[2^sxn]^2*n/2^[2s]
\ q=t*x/2^[2n]
\ Newton-Ralphson on y=2^s/x-A

: boverswap/ \ u v -- u u/v
  b2dup< if bdrop bzero exit then
  len1 cell > 0=
  if b>s bdup bs/mod drop exit then
  blog~ 0 locals| y x | 
  >bx bdup blog~ 2/ 6 + 2* to y 
  y x - dup to x bone blshift x
  if 6 bs* 5 bs/mod drop then 01F 0            \ start value
  do bdup b2* bover bdup b* bx b*
     y brshift b-    \ ??
     b2dup= bnip 
     if leave then 
  loop b* y brshift
  begin b2dup bx b* b< while b1- repeat
  begin b2dup bx b* bx b+ b< 0= while b1+ repeat 
  xdrop ; 

: b/ \ u v -- u/v
  boverswap/ bnip ;

\ Barrett reduction
\ Faster modulo when repeting [mod d] with same d

variable foo
1k bvariable bar
1k bvariable den

: barmod \ w -- v      w < d**2
  bdup den b@ b2dup<   \ w w den flag
  if 2 bdrops exit     \ w
  then bdrop           \ w w
  bar b@ b*            \ w w*bar
  foo @ brshift        \ w q
  den b@ b* b-         \ w-q*den  ??
  den b@ b2dup<        \ w-q*den den flag
  if bdrop else b- then ; \ ??

: >bar \ d --      d is the denominator; precalc for barmod
  blog~ 2* dup foo !               \ foo = 2*bitlen
  bone blshift bover b/ bar b!     \ bar = 2^foo/u
  den b! ; 

: boverswap** \ a b -- a a^b
  first @ 0= if 2 bdrops bone exit then
  >bx bzero >bx bone
  begin bover b*
     bone +x>=y?
  until ;

: b** boverswap** bnip ;

: bdups** \ a n -- a a^n
  bone 0 
  ?do bover b* loop ;

: bs** \ a n -- a^n
  bdups** bnip ;

: bs^ \ b n -- b^n
  ?dup
  if dup 1 and
     if bdup >bx else bone >bx then
     2/ recurse bdup b* bx> b*
  else bdrop bone
  then ;

: bmod \ u v -- r
  b2dup b/            \ u v u/v
  b* b- ;             \ u-v*u/v

: b/mod \ w u -- r q
  b2dup b/ bdup >bx b* b- bx> ;

: bsqrtf \ w -- v                  \ Newton-Ralphson
  bdup0= if exit then
  blog~ u2/ bone blshift 10 0      \ start value
  do b2dup b/ b2dup=
     b+ b2/ if leave then
  loop bdup bdup b* brot bswap b2dup< 2 bdrops
  if b1- then ;

: bsqrtc \ w -- v
  b1- bsqrtf b1+ ;

: bdupfactorial  \ v -- v v!
  >bx bzero bone
  begin bswap b1+ gtx? bswap 0=
  while bover b*
  repeat xdrop ;

: bfactorial \ v -- v!
  bdupfactorial bnip ;

: bsfactorial \ n -- bn!
  bone 0
  ?do i 1+ bs* loop ;

: bgcd \ v u -- w  greatest common divisor
  b2dup< if bswap then
  begin btuck bmod bdup0=
  until bdrop ;

: blcm \ v u -- w  least common multiple
  b2dup b* 
  b-rot bgcd b/ ;

\ the square-and-multiply-algorithm
: b**mod \ u v m -- u^v mod m
  >bx blog~ bswap >bx bone 0        \ v 1 | x: m u | l[v] 0
  do i bits/mod cells second + @    \ v w | x: m u | r celli
     1 rot lshift and               \ v w | x: m u | celli & 2^r
     if bx b* by bmod               \ v [w*u]
     then bx bx> b* bx bmod >bx     \ v [w*u] x<-[x*x]
  loop bnip 
  xdrop xdrop ;

\ the square-and-multiply-algorithm with Barrett reduction
: bar**mod \ u v m -- u^v mod m
  bover bone b= if bnip bmod exit then
  >bar blog~ bswap >bx bone 0
  do i bits/mod cells second + @
     1 rot lshift and
     if bx b* barmod
     then bx bx> b* barmod >bx
  loop bnip xdrop ;

: sign-comp  \ t q t' -- t" | f" f f' -- fnew f'
  b* >r r@ xor 2* +
  case 0 of b~ endof
      -1 of b+ true endof
      -2 of b+ false endof
      -3 of b~ 0= endof
  endcase r> ;

variable flag
variable flag11
variable flag12
variable flag21
variable flag22

: binvmod \ u v -- u'
  false flag !
  false flag11 ! false flag12 !
  false flag21 ! false flag22 !
  btuck bzero bone b2swap bswap
  begin bdup0= 0=
  while b2dup b/ >bx flag21 @ flag22 @ xor flag !
     b2swap btuck bx flag12 @ flag @ flag11 @
     sign-comp flag12 ! flag11 !
     b2swap btuck bx> flag22 @ flag @ flag21 @
     sign-comp flag22 ! flag21 !
  repeat 3 bdrops flag12 @
  if bover |b-| then bswap bmod ;

: bschoose \ n k -- big
  bone 0
  ?do dup i - bs*
     i 1+ bs/mod drop
  loop drop ;
\ choose k of n

\ rabin-miller strong pseudoprime test

: rs \ u -- s r
  0 0 locals| x y |
  b1- nextfree first 
  do i @ if i to y leave then x 1+ to x cell
  +loop y @ bits 0
  do dup 1 and if i leave then u2/
  loop nip x lbits lshift +
  dup brshift ;

: bdupdigit= \ u n -- u f    u=n?
  len1 cell > if drop false exit then
  first @ = ;

: digit= \ u n -- f    u=n?
  bdupdigit= bdrop ;

false [if]
: digit= \ u n -- f    u=n?
  len1 cell > if drop bdrop false exit then
  first @ = bdrop ;
[then]

: pseudo1 \ xsi s m -- | -- f
  bar**mod
  1 digit= ;

: pseudo2 \ xsi s m r -- f
  false locals| flag | 
  >bx bx b1- >bx 0
  do b2dup i blshift by bar**mod
     bx b=
     if true to flag leave then
  loop xdrop xdrop 2 bdrops flag ;

: bmiller \ u -- u f    u odd >3
  >bx bx btwo bx rs locals| z |
  b2dup
  bx pseudo1 ?dup
  if xdrop 2 bdrops exit
  then bx> z pseudo2 ;
\ u is of the form u=1+s*2^r, where s is odd
\ given any number 1 < xsi < u
\ if xsi^s=1[mod u] or
\ if it exist j: 0 =< j < r with
\ xsi^[s*2^j]=-1[mod u]
\ then u is pseudoprime.

: bmillerx \ u -- u f
  4 s>b b2dup< bdrop if b>s 1 > exit then
  bdupeven if false exit then
  bmiller ;

: bdupisprime \ b -- b flag 
  len1 cell >
  if bmillerx 
  else bdup b>s isprime
  then ;

: bisprime \ big -- flag
  bdupisprime bdrop ;

: bnextprime \ b -- p
  btwo b2dup< if bnip exit 
  then bdrop b1+ b1or
  begin bdupisprime 0=
  while b2+
  repeat ; 

: blegendre \ b p -- i 
  bdup                      \ b p p 
  b1- b2/ bswap b**mod      \ b (p-1)/2 p -- x
  bdup bone b>              \ x x>1
  if bdrop -1 else b>s then ; 

base !

\ Signed big integers

: clxs xs dup ! ; 

: sb. \ sb -- 
  xs> if ." -" then b. ; 

: sb  bl parse over c@ [char] - = 
  dup >r if swap 1+ swap 1- then 
  vpush v>b r> >xs ; 

: sb+ \ sb1 sb2 -- sb3 
  xs@ xs> xs> xor 
  if b~ swap 0= if 0= then 
  else b+ 
  then >xs ; 

: sb- \ sb1 sb2 -- sb3 
  xs> 0= >xs sb+ ; 

: sb* \ sb1 sb2 -- sb3
  xs> xs> xor >xs b* ;

: sb/ \ sb1 sb2 -- sb3
  xs> xs> xor >xs b/mod bswap b0= 0= 
  if dup if b1+ then then ; 

: sbdup  bdup xs@ >xs ; 
: sbswap  bswap xs> xs> swap >xs >xs ; 
: sbdrop  bdrop xs> drop ; 
: sbover  bover xs> xs@ swap >xs >xs ; 
: sbtuck  btuck xs@ xs> xs> swap >xs >xs >xs ; 
: sbrot  brot xs> xs> xs> rot >xs swap >xs >xs ; 
: sbnip  bnip xs> xs> drop >xs ;
: sbpick  dup bpick xspick >xs ;

: .sb  bempty 0=
  if cr sbdup sb. xs> >r >bx recurse bx> r> >xs then ;
  
: sb>s \ sb -- n
  b>s xs> if negate then ;

: sbabs \ sb -- sb'
  xs> abs >xs ;

: sbnegate \ sb -- sb'
  xs> 0= >xs ;

\ utime b 17 b 250 b** b 2704 b+ bthree bswap bdup bar**mod utime d- d. b.


\ NESTED SETS WITH CARTESIAN PRODUCTS

[defined] log~ 0= [if]
: log~ \ n -- #binary digits
  0 swap begin swap 1+ swap 1 rshift ?dup 0= until ;
[then]

[defined] -cell 0= [if]
: -cell cell negate ;
[then]

\ Sorting the stack

[defined] lower 0= [if]
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
[then]

\ Stacks_____

: cs negate 2/ ;
: listflag 1 and ;

: objsize \ bc -- n
  dup 0< if cs 1+ else drop 1 then ;

: >stack ( n ad -- )  cell over +! @ ! ;
: stack> ( ad -- n )  dup @ @ -cell rot +! ;
: >stack> ( n ad -- m )  dup @ @ -rot @ ! ;
: stack@ ( ad -- n )  @ @ ;
: stack! ( n ad -- )  @ ! ;
: stack+! ( n ad -- )  @ +! ;

1 23 lshift cells allocate throw dup constant xst dup !

: >xst ( n -- )  xst >stack ;
: xst> ( -- n )  xst stack> ;
: >xst> ( n -- m )  xst >stack> ;
: xst@ ( -- n )  xst @ @ ;
: xst! ( n -- )  xst @ ! ;
: xst+! ( n -- )  xst @ +! ;

: >>xst ( xn ... x1 bc -- )  >r r@ cs 0 ?do >xst loop r> >xst ;
: xst>> ( -- x1 ... xn bc )  xst@ >r xst> cs 0 ?do xst> loop r> ;

1 23 lshift cells allocate throw dup constant yst dup !

: >yst ( n -- )  yst >stack ;
: yst> ( -- n )  yst stack> ;
: >yst> ( n -- m )  yst >stack> ;
: yst@ ( -- n )  yst @ @ ;
: yst! ( n -- )  yst @ ! ;
: yst+! ( n -- )  yst @ +! ;

: >>yst ( xn ... x1 bc -- )  >r r@ cs 0 ?do >yst loop r> >yst ;
: yst>> ( -- x1 ... xn bc )  yst@ >r yst> cs 0 ?do yst> loop r> ;

cell 1- log~ constant cellshift

: stack-depth ( ad -- n )  dup @ swap - cellshift rshift ;
: stack-cl ( ad -- )  dup ! ;
: stack-empty ( ad -- flag )  dup @ = ;

1 24 lshift cells allocate throw dup constant zst dup !

: >zst ( n -- )  zst >stack ;
: zst> ( -- n )  zst stack> ;
: >zst> ( n -- m )  zst >stack> ;
: zst@ ( -- n )  zst @ @ ;
: zst! ( n -- )  zst @ ! ;
: zst+! ( n -- )  zst @ +! ;

: >>zst ( xn ... x1 bc -- )  >r r@ cs 0 ?do >zst loop r> >zst ;
: zst>> ( -- x1 ... xn -n )  zst@ >r zst> cs 0 ?do zst> loop r> ;

: showx xst stack-depth if xst> >r recurse r> dup . >xst then ;
: showy yst stack-depth if yst> >r recurse r> dup . >yst then ;
: showz zst stack-depth if zst> >r recurse r> dup . >zst then ;

: >zet ( s -- | -- s)
  >>yst yst> dup >xst cs 0 ?do yst> >zst loop xst> >zst ;

: zet> ( -- s | s -- )
  zst> dup >yst cs 0 ?do zst> >xst loop yst> >xst xst>> ;

\ Set manipulations_____

\ bundle code bc=-(2n+1)
\ z1...zn bc

: setdrop \ ad --
  dup @ @ cs cells cell+ negate swap +! ;

: setdup \ ad --
  >r
  r@ @ @ cs cells                 \ n'
  r@ @ over -                     \ n' ad1
  r@ @ cell+                      \ n' ad1 ad2
  rot cell+ dup r> +! cmove ;

: setover \ ad --
  dup >r @ @ cs cells cell+       \ nr of bytes 1'st set
  r@ @ swap -                     \ ad to 2'nd set
  dup @ cs cells cell+ dup >r -   \ ad to 3'rd set
  cell+ r> r@ @ cell+             \ ad to move to
  swap dup r> +! cmove ;

: setcopy \ ad1 ad2 --
  locals| ad2 ad1 |
  ad1 @ @ cs cells             \ n'
  ad1 @ over - swap cell+      \ ad1-n' n
  ad2 @ cell+ over ad2 +! swap cmove ; 

: setmove \ ad1 ad2 --
  swap dup rot setcopy setdrop ;

: adn1 zst@ cs cells zst @ over - swap cell+ ;
: adn2 adn1 drop cell - dup @ cs cells tuck - swap cell+ ;
: adn3 adn2 drop cell - dup @ cs cells tuck - swap cell+ ;

: zdup  zst setdup ;
: zdrop  zst setdrop ;
: zover  adn2 tuck zst @ cell+ swap cmove zst +! ;
: zswap  zover adn2 adn3 rot + move zdrop ;
: znip  zswap zdrop ;
: ztuck  zswap zover ;
: zrot  zst>> zswap >>zst zswap ;

: setad \ n ad1 -- ad2    addr to n-th set
  @ swap 0
  ?do dup @ cs 1+ cells -
  loop ;

: setpick \ n ad -- set
  locals| ad |
  ad setad dup @        \ ad1 m'
  cs cells tuck -       \ m ad1-4m 
  swap cell+ dup >r     \ ad1-4m m+4a
  ad @ cell+ swap move 
  r> ad +! ;

: zpick \ n -- set 
  zst setpick ;

\ Output of sets_____

0 value addr1

: addr1- \ --
  addr1 1- to addr1 ;

: fillad$ \ addr n --
  dup 1- negate addr1 + dup to addr1 swap move addr1- ;

: n>addr1 \ n --
  0 <# #s #> fillad$ ;

: a>addr1 \ c --
  addr1 c! addr1- ;

: cardinality \ -- n | s --
  zst> cs dup >xst 0
  ?do zst@ 0<
     if zst@ dup cs negate xst+! >r zdrop r> cs 1+
     else zst> drop 1
     then
  +loop xst> ;

: foreach \ -- n 0 | s -- z1...zn
  zdup cardinality zst> drop 0 ;

: closep \ -- bc asc
  zst@ dup listflag if [char] ) else [char] } then ;

: openp \ bc -- asc
  listflag if [char] ( else [char] { then ;

: list$ \ ad -- ad n | s --
  dup to addr1 false locals| flag addr2 |
  closep a>addr1
  foreach
  ?do flag if [char] , a>addr1 then zst@ 0<
     if addr1 recurse 2drop
     else zst> n>addr1
     then flag 0= if true to flag then
  loop openp a>addr1
  addr1 1+ addr2 over - 1+ ;

1 20 lshift dup allocate throw swap cell - + constant printbuf

: zet. \ -- | s --
  zst@ 0=
  if zst> .
  else printbuf list$ type
  then ;

: z.  zet. ;

: set. \ yst,xst --
  zst setcopy zet. ;

\ Analyzing sets_____

: ?obj \ x -- 0,1,2
  dup 0<
  if listflag
     if 1 else 2 then
  else drop 0
  then ;
\ 0=numb, 1=vect, 2=set

: _split \ ad --   ad=yst,zst
  dup >r @ cell - @ 0< 0=
  if r@ stack> 2 + r@ stack> swap r@ >stack r> >stack exit then
  r@ stack>
  r@ xst setmove
  xst@ cs 1+ 2* + r@ >stack
  xst r> setmove ;

: ysplit \ -- | s -- s' x  in yst stack
  yst _split ;

: zsplit \ -- | s -- s' x
  zst _split ;

\ Set equal, subset and membership_____

: zetmerge \ -- | s s' -- s"
  zst yst setmove
  yst@ zst> +
  yst zst setmove
  zst! ;

: ymerge yst xst setmove xst@ yst> + xst yst setmove yst! ;
: zmerge zetmerge ;

: vmerge \ -- | v v'-- v"
  zst yst setmove
  yst@ zst> + 1+
  yst zst setmove
  zst! ;

: _fence \ ad -- | x -- {x}
  dup >r stack@ ?obj
  case 0 of -2 r@ >stack endof
       1 of r@ stack@ 1- r@ >stack endof
       2 of r@ stack@ 2 - r@ >stack endof
  endcase rdrop ;

: xfence xst _fence ;
: yfence yst _fence ;
: zfence zst _fence ;

: zxmove# \ n -- n'
  zst@ cs 1+ + zst xst setmove ;

: set-sort2 \ -- | s -- n1...nk -2k
  0 locals| counter | 0 >xst 0 >yst
  foreach
  ?do zst@ ?obj
     case 0 of counter 1+ to counter zst> endof
          1 of zfence xst zst setmove zetmerge zst xst setmove endof
          2 of zfence yst zst setmove zetmerge zst yst setmove endof
     endcase
  loop counter sort 2* negate >zet
  xst zst setmove zetmerge
  yst zst setmove zetmerge ;

: adswap \ ad1 ad2 --
  over @ over @ swap rot ! swap ! ;

: singlepart \ ad1 ad2 -- ad
  tuck 2dup @ locals| p ad | swap                \ ad2 ad2 ad1
  do i @ p <                                     \ ad2 flag
     if ad i adswap ad cell + to ad then cell    \ ad2 cell
  +loop ad adswap ad ;                           \ ad

: qsort \ ad1 ad2 --      pointing on first and last cell in array
  begin
    2dup < 0= if 2drop exit then
    2dup - negate 1 rshift >r      \ keep radius (half of the distance)
    2dup singlepart 2dup - >r >r   \ ( R: radius distance2 ad )
    r@ cell - swap r> cell+ swap   \ ( d-subarray1 d-subarray2 )
    2r> u< if 2swap then recurse   \ take smallest subarray first
  again \ tail call optimization by hand
;

: qsort~ \ ad1 ad2 --      pointing on first and last cell
  2dup <
  if 2dup singlepart >r
     swap r@ cell - recurse
     r> cell + swap recurse
  else 2drop
  then ; \ problem with almost sorted big set

: set-sort \ -- | s -- n1...nk -2k ???
  xst @ cell+ 0 locals| counter ad1 | 0 >yst
  foreach
  ?do zst@ ?obj
     case 0 of counter 1+ to counter zst> >xst endof
          1 of zfence yst zst setmove zetmerge zst yst setmove endof
          2 of zfence yst zst setmove zetmerge zst yst setmove endof
     endcase
  loop ad1 dup counter 1- cells + qsort counter 2* negate >xst
  xst zst setmove
  yst zst setmove zetmerge ;

: next-element-ad \ ad1 -- ad2
  dup @ objsize cells - ;

: smember \ n -- flag | s --
  zst@ cs false locals| flag m | 
  foreach
  ?do zst@ 0<
     if m zst@ cs 1+ - to m zdrop
     else m 1- to m dup zst> 2dup >
        if false to flag 2drop
           m cells negate zst +! leave
        then =
        if true to flag
           m cells negate zst +! leave
        then
     then
  loop drop flag ;

: vect= \ s -- flag | s' --
\ s non empty list not including non empty sets
  dup zst@ = 0=
  if zdrop cs 0 ?do drop loop false exit
  then true locals| flag | zst> drop cs 0
  ?do flag
     if zst> = 0= if false to flag then
     else zst> 2drop
     then
  loop flag ;

: vector= \ -- flag | s s' --
  zet> vect= ;

: vmember \ -- flag | s s' --
  zswap zst yst setmove
  zst@ cs false locals| flag m |
  foreach
  ?do zst@ ?obj
    case 0 of m 1 - to m zst> drop endof
         1 of m zst@ cs 1+ - to m
              yst zst setcopy vector=
              if true to flag
                 m cells negate zst +! leave
              then endof
         2 of m zst@ cs 1+ - to m
              zst@ cs 1+ cells negate zst +! endof
    endcase
  loop yst setdrop flag ;

: secobjad \ -- ad | x y -- x y
  zst @ zst@ 0< if zst@ cs 1+ cells - else cell - then ;

: routout \ -- x | x s -- s
  secobjad dup @ swap dup cell+ swap zst@ cs 1+ cells move zst> drop ;

0 value 'subset
: subset \ -- flag | s s' --
  'subset execute ;

: zet= \ -- flag | s s' --
  zover zover subset
  if zswap subset
  else zdrop zdrop false
  then ;

: zet-member \ -- flag | s s' --
  zswap zst yst setmove
  begin zst@                         \ set not empty?
  while zsplit zst@ ?obj 2 =      \ element is a set?
     if yst zst setcopy zet=
        if yst setdrop zdrop true exit then
     else zst@ ?obj if zdrop else zst> drop then
     then
  repeat yst setdrop zdrop false ;

: member \ -- flag | x s --
  secobjad @ ?obj
  case 0 of routout smember endof
       1 of vmember endof
       2 of zet-member endof
  endcase ;

:noname \ -- flag | s s' --          \ the subset code
  zover zst @ @ zdrop 0=
  if zdrop zdrop true exit then      \ true if s is empty
  zswap zst yst setmove
  begin yst@                         \ set is not empty?
  while ysplit yst@ ?obj
     if yst zst setmove zover member
     else yst> zdup smember
     then 0= if yst setdrop zdrop false exit then
  repeat yst> drop zdrop true ; to 'subset

\ Set algebra_____

: reduce \ -- | s -- s'
  0 >yst foreach
  ?do zfence zdup zst> drop
     yst zst setcopy member
     if zdrop
     else yst zst setmove
        zetmerge zst yst setmove
     then
  loop yst zst setmove ;

: union \ -- | s s' -- s"
  zetmerge set-sort reduce ;

: intersection \ -- | s s' -- s"
  0 >xst zst yst setmove
  begin zst@
  while zsplit zfence zdup zst> drop
     yst zst setcopy member
     if xst zst setmove zetmerge zst xst setmove
     else zdrop
     then
  repeat zdrop yst setdrop
  xst zst setmove reduce ;

: diff \ s s' -- s"
  0 >xst zst yst setmove
  begin zst@
  while zsplit zfence zdup zst> drop
     yst zst setcopy member
     if zdrop
     else xst zst setmove zetmerge zst xst setmove
     then
  repeat zdrop yst setdrop
  xst zst setmove reduce ;

: multincl \ s x -- s'
  0 >xst zfence zst yst setmove
  begin zst@
  while zsplit yst zst setcopy union zfence
     xst zst setmove zetmerge zst xst setmove
  repeat zdrop yst setdrop xst zst setmove ;

: powerset \ s -- s'
  zst@ 0= if -2 >zst exit then
  zsplit zfence zst yst setmove recurse
  zdup yst zst setmove zst> drop multincl
  zetmerge ;

: cartprod \ s s' -- s"
  zst yst setmove
  zst xst setcopy xst> drop cardinality 0 0 >zst
  ?do xfence -1 xst+!
     yst setdup
     begin yst@
     while ysplit yfence -1 yst+!
        xst zst setcopy
        yst zst setmove vmerge
        zfence
        zetmerge
     repeat yst> drop xst setdrop
  loop yst setdrop ;

\ {x1,...,xn} -- {{x1},...,{xn}}
: infence \ s -- s'
  0 >xst foreach
  ?do zfence zfence
     xst zst setmove zetmerge
     zst xst setmove
  loop xst zst setmove ;

\ p(A,k)=p(A\{f(A)},k)+(p(A\{f(A)},k-1)%f(A))
: power# \ n -- | s -- s'
  ?dup 0= if zdrop 0 >zst zfence exit then
  dup 1 = if drop infence exit then
  dup zdup cardinality =
  if drop zfence exit then
  dup 1 = if drop infence exit then
  zsplit zfence zst xst setmove
  dup zdup recurse
  zswap 1- recurse xst zst setmove
  zst> drop multincl
  zetmerge ;

[defined] choose 0= [if]
\ from rosetta code
: choose \ n k -- nCk
  1 swap 0
  ?do over i - i 1+ */
  loop nip ;
[then]

\ {s1,...,sn} -- s1U...Usn
: multiunion \ -- | s -- s'
  foreach 0 >zst
  ?do zetmerge
  loop set-sort reduce ;

\ {s1,...,sn} s' -- {s1Us',...,snUs'}
: zetcup \ -- | s s' -- s"
  zst xst setmove 0 >yst foreach
  ?do xst zst setcopy union zfence
     yst zst setmove zetmerge zst yst setmove
  loop xst setdrop yst zst setmove ;

\ {s1,...,sn} s' -- {s1&s',...,sn&s'}
: zetcap \ -- | s s' -- s"
  zst xst setmove 0 >yst foreach
  ?do xst zst setcopy intersection zfence
     yst zst setmove zetmerge zst yst setmove
  loop xst setdrop yst zst setmove ;

\ {s1,...,sn} {t1,...,tm} -- {siUtj}ij
: zetunion \ -- | s s' -- s"
  0 >xst zst yst setmove foreach
  ?do yst zst setcopy
     zswap zetcup
     xst zst setmove union
     zst xst setmove
  loop yst setdrop xst zst setmove ;
\
: functions \ s s' -- s"
  secobjad @ 0= if zdrop -2 >zst exit then
  secobjad @ -2 = if cartprod infence exit then
  zswap zsplit zfence zst xst setmove
  zover recurse zswap xst zst setmove
  zswap cartprod infence zetunion ;
\ s" is the set of all functions s->s'

: xzmerge \ s -- 
  xst zst setmove
  zswap zetmerge 
  zst xst setmove ; 
  
: xzmergered \ s --
  xst zst setmove
  zswap zetmerge 
  set-sort reduce
  zst xst setmove ; 
  
\ Input of sets_____

0 create match ,
true value sort?

: { \ --
  1 match +! depth >xst true to sort? ;

: } \ x1...xk --
  depth xst> - 2* negate
  -1 match +! >zet sort?
  if set-sort2 then reduce match @
  if zet> then true to sort? ;

: q  xst stack-cl yst stack-cl zst stack-cl 0 match ! abort ;
\ used to clear stack at error

: (  { ;

: ) \ x1...xk --
  depth xst> - 2* 1+ negate
  -1 match +! >zet match @ if zet> then ;

\ cond ( n -- flag )
: all drop true ;
: odd 1 and ;
: even 1 xor ;
: 1mod4 4 mod 1 = ;
: 3mod4 4 mod 3 = ;

\ 30 70 | odd
: | \ m n -- x1...xk
  swap ' locals| xt |
  ?do i xt execute if i then loop false to sort? ;

: bl# \ ad n -- m
  over + swap 0 -rot
  do i c@ bl = -
  loop ;

variable loc#
variable sta#

: locals# \ -- 
  >in @ >r
  [char] | parse bl# loc# !
  r> >in ! 
  1 sta# !
; immediate

: :| \ -- 
  :noname
  postpone locals#
  postpone locals| ; 

: 2; 2 sta# ! postpone ; 
; immediate

: cleanvector \ s1 -- s2
  zst@ locals| n | 
  zst> cs 0
  do zst> dup 0<
     if drop n 2 + to n then
  loop n cs 0
  do >zst loop n >zst ;

: cleanset \ s1 -- s2
  0 foreach
  do cleanvector zxmove# 
  loop 2* negate >xst
  xst zst setmove ;

: intcond \ low hi xt -- | -- s   "intervall condition" 
  locals| xt |
  0 -rot swap
  ?do i xt execute
     if i >zst 1+ then
  loop 2* negate >zst ;

: setcond \ xt -- | s -- s'       "set condition"
  locals| xt | 0
  foreach
  ?do zst> dup xt execute
     if >xst 1+ else drop then
  loop dup 0
  ?do xst> >zst
  loop 2* negate >zst ;
  
: intimage \ low hi xt -- | -- s  "intervall image"
  locals| xt |
  swap 2dup
  ?do i xt execute >zst
  loop - 2* negate >zst
  set-sort reduce ;

: setimage \ xt -- | s -- s'      "set image"
  locals| xt | 0
  foreach
  ?do zst> xt execute >xst 1+
  loop dup 0
  ?do xst> >zst
  loop 2* negate >zst
  set-sort reduce ;

: ^2 dup * ;
: ^3 dup dup * * ;

: paircond \ xt -- | s -- s'
  locals| xt | 0
  foreach
  ?do zdup zet> drop xt execute
     if zst xst setmove 1+ else zdrop then
  loop 6 * negate >xst
  xst zst setmove ;

: pairimage \ s xt -- s' 
  locals| xt | 0 
  foreach 
  ?do 1+ zet> drop 
  xt execute >xst 
  loop dup 0 
  ?do xst> >zst 
  loop 2* negate >zst 
  set-sort reduce ;

: non all ;

: reverse-cartesian-set \ s -- s'
  zst@ 0= if exit then
  0 foreach
  do zxmove# loop 
  2* negate >xst
  xst zst setmove ;

: 2dcond \ lo hi xt -- set
  locals| xt | 0 >zst swap 2dup
  do 2dup 
     do i j xt execute
        if { ( i j ) } zmerge 
        then
     loop 
  loop 2drop ;

: 3dcond \ lo hi xt -- set
  0 locals| k xt hi lo | 
  0 >zst hi lo
  do i to k hi lo
     do hi lo
        do i j k xt execute
           if { ( i j k ) } zmerge 
           then
        loop 
     loop
  loop ;
  
: 4dcond \ lo hi xt -- set
  0 0 locals| m k xt hi lo | 
  0 >zst hi lo
  do i to m hi lo
     do i to k hi lo
        do hi lo
           do i j k m xt execute
              if { ( i j k m ) } zmerge 
              then
           loop 
        loop
     loop
  loop ;

: 5dcond \ lo hi xt -- set
  0 0 0 locals| n m k xt hi lo | 
  0 >zst hi lo
  do i to n hi lo
     do i to m hi lo
        do i to k hi lo
           do hi lo
              do i j k m n xt execute
                 if { ( i j k m n ) } zmerge 
                 then
              loop 
           loop
        loop
     loop 
  loop ;

: revseq \ vect -- vect'
  zet> >>zst ;

: reverse \ set1 -- set2    reverse order of pairs in sets
  zst@ 0= if exit then
  0 >xst
  foreach
  do revseq zfence 
     xst zst setmove 
     zmerge
     zst xst setmove
  loop xst zst setmove ;

: create-set \ m n xt -- set
  locals| xt n m |
  loc# @ 
  case 1 of m n xt intcond endof
       2 of m n xt 2dcond endof
       3 of m n xt 3dcond endof
       4 of m n xt 4dcond endof
       5 of m n xt 5dcond endof
  endcase ;

: cset  create-set ;

: 2setcond \ set1 xt -- set2
  locals| xt |
  0 >yst foreach
  do zdup zet> drop 
     xt execute
     if zfence
        zst yst setmove ymerge 
     else zdrop 
     then
  loop yst zst setmove 
  reverse-cartesian-set ;

: filter-set \ set1 xt -- set2
  locals| xt |
  loc# @ 
  case 1 of xt setcond endof
     dup of xt 2setcond endof
  endcase ;

: fset  filter-set ;

: 1setim2 \ set1 xt -- set2
  locals| xt | 0 >xst
  begin zst@
  while zsplit zst> xt execute
     swap >zst >zst -5 >zst 
     zfence xzmerge
  repeat zst> drop
  xst zst setmove 
  reverse-cartesian-set ;

: 1setim \ set1 xt -- set2
  sta# @
  case 1 of setimage endof
       2 of 1setim2 endof
  endcase ;

: transform-set \ set1 xt -- set2
  loc# @ 1 = 
  if 1setim 
  else pairimage
  then ;

: tset  transform-set ;

: 1func \ m n xt -- set
  locals| xt | swap 0 -rot
  do i xt execute >zst 1+ 
  loop 2* negate >zst ;

: 2func \ m n xt -- set
  locals| xt n m | 0 n m
  do n m 
     do j i xt execute >zst 1+ 
     loop
  loop 2* negate >zst ;

: 3func \ m n xt -- set
  0 locals| h xt n m | 0 n m
  do i to h n m
     do n m 
        do i j h xt execute >zst 1+ 
        loop
     loop
  loop 2* negate >zst ;

: 4func \ m n xt -- set
  0 0 locals| k h xt n m | 0 n m
  do i to k n m
     do i to h n m
        do n m 
           do i j h k xt execute >zst 1+ 
           loop
        loop
     loop
  loop 2* negate >zst ;

: 5func \ m n xt -- set
  0 0 0 locals| g k h xt n m | 0 n m
  do i to g n m
     do i to k n m
        do i to h n m
           do n m 
              do i j h k g xt execute >zst 1+ 
              loop
           loop
        loop
     loop
  loop 2* negate >zst ;

: build-set \ m n xt -- set
  locals| xt n m |
  loc# @ 
  case 1 of m n xt 1func endof
       2 of m n xt 2func endof
       3 of m n xt 3func endof
       4 of m n xt 4func endof
       5 of m n xt 5func endof
  endcase set-sort reduce ;

: bset  build-set ;

\ cond ( n -- flag )
: sqr dup sqrtf dup * = ; 
: sqrfree dup radical = ; 
: twinprime dup isprime over 2 + isprime rot 2 - isprime or and ;  
: singleprime dup isprime swap twinprime 0= and ; 
: semiprime bigomega 2 = ; 
: primepower smallomega 1 = ; 
: biprime smallomega 2 = ; 

: 2sqsum  dup * swap dup * + ;
: 3sqsum  dup * rot dup * rot dup * + + ;
: 4sqsum  3sqsum swap dup * + ;
: 5sqsum  4sqsum swap dup * + ;  \ a b c d e -- a²+b²+c²+d²+e²
: <<  over > -rot < and ;  \ a<b<c
: <<=  over >= -rot <= and ;
: isp  isprime ;
: r2p  isprime swap isprime and ;
: r3p  isprime -rot isprime swap isprime and and ;
: fi postpone else postpone false postpone then ; immediate

\ cond ( m n -- flag )
: coprime ugcd 1 = ;
: cop  coprime ;
: divide swap mod 0= ; 

: factorset \ n -- set
  dup 1 = if >zst -3 >zst exit then
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
: sfac \ w -- w ?v | m n -- p/0 
  bdupeven if 2drop 2 bdup b2/ exit then
  0 locals| flag | 
  do bdup i pnr@ bs/mod 0= 
     if i pnr@ to flag leave then bdrop
  loop flag ;

: sfacset \ b -- b' set
  0                           \ count of the number of elements
  begin pi_plim 1 sfac ?dup 
  while >zst 2 - bnip 
     1 bdupdigit= 
     if 1- >zst exit then
     bdupisprime
     if 1- >zst exit then
  repeat 1- >zst ; 

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

: isq  sqr ;             \ is perfect square: n -- flag
: isqf  sqrfree ;        \ is square free: n -- flag
: isem  bigomega 2 = ;   \ is semi prime: n -- flag
: ispp  smallomega 1 = ; \ is prime power: n -- flag

: 2sqs  2sqsum ;         \ square sum: a b -- sum
: 3sqs  3sqsum ;         \ square sum: a b c -- sum
: 4sqs  4sqsum ;         \ square sum: a b c d -- sum

\ : rcop  coprime ;      \ are coprime: m n -- flag
: div  swap mod 0= ;     \ divides: m n -- flag
: z. zet. ;
: cset create-set ;
: fset filter-set ;
: bset build-set ;
: tset transform-set ;

: is-sum-of-two-squares \ n -- flag 
  dup 3 < if drop true exit then
  dup isprime if 3 and 3 <> exit then
  true 0 0 locals| m k flag | 
  primefactors 0 
  do flag
     if dup 3 and 3 =
        if m over = 
           if drop k 1+ to k 
           else to m k odd 1 to k 
              if false to flag then 
           then 
        else drop k odd 0 to k 
           if false to flag then
        then 
     else drop
     then
  loop flag k odd 0= and ;

: 2sqrs  is-sum-of-two-squares ;

: is-sum-of-three-squares \ n -- flag
  oddpart 7 and 7 <> swap odd 0= 0= or ;

: 3sqrs  is-sum-of-three-squares ;

: squaresum# \ n -- m=1,2,3,4
  dup sqr if drop 1 exit then
  dup is-sum-of-two-squares if drop 2 exit then
  is-sum-of-three-squares if 3 exit else 4 then ;
\ Lagrange's 4 square theorem

: sqs#  squaresum# ;
: primes  primefactors ;
: card  cardinality ;
: \0  { 0 } diff ;

: divz \ u -- set 
  locals| u | 
  0 u sqrtf 1+ 1
  do u 0 i um/mod -rot 0=
     if 2 +
        i >zst 
        swap >zst
     else nip
     then 
  loop 2* negate >zst
  set-sort reduce ;

: psum \ n -- m  n>0
  dup 1 = if drop 0 exit then
  dup isp if exit then
  primes 1
  do + loop ; \ sum of all prime factors

: psqsum \ n -- m  n>0
  dup 1 = if drop 0 exit then
  dup isp if ^2 exit then
  primes swap ^2 swap 1
  do swap ^2 + loop ; \ sum of all prime factors squared

: lpsum \ n -- p
  dup 4 = if exit then
  begin dup isp 0=
  while psum
  repeat ; 

: ismp \ n -- flag
  dup isp 0=
  if drop false 
  else 1+ oddpart nip 1 = 
  then ; \ is Mersenne prime

: lpf \ n -- p
  dup 1
  do dup i pnr@ mod 0=
     if drop i pnr@ leave then
  loop ;

: gpf \ n -- p
  primes over >r drops r> ;
\ greatest prime factor

: .s depth 0= if exit then >r recurse r@ . r> ;

: mu \ n -- mu(n)
  primes dup 0= if exit then
  0 swap 0 do swap pi + loop 
; \ mu(a*b)=mu(a)+mu(b)


\ Polynomials 1

\ Dynamical allocation of arrays

: >da \ vect -- vect ad n 
  zst @ zst@ cs tuck cells - swap ; 
\ Gives the address to the first coefficient plus the count
\ of the polynomial at top of stack

: >da2 \ vect2 vect1 -- vect2 vect1 ad2 n2  
  adn2 cell- cell / ;
\ Gives address and count to the second polynomial of stack

: >xst+ \ vect1 m -- vect2 
  xst> swap >xst 2 - >xst ; 
\ Add item to the xst list

: >zst+ \ vect1 m -- vect2 
  zst> swap >zst 2 - >zst ; 
\ Add item to the zst list

: da \ -- vect ad  
  -1 >zst zst @ ; 
\ Initiate an empty list 

: da. \ vect -- 
  >da 0
  do dup i cells + @ .
  loop zdrop drop ;
\ print the coefficients

\ Printing polynomials
\ 64 bits systems only

create potence 
s" " s,    s" x" s,   s" x²" s,  s" x³" s,  s" x⁴" s, 
s" x⁵" s,  s" x⁶" s,  s" x⁷" s,  s" x⁸" s,  s" x⁹" s, 
s" x¹⁰" s, s" x¹¹" s, s" x¹²" s, s" x¹³" s, s" x¹⁴" s, 
s" x¹⁵" s, s" x¹⁶" s, s" x¹⁷" s, s" x¹⁸" s, s" x¹⁹" s, 

true value lowterm 
: .term \ i n -- 
  ?dup 0= if drop exit then 
  dup 0< 
  if ." -"
  else lowterm 0= if ." +" then
  then abs dup 1 > 2 pick 0= or
  if 0 <# #s #> type 
  else drop 
  then false to lowterm 
  cells potence + count type ; 

: p. \ vect --
  true to lowterm
  >da 0 
  do i over i cells + @ .term
  loop zdrop drop ;

\ Greatest common divisors for multiple integers

: multgcd \ k1...kn n -- gcd
  dup 0= if exit then
  swap abs swap 1
  ?do swap abs ugcd loop ;
\ Gives multiple greatest common device

\ Calculation with polynomials

: polynom \ ad n m -- m' 
  locals| m | cells over + cell- 
  dup @ -rot cell- 
  ?do m * i @ + -cell +loop ; 
\ m' is the evaluation of m with polynomial at ad n

: sbs* \ sb m -- sb*m
  dup 0< xs> xor >xs abs bs* ;

: s>sb \ n -- sb
  dup abs s>b 0< >xs ;

: sbpolynom \ ad n m -- sb
  locals| m | cells over + cell- 
  dup @ s>sb cell- 
  ?do m sbs* i @ s>sb sb+ -cell +loop ; 
\ single input and big output

: polyn \ vect m -- vect m'
  >da rot polynom ;
\ m' is the evaluation of m with the polynomial vect

: sbpolyn \ vect m -- vect sb
  >da rot sbpolynom ;
\ m' is the evaluation of m with the polynomial vect

: gcoeff \ vect -- vect n
  zst @ cell - @ ;
\ Gives the coefficient of the greatest power

: lcoeff \ vect -- vect n
  >da drop @ ;
\ Gives the coefficient of the constant term

: rrzs \ vect1 -- vect2  "reduce right zeroes"
  begin gcoeff 0= 
  while zst> zst> drop 2 + >zst
  repeat ;
\ Eliminate leading coefficient equal to zero

: poly* \ ad1 n1 ad2 n2 -- vect 
  locals| n2 ad2 n1 ad1 | da drop 
  n1 n2 + 1- 0 
  do 0 i 1+ 0 
     do j i - 0 n2 within i n1 < and
        if i cells ad1 + @ 
           j i - cells ad2 + @ * + 
        then
     loop >zst+
  loop rrzs ; 
\ Multiply polynomials given by arrays

: p* \ vect1 vect2 -- vect3 
  >da2 >da poly*
  znip znip ;
\ Multiply polynomials

: v+ \ vect1 vect2 -- vect3 
  adn2 nip adn1 nip < if zswap then 
  adn2 drop locals| ad | 
  zst>> cs 0 
  do ad i cells + +! 
  loop ;
\ Add vectors

: p+ \ vect1 vect2 -- vect3 
  v+ rrzs ;
\ Add polynomials

: ps* \ vect1 n -- vect2
  locals| n |
  >da cells over + swap
  do i @ n * i ! cell +loop ;
\ Multiply polynomial with integer

: pnegate \ vect1 -- vect2
  -1 ps* ;

false [if]
: pnegate \ vect1 -- vect2
  adn1 cell- 0
  do dup i + dup @ negate swap ! cell
  +loop drop ;
\ Negate a polynomial
[then]

: p- \ vect1 vect2 -- vect3
  pnegate p+ ;
\ Subtract polynomials

: v- \ vect1 vect2 -- vect3
  pnegate v+ ;
\ Subtract vectors

: ps/ \ vect1 n -- vect2
  locals| n |
  >da cells over + swap
  do i @ n / i ! cell +loop ;
\ Divide polynomial with integer

: degree \ vect -- vect n
  zst@ cs 1- ;

\ long division

: vcutr \ vect1 n -- vect2
  degree swap 1- -
  >r zst>> cs r@ - >xs
  r> drops xs> 2* 1+ negate >>zst ;
\ vect2 is the n rightmost coefficients of vect1

: vshiftr \ vect1 -- vect2
  zst> zst> drop 2 + >zst ;
\ drop the rightmost coefficient 

: getcoeff \ xvect i -- xvect n
  cells xst @ cell - swap - @ ;

: vor \ vect -- flag
  zst>> cs 1 ?do or loop ;

: p/ \ v1 v2 -- v1/v2 flag
  degree zst yst setmove
  degree zst xst setcopy
  over 1+ vcutr                           \ w
  2 + 2 under+ swap 0 -rot
  do zst> zst@ swap >zst 
     yst> yst@ swap >yst /
     dup >xs 1 under+ 
     yst zst setcopy ps* v- 
     vshiftr ( i getcoeff ) zswap vmerge  \ w'
  loop
  zst> zst@ swap >zst 
  yst> yst@ swap >yst / dup
  >xs 1 under+ 
  yst zst setcopy ps* v- vor
  xst setdrop yst setdrop
  ( over 0 ?do xs> loop ) nip 0= ;
\ flag is true if v2 divides v1
\ else the division is irrelevant

\ auto definition of polynomial
: makepoly \ vect ad n --  name of polynomial
  cr ." : " type space 
  zst> zst> .
  cs 1- 1
  do ." over * " zst> . ." + "
  loop ." * " zst> . ." + ; " ;
\ Prints the definition of a polynomial to be
\ copied and pasted 

\ Integer valued polynomials 

: bin*sum \ ad k -- sum 
  locals| k ad |
  k 0= if 1 exit then 0 k 0 
  ?do i cells ad + @ 
     k i choose * + 
  loop ; 

: polyacoeff \ ad1 n1 -- vect 
  da locals| ad2 n1 ad1 |
  ad1 @ >zst+ 
  n1 1
  ?do ad1 n1 i polynom 
     ad2 i bin*sum - >zst+
  loop ; 
\ Calculate the vector (c0,...,cn) from 
\ integer polynomial at ad1 n1

: polya \ ad n m -- m' 
  swap -rot locals| m ad | 0 swap 0 
  ?do i cells ad + @ 
     m i choose * + 
  loop ; 
\ m' is the evaluation of m with the pólya function at ad n

: coeffgcd \ vect -- n
  zst>> cs       \ CS transform set count into stack count
  multgcd ;
\ GCD of the coefficients

: fixdiv \ vect -- vect n
  >da            \ get address and count for polynomial
  polyacoeff     \ calculate Pólya's coefficients
  coeffgcd ;
\ The multiple GCD of c0,...,cn is the fixed divisor of the
\ corresponding original polynomial with integer coefficients

: divcofac \ vect -- vect'
  zdup coeffgcd ps/ ;

: iseisenstein \ vect -- vect flag 
  zdup zst> 2 + zst> abs false 0 locals| p flag  an | 
  >zst coeffgcd dup an ugcd 1 <>
  if zdrop drop false exit then
  primes ?dup 
  if 0 
     do to p flag 0= 
        if an p umod 0= 0= 
           >da drop @ abs p ^2 umod 0= 0= and 
           to flag 
        then 
     loop 
  then flag ;

2000 value xlim

: isirr \ vect -- vect flag 
  iseisenstein if true exit then
  degree 0= if gcoeff isp exit then 
  degree 1 = if zdup coeffgcd 1 = exit then 
  fixdiv degree 0 0 locals| posp negp n d | 
  0 sbpolyn d bs/mod drop bisprime 
  if xs@ if negp 1+ to negp else posp 1+ to posp then
  then xsdrop
  xlim 1
  do i sbpolyn d bs/mod drop bisprime
     if xs@ if negp 1+ to negp else posp 1+ to posp then
     then xsdrop
     i negate sbpolyn d bs/mod drop bisprime
     if xs@ if negp 1+ to negp else posp 1+ to posp then
     then xsdrop 
     posp n > negp n > or if leave then
  loop posp n > negp n > or ; 

: nopsqr \ x p -- x'     p|x
  begin 2dup /mod swap 0=
  while -rot nip
  repeat drop * ; 

: negate? \ |n| -- n
  2 random if negate then ;

: pickprime \ n -- p
  primes dup >r 1 max random 
  pick r> drops ;

: geteis0 \ u -- vect p
  ( )
  2 - 1 max random 2 +
  dup pickprime 
  tuck nopsqr negate? >zst+ ; 

: x/p^n \ an p -- an'
  begin 2dup mod 0=
  while tuck / swap
  repeat drop ;

: geteisvar \ n u -- vect
  dup geteis0 locals| p u | 1- 1 max random 1+ 0
  ?do u p / random 1+ p * negate? >zst+
  loop u 1+ random 1+ p x/p^n dup 0= or
  negate? >zst+ 
  divcofac ;

: dupderiv \ vect -- vect vect'
  ( >da swap locals| ad | 1
  do ad i cells + @ i * loop ) ;

: deriv \ vect -- vect'
  dupderiv znip ;

\ p(x) --> p(x+d)

: mtransl \ k d ak -- vect
  locals| ak d k |
  ( k 1+ 0
  do k i choose d i ** * ak *
  loop ) ;

: zerovect \ n -- vect
  >r ( r> 0
  do 0 loop ) ;

: ptransl \ vect1 d -- vect2 
  locals| d | 
  >da 0 over zerovect 
  do i over i cells + @ d swap 
     mtransl p+ 
  loop drop znip ; 

\ Rational roots

: q* \ a b c d -- ac/(ac,bd) bd/(ac,bd)
  rot * >r * r>         \ ac bd
  2dup abs swap abs
  ugcd tuck             \ ac gcd bd gcd 
  / >r / r> ; 

: q/  2swap q* ;

: q+ \ a b c d -- (ad+bc)/gcd bd/gcd
  dup 3 pick * >r      \ a b c d  r: bd
  -rot * -rot * +      \ a*d+b*c  r: bd
  dup abs r@ abs
  ugcd r> over         \ a*d+b*c gcd bd gcd
  / >r / r> ;

: q-  negate q+ ;

: qpolynom \ ad n a b -- a' b' 
  locals| b a | cells over + cell- 
  dup @ >r cell- r> 1 2swap
  do a b q* i @ 1 q+ -cell +loop ; 

: getpospairs \ vect -- vect set
  lcoeff abs gcoeff abs divz divz
  cartprod ;

: getypair \ yset -- yset' y x
  yst> drop yst> yst> ;

: haverationalroots \ vect -- vect flag
  lcoeff 0= if true exit then
  getpospairs zst yst setmove
  begin yst@
  while ysplit
     getypair 2dup ugcd 1 = 
     if >da 2over qpolynom drop 0= 
        if yst setdrop 2drop true exit then 
        >r negate >r 
        >da r> r> qpolynom drop 0= 
        if yst setdrop true exit then 
     else 2drop 
     then 
  repeat yst> ; 

: setofroots \ vect -- vect set
  lcoeff 0= if true exit then
  getpospairs 
  zst yst setmove xst @
  begin yst@
  while ysplit
     getypair 2dup ugcd 1 = 
     if >da 2over qpolynom drop 0= 
        if ( 2dup ) zst xst setmove then
        swap negate swap
        >da 2over qpolynom drop 0=
        if ( 2dup ) zst xst setmove then
     then 2drop
  repeat yst> drop
  xst @ - cell / 2* >xst
  xst zst setmove ; 

: .root \ b a --  "a/b"
  dup 0= if . drop exit then
  over abs 1 = if . drop exit then
  . 8 emit ." /" . ;

: .roots \ set -- 
  zst> cs 3 / 0 
  do zst> drop zst> zst> .root space loop 
;

: isirreducible \ vect -- vect flag
  haverationalroots degree 1 > and
  if false else isirr then ;

\ Testing --------------------------------

19 value clim
6 value rlim

: raco \ -- n  random coefficient
  clim random clim 2/ - ;

: racos \ m -- k1...km
  0 do raco loop ;

: getirrvar \ u -- vect
  locals| u |
  begin u random 1+ to rlim
     ( rlim 2 + racos ) rrzs
     divcofac isirr 0= 
  while zdrop 
  repeat ; 

: getirr \ -- vect
  begin ( rlim racos ) rrzs
     divcofac isirr 0=
  while zdrop
  repeat ;

: geteis \ -- vect
  begin ( rlim racos ) rrzs
     divcofac iseisenstein 0=
  while zdrop
  repeat ;

: test1 \ r n --
  0
  do dup geteisvar isirr 
     if zdrop else cr p. then
  loop drop ;

: clp clxs cl q ;

: get1irr ( raco dup raco dup abs rot abs ugcd / ) ;
: get1any ( raco raco ) ;
: getpol ( rlim 1+ random 2 + racos 1 or ) ;
: getreg getpol divcofac ;
: getred begin getreg isirr 0= until ;

