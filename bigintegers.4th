\ unsigned natural numbers of dynamical length in 32+ bit ANS Forth
\ forthmath.blogspot.se

s" numbertheory.4th" included

: ?undef ( -- flag ) bl word find nip 0= ;
\ flag is true if word undefined

base @ hex

\ miscellanous

: 0! 0 swap ! ;
: 1+! 1 swap +! ;
: u2/ 1 rshift ;
?undef u/ [if] : u/ 0 swap um/mod nip ; [then]
?undef umod [if] : umod 0 swap um/mod drop ; [then]
?undef cell- [if] : cell- cell - ; [then]
?undef rdrop [if] : rdrop r> drop ; [then]
?undef .r [if] : .r >r 0 <# #S #> r> over - spaces type ; [then]
?undef s>f [if] : s>f s>d d>f ; [then]
?undef f>s [if] : f>s f>d d>s ; [then]

: d256*  \ ud -- 256ud
  over 8 lshift rot 0FF000000 and 018 rshift
  rot 8 lshift or ;

: sqrtf \ m -- n       floor
  0 d>f fsqrt f>s ;

: sqrtc \ m -- n  ceiling
  1- sqrtf 1+ ;

0400 constant 1k
0800 constant 2k
cell negate constant -cell

: log~ \ n -- #binary digits
  0 swap begin swap 1+ swap u2/ ?dup 0= until ;

    8 cell * constant bits
     bits 1- constant bits-1
 bits-1 log~ constant lbits
cell log~ 1- constant lcell

: 2/mod \ n -- r q
  dup 1 and swap u2/ ;

: 4/mod \ n -- r q
  dup 3 and swap 2 rshift ;

: 8/mod \ n -- r q
  dup 7 and swap 3 rshift ;

: bits/mod \ n -- r q
  dup bits-1 and swap lbits rshift ;

: 256/mod \ n -- r q
  dup 0FF and swap 8 rshift ;

\ extra stacks for singel numbers

: clst ( ad -- )  dup ! ;
: stdrops ( m ad -- )  swap cells negate swap +! ;
: stdrop ( ad -- ) -cell swap +! ;
: >st ( n ad -- )  cell over +! @ ! ;
: st> ( ad -- n )  dup @ @ -cell rot +! ;
: >st> ( n ad -- m )  dup @ @ -rot @ ! ;
: st@ ( ad -- n )  @ @ ;
: st! ( n ad -- )  @ ! ;
: st+! ( n ad -- )  @ +! ;
: stpick ( m ad -- xm )  @ swap cells - @ ;
: stpatch ( n m ad -- )  @ swap cells - ! ;
: stpatad ( n m ad -- )  @ swap cells - +! ;
: stdepth ( ad -- n )  dup @ swap - lcell rshift ;

: .st \ ad --
  dup @ cell+ swap cell+
  ?do i @ . cell
  +loop ;

: >st# \ xn ... x1 n ad --
  swap 0
  ?do cell over +! swap over @ !
  loop drop ;

: stack \ size --
  allocate throw dup constant clst ;

2k stack xs

: >xs ( n -- )  xs >st ;
: xs> ( -- n )  xs st> ;
: >xs> ( m -- n)  xs >st> ;
: xs@ ( -- n )  xs st@ ;
: xs! ( n -- )  xs st! ;
: xs+! ( n -- )  xs st+! ;
: xsdrop ( -- )  xs stdrop ;
: xsdepth ( -- #bytes )  xs stdepth ;

2k stack ys

: >ys ( n -- )  ys >st ;
: ys> ( -- n )  ys st> ;
: >ys> ( m -- n)  ys >st> ;
: ys@ ( -- n )  ys st@ ;
: ys! ( n -- )  ys st! ;
: ys+! ( n -- )  ys st+! ;
: ysdrop ( -- )  ys stdrop ;
: ysdepth ( -- n )  ys stdepth ;

2k stack zs

: >zs ( n -- )  zs >st ;
: zs> ( -- n )  zs st> ;
: >zs> ( m -- n)  zs >st> ;
: zs@ ( -- n )  zs st@ ;
: zs! ( n -- )  zs st! ;
: zs+! ( n -- )  zs st+! ;
: zsdrop ( -- )  zs stdrop ;
: zsdepth ( -- n )  zs stdepth ;

: drop-all ( -- )  xsdrop ysdrop zsdrop ;

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

0A000 constant maxv
maxv cell + allocate throw aligned constant v$0
v$0 maxv + constant b0
variable bvp

\ extra stack
08000 constant maxx
maxx cell + allocate throw aligned constant x$0
x$0 maxx + constant x0
variable xp

\ extra pad
02000 dup allocate throw constant pad1
pad1 + cell - constant pad2

: rez \ a n -- a' n'  delete leading zero ascii 48
  dup 1 =
  if exit
  then over c@ 030 =
  if 1- swap 1+ swap recurse
  then ;

: asc>  0F and ;    \ ascii number to binary number
: >asc  030 or ;    \ reverse
: vst!  b0 cell - bvp ! v$0 bvp @ ! ;

vst!   \ initialize stack för dynamical numbers

: nextfree ( -- a )  bvp @ @ ;
: first ( -- a )  bvp @ cell + @ ;  \ big on tos
: second ( -- a )  bvp @ 2 cells + @ ;  \ big on second
: third ( -- a )  bvp @ 3 cells + @ ;  \ big on third
: vp+ ( -- )  -cell bvp +! ;    \ stack pointer

: tov \ ad --    ad of number array to stack
  vp+ bvp @ ! ;

: bempty ( -- f )  nextfree v$0 = ;
: len1 ( -- n )  nextfree first - ;  \ get length to first
: len2 ( -- n )  first second - ;
: len3 ( -- n )  second third - ;
: top$ ( -- a n )  first len1 ;
: sec$ ( -- a n )  second len2 ;
: thi$ ( -- a n )  third len3 ;

: vdigit \ n --    put single "digit" on stack
  nextfree tuck ! cell+ tov ;

: bsconstant \ n --
  create , does> @ vdigit ;

: dvdigit \ ud --   put double "digit" number on stack
  swap nextfree dup >r 2! 2 cells r> + tov ;

: bdconstant \ d --
  create , , does> 2@ dvdigit ;

: vpush \ a n --  put string on stack
  rez >xs nextfree xs@ over + tov xs> cmove ;

: bpush \ a n --  put any number array on stack
  nextfree over aligned     \ a n nxt na
  2dup + cell - 0!          \ a n nxt na
  over + tov              \ a n nxt
  swap cmove ;

: bpusha \ a n --  put aligned number array on stack
  nextfree 2>r 2r@ swap cmove
  2r> + tov ;

: bdupall \ v -- v u        allocate array of same size as btos
  nextfree len1 + tov ;

: bdrop  cell bvp +! ;
: bdup  top$ bpusha ;
: vdup  top$ vpush ;
: bover  sec$ bpusha ;
: boover  thi$ bpusha ;

: bvariable \ n --
  create allocate throw cell , , does> ;

: b! \ v -- | ad --
  dup cell+ @ first nextfree over - rot swap >r r@ cmove
  r> swap ! bdrop ;

: b@ \ -- v | ad --
  2@ bpusha ;

: xstack!  x0 cell - xp ! x$0 xp @ ! ; xstack!  \ xtra stack
: xp+ ( -- )  -cell xp +! ;
: tox ( a -- )  xp+ xp @ ! ;
: xnext ( -- ad )  xp @ @ ;
: xfirst ( -- ad )  xp @ cell+ @ ;
: xsecond ( -- ad )  xp @ 2 cells + @ ;
: xthird ( -- ad )  xp @ 3 cells + @ ;
: xlen ( -- n )  xnext xfirst - ;
: xpush ( a n -- ) rez >xs xnext xs@ over + tox xs> cmove ;

: bxpush ( a n -- ) >xs xnext xs@ over + tox xs> cmove ;
: xdrop  cell xp +! ;
: xempty ( -- f )  xnext x$0 = ;

: >bx ( v -- )  top$ bxpush bdrop ;
: bx! ( v -- v )  top$ bxpush ;
: bx  ( -- v )  xfirst xnext over - bpusha ;
: bx> ( -- v )  bx xdrop ;

: by  \ -- v  y is the second value on x-stack
  xsecond xfirst over - bpusha ;

: bz  ( -- v )  xthird xsecond over - bpusha ;
: v>x ( v -- )  top$ bdrop xpush ;
: vx  ( -- v )  xfirst xnext over - vpush ;
: vx> ( -- v )  vx xdrop ;

: vy  \ -- v
  xsecond xfirst over - vpush ;

: bnip  >bx bdrop bx> ;
: bswap  >bx >bx by bx> xdrop ;
: vswap  v>x v>x vy vx> xdrop ;
: brot  >bx bswap bx> bswap ;
: btuck  bswap bover ;
: b2swap brot >bx brot bx> ;
: b2dup bover bover ;
: b2drop bdrop bdrop ;
: b3dup boover boover boover ;

: reztop  top$ xpush bdrop bx> ;      \ clean leading asczeros
: vzero  [char] 0 nextfree tuck c! 1+ tov ;
: bzero 0 vdigit ;                    \ small bigintegers
: bone  1 vdigit ;
: btwo  2 vdigit ;
: bthree 3 vdigit ;
: bten  0A vdigit ;

: byte1@ \ v -- v | -- b  get least significant byte of tos
  first c@ ;

: byte2@ \ v -- v | -- b  least sign byte on second number
  second c@ ;

: <vtop  \ delete unwanted leading asc zeros
  begin len1 2 <
     if exit then nextfree 1- c@ 0=
  while -1 bvp @ +!
  repeat ;

: <top  \ delete unwanted leading zeros
  begin len1 cell > 0=
     if nextfree 0! exit
     then nextfree cell - @ 0=
  while -cell bvp @ +!
  repeat nextfree 0! cell len1 3 and - 3 and bvp @ +! ;

: bs/mod \ v -- q | n -- r    v=nq+r
  >xs bdupall nextfree cell - 0!
  0 0 len1 cell -
  do i second + @ swap xs@ um/mod i first + ! -cell
  +loop <top xsdrop bnip ;

: vr< \ u v -- u v | -- f  compare numbers as asc strings
  reztop <vtop vswap reztop <vtop vswap
  len2 len1 2dup <
  if 2drop true exit
  then dup >zs >
  if zsdrop false exit
  then first nextfree 1-
  do i zs@ - c@ i c@ 2dup = 0=
     if zsdrop < if true else false then unloop exit
     then 2drop -1
  +loop zsdrop false ;

: vr= \ u v -- u v | -- f
  vr< if false exit then
  vswap vr< if vswap false exit then vswap true ;

: v2/  \ v -- v/2
\ divide asc number by 2
  nextfree first >xs 0 >ys
  begin xs@ c@ over xs@ >
  while asc> 2/mod ys> + >asc xs@ c!
     negate 5 and >ys 1 xs+!
  repeat reztop <vtop 2drop xsdrop ysdrop ;

: v>byte \ u -- v | -- f b
\ divide asc-string by 256 leaving rest b. f true if v=0
  xsdepth false >ys 8 0
  do nextfree 1- c@ 1 and >xs v2/ vzero vr= bdrop
     if true ys! leave then
  loop xsdepth swap - 0 tuck
  do 2* xs> + loop ys> swap ;

: nth ( n -- b/0 )  1+ bvp @ swap cells +
  dup b0 = if drop 0 else @ then ;

: len# \ n -- m
  dup nth swap 1- nth ?dup
  if swap else v$0 swap then - ;

: bpick \ bn ... b0 -- bn ... b0 bm | m --
  dup nth swap len# bpusha ;

: xnth ( n -- b/0 )  1+ xp @ swap cells +
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

: s>b \ -- v | n --  convert single to big
  0 <# #s #> vpush v>b ;

: b>s  \ u -- | -- n  conv big to single
  first @ bdrop ;

: d>b \ -- v | d --
  <# #s #> vpush v>b ;

: b>d  \ u -- | -- d
  top$ 5 < if @ 0 else 2@ swap then bdrop ;

: v  bl parse vpush ;     \ 'v 12345' put asc numb on tos
: b  v v>b ;             \ put bigint on tos
: cl vst! xstack! ;    \ clear stacks

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
  0 >xs nextfree first
  do i over - @ i @ 0 tuck d+ xs> 0 d+ >xs i ! cell
  +loop drop xs> ?dup if nextfree cell bvp @ +! ! then ;

: b+ \ u v -- u+v    adding bigint
  len2 len1 < 0=
  if b+_s>=f
  else bswap b+_s>=f
  then bnip ;

: br< \ u v -- u v | -- f  bigstack remain less
  len2 len1 2dup u<
  if 2drop true exit
  then dup pad1 ! u>
  if false exit
  then first >xs second >ys 0 >zs 0 pad1 @ cell -
  do ys@ i + @ xs@ i + @ 2dup = 0=
     if drop-all u< if true else false then unloop exit
     then 2drop -cell
  +loop drop-all false ;

: b< \ u v -- | --f    bigstack less
  br< bdrop bdrop ;

: br= \ u v -- u v | -- f
  br< if false exit then
  bswap br< if bswap false exit then bswap true ;

: b= \ u v -- | --f
  br= bdrop bdrop ;

: br> \ u v -- u v | -- f
  br= br< or 0= ;

: b> \ u v -- | --f
  br> bdrop bdrop ;

: br0= \ v -- v | -- f
  len1 cell - first @ or 0= ;

: b0= \ v -- | -- f
  br0= bdrop ;

: b>v$ \ b -- b | -- a n
  pad2 pad1 ! bdup 0A
  begin dup bs/mod >asc pad1 @ c! -1 pad1 +! br0= until
  drop bdrop 1 pad1 +! pad1 @ pad2 over - 1+ ;

: b>v  \ b -- b v
  b>v$ vpush ;

: bdec# ( b -- b | -- n )  b>v$ nip ;

: br. \ b -- b
  b>v$ type space ;

: b. \ b --
  br. bdrop ;

: .b  bempty 0=
  if cr br. >bx recurse bx> then ;

: .x  xempty 0=
  if bx> cr br. recurse >bx then ;

: gtx? \ v -- v | -- f    greater than value in bx?
  len1 xlen 2dup <
  if 2drop false exit then >
  if true exit then false 0 xlen cell -
  do first i + @ xfirst i + @ 2dup <
     if 2drop leave then >
     if 0= leave then -cell
  +loop ;

: +x>=y? \ v -- | -- f    add v to bx and compare with y
  bx> b+ bx> br< >bx >bx 0=
  dup if xdrop xdrop then ;  \ 2 xdrop when equal or greater

variable borrow
: b~ \ u v -- |u-v| | -- f
  br< if bswap true else false then >zs
  first len1 + len2 len1 - dup bvp @ +! erase
  false borrow ! first >xs second >ys len1 0
  do i ys@ + @ 0
     borrow @ 0 d-
     i xs@ + @ 0 d-
     abs borrow ! i ys@ + ! cell
  +loop 0 >zs bdrop drop-all <top zs> ;

: b- \ u v -- u-v
  b~ if cr ." negative big!" cr 10 throw then ;

: |b-| \ u v -- |u-v|
  b~ drop ;

: bsl \ n i -- n1 n0        big shift left, n < 2^bits
  2dup bits swap - rshift -rot lshift ;

: blshift  \ v -- u | n --     big left shift
  bits/mod over 0=
  if nip first dup rot cells dup >xs + len1 cmove>
     xs@ bvp @ +! first xs> erase exit
  then cells >ys      \ i  y=4[n/32]
  ys@ first dup >xs +       \ i f+4[n/32]  x=first
  xs@ over len1 dup >zs cmove>    \ i f+4[n/32]  z=len1
  xs@ ys@ erase
  zs> over + dup xs! swap 0 >zs    \ i f+4[n/32]+len1 f+4[n/32]
  ?do i @ over bsl zs> or i ! >zs cell +loop
  zs@ xs@ ! xs@ cell+ bvp @ ! drop drop-all <top ;

: brshift \ v -- u | n --
  8/mod >ys >xs
  nextfree 0! nextfree first
  do ys@ i + @ 0FFFF and xs@ rshift 0FF and i c!
  loop nextfree ys@ - ys> erase
  <top xsdrop ;

: b1and \ v -- v s
  first @ 1 and vdigit ;

: beven \ v -- v | -- f
  first @ 1 and 0= ;

: bodd \ v -- v | -- f
  beven 0= ;

: b1or \ v -- v'
  first @ 1 or first ! ;

: b2/mod \ v -- r k
  b1and bswap 1 brshift ;

: msb@ \ v -- v | -- c      most significant byte in value on tos
  nextfree cell- nextfree 1-
  do i c@ ?dup if leave then -1 +loop ;

: msb@2 \ u v -- u v | -- c      most sign byte second for on stack
  first cell- first 1-
  do i c@ ?dup if leave then -1 +loop ;

: z# \ v -- v | -- n      nr of zero bytes in most sign cell tos
  0 >xs nextfree
  begin 1- dup c@ 0=
  while 1 xs+!
  repeat drop xs> ;

: z#2 \ u v -- u v | -- n
  0 >xs first
  begin 1- dup c@ 0=
  while 1 xs+!
  repeat drop xs> ;

: blog~ \ v -- v | -- n    8(len-1)+log(byte0)+1
  len1 z# - 1- 3 lshift msb@ log~ + ; \ n is the number of binary digits

: blog~2 \ u v -- u v | -- n
  len2 z#2 - 1- 3 lshift msb@2 log~ + ;

: blog \ v -- | -- n   integer part of 2-logarithm
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

: cell*x \ -- n*v ; x: v -- v | n --
  bzero 0 >xs xnext xfirst
  do dup i @ um* xs> 0 d+ >xs last!> cell +loop
  xs> nextfree cell - ! drop <top ;

: bs* \ v -- n*v | n --
  >bx cell*x xdrop ;

: bdups* \ v -- v n*v | n --
  bzero 0 >xs first second
  do dup i @ um* xs> 0 d+ >xs last!> cell +loop
  xs> nextfree cell - ! drop <top ;

: bitsblshift \ v -- w         big shift left with number of bits
  top$ over cell+ swap cmove>
  cell bvp @ +! 0 first ! ;

: b* \ u v -- u*v
  len1 len2 < if bswap then
  >bx bzero second first cell -
  do bitsblshift i @ cell*x b+ -cell +loop
  bnip xdrop <top ;

: brandom \ -- u | n --  the maximal number of decimal digits in u
  bzero 0 do bten b* 10 random s>b b+ loop ;

\ 2^sxn+1=2*2^sxn-[2^sxn]^2*n/2^[2s]
\ q=t*x/2^[2n]
: b/ \ u v -- q   Newton-Ralphson on y=2^s/x-A
  br< if bdrop bdrop bzero exit then          \ qoute < 1
  len1 cell > 0=
  if b>s bs/mod drop exit then                \ denominator < 2^bits
  blog~ >xs >bx bdup blog~ 2/ 6 + >ys
  ys@ 2* xs> - dup >xs bone blshift xs>
  if 6 bs* 5 bs/mod drop then 1F 0            \ start value
  do bdup b2* bover bdup b* bx b*
     ys@ 2* brshift b-
     br= bnip
     if leave then
  loop b* ys> 2* brshift
  begin bover bover bx b* b< while b1- repeat
  begin bover bover bx b* bx b+ b< 0= while b1+ repeat
  bnip xdrop ; \ t-nq>n <=> t>n+nq

\ Barrett reduction
\ Faster modulo when repeting [mod d] with same d

variable foo
1k bvariable bar
1k bvariable den

: barmod~ \ w -- v      w < d**2
  bdup
  bar b@ b*
  foo @ brshift        \ w q
  den b@ b* b-         \ w-qd
  den b@ br<
  if bdrop else b- then ;

: barmod \ w -- v      w < d**2
  bdup den b@ br<
  if b2drop exit
  then bdrop bar b@ b*
  foo @ brshift        \ w q
  den b@ b* b-         \ w-qd
  den b@ br<
  if bdrop else b- then ;

: >bar \ u --      u is the denominator; precalc for barmod
  blog~ 2* dup foo !       \ foo = 2*bitlen
  bone blshift bover b/ bar b!     \ bar = 2^foo/u
  den b! ;        \ den = u

: b** \ b a -- b^a
  first @ 0= if bdrop bdrop bone exit then
  >bx bzero >bx bone
  begin bover b*
     bone +x>=y?
  until bnip ;

: bmod \ w u -- r
  bover bover b/ b* b- ;

: b/mod \ w u -- r q
  bover bover b/ bdup >bx b* b- bx> ;

: bsqrtf \ w -- v                  \ Newton-Ralphson
  br0= if exit then
  blog~ u2/ bone blshift 10 0      \ start value
  do bover bover b/ br=
     b+ b2/ if leave then
  loop bdup bdup b* brot bswap br< bdrop bdrop
  if b1- then ;

: bsqrtc \ w -- v
  b1- bsqrtf b1+ ;

: bfactorial  \ v -- v!
  >bx bzero bone
  begin bswap b1+ gtx? bswap 0=
  while bover b*
  repeat bnip xdrop ;

: bgcd \ v u -- w  greatest common divisor
  br< if bswap then
  begin btuck bmod br0=
  until bdrop ;
false [if]
: gcd \ m n -- d
  2dup u< if swap then
  begin tuck 0 swap um/mod drop dup 0=
  until drop ;
[then]
: blcm \ v u -- w  least common multiple
  bover bover b* brot brot bgcd b/ ;

\ the square-and-multiply-algorithm
: b**mod~ \ u v m -- u^v mod m
  >bx blog~ bswap >bx bone 0        \ v 1 | x: m u | l[v] 0
  do i bits/mod cells second + @    \ v w | x: m u | r celli
     1 rot lshift and        \ v w | x: m u | celli & 2^r
     if bx b* by bmod        \ v [w*u]
     then bx bx> b* bx bmod >bx     \ v [w*u] x<-[x*x]
  loop bnip xdrop xdrop ;

\ the square-and-multiply-algorithm with Barrett reduction ?
: b**mod \ u v m -- u^v mod m
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
  begin br0= 0=
  while bover bover b/ >bx flag21 @ flag22 @ xor flag !
     b2swap btuck bx flag12 @ flag @ flag11 @
     sign-comp flag12 ! flag11 !
     b2swap btuck bx> flag22 @ flag @ flag21 @
     sign-comp flag22 ! flag21 !
  repeat bdrop bdrop bdrop flag12 @
  if bover |b-| then bswap bmod ;

: bschoose \ n k -- b
  bone 0
  ?do dup i - bs*
     i 1+ bs/mod drop
  loop drop ;

\ rabin-miller strong pseudoprime test

: rs \ u -- s | -- r
  b1- nextfree first 0 >xs
  do i @ if i >ys leave then 1 xs+! cell
  +loop ys> @ bits 0
  do dup 1 and if i leave then u2/
  loop nip xs> lbits lshift +
  dup brshift ;

: digit= \ u -- | n -- f  u=n?
  len1 cell > if drop bdrop false exit then
  first @ = bdrop ;

: pseudo1 \ xsi s m -- | -- f
  b**mod 1 digit= ;

: pseudo2 \ xsi s m -- | r -- f
  >bx bx b1- >bx false >ys 0
  do bover bover i blshift by b**mod
     bx b=
     if true ys! leave then
  loop xdrop xdrop bdrop bdrop ys> ;

: bmiller \ u -- u | -- f    u odd >3
  >bx bx btwo bx rs >zs bover bover
  bx pseudo1 ?dup
  if xdrop bdrop bdrop zsdrop exit
  then bx> zs> pseudo2 ;
\ u is of the form u=1+s*2^r, where s is odd
\ given any number 1 < xsi < u
\ if xsi^s=1[mod u] or
\ if it exist j: 0 =< j < r with
\ xsi^[s*2^j]=-1[mod u]
\ then u is pseudoprime.

: bisprime \ b -- flag
  len1 cell >
  if bmiller bdrop
  else b>s isprime
  then ;

: bnextprime \ b -- p
  b1or
  begin bdup bisprime 0=
  while b2+
  repeat ; 

base !

