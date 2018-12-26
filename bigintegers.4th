\ unsigned natural numbers of dynamical length in 32+ bit ANS Forth
\ https://github.com/Lehs/ANS-Forth-libraries
\ https://forthmath.blogspot.se

s" numbertheory.4th" included

false value karatsuba \ multiplication 

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
  begin len1 2 <=     if exit then nextfree 1- c@ 0=
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

: msb@ \ v -- v | -- c      most significant byte in value on tos
  nextfree cell- nextfree 1-
  do i c@ ?dup if leave then -1 +loop ;

: msb@2 \ u v -- u v | -- c      most sign byte second for on stack
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

: bcells. \ b -- 
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
     y brshift b- 
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
  den b@ b* b-         \ w-q*den
  den b@ b2dup<        \ w-q*den den flag
  if bdrop else b- then ;

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

: digit= \ u n -- f    u=n?
  len1 cell > if drop bdrop false exit then
  first @ = bdrop ;

: pseudo1 \ xsi s m -- | -- f
  bar**mod 1 digit= ;

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
