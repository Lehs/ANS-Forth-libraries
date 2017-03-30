\ NESTED SETS WITH CARTESIAN PRODUCTS

: log~ \ n -- #binary digits
  0 swap begin swap 1+ swap 1 rshift ?dup 0= until ;

: -cell cell negate ;

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

: set. \ yst,xst --
  zst setcopy zet. ;

\ Analyzing sets_____

: ?obj \ x -- 0,1,2
  dup 0<
  if listflag
     if 1 else 2 then
  else drop 0
  then ;

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
    2dup - negate 1 rshift >r \ keep radius (half of the distance)
    2dup singlepart 2dup - >r >r \ ( R: radius distance2 ad )
    r@ cell - swap r> cell+ swap \ ( d-subarray1 d-subarray2 )
    2r> u< if 2swap then recurse \ take smallest subarray first
  again \ tail call optimization by hand
;

: qsort~ \ ad1 ad2 --      pointing on first and last cell
  2dup <
  if 2dup singlepart >r
     swap r@ cell - recurse
     r> cell + swap recurse
  else 2drop
  then ; \ problem with sorting sorted big set

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
  zst @ cell - 2@ or 0=
  if zdrop zdrop true exit then      \ true if both sets are empty
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
: infence \ -- | s -- s'
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

\ from rosetta code
: choose \ n k -- nCk
  1 swap 0
  ?do over i - i 1+ */
  loop nip ;

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

: functions \ -- | s s' -- s"
  secobjad @ 0= if zdrop -2 >zst exit then
  secobjad @ -2 = if cartprod infence exit then
  zswap zsplit zfence zst xst setmove
  zover recurse zswap xst zst setmove
  zswap cartprod infence zetunion ;

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
: all dup = ;
: odd 1 and ;
: even 1 xor ;
: 1mod4 4 mod 1 = ;
: 3mod4 4 mod 3 = ;

\ 30 70 | odd
: | \ m n -- x1...xk
  swap ' locals| xt |
  ?do i xt execute if i then loop false to sort? ;
 
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

: square dup * ;                \ x ? x²

: paircond \ xt -- | s -- s'
  locals| xt | 0
  foreach
  ?do zdup zet> drop xt execute
     if zst xst setmove 1+ else zdrop then
  loop 6 * negate >xst
  xst zst setmove ;

: pairimage \ xt -- | s -- s'
  locals| xt | 0
  foreach
  ?do 1+ zet> drop xt execute >xst
  loop dup 0
  ?do xst> >zst
  loop 2* negate >zst
  set-sort reduce ;

: int2cond \ low hi n xt -- | -- s   "intervall two-condition"
  locals| xt n |
  swap 0 -rot
  ?do i n xt execute
     if i >zst 1+ then
  loop 2* negate >zst ;

: int2image \ low hi n xt -- | -- s  "intervall image"
  locals| xt n |
  swap 2dup
  ?do i n xt execute >zst
  loop - 2* negate >zst
  set-sort reduce ;

: set2cond \ n xt -- | s -- s'       "set condition"
  locals| xt n | 0
  foreach
  ?do zst> dup n xt execute
     if >xst 1+ else drop then
  loop dup 0
  ?do xst> >zst
  loop 2* negate >zst ;

: set2image \ n xt -- | s -- s'      "set image"
  locals| xt n | 0
  foreach
  ?do zst> n xt execute >xst 1+
  loop dup 0
  ?do xst> >zst
  loop 2* negate >zst
  set-sort reduce ;

variable zp
variable cf2

: condition  ' 0 cf2 ! sp@ zp ! ;
: function  ' 2 cf2 ! sp@ zp ! ;
: 2dim  ' -1 cf2 ! sp@ zp ! ;
: syntax  sp@ zp @ - 0= if 0 0 else 1 then cf2 @ ;
: non all ;

\ e.g. 1 20 condition < 7 create-set
: create-set \ m n xt nr -- set
  syntax locals| cf k nr xt n m |
  k cf or
  case 0 of m n xt intcond endof
       1 of m n nr xt int2cond endof
       2 of m n xt intimage endof
       3 of m n nr xt int2image endof
  endcase ;

\ e.g. condition > 5 filter-set
: filter-set \ set xt nr -- set'
  syntax locals| cf k nr xt |
  cf 0< if xt paircond exit then k
  case 0 of xt setcond endof
       1 of nr xt set2cond endof
  endcase ;

\ e.g. 2dim + transform-set
: transform-set \ set xt nr -- set'
  syntax locals| cf k nr xt |
  cf 0< if xt pairimage exit then k
  case 0 of xt setimage endof
       1 of nr xt set2image endof
  endcase ;
