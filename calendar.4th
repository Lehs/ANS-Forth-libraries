\ Calendar functions

\ String extensions
: c+! \ c adr -- 
  tuck c@ + swap c! ;
  
: c1+! \ adr -- 
  1 swap c+! ;
  
: string! \ ad n adr -- 
  >r dup r@ c! r> 1+ swap move ;
  
: string& \ ad n cadr -- 
  >r tuck r@ count + swap move r> c+! ;
  
: char& \ ch cad -- 
  tuck count + c! c1+! ;
  
: space& \ cad -- 
  bl swap char& ;
  
: unum& \ u cad -- 
  swap 0 <# #s #> string& ;
  
: num& \ n cad -- 
  swap dup abs 0 <# #s rot sign #> string& ;

: mjd \ y m d -- mjd
  swap rot
  >r 3 - dup 0< 
  if 12 + r> 1- >r 
  then 153 * 2 + 5 / +
  r@ 1461 4 */ + 678882 - 
  r@ 100 / - r> 400 / + ; 
\ modified Julian day
\ 1858 11 17 -> 0  

: ymd \ mjd -- y m d
  51604 - 146097 /mod swap 
  dup 146096 = 
  if drop 3 36524 else 36524 /mod swap then
  1461 /mod swap dup 1460 = 
  if drop 3 366 else 365 /mod swap 1+ then
  >r rot 100 * + rot 400 * + swap 4 * + 2000 + r> 
  5 * 3 - 153 /mod swap 5 / 1+ 
  >r 3 + dup >r 12 > 
  if 1 + r> 12 - else r> then r> ; 

: dow \ mjd -- m
  3 + 7 mod ;
\ day of week
\ sunday=0

: dow$ \ m -- ad n
  2 lshift 
  s" Sun Mon Tue Wed Thu Fre Sat " 
  drop + 4 ;
\ name of day of week

: month$ \ m -- ad n
  1- 2 lshift 
  s" Jan Feb Mar Apr May Jun Jul Aug Sep Oct Nov Dec " 
  drop + 4 ;
\ name of month

: days \ y1 m1 d1 y2 m2 d2 -- n
  mjd >r mjd r> - negate ;

: sec \ h m s -- n
  rot 60 *
  rot + 60 * + ;

: hms \ n -- h m s
  60 /mod 
  60 /mod
  swap rot ;

: ymd$ \ y m d -- ad n
  swap rot
  0 <# # # # # #> here string! [char] - here char&
  0 <# # # #> here string& [char] - here char&
  0 <# # # #> here string&
  here count ;

: hms$ \ h m s -- ad n
  swap rot
  0 <# # # #> here string! [char] : here char&
  0 <# # # #> here string& [char] : here char&
  0 <# # # #> here string&
  here count ;

: now \ -- mjd sec
  time&date 
  swap rot mjd >r
  60 * +
  60 * +
  r> swap ;

: seconds \ h1 m1 s1 h2 m2 s2 -- n
  sec >r sec r> - negate ;

create dom% 31 c, 28 c, 31 c, 30 c, 31 c, 30 c, 31 c, 31 c, 30 c, 31 c, 30 c, 31 c, 
create doy% 0 , 11 cells allot

: doycalc \ --
  0 12 1
  do dom% i 1- + c@ + dup doy% i cells + !
  loop drop ; doycalc
\ load doy%

: isleapyear \ y -- flag
  dup 4 mod 0=
  over 100 mod 0= 0= and 
  swap 400 mod 0= or ;

: wasleapyear \ y -- flag
  isleapyear ;

: doy \ y m d -- n
  swap 1- cells doy% + @ + 
  dup 59 > if swap isleapyear - else nip then ;
\ day of year

: week-eu \ y m d -- n
  2 pick 1 4 mjd dow ?dup   \ y m d dow dow?
  if negate 12 +            \ y m d 12-dow
  else 5                    \ y m d 5
  then >r                   \ first day of week 2 in r
  doy r> - dup 0<           \ doy-r flag
  if 7 + 0< 
     if 52 else 1 then
  else 7 / 2 + 
  then ; 
\ week numbers used in EU and a lot of other countries

2000 1 1 mjd constant mjd2k

: fm2k \ n -- mjd
  s>f
  29.530588861e
  fover f* 
  fswap fdup f*
  102.026e-12 f* f+
  20.362955e f+ f>s
  mjd2k + ; 
\ n is the number of full moons since 
\ the first full moon after 2000 1 1 0 0 0

0 fm2k constant ffm2k
\ first fullmoon mjd 2000

: equinox \ y -- mjd
  3 21 mjd ;
\ The date used by Christian church

: nextfm \ mjd1 -- mjd2
  dup ffm2k - 10 297 */      \ mjd1 n
  begin 2dup fm2k >          \ mjd1 n mjd1>mjd2
  while 1+ 
  repeat nip fm2k ; 
\ next full moon from mjd

: nextdow \ dow mjd1 -- mjd2
  begin dup dow 2 pick <>
  while 1+ 
  repeat nip ;

: easter \ y -- mjd
  equinox nextfm 0 swap nextdow ;
\ The Christian Easter
