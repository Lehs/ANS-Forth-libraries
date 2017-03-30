\ Modified Julian calendar functions, ANS-Forth

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
  s" Sun Mon Tue Wed Thu Fri Sat " 
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

: isleapyear \ y -- flag
  dup 4 mod 0=
  over 100 mod 0= 0= and 
  swap 400 mod 0= or ;

: wasleapyear \ y -- flag
  isleapyear ;

: doy \ y m d -- n
  swap 1- cells doy% + @ + 
  dup 59 > if swap isleapyear - else nip then ;

: doy~ \ y m d -- n
  2 pick >r
  mjd r> 1 1 mjd - 1+ ;

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
