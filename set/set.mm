$( This is the Metamath database set.mm. $)

$( Metamath is a formal language and associated computer program for
   archiving, verifying, and studying mathematical proofs, created by Norman
   Dwight Megill (1950--2021).  For more information, visit
   https://us.metamath.org and
   https://github.com/metamath/set.mm, and feel free to ask questions at
   https://groups.google.com/g/metamath. $)

$( New users may want to read https://us.metamath.org/mpeuni/conventions.html
   to understand the label naming conventions used in set.mm.  See also the
   Metamath program command "MM> HELP VERIFY MARKUP" for markup conventions. $)

$( To break this file into smaller modules, in the Metamath program type
   "MM> READ set.mm" followed by "MM> WRITE SOURCE set.mm / SPLIT".  To
   recombine, omit "/ SPLIT". $)

$( The database set.mm was created by Norman Megill on 30-Sep-1992 and has
   been continuously enriched since then (list of contributors below). $)


$( !
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Metamath source file for logic and set theory
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

                           ~~ PUBLIC DOMAIN ~~
This work is waived of all rights, including copyright, according to the CC0
Public Domain Dedication.  https://creativecommons.org/publicdomain/zero/1.0/

Currently active maintainers: See the list in the CONTRIBUTING.md file of
https://github.com/metamath/set.mm.

Contributor list:

DA  David Abernethy
SA  Stefan Allan
TA  Thierry Arnoux
JA  Juha Arpiainen
JB  Jonathan Ben-Naim
GB  Gregory Bush
MC  Mario Carneiro
FC  Filip Cernatescu
PC  Paul Chapman
DF  Drahflow
AD  Adrian Ducourtial
GD  Georgy Dunaev
SF  Scott Fenton
GG  Gino Giotto
JGH Jeff Hankins
AH  Anthony Hart
DH  David Harvey
CH  Chen-Pang He
JH  Jeff Hoffman
II  Igor Ieskov
AI  Asger C. Ipsen
JJ  Jerry James
SJ  Szymon Jaroszewicz
BJ  Benoit Jubin
JK  Jim Kingdon
ML  M L
WL  Wolf Lammen
GL  Gerard Lang
BL  Brendan Leahy
LL  Larry Lesyna
RL  Raph Levien
FL  Frederic Line
RFL Roy F. Longton
TM  T M
TVM Thomas van Maaren
JPM Jeffrey P. Machado
JM  Jeff Madsen
GM  Giovanni Mascellani
PM  Peter Mazsa
RM  Rodolfo Medina
NM  Norman Megill
MKU metakunt
DM  David Moews
MM  Mykola Mostovenko
LM  Luke Murphy
SN  Steven Nguyen
MO  Mel L. O'Cat
OAI OpenAI
SO  Stefan O'Rear
JO  Jason Orendorff
KP  K P
NP  Noam Pasman
JPP Jon Pennant
RP  Richard Penner
SP  Stanislas Polu
JP  Josh Purinton
RMI Remi
RR  Rohan Ridenour
SR  Steve Rodriguez
ATS Andrew Salmon
AS  Alan Sare
ES  Eric Schmidt
GS  Glauco Siliprandi
SS  Saveliy Skresanov
BTT BTernaryTau
ET  Ender Ting
JU  Jarvin Udandy
ADH Stijn "Adhemar" Vandamme
AV  Alexander van der Vekens
JV  Jannik Vierling
ZW  Zhi Wang
EW  Emmett Weisz
DAW David A. Wheeler
RW  Roger Witte
KW  Kyle Wyonch
JY  Jonathan Yan
MY  Mingli Yuan
FZ  Fan Zheng
KZ  Kunhao Zheng

HTML code for accented names:
  BJ Beno&icirc;t Jubin
  GL G&eacute;rard Lang
  FL Fr&eacute;d&eacute;ric Lin&eacute;

$)


$( See "MM> HELP VERIFY MARKUP" for help with modularization tags. $)
$[ set-header.mm $]


$[ set-main.mm $]


$[ set-deprec.mm $]


$[ set-typeset.mm $]


$[ set-hilsp.mm $]


$[ set-mbox.mm $]
