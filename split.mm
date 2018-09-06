$( set.mm - Version of 5-Sep-2018 $)
$( To prevent GitHub merge conflicts, please change the above date only if
there are no other pull requests in the queue.  Travis has been modified to use
"verify markup * /date_skip" to prevent a non-updated date from causing an
error.  I will maintain the date when necessary.  --NM $)

$( Important recent changes:  On 28-Jul-2017 and 18-Aug-2017, specialization
related theorems *cla4* and *a4* (no cl) were renamed *spc* and *sp*
respectively.  On 27-Apr-2017, copab2 was renamed coprab (122 places).
Starting 17-Aug-2018, redundant "A e. V" antecedents are being removed from
sbc* and csb* theorems and their consequences.  --NM

See 'help verify markup' in metamath.exe for markup conventions. $)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
            Metamath source file for logic and set theory
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

                           ~~ PUBLIC DOMAIN ~~
This work is waived of all rights, including copyright, according to the CC0
Public Domain Dedication.  http://creativecommons.org/publicdomain/zero/1.0/

Principal curator:  Norman Megill   http://us.metamath.org/email.html

Contributor list:

DA  David Abernethy      JH  Jeff Hoffman          MM  Mykola Mostovenko
SA  Stefan Allan         SJ  Szymon Jaroszewicz    SO  Stefan O'Rear
TA  Thierry Arnoux       BJ  Benoit Jubin          JO  Jason Orendorff
JA  Juha Arpiainen       JK  Jim Kingdon           JP  Josh Purinton
JB  Jonathan Ben-Naim    WL  Wolf Lammen           SR  Steve Rodriguez
GB  Gregory Bush         GL  Gerard Lang           ATS Andrew Salmon
MC  Mario Carneiro       BL  Brendan Leahy         AS  Alan Sare
PC  Paul Chapman         RL  Raph Levien           ES  Eric Schmidt
DF  Drahflow             FL  Frederic Line         GS  Glauco Siliprandi
GD  Georgy Dunaev        RFL Roy F. Longton        SS  Saveliy Skresanov
SF  Scott Fenton         GM  Giovanni Mascellani   JU  Jarvin Udandy
JGH Jeffrey Hankins      JM  Jeff Madsen           AV  Alexander van der Vekens
AH  Anthony Hart         RM  Rodolfo Medina        DAW David A. Wheeler
DH  David Harvey         NM  Norman Megill         JY  Jonathan Yan
CH  Chen-Pang He         MO  Mel L. O'Cat          FZ  Fan Zheng


HTML code for accented names:
  BJ Beno&icirc;t Jubin
  GL G&eacute;rard Lang
  FL Fr&eacute;d&eacute;ric Lin&eacute;

$)

$( (See 'help verify markup' for help with the markup syntax.) $)
$[ set/header.mm $]

$[ set/main.mm $]

$[ set/deprec.mm $]

$[ set/typeset.mm $]


$[ set/hilsp.mm $]


$[ set/mbox.mm $]
